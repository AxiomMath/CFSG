module

public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdModel
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvdLat
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  UCoord SpCoord

theorem ggTorusLattice_psu_dvd
    {K : Type} [Field K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 5 ≤ d) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) :
    GGTorusLattice p (d - 3) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hp2 : p ≠ 2 := by omega
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := by
    have hdp : d / p ≤ d / 5 := Nat.div_le_div_left hp5 (by norm_num)
    have hle : d / p + 2 ≤ max (d - 3) 3 := by
      rcases le_total (d - 3) 3 with h | h
      · rw [max_eq_right h]
        omega
      · rw [max_eq_left h]
        omega
    have h1 : p ^ (d / p + 2) ≤ p ^ max (d - 3) 3 := Nat.pow_le_pow_right hp.pos hle
    have h2 : p ^ max (d - 3) 3 ≤ Nat.card A := by
      rcases le_total (d - 3) 3 with h | h
      · rw [max_eq_right h]
        exact h3
      · rw [max_eq_left h]
        exact hr
    exact h1.trans h2
  obtain ⟨φ, -, -, -, S, Θ, hS, hΘ, hkerΘ, hperm, -⟩ :=
    ggKGTAU_permModel hK hn hd hp hpq hpd hψ hker hperf hAe hAI hcard hsc
  exact ggKGTAD_lattice hp hp2 hpd hd hS Θ hΘ hkerΘ hperm

private theorem ggKGTuk_mem_permAut {p d : ℕ}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ : Equiv.Perm (Fin d))
    (f : Fin d → Multiplicative (ZMod p)) (hf : f ∈ S) : permAut σ f ∈ S := by
  rcases hS with h | h
  · rw [h]; exact Subgroup.mem_top _
  · rw [h] at hf ⊢; exact permAut_mem_sumZero σ hf

private theorem ggKGTuk_model {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (h : UnitaryFieldData 2 n K)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) :
    UnitTB.Model φ where
  field := h
  surj := hφs
  ker := hφker

private theorem ggKGTuk_ker_le_center {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (h : UnitaryFieldData 2 n K) (hd0 : 0 < d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) :
    φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro g hg
  have hmem : g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := by
    rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    exact (LineU.mem_scalars_subgroupOf_iff h hd0).mpr (hφker g (MonoidHom.mem_ker.mp hg))
  exact TableBUE.ker_projMk_le_center (K := K) (n := n) (d := d) hmem

private theorem ggKGTuk_layer {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) (hd : 3 ≤ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t)
    {i j : Fin d} (hij : i ≠ j) {a : MulAut L'} (ha : a ∈ A)
    (hcomm : MulAut.conj (φ (LineU.permSU h (Equiv.swap i j))) * a =
      a * MulAut.conj (φ (LineU.permSU h (Equiv.swap i j)))) :
    φ (LineU.permSU h (Equiv.swap i j)) ∈ LargeEvenLayer (ggFix a) := by
  classical
  obtain ⟨t, hact⟩ := hdiag a ha
  have htij : t i = t j :=
    (SuDvdRootGen.commute_conj_permSU_swap_iff h hd hφker hφs hact i j).mp hcomm
  obtain ⟨σ, hσt, hacts⟩ := SmallU.ActsU.of_actsDiagU hact
  have hσij : σ i = σ j := by
    apply Units.ext
    rw [hσt i, hσt j, htij]
  let Sc : Finset (Fin d) := Finset.univ.filter fun k => σ k = σ i
  have hSmem : ∀ k : Fin d, k ∈ Sc ↔ σ k = σ i := by
    intro k
    simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub_ij : ({i, j} : Finset (Fin d)) ⊆ Sc := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨(hSmem i).mpr rfl, (hSmem j).mpr hσij.symm⟩
  have hcardS : 2 ≤ Sc.card := by
    calc 2 = ({i, j} : Finset (Fin d)).card := (Finset.card_pair hij).symm
      _ ≤ Sc.card := Finset.card_le_card hsub_ij
  have hScond : ∀ i' ∈ Sc, ∀ j' : Fin d, j' ∈ Sc ↔ σ j' = σ i' := by
    intro i' hi' j'
    have hi'eq : σ i' = σ i := (hSmem i').mp hi'
    rw [hSmem j', hi'eq]
  have hModel : UnitTB.Model φ := ggKGTuk_model h hφs hφker
  have hkerSU : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) :=
    ggKGTuk_ker_le_center h (by omega) hφker
  have hq : Assembly.IsQuasisimple
      ↥((TableBUE.blockSU (K := K) (n := n) Sc).map φ) :=
    SURepair.isQuasisimple_map_blockSU_of_two_le (K := K) (f := n) (n := d) h hn hkerSU hcardS
  have hcomp := SmallU.isComponentOf_block hModel hacts hScond hq
  have hle : (TableBUE.blockSU (K := K) (n := n) Sc).map φ ≤ LargeEvenLayer (ggFix a) :=
    le_sSup hcomp
  exact hle (Subgroup.mem_map_of_mem φ
    (SUTorus.blockSU_mono (K := K) (f := n) (n := d) hsub_ij
      (SuDvdRootGen.permSU_swap_mem_blockSU h i j)))

theorem ggTorusRootSL2_psu_dvd
    {K : Type} [Field K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 5 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    {r : ℕ} (hle : d / p + 2 ≤ max r 3) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) :
    GGTorusRootSL2 p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hd3 : 3 ≤ d := by omega
  have hd4 : 4 ≤ d := by omega
  have h1n : 1 ≤ n := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro h'
    have := congrArg Prod.fst h'
    simp only at this
    omega
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  have hAp : ∀ a ∈ A, a ^ p = 1 := hAe.2
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := by
    have h1 : p ^ (d / p + 2) ≤ p ^ max r 3 := Nat.pow_le_pow_right hp.pos hle
    have h2 : p ^ max r 3 ≤ Nat.card A := by
      rcases le_total r 3 with h | h
      · rw [max_eq_right h]
        exact h3
      · rw [max_eq_left h]
        exact hr
    exact h1.trans h2
  obtain ⟨φ, hφs, hφker, hdiag, S, Θ, hS, hΘ, hkerΘ, hperm, hpermlift⟩ :=
    ggKGTAU_permModel hK hn hd hp hpq hpd hψ hker hperf hAe hAI hcard hsc
  have hK' : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK h1n
  intro φ₀ hφ₀ hrefl
  obtain ⟨i, j, hij, hclas⟩ :=
    ggKGTl_classify_apply hp hp2 hpd hd4 hS Θ hΘ hkerΘ hperm hφ₀ hrefl
  have hnorm : MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) ∈
      Subgroup.normalizer (A : Set (MulAut L')) :=
    SuDvdRootGen.conj_permSU_mem_normalizer hK' hpq hd3 hφs hφker hdiag hAp hsc (Equiv.swap i j)
  have hmperm : ggConjAut A hnorm = φ₀ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    obtain ⟨f, rfl⟩ := hΘ b
    let g : ↥S := ⟨permAut (Equiv.swap i j) (f : Fin d → Multiplicative (ZMod p)),
      ggKGTuk_mem_permAut hS (Equiv.swap i j) (f : Fin d → Multiplicative (ZMod p)) f.2⟩
    have hg : (g : Fin d → Multiplicative (ZMod p)) =
        permAut (Equiv.swap i j) (f : Fin d → Multiplicative (ZMod p)) := rfl
    have h1 := hpermlift hK' (Equiv.swap i j) hnorm f g hg
    have h2 := hclas f g hg
    rw [h1, h2]
  refine ⟨φ (LineU.permSU hK' (Equiv.swap i j)), hnorm,
    (TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ,
    SuDvdRootGen.ggTorusWeylElt_permSU hK' hd3 hφker hdiag hAp (Equiv.swap i j),
    hmperm,
    Subgroup.mem_map_of_mem φ (SuDvdRootGen.permSU_swap_mem_blockSU hK' i j),
    ?_, ?_, ?_⟩
  · have hcommC : ∀ a ∈ A, MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) * a =
        a * MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) →
        ∃ t : Fin d → K, LineU.ActsDiagU φ a t ∧ t i = t j := by
      intro a ha hconj
      obtain ⟨t, ht⟩ := hdiag a ha
      exact ⟨t, ht,
        (SuDvdRootGen.commute_conj_permSU_swap_iff hK' hd3 hφker hφs ht i j).mp hconj⟩
    exact SuDvdRootGen.isComponentOf_blockSU_pair_ggHypCent hK' hn hp hpq hd4 hφs hφker
      hdiag hsc hij hcommC
  · exact SuDvdRootGen.dvd_card_blockSU_pair_map hK' hp hpq hd3 hφker hij
  · intro a ha hfix
    have hfix' : ggConjAut A hnorm ⟨a, ha⟩ = ⟨a, ha⟩ := by
      rw [hmperm]
      exact hfix
    by_cases ha1 : a = 1
    · subst ha1
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hSUq : CFSG.IsQuasisimple ↥(unitarySU 2 n K d) :=
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2)
          (f := n) hK (by omega) hdq).1
      have hcent : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) :=
        ggKGTuk_ker_le_center hK' (by omega) hφker
      have hLq : CFSG.IsQuasisimple L' :=
        CFSG.LocalCores.isQuasisimple_of_surjective hSUq φ hφs hcent
      have hqtop : CFSG.IsQuasisimple (↥(⊤ : Subgroup L')) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := L')).symm hLq
      have hqtopA : Assembly.IsQuasisimple (↥(⊤ : Subgroup L')) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqtop
      have hcompTop : IsComponentOf (⊤ : Subgroup L') (⊤ : Subgroup L') :=
        ⟨le_top, IsSubnormal.refl ⊤, hqtopA⟩
      have hlayerTop : LargeEvenLayer (⊤ : Subgroup L') = ⊤ :=
        le_antisymm le_top (le_sSup hcompTop)
      have hfix1 : ggFix (1 : MulAut L') = ⊤ := by
        ext x
        simp [ggFix]
      rw [hfix1, hlayerTop]
      exact Subgroup.mem_top _
    · have hcomm : MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) * a =
          a * MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) := by
        have h := congrArg (fun x : ↥A => (x : MulAut L')) hfix'
        rw [ggConjAut_apply] at h
        calc MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) * a
            = (MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) * a *
                (MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))))⁻¹) *
                MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) := by group
          _ = a * MulAut.conj (φ (LineU.permSU hK' (Equiv.swap i j))) := by rw [h]
      exact ggKGTuk_layer hK' hn hd3 hφs hφker hdiag hij ha hcomm

end CFSG.StandardType
