module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdBlock

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open SuNsRootGen

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover

private theorem ggKGSu_model {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (h : UnitaryFieldData 2 n K)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker) (hd0 : 0 < d) :
    UnitTB.Model φ where
  field := h
  surj := hφs
  ker := fun g hg => (UnitTB.projMk_eq_one_iff (K := K) (n := n) (d := d) hd0 (x := g)).mp
    (MonoidHom.mem_ker.mp (hφker g hg))

private theorem ggKGSu_actsU {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} {a : MulAut L'} {D : ↥(unitarySU 2 n K d)}
    {σ : Fin d → Kˣ} (hD : (D : GL (Fin d) K) = diagHom d σ)
    (haD : a = MulAut.conj (φ D)) : SmallU.ActsU φ a σ := by
  have hDn : diagHom d σ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.le_normalizer (by rw [← hD]; exact D.2)
  refine ⟨hDn, ?_⟩
  intro s
  have hconj : LineU.conjN (diagHom d σ) hDn s = D * s * D⁻¹ := by
    apply Subtype.ext
    rw [LineU.coe_conjN, ← hD]
    rfl
  rw [haD, MulAut.conj_apply, hconj]
  rw [map_mul, map_mul, map_inv]

theorem ggTorusRootSL2_psu_coprime
    {K : Type} [Field K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGTorusRootSL2 p 0 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h := TableBU.unitaryFieldData_of_card hK (by omega)
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  intro φ₀ hφ₀ hrefl
  rcases (show d = 3 ∨ 4 ≤ d by omega) with rfl | hd4
  ·
    exfalso
    have hdq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := fun h' => by
      have := congrArg Prod.snd h'
      simp only at this
      omega
    obtain ⟨Θ, -⟩ := exists_permModel hp (TableBUE.center_proj_eq_bot hK le_rfl hdq)
      (fun φa hφa hφap => InndiagSU.ggOutdiagPrime_unitary hK (by omega) le_rfl hdq hp hpq hpd
        φa hφa hφap)
      (StdSubRestU.ggCenterPrime_unitary hK (by omega) le_rfl hdq hp hp2 hpd)
      (UModel.ggTorusPermEltSC_unitary hK (by omega) (by omega) hp hp2 hpq hpd)
      hψ hker hperf hAe hAI h3 hsc
    have : NeZero p := ⟨hp.ne_zero⟩
    have hle : Nat.card ↥(UCoord.sumZero 3 p) ≤ p ^ 2 := UCoord.card_sumZero_le 2 p
    rw [Nat.card_congr Θ.toEquiv] at hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
    omega
  · have hdq : (d, 2 ^ n) ≠ (3, 2) := by
      intro h'
      have := congrArg Prod.fst h'
      simp only at this
      omega
    obtain ⟨φ, hφs, hφker, hM⟩ :=
      exists_isDiagTorusModelU hK hn hd4 hp hpq hpd hψ hker hperf hAe hAI hsc
    haveI : Finite (MulAut L') :=
      Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
        ext x
        exact congrFun h x
    haveI : Finite ↥A := Subtype.finite
    obtain ⟨Θ, -, hΘsurj, hΘperm⟩ := exists_permModel hp
      (TableBUE.center_proj_eq_bot hK (by omega) hdq)
      (fun φa hφa hφap => InndiagSU.ggOutdiagPrime_unitary hK (by omega) (by omega) hdq hp hpq
        hpd φa hφa hφap)
      (StdSubRestU.ggCenterPrime_unitary hK (by omega) (by omega) hdq hp hp2 hpd)
      (UModel.ggTorusPermEltSC_unitary hK (by omega) (by omega) hp hp2 hpq hpd)
      hψ hker hperf hAe hAI h3 hsc
    let E : Equiv.Perm (Fin d) →* MulAut ↥A :=
      (MulAut.congr Θ).toMonoidHom.comp (UCoord.permAutVHom d p)
    have hEapply : ∀ σ : Equiv.Perm (Fin d), E σ = MulAut.congr Θ (UCoord.permAutV σ) :=
      fun σ => rfl
    have hEinj : Function.Injective E :=
      (MulAut.congr Θ).injective.comp (UCoord.permAutV_injective hp hp2)
    have hEauto : ggAutomizer (MulAut.conj : L' →* MulAut L').range A = E.range := by
      refine le_antisymm ?_ ?_
      · rw [ggAutomizer, Subgroup.closure_le]
        rintro φa ⟨g, hg, hgn, hga⟩
        obtain ⟨n, rfl⟩ := hg
        have hφeq : φa = ggConjAut A hgn := MulEquiv.ext fun b => Subtype.ext (by
          rw [hga b, ggConjAut_apply])
        rw [hφeq]
        obtain ⟨π, hπ⟩ := hΘperm n hgn
        exact ⟨π, (hEapply π).trans hπ.symm⟩
      · rintro _ ⟨σ, rfl⟩
        obtain ⟨n, hn, hnn⟩ := hΘsurj σ
        rw [hEapply σ, ← hnn]
        exact Subgroup.subset_closure ⟨MulAut.conj n, ⟨n, rfl⟩, hn, fun b =>
          ggConjAut_apply A hn b⟩
    obtain ⟨u, hord, huq⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) h hp hpq
    have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
    let Θ' : ↥(UCoord.sumZero d p) ≃* ↥A :=
      torusEquivUOf h hp hpd (by omega) hφker hM hu hord huq
    let E' : Equiv.Perm (Fin d) →* MulAut ↥A :=
      (MulAut.congr Θ').toMonoidHom.comp (UCoord.permAutVHom d p)
    have hE'apply : ∀ σ : Equiv.Perm (Fin d), E' σ = MulAut.congr Θ' (UCoord.permAutV σ) :=
      fun σ => rfl
    have hE'inj : Function.Injective E' :=
      (MulAut.congr Θ').injective.comp (UCoord.permAutV_injective hp hp2)
    have hswapU : ∀ x y : Fin d, x ≠ y →
        E' (Equiv.swap x y) = ggConjAut A (conj_swapU_mem_normalizer h hM x y) := by
      intro x y hxy
      rw [hE'apply]
      exact (ggConjAut_swapU_eq_of h hp hpd (by omega) hφker hM hu hord huq x y).symm
    have hE'leE : E'.range ≤ E.range := by
      have hle_auto : E'.range ≤ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
        let P : Subgroup (MulAut ↥(UCoord.sumZero d p)) :=
          Subgroup.comap (MulAut.congr Θ').toMonoidHom
            (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
        have hH : ∀ i j : Fin d, i ≠ j → UCoord.permAutV (Equiv.swap i j) ∈ P := by
          intro x y hxy
          change E' (Equiv.swap x y) ∈
            ggAutomizer (MulAut.conj : L' →* MulAut L').range A
          rw [hswapU x y hxy]
          exact Subgroup.subset_closure ⟨MulAut.conj (φ (SURep.swapU h x y)), ⟨_, rfl⟩,
            conj_swapU_mem_normalizer h hM x y, fun b => ggConjAut_apply A _ b⟩
        rintro _ ⟨σ, rfl⟩
        change MulAut.congr Θ' (UCoord.permAutV σ) ∈
          ggAutomizer (MulAut.conj : L' →* MulAut L').range A
        exact UCoord.mem_closure_permAutV (H := P) hH σ
      exact hle_auto.trans (le_of_eq hEauto)
    have hcardE : Nat.card E.range = Nat.card (Equiv.Perm (Fin d)) :=
      (Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv).symm
    have hcardE' : Nat.card E'.range = Nat.card (Equiv.Perm (Fin d)) :=
      (Nat.card_congr (MonoidHom.ofInjective hE'inj).toEquiv).symm
    have hE'range : E'.range = E.range :=
      Subgroup.eq_of_le_of_card_ge hE'leE (by rw [hcardE, hcardE'])
    have hφ₀E' : φ₀ ∈ E'.range := by
      rw [hE'range, ← hEauto]
      exact hφ₀
    obtain ⟨π, hπ⟩ := hφ₀E'
    have hreflE : GGIsReflection p (E' π) := by
      rw [hπ]
      exact hrefl
    have hisSwap : π.IsSwap := by
      haveI : Fact p.Prime := ⟨hp⟩
      exact isSwap_of_ggIsReflection hp2 hAe E' hE'inj
        (fun x y hxy => by
          rw [hswapU x y hxy]
          exact isReflection_conj_swapU h hp hpq hpd (by omega) hφker hM hxy)
        hreflE
    obtain ⟨i, j, hij, hπij⟩ := hisSwap
    have hφ₀eq : ggConjAut A (conj_swapU_mem_normalizer h hM i j) = φ₀ := by
      rw [← hswapU i j hij, ← hπij]
      exact hπ
    refine ⟨φ (SURep.swapU h i j), conj_swapU_mem_normalizer h hM i j,
      (TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ,
      ggTorusWeylElt_swapU h hM i j, hφ₀eq,
      Subgroup.mem_map_of_mem φ (swapU_mem_blockSU h i j), ?_, ?_, ?_⟩
    · rw [ggHypCent_swapU_eq h hp hpd hφs hφker hM i j]
      exact isComponentOf_blockSU_pair (φ := φ) h hn hp hpq hd4 hφker hij
    · exact dvd_card_blockSU_pair h hp hpq (by omega) hφker hij
    ·
      intro a ha hfix
      have hfix' : ggConjAut A (conj_swapU_mem_normalizer h hM i j) ⟨a, ha⟩ = ⟨a, ha⟩ := by
        rw [hφ₀eq]
        exact hfix
      by_cases ha1 : a = 1
      ·
        subst ha1
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hSUq : CFSG.IsQuasisimple ↥(unitarySU 2 n K d) :=
          (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2)
            (f := n) hK (by omega) hdq).1
        have hcent : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) :=
          fun z hz => TableBUE.ker_projMk_le_center (K := K) (n := n) (d := d) (hφker z hz)
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
      ·
        obtain ⟨D, ⟨σ, hDσ⟩, -, haeq⟩ := (hM a).mp ha
        have hcomm : MulAut.conj (φ (SURep.swapU h i j)) * MulAut.conj (φ D) =
            MulAut.conj (φ D) * MulAut.conj (φ (SURep.swapU h i j)) := by
          have h1 : MulAut.conj (φ (SURep.swapU h i j)) * a *
              (MulAut.conj (φ (SURep.swapU h i j)))⁻¹ = a := by
            have h2 := congrArg (fun x : ↥A => (x : MulAut L')) hfix'
            rw [ggConjAut_apply] at h2
            simpa using h2
          have hAB : MulAut.conj (φ (SURep.swapU h i j)) * MulAut.conj (φ D) *
              (MulAut.conj (φ (SURep.swapU h i j)))⁻¹ = MulAut.conj (φ D) := by
            rw [← haeq]
            exact h1
          calc MulAut.conj (φ (SURep.swapU h i j)) * MulAut.conj (φ D)
              = (MulAut.conj (φ (SURep.swapU h i j)) * MulAut.conj (φ D) *
                  (MulAut.conj (φ (SURep.swapU h i j)))⁻¹) *
                  MulAut.conj (φ (SURep.swapU h i j)) := by group
            _ = MulAut.conj (φ D) * MulAut.conj (φ (SURep.swapU h i j)) := by rw [hAB]
        have hσij : σ i = σ j :=
          (conj_swapU_comm_conj_iff h hφker i j hDσ).mp hcomm
        let S : Finset (Fin d) := Finset.univ.filter fun k => σ k = σ i
        have hSmem : ∀ k : Fin d, k ∈ S ↔ σ k = σ i := by
          intro k
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        have hsub_ij : ({i, j} : Finset (Fin d)) ⊆ S := by
          rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact ⟨(hSmem i).mpr rfl, (hSmem j).mpr hσij.symm⟩
        have hcardS : 2 ≤ S.card := by
          calc 2 = ({i, j} : Finset (Fin d)).card := (Finset.card_pair hij).symm
            _ ≤ S.card := Finset.card_le_card hsub_ij
        have hScond : ∀ i' ∈ S, ∀ j' : Fin d, j' ∈ S ↔ σ j' = σ i' := by
          intro i' hi' j'
          have hi'eq : σ i' = σ i := (hSmem i').mp hi'
          rw [hSmem j', hi'eq]
        have hModel : UnitTB.Model φ := ggKGSu_model h hφs hφker (by omega)
        have hacts : SmallU.ActsU φ a σ := ggKGSu_actsU hDσ haeq
        have hkerSU : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) :=
          fun z hz => TableBUE.ker_projMk_le_center (K := K) (n := n) (d := d) (hφker z hz)
        have hq : Assembly.IsQuasisimple
            ↥((TableBUE.blockSU (K := K) (n := n) S).map φ) :=
          SURepair.isQuasisimple_map_blockSU_of_two_le (K := K) (f := n) (n := d) h (by omega)
            hkerSU hcardS
        have hcomp := SmallU.isComponentOf_block hModel hacts hScond hq
        have hle : (TableBUE.blockSU (K := K) (n := n) S).map φ ≤
            LargeEvenLayer (ggFix a) := le_sSup hcomp
        exact hle (Subgroup.mem_map_of_mem φ
          (SUTorus.blockSU_mono (K := K) (f := n) (n := d) hsub_ij
            (swapU_mem_blockSU h i j)))

end CFSG.StandardType

end
