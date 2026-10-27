module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperElt
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairPair

public section

namespace CFSG.StandardType

namespace IOneU

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2 TableBUE

section Comb

variable {K : Type} [Field K] {d p : ℕ}

abbrev freeSet (t c : Fin d) : Finset (Fin d) := (Finset.univ.erase t).erase c

theorem card_freeSet {t c : Fin d} (hct : c ≠ t) : (freeSet t c).card = d - 2 := by
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hct, Finset.mem_univ c⟩),
    Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]
  omega

theorem eq_of_agree {σ σ' : Fin d → Kˣ} (h1 : ∏ k, (σ k : K) = 1) (h1' : ∏ k, (σ' k : K) = 1)
    {s t c : Fin d} (hst : σ s = σ t) (hst' : σ' s = σ' t) (hs : s ≠ t) (hsc : s ≠ c)
    (hagree : ∀ i ∈ freeSet t c, σ i = σ' i) : σ = σ' := by
  have hne : ∀ k, k ≠ c → σ k = σ' k := by
    intro k hk
    by_cases hkt : k = t
    · rw [hkt, ← hst, ← hst']
      exact hagree s (Finset.mem_erase.mpr ⟨hsc, Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩⟩)
    · exact hagree k (Finset.mem_erase.mpr ⟨hk, Finset.mem_erase.mpr ⟨hkt, Finset.mem_univ k⟩⟩)
  funext k
  by_cases hkc : k = c
  · subst hkc
    apply Units.ext
    have e1 := Finset.mul_prod_erase Finset.univ (fun k => (σ k : K)) (Finset.mem_univ k)
    have e2 := Finset.mul_prod_erase Finset.univ (fun k => (σ' k : K)) (Finset.mem_univ k)
    have hrest : ∏ x ∈ Finset.univ.erase k, (σ x : K) = ∏ x ∈ Finset.univ.erase k, (σ' x : K) :=
      Finset.prod_congr rfl fun x hx => by rw [hne x (Finset.ne_of_mem_erase hx)]
    have hnz : ∏ x ∈ Finset.univ.erase k, (σ' x : K) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun x _ => Units.ne_zero _
    have e3 := e1.trans (h1.trans (h1'.symm.trans e2.symm))
    rw [hrest] at e3
    exact mul_right_cancel₀ hnz e3
  · exact hne k hkc

variable [Finite K]

theorem exists_node_of_pair (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hpd : ¬ p ∣ d)
    {W : Subgroup (Fin d → Kˣ)} (hWp : ∀ σ ∈ W, ∀ k, σ k ∈ rootsOfUnity p K)
    (hW1 : ∀ σ ∈ W, ∏ k, (σ k : K) = 1) {s t c : Fin d} (hst : s ≠ t) (hsc : s ≠ c)
    (hct : c ≠ t) (hWst : ∀ σ ∈ W, σ s = σ t) (hcard : p ^ (d - 2) ≤ Nat.card W) :
    ∃ σ ∈ W, σ ≠ 1 ∧ (∀ i, i ≠ c → ∀ j, j ≠ c → σ i = σ j) ∧ (∀ j, j ≠ c → σ j ≠ σ c) ∧
      ∀ σ' ∈ W, (∀ i, i ≠ c → ∀ j, j ≠ c → σ' i = σ' j) → σ' ∈ Subgroup.zpowers σ := by
  classical
  have := Fact.mk hp
  set F := freeSet t c with hF
  let f : W → (F → rootsOfUnity p K) := fun σ i => ⟨(σ : Fin d → Kˣ) i, hWp σ σ.2 i⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    refine eq_of_agree (hW1 _ a.2) (hW1 _ b.2) (hWst _ a.2) (hWst _ b.2) hst hsc fun i hi => ?_
    exact congrArg Subtype.val (congrFun hab ⟨i, hi⟩)
  have hcardF : Nat.card (F → rootsOfUnity p K) = p ^ (d - 2) := by
    rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_finsetCard,
      card_freeSet hct]
  have hbij := hf.bijective_of_nat_card_le (hcardF ▸ hcard)
  have hnt : Nontrivial (rootsOfUnity p K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, TypeA.card_rootsOfUnity_of_dvd hp hpK]
    exact hp.one_lt
  obtain ⟨lam, hlam⟩ := exists_ne (1 : rootsOfUnity p K)
  have hgen : ∀ μ : rootsOfUnity p K, μ ∈ Subgroup.zpowers lam := by
    intro μ
    have hle : Subgroup.zpowers lam = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [Nat.card_zpowers, TypeA.card_rootsOfUnity_of_dvd hp hpK]
      refine orderOf_eq_prime ?_ hlam
      have := lam.2
      rw [mem_rootsOfUnity] at this
      exact Subtype.ext (by simpa using this)
    rw [hle]
    exact Subgroup.mem_top μ
  obtain ⟨⟨σ, hσW⟩, hσ⟩ := hbij.2 fun _ => lam
  have hσF : ∀ i ∈ F, σ i = lam := fun i hi => congrArg Subtype.val (congrFun hσ ⟨i, hi⟩)
  have hsF : s ∈ F := Finset.mem_erase.mpr ⟨hsc, Finset.mem_erase.mpr ⟨hst, Finset.mem_univ s⟩⟩
  have hoff : ∀ i, i ≠ c → σ i = lam := by
    intro i hi
    by_cases hit : i = t
    · rw [hit, ← hWst σ hσW]
      exact hσF s hsF
    · exact hσF i (Finset.mem_erase.mpr ⟨hi, Finset.mem_erase.mpr ⟨hit, Finset.mem_univ i⟩⟩)
  have hlam1 : (lam : Kˣ) ≠ 1 := fun h => hlam (Subtype.ext h)
  refine ⟨σ, hσW, fun h1 => hlam1 ?_, fun i hi j hj => by rw [hoff i hi, hoff j hj], ?_, ?_⟩
  · rw [← hoff s hsc, h1]
    rfl
  · intro j hj hjc
    apply hpd
    have hall : ∀ k, σ k = lam := fun k => by
      by_cases hk : k = c
      · rw [hk, ← hjc, hoff j hj]
      · exact hoff k hk
    have hprod := hW1 σ hσW
    simp only [hall, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
    have hord : orderOf (lam : Kˣ) = p := by
      refine orderOf_eq_prime ?_ hlam1
      have := lam.2
      rw [mem_rootsOfUnity] at this
      exact this
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hprod, Units.val_one])
  · intro σ' hσ' hc'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨σ' s, hWp σ' hσ' s⟩)
    have hσ'off : ∀ i, i ≠ c → σ' i = (lam : Kˣ) ^ m := by
      intro i hi
      rw [hc' i hi s hsc]
      exact (congrArg Subtype.val hm).symm.trans (by rw [Subgroup.coe_zpow])
    have hσm : σ ^ m ∈ W := W.zpow_mem hσW m
    have heq : f ⟨σ', hσ'⟩ = f ⟨σ ^ m, hσm⟩ := by
      funext ⟨i, hi⟩
      apply Subtype.ext
      have hic : i ≠ c := Finset.ne_of_mem_erase hi
      show σ' i = (σ ^ m) i
      rw [hσ'off i hic, Pi.pow_apply, hoff i hic]
    have := congrArg Subtype.val (hf heq)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, this.symm⟩

end Comb

section Diag

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)

@[expose] noncomputable def swapSU (s t : Fin d) : ↥(unitarySU 2 n K d) :=
  ⟨permGL (Equiv.swap s t), permGL_swap_mem h s t⟩

omit [Finite K] in
theorem swapSU_sq (s t : Fin d) : swapSU h s t ^ 2 ^ 1 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_one, sq, swapSU, ← map_mul, Equiv.swap_mul_self, map_one]
  rfl

omit [Finite K] in
theorem commute_swapSU {s t : Fin d} {y : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ}
    (hy : (y : GL (Fin d) K) = diagHom d σ) (hst : σ s = σ t) :
    swapSU h s t * y = y * swapSU h s t := by
  apply Subtype.ext
  have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap s t) σ
  have h2 : σ ∘ (Equiv.swap s t).symm = σ := by
    funext k
    rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_def]
    split_ifs with h3 h4
    · rw [h3, hst]
    · rw [h4, hst]
    · rfl
  rw [h2, ← hy] at h1
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  show permGL (Equiv.swap s t) * (y : GL (Fin d) K) = (y : GL (Fin d) K) * permGL (Equiv.swap s t)
  calc permGL (Equiv.swap s t) * (y : GL (Fin d) K) =
        permGL (Equiv.swap s t) * (y : GL (Fin d) K) * (permGL (Equiv.swap s t))⁻¹ *
          permGL (Equiv.swap s t) := by group
    _ = (y : GL (Fin d) K) * permGL (Equiv.swap s t) := by rw [h1]

omit [Finite K] in
theorem projMk_swapSU_ne_one {s t : Fin d} (hst : s ≠ t) :
    LargeEvenProjMk (unitarySU 2 n K d) (swapSU h s t) ≠ 1 := by
  intro h1
  have hz : swapSU h s t ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := h1
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K))
    hu) s) t
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hst] at h2
  have h3 : ((swapSU h s t : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = permGL (Equiv.swap s t) := rfl
  rw [h3, permGL_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h2
  simp at h2

include h in
theorem exists_rootEndNode_diag (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d)
    {A : Subgroup ↥(unitarySU 2 n K d)} (hA : IsElemAbelian p A)
    (hdiag : ∀ x ∈ A, ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ)
    (hcard : p ^ (d - 2) ≤ Nat.card A) {s t : Fin d} (hst : s ≠ t)
    (hpair : ∀ σ ∈ diagVec A, σ s = σ t) :
    ∃ t₀, TableBOrth.IsEndNode (A.map (LargeEvenProjMk (unitarySU 2 n K d))) t₀ ∧
      ∃ U : Subgroup (LargeEvenProj (unitarySU 2 n K d)),
        U ≤ LargeEvenLayer (Subgroup.centralizer ({t₀} : Set _)) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        A.map (LargeEvenProjMk (unitarySU 2 n K d)) ≤ Subgroup.normalizer (U : Set _) := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hpK := dvd_card_sub_one hK hpq
  obtain ⟨c, hcs, hct⟩ : ∃ c : Fin d, c ≠ s ∧ c ≠ t := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin d)) ⊆ {s, t} := fun c _ => by
      by_cases hcs : c = s
      · simp [hcs]
      · simp [hcon c hcs]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ({s, t} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
    omega
  set W := diagVec A with hW
  have hWp : ∀ σ ∈ W, ∀ k, σ k ∈ rootsOfUnity p K := fun σ hσ k => by
    rw [mem_rootsOfUnity]
    exact (diagVec_props h hA hσ).1 k
  have hW1 : ∀ σ ∈ W, ∏ k, (σ k : K) = 1 := fun σ hσ => (diagVec_props h hA hσ).2
  have hWc : p ^ (d - 2) ≤ Nat.card W := by
    rw [hW, card_diagVec hdiag]
    exact hcard
  obtain ⟨σ, hσW, hσ1, hconst, hdist, hpow⟩ :=
    exists_node_of_pair hp hpK hpd hWp hW1 hst hcs.symm hct hpair hWc
  obtain ⟨x, hxA, hxσ⟩ := mem_diagVec.mp hσW
  set S : Finset (Fin d) := {c}ᶜ with hSdef
  have hmemS : ∀ i, i ∈ S ↔ i ≠ c := fun i => by simp [hSdef]
  have hSnode : IsNodeOn σ S := by
    refine ⟨fun i hi j hj => hconst i ((hmemS i).mp hi) j ((hmemS j).mp hj), fun i hi j hj => ?_⟩
    have hic : i = c := by
      by_contra hne
      exact hi ((hmemS i).mpr hne)
    rw [hic] at hj ⊢
    exact hdist j hj
  have hScard : S.card = d - 1 := by
    rw [hSdef, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hS3 : 3 ≤ S.card := by omega
  have hSq : (S.card, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : S.card = 3 := congrArg Prod.fst he
    have h2 : 2 ^ n = 2 := congrArg Prod.snd he
    rcases hq with hq | hq <;> omega
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  have hker := ker_projMk_le_center (n := n) (d := d) (K := K)
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hσ1
    have h1 : diagHom d σ = 1 := by rw [← hxσ]; rfl
    exact diagHom_injective d (h1.trans (map_one _).symm)
  have hC := centralizer_map_eq_of_noTorsion π (QuotientGroup.mk'_surjective _) hker hnp
    (hA.2 x hxA)
  have hJq := isQuasisimple_blockSU S h hK hS3 hSq
  have hJC := blockSU_le_centralizer hSnode.1 hxσ
  have hcomm : ∀ g ∈ Subgroup.centralizer {x}, ∀ g' ∈ Subgroup.centralizer {x},
      g * g' * g⁻¹ * g'⁻¹ ∈ blockSU S := fun g hg g' hg' =>
    commutator_mem_blockSU hSnode hxσ hg hg'
  have hcent : ∀ y' ∈ A, (∀ j ∈ blockSU S, y' * j = j * y') ↔ y' ∈ Subgroup.zpowers x := by
    intro y' hy'
    obtain ⟨σ', hσ'⟩ := hdiag y' hy'
    rw [commute_blockSU_iff h hσ']
    constructor
    · intro hc
      have hmem := hpow σ' (mem_diagVec_of hy' hσ') fun i hi j hj =>
        hc i ((hmemS i).mpr hi) j ((hmemS j).mpr hj)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow, hxσ, hσ', ← hm, map_zpow]
    · intro hmem i hi j hj
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hσm : σ' = σ ^ m := by
        apply diagHom_injective d
        rw [← hσ', map_zpow, ← hxσ, Subgroup.coe_zpow]
      rw [hσm, Pi.pow_apply, Pi.pow_apply, hSnode.1 i hi j hj]
  have hinj : ∀ y ∈ A, π y = 1 → y = 1 := fun y hy hy1 => hnp y hy1 (hA.2 y hy)
  have hend := isEndNode_map_of_cover π hker hinj hxA hx1 hJq hJC hcomm hC hcent
  have hJq' : CFSG.IsQuasisimple ((blockSU S).map π) := by
    have h1 := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hJq
      (π.comp (blockSU S).subtype) (by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hz) y))
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  obtain ⟨hlayer, -⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem
    (H := Subgroup.centralizer {π x}) (D := (blockSU S).map π)
    (by rw [hC]; exact Subgroup.map_mono hJC)
    (by
      rw [hC]
      rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      refine ⟨g * g' * g⁻¹ * g'⁻¹, hcomm g hg g' hg', ?_⟩
      simp only [map_mul, map_inv])
    hJq'
  have hsS : s ∈ S := (hmemS s).mpr hcs.symm
  have htS : t ∈ S := (hmemS t).mpr hct.symm
  have hwS : swapSU h s t ∈ blockSU S := isBlockOn_permGL_swap hsS htS
  refine ⟨π x, hend, (Subgroup.zpowers (swapSU h s t)).map π, ?_, ?_,
    (isPGroup_two_zpowers (swapSU_sq h s t)).map π, ?_⟩
  · rw [hlayer]
    exact Subgroup.map_mono (Subgroup.zpowers_le.mpr hwS)
  · intro hbot
    apply projMk_swapSU_ne_one h hst
    have h1 : π (swapSU h s t) ∈ (Subgroup.zpowers (swapSU h s t)).map π :=
      ⟨_, Subgroup.mem_zpowers _, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact h1
  · rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨y, hy, rfl⟩ _ ⟨u, hu, rfl⟩
    obtain ⟨σ', hσ'⟩ := hdiag y hy
    have hyw := commute_swapSU h hσ' (hpair σ' (mem_diagVec_of hy hσ'))
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine ⟨swapSU h s t ^ m, Subgroup.zpow_mem_zpowers _ _, ?_⟩
    have hc : y * swapSU h s t ^ m * y⁻¹ = swapSU h s t ^ m := by
      rw [← (Commute.zpow_left hyw m).eq, mul_inv_cancel_right]
    rw [← map_inv, ← map_mul, ← map_mul, hc]

include h in
theorem exists_rootEndNode_unitary (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d)
    {Ab : Subgroup (LargeEvenProj (unitarySU 2 n K d))} (hAb : IsElemAbelian p Ab)
    (hr : p ^ (d - 2) ≤ Nat.card Ab)
    (hU : ∃ U : Subgroup (LargeEvenProj (unitarySU 2 n K d)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      Ab ≤ Subgroup.normalizer (U : Set _)) :
    ∃ t, TableBOrth.IsEndNode Ab t ∧
      ∃ U : Subgroup (LargeEvenProj (unitarySU 2 n K d)),
        U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set _)) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        Ab ≤ Subgroup.normalizer (U : Set _) := by
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hmap, -, hA, hcardA⟩ :=
    exists_lift_of_noTorsion π (QuotientGroup.mk'_surjective _) hp hnp hAb
  obtain ⟨P, hP, hdiag⟩ := exists_conj_diag h hp hpq hA
  set c := conjSU h P hP with hc
  set A' := A.map (c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)) with hA'
  have hA'ab : IsElemAbelian p A' := by
    have := isElemAbelian_range (H := A) (p := p)
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
      (fun a => Subtype.ext (by simpa using hA.2 a a.2))
      ((c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)).comp A.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hdiag' : ∀ x ∈ A', ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiag x hx
  have hcard' : Nat.card A' = Nat.card Ab := by
    rw [hA', ← hcardA]
    exact (Nat.card_congr (A.equivMapOfInjective _ c.injective).toEquiv).symm
  set cR := conjProj h P hP with hcR
  have hmap' : A'.map π = Ab.map (cR : LargeEvenProj (unitarySU 2 n K d) →*
      LargeEvenProj (unitarySU 2 n K d)) := by
    rw [← hmap, hA', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  set U' := U.map (cR : LargeEvenProj (unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d))
    with hU'
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have h1 : cR u ∈ U' := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact cR.injective (h1.trans (map_one cR).symm)
  have hBU' : A'.map π ≤ Subgroup.normalizer (U' : Set _) := by
    rw [hmap']
    exact (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map _)
  obtain ⟨s, t, hst, hpairF⟩ := SURepair.exists_framePair_of_twoSubgroup h
    (ker_projMk_le_center (n := n) (d := d) (K := K)) hU'1 (hU2.map _)
    (fun u _ => QuotientGroup.mk'_surjective _ u) hBU'
  have hpair : ∀ σ ∈ diagVec A', σ s = σ t := by
    intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp hσ
    obtain ⟨hpow, -⟩ := diagVec_props h hA'ab hσ
    refine hpairF (π x) ⟨x, hx, rfl⟩ σ ⟨fun i => ?_, fun u u' hu' => ?_⟩
    · obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hpow i, Units.val_one, one_pow]
    · have hu'' : u' = x * u * x⁻¹ := by
        apply Subtype.ext
        rw [hu', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxσ]
      rw [hu'', map_mul, map_mul, map_inv]
  obtain ⟨t₀, hend, U₀, hU₀J, hU₀1, hU₀2, hAU₀⟩ := exists_rootEndNode_diag h hK hp hpq hpd hd hq
    hA'ab hdiag' (hcard' ▸ hr) hst hpair
  rw [hmap'] at hend hAU₀
  have hid : cR.symm.toMonoidHom.comp
      (cR : LargeEvenProj (unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d)) =
        MonoidHom.id _ := by
    ext x
    simp
  have hAbeq : (Ab.map (cR : LargeEvenProj (unitarySU 2 n K d) →*
      LargeEvenProj (unitarySU 2 n K d))).map cR.symm.toMonoidHom = Ab := by
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  have hend' := hend.map cR.symm
  rw [hAbeq] at hend'
  have hC : Subgroup.centralizer ({cR.symm t₀} : Set (LargeEvenProj (unitarySU 2 n K d))) =
      (Subgroup.centralizer ({t₀} : Set _)).map cR.symm.toMonoidHom :=
    (TableBSymp.map_centralizer_singleton cR.symm t₀).symm
  have hL : LargeEvenLayer
      (Subgroup.centralizer ({cR.symm t₀} : Set (LargeEvenProj (unitarySU 2 n K d)))) =
      (LargeEvenLayer (Subgroup.centralizer ({t₀} : Set _))).map cR.symm.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective cR.symm.toMonoidHom cR.symm.injective]
  refine ⟨cR.symm t₀, hend', U₀.map cR.symm.toMonoidHom, ?_, ?_, hU₀2.map _, ?_⟩
  · rw [hL]
    exact Subgroup.map_mono hU₀J
  · intro hbot
    apply hU₀1
    rw [eq_bot_iff]
    intro u hu
    have h1 : cR.symm u ∈ U₀.map cR.symm.toMonoidHom := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact cR.symm.injective (h1.trans (map_one cR.symm).symm)
  · rw [← hAbeq]
    exact (Subgroup.map_mono hAU₀).trans (Subgroup.le_normalizer_map _)

end Diag

end IOneU

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
theorem ggEndNodeRootElt_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d) :
    GGEndNodeRootElt p (d - 2) (LargeEvenProj (unitarySU 2 n K d)) :=
  fun _ hA hr _ hU => IOneU.exists_rootEndNode_unitary h hK hp hpq hpd hd hq hA hr hU

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial in
theorem ggEndNodeRoot_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hp3 : p ≠ 3) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d) :
    GGEndNodeRoot p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : d = 3 := congrArg Prod.fst he
    omega
  exact ggEndNodeRoot_of_elt
    (fun φ hφ hφp => TableBUE.mem_range_conj_of_pow_eq_one h hK (by omega) hdq hp hpq hpd hφ hφp)
    (TableBUE.center_proj_eq_bot hK (by omega) hdq) hp3
    (ggEndNodeRootElt_unitary h hK hp hpq hpd hd hq)

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial in
theorem ggEndNodeIOne_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hp3 : p ≠ 3) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d)
    (hZ : GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    GGEndNodeIOne p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : d = 3 := congrArg Prod.fst he
    omega
  exact ggEndNodeIOne_of_root_prime (ggEndNodeRoot_unitary h hK hp hpq hpd hp3 hd hq)
    (fun φ hφ hφp => TableBUE.mem_range_conj_of_pow_eq_one h hK (by omega) hdq hp hpq hpd hφ hφp)
    hZ

end CFSG.StandardType
