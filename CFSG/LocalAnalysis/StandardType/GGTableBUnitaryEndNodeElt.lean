module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvdComb

public section

namespace CFSG.StandardType

namespace TableBUE

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.SectionRank.OddCover

section Ratio

variable {K : Type} [Field K] {d : ℕ}

@[expose] def ratioHom (k₀ : Fin d) : (Fin d → Kˣ) →* (Fin d → Kˣ) where
  toFun σ k := σ k * (σ k₀)⁻¹
  map_one' := by
    funext k
    simp
  map_mul' σ τ := by
    funext k
    simp only [Pi.mul_apply, mul_inv]
    rw [mul_mul_mul_comm]

theorem ratioHom_apply (k₀ : Fin d) (σ : Fin d → Kˣ) (k : Fin d) :
    ratioHom k₀ σ k = σ k * (σ k₀)⁻¹ :=
  rfl

theorem ratioHom_self (k₀ : Fin d) (σ : Fin d → Kˣ) : ratioHom k₀ σ k₀ = 1 :=
  mul_inv_cancel _

theorem ratioHom_eq_iff (k₀ : Fin d) (σ : Fin d → Kˣ) (k l : Fin d) :
    ratioHom k₀ σ k = ratioHom k₀ σ l ↔ σ k = σ l := by
  rw [ratioHom_apply, ratioHom_apply, mul_left_inj]

end Ratio

section Diag

variable {K : Type} [Field K] {n d p : ℕ}

@[expose] noncomputable def diagVec (A : Subgroup ↥(unitarySU 2 n K d)) : Subgroup (Fin d → Kˣ) :=
  (A.map (unitarySU 2 n K d).subtype).comap (diagHom d)

theorem mem_diagVec {A : Subgroup ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ} :
    σ ∈ diagVec A ↔ ∃ x ∈ A, (x : GL (Fin d) K) = diagHom d σ := by
  simp [diagVec, Subgroup.mem_map]

theorem mem_diagVec_of {A : Subgroup ↥(unitarySU 2 n K d)} {x : ↥(unitarySU 2 n K d)} (hx : x ∈ A)
    {σ : Fin d → Kˣ} (hσ : (x : GL (Fin d) K) = diagHom d σ) : σ ∈ diagVec A :=
  mem_diagVec.mpr ⟨x, hx, hσ⟩

theorem diagVec_props (h : UnitaryFieldData 2 n K) {A : Subgroup ↥(unitarySU 2 n K d)}
    (hA : IsElemAbelian p A) {σ : Fin d → Kˣ} (hσ : σ ∈ diagVec A) :
    (∀ k, σ k ^ p = 1) ∧ ∏ k, (σ k : K) = 1 := by
  obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp hσ
  refine ⟨fun k => ?_, ?_⟩
  · have h1 : diagHom d (σ ^ p) = 1 := by
      rw [map_pow, ← hxσ, ← Subgroup.coe_pow, hA.2 x hx]
      rfl
    have h2 := diagHom_injective d (h1.trans (map_one _).symm)
    exact congrFun h2 k
  · have h1 := ((mem_unitarySU_iff h).mp x.2).1
    rwa [hxσ, det_diagHom] at h1

theorem card_diagVec {A : Subgroup ↥(unitarySU 2 n K d)}
    (hdiag : ∀ x ∈ A, ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ) :
    Nat.card (diagVec A) = Nat.card A := by
  have hmap : (diagVec A).map (diagHom d) = A.map (unitarySU 2 n K d).subtype := by
    apply le_antisymm
    · rintro _ ⟨σ, hσ, rfl⟩
      exact hσ
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨σ, hσ⟩ := hdiag x hx
      exact ⟨σ, mem_diagVec_of hx hσ, hσ.symm⟩
  rw [← Nat.card_congr ((diagVec A).equivMapOfInjective _ (diagHom_injective d)).toEquiv.symm,
    hmap, ← Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv]

theorem eq_one_of_ratioHom (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hpd : ¬ p ∣ d)
    {A : Subgroup ↥(unitarySU 2 n K d)} (hA : IsElemAbelian p A) (k₀ : Fin d)
    {σ : Fin d → Kˣ} (hσ : σ ∈ diagVec A) (h1 : ratioHom k₀ σ = 1) : σ = 1 := by
  obtain ⟨hpow, hprod⟩ := diagVec_props h hA hσ
  have hc : ∀ k, σ k = σ k₀ := fun k => by
    have := congrFun h1 k
    rwa [ratioHom_apply, Pi.one_apply, mul_inv_eq_one] at this
  have hd : (σ k₀) ^ d = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hprod,
      Finset.prod_congr rfl fun k _ => congrArg Units.val (hc k), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hgcd : Nat.gcd d p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
  have h1' := pow_gcd_eq_one.mpr ⟨hd, hpow k₀⟩
  rw [hgcd, pow_one] at h1'
  funext k
  rw [hc k, h1']
  rfl

end Diag

section Node

variable {K : Type} [Field K] [Finite K] {d p : ℕ}

theorem exists_node_ratio (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    {Y : Subgroup (Fin d → Kˣ)} (hY0 : ∀ y ∈ Y, y ⟨3, by omega⟩ = 1)
    (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K) (hcard : p ^ (d - 2) ≤ Nat.card Y)
    (hcard3 : p ^ 3 ≤ Nat.card Y) :
    ∃ y ∈ Y, y ≠ 1 ∧ ∃ T : Finset (Fin d), T.card ≤ 2 ∧ (d = 4 → T.card ≤ 1) ∧
      (∀ i ∈ T, ∀ j, j ≠ i → y j ≠ y i) ∧ (∀ k l, k ∉ T → l ∉ T → y k = y l) ∧
      ∀ y' ∈ Y, (∀ k l, k ∉ T → l ∉ T → y' k = y' l) → y' ∈ Subgroup.zpowers y := by
  classical
  by_cases hd5 : 5 ≤ d
  · obtain ⟨y, hyY, hy1, T, -, hT2, hT⟩ := TypeA.exists_node hp hp2 hpK hd5 hY0 hYp hcard
    exact ⟨y, hyY, hy1, T, hT2, fun h4 => absurd h4 (by omega), hT⟩
  have hd4 : d = 4 := by omega
  subst hd4
  have hex : ∃ y ∈ Y, y ≠ 1 ∧ y 1 = 1 ∧ y 2 = 1 := by
    by_contra hne
    push Not at hne
    let f : Y → rootsOfUnity p K × rootsOfUnity p K := fun y =>
      (⟨y.1 1, hYp y.1 y.2 1⟩, ⟨y.1 2, hYp y.1 y.2 2⟩)
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : a.1 1 = b.1 1 := congrArg (fun z => ((z.1 : Kˣ))) hab
      have h2 : a.1 2 = b.1 2 := congrArg (fun z => ((z.2 : Kˣ))) hab
      have hab' : (a.1 * b.1⁻¹) = 1 := by
        by_contra hc
        have := hne _ (Y.mul_mem a.2 (Y.inv_mem b.2)) hc
        apply this <;> simp [h1, h2]
      exact Subtype.ext (mul_inv_eq_one.mp hab')
    have hle := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, TypeA.card_rootsOfUnity_of_dvd hp hpK] at hle
    have : p * p < p ^ 3 := by
      have h2 := hp.two_le
      nlinarith
    omega
  obtain ⟨y, hyY, hy1, hy1', hy2'⟩ := hex
  have hy3 := hY0 y hyY
  have hyc : ∀ k l : Fin 4, k ≠ 0 → l ≠ 0 → y k = y l := by
    have hval : ∀ k : Fin 4, k ≠ 0 → y k = 1 := by
      intro k hk
      fin_cases k
      · exact absurd rfl hk
      · exact hy1'
      · exact hy2'
      · exact hy3
    intro k l hk hl
    rw [hval k hk, hval l hl]
  obtain ⟨h1, h2⟩ := TypeA.node_of_single hp hpK hY0 hYp (i := 0) (m := 1) (by decide) hyY hy1
    hyc
  refine ⟨y, hyY, hy1, {0}, by simp, fun _ => by simp, ?_, ?_, ?_⟩
  · intro i hi j hj
    rw [Finset.mem_singleton] at hi
    subst hi
    exact h1 j hj
  · intro k l hk hl
    exact hyc k l (by simpa using hk) (by simpa using hl)
  · intro y' hy' hc'
    exact h2 y' hy' fun k l hk hl => hc' k l (by simpa using hk) (by simpa using hl)

end Node

section EndNode

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)

omit [Finite K] in
theorem ker_projMk_le_center :
    (LargeEvenProjMk (unitarySU 2 n K d)).ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro z hz
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hz g)

omit [Field K] [Finite K] in
theorem dvd_card_sub_one (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) :
    p ∣ Nat.card K - 1 := by
  rw [hK, sq, show 2 ^ n * 2 ^ n - 1 = 2 ^ n * 2 ^ n - 1 * 1 by rw [mul_one],
    Nat.mul_self_sub_mul_self_eq]
  exact Dvd.dvd.mul_right hpq _

include h in
theorem exists_isEndNode_diag (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d)
    {A : Subgroup ↥(unitarySU 2 n K d)} (hA : IsElemAbelian p A)
    (hdiag : ∀ x ∈ A, ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ)
    (hcard : p ^ (d - 2) ≤ Nat.card A) (hcard3 : p ^ 3 ≤ Nat.card A) :
    ∃ t, TableBOrth.IsEndNode (A.map (LargeEvenProjMk (unitarySU 2 n K d))) t := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  have hpK := dvd_card_sub_one hK hpq
  set k₀ : Fin d := ⟨3, by omega⟩ with hk₀
  set W := diagVec A with hW
  set Y := W.map (ratioHom k₀) with hY
  have hWinj : ∀ σ ∈ W, ratioHom k₀ σ = 1 → σ = 1 := fun σ hσ h1 =>
    eq_one_of_ratioHom h hp hpd hA k₀ hσ h1
  have hYcard : Nat.card Y = Nat.card A := by
    have hinj : Function.Injective ((ratioHom k₀).comp W.subtype) := by
      rw [injective_iff_map_eq_one]
      intro σ hσ
      exact Subtype.ext (hWinj σ σ.2 hσ)
    rw [hY, show W.map (ratioHom k₀) = ((ratioHom k₀).comp W.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype],
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_diagVec hdiag]
  have hY0 : ∀ y ∈ Y, y k₀ = 1 := by
    rintro _ ⟨σ, -, rfl⟩
    exact ratioHom_self k₀ σ
  have hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K := by
    rintro _ ⟨σ, hσ, rfl⟩ k
    obtain ⟨hpow, -⟩ := diagVec_props h hA hσ
    rw [mem_rootsOfUnity, ratioHom_apply, mul_pow, hpow k, inv_pow, hpow k₀, inv_one, mul_one]
  obtain ⟨y, ⟨σ, hσW, rfl⟩, hy1, T, hT2, hT4, hTi, hTc, hTpow⟩ :=
    exists_node_ratio hp hp2 hpK hd hY0 hYp (hYcard ▸ hcard) (hYcard ▸ hcard3)
  obtain ⟨x, hxA, hxσ⟩ := mem_diagVec.mp hσW
  set S : Finset (Fin d) := Tᶜ with hSdef
  have hSnode : IsNodeOn σ S := by
    refine ⟨fun i hi j hj => (ratioHom_eq_iff k₀ σ i j).mp
      (hTc i j (Finset.mem_compl.mp hi) (Finset.mem_compl.mp hj)), fun i hi j hj => ?_⟩
    have hiT : i ∈ T := by simpa [hSdef] using hi
    exact fun he => hTi i hiT j hj ((ratioHom_eq_iff k₀ σ j i).mpr he)
  have hScard : S.card = d - T.card := by
    rw [hSdef, Finset.card_compl, Fintype.card_fin]
  have hS3 : 3 ≤ S.card := by
    rw [hScard]
    by_cases h4 : d = 4
    · have := hT4 h4
      omega
    · omega
  have hSq : (S.card, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : S.card = 3 := congrArg Prod.fst he
    have h2 : 2 ^ n = 2 := congrArg Prod.snd he
    rcases hq with hq | hq
    · omega
    · omega
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  have hker := ker_projMk_le_center (n := n) (d := d) (K := K)
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hy1
    have h1 : diagHom d σ = 1 := by rw [← hxσ]; rfl
    rw [diagHom_injective d (h1.trans (map_one _).symm), map_one]
  refine ⟨π x, isEndNode_map_of_cover π hker (fun y' hy' hy1' => hnp y' hy1' (hA.2 y' hy'))
    hxA hx1 (isQuasisimple_blockSU S h hK hS3 hSq) (blockSU_le_centralizer hSnode.1 hxσ)
    (fun g hg g' hg' => commutator_mem_blockSU hSnode hxσ hg hg')
    (centralizer_map_eq_of_noTorsion π (QuotientGroup.mk'_surjective _) hker hnp (hA.2 x hxA))
    fun y' hy' => ?_⟩
  obtain ⟨σ', hσ'⟩ := hdiag y' hy'
  rw [commute_blockSU_iff h hσ']
  constructor
  · intro hc
    have hmem := hTpow (ratioHom k₀ σ') ⟨σ', mem_diagVec_of hy' hσ', rfl⟩ fun k l hk hl =>
      (ratioHom_eq_iff k₀ σ' k l).mpr (hc k (Finset.mem_compl.mpr hk) l (Finset.mem_compl.mpr hl))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hσm : σ' = σ ^ m := by
      have h1 := hWinj (σ' * (σ ^ m)⁻¹) (W.mul_mem (mem_diagVec_of hy' hσ')
        (W.inv_mem (W.zpow_mem hσW m))) (by rw [map_mul, map_inv, map_zpow, hm, mul_inv_cancel])
      exact mul_inv_eq_one.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, hxσ, hσ', hσm, map_zpow]
  · intro hmem i hi j hj
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hσm : σ' = σ ^ m := by
      apply diagHom_injective d
      rw [← hσ', map_zpow, ← hxσ, Subgroup.coe_zpow]
    rw [hσm, Pi.pow_apply, Pi.pow_apply, hSnode.1 i hi j hj]

include h in
theorem card_le_of_diag_three (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    {A : Subgroup ↥(unitarySU 2 n K 3)} (hA : IsElemAbelian p A)
    (hdiag : ∀ x ∈ A, ∃ σ : Fin 3 → Kˣ, (x : GL (Fin 3) K) = diagHom 3 σ) :
    Nat.card A ≤ p * p := by
  rw [← card_diagVec hdiag]
  set W := diagVec A
  let f : W → rootsOfUnity p K × rootsOfUnity p K := fun σ =>
    (⟨σ.1 0, by rw [mem_rootsOfUnity]; exact (diagVec_props h hA σ.2).1 0⟩,
      ⟨σ.1 1, by rw [mem_rootsOfUnity]; exact (diagVec_props h hA σ.2).1 1⟩)
  have hf : Function.Injective f := by
    intro a b hab
    have h0 : a.1 0 = b.1 0 := congrArg (fun z => ((z.1 : Kˣ))) hab
    have h1 : a.1 1 = b.1 1 := congrArg (fun z => ((z.2 : Kˣ))) hab
    have ha := (diagVec_props h hA a.2).2
    have hb := (diagVec_props h hA b.2).2
    rw [Fin.prod_univ_three] at ha hb
    have h2 : a.1 2 = b.1 2 := by
      apply Units.ext
      have hne : ((a.1 0 : Kˣ) : K) * (a.1 1 : K) ≠ 0 :=
        mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
      apply mul_left_cancel₀ hne
      rw [ha, h0, h1, hb]
    apply Subtype.ext
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, TypeA.card_rootsOfUnity_of_dvd hp hpK] at hle

include h in
theorem ggEndNodeElt_unitary (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 3 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d) :
    GGEndNodeElt p (d - 2) (LargeEvenProj (unitarySU 2 n K d)) := by
  intro Ab hAb hr h3
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
  by_cases hd3 : d = 3
  · exfalso
    subst hd3
    have hle := card_le_of_diag_three h hp (dvd_card_sub_one hK hpq) hA'ab hdiag'
    rw [hcard'] at hle
    have : p * p < p ^ 3 := by
      have h2 := hp.two_le
      nlinarith
    omega
  obtain ⟨t, ht⟩ := exists_isEndNode_diag h hK hp hpq hpd (by omega) hq hA'ab hdiag'
    (hcard' ▸ hr) (hcard' ▸ h3)
  set cR := conjProj h P hP with hcR
  have hmap' : A'.map π = Ab.map (cR : LargeEvenProj (unitarySU 2 n K d) →*
      LargeEvenProj (unitarySU 2 n K d)) := by
    rw [← hmap, hA', Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap'] at ht
  have ht' := ht.map cR.symm
  rw [Subgroup.map_map] at ht'
  have hid : cR.symm.toMonoidHom.comp
      (cR : LargeEvenProj (unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d)) =
        MonoidHom.id _ := by
    ext x
    simp
  rw [hid, Subgroup.map_id] at ht'
  obtain ⟨h1, h2, h3, h4⟩ := ht'
  exact ⟨_, h1, h2, h3, h4⟩

end EndNode

end TableBUE

end CFSG.StandardType
