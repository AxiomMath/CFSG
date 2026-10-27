module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffStd
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffLine
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Chevalley (torusTorsion)

private lemma isElemAbelian_map_congr {L G : Type*} [Group L] [Group G]
    (e : L ≃* G) {A : Subgroup (MulAut L)} (hA : IsElemAbelian 3 A) :
    IsElemAbelian 3 (A.map (MulAut.congr e).toMonoidHom) := by
  constructor
  · rw [isMulCommutative_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [Subgroup.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a * b = b * a :=
      congrArg Subtype.val ((isMulCommutative_iff.mp hA.1) ⟨a, ha⟩ ⟨b, hb⟩)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hab]
  · rintro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_pow, hA.2 a ha, map_one]

private lemma congr_apply_apply {L G : Type*} [Group L] [Group G] (e : L ≃* G)
    (a : MulAut L) (m : G) : MulAut.congr e a m = e (a (e.symm m)) := by
  simp [MulAut.congr_apply, MulEquiv.trans_apply]

private lemma ggFix_map_congr {L G : Type*} [Group L] [Group G] (e : L ≃* G)
    (a : MulAut L) :
    (ggFix a).map (e : L →* G) = ggFix (MulAut.congr e a) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ggFix] at hx ⊢
    have := congrArg e hx
    simpa [congr_apply_apply] using this
  · intro hg
    refine ⟨e.symm g, ?_, by simp⟩
    rw [mem_ggFix] at hg ⊢
    apply e.injective
    rw [show e (a (e.symm g)) = MulAut.congr e a g from (congr_apply_apply e a g).symm,
      MulEquiv.apply_symm_apply]
    exact hg

private lemma card_ggFix_congr {L G : Type*} [Group L] [Group G] (e : L ≃* G)
    (a : MulAut L) :
    Nat.card (ggFix (MulAut.congr e a)) = Nat.card (ggFix a) := by
  rw [← ggFix_map_congr e a]
  exact Subgroup.card_map_of_injective (f := (e : L →* G)) (K := ggFix a) e.injective

private lemma ggFix_conj_eq_centralizer {L : Type*} [Group L] (l : L) :
    ggFix (MulAut.conj l) = Subgroup.centralizer ({l} : Set L) := by
  ext h
  rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private lemma conj_mul_apply_conj {G : Type*} [Group G] (x : G) (α : MulAut G) (y : G) :
    (MulAut.conj x * α * (MulAut.conj x)⁻¹) (x * y * x⁻¹) = x * α y * x⁻¹ := by
  have h1 : (MulAut.conj x : MulAut G)⁻¹ = MulAut.conj x⁻¹ :=
    (map_inv (MulAut.conj : G →* MulAut G) x).symm
  rw [MulAut.mul_apply, MulAut.mul_apply, h1, MulAut.conj_apply, MulAut.conj_apply]
  group

private lemma conj_mul_apply_conj_inv {G : Type*} [Group G] (x : G) (α : MulAut G) (w : G) :
    α (x⁻¹ * w * x) = x⁻¹ * ((MulAut.conj x * α * (MulAut.conj x)⁻¹) w) * x := by
  have h := conj_mul_apply_conj x α (x⁻¹ * w * x)
  have h1 : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
  rw [h1] at h
  rw [h]
  group

private noncomputable def conjCongrHom {L G : Type*} [Group L] [Group G] (e : L ≃* G)
    (x : G) : MulAut L →* MulAut G :=
  (MulAut.conj (MulAut.conj x)).toMonoidHom.comp (MulAut.congr e).toMonoidHom

private lemma conjCongrHom_conj {L G : Type*} [Group L] [Group G] (e : L ≃* G) (x : G)
    (m : L) : conjCongrHom e x (MulAut.conj m) = MulAut.conj (x * e m * x⁻¹) := by
  simp only [conjCongrHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, congr_mulAutConj, mul_mulAutConj_mul_inv]

private abbrev T3 {K : Type} [Field K] (z : adjointGroup Tag.G2 K) : Prop :=
  (z : ModGL Tag.G2 K) ∈ torusTorsion K 3

private lemma T3_pow_three
    {K : Type} [Field K] {z : adjointGroup Tag.G2 K}
    (hz : T3 z) : z ^ 3 = 1 :=
  Subtype.ext (by
    rw [SubgroupClass.coe_pow, Subgroup.coe_one]
    exact (CFSG.RankThree.Chevalley.mem_torusTorsion_iff.mp hz).2)

private lemma T3_mul {K : Type} [Field K] {u v : adjointGroup Tag.G2 K}
    (hu : T3 u) (hv : T3 v) : T3 (u * v) := by
  show ((u * v : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈ torusTorsion K 3
  rw [Subgroup.coe_mul]
  exact Subgroup.mul_mem _ hu hv

private lemma T3_inv {K : Type} [Field K] {u : adjointGroup Tag.G2 K} (hu : T3 u) :
    T3 u⁻¹ := by
  show ((u⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈ torusTorsion K 3
  rw [Subgroup.coe_inv]
  exact Subgroup.inv_mem _ hu

private lemma torusTorsion_comm
    {K : Type} [Field K] {u v : ModGL Tag.G2 K}
    (hu : u ∈ torusTorsion K 3) (hv : v ∈ torusTorsion K 3) : u * v = v * u := by
  haveI : CFSG.IsElementaryAbelian 3 (torusTorsion K 3) :=
    CFSG.RankThree.Chevalley.isElementaryAbelian_torusTorsion 3
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

private lemma T3_comm
    {K : Type} [Field K] {u v : adjointGroup Tag.G2 K}
    (hu : T3 u) (hv : T3 v) : u * v = v * u :=
  Subtype.ext (torusTorsion_comm (K := K) hu hv)

private lemma inv_mul_pow_three_conj {G : Type*} [Group G] (x c : G) :
    (x⁻¹ * c * x) ^ 3 = x⁻¹ * c ^ 3 * x := by
  rw [show x⁻¹ * c * x = (MulAut.conj x⁻¹) c by rw [MulAut.conj_apply, inv_inv], ← map_pow,
    MulAut.conj_apply, inv_inv]

private lemma g2FieldHom_pow_apply_eq
    {K : Type} [Field K] (σ : K ≃+* K)
    {u : adjointGroup Tag.G2 K} (hu : g2FieldHom K σ u = u) (k : ℕ) :
    (g2FieldHom K σ ^ k) u = u := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hu]

theorem ggNbrG2Off_weyl_set
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h6 : 6 ∣ n) {L' : Type} [Group L'] (e : L' ≃* adjointGroup Tag.G2 K)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) :
    ∃ W : Set L',
      (∀ m ∈ W, ∀ a ∈ A, (m * (a m)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (m * (a m)⁻¹) = m * (a m)⁻¹) ∧
      ∀ a₀ ∈ A, a₀ ≠ 1 → a₀ ∈ (MulAut.conj : L' →* MulAut L').range →
        Nat.card (ggFix a₀) ≠ Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) →
          ∃ m ∈ W, MulAut.conj m * a₀ * (MulAut.conj m)⁻¹ ∉ Subgroup.zpowers a₀ := by
  classical
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    rw [hn0, pow_zero] at hK
    have h2 : 2 ≤ Nat.card K := by
      haveI := Fintype.ofFinite K
      have hlt := Fintype.one_lt_card (α := K)
      rw [Nat.card_eq_fintype_card]
      omega
    omega
  have hn6 : 6 ≤ n := Nat.le_of_dvd hnpos h6
  have hchar : ringChar K ≠ 3 := by
    haveI : CharP K 2 := charP_two_of_card hK
    rw [ringChar.eq K 2]
    norm_num
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
  have h3 : 3 ∣ Nat.card K - 1 := by
    obtain ⟨t, ht⟩ := h6
    have hK' : Nat.card K = 4 ^ (3 * t) := by
      have h1 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [hK, ht, h1, ← pow_mul]
      congr 1
      ring
    rw [hK']
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 (3 * t)
  let G := adjointGroup Tag.G2 K
  let A' : Subgroup (MulAut G) := A.map (MulAut.congr e).toMonoidHom
  have hA' : IsElemAbelian 3 A' := isElemAbelian_map_congr e hA
  have h27' : 27 ≤ Nat.card A' := by
    show 27 ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom)
    rw [Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom) (K := A)
      (MulAut.congr e).injective]
    exact h27
  obtain ⟨σ, x, hσ, H⟩ := ggNbrG2Off_stdForm hK h6 A' hA' h27'
  have hcenter : Subgroup.center G = ⊥ := center_adjointGroup_eq_bot
  let W' : Set G := {w | g2FieldHom K σ w = w ∧
    ∀ y : G, T3 y → T3 (w * y * w⁻¹)}
  let W : Set L' := {m | ∃ w ∈ W', e m = x⁻¹ * w * x}
  refine ⟨W, ?_, ?_⟩
  ·
    intro m hm a ha
    obtain ⟨w, hwW', hmw⟩ := hm
    obtain ⟨hwφ, hwn⟩ := hwW'
    have hαmem : MulAut.congr e a ∈ A' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨z, j, hzT, hzφ, hαeq⟩ := H (MulAut.congr e a) hαmem
    have heam : e (a m) = x⁻¹ * (z * w * z⁻¹) * x := by
      have h1 : e (a m) = (MulAut.congr e a) (e m) := by
        rw [congr_apply_apply, MulEquiv.symm_apply_apply]
      rw [h1, hmw, conj_mul_apply_conj_inv, hαeq]
      rw [MulAut.mul_apply, MulAut.conj_apply, g2FieldHom_pow_apply_eq σ hwφ j]
    have hcT : T3 (w * z * w⁻¹ * z⁻¹) := T3_mul (hwn z hzT) (T3_inv hzT)
    have hc3 : (w * z * w⁻¹ * z⁻¹) ^ 3 = 1 := T3_pow_three hcT
    have hecom : e (m * (a m)⁻¹) = x⁻¹ * (w * z * w⁻¹ * z⁻¹) * x := by
      rw [map_mul, map_inv, heam, hmw]
      group
    constructor
    ·
      apply e.injective
      rw [map_pow, map_one, hecom, inv_mul_pow_three_conj, hc3]
      group
    ·
      intro a' ha'
      obtain ⟨z', j', hz'T, hz'φ, hα'eq⟩ :=
        H (MulAut.congr e a') (Subgroup.mem_map.mpr ⟨a', ha', rfl⟩)
      apply e.injective
      have hea' : e (a' (m * (a m)⁻¹)) =
          x⁻¹ * (z' * ((g2FieldHom K σ ^ j') (w * z * w⁻¹ * z⁻¹)) * z'⁻¹) * x := by
        have h1 : e (a' (m * (a m)⁻¹)) = (MulAut.congr e a') (e (m * (a m)⁻¹)) := by
          rw [congr_apply_apply, MulEquiv.symm_apply_apply]
        rw [h1, hecom, conj_mul_apply_conj_inv, hα'eq]
        rw [MulAut.mul_apply, MulAut.conj_apply]
      rw [hea', hecom]
      have hφc : g2FieldHom K σ (w * z * w⁻¹ * z⁻¹) = w * z * w⁻¹ * z⁻¹ := by
        simp only [map_mul, map_inv, hwφ, hzφ]
      have hφ'c : (g2FieldHom K σ ^ j') (w * z * w⁻¹ * z⁻¹) = w * z * w⁻¹ * z⁻¹ :=
        g2FieldHom_pow_apply_eq σ hφc j'
      rw [hφ'c, T3_comm hz'T hcT]
      group
  ·
    intro a₀ ha₀ ha₀ne ha₀inn hN
    obtain ⟨l₀, rfl⟩ := ha₀inn
    have hαmem : MulAut.congr e (MulAut.conj l₀) ∈ A' :=
      Subgroup.mem_map.mpr ⟨MulAut.conj l₀, ha₀, rfl⟩
    obtain ⟨z, j, hzT, hzφ, hαeq⟩ := H (MulAut.congr e (MulAut.conj l₀)) hαmem
    have hαeq' : MulAut.conj (x * e l₀ * x⁻¹) = MulAut.conj z * g2FieldHom K σ ^ j := by
      rw [congr_mulAutConj, mul_mulAutConj_mul_inv, MulAut.conj_apply] at hαeq
      exact hαeq
    have hinner : IsInnerAut (g2FieldHom K σ ^ j) := by
      have h1 : IsInnerAut (MulAut.conj z * g2FieldHom K σ ^ j) := by
        rw [← hαeq']
        exact isInnerAut_conj _
      have h2 : (MulAut.conj z * g2FieldHom K σ ^ j) ∈
          (MulAut.conj : G →* MulAut G).range := h1
      have h3 : (MulAut.conj z) ∈ (MulAut.conj : G →* MulAut G).range := isInnerAut_conj z
      have h4 : (g2FieldHom K σ ^ j) ∈ (MulAut.conj : G →* MulAut G).range := by
        have h4' := Subgroup.mul_mem _ (Subgroup.inv_mem _ h3) h2
        rwa [inv_mul_cancel_left] at h4'
      exact h4
    have hσj : σ ^ j = 1 := (g2_automorphism_normal_form hchar h4).2 (σ ^ j) (by
      rw [map_pow]
      exact hinner)
    have hφj : g2FieldHom K σ ^ j = 1 := by
      rw [← map_pow, hσj, map_one]
    have hconj : MulAut.conj (x * e l₀ * x⁻¹) = MulAut.conj z := by
      rw [hαeq', hφj, mul_one]
    have hxel0 : x * e l₀ * x⁻¹ = z := mulAut_conj_injective hcenter hconj
    have hz1 : z ≠ 1 := by
      intro hz
      have hel0 : e l₀ = 1 := by
        have h1 : x * e l₀ * x⁻¹ = 1 := by rw [hxel0, hz]
        calc e l₀ = x⁻¹ * (x * e l₀ * x⁻¹) * x := by group
          _ = x⁻¹ * 1 * x := by rw [h1]
          _ = 1 := by group
      have hl0 : l₀ = 1 := e.injective (by rw [hel0]; exact (map_one e).symm)
      exact ha₀ne (by rw [hl0]; exact map_one (MulAut.conj : L' →* MulAut L'))
    have hcard_e : Nat.card (ggFix (MulAut.conj (e l₀))) =
        Nat.card (ggFix (MulAut.conj l₀)) := by
      rw [← congr_mulAutConj e l₀]
      exact card_ggFix_congr e (MulAut.conj l₀)
    have hcard : Nat.card (ggFix (MulAut.conj l₀)) =
        Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := by
      rw [← hcard_e, ggFix_conj_eq_centralizer, ← hxel0]
      exact Nat.card_congr
        (CFSG.RankThree.PartTwo.Sec4.E27.centralizerConjEquiv x (e l₀)).toEquiv
    have hC : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) ≠
        Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
      rw [← hcard]
      exact hN
    obtain ⟨w, hwφ, hwn, hwz⟩ := ggNbrG2Off_torsion_moved h3 σ hzT hz1 hC
    have hwW' : w ∈ W' := ⟨hwφ, hwn⟩
    set m : L' := e.symm (x⁻¹ * w * x) with hm_def
    refine ⟨m, ?_, ?_⟩
    · refine ⟨w, hwW', ?_⟩
      rw [hm_def, MulEquiv.apply_symm_apply]
    · rintro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hem : e m = x⁻¹ * w * x := by rw [hm_def, MulEquiv.apply_symm_apply]
      have hΘm : conjCongrHom e x (MulAut.conj m) = MulAut.conj w := by
        rw [conjCongrHom_conj, hem]
        congr 1
        group
      have hΘl : conjCongrHom e x (MulAut.conj l₀) = MulAut.conj z := by
        rw [conjCongrHom_conj, hxel0]
      have happ := congrArg (conjCongrHom e x) hk
      rw [map_zpow, map_mul, map_mul, map_inv, hΘm, hΘl] at happ
      rw [mul_mulAutConj_mul_inv, MulAut.conj_apply] at happ
      rw [← map_zpow] at happ
      have hwzz : z ^ k = w * z * w⁻¹ := mulAut_conj_injective hcenter happ
      exact hwz (Subgroup.mem_zpowers_iff.mpr ⟨k, hwzz⟩)

end CFSG.StandardType

end
