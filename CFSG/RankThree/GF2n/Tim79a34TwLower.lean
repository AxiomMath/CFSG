module

public import CFSG.RankThree.GF2n.Tim79a34TwDefs
public import CFSG.RankThree.GF2n.Tim79a34SpFacts

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.LieType.Universal.Symplectic Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem twl_gf2 (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases key (GaloisField.equivZmodP 2 c) with h | h
  · left
    apply (GaloisField.equivZmodP 2).injective
    rw [h, map_zero]
  · right
    apply (GaloisField.equivZmodP 2).injective
    rw [h, map_one]

theorem twl_unit_ne_zero {n : ℕ} (i : Fin n ⊕ Fin n) :
    (Pi.single i (1 : GaloisField 2 1) : Fin n ⊕ Fin n → GaloisField 2 1) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

theorem twl_spTrans_one_ne_one {n : ℕ} {v : Fin n ⊕ Fin n → GaloisField 2 1} (hv : v ≠ 0) :
    CaseM.spTrans v 1 ≠ 1 := by
  intro h
  obtain ⟨w, hw⟩ := ModelRank.exists_spForm_ne_zero hv
  have h1 : CaseM.spTrans v 1 *ᵥ w = w := by rw [h, Matrix.one_mulVec]
  rw [ModelRank.spTrans_mulVec, one_mul] at h1
  rcases smul_eq_zero.mp (add_eq_left.mp h1) with h4 | h4
  · exact hw h4
  · exact hv h4

theorem twl_spForm_inl {n : ℕ} (v : Fin n ⊕ Fin n → GaloisField 2 1) (i : Fin n) :
    CaseM.spForm v (Pi.single (Sum.inl i) 1) = -v (Sum.inr i) := by
  simp [CaseM.spForm, CaseM.spGram, dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type,
    Pi.single_apply, Matrix.one_apply]

theorem twl_spForm_inr {n : ℕ} (v : Fin n ⊕ Fin n → GaloisField 2 1) (i : Fin n) :
    CaseM.spForm v (Pi.single (Sum.inr i) 1) = v (Sum.inl i) := by
  simp [CaseM.spForm, CaseM.spGram, dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type,
    Pi.single_apply, Matrix.one_apply]

theorem twl_trans_cases {n : ℕ} {v : Fin n ⊕ Fin n → GaloisField 2 1}
    {T : Subgroup (StatedSp n (GaloisField 2 1))} (hT : CaseM.IsTransGroup v T)
    {t : StatedSp n (GaloisField 2 1)} (ht : t ∈ T) :
    t = 1 ∨ SpExtras.mat n (GaloisField 2 1) t = CaseM.spTrans v 1 := by
  obtain ⟨c, hc⟩ := (hT.1 t).1 ht
  rcases twl_gf2 c with rfl | rfl
  · left
    apply SpExtras.mat_injective
    rw [hc, ModelRank.spTrans_zero, map_one]
  · right
    exact hc

theorem twl_spForm_zero {n : ℕ} {i k : Fin n ⊕ Fin n} (h : k ≠ Sum.swap i) :
    CaseM.spForm (Pi.single i (1 : GaloisField 2 1)) (Pi.single k 1) = 0 := by
  rcases i with j | j <;> rcases k with l | l
  · rw [twl_spForm_inl]
    simp [Pi.single_apply]
  · rw [twl_spForm_inr]
    have hl : l ≠ j := fun hh => h (by subst hh; rfl)
    simp [Pi.single_apply, hl]
  · rw [twl_spForm_inl]
    have hl : l ≠ j := fun hh => h (by subst hh; rfl)
    simp [Pi.single_apply, hl]
  · rw [twl_spForm_inr]
    simp [Pi.single_apply]

theorem twl_spForm_one {n : ℕ} (i : Fin n ⊕ Fin n) :
    CaseM.spForm (Pi.single i (1 : GaloisField 2 1)) (Pi.single (Sum.swap i) 1) = 1 := by
  rcases i with j | j
  · rw [Sum.swap_inl, twl_spForm_inr]
    simp
  · rw [Sum.swap_inr, twl_spForm_inl]
    simp [CharTwo.neg_eq]

theorem twl_swap_ne {n : ℕ} (i : Fin n ⊕ Fin n) : Sum.swap i ≠ i := by
  rcases i with j | j <;> simp

theorem twl_imgZ_conj_gen {V H : Subgroup G} (hVH : V ≤ H) (S : Subgroup G) (y : G)
    (hyX : y ∈ xOf V H) :
    imgZ V H (conjSubgroup y S) = conjSubgroup (xToZ hVH ⟨y, hyX⟩) (imgZ V H S) := by
  unfold imgZ
  have h1 := conjSubgroup_piBar_barOf (V := V) (H := H)
    (Subgroup.inclusion (xOf_le_H hVH) ⟨y, hyX⟩) S
  have h2 : conjSubgroup ((xToXbar hVH ⟨y, hyX⟩ : Xbar V H) : Hbar V H) (barOf V H S) =
      barOf V H (conjSubgroup y S) := h1
  rw [← h2, subgroupOf_conjSubgroup (barOf V H (xOf V H)) (barOf V H S) (xToXbar hVH ⟨y, hyX⟩)]
  exact (conjSubgroup_map_hom (projZ V H) ((barOf V H S).subgroupOf (barOf V H (xOf V H)))
    (xToXbar hVH ⟨y, hyX⟩)).symm

theorem twl_mem_imgZ {V H : Subgroup G} (hVH : V ≤ H) {S : Subgroup G} {y : G} (hyS : y ∈ S)
    (hyX : y ∈ xOf V H) : xToZ hVH ⟨y, hyX⟩ ∈ imgZ V H S := by
  unfold imgZ
  refine Subgroup.mem_map.mpr ⟨xToXbar hVH ⟨y, hyX⟩, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf, mem_barOf_iff]
  exact ⟨⟨y, xOf_le_H hVH hyX⟩, hyS, rfl⟩

theorem twl_xToZ_ne_one {V H : Subgroup G} (hVH : V ≤ H) (hdat : Sec23Data V H) {U : Subgroup G}
    (hU : U ∈ omegaOf V H) {y : G} (hyU : y ∈ U) (hyW : y ∉ wOf V H) (hyX : y ∈ xOf V H) :
    xToZ hVH ⟨y, hyX⟩ ≠ 1 := by
  intro h1
  have hyH : y ∈ H := xOf_le_H hVH hyX
  have hy1 : y ≠ 1 := fun h => hyW (by rw [h]; exact one_mem _)
  have hD : xToXbar hVH ⟨y, hyX⟩ ∈ Dy V H := by
    show ((xToXbar hVH ⟨y, hyX⟩ : Xbar V H) : Hbar V H) ∈ dbarOf V H
    rw [coe_xToXbar]
    exact mem_dbarOf_iff.mpr ⟨⟨y, hyH⟩, ⟨hy1, U, hU, hyU⟩, hyW, rfl⟩
  have hcen : xToXbar hVH ⟨y, hyX⟩ ∈ Subgroup.center (Xbar V H) := by
    have h2 : projZ V H (xToXbar hVH ⟨y, hyX⟩) = 1 := by
      rw [← xToZ_apply]; exact h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  exact hdat.noncentral _ hD hcen

theorem twl_member {V H : Subgroup G} (hVH : V ≤ H) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H) {a : Fin n ⊕ Fin n → GaloisField 2 1}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 1))} (hTa : CaseM.IsTransGroup a T)
    (hT : T.map Φ = VZ V H) (ha : a ≠ 0) {x : Fin n ⊕ Fin n → GaloisField 2 1} (hx : x ≠ 0) :
    ∃ (h : ↥(xOf V H)) (Tx : Subgroup ↥(StatedSp n (GaloisField 2 1))),
      CaseM.IsTransGroup x Tx ∧ imgZ V H (conjSubgroup (h : G) V) = Tx.map Φ := by
  obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero ha hx
  have hTx : CaseM.IsTransGroup x (CFSG.Timmesfeld.ARS.conjSub T g) := by
    rw [← hg]
    exact hTa.conjSub g
  obtain ⟨h, hh⟩ := xToZ_surjective hVH (Φ g)
  refine ⟨h, _, hTx, ?_⟩
  rw [imgZ_conj hVH h, hh, ← ModelRank.conjSub_map Φ T g, hT]
  rfl

theorem twl_commute {M Q P V H : Subgroup G} [Finite G] (hc : MinCex M V Q P H) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H) {x y : Fin n ⊕ Fin n → GaloisField 2 1}
    {h₁ h₂ : ↥(xOf V H)} {T₁ T₂ : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (hT₁ : CaseM.IsTransGroup x T₁) (hT₂ : CaseM.IsTransGroup y T₂)
    (hxy : CaseM.spForm x y = 0)
    (e₁ : imgZ V H (conjSubgroup (h₁ : G) V) = T₁.map Φ)
    (e₂ : imgZ V H (conjSubgroup (h₂ : G) V) = T₂.map Φ) :
    ∀ u ∈ conjSubgroup (h₁ : G) V, ∀ v ∈ conjSubgroup (h₂ : G) V, u * v = v * u := by
  refine hc.commute_conj_of_commute_tilde (x₁ := h₁) (x₂ := h₂) ?_
  intro a ha b hb
  rw [← imgZ_conj hc.V_le_H h₁, e₁] at ha
  rw [← imgZ_conj hc.V_le_H h₂, e₂] at hb
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp hb
  rw [← map_mul, ← map_mul, (CaseM.IsTransGroup.commuting hT₁ hT₂ hxy t ht t' ht').eq]

theorem twl_noCommute {M Q P V H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
    (hdat : Sec23Data V H) {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H)
    (hΦ : Function.Injective Φ) {i j : Fin n ⊕ Fin n} (hji : j ≠ i)
    (hij : CaseM.spForm (Pi.single i (1 : GaloisField 2 1)) (Pi.single j 1) = 1)
    {hi hj : ↥(xOf V H)} {Ti Tj : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (hTi : CaseM.IsTransGroup (Pi.single i (1 : GaloisField 2 1)) Ti)
    (hTj : CaseM.IsTransGroup (Pi.single j (1 : GaloisField 2 1)) Tj)
    (ei : imgZ V H (conjSubgroup (hi : G) V) = Ti.map Φ)
    (ej : imgZ V H (conjSubgroup (hj : G) V) = Tj.map Φ)
    {y a : G} (hy : y ∈ conjSubgroup (hi : G) V) (hyW : y ∉ wOf V H)
    (ha : a ∈ conjSubgroup (hj : G) V) (ha1 : a ≠ 1) (hc' : y * a = a * y) : False := by
  have hVH : V ≤ H := hc.V_le_H
  have hhi : (hi : G) ∈ H := xOf_le_H hVH hi.2
  have hyX : y ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hhi) hy
  have hyN : y ∈ Subgroup.normalizer (conjSubgroup (hj : G) V : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI
      (CFSG.RankThree.GF2n.isTI_conjSubgroup hc.ti (hj : G)) ha ha1 hc'
  have hyN' : conjSubgroup y (conjSubgroup (hj : G) V) = conjSubgroup (hj : G) V :=
    mem_normalizer_iff_conjSubgroup_eq.mp hyN
  have hsN : xToZ hVH ⟨y, hyX⟩ ∈ Subgroup.normalizer
      ((imgZ V H (conjSubgroup (hj : G) V) : Subgroup (XbarZ V H)) : Set (XbarZ V H)) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have h1 := twl_imgZ_conj_gen hVH (conjSubgroup (hj : G) V) y hyX
    rw [hyN'] at h1
    exact h1.symm
  have hsU : xToZ hVH ⟨y, hyX⟩ ∈ imgZ V H (conjSubgroup (hi : G) V) :=
    twl_mem_imgZ hVH hy hyX
  rw [ei] at hsU
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hsU
  have hs1 : xToZ hVH ⟨y, hyX⟩ ≠ 1 :=
    twl_xToZ_ne_one hVH hdat (conjSubgroup_mem_omegaOf hhi) hy hyW hyX
  rcases twl_trans_cases hTi ht with ht1 | htm
  · exact hs1 (by rw [← hts, ht1, map_one])
  obtain ⟨t', ht't⟩ := hTj.2 1
  have ht'T : t' ∈ Tj := (hTj.1 t').2 ⟨1, ht't⟩
  have ht'1 : t' ≠ 1 := by
    intro h
    apply twl_spTrans_one_ne_one (twl_unit_ne_zero j)
    rw [← ht't, h, map_one]
  have hp : Φ t' ∈ imgZ V H (conjSubgroup (hj : G) V) := by
    rw [ej]
    exact Subgroup.mem_map.mpr ⟨t', ht'T, rfl⟩
  have hconj := (Subgroup.mem_normalizer_iff.mp hsN (Φ t')).mp hp
  rw [ej] at hconj
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hconj
  set s := xToZ hVH ⟨y, hyX⟩ with hsdef
  rcases twl_trans_cases hTj hu with hu1 | hum
  · rw [hu1, map_one] at hu'
    have h1' : Φ t' = 1 := by
      calc Φ t' = s⁻¹ * (s * Φ t' * s⁻¹) * s := by group
        _ = 1 := by rw [← hu']; group
    exact ht'1 (hΦ (show Φ t' = Φ 1 by rw [h1', map_one]))
  · have hut : u = t' := SpExtras.mat_injective (hum.trans ht't.symm)
    rw [hut] at hu'
    have hcomm2 : s * Φ t' = Φ t' * s := by
      calc s * Φ t' = (s * Φ t' * s⁻¹) * s := by group
        _ = Φ t' * s := by rw [← hu']
    have hcomm3 : Φ (t * t') = Φ (t' * t) := by
      rw [map_mul, map_mul, hts, hcomm2]
    have htt : t * t' = t' * t := hΦ hcomm3
    have hmat := congrArg (SpExtras.mat n (GaloisField 2 1)) htt
    rw [map_mul, map_mul, htm, ht't] at hmat
    rcases CaseM.spForm_eq_zero_of_commute (twl_unit_ne_zero i) hmat with h0 | ⟨l, hl⟩
    · rw [hij] at h0
      exact one_ne_zero h0
    · have h2 := congrFun hl j
      simp [Pi.single_apply, hji] at h2

abbrev twl_wComm {V H : Subgroup G} (hW : IsMulCommutative ↥(wOf V H)) :
    CommGroup ↥(wOf V H) :=
  { (inferInstance : Group ↥(wOf V H)) with
    mul_comm := fun a b => hW.is_comm.comm a b }

theorem twl_conj_mem {V H : Subgroup G} {y : G} (hyH : y ∈ H) (a : ↥(wOf V H)) :
    y * (a : G)⁻¹ * y⁻¹ ∈ wOf V H :=
  (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hyH) (a : G)⁻¹).mp
    ((wOf V H).inv_mem a.2)

noncomputable def twl_D {V H : Subgroup G} (hW : IsMulCommutative ↥(wOf V H)) {y : G}
    (hyH : y ∈ H) : ↥(wOf V H) →* ↥(wOf V H) :=
  MonoidHom.mk' (fun a => a * ⟨y * (a : G)⁻¹ * y⁻¹, twl_conj_mem hyH a⟩) (fun a b => by
    letI := twl_wComm hW
    have hab : (⟨y * ((a * b : ↥(wOf V H)) : G)⁻¹ * y⁻¹, twl_conj_mem hyH (a * b)⟩ :
        ↥(wOf V H)) = ⟨y * (b : G)⁻¹ * y⁻¹, twl_conj_mem hyH b⟩ *
          ⟨y * (a : G)⁻¹ * y⁻¹, twl_conj_mem hyH a⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]; group)
    rw [hab]
    simp only [mul_comm, mul_assoc, mul_left_comm])

theorem twl_D_eq_one_iff {V H : Subgroup G} (hW : IsMulCommutative ↥(wOf V H)) {y : G}
    (hyH : y ∈ H) (a : ↥(wOf V H)) : twl_D hW hyH a = 1 ↔ y * (a : G) = (a : G) * y := by
  have key : twl_D hW hyH a = 1 ↔ (a : G) * (y * (a : G)⁻¹ * y⁻¹) = 1 := by
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      simpa [twl_D] using h'
    · intro h
      apply Subtype.ext
      simpa [twl_D] using h
  rw [key]
  constructor
  · intro h
    have h1 : y * (a : G)⁻¹ * y⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : Commute y (a : G)⁻¹ := by
      show y * (a : G)⁻¹ = (a : G)⁻¹ * y
      calc y * (a : G)⁻¹ = (y * (a : G)⁻¹ * y⁻¹) * y := by group
        _ = (a : G)⁻¹ * y := by rw [h1]
    exact Commute.inv_right_iff.mp h2
  · intro h
    have h2 : Commute y (a : G)⁻¹ := Commute.inv_right h
    have h3 : y * (a : G)⁻¹ * y⁻¹ = (a : G)⁻¹ := by
      rw [h2.eq]
      group
    rw [h3]
    group

theorem twistedWLower_holds : TwistedWLowerStatement := by
  intro G _ _ M V Q P H hs n Φ a T z₀ hd
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hΦ : Function.Injective Φ := hd.bij.1
  have hW : IsMulCommutative ↥(wOf V H) := hc.wOf_isElemAbelian.1
  letI : CommGroup ↥(wOf V H) := twl_wComm hW
  have hmem : ∀ i : Fin n ⊕ Fin n, ∃ (h : ↥(xOf V H))
      (Tx : Subgroup ↥(StatedSp n (GaloisField 2 1))),
      CaseM.IsTransGroup (Pi.single i (1 : GaloisField 2 1)) Tx ∧
        imgZ V H (conjSubgroup (h : G) V) = Tx.map Φ :=
    fun i => twl_member hVH Φ hd.trans hd.map_eq hd.ne_zero (twl_unit_ne_zero i)
  choose hh TT hTT hEq using hmem
  obtain ⟨v₀, hv₀V, hv₀W⟩ : ∃ v ∈ V, v ∉ wOf V H :=
    SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hXH : ∀ i, (hh i : G) ∈ H := fun i => xOf_le_H hVH (hh i).2
  have hUW : ∀ i, conjSubgroup (hh i : G) (wOf V H) = wOf V H := fun i =>
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr (H_le_normalizer_wOf V H (hXH i))
  have hyH : ∀ i, (hh i : G) * v₀ * (hh i : G)⁻¹ ∈ H := fun i =>
    H.mul_mem (H.mul_mem (hXH i) (hVH hv₀V)) (H.inv_mem (hXH i))
  have hyU : ∀ i, (hh i : G) * v₀ * (hh i : G)⁻¹ ∈ conjSubgroup (hh i : G) V := fun i => by
    rw [mem_conjSubgroup, show (hh i : G)⁻¹ * ((hh i : G) * v₀ * (hh i : G)⁻¹) * (hh i : G) = v₀ by
      group]
    exact hv₀V
  have hyW : ∀ i, (hh i : G) * v₀ * (hh i : G)⁻¹ ∉ wOf V H := fun i hW' => by
    have h1 : (hh i : G) * v₀ * (hh i : G)⁻¹ ∈ conjSubgroup (hh i : G) (wOf V H) := by
      rw [hUW i]
      exact hW'
    rw [mem_conjSubgroup, show (hh i : G)⁻¹ * ((hh i : G) * v₀ * (hh i : G)⁻¹) * (hh i : G) = v₀ by
      group] at h1
    exact hv₀W h1
  have hkill : ∀ i k : Fin n ⊕ Fin n, k ≠ Sum.swap i →
      ∀ x ∈ (conjSubgroup (hh k : G) V ⊓ wOf V H).subgroupOf (wOf V H),
        twl_D hW (hyH i) x = 1 := by
    intro i k hk x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    rw [twl_D_eq_one_iff]
    exact twl_commute hc Φ (hTT i) (hTT k) (twl_spForm_zero hk) (hEq i) (hEq k) _ (hyU i) _ hx.1
  have hinj : ∀ i : Fin n ⊕ Fin n,
      ∀ x ∈ (conjSubgroup (hh (Sum.swap i) : G) V ⊓ wOf V H).subgroupOf (wOf V H),
        twl_D hW (hyH i) x = 1 → x = 1 := by
    intro i x hx hD
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    rw [twl_D_eq_one_iff] at hD
    by_contra hx1
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact twl_noCommute hc hs.data Φ hΦ (twl_swap_ne i) (twl_spForm_one i) (hTT i)
      (hTT (Sum.swap i)) (hEq i) (hEq (Sum.swap i)) (hyU i) (hyW i) hx.1 hx1' hD
  have hA : ∀ i : Fin n ⊕ Fin n,
      Nat.card ↥((conjSubgroup (hh i : G) V ⊓ wOf V H).subgroupOf (wOf V H)) =
        Nat.card ↥(V ⊓ wOf V H) := by
    intro i
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : conjSubgroup (hh i : G) V ⊓ wOf V H ≤ wOf V H)).toEquiv,
      ← CFSG.RankThree.GF2n.card_conjSubgroup (hh i : G) (V ⊓ wOf V H),
      CFSG.RankThree.GF2n.conjSubgroup_inf, hUW i]
  have key : ∏ i : Fin n ⊕ Fin n,
      Nat.card ↥((conjSubgroup (hh i : G) V ⊓ wOf V H).subgroupOf (wOf V H)) ≤
        Nat.card ↥(wOf V H) :=
    CFSG.RankThree.GF2n.Tim79a.card_prod_le_of_pairing
      (fun i => (conjSubgroup (hh i : G) V ⊓ wOf V H).subgroupOf (wOf V H)) Sum.swap
      (fun i => by simp) (fun i => twl_D hW (hyH i)) hkill hinj
  have hprod : ∏ i : Fin n ⊕ Fin n,
      Nat.card ↥((conjSubgroup (hh i : G) V ⊓ wOf V H).subgroupOf (wOf V H)) =
        Nat.card ↥(V ⊓ wOf V H) ^ (2 * n) := by
    rw [Finset.prod_congr rfl (fun i _ => hA i), Finset.prod_const, Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin, two_mul]
  rw [hprod] at key
  exact key

end CFSG.RankThree.GF2n.Tim79a
