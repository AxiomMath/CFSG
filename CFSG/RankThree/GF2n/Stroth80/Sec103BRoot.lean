module

public import CFSG.RankThree.GF2n.Stroth80.Sec103BRt
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenRoots
public import CFSG.RankThree.GF2n.Stroth80.Sec8BridgeModel
public import CFSG.RankThree.GF2n.Smith81.S81BBridge
public import CFSG.RankThree.GF2n.Smith81.TiRootLines

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem apply_mem_line_of_apply_mem_plane
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Module.Finite K E]
    {V C : Submodule K E} (hCV : C ≤ V)
    (hVdim : Module.finrank K V = 2) (hCdim : Module.finrank K C = 1)
    {ι : Type*} {g : ι → E →ₗ[K] E}
    (hcomm : ∀ i j e, g i (g j e) = g j (g i e))
    (hsq : ∀ i e, g i (g i e) = 0)
    (hVC : ∀ i v, v ∈ V → g i v ∈ C)
    (hker : ∀ v ∈ V, (∀ i, g i v = 0) → v ∈ C)
    {e : E} (he : ∀ i, g i e ∈ V) :
    ∀ i, g i e ∈ C := by
  obtain ⟨c₀, hc₀, hgen⟩ := finrank_eq_one_iff'.mp hCdim
  have hc₀' : (c₀ : E) ≠ 0 := fun h => hc₀ (Subtype.ext h)
  have hgen' : ∀ w : E, w ∈ C → ∃ a : K, a • (c₀ : E) = w := by
    intro w hw
    obtain ⟨a, ha⟩ := hgen ⟨w, hw⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  have hCker : ∀ i c, c ∈ C → g i c = 0 := by
    intro i c hc
    obtain ⟨a, ha⟩ := hgen' c hc
    rw [← ha, map_smul]
    suffices h : g i (c₀ : E) = 0 by rw [h, smul_zero]
    by_contra hne
    obtain ⟨b, hb⟩ := hgen' (g i (c₀ : E)) (hVC i _ (hCV c₀.2))
    have hb0 : b ≠ 0 := by
      intro h0
      exact hne (by rw [← hb, h0, zero_smul])
    have h0 : g i (g i (c₀ : E)) = 0 := hsq i (c₀ : E)
    rw [← hb, map_smul, ← hb, smul_smul] at h0
    exact hb0 (mul_self_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hc₀'))
  intro i
  by_contra hcon
  have hwi : g i e ∈ V := he i
  have hkill : ∀ v ∈ V, g i v = 0 := by
    intro v hv
    have hspan : C ⊔ Submodule.span K {g i e} = V := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · exact sup_le hCV (Submodule.span_le.mpr (by simpa using hwi))
      · rw [Submodule.finrank_sup_span_singleton (K := K) (p := C) (v := g i e) hcon,
          hCdim, hVdim]
    rw [← hspan] at hv
    obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_add, map_smul, hCker i c hc, hsq i e, smul_zero, add_zero]
  obtain ⟨j, hj⟩ : ∃ j, g j (g i e) ≠ 0 := by
    by_contra h
    push Not at h
    exact hcon (hker (g i e) hwi h)
  rw [hcomm j i e] at hj
  exact hj (hkill (g j e) (he j))

private theorem add_self_eq_zero_of_charP (K : Type*) [Field K] [CharP K 2]
    {E : Type*} [AddCommGroup E] [Module K E] (x : E) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero (R := K), zero_smul]

private theorem finrank_eq_two_of_card {K W : Type*} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [Module.Finite K W] (hW : Nat.card W = Nat.card K ^ 2) :
    Module.finrank K W = 2 := by
  have h2 : 2 ≤ Nat.card K := by have := Finite.one_lt_card (α := K); omega
  have h := Module.natCard_eq_pow_finrank (K := K) (V := W)
  rw [hW] at h
  exact (Nat.pow_right_injective h2 h).symm


private theorem rootGroup_le_Vt {hc : Ctx M Q Z B} {n : ℕ} (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) (H : Sec10Hyp hc n) {t : G}
    (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {C : Subgroup G}
    (hC : Ctx M Q Z C) (hCY : C ≤ QB Y) : C ≤ Vt M (LB M Q B) B Z t := by
  intro c hcC
  by_cases hc1 : c = 1
  · rw [hc1]
    exact (Vt M (LB M Q B) B Z t).one_mem
  · obtain ⟨g, hg⟩ := hC.conj
    have hcg : c ∈ conjSubgroup g Z := hg ▸ hcC
    have hz : g⁻¹ * c * g ∈ Z := mem_conjSubgroup.mp hcg
    have hz1 : g⁻¹ * c * g ≠ 1 := by
      intro h1
      rw [h1] at hz
      apply hc1
      calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    refine Good101.mem_Vt_of_isRoot h34 hspread H ht hs ⟨hC.le hcC, hCY hcC⟩
      ⟨g, g⁻¹ * c * g, hz, hz1, ?_⟩
    group


private theorem comm_mem_sup_Z_of_mem_sup {hc : Ctx M Q Z B} {C : Subgroup G}
    (hC : Ctx M Q Z C) {a : G} (ha : a ∈ Q)
    (hcomm : ∀ l ∈ LB M Q C, ⁅l, a⁆ ∈ C ⊔ Z) :
    ∀ x ∈ Subgroup.zpowers a ⊔ Z, ∀ t ∈ LB M Q C, ⁅t, x⁆ ∈ C ⊔ Z := by
  have hQnorm : Q ≤ Subgroup.normalizer ((C ⊔ Z : Subgroup G) : Set G) :=
    Q_le_normalizer_of_Z_le hc.hyp le_sup_right (sup_le hC.le hc.Z_le_Q)
  let S : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ ∀ t ∈ LB M Q C, ⁅t, x⁆ ∈ C ⊔ Z}
      mul_mem' := by
        rintro x y ⟨hxQ, hx⟩ ⟨hyQ, hy⟩
        refine ⟨Q.mul_mem hxQ hyQ, fun t ht => ?_⟩
        have e : ⁅t, x * y⁆ = ⁅t, x⁆ * (x * ⁅t, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (C ⊔ Z).mul_mem (hx t ht)
          ((Subgroup.mem_normalizer_iff.mp (hQnorm hxQ) _).mp (hy t ht))
      one_mem' := ⟨Q.one_mem, fun t ht => by simp⟩
      inv_mem' := by
        rintro x ⟨hxQ, hx⟩
        refine ⟨Q.inv_mem hxQ, fun t ht => ?_⟩
        have e : ⁅t, x⁻¹⁆ = x⁻¹ * ⁅t, x⁆⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [e]
        simpa using (Subgroup.mem_normalizer_iff.mp (hQnorm (Q.inv_mem hxQ)) _).mp
          ((C ⊔ Z).inv_mem (hx t ht)) }
  have haS : a ∈ S := ⟨ha, hcomm⟩
  have hZS : Z ≤ S := by
    intro z hz
    refine ⟨hc.Z_le_Q hz, fun t ht => ?_⟩
    have h1 : t * z = z * t :=
      (Subgroup.mem_centralizer_iff.mp (hC.LB_le_H0 ht).2 z hz).symm
    have hz1 : ⁅t, z⁆ = 1 := by
      rw [commutatorElement_def, h1]
      group
    rw [hz1]
    exact Subgroup.one_mem _
  have hX : Subgroup.zpowers a ⊔ Z ≤ S := sup_le (Subgroup.zpowers_le.mpr haS) hZS
  intro x hx t ht
  exact (hX hx).2 t ht

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}

private theorem card_img_Vt {hc : Ctx M Q Z B} (hD : GlobalModelData M Q Z γ M₀) {t : G}
    (h2 : SLMNat hc t 2) :
    Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card K ^ 2 := by
  set V := Vt M (LB M Q B) B Z t
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have h1 : Nat.card ↥V = Nat.card Z ^ (2 + 1) := SLMNat.card_Vt h2
  have h2' : Nat.card ↥V = Nat.card Z * Nat.card ↥(M₀.img V) :=
    Tim79.QuadModel.card_eq M₀ hVQ hZV
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have h3 : Nat.card Z * Nat.card ↥(M₀.img V) = Nat.card Z * Nat.card Z ^ 2 := by
    rw [← h2', h1]
    ring
  have h4 : Nat.card ↥(M₀.img V) = Nat.card Z ^ 2 := Nat.mul_left_cancel hZpos h3
  rw [h4, ← hD.card]

private theorem pi_comm_eq {hc : Ctx M Q Z B}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {h x : G} (hh : h ∈ H0 M Z) (hx : x ∈ Q) :
    M₀.π ⁅h, x⁆ = φ ⟨h, hh⟩ (M₀.π x) - M₀.π x := by
  have hxQ : h * x * h⁻¹ ∈ Q := conj_mem_Q (H := hc.hyp) hh.1 hx
  rw [show ⁅h, x⁆ = h * x * h⁻¹ * x⁻¹ by rfl, M₀.π_mul _ hxQ _ (Q.inv_mem hx),
    hφπ ⟨h, hh⟩ x hx, M₀.pi_inv hx, sub_eq_add_neg]

private theorem action_sub_one_comm {hc : Ctx M Q Z B}
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {C : Subgroup G} (hC : Ctx M Q Z C) (hLC : LB M Q C ≤ H0 M Z)
    (i j : ↥(LB M Q C)) (e : M₀.E) :
    ((φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1)
        (((φ ⟨j, hLC j.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) e) =
      ((φ ⟨j, hLC j.2⟩ : M₀.E →ₗ[K] M₀.E) - 1)
        (((φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) e) := by
  have hmem : ⁅(i : G), (j : G)⁆ ∈ LB M Q C := by
    rw [commutatorElement_def]
    exact (LB M Q C).mul_mem ((LB M Q C).mul_mem ((LB M Q C).mul_mem i.2 j.2)
      ((LB M Q C).inv_mem i.2)) ((LB M Q C).inv_mem j.2)
  have hQ : ⁅(i : G), (j : G)⁆ ∈ Q :=
    hC.commutator_LB_le_Q (Subgroup.commutator_mem_commutator i.2 j.2)
  let z : ↥(H0 M Z) := ⟨⁅(i : G), (j : G)⁆, hLC hmem⟩
  have h1 : φ z = 1 := (hφQ _).mpr hQ
  have hsub : z = ⁅(⟨i, hLC i.2⟩ : ↥(H0 M Z)), (⟨j, hLC j.2⟩ : ↥(H0 M Z))⁆ :=
    Subtype.ext rfl
  have h2 : φ ⟨i, hLC i.2⟩ * φ ⟨j, hLC j.2⟩ = φ ⟨j, hLC j.2⟩ * φ ⟨i, hLC i.2⟩ := by
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    rw [hsub] at h1
    rw [map_commutatorElement] at h1
    exact h1
  have h3 : (φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) ((φ ⟨j, hLC j.2⟩ : M₀.E →ₗ[K] M₀.E) e) =
      (φ ⟨j, hLC j.2⟩ : M₀.E →ₗ[K] M₀.E) ((φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) e) :=
    congrArg (fun f => f e) h2
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [h3]
  abel

private theorem action_sub_one_sq {hc : Ctx M Q Z B}
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {C : Subgroup G} (hC : Ctx M Q Z C) (hLC : LB M Q C ≤ H0 M Z)
    (i : ↥(LB M Q C)) (e : M₀.E) :
    ((φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1)
        (((φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) e) = 0 := by
  have hi2 : (i : G) ^ 2 ∈ Q := hC.sq_mem_Q_of_mem_LB i.2
  have hsq : φ ⟨i, hLC i.2⟩ * φ ⟨i, hLC i.2⟩ = 1 := by
    have hz : (⟨i, hLC i.2⟩ : ↥(H0 M Z)) * ⟨i, hLC i.2⟩ =
        ⟨(i : G) ^ 2, hLC (pow_mem i.2 2)⟩ := Subtype.ext (by simp [pow_two])
    rw [← map_mul, hz]
    exact (hφQ _).mpr hi2
  have hge : (φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E)
      ((φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) e) = e := by
    simpa using congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) hsq
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [hge]
  have hx : e - (φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) e =
      -((φ ⟨i, hLC i.2⟩ : M₀.E →ₗ[K] M₀.E) e - e) := by abel
  rw [hx, sub_eq_add_neg, ← neg_add, add_self_eq_zero_of_charP K, neg_zero]

private theorem action_sub_one_mem_span {hc : Ctx M Q Z B}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {t : G} {C : Subgroup G} (hC : Ctx M Q Z C) {e : M₀.E}
    (he : ∀ w : M₀.E, w ∈ M₀.img C ↔ ∃ s : K, w = s • e)
    (hVC : Vt M (LB M Q B) B Z t ≤ QB C)
    (i : ↥(LB M Q C)) {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t) :
    ((φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π v) ∈
      Submodule.span K {e} := by
  obtain ⟨s, hs, q, hq, hi⟩ := hC.exists_mul_of_mem_LB i.2
  have hsLB : s ∈ LB M Q C := Subgroup.mem_sup_right hs
  have hqLB : q ∈ LB M Q C := sec39_Q_le_LB hq
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have hsv : ⁅s, v⁆ ∈ C := Smith81.Ctx.comm_mem_of_mem_QB hC hs.1 (hVC hv)
  have hφi : φ ⟨i, hC.LB_le_H0 i.2⟩ = φ ⟨s, hC.LB_le_H0 hsLB⟩ := by
    have h1 : (⟨i, hC.LB_le_H0 i.2⟩ : ↥(H0 M Z)) =
        ⟨s, hC.LB_le_H0 hsLB⟩ * ⟨q, hC.LB_le_H0 hqLB⟩ := Subtype.ext hi
    rw [h1, map_mul, (hφQ ⟨q, hC.LB_le_H0 hqLB⟩).mpr hq, mul_one]
  have hform : M₀.π ⁅s, v⁆ = φ ⟨s, hC.LB_le_H0 hsLB⟩ (M₀.π v) - M₀.π v :=
    pi_comm_eq (hc := hC) hφπ (hC.LB_le_H0 hsLB) hvQ
  have h : ((φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π v) = M₀.π ⁅s, v⁆ := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hφi]
    exact hform.symm
  rw [h]
  obtain ⟨a, ha⟩ := (he _).mp (M₀.pi_mem_img hsv (hC.le hsv))
  exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩

private theorem action_sub_one_kernel {hc : Ctx M Q Z B}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (h34 : Stroth34Statement) {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} {C : Subgroup G} (hC : Ctx M Q Z C) (hno : NoA2 Q Z (LB M Q C))
    (hgen : GenByB M Q C) {e : M₀.E}
    (he : ∀ w : M₀.E, w ∈ M₀.img C ↔ ∃ s : K, w = s • e)
    {v : M₀.E} (hv : v ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (h : ∀ i : ↥(LB M Q C),
      ((φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) v = 0) :
    v ∈ Submodule.span K {e} := by
  obtain ⟨x, hxV, hxQ, rfl⟩ := (M₀.mem_img).mp hv
  have h35 : CQt Q Z (LB M Q C) = ((C ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hC H.width H.n_gt hno hgen).2.1
  have hx : x ∈ CQt Q Z (LB M Q C) := by
    refine ⟨hxQ, fun i hi => ?_⟩
    have h0 := h (⟨i, hi⟩ : ↥(LB M Q C))
    change ((φ ⟨i, hC.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π x) = 0 at h0
    have hform := pi_comm_eq (hc := hC) hφπ (hC.LB_le_H0 hi) hxQ
    have hxQ' : ⁅i, x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (conj_mem_Q (H := hc.hyp) (hC.LB_le_H0 hi).1 hxQ) (Q.inv_mem hxQ)
    rw [LinearMap.sub_apply, Module.End.one_apply] at h0
    have h0' : M₀.π ⁅i, x⁆ = 0 := by
      rw [hform]
      exact h0
    exact (M₀.π_ker _ hxQ').mp h0'
  rw [h35] at hx
  have hx' : M₀.π x ∈ M₀.img (C ⊔ Z) :=
    M₀.pi_mem_img hx (sup_le hC.le hc.Z_le_Q hx)
  have hle : M₀.img (C ⊔ Z) ≤ M₀.img C := by
    intro w hw
    exact sec8_img_sup_le M₀ hC (by rwa [sup_comm] at hw)
  obtain ⟨a, ha⟩ := (he _).mp (hle hx')
  exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩


private theorem finrank_Vs {hc : Ctx M Q Z B} (hD : GlobalModelData M Q Z γ M₀) {t : G}
    (h2 : SLMNat hc t 2) :
    Module.finrank K (imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hD t c he)) = 2 := by
  refine finrank_eq_two_of_card ?_
  have h1 : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hD t c he)) =
      Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) := rfl
  rw [h1]
  exact card_img_Vt hD h2

private theorem span_le_imgSub {hc : Ctx M Q Z B} (hD : GlobalModelData M Q Z γ M₀) {t : G}
    {C : Subgroup G} (hCV : C ≤ Vt M (LB M Q B) B Z t) {e : M₀.E}
    (heC : ∀ w : M₀.E, w ∈ M₀.img C ↔ ∃ s : K, w = s • e) :
    Submodule.span K {e} ≤ imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hD t c he) := by
  intro x hx
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hx
  exact mem_imgSub.mpr (M₀.img_mono hCV ((heC x).mpr ⟨s, hs.symm⟩))

private theorem mem_span_of_mem_img {hc : Ctx M Q Z B}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) (hD : GlobalModelData M Q Z γ M₀) {t : G}
    {C : Subgroup G} (hC : Ctx M Q Z C)
    (hVCle : Vt M (LB M Q B) B Z t ≤ QB C) {e : M₀.E}
    (heC : ∀ w : M₀.E, w ∈ M₀.img C ↔ ∃ s : K, w = s • e) (i : ↥(LB M Q C))
    {v : M₀.E} (hv : v ∈ imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hD t c he)) :
    ((φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) v ∈ Submodule.span K {e} := by
  obtain ⟨x, hxV, -, rfl⟩ := (M₀.mem_img).mp (mem_imgSub.mp hv)
  exact action_sub_one_mem_span (hc := hc) hφπ hφQ hC heC hVCle i hxV

private theorem mem_img_Vt {hc : Ctx M Q Z B}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hD : GlobalModelData M Q Z γ M₀) {t : G}
    {Y : Subgroup G} {C : Subgroup G} (hC : Ctx M Q Z C) {a : G} (ha : a ∈ Q ⊓ QB Y)
    (hl : ∀ l ∈ LB M Q C, ⁅l, a⁆ ∈ Vt M (LB M Q B) B Z t) (i : ↥(LB M Q C)) :
    ((φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π a) ∈
      imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hD t c he) := by
  have hmemV : ⁅(i : G), a⁆ ∈ Vt M (LB M Q B) B Z t := hl i i.2
  have h1 : ((φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π a) =
      M₀.π ⁅(i : G), a⁆ := by
    have hform := pi_comm_eq (hc := hC) hφπ (hC.LB_le_H0 i.2) ha.1
    show (φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) (M₀.π a) - M₀.π a =
      M₀.π ⁅(i : G), a⁆
    exact hform.symm
  rw [h1]
  exact mem_imgSub.mpr (M₀.pi_mem_img hmemV (hc.Vt_le_Q t hmemV))

private theorem mem_sup_of_pi_mem_img {hc : Ctx M Q Z B} {C : Subgroup G} {a l : G}
    (hl : l ∈ H0 M Z) (ha : a ∈ Q) (hπ : M₀.π ⁅l, a⁆ ∈ M₀.img C) : ⁅l, a⁆ ∈ C ⊔ Z := by
  obtain ⟨c, hcC, hcQ, hπc⟩ := (M₀.mem_img).mp hπ
  have hxQ : ⁅l, a⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (conj_mem_Q (H := hc.hyp) hl.1 ha) (Q.inv_mem ha)
  have hz : c⁻¹ * ⁅l, a⁆ ∈ Z := (M₀.pi_eq_iff hcQ hxQ).mp hπc
  have heq : ⁅l, a⁆ = c * (c⁻¹ * ⁅l, a⁆) := by group
  rw [heq]
  exact Subgroup.mul_mem_sup hcC hz

private theorem comm_mem_sup_Z_of_forall_mem_Vt {hc : Ctx M Q Z B} {n : ℕ}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) (hD : GlobalModelData M Q Z γ M₀)
    (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement) (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {C : Subgroup G} (hC : Ctx M Q Z C) (hCY : C ≤ QB Y) {a : G}
    (ha : a ∈ Q ⊓ QB Y) (hl : ∀ l ∈ LB M Q C, ⁅l, a⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∀ l ∈ LB M Q C, ⁅l, a⁆ ∈ C ⊔ Z := by
  obtain ⟨μ, hμ, hμC⟩ := H.rootTrans h34 hspread C hC
  have hno : NoA2 Q Z (LB M Q C) := by rw [← hμC]; exact hc.noA2_conj H.noA2 hμ
  have hgen : GenByB M Q C := by rw [← hμC]; exact H.gen.conj_of_mem hμ
  have hVCle : Vt M (LB M Q B) B Z t ≤ QB C :=
    Good101.Vt_le_QB_of_root h34 hspread H ht hs hC hCY
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hCV : C ≤ Vt M (LB M Q B) B Z t := rootGroup_le_Vt h34 hspread H ht hs hC hCY
  obtain ⟨gC, hgC⟩ := hC.conj
  have hline : M₀.IsLine C :=
    hgC ▸ hD.line gC (by rw [← hgC]; exact hC.ne) (by rw [← hgC]; exact hC.le)
  obtain ⟨e, he0, heC⟩ := hline
  have hVdim : Module.finrank K (imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hD t c he)) = 2 := finrank_Vs hD h2
  have hCs_le : Submodule.span K {e} ≤ imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hD t c he) := span_le_imgSub (hc := hc) hD hCV heC
  let g : ↥(LB M Q C) → M₀.E →ₗ[K] M₀.E :=
    fun i => (φ ⟨i, hC.LB_le_H0 i.2⟩ : M₀.E →ₗ[K] M₀.E) - 1
  have hres := apply_mem_line_of_apply_mem_plane hCs_le hVdim (finrank_span_singleton he0)
    (fun i j e => action_sub_one_comm (hc := hc) hφQ hC hC.LB_le_H0 i j e)
    (fun i e => action_sub_one_sq (hc := hc) hφQ hC hC.LB_le_H0 i e)
    (fun i v hv => mem_span_of_mem_img (hc := hc) hφπ hφQ hD hC hVCle heC i hv)
    (fun v hv h => action_sub_one_kernel (hc := hc) hφπ h34 H hC hno hgen heC
      (mem_imgSub.mp hv) h)
    (fun i => mem_img_Vt (hc := hc) hφπ hD hC ha hl i)
  intro l hl
  refine mem_sup_of_pi_mem_img (K := K) (M₀ := M₀) (hc := hc) (C := C) (a := a) (l := l)
    (hC.LB_le_H0 hl) ha.1 ?_
  rw [pi_comm_eq (hc := hC) hφπ (hC.LB_le_H0 hl) ha.1]
  obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp (hres ⟨l, hl⟩)
  exact (heC _).mpr ⟨s, hs'.symm⟩


end Model

theorem Good101.mem_QB_of_forall_comm_LB_mem_Vt (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {C : Subgroup G} (hC : Ctx M Q Z C) (hCY : C ≤ QB Y) {a : G}
    (ha : a ∈ Q ⊓ QB Y) (hl : ∀ l ∈ LB M Q C, ⁅l, a⁆ ∈ Vt M (LB M Q B) B Z t) :
    a ∈ QB C := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφQ, -⟩ := exists_actionHom_H0 hc.hyp hD
  have hcomm : ∀ l ∈ LB M Q C, ⁅l, a⁆ ∈ C ⊔ Z :=
    comm_mem_sup_Z_of_forall_mem_Vt (K := K) (M₀ := M₀) (φ := φ) hφπ hφQ hD h34 hspread H
      ht hs h2 hC hCY ha hl
  obtain ⟨μ, hμ, hμC⟩ := H.rootTrans h34 hspread C hC
  have hno : NoA2 Q Z (LB M Q C) := by rw [← hμC]; exact hc.noA2_conj H.noA2 hμ
  have hgen : GenByB M Q C := by rw [← hμC]; exact H.gen.conj_of_mem hμ
  have hXcomm : ∀ x ∈ Subgroup.zpowers a ⊔ Z, ∀ t ∈ LB M Q C, ⁅t, x⁆ ∈ C ⊔ Z :=
    comm_mem_sup_Z_of_mem_sup (hc := hc) hC ha.1 hcomm
  haveI : IsMulCommutative ↥(Q ⊓ QB Y) := (Sit.inf_QB_elemAbelian hs).1
  have hXQ : Subgroup.zpowers a ⊔ Z ≤ Q ⊓ Subgroup.centralizer (C : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · refine Subgroup.mem_inf.mpr ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun c hcC => ?_⟩
      exact Subgroup.mul_comm_of_mem_isMulCommutative (H := Q ⊓ QB Y)
        ⟨hC.le hcC, hCY hcC⟩ ha
    · intro z hz
      exact Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz,
        Subgroup.mem_centralizer_iff.mpr fun c hcC =>
          (Z_central (z := z) (q := c) hc.hyp hz (hC.le hcC)).symm⟩
  exact ((h34 G M Q Z C hC n H.width H.n_gt hno hgen) _ hXQ hXcomm
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))).2

theorem Good101.inf_QB_le_QB_of_root_of_not_caseA (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hB : ¬ CaseA Q Z t) (h2 : SLMNat hc t 2) {C : Subgroup G} (hC : Ctx M Q Z C)
    (hCY : C ≤ QB Y) : Q ⊓ QB Y ≤ QB C := by
  have hne : C ≠ Y := by
    intro h
    obtain ⟨c, hc, hc1⟩ := hC.exists_ne_one
    have hmem : c ∈ Y ⊓ Q := ⟨h ▸ hc, hC.le hc⟩
    rw [hs.X_inf_Q, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hYC : Y ≤ QB C := hc.hyp.le_QB_of_le_QB hC.conj hs.conj hne hCY
  have htLC : t ∈ LB M Q C := Subgroup.mem_sup_right ⟨hYC hs.mem, hs.memM⟩
  obtain ⟨μ, hμ, hμC⟩ := H.rootTrans h34 hspread C hC
  intro a ha
  refine Good101.mem_QB_of_forall_comm_LB_mem_Vt h34 hspread H ht hs h2 hC hCY ha ?_
  intro l hl
  have htm : t ∈ conjSubgroup μ (LB M Q B) := by
    rw [← hc.LB_conj hμ]
    rwa [← hμC] at htLC
  have hl' : l ∈ LB M Q (conjSubgroup μ B) := by rwa [← hμC] at hl
  exact Good101.comm_Rt_mem_Vt_of_not_caseA h34 hspread H ht hs hB
    (hc.LB_conj_le_Rt hμ htm hl') ha

theorem Good101.inf_QB_le_QB_of_not_caseA (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hB : ¬ CaseA Q Z t) (h2 : SLMNat hc t 2) : Q ⊓ QB Y ≤ QB B := by
  have hBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  exact Good101.inf_QB_le_QB_of_root_of_not_caseA h34 hspread H ht hs hB h2 hc hBY


end CFSG.RankThree.GF2n.Stroth80
