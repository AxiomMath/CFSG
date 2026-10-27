module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


@[expose] def sec8ImgUtRange {E K : Type} [AddCommGroup E] [Field K] [Module K E]
    (T : E ≃ₗ[K] E) : AddSubgroup E where
  carrier := {e | ∃ f, e = T f - f}
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨f', rfl⟩
    exact ⟨f + f', by rw [map_add]; abel⟩
  zero_mem' := ⟨0, by rw [map_zero, sub_self]⟩
  neg_mem' := by
    rintro _ ⟨f, rfl⟩
    exact ⟨-f, by rw [map_neg]; abel⟩

theorem mem_sec8ImgUtRange {E K : Type} [AddCommGroup E] [Field K] [Module K E]
    (T : E ≃ₗ[K] E) (e : E) : e ∈ sec8ImgUtRange T ↔ ∃ f, e = T f - f :=
  Iff.rfl

@[expose] def sec8ImgUtPre {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (R : AddSubgroup M₀.E) : Subgroup G where
  carrier := {u | u ∈ Q ∧ M₀.π u ∈ R}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Q.mul_mem ha hb, by rw [M₀.π_mul a ha b hb]; exact add_mem ha' hb'⟩
  one_mem' := ⟨Q.one_mem, by rw [Tim79.QuadModel.pi_one M₀]; exact R.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨Q.inv_mem ha, by rw [Tim79.QuadModel.pi_inv M₀ ha]; exact neg_mem ha'⟩

theorem mem_sec8ImgUtPre {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (R : AddSubgroup M₀.E) (u : G) :
    u ∈ sec8ImgUtPre M₀ R ↔ u ∈ Q ∧ M₀.π u ∈ R :=
  Iff.rfl

theorem sec8_img_Ut_iff {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {x : G} (hxM : x ∈ M) (hx2 : x ^ 2 ∈ Q)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : ∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y)) (e : M₀.E) :
    e ∈ M₀.img (Ut Q Z x) ↔ ∃ f : M₀.E, e = T f - f := by
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hzpow2 : ∀ i : ℤ, x ^ (2 * i) ∈ Q := by
    intro i
    rw [zpow_mul, zpow_two, ← pow_two]
    exact Q.zpow_mem hx2 i
  have hZS : Z ≤ sec8ImgUtPre M₀ (sec8ImgUtRange T) := by
    intro z hz
    refine (mem_sec8ImgUtPre M₀ _ z).mpr ⟨hZQ hz, ?_⟩
    rw [(M₀.π_ker z (hZQ hz)).mpr hz]
    exact (mem_sec8ImgUtRange T 0).mpr ⟨0, by rw [map_zero, sub_self]⟩
  constructor
  · intro he
    obtain ⟨u, huU, huQ, hu⟩ := (Tim79.QuadModel.mem_img M₀).mp he
    have hUS : Ut Q Z x ≤ sec8ImgUtPre M₀ (sec8ImgUtRange T) := by
      unfold Ut
      refine sup_le ?_ hZS
      rw [Subgroup.commutator_le]
      intro q hq k hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
      · exact hZS (M₀.comm_mem q hq _ (hzpow2 i))
      · obtain ⟨c, hcQ, hcx⟩ : ∃ c, c ∈ Q ∧ x ^ (2 * i + 1) = c * x :=
          ⟨x ^ (2 * i), hzpow2 i, zpow_add_one x (2 * i)⟩
        have hpQ : x * q⁻¹ * x⁻¹ ∈ Q := hQn x hxM q⁻¹ (Q.inv_mem hq)
        have hcp : c * (x * q⁻¹ * x⁻¹) * c⁻¹ ∈ Q :=
          Q.mul_mem (Q.mul_mem hcQ hpQ) (Q.inv_mem hcQ)
        have heq : ⁅q, c * x⁆ = q * (c * (x * q⁻¹ * x⁻¹) * c⁻¹) := by
          rw [commutatorElement_def]
          group
        have hval : M₀.π ⁅q, c * x⁆ = M₀.π q + T (-M₀.π q) := by
          rw [heq, M₀.π_mul q hq _ hcp,
            Tim79.QuadModel.pi_conj_self (M₀ := M₀) hcQ hpQ, hT q⁻¹ (Q.inv_mem hq),
            Tim79.QuadModel.pi_inv M₀ hq]
        rw [hcx]
        refine (mem_sec8ImgUtPre M₀ _ _).mpr ⟨?_, ?_⟩
        · rw [heq]
          exact Q.mul_mem hq hcp
        · rw [hval]
          exact (mem_sec8ImgUtRange T _).mpr ⟨-M₀.π q, by abel⟩
    have huS := hUS huU
    obtain ⟨-, hR⟩ := (mem_sec8ImgUtPre M₀ _ u).mp huS
    obtain ⟨f, hf⟩ := (mem_sec8ImgUtRange T _).mp hR
    exact ⟨f, hu.symm.trans hf⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj f
    have hA : x * y * x⁻¹ ∈ Q := hQn x hxM y hyQ
    have hwQ : x * y * x⁻¹ * y⁻¹ ∈ Q := Q.mul_mem hA (Q.inv_mem hyQ)
    have hwU : x * y * x⁻¹ * y⁻¹ ∈ Ut Q Z x := by
      have h3 : ⁅y, x⁆ ∈ ⁅Q, Subgroup.zpowers x⁆ :=
        Subgroup.commutator_mem_commutator hyQ (Subgroup.mem_zpowers x)
      have h4 : ⁅y, x⁆⁻¹ ∈ ⁅Q, Subgroup.zpowers x⁆ := inv_mem h3
      have h5 : ⁅y, x⁆⁻¹ = x * y * x⁻¹ * y⁻¹ := by
        rw [commutatorElement_inv, commutatorElement_def]
      rw [← h5]
      unfold Ut
      exact Subgroup.mem_sup_left h4
    have hπw : M₀.π (x * y * x⁻¹ * y⁻¹) = T (M₀.π y) - M₀.π y := by
      rw [M₀.π_mul _ hA _ (Q.inv_mem hyQ), Tim79.QuadModel.pi_inv M₀ hyQ, hT y hyQ,
        sub_eq_add_neg]
    rw [← hπw]
    exact Tim79.QuadModel.pi_mem_img M₀ hwU hwQ

theorem sec8_card_W_mul_card_V {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {t : G}
    (ht : t ∈ LB M Q B) (hV : Vt M (LB M Q B) B Z t = Ut Q Z t)
    (hW : Wt Q (Vt M (LB M Q B) B Z t) = Q1 hc t)
    (hP1 : ∀ (e : M₀.E) {T : M₀.E ≃ₗ[K] M₀.E}, (∀ y ∈ Q, M₀.π (t * y * t⁻¹) = T (M₀.π y)) →
      (e ∈ M₀.img (Ut Q Z t) ↔ ∃ f : M₀.E, e = T f - f)) :
    Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t) =
      Nat.card Q * Nat.card Z := by
  have htH : t ∈ H0 M Z := hc.LB_le_H0 ht
  have htM : t ∈ M := hc.LB_le_M ht
  have htC : t ∈ Subgroup.centralizer (Z : Set G) := (Subgroup.mem_inf.mp htH).2
  have hcz : ∀ z ∈ Z, t * z * t⁻¹ = z := by
    intro z hz
    rw [← Subgroup.mem_centralizer_iff.mp htC z hz, mul_inv_cancel_right]
  obtain ⟨T, hTπ, -, -⟩ := hD.linear_of_centralizes htM hcz
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  generalize Vt M (LB M Q B) B Z t = V at hVQ hZV hV hW ⊢
  have hWQ : Wt Q V ≤ Q := fun x hx => hx.1
  have hZW : Z ≤ Wt Q V := fun z hz => ⟨hZQ hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩
  have hWmem : ∀ x ∈ Q, (x ∈ Wt Q V ↔ M₀.π (t * x * t⁻¹) = M₀.π x) := by
    intro x hxQ
    have hxt : t * x * t⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) x).mp hxQ
    have hcomm : ⁅t, x⁆ ∈ Z ↔ M₀.π (t * x * t⁻¹) = M₀.π x :=
      Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ hxt
    have hiff : x ∈ Wt Q V ↔ x ∈ Q1 hc t := by rw [hW]
    rw [hiff, hc.mem_Q1_iff htM]
    exact ⟨fun h => hcomm.mp h.2, fun h => ⟨hxQ, hcomm.mpr h⟩⟩
  let g : M₀.E →+ M₀.E :=
    { toFun := fun e => T e - e
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add]; abel }
  have hg : ∀ e, g e = T e - e := fun e => rfl
  have himgW : M₀.img (Wt Q V) = g.ker := by
    ext e
    rw [AddMonoidHom.mem_ker, hg, sub_eq_zero]
    constructor
    · rintro ⟨x, hxW, hxQ, rfl⟩
      exact (hTπ x hxQ).symm.trans ((hWmem x hxQ).mp hxW)
    · intro h
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      exact ⟨x, (hWmem x hxQ).mpr ((hTπ x hxQ).trans h), hxQ, rfl⟩
  have himgV : M₀.img V = g.range := by
    ext e
    rw [AddMonoidHom.mem_range, hV, hP1 e hTπ]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, hg f⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, hg y⟩
  have hrank : Nat.card ↥(M₀.img (Wt Q V)) * Nat.card ↥(M₀.img V) = Nat.card M₀.E := by
    rw [himgW, himgV]
    exact AddSubgroup.card_ker_mul_card_range g
  have hWcard : Nat.card ↥(Wt Q V) = Nat.card Z * Nat.card ↥(M₀.img (Wt Q V)) :=
    M₀.card_eq hWQ hZW
  have hVcard : Nat.card ↥V = Nat.card Z * Nat.card ↥(M₀.img V) := M₀.card_eq hVQ hZV
  have hQcard : Nat.card ↥Q = Nat.card Z * Nat.card M₀.E := by
    have hall : ∀ e : M₀.E, e ∈ M₀.img Q := fun e => by
      obtain ⟨x, hxQ, hx⟩ := M₀.π_surj e
      exact ⟨x, hxQ, hxQ, hx⟩
    rw [M₀.card_eq (le_refl Q) hZQ]
    congr 1
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  rw [hWcard, hVcard, hQcard, ← hrank]
  ring

theorem sec8_card_arith (zc nE nU nP nA nV nQ nW nW₁ nV₁ : ℕ) (hzc : 0 < zc) (hnE : 0 < nE)
    (h1 : nV₁ = nV * zc) (h2 : nW = nW₁ * zc) (h3 : nW * nV = nQ * zc)
    (h4 : nV₁ = zc * nP) (h5 : nW₁ = zc * nU) (h6 : nQ = zc * nE) (h7 : nU * nA = nE) :
    nA = nP := by
  subst h2 h5 h6
  subst h1
  have hP : nV = nP := Nat.eq_of_mul_eq_mul_right hzc (by rw [h4]; ring)
  have hU : nU * nV = nE := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hzc hzc) ?_
    calc zc * zc * (nU * nV) = zc * nU * zc * nV := by ring
      _ = zc * nE * zc := h3
      _ = zc * zc * nE := by ring
  have hUpos : 0 < nU := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at h7; omega)
  exact (Nat.eq_of_mul_eq_mul_left hUpos (h7.trans hU.symm)).trans hP

theorem sec8_card_arith2 (zc nK nP nV nVi nV₁ : ℕ) (hzc : 0 < zc) (hK : nK = zc)
    (h1 : nV₁ = nV * zc) (h4 : nV₁ = zc * nP) (h5 : nV = zc * nVi) : nP = nVi * nK := by
  have key : zc * nP = zc * (nVi * zc) := by
    rw [← h4, h1, h5]
    ring
  rw [hK]
  exact Nat.eq_of_mul_eq_mul_left hzc key

theorem sec8_V1_le_Q {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) (t r : G) : Sec8V1 M Q Z B t r ≤ Q := by
  show ((Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t) ⊓
    ((Q ⊓ QB (conjSubgroup r B)) ⊔ Vt M (LB M Q B) B Z t) ≤ Q
  exact inf_le_left.trans (sup_le inf_le_left (hc.Vt_le_Q t))

theorem sec8_Z_le_V1 {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) (t r : G) : Z ≤ Sec8V1 M Q Z B t r := by
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVV₁ : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := by
    show Vt M (LB M Q B) B Z t ≤ ((Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t) ⊓
      ((Q ⊓ QB (conjSubgroup r B)) ⊔ Vt M (LB M Q B) B Z t)
    exact le_inf le_sup_right le_sup_right
  exact hZV.trans hVV₁

theorem sec8_W1_le_Q {G : Type} [Group G] [Finite G] (M Q Z B : Subgroup G) (t r : G) :
    Sec8W1 M Q Z B t r ≤ Q := by
  show Q ⊓ Subgroup.centralizer ((Sec8V1 M Q Z B t r : Subgroup G) : Set G) ≤ Q
  exact inf_le_left

theorem sec8_Z_le_W1 {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) (t r : G) : Z ≤ Sec8W1 M Q Z B t r := by
  intro z hz
  show z ∈ Q ⊓ Subgroup.centralizer ((Sec8V1 M Q Z B t r : Subgroup G) : Set G)
  refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact mul_inv_eq_iff_eq_mul.mp (hc.conj_Z_of_mem_Q (sec8_V1_le_Q hc t r hv) hz)

theorem sec8_img_W1_iff_perp {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t r : G} {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) (e : M₀.E) :
    e ∈ M₀.img (Sec8W1 M Q Z B t r) ↔ ∀ f ∈ M₀.img (Sec8V1 M Q Z B t r), M₀.B f e = 0 := by
  constructor
  · rintro ⟨w, hwW, hwQ, rfl⟩ f hf
    obtain ⟨v, hvV, hvQ, rfl⟩ := hf
    have hwW' : w ∈ Q ⊓ Subgroup.centralizer ((Sec8V1 M Q Z B t r : Subgroup G) : Set G) :=
      hwW
    have hvw : v * w = w * v := Subgroup.mem_centralizer_iff.mp hwW'.2 v hvV
    exact (M₀.comm_iff_B hD.reg hvQ hwQ).mp hvw
  · intro h
    obtain ⟨w, hwQ, hwe⟩ := M₀.π_surj e
    refine M₀.mem_img.mpr ⟨w, ?_, hwQ, hwe⟩
    show w ∈ Q ⊓ Subgroup.centralizer ((Sec8V1 M Q Z B t r : Subgroup G) : Set G)
    refine Subgroup.mem_inf.mpr ⟨hwQ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    refine (M₀.comm_iff_B hD.reg (sec8_V1_le_Q hc t r hv) hwQ).mpr ?_
    rw [hwe]
    exact h (M₀.π v) (M₀.pi_mem_img hv (sec8_V1_le_Q hc t r hv))

theorem sec8_img_W1_eq_orthogonal_span {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t r : G} {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) (e : M₀.E) :
    e ∈ M₀.img (Sec8W1 M Q Z B t r) ↔
      e ∈ M₀.B.orthogonal (Submodule.span K (M₀.img (Sec8V1 M Q Z B t r) : Set M₀.E)) := by
  rw [sec8_img_W1_iff_perp (t := t) (r := r) hc hD e, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h a ha
    have hle : Submodule.span K (M₀.img (Sec8V1 M Q Z B t r) : Set M₀.E) ≤
        LinearMap.ker (LinearMap.flip M₀.B e) := by
      rw [Submodule.span_le]
      exact fun f hf => h f hf
    exact LinearMap.mem_ker.mp (hle ha)
  · intro h f hf
    exact h f (Submodule.subset_span hf)

theorem sec8_img_W1_eq_orthogonal {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t r : G} {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (A : Submodule K M₀.E) (hA : (A : Set M₀.E) = ↑(M₀.img (Sec8V1 M Q Z B t r))) (e : M₀.E) :
    e ∈ M₀.img (Sec8W1 M Q Z B t r) ↔ e ∈ M₀.B.orthogonal A := by
  have hA' : A = Submodule.span K (M₀.img (Sec8V1 M Q Z B t r) : Set M₀.E) :=
    (Submodule.span_eq A).symm.trans (congrArg (Submodule.span K) hA)
  subst hA'
  exact sec8_img_W1_eq_orthogonal_span (t := t) (r := r) hc hD e

theorem sec8_card_img_V1 {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (h53a : Stroth53aStatement) :
    Nat.card ↥(M₀.img (Sec8V1 M Q Z B t r)) =
      Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) * Nat.card K := by
  obtain ⟨hV1card, -, -⟩ := h53a G M Q Z B hc n t hs.toSec5 hs.spNat r hr.mem hr.plane
    (conjSubgroup r B) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    (Sec8V1 M Q Z B t r) (Sec8W1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hcV₁ : Nat.card ↥(Sec8V1 M Q Z B t r) =
      Nat.card ↥Z * Nat.card ↥(M₀.img (Sec8V1 M Q Z B t r)) :=
    M₀.card_eq (sec8_V1_le_Q hc t r) (sec8_Z_le_V1 hc t r)
  have hcV : Nat.card ↥(Vt M (LB M Q B) B Z t) =
      Nat.card ↥Z * Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) :=
    M₀.card_eq (hc.Vt_le_Q t) sec39_Z_le_Vt
  have hzc : 0 < Nat.card ↥Z := by
    rw [← hD.card]
    exact Nat.card_pos
  exact sec8_card_arith2 _ _ _ _ _ _ hzc hD.card hV1card hcV₁ hcV

theorem sec8_img_V1_kclosed {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (h53a : Stroth53aStatement)
    (hcard : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t) =
      Nat.card Q * Nat.card Z) :
    ∃ A : Submodule K M₀.E, (A : Set M₀.E) = ↑(M₀.img (Sec8V1 M Q Z B t r)) := by
  obtain ⟨hV1card, hWcard, -⟩ := h53a G M Q Z B hc n t hs.toSec5 hs.spNat r hr.mem hr.plane
    (conjSubgroup r B) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    (Sec8V1 M Q Z B t r) (Sec8W1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hcV₁ : Nat.card ↥(Sec8V1 M Q Z B t r) =
      Nat.card ↥Z * Nat.card ↥(M₀.img (Sec8V1 M Q Z B t r)) :=
    M₀.card_eq (sec8_V1_le_Q hc t r) (sec8_Z_le_V1 hc t r)
  have hcW₁ : Nat.card ↥(Sec8W1 M Q Z B t r) =
      Nat.card ↥Z * Nat.card ↥(M₀.img (Sec8W1 M Q Z B t r)) :=
    M₀.card_eq (sec8_W1_le_Q M Q Z B t r) (sec8_Z_le_W1 hc t r)
  haveI hEfin : Finite M₀.E := Module.finite_of_finite K
  have himgQ : M₀.img Q = ⊤ := by
    rw [eq_top_iff]
    intro e _
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj e
    exact M₀.mem_img.mpr ⟨x, hxQ, hxQ, hx⟩
  have hQE : Nat.card ↥Q = Nat.card ↥Z * Nat.card M₀.E := by
    rw [M₀.card_eq le_rfl hD.reg.V_le, himgQ, AddSubgroup.card_top]
  have hzc : 0 < Nat.card ↥Z := by
    rw [← hD.card]
    exact Nat.card_pos
  have hnE : 0 < Nat.card M₀.E := Nat.card_pos
  obtain ⟨A, hAdef⟩ : ∃ A : Submodule K M₀.E,
      A = Submodule.span K (M₀.img (Sec8V1 M Q Z B t r) : Set M₀.E) := ⟨_, rfl⟩
  have hiff : ∀ e : M₀.E, e ∈ M₀.img (Sec8W1 M Q Z B t r) ↔ e ∈ M₀.B.orthogonal A := by
    intro e
    rw [hAdef]
    exact sec8_img_W1_eq_orthogonal_span (t := t) (r := r) hc hD e
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun x => ?_⟩
    rw [Tim79.QuadModel.B_comm, hy x, neg_zero]
  have hprod : Nat.card ↥(M₀.B.orthogonal A) * Nat.card ↥A = Nat.card M₀.E := by
    have hfin : Module.finrank K ↥(M₀.B.orthogonal A) =
        Module.finrank K M₀.E - Module.finrank K ↥A :=
      LinearMap.BilinForm.finrank_orthogonal hnd A
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(M₀.B.orthogonal A)),
      Module.natCard_eq_pow_finrank (K := K) (V := ↥A),
      Module.natCard_eq_pow_finrank (K := K) (V := M₀.E), hfin, ← pow_add,
      Nat.sub_add_cancel (Submodule.finrank_le A)]
  have hpq : (fun e : M₀.E => e ∈ M₀.img (Sec8W1 M Q Z B t r)) =
      fun e : M₀.E => e ∈ M₀.B.orthogonal A :=
    funext fun e => propext (hiff e)
  have hcW : Nat.card ↥(M₀.img (Sec8W1 M Q Z B t r)) = Nat.card ↥(M₀.B.orthogonal A) :=
    Nat.card_congr (Equiv.subtypeEquivProp hpq)
  have hcount : Nat.card ↥(M₀.img (Sec8W1 M Q Z B t r)) * Nat.card ↥A = Nat.card M₀.E := by
    rw [hcW]
    exact hprod
  have hnA : Nat.card ↥A = Nat.card ↥(M₀.img (Sec8V1 M Q Z B t r)) :=
    sec8_card_arith _ _ _ _ _ _ _ _ _ _ hzc hnE hV1card hWcard hcard hcV₁ hcW₁ hQE hcount
  have hPA : M₀.img (Sec8V1 M Q Z B t r) ≤ A.toAddSubgroup := by
    rw [hAdef]
    exact fun e he => Submodule.subset_span he
  have hPeq : M₀.img (Sec8V1 M Q Z B t r) = A.toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hPA (le_of_eq hnA)
  exact ⟨A, by rw [hPeq, Submodule.coe_toAddSubgroup]⟩

theorem sec8_pi_comm {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {x w : G} {f : M₀.E → M₀.E} (hw : w ∈ Q)
    (hxw : x * w * x⁻¹ ∈ Q) (hf : M₀.π (x * w * x⁻¹) = f (M₀.π w)) :
    M₀.π ⁅x, w⁆ = f (M₀.π w) - M₀.π w := by
  rw [commutatorElement_def, M₀.π_mul _ hxw _ (Q.inv_mem hw), Tim79.QuadModel.pi_inv M₀ hw, hf,
    sub_eq_add_neg]

theorem sec8_exists_codim_one (h310chi : Stroth310ChiStatement) (h53a : Stroth53aStatement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {n : ℕ} {t r : G}
    (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) :
    ∃ A A₀ : Submodule K M₀.E, (∀ e, e ∈ A ↔ e ∈ M₀.img (Sec8V1 M Q Z B t r)) ∧
      (∀ e, e ∈ A₀ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧ A₀ ≤ A ∧
      Module.finrank K ↥A = Module.finrank K ↥A₀ + 1 := by
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨hV, hWQ1⟩ := h310chi G M Q Z B hc n t h5 (Or.inl hs.spNat)
  haveI hEfin : Module.Finite K M₀.E := M₀.fin
  haveI hEfinite : Finite M₀.E := Module.finite_of_finite K
  have hq : Nat.card K = Nat.card Z := hD.card
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have htcz : ∀ z ∈ Z, t * z * t⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp (hc.LB_le_H0 ht).2 z hz, mul_inv_cancel_right]
  have hP1 : ∀ (e : M₀.E) {T : M₀.E ≃ₗ[K] M₀.E},
      (∀ y ∈ Q, M₀.π (t * y * t⁻¹) = T (M₀.π y)) →
      (e ∈ M₀.img (Ut Q Z t) ↔ ∃ f : M₀.E, e = T f - f) :=
    fun e _ hT => sec8_img_Ut_iff hc hD htM (hc.sq_mem_Q_of_mem_LB ht) hT e
  have hcard := sec8_card_W_mul_card_V hc hD ht hV hWQ1 hP1
  obtain ⟨A, hA⟩ := sec8_img_V1_kclosed hc hs hr hD h53a hcard
  have hAmem : ∀ e, e ∈ A ↔ e ∈ M₀.img (Sec8V1 M Q Z B t r) := fun e => Set.ext_iff.mp hA e
  obtain ⟨Tt, hTtπ, -, -⟩ := hD.linear_of_centralizes htM htcz
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : Submodule K M₀.E, A₀ = LinearMap.range
      ((Tt : M₀.E →ₗ[K] M₀.E) - 1) := ⟨_, rfl⟩
  have hA₀mem : ∀ e, e ∈ A₀ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
    intro e
    rw [hA₀def, hV, sec8_img_Ut_iff hc hD htM (hc.sq_mem_Q_of_mem_LB ht) hTtπ e,
      LinearMap.mem_range]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f, by rw [← hf]; simp⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, by rw [hf]; simp⟩
  have hVV₁ : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := by
    show Vt M (LB M Q B) B Z t ≤ ((Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t) ⊓
      ((Q ⊓ QB (conjSubgroup r B)) ⊔ Vt M (LB M Q B) B Z t)
    exact le_inf le_sup_right le_sup_right
  have hA₀A : A₀ ≤ A := fun e he => (hAmem e).mpr (M₀.img_mono hVV₁ ((hA₀mem e).mp he))
  refine ⟨A, A₀, hAmem, hA₀mem, hA₀A, ?_⟩
  have h1 := sec8_card_img_V1 hc hs hr hD h53a
  have h2 : Nat.card ↥A = Nat.card ↥(M₀.img (Sec8V1 M Q Z B t r)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hAmem)
  have h3 : Nat.card ↥A₀ = Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hA₀mem)
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥A)] at h2
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥A₀)] at h3
  have hK2 : 2 ≤ Nat.card K := by rw [hq]; exact hq2
  have key : Nat.card K ^ Module.finrank K ↥A =
      Nat.card K ^ (Module.finrank K ↥A₀ + 1) := by
    rw [h2, h1, pow_succ, h3]
  exact Nat.pow_right_injective hK2 key

end CFSG.RankThree.GF2n.Stroth80
