module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveYBase
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNbBound

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

structure MoveFrameRep {K E X : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [Group X] (B : LinearMap.BilinForm K E) (φ : X →* (E ≃ₗ[K] E))
    (V L Nb Rb : Subgroup X) (Tt : X → Submodule K E) : Prop where
  Nb_semi : ∀ z ∈ Nb, z ∉ V → ∀ w ∈ V, ∃ m ∈ Nb, m * z * m⁻¹ = w * z
  semilinear : ∀ Y : Subgroup X, Y ≤ normalizer (V : Set X) → (∀ y ∈ Y, y * y = 1) →
    (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) →
      Nat.card Y ≤ 2 * Nat.card ↥(centralizer (V : Set X) ⊓ Y)
  two_elements : ∀ k ∈ normalizer (V : Set X), (∀ a ∈ V, k * a = a * k) →
    IsPGroup 2 (zpowers k) → k ∈ Rb
  CL : ∀ r ∈ Rb, (∀ l ∈ L, r * l = l * r) → r ∈ L
  quad : ∀ s ∈ L, ∀ u ∈ L, ∀ w, opm (φ s) (opm (φ u) w) = 0
  pair_dim : ∀ g₁ g₂ : X,
    (∀ a ∈ V, ∀ b ∈ V, (g₁ * a * g₁⁻¹) * (g₂ * b * g₂⁻¹) = (g₂ * b * g₂⁻¹) * (g₁ * a * g₁⁻¹)) →
    (∀ b ∈ V, g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ ∈ Rb) →
    (¬ ∀ b ∈ V, g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ ∈ Nb) →
      Module.finrank K ↥(Tt g₁ ⊓ Tt g₂) = 2
  image_dim : ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
    2 ≤ Module.finrank K ↥((Tt g).map (B.orthogonal (Tt 1)).mkQ)
  no_isotropic : ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
    ∀ Lm : Submodule K E, Tt 1 ≤ Lm → Lm ≤ B.orthogonal (Tt 1) →
      (∀ r ∈ Rb, ∀ w ∈ Lm, φ r w ∈ Lm) → (∀ x ∈ Lm, ∀ y ∈ Lm, B x y = 0) →
      ∀ a ∈ V, a ≠ 1 →
        ¬ ((B.orthogonal (Tt 1)).map (opm (φ (g * a * g⁻¹))) ≤ Lm)
  transvection : ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
    ∀ a ∈ V, ∀ b ∈ V, ∀ x ∈ L, ⁅g * a * g⁻¹, ⁅x, g * b * g⁻¹⁆⁆ ∈ V

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem exists_barAct {G : Type} [Group G] {M Q Hs : Subgroup G} [(Q.subgroupOf M).Normal]
    (hQH : Q ≤ Hs) (hHM : Hs ≤ M) {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (φ₀ : ↥Hs →* (E ≃ₗ[K] E)) (hker : ∀ m : ↥Hs, φ₀ m = 1 ↔ (m : G) ∈ Q) :
    ∃ φ : ↥(bar M Q Hs) →* (E ≃ₗ[K] E), Function.Injective φ ∧
      ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q Hs) (hyH : (y : G) ∈ Hs),
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ = φ₀ ⟨(y : G), hyH⟩ := by
  haveI hN : (Q.subgroupOf Hs).Normal := normal_subgroupOf_of_le hQH hHM
  have hle : Q.subgroupOf Hs ≤ φ₀.ker := by
    intro x hx
    exact MonoidHom.mem_ker.mpr ((hker x).mpr (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (↥Hs ⧸ Q.subgroupOf Hs) →* (E ≃ₗ[K] E),
      ∀ y : ↥Hs, ψ (QuotientGroup.mk y) = φ₀ y :=
    ⟨QuotientGroup.lift (Q.subgroupOf Hs) φ₀ hle, fun y => QuotientGroup.lift_mk _ hle y⟩
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hψ] at hx
    exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr ((hker y).mp hx))
  obtain ⟨ε, hε⟩ : ∃ ε : (↥Hs ⧸ Q.subgroupOf Hs) ≃* ↥(bar M Q Hs),
      ∀ x : ↥Hs ⧸ Q.subgroupOf Hs, ((ε x : ↥(bar M Q Hs)) : ↥M ⧸ Q.subgroupOf M) =
        embBar M Q hHM hQH x :=
    ⟨(MonoidHom.ofInjective (embBar_injective hHM hQH)).trans
      (MulEquiv.subgroupCongr (embBar_range hHM hQH)), fun x => rfl⟩
  refine ⟨ψ.comp ε.symm.toMonoidHom, hψinj.comp ε.symm.injective, fun y hy hyH => ?_⟩
  have hw : ε.symm ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ =
      QuotientGroup.mk (⟨(y : G), hyH⟩ : ↥Hs) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext ((hε (QuotientGroup.mk ⟨(y : G), hyH⟩)).trans
      (embBar_mk hHM hQH ⟨(y : G), hyH⟩)).symm
  show ψ (ε.symm ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩) = φ₀ ⟨(y : G), hyH⟩
  rw [hw, hψ]

theorem quadModel_form_facts {G : Type} [Group G] {Q V : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q V K γ) :
    M₀.B.Nondegenerate ∧ M₀.B.IsRefl ∧
      ∀ T : M₀.E ≃ₗ[K] M₀.E, (∀ e, M₀.Qf (T e) = M₀.Qf e) →
        ∀ u v, M₀.B (T u) (T v) = M₀.B u v := by
  have hsymm : ∀ e f, M₀.B e f = M₀.B f e := by
    intro e f
    have h1 := M₀.Qf_add e f
    have h1' := M₀.Qf_add f e
    rw [add_comm f e] at h1'
    linear_combination h1' - h1
  refine ⟨?_, fun x y h => (hsymm x y).symm.trans h, ?_⟩
  · exact And.intro (fun e he => M₀.nondeg e he)
      (fun f hf => M₀.nondeg f fun g => (hsymm f g).trans (hf g))
  · intro T hT u v
    have h1 := M₀.Qf_add (T u) (T v)
    have h2' := M₀.Qf_add u v
    rw [← map_add T u v, hT (u + v), hT u, hT v] at h1
    linear_combination h2' - h1

theorem range_opm_conj {K E : Type*} [Field K] [AddCommGroup E] [Module K E] (T S : E ≃ₗ[K] E) :
    LinearMap.range (opm (T * S * T⁻¹)) = (LinearMap.range (opm S)).map (T : E →ₗ[K] E) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    refine Submodule.mem_map.mpr ⟨opm S (T.symm x), LinearMap.mem_range.mpr ⟨T.symm x, rfl⟩, ?_⟩
    simp [opm_apply]
  · intro hy
    obtain ⟨w, hw, hTw⟩ := Submodule.mem_map.mp hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
    refine LinearMap.mem_range.mpr ⟨T u, ?_⟩
    rw [← hTw]
    simp [opm_apply]

private theorem opmQmPiOne {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) : M₀.π 1 = 0 := by
  have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  have h' : M₀.π 1 + 0 = M₀.π 1 + M₀.π 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

private theorem opmQmPiInv {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {x : G} (hx : x ∈ Q) :
    M₀.π x⁻¹ = -M₀.π x := by
  have h := M₀.π_mul x hx x⁻¹ (Q.inv_mem hx)
  have h1 : x * x⁻¹ = 1 := by simp
  rw [h1, opmQmPiOne M₀] at h
  have h2 : M₀.π x⁻¹ + M₀.π x = 0 := by rw [add_comm]; exact h.symm
  exact eq_neg_of_add_eq_zero_left h2

theorem range_opm_eq_image {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (z : G) (T : M₀.E ≃ₗ[K] M₀.E) (hZQ : Z ≤ Q)
    (hzQ : ∀ x ∈ Q, z * x * z⁻¹ ∈ Q) (hT : ∀ x ∈ Q, M₀.π (z * x * z⁻¹) = T (M₀.π x))
    (hz2 : z ^ 2 ∈ Q) :
    (LinearMap.range (opm T) : Set M₀.E) = M₀.π '' ((Ut Q Z z : Subgroup G) : Set G) := by
  have hRmem : ∀ u : M₀.E, T u - u ∈ LinearMap.range (opm T) := by
    intro u
    have h := LinearMap.mem_range_self (opm T) u
    rwa [opm_apply] at h
  have hzinv : ∀ x ∈ Q, z⁻¹ * x * z ∈ Q ∧ M₀.π (z⁻¹ * x * z) = T (M₀.π x) := by
    intro x hx
    have hc : z * x * z⁻¹ ∈ Q := hzQ x hx
    have hiQ : (z ^ 2)⁻¹ ∈ Q := Q.inv_mem hz2
    have hid : z⁻¹ * x * z = (z ^ 2)⁻¹ * (z * x * z⁻¹) * z ^ 2 := by group
    rw [hid]
    refine ⟨Q.mul_mem (Q.mul_mem hiQ hc) hz2, ?_⟩
    rw [M₀.π_mul _ (Q.mul_mem hiQ hc) _ hz2, M₀.π_mul _ hiQ _ hc, opmQmPiInv M₀ hz2,
      hT x hx]
    abel
  have hpow : ∀ k : ℤ, ∀ x ∈ Q, z ^ k * x * (z ^ k)⁻¹ ∈ Q ∧
      M₀.π (z ^ k * x * (z ^ k)⁻¹) - M₀.π x ∈ LinearMap.range (opm T) := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [zpow_zero, one_mul, inv_one, mul_one, sub_self]
      exact ⟨hx, Submodule.zero_mem _⟩
    | succ n ih =>
      intro x hx
      have hid : z ^ ((n : ℤ) + 1) * x * (z ^ ((n : ℤ) + 1))⁻¹
          = z ^ (n : ℤ) * (z * x * z⁻¹) * (z ^ (n : ℤ))⁻¹ := by
        rw [zpow_add_one]; group
      obtain ⟨h1, h2⟩ := ih (z * x * z⁻¹) (hzQ x hx)
      have h3 : M₀.π (z * x * z⁻¹) - M₀.π x ∈ LinearMap.range (opm T) := by
        rw [hT x hx]; exact hRmem _
      rw [hid]
      refine ⟨h1, ?_⟩
      have h4 := Submodule.add_mem _ h2 h3
      rwa [sub_add_sub_cancel] at h4
    | pred n ih =>
      intro x hx
      have hid : z ^ (-(n : ℤ) - 1) * x * (z ^ (-(n : ℤ) - 1))⁻¹
          = z ^ (-(n : ℤ)) * (z⁻¹ * x * z) * (z ^ (-(n : ℤ)))⁻¹ := by
        rw [zpow_sub_one]; group
      obtain ⟨h1, h2⟩ := ih (z⁻¹ * x * z) (hzinv x hx).1
      have h3 : M₀.π (z⁻¹ * x * z) - M₀.π x ∈ LinearMap.range (opm T) := by
        rw [(hzinv x hx).2]; exact hRmem _
      rw [hid]
      refine ⟨h1, ?_⟩
      have h4 := Submodule.add_mem _ h2 h3
      rwa [sub_add_sub_cancel] at h4
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G,
      ∀ w, w ∈ S ↔ (w ∈ Q ∧ M₀.π w ∈ LinearMap.range (opm T)) :=
    ⟨{ carrier := {w | w ∈ Q ∧ M₀.π w ∈ LinearMap.range (opm T)}
       mul_mem' := fun {a b} ha hb => by
         obtain ⟨ha1, ha2⟩ := ha
         obtain ⟨hb1, hb2⟩ := hb
         refine ⟨Q.mul_mem ha1 hb1, ?_⟩
         rw [M₀.π_mul a ha1 b hb1]
         exact Submodule.add_mem _ ha2 hb2
       one_mem' := by
         refine ⟨Q.one_mem, ?_⟩
         rw [opmQmPiOne M₀]
         exact Submodule.zero_mem _
       inv_mem' := fun {a} ha => by
         obtain ⟨ha1, ha2⟩ := ha
         refine ⟨Q.inv_mem ha1, ?_⟩
         rw [opmQmPiInv M₀ ha1]
         exact Submodule.neg_mem _ ha2 }, fun w => Iff.rfl⟩
  have hZS : Z ≤ S := by
    intro w hw
    rw [hS]
    refine ⟨hZQ hw, ?_⟩
    rw [(M₀.π_ker w (hZQ hw)).mpr hw]
    exact Submodule.zero_mem _
  have hcomm : ∀ k : ℤ, ∀ x ∈ Q, ⁅x, z ^ k⁆ ∈ S := by
    intro k x hx
    obtain ⟨h1, h2⟩ := hpow k x hx
    have hid : ⁅x, z ^ k⁆ = x * (z ^ k * x * (z ^ k)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hS, hid]
    refine ⟨Q.mul_mem hx (Q.inv_mem h1), ?_⟩
    rw [M₀.π_mul x hx _ (Q.inv_mem h1), opmQmPiInv M₀ h1]
    convert Submodule.neg_mem _ h2 using 1
    abel
  have hcomm_le : ⁅Q, Subgroup.zpowers z⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact hcomm k x hx
  have hUt_le : Ut Q Z z ≤ S := by
    show ⁅Q, Subgroup.zpowers z⁆ ⊔ Z ≤ S
    exact sup_le hcomm_le hZS
  ext e
  simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj u
    refine ⟨⁅z, x⁆, ?_, ?_⟩
    · have hc1 : ⁅x, z⁆ ∈ ⁅Q, Subgroup.zpowers z⁆ :=
        Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers z)
      have hid : ⁅z, x⁆ = ⁅x, z⁆⁻¹ := (commutatorElement_inv x z).symm
      have hc2 : ⁅z, x⁆ ∈ ⁅Q, Subgroup.zpowers z⁆ := by
        rw [hid]
        exact (⁅Q, Subgroup.zpowers z⁆).inv_mem hc1
      show ⁅z, x⁆ ∈ ⁅Q, Subgroup.zpowers z⁆ ⊔ Z
      exact Subgroup.mem_sup_left hc2
    · rw [opm_apply, commutatorElement_def, M₀.π_mul _ (hzQ x hx) _ (Q.inv_mem hx),
        opmQmPiInv M₀ hx, hT x hx, sub_eq_add_neg]
  · rintro ⟨w, hw, rfl⟩
    exact LinearMap.mem_range.mp ((hS w).mp (hUt_le hw)).2

theorem natCard_image_pi {G : Type} [Group G] [Finite G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {W : Subgroup G} (hWQ : W ≤ Q) (hZW : Z ≤ W) :
    Nat.card ↥(M₀.π '' (W : Set G)) * Nat.card Z = Nat.card W := by
  have key : ∀ a b : ↥W, (a : G)⁻¹ * (b : G) ∈ Z ↔ M₀.π (a : G) = M₀.π (b : G) := by
    intro a b
    have haQ : (a : G) ∈ Q := hWQ a.2
    have hbQ : (b : G) ∈ Q := hWQ b.2
    have hcQ : (a : G)⁻¹ * (b : G) ∈ Q := Q.mul_mem (Q.inv_mem haQ) hbQ
    rw [← M₀.π_ker _ hcQ, M₀.π_mul _ (Q.inv_mem haQ) _ hbQ, opmQmPiInv M₀ haQ,
      neg_add_eq_zero]
  let f : ↥W → ↥(M₀.π '' (W : Set G)) := fun w => ⟨M₀.π (w : G), (w : G), w.2, rfl⟩
  have hfab : ∀ a b : ↥W, a⁻¹ * b ∈ Z.subgroupOf W ↔ f a = f b := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, key a b]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  let F : ↥W ⧸ Z.subgroupOf W → ↥(M₀.π '' (W : Set G)) :=
    Quotient.lift f (fun a b hab => (hfab a b).mp (QuotientGroup.leftRel_apply.mp hab))
  have hF : Function.Bijective F := by
    constructor
    · intro q1 q2 h
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q1
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q2
      exact QuotientGroup.eq.mpr ((hfab a b).mpr h)
    · intro e
      obtain ⟨w, hw, hwe⟩ := e.2
      exact ⟨QuotientGroup.mk (⟨w, hw⟩ : ↥W), Subtype.ext hwe⟩
  have hidx : (Z.subgroupOf W).index = Nat.card ↥(M₀.π '' (W : Set G)) := by
    unfold Subgroup.index
    exact Nat.card_congr (Equiv.ofBijective F hF)
  have hH : Nat.card ↥(Z.subgroupOf W) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  rw [← hidx, ← hH, mul_comm]
  exact Subgroup.card_mul_index (H := Z.subgroupOf W)

@[expose] def Sec717MoveRepStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    ∀ (m : ℕ) (γ : G → GaloisField 2 m) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ),
      GlobalModelData M Q Z γ M₀ →
      ∀ (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E)),
        (∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
          x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
            φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) →
        ∀ (Tt : ↥(bar M Q (H0 M Z)) → Submodule (GaloisField 2 m) M₀.E),
          (∀ g a : ↥(bar M Q (H0 M Z)), a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) →
            a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g) →
          MoveFrameRep M₀.B φ ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
            ((bar M Q L).subgroupOf (bar M Q (H0 M Z)))
            ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
            ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) Tt

theorem Ctx.move_Tt_facts (hZV : Sec7ZVStatement) (hZc : Sec7CentreMpStatement)
    (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hKcard : Nat.card K = Nat.card Z)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) :
    ∃ Tt : ↥(bar M Q (H0 M Z)) → Submodule K M₀.E,
      (∀ g a : ↥(bar M Q (H0 M Z)), a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) → a ≠ 1 →
        LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g) ∧
      (∀ g, Module.finrank K ↥(Tt g) = 6) ∧
      (∀ n ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ w ∈ Tt 1, φ n w = w) ∧
      (∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
        (∀ w ∈ Tt 1, φ r w = w) →
          r ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZVt : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)
  have hVH : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans hRH)
  have hlift : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      ∃ (z : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) z ∈ bar M Q (H0 M Z)), (z : G) ∈ Z0 ∧
        a = ⟨QuotientGroup.mk' (Q.subgroupOf M) z, hy⟩ := by
    intro a ha ha1
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (a : Mbar M Q)
    have hzZ : (z : G) ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 z).mp (hz ▸ Subgroup.mem_subgroupOf.mp ha)
    exact ⟨z, hz ▸ a.2, hzZ, Subtype.ext hz.symm⟩
  have hrange : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      (LinearMap.range (opm (φ a)) : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
    intro a ha ha1
    obtain ⟨z, hy, hzZ, rfl⟩ := hlift a ha ha1
    have hzR : (z : G) ∈ Rt M (LB M Q B) t := hZ0.le hzZ
    have hzQ : ∀ x ∈ Q, (z : G) * x * (z : G)⁻¹ ∈ Q := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 z.2) x).mp hx
    have hz2 : (z : G) ^ 2 ∈ Q := by
      have h := sq_eq_one_bar hc hs hZc hZ0 (QuotientGroup.mk' (Q.subgroupOf M) z)
        ((mk_mem_bar_iff_sec4 hQZ0 z).mpr hzZ)
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact Subgroup.mem_subgroupOf.mp h
    have hzNQ : (z : G) ∉ Q := fun h => ha1 (Subtype.ext
      ((QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_subgroupOf.mpr h)))
    have hZVz : Ut Q Z (z : G) = Vt M (LB M Q B) B Z t :=
      hZV G M Q Z B hc n t hs Z0 hZ0 (z : G) hzZ hzNQ
    have h1 := range_opm_eq_image M₀ (z : G) (φ ⟨QuotientGroup.mk' (Q.subgroupOf M) z, hy⟩) hZQ
      hzQ (fun x hx => hφπ z hy x hx) hz2
    rw [h1, hZVz]
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q Z0 :=
    (mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) := hVH hsbar
  have ha₀V : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ∈
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hsbar
  have ha₀1 : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  set a₀ : ↥(bar M Q (H0 M Z)) := ⟨_, hsH⟩ with ha₀
  let Tt : ↥(bar M Q (H0 M Z)) → Submodule K M₀.E := fun g =>
    (LinearMap.range (opm (φ a₀))).map ((φ g : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
  have hTt1 : Tt 1 = LinearMap.range (opm (φ a₀)) := by
    simp [Tt]
  have hTt1set : (Tt 1 : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
    rw [hTt1]
    exact hrange a₀ ha₀V ha₀1
  refine ⟨Tt, ?_, ?_, ?_, ?_⟩
  · intro g a ha ha1
    have hsame : LinearMap.range (opm (φ a)) = LinearMap.range (opm (φ a₀)) :=
      SetLike.coe_injective ((hrange a ha ha1).trans (hrange a₀ ha₀V ha₀1).symm)
    rw [map_mul, map_mul, map_inv, range_opm_conj, hsame]
  · intro g
    haveI := Fintype.ofFinite K
    haveI : Finite M₀.E := Module.finite_of_finite K
    have h1 : Nat.card ↥(LinearMap.range (opm (φ a₀))) =
        Nat.card ↥(M₀.π '' (Vt M (LB M Q B) B Z t : Set G)) :=
      congrArg (fun S : Set M₀.E => Nat.card ↥S) (hrange a₀ ha₀V ha₀1)
    have h2 := natCard_image_pi M₀ hVtQ hZVt
    have h3 := card_Vt_of_plus hp3
    have h4 : Nat.card ↥(M₀.π '' (Vt M (LB M Q B) B Z t : Set G)) * Nat.card Z =
        Nat.card Z ^ 6 * Nat.card Z := by
      rw [h2, h3]
      ring
    have h5 := Nat.eq_of_mul_eq_mul_right Nat.card_pos h4
    haveI : Fintype ↥(LinearMap.range (opm (φ a₀))) := Fintype.ofFinite _
    have h6 := Module.card_eq_pow_finrank (K := K) (V := ↥(LinearMap.range (opm (φ a₀))))
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := K), h1, h5, hKcard] at h6
    have hq : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
    have h7 : Module.finrank K ↥(LinearMap.range (opm (φ a₀))) = 6 :=
      (Nat.pow_right_injective hq h6).symm
    show Module.finrank K ↥((LinearMap.range (opm (φ a₀))).map
      ((φ g : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)) = 6
    rw [LinearEquiv.finrank_map_eq]
    exact h7
  · intro nn hnn w hw
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (nn : Mbar M Q)
    have hyCN : (y : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hnn)
    have hw' : w ∈ (Tt 1 : Set M₀.E) := hw
    rw [hTt1set] at hw'
    obtain ⟨v, hv, rfl⟩ := hw'
    have hyH : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ nn.2
    have hnn' : nn = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyH⟩ := Subtype.ext hy.symm
    rw [hnn', ← hφπ y hyH v (hVtQ hv)]
    have hcZ : ⁅(y : G), v⁆ ∈ Z := (Ctx.mem_CN.mp hyCN).2 v hv
    have hcQ : ⁅(y : G), v⁆ ∈ Q := hZQ hcZ
    have hyv : (y : G) * v * (y : G)⁻¹ = ⁅(y : G), v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [hyv, M₀.π_mul _ hcQ v (hVtQ hv), (M₀.π_ker _ hcQ).mpr hcZ, zero_add]
  · intro r hr hfix
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (r : Mbar M Q)
    have hyR : (y : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hr)
    have hyH : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ r.2
    have hrr : r = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyH⟩ := Subtype.ext hy.symm
    refine Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQN y).mpr ?_ |> fun h => hy ▸ h)
    refine Ctx.mem_CN.mpr ⟨hyR, fun v hv => ?_⟩
    have hyM : (y : G) ∈ M := y.2
    have hvQ : v ∈ Q := hVtQ hv
    have hπv : M₀.π v ∈ Tt 1 := by
      have : M₀.π v ∈ (Tt 1 : Set M₀.E) := by
        rw [hTt1set]
        exact ⟨v, hv, rfl⟩
      exact this
    have hf := hfix _ hπv
    rw [hrr, ← hφπ y hyH v hvQ] at hf
    have hyvQ : (y : G) * v * (y : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2) v).mp hvQ
    have hcQ : ⁅(y : G), v⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hyvQ (Q.inv_mem hvQ)
    have hyv : (y : G) * v * (y : G)⁻¹ = ⁅(y : G), v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [hyv, M₀.π_mul _ hcQ v hvQ] at hf
    have h0 : M₀.π ⁅(y : G), v⁆ = 0 := by
      have := add_eq_right.mp hf
      exact this
    exact (M₀.π_ker _ hcQ).mp h0

theorem sec717MoveFrame_of_rep (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (hCN : Sec7CommNStatement)
    (hRep : Sec717MoveRepStatement) : Sec717MoveFrameStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZNc hTI L hL hLn
  have Bs := Ctx.yBase h34 h311a hZt hZcard hZc h78 hc hs hp3 hZ0 hZNc hTI hL hLn
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  obtain ⟨m, γ, M₀, hmcard, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ₀, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp hM
  obtain ⟨φ, hφinj, hφmk⟩ := exists_barAct hQH hHM φ₀ hφker
  have hφπ' : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z))
      (x : G), x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x) := by
    intro y hy x hx
    have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hy
    rw [hφmk y hy hyH]
    exact hφπ ⟨(y : G), hyH⟩ x hx
  have hQf : ∀ x : ↥(bar M Q (H0 M Z)), ∀ e, M₀.Qf (φ x e) = M₀.Qf e := by
    intro x e
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
    have hxy : x = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy ▸ x.2⟩ := Subtype.ext hy.symm
    have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp (hy ▸ x.2)
    rw [hxy, hφmk y _ hyH]
    exact hφQ ⟨(y : G), hyH⟩ e
  obtain ⟨Tt, hTtR, hTtrank, hTtN, hTtR'⟩ :=
    Ctx.move_Tt_facts hZV hZc hZcard hc hs hp3 hZ0 M₀ hM.card φ hφπ'
  have hrep := hRep G M Q Z B hc n t hs hp3 Z0 hZ0 hZNc hTI L hL hLn m γ M₀ hM φ hφπ' Tt hTtR
  obtain ⟨hnd, hrefl, hisom⟩ := quadModel_form_facts M₀
  have h2 : (2 : GaloisField 2 m) = 0 := by
    have := CharP.cast_eq_zero (GaloisField 2 m) 2
    simpa using this
  have hNcomm : ∀ a ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ b ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
        ⁅a, b⁆ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
    intro a ha b hb
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (a : Mbar M Q)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (b : Mbar M Q)
    have hxN : (x : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN x).mp (hx ▸ Subgroup.mem_subgroupOf.mp ha)
    have hyN : (y : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hb)
    have hcomm : ⁅(x : G), (y : G)⁆ ∈ Z0 :=
      hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hxN hyN)
    rw [Subgroup.mem_subgroupOf]
    show ⁅(a : Mbar M Q), (b : Mbar M Q)⁆ ∈ bar M Q Z0
    rw [← hx, ← hy, ← map_commutatorElement]
    have hxy : (((⁅x, y⁆ : ↥M)) : G) = ⁅(x : G), (y : G)⁆ := by
      simp [commutatorElement_def]
    exact (mk_mem_bar_iff_sec4 hQZ0 ⁅x, y⁆).mpr (hxy ▸ hcomm)
  refine ⟨GaloisField 2 m, inferInstance, M₀.E, M₀.acg, M₀.mod, M₀.fin, M₀.B, φ, Tt,
    Nat.card Z, ?_⟩
  exact
    { char2 := h2
      nondeg := hnd
      refl := hrefl
      inj := hφinj
      isom := fun x u v => hisom (φ x) (hQf x) u v
      V_le_L := Bs.VL
      L_le_Nb := Bs.LN
      Nb_le_Rb := Bs.NR
      V_comm := fun a ha b hb => Bs.Vc a ha b (Bs.LN (Bs.VL hb))
      V_sq := Bs.Vsq
      V_card := Bs.Vcard
      q_ge := hc.hyp.q4
      ti := Bs.ti
      L_comm := Bs.Lcomm
      L_card := Bs.Lcard
      L_norm := fun k hk l hl => by
        rw [← Bs.K_eq] at hk
        exact (Subgroup.mem_normalizer_iff.mp (Bs.Ln k hk) l).mp hl
      Rb_le_K := fun r hr => by
        rw [← Bs.K_eq]
        exact Bs.RK hr
      Nb_comm := hNcomm
      Nb_center := Bs.ZN
      Nb_semi := hrep.Nb_semi
      Nb_bound := abelian_card_le_of_semiextraspecial _ _ (Nat.card Z) (Bs.VL.trans Bs.LN) Bs.Vc
        hNcomm Bs.Vsq Bs.ZN hrep.Nb_semi Bs.Vcard Bs.Ncard
      Nb_pgroup := Bs.N2
      semilinear := hrep.semilinear
      two_elements := hrep.two_elements
      CL := hrep.CL
      Tt_range := hTtR
      Tt_rank := hTtrank
      Nb_fixes := hTtN
      Rb_fix_Nb := hTtR'
      quad := hrep.quad
      pair_dim := hrep.pair_dim
      image_dim := hrep.image_dim
      no_isotropic := hrep.no_isotropic
      transvection := hrep.transvection }

end CFSG.RankThree.GF2n.Stroth80

