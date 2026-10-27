module

public import CFSG.RankThree.S4Free.Stellmacher33Module
import CFSG.RankThree.S4Free.StellmacherL24

public section

namespace CFSG.RankThree.S4Free.Stell33

open Subgroup CFSG.Quasithin
open scoped commutatorElement Pointwise

section Index

variable {G : Type*} [Group G]

theorem relIndex_sup_le_mul [Finite G] {A B N : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (hN : A ⊔ B ≤ normalizer (N : Set G)) :
    N.relIndex (A ⊔ B) ≤ N.relIndex A * N.relIndex B := by
  haveI hNn : (N.subgroupOf (A ⊔ B)).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (hN g.2) n).mp hn⟩
  set f := QuotientGroup.mk' (N.subgroupOf (A ⊔ B)) with hf
  have hcA : Nat.card ((A.subgroupOf (A ⊔ B)).map f) = N.relIndex A := by
    rw [← relIndex_ker, hf, QuotientGroup.ker_mk', relIndex_subgroupOf le_sup_left]
  have hcB : Nat.card ((B.subgroupOf (A ⊔ B)).map f) = N.relIndex B := by
    rw [← relIndex_ker, hf, QuotientGroup.ker_mk', relIndex_subgroupOf le_sup_right]
  have htop : (A.subgroupOf (A ⊔ B)).map f ⊔ (B.subgroupOf (A ⊔ B)).map f = ⊤ := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self,
      ← MonoidHom.range_eq_map, hf, QuotientGroup.range_mk']
  have hnorm : (A.subgroupOf (A ⊔ B)).map f ≤
      normalizer (((B.subgroupOf (A ⊔ B)).map f : Subgroup _) : Set _) := by
    refine le_normalizer_of_forall_conj_mem (fun g hg x hx => ?_)
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    change (a : G) ∈ A at ha
    change (b : G) ∈ B at hb
    change (a : G) * b * (a : G)⁻¹ ∈ B
    exact (mem_normalizer_iff.mp (hAB ha) b).mp hb
  calc N.relIndex (A ⊔ B) = Nat.card (↥(A ⊔ B) ⧸ N.subgroupOf (A ⊔ B)) := rfl
    _ = Nat.card ↥((A.subgroupOf (A ⊔ B)).map f ⊔ (B.subgroupOf (A ⊔ B)).map f) := by
      rw [htop, card_top]
    _ = Nat.card ↥(((A.subgroupOf (A ⊔ B)).map f : Set (↥(A ⊔ B) ⧸ N.subgroupOf (A ⊔ B))) *
          ((B.subgroupOf (A ⊔ B)).map f : Set (↥(A ⊔ B) ⧸ N.subgroupOf (A ⊔ B)))) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm]
      rfl
    _ ≤ _ := Set.natCard_mul_le
    _ = N.relIndex A * N.relIndex B := by rw [← hcA, ← hcB]; rfl

end Index

section Transport

variable {H K : Type*} [Group H] [Group K] {Y : Subgroup H} (θ : Y →* K)

abbrev img (Z : Subgroup H) : Subgroup K := (Z.subgroupOf Y).map θ

abbrev pre (C : Subgroup K) : Subgroup H := (C.comap θ).map Y.subtype

theorem mem_pre {C : Subgroup K} {x : H} (hY : x ∈ Y) : x ∈ pre θ C ↔ θ ⟨x, hY⟩ ∈ C := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hc
    exact ⟨⟨x, hY⟩, hc, rfl⟩

theorem pre_le (C : Subgroup K) : pre θ C ≤ Y := map_subtype_le _

theorem mem_img_of_mem {Z : Subgroup H} {x : H} (hY : x ∈ Y) (hZ : x ∈ Z) :
    θ ⟨x, hY⟩ ∈ img θ Z :=
  ⟨⟨x, hY⟩, hZ, rfl⟩

theorem mem_of_mem_img (hθ : Function.Injective θ) {Z : Subgroup H} {y : Y}
    (h : θ y ∈ img θ Z) : (y : H) ∈ Z := by
  obtain ⟨y', hy', hθy'⟩ := h
  rw [← hθ hθy']
  exact hy'

theorem img_mono {Z₁ Z₂ : Subgroup H} (hZ : Z₁ ≤ Z₂) : img θ Z₁ ≤ img θ Z₂ :=
  map_mono fun _ hy => hZ hy

theorem relIndex_img_img (hθ : Function.Injective θ) {Z₁ Z₂ : Subgroup H} (hZ₂ : Z₂ ≤ Y) :
    (img θ Z₁).relIndex (img θ Z₂) = Z₁.relIndex Z₂ := by
  rw [relIndex_map_map_of_injective _ _ hθ, relIndex_subgroupOf hZ₂]

theorem relIndex_img {C : Subgroup K} {Z : Subgroup H} (hZ : Z ≤ Y) :
    C.relIndex (img θ Z) = (pre θ C).relIndex Z := by
  rw [← relIndex_comap, ← relIndex_map_map_of_injective _ _ Y.subtype_injective,
    subgroupOf_map_subtype, inf_of_le_left hZ]

theorem img_pre {C : Subgroup K} (hC : C ≤ θ.range) : img θ (pre θ C) = C := by
  rw [img, pre, subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective, map_comap_eq,
    inf_of_le_right hC]

theorem comm_mem_pre {C₁ C₂ C₃ : Subgroup K} (hC : ⁅C₁, C₂⁆ ≤ C₃) {x y : H}
    (hx : x ∈ pre θ C₁) (hy : y ∈ pre θ C₂) : x * y * x⁻¹ * y⁻¹ ∈ pre θ C₃ := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨x' * y' * x'⁻¹ * y'⁻¹, ?_, by simp⟩
  change θ (x' * y' * x'⁻¹ * y'⁻¹) ∈ C₃
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hC (commutator_mem_commutator hx' hy')

theorem conj_mem_pre {C : Subgroup K} [C.Normal] {g x : H} (hg : g ∈ Y) (hx : x ∈ pre θ C) :
    g * x * g⁻¹ ∈ pre θ C := by
  obtain ⟨x', hx', rfl⟩ := hx
  refine ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  change θ (⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹) ∈ C
  rw [map_mul, map_mul, map_inv]
  exact (inferInstance : C.Normal).conj_mem _ hx' _

end Transport

universe u

namespace LCfg

variable {H : Type*} [Group H] {L W P : Subgroup H} {u : H} (h : LCfg L W P u)

include h

theorem false_of_step_of_thmA [Finite H] (h3 : ¬ 3 ∣ Nat.card L) {𝒦 : HostClass}
    (hThmA : ThmA.{u} 𝒦) {K : Type u} [Group K] [Finite K] (hK : 𝒦.Holds K) (hS3 : IsSym3Free K)
    {T : Subgroup K} (hTsyl : ∃ Q : Sylow 2 K, (Q : Subgroup K) = T)
    (hM : ∀ N : Subgroup K, N.Normal → T ⊓ N ≤ oTwo K ∨ pResidual 2 K ≤ N)
    (θ : ↥(X W P u ⊔ W) →* K) (hθ : Function.Injective θ) (hθT : ∀ y, θ y ∈ T)
    (hθW : img θ W ≤ oTwo K)
    {V₀ : Subgroup K} [V₀.Normal] (hV₀W : V₀ ≤ img θ W)
    (hV : ⁅V₀, pResidual 2 K⁆ ≠ ⊥) (hV₀A : V₀ ≤ ⁅V₀, pResidual 2 K⁆ ⊔ img θ (A W P))
    (hV₀X : ¬ V₀ ≤ img θ (X W P u))
    {U₀ : Subgroup K} (hU₀ : V₀ ≤ normalClosure (U₀ : Set K))
    (hstep : ∀ k : K, (∀ y, k * θ y * k⁻¹ ∈ T) → ∀ t ∈ U₀, k⁻¹ * t * k ∈ img θ (X W P u)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (pResidual 2 K).Normal := normal_pResidual 2 K
  obtain ⟨VK, hVK⟩ : ∃ VK, ⁅V₀, pResidual 2 K⁆ = VK := ⟨_, rfl⟩
  obtain ⟨V₁K, hV₁K⟩ : ∃ V₁K, ⁅VK, oTwo K⁆ = V₁K := ⟨_, rfl⟩
  haveI hVKn : VK.Normal := hVK ▸ inferInstance
  haveI hV₁Kn : V₁K.Normal := hV₁K ▸ inferInstance
  rw [hVK] at hV hV₀A
  obtain ⟨Tsyl, hTsyl⟩ := hTsyl
  have hOT : oTwo K ≤ T := hTsyl ▸ (Stell.oTwo_isPGroup K).le_sylow_of_normal Tsyl
  have hXY : X W P u ≤ X W P u ⊔ W := le_sup_left
  have hWY : W ≤ X W P u ⊔ W := le_sup_right
  have hAY : A W P ≤ X W P u ⊔ W := h.A_le_X.trans hXY
  have hBY : B W P u ≤ X W P u ⊔ W := h.B_le_X.trans hXY
  have hrange : img θ W ≤ θ.range := map_le_range _ _
  have hVKV₀ : VK ≤ V₀ := hVK ▸ commutator_le_left _ _
  have hVKW : VK ≤ img θ W := hVKV₀.trans hV₀W
  have hVhW : pre θ VK ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_of_mem_img θ hθ (hVKW hy)
  have hXVh : X W P u ≤ normalizer (pre θ VK : Set H) :=
    le_normalizer_of_forall_conj_mem (fun g hg x hx => conj_mem_pre θ (hXY hg) hx)
  have hVhX : ¬ pre θ VK ≤ X W P u := by
    intro hle
    apply hV₀X
    refine hV₀A.trans (sup_le ?_ (img_mono θ h.A_le_X))
    intro k hk
    obtain ⟨y, hyW, rfl⟩ := hVKW hk
    exact ⟨y, hle ((mem_pre θ y.2).mpr hk), rfl⟩
  have hA1 := h.A_le_sup_of_not_le hVhW hXVh hVhX
  have hidxA : (A W P).relIndex (pre θ VK) ≤ 2 := by
    calc (A W P).relIndex (pre θ VK) ≤ (A W P).relIndex W :=
          relIndex_le_of_le_right hVhW (Stell.relIndex_ne_zero_of_finite _ _)
      _ = 2 := h.relIndex_eq
  have hDn : D W P u ≤ normalizer ((pre θ VK ⊓ A W P : Subgroup H) : Set H) := by
    refine le_normalizer_of_forall_conj_mem (fun d hd z hz => ?_)
    have hzL : z ∈ L := h.X_le_L (h.A_le_X hz.2)
    rw [← h.comm_D hd hzL, mul_inv_cancel_right]
    exact hz
  have hcomm : ∀ x ∈ X W P u, ∀ b ∈ B W P u, b ∈ pre θ (oTwo K) →
      x * b * x⁻¹ * b⁻¹ ∈ pre θ V₁K := by
    intro x hx b hb hbO
    obtain ⟨a, ha, b', hb', rfl⟩ := h.mem_X_iff.mp hx
    have ha1 := hA1 ha
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hDn, Set.mem_mul] at ha1
    obtain ⟨a', ha', d, hd, rfl⟩ := ha1
    have hbL : b ∈ L := h.X_le_L (h.B_le_X hb)
    have h1 : b' * b = b * b' := h.comm_Wu hb'.1 hb.1
    have h2 : b * d = d * b := h.comm_D hd hbL
    have e : a' * d * b' * b * (a' * d * b')⁻¹ * b⁻¹ = a' * b * a'⁻¹ * b⁻¹ := by
      calc a' * d * b' * b * (a' * d * b')⁻¹ * b⁻¹
          = a' * d * (b' * b) * b'⁻¹ * d⁻¹ * a'⁻¹ * b⁻¹ := by group
        _ = a' * d * (b * b') * b'⁻¹ * d⁻¹ * a'⁻¹ * b⁻¹ := by rw [h1]
        _ = a' * (b * d) * d⁻¹ * a'⁻¹ * b⁻¹ := by rw [h2]; group
        _ = a' * b * a'⁻¹ * b⁻¹ := by group
    rw [e]
    exact comm_mem_pre θ hV₁K.le ha'.1 hbO
  let X₁ : Subgroup H :=
    { carrier := {y | y ∈ X W P u ∧ ∀ x ∈ X W P u, x * y * x⁻¹ * y⁻¹ ∈ pre θ V₁K}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
        refine ⟨mul_mem h₁ h₂, fun x hx => ?_⟩
        have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
            (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e]
        exact mul_mem (k₁ x hx) (conj_mem_pre θ (hXY h₁) (k₂ x hx))
      inv_mem' := by
        rintro y ⟨h₁, k₁⟩
        refine ⟨inv_mem h₁, fun x hx => ?_⟩
        have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact conj_mem_pre θ (hXY (inv_mem h₁)) (inv_mem (k₁ x hx)) }
  have hmemX₁ : ∀ y, y ∈ X₁ ↔ y ∈ X W P u ∧ ∀ x ∈ X W P u, x * y * x⁻¹ * y⁻¹ ∈ pre θ V₁K :=
    fun _ => Iff.rfl
  have hX₁X : X₁ ≤ X W P u := fun y hy => ((hmemX₁ y).mp hy).1
  have hX₁L : L ≤ normalizer (X₁ : Set H) := by
    refine le_normalizer_of_forall_conj_mem (fun g hg y hy => ?_)
    rw [hmemX₁] at hy ⊢
    refine ⟨(mem_normalizer_iff.mp (h.L_le_normalizer_X hg) y).mp hy.1, fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ X W P u := by
      have := (mem_normalizer_iff.mp (h.L_le_normalizer_X (inv_mem hg)) x).mp hx
      rwa [inv_inv] at this
    have hD := h.comm_X_mem_D hx' hy.1
    have e : x * (g * y * g⁻¹) * x⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * ((g⁻¹ * x * g) * y * (g⁻¹ * x * g)⁻¹ * y⁻¹) * g⁻¹ := by group
    rw [e, h.conj_D hD hg]
    exact hy.2 _ hx'
  have hDX₁ : D W P u ≤ X₁ := by
    intro d hd
    refine ⟨(h.D_le_A.trans h.A_le_X) hd, fun x hx => ?_⟩
    rw [h.comm_D hd (h.X_le_L hx), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hBQX₁ : B W P u ⊓ pre θ (oTwo K) ≤ X₁ := fun y hy =>
    ⟨h.B_le_X hy.1, fun x hx => hcomm x hx y hy.1 hy.2⟩
  have hV₀T : V₀ ≤ T := by
    intro k hk
    obtain ⟨y, -, rfl⟩ := hV₀W hk
    exact hθT y
  have hWc : ∀ k₁ ∈ img θ W, ∀ k₂ ∈ img θ W, k₁ * k₂ = k₂ * k₁ := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (h.comm_W (mem_subgroupOf.mp hy₁) (mem_subgroupOf.mp hy₂)))
  have hW2 : ∀ k ∈ img θ W, k * k = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (h.mul_self_eq_one (mem_subgroupOf.mp hy))
    rw [this, map_one]
  have hV₀c : ∀ x ∈ V₀, ∀ y ∈ V₀, x * y = y * x := fun x hx y hy =>
    hWc x (hV₀W hx) y (hV₀W hy)
  have hV₀2 : ∀ x ∈ V₀, x * x = 1 := fun x hx => hW2 x (hV₀W hx)
  have hθD : ∀ y : ↥(X W P u ⊔ W), (y : H) ∈ D W P u → θ y ∈ oTwo K := fun y hy =>
    hθW (mem_img_of_mem θ y.2 ((h.D_le_A.trans h.A_le_W) hy))
  have hTA : ∀ E : Subgroup K, E ≤ T → (∀ e ∈ E, e * e ∈ oTwo K) →
      (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈ oTwo K) →
      ((oTwo K).relIndex E) ^ 2 ≤ (centMod VK V₁K E).relIndex VK := fun E hET hE2 hEc =>
    sq_relIndex_le_of_thmA hThmA hK hS3 ⟨Tsyl, hTsyl⟩ hM (V₀ := V₀) (V := VK) (V₁ := V₁K) hV₀T
      hV₀c hV₀2 hVK hV₁K hV hET hE2 hEc
  have himgT : ∀ Z : Subgroup H, img θ Z ≤ T := by
    rintro Z _ ⟨y, -, rfl⟩
    exact hθT y
  have hVKimg : img θ (pre θ VK) = VK := img_pre θ (hVKW.trans hrange)
  have hne : ∀ C : Subgroup K, C.relIndex VK ≠ 0 := fun C =>
    Stell.relIndex_ne_zero_of_finite C VK
  have hX₁O : X₁ ≤ pre θ (oTwo K) := by
    have hE2 : ∀ e ∈ img θ X₁, e * e ∈ oTwo K := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul]
      exact hθD _ (h.sq_X_mem_D (hX₁X (mem_subgroupOf.mp hy)))
    have hEc : ∀ e₁ ∈ img θ X₁, ∀ e₂ ∈ img θ X₁, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈ oTwo K := by
      rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact hθD _ (h.comm_X_mem_D (hX₁X (mem_subgroupOf.mp hy₁))
        (hX₁X (mem_subgroupOf.mp hy₂)))
    have h1 := hTA _ (himgT X₁) hE2 hEc
    have hle : img θ (pre θ VK ⊓ A W P) ≤ centMod VK V₁K (img θ X₁) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' := mem_subgroupOf.mp hy
      refine mem_centMod.mpr ⟨(mem_pre θ y.2).mp hy'.1, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      have h2 := ((hmemX₁ z).mp (mem_subgroupOf.mp hz)).2 y (h.A_le_X hy'.2)
      have e : (z : H) * y * (z : H)⁻¹ * (y : H)⁻¹ =
          ((y : H) * z * (y : H)⁻¹ * (z : H)⁻¹)⁻¹ := by group
      have h3 : (z : H) * y * (z : H)⁻¹ * (y : H)⁻¹ ∈ pre θ V₁K := by
        rw [e]
        exact inv_mem h2
      exact (mem_pre θ (z * y * z⁻¹ * y⁻¹).2).mp h3
    have h2 : (centMod VK V₁K (img θ X₁)).relIndex VK ≤ 2 := by
      have h3 := relIndex_img_img θ hθ (Z₁ := pre θ VK ⊓ A W P) (pre_le θ VK)
      rw [hVKimg] at h3
      calc (centMod VK V₁K (img θ X₁)).relIndex VK
          ≤ (img θ (pre θ VK ⊓ A W P)).relIndex VK := relIndex_le_of_le_left hle (hne _)
        _ = (pre θ VK ⊓ A W P).relIndex (pre θ VK) := h3
        _ = (A W P).relIndex (pre θ VK) := by
          rw [inf_comm (pre θ VK) (A W P), inf_relIndex_right]
        _ ≤ 2 := hidxA
    have h4 : (oTwo K).relIndex (img θ X₁) ≤ 1 := by nlinarith
    have h5 : img θ X₁ ≤ oTwo K := by
      have h6 := Stell.relIndex_ne_zero_of_finite (oTwo K) (img θ X₁)
      exact relIndex_eq_one.mp (by omega)
    intro y hy
    exact (mem_pre θ (hXY (hX₁X hy))).mpr (h5 ⟨⟨y, hXY (hX₁X hy)⟩, hy, rfl⟩)
  have hBX₁ : B W P u ⊓ X₁ = B W P u ⊓ pre θ (oTwo K) :=
    le_antisymm (inf_le_inf_left _ hX₁O) (le_inf inf_le_left hBQX₁)
  have hb_eq : X₁.relIndex (B W P u) = (pre θ (oTwo K)).relIndex (B W P u) := by
    rw [← inf_relIndex_right (H := X₁), inf_comm X₁ (B W P u), hBX₁,
      inf_comm (B W P u) (pre θ (oTwo K)), inf_relIndex_right]
  have hAB : X₁.relIndex (A W P) = X₁.relIndex (B W P u) := by
    have hu : u ∈ normalizer (X₁ : Set H) := hX₁L h.u_mem
    calc X₁.relIndex (A W P)
        = (X₁.map (MulAut.conj u).toMonoidHom).relIndex
            ((A W P).map (MulAut.conj u).toMonoidHom) :=
          (relIndex_map_map_of_injective _ _ (MulAut.conj u).injective).symm
      _ = X₁.relIndex (B W P u) := by rw [map_conj_eq_of_mem_normalizer hu, h.map_conj_A]
  have hb2 : X₁.relIndex (B W P u) ≤ 2 := by
    have hE2 : ∀ e ∈ img θ (B W P u), e * e ∈ oTwo K := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul]
      have : y * y = 1 := Subtype.ext (by
        change (y : H) * y = 1
        rw [← sq]
        exact h.elemAb_Wu.2 _ (mem_subgroupOf.mp hy).1)
      rw [this, map_one]
      exact one_mem _
    have hEc : ∀ e₁ ∈ img θ (B W P u), ∀ e₂ ∈ img θ (B W P u),
        e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈ oTwo K := by
      rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      have : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = 1 := Subtype.ext (by
        change (y₁ : H) * y₂ * (y₁ : H)⁻¹ * (y₂ : H)⁻¹ = 1
        rw [h.comm_Wu (mem_subgroupOf.mp hy₁).1 (mem_subgroupOf.mp hy₂).1]
        group)
      rw [this, map_one]
      exact one_mem _
    have h1 := hTA _ (himgT _) hE2 hEc
    rw [relIndex_img θ hBY, ← hb_eq] at h1
    have hle : img θ (pre θ VK ⊓ X₁) ≤ centMod VK V₁K (img θ (B W P u)) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' := mem_subgroupOf.mp hy
      refine mem_centMod.mpr ⟨(mem_pre θ y.2).mp hy'.1, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact (mem_pre θ (z * y * z⁻¹ * y⁻¹).2).mp
        (((hmemX₁ y).mp hy'.2).2 z (h.B_le_X (mem_subgroupOf.mp hz)))
    have hinf : X₁ ⊓ pre θ VK ≤ A W P := fun y hy =>
      ⟨hVhW hy.2, h.X_le_P (hX₁X hy.1)⟩
    have e1 := relIndex_inf_mul_relIndex X₁ (A W P) (pre θ VK)
    have e2 : (X₁ ⊓ A W P).relIndex (pre θ VK) = X₁.relIndex (pre θ VK) := by
      have e4 : X₁ ⊓ A W P ⊓ pre θ VK = X₁ ⊓ pre θ VK :=
        le_antisymm (inf_le_inf_right _ inf_le_left)
          (le_inf (le_inf inf_le_left hinf) inf_le_right)
      rw [← inf_relIndex_right (H := X₁ ⊓ A W P), e4, inf_relIndex_right]
    have e3 : X₁.relIndex (A W P ⊓ pre θ VK) ≤ X₁.relIndex (A W P) :=
      relIndex_le_of_le_right inf_le_left (Stell.relIndex_ne_zero_of_finite _ _)
    have h2 : (centMod VK V₁K (img θ (B W P u))).relIndex VK ≤
        2 * X₁.relIndex (B W P u) := by
      have h3 := relIndex_img_img θ hθ (Z₁ := pre θ VK ⊓ X₁) (pre_le θ VK)
      rw [hVKimg] at h3
      calc (centMod VK V₁K (img θ (B W P u))).relIndex VK
          ≤ (img θ (pre θ VK ⊓ X₁)).relIndex VK := relIndex_le_of_le_left hle (hne _)
        _ = (pre θ VK ⊓ X₁).relIndex (pre θ VK) := h3
        _ = X₁.relIndex (pre θ VK) := by rw [inf_comm (pre θ VK) X₁, inf_relIndex_right]
        _ = X₁.relIndex (A W P ⊓ pre θ VK) * (A W P).relIndex (pre θ VK) := by rw [← e2, e1]
        _ ≤ 2 * X₁.relIndex (B W P u) := by
          rw [← hAB]
          nlinarith [e3, hidxA, Nat.zero_le (X₁.relIndex (A W P ⊓ pre θ VK))]
    nlinarith
  have hidx4 : X₁.relIndex (X W P u) ≤ 4 := by
    calc X₁.relIndex (X W P u) ≤ X₁.relIndex (A W P) * X₁.relIndex (B W P u) :=
          relIndex_sup_le_mul h.A_le_normalizer_B (h.X_le_L.trans hX₁L)
      _ ≤ 2 * 2 := Nat.mul_le_mul (hAB ▸ hb2) hb2
  have hXX₁ := h.X_le_of_relIndex_le_four hX₁L hDX₁ hidx4 h3
  have hYO : X W P u ⊔ W ≤ pre θ (oTwo K) :=
    sup_le (hXX₁.trans hX₁O) (fun w hw => (mem_pre θ (hWY hw)).mpr
      (hθW (mem_img_of_mem θ (hWY hw) hw)))
  have hθO : ∀ y, θ y ∈ oTwo K := fun y => (mem_pre θ y.2).mp (hYO y.2)
  obtain ⟨z, t, ht, hzt⟩ : ∃ z : K, ∃ t ∈ U₀, z * t * z⁻¹ ∉ img θ (X W P u) := by
    by_contra hall
    push Not at hall
    apply hV₀X
    refine hU₀.trans ?_
    rw [normalClosure, closure_le]
    intro x hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    exact hall c a ha
  apply hzt
  have := hstep z⁻¹ (fun y => hOT ((inferInstance : (oTwo K).Normal).conj_mem _ (hθO y) z⁻¹))
    t ht
  rwa [inv_inv] at this

end LCfg

end CFSG.RankThree.S4Free.Stell33
