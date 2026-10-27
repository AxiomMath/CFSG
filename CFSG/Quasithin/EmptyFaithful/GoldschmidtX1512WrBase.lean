module

public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace X1512

variable {G : Type} [Group G]

theorem le_normalizer_of_forall {F X : Subgroup G} (h : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ ∈ X) :
    F ≤ Subgroup.normalizer (X : Set G) := fun g hg =>
  Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => h g hg x hx, fun hx => by
    have h1 := h g⁻¹ (F.inv_mem hg) _ hx
    rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1⟩

theorem conj_mem_of_normal {L X : Subgroup G} [hN : (L.subgroupOf X).Normal] (hLX : L ≤ X) {x l : G}
    (hx : x ∈ X) (hl : l ∈ L) : x * l * x⁻¹ ∈ L := by
  have := hN.conj_mem ⟨l, hLX hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem mem_fixSecIn {A L N : Subgroup G} [(L.subgroupOf N).Normal] (hLN : L ≤ N) {x : G} :
    x ∈ fixSecIn A L N ↔ x ∈ N ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨N.one_mem, fun a _ => by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨N.mul_mem hx.1 hy.1, fun a ha => ?_⟩
      have e : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
          (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e]
      exact L.mul_mem (hx.2 a ha) (conj_mem_of_normal hLN hx.1 (hy.2 a ha))
    | inv x _ hx =>
      refine ⟨N.inv_mem hx.1, fun a ha => ?_⟩
      have e : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by group
      rw [e]
      have := conj_mem_of_normal hLN (N.inv_mem hx.1) (L.inv_mem (hx.2 a ha))
      simpa using this
  · exact fun h => Subgroup.subset_closure h

theorem mem_cSecIn_of_normalizes {F L X : Subgroup G} (hFL : F ≤ Subgroup.normalizer (L : Set G))
    {f : G} (hf : f ∈ cSecIn F L X) : f ∈ F ∧ ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ L := by
  induction hf using Subgroup.closure_induction with
  | mem f hf => exact hf
  | one => exact ⟨F.one_mem, fun x _ => by simp⟩
  | mul f g _ _ hf hg =>
    refine ⟨F.mul_mem hf.1 hg.1, fun x hx => ?_⟩
    have e : f * g * x * (f * g)⁻¹ * x⁻¹ =
        (f * (g * x * g⁻¹ * x⁻¹) * f⁻¹) * (f * x * f⁻¹ * x⁻¹) := by group
    rw [e]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFL hf.1) _).mp (hg.2 x hx)) (hf.2 x hx)
  | inv f _ hf =>
    refine ⟨F.inv_mem hf.1, fun x hx => ?_⟩
    have e : f⁻¹ * x * f⁻¹⁻¹ * x⁻¹ = f⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * f⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hFL (F.inv_mem hf.1)) _).mp (L.inv_mem (hf.2 x hx))

theorem inf_cSecIn_eq {A H L N : Subgroup G} (hAH : A ≤ H)
    (hH : H ≤ Subgroup.normalizer (L : Set G)) : A ⊓ cSecIn H L N = cSecIn A L N := by
  ext a
  constructor
  · rintro ⟨haA, haC⟩
    exact Subgroup.subset_closure ⟨haA, (mem_cSecIn_of_normalizes hH haC).2⟩
  · intro ha
    have h := mem_cSecIn_of_normalizes (hAH.trans hH) ha
    exact ⟨h.1, Subgroup.subset_closure ⟨hAH h.1, h.2⟩⟩

section Quotient

variable {L X : Subgroup G} [(L.subgroupOf X).Normal]

theorem mk_eq_iff (hLX : L ≤ X) {y z : ↥X} :
    (QuotientGroup.mk y : ↥X ⧸ L.subgroupOf X) = QuotientGroup.mk z ↔
      (z : G) * (y : G)⁻¹ ∈ L := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h1 : (z : G) * (y : G)⁻¹ = (y : G) * ((y : G)⁻¹ * (z : G)) * (y : G)⁻¹ := by group
  constructor
  · intro h
    rw [h1]
    exact conj_mem_of_normal hLX y.2 (by simpa using h)
  · intro h
    have h2 : ((y : G)⁻¹ * (z : G)) = (y : G)⁻¹ * ((z : G) * (y : G)⁻¹) * ((y : G)⁻¹)⁻¹ := by
      group
    simpa [h2] using conj_mem_of_normal hLX (X.inv_mem y.2) h

end Quotient

structure WrStep (H U L N K F₁ F₂ X₁ X₂ : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 U
  step : IsChiefStep H U L N
  FFK : F₁ ⊔ F₂ = K
  K_idx : K.relIndex H = 2
  K_le : K ≤ H
  F₁_le : F₁ ≤ H
  F₂_le : F₂ ≤ H
  L_le₁ : L ≤ X₁
  X₁_le : X₁ ≤ N
  L_le₂ : L ≤ X₂
  X₂_le : X₂ ≤ N
  inf_eq : X₁ ⊓ X₂ = L
  sup_eq : X₁ ⊔ X₂ = N
  F₂_triv : ∀ f ∈ F₂, ∀ x ∈ X₁, f * x * f⁻¹ * x⁻¹ ∈ L
  F₁_triv : ∀ f ∈ F₁, ∀ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∈ L
  F₁_norm : ∀ f ∈ F₁, ∀ x ∈ X₁, f * x * f⁻¹ ∈ X₁
  F₂_norm : ∀ f ∈ F₂, ∀ x ∈ X₂, f * x * f⁻¹ ∈ X₂
  K_normal : ∀ σ ∈ H, ∀ b ∈ K, σ * b * σ⁻¹ ∈ K
  irr₁ : ∀ Y : Subgroup G, L ≤ Y → Y ≤ X₁ → (∀ f ∈ F₁, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) →
    Y = L ∨ Y = X₁
  irr₂ : ∀ Y : Subgroup G, L ≤ Y → Y ≤ X₂ → (∀ f ∈ F₂, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) →
    Y = L ∨ Y = X₂
  card_eq : Nat.card X₁ = Nat.card X₂
  L_ne₁ : L ≠ X₁
  L_ne₂ : L ≠ X₂
  nontriv₁ : ∃ f ∈ F₁, ∃ x ∈ X₁, f * x * f⁻¹ * x⁻¹ ∉ L
  nontriv₂ : ∃ f ∈ F₂, ∃ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∉ L

namespace WrStep

variable {H U L N K F₁ F₂ X₁ X₂ : Subgroup G} (P : WrStep H U L N K F₁ F₂ X₁ X₂)

include P

theorem H_norm_L : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := P.step.2.1.2

theorem H_norm_N : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := P.step.1.2

theorem F₁_le_K : F₁ ≤ K := P.FFK ▸ le_sup_left

theorem F₂_le_K : F₂ ≤ K := P.FFK ▸ le_sup_right

theorem N_abelian : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun _ ha _ hb =>
  B2F.isElemAbelian_comm P.elemAbelian (P.step.1.1 ha) (P.step.1.1 hb)

theorem F₂_norm₁ : ∀ f ∈ F₂, ∀ x ∈ X₁, f * x * f⁻¹ ∈ X₁ := fun f hf x hx => by
  have e : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact X₁.mul_mem (P.L_le₁ (P.F₂_triv f hf x hx)) hx

theorem F₁_norm₂ : ∀ f ∈ F₁, ∀ x ∈ X₂, f * x * f⁻¹ ∈ X₂ := fun f hf x hx => by
  have e : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact X₂.mul_mem (P.L_le₂ (P.F₁_triv f hf x hx)) hx

theorem K_norm₁ : ∀ b ∈ K, ∀ x ∈ X₁, b * x * b⁻¹ ∈ X₁ := by
  have : K ≤ Subgroup.normalizer (X₁ : Set G) := by
    rw [← P.FFK]
    exact sup_le (le_normalizer_of_forall P.F₁_norm) (le_normalizer_of_forall P.F₂_norm₁)
  exact fun b hb x hx => (Subgroup.mem_normalizer_iff.mp (this hb) x).mp hx

theorem K_norm₂ : ∀ b ∈ K, ∀ x ∈ X₂, b * x * b⁻¹ ∈ X₂ := by
  have : K ≤ Subgroup.normalizer (X₂ : Set G) := by
    rw [← P.FFK]
    exact sup_le (le_normalizer_of_forall P.F₁_norm₂) (le_normalizer_of_forall P.F₂_norm)
  exact fun b hb x hx => (Subgroup.mem_normalizer_iff.mp (this hb) x).mp hx

theorem K_norm_L : ∀ b ∈ K, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
  P.H_norm_L b (P.K_le hb) l hl

theorem conj_comm_mul {f a b : G} (hf : f ∈ H) (ha : a ∈ N) (hb : b ∈ N) :
    f * (a * b) * f⁻¹ * (a * b)⁻¹ = (f * a * f⁻¹ * a⁻¹) * (f * b * f⁻¹ * b⁻¹) := by
  have hq : f * b * f⁻¹ ∈ N := P.H_norm_N f hf b hb
  have hc : Commute (f * b * f⁻¹) a⁻¹ := P.N_abelian _ hq _ (N.inv_mem ha)
  have hab : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
    rw [mul_inv_rev]
    exact (P.N_abelian a⁻¹ (N.inv_mem ha) b⁻¹ (N.inv_mem hb)).symm
  have e : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
  rw [e, hab]
  exact hc.mul_mul_mul_comm (f * a * f⁻¹) b⁻¹

theorem normal_sub {Y : Subgroup G} (hYN : Y ≤ N) : (L.subgroupOf Y).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) = (n : G) * (g : G) := P.N_abelian _ (hYN g.2) _ (hYN n.2)
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ L
    rw [h1, mul_inv_cancel_right]
    exact hn⟩

theorem symm : WrStep H U L N K F₂ F₁ X₂ X₁ where
  elemAbelian := P.elemAbelian
  step := P.step
  FFK := by rw [sup_comm]; exact P.FFK
  K_idx := P.K_idx
  K_le := P.K_le
  F₁_le := P.F₂_le
  F₂_le := P.F₁_le
  L_le₁ := P.L_le₂
  X₁_le := P.X₂_le
  L_le₂ := P.L_le₁
  X₂_le := P.X₁_le
  inf_eq := by rw [inf_comm]; exact P.inf_eq
  sup_eq := by rw [sup_comm]; exact P.sup_eq
  F₂_triv := P.F₁_triv
  F₁_triv := P.F₂_triv
  F₁_norm := P.F₂_norm
  F₂_norm := P.F₁_norm
  K_normal := P.K_normal
  irr₁ := P.irr₂
  irr₂ := P.irr₁
  card_eq := P.card_eq.symm
  L_ne₁ := P.L_ne₂
  L_ne₂ := P.L_ne₁
  nontriv₁ := P.nontriv₂
  nontriv₂ := P.nontriv₁

end WrStep

end X1512

end CFSG.Quasithin
