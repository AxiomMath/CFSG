module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrBase

public section

namespace CFSG.Quasithin

namespace X1512

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_comm {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with h | h
    · exact ⟨y, h, 1, B.one_mem, mul_one y⟩
    · exact ⟨1, A.one_mem, y, h, one_mul y⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have h := hc a₂ ha₂ b₁ hb₁
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [h]
      _ = a₁ * b₁ * (a₂ * b₂) := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)

theorem card_sup_mul_card_inf [Finite G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let μ : ↥A × ↥B →* G := A.subtype.noncommCoprod B.subtype fun a b => hc a a.2 b b.2
  have hμ : ∀ p : ↥A × ↥B, μ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hr : μ.range = A ⊔ B := by
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨p, rfl⟩
      rw [hμ]
      exact Subgroup.mul_mem_sup p.1.2 p.2.2
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm hc hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hrel : ∀ p : μ.ker, ((p : ↥A × ↥B).1 : G) = ((p : ↥A × ↥B).2 : G)⁻¹ := fun p => by
    have h := p.2
    rw [MonoidHom.mem_ker, hμ] at h
    exact eq_inv_of_mul_eq_one_left h
  let φ : μ.ker → ↥(A ⊓ B) := fun p =>
    ⟨((p : ↥A × ↥B).1 : G), (p : ↥A × ↥B).1.2, by
      rw [hrel p]
      exact B.inv_mem (p : ↥A × ↥B).2.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun p q h => ?_, fun z => ?_⟩
    · have h1 : ((p : ↥A × ↥B).1 : G) = ((q : ↥A × ↥B).1 : G) :=
        congrArg (fun z : ↥(A ⊓ B) => (z : G)) h
      have h2 : ((p : ↥A × ↥B).2 : G) = ((q : ↥A × ↥B).2 : G) := by
        rw [← inv_inv ((p : ↥A × ↥B).2 : G), ← inv_inv ((q : ↥A × ↥B).2 : G), ← hrel p,
          ← hrel q, h1]
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    · refine ⟨⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, B.inv_mem z.2.2⟩), ?_⟩, Subtype.ext rfl⟩
      rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
  have h1 := Subgroup.card_ker_mul_card_range μ
  rw [Nat.card_prod, Nat.card_eq_of_bijective φ hφ, hr] at h1
  rw [mul_comm]
  exact h1

namespace WrStep

variable {H U L N K F₁ F₂ X₁ X₂ : Subgroup G}

theorem L_le_N (P : WrStep H U L N K F₁ F₂ X₁ X₂) : L ≤ N := P.L_le₁.trans P.X₁_le

theorem X_comm (P : WrStep H U L N K F₁ F₂ X₁ X₂) :
    ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x := fun x hx y hy =>
  P.N_abelian x (P.X₁_le hx) y (P.X₂_le hy)

theorem comm_mem_L_of_mul (P : WrStep H U L N K F₁ F₂ X₁ X₂) {f x₁ x₂ : G} (hf : f ∈ K)
    (hx₁ : x₁ ∈ X₁) (hx₂ : x₂ ∈ X₂) (h : f * (x₁ * x₂) * f⁻¹ * (x₁ * x₂)⁻¹ ∈ L) :
    f * x₁ * f⁻¹ * x₁⁻¹ ∈ L ∧ f * x₂ * f⁻¹ * x₂⁻¹ ∈ L := by
  rw [P.conj_comm_mul (P.K_le hf) (P.X₁_le hx₁) (P.X₂_le hx₂)] at h
  have h₁ : f * x₁ * f⁻¹ * x₁⁻¹ ∈ X₁ := X₁.mul_mem (P.K_norm₁ f hf x₁ hx₁) (X₁.inv_mem hx₁)
  have h₂ : f * x₂ * f⁻¹ * x₂⁻¹ ∈ X₂ := X₂.mul_mem (P.K_norm₂ f hf x₂ hx₂) (X₂.inv_mem hx₂)
  have h₁L : f * x₁ * f⁻¹ * x₁⁻¹ ∈ L := by
    have e : f * x₁ * f⁻¹ * x₁⁻¹ =
        (f * x₁ * f⁻¹ * x₁⁻¹ * (f * x₂ * f⁻¹ * x₂⁻¹)) * (f * x₂ * f⁻¹ * x₂⁻¹)⁻¹ := by group
    have h₁₂ : f * x₁ * f⁻¹ * x₁⁻¹ ∈ X₂ := by
      rw [e]
      exact X₂.mul_mem (P.L_le₂ h) (X₂.inv_mem h₂)
    rw [← P.inf_eq]
    exact ⟨h₁, h₁₂⟩
  refine ⟨h₁L, ?_⟩
  have e : f * x₂ * f⁻¹ * x₂⁻¹ =
      (f * x₁ * f⁻¹ * x₁⁻¹)⁻¹ * (f * x₁ * f⁻¹ * x₁⁻¹ * (f * x₂ * f⁻¹ * x₂⁻¹)) := by group
  rw [e]
  exact L.mul_mem (L.inv_mem h₁L) h

theorem fixSecIn_eq_sup (P : WrStep H U L N K F₁ F₂ X₁ X₂) {A : Subgroup G} (hAK : A ≤ K) :
    fixSecIn A L N = fixSecIn A L X₁ ⊔ fixSecIn A L X₂ := by
  have hN : (L.subgroupOf N).Normal := P.normal_sub (Y := N) le_rfl
  have h₁ : (L.subgroupOf X₁).Normal := P.normal_sub (Y := X₁) P.X₁_le
  have h₂ : (L.subgroupOf X₂).Normal := P.normal_sub (Y := X₂) P.X₂_le
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
  · obtain ⟨hxN, hx'⟩ := (mem_fixSecIn P.L_le_N).1 hx
    rw [← P.sup_eq] at hxN
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_comm P.X_comm hxN
    refine Subgroup.mul_mem_sup ((mem_fixSecIn P.L_le₁).2 ⟨hx₁, fun a ha => ?_⟩)
      ((mem_fixSecIn P.L_le₂).2 ⟨hx₂, fun a ha => ?_⟩)
    · exact (P.comm_mem_L_of_mul (hAK ha) hx₁ hx₂ (hx' a ha)).1
    · exact (P.comm_mem_L_of_mul (hAK ha) hx₁ hx₂ (hx' a ha)).2
  · exact Subgroup.closure_mono fun x hx => ⟨P.X₁_le hx.1, hx.2⟩
  · exact Subgroup.closure_mono fun x hx => ⟨P.X₂_le hx.1, hx.2⟩

theorem relIndex_fixSecIn [Finite G] (P : WrStep H U L N K F₁ F₂ X₁ X₂) {A : Subgroup G}
    (hAK : A ≤ K) :
    (fixSecIn A L N).relIndex N =
      (fixSecIn A L X₁).relIndex X₁ * (fixSecIn A L X₂).relIndex X₂ := by
  have hN : (L.subgroupOf N).Normal := P.normal_sub (Y := N) le_rfl
  have h₁ : (L.subgroupOf X₁).Normal := P.normal_sub (Y := X₁) P.X₁_le
  have h₂ : (L.subgroupOf X₂).Normal := P.normal_sub (Y := X₂) P.X₂_le
  have hFN : fixSecIn A L N ≤ N := fun x hx => ((mem_fixSecIn P.L_le_N).1 hx).1
  have hF₁ : fixSecIn A L X₁ ≤ X₁ := fun x hx => ((mem_fixSecIn P.L_le₁).1 hx).1
  have hF₂ : fixSecIn A L X₂ ≤ X₂ := fun x hx => ((mem_fixSecIn P.L_le₂).1 hx).1
  have hLF₁ : L ≤ fixSecIn A L X₁ := fun l hl =>
    (mem_fixSecIn P.L_le₁).2
      ⟨P.L_le₁ hl, fun a ha => L.mul_mem (P.K_norm_L a (hAK ha) l hl) (L.inv_mem hl)⟩
  have hLF₂ : L ≤ fixSecIn A L X₂ := fun l hl =>
    (mem_fixSecIn P.L_le₂).2
      ⟨P.L_le₂ hl, fun a ha => L.mul_mem (P.K_norm_L a (hAK ha) l hl) (L.inv_mem hl)⟩
  have hinf : fixSecIn A L X₁ ⊓ fixSecIn A L X₂ = L := by
    refine le_antisymm (fun x hx => ?_) (le_inf hLF₁ hLF₂)
    rw [← P.inf_eq]
    exact ⟨hF₁ hx.1, hF₂ hx.2⟩
  have hXcard := card_sup_mul_card_inf P.X_comm
  rw [P.sup_eq, P.inf_eq] at hXcard
  have hFcard := card_sup_mul_card_inf
    (A := fixSecIn A L X₁) (B := fixSecIn A L X₂) fun x hx y hy => P.X_comm x (hF₁ hx) y (hF₂ hy)
  rw [← P.fixSecIn_eq_sup hAK, hinf] at hFcard
  have r := Subgroup.relIndex_mul_card (fixSecIn A L N) N
  have r₁ := Subgroup.relIndex_mul_card (fixSecIn A L X₁) X₁
  have r₂ := Subgroup.relIndex_mul_card (fixSecIn A L X₂) X₂
  rw [inf_of_le_left hFN] at r
  rw [inf_of_le_left hF₁] at r₁
  rw [inf_of_le_left hF₂] at r₂
  have hpos : 0 < Nat.card ↥(fixSecIn A L N) * Nat.card ↥L :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc (fixSecIn A L N).relIndex N * (Nat.card ↥(fixSecIn A L N) * Nat.card ↥L)
      = ((fixSecIn A L N).relIndex N * Nat.card ↥(fixSecIn A L N)) * Nat.card ↥L := by ring
    _ = Nat.card ↥N * Nat.card ↥L := by rw [r]
    _ = Nat.card ↥X₁ * Nat.card ↥X₂ := hXcard
    _ = ((fixSecIn A L X₁).relIndex X₁ * Nat.card ↥(fixSecIn A L X₁)) *
          ((fixSecIn A L X₂).relIndex X₂ * Nat.card ↥(fixSecIn A L X₂)) := by rw [r₁, r₂]
    _ = (fixSecIn A L X₁).relIndex X₁ * (fixSecIn A L X₂).relIndex X₂ *
          (Nat.card ↥(fixSecIn A L X₁) * Nat.card ↥(fixSecIn A L X₂)) := by ring
    _ = (fixSecIn A L X₁).relIndex X₁ * (fixSecIn A L X₂).relIndex X₂ *
          (Nat.card ↥(fixSecIn A L N) * Nat.card ↥L) := by rw [hFcard]

end WrStep

end X1512

end CFSG.Quasithin
