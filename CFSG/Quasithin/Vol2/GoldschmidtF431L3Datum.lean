module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Base

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

structure Frame (S Q₁ Q₂ : Subgroup G) : Prop where
  Q₁_le : Q₁ ≤ S
  Q₂_le : Q₂ ≤ S
  Q₁_ea : IsElemAbelian 2 Q₁
  Q₂_ea : IsElemAbelian 2 Q₂
  inter : Q₁ ⊓ Q₂ = centerOf S
  card_eq : Nat.card Q₁ = Nat.card Q₂
  four_le : 4 ≤ Nat.card Q₁
  Q_ne : Q₁ ≠ Q₂
  comm : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ centerOf S
  inv : ∀ x ∈ S, x ^ 2 = 1 → x ≠ 1 → x ∈ Q₁ ∨ x ∈ Q₂
  cent₁ : ∀ x ∈ Q₁, x ∉ centerOf S → ∀ y ∈ S, y * x = x * y → y ∈ Q₁
  cent₂ : ∀ x ∈ Q₂, x ∉ centerOf S → ∀ y ∈ S, y * x = x * y → y ∈ Q₂
  maxea : ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A → Nat.card Q₁ ≤ Nat.card A →
    A = Q₁ ∨ A = Q₂

theorem Frame.conj {S Q₁ Q₂ : Subgroup G} (F : Frame S Q₁ Q₂) (g : G) :
    Frame (conjSub g S) (conjSub g Q₁) (conjSub g Q₂) := by
  have hc : ∀ x, x ∈ conjSub g (centerOf S) ↔ g⁻¹ * x * g ∈ centerOf S := fun x => mem_conjSub
  refine ⟨conjSub_mono g F.Q₁_le, conjSub_mono g F.Q₂_le, F7.isElemAbelian_conjSub F.Q₁_ea,
    F7.isElemAbelian_conjSub F.Q₂_ea, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← conjSub_inf, F.inter, centerOf_conjSub]
  · rw [card_conjSub, card_conjSub, F.card_eq]
  · rw [card_conjSub]; exact F.four_le
  · intro h
    apply F.Q_ne
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
  · intro x hx y hy
    rw [mem_conjSub] at hx hy
    rw [centerOf_conjSub, mem_conjSub]
    have := F.comm _ hx _ hy
    rwa [show g⁻¹ * (x * y * x⁻¹ * y⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ *
      (g⁻¹ * y * g)⁻¹ by group]
  · intro x hx hx2 hx1
    rw [mem_conjSub] at hx
    rw [mem_conjSub, mem_conjSub]
    exact F.inv _ hx (by rw [conj_sq, hx2]; group) (conj_ne_one' hx1)
  · intro x hx hxZ y hy hxy
    rw [mem_conjSub] at hx ⊢
    rw [centerOf_conjSub, hc] at hxZ
    rw [mem_conjSub] at hy
    exact F.cent₁ _ hx hxZ _ hy (conj_commute hxy.symm).symm
  · intro x hx hxZ y hy hxy
    rw [mem_conjSub] at hx ⊢
    rw [centerOf_conjSub, hc] at hxZ
    rw [mem_conjSub] at hy
    exact F.cent₂ _ hx hxZ _ hy (conj_commute hxy.symm).symm
  · intro A hA hAe hcard
    have hA' : conjSub g⁻¹ A ≤ S := (le_conjSub_iff g).mp hA
    have hAe' := F7.isElemAbelian_conjSub (g := g⁻¹) hAe
    have hcard' : Nat.card Q₁ ≤ Nat.card (conjSub g⁻¹ A) := by
      rw [card_conjSub]
      rwa [card_conjSub] at hcard
    rcases F.maxea _ hA' hAe' hcard' with h | h
    · left
      rw [← h, conjSub_inv_conjSub]
    · right
      rw [← h, conjSub_inv_conjSub]

theorem Frame.symm {S Q₁ Q₂ : Subgroup G} (F : Frame S Q₁ Q₂) : Frame S Q₂ Q₁ where
  Q₁_le := F.Q₂_le
  Q₂_le := F.Q₁_le
  Q₁_ea := F.Q₂_ea
  Q₂_ea := F.Q₁_ea
  inter := by rw [inf_comm]; exact F.inter
  card_eq := F.card_eq.symm
  four_le := by rw [← F.card_eq]; exact F.four_le
  Q_ne := fun h => F.Q_ne h.symm
  comm := F.comm
  inv := fun x hx hx2 hx1 => (F.inv x hx hx2 hx1).symm
  cent₁ := F.cent₂
  cent₂ := F.cent₁
  maxea := fun A hA hAe hc => by
    have := F.maxea A hA hAe (by rw [F.card_eq]; exact hc)
    exact this.symm

@[expose] def NormedBy (B K : Subgroup G) : Prop := ∀ b ∈ B, ∀ x ∈ K, b * x * b⁻¹ ∈ K

structure L3Datum (M₁ M₂ : Subgroup G) where
  S : Subgroup G
  B : Subgroup G
  Q₁ : Subgroup G
  Q₂ : Subgroup G
  s₁ : G
  s₂ : G
  S_eq : S = pCoreOf 2 (M₁ ⊓ M₂)
  B_le : B ≤ M₁ ⊓ M₂
  B_odd : Odd (Nat.card B)
  mul_SB : ∀ h ∈ M₁ ⊓ M₂, ∃ s ∈ S, ∃ b ∈ B, h = s * b
  S_index : ¬ 2 ∣ S.relIndex M₁
  frame : Frame S Q₁ Q₂
  Q₁_norm : ∀ m ∈ M₁, ∀ x ∈ Q₁, m * x * m⁻¹ ∈ Q₁
  Q₂_norm : ∀ m ∈ M₂, ∀ x ∈ Q₂, m * x * m⁻¹ ∈ Q₂
  trans : ∀ x ∈ centerOf S, x ≠ 1 → ∀ y ∈ centerOf S, y ≠ 1 → ∃ b ∈ B, b * x * b⁻¹ = y
  cent : ∀ x ∈ centerOf S, x ≠ 1 → ∀ y ∈ M₁, y * x = x * y → y ∈ M₂
  cov₁ : ∀ x ∈ Q₁, x ≠ 1 → ∃ m ∈ M₁, m * x * m⁻¹ ∈ centerOf S
  cov₂ : ∀ x ∈ Q₂, x ≠ 1 → ∃ m ∈ M₂, m * x * m⁻¹ ∈ centerOf S
  nonsolv : ¬ Group.IsSolvable M₁
  s₁_mem : s₁ ∈ M₁
  s₁_not : s₁ ∉ M₂
  s₁_sq : s₁ * s₁ = 1
  s₁_norm : ∀ b ∈ B, s₁ * b * s₁⁻¹ ∈ B
  s₂_mem : s₂ ∈ M₂
  s₂_not : s₂ ∉ M₁
  s₂_sq : s₂ * s₂ = 1
  s₂_norm : ∀ b ∈ B, s₂ * b * s₂⁻¹ ∈ B
  fix₁ : ∀ m ∈ M₁, NormedBy B (conjSub m (centerOf S)) →
    conjSub m (centerOf S) = centerOf S ∨ conjSub m (centerOf S) = conjSub s₁ (centerOf S)
  fix₂ : ∀ m ∈ M₂, NormedBy B (conjSub m (centerOf S)) →
    conjSub m (centerOf S) = centerOf S ∨ conjSub m (centerOf S) = conjSub s₂ (centerOf S)
  centS : ∀ x ∈ S, (∀ b ∈ B, x * b = b * x) → x = 1
  Z_big : ∃ x ∈ centerOf S, ∃ y ∈ centerOf S, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y
  rot : ∃ b₃ ∈ B, ∀ x ∈ B, (s₁ * s₂) ^ 3 * x * ((s₁ * s₂) ^ 3)⁻¹ = b₃ * x * b₃⁻¹

namespace L3Datum

variable {M₁ M₂ : Subgroup G} (D : L3Datum M₁ M₂)

theorem S_le_H : D.S ≤ M₁ ⊓ M₂ := by
  rw [D.S_eq]; exact LieType.BorelTits.pCoreOf_le 2 _

theorem S_pgroup [Finite G] : IsPGroup 2 D.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [D.S_eq]; exact LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem S_norm [Finite G] : ∀ h ∈ M₁ ⊓ M₂, ∀ x ∈ D.S, h * x * h⁻¹ ∈ D.S := by
  intro h hh x hx
  have := LieType.BorelTits.le_normalizer_pCoreOf 2 (M₁ ⊓ M₂) hh
  rw [← D.S_eq] at this
  exact (Subgroup.mem_normalizer_iff.mp this x).mp hx

end L3Datum

namespace L3Datum

section Gen

variable {M₁ M₂ : Subgroup G} (D : L3Datum M₁ M₂)

abbrev Z : Subgroup G := centerOf D.S

theorem mem_Z {x : G} : x ∈ D.Z ↔ x ∈ D.S ∧ ∀ s ∈ D.S, s * x = x * s := by
  unfold Z centerOf
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem Z_le_S : D.Z ≤ D.S := inf_le_left

theorem Z_le_Q₁ : D.Z ≤ D.Q₁ := by
  show centerOf D.S ≤ D.Q₁
  rw [← D.frame.inter]; exact inf_le_left

theorem Z_le_Q₂ : D.Z ≤ D.Q₂ := by
  show centerOf D.S ≤ D.Q₂
  rw [← D.frame.inter]; exact inf_le_right

theorem Z_sq {x : G} (hx : x ∈ D.Z) : x ^ 2 = 1 :=
  F7.isElemAbelian_pow_eq_one D.frame.Q₁_ea (D.Z_le_Q₁ hx)

theorem Z_comm {x y : G} (hx : x ∈ D.Z) (hy : y ∈ D.Z) : x * y = y * x :=
  ((D.mem_Z.mp hx).2 y (D.Z_le_S hy)).symm

theorem S_le_M₁ : D.S ≤ M₁ := D.S_le_H.trans inf_le_left

theorem S_le_M₂ : D.S ≤ M₂ := D.S_le_H.trans inf_le_right

theorem centZ_of_hyp {z : G} (hz : z ∈ D.Z) (hz1 : z ≠ 1)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) :
    ∀ x ∈ D.Z, x ≠ 1 → ∀ y : G, y * x = x * y → y ∈ M₁ ⊓ M₂ := by
  intro x hx hx1 y hy
  obtain ⟨b, hb, hbz⟩ := D.trans z hz hz1 x hx hx1
  have hbH : b ∈ M₁ ⊓ M₂ := D.B_le hb
  have h1 : b⁻¹ * y * b ∈ M₁ := by
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : y * (b * z * b⁻¹) = (b * z * b⁻¹) * y := by rw [hbz]; exact hy
    calc b⁻¹ * y * b * z = b⁻¹ * (y * (b * z * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * z * b⁻¹) * y) * b := by rw [this]
      _ = z * (b⁻¹ * y * b) := by group
  have h2 : y ∈ M₁ := by
    have := M₁.mul_mem (M₁.mul_mem hbH.1 h1) (M₁.inv_mem hbH.1)
    simpa [mul_assoc] using this
  exact ⟨h2, D.cent x hx hx1 y h2 hy⟩

end Gen

section Fin

variable [Finite G] {M₁ M₂ : Subgroup G} (D : L3Datum M₁ M₂)

theorem Z_norm {h x : G} (hh : h ∈ M₁ ⊓ M₂) (hx : x ∈ D.Z) : h * x * h⁻¹ ∈ D.Z := by
  rw [mem_Z] at hx ⊢
  have hh' : h⁻¹ ∈ M₁ ⊓ M₂ := (M₁ ⊓ M₂).inv_mem hh
  refine ⟨D.S_norm h hh x hx.1, fun s hs => ?_⟩
  have h1 := hx.2 (h⁻¹ * s * h) (by simpa using D.S_norm h⁻¹ hh' s hs)
  calc s * (h * x * h⁻¹) = h * ((h⁻¹ * s * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * s * h)) * h⁻¹ := by rw [h1]
    _ = h * x * h⁻¹ * s := by group

theorem B_inf_S {x : G} (hxS : x ∈ D.S) (hxB : x ∈ D.B) : x = 1 := by
  have hp := D.S_pgroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨x, hxS⟩
  have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hxS]; exact hk
  have h2 : orderOf x ∣ Nat.card D.B := by
    have := orderOf_dvd_natCard (⟨x, hxB⟩ : D.B)
    rwa [Subgroup.orderOf_mk] at this
  have hodd : Odd (orderOf x) := D.B_odd.of_dvd_nat h2
  have hk0 : k = 0 := by
    by_contra hk0
    have : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    rw [← h1] at this
    exact (Nat.not_even_iff_odd.mpr hodd) this
  rw [hk0, pow_zero] at h1
  exact orderOf_eq_one_iff.mp h1

end Fin

end L3Datum

end CFSG.Quasithin.H13.F431.L3
