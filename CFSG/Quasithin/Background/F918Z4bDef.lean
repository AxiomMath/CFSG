module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

@[expose] def IsElemAb2 {Γ : Type*} [Group Γ] (E : Subgroup Γ) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ 2 = 1

@[expose] def AutRankLe (L : Type) [Group L] (m : ℕ) : Prop :=
  ∀ E : Subgroup (MulAut L), IsElemAb2 E → rk E ≤ m

section Basic

variable {Γ Δ : Type*} [Group Γ] [Group Δ]

theorem IsElemAb2.mono {E F : Subgroup Γ} (hE : IsElemAb2 E) (h : F ≤ E) : IsElemAb2 F :=
  ⟨fun a ha b hb => hE.1 a (h ha) b (h hb), fun a ha => hE.2 a (h ha)⟩

theorem IsElemAb2.isPGroup {E : Subgroup Γ} (hE : IsElemAb2 E) : IsPGroup 2 E :=
  isPGroup_two_of_sq_eq_one fun a => Subtype.ext (hE.2 a a.2)

theorem IsElemAb2.card_eq_two_pow {E : Subgroup Γ} [Finite E] (hE : IsElemAb2 E) :
    Nat.card E = 2 ^ rk E :=
  card_eq_two_pow_of_isPGroup hE.isPGroup

theorem IsElemAb2.map {E : Subgroup Γ} (hE : IsElemAb2 E) (f : Γ →* Δ) : IsElemAb2 (E.map f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem IsElemAb2.comap {E : Subgroup Δ} (hE : IsElemAb2 E) (f : Γ →* Δ)
    (hf : Function.Injective f) : IsElemAb2 (E.comap f) := by
  refine ⟨fun a ha b hb => hf ?_, fun a ha => hf ?_⟩
  · rw [map_mul, map_mul]
    exact hE.1 _ ha _ hb
  · rw [map_pow, map_one]
    exact hE.2 _ ha

theorem rk_le_of_card_le_two_pow {W : Type*} [Group W] [Finite W] (hW : IsPGroup 2 W) {m : ℕ}
    (h : Nat.card W ≤ 2 ^ m) : rk W ≤ m := by
  rw [card_eq_two_pow_of_isPGroup hW] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem rk_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) : rk A = rk B := by
  unfold rk
  rw [Nat.card_congr e.toEquiv]

theorem rk_map_eq_of_injective {E : Subgroup Γ} (f : Γ →* Δ) (hf : Function.Injective f) :
    rk (E.map f) = rk E :=
  (rk_eq_of_mulEquiv (Subgroup.equivMapOfInjective E f hf)).symm

theorem rk_comap_eq_of_le_range {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {E : Subgroup B} (hE : E ≤ f.range) :
    rk (E.comap f) = rk E := by
  have h : (E.comap f).map f = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hE
  calc rk (E.comap f) = rk ((E.comap f).map f) := (rk_map_eq_of_injective f hf).symm
    _ = rk E := by rw [h]

end Basic

theorem AutRankLe.mono {L : Type} [Group L] {m m' : ℕ} (h : AutRankLe L m) (hm : m ≤ m') :
    AutRankLe L m' := fun E hE => (h E hE).trans hm

theorem AutRankLe.rk_map_le {L : Type} [Group L] {m : ℕ} (h : AutRankLe L m) {Γ : Type*}
    [Group Γ] {E : Subgroup Γ} (hE : IsElemAb2 E) (f : Γ →* MulAut L) : rk (E.map f) ≤ m :=
  h _ (hE.map f)

theorem AutRankLe.of_mulEquiv {L M : Type} [Group L] [Group M] (e : L ≃* M) {m : ℕ}
    (h : AutRankLe M m) : AutRankLe L m := fun E hE => by
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  rw [← rk_map_eq_of_injective _ hinj]
  exact h _ (hE.map _)

end CFSG.Quasithin
