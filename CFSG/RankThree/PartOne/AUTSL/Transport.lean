module

public import CFSG.RankThree.PartOne.AUTSL.Narrow

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace AUTSL

section Core

@[expose] def CoreStmt (Γ : Type*) [Group Γ] : Prop :=
  ∀ (S : Subgroup Γ), IsPGroup 2 S →
    (∃ S₀ : Sylow 2 Γ, Subgroup.normalizer ((S₀ : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer (S : Set Γ)) →
    Subgroup.normalizer (S : Set Γ) ≠ ⊤ →
    ∀ E B : Subgroup Γ, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 5 = 1) → B ≤ E →
      B ≤ Subgroup.normalizer (S : Set Γ) → Nat.card B = 25 →
      ∀ α : MulAut Γ, B.map α.toMonoidHom = B → (∀ b ∈ B, (α ^ 3) b = b) →
        (∃ b ∈ B, α b ≠ b) → ∀ x : MulAut Γ, (∀ b ∈ B, b⁻¹ * x b ∈ S) →
          E ≤ Subgroup.normalizer (S : Set Γ) ∧ ∀ g ∈ E, g⁻¹ * x g ∈ S

theorem congr_apply_apply' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) (x : X) :
    MulAut.congr e α (e x) = e (α x) := by
  simp [MulAut.congr_apply]

theorem transport_core {X Γ : Type*} [Group X] [Finite X] [Group Γ] (e : X ≃* Γ)
    (h : CoreStmt Γ) : CoreStmt X := by
  intro S hS hsyl hne E B hEc hE5 hBE hBN hB α hαB hα3 hα1 x hxB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hNmap : ∀ T : Subgroup X, (Subgroup.normalizer (T : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup Γ) : Set Γ) := fun T =>
    Subgroup.map_equiv_normalizer_eq T e
  have hS' : IsPGroup 2 (S.map e.toMonoidHom) :=
    hS.of_surjective (e.toMonoidHom.subgroupMap S) (e.toMonoidHom.subgroupMap_surjective S)
  have hsyl' : ∃ S₀ : Sylow 2 Γ, Subgroup.normalizer ((S₀ : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Γ) : Set Γ) := by
    obtain ⟨S₀, hS₀⟩ := hsyl
    refine ⟨Sylow.mapSurjective hsurj S₀, ?_⟩
    rw [Sylow.coe_mapSurjective hsurj S₀, ← hNmap, ← hNmap]
    exact Subgroup.map_mono hS₀
  have hne' : Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Γ) : Set Γ) ≠ ⊤ := by
    intro htop
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) (fun a b h => e.injective h)
    rw [hNmap, htop, Subgroup.map_top_of_surjective _ hsurj]
  have hEc' : ∀ g ∈ E.map e.toMonoidHom, ∀ h ∈ E.map e.toMonoidHom, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg e (hEc a ha b hb)
  have hE5' : ∀ g ∈ E.map e.toMonoidHom, g ^ 5 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE5 a ha, map_one]
  have hBE' : B.map e.toMonoidHom ≤ E.map e.toMonoidHom := Subgroup.map_mono hBE
  have hBN' : B.map e.toMonoidHom ≤
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Γ) : Set Γ) := by
    rw [← hNmap]
    exact Subgroup.map_mono hBN
  have hB' : Nat.card (B.map e.toMonoidHom) = 25 := by
    rw [Subgroup.card_map_of_injective e.injective, hB]
  have hαB' : (B.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom = B.map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have : (MulAut.congr e α).toMonoidHom (e.toMonoidHom b) = e (α b) :=
        congr_apply_apply' e α b
      rw [this]
      refine ⟨α b, ?_, rfl⟩
      rw [← hαB]
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      rw [← hαB] at hb
      obtain ⟨c, hc, rfl⟩ := hb
      refine ⟨e c, ⟨c, hc, rfl⟩, ?_⟩
      exact congr_apply_apply' e α c
  have hα3' : ∀ b ∈ B.map e.toMonoidHom, ((MulAut.congr e α) ^ 3) b = b := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow]
    have := congr_apply_apply' e (α ^ 3) b
    change (MulAut.congr e (α ^ 3)) (e b) = e b
    rw [this, hα3 b hb]
  have hα1' : ∃ b ∈ B.map e.toMonoidHom, (MulAut.congr e α) b ≠ b := by
    obtain ⟨b, hb, hne⟩ := hα1
    refine ⟨e b, ⟨b, hb, rfl⟩, ?_⟩
    rw [congr_apply_apply']
    exact fun h => hne (e.injective h)
  have hxB' : ∀ b ∈ B.map e.toMonoidHom, b⁻¹ * (MulAut.congr e x) b ∈ S.map e.toMonoidHom := by
    rintro _ ⟨b, hb, rfl⟩
    have := congr_apply_apply' e x b
    change (e b)⁻¹ * (MulAut.congr e x) (e b) ∈ _
    rw [this, ← map_inv, ← map_mul]
    exact ⟨_, hxB b hb, rfl⟩
  obtain ⟨hEN, hEx⟩ := h _ hS' hsyl' hne' _ _ hEc' hE5' hBE' hBN' hB' (MulAut.congr e α) hαB' hα3'
    hα1' (MulAut.congr e x) hxB'
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have h1 := hEN ⟨g, hg, rfl⟩
    rw [← hNmap] at h1
    obtain ⟨n, hn, hng⟩ := h1
    have : n = g := e.injective hng
    rwa [← this]
  · have h1 := hEx _ ⟨g, hg, rfl⟩
    change (e g)⁻¹ * (MulAut.congr e x) (e g) ∈ _ at h1
    rw [congr_apply_apply', ← map_inv, ← map_mul] at h1
    obtain ⟨s, hs, hse⟩ := h1
    have : s = g⁻¹ * x g := e.injective hse
    rwa [← this]

theorem kf1511BTEAt_of_core (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ)
    (h : ∀ (X : Type) [Group X] [Finite X] (f : ℕ), Blueprint.LieModel X t n 2 f →
      CoreStmt X) : KF1511BTEAt t n := by
  intro X _ _ f hmodel S _ hS2 _ hne hsyl E hE _ B hBE hBN hBcard α _ hαB hα3 hα1 Q _ _ ρ _ _ hρB
  have hEexp : ∀ g ∈ E, g ^ 5 = 1 := fun g hg => by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian g hg
  have hEcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨g, hg⟩ : E) ⟨h, hh⟩)
  have main := h X f hmodel S hS2 hsyl hne E B hEcomm hEexp hBE hBN hBcard α hαB hα3 hα1
  exact ⟨(main 1 fun b _ => by simp).1, fun q g hg => (main (ρ q) (hρB q)).2 g hg⟩

end Core

end AUTSL

end CFSG.RankThree.PartOne
