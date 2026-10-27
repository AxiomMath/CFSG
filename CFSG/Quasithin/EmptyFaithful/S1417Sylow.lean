module

public import CFSG.Quasithin.EmptyFaithful.S1417Blocks
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S1417

section Card

variable {G : Type*} [Group G] [Finite G]

theorem card_eq_two_of_isSylowTwoOf {P H : Subgroup G} (hP : IsSylowTwoOf P H)
    (hH : Nat.card H = 6) : Nat.card P = 2 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP.2.1
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_eq_left.mpr hP.1, hk, hH] at h1
  have hodd : ¬ 2 ∣ P.relIndex H := hP.2.2
  rcases k with _ | _ | k
  · exfalso
    apply hodd
    have : P.relIndex H = 6 := by simpa using h1
    rw [this]
    norm_num
  · simpa using hk
  · exfalso
    have : 4 ∣ 6 := ⟨P.relIndex H * 2 ^ k, by rw [← h1]; ring⟩
    omega

theorem card_eq_four_of_isSylowTwoOf {P H : Subgroup G} (hP : IsSylowTwoOf P H)
    (hH : Nat.card H = 36) : Nat.card P = 4 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP.2.1
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_eq_left.mpr hP.1, hk, hH] at h1
  have hodd : ¬ 2 ∣ P.relIndex H := hP.2.2
  rcases k with _ | _ | _ | k
  · exfalso
    apply hodd
    have : P.relIndex H = 36 := by simpa using h1
    rw [this]
    norm_num
  · exfalso
    apply hodd
    have : P.relIndex H = 18 := by
      have : P.relIndex H * 2 = 36 := by simpa using h1
      omega
    rw [this]
    norm_num
  · simpa using hk
  · exfalso
    have : 8 ∣ 36 := ⟨P.relIndex H * 2 ^ k, by rw [← h1]; ring⟩
    omega

omit [Finite G] in
theorem exists_eq_of_card_eq_two {P : Subgroup G} (h : Nat.card P = 2) :
    ∃ s ∈ P, s ≠ 1 ∧ ∀ x ∈ P, x = 1 ∨ x = s := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : P)).mp h
  refine ⟨y, y.2, fun h1 => hy (Subtype.ext h1), fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have := huniq ⟨x, hx⟩ (fun h' => hx1 (congrArg Subtype.val h'))
    exact congrArg Subtype.val this

end Card

section Swap

variable {W : Type*} [CommGroup W] {L₁ L₂ X T' : Subgroup (MulAut W)}

theorem conjAut_eq_iff_mem_normalizer {g : MulAut W} {A : Subgroup (MulAut W)} :
    B1.conjAut g A = A ↔ g ∈ Subgroup.normalizer (A : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff'']
  constructor
  · intro h x
    rw [← B1.mem_conjAut, h]
  · intro h
    ext x
    rw [B1.mem_conjAut, ← h x]

theorem exists_swap_mem_of_isSylowTwoOf [Finite W] (hT : IsSylowTwoOf T' X) {s : MulAut W}
    (hsX : s ∈ X) (hs : B1.conjAut s L₁ ≠ L₁)
    (hperm : ∀ g ∈ X, (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
      (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁)) :
    ∃ τ ∈ T', B1.conjAut τ L₁ ≠ L₁ := by
  by_contra hcon
  push Not at hcon
  have hs' : B1.conjAut s L₁ = L₂ ∧ B1.conjAut s L₂ = L₁ := by
    rcases hperm s hsX with ⟨h, -⟩ | h
    · exact absurd h hs
    · exact h
  have hidx : (X ⊓ Subgroup.normalizer (L₁ : Set (MulAut W))).relIndex X = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨s, hsX, fun b hb => ?_⟩
    have hbs : b * s ∈ X := X.mul_mem hb hsX
    have e1 : b * s ∈ X ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)) ↔
        B1.conjAut (b * s) L₁ = L₁ := by
      rw [Subgroup.mem_inf, conjAut_eq_iff_mem_normalizer]
      exact ⟨fun h => h.2, fun h => ⟨hbs, h⟩⟩
    have e2 : b ∈ X ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)) ↔ B1.conjAut b L₁ = L₁ := by
      rw [Subgroup.mem_inf, conjAut_eq_iff_mem_normalizer]
      exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
    rw [e1, e2, conjAut_mul, hs'.1]
    rcases hperm b hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, h1]
      have hne : L₂ ≠ L₁ := by
        intro h
        exact hs (hs'.1.trans h)
      simp [hne]
    · rw [h2, h1]
      have hne : L₂ ≠ L₁ := by
        intro h
        exact hs (hs'.1.trans h)
      simp [hne]
  have hle : T' ≤ X ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
    intro τ hτ
    exact ⟨hT.1 hτ, conjAut_eq_iff_mem_normalizer.mp (hcon τ hτ)⟩
  have hdvd := Subgroup.relIndex_dvd_of_le_left X hle
  rw [hidx] at hdvd
  exact hT.2.2 hdvd

end Swap

section SylowData

variable {W : Type*} [CommGroup W] [Finite W] {L₁ L₂ S : Subgroup (MulAut W)}

structure SylowData (S L₁ L₂ : Subgroup (MulAut W)) (s₁ s₂ : MulAut W) (a₁ a₂ : W) : Prop where
  s₁_mem_S : s₁ ∈ S
  s₂_mem_S : s₂ ∈ S
  s₁_mem_L : s₁ ∈ L₁
  s₂_mem_L : s₂ ∈ L₂
  s₁_ne : s₁ ≠ 1
  s₂_ne : s₂ ≠ 1
  inf₁ : ∀ x ∈ S, x ∈ L₁ → x = 1 ∨ x = s₁
  inf₂ : ∀ x ∈ S, x ∈ L₂ → x = 1 ∨ x = s₂
  a₁_mem : a₁ ∈ commV L₁
  a₂_mem : a₂ ∈ commV L₂
  a₁_ne : a₁ ≠ 1
  a₂_ne : a₂ ≠ 1
  fix₁ : ∀ u ∈ commV L₁, s₁ u = u ↔ (u = 1 ∨ u = a₁)
  fix₂ : ∀ u ∈ commV L₂, s₂ u = u ↔ (u = 1 ∨ u = a₂)
  fixS : ∀ w : W, (∀ x ∈ S, x w = w) ↔ (w = 1 ∨ w = a₁ ∨ w = a₂ ∨ w = a₁ * a₂)

theorem exists_sylowData (hS : IsSylowTwoOf S (L₁ ⊔ L₂)) (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hLinf : L₁ ⊓ L₂ = ⊥) (hinf : commV L₁ ⊓ commV L₂ = ⊥)
    (hUtop : commV L₁ ⊔ commV L₂ = ⊤) :
    ∃ (s₁ s₂ : MulAut W) (a₁ a₂ : W), SylowData S L₁ L₂ s₁ s₂ a₁ a₂ := by
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : commV L₂ ⊓ commV L₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hcard₁ : Nat.card L₁ = 6 := (card_of_actsAsNaturalL2 hN₁).1
  have hcard₂ : Nat.card L₂ = 6 := (card_of_actsAsNaturalL2 hN₂).1
  have hJcard : Nat.card ↥(L₁ ⊔ L₂) = 36 := by
    have := B2F.card_sup_mul_card_inf_of_commute hc
    rw [hLinf, Subgroup.card_bot, mul_one, hcard₁, hcard₂] at this
    omega
  have hScard : Nat.card S = 4 := card_eq_four_of_isSylowTwoOf hS hJcard
  have hn₁ : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    exact Subgroup.centralizer_le_normalizer (s := (L₁ : Set (MulAut W)))
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb)
  have hn₂ : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₂ : Set (MulAut W)) := by
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer (s := (L₂ : Set (MulAut W)))
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)
  have hS₁ : IsSylowTwoOf (S ⊓ L₁) L₁ := A4.isSylowTwoOf_inf_normal hS le_sup_left hn₁
  have hS₂ : IsSylowTwoOf (S ⊓ L₂) L₂ := A4.isSylowTwoOf_inf_normal hS le_sup_right hn₂
  have hS₁card : Nat.card ↥(S ⊓ L₁) = 2 := card_eq_two_of_isSylowTwoOf hS₁ hcard₁
  have hS₂card : Nat.card ↥(S ⊓ L₂) = 2 := card_eq_two_of_isSylowTwoOf hS₂ hcard₂
  obtain ⟨s₁, hs₁m, hs₁1, hs₁u⟩ := exists_eq_of_card_eq_two hS₁card
  obtain ⟨s₂, hs₂m, hs₂1, hs₂u⟩ := exists_eq_of_card_eq_two hS₂card
  have hs₁sq : s₁ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥(S ⊓ L₁)) (x := ⟨s₁, hs₁m⟩)
    rw [hS₁card] at this
    exact congrArg Subtype.val this
  have hs₂sq : s₂ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥(S ⊓ L₂)) (x := ⟨s₂, hs₂m⟩)
    rw [hS₂card] at this
    exact congrArg Subtype.val this
  obtain ⟨a₁, ha₁m, ha₁1, ha₁f⟩ := exists_fixed_vector hN₁
    (fun l hl u hu => commV_stable L₁ hl hu) hs₁m.2 hs₁sq hs₁1
  obtain ⟨a₂, ha₂m, ha₂1, ha₂f⟩ := exists_fixed_vector hN₂
    (fun l hl u hu => commV_stable L₂ hl hu) hs₂m.2 hs₂sq hs₂1
  have htr₁ : ∀ x ∈ L₁, ∀ u ∈ commV L₂, x u = u := fun x hx u hu =>
    apply_eq_of_mem_commV_of_commute hc hinf hx hu
  have htr₂ : ∀ x ∈ L₂, ∀ u ∈ commV L₁, x u = u := fun x hx u hu =>
    apply_eq_of_mem_commV_of_commute hc' hinf' hx hu
  have hcomm : ∀ a ∈ S ⊓ L₁, ∀ b ∈ S ⊓ L₂, a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have hSeq : S = (S ⊓ L₁) ⊔ (S ⊓ L₂) := by
    have hinf2 : (S ⊓ L₁) ⊓ (S ⊓ L₂) = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [← hLinf]
      exact inf_le_inf inf_le_right inf_le_right
    have h1 := B2F.card_sup_mul_card_inf_of_commute hcomm
    rw [hinf2, Subgroup.card_bot, mul_one, hS₁card, hS₂card] at h1
    exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (by omega)).symm
  refine ⟨s₁, s₂, a₁, a₂, ⟨hs₁m.1, hs₂m.1, hs₁m.2, hs₂m.2, hs₁1, hs₂1,
    fun x hx hxL => hs₁u x ⟨hx, hxL⟩, fun x hx hxL => hs₂u x ⟨hx, hxL⟩, ha₁m, ha₂m, ha₁1, ha₂1,
    ha₁f, ha₂f, fun w => ?_⟩⟩
  constructor
  · intro hw
    have hw' : w ∈ commV L₁ ⊔ commV L₂ := by rw [hUtop]; exact Subgroup.mem_top w
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hw'
    have e₁ : s₁ u₁ = u₁ := by
      have h := hw s₁ hs₁m.1
      rw [map_mul, htr₁ s₁ hs₁m.2 u₂ hu₂] at h
      exact mul_right_cancel h
    have e₂ : s₂ u₂ = u₂ := by
      have h := hw s₂ hs₂m.1
      rw [map_mul, htr₂ s₂ hs₂m.2 u₁ hu₁] at h
      exact mul_left_cancel h
    rcases (ha₁f u₁ hu₁).mp e₁ with h₁ | h₁ <;> rcases (ha₂f u₂ hu₂).mp e₂ with h₂ | h₂
    · left; rw [h₁, h₂, mul_one]
    · right; right; left; rw [h₁, h₂, one_mul]
    · right; left; rw [h₁, h₂, mul_one]
    · right; right; right; rw [h₁, h₂]
  · intro hw x hx
    rw [hSeq] at hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    have hfix₁ : ∀ w' : W, (w' = 1 ∨ w' = a₁ ∨ w' = a₂ ∨ w' = a₁ * a₂) → s₁ w' = w' := by
      rintro w' (h | h | h | h)
      · rw [h, map_one]
      · rw [h]; exact (ha₁f a₁ ha₁m).mpr (Or.inr rfl)
      · rw [h]; exact htr₁ s₁ hs₁m.2 a₂ ha₂m
      · rw [h, map_mul, htr₁ s₁ hs₁m.2 a₂ ha₂m, (ha₁f a₁ ha₁m).mpr (Or.inr rfl)]
    have hfix₂ : ∀ w' : W, (w' = 1 ∨ w' = a₁ ∨ w' = a₂ ∨ w' = a₁ * a₂) → s₂ w' = w' := by
      rintro w' (h | h | h | h)
      · rw [h, map_one]
      · rw [h]; exact htr₂ s₂ hs₂m.2 a₁ ha₁m
      · rw [h]; exact (ha₂f a₂ ha₂m).mpr (Or.inr rfl)
      · rw [h, map_mul, htr₂ s₂ hs₂m.2 a₁ ha₁m, (ha₂f a₂ ha₂m).mpr (Or.inr rfl)]
    have h₂w : x₂ w = w := by
      rcases hs₂u x₂ hx₂ with h | h
      · rw [h, MulAut.one_apply]
      · rw [h]; exact hfix₂ w hw
    have h₁w : x₁ w = w := by
      rcases hs₁u x₁ hx₁ with h | h
      · rw [h, MulAut.one_apply]
      · rw [h]; exact hfix₁ w hw
    rw [MulAut.mul_apply, h₂w, h₁w]

omit [Finite W] in
theorem SylowData.swap_apply {s₁ s₂ : MulAut W} {a₁ a₂ : W} (hd : SylowData S L₁ L₂ s₁ s₂ a₁ a₂)
    {τ : MulAut W} (hτS : B1.conjAut τ S = S) (hτ₁ : B1.conjAut τ L₁ = L₂)
    (hτ₂ : B1.conjAut τ L₂ = L₁) (hU₁ : ∀ u ∈ commV L₁, τ u ∈ commV L₂)
    (hU₂ : ∀ u ∈ commV L₂, τ u ∈ commV L₁) : τ a₁ = a₂ ∧ τ a₂ = a₁ := by
  have key₁ : τ * s₁ * τ⁻¹ = s₂ := by
    have hmS : τ * s₁ * τ⁻¹ ∈ S := by
      have : τ * s₁ * τ⁻¹ ∈ B1.conjAut τ S := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₁_mem_S
      rwa [hτS] at this
    have hmL : τ * s₁ * τ⁻¹ ∈ L₂ := by
      have : τ * s₁ * τ⁻¹ ∈ B1.conjAut τ L₁ := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₁_mem_L
      rwa [hτ₁] at this
    rcases hd.inf₂ _ hmS hmL with h | h
    · exfalso
      apply hd.s₁_ne
      have h2 : s₁ = τ⁻¹ * (τ * s₁ * τ⁻¹) * τ := by group
      rw [h, mul_one, inv_mul_cancel] at h2
      exact h2
    · exact h
  have key₂ : τ * s₂ * τ⁻¹ = s₁ := by
    have hmS : τ * s₂ * τ⁻¹ ∈ S := by
      have : τ * s₂ * τ⁻¹ ∈ B1.conjAut τ S := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₂_mem_S
      rwa [hτS] at this
    have hmL : τ * s₂ * τ⁻¹ ∈ L₁ := by
      have : τ * s₂ * τ⁻¹ ∈ B1.conjAut τ L₂ := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₂_mem_L
      rwa [hτ₂] at this
    rcases hd.inf₁ _ hmS hmL with h | h
    · exfalso
      apply hd.s₂_ne
      have h2 : s₂ = τ⁻¹ * (τ * s₂ * τ⁻¹) * τ := by group
      rw [h, mul_one, inv_mul_cancel] at h2
      exact h2
    · exact h
  have hne₁ : τ a₁ ≠ 1 := fun h => hd.a₁_ne (τ.injective (by rw [h, map_one]))
  have hne₂ : τ a₂ ≠ 1 := fun h => hd.a₂_ne (τ.injective (by rw [h, map_one]))
  constructor
  · have hfix : s₂ (τ a₁) = τ a₁ := by
      rw [← key₁, MulAut.mul_apply, MulAut.mul_apply]
      have : τ⁻¹ (τ a₁) = a₁ := by simp
      rw [this, (hd.fix₁ a₁ hd.a₁_mem).mpr (Or.inr rfl)]
    rcases (hd.fix₂ _ (hU₁ a₁ hd.a₁_mem)).mp hfix with h | h
    · exact absurd h hne₁
    · exact h
  · have hfix : s₁ (τ a₂) = τ a₂ := by
      rw [← key₂, MulAut.mul_apply, MulAut.mul_apply]
      have : τ⁻¹ (τ a₂) = a₂ := by simp
      rw [this, (hd.fix₂ a₂ hd.a₂_mem).mpr (Or.inr rfl)]
    rcases (hd.fix₁ _ (hU₂ a₂ hd.a₂_mem)).mp hfix with h | h
    · exact absurd h hne₂
    · exact h

end SylowData

end S1417

end CFSG.Quasithin
