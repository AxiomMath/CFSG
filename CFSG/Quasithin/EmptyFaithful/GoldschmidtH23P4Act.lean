module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique CFSG.Quasithin.H23Out
open scoped Pointwise

theorem conj_injective_of_center_eq_bot {Γ : Type*} [Group Γ] (hZ : Subgroup.center Γ = ⊥) :
    Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
  have hcen : g ∈ Subgroup.center Γ := by
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    have h1 := congrArg (fun φ : MulAut Γ => φ y) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * g = (g * y * g⁻¹) * g := by rw [h1]
      _ = g * y := by group
  rwa [hZ, Subgroup.mem_bot] at hcen

theorem key_overgroup {Γ : Type*} [Group Γ] [Finite Γ] (hZ : Subgroup.center Γ = ⊥)
    (hOut : Out5Pow Γ) {A : Type*} [Group A] (ρ : A →* MulAut Γ)
    {X Y : Subgroup A} (hX : IsPGroup 2 X) (hY : IsPGroup 5 Y)
    (hXY : (X : Set A) * Y = Y * X) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hsub : ∀ s ∈ S₀, (MulAut.conj s : MulAut Γ) ∈ X.map ρ) :
    ∃ (U : Subgroup Γ) (b : ℕ), S₀ ≤ U ∧ S₀.relIndex U = 5 ^ b ∧
      (∀ y ∈ Y, ∃ g ∈ U, ρ y = MulAut.conj g) ∧ (b = 0 → Y ≤ ρ.ker) ∧
      (∀ x ∈ X, ∀ g : Γ, ρ x = MulAut.conj g → g ∈ S₀) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) :=
    conj_injective_of_center_eq_bot hZ
  set c : Γ →* MulAut Γ := MulAut.conj with hc
  set I : Subgroup (MulAut Γ) := c.range with hI
  set P₂ : Subgroup (MulAut Γ) := X.map ρ with hP₂def
  set P₅ : Subgroup (MulAut Γ) := Y.map ρ with hP₅def
  have hP₂ : IsPGroup 2 P₂ := hX.map ρ
  have hP₅ : IsPGroup 5 P₅ := hY.map ρ
  have hP₅I : P₅ ≤ I := by
    have := hOut.range_le_inner hP₅ P₅.subtype
    rwa [Subgroup.range_subtype] at this
  have hodd : ¬ 2 ∣ S₀.index := (isSylowTwoOf_top_iff.1 hS₀).2
  have hS₀P : ∀ s ∈ S₀, c s ∈ P₂ ⊓ I := fun s hs => ⟨hsub s hs, s, rfl⟩
  have hT₂ : S₀ = (P₂ ⊓ I).comap c := by
    have hp : IsPGroup 2 ((P₂ ⊓ I).comap c) :=
      (hP₂.to_le inf_le_left).comap_of_injective c hinj
    exact eq_of_isPGroup_two_of_le (fun s hs => hS₀P s hs) hp hodd
  have hcomm : (P₂ : Set (MulAut Γ)) * (P₅ : Set (MulAut Γ)) =
      (P₅ : Set (MulAut Γ)) * (P₂ : Set (MulAut Γ)) := by
    simp only [hP₂def, hP₅def, Subgroup.coe_map]
    rw [← Set.image_mul, ← Set.image_mul, hXY]
  have hD : ((P₂ ⊔ P₅ : Subgroup (MulAut Γ)) : Set (MulAut Γ)) =
      (P₂ : Set (MulAut Γ)) * (P₅ : Set (MulAut Γ)) :=
    coe_sup_eq_mul_of_mul_comm hcomm
  set U : Subgroup Γ := ((P₂ ⊔ P₅) ⊓ I).comap c with hU
  set Yt : Subgroup Γ := P₅.comap c with hYt
  have hS₀U : S₀ ≤ U := by
    intro s hs
    refine ⟨Subgroup.mem_sup_left (hS₀P s hs).1, (hS₀P s hs).2⟩
  have hUset : (U : Set Γ) = (S₀ : Set Γ) * Yt := by
    ext x
    constructor
    · intro hx
      have hx' : c x ∈ ((P₂ : Set (MulAut Γ)) * (P₅ : Set (MulAut Γ))) ∩ (I : Set (MulAut Γ)) := by
        have h1 : c x ∈ (P₂ ⊔ P₅) ⊓ I := hx
        exact ⟨by rw [← hD]; exact h1.1, h1.2⟩
      rw [inf_mul_eq_mul_inf hP₅I] at hx'
      obtain ⟨p, hp, q, hq, hpq⟩ := hx'
      obtain ⟨s, hs⟩ := hp.2
      obtain ⟨y, hy⟩ := hP₅I hq
      have hxsy : x = s * y := by
        apply hinj
        rw [map_mul, hs, hy]
        exact hpq.symm
      refine ⟨s, ?_, y, ?_, hxsy.symm⟩
      · rw [hT₂]
        show c s ∈ P₂ ⊓ I
        rw [hs]
        exact hp
      · show c y ∈ P₅
        rw [hy]
        exact hq
    · rintro ⟨s, hs, y, hy, rfl⟩
      have h1 : c s ∈ P₂ ⊓ I := hS₀P s hs
      have h2 : c y ∈ P₅ := hy
      show c (s * y) ∈ (P₂ ⊔ P₅) ⊓ I
      rw [map_mul]
      exact ⟨(P₂ ⊔ P₅).mul_mem (Subgroup.mem_sup_left h1.1) (Subgroup.mem_sup_right h2),
        I.mul_mem h1.2 (hP₅I h2)⟩
  have hdisj : S₀ ⊓ Yt = ⊥ := by
    have hS2 : IsPGroup 2 S₀ := (isSylowTwoOf_top_iff.1 hS₀).1
    have hY5 : IsPGroup 5 Yt := hP₅.comap_of_injective c hinj
    exact disjoint_iff.1 (IsPGroup.disjoint_of_ne 2 5 (by norm_num) S₀ Yt hS2 hY5)
  have hidx : S₀.relIndex U = Nat.card Yt :=
    relIndex_eq_card_of_coe_eq_mul hS₀U hUset hdisj
  have hY5 : IsPGroup 5 Yt := hP₅.comap_of_injective c hinj
  obtain ⟨b, hb⟩ := hY5.exists_card_eq
  refine ⟨U, b, hS₀U, hidx.trans hb, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨g, hg⟩ := hP₅I (⟨y, hy, rfl⟩ : ρ y ∈ P₅)
    refine ⟨g, ?_, hg.symm⟩
    show c g ∈ (P₂ ⊔ P₅) ⊓ I
    rw [hg]
    exact ⟨Subgroup.mem_sup_right ⟨y, hy, rfl⟩, hP₅I ⟨y, hy, rfl⟩⟩
  · intro hb0
    have hcard : Nat.card Yt = 1 := by rw [hb, hb0, pow_zero]
    have hYtbot : Yt = ⊥ := Subgroup.eq_bot_of_card_eq Yt hcard
    have hP₅bot : P₅ = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      obtain ⟨g, hg⟩ := hP₅I hx
      have : g ∈ Yt := by
        show c g ∈ P₅
        rw [hg]
        exact hx
      rw [hYtbot, Subgroup.mem_bot] at this
      rw [← hg, this, map_one]
    intro y hy
    have : ρ y ∈ P₅ := ⟨y, hy, rfl⟩
    rw [hP₅bot, Subgroup.mem_bot] at this
    exact this
  · intro x hx g hg
    rw [hT₂]
    show c g ∈ P₂ ⊓ I
    rw [← hg]
    exact ⟨⟨x, hx, rfl⟩, ⟨g, hg.symm⟩⟩

theorem trivial_of_overgroup {Γ : Type*} [Group Γ] [Finite Γ] (hZ : Subgroup.center Γ = ⊥)
    (hOut : Out5Pow Γ) (hNo : NoFiveIndex Γ) {A : Type*} [Group A] (ρ : A →* MulAut Γ)
    {X Y : Subgroup A} (hX : IsPGroup 2 X) (hY : IsPGroup 5 Y)
    (hXY : (X : Set A) * Y = Y * X) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hsub : ∀ s ∈ S₀, (MulAut.conj s : MulAut Γ) ∈ X.map ρ) : Y ≤ ρ.ker := by
  obtain ⟨U, b, hS₀U, hb, -, hb0, -⟩ := key_overgroup hZ hOut ρ hX hY hXY hS₀ hsub
  exact hb0 (hNo S₀ U hS₀ hS₀U b hb)

end CFSG.Quasithin.H23P4
