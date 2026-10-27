module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Lines
public import CFSG.Quasithin.Recognition.F4Setting

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin

section Setting

@[expose] noncomputable def d4Setting : LieSetting.{0, 0} where
  α := RankTwoAmalgam.ofSubgroups d4H d4N
  Yb := ↥(d4H ⊔ d4N)
  ι := RankTwoAmalgam.inclusionCompletion d4H d4N (d4H ⊔ d4N) rfl
  hι := RankTwoAmalgam.inclusionCompletion_isFaithful d4H d4N (d4H ⊔ d4N) rfl
  N := ⊤
  hN := Subgroup.normal_of_characteristic ⊤
  p := 2
  hp := Nat.prime_two
  m := 6
  hm := by norm_num

@[simp] theorem d4Setting_m : d4Setting.m = 6 := rfl

@[simp] theorem d4Setting_p : d4Setting.p = 2 := rfl

@[simp] theorem d4Setting_N : d4Setting.N = ⊤ := rfl

theorem card_d4Setting_Yb :
    Nat.card d4Setting.Yb = 211341312 := by
  change Nat.card ↥(d4H ⊔ d4N) = _
  rw [d4H_sup_d4N, Subgroup.card_top]
  exact card_trialityGroup8

end Setting

section Phi

@[expose] noncomputable def d4Phi : D →* d4Setting.ι.G0 where
  toFun x := ⟨⟨x, by rw [d4H_sup_d4N]; exact Subgroup.mem_top _⟩, by
    rw [d4Setting.ι.gen]
    exact Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def d4ToD (k : d4Setting.ι.G0) : D := Subtype.val (Subtype.val k)

theorem d4ToD_d4Phi (x : D) : d4ToD (d4Phi x) = x := rfl

theorem d4Phi_injective : Function.Injective d4Phi := fun x y h =>
  by simpa [d4ToD_d4Phi] using congrArg d4ToD h

theorem d4Phi_surjective : Function.Surjective d4Phi := by
  rintro ⟨⟨σ, hσ⟩, hg⟩
  exact ⟨σ, rfl⟩

theorem mem_range_φ1_iff (k : d4Setting.ι.G0) :
    ((k : d4Setting.Yb) ∈ d4Setting.ι.φ1.range) ↔ d4ToD k ∈ d4H := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [d4ToD, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem mem_range_φ2_iff (k : d4Setting.ι.G0) :
    ((k : d4Setting.Yb) ∈ d4Setting.ι.φ2.range) ↔ d4ToD k ∈ d4N := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [d4ToD, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

end Phi

end CFSG.Quasithin.D4Hex
