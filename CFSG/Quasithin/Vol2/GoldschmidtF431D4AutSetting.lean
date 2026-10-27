module

public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Recognition.F4Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Stab

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

theorem normal_conj_range (G : Type*) [Group G] :
    ((MulAut.conj : G →* MulAut G).range).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, MulEquiv.ext fun x => ?_⟩
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

section Setting

@[expose] noncomputable def d3Iota :
    (RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)).Completion
      ↥(autStab d4H ⊔ autStab d4N) :=
  RankTwoAmalgam.inclusionCompletion (autStab d4H) (autStab d4N) (autStab d4H ⊔ autStab d4N) rfl

@[expose] noncomputable def d3NN : Subgroup d3Iota.G0 :=
  Subgroup.comap
    ((Subgroup.subtype (autStab d4H ⊔ autStab d4N)).comp
      (Subgroup.subtype (d3Iota.φ1.range ⊔ d3Iota.φ2.range)))
    (MulAut.conj : D →* MulAut D).range

theorem d3NN_normal : d3NN.Normal := (normal_conj_range D).comap _

@[expose] noncomputable def d3Setting : LieSetting.{0, 0} where
  α := RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)
  Yb := ↥(autStab d4H ⊔ autStab d4N)
  ι := d3Iota
  hι := RankTwoAmalgam.inclusionCompletion_isFaithful _ _ _ rfl
  N := d3NN
  hN := d3NN_normal
  p := 2
  hp := Nat.prime_two
  m := 6
  hm := by norm_num

@[simp] theorem d3Setting_m : d3Setting.m = 6 := rfl

@[simp] theorem d3Setting_p : d3Setting.p = 2 := rfl

end Setting

section Phi

@[expose] noncomputable def d3Phi : ↥(autStab d4H ⊔ autStab d4N) →* d3Setting.ι.G0 where
  toFun x := ⟨x, by rw [d3Setting.ι.gen]; exact Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def d3ToAut (k : d3Setting.ι.G0) : MulAut D := Subtype.val (Subtype.val k)

theorem d3ToAut_d3Phi (x : ↥(autStab d4H ⊔ autStab d4N)) : d3ToAut (d3Phi x) = x := rfl

theorem d3Phi_injective : Function.Injective d3Phi := fun x y h =>
  Subtype.ext (by simpa [d3ToAut_d3Phi] using congrArg d3ToAut h)

theorem d3Phi_surjective : Function.Surjective d3Phi := by
  rintro ⟨⟨σ, hσ⟩, hg⟩
  exact ⟨⟨σ, hσ⟩, rfl⟩

theorem mem_range_φ1_iff_d3 (k : d3Setting.ι.G0) :
    ((k : d3Setting.Yb) ∈ d3Setting.ι.φ1.range) ↔ d3ToAut k ∈ autStab d4H := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [d3ToAut, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem mem_range_φ2_iff_d3 (k : d3Setting.ι.G0) :
    ((k : d3Setting.Yb) ∈ d3Setting.ι.φ2.range) ↔ d3ToAut k ∈ autStab d4N := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [d3ToAut, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem mem_d3NN_iff (k : d3Setting.ι.G0) :
    k ∈ d3Setting.N ↔ d3ToAut k ∈ (MulAut.conj : D →* MulAut D).range := Iff.rfl

end Phi

end CFSG.Quasithin.D4Hex
