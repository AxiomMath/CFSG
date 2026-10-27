module

public import CFSG.Quasithin.Background.SmithB42LnL5Curtis
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis

namespace S125Six

theorem finrank_ne_six
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G5 V}
    (hρ : IsSimpleRep ρ) [Finite V] : Module.finrank (ZMod 2) V ≠ 6 := by
  intro h6
  rcases B42Ln.l5Model_of_finrank_le hρ (by omega) with htriv | ⟨-, β, -⟩ | ⟨-, β, -⟩
  · have := hρ.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    rcases hρ.2 (Submodule.span (ZMod 2) {v}) (fun g w hw => by rw [htriv]; exact hw) with
      h | h
    · exact hv (Submodule.span_singleton_eq_bot.mp h)
    · have h1 := finrank_span_singleton (K := ZMod 2) hv
      rw [h, finrank_top, h6] at h1
      omega
  · have h1 := β.finrank_eq
    rw [h6, Module.finrank_fin_fun] at h1
    omega
  · have h1 := β.finrank_eq
    rw [h6, Module.finrank_fin_fun] at h1
    omega

theorem false_of_mulEquiv_sl5
    {V : Type*} [CommGroup V] [Finite V] (h2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 6)
    {H : Subgroup (MulAut V)} (φ : ↥H ≃* G5)
    (hirr : ∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    False := by
  let _ : Module (ZMod 2) (Additive V) := Orbit.zmod2Module h2
  have : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  have hsimple := Orbit.isSimpleRep_repOfIso φ hirr
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have hfin : Module.finrank (ZMod 2) (Additive V) = 6 := by
    have : Fintype (Additive V) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    change Nat.card V = _ at h
    rw [hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  exact finrank_ne_six hsimple hfin

theorem false_of_orderOf_eleven {V : Type*} [Group V] [Finite V] (hcard : Nat.card V = 2 ^ 6)
    {a : MulAut V} (ha : orderOf a = 11) : False := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set P : Subgroup (MulAut V) := Subgroup.zpowers a with hP
  have hP11 : IsPGroup 11 ↥P := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha, pow_one]
  let W : Subgroup V :=
    { carrier := MulAction.fixedPoints ↥P V
      one_mem' := fun g => map_one ((g : ↥P) : MulAut V)
      mul_mem' := fun {x y} hx hy g => by
        change ((g : ↥P) : MulAut V) (x * y) = x * y
        rw [map_mul]
        exact congrArg₂ (· * ·) (hx g) (hy g)
      inv_mem' := fun {x} hx g => by
        change ((g : ↥P) : MulAut V) x⁻¹ = x⁻¹
        rw [map_inv]
        exact congrArg (·⁻¹) (hx g) }
  have hmod := hP11.card_modEq_card_fixedPoints V
  have hW : Nat.card ↥W = Nat.card (MulAction.fixedPoints ↥P V) := rfl
  obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hcard ▸ Subgroup.card_subgroup_dvd_card W)
  rw [← hW, hk, hcard] at hmod
  have hk' : k = 6 := by
    have h : 2 ^ 6 % 11 = 2 ^ k % 11 := hmod
    interval_cases k <;> first | rfl | norm_num at h
  subst hk'
  have htop : W = ⊤ := Subgroup.eq_top_of_card_eq W (hk.trans hcard.symm)
  have ha1 : a = 1 := by
    ext v
    have hv : v ∈ W := htop ▸ Subgroup.mem_top v
    exact hv ⟨a, Subgroup.mem_zpowers a⟩
  rw [ha1, orderOf_one] at ha
  omega

end S125Six

end CFSG.Quasithin.H13
