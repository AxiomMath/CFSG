module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Data
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Quad
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Trans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.ClassicalGroups.Symplectic
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.JonesParshall
  CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem s16sp_quad_transfer {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (θ : W ≃* Multiplicative M)
    (ρM : Representation (ZMod 2) (bilinIsometryGroup (spForm 3 (ZMod 2))) M)
    (q : M →ₗ[ZMod 2] (Fin 3 ⊕ Fin 3 → ZMod 2))
    (π : bilinIsometryGroup (spForm 3 (ZMod 2)) →* ↥H) (hπ : Function.Surjective π)
    (hq : Function.Surjective q)
    (hθ : ∀ (g : bilinIsometryGroup (spForm 3 (ZMod 2))) (w : W),
      θ ((π g : MulAut W) w) = Multiplicative.ofAdd (ρM g (Multiplicative.toAdd (θ w))))
    (hker : ∀ w : W, q (Multiplicative.toAdd (θ w)) = 0 ↔ w ∈ Z)
    (Q : M → ZMod 2)
    (hQ : ∀ m m', Q (m + m') = Q m + Q m' + spForm 3 (ZMod 2) (q m) (q m'))
    (hQinv : ∀ g m, Q (ρM g m) = Q m) {z : W} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hQz : Q (Multiplicative.toAdd (θ z)) = 1) (hZ : ∀ z' ∈ Z, z' = 1 ∨ z' = z) :
    ∃ Q' : W → ZMod 2, IsQuadF2 Q' ∧ QuadInvariant Q' H ∧
      (∀ x : W, (∀ y : W, polarQ Q' x y = 0) ↔ x ∈ Z) ∧
      (∀ z' : W, z' ∈ Z → z' ≠ 1 → Q' z' ≠ 0) := by
  classical
  let Q' : W → ZMod 2 := fun w => Q (Multiplicative.toAdd (θ w))
  have hQ'add : ∀ w w' : W, Q' (w * w') =
      Q' w + Q' w' + spForm 3 (ZMod 2) (q (Multiplicative.toAdd (θ w)))
        (q (Multiplicative.toAdd (θ w'))) := by
    intro w w'
    have hθw : Multiplicative.toAdd (θ (w * w')) =
        Multiplicative.toAdd (θ w) + Multiplicative.toAdd (θ w') := by
      rw [map_mul, toAdd_mul]
    change Q (Multiplicative.toAdd (θ (w * w'))) = _
    rw [hθw, hQ]
  have hpol : ∀ w w' : W, polarQ Q' w w' =
      spForm 3 (ZMod 2) (q (Multiplicative.toAdd (θ w)))
        (q (Multiplicative.toAdd (θ w'))) := by
    intro w w'
    rw [polarQ, hQ'add]
    ring
  have hquad : IsQuadF2 Q' := by
    refine ⟨?_, ?_⟩
    · intro x y z
      have hxy : q (Multiplicative.toAdd (θ (x * y))) =
          q (Multiplicative.toAdd (θ x)) + q (Multiplicative.toAdd (θ y)) := by
        rw [map_mul, toAdd_mul, map_add]
      rw [hpol, hpol, hpol, hxy]
      simp only [map_add, LinearMap.add_apply]
    · intro x y z
      have hyz : q (Multiplicative.toAdd (θ (y * z))) =
          q (Multiplicative.toAdd (θ y)) + q (Multiplicative.toAdd (θ z)) := by
        rw [map_mul, toAdd_mul, map_add]
      rw [hpol, hpol, hpol, hyz]
      simp only [map_add]
  have hinv : QuadInvariant Q' H := by
    intro h hh x
    obtain ⟨g, hg⟩ := hπ ⟨h, hh⟩
    change Q (Multiplicative.toAdd (θ (h x))) = Q (Multiplicative.toAdd (θ x))
    have hx : h x = (π g : MulAut W) x := by rw [hg]
    rw [hx, hθ, toAdd_ofAdd]
    exact hQinv g _
  have hrad : ∀ x : W, (∀ y : W, polarQ Q' x y = 0) ↔ x ∈ Z := by
    intro x
    rw [← hker x]
    constructor
    · intro h
      refine (spForm_nondegenerate (m := 3) (K := ZMod 2)).1 _ ?_
      intro e
      obtain ⟨m, hm⟩ := hq e
      have hy : q (Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd m)))) = e := by
        rw [← hm]
        exact congrArg q (by simp)
      have h0 := h (θ.symm (Multiplicative.ofAdd m))
      rwa [hpol, hy] at h0
    · intro hq0 y
      rw [hpol, hq0]
      simp
  have hQ'z : ∀ z' : W, z' ∈ Z → z' ≠ 1 → Q' z' ≠ 0 := by
    intro z' hz' hz1'
    rcases hZ z' hz' with h | h
    · exact (hz1' h).elim
    · rw [h]
      change Q (Multiplicative.toAdd (θ z)) ≠ 0
      rw [hQz]
      exact one_ne_zero
  exact ⟨Q', hquad, hinv, hrad, hQ'z⟩

theorem s16sp_cover_dichotomy {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hreal : (FFModel.nat (StatedSp 3 K)).Realizes H ⊤ Z) :
    Z = ⊥ ∨ (Nat.card Z = 2 ∧
      ∃ Q : W → ZMod 2, IsQuadF2 Q ∧ QuadInvariant Q H ∧
        (∀ x : W, (∀ y : W, polarQ Q x y = 0) ↔ x ∈ Z) ∧
        (∀ z : W, z ∈ Z → z ≠ 1 → Q z ≠ 0)) := by
  have hreal2 := s16sp_realizes_zmod2 hK hreal
  obtain ⟨M, _, _, _, θ, ρM, q, π, hπ, hq, hqρ, hZc, hperf, hθ, hker⟩ :=
    s16sp_module_data hW2 hZ hcomm hreal2
  haveI : Finite (bilinIsometryGroup (spForm 3 (ZMod 2))) :=
    Finite.of_equiv _ (spEquiv (m := 3) (K := ZMod 2)).toEquiv
  have hfin : Module.finrank (ZMod 2) (LinearMap.ker q) ≤ 1 :=
    (finrank_ker_le_finrank_H1_dual ρM (binarySymplecticNatural (spForm 3 (ZMod 2))) q hq hqρ
      hZc hperf).trans s16sp_finrank_H1_le_one
  have hkerZ : Nat.card Z = Nat.card (LinearMap.ker q) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨Multiplicative.toAdd (θ z), (hker z).mpr z.2⟩
        invFun := fun m => ⟨θ.symm (Multiplicative.ofAdd (m : M)), ?_⟩
        left_inv := fun z => ?_
        right_inv := fun m => ?_ }
    · apply (hker _).mp
      simpa using m.2
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      simp
  have hcardZ : Nat.card Z ≤ 2 := by
    rw [hkerZ, ← FiniteField.pow_finrank_eq_natCard 2 ↥(LinearMap.ker q)]
    calc 2 ^ Module.finrank (ZMod 2) (LinearMap.ker q) ≤ 2 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) hfin
      _ = 2 := by norm_num
  by_cases hZ1 : Z = ⊥
  · exact Or.inl hZ1
  right
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZ1 ((Subgroup.eq_bot_iff_forall Z).mpr hcon)
  have hcard2 : Nat.card Z = 2 := by
    refine le_antisymm hcardZ ?_
    have : 1 < Nat.card Z := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      refine ⟨fun h0 => ?_, fun h1 => hz1 ?_⟩
      · haveI : Nonempty ↥Z := ⟨⟨z, hzZ⟩⟩
        exact (Nat.card_pos.ne') h0
      · haveI : Subsingleton ↥Z := (Nat.card_eq_one_iff_unique.mp h1).1
        exact Subtype.ext_iff.mp (Subsingleton.elim (⟨z, hzZ⟩ : Z) 1)
    omega
  have hZeq : ∀ z' ∈ Z, z' = 1 ∨ z' = z := by
    intro z' hz'
    obtain ⟨w, -, hwuniq⟩ :=
      (Nat.card_eq_two_iff' (⟨1, one_mem Z⟩ : Z)).mp hcard2
    rcases eq_or_ne (⟨z', hz'⟩ : Z) ⟨1, one_mem Z⟩ with h1 | h1
    · exact Or.inl (Subtype.ext_iff.mp h1)
    · refine Or.inr ?_
      have hz_ne : (⟨z, hzZ⟩ : Z) ≠ ⟨1, one_mem Z⟩ := fun h =>
        hz1 (Subtype.ext_iff.mp h)
      have hEq : (⟨z', hz'⟩ : Z) = (⟨z, hzZ⟩ : Z) :=
        (hwuniq (⟨z', hz'⟩ : Z) h1).trans (hwuniq (⟨z, hzZ⟩ : Z) hz_ne).symm
      exact congrArg Subtype.val hEq
  have hz0 : Multiplicative.toAdd (θ z) ≠ 0 := by
    intro h
    apply hz1
    apply θ.injective
    simpa using h
  obtain ⟨Q, hQ, hQinv, hQz⟩ := s16sp_exists_invariant_quad ρM
    (binarySymplecticNatural (spForm 3 (ZMod 2))) q hq hqρ hZc hperf
    (z := Multiplicative.toAdd (θ z)) ((hker z).mpr hzZ) hz0 s16spQ0 (spForm 3 (ZMod 2))
    s16spQ0_add (fun g x y => b_sE g x y) s16sp_no_invariant s16sp_finrank_H1_le_one
  exact ⟨hcard2, s16sp_quad_transfer θ ρM q π hπ hq hθ hker Q hQ hQinv hzZ hz1 hQz hZeq⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
