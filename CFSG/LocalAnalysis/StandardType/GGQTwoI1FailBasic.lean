module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2nP2_coe_pow {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] V) (n : ℕ) :
    ((e ^ n : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) = (e : V →ₗ[ZMod 3] V) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, LinearEquiv.coe_toLinearMap_mul, ih, pow_succ]

private lemma ggQ2nP2_cube {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (ν : V ≃ₗ[ZMod 3] V) (N : V →ₗ[ZMod 3] V) (Z : Submodule (ZMod 3) V)
    (h1 : ∀ v, ν v = v + N v)
    (hNmem : ∀ v, N v ∈ Z)
    (hNsq : ∀ z ∈ Z, N (N z) = 0) :
    ν ^ 3 = 1 := by
  have hcast : (ν : Module.End (ZMod 3) V) = 1 + N := by
    ext v
    rw [LinearMap.add_apply, Module.End.one_apply]
    exact h1 v
  have h3z : (3 : Module.End (ZMod 3) V) = 0 := by
    rw [show (3 : Module.End (ZMod 3) V) = ((3 : ℕ) : Module.End (ZMod 3) V) by
      exact Nat.cast_ofNat.symm]
    rw [← map_natCast (algebraMap (ZMod 3) (Module.End (ZMod 3) V)) 3]
    rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, map_zero]
  have hexp : (ν : Module.End (ZMod 3) V) ^ 3 = 1 + 3 * N + 3 * N ^ 2 + N ^ 3 := by
    rw [hcast]; noncomm_ring
  have hN3 : N ^ 3 = 0 := by
    ext v
    show N (N (N v)) = 0
    exact hNsq (N v) (hNmem v)
  have hEnd : (ν : Module.End (ZMod 3) V) ^ 3 = 1 := by
    rw [hexp]
    rw [show (3 : Module.End (ZMod 3) V) * N = 0 by rw [h3z, zero_mul]]
    rw [show (3 : Module.End (ZMod 3) V) * N ^ 2 = 0 by rw [h3z, zero_mul]]
    rw [hN3]; simp
  apply LinearEquiv.ext
  intro v
  change ((ν ^ 3 : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) v = v
  rw [ggQ2nP2_coe_pow ν 3]
  simpa using congrArg (fun f : Module.End (ZMod 3) V => f v) hEnd

private lemma ggQ2nP2_odd {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hK : ∀ x ∈ K, x ^ 3 = 1) : ¬ 2 ∣ Nat.card ↥K := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2
  have hx3 : orderOf x ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (hK ↑x x.2)
  rw [hx] at hx3
  omega

private lemma ggQ2nP2_functional {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (w u : V) (hu : u ∉ Submodule.span (ZMod 3) ({w} : Set V)) :
    ∃ lam : V →ₗ[ZMod 3] ZMod 3, lam w = 0 ∧ lam u = 1 := by
  obtain ⟨f, hfu, hker⟩ := Submodule.exists_le_ker_of_notMem
    (p := Submodule.span (ZMod 3) ({w} : Set V)) hu
  have hfw : f w = 0 := hker (Submodule.mem_span_singleton_self w)
  refine ⟨(f u)⁻¹ • f, ?_, ?_⟩
  · rw [LinearMap.smul_apply, hfw, smul_zero]
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfu]

private lemma ggQ2nP2_li {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (w u : V)
    (hw0 : w ≠ 0) (hu : u ∉ Submodule.span (ZMod 3) ({w} : Set V)) :
    LinearIndependent (ZMod 3) ![w, u] := by
  rw [LinearIndependent.pair_iff' hw0]
  intro a ha
  apply hu
  rw [Submodule.mem_span_singleton]
  exact ⟨a, ha⟩

private lemma ggQ2nP2_finrank_pair {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (w u : V)
    (hw0 : w ≠ 0) (hu : u ∉ Submodule.span (ZMod 3) ({w} : Set V)) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({w, u} : Set V)) = 2 := by
  have hli : LinearIndependent (ZMod 3) ![w, u] := ggQ2nP2_li w u hw0 hu
  have h := finrank_span_eq_card hli
  rw [show Set.range (fun i : Fin 2 => ![w, u] i) = ({w, u} : Set V) from by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩] at h
  simpa using h

private lemma ggQ2nP2_Zspan {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (Z : Submodule (ZMod 3) V) (w u : V) (hwZ : w ∈ Z) (huZ : u ∈ Z)
    (hw0 : w ≠ 0) (hu : u ∉ Submodule.span (ZMod 3) ({w} : Set V))
    (hZ2 : Module.finrank (ZMod 3) Z = 2) :
    Z = Submodule.span (ZMod 3) ({w, u} : Set V) := by
  have h : Submodule.span (ZMod 3) ({w, u} : Set V) = Z := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact hwZ
      · exact huZ
    · rw [ggQ2nP2_finrank_pair w u hw0 hu, hZ2]
  exact h.symm

private lemma ggQ2nP2_finite_le {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] :
    Finite (V ≃ₗ[ZMod 3] V) :=
  Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
    (fun e₁ e₂ h => LinearEquiv.ext (fun x => congrFun h x))

private lemma ggQ2nP2_case_two {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (Z F : Submodule (ZMod 3) V) (H : Subgroup (V ≃ₗ[ZMod 3] V))
    (hH : ∀ ν ∈ H, (∀ v, ν v - v ∈ Z) ∧ ∀ f ∈ F, ν f = f)
    (w : V) (hwZ : w ∈ Z) (hwF : w ∈ F) (hw0 : w ≠ 0)
    (u : V) (huZ : u ∈ Z) (hu_notmem : u ∉ Submodule.span (ZMod 3) ({w} : Set V))
    (hZ2 : Module.finrank (ZMod 3) Z = 2) :
    padicValNat 2 (Nat.card ↥H) ≤ 1 := by
  haveI : Finite (V ≃ₗ[ZMod 3] V) := ggQ2nP2_finite_le
  have hZspan : Z = Submodule.span (ZMod 3) ({w, u} : Set V) :=
    ggQ2nP2_Zspan Z w u hwZ huZ hw0 hu_notmem hZ2
  obtain ⟨lam, hlamw, hlamu⟩ := ggQ2nP2_functional w u hu_notmem
  have hνu_mem : ∀ ν : ↥H, ν.1 u ∈ Z := by
    intro ν
    have h := (hH ν.1 ν.2).1 u
    have h2 : ν.1 u = u + (ν.1 u - u) := by abel
    rw [h2]
    exact Z.add_mem huZ h
  have hνu_span : ∀ ν : ↥H, ν.1 u ∈ Submodule.span (ZMod 3) ({w, u} : Set V) := by
    intro ν
    rw [← hZspan]
    exact hνu_mem ν
  have hνu_notmem : ∀ ν : ↥H, ν.1 u ∉ Submodule.span (ZMod 3) ({w} : Set V) := by
    intro ν hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hwfix : ν.1 w = w := (hH ν.1 ν.2).2 w hwF
    have hwfixinv : ν.1.symm w = w := by
      have h := ν.1.symm_apply_apply w
      rw [hwfix] at h
      exact h
    have hu_eq : u = c • w := by
      calc u = ν.1.symm (ν.1 u) := (ν.1.symm_apply_apply u).symm
        _ = ν.1.symm (c • w) := by rw [← hc]
        _ = c • ν.1.symm w := by rw [map_smul]
        _ = c • w := by rw [hwfixinv]
    refine hu_notmem ?_
    rw [hu_eq]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)
  have hχ_ne_zero : ∀ ν : ↥H, lam (ν.1 u) ≠ 0 := by
    intro ν h0
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hνu_span ν)
    have hb : b = 0 := by
      have h := congrArg (fun x => lam x) hab
      simp only [map_add, map_smul, hlamw, hlamu, smul_zero, zero_add,
        smul_eq_mul, mul_one] at h
      rw [h0] at h
      simpa using h
    apply hνu_notmem ν
    rw [← hab, hb, zero_smul, add_zero]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w)
  let χ : ↥H →* (ZMod 3)ˣ :=
  { toFun := fun ν => Units.mk0 (lam (ν.1 u)) (hχ_ne_zero ν)
    map_one' := by
      apply Units.ext
      show lam ((1 : ↥H).1 u) = 1
      simpa using hlamu
    map_mul' := by
      intro ν₁ ν₂
      apply Units.ext
      show lam ((ν₁ * ν₂).1 u) = lam (ν₁.1 u) * lam (ν₂.1 u)
      obtain ⟨a₂, b₂, hab₂⟩ := Submodule.mem_span_pair.mp (hνu_span ν₂)
      have hν₁w : ν₁.1 w = w := (hH ν₁.1 ν₁.2).2 w hwF
      have hlam₂ : lam (ν₂.1 u) = b₂ := by
        have h := congrArg (fun x => lam x) hab₂
        simp only [map_add, map_smul, hlamw, hlamu, smul_zero, mul_zero,
          zero_add, smul_eq_mul, mul_one] at h
        exact h.symm
      have hLHS : lam ((ν₁ * ν₂).1 u) = b₂ * lam (ν₁.1 u) := by
        have hcomp : (ν₁ * ν₂).1 u = ν₁.1 (ν₂.1 u) := rfl
        rw [hcomp, ← hab₂]
        simp only [map_add, map_smul, hν₁w, hlamw, hlamu, smul_zero, mul_zero,
          zero_add, smul_eq_mul, mul_one]
      rw [hLHS, hlam₂]
      ring }
  have hker_cube : ∀ x ∈ χ.ker, x ^ 3 = 1 := by
    intro x hx
    have hx1 : χ x = 1 := MonoidHom.mem_ker.mp hx
    have hx2 : x.1 ^ 3 = 1 := by
      have hlam1 : lam (x.1 u) = 1 := by
        change (χ x : ZMod 3) = 1
        rw [hx1]
        rfl
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hνu_span x)
      have hb : b = 1 := by
        have h := congrArg (fun y => lam y) hab
        simp only [map_add, map_smul, hlamw, hlamu, smul_zero, zero_add,
          smul_eq_mul, mul_one] at h
        rw [hlam1] at h
        simpa using h
      have hNw : ((x.1 : V →ₗ[ZMod 3] V) - 1) w = 0 := by
        have hwx : (x.1 : V →ₗ[ZMod 3] V) w = w := (hH x.1 x.2).2 w hwF
        rw [LinearMap.sub_apply, Module.End.one_apply, hwx, sub_self]
      have hNu : ((x.1 : V →ₗ[ZMod 3] V) - 1) u = a • w := by
        have hx_u : (x.1 : V →ₗ[ZMod 3] V) u = a • w + b • u := hab.symm
        rw [LinearMap.sub_apply, Module.End.one_apply, hx_u, hb]
        simp
      refine ggQ2nP2_cube x.1 ((x.1 : V →ₗ[ZMod 3] V) - 1) Z ?_ ?_ ?_
      · intro v; simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
      · intro v; rw [LinearMap.sub_apply, Module.End.one_apply]; exact (hH x.1 x.2).1 v
      · intro z hz
        have hzspan : z ∈ Submodule.span (ZMod 3) ({w, u} : Set V) := by
          rw [← hZspan]; exact hz
        obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hzspan
        rw [← hpq]
        simp [map_add, map_smul, hNw, hNu]
    apply Subtype.ext
    simpa using hx2
  have hodd : ¬ 2 ∣ Nat.card ↥χ.ker := ggQ2nP2_odd χ.ker hker_cube
  have hcard : Nat.card ↥χ.ker * Nat.card ↥χ.range = Nat.card ↥H :=
    Subgroup.card_ker_mul_card_range χ
  have hKne : Nat.card ↥χ.ker ≠ 0 := by
    have hne : Nonempty ↥χ.ker := ⟨⟨(1 : ↥H), χ.ker.one_mem⟩⟩
    exact Nat.card_ne_zero.mpr ⟨hne, inferInstance⟩
  have hRne : Nat.card ↥χ.range ≠ 0 := by
    have hne : Nonempty ↥χ.range := ⟨⟨(1 : (ZMod 3)ˣ), χ.range.one_mem⟩⟩
    exact Nat.card_ne_zero.mpr ⟨hne, inferInstance⟩
  have h2units : Nat.card ((ZMod 3)ˣ) = 2 := by
    rw [Nat.card_eq_fintype_card]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    simpa using ZMod.card_units 3
  have hR_dvd : Nat.card ↥χ.range ∣ 2 := by
    have h := Subgroup.card_subgroup_dvd_card χ.range
    rwa [h2units] at h
  have hRval : padicValNat 2 (Nat.card ↥χ.range) ≤ 1 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (Nat.card ↥χ.range) hR_dvd with h | h
    · rw [h]; simp
    · rw [h]; norm_num
  rw [← hcard, padicValNat.mul hKne hRne, padicValNat.eq_zero_of_not_dvd hodd]
  omega

private lemma ggQ2nP2_case_one {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (Z F : Submodule (ZMod 3) V) (H : Subgroup (V ≃ₗ[ZMod 3] V))
    (hH : ∀ ν ∈ H, (∀ v, ν v - v ∈ Z) ∧ ∀ f ∈ F, ν f = f)
    (w : V) (hwZ : w ∈ Z) (hwF : w ∈ F) (hw0 : w ≠ 0)
    (hZ1 : Module.finrank (ZMod 3) Z = 1) :
    padicValNat 2 (Nat.card ↥H) ≤ 1 := by
  haveI : Finite (V ≃ₗ[ZMod 3] V) := ggQ2nP2_finite_le
  have hZspan : Z = Submodule.span (ZMod 3) ({w} : Set V) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hZ1 hwZ hw0
  have hcube : ∀ ν ∈ H, ν ^ 3 = 1 := by
    intro ν hν
    have h1 : ∀ v, ν v = v + ((ν : V →ₗ[ZMod 3] V) - 1) v := by
      intro v; simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
    have hNmem : ∀ v, ((ν : V →ₗ[ZMod 3] V) - 1) v ∈ Z := by
      intro v; rw [LinearMap.sub_apply, Module.End.one_apply]; exact (hH ν hν).1 v
    have hNsq : ∀ z ∈ Z, ((ν : V →ₗ[ZMod 3] V) - 1) (((ν : V →ₗ[ZMod 3] V) - 1) z) = 0 := by
      intro z hz
      have hz' : z ∈ Submodule.span (ZMod 3) ({w} : Set V) := by rw [← hZspan]; exact hz
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz'
      have hwfix : ν w = w := (hH ν hν).2 w hwF
      have hwfix' : (ν : V →ₗ[ZMod 3] V) w = w := (hH ν hν).2 w hwF
      have hNw : ((ν : V →ₗ[ZMod 3] V) - 1) w = 0 := by
        rw [LinearMap.sub_apply, Module.End.one_apply, hwfix', sub_self]
      rw [← hc]
      simp [map_smul, hNw]
    exact ggQ2nP2_cube ν ((ν : V →ₗ[ZMod 3] V) - 1) Z h1 hNmem hNsq
  have hodd : ¬ 2 ∣ Nat.card ↥H := ggQ2nP2_odd H hcube
  rw [padicValNat.eq_zero_of_not_dvd hodd]
  exact Nat.zero_le 1

theorem ggQ2n_P_two_part {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (Z F : Submodule (ZMod 3) V) (hZF : Z ⊓ F ≠ ⊥) (hZ : Module.finrank (ZMod 3) Z ≤ 2)
    (H : Subgroup (V ≃ₗ[ZMod 3] V))
    (hH : ∀ ν ∈ H, (∀ v, ν v - v ∈ Z) ∧ ∀ f ∈ F, ν f = f) :
    padicValNat 2 (Nat.card ↥H) ≤ 1 := by
  obtain ⟨w, hwZF, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZF
  have hwZ : w ∈ Z := hwZF.1
  have hwF : w ∈ F := hwZF.2
  have hspan : ZMod 3 ∙ w ≤ Z := by
    rw [Submodule.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hwZ
  have hfin1 : 1 ≤ Module.finrank (ZMod 3) Z := by
    have hmono := Submodule.finrank_mono hspan
    rwa [finrank_span_singleton hw0] at hmono
  have hcases : Module.finrank (ZMod 3) Z = 1 ∨ Module.finrank (ZMod 3) Z = 2 := by omega
  rcases hcases with h1 | h2
  · exact ggQ2nP2_case_one Z F H hH w hwZ hwF hw0 h1
  · have hnotsub : ¬ (Z : Set V) ⊆ (ZMod 3 ∙ w : Set V) := by
      intro hle
      have hmono := Submodule.finrank_mono hle
      rw [finrank_span_singleton hw0] at hmono
      omega
    obtain ⟨u, huZ, hu_notmem⟩ := Set.not_subset.mp hnotsub
    exact ggQ2nP2_case_two Z F H hH w hwZ hwF hw0 u huZ hu_notmem h2

end CFSG.StandardType

end
