module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL

public section

namespace CFSG.StandardType.A8Coord

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem a8o_not_dvd_prod_pow (n : ℕ) (hn : n ≤ 8) :
    ¬ (73 : ℕ) ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  interval_cases n <;> decide

private theorem a8o_not_dvd_card_linearEquiv
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (h8 : Module.finrank (ZMod 2) M ≤ 8) :
    ¬ (73 : ℕ) ∣ Nat.card (M ≃ₗ[ZMod 2] M) := by
  rw [CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod
    (n := Module.finrank (ZMod 2) M) rfl]
  exact a8o_not_dvd_prod_pow (Module.finrank (ZMod 2) M) h8

private theorem a8o_linearEquiv_eq_one_of_finrank_le_eight
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (h8 : Module.finrank (ZMod 2) M ≤ 8) (g : M ≃ₗ[ZMod 2] M) (hg : g ^ 73 = 1) : g = 1 := by
  have hdvd73 : orderOf g ∣ 73 := orderOf_dvd_of_pow_eq_one hg
  have hdvd : orderOf g ∣ Nat.card (M ≃ₗ[ZMod 2] M) := orderOf_dvd_natCard g
  have hnot := a8o_not_dvd_card_linearEquiv (M := M) h8
  have hord : orderOf g = 1 := by
    rcases (by norm_num : Nat.Prime 73).eq_one_or_self_of_dvd (orderOf g) hdvd73 with h | h
    · exact h
    · exact absurd (h ▸ hdvd) hnot
  exact orderOf_eq_one_iff.mp hord

private theorem a8o_zeta_pow_val_eq_one_iff (a : ZMod 7) :
    ggSL9Zeta ^ a.val = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hdvd : 7 ∣ a.val := by
      have h := orderOf_dvd_of_pow_eq_one h
      rwa [orderOf_ggSL9Zeta] at h
    have hlt : a.val < 7 := ZMod.val_lt a
    exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
  · intro ha
    rw [ha, ZMod.val_zero, pow_zero]

private theorem a8o_coord_fixed_iff (a : ZMod 7) (x : GaloisField 2 3) :
    ((ggSL9Zeta ^ a.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * x = x ↔ a = 0 ∨ x = 0 := by
  constructor
  · intro h
    have h' : (((ggSL9Zeta ^ a.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) - 1) * x = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.mp h' with h1 | h2
    · left
      exact (a8o_zeta_pow_val_eq_one_iff a).mp (Units.val_eq_one.mp (sub_eq_zero.mp h1))
    · right
      exact h2
  · rintro (rfl | rfl)
    · rw [ZMod.val_zero, pow_zero, Units.val_one, one_mul]
    · rw [mul_zero]

private noncomputable def a8o_V0 (f : Fin 3 → ZMod 7) : Submodule (ZMod 2) GGSL9V :=
  LinearMap.ker (((ggSL9TorusCoord (Multiplicative.ofAdd f) : GGSL9V →ₗ[ZMod 2] GGSL9V)) - 1)

private theorem a8o_mem_V0_iff_fixed (f : Fin 3 → ZMod 7) (v : GGSL9V) :
    v ∈ a8o_V0 f ↔ ggSL9TorusCoord (Multiplicative.ofAdd f) v = v := by
  rw [a8o_V0, LinearMap.mem_ker]
  change (ggSL9TorusCoord (Multiplicative.ofAdd f) : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v = 0 ↔ _
  rw [sub_eq_zero]
  rfl

private theorem a8o_mem_V0_iff (f : Fin 3 → ZMod 7) (v : GGSL9V) :
    v ∈ a8o_V0 f ↔ ∀ j : Fin 3, f j ≠ 0 → v j = 0 := by
  rw [a8o_mem_V0_iff_fixed]
  constructor
  · intro hv j hj
    have h2 : ((ggSL9Zeta ^ (f j).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * v j = v j := by
      have h := congrFun hv j
      rwa [ggSL9TorusCoord_apply] at h
    rcases (a8o_coord_fixed_iff (f j) (v j)).mp h2 with h3 | h3
    · exact absurd h3 hj
    · exact h3
  · intro hv
    funext j
    rw [ggSL9TorusCoord_apply]
    by_cases hj : f j = 0
    · rw [hj, ZMod.val_zero, pow_zero, Units.val_one, one_mul]
    · rw [hv j hj, mul_zero]

private theorem a8o_torusCoord_ne_one {f : Fin 3 → ZMod 7} (hf : f ≠ 0) :
    ggSL9TorusCoord (Multiplicative.ofAdd f) ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hf
  have h1 : ((ggSL9Zeta ^ (f j).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) = 1 := by
    have h2 := congrFun (congrArg (fun (g : GGSL9V ≃ₗ[ZMod 2] GGSL9V) =>
      g (Pi.single j (1 : GaloisField 2 3))) h) j
    simpa [ggSL9TorusCoord_apply] using h2
  exact hj ((a8o_zeta_pow_val_eq_one_iff (f j)).mp (Units.val_eq_one.mp h1))

private theorem a8o_V0_ne_top {f : Fin 3 → ZMod 7} (hf : f ≠ 0) : a8o_V0 f ≠ ⊤ := by
  intro h
  exact a8o_torusCoord_ne_one hf (LinearEquiv.ext fun v =>
    (a8o_mem_V0_iff_fixed f v).mp (by rw [h]; trivial))

private theorem a8o_V0_ne_bot {f : Fin 3 → ZMod 7} {i : Fin 3} (hi : f i = 0) :
    a8o_V0 f ≠ ⊥ := by
  intro h
  let e : GGSL9V := Pi.single i (1 : GaloisField 2 3)
  have hmem : e ∈ a8o_V0 f := by
    rw [a8o_mem_V0_iff]
    intro j hj
    have hji : j ≠ i := fun hji => hj (by rw [hji]; exact hi)
    show e j = 0
    simp [e, Pi.single_eq_of_ne hji]
  rw [h] at hmem
  have hzero : e = 0 := by simpa using hmem
  have h1 : (1 : GaloisField 2 3) = 0 := by simpa [e] using congrFun hzero i
  exact one_ne_zero h1

private theorem a8o_V0_map_eq {f : Fin 3 → ZMod 7} {w : GGSL9V ≃ₗ[ZMod 2] GGSL9V}
    (hc : w * ggSL9TorusCoord (Multiplicative.ofAdd f) =
      ggSL9TorusCoord (Multiplicative.ofAdd f) * w) :
    (a8o_V0 f).map (w : GGSL9V →ₗ[ZMod 2] GGSL9V) = a8o_V0 f := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine (a8o_mem_V0_iff_fixed f (w v)).mpr ?_
    have hv' : ggSL9TorusCoord (Multiplicative.ofAdd f) v = v :=
      (a8o_mem_V0_iff_fixed f v).mp hv
    have hcomm : w (ggSL9TorusCoord (Multiplicative.ofAdd f) v) =
        ggSL9TorusCoord (Multiplicative.ofAdd f) (w v) := by
      have h := congrArg (fun (g : GGSL9V ≃ₗ[ZMod 2] GGSL9V) => g v) hc
      simpa [LinearEquiv.mul_apply] using h
    rw [← hcomm, hv']
  · intro v hv
    refine ⟨w.symm v, ?_, by simp⟩
    refine (a8o_mem_V0_iff_fixed f (w.symm v)).mpr ?_
    have hv' : ggSL9TorusCoord (Multiplicative.ofAdd f) v = v :=
      (a8o_mem_V0_iff_fixed f v).mp hv
    apply w.injective
    have hcomm : w (ggSL9TorusCoord (Multiplicative.ofAdd f) (w.symm v)) =
        ggSL9TorusCoord (Multiplicative.ofAdd f) (w (w.symm v)) := by
      have h := congrArg (fun (g : GGSL9V ≃ₗ[ZMod 2] GGSL9V) => g (w.symm v)) hc
      simpa [LinearEquiv.mul_apply] using h
    rw [hcomm, LinearEquiv.apply_symm_apply, hv']

private theorem a8o_V0_finrank_le {f : Fin 3 → ZMod 7} (hf : f ≠ 0) :
    Module.finrank (ZMod 2) (a8o_V0 f) ≤ 8 := by
  have hlt : Module.finrank (ZMod 2) (a8o_V0 f) < Module.finrank (ZMod 2) GGSL9V :=
    Submodule.finrank_lt (a8o_V0_ne_top hf)
  rw [finrank_ggSL9V] at hlt
  omega

private theorem a8o_quotient_finrank_le {f : Fin 3 → ZMod 7} {i : Fin 3} (hi : f i = 0) :
    Module.finrank (ZMod 2) (GGSL9V ⧸ a8o_V0 f) ≤ 8 := by
  have h1 : 1 ≤ Module.finrank (ZMod 2) (a8o_V0 f) :=
    Submodule.one_le_finrank_iff.mpr (a8o_V0_ne_bot hi)
  have h2 := Submodule.finrank_quotient_add_finrank (a8o_V0 f)
  rw [finrank_ggSL9V] at h2
  omega

theorem ggSL9_torusCoord_ne_zero_of_order73 {f : Fin 3 → ZMod 7} (hf : f ≠ 0)
    {w : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hw : orderOf w = 73)
    (hc : w * ggSL9TorusCoord (Multiplicative.ofAdd f) =
      ggSL9TorusCoord (Multiplicative.ofAdd f) * w) :
    ∀ i : Fin 3, f i ≠ 0 := by
  intro i0 hi0
  have hmap := a8o_V0_map_eq hc
  let w₀ : ↥(a8o_V0 f) ≃ₗ[ZMod 2] ↥(a8o_V0 f) :=
    LinearEquiv.ofSubmodules w (a8o_V0 f) (a8o_V0 f) hmap
  have hw₀app : ∀ x : ↥(a8o_V0 f), ((w₀ x : ↥(a8o_V0 f)) : GGSL9V) = w (x : GGSL9V) :=
    fun _ => rfl
  have hw73 : w ^ 73 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw₀73 : w₀ ^ 73 = 1 := by
    have hpow : ∀ n : ℕ, ∀ x : ↥(a8o_V0 f),
        (((w₀ ^ n) x : ↥(a8o_V0 f)) : GGSL9V) = (w ^ n) (x : GGSL9V) := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
          intro x
          rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hw₀app, ih]
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [hpow 73 x, hw73]
    rfl
  have hw₀1 : w₀ = 1 :=
    a8o_linearEquiv_eq_one_of_finrank_le_eight (a8o_V0_finrank_le hf) w₀ hw₀73
  let wbar := Submodule.Quotient.equiv (a8o_V0 f) (a8o_V0 f) w hmap
  have hwbar_apply : ∀ y : GGSL9V,
      wbar (Submodule.Quotient.mk (p := a8o_V0 f) y) =
        Submodule.Quotient.mk ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) y) := by
    intro y
    change Submodule.Quotient.equiv (a8o_V0 f) (a8o_V0 f) w hmap
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) y)
    rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  have hwbar73 : wbar ^ 73 = 1 := by
    apply LinearEquiv.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
        have hpow : ∀ n : ℕ, (wbar ^ n) (Submodule.Quotient.mk (p := a8o_V0 f) x) =
            Submodule.Quotient.mk ((w ^ n) x) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
              rw [pow_succ', LinearEquiv.mul_apply, ih, hwbar_apply,
                pow_succ', LinearEquiv.mul_apply]
              rfl
        rw [hpow 73, hw73]
        rfl
  have hwbar1 : wbar = 1 :=
    a8o_linearEquiv_eq_one_of_finrank_le_eight (a8o_quotient_finrank_le hi0) wbar hwbar73
  have hkill : ∀ x : ↥(a8o_V0 f),
      (w : GGSL9V →ₗ[ZMod 2] GGSL9V) (x : GGSL9V) = (x : GGSL9V) := by
    intro x
    have hx : w₀ x = x := by rw [hw₀1]; rfl
    have h := congrArg (fun y : ↥(a8o_V0 f) => (y : GGSL9V)) hx
    rwa [hw₀app x] at h
  have hmaps : ∀ v : GGSL9V,
      (w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v ∈ a8o_V0 f := by
    intro v
    have h : wbar (Submodule.Quotient.mk (p := a8o_V0 f) v) =
        Submodule.Quotient.mk (p := a8o_V0 f) v := by
      rw [hwbar1]
      rfl
    rw [hwbar_apply v] at h
    exact (Submodule.Quotient.eq (a8o_V0 f)).mp h
  have hw2 : w ^ 2 = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [pow_two, LinearEquiv.mul_apply]
    change (w : GGSL9V →ₗ[ZMod 2] GGSL9V) ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v) = v
    have hv : (w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v ∈ a8o_V0 f := hmaps v
    have h1 : (w : GGSL9V →ₗ[ZMod 2] GGSL9V)
        ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v) =
        (w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v := hkill ⟨_, hv⟩
    rw [map_sub] at h1
    have key : (w : GGSL9V →ₗ[ZMod 2] GGSL9V)
          ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v) - v =
        ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v)
          + ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v) := by
      calc (w : GGSL9V →ₗ[ZMod 2] GGSL9V) ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v) - v
          = ((w : GGSL9V →ₗ[ZMod 2] GGSL9V)
                ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v)
              - (w : GGSL9V →ₗ[ZMod 2] GGSL9V) v)
            + ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v) := by abel
        _ = ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v)
            + ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v - v) := by rw [h1]
    have key2 : (w : GGSL9V →ₗ[ZMod 2] GGSL9V)
        ((w : GGSL9V →ₗ[ZMod 2] GGSL9V) v) - v = 0 := by
      rw [key, CharTwo.add_self_eq_zero]
    exact sub_eq_zero.mp key2
  exact (by norm_num : ¬ (73 : ℕ) ∣ 2) (by rw [← hw]; exact orderOf_dvd_of_pow_eq_one hw2)

theorem exists_orderOf_seventythree_lowerBlock {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G) (hφ : Function.Injective φ) :
    ∃ w ∈ (φ.comp (slLowerBlockHom 3 (GaloisField 2 3))).range, orderOf w = 73 := by
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  have h73 : 73 ∣ Nat.card (SpecialLinearGroup (Fin 3) (GaloisField 2 3)) := by
    rw [Matrix.card_SL_field (𝔽 := GaloisField 2 3) 3]
    have hq : Fintype.card (GaloisField 2 3) = 8 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
      norm_num
    rw [hq]
    norm_num [Fin.prod_univ_three]
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
    (G := SpecialLinearGroup (Fin 3) (GaloisField 2 3)) 73 h73
  refine ⟨φ (slLowerBlockHom 3 (GaloisField 2 3) s),
    MonoidHom.mem_range.mpr ⟨s, rfl⟩, ?_⟩
  exact (orderOf_injective (φ.comp (slLowerBlockHom 3 (GaloisField 2 3)))
    (hφ.comp slLowerBlockHom_injective) s).trans hs

end CFSG.StandardType.A8Coord

end
