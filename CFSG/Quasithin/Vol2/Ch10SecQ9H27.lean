module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H26
public import CFSG.Quasithin.Vol2.Ch10SecQ9H13
public import CFSG.Quasithin.Vol2.Ch10SecQ9H24

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

variable {G H : Type*} [Group G] [Group H]

theorem inf_centralizer_ne_bot' [Finite H] {X S : Subgroup H} (hS : IsPGroup 2 S)
    (hS32 : 32 ≤ Nat.card S) (hSX : S ≤ Subgroup.normalizer (X : Set H))
    (e : ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    S ⊓ Subgroup.centralizer (X : Set H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have h1 : Nat.card (MulAut ↥X) ≤ 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact card_mulAut_SL3_le
  set S' := S.subgroupOf (Subgroup.normalizer (X : Set H))
  set φ := X.normalizerMonoidHom.comp S'.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h2 : (s : ↥(Subgroup.normalizer (X : Set H))) ∈ X.normalizerMonoidHom.ker := hs
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    have h3 : ((s : ↥(Subgroup.normalizer (X : Set H))) : H) ∈
        S ⊓ Subgroup.centralizer (X : Set H) := ⟨Subgroup.mem_subgroupOf.mp s.2, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact Subtype.ext (Subtype.ext h3)
  have hS' : Nat.card S' = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  have h32 : 32 ∣ Nat.card S := by
    obtain ⟨a, ha⟩ := hS.exists_card_eq
    rw [ha] at hS32 ⊢
    have ha5 : 5 ≤ a := by
      by_contra hc
      have : 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (show (32 : ℕ) = 2 ^ 5 by norm_num) ▸ pow_dvd_pow 2 ha5
  have h32' : 32 ∣ Nat.card (MulAut ↥X) := by
    have h := Subgroup.card_subgroup_dvd_card (φ.range)
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hS'] at h
    exact h32.trans h
  have hc : Subgroup.center ↥X = ⊥ := by
    have h := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [center_SL_eq_bot 3, Subgroup.card_bot] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have hinj : Function.Injective (MulAut.conj : ↥X →* MulAut ↥X) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center ↥X := Subgroup.mem_center_iff.mpr fun y => by
      have := congrArg (fun α : MulAut ↥X => α y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    rw [hc, Subgroup.mem_bot] at hxc
    exact hxc
  have hX : Nat.card ↥X = 168 := by
    rw [Nat.card_congr e.toEquiv, card_SL_three_two]
  have h168 : 168 ∣ Nat.card (MulAut ↥X) := by
    have h := Subgroup.card_subgroup_dvd_card ((MulAut.conj : ↥X →* MulAut ↥X).range)
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hX] at h
  have hlcm : 672 ∣ Nat.card (MulAut ↥X) := by
    have := Nat.lcm_dvd h32' h168
    rwa [show Nat.lcm 32 168 = 672 by norm_num] at this
  have hpos : 0 < Nat.card (MulAut ↥X) := Nat.card_pos
  have := Nat.le_of_dvd hpos hlcm
  omega

theorem exists_twoSubgroup [Finite G] [Finite H] {X : Subgroup G}
    (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (φ : ↥X →* H)
    (hφ : ∀ x, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) {U : Subgroup H} (hU : IsPGroup 2 U)
    (hU32 : 32 ≤ Nat.card U) (hU1 : U ≤ Subgroup.normalizer (φ.range : Set H))
    (hU2 : U ≤ Subgroup.normalizer (((CFSG.pCore 2 ↥X).map φ : Subgroup H) : Set H)) :
    ∃ A : Subgroup H, IsPGroup 2 A ∧ A ≠ ⊥ ∧ φ.range ≤ Subgroup.normalizer (A : Set H) ∧
      U ≤ Subgroup.normalizer (A : Set H) := by
  by_cases h : (CFSG.pCore 2 ↥X).map φ = ⊥
  · have hker : φ.ker = CFSG.pCore 2 ↥X := by
      refine le_antisymm (ker_le_pCore φ hφ) fun x hx => ?_
      have : φ x ∈ (CFSG.pCore 2 ↥X).map φ := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    have e' : ↥φ.range ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
      (QuotientGroup.quotientKerEquivRange φ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans e)
    obtain ⟨h1, h2⟩ := le_normalizer_inf_centralizer hU1
    exact ⟨U ⊓ Subgroup.centralizer (φ.range : Set H), hU.to_le inf_le_left,
      inf_centralizer_ne_bot' hU hU32 hU1 e', h1, h2⟩
  · refine ⟨(CFSG.pCore 2 ↥X).map φ, CFSG.pCore_isPGroup.map φ, h, ?_, hU2⟩
    refine le_normalizer_of_conj ?_
    rintro _ ⟨x, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨x * q * x⁻¹, CFSG.pCore_normal.conj_mem q hq x, by rw [map_mul, map_mul, map_inv]⟩

theorem exists_invStd {n : ℕ} {X A : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))}
    (hn : 1 ≤ n) (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥)
    (hXA : X ≤ Subgroup.normalizer (A : Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))))
    (htA : ∀ (i j : Fin n) (h : (i : ℕ) + 1 = j), trvE i j (by intro e; subst e; omega) ∈
      Subgroup.normalizer (A : Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))) :
    ∃ M, 1 ≤ M ∧ M < n ∧ InvStd X M := by
  obtain ⟨M, hMn, hW⟩ := eq_stdE_of_invariant (W := fixN A) fun i j h w hw =>
    smul_mem_fixN (htA i j h) hw
  refine ⟨M, ?_, ?_, fun x hx v hv => ?_⟩
  · obtain ⟨v, hv, hv0⟩ := exists_ne_zero_fixN hA hn
    by_contra hM
    rw [hW] at hv
    exact hv0 (funext fun i => hv i (by omega))
  · obtain ⟨v, hv⟩ := exists_not_mem_fixN hA1
    by_contra hM
    rw [hW] at hv
    exact hv fun i hi => absurd i.2 (by omega)
  · rw [← hW] at hv ⊢
    exact smul_mem_fixN (hXA hx) hv

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
