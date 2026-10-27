module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmChars
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmComp
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCase

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative QuadraticMap ChoiceTwo Polynomial
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace OmCoord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} (C : OmCoord K Q A)

section Commute

omit [Finite K] [FiniteDimensional K V] in
theorem exists_decomp (β : Fin C.s → ZMod 3) (v : V) :
    ∃ v₀ v₁, v = v₀ + v₁ ∧ C.tor β v₀ = v₀ ∧ C.tor β (C.tor β v₁) + C.tor β v₁ + v₁ = 0 := by
  classical
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  set dZ : Fin C.s → K × K := fun i => if β i = 0 then d i else 0 with hdZ
  refine ⟨C.Φ (dZ, x), C.Φ (d - dZ, 0), ?_, ?_, ?_⟩
  · rw [← map_add, Prod.mk_add_mk, add_sub_cancel, add_zero]
  · refine (C.tor_Φ_eq_iff β dZ x).mpr fun i hi => ?_
    simp [hdZ, hi]
  · refine (C.phi3_Φ_eq_zero_iff β _ 0).mpr ⟨rfl, fun i hi => ?_⟩
    simp [hdZ, hi]

variable (hK : Nat.card K = 2)
include hK

theorem commute_fixed_phi3 (β : Fin C.s → ZMod 3) {g h : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q (C.tor β) (X - 1)) (hh : h ∈ supportedBlock Q (C.tor β) (phi3 K)) :
    g * h = h * g := by
  have : Fact (Irreducible (phi3 K)) := ⟨phi3_irreducible hK⟩
  set x := C.tor β with hxdef
  have hgx : g * x = x * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
  have hhx : h * x = x * h :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hh).1).2
  have ex : ∀ (k : V ≃ₗ[K] V), k * x = x * k → ∀ w, k (x w) = x (k w) := fun k hk w => by
    have := congrArg (fun f : V ≃ₗ[K] V => f w) hk
    simpa only [LinearEquiv.mul_apply] using this
  have hg1 : ∀ v₁, x (x v₁) + x v₁ + v₁ = 0 → g v₁ = v₁ := by
    intro v₁ hv₁
    by_cases hk : phi3 K ∈ primaryFactors x.toLinearMap
    · refine apply_eq_of_mem_supportedBlock hg hk phi3_ne_X_sub_one ?_ ?_
      · rw [reciprocalPolynomial_X_sub_one]
        exact phi3_ne_X_sub_one
      · exact mem_primaryComponent.mpr (by rw [aeval_phi3_apply']; exact hv₁)
    · have h0 : v₁ ∈ primaryComponent x.toLinearMap (phi3 K) :=
        mem_primaryComponent.mpr (by rw [aeval_phi3_apply']; exact hv₁)
      rw [CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem (phi3_irreducible hK)
        monic_phi3 hk,
        Submodule.mem_bot] at h0
      rw [h0, map_zero]
  have hh0 : ∀ v₀, x v₀ = v₀ → h v₀ = v₀ := by
    intro v₀ hv₀
    have hmem : v₀ ∈ primaryComponent x.toLinearMap (X - 1) := by
      rw [← fixedSpace_eq_primaryComponent]
      exact mem_fixedSpace.mpr hv₀
    by_cases hk : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
    · refine apply_eq_of_mem_supportedBlock hh hk (Ne.symm phi3_ne_X_sub_one) ?_ hmem
      rw [reciprocal_phi3]
      exact (Ne.symm phi3_ne_X_sub_one)
    · rw [CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one
        monic_X_sub_one hk,
        Submodule.mem_bot] at hmem
      rw [hmem, map_zero]
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨v₀, v₁, rfl, hv₀, hv₁⟩ := C.exists_decomp β v
  have hgv₀ : x (g v₀) = g v₀ := by rw [← ex g hgx, hv₀]
  have hhv₁ : x (x (h v₁)) + x (h v₁) + h v₁ = 0 := by
    rw [← ex h hhx, ← ex h hhx, ← map_add, ← map_add, hv₁, map_zero]
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hg1 v₁ hv₁, hh0 v₀ hv₀, hg1 _ hhv₁, hh0 _ hgv₀]

end Commute

section Count

omit [Finite K] [FiniteDimensional K V] in
theorem tor_smul_mem {H : Subgroup (V ≃ₗ[K] V)} {f : Fin C.s → ZMod 3} (hf : C.tor f ∈ H)
    (k : ZMod 3) : C.tor (k • f) ∈ H := by
  have : ∀ m : ℕ, C.tor ((m : ZMod 3) • f) = C.tor f ^ m := by
    intro m
    induction m with
    | zero => simp [C.tor_zero]
    | succ m ih => rw [Nat.cast_succ, add_smul, one_smul, C.tor_add, ih, pow_succ]
  rw [← ZMod.natCast_zmod_val k, this]
  exact pow_mem hf _

omit [Finite K] [FiniteDimensional K V] in
theorem pow_card_le_succ (U : Finset (Fin C.s)) {H : Subgroup (V ≃ₗ[K] V)} [Finite H]
    (hU : ∀ i ∈ U, ∀ a, C.tor (Pi.single i a) ∈ H) {f₀ : Fin C.s → ZMod 3}
    (hf₀U : ∀ i ∈ U, f₀ i = 0) (hf₀ : f₀ ≠ 0) (h0 : C.tor f₀ ∈ H) :
    3 ^ (U.card + 1) ≤ Nat.card H := by
  classical
  set ext : (U → ZMod 3) → Fin C.s → ZMod 3 :=
    fun e l => if h : l ∈ U then e ⟨l, h⟩ else 0 with hext
  have hsum : ∀ e : U → ZMod 3, ext e = ∑ i ∈ U.attach, Pi.single (i : Fin C.s) (e i) := by
    intro e
    funext l
    rw [Finset.sum_apply]
    by_cases hl : l ∈ U
    · rw [Finset.sum_eq_single ⟨l, hl⟩]
      · simp [hext, hl]
      · intro b _ hb
        rw [Pi.single_eq_of_ne]
        intro h
        exact hb (Subtype.ext h.symm)
      · intro h
        exact absurd (Finset.mem_attach _ _) h
    · rw [Finset.sum_eq_zero]
      · simp [hext, hl]
      · intro b _
        rw [Pi.single_eq_of_ne]
        rintro rfl
        exact hl b.2
  have hmem : ∀ e, C.tor (ext e) ∈ H := by
    intro e
    rw [hsum]
    induction (U.attach) using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, C.tor_zero]
      exact one_mem _
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, C.tor_add]
      exact mul_mem (hU _ a.2 _) ih
  obtain ⟨j, hj⟩ : ∃ j, f₀ j ≠ 0 := Function.ne_iff.mp hf₀
  have hjU : j ∉ U := fun h => hj (hf₀U j h)
  have hmem' : ∀ p : (U → ZMod 3) × ZMod 3, C.tor (ext p.1 + p.2 • f₀) ∈ H := fun p => by
    rw [C.tor_add]
    exact mul_mem (hmem _) (C.tor_smul_mem h0 _)
  have hinj : Function.Injective fun p : (U → ZMod 3) × ZMod 3 =>
      (⟨C.tor (ext p.1 + p.2 • f₀), hmem' p⟩ : H) := by
    rintro ⟨e, k⟩ ⟨e', k'⟩ h
    have h1 := C.tor_injective (congrArg Subtype.val h)
    have hk : k = k' := by
      have := congrFun h1 j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hext, hjU, dite_false,
        zero_add] at this
      exact mul_right_cancel₀ hj this
    subst hk
    refine Prod.ext (funext fun l => ?_) rfl
    have := congrFun h1 l
    simpa [hext, l.2] using this
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := U),
    Fintype.card_coe, ← pow_succ] at this

end Count

section Choice

omit [Finite K] [FiniteDimensional K V] in
theorem pow_le_aux {n : ℕ} {u : ℕ} (h : 3 ^ u ≤ 3 ^ n) : u ≤ n :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem choice_core (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hs : 4 ≤ C.s)
    {β : Fin C.s → ZMod 3} (hβ : β ≠ 0) {L₁ : Subgroup (V ≃ₗ[K] V)}
    (hL₁ : CFSG.Assembly.IsComponentOf L₁
      (CFSG.RankThree.Classical2.orthDerived Q ⊓ Subgroup.centralizer {C.tor β}))
    (hL₁c : Nat.card (A ⊓ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ 3 ^ 2)
    (t₁ t₂ : Fin C.s → ZMod 3) {J : Subgroup (V ≃ₗ[K] V)} (hJq : CFSG.IsQuasisimple J)
    (hJO : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hJc : ∀ a, ∀ g ∈ J, g * C.tor (comb2 t₁ t₂ a) = C.tor (comb2 t₁ t₂ a) * g)
    (hJA : Nat.card (A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ 3 ^ 3)
    (hJA4 : C.s = 4 →
      Nat.card (A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ 3 ^ 2) :
    ∃ (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool),
      (η = (fun _ => false) ∨ ∃ i j, i ≠ j ∧ η = swapSgn i j true) ∧
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧ g * g = 1 ∧
        ∀ a, g * C.tor (moveExp π η (comb2 t₁ t₂ a)) =
          C.tor (moveExp π η (comb2 t₁ t₂ a)) * g := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  have hJp : ⁅J, J⁆ = J := LayerFacts.ggCommutator_eq_of_isQuasisimple hJq
  have hcount : ∀ U : Finset (Fin C.s), (∀ i ∈ U, ∀ a, ∀ g ∈ J,
      g * C.tor (Pi.single i a) = C.tor (Pi.single i a) * g) → U.card + 1 < C.s := by
    intro U hU
    have hle := C.pow_card_le U (H := A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)))
      fun i hi a => Subgroup.mem_inf.mpr ⟨C.tor_mem _,
        Subgroup.mem_centralizer_iff.mpr fun g hg => hU i hi a g hg⟩
    rcases (show C.s = 4 ∨ 5 ≤ C.s by omega) with h4 | h5
    · have := pow_le_aux (hle.trans (hJA4 h4))
      omega
    · have := pow_le_aux (hle.trans hJA)
      omega
  obtain ⟨j₁, j₂, hj, ε, hε⟩ := C.exists_pair t₁ t₂ hJp hJO hJc hcount
  have hx := C.oddOrderIsometry hQ β
  obtain ⟨h, hh, hLF⟩ := SevOm.exists_le_supportedBlock hx
    (SevOm.isComponentOf_isometryCentralizer hL₁)
  set H := A ⊓ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)) with hHdef
  have hHmem : ∀ f, (∀ g ∈ L₁, g * C.tor f = C.tor f * g) → C.tor f ∈ H := fun f hf =>
    Subgroup.mem_inf.mpr ⟨C.tor_mem f, Subgroup.mem_centralizer_iff.mpr fun g hg => hf g hg⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin C.s)))
    (fun i => β i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  rcases primaryFactor_cases hK (C.toLinearMap_pow_three β) hh with rfl | rfl
  ·
    have hS2 : (Finset.univ.filter fun i => ¬ β i = 0).card ≤ 2 := by
      have hle := C.pow_card_le (Finset.univ.filter fun i => ¬ β i = 0) (H := H)
        fun i hi a => hHmem _ fun g hg =>
        C.commute_fixed_phi3 hK β (hLF hg) (C.tor_mem_phi3Block hK fun l hl => by
          rw [Pi.single_eq_of_ne]
          rintro rfl
          exact (Finset.mem_filter.mp hi).2 hl)
      exact pow_le_aux (hle.trans hL₁c)
    obtain ⟨i₁, hi₁, i₂, hi₂, h12⟩ := Finset.one_lt_card.mp
      (show 1 < (Finset.univ.filter fun i => β i = 0).card by omega)
    have hβ1 : β i₁ = 0 := (Finset.mem_filter.mp hi₁).2
    have hβ2 : β i₂ = 0 := (Finset.mem_filter.mp hi₂).2
    obtain ⟨π, hπ1, hπ2⟩ := exists_perm_pair h12 hj
    refine ⟨π, fun _ => false, Or.inl rfl, C.move (Equiv.swap i₁ i₂) (swapSgn i₁ i₂ ε), ?_,
      ⟨C.tor (Pi.single i₁ 1), ?_, C.swap_not_commute_tor h12 ε⟩, C.swap_mul_self h12 ε,
      fun a => ?_⟩
    · exact mem_of_fixedBlock hK hQ (by decide) hx hL₁ hLF (C.swap_mem_fixedBlock hK ε hβ1 hβ2)
        (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ (C.swap_mem hQ hT h12 ε))
    · exact mem_of_fixedBlock_of_pow hK hQ (by decide) hx hL₁ hLF
        (C.tor_mem_fixedBlock hK fun l hl => by
          rw [Pi.single_eq_of_ne]
          rintro rfl
          exact hl hβ1) (by decide : Odd 3) (C.tor_pow_three _)
    · apply C.swap_commute_tor ε
      rw [moveExp_apply, moveExp_apply, hπ1, hπ2, hε a, sgnZ_false, sgnZ_false]
  ·
    have hLeq := eq_specialBlock_of_phi3 hx hL₁ hh hLF
    have hZ1 : (Finset.univ.filter fun i => β i = 0).card ≤ 1 := by
      have hle := C.pow_card_le_succ (Finset.univ.filter fun i => β i = 0) (H := H)
        (fun i hi a => hHmem _ fun g hg =>
        (C.commute_fixed_phi3 hK β (C.tor_mem_fixedBlock hK fun l hl => by
          rw [Pi.single_eq_of_ne]
          rintro rfl
          exact hl (Finset.mem_filter.mp hi).2) (hLF hg)).symm)
        (fun i hi => (Finset.mem_filter.mp hi).2) hβ (hHmem _ fun g hg =>
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hL₁.1 hg)).2)
      have := pow_le_aux (hle.trans hL₁c)
      omega
    obtain ⟨i₁, hi₁, i₂, hi₂, i₃, hi₃, h12, h13, h23⟩ := Finset.two_lt_card.mp
      (show 2 < (Finset.univ.filter fun i => ¬ β i = 0).card by omega)
    have hβ1 : β i₁ ≠ 0 := (Finset.mem_filter.mp hi₁).2
    have hβ2 : β i₂ ≠ 0 := (Finset.mem_filter.mp hi₂).2
    have hβ3 : β i₃ ≠ 0 := (Finset.mem_filter.mp hi₃).2
    obtain ⟨bsw, hbsw⟩ : ∃ b, β i₁ = sgnZ b (β i₂) := by
      rcases exists_sgnZ_of_ne_zero _ _ hβ1 hβ2 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨bsw', hbsw'⟩ : ∃ b, β i₁ = sgnZ b (β i₃) := by
      rcases exists_sgnZ_of_ne_zero _ _ hβ1 hβ3 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨π, hπ1, hπ2⟩ := exists_perm_pair h12 hj
    set e := bsw ^^ ε with he
    set η : Fin C.s → Bool := if e then swapSgn i₁ i₃ true else fun _ => false with hη
    have hη1 : η i₁ = e := by
      rw [hη]
      cases e <;> simp [swapSgn]
    have hη2 : η i₂ = false := by
      rw [hη]
      cases e <;> simp [swapSgn, Ne.symm h12, h23]
    refine ⟨π, η, ?_, C.move (Equiv.swap i₁ i₂) (swapSgn i₁ i₂ bsw), ?_,
      ⟨C.move (Equiv.swap i₁ i₃) (swapSgn i₁ i₃ bsw'), ?_, C.swap_not_commute h12 h13 h23 _ _⟩,
      C.swap_mul_self h12 bsw, fun a => ?_⟩
    · rw [hη]
      cases e
      · exact Or.inl rfl
      · exact Or.inr ⟨i₁, i₃, h13, rfl⟩
    · rw [hLeq]
      exact mem_specialBlock_of_mul_self hK (C.swap_mem_phi3Block hK bsw hβ1 hβ2 hbsw)
        (C.swap_mul_self h12 bsw)
    · rw [hLeq]
      exact mem_specialBlock_of_mul_self hK (C.swap_mem_phi3Block hK bsw' hβ1 hβ3 hbsw')
        (C.swap_mul_self h13 bsw')
    · apply C.swap_commute_tor bsw
      rw [moveExp_apply, moveExp_apply, hπ1, hπ2, hη1, hη2, hε a, sgnZ_sgnZ_xor, he,
        bxor_bxor_cancel, sgnZ_false]

end Choice

end OmCoord

end ChoiceTwoOm

end CFSG.StandardType
