module

public import CFSG.Quasithin.H13.NQBlockMixedA5
public import CFSG.Quasithin.H13.NQTermTensorEquality
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

open Module

namespace CFSG.Quasithin.H13.NQTerm

theorem eq_one_of_pow_five_of_finrank_range_le_two {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {T : Module.End (ZMod 2) V}
    (hdim : finrank (ZMod 2) (LinearMap.range (T - 1)) ≤ 2) (hT : T ^ 5 = 1) : T = 1 := by
  classical
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  set U := LinearMap.range (T - 1) with hU
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card U ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    calc 2 ^ finrank (ZMod 2) U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hdim
      _ = 4 := by norm_num
  have hTU : ∀ u ∈ U, T u ∈ U := by
    rintro _ ⟨v, rfl⟩
    refine ⟨T v, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  have hTinj : Function.Injective T := by
    have hinv : T ^ 4 * T = 1 := by rw [← pow_succ, hT]
    intro a b hab
    have e : (T ^ 4) (T a) = (T ^ 4) (T b) := by rw [hab]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hinv] at e
    exact e
  set f : U → U := fun u => ⟨T u, hTU u u.2⟩ with hf
  have hfinj : Function.Injective f := fun a b h => Subtype.ext (hTinj (congrArg Subtype.val h))
  set σ : Equiv.Perm U := Equiv.ofBijective f hfinj.bijective_of_finite with hσ
  have hσpow : ∀ (n : ℕ) (u : U), ((σ ^ n) u : V) = (T ^ n) u := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have hσ5 : σ ^ 5 = 1 := by
    ext u
    rw [hσpow, hT, Module.End.one_apply, Equiv.Perm.one_apply]
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ5
    have h2 : orderOf σ ∣ (Nat.card U).factorial := by
      rw [← Nat.card_perm]
      exact orderOf_dvd_natCard σ
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      have := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 5)).mp h2
      omega
  have hTT : ∀ v, T (T v) = v := by
    intro v
    have h1 : σ ⟨(T - 1) v, ⟨v, rfl⟩⟩ = ⟨(T - 1) v, ⟨v, rfl⟩⟩ := by rw [hσ1]; rfl
    have h3 : T ((T - 1) v) = (T - 1) v := congrArg Subtype.val h1
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub] at h3
    have h4 : T (T v) = T v - v + T v := by rw [← h3]; abel
    rw [h4, sub_add_eq_add_sub, h2, zero_sub]
    have h5 := h2 v
    rw [add_eq_zero_iff_eq_neg] at h5
    exact h5.symm
  have hT2 : T * T = 1 := LinearMap.ext fun v => by
    rw [Module.End.mul_apply, hTT, Module.End.one_apply]
  calc T = T * (T * T) * (T * T) := by rw [hT2, mul_one, mul_one]
    _ = T ^ 5 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := hT

theorem mul_eq_one_of_pow_five_of_rank_le_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {y y' : Module.End (ZMod 2) V}
    (hy : finrank (ZMod 2) (LinearMap.range (y - 1)) ≤ 1)
    (hy' : finrank (ZMod 2) (LinearMap.range (y' - 1)) ≤ 1) (hT : (y * y') ^ 5 = 1) :
    y * y' = 1 := by
  refine eq_one_of_pow_five_of_finrank_range_le_two ?_ hT
  have hUle :
      LinearMap.range (y * y' - 1) ≤ LinearMap.range (y - 1) ⊔ LinearMap.range (y' - 1) := by
    rintro _ ⟨v, rfl⟩
    have e : (y * y' - 1) v = (y - 1) (y' v) + (y' - 1) v := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply]
      abel
    rw [e]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  have h1 := Submodule.finrank_mono hUle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (y - 1))
    (LinearMap.range (y' - 1))
  omega

theorem exists_conj_mul_pow_five : ∀ y : alternatingGroup (Fin 5), y ≠ 1 → y ^ 2 = 1 →
    ∃ g : alternatingGroup (Fin 5), (y * (g * y * g⁻¹)) ^ 5 = 1 ∧ y * (g * y * g⁻¹) ≠ 1 := by
  decide +kernel

theorem card_le_of_embeds_aut {G : Type*} [Group G] {D Y : Subgroup G}
    (hYn : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (eY : Y ≃* alternatingGroup (Fin 5))
    (hCY : ∀ d ∈ D, (∀ y ∈ Y, d * y = y * d) → d = 1) :
    Nat.card D ≤ 120 ∧ ∀ A : Subgroup G, A ≤ D → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ 2 = 1) → Nat.card A ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDN : D ≤ Subgroup.normalizer (Y : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hYn d hd h hh, fun hh => ?_⟩
    have h1 := hYn d⁻¹ (D.inv_mem hd) _ hh
    rwa [inv_inv, show d⁻¹ * (d * h * d⁻¹) * d = h by group] at h1
  set κ : D →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hDN) with hκ
  have hκinj : Function.Injective κ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    have h1 : Subgroup.inclusion hDN d ∈ Y.normalizerMonoidHom.ker := hd
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hCY d d.2 fun y hy => (h1 y hy).symm)
  set Θ := CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm eY
  have : Finite (MulAut Y) := Finite.of_equiv _ Θ.symm.toEquiv
  have hcard : Nat.card (MulAut Y) = 120 := by
    rw [Nat.card_congr Θ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  refine ⟨hcard ▸ Nat.card_le_card_of_injective κ hκinj, fun A hAD hAc hA2 => ?_⟩
  have hAe : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hA2 a a.2) }
  have : CFSG.IsElementaryAbelian 2 (A.subgroupOf D) := CFSG.IsElementaryAbelian.subgroupOf hAD
  have : CFSG.IsElementaryAbelian 2 ((A.subgroupOf D).map κ) := CFSG.IsElementaryAbelian.map κ
  have h1 := CFSG.LieType.SteinbergBR.card_le_sq_of_orderOf
    (g := Θ.symm CFSG.LieType.SteinbergBR.AltFiveGL3.c4) (k := 2)
    (by rw [MulEquiv.orderOf_eq, CFSG.LieType.SteinbergBR.AltFiveGL3.orderOf_c4])
    (by rw [hcard]; norm_num) ((A.subgroupOf D).map κ)
  rw [Subgroup.card_map_of_injective hκinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv] at h1
  simpa using h1

section Commutant

open LocalAnalysis.CommutingFactor

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] {D : Subgroup (Module.End (ZMod 2) S)ˣ}
  {I : Submodule (ZMod 2) S}

theorem resD_mul (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I) (d₁ d₂ : D) :
    resD hDI (d₁ * d₂) = resD hDI d₁ * resD hDI d₂ :=
  LinearMap.ext fun _ => Subtype.ext rfl

theorem resD_one (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I) :
    resD hDI 1 = 1 :=
  LinearMap.ext fun _ => Subtype.ext rfl

theorem resD_pow (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I) (d : D) (n : ℕ) :
    resD hDI (d ^ n) = resD hDI d ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, resD_one]
  | succ n ih => rw [pow_succ, pow_succ, resD_mul, ih]

theorem natCard_commutantD_eq_two [FiniteDimensional (ZMod 2) S]
    (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I) (hI0 : I ≠ ⊥)
    (hIirr : ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End (ZMod 2) S) v ∈ U) → U = ⊥ ∨ U = I)
    (b : D) (hb1 : resD hDI b ≠ 1)
    (hrank : finrank (ZMod 2) (LinearMap.range (resD hDI b - 1)) ≤ 1) :
    Nat.card (commutantD hDI) = 2 := by
  classical
  set U := LinearMap.range (resD hDI b - 1) with hU
  have hU0 : U ≠ ⊥ := by
    intro h
    apply hb1
    rw [LinearMap.range_eq_bot, sub_eq_zero] at h
    exact h
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hU1 : finrank (ZMod 2) U = 1 := by
    have : 0 < finrank (ZMod 2) U :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨u, huU⟩, by simpa using hu0⟩
    omega
  have hUu : ∀ w ∈ U, w = 0 ∨ w = u := by
    intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u, huU⟩ : U)
      (by simpa using hu0)).mp hU1 ⟨w, hw⟩
    have hc' : c • u = w := congrArg Subtype.val hc
    have hc01 : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc01 with rfl | rfl
    · left
      rw [← hc', zero_smul]
    · right
      rw [← hc', one_smul]
  have hφU : ∀ φ ∈ commutantD hDI, φ u ∈ U := by
    intro φ hφ
    obtain ⟨v, rfl⟩ := huU
    refine ⟨φ v, ?_⟩
    have h1 := LinearMap.congr_fun ((mem_commutantD hDI).mp hφ b) v
    rw [Module.End.mul_apply, Module.End.mul_apply] at h1
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, h1]
  have h01 : ∀ φ ∈ commutantD hDI, φ = 0 ∨ φ = 1 := by
    intro φ hφ
    by_cases h0 : φ = 0
    · exact Or.inl h0
    right
    have hφinj := injective_of_mem_commutantD hDI hIirr hφ h0
    have hφu : φ u = u := by
      rcases hUu _ (hφU φ hφ) with h | h
      · exact absurd (hφinj (h.trans (map_zero φ).symm)) hu0
      · exact h
    by_contra h1
    have hψ : φ - 1 ∈ commutantD hDI := Subalgebra.sub_mem _ hφ (Subalgebra.one_mem _)
    have hψinj := injective_of_mem_commutantD hDI hIirr hψ (sub_ne_zero.mpr h1)
    apply hu0
    apply hψinj
    rw [LinearMap.sub_apply, hφu, Module.End.one_apply, sub_self, map_zero]
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI0
  rw [Nat.card_eq_two_iff]
  refine ⟨0, 1, fun h => zero_ne_one (α := Module.End (ZMod 2) I) (congrArg Subtype.val h),
    Set.eq_univ_of_forall fun φ => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h01 φ.1 φ.2 with h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (Subtype.ext h)

end Commutant

open LocalAnalysis.CommutingFactor (resD commutantD fixedSub) in
theorem near_maximal_mixed_A5_action_exceeds_the_rank_budget
    {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [FiniteDimensional (ZMod 2) S]
    [Nontrivial S] {X D Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    (hirr : ∀ W : Submodule (ZMod 2) S,
      (∀ g ∈ X ⊔ D, ∀ v ∈ W, (g : Module.End (ZMod 2) S) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hX1 : X ≠ ⊥) (hXp : Group.IsPerfect X)
    (hYn : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (eY : Y ≃* alternatingGroup (Fin 5))
    (hCY : ∀ d ∈ D, (∀ y ∈ Y, d * y = y * d) → d = 1)
    (hDYA : D = Y ⊔ A) (hA1 : A ≠ ⊥) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {j : ℕ} (hj : j ≤ 1) :
    j + Nat.log 2 (Nat.card A) < finrank (ZMod 2) S - finrank (ZMod 2) (fixedSub A) := by
  classical
  by_contra hc
  push Not at hc
  have hYD : Y ≤ D := by rw [hDYA]; exact le_sup_left
  have hAD : A ≤ D := by rw [hDYA]; exact le_sup_right
  obtain ⟨hD120, hA4⟩ := card_le_of_embeds_aut hYn eY hCY
  obtain ⟨I, hDI, hI0, hIirr⟩ := exists_irreducible_invariant D
  obtain ⟨r, -, -, -, hfaith, -, -, -, -, hcod, hr2, hr3, -⟩ :=
    LocalAnalysis.CommutingFactor.commuting_factor_irreducible_modules_have_isotypic_multiplicity
      hXD hirr hDI hI0 hIirr
  have hr2' : 2 ≤ r := hr2 hX1 hXp
  have : Finite (Module.End (ZMod 2) S)ˣ := LocalAnalysis.CommutingFactor.finite_endUnits
  have hcodA := hcod A hAD
  set C := fixedSub A with hC
  have hcI : 1 ≤ finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C) := by
    by_contra h0
    have heq : I ⊓ C = I := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
    apply hA1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine hfaith b (hAD hb) fun v hv => ?_
    have hv' : v ∈ I ⊓ C := by rw [heq]; exact hv
    exact LocalAnalysis.CommutingFactor.mem_fixedSub.mp (Submodule.mem_inf.mp hv').2 b hb
  obtain ⟨a, ha⟩ : ∃ a, Nat.card A = 2 ^ a := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.exists_card_eq (p := 2) fun g => ⟨1, Subtype.ext ?_⟩
    simpa using hA2 g g.2
  rw [ha, Nat.log_pow one_lt_two] at hc
  have key : r * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) ≤ j + a := by
    rw [← hcodA]
    exact hc
  have h2c : 2 * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) ≤
      r * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) := Nat.mul_le_mul hr2' le_rfl
  have ha2 : a ≤ 2 := by
    have h1 := hA4 A hAD hAc hA2
    rw [ha] at h1
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hc1 : finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C) = 1 := by omega
  have hrank : ∀ b : D, (b : (Module.End (ZMod 2) S)ˣ) ∈ A →
      finrank (ZMod 2) (LinearMap.range (resD hDI b - 1)) ≤ 1 := by
    intro b hb
    have hle : (I ⊓ C).comap I.subtype ≤ LinearMap.ker (resD hDI b - 1) := by
      intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      apply Subtype.ext
      rw [LocalAnalysis.CommutingFactor.coe_resD]
      exact LocalAnalysis.CommutingFactor.mem_fixedSub.mp (Submodule.mem_inf.mp hv).2 b hb
    have h1 := Submodule.finrank_mono hle
    have h2 := LinearMap.finrank_range_add_finrank_ker (resD hDI b - 1)
    have h3 : finrank (ZMod 2) ((I ⊓ C).comap I.subtype) = finrank (ZMod 2) ↥(I ⊓ C) :=
      (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
    omega
  have hres1 : ∀ d : D, resD hDI d = 1 → d = 1 := by
    intro d hd
    refine Subtype.ext (hfaith d d.2 fun v hv => ?_)
    have h1 := LinearMap.congr_fun hd ⟨v, hv⟩
    exact congrArg Subtype.val h1
  obtain ⟨b₀, hb₀A, hb₀1⟩ : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    exact ⟨b, hb, fun h => hb1 (Subtype.ext h)⟩
  have hcomm2 : Nat.card (commutantD hDI) = 2 :=
    natCard_commutantD_eq_two hDI hI0 hIirr ⟨b₀, hAD hb₀A⟩
      (fun h => hb₀1 (congrArg Subtype.val (hres1 _ h))) (hrank _ hb₀A)
  have hr3' : 3 ≤ r := hr3 (Nat.card_zmod 2) hcomm2 hX1 hXp
  have ha2' : a = 2 := by
    have h3c : 3 * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) ≤
        r * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) := Nat.mul_le_mul hr3' le_rfl
    omega
  obtain ⟨y, hyA, hyY, hy1⟩ : ∃ y ∈ A, y ∈ Y ∧ y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hidx : (Y.subgroupOf D).index ≤ 2 := by
      have h1 := Subgroup.card_mul_index (Y.subgroupOf D)
      have h2 : Nat.card (Y.subgroupOf D) = 60 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYD).toEquiv, Nat.card_congr eY.toEquiv,
          nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      rw [h2] at h1
      omega
    have hinj : Function.Injective fun x : A =>
        (QuotientGroup.mk (⟨x, hAD x.2⟩ : D) : D ⧸ Y.subgroupOf D) := by
      intro x₁ x₂ h
      have h1 : (⟨x₁, hAD x₁.2⟩ : D)⁻¹ * ⟨x₂, hAD x₂.2⟩ ∈ Y.subgroupOf D := QuotientGroup.eq.mp h
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 := hcon _ (A.mul_mem (A.inv_mem x₁.2) x₂.2) h1
      exact Subtype.ext (inv_mul_eq_one.mp h2)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [ha, ha2'] at h1
    have h2 : Nat.card (D ⧸ Y.subgroupOf D) ≤ 2 := hidx
    omega
  set yY : Y := ⟨y, hyY⟩ with hyYdef
  have hey1 : eY yY ≠ 1 := by
    intro h
    apply hy1
    have h1 : yY = 1 := eY.injective (h.trans (map_one eY).symm)
    exact congrArg Subtype.val h1
  have hey2 : eY yY ^ 2 = 1 := by
    rw [← map_pow]
    have h1 : yY ^ 2 = 1 := Subtype.ext (by simpa using hA2 y hyA)
    rw [h1, map_one]
  obtain ⟨g, hg5, hg1⟩ := exists_conj_mul_pow_five (eY yY) hey1 hey2
  set g' : Y := eY.symm g with hg'
  set w : Y := yY * (g' * yY * g'⁻¹) with hw
  have hew : eY w = eY yY * (g * eY yY * g⁻¹) := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, hg', MulEquiv.apply_symm_apply]
  have hw5 : w ^ 5 = 1 := eY.injective (by rw [map_pow, hew, hg5, map_one])
  have hw1 : w ≠ 1 := fun h => hg1 (by rw [← hew, h, map_one])
  set dy : D := ⟨y, hYD hyY⟩ with hdy
  set dg : D := ⟨(g' : (Module.End (ZMod 2) S)ˣ), hYD g'.2⟩ with hdg
  set dy' : D := dg * dy * dg⁻¹ with hdy'
  have hρy' : finrank (ZMod 2) (LinearMap.range (resD hDI dy' - 1)) ≤ 1 := by
    have hgg : resD hDI dg * resD hDI dg⁻¹ = 1 := by
      rw [← resD_mul, mul_inv_cancel, resD_one]
    have e1 : resD hDI dy' - 1 = resD hDI dg * (resD hDI dy - 1) * resD hDI dg⁻¹ := by
      rw [hdy', resD_mul, resD_mul, mul_sub, sub_mul, mul_one, hgg]
    rw [e1]
    calc finrank (ZMod 2) (LinearMap.range (resD hDI dg * (resD hDI dy - 1) * resD hDI dg⁻¹))
        ≤ finrank (ZMod 2) (LinearMap.range (resD hDI dg * (resD hDI dy - 1))) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
      _ = finrank (ZMod 2) ((LinearMap.range (resD hDI dy - 1)).map (resD hDI dg)) := by
          rw [Module.End.mul_eq_comp, LinearMap.range_comp]
      _ ≤ finrank (ZMod 2) (LinearMap.range (resD hDI dy - 1)) := Submodule.finrank_map_le _ _
      _ ≤ 1 := hrank dy hyA
  have hdw : dy * dy' = ⟨(w : (Module.End (ZMod 2) S)ˣ), hYD w.2⟩ := Subtype.ext rfl
  have hpow : (resD hDI dy * resD hDI dy') ^ 5 = 1 := by
    rw [← resD_mul, ← resD_pow, hdw]
    have h1 : (⟨(w : (Module.End (ZMod 2) S)ˣ), hYD w.2⟩ : D) ^ 5 = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      change (w : (Module.End (ZMod 2) S)ˣ) ^ 5 = 1
      rw [← SubgroupClass.coe_pow, hw5, OneMemClass.coe_one]
    rw [h1, resD_one]
  have h1 := mul_eq_one_of_pow_five_of_rank_le_one (hrank dy hyA) hρy' hpow
  rw [← resD_mul, hdw] at h1
  apply hw1
  have h2 : (w : (Module.End (ZMod 2) S)ˣ) = 1 := congrArg Subtype.val (hres1 _ h1)
  exact Subtype.ext h2

theorem mixedA5RankBudget_holds : NQBlock.MixedA5RankBudget := by
  intro S _ _ _ _ X D Y A hXD hirr hX1 hXp hYn ⟨eY⟩ hCY hDYA hA1 hAc hA2 j hj
  exact near_maximal_mixed_A5_action_exceeds_the_rank_budget hXD hirr hX1 hXp hYn eY hCY hDYA
    hA1 hAc hA2 hj

end CFSG.Quasithin.H13.NQTerm

