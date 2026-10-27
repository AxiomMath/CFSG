module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorData
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.CoverEquiv
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddL2Big
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicM11J1
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiModule
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover CFSG.Blueprint CFSG.LieType.Ree
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
  CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

theorem isPGroup_two_of_sq_eq_one {S : Type} [Group S] (B : Subgroup (MulAut S))
    (h2 : ∀ x ∈ B, x * x = 1) : IsPGroup 2 B :=
  fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using h2 x.1 x.2⟩

theorem center_eq_bot_of_simple_perfect {S : Type} [Group S] [IsSimpleGroup S]
    (hperf : Group.IsPerfect S) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · have h1 := hperf.commutator_eq_top
    rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
    exact absurd h1 bot_ne_top

theorem card_elemAbelian_mulAut_of_inner {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    (hP : ∀ B : Subgroup (MulAut S), IsPGroup 2 B → B ≤ (MulAut.conj : S →* MulAut S).range)
    {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) :
    ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun y => by
      have := congrArg (fun α : MulAut S => α y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact hgZ
  intro B hc h2
  let B' : Subgroup S := B.comap (MulAut.conj : S →* MulAut S)
  have hmap : B'.map (MulAut.conj : S →* MulAut S) = B :=
    Subgroup.map_comap_eq_self (hP B (isPGroup_two_of_sq_eq_one B h2))
  have hB' := hr B'
    (fun x hx y hy => hinj (by
      rw [map_mul, map_mul]; exact hc _ hx _ hy))
    (fun x hx => hinj (by
      rw [map_mul, map_one]; exact h2 _ hx))
  rw [← hmap, Subgroup.card_map_of_injective hinj]
  exact hB'

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Γ A L L₂ : Subgroup (GLV V)} {m : ℕ}


theorem j1_perfect_odd_cover_trivial {E : Type} [Group E]
    [Finite E] [Group.IsPerfect E] (π : E →* NativeSporadic.J1)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have : Finite NativeSporadic.J1 := Finite.of_surjective π hπ
  refine CFSG.SectionRank.ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd
    fun r hr hr2 hsq _ _ => ?_
  exfalso
  rw [CFSG.Sporadic.J1.card_J1] at hsq
  by_cases h3 : r = 3
  · subst h3
    exact absurd hsq (by norm_num)
  · exact (CFSG.SectionRank.small_sporadic_order_conditions (Or.inr (Or.inr (Or.inr rfl)))).2
      r hr hr2 h3 hsq

theorem suzuki_four_mul_le_finrank
    {f a : ℕ} {K : Type} [Field K] [Finite K] (hf3 : 3 ≤ f) (hfa : f = 2 * a + 1)
    (hKc : Nat.card K = 2 ^ (2 * a + 1)) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (L' : Subgroup (GLV W)) (g : suzukiGroup a K ≃* ↥L') :
    4 * f ≤ Module.finrank (ZMod 2) W := by
  obtain ⟨p, hpP⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor
    (k := 4 * f) (by omega) (by omega)
  have hp := hpP.prime
  have hdvd : p ∣ 2 ^ (2 * f) + 1 :=
    (hpP.dvd_add_one_iff (by omega) (2 * f)).2
      ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hpP.ne_two (by omega)
  have hcard : p ∣ Nat.card (suzukiGroup a K) := by
    rw [suzuki_order hKc]
    refine Dvd.dvd.mul_left ?_ _
    rw [← pow_mul, ← hfa, mul_comm]
    exact hdvd
  have hcard' : p ∣ Nat.card ↥L' := by
    rw [← Nat.card_congr g.toEquiv]
    exact hcard
  have h1 := orderOf_two_le_finrank_of_dvd_card L' hp2 hcard'
  have h2 : orderOf (2 : ZMod p) = 4 * f := by
    have hpow : (2 : ZMod p) ^ (4 * f) = 1 :=
      (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (4 * f)).1 hpP.dvd
    have hdv : orderOf (2 : ZMod p) ∣ 4 * f := orderOf_dvd_of_pow_eq_one hpow
    have hpos : 0 < orderOf (2 : ZMod p) :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at hdv; omega
    refine le_antisymm (Nat.le_of_dvd (by omega) hdv) ?_
    by_contra hlt
    push Not at hlt
    exact hpP.2.2 _ hpos hlt
      ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).2 (pow_orderOf_eq_one _))
  omega

section


theorem Setting.false_of_cover_rank_dim'
    (h : Setting Γ A L L₂ m) {S : Type} [Group S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    {r : ℕ} (hr1 : 1 ≤ r)
    (hr : Group.IsPerfect S → ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {ρ : ℕ}
    (hDim : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (L' : Subgroup (GLV W)), Nonempty (S ≃* ↥L') → ρ ≤ Module.finrank (ZMod 2) W)
    (hlt : 2 * r + 1 < ρ) : False := by
  obtain ⟨f, -⟩ := exists_mulEquiv_of_cover_odd h.hyp.L_comp.2.2 h.centerL_odd e hCover
  have : Group.IsPerfect ↥L := ⟨h.hyp.L_comp.2.2.1⟩
  have hperf : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  have hm := h.m_le_two_mul f hr1 (hr hperf)
  obtain ⟨W, _, _, _, L', ⟨g⟩, hW⟩ := h.half_module
  have hd := hDim W L' ⟨f.symm.trans g⟩
  have hb := h.hyp.bound
  omega

theorem Setting.false_of_suzuki
    (h : Setting Γ A L L₂ m) {f : ℕ} (_hf : Odd f) (hf3 : 3 ≤ f)
    (hS : IsSz f (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨-, a, ha, K, instF, instFin, hfa, hKc, ⟨e⟩⟩ := hS
  have hKc' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hKc
  refine h.false_of_cover_rank_dim' e ?_ (r := f) (by omega) ?_ (ρ := 4 * f) ?_ (by omega)
  · intro E _ _ _ π hπ hC hodd
    let ε := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup (a := a) hKc'
    let π' := ε.toMonoidHom.comp π
    have hker : π'.ker = π.ker := by
      ext x
      simp [π']
    have := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) π'
      (ε.surjective.comp hπ) (hker ▸ hC) (hker ▸ hodd)
    rwa [hker] at this
  · intro hperf
    have : IsSimpleGroup (suzukiGroup a K) := (suzuki_simple ha hKc').2.2
    refine card_elemAbelian_mulAut_of_inner (center_eq_bot_of_simple_perfect hperf)
      (fun B hB => (CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order
        ha hKc').2 B hB) ?_
    intro B _ hB2
    rw [hfa]
    exact suzuki_exponent_two_card_le hKc' B hB2
  · intro W _ _ _ L' ⟨g⟩
    exact suzuki_four_mul_le_finrank hf3 hfa hKc' L' g

theorem Setting.false_of_j1
    (h : Setting Γ A L L₂ m)
    (hS : IsSporadic .J1 (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨e⟩ := hS
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.J1 := e
  refine h.false_of_cover_rank_dim' e' ?_ (r := 3) (by norm_num) ?_ (ρ := 18) ?_ (by norm_num)
  · intro E _ _ _ π hπ hC hodd
    exact j1_perfect_odd_cover_trivial π hπ hC hodd
  · intro hperf
    have : IsSimpleGroup NativeSporadic.J1 := CFSG.Sporadic.J1.isSimpleGroup_J1
    have hAut := autInner_of_mulEquiv CFSG.Walter.walterJ1EquivNative walterJ1_autInner
    refine card_elemAbelian_mulAut_of_inner (center_eq_bot_of_simple_perfect hperf)
      (fun B _ x _ => ?_)
      (elemAbelian_le_of_mulEquiv CFSG.Walter.walterJ1EquivNative walterJ1_elemAbelian_le)
    obtain ⟨s, hs⟩ := hAut (x : NativeSporadic.J1 ≃* NativeSporadic.J1)
    exact ⟨s, MulEquiv.ext fun y => by rw [MulAut.conj_apply]; exact (hs y).symm⟩
  · intro W _ _ _ L' ⟨g⟩
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    have hdvd : 19 ∣ Nat.card ↥L' := by
      rw [← Nat.card_congr g.toEquiv, CFSG.Sporadic.J1.card_J1]
      norm_num
    have h1 := orderOf_two_le_finrank_of_dvd_card L' (by norm_num : 19 ≠ 2) hdvd
    rwa [orderOf_two_zmod_19] at h1

theorem Setting.false_of_oddL2
    (h : Setting Γ A L L₂ m) {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he1 : 1 ≤ e) (he2 : e ≤ 2) (hq : p ^ e ≠ 5 ∧ p ^ e ≠ 7)
    (hS : IsPSL 2 p e (↥L ⧸ Subgroup.center ↥L)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hpar, K, instK, instF, hK, ⟨e'⟩⟩ := hS
  have h9 : p ^ e ≠ 9 := fun h9 => by
    have := (eq_three_of_pow_eq_nine hp h9).1
    omega
  have hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
      (π : E →* StatedProj (StatedSL 2 K)), Function.Surjective π → π.ker ≤ Subgroup.center E →
      Odd (Nat.card π.ker) → π.ker = ⊥ := fun E _ _ _ π hπ hC hodd =>
    (odd_psl_two_perfect_odd_cover_kernel hp2 hK π hπ hC hodd).1 h9
  have hdim : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (L' : Subgroup (GLV W)), Nonempty (StatedProj (StatedSL 2 K) ≃* ↥L') →
      (p ^ e - 1) / 2 ≤ Module.finrank (ZMod 2) W ∧ p ∣ Nat.card ↥L' := by
    intro W _ _ _ L' ⟨g⟩
    exact oddL2_finrank_bound hp hp2 (show StatedClassicalModel ↥L' .PSL 2 p e from
      ⟨hpar, K, instK, instF, hK, ⟨g.symm⟩⟩)
  have he : e = 1 ∨ e = 2 := by omega
  rcases he with rfl | rfl
  · rw [pow_one] at hK hq
    have hp11 : 11 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p <;> first | omega | (exfalso; norm_num at hp)
    refine h.false_of_cover_rank_dim' e' hCover (r := 2) (by norm_num)
      (fun _ B hc h2 => ?_) (ρ := 6) ?_ (by norm_num)
    · have := card_elemAbelian_mulAut_of_equiv_prime (p := p) (by omega) hK
        (MulEquiv.refl (StatedProj (StatedSL 2 K))) B hc h2
      exact this
    · intro W _ _ _ L' hg
      obtain ⟨hd, hdvd⟩ := hdim W L' hg
      rw [pow_one] at hd
      by_cases hp13 : 13 ≤ p
      · omega
      · have hp12 : p ≠ 12 := by
          rintro rfl
          norm_num at hp
        have hp11' : p = 11 := by omega
        subst hp11'
        have hord := orderOf_two_le_finrank_of_dvd_card L' hp2 hdvd
        rw [oddL2Big_orderOf_two_11] at hord
        omega
  · have hp5 : 5 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p
      norm_num at hp
    refine h.false_of_cover_rank_dim' e' hCover (r := 3) (by norm_num)
      (fun _ B hc h2 => ?_) (ρ := 12) ?_ (by norm_num)
    · exact card_elemAbelian_mulAut_of_equiv_prime_sq (p := p) hp5 hK
        (MulEquiv.refl (StatedProj (StatedSL 2 K))) B hc h2
    · intro W _ _ _ L' hg
      obtain ⟨hd, -⟩ := hdim W L' hg
      have : 25 ≤ p ^ 2 := by nlinarith
      omega

end

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
