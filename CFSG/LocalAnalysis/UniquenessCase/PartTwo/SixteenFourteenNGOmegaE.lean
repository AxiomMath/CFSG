module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGOmegaFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGOmegaRot
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.ClassicalGroups.Orthogonal

open scoped IsMulCommutative

private def s1614_oe_mulHom {ι K : Type} [Field K] (u : (ι → K) ≃ₗ[K] (ι → K)) :
    Multiplicative (ι → K) →* Multiplicative (ι → K) where
  toFun y := Multiplicative.ofAdd (u (Multiplicative.toAdd y))
  map_one' := by simp
  map_mul' x y := by
    rw [toAdd_mul, map_add, ofAdd_add]

private lemma s1614_oe_zpow_eq_one_or_self {G : Type*} [Group G] {v z : G} (hv : v ^ 2 = 1)
    (hz : z ∈ Subgroup.zpowers v) : z = 1 ∨ z = v := by
  have hv2 : v ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hv]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← hk, zpow_eq_zpow_emod k hv2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

theorem s1614_om_X_card {ι K : Type} [Field K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    {a a' : ι → K} (ha : Q a = 1) (ha' : Q a' = 1) (h : QuadraticMap.polar Q a a' = 1) :
    Nat.card ↥(Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'}) = 4 := by
  classical
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.map_zero] at ha
    exact zero_ne_one ha
  have ha'0 : a' ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.map_zero] at ha'
    exact zero_ne_one ha'
  have hane : a ≠ a' := by
    intro h0
    rw [h0, QuadraticMap.polar_self, CharTwo.two_nsmul] at h
    exact zero_ne_one h
  have h2a : a + a = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have h2a' : a' + a' = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (a' i)
  have hsq_a : Multiplicative.ofAdd a ^ 2 = 1 := by
    rw [pow_two, ← ofAdd_add, h2a]
    rfl
  have hsq_a' : Multiplicative.ofAdd a' ^ 2 = 1 := by
    rw [pow_two, ← ofAdd_add, h2a']
    rfl
  have hne_a : Multiplicative.ofAdd a ≠ 1 := by
    intro hh
    exact ha0 (Multiplicative.ofAdd.injective hh)
  have hne_a' : Multiplicative.ofAdd a' ≠ 1 := by
    intro hh
    exact ha'0 (Multiplicative.ofAdd.injective hh)
  have hne : Multiplicative.ofAdd a ≠ Multiplicative.ofAdd a' := by
    intro hh
    exact hane (Multiplicative.ofAdd.injective hh)
  have hX : Subgroup.closure ({Multiplicative.ofAdd a, Multiplicative.ofAdd a'} :
      Set (Multiplicative (ι → K))) =
      Subgroup.zpowers (Multiplicative.ofAdd a) ⊔
        Subgroup.zpowers (Multiplicative.ofAdd a') := by
    rw [show ({Multiplicative.ofAdd a, Multiplicative.ofAdd a'} :
        Set (Multiplicative (ι → K))) =
        {Multiplicative.ofAdd a} ∪ {Multiplicative.ofAdd a'} by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  have hU : Nat.card ↥(Subgroup.zpowers (Multiplicative.ofAdd a)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hsq_a hne_a]
  have hW : Nat.card ↥(Subgroup.zpowers (Multiplicative.ofAdd a')) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hsq_a' hne_a']
  have hinf : Subgroup.zpowers (Multiplicative.ofAdd a) ⊓
      Subgroup.zpowers (Multiplicative.ofAdd a') = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzu, hzw⟩ := Subgroup.mem_inf.1 hz
    obtain h | h := s1614_oe_zpow_eq_one_or_self hsq_a hzu
    · exact h
    · obtain h' | h' := s1614_oe_zpow_eq_one_or_self hsq_a' hzw
      · exact absurd (h.symm.trans h') hne_a
      · exact absurd (h.symm.trans h') hne
  have hinfcard : Nat.card ↥(Subgroup.zpowers (Multiplicative.ofAdd a) ⊓
      Subgroup.zpowers (Multiplicative.ofAdd a')) = 1 := by
    rw [hinf, Subgroup.card_bot]
  have hmain := card_sup_mul_card_inf (Subgroup.zpowers (Multiplicative.ofAdd a))
    (Subgroup.zpowers (Multiplicative.ofAdd a'))
  rw [hU, hW, hinfcard, mul_one] at hmain
  rw [hX]
  norm_num at hmain ⊢
  exact hmain

theorem s1614_om_E {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Q : QuadraticForm K (ι → K)) {a a' x x' : ι → K} (hF : S1614OmFrame Q a a' x x') :
    ∃ E : Subgroup (Matrix.GeneralLinearGroup ι K), E ≤ StatedOmega ⇑Q ∧ IsElemAbelian 3 E ∧
      9 ≤ Nat.card ↥E ∧
      ∀ e ∈ E, ∀ y ∈ Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'},
        Multiplicative.ofAdd ((e : Matrix ι ι K).mulVec (Multiplicative.toAdd y)) ∈
          Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'} := by
  classical
  obtain ⟨ha, ha', hx, hx', haa', hxx', hax, hax', ha'x, ha'x'⟩ := hF
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.map_zero] at ha
    exact zero_ne_one ha
  have ha'0 : a' ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.map_zero] at ha'
    exact zero_ne_one ha'
  have hane : a ≠ a' := by
    intro h0
    rw [h0, QuadraticMap.polar_self, CharTwo.two_nsmul] at haa'
    exact zero_ne_one haa'
  have hxne : x ≠ x' := by
    intro h0
    rw [h0, QuadraticMap.polar_self, CharTwo.two_nsmul] at hxx'
    exact zero_ne_one hxx'
  let g : (ι → K) ≃ₗ[K] (ι → K) := s1614_rot Q a a'
  let h : (ι → K) ≃ₗ[K] (ι → K) := s1614_rot Q x x'
  have hg3 : g ^ 3 = 1 := s1614_rot_pow_three ha ha' haa'
  have hh3 : h ^ 3 = 1 := s1614_rot_pow_three hx hx' hxx'
  have hgh : Commute g h := s1614_rot_commute hax hax' ha'x ha'x'
  have hga : g a = a' := s1614_rot_apply_left ha ha' haa'
  have hga' : g a' = a + a' := s1614_rot_apply_right ha ha' haa'
  have hgx : g x = x := s1614_rot_apply_of_polar_eq_zero hax ha'x
  have hgx' : g x' = x' := s1614_rot_apply_of_polar_eq_zero hax' ha'x'
  have hhx : h x = x' := s1614_rot_apply_left hx hx' hxx'
  have hhx' : h x' = x + x' := s1614_rot_apply_right hx hx' hxx'
  have hxa : QuadraticMap.polar Q x a = 0 := (QuadraticMap.polar_comm Q a x).symm.trans hax
  have hx'a : QuadraticMap.polar Q x' a = 0 := (QuadraticMap.polar_comm Q a x').symm.trans hax'
  have hxa' : QuadraticMap.polar Q x a' = 0 := (QuadraticMap.polar_comm Q a' x).symm.trans ha'x
  have hx'a' : QuadraticMap.polar Q x' a' = 0 :=
    (QuadraticMap.polar_comm Q a' x').symm.trans ha'x'
  have hha : h a = a := s1614_rot_apply_of_polar_eq_zero hxa hx'a
  have hha' : h a' = a' := s1614_rot_apply_of_polar_eq_zero hxa' hx'a'
  have hgne : g ≠ 1 := by
    intro hg1
    have hgaa : g a = a := by rw [hg1]; rfl
    rw [hga] at hgaa
    exact hane hgaa.symm
  have hhne : h ≠ 1 := by
    intro hh1
    have hhxx : h x = x := by rw [hh1]; rfl
    rw [hhx] at hhxx
    exact hxne hhxx.symm
  let E₀ : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := Subgroup.closure {g, h}
  let E : Subgroup (Matrix.GeneralLinearGroup ι K) :=
    E₀.comap (toLinEquiv ι K).toMonoidHom
  have hE0comm : IsMulCommutative E₀ := by
    change IsMulCommutative (Subgroup.closure ({g, h} : Set ((ι → K) ≃ₗ[K] (ι → K))))
    apply Subgroup.isMulCommutative_closure
    intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · exact hgh
    · exact hgh.symm
    · exact absurd rfl huv
  have hE0pow : ∀ y ∈ E₀, y ^ 3 = 1 := by
    intro y hy
    change y ∈ Subgroup.closure ({g, h} : Set ((ι → K) ≃ₗ[K] (ι → K))) at hy
    refine Subgroup.closure_induction (p := fun z _ => z ^ 3 = 1) ?_ ?_ ?_ ?_ hy
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hg3
      · exact hh3
    · simp
    · intro p q hp hq ihp ihq
      have hc : Commute p q := by
        rw [commute_iff_eq]
        simpa using congrArg Subtype.val
          (hE0comm.is_comm.comm (⟨p, hp⟩ : E₀) (⟨q, hq⟩ : E₀))
      rw [hc.mul_pow 3, ihp, ihq, one_mul]
    · intro p hp ihp
      rw [inv_pow, ihp, inv_one]
  have hE_omega : E ≤ StatedOmega ⇑Q := by
    have hE0_le : E₀ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
      change Subgroup.closure ({g, h} : Set ((ι → K) ≃ₗ[K] (ι → K))) ≤ _
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact s1614_rot_mem_commutator ha ha' haa'
      · exact s1614_rot_mem_commutator hx hx' hxx'
    rw [show E = E₀.comap (toLinEquiv ι K).toMonoidHom from rfl,
      statedOmega_eq_comap (Q := Q) (Q₀ := ⇑Q) rfl]
    exact Subgroup.comap_mono hE0_le
  have hEab : IsElemAbelian 3 E := by
    constructor
    · refine ⟨⟨fun u v => Subtype.ext ((toLinEquiv ι K).injective ?_)⟩⟩
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (hE0comm.is_comm.comm
        (⟨(toLinEquiv ι K) u.1, Subgroup.mem_comap.1 u.2⟩ : E₀)
        (⟨(toLinEquiv ι K) v.1, Subgroup.mem_comap.1 v.2⟩ : E₀))
    · intro u hu
      apply (toLinEquiv ι K).injective
      rw [map_pow, map_one]
      exact hE0pow ((toLinEquiv ι K) u) (Subgroup.mem_comap.1 hu)
  have hcardE : Nat.card ↥E = Nat.card ↥E₀ := by
    rw [show E = E₀.comap (toLinEquiv ι K).toMonoidHom from rfl,
      Subgroup.comap_equiv_eq_map_symm' (toLinEquiv ι K) E₀]
    exact Subgroup.card_map_of_injective (K := E₀)
      (f := (toLinEquiv ι K).symm.toMonoidHom) (toLinEquiv ι K).symm.injective
  have hE0card : Nat.card ↥E₀ = 9 := by
    have hE0eq : E₀ = Subgroup.zpowers g ⊔ Subgroup.zpowers h := by
      change Subgroup.closure ({g, h} : Set ((ι → K) ≃ₗ[K] (ι → K))) = _
      rw [show ({g, h} : Set ((ι → K) ≃ₗ[K] (ι → K))) = {g} ∪ {h} by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
      rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
    have hg2a : (g ^ 2) a = a + a' := by
      calc (g ^ 2) a = g (g a) := by rw [pow_two, LinearEquiv.mul_apply]
        _ = g a' := by rw [hga]
        _ = a + a' := hga'
    let StabA : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) :=
      { carrier := {u | u a = a}
        one_mem' := LinearEquiv.refl_apply a
        mul_mem' := by
          intro u v hu hv
          show (u * v) a = a
          rw [LinearEquiv.mul_apply, hv, hu]
        inv_mem' := by
          intro u hu
          show u⁻¹ a = a
          have h1 : u⁻¹ (u a) = a := by
            rw [← LinearEquiv.mul_apply, inv_mul_cancel]
            exact LinearEquiv.refl_apply a
          rw [hu] at h1
          exact h1 }
    have hhStabA : h ∈ StabA := hha
    have hgStabA : g ∉ StabA := by
      intro hmem
      change g a = a at hmem
      rw [hga] at hmem
      exact hane hmem.symm
    have hg2StabA : g ^ 2 ∉ StabA := by
      intro hmem
      change (g ^ 2) a = a at hmem
      rw [hg2a] at hmem
      exact ha'0 (add_left_cancel (by rw [hmem, add_zero]))
    have hgfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hg3⟩
    have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hgne
    have hinf : Subgroup.zpowers g ⊓ Subgroup.zpowers h = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      obtain ⟨hzg, hzh⟩ := Subgroup.mem_inf.1 hz
      have hzStabA : z ∈ StabA := (Subgroup.zpowers_le.mpr hhStabA) hzh
      have hzrange : z ∈ (Finset.range (orderOf g)).image (g ^ ·) := by
        rw [← IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hgfin]
        exact hzg
      rw [hgo] at hzrange
      simp only [Finset.mem_image, Finset.mem_range] at hzrange
      obtain ⟨i, hi, hiz⟩ := hzrange
      interval_cases i
      · rw [← hiz]; simp
      · exfalso
        apply hgStabA
        rw [← hiz] at hzStabA
        simpa using hzStabA
      · exfalso
        apply hg2StabA
        rw [← hiz] at hzStabA
        simpa using hzStabA
    haveI : IsMulCommutative ↥E₀ := hE0comm
    let U : Subgroup ↥E₀ := (Subgroup.zpowers g).subgroupOf E₀
    let W : Subgroup ↥E₀ := (Subgroup.zpowers h).subgroupOf E₀
    have hle_g : Subgroup.zpowers g ≤ E₀ :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hle_h : Subgroup.zpowers h ≤ E₀ :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hUcard : Nat.card U = 3 := by
      change Nat.card ↥((Subgroup.zpowers g).subgroupOf E₀) = 3
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_g).toEquiv, Nat.card_zpowers, hgo]
    have hWcard : Nat.card W = 3 := by
      change Nat.card ↥((Subgroup.zpowers h).subgroupOf E₀) = 3
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_h).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime hh3 hhne]
    have hsup : U ⊔ W = ⊤ := by
      change (Subgroup.zpowers g).subgroupOf E₀ ⊔ (Subgroup.zpowers h).subgroupOf E₀ = ⊤
      rw [← Subgroup.subgroupOf_sup hle_g hle_h, hE0eq, Subgroup.subgroupOf_self]
    have hinfUW : U ⊓ W = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      obtain ⟨hzu, hzw⟩ := Subgroup.mem_inf.1 hz
      rw [Subgroup.mem_subgroupOf] at hzu hzw
      have hz' : (z : (ι → K) ≃ₗ[K] (ι → K)) ∈
          Subgroup.zpowers g ⊓ Subgroup.zpowers h := ⟨hzu, hzw⟩
      rw [hinf, Subgroup.mem_bot] at hz'
      exact Subtype.ext hz'
    have hmain := card_sup_mul_card_inf U W
    rw [hsup, hinfUW, Subgroup.card_top, Subgroup.card_bot, mul_one, hUcard, hWcard] at hmain
    norm_num at hmain
    exact hmain
  have hE9 : 9 ≤ Nat.card ↥E := by
    rw [hcardE, hE0card]
  have hstab : ∀ e ∈ E,
      ∀ y ∈ Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'},
        Multiplicative.ofAdd ((e : Matrix ι ι K).mulVec (Multiplicative.toAdd y)) ∈
          Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'} := by
    let X : Subgroup (Multiplicative (ι → K)) :=
      Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'}
    let Stab : Submonoid ((ι → K) ≃ₗ[K] (ι → K)) :=
      { carrier := {u | ∀ y ∈ X, Multiplicative.ofAdd (u (Multiplicative.toAdd y)) ∈ X}
        one_mem' := by
          intro y hy
          simpa using hy
        mul_mem' := by
          intro u v hu hv y hy
          show Multiplicative.ofAdd ((u * v) (Multiplicative.toAdd y)) ∈ X
          rw [LinearEquiv.mul_apply]
          exact hu _ (hv y hy) }
    have hgStab : g ∈ Stab := by
      intro y hy
      have hle : X ≤ X.comap (s1614_oe_mulHom g) := by
        change Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'} ≤
          X.comap (s1614_oe_mulHom g)
        rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz
        · rw [hz]
          show Multiplicative.ofAdd (g (Multiplicative.toAdd (Multiplicative.ofAdd a))) ∈ X
          rw [toAdd_ofAdd, hga]
          exact Subgroup.subset_closure (by simp)
        · rw [hz]
          show Multiplicative.ofAdd (g (Multiplicative.toAdd (Multiplicative.ofAdd a'))) ∈ X
          rw [toAdd_ofAdd, hga', ofAdd_add]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
      show s1614_oe_mulHom g y ∈ X
      exact hle hy
    have hhStab : h ∈ Stab := by
      intro y hy
      have hle : X ≤ X.comap (s1614_oe_mulHom h) := by
        change Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'} ≤
          X.comap (s1614_oe_mulHom h)
        rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz
        · rw [hz]
          show Multiplicative.ofAdd (h (Multiplicative.toAdd (Multiplicative.ofAdd a))) ∈ X
          rw [toAdd_ofAdd, hha]
          exact Subgroup.subset_closure (by simp)
        · rw [hz]
          show Multiplicative.ofAdd (h (Multiplicative.toAdd (Multiplicative.ofAdd a'))) ∈ X
          rw [toAdd_ofAdd, hha']
          exact Subgroup.subset_closure (by simp)
      show s1614_oe_mulHom h y ∈ X
      exact hle hy
    have hStab_le : Submonoid.closure ({g, h} : Set ((ι → K) ≃ₗ[K] (ι → K))) ≤ Stab := by
      rw [Submonoid.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact hgStab
      · exact hhStab
    have hE0sub : E₀.toSubmonoid = Submonoid.closure ({g, h} :
        Set ((ι → K) ≃ₗ[K] (ι → K))) := by
      change (Subgroup.closure ({g, h} : Set ((ι → K) ≃ₗ[K] (ι → K)))).toSubmonoid = _
      exact Subgroup.closure_toSubmonoid_of_isOfFinOrder (s := {g, h}) (by
        intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hg3⟩
        · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hh3⟩)
    intro e he y hy
    have hTe : (toLinEquiv ι K) e ∈ E₀ := Subgroup.mem_comap.1 he
    have hTe' : (toLinEquiv ι K) e ∈ Submonoid.closure ({g, h} :
        Set ((ι → K) ≃ₗ[K] (ι → K))) := by
      rw [← hE0sub]
      exact hTe
    have hTeStab : (toLinEquiv ι K) e ∈ Stab := hStab_le hTe'
    have hthis : Multiplicative.ofAdd ((toLinEquiv ι K) e (Multiplicative.toAdd y)) ∈ X :=
      hTeStab y hy
    rw [toLinEquiv_apply] at hthis
    exact hthis
  exact ⟨E, hE_omega, hEab, hE9, hstab⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
