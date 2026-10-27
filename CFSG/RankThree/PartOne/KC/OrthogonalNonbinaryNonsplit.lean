module

public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalNonbinaryData
public import CFSG.RankThree.PartOne.KC.OrthogonalQuarticNonsplit
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

section Restriction

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {Ã : Subgroup (orthDerived Q)}

theorem stable_lineFixSpace (hcomm : ∀ x y : Ã, x * y = y * x) (M : Subgroup Ã) (a : Ã) {v : V}
    (hv : v ∈ lineFixSpace M) : ((a : orthDerived Q) : V ≃ₗ[K] V) v ∈ lineFixSpace M := by
  rw [lineFixSpace_eq_fixSub, mem_fixSub] at hv ⊢
  intro m hm
  show orthRep Ã m (orthRep Ã a v) = orthRep Ã a v
  rw [← Module.End.mul_apply, ← map_mul, hcomm m a, map_mul, Module.End.mul_apply, hv m hm]

@[expose] noncomputable def restrictToSubspace (W : Submodule K V)
    (hW : ∀ g : Ã, W.map (((g : orthDerived Q) : V ≃ₗ[K] V) : V →ₗ[K] V) = W) :
    Ã →* (W ≃ₗ[K] W) where
  toFun g := LinearEquiv.ofSubmodules (((g : orthDerived Q) : V ≃ₗ[K] V)) W W (hW g)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

end Restriction

section Nonsplit

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {Ã : Subgroup (orthDerived Q)}

open _root_.Classical in
theorem not_split_four_aux (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hΓ : Nat.card Ã = p ^ 2) (hexp : ∀ x : Ã, x ^ p = 1)
    (hV0 : planeFixSpace Ã = ⊥) {M : Subgroup Ã} (hM : Nat.card M = p)
    (hc4 : orderOf (Nat.card K : ZMod p) = 4) (W : Submodule K V) (hdim : finrank K W = 4)
    (hWmap : ∀ g : Ã, W.map (((g : orthDerived Q) : V ≃ₗ[K] V) : V →ₗ[K] V) = W)
    (hMfix : ∀ m ∈ M, ∀ w ∈ W, ((m : orthDerived Q) : V ≃ₗ[K] V) w = w)
    (hQW : (polarBilin (Q.comp W.subtype)).Nondegenerate) :
    ¬ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ s ∈ S, (Q.comp W.subtype) s = 0 := by
  obtain ⟨b, hb⟩ : ∃ b : Ã, b ∉ M := by
    by_contra hall
    push Not at hall
    have htop : M = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.card_top, hΓ] at hM
    have := hp.one_lt
    nlinarith
  let bW : W ≃ₗ[K] W := restrictToSubspace W hWmap b
  have hQb : ∀ v, Q (((b : orthDerived Q) : V ≃ₗ[K] V) v) = Q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup b.1.2) v
  have hxO : bW ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    exact hQb w
  have hfix : ∀ w : W, bW w = w → w = 0 := by
    intro w hw
    let S : Subgroup Ã :=
      { carrier := {g | ((g : orthDerived Q) : V ≃ₗ[K] V) (w : V) = w}
        mul_mem' := fun {g h} hg hh => by
          show ((g : orthDerived Q) : V ≃ₗ[K] V) (((h : orthDerived Q) : V ≃ₗ[K] V) (w : V)) = w
          rw [show ((h : orthDerived Q) : V ≃ₗ[K] V) (w : V) = w from hh]
          exact hg
        one_mem' := rfl
        inv_mem' := fun {g} hg => by
          show ((g : orthDerived Q) : V ≃ₗ[K] V).symm (w : V) = w
          rw [LinearEquiv.symm_apply_eq]
          exact hg.symm }
    have hMS : M ≤ S := fun m hm => hMfix m hm w w.2
    have hbS : b ∈ S := congrArg Subtype.val hw
    have hS : S = ⊤ := by
      have hd1 : Nat.card M ∣ Nat.card S := Subgroup.card_dvd_of_le hMS
      have hd2 : Nat.card S ∣ p ^ 2 := hΓ ▸ Subgroup.card_subgroup_dvd_card S
      obtain ⟨i, hi, hiS⟩ := (Nat.dvd_prime_pow hp).mp hd2
      rw [hM, hiS] at hd1
      have hi1 : i ≠ 0 := by
        rintro rfl
        simp at hd1
        exact hp.one_lt.ne' hd1
      have hfinS : Finite S := Nat.finite_of_card_ne_zero (by rw [hiS]; positivity)
      by_cases hi2 : i = 2
      · rw [hi2] at hiS
        exact (Subgroup.card_eq_iff_eq_top S).mp (by rw [hiS, hΓ])
      · exfalso
        have hi1' : i = 1 := by omega
        rw [hi1', pow_one] at hiS
        have : M = S := Subgroup.eq_of_le_of_card_ge hMS (by rw [hiS, hM])
        exact hb (this ▸ hbS)
    have hmem : (w : V) ∈ planeFixSpace Ã := by
      rw [planeFixSpace_eq_fixSub, mem_fixSub]
      intro g _
      exact (hS ▸ Subgroup.mem_top g : g ∈ S)
    rw [hV0] at hmem
    exact Subtype.ext ((Submodule.mem_bot K).mp hmem)
  have hx1 : LinearMap.ker (bW.toLinearMap - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    apply hfix
    exact sub_eq_zero.mp hw
  have hbp : bW ^ p = 1 := by
    have : restrictToSubspace W hWmap (b ^ p) = 1 := by rw [hexp b]; exact map_one _
    rwa [map_pow] at this
  have hb1 : bW ≠ 1 := by
    intro h1
    obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hdim]; norm_num :
      0 < finrank K W)
    exact hw0 (hfix w (by rw [h1]; rfl))
  have hxp : orderOf bW = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hbp hb1
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  obtain ⟨f, hf, hK⟩ := CFSG.RankThree.PartOne.KCOrthogonalAut.exists_card_eq_pow K
  exact (quartic_prime_orthogonal_four_space_is_nonsplit hℓ hp hp3 hpl hf hK hc4 hdim
    (Q.comp W.subtype) hQW hxO hxp hx1).2.1

open _root_.Classical in
theorem not_split_four_of_active (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) (hD : KernelLineData Q p Ã) (hDims : KernelLineDims Q p Ã)
    {M : Subgroup Ã} (hM : Nat.card M = p) (hMa : lineSpace M ≠ ⊥)
    (hdim : finrank K (lineFixSpace M) = 4) :
    ¬ ∃ S : Submodule K (lineFixSpace M), finrank K S = 2 ∧
      ∀ s ∈ S, (Q.comp (lineFixSpace M).subtype) s = 0 := by
  obtain ⟨hpos, hdvd⟩ := hDims.dvd M hM hMa
  have hlcm0 : Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≠ 0 := fun h => by
    rw [h] at hdvd
    exact hpos.ne' (zero_dvd_iff.mp hdvd)
  have hlcm4 := four_le_lcm_of_not_dvd (Nat.card K) hpq hlcm0
  have h3 := three_le_orderOf_of_not_dvd (Nat.card K) hpq hlcm0
  have hVM4 : 4 ≤ finrank K (lineSpace M) := hlcm4.trans (Nat.le_of_dvd hpos hdvd)
  have hdisj0 : Disjoint (planeFixSpace Ã) (lineSpace M) :=
    hD.internal.submodule_iSupIndep.pairwiseDisjoint (i := none) (j := some ⟨M, hM⟩)
      (by simp)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace Ã) (lineSpace M)
  rw [← hDims.line_fix M hM, disjoint_iff.mp hdisj0, finrank_bot, hdim] at hsup
  have hV0 : planeFixSpace Ã = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hWV : lineFixSpace M = lineSpace M := by
    rw [hDims.line_fix M hM, hV0, bot_sup_eq]
  have hVM : finrank K (lineSpace M) = 4 := by rw [← hWV]; exact hdim
  have hc4 : orderOf (Nat.card K : ZMod p) = 4 := by
    rw [hVM] at hdvd
    have hcd : orderOf (Nat.card K : ZMod p) ∣ 4 := (Nat.dvd_lcm_left _ 2).trans hdvd
    have hcle : orderOf (Nat.card K : ZMod p) ≤ 4 := Nat.le_of_dvd (by norm_num) hcd
    generalize orderOf (Nat.card K : ZMod p) = c at *
    rcases (by omega : c = 3 ∨ c = 4) with rfl | rfl
    · exact absurd hcd (by norm_num)
    · rfl
  have hQW : (polarBilin (Q.comp (lineFixSpace M).subtype)).Nondegenerate := by
    rw [polarBilin_comp_subtype, hWV]
    exact hD.regular (some ⟨M, hM⟩)
  refine not_split_four_aux hp hp3 hpl hD.card hD.exp hV0 hM hc4 (lineFixSpace M) hdim
    (fun g => ?_) (fun m hm w hw => ?_) hQW
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact stable_lineFixSpace hD.comm M g hw
    · intro w hw
      refine ⟨(((g⁻¹ : Ã) : orthDerived Q) : V ≃ₗ[K] V) w,
        stable_lineFixSpace hD.comm M g⁻¹ hw, ?_⟩
      show ((g : orthDerived Q) : V ≃ₗ[K] V) ((((g⁻¹ : Ã) : orthDerived Q) : V ≃ₗ[K] V) w) = w
      exact (LinearEquiv.apply_symm_apply _ w)
  · rw [lineFixSpace_eq_fixSub, mem_fixSub] at hw
    exact hw m hm

end Nonsplit

end CFSG.RankThree.PartOne.KCOrthogonal
