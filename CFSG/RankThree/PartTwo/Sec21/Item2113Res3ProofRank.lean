module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofHJ
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRankCases
import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRankTools
import CFSG.ClassicalInvolution.Basic
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofNormal

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normal_map_of_le_normalizer {H I : Subgroup G} (hIH : I ≤ H)
    (hN : H ≤ normalizer ((I ⊔ inSubgroup (aschbacherSolvableCore 3) H : Subgroup G) : Set G)) :
    ((I.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))).Normal := by
  set θ := aschbacherSolvableCore 3 H
  set π := QuotientGroup.mk' θ with hπ
  have hθI : I ≤ normalizer (inSubgroup (aschbacherSolvableCore 3) H : Set G) :=
    le_normalizer_theta (hIH.trans le_normalizer)
  constructor
  rintro _ ⟨i, hi, rfl⟩ g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective θ g
  have hmem : (h : G) * i * (h : G)⁻¹ ∈ I ⊔ inSubgroup (aschbacherSolvableCore 3) H :=
    (mem_normalizer_iff.mp (hN h.2) i).mp (mem_sup_left (mem_subgroupOf.mp hi))
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hθI] at hmem
  obtain ⟨i', hi', _, ⟨t, ht, rfl⟩, he⟩ := hmem
  refine ⟨⟨i', hIH hi'⟩, mem_subgroupOf.mpr hi', ?_⟩
  have heq : h * i * h⁻¹ = ⟨i', hIH hi'⟩ * t := Subtype.ext he.symm
  have ht1 : π t = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ht
  rw [← map_inv, ← map_mul, ← map_mul, heq, map_mul, ht1, mul_one]

theorem exists_component_of_conj {I : Subgroup G} {c d x : G} (hx : x * c * x⁻¹ = d)
    (hdI : d ∈ I) (hIC : I ≤ centralizer ({d} : Set G))
    (hN : centralizer ({d} : Set G) ≤ normalizer ((I ⊔ inSubgroup (aschbacherSolvableCore 3)
      (centralizer ({d} : Set G)) : Subgroup G) : Set G))
    (hq : IsQuasisimple (lBar I)) {w : lBar I} (hw3 : w ^ 3 = 1) (hw : w ∉ center (lBar I)) :
    ∃ N : Subgroup (centralizer ({c} : Set G) ⧸
        aschbacherSolvableCore 3 (centralizer ({c} : Set G))),
      IsComponent N ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 (centralizer ({c} : Set G)))
        ⟨c, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ N ∧
      ∃ y ∈ N, y ^ 3 = 1 ∧ ∃ n ∈ N, y * n ≠ n * y := by
  set Hd := centralizer ({d} : Set G) with hHd
  set Hc := centralizer ({c} : Set G)
  set πd := QuotientGroup.mk' (aschbacherSolvableCore 3 Hd)
  set πc := QuotientGroup.mk' (aschbacherSolvableCore 3 Hc)
  set I₀ := I.subgroupOf Hd
  have hIn := normal_map_of_le_normalizer hIC hN
  obtain ⟨η, -⟩ := exists_mulEquiv_map_of_normal I₀ hIn
  set e₀ := subgroupOfEquivOfLe hIC
  let e₁ : lBar I ≃* I₀ ⧸ aschbacherSolvableCore 3 I₀ :=
    QuotientGroup.congr _ _ e₀.symm (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀.symm)
  have h1 : x⁻¹ * d * x⁻¹⁻¹ = c := by rw [← hx]; group
  have hκ : Hd.map (MulAut.conj x⁻¹).toMonoidHom = Hc := by
    rw [hHd, ClassicalInvolution.map_conj_centralizer_singleton, h1]
  let κ : Hd ≃* Hc := ((MulAut.conj x⁻¹).subgroupMap Hd).trans (MulEquiv.subgroupCongr hκ)
  let Φ : (Hd ⧸ aschbacherSolvableCore 3 Hd) ≃* (Hc ⧸ aschbacherSolvableCore 3 Hc) :=
    QuotientGroup.congr _ _ κ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three κ)
  set N := (I₀.map πd).map Φ.toMonoidHom
  let ε : lBar I ≃* N :=
    e₁.trans (η.trans ((I₀.map πd).equivMapOfInjective Φ.toMonoidHom Φ.injective))
  have hdHd : d ∈ Hd := mem_centralizer_singleton_iff.mpr rfl
  have hκd : κ ⟨d, hdHd⟩ = ⟨c, mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext h1
  refine ⟨N, ⟨LocalCores.isQuasisimple_of_mulEquiv ε hq,
    (hIn.map _ Φ.surjective).isSubnormal⟩, ?_, ε w, (ε w).2, ?_, ?_⟩
  · refine ⟨πd ⟨d, hdHd⟩, ⟨⟨d, hdHd⟩, mem_subgroupOf.mpr hdI, rfl⟩, ?_⟩
    change πc (κ ⟨d, hdHd⟩) = _
    rw [hκd]
  · rw [← coe_pow, ← map_pow, hw3, map_one, coe_one]
  · obtain ⟨v, hv⟩ : ∃ v, v * w ≠ w * v := by
      simpa only [mem_center_iff, not_forall] using hw
    refine ⟨ε v, (ε v).2, fun h => hv (ε.injective ?_)⟩
    rw [map_mul, map_mul]
    exact Subtype.ext h.symm

section Certs


theorem card_inf_eq_nine (h211 : Item211) (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) : Nat.card (A ⊓ L : Subgroup G) = 9 := by
  open Item2113Res2Proof in
  rcases starOf_cases_of_isList218 h211 hpair hL with ⟨-, hS⟩ | ⟨-, hS⟩ | ⟨hJ, hS⟩
  · rcases hS with hS | hS
    · obtain ⟨e⟩ := hS
      obtain ⟨h3, h1, hz2, hz1, -⟩ := dihedral_six_data
      obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
      obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 dihedral_six_central
      exact (card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1 hζc).1
    · obtain ⟨e⟩ := hS
      obtain ⟨h3, h1, hz2, hz1, -⟩ := gl_two_three_data
      obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
      obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 gl_two_three_central
      exact (card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1 hζc).1
  · obtain ⟨e⟩ := hS
    obtain ⟨h3, h1, hz2, hz1, -⟩ := dihedral_six_data
    obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
    obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 dihedral_six_central
    exact (card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1 hζc).1
  · exact item2113ChoiceHJ_of h211 h45 G A E U c L hpair hJ hS

theorem false_of_component_at (h211 : Item211) (h45 : Sec4.Item4_5) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    {N : Subgroup (centralizer ({c} : Set G) ⧸
      aschbacherSolvableCore 3 (centralizer ({c} : Set G)))} (hN : IsComponent N)
    (hcN : QuotientGroup.mk' (aschbacherSolvableCore 3 (centralizer ({c} : Set G)))
      ⟨c, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ N)
    {y : centralizer ({c} : Set G) ⧸ aschbacherSolvableCore 3 (centralizer ({c} : Set G))}
    (hyN : y ∈ N) (hy3 : y ^ 3 = 1) (hyc : ∃ n ∈ N, y * n ≠ n * y) : False := by
  set H := centralizer ({c} : Set G)
  set θ := aschbacherSolvableCore 3 H
  set π := QuotientGroup.mk' θ with hπ
  obtain ⟨hcA, hc1, hLc, hAL, -⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLθ : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hAe := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by
    rw [Item2113Proof.card_eq_of_isList218 h211 hpair hL]; norm_num
  have h9 := card_inf_eq_nine h211 h45 hpair hL
  obtain ⟨-, hL₀⟩ := mem_thetaComponentsIn_iff.mp hLθ
  set L₀ := L.subgroupOf H
  have hLb : IsComponent (L₀.map π) := isComponent_map_of_mem_thetaComponents Nat.prime_three hL₀
  have hZ : center (L₀.map π) = ⊥ := by
    obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hL₀.2.1
    set e := subgroupOfEquivOfLe hLc
    exact Item2113Proof.center_eq_bot_of_mulEquiv
      (Item2113Proof.center_lBar_eq_bot_of_isList218 hL)
      (η.symm.trans (QuotientGroup.congr _ _ e
        (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)))
  obtain ⟨E₀, hE₀, hE₀A, hLE₀⟩ := mem_lZeroUnion_iff.mp
    (lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1))
  have hE₀eq : E₀ = A := eq_of_le_of_card_ge hE₀A (by rw [h27, hE₀.2.1])
  rw [hE₀eq] at hLE₀
  obtain ⟨-, UL, hUL, hULθ⟩ := hLE₀
  obtain ⟨hULL, hUL2, hAUL⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hUL
  set U₀ := UL.subgroupOf H with hU₀
  have hUbL : U₀.map π ≤ L₀.map π :=
    map_mono fun u hu => mem_subgroupOf.mpr (hULL (mem_subgroupOf.mp hu))
  have hUb2 : IsPGroup 2 (U₀.map π) :=
    (hUL2.of_equiv (subgroupOfEquivOfLe (hULL.trans hLc)).symm).map π
  have hUb1 : U₀.map π ≠ ⊥ := by
    intro hbot
    apply hULθ
    have hU₀θ : U₀ ≤ θ := by
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
      exact hbot
    have hULθL : UL ≤ inSubgroup (aschbacherSolvableCore 3) L := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hLθ]
      refine le_inf hULL ?_
      rw [← map_subgroupOf_eq_of_le (hULL.trans hLc)]
      exact map_mono hU₀θ
    exact (commutator_mono hULθL le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (le_normalizer_theta hAL))
  set F₀ := (A ⊓ L).subgroupOf H with hF₀
  have hF₀e : CFSG.Assembly.IsElemAbelian 3 F₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val (hAe.1.1.comm ⟨(a : G), (mem_subgroupOf.mp a.2).1⟩
        ⟨(b : G), (mem_subgroupOf.mp b.2).1⟩)
      exact h
    · exact hAe.2 _ (mem_subgroupOf.mp ha).1
  have hF₀c : Nat.card F₀ = 9 := by
    rw [hF₀, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right.trans hLc)).toEquiv, h9]
  have hF₀3 : IsPGroup 3 F₀ := IsPGroup.of_card (n := 2) (by rw [hF₀c]; norm_num)
  have hFL : F₀.map π ≤ L₀.map π :=
    map_mono fun u hu => mem_subgroupOf.mpr (mem_subgroupOf.mp hu).2
  have hFe : CFSG.Assembly.IsElemAbelian 3 (F₀.map π) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
      obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
      change π a' * π b' = π b' * π a'
      have h := congrArg Subtype.val (hF₀e.1.1.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg π h
    · rintro _ ⟨a', ha', rfl⟩
      rw [← map_pow, hF₀e.2 a' ha', map_one]
  have hF9 : Nat.card (F₀.map π) = 9 := by
    have h := Nat.card_image_of_injOn (injOn_mk_of_isPGroup Nat.prime_three hF₀3)
    rw [← hF₀c]
    exact h
  have hFU : F₀.map π ≤ normalizer ((U₀.map π : Subgroup (H ⧸ θ)) : Set (H ⧸ θ)) := by
    refine le_trans (map_mono fun a ha => ?_) (le_normalizer_map π)
    rw [mem_normalizer_iff]
    intro u
    simp only [hU₀, mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hAUL (mem_subgroupOf.mp ha).1) u
  have hcH : c ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hz : π ⟨c, hcH⟩ ∈ center (H ⧸ θ) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective θ g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hz3 : π ⟨c, hcH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcH⟩ : H) ^ 3 = 1 := Subtype.ext hc3
    rw [this, map_one]
  have hz1 : π ⟨c, hcH⟩ ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨c, hcH⟩ : H) = 3 :=
      orderOf_eq_prime (Subtype.ext hc3) fun h => hc1 (congrArg Subtype.val h)
    have hdvd : orderOf (⟨c, hcH⟩ : H) ∣ Nat.card θ := Subgroup.orderOf_dvd_natCard θ h1
    rw [hord] at hdvd
    exact three_not_dvd_card_aschbacherSolvableCore hdvd
  have hrank : CFSG.Assembly.RankThreeEven.localRank 3 (H ⧸ θ) ≤ 3 := by
    have h1 : CFSG.Assembly.RankThreeEven.localRank 3 (H ⧸ θ) ≤
        CFSG.Assembly.RankThreeEven.localRank 3 H :=
      (theta_quotient_core_and_ranks (G := H)).2.2.1.2.1
    have h2 := localRank_subgroup_le Nat.prime_three H
    have h3 := hpair.standing.toTheoremFourHyp.localRank_three
    omega
  exact false_of_components hrank hLb hZ hUbL hUb1 hUb2 hFL hFe hF9 hFU hz hz1 hz3 hN hcN hyN
    hy3 hyc

theorem item2112Rank_of (h211 : Item211) (h45 : Sec4.Item4_5) : Item2112Rank := by
  intro G _ _ A E U c L E' U' b K hpair hL hpair' hK d hdA hd1 hdcen h219 h2101 x hx
  obtain ⟨hdI, hcases⟩ := h219
  obtain ⟨hq, w, hw3, hw⟩ := lBar_facts_of_item219 hcases
  have hIC : iOf218 K d ≤ centralizer ({d} : Set G) := (map_subtype_le _).trans inf_le_right
  obtain ⟨N, hN, hcN, y, hyN, hy3, hyc⟩ := exists_component_of_conj hx hdI hIC h2101 hq hw3 hw
  exact false_of_component_at h211 h45 hpair hL hN hcN hyN hy3 hyc

end Certs

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof
