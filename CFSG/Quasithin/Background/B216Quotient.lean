module

public import CFSG.Quasithin.Background.B2FactorizationSolvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

section Quot

variable [Finite G] {V H T : Subgroup G} (hV : IsElemAbelian 2 V)

theorem structure_of_not_le_of_quot (hred : IsTwoReducedIn H V)
    (hsolvX : Group.IsSolvable ↥(autI hV H))
    (hT : IsSylowTwoOf T H) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ I : Finset (Subgroup (MulAut (IntMod V hV))),
      IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) ∧
      autI hV (thompsonJ H) = ⨆ L ∈ I, L ∧
      (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
      (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
      (∀ L ∈ I, ActsAsNaturalL2 L (commV L)) ∧
      fixV (autI hV (thompsonJ H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
      fixV (autI hV (thompsonJ H)) ⊓ ⨆ L ∈ I, commV L = ⊥ ∧
      (∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥) ∧
      (∀ g ∈ autI hV H, ∀ L ∈ I, B1.conjAut g L ∈ I ∧
        (commV L).map g.toMonoidHom = commV (B1.conjAut g L)) := by
  have hVH : V ≤ H := hred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h)
  obtain ⟨-, hstable, hNeq, -⟩ := B2_7_of_not_le hV hVH hHN hJH
  have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 => eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
  have hJX := B1.closure_transvectionsIn_le (autI hV H)
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn (autI hV H))) :=
    B1.solvable_of_le hJX hsolvX
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn (autI hV H)))) =
      Subgroup.closure (transvectionsIn (autI hV H)) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hW hsolvJ hOJ hcl
  obtain ⟨I, hI𝓗, hJPeq, hsylI, -⟩ := hb.stable_decomposition hW hsolvX hO2 hstable
  have hN : autI hV (thompsonJ H) = ⨆ L ∈ I, L := hNeq.trans hJPeq
  have hNnorm : ∀ g ∈ autI hV H, B1.conjAut g (autI hV (thompsonJ H)) = autI hV (thompsonJ H) := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hg
    have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := y.2
    rw [conjAut_eq_map, autI_cjSub hV hyN (thompsonJ H),
      cjSub_eq_of_mem_normalizer (normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hy))]
  have hdec := hb.decomp hW I hI𝓗
  refine ⟨I, ?_, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hTs := isSylowTwoOf_autI hV hHN hT
    have hNX : autI hV (thompsonJ H) ≤ autI hV H := autI_mono hV (thompsonJ_le_self H)
    have hTsN : autI hV T ≤ Subgroup.normalizer
        ((autI hV (thompsonJ H) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
      intro t ht
      refine Subgroup.mem_normalizer_iff''.2 fun x => ?_
      rw [← B1.mem_conjAut, hNnorm t (autI_mono hV hT.1 ht)]
    have hTN : IsSylowTwoOf (autI hV T ⊓ autI hV (thompsonJ H)) (autI hV (thompsonJ H)) :=
      ⟨inf_le_right, (isPGroup_autI hV hT.2.1 (hT.1.trans hHN)).to_le inf_le_left,
        not_two_dvd_relIndex_inf_of_normalizer hTs.1 hNX hTs.2.2 hTsN⟩
    have hLN : ∀ L ∈ I, autI hV (thompsonJ H) ≤
        Subgroup.normalizer ((L : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
      intro L hL
      rw [hN]
      refine iSup₂_le fun L' hL' => ?_
      by_cases hLL : L' = L
      · rw [hLL]
        exact Subgroup.le_normalizer
      · refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((L : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))))
        intro a ha
        exact Subgroup.mem_centralizer_iff.2 fun b hb' =>
          (hb.comm L' (hI𝓗 hL') L (hI𝓗 hL) hLL a ha b hb').symm
    have hLleN : ∀ L ∈ I, L ≤ autI hV (thompsonJ H) := fun L hL => by
      rw [hN]
      exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ I) => K) L hL
        le_rfl
    have hSL : ∀ L ∈ I, IsSylowTwoOf (autI hV T ⊓ L) L := by
      intro L hL
      have h := not_two_dvd_relIndex_inf_of_normalizer
        (S := autI hV T ⊓ autI hV (thompsonJ H)) (D := L) (K := autI hV (thompsonJ H)) hTN.1
        (hLleN L hL) hTN.2.2 (inf_le_right.trans (hLN L hL))
      have heq : (autI hV T ⊓ autI hV (thompsonJ H)) ⊓ L = autI hV T ⊓ L := by
        rw [inf_assoc, inf_eq_right.2 (hLleN L hL)]
      rw [heq] at h
      exact ⟨inf_le_right, (isPGroup_autI hV hT.2.1 (hT.1.trans hHN)).to_le inf_le_left, h⟩
    have hcard2 : ∀ L ∈ I, Nat.card ↥(autI hV T ⊓ L) = 2 := by
      intro L hL
      have h := Subgroup.relIndex_mul_card (autI hV T ⊓ L) L
      rw [inf_eq_left.2 (inf_le_right : autI hV T ⊓ L ≤ L), hb.card_eq L (hI𝓗 hL)] at h
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hSL L hL).2.1
      have hodd : ¬ 2 ∣ (autI hV T ⊓ L).relIndex L := (hSL L hL).2.2
      rw [hk] at h ⊢
      rcases k with _ | _ | k
      · exfalso
        apply hodd
        have : (autI hV T ⊓ L).relIndex L = 6 := by simpa using h
        rw [this]
        norm_num
      · norm_num
      · exfalso
        have h4 : 4 * ((autI hV T ⊓ L).relIndex L * 2 ^ k) = 6 := by
          rw [← h]
          ring
        omega
    have hJt2 : IsPGroup 2 (autI hV (thompsonJ T)) :=
      isPGroup_autI hV (hT.2.1.to_le (thompsonJ_le_self T))
        ((thompsonJ_le_self T).trans (hT.1.trans hHN))
    have hJtN : autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
      autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
    have hScard : Nat.card ↥(⨆ L ∈ I, (autI hV T ⊓ L)) = 2 ^ I.card := by
      have h := hb.card_biSup_eq_prod (fun L => autI hV T ⊓ L) (fun L _ => inf_le_right) I hI𝓗
      beta_reduce at h
      rw [h, Finset.prod_congr rfl hcard2]
      simp
    have hNcard : Nat.card ↥(autI hV (thompsonJ H)) = 6 ^ I.card := by
      have h := hb.card_biSup_eq_prod (fun L => L) (fun L _ => le_rfl) I hI𝓗
      beta_reduce at h
      rw [hN, h, Finset.prod_congr rfl (fun L hL => hb.card_eq L (hI𝓗 hL))]
      simp
    have hSle : (⨆ L ∈ I, (autI hV T ⊓ L)) ≤ autI hV (thompsonJ T) := by
      refine iSup₂_le fun L hL => ?_
      exact offenderImages_le_autI_thompsonJ hV hHN hT (hsylI L hL _ (hSL L hL)) inf_le_left
    exact isSylowTwoOf_of_card hJtN hJt2 hNcard (hScard ▸ Subgroup.card_le_of_le hSle)
  · exact fun L hL L' hL' hne a ha b hb' => hb.comm L (hI𝓗 hL) L' (hI𝓗 hL') hne a ha b hb'
  · intro L hL
    refine le_bot_iff.1 ?_
    calc L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' ≤ L ⊓ ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L), L' :=
          inf_le_inf_left L (iSup₂_mono' fun L' hL' => ⟨L', hI𝓗 hL', le_rfl⟩)
      _ = ⊥ := hb.inf_biSup_ne_eq_bot (hI𝓗 hL)
  · intro L hL
    rw [commV_eq_commSub]
    exact actsAsNaturalL2_of_full hW (hb.card_comm L (hI𝓗 hL)) (hb.le_stabSub (hI𝓗 hL))
      (hb.inf_centSub (hI𝓗 hL)) (hb.autSub_eq_top L (hI𝓗 hL))
  · rw [hN]
    simp only [commV_eq_commSub]
    exact hdec.1
  · rw [hN]
    simp only [commV_eq_commSub]
    exact hdec.2
  · intro L hL
    simp only [commV_eq_commSub]
    refine le_bot_iff.1 ?_
    calc commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' ≤
        commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' :=
          inf_le_inf_left _ (iSup₂_mono' fun L' hL' => ⟨L', hI𝓗 hL', le_rfl⟩)
      _ = ⊥ := hb.commSub_inf_biSup_ne_eq_bot hW (hI𝓗 hL)
  · intro g hg L hL
    have hN' : B1.conjAut g (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, L := by
      rw [← hN, hNnorm g hg]
    refine ⟨hb.conjAut_mem hW hI𝓗 hg hN' hL, ?_⟩
    simp only [commV_eq_commSub]
    exact IsTransvectionBlocks.map_commSub_conjAut L g

theorem rank_inf_centralizer_of_quot (hred : IsTwoReducedIn H V)
    (hsolvX : Group.IsSolvable ↥(autI hV H))
    (hT : IsSylowTwoOf T H) :
    CFSG.Open.pRank 2 (T ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 T ∧
      thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ thompsonJ T := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hVH : V ≤ H := hred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVT : V ≤ T := (le_pCoreOf_of_isTwoReducedIn hred).trans (pCoreOf_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  ·
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have hA₀Q : A₀ ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
      le_inf hA₀.1 ((le_iSup₂_of_le A₀ hA₀ le_rfl : A₀ ≤ thompsonJ T).trans hJ)
    refine ⟨pRank_eq_of_isMaxElemAbelian hA₀ hA₀Q inf_le_left, ?_⟩
    refine iSup_le fun D => iSup_le fun hD => ?_
    refine le_iSup₂_of_le D ⟨hD.1.trans inf_le_left, hD.2.1, fun B hBT hBe => ?_⟩ le_rfl
    exact (hA₀.2.2 B hBT hBe).trans (hD.2.2 A₀ hA₀Q hA₀.2.1)
  ·
    have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
      hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h)
    have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
    obtain ⟨hFF, -⟩ := B2_7_of_not_le hV hVH hHN hJH
    have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 =>
      eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
    have hq := (B1_8_3 hW hsolvX hO2 hFF).2
    have hcon : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hJ (iSup_le fun A => iSup_le fun hA => hcon A hA)
    obtain ⟨A, hA, hAC⟩ := hcon
    have hnot : ¬ IsStrongFFOffender hV T A := fun h =>
      hq _ (isStrongFFStarOffender_mono (autI_mono hV hT.1) h.2)
    have heq := B2_8_card_eq hV hVT hTN ⟨hA, hAC⟩ hnot
    have h1 : Nat.card (IntMod V hV) = Nat.card V := rfl
    rw [h1, card_autI_eq hV (hA.1.trans hTN), card_fixV_autI hV (hA.1.trans hTN)] at heq
    obtain ⟨-, hrk, hsub, -⟩ := B24_three hV hVT hA heq
    exact ⟨hrk, iSup_le fun D => iSup_le fun hD => le_iSup₂_of_le D (hsub D hD) le_rfl⟩

end Quot

end B2F

open B2F in
theorem B2_16_of_quot [Finite G] {H T V : Subgroup G}
    (hF : CharTwo H) (hsolv : Group.IsSolvable ↥(autOn H V))
    (hT : IsSylowTwoOf T H) (hV : V = conjClosure (quasithinOmegaOneCenter T) H) :
    ∃ hU : IsElemAbelian 2 V, IsTwoReducedIn H V ∧
      ((thompsonJ T ≤ Subgroup.centralizer (V : Set G) ∧
          ∀ h ∈ H, ∃ n ∈ H ⊓ Subgroup.normalizer (thompsonJ T : Set G),
            ∃ c ∈ H ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G), h = n * c) ∨
        (¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) ∧
          ∃ I : Finset (Subgroup (MulAut (IntMod V hU))),
            IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ H)) ∧
            autI hU (thompsonJ H) = ⨆ L ∈ I, L ∧
            (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
            (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
            (∀ L ∈ I, ActsAsNaturalL2 L (commV L)) ∧
            fixV (autI hU (thompsonJ H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
            fixV (autI hU (thompsonJ H)) ⊓ ⨆ L ∈ I, commV L = ⊥ ∧
            (∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥) ∧
            (∀ g ∈ autI hU H, ∀ L ∈ I, B1.conjAut g L ∈ I ∧
              (commV L).map g.toMonoidHom = commV (B1.conjAut g L)))) ∧
      CFSG.Open.pRank 2 (T ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 T ∧
      thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ thompsonJ T := by
  subst hV
  obtain ⟨hU, hcase⟩ := B2_15 hF hT
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  refine ⟨hU, hred, ?_, rank_inf_centralizer_of_quot hU hred hsolv hT⟩
  rcases hcase with ⟨hJ, -, -⟩ | ⟨hJ, hfact⟩
  · exact Or.inr ⟨hJ, structure_of_not_le_of_quot hU hred hsolv hT hJ⟩
  · refine Or.inl ⟨hJ, fun h hh => ?_⟩
    obtain ⟨c, hc, n, hn, hcn⟩ := hfact h⁻¹ (H.inv_mem hh)
    refine ⟨n⁻¹, ⟨H.inv_mem hn.1, (Subgroup.normalizer _).inv_mem hn.2⟩, c⁻¹,
      ⟨H.inv_mem hc.1, (Subgroup.centralizer _).inv_mem hc.2⟩, ?_⟩
    rw [← mul_inv_rev, ← hcn, inv_inv]

end CFSG.Quasithin
