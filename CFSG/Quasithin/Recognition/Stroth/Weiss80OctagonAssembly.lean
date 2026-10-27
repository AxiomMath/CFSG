module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.Stroth.WeissFQ
public import CFSG.Quasithin.Recognition.Stroth.OctagonIdentification
public import CFSG.Quasithin.Recognition.Stroth.BorelResidualSplitTransport
public import CFSG.Quasithin.Recognition.Stroth.ExtensionOfStabilizers
public import CFSG.Quasithin.Recognition.Stroth.OctLieModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Simple
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRGD2
public import CFSG.Quasithin.Recognition.Stroth.Weiss80AssemblyFacts
public import CFSG.Quasithin.Recognition.Stroth.Weiss80OctagonModelFacts

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits


theorem weiss80OctagonAssembly :
    WeissEmbeddingFacts 8 → RootGroupRegular 8 → MoufangRankTwoSystem 8 →
      MoufangLittleNormal 8 → StabilizersOfPolygon 8 → ExtensionOfStabilizers →
      BorelResidualSplitTransport → OctBorelResidualSplit → OctLieModel →
      Weiss80OctagonOfLeaves := by
  intro hEmb hRGR hRTS hMLN hStab hExt hBRST hOctBRS hOctLie
  intro hPoly hT8 hT8Ord hSubNat
  intro X _ _ P1 P2 a m ha hm hMouf hK1 hK2 hSzN hL2N hV1 hV2
  obtain ⟨Y, hY, hFinY, c, hcFaith, hcProj, hcMouf, hcWf, hcGirth⟩ :=
    ofSubgroups_exists_faithful_finite_completion_weiss P1 P2 (n := 8) (by norm_num)
      hMouf (2 * 8 + 2)
  letI : Group Y := hY
  letI : Finite Y := hFinY
  obtain ⟨V, hFinV, Δ, hDecΔ, D, hD, hFinD, hAct, hFaith, hGraphAct, u, v, ψ1, ψ2, ι,
    hGP, hThick, huv, hMoufΔ, hψ1u0, hψ2v0, hWEmb, huVal, hvVal⟩ :=
    hPoly X P1 P2 a m ha hm hK1 hK2 hSzN hL2N hV1 hV2 Y c hcFaith hcMouf hcWf
      (show ((2 * 8 + 2 : ℕ) : ℕ∞) < c.graph.egirth by simpa using hcGirth)
  letI : Fintype V := hFinV
  letI : DecidableRel Δ.Adj := hDecΔ
  letI : Group D := hD
  letI : Finite D := hFinD
  letI : MulAction D V := hAct
  letI : FaithfulSMul D V := hFaith
  letI : GraphAction D Δ := hGraphAct
  have hApt : ∃ t : ZMod (2 * 8) → V, IsPolygonApartment Δ 8 t ∧ t 8 = v ∧ t 9 = u :=
    exists_polygonApartment_through_edge (Γ := Δ) (n := 8) (by norm_num) hGP hThick
      (v := v) (u := u) huv.symm
  obtain ⟨t, ht, ht8, ht9⟩ := hApt
  have ht8' : t ((8 : ℕ) : ZMod (2 * 8)) = v := by simpa using ht8
  have ht9' : t (((8 : ℕ) : ZMod (2 * 8)) + 1) = u := by
    have h98 : (((8 : ℕ) : ZMod (2 * 8)) + 1) = ((9 : ℕ) : ZMod (2 * 8)) := by norm_num
    rw [h98]
    simpa using ht9
  have h9z : (((8 : ℕ) : ZMod (2 * 8)) + 1) = ((9 : ℕ) : ZMod (2 * 8)) := by norm_num
  obtain ⟨hAdj, hψ1u, hψ2v, hinter1, hinter2, htrans1, htrans2, hdegU, hdegV, hrootLe⟩ :=
    hEmb X P1 P2 Y c (by norm_num) hcFaith hcMouf V Δ D u v ψ1 ψ2 ι hGP hThick hMoufΔ hWEmb
  have hVal : ∀ w : V, ∃ e : ℕ, Δ.degree w = 2 ^ e + 1 := by
    intro w
    rcases degree_eq_degree_u_or_degree_v_of_adj_orbit (Γ := Δ) (D := D) hGP.connected
      (fun x hx => let ⟨g, hg⟩ := htrans1 x hx; ⟨ψ1 g, hg⟩)
      (fun x hx => let ⟨g, hg⟩ := htrans2 x hx; ⟨ψ2 g, hg⟩) w with h | h
    · obtain ⟨e, -, hdeg⟩ := huVal
      exact ⟨e, by rw [h, hdeg]⟩
    · obtain ⟨e, -, hdeg⟩ := hvVal
      exact ⟨e, by rw [h, hdeg]⟩
  obtain ⟨R, hRoot, hXplus, hRB, hRP1, hRP2⟩ :=
    hRTS V Δ D (by norm_num) hGP hThick hMoufΔ hVal t ht
  let L : Subgroup D := littleGroup D Δ 8
  let Du : Subgroup D := MulAction.stabilizer D u
  let Dv : Subgroup D := MulAction.stabilizer D v
  let B : Subgroup D := (psiB P2 ψ1).range
  obtain ⟨f, hfodd, horders⟩ := hT8Ord L R
  have hrootLe' : ∀ p : GPath Δ 8, p.NoBack → ∀ j : ℕ, j + 1 ≤ 8 →
      ((p j = t 8 ∧ p (j + 1) = t 9) ∨ (p j = t 9 ∧ p (j + 1) = t 8)) →
      pathRootGroup D Δ p ≤ B := by
    intro p hp j hj h
    refine hrootLe p hp j hj ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      rw [h1, h2]
      exact ⟨ht8, ht9⟩
    · left
      rw [h1, h2]
      exact ⟨ht9, ht8⟩
  have hUle : R.U.map L.subtype ≤ B :=
    map_U_le_of_pathRootGroup_le (n := 8) (by norm_num) ht
      (fun i hi1 hi8 => (hRoot i hi1 hi8).1) hrootLe' 
  have hdegUval : Δ.degree u = 1 + Nat.card (R.root 1) := by
    rw [← card_nbrs_eq_degree (Γ := Δ) u]
    change Fintype.card {w : V // Δ.Adj u w} = 1 + Nat.card (R.root 1)
    rw [← ht9]
    refine card_nbrs_succ_eq_one_add_card_root_one (n := 8) (by norm_num)
      (Γ := Δ) (D := D) (L := L) (R := R) (t := t)
      ht hGP hThick hMoufΔ (fun i hi1 hi8 => (hRoot i hi1 hi8).1) ?_
    convert huv.symm using 2
  have hdegVval : Δ.degree v = 1 + Nat.card (R.root 8) := by
    rw [← card_nbrs_eq_degree (Γ := Δ) v]
    change Fintype.card {w : V // Δ.Adj v w} = 1 + Nat.card (R.root 8)
    rw [← ht8]
    refine card_nbrs_eq_one_add_card_root_last (n := 8) (by norm_num)
      (Γ := Δ) (D := D) (L := L) (R := R) (t := t)
      ht hGP hThick hMoufΔ (fun i hi1 hi8 => (hRoot i hi1 hi8).1) ?_
    convert huv.symm using 2
  have hpowU : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card {w : V // Δ.Adj u w} = 1 + 2 ^ e := by
    rcases horders with ⟨hodd, heven⟩ | ⟨heven, hodd⟩
    · have h1 : Nat.card (R.root 1) = 2 ^ f :=
        hodd 1 (by norm_num) (by norm_num) (by norm_num)
      refine ⟨f, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hfodd; omega
      · rw [show Fintype.card {w : V // Δ.Adj u w} = Δ.degree u from by
              simpa [nbrs] using card_nbrs_eq_degree (Γ := Δ) u, hdegUval, h1]
    · have h1 : Nat.card (R.root 1) = 2 ^ (2 * f) :=
        hodd 1 (by norm_num) (by norm_num) (by norm_num)
      refine ⟨2 * f, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hfodd; omega
      · rw [show Fintype.card {w : V // Δ.Adj u w} = Δ.degree u from by
              simpa [nbrs] using card_nbrs_eq_degree (Γ := Δ) u, hdegUval, h1]
  have hpowV : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card {w : V // Δ.Adj v w} = 1 + 2 ^ e := by
    rcases horders with ⟨hodd, heven⟩ | ⟨heven, hodd⟩
    · have h8 : Nat.card (R.root 8) = 2 ^ (2 * f) :=
        heven 8 (by norm_num) (by norm_num) (by norm_num)
      refine ⟨2 * f, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hfodd; omega
      · rw [show Fintype.card {w : V // Δ.Adj v w} = Δ.degree v from by
              simpa [nbrs] using card_nbrs_eq_degree (Γ := Δ) v, hdegVval, h8]
    · have h8 : Nat.card (R.root 8) = 2 ^ f :=
        heven 8 (by norm_num) (by norm_num) (by norm_num)
      refine ⟨f, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hfodd; omega
      · rw [show Fintype.card {w : V // Δ.Adj v w} = Δ.degree v from by
              simpa [nbrs] using card_nbrs_eq_degree (Γ := Δ) v, hdegVval, h8]
  have hcardU : Nat.card {w : V // Δ.Adj u w} = 2 ^ (2 * (2 * a + 1)) + 1 := by
    let p : GPath Δ 8 := aptPath ht.2 1
    have hp : p.NoBack := aptPath_noBack (by norm_num) ht 1
    have hp8 : p 8 = t 9 := by
      change apt t (1 + (8 : ℤ)) = t 9
      norm_num
      rfl
    have hp7 : p 7 = t 8 := by
      change apt t (1 + (7 : ℤ)) = t 8
      norm_num
      rfl
    have hroot_le : pathRootGroup D Δ p ≤ B :=
      hrootLe' p hp 7 (by norm_num) (Or.inl ⟨hp7, hp8⟩)
    have hreg : ∀ y y' : V, Δ.Adj u y → Δ.Adj u y' → y ≠ v → y' ≠ v →
        ∃! g : ↥(pathRootGroup D Δ p), (g : D) • y = y' := by
      intro y y' hy hy' hne hne'
      exact rootGroupRegular (n := 8) (V := V) (Γ := Δ) (D := D) (by norm_num)
        hGP hThick hMoufΔ p hp y y'
        (by simpa [hp8, ht9] using hy) (by simpa [hp8, ht9] using hy')
        (by simpa [hp7, ht8] using hne) (by simpa [hp7, ht8] using hne')
    have h := subconstNatural_sz (Γ := Δ) (D := D) (P1 := P1) (P2 := P2) (ψ1 := ψ1)
      (u := u) (v := v) hSubNat a ha hWEmb.1 hψ1u hinter1 htrans1
      (pathRootGroup D Δ p) hroot_le hreg huv hpowU hSzN
    simpa [nbrs, Nat.card_eq_fintype_card] using h
  have hcardV : Nat.card {w : V // Δ.Adj v w} = 2 ^ m + 1 := by
    let p : GPath Δ 8 := aptPathRev ht.2 8
    have hp : p.NoBack := aptPathRev_noBack (by norm_num) ht 8
    have hp8 : p 8 = t 8 := by
      change apt t (8 + (8 : ℤ) - 8) = t 8
      norm_num
      rfl
    have hp7 : p 7 = t 9 := by
      change apt t (8 + (8 : ℤ) - 7) = t 9
      norm_num
      rfl
    have hroot_le : pathRootGroup D Δ p ≤ (psiB P1 ψ2).range := by
      rw [range_psiB_comm hWEmb.2.2.1]
      exact hrootLe' p hp 7 (by norm_num) (Or.inr ⟨hp7, hp8⟩)
    have hreg : ∀ y y' : V, Δ.Adj v y → Δ.Adj v y' → y ≠ u → y' ≠ u →
        ∃! g : ↥(pathRootGroup D Δ p), (g : D) • y = y' := by
      intro y y' hy hy' hne hne'
      exact rootGroupRegular (n := 8) (V := V) (Γ := Δ) (D := D) (by norm_num)
        hGP hThick hMoufΔ p hp y y'
        (by simpa [hp8, ht8] using hy) (by simpa [hp8, ht8] using hy')
        (by simpa [hp7, ht9] using hne) (by simpa [hp7, ht9] using hne')
    have h := subconstNatural_l2 (Γ := Δ) (D := D) (P1 := P2) (P2 := P1) (ψ1 := ψ2)
      (u := v) (v := u) hSubNat m hm hWEmb.2.1 hψ2v
      (by rw [range_psiB_comm hWEmb.2.2.1]; exact hinter2) htrans2
      (pathRootGroup D Δ p) hroot_le hreg huv.symm hpowV hL2N
    simpa [nbrs, Nat.card_eq_fintype_card] using h
  let K := GaloisField 2 (2 * a + 1)
  haveI : Field K := inferInstance
  haveI : Finite K := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero (2 * a + 1) := ⟨by omega⟩
  have hKcard : Nat.card K = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card, hKcard]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) hKf
  haveI : CharP K F4.prime := ‹CharP K 2›
  haveI : IsSimpleGroup (Gm K a) := isSimpleGroup_gm ha hKcard
  let hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a) := octRGD2 hKcard
  have hdu : Nat.card {w : V // Δ.Adj u w} = Δ.degree u := by
    rw [Nat.card_eq_fintype_card]
    exact card_nbrs_eq_degree (Γ := Δ) u
  have hdv : Nat.card {w : V // Δ.Adj v w} = Δ.degree v := by
    rw [Nat.card_eq_fintype_card]
    exact card_nbrs_eq_degree (Γ := Δ) v
  have hroot1 : Nat.card (R.root 1) = 2 ^ (2 * (2 * a + 1)) := by omega
  have hroot8 : Nat.card (R.root 8) = 2 ^ m := by omega
  obtain ⟨hm_eq, hrootOrders⟩ :=
    octagon_orders_of_root_cards (m := m) hT8Ord R hR ha hm hKcard hroot1 hroot8
  have hIdent := octagonIdentification_of_tits83 hT8
  obtain ⟨κ0⟩ := hIdent L R K a hR ha hKcard hrootOrders
  let κtop : ↥L ≃* Gm K a :=
    (Subgroup.topEquiv.symm).trans ((MulEquiv.subgroupCongr hXplus).symm.trans κ0)
  have hmodelSylow : IsSylowTwoOf (octSystemOf hR).U ⊤ := by
    rw [octSystemOf_U]
    exact isSylowTwoOf_Ug hKcard
  have hcardR : Nat.card R.U = (Nat.card K) ^ 12 := by
    rw [octagon_rootSystem_card_U (hR := hR) hrootOrders, octSystemOf_card_U (hR := hR) hKcard]
  have hP : IsPGroup 2 R.U := by
    rw [IsPGroup.iff_card]
    refine ⟨12 * (2 * a + 1), ?_⟩
    rw [hcardR, hKcard, ← pow_mul]
    ring
  have htwoGm : twoPart (⊤ : Subgroup (Gm K a)) = (Nat.card K) ^ 12 := by
    rw [← hmodelSylow.card_eq, octSystemOf_card_U (hR := hR) hKcard]
  have htwoL : twoPart (⊤ : Subgroup ↥L) = twoPart (⊤ : Subgroup (Gm K a)) := by
    simp only [twoPart, Subgroup.card_top]
    rw [Nat.card_congr κtop.toEquiv]
  have hcard_two : Nat.card R.U = twoPart (⊤ : Subgroup ↥L) :=
    hcardR.trans (htwoL.trans htwoGm).symm
  have hSylowU : IsSylowTwoOf R.U ⊤ :=
    isSylowTwoOf_of_card_eq le_top hP hcard_two
  obtain ⟨κ, hκU⟩ : ∃ κ : ↥L ≃* Gm K a, R.U.map κ.toMonoidHom = (octSystemOf hR).U :=
    exists_mulEquiv_map_eq_of_isSylowTwoOf_top κtop hSylowU hmodelSylow
  have hBmap : R.B.map κ.toMonoidHom = (octSystemOf hR).B := by
    rw [← CFSG.Quasithin.H13.F431.BN.normalizer_U_eq_B R,
      Subgroup.map_equiv_normalizer_eq, hκU,
      CFSG.Quasithin.H13.F431.BN.normalizer_U_eq_B (octSystemOf hR)]
  have hP1map : R.P₁.map κ.toMonoidHom = (octSystemOf hR).P₁ ∨
      R.P₁.map κ.toMonoidHom = (octSystemOf hR).P₂ := by
    have h := map_parabolic_eq_or R (octSystemOf hR) κ hBmap true
    simpa [CFSG.Quasithin.H13.F431.BN.P_true] using h
  have hP2map : R.P₂.map κ.toMonoidHom = (octSystemOf hR).P₁ ∨
      R.P₂.map κ.toMonoidHom = (octSystemOf hR).P₂ := by
    have h := map_parabolic_eq_or R (octSystemOf hR) κ hBmap false
    simpa [CFSG.Quasithin.H13.F431.BN.P_false] using h
  have hYamModel : IsYAmalgamPair (octSystemOf hR).U (octSystemOf hR).P₁
      (octSystemOf hR).P₂ :=
    CFSG.Quasithin.H13.F431.BN.isYAmalgamPair (octSystemOf hR) (isSylowTwoOf_Ug hKcard)
  have hYamSwap : IsYAmalgamPair (octSystemOf hR).U (octSystemOf hR).P₂
      (octSystemOf hR).P₁ := by
    obtain ⟨hT, hne, hmax⟩ := hYamModel
    exact ⟨hT, hne.symm, fun M => by rw [hmax M]; exact or_comm⟩
  have hDu : Du.subgroupOf L = R.P₁ := by
    change (MulAction.stabilizer D u).subgroupOf L = R.P₁
    rw [hRP1, ← ht9']
  have hDv : Dv.subgroupOf L = R.P₂ := by
    change (MulAction.stabilizer D v).subgroupOf L = R.P₂
    rw [hRP2, ← ht8']
  have hYam : IsYAmalgamPair (octSystemOf hR).U
      ((Du.subgroupOf L).map κ.toMonoidHom) ((Dv.subgroupOf L).map κ.toMonoidHom) := by
    rw [hDu, hDv]
    rcases hP1map with h1 | h1 <;> rcases hP2map with h2 | h2
    · exfalso
      exact CFSG.Quasithin.H13.F431.BN.P₁_ne_P₂ R
        (Subgroup.map_injective κ.injective (h1.trans h2.symm))
    · rw [h1, h2]; exact hYamModel
    · rw [h1, h2]; exact hYamSwap
    · exfalso
      exact CFSG.Quasithin.H13.F431.BN.P₁_ne_P₂ R
        (Subgroup.map_injective κ.injective (h1.trans h2.symm))
  have hBRS : BorelResidualSplit R :=
    hBRST L (Gm K a) 8 R (octSystemOf hR) ⟨κ⟩ hSylowU
      (by rw [octSystemOf_U]; exact isSylowTwoOf_Ug hKcard)
      (hOctBRS K a hR ha hKcard)
  obtain ⟨hLnorm, hcent, hNz, hswap⟩ :=
    hMLN V Δ D (by norm_num) hGP hThick hMoufΔ
  obtain ⟨hrange1, hrange2, hrangeB⟩ :=
    hStab X P1 P2 V Δ D (by norm_num) hGP hThick
      hMoufΔ hLnorm u v ψ1 ψ2 hWEmb.2.2.1 hψ1u hψ2v hWEmb.2.2.2.1 hinter1 hinter2
      htrans1 htrans2 R (by rw [hRB, ht8', ht9', inf_comm])
      (by left; rw [hRP1, hRP2, ht8', ht9']; exact ⟨rfl, rfl⟩)
      hUle hSylowU hBRS
  have hNdiag : Subgroup.normalizer ((L ⊓ Du ⊓ Dv : Subgroup D) : Set D) ≤ Du := by
    refine normalizer_chamber_le_left (Γ := Δ) (D := D) (L := L) (Du := Du) (Dv := Dv)
      (u := u) (v := v) ?_ ?_ ?_
    · intro d
      change d ∈ MulAction.stabilizer D u ↔ d • u = u
      rw [MulAction.mem_stabilizer_iff]
    · simpa [Du, Dv] using hswap u v huv
    · intro hdeg
      have hcu : Δ.degree u = Nat.card {w : V // Δ.Adj u w} := by
        rw [Nat.card_eq_fintype_card, card_nbrs_eq_degree]
      have hcv : Δ.degree v = Nat.card {w : V // Δ.Adj v w} := by
        rw [Nat.card_eq_fintype_card, card_nbrs_eq_degree]
      rw [hcu, hcv, hcardU, hcardV, hm_eq] at hdeg
      have hpow : 2 ^ (2 * (2 * a + 1)) = 2 ^ (2 * a + 1) := by omega
      have heq : 2 * (2 * a + 1) = 2 * a + 1 :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
      omega
  have hExtApp : IsExtensionOfLieAmalgam (Gm K a) P1 P2 :=
    hExt X P1 P2 D L Du Dv ψ1 ψ2 hLnorm hWEmb.1 hWEmb.2.1 hWEmb.2.2.1
      hrange1 hrange2 hrangeB hcent
      (by
        change Subgroup.normalizer ((L ⊓ MulAction.stabilizer D u : Subgroup D) : Set D) =
          MulAction.stabilizer D u
        exact hNz u)
      (by
        change Subgroup.normalizer ((L ⊓ MulAction.stabilizer D v : Subgroup D) : Set D) =
          MulAction.stabilizer D v
        exact hNz v)
      hNdiag (Gm K a) κ (octSystemOf hR).U hYam
  exact ⟨hm_eq, Gm K a, inferInstance, hOctLie K a ha hKcard, hExtApp⟩

end CFSG.Quasithin.Stroth
