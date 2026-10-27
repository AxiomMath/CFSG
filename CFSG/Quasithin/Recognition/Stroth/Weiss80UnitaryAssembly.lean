module

public import CFSG.Quasithin.Recognition.Stroth.WeissFQ
public import CFSG.Quasithin.Recognition.Stroth.Un5ModelProps
public import CFSG.Quasithin.Recognition.Stroth.Un5LieModel
public import CFSG.Quasithin.Recognition.Stroth.BorelResidualSplitTransport
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.BNPair CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Universal.Unitary

theorem weiss80UnitaryAssembly :
    WeissEmbeddingFacts 4 → RootGroupRegular 4 → MoufangRankTwoSystem 4 →
      QuadrangleIdentification → MoufangLittleNormal 4 → StabilizersOfPolygon 4 →
      ExtensionOfStabilizers → BorelResidualSplitTransport → Un5BorelResidualSplit →
      Weiss80UnitaryOfLeaves := by
  intro hEmb hRGR hRTS hQuad hMLN hStab hExt hBRST hUn5BRS
  intro hPoly hHerm hRootsAb hSubNat hNonab
  intro X _ _ P1 P2 k m F _ _ hk hm hF hm2k hMouf hU3N hL2N hV1 hV2
  obtain ⟨Y, hY, hFinY, c, hcFaith, hcProj, hcMouf, hcWf, hcGirth⟩ :=
    ofSubgroups_exists_faithful_finite_completion_weiss P1 P2 (n := 4) (by norm_num)
      hMouf (2 * 4 + 2)
  letI : Group Y := hY
  letI : Finite Y := hFinY
  obtain ⟨V, hFinV, Δ, hDecΔ, D, hD, hFinD, hAct, hFaith, hGraphAct, u, v, ψ1, ψ2, ι,
    hGP, hThick, huv, hMoufΔ, hψ1u0, hψ2v0, hWEmb, huVal, hvVal⟩ :=
    hPoly X P1 P2 k m F hk hm hF hm2k hU3N hL2N hV1 hV2 Y c hcFaith hcMouf hcWf
      (show ((2 * 4 + 2 : ℕ) : ℕ∞) < c.graph.egirth by simpa using hcGirth)
  letI : Fintype V := hFinV
  letI : DecidableRel Δ.Adj := hDecΔ
  letI : Group D := hD
  letI : Finite D := hFinD
  letI : MulAction D V := hAct
  letI : FaithfulSMul D V := hFaith
  letI : GraphAction D Δ := hGraphAct
  have hApt : ∃ t : ZMod (2 * 4) → V, IsPolygonApartment Δ 4 t ∧ t 4 = v ∧ t 5 = u :=
    exists_polygonApartment_through_edge (Γ := Δ) (n := 4) (by norm_num) hGP hThick
      (v := v) (u := u) huv.symm
  obtain ⟨t, ht, ht4, ht5⟩ := hApt
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
  have hrootLe' : ∀ p : GPath Δ 4, p.NoBack → ∀ j : ℕ, j + 1 ≤ 4 →
      ((p j = t 4 ∧ p (j + 1) = t 5) ∨ (p j = t 5 ∧ p (j + 1) = t 4)) →
      pathRootGroup D Δ p ≤ (psiB P2 ψ1).range := by
    intro p hp j hj h
    refine hrootLe p hp j hj ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      rw [h1, h2]
      exact ⟨ht4, ht5⟩
    · left
      rw [h1, h2]
      exact ⟨ht5, ht4⟩
  have hBcomm : (psiB P1 ψ2).range = (psiB P2 ψ1).range :=
    range_psiB_comm hWEmb.2.2.1
  have hcardU : Nat.card {w : V // Δ.Adj u w} = 2 ^ (3 * k) + 1 := by
    have hpowU : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card (nbrs (Γ := Δ) u) = 1 + 2 ^ e := by
      obtain ⟨e, he, hdeg⟩ := huVal
      exact ⟨e, he, by rw [show Fintype.card (nbrs (Γ := Δ) u) = Δ.degree u from
        card_nbrs_eq_degree (Γ := Δ) u]; simpa [Nat.add_comm] using hdeg⟩
    let q : GPath Δ 4 := aptPath ht.2 1
    have hq : q.NoBack := aptPath_noBack (by norm_num) ht 1
    have hq4 : q 4 = u := by
      change apt t (1 + (4 : ℤ)) = u
      rw [show (1 + (4 : ℤ)) = (5 : ℤ) by norm_num]
      simpa [apt] using ht5
    have hq3 : q 3 = v := by
      change apt t (1 + (3 : ℤ)) = v
      rw [show (1 + (3 : ℤ)) = (4 : ℤ) by norm_num]
      simpa [apt] using ht4
    have hroot_le : pathRootGroup D Δ q ≤ (psiB P2 ψ1).range := by
      refine hrootLe' q hq 3 (by norm_num) ?_
      left
      exact ⟨by rw [hq3, ← ht4], by rw [hq4, ← ht5]⟩
    have hreg : ∀ y y' : V, Δ.Adj u y → Δ.Adj u y' → y ≠ v → y' ≠ v →
        ∃! g : ↥(pathRootGroup D Δ q), (g : D) • y = y' := by
      intro y y' hy hy' hne hne'
      exact rootGroupRegular (n := 4) (V := V) (Γ := Δ) (D := D) (by norm_num)
        hGP hThick hMoufΔ q hq y y' (by simpa [hq4, ht5] using hy)
        (by simpa [hq4, ht5] using hy') (by simpa [hq3, ht4] using hne)
        (by simpa [hq3, ht4] using hne')
    have h := subconstNatural_psu3 (Γ := Δ) (D := D) (P1 := P1) (P2 := P2)
      (ψ1 := ψ1) (u := u) (v := v) hSubNat k F hk hF hWEmb.1 hψ1u hinter1 htrans1
      (pathRootGroup D Δ q) hroot_le hreg huv hpowU hU3N
    simpa [nbrs, Nat.card_eq_fintype_card] using h
  have hcardV : Nat.card {w : V // Δ.Adj v w} = 2 ^ m + 1 := by
    have hpowV : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card (nbrs (Γ := Δ) v) = 1 + 2 ^ e := by
      obtain ⟨e, he, hdeg⟩ := hvVal
      exact ⟨e, he, by rw [show Fintype.card (nbrs (Γ := Δ) v) = Δ.degree v from
        card_nbrs_eq_degree (Γ := Δ) v]; simpa [Nat.add_comm] using hdeg⟩
    let q : GPath Δ 4 := aptPathRev ht.2 4
    have hq : q.NoBack := aptPathRev_noBack (by norm_num) ht 4
    have hq4 : q 4 = v := by
      change apt t ((4 : ℤ) + (4 : ℤ) - 4) = v
      norm_num
      simpa [apt] using ht4
    have hq3 : q 3 = u := by
      change apt t ((4 : ℤ) + (4 : ℤ) - 3) = u
      norm_num
      simpa [apt] using ht5
    have hroot_le : pathRootGroup D Δ q ≤ (psiB P1 ψ2).range := by
      rw [hBcomm]
      refine hrootLe' q hq 3 (by norm_num) ?_
      right
      exact ⟨by rw [hq3, ← ht5], by rw [hq4, ← ht4]⟩
    have hreg : ∀ y y' : V, Δ.Adj v y → Δ.Adj v y' → y ≠ u → y' ≠ u →
        ∃! g : ↥(pathRootGroup D Δ q), (g : D) • y = y' := by
      intro y y' hy hy' hne hne'
      exact rootGroupRegular (n := 4) (V := V) (Γ := Δ) (D := D) (by norm_num)
        hGP hThick hMoufΔ q hq y y' (by simpa [hq4, ht5] using hy)
        (by simpa [hq4, ht5] using hy') (by simpa [hq3, ht4] using hne)
        (by simpa [hq3, ht4] using hne')
    have h := subconstNatural_l2 (Γ := Δ) (D := D) (P1 := P2) (P2 := P1)
      (ψ1 := ψ2) (u := v) (v := u) hSubNat m (by omega : 2 ≤ m) hWEmb.2.1 hψ2v
      (by simpa [hBcomm] using hinter2) htrans2 (pathRootGroup D Δ q) hroot_le hreg
      huv.symm hpowV hL2N
    simpa [nbrs, Nat.card_eq_fintype_card] using h
  have hLemmaN : ∃ p : GPath Δ 4, p.NoBack ∧ Δ.degree (p 0) = 2 ^ (3 * k) + 1 ∧
      ∃ a ∈ pathRootGroup D Δ p, ∃ b ∈ pathRootGroup D Δ p, a * b ≠ b * a :=
    exists_noncommuting_pathRootGroup_of_subconstUnitary (Δ := Δ) (D := D)
      (P1 := P1) (P2 := P2) (ψ1 := ψ1) t ht hGP hThick hMoufΔ hWEmb.1
      (by simpa [ht5] using hψ1u) (by simpa [ht4] using hinter1)
      (by simpa [ht5, ht4] using htrans1) hrootLe'
      (by simpa [ht5] using hcardU) hU3N hNonab hk hF
      (by simpa [ht4, ht5] using huv.symm)
  obtain ⟨R, hRoot, hXplus, hRB, hRP1, hRP2⟩ :=
    hRTS V Δ D (by norm_num) hGP hThick hMoufΔ hVal t ht
  let L : Subgroup D := littleGroup D Δ 4
  let Du : Subgroup D := MulAction.stabilizer D u
  let Dv : Subgroup D := MulAction.stabilizer D v
  let B : Subgroup D := (psiB P2 ψ1).range
  have hUle : R.U.map L.subtype ≤ B :=
    map_U_le_of_pathRootGroup_le (n := 4) (by norm_num) ht
      (fun i hi1 hi4 => (hRoot i hi1 hi4).1) hrootLe'
  have hroot1 : Nat.card (R.root 1) = (2 ^ k) ^ 3 := by
    let q : GPath Δ 4 := aptPath ht.2 1
    have hq : q.NoBack := aptPath_noBack (by norm_num) ht 1
    have hq4 : q 4 = u := by
      change apt t (1 + (4 : ℤ)) = u
      rw [show (1 + (4 : ℤ)) = (5 : ℤ) by norm_num]
      simpa [apt] using ht5
    have hq3 : q 3 = v := by
      change apt t (1 + (3 : ℤ)) = v
      rw [show (1 + (3 : ℤ)) = (4 : ℤ) by norm_num]
      simpa [apt] using ht4
    have hcardq := card_pathRootGroup_add_one (n := 4) (V := V) (Γ := Δ) (D := D)
      (by norm_num) hGP hThick hMoufΔ q hq
    rw [hq4, show Δ.degree u = 2 ^ (3 * k) + 1 from by
      rw [← card_nbrs_eq_degree (Γ := Δ) u]
      simpa [nbrs, Nat.card_eq_fintype_card] using hcardU] at hcardq
    have hmap : Nat.card (R.root 1) = Nat.card (pathRootGroup D Δ q) := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective]
      rw [(hRoot 1 (by norm_num) (by norm_num)).1, aptRoot_eq_pathRootGroup ht 1]
    rw [hmap]
    have hc : Nat.card (pathRootGroup D Δ q) = 2 ^ (3 * k) := by omega
    rw [hc, show 3 * k = k * 3 by omega, ← pow_mul]
  have hroot4 : Nat.card (R.root 4) = 2 ^ m := by
    let q : GPath Δ 4 := aptPathRev ht.2 4
    have hq : q.NoBack := aptPathRev_noBack (by norm_num) ht 4
    have hq4 : q 4 = v := by
      change apt t ((4 : ℤ) + (4 : ℤ) - 4) = v
      norm_num
      simpa [apt] using ht4
    have hq3 : q 3 = u := by
      change apt t ((4 : ℤ) + (4 : ℤ) - 3) = u
      norm_num
      simpa [apt] using ht5
    have hcardq := card_pathRootGroup_add_one (n := 4) (V := V) (Γ := Δ) (D := D)
      (by norm_num) hGP hThick hMoufΔ q hq
    rw [hq4, show Δ.degree v = 2 ^ m + 1 from by
      rw [← card_nbrs_eq_degree (Γ := Δ) v]
      simpa [nbrs, Nat.card_eq_fintype_card] using hcardV] at hcardq
    have hmap : Nat.card (R.root 4) = Nat.card (pathRootGroup D Δ q) := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective]
      rw [(hRoot 4 (by norm_num) (by norm_num)).1, aptRoot_eq_pathRootGroupRev (by norm_num) ht 4]
    rw [hmap]
    have : Nat.card (pathRootGroup D Δ q) = 2 ^ m := by omega
    exact this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := by
    letI : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 2 ^ (2 * k) := by
      rw [← Nat.card_eq_fintype_card, hF, pow_two, ← pow_add]
      congr 1
      omega
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * k) hcard
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (p := 2) (f := k) hF
  letI : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have hdegOr : ∀ w : V, Δ.degree w = 2 ^ m + 1 ∨ Δ.degree w = 2 ^ (3 * k) + 1 := by
    intro w
    rcases degree_eq_degree_u_or_degree_v_of_adj_orbit (Γ := Δ) (D := D) hGP.connected
      (fun x hx => let ⟨g, hg⟩ := htrans1 x hx; ⟨ψ1 g, hg⟩)
      (fun x hx => let ⟨g, hg⟩ := htrans2 x hx; ⟨ψ2 g, hg⟩) w with h | h
    · right
      rw [h, show Δ.degree u = 2 ^ (3 * k) + 1 from by
        rw [← card_nbrs_eq_degree (Γ := Δ) u]
        simpa [nbrs, Nat.card_eq_fintype_card] using hcardU]
    · left
      rw [h, show Δ.degree v = 2 ^ m + 1 from by
        rw [← card_nbrs_eq_degree (Γ := Δ) v]
        simpa [nbrs, Nat.card_eq_fintype_card] using hcardV]
  obtain ⟨_, φ, κ, hκequiv⟩ :=
    hQuad V Δ D hGP hThick hMoufΔ k m F hF ζ (by omega) hm hdegOr
      ⟨v, by
        rw [← card_nbrs_eq_degree (Γ := Δ) v]
        simpa [nbrs, Nat.card_eq_fintype_card] using hcardV⟩
      ⟨u, by
        rw [← card_nbrs_eq_degree (Γ := Δ) u]
        simpa [nbrs, Nat.card_eq_fintype_card] using hcardU⟩
      hLemmaN
  let M : RankTwoSystem (Un5Group k F) 4 := un5System hF ζ
  have hmodelSylow : IsSylowTwoOf M.U ⊤ := isSylowTwoOf_un5System hF ζ
  have hmodelCard : Nat.card M.U = (2 ^ k) ^ 10 := by
    have horders := un5RootGroupOrders (hF := hF) (ζ := ζ)
    have h1 : Nat.card (M.root 1) = (2 ^ k) ^ 2 := horders.1
    have h4 : Nat.card (M.root 4) = (2 ^ k) ^ 3 := horders.2
    have h2 : Nat.card (M.root 2) = (2 ^ k) ^ 3 := by
      rw [rankTwoSystem_card_root_two_eq_card_root_four M, h4]
    have h3 : Nat.card (M.root 3) = (2 ^ k) ^ 2 := by
      rw [rankTwoSystem_card_root_three_eq_card_root_one M, h1]
    have hlist : intList 1 ((4 : ℕ) : ℤ) = [1, 2, 3, 4] := by decide
    rw [rankTwoSystem_card_U, hlist]
    norm_num
    rw [h1, h2, h3, h4]
    ring
  have hcardR : Nat.card R.U = (2 ^ k) ^ 10 := by
    have hlist : intList 1 ((4 : ℕ) : ℤ) = [1, 2, 3, 4] := by decide
    rw [rankTwoSystem_card_U, hlist]
    norm_num
    have h4 : Nat.card (R.root 4) = (2 ^ k) ^ 2 := by
      rw [hroot4, hm2k]
      rw [show 2 * k = k * 2 by ring, pow_mul]
    have h2 : Nat.card (R.root 2) = (2 ^ k) ^ 2 := by
      rw [rankTwoSystem_card_root_two_eq_card_root_four R, h4]
    have h3 : Nat.card (R.root 3) = (2 ^ k) ^ 3 := by
      rw [rankTwoSystem_card_root_three_eq_card_root_one R, hroot1]
    rw [hroot1, h2, h3, h4]
    ring_nf
  have hP : IsPGroup 2 R.U := by
    rw [IsPGroup.iff_card]
    refine ⟨5 * (2 * k), ?_⟩
    rw [hcardR]
    ring_nf
  have htwoM : twoPart (⊤ : Subgroup (Un5Group k F)) = (2 ^ k) ^ 10 := by
    rw [← hmodelSylow.card_eq, hmodelCard]
  have htwoL : twoPart (⊤ : Subgroup ↥L) = twoPart (⊤ : Subgroup (Un5Group k F)) := by
    simp only [twoPart, Subgroup.card_top]
    rw [Nat.card_congr κ.toEquiv]
  have hcard_two : Nat.card R.U = twoPart (⊤ : Subgroup ↥L) :=
    hcardR.trans (htwoL.trans htwoM).symm
  have hSylowU : IsSylowTwoOf R.U ⊤ :=
    isSylowTwoOf_of_card_eq le_top hP hcard_two
  obtain ⟨κ', hκU⟩ : ∃ κ' : ↥L ≃* Un5Group k F,
      R.U.map κ'.toMonoidHom = M.U :=
    exists_mulEquiv_map_eq_of_isSylowTwoOf_top κ hSylowU hmodelSylow
  have hBmap : R.B.map κ'.toMonoidHom = M.B := by
    rw [← CFSG.Quasithin.H13.F431.BN.normalizer_U_eq_B R,
      Subgroup.map_equiv_normalizer_eq, hκU,
      CFSG.Quasithin.H13.F431.BN.normalizer_U_eq_B M]
  have hP1map : R.P₁.map κ'.toMonoidHom = M.P₁ ∨
      R.P₁.map κ'.toMonoidHom = M.P₂ := by
    have h := map_parabolic_eq_or R M κ' hBmap true
    simpa [CFSG.Quasithin.H13.F431.BN.P_true] using h
  have hP2map : R.P₂.map κ'.toMonoidHom = M.P₁ ∨
      R.P₂.map κ'.toMonoidHom = M.P₂ := by
    have h := map_parabolic_eq_or R M κ' hBmap false
    simpa [CFSG.Quasithin.H13.F431.BN.P_false] using h
  haveI : IsSimpleGroup (Un5Group k F) := isSimpleGroup_un5 hF
  have hYamModel : IsYAmalgamPair M.U M.P₁ M.P₂ :=
    CFSG.Quasithin.H13.F431.BN.isYAmalgamPair M hmodelSylow
  have hYamSwap : IsYAmalgamPair M.U M.P₂ M.P₁ := by
    obtain ⟨hT, hne, hmax⟩ := hYamModel
    exact ⟨hT, hne.symm, fun N => by rw [hmax N]; exact or_comm⟩
  have hDu : Du.subgroupOf L = R.P₁ := by
    change (MulAction.stabilizer D u).subgroupOf L = R.P₁
    rw [hRP1]
    exact congrArg (fun x => (MulAction.stabilizer D x).subgroupOf L) (by
      norm_num
      exact ht5.symm)
  have hDv : Dv.subgroupOf L = R.P₂ := by
    change (MulAction.stabilizer D v).subgroupOf L = R.P₂
    rw [hRP2]
    exact congrArg (fun x => (MulAction.stabilizer D x).subgroupOf L) (by
      norm_num
      exact ht4.symm)
  have hYam : IsYAmalgamPair M.U ((Du.subgroupOf L).map κ'.toMonoidHom)
      ((Dv.subgroupOf L).map κ'.toMonoidHom) := by
    rw [hDu, hDv]
    rcases hP1map with h1 | h1 <;> rcases hP2map with h2 | h2
    · exfalso
      exact CFSG.Quasithin.H13.F431.BN.P₁_ne_P₂ R
        (Subgroup.map_injective κ'.injective (h1.trans h2.symm))
    · rw [h1, h2]; exact hYamModel
    · rw [h1, h2]; exact hYamSwap
    · exfalso
      exact CFSG.Quasithin.H13.F431.BN.P₁_ne_P₂ R
        (Subgroup.map_injective κ'.injective (h1.trans h2.symm))
  have hBRS : BorelResidualSplit R :=
    hBRST L (Un5Group k F) 4 R M ⟨κ'⟩ hSylowU hmodelSylow
      (hUn5BRS k F hF ζ hk)
  obtain ⟨hLnorm, hcent, hNz, hswap⟩ :=
    hMLN V Δ D (by norm_num) hGP hThick hMoufΔ
  obtain ⟨hrange1, hrange2, hrangeB⟩ :=
    hStab X P1 P2 V Δ D (by norm_num) hGP hThick
      hMoufΔ hLnorm u v ψ1 ψ2 hWEmb.2.2.1 hψ1u hψ2v hWEmb.2.2.2.1 hinter1 hinter2
      htrans1 htrans2 R (by
        have h45 : (((4 : ℕ) : ZMod (2 * 4)) + 1) = ((5 : ℕ) : ZMod (2 * 4)) := by
          norm_num
        rw [hRB]
        congr 1
        ext x
        rw [h45]
        simp [ht4, ht5, and_comm])
      (by left
          constructor
          · rw [hRP1]
            have h45 : (((4 : ℕ) : ZMod (2 * 4)) + 1) = ((5 : ℕ) : ZMod (2 * 4)) := by
              norm_num
            rw [h45]
            simpa [ht5]
          · rw [hRP2]
            simpa [ht4])
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
      rw [hcu, hcv, hcardU, hcardV, hm2k] at hdeg
      have hpow : 2 ^ (3 * k) = 2 ^ (2 * k) := by omega
      have heq : 3 * k = 2 * k :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
      omega
  have hExtApp : IsExtensionOfLieAmalgam (Un5Group k F) P1 P2 :=
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
      hNdiag (Un5Group k F) κ' M.U hYam
  exact ⟨Un5Group k F, inferInstance, isLieOverTwo_un5 hF (by omega), hExtApp⟩

end CFSG.Quasithin.Stroth
