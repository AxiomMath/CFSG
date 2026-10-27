module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVDeg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVInvol
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveTransport
public import CFSG.Quasithin.Background.HLUBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotSp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Vtil_sq_eq_one {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (w : Vtil V₀ V hV) :
    w ^ 2 = 1 := by
  induction w using QuotientGroup.induction_on with
  | H x => rw [← QuotientGroup.mk_pow]; simp [IntMod.sq_eq_one]

theorem map_congrHom_symm_eq {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) :
    H'.map (CFSG.Quasithin.H.congrHom e.symm) = H := by
  rw [h, Subgroup.map_map, CFSG.Quasithin.H.LU.congrHom_symm_comp, Subgroup.map_id]

noncomputable def subgroupCongrHomEquiv {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) : ↥H ≃* ↥H' :=
  ((MulAut.congr e).subgroupMap H).trans (MulEquiv.subgroupCongr h.symm)

theorem realizes_of_map_congrHom {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) {D : FFModel}
    (hR : D.Realizes H' ⊤ ⊥) : D.Realizes H ⊤ ⊥ := by
  rw [← map_congrHom_symm_eq e h]
  exact CFSG.Quasithin.H.LU.realizes_map D e.symm hR

theorem isSpn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSpn X n a) : IsSpn Y n a := by
  obtain ⟨hn, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem binaryNaturalSL_of_map_congrHom {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) {d a : ℕ}
    (hN : BinaryNaturalSL H' ⊤ ⊥ d a) : BinaryNaturalSL H ⊤ ⊥ d a := by
  obtain ⟨K, hF, hFin, hK, hR⟩ := hN
  exact ⟨K, hF, hFin, hK, realizes_of_map_congrHom e h hR⟩

theorem natSpn_of_map_congrHom {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) {n a : ℕ}
    (hN : NatSpn H' ⊤ ⊥ n a) : NatSpn H ⊤ ⊥ n a := by
  obtain ⟨hn, K, hF, hFin, hK, hR⟩ := hN
  exact ⟨hn, K, hF, hFin, hK, realizes_of_map_congrHom e h hR⟩

theorem natOmegaPlus_of_map_congrHom {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) {n a : ℕ}
    (hN : NatOmegaPlus H' ⊤ ⊥ n a) : NatOmegaPlus H ⊤ ⊥ n a := by
  obtain ⟨hn, K, hF, hFin, hK, hR⟩ := hN
  exact ⟨hn, K, hF, hFin, hK, realizes_of_map_congrHom e h hR⟩

theorem natOmegaMinus_of_map_congrHom {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) {n a : ℕ}
    (hN : NatOmegaMinus H' ⊤ ⊥ n a) : NatOmegaMinus H ⊤ ⊥ n a := by
  obtain ⟨hn, K, hF, hFin, b, c, hK, hirr, hR⟩ := hN
  exact ⟨hn, K, hF, hFin, b, c, hK, hirr, realizes_of_map_congrHom e h hR⟩

theorem natSUn_of_map_congrHom {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) {n a : ℕ}
    (hN : NatSUn H' ⊤ ⊥ n a) : NatSUn H ⊤ ⊥ n a := by
  obtain ⟨K, hF, hFin, hK, hR⟩ := hN
  exact ⟨K, hF, hFin, hK, realizes_of_map_congrHom e h hR⟩

theorem IsNaturalClassicalModule.of_map_congrHom {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    (h : H' = H.map (CFSG.Quasithin.H.congrHom e)) {n : ℕ}
    (hnat : IsNaturalClassicalModule H' n) : IsNaturalClassicalModule H n := by
  let eH := subgroupCongrHomEquiv e h
  rcases hnat with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact Or.inl ⟨CFSG.Blueprint.LieModel.of_mulEquiv eH.symm h1.1,
      binaryNaturalSL_of_map_congrHom e h h1.2⟩
  · exact Or.inr (Or.inl ⟨IsOmegaMinus.of_mulEquiv eH.symm h2.1,
      natOmegaMinus_of_map_congrHom e h h2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨IsOmegaPlus.of_mulEquiv eH.symm h3.1,
      natOmegaPlus_of_map_congrHom e h h3.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨CFSG.Blueprint.LieModel.of_mulEquiv eH.symm h4.1,
      natSpn_of_map_congrHom e h h4.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨IsSLn.of_mulEquiv eH.symm h5.1, binaryNaturalSL_of_map_congrHom e h h5.2⟩))))
  · obtain ⟨a, hn, h6a, h6b⟩ := h6
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, hn, IsSUn.of_mulEquiv eH.symm h6a, natSUn_of_map_congrHom e h h6b⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨IsOmegaMinus.of_mulEquiv eH.symm h7.1, natOmegaMinus_of_map_congrHom e h h7.2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨IsSLn.of_mulEquiv eH.symm h8.1, binaryNaturalSL_of_map_congrHom e h h8.2⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨IsOmegaPlus.of_mulEquiv eH.symm h9.1, natOmegaPlus_of_map_congrHom e h h9.2⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨isSpn_of_mulEquiv eH.symm h10.1, natSpn_of_map_congrHom e h h10.2⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨CFSG.Blueprint.LieModel.of_mulEquiv eH.symm h11.1,
        natOmegaMinus_of_map_congrHom e h h11.2⟩)))))))))

theorem barSub_le_stabSub_imgTil {V A L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : IsElemAbelian 2 A) (hAV : A ≤ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) :
    barSub ⊥ V hV L ≤ stabSub (imgTil ⊥ V hV A) := by
  intro φ hφ
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V hV L φ).1 hφ
  exact actTil_mem_stabSub_imgTil hV hA hAV (mem_stabTil_bot (hLV hgL))
    (mem_stabTil_bot (hLA hgL))

theorem actTil_mem_normalizer_barSub {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hL : L ≤ stabTil (⊥ : Subgroup G) V) {g : G} (hg : g ∈ stabTil (⊥ : Subgroup G) V)
    (hgL : L.map (MulAut.conj g).toMonoidHom = L) :
    actTil (⊥ : Subgroup G) V hV ⟨g, hg⟩ ∈
      Subgroup.normalizer (barSub (⊥ : Subgroup G) V hV L) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  calc (barSub (⊥ : Subgroup G) V hV L).map
        (MulAut.conj (actTil (⊥ : Subgroup G) V hV ⟨g, hg⟩)).toMonoidHom
      = barSub (⊥ : Subgroup G) V hV (L.map (MulAut.conj g).toMonoidHom) :=
        (TwelveTwentyThree.barSub_map_conj hV hL hg).symm
    _ = barSub (⊥ : Subgroup G) V hV L := by rw [hgL]

theorem autQuot_commutator {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {U : Subgroup V} (hH : H ≤ stabSub U) (hperf : ⁅H, H⁆ = H) :
    ⁅autQuot H U, autQuot H U⁆ = autQuot H U := by
  have hsub : ⁅H.subgroupOf (stabSub U), H.subgroupOf (stabSub U)⁆ =
      H.subgroupOf (stabSub U) := by
    apply Subgroup.map_injective (stabSub U).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hH, hperf]
  calc ⁅autQuot H U, autQuot H U⁆
      = ⁅(H.subgroupOf (stabSub U)).map (quotHom U),
          (H.subgroupOf (stabSub U)).map (quotHom U)⁆ := rfl
    _ = (⁅H.subgroupOf (stabSub U), H.subgroupOf (stabSub U)⁆).map (quotHom U) :=
        (Subgroup.map_commutator _ _ (quotHom U)).symm
    _ = (H.subgroupOf (stabSub U)).map (quotHom U) := by rw [hsub]
    _ = autQuot H U := rfl

theorem resHom_mem_normalizer_autSub {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {U : Subgroup V} {s : MulAut V} (hsU : s ∈ stabSub U)
    (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    resHom U ⟨s, hsU⟩ ∈ Subgroup.normalizer (autSub H U : Set (MulAut ↥U)) := by
  have h1 : (⟨s, hsU⟩ : ↥(stabSub U)) ∈
      Subgroup.normalizer ((H.subgroupOf (stabSub U) : Subgroup ↥(stabSub U)) :
        Set ↥(stabSub U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp hsN (h : MulAut V)
  exact Subgroup.le_normalizer_map (resHom U) ⟨⟨s, hsU⟩, h1, rfl⟩

theorem quotHom_mem_normalizer_autQuot {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {U : Subgroup V} {s : MulAut V} (hsU : s ∈ stabSub U)
    (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    quotHom U ⟨s, hsU⟩ ∈ Subgroup.normalizer (autQuot H U : Set (MulAut (V ⧸ U))) := by
  have h1 : (⟨s, hsU⟩ : ↥(stabSub U)) ∈
      Subgroup.normalizer ((H.subgroupOf (stabSub U) : Subgroup ↥(stabSub U)) :
        Set ↥(stabSub U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp hsN (h : MulAut V)
  exact Subgroup.le_normalizer_map (quotHom U) ⟨⟨s, hsU⟩, h1, rfl⟩

private theorem false_of_centralizes_of_not_centralizes {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {s : MulAut V}
    (hs : s ∈ Subgroup.centralizer (H : Set (MulAut V)))
    (hnotcent : ∃ h ∈ H, s * h * s⁻¹ ≠ h) : False := by
  obtain ⟨h, hh, hne⟩ := hnotcent
  apply hne
  have hcomm : h * s = s * h := Subgroup.mem_centralizer_iff.mp hs h hh
  calc s * h * s⁻¹ = (h * s) * s⁻¹ := by rw [hcomm]
    _ = h := by group

theorem orderOf_resHom_eq_two {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {A' : Subgroup V}
    (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCA : ∀ h : ↥H, (h : MulAut V) ∈ centSub A' → h ∈ Subgroup.center ↥H)
    {s : MulAut V} (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hsA : s ∈ stabSub A') (hs2 : orderOf s = 2)
    (hnotcent : ∃ h ∈ H, s * h * s⁻¹ ≠ h) :
    orderOf (resHom A' ⟨s, hsA⟩) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2' : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hsq : resHom A' ⟨s, hsA⟩ ^ 2 = 1 := by
    calc resHom A' ⟨s, hsA⟩ ^ 2
        = resHom A' ((⟨s, hsA⟩ : ↥(stabSub A')) ^ 2) := (map_pow _ _ _).symm
      _ = 1 := by
          rw [show (⟨s, hsA⟩ : ↥(stabSub A')) ^ 2 = 1 from Subtype.ext (by simpa using hs2'),
            map_one]
  refine orderOf_eq_prime hsq ?_
  intro h1
  have hcent : resHom A' ⟨s, hsA⟩ ∈
      Subgroup.centralizer (autSub H A' : Set (MulAut ↥A')) := by
    rw [h1]
    exact Subgroup.one_mem _
  exact false_of_centralizes_of_not_centralizes
    (CFSG.GroupTheory.centralizes_of_resAut_mem_centralizer hH hHA hCA hsN hsA hcent)
    hnotcent

theorem orderOf_quotHom_eq_two {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {A' : Subgroup V}
    (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCW : ∀ h : ↥H, (h : MulAut V) ∈ centQuot A' → h ∈ Subgroup.center ↥H)
    {s : MulAut V} (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hsA : s ∈ stabSub A') (hs2 : orderOf s = 2)
    (hnotcent : ∃ h ∈ H, s * h * s⁻¹ ≠ h) :
    orderOf (quotHom A' ⟨s, hsA⟩) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2' : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hsq : quotHom A' ⟨s, hsA⟩ ^ 2 = 1 := by
    calc quotHom A' ⟨s, hsA⟩ ^ 2
        = quotHom A' ((⟨s, hsA⟩ : ↥(stabSub A')) ^ 2) := (map_pow _ _ _).symm
      _ = 1 := by
          rw [show (⟨s, hsA⟩ : ↥(stabSub A')) ^ 2 = 1 from Subtype.ext (by simpa using hs2'),
            map_one]
  refine orderOf_eq_prime hsq ?_
  intro h1
  have hcent : quotHom A' ⟨s, hsA⟩ ∈
      Subgroup.centralizer (autQuot H A' : Set (MulAut (V ⧸ A'))) := by
    rw [h1]
    exact Subgroup.one_mem _
  exact false_of_centralizes_of_not_centralizes
    (CFSG.GroupTheory.centralizes_of_quotHom_mem_centralizer hH hHA hCW hsN hsA hcent)
    hnotcent

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem L_le_normalizers (c : Ctx23L D Ch) {A : Subgroup G}
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    c.L ≤ stabTil (⊥ : Subgroup G) c.V ∧
      c.L ≤ Subgroup.normalizer (c.V : Set G) ∧
      c.L ≤ Subgroup.normalizer (A : Set G) :=
  ⟨c.L_le_stabTil, fun l hl => (c.L_le_stabTil hl).1, fun l hl => hAN (c.L_le_N hl)⟩

private theorem actN_mem_normalizer_barSub (c : Ctx23L D Ch)
    (hLN : (c.L.subgroupOf c.N).Normal) {x : c.N} :
    actN c x ∈ Subgroup.normalizer (barSub ⊥ c.V (isElemAbelian_V_basic c) c.L) := by
  let hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  have hNL : c.N ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (c.L_le_N)).mp hLN
  have hxV : (x : G) ∈ stabTil (⊥ : Subgroup G) c.V :=
    mem_stabTil_bot (uc22p22v_le_normalizer_conjClosure c.N D.Z x.2)
  have hxL : c.L.map (MulAut.conj (x : G)).toMonoidHom = c.L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNL x.2)
  simpa [actN] using actTil_mem_normalizer_barSub hV c.L_le_stabTil hxV hxL

private theorem actN_mem_stabSub_imgTil (c : Ctx23L D Ch) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {x : c.N} :
    actN c x ∈ stabSub (imgTil ⊥ c.V (isElemAbelian_V_basic c) A) := by
  let hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  have hxV : (x : G) ∈ stabTil (⊥ : Subgroup G) c.V :=
    mem_stabTil_bot (uc22p22v_le_normalizer_conjClosure c.N D.Z x.2)
  simpa [actN] using
    actTil_mem_stabSub_imgTil hV hA hAV hxV (mem_stabTil_bot (hAN x.2))

theorem k_add_two_le_rkIdx_fixV_of_mem_N (c : Ctx23L D Ch) (hTv : KNoTransv)
    (hLN : (c.L.subgroupOf c.N).Normal)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {k : ℕ} (hnat : IsNaturalClassicalModule (barSub ⊥ A hA c.L) k)
    (hk : 3 ≤ k ∨ 2 ≤ k ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k)
    (hCA : ∀ h : ↥(barSub ⊥ c.V (isElemAbelian_V_basic c) c.L),
      (h : MulAut (Vtil ⊥ c.V (isElemAbelian_V_basic c))) ∈
        centSub (imgTil ⊥ c.V (isElemAbelian_V_basic c) A) →
      h ∈ Subgroup.center ↥(barSub ⊥ c.V (isElemAbelian_V_basic c) c.L))
    (hCW : ∀ h : ↥(barSub ⊥ c.V (isElemAbelian_V_basic c) c.L),
      (h : MulAut (Vtil ⊥ c.V (isElemAbelian_V_basic c))) ∈
        centQuot (imgTil ⊥ c.V (isElemAbelian_V_basic c) A) →
      h ∈ Subgroup.center ↥(barSub ⊥ c.V (isElemAbelian_V_basic c) c.L))
    {x : c.N} (hs2 : orderOf (actN c x) = 2)
    (hnotcent : ∃ h ∈ barSub ⊥ c.V (isElemAbelian_V_basic c) c.L,
      actN c x * h * (actN c x)⁻¹ ≠ h) :
    k + 2 ≤ rkIdx (fixV (Subgroup.zpowers (actN c x))) := by
  let hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  let H : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
  let A' : Subgroup (Vtil ⊥ c.V hV) := imgTil ⊥ c.V hV A
  have hNL : c.N ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (c.L_le_N)).mp hLN
  obtain ⟨hLst, hLV, hLA⟩ := L_le_normalizers c hAN
  have hH : ⁅H, H⁆ = H := barSub_commutator hV hLst c.hL.1.2.1
  have hHA : H ≤ stabSub A' := barSub_le_stabSub_imgTil hV hA hAV hLV hLA
  obtain ⟨e, he⟩ := Mbar_eq_autSub_map hV hA hAV hLV hLA
  have hnatA : IsNaturalClassicalModule (autSub H A') k :=
    IsNaturalClassicalModule.of_map_congrHom e he hnat
  let eH : ↥(autSub H A') ≃* ↥(barSub ⊥ A hA c.L) := subgroupCongrHomEquiv e he
  have hkA : 3 ≤ k ∨ 2 ≤ k ∧ IsOmegaMinus ↥(autSub H A') 4 k := by
    rcases hk with h3 | ⟨h2, hOm⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h2, IsOmegaMinus.of_mulEquiv eH.symm hOm⟩
  have hsN := actN_mem_normalizer_barSub c hLN (x := x)
  have hsA := actN_mem_stabSub_imgTil c hA hAV hAN (x := x)
  have hsAN : resHom A' ⟨actN c x, hsA⟩ ∈
      Subgroup.normalizer (autSub H A' : Set (MulAut ↥A')) :=
    resHom_mem_normalizer_autSub hsA hsN
  have hsBN : quotHom A' ⟨actN c x, hsA⟩ ∈
      Subgroup.normalizer (autQuot H A' : Set (MulAut ((Vtil ⊥ c.V hV) ⧸ A'))) :=
    quotHom_mem_normalizer_autQuot hsA hsN
  have hperfB : ⁅autQuot H A', autQuot H A'⁆ = autQuot H A' := autQuot_commutator hHA hH
  have hs2A : orderOf (resHom A' ⟨actN c x, hsA⟩) = 2 :=
    orderOf_resHom_eq_two hH hHA hCA hsN hsA hs2 hnotcent
  have hs2B : orderOf (quotHom A' ⟨actN c x, hsA⟩) = 2 :=
    orderOf_quotHom_eq_two hH hHA hCW hsN hsA hs2 hnotcent
  exact k_add_two_le_rkIdx_fixV_zpowers (W := Vtil ⊥ c.V hV) (H := H) (A' := A')
    (Vtil_sq_eq_one hV) hH hHA hCA hCW hnatA hkA hsN hsA hs2 hnotcent hsAN hs2A hsBN hs2B
    hperfB hTv

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
