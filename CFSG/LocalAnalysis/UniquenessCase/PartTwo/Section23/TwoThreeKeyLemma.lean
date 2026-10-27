module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatCentMove.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelSolv20_7.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem map_normalizer_eq_inf {X : Type} [Group X] {H : Subgroup X} (K : Subgroup H) :
    (Subgroup.normalizer K).map H.subtype =
      H ⊓ Subgroup.normalizer ((K.map H.subtype : Subgroup X) : Set X) := by
  have hK : K.map H.subtype ≤ H := Subgroup.map_subtype_le K
  have hsub : (K.map H.subtype).subgroupOf H = K := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := H.subtype_injective hyx
      rwa [hxy] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  calc (Subgroup.normalizer K).map H.subtype
      = ((Subgroup.normalizer (K.map H.subtype)).subgroupOf H).map H.subtype := by
        rw [Subgroup.subgroupOf_normalizer_eq hK, hsub]
    _ = Subgroup.normalizer (K.map H.subtype) ⊓ H := Subgroup.subgroupOf_map_subtype _ _
    _ = H ⊓ Subgroup.normalizer (K.map H.subtype) := inf_comm _ _

theorem barSub_eq_map_phiL (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {X : Subgroup G}
    (hX : X ≤ c.L) :
    barSub (⊥ : Subgroup G) c.V hV X =
      ((X.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hgX, rfl⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV X φ).1 hφ
    refine Subgroup.mem_map.mpr ⟨c.phiL hV ⟨g, hX hgX⟩, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hX hgX⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩
  · intro hφ
    obtain ⟨ψ, hψ, hψφ⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨x, hx, hxψ⟩ := Subgroup.mem_map.1 hψ
    rw [← hψφ, ← hxψ]
    exact (mem_barSub (⊥ : Subgroup G) c.V hV X _).2
      ⟨⟨(x : G), c.L_le_stabTil x.2⟩,
        (Subgroup.mem_subgroupOf (H := X) (K := c.L)).mp hx, rfl⟩

theorem ne_bot_V (c : Ctx23L D Ch) : c.V ≠ ⊥ := fun h =>
  uc22main1_Z_ne_bot D (le_bot_iff.mp (h ▸ uc22p22v_le_conjClosure c.N D.Z))

noncomputable abbrev sylowStarImage (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup (MulAut (c.W hV)) :=
  ((c.sylowStar hV : Subgroup ↥(c.H hV))).map (c.H hV).subtype

theorem isSylowIn_sylowStarImage (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    IsSylowIn 2 (c.sylowStarImage hV) (c.H hV) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowIn_of_card_eq (Subgroup.map_subtype_le _) ?_
  rw [Ctx23L.sylowStarImage, Subgroup.card_map_of_injective (c.H hV).subtype_injective]
  exact Sylow.card_eq_multiplicity (c.sylowStar hV)

theorem barSub_T_inf_L_eq_sylowStarImage (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    barSub (⊥ : Subgroup G) c.V hV (D.T ⊓ c.L) = c.sylowStarImage hV := by
  rw [c.barSub_eq_map_phiL hV inf_le_right]
  have hsub : (D.T ⊓ c.L).subgroupOf c.L = D.T.subgroupOf c.L := by
    ext x
    show ((x : G) ∈ D.T ∧ (x : G) ∈ c.L) ↔ (x : G) ∈ D.T
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [hsub]
  change (((D.T.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype) =
    ((c.sylowStar hV : Subgroup ↥(c.H hV))).map (c.H hV).subtype
  rw [c.sylowStar_coe hV]

theorem barSub_normalizer_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    barSub (⊥ : Subgroup G) c.V hV
        (c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G))) =
      c.H hV ⊓ Subgroup.normalizer (c.sylowStarImage hV : Set (MulAut (c.W hV))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SL : Sylow 2 ↥c.L := (c.isSylowIn_T_inf_L).toSylow
  have hSL : (SL : Subgroup ↥c.L) = D.T.subgroupOf c.L := by
    rw [show SL = (c.isSylowIn_T_inf_L).toSylow from rfl,
      CFSG.Quasithin.IsSylowIn.coe_toSylow]
    ext x
    show ((x : G) ∈ D.T ∧ (x : G) ∈ c.L) ↔ (x : G) ∈ D.T
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hSmap : (SL : Subgroup ↥c.L).map (c.phiL hV) =
      (c.sylowStar hV : Subgroup ↥(c.H hV)) := by
    rw [hSL, ← c.sylowStar_coe hV]
  have hsubinf : (D.T ⊓ c.L).subgroupOf c.L = SL := by
    rw [hSL]
    ext x
    show ((x : G) ∈ D.T ∧ (x : G) ∈ c.L) ↔ (x : G) ∈ D.T
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hsub : (c.L ⊓ Subgroup.normalizer
      (((D.T ⊓ c.L : Subgroup G) : Set G))).subgroupOf c.L =
      Subgroup.normalizer (SL : Set ↥c.L) := by
    rw [Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq (inf_le_right : D.T ⊓ c.L ≤ c.L)]
    exact congrArg (fun K : Subgroup ↥c.L => Subgroup.normalizer (K : Set ↥c.L)) hsubinf
  have hmapN : (Subgroup.normalizer (SL : Set ↥c.L)).map (c.phiL hV) =
      Subgroup.normalizer ((c.sylowStar hV : Subgroup ↥(c.H hV)) : Set ↥(c.H hV)) := by
    rw [← normalizer_map_sylow_eq (c.phiL hV) (c.phiL_surjective hV) SL, hSmap]
  rw [c.barSub_eq_map_phiL hV inf_le_left, hsub, hmapN]
  simpa [Ctx23L.sylowStarImage] using
    map_normalizer_eq_inf (H := c.H hV) (c.sylowStar hV : Subgroup ↥(c.H hV))

theorem imgTil_inf_centralizer_eq_fixV (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    imgTil (⊥ : Subgroup G) c.V hV
        (c.V ⊓ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G))) =
      fixV (c.sylowStarImage hV) := by
  rw [← c.barSub_T_inf_L_eq_sylowStarImage hV]
  have hX : D.T ⊓ c.L ≤ stabTil (⊥ : Subgroup G) c.V := by
    refine le_inf ?_ ?_
    · exact (inf_le_left : D.T ⊓ c.L ≤ D.T).trans (c.T_le_stabTil.trans inf_le_left)
    · rw [Subgroup.normalizer_eq_top]
      exact le_top
  exact (fixV_barSub_eq_imgTil_centralizer hV hX).symm

theorem mem_normalizer_of_actTil_mem_stabSub (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {U : Subgroup G} (hU : U ≤ c.V) {g : G} (hg : g ∈ stabTil (⊥ : Subgroup G) c.V)
    (h : actTil (⊥ : Subgroup G) c.V hV ⟨g, hg⟩ ∈
      stabSub (imgTil (⊥ : Subgroup G) c.V hV U)) :
    g ∈ Subgroup.normalizer (U : Set G) := by
  have hinv' : actTil (⊥ : Subgroup G) c.V hV
      ⟨g⁻¹, (stabTil (⊥ : Subgroup G) c.V).inv_mem hg⟩ ∈
      stabSub (imgTil (⊥ : Subgroup G) c.V hV U) := by
    have h' := (stabSub _).inv_mem h
    rw [← map_inv] at h'
    rwa [show (⟨g, hg⟩ : stabTil (⊥ : Subgroup G) c.V)⁻¹ =
      ⟨g⁻¹, (stabTil (⊥ : Subgroup G) c.V).inv_mem hg⟩ from Subtype.ext rfl] at h'
  have happly : ∀ (s : stabTil (⊥ : Subgroup G) c.V) (y : G),
      actTil (⊥ : Subgroup G) c.V hV s ∈ stabSub (imgTil (⊥ : Subgroup G) c.V hV U) →
      y ∈ c.V → y ∈ U → (s : G) * y * (s : G)⁻¹ ∈ U := by
    intro s y hs hyV hyU
    let x : IntMod c.V hV := IntMod.mk hV ⟨y, hyV⟩
    have hq : mkTil (⊥ : Subgroup G) c.V hV x ∈ imgTil (⊥ : Subgroup G) c.V hV U := by
      rw [mem_imgTil]; exact ⟨x, hyU, rfl⟩
    have h1 := (mem_stabSub.mp hs (mkTil (⊥ : Subgroup G) c.V hV x)).2 hq
    rw [actTil_mk, mem_imgTil] at h1
    obtain ⟨z, hzU, hz⟩ := h1
    have h2 := (mkTil_eq_iff (⊥ : Subgroup G) c.V hV z
      (actStab (⊥ : Subgroup G) c.V hV s x)).1 hz
    rw [Subgroup.mem_bot, actStab_apply_val] at h2
    have hxval : (IntMod.mk hV ⟨y, hyV⟩).val = y := rfl
    rw [hxval] at h2
    have h3 : z.val = (s : G) * y * (s : G)⁻¹ := by simpa using mul_inv_eq_one.mp h2
    rwa [← h3]
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    simpa using happly ⟨g⁻¹, (stabTil (⊥ : Subgroup G) c.V).inv_mem hg⟩ y hinv' (hU hy) hy
  · intro hy
    have h1 := happly ⟨g, hg⟩ (g⁻¹ * y * g) h (hU hy) hy
    simpa [mul_assoc] using h1

theorem stableUnder_imgTil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {B U : Subgroup G}
    (hB : B ≤ stabTil (⊥ : Subgroup G) c.V) (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    StableUnder (barSub (⊥ : Subgroup G) c.V hV B) (imgTil (⊥ : Subgroup G) c.V hV U) := by
  intro φ hφ q hq
  obtain ⟨g, hgB, rfl⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV B φ).1 hφ
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) c.V hV U q).1 hq
  rw [actTil_mk, mem_imgTil]
  refine ⟨actStab (⊥ : Subgroup G) c.V hV g x, ?_, rfl⟩
  rw [actStab_apply_val]
  simpa using (Subgroup.mem_normalizer_iff''.1 (hBU (B.inv_mem hgB)) x.val).1 hxU

theorem Tstar_le_normalizer_barSub (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {B : Subgroup G} (hB : B ≤ c.L)
    (hTB : D.T ≤ Subgroup.normalizer (B : Set G)) :
    c.Tstar hV ≤ Subgroup.normalizer
      (barSub (⊥ : Subgroup G) c.V hV B : Set (MulAut (c.W hV))) := by
  intro r hr
  rw [Ctx23L.Tstar, MonoidHom.mem_range] at hr
  obtain ⟨t, rfl⟩ := hr
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have ht : (t : G) ∈ stabTil (⊥ : Subgroup G) c.V := c.T_le_stabTil t.2
  have hBstab : B ≤ stabTil (⊥ : Subgroup G) c.V := hB.trans c.L_le_stabTil
  have hmap := TwelveTwentyThree.barSub_map_conj (V₀ := ⊥) hV hBstab ht
  have hφ : c.phiT hV t = actTil (⊥ : Subgroup G) c.V hV ⟨t, ht⟩ := rfl
  have hBeq : B.map (MulAut.conj (t : G)).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTB t.2)
  calc (barSub (⊥ : Subgroup G) c.V hV B).map
        (MulAut.conj (c.phiT hV t)).toMonoidHom
      = (barSub (⊥ : Subgroup G) c.V hV B).map
          (MulAut.conj (actTil (⊥ : Subgroup G) c.V hV ⟨t, ht⟩)).toMonoidHom := by
        rw [hφ]
    _ = barSub (⊥ : Subgroup G) c.V hV (B.map (MulAut.conj (t : G)).toMonoidHom) := hmap.symm
    _ = barSub (⊥ : Subgroup G) c.V hV B := by rw [hBeq]

noncomputable abbrev infCentralizer (c : Ctx23L D Ch) : Subgroup G :=
  c.V ⊓ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G))

theorem Z_le_infCentralizer (c : Ctx23L D Ch) : D.Z ≤ c.infCentralizer :=
  le_inf (uc22p22v_le_conjClosure c.N D.Z)
    (((omegaOneCenterIn_le_inf_centralizer D.T).trans inf_le_right).trans
      (Subgroup.centralizer_le (inf_le_left : D.T ⊓ c.L ≤ D.T)))

theorem borel_le_normalizer_infCentralizer (c : Ctx23L D Ch) :
    c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (c.infCentralizer : Set G) := by
  intro x hx
  obtain ⟨hxL, hxN⟩ := hx
  have hxV : x ∈ Subgroup.normalizer (c.V : Set G) :=
    ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (sup_le_normalizer_V D Ch c)) hxL
  rw [Subgroup.mem_normalizer_iff]; intro v; constructor
  · rintro ⟨hvV, hvC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hxV v).1 hvV, ?_⟩
    change x * v * x⁻¹ ∈ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G))
    rw [Subgroup.mem_centralizer_iff]; intro s hs
    have hxs : x⁻¹ * s * x ∈ D.T ⊓ c.L := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G))).inv_mem hxN) s).1 hs
    have hcomm : (x⁻¹ * s * x) * v = v * (x⁻¹ * s * x) :=
      Subgroup.mem_centralizer_iff.mp hvC _ hxs
    calc s * (x * v * x⁻¹) = x * ((x⁻¹ * s * x) * v) * x⁻¹ := by group
      _ = x * (v * (x⁻¹ * s * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * v * x⁻¹) * s := by group
  · rintro ⟨hvV, hvC⟩
    have hvV' : v ∈ c.V := by
      have h2 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (c.V : Set G)).inv_mem hxV) (x * v * x⁻¹)).1 hvV
      simpa [mul_assoc] using h2
    refine ⟨hvV', ?_⟩
    change v ∈ Subgroup.centralizer (((D.T ⊓ c.L : Subgroup G) : Set G))
    rw [Subgroup.mem_centralizer_iff]; intro s hs
    have hxs : x⁻¹ * s * x ∈ D.T ⊓ c.L := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G))).inv_mem hxN) s).1 hs
    have hs' : x * s * x⁻¹ ∈ D.T ⊓ c.L :=
      (Subgroup.mem_normalizer_iff.mp hxN s).1 hs
    have hcomm : (x * s * x⁻¹) * (x * v * x⁻¹) = (x * v * x⁻¹) * (x * s * x⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hvC _ hs'
    calc s * v = x⁻¹ * ((x * s * x⁻¹) * (x * v * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * v * x⁻¹) * (x * s * x⁻¹)) * x := by rw [hcomm]
      _ = v * s := by group

theorem irrOn_borel_of_not_le_stabSub (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {k : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) k)
    (hirr : ¬ c.H hV ≤ stabSub (fixV (c.sylowStarImage hV))) :
    ∀ J : Subgroup (c.W hV), J ≤ fixV (c.sylowStarImage hV) →
      StableUnder (barSub (⊥ : Subgroup G) c.V hV
        (c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)))) J →
      J = ⊥ ∨ J = fixV (c.sylowStarImage hV) := by
  have hperfH : ⁅c.H hV, c.H hV⁆ = c.H hV := c.commutator_H_eq hV
  have hHinf : Hinf (c.H hV) = c.H hV := by
    rw [Hinf, CFSG.inSubgroup, ← CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hperfH
  have hmain := kNatBorelIrr_holds (c.W hV) (c.H hV) (c.sylowStarImage hV) (c.H hV) k hnat hperfH
    (c.isSylowIn_sylowStarImage hV) inf_le_left le_rfl hirr
  intro J hJ hst
  refine hmain J hJ ?_
  rw [hHinf, ← c.barSub_normalizer_eq hV]
  exact hst

theorem le_of_inf_invariant (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hirr : ∀ J : Subgroup (c.W hV), J ≤ fixV (c.sylowStarImage hV) →
      StableUnder (barSub (⊥ : Subgroup G) c.V hV
        (c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)))) J →
      J = ⊥ ∨ J = fixV (c.sylowStarImage hV))
    {X : Subgroup G} (hXle : X ≤ c.infCentralizer) (hZ : D.Z ≤ X)
    (hXinv : c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (X : Set G)) : c.infCentralizer ≤ X := by
  have hXleV : X ≤ c.V := hXle.trans inf_le_left
  have hXne : X ≠ ⊥ := fun h => uc22main1_Z_ne_bot D (le_bot_iff.mp (h ▸ hZ))
  have hBstab : c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) ≤
      stabTil (⊥ : Subgroup G) c.V := inf_le_left.trans c.L_le_stabTil
  have himg_le : imgTil (⊥ : Subgroup G) c.V hV X ≤ fixV (c.sylowStarImage hV) := by
    rw [← c.imgTil_inf_centralizer_eq_fixV hV]
    intro q hq
    rw [mem_imgTil] at hq ⊢
    obtain ⟨x, hxX, rfl⟩ := hq
    exact ⟨x, hXle hxX, rfl⟩
  have hstable : StableUnder (barSub (⊥ : Subgroup G) c.V hV
      (c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G))))
      (imgTil (⊥ : Subgroup G) c.V hV X) := c.stableUnder_imgTil hV hBstab hXinv
  have himg_ne : imgTil (⊥ : Subgroup G) c.V hV X ≠ ⊥ := by
    intro h
    have hpre := CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le
      (V₀ := ⊥) hV hXleV bot_le
    rw [h, preTil_bot, inf_bot_eq] at hpre; exact hXne hpre.symm
  have himg_eq : imgTil (⊥ : Subgroup G) c.V hV X =
      imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer := by
    rcases hirr _ himg_le hstable with h | h
    · exact absurd h himg_ne
    · rw [h, c.imgTil_inf_centralizer_eq_fixV hV]
  intro v hv; have hveq : X = c.infCentralizer := by
    rw [← CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le (V₀ := ⊥) hV hXleV bot_le,
      himg_eq, CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le (V₀ := ⊥) hV
        inf_le_left bot_le]
  exact hveq ▸ hv

end Ctx23L

theorem not_le_stabSub_fixV_of_natural {W : Type} [CommGroup W] [Finite W]
    {H S : Subgroup (MulAut W)} {k : ℕ} (hnat : IsNaturalClassicalModule H k)
    (hperf : ⁅H, H⁆ = H) (hS : IsSylowIn 2 S H) (hS1 : S ≠ ⊥) :
    ¬ H ≤ stabSub (fixV S) := by
  intro hH
  have hfixne : fixV S ≠ ⊤ := by
    intro htop
    apply hS1
    rw [eq_bot_iff]
    intro s hs
    ext v
    have hv : v ∈ fixV S := htop ▸ Subgroup.mem_top v
    simpa using (mem_fixV.mp hv s hs)
  have hex : ∃ v : W, v ∉ fixV S := by
    by_contra h
    apply hfixne
    rw [eq_top_iff]
    intro v _
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  have hv1 : v ≠ 1 := fun h1 => hv (h1 ▸ (fixV S).one_mem)
  obtain ⟨h, hhH, -, hstab⟩ :=
    kNatCentMove_holds (W := W) H S k hnat hperf hS v hv1 hv
  exact hstab (hH hhH)

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem H_ne_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) : c.H hV ≠ ⊥ := by
  intro hbot
  have hLcent : c.L ≤ Subgroup.centralizer (c.V : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hmem : (c.phiL hV ⟨l, hl⟩ : MulAut (c.W hV)) ∈ c.H hV := (c.phiL hV ⟨l, hl⟩).2
    have h1 : (c.phiL hV ⟨l, hl⟩ : MulAut (c.W hV)) = 1 :=
      Subgroup.mem_bot.mp (hbot ▸ hmem)
    have h1' : actTil (⊥ : Subgroup G) c.V hV ⟨l, c.L_le_stabTil hl⟩ = 1 := by
      change actTil (⊥ : Subgroup G) c.V hV
        ((Subgroup.inclusion c.L_le_stabTil) ⟨l, hl⟩) = 1
      exact h1
    have h2 := (actTil_eq_one_iff (⊥ : Subgroup G) c.V hV _).1 h1' v hv
    rw [Subgroup.mem_bot] at h2
    have h3 : l * v * l⁻¹ = v := mul_inv_eq_one.mp h2
    exact (calc l * v = (l * v * l⁻¹) * l := by group
      _ = v * l := by rw [h3]).symm
  have hVle : c.V ≤ Subgroup.centralizer (c.L : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLcent hl) v hv).symm
  have hle : c.V ≤ c.V ⊓ Subgroup.centralizer (c.L : Set G) := le_inf le_rfl hVle
  rw [c.fixed_L_eq_bot] at hle
  exact c.ne_bot_V (le_bot_iff.mp hle)

theorem sylowStarImage_ne_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    c.sylowStarImage hV ≠ ⊥ := by
  intro hbot
  have hodd : Odd (Nat.card ↥(c.H hV)) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    simpa [hbot] using (c.isSylowIn_sylowStarImage hV).not_dvd_relIndex
  haveI : Nontrivial ↥(c.H hV) :=
    (Subgroup.nontrivial_iff_ne_bot (c.H hV)).mpr (c.H_ne_bot hV)
  haveI : Group.IsPerfect ↥(c.H hV) := Subgroup.isPerfect_iff.mpr (c.commutator_H_eq hV)
  exact Group.IsPerfect.not_isSolvable ↥(c.H hV) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem not_le_stabSub_fixV_sylowStar {k : ℕ} (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    ¬ c.H hV ≤ stabSub (fixV (c.sylowStarImage hV)) :=
  not_le_stabSub_fixV_of_natural hnat (c.commutator_H_eq hV)
    (c.isSylowIn_sylowStarImage hV) (c.sylowStarImage_ne_bot hV)

theorem le_uCore_of_natural (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    c.infCentralizer ≤ D.U := by
  have hirr := c.not_le_stabSub_fixV_sylowStar hV hnat
  have hB := c.irrOn_borel_of_not_le_stabSub hV hnat hirr
  have hBM : c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) ≤ D.M :=
    c.borel_le_M h207 h209 kBorelSolv20_7_holds h1930
  refine (c.le_of_inf_invariant hV hB (X := D.U ⊓ c.infCentralizer) inf_le_right
    (le_inf (Data.Z_le_U D) (c.Z_le_infCentralizer)) ?_).trans inf_le_left
  exact (le_inf (hBM.trans (le_normalizer_uCore D.M D.T))
    c.borel_le_normalizer_infCentralizer).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem le_U0_of_natural (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    c.infCentralizer ≤ c.U0 := by
  have hirr := c.not_le_stabSub_fixV_sylowStar hV hnat
  have hB := c.irrOn_borel_of_not_le_stabSub hV hnat hirr
  have hBM : c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) ≤ D.M :=
    c.borel_le_M h207 h209 kBorelSolv20_7_holds h1930
  have hBN : c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G)) ≤ c.N :=
    inf_le_left.trans (Ctx23L.L_le_N c)
  refine (c.le_of_inf_invariant hV hB (X := c.U0 ⊓ c.infCentralizer) inf_le_right
    (le_inf (uc22p22v_le_conjClosure (c.N ⊓ D.M) D.Z) (c.Z_le_infCentralizer)) ?_).trans
    inf_le_left
  exact (le_inf ((le_inf hBN hBM).trans
    (uc22p22v_le_normalizer_conjClosure (c.N ⊓ D.M) D.Z))
    c.borel_le_normalizer_infCentralizer).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem inf_normalizer_le_M (c : Ctx23L D Ch) (hU : c.infCentralizer ≤ D.U) :
    c.L ⊓ Subgroup.normalizer (c.infCentralizer : Set G) ≤ D.M := by
  intro x hx
  obtain ⟨hxL, hxN⟩ := hx
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (uc22main1_Z_ne_bot D)
  have hzℓ : (z : G) ∈ c.infCentralizer := c.Z_le_infCentralizer z.2
  have hxz : x * (z : G) * x⁻¹ ∈ c.infCentralizer :=
    (Subgroup.mem_normalizer_iff.mp hxN (z : G)).1 hzℓ
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hne : D.U ⊓ conjSubgroup x D.U ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨x * (z : G) * x⁻¹, hU hxz, ?_⟩, ?_⟩
    · refine CFSG.CGT.Timmesfeld75.mem_conjSubgroup.2 ?_
      have hz : x⁻¹ * (x * (z : G) * x⁻¹) * x = (z : G) := by group
      rw [hz]
      exact Data.Z_le_U D z.2
    · intro h
      have h1 : x * (z : G) * x⁻¹ = 1 := congrArg Subtype.val h
      have h2 : (z : G) = 1 := by
        have := congrArg (fun w => x⁻¹ * w * x) h1
        simpa [mul_assoc] using this
      exact hz1' h2
  exact Ctx23.mem_M_of_ne_bot c.toCtx23 hne
