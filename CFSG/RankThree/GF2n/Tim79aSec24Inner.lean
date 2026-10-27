module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.RankThree.GF2n.Tim79aIdentU3

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem inv_mul_tildeAut_projZ [Finite G] {V H : Subgroup G} {p : Hbar V H} {b r : Xbar V H}
    (hr : (r : Hbar V H) = (b : Hbar V H)⁻¹ * p * b * p⁻¹) :
    (projZ V H b)⁻¹ * tildeAut V H p (projZ V H b) = projZ V H r := by
  haveI := normal_barOf_xOf V H
  have h1 : tildeAut V H p (projZ V H b) = projZ V H (MulAut.conjNormal p b) := tildeAut_mk p b
  have h2 : b⁻¹ * (MulAut.conjNormal p b : Xbar V H) = r := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, hr]
    group
  rw [h1, ← h2, map_mul, map_inv]

theorem mem_cX_of_centralizes {V H : Subgroup G} (hVH : V ≤ H) {c : G} (hcH : c ∈ H)
    (hcen : ∀ z : Xbar V H, piBar V H ⟨c, hcH⟩ * (z : Hbar V H) * (piBar V H ⟨c, hcH⟩)⁻¹ =
      (z : Hbar V H)) : c ∈ cX V H := by
  refine ⟨hcH, fun y hy => ?_⟩
  have hyH : y ∈ H := xOf_le_H hVH hy
  have hyX : piBar V H ⟨y, hyH⟩ ∈ barOf V H (xOf V H) := mem_barOf_iff.mpr ⟨⟨y, hyH⟩, hy, rfl⟩
  have h1 : piBar V H ⟨c, hcH⟩ * piBar V H ⟨y, hyH⟩ * (piBar V H ⟨c, hcH⟩)⁻¹ =
      piBar V H ⟨y, hyH⟩ := hcen ⟨_, hyX⟩
  have h2 : piBar V H (⟨c, hcH⟩ * ⟨y, hyH⟩ * ⟨c, hcH⟩⁻¹ * ⟨y, hyH⟩⁻¹) = 1 := by
    simp only [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := (piBar_eq_one_iff _).1 h2
  simpa [commutatorElement_def] using h3

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem commutator_mem_V_of_mem_P (hc : MinCex M V Q P H) {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    ⁅a, b⁆ ∈ V := by
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hmem : (⁅(⟨a, ha⟩ : P), (⟨b, hb⟩ : P)⁆ : ↥P) ∈ frattini ↥P :=
    CFSG.commutator_le_frattini_of_isPGroup (R := ↥P) (p := 2)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact hc.frattini_P_le ⟨_, hmem, by simp [commutatorElement_def]⟩

theorem commutator_mem_barOf_V (hc : MinCex M V Q P H) {a b : Hbar V H}
    (ha : a ∈ barOf V H P) (hb : b ∈ barOf V H P) : a * b * a⁻¹ * b⁻¹ ∈ barOf V H V := by
  obtain ⟨a', ha', rfl⟩ := mem_barOf_iff.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_barOf_iff.mp hb
  refine mem_barOf_iff.mpr ⟨a' * b' * a'⁻¹ * b'⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  have := hc.commutator_mem_V_of_mem_P ha' hb'
  simpa [commutatorElement_def] using this

theorem tildeAut_fix_VZ (hc : MinCex M V Q P H) {p : Hbar V H} (hp : p ∈ barOf V H P) :
    ∀ a ∈ VZ V H, tildeAut V H p a = a :=
  hc.tildeAut_fix hp

theorem inv_mul_tildeAut_mem_VZ_of_normalizer (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hRV : Rtilde V H P = VZ V H) {p : Hbar V H} (hp : p ∈ barOf V H P) :
    ∀ b ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)), b⁻¹ * tildeAut V H p b ∈ VZ V H := by
  intro b hb
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H)) b
  have hb'b : projZ V H b' = b := hb'
  subst hb'b
  have hbN : b' ∈ Subgroup.normalizer (Vy V H : Set (Xbar V H)) :=
    hc.mem_normalizer_Vy_of_tilde hd hb
  obtain ⟨r, hr, hreq⟩ := hc.commutator_mem_Rbar (Subgroup.inv_mem _ hbN) hp
  have hreq' : (r : Hbar V H) = (b' : Hbar V H)⁻¹ * p * b' * p⁻¹ := by
    rw [hreq, Subgroup.coe_inv, inv_inv]
  rw [inv_mul_tildeAut_projZ hreq', ← hRV]
  exact ⟨r, hr, rfl⟩

theorem inv_mul_tildeAut_mem_VZ_of_Rtilde (hc : MinCex M V Q P H) {p : Hbar V H}
    (hp : p ∈ barOf V H P) :
    ∀ b ∈ Rtilde V H P, b⁻¹ * tildeAut V H p b ∈ VZ V H := by
  intro b hb
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hb
  have hcomm := hc.commutator_mem_barOf_V (Subgroup.inv_mem _ (mem_Rbar.mp hr')) hp
  rw [inv_inv] at hcomm
  rw [inv_mul_tildeAut_projZ (r := ⟨_, barOf_V_le V H hcomm⟩) rfl]
  exact ⟨_, Subgroup.mem_subgroupOf.mpr hcomm, rfl⟩

theorem centralizes_of_tildeAut_eq_conj (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    {p : Hbar V H} {y : Xbar V H} (hα : tildeAut V H p = MulAut.conj (projZ V H y)) :
    ∀ z : Xbar V H, ((y : Hbar V H)⁻¹ * p) * (z : Hbar V H) * ((y : Hbar V H)⁻¹ * p)⁻¹ =
      (z : Hbar V H) := by
  haveI := normal_barOf_xOf V H
  apply hc.centralizes_of_tildeAut_eq_one hd
  intro z
  have hy : projZ V H (MulAut.conjNormal p z) = projZ V H y * projZ V H z * (projZ V H y)⁻¹ := by
    have h' : tildeAut V H p (projZ V H z) = projZ V H (MulAut.conjNormal p z) := tildeAut_mk p z
    rw [← h', hα]
    rfl
  have hcz : (MulAut.conjNormal ((y : Hbar V H)⁻¹ * p) z : Xbar V H) =
      y⁻¹ * MulAut.conjNormal p z * y := by
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hcz, map_mul, map_mul, map_inv, hy]
  group

theorem exists_split_of_tildeAut_eq_conj (hc : MinCex M V Q P H) (hd : Sec23Data V H) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (hyX : y ∈ xOf V H)
    (hα : tildeAut V H (piBar V H ⟨x, hc.PleH hx⟩) = MulAut.conj (xToZ hc.V_le_H ⟨y, hyX⟩)) :
    ∃ c ∈ cPbar V H P, x = y * c := by
  have hyH : y ∈ H := hc.PleH hy
  have hxH : x ∈ H := hc.PleH hx
  have hcen := hc.centralizes_of_tildeAut_eq_conj hd (y := xToXbar hc.V_le_H ⟨y, hyX⟩) hα
  have hmem : y⁻¹ * x ∈ H := H.mul_mem (H.inv_mem hyH) hxH
  have e : piBar V H ⟨y⁻¹ * x, hmem⟩ =
      ((xToXbar hc.V_le_H ⟨y, hyX⟩ : Xbar V H) : Hbar V H)⁻¹ * piBar V H ⟨x, hxH⟩ := by
    show piBar V H (⟨y, hyH⟩⁻¹ * ⟨x, hxH⟩) = (piBar V H ⟨y, hyH⟩)⁻¹ * piBar V H ⟨x, hxH⟩
    rw [map_mul, map_inv]
  refine ⟨y⁻¹ * x, Subgroup.mem_inf.mpr ⟨P.mul_mem (P.inv_mem hy) hx,
    mem_cX_of_centralizes hc.V_le_H hmem fun z => ?_⟩, by group⟩
  rw [e]
  exact hcen z

theorem exists_mem_V_of_mem_VZ (hc : MinCex M V Q P H) {s : XbarZ V H} (hs : s ∈ VZ V H) :
    ∃ (v : G) (hv : v ∈ V), xToZ hc.V_le_H ⟨v, le_xOf (V_mem_omegaOf V H) hv⟩ = s := by
  obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hs
  obtain ⟨v, hv, hvv⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hv')
  refine ⟨(v : G), hv, ?_⟩
  rw [xToZ_apply]
  congr 1
  exact Subtype.ext hvv

theorem exists_mem_P_inf_xOf_of_mem_Rtilde (hc : MinCex M V Q P H) {s : XbarZ V H}
    (hs : s ∈ Rtilde V H P) :
    ∃ (y : G) (hy : y ∈ P ⊓ xOf V H), xToZ hc.V_le_H ⟨y, hy.2⟩ = s := by
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hs
  obtain ⟨y, hyP, hyr⟩ := mem_barOf_iff.mp (mem_Rbar.mp hr')
  have hyX : (y : G) ∈ xOf V H := by
    refine preimOf_le_xOf (S := barOf V H (xOf V H)) le_rfl (mem_preimOf.mpr ⟨y, rfl, ?_⟩)
    rw [hyr]
    exact r'.2
  refine ⟨(y : G), ⟨hyP, hyX⟩, ?_⟩
  rw [xToZ_apply]
  congr 1
  exact Subtype.ext hyr

theorem exists_mul_cPbar_of_rootInnerModel (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hm : RootInnerModel (XbarZ V H) (VZ V H)) (hRV : Rtilde V H P = VZ V H) {x : G}
    (hx : x ∈ P) : ∃ v ∈ V, ∃ c ∈ cPbar V H P, x = v * c := by
  have hp : piBar V H ⟨x, hc.PleH hx⟩ ∈ barOf V H P := mem_barOf_iff.mpr ⟨_, hx, rfl⟩
  obtain ⟨s, hsV, hαs⟩ := hm (tildeAut V H (piBar V H ⟨x, hc.PleH hx⟩)) (hc.tildeAut_fix_VZ hp)
    (hc.inv_mul_tildeAut_mem_VZ_of_normalizer hd hRV hp)
  obtain ⟨v, hv, hvs⟩ := hc.exists_mem_V_of_mem_VZ hsV
  obtain ⟨c, hcC, hxc⟩ := hc.exists_split_of_tildeAut_eq_conj hd hx (hc.V_le_P hv)
    (le_xOf (V_mem_omegaOf V H) hv) (by rw [hvs]; exact hαs)
  exact ⟨v, hv, c, hcC, hxc⟩

theorem le_sup_cPbar_of_rootS2Model (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hm : RootS2Model (XbarZ V H) (VZ V H)) (hRT : Sec24bTilde V H P) :
    P ≤ (P ⊓ xOf V H) ⊔ cPbar V H P := by
  have hRT' : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := hRT
  intro x hx
  have hp : piBar V H ⟨x, hc.PleH hx⟩ ∈ barOf V H P := mem_barOf_iff.mpr ⟨_, hx, rfl⟩
  obtain ⟨s, hsO, hαs⟩ := hm (tildeAut V H (piBar V H ⟨x, hc.PleH hx⟩)) (hc.tildeAut_fix_VZ hp)
    (by rw [← hRT']; exact hc.inv_mul_tildeAut_mem_VZ_of_Rtilde hp)
  rw [← hRT'] at hsO
  obtain ⟨y, hy, hys⟩ := hc.exists_mem_P_inf_xOf_of_mem_Rtilde hsO
  obtain ⟨c, hcC, hxc⟩ := hc.exists_split_of_tildeAut_eq_conj hd hx hy.1 hy.2
    (by rw [hys]; exact hαs)
  rw [hxc]
  exact Subgroup.mul_mem_sup hy hcC

end MinCex

theorem tim79aSec24InnerTildeStatement_of_model (hk : RootPairOfKindStatement)
    (hm : RootInnerAll) : Tim79aSec24InnerTildeStatement := by
  intro G _ _ M V Q P H hs hcase hRV x hx
  exact hs.mc.toMinCex.exists_mul_cPbar_of_rootInnerModel hs.data
    (hm (XbarZ V H) (VZ V H) (hk G M V Q P H hs hcase)) hRV hx

theorem tim79aSec25S2TildeStatement_of_model (hk : RootPairOfKindStatement) (hm : RootS2All) :
    Tim79aSec25S2TildeStatement := by
  intro G _ _ M V Q P H hs hcase hRT
  exact hs.mc.toMinCex.le_sup_cPbar_of_rootS2Model hs.data
    (hm (XbarZ V H) (VZ V H) (hk G M V Q P H hs hcase)) hRT

end CFSG.RankThree.GF2n.Tim79a
