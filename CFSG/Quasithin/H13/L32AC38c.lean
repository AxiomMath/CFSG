module

public import CFSG.Quasithin.H13.L32AC38b
public import CFSG.Quasithin.H13.L32A711c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem map_conjClosure_38 {G' : Type*} [Group G'] (f : G →* G') (Z H : Subgroup G) :
    (conjClosure Z H).map f = conjClosure (Z.map f) (H.map f) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine conjClosure_le fun h hh z hz => ?_
    show f (h * z * h⁻¹) ∈ conjClosure (Z.map f) (H.map f)
    rw [map_mul, map_mul, map_inv]
    exact mem_conjClosure (Subgroup.mem_map_of_mem f hh) (Subgroup.mem_map_of_mem f hz)
  · refine conjClosure_le fun h' hh' z' hz' => ?_
    obtain ⟨h, hh, rfl⟩ := hh'
    obtain ⟨z, hz, rfl⟩ := hz'
    exact ⟨h * z * h⁻¹, mem_conjClosure hh hz, by simp⟩

structure Ctx38 (T L V H : Subgroup G) (b c : G) : Prop where
  S : Setting147 G T L V H
  hF : HypF98 T V L (fsuV1 T V) V H
  bH : b ∈ H
  bQ : b ∉ pCoreOf 2 H
  cU : c ∈ conjClosure V H
  cV : c ∉ fsuV1 T V
  tr : ∀ u ∈ conjClosure V H, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * c

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem HN : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := C.hF.toHypF91.H_normalizes_V₁

theorem UH : conjClosure V H ≤ H :=
  C.hF.toHypF91.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)

theorem bN : b ∈ Subgroup.normalizer (fsuV1 T V : Set G) := C.HN C.bH

theorem cN : c ∈ Subgroup.normalizer (fsuV1 T V : Set G) := C.HN (C.UH C.cU)

omit C

@[expose] noncomputable def ct (C : Ctx38 T L V H b c) :
    SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) :=
  secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨c, C.cN⟩

@[expose] noncomputable def Wt (C : Ctx38 T L V H b c) :
    Subgroup (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) :=
  conjClosure (Subgroup.zpowers C.ct) (tildeOf (fsuV1 T V) H)

include C

theorem ct_mem : C.ct ∈ tildeOf (fsuV1 T V) (conjClosure V H) := secMk_mem_secImg C.cU

theorem Wt_le : C.Wt ≤ tildeOf (fsuV1 T V) (conjClosure V H) :=
  conjClosure_zpowers_le (HypF91.tilde_le_normalizer le_rfl) C.ct_mem

theorem hUe : IsElemAbelian 2 C.Wt := by
  have h := C.hF.toHypF91.isElemAbelian_tilde
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => h.2 x (C.Wt_le hx)⟩
  exact F7.isElemAbelian_comm h (C.Wt_le x.2) (C.Wt_le y.2)

theorem tH_le : tildeOf (fsuV1 T V) H ≤ Subgroup.normalizer (C.Wt : Set
    (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) :=
  le_normalizer_conjClosure _ _

omit C

@[expose] noncomputable def ψ (C : Ctx38 T L V H b c) : ↥H →* MulAut (IntMod C.Wt C.hUe) :=
  (convI C.hUe).comp (((secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)).comp
    (Subgroup.inclusion C.HN)).codRestrict _ fun h => C.tH_le (secMk_mem_secImg h.2))

include C

theorem ψ_apply_val (h : ↥H) (w : IntMod C.Wt C.hUe) :
    (C.ψ h w).val = secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
      ⟨h, C.HN h.2⟩ * w.val * (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
        ⟨h, C.HN h.2⟩)⁻¹ :=
  convI_apply_val C.hUe _ w

theorem range_ψ : C.ψ.range = autI C.hUe (tildeOf (fsuV1 T V) H) := by
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    exact convI_mem_autI C.hUe (secMk_mem_secImg h.2) (C.tH_le (secMk_mem_secImg h.2))
  · intro f hf
    obtain ⟨⟨x, hxN⟩, hxH, rfl⟩ := (mem_autI C.hUe).mp hf
    obtain ⟨y, hyH, hyx⟩ := mem_secImg.mp hxH
    refine ⟨⟨y, hyH⟩, ?_⟩
    show convI C.hUe _ = convI C.hUe ⟨x, hxN⟩
    congr 1
    exact Subtype.ext hyx

theorem concl (hG64 : G64.LemmaG64) :
    G64.Conclusion (autI C.hUe (tildeOf (fsuV1 T V) H)) (C.ψ ⟨b, C.bH⟩) := by
  have hR := isTwoReducedIn_tilde C.hF
  have htH := secMk_mem_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G))
    (B := fsuV1 T V) (x := ⟨b, C.bN⟩) C.bH
  have hyp := hyp61_tilde C.hF (isSQTKCat_H C.S) C.bH C.bQ C.cU C.cV C.tr C.bN C.cN C.hUe
  have hv : C.ct ∈ tildeOf (fsuV1 T V) (conjClosure V H) := C.ct_mem
  have hv1 : C.ct ≠ 1 := fun h => C.cV (secMk_eq_one_iff.mp h)
  have htr' := tilde_transvection C.bN C.cN C.tr
  have htC : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, C.bN⟩ ∉
      Subgroup.centralizer (tildeOf (fsuV1 T V) (conjClosure V H) :
        Set (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) := by
    intro hc
    have hV1 : fsuV1 T V ≤ H ⊓ pCoreOf 2 H :=
      le_inf (C.hF.toHypF91.V₁_le_pCoreOf.trans (pCoreOf_le 2 H)) C.hF.toHypF91.V₁_le_pCoreOf
    have h1 : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, C.bN⟩ ∈
        tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) := by
      rw [← C.hF.toHypF91.tilde_inf_centralizer_pCoreOf (le_refl H)]
      exact ⟨htH, hc⟩
    exact C.bQ ((secMk_mem_secImg_iff hV1).mp h1).2
  have hcard := card_commV_transvI C.hUe hR htH hv hv1 htr' htC
  exact hG64 _ (fun w => IntMod.sq_eq_one w) _ _ hyp hcard

abbrev H1 (H : Subgroup G) (b : G) : Subgroup G := conjClosure (Subgroup.zpowers b) H

theorem H1_le : H1 H b ≤ H :=
  conjClosure_le fun _ hh _ hz => H.mul_mem (H.mul_mem hh
    ((Subgroup.zpowers_le.mpr C.bH) hz)) (H.inv_mem hh)

theorem H1_subgroupOf :
    (H1 H b).subgroupOf H = conjClosure (Subgroup.zpowers (⟨b, C.bH⟩ : ↥H)) ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr C.H1_le, map_conjClosure_38,
    MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem map_H1 : ((H1 H b).subgroupOf H).map C.ψ =
    conjClosure (Subgroup.zpowers (C.ψ ⟨b, C.bH⟩)) (autI C.hUe (tildeOf (fsuV1 T V) H)) := by
  rw [C.H1_subgroupOf, map_conjClosure_38, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
    C.range_ψ]

theorem H1t_le : conjClosure (Subgroup.zpowers
    (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, C.bN⟩))
      (tildeOf (fsuV1 T V) H) ≤
    centralizerMod C.Wt (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) := by
  have hN := le_normalizer_centralizerMod (H := tildeOf (fsuV1 T V) H)
    (U := tildeOf (fsuV1 T V) (conjClosure V H)) C.tH_le Subgroup.le_normalizer
    (HypF91.tilde_le_normalizer (V₁ := fsuV1 T V) (Vp := V) le_rfl)
  have hb : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, C.bN⟩ ∈
      centralizerMod C.Wt (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) := by
    have hbH : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, C.bN⟩ ∈
        tildeOf (fsuV1 T V) H := secMk_mem_secImg C.bH
    refine ⟨hbH, C.tH_le hbH, fun u hu => ?_⟩
    rcases tilde_transvection C.bN C.cN C.tr u hu with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h]
      exact (Subgroup.mem_normalizer_iff.mp (C.tH_le (secImg_mono C.UH hu)) _).mp
        (le_conjClosure _ _ (Subgroup.mem_zpowers _))
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) z).mp ((Subgroup.zpowers_le.mpr hb) hz)

theorem le_centralizer_of_mem :
    centralizerMod C.Wt (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) ⊓
        Subgroup.centralizer (C.Wt : Set
          (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) ≤
      Subgroup.centralizer (tildeOf (fsuV1 T V) (conjClosure V H) :
        Set (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) := by
  have hR := isTwoReducedIn_tilde C.hF
  have hUe := C.hF.toHypF91.isElemAbelian_tilde
  have hN1 := le_normalizer_centralizerMod (H := tildeOf (fsuV1 T V) H)
    (U := tildeOf (fsuV1 T V) (conjClosure V H)) C.tH_le Subgroup.le_normalizer
    (HypF91.tilde_le_normalizer (V₁ := fsuV1 T V) (Vp := V) le_rfl)
  have hN2 : tildeOf (fsuV1 T V) H ≤ Subgroup.normalizer (Subgroup.centralizer (C.Wt : Set
      (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) : Set
        (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) :=
    fun h hh => mem_normalizer_centralizer' (C.tH_le hh)
  refine hR.2.2.2 _ (inf_le_left.trans (centralizerMod_le_left _ _ _))
    (fun h hh => Subgroup.inf_normalizer_le_normalizer_inf ⟨hN1 hh, hN2 hh⟩) fun y hy => ?_
  refine ⟨1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  obtain ⟨⟨-, -, hyu⟩, hyW⟩ := hy
  have hw := hyu u hu
  set w := y * u * y⁻¹ * u⁻¹ with hwdef
  have hyw : y * w * y⁻¹ = w := by
    have := Subgroup.mem_centralizer_iff.mp hyW w hw
    rw [← this]
    group
  have hww : w * w = 1 := by
    rw [← pow_two]
    exact hUe.2 w (C.Wt_le hw)
  have hwu : w * u = u * w := F7.isElemAbelian_comm hUe (C.Wt_le hw) hu
  have e1 : y * u * y⁻¹ = w * u := by rw [hwdef]; group
  have e2 : y * y * u * (y * y)⁻¹ = u := by
    calc y * y * u * (y * y)⁻¹ = y * (y * u * y⁻¹) * y⁻¹ := by group
      _ = y * (w * u) * y⁻¹ := by rw [e1]
      _ = (y * w * y⁻¹) * (y * u * y⁻¹) := by group
      _ = u := by rw [hyw, e1, ← mul_assoc, hww, one_mul]
  rw [pow_one, pow_two]
  calc u * (y * y) = (y * y * u * (y * y)⁻¹) * (y * y) := by rw [e2]
    _ = y * y * u := by group

theorem mem_pCoreOf_of_mem_H1 {h : G} (hh : h ∈ H1 H b) (h1 : C.ψ ⟨h, C.H1_le hh⟩ = 1) :
    h ∈ pCoreOf 2 H := by
  have h91 := C.hF.toHypF91
  have hhH : h ∈ H := C.H1_le hh
  have hmem : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨h, C.HN hhH⟩ ∈
      conjClosure (Subgroup.zpowers
        (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, C.bN⟩))
          (tildeOf (fsuV1 T V) H) := by
    have hle : H1 H b ≤ ((conjClosure (Subgroup.zpowers
        (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, C.bN⟩))
          (tildeOf (fsuV1 T V) H)).comap
            (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))).map
              (Subgroup.normalizer (fsuV1 T V : Set G)).subtype := by
      refine conjClosure_le fun g hg z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hgN := C.HN hg
      have hm : g * b ^ k * g⁻¹ ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
        mul_mem (mul_mem hgN (zpow_mem C.bN k)) (inv_mem hgN)
      refine ⟨⟨_, hm⟩, ?_, rfl⟩
      have e : (⟨g * b ^ k * g⁻¹, hm⟩ : ↥(Subgroup.normalizer (fsuV1 T V : Set G))) =
          ⟨g, hgN⟩ * ⟨b, C.bN⟩ ^ k * ⟨g, hgN⟩⁻¹ := rfl
      refine Subgroup.mem_comap.mpr ?_
      rw [e, map_mul, map_mul, map_inv, map_zpow]
      exact mem_conjClosure (secMk_mem_secImg hg) (Subgroup.zpow_mem_zpowers _ k)
    obtain ⟨y, hy, hyh⟩ := hle hh
    have e : (⟨h, C.HN hhH⟩ : ↥(Subgroup.normalizer (fsuV1 T V : Set G))) = y :=
      Subtype.ext hyh.symm
    rw [e]
    exact hy
  have hcW : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨h, C.HN hhH⟩ ∈
      Subgroup.centralizer (C.Wt : Set
        (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) :=
    (convI_eq_one_iff C.hUe _).mp h1
  have hc := C.le_centralizer_of_mem ⟨C.H1t_le hmem, hcW⟩
  have hV1 : fsuV1 T V ≤ H ⊓ pCoreOf 2 H :=
    le_inf (h91.V₁_le_pCoreOf.trans (pCoreOf_le 2 H)) h91.V₁_le_pCoreOf
  have h2 : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨h, C.HN hhH⟩ ∈
      tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) := by
    rw [← h91.tilde_inf_centralizer_pCoreOf (le_refl H)]
    exact ⟨secMk_mem_secImg hhH, hc⟩
  exact ((secMk_mem_secImg_iff hV1).mp h2).2

end Ctx38

end CFSG.Quasithin.H13.L32A.C
