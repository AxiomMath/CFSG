module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Lift
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin
import CFSG.LocalAnalysis.WeakClosure81.W183K3Dyn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y L A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem br3_false_of_A6 (rows : Br3Rows) (h : Assumption131 Y Γ VA i)
    (hcore : QuasiCore Y L (quasiCentre L)) (hshape : IsAlt (↥L ⧸ Subgroup.center ↥L) 6)
    (hτ : ∃ τ ∈ Y, ActsOnDynkinMod (quasiCentre L) L τ) (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hcard : Nat.card ↥A = 4) : False := by
  classical
  haveI : Finite (LGL 2 V) := inferInstance
  haveI : Finite ↥Y := Subtype.finite
  let N0 : Subgroup ↥Y := (quasiCentre L).subgroupOf Y
  have hN0le : quasiCentre L ≤ Y := (quasiCentre_le L).trans hcore.le
  haveI : N0.Normal := (Subgroup.normal_subgroupOf_iff hN0le).mpr fun hh k hhh hk => by
    rw [mem_quasiCentre] at hhh ⊢
    refine ⟨hcore.normal k hk hh hhh.1, fun l hl => ?_⟩
    have hkl : k⁻¹ * l * k ∈ L := by
      have := hcore.normal k⁻¹ (Y.inv_mem hk) l hl
      simpa using this
    have hc := hhh.2 (k⁻¹ * l * k) hkl
    calc k * hh * k⁻¹ * l
        = k * (hh * (k⁻¹ * l * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * l * k) * hh) * k⁻¹ := by rw [hc]
      _ = l * (k * hh * k⁻¹) := by group
  let mk : ↥Y →* ↥Y ⧸ N0 := QuotientGroup.mk' N0
  let e : ↥L ≃* ↥(L.subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe hcore.le).symm
  let phi : ↥L →* ↥Y ⧸ N0 :=
    (QuotientGroup.mk' N0).comp ((L.subgroupOf Y).subtype.comp e.toMonoidHom)
  let Abar : Subgroup (↥Y ⧸ N0) := (A.subgroupOf Y).map mk
  let Lbar : Subgroup (↥Y ⧸ N0) := (L.subgroupOf Y).map mk
  have hA'el : IsElemAbelian 2 (A.subgroupOf Y) := (h.isElemAb A hA).subgroupOf Y
  have hA'2 : IsPGroup 2 (A.subgroupOf Y) := hA'el.isPGroup
  have hTI' : IsTISub ↥Y (A.subgroupOf Y) := h.isTISub_member hA hr
  have hcardA' : Nat.card ↥(A.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_G A hA)).toEquiv, hcard]
  have hN0_odd : Odd (Nat.card ↥N0) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN0le).toEquiv]
    exact hcore.odd
  have hcardAbar : Nat.card ↥Abar = 4 := by
    rw [card_map_mk_of_isPGroup hN0_odd hA'2, hcardA']
  have hAbarEl : IsElemAbelian 2 Abar := hA'el.map mk
  have hTIAbar : IsTISub (↥Y ⧸ N0) Abar := isTISub_map_mk hN0_odd hA'2 hTI'
  have hLsubNormal : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hcore.le).mpr fun hh k hhh hk => hcore.normal k hk hh hhh
  have hLbarNormal : Lbar.Normal := hLsubNormal.map mk (QuotientGroup.mk'_surjective N0)
  have hker : phi.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hl
      have hl' : ((L.subgroupOf Y).subtype (e l) : ↥Y ⧸ N0) = 1 := by
        show QuotientGroup.mk' N0 ((L.subgroupOf Y).subtype (e l)) = 1
        rw [QuotientGroup.mk'_apply]
        exact hl
      have hmem : (L.subgroupOf Y).subtype (e l) ∈ N0 :=
        (QuotientGroup.eq_one_iff ((L.subgroupOf Y).subtype (e l))).mp hl'
      rw [Subgroup.mem_subgroupOf, mem_quasiCentre] at hmem
      intro g
      apply Subtype.ext
      exact (hmem.2 (g : LGL 2 V) g.2).symm
    · intro hl
      have hmem : (L.subgroupOf Y).subtype (e l) ∈ N0 := by
        rw [Subgroup.mem_subgroupOf, mem_quasiCentre]
        refine ⟨l.2, fun m hm => ?_⟩
        exact (congrArg Subtype.val (hl ⟨m, hm⟩)).symm
      have hl' : ((L.subgroupOf Y).subtype (e l) : ↥Y ⧸ N0) = 1 :=
        (QuotientGroup.eq_one_iff ((L.subgroupOf Y).subtype (e l))).mpr hmem
      show QuotientGroup.mk' N0 ((L.subgroupOf Y).subtype (e l)) = 1
      rw [QuotientGroup.mk'_apply]
      exact hl'
  have hrange : phi.range = Lbar := by
    apply le_antisymm
    · rintro x ⟨l, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(L.subgroupOf Y).subtype (e l), (e l).2, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      show QuotientGroup.mk' N0 ((L.subgroupOf Y).subtype (e (e.symm ⟨y, hy⟩))) =
        QuotientGroup.mk' N0 y
      rw [MulEquiv.apply_symm_apply]
      rfl
  have hiso : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Lbar :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange phi).trans (MulEquiv.subgroupCongr hrange))
  have hLbarAlt : IsAlt ↥Lbar 6 := by
    obtain ⟨e6⟩ := hshape
    exact ⟨hiso.symm.trans e6⟩
  have hCbot : Subgroup.centralizer (Lbar : Set (↥Y ⧸ N0)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N0 z
    rw [Subgroup.mem_bot]
    have hmod : ∀ l ∈ L, (y : LGL 2 V) * l * (y : LGL 2 V)⁻¹ * l⁻¹ ∈ quasiCentre L := by
      intro l hl
      let l' : ↥Y := ⟨l, hcore.le hl⟩
      have hl' : l' ∈ L.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hl
      have hx : mk l' ∈ Lbar := Subgroup.mem_map.mpr ⟨l', hl', rfl⟩
      have hcz := (Subgroup.mem_centralizer_iff.mp hz) (mk l') hx
      have h1 : mk (y * l' * y⁻¹ * l'⁻¹) = 1 := by
        calc mk (y * l' * y⁻¹ * l'⁻¹)
            = mk y * mk l' * (mk y)⁻¹ * (mk l')⁻¹ := by
              simp only [map_mul, map_inv]
          _ = mk l' * mk y * (mk y)⁻¹ * (mk l')⁻¹ := by rw [hcz.symm]
          _ = 1 := by group
      have hmem : y * l' * y⁻¹ * l'⁻¹ ∈ N0 :=
        (QuotientGroup.eq_one_iff (y * l' * y⁻¹ * l'⁻¹)).mp h1
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa [l'] using hmem
    have hcentL : ∀ l ∈ L, (y : LGL 2 V) * l = l * (y : LGL 2 V) :=
      fun l hl => quasi_comm_of_comm_mod_centre hcore.quasi
        (fun m hm => hcore.normal (y : LGL 2 V) y.2 m hm) hmod l hl
    have hyN0 : y ∈ N0 := Subgroup.mem_subgroupOf.mpr (hcore.cent (y : LGL 2 V) y.2 hcentL)
    exact (QuotientGroup.eq_one_iff y).mpr hyN0
  obtain ⟨tau, htauY, hd⟩ := hτ
  have hdN : ActsOnDynkinMod N0 (L.subgroupOf Y) (⟨tau, htauY⟩ : ↥Y) :=
    actsOnDynkinMod_subgroupOf Y hcore.le htauY hd
  have hkerN : mk.ker ⊓ (L.subgroupOf Y) ≤ N0 := by
    change (QuotientGroup.mk' N0).ker ⊓ (L.subgroupOf Y) ≤ N0
    rw [QuotientGroup.ker_mk']
    exact inf_le_left
  have hdbar : ActsOnDynkinMod (N0.map mk) Lbar (mk ⟨tau, htauY⟩) :=
    actsOnDynkinMod_map mk hkerN hdN
  have hNmap : N0.map mk = ⊥ := by
    apply le_antisymm _ bot_le
    rintro x ⟨n, hn, rfl⟩
    rw [Subgroup.mem_bot]
    refine (MonoidHom.mem_ker).mpr ?_
    show n ∈ (QuotientGroup.mk' N0).ker
    rwa [QuotientGroup.ker_mk']
  have htaubar : ∃ taubar : ↥Y ⧸ N0, ActsOnDynkinMod ⊥ Lbar taubar :=
    ⟨mk ⟨tau, htauY⟩, by rw [← hNmap]; exact hdbar⟩
  exact (rows.a6 (↥Y ⧸ N0) Lbar hLbarNormal hLbarAlt hCbot htaubar Abar hcardAbar hAbarEl)
    hTIAbar

end CFSG.LocalAnalysis.WeakClosure81

end
