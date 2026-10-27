module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.GH74.GLS.IVK.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenCand
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
import CFSG.CGT.Timmesfeld75.OddCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

abbrev QuotL (Y L : Subgroup (MulAut W)) : Type :=
  ↥(L.subgroupOf Y) ⧸ Subgroup.center ↥(L.subgroupOf Y)

@[expose] noncomputable def quotAct (Y L : Subgroup (MulAut W))
    (hLn : (L.subgroupOf Y).Normal) : ↥Y →* MulAut (QuotL Y L) :=
  letI := hLn
  (quotCenterAut ↥(L.subgroupOf Y)).comp MulAut.conjNormal

omit [Finite W] in
theorem nonempty_quotL_equiv {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) :
    Nonempty (QuotL Y L ≃* (↥L ⧸ Subgroup.center ↥L)) := by
  classical
  let e : ↥(L.subgroupOf Y) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  exact ⟨QuotientGroup.congr (Subgroup.center ↥(L.subgroupOf Y))
    (Subgroup.center ↥L) e (Subgroup.map_center_eq e)⟩

private lemma mem_center_of_mem_ker_quotAct {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L)
    {y : ↥Y} (hy : y ∈ (quotAct Y L hLn).ker) :
    y ∈ (Subgroup.center (L.subgroupOf Y)).map (L.subgroupOf Y).subtype := by
  let L' : Subgroup ↥Y := L.subgroupOf Y
  have : L'.Normal := hLn
  have hperfL' : Group.IsPerfect ↥L' := by
    let e : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
    let : Group.IsPerfect ↥L := hperf
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hq : quotAct Y L hLn y = 1 := MonoidHom.mem_ker.mp hy
  have hq' : quotCenterAut L' (MulAut.conjNormal y) = 1 := hq
  let : Group.IsPerfect ↥L' := hperfL'
  have hcentral : ∀ x : ↥L',
      x⁻¹ * (MulAut.conjNormal y) x ∈ Subgroup.center ↥L' := by
    intro x
    have hfixed : QuotientGroup.mk' (Subgroup.center ↥L') ((MulAut.conjNormal y) x) =
        QuotientGroup.mk' (Subgroup.center ↥L') x := by
      have h := congrArg (fun f : MulAut (QuotL Y L) => f (QuotientGroup.mk x)) hq'
      simpa [quotCenterAut_apply_mk, QuotientGroup.mk'_apply] using h
    apply (QuotientGroup.eq_one_iff (x⁻¹ * (MulAut.conjNormal y) x)).mp
    change QuotientGroup.mk' (Subgroup.center ↥L') (x⁻¹ * (MulAut.conjNormal y) x) = 1
    rw [map_mul, map_inv, hfixed, inv_mul_cancel]
  have hhom := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (MulAut.conjNormal (G := ↥Y) (H := L') y).toMonoidHom hcentral
  have hfix : ∀ x : ↥L', (MulAut.conjNormal (G := ↥Y) (H := L') y) x = x := by
    intro x
    simpa using congrArg (fun f : ↥L' →* ↥L' => f x) hhom
  have hcent : ((y : ↥Y) : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ Y := hLY hz
    have h1 : (MulAut.conjNormal (G := ↥Y) (H := L') y) ⟨⟨z, hz'⟩,
        Subgroup.mem_subgroupOf.mpr hz⟩ = ⟨⟨z, hz'⟩, Subgroup.mem_subgroupOf.mpr hz⟩ := by
      simpa using hfix ⟨⟨z, hz'⟩, Subgroup.mem_subgroupOf.mpr hz⟩
    have h2 : ((y : ↥Y) : MulAut W) * z * ((y : ↥Y) : MulAut W)⁻¹ = z := by
      have h3 : ((MulAut.conjNormal (G := ↥Y) (H := L') y) ⟨⟨z, hz'⟩,
          Subgroup.mem_subgroupOf.mpr hz⟩ : ↥Y) = ⟨z, hz'⟩ := by
        simpa using congrArg (fun w : ↥L' => (w : ↥Y)) h1
      rw [MulAut.conjNormal_apply] at h3
      simpa using congrArg (fun w : ↥Y => (w : MulAut W)) h3
    calc z * ((y : ↥Y) : MulAut W)
        = (((y : ↥Y) : MulAut W) * z * ((y : ↥Y) : MulAut W)⁻¹) *
            ((y : ↥Y) : MulAut W) := by rw [h2]
      _ = ((y : ↥Y) : MulAut W) * z := by group
  have hyL : ((y : ↥Y) : MulAut W) ∈ L :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.mem_of_mem_centralizer_of_fstar_eq
      hLY hF y.2 hcent
  have hyL' : y ∈ L' := Subgroup.mem_subgroupOf.mpr hyL
  have hcenter : (⟨y, hyL'⟩ : ↥L') ∈ Subgroup.center ↥L' := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have h1 : (y : ↥Y) * (x : ↥Y) * (y : ↥Y)⁻¹ = (x : ↥Y) := by
      have h2 := congrArg Subtype.val (hfix x)
      rw [MulAut.conjNormal_apply] at h2
      simpa using h2
    calc (x : ↥Y) * (y : ↥Y) = ((y : ↥Y) * (x : ↥Y) * (y : ↥Y)⁻¹) * (y : ↥Y) := by rw [h1]
      _ = (y : ↥Y) * (x : ↥Y) := by group
  exact Subgroup.mem_map.mpr ⟨⟨y, hyL'⟩, hcenter, rfl⟩

theorem odd_card_ker_quotAct {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hLq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) : Odd (Nat.card (quotAct Y L hLn).ker) := by
  classical
  let L' : Subgroup ↥Y := L.subgroupOf Y
  have : L'.Normal := hLn
  have hperfL : Group.IsPerfect ↥L := hLq.1
  let e : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  have hker_center : (quotAct Y L hLn).ker ≤ (Subgroup.center L').map L'.subtype :=
    fun y hy => mem_center_of_mem_ker_quotAct hLY hLn hF hperfL hy
  have hZoddL : Odd (Nat.card (Subgroup.center ↥L)) := by
    apply CFSG.CGT.Timmesfeld75.odd_card_center
    intro N hNn hN2
    let P : Subgroup (MulAut W) := N.map L.subtype
    have hPle : P ≤ L := Subgroup.map_subtype_le N
    have hP2 : IsPGroup 2 P := hN2.map L.subtype
    have hPn : (P.subgroupOf L).Normal := by
      change (Subgroup.comap L.subtype P).Normal
      rw [show Subgroup.comap L.subtype (N.map L.subtype) = N from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective N]
      exact hNn
    have hPbot : P = ⊥ := hO2 P hPle hPn hP2
    have hNbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxP : L.subtype x ∈ P := ⟨x, hx, rfl⟩
      rw [hPbot, Subgroup.mem_bot] at hxP
      exact Subgroup.mem_bot.mpr (L.subtype_injective (by simpa using hxP))
    exact hNbot
  have hZoddL' : Odd (Nat.card (Subgroup.center ↥L')) := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZoddL
  have hdvd : Nat.card (quotAct Y L hLn).ker ∣ Nat.card (Subgroup.center ↥L') := by
    have h1 := Subgroup.card_dvd_of_le hker_center
    rwa [← Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center L') L'.subtype
      L'.subtype_injective).toEquiv] at h1
  exact Odd.of_dvd_nat hZoddL' hdvd

omit [Finite W] in
theorem map_quotAct {Y L : Subgroup (MulAut W)} (hLn : (L.subgroupOf Y).Normal) :
    (L.subgroupOf Y).map (quotAct Y L hLn) = CFSG.GH74.GLS.IVK.innAut (QuotL Y L) := by
  classical
  let L' : Subgroup ↥Y := L.subgroupOf Y
  have : L'.Normal := hLn
  have hcomp : ∀ l : ↥L', quotAct Y L hLn (l : ↥Y) =
      MulAut.conj (QuotientGroup.mk l) := by
    intro l
    have hconj : MulAut.conjNormal (G := ↥Y) (H := L') (l : ↥Y) = MulAut.conj l := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    change quotCenterAut L' (MulAut.conjNormal (l : ↥Y)) = MulAut.conj (QuotientGroup.mk l)
    rw [hconj, quotCenterAut_conj]
  ext f
  constructor
  · intro hf
    rw [Subgroup.mem_map] at hf
    obtain ⟨l, hl, rfl⟩ := hf
    exact MonoidHom.mem_range.mpr ⟨QuotientGroup.mk ⟨l, hl⟩, (hcomp ⟨l, hl⟩).symm⟩
  · intro hf
    rw [CFSG.GH74.GLS.IVK.innAut, MonoidHom.mem_range] at hf
    obtain ⟨q, rfl⟩ := hf
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact Subgroup.mem_map.mpr ⟨(l : ↥Y), l.2, hcomp l⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix
