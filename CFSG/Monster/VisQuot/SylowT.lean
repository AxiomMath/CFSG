module

public import CFSG.Monster.VisQuot.MonoRankBound
public import CFSG.Monster.Schur.GmatStructurePhi
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.Existence CFSG.Monster.VisCert CFSG.Monster.Griess

@[expose] def Tbar : Subgroup GLV := Tsd.map monoHom

@[expose] def Tvis : Subgroup Gvis := Tbar.comap CFSG.Monster.Schur.PhiV

@[expose] def toMat (A : Subgroup Gvis) : Subgroup CFSG.Monster.Generated.Gmat :=
  (A.map Gvis.subtype).comap CFSG.Monster.Generated.Gmat.subtype

@[expose] def Tmat : Subgroup CFSG.Monster.Generated.Gmat := toMat Tvis

private theorem natCard_comap_eq_mul {G H : Type*} [Group G] [Group H] {f : G →* H}
    {K : Subgroup H} (hK : K ≤ f.range) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  let g : K.comap f →* K :=
    (f.comp (K.comap f).subtype).codRestrict K fun x => Subgroup.mem_comap.1 x.2
  have hker : g.ker = f.ker.subgroupOf (K.comap f) := by
    dsimp only [g]
    rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker f (K.comap f).subtype,
      Subgroup.comap_subtype]
  have hrange : g.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hK hy)
    exact ⟨⟨x, Subgroup.mem_comap.2 (hx ▸ hy)⟩, Subtype.ext hx⟩
  have hle : f.ker ≤ K.comap f := fun x hx =>
    Subgroup.mem_comap.2 (by rw [show f x = 1 from hx]; exact K.one_mem)
  have h := Subgroup.card_ker_mul_card_range g
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at h
  exact h.symm

theorem mem_Tvis_of_PhiV_eq {g : Gvis} {m : MonoSD} (hm : m ∈ Tsd)
    (h : CFSG.Monster.Schur.PhiV g = monoHom m) : g ∈ Tvis := by
  rw [Tvis, Subgroup.mem_comap, Tbar, Subgroup.mem_map]
  exact ⟨m, hm, h.symm⟩

theorem mem_Tvis_of_PhiV_eq_inl {g : Gvis} (n : Multiplicative (C ⧸ ΩLine))
    (h : CFSG.Monster.Schur.PhiV g = monoHom (SemidirectProduct.inl n)) : g ∈ Tvis := by
  refine mem_Tvis_of_PhiV_eq ?_ h
  rw [mem_Tsd, SemidirectProduct.right_inl]
  exact CFSG.Monster.B.TwoA.Census.sylowSub.one_mem

theorem rhoQvis_le_Tvis : rhoQvis ≤ Tvis := by
  intro g hg
  refine mem_Tvis_of_PhiV_eq (m := 1) Tsd.one_mem ?_
  rw [map_one, ← MonoidHom.mem_ker, CFSG.Monster.Schur.ker_PhiV]
  exact hg

theorem exists_mem_Tsd_of_mem_Tvis {g : Gvis} (hg : g ∈ Tvis) :
    ∃ m ∈ Tsd, CFSG.Monster.Schur.PhiV g = monoHom m := by
  rw [Tvis, Subgroup.mem_comap, Tbar, Subgroup.mem_map] at hg
  obtain ⟨m, hm, hgm⟩ := hg
  exact ⟨m, hm, hgm.symm⟩

theorem natCard_Tsd : Nat.card Tsd = 2 ^ 21 := by
  have hK : Nat.card (CFSG.Monster.B.TwoA.Census.sylowSub.comap AutPerm.subtype) = 2 ^ 10 := by
    have h1 : CFSG.Monster.B.TwoA.Census.sylowSub.comap AutPerm.subtype =
        CFSG.Monster.B.TwoA.Census.sylowSub.subgroupOf AutPerm := by
      ext x
      exact Iff.rfl
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      CFSG.Monster.B.TwoA.Census.sylowSub_le).toEquiv,
      CFSG.Monster.B.TwoA.Census.sylowSub_facts.1]
    norm_num
  have hker : Nat.card (SemidirectProduct.rightHom : MonoSD →* AutPerm).ker = 2 ^ 11 := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv,
      Nat.card_congr Multiplicative.toAdd, natCard_quot_ΩLine]
  have hsurj : Function.Surjective (SemidirectProduct.rightHom : MonoSD →* AutPerm) :=
    SemidirectProduct.rightHom_surjective
  have h := natCard_comap_eq_mul (f := (SemidirectProduct.rightHom : MonoSD →* AutPerm))
    (K := CFSG.Monster.B.TwoA.Census.sylowSub.comap AutPerm.subtype) (fun x _ => by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact Subgroup.mem_top x)
  rw [hker, hK] at h
  rw [show Tsd = (CFSG.Monster.B.TwoA.Census.sylowSub.comap AutPerm.subtype).comap
    (SemidirectProduct.rightHom : MonoSD →* AutPerm) from rfl, h]
  norm_num

theorem natCard_Tvis :
    Nat.card Tvis = 2 ^ 46 := by
  have hrange : CFSG.Monster.Schur.PhiV.range = Hvis := by
    refine le_antisymm (fun ν hν => ?_) fun ν hν => ?_
    · obtain ⟨g, rfl⟩ := hν
      exact CFSG.Monster.Schur.PhiV_mem_Hvis g
    · obtain ⟨g, hg⟩ := CFSG.Monster.Schur.exists_PhiV_eq hν
      exact ⟨g, hg⟩
  have hle : Tbar ≤ CFSG.Monster.Schur.PhiV.range := by
    rw [hrange]
    calc Tbar ≤ CFSG.Monster.VisQuot.monoHom.range := Subgroup.map_le_range monoHom Tsd
      _ = Nvis := Nvis_eq_range_monoHom.symm
      _ ≤ Hvis := Nvis_le_Hvis
  have h := natCard_comap_eq_mul (f := CFSG.Monster.Schur.PhiV) (K := Tbar) hle
  rw [CFSG.Monster.Schur.ker_PhiV, CFSG.Monster.Existence.natCard_rhoQvis] at h
  have hTbar : Nat.card Tbar = 2 ^ 21 := by
    rw [Tbar, Subgroup.card_map_of_injective monoHom_injective, natCard_Tsd]
  rw [show Tvis = Tbar.comap CFSG.Monster.Schur.PhiV from rfl, h, hTbar]
  norm_num

theorem mem_toMat {A : Subgroup Gvis} {g : CFSG.Monster.Generated.Gmat} :
    g ∈ toMat A ↔ ∃ a ∈ A,
      (a : SpaceB ≃ₗ[ℚ] SpaceB) = (g : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [toMat, Subgroup.mem_comap, Subgroup.mem_map]
  constructor <;> rintro ⟨a, ha, h⟩ <;> exact ⟨a, ha, h⟩

theorem map_subtype_toMat (A : Subgroup Gvis) :
    (toMat A).map CFSG.Monster.Generated.Gmat.subtype = A.map Gvis.subtype := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, hga⟩ := mem_toMat.1 hg
    have hga' : Gvis.subtype a = CFSG.Monster.Generated.Gmat.subtype g := hga
    rw [← hga']
    exact Subgroup.mem_map_of_mem Gvis.subtype ha
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨(a : SpaceB ≃ₗ[ℚ] SpaceB), CFSG.Monster.Generated.Hmat_le_Gmat a.2⟩,
      mem_toMat.2 ⟨a, ha, rfl⟩, rfl⟩

theorem toMat_mono {A B : Subgroup Gvis} (h : A ≤ B) : toMat A ≤ toMat B :=
  Subgroup.comap_mono (Subgroup.map_mono h)

theorem toMat_le_centralizer (A : Subgroup Gvis) :
    toMat A ≤ Subgroup.centralizer {CFSG.Monster.Existence.xGmat} := by
  have hle : Gvis ≤ Subgroup.centralizer {CFSG.Monster.Generated.xmat} := by
    have h : CFSG.Monster.Generated.Hmat ≤
        Subgroup.centralizer {CFSG.Monster.Generated.xmat} := by
      rw [← CFSG.Monster.Generated.Gmat_inf_centralizer_xmat]
      exact inf_le_right
    exact h
  intro g hg
  obtain ⟨a, ha, hga⟩ := mem_toMat.1 hg
  have hgG : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := hga ▸ a.2
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  show (g : SpaceB ≃ₗ[ℚ] SpaceB) * CFSG.Monster.Generated.xmat =
    CFSG.Monster.Generated.xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hgG)

theorem natCard_toMat (A : Subgroup Gvis) : Nat.card (toMat A) = Nat.card A := by
  have h : Nat.card ((toMat A).map CFSG.Monster.Generated.Gmat.subtype) =
      Nat.card (toMat A) :=
    Subgroup.card_map_of_injective CFSG.Monster.Generated.Gmat.subtype_injective
  rw [map_subtype_toMat, Subgroup.card_map_of_injective Gvis.subtype_injective] at h
  exact h.symm

theorem isElemAbelian_toMat_iff {A : Subgroup Gvis} :
    CFSG.Open.IsElemAbelian 2 (toMat A) ↔ CFSG.Open.IsElemAbelian 2 A := by
  have hmap := map_subtype_toMat A
  constructor
  · intro h
    have h1 : CFSG.Open.IsElemAbelian 2 ((toMat A).map
        CFSG.Monster.Generated.Gmat.subtype) := h.map CFSG.Monster.Generated.Gmat.subtype
    rw [hmap] at h1
    have h2 : CFSG.Open.IsElemAbelian 2 ((A.map Gvis.subtype).comap Gvis.subtype) :=
      h1.comap Gvis.subtype_injective
    rwa [Subgroup.comap_map_eq_self_of_injective Gvis.subtype_injective A] at h2
  · intro h
    have h1 : CFSG.Open.IsElemAbelian 2 ((toMat A).map
        CFSG.Monster.Generated.Gmat.subtype) := by
      rw [hmap]
      exact h.map Gvis.subtype
    have h2 : CFSG.Open.IsElemAbelian 2 (((toMat A).map
        CFSG.Monster.Generated.Gmat.subtype).comap CFSG.Monster.Generated.Gmat.subtype) :=
      h1.comap CFSG.Monster.Generated.Gmat.subtype_injective
    rwa [Subgroup.comap_map_eq_self_of_injective
      CFSG.Monster.Generated.Gmat.subtype_injective (toMat A)] at h2

theorem toMat_iInf {ι : Type*} [Nonempty ι] (A : ι → Subgroup Gvis) :
    toMat (⨅ i, A i) = ⨅ i, toMat (A i) := by
  simp only [toMat, Subgroup.map_iInf _ Gvis.subtype_injective, Subgroup.comap_iInf]

theorem exists_eq_toMat {B : Subgroup CFSG.Monster.Generated.Gmat} (hB : B ≤ Tmat) :
    ∃ A : Subgroup Gvis, A ≤ Tvis ∧ B = toMat A := by
  refine ⟨(B.map CFSG.Monster.Generated.Gmat.subtype).comap Gvis.subtype, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 ha)
    have hbT : (b : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Tvis.map Gvis.subtype := by
      have h1 : b ∈ Tmat := hB hb
      have h2 : (b : SpaceB ≃ₗ[ℚ] SpaceB) ∈ (toMat Tvis).map
          CFSG.Monster.Generated.Gmat.subtype := Subgroup.mem_map_of_mem _ h1
      rwa [map_subtype_toMat] at h2
    have h3 : Gvis.subtype a ∈ Tvis.map Gvis.subtype := hba ▸ hbT
    rw [← Subgroup.comap_map_eq_self_of_injective Gvis.subtype_injective Tvis]
    exact Subgroup.mem_comap.2 h3
  · have hBmono : B.map CFSG.Monster.Generated.Gmat.subtype ≤ Tvis.map Gvis.subtype := by
      rw [← map_subtype_toMat Tvis]
      exact Subgroup.map_mono hB
    have hle : B.map CFSG.Monster.Generated.Gmat.subtype ≤ Gvis.subtype.range :=
      hBmono.trans (Subgroup.map_le_range Gvis.subtype Tvis)
    show B = (((B.map CFSG.Monster.Generated.Gmat.subtype).comap Gvis.subtype).map
      Gvis.subtype).comap CFSG.Monster.Generated.Gmat.subtype
    rw [Subgroup.map_comap_eq_self hle,
      Subgroup.comap_map_eq_self_of_injective
        CFSG.Monster.Generated.Gmat.subtype_injective B]

theorem xGmat_mem_Tmat : CFSG.Monster.Existence.xGmat ∈ Tmat := by
  refine mem_toMat.2 ⟨(CFSG.Monster.Existence.rhoQvisEquivQ.symm
    CFSG.Monster.Spin.zQ : Gvis), rhoQvis_le_Tvis
      (CFSG.Monster.Existence.rhoQvisEquivQ.symm CFSG.Monster.Spin.zQ).2, ?_⟩
  rw [CFSG.Monster.Existence.rhoQvisEquivQ_symm_zQ]
  rfl

theorem natCard_Tmat :
    Nat.card Tmat = 2 ^ 46 := by
  rw [Tmat, natCard_toMat, natCard_Tvis]

theorem isSylowTwoOf_Tmat
    (hG : Nat.card CFSG.Monster.Generated.Gmat = CFSG.Open.monsterOrder) :
    CFSG.QuasithinUnique.IsSylowTwoOf Tmat ⊤ := by
  set m : ℕ := 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 *
    59 * 71 with hm_def
  have hcard : Nat.card Tmat = 2 ^ 46 := natCard_Tmat
  have hm : CFSG.Open.monsterOrder = 2 ^ 46 * m := by
    rw [hm_def, CFSG.Open.monsterOrder]
    ring
  have hodd : ¬ 2 ∣ m := by
    rw [hm_def]
    norm_num
  refine ⟨le_top, IsPGroup.of_card (n := 46) hcard, ?_⟩
  have hidx : (Tmat.subgroupOf ⊤).index = m := by
    rw [← Subgroup.relIndex_top_right (Tmat.subgroupOf ⊤)]
    have h2 : (Tmat.subgroupOf ⊤).relIndex ⊤ =
        Tmat.relIndex ⊤ := by
      have h := Subgroup.relIndex_subgroupOf (G := CFSG.Monster.Generated.Gmat) (H := Tmat)
        (K := ⊤) (L := ⊤) le_top
      rwa [Subgroup.subgroupOf_self] at h
    rw [h2, Subgroup.relIndex_top_right]
    have hc : Nat.card Tmat * Tmat.index = 2 ^ 46 * m := by
      rw [Tmat.card_mul_index, hG, hm]
    rw [hcard] at hc
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hc
  rw [hidx]
  exact hodd

end CFSG.Monster.VisQuot
