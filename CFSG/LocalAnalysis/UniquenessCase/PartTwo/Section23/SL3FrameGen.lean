module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerCartanCommute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSL3FrameTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3FramePoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx2311

noncomputable abbrev frameKStar {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) : Subgroup ↥(c.H F.hV) :=
  (c.K.subgroupOf c.L).map (c.phiL F.hV)

abbrev frameE {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (x : Fin 3 → ↥c.L) (i : Fin 3) : Subgroup G :=
  conjSubgroup c.E (x i : G)

abbrev frameS {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch) : Subgroup G :=
  CFSG.Open.pCoreOf 2 c.L

abbrev frameS0 {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (x : Fin 3 → ↥c.L) : Subgroup G :=
  ⨆ i, frameE x i ⊓ frameS c

private theorem frame_E_le_L {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) : frameE x i ≤ c.L := by
  have hE : c.E ≤ c.L :=
    (Ctx2311.E_le_K c F.h1930 F.h4 F.h12 F.hN8).trans c.K_le_L
  rintro y ⟨a, ha, rfl⟩
  exact c.L.mul_mem (c.L.mul_mem (c.L.inv_mem (x i).2) (hE ha))
    (c.L.inv_mem (c.L.inv_mem (x i).2))

private theorem frame_S_le_M {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch} :
    frameS c ≤ D.M :=
  (Ctx23L.pCoreOf_L_le_T D Ch c.toCtx23L).trans D.sylowM.le

private theorem frame_S_le_conj_M {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (x : Fin 3 → ↥c.L) (i : Fin 3) : frameS c ≤ conjSubgroup D.M (x i : G) := by
  have hSL : c.L ≤ Subgroup.normalizer (frameS c : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) c.L
  have hfix : conjSubgroup (frameS c) (x i : G) = frameS c :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hSL (x i).2)
  rw [← hfix]
  exact Subgroup.map_mono (f := (MulAut.conj (x i : G)⁻¹).toMonoidHom) (frame_S_le_M (c := c))

private theorem frame_conj_M_le_normalizer {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup D.M (x i : G) ≤
      Subgroup.normalizer (frameE x i : Set G) := by
  have hM : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  have hN : conjSubgroup (Subgroup.normalizer (c.E : Set G)) (x i : G) =
      Subgroup.normalizer (frameE x i : Set G) := by
    change (Subgroup.normalizer (c.E : Set G)).map
        (MulAut.conj (x i : G)⁻¹).toMonoidHom =
      Subgroup.normalizer (c.E.map (MulAut.conj (x i : G)⁻¹).toMonoidHom : Set G)
    exact Subgroup.map_normalizer_eq_of_bijective _
      (MulAut.conj (x i : G)⁻¹).bijective
  have hmap := Subgroup.map_mono (f := (MulAut.conj (x i : G)⁻¹).toMonoidHom) hM
  have hmap' : conjSubgroup D.M (x i : G) ≤
      conjSubgroup (Subgroup.normalizer (c.E : Set G)) (x i : G) := hmap
  rwa [hN] at hmap'

private theorem frame_S_le_normalizer_E {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (x : Fin 3 → ↥c.L) (i : Fin 3) :
    frameS c ≤ Subgroup.normalizer (frameE x i : Set G) :=
  (frame_S_le_conj_M x i).trans (frame_conj_M_le_normalizer x i)

theorem SL3Facts.frame_commutator_le {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) :
    ⁅frameE x i, frameE x i⁆ ≤ conjSubgroup D.Z (x i : G) := by
  have h : ⁅frameE x i, frameE x i⁆ = conjSubgroup ⁅c.E, c.E⁆ (x i : G) := by
    rw [frameE, conjSubgroup, conjSubgroup, ← Subgroup.map_commutator]
  rw [h]
  exact Subgroup.map_mono (f := (MulAut.conj (x i : G)⁻¹).toMonoidHom) F.hEE

theorem SL3Facts.frame_sq_mem_Z {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) {e : G}
    (he : e ∈ frameE x i) : e ^ 2 ∈ conjSubgroup D.Z (x i : G) := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp he
  refine Subgroup.mem_map.mpr ⟨a ^ 2, F.hEsq a ha, ?_⟩
  simp only [map_pow]

theorem SL3Facts.frame_Z_le_V {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup D.Z (x i : G) ≤ conjSubgroup c.V (x i : G) :=
  Subgroup.map_mono (f := (MulAut.conj (x i : G)⁻¹).toMonoidHom)
    (uc22p22v_le_conjClosure c.N D.Z)

theorem SL3Facts.frame_V_le_E {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup c.V (x i : G) ≤ frameE x i :=
  Subgroup.map_mono (f := (MulAut.conj (x i : G)⁻¹).toMonoidHom)
    (uc22p22v_le_conjClosure D.M c.V)

theorem SL3Facts.frame_E_le_K {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) :
    frameE x i ≤ conjSubgroup c.K (x i : G) :=
  Subgroup.map_mono (f := (MulAut.conj (x i : G)⁻¹).toMonoidHom)
    (Ctx2311.E_le_K c F.h1930 F.h4 F.h12 F.hN8)

theorem SL3Facts.frame_E_le_pCoreOf_K {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) :
    frameE x i ≤ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) := by
  have hpc : CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) =
      conjSubgroup (CFSG.Open.pCoreOf 2 c.K) (x i : G) := by
    rw [conjSubgroup, conjSubgroup, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  rw [hpc]
  exact Subgroup.map_mono (f := (MulAut.conj (x i : G)⁻¹).toMonoidHom)
    (le_pCoreOf_parts c F.h1930 F.h4 F.h12 F.hN8 F.hker).1

theorem SL3Facts.frame_pCoreOf_trivial {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) :
    ∀ u ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)),
      ∀ e ∈ frameE x i, ⁅u, e⁆ ∈ conjSubgroup D.Z (x i : G) := by
  have hpc : CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) =
      conjSubgroup (CFSG.Open.pCoreOf 2 c.K) (x i : G) := by
    rw [conjSubgroup, conjSubgroup, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  intro u hu e he
  rw [hpc] at hu
  obtain ⟨u0, hu0, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
  rw [← map_commutatorElement (MulAut.conj (x i : G)⁻¹).toMonoidHom u0 e0]
  exact Subgroup.mem_map_of_mem _ (F.commutator_mem_Z_of_pCoreOf hu0 he0)

theorem SL3Facts.frame_mem_Z_of_commutator_mem {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) {k : G}
    (hk : k ∈ conjSubgroup c.K (x i : G))
    (hkO : k ∉ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)))
    {r : ℕ} (hr : Odd r)
    (hkr : k ^ r ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)))
    {e : G} (he : e ∈ frameE x i)
    (hcomm : ⁅k, e⁆ ∈ conjSubgroup D.Z (x i : G)) :
    e ∈ conjSubgroup D.Z (x i : G) := by
  have hpc : CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) =
      conjSubgroup (CFSG.Open.pCoreOf 2 c.K) (x i : G) := by
    rw [conjSubgroup, conjSubgroup, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.mp hk
  obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
  have hkO' : k0 ∉ CFSG.Open.pCoreOf 2 c.K := by
    intro h
    exact hkO (hpc ▸ Subgroup.mem_map_of_mem _ h)
  have hkr' : k0 ^ r ∈ CFSG.Open.pCoreOf 2 c.K := by
    rw [hpc, ← map_pow] at hkr
    exact (Subgroup.mem_map_iff_mem (MulAut.conj (x i : G)⁻¹).injective).mp hkr
  have hcomm' : ⁅k0, e0⁆ ∈ D.Z := by
    rw [← map_commutatorElement (MulAut.conj (x i : G)⁻¹).toMonoidHom k0 e0] at hcomm
    exact (Subgroup.mem_map_iff_mem (MulAut.conj (x i : G)⁻¹).injective).mp hcomm
  exact Subgroup.mem_map_of_mem _
    ((F.mem_Z_of_commutator_mem hk0 hkO' hr hkr') e0 he0 hcomm')

theorem SL3Facts.frame_map_E_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) :
    ((frameE x i).subgroupOf c.L).map (c.phiL F.hV) =
      (CFSG.Open.pCoreOf 2 (frameKStar F)).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom := by
  have hsub : (frameE x i).subgroupOf c.L =
      (c.E.subgroupOf c.L).map (MulAut.conj ((x i : ↥c.L)⁻¹)).toMonoidHom := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_conjSubgroup_iff, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨⟨(x i : G) * (y : G) * (x i : G)⁻¹, ?_⟩, ?_, ?_⟩
      · exact c.L.mul_mem (c.L.mul_mem (x i).2 y.2) (c.L.inv_mem (x i).2)
      · exact Subgroup.mem_subgroupOf.mpr hy
      · apply Subtype.ext
        change (x i : G)⁻¹ * ((x i : G) * (y : G) * (x i : G)⁻¹) *
          ((x i : G)⁻¹)⁻¹ = (y : G)
        group
    · rintro ⟨a, ha, hay⟩
      have haE : (a : G) ∈ c.E := Subgroup.mem_subgroupOf.mp ha
      have hge : (x i : G) * (y : G) * (x i : G)⁻¹ = (a : G) := by
        have hval := congrArg (Subtype.val) hay
        change (x i : G)⁻¹ * (a : G) * ((x i : G)⁻¹)⁻¹ = (y : G) at hval
        rw [← hval]
        group
      rw [hge]
      exact haE
  rw [hsub, Subgroup.map_map_conj, frameKStar, F.map_E_eq]
  simp only [map_inv]

theorem SL3Facts.frame_mem_M_iff {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) (l : ↥c.L) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    ((l : G) ∈ conjSubgroup D.M (x i : G) ↔
      c.phiL F.hV l ∈ (MulAction.stabilizer ↥(c.H F.hV)
        ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
          Set (c.toCtx23L.W F.hV))).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom) := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  let l' : ↥c.L :=
    ⟨(x i : G) * (l : G) * (x i : G)⁻¹,
      c.L.mul_mem (c.L.mul_mem (x i).2 l.2) (c.L.inv_mem (x i).2)⟩
  have hmem : (l : G) ∈ conjSubgroup D.M (x i : G) ↔ (l' : G) ∈ D.M := by
    rw [mem_conjSubgroup_iff]
  rw [hmem, F.mem_M_iff l']
  constructor
  · intro h
    refine Subgroup.mem_map.mpr ⟨c.phiL F.hV l', h, ?_⟩
    have hval : c.phiL F.hV l' =
        c.phiL F.hV (x i) * c.phiL F.hV l * (c.phiL F.hV (x i))⁻¹ := by
      change c.phiL F.hV (x i * l * (x i)⁻¹) = _
      rw [map_mul, map_mul, map_inv]
    rw [hval]
    change (MulAut.conj (c.phiL F.hV (x i))⁻¹)
      (c.phiL F.hV (x i) * c.phiL F.hV l * (c.phiL F.hV (x i))⁻¹) = c.phiL F.hV l
    rw [MulAut.conj_apply]
    group
  · rintro ⟨p, hp, hpeq⟩
    have ha : c.phiL F.hV (x i) * c.phiL F.hV l * (c.phiL F.hV (x i))⁻¹ = p := by
      calc c.phiL F.hV (x i) * c.phiL F.hV l * (c.phiL F.hV (x i))⁻¹
          = c.phiL F.hV (x i) *
              ((MulEquiv.toMonoidHom (MulAut.conj (c.phiL F.hV (x i))⁻¹)) p) *
              (c.phiL F.hV (x i))⁻¹ := by rw [hpeq]
        _ = p := by
              change (MulAut.conj (c.phiL F.hV (x i)))
                ((MulAut.conj (c.phiL F.hV (x i))⁻¹) p) = p
              rw [MulAut.conj_apply, MulAut.conj_apply]
              group
    have hval : c.phiL F.hV l' =
        c.phiL F.hV (x i) * c.phiL F.hV l * (c.phiL F.hV (x i))⁻¹ := by
      change c.phiL F.hV (x i * l * (x i)⁻¹) = _
      rw [map_mul, map_mul, map_inv]
    rw [hval, ha]
    exact hp

theorem SL3Facts.frame_comap_stabilizer_le {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) {l : ↥c.L} :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    c.phiL F.hV l ∈ (MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom →
      (l : G) ∈ conjSubgroup D.M (x i : G) ∧
        (l : G) ∈ Subgroup.normalizer (frameE x i : Set G) := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  intro hl
  have hM := (F.frame_mem_M_iff x i l).mpr hl
  exact ⟨hM, frame_conj_M_le_normalizer x i hM⟩

private theorem frame_iSup_map_eq_top {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    ((⨆ i, (frameE x i).subgroupOf c.L).map (c.phiL F.hV)) = ⊤ := by
  rw [Subgroup.map_iSup]
  have hframe : (⨆ i, (CFSG.Open.pCoreOf 2 (frameKStar F)).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom) = ⊤ := by
    simpa [IsSL3Frame, frameKStar] using hx.2.1
  calc (⨆ i, ((frameE x i).subgroupOf c.L).map (c.phiL F.hV))
      = ⨆ i, (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom :=
        iSup_congr fun i => F.frame_map_E_eq x i
    _ = ⊤ := hframe

private theorem frame_iSup_sup_pCore_eq_top {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    (⨆ i, (frameE x i).subgroupOf c.L) ⊔ CFSG.pCore 2 ↥c.L = ⊤ := by
  have hmap := frame_iSup_map_eq_top F x hx
  have htop : (⊤ : Subgroup ↥c.L).map (c.phiL F.hV) = ⊤ :=
    Subgroup.map_top_of_surjective _ (c.phiL_surjective F.hV)
  have h := (Subgroup.map_eq_map_iff (f := c.phiL F.hV)
    (H := ⨆ i, (frameE x i).subgroupOf c.L) (K := ⊤)).mp (hmap.trans htop.symm)
  simpa [F.hker] using h

private theorem frame_iSup_normal {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    (⨆ i, (frameE x i).subgroupOf c.L).Normal := by
  have hsup := frame_iSup_sup_pCore_eq_top F x hx
  let J : Subgroup G := (⨆ i, (frameE x i).subgroupOf c.L).map c.L.subtype
  have htopmap : (⊤ : Subgroup ↥c.L).map c.L.subtype = c.L := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) c.L
  have hJeq : J = ⨆ i, frameE x i := by
    rw [show J = (⨆ i, (frameE x i).subgroupOf c.L).map c.L.subtype from rfl,
      Subgroup.map_iSup]
    exact iSup_congr fun i => by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (frame_E_le_L F x i)]
  have hJsup : J ⊔ frameS c = c.L := by
    have h := congrArg (Subgroup.map c.L.subtype) hsup
    simpa [J, frameS, CFSG.Open.pCoreOf, Subgroup.map_sup, htopmap] using h
  have hJleL : J ≤ c.L := by
    rw [hJeq]
    exact iSup_le fun i => frame_E_le_L F x i
  have hJn : c.L ≤ Subgroup.normalizer (J : Set G) := by
    have hJle : J ≤ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer
    have hSle : frameS c ≤ Subgroup.normalizer (J : Set G) := by
      have hSn : ∀ i, frameS c ≤ Subgroup.normalizer (frameE x i : Set G) :=
        fun i => frame_S_le_normalizer_E x i
      have h := (le_iInf hSn).trans
        (Subgroup.iInf_normalizer_le_normalizer_iSup (frameE x))
      rwa [← hJeq] at h
    rw [← hJsup]
    exact sup_le hJle hSle
  have hJL_eq_sub : (⨆ i, (frameE x i).subgroupOf c.L) = J.subgroupOf c.L := by
    apply Subgroup.map_subtype_inj.mp
    rw [show (⨆ i, (frameE x i).subgroupOf c.L).map c.L.subtype = J from rfl,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJleL]
  rw [hJL_eq_sub]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJleL).mpr hJn

private theorem frame_iSup_subgroupOf_eq_top {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    (⨆ i, (frameE x i).subgroupOf c.L) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let JL : Subgroup ↥c.L := ⨆ i, (frameE x i).subgroupOf c.L
  let SL : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  haveI : JL.Normal := frame_iSup_normal F x hx
  have hsup : JL ⊔ SL = ⊤ := frame_iSup_sup_pCore_eq_top F x hx
  have hSLmapq : SL.map (QuotientGroup.mk' JL) = ⊤ := by
    have htopq : (⊤ : Subgroup ↥c.L).map (QuotientGroup.mk' JL) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective JL)
    rw [← htopq, Subgroup.map_eq_map_iff, QuotientGroup.ker_mk', sup_comm]
    rw [show JL ⊔ SL = ⊤ from hsup]
    simp
  have hP : IsPGroup 2 (↥c.L ⧸ JL) := by
    have hmapP : IsPGroup 2 (SL.map (QuotientGroup.mk' JL)) :=
      IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L))
        (QuotientGroup.mk' JL)
    rw [hSLmapq] at hmapP
    exact IsPGroup.of_equiv hmapP Subgroup.topEquiv
  haveI : Group.IsPerfect ↥c.L := Subgroup.isPerfect_iff.mpr c.hL.1.2.1
  haveI : Group.IsPerfect (↥c.L ⧸ JL) := inferInstance
  have hNil : Group.IsNilpotent (↥c.L ⧸ JL) := IsPGroup.isNilpotent hP
  have hsub : Subsingleton (↥c.L ⧸ JL) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    haveI : Nontrivial (↥c.L ⧸ JL) := hnt
    exact Group.IsPerfect.not_isNilpotent (↥c.L ⧸ JL) hNil
  exact QuotientGroup.subgroup_eq_top_of_subsingleton JL hsub

theorem SL3Facts.iSup_frame_eq_L {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    (⨆ i, conjSubgroup c.E (x i : G)) = c.L := by
  have htop := frame_iSup_subgroupOf_eq_top F x hx
  have hmap : (⨆ i, (frameE x i).subgroupOf c.L).map c.L.subtype = ⨆ i, frameE x i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (frame_E_le_L F x i)]
  have htopmap : (⊤ : Subgroup ↥c.L).map c.L.subtype = c.L := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) c.L
  calc (⨆ i, conjSubgroup c.E (x i : G))
      = (⨆ i, (frameE x i).subgroupOf c.L).map c.L.subtype := hmap.symm
    _ = (⊤ : Subgroup ↥c.L).map c.L.subtype := by rw [htop]
    _ = c.L := htopmap

private theorem frame_commutator_E_pCoreOf_le {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) :
    ⁅frameE x i, frameS c⁆ ≤ frameE x i ⊓ frameS c := by
  refine le_inf ?_ ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
      ((frame_S_le_conj_M x i).trans (frame_conj_M_le_normalizer x i))
  · exact (Subgroup.le_normalizer_iff_commutator_le_right).mp
      ((frame_E_le_L F x i).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) c.L))

private theorem frame_E_le_normalizer_S0 {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L) (i : Fin 3) :
    frameE x i ≤ Subgroup.normalizer (frameS0 x : Set G) := by
  have hmaps : ∀ g ∈ frameE x i,
      (frameS0 x).map (MulAut.conj g).toMonoidHom ≤ frameS0 x := by
    intro g hg
    rw [show frameS0 x = ⨆ j, frameE x j ⊓ frameS c from rfl, Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rintro z ⟨y, hy, rfl⟩
    have hcomm₁ : ⁅g, y⁆ ∈ frameE x i ⊓ frameS c :=
      (Subgroup.commutator_le.mp (frame_commutator_E_pCoreOf_le F x i)) g hg y hy.2
    have hcomm : ⁅g, y⁆ ∈ frameS0 x := Subgroup.mem_iSup_of_mem i hcomm₁
    have hyS0 : y ∈ frameS0 x := Subgroup.mem_iSup_of_mem j hy
    have hid : (MulAut.conj g) y = ⁅g, y⁆ * y := by
      rw [MulAut.conj_apply, commutatorElement_def]
      group
    change (MulAut.conj g) y ∈ frameS0 x
    rw [hid]
    exact (frameS0 x).mul_mem hcomm hyS0
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hmaps g hg (Subgroup.mem_map_of_mem _ hy)
  · intro hy
    have hmem := hmaps g⁻¹ ((frameE x i).inv_mem hg) (Subgroup.mem_map_of_mem _ hy)
    change (MulAut.conj g⁻¹) (g * y * g⁻¹) ∈ frameS0 x at hmem
    rw [MulAut.conj_apply, inv_inv] at hmem
    have hEq : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [hEq] at hmem

private theorem frame_commutator_mul_mem {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} {x : Fin 3 → ↥c.L}
    (hLnorm : c.L ≤ Subgroup.normalizer (frameS0 x : Set G))
    {a b : G} (haL : a ∈ c.L) (hbL : b ∈ c.L)
    (ha : ∀ s ∈ frameS c, ⁅a, s⁆ ∈ frameS0 x)
    (hb : ∀ s ∈ frameS c, ⁅b, s⁆ ∈ frameS0 x) :
    ∀ s ∈ frameS c, ⁅a * b, s⁆ ∈ frameS0 x := by
  intro s hs
  have hconj : a * ⁅b, s⁆ * a⁻¹ ∈ frameS0 x :=
    (Subgroup.mem_normalizer_iff.mp (hLnorm haL) ⁅b, s⁆).mp (hb s hs)
  have hid : ⁅a * b, s⁆ = a * ⁅b, s⁆ * a⁻¹ * ⁅a, s⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact (frameS0 x).mul_mem hconj (ha s hs)

private theorem frame_commutator_inv_mem {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} {x : Fin 3 → ↥c.L}
    (hLnorm : c.L ≤ Subgroup.normalizer (frameS0 x : Set G))
    {a : G} (haL : a ∈ c.L)
    (ha : ∀ s ∈ frameS c, ⁅a, s⁆ ∈ frameS0 x) :
    ∀ s ∈ frameS c, ⁅a⁻¹, s⁆ ∈ frameS0 x := by
  intro s hs
  have hconj : a⁻¹ * ⁅a, s⁆ * a ∈ frameS0 x := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hLnorm (c.L.inv_mem haL)) ⁅a, s⁆).mp (ha s hs)
  have hid : ⁅a⁻¹, s⁆ = (a⁻¹ * ⁅a, s⁆ * a)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact (frameS0 x).inv_mem hconj

private theorem frame_commutator_L_pCoreOf_le {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    ⁅c.L, frameS c⁆ ≤ frameS0 x := by
  have hJ := F.iSup_frame_eq_L x hx
  have hLnorm : c.L ≤ Subgroup.normalizer (frameS0 x : Set G) := by
    rw [← hJ]
    exact iSup_le fun i => frame_E_le_normalizer_S0 F x i
  let K : Subgroup G :=
    { carrier := {l : G | l ∈ c.L ∧ ∀ s ∈ frameS c, ⁅l, s⁆ ∈ frameS0 x}
      one_mem' := ⟨c.L.one_mem, by
        intro s _
        simp [commutatorElement_def]⟩
      mul_mem' := fun ha hb =>
        ⟨c.L.mul_mem ha.1 hb.1, frame_commutator_mul_mem hLnorm ha.1 hb.1 ha.2 hb.2⟩
      inv_mem' := fun ha =>
        ⟨c.L.inv_mem ha.1, frame_commutator_inv_mem hLnorm ha.1 ha.2⟩ }
  have hE_le_K : ∀ i, frameE x i ≤ K := by
    intro i g hg
    refine ⟨frame_E_le_L F x i hg, ?_⟩
    intro s hs
    exact Subgroup.mem_iSup_of_mem i
      ((Subgroup.commutator_le.mp (frame_commutator_E_pCoreOf_le F x i)) g hg s hs)
  have hL_le_K : c.L ≤ K := by
    rw [← hJ]
    exact iSup_le hE_le_K
  exact Subgroup.commutator_le.mpr fun l hl s hs => (hL_le_K hl).2 s hs

private theorem frame_S0_subgroupOf_normal {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    ((frameS0 x).subgroupOf c.L).Normal := by
  have hJ := F.iSup_frame_eq_L x hx
  have hS0_le_L : frameS0 x ≤ c.L :=
    (iSup_le fun i => inf_le_right).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hS0_le_L).mpr ?_
  rw [← hJ]
  exact iSup_le fun i => frame_E_le_normalizer_S0 F x i

private theorem frame_commutator_top_pCore_le {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    ⁅(⊤ : Subgroup ↥c.L), CFSG.pCore 2 ↥c.L⁆ ≤
      (frameS0 x).subgroupOf c.L := by
  rw [Subgroup.commutator_le]
  intro l _ s hs
  rw [Subgroup.mem_subgroupOf]
  have hsS : (s : G) ∈ frameS c := Subgroup.mem_map_of_mem _ hs
  have hmem : ⁅(l : G), (s : G)⁆ ∈ frameS0 x :=
    (Subgroup.commutator_le.mp (frame_commutator_L_pCoreOf_le F x hx)) (l : G) l.2
      (s : G) hsS
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

private theorem frame_pCore_center_quotient {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    [hS0L : ((frameS0 x).subgroupOf c.L).Normal] :
    ((CFSG.pCore 2 ↥c.L).map
      (QuotientGroup.mk' ((frameS0 x).subgroupOf c.L))) ≤
      Subgroup.center (↥c.L ⧸ (frameS0 x).subgroupOf c.L) := by
  let S0L : Subgroup ↥c.L := (frameS0 x).subgroupOf c.L
  let SL : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let q : ↥c.L →* ↥c.L ⧸ S0L := QuotientGroup.mk' S0L
  let Z : Subgroup (↥c.L ⧸ S0L) := SL.map q
  haveI : S0L.Normal := hS0L
  have hLS := frame_commutator_top_pCore_le F x hx
  rw [← Subgroup.commutator_top_left_eq_bot_iff_le_center]
  have hmap := Subgroup.map_mono (f := q) hLS
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective S0L)] at hmap
  have hq : S0L.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [hq] at hmap
  simpa [Z] using hmap

private theorem frame_pCore_shape_quotient {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    [hS0L : ((frameS0 x).subgroupOf c.L).Normal] :
    PartTwo.IsSLn ((↥c.L ⧸ (frameS0 x).subgroupOf c.L) ⧸
      ((CFSG.pCore 2 ↥c.L).map
        (QuotientGroup.mk' ((frameS0 x).subgroupOf c.L))))
      3 (CFSG.Open.pRank 2 D.Z) := by
  let S0L : Subgroup ↥c.L := (frameS0 x).subgroupOf c.L
  let SL : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let Z : Subgroup (↥c.L ⧸ S0L) := SL.map (QuotientGroup.mk' S0L)
  haveI : S0L.Normal := hS0L
  have hS0_le_S : frameS0 x ≤ frameS c := iSup_le fun i => inf_le_right
  have hS0L_le_SL : S0L ≤ SL := by
    intro l hl
    have hlS : (l : G) ∈ frameS c := hS0_le_S (Subgroup.mem_subgroupOf.mp hl)
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp hlS
    have hls : l = s := Subtype.ext hse.symm
    rw [hls]
    exact hs
  have e1 : (↥c.L ⧸ S0L) ⧸ Z ≃* ↥c.L ⧸ SL :=
    QuotientGroup.quotientQuotientEquivQuotient (N := S0L) (M := SL) hS0L_le_SL
  have e2 : ↥c.L ⧸ SL ≃* ↥(c.H F.hV) :=
    QuotientGroup.liftEquiv (φ := c.phiL F.hV) (N := SL)
      (c.phiL_surjective F.hV) F.hker.symm
  simpa [S0L, SL, Z] using
    (PartTwo.IsSLn.of_mulEquiv (e1.trans e2).symm F.hSL)

private theorem frame_pCore_le_S0 {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    CFSG.pCore 2 ↥c.L ≤ (frameS0 x).subgroupOf c.L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hS0Lnorm : ((frameS0 x).subgroupOf c.L).Normal :=
    frame_S0_subgroupOf_normal F x hx
  let S0L : Subgroup ↥c.L := (frameS0 x).subgroupOf c.L
  let SL : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let q : ↥c.L →* ↥c.L ⧸ S0L := QuotientGroup.mk' S0L
  let Z : Subgroup (↥c.L ⧸ S0L) := SL.map q
  haveI : S0L.Normal := hS0Lnorm
  have hcenter : Z ≤ Subgroup.center (↥c.L ⧸ S0L) :=
    frame_pCore_center_quotient F x hx
  have hshape : PartTwo.IsSLn ((↥c.L ⧸ S0L) ⧸ Z) 3 (CFSG.Open.pRank 2 D.Z) :=
    frame_pCore_shape_quotient F x hx
  have hXperf : ⁅(⊤ : Subgroup (↥c.L ⧸ S0L)),
      (⊤ : Subgroup (↥c.L ⧸ S0L))⁆ = ⊤ := by
    haveI : Group.IsPerfect ↥c.L := Subgroup.isPerfect_iff.mpr c.hL.1.2.1
    haveI : Group.IsPerfect (↥c.L ⧸ S0L) := inferInstance
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  haveI : Z.Normal := Subgroup.normal_of_le_center hcenter
  have hZbot : Z = ⊥ := kSchurSL3_holds (↥c.L ⧸ S0L) (CFSG.Open.pRank 2 D.Z)
    hXperf Z hcenter hshape F.h3
  have hmapbot : SL.map q = ⊥ := hZbot
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmapbot
  exact hmapbot

theorem SL3Facts.pCoreOf_eq_iSup_frame {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    CFSG.Open.pCoreOf 2 c.L =
      ⨆ i, conjSubgroup c.E (x i : G) ⊓ CFSG.Open.pCoreOf 2 c.L := by
  have hS0_le_S : frameS0 x ≤ frameS c := iSup_le fun i => inf_le_right
  have hSL_le_S0L := frame_pCore_le_S0 F x hx
  have hS_le_S0 : frameS c ≤ frameS0 x := by
    intro s hs
    obtain ⟨l, hl, hls⟩ := Subgroup.mem_map.mp hs
    have hls0 : (l : G) ∈ frameS0 x :=
      Subgroup.mem_subgroupOf.mp (hSL_le_S0L hl)
    rw [← hls]
    exact hls0
  exact le_antisymm hS_le_S0 hS0_le_S

end Ctx2311

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
