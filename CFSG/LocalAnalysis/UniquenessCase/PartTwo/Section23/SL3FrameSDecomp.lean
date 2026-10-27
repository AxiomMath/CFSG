module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3FrameGen
public import CFSG.Quasithin.Background.G25Comm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G}

private abbrev frameInter {c : Ctx2311 D Ch} (x : Fin 3 → ↥c.L) (i j : Fin 3) : Subgroup G :=
  frameE x i ⊓ frameE x j

private theorem frameAux_Ki_le_L {c : Ctx2311 D Ch} (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup c.K (x i : G) ≤ c.L := by
  rw [conjSubgroup]
  have hL : c.L.map (MulAut.conj (x i : G)⁻¹).toMonoidHom = c.L := by
    simpa [conjSubgroup] using
      (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr
        (Subgroup.le_normalizer (x i).2))
  exact (Subgroup.map_mono (Ctx2311.K_le_L c)).trans (le_of_eq hL)

private theorem frameAux_V_eq {c : Ctx2311 D Ch} (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup c.V (x i : G) = c.V := by
  refine CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr ?_
  exact Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L (Subgroup.mem_sup_left (x i).2)

private theorem frameAux_Z_le_E {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup D.Z (x i : G) ≤ frameE x i := by
  have hZV : conjSubgroup D.Z (x i : G) ≤ c.V := by
    simpa [frameAux_V_eq x i] using SL3Facts.frame_Z_le_V x i
  exact hZV.trans (by simpa [frameAux_V_eq x i] using SL3Facts.frame_V_le_E x i)

private theorem frameAux_V_le_inter {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i j : Fin 3) :
    c.V ≤ frameE x i ⊓ frameE x j := by
  refine le_inf ?_ ?_
  · simpa [frameAux_V_eq x i] using SL3Facts.frame_V_le_E x i
  · simpa [frameAux_V_eq x j] using SL3Facts.frame_V_le_E x j

private theorem frameAux_A_le_pCoreOf {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j : Fin 3) (hij : i ≠ j) :
    frameE x i ⊓ frameE x j ≤ frameS c := by
  intro a ha
  have hai : a ∈ frameE x i := ha.1
  have haj : a ∈ frameE x j := ha.2
  have haiL : a ∈ c.L := (F.frame_E_le_K x i).trans (frameAux_Ki_le_L x i) hai
  let l : ↥c.L := ⟨a, haiL⟩
  have hi : c.phiL F.hV l ∈ ((frameE x i).subgroupOf c.L).map (c.phiL F.hV) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hai)
  have hj : c.phiL F.hV l ∈ ((frameE x j).subgroupOf c.L).map (c.phiL F.hV) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haj)
  rw [F.frame_map_E_eq x i] at hi
  rw [F.frame_map_E_eq x j] at hj
  have hbot := (Subgroup.mem_inf.mpr ⟨hi, hj⟩ : c.phiL F.hV l ∈
    (CFSG.Open.pCoreOf 2 (frameKStar F)).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ⊓
      (CFSG.Open.pCoreOf 2 (frameKStar F)).map
        (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom)
  rw [hx.2.2.1 i j hij] at hbot
  have hphi : c.phiL F.hV l = 1 := Subgroup.mem_bot.mp hbot
  rw [show frameS c = (CFSG.pCore 2 ↥c.L).map c.L.subtype from rfl, Subgroup.mem_map]
  refine ⟨l, ?_, rfl⟩
  rw [← F.hker, MonoidHom.mem_ker]
  exact hphi

private theorem frameAux_S_le_normalizer_E {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) :
    frameS c ≤ Subgroup.normalizer (frameE x i : Set G) := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  intro s hs
  have hsL : s ∈ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L hs
  let l : ↥c.L := ⟨s, hsL⟩
  have hphi : c.phiL F.hV l = 1 := by
    have hker : l ∈ (c.phiL F.hV).ker := by
      rw [F.hker]
      obtain ⟨y, hy, hys⟩ :=
        Subgroup.mem_map.mp (show s ∈ (CFSG.pCore 2 ↥c.L).map c.L.subtype from hs)
      have hly : l = y := Subtype.ext hys.symm
      rwa [hly]
    simpa [MonoidHom.mem_ker] using hker
  have hstab : c.phiL F.hV l ∈ (MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom := by
    rw [hphi]
    exact Subgroup.mem_map.mpr ⟨1, Subgroup.one_mem _, map_one _⟩
  exact (F.frame_comap_stabilizer_le x i hstab).2

private theorem frameAux_S_le_normalizer_sup {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i j k : Fin 3) :
    frameS c ≤ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) := by
  have hij : frameS c ≤
      Subgroup.normalizer ((frameE x i ⊓ frameE x j : Subgroup G) : Set G) :=
    (le_inf (frameAux_S_le_normalizer_E F x i) (frameAux_S_le_normalizer_E F x j)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := frameE x i) (K := frameE x j))
  have hik : frameS c ≤
      Subgroup.normalizer ((frameE x i ⊓ frameE x k : Subgroup G) : Set G) :=
    (le_inf (frameAux_S_le_normalizer_E F x i) (frameAux_S_le_normalizer_E F x k)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := frameE x i) (K := frameE x k))
  exact (le_inf hij hik).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (frameE x i ⊓ frameE x j)
      (frameE x i ⊓ frameE x k))

private theorem frameAux_commutator_inter_le {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) {m i : Fin 3} (hmi : m ≠ i) :
    ⁅frameE x m ⊓ frameS c, frameE x i ⊓ frameS c⁆ ≤ frameE x i ⊓ frameE x m := by
  refine Subgroup.commutator_le.mpr ?_
  intro g hg y hy
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hconj : g * y * g⁻¹ ∈ frameE x i :=
      (Subgroup.mem_normalizer_iff.mp (frameAux_S_le_normalizer_E F x i hg.2) y).mp hy.1
    show g * y * g⁻¹ * y⁻¹ ∈ frameE x i
    exact (frameE x i).mul_mem hconj ((frameE x i).inv_mem hy.1)
  · have hconj : y * g⁻¹ * y⁻¹ ∈ frameE x m :=
      (Subgroup.mem_normalizer_iff.mp (frameAux_S_le_normalizer_E F x m hy.2) g⁻¹).mp
        ((frameE x m).inv_mem hg.1)
    show g * y * g⁻¹ * y⁻¹ ∈ frameE x m
    have heq : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
    rw [heq]
    exact (frameE x m).mul_mem hg.1 hconj

private theorem frameAux_commutator_pCoreOf_le_sup {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅frameS c, frameE x i ⊓ frameS c⁆ ≤
      ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) := by
  let Dsup : Subgroup G := ((frameInter x i j ⊔ frameInter x i k) : Subgroup G)
  have hN : ∀ m, frameE x m ⊓ frameS c ≤
      Subgroup.normalizer (Dsup : Set G) := fun m =>
    inf_le_right.trans (frameAux_S_le_normalizer_sup F x i j k)
  have hA : ∀ m, ⁅frameE x m ⊓ frameS c, frameE x i ⊓ frameS c⁆ ≤ Dsup := by
    intro m
    have hmem : m = i ∨ m = j ∨ m = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all
    rcases hmem with hmi | hmj | hmk
    · subst m
      have hZV : conjSubgroup D.Z (x i : G) ≤ c.V := by
        simpa [frameAux_V_eq x i] using SL3Facts.frame_Z_le_V x i
      have h1 : ⁅frameE x i ⊓ frameS c, frameE x i ⊓ frameS c⁆ ≤
          ⁅frameE x i, frameE x i⁆ := Subgroup.commutator_mono inf_le_left inf_le_left
      exact (h1.trans (F.frame_commutator_le x i)).trans
        ((hZV.trans (frameAux_V_le_inter F x i j)).trans le_sup_left)
    · subst m
      exact (frameAux_commutator_inter_le F x hij.symm).trans le_sup_left
    · subst m
      exact (frameAux_commutator_inter_le F x hik.symm).trans le_sup_right
  have h := CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
    (A := fun m => frameE x m ⊓ frameS c) (Y := frameE x i ⊓ frameS c) (N := Dsup) hN hA
  change ⁅CFSG.Open.pCoreOf 2 c.L, frameE x i ⊓ CFSG.Open.pCoreOf 2 c.L⁆ ≤ Dsup
  nth_rw 1 [F.pCoreOf_eq_iSup_frame x hx]
  exact h

private theorem frameAux_Ki_le_normalizer {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup c.K (x i : G) ≤
      Subgroup.normalizer (frameE x i : Set G) ⊓
        Subgroup.normalizer (conjSubgroup D.Z (x i : G) : Set G) := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  refine le_inf ?_ ?_
  · have hK : c.K ≤ Subgroup.normalizer (c.E : Set G) :=
      hKM.trans (uc22p22v_le_normalizer_conjClosure D.M c.V)
    have hN : conjSubgroup (Subgroup.normalizer (c.E : Set G)) (x i : G) =
        Subgroup.normalizer (frameE x i : Set G) := by
      change (Subgroup.normalizer (c.E : Set G)).map
          (MulAut.conj (x i : G)⁻¹).toMonoidHom =
        Subgroup.normalizer (c.E.map (MulAut.conj (x i : G)⁻¹).toMonoidHom : Set G)
      exact Subgroup.map_normalizer_eq_of_bijective _
        (MulAut.conj (x i : G)⁻¹).bijective
    exact hN ▸ Subgroup.map_mono hK
  · have h4 := F.h4 F.h1930 c.toCtx23L
    have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
      simpa only [h4.1] using h4.2.2
    have hK : c.K ≤ Subgroup.normalizer (D.Z : Set G) := hKM.trans hMZ
    have hN : conjSubgroup (Subgroup.normalizer (D.Z : Set G)) (x i : G) =
        Subgroup.normalizer (conjSubgroup D.Z (x i : G) : Set G) := by
      change (Subgroup.normalizer (D.Z : Set G)).map
          (MulAut.conj (x i : G)⁻¹).toMonoidHom =
        Subgroup.normalizer (D.Z.map (MulAut.conj (x i : G)⁻¹).toMonoidHom : Set G)
      exact Subgroup.map_normalizer_eq_of_bijective _
        (MulAut.conj (x i : G)⁻¹).bijective
    exact hN ▸ Subgroup.map_mono hK

private theorem frameAux_exists_lift {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) {u : ↥(c.H F.hV)}
    (hu : u ∈ (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom) :
    ∃ (k : G) (hkL : k ∈ c.L), k ∈ conjSubgroup c.K (x i : G) ∧
      c.phiL F.hV ⟨k, hkL⟩ = u := by
  obtain ⟨k0, hk0, hk0u⟩ := Subgroup.mem_map.mp hu
  obtain ⟨l, hl, hl0⟩ := Subgroup.mem_map.mp hk0
  let k : G := (x i : G)⁻¹ * (l : G) * (x i : G)
  have hkL : k ∈ c.L :=
    c.L.mul_mem (c.L.mul_mem (c.L.inv_mem (x i).2) l.2) (x i).2
  refine ⟨k, hkL, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨(l : G), Subgroup.mem_subgroupOf.mp hl,
      by simp [k, MulAut.conj_apply]⟩
  · have hsub : (⟨k, hkL⟩ : ↥c.L) =
        (⟨(x i : G)⁻¹, c.L.inv_mem (x i).2⟩ : ↥c.L) * l *
          ⟨(x i : G), (x i).2⟩ := by
      apply Subtype.ext
      simp [k, mul_assoc]
    have hxsub : (⟨(x i : G)⁻¹, c.L.inv_mem (x i).2⟩ : ↥c.L) =
        (⟨(x i : G), (x i).2⟩ : ↥c.L)⁻¹ := rfl
    rw [hsub, map_mul, map_mul, hxsub, map_inv, hl0]
    simpa [MulAut.conj_apply] using hk0u

private theorem frameAux_Kstar_le_stabilizer {c : Ctx2311 D Ch} (F : c.SL3Facts) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    frameKStar F ≤ MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV)) := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  intro h hh
  obtain ⟨l, hl, hlh⟩ := Subgroup.mem_map.mp hh
  have hlK : (l : G) ∈ c.K := Subgroup.mem_subgroupOf.mp hl
  have hlM : (l : G) ∈ D.M :=
    ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left) hlK
  have hmem := (F.mem_M_iff l).mp hlM
  simpa [hlh] using hmem

private theorem frameAux_map_Kstar_le_stabilizer {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) {u : ↥(c.H F.hV)}
    (hu : u ∈ (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom) :
    u ∈ (MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom :=
  Subgroup.map_mono (f := (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom)
    (frameAux_Kstar_le_stabilizer F) hu

private theorem frameAux_exists_decomp {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    {i j : Fin 3} (hij : i ≠ j) {u : ↥(c.H F.hV)}
    (huKstar : u ∈ (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom)
    (huU : u ∈ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
      (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom) :
    ∃ (uK g s : G) (huKL : uK ∈ c.L),
      uK ∈ conjSubgroup c.K (x i : G) ∧ c.phiL F.hV ⟨uK, huKL⟩ = u ∧
      g ∈ frameE x j ∧ g ∈ Subgroup.normalizer (frameE x i : Set G) ∧
      s ∈ frameS c ∧ uK = g * s := by
  obtain ⟨uK, huKL, huKi, huKphi⟩ := frameAux_exists_lift F x i huKstar
  have huU' : u ∈ ((frameE x j).subgroupOf c.L).map (c.phiL F.hV) := by
    rw [F.frame_map_E_eq x j]
    exact huU
  have hmem : c.phiL F.hV ⟨uK, huKL⟩ ∈ ((frameE x j).subgroupOf c.L).map (c.phiL F.hV) := by
    rw [huKphi]
    exact huU'
  obtain ⟨gL, hgL, hgLphi⟩ := Subgroup.mem_map.mp hmem
  have hgE : (gL : G) ∈ frameE x j := Subgroup.mem_subgroupOf.mp hgL
  have huP := frameAux_map_Kstar_le_stabilizer F x i huKstar
  have hgP : c.phiL F.hV gL ∈ (MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom := by
    rw [hgLphi, huKphi]
    exact huP
  obtain ⟨-, hgN⟩ := (F.frame_comap_stabilizer_le x i hgP : (gL : G) ∈
    conjSubgroup D.M (x i : G) ∧ (gL : G) ∈ Subgroup.normalizer (frameE x i : Set G))
  let s : G := (gL : G)⁻¹ * uK
  have hsL : s ∈ c.L := c.L.mul_mem (c.L.inv_mem gL.2) huKL
  have hsphi : c.phiL F.hV ⟨s, hsL⟩ = 1 := by
    have hsub : (⟨s, hsL⟩ : ↥c.L) = gL⁻¹ * ⟨uK, huKL⟩ := Subtype.ext (by simp [s])
    rw [hsub, map_mul, map_inv, hgLphi, huKphi]
    simp
  have hsS : s ∈ frameS c := by
    rw [show frameS c = (CFSG.pCore 2 ↥c.L).map c.L.subtype from rfl, Subgroup.mem_map]
    refine ⟨⟨s, hsL⟩, ?_, rfl⟩
    rw [← F.hker, MonoidHom.mem_ker]
    exact hsphi
  refine ⟨uK, (gL : G), s, huKL, huKi, huKphi, hgE, hgN, hsS, ?_⟩
  show uK = (gL : G) * s
  simp [s]

private theorem frameAux_mem_pCoreOf_of_phi_eq_one {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) {k : G} (hkL : k ∈ c.L)
    (hk : k ∈ conjSubgroup c.K (x i : G))
    (hphi : c.phiL F.hV ⟨k, hkL⟩ = 1) :
    k ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkS : k ∈ frameS c := by
    rw [show frameS c = (CFSG.pCore 2 ↥c.L).map c.L.subtype from rfl, Subgroup.mem_map]
    refine ⟨⟨k, hkL⟩, ?_, rfl⟩
    rw [← F.hker, MonoidHom.mem_ker]
    exact hphi
  let P : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  let N2 : Subgroup G := conjSubgroup c.K (x i : G) ⊓ P
  have hN2p : IsPGroup 2 N2 :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le
      (inf_le_right : N2 ≤ P)
  have hKiS : conjSubgroup c.K (x i : G) ≤
      Subgroup.normalizer (frameS c : Set G) :=
    (frameAux_Ki_le_L x i).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) c.L)
  have hnorm : conjSubgroup c.K (x i : G) ≤
      Subgroup.normalizer ((conjSubgroup c.K (x i : G) ⊓ frameS c : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer) hKiS).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := conjSubgroup c.K (x i : G))
        (K := frameS c))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hN2p
    ⟨hk, hkS⟩

private theorem frameAux_phi_pCoreOf_mem {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) {k : G} (hkL : k ∈ c.L)
    (hk : k ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G))) :
    c.phiL F.hV ⟨k, hkL⟩ ∈
      (CFSG.Open.pCoreOf 2 (frameKStar F)).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom := by
  have hpc : CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) =
      (CFSG.Open.pCoreOf 2 c.K).map (MulAut.conj (x i : G)⁻¹).toMonoidHom := by
    rw [conjSubgroup, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  rw [hpc] at hk
  obtain ⟨k0, hk0, hk0k⟩ := Subgroup.mem_map.mp hk
  have hk0K : k0 ∈ c.K := CFSG.LieType.BorelTits.pCoreOf_le 2 c.K hk0
  have hk0L : k0 ∈ c.L := Ctx2311.K_le_L c hk0K
  have hphiK0 : c.phiL F.hV ⟨k0, hk0L⟩ ∈ CFSG.Open.pCoreOf 2 (frameKStar F) := by
    have h := Ctx2311.map_pCoreOf_phiL_le c F.hV
      (Subgroup.mem_map_of_mem
        ((c.phiL F.hV).comp (Subgroup.inclusion c.K_le_L))
        (show (⟨k0, hk0K⟩ : ↥c.K) ∈
            (CFSG.Open.pCoreOf 2 c.K).subgroupOf c.K from
          Subgroup.mem_subgroupOf.mpr hk0))
    have harg : ((Subgroup.inclusion c.K_le_L) ⟨k0, hk0K⟩ : ↥c.L) = ⟨k0, hk0L⟩ :=
      Subtype.ext rfl
    change c.phiL F.hV ((Subgroup.inclusion c.K_le_L) ⟨k0, hk0K⟩) ∈
      CFSG.Open.pCoreOf 2 (frameKStar F) at h
    rw [harg] at h
    exact h
  refine Subgroup.mem_map.mpr ⟨c.phiL F.hV ⟨k0, hk0L⟩, hphiK0, ?_⟩
  have hk_eq : k = (x i : G)⁻¹ * k0 * (x i : G) := by
    simpa [MulAut.conj_apply] using hk0k.symm
  have hsub : (⟨k, hkL⟩ : ↥c.L) =
      (⟨(x i : G)⁻¹, c.L.inv_mem (x i).2⟩ : ↥c.L) * ⟨k0, hk0L⟩ *
        ⟨(x i : G), (x i).2⟩ := by
    apply Subtype.ext
    simpa [hk_eq, mul_assoc]
  have hval : c.phiL F.hV ⟨k, hkL⟩ =
      (MulAut.conj (c.phiL F.hV (x i))⁻¹) (c.phiL F.hV ⟨k0, hk0L⟩) := by
    have hxinv : c.phiL F.hV
        (⟨(x i : G)⁻¹, c.L.inv_mem (x i).2⟩ : ↥c.L) =
        (c.phiL F.hV (x i))⁻¹ := by
      rw [show (⟨(x i : G)⁻¹, c.L.inv_mem (x i).2⟩ : ↥c.L) =
        (⟨(x i : G), (x i).2⟩ : ↥c.L)⁻¹ from rfl, map_inv]
    rw [hsub, map_mul, map_mul, hxinv]
    simp [MulAut.conj_apply]
  exact hval.symm

private theorem frameAux_point_congruence {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) {uK vK : G}
    (huKi : uK ∈ conjSubgroup c.K (x i : G))
    (hvKi : vK ∈ conjSubgroup c.K (x i : G))
    (hu2 : uK ^ 2 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)))
    (hv2 : vK ^ 2 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)))
    (huv3 : (uK * vK) ^ 3 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)))
    (huvO : uK * vK ∉ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G))) :
    ∀ y ∈ frameE x i,
      y⁻¹ * (⁅uK, ⁅vK, y⁆⁆ * ⁅vK, ⁅uK, y⁆⁆) ∈ conjSubgroup D.Z (x i : G) := by
  have hnorm := frameAux_Ki_le_normalizer F x i
  have hZE : conjSubgroup D.Z (x i : G) ≤ frameE x i := frameAux_Z_le_E F x i
  have hu : uK ∈ Subgroup.normalizer (frameE x i : Set G) ⊓
      Subgroup.normalizer (conjSubgroup D.Z (x i : G) : Set G) :=
    ⟨(hnorm huKi).1, (hnorm huKi).2⟩
  have hv : vK ∈ Subgroup.normalizer (frameE x i : Set G) ⊓
      Subgroup.normalizer (conjSubgroup D.Z (x i : G) : Set G) :=
    ⟨(hnorm hvKi).1, (hnorm hvKi).2⟩
  have hu2' : ∀ y ∈ frameE x i,
      ⁅uK ^ 2, y⁆ ∈ conjSubgroup D.Z (x i : G) := fun y hy =>
    F.frame_pCoreOf_trivial x i (uK ^ 2) hu2 y hy
  have hv2' : ∀ y ∈ frameE x i,
      ⁅vK ^ 2, y⁆ ∈ conjSubgroup D.Z (x i : G) := fun y hy =>
    F.frame_pCoreOf_trivial x i (vK ^ 2) hv2 y hy
  have hw3 : ∀ y ∈ frameE x i,
      ⁅(uK * vK) ^ 3, y⁆ ∈ conjSubgroup D.Z (x i : G) := fun y hy =>
    F.frame_pCoreOf_trivial x i ((uK * vK) ^ 3) huv3 y hy
  have hfree : ∀ y ∈ frameE x i,
      ⁅uK * vK, y⁆ ∈ conjSubgroup D.Z (x i : G) → y ∈ conjSubgroup D.Z (x i : G) := by
    intro y hy hcomm
    exact F.frame_mem_Z_of_commutator_mem x i ((conjSubgroup c.K (x i : G)).mul_mem huKi hvKi)
      huvO (r := 3) (by norm_num) huv3 hy hcomm
  exact CFSG.inv_mul_mem_of_s3 hZE (F.frame_commutator_le x i)
    (fun y hy => F.frame_sq_mem_Z x i hy) hu hv hu2' hv2' hw3 hfree

private theorem frameAux_map_conj_le {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j k : Fin 3) (hik : i ≠ k) {A B : Subgroup G}
    (hAeq : A = frameInter x i j) (hBeq : B = frameInter x i k) {g : G}
    (hgn : g ∈ Subgroup.normalizer (frameE x i : Set G))
    (hgj : g ∈ frameE x j) :
    (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · have hgA : g ∈ Subgroup.normalizer ((frameInter x i j : Subgroup G) : Set G) :=
      (Subgroup.inf_normalizer_le_normalizer_inf (H := frameE x i) (K := frameE x j))
        ⟨hgn, Subgroup.le_normalizer hgj⟩
    have hmapA : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [hAeq]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgA
    rw [hmapA]
    exact le_sup_left
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hbI : b ∈ frameInter x i k := by simpa only [hBeq] using hb
    have hbS : b ∈ frameS c := (frameAux_A_le_pCoreOf F x hx i k hik) hbI
    have hbEi : b ∈ frameE x i := hbI.1
    have hcommE : ⁅g, b⁆ ∈ frameE x i := by
      have hc : g * b * g⁻¹ ∈ frameE x i :=
        (Subgroup.mem_normalizer_iff.mp hgn b).mp hbEi
      show g * b * g⁻¹ * b⁻¹ ∈ frameE x i
      exact (frameE x i).mul_mem hc ((frameE x i).inv_mem hbEi)
    have hcommJ : ⁅g, b⁆ ∈ frameE x j := by
      have hc : b * g⁻¹ * b⁻¹ ∈ frameE x j :=
        (Subgroup.mem_normalizer_iff.mp (frameAux_S_le_normalizer_E F x j hbS) g⁻¹).mp
          ((frameE x j).inv_mem hgj)
      show g * b * g⁻¹ * b⁻¹ ∈ frameE x j
      have heq : g * b * g⁻¹ * b⁻¹ = g * (b * g⁻¹ * b⁻¹) := by group
      rw [heq]
      exact (frameE x j).mul_mem hgj hc
    have hcomm : ⁅g, b⁆ ∈ frameInter x i j :=
      Subgroup.mem_inf.mpr ⟨hcommE, hcommJ⟩
    have hgb : (MulAut.conj g).toMonoidHom b = ⁅g, b⁆ * b := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [hgb]
    exact Subgroup.mul_mem_sup (show ⁅g, b⁆ ∈ A from by simpa only [hAeq] using hcomm) hb

private theorem frameAux_normalizes_sup {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {g : G} (hgn : g ∈ Subgroup.normalizer (frameE x i : Set G))
    (hgj : g ∈ frameE x j) :
    g ∈ Subgroup.normalizer
      (((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap := frameAux_map_conj_le F x hx i j k hik rfl rfl hgn hgj
  refine le_antisymm hmap ?_
  have hmap' := frameAux_map_conj_le F x hx i j k hik rfl rfl
    (Subgroup.inv_mem _ hgn) ((frameE x j).inv_mem hgj)
  have hleft : ((frameInter x i j ⊔ frameInter x i k).map
      (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
      (frameInter x i j ⊔ frameInter x i k).map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hmap'
  have hcomp : ((frameInter x i j ⊔ frameInter x i k).map
      (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      frameInter x i j ⊔ frameInter x i k := by
    rw [Subgroup.map_map]
    have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply]
      group
    rw [hc, Subgroup.map_id]
  rwa [hcomp] at hleft

private theorem frameAux_commutator_mem_sup {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {u g s y : G} (hgu : g ∈ frameE x j)
    (hgn : g ∈ Subgroup.normalizer (frameE x i : Set G))
    (hs : s ∈ frameS c) (hu : u = g * s) (hy : y ∈ frameE x i ⊓ frameS c) :
    ⁅u, y⁆ ∈ ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) := by
  have hb := frameAux_commutator_pCoreOf_le_sup F x hx i j k hij hik hjk
  have hgs : ⁅s, y⁆ ∈ ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) :=
    (Subgroup.commutator_le.mp hb) s hs y hy
  have hgyE : ⁅g, y⁆ ∈ frameE x i := by
    have hc : g * y * g⁻¹ ∈ frameE x i :=
      (Subgroup.mem_normalizer_iff.mp hgn y).mp hy.1
    show g * y * g⁻¹ * y⁻¹ ∈ frameE x i
    exact (frameE x i).mul_mem hc ((frameE x i).inv_mem hy.1)
  have hgyJ : ⁅g, y⁆ ∈ frameE x j := by
    have hc : y * g⁻¹ * y⁻¹ ∈ frameE x j :=
      (Subgroup.mem_normalizer_iff.mp (frameAux_S_le_normalizer_E F x j hy.2) g⁻¹).mp
        ((frameE x j).inv_mem hgu)
    show g * y * g⁻¹ * y⁻¹ ∈ frameE x j
    have heq : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
    rw [heq]
    exact (frameE x j).mul_mem hgu hc
  have hgy : ⁅g, y⁆ ∈ frameE x i ⊓ frameE x j := Subgroup.mem_inf.mpr ⟨hgyE, hgyJ⟩
  have hgD : g ∈ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) :=
    frameAux_normalizes_sup F x hx i j k hij hik hjk hgn hgu
  have hconj : g * ⁅s, y⁆ * g⁻¹ ∈
      ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hgD ⁅s, y⁆).mp hgs
  have hid : ⁅u, y⁆ = g * ⁅s, y⁆ * g⁻¹ * ⁅g, y⁆ := by
    rw [hu, commutatorElement_def, commutatorElement_def]
    group
  rw [hid]
  exact (((frameInter x i j ⊔ frameInter x i k) : Subgroup G)).mul_mem hconj
    (Subgroup.mem_sup_left hgy)

private theorem frameAux_inf_le_sup_of_special {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {uK vK gu su gv sv : G}
    (hguE : gu ∈ frameE x j)
    (hguN : gu ∈ Subgroup.normalizer (frameE x i : Set G))
    (hsu : su ∈ frameS c) (huEq : uK = gu * su)
    (hgvE : gv ∈ frameE x k)
    (hgvN : gv ∈ Subgroup.normalizer (frameE x i : Set G))
    (hsv : sv ∈ frameS c) (hvEq : vK = gv * sv)
    (hcongr : ∀ y ∈ frameE x i,
      y⁻¹ * (⁅uK, ⁅vK, y⁆⁆ * ⁅vK, ⁅uK, y⁆⁆) ∈ conjSubgroup D.Z (x i : G)) :
    frameE x i ⊓ frameS c ≤
      ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) := by
  intro y hy
  have hu_y : ⁅uK, y⁆ ∈ ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) :=
    frameAux_commutator_mem_sup F x hx i j k hij hik hjk hguE hguN hsu huEq hy
  have hv_y : ⁅vK, y⁆ ∈ ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) := by
    have h := frameAux_commutator_mem_sup F x hx i k j hik hij hjk.symm hgvE hgvN hsv hvEq hy
    simpa [sup_comm] using h
  have hguD : gu ∈ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) :=
    frameAux_normalizes_sup F x hx i j k hij hik hjk hguN hguE
  have hgvD : gv ∈ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) := by
    simpa [sup_comm] using
      frameAux_normalizes_sup F x hx i k j hik hij hjk.symm hgvN hgvE
  have hsuD : su ∈ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) :=
    frameAux_S_le_normalizer_sup F x i j k hsu
  have hsvD : sv ∈ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) :=
    frameAux_S_le_normalizer_sup F x i j k hsv
  have huD : uK ∈ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) := by
    rw [huEq]
    exact Subgroup.mul_mem _ hguD hsuD
  have hvD : vK ∈ Subgroup.normalizer
      ((((frameInter x i j ⊔ frameInter x i k) : Subgroup G) : Subgroup G) : Set G) := by
    rw [hvEq]
    exact Subgroup.mul_mem _ hgvD hsvD
  have hA : ⁅uK, ⁅vK, y⁆⁆ ∈
      ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) := by
    have hconj := (Subgroup.mem_normalizer_iff.mp huD ⁅vK, y⁆).mp hv_y
    show uK * ⁅vK, y⁆ * uK⁻¹ * ⁅vK, y⁆⁻¹ ∈ _
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hv_y)
  have hB : ⁅vK, ⁅uK, y⁆⁆ ∈
      ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) := by
    have hconj := (Subgroup.mem_normalizer_iff.mp hvD ⁅uK, y⁆).mp hu_y
    show vK * ⁅uK, y⁆ * vK⁻¹ * ⁅uK, y⁆⁻¹ ∈ _
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hu_y)
  have hAB : ⁅uK, ⁅vK, y⁆⁆ * ⁅vK, ⁅uK, y⁆⁆ ∈
      ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) :=
    Subgroup.mul_mem _ hA hB
  have hyZ := hcongr y hy.1
  have hZV : conjSubgroup D.Z (x i : G) ≤ c.V := by
    simpa [frameAux_V_eq x i] using SL3Facts.frame_Z_le_V x i
  have hVD : c.V ≤ ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) :=
    (frameAux_V_le_inter F x i j).trans le_sup_left
  have hzD : y⁻¹ * (⁅uK, ⁅vK, y⁆⁆ * ⁅vK, ⁅uK, y⁆⁆) ∈
      ((frameInter x i j ⊔ frameInter x i k) : Subgroup G) :=
    (hZV.trans hVD) hyZ
  have hy_eq : y = (⁅uK, ⁅vK, y⁆⁆ * ⁅vK, ⁅uK, y⁆⁆) *
      (y⁻¹ * (⁅uK, ⁅vK, y⁆⁆ * ⁅vK, ⁅uK, y⁆⁆))⁻¹ := by group
  rw [hy_eq]
  exact Subgroup.mul_mem _ hAB (Subgroup.inv_mem _ hzD)

private theorem frameAux_special_powers {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) {u v : ↥(c.H F.hV)} {uK vK : G}
    (huKL : uK ∈ c.L) (huKi : uK ∈ conjSubgroup c.K (x i : G))
    (huKphi : c.phiL F.hV ⟨uK, huKL⟩ = u)
    (hvKL : vK ∈ c.L) (hvKi : vK ∈ conjSubgroup c.K (x i : G))
    (hvKphi : c.phiL F.hV ⟨vK, hvKL⟩ = v)
    (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (huv3 : (u * v) ^ 3 = 1)
    (huv_not : u * v ∉ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom) :
    uK ^ 2 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) ∧
      vK ^ 2 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) ∧
      (uK * vK) ^ 3 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) ∧
      uK * vK ∉ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) := by
  have hpuL : uK ^ 2 ∈ c.L := Subgroup.pow_mem (K := c.L) huKL 2
  have hpuK : uK ^ 2 ∈ conjSubgroup c.K (x i : G) :=
    Subgroup.pow_mem (K := conjSubgroup c.K (x i : G)) huKi 2
  have hpvL : vK ^ 2 ∈ c.L := Subgroup.pow_mem (K := c.L) hvKL 2
  have hpvK : vK ^ 2 ∈ conjSubgroup c.K (x i : G) :=
    Subgroup.pow_mem (K := conjSubgroup c.K (x i : G)) hvKi 2
  have hpuvL : (uK * vK) ^ 3 ∈ c.L :=
    Subgroup.pow_mem (K := c.L) (c.L.mul_mem huKL hvKL) 3
  have hpuvK : (uK * vK) ^ 3 ∈ conjSubgroup c.K (x i : G) :=
    Subgroup.pow_mem (K := conjSubgroup c.K (x i : G))
      (Subgroup.mul_mem _ huKi hvKi) 3
  have hu2O : uK ^ 2 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) := by
    refine frameAux_mem_pCoreOf_of_phi_eq_one F x i hpuL hpuK ?_
    rw [show (⟨uK ^ 2, hpuL⟩ : ↥c.L) = ⟨uK, huKL⟩ ^ 2 from rfl,
      map_pow, huKphi, hu2]
  have hv2O : vK ^ 2 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) := by
    refine frameAux_mem_pCoreOf_of_phi_eq_one F x i hpvL hpvK ?_
    rw [show (⟨vK ^ 2, hpvL⟩ : ↥c.L) = ⟨vK, hvKL⟩ ^ 2 from rfl,
      map_pow, hvKphi, hv2]
  have hphi_mul : c.phiL F.hV ⟨uK * vK, c.L.mul_mem huKL hvKL⟩ = u * v := by
    rw [show (⟨uK * vK, c.L.mul_mem huKL hvKL⟩ : ↥c.L) =
      ⟨uK, huKL⟩ * ⟨vK, hvKL⟩ from rfl, map_mul, huKphi, hvKphi]
  have huv3O : (uK * vK) ^ 3 ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) := by
    refine frameAux_mem_pCoreOf_of_phi_eq_one F x i hpuvL hpuvK ?_
    rw [show (⟨(uK * vK) ^ 3, hpuvL⟩ : ↥c.L) =
      ⟨uK * vK, c.L.mul_mem huKL hvKL⟩ ^ 3 from rfl, map_pow, hphi_mul, huv3]
  have huvO : uK * vK ∉ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i : G)) := by
    intro hmem
    have hcontra := frameAux_phi_pCoreOf_mem F x i (c.L.mul_mem huKL hvKL) hmem
    rw [hphi_mul] at hcontra
    exact huv_not hcontra
  exact ⟨hu2O, hv2O, huv3O, huvO⟩

private theorem frameAux_special_data {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ uK vK gu su gv sv : G,
      uK ∈ conjSubgroup c.K (x i : G) ∧ vK ∈ conjSubgroup c.K (x i : G) ∧
      gu ∈ frameE x j ∧ gu ∈ Subgroup.normalizer (frameE x i : Set G) ∧
      su ∈ frameS c ∧ uK = gu * su ∧
      gv ∈ frameE x k ∧ gv ∈ Subgroup.normalizer (frameE x i : Set G) ∧
      sv ∈ frameS c ∧ vK = gv * sv ∧
      ∀ y ∈ frameE x i,
        y⁻¹ * (⁅uK, ⁅vK, y⁆⁆ * ⁅vK, ⁅uK, y⁆⁆) ∈ conjSubgroup D.Z (x i : G) := by
  obtain ⟨u, hu_mem, v, hv_mem, hu2, hv2, huv3, huv_not⟩ := hx.2.2.2 i j k hij hik hjk
  obtain ⟨uK, gu, su, huKL, huKi, huKphi, hguE, hguN, hsu, huEq⟩ :=
    frameAux_exists_decomp F x hx hij hu_mem.2 hu_mem.1
  obtain ⟨vK, gv, sv, hvKL, hvKi, hvKphi, hgvE, hgvN, hsv, hvEq⟩ :=
    frameAux_exists_decomp F x hx hik hv_mem.2 hv_mem.1
  obtain ⟨hu2O, hv2O, huv3O, huvO⟩ :=
    frameAux_special_powers F x i huKL huKi huKphi hvKL hvKi hvKphi hu2 hv2 huv3 huv_not
  have hcongr := frameAux_point_congruence F x i huKi hvKi hu2O hv2O huv3O huvO
  exact ⟨uK, vK, gu, su, gv, sv, huKi, hvKi, hguE, hguN, hsu, huEq,
    hgvE, hgvN, hsv, hvEq, hcongr⟩

theorem SL3Facts.inf_pCoreOf_le {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    frameE x i ⊓ CFSG.Open.pCoreOf 2 c.L ≤
      ((frameE x i ⊓ frameE x j : Subgroup G) ⊔ (frameE x i ⊓ frameE x k : Subgroup G)) := by
  obtain ⟨uK, vK, gu, su, gv, sv, huKi, hvKi, hguE, hguN, hsu, huEq,
    hgvE, hgvN, hsv, hvEq, hcongr⟩ := frameAux_special_data F x hx i j k hij hik hjk
  exact frameAux_inf_le_sup_of_special F x hx i j k hij hik hjk hguE hguN hsu huEq
    hgvE hgvN hsv hvEq hcongr

private theorem frameAux_sq_inter {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i j : Fin 3) {y : G} (hy : y ∈ frameInter x i j) :
    y ^ 2 ∈ c.V := by
  have hy2 : y ^ 2 ∈ conjSubgroup D.Z (x i : G) := F.frame_sq_mem_Z x i hy.1
  have hZV : conjSubgroup D.Z (x i : G) ≤ c.V := by
    simpa [frameAux_V_eq x i] using SL3Facts.frame_Z_le_V x i
  exact hZV hy2

private theorem frameAux_pair_le_V {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) {p : Fin 3} {A B : Subgroup G}
    (hA : A ≤ frameE x p) (hB : B ≤ frameE x p) : ⁅A, B⁆ ≤ c.V := by
  have hZV : conjSubgroup D.Z (x p : G) ≤ c.V := by
    simpa [frameAux_V_eq x p] using SL3Facts.frame_Z_le_V x p
  exact ((Subgroup.commutator_mono hA hB).trans (F.frame_commutator_le x p)).trans hZV

private abbrev frameTriple {c : Ctx2311 D Ch} (x : Fin 3 → ↥c.L) : Fin 3 → Subgroup G :=
  ![frameInter x 0 1, frameInter x 0 2, frameInter x 1 2]

private theorem frameAux_pCoreOf_le_normalizer_V {c : Ctx2311 D Ch} :
    frameS c ≤ Subgroup.normalizer (c.V : Set G) :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L).trans
    ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans
      (Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L))

private theorem frameAux_pCoreOf_eq_sup_inter {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    frameS c = (frameInter x 0 1 ⊔ frameInter x 0 2 ⊔ frameInter x 1 2 : Subgroup G) := by
  have hB0 := F.inf_pCoreOf_le x hx 0 1 2 (by decide) (by decide) (by decide)
  have hB1 := F.inf_pCoreOf_le x hx 1 0 2 (by decide) (by decide) (by decide)
  have hB2 := F.inf_pCoreOf_le x hx 2 0 1 (by decide) (by decide) (by decide)
  let A01 : Subgroup G := frameInter x 0 1
  let A02 : Subgroup G := frameInter x 0 2
  let A12 : Subgroup G := frameInter x 1 2
  let D3 : Subgroup G := A01 ⊔ A02 ⊔ A12
  change frameS c = D3
  have hB0' : frameE x 0 ⊓ frameS c ≤ A01 ⊔ A02 := by
    simpa only [A01, A02, frameInter] using hB0
  have hB1' : frameE x 1 ⊓ frameS c ≤ A01 ⊔ A12 := by
    simpa only [A01, A12, frameInter, inf_comm] using hB1
  have hB2' : frameE x 2 ⊓ frameS c ≤ A02 ⊔ A12 := by
    simpa only [A02, A12, frameInter, inf_comm] using hB2
  have hSsplit : frameS c =
      (frameE x 0 ⊓ frameS c) ⊔ (frameE x 1 ⊓ frameS c) ⊔ (frameE x 2 ⊓ frameS c) :=
    (F.pCoreOf_eq_iSup_frame x hx).trans (CFSG.Quasithin.iSup_fin_three _)
  refine le_antisymm ?_ ?_
  · rw [hSsplit]
    change (frameE x 0 ⊓ frameS c) ⊔ (frameE x 1 ⊓ frameS c) ⊔
      (frameE x 2 ⊓ frameS c) ≤ A01 ⊔ A02 ⊔ A12
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hB0'.trans le_sup_left
    · exact hB1'.trans (sup_le (le_trans le_sup_left le_sup_left) le_sup_right)
    · exact hB2'.trans (sup_le (le_trans le_sup_right le_sup_left) le_sup_right)
  · change A01 ⊔ A02 ⊔ A12 ≤ frameS c
    refine sup_le (sup_le ?_ ?_) ?_
    · simpa only [A01, frameInter] using frameAux_A_le_pCoreOf F x hx 0 1 (by decide)
    · simpa only [A02, frameInter] using frameAux_A_le_pCoreOf F x hx 0 2 (by decide)
    · simpa only [A12, frameInter] using frameAux_A_le_pCoreOf F x hx 1 2 (by decide)

private theorem frameAux_iSup_triple_eq_pCoreOf {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    (⨆ i, frameTriple x i) = frameS c := by
  rw [CFSG.Quasithin.iSup_fin_three, frameAux_pCoreOf_eq_sup_inter F x hx]
  simp [frameTriple]

private theorem frameAux_commutator_pCoreOf_le_V {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    ⁅frameS c, frameS c⁆ ≤ c.V := by
  have hSA := frameAux_iSup_triple_eq_pCoreOf F x hx
  have hSleN := frameAux_pCoreOf_le_normalizer_V (D := D) (Ch := Ch) (c := c)
  have hAN : ∀ i, frameTriple x i ≤ Subgroup.normalizer (c.V : Set G) := by
    intro i
    fin_cases i
    · exact (frameAux_A_le_pCoreOf F x hx 0 1 (by decide)).trans hSleN
    · exact (frameAux_A_le_pCoreOf F x hx 0 2 (by decide)).trans hSleN
    · exact (frameAux_A_le_pCoreOf F x hx 1 2 (by decide)).trans hSleN
  have hpair : ∀ i j, ⁅frameTriple x i, frameTriple x j⁆ ≤ c.V := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [frameTriple]
    · exact frameAux_pair_le_V F x inf_le_left inf_le_left
    · exact frameAux_pair_le_V F x inf_le_left inf_le_left
    · exact frameAux_pair_le_V F x inf_le_right inf_le_left
    · exact frameAux_pair_le_V F x inf_le_left inf_le_left
    · exact frameAux_pair_le_V F x inf_le_left inf_le_left
    · exact frameAux_pair_le_V F x inf_le_right inf_le_right
    · exact frameAux_pair_le_V F x inf_le_left inf_le_right
    · exact frameAux_pair_le_V F x inf_le_right inf_le_right
    · exact frameAux_pair_le_V F x inf_le_left inf_le_left
  have hright : ∀ i, ⁅frameTriple x i, ⨆ j, frameTriple x j⁆ ≤ c.V := fun i =>
    CFSG.GroupTheory.commutator_iSup_right_le_of_le_normalizer
      (B := frameTriple x) (K := frameTriple x i) (N := c.V) hAN (fun j => hpair i j)
  have h := CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
    (A := frameTriple x) (Y := ⨆ j, frameTriple x j) (N := c.V) hAN hright
  rwa [hSA] at h

private theorem frameAux_sq_mul_mem {c : Ctx2311 D Ch}
    [hN : (c.V.subgroupOf (frameS c)).Normal] {y z : ↥(frameS c)}
    (hyz : ⁅y, z⁆ ∈ c.V.subgroupOf (frameS c))
    (hy : y ^ 2 ∈ c.V.subgroupOf (frameS c))
    (hz : z ^ 2 ∈ c.V.subgroupOf (frameS c)) :
    (y * z) ^ 2 ∈ c.V.subgroupOf (frameS c) := by
  let N : Subgroup ↥(frameS c) := c.V.subgroupOf (frameS c)
  haveI : N.Normal := hN
  change (y * z) ^ 2 ∈ N
  rw [← QuotientGroup.eq_one_iff]
  have hcomm : Commute (QuotientGroup.mk' N y) (QuotientGroup.mk' N z) :=
    QuotientGroup.commute_mk_iff.mpr hyz
  have hy1 : (QuotientGroup.mk' N y) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ 2)).mpr hy
  have hz1 : (QuotientGroup.mk' N z) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (z ^ 2)).mpr hz
  change (QuotientGroup.mk' N) ((y * z) ^ 2) = 1
  rw [show (QuotientGroup.mk' N) ((y * z) ^ 2) =
      ((QuotientGroup.mk' N) y * (QuotientGroup.mk' N) z) ^ 2 by
    rw [map_pow, map_mul]]
  rw [hcomm.mul_pow, hy1, hz1, mul_one]

private theorem frameAux_sq_mem_V {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    ∀ s ∈ frameS c, s ^ 2 ∈ c.V := by
  have hcomm := frameAux_commutator_pCoreOf_le_V F x hx
  have hSA := frameAux_iSup_triple_eq_pCoreOf F x hx
  have hSclosure : frameS c = Subgroup.closure (⋃ i, (frameTriple x i : Set G)) := by
    rw [← hSA, Subgroup.iSup_eq_closure]
  haveI : (c.V.subgroupOf (frameS c)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (frameAux_pCoreOf_le_normalizer_V (D := D) (Ch := Ch) (c := c))
  intro s hs
  rw [hSclosure] at hs
  induction hs using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      fin_cases i
      · exact frameAux_sq_inter F x 0 1 (by simpa [frameTriple] using hyi)
      · exact frameAux_sq_inter F x 0 2 (by simpa [frameTriple] using hyi)
      · exact frameAux_sq_inter F x 1 2 (by simpa [frameTriple] using hyi)
  | one => simp
  | mul y z hy hz ihy ihz =>
      have hyS : y ∈ frameS c := hSclosure.symm ▸ hy
      have hzS : z ∈ frameS c := hSclosure.symm ▸ hz
      have hyz : ⁅y, z⁆ ∈ c.V :=
        (Subgroup.commutator_le.mp hcomm) y hyS z hzS
      have hsq := frameAux_sq_mul_mem
        (y := (⟨y, hyS⟩ : ↥(frameS c))) (z := (⟨z, hzS⟩ : ↥(frameS c)))
        (Subgroup.mem_subgroupOf.mpr hyz)
        (Subgroup.mem_subgroupOf.mpr ihy) (Subgroup.mem_subgroupOf.mpr ihz)
      exact Subgroup.mem_subgroupOf.mp hsq
  | inv y hy ihy =>
      simpa [inv_pow] using c.V.inv_mem ihy

theorem SL3Facts.pCoreOf_eq_sup_inter {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i))) :
    CFSG.Open.pCoreOf 2 c.L =
        (((frameE x 0 ⊓ frameE x 1 : Subgroup G) ⊔
          (frameE x 0 ⊓ frameE x 2 : Subgroup G) ⊔
          (frameE x 1 ⊓ frameE x 2 : Subgroup G)) : Subgroup G) ∧
      ⁅CFSG.Open.pCoreOf 2 c.L, CFSG.Open.pCoreOf 2 c.L⁆ ≤ c.V ∧
        ∀ s ∈ CFSG.Open.pCoreOf 2 c.L, s ^ 2 ∈ c.V :=
  ⟨frameAux_pCoreOf_eq_sup_inter F x hx,
    frameAux_commutator_pCoreOf_le_V F x hx,
    frameAux_sq_mem_V F x hx⟩

end Ctx2311

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

