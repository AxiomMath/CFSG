module

public import CFSG.Monster.B.TwoA.Unitary.CliqueFibers
public import CFSG.Monster.B.TwoA.Unitary.CliqueMain
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix
open scoped LinearAlgebra.Projectivization

theorem smul_eq_pt (g : SU frobeniusF4 6) (q : IsoPt) :
    g • q = pt (g • q.1.rep) ((smul_ne_zero_iff_ne g).mpr (rep_ne_zero q))
      (by rw [herm_smul_smul]; exact isIsoPt_of q) := by
  conv_lhs => rw [← pt_rep q]
  exact smul_pt g _ _

theorem herm_rep_smul_iff (g : SU frobeniusF4 6) (q : IsoPt) (v : V) :
    herm v (g • q).1.rep = 0 ↔ herm v (g • q.1.rep) = 0 := by
  obtain ⟨c, hc⟩ := rep_pt ((smul_ne_zero_iff_ne g).mpr (rep_ne_zero q))
    (by rw [herm_smul_smul]; exact isIsoPt_of q)
  rw [smul_eq_pt, ← hc, Units.smul_def, herm_smul_right, mul_eq_zero,
    or_iff_right (fun h => c.ne_zero (bar_eq_zero_iff.1 h))]

theorem perpSub_smul (g : SU frobeniusF4 6) (q : IsoPt) :
    perpSub (g • q) = smulSub g (perpSub q) := by
  ext v
  rw [mem_perpSub, herm_rep_smul_iff, mem_smulSub, mem_perpSub, herm_inv_smul]

theorem smulSub_inf (g : SU frobeniusF4 6) (X Y : Submodule F4 V) :
    smulSub g (X ⊓ Y) = smulSub g X ⊓ smulSub g Y := by
  ext v
  rw [Submodule.mem_inf, mem_smulSub, mem_smulSub, mem_smulSub, Submodule.mem_inf]

theorem smulSub_inv_smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    smulSub g⁻¹ (smulSub g X) = X := by
  rw [← smulSub_mul, inv_mul_cancel, smulSub_one]

theorem smulSub_inj (g : SU frobeniusF4 6) {X Y : Submodule F4 V} :
    smulSub g X = smulSub g Y ↔ X = Y :=
  ⟨fun h => by rw [← smulSub_inv_smulSub g X, h, smulSub_inv_smulSub], fun h => h ▸ rfl⟩

theorem smul_mem_fiberY (g : SU frobeniusF4 6) (W A : Submodule F4 V) (q : IsoPt) :
    g • q ∈ fiberY (smulSub g W) (smulSub g A) ↔ q ∈ fiberY W A := by
  rw [mem_fiberY, mem_fiberY, smul_mem_planePts, perpSub_smul, ← smulSub_inf, smulSub_inj]

theorem fiberY_smulSub (g : SU frobeniusF4 6) (W A : Submodule F4 V) :
    fiberY (smulSub g W) (smulSub g A) = (g • ·) '' fiberY W A := by
  ext p
  constructor
  · intro hp
    refine ⟨g⁻¹ • p, ?_, smul_inv_smul g p⟩
    rw [← smul_mem_fiberY g, smul_inv_smul]
    exact hp
  · rintro ⟨q, hq, rfl⟩
    exact (smul_mem_fiberY g W A q).2 hq

theorem fixL_smul (g : SU frobeniusF4 6) (q : IsoPt) :
    fixL (g • q) = (fixL q).map (MulAut.conj (g : ProjSU)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_fixL, mem_fixL, map_mul, map_mul,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, projAct_mk, projAct_mk_inv]
  constructor
  · intro h
    rw [h, inv_smul_smul]
  · intro h
    calc projAct x (g • q) = g • (g⁻¹ • projAct x (g • q)) := (smul_inv_smul g _).symm
      _ = g • q := by rw [h]

theorem ncard_fiberY {W A : Submodule F4 V} (hW : IsMaxIso W) (hAW : A ≤ W)
    (hA : Module.finrank F4 A = 2) : (fiberY W A).ncard = 32 := by
  obtain ⟨g, rfl, rfl⟩ := exists_smulSub_W0_A0 hW hAW hA
  rw [fiberY_smulSub, Set.ncard_image_of_injective _ (MulAction.injective g), ncard_fiberY_W0_A0]

theorem ncard_planePts_line {W A : Submodule F4 V} (hW : IsMaxIso W) (hAW : A ≤ W)
    (hA : Module.finrank F4 A = 2) : (planePts A).ncard = 5 := by
  obtain ⟨g, rfl, rfl⟩ := exists_smulSub_W0_A0 hW hAW hA
  rw [ncard_planePts_smulSub, ncard_planePts_A0]

theorem projAct_conj_smul (g : SU frobeniusF4 6) (y : ProjSU) (q : IsoPt) :
    projAct (MulAut.conj (g : ProjSU) y) (g • q) = g • projAct y q := by
  rw [MulAut.conj_apply, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    projAct_mk, projAct_mk_inv, inv_smul_smul]

theorem exists_kerL_of_mem_fiberY {W A : Submodule F4 V} (hW : IsMaxIso W) (hAW : A ≤ W)
    (hA : Module.finrank F4 A = 2) {p q : IsoPt} (hp : p ∈ fiberY W A) (hq : q ∈ fiberY W A) :
    ∃ x ∈ kerL W, projAct x p = q := by
  obtain ⟨g, rfl, rfl⟩ := exists_smulSub_W0_A0 hW hAW hA
  rw [fiberY_smulSub] at hp hq
  obtain ⟨p', hp', rfl⟩ := hp
  obtain ⟨q', hq', rfl⟩ := hq
  obtain ⟨y, hy, hyp⟩ := exists_kerL_W0_of_mem_fiberY hp' hq'
  refine ⟨MulAut.conj (g : ProjSU) y, ?_, ?_⟩
  · rw [kerL_smulSub]
    exact ⟨y, hy, rfl⟩
  · rw [projAct_conj_smul, hyp]

theorem kerL_inf_fixL {W A : Submodule F4 V} (hW : IsMaxIso W) (hAW : A ≤ W)
    (hA : Module.finrank F4 A = 2) {p : IsoPt} (hp : p ∈ fiberY W A) :
    kerL W ⊓ fixL p = Subgroup.closure (tPt '' planePts A) := by
  obtain ⟨g, rfl, rfl⟩ := exists_smulSub_W0_A0 hW hAW hA
  rw [fiberY_smulSub] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  rw [kerL_smulSub, fixL_smul, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    kerL_W0_inf_fixL hp', MonoidHom.map_closure, image_tPt_planePts_smulSub]

theorem natCard_kerL_inf_fixL {W A : Submodule F4 V} (hW : IsMaxIso W) (hAW : A ≤ W)
    (hA : Module.finrank F4 A = 2) {p : IsoPt} (hp : p ∈ fiberY W A) :
    Nat.card (kerL W ⊓ fixL p : Subgroup ProjSU) = 16 := by
  let _ : MulAction ProjSU IsoPt := MulAction.compHom IsoPt projAct
  have hsmul : ∀ (x : kerL W) (q : IsoPt), x • q = projAct (x : ProjSU) q := fun _ _ => rfl
  have horbit : MulAction.orbit (kerL W) p = fiberY W A := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      change x • p ∈ fiberY W A
      rw [hsmul]
      exact projAct_mem_fiberY hW.2 x.2 hp
    · intro hq
      obtain ⟨x, hx, hxq⟩ := exists_kerL_of_mem_fiberY hW hAW hA hp hq
      refine ⟨⟨x, hx⟩, ?_⟩
      change (⟨x, hx⟩ : kerL W) • p = q
      rw [hsmul]
      exact hxq
  have hstab : MulAction.stabilizer (kerL W) p = (kerL W ⊓ fixL p).subgroupOf (kerL W) := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hsmul,
      mem_fixL]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (kerL W) p)
  rw [MulAction.index_stabilizer, horbit, ncard_fiberY hW hAW hA, hW.natCard_kerL, hstab,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  omega

theorem ncard_lines {W : Submodule F4 V} (hW : IsMaxIso W) :
    {A : Submodule F4 V | A ≤ W ∧ Module.finrank F4 A = 2}.ncard = 21 := by
  classical
  set 𝒜 := {A : Submodule F4 V | A ≤ W ∧ Module.finrank F4 A = 2} with h𝒜
  have hfin : 𝒜.Finite := Set.toFinite _
  set s : Finset IsoPt := (planePts W)ᶜ.toFinset with hsdef
  have hs : s.card = 672 := by
    rw [hsdef, ← Set.ncard_eq_toFinset_card', Set.ncard_compl, hW.ncard_planePts,
      Nat.card_eq_fintype_card, card_isoPt]
  have hmaps : Set.MapsTo (fun p => perpSub p ⊓ W) s hfin.toFinset := by
    intro p hp
    rw [Finset.mem_coe, hsdef, Set.mem_toFinset] at hp
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨inf_le_right, finrank_perpSub_inf hW hp⟩
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ A ∈ hfin.toFinset, (s.filter fun p => perpSub p ⊓ W = A).card = 32 := by
    intro A hA
    rw [Set.Finite.mem_toFinset] at hA
    have e : (s.filter fun p => perpSub p ⊓ W = A) = (fiberY W A).toFinset := by
      ext p
      rw [Finset.mem_filter, hsdef, Set.mem_toFinset, Set.mem_toFinset]
      rfl
    rw [e, ← Set.ncard_eq_toFinset_card', ncard_fiberY hW hA.1 hA.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hs] at h
  rw [Set.ncard_eq_toFinset_card 𝒜 hfin]
  omega

theorem unitary_six_plane_complement_unipotent_fibers :
    (∀ (p : IsoPt) (v : V), v ∈ perpSub p ↔ ∀ w ∈ p.1.submodule, herm v w = 0) ∧
    (∀ (p : IsoPt) (x : ProjSU), x ∈ fixL p ↔ projAct x p = p) ∧
    ∀ W : Submodule F4 V, IsMaxIso W →
      (∀ p : IsoPt, p ∉ planePts W →
        ∃! A : Submodule F4 V, A ≤ W ∧ Module.finrank F4 A = 2 ∧ p ∈ fiberY W A) ∧
      {A : Submodule F4 V | A ≤ W ∧ Module.finrank F4 A = 2}.ncard = 21 ∧
      ∀ A : Submodule F4 V, A ≤ W → Module.finrank F4 A = 2 →
        (fiberY W A).ncard = 32 ∧
        (∀ x ∈ kerL W, ∀ p ∈ fiberY W A, projAct x p ∈ fiberY W A) ∧
        (∀ p ∈ fiberY W A, ∀ q ∈ fiberY W A, ∃ x ∈ kerL W, projAct x p = q) ∧
        (planePts A).ncard = 5 ∧
        (∀ p ∈ fiberY W A, kerL W ⊓ fixL p = Subgroup.closure (tPt '' planePts A)) ∧
        CFSG.IsElementaryAbelian 2 (Subgroup.closure (tPt '' planePts A)) ∧
        Nat.card (Subgroup.closure (tPt '' planePts A)) = 16 ∧
        (∀ p ∈ fiberY W A, ∀ q ∈ planePts W, isoGraph.Adj p q ↔ q ∈ planePts A) := by
  refine ⟨fun _ _ => mem_perpSub_iff, fun _ _ => mem_fixL, fun W hW => ⟨?_, ncard_lines hW,
    fun A hAW hA => ?_⟩⟩
  · intro p hp
    refine ⟨perpSub p ⊓ W, ⟨inf_le_right, finrank_perpSub_inf hW hp, hp, rfl⟩, ?_⟩
    rintro A ⟨-, -, -, hA⟩
    exact hA.symm
  · have hne : (fiberY W A).Nonempty := Set.nonempty_of_ncard_ne_zero (by
      rw [ncard_fiberY hW hAW hA]
      decide)
    obtain ⟨p₀, hp₀⟩ := hne
    have hcl : Subgroup.closure (tPt '' planePts A) ≤ kerL W := by
      rw [Subgroup.closure_le]
      rintro _ ⟨q, hq, rfl⟩
      exact tPt_mem_kerL hW.2 (planePts_mono hAW hq)
    refine ⟨ncard_fiberY hW hAW hA, fun x hx p hp => projAct_mem_fiberY hW.2 hx hp,
      fun p hp q hq => exists_kerL_of_mem_fiberY hW hAW hA hp hq, ncard_planePts_line hW hAW hA,
      fun p hp => kerL_inf_fixL hW hAW hA hp, ?_, ?_,
      fun p hp q hq => adj_iff_of_mem_fiberY hp hq⟩
    · exact isElementaryAbelian_two_of _ (fun x hx y hy => hW.kerL_comm x (hcl hx) y (hcl hy))
        (fun x hx => hW.kerL_sq x (hcl hx))
    · rw [← kerL_inf_fixL hW hAW hA hp₀]
      exact natCard_kerL_inf_fixL hW hAW hA hp₀

end CFSG.Monster.B.TwoA.Unitary.Clique
