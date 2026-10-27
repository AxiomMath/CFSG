module

public import CFSG.Sporadic.Schreier.RuOrbLInvInputs
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.RuCentralizer
public import CFSG.Sporadic.Schreier.RuLGroup
public import CFSG.Sporadic.Schreier.RuTreeElt

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruL_card_of_count
    {p : Array ℕ → Bool} {P : Equiv.Perm (Fin 4060) → Prop}
    (hp : ∀ t g, Rep 4060 t g → (p t = true ↔ P g)) :
    Nat.card {g : ruL // P g} = count2 4060 ruLevL p := by
  have h := ruL_check.1
  have key : Nat.card {g : ruChainL.originalSubgroup // P g} = count2 4060 ruLevL p :=
    chain_card_of_count2 (ruChain_arrays h) (by norm_num : 0 < 4) h rfl hp
  rw [ruChainL_sub] at key
  exact key

theorem ruCommTest_iff {l t : Array ℕ} {L T : Equiv.Perm (Fin 4060)} (hl : Rep 4060 l L)
    (ht : Rep 4060 t T) : ruCommTest l t = true ↔ L * T = T * L := by
  rw [ruCommTest, allLt_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rwa [beq_iff_eq, ht x, hl (T x), hl x, ht (L x)] at this
  · intro h i hi
    rw [beq_iff_eq, ht.apply hi, hl (T _), hl.apply hi, ht (L _)]
    exact congrArg Fin.val (congrArg (fun f : Equiv.Perm (Fin 4060) => f ⟨i, hi⟩) h)

theorem ruL_check' :
    ruChainOK 4060 (ruField4060 5) 3 6 ruLChainBase ruLChainDerivations = true := ruL_check.1

theorem ruL_arrays :
    ChainArrays ruChainL ((ruField4060 5).extract 0 3) (ruField4060 5)
      (ruBaseArr 4060 ruLChainBase) (ruWordsArr 3 6 ruLChainDerivations) :=
  ruChain_arrays ruL_check'

theorem ruL_lev_sizes :
    (ChainArrays.lev 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) 0).pts.size = 1820 ∧
      (ChainArrays.lev 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) 1).pts.size = 64 := by
  have e := (chain_rawOrbitSizes_eq ruL_arrays).symm.trans ruL_check.2.1
  have hb : ruChainL.baseCount = 2 := rfl
  rw [hb] at e
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
  exact e

@[expose] def ruZL (i : ℕ) : Equiv.Perm (Fin 4060) :=
  ChainArrays.levT 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) 0 (ruZLPos.getD i (0, 0)).1 *
    ChainArrays.levT 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) 1 (ruZLPos.getD i (0, 0)).2

theorem rep_ruZL {i : ℕ} (hi : i < 3) :
    Rep 4060 (ruZLA i) (ruZL i) := by
  have ha : (ruZLPos.getD i (0, 0)).1 < 1820 := by interval_cases i <;> decide
  have hb : (ruZLPos.getD i (0, 0)).2 < 64 := by interval_cases i <;> decide
  exact chain_rep_prod2A ruL_arrays ruL_check' (by decide) (ruL_lev_sizes.1 ▸ ha)
    (ruL_lev_sizes.2 ▸ hb)

abbrev ruLOrbFixP (t : Equiv.Perm (Fin 4060)) : ℕ := Nat.card {g : ruL // t (g.1 0) = g.1 0}

abbrev ruLInvP (t : Equiv.Perm (Fin 4060)) : List ℕ :=
  ruLOrbFixP t :: (List.range 3).flatMap fun i =>
    [(fixSet (ruZL i * t)).ncard, (fixSet (ruZL i * t * (ruZL i * t))).ncard]

theorem ruLInv_eq
    {t : Array ℕ} {T : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t T) :
    ruLInv t = ruLInvP T := by
  have hf : ∀ {x : Array ℕ} {X : Equiv.Perm (Fin 4060)}, Rep 4060 x X →
      ruFixCnt x = (fixSet X).ncard := fun hx => by
    rw [ruFixCnt, ← ncard_finSet (pointList_fixedList _), finSet_fixedList hx]
  have hc : ruLOrbFix t = ruLOrbFixP T := by
    rw [ruLOrbFix, ruLOrbFixP, ruL_card_of_count (P := fun g => T (g 0) = g 0)
      (p := fun l => t[l[0]!]! == l[0]!) fun l g hl => by
        rw [beq_iff_eq, hl.apply (by norm_num : 0 < 4060), ht (g ⟨0, by norm_num⟩)]
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩]
  rw [ruLInv, ruLInvP, hc]
  refine congrArg (List.cons (ruLOrbFixP T)) (List.flatMap_congr fun i hi => ?_)
  have hi3 : i < 3 := List.mem_range.1 hi
  have hy := rep_compA (rep_ruZL hi3) ht
  rw [hf hy, hf (rep_compA hy hy)]

theorem ruLInvP_conj
    (hz : ∀ i < 3, ruZL i ∈ Subgroup.centralizer (ruL : Set (Equiv.Perm (Fin 4060)))) {l : Equiv.Perm (Fin 4060)} (hl : l ∈ ruL) (t : Equiv.Perm (Fin 4060)) :
    ruLInvP (l * t * l⁻¹) = ruLInvP t := by
  have hc : ruLOrbFixP (l * t * l⁻¹) = ruLOrbFixP t := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft (⟨l, hl⟩ : ruL)⁻¹) fun g => ?_)
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    exact Equiv.Perm.eq_inv_iff_eq.symm
  rw [ruLInvP, ruLInvP, hc]
  refine congrArg (List.cons (ruLOrbFixP t)) (List.flatMap_congr fun i hi => ?_)
  have hi3 : i < 3 := List.mem_range.1 hi
  have e : ruZL i * (l * t * l⁻¹) = l * (ruZL i * t) * l⁻¹ :=
    calc ruZL i * (l * t * l⁻¹) = ruZL i * l * t * l⁻¹ := by group
      _ = l * ruZL i * t * l⁻¹ := by rw [(Subgroup.mem_centralizer_iff.1 (hz i hi3) l hl).symm]
      _ = l * (ruZL i * t) * l⁻¹ := by group
  have e2 : ruZL i * (l * t * l⁻¹) * (ruZL i * (l * t * l⁻¹)) =
      l * (ruZL i * t * (ruZL i * t)) * l⁻¹ := by
    rw [e]
    group
  rw [e2, e, ncard_fixSet_conj, ncard_fixSet_conj]

abbrev ruRepZ (k : ℕ) : Equiv.Perm (Fin 4060) := ruTZ (ruReps.getD k 0)

theorem rep_ruRepZ
    (k : ℕ) : Rep 4060 (ruRepZA k) (ruRepZ k) := rep_ruTZ _

abbrev ruOrb (k : ℕ) : Set (Equiv.Perm (Fin 4060)) := conjSet ruL (ruRepZ k)

end CFSG.Sporadic.RuSchreier
