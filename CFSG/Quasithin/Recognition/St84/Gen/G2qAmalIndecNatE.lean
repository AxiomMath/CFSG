module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecNatEPair
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecBasic
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSplit
import CFSG.Quasithin.Recognition.St84.Gen.L2QuadSecNat
import CFSG.Quasithin.Background.SpecialPGroupCenter
import CFSG.Quasithin.EmptyFaithful.S1422Center

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

private theorem natE_mem_iff_apply_one_eq_zero {G : Type*} [Group G] {L Z N S : Subgroup G}
    {F : Type} [Field F] [Finite F] {α : ↥L →* SL(2, F)} {zv : G → Fin 2 → F}
    (hzv : IsNatSecCoord L Z ⊥ α zv) (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (hNZ : N ≤ Z)
    (hN : ∀ z ∈ N, ∀ s ∈ S, s * z = z * s) (hcard : Nat.card N = Nat.card F) {z : G}
    (hz : z ∈ Z) : z ∈ N ↔ zv z 1 = 0 := by
  have hfwd : ∀ n ∈ N, zv n 1 = 0 := fun n hn =>
    hzv.apply_one_eq_zero_of_commutator_mem hα hmem (hNZ hn) fun s hs =>
      Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hN n hn s hs))
  refine ⟨hfwd z, fun h1 => ?_⟩
  have hinj : Function.Injective fun n : ↥N => zv n 0 := by
    intro n n' h
    refine Subtype.ext (hzv.eq_of_eq (hNZ n.2) (hNZ n'.2) ?_)
    funext i
    fin_cases i
    · exact h
    · exact (hfwd n n.2).trans (hfwd n' n'.2).symm
  obtain ⟨n, hn⟩ := (hinj.bijective_of_nat_card_le hcard.symm.le).2 (zv z 0)
  have hnz : (n : G) = z := by
    refine hzv.eq_of_eq (hNZ n.2) hz ?_
    funext i
    fin_cases i
    · exact hn
    · exact (hfwd n n.2).trans h1.symm
  rw [← hnz]
  exact n.2

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

attribute [local instance] G2qCoord.field G2qCoord.fintype

private theorem natE_exists_splitData (hD : G2qLocalData L1 L2 S f) (c : G2qCoordRight L2 S f) :
    ∃ nv zv : G → Fin 2 → c.F,
      G2qSplitData L2 (pCoreOf 2 L2) (centerOf (pCoreOf 2 L2)) c.W c.α nv zv := by
  obtain ⟨nv, hnv⟩ := c.natW.exists_isNatSecCoord fun ℓ hℓ x hx => conj_mem_pCoreOf_of_mem hℓ hx
  obtain ⟨zv, hzv⟩ := c.nat.exists_isNatSecCoord fun ℓ hℓ x hx =>
    mem_centerOf_conj_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hℓ) hx
  exact ⟨nv, zv, c.surj, pCoreOf_le 2 L2, c.center_le, c.le_pCoreOf,
    fun z hz a ha => mul_comm_of_mem_centerOf hz ha,
    fun a ha h => mem_centerOf_of_forall_comm ha h,
    fun a ha b hb => hD.special_right.commutator_le_centerOf
      (Subgroup.commutator_mem_commutator ha hb),
    fun w hw ℓ hℓ => c.commutator_le (Subgroup.commutator_mem_commutator hw hℓ), hnv, hzv⟩

private theorem natE_card_centerOf_left (hD : G2qLocalData L1 L2 S f) :
    Nat.card (centerOf (pCoreOf 2 L1)) = 2 ^ f := by
  rw [card_centerOf_eq_card_center, hD.special_left.2.2]

private theorem natE_card_E (hD : G2qLocalData L1 L2 S f) {F : Type} [Field F]
    (hF : Nat.card F = 2 ^ f) {E : Subgroup G} (hZE : centerOf (pCoreOf 2 L1) ≤ E)
    {β : ↥E →* Multiplicative (Fin 2 → F)} (hβs : Function.Surjective β)
    (hβk : β.ker = (centerOf (pCoreOf 2 L1)).subgroupOf E) : Nat.card E = 2 ^ (3 * f) := by
  have h := Subgroup.card_ker_mul_card_range β
  rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hβk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv, natE_card_centerOf_left hD] at h
  rw [← h]
  change 2 ^ f * Nat.card (Fin 2 → F) = _
  rw [Nat.card_fun, hF, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  ring

private theorem natE_exists_E (hD : G2qLocalData L1 L2 S f) (c₁ : G2qCoord L1 S f)
    [CharP c₁.F 2]
    (hquad : ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ pCoreOf 2 L1,
      ⁅s, ⁅s', x⁆⁆ ∈ centerOf (pCoreOf 2 L1))
    (hfix : ∀ x ∈ pCoreOf 2 L1, (∀ l ∈ L1, ⁅l, x⁆ ∈ centerOf (pCoreOf 2 L1)) →
      x ∈ centerOf (pCoreOf 2 L1)) {z₀ : G} (hz₀Q : z₀ ∈ pCoreOf 2 L1)
    (hz₀Z : z₀ ∉ centerOf (pCoreOf 2 L1))
    (hz₀S : ∀ s : ↥L1, c₁.α s ∈ utri c₁.F → ⁅(s : G), z₀⁆ ∈ centerOf (pCoreOf 2 L1)) :
    ∃ E : Subgroup G, centerOf (pCoreOf 2 L1) ≤ E ∧ E ≤ pCoreOf 2 L1 ∧ z₀ ∈ E ∧
      L1 ≤ Subgroup.normalizer (E : Set G) ∧ Nat.card E = 2 ^ (3 * f) ∧
      ∃ vE : G → Fin 2 → c₁.F, IsNatSecCoord L1 E (centerOf (pCoreOf 2 L1)) c₁.α vE ∧
        vE z₀ = ![1, 0] := by
  obtain ⟨E, hZE, hEQ, hz₀E, hEL, β, hβs, hβk, hβe, hβw⟩ :=
    exists_isNatSecOf_closure_of_quadratic c₁.α c₁.surj c₁.ker (pCoreOf_le 2 L1)
      (show centerOf (pCoreOf 2 L1) ≤ pCoreOf 2 L1 from inf_le_left)
      (le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L1))
      (Subgroup.commutator_le.mpr fun x hx y hy => hD.commutator_mem_centerOf_left hx hy) hfix
      (fun s s' hs hs' x hx => hquad s ((c₁.memS s).mpr hs) s' ((c₁.memS s').mpr hs') x hx)
      hz₀Q hz₀Z hz₀S
  refine ⟨E, hZE, hEQ, hz₀E, hEL, natE_card_E hD c₁.card hZE hβs hβk, natSecVec β,
    isNatSecCoord_natSecVec hβs hβk hβe fun l hl x hx =>
      (Subgroup.mem_normalizer_iff.mp (hEL hl) x).mp hx, ?_⟩
  rw [natSecVec_of_mem β hz₀E]
  exact hβw hz₀E

private theorem natE_conf (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) (c₁ : G2qCoord L1 S f)
    (hsplit : ⁅pCoreOf 2 L2, L2⁆ ⊓ c.W = centerOf (pCoreOf 2 L2))
    (hYS : ∀ s ∈ S, ∀ y ∈ ⁅pCoreOf 2 L2, L2⁆ ⊓ pCoreOf 2 L1,
      ⁅s, y⁆ ∈ centerOf (pCoreOf 2 L1)) {nv zv : G → Fin 2 → c.F}
    (hd : G2qSplitData L2 (pCoreOf 2 L2) (centerOf (pCoreOf 2 L2)) c.W c.α nv zv)
    (hZ1iff : ∀ z ∈ centerOf (pCoreOf 2 L2), z ∈ centerOf (pCoreOf 2 L1) ↔ zv z 1 = 0)
    {E : Subgroup G} {vE : G → Fin 2 → c₁.F}
    (hvE : IsNatSecCoord L1 E (centerOf (pCoreOf 2 L1)) c₁.α vE)
    (hZE : centerOf (pCoreOf 2 L1) ≤ E) (hEQ : E ≤ pCoreOf 2 L1) {z₀ : G}
    (hz₀Z : z₀ ∈ centerOf (pCoreOf 2 L2)) (hz₀E : z₀ ∈ E) (hz₀v : vE z₀ = ![1, 0]) :
    G2qNatEConf L1 L2 S (pCoreOf 2 L1) (pCoreOf 2 L2) (centerOf (pCoreOf 2 L1))
      (centerOf (pCoreOf 2 L2)) c.W E c₁.α c.α vE nv zv := by
  have hS1 : S ≤ L1 := hD.le_left hH (by omega) h1
  have hS2 : S ≤ L2 := hD.le_right hH (by omega) h2
  exact
    { split := hd
      natE := hvE
      surj_left := c₁.surj
      memS_left := c₁.memS
      memS_right := c.memS
      ker_right := c.ker
      le_left := hS1
      le_right := hS2
      core_left := hH.pCoreOf_le_left
      core_right := hH.pCoreOf_le_right
      conj_left := fun l hl x hx => conj_mem_pCoreOf_of_mem hl hx
      center_left := fun z hz l hl => by
        rw [hD.center_left] at hz
        exact mul_comm_of_mem_centerOf hz hl
      comm_left := fun x hx y hy => hD.commutator_mem_centerOf_left hx hy
      le_center := hD.centerOf_pCoreOf_left_le_right hH h1 h2
      W_le_left := c.W_le_pCoreOf_left hH hD h1 h2
      mem_left_iff := hZ1iff
      E_le := hEQ
      center_le_E := hZE
      exists_z₀ := ⟨z₀, hz₀Z, hz₀E, hz₀v⟩
      R_comm := c.commute_of_commutator_inf_W_eq hD hsplit
      R_inf_W := hsplit
      YS := hYS
      borel_left := fun b hb => by
        have hbB : (b : G) ∈ borelOf L1 S :=
          (mem_borelOf_iff_alpha_mem_borel hS1 c₁.α c₁.surj c₁.memS b).mpr hb
        exact ⟨hH.h2.borel_le hbB, normalizer_le_normalizer_pCoreOf 2 L2 (hH.h2.borel_le hbB)⟩
      borel_right := fun l hl => normalizer_le_normalizer_pCoreOf 2 L1
        (hH.h1.borel_le ((mem_borelOf_iff_alpha_mem_borel hS2 c.α c.surj c.memS l).mpr hl))
      card_eq := c₁.card.trans c.card.symm
      five_le := by
        rw [c.card]
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf }

theorem G2qCoordRight.false_of_split_of_fix (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f)
    (hsplit : ⁅pCoreOf 2 L2, L2⁆ ⊓ c.W = centerOf (pCoreOf 2 L2))
    (hYS : ∀ s ∈ S, ∀ y ∈ ⁅pCoreOf 2 L2, L2⁆ ⊓ pCoreOf 2 L1,
      ⁅s, y⁆ ∈ centerOf (pCoreOf 2 L1))
    (hquad : ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ pCoreOf 2 L1,
      ⁅s, ⁅s', x⁆⁆ ∈ centerOf (pCoreOf 2 L1))
    (hfix : ∀ x ∈ pCoreOf 2 L1, (∀ l ∈ L1, ⁅l, x⁆ ∈ centerOf (pCoreOf 2 L1)) →
      x ∈ centerOf (pCoreOf 2 L1)) :
    False := by
  classical
  obtain ⟨c₁⟩ := hD.exists_coordLeft hH h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP c.F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c.card])
  haveI : CharP c₁.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  have hS1 : S ≤ L1 := hD.le_left hH (by omega) h1
  have hS2 : S ≤ L2 := hD.le_right hH (by omega) h2
  obtain ⟨nv, zv, hd⟩ := natE_exists_splitData hD c
  have hZ1iff : ∀ z ∈ centerOf (pCoreOf 2 L2), z ∈ centerOf (pCoreOf 2 L1) ↔ zv z 1 = 0 :=
    fun z hz => natE_mem_iff_apply_one_eq_zero hd.nat c.surj c.memS
      (hD.centerOf_pCoreOf_left_le_right hH h1 h2)
      (fun z hz s hs => by
        rw [hD.center_left] at hz
        exact mul_comm_of_mem_centerOf hz (hS1 hs))
      (by rw [natE_card_centerOf_left hD, c.card]) hz
  obtain ⟨z₀, hz₀Z, hz₀v⟩ := hd.nat.surj ![0, 1]
  have hz₀Z1 : z₀ ∉ centerOf (pCoreOf 2 L1) := fun h => by
    have h' := (hZ1iff z₀ hz₀Z).mp h
    rw [hz₀v] at h'
    simp at h'
  have hz₀S : ∀ s : ↥L1, c₁.α s ∈ utri c₁.F → ⁅(s : G), z₀⁆ ∈ centerOf (pCoreOf 2 L1) := by
    intro s hs
    have hsS : (s : G) ∈ S := (c₁.memS s).mpr hs
    exact (hZ1iff _ (hd.nat.commutator_left_mem ⟨s, hS2 hsS⟩ hz₀Z)).mpr
      (hd.nat.map_commutator_left_apply_one ((c.memS ⟨s, hS2 hsS⟩).mp hsS) hz₀Z)
  obtain ⟨E, hZE, hEQ, hz₀E, hEL, hcardE, vE, hvE, hz₀vE⟩ := natE_exists_E hD c₁ hquad hfix
    (hD.centerOf_pCoreOf_right_le_left hH h1 h2 hz₀Z) hz₀Z1 hz₀S
  have hC := natE_conf hf hH hD h1 h2 c c₁ hsplit hYS hd hZ1iff hvE hZE hEQ hz₀Z hz₀E hz₀vE
  have hEeq : E = c.W := Subgroup.eq_of_le_of_card_ge (hC.E_le_W hC.E_le_core_right)
    (by rw [c.card_W, hcardE])
  exact c.false_of_le_normalizer_W hH (hEeq ▸ hEL)

end CFSG.Quasithin.F112R.St84

end
