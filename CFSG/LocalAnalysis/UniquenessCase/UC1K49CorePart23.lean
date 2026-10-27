module

import all CFSG.LocalAnalysis.UniquenessCase.UC1K49Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CorePart1
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Core334
public import CFSG.GroupTheory.SteinbergCBFTSCN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma KI_le_I49 (X I : Subgroup G) : KI X I ≤ I := by
  rw [KI]
  exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_right

local instance instDecidablePredMemCore : DecidablePred (· ∈ G6.coreMod 5) :=
  fun x => decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) G6.mem_coreMod.symm

def bv (k : Fin 4) : G6.coreMod 5 :=
  ⟨Multiplicative.ofAdd (fun i => if i = k.castSucc ∨ i = 4 then (1 : ZMod 2) else 0), by
    rw [G6.mem_coreMod]
    revert k
    decide⟩

def crd5 (w : G6.coreMod 5) (k : Fin 4) : ZMod 2 :=
  Multiplicative.toAdd (w : G6.PermMod 5) k.castSucc

def pact (σ : Equiv.Perm (Fin 5)) (x : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  fun i => x (σ⁻¹ i)

def pairV (a b : Fin 5) : Fin 5 → ZMod 2 := Pi.single a 1 + Pi.single b 1

private def PairVEven (a b : Fin 5) : Prop := a ≠ b → (∑ i, pairV a b i) = 0

private instance instDecidablePairVEven (a b : Fin 5) : Decidable (PairVEven a b) := by
  unfold PairVEven
  infer_instance

private def PairVTransitive (a b c d : Fin 5) : Prop :=
  a ≠ b → c ≠ d → ∃ (σ : Equiv.Perm (Fin 5)),
    Equiv.Perm.sign σ = 1 ∧ pact σ (pairV a b) = pairV c d

private instance instDecidablePairVTransitive (a b c d : Fin 5) :
    Decidable (PairVTransitive a b c d) := by
  unfold PairVTransitive
  infer_instance

theorem pairV_transitive : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    ∃ (σ : Equiv.Perm (Fin 5)), Equiv.Perm.sign σ = 1 ∧ pact σ (pairV a b) = pairV c d := by
  change ∀ a b c d : Fin 5, PairVTransitive a b c d
  decide +kernel

private def IsPairVec (x : Fin 5 → ZMod 2) : Prop :=
  ∃ a b : Fin 5, a ≠ b ∧ x = pairV a b

private instance instDecidableIsPairVec (x : Fin 5 → ZMod 2) : Decidable (IsPairVec x) := by
  unfold IsPairVec
  infer_instance

private def IsPairVecAfterPerm (x : Fin 5 → ZMod 2) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 5)) (a b : Fin 5), Equiv.Perm.sign σ = 1 ∧ a ≠ b ∧
    x + pact σ x = pairV a b

private instance instDecidableIsPairVecAfterPerm (x : Fin 5 → ZMod 2) :
    Decidable (IsPairVecAfterPerm x) := by
  unfold IsPairVecAfterPerm
  infer_instance

private def PairReducible (x : Fin 5 → ZMod 2) : Prop := IsPairVec x ∨ IsPairVecAfterPerm x

private instance instDecidablePairReducible (x : Fin 5 → ZMod 2) :
    Decidable (PairReducible x) := by
  unfold PairReducible
  infer_instance

theorem reduce_to_pairV : ∀ x : Fin 5 → ZMod 2, (∑ i, x i) = 0 → x ≠ 0 →
    (∃ a b : Fin 5, a ≠ b ∧ x = pairV a b) ∨
    (∃ (σ : Equiv.Perm (Fin 5)) (a b : Fin 5), Equiv.Perm.sign σ = 1 ∧ a ≠ b ∧
      x + pact σ x = pairV a b) := by
  change ∀ x : Fin 5 → ZMod 2, (∑ i, x i) = 0 → x ≠ 0 → PairReducible x
  decide +kernel

theorem toAdd_bv (k : Fin 4) :
    Multiplicative.toAdd ((bv k : G6.coreMod 5) : G6.PermMod 5) = pairV k.castSucc 4 := by
  funext i
  fin_cases i <;> fin_cases k <;> rfl

private def BvBasis (w : G6.coreMod 5) : Prop := ∏ k : Fin 4, bv k ^ (crd5 w k).val = w

private instance instDecidableBvBasis (w : G6.coreMod 5) : Decidable (BvBasis w) := by
  unfold BvBasis
  infer_instance

theorem bv_basis5 : ∀ w : G6.coreMod 5, ∏ k : Fin 4, bv k ^ (crd5 w k).val = w := by
  change ∀ w : G6.coreMod 5, BvBasis w
  decide +kernel

theorem toAdd_coreAct (σ : Equiv.Perm (Fin 5)) (w : G6.coreMod 5) :
    Multiplicative.toAdd ((G6.coreAct 5 σ w : G6.coreMod 5) : G6.PermMod 5) =
      pact σ (Multiplicative.toAdd (w : G6.PermMod 5)) := by
  funext i
  rw [pact, G6.coreAct_coe, G6.permAct_apply]

private theorem exists_pairV_of_alt_invariant_ne_bot (W : Subgroup (G6.coreMod 5))
    (hW : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
      ∀ w ∈ W, G6.coreAct 5 σ w ∈ W) (hne : W ≠ ⊥) :
    ∃ (a b : Fin 5), a ≠ b ∧ ∃ y ∈ W,
      Multiplicative.toAdd ((y : G6.coreMod 5) : G6.PermMod 5) = pairV a b := by
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall W).2 h)
  let x : Fin 5 → ZMod 2 := Multiplicative.toAdd ((w : G6.coreMod 5) : G6.PermMod 5)
  have hxeven : ∑ i, x i = 0 := G6.mem_coreMod.mp (w : G6.coreMod 5).2
  have hxne : x ≠ 0 := by
    intro h0
    apply hw1
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd ((w : G6.coreMod 5) : G6.PermMod 5) =
      Multiplicative.toAdd (1 : G6.PermMod 5)
    rw [toAdd_one]
    exact h0
  rcases reduce_to_pairV x hxeven hxne with ⟨a, b, hab, hxab⟩ | ⟨σ, a, b, hσ, hab, hxσ⟩
  · exact ⟨a, b, hab, w, hwW, hxab⟩
  · refine ⟨a, b, hab, w * G6.coreAct 5 σ w,
      W.mul_mem hwW (hW σ hσ w hwW), ?_⟩
    change Multiplicative.toAdd (((w : G6.coreMod 5) : G6.PermMod 5) *
      (((G6.coreAct 5 σ w : G6.coreMod 5)) : G6.PermMod 5)) = pairV a b
    rw [toAdd_mul, toAdd_coreAct]
    exact hxσ

private theorem bv_mem_of_alt_invariant_of_pairV (W : Subgroup (G6.coreMod 5))
    (hW : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
      ∀ w ∈ W, G6.coreAct 5 σ w ∈ W)
    {a b : Fin 5} (hab : a ≠ b) {y : G6.coreMod 5} (hyW : y ∈ W)
    (hy : Multiplicative.toAdd ((y : G6.coreMod 5) : G6.PermMod 5) = pairV a b) :
    ∀ k : Fin 4, bv k ∈ W := by
  have hbv0 : bv 0 ∈ W := by
    obtain ⟨τ, hτ, hτab⟩ := pairV_transitive a b (0 : Fin 4).castSucc 4 hab (by decide)
    have hmem : G6.coreAct 5 τ y ∈ W := hW τ hτ y hyW
    have hto : Multiplicative.toAdd
        (((G6.coreAct 5 τ y : G6.coreMod 5)) : G6.PermMod 5) =
        pairV (0 : Fin 4).castSucc 4 := by
      rw [toAdd_coreAct, hy, hτab]
    have heq : (G6.coreAct 5 τ y : G6.coreMod 5) = bv 0 := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [hto, toAdd_bv]
    rwa [← heq]
  intro k
  have hk4 : k.castSucc ≠ (4 : Fin 5) := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_castSucc] at this
    omega
  obtain ⟨σ, hσ, hσk⟩ := pairV_transitive (0 : Fin 4).castSucc 4 k.castSucc 4
    (by decide) hk4
  have hmem : G6.coreAct 5 σ (bv 0) ∈ W := hW σ hσ (bv 0) hbv0
  have hto : Multiplicative.toAdd
      (((G6.coreAct 5 σ (bv 0) : G6.coreMod 5)) : G6.PermMod 5) =
      Multiplicative.toAdd ((bv k : G6.coreMod 5) : G6.PermMod 5) := by
    rw [toAdd_coreAct, toAdd_bv, toAdd_bv, hσk]
  have heq : (G6.coreAct 5 σ (bv 0) : G6.coreMod 5) = bv k := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact hto
  rwa [← heq]

theorem coreMod5_alt_invariant_eq_bot_or_top (W : Subgroup (G6.coreMod 5))
    (hW : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
      ∀ w ∈ W, G6.coreAct 5 σ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨a, b, hab, y, hyW, hy⟩ := exists_pairV_of_alt_invariant_ne_bot W hW hbot
  have hbv : ∀ k : Fin 4, bv k ∈ W := bv_mem_of_alt_invariant_of_pairV W hW hab hyW hy
  refine (Subgroup.eq_top_iff' W).2 fun w' => ?_
  have hprod : (∏ k : Fin 4, bv k ^ (crd5 w' k).val) ∈ W :=
    Finset.prod_induction (fun k : Fin 4 => bv k ^ (crd5 w' k).val) (· ∈ W)
      (fun a b ha hb => W.mul_mem ha hb) W.one_mem (fun k _ => W.pow_mem (hbv k) _)
  rw [bv_basis5 w'] at hprod
  exact hprod

theorem NatA5Sec_eq_bot_or_eq_top {D N₀ N₁ M : Subgroup G} (hnat : NatA5Sec D N₀ N₁)
    (h1M : N₁ ≤ M) (hM0 : M ≤ N₀) (hDM : D ≤ Subgroup.normalizer (M : Set G)) :
    M = N₁ ∨ M = N₀ := by
  obtain ⟨φ, ψ, hφs, hψs, hψk, hψe⟩ := hnat
  let W : Subgroup (G6.coreMod 5) := (M.subgroupOf N₀).map ψ
  have hWinv : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
      ∀ z ∈ W, G6.coreAct 5 σ z ∈ W := by
    intro σ hσ z hz
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨d, hφd⟩ := hφs ⟨σ, hσ⟩
    have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    obtain ⟨hconj, -⟩ := (Subgroup.mem_normalizer_iff.mp (hDM d.2) (m : G))
    have hconjM : (d : G) * (m : G) * (d : G)⁻¹ ∈ M := (hconj hmM)
    let n' : ↥N₀ := ⟨(d : G) * (m : G) * (d : G)⁻¹, hM0 hconjM⟩
    have hn'm : n' ∈ M.subgroupOf N₀ := Subgroup.mem_subgroupOf.mpr hconjM
    refine Subgroup.mem_map.mpr ⟨n', hn'm, ?_⟩
    rw [hψe d m n' rfl, congrArg Subtype.val hφd]
  rcases coreMod5_alt_invariant_eq_bot_or_top W hWinv with hWbot | hWtop
  · left
    refine le_antisymm ?_ h1M
    intro m hm
    have hmm : (⟨m, hM0 hm⟩ : ↥N₀) ∈ M.subgroupOf N₀ := Subgroup.mem_subgroupOf.mpr hm
    have hψm : ψ ⟨m, hM0 hm⟩ ∈ W := Subgroup.mem_map.mpr ⟨_, hmm, rfl⟩
    rw [hWbot, Subgroup.mem_bot] at hψm
    have hker : (⟨m, hM0 hm⟩ : ↥N₀) ∈ ψ.ker := MonoidHom.mem_ker.mpr hψm
    rw [hψk] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  · right
    refine le_antisymm hM0 ?_
    intro n hn
    have hmemW : ψ ⟨n, hn⟩ ∈ W := by rw [hWtop]; exact Subgroup.mem_top _
    obtain ⟨p, hp, hpn⟩ := Subgroup.mem_map.mp hmemW
    have hpM : (p : G) ∈ M := Subgroup.mem_subgroupOf.mp hp
    have hker : p⁻¹ * ⟨n, hn⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpn, inv_mul_cancel]
    rw [hψk] at hker
    have hN1 : ((p⁻¹ * ⟨n, hn⟩ : ↥N₀) : G) ∈ N₁ := Subgroup.mem_subgroupOf.mp hker
    have hnM : (n : G) = (p : G) * ((p⁻¹ * ⟨n, hn⟩ : ↥N₀) : G) := by
      simp [mul_assoc]
    rw [hnM]
    exact M.mul_mem hpM (h1M hN1)

theorem centralizer_sup_eq (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun b hb => h b (Or.inr hb)⟩
  · rintro ⟨ha, hb⟩ y (hyA | hyB)
    · exact ha y hyA
    · exact hb y hyB

theorem I_eq_sup_conjugates {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hxgen : X = Subgroup.zpowers x) :
    I = Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2 := by
  have hord : orderOf x = 3 := by
    have hc := Nat.card_zpowers x
    rw [← hxgen] at hc
    rw [h.card_X] at hc
    exact hc.symm
  rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun y => ?_
    have hy : (y : G) ∈ Subgroup.zpowers x := hxgen ▸ y.2
    rcases zpowers_eq_triple hord hy with h1 | h1 | h1
    · have hy1 : CFSG.conjugate L (y : G) = Lc L x 0 := by rw [h1, Lc, pow_zero]
      rw [hy1]; exact le_sup_left.trans le_sup_left
    · have hy1 : CFSG.conjugate L (y : G) = Lc L x 1 := by rw [h1, Lc, pow_one]
      rw [hy1]; exact le_sup_right.trans le_sup_left
    · have hy1 : CFSG.conjugate L (y : G) = Lc L x 2 := by rw [h1, Lc]
      rw [hy1]; exact le_sup_right
  · refine sup_le (sup_le ?_ ?_) ?_
    · show Lc L x 0 ≤ _
      rw [Lc, pow_zero]
      exact le_iSup (fun y : X => CFSG.conjugate L (y : G)) ⟨1, X.one_mem⟩
    · show Lc L x 1 ≤ _
      rw [Lc, pow_one]
      exact le_iSup (fun y : X => CFSG.conjugate L (y : G)) ⟨x, hxX⟩
    · show Lc L x 2 ≤ _
      exact le_iSup (fun y : X => CFSG.conjugate L (y : G)) ⟨x ^ 2, X.pow_mem hxX 2⟩

private theorem k334_local_commutator_facts {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) {i : ℕ} {N0 N1 : Subgroup G}
    (hN1N0 : N1 ≤ N0) (hN0Q : N0 ≤ Q) (hHN0 : H ≤ Subgroup.normalizer (N0 : Set G))
    (hHN1 : H ≤ Subgroup.normalizer (N1 : Set G)) (hN1I : ⁅N1, I⁆ = ⊥)
    (hN0QN1 : ⁅N0, Q⁆ ≤ N1) :
    Lc L x i ≤ Subgroup.normalizer (Q : Set G) ∧
    Lc L x i ⊔ Q ≤ Subgroup.normalizer ((⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G) : Set G) ∧
    Lc L x i ⊔ Q ≤ Subgroup.normalizer (N1 : Set G) ∧
    ⁅Lc L x i, N1⁆ = ⊥ ∧
    (⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G) ≤ Q ∧
    ⁅(⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G), Q⁆ ≤ N1 := by
  have hxiX : x ^ i ∈ X := X.pow_mem hxX i
  have hD_le_H : Lc L x i ≤ H := (conjugate_le_I h hxiX).trans (I_le_H h)
  have hDmem := (struct49 h).2.2.2.2.1 (x ^ i) hxiX
  have hQN : Q ≤ Subgroup.normalizer (Lc L x i : Set G) := hDmem.2.2.1
  have hQH : Q ≤ H := h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hQnormH : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hDQ : Lc L x i ≤ Subgroup.normalizer (Q : Set G) := hD_le_H.trans hQnormH
  have hDVnorm : Lc L x i ≤
      Subgroup.normalizer ((⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G) : Set G) :=
    (le_inf (Subgroup.normalizer_commutator_ge_right N0 (Lc L x i))
      (hD_le_H.trans hHN1)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hQVnorm : Q ≤ Subgroup.normalizer ((⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G) : Set G) :=
    (le_inf (CFSG.GroupTheory.FT63ChII.le_normalizer_commutator
      (hQH.trans hHN0) hQN) (hQH.trans hHN1)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have h0 : Lc L x i ⊔ Q ≤ Subgroup.normalizer ((⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G) : Set G) :=
    sup_le hDVnorm hQVnorm
  have h1 : Lc L x i ⊔ Q ≤ Subgroup.normalizer (N1 : Set G) :=
    sup_le (hD_le_H.trans hHN1) (hQH.trans hHN1)
  have hD1 : ⁅Lc L x i, N1⁆ = ⊥ := by
    have hle : ⁅Lc L x i, N1⁆ ≤ ⁅I, N1⁆ :=
      Subgroup.commutator_mono (conjugate_le_I h hxiX) le_rfl
    rw [Subgroup.commutator_comm I N1, hN1I] at hle
    exact le_bot_iff.mp hle
  have hVleN0 : (⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G) ≤ N0 :=
    sup_le (CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer
      (hD_le_H.trans hHN0)) hN1N0
  have hN0QV : ⁅(⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G), Q⁆ ≤ N1 :=
    (Subgroup.commutator_mono hVleN0 le_rfl).trans hN0QN1
  exact ⟨hDQ, h0, h1, hD1, hVleN0.trans hN0Q, hN0QV⟩

theorem k334_local {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G} (hxX : x ∈ X)
    {i : ℕ} (hi : i < 3) {N0 N1 : Subgroup G}
    (hN1N0 : N1 ≤ N0) (hN0Q : N0 ≤ Q) (hHN0 : H ≤ Subgroup.normalizer (N0 : Set G))
    (hHN1 : H ≤ Subgroup.normalizer (N1 : Set G)) (hN1I : ⁅N1, I⁆ = ⊥)
    (hN0QN1 : ⁅N0, Q⁆ ≤ N1) (hQi : ⁅Q, Lc L x i⁆ ≤ ⁅N0, Lc L x i⁆ ⊔ N1)
    (hnat : NatA5Sec (Lc L x i) (⁅N0, Lc L x i⁆ ⊔ N1) N1) :
    Q = ⁅Q, Lc L x i⁆ ⊔ (Q ⊓ Subgroup.centralizer (Lc L x i : Set G)) ∧
    ⁅⁅Q, Lc L x i⁆, Q ⊓ Subgroup.centralizer (Lc L x i : Set G)⁆ = ⊥ ∧
    ⁅Q, Lc L x i⁆ ⊓ N1 =
      CFSG.ComponentClassification.AschbacherTheorem3.frattiniOf ⁅Q, Lc L x i⁆ ∧
    ⁅Q, Lc L x i⁆ ⊔ N1 = ⁅N0, Lc L x i⁆ ⊔ N1 := by
  have hxiX : x ^ i ∈ X := X.pow_mem hxX i
  have hDmem := (struct49 h).2.2.2.2.1 (x ^ i) hxiX
  have hD5 : IsAlt (Bar2 (Lc L x i)) 5 := hDmem.2.1
  have hQN : Q ≤ Subgroup.normalizer (Lc L x i : Set G) := hDmem.2.2.1
  have hDQ2 : Lc L x i ⊓ Q = CFSG.Open.pCoreOf 2 (Lc L x i) := hDmem.2.2.2
  have hperf : ⁅Lc L x i, Lc L x i⁆ = Lc L x i :=
    CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn hDmem.1
  have hQ2 : IsPGroup 2 Q := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  obtain ⟨hDQ, h0, h1, hD1, hVleQ, hN0QV⟩ :=
    k334_local_commutator_facts (i := i) (N0 := N0) (N1 := N1) h hxX
      hN1N0 hN0Q hHN0 hHN1 hN1I hN0QN1
  obtain ⟨hQeq, hSC, hSN1, hSV⟩ := k334 hQ2 hDQ hQN hperf hD5 hDQ2
    (le_sup_right : N1 ≤ (⁅N0, Lc L x i⁆ ⊔ N1 : Subgroup G)) hVleQ h0 h1 hD1 hQi hN0QV hnat
  exact ⟨hQeq, hSC, hSN1, hSV⟩

private theorem commutator_le_normalizer_inf_centralizer (Q A : Subgroup G)
    (h : ⁅⁅Q, A⁆, Q ⊓ Subgroup.centralizer (A : Set G)⁆ = ⊥) :
    ⁅Q, A⁆ ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (A : Set G)) : Set G) :=
  (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans (Subgroup.centralizer_le_normalizer _)

private theorem part2_decompose_initial_conjugates {Q L0 L1 : Subgroup G} {q : G}
    (hl0 : Q = ⁅Q, L0⁆ ⊔ (Q ⊓ Subgroup.centralizer (L0 : Set G)))
    (hl1 : Q = ⁅Q, L1⁆ ⊔ (Q ⊓ Subgroup.centralizer (L1 : Set G)))
    (hn0 : ⁅Q, L0⁆ ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L0 : Set G)) : Set G))
    (hn1 : ⁅Q, L1⁆ ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L1 : Set G)) : Set G))
    (hc : ⁅Q, L1⁆ ≤ Subgroup.centralizer (L0 : Set G)) (hq : q ∈ Q) :
    ∃ s0 s1 c1 : G, s0 ∈ ⁅Q, L0⁆ ∧ s1 ∈ ⁅Q, L1⁆ ∧ c1 ∈ Q ∧
      c1 ∈ Subgroup.centralizer (L0 : Set G) ∧ c1 ∈ Subgroup.centralizer (L1 : Set G) ∧
      q = (s0 * s1) * c1 := by
  have hq0 : q ∈ ⁅Q, L0⁆ ⊔ (Q ⊓ Subgroup.centralizer (L0 : Set G)) := by
    rw [← hl0]; exact hq
  obtain ⟨s0, hs0, c0, hc0, h0eq⟩ := (mem_sup_of_le_normalizer hn0).mp hq0
  have hc0Q : c0 ∈ Q := hc0.1
  have hc0Q' : c0 ∈ ⁅Q, L1⁆ ⊔ (Q ⊓ Subgroup.centralizer (L1 : Set G)) := by
    rw [← hl1]; exact hc0Q
  obtain ⟨s1, hs1, c1, hc1, h1eq⟩ := (mem_sup_of_le_normalizer hn1).mp hc0Q'
  have hc1C0 : c1 ∈ Subgroup.centralizer (L0 : Set G) := by
    have h1 : s1⁻¹ * c0 ∈ Subgroup.centralizer (L0 : Set G) :=
      (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem (hc hs1)) hc0.2
    rwa [← h1eq, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact ⟨s0, s1, c1, hs0, hs1, hc1.1, hc1C0, hc1.2, by rw [← h0eq, ← h1eq]; group⟩

private theorem part2_decompose_final_conjugate {Q L0 L1 L2 : Subgroup G} {c1 : G}
    (hl2 : Q = ⁅Q, L2⁆ ⊔ (Q ⊓ Subgroup.centralizer (L2 : Set G)))
    (hn2 : ⁅Q, L2⁆ ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L2 : Set G)) : Set G))
    (hc0 : ⁅Q, L2⁆ ≤ Subgroup.centralizer (L0 : Set G))
    (hc1 : ⁅Q, L2⁆ ≤ Subgroup.centralizer (L1 : Set G))
    (hc1Q : c1 ∈ Q) (hc1C0 : c1 ∈ Subgroup.centralizer (L0 : Set G))
    (hc1C1 : c1 ∈ Subgroup.centralizer (L1 : Set G)) :
    ∃ s2 c2 : G, s2 ∈ ⁅Q, L2⁆ ∧ c2 ∈ Q ∧
      c2 ∈ Subgroup.centralizer (L0 : Set G) ∧ c2 ∈ Subgroup.centralizer (L1 : Set G) ∧
      c2 ∈ Subgroup.centralizer (L2 : Set G) ∧ c1 = s2 * c2 := by
  have hc1Q' : c1 ∈ ⁅Q, L2⁆ ⊔ (Q ⊓ Subgroup.centralizer (L2 : Set G)) := by
    rw [← hl2]; exact hc1Q
  obtain ⟨s2, hs2, c2, hc2, h2eq⟩ := (mem_sup_of_le_normalizer hn2).mp hc1Q'
  have hc2C0 : c2 ∈ Subgroup.centralizer (L0 : Set G) := by
    have h1 : s2⁻¹ * c1 ∈ Subgroup.centralizer (L0 : Set G) :=
      (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem (hc0 hs2)) hc1C0
    rwa [← h2eq, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  have hc2C1 : c2 ∈ Subgroup.centralizer (L1 : Set G) := by
    have h1 : s2⁻¹ * c1 ∈ Subgroup.centralizer (L1 : Set G) :=
      (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem (hc1 hs2)) hc1C1
    rwa [← h2eq, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact ⟨s2, c2, hs2, hc2.1, hc2C0, hc2C1, hc2.2, h2eq.symm⟩

private theorem part2_le_sup_centralizer {Q I L : Subgroup G} {x : G}
    (hSle : ∀ i : ℕ, i < 3 → ⁅Q, Lc L x i⁆ ≤ ⁅Q, I⁆)
    (hn0 : ⁅Q, Lc L x 0⁆ ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Lc L x 0 : Set G)) : Set G))
    (hn1 : ⁅Q, Lc L x 1⁆ ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Lc L x 1 : Set G)) : Set G))
    (hn2 : ⁅Q, Lc L x 2⁆ ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Lc L x 2 : Set G)) : Set G))
    (hS1C0 : ⁅Q, Lc L x 1⁆ ≤ Subgroup.centralizer (Lc L x 0 : Set G))
    (hS2C0 : ⁅Q, Lc L x 2⁆ ≤ Subgroup.centralizer (Lc L x 0 : Set G))
    (hS2C1 : ⁅Q, Lc L x 2⁆ ≤ Subgroup.centralizer (Lc L x 1 : Set G))
    (hIeq : I = Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2)
    (hl0 : Q = ⁅Q, Lc L x 0⁆ ⊔ (Q ⊓ Subgroup.centralizer (Lc L x 0 : Set G)))
    (hl1 : Q = ⁅Q, Lc L x 1⁆ ⊔ (Q ⊓ Subgroup.centralizer (Lc L x 1 : Set G)))
    (hl2 : Q = ⁅Q, Lc L x 2⁆ ⊔ (Q ⊓ Subgroup.centralizer (Lc L x 2 : Set G))) :
    Q ≤ ⁅Q, I⁆ ⊔ (Q ⊓ Subgroup.centralizer (I : Set G)) := by
  intro q hq
  obtain ⟨s0, s1, c1, hs0, hs1, hc1Q, hc1C0, hc1C1, hqeq⟩ :=
    part2_decompose_initial_conjugates (L0 := Lc L x 0) (L1 := Lc L x 1) (q := q)
      hl0 hl1 hn0 hn1 hS1C0 hq
  obtain ⟨s2, c2, hs2, hc2Q, hc2C0, hc2C1, hc2C2, hc1eq⟩ :=
    part2_decompose_final_conjugate (L0 := Lc L x 0) (L1 := Lc L x 1) (L2 := Lc L x 2)
      hl2 hn2 hS2C0 hS2C1 hc1Q hc1C0 hc1C1
  have hc2CI : c2 ∈ Subgroup.centralizer (I : Set G) := by
    rw [hIeq, centralizer_sup_eq, centralizer_sup_eq]
    exact ⟨⟨hc2C0, hc2C1⟩, hc2C2⟩
  have hc2mem : c2 ∈ Q ⊓ Subgroup.centralizer (I : Set G) := ⟨hc2Q, hc2CI⟩
  have hs012 : s0 * (s1 * s2) ∈ ⁅Q, I⁆ :=
    (⁅Q, I⁆).mul_mem (hSle 0 (by norm_num) hs0)
      ((⁅Q, I⁆).mul_mem (hSle 1 (by norm_num) hs1) (hSle 2 (by norm_num) hs2))
  have hqeq' : q = (s0 * (s1 * s2)) * c2 := by
    rw [hqeq, hc1eq]; group
  rw [hqeq']
  exact Subgroup.mul_mem_sup hs012 hc2mem

private theorem part2_distinct_commutator_eq_bot {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {x : G} (hxX : x ∈ X) {N0 N1 : Subgroup G} (hN1I : ⁅N1, I⁆ = ⊥)
    (hVcommall : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j →
      ⁅⁅N0, Lc L x i⁆ ⊔ N1, Lc L x j⁆ ≤ N1)
    (hQi : ∀ i : ℕ, i < 3 → ⁅Q, Lc L x i⁆ ≤ ⁅N0, Lc L x i⁆ ⊔ N1) :
    ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅⁅Q, Lc L x i⁆, Lc L x j⁆ = ⊥ := by
  intro i j hi hj hij
  have hDj := (struct49 h).2.2.2.2.1 (x ^ j) (X.pow_mem hxX j)
  refine CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step
    (D := Lc L x j) (Y := ⁅Q, Lc L x i⁆) (Y₁ := N1) ?_ ?_ ?_
  · exact CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn hDj.1
  · exact (Subgroup.commutator_mono (hQi i hi) le_rfl).trans (hVcommall i j hi hj hij)
  · have hle : ⁅N1, Lc L x j⁆ ≤ ⁅N1, I⁆ :=
      Subgroup.commutator_mono le_rfl (conjugate_le_I h (X.pow_mem hxX j))
    rw [hN1I] at hle
    exact le_bot_iff.mp hle

private theorem part2_commutator_le_centralizer_conjugates {Q L : Subgroup G} {x : G}
    (hcomm : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅⁅Q, Lc L x i⁆, Lc L x j⁆ = ⊥) :
    ⁅Q, Lc L x 1⁆ ≤ Subgroup.centralizer (Lc L x 0 : Set G) ∧
    ⁅Q, Lc L x 2⁆ ≤ Subgroup.centralizer (Lc L x 0 : Set G) ∧
    ⁅Q, Lc L x 2⁆ ≤ Subgroup.centralizer (Lc L x 1 : Set G) :=
  ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hcomm 1 0 (by norm_num) (by norm_num) (by norm_num)),
   Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hcomm 2 0 (by norm_num) (by norm_num) (by norm_num)),
   Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hcomm 2 1 (by norm_num) (by norm_num) (by norm_num))⟩

theorem part2_49 (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    (hK : KI49 X I) : Part2_49 Q I := by
  obtain ⟨x, hxX, hxgen, -, -, -⟩ := exists_generator49 h
  obtain ⟨N0, N1, hN1N0, hN0Q, hHN0, hHN1, hN1I, hQIN0, hN0QN1, hshape⟩ :=
    propM49 hI h hxgen hK
  let V : ℕ → Subgroup G := fun i => ⁅N0, Lc L x i⁆ ⊔ N1
  have hVeq : ∀ i, V i = ⁅N0, Lc L x i⁆ ⊔ N1 := fun i => rfl
  obtain ⟨-, -, hVcommall, hVnatall⟩ := hshape V hVeq
  have hl0 := k334_local h hxX (by norm_num) hN1N0 hN0Q hHN0 hHN1 hN1I hN0QN1
    (hVnatall 0 (by norm_num)).1 (hVnatall 0 (by norm_num)).2
  have hl1 := k334_local h hxX (by norm_num) hN1N0 hN0Q hHN0 hHN1 hN1I hN0QN1
    (hVnatall 1 (by norm_num)).1 (hVnatall 1 (by norm_num)).2
  have hl2 := k334_local h hxX (by norm_num) hN1N0 hN0Q hHN0 hHN1 hN1I hN0QN1
    (hVnatall 2 (by norm_num)).1 (hVnatall 2 (by norm_num)).2
  have hIeq := I_eq_sup_conjugates h hxX hxgen
  have hcomm := part2_distinct_commutator_eq_bot h hxX hN1I hVcommall
    (fun i hi => (hVnatall i hi).1)
  have hSle : ∀ i : ℕ, i < 3 → ⁅Q, Lc L x i⁆ ≤ ⁅Q, I⁆ := fun i _ =>
    Subgroup.commutator_mono le_rfl (conjugate_le_I h (X.pow_mem hxX i))
  obtain ⟨hS1C0, hS2C0, hS2C1⟩ := part2_commutator_le_centralizer_conjugates hcomm
  have hn0 := commutator_le_normalizer_inf_centralizer Q (Lc L x 0) hl0.2.1
  have hn1 := commutator_le_normalizer_inf_centralizer Q (Lc L x 1) hl1.2.1
  have hn2 := commutator_le_normalizer_inf_centralizer Q (Lc L x 2) hl2.2.1
  have hQle := part2_le_sup_centralizer hSle hn0 hn1 hn2 hS1C0 hS2C0 hS2C1 hIeq
    hl0.1 hl1.1 hl2.1
  have hQnorm : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQH : Q ≤ H := h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hsupcomm : ⁅Q, I⁆ ⊔ (Q ⊓ Subgroup.centralizer (I : Set G)) =
      (Q ⊓ Subgroup.centralizer (I : Set G)) ⊔ ⁅Q, I⁆ := sup_comm _ _
  refine ⟨le_antisymm (hQle.trans (le_of_eq hsupcomm))
    (sup_le inf_le_left (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((I_le_H h).trans hQnorm))), ?_⟩
  have hle : ⁅Q ⊓ Subgroup.centralizer (I : Set G), ⁅Q, I⁆⁆ ≤
      ⁅Subgroup.centralizer (I : Set G), I⁆ :=
    Subgroup.commutator_mono inf_le_right
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (hQH.trans (le_normalizer_I h)))
  have hbot : ⁅Subgroup.centralizer (I : Set G), I⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
  rw [hbot] at hle
  exact le_bot_iff.mp hle

theorem le_normalizer_omegaOne_of_le_normalizer {N H : Subgroup G}
    (hNnorm : H ≤ Subgroup.normalizer (N : Set G)) :
    H ≤ Subgroup.normalizer (CFSG.RankThree.PartOne.omegaOne 2 N : Set G) := by
  intro g hg
  refine CFSG.RankThree.PartTwo.Sec18.Item18ResProof.mem_normalizer_of_map_conj_le ?_
  rw [show CFSG.RankThree.PartOne.omegaOne 2 N =
      Subgroup.closure {x : G | x ∈ N ∧ x ^ 2 = 1} from rfl, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro y ⟨x, ⟨hxN, hx2⟩, rfl⟩
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hNnorm hg) x).mp hxN
  · change (g * x * g⁻¹) ^ 2 = 1
    rw [pow_two]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [← pow_two, hx2]
      _ = 1 := by group

private def CoreModNoFixed (w : G6.coreMod 5) : Prop :=
  (∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → G6.coreAct 5 σ w = w) → w = 1

private instance instDecidableCoreModNoFixed (w : G6.coreMod 5) :
    Decidable (CoreModNoFixed w) := by
  unfold CoreModNoFixed
  infer_instance

theorem coreMod5_no_fixed : ∀ w : G6.coreMod 5,
    (∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → G6.coreAct 5 σ w = w) → w = 1 := by
  change ∀ w : G6.coreMod 5, CoreModNoFixed w
  decide +kernel

theorem not_isMulCommutative_of_isQ8D8 {W : Subgroup G}
    (h : CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 W)
    (hZ : Nat.card ↥(W ⊓ Subgroup.centralizer (W : Set G)) = 2) :
    ¬ IsMulCommutative ↥W := by
  intro hcomm
  have hfacts := CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8.facts h
  have hWle : W ≤ Subgroup.centralizer (W : Set G) := Subgroup.le_centralizer (H := W)
  have hWeq : W ⊓ Subgroup.centralizer (W : Set G) = W := inf_eq_left.mpr hWle
  rw [hWeq, hfacts.1] at hZ
  norm_num at hZ

theorem eq_of_sup_frattiniOf_eq {P K : Subgroup G}
    (h : K ⊔ CFSG.ComponentClassification.AschbacherTheorem3.frattiniOf P = P) (hK : K ≤ P) :
    K = P := by
  have htopmap : (⊤ : Subgroup ↥P).map P.subtype = P := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have htop : K.subgroupOf P ⊔ frattini ↥P = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := P)).mp
    rw [Subgroup.map_sup, htopmap, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK,
      show (frattini ↥P).map P.subtype =
        CFSG.ComponentClassification.AschbacherTheorem3.frattiniOf P from rfl]
    exact h
  have hKP : K.subgroupOf P = ⊤ := frattini_nongenerating htop
  have hKeq : (K.subgroupOf P).map P.subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK]
  rw [← hKeq, hKP, htopmap]

theorem commutator_conj_eq_bot_iff {A B : Subgroup G} {g : G}
    (hA : CFSG.conjugate A g = A) :
    ⁅A, CFSG.conjugate B g⁆ = ⊥ ↔ ⁅A, B⁆ = ⊥ := by
  have hmap := Subgroup.map_commutator (f := (MulAut.conj g⁻¹).toMonoidHom) A B
  rw [show A.map (MulAut.conj g⁻¹).toMonoidHom = CFSG.conjugate A g from rfl,
    show B.map (MulAut.conj g⁻¹).toMonoidHom = CFSG.conjugate B g from rfl, hA] at hmap
  constructor
  · intro h
    have h2 : (⁅A, B⁆).map (MulAut.conj g⁻¹).toMonoidHom =
        (⊥ : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hmap, h, Subgroup.map_bot]
    exact (Subgroup.map_injective (MulAut.conj g⁻¹).injective).eq_iff.mp h2
  · intro h
    rw [h, Subgroup.map_bot] at hmap
    exact hmap.symm

theorem commutator_sup_le_of_normal {Q A B E : Subgroup G}
    (hE : A ⊔ B ≤ Subgroup.normalizer (E : Set G))
    (hA : ⁅Q, A⁆ ≤ E) (hB : ⁅Q, B⁆ ≤ E) : ⁅Q, A ⊔ B⁆ ≤ E := by
  rw [Subgroup.commutator_le] at hA hB ⊢
  intro q hq g hg
  rw [Subgroup.sup_eq_closure] at hg
  refine Subgroup.closure_induction (k := (A : Set G) ∪ (B : Set G))
    (p := fun g _ => ⁅q, g⁆ ∈ E) ?_ ?_ ?_ ?_ hg
  · rintro x (hxA | hxB)
    · exact hA q hq x hxA
    · exact hB q hq x hxB
  · simp
  · intro x y hx hy ihx ihy
    have hxAB : x ∈ A ⊔ B := by rwa [Subgroup.sup_eq_closure]
    have hconj : x * ⁅q, y⁆ * x⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hE hxAB) ⁅q, y⁆).mp ihy
    rw [commutatorElement_mul_right_eq_mul_conj,
      show ⁅q, x⁆ * x * ⁅q, y⁆ * x⁻¹ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) by group]
    exact E.mul_mem ihx hconj
  · intro x hx ihx
    have hxAB : x ∈ A ⊔ B := by rwa [Subgroup.sup_eq_closure]
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer _).inv_mem (hE hxAB)
    have hxq : ⁅x, q⁆ ∈ E := by
      rw [← commutatorElement_inv q x]
      exact E.inv_mem ihx
    have := (Subgroup.mem_normalizer_iff.mp hxinv ⁅x, q⁆).mp hxq
    rw [commutatorElement_inv_right]
    simpa [inv_inv] using this

private theorem commutator_sup_ne_of_commutator_ne_bot {D E N1 : Subgroup G}
    (hperf : ⁅D, D⁆ = D) (hN1D : ⁅N1, D⁆ = ⊥) (hEi : ⁅E, D⁆ ≠ ⊥) :
    (⁅E, D⁆ ⊔ N1 : Subgroup G) ≠ N1 := by
  intro hMN
  have hEN : ⁅E, D⁆ ≤ N1 := by
    have hle := le_sup_left (a := ⁅E, D⁆) (b := N1)
    rwa [hMN] at hle
  exact hEi (CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step
    (D := D) (Y := E) (Y₁ := N1) hperf hEN hN1D)

private theorem commutator_eq_sup_frattini_of_le_sup {S E N1 : Subgroup G}
    (hE_N1 : E ≤ Subgroup.normalizer (N1 : Set G))
    (hle : S ≤ E ⊔ N1) (hES : E ≤ S)
    (hSN1 : S ⊓ N1 = CFSG.ComponentClassification.AschbacherTheorem3.frattiniOf S) :
    S = E ⊔ CFSG.ComponentClassification.AschbacherTheorem3.frattiniOf S := by
  apply le_antisymm
  · intro s hs
    obtain ⟨e, he, n, hn, hen⟩ := (mem_sup_of_le_normalizer hE_N1).mp (hle hs)
    have hnS : n ∈ S := by
      have hn_eq : n = e⁻¹ * s := by rw [← hen]; group
      rw [hn_eq]
      exact S.mul_mem (S.inv_mem (hES he)) hs
    have hnN : n ∈ S ⊓ N1 := ⟨hnS, hn⟩
    rw [hSN1] at hnN
    rw [← hen]
    exact Subgroup.mul_mem_sup he hnN
  · exact sup_le hES (Subgroup.map_subtype_le (frattini ↥S))

theorem commutator_S_le_of_commutator_E {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) {i : ℕ} (hi : i < 3) {N0 N1 E : Subgroup G}
    (hN1N0 : N1 ≤ N0) (hN0Q : N0 ≤ Q) (hHN0 : H ≤ Subgroup.normalizer (N0 : Set G))
    (hHN1 : H ≤ Subgroup.normalizer (N1 : Set G)) (hN1I : ⁅N1, I⁆ = ⊥)
    (hN0QN1 : ⁅N0, Q⁆ ≤ N1) (hQi : ⁅Q, Lc L x i⁆ ≤ ⁅N0, Lc L x i⁆ ⊔ N1)
    (hnat : NatA5Sec (Lc L x i) (⁅N0, Lc L x i⁆ ⊔ N1) N1)
    (hEQ : E ≤ Q) (hEnorm : H ≤ Subgroup.normalizer (E : Set G))
    (hEi : ⁅E, Lc L x i⁆ ≠ ⊥) :
    ⁅Q, Lc L x i⁆ ≤ E := by
  have hxiX : x ^ i ∈ X := X.pow_mem hxX i
  have hliH : Lc L x i ≤ H := (conjugate_le_I h hxiX).trans (I_le_H h)
  have hl := k334_local h hxX hi hN1N0 hN0Q hHN0 hHN1 hN1I hN0QN1 hQi hnat
  have hDmem := (struct49 h).2.2.2.2.1 (x ^ i) hxiX
  have hperf : ⁅Lc L x i, Lc L x i⁆ = Lc L x i :=
    CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn hDmem.1
  have hQnormH : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQH : Q ≤ H := h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hQL_le_Q : ⁅Q, Lc L x i⁆ ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hliH.trans hQnormH)
  have hELi_le_E : ⁅E, Lc L x i⁆ ≤ E :=
    CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer (hliH.trans hEnorm)
  have hELi_le_S : ⁅E, Lc L x i⁆ ≤ ⁅Q, Lc L x i⁆ := Subgroup.commutator_mono hEQ le_rfl
  have hMnorm : Lc L x i ≤
      Subgroup.normalizer ((⁅E, Lc L x i⁆ ⊔ N1 : Subgroup G) : Set G) :=
    (le_inf (Subgroup.normalizer_commutator_ge_right E (Lc L x i))
      (hliH.trans hHN1)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hMleV : (⁅E, Lc L x i⁆ ⊔ N1 : Subgroup G) ≤ ⁅N0, Lc L x i⁆ ⊔ N1 :=
    sup_le (hELi_le_S.trans hQi) le_sup_right
  have hN1Li : ⁅N1, Lc L x i⁆ = ⊥ := by
    have hle := Subgroup.commutator_mono (le_refl N1) (conjugate_le_I h hxiX)
    rw [hN1I] at hle
    exact le_bot_iff.mp hle
  have hMne : (⁅E, Lc L x i⁆ ⊔ N1 : Subgroup G) ≠ N1 :=
    commutator_sup_ne_of_commutator_ne_bot (D := Lc L x i) (N1 := N1) hperf hN1Li hEi
  have hMV : (⁅E, Lc L x i⁆ ⊔ N1 : Subgroup G) = ⁅N0, Lc L x i⁆ ⊔ N1 :=
    (NatA5Sec_eq_bot_or_eq_top hnat le_sup_right hMleV hMnorm).resolve_left hMne
  have hS_le_M : ⁅Q, Lc L x i⁆ ≤ ⁅E, Lc L x i⁆ ⊔ N1 := hQi.trans (le_of_eq hMV.symm)
  have hE_N1 : ⁅E, Lc L x i⁆ ≤ Subgroup.normalizer (N1 : Set G) :=
    hELi_le_S.trans (hQL_le_Q.trans (hQH.trans hHN1))
  have hS_eq := commutator_eq_sup_frattini_of_le_sup (S := ⁅Q, Lc L x i⁆)
    (E := ⁅E, Lc L x i⁆) (N1 := N1) hE_N1 hS_le_M hELi_le_S hl.2.2.1
  have hEq : ⁅E, Lc L x i⁆ = ⁅Q, Lc L x i⁆ := eq_of_sup_frattiniOf_eq hS_eq.symm hELi_le_S
  rw [← hEq]
  exact hELi_le_E

private theorem commutator_conj_succ_eq_bot_iff {E L : Subgroup G} {x : G}
    (hEx : CFSG.conjugate E x = E) (i : ℕ) :
    ⁅E, Lc L x (i + 1)⁆ = ⊥ ↔ ⁅E, Lc L x i⁆ = ⊥ := by
  have hL : CFSG.conjugate (Lc L x i) x = Lc L x (i + 1) := by
    rw [Lc, Lc, conjugate_conjugate, ← pow_succ]
  rw [← hL]
  exact commutator_conj_eq_bot_iff hEx

private theorem commutator_conj_eq_bot_iff_of_lt_three {E L : Subgroup G} {x : G}
    (hEx : CFSG.conjugate E x = E) {i : ℕ} (hi : i < 3) :
    ⁅E, Lc L x i⁆ = ⊥ ↔ ⁅E, Lc L x 0⁆ = ⊥ := by
  interval_cases i
  · rfl
  · exact commutator_conj_succ_eq_bot_iff hEx 0
  · exact (commutator_conj_succ_eq_bot_iff hEx 1).trans (commutator_conj_succ_eq_bot_iff hEx 0)

private theorem commutator_eq_bot_of_forall_conjugates {E I L : Subgroup G} {x : G}
    (hIeq : I = Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2)
    (h : ∀ i : ℕ, i < 3 → ⁅E, Lc L x i⁆ = ⊥) : ⁅E, I⁆ = ⊥ := by
  have hIleC : I ≤ Subgroup.centralizer (E : Set G) := by
    rw [hIeq]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.le_centralizer_iff (H := Lc L x 0) (K := E)).mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h 0 (by norm_num)))
    · exact (Subgroup.le_centralizer_iff (H := Lc L x 1) (K := E)).mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h 1 (by norm_num)))
    · exact (Subgroup.le_centralizer_iff (H := Lc L x 2) (K := E)).mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h 2 (by norm_num)))
  have hle : ⁅E, I⁆ ≤ ⁅E, Subgroup.centralizer (E : Set G)⁆ :=
    Subgroup.commutator_mono le_rfl hIleC
  have hbot : ⁅E, Subgroup.centralizer (E : Set G)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
  rw [hbot] at hle
  exact le_bot_iff.mp hle

private theorem commutator_Q_I_le_of_commutator_E_conjugates {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {x : G} (hxX : x ∈ X) {E : Subgroup G}
    (hEnorm : H ≤ Subgroup.normalizer (E : Set G))
    (hIeq : I = Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2)
    (hSle : ∀ i : ℕ, i < 3 → ⁅Q, Lc L x i⁆ ≤ E) : ⁅Q, I⁆ ≤ E := by
  have hLiN : ∀ i : ℕ, Lc L x i ≤ Subgroup.normalizer (E : Set G) := fun i =>
    (conjugate_le_I h (X.pow_mem hxX i)).trans ((I_le_H h).trans hEnorm)
  have h01 : ⁅Q, Lc L x 0 ⊔ Lc L x 1⁆ ≤ E :=
    commutator_sup_le_of_normal (Q := Q) (A := Lc L x 0) (B := Lc L x 1) (E := E)
      (sup_le (hLiN 0) (hLiN 1)) (hSle 0 (by norm_num)) (hSle 1 (by norm_num))
  have h012 : ⁅Q, (Lc L x 0 ⊔ Lc L x 1) ⊔ Lc L x 2⁆ ≤ E :=
    commutator_sup_le_of_normal (Q := Q) (A := Lc L x 0 ⊔ Lc L x 1) (B := Lc L x 2) (E := E)
      (sup_le (sup_le (hLiN 0) (hLiN 1)) (hLiN 2)) h01 (hSle 2 (by norm_num))
  rw [hIeq]; exact h012

private theorem commutator_Q_I_le_of_commutator_E_ne_bot {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {x : G} (hxX : x ∈ X) (hxgen : X = Subgroup.zpowers x)
    {N0 N1 E : Subgroup G}
    (hN1N0 : N1 ≤ N0) (hN0Q : N0 ≤ Q) (hHN0 : H ≤ Subgroup.normalizer (N0 : Set G))
    (hHN1 : H ≤ Subgroup.normalizer (N1 : Set G)) (hN1I : ⁅N1, I⁆ = ⊥)
    (hN0QN1 : ⁅N0, Q⁆ ≤ N1)
    (hVnatall : ∀ i : ℕ, i < 3 → ⁅Q, Lc L x i⁆ ≤ ⁅N0, Lc L x i⁆ ⊔ N1 ∧
      NatA5Sec (Lc L x i) (⁅N0, Lc L x i⁆ ⊔ N1) N1)
    (hEQ : E ≤ Q) (hEnorm : H ≤ Subgroup.normalizer (E : Set G))
    (hne : ⁅E, I⁆ ≠ ⊥) : ⁅Q, I⁆ ≤ E := by
  have hIeq := I_eq_sup_conjugates h hxX hxgen
  have hEx : CFSG.conjugate E x = E := by
    have hmem : x⁻¹ ∈ H := h.X_le (X.inv_mem hxX)
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEnorm hmem)
    simpa [CFSG.conjugate] using this
  have hex : ∃ j, j < 3 ∧ ⁅E, Lc L x j⁆ ≠ ⊥ := by
    by_contra hc
    push Not at hc
    exact hne (commutator_eq_bot_of_forall_conjugates hIeq hc)
  obtain ⟨j, hj, hjn⟩ := hex
  have hAll : ∀ i, i < 3 → ⁅E, Lc L x i⁆ ≠ ⊥ := fun i hi h0 =>
    hjn ((commutator_conj_eq_bot_iff_of_lt_three hEx hj).mpr
      ((commutator_conj_eq_bot_iff_of_lt_three hEx hi).mp h0))
  have hSle : ∀ i, i < 3 → ⁅Q, Lc L x i⁆ ≤ E := fun i hi =>
    commutator_S_le_of_commutator_E h hxX hi hN1N0 hN0Q hHN0 hHN1 hN1I hN0QN1
      (hVnatall i hi).1 (hVnatall i hi).2 hEQ hEnorm (hAll i hi)
  exact commutator_Q_I_le_of_commutator_E_conjugates h hxX hEnorm hIeq hSle

private theorem false_of_commutator_isQ8D8_eq_bot {K V : Subgroup G}
    (hVK : ⁅V, K⁆ = ⊥) (hQ8D8 : CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 V)
    (hZcard : Nat.card ↥(V ⊓ Subgroup.centralizer (V : Set G)) = 2)
    (hnat : NatA5Sec K V (V ⊓ Subgroup.centralizer (V : Set G))) : False := by
  obtain ⟨φ, ψ, hφs, hψs, hψk, hψe⟩ := hnat
  have hVKc : V ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVK
  have hfix : ∀ m : ↥V, ψ m = 1 := by
    intro m
    refine coreMod5_no_fixed (ψ m) ?_
    intro σ hσ
    obtain ⟨d, hdφ⟩ := hφs ⟨σ, hσ⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hVKc m.2)) (d : G) d.2
    have hconj : (d : G) * (m : G) * (d : G)⁻¹ = (m : G) := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h1 := hψe d m m hconj.symm
    rw [congrArg Subtype.val hdφ] at h1
    exact h1.symm
  have hVZ : V ≤ V ⊓ Subgroup.centralizer (V : Set G) := by
    intro v hv
    refine ⟨hv, ?_⟩
    have hvker : (⟨v, hv⟩ : ↥V) ∈ ψ.ker := MonoidHom.mem_ker.mpr (hfix ⟨v, hv⟩)
    rw [hψk] at hvker
    exact (Subgroup.mem_subgroupOf.mp hvker).2
  have hcard32 := (CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8.facts hQ8D8).1
  have heq : V ⊓ Subgroup.centralizer (V : Set G) = V :=
    inf_eq_left.mpr (hVZ.trans inf_le_right)
  rw [heq, hcard32] at hZcard
  norm_num at hZcard

private theorem false_of_commutator_isQ8D8_eq_centralizer {K V : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hZ : ⁅V, K⁆ = V ⊓ Subgroup.centralizer (V : Set G))
    (hKZ : ⁅K, V ⊓ Subgroup.centralizer (V : Set G)⁆ = ⊥)
    (hZcard : Nat.card ↥(V ⊓ Subgroup.centralizer (V : Set G)) = 2) : False := by
  have h2 : ⁅⁅V, K⁆, K⁆ = ⊥ := by
    rw [hZ, Subgroup.commutator_comm]
    exact hKZ
  have hzero := CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step
    (D := K) (Y := V) (Y₁ := ⁅V, K⁆) hperf le_rfl h2
  have heq : V ⊓ Subgroup.centralizer (V : Set G) = ⊥ := hZ.symm.trans hzero
  rw [heq] at hZcard
  simp at hZcard

private theorem false_of_le_commutator_Q_I_of_elemAbelian (hI : Inputs49)
    {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) (hK : KI49 X I) {E : Subgroup G}
    (hEel : CFSG.Open.IsElemAbelian 2 E) (hQI_le_E : ⁅Q, I⁆ ≤ E) : False := by
  obtain ⟨x, hxX, hxgen, -, -, -⟩ := exists_generator49 h
  obtain ⟨A, a, n, hd⟩ := xaData_exists h hxgen
  have hkb := kbasic49 h hd.reg hd.A_le
  obtain ⟨Vk, hVk_le, hKVk, hQ8D8, hVk_pcore, hZcard, hKZ, hinv, hnat, h3el⟩ :=
    kmodel49 hI hK hkb.1
  have hKQ : KI X I ⊓ Q = Vk := hkb.2.2.1.trans hVk_pcore.symm
  have hVkQ : Vk ≤ Q := by rw [← hKQ]; exact inf_le_right
  have hWle : ⁅Vk, KI X I⁆ ≤ Vk :=
    CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hKVk
  have hWnorm : KI X I ≤ Subgroup.normalizer ((⁅Vk, KI X I⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right Vk (KI X I)
  have hVK : ⁅Vk, KI X I⁆ = Vk := by
    rcases hinv ⁅Vk, KI X I⁆ hWle hWnorm with hbot | hZ | hV
    · exact (false_of_commutator_isQ8D8_eq_bot hbot hQ8D8 hZcard hnat).elim
    · exact (false_of_commutator_isQ8D8_eq_centralizer hkb.1 hZ hKZ hZcard).elim
    · exact hV
  have hVk_le_QI : Vk ≤ ⁅Q, I⁆ := by
    rw [← hVK]
    exact Subgroup.commutator_mono hVkQ (KI_le_I49 X I)
  have hVkE : Vk ≤ E := hVk_le_QI.trans hQI_le_E
  have hVkcomm : IsMulCommutative ↥Vk := by
    rw [isMulCommutative_iff]
    intro u v
    apply Subtype.ext
    show (u : G) * (v : G) = (v : G) * (u : G)
    exact congrArg Subtype.val
      ((isMulCommutative_iff.mp hEel.1) ⟨(u : G), hVkE u.2⟩ ⟨(v : G), hVkE v.2⟩)
  exact not_isMulCommutative_of_isQ8D8 hQ8D8 hZcard hVkcomm

theorem commutator_E_I_eq_bot (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    (hK : KI49 X I) {E : Subgroup G} (hEH : E ≤ H)
    (hEnorm : H ≤ Subgroup.normalizer (E : Set G))
    (hEel : CFSG.Open.IsElemAbelian 2 E) (hEQ : E ≤ Q) : ⁅E, I⁆ = ⊥ := by
  by_contra hEIn
  obtain ⟨x, hxX, hxgen, -, -, -⟩ := exists_generator49 h
  obtain ⟨N0, N1, hN1N0, hN0Q, hHN0, hHN1, hN1I, hQIN0, hN0QN1, hshape⟩ :=
    propM49 hI h hxgen hK
  let V : ℕ → Subgroup G := fun i => ⁅N0, Lc L x i⁆ ⊔ N1
  have hVeq : ∀ i, V i = ⁅N0, Lc L x i⁆ ⊔ N1 := fun i => rfl
  obtain ⟨-, -, hVcommall, hVnatall⟩ := hshape V hVeq
  have hQI_le_E := commutator_Q_I_le_of_commutator_E_ne_bot h hxX hxgen hN1N0 hN0Q
    hHN0 hHN1 hN1I hN0QN1 hVnatall hEQ hEnorm hEIn
  exact false_of_le_commutator_Q_I_of_elemAbelian hI h hK hEel hQI_le_E

theorem part3_49 (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    (hK : KI49 X I) : Part3_49 H Q I := by
  intro hdisj
  let P : Subgroup G := Q ⊓ Subgroup.centralizer (I : Set G)
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQnormH : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hP2 : IsPGroup 2 ↥P := hQ2.to_le inf_le_left
  have hCnorm : H ≤ Subgroup.normalizer (Subgroup.centralizer (I : Set G) : Set G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer (le_normalizer_I h)
  have hPnorm : H ≤ Subgroup.normalizer (P : Set G) :=
    (le_inf hQnormH hCnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨isElemAbelian_omegaOne hP2 hdisj, le_normalizer_omegaOne_of_le_normalizer hPnorm, ?_⟩
  intro p hp E hEH hEnorm hEel
  by_cases hp2 : p = 2
  · subst hp2
    have hE2 : IsPGroup 2 ↥E := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hEel.2 (g : G) g.2⟩
    have hEQ : E ≤ Q := by
      rw [h.Q_eq]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hEH hEnorm hE2
    have hEI : ⁅E, I⁆ = ⊥ := commutator_E_I_eq_bot hI h hK hEH hEnorm hEel hEQ
    have hEP : E ≤ P := fun x hx =>
      ⟨hEQ hx, Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEI hx⟩
    intro x hx
    exact Subgroup.subset_closure ⟨hEP hx, by simpa using hEel.2 x hx⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    have hEp : IsPGroup p ↥E := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hEel.2 (g : G) g.2⟩
    have hEodd : Odd (Nat.card E) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥E)).mp hEp
      rw [hn]
      exact (hp.odd_of_ne_two hp2).pow
    have hbot : E = ⊥ := (struct49 h).2.2.2.2.2.2.2 E hEH hEnorm hEodd
    rw [hbot]
    exact bot_le

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
