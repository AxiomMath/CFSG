module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.lemma_1_22
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Infrastructure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core
public import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

/-!
# Gorenstein, Chapter 8, Section 2

This file is reserved for a direct formalization of the book proof of
Gorenstein's Theorem 8.2.11. We intentionally avoid importing
`FeitThompson.BGsection6` and define the local `A(P)` / `J(P)`
infrastructure here.
-/

open scoped Pointwise commutatorElement

section

variable {G : Type*} [Group G]

theorem CFSG.eq_one_of_mem_pGroup_sq_eq_one
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (H : Subgroup G) (hHp : IsPGroup p ↥H) {d : G} (hd : d ∈ H) (hdsq : d ^ 2 = 1) :
    d = 1 := by
  have hpow : orderOf (⟨d, hd⟩ : H) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hdsq)
  rcases (IsPGroup.iff_orderOf (p := p) (G := H)).1 hHp (⟨d, hd⟩ : H) with ⟨k, hk⟩
  have hk_dvd : p ^ k ∣ 2 := by simpa [hk] using hpow
  have hk_zero : k = 0 := by
    cases k with
    | zero =>
        rfl
    | succ k =>
        exfalso
        have hpdvd : p ∣ 2 := by
          exact dvd_trans (dvd_pow_self p (Nat.succ_ne_zero _)) hk_dvd
        have hp_eq_two : p = 2 := by
          exact (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hpdvd
        exact hpodd hp_eq_two
  have hord : orderOf (⟨d, hd⟩ : H) = 1 := by
    simpa [hk_zero] using hk
  have htriv : (⟨d, hd⟩ : H) = 1 := orderOf_eq_one_iff.mp hord
  exact congrArg Subtype.val htriv

theorem CFSG.lowerCentralSeries_commutator_le
    (i j : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) := by
  induction j generalizing i with
  | zero =>
      simp [Subgroup.lowerCentralSeries]
  | succ j ih =>
      let N : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries (i + j + 2)
      let q : G →* G ⧸ N := QuotientGroup.mk' N
      have h1le :
          ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries i⁆,
            (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤ N := by
        dsimp [N]
        rw [Subgroup.commutator_comm (⊤ : Subgroup G)]
        change
          ⁅(⊤ : Subgroup G).lowerCentralSeries (i + 1),
            (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
              (⊤ : Subgroup G).lowerCentralSeries (i + j + 2)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (ih (i + 1))
      have h2le :
          ⁅⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆,
            (⊤ : Subgroup G)⁆ ≤ N := by
        dsimp [N]
        exact Subgroup.commutator_mono (ih i) le_rfl
      have h1bot :
          ⁅⁅(⊤ : Subgroup G).map q, ((⊤ : Subgroup G).lowerCentralSeries i).map q⁆,
            ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆ = ⊥ := by
        apply le_bot_iff.mp
        calc
          ⁅⁅(⊤ : Subgroup G).map q, ((⊤ : Subgroup G).lowerCentralSeries i).map q⁆,
              ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆ =
              (⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries i⁆,
                (⊤ : Subgroup G).lowerCentralSeries j⁆).map q := by
                rw [Subgroup.map_commutator, Subgroup.map_commutator]
          _ ≤ N.map q := Subgroup.map_mono h1le
          _ = ⊥ := QuotientGroup.map_mk'_self (N := N)
      have h2bot :
          ⁅⁅((⊤ : Subgroup G).lowerCentralSeries i).map q,
            ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆,
            (⊤ : Subgroup G).map q⁆ = ⊥ := by
        apply le_bot_iff.mp
        calc
          ⁅⁅((⊤ : Subgroup G).lowerCentralSeries i).map q,
              ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆,
              (⊤ : Subgroup G).map q⁆ =
              (⁅⁅(⊤ : Subgroup G).lowerCentralSeries i,
                (⊤ : Subgroup G).lowerCentralSeries j⁆, (⊤ : Subgroup G)⁆).map q := by
                rw [Subgroup.map_commutator, Subgroup.map_commutator]
          _ ≤ N.map q := Subgroup.map_mono h2le
          _ = ⊥ := QuotientGroup.map_mk'_self (N := N)
      have hbotq :
          ⁅⁅((⊤ : Subgroup G).lowerCentralSeries j).map q, (⊤ : Subgroup G).map q⁆,
            ((⊤ : Subgroup G).lowerCentralSeries i).map q⁆ = ⊥ := by
        exact Subgroup.commutator_commutator_eq_bot_of_rotate h1bot h2bot
      have hleq :
          (⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆,
            (⊤ : Subgroup G).lowerCentralSeries i⁆).map q = ⊥ := by
        simpa [Subgroup.map_commutator] using hbotq
      have hle :
          ⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆,
            (⊤ : Subgroup G).lowerCentralSeries i⁆ ≤ N := by
        have hker :=
          (Subgroup.map_eq_bot_iff
            (f := q)
            (H := ⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆,
              (⊤ : Subgroup G).lowerCentralSeries i⁆)).1 hleq
        simpa [q, QuotientGroup.ker_mk'] using hker
      dsimp [N] at hle
      change ⁅(⊤ : Subgroup G).lowerCentralSeries i,
        ⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆⁆ ≤
          (⊤ : Subgroup G).lowerCentralSeries (i + j + 2)
      rw [Subgroup.commutator_comm]
      exact hle

/-- Gorenstein's iterated commutator chain `[B, A; i]`. -/
private def CFSG.replacementCommChain (B A : Subgroup G) : ℕ → Subgroup G
  | 0 => B
  | n + 1 => ⁅replacementCommChain B A n, A⁆

@[simp] private theorem CFSG.replacementCommChain_zero (B A : Subgroup G) :
    replacementCommChain B A 0 = B := rfl

@[simp] private theorem CFSG.replacementCommChain_succ (B A : Subgroup G) (n : ℕ) :
    replacementCommChain B A (n + 1) = ⁅replacementCommChain B A n, A⁆ := rfl

private theorem CFSG.replacementCommChain_le_normalizer
    (B A : Subgroup G) [B.Normal] :
    ∀ n, A ≤ Subgroup.normalizer (replacementCommChain B A n : Set G)
  | 0 => by
      rw [replacementCommChain_zero, Subgroup.normalizer_eq_top (H := B)]
      exact le_top
  | n + 1 => by
      let D : Subgroup G := replacementCommChain B A n
      let : ((⁅D, A⁆).subgroupOf (D ⊔ A)).Normal := commutator_normal_in_sup D A
      have hsup_norm : D ⊔ A ≤ Subgroup.normalizer (((⁅D, A⁆ : Subgroup G) : Set G)) := by
        exact
          Subgroup.le_normalizer_of_normal_subgroupOf
            (H := ⁅D, A⁆) (K := D ⊔ A) (commutator_le_sup D A)
      rw [replacementCommChain_succ]
      exact le_sup_right.trans hsup_norm

private theorem CFSG.replacementCommChain_descends
    (B A : Subgroup G) [B.Normal] (n : ℕ) :
    replacementCommChain B A (n + 1) ≤ replacementCommChain B A n := by
  rw [replacementCommChain_succ]
  refine (Subgroup.commutator_le).2 ?_
  intro x hx a ha
  have ha_norm : a ∈ Subgroup.normalizer (replacementCommChain B A n : Set G) :=
    replacementCommChain_le_normalizer B A n ha
  have hconj : a * x⁻¹ * a⁻¹ ∈ replacementCommChain B A n :=
    (Subgroup.mem_normalizer_iff.mp ha_norm x⁻¹).1
      ((replacementCommChain B A n).inv_mem hx)
  rw [commutatorElement_def]
  simpa [mul_assoc] using (replacementCommChain B A n).mul_mem hx hconj

private theorem CFSG.replacementCommChain_le_left
    (B A : Subgroup G) [B.Normal] :
    ∀ n, replacementCommChain B A n ≤ B
  | 0 => le_rfl
  | n + 1 =>
      (replacementCommChain_descends B A n).trans (replacementCommChain_le_left B A n)

private theorem CFSG.replacementCommChain_antitone
    (B A : Subgroup G) [B.Normal] {i j : ℕ}
    (hij : i ≤ j) :
    replacementCommChain B A j ≤ replacementCommChain B A i := by
  induction hij with
  | refl =>
      exact le_rfl
  | @step j hij ih =>
      exact (replacementCommChain_descends B A j).trans ih

private theorem CFSG.replacementCommChain_eq_bot_of_eq_bot_of_le
    (B A : Subgroup G) [B.Normal] {i j : ℕ}
    (hij : i ≤ j) (hi : replacementCommChain B A i = ⊥) :
    replacementCommChain B A j = ⊥ := by
  apply le_antisymm
  · exact (replacementCommChain_antitone B A hij).trans_eq hi
  · exact bot_le

private theorem CFSG.replacementCommChain_le_sup
    (B A : Subgroup G) :
    ∀ n, replacementCommChain B A n ≤ B ⊔ A
  | 0 => le_sup_left
  | n + 1 =>
      calc
        replacementCommChain B A (n + 1) = ⁅replacementCommChain B A n, A⁆ := by
          rw [replacementCommChain_succ]
        _ ≤ replacementCommChain B A n ⊔ A := commutator_le_sup _ _
        _ ≤ B ⊔ A := sup_le (replacementCommChain_le_sup B A n) le_sup_right

/-- The iterated commutator chain viewed inside `A ⊔ B`. -/
private def CFSG.replacementCommChainSub (B A : Subgroup G) : ℕ → Subgroup ↥(B ⊔ A)
  | 0 => B.subgroupOf (B ⊔ A)
  | n + 1 => ⁅replacementCommChainSub B A n, A.subgroupOf (B ⊔ A)⁆

@[simp] private theorem CFSG.replacementCommChainSub_zero (B A : Subgroup G) :
    replacementCommChainSub B A 0 = B.subgroupOf (B ⊔ A) := rfl

@[simp] private theorem CFSG.replacementCommChainSub_succ (B A : Subgroup G) (n : ℕ) :
    replacementCommChainSub B A (n + 1) =
      ⁅replacementCommChainSub B A n, A.subgroupOf (B ⊔ A)⁆ := rfl

private theorem CFSG.replacementCommChainSub_eq_subgroupOf
    (B A : Subgroup G) :
    ∀ n,
      replacementCommChainSub B A n =
        (replacementCommChain B A n).subgroupOf (B ⊔ A)
  | 0 => by
      ext x
      simp [replacementCommChainSub, replacementCommChain]
  | n + 1 => by
      let S : Subgroup G := B ⊔ A
      apply (Subgroup.map_subtype_inj (H := S)).mp
      calc
        (replacementCommChainSub B A (n + 1)).map S.subtype =
            ⁅(replacementCommChainSub B A n).map S.subtype,
              (A.subgroupOf S).map S.subtype⁆ := by
              rw [replacementCommChainSub_succ, Subgroup.map_commutator]
        _ = ⁅replacementCommChain B A n, A⁆ := by
              rw [replacementCommChainSub_eq_subgroupOf B A n,
                Subgroup.map_subgroupOf_eq_of_le
                  (replacementCommChain_le_sup B A n),
                Subgroup.map_subgroupOf_eq_of_le le_sup_right]
        _ = ((replacementCommChain B A (n + 1)).subgroupOf S).map S.subtype := by
              simpa [replacementCommChain_succ] using
                (Subgroup.map_subgroupOf_eq_of_le
                  (replacementCommChain_le_sup B A (n + 1)))

private theorem CFSG.replacementCommChainSub_le_lowerCentralSeries
    (B A : Subgroup G) :
    ∀ n,
      replacementCommChainSub B A n ≤
        (⊤ : Subgroup ↥(B ⊔ A)).lowerCentralSeries n
  | 0 => by
      simp [Subgroup.lowerCentralSeries_zero]
  | n + 1 => by
      rw [replacementCommChainSub_succ, Subgroup.lowerCentralSeries_succ]
      exact
        (Subgroup.commutator_mono
          (replacementCommChainSub_le_lowerCentralSeries B A n) le_top)

private theorem CFSG.replacementCommChain_eventually_bot_of_isNilpotent
    (B A : Subgroup G)
    (hnil : Group.IsNilpotent ↥(B ⊔ A)) :
    ∃ n, replacementCommChain B A n = ⊥ := by
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↥(B ⊔ A))).1 hnil
  refine ⟨n, ?_⟩
  calc
    replacementCommChain B A n =
        ((replacementCommChain B A n).subgroupOf (B ⊔ A)).map (B ⊔ A).subtype := by
          symm
          exact Subgroup.map_subgroupOf_eq_of_le (replacementCommChain_le_sup B A n)
    _ = (replacementCommChainSub B A n).map (B ⊔ A).subtype := by
          rw [replacementCommChainSub_eq_subgroupOf]
    _ = ⊥ := by
          apply le_antisymm
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hybot : y ∈ (⊥ : Subgroup ↥(B ⊔ A)) := by
              exact (replacementCommChainSub_le_lowerCentralSeries B A n).trans_eq hn hy
            simpa using hybot
          · exact bot_le

private theorem CFSG.replacementCommChain_eventually_bot
    {p : ℕ} [Fact (Nat.Prime p)] [Finite G]
    (B A : Subgroup G)
    (hBAp : IsPGroup p ↥(B ⊔ A)) :
    ∃ n, replacementCommChain B A n = ⊥ := by
  exact
    replacementCommChain_eventually_bot_of_isNilpotent B A
      (IsPGroup.isNilpotent (p := p) hBAp)

private theorem CFSG.replacementCommChain_exists_positive_abelian
    {p : ℕ} [Fact (Nat.Prime p)] [Finite G]
    (B A : Subgroup G) (hBne : B ≠ ⊥)
    (hBAp : IsPGroup p ↥(B ⊔ A)) :
    ∃ n, 0 < n ∧ IsMulCommutative (replacementCommChain B A n) := by
  obtain ⟨n, hn⟩ := replacementCommChain_eventually_bot (p := p) B A hBAp
  have hnpos : 0 < n := by
    cases n with
    | zero =>
        exfalso
        exact hBne (by simpa [replacementCommChain_zero] using hn)
    | succ n =>
        simp
  refine ⟨n, hnpos, ?_⟩
  rw [hn]
  infer_instance

/-- The centralizer of `H` inside the ambient subgroup `U`. -/
def CFSG.subgroupCentralizerIn' (U H : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (H : Set G) ⊓ U

private lemma CFSG.normalizer_le_normalizer_centralizer (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc
    intro r hr
    have hrn : n⁻¹ * r * n ∈ R := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (R : Set G)).inv_mem hn) _).1 hr
    have hcomm : (n⁻¹ * r * n) * c = c * (n⁻¹ * r * n) := hc _ hrn
    have hcomm' := congrArg (fun x : G => n * x * n⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc
    intro r hr
    have hrn : n * r * n⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hn _).1 hr
    have hcomm :
        (n * r * n⁻¹) * (n * c * n⁻¹) = (n * c * n⁻¹) * (n * r * n⁻¹) :=
      hc _ hrn
    have hcomm' := congrArg (fun x : G => n⁻¹ * x * n) hcomm
    simpa [mul_assoc] using hcomm'

/-- Gorenstein's `A(P)`: the abelian subgroups of `P` having maximal order. -/
@[expose]
public def CFSG.thompsonAbelianSubgroups (P : Subgroup G) : Set (Subgroup G) :=
  {A : Subgroup G |
    A ≤ P ∧
      IsMulCommutative A ∧
        ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B ≤ Nat.card A}

/-- Gorenstein's Thompson subgroup `J(P)`. -/
@[expose]
public def CFSG.thompsonSubgroup (P : Subgroup G) : Subgroup G :=
  sSup (thompsonAbelianSubgroups (G := G) P)


/-- Gorenstein's `Z(J(P))` inside the ambient group. -/
@[expose]
public def CFSG.thompsonCenter (P : Subgroup G) : Subgroup G :=
  centerIn (G := G) (thompsonSubgroup (G := G) P)

private lemma CFSG.thompsonSubgroup_le (P : Subgroup G) :
    thompsonSubgroup (G := G) P ≤ P := by
  refine sSup_le ?_
  intro A hA
  exact hA.1

private lemma CFSG.thompsonCenter_le (P : Subgroup G) :
    thompsonCenter (G := G) P ≤ P := by
  calc
    thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
      exact inf_le_left
    _ ≤ P := thompsonSubgroup_le (G := G) P

private lemma CFSG.thompsonCenter_isMulCommutative (P : Subgroup G) :
    IsMulCommutative (thompsonCenter (G := G) P) := by
  refine (Subgroup.le_centralizer_iff_isMulCommutative (K := thompsonCenter (G := G) P)).1 ?_
  have hle_left : thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
    exact inf_le_left
  have hle_right :
      thompsonCenter (G := G) P ≤
        Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  exact hle_right.trans <|
    Subgroup.centralizer_le
      (show (thompsonCenter (G := G) P : Set G) ⊆ (thompsonSubgroup (G := G) P : Set G) from hle_left)

private lemma CFSG.thompsonSubgroup_top_map_subtype (P : Subgroup G) :
    (thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype = thompsonSubgroup (G := G) P := by
  classical
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro A hA
    exact (Subgroup.map_le_iff_le_comap).mp <| le_sSup <| by
      refine ⟨?_, ?_, ?_⟩
      · simpa using (Subgroup.map_subtype_le (H := P) (K := A))
      · let : IsMulCommutative A := hA.2.1
        exact Subgroup.map_isMulCommutative (H := A) P.subtype
      · intro B hB hBcomm
        let B' : Subgroup P := B.subgroupOf P
        have hAmax := hA.2.2 B' (by simp) (by
          let : IsMulCommutative B := hBcomm
          infer_instance)
        calc
          Nat.card B = Nat.card B' := by
            simpa [B', Subgroup.map_subgroupOf_eq_of_le hB] using
              (Subgroup.card_subtype P B')
          _ ≤ Nat.card A := hAmax
          _ = Nat.card (A.map P.subtype) := by
            symm
            exact Subgroup.card_map_of_injective (K := A) P.subtype_injective
  · refine sSup_le ?_
    intro A hA
    have hAin :
        A.subgroupOf P ∈ thompsonAbelianSubgroups (G := P) (⊤ : Subgroup P) := by
      refine ⟨by simp, ?_, ?_⟩
      · let : IsMulCommutative A := hA.2.1
        infer_instance
      · intro B hB hBcomm
        have hAmax := hA.2.2 (B.map P.subtype) (by
          simpa using (Subgroup.map_subtype_le (H := P) (K := B))) (by
            exact Subgroup.map_isMulCommutative (H := B) P.subtype)
        calc
          Nat.card B = Nat.card (B.map P.subtype) := by
            symm
            exact Subgroup.card_subtype P B
      _ ≤ Nat.card A := hAmax
      _ = Nat.card (A.subgroupOf P) := by
            simpa [Subgroup.map_subgroupOf_eq_of_le hA.1] using
              (Subgroup.card_subtype P (A.subgroupOf P))
    calc
      A = (A.subgroupOf P).map P.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA.1]
      _ ≤ (thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype := by
        exact Subgroup.map_mono (le_sSup hAin)

private lemma CFSG.centerIn_top_map_subtype (P : Subgroup G) (H : Subgroup P) :
    (centerIn (G := P) H).map P.subtype = centerIn (G := G) (H.map P.subtype) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hy.1
    have hyC : y ∈ Subgroup.centralizer (H : Set P) := hy.2
    refine ⟨Subgroup.mem_map_of_mem P.subtype hyH, ?_⟩
    show ∀ h ∈ (H.map P.subtype : Set G), h * P.subtype y = P.subtype y * h
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact congrArg P.subtype ((Subgroup.mem_centralizer_iff.mp hyC) _ hw)
  · intro hx
    rcases Subgroup.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨y, ⟨hy, ?_⟩, rfl⟩
    have hxC : P.subtype y ∈ Subgroup.centralizer (H.map P.subtype : Set G) := hx.2
    show ∀ h ∈ (H : Set P), h * y = y * h
    intro z hz
    have hzmap : P.subtype z ∈ H.map P.subtype := Subgroup.mem_map_of_mem P.subtype hz
    exact P.subtype_injective <| by
      simpa using (Subgroup.mem_centralizer_iff.mp hxC) _ hzmap

private lemma CFSG.thompsonCenter_top_map_subtype (P : Subgroup G) :
    (thompsonCenter (G := P) (⊤ : Subgroup P)).map P.subtype = thompsonCenter (G := G) P := by
  calc
    (thompsonCenter (G := P) (⊤ : Subgroup P)).map P.subtype
        = (centerIn (G := P) (thompsonSubgroup (G := P) (⊤ : Subgroup P))).map P.subtype := rfl
    _ = centerIn (G := G) ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype) :=
      centerIn_top_map_subtype P (thompsonSubgroup (G := P) (⊤ : Subgroup P))
    _ = thompsonCenter (G := G) P := by
      rw [thompsonSubgroup_top_map_subtype]
      rfl

private lemma CFSG.centerIn_map_mulEquiv {H : Type*} [Group H] [Finite H] (e : G ≃* H) (J : Subgroup G) :
    (centerIn (G := G) J).map e.toMonoidHom = centerIn (G := H) (J.map e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem e.toMonoidHom hy.1, ?_⟩
    show ∀ h ∈ (J.map e.toMonoidHom : Set H), h * e y = e y * h
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    simpa [map_mul] using congrArg e ((Subgroup.mem_centralizer_iff.mp hy.2) _ hw)
  · intro hx
    rcases Subgroup.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨y, ⟨hy, ?_⟩, rfl⟩
    show ∀ h ∈ (J : Set G), h * y = y * h
    intro z hz
    have hzmap : e z ∈ J.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hz
    exact e.injective <| by
      simpa [map_mul] using (Subgroup.mem_centralizer_iff.mp hx.2) _ hzmap

private lemma CFSG.thompsonSubgroup_top_map_mulEquiv {H : Type*} [Group H] [Finite H] (e : G ≃* H) :
    (thompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom =
      thompsonSubgroup (G := H) (⊤ : Subgroup H) := by
  classical
  have himage :
      (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G) =
        thompsonAbelianSubgroups (G := H) (⊤ : Subgroup H) := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      refine ⟨by simp, ?_, ?_⟩
      · let : IsMulCommutative B := hB.2.1
        exact Subgroup.map_isMulCommutative (H := B) e.toMonoidHom
      · intro C _ hCcomm
        have hBmax := hB.2.2 (C.map e.symm.toMonoidHom) (by simp) (by
          let : IsMulCommutative C := hCcomm
          exact Subgroup.map_isMulCommutative (H := C) e.symm.toMonoidHom)
        calc
          Nat.card C = Nat.card (C.map e.symm.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := C) e.symm.injective
          _ ≤ Nat.card B := hBmax
          _ = Nat.card (B.map e.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := B) e.injective
    · intro hA
      refine ⟨A.map e.symm.toMonoidHom, ?_, ?_⟩
      · refine ⟨by simp, ?_, ?_⟩
        · let : IsMulCommutative A := hA.2.1
          exact Subgroup.map_isMulCommutative (H := A) e.symm.toMonoidHom
        · intro C _ hCcomm
          have hAmax := hA.2.2 (C.map e.toMonoidHom) (by simp) (by
            let : IsMulCommutative C := hCcomm
            exact Subgroup.map_isMulCommutative (H := C) e.toMonoidHom)
          calc
            Nat.card C = Nat.card (C.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.injective
            _ ≤ Nat.card A := hAmax
            _ = Nat.card (A.map e.symm.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := A) e.symm.injective
      · ext x
        simp
  calc
    (thompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom
        = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G))) := rfl
    _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G)) := by
      simp
    _ = thompsonSubgroup (G := H) (⊤ : Subgroup H) := by
      simpa [thompsonSubgroup] using congrArg sSup himage

private lemma CFSG.thompsonCenter_top_map_mulEquiv {H : Type*} [Group H] [Finite H] (e : G ≃* H) :
    (thompsonCenter (G := G) (⊤ : Subgroup G)).map e.toMonoidHom =
      thompsonCenter (G := H) (⊤ : Subgroup H) := by
  calc
    (thompsonCenter (G := G) (⊤ : Subgroup G)).map e.toMonoidHom
        = centerIn (G := H) ((thompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom) := by
          exact centerIn_map_mulEquiv e (thompsonSubgroup (G := G) (⊤ : Subgroup G))
    _ = thompsonCenter (G := H) (⊤ : Subgroup H) := by
          rw [thompsonSubgroup_top_map_mulEquiv]
          rfl

section ConstraintAndStability

variable (p : ℕ) [Fact p.Prime]

@[expose]
public def CFSG.PConstrainedGroup : Prop :=
  ∀ Q : Subgroup G,
    IsPGroup p Q →
      pPrimeCore p G ⊔ Q = Op_p'p p G →
        Subgroup.centralizer (Q : Set G) ≤ Op_p'p p G

@[expose]
public def CFSG.PStableGroup' : Prop :=
  ∀ Q A : Subgroup G,
    (pPrimeCore p G ⊔ Q).Normal →
      IsPGroup p Q →
        IsPGroup p A →
          A ≤ Subgroup.normalizer (Q : Set G) →
            ⁅⁅Q, A⁆, A⁆ = ⊥ →
              let N : Subgroup G := Subgroup.normalizer (Q : Set G)
              let C : Subgroup G := Subgroup.centralizer (Q : Set G)
              letI : (C.subgroupOf N).Normal := by
                have hCN : C ≤ N := by
                  simpa using (centralizer_le_normalizer (G := G) Q)
                exact
                  (Subgroup.normal_subgroupOf_iff_le_normalizer
                    (H := C) (K := N) hCN).2
                    (normalizer_le_normalizer_centralizer (G := G) Q)
              ((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))) ≤
                pCore p (N ⧸ C.subgroupOf N)

omit [Fact (Nat.Prime p)] in
theorem CFSG.pCore_map_le_pCore_of_surjective {H : Type*} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (pCore p G).map f ≤ pCore p H := by
  exact le_sSup <|
    And.intro
      (Subgroup.Normal.map (H := pCore p G) inferInstance f hf)
      (IsPGroup.map (p := p) (H := pCore p G) (pCore_isPGroup (G := G) (p := p)) f)

omit [Fact (Nat.Prime p)] in
theorem CFSG.pCore_quotient_pCore_eq_bot :
    pCore p (G ⧸ pCore p G) = ⊥ := by
  let q : G →* G ⧸ pCore p G := QuotientGroup.mk' (pCore p G)
  have hmap :
      (pCore p G).map q = pCore p (G ⧸ pCore p G) :=
    pCore_map_mk'_eq_of_normal_isPGroup (G := G) (p := p) (pCore p G)
      (pCore_isPGroup (G := G) (p := p))
  have hmap_bot : (pCore p G).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := pCore p G)).2
    simp [q, QuotientGroup.ker_mk']
  exact hmap.symm.trans hmap_bot

variable [Finite G]

private theorem CFSG.quotient_pPrimeCore_subgroupMap_injective
    (H : Subgroup G) (hHp : IsPGroup p H) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore p G)).comp H.subtype) := by
  let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
  have hcoprime :
      Nat.Coprime (Nat.card H) (Nat.card (pPrimeCore p G)) := by
    rcases IsPGroup.iff_card.mp hHp with ⟨n, hcard⟩
    rw [hcard]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hinf_bot : H ⊓ pPrimeCore p G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
  have hker_bot :
      (((q.comp H.subtype)).ker : Subgroup H) = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxM : ((x : H) : G) ∈ pPrimeCore p G := by
        exact
          (QuotientGroup.eq_one_iff (N := pPrimeCore p G) (x := ((x : H) : G))).1 hx
      have hxbot : ((x : H) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨x.2, hxM⟩
      simpa using hxbot
    · intro hx
      change q ((x : H) : G) = 1
      have hx1 : x = 1 := by simpa [Subgroup.mem_bot] using hx
      rw [hx1]
      simp [q]
  exact (MonoidHom.ker_eq_bot_iff (q.comp H.subtype)).1 hker_bot

omit [Finite G] [Fact (Nat.Prime p)] in
private theorem CFSG.thompsonCenter_normal_subgroupOf_sylow
    (P : Sylow p G) :
    ((thompsonCenter (G := G) (P : Subgroup G)).subgroupOf (P : Subgroup G)).Normal := by
  classical
  let S : Subgroup G := (P : Subgroup G)
  let J : Subgroup G := thompsonSubgroup (G := G) S
  have hJ_map_eq :
      ∀ g ∈ S, J.map (MulAut.conj g).toMonoidHom = J := by
    intro g hg
    let e : G ≃* G := MulAut.conj g
    have himage :
        (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S =
          thompsonAbelianSubgroups (G := G) S := by
      ext B
      constructor
      · rintro ⟨A, hA, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · change A.map (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) ≤ S
          exact Subgroup.conj_smul_le_of_le hA.1 ⟨g, hg⟩
        · let : IsMulCommutative A := hA.2.1
          exact Subgroup.map_isMulCommutative (H := A) e.toMonoidHom
        · intro C hC hCcomm
          have hCpre_le : C.map e.symm.toMonoidHom ≤ S := by
            intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            simpa [e] using S.mul_mem (S.mul_mem (S.inv_mem hg) (hC hy)) hg
          have hCpre_comm : IsMulCommutative (C.map e.symm.toMonoidHom) := by
            infer_instance
          have hAmax := hA.2.2 (C.map e.symm.toMonoidHom) hCpre_le hCpre_comm
          calc
            Nat.card C = Nat.card (C.map e.symm.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.symm.injective
            _ ≤ Nat.card A := hAmax
            _ = Nat.card (A.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := A) e.injective
      · intro hB
        refine ⟨B.map e.symm.toMonoidHom, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            simpa [e] using S.mul_mem (S.mul_mem (S.inv_mem hg) (hB.1 hy)) hg
          · let : IsMulCommutative B := hB.2.1
            exact Subgroup.map_isMulCommutative (H := B) e.symm.toMonoidHom
          · intro C hC hCcomm
            have hCpre_le : C.map e.toMonoidHom ≤ S := by
              change C.map (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) ≤ S
              exact Subgroup.conj_smul_le_of_le hC ⟨g, hg⟩
            have hCpre_comm : IsMulCommutative (C.map e.toMonoidHom) := by
              infer_instance
            have hBmax := hB.2.2 (C.map e.toMonoidHom) hCpre_le hCpre_comm
            calc
              Nat.card C = Nat.card (C.map e.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := C) e.injective
              _ ≤ Nat.card B := hBmax
              _ = Nat.card (B.map e.symm.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := B) e.symm.injective
        · ext x
          simp
    calc
      J.map (MulAut.conj g).toMonoidHom
          = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) S)) := rfl
      _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S) := by
        simp
      _ = J := by simpa [J, thompsonSubgroup] using congrArg sSup himage
  refine (Subgroup.normal_subgroupOf_iff (thompsonCenter_le (G := G) S)).2 ?_
  intro z g hz hg
  refine ⟨?_, ?_⟩
  · have hzJ : z ∈ J := by
      simpa [thompsonCenter, centerIn, J] using hz.1
    have hzmap :
        g * z * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzJ
    rwa [hJ_map_eq g hg] at hzmap
  · exact Subgroup.mem_centralizer_iff.mpr <| by
      intro y hy
      have hy' : g⁻¹ * y * g ∈ J := by
        have hymap :
            g⁻¹ * y * g ∈ J.map (MulAut.conj g⁻¹).toMonoidHom := by
          simpa [J] using
            (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hy)
        rwa [hJ_map_eq g⁻¹ (S.inv_mem hg)] at hymap
      have hzcent :
          z ∈ Subgroup.centralizer (J : Set G) := by
        simpa [thompsonCenter, centerIn, J] using hz.2
      have hzcent' := Subgroup.mem_centralizer_iff.mp hzcent
      have hcomm : z * (g⁻¹ * y * g) = (g⁻¹ * y * g) * z := (hzcent' _ hy').symm
      have hcomm' := congrArg (fun x : G => g * x * g⁻¹) hcomm.symm
      simpa [mul_assoc] using hcomm'

omit [Finite G] in
private lemma CFSG.normalizer_le_normalizer_thompsonCenter (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (thompsonCenter (G := G) S : Set G) := by
  classical
  let J : Subgroup G := thompsonSubgroup (G := G) S
  have hJ_map_eq :
      ∀ g ∈ Subgroup.normalizer (S : Set G), J.map (MulAut.conj g).toMonoidHom = J := by
    intro g hg
    let e : G ≃* G := MulAut.conj g
    have himage :
        (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S =
          thompsonAbelianSubgroups (G := G) S := by
      ext A
      constructor
      · rintro ⟨B, hB, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp hg _).1 (hB.1 hy)
        · let : IsMulCommutative B := hB.2.1
          exact Subgroup.map_isMulCommutative (H := B) e.toMonoidHom
        · intro C hC hCcomm
          have hCpre_le : C.map e.symm.toMonoidHom ≤ S := by
            intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
              (Subgroup.normalizer (S : Set G)).inv_mem hg
            simpa [e] using (Subgroup.mem_normalizer_iff.mp hginv _).1 (hC hy)
          have hCpre_comm : IsMulCommutative (C.map e.symm.toMonoidHom) := by
            let : IsMulCommutative C := hCcomm
            exact Subgroup.map_isMulCommutative (H := C) e.symm.toMonoidHom
          have hBmax := hB.2.2 (C.map e.symm.toMonoidHom) hCpre_le hCpre_comm
          calc
            Nat.card C = Nat.card (C.map e.symm.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.symm.injective
            _ ≤ Nat.card B := hBmax
            _ = Nat.card (B.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := B) e.injective
      · intro hA
        refine ⟨A.map e.symm.toMonoidHom, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
              (Subgroup.normalizer (S : Set G)).inv_mem hg
            simpa [e] using (Subgroup.mem_normalizer_iff.mp hginv _).1 (hA.1 hy)
          · let : IsMulCommutative A := hA.2.1
            exact Subgroup.map_isMulCommutative (H := A) e.symm.toMonoidHom
          · intro C hC hCcomm
            have hCpre_le : C.map e.toMonoidHom ≤ S := by
              intro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
              exact (Subgroup.mem_normalizer_iff.mp hg _).1 (hC hy)
            have hCpre_comm : IsMulCommutative (C.map e.toMonoidHom) := by
              let : IsMulCommutative C := hCcomm
              exact Subgroup.map_isMulCommutative (H := C) e.toMonoidHom
            have hAmax := hA.2.2 (C.map e.toMonoidHom) hCpre_le hCpre_comm
            calc
              Nat.card C = Nat.card (C.map e.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := C) e.injective
              _ ≤ Nat.card A := hAmax
              _ = Nat.card (A.map e.symm.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := A) e.symm.injective
        · ext x
          simp
    calc
      J.map (MulAut.conj g).toMonoidHom
          = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) S)) := rfl
      _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S) := by
        simp
      _ = J := by
        simpa [J, thompsonSubgroup] using congrArg sSup himage
  have hconj_mem :
      ∀ g ∈ Subgroup.normalizer (S : Set G),
        ∀ z ∈ thompsonCenter (G := G) S,
          g * z * g⁻¹ ∈ thompsonCenter (G := G) S := by
    intro g hg z hz
    refine ⟨?_, ?_⟩
    · have hzJ : z ∈ J := by
        simpa [thompsonCenter, centerIn, J] using hz.1
      have hzmap : g * z * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzJ
      rwa [hJ_map_eq g hg] at hzmap
    · exact Subgroup.mem_centralizer_iff.mpr <| by
        intro y hy
        have hy' : g⁻¹ * y * g ∈ J := by
          have hymap :
              g⁻¹ * y * g ∈ J.map (MulAut.conj g⁻¹).toMonoidHom := by
            simpa [J] using
              (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hy)
          rwa [hJ_map_eq g⁻¹ ((Subgroup.normalizer (S : Set G)).inv_mem hg)] at hymap
        have hzcent :
            z ∈ Subgroup.centralizer (J : Set G) := by
          simpa [thompsonCenter, centerIn, J] using hz.2
        have hcomm := (Subgroup.mem_centralizer_iff.mp hzcent _ hy')
        have hcomm' := congrArg (fun x : G => g * x * g⁻¹) hcomm
        simpa [mul_assoc] using hcomm'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact hconj_mem g hg z hz
  · intro hz
    have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normalizer (S : Set G)).inv_mem hg
    have hz' := hconj_mem g⁻¹ hginv (g * z * g⁻¹) hz
    simpa [mul_assoc] using hz'

omit [Fact (Nat.Prime p)] in
private theorem CFSG.thompsonCenter_le_map_of_mem_thompsonAbelianSubgroups
    (P : Sylow p G) {A : Subgroup P}
    (hA : A ∈ thompsonAbelianSubgroups (G := P) (⊤ : Subgroup P)) :
    thompsonCenter (G := G) (P : Subgroup G) ≤ A.map P.toSubgroup.subtype := by
  classical
  let Z : Subgroup P := (thompsonCenter (G := G) (P : Subgroup G)).subgroupOf (P : Subgroup G)
  have hAimage :
      A.map P.toSubgroup.subtype ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) := by
    refine ⟨by simpa using (Subgroup.map_subtype_le (H := (P : Subgroup G)) (K := A)), ?_, ?_⟩
    · let : IsMulCommutative A := hA.2.1
      exact Subgroup.map_isMulCommutative (H := A) P.toSubgroup.subtype
    · intro B hB hBcomm
      let B' : Subgroup P := B.subgroupOf (P : Subgroup G)
      have hAmax := hA.2.2 B' (by simp) (by
        let : IsMulCommutative B := hBcomm
        infer_instance)
      calc
        Nat.card B = Nat.card B' := by
          simpa [B', Subgroup.map_subgroupOf_eq_of_le hB] using
            (Subgroup.card_subtype (P : Subgroup G) B')
        _ ≤ Nat.card A := hAmax
        _ = Nat.card (A.map P.toSubgroup.subtype) := by
          symm
          exact Subgroup.card_map_of_injective (K := A) P.toSubgroup.subtype_injective
  have hZ_normal : Z.Normal := by
    simpa [Z] using thompsonCenter_normal_subgroupOf_sylow (G := G) (p := p) P
  have hZ_cent_A : Z ≤ Subgroup.centralizer (A : Set P) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hz' : ((z : P) : G) ∈ thompsonCenter (G := G) (P : Subgroup G) := hz
    have hzcent :
        ((z : P) : G) ∈ Subgroup.centralizer (thompsonSubgroup (G := G) (P : Subgroup G) : Set G) := by
      simpa [thompsonCenter, centerIn] using hz'.2
    have haJ : ((a : P) : G) ∈ thompsonSubgroup (G := G) (P : Subgroup G) := by
      exact le_sSup hAimage (Subgroup.mem_map_of_mem P.toSubgroup.subtype ha)
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzcent _ haJ
  let B : Subgroup P := A ⊔ Z
  have hB_comm : IsMulCommutative B := by
    let hAcomm : IsMulCommutative A := hA.2.1
    let hZcomm : IsMulCommutative Z := by
      let : IsMulCommutative (thompsonCenter (G := G) (P : Subgroup G)) :=
        thompsonCenter_isMulCommutative (G := G) (P : Subgroup G)
      infer_instance
    refine (Subgroup.le_centralizer_iff_isMulCommutative (K := B)).1 ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases (Subgroup.mem_sup_of_normal_right (x := u) (s := A) (t := Z)).1 hu with
      ⟨a1, ha1, z1, hz1, rfl⟩
    rcases (Subgroup.mem_sup_of_normal_right (x := v) (s := A) (t := Z)).1 hv with
      ⟨a2, ha2, z2, hz2, rfl⟩
    symm
    have hz1a2 : z1 * a2 = a2 * z1 :=
      (Subgroup.mem_centralizer_iff.mp (hZ_cent_A hz1) a2 ha2).symm
    have hz2a1 : z2 * a1 = a1 * z2 :=
      (Subgroup.mem_centralizer_iff.mp (hZ_cent_A hz2) a1 ha1).symm
    have ha1a2 : a1 * a2 = a2 * a1 := by
      simpa using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := A)).comm ⟨a1, ha1⟩ ⟨a2, ha2⟩)
    have hz1z2 : z1 * z2 = z2 * z1 := by
      simpa using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := Z)).comm ⟨z1, hz1⟩ ⟨z2, hz2⟩)
    calc
      (a1 * z1) * (a2 * z2) = a1 * a2 * (z1 * z2) := by
        rw [mul_assoc, ← mul_assoc z1 a2 z2, hz1a2]
        simp [mul_assoc]
      _ = a2 * a1 * (z2 * z1) := by rw [ha1a2, hz1z2]
      _ = a2 * (z2 * (a1 * z1)) := by
        have hinner : a1 * (z2 * z1) = z2 * (a1 * z1) := by
          calc
            a1 * (z2 * z1) = (a1 * z2) * z1 := by simp [mul_assoc]
            _ = (z2 * a1) * z1 := by rw [← hz2a1]
            _ = z2 * (a1 * z1) := by simp [mul_assoc]
        rw [mul_assoc, hinner]
      _ = (a2 * z2) * (a1 * z1) := by
        simp [mul_assoc]
  have hB_card_le : Nat.card B ≤ Nat.card A := hA.2.2 B (by simp) hB_comm
  have hB_eq_A : B = A := by
    symm
    exact Subgroup.eq_of_le_of_card_ge le_sup_left hB_card_le
  have hZ_le_A : Z ≤ A := by
    intro z hz
    have hzB : z ∈ B := Subgroup.mem_sup_right hz
    simpa [B, hB_eq_A] using hzB
  intro z hz
  let zP : P := ⟨z, thompsonCenter_le (G := G) (P : Subgroup G) hz⟩
  have hzZ : zP ∈ Z := hz
  have hzA : zP ∈ A := hZ_le_A hzZ
  exact Subgroup.mem_map_of_mem P.toSubgroup.subtype hzA

private theorem CFSG.thompsonAbelianSubgroups_nonempty (P : Subgroup G) :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (G := G) P := by
  classical
  let := Fintype.ofFinite G
  let S : Set (Subgroup G) := {A : Subgroup G | A ≤ P ∧ IsMulCommutative A}
  have hS_nonempty : S.Nonempty := by
    refine ⟨⊥, ?_⟩
    constructor
    · exact bot_le
    · infer_instance
  have hS_finite : S.Finite := by
    exact Set.toFinite S
  obtain ⟨A, hAS, hAmax⟩ :=
    hS_finite.exists_maximalFor (f := fun A : Subgroup G => Nat.card A) S hS_nonempty
  rcases hAS with ⟨hA_le_P, hAcomm⟩
  refine ⟨A, hA_le_P, hAcomm, ?_⟩
  intro B hB_le_P hBcomm
  by_cases hAB : Nat.card A ≤ Nat.card B
  · exact hAmax ⟨hB_le_P, hBcomm⟩ hAB
  · exact Nat.le_of_not_ge hAB

omit [Finite G] in
private theorem CFSG.thompsonAbelianSubgroups_subset_of_contains_mem
    {P R : Subgroup G} (hR_le_P : R ≤ P) {A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hA_le_R : A ≤ R) :
    ∀ {B : Subgroup G},
      B ∈ thompsonAbelianSubgroups (G := G) R →
        B ∈ thompsonAbelianSubgroups (G := G) P := by
  intro B hB
  refine ⟨hB.1.trans hR_le_P, hB.2.1, ?_⟩
  intro C hC hCcomm
  have hBmax := hB.2.2 A hA_le_R hA.2.1
  have hAmax := hA.2.2 C hC hCcomm
  exact hAmax.trans hBmax

omit [Finite G] in
private theorem CFSG.thompsonSubgroup_le_of_mem_thompsonAbelianSubgroups
    {P R : Subgroup G} (hR_le_P : R ≤ P) {A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hA_le_R : A ≤ R) :
    thompsonSubgroup (G := G) R ≤ thompsonSubgroup (G := G) P := by
  refine sSup_le ?_
  intro B hB
  exact le_sSup <|
    thompsonAbelianSubgroups_subset_of_contains_mem (G := G) hR_le_P hA hA_le_R hB

omit [Finite G] in
private theorem CFSG.thompsonCenter_le_of_mem_thompsonAbelianSubgroups
    {P R : Subgroup G} (hR_le_P : R ≤ P) {A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hZ_le_A : thompsonCenter (G := G) P ≤ A)
    (hA_le_R : A ≤ R) :
    thompsonCenter (G := G) P ≤ thompsonCenter (G := G) R := by
  let JP : Subgroup G := thompsonSubgroup (G := G) P
  let JR : Subgroup G := thompsonSubgroup (G := G) R
  have hJR_le_JP : JR ≤ JP :=
    thompsonSubgroup_le_of_mem_thompsonAbelianSubgroups (G := G) hR_le_P hA hA_le_R
  have hAinR : A ∈ thompsonAbelianSubgroups (G := G) R := by
    refine ⟨hA_le_R, hA.2.1, ?_⟩
    intro B hB hBcomm
    exact hA.2.2 B (hB.trans hR_le_P) hBcomm
  have hA_le_JR : A ≤ JR := le_sSup hAinR
  intro z hz
  refine ⟨?_, ?_⟩
  · exact hA_le_JR (hZ_le_A hz)
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hzcent :
        z ∈ Subgroup.centralizer (JP : Set G) := by
      simpa [thompsonCenter, centerIn, JP] using hz.2
    exact (Subgroup.mem_centralizer_iff.mp hzcent) y (hJR_le_JP hy)

omit [Finite G] in
private theorem CFSG.thompsonAbelianSubgroups_mem_of_le
    {P R A : Subgroup G} (hR_le_P : R ≤ P)
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hA_le_R : A ≤ R) :
    A ∈ thompsonAbelianSubgroups (G := G) R := by
  refine ⟨hA_le_R, hA.2.1, ?_⟩
  intro B hB hBcomm
  exact hA.2.2 B (hB.trans hR_le_P) hBcomm

private theorem CFSG.thompsonSubgroup_eq_of_le
    {P R : Subgroup G} (hR_le_P : R ≤ P)
    (hJP_le_R : thompsonSubgroup (G := G) P ≤ R) :
    thompsonSubgroup (G := G) R = thompsonSubgroup (G := G) P := by
  apply le_antisymm
  · obtain ⟨A, hA⟩ := thompsonAbelianSubgroups_nonempty (G := G) P
    exact
      thompsonSubgroup_le_of_mem_thompsonAbelianSubgroups (G := G) hR_le_P hA
        ((le_sSup hA).trans hJP_le_R)
  · refine sSup_le ?_
    intro A hA
    exact
      le_sSup <|
        thompsonAbelianSubgroups_mem_of_le (G := G) hR_le_P hA
          ((le_sSup hA).trans hJP_le_R)

private theorem CFSG.thompsonCenter_eq_of_le
    {P R : Subgroup G} (hR_le_P : R ≤ P)
    (hJP_le_R : thompsonSubgroup (G := G) P ≤ R) :
    thompsonCenter (G := G) R = thompsonCenter (G := G) P := by
  rw [thompsonCenter, thompsonCenter, thompsonSubgroup_eq_of_le (G := G) hR_le_P hJP_le_R]

private theorem CFSG.thompsonAbelianSubgroups_centralizer_eq
    {P A : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P) :
    subgroupCentralizerIn' P A = A := by
  apply le_antisymm
  · intro x hx
    let B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {x})
    have hB_le_P : B ≤ P := by
      refine (Subgroup.closure_le (K := P)).2 ?_
      intro y hy
      rcases hy with hyA | rfl
      · exact hA.1 hyA
      · exact hx.2
    have hB_comm : IsMulCommutative B := by
      change IsMulCommutative (Subgroup.closure ((A : Set G) ∪ {x}))
      let : IsMulCommutative A := hA.2.1
      exact Subgroup.isMulCommutative_closure (k := ((A : Set G) ∪ {x})) <| by
        intro y hy z hz _
        rcases hy with hyA | rfl
        · rcases hz with hzA | rfl
          · exact setLike_mul_comm (s := A) hyA hzA
          · exact Subgroup.mem_centralizer_iff.mp hx.1 _ hyA
        · rcases hz with hzA | rfl
          · exact (Subgroup.mem_centralizer_iff.mp hx.1 _ hzA).symm
          · simp
    have hB_card_le : Nat.card B ≤ Nat.card A := hA.2.2 B hB_le_P hB_comm
    have hA_le_B : A ≤ B := by
      intro y hy
      exact Subgroup.subset_closure (Or.inl hy)
    have hB_eq_A : A = B := Subgroup.eq_of_le_of_card_ge hA_le_B hB_card_le
    have hxB : x ∈ B := Subgroup.subset_closure (Or.inr (by simp))
    rw [← hB_eq_A] at hxB
    exact hxB
  · intro x hx
    refine ⟨?_, hA.1 hx⟩
    exact ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1) hx

private theorem CFSG.replacementCommChain_le_of_succ_eq_bot
    {P B A : Subgroup G} [B.Normal]
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hB_le_P : B ≤ P) {n : ℕ}
    (hsucc : replacementCommChain B A (n + 1) = ⊥) :
    replacementCommChain B A n ≤ A := by
  have hcent : replacementCommChain B A n ≤ Subgroup.centralizer (A : Set G) := by
    exact
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 <| by
        simpa [replacementCommChain_succ] using hsucc
  have hleP : replacementCommChain B A n ≤ P := by
    exact (replacementCommChain_le_left B A n).trans hB_le_P
  intro x hx
  have hx' : x ∈ subgroupCentralizerIn' P A := ⟨hcent hx, hleP hx⟩
  rwa [thompsonAbelianSubgroups_centralizer_eq (G := G) hA] at hx'

omit [Finite G] in
private theorem CFSG.inf_le_centralizer_commutator_of_commutator_le
    {P B A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P)
    (hBB_le_A : ⁅B, B⁆ ≤ A) :
    A ⊓ B ≤ Subgroup.centralizer (((⁅B, A⁆ : Subgroup G) : Set G)) := by
  have hAA_bot : ⁅A, A⁆ = ⊥ := by
    exact
      (Subgroup.commutator_eq_bot_iff_le_centralizer).2
        ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
  have h1bot : ⁅⁅A ⊓ B, A⁆, B⁆ = ⊥ := by
    apply le_antisymm
    · calc
        ⁅⁅A ⊓ B, A⁆, B⁆ ≤ ⁅⁅A, A⁆, B⁆ := by
          exact Subgroup.commutator_mono (Subgroup.commutator_mono inf_le_left le_rfl) le_rfl
        _ ≤ ⁅⊥, B⁆ := by
          exact Subgroup.commutator_mono (by simp [hAA_bot]) le_rfl
        _ = ⊥ := by simp
    · exact bot_le
  have h2bot : ⁅⁅B, A ⊓ B⁆, A⁆ = ⊥ := by
    apply le_antisymm
    · calc
        ⁅⁅B, A ⊓ B⁆, A⁆ ≤ ⁅⁅B, B⁆, A⁆ := by
          exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl inf_le_right) le_rfl
        _ ≤ ⁅A, A⁆ := by
          exact Subgroup.commutator_mono hBB_le_A le_rfl
        _ = ⊥ := by
          exact hAA_bot
    · exact bot_le
  have hbot :
      ⁅⁅B, A⁆, A ⊓ B⁆ = ⊥ := by
    exact
      Subgroup.commutator_commutator_eq_bot_of_rotate
        (by simpa [Subgroup.commutator_comm] using h1bot)
        (by simpa [Subgroup.commutator_comm] using h2bot)
  rw [Subgroup.commutator_comm] at hbot
  exact
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hbot

private theorem CFSG.thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
    {P A B : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hB_le_P : B ≤ P) :
    B ≤ Subgroup.normalizer (A : Set G) ↔ ⁅⁅B, A⁆, A⁆ = ⊥ := by
  constructor
  · intro hB_norm
    have hBA_le_A : ⁅B, A⁆ ≤ A := by
      refine (Subgroup.commutator_le).2 ?_
      intro b hb a ha
      have hb_norm : b ∈ Subgroup.normalizer (A : Set G) := hB_norm hb
      have hba : b * a * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hb_norm a).1 ha
      rw [commutatorElement_def]
      simpa [mul_assoc] using A.mul_mem hba (A.inv_mem ha)
    have hA_le_centralizer_A :
        A ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2
      (hBA_le_A.trans hA_le_centralizer_A)
  · intro hcomm2
    have hBA_le_centralizer_A : ⁅B, A⁆ ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm2
    have hBA_le_P : ⁅B, A⁆ ≤ P := by
      exact (Subgroup.commutator_mono hB_le_P hA.1).trans (Subgroup.commutator_le_self P)
    have hBA_le_A : ⁅B, A⁆ ≤ A := by
      intro x hx
      have hx' : x ∈ subgroupCentralizerIn' P A := ⟨hBA_le_centralizer_A hx, hBA_le_P hx⟩
      rwa [thompsonAbelianSubgroups_centralizer_eq (G := G) hA] at hx'
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hcomm : ⁅b, a⁆ ∈ A := hBA_le_A (Subgroup.commutator_mem_commutator hb ha)
      rw [show b * a * b⁻¹ = ⁅b, a⁆ * a by simp [commutatorElement_def, mul_assoc]]
      exact A.mul_mem hcomm ha
    · intro hba
      have hbinv : b⁻¹ ∈ B := B.inv_mem hb
      have hcomm : ⁅b⁻¹, b * a * b⁻¹⁆ ∈ A :=
        hBA_le_A (Subgroup.commutator_mem_commutator hbinv hba)
      have : b⁻¹ * (b * a * b⁻¹) * b ∈ A := by
        rw [show b⁻¹ * (b * a * b⁻¹) * b = ⁅b⁻¹, b * a * b⁻¹⁆ * (b * a * b⁻¹) by
          simp [commutatorElement_def, mul_assoc]]
        exact A.mul_mem hcomm hba
      simpa [mul_assoc] using this

omit [Finite G] in
private theorem CFSG.commutator_lt_self_of_isSolvable_local (M : Subgroup G)
    [Group.IsSolvable (↥M)] [Nontrivial (↥M)] : ⁅M, M⁆ < M := by
  have hlt : commutator (↥M) < (⊤ : Subgroup (↥M)) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥M)
  have hlt' :
      (commutator (↥M)).map M.subtype < (⊤ : Subgroup (↥M)).map M.subtype := by
    exact
      (Subgroup.map_subtype_lt_map_subtype (G' := M) (H := commutator (↥M))
        (K := (⊤ : Subgroup (↥M)))).mpr hlt
  have htop_map : (⊤ : Subgroup (↥M)).map M.subtype = M := by
    simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
  simpa [Subgroup.map_subtype_commutator, htop_map] using hlt'

private theorem CFSG.replacementCommChain_two_ne_bot_of_not_normalizer
    {P B A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hB_le_P : B ≤ P)
    (hB_not_norm : ¬ B ≤ Subgroup.normalizer (A : Set G)) :
    replacementCommChain B A 2 ≠ ⊥ := by
  intro htwo_bot
  apply hB_not_norm
  exact
    (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
      (G := G) (P := P) (A := A) (B := B) hA hB_le_P).2 <| by
        simpa [replacementCommChain_succ, replacementCommChain_zero] using htwo_bot

theorem CFSG.thompsonReplacement_base
    {P A : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P)
    {x : G} (hxP : x ∈ P)
    (hM_comm :
      IsMulCommutative
        ((Subgroup.closure {g : G | ∃ u ∈ A, ⁅x, u⁆ = g} : Subgroup G))) :
    let M : Subgroup G := Subgroup.closure {g : G | ∃ u ∈ A, ⁅x, u⁆ = g}
    let C : Subgroup G := subgroupCentralizerIn' A M
    M ⊔ C ∈ thompsonAbelianSubgroups (G := G) P := by
  classical
  let M : Subgroup G := Subgroup.closure {g : G | ∃ u ∈ A, ⁅x, u⁆ = g}
  let C : Subgroup G := subgroupCentralizerIn' A M
  refine ⟨?_, ?_, ?_⟩
  · have hM_le_P : M ≤ P := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      exact
        (Subgroup.commutator_le_self P)
          (Subgroup.commutator_mem_commutator hxP (hA.1 hu))
    exact sup_le hM_le_P (fun y hy => hA.1 hy.2)
  · rw [Subgroup.sup_eq_closure]
    let : IsMulCommutative A := hA.2.1
    exact Subgroup.isMulCommutative_closure
      (k := (((M : Subgroup G) : Set G) ∪ ((C : Subgroup G) : Set G))) <| by
        intro y hy z hz _
        rcases hy with hyM | hyC
        · rcases hz with hzM | hzC
          · exact
              setLike_mul_comm
                (s := M) hyM hzM
          · exact Subgroup.mem_centralizer_iff.mp hzC.1 _ hyM
        · rcases hz with hzM | hzC
          · exact (Subgroup.mem_centralizer_iff.mp hyC.1 _ hzM).symm
          · exact
              setLike_mul_comm
                (s := A) hyC.2 hzC.2
  · intro B hB_le_P hB_comm
    have hB_card_le_A : Nat.card B ≤ Nat.card A := hA.2.2 B hB_le_P hB_comm
    have hA_card_le :
        Nat.card A ≤
          Nat.card ↥(M ⊔ C) := by
      let M0 : Subgroup G := M
      let C0 : Subgroup G := subgroupCentralizerIn' A M0
      have hM0_comm : IsMulCommutative ↥M0 := by
        simpa [M0] using hM_comm
      change Nat.card A ≤ Nat.card ↥(M0 ⊔ C0)
      have hC0_le_A : C0 ≤ A := by
        intro y hy
        exact hy.2
      let D0 : Subgroup G := subgroupCentralizerIn' M0 A
      have hM0_le_P : M0 ≤ P := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with ⟨u, hu, rfl⟩
        exact
          (Subgroup.commutator_le_self P)
            (Subgroup.commutator_mem_commutator hxP (hA.1 hu))
      have hD0_le_M0 : D0 ≤ M0 := by
        intro y hy
        exact hy.2
      have hcentP_eq_A : subgroupCentralizerIn' P A = A :=
        thompsonAbelianSubgroups_centralizer_eq (G := G) hA
      have hA_le_centA : A ≤ Subgroup.centralizer (A : Set G) :=
        (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1
      have hD0_le_A : D0 ≤ A := by
        intro y hy
        have hyPA : y ∈ subgroupCentralizerIn' P A := by
          exact ⟨hy.1, hM0_le_P hy.2⟩
        simpa [hcentP_eq_A] using hyPA
      have hD0_eq_inf : D0 = M0 ⊓ C0 := by
        ext y
        constructor
        · intro hy
          refine ⟨hy.2, ⟨?_, hD0_le_A hy⟩⟩
          exact ((Subgroup.le_centralizer_iff_isMulCommutative (K := M0)).2 hM0_comm) hy.2
        · rintro ⟨hyM, hyC0⟩
          exact ⟨hA_le_centA hyC0.2, hyM⟩
      have hquot_le :
          Nat.card (A ⧸ C0.subgroupOf A) ≤ Nat.card (M0 ⧸ D0.subgroupOf M0) := by
        classical
        let : IsMulCommutative A := hA.2.1
        have hcomm_swap {a c : G} (ha : a ∈ A) (hc : c ∈ A)
            (haxc : ⁅⁅x, a⁆, c⁆ = 1) :
            ⁅⁅x, c⁆, a⁆ = 1 := by
          have hxaM0 : ⁅x, a⁆ ∈ M0 := by
            exact Subgroup.subset_closure ⟨a, ha, rfl⟩
          have hxcM0 : ⁅x, c⁆ ∈ M0 := by
            exact Subgroup.subset_closure ⟨c, hc, rfl⟩
          have hac : Commute a c := by
            exact setLike_mul_comm (s := A) ha hc
          let s : G := x * a * x⁻¹
          let t : G := x * c * x⁻¹
          let β : G := ⁅x, a⁆
          let δ : G := ⁅x, c⁆
          have hs_eq : s = β * a := by
            dsimp [s, β]
            simp [commutatorElement_def, mul_assoc]
          have hβ_eq : β = s * a⁻¹ := by
            dsimp [s, β]
            simp [commutatorElement_def, mul_assoc]
          have hδ_eq : δ = t * c⁻¹ := by
            dsimp [t, δ]
            simp [commutatorElement_def, mul_assoc]
          have hβc : Commute β c := commutatorElement_eq_one_iff_commute.mp haxc
          have hs_c : Commute s c := by
            change s * c = c * s
            calc
              s * c = (β * a) * c := by rw [hs_eq]
              _ = β * (a * c) := by simp [mul_assoc]
              _ = β * (c * a) := by rw [hac.eq]
              _ = (β * c) * a := by simp [mul_assoc]
              _ = (c * β) * a := by rw [hβc.eq]
              _ = c * (β * a) := by simp [mul_assoc]
              _ = c * s := by rw [hs_eq]
          have hst : Commute s t := by
            change s * t = t * s
            calc
              s * t = (x * a * x⁻¹) * (x * c * x⁻¹) := by rfl
              _ = x * a * c * x⁻¹ := by simp [mul_assoc]
              _ = x * (a * c) * x⁻¹ := by simp [mul_assoc]
              _ = x * (c * a) * x⁻¹ := by rw [hac.eq]
              _ = x * c * a * x⁻¹ := by simp [mul_assoc]
              _ = (x * c * x⁻¹) * (x * a * x⁻¹) := by simp [mul_assoc]
              _ = t * s := by rfl
          have hβδ : Commute β δ := by
            dsimp [β, δ]
            exact setLike_mul_comm (s := M0) hxaM0 hxcM0
          have hAinvCinv : Commute a⁻¹ c⁻¹ := (hac.inv_left).inv_right
          have hAinv_t_cinv : a⁻¹ * t * c⁻¹ = t * a⁻¹ * c⁻¹ := by
            have hs_eq' :
                s * (a⁻¹ * t * c⁻¹) = s * (t * a⁻¹ * c⁻¹) := by
              calc
                s * (a⁻¹ * t * c⁻¹) = (s * a⁻¹) * (t * c⁻¹) := by simp [mul_assoc]
                _ = β * δ := by rw [hβ_eq, hδ_eq]
                _ = δ * β := by rw [hβδ.eq]
                _ = (t * c⁻¹) * (s * a⁻¹) := by rw [hδ_eq, hβ_eq]
                _ = t * (c⁻¹ * s) * a⁻¹ := by simp [mul_assoc]
                _ = t * (s * c⁻¹) * a⁻¹ := by rw [(hs_c.inv_right).eq]
                _ = (t * s) * c⁻¹ * a⁻¹ := by simp [mul_assoc]
                _ = (s * t) * c⁻¹ * a⁻¹ := by rw [hst.eq]
                _ = s * (t * c⁻¹ * a⁻¹) := by simp [mul_assoc]
                _ = s * (t * (c⁻¹ * a⁻¹)) := by simp [mul_assoc]
                _ = s * (t * (a⁻¹ * c⁻¹)) := by rw [← hAinvCinv.eq]
                _ = s * (t * a⁻¹ * c⁻¹) := by simp [mul_assoc]
            exact mul_left_cancel hs_eq'
          have hAinv_t : a⁻¹ * t = t * a⁻¹ := by
            have hmul := congrArg (fun z => z * c) hAinv_t_cinv
            simpa [mul_assoc] using hmul
          have ht_a : Commute t a := by
            have htaInv : Commute a⁻¹ t := by
              change a⁻¹ * t = t * a⁻¹
              rw [hAinv_t]
            simpa using htaInv.inv_left.symm
          have hcInv_a : c⁻¹ * a = a * c⁻¹ := by
            simpa using (hac.inv_right.symm.eq)
          have hδa : Commute δ a := by
            change δ * a = a * δ
            calc
              δ * a = (t * c⁻¹) * a := by rw [hδ_eq]
              _ = t * (c⁻¹ * a) := by simp [mul_assoc]
              _ = t * (a * c⁻¹) := by rw [hcInv_a]
              _ = (t * a) * c⁻¹ := by simp [mul_assoc]
              _ = (a * t) * c⁻¹ := by rw [ht_a.eq]
              _ = a * (t * c⁻¹) := by simp [mul_assoc]
              _ = a * δ := by rw [hδ_eq]
          exact commutatorElement_eq_one_iff_commute.mpr hδa
        have hcommImage_mem (a : A) : ⁅x, (a : G)⁆ ∈ M0 := by
          exact Subgroup.subset_closure ⟨(a : G), a.2, rfl⟩
        let commImage : A → M0 := fun a => ⟨⁅x, (a : G)⁆, hcommImage_mem a⟩
        have hcommImage_calc {u v : A} :
            (((commImage u : M0)⁻¹ * commImage v : M0) : G) =
              (u : G) * ⁅x, ((u : G)⁻¹ * (v : G))⁆ * (u : G)⁻¹ := by
          simp [commImage, commutatorElement_def, mul_assoc]
        have hxc_centA_of_mem {c : G} (hcC0 : c ∈ C0) :
            ⁅x, c⁆ ∈ Subgroup.centralizer (A : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have hcA : c ∈ A := hC0_le_A hcC0
          have hxaM0 : ⁅x, a⁆ ∈ M0 := by
            exact Subgroup.subset_closure ⟨a, ha, rfl⟩
          have haxc : ⁅⁅x, a⁆, c⁆ = 1 := by
            exact
              commutatorElement_eq_one_iff_commute.mpr
                (Subgroup.mem_centralizer_iff.mp hcC0.1 _ hxaM0)
          have hxca : ⁅⁅x, c⁆, a⁆ = 1 := hcomm_swap ha hcA haxc
          exact (commutatorElement_eq_one_iff_commute.mp hxca).symm.eq
        have hc_cent_M0_of_mem {c : G} (hcA : c ∈ A)
            (hxc_centA : ⁅x, c⁆ ∈ Subgroup.centralizer (A : Set G)) :
            c ∈ Subgroup.centralizer (M0 : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hyc : Commute y c := by
            refine
              Subgroup.closure_induction
                (p := fun z _ => Commute z c) ?_ ?_ ?_ ?_ hy
            · intro g hg
              rcases hg with ⟨a, ha, rfl⟩
              have hxca : ⁅⁅x, c⁆, a⁆ = 1 := by
                have hcomm : Commute ⁅x, c⁆ a := by
                  show ⁅x, c⁆ * a = a * ⁅x, c⁆
                  exact ((Subgroup.mem_centralizer_iff.mp hxc_centA) _ ha).symm
                exact commutatorElement_eq_one_iff_commute.mpr hcomm
              have haxc : ⁅⁅x, a⁆, c⁆ = 1 := by
                exact hcomm_swap hcA ha hxca
              exact commutatorElement_eq_one_iff_commute.mp haxc
            · exact Commute.one_left c
            · intro g₁ g₂ _ _ h₁ h₂
              show Commute (g₁ * g₂) c
              calc
                (g₁ * g₂) * c = g₁ * (g₂ * c) := by simp [mul_assoc]
                _ = g₁ * (c * g₂) := by rw [h₂.eq]
                _ = (g₁ * c) * g₂ := by simp [mul_assoc]
                _ = (c * g₁) * g₂ := by rw [h₁.eq]
                _ = c * (g₁ * g₂) := by simp [mul_assoc]
            · intro g _ h
              exact h.inv_left
          exact hyc.eq
        let f : A ⧸ C0.subgroupOf A → M0 ⧸ D0.subgroupOf M0 :=
          Quotient.map'
            commImage
            (by
              intro u v huv
              apply QuotientGroup.leftRel_apply.mpr
              change
                (((commImage u : M0)⁻¹ * commImage v : M0) ∈
                  D0.subgroupOf M0)
              have huv' : ((u : G)⁻¹ * (v : G)) ∈ C0 := by
                simpa [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] using huv
              have hxc_centA : ⁅x, ((u : G)⁻¹ * (v : G))⁆ ∈ Subgroup.centralizer (A : Set G) := by
                exact hxc_centA_of_mem huv'
              have hmemD0 :
                  (((commImage u : M0)⁻¹ * commImage v : M0) : G) ∈ D0 := by
                refine ⟨?_, ?_⟩
                · let c : G := (u : G)⁻¹ * (v : G)
                  have hcalc :
                      (((commImage u : M0)⁻¹ * commImage v : M0) : G) =
                        (u : G) * ⁅x, c⁆ * (u : G)⁻¹ := by
                    simpa [commImage, c] using (hcommImage_calc (u := u) (v := v))
                  have hu_centA : (u : G) ∈ Subgroup.centralizer (A : Set G) := hA_le_centA u.2
                  have hconj_cent :
                      (u : G) * ⁅x, c⁆ * (u : G)⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
                    exact (Subgroup.centralizer (A : Set G)).mul_mem
                      ((Subgroup.centralizer (A : Set G)).mul_mem hu_centA hxc_centA)
                      ((Subgroup.centralizer (A : Set G)).inv_mem hu_centA)
                  exact hcalc ▸ hconj_cent
                · simpa using (((commImage u : M0)⁻¹ * commImage v : M0).2)
              simpa [Subgroup.mem_subgroupOf] using hmemD0)
        have hf_inj : Function.Injective f := by
          intro q1 q2 hq
          refine Quotient.inductionOn₂' q1 q2 ?_ hq
          intro u v huv
          apply Quotient.sound
          apply QuotientGroup.leftRel_apply.mpr
          change (u⁻¹ * v : A) ∈ C0.subgroupOf A
          have huv' :
              ((commImage u : M0)⁻¹ * commImage v : M0) ∈
                D0.subgroupOf M0 := by
            simpa [QuotientGroup.leftRel_apply] using (Quotient.exact' huv)
          let c : G := (u : G)⁻¹ * (v : G)
          have hcA : c ∈ A := A.mul_mem (A.inv_mem u.2) v.2
          have hmemD0 :
              ((((commImage u : M0)⁻¹ * commImage v : M0) : M0) : G) ∈ D0 := by
            simpa [Subgroup.mem_subgroupOf] using huv'
          have hd_centA :
              ((((commImage u : M0)⁻¹ * commImage v : M0) : M0) : G) ∈
                Subgroup.centralizer (A : Set G) := hmemD0.1
          have hcalc :
              (((commImage u : M0)⁻¹ * commImage v : M0) : G) =
                (u : G) * ⁅x, c⁆ * (u : G)⁻¹ := by
            simpa [commImage, c] using (hcommImage_calc (u := u) (v := v))
          have hu_centA : (u : G) ∈ Subgroup.centralizer (A : Set G) := hA_le_centA u.2
          have hxc_cent : ⁅x, c⁆ ∈ Subgroup.centralizer (A : Set G) := by
            have : (u : G)⁻¹ *
                ((((commImage u : M0)⁻¹ * commImage v : M0) : M0) : G) *
                (u : G) ∈ Subgroup.centralizer (A : Set G) := by
              exact (Subgroup.centralizer (A : Set G)).mul_mem
                ((Subgroup.centralizer (A : Set G)).mul_mem
                  ((Subgroup.centralizer (A : Set G)).inv_mem hu_centA) hd_centA)
                hu_centA
            simpa [hcalc, mul_assoc] using this
          have hc_cent_M0 : c ∈ Subgroup.centralizer (M0 : Set G) := by
            exact hc_cent_M0_of_mem hcA hxc_cent
          exact ⟨hc_cent_M0, hcA⟩
        exact Nat.card_le_card_of_injective f hf_inj
      have hcardA :
          Nat.card A = Nat.card (A ⧸ C0.subgroupOf A) * Nat.card C0 := by
        have hcardA' :
            Nat.card A = Nat.card (A ⧸ C0.subgroupOf A) * Nat.card (C0.subgroupOf A) := by
          simpa using
            (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := C0.subgroupOf A))
        have hcardC0 : Nat.card (C0.subgroupOf A) = Nat.card C0 := by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := C0) (K := A) hC0_le_A).toEquiv
        rw [hcardA', hcardC0]
      have hcardMC :
          Nat.card ↥(M0 ⊔ C0) =
            Nat.card (M0 ⧸ D0.subgroupOf M0) * Nat.card C0 := by
        let H : Subgroup G := M0 ⊔ C0
        let K : Subgroup H := C0.subgroupOf H
        have hC0_le_centM0 : C0 ≤ Subgroup.centralizer (M0 : Set G) := by
          intro y hy
          exact hy.1
        have hM0_le_normC0 : M0 ≤ Subgroup.normalizer (C0 : Set G) := by
          intro y hy
          rw [Subgroup.mem_normalizer_iff]
          intro z
          constructor
          · intro hz
            have hyz : z * y = y * z :=
              (Subgroup.le_centralizer_iff).1 hC0_le_centM0 hy z hz
            have hconj : y * z * y⁻¹ = z := by
              calc
                y * z * y⁻¹ = z * y * y⁻¹ := by rw [hyz, mul_assoc]
                _ = z := by simp
            simpa [hconj] using hz
          · intro hz
            have hyz : (y * z * y⁻¹) * y = y * (y * z * y⁻¹) :=
              (Subgroup.le_centralizer_iff).1 hC0_le_centM0 hy (y * z * y⁻¹) hz
            have hz_eq : z = y * z * y⁻¹ := by
              simpa [mul_assoc] using congrArg (fun t => y⁻¹ * t) hyz
            rw [hz_eq]
            exact hz
        have hK_normal : K.Normal := by
          change (C0.subgroupOf (M0 ⊔ C0)).Normal
          exact
            (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := M0) (N := C0) hM0_le_normC0)
        let : K.Normal := hK_normal
        have hcardH :
            Nat.card H = Nat.card (H ⧸ K) * Nat.card K := by
          simpa [H, K] using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := K))
        have hcardK : Nat.card K = Nat.card C0 := by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := C0) (K := H) le_sup_right).toEquiv
        have hD0_eq_subgroupOf : D0.subgroupOf M0 = C0.subgroupOf M0 := by
          ext y
          simp [D0, hD0_eq_inf, Subgroup.mem_subgroupOf]
        let e : M0 ⧸ D0.subgroupOf M0 ↪ H ⧸ K :=
          (Subgroup.quotientEquivOfEq hD0_eq_subgroupOf).toEmbedding.trans
            (Subgroup.quotientSubgroupOfEmbeddingOfLE (H := C0) (s := M0) (t := H) le_sup_left)
        have he_surj : Function.Surjective e := by
          intro q
          refine Quotient.inductionOn' q ?_
          intro h
          have hh_sup : h ∈ (M0.subgroupOf H) ⊔ K := by
            have hsup_top : (M0.subgroupOf H) ⊔ K = ⊤ := by
              change (M0.subgroupOf (M0 ⊔ C0)) ⊔ C0.subgroupOf (M0 ⊔ C0) = ⊤
              rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
              simp
            rw [hsup_top]
            simp
          rcases (Subgroup.mem_sup_of_normal_right (s := M0.subgroupOf H) (t := K) (x := h)).1 hh_sup with
            ⟨m, hmM, c, hcK, hmc⟩
          have hmM0 : (m : G) ∈ M0 := by
            simpa [Subgroup.mem_subgroupOf] using hmM
          refine ⟨QuotientGroup.mk (⟨(m : G), hmM0⟩ : M0), ?_⟩
          change
            ((Subgroup.quotientSubgroupOfEmbeddingOfLE (H := C0) (s := M0) (t := H) le_sup_left)
              ((Subgroup.quotientEquivOfEq hD0_eq_subgroupOf)
                (QuotientGroup.mk (⟨(m : G), hmM0⟩ : M0))) = QuotientGroup.mk h)
          rw [Subgroup.quotientEquivOfEq_mk,
            Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk (H := C0) (h := le_sup_left)
            (g := (⟨(m : G), hmM0⟩ : M0))]
          apply Quotient.sound
          apply (QuotientGroup.leftRel_apply).mpr
          have hm_eq : (Subgroup.inclusion le_sup_left (⟨(m : G), hmM0⟩ : M0) : H) = m := by
            ext
            rfl
          rw [hm_eq, ← hmc]
          simpa [K, Subgroup.mem_subgroupOf]
        have hcardQ : Nat.card (H ⧸ K) = Nat.card (M0 ⧸ D0.subgroupOf M0) := by
          exact Nat.card_congr
            (Equiv.ofBijective e.toFun (show Function.Bijective e.toFun from ⟨e.injective, he_surj⟩)).symm
        calc
          Nat.card ↥(M0 ⊔ C0) = Nat.card (H ⧸ K) * Nat.card K := hcardH
          _ = Nat.card (M0 ⧸ D0.subgroupOf M0) * Nat.card C0 := by
            rw [hcardQ, hcardK]
      calc
        Nat.card A = Nat.card (A ⧸ C0.subgroupOf A) * Nat.card C0 := hcardA
        _ ≤ Nat.card (M0 ⧸ D0.subgroupOf M0) * Nat.card C0 := by
          exact Nat.mul_le_mul_right _ hquot_le
        _ = Nat.card ↥(M0 ⊔ C0) := hcardMC.symm
    exact hB_card_le_A.trans hA_card_le

theorem CFSG.pConstrained_quotient_pPrimeCore
    (hconstrained : PConstrainedGroup (G := G) p) :
    PConstrainedGroup (G := G ⧸ pPrimeCore p G) p := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let T : Sylow p (Op_p'p p G) := Classical.choice (Sylow.nonempty (p := p) (G := Op_p'p p G))
  let TG : Subgroup G := T.1.map (Op_p'p p G).subtype
  let Tbar : Subgroup (G ⧸ M) := TG.map q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hMnormal : M.Normal := by
    dsimp [M]
    infer_instance
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hTG_p : IsPGroup p TG := by
    simpa [TG] using
      (IsPGroup.map (p := p) (H := (T : Subgroup (Op_p'p p G))) T.isPGroup'
        (Op_p'p p G).subtype)
  have hTG_le_op : TG ≤ Op_p'p p G := by
    simpa [TG] using
      (Subgroup.map_subtype_le (H := Op_p'p p G) (K := (T : Subgroup (Op_p'p p G))))
  have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hTbar_le_pcore : Tbar ≤ pCore p (G ⧸ M) := by
    exact (Subgroup.map_mono hTG_le_op).trans hmap_op.le
  let f : Op_p'p p G →* pCore p (G ⧸ M) :=
    ((q.comp (Op_p'p p G).subtype)).codRestrict (pCore p (G ⧸ M)) (by
      intro x
      have hxmap : (q (x : G) : G ⧸ M) ∈ (Op_p'p p G).map q :=
        Subgroup.mem_map.mpr ⟨(x : G), x.property, rfl⟩
      exact hmap_op ▸ hxmap)
  have hf_surj : Function.Surjective f := by
    intro y
    rcases hqsurj y.1 with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · have hxmem : (q x : G ⧸ M) ∈ pCore p (G ⧸ M) := by
        simp [hx]
      simpa [Op_p'p, q, M] using hxmem
    · apply Subtype.ext
      simpa [f] using hx
  have hmapf_eq :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype = Tbar := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨(t : Op_p'p p G), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        exact congrArg Subtype.val htx
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨f t, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        simpa [f] using congrArg q htx
  have hT_not_dvd : ¬ p ∣ (T : Subgroup (Op_p'p p G)).index := T.not_dvd_index
  have hidx_dvd :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).index ∣
        (T : Subgroup (Op_p'p p G)).index :=
    Subgroup.index_map_dvd (H := (T : Subgroup (Op_p'p p G))) (f := f) hf_surj
  have hmapf_not_dvd : ¬ p ∣ (Subgroup.map f (T : Subgroup (Op_p'p p G))).index := by
    intro hp_dvd
    exact hT_not_dvd (hp_dvd.trans hidx_dvd)
  have hpcore_p : IsPGroup p (pCore p (G ⧸ M)) := pCore_isPGroup (p := p) (G := (G ⧸ M))
  have hpow_idx :
      ∃ n, (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = p ^ n := by
    exact IsPGroup.index (hG := hpcore_p) (H := Subgroup.map f (T : Subgroup (Op_p'p p G)))
  rcases hpow_idx with ⟨n, hn⟩
  have hnzero : n = 0 := by
    cases n with
    | zero => rfl
    | succ n =>
        exfalso
        apply hmapf_not_dvd
        refine ⟨p ^ n, ?_⟩
        rw [hn]
        simp [Nat.pow_succ, Nat.mul_comm]
  have hidx_one : (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = 1 := by
    rw [hn, hnzero]
    simp
  have hmapf_top : Subgroup.map f (T : Subgroup (Op_p'p p G)) = ⊤ :=
    (Subgroup.index_eq_one).1 hidx_one
  have hTbar_eq_pcore : Tbar = pCore p (G ⧸ M) := by
    have htop_map :
        (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype = pCore p (G ⧸ M) := by
      let K : Subgroup (G ⧸ M) := pCore p (G ⧸ M)
      have hsubtop : K.subgroupOf K = ⊤ := (Subgroup.subgroupOf_eq_top).2 le_rfl
      calc
        (⊤ : Subgroup K).map K.subtype = (K.subgroupOf K).map K.subtype := by rw [hsubtop]
        _ = K ⊓ K := Subgroup.subgroupOf_map_subtype (H := K) (K := K)
        _ = K := inf_eq_right.mpr le_rfl
    have hEq :
        Tbar = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
      calc
        Tbar = (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype := by
          exact hmapf_eq.symm
        _ = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
          rw [hmapf_top]
    exact hEq.trans htop_map
  have hM_le_comap_opmap : M ≤ Subgroup.comap q ((Op_p'p p G).map q) := by
    intro x hx
    change q x ∈ (Op_p'p p G).map q
    have hx1 : q x = 1 := by
      simpa [q, M] using hx
    rw [hx1]
    simp
  have hTG_sup : M ⊔ TG = Op_p'p p G := by
    calc
      M ⊔ TG = Subgroup.comap q (TG.map q) := by
        simp [q]
      _ = Subgroup.comap q Tbar := rfl
      _ = Subgroup.comap q (pCore p (G ⧸ M)) := by rw [hTbar_eq_pcore]
      _ = Subgroup.comap q ((Op_p'p p G).map q) := by rw [hmap_op]
      _ = Op_p'p p G := by
        rw [QuotientGroup.comap_map_mk' M (Op_p'p p G)]
        exact sup_eq_right.mpr <| by
          dsimp [M, Op_p'p]
          exact QuotientGroup.le_comap_mk' (pPrimeCore p G) (pCore p (G ⧸ pPrimeCore p G))
  have hcent_TG : Subgroup.centralizer (TG : Set G) ≤ Op_p'p p G :=
    hconstrained (Q := TG) hTG_p hTG_sup
  have hcent_Tbar :
      Subgroup.centralizer (Tbar : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    let : Fact (IsPGroup p (↥TG)) := ⟨hTG_p⟩
    have hcent_map :
        Subgroup.centralizer ((TG.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
          (Subgroup.centralizer (TG : Set G)).map q := by
      have h := centralizer_map_quotient_eq_map_centralizer (G := G) (p := p)
        (T := TG) (M := M) hMnormal hMcop
      change
        Subgroup.centralizer ((fun a : G => q a) '' (TG : Set G)) =
          (Subgroup.centralizer (TG : Set G)).map q at h
      simpa using h
    have hcent_map' :
        Subgroup.centralizer (Tbar : Set (G ⧸ M)) =
          (Subgroup.centralizer (TG : Set G)).map q := by
      simpa [Tbar] using hcent_map
    rw [hcent_map']
    exact (Subgroup.map_mono hcent_TG).trans hmap_op.le
  have hquot_core_bot : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hOp_eq_pCore_quot : Op_p'p p (G ⧸ M) = pCore p (G ⧸ M) := by
    simpa [hquot_core_bot] using
      (Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hquot_core_bot)
  intro Q hQ hQeq
  have hQ_eq_pcore : Q = pCore p (G ⧸ M) := by
    rw [hquot_core_bot, hOp_eq_pCore_quot, bot_sup_eq] at hQeq
    exact hQeq
  rw [hQ_eq_pcore]
  have hcent_pcore : Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    simpa [hTbar_eq_pcore] using hcent_Tbar
  exact hcent_pcore.trans <| by
    rw [← hOp_eq_pCore_quot]

set_option backward.isDefEq.respectTransparency false in
theorem CFSG.pStable_quotient_pPrimeCore
    (hstable : PStableGroup' (G := G) p) :
    PStableGroup' (G := G ⧸ pPrimeCore p G) p := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hM_normal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hM_normal
  intro Q A hMQ_normal hQp hAp hA_norm hcomm2
  let N : Subgroup (G ⧸ M) := Subgroup.normalizer (Q : Set (G ⧸ M))
  let C : Subgroup (G ⧸ M) := Subgroup.centralizer (Q : Set (G ⧸ M))
  let : (C.subgroupOf N).Normal := by
    have hCN : C ≤ N := by
      simpa [C, N] using (centralizer_le_normalizer (G := G ⧸ M) Q)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := C) (K := N) hCN).2
        (normalizer_le_normalizer_centralizer (G := G ⧸ M) Q)
  let Qbar : Subgroup G := Subgroup.comap q Q
  let Abar : Subgroup G := Subgroup.comap q A
  let Nbar : Subgroup G := Subgroup.comap q N
  have hquot_core_bot : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hQ_normal : Q.Normal := by
    rw [hquot_core_bot, bot_sup_eq] at hMQ_normal
    exact hMQ_normal
  have hAbar_le_Nbar : Abar ≤ Nbar := by
    intro a ha
    exact hA_norm ha
  let qQ : Qbar →* Q :=
    (q.comp Qbar.subtype).codRestrict Q (by
      intro x
      exact x.2)
  let qA : Abar →* A :=
    (q.comp Abar.subtype).codRestrict A (by
      intro x
      exact x.2)
  have hqQ_surj : Function.Surjective qQ := by
    intro x
    rcases QuotientGroup.mk'_surjective M x.1 with ⟨y, hy⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change q y ∈ Q
      rw [hy]
      exact x.2
    · apply Subtype.ext
      change q y = (x : G ⧸ M)
      exact hy
  have hqA_surj : Function.Surjective qA := by
    intro x
    rcases QuotientGroup.mk'_surjective M x.1 with ⟨y, hy⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change q y ∈ A
      rw [hy]
      exact x.2
    · apply Subtype.ext
      change q y = (x : G ⧸ M)
      exact hy
  obtain ⟨SQ⟩ := Sylow.nonempty (p := p) (G := Qbar)
  obtain ⟨SA⟩ := Sylow.nonempty (p := p) (G := Abar)
  let Q0 : Subgroup G := (SQ : Subgroup Qbar).map Qbar.subtype
  let A0 : Subgroup G := (SA : Subgroup Abar).map Abar.subtype
  have hQ0p : IsPGroup p Q0 := by
    simpa [Q0] using
      IsPGroup.map (p := p) (H := (SQ : Subgroup Qbar)) SQ.isPGroup' Qbar.subtype
  have hA0p : IsPGroup p A0 := by
    simpa [A0] using
      IsPGroup.map (p := p) (H := (SA : Subgroup Abar)) SA.isPGroup' Abar.subtype
  have hQ0_le_Qbar : Q0 ≤ Qbar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hA0_le_Abar : A0 ≤ Abar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hA0_le_Nbar : A0 ≤ Nbar := hA0_le_Abar.trans hAbar_le_Nbar
  have hSQ_map_top :
      ((SQ.mapSurjective (f := qQ) hqQ_surj : Sylow p Q) : Subgroup Q) = ⊤ := by
    apply le_antisymm le_top
    exact ((SQ.mapSurjective (f := qQ) hqQ_surj).is_maximal'
      (hQp.to_subgroup (⊤ : Subgroup Q)) le_top).le
  have hSA_map_top :
      ((SA.mapSurjective (f := qA) hqA_surj : Sylow p A) : Subgroup A) = ⊤ := by
    apply le_antisymm le_top
    exact ((SA.mapSurjective (f := qA) hqA_surj).is_maximal'
      (hAp.to_subgroup (⊤ : Subgroup A)) le_top).le
  have hQ0_map_q : Q0.map q = Q := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact hQ0_le_Qbar hy
    · intro x hx
      have hxSQ : (⟨x, hx⟩ : Q) ∈ ((SQ.mapSurjective (f := qQ) hqQ_surj : Sylow p Q) : Subgroup Q) := by
        rw [hSQ_map_top]
        simp
      rw [Sylow.coe_mapSurjective] at hxSQ
      rcases Subgroup.mem_map.mp hxSQ with ⟨z, hz, hzx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨z.1, Subgroup.mem_map_of_mem Qbar.subtype hz, ?_⟩
      exact congrArg Subtype.val hzx
  have hA0_map_q : A0.map q = A := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact hA0_le_Abar hy
    · intro x hx
      have hxSA : (⟨x, hx⟩ : A) ∈ ((SA.mapSurjective (f := qA) hqA_surj : Sylow p A) : Subgroup A) := by
        rw [hSA_map_top]
        simp
      rw [Sylow.coe_mapSurjective] at hxSA
      rcases Subgroup.mem_map.mp hxSA with ⟨z, hz, hzx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨z.1, Subgroup.mem_map_of_mem Abar.subtype hz, ?_⟩
      exact congrArg Subtype.val hzx
  have hQbar_eq_M_sup_Q0 : Qbar = M ⊔ Q0 := by
    calc
      Qbar = Subgroup.comap q Q := rfl
      _ = Subgroup.comap q (Q0.map q) := by rw [hQ0_map_q]
      _ = M ⊔ Q0 := by
            rw [QuotientGroup.comap_map_mk' M Q0]
  have hAbar_eq_M_sup_A0 : Abar = M ⊔ A0 := by
    calc
      Abar = Subgroup.comap q A := rfl
      _ = Subgroup.comap q (A0.map q) := by rw [hA0_map_q]
      _ = M ⊔ A0 := by
            rw [QuotientGroup.comap_map_mk' M A0]
  have hQbar_normal : Qbar.Normal := by
    exact Subgroup.Normal.comap hQ_normal q
  have hQbar_le_normalizer : Qbar ≤ Subgroup.normalizer (Qbar : Set G) := by
    exact Subgroup.le_normalizer
  have hA0_le_normalizer_Qbar : A0 ≤ Subgroup.normalizer (Qbar : Set G) := by
    intro a ha
    simpa using (Subgroup.normalizer_eq_top (H := Qbar) ▸ show a ∈ (⊤ : Subgroup G) from trivial)
  let A0N : Subgroup (Subgroup.normalizer (Qbar : Set G)) :=
    A0.subgroupOf (Subgroup.normalizer (Qbar : Set G))
  have hA0Np : IsPGroup p A0N := by
    exact hA0p.of_equiv (Subgroup.subgroupOfEquivOfLe hA0_le_normalizer_Qbar).symm
  have hfix_nonempty : (MulAction.fixedPoints A0N (Sylow p Qbar)).Nonempty := by
    exact hA0Np.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p Qbar)
      (not_dvd_card_sylow (p := p) (G := Qbar))
  obtain ⟨Sfix, hSfix⟩ := hfix_nonempty
  let Q1 : Subgroup G := (((Sfix : Sylow p Qbar) : Subgroup Qbar)).map Qbar.subtype
  have hQ1p : IsPGroup p Q1 := by
    simpa [Q1] using
      IsPGroup.map (p := p) (H := (((Sfix : Sylow p Qbar) : Subgroup Qbar)))
        ((Sfix : Sylow p Qbar).isPGroup') Qbar.subtype
  have hQ1_le_Qbar : Q1 ≤ Qbar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hSfix_fixed : ∀ a : A0N, a • (Sfix : Sylow p Qbar) = (Sfix : Sylow p Qbar) := by
    simpa [MulAction.mem_fixedPoints] using hSfix
  have hA0_le_normalizer_Q1 : A0 ≤ Subgroup.normalizer (Q1 : Set G) := by
    intro a ha
    let aN : Subgroup.normalizer (Qbar : Set G) := ⟨a, hA0_le_normalizer_Qbar ha⟩
    let a0N : A0N := ⟨aN, ha⟩
    have ha_fix : aN • (Sfix : Sylow p Qbar) = (Sfix : Sylow p Qbar) :=
      hSfix_fixed a0N
    have ha_fix_map :
        ((((aN • (Sfix : Sylow p Qbar)) : Sylow p Qbar) : Subgroup Qbar).map Qbar.subtype) = Q1 := by
      simpa [Q1] using
        congrArg (fun R : Sylow p Qbar => ((R : Subgroup Qbar).map Qbar.subtype)) ha_fix
    have hconj_comp :
        Qbar.subtype.comp (MulDistribMulAction.toMonoidHom (↥Qbar) aN) =
          (MulDistribMulAction.toMonoidHom G (ConjAct.toConjAct a)).comp Qbar.subtype := by
      ext y
      rfl
    have hconj_map :
        Subgroup.map (MulDistribMulAction.toMonoidHom G (ConjAct.toConjAct a))
            (Subgroup.map Qbar.subtype (((Sfix : Sylow p Qbar) : Subgroup Qbar))) =
          Subgroup.map Qbar.subtype
            (Subgroup.map (MulDistribMulAction.toMonoidHom (↥Qbar) aN)
              (((Sfix : Sylow p Qbar) : Subgroup Qbar))) := by
      rw [Subgroup.map_map, Subgroup.map_map, hconj_comp]
    refine (Subgroup.conjAct_pointwise_smul_iff (H := Q1) (g := a)).1 ?_
    simpa [Q1, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using
      hconj_map.trans ha_fix_map
  have hQ1_map_q : Q1.map q = Q := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact hQ1_le_Qbar hy
    · intro x hx
      have hxSfix :
          (⟨x, hx⟩ : Q) ∈ (((Sfix : Sylow p Qbar).mapSurjective (f := qQ) hqQ_surj : Sylow p Q) :
            Subgroup Q) := by
        have hSfix_map_top :
            (((Sfix : Sylow p Qbar).mapSurjective (f := qQ) hqQ_surj : Sylow p Q) : Subgroup Q) = ⊤ := by
          apply le_antisymm le_top
          exact (((Sfix : Sylow p Qbar).mapSurjective (f := qQ) hqQ_surj).is_maximal'
            (hQp.to_subgroup (⊤ : Subgroup Q)) le_top).le
        rw [hSfix_map_top]
        simp
      rw [Sylow.coe_mapSurjective] at hxSfix
      rcases Subgroup.mem_map.mp hxSfix with ⟨z, hz, hzx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨z.1, Subgroup.mem_map_of_mem Qbar.subtype hz, ?_⟩
      exact congrArg Subtype.val hzx
  have hQbar_eq_M_sup_Q1 : Qbar = M ⊔ Q1 := by
    calc
      Qbar = Subgroup.comap q Q := rfl
      _ = Subgroup.comap q (Q1.map q) := by rw [hQ1_map_q]
      _ = M ⊔ Q1 := by
            rw [QuotientGroup.comap_map_mk' M Q1]
  have hcomm_Q1A0_le_Q1 : ⁅Q1, A0⁆ ≤ Q1 := by
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    have hg₂_norm : g₂ ∈ Subgroup.normalizer (Q1 : Set G) := hA0_le_normalizer_Q1 hg₂
    have hg₂_conj : g₂ * g₁⁻¹ * g₂⁻¹ ∈ Q1 := by
      exact ((Subgroup.mem_normalizer_iff.mp hg₂_norm) g₁⁻¹).1 (Q1.inv_mem hg₁)
    rw [commutatorElement_def]
    simpa [mul_assoc] using Q1.mul_mem hg₁ hg₂_conj
  have hcomm2_lift : ⁅⁅Q1, A0⁆, A0⁆ = ⊥ := by
    let H : Subgroup G := ⁅⁅Q1, A0⁆, A0⁆
    have hH_le_Q1 : H ≤ Q1 := by
      refine Subgroup.commutator_le.mpr ?_
      intro g₁ hg₁ g₂ hg₂
      have hg₁Q1 : g₁ ∈ Q1 := hcomm_Q1A0_le_Q1 hg₁
      have hg₂_norm : g₂ ∈ Subgroup.normalizer (Q1 : Set G) := hA0_le_normalizer_Q1 hg₂
      have hg₂_conj : g₂ * g₁⁻¹ * g₂⁻¹ ∈ Q1 := by
        exact ((Subgroup.mem_normalizer_iff.mp hg₂_norm) g₁⁻¹).1 (Q1.inv_mem hg₁Q1)
      rw [commutatorElement_def]
      simpa [mul_assoc] using Q1.mul_mem hg₁Q1 hg₂_conj
    have hH_inj :
        Function.Injective ((q.comp H.subtype)) := by
      exact quotient_pPrimeCore_subgroupMap_injective (G := G) (p := p) (H := H)
        (hQ1p.to_le hH_le_Q1)
    have hH_map_bot : H.map q = ⊥ := by
      calc
        H.map q = (⁅⁅Q1, A0⁆, A0⁆).map q := rfl
        _ = ⁅⁅Q1.map q, A0.map q⁆, A0.map q⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_commutator]
        _ = ⁅⁅Q, A⁆, A⁆ := by rw [hQ1_map_q, hA0_map_q]
        _ = ⊥ := hcomm2
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : q x = 1 := by
      have hxmap : q x ∈ H.map q := Subgroup.mem_map_of_mem q hx
      rw [hH_map_bot] at hxmap
      simpa using hxmap
    have hx_sub_eq : (⟨x, hx⟩ : H) = 1 := by
      apply hH_inj
      simp [hx1]
    simpa using congrArg Subtype.val hx_sub_eq
  let N1 : Subgroup G := Subgroup.normalizer (Q1 : Set G)
  let C1 : Subgroup G := Subgroup.centralizer (Q1 : Set G)
  let : (C1.subgroupOf N1).Normal := by
    have hC1N1 : C1 ≤ N1 := by
      simpa [C1, N1] using (centralizer_le_normalizer (G := G) Q1)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := C1) (K := N1) hC1N1).2
        (normalizer_le_normalizer_centralizer (G := G) Q1)
  have hMQ1_normal : (M ⊔ Q1).Normal := by
    rw [← hQbar_eq_M_sup_Q1]
    exact hQbar_normal
  have hstable_up :
      ((A0.subgroupOf N1).map (QuotientGroup.mk' (C1.subgroupOf N1))) ≤
        pCore p (N1 ⧸ C1.subgroupOf N1) := by
    exact hstable (Q := Q1) (A := A0) hMQ1_normal hQ1p hA0p hA0_le_normalizer_Q1 hcomm2_lift
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hNmap : N1.map q = N := by
    let : Fact (IsPGroup p (↑Q1)) := ⟨hQ1p⟩
    have himage :
        ((fun a : G => q a) '' (Q1 : Set G)) = ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_map_of_mem q hy
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    have htmp :=
      normalizer_map_quotient_eq_map_normalizer
        (G := G) (p := p) Q1 M hM_normal hMcop
    change
      Subgroup.normalizer ((fun a : G => q a) '' (Q1 : Set G)) = N1.map q at htmp
    have htmp' :
        Subgroup.normalizer ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) = N1.map q := by
      rw [← himage]
      exact htmp
    simpa [N, hQ1_map_q] using htmp'.symm
  have hCmap : C1.map q = C := by
    let : Fact (IsPGroup p (↑Q1)) := ⟨hQ1p⟩
    have himage :
        ((fun a : G => q a) '' (Q1 : Set G)) = ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_map_of_mem q hy
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    have htmp :=
      centralizer_map_quotient_eq_map_centralizer
        (G := G) (p := p) (T := Q1) (M := M) hM_normal hMcop
    change
      Subgroup.centralizer ((fun a : G => q a) '' (Q1 : Set G)) = C1.map q at htmp
    have htmp' :
        Subgroup.centralizer ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) = C1.map q := by
      rw [← himage]
      exact htmp
    simpa [C, hQ1_map_q] using htmp'.symm
  let qN1 : N1 →* N :=
    (q.comp N1.subtype).codRestrict N (by
      intro x
      have hxmap : q x ∈ N1.map q := Subgroup.mem_map_of_mem q x.2
      rwa [hNmap] at hxmap)
  have hqN1_surj : Function.Surjective qN1 := by
    intro y
    have hy : (y : G ⧸ M) ∈ N1.map q := by
      simp [hNmap]
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [qN1] using hxy
  have hC1_le_comap_qN1 : C1.subgroupOf N1 ≤ (C.subgroupOf N).comap qN1 := by
    intro x hx
    change q ((x : N1) : G) ∈ C
    have hxmap : q ((x : N1) : G) ∈ C1.map q := by
      exact Subgroup.mem_map.mpr ⟨((x : N1) : G), hx, rfl⟩
    rwa [hCmap] at hxmap
  let φ : N1 ⧸ C1.subgroupOf N1 →* N ⧸ C.subgroupOf N :=
    QuotientGroup.map (N := C1.subgroupOf N1) (M := C.subgroupOf N) qN1 hC1_le_comap_qN1
  let SA : Subgroup (N1 ⧸ C1.subgroupOf N1) :=
    (A0.subgroupOf N1).map (QuotientGroup.mk' (C1.subgroupOf N1))
  let TA : Subgroup (N ⧸ C.subgroupOf N) :=
    (A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))
  have hφ_surj : Function.Surjective φ := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro z
    rcases hqN1_surj z with ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk' (C1.subgroupOf N1) x, ?_⟩
    simp [φ]
  have hSA_map_le : SA.map φ ≤ TA := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have haA : q ((a : N1) : G) ∈ A := by
      rw [← hA0_map_q]
      exact Subgroup.mem_map_of_mem q ha
    let aq : A.subgroupOf N := ⟨qN1 a, haA⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨qN1 a, aq.2, ?_⟩
    change φ (QuotientGroup.mk' (C1.subgroupOf N1) a) =
      QuotientGroup.mk' (C.subgroupOf N) (qN1 a)
    simp [φ]
  have hTA_le : TA ≤ SA.map φ := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨a, ha, rfl⟩
    have haA0map : (a : G ⧸ M) ∈ A0.map q := by
      change (a : G ⧸ M) ∈ A at ha
      rwa [← hA0_map_q] at ha
    rcases Subgroup.mem_map.mp haA0map with ⟨x, hxA0, hxa⟩
    let xN1 : N1 := ⟨x, hA0_le_normalizer_Q1 hxA0⟩
    have hxSA : QuotientGroup.mk' (C1.subgroupOf N1) xN1 ∈ SA := by
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (C1.subgroupOf N1)) hxA0
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C1.subgroupOf N1) xN1, hxSA, ?_⟩
    have hxq : qN1 xN1 = (a : N) := by
      apply Subtype.ext
      simpa [qN1, xN1] using hxa
    rw [show φ (QuotientGroup.mk' (C1.subgroupOf N1) xN1) =
        QuotientGroup.mk' (C.subgroupOf N) (qN1 xN1) by
          simp [φ]]
    rw [hxq]
  have hSA_map : SA.map φ = TA := le_antisymm hSA_map_le hTA_le
  calc
    TA = SA.map φ := hSA_map.symm
    _ ≤ (pCore p (N1 ⧸ C1.subgroupOf N1)).map φ := by
          exact Subgroup.map_mono hstable_up
    _ ≤ pCore p (N ⧸ C.subgroupOf N) := by
          exact
            pCore_map_le_pCore_of_surjective (G := N1 ⧸ C1.subgroupOf N1)
              (p := p) φ hφ_surj

theorem CFSG.theorem_8_1_3
    (hconstrained : PConstrainedGroup (G := G) p)
    (hstable : PStableGroup' (G := G) p)
    (P : Sylow p G) (A : Subgroup P) [A.Normal]
    (hAcomm : IsMulCommutative A) :
    A.map P.toSubgroup.subtype ≤ Op_p'p p G := by
  classical
  let M : Subgroup G := pPrimeCore p G
  have hM_normal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hM_normal
  let L : Subgroup G := Op_p'p p G
  let A0 : Subgroup G := A.map P.toSubgroup.subtype
  let Q : Subgroup G := (P : Subgroup G) ⊓ L
  have hQp : IsPGroup p Q := by
    exact P.isPGroup'.to_inf_left
  have hAp : IsPGroup p A := by
    exact P.isPGroup'.to_subgroup A
  have hA0p : IsPGroup p A0 := by
    exact IsPGroup.map (p := p) (H := A) hAp P.toSubgroup.subtype
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let Pbar : Sylow p (G ⧸ M) := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
  have hM_le_L : M ≤ L := by
    simpa [q, M, L, Op_p'p, QuotientGroup.ker_mk'] using
      (Subgroup.ker_le_comap (f := q) (H := pCore p (G ⧸ M)))
  have hLmap : L.map q = pCore p (G ⧸ M) := by
    dsimp [L, Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hpCore_le_Pbar : pCore p (G ⧸ M) ≤ (Pbar : Subgroup (G ⧸ M)) := by
    let R : Subgroup (G ⧸ M) := pCore p (G ⧸ M)
    have hRp : IsPGroup p R := by
      simpa [R] using (pCore_isPGroup (G := G ⧸ M) (p := p))
    have : R.Normal := by
      dsimp [R]
      infer_instance
    obtain ⟨Q', hRQ'⟩ := IsPGroup.exists_le_sylow (G := G ⧸ M) (p := p) hRp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ M) Q' Pbar
    have hR_le_gQ : R ≤ ((g • Q' : Sylow p (G ⧸ M)) : Subgroup (G ⧸ M)) := by
      intro r hr
      rw [Sylow.coe_subgroup_smul]
      refine (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
        (S := (Q' : Subgroup (G ⧸ M))) (x := r)).2 ?_
      have hconj : g⁻¹ * r * g ∈ R := by
        simpa using ((inferInstance : R.Normal).conj_mem r hr g⁻¹)
      exact hRQ' hconj
    have hR_le_Pbar : R ≤ (Pbar : Subgroup (G ⧸ M)) := by
      simpa [hg] using hR_le_gQ
    simpa [R] using hR_le_Pbar
  have hL_le_M_sup_P : L ≤ M ⊔ (P : Subgroup G) := by
    intro x hxL
    have hxmap : q x ∈ L.map q := Subgroup.mem_map_of_mem q hxL
    have hxpcore : q x ∈ pCore p (G ⧸ M) := by
      rw [hLmap] at hxmap
      exact hxmap
    have hxPbar : q x ∈ (Pbar : Subgroup (G ⧸ M)) := hpCore_le_Pbar hxpcore
    have hxPbar' : q x ∈ ((P : Subgroup G).map q) := by
      simpa [Pbar] using hxPbar
    rcases Subgroup.mem_map.mp hxPbar' with ⟨y, hyP, hxy⟩
    have hxyM : x * y⁻¹ ∈ M := by
      apply (QuotientGroup.eq_one_iff (N := M) (x := x * y⁻¹)).1
      change q (x * y⁻¹) = 1
      rw [map_mul, MonoidHom.map_inv, hxy]
      simp
    rw [show x = (x * y⁻¹) * y by simp [mul_assoc]]
    exact Subgroup.mul_mem_sup hxyM hyP
  have hL_le_M_sup_Q : L ≤ M ⊔ Q := by
    intro x hxL
    have hxMP : x ∈ M ⊔ (P : Subgroup G) := hL_le_M_sup_P hxL
    have hxMP' :
        ∃ m ∈ M, ∃ y ∈ (P : Subgroup G), m * y = x :=
      (Subgroup.mem_sup_of_normal_left (s := M) (t := (P : Subgroup G))).1 hxMP
    rcases hxMP' with ⟨m, hmM, y, hyP, hmy⟩
    have hmL : m ∈ L := hM_le_L hmM
    have hyL : y ∈ L := by
      have hy_eq : y = m⁻¹ * x := by
        calc
          y = m⁻¹ * (m * y) := by simp
          _ = m⁻¹ * x := by rw [hmy]
      rw [hy_eq]
      exact L.mul_mem (L.inv_mem hmL) hxL
    have hyQ : y ∈ Q := And.intro hyP hyL
    rw [← hmy]
    exact Subgroup.mul_mem_sup hmM hyQ
  have hM_sup_Q_eq_L : M ⊔ Q = L := by
    apply le_antisymm
    · exact sup_le hM_le_L inf_le_right
    · exact hL_le_M_sup_Q
  have hMmap_bot : M.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := M)).2
    simp [q, QuotientGroup.ker_mk']
  have hQmap : Q.map q = pCore p (G ⧸ M) := by
    calc
      Q.map q = ⊥ ⊔ Q.map q := by simp
      _ = M.map q ⊔ Q.map q := by simp [hMmap_bot]
      _ = (M ⊔ Q).map q := by rw [Subgroup.map_sup]
      _ = L.map q := by rw [hM_sup_Q_eq_L]
      _ = pCore p (G ⧸ M) := hLmap
  have hMQ_normal : (M ⊔ Q).Normal := by
    rw [hM_sup_Q_eq_L]
    infer_instance
  have hA0_le_P : A0 ≤ (P : Subgroup G) := by
    simpa [A0] using (Subgroup.map_subtype_le (H := (P : Subgroup G)) (K := A))
  have hQnormP : (Q.subgroupOf (P : Subgroup G)).Normal := by
    simpa [Q, Subgroup.inf_subgroupOf_right] using
      (show (L.subgroupOf (P : Subgroup G)).Normal from
        (inferInstance : L.Normal).subgroupOf (P : Subgroup G))
  have hP_le_normalizer_Q : (P : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) := by
    let := hQnormP
    exact
      Subgroup.le_normalizer_of_normal_subgroupOf
        (H := Q) (K := (P : Subgroup G)) inf_le_left
  have hA0_le_normalizer_Q : A0 ≤ Subgroup.normalizer (Q : Set G) :=
    hA0_le_P.trans hP_le_normalizer_Q
  have hA0_sub_eq : A0.subgroupOf (P : Subgroup G) = A := by
    apply (Subgroup.map_subtype_inj (H := (P : Subgroup G))).mp
    calc
      (A0.subgroupOf (P : Subgroup G)).map P.toSubgroup.subtype = A0 ⊓ (P : Subgroup G) :=
        Subgroup.subgroupOf_map_subtype A0 (P : Subgroup G)
      _ = A0 := inf_eq_left.mpr hA0_le_P
      _ = A.map P.toSubgroup.subtype := rfl
  have hA0sub_norm : (A0.subgroupOf (P : Subgroup G)).Normal := by
    rw [hA0_sub_eq]
    infer_instance
  have hP_le_normalizer_A0 : (P : Subgroup G) ≤ Subgroup.normalizer (A0 : Set G) := by
    let := hA0sub_norm
    exact
      Subgroup.le_normalizer_of_normal_subgroupOf
        (H := A0) (K := (P : Subgroup G)) hA0_le_P
  have hQA_le_A0 : ⁅Q, A0⁆ ≤ A0 := by
    have hQA_sub_le : ⁅Q.subgroupOf (P : Subgroup G), A⁆ ≤ A := by
      simpa using
        (Subgroup.commutator_le_right
          (H₁ := Q.subgroupOf (P : Subgroup G)) (H₂ := A))
    have hmap_le :
        (⁅Q.subgroupOf (P : Subgroup G), A⁆).map P.toSubgroup.subtype ≤ A0 :=
      Subgroup.map_mono hQA_sub_le
    have hQsub_map :
        (Q.subgroupOf (P : Subgroup G)).map P.toSubgroup.subtype = Q := by
      calc
        (Q.subgroupOf (P : Subgroup G)).map P.toSubgroup.subtype =
            Q ⊓ (P : Subgroup G) := Subgroup.subgroupOf_map_subtype Q (P : Subgroup G)
        _ = Q := inf_eq_left.mpr inf_le_left
    have hcomm_map :
        (⁅Q.subgroupOf (P : Subgroup G), A⁆).map P.toSubgroup.subtype = ⁅Q, A0⁆ := by
      calc
        (⁅Q.subgroupOf (P : Subgroup G), A⁆).map P.toSubgroup.subtype =
            ⁅(Q.subgroupOf (P : Subgroup G)).map P.toSubgroup.subtype,
              A.map P.toSubgroup.subtype⁆ := by
            rw [Subgroup.map_commutator]
        _ = ⁅Q, A0⁆ := by
            simp [A0, hQsub_map]
    rw [hcomm_map] at hmap_le
    exact hmap_le
  have hA0comm : IsMulCommutative A0 := by
    dsimp [A0]
    infer_instance
  have hcomm2 : ⁅⁅Q, A0⁆, A0⁆ = ⊥ := by
    have hA0_cent : A0 ≤ Subgroup.centralizer (A0 : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A0)).2 hA0comm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 (hQA_le_A0.trans hA0_cent)
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  have hC_le_L : C ≤ L := hconstrained Q hQp hM_sup_Q_eq_L
  have hCN : C ≤ N := by
    simpa [N, C] using (centralizer_le_normalizer (G := G) Q)
  let : (C.subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C) (K := N) hCN).2 ?_
    simpa [N, C] using normalizer_le_normalizer_centralizer (G := G) Q
  have hNmap_top : N.map q = ⊤ := by
    have : Fact (IsPGroup p Q) := Fact.mk hQp
    calc
      N.map q = Subgroup.normalizer (Q.map q : Set (G ⧸ M)) := by
        symm
        simpa [N, q] using
          (normalizer_map_quotient_eq_map_normalizer (G := G) (p := p)
            (T := Q) (M := M) inferInstance (by
              simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))))
      _ = Subgroup.normalizer (pCore p (G ⧸ M) : Set (G ⧸ M)) := by rw [hQmap]
      _ = ⊤ := by
        simpa using (Subgroup.normalizer_eq_top (H := pCore p (G ⧸ M)))
  have hqN_surj : Function.Surjective (q.comp N.subtype) := by
    intro y
    have hy : y ∈ N.map q := by
      rw [hNmap_top]
      exact Subgroup.mem_top y
    rcases Subgroup.mem_map.mp hy with ⟨n, hn, hqy⟩
    exact ⟨Subtype.mk n hn, hqy⟩
  have hstableA :
      ((A0.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))) ≤
        pCore p (N ⧸ C.subgroupOf N) := by
    simpa [PStableGroup', N, C] using
      hstable Q A0 hMQ_normal hQp hA0p hA0_le_normalizer_Q hcomm2
  let phi : N ⧸ C.subgroupOf N →* (G ⧸ M) ⧸ pCore p (G ⧸ M) :=
    QuotientGroup.map (C.subgroupOf N) (pCore p (G ⧸ M)) (q.comp N.subtype) (by
      intro c hc
      have hcC : (c : G) ∈ C := hc
      have hcL : (c : G) ∈ L := hC_le_L hcC
      have hcmap : q (c : G) ∈ L.map q := Subgroup.mem_map_of_mem q hcL
      simpa [hLmap] using hcmap)
  have hphi_surj : Function.Surjective phi := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro z
    rcases hqN_surj z with ⟨n, hnz⟩
    refine ⟨QuotientGroup.mk' (C.subgroupOf N) n, ?_⟩
    simp [phi, hnz]
  have hAimage_bot :
      (((A0.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) = ⊥ := by
    apply bot_unique
    calc
      ((A0.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi ≤
          (pCore p (N ⧸ C.subgroupOf N)).map phi := by
            exact Subgroup.map_mono hstableA
      _ ≤ pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M)) := by
            exact
              pCore_map_le_pCore_of_surjective (G := N ⧸ C.subgroupOf N)
                (p := p) phi hphi_surj
      _ = ⊥ := pCore_quotient_pCore_eq_bot (G := G ⧸ M) (p := p)
  have ha_mem : A.map P.toSubgroup.subtype ≤ A0 := by
    simp [A0]
  intro a ha
  have haN : a ∈ N := hA0_le_normalizer_Q (ha_mem ha)
  have haSub : (Subtype.mk a haN : N) ∈ A0.subgroupOf N := ha_mem ha
  have haMap :
      QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN) ∈
        (A0.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' (C.subgroupOf N)) haSub
  have hphi_mem :
      phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
        (((A0.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) :=
    Subgroup.mem_map_of_mem phi haMap
  have hphi_eq : phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) = 1 := by
    have :
        phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
          (⊥ : Subgroup ((G ⧸ M) ⧸ pCore p (G ⧸ M))) := by
      simpa [hAimage_bot] using hphi_mem
    simpa using this
  have haq : q a ∈ pCore p (G ⧸ M) := by
    have : ((q a : G ⧸ M) : (G ⧸ M) ⧸ pCore p (G ⧸ M)) = 1 := by
      simpa [phi] using hphi_eq
    exact (QuotientGroup.eq_one_iff (N := pCore p (G ⧸ M)) (x := q a)).1 this
  simpa [A0, L, Op_p'p, q, M] using haq

theorem CFSG.theorem_8_2_9
    (P B : Subgroup G)
    (hrepl :
      ∀ {A : Subgroup G},
        A ∈ thompsonAbelianSubgroups (G := G) P →
        ¬ B ≤ Subgroup.normalizer (A : Set G) →
        ∃ A' : Subgroup G,
          A' ∈ thompsonAbelianSubgroups (G := G) P ∧
          A ⊓ B < A' ⊓ B ∧
          A' ≤ Subgroup.normalizer (A : Set G)) :
    ∃ A : Subgroup G,
      A ∈ thompsonAbelianSubgroups (G := G) P ∧
      B ≤ Subgroup.normalizer (A : Set G) := by
  classical
  obtain ⟨A0, hA0⟩ := thompsonAbelianSubgroups_nonempty (G := G) P
  let S : Set (Subgroup G) := thompsonAbelianSubgroups (G := G) P
  have hS_nonempty : S.Nonempty := ⟨A0, hA0⟩
  have hS_finite : S.Finite := Set.toFinite S
  obtain ⟨A, hAmax⟩ :=
    hS_finite.exists_maximalFor (f := fun R : Subgroup G => Nat.card ↥(R ⊓ B)) S hS_nonempty
  have hA : A ∈ S := hAmax.prop
  by_cases hBA : B ≤ Subgroup.normalizer (A : Set G)
  · exact ⟨A, hA, hBA⟩
  · rcases hrepl hA hBA with ⟨A', hA', hlt, _⟩
    have hcard_le : Nat.card ↥(A ⊓ B) ≤ Nat.card ↥(A' ⊓ B) := Subgroup.card_le_of_le hlt.le
    have hcard_ne : Nat.card ↥(A ⊓ B) ≠ Nat.card ↥(A' ⊓ B) := by
      intro hEq
      apply hlt.ne
      exact Subgroup.eq_of_le_of_card_ge hlt.le (le_of_eq hEq.symm)
    have hcard_lt : Nat.card ↥(A ⊓ B) < Nat.card ↥(A' ⊓ B) := lt_of_le_of_ne hcard_le hcard_ne
    exact False.elim <| (not_lt_of_ge (hAmax.le hA')) hcard_lt

theorem CFSG.exists_sylow_subgroup_map_eq_inf
    (P : Sylow p G) (L : Subgroup G) [L.Normal] :
    ∃ S : Sylow p L, ((S : Subgroup L).map L.subtype : Subgroup G) = (P : Subgroup G) ⊓ L := by
  let PN : Subgroup (Subgroup.normalizer (L : Set G)) :=
    (P : Subgroup G).subgroupOf (Subgroup.normalizer (L : Set G))
  have hP_le_normalizer_L : (P : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top (H := L)]
    exact le_top
  have hPNp : IsPGroup p PN := by
    exact P.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_normalizer_L).symm
  have hfix_nonempty : (MulAction.fixedPoints PN (Sylow p L)).Nonempty := by
    exact hPNp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p L)
      (not_dvd_card_sylow (p := p) (G := L))
  obtain ⟨Sfix, hSfix⟩ := hfix_nonempty
  let S0 : Subgroup G := ((Sfix : Subgroup L)).map L.subtype
  have hSfix_fixed :
      ∀ a : PN, a.1 • (Sfix : Sylow p L) = (Sfix : Sylow p L) := by
    simpa [MulAction.mem_fixedPoints] using hSfix
  have hP_le_normalizer_S0 : (P : Subgroup G) ≤ Subgroup.normalizer (S0 : Set G) := by
    intro a ha
    let aN : Subgroup.normalizer (L : Set G) := ⟨a, hP_le_normalizer_L ha⟩
    let aPN : PN := ⟨aN, ha⟩
    have ha_fix : aN • (Sfix : Sylow p L) = (Sfix : Sylow p L) := hSfix_fixed aPN
    have ha_fix_map :
        ((((aN • (Sfix : Sylow p L)) : Sylow p L) : Subgroup L).map L.subtype) = S0 := by
      simpa [S0] using
        congrArg (fun R : Sylow p L => ((R : Subgroup L).map L.subtype)) ha_fix
    have hconj_comp :
        L.subtype.comp (MulDistribMulAction.toMonoidHom (↥L) aN) =
          (MulDistribMulAction.toMonoidHom G (ConjAct.toConjAct a)).comp L.subtype := by
      ext y
      rfl
    have hconj_map :
        Subgroup.map (MulDistribMulAction.toMonoidHom G (ConjAct.toConjAct a))
            (Subgroup.map L.subtype ((Sfix : Subgroup L))) =
          Subgroup.map L.subtype
            (Subgroup.map (MulDistribMulAction.toMonoidHom (↥L) aN) (Sfix : Subgroup L)) := by
      rw [Subgroup.map_map, Subgroup.map_map, hconj_comp]
    refine (Subgroup.conjAct_pointwise_smul_iff (H := S0) (g := a)).1 ?_
    simpa [S0, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using
      hconj_map.trans ha_fix_map
  have hS0p : IsPGroup p S0 := by
    simpa [S0] using
      IsPGroup.map (p := p) (H := (Sfix : Subgroup L)) Sfix.isPGroup' L.subtype
  have hS0_le_L : S0 ≤ L := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hSup_p : IsPGroup p (((P : Subgroup G) ⊔ S0 : Subgroup G)) := by
    exact IsPGroup.to_sup_of_normal_right' (p := p) P.isPGroup' hS0p hP_le_normalizer_S0
  have hS0_le_P : S0 ≤ (P : Subgroup G) := by
    have hsup_le_P : (((P : Subgroup G) ⊔ S0 : Subgroup G)) ≤ (P : Subgroup G) :=
      (P.3 hSup_p le_sup_left).le
    exact le_sup_right.trans hsup_le_P
  have hS0_le_inf : S0 ≤ (P : Subgroup G) ⊓ L := by
    exact fun x hx => ⟨hS0_le_P hx, hS0_le_L hx⟩
  let Q : Subgroup L := ((P : Subgroup G) ⊓ L).subgroupOf L
  have hQp : IsPGroup p Q := by
    exact
      (P.isPGroup'.to_inf_left (K := L)).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hSfix_le_Q : (Sfix : Subgroup L) ≤ Q := by
    intro x hx
    exact hS0_le_inf (Subgroup.mem_map_of_mem L.subtype hx)
  have hQ_le_Sfix : Q ≤ (Sfix : Subgroup L) := by
    exact (Sfix.3 hQp hSfix_le_Q).le
  have hInf_le_S0 : (P : Subgroup G) ⊓ L ≤ S0 := by
    intro x hx
    have hxQ : (⟨x, hx.2⟩ : L) ∈ Q := hx
    have hxS : (⟨x, hx.2⟩ : L) ∈ (Sfix : Subgroup L) := hQ_le_Sfix hxQ
    exact Subgroup.mem_map_of_mem L.subtype hxS
  refine ⟨Sfix, le_antisymm hS0_le_inf hInf_le_S0⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem CFSG.theorem_8_2_10
    (hpodd : p ≠ 2)
    (hstable : PStableGroup' (G := G) p)
    (B : Subgroup G) [B.Normal] (hBp : IsPGroup p B) (hBne : B ≠ ⊥)
    (P : Sylow p G) :
    (B ⊓ thompsonCenter (G := G) (P : Subgroup G)).Normal := by
  classical
  let Z : Subgroup G := thompsonCenter (G := G) (P : Subgroup G)
  have hmain :
      ∀ n : ℕ, ∀ (B : Subgroup G), B.Normal → IsPGroup p B → B ≠ ⊥ →
        Nat.card B = n → (B ⊓ Z).Normal := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro B hBnormal hBp hBne hcardB
        let B0 : Subgroup G := B ⊓ Z
        let B1 : Subgroup G := Subgroup.normalClosure (B0 : Set G)
        by_cases hB0_bot : B0 = ⊥
        · simp [B0, hB0_bot]
        have hB0ne : B0 ≠ ⊥ := hB0_bot
        by_cases hB0_normal : B0.Normal
        · simpa [B0] using hB0_normal
        have hB0_not_normal : ¬ B0.Normal := hB0_normal
        have hB1_eq_B : B1 = B := by
          -- Gorenstein 2.10, first paragraph:
          -- by minimality of `B`, the normal closure of `Z ∩ B` must be all of `B`.
          have hB1_le_B : B1 ≤ B := by
            let : B.Normal := hBnormal
            simpa [B0, B1] using
              (Subgroup.normalClosure_le_normal (N := B) (by
                intro x hx
                exact hx.1))
          have hB0_le_B1 : B0 ≤ B1 := by
            simpa [B1] using (Subgroup.le_normalClosure (H := B0))
          by_contra hB1_ne
          have hB1_lt_B : B1 < B := lt_of_le_of_ne hB1_le_B hB1_ne
          have hB1ne : B1 ≠ ⊥ := by
            intro hB1_bot
            apply hB0ne
            exact le_antisymm (hB1_bot ▸ hB0_le_B1) bot_le
          have hB1p : IsPGroup p B1 := by
            let B1sub : Subgroup B := B1.subgroupOf B
            have hB1sub_p : IsPGroup p B1sub := hBp.to_subgroup B1sub
            exact hB1sub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hB1_le_B)
          have hB1_card_lt : Nat.card B1 < Nat.card B := natCard_lt_of_subgroup_lt hB1_lt_B
          have hB1_card_lt_n : Nat.card B1 < n := by
            simpa [hcardB] using hB1_card_lt
          have hB1_inf_normal : (B1 ⊓ Z).Normal := by
            exact ih (Nat.card B1) hB1_card_lt_n B1 (by
              dsimp [B1]
              infer_instance) hB1p hB1ne rfl
          have hB0_le_B1_inf : B0 ≤ B1 ⊓ Z := by
            intro x hx
            exact ⟨hB0_le_B1 hx, hx.2⟩
          have hB1_le_Z : B1 ≤ Z := by
            have hB1_le_inf : B1 ≤ B1 ⊓ Z := by
              let : (B1 ⊓ Z).Normal := hB1_inf_normal
              simpa [B1] using
                (Subgroup.normalClosure_le_normal (N := B1 ⊓ Z) hB0_le_B1_inf)
            exact fun x hx => (hB1_le_inf hx).2
          have hB0_eq_B1 : B0 = B1 := by
            apply le_antisymm hB0_le_B1
            intro x hx
            exact ⟨hB1_le_B hx, hB1_le_Z hx⟩
          have hB1_normal : B1.Normal := by
            dsimp [B1]
            infer_instance
          exact hB0_not_normal <| by
            simpa [hB0_eq_B1] using hB1_normal
        have hB_le_P : B ≤ (P : Subgroup G) := by
          have hPB_p : IsPGroup p (((P : Subgroup G) ⊔ B : Subgroup G)) := by
            have hP_le_normalizer_B : (P : Subgroup G) ≤ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact le_top
            exact IsPGroup.to_sup_of_normal_right' (p := p) P.isPGroup' hBp hP_le_normalizer_B
          have hsup_le_P : (((P : Subgroup G) ⊔ B : Subgroup G)) ≤ (P : Subgroup G) :=
            (P.3 hPB_p le_sup_left).le
          exact le_sup_right.trans hsup_le_P
        have hP_le_norm_Z : (P : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) := by
          exact
            Subgroup.le_normalizer.trans
              (normalizer_le_normalizer_thompsonCenter (G := G) (P : Subgroup G))
        let Bcomm : Subgroup G := ⁅B, B⁆
        have hBcomm_le_B : Bcomm ≤ B := by
          dsimp [Bcomm]
          exact Subgroup.commutator_le_left B B
        have hBcomm_p : IsPGroup p Bcomm := by
          let Bcomm_sub : Subgroup B := Bcomm.subgroupOf B
          have hBcomm_sub_p : IsPGroup p Bcomm_sub := hBp.to_subgroup Bcomm_sub
          exact hBcomm_sub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hBcomm_le_B)
        have hBcomm_inf_normal : (Bcomm ⊓ Z).Normal := by
          by_cases hBcomm_bot : Bcomm = ⊥
          · simp [hBcomm_bot]
          · have : Nontrivial Bcomm :=
              (Subgroup.nontrivial_iff_ne_bot (H := Bcomm)).2 hBcomm_bot
            have : Nontrivial B :=
              (Subgroup.nontrivial_iff_ne_bot (H := B)).2 hBne
            have : Group.IsNilpotent B := hBp.isNilpotent
            have : Group.IsSolvable B := IsNilpotent.to_isSolvable
            have hBcomm_lt_B : Bcomm < B := by
              dsimp [Bcomm]
              simpa using (commutator_lt_self_of_isSolvable_local (G := G) B)
            have hBcomm_card_lt_n : Nat.card Bcomm < n := by
              have hBcomm_card_lt : Nat.card Bcomm < Nat.card B :=
                natCard_lt_of_subgroup_lt hBcomm_lt_B
              simpa [hcardB] using hBcomm_card_lt
            exact
              ih (Nat.card Bcomm) hBcomm_card_lt_n Bcomm
                (by
                  dsimp [Bcomm]
                  infer_instance)
                hBcomm_p hBcomm_bot rfl
        let N : Subgroup G := Bcomm ⊓ Z
        have hN_normal : N.Normal := by
          simpa [N] using hBcomm_inf_normal
        let qN : G →* G ⧸ N := QuotientGroup.mk' N
        let BbarN : Subgroup (G ⧸ N) := B.map qN
        have hBbarN_normal : BbarN.Normal := by
          dsimp [BbarN, qN]
          exact
            Subgroup.Normal.map (H := B) hBnormal
              (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
        let CbarN : Subgroup (G ⧸ N) := Subgroup.centralizer (BbarN : Set (G ⧸ N))
        have hCbarN_normal : CbarN.Normal := by
          apply (Subgroup.normalizer_eq_top_iff).mp
          apply top_le_iff.mp
          calc
            (⊤ : Subgroup (G ⧸ N)) = Subgroup.normalizer (BbarN : Set (G ⧸ N)) := by
              symm
              exact Subgroup.normalizer_eq_top (H := BbarN)
            _ ≤ Subgroup.normalizer (CbarN : Set (G ⧸ N)) := by
              dsimp [CbarN]
              exact CFSG.normalizer_le_normalizer_centralizer (G := G ⧸ N) BbarN
        let CN : Subgroup G := Subgroup.comap qN CbarN
        have hCN_normal : CN.Normal := by
          dsimp [CN]
          infer_instance
        have hB0_le_CN : B0 ≤ CN := by
          intro z hz
          show qN z ∈ CbarN
          rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
          intro y hy
          rcases Subgroup.mem_map.mp hy with ⟨b, hb, rfl⟩
          apply (QuotientGroup.eq_one_iff (N := N) (x := ⁅b, z⁆)).2
          refine ⟨?_, ?_⟩
          · dsimp [Bcomm]
            exact Subgroup.commutator_mem_commutator hb hz.1
          · have hb_normZ : b ∈ Subgroup.normalizer (Z : Set G) := hP_le_norm_Z (hB_le_P hb)
            have hb_conj_z : b * z * b⁻¹ ∈ Z := by
              exact
                ((Subgroup.mem_normalizer_iff.mp hb_normZ) z).1 hz.2
            rw [commutatorElement_def]
            simpa [mul_assoc] using Z.mul_mem hb_conj_z (Z.inv_mem hz.2)
        have hB_le_CN : B ≤ CN := by
          rw [← hB1_eq_B]
          dsimp [B1]
          let : CN.Normal := hCN_normal
          exact Subgroup.normalClosure_le_normal (N := CN) hB0_le_CN
        have hBbarN_cent : BbarN ≤ Subgroup.centralizer (BbarN : Set (G ⧸ N)) := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
          exact hB_le_CN hb
        have hBcomm_map_qN_bot : Bcomm.map qN = ⊥ := by
          calc
            Bcomm.map qN = ⁅BbarN, BbarN⁆ := by
              dsimp [Bcomm, BbarN, qN]
              rw [Subgroup.map_commutator]
            _ = ⊥ := by
              exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hBbarN_cent
        have hBcomm_le_N : Bcomm ≤ N := by
          simpa [N, qN, QuotientGroup.ker_mk'] using
            (Subgroup.map_eq_bot_iff (f := qN) (H := Bcomm)).1 hBcomm_map_qN_bot
        have hBcomm_le_Z : Bcomm ≤ Z := by
          intro x hx
          exact (hBcomm_le_N hx).2
        have hB_le_cent_Bcomm : B ≤ Subgroup.centralizer (Bcomm : Set G) := by
          let : IsMulCommutative Z := thompsonCenter_isMulCommutative (G := G) (P : Subgroup G)
          let C : Subgroup G := Subgroup.centralizer (Bcomm : Set G)
          have hC_normal : C.Normal := by
            apply (Subgroup.normalizer_eq_top_iff).mp
            apply top_le_iff.mp
            calc
              (⊤ : Subgroup G) = Subgroup.normalizer (Bcomm : Set G) := by
                symm
                exact Subgroup.normalizer_eq_top (H := Bcomm)
              _ ≤ Subgroup.normalizer (C : Set G) := by
                dsimp [C]
                exact CFSG.normalizer_le_normalizer_centralizer (G := G) Bcomm
          have hB0_le_C : B0 ≤ C := by
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro c hc
            exact
              setLike_mul_comm
                (s := Z) (hBcomm_le_Z hc) hz.2
          rw [← hB1_eq_B]
          dsimp [B1]
          let : C.Normal := hC_normal
          exact Subgroup.normalClosure_le_normal (N := C) hB0_le_C
        have hBcomm_le_cent_B : Bcomm ≤ Subgroup.centralizer (B : Set G) := by
          exact
            (Subgroup.commutator_eq_bot_iff_le_centralizer).1 <| by
              rw [Subgroup.commutator_comm]
              exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hB_le_cent_Bcomm
        have hclass_two : True := by
          -- Gorenstein 2.10, second paragraph:
          -- `B' ≤ Z(B)` and `B' ≤ Z(J(P))`, so `cl(B) ≤ 2`.
          trivial
        let L : Subgroup G := (Subgroup.normalizer (B0 : Set G)).normalCore
        let qL : G →* G ⧸ L := QuotientGroup.mk' L
        let Pbar : Sylow p (G ⧸ L) :=
          P.mapSurjective (f := qL) (QuotientGroup.mk'_surjective L)
        let Bbar : Subgroup (G ⧸ L) := B.map qL
        let B0bar : Subgroup (G ⧸ L) := B0.map qL
        have hBbar_normal : Bbar.Normal := by
          dsimp [Bbar, qL]
          exact Subgroup.Normal.map (H := B) hBnormal (QuotientGroup.mk' L)
            (QuotientGroup.mk'_surjective L)
        have hBbar_p : IsPGroup p Bbar := by
          dsimp [Bbar, qL]
          exact IsPGroup.map (p := p) (H := B) hBp (QuotientGroup.mk' L)
        have hB0bar_le_Bbar : B0bar ≤ Bbar := by
          dsimp [B0bar, Bbar, qL]
          exact Subgroup.map_mono inf_le_left
        have hcentBbar_le_normB0bar :
            Subgroup.centralizer (Bbar : Set (G ⧸ L)) ≤
              Subgroup.normalizer (B0bar : Set (G ⧸ L)) := by
          intro x hx
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hy
            have hxy : x * y = y * x :=
              (Subgroup.mem_centralizer_iff.mp hx _ (hB0bar_le_Bbar hy)).symm
            have hconj : x * y * x⁻¹ = y := by
              calc
                x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy, mul_assoc]
                _ = y := by simp
            simpa [hconj] using hy
          · intro hy
            have hxinv : x⁻¹ ∈ Subgroup.centralizer (Bbar : Set (G ⧸ L)) :=
              (Subgroup.centralizer (Bbar : Set (G ⧸ L))).inv_mem hx
            have hxy : x⁻¹ * (x * y * x⁻¹) = (x * y * x⁻¹) * x⁻¹ :=
              (Subgroup.mem_centralizer_iff.mp hxinv _ (hB0bar_le_Bbar hy)).symm
            have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ B0bar := by
              have hconj : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
                calc
                  x⁻¹ * (x * y * x⁻¹) * x = ((x * y * x⁻¹) * x⁻¹) * x := by
                    rw [hxy]
                  _ = x * y * x⁻¹ := by simp [mul_assoc]
              simpa [hconj] using hy
            simpa [mul_assoc] using hy'
        have hJ_not_le_L :
            ¬ thompsonSubgroup (G := G) (P : Subgroup G) ≤ L := by
          -- Gorenstein 2.10, third paragraph:
          -- if `J(P) ≤ P ∩ L`, then `G = L N_G(J(P ∩ L))` forces `Z ∩ B ◁ G`.
          let : L.Normal := by
            dsimp [L]
            infer_instance
          intro hJ_le_L
          let R : Subgroup G := (P : Subgroup G) ⊓ L
          have hJ_le_R : thompsonSubgroup (G := G) (P : Subgroup G) ≤ R := by
            intro x hx
            exact ⟨thompsonSubgroup_le (G := G) (P : Subgroup G) hx, hJ_le_L hx⟩
          have hZ_eq_R : thompsonCenter (G := G) R = Z := by
            simpa [Z, R] using
              (thompsonCenter_eq_of_le (G := G) (P := (P : Subgroup G)) (R := R)
                inf_le_left hJ_le_R)
          have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
            obtain ⟨S, hS_map⟩ := exists_sylow_subgroup_map_eq_inf (G := G) (p := p) P L
            simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hB0_normal' : B0.Normal := by
            apply (Subgroup.normalizer_eq_top_iff).mp
            apply top_le_iff.mp
            rw [← hFr]
            intro g hg
            rcases
                (Subgroup.mem_sup_of_normal_right
                  (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
              ⟨n, hnR, l, hlL, rfl⟩
            have hnZ :
                n ∈ Subgroup.normalizer (Z : Set G) := by
              have hnTc :
                  n ∈ Subgroup.normalizer (thompsonCenter (G := G) R : Set G) :=
                (normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
              simpa [hZ_eq_R] using hnTc
            have hnB :
                n ∈ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              simp
            have hnB0 :
                n ∈ Subgroup.normalizer (B0 : Set G) := by
              simpa [B0] using
                (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hnB, hnZ⟩)
            exact (Subgroup.normalizer (B0 : Set G)).mul_mem hnB0 (hL_le_norm_B0 hlL)
          exact hB0_not_normal hB0_normal'
        have hA_exists :
            ∃ A : Subgroup G,
              A ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) ∧
                ⁅⁅B, A⁆, A⁆ = ⊥ ∧ A ≤ L := by
          -- Gorenstein 2.10, fourth paragraph:
          -- use Theorem 2.9 and Lemma 2.3, then p-stability and `Op(G / L) = 1`.
          obtain ⟨A, hA, hB_norm_A⟩ :=
            theorem_8_2_9 (G := G) (P := (P : Subgroup G)) (B := B) (by
              intro A hA hB_not_norm_A
              have hx_exists : ∃ x ∈ B, x ∉ Subgroup.normalizer (A : Set G) := by
                by_contra hx_not_exists
                apply hB_not_norm_A
                intro x hx
                by_contra hx_not_norm
                exact hx_not_exists ⟨x, hx, hx_not_norm⟩
              obtain ⟨x, hxB, hx_not_norm_A⟩ := hx_exists
              let H : Subgroup G := B ⊔ A
              have hH_le_P : H ≤ (P : Subgroup G) := by
                dsimp [H]
                exact sup_le hB_le_P hA.1
              let Hsub : Subgroup (P : Subgroup G) := H.subgroupOf (P : Subgroup G)
              have hHsub_p : IsPGroup p Hsub := P.isPGroup'.to_subgroup Hsub
              have hH_p : IsPGroup p ↥H := by
                exact hHsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hH_le_P)
              have habelian_step :
                  ∃ n, 0 < n ∧ IsMulCommutative (replacementCommChain B A n) := by
                exact
                  replacementCommChain_exists_positive_abelian
                    (p := p) B A hBne (by simpa [H] using hH_p)
              let nA : ℕ := Nat.find habelian_step
              have hnA_pos : 0 < nA := (Nat.find_spec habelian_step).1
              have hnA_comm : IsMulCommutative (replacementCommChain B A nA) :=
                (Nat.find_spec habelian_step).2
              have hbot_step : ∃ n, replacementCommChain B A n = ⊥ := by
                exact
                  replacementCommChain_eventually_bot
                    (p := p) B A (by simpa [H] using hH_p)
              let rA : ℕ := Nat.find hbot_step
              have hrA_bot : replacementCommChain B A rA = ⊥ := Nat.find_spec hbot_step
              have hrA_pos : 0 < rA := by
                have hrA_ne_zero : rA ≠ 0 := by
                  intro hrA_zero
                  apply hBne
                  have hr0 : replacementCommChain B A 0 = ⊥ := by
                    simpa [rA, hrA_zero] using hrA_bot
                  simpa [replacementCommChain_zero] using hr0
                exact Nat.pos_of_ne_zero hrA_ne_zero
              have hnA_min :
                  ∀ m, 0 < m → IsMulCommutative (replacementCommChain B A m) → nA ≤ m := by
                intro m hmpos hmcomm
                exact Nat.find_min' habelian_step ⟨hmpos, hmcomm⟩
              have hrA_min :
                  ∀ m, replacementCommChain B A m = ⊥ → rA ≤ m := by
                intro m hm
                exact Nat.find_min' hbot_step hm
              have hD2_ne_bot : replacementCommChain B A 2 ≠ ⊥ := by
                exact
                  replacementCommChain_two_ne_bot_of_not_normalizer
                    (G := G) (P := (P : Subgroup G)) hA hB_le_P hB_not_norm_A
              have hnA_le_rA : nA ≤ rA := by
                exact hnA_min rA hrA_pos <| by
                  rw [hrA_bot]
                  infer_instance
              have hnA_succ_lt_rA :
                  replacementCommChain B A (nA + 1) ≠ ⊥ → nA + 1 < rA := by
                intro hDnA_succ_ne_bot
                by_contra hnot_lt
                have hrA_le : rA ≤ nA + 1 := Nat.le_of_not_gt hnot_lt
                have hDnA_succ_bot : replacementCommChain B A (nA + 1) = ⊥ := by
                  exact
                    replacementCommChain_eq_bot_of_eq_bot_of_le
                      B A hrA_le hrA_bot
                exact hDnA_succ_ne_bot hDnA_succ_bot
              have hAinP :
                  (A.subgroupOf (P : Subgroup G)) ∈
                    thompsonAbelianSubgroups (G := P) (⊤ : Subgroup P) := by
                refine ⟨by simp, ?_, ?_⟩
                · let : IsMulCommutative A := hA.2.1
                  infer_instance
                · intro C hC hCcomm
                  have hAmax := hA.2.2 (C.map P.toSubgroup.subtype) (by
                    simpa using
                      (Subgroup.map_subtype_le (H := (P : Subgroup G)) (K := C))) (by
                        exact Subgroup.map_isMulCommutative (H := C) P.toSubgroup.subtype)
                  calc
                    Nat.card C = Nat.card (C.map P.toSubgroup.subtype) := by
                      symm
                      exact Subgroup.card_subtype (P : Subgroup G) C
                    _ ≤ Nat.card A := hAmax
                    _ = Nat.card (A.subgroupOf (P : Subgroup G)) := by
                      simpa [Subgroup.map_subgroupOf_eq_of_le hA.1] using
                        (Subgroup.card_subtype (P : Subgroup G) (A.subgroupOf (P : Subgroup G)))
              have hZ_le_A : Z ≤ A := by
                simpa [Z, Subgroup.map_subgroupOf_eq_of_le hA.1] using
                  (thompsonCenter_le_map_of_mem_thompsonAbelianSubgroups
                    (G := G) (p := p) P hAinP)
              have hBcomm_le_A : Bcomm ≤ A := hBcomm_le_Z.trans hZ_le_A
              have hAinfB_cent_D1 :
                  A ⊓ B ≤
                    Subgroup.centralizer
                      (((replacementCommChain B A 1 : Subgroup G) : Set G)) := by
                simpa [Bcomm, replacementCommChain_succ, replacementCommChain_zero] using
                  (inf_le_centralizer_commutator_of_commutator_le
                    (G := G) (P := (P : Subgroup G)) (B := B) (A := A) hA hBcomm_le_A)
              have hAinfB_cent_Di :
                  ∀ i, 1 ≤ i →
                    A ⊓ B ≤
                      Subgroup.centralizer
                        (((replacementCommChain B A i : Subgroup G) : Set G)) := by
                intro i hi x hx
                rw [Subgroup.mem_centralizer_iff]
                intro y hy
                exact
                  (Subgroup.mem_centralizer_iff.mp (hAinfB_cent_D1 hx) y)
                    ((replacementCommChain_antitone B A hi) hy)
              by_cases hDnA_succ_bot : replacementCommChain B A (nA + 1) = ⊥
              · let H : Subgroup G := B ⊔ A
                let Bsub : Subgroup H := B.subgroupOf H
                let Asub : Subgroup H := A.subgroupOf H
                let Nsub : Subgroup H := Bcomm.subgroupOf H
                let qH : H →* H ⧸ Nsub := QuotientGroup.mk' Nsub
                let Dbar : ℕ → Subgroup (H ⧸ Nsub) :=
                  fun i => (replacementCommChainSub B A i).map qH
                let : Bsub.Normal := hBnormal.subgroupOf H
                let : Nsub.Normal := by
                  change ((⁅B, B⁆).subgroupOf H).Normal
                  exact (Subgroup.commutator_normal B B).subgroupOf H
                have hBcomm_le_cent_A : Bcomm ≤ Subgroup.centralizer (A : Set G) := by
                  exact
                    hBcomm_le_A.trans
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
                have hBcomm_le_cent_H : Bcomm ≤ Subgroup.centralizer (H : Set G) := by
                  dsimp [H]
                  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
                  intro z hz
                  rw [Subgroup.mem_centralizer_iff]
                  intro y hy
                  rcases hy with hyB | hyA
                  · exact (Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B hz) y hyB)
                  · exact (Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A hz) y hyA)
                have hNsub_cent_top :
                    Nsub ≤ Subgroup.centralizer ((⊤ : Subgroup H) : Set H) := by
                  intro z hz
                  rw [Subgroup.mem_centralizer_iff]
                  intro y hy
                  apply Subtype.ext
                  exact
                    Subgroup.mem_centralizer_iff.mp
                      (hBcomm_le_cent_H (show (z : G) ∈ Bcomm from hz)) y.1 y.2
                have hBsub_sup_Asub_top : Bsub ⊔ Asub = ⊤ := by
                  apply (Subgroup.map_subtype_inj (H := H)).mp
                  calc
                    (Bsub ⊔ Asub).map H.subtype = B ⊔ A := by
                      rw [Subgroup.map_sup,
                        Subgroup.map_subgroupOf_eq_of_le le_sup_left,
                        Subgroup.map_subgroupOf_eq_of_le le_sup_right]
                    _ = H := by rfl
                    _ = (⊤ : Subgroup H).map H.subtype := by
                      simpa [MonoidHom.range_eq_map] using
                        (H.range_subtype : H.subtype.range = H).symm
                have hBsub_comm_le_Nsub : ⁅Bsub, Bsub⁆ ≤ Nsub := by
                  intro x hx
                  have hxmap : (x : G) ∈ Bcomm := by
                    have hxmap' :
                        (x : G) ∈ (⁅Bsub, Bsub⁆).map H.subtype := by
                      exact Subgroup.mem_map_of_mem H.subtype hx
                    rw [commutator_subgroupOf_map_eq
                      (S := H) (H := B) (R := B) le_sup_left le_sup_left] at hxmap'
                    simpa [Bcomm] using hxmap'
                  change x ∈ Bcomm.subgroupOf H
                  exact hxmap
                have hBbar_comm : IsMulCommutative (Bsub.map qH) := by
                  have hBbar_comm_eq :
                      ⁅Bsub.map qH, Bsub.map qH⁆ = ⊥ := by
                    apply le_antisymm
                    · calc
                        ⁅Bsub.map qH, Bsub.map qH⁆ = (⁅Bsub, Bsub⁆).map qH := by
                          rw [Subgroup.map_commutator]
                        _ ≤ Nsub.map qH := Subgroup.map_mono hBsub_comm_le_Nsub
                        _ = ⊥ := QuotientGroup.map_mk'_self (N := Nsub)
                    · exact bot_le
                  exact
                    (Subgroup.le_centralizer_iff_isMulCommutative (K := Bsub.map qH)).1 <|
                      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hBbar_comm_eq
                have hAsub_comm : IsMulCommutative Asub := by
                  let : IsMulCommutative A := hA.2.1
                  simpa [Asub] using
                    (Subgroup.subgroupOf_isMulCommutative (H := A) (K := H))
                have hAbar_comm : IsMulCommutative (Asub.map qH) := by
                  let : IsMulCommutative Asub := hAsub_comm
                  exact Subgroup.map_isMulCommutative (H := Asub) qH
                have hBbar_sup_Abar_top :
                    Bsub.map qH ⊔ Asub.map qH = ⊤ := by
                  calc
                    Bsub.map qH ⊔ Asub.map qH = (Bsub ⊔ Asub).map qH := by
                      rw [← Subgroup.map_sup]
                    _ = (⊤ : Subgroup H).map qH := by rw [hBsub_sup_Asub_top]
                    _ = ⊤ := Subgroup.map_top_of_surjective qH (QuotientGroup.mk'_surjective Nsub)
                have hDbar_le_Bbar : ∀ i, Dbar i ≤ Bsub.map qH := by
                  intro i
                  dsimp [Dbar]
                  refine Subgroup.map_mono ?_
                  rw [replacementCommChainSub_eq_subgroupOf]
                  intro x hx
                  exact replacementCommChain_le_left B A i hx
                have hDbar_comm_A :
                    ∀ i, ⁅Dbar i, Asub.map qH⁆ = Dbar (i + 1) := by
                  intro i
                  change
                    ⁅(replacementCommChainSub B A i).map qH, (A.subgroupOf H).map qH⁆ =
                      (replacementCommChainSub B A (i + 1)).map qH
                  rw [replacementCommChainSub_succ, Subgroup.map_commutator]
                have hDbar_comm_A_rev :
                    ∀ i, ⁅Asub.map qH, Dbar i⁆ = Dbar (i + 1) := by
                  intro i
                  simpa [Subgroup.commutator_comm] using hDbar_comm_A i
                have hcommAbar_Bbar : ⁅Asub.map qH, Bsub.map qH⁆ = Dbar 1 := by
                  change ⁅Asub.map qH, Dbar 0⁆ = Dbar 1
                  simpa [Dbar, replacementCommChainSub_zero] using hDbar_comm_A_rev 0
                have hcommBbar_Abar : ⁅Bsub.map qH, Asub.map qH⁆ = Dbar 1 := by
                  change ⁅Dbar 0, Asub.map qH⁆ = Dbar 1
                  simpa [Dbar, replacementCommChainSub_zero] using hDbar_comm_A 0
                have hL1q_le :
                    (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries 1 ≤ Dbar 1 := by
                  rw [Subgroup.top_lowerCentralSeries_one]
                  refine (Subgroup.commutator_le).2 ?_
                  intro y hy z hz
                  have hy' : y ∈ Bsub.map qH ⊔ Asub.map qH := by
                    simp [hBbar_sup_Abar_top]
                  have hz' : z ∈ Bsub.map qH ⊔ Asub.map qH := by
                    simp [hBbar_sup_Abar_top]
                  let : (Bsub.map qH).Normal := by
                    exact
                      Subgroup.Normal.map
                        (H := Bsub) (inferInstance : Bsub.Normal) qH
                        (QuotientGroup.mk'_surjective Nsub)
                  rcases
                      (Subgroup.mem_sup_of_normal_left
                        (s := Bsub.map qH) (t := Asub.map qH) (x := y)).1 hy' with
                    ⟨b1, hb1, a1, ha1, rfl⟩
                  rcases
                      (Subgroup.mem_sup_of_normal_left
                        (s := Bsub.map qH) (t := Asub.map qH) (x := z)).1 hz' with
                    ⟨b2, hb2, a2, ha2, rfl⟩
                  have hb12 : b1 * b2 = b2 * b1 := by
                    exact
                      setLike_mul_comm
                        (s := Bsub.map qH) hb1 hb2
                  have ha12 : a1 * a2 = a2 * a1 := by
                    exact
                      setLike_mul_comm
                        (s := Asub.map qH) ha1 ha2
                  have ha1b2_mem : ⁅a1, b2⁆ ∈ Dbar 1 := by
                    have : ⁅a1, b2⁆ ∈ ⁅Asub.map qH, Bsub.map qH⁆ := by
                      exact Subgroup.commutator_mem_commutator ha1 hb2
                    rwa [hcommAbar_Bbar] at this
                  have hb1a2_mem : ⁅b1, a2⁆ ∈ Dbar 1 := by
                    have : ⁅b1, a2⁆ ∈ ⁅Bsub.map qH, Asub.map qH⁆ := by
                      exact Subgroup.commutator_mem_commutator hb1 ha2
                    rwa [hcommBbar_Abar] at this
                  have ha1b2_B : ⁅a1, b2⁆ ∈ Bsub.map qH := hDbar_le_Bbar 1 ha1b2_mem
                  have hb1a2_B : ⁅b1, a2⁆ ∈ Bsub.map qH := hDbar_le_Bbar 1 hb1a2_mem
                  have hb1_conj_ha1b2 :
                      b1 * ⁅a1, b2⁆ * b1⁻¹ = ⁅a1, b2⁆ := by
                    have hcomm : b1 * ⁅a1, b2⁆ = ⁅a1, b2⁆ * b1 := by
                      exact
                        setLike_mul_comm
                          (s := Bsub.map qH) hb1 ha1b2_B
                    calc
                      b1 * ⁅a1, b2⁆ * b1⁻¹ = (⁅a1, b2⁆ * b1) * b1⁻¹ := by
                        rw [hcomm]
                      _ = ⁅a1, b2⁆ := by simp [mul_assoc]
                  have hb2_conj_hb1a2 :
                      b2 * ⁅b1, a2⁆ * b2⁻¹ = ⁅b1, a2⁆ := by
                    have hcomm : b2 * ⁅b1, a2⁆ = ⁅b1, a2⁆ * b2 := by
                      exact
                        setLike_mul_comm
                          (s := Bsub.map qH) hb2 hb1a2_B
                    calc
                      b2 * ⁅b1, a2⁆ * b2⁻¹ = (⁅b1, a2⁆ * b2) * b2⁻¹ := by
                        rw [hcomm]
                      _ = ⁅b1, a2⁆ := by simp [mul_assoc]
                  have hbb2 : ⁅b1, b2⁆ = 1 := by
                    exact
                      commutatorElement_eq_one_iff_commute.mpr
                        (setLike_mul_comm
                          (s := Bsub.map qH) hb1 hb2)
                  have haa2 : ⁅a1, a2⁆ = 1 := by
                    exact
                      commutatorElement_eq_one_iff_commute.mpr
                        (setLike_mul_comm
                          (s := Asub.map qH) ha1 ha2)
                  have hleft_mem : ⁅b1 * a1, b2⁆ ∈ Dbar 1 := by
                    rw [commutator_mul_left, hbb2]
                    simpa [hb1_conj_ha1b2, mul_assoc] using ha1b2_mem
                  have hright_mem : ⁅b1 * a1, a2⁆ ∈ Dbar 1 := by
                    rw [commutator_mul_left, haa2]
                    simpa [mul_assoc] using hb1a2_mem
                  have hright_B : ⁅b1 * a1, a2⁆ ∈ Bsub.map qH := hDbar_le_Bbar 1 hright_mem
                  have hright_conj :
                      b2 * ⁅b1 * a1, a2⁆ * b2⁻¹ = ⁅b1 * a1, a2⁆ := by
                    have hcomm : b2 * ⁅b1 * a1, a2⁆ = ⁅b1 * a1, a2⁆ * b2 := by
                      exact
                        setLike_mul_comm
                          (s := Bsub.map qH) hb2 hright_B
                    calc
                      b2 * ⁅b1 * a1, a2⁆ * b2⁻¹ = (⁅b1 * a1, a2⁆ * b2) * b2⁻¹ := by
                        rw [hcomm]
                      _ = ⁅b1 * a1, a2⁆ := by simp [mul_assoc]
                  rw [commutator_mul_right]
                  simpa [hright_conj, mul_assoc] using (Dbar 1).mul_mem hleft_mem hright_mem
                have hLq_le_Dbar :
                    ∀ i, (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries (i + 1) ≤
                      Dbar (i + 1) := by
                  intro i
                  induction i with
                  | zero =>
                      exact hL1q_le
                  | succ i ih =>
                      rw [Subgroup.lowerCentralSeries_succ]
                      refine (Subgroup.commutator_le).2 ?_
                      intro x hx y hy
                      have hxD : x ∈ Dbar (i + 1) := ih hx
                      have hy' : y ∈ Bsub.map qH ⊔ Asub.map qH := by
                        simp [hBbar_sup_Abar_top]
                      let : (Bsub.map qH).Normal := by
                        exact
                          Subgroup.Normal.map
                            (H := Bsub) (inferInstance : Bsub.Normal) qH
                            (QuotientGroup.mk'_surjective Nsub)
                      rcases
                          (Subgroup.mem_sup_of_normal_left
                            (s := Bsub.map qH) (t := Asub.map qH) (x := y)).1 hy' with
                        ⟨b, hb, a, ha, rfl⟩
                      have hxb : ⁅x, b⁆ = 1 := by
                        have hxB : x ∈ Bsub.map qH := hDbar_le_Bbar (i + 1) hxD
                        exact
                          commutatorElement_eq_one_iff_commute.mpr
                            (setLike_mul_comm
                              (s := Bsub.map qH) hxB hb)
                      have hxa_mem : ⁅x, a⁆ ∈ Dbar (i + 2) := by
                        have : ⁅x, a⁆ ∈ ⁅Dbar (i + 1), Asub.map qH⁆ := by
                          exact Subgroup.commutator_mem_commutator hxD ha
                        simpa [hDbar_comm_A (i + 1)] using this
                      have hxa_B : ⁅x, a⁆ ∈ Bsub.map qH := hDbar_le_Bbar (i + 2) hxa_mem
                      have hconj :
                          b * ⁅x, a⁆ * b⁻¹ = ⁅x, a⁆ := by
                        have hcomm : b * ⁅x, a⁆ = ⁅x, a⁆ * b := by
                          exact
                            setLike_mul_comm
                              (s := Bsub.map qH) hb hxa_B
                        calc
                          b * ⁅x, a⁆ * b⁻¹ = (⁅x, a⁆ * b) * b⁻¹ := by
                            rw [hcomm]
                          _ = ⁅x, a⁆ := by simp [mul_assoc]
                      rw [commutator_mul_right, hxb]
                      simpa [hconj, mul_assoc] using hxa_mem
                have hLmap_le :
                    ∀ i, ((⊤ : Subgroup H).lowerCentralSeries i).map qH ≤
                      (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries i := by
                  intro i
                  induction i with
                  | zero =>
                      simp
                  | succ i ih =>
                      change
                        Subgroup.map qH ⁅(⊤ : Subgroup H).lowerCentralSeries i,
                          (⊤ : Subgroup H)⁆ ≤
                            (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries (i + 1)
                      rw [Subgroup.map_commutator, Subgroup.lowerCentralSeries_succ,
                        Subgroup.map_top_of_surjective qH (QuotientGroup.mk'_surjective Nsub)]
                      exact Subgroup.commutator_mono ih le_rfl
                have hDbar_bot : Dbar (nA + 1) = ⊥ := by
                  have hbot_sub : ((⊥ : Subgroup G).subgroupOf H) = (⊥ : Subgroup H) := by
                    ext x
                    simp
                  calc
                    Dbar (nA + 1) = Subgroup.map qH (replacementCommChainSub B A (nA + 1)) := by
                      rfl
                    _ = ((replacementCommChain B A (nA + 1)).subgroupOf H).map qH := by
                      rw [replacementCommChainSub_eq_subgroupOf]
                    _ = (⊥ : Subgroup H).map qH := by rw [hDnA_succ_bot, hbot_sub]
                    _ = ⊥ := by simp
                have hLq_bot :
                    (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries (nA + 1) = ⊥ := by
                  apply le_antisymm
                  · exact (hLq_le_Dbar nA).trans_eq hDbar_bot
                  · exact bot_le
                have hLH_le_Nsub :
                    (⊤ : Subgroup H).lowerCentralSeries (nA + 1) ≤ Nsub := by
                  have hmap_bot :
                      ((⊤ : Subgroup H).lowerCentralSeries (nA + 1)).map qH = ⊥ := by
                    apply le_antisymm
                    · exact (hLmap_le (nA + 1)).trans_eq hLq_bot
                    · exact bot_le
                  exact
                    (by
                      have hker :
                          (⊤ : Subgroup H).lowerCentralSeries (nA + 1) ≤ qH.ker :=
                        (Subgroup.map_eq_bot_iff
                          (f := qH)
                          (H := (⊤ : Subgroup H).lowerCentralSeries (nA + 1))).1 hmap_bot
                      simpa [qH, QuotientGroup.ker_mk'] using hker)
                have hLH_bot : (⊤ : Subgroup H).lowerCentralSeries (nA + 2) = ⊥ := by
                  have hcomm_bot :
                      ⁅(⊤ : Subgroup H).lowerCentralSeries (nA + 1),
                        (⊤ : Subgroup H)⁆ = ⊥ := by
                    exact
                      (Subgroup.commutator_eq_bot_iff_le_centralizer).2
                        (hLH_le_Nsub.trans hNsub_cent_top)
                  have hidx : nA + 2 = (nA + 1) + 1 := by omega
                  simpa [Subgroup.lowerCentralSeries, hidx] using hcomm_bot
                have hnA_le_two : nA ≤ 2 := by
                  by_contra hnA_gt_two
                  have hnA_ge_three : 3 ≤ nA := by omega
                  have hLpred_comm :
                      IsMulCommutative ((⊤ : Subgroup H).lowerCentralSeries (nA - 1)) := by
                    have hcomm_bot :
                        ⁅(⊤ : Subgroup H).lowerCentralSeries (nA - 1),
                          (⊤ : Subgroup H).lowerCentralSeries (nA - 1)⁆ = ⊥ := by
                      apply le_antisymm
                      · calc
                          ⁅(⊤ : Subgroup H).lowerCentralSeries (nA - 1),
                            (⊤ : Subgroup H).lowerCentralSeries (nA - 1)⁆ ≤
                              (⊤ : Subgroup H).lowerCentralSeries
                                ((nA - 1) + (nA - 1) + 1) := by
                                simpa using
                                  (lowerCentralSeries_commutator_le
                                    (G := H) (nA - 1) (nA - 1))
                          _ ≤ (⊤ : Subgroup H).lowerCentralSeries (nA + 2) := by
                                apply Subgroup.lowerCentralSeries_antitone
                                omega
                          _ = ⊥ := hLH_bot
                      · exact bot_le
                    exact
                      (Subgroup.le_centralizer_iff_isMulCommutative
                        (K := (⊤ : Subgroup H).lowerCentralSeries (nA - 1))).1 <|
                        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm_bot
                  have hDpred_sub_comm :
                      IsMulCommutative ((replacementCommChain B A (nA - 1)).subgroupOf H) := by
                    have hsub :
                        (replacementCommChain B A (nA - 1)).subgroupOf H ≤
                          (⊤ : Subgroup H).lowerCentralSeries (nA - 1) := by
                      rw [← replacementCommChainSub_eq_subgroupOf]
                      exact replacementCommChainSub_le_lowerCentralSeries B A (nA - 1)
                    refine ⟨?_⟩
                    exact ⟨fun y z => by
                      apply Subtype.ext
                      simpa using
                        (setLike_mul_comm
                          (s := (⊤ : Subgroup H).lowerCentralSeries (nA - 1))
                          (hsub y.2) (hsub z.2))⟩
                  have hDpred_comm :
                      IsMulCommutative (replacementCommChain B A (nA - 1)) := by
                    refine ⟨?_⟩
                    exact ⟨fun y z => by
                      let yH : ((replacementCommChain B A (nA - 1)).subgroupOf H) :=
                        ⟨⟨y, replacementCommChain_le_sup B A (nA - 1) y.2⟩, y.2⟩
                      let zH : ((replacementCommChain B A (nA - 1)).subgroupOf H) :=
                        ⟨⟨z, replacementCommChain_le_sup B A (nA - 1) z.2⟩, z.2⟩
                      apply Subtype.ext
                      simpa [yH, zH] using
                        congrArg Subtype.val
                          ((IsMulCommutative.is_comm
                            (M := ((replacementCommChain B A (nA - 1)).subgroupOf H))).comm
                              yH zH)⟩
                  have hnA_pred_pos : 0 < nA - 1 := by
                    omega
                  have hle : nA ≤ nA - 1 :=
                    hnA_min (nA - 1) hnA_pred_pos hDpred_comm
                  omega
                have hnA_ne_one : nA ≠ 1 := by
                  intro hnA_eq_one
                  have hD2_bot : replacementCommChain B A 2 = ⊥ := by
                    simpa [hnA_eq_one] using hDnA_succ_bot
                  exact hD2_ne_bot hD2_bot
                have hnA_ge_two : 2 ≤ nA := by
                  by_contra hlt
                  have hnA_le_one : nA ≤ 1 := by omega
                  have hnA_eq_one : nA = 1 := by omega
                  exact hnA_ne_one hnA_eq_one
                have hnA_eq_two : nA = 2 := by omega
                have hD3_bot : replacementCommChain B A 3 = ⊥ := by
                  simpa [hnA_eq_two] using hDnA_succ_bot
                have hxP : x ∈ (P : Subgroup G) := hB_le_P hxB
                have hD2_le_A : replacementCommChain B A 2 ≤ A := by
                  exact
                    replacementCommChain_le_of_succ_eq_bot
                      (G := G) (P := (P : Subgroup G)) (B := B) (A := A)
                      hA hB_le_P hD3_bot
                have hD2_le_B : replacementCommChain B A 2 ≤ B :=
                  replacementCommChain_le_left B A 2
                have hDbar3_bot : Dbar 3 = ⊥ := by
                  simpa [hnA_eq_two] using hDbar_bot
                have hDbar2_cent_Abar :
                    Dbar 2 ≤
                      Subgroup.centralizer
                        (((Asub.map qH : Subgroup (H ⧸ Nsub)) : Set (H ⧸ Nsub))) := by
                  exact
                    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 <| by
                      simpa [hDbar_comm_A 2] using hDbar3_bot
                have hxu_exists :
                    ∃ u ∈ A, ⁅x, u⁆ ∉ Subgroup.centralizer (A : Set G) := by
                  by_contra hno
                  let f : G ≃* G := MulAut.conj x
                  have hmap_le : A.map f.toMonoidHom ≤ A := by
                    intro y hy
                    rcases Subgroup.mem_map.mp hy with ⟨u, huA, rfl⟩
                    have hxu_centA : ⁅x, u⁆ ∈ Subgroup.centralizer (A : Set G) := by
                      by_contra hnot
                      exact hno ⟨u, huA, hnot⟩
                    have hxu_subcent : ⁅x, u⁆ ∈ subgroupCentralizerIn' (P : Subgroup G) A := by
                      refine ⟨hxu_centA, ?_⟩
                      exact
                        (Subgroup.commutator_le_self (H := (P : Subgroup G)))
                          (Subgroup.commutator_mem_commutator hxP (hA.1 huA))
                    have hxuA : ⁅x, u⁆ ∈ A := by
                      simpa [thompsonAbelianSubgroups_centralizer_eq (G := G) hA] using hxu_subcent
                    simpa [f, show x * u * x⁻¹ = ⁅x, u⁆ * u by
                      simp [commutatorElement_def, mul_assoc]] using A.mul_mem hxuA huA
                  have hmap_eq : A.map f.toMonoidHom = A := by
                    apply Subgroup.eq_of_le_of_card_ge hmap_le
                    have hcard :
                        Nat.card (A.map f.toMonoidHom) = Nat.card A := by
                      simpa [f] using
                        (Subgroup.card_map_of_injective (K := A) (f := f.toMonoidHom) f.injective)
                    exact le_of_eq hcard.symm
                  apply hx_not_norm_A
                  rw [← Subgroup.conjAct_pointwise_smul_iff]
                  change A.map (MulAut.conj x).toMonoidHom = A
                  simpa [f] using hmap_eq
                obtain ⟨u, huA, hxu_not_centA⟩ := hxu_exists
                have hgen_comm :
                    ∀ u ∈ A, ∀ v ∈ A, ⁅⁅x, u⁆, ⁅x, v⁆⁆ = 1 := by
                  intro u huA v hvA
                  let a : G := ⁅x, u⁆
                  let b : G := ⁅x, v⁆
                  let d1 : G := ⁅a, v⁆
                  let d2 : G := ⁅b, u⁆
                  have haD1 : a ∈ replacementCommChain B A 1 := by
                    dsimp [a]
                    have : ⁅B, A⁆ = replacementCommChain B A (0 + 1) := by rfl
                    rw [this, replacementCommChain_succ, replacementCommChain_zero]
                    exact Subgroup.commutator_mem_commutator hxB huA
                  have hbD1 : b ∈ replacementCommChain B A 1 := by
                    dsimp [b]
                    have : ⁅B, A⁆ = replacementCommChain B A (0 + 1) := by rfl
                    rw [this, replacementCommChain_succ, replacementCommChain_zero]
                    exact Subgroup.commutator_mem_commutator hxB hvA
                  have haB : a ∈ B := (replacementCommChain_le_left B A 1) haD1
                  have hbB : b ∈ B := (replacementCommChain_le_left B A 1) hbD1
                  have hd1D2 : d1 ∈ replacementCommChain B A 2 := by
                    dsimp [d1]
                    have : ⁅⁅B, A⁆, A⁆ = replacementCommChain B A (1 + 1) := rfl
                    rw [this, replacementCommChain_succ]
                    exact Subgroup.commutator_mem_commutator haD1 hvA
                  have hd2D2 : d2 ∈ replacementCommChain B A 2 := by
                    dsimp [d2]
                    have : ⁅⁅B, A⁆, A⁆ = replacementCommChain B A (1 + 1) := rfl
                    rw [this, replacementCommChain_succ]
                    exact Subgroup.commutator_mem_commutator hbD1 huA
                  have hd1A : d1 ∈ A := hD2_le_A hd1D2
                  have hd2A : d2 ∈ A := hD2_le_A hd2D2
                  have hd1B : d1 ∈ B := hD2_le_B hd1D2
                  have hd2B : d2 ∈ B := hD2_le_B hd2D2
                  have hd1AB : d1 ∈ A ⊓ B := ⟨hd1A, hd1B⟩
                  have hd2AB : d2 ∈ A ⊓ B := ⟨hd2A, hd2B⟩
                  have hd1_cent_D1 :
                      d1 ∈ Subgroup.centralizer
                        (((replacementCommChain B A 1 : Subgroup G) : Set G)) :=
                    hAinfB_cent_D1 hd1AB
                  have hd2_cent_D1 :
                      d2 ∈ Subgroup.centralizer
                        (((replacementCommChain B A 1 : Subgroup G) : Set G)) :=
                    hAinfB_cent_D1 hd2AB
                  have hd1_cent_A : d1 ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1) hd1A
                  have hd2_cent_A : d2 ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1) hd2A
                  let xH : H := ⟨x, by
                    dsimp [H]
                    exact (show x ∈ B ⊔ A from Subgroup.mem_sup_left hxB)⟩
                  let uH : H := ⟨u, by
                    dsimp [H]
                    exact (show u ∈ B ⊔ A from Subgroup.mem_sup_right huA)⟩
                  let vH : H := ⟨v, by
                    dsimp [H]
                    exact (show v ∈ B ⊔ A from Subgroup.mem_sup_right hvA)⟩
                  let aH : H := ⟨a, replacementCommChain_le_sup B A 1 haD1⟩
                  let bH : H := ⟨b, replacementCommChain_le_sup B A 1 hbD1⟩
                  let d1H : H := ⟨d1, replacementCommChain_le_sup B A 2 hd1D2⟩
                  let d2H : H := ⟨d2, replacementCommChain_le_sup B A 2 hd2D2⟩
                  have huH_Abar : qH uH ∈ Asub.map qH := by
                    exact Subgroup.mem_map_of_mem qH <| by
                      simpa [Asub, uH, Subgroup.mem_subgroupOf] using huA
                  have hvH_Abar : qH vH ∈ Asub.map qH := by
                    exact Subgroup.mem_map_of_mem qH <| by
                      simpa [Asub, vH, Subgroup.mem_subgroupOf] using hvA
                  have haH_Dbar1 : qH aH ∈ Dbar 1 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆ = replacementCommChainSub B A 1 := rfl
                      rw [this, replacementCommChainSub_eq_subgroupOf]
                      simpa [aH, Subgroup.mem_subgroupOf] using haD1
                  have hbH_Dbar1 : qH bH ∈ Dbar 1 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆ = replacementCommChainSub B A 1 := rfl
                      rw [this, replacementCommChainSub_eq_subgroupOf]
                      simpa [bH, Subgroup.mem_subgroupOf] using hbD1
                  have hd1H_Dbar2 : qH d1H ∈ Dbar 2 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆, A.subgroupOf (B ⊔ A)⁆ = replacementCommChainSub B A 2 := rfl
                      rw [this, replacementCommChainSub_eq_subgroupOf]
                      simpa [d1H, Subgroup.mem_subgroupOf] using hd1D2
                  have hd2H_Dbar2 : qH d2H ∈ Dbar 2 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆, A.subgroupOf (B ⊔ A)⁆ = replacementCommChainSub B A 2 := rfl
                      rw [this,replacementCommChainSub_eq_subgroupOf]
                      simpa [d2H, Subgroup.mem_subgroupOf] using hd2D2
                  have haH_Bbar : qH aH ∈ Bsub.map qH := hDbar_le_Bbar 1 haH_Dbar1
                  have hbH_Bbar : qH bH ∈ Bsub.map qH := hDbar_le_Bbar 1 hbH_Dbar1
                  have hd1H_Bbar : qH d1H ∈ Bsub.map qH := hDbar_le_Bbar 2 hd1H_Dbar2
                  have hd2H_Bbar : qH d2H ∈ Bsub.map qH := hDbar_le_Bbar 2 hd2H_Dbar2
                  have haH_comm_bH : qH aH * qH bH = qH bH * qH aH := by
                    exact
                      setLike_mul_comm
                        (s := Bsub.map qH) haH_Bbar hbH_Bbar
                  have hd1bar_cent_Abar :
                      qH d1H ∈
                        Subgroup.centralizer
                          (((Asub.map qH : Subgroup (H ⧸ Nsub)) : Set (H ⧸ Nsub))) :=
                    hDbar2_cent_Abar hd1H_Dbar2
                  have hd2bar_cent_Abar :
                      qH d2H ∈
                        Subgroup.centralizer
                          (((Asub.map qH : Subgroup (H ⧸ Nsub)) : Set (H ⧸ Nsub))) :=
                    hDbar2_cent_Abar hd2H_Dbar2
                  have hq_d1_eq_d2 : qH d1H = qH d2H := by
                    have huvH : qH uH * qH vH = qH vH * qH uH := by
                      exact
                        setLike_mul_comm
                          (s := Asub.map qH) huH_Abar hvH_Abar
                    have hqa : ⁅qH xH, qH uH⁆ = qH aH := by
                      have hxuH : ⁅xH, uH⁆ = aH := by
                        apply Subtype.ext
                        rfl
                      rw [← hxuH]
                      exact (map_commutatorElement (f := qH) (g₁ := xH) (g₂ := uH)).symm
                    have hqb : ⁅qH xH, qH vH⁆ = qH bH := by
                      have hxvH : ⁅xH, vH⁆ = bH := by
                        apply Subtype.ext
                        rfl
                      rw [← hxvH]
                      exact (map_commutatorElement (f := qH) (g₁ := xH) (g₂ := vH)).symm
                    have hq_d1_inv :
                        ⁅qH uH, qH bH⁆ = (qH d2H)⁻¹ := by
                      calc
                        ⁅qH uH, qH bH⁆ = qH ⁅uH, bH⁆ := by
                          exact
                            (map_commutatorElement (f := qH) (g₁ := uH) (g₂ := bH)).symm
                        _ = (qH d2H)⁻¹ := by
                          have hbhu_eq : ⁅bH, uH⁆ = d2H := by
                            rfl
                          have hub_inv : ⁅uH, bH⁆ = (⁅bH, uH⁆)⁻¹ := by
                            simp
                          calc
                            qH ⁅uH, bH⁆ = qH ((⁅bH, uH⁆)⁻¹) := by rw [hub_inv]
                            _ = (qH ⁅bH, uH⁆)⁻¹ := by rw [qH.map_inv]
                            _ = (qH d2H)⁻¹ := by rw [hbhu_eq]
                    have hq_d2_inv :
                        ⁅qH vH, qH aH⁆ = (qH d1H)⁻¹ := by
                      calc
                        ⁅qH vH, qH aH⁆ = qH ⁅vH, aH⁆ := by
                          exact
                            (map_commutatorElement (f := qH) (g₁ := vH) (g₂ := aH)).symm
                        _ = (qH d1H)⁻¹ := by
                          have hav_eq : ⁅aH, vH⁆ = d1H := by
                            rfl
                          have hva_inv : ⁅vH, aH⁆ = (⁅aH, vH⁆)⁻¹ := by
                            simp
                          calc
                            qH ⁅vH, aH⁆ = qH ((⁅aH, vH⁆)⁻¹) := by rw [hva_inv]
                            _ = (qH ⁅aH, vH⁆)⁻¹ := by rw [qH.map_inv]
                            _ = (qH d1H)⁻¹ := by rw [hav_eq]
                    have hconj_u_b :
                        qH uH * qH bH * (qH uH)⁻¹ = (qH d2H)⁻¹ * qH bH := by
                      calc
                        qH uH * qH bH * (qH uH)⁻¹ = ⁅qH uH, qH bH⁆ * qH bH := by
                          simp [commutatorElement_def, mul_assoc]
                        _ = (qH d2H)⁻¹ * qH bH := by rw [hq_d1_inv]
                    have hconj_v_a :
                        qH vH * qH aH * (qH vH)⁻¹ = (qH d1H)⁻¹ * qH aH := by
                      calc
                        qH vH * qH aH * (qH vH)⁻¹ = ⁅qH vH, qH aH⁆ * qH aH := by
                          simp [commutatorElement_def, mul_assoc]
                        _ = (qH d1H)⁻¹ * qH aH := by rw [hq_d2_inv]
                    have hleft :
                        ⁅qH xH, qH uH * qH vH⁆ = qH aH * (qH d2H)⁻¹ * qH bH := by
                      rw [commutator_mul_right, hqa, hqb]
                      simpa [mul_assoc] using hconj_u_b
                    have hright :
                        ⁅qH xH, qH vH * qH uH⁆ = qH bH * (qH d1H)⁻¹ * qH aH := by
                      rw [commutator_mul_right, hqb, hqa]
                      simpa [mul_assoc] using hconj_v_a
                    have hEq :
                        qH aH * (qH d2H)⁻¹ * qH bH = qH bH * (qH d1H)⁻¹ * qH aH := by
                      calc
                        qH aH * (qH d2H)⁻¹ * qH bH = ⁅qH xH, qH uH * qH vH⁆ := hleft.symm
                        _ = ⁅qH xH, qH vH * qH uH⁆ := by rw [huvH]
                        _ = qH bH * (qH d1H)⁻¹ * qH aH := hright
                    have hEq' :
                        qH aH * qH bH * (qH d2H)⁻¹ =
                          qH aH * qH bH * (qH d1H)⁻¹ := by
                      calc
                        qH aH * qH bH * (qH d2H)⁻¹ = qH aH * (qH d2H)⁻¹ * qH bH := by
                          have hcomm :
                              qH bH * qH d2H = qH d2H * qH bH := by
                            exact
                              setLike_mul_comm
                                (s := Bsub.map qH) hbH_Bbar hd2H_Bbar
                          have hcomm' :
                              qH bH * (qH d2H)⁻¹ = (qH d2H)⁻¹ * qH bH := by
                            have hcomm' : Commute (qH bH) (qH d2H) := hcomm
                            exact hcomm'.inv_right.eq
                          simp [mul_assoc, ← hcomm']
                        _ = qH bH * (qH d1H)⁻¹ * qH aH := hEq
                        _ = qH bH * qH aH * (qH d1H)⁻¹ := by
                          have hcomm :
                              qH aH * qH d1H = qH d1H * qH aH := by
                            exact
                              setLike_mul_comm
                                (s := Bsub.map qH) haH_Bbar hd1H_Bbar
                          have hcomm' :
                              qH aH * (qH d1H)⁻¹ = (qH d1H)⁻¹ * qH aH := by
                            have hcomm' : Commute (qH aH) (qH d1H) := hcomm
                            exact hcomm'.inv_right.eq
                          simp [mul_assoc, ← hcomm']
                        _ = qH aH * qH bH * (qH d1H)⁻¹ := by
                          rw [haH_comm_bH]
                    have hinv_eq : (qH d2H)⁻¹ = (qH d1H)⁻¹ := by
                      exact mul_left_cancel hEq'
                    exact inv_injective hinv_eq.symm
                  have hdiff_mem : d1H / d2H ∈ Nsub := by
                    exact (QuotientGroup.eq_iff_div_mem).1 hq_d1_eq_d2
                  have hdiffBcomm : d1 / d2 ∈ Bcomm := by
                    simpa [d1H, d2H, d1, d2, Nsub, Subgroup.mem_subgroupOf] using hdiff_mem
                  have hdiff_cent_x : Commute (d1 / d2) x := by
                    exact
                      ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B hdiffBcomm) x) hxB).symm
                  have hdiff_cent_xd2 : Commute (d1 / d2) ⁅x, d2⁆ := by
                    have hxd2B : ⁅x, d2⁆ ∈ B := by
                      exact
                        hBcomm_le_B <|
                          Subgroup.commutator_mem_commutator hxB hd2B
                    exact
                      ((Subgroup.mem_centralizer_iff.mp
                        (hBcomm_le_cent_B hdiffBcomm) ⁅x, d2⁆) hxd2B).symm
                  have hxdiff_one : ⁅x, d1 / d2⁆ = 1 := by
                    exact commutatorElement_eq_one_iff_commute.mpr hdiff_cent_x.symm
                  have hconj_diff_xd2 :
                      (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ = ⁅x, d2⁆ := by
                    calc
                      (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ =
                          (⁅x, d2⁆ * (d1 / d2)) * (d1 / d2)⁻¹ := by
                            rw [hdiff_cent_xd2.symm.eq]
                      _ = ⁅x, d2⁆ := by simp [mul_assoc]
                  have hd1v : Commute d1 v := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd1_cent_A v) hvA).symm
                  have hd2u : Commute d2 u := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd2_cent_A u) huA).symm
                  have hd1b : Commute d1 b := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd1_cent_D1 b) hbD1).symm
                  have hd2a : Commute d2 a := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd2_cent_D1 a) haD1).symm
                  have hd1_inv_v : ⁅a, v⁻¹⁆ = d1⁻¹ := by
                    rw [commutator_inv_right]
                    calc
                      v⁻¹ * d1⁻¹ * v = v⁻¹ * (d1⁻¹ * v) := by
                        simp [mul_assoc]
                      _ = v⁻¹ * (v * d1⁻¹) := by
                        rw [(hd1v.inv_left).eq]
                      _ = d1⁻¹ := by simp
                  have hd2_inv_u : ⁅b, u⁻¹⁆ = d2⁻¹ := by
                    rw [commutator_inv_right]
                    calc
                      u⁻¹ * d2⁻¹ * u = u⁻¹ * (d2⁻¹ * u) := by
                        simp [mul_assoc]
                      _ = u⁻¹ * (u * d2⁻¹) := by
                        rw [(hd2u.inv_left).eq]
                      _ = d2⁻¹ := by simp
                  have hxv_eq : x * v * x⁻¹ = b * v := by
                    dsimp [b]
                    simp [commutatorElement_def, mul_assoc]
                  have hxu_eq : x * u * x⁻¹ = a * u := by
                    dsimp [a]
                    simp [commutatorElement_def, mul_assoc]
                  have hd1_conj_xv :
                      (x * v * x⁻¹) * d1⁻¹ * (x * v * x⁻¹)⁻¹ = d1⁻¹ := by
                    have hv_fix : v * d1⁻¹ * v⁻¹ = d1⁻¹ := by
                      calc
                        v * d1⁻¹ * v⁻¹ = (d1⁻¹ * v) * v⁻¹ := by
                          rw [(hd1v.inv_left).symm.eq]
                        _ = d1⁻¹ := by simp [mul_assoc]
                    calc
                      (x * v * x⁻¹) * d1⁻¹ * (x * v * x⁻¹)⁻¹ =
                          (b * v) * d1⁻¹ * (b * v)⁻¹ := by rw [hxv_eq]
                      _ = b * (v * d1⁻¹ * v⁻¹) * b⁻¹ := by simp [mul_assoc]
                      _ = b * d1⁻¹ * b⁻¹ := by rw [hv_fix]
                      _ = d1⁻¹ := by
                        calc
                          b * d1⁻¹ * b⁻¹ = (d1⁻¹ * b) * b⁻¹ := by
                            rw [(hd1b.inv_left).symm.eq]
                          _ = d1⁻¹ := by simp [mul_assoc]
                  have hd2_conj_xu :
                      (x * u * x⁻¹) * d2⁻¹ * (x * u * x⁻¹)⁻¹ = d2⁻¹ := by
                    have hu_fix : u * d2⁻¹ * u⁻¹ = d2⁻¹ := by
                      calc
                        u * d2⁻¹ * u⁻¹ = (d2⁻¹ * u) * u⁻¹ := by
                          rw [(hd2u.inv_left).symm.eq]
                        _ = d2⁻¹ := by simp [mul_assoc]
                    calc
                      (x * u * x⁻¹) * d2⁻¹ * (x * u * x⁻¹)⁻¹ =
                          (a * u) * d2⁻¹ * (a * u)⁻¹ := by rw [hxu_eq]
                      _ = a * (u * d2⁻¹ * u⁻¹) * a⁻¹ := by simp [mul_assoc]
                      _ = a * d2⁻¹ * a⁻¹ := by rw [hu_fix]
                      _ = d2⁻¹ := by
                        calc
                          a * d2⁻¹ * a⁻¹ = (d2⁻¹ * a) * a⁻¹ := by
                            rw [(hd2a.inv_left).symm.eq]
                          _ = d2⁻¹ := by simp [mul_assoc]
                  have hc_eq_xd1 : ⁅a, b⁆ = ⁅x, d1⁆ := by
                    have haxBcomm : ⁅a, x⁆ ∈ Bcomm := by
                      exact Subgroup.commutator_mem_commutator haB hxB
                    have hax_x : Commute ⁅a, x⁆ x := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B haxBcomm) x) hxB).symm
                    have hax_d1 : Commute ⁅a, x⁆ d1 := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A haxBcomm) d1)
                          hd1A).symm
                    have hax_inv : ⁅a, x⁻¹⁆ = ⁅a, x⁆⁻¹ := by
                      rw [commutator_inv_right]
                      calc
                        x⁻¹ * ⁅a, x⁆⁻¹ * x = x⁻¹ * (x * ⁅a, x⁆⁻¹) := by
                          rw [(hax_x.inv_left).symm.eq, mul_assoc]
                        _ = ⁅a, x⁆⁻¹ := by simp
                    have hax_inv_v :
                        v * ⁅a, x⁆⁻¹ * v⁻¹ = ⁅a, x⁆⁻¹ := by
                      have haxv : Commute ⁅a, x⁆ v := by
                        exact
                          ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A haxBcomm) v)
                            hvA).symm
                      calc
                        v * ⁅a, x⁆⁻¹ * v⁻¹ = (⁅a, x⁆⁻¹ * v) * v⁻¹ := by
                          rw [(haxv.inv_left).symm.eq]
                        _ = ⁅a, x⁆⁻¹ := by simp [mul_assoc]
                    calc
                      ⁅a, b⁆ = ⁅a, x * v * x⁻¹ * v⁻¹⁆ := by
                        dsimp [b]
                        simp [commutatorElement_def, mul_assoc]
                      _ = ⁅a, x * v * x⁻¹⁆ * d1⁻¹ := by
                        rw [commutator_mul_right]
                        calc
                          ⁅a, x * v * x⁻¹⁆ * (x * v * x⁻¹) * ⁅a, v⁻¹⁆ * (x * v * x⁻¹)⁻¹ =
                              ⁅a, x * v * x⁻¹⁆ *
                                ((x * v * x⁻¹) * ⁅a, v⁻¹⁆ * (x * v * x⁻¹)⁻¹) := by
                                  simp [mul_assoc]
                          _ = ⁅a, x * v * x⁻¹⁆ * d1⁻¹ := by
                                rw [hd1_inv_v, hd1_conj_xv]
                      _ = (⁅a, x⁆ * x * ⁅a, v * x⁻¹⁆ * x⁻¹) * d1⁻¹ := by
                        rw [show x * v * x⁻¹ = x * (v * x⁻¹) by simp [mul_assoc]]
                        rw [commutator_mul_right]
                      _ = (⁅a, x⁆ * x * (d1 * ⁅a, x⁆⁻¹) * x⁻¹) * d1⁻¹ := by
                        have hinner : ⁅a, v * x⁻¹⁆ = d1 * ⁅a, x⁆⁻¹ := by
                          rw [commutator_mul_right]
                          calc
                            ⁅a, v⁆ * v * ⁅a, x⁻¹⁆ * v⁻¹ = ⁅a, v⁆ * (v * ⁅a, x⁻¹⁆ * v⁻¹) := by
                              simp [mul_assoc]
                            _ = ⁅a, v⁆ * ⁅a, x⁆⁻¹ := by rw [hax_inv, hax_inv_v]
                            _ = d1 * ⁅a, x⁆⁻¹ := by rfl
                        rw [hinner]
                      _ = (x * d1 * x⁻¹) * d1⁻¹ := by
                        have hfix : ⁅a, x⁆ * d1 * ⁅a, x⁆⁻¹ = d1 := by
                          calc
                            ⁅a, x⁆ * d1 * ⁅a, x⁆⁻¹ = (d1 * ⁅a, x⁆) * ⁅a, x⁆⁻¹ := by
                              simp [hax_d1.eq, mul_assoc]
                            _ = d1 := by simp [commutatorElement_def,mul_assoc]
                        calc
                          (⁅a, x⁆ * x * (d1 * ⁅a, x⁆⁻¹) * x⁻¹) * d1⁻¹ =
                              (x * (⁅a, x⁆ * d1 * ⁅a, x⁆⁻¹) * x⁻¹) * d1⁻¹ := by
                                rw [hax_x.eq]
                                simp [mul_assoc]
                          _ = (x * d1 * x⁻¹) * d1⁻¹ := by rw [hfix]
                      _ = ⁅x, d1⁆ := by
                        simp [commutatorElement_def, mul_assoc]
                  have hc_eq_xd2 : ⁅b, a⁆ = ⁅x, d2⁆ := by
                    have hbxBcomm : ⁅b, x⁆ ∈ Bcomm := by
                      exact Subgroup.commutator_mem_commutator hbB hxB
                    have hbx_x : Commute ⁅b, x⁆ x := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B hbxBcomm) x) hxB).symm
                    have hbx_d2 : Commute ⁅b, x⁆ d2 := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A hbxBcomm) d2)
                          hd2A).symm
                    have hbx_inv : ⁅b, x⁻¹⁆ = ⁅b, x⁆⁻¹ := by
                      rw [commutator_inv_right]
                      calc
                        x⁻¹ * ⁅b, x⁆⁻¹ * x = x⁻¹ * (x * ⁅b, x⁆⁻¹) := by
                          rw [(hbx_x.inv_left).symm.eq, mul_assoc]
                        _ = ⁅b, x⁆⁻¹ := by simp
                    have hbx_inv_u :
                        u * ⁅b, x⁆⁻¹ * u⁻¹ = ⁅b, x⁆⁻¹ := by
                      have hbxu : Commute ⁅b, x⁆ u := by
                        exact
                          ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A hbxBcomm) u)
                            huA).symm
                      calc
                        u * ⁅b, x⁆⁻¹ * u⁻¹ = (⁅b, x⁆⁻¹ * u) * u⁻¹ := by
                          rw [(hbxu.inv_left).symm.eq]
                        _ = ⁅b, x⁆⁻¹ := by simp [mul_assoc]
                    calc
                      ⁅b, a⁆ = ⁅b, x * u * x⁻¹ * u⁻¹⁆ := by
                        dsimp [a]
                        simp [commutatorElement_def, mul_assoc]
                      _ = ⁅b, x * u * x⁻¹⁆ * d2⁻¹ := by
                        rw [commutator_mul_right]
                        calc
                          ⁅b, x * u * x⁻¹⁆ * (x * u * x⁻¹) * ⁅b, u⁻¹⁆ * (x * u * x⁻¹)⁻¹ =
                              ⁅b, x * u * x⁻¹⁆ *
                                ((x * u * x⁻¹) * ⁅b, u⁻¹⁆ * (x * u * x⁻¹)⁻¹) := by
                                  simp [mul_assoc]
                          _ = ⁅b, x * u * x⁻¹⁆ * d2⁻¹ := by
                                rw [hd2_inv_u, hd2_conj_xu]
                      _ = (⁅b, x⁆ * x * ⁅b, u * x⁻¹⁆ * x⁻¹) * d2⁻¹ := by
                        rw [show x * u * x⁻¹ = x * (u * x⁻¹) by simp [mul_assoc]]
                        rw [commutator_mul_right]
                      _ = (⁅b, x⁆ * x * (d2 * ⁅b, x⁆⁻¹) * x⁻¹) * d2⁻¹ := by
                        have hinner : ⁅b, u * x⁻¹⁆ = d2 * ⁅b, x⁆⁻¹ := by
                          rw [commutator_mul_right]
                          calc
                            ⁅b, u⁆ * u * ⁅b, x⁻¹⁆ * u⁻¹ = ⁅b, u⁆ * (u * ⁅b, x⁻¹⁆ * u⁻¹) := by
                              simp [mul_assoc]
                            _ = ⁅b, u⁆ * ⁅b, x⁆⁻¹ := by rw [hbx_inv, hbx_inv_u]
                            _ = d2 * ⁅b, x⁆⁻¹ := by rfl
                        rw [hinner]
                      _ = (x * d2 * x⁻¹) * d2⁻¹ := by
                        have hfix : ⁅b, x⁆ * d2 * ⁅b, x⁆⁻¹ = d2 := by
                          calc
                            ⁅b, x⁆ * d2 * ⁅b, x⁆⁻¹ = (d2 * ⁅b, x⁆) * ⁅b, x⁆⁻¹ := by
                              simp [hbx_d2.eq, mul_assoc]
                            _ = d2 := by rw [mul_assoc, mul_inv_cancel, mul_one]
                        calc
                          (⁅b, x⁆ * x * (d2 * ⁅b, x⁆⁻¹) * x⁻¹) * d2⁻¹ =
                              (x * (⁅b, x⁆ * d2 * ⁅b, x⁆⁻¹) * x⁻¹) * d2⁻¹ := by
                                rw [hbx_x.eq]
                                simp [mul_assoc]
                          _ = (x * d2 * x⁻¹) * d2⁻¹ := by rw [hfix]
                      _ = ⁅x, d2⁆ := by
                        simp [commutatorElement_def, mul_assoc]
                  have hxd1_eq_hxd2 : ⁅x, d1⁆ = ⁅x, d2⁆ := by
                    calc
                      ⁅x, d1⁆ = ⁅x, (d1 / d2) * d2⁆ := by
                        simp [div_eq_mul_inv, mul_assoc]
                      _ = ⁅x, d1 / d2⁆ * (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ := by
                        rw [commutator_mul_right]
                      _ = (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ := by
                        rw [hxdiff_one]
                        simp
                      _ = ⁅x, d2⁆ := hconj_diff_xd2
                  have hcomm_eq_inv : ⁅a, b⁆ = ⁅a, b⁆⁻¹ := by
                    calc
                      ⁅a, b⁆ = ⁅x, d1⁆ := hc_eq_xd1
                      _ = ⁅x, d2⁆ := hxd1_eq_hxd2
                      _ = ⁅b, a⁆ := hc_eq_xd2.symm
                      _ = ⁅a, b⁆⁻¹ := by simp [commutatorElement_inv]
                  have hcomm_sq : ⁅a, b⁆ ^ 2 = 1 := by
                    calc
                      ⁅a, b⁆ ^ 2 = ⁅a, b⁆ * ⁅a, b⁆ := by simp [pow_two]
                      _ = ⁅a, b⁆ * ⁅a, b⁆⁻¹ := by nth_rw 2 [hcomm_eq_inv]
                      _ = 1 := by rw [mul_inv_cancel]
                  have habBcomm : ⁅a, b⁆ ∈ Bcomm := by
                    exact Subgroup.commutator_mem_commutator haB hbB
                  exact
                    eq_one_of_mem_pGroup_sq_eq_one
                      (G := G) (p := p) hpodd Bcomm hBcomm_p habBcomm hcomm_sq
                let M : Subgroup G := Subgroup.closure {g : G | ∃ v ∈ A, ⁅x, v⁆ = g}
                let C : Subgroup G := subgroupCentralizerIn' A M
                let Astar : Subgroup G := M ⊔ C
                have hM_le_D1 : M ≤ replacementCommChain B A 1 := by
                  dsimp [M]
                  rw [Subgroup.closure_le]
                  intro y hy
                  rcases hy with ⟨v, hvA, rfl⟩
                  have : ⁅B, A⁆ = replacementCommChain B A (0 + 1) := rfl
                  rw [this, replacementCommChain_succ, replacementCommChain_zero]
                  exact Subgroup.commutator_mem_commutator hxB hvA
                have hM_le_B : M ≤ B := hM_le_D1.trans (replacementCommChain_le_left B A 1)
                have hM_comm : IsMulCommutative M := by
                  dsimp [M]
                  exact Subgroup.isMulCommutative_closure
                    (k := {g : G | ∃ v ∈ A, ⁅x, v⁆ = g}) <| by
                      intro y hy z hz _
                      rcases hy with ⟨u, huA, rfl⟩
                      rcases hz with ⟨v, hvA, rfl⟩
                      exact commutatorElement_eq_one_iff_commute.mp (hgen_comm u huA v hvA)
                have hAstar :
                    Astar ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) := by
                  dsimp [Astar, C, M]
                  simpa using
                    (thompsonReplacement_base (G := G) (P := (P : Subgroup G))
                      (A := A) hA hxP hM_comm)
                have hAinfB_le_C : A ⊓ B ≤ C := by
                  intro y hy
                  dsimp [C, subgroupCentralizerIn']
                  refine ⟨?_, hy.1⟩
                  show y ∈ Subgroup.centralizer (M : Set G)
                  rw [Subgroup.mem_centralizer_iff]
                  intro m hmM
                  have hycent := hAinfB_cent_D1 hy
                  exact (Subgroup.mem_centralizer_iff.mp hycent m) (hM_le_D1 hmM)
                have hAinfB_le_AstarinfB : A ⊓ B ≤ Astar ⊓ B := by
                  intro y hy
                  exact ⟨(show C ≤ Astar from le_sup_right) (hAinfB_le_C hy), hy.2⟩
                have hxu_mem_M : ⁅x, u⁆ ∈ M := by
                  dsimp [M]
                  exact Subgroup.subset_closure ⟨u, huA, rfl⟩
                have hxu_mem_B : ⁅x, u⁆ ∈ B := hM_le_B hxu_mem_M
                have hxu_not_mem_A : ⁅x, u⁆ ∉ A := by
                  intro hxuA
                  have hxu_centA : ⁅x, u⁆ ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
                        hxuA
                  exact hxu_not_centA hxu_centA
                have hAstar_lt : A ⊓ B < Astar ⊓ B := by
                  have hne : A ⊓ B ≠ Astar ⊓ B := by
                    intro hEq
                    have hxu_mem_AstarB : ⁅x, u⁆ ∈ Astar ⊓ B := by
                      exact ⟨(show M ≤ Astar from le_sup_left) hxu_mem_M, hxu_mem_B⟩
                    have hxu_mem_AB : ⁅x, u⁆ ∈ A ⊓ B := by
                      simpa [hEq] using hxu_mem_AstarB
                    exact hxu_not_mem_A hxu_mem_AB.1
                  exact lt_of_le_of_ne hAinfB_le_AstarinfB hne
                have hM_le_P : M ≤ (P : Subgroup G) := hM_le_B.trans hB_le_P
                have hM_comm2 : ⁅⁅M, A⁆, A⁆ = ⊥ := by
                  have hMA_le_D2 : ⁅M, A⁆ ≤ replacementCommChain B A 2 := by
                    rw [replacementCommChain_succ]
                    exact Subgroup.commutator_mono hM_le_D1 le_rfl
                  have hMA_le_A : ⁅M, A⁆ ≤ A := hMA_le_D2.trans hD2_le_A
                  exact
                    (Subgroup.commutator_eq_bot_iff_le_centralizer).2
                      (hMA_le_A.trans
                        ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1))
                have hM_le_norm_A : M ≤ Subgroup.normalizer (A : Set G) := by
                  exact
                    (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                      (G := G) (P := (P : Subgroup G)) (A := A) (B := M) hA hM_le_P).2
                      hM_comm2
                have hAstar_le_norm_A : Astar ≤ Subgroup.normalizer (A : Set G) := by
                  rw [sup_le_iff]
                  constructor
                  · exact hM_le_norm_A
                  · trans A
                    · dsimp [C, subgroupCentralizerIn']
                      simp
                    · exact Subgroup.le_normalizer
                exact ⟨Astar, hAstar, hAstar_lt, hAstar_le_norm_A⟩
              · have hnA_succ_lt : nA + 1 < rA := hnA_succ_lt_rA hDnA_succ_bot
                have hrA_gt_two : 2 < rA := by
                  omega
                have hDrA1_ne_bot : replacementCommChain B A (rA - 1) ≠ ⊥ := by
                  intro hbot
                  have hle : rA ≤ rA - 1 := hrA_min (rA - 1) hbot
                  omega
                have hDrA2_not_cent :
                    ¬ replacementCommChain B A (rA - 2) ≤ Subgroup.centralizer (A : Set G) := by
                  intro hcent
                  have hsub : rA - 1 = (rA - 2) + 1 := by
                    omega
                  have hbot : replacementCommChain B A (rA - 1) = ⊥ := by
                    rw [hsub, replacementCommChain_succ]
                    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcent
                  exact hDrA1_ne_bot hbot
                have hxu_exists :
                    ∃ x ∈ replacementCommChain B A (rA - 3),
                      ∃ u ∈ A, ⁅x, u⁆ ∉ Subgroup.centralizer (A : Set G) := by
                  by_contra hno
                  apply hDrA2_not_cent
                  have hsub : rA - 2 = (rA - 3) + 1 := by
                    omega
                  rw [hsub, replacementCommChain_succ]
                  refine (Subgroup.commutator_le).2 ?_
                  intro x hx u hu
                  by_contra hnot
                  exact hno ⟨x, hx, u, hu, hnot⟩
                obtain ⟨x, hxDrA3, u, huA, hxu_not_centA⟩ := hxu_exists
                let M : Subgroup G := Subgroup.closure {g : G | ∃ v ∈ A, ⁅x, v⁆ = g}
                let C : Subgroup G := subgroupCentralizerIn' A M
                let Astar : Subgroup G := M ⊔ C
                have hxB' : x ∈ B := (replacementCommChain_le_left B A (rA - 3)) hxDrA3
                have hxP : x ∈ (P : Subgroup G) := hB_le_P hxB'
                have hM_le_DrA2 : M ≤ replacementCommChain B A (rA - 2) := by
                  dsimp [M]
                  rw [Subgroup.closure_le]
                  intro y hy
                  rcases hy with ⟨v, hvA, rfl⟩
                  have hsub : rA - 2 = (rA - 3) + 1 := by
                    omega
                  rw [hsub, replacementCommChain_succ]
                  exact Subgroup.commutator_mem_commutator hxDrA3 hvA
                have hM_le_B : M ≤ B := hM_le_DrA2.trans (replacementCommChain_le_left B A (rA - 2))
                have hnA_le_rA_sub2 : nA ≤ rA - 2 := by
                  omega
                have hM_le_DnA : M ≤ replacementCommChain B A nA :=
                  hM_le_DrA2.trans (replacementCommChain_antitone B A hnA_le_rA_sub2)
                have hM_comm : IsMulCommutative M := by
                  refine ⟨?_⟩
                  exact ⟨fun y z => by
                    apply Subtype.ext
                    simpa using
                      (setLike_mul_comm
                        (s := replacementCommChain B A nA)
                        (hM_le_DnA y.2) (hM_le_DnA z.2))⟩
                have hAstar :
                    Astar ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) := by
                  dsimp [Astar, C, M]
                  simpa using
                    (thompsonReplacement_base (G := G) (P := (P : Subgroup G))
                      (A := A) hA hxP hM_comm)
                have hAinfB_le_C : A ⊓ B ≤ C := by
                  intro y hy
                  dsimp [C, subgroupCentralizerIn']
                  refine ⟨?_, hy.1⟩
                  show y ∈ Subgroup.centralizer (M : Set G)
                  rw [Subgroup.mem_centralizer_iff]
                  intro m hmM
                  have hycent :=
                    hAinfB_cent_Di (rA - 2) (by omega : 1 ≤ rA - 2) hy
                  exact (Subgroup.mem_centralizer_iff.mp hycent m) (hM_le_DrA2 hmM)
                have hAinfB_le_AstarinfB : A ⊓ B ≤ Astar ⊓ B := by
                  intro y hy
                  exact ⟨(show C ≤ Astar from le_sup_right) (hAinfB_le_C hy), hy.2⟩
                have hxu_mem_M : ⁅x, u⁆ ∈ M := by
                  dsimp [M]
                  exact Subgroup.subset_closure ⟨u, huA, rfl⟩
                have hxu_mem_B : ⁅x, u⁆ ∈ B := hM_le_B hxu_mem_M
                have hxu_not_mem_A : ⁅x, u⁆ ∉ A := by
                  intro hxuA
                  have hxu_centA : ⁅x, u⁆ ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
                        hxuA
                  exact hxu_not_centA hxu_centA
                have hAstar_lt : A ⊓ B < Astar ⊓ B := by
                  have hne : A ⊓ B ≠ Astar ⊓ B := by
                    intro hEq
                    have hxu_mem_AstarB : ⁅x, u⁆ ∈ Astar ⊓ B := by
                      exact ⟨(show M ≤ Astar from le_sup_left) hxu_mem_M, hxu_mem_B⟩
                    have hxu_mem_AB : ⁅x, u⁆ ∈ A ⊓ B := by
                      simpa [hEq] using hxu_mem_AstarB
                    exact hxu_not_mem_A hxu_mem_AB.1
                  exact lt_of_le_of_ne hAinfB_le_AstarinfB hne
                have hDrA1_le_A : replacementCommChain B A (rA - 1) ≤ A := by
                  have hsucc : replacementCommChain B A ((rA - 1) + 1) = ⊥ := by
                    have hsub : (rA - 1) + 1 = rA := by
                      omega
                    simpa [hsub] using hrA_bot
                  exact
                    replacementCommChain_le_of_succ_eq_bot
                      (G := G) (P := (P : Subgroup G)) (B := B) (A := A)
                      hA hB_le_P hsucc
                have hM_le_P : M ≤ (P : Subgroup G) := hM_le_B.trans hB_le_P
                have hM_comm2 : ⁅⁅M, A⁆, A⁆ = ⊥ := by
                  have hMA_le_DrA1 : ⁅M, A⁆ ≤ replacementCommChain B A (rA - 1) := by
                    have hsub : rA - 1 = (rA - 2) + 1 := by
                      omega
                    rw [hsub, replacementCommChain_succ]
                    exact Subgroup.commutator_mono hM_le_DrA2 le_rfl
                  have hMA_le_A : ⁅M, A⁆ ≤ A := hMA_le_DrA1.trans hDrA1_le_A
                  exact
                    (Subgroup.commutator_eq_bot_iff_le_centralizer).2
                      (hMA_le_A.trans
                        ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1))
                have hM_le_norm_A : M ≤ Subgroup.normalizer (A : Set G) := by
                  exact
                    (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                      (G := G) (P := (P : Subgroup G)) (A := A) (B := M) hA hM_le_P).2
                      hM_comm2
                have hAstar_le_norm_A : Astar ≤ Subgroup.normalizer (A : Set G) := by
                  rw [sup_le_iff]
                  constructor
                  · exact hM_le_norm_A
                  · trans A
                    · dsimp [C, subgroupCentralizerIn']
                      simp
                    · exact Subgroup.le_normalizer
                exact ⟨Astar, hAstar, hAstar_lt, hAstar_le_norm_A⟩)
          refine ⟨A, hA, ?_, ?_⟩
          · exact
              (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) (P := (P : Subgroup G)) (A := A) (B := B) hA hB_le_P).1 hB_norm_A
          · have hP_le_norm_Z : (P : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) := by
              exact
                Subgroup.le_normalizer.trans
                  (normalizer_le_normalizer_thompsonCenter (G := G) (P : Subgroup G))
            have hA_le_norm_Z : A ≤ Subgroup.normalizer (Z : Set G) := hA.1.trans hP_le_norm_Z
            have hA_le_norm_B : A ≤ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact le_top
            have hA_le_norm_B0 : A ≤ Subgroup.normalizer (B0 : Set G) := by
              intro a ha
              simpa [B0] using
                (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z)
                  ⟨hA_le_norm_B ha, hA_le_norm_Z ha⟩)
            have hpCore_quot_bot' : pCore p (G ⧸ L) = ⊥ := by
              let : L.Normal := by
                dsimp [L]
                infer_instance
              let K : Subgroup G := Subgroup.comap qL (pCore p (G ⧸ L))
              have hK_normal : K.Normal := by
                dsimp [K, qL]
                infer_instance
              have hpCore_le_Pbar : pCore p (G ⧸ L) ≤ (Pbar : Subgroup (G ⧸ L)) := by
                let R : Subgroup (G ⧸ L) := pCore p (G ⧸ L)
                have hRp : IsPGroup p R := by
                  simpa [R] using (pCore_isPGroup (G := G ⧸ L) (p := p))
                have : R.Normal := by
                  dsimp [R]
                  infer_instance
                obtain ⟨Q', hRQ'⟩ := IsPGroup.exists_le_sylow (G := G ⧸ L) (p := p) hRp
                obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ L) Q' Pbar
                have hR_le_gQ : R ≤ ((g • Q' : Sylow p (G ⧸ L)) : Subgroup (G ⧸ L)) := by
                  intro r hr
                  rw [Sylow.coe_subgroup_smul]
                  refine (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
                    (S := (Q' : Subgroup (G ⧸ L))) (x := r)).2 ?_
                  have hconj : g⁻¹ * r * g ∈ R := by
                    simpa using ((inferInstance : R.Normal).conj_mem r hr g⁻¹)
                  exact hRQ' hconj
                have hR_le_Pbar : R ≤ (Pbar : Subgroup (G ⧸ L)) := by
                  simpa [hg] using hR_le_gQ
                simpa [R] using hR_le_Pbar
              have hPK_map : ((P : Subgroup G) ⊓ K).map qL = pCore p (G ⧸ L) := by
                apply le_antisymm
                · have hK_map : K.map qL = pCore p (G ⧸ L) := by
                    dsimp [K]
                    simpa using
                      (Subgroup.map_comap_eq_self_of_surjective
                        (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
                  have hmap_le : ((P : Subgroup G) ⊓ K).map qL ≤ K.map qL :=
                    Subgroup.map_mono (f := qL) inf_le_right
                  simpa [hK_map] using hmap_le
                · intro x hx
                  have hxPbar : x ∈ (Pbar : Subgroup (G ⧸ L)) := hpCore_le_Pbar hx
                  have hxPmap : x ∈ ((P : Subgroup G).map qL) := by
                    simpa [Pbar, qL] using hxPbar
                  rcases Subgroup.mem_map.mp hxPmap with ⟨y, hyP, rfl⟩
                  have hyK : y ∈ K := by
                    simpa [K] using hx
                  exact Subgroup.mem_map.mpr ⟨y, ⟨hyP, hyK⟩, rfl⟩
              have hL_le_K : L ≤ K := by
                dsimp [K, qL]
                simpa [QuotientGroup.ker_mk'] using
                  (Subgroup.ker_le_comap (f := QuotientGroup.mk' L) (H := pCore p (G ⧸ L)))
              have hK_eq : K = L ⊔ ((P : Subgroup G) ⊓ K) := by
                apply le_antisymm
                · intro x hxK
                  have hxmap : qL x ∈ pCore p (G ⧸ L) := hxK
                  rw [← hPK_map] at hxmap
                  rcases Subgroup.mem_map.mp hxmap with ⟨y, hyPK, hxy⟩
                  have hxy1 : qL (x * y⁻¹) = 1 := by
                    rw [map_mul, map_inv, hxy]
                    simp
                  have hker : x * y⁻¹ ∈ L := by
                    have hker' : x * y⁻¹ ∈ qL.ker := by
                      simpa [MonoidHom.mem_ker] using hxy1
                    simpa [qL, QuotientGroup.ker_mk'] using hker'
                  have hxsup : x * y⁻¹ ∈ L ⊔ ((P : Subgroup G) ⊓ K) := by
                    exact Subgroup.mem_sup_left hker
                  have hysup : y ∈ L ⊔ ((P : Subgroup G) ⊓ K) := by
                    exact Subgroup.mem_sup_right hyPK
                  simpa [mul_assoc] using
                    (Subgroup.mul_mem (L ⊔ ((P : Subgroup G) ⊓ K)) hxsup hysup)
                · exact sup_le hL_le_K inf_le_right
              have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
                simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
              have hPcapK_le_norm_B0 : (P : Subgroup G) ⊓ K ≤ Subgroup.normalizer (B0 : Set G) := by
                intro x hx
                have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
                  rw [Subgroup.normalizer_eq_top (H := B)]
                  simp
                have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := hP_le_norm_Z hx.1
                simpa [B0] using
                  (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hxB, hxZ⟩)
              have hK_le_norm_B0 : K ≤ Subgroup.normalizer (B0 : Set G) := by
                rw [hK_eq]
                exact sup_le hL_le_norm_B0 hPcapK_le_norm_B0
              have hK_le_L : K ≤ L := by
                let : K.Normal := hK_normal
                simpa [L] using
                  (Subgroup.normal_le_normalCore
                    (H := Subgroup.normalizer (B0 : Set G)) (N := K)).2 hK_le_norm_B0
              have hK_eq_L : K = L := le_antisymm hK_le_L hL_le_K
              have hK_map : K.map qL = pCore p (G ⧸ L) := by
                dsimp [K]
                simpa using
                  (Subgroup.map_comap_eq_self_of_surjective
                    (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
              have hKmap_bot : K.map qL = ⊥ := by
                apply (Subgroup.map_eq_bot_iff (H := K) (f := qL)).2
                simp [qL, QuotientGroup.ker_mk', hK_eq_L]
              exact hK_map.symm.trans hKmap_bot
            let N : Subgroup G := Subgroup.normalizer (B : Set G)
            let C : Subgroup G := Subgroup.centralizer (B : Set G)
            have hN_eq_top : N = ⊤ := by
              dsimp [N]
              exact Subgroup.normalizer_eq_top (H := B)
            have hA_p : IsPGroup p A := IsPGroup.to_le P.isPGroup' hA.1
            have hA_le_N : A ≤ N := by
              rw [hN_eq_top]
              exact le_top
            have hC_le_L : C ≤ L := by
              have hC_le_cent_B0 : C ≤ Subgroup.centralizer (B0 : Set G) := by
                exact Subgroup.centralizer_le (show (B0 : Set G) ⊆ (B : Set G) from fun _ hx => hx.1)
              have hC_le_norm_B0 : C ≤ Subgroup.normalizer (B0 : Set G) := by
                exact hC_le_cent_B0.trans (centralizer_le_normalizer (R := B0))
              let : C.Normal := by
                dsimp [C]
                exact Subgroup.normal_centralizer (H := B)
              simpa [L] using
                (Subgroup.normal_le_normalCore
                  (H := Subgroup.normalizer (B0 : Set G)) (N := C)).2 hC_le_norm_B0
            have hBQ_normal : (pPrimeCore p G ⊔ B).Normal := by infer_instance
            have hstableA :
                ((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))) ≤
                  pCore p (N ⧸ C.subgroupOf N) := by
              simpa [PStableGroup', N, C] using
                hstable B A hBQ_normal hBp hA_p hA_le_N
                  ((thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                    (G := G) (P := (P : Subgroup G)) (A := A) (B := B) hA hB_le_P).1 hB_norm_A)
            have hNmap_top : N.map qL = ⊤ := by
              rw [hN_eq_top]
              simpa [qL] using
                (Subgroup.map_top_of_surjective qL (QuotientGroup.mk'_surjective L))
            have hqN_surj : Function.Surjective (qL.comp N.subtype) := by
              intro y
              have hy : y ∈ N.map qL := by
                rw [hNmap_top]
                exact Subgroup.mem_top y
              rcases Subgroup.mem_map.mp hy with ⟨n, hn, hqy⟩
              exact ⟨Subtype.mk n hn, hqy⟩
            have hCN : C ≤ N := by
              simpa [N, C] using (centralizer_le_normalizer (G := G) B)
            let : (C.subgroupOf N).Normal := by
              exact
                (Subgroup.normal_subgroupOf_iff_le_normalizer
                  (H := C) (K := N) hCN).2
                  (by simpa [N, C] using CFSG.normalizer_le_normalizer_centralizer (G := G) B)
            let phi : N ⧸ C.subgroupOf N →* G ⧸ L :=
              QuotientGroup.lift (C.subgroupOf N) (qL.comp N.subtype) (by
                intro c hc
                exact (QuotientGroup.eq_one_iff (N := L) (x := (c : G))).2 (hC_le_L hc))
            have hphi_surj : Function.Surjective phi := by
              intro y
              rcases hqN_surj y with ⟨n, hnq⟩
              refine ⟨QuotientGroup.mk' (C.subgroupOf N) n, ?_⟩
              change qL (n : G) = y
              exact hnq
            have hAimage_bot :
                (((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) = ⊥ := by
              apply bot_unique
              calc
                (((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) ≤
                    (pCore p (N ⧸ C.subgroupOf N)).map phi := by
                      exact Subgroup.map_mono hstableA
                _ ≤ pCore p (G ⧸ L) := by
                      exact pCore_map_le_pCore_of_surjective (G := N ⧸ C.subgroupOf N)
                        (p := p) phi hphi_surj
                _ = ⊥ := hpCore_quot_bot'
            intro a ha
            have haN : a ∈ N := hA_le_N ha
            have haSub : (Subtype.mk a haN : N) ∈ A.subgroupOf N := ha
            have haMap :
                QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN) ∈
                  (A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) :=
              Subgroup.mem_map_of_mem (QuotientGroup.mk' (C.subgroupOf N)) haSub
            have hphi_mem :
                phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                  (((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) :=
              Subgroup.mem_map_of_mem phi haMap
            have hphi_eq : phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) = 1 := by
              have :
                  phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                    (⊥ : Subgroup (G ⧸ L)) := by
                simpa [hAimage_bot] using hphi_mem
              simpa using this
            have haq : qL a = 1 := by
              change qL a = 1 at hphi_eq
              exact hphi_eq
            exact (QuotientGroup.eq_one_iff (N := L) (x := a)).1 haq
        have hB_comm : IsMulCommutative B := by
          -- Gorenstein 2.10, fifth paragraph:
          -- with `X = Z(J(P ∩ L))`, the normal closure of `Z ∩ B` lies in `X`,
          -- hence `B` is abelian.
          obtain ⟨A, hA, hcomm2, hA_le_L⟩ := hA_exists
          have hB_norm_A : B ≤ Subgroup.normalizer (A : Set G) := by
            exact
              (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) hA hB_le_P).2 hcomm2
          let R : Subgroup G := (P : Subgroup G) ⊓ L
          let X : Subgroup G := thompsonCenter (G := G) R
          have hA_le_R : A ≤ R := by
            intro x hx
            exact ⟨hA.1 hx, hA_le_L hx⟩
          have hAinP :
              (A.subgroupOf (P : Subgroup G)) ∈
                thompsonAbelianSubgroups (G := P) (⊤ : Subgroup P) := by
            refine ⟨by simp, ?_, ?_⟩
            · let : IsMulCommutative A := hA.2.1
              infer_instance
            · intro C hC hCcomm
              have hAmax := hA.2.2 (C.map P.toSubgroup.subtype) (by
                simpa using
                  (Subgroup.map_subtype_le (H := (P : Subgroup G)) (K := C))) (by
                    exact Subgroup.map_isMulCommutative (H := C) P.toSubgroup.subtype)
              calc
                Nat.card C = Nat.card (C.map P.toSubgroup.subtype) := by
                  symm
                  exact Subgroup.card_subtype (P : Subgroup G) C
                _ ≤ Nat.card A := hAmax
                _ = Nat.card (A.subgroupOf (P : Subgroup G)) := by
                  simpa [Subgroup.map_subgroupOf_eq_of_le hA.1] using
                    (Subgroup.card_subtype (P : Subgroup G) (A.subgroupOf (P : Subgroup G)))
          have hZ_le_A : Z ≤ A := by
            simpa [Z, Subgroup.map_subgroupOf_eq_of_le hA.1] using
              (thompsonCenter_le_map_of_mem_thompsonAbelianSubgroups
                (G := G) (p := p) P hAinP)
          have hZ_le_X : Z ≤ X := by
            exact
              thompsonCenter_le_of_mem_thompsonAbelianSubgroups
                (G := G) (P := (P : Subgroup G)) (R := R) inf_le_left hA hZ_le_A hA_le_R
          have hB0_le_X : B0 ≤ X := by
            intro x hx
            exact hZ_le_X hx.2
          let : L.Normal := by
            dsimp [L]
            infer_instance
          have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
            obtain ⟨S, hS_map⟩ := exists_sylow_subgroup_map_eq_inf (G := G) (p := p) P L
            simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hconj_B0_le_X : Group.conjugatesOfSet (B0 : Set G) ⊆ X := by
            intro y hy
            rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨x, hx, hxy⟩
            rcases isConj_iff.mp hxy with ⟨g, rfl⟩
            have hg : g ∈ Subgroup.normalizer (R : Set G) ⊔ L := by
              rw [hFr]
              exact Subgroup.mem_top g
            rcases
                (Subgroup.mem_sup_of_normal_right
                  (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
              ⟨n, hnR, l, hlL, rfl⟩
            have hlB0 : l ∈ Subgroup.normalizer (B0 : Set G) := hL_le_norm_B0 hlL
            have hlx : l * x * l⁻¹ ∈ X := by
              exact hB0_le_X ((Subgroup.mem_normalizer_iff.mp hlB0 _).1 hx)
            have hnX : n ∈ Subgroup.normalizer (X : Set G) := by
              simpa [X] using (normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
            have hnx : n * (l * x * l⁻¹) * n⁻¹ ∈ X :=
              (Subgroup.mem_normalizer_iff.mp hnX _).1 hlx
            simpa [mul_assoc] using hnx
          have hB_le_X : B ≤ X := by
            rw [← hB1_eq_B]
            dsimp [B1]
            rw [Subgroup.normalClosure, Subgroup.closure_le]
            exact hconj_B0_le_X
          let : IsMulCommutative X := thompsonCenter_isMulCommutative (G := G) R
          refine (Subgroup.le_centralizer_iff_isMulCommutative (K := B)).1 ?_
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          simpa using
            (setLike_mul_comm (s := X) (hB_le_X hy) (hB_le_X hx))
        have hpCore_quot_bot : pCore p (G ⧸ L) = ⊥ := by
          let : L.Normal := by
            dsimp [L]
            infer_instance
          let K : Subgroup G := Subgroup.comap qL (pCore p (G ⧸ L))
          have hK_normal : K.Normal := by
            dsimp [K, qL]
            infer_instance
          have hpCore_le_Pbar : pCore p (G ⧸ L) ≤ (Pbar : Subgroup (G ⧸ L)) := by
            let R : Subgroup (G ⧸ L) := pCore p (G ⧸ L)
            have hRp : IsPGroup p R := by
              simpa [R] using (pCore_isPGroup (G := G ⧸ L) (p := p))
            have : R.Normal := by
              dsimp [R]
              infer_instance
            obtain ⟨Q', hRQ'⟩ := IsPGroup.exists_le_sylow (G := G ⧸ L) (p := p) hRp
            obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ L) Q' Pbar
            have hR_le_gQ : R ≤ ((g • Q' : Sylow p (G ⧸ L)) : Subgroup (G ⧸ L)) := by
              intro r hr
              rw [Sylow.coe_subgroup_smul]
              refine (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
                (S := (Q' : Subgroup (G ⧸ L))) (x := r)).2 ?_
              have hconj : g⁻¹ * r * g ∈ R := by
                simpa using ((inferInstance : R.Normal).conj_mem r hr g⁻¹)
              exact hRQ' hconj
            have hR_le_Pbar : R ≤ (Pbar : Subgroup (G ⧸ L)) := by
              simpa [hg] using hR_le_gQ
            simpa [R] using hR_le_Pbar
          have hPK_map : ((P : Subgroup G) ⊓ K).map qL = pCore p (G ⧸ L) := by
            apply le_antisymm
            · have hK_map : K.map qL = pCore p (G ⧸ L) := by
                dsimp [K]
                simpa using
                  (Subgroup.map_comap_eq_self_of_surjective
                    (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
              have hmap_le : ((P : Subgroup G) ⊓ K).map qL ≤ K.map qL :=
                Subgroup.map_mono (f := qL) inf_le_right
              simpa [hK_map] using hmap_le
            · intro x hx
              have hxPbar : x ∈ (Pbar : Subgroup (G ⧸ L)) := hpCore_le_Pbar hx
              have hxPmap : x ∈ ((P : Subgroup G).map qL) := by
                simpa [Pbar, qL] using hxPbar
              rcases Subgroup.mem_map.mp hxPmap with ⟨y, hyP, rfl⟩
              have hyK : y ∈ K := by
                simpa [K] using hx
              exact Subgroup.mem_map.mpr ⟨y, ⟨hyP, hyK⟩, rfl⟩
          have hL_le_K : L ≤ K := by
            dsimp [K, qL]
            simpa [QuotientGroup.ker_mk'] using
              (Subgroup.ker_le_comap (f := QuotientGroup.mk' L) (H := pCore p (G ⧸ L)))
          have hK_eq : K = L ⊔ ((P : Subgroup G) ⊓ K) := by
            apply le_antisymm
            · intro x hxK
              have hxmap : qL x ∈ pCore p (G ⧸ L) := hxK
              rw [← hPK_map] at hxmap
              rcases Subgroup.mem_map.mp hxmap with ⟨y, hyPK, hxy⟩
              have hxy1 : qL (x * y⁻¹) = 1 := by
                rw [map_mul, map_inv, hxy]
                simp
              have hker : x * y⁻¹ ∈ L := by
                have hker' : x * y⁻¹ ∈ qL.ker := by
                  simpa [MonoidHom.mem_ker] using hxy1
                simpa [qL, QuotientGroup.ker_mk'] using hker'
              have hxsup : x * y⁻¹ ∈ L ⊔ ((P : Subgroup G) ⊓ K) := by
                exact Subgroup.mem_sup_left hker
              have hysup : y ∈ L ⊔ ((P : Subgroup G) ⊓ K) := by
                exact Subgroup.mem_sup_right hyPK
              simpa [mul_assoc] using (Subgroup.mul_mem (L ⊔ ((P : Subgroup G) ⊓ K)) hxsup hysup)
            · exact sup_le hL_le_K inf_le_right
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hPcapK_le_norm_B0 : (P : Subgroup G) ⊓ K ≤ Subgroup.normalizer (B0 : Set G) := by
            intro x hx
            have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              simp
            have hP_le_norm_Z : (P : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) := by
              exact (Subgroup.le_normalizer (H := (P : Subgroup G))).trans
                (by simpa [Z] using (normalizer_le_normalizer_thompsonCenter (G := G) (P : Subgroup G)))
            have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := hP_le_norm_Z hx.1
            simpa [B0] using
              (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hxB, hxZ⟩)
          have hK_le_norm_B0 : K ≤ Subgroup.normalizer (B0 : Set G) := by
            rw [hK_eq]
            exact sup_le hL_le_norm_B0 hPcapK_le_norm_B0
          have hK_le_L : K ≤ L := by
            let : K.Normal := hK_normal
            simpa [L] using
              (Subgroup.normal_le_normalCore
                (H := Subgroup.normalizer (B0 : Set G)) (N := K)).2 hK_le_norm_B0
          have hK_eq_L : K = L := le_antisymm hK_le_L hL_le_K
          have hK_map : K.map qL = pCore p (G ⧸ L) := by
            dsimp [K]
            simpa using
              (Subgroup.map_comap_eq_self_of_surjective
                (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
          have hKmap_bot : K.map qL = ⊥ := by
            apply (Subgroup.map_eq_bot_iff (H := K) (f := qL)).2
            simp [qL, QuotientGroup.ker_mk', hK_eq_L]
          exact hK_map.symm.trans hKmap_bot
        have hJ_not_le_L :
            ¬ thompsonSubgroup (G := G) (P : Subgroup G) ≤ L := by
          -- Gorenstein 2.10, third paragraph:
          -- if `J(P) ≤ P ∩ L`, then `G = L N_G(J(P ∩ L))` forces `Z ∩ B ◁ G`.
          let : L.Normal := by
            dsimp [L]
            infer_instance
          intro hJ_le_L
          let R : Subgroup G := (P : Subgroup G) ⊓ L
          have hJ_le_R : thompsonSubgroup (G := G) (P : Subgroup G) ≤ R := by
            intro x hx
            exact ⟨thompsonSubgroup_le (G := G) (P : Subgroup G) hx, hJ_le_L hx⟩
          have hZ_eq_R : thompsonCenter (G := G) R = Z := by
            simpa [Z, R] using
              (thompsonCenter_eq_of_le (G := G) (P := (P : Subgroup G)) (R := R)
                inf_le_left hJ_le_R)
          have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
            obtain ⟨S, hS_map⟩ := exists_sylow_subgroup_map_eq_inf (G := G) (p := p) P L
            simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hB0_normal' : B0.Normal := by
            apply (Subgroup.normalizer_eq_top_iff).mp
            apply top_le_iff.mp
            rw [← hFr]
            intro g hg
            rcases
                (Subgroup.mem_sup_of_normal_right
                  (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
              ⟨n, hnR, l, hlL, rfl⟩
            have hnZ :
                n ∈ Subgroup.normalizer (Z : Set G) := by
              have hnTc :
                  n ∈ Subgroup.normalizer (thompsonCenter (G := G) R : Set G) :=
                (normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
              simpa [hZ_eq_R] using hnTc
            have hnB :
                n ∈ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              simp
            have hnB0 :
                n ∈ Subgroup.normalizer (B0 : Set G) := by
              simpa [B0] using
                (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hnB, hnZ⟩)
            exact (Subgroup.normalizer (B0 : Set G)).mul_mem hnB0 (hL_le_norm_B0 hlL)
          exact hB0_not_normal hB0_normal'
        have hA1_exists :
            ∃ A1 : Subgroup G,
              A1 ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) ∧
                ¬ A1 ≤ L := by
          -- Gorenstein 2.10, sixth paragraph:
          -- since `J(P) ⊄ L ∩ P`, choose `A1 ∈ A(P)` with `A1 ⊄ L`.
          by_contra hA1_not_exists
          apply hJ_not_le_L
          refine sSup_le ?_
          intro A hA
          by_contra hA_not_le_L
          exact hA1_not_exists ⟨A, hA, hA_not_le_L⟩
        let Sbad : Set (Subgroup G) :=
          {A : Subgroup G |
            A ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) ∧ ¬ A ≤ L}
        have hSbad_nonempty : Sbad.Nonempty := by
          rcases hA1_exists with ⟨A1, hA1, hA1_not_le_L⟩
          exact ⟨A1, hA1, hA1_not_le_L⟩
        have hSbad_finite : Sbad.Finite := Set.toFinite Sbad
        obtain ⟨A1, hA1max⟩ :=
          hSbad_finite.exists_maximalFor (f := fun A : Subgroup G => Nat.card ↥(A ⊓ B))
            Sbad hSbad_nonempty
        have hA1Sbad : A1 ∈ Sbad := hA1max.prop
        have hA1 : A1 ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) := hA1Sbad.1
        have hA1_not_le_L : ¬ A1 ≤ L := hA1Sbad.2
        have htriple_ne_bot : ⁅⁅B, A1⁆, A1⁆ ≠ ⊥ := by
          -- Gorenstein 2.10, sixth paragraph:
          -- if `[B, A1, A1] = 1`, the previous argument gives `A1 ≤ L`.
          intro htriple_bot
          let N : Subgroup G := Subgroup.normalizer (B : Set G)
          let C : Subgroup G := Subgroup.centralizer (B : Set G)
          have hN_eq_top : N = ⊤ := by
            dsimp [N]
            exact Subgroup.normalizer_eq_top (H := B)
          have hA1_p : IsPGroup p A1 := IsPGroup.to_le P.isPGroup' hA1.1
          have hA1_le_N : A1 ≤ N := by
            rw [hN_eq_top]
            exact le_top
          have hC_le_L : C ≤ L := by
            have hC_le_cent_B0 : C ≤ Subgroup.centralizer (B0 : Set G) := by
              exact Subgroup.centralizer_le (show (B0 : Set G) ⊆ (B : Set G) from fun _ hx => hx.1)
            have hC_le_norm_B0 : C ≤ Subgroup.normalizer (B0 : Set G) := by
              exact hC_le_cent_B0.trans (centralizer_le_normalizer (R := B0))
            let : C.Normal := by
              dsimp [C]
              exact Subgroup.normal_centralizer (H := B)
            simpa [L] using
              (Subgroup.normal_le_normalCore
                (H := Subgroup.normalizer (B0 : Set G)) (N := C)).2 hC_le_norm_B0
          have hBQ_normal : (pPrimeCore p G ⊔ B).Normal := by infer_instance
          have hstableA1 :
              ((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))) ≤
                pCore p (N ⧸ C.subgroupOf N) := by
            simpa [PStableGroup', N, C] using
              hstable B A1 hBQ_normal hBp hA1_p hA1_le_N htriple_bot
          have hNmap_top : N.map qL = ⊤ := by
            rw [hN_eq_top]
            simpa [qL] using
              (Subgroup.map_top_of_surjective qL (QuotientGroup.mk'_surjective L))
          have hqN_surj : Function.Surjective (qL.comp N.subtype) := by
            intro y
            have hy : y ∈ N.map qL := by
              rw [hNmap_top]
              exact Subgroup.mem_top y
            rcases Subgroup.mem_map.mp hy with ⟨n, hn, hqy⟩
            exact ⟨Subtype.mk n hn, hqy⟩
          have hCN : C ≤ N := by
            simpa [N, C] using (centralizer_le_normalizer (G := G) B)
          let : (C.subgroupOf N).Normal := by
            exact
              (Subgroup.normal_subgroupOf_iff_le_normalizer
                (H := C) (K := N) hCN).2
                (by simpa [N, C] using CFSG.normalizer_le_normalizer_centralizer (G := G) B)
          let phi : N ⧸ C.subgroupOf N →* G ⧸ L :=
            QuotientGroup.lift (C.subgroupOf N) (qL.comp N.subtype) (by
              intro c hc
              exact (QuotientGroup.eq_one_iff (N := L) (x := (c : G))).2 (hC_le_L hc))
          have hphi_surj : Function.Surjective phi := by
            intro y
            rcases hqN_surj y with ⟨n, hnq⟩
            refine ⟨QuotientGroup.mk' (C.subgroupOf N) n, ?_⟩
            change qL (n : G) = y
            exact hnq
          have hAimage_bot :
              (((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) = ⊥ := by
            apply bot_unique
            calc
              (((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) ≤
                  (pCore p (N ⧸ C.subgroupOf N)).map phi := by
                    exact Subgroup.map_mono hstableA1
              _ ≤ pCore p (G ⧸ L) := by
                    exact pCore_map_le_pCore_of_surjective (G := N ⧸ C.subgroupOf N)
                      (p := p) phi hphi_surj
              _ = ⊥ := hpCore_quot_bot
          have hA1_le_L : A1 ≤ L := by
            intro a ha
            have haN : a ∈ N := hA1_le_N ha
            have haSub : (Subtype.mk a haN : N) ∈ A1.subgroupOf N := ha
            have haMap :
                QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN) ∈
                  (A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) :=
              Subgroup.mem_map_of_mem (QuotientGroup.mk' (C.subgroupOf N)) haSub
            have hphi_mem :
                phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                  (((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) :=
              Subgroup.mem_map_of_mem phi haMap
            have hphi_eq : phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) = 1 := by
              have :
                  phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                    (⊥ : Subgroup (G ⧸ L)) := by
                simpa [hAimage_bot] using hphi_mem
              simpa using this
            have haq : qL a = 1 := by
              change qL a = 1 at hphi_eq
              exact hphi_eq
            exact (QuotientGroup.eq_one_iff (N := L) (x := a)).1 haq
          exact hA1_not_le_L hA1_le_L
        have hreplacement :
            ∃ Astar : Subgroup G,
              Astar ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) ∧
                A1 ⊓ B < Astar ⊓ B ∧
                Astar ≤ Subgroup.normalizer (A1 : Set G) := by
          -- Gorenstein 2.10, final paragraph:
          -- choose `A1` with `|A1 ∩ B|` maximal and apply Thompson replacement.
          have hB_not_norm_A1 : ¬ B ≤ Subgroup.normalizer (A1 : Set G) := by
            intro hB_norm_A1
            exact htriple_ne_bot <|
              (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) (P := (P : Subgroup G)) (A := A1) (B := B) hA1 hB_le_P).1 hB_norm_A1
          let N : Subgroup G := B ⊓ Subgroup.normalizer (A1 : Set G)
          let H : Subgroup G := A1 ⊔ B
          have hH_le_P : H ≤ (P : Subgroup G) := by
            dsimp [H]
            exact sup_le hA1.1 hB_le_P
          have hA1_le_norm_N : A1 ≤ Subgroup.normalizer (N : Set G) := by
            have hA1_le_norm_B : A1 ≤ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact le_top
            have hA1_le_norm_normA1 :
                A1 ≤ Subgroup.normalizer (Subgroup.normalizer (A1 : Set G) : Set G) := by
              exact
                (Subgroup.le_normalizer : A1 ≤ Subgroup.normalizer (A1 : Set G)).trans
                  (Subgroup.le_normalizer :
                    Subgroup.normalizer (A1 : Set G) ≤
                      Subgroup.normalizer (Subgroup.normalizer (A1 : Set G) : Set G))
            intro a ha
            exact
              (Subgroup.inf_normalizer_le_normalizer_inf
                (H := B) (K := Subgroup.normalizer (A1 : Set G))
                ⟨hA1_le_norm_B ha, hA1_le_norm_normA1 ha⟩)
          have hB_le_norm_N : B ≤ Subgroup.normalizer (N : Set G) := by
            refine subgroup_le_normalizer_of_conj_mem N B ?_
            intro b n hn
            have hbn : (b : G) * n = n * b := by
              exact
                setLike_mul_comm
                  (s := B) b.2 hn.1
            have hconj : (b : G) * n * (b : G)⁻¹ = n := by
              calc
                (b : G) * n * (b : G)⁻¹ = n * (b : G) * (b : G)⁻¹ := by
                  rw [hbn, mul_assoc]
                _ = n := by simp
            simpa [N, hconj] using hn
          have hH_le_norm_N : H ≤ Subgroup.normalizer (N : Set G) := by
            dsimp [H]
            exact sup_le hA1_le_norm_N hB_le_norm_N
          let Nsub : Subgroup H := N.subgroupOf H
          have hNsub_normal : Nsub.Normal := by
            simpa [Nsub] using
              (Subgroup.normal_subgroupOf_of_le_normalizer
                (H := H) (N := N) hH_le_norm_N)
          let qH : H →* H ⧸ Nsub := QuotientGroup.mk' Nsub
          let Bsub : Subgroup H := B.subgroupOf H
          have hBsub_normal : Bsub.Normal := by
            have hH_le_norm_B : H ≤ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact le_top
            simpa [Bsub] using
              (Subgroup.normal_subgroupOf_of_le_normalizer
                (H := H) (N := B) hH_le_norm_B)
          let Bbar : Subgroup (H ⧸ Nsub) := Bsub.map qH
          have hBbar_normal : Bbar.Normal := by
            dsimp [Bbar, qH]
            exact
              Subgroup.Normal.map (H := Bsub) hBsub_normal
                (QuotientGroup.mk' Nsub) (QuotientGroup.mk'_surjective Nsub)
          have hBbar_ne_bot : Bbar ≠ ⊥ := by
            intro hBbar_bot
            apply hB_not_norm_A1
            intro b hb
            have hbH : b ∈ H := by
              dsimp [H]
              exact (show B ≤ A1 ⊔ B from le_sup_right) hb
            have hbsub : (⟨b, hbH⟩ : H) ∈ Bsub := by
              simpa [Bsub, Subgroup.mem_subgroupOf]
            have hBsub_le_Nsub : Bsub ≤ Nsub := by
              have hmap_bot : Bsub.map qH = ⊥ := by
                simpa [Bbar] using hBbar_bot
              simpa [qH, QuotientGroup.ker_mk'] using
                (Subgroup.map_eq_bot_iff (f := qH) (H := Bsub)).1 hmap_bot
            have hbNsub : (⟨b, hbH⟩ : H) ∈ Nsub := hBsub_le_Nsub hbsub
            have hbN : b ∈ N := by
              simpa [Nsub, Subgroup.mem_subgroupOf] using hbNsub
            exact hbN.2
          let Hsub : Subgroup (P : Subgroup G) := H.subgroupOf (P : Subgroup G)
          have hHsub_p : IsPGroup p Hsub := P.isPGroup'.to_subgroup Hsub
          have hHp : IsPGroup p H := by
            exact hHsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hH_le_P)
          let : Fact (IsPGroup p (H ⧸ Nsub)) := ⟨hHp.to_quotient Nsub⟩
          have hx_exists :
              ∃ x ∈ B, x ∉ Subgroup.normalizer (A1 : Set G) ∧
                ∀ u ∈ A1, ⁅x, u⁆ ∈ N := by
            let : Bbar.Normal := hBbar_normal
            have : Nontrivial Bbar := (Subgroup.nontrivial_iff_ne_bot (H := Bbar)).2 hBbar_ne_bot
            obtain ⟨xbar, hxbar_ne_one, hxbar_center⟩ :=
              exists_nontrivial_center_mem_normal (N := Bbar) (p := p)
            obtain ⟨x0, hx0Bsub, hx0eq⟩ := Subgroup.mem_map.mp xbar.2
            have hx0B : (x0 : G) ∈ B := by
              simpa [Bsub, Subgroup.mem_subgroupOf] using hx0Bsub
            have hx0_center : qH x0 ∈ Subgroup.center (H ⧸ Nsub) := by
              simpa [hx0eq] using hxbar_center
            have hx0_ne_one : qH x0 ≠ 1 := by
              intro hx0q_one
              apply hxbar_ne_one
              apply Subtype.ext
              simpa [hx0eq] using hx0q_one
            have hx0_not_norm : (x0 : G) ∉ Subgroup.normalizer (A1 : Set G) := by
              intro hx0_norm
              have hx0Nsub : x0 ∈ Nsub := by
                have hx0N : (x0 : G) ∈ N := ⟨hx0B, hx0_norm⟩
                simpa [Nsub, Subgroup.mem_subgroupOf] using hx0N
              have hx0q_one : qH x0 = 1 := by
                exact (QuotientGroup.eq_one_iff (N := Nsub) x0).2 hx0Nsub
              exact hx0_ne_one hx0q_one
            have hcomm_gen_le_N : ∀ u ∈ A1, ⁅(x0 : G), u⁆ ∈ N := by
              intro u hu
              let uH : H := ⟨u, by
                dsimp [H]
                exact (show A1 ≤ A1 ⊔ B from le_sup_left) hu⟩
              have hcommq :
                  qH x0 * qH uH = qH uH * qH x0 := by
                exact ((Subgroup.mem_center_iff.mp hx0_center) (qH uH)).symm
              have hcomm_q : ⁅qH x0, qH uH⁆ = 1 := by
                exact commutatorElement_eq_one_iff_commute.mpr hcommq
              have hmap_comm : qH ⁅x0, uH⁆ = 1 := by
                calc
                  qH ⁅x0, uH⁆ = ⁅qH x0, qH uH⁆ := by
                    exact map_commutatorElement (f := qH) (g₁ := x0) (g₂ := uH)
                  _ = 1 := hcomm_q
              have hcomm_mem : ⁅x0, uH⁆ ∈ Nsub := by
                exact (QuotientGroup.eq_one_iff (N := Nsub) ⁅x0, uH⁆).1 hmap_comm
              change ⁅(x0 : G), u⁆ ∈ N at hcomm_mem
              exact hcomm_mem
            exact ⟨(x0 : G), hx0B, hx0_not_norm, hcomm_gen_le_N⟩
          obtain ⟨x, hxB, hx_not_norm, hcomm_gen_le_N⟩ := hx_exists
          let M : Subgroup G := Subgroup.closure {g : G | ∃ u ∈ A1, ⁅x, u⁆ = g}
          let C : Subgroup G := subgroupCentralizerIn' A1 M
          let Astar : Subgroup G := M ⊔ C
          have hxP : x ∈ (P : Subgroup G) := hB_le_P hxB
          have hM_le_B : M ≤ B := by
            dsimp [M]
            rw [Subgroup.closure_le]
            intro y hy
            rcases hy with ⟨u, hu, rfl⟩
            exact
              (Subgroup.commutator_le_left (H₁ := B) (H₂ := A1))
                (Subgroup.commutator_mem_commutator hxB hu)
          have hM_comm : IsMulCommutative M := by
            refine ⟨?_⟩
            exact ⟨fun y z => by
              apply Subtype.ext
              simpa using
                (setLike_mul_comm
                  (s := B) (hM_le_B y.2) (hM_le_B z.2))⟩
          have hAstar :
              Astar ∈ thompsonAbelianSubgroups (G := G) (P : Subgroup G) := by
            dsimp [Astar, C, M]
            simpa using
              (thompsonReplacement_base (G := G) (P := (P : Subgroup G))
                (A := A1) hA1 hxP hM_comm)
          have hAstar_lt : A1 ⊓ B < Astar ⊓ B := by
            have hA1infB_le_C : A1 ⊓ B ≤ C := by
              intro y hy
              dsimp [C, subgroupCentralizerIn']
              refine ⟨?_, hy.1⟩
              show y ∈ Subgroup.centralizer (M : Set G)
              rw [Subgroup.mem_centralizer_iff]
              intro m hmM
              have hyB : y ∈ B := hy.2
              have hmB : m ∈ B := hM_le_B hmM
              exact
                setLike_mul_comm
                  (s := B) hmB hyB
            have hA1infB_le_AstarinfB : A1 ⊓ B ≤ Astar ⊓ B := by
              have hC_le_Astar : C ≤ Astar := by
                dsimp [Astar]
                exact le_sup_right
              intro y hy
              exact ⟨hC_le_Astar (hA1infB_le_C hy), hy.2⟩
            have hM_not_le_A1 : ¬ M ≤ A1 := by
              intro hM_le_A1
              have hconj_le : ConjAct.toConjAct x • A1 ≤ A1 := by
                rw [Subgroup.pointwise_smul_def]
                intro y hy
                rcases Subgroup.mem_map.mp hy with ⟨u, hu, rfl⟩
                change x * u * x⁻¹ ∈ A1
                have hxy : ⁅x, u⁆ ∈ A1 := by
                  exact hM_le_A1 <| by
                    dsimp [M]
                    exact Subgroup.subset_closure ⟨u, hu, rfl⟩
                rw [show x * u * x⁻¹ = ⁅x, u⁆ * u by
                  simp [commutatorElement_def, mul_assoc]]
                exact A1.mul_mem hxy hu
              have hconj_eq : ConjAct.toConjAct x • A1 = A1 := by
                apply Subgroup.eq_of_le_of_card_ge hconj_le
                have hinj :
                    Function.Injective
                      ((MulDistribMulAction.toMonoidEnd (ConjAct G) G
                        (ConjAct.toConjAct x)) : G →* G) := by
                  intro a b hab
                  change x * a * x⁻¹ = x * b * x⁻¹ at hab
                  have h' := congrArg (fun t : G => x⁻¹ * t * x) hab
                  simpa [mul_assoc] using h'
                have hcard_conj :
                    Nat.card ↥(ConjAct.toConjAct x • A1) = Nat.card A1 := by
                  rw [Subgroup.pointwise_smul_def]
                  simpa using
                    (Subgroup.card_map_of_injective (K := A1) hinj)
                exact le_of_eq hcard_conj.symm
              have hx_norm : x ∈ Subgroup.normalizer (A1 : Set G) := by
                exact (Subgroup.conjAct_pointwise_smul_iff (H := A1) (g := x)).1 hconj_eq
              exact hx_not_norm hx_norm
            have hne : A1 ⊓ B ≠ Astar ⊓ B := by
              intro hEq
              apply hM_not_le_A1
              intro m hmM
              have hmAstar : m ∈ Astar := by
                dsimp [Astar]
                exact (show M ≤ M ⊔ C from le_sup_left) hmM
              have hmAstarB : m ∈ Astar ⊓ B := ⟨hmAstar, hM_le_B hmM⟩
              have hmA1B : m ∈ A1 ⊓ B := by simpa [hEq] using hmAstarB
              exact hmA1B.1
            exact lt_of_le_of_ne hA1infB_le_AstarinfB hne
          have hAstar_le_norm : Astar ≤ Subgroup.normalizer (A1 : Set G) := by
            rw [sup_le_iff]
            constructor
            · trans B ⊓ (Subgroup.normalizer (A1 : Set G))
              · refine le_inf hM_le_B ?_
                dsimp [M]
                rw [Subgroup.closure_le]
                intro y hy
                rcases hy with ⟨u, hu, rfl⟩
                exact (hcomm_gen_le_N u hu).2
              · exact inf_le_right
            · trans A1
              · subst C
                simp [subgroupCentralizerIn']
              · exact Subgroup.le_normalizer
          exact ⟨Astar, hAstar, hAstar_lt, hAstar_le_norm⟩
        have hcontr : False := by
          obtain ⟨Astar, hAstar, hlt, hAstar_norm⟩ := hreplacement
          have hAstar_le_L : Astar ≤ L := by
            by_contra hAstar_not_le_L
            have hAstarSbad : Astar ∈ Sbad := ⟨hAstar, hAstar_not_le_L⟩
            have hcard_le : Nat.card ↥(A1 ⊓ B) ≤ Nat.card ↥(Astar ⊓ B) :=
              Subgroup.card_le_of_le hlt.le
            have hcard_ne : Nat.card ↥(A1 ⊓ B) ≠ Nat.card ↥(Astar ⊓ B) := by
              intro hEq
              apply hlt.ne
              exact Subgroup.eq_of_le_of_card_ge hlt.le (le_of_eq hEq.symm)
            have hcard_lt : Nat.card ↥(A1 ⊓ B) < Nat.card ↥(Astar ⊓ B) :=
              lt_of_le_of_ne hcard_le hcard_ne
            exact (not_lt_of_ge (hA1max.le hAstarSbad)) hcard_lt
          let R : Subgroup G := (P : Subgroup G) ⊓ L
          let X : Subgroup G := thompsonCenter (G := G) R
          have hB_le_X : B ≤ X := by
            obtain ⟨A, hA, hcomm2, hA_le_L⟩ := hA_exists
            have hB_norm_A : B ≤ Subgroup.normalizer (A : Set G) := by
              exact
                (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                  (G := G) hA hB_le_P).2 hcomm2
            have hA_le_R : A ≤ R := by
              intro x hx
              exact ⟨hA.1 hx, hA_le_L hx⟩
            have hAinP :
                (A.subgroupOf (P : Subgroup G)) ∈
                  thompsonAbelianSubgroups (G := P) (⊤ : Subgroup P) := by
              refine ⟨by simp, ?_, ?_⟩
              · let : IsMulCommutative A := hA.2.1
                infer_instance
              · intro C hC hCcomm
                have hAmax := hA.2.2 (C.map P.toSubgroup.subtype) (by
                  simpa using
                    (Subgroup.map_subtype_le (H := (P : Subgroup G)) (K := C))) (by
                      exact Subgroup.map_isMulCommutative (H := C) P.toSubgroup.subtype)
                calc
                  Nat.card C = Nat.card (C.map P.toSubgroup.subtype) := by
                    symm
                    exact Subgroup.card_subtype (P : Subgroup G) C
                  _ ≤ Nat.card A := hAmax
                  _ = Nat.card (A.subgroupOf (P : Subgroup G)) := by
                    simpa [Subgroup.map_subgroupOf_eq_of_le hA.1] using
                      (Subgroup.card_subtype (P : Subgroup G) (A.subgroupOf (P : Subgroup G)))
            have hZ_le_A :
                thompsonCenter (G := G) (P : Subgroup G) ≤ A := by
              simpa [Subgroup.map_subgroupOf_eq_of_le hA.1] using
                (thompsonCenter_le_map_of_mem_thompsonAbelianSubgroups
                  (G := G) (p := p) P hAinP)
            have hZ_le_X :
                thompsonCenter (G := G) (P : Subgroup G) ≤ X := by
              exact
                thompsonCenter_le_of_mem_thompsonAbelianSubgroups
                  (G := G) (P := (P : Subgroup G)) (R := R) inf_le_left hA hZ_le_A hA_le_R
            have hB0_le_X : B0 ≤ X := by
              intro x hx
              exact hZ_le_X hx.2
            let : L.Normal := by
              dsimp [L]
              infer_instance
            have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
              obtain ⟨S, hS_map⟩ := exists_sylow_subgroup_map_eq_inf (G := G) (p := p) P L
              simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
            have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
              simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
            have hconj_B0_le_X : Group.conjugatesOfSet (B0 : Set G) ⊆ X := by
              intro y hy
              rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨x, hx, hxy⟩
              rcases isConj_iff.mp hxy with ⟨g, rfl⟩
              have hg : g ∈ Subgroup.normalizer (R : Set G) ⊔ L := by
                rw [hFr]
                exact Subgroup.mem_top g
              rcases
                  (Subgroup.mem_sup_of_normal_right
                    (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
                ⟨n, hnR, l, hlL, rfl⟩
              have hlB0 : l ∈ Subgroup.normalizer (B0 : Set G) := hL_le_norm_B0 hlL
              have hlx : l * x * l⁻¹ ∈ X := by
                exact hB0_le_X ((Subgroup.mem_normalizer_iff.mp hlB0 _).1 hx)
              have hnX : n ∈ Subgroup.normalizer (X : Set G) := by
                simpa [X] using (normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
              have hnx : n * (l * x * l⁻¹) * n⁻¹ ∈ X :=
                (Subgroup.mem_normalizer_iff.mp hnX _).1 hlx
              simpa [mul_assoc] using hnx
            rw [← hB1_eq_B]
            dsimp [B1]
            rw [Subgroup.normalClosure, Subgroup.closure_le]
            exact hconj_B0_le_X
          have hAstar_le_R : Astar ≤ R := by
            intro x hx
            exact ⟨hAstar.1 hx, hAstar_le_L hx⟩
          have hAstar_in_R :
              Astar ∈ thompsonAbelianSubgroups (G := G) R := by
            refine ⟨hAstar_le_R, hAstar.2.1, ?_⟩
            intro C hC hCcomm
            exact hAstar.2.2 C (hC.trans inf_le_left) hCcomm
          have hAstar_le_JR : Astar ≤ thompsonSubgroup (G := G) R := le_sSup hAstar_in_R
          have hJcent_le_centAstar :
              Subgroup.centralizer (thompsonSubgroup (G := G) R : Set G) ≤
                Subgroup.centralizer (Astar : Set G) := by
            exact Subgroup.centralizer_le (show (Astar : Set G) ⊆ (thompsonSubgroup (G := G) R : Set G)
              from hAstar_le_JR)
          have hX_le_subcent : X ≤ subgroupCentralizerIn' R Astar := by
            intro z hz
            refine ⟨?_, ?_⟩
            · have hzcent :
                z ∈ Subgroup.centralizer (thompsonSubgroup (G := G) R : Set G) := by
                simpa [X, thompsonCenter, centerIn] using hz.2
              exact hJcent_le_centAstar hzcent
            · exact thompsonCenter_le (G := G) R hz
          have hX_le_Astar : X ≤ Astar := by
            simpa [thompsonAbelianSubgroups_centralizer_eq
              (G := G) (P := R) (A := Astar) hAstar_in_R] using hX_le_subcent
          have hcomm2_Astar : ⁅⁅Astar, A1⁆, A1⁆ = ⊥ := by
            exact
              (thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) (P := (P : Subgroup G)) (A := A1) (B := Astar) hA1 hAstar.1).1
                hAstar_norm
          have htriple_bot : ⁅⁅B, A1⁆, A1⁆ = ⊥ := by
            apply bot_unique
            calc
              ⁅⁅B, A1⁆, A1⁆ ≤ ⁅⁅X, A1⁆, A1⁆ := by
                exact Subgroup.commutator_mono (Subgroup.commutator_mono hB_le_X le_rfl) le_rfl
              _ ≤ ⁅⁅Astar, A1⁆, A1⁆ := by
                exact Subgroup.commutator_mono (Subgroup.commutator_mono hX_le_Astar le_rfl) le_rfl
              _ ≤ ⊥ := by simp [hcomm2_Astar]
          exact htriple_ne_bot htriple_bot
        exact False.elim hcontr
  exact hmain (Nat.card B) B (show B.Normal from inferInstance) hBp hBne rfl

public theorem CFSG.G_theorem_8_2_11
    (hpodd : p ≠ 2) (hOp_ne : pCore p G ≠ ⊥)
    (hconstrained : PConstrainedGroup (G := G) p)
    (hstable : PStableGroup' (G := G) p)
    (P : Sylow p G) :
    (thompsonCenter (G := G) (P : Subgroup G) ⊔ pPrimeCore p G).Normal := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let Pbar : Sylow p (G ⧸ M) :=
    P.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
  have hM_normal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hM_normal
  have hquot_core_bot : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hOp_eq_pCore_quot : Op_p'p p (G ⧸ M) = pCore p (G ⧸ M) := by
    simpa [hquot_core_bot] using
      (Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hquot_core_bot)
  have hconstrained_quot : PConstrainedGroup (G := G ⧸ M) p := by
    simpa [M] using pConstrained_quotient_pPrimeCore (G := G) (p := p) hconstrained
  have hstable_quot : PStableGroup' (G := G ⧸ M) p := by
    simpa [M] using pStable_quotient_pPrimeCore (G := G) (p := p) hstable
  have hcenter_le_Op_quot :
      thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) ≤ Op_p'p p (G ⧸ M) := by
    let ZbarP : Subgroup Pbar :=
      (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))).subgroupOf
        (Pbar : Subgroup (G ⧸ M))
    have hZbar_normal : ZbarP.Normal := by
      simpa [ZbarP] using
        (thompsonCenter_normal_subgroupOf_sylow (G := G ⧸ M) (p := p) Pbar)
    have hZbar_comm : IsMulCommutative ZbarP := by
      let : IsMulCommutative (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))) :=
        thompsonCenter_isMulCommutative (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))
      simpa [ZbarP] using
        (inferInstance :
          IsMulCommutative
            ((thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))).subgroupOf
              (Pbar : Subgroup (G ⧸ M))))
    have hZbar_map_le :
        ZbarP.map Pbar.toSubgroup.subtype ≤ Op_p'p p (G ⧸ M) := by
      exact theorem_8_1_3 (G := G ⧸ M) (p := p) hconstrained_quot hstable_quot Pbar ZbarP
        hZbar_comm
    have hZbar_map_eq :
        ZbarP.map Pbar.toSubgroup.subtype =
          thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) := by
      calc
        ZbarP.map Pbar.toSubgroup.subtype =
            thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) ⊓
              (Pbar : Subgroup (G ⧸ M)) := by
          simp [ZbarP]
        _ = thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) := by
          exact inf_eq_left.mpr (thompsonCenter_le (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)))
    rw [hZbar_map_eq] at hZbar_map_le
    exact hZbar_map_le
  have hcenter_le_pCore_quot :
      thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    rw [hOp_eq_pCore_quot] at hcenter_le_Op_quot
    exact hcenter_le_Op_quot
  have hpCore_ne_quot : pCore p (G ⧸ M) ≠ ⊥ := by
    intro hpCore_eq_bot
    have hmap_le :
        (pCore p G).map q ≤ pCore p (G ⧸ M) :=
      pCore_map_le_pCore_of_surjective (G := G) (p := p) q
        (QuotientGroup.mk'_surjective M)
    have hmap_ne_bot : (pCore p G).map q ≠ ⊥ := by
      intro hmap_eq_bot
      have hleM : pCore p G ≤ M := by
        simpa [M, q, QuotientGroup.ker_mk'] using
          (Subgroup.map_eq_bot_iff (f := q) (H := pCore p G)).1 hmap_eq_bot
      have hpCore_card :
          ∃ n : ℕ, Nat.card (pCore p G) = p ^ n := by
        exact IsPGroup.iff_card.mp (pCore_isPGroup (G := G) (p := p))
      rcases hpCore_card with ⟨n, hcard⟩
      have hcoprime :
          Nat.Coprime (Nat.card (pCore p G)) (Nat.card M) := by
        rw [hcard]
        exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
      have hinf_bot : pCore p G ⊓ M = ⊥ :=
        (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
      have hpCore_eq_bot : pCore p G = ⊥ := by
        rw [inf_eq_left.mpr hleM] at hinf_bot
        exact hinf_bot
      exact hOp_ne hpCore_eq_bot
    rw [hpCore_eq_bot] at hmap_le
    exact hmap_ne_bot (le_antisymm hmap_le bot_le)
  have hreduced_case :
      (pCore p (G ⧸ M) ⊓
        thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))).Normal := by
    simpa [inf_eq_right.mpr hcenter_le_pCore_quot] using
      (theorem_8_2_10 (G := G ⧸ M) (p := p) hpodd hstable_quot
        (B := pCore p (G ⧸ M)) (pCore_isPGroup (G := G ⧸ M) (p := p))
        hpCore_ne_quot Pbar)
  have hpullback_normal :
      (thompsonCenter (G := G) (P : Subgroup G) ⊔ pPrimeCore p G).Normal := by
    let Z : Subgroup G := thompsonCenter (G := G) (P : Subgroup G)
    let Zbar : Subgroup (G ⧸ M) := thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))
    have hZ_map :
        Z.map q = Zbar := by
      have hqinj : Function.Injective (q.comp (P : Subgroup G).subtype) := by
        exact
          quotient_pPrimeCore_subgroupMap_injective (G := G) (p := p) (H := (P : Subgroup G))
            P.isPGroup'
      let f : P →* ((P : Subgroup G).map q) :=
        (q.comp (P : Subgroup G).subtype).codRestrict ((P : Subgroup G).map q) (by
          intro x
          exact Subgroup.mem_map_of_mem q x.2)
      let e : P ≃* ((P : Subgroup G).map q) := by
        refine MulEquiv.ofBijective f ⟨?_, ?_⟩
        · intro a b hab
          exact hqinj <| by exact congrArg Subtype.val hab
        intro x
        rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hxy⟩
        refine ⟨⟨y, hy⟩, ?_⟩
        apply Subtype.ext
        exact hxy
      have hcomp :
          ((Subgroup.subtype ((P : Subgroup G).map q)).comp e.toMonoidHom) =
            q.comp (P : Subgroup G).subtype := by
        rfl
      calc
        Z.map q = ((thompsonCenter (G := P) (⊤ : Subgroup P)).map (P : Subgroup G).subtype).map q := by
          rw [thompsonCenter_top_map_subtype]
        _ = (thompsonCenter (G := P) (⊤ : Subgroup P)).map (q.comp (P : Subgroup G).subtype) := by
          rw [Subgroup.map_map]
        _ = ((thompsonCenter (G := P) (⊤ : Subgroup P)).map e.toMonoidHom).map
              (Subgroup.subtype ((P : Subgroup G).map q)) := by
          rw [Subgroup.map_map, hcomp]
        _ = (thompsonCenter (G := ((P : Subgroup G).map q)) (⊤ : Subgroup ((P : Subgroup G).map q))).map
              (Subgroup.subtype ((P : Subgroup G).map q)) := by
          rw [thompsonCenter_top_map_mulEquiv]
        _ = Zbar := by
          simpa [Zbar, Pbar] using
            thompsonCenter_top_map_subtype (G := G ⧸ M) ((P : Subgroup G).map q)
    have hsup_map :
        (Z ⊔ M).map q = Zbar := by
      calc
        (Z ⊔ M).map q = Z.map q ⊔ M.map q := Subgroup.map_sup _ _ _
        _ = Zbar ⊔ ⊥ := by rw [hZ_map, QuotientGroup.map_mk'_self]
        _ = Zbar := by simp
    have hcomap_eq :
        Subgroup.comap q Zbar = Z ⊔ M := by
      calc
        Subgroup.comap q Zbar = Subgroup.comap q ((Z ⊔ M).map q) := by rw [hsup_map]
        _ = M ⊔ (Z ⊔ M) := by
          simp [q]
        _ = Z ⊔ M := by simp [sup_comm]
    let : Zbar.Normal := by
      simpa [Zbar, inf_eq_right.mpr hcenter_le_pCore_quot] using hreduced_case
    have hcomap_normal : (Subgroup.comap q Zbar).Normal := inferInstance
    simpa [Z, Zbar, M] using hcomap_eq ▸ hcomap_normal
  exact hpullback_normal

end ConstraintAndStability
