module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the `f'`-core

This module packages the source-independent part of (e).  Once part (d)
normalizes the subgroup `B`, its ambient `f'`-core is normalized as well.
Moreover, the preceding conclusion that `C_B(P)` is an `f`-group makes the
centralizer of `P` in that `f'`-core trivial.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

private theorem lemma115_subgroupOf_le_pPrimeCore_map
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K H : Subgroup G} (hKH : K ≤ H)
    [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p ↥H).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p ↥H :=
    le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

/-- Source notation `B₁ = O_{f'}(B)`, embedded back into the ambient group. -/
@[expose] public def lemma115BOne
    {X : Type u} [Group X] (B : Subgroup X) (f : ℕ) : Subgroup X :=
  (pPrimeCore f B).map B.subtype

/-- The ambient `f'`-core remains inside `B`. -/
public theorem lemma115_BOne_le
    {X : Type u} [Group X] (B : Subgroup X) (f : ℕ) :
    lemma115BOne B f ≤ B := by
  exact Subgroup.map_subtype_le (pPrimeCore f B)

/-- The ambient copy of `O_{f'}(B)` has order prime to `f`. -/
public theorem lemma115_BOne_coprime_card
    {X : Type u} [Group X] [Finite X]
    (B : Subgroup X) {f : ℕ} (hf : f.Prime) :
    Nat.Coprime f (Nat.card (lemma115BOne B f)) := by
  letI : Fact f.Prime := ⟨hf⟩
  rw [show Nat.card (lemma115BOne B f) = Nat.card (pPrimeCore f B) by
    simpa [lemma115BOne] using
      (Subgroup.card_map_of_injective
        (K := pPrimeCore f B) B.subtype_injective)]
  exact pPrimeCore_coprime_card

/-- A subgroup normalizing `B` also normalizes its ambient `f'`-core. -/
public theorem lemma115_BOne_normalized
    {X : Type u} [Group X] [Finite X]
    {B P : Subgroup X} {f : ℕ}
    (hPnorm : P ≤ Subgroup.normalizer (B : Set X)) :
    P ≤ Subgroup.normalizer (lemma115BOne B f : Set X) := by
  letI : (pPrimeCore f B).Characteristic := pPrimeCore_characteristic
  exact hPnorm.trans
    (section8_normalizer_map_subtype_le_of_characteristic (H := B)
      (K := pPrimeCore f B))

/-- If `C_B(P)` is an `f`-group, then `P` has no nontrivial fixed point in
the ambient `f'`-core of `B`. -/
public theorem lemma115_BOne_inf_centralizer_eq_bot
    {X : Type u} [Group X] [Finite X]
    {B P : Subgroup X} {f : ℕ}
    (hf : f.Prime)
    (hH : IsPGroup f ↥(B ⊓ Subgroup.centralizer (P : Set X))) :
    lemma115BOne B f ⊓ Subgroup.centralizer (P : Set X) = ⊥ := by
  letI : Fact f.Prime := ⟨hf⟩
  let O : Subgroup X := lemma115BOne B f
  let H : Subgroup X := B ⊓ Subgroup.centralizer (P : Set X)
  let I : Subgroup X := O ⊓ Subgroup.centralizer (P : Set X)
  have hOcop : Nat.Coprime f (Nat.card O) := by
    simpa [O] using lemma115_BOne_coprime_card B hf
  have hIleH : I ≤ H := by
    intro x hx
    exact ⟨lemma115_BOne_le B f hx.1, hx.2⟩
  have hIp : IsPGroup f I := by
    let Isub : Subgroup H := I.subgroupOf H
    have hIsub : IsPGroup f Isub := hH.to_subgroup Isub
    let e : Isub ≃* I := Subgroup.subgroupOfEquivOfLe hIleH
    exact hIsub.of_equiv e
  have hIcop : Nat.Coprime f (Nat.card I) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (show I ≤ O by exact inf_le_left)) hOcop
  change I = ⊥
  apply (Subgroup.card_eq_one (H := I)).mp
  rcases hIp.exists_card_eq with ⟨n, hn⟩
  by_cases hn0 : n = 0
  · rw [hn, hn0, pow_zero]
  · have hfdvd : f ∣ Nat.card I := by
      rw [hn]
      exact dvd_pow_self f hn0
    exact False.elim ((hf.coprime_iff_not_dvd.mp hIcop) hfdvd)

/-- A cyclic group which is not an `f`-group has a nontrivial `f'`-core. -/
public theorem lemma115_pPrimeCore_ne_bot_of_cyclic_not_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime)
    (hcyc : IsCyclic G) (hnot : ¬ IsPGroup p G) :
    pPrimeCore p G ≠ ⊥ := by
  intro hcore
  apply hnot
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic G := hcyc
  letI : IsMulCommutative G := hcyc.isMulCommutative
  let pPrime : Nat.Primes := ⟨p, hp⟩
  have htop : IsPGroup p (⊤ : Subgroup G) := by
    apply isPGroup_of_isPiSubgroup_singleton (q := pPrime)
    intro q hq
    by_contra hqne
    letI : Fact q.val.Prime := ⟨q.property⟩
    let Q : Sylow q.val G := default
    have hqG : q.val ∣ Nat.card G := by simpa using hq
    have hQne : (Q : Subgroup G) ≠ ⊥ := Q.ne_bot_of_dvd_card hqG
    have hpq : Nat.Coprime p q.val :=
      (Nat.coprime_primes hp q.property).mpr (by
        intro hpq
        apply hqne
        exact Subtype.ext hpq.symm)
    have hQcop : Nat.Coprime p (Nat.card (Q : Subgroup G)) := by
      rcases Q.isPGroup'.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact hpq.pow_right n
    have hQbot : (Q : Subgroup G) = ⊥ :=
      (pPrimeCore_eq_bot_iff.mp hcore) Q inferInstance hQcop
    exact hQne hQbot
  exact htop.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)

/-- A cyclic subgroup of an abelian `B` which is not an `f`-group forces the
ambient copy of `O_{f'}(B)` to be nontrivial. -/
public theorem lemma115_BOne_ne_bot_of_cyclic_subgroup_not_isPGroup
    {X : Type u} [Group X] [Finite X]
    {B T : Subgroup X} {f : ℕ}
    (hf : f.Prime) (hBcomm : IsMulCommutative B)
    (hTB : T ≤ B) (hTcyc : IsCyclic T)
    (hTnot : ¬ IsPGroup f T) :
    lemma115BOne B f ≠ ⊥ := by
  letI : Fact f.Prime := ⟨hf⟩
  letI : IsMulCommutative B := hBcomm
  let K : Subgroup X := (pPrimeCore f T).map T.subtype
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hcorebot : pPrimeCore f T = ⊥ := by
      apply Subgroup.map_injective T.subtype_injective
      simpa [K] using hKbot
    exact lemma115_pPrimeCore_ne_bot_of_cyclic_not_isPGroup
      hf hTcyc hTnot hcorebot
  have hKleB : K ≤ B := by
    exact (Subgroup.map_subtype_le (pPrimeCore f T)).trans hTB
  have hKnormal : (K.subgroupOf B).Normal := by infer_instance
  letI : (K.subgroupOf B).Normal := hKnormal
  have hKcop : Nat.Coprime f (Nat.card K) := by
    rw [show Nat.card K = Nat.card (pPrimeCore f T) by
      simpa [K] using
        (Subgroup.card_map_of_injective
          (K := pPrimeCore f T) T.subtype_injective)]
    exact pPrimeCore_coprime_card
  have hKleCore : K ≤ lemma115BOne B f := by
    simpa [lemma115BOne] using
      lemma115_subgroupOf_le_pPrimeCore_map hKleB hKcop
  intro hBbot
  apply hKne
  apply eq_bot_iff.mpr
  intro x hx
  exact hBbot ▸ hKleCore hx

end CFSG.BenderSuzuki
