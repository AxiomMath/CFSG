module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Section 4, equation (11): the join identities (source L850--853)

For the aligned conjugate `X = P^g ⊆ A` (with `A^g = A`), the source
derives

```text
P × K = X × K    and    X × K^g = P × K^g
```

(the ambient joins `P ⊔ K = X ⊔ K` and `X ⊔ K^g = P ⊔ K^g`), and states
`P` is not conjugate to `A ∩ K`.  Formally:

* `A ∩ K = P0`: since `A = P·P0` (setwise, `P0 ≤ C_G(P)`), `P ∩ K = 1`,
  and `P0 ≤ K0 ≤ K`, every element of `A ∩ K` has its `P`-part in
  `P ∩ K = 1`, hence lies in `P0`;
* `P` is not conjugate to `A ∩ K`: this is the source's "Being centralized
  by `S`, `P` is not conjugate to `A ∩ K`" (hypothesis
  `hP_notConjP0`, i.e. `P` is not conjugate to `P0`);
* `X ∩ K = 1`: `X ∩ K ≤ A ∩ K = P0`, and `X ≠ P0` with `|X| = p` prime
  force the intersection to be trivial; the same holds for the conjugate
  `P^{g⁻¹}` (using `A^{g⁻¹} = A`);
* `X ≤ C_G(K)` and `P ≤ C_G(K)`: `X ≤ A = P·P0` with `P ≤ C_G(E)`
  (`K ≤ E`) and `P0 ≤ K` (cyclic `K`), so both lie in the centralizer of
  `K`, which makes the joins setwise products with the exact cardinalities
  `|X ⊔ K| = p·|K| = |P ⊔ K|`, hence `P ⊔ K = X ⊔ K`;
* the second identity follows symmetrically, with the conjugate data
  `K^g`, `P^{g⁻¹} ≤ A`, and `X = P^g` transported from
  `P ≤ P^{g⁻1} ⊔ K`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- `|K ⊔ B| = |K|·|B|` when `B` normalizes `K` and `K ∩ B = 1`. -/
private lemma natCard_sup_of_disjoint {G : Type u} [Group G] [Finite G]
    (K B : Subgroup G)
    (hBleN : B ≤ Subgroup.normalizer (K : Set G))
    (hKB : K ⊓ B = ⊥) :
    Nat.card (↥(K ⊔ B)) = Nat.card (↥K) * Nat.card (↥B) := by
  classical
  let f : ↥K × ↥B → ↥(K ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), by
      have hcoe : (↑(K ⊔ B) : Set G) = (K : Set G) * (B : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left K B hBleN
      change (p.1 : G) * (p.2 : G) ∈ (↑(K ⊔ B) : Set G)
      rw [hcoe]
      exact ⟨(p.1 : G), p.1.2, (p.2 : G), p.2.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro p q h
    have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val h
    have hK : (q.1 : G)⁻¹ * (p.1 : G) ∈ K := K.mul_mem (K.inv_mem q.1.2) p.1.2
    have hB : (q.2 : G) * (p.2 : G)⁻¹ ∈ B := B.mul_mem q.2.2 (B.inv_mem p.2.2)
    have hEq : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G)
            = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hval]
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hbot : (q.1 : G)⁻¹ * (p.1 : G) = 1 := by
      have hmem : (q.1 : G)⁻¹ * (p.1 : G) ∈ K ⊓ B := ⟨hK, by rwa [hEq]⟩
      rw [hKB] at hmem
      exact Subgroup.mem_bot.mp hmem
    apply Prod.ext
    · apply Subtype.ext
      calc
        (p.1 : G) = (q.1 : G) * ((q.1 : G)⁻¹ * (p.1 : G)) := by group
        _ = (q.1 : G) := by rw [hbot]; simp
    · apply Subtype.ext
      calc
        (p.2 : G) = ((q.2 : G) * (p.2 : G)⁻¹)⁻¹ * (q.2 : G) := by group
        _ = ((q.1 : G)⁻¹ * (p.1 : G))⁻¹ * (q.2 : G) := by rw [hEq]
        _ = (q.2 : G) := by rw [hbot]; simp
  have hsurj : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (K : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K B hBleN]
      exact x.2
    rcases hx with ⟨a, haK, b, hbB, hxab⟩
    refine ⟨(⟨a, haK⟩, ⟨b, hbB⟩), ?_⟩
    apply Subtype.ext
    exact hxab
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  have hc : Nat.card (↥K × ↥B) = Nat.card (↥(K ⊔ B)) :=
    Nat.card_congr (Equiv.ofBijective f hbij)
  calc
    Nat.card (↥(K ⊔ B)) = Nat.card (↥K × ↥B) := hc.symm
    _ = Nat.card (↥K) * Nat.card (↥B) := by simp

/-- Conjugation preserves cardinality. -/
private lemma card_conjugate
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} (g : G) :
    Nat.card (conjugateSubgroup H g) = Nat.card H := by
  change Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := H)
    (MulAut.conj g).injective

/-- Conjugating a join conjugates both summands. -/
private lemma sup_conjugate
    {G : Type u} [Group G] {A B : Subgroup G} (g : G) :
    conjugateSubgroup (A ⊔ B) g =
      conjugateSubgroup A g ⊔ conjugateSubgroup B g := by
  change (A ⊔ B).map (MulAut.conj g).toMonoidHom =
    A.map (MulAut.conj g).toMonoidHom ⊔ B.map (MulAut.conj g).toMonoidHom
  exact Subgroup.map_sup A B (MulAut.conj g).toMonoidHom

/-- `H^1 = H`. -/
private lemma conjugate_one {G : Type u} [Group G] {H : Subgroup G} :
    conjugateSubgroup H (1 : G) = H := by
  change H.map (MulAut.conj (1 : G)).toMonoidHom = H
  have hcid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hcid, Subgroup.map_id]

/-- `(H^a)^b = H^(b·a)`. -/
private lemma conjugate_conjugate
    {G : Type u} [Group G] {H : Subgroup G} (a b : G) :
    conjugateSubgroup (conjugateSubgroup H a) b = conjugateSubgroup H (b * a) := by
  change (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
    H.map (MulAut.conj (b * a)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Conjugation is monotone. -/
private lemma conjugate_mono
    {G : Type u} [Group G] {H K : Subgroup G} (h : H ≤ K) (g : G) :
    conjugateSubgroup H g ≤ conjugateSubgroup K g := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr ⟨y, h hy, rfl⟩

/-- `A ∩ K = P0`: the intersection of the rank-two subgroup with the
inverted subgroup is the `P0`-part. -/
private lemma A_inter_K_eq_P0
    {G : Type u} [Group G]
    {K K0 P P0 A : Subgroup G}
    (hA : A = P ⊔ P0) (hP0leK0 : P0 ≤ K0) (hK0leK : K0 ≤ K)
    (hPinterK : P ⊓ K = ⊥)
    (hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G)) :
    A ⊓ K = P0 := by
  apply le_antisymm
  · intro a ha
    have hP0leN : P0 ≤ Subgroup.normalizer (P : Set G) := by
      intro p0 hp0
      exact (Subgroup.centralizer_le_normalizer (P : Set G)) (hP0leCGP hp0)
    have hcoe : ((P ⊔ P0 : Subgroup G) : Set G) = (P : Set G) * (P0 : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left P P0 hP0leN
    have haPP0 : a ∈ (P : Set G) * (P0 : Set G) := by
      have haA' : a ∈ P ⊔ P0 := by simpa [hA] using ha.1
      rwa [← hcoe]
    rcases haPP0 with ⟨p, hp, p0, hp0, hEq⟩
    have hpK : p ∈ K := by
      have hmem : a * p0⁻¹ ∈ K := K.mul_mem ha.2 (K.inv_mem (hK0leK (hP0leK0 hp0)))
      have hEq' : p = a * p0⁻¹ := by
        rw [← hEq]
        group
      rwa [hEq']
    have hpbot : p = 1 := by
      have hmem : p ∈ P ⊓ K := ⟨hp, hpK⟩
      have hbot : p ∈ (⊥ : Subgroup G) := by rwa [hPinterK] at hmem
      exact Subgroup.mem_bot.mp hbot
    have ha_eq : a = p0 := by
      calc
        a = p * p0 := hEq.symm
        _ = p0 := by rw [hpbot]; simp
    rwa [ha_eq]
  · intro p0 hp0
    exact ⟨by
      rw [hA]
      exact (le_sup_right : P0 ≤ P ⊔ P0) hp0, hK0leK (hP0leK0 hp0)⟩

/-- `Y ∩ K = 1` for an order-`p` subgroup `Y ≤ A` with `Y ≠ P0`. -/
private lemma inter_K_eq_bot_of_le_A_of_ne_P0
    {G : Type u} [Group G] [Finite G]
    {K P0 A Y : Subgroup G} {p : ℕ}
    (hA_inter_K : A ⊓ K = P0) (hYleA : Y ≤ A) (hYneP0 : Y ≠ P0)
    (hYcard : Nat.card Y = p) (hP0card : Nat.card P0 = p) (hp : p.Prime) :
    Y ⊓ K = ⊥ := by
  apply le_bot_iff.mp
  intro y hy
  have hyP0 : y ∈ P0 := by
    have hyAK : y ∈ A ⊓ K := ⟨hYleA hy.1, hy.2⟩
    rwa [hA_inter_K] at hyAK
  have hYinterP0 : Y ⊓ P0 = ⊥ := by
    have hYne : Y ≠ ⊥ := by
      intro hbot
      have hc : Nat.card Y = 1 := by rw [hbot]; simp
      have hp2 : 2 ≤ p := hp.two_le
      omega
    apply le_bot_iff.mp
    intro y hyYP0
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.mem_bot.mpr rfl
    · exfalso
      have hdiv : Nat.card (↥(Y ⊓ P0)) ∣ p := by
        simpa [hYcard] using (Subgroup.card_dvd_of_le (inf_le_left : Y ⊓ P0 ≤ Y))
      have hne1 : Nat.card (↥(Y ⊓ P0)) ≠ 1 := by
        intro h1
        have hbot : Y ⊓ P0 = ⊥ := (Subgroup.eq_bot_iff_card (H := Y ⊓ P0)).mpr h1
        have hmem : y ∈ Y ⊓ P0 := ⟨hyYP0.1, hyYP0.2⟩
        have hmem' : y ∈ (⊥ : Subgroup G) := by rwa [hbot] at hmem
        exact hy1 (Subgroup.mem_bot.mp hmem')
      rcases (Nat.dvd_prime hp).mp hdiv with h1 | hp'
      · exact hne1 h1
      · have hEq : Y ⊓ P0 = Y := by
          apply Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq _)
          rw [hYcard]
          exact hp'.symm
        have hYleP0 : Y ≤ P0 := by
          intro y hy
          have hy' : y ∈ Y ⊓ P0 := by rwa [← hEq] at hy
          exact hy'.2
        have hYeq : Y = P0 := by
          apply Subgroup.eq_of_le_of_card_ge hYleP0 (le_of_eq _)
          rw [hYcard]
          exact hP0card
        exact hYneP0 hYeq
  have hyYP0 : y ∈ Y ⊓ P0 := ⟨hy.1, hyP0⟩
  have hbot : y ∈ (⊥ : Subgroup G) := by rwa [hYinterP0] at hyYP0
  exact Subgroup.mem_bot.mp hbot

/-- A conjugate of a subgroup centralizing `K` centralizes the conjugate of
`K`. -/
private lemma centralizer_conjugate_le_of_le
    {G : Type u} [Group G] {H K : Subgroup G} (g : G)
    (h : H ≤ Subgroup.centralizer (K : Set G)) :
    conjugateSubgroup H g ≤
      Subgroup.centralizer ((conjugateSubgroup K g) : Set G) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
  exact Subgroup.mem_centralizer_iff.mpr (by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨v, hv, hvy⟩
    have huv : u * v = v * u := ((Subgroup.mem_centralizer_iff.mp (h hu)) v hv).symm
    have hxy : (g * u * g⁻¹) * (g * v * g⁻¹) = (g * v * g⁻¹) * (g * u * g⁻¹) := by
      calc
        (g * u * g⁻¹) * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
        _ = g * (v * u) * g⁻¹ := by rw [huv]
        _ = (g * v * g⁻¹) * (g * u * g⁻¹) := by group
    rw [← hvy]
    simpa [MulAut.conj_apply] using hxy.symm)

/-- The join identities for the aligned conjugate: `P ⊔ K = X ⊔ K` and
`X ⊔ K^g = P ⊔ K^g`, together with `A ∩ K = P0` and the source's
"`P` is not conjugate to `A ∩ K`" (source L850--853).

The hypotheses are the corrected geometry (`P ≤ F ≤ C_G(E)`,
`P0 ≤ K0 ≤ E`, `A = P ⊔ P0`), the equations-(1)--(3) inverted-subgroup
data (`K0 ≤ K`, `K` cyclic, `P ∩ K = 1`), the aligned-conjugate data
(`X = P^g ≤ A`, `A^g = A`), and `hP_notConjP0` — the source's
"Being centralized by `S`, `P` is not conjugate to `A ∩ K`".
-/
public theorem secondCase_equation11_aligned_join_identities
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K K0 P P0 A X : Subgroup G) (g : G) {p : ℕ}
    (hp : p.Prime)
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hPleCGE : P ≤ Subgroup.centralizer (d.E : Set G))
    (hP0leK0 : P0 ≤ K0) (hK0leK : K0 ≤ K) (hKleE : K ≤ d.E)
    (hKcyc : IsCyclic K)
    (hPinterK : P ⊓ K = ⊥)
    (hX : X = conjugateSubgroup P g) (hXleA : X ≤ A)
    (hA : A = P ⊔ P0)
    (hAg : conjugateSubgroup A g = A)
    (hP_notConjP0 : ¬ ∃ h : G, conjugateSubgroup P h = P0) :
    (A ⊓ K = P0 ∧ ¬ ∃ h : G, conjugateSubgroup P h = A ⊓ K) ∧
      P ⊔ K = X ⊔ K ∧
      X ⊔ conjugateSubgroup K g = P ⊔ conjugateSubgroup K g := by
  classical
  -- `P0 ≤ C_G(P)` (via `P0 ≤ K0 ≤ E` and `P ≤ C_G(E)`), so `A = P·P0`
  have hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G) := by
    intro p0 hp0
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro p hp
      have hpcent : p ∈ Subgroup.centralizer (d.E : Set G) := hPleCGE hp
      exact ((Subgroup.mem_centralizer_iff.mp hpcent)
        p0 (hKleE (hK0leK (hP0leK0 hp0)))).symm)
  have hA_inter_K : A ⊓ K = P0 :=
    A_inter_K_eq_P0 hA hP0leK0 hK0leK hPinterK hP0leCGP
  have hP_notConj_AK : ¬ ∃ h : G, conjugateSubgroup P h = A ⊓ K := by
    intro h
    apply hP_notConjP0
    rcases h with ⟨u, hu⟩
    exact ⟨u, by rwa [hA_inter_K] at hu⟩
  have hXneP0 : X ≠ P0 := by
    intro h
    apply hP_notConjP0
    rw [hX] at h
    exact ⟨g, h⟩
  -- `K` is abelian, and `A ≤ C_G(K)` (via `P ≤ C_G(E)`, `P0 ≤ K`)
  haveI : CommGroup K := hKcyc.commGroup
  have hKleCK : K ≤ Subgroup.centralizer (K : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro k' hk'
      letI : IsCyclic K := hKcyc
      letI : CommGroup K := IsCyclic.commGroup
      have hcomm : (⟨k, hk⟩ : K) * ⟨k', hk'⟩ = ⟨k', hk'⟩ * ⟨k, hk⟩ := mul_comm _ _
      exact (congrArg (fun z : K => (z : G)) hcomm).symm)
  have hAleCK : A ≤ Subgroup.centralizer (K : Set G) := by
    rw [hA]
    refine sup_le ?_ ?_
    · intro p hp
      exact Subgroup.mem_centralizer_iff.mpr (by
        intro k hk
        have hpcent : p ∈ Subgroup.centralizer (d.E : Set G) := hPleCGE hp
        exact (Subgroup.mem_centralizer_iff.mp hpcent k (hKleE hk)))
    · intro p0 hp0
      exact Subgroup.mem_centralizer_iff.mpr (by
        intro k hk
        exact ((Subgroup.mem_centralizer_iff.mp (hKleCK hk))
          p0 (hK0leK (hP0leK0 hp0))).symm)
  have hPleA : P ≤ A := by
    rw [hA]
    exact le_sup_left
  have hXleCK : X ≤ Subgroup.centralizer (K : Set G) := hXleA.trans hAleCK
  have hPleCK : P ≤ Subgroup.centralizer (K : Set G) := hPleA.trans hAleCK
  -- `X ∩ K = 1` and `|X| = p`
  have hXcard : Nat.card X = p := by
    rw [hX, card_conjugate, hPcard]
  have hXinterK : X ⊓ K = ⊥ :=
    inter_K_eq_bot_of_le_A_of_ne_P0 hA_inter_K hXleA hXneP0 hXcard hP0card hp
  -- `A^{g⁻¹} = A`, `P^{g⁻¹} ≤ A`, `|P^{g⁻¹}| = p`
  have hAg' : conjugateSubgroup A g⁻¹ = A := by
    have h1 : conjugateSubgroup (conjugateSubgroup A g) g⁻¹ = A := by
      calc
        conjugateSubgroup (conjugateSubgroup A g) g⁻¹ =
            conjugateSubgroup A (g⁻¹ * g) := conjugate_conjugate (H := A) g g⁻¹
        _ = A := by simp [conjugate_one]
    rwa [hAg] at h1
  have hPg1leA : conjugateSubgroup P g⁻¹ ≤ A := by
    calc
      conjugateSubgroup P g⁻¹ ≤ conjugateSubgroup A g⁻¹ := conjugate_mono hPleA g⁻¹
      _ = A := hAg'
  have hPg1neP0 : conjugateSubgroup P g⁻¹ ≠ P0 := by
    intro h
    apply hP_notConjP0
    exact ⟨g⁻¹, h⟩
  have hPg1card : Nat.card (conjugateSubgroup P g⁻¹) = p := by
    rw [card_conjugate, hPcard]
  have hPg1interK : conjugateSubgroup P g⁻¹ ⊓ K = ⊥ :=
    inter_K_eq_bot_of_le_A_of_ne_P0 hA_inter_K hPg1leA hPg1neP0 hPg1card hP0card hp
  -- `|X ⊔ K| = p·|K| = |P ⊔ K|`, and `X ⊔ K ≤ P ⊔ K`
  have hXleNK : X ≤ Subgroup.normalizer (K : Set G) :=
    hXleCK.trans (Subgroup.centralizer_le_normalizer (K : Set G))
  have hPleNK : P ≤ Subgroup.normalizer (K : Set G) :=
    hPleCK.trans (Subgroup.centralizer_le_normalizer (K : Set G))
  have hcardXK : Nat.card (↥(X ⊔ K)) = p * Nat.card (↥K) := by
    calc
      Nat.card (↥(X ⊔ K)) = Nat.card (↥X) * Nat.card (↥K) := by
        rw [sup_comm, mul_comm]
        exact natCard_sup_of_disjoint K X hXleNK (by simpa [inf_comm] using hXinterK)
      _ = p * Nat.card (↥K) := by rw [hXcard]
  have hcardPK : Nat.card (↥(P ⊔ K)) = p * Nat.card (↥K) := by
    calc
      Nat.card (↥(P ⊔ K)) = Nat.card (↥P) * Nat.card (↥K) := by
        rw [sup_comm, mul_comm]
        exact natCard_sup_of_disjoint K P hPleNK (by simpa [inf_comm] using hPinterK)
      _ = p * Nat.card (↥K) := by rw [hPcard]
  have hXK_le_PK : X ⊔ K ≤ P ⊔ K := by
    exact sup_le
      (by exact hXleA.trans (by
        rw [hA]
        exact sup_le le_sup_left (le_trans (le_trans hP0leK0 hK0leK) le_sup_right)))
      le_sup_right
  have hjoin1 : P ⊔ K = X ⊔ K := by
    have hEq : X ⊔ K = P ⊔ K :=
      Subgroup.eq_of_le_of_card_ge hXK_le_PK (by
        rw [hcardPK]
        exact le_of_eq hcardXK.symm)
    exact hEq.symm
  -- the second identity: `X = P^g ≤ P ⊔ K^g` from `P ≤ P^{g⁻¹} ⊔ K`
  have hPg1leCK : conjugateSubgroup P g⁻¹ ≤ Subgroup.centralizer (K : Set G) :=
    hPg1leA.trans hAleCK
  have hPg1leNK : conjugateSubgroup P g⁻¹ ≤ Subgroup.normalizer (K : Set G) :=
    hPg1leCK.trans (Subgroup.centralizer_le_normalizer (K : Set G))
  have hcardPg1K : Nat.card (↥(conjugateSubgroup P g⁻¹ ⊔ K)) = p * Nat.card (↥K) := by
    calc
      Nat.card (↥(conjugateSubgroup P g⁻¹ ⊔ K)) =
          Nat.card (↥(conjugateSubgroup P g⁻¹)) * Nat.card (↥K) := by
            rw [sup_comm, mul_comm]
            exact natCard_sup_of_disjoint K (conjugateSubgroup P g⁻¹) hPg1leNK
              (by simpa [inf_comm] using hPg1interK)
      _ = p * Nat.card (↥K) := by rw [hPg1card]
  have hPg1K_le_PK : conjugateSubgroup P g⁻¹ ⊔ K ≤ P ⊔ K := by
    exact sup_le
      (by exact hPg1leA.trans (by
        rw [hA]
        exact sup_le le_sup_left (le_trans (le_trans hP0leK0 hK0leK) le_sup_right)))
      le_sup_right
  have hPg1K_eq_PK : conjugateSubgroup P g⁻¹ ⊔ K = P ⊔ K := by
    apply Subgroup.eq_of_le_of_card_ge hPg1K_le_PK (le_of_eq _)
    rw [hcardPK]
    exact hcardPg1K.symm
  have hP_le_Pg1K : P ≤ conjugateSubgroup P g⁻¹ ⊔ K := by
    rw [hPg1K_eq_PK]
    exact le_sup_left
  have hX_le_PKg : X ≤ P ⊔ conjugateSubgroup K g := by
    -- `X = P^g ≤ (P^{g⁻¹} ⊔ K)^g = P ⊔ K^g`
    have h1 : conjugateSubgroup P g ≤
        conjugateSubgroup (conjugateSubgroup P g⁻¹ ⊔ K) g := by
      exact conjugate_mono hP_le_Pg1K g
    have h2 : conjugateSubgroup (conjugateSubgroup P g⁻¹ ⊔ K) g =
        P ⊔ conjugateSubgroup K g := by
      calc
        conjugateSubgroup (conjugateSubgroup P g⁻¹ ⊔ K) g =
            conjugateSubgroup (conjugateSubgroup P g⁻¹) g ⊔ conjugateSubgroup K g := by
              rw [sup_conjugate]
        _ = P ⊔ conjugateSubgroup K g := by
          have hPg : conjugateSubgroup (conjugateSubgroup P g⁻¹) g = P := by
            calc
              conjugateSubgroup (conjugateSubgroup P g⁻¹) g = conjugateSubgroup P (g * g⁻¹) :=
                conjugate_conjugate (H := P) g⁻¹ g
              _ = P := by simp [conjugate_one]
          rw [hPg]
    rw [hX]
    exact h1.trans (le_of_eq h2)
  -- `X ∩ K^g = 1`, `P ∩ K^g = 1`
  have hXinterKg : X ⊓ conjugateSubgroup K g = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxX : x ∈ conjugateSubgroup P g := by simpa [hX] using hx.1
    rcases Subgroup.mem_map.mp hxX with ⟨p, hp, hxp⟩
    rcases Subgroup.mem_map.mp hx.2 with ⟨k, hk, hxk⟩
    have hpk : p = k := by
      apply (MulAut.conj g).injective
      calc
        (MulAut.conj g) p = x := by simpa using hxp
        _ = (MulAut.conj g) k := by simpa [MulAut.conj_apply] using hxk.symm
    have hpK : p ∈ K := by rwa [hpk]
    have hmem : p ∈ P ⊓ K := ⟨hp, hpK⟩
    have hbot : p ∈ (⊥ : Subgroup G) := by rwa [hPinterK] at hmem
    have hp1 : p = 1 := Subgroup.mem_bot.mp hbot
    exact Subgroup.mem_bot.mpr (by
      calc
        x = (MulAut.conj g) p := by simpa [MulAut.conj_apply] using hxp.symm
        _ = (MulAut.conj g) 1 := by rw [hp1]
        _ = 1 := by simp)
  have hPinterKg : P ⊓ conjugateSubgroup K g = ⊥ := by
    apply le_bot_iff.mp
    intro p hp
    rcases Subgroup.mem_map.mp hp.2 with ⟨k, hk, hpk⟩
    -- p = g·k·g⁻¹ ⟹ g⁻¹·p·g = k ∈ K ∩ P^{g⁻1}
    have hgp : g⁻¹ * p * g ∈ conjugateSubgroup P g⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨p, hp.1, by simp⟩
    have hpk' : p = g * k * g⁻¹ := by simpa [MulAut.conj_apply] using hpk.symm
    have hgpk : g⁻¹ * p * g = k := by
      calc
        g⁻¹ * p * g = g⁻¹ * (g * k * g⁻¹) * g := by rw [hpk']
        _ = k := by group
    have hkinter : k ∈ conjugateSubgroup P g⁻¹ ⊓ K := ⟨by rwa [hgpk] at hgp, hk⟩
    have hbot : k ∈ (⊥ : Subgroup G) := by rwa [hPg1interK] at hkinter
    have hk1 : k = 1 := Subgroup.mem_bot.mp hbot
    exact Subgroup.mem_bot.mpr (by
      calc
        p = g * k * g⁻¹ := hpk'
        _ = 1 := by rw [hk1]; simp)
  -- `|X ⊔ K^g| = p·|K| = |P ⊔ K^g|`
  have hXleCKg : X ≤ Subgroup.centralizer ((conjugateSubgroup K g) : Set G) := by
    rw [hX]
    exact centralizer_conjugate_le_of_le g hPleCK
  have hPleCKg : P ≤ Subgroup.centralizer ((conjugateSubgroup K g) : Set G) := by
    intro p hp
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨k, hk, hky⟩
      have hgp : g⁻¹ * p * g ∈ Subgroup.centralizer (K : Set G) :=
        hPg1leCK (Subgroup.mem_map.mpr ⟨p, hp, by simp⟩)
      have hcomm : (g⁻¹ * p * g) * k = k * (g⁻¹ * p * g) :=
        ((Subgroup.mem_centralizer_iff.mp hgp) k hk).symm
      have hpy : p * (g * k * g⁻¹) = (g * k * g⁻¹) * p := by
        calc
          p * (g * k * g⁻¹) = g * ((g⁻¹ * p * g) * k) * g⁻¹ := by group
          _ = g * (k * (g⁻¹ * p * g)) * g⁻¹ := by rw [hcomm]
          _ = (g * k * g⁻¹) * p := by group
      rw [← hky]
      simpa [MulAut.conj_apply] using hpy.symm)
  have hXleNKg : X ≤ Subgroup.normalizer ((conjugateSubgroup K g) : Set G) :=
    hXleCKg.trans (Subgroup.centralizer_le_normalizer (conjugateSubgroup K g : Set G))
  have hPleNKg : P ≤ Subgroup.normalizer ((conjugateSubgroup K g) : Set G) :=
    hPleCKg.trans (Subgroup.centralizer_le_normalizer (conjugateSubgroup K g : Set G))
  have hcardXKg : Nat.card (↥(X ⊔ conjugateSubgroup K g)) =
      p * Nat.card (↥K) := by
    calc
      Nat.card (↥(X ⊔ conjugateSubgroup K g)) =
          Nat.card (↥X) * Nat.card (↥(conjugateSubgroup K g)) := by
            rw [sup_comm, mul_comm]
            exact natCard_sup_of_disjoint (conjugateSubgroup K g) X hXleNKg
              (by simpa [inf_comm] using hXinterKg)
      _ = p * Nat.card (↥K) := by rw [hXcard, card_conjugate]
  have hcardPKg : Nat.card (↥(P ⊔ conjugateSubgroup K g)) =
      p * Nat.card (↥K) := by
    calc
      Nat.card (↥(P ⊔ conjugateSubgroup K g)) =
          Nat.card (↥P) * Nat.card (↥(conjugateSubgroup K g)) := by
            rw [sup_comm, mul_comm]
            exact natCard_sup_of_disjoint (conjugateSubgroup K g) P hPleNKg
              (by simpa [inf_comm] using hPinterKg)
      _ = p * Nat.card (↥K) := by rw [hPcard, card_conjugate]
  have hXKg_le_PKg : X ⊔ conjugateSubgroup K g ≤ P ⊔ conjugateSubgroup K g := by
    exact sup_le hX_le_PKg le_sup_right
  have hjoin2 : X ⊔ conjugateSubgroup K g = P ⊔ conjugateSubgroup K g := by
    apply Subgroup.eq_of_le_of_card_ge hXKg_le_PKg (le_of_eq _)
    rw [hcardPKg]
    exact hcardXKg.symm
  exact ⟨⟨hA_inter_K, hP_notConj_AK⟩, hjoin1, hjoin2⟩

end CFSG.GorensteinWalter
