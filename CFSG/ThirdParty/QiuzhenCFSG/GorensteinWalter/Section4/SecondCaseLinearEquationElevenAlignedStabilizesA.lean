module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreFittingTI
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Section 4, equation (11): `A^g = A` for the aligned conjugate (source L848--850)

For the aligned conjugate `X = P^g ⊆ A` (with `g` chosen so that
`t^g = t`), the source proves `A^g = A` from the centralizer identity

```text
C_{F(U)}(P) = F × K0 ⊆ C_{F(U)}(P^g) = (F·K0)^g
```

Here `×` is the ambient join `F ⊔ K0`.  Formally:

* the hypothesis `hCP` is `C_{F(U)}(P) = F ⊔ K0`;
* the hypothesis `hCPg` is its conjugate `C_{F(U)}(P^g) = (F ⊔ K0)^g`;
* since `X = P^g ≤ A ≤ F ⊔ K0 = C_{F(U)}(P)` and `F ⊔ K0` is abelian, the
  centralizer `C_{F(U)}(P)` centralizes `P^g`, so
  `F ⊔ K0 ⊆ C_{F(U)}(P^g) = (F ⊔ K0)^g`;
* equal finite cardinalities force `(F ⊔ K0)^g = F ⊔ K0`, i.e. `g`
  normalizes `F ⊔ K0`;
* `A` is the unique subgroup of order `p²` of `F ⊔ K0` (the source's "the
  subgroup of type `(p,p)` in `F × K0`", hypothesis `hA_unique`), so the
  conjugate `A^g ≤ (F ⊔ K0)^g = F ⊔ K0` of the same order `p²` equals `A`.

The hypotheses `hPleCGE` (`P ≤ C_G(E)`), `hPinterE` (`P ∩ E = 1`),
`hP0leK0`, `hK0leE` (`P0 ≤ K0 ≤ E`) are the corrected geometry
`P ≤ F ≤ C_G(E)`, `P0 ≤ K0 ≤ E`, `A = P ⊔ P0`; they give `|A| = p²` and
`P ≤ C_G(P0)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- `|K ⊔ B| = |K|·|B|` when `B` normalizes `K` and `K ∩ B = 1`
(bijection `K × B ≃ K ⊔ B` via the product map). -/
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

/-- Conjugating a join conjugates both summands. -/
private lemma sup_conjugate
    {G : Type u} [Group G] {A B : Subgroup G} (g : G) :
    conjugateSubgroup (A ⊔ B) g =
      conjugateSubgroup A g ⊔ conjugateSubgroup B g := by
  change (A ⊔ B).map (MulAut.conj g).toMonoidHom =
    A.map (MulAut.conj g).toMonoidHom ⊔ B.map (MulAut.conj g).toMonoidHom
  exact Subgroup.map_sup A B (MulAut.conj g).toMonoidHom

/-- Conjugation preserves cardinality. -/
private lemma card_conjugate
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} (g : G) :
    Nat.card (conjugateSubgroup H g) = Nat.card H := by
  change Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := H)
    (MulAut.conj g).injective

/-- Conjugation is monotone. -/
private lemma conjugate_mono
    {G : Type u} [Group G] {H K : Subgroup G} (h : H ≤ K) (g : G) :
    conjugateSubgroup H g ≤ conjugateSubgroup K g := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr ⟨y, h hy, rfl⟩

/-- The rank-two subgroup `A = P ⊔ P0` has order `p²`. -/
private lemma A_card_eq_p_sq
    {G : Type u} [Group G] [Finite G]
    {P P0 A : Subgroup G} {p : ℕ}
    (hA : A = P ⊔ P0) (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G))
    (hPinterP0 : P ⊓ P0 = ⊥) :
    Nat.card A = p ^ 2 := by
  have hPleN : P ≤ Subgroup.normalizer (P0 : Set G) := by
    intro p hp
    exact (Subgroup.centralizer_le_normalizer (P0 : Set G)) (by
      exact Subgroup.mem_centralizer_iff.mpr (by
        intro p0 hp0
        exact ((Subgroup.mem_centralizer_iff.mp (hP0leCGP hp0)) p hp).symm))
  have hcard : Nat.card (↥(P0 ⊔ P)) = p * p := by
    calc
      Nat.card (↥(P0 ⊔ P)) = Nat.card (↥P0) * Nat.card (↥P) := by
        exact natCard_sup_of_disjoint P0 P hPleN (by simpa [inf_comm] using hPinterP0)
      _ = p * p := by rw [hP0card, hPcard]
  calc
    Nat.card (↥A) = Nat.card (↥(P ⊔ P0)) := by rw [hA]
    _ = Nat.card (↥(P0 ⊔ P)) := by rw [sup_comm]
    _ = p * p := hcard
    _ = p ^ 2 := by ring

/-- `A^g = A`: the aligned conjugate of the chosen order-`p` subgroup
stabilizes the rank-two subgroup `A = P ⊔ P0` (source L848--850).

The source argument is: `C_{F(U)}(P) = F × K0 ⊆ C_{F(U)}(P^g) =
(F·K0)^g` forces `(F·K0)^g = F·K0` by equal finite cardinalities, and
`A` is the unique order-`p²` subgroup of `F·K0`, so `A^g = A`.  The two
centralizer identities and the uniqueness are the explicit hypotheses
`hCP`, `hCPg`, `hA_unique`; everything else is derived.
-/
public theorem secondCase_equation11_aligned_A_conjugate_eq_A
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F K0 P P0 A X : Subgroup G) (g : G) {p : ℕ}
    (hp : p.Prime)
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hPleCGE : P ≤ Subgroup.centralizer (d.E : Set G))
    (hPinterE : P ⊓ d.E = ⊥)
    (hP0leK0 : P0 ≤ K0) (hK0leE : K0 ≤ d.E)
    (hXleA : X ≤ A)
    (hA : A = P ⊔ P0) (hPleF : P ≤ F)
    (hFK0_ab : IsMulCommutative (↥(F ⊔ K0)))
    (hCP : (Subgroup.centralizer (P : Set G)) ⊓ c.FU = F ⊔ K0)
    (hCPg : (Subgroup.centralizer (X : Set G)) ⊓ c.FU = conjugateSubgroup (F ⊔ K0) g)
    (hA_elem : IsElementaryAbelian p A)
    (hA_unique : ∀ B : Subgroup G, B ≤ F ⊔ K0 →
      IsElementaryAbelian p B → Nat.card B = p ^ 2 → B = A) :
    conjugateSubgroup A g = A := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  -- `A ≤ F ⊔ K0`, hence `X ≤ F ⊔ K0`
  have hA_le_FK0 : A ≤ F ⊔ K0 := by
    rw [hA]
    exact sup_le (le_trans hPleF le_sup_left) (le_trans hP0leK0 le_sup_right)
  have hX_le_FK0 : X ≤ F ⊔ K0 := hXleA.trans hA_le_FK0
  -- `F ⊔ K0 = C_{F(U)}(P) ⊆ C_{F(U)}(P^g)`: elements of the abelian group
  -- `F ⊔ K0` centralize `X = P^g ≤ F ⊔ K0`
  have hle : F ⊔ K0 ≤ (Subgroup.centralizer (X : Set G)) ⊓ c.FU := by
    intro y hy
    have hyCP : y ∈ (Subgroup.centralizer (P : Set G)) ⊓ c.FU := by
      rwa [hCP]
    refine ⟨?_, hyCP.2⟩
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro x hx
      have hcomm : y * x = x * y :=
        congrArg Subtype.val ((isMulCommutative_iff.mp hFK0_ab) ⟨y, hy⟩ ⟨x, hX_le_FK0 hx⟩)
      exact hcomm.symm)
  -- `F ⊔ K0 ⊆ (F ⊔ K0)^g`, and equal finite cardinalities force equality
  have hle' : F ⊔ K0 ≤ conjugateSubgroup (F ⊔ K0) g := by
    rwa [hCPg] at hle
  have hFK0g : conjugateSubgroup (F ⊔ K0) g = F ⊔ K0 := by
    have heq : F ⊔ K0 = conjugateSubgroup (F ⊔ K0) g :=
      Subgroup.eq_of_le_of_card_ge hle' (le_of_eq (card_conjugate g))
    exact heq.symm
  -- `A^g ≤ (F ⊔ K0)^g = F ⊔ K0` has order `p²`, so uniqueness gives `A^g = A`
  have hAg_le : conjugateSubgroup A g ≤ F ⊔ K0 := by
    exact (conjugate_mono hA_le_FK0 g).trans (by simp [hFK0g])
  have hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G) := by
    intro p0 hp0
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro p hp
      have hpcent : p ∈ Subgroup.centralizer (d.E : Set G) := hPleCGE hp
      exact ((Subgroup.mem_centralizer_iff.mp hpcent) p0 (hK0leE (hP0leK0 hp0))).symm)
  have hPinterP0 : P ⊓ P0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxE : x ∈ d.E := hK0leE (hP0leK0 hx.2)
    have hxPE : x ∈ P ⊓ d.E := ⟨hx.1, hxE⟩
    rwa [hPinterE] at hxPE
  have hAg_card : Nat.card (conjugateSubgroup A g) = p ^ 2 := by
    rw [card_conjugate]
    exact A_card_eq_p_sq hA hPcard hP0card hP0leCGP hPinterP0
  let : IsElementaryAbelian p A := hA_elem
  have hAg_elem : IsElementaryAbelian p (conjugateSubgroup A g) := by
    change IsElementaryAbelian p
      (A.map (MulAut.conj g).toMonoidHom)
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  exact hA_unique (conjugateSubgroup A g) hAg_le hAg_elem hAg_card

end CFSG.GorensteinWalter
