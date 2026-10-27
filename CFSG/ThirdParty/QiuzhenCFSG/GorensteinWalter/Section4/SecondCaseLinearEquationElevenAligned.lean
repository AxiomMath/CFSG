module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Section 4, equation (11): the aligned normalizer/intersection identities (source L844--857)

For a conjugate `X = P^g ⊆ A` of the chosen order-`p` subgroup `P` with
`N_G(P) = M`, `X ≠ P`, and the representative `g` chosen so that
`t^g = t`, the source derives the exact normalizer/intersection chains

```text
M^g ∩ P×E = N_{P×E}(X) = P·K·S0 = C_{P×E}(A)
M ∩ X×E^g = X·K^g·S0 = C_{X×E^g}(A)
```

(ambient joins: `M^g ∩ (P ⊔ E) = N_{P⊔E}(X) = P ⊔ K ⊔ S0 =
C_{P⊔E}(A)` and `M ∩ (X ⊔ E^g) = X ⊔ K^g ⊔ S0 = C_{X⊔E^g}(A)`).

The proof uses the corrected geometry `P ≤ F ≤ C_G(E)`, `P0 ≤ K0 ≤ E`,
`A = P ⊔ P0`, `N_G(P) = M`; the equations-(1)--(3) inverted-subgroup data
(`K0 ≤ K ≤ E`, `K` cyclic, `K0 ≤ F(U)`, `F ≤ F(U)`); the equation-(9)
facts (`S0 = O_2(H)`, `S0 ≤ E`, `[S0, U] = 1`); the aligned-conjugate
facts (`X = P^g ≤ A`, `A^g = A`, `g ∈ C_G(t)`, and `hP_notConjP0` —
"being centralized by `S`, `P` is not conjugate to `A ∩ K`"); and the
PSL₂ torus-centralizer identity `C_E(P0) = K ⊔ S0` (`hCP0E`).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The normalizer of a conjugate is the conjugate of the normalizer. -/
private lemma normalizer_conjugate_eq
    {G : Type u} [Group G] {P : Subgroup G} (g : G) :
    Subgroup.normalizer ((conjugateSubgroup P g) : Set G) =
      conjugateSubgroup (Subgroup.normalizer (P : Set G)) g := by
  change Subgroup.normalizer ((P.map (MulAut.conj g).toMonoidHom) : Set G) =
    (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom
  exact (Subgroup.map_normalizer_eq_of_bijective P (MulAut.conj g).bijective).symm

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

/-- Conjugation is monotone. -/
private lemma conjugate_mono
    {G : Type u} [Group G] {H K : Subgroup G} (h : H ≤ K) (g : G) :
    conjugateSubgroup H g ≤ conjugateSubgroup K g := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr ⟨y, h hy, rfl⟩

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

/-- `t^g = t` means `g ∈ H = C_G(t)`. -/
private lemma g_mem_H_of_fixes_t
    {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) {g : G}
    (hgt : g * c.t * g⁻¹ = c.t) : g ∈ c.H := by
  rw [c.H_eq_centralizer]
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.mp hgt

/-- The two-core `O₂(H)` is invariant under conjugation by elements of
`H`: it is characteristic in `H`, and conjugation by `h ∈ H` is an inner
automorphism of `H`. -/
private lemma conjugate_twoCoreOf_of_mem
    {G : Type u} [Group G] {H : Subgroup G} (h : G) (hh : h ∈ H) :
    conjugateSubgroup (twoCoreOf H) h = twoCoreOf H := by
  classical
  let K : Subgroup H := pCore 2 H
  let φ : H →* H := (MulAut.conj (⟨h, hh⟩ : H)).toMonoidHom
  have hKφ : K.map φ = K := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
      simpa [φ] using (pCore_normal.conj_mem (G := H) k hk (⟨h, hh⟩ : H))
    · intro k hk
      have hk' : (⟨h, hh⟩ : H)⁻¹ * k * ⟨h, hh⟩ ∈ K := by
        simpa using (pCore_normal.conj_mem (G := H)) k hk (⟨h, hh⟩ : H)⁻¹
      exact Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : H)⁻¹ * k * ⟨h, hh⟩, hk', by
        simp [φ, MulAut.conj_apply, mul_assoc]⟩
  have hcomp : (MulAut.conj h).toMonoidHom.comp H.subtype = H.subtype.comp φ := by
    ext x
    simp [φ, MulAut.conj_apply]
  calc
    conjugateSubgroup (twoCoreOf H) h = (K.map H.subtype).map (MulAut.conj h).toMonoidHom := by
      rfl
    _ = K.map ((MulAut.conj h).toMonoidHom.comp H.subtype) := by rw [Subgroup.map_map]
    _ = K.map (H.subtype.comp φ) := by rw [hcomp]
    _ = (K.map φ).map H.subtype := by rw [Subgroup.map_map]
    _ = K.map H.subtype := by rw [hKφ]
    _ = twoCoreOf H := rfl

/-- `A ∩ E = P0`: the rank-two subgroup meets the component in its
`P0`-part. -/
private lemma A_inter_E_eq_P0
    {G : Type u} [Group G]
    {P P0 A : Subgroup G} (E : Subgroup G)
    (hA : A = P ⊔ P0) (hP0leE : P0 ≤ E) (hPinterE : P ⊓ E = ⊥)
    (hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G)) :
    A ⊓ E = P0 := by
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
    have hpE : p ∈ E := by
      have hmem : a * p0⁻¹ ∈ E := E.mul_mem ha.2 (E.inv_mem (hP0leE hp0))
      have hEq' : p = a * p0⁻¹ := by
        rw [← hEq]
        group
      rwa [hEq']
    have hpbot : p = 1 := by
      have hmem : p ∈ P ⊓ E := ⟨hp, hpE⟩
      have hbot : p ∈ (⊥ : Subgroup G) := by rwa [hPinterE] at hmem
      exact Subgroup.mem_bot.mp hbot
    have ha_eq : a = p0 := by
      calc
        a = p * p0 := hEq.symm
        _ = p0 := by rw [hpbot]; simp
    rwa [ha_eq]
  · intro p0 hp0
    exact ⟨by
      rw [hA]
      exact (le_sup_right : P0 ≤ P ⊔ P0) hp0, hP0leE hp0⟩

/-- `Y ∩ Z = 1` for an order-`p` subgroup `Y ≤ A` with `Y ≠ P0`, where
`A ∩ Z = P0`. -/
private lemma inter_eq_bot_of_le_A_of_ne_P0
    {G : Type u} [Group G] [Finite G]
    {Z P0 A Y : Subgroup G} {p : ℕ}
    (hA_inter_Z : A ⊓ Z = P0) (hYleA : Y ≤ A) (hYneP0 : Y ≠ P0)
    (hYcard : Nat.card Y = p) (hP0card : Nat.card P0 = p) (hp : p.Prime) :
    Y ⊓ Z = ⊥ := by
  apply le_bot_iff.mp
  intro y hy
  have hyP0 : y ∈ P0 := by
    have hyAZ : y ∈ A ⊓ Z := ⟨hYleA hy.1, hy.2⟩
    rwa [hA_inter_Z] at hyAZ
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

/-- Two order-`p` subgroups are disjoint unless equal. -/
private lemma inter_eq_bot_of_card_eq_prime_of_ne
    {G : Type u} [Group G] [Finite G]
    {Y Z : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hYcard : Nat.card Y = p) (hZcard : Nat.card Z = p) (hne : Y ≠ Z) :
    Y ⊓ Z = ⊥ := by
  apply le_bot_iff.mp
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.mem_bot.mpr rfl
  · exfalso
    have hdiv : Nat.card (↥(Y ⊓ Z)) ∣ p := by
      simpa [hYcard] using (Subgroup.card_dvd_of_le (inf_le_left : Y ⊓ Z ≤ Y))
    have hne1 : Nat.card (↥(Y ⊓ Z)) ≠ 1 := by
      intro h1
      have hbot : Y ⊓ Z = ⊥ := (Subgroup.eq_bot_iff_card (H := Y ⊓ Z)).mpr h1
      have hmem' : y ∈ (⊥ : Subgroup G) := by rwa [hbot] at hy
      exact hy1 (Subgroup.mem_bot.mp hmem')
    rcases (Nat.dvd_prime hp).mp hdiv with h1 | hp'
    · exact hne1 h1
    · have hEq : Y ⊓ Z = Y := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq _)
        rw [hYcard]
        exact hp'.symm
      have hYleZ : Y ≤ Z := by
        intro y hy
        have hy' : y ∈ Y ⊓ Z := by rwa [← hEq] at hy
        exact hy'.2
      have hYZ : Y = Z := by
        apply Subgroup.eq_of_le_of_card_ge hYleZ (le_of_eq _)
        rw [hYcard]
        exact hZcard
      exact hne hYZ

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

/-- Every `p0 ∈ P0` occurs as the `P0`-part of an element of the graph
subgroup `X` (with `A = X·P`). -/
private lemma exists_P_part_of_mem_P0
    {G : Type u} [Group G] [Finite G]
    {X P P0 A : Subgroup G} {p : ℕ}
    (hA : A = P ⊔ P0) (hXleA : X ≤ A) (hXcard : Nat.card X = p) (hPcard : Nat.card P = p)
    (hX_inter_P : X ⊓ P = ⊥) (hPleNX : P ≤ Subgroup.normalizer (X : Set G))
    (hA_card : Nat.card A = p ^ 2)
    (hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G))
    {p0 : G} (hp0 : p0 ∈ P0) :
    ∃ p : G, p ∈ P ∧ p * p0 ∈ X := by
  classical
  have hcoe : ((X ⊔ P : Subgroup G) : Set G) = (X : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left X P hPleNX
  have hcardXP : Nat.card (↥(X ⊔ P)) = p * p := by
    calc
      Nat.card (↥(X ⊔ P)) = Nat.card (↥X) * Nat.card (↥P) := by
        exact natCard_sup_of_disjoint X P hPleNX hX_inter_P
      _ = p * p := by rw [hXcard, hPcard]
  have hXP_le_A : X ⊔ P ≤ A := by
    rw [hA]
    exact sup_le (by simpa [hA] using hXleA) le_sup_left
  have hXPsq : Nat.card (↥A) = p * p := by
    rw [hA_card]
    ring
  have hXP_eq_A : X ⊔ P = A := by
    apply Subgroup.eq_of_le_of_card_ge hXP_le_A (le_of_eq _)
    rw [hXPsq]
    exact hcardXP.symm
  have hp0XP : p0 ∈ (X : Set G) * (P : Set G) := by
    have hp0A : p0 ∈ A := by
      rw [hA]
      exact (le_sup_right : P0 ≤ P ⊔ P0) hp0
    have hp0XP' : p0 ∈ X ⊔ P := by rwa [← hXP_eq_A] at hp0A
    change p0 ∈ ((X ⊔ P : Subgroup G) : Set G) at hp0XP'
    rw [hcoe] at hp0XP'
    exact hp0XP'
  rcases hp0XP with ⟨x, hx, p, hp, hEq⟩
  have hxeq : p⁻¹ * p0 = x := by
    have h1 : p0 * p⁻¹ = x := by
      calc
        p0 * p⁻¹ = (x * p) * p⁻¹ := by rw [← hEq]
        _ = x := by group
    have hcomm : p0 * p⁻¹ = p⁻¹ * p0 := by
      have hp0c : p0 ∈ Subgroup.centralizer (P : Set G) := hP0leCGP hp0
      exact ((Subgroup.mem_centralizer_iff.mp hp0c) (p⁻¹) (P.inv_mem hp)).symm
    calc
      p⁻¹ * p0 = p0 * p⁻¹ := hcomm.symm
      _ = x := h1
  refine ⟨p⁻¹, P.inv_mem hp, ?_⟩
  rwa [hxeq]

/-- An element of `E` normalizing the graph subgroup `X` centralizes
`P0`: `(e·x·e⁻¹)·x⁻¹` lies in `X ∩ E = 1`. -/
private lemma centralizes_P0_of_normalizes_X_of_mem_E
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c) (d : SecondCaseComponentData w)
    {X P P0 A : Subgroup G} {p : ℕ}
    (hA : A = P ⊔ P0) (hXleA : X ≤ A)
    (hXcard : Nat.card X = p) (hPcard : Nat.card P = p)
    (hX_inter_P : X ⊓ P = ⊥) (hX_inter_E : X ⊓ d.E = ⊥)
    (hPleNX : P ≤ Subgroup.normalizer (X : Set G))
    (hA_card : Nat.card A = p ^ 2)
    (hPleCGE : P ≤ Subgroup.centralizer (d.E : Set G))
    (hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G))
    (hP0leE : P0 ≤ d.E)
    {e : G} (heE : e ∈ d.E) (heNX : e ∈ Subgroup.normalizer (X : Set G)) :
    e ∈ Subgroup.centralizer (P0 : Set G) := by
  classical
  exact Subgroup.mem_centralizer_iff.mpr (by
    intro p0 hp0
    obtain ⟨p, hp, hx⟩ := exists_P_part_of_mem_P0 hA hXleA hXcard hPcard hX_inter_P
      hPleNX hA_card hP0leCGP hp0
    have hxX : p * p0 ∈ X := hx
    have hwX : (e * (p * p0) * e⁻¹) * (p * p0)⁻¹ ∈ X := by
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp heNX (p * p0)).1 hxX)
        (X.inv_mem hxX)
    have hcomm1 : e * p = p * e := (Subgroup.mem_centralizer_iff.mp (hPleCGE hp)) e heE
    let y : G := e * p0 * e⁻¹ * p0⁻¹
    have hyE : y ∈ d.E := by
      dsimp [y]
      exact d.E.mul_mem
        (d.E.mul_mem (d.E.mul_mem heE (hP0leE hp0)) (d.E.inv_mem heE))
        (d.E.inv_mem (hP0leE hp0))
    have hpcy : p * y * p⁻¹ = y := by
      have hpy : y * p = p * y :=
        (Subgroup.mem_centralizer_iff.mp (hPleCGE hp)) y hyE
      calc
        p * y * p⁻¹ = y * p * p⁻¹ := by rw [← hpy]
        _ = y := by simp
    have hw : (e * (p * p0) * e⁻¹) * (p * p0)⁻¹ = e * p0 * e⁻¹ * p0⁻¹ := by
      calc
        (e * (p * p0) * e⁻¹) * (p * p0)⁻¹ = e * p * p0 * e⁻¹ * p0⁻¹ * p⁻¹ := by
          rw [mul_inv_rev]
          group
        _ = p * e * p0 * e⁻¹ * p0⁻¹ * p⁻¹ := by rw [hcomm1]
        _ = p * (e * p0 * e⁻¹ * p0⁻¹) * p⁻¹ := by group
        _ = e * p0 * e⁻¹ * p0⁻¹ := by simpa [y] using hpcy
    have hwE : (e * (p * p0) * e⁻¹) * (p * p0)⁻¹ ∈ d.E := by
      rw [hw]
      exact hyE
    have hwbot : (e * (p * p0) * e⁻¹) * (p * p0)⁻¹ = 1 := by
      have hmem : (e * (p * p0) * e⁻¹) * (p * p0)⁻¹ ∈ X ⊓ d.E := ⟨hwX, hwE⟩
      have hbot : (e * (p * p0) * e⁻¹) * (p * p0)⁻¹ ∈ (⊥ : Subgroup G) := by
        rwa [hX_inter_E] at hmem
      exact Subgroup.mem_bot.mp hbot
    have hw1 : e * p0 * e⁻¹ * p0⁻¹ = 1 := by
      rw [← hw]
      exact hwbot
    have hcomm : p0 * e = e * p0 := by
      calc
        p0 * e = (e * p0 * e⁻¹ * p0⁻¹)⁻¹ * (e * p0) := by group
        _ = 1⁻¹ * (e * p0) := by rw [hw1]
        _ = e * p0 := by simp
    exact hcomm)

/-- A conjugate of a subgroup centralizing `K` centralizes the conjugate
of `K`. -/
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

/-- The first aligned chain, parametrized by the conjugator `h`: for
`Xh = P^h ≤ A`, `Xh ≠ P`, `A^h = A`,
`M^h ∩ (P ⊔ E) = N_{P⊔E}(Xh) = P ⊔ K ⊔ S0 = C_{P⊔E}(A)` and
`E ∩ N_G(Xh) = K ⊔ S0`. -/
public theorem secondCase_linearEquation11_first_identity_chain
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K K0 F P P0 A S0 : Subgroup G) {p : ℕ}
    (hp : p.Prime)
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hPleF : P ≤ F) (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hK0leFU : K0 ≤ fittingSubgroupOf c.U)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hPinterE : P ⊓ d.E = ⊥)
    (hP0leK0 : P0 ≤ K0) (hK0leE : K0 ≤ d.E) (hKleE : K ≤ d.E)
    (_hKcyc : IsCyclic K)
    (hNP : Subgroup.normalizer (P : Set G) = w.M)
    (hA : A = P ⊔ P0)
    (hCP0E : (Subgroup.centralizer (P0 : Set G)) ⊓ d.E = K ⊔ S0)
    (hS0leCU : S0 ≤ Subgroup.centralizer (c.U : Set G))
    (hS0leE : S0 ≤ d.E)
    (hP_notConjP0 : ¬ ∃ h : G, conjugateSubgroup P h = P0)
    {h : G} (Xh : Subgroup G)
    (hXh : Xh = conjugateSubgroup P h) (hXh_le_A : Xh ≤ A) (hXh_ne_P : Xh ≠ P)
    (hAh : conjugateSubgroup A h = A) :
    (conjugateSubgroup w.M h ⊓ (P ⊔ d.E) =
        (P ⊔ d.E) ⊓ Subgroup.normalizer (Xh : Set G)) ∧
      ((P ⊔ d.E) ⊓ Subgroup.normalizer (Xh : Set G) = P ⊔ K ⊔ S0) ∧
      (P ⊔ K ⊔ S0 = (P ⊔ d.E) ⊓ Subgroup.centralizer (A : Set G)) ∧
      (d.E ⊓ Subgroup.normalizer (Xh : Set G) = K ⊔ S0) := by
  classical
  have hPleCGE : P ≤ Subgroup.centralizer (d.E : Set G) := hPleF.trans hFcentE
  have hP0leE : P0 ≤ d.E := hP0leK0.trans hK0leE
  have hP0leCGP : P0 ≤ Subgroup.centralizer (P : Set G) := by
    intro p0 hp0
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro p hp
      have hpcent : p ∈ Subgroup.centralizer (d.E : Set G) := hPleCGE hp
      exact ((Subgroup.mem_centralizer_iff.mp hpcent) p0 (hP0leE hp0)).symm)
  have hPinterP0 : P ⊓ P0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxPE : x ∈ P ⊓ d.E := ⟨hx.1, hP0leE hx.2⟩
    rwa [hPinterE] at hxPE
  have hA_card : Nat.card A = p ^ 2 :=
    A_card_eq_p_sq hA hPcard hP0card hP0leCGP hPinterP0
  -- `A ≤ M` (from `P ≤ N_G(P) = M` and `P0 ≤ E ≤ M`)
  have hPleM : P ≤ w.M := by
    intro p hp
    have hmem : p ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
      · intro hx
        have hback : p⁻¹ * (p * x * p⁻¹) * p ∈ P :=
          P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
        have hx' : p⁻¹ * (p * x * p⁻¹) * p = x := by group
        rwa [hx'] at hback
    rwa [hNP] at hmem
  have hP0leM : P0 ≤ w.M := hP0leE.trans d.E_component.1
  have hAleM : A ≤ w.M := by
    rw [hA]
    exact sup_le hPleM hP0leM
  -- `Xh ≤ F(U) ≤ U`
  have hA_le_FU : A ≤ fittingSubgroupOf c.U := by
    rw [hA]
    exact sup_le (hPleF.trans hFleFU) (hP0leK0.trans hK0leFU)
  have hXh_le_FU : Xh ≤ fittingSubgroupOf c.U := hXh_le_A.trans hA_le_FU
  have hXh_le_U : Xh ≤ c.U := hXh_le_FU.trans (Subgroup.map_subtype_le (fittingSubgroup c.U))
  -- `N_G(Xh) = M^h`
  have hNXh : Subgroup.normalizer (Xh : Set G) = conjugateSubgroup w.M h := by
    calc
      Subgroup.normalizer (Xh : Set G) =
          Subgroup.normalizer ((conjugateSubgroup P h) : Set G) := by rw [hXh]
      _ = conjugateSubgroup (Subgroup.normalizer (P : Set G)) h :=
          normalizer_conjugate_eq h
      _ = conjugateSubgroup w.M h := by rw [hNP]
  -- `Xh ≠ P0`, `|Xh| = p`
  have hXh_ne_P0 : Xh ≠ P0 := by
    intro hx
    apply hP_notConjP0
    rw [hXh] at hx
    exact ⟨h, hx⟩
  have hXh_card : Nat.card Xh = p := by
    rw [hXh, card_conjugate, hPcard]
  -- `Xh ∩ P = Xh ∩ P0 = Xh ∩ E = 1`
  have hXh_inter_P : Xh ⊓ P = ⊥ :=
    inter_eq_bot_of_card_eq_prime_of_ne hp hXh_card hPcard hXh_ne_P
  have hXh_inter_P0 : Xh ⊓ P0 = ⊥ :=
    inter_eq_bot_of_card_eq_prime_of_ne hp hXh_card hP0card hXh_ne_P0
  have hA_inter_E : A ⊓ d.E = P0 := A_inter_E_eq_P0 d.E hA hP0leE hPinterE hP0leCGP
  have hXh_inter_E : Xh ⊓ d.E = ⊥ :=
    inter_eq_bot_of_le_A_of_ne_P0 hA_inter_E hXh_le_A hXh_ne_P0 hXh_card hP0card hp
  -- `A^{h⁻¹} = A` and `P ≤ N_G(Xh) = M^h`
  have hAh' : conjugateSubgroup A h⁻¹ = A := by
    have h1 : conjugateSubgroup (conjugateSubgroup A h) h⁻¹ = A := by
      calc
        conjugateSubgroup (conjugateSubgroup A h) h⁻¹ =
            conjugateSubgroup A (h⁻¹ * h) := conjugate_conjugate (H := A) h h⁻¹
        _ = A := by simp [conjugate_one]
    rwa [hAh] at h1
  have hP_le_Mh : P ≤ conjugateSubgroup w.M h := by
    intro p hp
    have hpA : h⁻¹ * p * h ∈ A := by
      have hpAh : h⁻¹ * p * h ∈ conjugateSubgroup A h⁻¹ :=
        Subgroup.mem_map.mpr ⟨p, by
          rw [hA]
          exact (le_sup_left : P ≤ P ⊔ P0) hp, by simp⟩
      rwa [hAh'] at hpAh
    have hpM : h⁻¹ * p * h ∈ w.M := hAleM hpA
    exact Subgroup.mem_map.mpr ⟨h⁻¹ * p * h, hpM, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hPleNXh : P ≤ Subgroup.normalizer (Xh : Set G) := by
    rwa [hNXh]
  -- `K ≤ C_G(A)` (via `K ≤ E`, `P0 ≤ K` cyclic), hence `K ≤ N_G(Xh)`
  have hKleCA : K ≤ Subgroup.centralizer (A : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro a ha
      have hP0leN : P0 ≤ Subgroup.normalizer (P : Set G) := by
        intro p0 hp0
        exact Subgroup.centralizer_le_normalizer (P : Set G) (hP0leCGP hp0)
      have hcoe : ((P ⊔ P0 : Subgroup G) : Set G) = (P : Set G) * (P0 : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left P P0 hP0leN
      have haPP0 : a ∈ (P : Set G) * (P0 : Set G) := by
        have ha' : a ∈ P ⊔ P0 := by simpa [hA] using ha
        change a ∈ ((P ⊔ P0 : Subgroup G) : Set G) at ha'
        rw [hcoe] at ha'
        exact ha'
      rcases haPP0 with ⟨p, hp, p0, hp0, hpa⟩
      have hkp : p * k = k * p := by
        have hpcent := (Subgroup.mem_centralizer_iff.mp (hPleCGE hp)) k (hKleE hk)
        exact hpcent.symm
      have hkp0 : p0 * k = k * p0 := by
        have hkCP0 : k ∈ Subgroup.centralizer (P0 : Set G) := by
          have hk' : k ∈ K ⊔ S0 := (le_sup_left : K ≤ K ⊔ S0) hk
          have hkCE : k ∈ (Subgroup.centralizer (P0 : Set G)) ⊓ d.E := by
            rw [hCP0E]
            exact hk'
          exact hkCE.1
        exact (Subgroup.mem_centralizer_iff.mp hkCP0) p0 hp0
      calc
        a * k = (p * p0) * k := congrArg (fun z => z * k) hpa.symm
        _ = p * (p0 * k) := by group
        _ = p * (k * p0) := by rw [hkp0]
        _ = (p * k) * p0 := by group
        _ = (k * p) * p0 := by rw [hkp]
        _ = k * (p * p0) := by group
        _ = k * a := congrArg (fun z => k * z) hpa)
  have hKleCXh : K ≤ Subgroup.centralizer (Xh : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hKleCA hk)) x (hXh_le_A hx))
  have hKleMXh : K ≤ Subgroup.normalizer (Xh : Set G) := by
    intro k hk
    exact (Subgroup.centralizer_le_normalizer (Xh : Set G)) (hKleCXh hk)
  -- `S0 ≤ C_G(Xh) ≤ N_G(Xh)` (via `[S0, U] = 1` and `Xh ≤ U`)
  have hS0leCXh : S0 ≤ Subgroup.centralizer (Xh : Set G) := by
    intro s hs
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hS0leCU hs)) x (hXh_le_U hx))
  have hS0leMXh : S0 ≤ Subgroup.normalizer (Xh : Set G) := by
    intro s hs
    exact (Subgroup.centralizer_le_normalizer (Xh : Set G)) (hS0leCXh hs)
  -- `E ∩ N_G(Xh) = C_E(P0) = K ⊔ S0`
  have hE_inter_NXh : d.E ⊓ Subgroup.normalizer (Xh : Set G) = K ⊔ S0 := by
    apply le_antisymm
    · intro e he
      have heC : e ∈ Subgroup.centralizer (P0 : Set G) :=
        centralizes_P0_of_normalizes_X_of_mem_E c w d hA hXh_le_A hXh_card hPcard
          hXh_inter_P hXh_inter_E hPleNXh hA_card hPleCGE hP0leCGP hP0leE he.1 he.2
      have hmem : e ∈ (Subgroup.centralizer (P0 : Set G)) ⊓ d.E := ⟨heC, he.1⟩
      rwa [hCP0E] at hmem
    · intro e he
      have heE : e ∈ d.E := (sup_le hKleE hS0leE) he
      have heCP0 : e ∈ Subgroup.centralizer (P0 : Set G) := by
        have hmem : e ∈ (Subgroup.centralizer (P0 : Set G)) ⊓ d.E := by
          rw [hCP0E]
          exact he
        exact hmem.1
      have heCP : e ∈ Subgroup.centralizer (P : Set G) := by
        exact Subgroup.mem_centralizer_iff.mpr (by
          intro p hp
          have hpcent : p ∈ Subgroup.centralizer (d.E : Set G) := hPleCGE hp
          exact ((Subgroup.mem_centralizer_iff.mp hpcent) e heE).symm)
      have heCXh : e ∈ Subgroup.centralizer (Xh : Set G) := by
        exact Subgroup.mem_centralizer_iff.mpr (by
          intro x hx
          have hP0leN : P0 ≤ Subgroup.normalizer (P : Set G) := by
            intro p0 hp0
            exact (Subgroup.centralizer_le_normalizer (P : Set G)) (hP0leCGP hp0)
          have hcoe : ((P ⊔ P0 : Subgroup G) : Set G) = (P : Set G) * (P0 : Set G) :=
            Subgroup.coe_mul_of_right_le_normalizer_left P P0 hP0leN
          have hxP0 : x ∈ (P : Set G) * (P0 : Set G) := by
            have hxA : x ∈ P ⊔ P0 := by simpa [hA] using hXh_le_A hx
            change x ∈ ((P ⊔ P0 : Subgroup G) : Set G) at hxA
            rw [hcoe] at hxA
            exact hxA
          rcases hxP0 with ⟨p, hp, p0, hp0, hEq⟩
          have hcomm1 : e * p = p * e :=
            (Subgroup.mem_centralizer_iff.mp (hPleCGE hp)) e heE
          have hcomm2 : e * p0 = p0 * e :=
            ((Subgroup.mem_centralizer_iff.mp heCP0) p0 hp0).symm
          calc
            x * e = (p * p0) * e := congrArg (fun z => z * e) hEq.symm
            _ = p * (p0 * e) := by group
            _ = p * (e * p0) := by rw [hcomm2]
            _ = (p * e) * p0 := by group
            _ = (e * p) * p0 := by rw [hcomm1]
            _ = e * (p * p0) := by group
            _ = e * x := congrArg (fun z => e * z) hEq)
      exact ⟨heE, (Subgroup.centralizer_le_normalizer (Xh : Set G)) heCXh⟩
  -- `P ≤ C_G(A)`
  have hPleCA : P ≤ Subgroup.centralizer (A : Set G) := by
    intro q hq
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro a ha
      have hP0leN : P0 ≤ Subgroup.normalizer (P : Set G) := by
        intro p0 hp0
        exact (Subgroup.centralizer_le_normalizer (P : Set G)) (hP0leCGP hp0)
      have hcoe : ((P ⊔ P0 : Subgroup G) : Set G) = (P : Set G) * (P0 : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left P P0 hP0leN
      have haP0 : a ∈ (P : Set G) * (P0 : Set G) := by
        have haA : a ∈ P ⊔ P0 := by simpa [hA] using ha
        change a ∈ ((P ⊔ P0 : Subgroup G) : Set G) at haA
        rw [hcoe] at haA
        exact haA
      rcases haP0 with ⟨p', hp', p0, hp0, hEq⟩
      let : Fact (Nat.Prime p) := ⟨hp⟩
      let : IsCyclic P := isCyclic_of_prime_card hPcard
      let : CommGroup P := IsCyclic.commGroup
      have hcomm1 : q * p' = p' * q := by
        exact congrArg Subtype.val
          (show (⟨q, hq⟩ : P) * ⟨p', hp'⟩ = ⟨p', hp'⟩ * ⟨q, hq⟩ by
            exact mul_comm _ _)
      have hcomm2 : q * p0 = p0 * q :=
        (Subgroup.mem_centralizer_iff.mp (hP0leCGP hp0)) q hq
      calc
        a * q = (p' * p0) * q := congrArg (fun z => z * q) hEq.symm
        _ = p' * (p0 * q) := by group
        _ = p' * (q * p0) := by rw [hcomm2]
        _ = (p' * q) * p0 := by group
        _ = (q * p') * p0 := by rw [hcomm1]
        _ = q * (p' * p0) := by group
        _ = q * a := congrArg (fun z => q * z) hEq)
  -- `P ⊔ K ⊔ S0 ≤ M^h ∩ (P ⊔ E)` and `P ⊔ K ⊔ S0 ≤ (P ⊔ E) ∩ C_G(A)`
  have hPKS0_le_MhPE : P ⊔ K ⊔ S0 ≤ conjugateSubgroup w.M h ⊓ (P ⊔ d.E) := by
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · intro q hq
        exact ⟨hP_le_Mh hq, (le_sup_left : P ≤ P ⊔ d.E) hq⟩
      · intro k hk
        have hkN : k ∈ Subgroup.normalizer (Xh : Set G) := hKleMXh hk
        have hkM : k ∈ conjugateSubgroup w.M h := hNXh ▸ hkN
        exact ⟨hkM, (hKleE.trans (le_sup_right : d.E ≤ P ⊔ d.E)) hk⟩
    · intro s hs
      have hsN : s ∈ Subgroup.normalizer (Xh : Set G) := hS0leMXh hs
      have hsM : s ∈ conjugateSubgroup w.M h := hNXh ▸ hsN
      exact ⟨hsM, (hS0leE.trans (le_sup_right : d.E ≤ P ⊔ d.E)) hs⟩
  have hPKS0_le_CPEA : P ⊔ K ⊔ S0 ≤ (P ⊔ d.E) ⊓ Subgroup.centralizer (A : Set G) := by
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · intro q hq
        exact ⟨(le_sup_left : P ≤ P ⊔ d.E) hq, hPleCA hq⟩
      · intro k hk
        exact ⟨(hKleE.trans (le_sup_right : d.E ≤ P ⊔ d.E)) hk, hKleCA hk⟩
    · intro s hs
      exact ⟨(hS0leE.trans (le_sup_right : d.E ≤ P ⊔ d.E)) hs,
        Subgroup.mem_centralizer_iff.mpr (by
          intro a ha
          have haU : a ∈ c.U :=
            (hA_le_FU.trans (Subgroup.map_subtype_le (fittingSubgroup c.U))) ha
          exact (Subgroup.mem_centralizer_iff.mp (hS0leCU hs)) a haU)⟩
  -- the reverse inclusions
  have hEleNP : d.E ≤ Subgroup.normalizer (P : Set G) := by
    intro e he
    exact (Subgroup.centralizer_le_normalizer (P : Set G))
      (Subgroup.mem_centralizer_iff.mpr (by
        intro p hp
        exact ((Subgroup.mem_centralizer_iff.mp (hPleCGE hp)) e he).symm))
  have hcoePE : ((P ⊔ d.E : Subgroup G) : Set G) = (P : Set G) * (d.E : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P d.E hEleNP
  have hMhPE_le_PKS0 : conjugateSubgroup w.M h ⊓ (P ⊔ d.E) ≤ P ⊔ K ⊔ S0 := by
    intro m hm
    have hmPE : m ∈ (P : Set G) * (d.E : Set G) := by
      have hmPE' := hm.2
      change m ∈ ((P ⊔ d.E : Subgroup G) : Set G) at hmPE'
      rw [hcoePE] at hmPE'
      exact hmPE'
    rcases hmPE with ⟨p, hp, e, he, hEq⟩
    have heMh : e ∈ conjugateSubgroup w.M h := by
      have hEq' : e = p⁻¹ * m := by
        calc
          e = p⁻¹ * (p * e) := by group
          _ = p⁻¹ * m := congrArg (fun z => p⁻¹ * z) hEq
      have hmem : p⁻¹ * m ∈ conjugateSubgroup w.M h :=
        (conjugateSubgroup w.M h).mul_mem
          ((conjugateSubgroup w.M h).inv_mem (hP_le_Mh hp)) hm.1
      rw [hEq']
      exact hmem
    have heNX : e ∈ Subgroup.normalizer (Xh : Set G) := by
      exact hNXh.symm ▸ heMh
    have heKS : e ∈ K ⊔ S0 := by
      have hmem : e ∈ d.E ⊓ Subgroup.normalizer (Xh : Set G) := ⟨he, heNX⟩
      rwa [hE_inter_NXh] at hmem
    have hmKS : m ∈ P ⊔ (K ⊔ S0) := by
      rw [← hEq]
      exact (P ⊔ (K ⊔ S0)).mul_mem
        ((le_sup_left : P ≤ P ⊔ (K ⊔ S0)) hp)
        ((le_sup_right : K ⊔ S0 ≤ P ⊔ (K ⊔ S0)) heKS)
    simpa [sup_assoc] using hmKS
  have hCPEA_le_PKS0 : (P ⊔ d.E) ⊓ Subgroup.centralizer (A : Set G) ≤ P ⊔ K ⊔ S0 := by
    intro m hm
    have hmPE : m ∈ (P : Set G) * (d.E : Set G) := by
      have hmPE' := hm.1
      change m ∈ ((P ⊔ d.E : Subgroup G) : Set G) at hmPE'
      rw [hcoePE] at hmPE'
      exact hmPE'
    rcases hmPE with ⟨p, hp, e, he, hEq⟩
    have hEq' : e = p⁻¹ * m := by
      calc
        e = p⁻¹ * (p * e) := by group
        _ = p⁻¹ * m := congrArg (fun z => p⁻¹ * z) hEq
    have heCA : e ∈ Subgroup.centralizer (A : Set G) := by
      rw [hEq']
      exact (Subgroup.centralizer (A : Set G)).mul_mem
        ((Subgroup.centralizer (A : Set G)).inv_mem (hPleCA hp)) hm.2
    have heCP0 : e ∈ Subgroup.centralizer (P0 : Set G) := by
      have hmem : e ∈ (Subgroup.centralizer (P0 : Set G)) ⊓ d.E := by
        exact ⟨Subgroup.mem_centralizer_iff.mpr (by
          intro p0 hp0
          exact (Subgroup.mem_centralizer_iff.mp heCA) p0 (by
            rw [hA]
            exact (le_sup_right : P0 ≤ P ⊔ P0) hp0)), he⟩
      exact hmem.1
    have heKS : e ∈ K ⊔ S0 := by
      have hmem : e ∈ (Subgroup.centralizer (P0 : Set G)) ⊓ d.E := ⟨heCP0, he⟩
      rwa [hCP0E] at hmem
    have hmKS : m ∈ P ⊔ (K ⊔ S0) := by
      rw [← hEq]
      exact (P ⊔ (K ⊔ S0)).mul_mem
        ((le_sup_left : P ≤ P ⊔ (K ⊔ S0)) hp)
        ((le_sup_right : K ⊔ S0 ≤ P ⊔ (K ⊔ S0)) heKS)
    simpa [sup_assoc] using hmKS
  have hNPE_eq : (P ⊔ d.E) ⊓ Subgroup.normalizer (Xh : Set G) = P ⊔ K ⊔ S0 := by
    apply le_antisymm
    · intro m hm
      have hmem : m ∈ conjugateSubgroup w.M h ⊓ (P ⊔ d.E) := by
        exact ⟨hNXh ▸ hm.2, hm.1⟩
      exact hMhPE_le_PKS0 hmem
    · intro m hm
      have hmem : m ∈ conjugateSubgroup w.M h ⊓ (P ⊔ d.E) := hPKS0_le_MhPE hm
      exact ⟨hmem.2, hNXh.symm ▸ hmem.1⟩
  have hCPEA_eq : P ⊔ K ⊔ S0 = (P ⊔ d.E) ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · exact hPKS0_le_CPEA
    · exact hCPEA_le_PKS0
  have hMhPE_eq : conjugateSubgroup w.M h ⊓ (P ⊔ d.E) =
      (P ⊔ d.E) ⊓ Subgroup.normalizer (Xh : Set G) := by
    apply le_antisymm
    · intro m hm
      exact ⟨hm.2, hNXh.symm ▸ hm.1⟩
    · intro m hm
      exact ⟨hNXh ▸ hm.2, hm.1⟩
  exact ⟨hMhPE_eq, hNPE_eq, hCPEA_eq, hE_inter_NXh⟩

end CFSG.GorensteinWalter
