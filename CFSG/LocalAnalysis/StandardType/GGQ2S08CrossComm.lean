module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTrivial

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

private theorem ggQ2s08g1_commutator_zpowers_le {G : Type} [Group G] {X P : Subgroup G} {c : G}
    (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (h : ∀ x ∈ X, ⁅x, c⁆ ∈ P) :
    ⁅X, Subgroup.zpowers c⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro x hx z hz
  have hT : ∀ z ∈ Subgroup.zpowers c, ⁅x, z⁆ ∈ P := by
    let T : Subgroup G :=
      { carrier := {z : G | z ∈ Subgroup.normalizer (P : Set G) ∧ ⁅x, z⁆ ∈ P}
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          intro y z hy hz
          obtain ⟨hyN, hyP⟩ := hy
          obtain ⟨hzN, hzP⟩ := hz
          refine ⟨Subgroup.mul_mem _ hyN hzN, ?_⟩
          have h1 : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          rw [h1]
          exact P.mul_mem hyP ((Subgroup.mem_normalizer_iff.mp hyN _).mp hzP)
        inv_mem' := by
          intro y hy
          obtain ⟨hyN, hyP⟩ := hy
          refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
          have h1 : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          have h2 : y⁻¹ * ⁅x, y⁆ * y ∈ P := by
            have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp hyP
            simpa only [inv_inv] using h3
          rw [h1]
          simpa only [mul_inv_rev, inv_inv, mul_assoc] using Subgroup.inv_mem _ h2 }
    have hcT : c ∈ T := ⟨hcP, h x hx⟩
    intro z hz
    exact (Subgroup.zpowers_le.mpr hcT hz).2
  exact hT z hz

private theorem ggQ2s08g1_commutator_le {G : Type} [Group G] {p : ℕ}
    {Bs Q X Y O : Subgroup G} {n b : G}
    (hnQ : n ∈ Q) (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) (hb : b ∈ Bs)
    (hQY : Q ≤ Y) (hBsY : Bs ≤ Y) (hOn : Y ≤ Subgroup.normalizer (O : Set G))
    (hcommQ : ⁅Q, X⁆ ≤ O) (hXO : X ⊓ O ≤ LargeEvenPPrimeCoreOf p X)
    (hXBs : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ⁅n, b⁆ ∈ Bs ∧ ⁅X, Subgroup.zpowers ⁅n, b⁆⁆ ≤ LargeEvenPPrimeCoreOf p X := by
  have hnY : n ∈ Y := hQY hnQ
  set h : G := b * n * b⁻¹ with hhdef
  set c : G := n * h⁻¹ with hcdef
  have hc_eq : c = ⁅n, b⁆ := by
    rw [hcdef, hhdef, commutatorElement_def]
    group
  have hcBs : c ∈ Bs := by
    have h1 : n * b * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnN b).mp hb
    rw [hc_eq, commutatorElement_def]
    exact Bs.mul_mem h1 (Bs.inv_mem hb)
  have hcN : c ∈ Subgroup.normalizer (X : Set G) := hXBs hcBs
  have hcP : c ∈ Subgroup.normalizer (LargeEvenPPrimeCoreOf p X : Set G) :=
    mem_normalizer_largeEvenPPrimeCoreOf hcN
  have hhY : h ∈ Y := by
    rw [hhdef]
    exact Y.mul_mem (Y.mul_mem (hBsY hb) hnY) (Y.inv_mem (hBsY hb))
  have hxc : ∀ z ∈ X, ⁅z, c⁆ ∈ LargeEvenPPrimeCoreOf p X := by
    intro z hz
    have hhz : ⁅h, z⁆ ∈ O := by
      have hbz : b⁻¹ * z * b ∈ X := by
        have hbN : b⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
          Subgroup.inv_mem _ (hXBs hb)
        simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hbN z).mp hz
      have h1 : ⁅h, z⁆ = b * ⁅n, b⁻¹ * z * b⁆ * b⁻¹ := by
        rw [hhdef, commutatorElement_def, commutatorElement_def]
        group
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp (hOn (hBsY hb)) _).mp
        ((Subgroup.commutator_le.mp hcommQ) n hnQ (b⁻¹ * z * b) hbz)
    have hnz : ⁅n, z⁆ ∈ O := (Subgroup.commutator_le.mp hcommQ) n hnQ z hz
    set o3 : G := (n * ⁅h⁻¹, z⁆ * n⁻¹) * ⁅n, z⁆ with ho3def
    have hhinv : ⁅h⁻¹, z⁆ ∈ O := by
      have h1 : h⁻¹ * ⁅h, z⁆ * h ∈ O := by
        have h3 := (Subgroup.mem_normalizer_iff.mp (hOn (Y.inv_mem hhY)) _).mp hhz
        simpa only [inv_inv] using h3
      have h2 : (h⁻¹ * ⁅h, z⁆ * h)⁻¹ ∈ O := Subgroup.inv_mem _ h1
      have h3 : (h⁻¹ * ⁅h, z⁆ * h)⁻¹ = ⁅h⁻¹, z⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rwa [h3] at h2
    have ho3O : o3 ∈ O :=
      O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hOn hnY) _).mp hhinv) hnz
    have hcx : c * z * c⁻¹ = o3 * z := by
      rw [hcdef, ho3def, hhdef]
      simp only [commutatorElement_def]
      group
    have ho3X : o3 ∈ X := by
      have h1 : o3 = (c * z * c⁻¹) * z⁻¹ := by
        rw [hcx]
        group
      rw [h1]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN z).mp hz) (X.inv_mem hz)
    have ho3P : o3 ∈ LargeEvenPPrimeCoreOf p X := hXO ⟨ho3X, ho3O⟩
    have hcz : ⁅c, z⁆ = o3 := by
      rw [commutatorElement_def, hcx]
      group
    have hzc : ⁅z, c⁆ = o3⁻¹ := by
      rw [← commutatorElement_inv c z, hcz]
    rw [hzc]
    exact Subgroup.inv_mem _ ho3P
  have hcommzp : ⁅X, Subgroup.zpowers c⁆ ≤ LargeEvenPPrimeCoreOf p X :=
    ggQ2s08g1_commutator_zpowers_le hcP hxc
  exact ⟨hc_eq ▸ hcBs, hc_eq ▸ hcommzp⟩

private theorem ggQ2s08g1_pcore_eq {G : Type} [Group G] (p : ℕ) (H : Subgroup G) :
    LargeEvenPPrimeCoreOf p H = CFSG.Open.lBalancePrimeCore p H := by
  rw [ComponentClassification.LBalance.primeCore_eq_map]
  rfl

private theorem ggQ2s08g1_inf_pcore_le {G : Type} [Group G] {p : ℕ} {Y X O : Subgroup G}
    (hXY : X ≤ Y) (hOn : Y ≤ Subgroup.normalizer (O : Set G))
    (hOcop : Nat.Coprime p (Nat.card O)) :
    X ⊓ O ≤ LargeEvenPPrimeCoreOf p X := by
  have hK : (X ⊓ O).subgroupOf X ≤ CFSG.pPrimeCore p ↥X := by
    apply le_sSup
    refine ⟨?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro o m ho hm
      exact ⟨X.mul_mem (X.mul_mem hm ho.1) (X.inv_mem hm),
        (Subgroup.mem_normalizer_iff.mp (hOn (hXY hm)) o).mp ho.2⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hOcop
  have h2 := Subgroup.map_mono (f := X.subtype) hK
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h2
  rw [LargeEvenPPrimeCoreOf, LargeEvenPPrimeCore]
  exact h2

theorem ggQ2s08_cross_commutes {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H X X' Bs : Subgroup G} (hX : LargeEvenPComponent p H X) (hX' : LargeEvenPComponent p H X')
    (hne : X ≠ X') (hBp : ∀ b ∈ Bs, b ^ p = 1) (hBH : Bs ≤ H)
    (hBX : Bs ≤ Subgroup.normalizer (X : Set G)) (hBX' : Bs ≤ Subgroup.normalizer (X' : Set G))
    {n : G} (hnX : n ∈ X) (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) :
    (∀ z ∈ Bs, ⁅X, Subgroup.zpowers z⁆ ≤ LargeEvenPPrimeCoreOf p X → n * z * n⁻¹ = z) ∧
      ∀ b ∈ Bs, ⁅n, b⁆ ∈ Bs ∧ ⁅X', Subgroup.zpowers ⁅n, b⁆⁆ ≤ LargeEvenPPrimeCoreOf p X' := by
  classical
  constructor
  · intro z hzBs hz
    have hcommO : ⁅n, z⁆ ∈ LargeEvenPPrimeCoreOf p X :=
      (Subgroup.commutator_le.mp hz) n hnX z (Subgroup.mem_zpowers z)
    have hcommBs : ⁅n, z⁆ ∈ Bs := by
      rw [commutatorElement_def]
      exact Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp hnN z).mp hzBs) (Bs.inv_mem hzBs)
    have hcommp : (⁅n, z⁆) ^ p = 1 := hBp _ hcommBs
    have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p X)) := by
      rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have h1 : ⁅n, z⁆ = 1 :=
      GGDichotomy.eq_one_of_mem_of_coprime hOcop hcommO hcommp
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    rw [h1]
    group
  · intro b hb
    have hcomm : (⁅X, X'⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p H := by
      rw [ggQ2s08g1_pcore_eq p H]
      exact GGDichotomy.commutator_le_primeCore_of_ne
        ((largeEvenPComponent_iff_lBalance p H X).1 hX).2
        ((largeEvenPComponent_iff_lBalance p H X').1 hX').2 hne
    have hXO : X' ⊓ LargeEvenPPrimeCoreOf p H ≤ LargeEvenPPrimeCoreOf p X' :=
      ggQ2s08g1_inf_pcore_le hX'.1
        (fun h hh => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hh))
        (by
          rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
          exact CFSG.pPrimeCore_coprime_card)
    exact ggQ2s08g1_commutator_le (Q := X) (X := X') (Y := H)
      (O := LargeEvenPPrimeCoreOf p H) hnX hnN hb hX.1 hBH
      (fun h hh => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hh))
      hcomm hXO hBX'

end CFSG.StandardType

end
