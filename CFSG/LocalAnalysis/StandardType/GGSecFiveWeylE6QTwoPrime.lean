module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem USixTwo.card_U {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 9196830720 := by
  have hcard : Nat.card K = ((2 ^ 1) ^ 2) := by rw [hK]; norm_num
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 2) (f := 1)
    (n := 6) Nat.prime_two (by norm_num) hcard (by norm_num)
  rw [CFSG.Assembly.largeEvenProj_eq_statedProj,
    CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
  rw [h]
  decide

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveE6QTwoCfg.prime_eq_three
    {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGSecFiveE6QTwoCfg p B Bs x L D J) : p = 3 := by
  obtain ⟨𝒦, hR, -, ι, M, e, hpres, -, r, hrA, hrCox, h6⟩ := hC
  obtain ⟨hRest, -, -, -⟩ := hR
  obtain ⟨hCfg, -, hInner, -, -, -⟩ := hRest
  obtain ⟨hThmI, hBstar, -⟩ := hCfg
  have hp : p.Prime := hThmI.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hThmI.2.2.2.2.2.1.2.1
  obtain ⟨-, hElem, -⟩ := hBstar
  have href : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrCox
  have hr2 : r * r = 1 := by rw [← pow_two]; exact href.1
  have hbex : ∃ b : ↥Bs, r b ≠ b := by
    by_contra h
    push Not at h
    have hcard : Nat.card {b : ↥Bs // r b = b} = Nat.card ↥Bs :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    have h2 := href.2
    rw [hcard] at h2
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by simpa using h2)
    exact hp.ne_one hp1
  obtain ⟨b, hb⟩ := hbex
  obtain ⟨n, hnS, -, hnind⟩ := ggExists_weylElt_of_mem_ggAutomizer hrA hr2
  let b0 : G := (b : G)⁻¹ * ((r b : ↥Bs) : G)
  have hb0mem : b0 ∈ Bs := Bs.mul_mem (Bs.inv_mem b.2) (r b).2
  have hb0ne : b0 ≠ 1 := by
    intro h
    apply hb
    have h' : (b : G) * b0 = (b : G) := by rw [h, mul_one]
    have h2 : ((r b : ↥Bs) : G) = (b : G) := by
      dsimp only [b0] at h'
      simpa [mul_assoc] using h'
    exact Subtype.ext h2
  have hb0p : b0 ^ p = 1 := hElem.2 b0 hb0mem
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf b0 = p := orderOf_eq_prime hb0p hb0ne
  have hrr : ∀ y : ↥Bs, r (r y) = y := by
    intro y
    have h := congrArg (fun f : MulAut ↥Bs => f y) href.1
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hb0s : (⟨b0, hb0mem⟩ : ↥Bs) = (⟨b, b.2⟩ : ↥Bs)⁻¹ * (r ⟨b, b.2⟩) := by
    apply Subtype.ext
    simp [b0]
  have hrb0 : ((r ⟨b0, hb0mem⟩ : ↥Bs) : G) = b0⁻¹ := by
    rw [hb0s, map_mul, map_inv, hrr]
    simp [b0, mul_inv_rev]
  have hninverts : n * b0 * n⁻¹ = b0⁻¹ := (hnind ⟨b0, hb0mem⟩).symm.trans hrb0
  have hkey : n * b0⁻¹ = b0 * n := by
    have h1 : n * b0⁻¹ * n⁻¹ = b0 := by
      have h := congrArg (fun t => t⁻¹) hninverts
      simpa [mul_assoc] using h
    calc n * b0⁻¹ = n * b0⁻¹ * n⁻¹ * n := by group
      _ = b0 * n := by rw [h1]
  have hsq : b0 ^ 2 = (b0 * n * b0⁻¹) * n⁻¹ := by
    have h2 : b0 * n * b0⁻¹ * n⁻¹ = b0 ^ 2 := by
      calc b0 * n * b0⁻¹ * n⁻¹ = b0 * (n * b0⁻¹) * n⁻¹ := by group
        _ = b0 * (b0 * n) * n⁻¹ := by rw [hkey]
        _ = b0 ^ 2 := by rw [pow_two]; group
    exact h2.symm
  have hb0N : b0 ∈ Subgroup.normalizer (L : Set G) := hInner.1.le_normalizer hb0mem
  have hLmap : L.map (MulAut.conj b0).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hb0N
  have ha1 : ∀ y : ↥Bs, ((((1 : MulAut ↥Bs)) y : ↥Bs) : G) = b0 * y * b0⁻¹ := by
    intro y
    simp only [MulAut.one_apply, Subgroup.coe_subtype]
    rw [CFSG.Open.IsElemAbelian.comm hElem hb0mem y.2]
    group
  have hconj := ggRankOneIn_map_conj (X := L) (g := b0) (a := 1) ha1 r
  rw [hLmap] at hconj
  simp only [one_mul, mul_one, inv_one] at hconj
  have hconjS : b0 * n * b0⁻¹ ∈ ggRankOneIn L Bs r := by
    rw [← hconj]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj b0).toMonoidHom hnS
  have hmemS : b0 ^ 2 ∈ ggRankOneIn L Bs r := by
    rw [hsq]
    exact (ggRankOneIn L Bs r).mul_mem hconjS ((ggRankOneIn L Bs r).inv_mem hnS)
  have h2ne : b0 ^ 2 ≠ 1 := by
    intro h
    have hd : orderOf b0 ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hord2 : orderOf (b0 ^ 2) = p := by
    refine orderOf_eq_prime ?_ h2ne
    rw [← pow_mul, show 2 * p = p * 2 by ring, pow_mul, hb0p, one_pow]
  have hdvd : p ∣ 6 := by
    have h := Subgroup.orderOf_dvd_natCard (ggRankOneIn L Bs r) hmemS
    rw [h6, hord2] at h
    exact h
  have h23 : p ∣ 2 ∨ p ∣ 3 := by
    have h : p ∣ 2 * 3 := by simpa using hdvd
    exact hp.dvd_mul.mp h
  rcases h23 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h

end Cfg

end CFSG.StandardType

end
