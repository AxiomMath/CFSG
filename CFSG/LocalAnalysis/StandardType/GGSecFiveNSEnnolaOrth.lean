module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoordModel
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthCoord
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthRelA
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthRelB
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthInd
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsLiftOmega
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative NbrFrameOne

@[expose] def GGTorusForkEltSC (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ ∧ τ.range = E ∧
      ∃ φ : Fin 4 → MulAut (Multiplicative (Fin k → ZMod p)),
        (∀ j, ∃ w : R, ∀ f, w⁻¹ * τ f * w = τ (φ j f)) ∧
        (∀ j, φ j ^ 2 = 1 ∧ Nat.card {f : Multiplicative (Fin k → ZMod p) // φ j f = f} * p =
          Nat.card (Multiplicative (Fin k → ZMod p))) ∧
        (∀ j, j ≠ 0 → orderOf (φ 0 * φ j) = 3) ∧
        (∀ j j', j ≠ 0 → j' ≠ 0 → j ≠ j' → orderOf (φ j * φ j') = 2)

theorem ggTorusFork_of_forkEltSC {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusForkEltSC p R) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusFork p A := by
  intro L' _ _ ψ A hA
  obtain ⟨k, τ, Θ, -, ⟨φ, hφw, hφsq, h0, h1⟩, hmodel⟩ :=
    ggTorusCoordModel hp hp2 hZ hIp hcp
      (fun k τ => ∃ φ : Fin 4 → MulAut (Multiplicative (Fin k → ZMod p)),
        (∀ j, ∃ w : R, ∀ f, w⁻¹ * τ f * w = τ (φ j f)) ∧
        (∀ j, φ j ^ 2 = 1 ∧ Nat.card {f : Multiplicative (Fin k → ZMod p) // φ j f = f} * p =
          Nat.card (Multiplicative (Fin k → ZMod p))) ∧
        (∀ j, j ≠ 0 → orderOf (φ 0 * φ j) = 3) ∧
        (∀ j j', j ≠ 0 → j' ≠ 0 → j ≠ j' → orderOf (φ j * φ j') = 2))
      h L' ψ A hA
  have hrefl : ∀ j, ∃ a ∈ ggTorusReflSet p A, a = MulAut.congr Θ (φ j) := by
    intro j
    obtain ⟨w, hw⟩ := hφw j
    obtain ⟨n, hn, hW, heq⟩ := hmodel (φ j) w hw
    refine ⟨ggConjAut A hn, ⟨n, hn, hW, rfl, ?_⟩, heq⟩
    rw [heq]
    exact ggIsReflection_congr Θ (hφsq j).1 (hφsq j).2
  choose a ha hae using hrefl
  have hord : ∀ j j', orderOf (a j * a j') = orderOf (φ j * φ j') := by
    intro j j'
    rw [hae j, hae j', ← map_mul, MulEquiv.orderOf_eq]
  refine ⟨a 0, ha 0, a 1, ha 1, a 2, ha 2, a 3, ha 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hord]
    exact h0 1 (by decide)
  · rw [hord]
    exact h0 2 (by decide)
  · rw [hord]
    exact h0 3 (by decide)
  · rw [hord]
    exact h1 1 2 (by decide) (by decide) (by decide)
  · rw [hord]
    exact h1 1 3 (by decide) (by decide) (by decide)
  · rw [hord]
    exact h1 2 3 (by decide) (by decide) (by decide)

namespace EnnolaFork

variable {p k : ℕ}

private theorem forkAut_sq_card (hp : p.Prime) {a b c d : Fin k} (hab : a ≠ b) (hbc : b ≠ c)
    (hcd : c ≠ d) (j : Fin 4) :
    (forkAut a b c d j : MulAut (Multiplicative (Fin k → ZMod p))) ^ 2 = 1 ∧
      Nat.card {f : Multiplicative (Fin k → ZMod p) // forkAut a b c d j f = f} * p =
        Nat.card (Multiplicative (Fin k → ZMod p)) := by
  fin_cases j
  · exact ⟨swapAut_sq b c, card_fix_swapAut hp hbc⟩
  · exact ⟨swapAut_sq a b, card_fix_swapAut hp hab⟩
  · exact ⟨swapAut_sq c d, card_fix_swapAut hp hcd⟩
  · exact ⟨antiSwapAut_sq hcd, card_fix_antiSwapAut hp hcd⟩

private theorem forkAut_orders (hp : p.Prime) (hp2 : p ≠ 2) {a b c d : Fin k} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (∀ j, j ≠ 0 → orderOf (forkAut a b c d 0 * forkAut a b c d j :
      MulAut (Multiplicative (Fin k → ZMod p))) = 3) ∧
    (∀ j j', j ≠ 0 → j' ≠ 0 → j ≠ j' → orderOf (forkAut a b c d j * forkAut a b c d j' :
      MulAut (Multiplicative (Fin k → ZMod p))) = 2) := by
  have hinj := forkAut_injective hp hp2 hab hac had hbc hbd hcd
  have hsq : ∀ j, (forkAut a b c d j : MulAut (Multiplicative (Fin k → ZMod p))) ^ 2 = 1 :=
    fun j => (forkAut_sq_card hp hab hbc hcd j).1
  refine ⟨fun j hj => ?_, fun j j' hj hj' hjj' => ?_⟩
  · have hne : (forkAut a b c d 0 : MulAut (Multiplicative (Fin k → ZMod p))) ≠
        forkAut a b c d j := fun h => hj (hinj h).symm
    refine orderOf_mul_eq_three_of_braid (hsq 0) (hsq j) hne ?_
    fin_cases j
    · exact absurd rfl hj
    · exact (swapAut_braid hab hbc hac).symm
    · exact swapAut_braid hbc hcd hbd
    · exact swapAut_antiSwapAut_braid hbc hcd hbd
  · have hne : (forkAut a b c d j : MulAut (Multiplicative (Fin k → ZMod p))) ≠
        forkAut a b c d j' := fun h => hjj' (hinj h)
    refine orderOf_mul_eq_two_of_commute (hsq j) (hsq j') hne ?_
    clear hjj' hne
    fin_cases j
    · exact absurd rfl hj
    · fin_cases j'
      · exact absurd rfl hj'
      · rfl
      · exact swapAut_comm_of_disjoint hac had hbc hbd
      · exact swapAut_antiSwapAut_comm_of_disjoint hcd hac had hbc hbd
    · fin_cases j'
      · exact absurd rfl hj'
      · exact (swapAut_comm_of_disjoint hac had hbc hbd).symm
      · rfl
      · exact swapAut_antiSwapAut_comm hcd
    · fin_cases j'
      · exact absurd rfl hj'
      · exact (swapAut_antiSwapAut_comm_of_disjoint hcd hac had hbc hbd).symm
      · exact (swapAut_antiSwapAut_comm hcd).symm
      · rfl

end EnnolaFork

theorem ggTorusForkEltSC_of_evenSignedPermEltSC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] {kP : ℕ → Prop} (hk : ∀ k, kP k → 4 ≤ k) (h : GGTorusEvenSignedPermEltSC p R kP) :
    GGTorusForkEltSC p R := by
  intro E hE h3 hsc
  obtain ⟨k, τ, hτinj, hτE, hkP, hd, hP, -⟩ := h E hE h3 hsc
  have hk4 : 4 ≤ k := hk k hkP
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  let c : Fin k := ⟨2, by omega⟩
  let d : Fin k := ⟨3, by omega⟩
  have hab : a ≠ b := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by norm_num)
  have hac : a ≠ c := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by norm_num)
  have had : a ≠ d := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 3 by norm_num)
  have hbc : b ≠ c := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 by norm_num)
  have hbd : b ≠ d := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 3 by norm_num)
  have hcd : c ≠ d := Fin.ne_of_val_ne (show (2 : ℕ) ≠ 3 by norm_num)
  let e := MulEquiv.funMultiplicative (Fin k) (ZMod p)
  let τ' : Multiplicative (Fin k → ZMod p) →* R := τ.comp e.toMonoidHom
  have hτ'inj : Function.Injective τ' := hτinj.comp e.injective
  have hτ'range : τ'.range = E := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [← hτE]
      exact ⟨e x, rfl⟩
    · intro y hy
      have hy' : y ∈ τ.range := hτE ▸ hy
      obtain ⟨z, rfl⟩ := hy'
      refine ⟨e.symm z, ?_⟩
      show τ (e (e.symm z)) = τ z
      rw [MulEquiv.apply_symm_apply]
  refine ⟨k, τ', hτ'inj, hτ'range, EnnolaFork.forkAut a b c d,
    fun j => EnnolaFork.forkAut_induced τ hd hP a b c d hcd j,
    EnnolaFork.forkAut_sq_card hp hab hbc hcd,
    EnnolaFork.forkAut_orders hp hp2 hab hac had hbc hbd hcd⟩

theorem ggRowFork_EOmM :
    GGRowFork ggRowP_EOmM := by
  intro p hp hp2 lab _ h
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  obtain ⟨htag, hl, hlo, hpn⟩ := h
  dsimp only at htag hl hlo hpn ⊢
  subst htag
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hm : 4 ≤ l - 1 := by omega
    have hme : Even (l - 1) := by
      obtain ⟨k, hk⟩ := hlo
      exact ⟨k, by omega⟩
    have hpK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpn
    obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ l - 1) hbc
    refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', l - 1,
      ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hbc, ?_⟩
    exact ggTorusFork_of_forkEltSC hp hp2 hZ (fun φ hφ _ => hφ) hcp
      (ggTorusForkEltSC_of_evenSignedPermEltSC hp hp2 (kP := fun k => k = l - 1 + 1)
        (fun k hk => by omega)
        (ggOrthEvenTorusInput_holds.2 K (l - 1) p b c hm hme hbc hp hpK))

theorem ggRowFork_EOmP :
    GGRowFork ggRowP_EOmP := by
  intro p hp hp2 lab hlab h
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨htag, hl, hle, hpn⟩ := h
  dsimp only at htag hl hle hpn ⊢
  subst htag
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hpK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpn
    obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
    have hlift : ∃ r, GGTorusLift p r (OrthRest.RPlus K l) := by
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · obtain rfl : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hn2) hn
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpn)
        subst hp3
        exact ⟨l - 1, ggOrthRestTorusLiftInput_holds.2 K l (by rw [hK]; norm_num) (by omega)⟩
      · have hK4 : 4 ≤ Nat.card K := by
          rw [hK]
          exact (Nat.pow_le_pow_right (by norm_num) hn2 : 2 ^ 2 ≤ 2 ^ n)
        exact ⟨3, TableBSymp.ggTorusLift_omegaPlusNs hp hp2 hpK hK4 (by omega)⟩
    obtain ⟨r, hr⟩ := hlift
    refine ⟨K, inferInstance, inferInstance, hK, hQ', r, hr, ?_⟩
    exact ggTorusFork_of_forkEltSC hp hp2 hZ (fun φ hφ _ => hφ) hcp
      (ggTorusForkEltSC_of_evenSignedPermEltSC hp hp2 (kP := fun k => k = l)
        (fun k hk => by omega)
        (ggOrthEvenTorusInput_holds.1 K l p hl hp (Or.inr ⟨hle, hpK⟩)))

end CFSG.StandardType

end
