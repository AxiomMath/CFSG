module

public import CFSG.RankThree.PartOne.KS.ONCores
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.SteinbergCBONOuterPrimes

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.RankThree.Native
open CFSG.ONSchreier (Pv onEquivPv)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

@[expose] def ONPointwiseSeven : Prop :=
  ∀ α : MulAut Pv, (∀ g : Pv,
    (g : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈ onSevenC 0 → α g = g) → α ^ 7 = 1

@[expose] noncomputable def onSevenX0 : Pv := ⟨onSevenLine (onSevenRep 0), onSeven_mem_P.2.1 _⟩

theorem onSevenX0_ne_one : onSevenX0 ≠ 1 := fun h =>
  onSevenLine_ne_one (onSevenRep 0) (congrArg Subtype.val h)

theorem exists_conj_onSevenX0_mem {E₁ : Subgroup Pv} (hcard : Nat.card E₁ = 7 ^ 2)
    (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a) : ∃ g : Pv, g * onSevenX0 * g⁻¹ ∈ E₁ := by
  have hp : Nat.Prime 7 := by norm_num
  obtain ⟨-, -, hC, hlow, -, -, -⟩ := R3E_ON_full_seven_centralizer_structures
  obtain ⟨-, hFC', -, hFcard, hcent', hYcard'⟩ := hlow 0
  have hFC : onSevenF 0 ≤ onSevenC 0 := hFC'
  have hcent : centralizer ((onSevenF 0 : Subgroup (Equiv.Perm (Fin CFSG.ONSchreier.N))) :
      Set (Equiv.Perm (Fin CFSG.ONSchreier.N))) ⊓ onSevenC 0 ≤ onSevenF 0 := hcent'
  have hYcard : Nat.card ↥(centralizer ((onSevenF 0 : Subgroup
      (Equiv.Perm (Fin CFSG.ONSchreier.N))) : Set (Equiv.Perm (Fin CFSG.ONSchreier.N))) ⊓
      onSevenC 0) = 7 := hYcard'
  have hC0 : onSevenC 0 =
      centralizer ({onSevenLine (onSevenRep 0)} : Set (Equiv.Perm (Fin CFSG.ONSchreier.N))) ⊓
        Pv := hC 0
  have hFP : onSevenF 0 ≤ Pv := onSeven_mem_P.2.2.2.1 0
  have hxF : ∀ f ∈ onSevenF 0,
      f * onSevenLine (onSevenRep 0) = onSevenLine (onSevenRep 0) * f := fun f hf => by
    have := hFC hf
    rw [hC0] at this
    exact mem_centralizer_singleton_iff.1 this.1
  have hxC : onSevenLine (onSevenRep 0) ∈ onSevenC 0 := by
    rw [hC0]
    exact ⟨mem_centralizer_singleton_iff.2 rfl, onSeven_mem_P.2.1 _⟩
  have hxmemF : onSevenLine (onSevenRep 0) ∈ onSevenF 0 :=
    hcent ⟨mem_centralizer_iff.2 fun f hf => hxF f hf, hxC⟩
  set F : Subgroup Pv := (onSevenF 0).subgroupOf Pv with hF
  have hFcard' : Nat.card F = 7 ^ 3 := by
    rw [hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv, hFcard]
    norm_num
  have hnab : ∃ f₁ ∈ F, ∃ f₂ ∈ F, f₁ * f₂ ≠ f₂ * f₁ := by
    by_contra hab
    push Not at hab
    have hle : onSevenF 0 ≤ centralizer ((onSevenF 0 : Subgroup _) : Set _) ⊓ onSevenC 0 := by
      refine le_inf ?_ hFC
      intro f hf
      rw [mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (hab ⟨g, hFP hg⟩ hg ⟨f, hFP hf⟩ hf)
    have := Subgroup.card_le_of_le hle
    rw [hFcard, hYcard] at this
    omega
  have hSyl : Nat.card F = 7 ^ (Nat.card Pv).factorization 7 := by
    rw [hFcard', factorization_card_Pv_seven]
  exact exists_conj_mem_of_central_of_abelian_sq hp hFcard' hSyl hcard hcomm
    (z := onSevenX0) hxmemF (fun f hf => Subtype.ext (hxF f hf).symm) hnab

theorem almostSimplePlaneOdd_seven_ONan (hin : ONPointwiseSeven) :
    AlmostSimplePlaneOdd 7 (Carrier .ONan) := by
  intro H _ _ K _ hK hCK E hE hEcard t htE ht1
  have hp : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp⟩
  obtain ⟨e⟩ := hK
  let φ : K ≃* Pv := e.trans onEquivPv
  have hOut : ¬ 7 ∣ Nat.card (Outer K) := by
    intro hd
    let e' : Outer K ≃* Outer CFSG.Blueprint.NativeSporadic.ON :=
      CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
    rw [Nat.card_congr e'.toEquiv] at hd
    rcases CFSG.Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent 7 hp hd with
      h | h <;> omega
  have hord : ∀ a ∈ E, a ≠ 1 → orderOf a = 7 := fun a ha ha1 =>
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hEK : E ≤ K := fun a ha => mem_of_pow_eq_one_of_not_dvd_card_outer hp hCK hOut
    (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hcen : ∀ a ∈ E, a ≠ 1 →
      (∀ x ∈ inSubgroup (aschbacherSolvableCore 7) (centralizer ({a} : Set H)),
        x ∈ K → x = 1) ∧
      ∀ x ∈ inSubgroup (aschbacherSolvableCore 7) (centralizer ({a} : Set H)),
        ∀ y ∈ K, y * a = a * y → x * y = y * x := fun a ha ha1 =>
    inf_core_centralizes_of_inner_core_bot hp K (hEK ha)
      (onSeven_core_bot_of_equiv φ (by rw [Subgroup.orderOf_mk]; exact hord a ha ha1))
  have hS : ⁅inSubgroup (aschbacherSolvableCore 7) (centralizer ({t} : Set H)), E⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    have hxy := (hcen t htE ht1).2 x hx y (hEK hy)
      (congrArg Subtype.val (hE.is_comm.comm ⟨y, hy⟩ ⟨t, htE⟩))
    rw [Subgroup.mem_bot, commutatorElement_def, hxy]
    group
  have hI : thetaT 7 E = ⊥ := by
    obtain ⟨-, -, hC, -⟩ := R3E_ON_full_seven_centralizer_structures
    set E₁ : Subgroup Pv := (E.subgroupOf K).map φ.toMonoidHom with hE₁
    have hE₁card : Nat.card E₁ = 7 ^ 2 := by
      rw [hE₁, Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hEcard]
    have hE₁comm : ∀ u ∈ E₁, ∀ v ∈ E₁, u * v = v * u := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      have hab : (a : H) * (b : H) = (b : H) * (a : H) :=
        congrArg Subtype.val (hE.is_comm.comm ⟨(a : H), ha⟩ ⟨(b : H), hb⟩)
      exact congrArg φ (Subtype.ext hab)
    obtain ⟨g, a, haE, hφa⟩ := exists_conj_onSevenX0_mem hE₁card hE₁comm
    have haE' : (a : H) ∈ E := haE
    have ha1 : (a : H) ≠ 1 := by
      intro h1
      have h2 : g * onSevenX0 * g⁻¹ = 1 := by
        rw [← hφa, show a = 1 from Subtype.ext h1, map_one]
      apply onSevenX0_ne_one
      calc onSevenX0 = g⁻¹ * (g * onSevenX0 * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    rw [eq_bot_iff]
    intro h' hh'
    rw [Subgroup.mem_bot]
    have hh'A : ∀ b ∈ E, b ≠ 1 →
        h' ∈ inSubgroup (aschbacherSolvableCore 7) (centralizer ({b} : Set H)) := fun b hb hb1 =>
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh' b) hb) hb1
    have hpow : h' ^ 7 = 1 := by
      refine pow_eq_one_of_centralizes_of_exists_conj hCK φ
        (S := {c : Pv | (c : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈ onSevenC 0})
        (x := onSevenX0) ?_ hin (a := a) (g := g) hφa ?_
      · intro c hc
        have hc' : (c : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈
            centralizer ({onSevenLine (onSevenRep 0)} : Set (Equiv.Perm (Fin CFSG.ONSchreier.N)))
              ⊓ Pv := by
          rw [← hC 0]
          exact hc
        exact Subtype.ext (mem_centralizer_singleton_iff.1 hc'.1)
      · intro k hk
        exact (hcen (a : H) haE' ha1).2 h' (hh'A _ haE' ha1) k k.2 (congrArg Subtype.val hk)
    by_contra hne
    have hord7 : orderOf h' = 7 := orderOf_eq_prime hpow hne
    have hA := hh'A t htE ht1
    have hdvd := orderOf_dvd_natCard
      (⟨h', hA⟩ : inSubgroup (aschbacherSolvableCore 7) (centralizer ({t} : Set H)))
    rw [Subgroup.orderOf_mk, hord7] at hdvd
    exact not_dvd_card_inSubgroup_aschbacherSolvableCore hp _ hdvd
  have hW : localCoreProduct 7 E t = ⊥ := by
    rw [localCoreProduct, hS, hI, sup_bot_eq]
  rw [hW, Subgroup.card_bot]
  omega

theorem card_ON_eq_card_Pv : Nat.card CFSG.Blueprint.NativeSporadic.ON = 460815505920 := by
  rw [Nat.card_congr onEquivPv.toEquiv]
  exact CFSG.ONSchreier.card_Pv

theorem not_sq_dvd_card_ON {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 460815505920 := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 9 * 3 ^ 4 * 7 ^ 3) := by
    refine Nat.Coprime.pow_left 2 ?_
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
    have h7 : Nat.Coprime p 7 := (Nat.coprime_primes hp (by norm_num)).mpr hp7
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right 9 h2)
      (Nat.Coprime.pow_right 4 h3)) (Nat.Coprime.pow_right 3 h7)
  have h' : p ^ 2 ∣ 32395 := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [show 2 ^ 9 * 3 ^ 4 * 7 ^ 3 * 32395 = 460815505920 by norm_num]
    exact h
  have h1 : p ∣ 5 * 11 * 19 * 31 := (dvd_pow_self p two_ne_zero).trans h'
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h4
        subst this
        norm_num at h'
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h4
        subst this
        norm_num at h'
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3
      subst this
      norm_num at h'
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2
    subst this
    norm_num at h'

theorem sporadicPlaneOdd_ONan (hin : ONPointwiseSeven) : SporadicPlaneOdd (Carrier .ONan) := by
  refine sporadicPlaneOdd_of_almostSimple {7} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_seven_ONan hin
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp7 : p ≠ 7 := fun h => hpS (by simp [h])
    have hc : center T = ⊥ := center_eq_bot_of_simple hnab
    rw [card_mulAut_eq_mul_card_outer hc]
    have hT : Nat.card T = 460815505920 := (Nat.card_congr e.toEquiv).trans card_ON_eq_card_Pv
    have hout : ¬ p ∣ Nat.card (Outer T) := by
      intro hd
      let e' : Outer T ≃* Outer CFSG.Blueprint.NativeSporadic.ON :=
        CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
      rw [Nat.card_congr e'.toEquiv] at hd
      rcases CFSG.Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent p hp hd with
        h | h <;> omega
    have hcop : Nat.Coprime (p ^ 2) (Nat.card (Outer T)) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hout)
    intro hdvd
    rw [hT] at hdvd
    exact not_sq_dvd_card_ON hp hp3 hp7 (hcop.dvd_of_dvd_mul_right hdvd)

end CFSG.RankThree.PartOne
