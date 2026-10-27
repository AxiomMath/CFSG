module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryLift
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.LieType.Steinberg.CentralExt.UnitaryTwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.SectionRank.OddCover CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

@[expose] def ggUnitaryTorusRank (p d : ℕ) : ℕ :=
  if p ∣ d then d - 3 else d - 2

namespace TableBU

section Generators

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def torusGen (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) (j : Fin m) : Fin d → Kˣ :=
  (Pi.mulSingle (⟨0, by omega⟩ : Fin d) ζ : Fin d → Kˣ) *
    (Pi.mulSingle (⟨1, by omega⟩ : Fin d) ζ : Fin d → Kˣ) *
    (Pi.mulSingle (⟨j + 2, by omega⟩ : Fin d) (ζ⁻¹ ^ 2) : Fin d → Kˣ)

theorem torusGen_apply (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) (j : Fin m) (i : Fin d) :
    torusGen ζ hm j i = (if (i : ℕ) = 0 then ζ else 1) * (if (i : ℕ) = 1 then ζ else 1) *
      (if (i : ℕ) = j + 2 then ζ⁻¹ ^ 2 else 1) := by
  simp only [torusGen, Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff]

theorem torusGen_zero (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) (j : Fin m) :
    torusGen ζ hm j ⟨0, by omega⟩ = ζ := by
  rw [torusGen_apply]
  simp

theorem torusGen_one (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) (j : Fin m) :
    torusGen ζ hm j ⟨1, by omega⟩ = ζ := by
  rw [torusGen_apply]
  simp

theorem torusGen_self (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) (j : Fin m) :
    torusGen ζ hm j ⟨j + 2, by omega⟩ = ζ⁻¹ ^ 2 := by
  rw [torusGen_apply]
  simp

theorem torusGen_other (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) {j j' : Fin m} (h : j' ≠ j) :
    torusGen ζ hm j' ⟨j + 2, by omega⟩ = 1 := by
  have hjj : (j : ℕ) ≠ j' := fun h' => h (Fin.ext h'.symm)
  rw [torusGen_apply]
  simp [hjj]

theorem torusGen_last (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) (hm3 : m + 3 ≤ d) (j : Fin m) :
    torusGen ζ hm j ⟨d - 1, by omega⟩ = 1 := by
  have hj := j.2
  rw [torusGen_apply]
  have h0 : d - 1 ≠ 0 := by omega
  have h1 : d - 1 ≠ 1 := by omega
  have h2 : d - 1 ≠ j + 2 := by omega
  simp [h0, h1, h2]

theorem torusGen_pow {ζ : Kˣ} {k : ℕ} (hζ : ζ ^ k = 1) {m : ℕ} (hm : m + 2 ≤ d) (j : Fin m)
    (i : Fin d) : torusGen ζ hm j i ^ k = 1 := by
  rw [torusGen_apply, mul_pow, mul_pow]
  have h3 : (ζ ^ 2) ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  split_ifs <;> simp [hζ, h3]

theorem prod_torusGen (ζ : Kˣ) {m : ℕ} (hm : m + 2 ≤ d) (j : Fin m) :
    ∏ i, torusGen ζ hm j i = 1 := by
  simp only [torusGen, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
  group

end Generators

section Model

variable {K : Type} [Field K] {d : ℕ}

theorem diagHom_eq_of_mem_center {t : Fin d → Kˣ}
    (ht : diagHom d t ∈ Subgroup.center (GL (Fin d) K))
    (i j : Fin d) : t i = t j := by
  have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) t
  rw [Subgroup.mem_center_iff.mp ht, mul_inv_cancel_right] at h1
  have h2 := congrFun (diagHom_injective d h1) i
  rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h2
  exact h2

theorem permGL_swap_not_mem_center {i j : Fin d} (hij : i ≠ j) {ζ : Kˣ} (hζ : ζ ≠ 1) :
    (permGL (Equiv.swap i j) : GL (Fin d) K) ∉ Subgroup.center (GL (Fin d) K) := by
  intro h
  have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) (Pi.mulSingle i ζ)
  rw [(Subgroup.mem_center_iff.mp h _).symm, mul_inv_cancel_right] at h1
  have h2 := congrFun (diagHom_injective d h1) j
  rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne hij.symm] at h2
  exact hζ h2.symm

end Model

theorem unitaryFieldData_of_card {K : Type} [Field K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) : UnitaryFieldData 2 n K :=
  ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩

theorem ne_two_of_dvd_two_pow_add_one {p n : ℕ} (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h3 := (Nat.dvd_add_right h2).mp hpq
  norm_num at h3

end TableBU

open TableBU

section Lift

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem ggTorusLift_unitary
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) :
    GGTorusLift p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKd : UnitaryFieldData 2 n K := unitaryFieldData_of_card hK hn
  have : CharP K 2 := hKd.charP
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_add_one hn hpq
  set H := LargeEvenSUGroup (Fin d) K (2 ^ n) with hH
  set m := ggUnitaryTorusRank p d with hmdef
  have hm : m + 2 ≤ d := by
    simp only [hmdef, ggUnitaryTorusRank]
    split_ifs <;> omega
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hKd hp hpq
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  set c := torusGen ζ hm with hc
  have hcp : ∀ j i, c j i ^ p = 1 := fun j i => torusGen_pow hζp hm j i
  have hcprod : ∀ j, ∏ i, c j i = 1 := fun j => prod_torusGen ζ hm j
  have hcnorm : ∀ j i, c j i ^ (2 ^ n + 1) = 1 := fun j i => torusGen_pow hζq hm j i
  have hmemH : ∀ a, diagHom d (expHom c hcp a) ∈ H := fun a =>
    diagHom_expHom_mem_unitarySU hKd c hcp hcprod hcnorm a
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
    intro j
    refine ⟨⟨j + 2, by omega⟩, fun j' hj' => torusGen_other ζ hm hj', ?_⟩
    rw [hc, torusGen_self, Nat.Coprime.orderOf_pow, orderOf_inv, hζo]
    rw [orderOf_inv, hζo]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hexpinj := expHom_injective c hcp hpriv
  set φ : Multiplicative (Fin m → ZMod p) →* H :=
    ((diagHom d).comp (expHom c hcp)).codRestrict H hmemH with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : diagHom d (expHom c hcp a) = diagHom d (expHom c hcp b) := congrArg Subtype.val hab
    exact hexpinj (diagHom_injective d h1)
  set E₀ := φ.range with hE₀
  have hE₀card : Nat.card E₀ = p ^ m := by
    rw [hE₀, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hapow : ∀ a : Multiplicative (Fin m → ZMod p), a ^ p = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    simp [Pi.smul_apply, nsmul_eq_mul]
  have hE₀ab : IsElemAbelian p E₀ := isElemAbelian_range (fun a b => mul_comm a b) hapow φ
  set q := LargeEvenProjMk H with hq
  have hkerq : q.ker = (LargeEvenScalars (Fin d) K).subgroupOf H := QuotientGroup.ker_mk' _
  have hscal : ∀ x : H, x ∈ q.ker → (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
    intro x hx
    rw [hkerq, Subgroup.mem_subgroupOf] at hx
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  have hE₀q : E₀ ⊓ q.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, hx⟩
    have hcen : diagHom d (expHom c hcp a) ∈ Subgroup.center (GL (Fin d) K) := hscal _ hx
    have htc := diagHom_eq_of_mem_center hcen
    have htp : ∀ i, expHom c hcp a i ^ p = 1 := by
      intro i
      have h1 : expHom c hcp a ^ p = 1 := by rw [← map_pow, hapow, map_one]
      exact congrFun h1 i
    have ht1 : expHom c hcp a = 1 := by
      have hlast : ∃ u, u = 1 ∧ ∀ i, expHom c hcp a i = u := by
        by_cases hpd : p ∣ d
        · have hm3 : m + 3 ≤ d := by
            simp only [hmdef, ggUnitaryTorusRank, hpd, ite_true]
            omega
          refine ⟨expHom c hcp a ⟨d - 1, by omega⟩, ?_, fun i => htc _ _⟩
          rw [expHom_apply]
          exact Finset.prod_eq_one fun j _ => by
            rw [show c j ⟨d - 1, by omega⟩ = 1 from torusGen_last ζ hm hm3 j, one_pow]
        · refine ⟨expHom c hcp a ⟨0, by omega⟩, ?_, fun i => htc _ _⟩
          set u := expHom c hcp a ⟨0, by omega⟩ with hu
          have hdet := ((mem_unitarySU_iff hKd).mp (hmemH a)).1
          rw [det_diagHom] at hdet
          have hud : u ^ d = 1 := by
            apply Units.ext
            rw [Units.val_pow_eq_pow_val, Units.val_one, ← hdet]
            rw [Finset.prod_congr rfl fun i _ => congrArg Units.val (htc i ⟨0, by omega⟩),
              Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have hcop : Nat.gcd d p = 1 :=
            Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
          have h1 := pow_gcd_eq_one.mpr ⟨hud, htp ⟨0, by omega⟩⟩
          rwa [hcop, pow_one] at h1
      obtain ⟨u, hu1, hu⟩ := hlast
      funext i
      rw [hu i, hu1]
      rfl
    have ha1 : a = 1 := hexpinj (by rw [ht1, map_one])
    rw [ha1, map_one]
    exact Subgroup.one_mem _
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hwH : (permGL (Equiv.swap i0 i1) : GL (Fin d) K) ∈ H := by
    rw [show H = unitarySU 2 n K d from rfl, mem_unitarySU_iff hKd]
    refine ⟨?_, permGL_unitary hKd _⟩
    rw [det_permGL, Equiv.Perm.sign_swap hi01]
    have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    linear_combination -h2K
  set w : H := ⟨_, hwH⟩ with hw
  have hw2 : w ^ 2 = 1 := Subtype.ext (by
    show (permGL (Equiv.swap i0 i1) : GL (Fin d) K) ^ 2 = 1
    rw [← map_pow, sq, Equiv.swap_mul_self, map_one])
  set U₀ := Subgroup.zpowers w with hU₀def
  have hU₀ : IsPGroup 2 U₀ := isPGroup_two_zpowers (k := 1) (by rw [pow_one]; exact hw2)
  have hU₀q : ¬ U₀ ≤ q.ker := by
    intro h
    exact permGL_swap_not_mem_center hi01 hζ1 (hscal w (h (Subgroup.mem_zpowers w)))
  have hc0 : ∀ j, c j i0 = ζ := fun j => torusGen_zero ζ hm j
  have hc1 : ∀ j, c j i1 = ζ := fun j => torusGen_one ζ hm j
  have hEU : E₀ ≤ Subgroup.normalizer (U₀ : Set H) := by
    rintro _ ⟨a, rfl⟩
    set t := expHom c hcp a with ht
    have ht01 : t i0 = t i1 := by
      rw [ht, expHom_apply, expHom_apply]
      exact Finset.prod_congr rfl fun j _ => by rw [hc0, hc1]
    have hts : t ∘ (Equiv.swap i0 i1).symm = t := by
      funext i
      rw [Function.comp_apply, Equiv.symm_swap]
      by_cases h0 : i = i0
      · rw [h0, Equiv.swap_apply_left, ht01]
      · by_cases h1 : i = i1
        · rw [h1, Equiv.swap_apply_right, ht01]
        · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    have hcomm : w * φ a = φ a * w := by
      apply Subtype.ext
      show permGL (Equiv.swap i0 i1) * diagHom d t = diagHom d t * permGL (Equiv.swap i0 i1)
      have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i0 i1) t
      rw [hts] at h1
      calc (permGL (Equiv.swap i0 i1) : GL (Fin d) K) * diagHom d t
          = permGL (Equiv.swap i0 i1) * diagHom d t * (permGL (Equiv.swap i0 i1))⁻¹ *
              permGL (Equiv.swap i0 i1) := by group
        _ = diagHom d t * permGL (Equiv.swap i0 i1) := by rw [h1]
    have hconj : ∀ k : ℤ, φ a * w ^ k * (φ a)⁻¹ = w ^ k := by
      intro k
      have hk : Commute (φ a) (w ^ k) := (Commute.zpow_right hcomm.symm k)
      rw [hk.eq, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [hconj]
      exact Subgroup.zpow_mem_zpowers w k
    · rintro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have : h = w ^ k := by
        have h2 := hconj k
        rw [hk] at h2
        calc h = (φ a)⁻¹ * (φ a * h * (φ a)⁻¹) * φ a := by group
          _ = (φ a)⁻¹ * (φ a * w ^ k * (φ a)⁻¹) * φ a := by rw [← h2, hk]
          _ = w ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem_zpowers w k
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen hC
    by_cases he : Even d
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
        (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn hd he hdq hπ hcen
  intro L _ _ ψ hψ hker _
  obtain ⟨U, E, hU, hU2, hEU', hEab, hEc, hEk⟩ :=
    exists_lift_of_section q hsplit hp hp2 hE₀ab hE₀q hU₀ hU₀q hEU ψ hψ hker
  exact ⟨U, E, hU, hU2, hEU', hEab, hEc.trans hE₀card, hEk⟩

end Lift

section Labels

theorem dvd_of_largeEvenSplit_twA {p : ℕ} {lab : LargeEvenLabel} (hs : LargeEvenSplit p lab)
    (htag : lab.tag = .twA) : p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨hn, rfl⟩
  · exact absurd h id
  · exact h
  · rcases h with h | h <;> exact absurd h (fun h' => by cases h')
  · dsimp only at hn ⊢
    rw [hn]
    norm_num

theorem largeEvenLabelAll_torusLift_twA
    {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twA) (hp : p.Prime)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (ggUnitaryTorusRank p (lab.rank + 1)) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpq ⊢
  subst htag
  obtain ⟨hn, hl, hl2⟩ := hlab
  dsimp only at hn hl hl2
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have h3 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hl2 (by omega))
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, ggTorusLift_unitary hK hn (by omega) hdq hp hpq⟩

theorem largeEvenLabelAll_torusLift_twD3
    {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twD) (hl : lab.rank = 3) (hp : p.Prime)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (ggUnitaryTorusRank p 4) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpq ⊢
  subst htag hl
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  have hdq : (4, 2 ^ n) ≠ (3, 2) := fun h => absurd (congrArg Prod.fst h) (by norm_num)
  exact ⟨K, i1, i2, hK, hq, ggTorusLift_unitary hK hn (by norm_num) hdq hp hpq⟩

end Labels

end CFSG.StandardType
