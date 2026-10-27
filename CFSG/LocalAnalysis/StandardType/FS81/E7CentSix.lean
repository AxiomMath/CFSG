module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.StandardType.FS81.L3TwoFixedPointFree
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.ClosurePairInvert
public import CFSG.RankThree.PartOne.MB3.FixedPoint
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

private lemma isSolvable_of_fixedPointFree_three {X : Type} [Group X] [Finite X]
    (α : MulAut X) (hα : orderOf α = 3) (hfix : ∀ x, α x = x → x = 1) : IsSolvable X := by
  have hnil : Group.IsNilpotent X :=
    CFSG.RankThree.PartOne.MB3.isNilpotent_of_fixedPointFree_prime α
      (show Nat.Prime (orderOf α) by rw [hα]; exact Nat.prime_three) hfix
  haveI := hnil
  exact IsNilpotent.to_isSolvable

private lemma exists_normalizer_lt_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hX : IsPGroup p X) {H : Subgroup X} (hH : H ≠ ⊤) :
    ∃ x ∈ Subgroup.normalizer (H : Set X), x ∉ H := by
  haveI : Group.IsNilpotent X := IsPGroup.isNilpotent hX
  have hnc : NormalizerCondition X := Group.normalizerCondition_of_isNilpotent
  have hNne : Subgroup.normalizer (H : Set X) ≠ H := by
    intro heq
    exact hH ((normalizerCondition_iff_only_full_group_self_normalizing.mp hnc H heq))
  have hlt : H < Subgroup.normalizer (H : Set X) :=
    lt_of_le_of_ne Subgroup.le_normalizer hNne.symm
  exact SetLike.exists_of_lt hlt

private lemma six_normalizers {G : Type} [Group G] {M P : Subgroup G} {k : G}
    (hPM : P ≤ Subgroup.normalizer (M : Set G)) (hPk : ∀ p ∈ P, p * k = k * p) :
    (M ⊓ Subgroup.centralizer ({k} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers k : Set G)) ∧
      (P ≤ Subgroup.normalizer (Subgroup.zpowers k : Set G)) ∧
      (P ≤ Subgroup.normalizer
        ((M ⊓ Subgroup.centralizer ({k} : Set G) : Subgroup G) : Set G)) := by
  have hCeq : Subgroup.centralizer ({k} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers k : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hzk : Subgroup.centralizer (Subgroup.zpowers k : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers k : Set G) :=
    Subgroup.centralizer_le_normalizer (Subgroup.zpowers k : Set G)
  have hTnorm : M ⊓ Subgroup.centralizer ({k} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers k : Set G) := by
    refine le_trans ?_ hzk
    rw [← hCeq]
    exact fun x hx => hx.2
  have hPT₀ : P ≤ Subgroup.normalizer (Subgroup.zpowers k : Set G) := by
    refine le_trans ?_ hzk
    rw [← hCeq]
    exact fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hPk p hp)
  have hPC : P ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({k} : Set G) : Subgroup G) : Set G) :=
    le_trans (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hPk p hp))
      Subgroup.le_normalizer
  have hPT : P ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer ({k} : Set G) : Subgroup G) : Set G) :=
    le_trans (le_inf hPM hPC) Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨hTnorm, hPT₀, hPT⟩

private lemma six_coset_fixed {G : Type} [Group G] [Finite G] {P : Subgroup G} {b₁ k t : G}
    (hk : orderOf k = 2) (hb₁P : b₁ ∈ P) (hb₁ : orderOf b₁ = 3)
    (hPk : ∀ p ∈ P, p * k = k * p)
    (htN : t ∈ Subgroup.normalizer (Subgroup.zpowers k : Set G))
    (hmem : b₁ * t * b₁⁻¹ * t⁻¹ ∈ Subgroup.zpowers k) :
    ∃ n ∈ Subgroup.zpowers k, b₁ * (t * n) * b₁⁻¹ = t * n := by
  have htinvN : t⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers k : Set G) :=
    (Subgroup.normalizer (Subgroup.zpowers k : Set G)).inv_mem htN
  have hcoset : t⁻¹ * (b₁ * t * b₁⁻¹) ∈ Subgroup.zpowers k := by
    have h := (Subgroup.mem_normalizer_iff.mp htinvN (b₁ * t * b₁⁻¹ * t⁻¹)).mp hmem
    rwa [show t⁻¹ * (b₁ * t * b₁⁻¹ * t⁻¹) * (t⁻¹)⁻¹ =
      t⁻¹ * (b₁ * t * b₁⁻¹) by group] at h
  have hT₀Cb₁ : Subgroup.zpowers k ≤ Subgroup.centralizer ({b₁} : Set G) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (hPk b₁ hb₁P).symm)
  have hN : ∀ n ∈ Subgroup.zpowers k, b₁ * n * b₁⁻¹ ∈ Subgroup.zpowers k := by
    intro n hn
    have hcomm : n * b₁ = b₁ * n :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT₀Cb₁ hn)
    have heq : b₁ * n * b₁⁻¹ = n := by
      rw [← hcomm]
      group
    rw [heq]
    exact hn
  have hcop : Nat.Coprime (orderOf b₁) (Nat.card (Subgroup.zpowers k)) := by
    rw [hb₁, Nat.card_zpowers, hk]
    decide
  exact CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (Subgroup.zpowers k) hN hcoset hcop

private lemma six_fix {G : Type} [Group G] [Finite G] {M P : Subgroup G} {b k b₁ : G}
    (hkM : k ∈ M) (hb : orderOf b = 3) (hk : orderOf k = 2)
    (hbk : k * b * k⁻¹ = b⁻¹) (hb₁P : b₁ ∈ P) (hb₁ : orderOf b₁ = 3)
    (hPk : ∀ p ∈ P, p * k = k * p)
    (hCb₁ : ∀ m ∈ M, m * b₁ = b₁ * m → m ∈ Subgroup.closure ({b, k} : Set G))
    (hTnorm : M ⊓ Subgroup.centralizer ({k} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers k : Set G)) :
    ∀ t ∈ M ⊓ Subgroup.centralizer ({k} : Set G),
      b₁ * t * b₁⁻¹ * t⁻¹ ∈ Subgroup.zpowers k → t ∈ Subgroup.zpowers k := by
  intro t ht hmem
  obtain ⟨n, hnT₀, hfixn⟩ := six_coset_fixed hk hb₁P hb₁ hPk (hTnorm ht) hmem
  have hnM : n ∈ M := Subgroup.zpowers_le.mpr hkM hnT₀
  have htnM : t * n ∈ M := M.mul_mem ht.1 hnM
  have htk : k ∈ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htnC : t * n ∈ Subgroup.centralizer ({k} : Set G) :=
    (Subgroup.centralizer ({k} : Set G)).mul_mem ht.2
      ((Subgroup.zpowers_le.mpr htk) hnT₀)
  have htncomm : (t * n) * b₁ = b₁ * (t * n) := by
    have h := congrArg (· * b₁) hfixn
    have h' : b₁ * (t * n) = (t * n) * b₁ := by simpa using h
    exact h'.symm
  have htnD : t * n ∈ Subgroup.closure ({b, k} : Set G) := hCb₁ (t * n) htnM htncomm
  have hk2' : k * k = 1 := by
    rw [← pow_two, ← hk]
    exact pow_orderOf_eq_one k
  have hodd : Odd (orderOf b) := by
    rw [hb]
    decide
  have htnT₀ : t * n ∈ Subgroup.zpowers k :=
    CFSG.GroupTheory.mem_zpowers_right_of_mem_closure_pair_of_conj_eq_inv hk2' hbk hodd htnD
      (Subgroup.mem_centralizer_singleton_iff.mp htnC)
  have ht_eq : t = (t * n) * n⁻¹ := by group
  rw [ht_eq]
  exact (Subgroup.zpowers k).mul_mem htnT₀ ((Subgroup.zpowers k).inv_mem hnT₀)

private lemma six_solvable_quotient {G : Type} [Group G] [Finite G] {T T₀ P : Subgroup G}
    (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPT₀ : P ≤ Subgroup.normalizer (T₀ : Set G))
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {b₁ : G} (hb₁P : b₁ ∈ P) (hb₁ : orderOf b₁ = 3)
    (hfix : ∀ t ∈ T, b₁ * t * b₁⁻¹ * t⁻¹ ∈ T₀ → t ∈ T₀)
    [hN : (T₀.subgroupOf T).Normal] :
    IsSolvable (↥T ⧸ T₀.subgroupOf T) := by
  by_cases hsub : Subsingleton (↥T ⧸ T₀.subgroupOf T)
  · haveI : Subsingleton (↥T ⧸ T₀.subgroupOf T) := hsub
    exact Group.isSolvable_of_comm (fun a b => Subsingleton.elim _ _)
  · obtain ⟨τ, hfixτ⟩ := l3Two_quotient_fixedPointFree hPT hPT₀ hb₁P hfix
    let α : MulAut (↥T ⧸ T₀.subgroupOf T) := τ ⟨b₁, hb₁P⟩
    have hb₁3 : b₁ ^ 3 = 1 := by
      have h3 : orderOf b₁ ∣ 3 := by simpa [hb₁] using (dvd_refl 3 : (3 : ℕ) ∣ 3)
      rwa [orderOf_dvd_iff_pow_eq_one] at h3
    have hα3 : α ^ 3 = 1 := by
      change τ ⟨b₁, hb₁P⟩ ^ 3 = 1
      rw [← map_pow]
      have h3 : (⟨b₁, hb₁P⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by simpa using hb₁3)
      rw [h3, map_one]
    have hα1 : α ≠ 1 := by
      intro h
      apply hsub
      refine ⟨fun x y => ?_⟩
      have hx : x = 1 := hfixτ x (by rw [show τ ⟨b₁, hb₁P⟩ = 1 from h]; rfl)
      have hy : y = 1 := hfixτ y (by rw [show τ ⟨b₁, hb₁P⟩ = 1 from h]; rfl)
      rw [hx, hy]
    have hαord : orderOf α = 3 := by
      have hdvd : orderOf α ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hα3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exfalso
        exact hα1 (orderOf_eq_one_iff.mp h)
      · exact h
    exact isSolvable_of_fixedPointFree_three α hαord hfixτ

private lemma six_solvable {G : Type} [Group G] [Finite G] {T T₀ P : Subgroup G}
    (hT₀T : T₀ ≤ T) (hTnorm : T ≤ Subgroup.normalizer (T₀ : Set G))
    (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPT₀ : P ≤ Subgroup.normalizer (T₀ : Set G))
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {b₁ k : G} (hb₁P : b₁ ∈ P) (hb₁ : orderOf b₁ = 3)
    (hfix : ∀ t ∈ T, b₁ * t * b₁⁻¹ * t⁻¹ ∈ T₀ → t ∈ T₀)
    (hT₀ : T₀ = Subgroup.zpowers k) :
    IsSolvable ↥T := by
  haveI hNnormal : (T₀.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mpr hTnorm
  haveI hquot : IsSolvable (↥T ⧸ T₀.subgroupOf T) :=
    six_solvable_quotient hPT hPT₀ hP hb₁P hb₁ hfix
  haveI hT₀solv : IsSolvable ↥(T₀.subgroupOf T) := by
    rw [hT₀]
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp a.2)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp b.2)
    simp only [Subgroup.coe_mul]
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  exact @Group.isSolvable_of_subgroup_quotient ↥T _ (T₀.subgroupOf T) hNnormal
    hT₀solv hquot

private lemma six_sylow_absurd {G : Type} [Group G] [Finite G] {M : Subgroup G} {k : G}
    (hkM : k ∈ M)
    (hkMord : orderOf (⟨k, hkM⟩ : ↥M) = 2) (hkMne : (⟨k, hkM⟩ : ↥M) ≠ 1)
    (hT : M ⊓ Subgroup.centralizer ({k} : Set G) = Subgroup.zpowers k)
    {R : Sylow 2 ↥M}
    (hRle : Subgroup.zpowers (⟨k, hkM⟩ : ↥M) ≤ (R : Subgroup ↥M))
    (hne : (R : Subgroup ↥M) ≠ Subgroup.zpowers (⟨k, hkM⟩ : ↥M)) : False := by
  let kM : ↥M := ⟨k, hkM⟩
  let P₀ : Subgroup ↥M := Subgroup.zpowers kM
  have hHne : P₀.subgroupOf (R : Subgroup ↥M) ≠ ⊤ := by
    intro htop
    exact hne (show (R : Subgroup ↥M) = P₀ from
      le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hRle)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxN, hxnot⟩ :=
    exists_normalizer_lt_of_isPGroup (p := 2) R.isPGroup'
      (H := P₀.subgroupOf (R : Subgroup ↥M)) hHne
  have hkmem : kM ∈ P₀ := Subgroup.mem_zpowers kM
  have hkR : (⟨kM, hRle hkmem⟩ : ↥R) ∈ P₀.subgroupOf (R : Subgroup ↥M) :=
    Subgroup.mem_subgroupOf.mpr hkmem
  have hconj : x * ⟨kM, hRle hkmem⟩ * x⁻¹ ∈ P₀.subgroupOf (R : Subgroup ↥M) :=
    (Subgroup.mem_normalizer_iff.mp hxN _).mp hkR
  have hzP₀ : (x.val * kM * x.val⁻¹ : ↥M) ∈ P₀ := by
    have h := Subgroup.mem_subgroupOf.mp hconj
    convert h using 2 <;> simp
  have hz_eq : (x.val * kM * x.val⁻¹ : ↥M) = kM := by
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hkMord).mp hzP₀ with h1 | hk'
    · exfalso
      refine hkMne ?_
      calc kM = x.val⁻¹ * (x.val * kM * x.val⁻¹) * x.val := by group
        _ = 1 := by rw [h1]; group
    · exact hk'
  have hxT : (x.val : G) ∈ M ⊓ Subgroup.centralizer ({k} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨x.val.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : x.val * kM = kM * x.val := by
      calc x.val * kM = (x.val * kM * x.val⁻¹) * x.val := by group
        _ = kM * x.val := by rw [hz_eq]
    simpa using congrArg (fun z : ↥M => (z : G)) h'
  have hxT₀ : (x.val : G) ∈ Subgroup.zpowers k := hT ▸ hxT
  have hxP₀ : x.val ∈ P₀ := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxT₀
    exact ⟨m, by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa using hm⟩
  exact hxnot (Subgroup.mem_subgroupOf.mpr hxP₀)

private lemma six_sylow {G : Type} [Group G] [Finite G] {M : Subgroup G} {k : G}
    (hkM : k ∈ M) (hk : orderOf k = 2)
    (hT : M ⊓ Subgroup.centralizer ({k} : Set G) = Subgroup.zpowers k) :
    ∃ R : Sylow 2 ↥M, (R : Subgroup ↥M) = Subgroup.zpowers (⟨k, hkM⟩ : ↥M) := by
  have hkMord : orderOf (⟨k, hkM⟩ : ↥M) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨k, hkM⟩ : ↥M)]
    exact hk
  have hkMne : (⟨k, hkM⟩ : ↥M) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hkMord
    omega
  have hP₀card : Nat.card ↥(Subgroup.zpowers (⟨k, hkM⟩ : ↥M)) = 2 := by
    rw [Nat.card_zpowers, hkMord]
  have hP₀p : IsPGroup 2 ↥(Subgroup.zpowers (⟨k, hkM⟩ : ↥M)) :=
    IsPGroup.of_card (n := 1) (by rw [hP₀card]; norm_num)
  obtain ⟨R, hRle⟩ := hP₀p.exists_le_sylow
  refine ⟨R, ?_⟩
  by_contra hne
  exact six_sylow_absurd hkM hkMord hkMne hT hRle hne

private lemma six_normalizer_le_centralizer {G : Type} [Group G] [Finite G] {M : Subgroup G}
    {k : G} (hkM : k ∈ M) (hk : orderOf k = 2) {R : Sylow 2 ↥M}
    (hRP₀ : (R : Subgroup ↥M) = Subgroup.zpowers (⟨k, hkM⟩ : ↥M)) :
    Subgroup.normalizer ((R : Subgroup ↥M) : Set ↥M) ≤
      Subgroup.centralizer ((R : Subgroup ↥M) : Set ↥M) := by
  let kM : ↥M := ⟨k, hkM⟩
  have hkMord : orderOf kM = 2 := by
    rw [← Subgroup.orderOf_coe kM]
    exact hk
  have hkMne : kM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hkMord
    omega
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyz : y ∈ Subgroup.zpowers kM := by
    rw [← hRP₀]
    exact hy
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hkMord).mp hyz with h1 | hk'
  · rw [h1, one_mul, mul_one]
  · have hgk : g * kM * g⁻¹ = kM := by
      have hmem : g * kM * g⁻¹ ∈ (R : Subgroup ↥M) :=
        (Subgroup.mem_normalizer_iff.mp hg kM).mp (by
          rw [hRP₀]
          exact Subgroup.mem_zpowers kM)
      rw [hRP₀] at hmem
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hkMord).mp hmem with h1 | hk''
      · exfalso
        have hk1 : kM = 1 := by
          calc kM = g⁻¹ * (g * kM * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group
        exact hkMne hk1
      · exact hk''
    rw [hk']
    calc kM * g = (g * kM * g⁻¹) * g := by rw [hgk]
      _ = g * kM := by group

private lemma six_index_two {G : Type} [Group G] [Finite G] {M : Subgroup G} {k : G}
    (hkM : k ∈ M) (hk : orderOf k = 2)
    (hT : M ⊓ Subgroup.centralizer ({k} : Set G) = Subgroup.zpowers k) :
    ∃ K : Subgroup ↥M, K.Normal ∧ K.index = 2 ∧
      K ⊔ Subgroup.zpowers (⟨k, hkM⟩ : ↥M) = ⊤ ∧
      K ⊓ Subgroup.zpowers (⟨k, hkM⟩ : ↥M) = ⊥ := by
  let kM : ↥M := ⟨k, hkM⟩
  have hkMord : orderOf kM = 2 := by
    rw [← Subgroup.orderOf_coe kM]
    exact hk
  obtain ⟨R, hRP₀⟩ := six_sylow hkM hk hT
  have hNR := six_normalizer_le_centralizer hkM hk hRP₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKnormal, -, hKindex, -, -, -, hsup, hinf, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement (p := 2) R hNR
  have hcardR : Nat.card R = 2 := by
    change Nat.card ↥(R : Subgroup ↥M) = 2
    rw [hRP₀, Nat.card_zpowers, hkMord]
  exact ⟨K, hKnormal, hKindex.trans hcardR, by rw [← hRP₀]; exact hsup,
    by rw [← hRP₀]; exact hinf⟩

private lemma six_b_mem {G : Type} [Group G] [Finite G] {M : Subgroup G} {b : G}
    (hbM : b ∈ M) (hb : orderOf b = 3) {K : Subgroup ↥M} (hKnormal : K.Normal)
    (hKindex : K.index = 2) : (⟨b, hbM⟩ : ↥M) ∈ K := by
  haveI : K.Normal := hKnormal
  have hqcard : Nat.card (↥M ⧸ K) = 2 := by
    rw [← Subgroup.index_eq_card K, hKindex]
  have hdvd2 : orderOf (QuotientGroup.mk' K ⟨b, hbM⟩) ∣ 2 := by
    have h := Subgroup.card_subgroup_dvd_card
      (Subgroup.zpowers (QuotientGroup.mk' K ⟨b, hbM⟩))
    rwa [Nat.card_zpowers, hqcard] at h
  have hdvd3 : orderOf (QuotientGroup.mk' K ⟨b, hbM⟩) ∣ 3 := by
    have h := orderOf_map_dvd (QuotientGroup.mk' K) (⟨b, hbM⟩ : ↥M)
    simpa [hb] using h
  have hone : QuotientGroup.mk' K ⟨b, hbM⟩ = 1 := by
    have hgcd : orderOf (QuotientGroup.mk' K ⟨b, hbM⟩) ∣ 1 := by
      have hgcd' := Nat.dvd_gcd hdvd2 hdvd3
      rwa [show Nat.gcd 2 3 = 1 from by decide] at hgcd'
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  exact (QuotientGroup.eq_one_iff _).mp hone

private lemma six_K_abelian {G : Type} [Group G] [Finite G] {M : Subgroup G} {k : G}
    (hkM : k ∈ M) (hk : orderOf k = 2)
    (hT : M ⊓ Subgroup.centralizer ({k} : Set G) = Subgroup.zpowers k)
    {K : Subgroup ↥M} (hKnormal : K.Normal)
    (hinf : K ⊓ Subgroup.zpowers (⟨k, hkM⟩ : ↥M) = ⊥) :
    ∀ x y : ↥K, Commute x y := by
  let kM : ↥M := ⟨k, hkM⟩
  have hkMord : orderOf kM = 2 := by
    rw [← Subgroup.orderOf_coe kM]
    exact hk
  have hkM2 : kM * kM = 1 := by
    rw [← pow_two, ← hkMord]
    exact pow_orderOf_eq_one kM
  haveI : K.Normal := hKnormal
  let φ : MulAut ↥K := MulAut.conjNormal (H := K) kM
  have hφff : MonoidHom.FixedPointFree (φ : ↥K → ↥K) := by
    intro x hx
    apply Subtype.ext
    have hxM_eq : kM * (x : ↥M) * kM⁻¹ = (x : ↥M) := by
      have h := congrArg (fun z : ↥K => (z : ↥M)) hx
      rwa [MulAut.conjNormal_apply] at h
    have hxT : ((x : ↥K) : G) ∈ M ⊓ Subgroup.centralizer ({k} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(x : ↥M).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : kM * (x : ↥M) = (x : ↥M) * kM := by
        calc kM * (x : ↥M) = kM * (x : ↥M) * kM⁻¹ * kM := by group
          _ = (x : ↥M) * kM := by rw [hxM_eq]
      simpa using congrArg (fun z : ↥M => (z : G)) h2.symm
    have hxT₀ : ((x : ↥K) : G) ∈ Subgroup.zpowers k := by
      rw [← hT]
      exact hxT
    have hxP₀ : (x : ↥M) ∈ Subgroup.zpowers (⟨k, hkM⟩ : ↥M) := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxT₀
      exact ⟨m, by
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        simpa using hm⟩
    have hxbot : (x : ↥M) ∈ (⊥ : Subgroup ↥M) := by
      have hmem : (x : ↥M) ∈ K ⊓ Subgroup.zpowers (⟨k, hkM⟩ : ↥M) :=
        ⟨Subtype.property x, hxP₀⟩
      rwa [hinf] at hmem
    exact Subgroup.mem_bot.mp hxbot
  have hφinv : Function.Involutive (φ : ↥K → ↥K) := by
    intro x
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    have hkminv : kM⁻¹ = kM := (eq_inv_iff_mul_eq_one.mpr hkM2).symm
    calc kM * (kM * ↑x * kM⁻¹) * kM⁻¹ = (kM * kM) * ↑x * (kM⁻¹ * kM⁻¹) := by group
      _ = ↑x := by rw [hkM2, hkminv, hkM2]; group
  exact MonoidHom.FixedPointFree.commute_all_of_involutive (φ := φ) hφff hφinv

private lemma six_K_le_D {G : Type} [Group G] {M : Subgroup G} {b k : G}
    (hbM : b ∈ M) (hCb : ∀ m ∈ M, m * b = b * m → m ∈ Subgroup.zpowers b)
    {K : Subgroup ↥M} (hKabel : ∀ x y : ↥K, Commute x y) (hbK : (⟨b, hbM⟩ : ↥M) ∈ K) :
    K ≤ Subgroup.comap M.subtype (Subgroup.closure ({b, k} : Set G)) := by
  intro x hx
  have hcommK : (⟨x, hx⟩ : ↥K) * ⟨⟨b, hbM⟩, hbK⟩ = ⟨⟨b, hbM⟩, hbK⟩ * ⟨x, hx⟩ :=
    hKabel ⟨x, hx⟩ ⟨⟨b, hbM⟩, hbK⟩
  have hcomm : (x : G) * b = b * (x : G) := by
    have := congrArg (fun z : ↥K => ((z : ↥M) : G)) hcommK
    simpa using this
  exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) (hCb (x : G) x.2 hcomm)

theorem fs81SixLemma_holds : FS81SixLemma := by
  intro G _ _ M P b k b₁ hbM hkM hb hk hbk hPM hP hb₁P hb₁ hPk hCb hCb₁
  classical
  let T : Subgroup G := M ⊓ Subgroup.centralizer ({k} : Set G)
  let T₀ : Subgroup G := Subgroup.zpowers k
  let kM : ↥M := ⟨k, hkM⟩
  have hT₀leM : T₀ ≤ M := Subgroup.zpowers_le.mpr hkM
  have hT₀leC : T₀ ≤ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hT₀leT : T₀ ≤ T := le_inf hT₀leM hT₀leC
  obtain ⟨hTnorm, hPT₀, hPT⟩ := six_normalizers hPM hPk
  have hfix : ∀ t ∈ T, b₁ * t * b₁⁻¹ * t⁻¹ ∈ T₀ → t ∈ T₀ :=
    six_fix hkM hb hk hbk hb₁P hb₁ hPk hCb₁ hTnorm
  have hsol : IsSolvable ↥T :=
    six_solvable hT₀leT hTnorm hPT hPT₀ hP hb₁P hb₁ hfix rfl
  have hTleT₀ : T ≤ T₀ :=
    le_of_l3TwoFixedPointFree (b := b₁) hT₀leT hTnorm hPT hPT₀ hP hb₁P hb₁ hsol hfix
  have hTeq : T = T₀ := le_antisymm hTleT₀ hT₀leT
  obtain ⟨K, hKnormal, hKindex, hsup, hinf⟩ := six_index_two hkM hk hTeq
  have hbK : (⟨b, hbM⟩ : ↥M) ∈ K := six_b_mem hbM hb hKnormal hKindex
  have hKabel : ∀ x y : ↥K, Commute x y := six_K_abelian hkM hk hTeq hKnormal hinf
  have hKleD : K ≤ Subgroup.comap M.subtype (Subgroup.closure ({b, k} : Set G)) :=
    six_K_le_D hbM hCb hKabel hbK
  have hzD : Subgroup.zpowers k ≤ Subgroup.closure ({b, k} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  intro m hm
  have htop : (⟨m, hm⟩ : ↥M) ∈ K ⊔ Subgroup.zpowers kM := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hle : K ⊔ Subgroup.zpowers kM ≤
      Subgroup.comap M.subtype (Subgroup.closure ({b, k} : Set G)) := by
    refine sup_le hKleD ?_
    intro x hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxG : ((x : ↥M) : G) ∈ Subgroup.zpowers k := by
      refine ⟨j, ?_⟩
      rw [← hj, Subgroup.coe_zpow]
    exact hzD hxG
  exact Subgroup.mem_subgroupOf.mp (hle htop)

end CFSG.StandardType.FrameRoute.FS81
