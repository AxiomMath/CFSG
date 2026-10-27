module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListFamilies
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLang
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2Defs
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate1952
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGF4SmallBook
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2
import CFSG.LocalAnalysis.StandardType.GGF4H1Coverage
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
import CFSG.LocalAnalysis.StandardType.GGNbrU63
import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
import CFSG.LocalAnalysis.StandardType.GGForkA8NotReflHolds
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeD
import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGPZWeylB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace F4H4Lin

theorem not_dvd_both {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ 2 ^ n - 1)
    (h2 : p ∣ 2 ^ n + 1) : False := by
  have h0 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h3 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have h4 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem factorial_succ_ne {n : ℕ} (h : (n + 1).factorial = 48) : False := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num [Nat.factorial] at h
  · have h5 : (5 : ℕ).factorial ≤ (n + 1).factorial := Nat.factorial_le (by omega)
    rw [h] at h5
    norm_num [Nat.factorial] at h5

theorem rank_two_of_dvd {p l : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : 1 ≤ l) (h3 : l ≤ 3)
    (hd : p ∣ l + 1) : l = 2 ∧ p = 3 := by
  interval_cases l
  · norm_num at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd) hp2
  · norm_num at hd
    exact ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd⟩
  · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hd)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2

theorem label_eq {lab : LargeEvenLabel} {t : LargeEvenLieTag} {l n : ℕ} (h1 : lab.tag = t)
    (h2 : lab.rank = l) (h3 : lab.n = n) : lab = ⟨t, l, n⟩ := by
  obtain ⟨t', l', n'⟩ := lab
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem halfSplit_A {p : ℕ} {lab : LargeEvenLabel} {c : Prop} (ht : lab.tag = .A)
    (h : LargeEvenHalfSplit p lab c) :
    p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) ∨ (lab.rank = 5 ∧ lab.n = 2 ∧ c ∧ p = 5) ∨
      (lab.rank = 8 ∧ lab.n = 1 ∧ p = 7) := by
  rcases h with ((⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h) | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h5, hn, hc, hp⟩ |
    ⟨-, h8, hn, hp⟩ | ⟨h, -⟩)
  · exact Or.inl h
  · simp [LargeEvenUntwisted, ht] at h
  · rcases h with h | h <;> simp [ht] at h
  · exact Or.inr (Or.inl h)
  · rcases h with h | h | h | h | h <;> simp [ht] at h
  · rcases h with ⟨h, -⟩ | h <;> simp [ht] at h
  · exact Or.inr (Or.inr (Or.inl ⟨h5, hn, hc, hp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h8, hn, hp⟩))
  · simp [ht] at h

theorem halfSplit_twA {p : ℕ} {lab : LargeEvenLabel} {c : Prop} (ht : lab.tag = .twA)
    (h : LargeEvenHalfSplit p lab c) :
    p ∣ 2 ^ lab.n + 1 ∨ (lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) := by
  rcases h with ((⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨hn, hp⟩) | ⟨h, -⟩ | ⟨h, hq⟩ | ⟨h, -⟩ |
    ⟨h, -⟩ | ⟨h, -⟩)
  · simp [LargeEvenUntwisted, ht] at h
  · exact Or.inl h
  · rcases h with h | h <;> simp [ht] at h
  · left
    rw [hn, hp]
    norm_num
  · rcases h with h | h | h | h | h <;> simp [ht] at h
  · rcases h with ⟨-, h5⟩ | h
    · exact Or.inr ⟨h5, hq⟩
    · simp [ht] at h
  · simp [ht] at h
  · simp [ht] at h
  · simp [ht] at h

theorem halfSplit_D {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (ht : lab.tag = .D ∨ lab.tag = .twD) (h : LargeEvenHalfSplit p lab c) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  rcases h with ((⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨hn, hp⟩) | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ |
    ⟨h, -⟩ | ⟨h, -⟩)
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h
  · right
    rw [hn, hp]
    norm_num
  · exact Or.inr h
  · exact Or.inl h
  · rcases ht with ht | ht <;> simp [ht] at h
  · rcases ht with ht | ht <;> simp [ht] at h
  · rcases ht with ht | ht <;> simp [ht] at h

theorem halfSplit_true {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : LargeEvenHalfSplit p lab c) : LargeEvenHalfSplit p lab True := by
  rcases h with h | h | h | ⟨h1, h2, h3, -, h5⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, trivial, h5⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem linear_of_iso {lab lab₁ : LargeEvenLabel} (htag : GGF4TagLinear lab.tag)
    (hiso : GGLabelIso lab lab₁) :
    GGF4TagLinear lab₁.tag ∨ ((lab₁.tag = .D ∨ lab₁.tag = .twD) ∧ lab₁.rank ≤ 3) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨t₁, l₁, n₁⟩ := lab₁
  simp only [GGF4TagLinear] at htag ⊢
  rcases hiso with heq | ⟨ht, -⟩ | ⟨heq, -⟩ | ⟨-, heq⟩ | ⟨heq, -⟩ | ⟨-, heq⟩ | ⟨heq, -⟩ |
    ⟨heq, -⟩
  · simp only [LargeEvenLabel.mk.injEq] at heq
    obtain ⟨rfl, -, -⟩ := heq
    exact Or.inl htag
  · dsimp only at ht
    rcases htag with rfl | rfl <;> simp at ht
  · simp only [LargeEvenLabel.mk.injEq] at heq
    obtain ⟨rfl, -, -⟩ := heq
    simp at htag
  · simp only [LargeEvenLabel.mk.injEq] at heq
    obtain ⟨rfl, rfl, -⟩ := heq
    exact Or.inr ⟨Or.inl rfl, le_refl 3⟩
  · simp only [LargeEvenLabel.mk.injEq] at heq
    obtain ⟨rfl, -, -⟩ := heq
    simp at htag
  · simp only [LargeEvenLabel.mk.injEq] at heq
    obtain ⟨rfl, rfl, -⟩ := heq
    exact Or.inr ⟨Or.inr rfl, le_refl 3⟩
  · simp only [LargeEvenLabel.mk.injEq] at heq
    obtain ⟨rfl, -, -⟩ := heq
    simp at htag
  · simp only [LargeEvenLabel.mk.injEq] at heq
    obtain ⟨rfl, rfl, -⟩ := heq
    exact Or.inr ⟨Or.inr rfl, by norm_num⟩

theorem alias_cov {p : ℕ} {lab : LargeEvenLabel} {c : Prop} (hlab : LargeEvenInLambda2 lab)
    (htD : lab.tag = .D ∨ lab.tag = .twD) (hr : lab.rank ≤ 3) (hHS : LargeEvenHalfSplit p lab c) :
    GGTBTorCov p lab := by
  rcases halfSplit_D htD hHS with hq | hq
  · rcases htD with ht | ht
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inl ⟨ht, Or.inl hq⟩)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨ht, Or.inl hq⟩)⟩
  · rcases htD with ht | ht
    · have h3 : 3 ≤ lab.rank := by
        have h := hlab.2
        rw [ht] at h
        exact h
      exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inl ⟨ht, hq, ⟨1, by omega⟩⟩)⟩
    · have h2 : 2 ≤ lab.rank := by
        have h := hlab.2
        rw [ht] at h
        exact h
      rcases (by omega : lab.rank = 2 ∨ lab.rank = 3) with h | h
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨ht, Or.inr ⟨hq, ⟨1, by omega⟩⟩⟩)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inr ⟨ht, hq, ⟨1, by omega⟩⟩)⟩

theorem row_rank_five {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hlin : GGF4TagLinear lab.tag ∨ ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank ≤ 3))
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt p lab r m N C M) (h48 : Nat.card M.Group = 48) :
    lab.rank = 5 ∧ ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)) := by
  have htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .D ∨ lab.tag = .twD := by
    rcases hlin with (h | h) | ⟨h | h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hDle : lab.tag = .D ∨ lab.tag = .twD → lab.rank ≤ 3 := by
    intro hD
    rcases hlin with (h | h) | ⟨-, h⟩
    · rcases hD with h' | h' <;> rw [h] at h' <;> simp at h'
    · rcases hD with h' | h' <;> rw [h] at h' <;> simp at h'
    · exact h
  have hD2 : lab.tag = .D ∨ lab.tag = .twD → 2 ≤ lab.rank := by
    intro hD
    have h := hlab.2
    rcases hD with hD | hD <;> rw [hD] at h <;> omega
  cases hrow with
  | aDep _ _ _ _ _ =>
      exact (factorial_succ_ne (by rw [← l05nK3a_card_coxeterA]; exact h48)).elim
  | e6Three h1 _ _ => rcases htag with h | h | h | h <;> simp [h] at h1
  | e8Three h1 _ => rcases htag with h | h | h | h <;> simp [h] at h1
  | aInd _ _ _ =>
      exact (factorial_succ_ne (by rw [← l05nK3a_card_coxeterA]; exact h48)).elim
  | c h1 _ => rcases htag with h | h | h | h <;> rcases h1 with h1 | h1 <;> simp [h] at h1
  | d h1 =>
      have hD : lab.tag = .D ∨ lab.tag = .twD := by
        rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr h
      have hle := SpJoinRefl.card_coxeterD_le lab.rank (hD2 hD)
      rw [h48] at hle
      have h3 := hDle hD
      have h2 := hD2 hD
      interval_cases h : lab.rank <;> norm_num [Nat.factorial] at hle
  | e6Ind _ h1 _ => rcases htag with h | h | h | h <;> rcases h1 with h1 | h1 <;> simp [h] at h1
  | e7 h1 _ => rcases htag with h | h | h | h <;> simp [h] at h1
  | e8Ind _ h1 _ => rcases htag with h | h | h | h <;> simp [h] at h1
  | f4 h1 _ _ => rcases htag with h | h | h | h <;> simp [h] at h1
  | g2 h1 _ => rcases htag with h | h | h | h <;> simp [h] at h1
  | relD h1 =>
      have hD : lab.tag = .D ∨ lab.tag = .twD := by
        rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr h
      have hle := card_coxeterB_le (lab.rank - 1)
      rw [h48] at hle
      have h3 := hDle hD
      have h2 := hD2 hD
      interval_cases h : lab.rank <;> norm_num [Nat.factorial] at hle
  | relE6 _ h1 =>
      rcases htag with h | h | h | h <;> rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h] at h1
  | relA5 h1 h2 => exact ⟨h1, h2⟩

section Config

variable {G : Type} [Group G] [Finite G]

theorem card_gamma_nbr {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = p ^ 4) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (ggGamma K hN).range = p ^ 3 := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have hB : B = Bs := ggF4Small_eq_Bs hcfg hcard
  subst hB
  apply Nat.mul_right_cancel hp.pos
  calc Nat.card (ggGamma K hN).range * p = Nat.card B :=
        card_range_ggGamma_mul_of_sHat hp hnb.1 hN
    _ = p ^ 3 * p := by rw [hcard, ← pow_succ]

theorem false_of_nbr_torusLift_ge_four {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = p ^ 4)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) {S : ℕ → LargeEvenLabel → Prop}
    (hM : GGInnerDiagOnLabel S p Bs K)
    (hlift : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ _ _ => ∃ r, 4 ≤ r ∧ GGTorusLift p r R) : False := by
  have hp : p.Prime := hcfg.tableB_facts.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨_, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP₀⟩ := hQ₀
  obtain ⟨hSlab, -, -⟩ := hP₀
  obtain ⟨R, _, I, F, hQ, hliftR⟩ := largeEvenRawDatum_exists (hlift lab hlab hSlab _ hraw)
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨-, hN, -⟩ := hP
  obtain ⟨r, hr4, hlift'⟩ := hliftR
  have hge := pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hperf θ hN hlift'
  have hp4 : p ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    (Nat.pow_le_pow_right hp.pos hr4).trans hge
  rw [card_gamma_nbr hcfg hcard hnb hN] at hp4
  have h43 : 4 ≤ 3 := (pow_le_pow_iff_right₀ hp.one_lt).mp hp4
  omega

omit [Finite G] in
theorem reflGenerated_of_weylOfType {p : ℕ} {Bs : Subgroup G} {ι : Type}
    {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} (h : GGWeylOfType p M A) :
    GGReflGenerated p A := by
  obtain ⟨f, hf⟩ := h
  apply le_antisymm
  · have hgen : Subgroup.closure (Set.range M.simple) = ⊤ :=
      M.toCoxeterSystem.subgroup_closure_range_simple
    let C : Subgroup ↥A :=
      (Subgroup.closure {a : MulAut ↥Bs | a ∈ A ∧ GGIsReflection p a}).comap A.subtype
    have hfac : Subgroup.comap (f : M.Group →* ↥A) C = ⊤ := by
      have hle : Subgroup.closure (Set.range M.simple) ≤
          Subgroup.comap (f : M.Group →* ↥A) C := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨i, rfl⟩
        exact (Subgroup.mem_comap).mpr ((Subgroup.mem_comap).mpr
          (Subgroup.subset_closure ⟨(f (M.simple i)).2, hf i⟩))
      rw [hgen] at hle
      exact le_antisymm le_top hle
    intro a ha
    have hx : (⟨a, ha⟩ : ↥A) ∈ C := by
      have hy : f.symm (⟨a, ha⟩ : ↥A) ∈ Subgroup.comap (f : M.Group →* ↥A) C := by
        rw [hfac]
        exact Subgroup.mem_top _
      simpa using hy
    exact hx
  · exact (Subgroup.closure_le A).mpr (fun x hx => hx.1)

theorem nbr_tor_card
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {lab₁ : LargeEvenLabel} (hM₁ : GGInnerDiagOnLabel (fun _ l => l = lab₁) p Bs K)
    (hcov : GGTBTorCov p lab₁) :
    ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      GGTBTorRowAt p lab₁ r m N C M ∧ Nat.card (ggAutomizer K Bs) = Nat.card M.Group := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hmk : GGInnerDiagOnLabel (fun p' lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p' lab r m N C M ∧ GGTBTorRowAt p lab₁ r m N C M)
      p Bs K := by
    obtain ⟨r, m, N, C, M, hrow⟩ := hcov
    refine largeEvenMarking_mono ?_ hM₁
    intro l R _ I F θ h
    obtain ⟨hl, h2⟩ := h
    subst hl
    exact ⟨⟨r, m, N, C, M, hrow, hrow⟩, h2⟩
  obtain ⟨lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hrow₁, hBsI, hlift,
    hTorW, -⟩ := l05nPlQ_marking_with (ggTBTorWRows_of_all (ggTBTorAll_of_remaining trivial))
      ggTBTorLiftRows_holds hp2 (fun r m N C M => GGTBTorRowAt p lab₁ r m N C M) hmk
  have hTB := ggTorusTBGroup_of_nbr hcfg hnb hperf θ hN hBsI hlift
  have hTor := hTorW ↥K (ggQuotHom θ) (ggGamma K hN).range hTB
  obtain ⟨hom, hpm, -, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨r, m, N, C, M, hrow₁, ggTD_card_automizer hp2 hom hpm hBs hSC hN hTor⟩

theorem small_false
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {lab₁ : LargeEvenLabel} {c : Prop}
    (hmark : ∀ T : ℕ → LargeEvenLabel → Prop, T p lab₁ → GGInnerDiagOnLabel T p Bs K)
    (hcov : ¬ GGTBTorCov p lab₁) (hHS : LargeEvenHalfSplit p lab₁ c) (hp7 : p ≠ 7)
    (hlin : GGF4TagLinear lab₁.tag) (hsmall : GGTBResSmallLabel p lab₁) : False := by
  have htw : lab₁.tag ≠ .twF4 ∧ lab₁.tag ≠ .twF4der := by
    rcases hlin with h | h <;> simp [h]
  have hU : ¬ (lab₁.tag = .twA ∧ lab₁.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab₁.n + 1) := by
    rintro ⟨ht, hr, -⟩
    rcases hsmall with ⟨h, -⟩ | ⟨-, h⟩ | h | h | h | h
    · rw [ht] at h
      simp at h
    · omega
    all_goals rw [ht] at h; simp at h
  exact ggTBWeylRowResRest_small_false_nbr hcfg hnb
    (hmark _ ⟨⟨⟨hcov, halfSplit_true hHS, fun h => hp7 h.1, htw.1, htw.2⟩, hU⟩, hsmall⟩)

end Config

section List

variable {G : Type} [Group G]

theorem list_of_A5 {p : ℕ} {K : Subgroup G} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hhas : GGHasLabel lab (K ⧸ Subgroup.center K)) (ht : lab.tag = .A) (hr5 : lab.rank = 5)
    (hq : p ∣ 2 ^ lab.n + 1) (hHS : LargeEvenHalfSplit p lab (Subgroup.center K = ⊥)) :
    GGF4NbrList p K := by
  rcases halfSplit_A ht hHS with hq' | ⟨hn1, hp3⟩ | ⟨-, hn2, hc, hp5⟩ | ⟨hr8, -, -⟩
  · exact (not_dvd_both hp hp2 hq' hq).elim
  · refine Or.inr (Or.inl ⟨hp3, Or.inl ?_⟩)
    rwa [label_eq ht hr5 hn1] at hhas
  · refine Or.inr (Or.inr (Or.inl ⟨hp5, ?_, hc⟩))
    rwa [label_eq ht hr5 hn2] at hhas
  · omega

theorem list_of_twA5 {p : ℕ} {K : Subgroup G} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (ht : lab.tag = .twA) (hr5 : lab.rank = 5) (hq : p ∣ 2 ^ lab.n - 1) : GGF4NbrList p K := by
  have hn : 2 ≤ lab.n := by
    by_contra hlt
    have h1 : lab.n = 1 := by
      have := hlab.1
      omega
    rw [h1] at hq
    have := Nat.le_of_dvd (by norm_num) hq
    have := hp.two_le
    omega
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hr5 hq hn
  subst ht hr5
  exact Or.inr (Or.inr (Or.inr ⟨n, hn, hq, hhas⟩))

end List

end F4H4Lin

open F4H4Lin in
theorem ggF4H4ListLin_holds
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) : GGF4H4ListLin := by
  intro G _ _ p B Bs x L D J ks hres hB K hK lab hΛ htag hlab
  classical
  obtain ⟨hR, -, ⟨ι, M, e, hP, hF⟩, -, -⟩ := hres
  have hrest : GGSecFiveRestHyp p B Bs x L D J := hR.1
  have hcfg : GGConfig p B Bs x L D J := hrest.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hcard : Nat.card Bs = p ^ 4 :=
    ggF4Small_card_Bs hTBF hWI hR (ggF4Small_weylOfType_F4 e hP hF) ⟨K, hK⟩
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hrest.2.2.1.2 y K hnb
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  obtain ⟨lab₁, hΛ₁, hhas₁, -, -, -, -, -, hHS⟩ :=
    largeEvenMarking_exists_hasLabel (ggNbr_halfSplit_of_secFiveRest hraw hiso hrest hnb)
  have hlin₁ := linear_of_iso htag (ggLabelRigidInput_holds lab lab₁ _ hΛ hΛ₁ hlab hhas₁)
  have hM₁ : GGInnerDiagOnLabel (fun _ l => l = lab₁) p Bs K :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hΛ₁ hhas₁
  have hmark : ∀ T : ℕ → LargeEvenLabel → Prop, T p lab₁ → GGInnerDiagOnLabel T p Bs K := by
    intro T hT
    refine largeEvenMarking_mono ?_ hM₁
    intro l R _ I F θ h
    obtain ⟨hl, h2⟩ := h
    subst hl
    exact ⟨hT, h2⟩
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := by
    obtain ⟨_, _, _, hraw₁⟩ := hM₁
    obtain ⟨_, _, _, _, _, _, _, _, hN, _⟩ := largeEvenRawDatum_exists hraw₁
    exact hN
  have h48 : Nat.card (ggAutomizer K Bs) = 48 := by
    obtain ⟨eK, -⟩ := hB K hK
    rw [← Nat.card_congr eK.toEquiv, ggCoxeterB_card 3 (by norm_num)]
    norm_num [Nat.factorial]
  by_cases hcov : GGTBTorCov p lab₁
  ·
    obtain ⟨r, m, N, C, M', hrow, hcW⟩ := nbr_tor_card hcfg hnb hM₁ hcov
    obtain ⟨hr5, hA | hT⟩ := row_rank_five hΛ₁ hlin₁ hrow (hcW ▸ h48)
    · exact list_of_A5 hp hp2 hhas₁ hA.1 hr5 hA.2 hHS
    · exact list_of_twA5 hp hΛ₁ hhas₁ hT.1 hr5 hT.2
  rcases hlin₁ with (htA | htT) | ⟨htD, hrD⟩
  ·
    rcases halfSplit_A htA hHS with hq | ⟨hn1, hp3⟩ | ⟨hr5, hn2, -, hp5⟩ | ⟨hr8, hn1, hp7⟩
    ·
      exfalso
      have hM : p ∣ ggTorM lab₁ := by simpa [ggTorM, htA] using hq
      have hr1 : 1 ≤ lab₁.rank := by
        have h := hΛ₁.2
        rw [htA] at h
        exact h.1
      by_cases hpr : p ∣ lab₁.rank + 1
      · by_cases h4 : 4 ≤ lab₁.rank
        · exact hcov ⟨_, _, _, _, _, GGTBTorRowAt.aDep (Or.inl htA) h4 hpr hM
            (fun h => not_dvd_both hp hp2 hq h.2.2)⟩
        · obtain ⟨hr2, hp3⟩ := rank_two_of_dvd hp hp2 hr1 (by omega) hpr
          exact small_false hcfg hnb hmark hcov hHS (by omega) (Or.inl htA)
            (Or.inl ⟨htA, Or.inl hr2⟩)
      · exact hcov ⟨_, _, _, _, _, GGTBTorRowAt.aInd (Or.inl htA) hpr hM⟩
    ·
      subst hp3
      have hr2 : 2 ≤ lab₁.rank := by
        have h := hΛ₁.2
        rw [htA] at h
        by_contra hlt
        have h1 : lab₁.rank = 1 := by omega
        have := h.2 h1
        omega
      by_cases hr4 : lab₁.rank ≤ 4
      · exfalso
        refine small_false hcfg hnb hmark hcov hHS (by norm_num) (Or.inl htA) (Or.inl ⟨htA, ?_⟩)
        rcases (by omega : lab₁.rank = 2 ∨ lab₁.rank = 3 ∨ lab₁.rank = 4) with h | h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl h, hn1, rfl⟩
        · exact Or.inr ⟨Or.inr h, hn1, rfl⟩
      by_cases hr5 : lab₁.rank = 5
      · exact (hcov ⟨_, _, _, _, _, GGTBTorRowAt.relA5 hr5
          (Or.inl ⟨htA, by rw [hn1]; norm_num⟩)⟩).elim
      by_cases hr6 : lab₁.rank = 6
      ·
        refine Or.inr (Or.inl ⟨rfl, Or.inr ?_⟩)
        rwa [label_eq htA hr6 hn1] at hhas₁
      exfalso
      refine false_of_nbr_torusLift_ge_four hcfg hcard hnb (hmark (fun _ l => l = lab₁) rfl) ?_
      intro l _ hl
      subst hl
      exact ggF4H1_large_linear_two_lift ⟨htA, by omega, hn1⟩
    ·
      exact (hcov ⟨_, _, _, _, _, GGTBTorRowAt.relA5 hr5
        (Or.inl ⟨htA, by rw [hn2, hp5]; norm_num⟩)⟩).elim
    ·
      subst hp7
      have hA8 : GGHasLabel ⟨.A, 8, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
        rwa [label_eq htA hr8 hn1] at hhas₁
      exact (ggForkNbrSevenExcl'_of_notRefl (ggForkA8NotReflInput_of_mp ggInnerDiagMpInput_holds)
        G B Bs x L D J hcfg hrest.2.1 hrest.2.2.1 hrest.2.2.2.1 y K hnb
        (reflGenerated_of_weylOfType (hB K hK)) hA8).elim
  ·
    rcases halfSplit_twA htT hHS with hq | ⟨hr5, hq⟩
    · exfalso
      have hM : p ∣ ggTorM lab₁ := by simpa [ggTorM, htT] using hq
      have hr2 : 2 ≤ lab₁.rank := by
        have h := hΛ₁.2
        rw [htT] at h
        exact h.1
      by_cases hpr : p ∣ lab₁.rank + 1
      · by_cases hU : p = 3 ∧ lab₁.rank = 5
        ·
          obtain ⟨hp3, hr5⟩ := hU
          have h4 := ggUnitDvd63NbrRankInput_holds hLB hPJ G p B Bs x L D J hcfg y K hnb hN
            (hmark GGNbrInner937U63Label ⟨⟨htT, by omega, hq, hpr⟩, hr5, hp3⟩)
          rw [card_gamma_nbr hcfg hcard hnb hN] at h4
          have h43 : 4 ≤ 3 := (pow_le_pow_iff_right₀ hp.one_lt).mp h4
          omega
        · by_cases h4 : 4 ≤ lab₁.rank
          · exact hcov ⟨_, _, _, _, _, GGTBTorRowAt.aDep (Or.inr htT) h4 hpr hM
              (fun h => hU ⟨h.1, h.2.1⟩)⟩
          · obtain ⟨hr2', hp3⟩ := rank_two_of_dvd hp hp2 (by omega) (by omega) hpr
            exact small_false hcfg hnb hmark hcov hHS (by omega) (Or.inr htT)
              (Or.inr (Or.inl ⟨htT, hr2'⟩))
      · exact hcov ⟨_, _, _, _, _, GGTBTorRowAt.aInd (Or.inr htT) hpr hM⟩
    · exact (hcov ⟨_, _, _, _, _, GGTBTorRowAt.relA5 hr5 (Or.inr ⟨htT, hq⟩)⟩).elim
  ·
    exact (hcov (alias_cov hΛ₁ htD hrD hHS)).elim

end CFSG.StandardType

end
