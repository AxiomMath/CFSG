module

public import CFSG.Monster.Schur.Defs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129SP

open CFSG

structure SporLocal (W : Type) [Group W] : Prop where
  simple : IsSimpleGroup W
  nonabelian : ∃ a b : W, a * b ≠ b * a
  inner3 : ∀ β : MulAut W, β ^ 3 = 1 → ∃ w : W, β = MulAut.conj w
  noDouble : CFSG.Monster.Schur.NoPerfectDoubleCover W
  threeCases : ∀ w : W, orderOf w = 3 →
    (CFSG.IsQuasisimple ↥(Subgroup.centralizer ({w} : Set W)) ∧
      Nat.card (Subgroup.center ↥(Subgroup.centralizer ({w} : Set W))) = 3) ∨
    Nat.card ↥(Subgroup.centralizer ({w} : Set W)) = 504

section Local

variable {W : Type} [Group W] [Finite W]

theorem center_eq_bot_of_simple_nonabelian {Q : Type} [Group Q] (hQs : IsSimpleGroup Q)
    (hQn : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  haveI := hQs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hQn
    have : a ∈ Subgroup.center Q := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem psi_central_eq_one {P Q : Type} [Group P] [Group Q] (hQs : IsSimpleGroup Q)
    (hQn : ∃ a b : Q, a * b ≠ b * a) (ψ : P →* Q) (hψ : Function.Surjective ψ) {z : P}
    (hz : z ∈ Subgroup.center P) : ψ z = 1 := by
  have h1 : ψ z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hψ g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y)]
  rw [center_eq_bot_of_simple_nonabelian hQs hQn] at h1
  exact h1

theorem card_eq_ker_mul {P Q : Type} [Group P] [Group Q] (ψ : P →* Q)
    (hψ : Function.Surjective ψ) : Nat.card P = Nat.card ψ.ker * Nat.card Q := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, mul_comm]

theorem false_of_threeA {C : Subgroup W} (hCq : CFSG.IsQuasisimple ↥C)
    (hCZ : Nat.card (Subgroup.center ↥C) = 3) {P : Subgroup W} (hP : P ≤ C)
    (hsub : (P.subgroupOf C).IsSubnormal) (hPp : Group.IsPerfect P) {Q : Type} [Group Q]
    (hQs : IsSimpleGroup Q) (hQn : ∃ a b : Q, a * b ≠ b * a) (ψ : P →* Q)
    (hψ : Function.Surjective ψ) (hψker : ¬ 3 ∣ Nat.card ψ.ker) : False := by
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hCq hsub with h | h
  ·
    have hPC : P = C := by
      apply le_antisymm hP
      intro c hc
      have : (⟨c, hc⟩ : C) ∈ P.subgroupOf C := by rw [h]; trivial
      exact this
    subst hPC
    have hPq : CFSG.IsQuasisimple ↥P := hCq
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hPq (MonoidHom.normal_ker ψ) with hk | hk
    ·
      obtain ⟨a, b, hab⟩ := hQn
      obtain ⟨x, rfl⟩ := hψ a
      obtain ⟨y, rfl⟩ := hψ b
      have hx : ψ x = 1 := by
        have : x ∈ ψ.ker := by rw [hk]; trivial
        exact this
      have hy : ψ y = 1 := by
        have : y ∈ ψ.ker := by rw [hk]; trivial
        exact this
      exact hab (by rw [hx, hy])
    ·
      have hdvd : Nat.card ψ.ker ∣ 3 := by
        rw [← hCZ]
        exact Subgroup.card_dvd_of_le hk
      have hk1 : Nat.card ψ.ker = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact h1
        · exact absurd (by rw [h3]) hψker
      have hZ3 : (Subgroup.center ↥P) ≠ ⊥ := by
        intro hbot
        rw [hbot] at hCZ
        simp at hCZ
      obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hZ3)
      have hψz := psi_central_eq_one hQs hQn ψ hψ hzZ
      have hzk : z ∈ ψ.ker := hψz
      have := Subgroup.eq_bot_of_card_eq ψ.ker hk1
      rw [this] at hzk
      exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hzk))
  ·
    have hPab : ∀ a b : P, a * b = b * a := by
      intro a b
      have ha : (⟨a, hP a.2⟩ : C) ∈ Subgroup.center ↥C := h (by
        show (⟨a, hP a.2⟩ : C) ∈ P.subgroupOf C
        exact a.2)
      have h1 : (b : W) * (a : W) = (a : W) * (b : W) := by
        have := Subgroup.mem_center_iff.mp ha ⟨b, hP b.2⟩
        exact congrArg Subtype.val this
      exact Subtype.ext h1.symm
    haveI := hPp
    haveI : IsMulCommutative P := ⟨⟨hPab⟩⟩
    obtain ⟨a, b, hab⟩ := hQn
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    exact hab (by rw [Subsingleton.elim x y])

theorem spor_threeB {w : W} (hw : orderOf w = 3)
    (hC : Nat.card ↥(Subgroup.centralizer ({w} : Set W)) = 504) {P : Subgroup W}
    (hP : P ≤ Subgroup.centralizer ({w} : Set W)) {Q : Type} [Group Q] [Finite Q]
    (hQs : IsSimpleGroup Q) (hQn : ∃ a b : Q, a * b ≠ b * a) (ψ : P →* Q)
    (hψ : Function.Surjective ψ) (hψker : ¬ 3 ∣ Nat.card ψ.ker) {s : ℕ} (hs4 : 4 ≤ s)
    (hs3 : ¬ 3 ∣ s) (hQcard : Nat.card Q * Nat.gcd 2 (s - 1) = s * (s ^ 2 - 1)) :
    s = 7 ∧ Nat.card P = 168 := by
  have hPQ := card_eq_ker_mul ψ hψ
  have hPdvd : Nat.card P ∣ 504 := hC ▸ Subgroup.card_dvd_of_le hP
  have hQdvd : Nat.card Q ∣ 504 := (Dvd.intro_left _ hPQ.symm).trans hPdvd
  have hQle : Nat.card Q ≤ 504 := Nat.le_of_dvd (by norm_num) hQdvd
  have hg2 : Nat.gcd 2 (s - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hs10 : s ≤ 10 := by
    by_contra h
    push Not at h
    have h1 : 11 * (11 ^ 2 - 1) ≤ s * (s ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    have h2 : s * (s ^ 2 - 1) ≤ 504 * 2 := by
      rw [← hQcard]
      exact Nat.mul_le_mul hQle hg2
    norm_num at h1
    omega
  have h8 : s = 8 → False := by
    intro h
    subst h
    norm_num at hQcard
    have hker1 : Nat.card ψ.ker = 1 := by
      have hle : Nat.card P ≤ 504 := Nat.le_of_dvd (by norm_num) hPdvd
      have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
      rw [hQcard] at hPQ
      omega
    have hPcard : Nat.card P = 504 := by rw [hPQ, hker1, hQcard]
    have hPC : P = Subgroup.centralizer ({w} : Set W) :=
      Subgroup.eq_of_le_of_card_ge hP (by rw [hC, hPcard])
    have hwP : w ∈ P := by
      rw [hPC]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hwZ : (⟨w, hwP⟩ : P) ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_centralizer_singleton_iff.mp (hP g.2)
      exact Subtype.ext this
    have h1 := psi_central_eq_one hQs hQn ψ hψ hwZ
    have hk : (⟨w, hwP⟩ : P) ∈ ψ.ker := h1
    rw [Subgroup.eq_bot_of_card_eq ψ.ker hker1, Subgroup.mem_bot] at hk
    have : w = 1 := congrArg Subtype.val hk
    rw [this, orderOf_one] at hw
    omega
  have hcases : s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    norm_num at hQcard
    rw [hQcard] at hQdvd
    exact absurd hQdvd (by norm_num)
  ·
    norm_num at hQcard
    have : Nat.card Q = 60 := by omega
    rw [this] at hQdvd
    exact absurd hQdvd (by norm_num)
  · exact (hs3 (by norm_num)).elim
  ·
    norm_num at hQcard
    have hQ168 : Nat.card Q = 168 := by omega
    rw [hQ168] at hPQ
    have h1 : Nat.card ψ.ker * 168 ∣ 3 * 168 := by rw [← hPQ]; simpa using hPdvd
    have h2 : Nat.card ψ.ker ∣ 3 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
    have hk1 : Nat.card ψ.ker = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
      · exact h
      · exact absurd (by rw [h]) hψker
    exact ⟨rfl, by rw [hPQ, hk1]⟩
  · exact (h8 rfl).elim
  · exact (hs3 (by norm_num)).elim
  ·
    norm_num at hQcard
    omega

theorem spor_local_lemma (hW : SporLocal W) {w : W} (hw : orderOf w = 3) {P : Subgroup W}
    (hP : P ≤ Subgroup.centralizer ({w} : Set W))
    (hsub : (P.subgroupOf (Subgroup.centralizer ({w} : Set W))).IsSubnormal)
    (hPp : Group.IsPerfect P) {Q : Type} [Group Q] [Finite Q] (hQs : IsSimpleGroup Q)
    (hQn : ∃ a b : Q, a * b ≠ b * a) (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (hψker : ¬ 3 ∣ Nat.card ψ.ker) {s : ℕ} (hs4 : 4 ≤ s) (hs3 : ¬ 3 ∣ s)
    (hQcard : Nat.card Q * Nat.gcd 2 (s - 1) = s * (s ^ 2 - 1)) :
    s = 7 ∧ Nat.card P = 168 := by
  rcases hW.threeCases w hw with ⟨hq, hZ⟩ | h504
  · exact (false_of_threeA hq hZ hP hsub hPp hQs hQn ψ hψ hψker).elim
  · exact spor_threeB hw h504 hP hQs hQn ψ hψ hψker hs4 hs3 hQcard

end Local

end CFSG.RankThree.PartTwo.Sec12.Hering129SP
