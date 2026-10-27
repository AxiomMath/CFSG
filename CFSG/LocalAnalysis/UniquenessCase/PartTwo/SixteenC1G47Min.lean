module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Rk2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

theorem s16c1_G47_min_basic {Hs : Type} [Group Hs] {S : Subgroup Hs}
    (hcl : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅⁅a, b⁆, c⁆ = 1) :
    ⁅S, S⁆ ≤ S ∧ (∀ c ∈ ⁅S, S⁆, ∀ s ∈ S, c * s = s * c) ∧
      ∀ g : Hs, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → ∀ c ∈ ⁅S, S⁆, g * c * g⁻¹ ∈ ⁅S, S⁆ := by
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def, mul_assoc]
      exact S.mul_mem (show a * b ∈ S from S.mul_mem ha hb)
        (show a⁻¹ * b⁻¹ ∈ S from S.mul_mem (S.inv_mem ha) (S.inv_mem hb))
  · intro c hc s hs
    have hZ : ⁅S, S⁆ ≤ Subgroup.centralizer ({s} : Set Hs) :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [Subgroup.mem_centralizer_singleton_iff, ← commutatorElement_eq_one_iff_mul_comm]
        exact hcl a ha b hb s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hZ hc)
  · intro g hg c hc
    have hZ : ⁅S, S⁆ ≤ (⁅S, S⁆).comap (MulAut.conj g).toMonoidHom :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [Subgroup.mem_comap]
        change MulAut.conj g ⁅a, b⁆ ∈ ⁅S, S⁆
        rw [MulAut.conj_apply, conjugate_commutatorElement]
        exact Subgroup.commutator_mem_commutator (hg a ha) (hg b hb)
    exact hZ hc

theorem s16c1_G47_min_fix {Hs : Type} [Group Hs] [Finite Hs] {Xs S : Subgroup Hs} {u : Hs}
    (hcl : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅⁅a, b⁆, c⁆ = 1)
    (hSX : ∀ x ∈ Xs, ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hSu : ∀ s ∈ S, u * s * u⁻¹ ∈ S)
    (hSnt : ∃ s ∈ S, u * s * u⁻¹ ≠ s)
    (hmin : ∀ T : Subgroup Hs, T ≤ S → (∀ x ∈ Xs, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      (∀ t ∈ T, u * t * u⁻¹ ∈ T) → (∃ t ∈ T, u * t * u⁻¹ ≠ t) → Nat.card S ≤ Nat.card T) :
    ∀ c ∈ ⁅S, S⁆, u * c * u⁻¹ = c := by
  obtain ⟨hZS, hZc, hZinv⟩ := s16c1_G47_min_basic hcl
  have hZX : ∀ x ∈ Xs, ∀ c ∈ ⁅S, S⁆, x * c * x⁻¹ ∈ ⁅S, S⁆ :=
    fun x hx => hZinv x (hSX x hx)
  have hZu : ∀ c ∈ ⁅S, S⁆, u * c * u⁻¹ ∈ ⁅S, S⁆ := hZinv u hSu
  intro c hc
  by_contra hne
  have hcardle : Nat.card (⁅S, S⁆ : Subgroup Hs) ≤ Nat.card S := Subgroup.card_le_of_le hZS
  have hminle : Nat.card S ≤ Nat.card (⁅S, S⁆ : Subgroup Hs) :=
    hmin ⁅S, S⁆ hZS hZX hZu ⟨c, hc, hne⟩
  have hZeq : ⁅S, S⁆ = S := Subgroup.eq_of_le_of_card_ge hZS hminle
  have hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    exact hZc a (hZeq.symm ▸ ha) b hb
  have hbot : ⁅S, S⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hab a ha b hb
  have hSbot : S = ⊥ := hZeq.symm.trans hbot
  obtain ⟨s, hs, hsu⟩ := hSnt
  have hs1 : s = 1 := Subgroup.mem_bot.mp (hSbot ▸ hs)
  refine hsu ?_
  rw [hs1]
  simp

theorem s16c1_G47_min_inv {Hs : Type} [Group Hs] [Finite Hs] {q : ℕ} (hq : Odd q)
    {Xs S : Subgroup Hs} {u : Hs} (hu2 : u * u = 1) (hux : ∀ x ∈ Xs, u * x = x * u)
    (hSq : ∀ s ∈ S, s ^ q = 1) (hcl : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅⁅a, b⁆, c⁆ = 1)
    (hSX : ∀ x ∈ Xs, ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hSu : ∀ s ∈ S, u * s * u⁻¹ ∈ S)
    (hSnt : ∃ s ∈ S, u * s * u⁻¹ ≠ s)
    (hmin : ∀ T : Subgroup Hs, T ≤ S → (∀ x ∈ Xs, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      (∀ t ∈ T, u * t * u⁻¹ ∈ T) → (∃ t ∈ T, u * t * u⁻¹ ≠ t) → Nat.card S ≤ Nat.card T)
    (hfix : ∀ c ∈ ⁅S, S⁆, u * c * u⁻¹ = c) :
    ∀ s ∈ S, u * s * u⁻¹ * s ∈ ⁅S, S⁆ := by
  classical
  obtain ⟨hZS, hZc, hZinv⟩ := s16c1_G47_min_basic hcl
  have hZX : ∀ x ∈ Xs, ∀ c ∈ ⁅S, S⁆, x * c * x⁻¹ ∈ ⁅S, S⁆ :=
    fun x hx => hZinv x (hSX x hx)
  have hZu : ∀ c ∈ ⁅S, S⁆, u * c * u⁻¹ ∈ ⁅S, S⁆ := hZinv u hSu
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hconj_uu : ∀ x : Hs, u * (u * x * u⁻¹) * u⁻¹ = x := by
    intro x
    have h : u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
    rw [h, hu2, one_mul, hu_inv, hu2, mul_one]
  have hswap : ∀ a ∈ S, ∀ s ∈ S, a * s ∈ ⁅S, S⁆ → s * a ∈ ⁅S, S⁆ := by
    intro a ha s hs has
    have h := hZc (a * s) has s hs
    have heq : a * s = s * a := mul_right_cancel (by
      calc (a * s) * s = s * (a * s) := h
        _ = (s * a) * s := by group)
    rw [← heq]
    exact has
  let Sminus : Subgroup Hs :=
    { carrier := {t | t ∈ S ∧ u * t * u⁻¹ * t ∈ ⁅S, S⁆}
      mul_mem' := fun {s t} hs ht => by
        obtain ⟨hsS, hsZ⟩ := hs
        obtain ⟨htS, htZ⟩ := ht
        refine ⟨S.mul_mem hsS htS, ?_⟩
        let a : Hs := u * s * u⁻¹
        let b : Hs := u * t * u⁻¹
        let k : Hs := ⁅b, s⁆
        have ha : a ∈ S := hSu s hsS
        have hb : b ∈ S := hSu t htS
        have hk : k ∈ ⁅S, S⁆ := Subgroup.commutator_mem_commutator hb hsS
        have hka : k * a = a * k := hZc k hk a ha
        have hbs : b * s = k * s * b := by
          dsimp only [k]
          rw [commutatorElement_def]
          group
        have hconj : u * (s * t) * u⁻¹ = a * b := by
          dsimp only [a, b]
          group
        have hgoal : a * b * (s * t) = k * ((a * s) * (b * t)) := by
          have h1 : a * b * (s * t) = a * (b * s) * t := by group
          have h2 : a * (b * s) * t = a * (k * s * b) * t := by rw [hbs]
          have h3 : a * (k * s * b) * t = (a * k) * (s * b) * t := by group
          have h4 : (a * k) * (s * b) * t = (k * a) * (s * b) * t := by rw [← hka]
          have h5 : (k * a) * (s * b) * t = k * ((a * s) * (b * t)) := by group
          exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
        rw [hconj, hgoal]
        exact (⁅S, S⁆).mul_mem hk ((⁅S, S⁆).mul_mem hsZ htZ)
      one_mem' := ⟨S.one_mem, by simpa using (⁅S, S⁆).one_mem⟩
      inv_mem' := fun {t} ht => by
        obtain ⟨htS, htZ⟩ := ht
        refine ⟨S.inv_mem htS, ?_⟩
        have ha : u * t * u⁻¹ ∈ S := hSu t htS
        have hconj : u * t⁻¹ * u⁻¹ = (u * t * u⁻¹)⁻¹ := by group
        have h2 : (u * t * u⁻¹)⁻¹ * t⁻¹ = (t * (u * t * u⁻¹))⁻¹ := by group
        have hsw : t * (u * t * u⁻¹) ∈ ⁅S, S⁆ :=
          hswap (u * t * u⁻¹) ha t htS htZ
        rw [hconj, h2]
        exact (⁅S, S⁆).inv_mem hsw }
  have hSminus_le : Sminus ≤ S := fun t ht => ht.1
  have hSminusX : ∀ x ∈ Xs, ∀ t ∈ Sminus, x * t * x⁻¹ ∈ Sminus := by
    intro x hx t ht
    have htS : t ∈ S := ht.1
    have htZ : u * t * u⁻¹ * t ∈ ⁅S, S⁆ := ht.2
    have hc_x : u * x * u⁻¹ = x := by rw [hux x hx]; group
    have hconj : u * (x * t * x⁻¹) * u⁻¹ = x * (u * t * u⁻¹) * x⁻¹ := by
      calc u * (x * t * x⁻¹) * u⁻¹
          = (u * x * u⁻¹) * (u * t * u⁻¹) * (u * x * u⁻¹)⁻¹ := by group
        _ = x * (u * t * u⁻¹) * x⁻¹ := by rw [hc_x]
    refine ⟨hSX x hx t htS, ?_⟩
    rw [hconj]
    have hxconj : x * (u * t * u⁻¹) * x⁻¹ * (x * t * x⁻¹)
        = x * ((u * t * u⁻¹) * t) * x⁻¹ := by group
    rw [hxconj]
    exact hZX x hx ((u * t * u⁻¹) * t) htZ
  have hSminusU : ∀ t ∈ Sminus, u * t * u⁻¹ ∈ Sminus := by
    intro t ht
    have htS : t ∈ S := ht.1
    have htZ : u * t * u⁻¹ * t ∈ ⁅S, S⁆ := ht.2
    refine ⟨hSu t htS, ?_⟩
    rw [hconj_uu t]
    exact hswap (u * t * u⁻¹) (hSu t htS) t htS htZ
  have hSle : S ≤ Sminus := by
    by_contra hnot
    have hlt : Sminus < S := by
      refine lt_of_le_of_ne hSminus_le ?_
      intro heq
      exact hnot (le_of_eq heq.symm)
    have hcardlt : Nat.card Sminus < Nat.card S := Subgroup.card_lt_of_lt hlt
    have htriv : ∀ t ∈ Sminus, u * t * u⁻¹ = t := by
      intro t ht
      by_contra hne
      have hle := hmin Sminus hSminus_le hSminusX hSminusU ⟨t, ht, hne⟩
      exact absurd hle (not_le.mpr hcardlt)
    obtain ⟨m, rfl⟩ := hq
    have hSminusZ : Sminus ≤ ⁅S, S⁆ := by
      intro t ht
      have htS : t ∈ S := ht.1
      have httZ : t * t ∈ ⁅S, S⁆ := by
        have h := ht.2
        rwa [htriv t ht] at h
      have hpow : (t * t) ^ m * t = 1 := by
        have h2 : t ^ (2 * m + 1) = 1 := hSq t htS
        rwa [pow_succ, pow_mul, sq] at h2
      have ht_eq : t = ((t * t) ^ m)⁻¹ := by
        conv_lhs => rw [← inv_mul_cancel_left ((t * t) ^ m) t]
        rw [hpow, mul_one]
      rw [ht_eq]
      exact (⁅S, S⁆).inv_mem ((⁅S, S⁆).pow_mem httZ m)
    obtain ⟨s, hs, hsu⟩ := hSnt
    let a : Hs := u * s * u⁻¹
    let w : Hs := s * a⁻¹
    let c' : Hs := a * s⁻¹
    have ha : a ∈ S := hSu s hs
    have hw : w ∈ S := S.mul_mem hs (S.inv_mem ha)
    have hconja : u * a * u⁻¹ = s := by
      dsimp only [a]
      exact hconj_uu s
    have hconja_inv : u * a⁻¹ * u⁻¹ = s⁻¹ := by
      calc u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
        _ = s⁻¹ := by rw [hconja]
    have hconjw : u * w * u⁻¹ = a * s⁻¹ := by
      have h1 : u * w * u⁻¹ = (u * s * u⁻¹) * (u * a⁻¹ * u⁻¹) := by
        dsimp only [w]
        group
      rw [h1, hconja_inv]
    have hwZmem : u * w * u⁻¹ * w ∈ ⁅S, S⁆ := by
      rw [hconjw]
      have hone : a * s⁻¹ * w = 1 := by
        dsimp only [w]
        group
      rw [hone]
      exact (⁅S, S⁆).one_mem
    have hwZ : w ∈ ⁅S, S⁆ := hSminusZ ⟨hw, hwZmem⟩
    have hc'Z : c' ∈ ⁅S, S⁆ := by
      have hc'inv : c' = w⁻¹ := by
        dsimp only [c', w]
        group
      rw [hc'inv]
      exact (⁅S, S⁆).inv_mem hwZ
    have hc'fix : u * c' * u⁻¹ = c' := hfix c' hc'Z
    have ha_eq : a = c' * s := by
      dsimp only [a, c']
      group
    have heq1 : s = c' * c' * s := by
      calc s = u * a * u⁻¹ := hconja.symm
        _ = u * (c' * s) * u⁻¹ := by rw [ha_eq]
        _ = (u * c' * u⁻¹) * (u * s * u⁻¹) := by group
        _ = c' * a := by dsimp only [a]; rw [hc'fix]
        _ = c' * (c' * s) := by rw [ha_eq]
        _ = c' * c' * s := by group
    have hc'2 : c' * c' = 1 := by
      have h : (c' * c') * s = 1 * s := by
        rw [one_mul]
        exact heq1.symm
      exact mul_right_cancel h
    have hc'one : c' = 1 := by
      have hc'q : c' ^ (2 * m + 1) = 1 := hSq c' (hZS hc'Z)
      have hc'pow : (c' * c') ^ m * c' = 1 := by
        rwa [pow_succ, pow_mul, sq] at hc'q
      rw [hc'2, one_pow, one_mul] at hc'pow
      exact hc'pow
    have ha_eq_s : a = s := by
      rw [ha_eq, hc'one, one_mul]
    exact hsu ha_eq_s
  intro s hs
  exact (hSle hs).2

theorem s16c1_G47_min_noncyclic {Hs : Type} [Group Hs] [Finite Hs] {Xs S : Subgroup Hs} {u : Hs}
    (hXp : Group.IsPerfect Xs) (hA9 : ∀ c : Hs, (∀ x ∈ Xs, c * x = x * c) → c * u = u * c)
    (hcl : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅⁅a, b⁆, c⁆ = 1)
    (hSX : ∀ x ∈ Xs, ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hSnt : ∃ s ∈ S, u * s * u⁻¹ ≠ s) :
    ¬ ∃ s ∈ S, S ≤ ⁅S, S⁆ ⊔ Subgroup.zpowers s := by
  obtain ⟨hZS, hZc, _⟩ := s16c1_G47_min_basic hcl
  rintro ⟨s, hsS, hle⟩
  have hZcent : ⁅S, S⁆ ≤ Subgroup.centralizer ({s} : Set Hs) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hZc c hc s hsS
  have hzcent : Subgroup.zpowers s ≤ Subgroup.centralizer ({s} : Set Hs) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hsupc : ⁅S, S⁆ ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({s} : Set Hs) :=
    sup_le hZcent hzcent
  have hscent : ∀ a ∈ S, a * s = s * a := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsupc (hle ha))
  have hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have hZcent_a : ⁅S, S⁆ ≤ Subgroup.centralizer ({a} : Set Hs) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hZc c hc a ha
    have hzcent_a : Subgroup.zpowers s ≤ Subgroup.centralizer ({a} : Set Hs) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hscent a ha).symm)
    have hsupc_a : ⁅S, S⁆ ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({a} : Set Hs) :=
      sup_le hZcent_a hzcent_a
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hsupc_a (hle hb))).symm
  have hZbot : ⁅S, S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => hab b hb a ha
  have hSle_z : S ≤ Subgroup.zpowers s := by
    have h := hle
    rwa [hZbot, bot_sup_eq] at h
  have hzS : Subgroup.zpowers s ≤ S := Subgroup.zpowers_le.mpr hsS
  have hSeq : S = Subgroup.zpowers s := le_antisymm hSle_z hzS
  have hScyc : IsCyclic ↥S := hSeq.symm ▸ Subgroup.isCyclic_zpowers s
  have hXS : Xs ≤ Subgroup.normalizer (S : Set Hs) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact Subgroup.commutator_le.mpr fun x hx c hc => by
      rw [commutatorElement_def]
      exact S.mul_mem (hSX x hx c hc) (S.inv_mem hc)
  have hper := s16c1_G47_perfect_cyclic hXp hXS hScyc
  have hsX : ∀ x ∈ Xs, s * x = x * s := by
    intro x hx
    have h := hper x hx s hsS
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hsu : u * s * u⁻¹ = s := by
    have h := hA9 s hsX
    rw [← h]
    group
  obtain ⟨t, ht, hne⟩ := hSnt
  have htz : t ∈ Subgroup.zpowers s := hSeq ▸ ht
  have ht_triv : u * t * u⁻¹ = t := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp htz
    rw [← conj_zpow, hsu]
  exact hne ht_triv

theorem s16c1_G47_min {Hs : Type} [Group Hs] [Finite Hs] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Xs D : Subgroup Hs} (hXp : Group.IsPerfect Xs) {u : Hs} (hu2 : u * u = 1)
    (hux : ∀ x ∈ Xs, u * x = x * u)
    (hA9 : ∀ c : Hs, (∀ x ∈ Xs, c * x = x * c) → c * u = u * c)
    (hDq : ∀ d ∈ D, d ^ q = 1) (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅⁅a, b⁆, c⁆ = 1)
    (hDX : ∀ x ∈ Xs, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hDu : ∀ d ∈ D, u * d * u⁻¹ ∈ D)
    (hDnt : ∃ d ∈ D, u * d * u⁻¹ ≠ d) (hr : CFSG.Open.pRank q (⊤ : Subgroup Hs) ≤ 2) :
    ∃ S Z : Subgroup Hs, S ≤ D ∧ Z ≤ S ∧ (∀ s ∈ S, u * s * u⁻¹ ∈ S) ∧
      (∃ s ∈ S, u * s * u⁻¹ ≠ s) ∧ (∀ s ∈ S, u * s * u⁻¹ * s ∈ Z) ∧
      (∀ c ∈ Z, ∀ s ∈ S, c * s = s * c) ∧ (∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Z) ∧
      (∀ c ∈ Z, u * c = c * u) ∧ (∀ c ∈ Z, ∀ x ∈ Xs, c * x = x * c) ∧
      ¬ ∃ s ∈ S, S ≤ Z ⊔ Subgroup.zpowers s := by
  classical
  have hodd : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  let P : ℕ → Prop := fun n => ∃ T : Subgroup Hs, T ≤ D ∧ (∀ x ∈ Xs, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
    (∀ t ∈ T, u * t * u⁻¹ ∈ T) ∧ (∃ t ∈ T, u * t * u⁻¹ ≠ t) ∧ Nat.card T = n
  have hex : ∃ n, P n := ⟨Nat.card D, D, le_rfl, hDX, hDu, hDnt, rfl⟩
  obtain ⟨S, hSD, hSX, hSu, hSnt, hSn⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subgroup Hs, T ≤ S → (∀ x ∈ Xs, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      (∀ t ∈ T, u * t * u⁻¹ ∈ T) → (∃ t ∈ T, u * t * u⁻¹ ≠ t) → Nat.card S ≤ Nat.card T := by
    intro T hTS hTX hTu hTnt
    rw [hSn]
    exact Nat.find_min' hex ⟨T, hTS.trans hSD, hTX, hTu, hTnt, rfl⟩
  have hSq : ∀ s ∈ S, s ^ q = 1 := fun s hs => hDq s (hSD hs)
  have hScl : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅⁅a, b⁆, c⁆ = 1 := fun a ha b hb c hc =>
    hDcl a (hSD ha) b (hSD hb) c (hSD hc)
  obtain ⟨hZS, hZc, hZinv⟩ := s16c1_G47_min_basic hScl
  have hfix := s16c1_G47_min_fix hScl hSX hSu hSnt hmin
  have hinv := s16c1_G47_min_inv hodd hu2 hux hSq hScl hSX hSu hSnt hmin hfix
  have hnc := s16c1_G47_min_noncyclic hXp hA9 hScl hSX hSnt
  have hZcyc : IsCyclic ↥⁅S, S⁆ := s16c1_G47_comm_card_le hq hSq hScl hr
  have hXZ : Xs ≤ normalizer ((⁅S, S⁆ : Subgroup Hs) : Set Hs) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hZinv x (hSX x hx) c hc, fun hc => ?_⟩
    have h := hZinv x⁻¹ (hSX x⁻¹ (Xs.inv_mem hx)) _ hc
    simpa [mul_assoc] using h
  have hXZc := s16c1_G47_perfect_cyclic hXp hXZ hZcyc
  refine ⟨S, ⁅S, S⁆, hSD, hZS, hSu, hSnt, hinv, hZc, ?_, ?_, ?_, hnc⟩
  · intro s hs t ht
    simpa [commutatorElement_def] using Subgroup.commutator_mem_commutator hs ht
  · intro c hc
    have h := hfix c hc
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  · intro c hc x hx
    have h := hXZc x hx c hc
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
