module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34Perm
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelSmallOrders
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingPlaneCore
import CFSG.Milestones.ASVolI.C31.J4NP.Enc
import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsL3)

private lemma prime_pow_dvd_180_le_nine {r k : ℕ} (hr : r.Prime) (h : r ^ k ∣ 180) :
    r ^ k ≤ 9 := by
  rcases k with _ | k
  · norm_num
  have hrdvd : r ∣ 180 := (dvd_pow_self r (Nat.succ_ne_zero k)).trans h
  have hr235 : r = 2 ∨ r = 3 ∨ r = 5 := by
    have h1 : r ∣ 2 ^ 2 * 3 ^ 2 * 5 := by
      norm_num at hrdvd ⊢
      exact hrdvd
    rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h5
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 5)).mp h5))
  have hk : k ≤ 6 := by
    have hle : 2 ^ (k + 1) ≤ r ^ (k + 1) := Nat.pow_le_pow_left hr.two_le (k + 1)
    have h180 : r ^ (k + 1) ≤ 180 := Nat.le_of_dvd (by norm_num) h
    have h2 : 2 ^ (k + 1) ≤ 180 := le_trans hle h180
    by_contra hk
    have h8 : 8 ≤ k + 1 := by omega
    have h256 : 256 ≤ 2 ^ (k + 1) := by
      have h256' := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h8
      norm_num at h256' ⊢
      exact h256'
    omega
  rcases hr235 with rfl | rfl | rfl <;> interval_cases k <;> norm_num at h
  all_goals norm_num

private lemma eq_of_dvd_of_modEq_seven {m d : ℕ} (hmpos : 0 < m) (hm : m ≤ 9)
    (hm180 : m ∣ 180) (hdvd : d ∣ m) (hmod : d ≡ m [MOD 7]) : d = m := by
  by_contra hne
  have hd_le : d ≤ m := Nat.le_of_dvd hmpos hdvd
  have hd_lt : d < m := lt_of_le_of_ne hd_le hne
  have h7 : 7 ∣ m - d := (Nat.modEq_iff_dvd' hd_le).mp hmod
  obtain ⟨k, hk⟩ := h7
  have hdiff : m - d = 7 := by
    have hpos : 0 < m - d := Nat.sub_pos_of_lt hd_lt
    have hle : m - d ≤ 9 := (Nat.sub_le m d).trans hm
    omega
  have hd7 : d ∣ 7 := by
    have hsub : d ∣ m - d := Nat.dvd_sub hdvd (dvd_refl d)
    rwa [hdiff] at hsub
  have hd1 : d = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd7 with h | h
    · exact h
    · omega
  have hm8 : m = 8 := by omega
  rw [hm8] at hm180
  norm_num at hm180

private lemma exists_invariant_sylow_aut {Y : Type*} [Group Y] [Finite Y]
    {N : Subgroup Y} [N.Normal] {x : Y} (hx : orderOf x = 7) (hN7 : ¬ 7 ∣ Nat.card N)
    {r : ℕ} [hr : Fact r.Prime] :
    ∃ (P : Sylow r N) (ψ : MulAut ↥P), ψ ^ 7 = 1 ∧
      (P : Subgroup N).map (MulAut.conjNormal x).toMonoidHom = P ∧
      (∀ p : ↥P, (ψ p).val = (MulAut.conjNormal x) p.val) := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let X7 : Subgroup Y := Subgroup.zpowers x
  have hX7card : Nat.card X7 = 7 := by rw [Nat.card_zpowers, hx]
  have hX7p : IsPGroup 7 X7 := IsPGroup.of_card (n := 1) (by rw [hX7card]; norm_num)
  let ρ : X7 →* MulAut N := (MulAut.conjNormal (H := N)).comp (Subgroup.subtype X7)
  let gx : X7 := ⟨x, Subgroup.mem_zpowers x⟩
  have hgxord : orderOf gx = 7 := by rw [Subgroup.orderOf_mk, hx]
  have hgx7 : gx ^ 7 = 1 := by rw [← hgxord]; exact pow_orderOf_eq_one gx
  obtain ⟨P, hP⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime
    (actor := X7) (group := N) 7 r hX7p hN7 ρ
  let Ψ : X7 →* MulAut ↥P :=
    CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism ρ (P : Subgroup N) hP
  let ψ : MulAut ↥P := Ψ gx
  have hψ7 : ψ ^ 7 = 1 := by
    change Ψ gx ^ 7 = 1
    rw [← map_pow, hgx7, map_one]
  have hPgen' : (P : Subgroup N).map (MulAut.conjNormal x).toMonoidHom = P := by
    have h := hP gx
    simpa [ρ, gx] using h
  have hψapply : ∀ p : ↥P, (ψ p).val = (MulAut.conjNormal x) p.val := by
    intro p
    rw [show ψ = CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
      (ρ gx) (P : Subgroup N) (hP gx) from rfl,
      CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_apply]
    rfl
  exact ⟨P, ψ, hψ7, hPgen', hψapply⟩

private lemma sylow_le_fixed_of_order_seven {Y : Type*} [Group Y] [Finite Y]
    {N : Subgroup Y} [N.Normal] {x : Y} (hx : orderOf x = 7) (hN7 : ¬ 7 ∣ Nat.card N)
    (hN180 : Nat.card N ∣ 180) {r : ℕ} [hr : Fact r.Prime] :
    ∃ P : Sylow r N, (P : Subgroup N) ≤
      (MulAut.conjNormal x).toMonoidHom.eqLocus (MonoidHom.id N) := by
  obtain ⟨P, ψ, hψ7, hPgen, hψapply⟩ := exists_invariant_sylow_aut (r := r) hx hN7
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPfin : Fintype ↥P := Fintype.ofFinite ↥P
  have hPdec : DecidableEq ↥P := Classical.decEq ↥P
  let σ : Equiv.Perm ↥P := MulAut.toPerm ↥P ψ
  have hσ7 : σ ^ 7 = 1 := by rw [← map_pow, hψ7, map_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥P)
    (f := (⇑σ : Function.End ↥P)) (p := 7) (n := 1) (by
      rw [pow_one]
      have h2 := Equiv.Perm.coe_pow σ 7
      rw [hσ7, Equiv.Perm.coe_one] at h2
      exact h2.symm)
  let F : Subgroup ↥P := ψ.toMonoidHom.eqLocus (MonoidHom.id ↥P)
  have hFcard : Nat.card (Function.fixedPoints (⇑σ)) = Nat.card ↥F := rfl
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  rw [hFcard] at hmod
  have hdvd : Nat.card ↥F ∣ Nat.card ↥P := F.card_subgroup_dvd_card
  have hpoweq : Nat.card ↥P = r ^ (Nat.card N).factorization r :=
    Sylow.card_eq_multiplicity P
  have hPdiv : Nat.card ↥P ∣ 180 :=
    (Subgroup.card_subgroup_dvd_card (P : Subgroup N)).trans hN180
  have hm9 : Nat.card ↥P ≤ 9 := by
    have h' : r ^ (Nat.card N).factorization r ∣ 180 := by rwa [hpoweq] at hPdiv
    have h9 := prime_pow_dvd_180_le_nine hr.out h'
    rwa [hpoweq]
  have hreq : Nat.card ↥F = Nat.card ↥P :=
    eq_of_dvd_of_modEq_seven (Nat.card_pos) hm9 hPdiv hdvd hmod.symm
  have hFtop : F = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hreq]
  refine ⟨P, ?_⟩
  intro p hp
  show (MulAut.conjNormal x) p = p
  have hpF : (⟨p, hp⟩ : ↥P) ∈ F := by rw [hFtop]; exact Subgroup.mem_top _
  have hfix : ψ ⟨p, hp⟩ = ⟨p, hp⟩ := hpF
  have hval := congrArg Subtype.val hfix
  rw [hψapply] at hval
  exact hval

private lemma centralizes_of_order_seven {Y : Type*} [Group Y] [Finite Y]
    {N : Subgroup Y} [N.Normal] {x : Y} (hx : orderOf x = 7) (hN7 : ¬ 7 ∣ Nat.card N)
    (hN180 : Nat.card N ∣ 180) : ∀ n : N, MulAut.conjNormal x n = n := by
  let C : Subgroup N := (MulAut.conjNormal x).toMonoidHom.eqLocus (MonoidHom.id N)
  have hCtop : C = ⊤ := by
    refine CFSG.ASVolI.burnsideJ4NP_eq_of_le_of_primePow_dvd
      (G := N) (L := C) (K := ⊤) le_top ?_
    intro p hp hpK
    have hpdvd : p ∣ Nat.card N := by simpa using hpK
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := sylow_le_fixed_of_order_seven (Y := Y) (N := N) (x := x)
      hx hN7 hN180 (r := p)
    have hPcard : Nat.card ↥(P : Subgroup N) = p ^ (Nat.card N).factorization p :=
      Sylow.card_eq_multiplicity P
    have hdvdC : Nat.card ↥(P : Subgroup N) ∣ Nat.card ↥C := Subgroup.card_dvd_of_le hP
    rw [Subgroup.card_top, ← hPcard]
    exact hdvdC
  intro n
  have hn : n ∈ C := by rw [hCtop]; exact Subgroup.mem_top n
  exact hn

private lemma exists_centralizing_cycle_of_section {Y : Subgroup (Equiv.Perm (Fin 10))}
    (N : Subgroup ↥Y) [N.Normal] (hL34 : IsL3 (↥Y ⧸ N) 2) :
    ∃ x : ↥Y, orderOf x = 7 ∧ (¬ 7 ∣ Nat.card ↥N) ∧
      (∀ n : N, MulAut.conjNormal x n = n) ∧
      ((x : ↥Y) : Equiv.Perm (Fin 10)).IsCycle ∧
      ((x : ↥Y) : Equiv.Perm (Fin 10)).support.card = 7 := by
  have hTcard : Nat.card (↥Y ⧸ N) = 20160 :=
    CFSG.Blueprint.LieModel.card_psl_three_four hL34
  have hHcard : Nat.card ↥Y = 20160 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hTcard]
  have hYdvd : Nat.card ↥Y ∣ Nat.card (Equiv.Perm (Fin 10)) :=
    Subgroup.card_subgroup_dvd_card Y
  have hPermCard : Nat.card (Equiv.Perm (Fin 10)) = 3628800 := by
    rw [Nat.card_perm]
    norm_num
  have hN180 : Nat.card N ∣ 180 := by
    rw [hHcard, hPermCard] at hYdvd
    obtain ⟨k, hk⟩ := hYdvd
    refine ⟨k, ?_⟩
    have h : 20160 * (Nat.card N * k) = 20160 * 180 := by
      rw [← mul_assoc, ← hk]
    exact (Nat.mul_left_cancel (by norm_num) h).symm
  have hN7 : ¬ 7 ∣ Nat.card N := by
    intro h7
    have h : 7 ∣ 180 := h7.trans hN180
    norm_num at h
  have h7fact : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hY7 : 7 ∣ Nat.card ↥Y := by
    rw [hHcard]
    exact dvd_mul_of_dvd_left (by norm_num : 7 ∣ 20160) (Nat.card N)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 7 hY7
  have hcent : ∀ n : N, MulAut.conjNormal x n = n :=
    centralizes_of_order_seven (Y := ↥Y) (N := N) (x := x) hxord hN7 hN180
  have hxGord : orderOf ((x : ↥Y) : Equiv.Perm (Fin 10)) = 7 := by
    rw [Subgroup.orderOf_coe, hxord]
  have hxcycle : ((x : ↥Y) : Equiv.Perm (Fin 10)).IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order ?_ ?_
    · rw [hxGord]; norm_num
    · rw [hxGord]
      have hle := Finset.card_le_univ ((x : ↥Y) : Equiv.Perm (Fin 10)).support
      have hle' : ((x : ↥Y) : Equiv.Perm (Fin 10)).support.card ≤ 10 := by simpa using hle
      omega
  have hxsupp : ((x : ↥Y) : Equiv.Perm (Fin 10)).support.card = 7 := by
    rw [← hxcycle.orderOf, hxGord]
  exact ⟨x, hxord, hN7, hcent, hxcycle, hxsupp⟩

private lemma support_subset_fixedPoints {Y : Subgroup (Equiv.Perm (Fin 10))}
    (N : Subgroup ↥Y) [N.Normal] {x : ↥Y} (hN7 : ¬ 7 ∣ Nat.card ↥N)
    (hcent : ∀ n : N, MulAut.conjNormal x n = n)
    (hxGord : orderOf ((x : ↥Y) : Equiv.Perm (Fin 10)) = 7)
    (hxcycle : ((x : ↥Y) : Equiv.Perm (Fin 10)).IsCycle) :
    ∀ a : Fin 10, a ∈ ((x : ↥Y) : Equiv.Perm (Fin 10)).support →
      a ∈ MulAction.fixedPoints N (Fin 10) := by
  intro a ha
  rw [MulAction.mem_fixedPoints]
  intro n
  have hcomm : Commute (((n : ↥Y) : Equiv.Perm (Fin 10)))
      ((x : ↥Y) : Equiv.Perm (Fin 10)) := by
    have hxn : (x : ↥Y) * (n : ↥Y) = (n : ↥Y) * (x : ↥Y) := by
      have h1 : (x : ↥Y) * (n : ↥Y) * (x : ↥Y)⁻¹ = (n : ↥Y) := by
        have hcn := congrArg Subtype.val (hcent n)
        simpa [MulAut.conjNormal_apply] using hcn
      calc (x : ↥Y) * (n : ↥Y) =
          ((x : ↥Y) * (n : ↥Y) * (x : ↥Y)⁻¹) * (x : ↥Y) := by group
        _ = (n : ↥Y) * (x : ↥Y) := by rw [h1]
    exact congrArg (fun y : ↥Y => (y : Equiv.Perm (Fin 10))) hxn.symm
  have hn7 : ¬ 7 ∣ orderOf (((n : ↥Y) : Equiv.Perm (Fin 10))) := by
    intro h7
    have hdvd : orderOf (((n : ↥Y) : Equiv.Perm (Fin 10))) ∣ Nat.card ↥N := by
      rw [Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard N n.2
    exact hN7 (h7.trans hdvd)
  have hfix := CFSG.RankThree.GroupTheory.apply_eq_self_of_commute_isCycle
    (p := 7) (by norm_num) hxcycle hxGord hcomm hn7 ha
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

private lemma fixedPoints_compl_card {Y : Subgroup (Equiv.Perm (Fin 10))}
    (N : Subgroup ↥Y) [N.Normal] {x : ↥Y}
    (hxsupp : ((x : ↥Y) : Equiv.Perm (Fin 10)).support.card = 7)
    (hsupp : ∀ a : Fin 10, a ∈ ((x : ↥Y) : Equiv.Perm (Fin 10)).support →
      a ∈ MulAction.fixedPoints N (Fin 10)) :
    Nat.card ↥((MulAction.fixedPoints N (Fin 10))ᶜ) ≤ 3 ∧
      Nat.card ↥(MulAction.fixedPoints N (Fin 10)) < 16 := by
  set xG : Equiv.Perm (Fin 10) := ((x : ↥Y) : Equiv.Perm (Fin 10)) with hxG
  have hsubset : (xG.support : Set (Fin 10)) ⊆ MulAction.fixedPoints N (Fin 10) := hsupp
  have hcompl : ((xG.support : Set (Fin 10))ᶜ).ncard = 3 := by
    rw [← Finset.coe_compl, Set.ncard_coe_finset, Finset.card_compl, hxG, hxsupp]
    norm_num
  have hSigmacard : Nat.card ↥((MulAction.fixedPoints N (Fin 10))ᶜ) ≤ 3 := by
    rw [Nat.card_coe_set_eq]
    have hsub : (MulAction.fixedPoints N (Fin 10))ᶜ ⊆ (xG.support : Set (Fin 10))ᶜ := by
      intro a ha
      simp only [Set.mem_compl_iff] at ha ⊢
      exact fun hx => ha (hsubset hx)
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (le_of_eq hcompl)
  have hΩlt : Nat.card ↥(MulAction.fixedPoints N (Fin 10)) < 16 := by
    have hle : Nat.card ↥(MulAction.fixedPoints N (Fin 10)) ≤ 10 := by
      have h := Nat.card_le_card_of_injective
        (fun a : ↥(MulAction.fixedPoints N (Fin 10)) => (a : Fin 10)) Subtype.val_injective
      simpa using h
    omega
  exact ⟨hSigmacard, hΩlt⟩

private def fixedPointsAction {Y : Subgroup (Equiv.Perm (Fin 10))} (N : Subgroup ↥Y) [N.Normal]
    (Ω : Set (Fin 10)) (hΩ : Ω = MulAction.fixedPoints N (Fin 10)) :
    ↥Y →* Equiv.Perm ↥Ω :=
  { toFun := fun h => Equiv.Perm.subtypePerm (h : Equiv.Perm (Fin 10)) (fun a => by
      have hmem : ∀ (h : ↥Y) (a : Fin 10),
          h • a ∈ MulAction.fixedPoints N (Fin 10) ↔
            a ∈ MulAction.fixedPoints N (Fin 10) := by
        intro h a
        constructor
        · intro ha
          have h' := smul_mem_fixedPoints_of_normal h⁻¹ ha
          simpa using h'
        · exact smul_mem_fixedPoints_of_normal h
      rw [hΩ]
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hmem h a)
    map_one' := by ext a; rfl
    map_mul' := by intro h1 h2; ext a; rfl }

private lemma kernel_fixes_fixedPoints {Y : Subgroup (Equiv.Perm (Fin 10))}
    (N : Subgroup ↥Y) [N.Normal] (Ω : Set (Fin 10))
    (hΩ : Ω = MulAction.fixedPoints N (Fin 10)) :
    ∀ k : (fixedPointsAction N Ω hΩ).ker, ∀ a : Fin 10, a ∈ Ω →
      ((k : ↥Y) : Equiv.Perm (Fin 10)) a = a := by
  intro k a ha
  have hk1 : fixedPointsAction N Ω hΩ (k : ↥Y) = 1 := MonoidHom.mem_ker.mp k.2
  have hcongr := congrArg (fun p : Equiv.Perm ↥Ω => p ⟨a, ha⟩) hk1
  have hv := congrArg Subtype.val hcongr
  simpa [fixedPointsAction, Equiv.Perm.subtypePerm_apply] using hv

private lemma normal_le_kernel {Y : Subgroup (Equiv.Perm (Fin 10))}
    (N : Subgroup ↥Y) [N.Normal] (Ω : Set (Fin 10))
    (hΩ : Ω = MulAction.fixedPoints N (Fin 10)) :
    N ≤ (fixedPointsAction N Ω hΩ).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  ext a
  have hfix : n • (a : Fin 10) = (a : Fin 10) := by
    have ha' : (a : Fin 10) ∈ MulAction.fixedPoints N (Fin 10) := by
      rw [← hΩ]
      exact a.2
    have h := (MulAction.mem_fixedPoints.mp ha') ⟨n, hn⟩
    simpa [Subgroup.smul_def] using h
  have hfix' : ((n : ↥Y) : Equiv.Perm (Fin 10)) (a : Fin 10) = (a : Fin 10) := by
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix
  simpa [fixedPointsAction, Equiv.Perm.subtypePerm_apply] using
    congrArg (fun z : Fin 10 => (z : ℕ)) hfix'

private lemma kernel_card_le_six {Y : Subgroup (Equiv.Perm (Fin 10))}
    (N : Subgroup ↥Y) [N.Normal] (Ω : Set (Fin 10))
    (hΩ : Ω = MulAction.fixedPoints N (Fin 10))
    (hSigmacard : Nat.card ↥(Ωᶜ) ≤ 3) :
    Nat.card ↥((fixedPointsAction N Ω hΩ).ker) ≤ 6 := by
  have hΩinv : ∀ (h : ↥Y) (a : Fin 10), h • a ∈ Ω ↔ a ∈ Ω := by
    intro h a
    rw [hΩ]
    constructor
    · intro ha
      have h' := smul_mem_fixedPoints_of_normal h⁻¹ ha
      simpa using h'
    · exact smul_mem_fixedPoints_of_normal h
  let σ : (fixedPointsAction N Ω hΩ).ker → Equiv.Perm ↥(Ωᶜ) := fun k =>
    Equiv.Perm.subtypePerm ((k : ↥Y) : Equiv.Perm (Fin 10)) (fun a => by
      have := not_congr (hΩinv (k : ↥Y) a)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using this)
  have hinj : Function.Injective σ := by
    intro k1 k2 hk
    apply Subtype.ext
    ext a
    by_cases ha : a ∈ Ω
    · rw [kernel_fixes_fixedPoints N Ω hΩ k1 a ha, kernel_fixes_fixedPoints N Ω hΩ k2 a ha]
    · have hcongr := congrArg (fun p : Equiv.Perm ↥(Ωᶜ) => p ⟨a, ha⟩) hk
      have hv : ((k1 : ↥Y) : Equiv.Perm (Fin 10)) a = ((k2 : ↥Y) : Equiv.Perm (Fin 10)) a := by
        simpa [σ, Equiv.Perm.subtypePerm_apply] using hcongr
      simpa using congrArg (fun z : Fin 10 => (z : ℕ)) hv
  have hle := Nat.card_le_card_of_injective σ hinj
  rw [Nat.card_perm] at hle
  have hfac : Nat.factorial (Nat.card ↥(Ωᶜ)) ≤ 6 := by
    set n := Nat.card ↥(Ωᶜ) with hn
    interval_cases n <;> norm_num
  exact hle.trans hfac

private lemma kernel_ne_top {Y : Subgroup (Equiv.Perm (Fin 10))}
    (N : Subgroup ↥Y) [N.Normal] (Ω : Set (Fin 10))
    (hΩ : Ω = MulAction.fixedPoints N (Fin 10)) (hYlarge : 20160 ≤ Nat.card ↥Y)
    (hKcard : Nat.card ↥((fixedPointsAction N Ω hΩ).ker) ≤ 6) :
    (fixedPointsAction N Ω hΩ).ker ≠ ⊤ := by
  intro hKtop
  have hKcardH : Nat.card ↥((fixedPointsAction N Ω hΩ).ker) = Nat.card ↥Y := by
    rw [hKtop]
    simp
  have h6 : Nat.card ↥((fixedPointsAction N Ω hΩ).ker) ≤ 6 := hKcard
  rw [hKcardH] at h6
  omega

private lemma kernel_eq_normal {Y : Subgroup (Equiv.Perm (Fin 10))}
    {N : Subgroup ↥Y} [N.Normal] (K : Subgroup ↥Y) [K.Normal]
    (hTsimple : IsSimpleGroup (↥Y ⧸ N)) (hNK : N ≤ K) (hKne : K ≠ ⊤) : K = N := by
  have : IsSimpleGroup (↥Y ⧸ N) := hTsimple
  let π : ↥Y →* ↥Y ⧸ N := QuotientGroup.mk' N
  let L : Subgroup (↥Y ⧸ N) := K.map π
  have hLnorm : L.Normal :=
    (inferInstance : K.Normal).map π (QuotientGroup.mk'_surjective N)
  rcases hLnorm.eq_bot_or_eq_top with hbot | htop
  · have hKN : K ≤ N := by
      intro k hk
      have hmem : π k ∈ L := Subgroup.mem_map_of_mem π hk
      rw [hbot] at hmem
      have h1 : π k = 1 := by simpa using hmem
      simpa [π, QuotientGroup.ker_mk'] using h1
    exact le_antisymm hKN hNK
  · exfalso
    have hKtop : K = ⊤ := by
      rw [eq_top_iff]
      intro h hh
      have hmem : π h ∈ L := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨k, hkK, hkh⟩ := Subgroup.mem_map.mp hmem
      have hprod : h * k⁻¹ ∈ N := by
        have h1 : QuotientGroup.mk' N (h * k⁻¹) = 1 := by
          calc QuotientGroup.mk' N (h * k⁻¹)
              = QuotientGroup.mk' N h * (QuotientGroup.mk' N k)⁻¹ := by
                rw [map_mul, map_inv]
            _ = QuotientGroup.mk' N k * (QuotientGroup.mk' N k)⁻¹ := by rw [hkh.symm]
            _ = 1 := by group
        exact (QuotientGroup.eq_one_iff (h * k⁻¹)).mp h1
      have heq : h = (h * k⁻¹) * k := by group
      rw [heq]
      exact K.mul_mem (hNK hprod) hkK
    exact hKne hKtop

private lemma final_contradiction {Y : Subgroup (Equiv.Perm (Fin 10))}
    {N : Subgroup ↥Y} [N.Normal] {Ω : Set (Fin 10)}
    (φ : ↥Y →* Equiv.Perm ↥Ω) (hL34 : IsL3 (↥Y ⧸ N) 2)
    (hNK : N ≤ φ.ker) (hKeqN : φ.ker = N) (hΩlt : Nat.card ↥Ω < 16) : False := by
  have hinj : Function.Injective (QuotientGroup.lift N φ hNK) :=
    (QuotientGroup.injective_lift_iff (N := N) φ hNK).mpr hKeqN.symm
  exact not_injective_of_isL3_two hL34 hΩlt (QuotientGroup.lift N φ hNK) hinj

theorem not_hasL34Section_perm_fin_ten :
    ¬ HasL34Section (⊤ : Subgroup (Equiv.Perm (Fin 10))) := by
  rintro ⟨Y, -, N, hN, hL34⟩
  have hNnormal : N.Normal := hN
  obtain ⟨x, hxord, hN7, hcent, hxcycle, hxsupp⟩ :=
    exists_centralizing_cycle_of_section N hL34
  have hxGord : orderOf ((x : ↥Y) : Equiv.Perm (Fin 10)) = 7 := by
    rw [Subgroup.orderOf_coe, hxord]
  have hsupp : ∀ a : Fin 10, a ∈ ((x : ↥Y) : Equiv.Perm (Fin 10)).support →
      a ∈ MulAction.fixedPoints N (Fin 10) :=
    support_subset_fixedPoints N hN7 hcent hxGord hxcycle
  obtain ⟨hSigmacard, hΩlt⟩ := fixedPoints_compl_card N hxsupp hsupp
  let Ω : Set (Fin 10) := MulAction.fixedPoints N (Fin 10)
  have hΩ : Ω = MulAction.fixedPoints N (Fin 10) := rfl
  let φ : ↥Y →* Equiv.Perm ↥Ω := fixedPointsAction N Ω hΩ
  have hNK : N ≤ φ.ker := normal_le_kernel N Ω hΩ
  have hKcard : Nat.card ↥(φ.ker) ≤ 6 := kernel_card_le_six N Ω hΩ hSigmacard
  have hTsimple : IsSimpleGroup (↥Y ⧸ N) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL34
  have hYlarge : 20160 ≤ Nat.card ↥Y := by
    have hTcard : Nat.card (↥Y ⧸ N) = 20160 :=
      CFSG.Blueprint.LieModel.card_psl_three_four hL34
    have hHcard : Nat.card ↥Y = 20160 * Nat.card N := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hTcard]
    rw [hHcard]
    exact Nat.le_mul_of_pos_right 20160 Nat.card_pos
  have : (φ.ker).Normal := MonoidHom.normal_ker φ
  have hKne : φ.ker ≠ ⊤ := kernel_ne_top N Ω hΩ hYlarge hKcard
  have hKeqN : φ.ker = N := kernel_eq_normal (N := N) φ.ker hTsimple hNK hKne
  exact final_contradiction φ hL34 hNK hKeqN hΩlt

theorem not_hasL34Section_mulAut_of_isAlt_ten {X : Type} [Group X] (h : IsAlt X 10) :
    ¬ HasL34Section (⊤ : Subgroup (MulAut X)) := by
  rintro hsec
  obtain ⟨e⟩ := h
  let Φ : MulAut X ≃* Equiv.Perm (Fin 10) :=
    CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv (by norm_num : 7 ≤ 10) e
  have htop : (⊤ : Subgroup (MulAut X)).map Φ.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective Φ.toMonoidHom Φ.surjective
  exact not_hasL34Section_perm_fin_ten (htop ▸ hsec.map Φ.injective)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
