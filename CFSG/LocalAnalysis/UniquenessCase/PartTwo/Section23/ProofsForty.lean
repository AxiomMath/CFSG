module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ContextFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SigmaCentZ
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.GroupTheory.CoprimeHyperplaneCentralizer
public import CFSG.GroupTheory.CoprimeCommutatorCard
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.SubgroupCardMul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem two_pow_add_two_le_card_V
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (n : ℕ) (hn : 2 ≤ n)
    (hZcard : Nat.card D.Z = 2 ^ n) :
    2 ^ (n + 2) ≤ Nat.card c.V := by
  classical
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← (h4 h1930 c).1]
    exact D.normalizer_U_eq
  have hVlarge : 2 ^ (n + 1) < Nat.card c.V := by
    by_contra hle
    push Not at hle
    have hNM : c.N ≤ D.M := by
      intro x hxN
      have hZxV : conjSubgroup D.Z x ≤ c.V := by
        have hVeq : c.V = ⨆ n : ↥c.N,
            D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
          rw [Ctx23L.V]
          exact uc22br4_conjClosure_eq c.N D.Z
        rw [hVeq]
        exact le_iSup (fun n : ↥c.N =>
          D.Z.map (MulAut.conj (n : G)).toMonoidHom) ⟨x⁻¹, c.N.inv_mem hxN⟩
      have hZxcard : Nat.card (conjSubgroup D.Z x) = 2 ^ n := by
        rw [CFSG.Quasithin.E3.card_conjSubgroup, hZcard]
      have hmeet : D.Z ⊓ conjSubgroup D.Z x ≠ ⊥ := by
        intro hbot
        have hcard := CFSG.card_mul_card_le_of_inf_eq_bot
          (A := c.V) hZleV hZxV hbot
        rw [hZcard, hZxcard] at hcard
        have h2 : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
          rw [← pow_add]
          congr 1
          omega
        have hle' : 2 ^ (2 * n) ≤ 2 ^ (n + 1) := by
          rw [h2]
          exact hcard.trans hle
        have : 2 * n ≤ n + 1 :=
          (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle'
        omega
      have hZxeq : conjSubgroup D.Z x = D.Z := by
        rcases c.Z_right_TI h4 h1930 x with h | h
        · exact absurd h hmeet
        · exact h
      have hxNZ : x ∈ Subgroup.normalizer (D.Z : Set G) :=
        (conjSubgroup_eq_iff_mem_normalizer).mp hZxeq
      rwa [hNZ] at hxNZ
    have hNM' : D.M = c.N := (c.N_mem_calMOf_T).1.2 D.M D.maxLocal.1 hNM
    exact c.N_ne_M hNM'.symm
  obtain ⟨kV, hkV⟩ := (IsElemAbelian.isPGroup (c.isElemAbelian_V h4 h1930)).exists_card_eq
  have hkVgt : n + 1 < kV := by
    apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp
    rwa [hkV] at hVlarge
  rw [hkV]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem exists_sigma_hyperplane_large_centralizer
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h61 : UC6.R6_1 D)
    (hZc : SigmaCentZ D Ch) (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hsig : D.sig.Nonempty) (h1930 : H1930 D) (n : ℕ) (hn : 2 ≤ n)
    (hZcard : Nat.card D.Z = 2 ^ n) :
    ∃ (p : ℕ) (Y : Subgroup G), p ∈ D.sig ∧ Y ≤ D.M ∧ IsPGroup p Y ∧ ¬ IsCyclic Y ∧
      2 ^ (n + 2) ≤ Nat.card ↥(c.E ⊓ Subgroup.centralizer (Y : Set G)) := by
  classical
  obtain ⟨p, hpσ⟩ := hsig
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  have hprank3 : 3 ≤ CFSG.Open.pRank p D.M := hrk p hpσ
  have hEel : IsElemAbelian 2 c.E := c.isElemAbelian_E h4 h39 h1930
  have hEisp : IsPGroup 2 c.E := hEel.isPGroup
  have hVleE : c.V ≤ c.E := uc22p22v_le_conjClosure D.M c.V
  obtain ⟨E0, hE0M, hE0el, hE0card⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained p D.M (by omega)
  have hp3dvd : p ^ 3 ∣ Nat.card E0 := by
    rw [hE0card]
    exact pow_dvd_pow p hprank3
  obtain ⟨X, hXcard, -, hXE0⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 3) (H := ⊥) (L := E0)
      (by simp) hp3dvd bot_le
  have hXM : X ≤ D.M := hXE0.trans hE0M
  have hXel : IsElemAbelian p X := IsElemAbelian.mono hE0el hXE0
  have hXp : IsPGroup p X := hXel.isPGroup
  have hXcentZ : X ≤ Subgroup.centralizer (D.Z : Set G) := by
    intro x hx
    have hxOpp : x ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.Opp p D.M := by
      unfold CFSG.LocalAnalysis.UniquenessCase.UC22.Opp
      refine Subgroup.subset_closure ⟨hXM hx, ?_⟩
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hXel.2 x hx)) with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    exact hZc h1930 c p hpσ hxOpp
  have hXE_norm : X ≤ Subgroup.normalizer (c.E : Set G) := by
    rw [c.normalizer_E_eq h4 h39 h1930]
    exact hXM
  have hXcard' : Nat.card X = p ^ 3 := hXcard
  have hp2dvd : p ^ 2 ∣ Nat.card X := by
    rw [hXcard']
    exact pow_dvd_pow p (by norm_num : 2 ≤ 3)
  obtain ⟨Y0, hY0card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X) p (n := 2) hp2dvd
  let Y : Subgroup G := Y0.map X.subtype
  have hYX : Y ≤ X := Subgroup.map_subtype_le Y0
  have hYM : Y ≤ D.M := hYX.trans hXM
  have hYcard : Nat.card Y = p ^ 2 := by
    rw [show Y = Y0.map X.subtype from rfl,
      Subgroup.card_map_of_injective X.subtype_injective, hY0card]
  have hYcardX : Nat.card Y * p = Nat.card X := by
    rw [hYcard, hXcard']
    ring
  have hYel : IsElemAbelian p Y := IsElemAbelian.mono hXel hYX
  have hYp : IsPGroup p Y := hYel.isPGroup
  have hYnc : ¬ IsCyclic Y := by
    have hYea : CFSG.IsElementaryAbelian p ↥Y :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Y).2 hYel
    exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (A := ↥Y) (p := p)
      hYcard
  have hYcardX' : Nat.card Y * p = Nat.card X := hYcardX
  by_cases hcent : X ≤ Subgroup.centralizer (c.E : Set G)
  · have hcardVE : Nat.card c.V ≤ Nat.card c.E := by
      rw [← CFSG.natCard_subgroupOf_eq c.V c.E hVleE]
      exact Subgroup.card_le_card_group (H := c.V.subgroupOf c.E)
    have hWbig : 2 ^ (n + 2) ≤
        Nat.card ↥(c.E ⊓ Subgroup.centralizer (Y : Set G)) := by
      have hW_eq : c.E ⊓ Subgroup.centralizer (Y : Set G) = c.E := by
        refine le_antisymm inf_le_left ?_
        refine le_inf le_rfl ?_
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp (hcent (hYX hy)) e he).symm
      rw [hW_eq]
      exact (two_pow_add_two_le_card_V D Ch c h4 h1930 n hn hZcard).trans hcardVE
    exact ⟨p, Y, hpσ, hYM, hYp, hYnc, hWbig⟩
  · obtain ⟨Y', hY'X, hY'cardX, hWnotcent⟩ :=
      CFSG.GroupTheory.exists_hyperplane_not_le_centralizer_inf_centralizer
        (r := p) (E := X) (Q := c.E) hXel
        (by rw [hXcard']; exact Nat.pow_le_pow_right hp.pos (by norm_num : 2 ≤ 3))
        hXE_norm (CFSG.GroupTheory.not_dvd_card_of_isPGroup hEisp hp hp2)
        hcent
    let W : Subgroup G := c.E ⊓ Subgroup.centralizer (Y' : Set G)
    let J : Subgroup G := ⁅W, X⁆
    have hY'M : Y' ≤ D.M := hY'X.trans hXM
    have hY'p : IsPGroup p Y' := hXp.to_le hY'X
    have hY'el : IsElemAbelian p Y' := IsElemAbelian.mono hXel hY'X
    have hY'card : Nat.card Y' = p ^ 2 := by
      have h : Nat.card Y' * p = p ^ 2 * p := by
        rw [hY'cardX, hXcard']
        ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos h
    have hY'nc : ¬ IsCyclic Y' := by
      have hY'ea : CFSG.IsElementaryAbelian p ↥Y' :=
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Y').2 hY'el
      exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (A := ↥Y') (p := p)
        hY'card
    have hWM : W ≤ c.E := inf_le_left
    have hYX_comm : ∀ x ∈ X, ∀ y ∈ Y', x * y = y * x := by
      intro x hx y hy
      exact congrArg Subtype.val ((hXel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hY'X hy⟩))
    have hX_le_CY : X ≤ Subgroup.centralizer (Y' : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hYX_comm x hx y hy).symm
    have hWin : X ≤ Subgroup.normalizer (W : Set G) := by
      refine (le_inf hXE_norm (hX_le_CY.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hW2 : IsPGroup 2 W := hEisp.to_le hWM
    have hWel : IsElemAbelian 2 W := hEel.mono hWM
    have hWab : IsMulCommutative ↥W := hWel.1
    have hWexp : ∀ w ∈ W, w ^ 2 = 1 := hWel.2
    have hJleW : J ≤ W := by
      simpa [J] using Subgroup.le_normalizer_iff_commutator_le_left.mp hWin
    have hJdecomp := CFSG.GroupTheory.card_centralizer_mul_card_commutator_of_coprime
      (W := W) (X := X) (p := p) hWab hWexp hXp hp2 hWin
    have hcardW : Nat.card ↥W =
        Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set G)) * Nat.card ↥J := by
      simpa [J] using hJdecomp.1
    have hdisj : (W ⊓ Subgroup.centralizer (X : Set G)) ⊓ J = ⊥ := by
      simpa [J] using hJdecomp.2
    have hJne : J ≠ ⊥ := by
      intro hJbot
      apply hWnotcent
      have hJbot' : ⁅W, X⁆ = ⊥ := by simpa [J] using hJbot
      rw [Subgroup.le_centralizer_iff]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hJbot'
    have hJfix : J ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
      rw [← hdisj]
      ext z
      constructor
      · rintro ⟨hzJ, hzC⟩
        exact ⟨⟨hJleW hzJ, hzC⟩, hzJ⟩
      · rintro ⟨⟨-, hzC⟩, hzJ⟩
        exact ⟨hzJ, hzC⟩
    have hJge4 : 4 ≤ Nat.card ↥J := by
      have h4 := CFSG.GroupTheory.four_le_card_commutator_of_fixedPoints_eq_bot
        (W := W) (X := X) hW2 hWin (by simpa [J] using hJne)
        (by simpa [J] using hJfix)
      simpa [J] using h4
    have hZleW : D.Z ≤ W := by
      refine le_inf ((uc22p22v_le_conjClosure c.N D.Z).trans hVleE) ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hXcentZ (hY'X hy)) z hz).symm
    have hZleCW : D.Z ≤ W ⊓ Subgroup.centralizer (X : Set G) :=
      le_inf hZleW (Subgroup.le_centralizer_iff.mp hXcentZ)
    have hCge : 2 ^ n ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set G)) := by
      calc 2 ^ n = Nat.card D.Z := hZcard.symm
        _ = Nat.card ↥(D.Z.subgroupOf (W ⊓ Subgroup.centralizer (X : Set G))) :=
            (CFSG.natCard_subgroupOf_eq D.Z (W ⊓ Subgroup.centralizer (X : Set G))
              hZleCW).symm
        _ ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set G)) :=
            Subgroup.card_le_card_group (H := D.Z.subgroupOf (W ⊓ Subgroup.centralizer (X : Set G)))
    have hWbig : 2 ^ (n + 2) ≤ Nat.card W := by
      calc 2 ^ (n + 2) = 2 ^ n * 4 := by ring
        _ ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set G)) * Nat.card ↥J :=
            Nat.mul_le_mul hCge hJge4
        _ = Nat.card W := hcardW.symm
    exact ⟨p, Y', hpσ, hY'M, hY'p, hY'nc, hWbig⟩

private theorem centralizer_singleton_le_M_of_mem_large
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h61 : UC6.R6_1 D) (h1930 : H1930 D)
    {p : ℕ} (hpσ : p ∈ D.sig) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hYp : IsPGroup p Y) (hYnc : ¬ IsCyclic Y)
    {u : G} (huE : u ∈ c.E) (huCY : u ∈ Subgroup.centralizer (Y : Set G)) (hu1 : u ≠ 1) :
    Subgroup.centralizer ({u} : Set G) ≤ D.M := by
  classical
  have hEel : IsElemAbelian 2 c.E := c.isElemAbelian_E h4 h39 h1930
  have hu2 : orderOf u = 2 := orderOf_eq_prime (hEel.2 u huE) hu1
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) := by
    refine ⟨Subgroup.zpowers u, Subgroup.zpowers_ne_bot.mpr hu1, ?_, rfl⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  obtain ⟨K, hKmax, hKle⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le hloc
  have hCzp : Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) =
      Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCu_le_N : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [← hCzp]
    exact Subgroup.centralizer_le_normalizer _
  have hY_le_Cu : Y ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp huCY y hy)
  have hYleK : Y ≤ K := (hY_le_Cu.trans hCu_le_N).trans hKle
  have huniq : UniqueMax D.M Y := h61 p hpσ Y hYM hYp hYnc
  have hKmem : K ∈ calMOf Y := ⟨hKmax, hYleK⟩
  rw [huniq] at hKmem
  have hKM : K = D.M := by simpa using hKmem
  exact hCu_le_N.trans (hKle.trans (le_of_eq hKM))

theorem s23_40_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h39 : S23_39 D Ch)
    (h61 : UC6.R6_1 D) (hZc : SigmaCentZ D Ch)
    (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M) (hsig : D.sig.Nonempty)
    (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) : S23_40 D Ch := by
  intro h1930 c
  classical
  set n : ℕ := CFSG.Open.pRank 2 D.Z with hn_def
  have hn' : 2 ≤ n := by simpa [hn_def] using hn
  have hZcard : Nat.card D.Z = 2 ^ n := by
    rw [hn_def]
    exact CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (c.isElemAbelian_Z h4 h1930)
  have hVbig : 2 ^ (n + 2) ≤ Nat.card c.V :=
    two_pow_add_two_le_card_V D Ch c h4 h1930 n hn' hZcard
  obtain ⟨p, Y, hpσ, hYM, hYp, hYnc, hWbig⟩ :=
    exists_sigma_hyperplane_large_centralizer D Ch c h4 h39 h61 hZc hrk hsig h1930 n hn' hZcard
  have hEel : IsElemAbelian 2 c.E := c.isElemAbelian_E h4 h39 h1930
  have hEisp : IsPGroup 2 c.E := hEel.isPGroup
  have hCent_le_M : ∀ u ∈ c.E ⊓ Subgroup.centralizer (Y : Set G), u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ D.M := by
    intro u hu hu1
    exact centralizer_singleton_le_M_of_mem_large D Ch c h4 h39 h61 h1930 hpσ hYM hYp hYnc
      hu.1 hu.2 hu1
  have hkey : ∀ U : Subgroup G, U ≤ c.E → ¬ Subgroup.centralizer (U : Set G) ≤ D.M →
      n + 2 ≤ CFSG.Quasithin.E3.mQuot c.E U := by
    intro U hUE hCnotM
    by_contra hlt
    push Not at hlt
    have hmU : CFSG.Quasithin.E3.mQuot c.E U ≤ n + 1 := by omega
    have hdisj : U ⊓ (c.E ⊓ Subgroup.centralizer (Y : Set G)) = ⊥ := by
      by_contra hne
      obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have huU : u ∈ U := hu.1
      have huW : u ∈ c.E ⊓ Subgroup.centralizer (Y : Set G) := hu.2
      have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
      have hCU_le_Cu : Subgroup.centralizer (U : Set G) ≤
          Subgroup.centralizer ({u} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU)
      exact hCnotM (hCU_le_Cu.trans (hCent_le_M u huW hu1'))
    have hcardUW : Nat.card U * Nat.card ↥(c.E ⊓ Subgroup.centralizer (Y : Set G)) ≤
        Nat.card c.E :=
      CFSG.card_mul_card_le_of_inf_eq_bot (A := c.E) hUE inf_le_left hdisj
    have hEcard : Nat.card c.E =
        2 ^ CFSG.Quasithin.E3.mQuot c.E U * Nat.card U :=
      CFSG.Quasithin.E3.card_eq_two_pow_mul hEisp hUE
    have hmul : Nat.card U * 2 ^ (n + 2) ≤ Nat.card U * 2 ^ CFSG.Quasithin.E3.mQuot c.E U := by
      calc Nat.card U * 2 ^ (n + 2)
          ≤ Nat.card U * Nat.card ↥(c.E ⊓ Subgroup.centralizer (Y : Set G)) :=
            Nat.mul_le_mul_left _ hWbig
        _ ≤ Nat.card c.E := hcardUW
        _ = 2 ^ CFSG.Quasithin.E3.mQuot c.E U * Nat.card U := hEcard
        _ = Nat.card U * 2 ^ CFSG.Quasithin.E3.mQuot c.E U := by ring
    have hpow : 2 ^ (n + 2) ≤ 2 ^ CFSG.Quasithin.E3.mQuot c.E U :=
      Nat.le_of_mul_le_mul_left hmul (Nat.card_pos (α := ↥U))
    have : n + 2 ≤ CFSG.Quasithin.E3.mQuot c.E U :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
    omega
  have hge : ((n + 2 : ℕ) : ℕ∞) ≤
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.rMV D.M c.E := by
    unfold CFSG.LocalAnalysis.UniquenessCase.PartTwo.rMV
    refine le_iInf₂ fun U hU => ?_
    exact_mod_cast hkey U hU.1 hU.2
  have hcast : (((n : ℕ) : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [hcast]
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self (n + 1)) hge
