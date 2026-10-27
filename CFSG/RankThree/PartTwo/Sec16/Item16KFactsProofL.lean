module

public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.RankThree.PartTwo.Sec16.KS165LProof

open CFSG CFSG.RankThree CFSG.RankThree.PerfectCover
open scoped MatrixGroups

theorem two_pow_natCast_zmod_three_eq_one {n : ℕ} (h : 2 ^ n % 3 = 1) :
    ((2 ^ n : ℕ) : ZMod 3) = 1 := by
  have h' : ((2 ^ n : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simpa using h
  simpa using h'

theorem even_of_two_pow_mod_three_eq_one {n : ℕ} (h : 2 ^ n % 3 = 1) : Even n := by
  have hZ : (2 : ZMod 3) ^ n = 1 := by
    simpa [Nat.cast_pow] using two_pow_natCast_zmod_three_eq_one h
  rw [show (2 : ZMod 3) = -1 by decide] at hZ
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hZ

theorem not_three_dvd_of_even_of_two_pow_mod_nine_ne_one {n : ℕ} (he : Even n)
    (h9 : 2 ^ n % 9 ≠ 1) : ¬ 3 ∣ n := by
  intro h3
  have h6 : 6 ∣ n := by
    have hc : Nat.Coprime 2 3 := by norm_num
    have h := hc.mul_dvd_of_dvd_of_dvd he.two_dvd h3
    simpa using h
  obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k := h6
  have hmod : 2 ^ (6 * k) % 9 = 1 := by
    clear he h3 h9
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [Nat.mul_succ, pow_add, Nat.mul_mod, ih]
        norm_num
  exact h9 hmod

theorem not_three_dvd_of_mod_three_and_mod_nine {n : ℕ} (hq : 2 ^ n % 3 = 1)
    (h9 : 2 ^ n % 9 ≠ 1) : ¬ 3 ∣ n :=
  not_three_dvd_of_even_of_two_pow_mod_nine_ne_one
    (even_of_two_pow_mod_three_eq_one hq) h9

theorem four_le_of_mod_three_mod_nine_and_ne_two {n : ℕ} (hq : 2 ^ n % 3 = 1)
    (h9 : 2 ^ n % 9 ≠ 1) (h2 : n ≠ 2) : 4 ≤ n := by
  have he := even_of_two_pow_mod_three_eq_one hq
  have hn0 : n ≠ 0 := by
    intro h0
    exact h9 (by rw [h0]; norm_num)
  obtain ⟨k, rfl⟩ := he
  omega

theorem ne_six_of_mod_three_and_mod_nine {n : ℕ} (hq : 2 ^ n % 3 = 1)
    (h9 : 2 ^ n % 9 ≠ 1) : n ≠ 6 := by
  intro h6
  exact not_three_dvd_of_mod_three_and_mod_nine hq h9 (by rw [h6]; norm_num)

theorem arithmetic {n : ℕ} (hq : 2 ^ n % 3 = 1) (h9 : 2 ^ n % 9 ≠ 1) (h2 : n ≠ 2) :
    Even n ∧ ¬ 3 ∣ n ∧ 4 ≤ n ∧ n ≠ 6 := by
  refine ⟨even_of_two_pow_mod_three_eq_one hq,
    not_three_dvd_of_mod_three_and_mod_nine hq h9,
    four_le_of_mod_three_mod_nine_and_ne_two hq h9 h2,
    ne_six_of_mod_three_and_mod_nine hq h9⟩

theorem exists_omega {n : ℕ} (hn : 0 < n) (hq : 2 ^ n % 3 = 1) :
    ∃ ω : GaloisField 2 n, ω ^ 2 + ω + 1 = 0 := by
  classical
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn.ne'
  have h3dvd : 3 ∣ 2 ^ n - 1 := by
    have hZ : ((2 ^ n : ℕ) : ZMod 3) = 1 := two_pow_natCast_zmod_three_eq_one hq
    have h0 : ((2 ^ n - 1 : ℕ) : ZMod 3) = 0 := by
      rw [Nat.cast_sub (show 1 ≤ 2 ^ n from Nat.one_le_two_pow), hZ, Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff (2 ^ n - 1) 3).mp h0
  have hdvd : 3 ∣ Nat.card (GaloisField 2 n)ˣ := by
    rw [Nat.card_units, hcard]
    exact h3dvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  set ω : GaloisField 2 n := (u : GaloisField 2 n) with hω
  have hω3 : ω ^ 3 = 1 := by
    have h : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    rw [hω, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have hu1 : u = 1 := Units.ext (by rwa [hω] at h1)
    rw [hu1] at hu
    simp at hu
  have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    have h : ω ^ 3 - 1 = 0 := by rw [hω3]; ring
    calc (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      _ = 0 := h
  exact ⟨ω, (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hω1)⟩

theorem center_eq_bot {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : 4 ≤ n)
    (hQ : CFSG.IsQuasisimple Q) (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center Q))
    (φ : Q ⧸ Subgroup.center Q ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) :
    Subgroup.center Q = ⊥ := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hcard' : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, hcard]
  have hk3 : 3 ≤ Fintype.card (GaloisField 2 n) := by
    rw [hcard']
    calc 3 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h34 : ¬(3 = 3 ∧ Fintype.card (GaloisField 2 n) = 4) := by
    rintro ⟨-, h4⟩
    rw [hcard'] at h4
    have h2 : 2 ^ n = 2 ^ 2 := by norm_num [h4]
    have hn2 : n = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    omega
  let ePSL : CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n) ≃*
      PSL(3, GaloisField 2 n) :=
    (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 n)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 (GaloisField 2 n)).symm
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hQ (φ.trans ePSL)
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
      (k := GaloisField 2 n) (n := 3) le_rfl hk3 h34
  have hcardHopf : Nat.card (hopfMultiplier (PSL(3, GaloisField 2 n))) =
      Nat.gcd 3 (2 ^ n - 1) := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess (PSL(3, GaloisField 2 n))).toEquiv,
      Nat.card_congr eM.toEquiv,
      Nat.card_congr (Multiplicative.toAdd :
        Multiplicative (ZMod (Nat.gcd 3 (Fintype.card (GaloisField 2 n) - 1))) ≃
          ZMod (Nat.gcd 3 (Fintype.card (GaloisField 2 n) - 1))),
      Nat.card_zmod, hcard']
  rw [hcardHopf] at hdvd
  have hdvd3 : Nat.card (Subgroup.center Q) ∣ 3 :=
    hdvd.trans (Nat.gcd_dvd_left 3 (2 ^ n - 1))
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (by simpa [h3]) hZ3

noncomputable def mulEquivProjectiveSL {Q : Type} [Group Q] {n : ℕ}
    (φ : Q ⧸ Subgroup.center Q ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))
    (hZ : Subgroup.center Q = ⊥) :
    Q ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField 2 n) :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (φ.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 n)))

@[expose] def Concl (X : Type) [Group X] (T : Subgroup (MulAut X)) : Prop :=
  ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ E : Subgroup X, IsPGroup p E ∧ E ≠ ⊥ ∧
    (∀ t ∈ T, ∀ e ∈ E, t e ∈ E) ∧
    ∀ e ∈ E, e ≠ 1 → Subgroup.closure ({x : X | ∀ t ∈ T, t x = x} ∪ {e}) = ⊤

theorem concl_of_mulEquiv {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y)
    {T : Subgroup (MulAut X)}
    (h : Concl Y (T.map (MulAut.congr Φ).toMonoidHom)) : Concl X T := by
  obtain ⟨p, hp, hp3, E, hE, hne, hinv, hgen⟩ := h
  refine ⟨p, hp, hp3, E.comap (Φ : X →* Y), hE.comap_of_injective (Φ : X →* Y) Φ.injective,
    ?_, ?_, ?_⟩
  ·
    intro hbot
    apply hne
    rw [eq_bot_iff]
    rintro y hy
    obtain ⟨x, rfl⟩ := Φ.surjective y
    have hx : x ∈ E.comap (Φ : X →* Y) := hy
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, map_one]
    exact Subgroup.mem_bot.mpr rfl
  ·
    intro t ht e he
    show Φ (t e) ∈ E
    have hmem : (MulAut.congr Φ) t ∈ T.map (MulAut.congr Φ).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.congr Φ).toMonoidHom ht
    have h1 : (MulAut.congr Φ).toMonoidHom t (Φ e) = Φ (t e) := by
      change (MulAut.congr Φ) t (Φ e) = Φ (t e)
      rw [MulAut.congr_apply]
      simp
    rw [← h1]
    exact hinv _ hmem _ he
  ·
    intro e he he1
    have hΦe : Φ e ∈ E := he
    have hΦe1 : Φ e ≠ 1 := by
      intro h1
      exact he1 (Φ.injective (by simpa using h1))
    have htop : Subgroup.map (Φ : X →* Y) (Subgroup.closure
        ({x : X | ∀ t ∈ T, t x = x} ∪ {e})) = ⊤ := by
      rw [MonoidHom.map_closure]
      have himg : (Φ : X →* Y) '' ({x : X | ∀ t ∈ T, t x = x} ∪ {e}) =
          {y : Y | ∀ s ∈ T.map (MulAut.congr Φ).toMonoidHom, s y = y} ∪ {Φ e} := by
        rw [Set.image_union, Set.image_singleton]
        congr 1
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          intro s hs
          obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hs
          rw [← hts]
          have h1 : (MulAut.congr Φ).toMonoidHom t (Φ x) = Φ (t x) := by
            change (MulAut.congr Φ) t (Φ x) = Φ (t x)
            rw [MulAut.congr_apply]
            simp
          exact h1.trans (congrArg Φ (hx t ht))
        · intro hy
          refine ⟨Φ.symm y, ?_, by simp⟩
          intro t ht
          have hmem : (MulAut.congr Φ) t ∈ T.map (MulAut.congr Φ).toMonoidHom :=
            Subgroup.mem_map_of_mem (MulAut.congr Φ).toMonoidHom ht
          have h2 : (MulAut.congr Φ) t y = y := hy _ hmem
          have h3 : Φ (t (Φ.symm y)) = Φ (Φ.symm y) := by
            calc Φ (t (Φ.symm y)) = (MulAut.congr Φ) t (Φ (Φ.symm y)) := by
                  rw [MulAut.congr_apply]
                  simp
              _ = (MulAut.congr Φ) t y := by simp
              _ = y := h2
              _ = Φ (Φ.symm y) := by simp
          exact Φ.injective h3
      rw [himg, hgen (Φ e) hΦe hΦe1]
    rw [eq_top_iff]
    intro x _
    have hx : Φ x ∈ Subgroup.map (Φ : X →* Y) (Subgroup.closure
        ({x : X | ∀ t ∈ T, t x = x} ∪ {e})) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← Φ.injective hyx]
    exact hy

theorem concl_of_conj {X : Type} [Group X] (α : MulAut X) {T : Subgroup (MulAut X)}
    (h : Concl X (T.map (MulAut.conj α).toMonoidHom)) : Concl X T := by
  have hconj : (MulAut.congr (α : X ≃* X)).toMonoidHom = (MulAut.conj α).toMonoidHom := by
    ext t x
    simp [MulAut.congr, MulAut.conj_apply]
  refine concl_of_mulEquiv (Φ := (α : X ≃* X)) ?_
  rwa [hconj]

theorem concl_of_le_zpowers {X : Type} [Group X] {T : Subgroup (MulAut X)} {g : MulAut X}
    (hT : T ≤ Subgroup.zpowers g) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {E : Subgroup X} (hE : IsPGroup p E) (hne : E ≠ ⊥)
    (hEinv : ∀ e : X, e ∈ E ↔ g e ∈ E)
    (hgen : ∀ e ∈ E, e ≠ 1 → Subgroup.closure ({x : X | g x = x} ∪ {e}) = ⊤) :
    Concl X T := by
  refine ⟨p, hp, hp3, E, hE, hne, ?_, ?_⟩
  ·
    let K : Subgroup (MulAut X) :=
      { carrier := {u : MulAut X | ∀ e : X, e ∈ E ↔ u e ∈ E}
        mul_mem' := by
          intro a b ha hb e
          rw [MulAut.mul_apply]
          exact (hb e).trans (ha (b e))
        one_mem' := by
          intro e
          simp
        inv_mem' := by
          intro a ha e
          rw [ha (a⁻¹ e), MulAut.apply_inv_self] }
    have hTK : T ≤ K := hT.trans (Subgroup.zpowers_le.mpr hEinv)
    exact fun t ht e he => ((hTK ht) e).mp he
  ·
    intro e he he1
    have hsubset : {x : X | g x = x} ⊆ {x : X | ∀ t ∈ T, t x = x} := by
      intro x hx t ht
      have hs : g • x = x := by simpa [MulAut.smul_def] using hx
      have h := smul_eq_self_of_mem_zpowers (hT ht) hs
      simpa [MulAut.smul_def] using h
    have hle : (⊤ : Subgroup X) ≤
        Subgroup.closure ({x : X | ∀ t ∈ T, t x = x} ∪ {e}) := by
      rw [← hgen e he he1]
      exact Subgroup.closure_mono (Set.union_subset_union_left _ hsubset)
    exact eq_top_iff.mpr hle

end CFSG.RankThree.PartTwo.Sec16.KS165LProof
