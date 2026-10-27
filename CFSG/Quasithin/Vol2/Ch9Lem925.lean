module

public import CFSG.Quasithin.Vol2.Ch9Sec2Faith
public import CFSG.Quasithin.Vol2.Ch9Lem924
public import CFSG.Quasithin.Vol2.Ch10SecB3CartanC
public import CFSG.Quasithin.Vol2.Ch10SecKHBC
public import CFSG.Quasithin.Vol2.Ch11SecBHBMainC
public import CFSG.Quasithin.Vol2.Ch11SecKGBorelComm

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem add_two_lt_two_pow {m : ℕ} (hm : 3 ≤ m) : m + 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem eq_or_of_dvd {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : n ≤ m + 1)
    (h : 2 ^ m - 1 ∣ n * (2 ^ n - 1)) : m = n ∨ (m = 2 ∧ n = 3) := by
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rcases lt_trichotomy m n with hlt | heq | hgt
  · right
    have hn' : n = m + 1 := by omega
    subst hn'
    have h2 : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by rw [pow_succ]; omega
    rw [h2, mul_add, mul_one] at h
    have h3 : 2 ^ m - 1 ∣ m + 1 :=
      (Nat.dvd_add_right (Dvd.dvd.mul_left (Dvd.intro_left 2 rfl) _)).mp h
    have h4 := Nat.le_of_dvd (by omega) h3
    by_contra h5
    have h6 := add_two_lt_two_pow (m := m) (by omega)
    omega
  · exact Or.inl heq
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, m = n + (k + 1) := ⟨m - n - 1, by omega⟩
    have hA : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have hB : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set A := 2 ^ n with hAdef
    set B := 2 ^ (k + 1) with hBdef
    have hm' : 2 ^ (n + (k + 1)) = A * B := by rw [pow_add]
    rw [hm'] at h
    have hd : (A * B - 1 : ℕ) ∣ n * (B - 1) := by
      have h1 : ((A * B - 1 : ℕ) : ℤ) ∣ (n * (A - 1) * B : ℤ) := by
        have := Int.natCast_dvd_natCast.mpr h
        push_cast [Nat.cast_sub (show 1 ≤ A from by omega),
          Nat.cast_sub (show 1 ≤ A * B from by nlinarith)] at this ⊢
        exact Dvd.dvd.mul_right this _
      have h2 : ((A * B - 1 : ℕ) : ℤ) ∣ (n * (A * B - 1) : ℤ) := by
        push_cast [Nat.cast_sub (show 1 ≤ A * B from by nlinarith)]
        exact Dvd.intro_left _ rfl
      have h3 : ((A * B - 1 : ℕ) : ℤ) ∣ ((n * (B - 1) : ℕ) : ℤ) := by
        have h4 : ((n * (B - 1) : ℕ) : ℤ) = (n * (A * B - 1) : ℤ) - (n * (A - 1) * B : ℤ) := by
          push_cast [Nat.cast_sub (show 1 ≤ B from by omega)]
          ring
        rw [h4]
        exact dvd_sub h2 h1
      exact Int.natCast_dvd_natCast.mp h3
    have hpos : 0 < n * (B - 1) := Nat.mul_pos (by omega) (by omega)
    have hle := Nat.le_of_dvd hpos hd
    have hlt : n * (B - 1) < A * B - 1 := by
      have h5 : n * (B - 1) ≤ (A - 1) * (B - 1) := Nat.mul_le_mul_right _ (by omega)
      have h6 : (A - 1) * (B - 1) < A * B - 1 := by
        zify [show 1 ≤ A from by omega, show 1 ≤ B from by omega,
          show 1 ≤ A * B from by nlinarith]
        nlinarith
      omega
    omega

namespace Setup

variable (S : Setup T L I n)
include S

theorem le_centralizer_of_hall (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h1 : zQ T I = fsuV T I) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) :
    B ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro b hb
  have hZH := S.le_centerOf h37c h38c hC58 h317 h1 hH
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hZH hz).2 b (hB.1 hb).1).symm

theorem eq_one_of_hall (h4414 : Stmt4_4_14)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1 : zQ T I = fsuV T I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {x : G} (hx : x ∈ B)
    (hxV : x ∈ Subgroup.centralizer (fsuV T I : Set G)) : x = 1 :=
  (S.hall_faithful h4414 h37 h38 h39 h1 hH hn1).2 B hB.1 hB.2.1 hB.2.2 x hx
    (S.comm_mem_pCoreOf h37c h38c (hB.1 hx).2 hxV)

theorem exists_orderOf_eq
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h331 : Stmt3_3_1) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight)
    (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3) (hH11 : Ch9InH11Plus)
    (h1 : zQ T I = fsuV T I) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hn1 : 1 < E1.nParam H) :
    E1.nParam H ≤ n ∧ ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      ∃ b ∈ B, orderOf b = 2 ^ n - 1 := by
  obtain ⟨K, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
  have hInM : InM T (fsuM T L) := ⟨S.uniq.1.1, le_sup_right.trans S.uniq.1.2⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ fsuM T L :=
    ((h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow).2 L
      S.hyp.fsu.maximal S.hyp.fsu.quasisimple).2.2.2.1
  have hDHB := Vol2.Ch11.SecB.derivedHallBorel_ofC hE22 Vol2.Ch11.SecB.factBorelComm_holds
  obtain ⟨m, hmH, hcart⟩ := Vol2.Ch10.SecB.fact10_2_3CartanLe_of hE22 hDHB
    Vol2.Ch10.SecB.factBorelCartan G T (fsuM T L) H S.hyp.fsu.simple S.hyp.fsu.nonabelian
    S.hyp.fsu.qtke S.hyp.fsu.sylow hInM hNT hH hn1
  obtain ⟨B₀, hB₀, -, -⟩ := hDHB G T (fsuM T L) H S.hyp.fsu.simple S.hyp.fsu.nonabelian
    S.hyp.fsu.qtke S.hyp.fsu.sylow hInM hNT hH hn1
  have hBZ : ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      ∀ b ∈ B, b ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun B hB b hb =>
    S.le_centralizer_of_hall h37c h38c hC58 h317 h1 hH hB hb
  have hBodd : ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      ∀ b ∈ B, Odd (orderOf b) := fun B hB b hb =>
    hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard hb)
  have hkill : ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      ∀ b ∈ B, ∀ k : ℕ, b ^ k ∈ Subgroup.centralizer (fsuV T I : Set G) → b ^ k = 1 := by
    intro B hB b hb k hk
    exact S.eq_one_of_hall h4414 h37c h38c h37 h38 h39 h1 hH hn1 hB (B.pow_mem hb k) hk
  have hpow : ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      ∀ b ∈ B, b ^ (n * (2 ^ n - 1)) = 1 := fun B hB b hb =>
    hkill B hB b hb _ (hc.pow_mem_centralizer h1 (hB.1 hb).2 (hBodd B hB b hb) (hBZ B hB b hb))
  have hm2 : 2 ≤ m := E2.E22A.two_le_of_one_lt_of_le hn1 hmH
  have hnm : n ≤ m + 1 := by
    have h2 := S.le_nParam_add_one h37 h38 h39 h3228 hE610 h63 hH11 h1 hH
    have h3 : (n : ℕ∞) ≤ (m + 1 : ℕ) := by
      push_cast
      exact h2.trans (add_le_add hmH le_rfl)
    exact_mod_cast h3
  obtain ⟨b₀, hb₀, hb₀o⟩ := hcart B₀ hB₀
  have hdvd : 2 ^ m - 1 ∣ n * (2 ^ n - 1) := by
    rw [← hb₀o]
    exact orderOf_dvd_of_pow_eq_one (hpow B₀ hB₀ b₀ hb₀)
  have hmn : m = n := by
    rcases eq_or_of_dvd hm2 S.two_le hnm hdvd with h | ⟨rfl, rfl⟩
    · exact h
    exfalso
    have hb₀M := (hB₀.1 hb₀).2
    obtain ⟨A, B, τ, hA, hB, hform⟩ :=
      hc.isUT_of_mem_centralizer h1 hb₀M (hBodd B₀ hB₀ b₀ hb₀) (hBZ B₀ hB₀ b₀ hb₀)
    set y : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨b₀, S.hMN hb₀M⟩ with hy
    have hτ : τ ≠ 1 := by
      rintro rfl
      have h7 := Om4.pow_eq_one_of_isUT hA hB (k := 1) (pow_one _)
      rw [← hform, hc.card] at h7
      have h8 : orderOf (bar e y) ∣ Nat.gcd (1 * (2 ^ 3 - 1) * 2) 3 := by
        refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h7) ?_
        have := orderOf_map_dvd (bar e) y
        rwa [hy, Subgroup.orderOf_mk, hb₀o] at this
      norm_num at h8
      have h9 : bar e (y ^ 1) = 1 := by rw [pow_one]; exact h8
      have h10 := hkill B₀ hB₀ b₀ hb₀ 1 (by
        have := mem_centralizer_of_bar e _ h9
        simpa [hy] using this)
      rw [pow_one] at h10
      rw [h10, orderOf_one] at hb₀o
      norm_num at hb₀o
    have hV1Z : fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤
        quasithinOmegaOneCenter T := by
      rw [S.omegaOneCenter_T_eq h1]
      exact le_inf inf_le_left (hc.le_centralizer_T (by decide))
    have hfix : ∀ c : K, (Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd
        (c • !![(1 : K), 0; 0, 0])) = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
      intro c
      have hw := hV1Z (hc.symm_mem (e := e) c)
      set w := e.symm (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) with hwdef
      have h2 : e w = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
        rw [hwdef, MulEquiv.apply_symm_apply]
      rw [← hform, ← h2, bar_apply]
      congr 1
      refine Subtype.ext ?_
      show b₀ * w * b₀⁻¹ = w
      rw [← Subgroup.mem_centralizer_iff.mp (hBZ B₀ hB₀ b₀ hb₀) _ hw, mul_inv_cancel_right]
    have hfix' : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 *
        τ c = c := by
      intro c
      have h3 := hfix c
      rw [Om4.apply_smul_e11 hA hB] at h3
      have h2 := congrArg (fun X : Om4.VM K =>
        (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) 0 0) h3
      simpa using h2
    have h11 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      simpa using hfix' 1
    exact hτ (RingEquiv.ext fun c => by simpa [h11] using hfix' c)
  subst hmn
  exact ⟨hmH, hcart⟩

end Setup

end CFSG.Quasithin.H13.Ch9
