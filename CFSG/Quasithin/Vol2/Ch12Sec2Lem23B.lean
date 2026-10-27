module

public import CFSG.Quasithin.Background.AutOnCard
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem23A
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22D
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22P

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem22

variable {G : Type} [Group G] [Finite G]

abbrev rR (V H P : Subgroup G) : Subgroup G :=
  conjClosure (V ⊓ pCoreOf 2 H) P ⊓ Subgroup.centralizer (V : Set G)

omit [Finite G] in
theorem card_autOn_mul {K V : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autOn K V) * Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) = Nat.card K :=
  CFSG.Quasithin.AutOn.card_autOn_mul hK

theorem comm_mem_of_fpf_four {R V₀ : Subgroup G} {z y : G} (hV₀R : V₀ ≤ R)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hcard : Nat.card R = 4 * Nat.card V₀)
    (hzR : ∀ a ∈ R, z * a * z⁻¹ ∈ R) (hzV : ∀ a ∈ V₀, z * a * z⁻¹ ∈ V₀) (hz3 : z ^ 3 = 1)
    (hzfix : ∀ a ∈ R, a⁻¹ * (z * a * z⁻¹) ∈ V₀ → a ∈ V₀)
    (hyR : ∀ a ∈ R, y * a * y⁻¹ ∈ R) (hyV : ∀ a ∈ V₀, y * a * y⁻¹ ∈ V₀) {k : ℕ}
    (hyk : y ^ 2 ^ k = 1)
    (hyz : ∀ a ∈ R, y * (z * a * z⁻¹) * y⁻¹ = z * (y * a * y⁻¹) * z⁻¹) :
    ∀ a ∈ R, a⁻¹ * (y * a * y⁻¹) ∈ V₀ := by
  set N := V₀.subgroupOf R with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e1 : ((g * n * g⁻¹ : ↥R) : G) = n := by
      have := hRc g g.2 n n.2
      show (g : G) * n * (g : G)⁻¹ = n
      rw [this]
      group
    rw [e1]
    exact hn⟩
  let cj : ∀ x : G, (∀ a ∈ R, x * a * x⁻¹ ∈ R) → ↥R →* ↥R := fun x hx =>
    { toFun := fun a => ⟨x * a * x⁻¹, hx a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show x * ((a : G) * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹)
        group) }
  have hcjN : ∀ x hx, (∀ a ∈ V₀, x * a * x⁻¹ ∈ V₀) → N ≤ N.comap (cj x hx) := by
    intro x hx hxV a ha
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hxV _ (Subgroup.mem_subgroupOf.mp ha)
  set Z := QuotientGroup.map N N (cj z hzR) (hcjN z hzR hzV) with hZ
  set Y := QuotientGroup.map N N (cj y hyR) (hcjN y hyR hyV) with hY
  have hZmk : ∀ a : ↥R, Z (a : ↥R ⧸ N) = ((cj z hzR a : ↥R) : ↥R ⧸ N) := fun a => rfl
  have hYmk : ∀ a : ↥R, Y (a : ↥R ⧸ N) = ((cj y hyR a : ↥R) : ↥R ⧸ N) := fun a => rfl
  have hpowR : ∀ n : ℕ, ∀ a ∈ R, y ^ n * a * (y ^ n)⁻¹ ∈ R := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      have := hyR _ (ih a ha)
      rwa [show y * (y ^ m * a * (y ^ m)⁻¹) * y⁻¹ = y ^ (m + 1) * a * (y ^ (m + 1))⁻¹ by
        rw [pow_succ']; group] at this
  have hYpow : ∀ n : ℕ, ∀ a : ↥R, Y^[n] (a : ↥R ⧸ N) =
      ((⟨y ^ n * a * (y ^ n)⁻¹, hpowR n a a.2⟩ : ↥R) : ↥R ⧸ N) := by
    intro n
    induction n with
    | zero =>
      intro a
      rw [Function.iterate_zero_apply]
      congr 1
      apply Subtype.ext
      simp
    | succ m ih =>
      intro a
      rw [Function.iterate_succ_apply', ih, hYmk]
      congr 1
      apply Subtype.ext
      show y * (y ^ m * (a : G) * (y ^ m)⁻¹) * y⁻¹ = y ^ (m + 1) * a * (y ^ (m + 1))⁻¹
      rw [pow_succ']
      group
  have hYid : ∀ x : ↥R ⧸ N, Y^[2 ^ k] x = x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [hYpow]
      congr 1
      apply Subtype.ext
      show y ^ 2 ^ k * (a : G) * (y ^ 2 ^ k)⁻¹ = a
      rw [hyk]
      group
  have hZ3 : ∀ x : ↥R ⧸ N, Z (Z (Z x)) = x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [hZmk, hZmk, hZmk]
      congr 1
      apply Subtype.ext
      show z * (z * (z * (a : G) * z⁻¹) * z⁻¹) * z⁻¹ = a
      have hz3' : z * z * z = 1 := by rw [← pow_three']; exact hz3
      calc z * (z * (z * (a : G) * z⁻¹) * z⁻¹) * z⁻¹ = (z * z * z) * a * (z * z * z)⁻¹ := by
            group
        _ = a := by rw [hz3']; group
  have hZfix : ∀ x : ↥R ⧸ N, Z x = x → x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      intro hx
      rw [hZmk] at hx
      have h1 := QuotientGroup.eq.mp hx.symm
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : (a : G) ∈ V₀ := hzfix a a.2 h1
      exact (QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_subgroupOf.mpr h2)
  have hYZ : ∀ x : ↥R ⧸ N, Y (Z x) = Z (Y x) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [hZmk, hYmk, hYmk, hZmk]
      congr 1
      apply Subtype.ext
      exact hyz a a.2
  have hQ4 : Nat.card (↥R ⧸ N) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : Nat.card N = Nat.card V₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀R).toEquiv
    rw [h2, hcard] at h1
    have hV0 : 0 < Nat.card V₀ := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hV0 h1).symm
  classical
  have : Fintype (↥R ⧸ N) := Fintype.ofFinite _
  have hnt : Nontrivial (↥R ⧸ N) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQ4]
    norm_num
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥R ⧸ N)
  have hZinj : ∀ w : ↥R ⧸ N, Z w = 1 → w = 1 := by
    intro w hw
    rw [← hZ3 w, hw, map_one, map_one]
  have hZx1 : Z x ≠ 1 := fun h0 => hx1 (hZinj x h0)
  have hZZx1 : Z (Z x) ≠ 1 := fun h0 => hZx1 (hZinj _ h0)
  have hxZ : x ≠ Z x := fun h0 => hx1 (hZfix x h0.symm)
  have hxZZ : x ≠ Z (Z x) := by
    intro h0
    apply hxZ
    calc x = Z (Z (Z x)) := (hZ3 x).symm
      _ = Z x := by rw [← h0]
  have hZZZ : Z x ≠ Z (Z x) := fun h0 => hZx1 (hZfix _ h0.symm)
  have huniv : ∀ w : ↥R ⧸ N, w = 1 ∨ w = x ∨ w = Z x ∨ w = Z (Z x) := by
    intro w
    have hcardS : ({1, x, Z x, Z (Z x)} : Finset (↥R ⧸ N)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hZZZ]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxZ, hxZZ⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hx1.symm, hZx1.symm, hZZx1.symm⟩
    have heq := Finset.eq_univ_of_card _ (by rw [hcardS, ← Nat.card_eq_fintype_card, hQ4])
    have hw : w ∈ ({1, x, Z x, Z (Z x)} : Finset (↥R ⧸ N)) := by rw [heq]; exact Finset.mem_univ w
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
  have hZmod : ∀ n : ℕ, ∀ w : ↥R ⧸ N, Z^[n] w = Z^[n % 3] w := by
    intro n w
    conv_lhs => rw [← Nat.mod_add_div n 3]
    rw [Function.iterate_add_apply]
    congr 1
    induction n / 3 with
    | zero => rfl
    | succ q ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, show Z^[3] w = w from hZ3 w, ih]
  have hk3 : 2 ^ k % 3 ≠ 0 := by
    intro h0
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hk3' : 2 ^ (k + 1) % 3 ≠ 0 := by
    intro h0
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hYx1 : Y x ≠ 1 := by
    intro h0
    apply hx1
    have h1 := hYid x
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = m + 1 :=
      ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
    rw [hm, Function.iterate_succ_apply, h0, Function.iterate_fixed (map_one Y)] at h1
    exact h1.symm
  have hcase : Y x = x := by
    rcases huniv (Y x) with h0 | h0 | h0 | h0
    · exact absurd h0 hYx1
    · exact h0
    · exfalso
      have hYeq : ∀ w, Y w = Z w := by
        intro w
        rcases huniv w with rfl | rfl | rfl | rfl
        · rw [map_one, map_one]
        · exact h0
        · rw [hYZ, h0]
        · rw [hYZ, hYZ, h0]
      have hfun : (⇑Y : ↥R ⧸ N → ↥R ⧸ N) = ⇑Z := funext hYeq
      have h1 := hYid x
      rw [hfun, hZmod] at h1
      have hlt := Nat.mod_lt (2 ^ k) (show 3 > 0 by norm_num)
      interval_cases hm : 2 ^ k % 3
      · exact absurd rfl hk3
      · exact hxZ h1.symm
      · exact hxZZ h1.symm
    · exfalso
      have hYeq : ∀ w, Y w = Z (Z w) := by
        intro w
        rcases huniv w with rfl | rfl | rfl | rfl
        · rw [map_one, map_one, map_one]
        · exact h0
        · rw [hYZ, h0]
        · rw [hYZ, hYZ, h0]
      have hfun : (⇑Y : ↥R ⧸ N → ↥R ⧸ N) = Z^[2] := funext hYeq
      have h1 := hYid x
      rw [hfun, ← Function.iterate_mul, hZmod, show 2 * 2 ^ k = 2 ^ (k + 1) by ring] at h1
      have hlt := Nat.mod_lt (2 ^ (k + 1)) (show 3 > 0 by norm_num)
      interval_cases hm : 2 ^ (k + 1) % 3
      · exact absurd rfl hk3'
      · exact hxZ h1.symm
      · exact hxZZ h1.symm
  have hYw : ∀ w, Y w = w := by
    intro w
    rcases huniv w with rfl | rfl | rfl | rfl
    · exact map_one Y
    · exact hcase
    · rw [hYZ, hcase]
    · rw [hYZ, hYZ, hcase]
  intro a ha
  have h1 := hYw ((⟨a, ha⟩ : ↥R) : ↥R ⧸ N)
  rw [hYmk] at h1
  have h2 := QuotientGroup.eq.mp h1.symm
  rw [Subgroup.mem_subgroupOf] at h2
  exact h2

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem V0_le_rR (e : Extra3 T L V H P U I h) : V ⊓ pCoreOf 2 H ≤ rR V H P := by
  obtain ⟨-, -, -, ⟨hcommV, -⟩, -⟩ := e.concl
  intro x hx
  refine ⟨le_conjClosure _ _ hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  exact congrArg Subtype.val (hcommV.is_comm.comm ⟨y, hy⟩ ⟨x, hx.1⟩)

theorem rR_inf_V (e : Extra3 T L V H P U I h) : rR V H P ⊓ V = V ⊓ pCoreOf 2 H := by
  refine le_antisymm (fun x hx => ⟨hx.2, (e.W_le_center hx.1.1).1⟩) fun x hx =>
    ⟨e.V0_le_rR hx, hx.1⟩

theorem rR_le_T (h331 : Stmt3_3_1) (e : Extra3 T L V H P U I h) : rR V H P ≤ T := by
  obtain ⟨hHs, -⟩ := e.pre
  exact fun x hx => pCoreOf_two_le_of_isSylowTwoOf (Lem7.minParabolic h331 e.hyp hHs).isSylow
    (e.W_le_center hx.1).1

theorem rR_elem (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    (∀ a ∈ rR V H P, ∀ b ∈ rR V H P, a * b = b * a) ∧ ∀ a ∈ rR V H P, a ^ 2 = 1 := by
  obtain ⟨hWc, hW2⟩ := e.W_elem h1222
  exact ⟨fun a ha b hb => hWc a ha.1 b hb.1, fun a ha => hW2 a ha.1⟩

theorem T_le_normalizer_rR (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) : T ≤ Subgroup.normalizer ((rR V H P : Subgroup G) : Set G) := by
  obtain ⟨hHs, -⟩ := e.pre
  have hTH : T ≤ H := (Lem7.minParabolic h331 e.hyp hHs).isSylow.1
  have hHW := e.le_normalizer_W h331 h1222
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  intro t ht
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hHW (hTH ht), B6.le_normalizer_centralizer hTV ht⟩

theorem frattini_le_normalizer_rR (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) :
    (frattini ↥P).map P.subtype ≤ Subgroup.normalizer ((rR V H P : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, -, -, hPH, -⟩ := e.pre
  have hHW := e.le_normalizer_W h331 h1222
  intro f hf
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hHW (hPH (frattini_map_le P hf)), B6.le_normalizer_centralizer e.ΦV hf⟩

theorem rR_fix (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) {f : G}
    (hf : f ∈ (frattini ↥P).map P.subtype)
    (hf1 : f ≠ 1) {a : G} (ha : a ∈ rR V H P) (hfa : f * a * f⁻¹ = a) : a = 1 := by
  have hzp := e.zpowers_eq hf hf1
  have hfa' : f * a = a * f := by
    calc f * a = (f * a * f⁻¹) * f := by group
      _ = a * f := by rw [hfa]
  have hac : a ∈ conjClosure (V ⊓ pCoreOf 2 H) P ⊓
      Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) := by
    refine ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    rw [← hzp] at hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact Commute.zpow_left hfa' k
  rw [e.W_inf_centralizer h331 h1222, Subgroup.mem_bot] at hac
  exact hac

theorem eq_one_of_mem_T (h331 : Stmt3_3_1) (e : Extra3 T L V H P U I h) {g : G}
    (hg : g ∈ (frattini ↥P).map P.subtype) (hgT : g ∈ T) : g = 1 := by
  obtain ⟨hHs, -⟩ := e.pre
  have hT2 : IsPGroup 2 ↥T := (Lem7.minParabolic h331 e.hyp hHs).isSylow.2.1
  obtain ⟨k, hk⟩ := hT2 ⟨g, hgT⟩
  have hgk : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hg3 : g ^ 3 = 1 := e.exp g (frattini_map_le P hg)
  have h1 : orderOf g ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgk) (orderOf_dvd_of_pow_eq_one hg3)
  have h2 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem comm_CT_mem_rR (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    ∀ f ∈ (frattini ↥P).map P.subtype, ∀ y ∈ T ⊓ Subgroup.centralizer (V : Set G),
      f * y * f⁻¹ * y⁻¹ ∈ rR V H P := by
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, -, -, hhP, hhM, -⟩ := e.pre
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hΦP : Φ ≤ P := frattini_map_le P
  have hcommW := e.comm_mem_W h331 h1222
  have hΦQ : Φ ≤ Subgroup.normalizer (Q : Set G) := e.frattini_le_normalizer_CT h331 h1222
  have hWT : conjClosure (V ⊓ pCoreOf 2 H) P ≤ T := fun w hw => hQT (e.W_le_center hw).1
  intro f hf y hy
  obtain ⟨q₀, hq₀, hn₀⟩ := exists_mul_mem_normalizer h331 e.hyp hHs hsol hp hp2 hPp hPH hPi hP1
    (hTH hy.1)
  set f' := (q₀ * y) * f⁻¹ * (q₀ * y)⁻¹ with hf'
  have hf'Φ : f' ∈ Φ := conj_mem_frattini hn₀ (Φ.inv_mem hf)
  have hw₁ : f'⁻¹ * q₀⁻¹ * f'⁻¹⁻¹ * q₀⁻¹⁻¹ ∈ conjClosure (V ⊓ pCoreOf 2 H) P :=
    hcommW _ (P.inv_mem (hΦP hf'Φ)) _ ((pCoreOf 2 H).inv_mem hq₀)
  have e1 : f * y * f⁻¹ * y⁻¹ = (f * f') * (f'⁻¹ * q₀⁻¹ * f'⁻¹⁻¹ * q₀⁻¹⁻¹) := by
    rw [hf']
    group
  have hc : f * y * f⁻¹ * y⁻¹ ∈ Q :=
    Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hΦQ hf) y).mp hy) (Q.inv_mem hy)
  have hff'T : f * f' ∈ T := by
    have e2 : f * f' = (f * y * f⁻¹ * y⁻¹) * (f'⁻¹ * q₀⁻¹ * f'⁻¹⁻¹ * q₀⁻¹⁻¹)⁻¹ := by
      rw [e1]
      group
    rw [e2]
    exact T.mul_mem hc.1 (T.inv_mem (hWT hw₁))
  have hff'1 : f * f' = 1 := e.eq_one_of_mem_T h331 (Φ.mul_mem hf hf'Φ) hff'T
  have e3 : f * y * f⁻¹ * y⁻¹ = f'⁻¹ * q₀⁻¹ * f'⁻¹⁻¹ * q₀⁻¹⁻¹ := by
    rw [e1, hff'1, one_mul]
  refine ⟨?_, hc.2⟩
  rw [e3]
  exact hw₁

theorem card_rR (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    Nat.card (rR V H P) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  set W := conjClosure (V ⊓ pCoreOf 2 H) P with hW
  have hVO := Lem21.not_le_pCoreOf_of_pre e.pre
  obtain ⟨hHs, -, -, -, -, hPH, -, -, -, hhP, -, -, -, hUsplit, -, -, -, -, hidx,
    hcommV', htr⟩ := e.pre
  obtain ⟨-, -, htop, ⟨hcommV, hnatV⟩, -⟩ := e.concl
  obtain ⟨DV⟩ := hnatV.toL3Coord
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 e.hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hHO : H ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hWT : W ≤ T := fun w hw => hQT (e.W_le_center hw).1
  have hWV : W ≤ Subgroup.normalizer (V : Set G) := hWT.trans hTV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := e.hyp.irrPlus.2.2.1
  have hUW : U ≤ W := by
    rw [hUsplit]
    refine sup_le (fun x hx => le_conjClosure _ _ ⟨hx.2, e.UO hx.1⟩) ?_
    rintro x ⟨hxU, hxV⟩
    obtain ⟨v', hv', rfl⟩ := hxV
    have hx' : h⁻¹ * v' * h⁻¹⁻¹ ∈ pCoreOf 2 H := e.UO hxU
    have hv'Q : v' ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (hHO (hPH hhP)) _).mp hx'
      simpa [mul_assoc] using this
    exact Subgroup.subset_closure ⟨h⁻¹, P.inv_mem hhP, v', ⟨hv', hv'Q⟩, rfl⟩
  obtain ⟨v, hvV, hvO⟩ := IsConcreteLE.not_le_iff_exists.mp hVO
  have hvU : v ∉ U := fun h0 => hvO (e.UO h0)
  have hUN : U ≤ Subgroup.normalizer (V : Set G) := fun x hx => hTV (hQT (e.UO hx))
  have := hcommV'
  have hle := inf_le_commutator hUN hV2 htr hidx hvV hvU
  have hUV1 : U ⊓ V ≠ ⊥ := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card (U ⊓ V) V
    rw [hidx, inf_assoc, inf_idem, h0, Subgroup.card_bot, e.concl.2.1] at h1
    norm_num at h1
  have hUc : ¬ U ≤ Subgroup.centralizer (V : Set G) := by
    intro h0
    apply hUV1
    rw [eq_bot_iff]
    refine hle.trans ?_
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr h0]
  obtain ⟨u, huU, huc⟩ := IsConcreteLE.not_le_iff_exists.mp hUc
  have hcard := card_autOn_mul hWV
  rw [e.card_W h331 h1222] at hcard
  have hAW2 : IsPGroup 2 ↥(autOn W V) := by
    have hWsub : IsPGroup 2 ↥(W.subgroupOf (Subgroup.normalizer (V : Set G))) := by
      intro x
      obtain ⟨k, hk⟩ := hT2 ⟨((x : ↥(Subgroup.normalizer (V : Set G))) : G),
        hWT (Subgroup.mem_subgroupOf.mp x.2)⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hk
    exact hWsub.map (conjAct V)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hAW2
  have hdvd : Nat.card (autOn W V) ∣ 168 := by
    rw [← DV.card_G]
    exact Subgroup.card_dvd_of_le (A4.autOn_mono (e.W_le h331 h1222))
  have hj3 : j ≤ 3 := by
    rw [hj] at hdvd
    by_contra hj3
    push Not at hj3
    have h16 : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 hj3).trans hdvd
    norm_num at h16
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    rw [hj, one_mul] at hcard
    have heq : W ⊓ Subgroup.centralizer (V : Set G) = W :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, e.card_W h331 h1222])
    have hu' : u ∈ W ⊓ Subgroup.centralizer (V : Set G) := by
      rw [heq]
      exact hUW huU
    exact huc hu'.2
  have hR3 : Nat.card ↥(rR V H P) ≡ 1 [MOD 3] := by
    have hΦ3 : IsPGroup 3 ↥Φ := IsPGroup.of_card (n := 1) (by rw [e.cardΦ]; norm_num)
    have hΦR := e.frattini_le_normalizer_rR h331 h1222
    let _ : MulAction ↥Φ ↥(rR V H P) :=
      { smul := fun f r => ⟨(f : G) * r * (f : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hΦR f.2) r).mp r.2⟩
        one_smul := fun r => Subtype.ext (by
          show ((1 : ↥Φ) : G) * (r : G) * ((1 : ↥Φ) : G)⁻¹ = r
          simp)
        mul_smul := fun f g r => Subtype.ext (by
          show (f * g : G) * r * (f * g : G)⁻¹ = f * (g * r * (g : G)⁻¹) * (f : G)⁻¹
          group) }
    have h1 := hΦ3.card_modEq_card_fixedPoints ↥(rR V H P)
    have hfix : MulAction.fixedPoints ↥Φ ↥(rR V H P) = {1} := by
      ext r
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro hr
        have hne : ∃ f ∈ Φ, f ≠ 1 := by
          have h3 : 1 < Nat.card Φ := by rw [e.cardΦ]; norm_num
          have := Finite.one_lt_card_iff_nontrivial.mp h3
          obtain ⟨⟨f, hf⟩, hf1⟩ := exists_ne (1 : ↥Φ)
          exact ⟨f, hf, fun h0 => hf1 (Subtype.ext h0)⟩
        obtain ⟨f, hf, hf1⟩ := hne
        have h2 := congrArg Subtype.val (hr ⟨f, hf⟩)
        exact Subtype.ext (e.rR_fix h331 h1222 hf hf1 r.2 h2)
      · rintro rfl f
        exact Subtype.ext (by show (f : G) * 1 * (f : G)⁻¹ = 1; group)
    have h2 : Nat.card ↑({1} : Set ↥(rR V H P)) = 1 := Nat.card_unique
    rw [hfix, h2] at h1
    exact h1
  rw [hj] at hcard
  interval_cases j
  · omega
  · have h32 : Nat.card ↥(rR V H P) = 32 := by
      have : (2 : ℕ) ^ 1 * Nat.card ↥(rR V H P) = 64 := hcard
      omega
    rw [h32] at hR3
    exact absurd hR3 (by decide)
  · have : (2 : ℕ) ^ 2 * Nat.card ↥(rR V H P) = 64 := hcard
    omega
  · have h8 : Nat.card ↥(rR V H P) = 8 := by
      have : (2 : ℕ) ^ 3 * Nat.card ↥(rR V H P) = 64 := hcard
      omega
    rw [h8] at hR3
    exact absurd hR3 (by decide)

theorem comm_rR_CT (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    ∀ r ∈ rR V H P, ∀ y ∈ T ⊓ Subgroup.centralizer (V : Set G),
      y * r * y⁻¹ * r⁻¹ ∈ V ⊓ pCoreOf 2 H := by
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  set R := rR V H P with hRdef
  set V₀ := V ⊓ pCoreOf 2 H with hV₀def
  obtain ⟨hHs, -⟩ := e.pre
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  obtain ⟨hRc, -⟩ := e.rR_elem h1222
  have hTR := e.T_le_normalizer_rR h331 h1222
  have hΦR := e.frattini_le_normalizer_rR h331 h1222
  obtain ⟨-, hΦV₀, hV₀C⟩ := e.eq_inf
  have hTV₀ : T ≤ Subgroup.normalizer ((V₀ : Subgroup G) : Set G) := by
    obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
      e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
    obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
    have hTH : T ≤ H := hmin.isSylow.1
    exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTV ht, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH ht)⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥Φ := isCyclic_of_prime_card e.cardΦ
  obtain ⟨⟨z, hzΦ⟩, hgen⟩ := hcyc.exists_generator
  have hz1 : z ≠ 1 := by
    intro h0
    have h3 : Nat.card Φ = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen a)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen b)
      rw [← hi, ← hj]
      have h1 : (⟨z, hzΦ⟩ : ↥Φ) = 1 := Subtype.ext h0
      rw [h1, one_zpow, one_zpow]
    rw [e.cardΦ] at h3
    norm_num at h3
  have hzR : ∀ a ∈ R, z * a * z⁻¹ ∈ R := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hΦR hzΦ) a).mp ha
  have hzV : ∀ a ∈ V₀, z * a * z⁻¹ ∈ V₀ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hΦV₀ hzΦ) a).mp ha
  have hzfix : ∀ a ∈ R, a⁻¹ * (z * a * z⁻¹) ∈ V₀ → a ∈ V₀ := by
    intro a ha hav
    have hfixV : ∀ b ∈ V₀, z * b * z⁻¹ = b → b = 1 := by
      intro b hb hzb
      exact e.rR_fix h331 h1222 hzΦ hz1 (e.V0_le_rR hb) hzb
    obtain ⟨b, hb, hbe⟩ := exists_eq_inv_mul_conj hzV hfixV _ hav
    have hab : b * a⁻¹ ∈ R := R.mul_mem (e.V0_le_rR hb) (R.inv_mem ha)
    have hfx : z * (b * a⁻¹) * z⁻¹ = b * a⁻¹ := by
      have e1 : z * a * z⁻¹ = a * (b⁻¹ * (z * b * z⁻¹)) := by
        rw [← hbe]
        group
      calc z * (b * a⁻¹) * z⁻¹ = (z * b * z⁻¹) * (z * a * z⁻¹)⁻¹ := by group
        _ = (z * b * z⁻¹) * (a * (b⁻¹ * (z * b * z⁻¹)))⁻¹ := by rw [e1]
        _ = b * a⁻¹ := by group
    have h1 := e.rR_fix h331 h1222 hzΦ hz1 hab hfx
    have h2 : a = b := (mul_inv_eq_one.mp h1).symm
    rw [h2]
    exact hb
  intro r hr y hy
  obtain ⟨k, hk⟩ := hT2 ⟨y, hy.1⟩
  have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hyR : ∀ a ∈ R, y * a * y⁻¹ ∈ R := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hTR hy.1) a).mp ha
  have hyV : ∀ a ∈ V₀, y * a * y⁻¹ ∈ V₀ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hTV₀ hy.1) a).mp ha
  have hyz : ∀ a ∈ R, y * (z * a * z⁻¹) * y⁻¹ = z * (y * a * y⁻¹) * z⁻¹ := by
    intro a ha
    have hkR : z * y * z⁻¹ * y⁻¹ ∈ R := e.comm_CT_mem_rR h331 h1222 z hzΦ y hy
    have hc : (z * y * z⁻¹ * y⁻¹) * (y * (z * a * z⁻¹) * y⁻¹) =
        (y * (z * a * z⁻¹) * y⁻¹) * (z * y * z⁻¹ * y⁻¹) := hRc _ hkR _ (hyR _ (hzR a ha))
    calc y * (z * a * z⁻¹) * y⁻¹
        = ((y * (z * a * z⁻¹) * y⁻¹) * (z * y * z⁻¹ * y⁻¹)) * (z * y * z⁻¹ * y⁻¹)⁻¹ := by group
      _ = ((z * y * z⁻¹ * y⁻¹) * (y * (z * a * z⁻¹) * y⁻¹)) * (z * y * z⁻¹ * y⁻¹)⁻¹ := by
          rw [hc]
      _ = z * (y * a * y⁻¹) * z⁻¹ := by group
  have hcard : Nat.card R = 4 * Nat.card V₀ := by
    rw [hRdef, e.card_rR h331 h1222, hV₀def, e.card_inf]
  have h1 := comm_mem_of_fpf_four (e.V0_le_rR) hRc hcard hzR hzV (e.exp z (frattini_map_le P hzΦ))
    hzfix hyR hyV hyk hyz r hr
  have hc := hRc _ (R.inv_mem hr) _ (hyR r hr)
  rw [show y * r * y⁻¹ * r⁻¹ = r⁻¹ * (y * r * y⁻¹) from hc.symm]
  exact h1

end Extra3

end Lem22

end CFSG.Quasithin.H13
