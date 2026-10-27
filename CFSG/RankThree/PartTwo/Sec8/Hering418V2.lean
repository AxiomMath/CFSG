module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Cfg
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE9
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE9Gen

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open

theorem exists_sub_of_surjective_coprime {C Q : Type*} [Group C] [Group Q] [Finite C]
    (π : C →* Q) (hπ : Function.Surjective π) {k : ℕ} (hQ : Nat.card Q = 3 ^ k)
    (hker : ¬ 3 ∣ Nat.card π.ker) :
    ∃ S : Subgroup C, Nat.card S = 3 ^ k ∧ Function.Injective (π.comp S.subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ k ∣ Nat.card C := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hπ, hQ]
    exact Dvd.intro_left _ rfl
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  refine ⟨S, hS, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  set f : S →* Q := π.comp S.subtype with hf
  let g : f.ker →* π.ker :=
    { toFun := fun x => ⟨(x.1 : C), by
        have := x.2
        rw [MonoidHom.mem_ker] at this ⊢
        exact this⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hg : Function.Injective g := by
    intro x y h
    have h' := congrArg (fun z : π.ker => (z : C)) h
    apply Subtype.ext
    apply Subtype.ext
    exact h'
  have h1 : Nat.card f.ker ∣ Nat.card π.ker := Subgroup.card_dvd_of_injective g hg
  have h2 : Nat.card f.ker ∣ 3 ^ k := hS ▸ Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card π.ker) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker)
  have h3 : Nat.card f.ker = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h2) h1
  exact Subgroup.eq_bot_of_card_eq _ h3

theorem isElemAbelian_of_injective_map {C Q : Type*} [Group C] [Group Q] (π : C →* Q)
    {E : Subgroup C} (hinj : Function.Injective (π.comp E.subtype))
    (hE : IsElemAbelian 3 (E.map π)) : IsElemAbelian 3 E := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply hinj
    have hx' : π x ∈ E.map π := ⟨x, x.2, rfl⟩
    have hy' : π y ∈ E.map π := ⟨y, y.2, rfl⟩
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨π x, hx'⟩ ⟨π y, hy'⟩)
    simpa using this
  · have h3 : (⟨x, hx⟩ : E) ^ 3 = 1 := by
      apply hinj
      have hx' : π x ∈ E.map π := ⟨x, hx, rfl⟩
      have := hE.2 _ hx'
      simpa using this
    simpa using congrArg Subtype.val h3

theorem zpow_apply_eq_of_apply_eq {M : Type*} [Group M] (σ : MulAut M) {y : M} (h : σ y = y)
    (m : ℤ) : (σ ^ m) y = y := by
  have h' : σ⁻¹ y = y := by
    rw [MulAut.inv_def]
    exact (MulEquiv.symm_apply_eq σ).mpr h.symm
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, MulAut.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply, h', ih]

theorem exists_elemAbelian_lift {G : Type} [Group G] [Finite G] {K : Subgroup G} {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1)
    {E₀ : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} {k : ℕ} (hE₀ : IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ k)
    (hfix : ∀ y ∈ E₀, Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) y = y) :
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧
      (∀ e ∈ E, a * (e : G) = (e : G) * a) ∧
      E.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) = E₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ : Subgroup K := aschbacherSolvableCore 3 K with hθ
  set π₀ : K →* K ⧸ θ := QuotientGroup.mk' θ with hπ₀
  obtain ⟨hθs, -, hθ3, -, -⟩ := solvable_prime_complement_core_characterization (H := K)
    Nat.prime_three
  have hle : Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr haK
  let φ : Subgroup.zpowers a →* MulAut K := (Subgroup.normalizerMonoidHom K).comp
    (Subgroup.inclusion hle)
  have hP : IsPGroup 3 (Subgroup.zpowers a) := isPGroup_zpowers_three ha3
  have hφ : ∀ (g : Subgroup.zpowers a) (x : K),
      (((φ g) x : K) : G) = (g : G) * (x : G) * (g : G)⁻¹ := fun g x => rfl
  have hφE : ∀ (g : Subgroup.zpowers a) (y : K ⧸ θ), y ∈ E₀ →
      Sec4.thetaQuotMulAut K (φ g) y = y := by
    intro g y hy
    obtain ⟨g, m, rfl⟩ := g
    have hg : (⟨a ^ m, m, rfl⟩ : Subgroup.zpowers a) = (⟨a, Subgroup.mem_zpowers a⟩ :
        Subgroup.zpowers a) ^ m := by
      apply Subtype.ext
      simp
    rw [hg, map_zpow, map_zpow]
    exact zpow_apply_eq_of_apply_eq _ (hfix y hy) m
  let C : Subgroup K := E₀.comap π₀ ⊓ (Subgroup.centralizer ({a} : Set G)).comap K.subtype
  let π : C →* E₀ := (π₀.comp C.subtype).codRestrict E₀ (fun c => c.2.1)
  have hπs : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk'_surjective θ y
    obtain ⟨k', hk', hfixk⟩ := KFacts.exists_fixed_of_coprime hP φ θ hθ3
      (fun g n hn => by
        have h := Sec4.map_aschbacherSolvableCore (H := K) (φ g)
        have hmem : (φ g) n ∈ Subgroup.map ((φ g : MulAut K) : K →* K)
            (aschbacherSolvableCore 3 K) := Subgroup.mem_map_of_mem _ hn
        have hh : (φ g) n ∈ aschbacherSolvableCore 3 K := h ▸ hmem
        exact hh)
      k₀ (fun g => by
        rw [← Sec4.thetaQuotMulAut_mk (φ g) k₀]
        have := hφE g y hy
        rw [← hk₀] at this
        exact this)
    have hmk : π₀ k' = y := by rw [← hk₀]; exact hk'
    have hcomm : (k' : G) * a = a * (k' : G) := by
      have h1 := hfixk ⟨a, Subgroup.mem_zpowers a⟩
      have h2 := congrArg (fun z : K => (z : G)) h1
      change a * (k' : G) * a⁻¹ = k' at h2
      calc (k' : G) * a = a * (k' : G) * a⁻¹ * a := by rw [h2]
        _ = a * (k' : G) := by group
    refine ⟨⟨k', ⟨?_, ?_⟩⟩, Subtype.ext hmk⟩
    · show π₀ k' ∈ E₀
      rw [hmk]; exact hy
    · show (k' : G) ∈ Subgroup.centralizer ({a} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    intro h3
    let g : π.ker →* θ :=
      { toFun := fun x => ⟨(x.1 : K), by
          have hx := x.2
          rw [MonoidHom.mem_ker] at hx
          have : π₀ (x.1 : K) = 1 := congrArg Subtype.val hx
          exact (QuotientGroup.eq_one_iff _).mp this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro x y h
      have h' := congrArg (fun z : θ => ((z : K))) h
      apply Subtype.ext
      apply Subtype.ext
      exact h'
    exact hθ3 (h3.trans (Subgroup.card_dvd_of_injective g hg))
  obtain ⟨S, hS, hSinj⟩ := exists_sub_of_surjective_coprime π hπs (Q := E₀) hcard hker
  have hSinj' : Function.Injective ((π₀.comp C.subtype).comp S.subtype) := by
    intro x y h
    apply hSinj
    apply Subtype.ext
    exact h
  set E : Subgroup K := S.map C.subtype with hE
  have hmapE : E.map π₀ = S.map (π₀.comp C.subtype) := by
    rw [hE, Subgroup.map_map]
  have hcardmap : Nat.card (S.map (π₀.comp C.subtype)) = 3 ^ k := by
    have hr : ((π₀.comp C.subtype).comp S.subtype).range = S.map (π₀.comp C.subtype) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hSinj').toEquiv, hS]
  have hle : S.map (π₀.comp C.subtype) ≤ E₀ := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2.1
  have hEq : S.map (π₀.comp C.subtype) = E₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardmap, hcard])
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · refine isElemAbelian_of_injective_map π₀ ?_ ?_
    · intro x y h
      obtain ⟨_, ⟨s₁, hs₁, rfl⟩⟩ := x
      obtain ⟨_, ⟨s₂, hs₂, rfl⟩⟩ := y
      have := hSinj' (a₁ := ⟨s₁, hs₁⟩) (a₂ := ⟨s₂, hs₂⟩) h
      have h12 : s₁ = s₂ := congrArg Subtype.val this
      subst h12
      rfl
    · rw [hmapE, hEq]
      exact hE₀
  · rw [hE, Subgroup.card_map_of_injective C.subtype_injective, hS]
  · rintro e ⟨c, hc, rfl⟩
    have := c.2.2
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  · rw [hmapE, hEq]

open CFSG.RankThree.PartTwo.Sec4.HeringUnitary in
theorem exists_elemAbelian_nine_statedSU {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : 3 ∣ q + 1) :
    ∃ E : Subgroup (CFSG.Assembly.LowTwoRank.StatedSU 3 q F), IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card F := Nat.card_pos
    rw [hF] at this
    simp at this
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h1 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have : 1 ≤ q := Nat.pos_of_ne_zero hq0
      zify [Nat.one_le_pow 2 q this, this]
      ring
    rw [h1]
    exact Dvd.dvd.mul_right hq _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvd
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hω; norm_num at hω
  set w : F := (ω : F) with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hw1 : w ≠ 1 := fun h => hω1 (Units.val_eq_one.mp h)
  have hwq : w ^ q = w ^ 2 := by
    obtain ⟨m, hm⟩ := hq
    obtain ⟨m', e⟩ : ∃ m' : ℕ, q = 3 * m' + 2 := ⟨m - 1, by omega⟩
    rw [e, pow_add, pow_mul, hw3, one_pow, one_mul]
  have hwq2 : (w ^ 2) ^ q = w ^ 4 := by
    rw [pow_right_comm, hwq]
    ring
  obtain ⟨d, hd⟩ := exists_gl_of_det_one (!![1, 0, 0; 0, w, 0; 0, 0, w ^ 2]) (det_diag_three hw3)
  obtain ⟨z, hz⟩ := exists_gl_of_det_one ((Matrix.scalar (Fin 3) w : Matrix (Fin 3) (Fin 3) F))
    (by
      rw [Matrix.det_fin_three]
      simp [Matrix.scalar_apply]
      linear_combination hw3)
  have hdmem : d ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 q F :=
    Subgroup.subset_closure ⟨by rw [hd]; exact det_diag_three hw3,
      by rw [hd]; exact diag_cond hq0 hw3 hwq hwq2⟩
  have hzmem : z ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 q F := by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [hz, Matrix.det_fin_three]
      simp [Matrix.scalar_apply]
      linear_combination hw3
    · rw [hz]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply,
          hq0, hwq] <;>
        first | ring1 | linear_combination hw3 | linear_combination (w ^ 3 + 1) * hw3
  have hd3 : d ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hd, Units.val_one]
    exact diag_pow_three hw3
  have hz3 : z ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hz, Units.val_one, ← map_pow, hw3, map_one]
  have hdz : d * z = z * d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hd, hz]
    exact ((Matrix.scalar_commute w (fun r' => Commute.all w r') _).eq).symm
  have hd00 : (d : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by rw [hd]; simp
  have hd11 : (d : Matrix (Fin 3) (Fin 3) F) 1 1 = w := by rw [hd]; simp
  have hz00 : (z : Matrix (Fin 3) (Fin 3) F) 0 0 = w := by rw [hz]; simp [Matrix.scalar_apply]
  let x : CFSG.Assembly.LowTwoRank.StatedSU 3 q F := ⟨d, hdmem⟩
  let y : CFSG.Assembly.LowTwoRank.StatedSU 3 q F := ⟨z, hzmem⟩
  have hx3 : x ^ 3 = 1 := Subtype.ext hd3
  have hy3 : y ^ 3 = 1 := Subtype.ext hz3
  have hxy : x * y = y * x := Subtype.ext hdz
  have hx1 : x ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : CFSG.Assembly.LowTwoRank.StatedSU 3 q F =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h
    simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq] at h1
    exact hw1 (hd11.symm.trans h1)
  have hy : y ∉ Subgroup.zpowers x := by
    intro hmem
    have hw1' : ∀ g : CFSG.Assembly.LowTwoRank.StatedSU 3 q F,
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 → w = 1 → False :=
      fun g _ h => hw1 h
    rcases mem_zpowers_three_cases hx3 hx1 hmem with h | h | h
    · have h1 := congrArg (fun g : CFSG.Assembly.LowTwoRank.StatedSU 3 q F =>
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) h
      simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq] at h1
      exact hw1 (hz00.symm.trans h1)
    · have h1 := congrArg (fun g : CFSG.Assembly.LowTwoRank.StatedSU 3 q F =>
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) h
      exact hw1 (hz00.symm.trans (h1.trans hd00))
    · have h1 := congrArg (fun g : CFSG.Assembly.LowTwoRank.StatedSU 3 q F =>
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) h
      have h2 : (((x ^ 2 : CFSG.Assembly.LowTwoRank.StatedSU 3 q F) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
        rw [sq, Subgroup.coe_mul, Units.val_mul]
        change ((d : Matrix (Fin 3) (Fin 3) F) * (d : Matrix (Fin 3) (Fin 3) F)) 0 0 = 1
        rw [hd]
        simp [Matrix.mul_apply, Fin.sum_univ_three]
      exact hw1 (hz00.symm.trans (h1.trans h2))
  exact exists_elemAbelian_nine_of_commuting x y hx3 hy3 hxy hx1 hy

theorem zpow_eq_natpow_mod {M : Type*} [Group M] {σ : M} (h3 : σ ^ 3 = 1) (i : ℤ) :
    σ ^ i = σ ^ (i % 3).toNat := by
  rw [zpow_eq_zpow_emod i (n := 3) (by exact_mod_cast h3), ← zpow_natCast,
    Int.toNat_of_nonneg (by omega)]

section Cfg

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G} (c : Cfg L K a b)

include c in
theorem Cfg.alpha_zpow_mul_ne {i : ℤ} (hi : ¬ 3 ∣ i) (j : ℤ) {k : G} (hk : k ∈ K) :
    c.alpha ^ i * c.beta ^ j ≠ rho L ⟨k, L.le_normalizer (c.hKL hk)⟩ := by
  rw [zpow_eq_natpow_mod c.alpha_pow_three i, zpow_eq_natpow_mod c.beta_pow_three j]
  exact rho_pow_mul_ne c.hKL c.hKb c.ha3 c.haL c.hbL c.haK c.hout (i := (i % 3).toNat)
    (j := (j % 3).toNat) (by omega) hk

include c in
theorem Cfg.mem_center_of_rho_eq_zpow {d : G} (hdK : d ∈ K) {j : ℤ}
    (h : rho L ⟨d, L.le_normalizer (c.hKL hdK)⟩ = c.beta ^ j) :
    ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := L.le_normalizer (c.hKL hdK)
  have hbjL : b ^ (-j) ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ c.hbL _
  have hbjK : b ^ (-j) ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ c.hbK _
  have hgL : d * b ^ (-j) ∈ Subgroup.normalizer (L : Set G) := mul_mem hdN hbjL
  have hgK : d * b ^ (-j) ∈ Subgroup.normalizer (K : Set G) :=
    mul_mem (K.le_normalizer hdK) hbjK
  have h1 : rho L ⟨d * b ^ (-j), hgL⟩ = 1 := by
    have e : (⟨d * b ^ (-j), hgL⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨d, hdN⟩ * (⟨b, c.hbL⟩ : Subgroup.normalizer (L : Set G)) ^ (-j) :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_zpow, h]
    change c.beta ^ j * c.beta ^ (-j) = 1
    rw [zpow_neg, mul_inv_cancel]
  have hK1 := thetaQuot_eq_one_of_rho_eq_one c.hKL hgL hgK h1
  have hb1 : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨b, c.hbK⟩) = 1 :=
    thetaQuot_eq_one_of_mem_centralizer c.hbC
  have e : (⟨d * b ^ (-j), hgK⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨d, K.le_normalizer hdK⟩ * (⟨b, c.hbK⟩ : Subgroup.normalizer (K : Set G)) ^ (-j) :=
    Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_zpow, map_zpow, hb1, one_zpow, mul_one,
    thetaQuot_eq_conj K hdK] at hK1
  exact mem_center_of_conj_eq_one hK1

theorem Cfg.e27_of_triple {x y z : MulAut (L ⧸ aschbacherSolvableCore 3 L)}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hx1 : x ≠ 1)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hy : y ∉ Subgroup.zpowers x) (hz : z ∉ Subgroup.closure ({x, y} : Set _))
    (hxm : x ∈ innBar L ⊔ Subgroup.zpowers c.alpha ⊔ Subgroup.zpowers c.beta)
    (hym : y ∈ innBar L ⊔ Subgroup.zpowers c.alpha ⊔ Subgroup.zpowers c.beta)
    (hzm : z ∈ innBar L ⊔ Subgroup.zpowers c.alpha ⊔ Subgroup.zpowers c.beta) : c.E27 := by
  obtain ⟨hF, h27⟩ := isElemAbelian_closure_three hx3 hy3 hz3 hx1 hxy hxz hyz hy hz
  refine ⟨_, hF, h27, ?_⟩
  rw [Subgroup.closure_le]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl <;> assumption

theorem exists_not_mem_zpowers_of_card_nine {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 9) {e : A} (he : orderOf e = 3) : ∃ d : A, d ∉ Subgroup.zpowers e := by
  by_contra h
  push Not at h
  have htop : Subgroup.zpowers e = ⊤ := Subgroup.eq_top_iff' _ |>.mpr h
  have h1 : Nat.card (Subgroup.zpowers e) = Nat.card A := by
    rw [htop, Subgroup.card_top]
  rw [Nat.card_zpowers, he, hA] at h1
  omega

theorem eq_one_of_pow_three_of_mem_theta {K : Type*} [Group K] [Finite K] {t : K}
    (ht3 : t ^ 3 = 1) (ht : t ∈ aschbacherSolvableCore 3 K) : t = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := K)
    Nat.prime_three
  have h1 : orderOf t ∣ Nat.card (aschbacherSolvableCore 3 K) := by
    have := orderOf_dvd_natCard (⟨t, ht⟩ : aschbacherSolvableCore 3 K)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one ht3
  have hcop : Nat.Coprime 3 (Nat.card (aschbacherSolvableCore 3 K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have : orderOf t ∣ Nat.gcd 3 (Nat.card (aschbacherSolvableCore 3 K)) := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

include c in
theorem Cfg.e27_of_elemAbelian_nine
    (hZ3 : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) ≤ 3)
    {E : Subgroup K} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEa : ∀ e ∈ E, a * ((e : K) : G) = ((e : K) : G) * a) : c.E27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hEc : IsMulCommutative E := hE.1
  let ρE : E →* MulAut (L ⧸ aschbacherSolvableCore 3 L) := (rhoK c.hKL).comp E.subtype
  have hρE : ∀ e : E, ρE e =
      rho L ⟨((e : K) : G), L.le_normalizer (c.hKL (e : K).2)⟩ := fun e => rfl
  have hρmem : ∀ e : E, ρE e ∈ innBar L := fun e => rho_mem_innBar L (c.hKL (e : K).2)
  have hE3 : ∀ e : E, e ^ 3 = 1 := fun e => Subtype.ext (hE.2 (e : K) e.2)
  have hρ3 : ∀ e : E, ρE e ^ 3 = 1 := by
    intro e
    rw [← map_pow, hE3 e, map_one]
  have hcα : ∀ e : E, c.alpha * ρE e = ρE e * c.alpha := by
    intro e
    rw [hρE e]
    change rho L ⟨a, c.haL⟩ * _ = _ * rho L ⟨a, c.haL⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEa e e.2)
  have hcβ : ∀ e : E, c.beta * ρE e = ρE e * c.beta := by
    intro e
    rw [hρE e]
    change rho L ⟨b, c.hbL⟩ * _ = _ * rho L ⟨b, c.hbL⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (c.hKb (e : K).2)).symm
  have hcomm : Commute c.alpha c.beta := c.alpha_mul_beta
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
  by_cases hinj : Function.Injective ρE
  ·
    obtain ⟨d₁, hd₁⟩ := exists_ne (1 : E)
    have hd₁3 : orderOf d₁ = 3 := orderOf_eq_prime (hE3 d₁) hd₁
    obtain ⟨d₂, hd₂⟩ := exists_not_mem_zpowers_of_card_nine hE9 hd₁3
    have hy : ρE d₁ ∉ Subgroup.zpowers c.alpha := by
      rintro ⟨i, hi⟩
      replace hi : c.alpha ^ i = ρE d₁ := hi
      by_cases h3 : 3 ∣ i
      · obtain ⟨m, rfl⟩ := h3
        have : c.alpha ^ (3 * m) = 1 := by
          rw [zpow_mul]
          rw [show c.alpha ^ (3 : ℤ) = 1 by exact_mod_cast c.alpha_pow_three, one_zpow]
        rw [this] at hi
        exact hd₁ (hinj (by rw [← hi, map_one]))
      · refine c.alpha_zpow_mul_ne h3 0 (d₁ : K).2 ?_
        rw [zpow_zero, mul_one, hi, hρE d₁]
    have hz : ρE d₂ ∉ Subgroup.closure ({c.alpha, ρE d₁} : Set _) := by
      intro hmem
      obtain ⟨i, j, hij⟩ := (mem_closure_pair_iff (hcα d₁)).mp hmem
      by_cases h3 : 3 ∣ i
      · obtain ⟨m, rfl⟩ := h3
        have h1 : c.alpha ^ (3 * m) = 1 := by
          rw [zpow_mul]
          rw [show c.alpha ^ (3 : ℤ) = 1 by exact_mod_cast c.alpha_pow_three, one_zpow]
        rw [h1, one_mul, ← map_zpow] at hij
        exact hd₂ ⟨j, (hinj hij).symm⟩
      · have he : ρE (d₂ * d₁ ^ (-j)) = c.alpha ^ i := by
          rw [map_mul, map_zpow, hij, zpow_neg, mul_inv_cancel_right]
        refine c.alpha_zpow_mul_ne h3 0 (d₂ * d₁ ^ (-j) : E).1.2 ?_
        rw [zpow_zero, mul_one, ← he, hρE]
    refine c.e27_of_triple c.alpha_pow_three (hρ3 d₁) (hρ3 d₂) c.alpha_ne_one (hcα d₁)
      (hcα d₂) ?_ hy hz ?_ ?_ ?_
    · rw [← map_mul, ← map_mul, mul_comm' d₁ d₂]
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hρmem d₁))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hρmem d₂))
  ·
    have hne : ¬ ∀ e : E, ρE e = 1 → e = 1 := fun h => hinj ((injective_iff_map_eq_one ρE).mpr h)
    push Not at hne
    obtain ⟨e₁, he₁ρ, he₁⟩ := hne
    have he₁3 : orderOf e₁ = 3 := orderOf_eq_prime (hE3 e₁) he₁
    set θ : Subgroup K := aschbacherSolvableCore 3 K with hθ
    have hē₁c : ((e₁ : K) : K ⧸ θ) ∈ Subgroup.center (K ⧸ θ) := by
      have := c.mem_center_of_rho_eq_zpow (d := ((e₁ : K) : G)) (e₁ : K).2 (j := 0)
        (by rw [zpow_zero, ← hρE e₁]; exact he₁ρ)
      exact this
    have hē₁1 : ((e₁ : K) : K ⧸ θ) ≠ 1 := by
      intro h
      apply he₁
      have hm : (e₁ : K) ∈ θ := (QuotientGroup.eq_one_iff _).mp h
      exact Subtype.ext (eq_one_of_pow_three_of_mem_theta (hE.2 (e₁ : K) e₁.2) hm)
    have hē₁3 : orderOf ((e₁ : K) : K ⧸ θ) = 3 := by
      refine orderOf_eq_prime ?_ hē₁1
      have := hE.2 (e₁ : K) e₁.2
      rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
    have hZgen : ∀ z ∈ Subgroup.center (K ⧸ θ), z ∈ Subgroup.zpowers ((e₁ : K) : K ⧸ θ) := by
      have hle : Subgroup.zpowers ((e₁ : K) : K ⧸ θ) ≤ Subgroup.center (K ⧸ θ) :=
        Subgroup.zpowers_le.mpr hē₁c
      have hcard : Nat.card (Subgroup.center (K ⧸ θ)) ≤
          Nat.card (Subgroup.zpowers ((e₁ : K) : K ⧸ θ)) := by
        rw [Nat.card_zpowers, hē₁3]; exact hZ3
      have := Subgroup.eq_of_le_of_card_ge hle hcard
      intro z hz
      rw [this]; exact hz
    obtain ⟨d, hd⟩ := exists_not_mem_zpowers_of_card_nine hE9 he₁3
    have hdnot : ∀ j : ℤ, ρE d ≠ c.beta ^ j := by
      intro j hj
      have hz := c.mem_center_of_rho_eq_zpow (d := ((d : K) : G)) (d : K).2 (j := j)
        (by rw [← hρE d]; exact hj)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hZgen _ hz)
      have hmem : (d : K)⁻¹ * (e₁ : K) ^ i ∈ θ := by
        have : ((d : K) : K ⧸ θ) = ((e₁ : K) : K ⧸ θ) ^ i := hi.symm
        rw [← QuotientGroup.mk_zpow] at this
        exact QuotientGroup.eq.mp this
      have ht3 : (((d⁻¹ * e₁ ^ i : E)) : K) ^ 3 = 1 := congrArg Subtype.val (hE3 _)
      have ht : (((d⁻¹ * e₁ ^ i : E)) : K) = 1 :=
        eq_one_of_pow_three_of_mem_theta ht3 hmem
      have ht' : d⁻¹ * e₁ ^ i = 1 := Subtype.ext ht
      exact hd ⟨i, (inv_mul_eq_one.mp ht').symm⟩
    have hξ : ρE d ∉ Subgroup.closure ({c.alpha, c.beta} : Set _) := by
      intro hmem
      obtain ⟨i, j, hij⟩ := (mem_closure_pair_iff hcomm).mp hmem
      by_cases h3 : 3 ∣ i
      · obtain ⟨m, rfl⟩ := h3
        have h1 : c.alpha ^ (3 * m) = 1 := by
          rw [zpow_mul]
          rw [show c.alpha ^ (3 : ℤ) = 1 by exact_mod_cast c.alpha_pow_three, one_zpow]
        rw [h1, one_mul] at hij
        exact hdnot j hij
      · exact c.alpha_zpow_mul_ne h3 j (d : K).2 (hij.symm.trans (hρE d))
    exact c.e27_of_triple c.alpha_pow_three c.beta_pow_three (hρ3 d) c.alpha_ne_one
      c.alpha_mul_beta (hcα d) (hcβ d) c.beta_notMem_zpowers hξ
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hρmem d)))

end Cfg

end CFSG.RankThree.PartTwo.Sec8.Hering418
