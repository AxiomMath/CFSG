module

public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.OddKernel.FrattiniLinear
public import CFSG.RankThree.OddKernel.EightGroupDims

public section

namespace CFSG.RankThree.OddKernel

open Module Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_inversion_of_elementary_eight {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {W : Type*} [Group W] [Finite W] (hWcomm : ∀ x y : W, x * y = y * x)
    (hWpow : ∀ x : W, x ^ p = 1) {G : Type*} [Group G] (α : G →* MulAut W) {a b c : G}
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1)
    (hne : ∀ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G), α g ≠ 1)
    (hfix : ∀ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G),
      Nat.card {w : W // α g w = w} ≤ p ^ 2)
    (hdet : ∀ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G),
      ∀ (n : ℕ) (e : W ≃* Multiplicative (Fin n → ZMod p)),
        Matrix.GeneralLinearGroup.det (elemAutEquivGL e (α g)) = 1) :
    ∃ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G), ∀ w, α g w = w⁻¹ := by
  classical
  have hWp : IsPGroup p W := fun x => ⟨1, by rw [pow_one, hWpow]⟩
  obtain ⟨n, hn⟩ := hWp.exists_card_eq
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hn
  have h2K : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hm1 : (-1 : ZMod p) ≠ 1 := by
    intro h
    apply h2K
    linear_combination -h
  have hinv : ∀ g : G, g * g = 1 → ∀ v, coordLin e (α g) (coordLin e (α g) v) = v :=
    fun g hg => coordLin_involution e (by rw [← map_mul, hg, map_one])
  have hcomm : ∀ g h : G, g * h = h * g → ∀ v,
      coordLin e (α g) (coordLin e (α h) v) = coordLin e (α h) (coordLin e (α g) v) :=
    fun g h hgh => coordLin_comm e (by rw [← map_mul, hgh, map_mul])
  have hprod : ∀ g h : G, coordLin e (α (g * h)) = coordLin e (α g) ∘ₗ coordLin e (α h) :=
    fun g h => by rw [map_mul, coordLin_mul]
  have hsum := sum_finrank_fix_eight h2K (coordLin e (α a)) (coordLin e (α b))
    (coordLin e (α c)) (hinv a ha) (hinv b hb) (hinv c hc)
    (hcomm a b hab) (hcomm a c hac) (hcomm b c hbc) ⊤ (fun _ _ => Submodule.mem_top)
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
  rw [top_inf_eq, top_inf_eq, top_inf_eq, top_inf_eq, top_inf_eq, top_inf_eq, top_inf_eq,
    finrank_top, Module.finrank_fin_fun] at hsum
  rw [← hprod, ← hprod, ← hprod, ← hprod] at hsum
  have hcons : ∀ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G), g * g = 1 →
      finrank (ZMod p) (fixSpace (coordLin e (α g))) ≤ 2 ∧
        finrank (ZMod p) (fixSpace (coordLin e (α g))) < n ∧
        Even (n - finrank (ZMod p) (fixSpace (coordLin e (α g)))) := by
    intro g hg hg2
    refine ⟨?_, ?_, ?_⟩
    · have h := hfix g hg
      rw [card_fixed_eq_pow e] at h
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h
    · have hlt : fixSpace (coordLin e (α g)) < ⊤ := by
        refine lt_top_iff_ne_top.2 fun htop => hne g hg ?_
        apply coordLin_injective e
        rw [coordLin_one]
        refine LinearMap.ext fun v => ?_
        exact mem_fixSpace.1 (htop ▸ Submodule.mem_top)
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rwa [finrank_top, Module.finrank_fin_fun] at this
    · have h1 := det_eq_neg_one_pow_of_involution (coordLin e (α g)) (hinv g hg2)
      rw [det_coordLin, hdet g hg n e, Units.val_one, Module.finrank_fin_fun] at h1
      exact (neg_one_pow_eq_one_iff_even hm1).1 h1.symm
  have hsq : ∀ g h : G, g * g = 1 → h * h = 1 → g * h = h * g → (g * h) * (g * h) = 1 := by
    intro g h hg hh hgh
    calc g * h * (g * h) = g * (h * g) * h := by group
      _ = g * (g * h) * h := by rw [hgh]
      _ = 1 := by rw [← mul_assoc, hg, one_mul, hh]
  have hab2 := hsq a b ha hb hab
  have hac2 := hsq a c ha hc hac
  have hbc2 := hsq b c hb hc hbc
  have habc : a * b * c = c * (a * b) := by
    rw [mul_assoc, hbc, ← mul_assoc, hac, mul_assoc]
  have habc2 := hsq (a * b) c hab2 hc habc
  have c1 := hcons a (by simp) ha
  have hzero : ∃ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G),
      finrank (ZMod p) (fixSpace (coordLin e (α g))) = 0 := by
    by_contra hnone
    push Not at hnone
    have key : ∀ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G), g * g = 1 →
        (n % 2 = 0 → finrank (ZMod p) (fixSpace (coordLin e (α g))) = 2) ∧
          (n % 2 = 1 → finrank (ZMod p) (fixSpace (coordLin e (α g))) = 1) := by
      intro g hg hg2
      obtain ⟨d, l, ev⟩ := hcons g hg hg2
      have h0 := hnone g hg
      rw [Nat.even_iff] at ev
      exact ⟨fun hn => by omega, fun hn => by omega⟩
    have l1 := c1.2.1
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [(key a (by simp) ha).1 hn, (key b (by simp) hb).1 hn,
        (key (a * b) (by simp) hab2).1 hn, (key c (by simp) hc).1 hn,
        (key (a * c) (by simp) hac2).1 hn, (key (b * c) (by simp) hbc2).1 hn,
        (key (a * b * c) (by simp) habc2).1 hn] at hsum
      rw [(key a (by simp) ha).1 hn] at l1
      omega
    · rw [(key a (by simp) ha).2 hn, (key b (by simp) hb).2 hn,
        (key (a * b) (by simp) hab2).2 hn, (key c (by simp) hc).2 hn,
        (key (a * c) (by simp) hac2).2 hn, (key (b * c) (by simp) hbc2).2 hn,
        (key (a * b * c) (by simp) habc2).2 hn] at hsum
      rw [(key a (by simp) ha).2 hn] at l1
      omega
  obtain ⟨g, hg, hg0⟩ := hzero
  refine ⟨g, hg, (coordLin_eq_neg_iff e (α g)).1 fun v => ?_⟩
  have hg2 : g * g = 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hab2
    · exact hc
    · exact hac2
    · exact hbc2
    · exact habc2
  exact eq_neg_of_fixSpace_eq_bot h2K _ (hinv g hg2) hg0 v

theorem exists_basis_eight {G : Type*} [Group G] {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA8 : Nat.card A = 8) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      ∀ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G), g ∈ A ∧ g ≠ 1 := by
  classical
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA8]; norm_num)
  have : Fintype A := Fintype.ofFinite A
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq, hA2 x hx])
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1} : Finset A)) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hA8]; simp)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1, a} : Finset A)) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hA8]
      exact Finset.card_le_two.trans_lt (by norm_num))
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1, a, b, a * b} : Finset A)) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hA8]
      exact Finset.card_le_four.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc
  obtain ⟨hb1, hba⟩ := hb
  obtain ⟨hc1, hca, hcb, hcab⟩ := hc
  have ne : ∀ x y : A, x ≠ y → (x : G) ≠ y := fun x y h h' => h (Subtype.ext h')
  have hab1 : (a : G) * b ≠ 1 := fun h => hba (Subtype.ext (by
    rw [← hinv a a.2]; exact eq_inv_of_mul_eq_one_right h))
  have hac1 : (a : G) * c ≠ 1 := fun h => hca (Subtype.ext (by
    rw [← hinv a a.2]; exact eq_inv_of_mul_eq_one_right h))
  have hbc1 : (b : G) * c ≠ 1 := fun h => hcb (Subtype.ext (by
    rw [← hinv b b.2]; exact eq_inv_of_mul_eq_one_right h))
  have habc1 : (a : G) * b * c ≠ 1 := fun h => hcab (Subtype.ext (by
    rw [Subgroup.coe_mul, ← hinv _ (mul_mem a.2 b.2)]; exact eq_inv_of_mul_eq_one_right h))
  refine ⟨a, a.2, b, b.2, c, c.2, fun g hg => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨a.2, ne a 1 ha⟩
  · exact ⟨b.2, ne b 1 hb1⟩
  · exact ⟨mul_mem a.2 b.2, hab1⟩
  · exact ⟨c.2, ne c 1 hc1⟩
  · exact ⟨mul_mem a.2 c.2, hac1⟩
  · exact ⟨mul_mem b.2 c.2, hbc1⟩
  · exact ⟨mul_mem (mul_mem a.2 b.2) c.2, habc1⟩

theorem pRank_two_quotient_eq {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) : pRank 2 (G ⧸ N) = pRank 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
  exact pRank_quotient_eq N (fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h))

theorem noncentral_odd_prime_kernel_two_rank_exactly_two {p : ℕ} [hp : Fact p.Prime]
    (hp3 : 3 < p) {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y)
    [P.Normal] (hP : IsPGroup p P) (hP1 : P ≠ ⊥) (hE : layer (Y ⧸ P) = ⊤)
    (hZ : center (Y ⧸ P) = ⊥) (hYP : ⁅(⊤ : Subgroup Y), P⁆ ≠ ⊥) (hloc : localRank p Y ≤ 2) :
    IsSimpleGroup (Y ⧸ P) ∧ (∃ a b : Y ⧸ P, a * b ≠ b * a) ∧ pRank 2 (Y ⧸ P) = 2 ∧
      pRank 2 Y = 2 ∧
      ∃ D : Subgroup P, ∃ _ : D.Characteristic, D ≠ ⊥ ∧ Monoid.exponent D = p ∧
        ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P) ∧
        IsPGroup p (frattiniAction D).ker ∧
        (frattiniConjAction P D).range ≠ ⊥ ∧ Group.IsPerfect (frattiniConjAction P D).range ∧
        (∀ (n : ℕ) (e : D ⧸ frattini D ≃* Multiplicative (Fin n → ZMod p)),
          ∀ r ∈ (frattiniConjAction P D).range,
            Matrix.GeneralLinearGroup.det (elemAutEquivGL e r) = 1) ∧
        (frattiniConjAction P D).ker ≤ P ∧
        P.map (frattiniConjAction P D).rangeRestrict =
          CFSG.pCore p (frattiniConjAction P D).range ∧
        (∃ _ : (P.map (frattiniConjAction P D).rangeRestrict).Normal,
          ∃ e : ((frattiniConjAction P D).range ⧸ P.map (frattiniConjAction P D).rangeRestrict) ≃*
            (Y ⧸ P), ∀ y : Y,
              e (QuotientGroup.mk ((frattiniConjAction P D).rangeRestrict y)) =
                QuotientGroup.mk y) ∧
        pRank 2 (frattiniConjAction P D).range = 2 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have h5 := noncentral_odd_prime_kernel_simple_quotient hp3 P hP hP1 hE hZ hYP hloc
  obtain ⟨D, hDc, hD1, hexp, hDZ, hker, hclass, hR, hRperf, hdet, hfixall, hSs, hSnab, hKP,
    hBO, hψex, hiso, hfaith⟩ := h5
  obtain ⟨ψ, hψs, hψker, hψapp⟩ := hψex
  have hiso' := hiso
  obtain ⟨hBn, e, he⟩ := hiso'
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hge : 2 ≤ pRank 2 (Y ⧸ P) := by
    have hV := exists_four_group_of_isSimpleGroup hSnab
    obtain ⟨V, hVc, hV2, hV4⟩ := hV
    rw [pRank_eq_open_pRank_top]
    exact le_pRank one_lt_two le_top ⟨⟨⟨fun x y => Subtype.ext (hVc _ x.2 _ y.2)⟩⟩, hV2⟩
      (by rw [hV4]; norm_num)
  have hle : pRank 2 (Y ⧸ P) ≤ 2 := by
    by_contra h3
    push Not at h3
    rw [pRank_eq_open_pRank_top] at h3
    have hE₀ := SectionRank.exists_pRank (G := Y ⧸ P) (p := 2) one_lt_two ⊤
    obtain ⟨E₀, -, hE₀e, hcard₀⟩ := hE₀
    have hE8 := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
      (H := ⊥) (L := E₀) (n := 3) (by rw [card_bot]; exact one_dvd _)
      (by rw [hcard₀]; exact pow_dvd_pow 2 h3) bot_le
    obtain ⟨E, hE8, -, hEE₀⟩ := hE8
    have hE2 : IsPGroup 2 E := IsPGroup.of_card hE8
    have hlift := exists_two_subgroup_map_eq (QuotientGroup.mk' P)
      (QuotientGroup.mk'_surjective P) (by rw [QuotientGroup.ker_mk']; exact hPodd) E hE2
    obtain ⟨A, hA2p, hAE, hAinj⟩ := hlift
    have hprops := props_of_injective_map _ hAinj hAE
      (fun x hx y hy => congrArg Subtype.val
        (hE₀e.1.is_comm.comm (⟨x, hEE₀ hx⟩ : E₀) ⟨y, hEE₀ hy⟩))
      (fun x hx => hE₀e.2 x (hEE₀ hx))
    obtain ⟨hAc, hA2, hAcard⟩ := hprops
    have hbasis := exists_basis_eight hA2 (by rw [hAcard, hE8]; norm_num)
    obtain ⟨a, haA, b, hbA, c, hcA, h7⟩ := hbasis
    have hαinj := hfaith A hA2p
    have hord : ∀ g ∈ ({a, b, a * b, c, a * c, b * c, a * b * c} : Set Y), orderOf g = 2 :=
      fun g hg => orderOf_eq_prime (hA2 g (h7 g hg).1) (h7 g hg).2
    have hDp : IsPGroup p D := hP.to_subgroup D
    obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
    have hinvex := exists_inversion_of_elementary_eight hp2 hWcomm hWpow (frattiniConjAction P D)
      (hAc a haA b hbA) (hAc a haA c hcA) (hAc b hbA c hcA)
      (by rw [← sq]; exact hA2 a haA) (by rw [← sq]; exact hA2 b hbA)
      (by rw [← sq]; exact hA2 c hcA)
      (fun g hg h1 => (h7 g hg).2 (by
        have := @hαinj ⟨g, (h7 g hg).1⟩ 1 (by simpa using h1)
        exact congrArg Subtype.val this))
      (fun g hg => (hfixall g (hord g hg)).2)
      (fun g _ n e' => hdet n e' ((frattiniConjAction P D) g) ⟨g, rfl⟩)
    obtain ⟨g, hg, hginv⟩ := hinvex
    have hcen : (frattiniConjAction P D).rangeRestrict g ∈
        center (frattiniConjAction P D).range := by
      rw [mem_center_iff]
      intro r
      apply Subtype.ext
      ext w
      change (r : MulAut _) ((frattiniConjAction P D) g w) =
        (frattiniConjAction P D) g ((r : MulAut _) w)
      rw [hginv, hginv, map_inv]
    have hcenS : ψ ((frattiniConjAction P D).rangeRestrict g) ∈ center (Y ⧸ P) := by
      rw [mem_center_iff]
      intro s
      obtain ⟨r, rfl⟩ := hψs s
      rw [← map_mul, ← map_mul, (mem_center_iff.1 hcen r)]
    rw [hZ, mem_bot, hψapp, QuotientGroup.eq_one_iff] at hcenS
    have hdvd := Subgroup.orderOf_dvd_natCard P hcenS
    rw [hord g hg] at hdvd
    exact (Nat.not_even_iff_odd.mpr hPodd) (even_iff_two_dvd.mpr hdvd)
  have hS2 : pRank 2 (Y ⧸ P) = 2 := le_antisymm hle hge
  refine ⟨hSs, hSnab, hS2, ?_, D, hDc, hD1, hexp, hDZ, hker, hR, hRperf, hdet, hKP, hBO, hiso, ?_⟩
  · rw [← pRank_two_quotient_eq P hPodd, hS2]
  ·
    have : Finite (frattiniConjAction P D).range :=
      Finite.of_surjective _ (frattiniConjAction P D).rangeRestrict_surjective
    have hBodd : Odd (Nat.card (P.map (frattiniConjAction P D).rangeRestrict)) :=
      Odd.of_dvd_nat hPodd (Subgroup.card_map_dvd P _)
    rw [← pRank_two_quotient_eq _ hBodd, pRank_eq_open_pRank_top, pRank_top_eq_of_mulEquiv
      one_lt_two e, ← pRank_eq_open_pRank_top, hS2]

end CFSG.RankThree.OddKernel
