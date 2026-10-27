module

public import CFSG.RankThree.OddKernel.SectionRep
public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.RankThree.OddKernel.RankTwoActionsVanish

public section

namespace CFSG.RankThree.OddKernel

open Module Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm

universe u

variable {K : Type*} [Field K] {Y : Type*} [Group Y] {W : Type*} [AddCommGroup W] [Module K W]

open _root_.Classical in
@[expose] noncomputable def factorMultiset (α : Y →* (W ≃ₗ[K] W)) (s : RelSeries (factorRel α)) :
    Multiset (ℕ × Bool) :=
  ((List.ofFn fun i : Fin s.length =>
    (finrank K (s i.succ) - finrank K (s (Fin.castSucc i)),
      decide (∃ y, ∃ w ∈ s i.succ, α y w - w ∉ s (Fin.castSucc i)))) : Multiset (ℕ × Bool))

theorem sum_succ_sub_add {L : ℕ} (f : Fin (L + 1) → ℕ) (hf : ∀ i : Fin L, f i.castSucc ≤ f i.succ) :
    ∑ i : Fin L, (f i.succ - f i.castSucc) + f 0 = f (Fin.last L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => f i.castSucc) (fun i => by
      simpa only [Fin.succ_castSucc] using hf i.castSucc)
    simp only [Fin.castSucc_zero] at h
    have hlast := hf (Fin.last L)
    simp only [Fin.succ_last] at hlast
    simp only [Fin.succ_castSucc, Fin.succ_last, Nat.succ_eq_add_one] at hlast h ⊢
    omega

theorem factor_multiset_cases {L n c : ℕ} (N C : Fin L → ℕ) (B : Fin L → Bool)
    (hNC : ∀ i, ∃ e d, N i = e + 3 * d ∧ C i = e + d) (hC : ∀ i, 1 ≤ C i)
    (hB0 : ∀ i, B i = false → N i = 1) (hB1 : ∀ i, B i = true → 3 ≤ N i)
    (hN : ∑ i, N i = n) (hCs : ∑ i, C i = c)
    (hnc : (n, c) = (3, 1) ∨ (n, c) = (4, 2) ∨ (n, c) = (6, 2)) :
    ((List.ofFn fun i => (N i, B i)) : Multiset (ℕ × Bool)) = {(3, true)} ∨
      ((List.ofFn fun i => (N i, B i)) : Multiset (ℕ × Bool)) = {(4, true)} ∨
      ((List.ofFn fun i => (N i, B i)) : Multiset (ℕ × Bool)) = {(3, true), (1, false)} ∨
      ((List.ofFn fun i => (N i, B i)) : Multiset (ℕ × Bool)) = {(6, true)} ∨
      ((List.ofFn fun i => (N i, B i)) : Multiset (ℕ × Bool)) = {(3, true), (3, true)} := by
  set M : Multiset (ℕ × Bool) := ((List.ofFn fun i => (N i, B i)) : Multiset (ℕ × Bool)) with hMdef
  have hLc : L ≤ c := by
    rw [← hCs]
    calc L = ∑ _i : Fin L, 1 := by simp
      _ ≤ ∑ i, C i := Finset.sum_le_sum fun i _ => hC i
  have hc2 : c ≤ 2 := by rcases hnc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hn3 : 3 ≤ n := by rcases hnc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hBN : ∀ i, B i = true ↔ 3 ≤ N i := by
    intro i
    constructor
    · exact hB1 i
    · intro h
      cases hb : B i
      · have := hB0 i hb
        omega
      · rfl
  obtain rfl | rfl | rfl : L = 0 ∨ L = 1 ∨ L = 2 := by omega
  · simp at hN
    omega
  · simp only [Fin.sum_univ_one] at hN hCs
    have hM : M = {(N 0, B 0)} := rfl
    have hB : B 0 = true := (hBN 0).2 (by omega)
    rw [hM, hB, hN]
    rcases hnc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> rw [h.1] <;> simp
  · simp only [Fin.sum_univ_two] at hN hCs
    have hM : M = {(N 0, B 0), (N 1, B 1)} := rfl
    have hC0 := hC 0
    have hC1 := hC 1
    obtain ⟨e0, d0, hN0, hC0'⟩ := hNC 0
    obtain ⟨e1, d1, hN1, hC1'⟩ := hNC 1
    have hc : c = 2 := by omega
    have hN0' : N 0 = 1 ∨ N 0 = 3 := by omega
    have hN1' : N 1 = 1 ∨ N 1 = 3 := by omega
    have hn : n = 4 ∨ n = 6 := by
      rcases hnc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
    rw [hM]
    rcases hN0' with h0 | h0 <;> rcases hN1' with h1 | h1
    · omega
    · have hb0 : B 0 = false := by
        cases hb : B 0
        · rfl
        · have := (hBN 0).1 hb; omega
      have hb1 : B 1 = true := (hBN 1).2 (by omega)
      rw [h0, h1, hb0, hb1]
      right; right; left
      exact Multiset.pair_comm _ _
    · have hb0 : B 0 = true := (hBN 0).2 (by omega)
      have hb1 : B 1 = false := by
        cases hb : B 1
        · rfl
        · have := (hBN 1).1 hb; omega
      rw [h0, h1, hb0, hb1]
      right; right; left
      rfl
    · have hb0 : B 0 = true := (hBN 0).2 (by omega)
      have hb1 : B 1 = true := (hBN 1).2 (by omega)
      rw [h0, h1, hb0, hb1]
      right; right; right; right
      rfl

theorem factor_counts [FiniteDimensional K W] (h2 : (2 : K) ≠ 0) (α : Y →* (W ≃ₗ[K] W)) {a b : Y}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) {U U' : Submodule K W} (hle : U ≤ U')
    (hU : ∀ y, ∀ w ∈ U, α y w ∈ U) (hU' : ∀ y, ∀ w ∈ U', α y w ∈ U') {c : ℕ}
    (hca : finrank K ↥(U' ⊓ fixSpace (α a).toLinearMap) -
      finrank K ↥(U ⊓ fixSpace (α a).toLinearMap) = c)
    (hcb : finrank K ↥(U' ⊓ fixSpace (α b).toLinearMap) -
      finrank K ↥(U ⊓ fixSpace (α b).toLinearMap) = c)
    (hcab : finrank K ↥(U' ⊓ fixSpace (α (a * b)).toLinearMap) -
      finrank K ↥(U ⊓ fixSpace (α (a * b)).toLinearMap) = c) :
    ∃ e d, finrank K U' - finrank K U = e + 3 * d ∧ c = e + d := by
  set σ := (α a).toLinearMap with hσdef
  set τ := (α b).toLinearMap with hτdef
  have hσ : ∀ w, σ (σ w) = w := fun w => by
    simp only [hσdef, LinearEquiv.coe_coe]
    rw [← LinearEquiv.mul_apply, ← map_mul, ha, map_one]
    rfl
  have hτ : ∀ w, τ (τ w) = w := fun w => by
    simp only [hτdef, LinearEquiv.coe_coe]
    rw [← LinearEquiv.mul_apply, ← map_mul, hb, map_one]
    rfl
  have hστ : ∀ w, σ (τ w) = τ (σ w) := fun w => by
    simp only [hσdef, hτdef, LinearEquiv.coe_coe]
    rw [← LinearEquiv.mul_apply, ← map_mul, hab, map_mul, LinearEquiv.mul_apply]
  have hcomp : (α (a * b)).toLinearMap = σ ∘ₗ τ := by
    ext w
    simp only [hσdef, hτdef, LinearEquiv.coe_coe, LinearMap.comp_apply, map_mul,
      LinearEquiv.mul_apply]
  rw [hcomp] at hcab
  have hσU' : ∀ x ∈ U', σ x ∈ U' := fun x hx => hU' a x hx
  have hτU' : ∀ x ∈ U', τ x ∈ U' := fun x hx => hU' b x hx
  have hσU : ∀ x ∈ U, σ x ∈ U := fun x hx => hU a x hx
  have hτU : ∀ x ∈ U, τ x ∈ U := fun x hx => hU b x hx
  obtain ⟨h1', h2', h3', h4'⟩ := finrank_four_group h2 σ τ hσ hτ hστ U' hσU' hτU'
  obtain ⟨h1, h2'', h3, h4⟩ := finrank_four_group h2 σ τ hσ hτ hστ U hσU hτU
  have m1 := Submodule.finrank_mono (inf_le_inf_right (fixSpace σ ⊓ fixSpace τ) hle)
  have m2 := Submodule.finrank_mono (inf_le_inf_right (fixSpace σ ⊓ negSpace τ) hle)
  have m3 := Submodule.finrank_mono (inf_le_inf_right (negSpace σ ⊓ fixSpace τ) hle)
  have m4 := Submodule.finrank_mono (inf_le_inf_right (negSpace σ ⊓ negSpace τ) hle)
  refine ⟨finrank K ↥(U' ⊓ (fixSpace σ ⊓ fixSpace τ)) - finrank K ↥(U ⊓ (fixSpace σ ⊓ fixSpace τ)),
    finrank K ↥(U' ⊓ (fixSpace σ ⊓ negSpace τ)) - finrank K ↥(U ⊓ (fixSpace σ ⊓ negSpace τ)),
    ?_, ?_⟩ <;> omega

@[expose] noncomputable def sectionGL (α : Y →* (W ≃ₗ[K] W)) {U U' : Submodule K W}
    (hU : ∀ y, ∀ w ∈ U, α y w ∈ U) (hU' : ∀ y, ∀ w ∈ U', α y w ∈ U') :
    Y →* ((U' ⧸ U.comap U'.subtype) ≃ₗ[K] (U' ⧸ U.comap U'.subtype)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).toMonoidHom.comp
    (sectionRep α hU hU').asGroupHom

theorem pGroup_trivial_on_factor {p : ℕ} [Fact p.Prime] [Finite Y] {P : Subgroup Y} [P.Normal]
    (hP : IsPGroup p P) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] {α : Y →* (V ≃ₗ[ZMod p] V)} {U U' : Submodule (ZMod p) V}
    (h : IsIrreducibleFactor α U U') : ∀ x ∈ P, ∀ w ∈ U', α x w - w ∈ U := by
  set ρ := sectionRep α h.1 h.2.1 with hρ
  let Z : Submodule (ZMod p) (U' ⧸ U.comap U'.subtype) := ⨅ x : P, fixSpace (ρ x)
  have hmemZ : ∀ v, v ∈ Z ↔ ∀ x : P, ρ x v = v := by
    intro v
    simp only [Z, Submodule.mem_iInf, mem_fixSpace]
  have hZinv : ∀ y, ∀ v ∈ Z, ρ y v ∈ Z := by
    intro y v hv
    rw [hmemZ] at hv ⊢
    intro x
    have hx : y⁻¹ * x * y ∈ P := by
      have := (inferInstance : P.Normal).conj_mem x x.2 y⁻¹
      simpa [mul_assoc] using this
    have hfix := hv ⟨_, hx⟩
    calc ρ x (ρ y v) = ρ (x * y) v := by rw [map_mul]; rfl
      _ = ρ (y * (y⁻¹ * x * y)) v := by group
      _ = ρ y (ρ (y⁻¹ * x * y) v) := by rw [map_mul]; rfl
      _ = ρ y v := by rw [hfix]
  obtain ⟨w₀, hw₀U', hw₀U⟩ := IsConcreteLE.exists_of_lt h.2.2.1
  have : Nontrivial (U' ⧸ U.comap U'.subtype) := by
    refine ⟨⟨Submodule.Quotient.mk ⟨w₀, hw₀U'⟩, 0, fun h0 => hw₀U ?_⟩⟩
    rwa [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨v, hv0, hvfix⟩ := exists_ne_zero_fixed hP (ρ.comp P.subtype)
  have hZ : Z = ⊤ := by
    rcases sectionRep_irreducible h Z hZinv with hbot | htop
    · exact absurd ((hmemZ v).2 hvfix) (by rw [hbot, Submodule.mem_bot]; exact hv0)
    · exact htop
  intro x hx w hw
  have hfix := (hmemZ (Submodule.Quotient.mk ⟨w, hw⟩)).1 (hZ ▸ Submodule.mem_top) ⟨x, hx⟩
  exact (sectionRep_mk_eq_mk_iff α h.1 h.2.1 x ⟨w, hw⟩).1 hfix

@[expose] def linearEquivToMulAut (V : Type*) [AddCommGroup V] [Module K V] :
    (V ≃ₗ[K] V) →* MulAut (Multiplicative V) where
  toFun e := AddEquiv.toMultiplicative e.toAddEquiv
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

theorem factor_action_of_nontrivial {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite Y]
    [Group.IsPerfect Y] {P : Subgroup Y} [P.Normal] (hP : IsPGroup p P) [IsSimpleGroup (Y ⧸ P)]
    (hnab : ∃ a b : Y ⧸ P, a * b ≠ b * a) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] {α : Y →* (V ≃ₗ[ZMod p] V)} {U U' : Submodule (ZMod p) V}
    (h : IsIrreducibleFactor α U U') (hnt : ∃ y, ∃ w ∈ U', α y w - w ∉ U) :
    (∃ ι : Y ⧸ P →* ((U' ⧸ U.comap U'.subtype) ≃ₗ[ZMod p] (U' ⧸ U.comap U'.subtype)),
      (∀ (y : Y) (w w' : U'), (w' : V) = α y w →
        ι y (Submodule.Quotient.mk w) = Submodule.Quotient.mk w') ∧
      Function.Injective ι ∧ ∀ s, LinearMap.det (ι s).toLinearMap = 1) ∧
    3 ≤ finrank (ZMod p) (U' ⧸ U.comap U'.subtype) := by
  set ψ := sectionGL α h.1 h.2.1 with hψ
  have hψmk : ∀ (y : Y) (w : U'), ψ y (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨α y w, h.2.1 y w w.2⟩ := fun y w => rfl
  have htriv := pGroup_trivial_on_factor hP h
  have hψ1 : ∀ y, ψ y = 1 ↔ ∀ w ∈ U', α y w - w ∈ U := by
    intro y
    constructor
    · intro hy w hw
      have := congrArg (fun e : _ ≃ₗ[ZMod p] _ => e (Submodule.Quotient.mk ⟨w, hw⟩)) hy
      simp only [LinearEquiv.coe_one, id_eq] at this
      exact (sectionRep_mk_eq_mk_iff α h.1 h.2.1 y ⟨w, hw⟩).1 this
    · intro hy
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ v
      exact (sectionRep_mk_eq_mk_iff α h.1 h.2.1 y w).2 (hy w w.2)
  have hPk : P ≤ ψ.ker := fun x hx => (MonoidHom.mem_ker).2 ((hψ1 x).2 (htriv x hx))
  obtain ⟨y₀, w₀, hw₀, hne⟩ := hnt
  have hψy₀ : ψ y₀ ≠ 1 := fun h1 => hne ((hψ1 y₀).1 h1 w₀ hw₀)
  refine ⟨⟨QuotientGroup.lift P ψ hPk, ?_, ?_, ?_⟩, ?_⟩
  · intro y w w' hw'
    change ψ y _ = _
    rw [hψmk]
    congr 1
    exact Subtype.ext hw'.symm
  · rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (QuotientGroup.lift P ψ hPk).ker with
      hbot | htop
    · exact hbot
    · exfalso
      apply hψy₀
      have : ((y₀ : Y ⧸ P)) ∈ (QuotientGroup.lift P ψ hPk).ker := htop ▸ mem_top _
      exact this
  · intro s
    have hdet := perfect_hom_eq_one_of_range_comm
      (LinearEquiv.det.comp (QuotientGroup.lift P ψ hPk)) (fun a _ b _ => mul_comm a b)
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) (DFunLike.congr_fun hdet s)
    simpa [LinearEquiv.coe_det] using this
  · by_contra hlt
    push Not at hlt
    set Q := Multiplicative (U' ⧸ U.comap U'.subtype)
    have : Finite (U' ⧸ U.comap U'.subtype) := Module.finite_of_finite (ZMod p)
    have : Finite Q := inferInstanceAs (Finite (U' ⧸ U.comap U'.subtype))
    have hcard : Nat.card Q = p ^ finrank (ZMod p) (U' ⧸ U.comap U'.subtype) := by
      change Nat.card (U' ⧸ U.comap U'.subtype) = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    have hQp : IsPGroup p Q := IsPGroup.of_card hcard
    have hrank : pRank p Q ≤ 2 := by
      rw [pRank_eq_open_pRank_top]
      refine SectionRank.pRank_le hp.out.one_lt fun E _ _ => ?_
      exact (Subgroup.card_le_card_group E).trans
        (hcard ▸ Nat.pow_le_pow_right hp.out.pos (by omega))
    have hE : CFSG.layer (Y ⧸ P) = ⊤ :=
      CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => Y ⧸ P)
        (fun _ => hnab) (MulEquiv.funUnique Unit (Y ⧸ P)).symm
    have hZ : center (Y ⧸ P) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Y ⧸ P)) with hbot | htop
      · exact hbot
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (mem_center_iff.1 (htop ▸ mem_top b) a)
    have hβ := centerless_semisimple_prime_quotient_rank_two_actions_vanish hp.out hp2 P hP hE hZ
      hQp hrank ((linearEquivToMulAut _).comp ψ)
    apply hψy₀
    refine LinearEquiv.ext fun v => ?_
    have := congrArg (fun σ : MulAut Q => σ (Multiplicative.ofAdd v)) (DFunLike.congr_fun hβ y₀)
    exact this

theorem finrank_section [FiniteDimensional K W] {U U' : Submodule K W} (hle : U ≤ U') :
    finrank K (U' ⧸ U.comap U'.subtype) = finrank K U' - finrank K U := by
  have h := Submodule.finrank_quotient_add_finrank (U.comap U'.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h
  omega

theorem exists_commuting_involutions {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite Y]
    {P : Subgroup Y} [P.Normal] (hP : IsPGroup p P) (h2 : 2 ≤ pRank 2 (Y ⧸ P)) :
    ∃ a b : Y, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ orderOf (a * b) = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  rw [pRank_eq_open_pRank_top] at h2
  obtain ⟨E₀, -, hE₀, hcard₀⟩ := SectionRank.exists_pRank (G := Y ⧸ P) (p := 2) one_lt_two ⊤
  obtain ⟨E, hE4, -, hEE₀⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (L := E₀) (n := 2) (by rw [card_bot]; exact one_dvd _)
    (by rw [hcard₀]; exact pow_dvd_pow 2 h2) bot_le
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hE4
  set π := QuotientGroup.mk' P with hπ
  have hker : Odd (Nat.card π.ker) := by rw [hπ, QuotientGroup.ker_mk']; exact hPodd
  obtain ⟨A, -, hAE, hAinj⟩ := exists_two_subgroup_map_eq π (QuotientGroup.mk'_surjective P)
    hker E hE2
  have hA4 : Nat.card A = 4 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hAinj).toEquiv, MonoidHom.range_comp,
      range_subtype, hAE, hE4]
    norm_num
  have hEmem : ∀ x ∈ A, π x ∈ E₀ := fun x hx => hEE₀ (hAE ▸ mem_map_of_mem π hx)
  have hsq : ∀ x ∈ A, x ^ 2 = 1 := by
    intro x hx
    have h1 : π (x ^ 2) = π 1 := by rw [map_pow, map_one, hE₀.2 _ (hEmem x hx)]
    have := @hAinj ⟨x ^ 2, pow_mem hx 2⟩ ⟨1, one_mem _⟩ h1
    exact congrArg Subtype.val this
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h1 : π (x * y) = π (y * x) := by
      rw [map_mul, map_mul]
      have := hE₀.1.is_comm.comm (⟨π x, hEmem x hx⟩ : E₀) ⟨π y, hEmem y hy⟩
      exact congrArg Subtype.val this
    have := @hAinj ⟨x * y, mul_mem hx hy⟩ ⟨y * x, mul_mem hy hx⟩ h1
    exact congrArg Subtype.val this
  have : Fintype A := Fintype.ofFinite A
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.1 (by rw [hA4]; norm_num)
  obtain ⟨a, ha1⟩ := exists_ne (1 : A)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1, a} : Finset A)) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hA4]
      exact Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  obtain ⟨hb1, hba⟩ := hb
  have ha1' : (a : Y) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : Y) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hba' : (b : Y) ≠ a := fun h => hba (Subtype.ext h)
  have ha2 := hsq a a.2
  have hb2 := hsq b b.2
  have hab := hcomm a a.2 b b.2
  refine ⟨a, b, orderOf_eq_prime ha2 ha1', orderOf_eq_prime hb2 hb1', hab, orderOf_eq_prime ?_ ?_⟩
  · rw [(show Commute (a : Y) b from hab).mul_pow, ha2, hb2, one_mul]
  · intro h1
    apply hba'
    have hainv : (a : Y)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha2])
    calc (b : Y) = (a : Y)⁻¹ * (a * b) := by group
      _ = a := by rw [h1, mul_one, hainv]

theorem factor_counts_of_conj [FiniteDimensional K W] (h2 : (2 : K) ≠ 0) (α : Y →* (W ≃ₗ[K] W))
    (hconjY : ∀ t t' : Y, orderOf t = 2 → orderOf t' = 2 → IsConj t t') {a b : Y}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a) (hab2 : orderOf (a * b) = 2)
    {U U' : Submodule K W} (h : IsIrreducibleFactor α U U') :
    (∀ t : Y, orderOf t = 2 →
      finrank K ↥(U' ⊓ fixSpace (α t).toLinearMap) - finrank K ↥(U ⊓ fixSpace (α t).toLinearMap) =
        finrank K ↥(U' ⊓ fixSpace (α a).toLinearMap) -
          finrank K ↥(U ⊓ fixSpace (α a).toLinearMap)) ∧
    (∃ e d, finrank K U' - finrank K U = e + 3 * d ∧
      finrank K ↥(U' ⊓ fixSpace (α a).toLinearMap) -
        finrank K ↥(U ⊓ fixSpace (α a).toLinearMap) = e + d) ∧
    1 ≤ finrank K ↥(U' ⊓ fixSpace (α a).toLinearMap) -
      finrank K ↥(U ⊓ fixSpace (α a).toLinearMap) := by
  obtain ⟨hU, hU', hlt, -⟩ := h
  have hconjdim : ∀ t : Y, orderOf t = 2 →
      finrank K ↥(U' ⊓ fixSpace (α t).toLinearMap) - finrank K ↥(U ⊓ fixSpace (α t).toLinearMap) =
        finrank K ↥(U' ⊓ fixSpace (α a).toLinearMap) -
          finrank K ↥(U ⊓ fixSpace (α a).toLinearMap) := by
    intro t ht
    obtain ⟨g, rfl⟩ := isConj_iff.1 (hconjY a t ha ht)
    rw [finrank_inf_fixSpace_conj α hU' g a, finrank_inf_fixSpace_conj α hU g a]
  have ha2 : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  obtain ⟨e, d, hn, hc⟩ := factor_counts h2 α ha2 hb2 hab hlt.le hU hU' rfl
    (hconjdim b hb) (hconjdim (a * b) hab2)
  refine ⟨hconjdim, ⟨e, d, hn, hc⟩, ?_⟩
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem noncentral_critical_composition_factor_alternatives {p : ℕ} [hp : Fact p.Prime]
    (hp3 : 3 < p) [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal] (hP : IsPGroup p P)
    [IsSimpleGroup (Y ⧸ P)] (hnab : ∃ a b : Y ⧸ P, a * b ≠ b * a) (h2 : pRank 2 (Y ⧸ P) = 2)
    {V : Type u} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (α : Y →* (V ≃ₗ[ZMod p] V)) (_hker : α.ker ≤ P)
    (hconj : ∀ s s' : Y ⧸ P, orderOf s = 2 → orderOf s' = 2 → IsConj s s')
    (hpair : ∃ n c : ℕ, ((n, c) = (3, 1) ∨ (n, c) = (4, 2) ∨ (n, c) = (6, 2)) ∧
      finrank (ZMod p) V = n ∧
        ∀ t : Y, orderOf t = 2 → finrank (ZMod p) (fixSpace (α t).toLinearMap) = c) :
    (∀ U U', IsIrreducibleFactor α U U' → ∀ x ∈ P, ∀ w ∈ U', α x w - w ∈ U) ∧
    (∀ U U', IsIrreducibleFactor α U U' → (∃ y, ∃ w ∈ U', α y w - w ∉ U) →
      ∃ ι : Y ⧸ P →* ((U' ⧸ U.comap U'.subtype) ≃ₗ[ZMod p] (U' ⧸ U.comap U'.subtype)),
        (∀ (y : Y) (w w' : U'), (w' : V) = α y w →
          ι y (Submodule.Quotient.mk w) = Submodule.Quotient.mk w') ∧
        Function.Injective ι ∧ ∀ s, LinearMap.det (ι s).toLinearMap = 1) ∧
    (∀ s : RelSeries (factorRel α), s.head = ⊥ → s.last = ⊤ →
      factorMultiset α s = {(3, true)} ∨ factorMultiset α s = {(4, true)} ∨
        factorMultiset α s = {(3, true), (1, false)} ∨ factorMultiset α s = {(6, true)} ∨
        factorMultiset α s = {(3, true), (3, true)}) ∧
    ((∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod p) X), finrank (ZMod p) X = 3 ∧
        ∃ ι : Y ⧸ P →* (X ≃ₗ[ZMod p] X), Function.Injective ι ∧
          ∀ Z : Submodule (ZMod p) X, (∀ s, ∀ v ∈ Z, ι s v ∈ Z) → Z = ⊥ ∨ Z = ⊤) ∨
      ((∀ U U', IsIrreducibleFactor α U U' → ∃ y, ∃ w ∈ U', α y w - w ∉ U) ∧
        ∀ t : Y, orderOf t = 2 → finrank (ZMod p) (fixSpace (α t).toLinearMap) = 2)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have h2K : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  obtain ⟨n, c, hnc, hn, hc⟩ := hpair
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  have hconjY : ∀ t t' : Y, orderOf t = 2 → orderOf t' = 2 → IsConj t t' :=
    fun t t' ht ht' => isConj_of_isConj_quotient P hPodd hconj ht ht'
  obtain ⟨a, b, ha, hb, hab, hab2⟩ := exists_commuting_involutions hp2 hP h2.ge
  have hcount := fun {U U'} (h : IsIrreducibleFactor α U U') =>
    factor_counts_of_conj h2K α hconjY ha hb hab hab2 h
  have part3 : ∀ s : RelSeries (factorRel α), s.head = ⊥ → s.last = ⊤ →
      factorMultiset α s = {(3, true)} ∨ factorMultiset α s = {(4, true)} ∨
        factorMultiset α s = {(3, true), (1, false)} ∨ factorMultiset α s = {(6, true)} ∨
        factorMultiset α s = {(3, true), (3, true)} := by
    intro s hs0 hsl
    have hstep : ∀ i : Fin s.length, IsIrreducibleFactor α (s (Fin.castSucc i)) (s i.succ) :=
      fun i => s.step i
    have hNsum := sum_succ_sub_add (fun k => finrank (ZMod p) (s k))
      (fun i => Submodule.finrank_mono (hstep i).2.2.1.le)
    have hCsum := sum_succ_sub_add (fun k => finrank (ZMod p) ↥(s k ⊓ fixSpace (α a).toLinearMap))
      (fun i => Submodule.finrank_mono (inf_le_inf_right _ (hstep i).2.2.1.le))
    have h0 : s 0 = ⊥ := hs0
    have hl : s (Fin.last s.length) = ⊤ := hsl
    rw [h0, hl, finrank_bot, finrank_top, add_zero] at hNsum
    rw [h0, hl, bot_inf_eq, top_inf_eq, finrank_bot, add_zero] at hCsum
    exact factor_multiset_cases _ _ _ (fun i => (hcount (hstep i)).2.1)
      (fun i => (hcount (hstep i)).2.2)
      (fun i hi => by
        have := finrank_eq_of_trivial_factor (hstep i) (by simpa using hi)
        omega)
      (fun i hi => by
        have hnt : ∃ y, ∃ w ∈ s i.succ, α y w - w ∉ s (Fin.castSucc i) := by simpa using hi
        have := (factor_action_of_nontrivial hp2 hP hnab (hstep i) hnt).2
        rwa [finrank_section (hstep i).2.2.1.le] at this)
      (hNsum.trans hn) (hCsum.trans (hc a ha)) hnc
  refine ⟨fun U U' h => pGroup_trivial_on_factor hP h,
    fun U U' h hnt => (factor_action_of_nontrivial hp2 hP hnab h hnt).1, part3, ?_⟩
  obtain ⟨s, hs0, hsl⟩ := exists_relSeries_factorRel α ⊤ fun y w _ => Submodule.mem_top
  have hstep : ∀ i : Fin s.length, IsIrreducibleFactor α (s (Fin.castSucc i)) (s i.succ) :=
    fun i => s.step i
  have hM := part3 s hs0 hsl
  set f : Fin s.length → ℕ × Bool := fun i =>
    (finrank (ZMod p) (s i.succ) - finrank (ZMod p) (s (Fin.castSucc i)),
      decide (∃ y, ∃ w ∈ s i.succ, α y w - w ∉ s (Fin.castSucc i))) with hf
  have hMf : factorMultiset α s = ((List.ofFn f : List (ℕ × Bool)) : Multiset (ℕ × Bool)) := rfl
  have hmem : ∀ x, x ∈ factorMultiset α s ↔ ∃ i, f i = x := by
    intro x
    rw [hMf, Multiset.mem_coe, List.mem_ofFn]
  by_cases h3 : (3, true) ∈ factorMultiset α s
  · left
    obtain ⟨i, hi⟩ := (hmem _).1 h3
    have hfi : finrank (ZMod p) (s i.succ) - finrank (ZMod p) (s (Fin.castSucc i)) = 3 :=
      congrArg Prod.fst hi
    have hbi := congrArg Prod.snd hi
    have hnt : ∃ y, ∃ w ∈ s i.succ, α y w - w ∉ s (Fin.castSucc i) := by
      simpa [hf] using hbi
    obtain ⟨⟨ι, hιmk, hιinj, -⟩, -⟩ := factor_action_of_nontrivial hp2 hP hnab (hstep i) hnt
    refine ⟨_, inferInstance, inferInstance, ?_, ι, hιinj, ?_⟩
    · rw [finrank_section (hstep i).2.2.1.le]
      exact hfi
    · intro Z hZ
      refine sectionRep_irreducible (hstep i) Z fun y v hv => ?_
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ v
      have := hιmk y w ⟨α y w, (hstep i).2.1 y w w.2⟩ rfl
      rw [Submodule.mkQ_apply, sectionRep_mk, ← this]
      exact hZ _ _ hv
  · right
    have hM' : factorMultiset α s = {(4, true)} ∨ factorMultiset α s = {(6, true)} := by
      rcases hM with h | h | h | h | h
      · exact absurd (by rw [h]; simp) h3
      · exact Or.inl h
      · exact absurd (by rw [h]; simp) h3
      · exact Or.inr h
      · exact absurd (by rw [h]; simp) h3
    have hlen : s.length = 1 := by
      have hcard := congrArg Multiset.card hMf
      rw [Multiset.coe_card, List.length_ofFn] at hcard
      rcases hM' with h | h <;> rw [h, Multiset.card_singleton] at hcard <;> exact hcard.symm
    set i0 : Fin s.length := ⟨0, by omega⟩ with hi0
    have hi0c : s (Fin.castSucc i0) = ⊥ := hs0
    have hi0s : s i0.succ = ⊤ := by
      rw [← hsl]
      exact congrArg s (Fin.ext (by simp [hi0, hlen]))
    have hfac : IsIrreducibleFactor α ⊥ ⊤ := by
      rw [← hi0c, ← hi0s]
      exact hstep i0
    have hfi0 : f i0 = (4, true) ∨ f i0 = (6, true) := by
      have hin := (hmem (f i0)).2 ⟨i0, rfl⟩
      rcases hM' with h | h
      · rw [h, Multiset.mem_singleton] at hin
        exact Or.inl hin
      · rw [h, Multiset.mem_singleton] at hin
        exact Or.inr hin
    have hb0 : (f i0).2 = true := by rcases hfi0 with h | h <;> rw [h]
    have hnt0 : ∃ y, ∃ w ∈ (⊤ : Submodule (ZMod p) V), α y w - w ∉ (⊥ : Submodule (ZMod p) V) := by
      have : ∃ y, ∃ w ∈ s i0.succ, α y w - w ∉ s (Fin.castSucc i0) := by simpa [hf] using hb0
      rwa [hi0c, hi0s] at this
    have hn0 : (f i0).1 = n := by
      change finrank (ZMod p) (s i0.succ) - finrank (ZMod p) (s (Fin.castSucc i0)) = n
      rw [hi0c, hi0s, finrank_top, finrank_bot, hn, Nat.sub_zero]
    have hc2 : c = 2 := by
      rcases hfi0 with h | h <;> rw [h] at hn0 <;>
        rcases hnc with h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;> omega
    refine ⟨fun U U' h => ?_, fun t ht => by rw [hc t ht, hc2]⟩
    rcases hfac.2.2.2 U h.1 bot_le le_top with hU | hU <;>
      rcases hfac.2.2.2 U' h.2.1 bot_le le_top with hU' | hU'
    · exact absurd (hU ▸ hU' ▸ h.2.2.1) (lt_irrefl _)
    · rw [hU, hU']
      exact hnt0
    · exact absurd (hU ▸ hU' ▸ h.2.2.1) (not_lt_of_ge bot_le)
    · exact absurd (hU ▸ hU' ▸ h.2.2.1) (lt_irrefl _)

end CFSG.RankThree.OddKernel
