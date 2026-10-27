module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

variable {V : Type} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

private theorem fixed_of_conj_aux (g g₀ : Matrix.GeneralLinearGroup ι F) (x : ι → F)
    (h : ((g * g₀ * g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = x) :
    ((g₀ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec
        (((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x) =
      ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x := by
  have h1 := congrArg (fun y => ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec y) h
  simp only [Units.val_mul, Matrix.mulVec_mulVec] at h1
  have e : ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
      ((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
        ((g₀ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
          ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
      ((g₀ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
        ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) := by
    rw [Units.inv_mul, Matrix.one_mul]
  have e2 : ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
      (((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
        ((g₀ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
          ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)) =
      ((g₀ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *
        ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) := by
    rw [← e]; simp only [Matrix.mul_assoc]
  rw [e2] at h1
  rw [Matrix.mulVec_mulVec]
  exact h1

theorem natural_borel_element_family [Finite F] (Γ : Subgroup (Matrix.GeneralLinearGroup ι F))
    (S₀ : Sylow 2 Γ) (g₀ : Γ) (hg₀ : g₀ ∈ Subgroup.normalizer ((S₀ : Subgroup Γ) : Set Γ))
    (hfix : ∀ m : ι → F,
      ((g₀ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec m = m → m = 0)
    {H : Subgroup (MulAut V)} {Z : Subgroup V} {κ : Type} {U : κ → Subgroup V} {π : Γ →* ↥H}
    (hπ : Function.Surjective π) (hR : ∀ i, (FFModel.nat Γ).RealizesVia H (U i) Z π)
    (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), orderOf b ∣ orderOf g₀ ∧
      ∀ i, ∀ u ∈ U i, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  have : Finite Γ := inferInstance
  obtain ⟨S₁, hS₁⟩ := Sylow.mapSurjective_surjective hπ 2 S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S₀ S₁
  have hg'N : g * g₀ * g⁻¹ ∈ Subgroup.normalizer ((S₁ : Subgroup Γ) : Set Γ) := by
    have h : (g * g₀ * g⁻¹) • S₁ = S₁ := by
      rw [← hg, mul_smul, mul_smul, inv_smul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr hg₀]
    exact Sylow.smul_eq_iff_mem_normalizer.mp h
  have hord : orderOf (g * g₀ * g⁻¹) = orderOf g₀ := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective g₀
    simpa [MulAut.conj_apply] using this
  refine ⟨π (g * g₀ * g⁻¹), ?_, ?_, ?_⟩
  · have h1 := Subgroup.le_normalizer_map π ⟨_, hg'N, rfl⟩
    have h2 : (S : Subgroup ↥H) = (S₁ : Subgroup Γ).map π := by
      rw [← hS₁, Sylow.coe_mapSurjective]
    rw [h2]
    exact h1
  · exact hord ▸ orderOf_map_dvd π _
  · intro i u hu hb
    obtain ⟨-, hZU, -, hUinv, -, -, -, β, -, hβker, hβact⟩ := hR i
    set g' : Γ := g * g₀ * g⁻¹ with hg'
    set u' : ↥(U i) := ⟨u, hu⟩ with hu'
    have hbU : ((π g' : ↥H) : MulAut V) u ∈ U i := hUinv (π g') u hu
    have hβeq : β ⟨((π g' : ↥H) : MulAut V) u, hbU⟩ = β u' := by
      have h1 : β (⟨((π g' : ↥H) : MulAut V) u, hbU⟩ * u'⁻¹) = 1 := by
        rw [hβker]
        exact hb
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u')
    have hm' : (FFModel.nat Γ).act g' m.1 ∈ (FFModel.nat Γ).sec := trivial
    have hact := hβact g' u' m hbU hm' hm.symm
    have hmk : (QuotientGroup.mk ⟨(FFModel.nat Γ).act g' m.1, hm'⟩ :
        ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) =
        QuotientGroup.mk m := hact.symm.trans (hβeq.trans hm.symm)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hmk
    have h1 : natAct Γ g' (m.1 : Multiplicative (ι → F)) = (m.1 : Multiplicative (ι → F)) := by
      have h0 := Subgroup.mem_bot.mp hmk
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h0
      exact inv_mul_eq_one.mp h0
    set x : ι → F := Multiplicative.toAdd (m.1 : Multiplicative (ι → F)) with hx
    have h2 : ((g' : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = x :=
      congrArg Multiplicative.toAdd h1
    have h3 := fixed_of_conj_aux (g : Matrix.GeneralLinearGroup ι F)
      (g₀ : Matrix.GeneralLinearGroup ι F) x h2
    have h4 := hfix _ h3
    have h5 : x = 0 := by
      have e : ((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec
          (((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x) = x := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [← e, h4, Matrix.mulVec_zero]
    have h6 : m = 1 := Subtype.ext (by
      apply Multiplicative.toAdd.injective
      exact h5)
    have h7 : β u' = 1 := by rw [← hm, h6]; rfl
    exact (hβker u').mp h7

theorem natural_borel_element [Finite F] (Γ : Subgroup (Matrix.GeneralLinearGroup ι F))
    (S₀ : Sylow 2 Γ) (g₀ : Γ) (hg₀ : g₀ ∈ Subgroup.normalizer ((S₀ : Subgroup Γ) : Set Γ))
    (hfix : ∀ m : ι → F,
      ((g₀ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec m = m → m = 0)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : Γ →* ↥H}
    (hR : (FFModel.nat Γ).RealizesVia H U Z π) (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), orderOf b ∣ orderOf g₀ ∧
      ∀ u ∈ U, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  obtain ⟨b, hb, ho, h⟩ := natural_borel_element_family Γ S₀ g₀ hg₀ hfix (κ := Unit)
    (U := fun _ => U) hR.1 (fun _ => hR) S
  exact ⟨b, hb, ho, h ()⟩

theorem exists_sylow_normalizer_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (Q : Sylow 2 A) (x : A) (hx : x ∈ Subgroup.normalizer ((Q : Subgroup A) : Set A)) :
    ∃ Q' : Sylow 2 B, e x ∈ Subgroup.normalizer ((Q' : Subgroup B) : Set B) := by
  let Q' : Sylow 2 B :=
    Q.comapOfInjective e.symm.toMonoidHom e.symm.injective
      (by rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)
  refine ⟨Q', ?_⟩
  have hmem : ∀ h : B, h ∈ (Q' : Subgroup B) ↔ e.symm h ∈ (Q : Subgroup A) := fun h => Iff.rfl
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hmem, hmem, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  exact Subgroup.mem_normalizer_iff.mp hx (e.symm h)

section SL2

private noncomputable def diagSL2' (ω : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

private theorem coe_diagSL2' (ω : Fˣ) :
    (diagSL2' ω : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F)] := rfl

private theorem diagSL2'_mem_upperTriangular (ω : Fˣ) :
    diagSL2' ω ∈ LinearFlag.upperTriangular 2 F := by
  rw [LinearFlag.mem_upperTriangular]
  intro i j hji
  rw [coe_diagSL2', Matrix.diagonal_apply_ne _ (ne_of_gt hji)]

private theorem diagSL2'_pow (ω : Fˣ) (r : ℕ) (hω : ω ^ r = 1) : (diagSL2' ω) ^ r = 1 := by
  have h3 : ((ω : F)) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
  have key : ((diagSL2' ω ^ r : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL2', Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp [h3]
    · simp [h3]
  exact Subtype.ext key

theorem natural_sl2_borel_element_family [Finite F] [CharP F 2] (ω : Fˣ) (hω1 : ω ≠ 1) (r : ℕ)
    (hr : ω ^ r = 1) {H : Subgroup (MulAut V)} {Z : Subgroup V} {κ : Type} {U : κ → Subgroup V}
    {π : ↥(StatedSL 2 F) →* ↥H} (hπ : Function.Surjective π)
    (hR : ∀ i, (FFModel.nat (StatedSL 2 F)).RealizesVia H (U i) Z π)
    (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), b ^ r = 1 ∧
      ∀ i, ∀ u ∈ U i, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q0, hQ0⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 2) (by norm_num)
  have hN : diagSL2' ω ∈ Subgroup.normalizer ((Q0 : Subgroup (SpecialLinearGroup (Fin 2) F)) :
      Set (SpecialLinearGroup (Fin 2) F)) := by
    rw [hQ0, LinearFlag.normalizer_unitriangular]
    exact diagSL2'_mem_upperTriangular ω
  obtain ⟨Q1, hQ1⟩ := exists_sylow_normalizer_of_mulEquiv (specialLinearGroupEquivStatedSL 2 F) Q0 _ hN
  set g₀ : ↥(StatedSL 2 F) := specialLinearGroupEquivStatedSL 2 F (diagSL2' ω) with hg₀
  have hfix : ∀ m : Fin 2 → F,
      ((g₀ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec m = m →
        m = 0 := by
    intro m hm
    have hc : ((g₀ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        Matrix.diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F)] := rfl
    rw [hc] at hm
    have h0 := congrFun hm 0
    have h1 := congrFun hm 1
    simp [Matrix.mulVec_diagonal] at h0 h1
    have hω0 : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
    funext i
    fin_cases i
    · by_contra hne
      apply hω0
      have := mul_right_cancel₀ hne (h0.trans (one_mul _).symm)
      simpa using this
    · by_contra hne
      have h2 : ((ω : F))⁻¹ = 1 := mul_right_cancel₀ hne (h1.trans (one_mul _).symm)
      apply hω0
      simpa using h2
  obtain ⟨b, hbN, hbo, hb⟩ := natural_borel_element_family (StatedSL 2 F) Q1 g₀ hQ1 hfix hπ hR S
  refine ⟨b, hbN, ?_, hb⟩
  have hg₀r : g₀ ^ r = 1 := by
    rw [hg₀, ← map_pow, diagSL2'_pow ω r hr, map_one]
  exact orderOf_dvd_iff_pow_eq_one.mp (hbo.trans (orderOf_dvd_of_pow_eq_one hg₀r))

theorem natural_sl2_borel_element [Finite F] [CharP F 2] (ω : Fˣ) (hω1 : ω ≠ 1) (r : ℕ)
    (hr : ω ^ r = 1) {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL 2 F) →* ↥H} (hR : (FFModel.nat (StatedSL 2 F)).RealizesVia H U Z π)
    (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), b ^ r = 1 ∧
      ∀ u ∈ U, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  obtain ⟨b, hb, hbr, h⟩ := natural_sl2_borel_element_family ω hω1 r hr (κ := Unit)
    (U := fun _ => U) hR.1 (fun _ => hR) S
  exact ⟨b, hb, hbr, h ()⟩

end SL2

section Suzuki

open CFSG.LieType.Ree CFSG.Blueprint

theorem exists_sylow_suzuki_normalizer {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) :
    ∃ Q : Sylow 2 (suzukiGroup a K),
      suzukiDElt a K l ∈ Subgroup.normalizer ((Q : Subgroup (suzukiGroup a K)) :
        Set (suzukiGroup a K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUcard : Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 :=
    (suzuki_unipotent_structure hK).2.1
  have hU2 : IsPGroup 2 (suzukiU a K) :=
    IsPGroup.of_card (n := (2 * a + 1) * 2) (by rw [hUcard, ← pow_mul])
  have hidx : (suzukiU a K).index = (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    have h := (suzukiU a K).card_mul_index
    rw [hUcard, suzuki_order hK] at h
    have hpos : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h, mul_assoc]
  have hodd : ¬ 2 ∣ (suzukiU a K).index := by
    rw [hidx]
    intro h
    have h1 : Odd (2 ^ (2 * a + 1) - 1) := by
      have : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
      have h2 : Even (2 ^ (2 * a + 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      obtain ⟨c, hc⟩ := h2
      exact ⟨c - 1, by omega⟩
    have h2 : Odd ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
      have h2 : Even ((2 ^ (2 * a + 1)) ^ 2) :=
        (Nat.even_pow.mpr ⟨(Nat.even_pow.mpr ⟨even_two, by omega⟩), by omega⟩)
      exact h2.add_one
    have := (Nat.odd_mul.mpr ⟨h1, h2⟩)
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  exact ⟨hU2.toSylow hodd, suzukiT_le_normalizer hK (suzukiDElt_mem_suzukiT a K l)⟩

theorem suzuki_torus_exponents_ne_one {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) (hl : l ≠ 1) :
    l ^ (2 ^ a) ≠ 1 ∧ l ^ (2 ^ a + 1) ≠ 1 := by
  have hq : l ^ (2 ^ (2 * a + 1)) = l := by
    have h1 : l ^ Nat.card Kˣ = 1 := pow_card_eq_one'
    rw [Nat.card_units, hK] at h1
    have hpos : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    calc l ^ (2 ^ (2 * a + 1)) = l ^ (2 ^ (2 * a + 1) - 1) * l := by
          rw [← pow_succ]; congr 1; omega
      _ = l := by rw [h1, one_mul]
  constructor
  · intro h
    apply hl
    have : l ^ (2 ^ (2 * a + 1)) = 1 := by
      rw [show 2 ^ (2 * a + 1) = 2 ^ a * 2 ^ (a + 1) by rw [← pow_add]; congr 1; ring, pow_mul, h,
        one_pow]
    rw [hq] at this
    exact this
  · intro h
    apply hl
    have hm : l ^ (2 ^ a) = l⁻¹ := by
      rw [pow_succ] at h
      exact eq_inv_of_mul_eq_one_left h
    have h2 : l ^ (2 ^ (2 * a)) = l := by
      have e : 2 ^ (2 * a) = 2 ^ a * 2 ^ a := by rw [← pow_add]; congr 1; ring
      rw [e, pow_mul, hm, inv_pow, hm, inv_inv]
    have h3 : l ^ (2 ^ (2 * a + 1)) = l ^ 2 := by
      rw [pow_succ, pow_mul, h2]
    rw [hq] at h3
    have h4 : l * l = l * 1 := by
      rw [mul_one, ← pow_two]
      exact h3.symm
    exact mul_left_cancel h4

private noncomputable def suzukiDHom (a : ℕ) (K : Type) [Field K] :
    Kˣ →* suzukiGroup a K where
  toFun := suzukiDElt a K
  map_one' := suzukiDElt_one
  map_mul' := fun l m => (suzukiDElt_mul l m).symm

theorem natural_sz_borel_element_family {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) (hl1 : l ≠ 1) (r : ℕ) (hr : l ^ r = 1)
    {H : Subgroup (MulAut V)} {Z : Subgroup V} {κ : Type} {U : κ → Subgroup V}
    {π : ↥(suzukiGroup a K) →* ↥H} (hπ : Function.Surjective π)
    (hR : ∀ i, (FFModel.nat (suzukiGroup a K)).RealizesVia H (U i) Z π) (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), b ^ r = 1 ∧
      ∀ i, ∀ u ∈ U i, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  obtain ⟨Q, hQ⟩ := exists_sylow_suzuki_normalizer hK l
  obtain ⟨hne1, hne2⟩ := suzuki_torus_exponents_ne_one hK l hl1
  set g₀ : ↥(suzukiGroup a K) := suzukiDElt a K l with hg₀
  have hfix : ∀ m : Fin 4 → K,
      ((g₀ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec m = m →
        m = 0 := by
    intro m hm
    have hc : ((g₀ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.diagonal ![(l : K) * (l : K) ^ 2 ^ a, (l : K) ^ 2 ^ a, ((l : K) ^ 2 ^ a)⁻¹,
          ((l : K) * (l : K) ^ 2 ^ a)⁻¹] := by
      rw [hg₀]
      exact suzukiD_eq a l
    rw [hc] at hm
    have hm1 : (l : K) ^ 2 ^ a ≠ 1 := fun h => hne1 (Units.ext (by simpa using h))
    have hm2 : (l : K) * (l : K) ^ 2 ^ a ≠ 1 := fun h =>
      hne2 (Units.ext (by rw [pow_succ, mul_comm] at *; simpa [pow_succ, mul_comm] using h))
    have h0 := congrFun hm 0
    have h1 := congrFun hm 1
    have h2 := congrFun hm 2
    have h3 := congrFun hm 3
    simp [Matrix.mulVec_diagonal] at h0 h1 h2 h3
    funext i
    fin_cases i
    · by_contra hne
      exact hm2 (mul_right_cancel₀ hne (h0.trans (one_mul _).symm))
    · by_contra hne
      exact hm1 (mul_right_cancel₀ hne (h1.trans (one_mul _).symm))
    · by_contra hne
      apply hm1
      have := mul_right_cancel₀ hne (h2.trans (one_mul _).symm)
      simpa using this
    · by_contra hne
      apply hm2
      have := mul_right_cancel₀ hne (h3.trans (one_mul _).symm)
      rw [← _root_.mul_inv_rev, inv_eq_one] at this
      exact this
  obtain ⟨b, hbN, hbo, hb⟩ := natural_borel_element_family (suzukiGroup a K) Q g₀ hQ hfix hπ hR S
  refine ⟨b, hbN, ?_, hb⟩
  have hg₀r : g₀ ^ r = 1 := by
    have : suzukiDHom a K (l ^ r) = 1 := by rw [hr, map_one]
    rw [map_pow] at this
    exact this
  exact orderOf_dvd_iff_pow_eq_one.mp (hbo.trans (orderOf_dvd_of_pow_eq_one hg₀r))

theorem natural_sz_borel_element {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) (hl1 : l ≠ 1) (r : ℕ) (hr : l ^ r = 1)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(suzukiGroup a K) →* ↥H}
    (hR : (FFModel.nat (suzukiGroup a K)).RealizesVia H U Z π) (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), b ^ r = 1 ∧
      ∀ u ∈ U, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  obtain ⟨b, hb, hbr, h⟩ := natural_sz_borel_element_family hK l hl1 r hr (κ := Unit)
    (U := fun _ => U) hR.1 (fun _ => hR) S
  exact ⟨b, hb, hbr, h ()⟩

end Suzuki

end CFSG.Quasithin
