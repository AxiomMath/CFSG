module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43Steps
public import CFSG.Quasithin.Vol2.Ch4Sec3L4312Lev

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat Vol2.Ch11.SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uMat uSL coe_uSL)
open scoped MatrixGroups Matrix Pointwise

namespace SL3Pt

variable {F : Type} [Field F]

theorem uMat_mulVec (a b : F) (v : Fin 3 → F) :
    uMat a b 0 *ᵥ v = ![v 0 + a * v 1 + b * v 2, v 1, v 2] := by
  funext i
  fin_cases i <;> simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem blk_mulVec (g : Matrix (Fin 2) (Fin 2) F) (v : Fin 3 → F) :
    blk g *ᵥ v = ![v 0, g 0 0 * v 1 + g 0 1 * v 2, g 1 0 * v 1 + g 1 1 * v 2] := by
  funext i
  fin_cases i <;> simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mem_radE0 {s : ↥(StatedSL 3 F)} :
    s ∈ radE0 F ↔ ∃ a b : F, ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat a b 0 := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨a, b, rfl⟩ := mem_rad1_iff_uSL.mp hB
    exact ⟨a, b, by rw [MulEquiv.coe_toMonoidHom, specialLinearGroupEquivStatedSL_coe]; rfl⟩
  · rintro ⟨a, b, h⟩
    refine ⟨uSL a b 0, mem_rad1_iff_uSL.mpr ⟨a, b, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [MulEquiv.coe_toMonoidHom, specialLinearGroupEquivStatedSL_coe, coe_uSL, h]

theorem radE0_le_stE0 : radE0 F ≤ stE0 F := by
  rintro _ ⟨B, hB, rfl⟩
  exact ⟨B, (mem_rad1.mp hB).1, rfl⟩

theorem sq_eq_one_of_mem_radE0 [CharP F 2] {s : ↥(StatedSL 3 F)} (hs : s ∈ radE0 F) :
    s ^ 2 = 1 := by
  obtain ⟨B, hB, rfl⟩ := hs
  rw [← map_pow, sq_eq_one_of_mem_rad1 hB, map_one]

theorem stabE0_le_normalizer_rad1 :
    stabE0 F ≤ Subgroup.normalizer (rad1 F : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  have key : ∀ g ∈ stabE0 F, ∀ h ∈ rad1 F, g * h * g⁻¹ ∈ rad1 F := by
    intro g hg h hh
    obtain ⟨k, hk, rfl⟩ := hh
    refine ⟨⟨g, hg⟩ * k * (⟨g, hg⟩ : ↥(stabE0 F))⁻¹, ?_, rfl⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hk, mul_one, mul_inv_cancel]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun h' => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h'
  simpa [mul_assoc] using this

theorem stE0_le_normalizer_radE0 :
    stE0 F ≤ Subgroup.normalizer (radE0 F : Set ↥(StatedSL 3 F)) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ (rad1 F).map _ ↔ _ ∈ (rad1 F).map _
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom, map_mul, map_mul,
    map_inv, MulEquiv.symm_apply_apply]
  exact Subgroup.mem_normalizer_iff.mp (stabE0_le_normalizer_rad1 hg) _

theorem le_radE0_of_isPGroup [Finite F] [CharP F 2] {N : Subgroup ↥(StatedSL 3 F)}
    (hN : N ≤ stE0 F) (hn : stE0 F ≤ Subgroup.normalizer (N : Set ↥(StatedSL 3 F)))
    (h2 : IsPGroup 2 N) : N ≤ radE0 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := specialLinearGroupEquivStatedSL 3 F with he
  set N' := N.map e.symm.toMonoidHom with hN'
  have hN'le : N' ≤ stabE0 F := by
    rintro _ ⟨n, hn', rfl⟩
    obtain ⟨g, hg, hge⟩ := hN hn'
    rw [MulEquiv.coe_toMonoidHom, ← hge, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hg
  have hnorm : stabE0 F ≤ Subgroup.normalizer (N' : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    intro g hg
    have hge : e g ∈ Subgroup.normalizer (N : Set ↥(StatedSL 3 F)) := hn ⟨g, hg, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hge ⊢
    intro x
    rw [hN', Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_mul, map_mul,
      map_inv]
    exact hge (e x)
  have h2' : IsPGroup 2 N' := h2.map _
  have hle := le_pCoreOf_of_le_normalizer 2 hN'le hnorm h2'
  rw [pCoreOf_stabE0] at hle
  intro x hx
  exact ⟨e.symm x, hle ⟨x, hx, rfl⟩, MulEquiv.apply_symm_apply e x⟩

theorem semilinear_decomp {fe : (Fin 3 → F) ≃+ (Fin 3 → F)} {σ : F ≃+* F}
    (hσ : ∀ (c : F) (n : Fin 3 → F), fe (c • n) = σ c • fe n) (x : Fin 3 → F) :
    fe x = σ (x 0) • fe ![1, 0, 0] + σ (x 1) • fe ![0, 1, 0] + σ (x 2) • fe ![0, 0, 1] := by
  have hx : x = x 0 • ![(1 : F), 0, 0] + x 1 • ![0, 1, 0] + x 2 • ![0, 0, 1] := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_add, hσ, hσ, hσ]

theorem exists_uMat_of_semilinear [CharP F 2] {fe : (Fin 3 → F) ≃+ (Fin 3 → F)} {σ : F ≃+* F}
    (hσ : ∀ (c : F) (n : Fin 3 → F), fe (c • n) = σ c • fe n)
    (hrad : ∀ a b : F, ∃ a' b' : F, ∀ x, fe (uMat a' b' 0 *ᵥ x) = uMat a b 0 *ᵥ fe x)
    (hlev : ∀ g : SL(2, F), ∃ a b : F, ∀ x,
      fe (blk (g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) = uMat a b 0 *ᵥ (blk g *ᵥ fe x))
    {k : ℕ} (hord : ∀ x, (⇑fe)^[2 ^ k] x = x) :
    ∃ a b : F, ∀ x, fe x = uMat a b 0 *ᵥ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f0, hf0⟩ : ∃ v, fe ![1, 0, 0] = v := ⟨_, rfl⟩
  obtain ⟨f1, hf1⟩ : ∃ v, fe ![0, 1, 0] = v := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ v, fe ![0, 0, 1] = v := ⟨_, rfl⟩
  have hdec : ∀ x : Fin 3 → F, fe x = σ (x 0) • f0 + σ (x 1) • f1 + σ (x 2) • f2 := by
    intro x
    rw [semilinear_decomp hσ x, hf0, hf1, hf2]
  have he0 : ∀ a' b' : F, uMat a' b' 0 *ᵥ ![(1 : F), 0, 0] = ![1, 0, 0] := by
    intro a' b'
    rw [uMat_mulVec]
    simp
  have hf01 : f0 1 = 0 := by
    obtain ⟨a', b', h⟩ := hrad 1 0
    have h0 := congrFun (h ![1, 0, 0]) 0
    rw [he0, hf0, uMat_mulVec] at h0
    simp only [Matrix.cons_val_zero, one_mul, zero_mul, add_zero] at h0
    linear_combination -h0
  have hf02 : f0 2 = 0 := by
    obtain ⟨a', b', h⟩ := hrad 0 1
    have h0 := congrFun (h ![1, 0, 0]) 0
    rw [he0, hf0, uMat_mulVec] at h0
    simp only [Matrix.cons_val_zero, one_mul, zero_mul, add_zero] at h0
    linear_combination -h0
  have h011 : fe ![0, 1, 1] = f1 + f2 := by
    rw [hdec]
    simp
  have hE12 : f2 2 = f1 1 ∧ f1 2 = 0 := by
    let g : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    obtain ⟨a, b, h⟩ := hlev g
    have hx : blk (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, 0, 1] = ![0, 1, 1] := by
      rw [blk_mulVec]
      simp [g]
    have h1 := h ![0, 0, 1]
    rw [hx, h011, hf2, blk_mulVec, uMat_mulVec] at h1
    have c1 := congrFun h1 1
    have c2 := congrFun h1 2
    simp [g] at c1 c2
    constructor
    · linear_combination -c1
    · linear_combination c2
  have hE21 : f2 1 = 0 := by
    let g : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    obtain ⟨a, b, h⟩ := hlev g
    have hx : blk (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, 1, 0] = ![0, 1, 1] := by
      rw [blk_mulVec]
      simp [g]
    have h1 := h ![0, 1, 0]
    rw [hx, h011, hf1, blk_mulVec, uMat_mulVec] at h1
    have c1 := congrFun h1 1
    simp [g] at c1
    linear_combination c1
  obtain ⟨β, hβ⟩ : ∃ b, f1 1 = b := ⟨_, rfl⟩
  have hf22 : f2 2 = β := hE12.1.trans hβ
  have hc1' : ∀ x : Fin 3 → F, (fe x) 1 = σ (x 1) * β := by
    intro x
    rw [hdec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf01, hβ, hE21]
    ring
  have hβ0 : β ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := fe.surjective ![0, 1, 0]
    have := hc1' x
    rw [hx, h0, mul_zero] at this
    simp at this
  have hσid : ∀ t : F, σ t = t := by
    intro t
    let g : SL(2, F) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    obtain ⟨a, b, h⟩ := hlev g
    have hx : blk (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, 0, 1] = ![0, t, 1] := by
      rw [blk_mulVec]
      simp [g]
    have h1 := h ![0, 0, 1]
    rw [hx, hf2, blk_mulVec, uMat_mulVec] at h1
    have c1 := congrFun h1 1
    rw [hc1'] at c1
    simp [g, hE21, hf22] at c1
    exact c1.resolve_right hβ0
  have hc1 : ∀ x : Fin 3 → F, (fe x) 1 = β * x 1 := by
    intro x
    rw [hc1', hσid, mul_comm]
  have hc2 : ∀ x : Fin 3 → F, (fe x) 2 = β * x 2 := by
    intro x
    rw [hdec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hσid, hf02, hE12.2, hf22]
    ring
  have hc0 : ∀ x : Fin 3 → F, (fe x) 0 = f0 0 * x 0 + f1 0 * x 1 + f2 0 * x 2 := by
    intro x
    rw [hdec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hσid]
    ring
  have hit1 : ∀ (j : ℕ) (x : Fin 3 → F), ((⇑fe)^[j] x) 1 = β ^ j * x 1 := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', hc1, ih, pow_succ]
      ring
  have hfe0 : ∀ c : F, fe ![c, 0, 0] = ![f0 0 * c, 0, 0] := by
    intro c
    funext i
    fin_cases i
    · simp [hc0]
    · simp [hc1]
    · simp [hc2]
  have hit0 : ∀ j : ℕ, (⇑fe)^[j] ![1, 0, 0] = ![f0 0 ^ j, 0, 0] := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hfe0, pow_succ]
      congr 1
      ring
  have hone : ∀ c : F, c ^ 2 ^ k = 1 → c = 1 := by
    intro c hc
    have h := sub_pow_char_pow (p := 2) c 1 k
    rw [hc, one_pow, sub_self] at h
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h)
  have hβ1 : β = 1 := by
    apply hone
    have := hit1 (2 ^ k) ![0, 1, 0]
    rw [hord] at this
    simpa using this.symm
  have hc01 : f0 0 = 1 := by
    apply hone
    have := congrFun (hit0 (2 ^ k)) 0
    rw [hord] at this
    simpa using this.symm
  refine ⟨f1 0, f2 0, fun x => ?_⟩
  have e0 : (fe x) 0 = x 0 + f1 0 * x 1 + f2 0 * x 2 := by rw [hc0, hc01, one_mul]
  have e1 : (fe x) 1 = x 1 := by rw [hc1, hβ1, one_mul]
  have e2 : (fe x) 2 = x 2 := by rw [hc2, hβ1, one_mul]
  rw [uMat_mulVec]
  funext i
  fin_cases i <;> simp [e0, e1, e2]

end SL3Pt

variable {G : Type} [Group G]

namespace L4314

variable {F : Type} [Field F]

theorem exists_conj_coord {U : Subgroup G} {β : ↥U →* Multiplicative (Fin 3 → F)}
    (hβ : Function.Bijective β) {p : G} (hp : p ∈ Subgroup.normalizer (U : Set G)) :
    ∃ fe : (Fin 3 → F) ≃+ (Fin 3 → F), ∀ u v : ↥U, (v : G) = p * u * p⁻¹ →
      fe (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β v) := by
  set e : ↥U ≃* Multiplicative (Fin 3 → F) := MulEquiv.ofBijective β hβ with he
  set c : ↥U ≃* ↥U := U.normalizerMonoidHom ⟨p, hp⟩ with hc
  refine ⟨AddEquiv.toMultiplicative.symm (e.symm.trans (c.trans e)), fun u v huv => ?_⟩
  have hcu : c u = v := Subtype.ext (by
    rw [hc, U.normalizerMonoidHom_apply_apply_coe]
    exact huv.symm)
  have h1 : e.symm (β u) = u := e.symm_apply_apply u
  show Multiplicative.toAdd (e (c (e.symm (β u)))) = Multiplicative.toAdd (β v)
  rw [h1, hcu]
  rfl

theorem iterate_conj_coord {U : Subgroup G} {β : ↥U →* Multiplicative (Fin 3 → F)} {p : G}
    (hp : p ∈ Subgroup.normalizer (U : Set G)) {fe : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (hfe : ∀ u v : ↥U, (v : G) = p * u * p⁻¹ →
      fe (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β v)) (j : ℕ) :
    ∀ u v : ↥U, (v : G) = p ^ j * u * (p ^ j)⁻¹ →
      (⇑fe)^[j] (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β v) := by
  induction j with
  | zero =>
    intro u v huv
    have : v = u := Subtype.ext (by simpa using huv)
    rw [this]
    rfl
  | succ j ih =>
    intro u v huv
    have hpj : p ^ j ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ hp j
    let w : ↥U := ⟨p ^ j * u * (p ^ j)⁻¹, (Subgroup.mem_normalizer_iff.mp hpj u).mp u.2⟩
    rw [Function.iterate_succ_apply', ih u w rfl]
    apply hfe
    rw [huv, pow_succ']
    show p * p ^ j * u * (p * p ^ j)⁻¹ = p * (p ^ j * u * (p ^ j)⁻¹) * p⁻¹
    group

theorem relPair_conj_coord {K U : Subgroup G} {α : ↥K →* ↥(StatedSL 3 F)}
    {β : ↥U →* Multiplicative (Fin 3 → F)} (hβ : Function.Bijective β)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hβa : ∀ (k : ↥K) (u v : ↥U), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    {p : G} (hpU : p ∈ Subgroup.normalizer (U : Set G)) {fe : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (hfe : ∀ u v : ↥U, (v : G) = p * u * p⁻¹ →
      fe (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β v))
    (k k' : ↥K) (hkk' : (k' : G) = p * k * p⁻¹) : FFC.SumNat.RelPair fe (α k) (α k') := by
  intro x
  obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd x)
  have hx : x = Multiplicative.toAdd (β u) := by rw [hu]; rfl
  let w : ↥U := ⟨k * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩
  let u' : ↥U := ⟨p * u * p⁻¹, (Subgroup.mem_normalizer_iff.mp hpU u).mp u.2⟩
  let w' : ↥U := ⟨p * w * p⁻¹, (Subgroup.mem_normalizer_iff.mp hpU w).mp w.2⟩
  have hw := hβa k u w rfl
  have hw' := hβa k' u' w' (by
    show p * (k * u * (k : G)⁻¹) * p⁻¹ = k' * (p * u * p⁻¹) * (k' : G)⁻¹
    rw [hkk']
    group)
  rw [hx, ← hw, hfe w w' rfl, hw', ← hfe u u' rfl]

end L4314

variable [Finite G]

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}

omit [Finite G] [Fintype F] in
theorem mem_P₀ {x : G} :
    x ∈ ((radE0 F).comap α).map K.subtype ↔ ∃ hx : x ∈ K, α ⟨x, hx⟩ ∈ radE0 F := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem α_eq_one_of_centralizes {k : ↥K} (hk : ∀ u : ↥(u4311 I K), (k : G) * u * (k : G)⁻¹ = u) :
    α k = 1 := by
  have hfix : ∀ x : Fin 3 → F,
      ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
    intro x
    obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd x)
    have h := s.β_act k u u (hk u).symm
    rw [hu] at h
    exact h.symm
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrFun (hfix (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h
  simp only [Matrix.col_apply, Pi.single_apply] at h
  rw [h]
  simp [Matrix.one_apply]

theorem mem_pCoreOf_of_centralizes {k : G} (hkK : k ∈ K)
    (hk : ∀ u : ↥(u4311 I K), k * u * k⁻¹ = u) : k ∈ pCoreOf 2 K := by
  have h1 := s.α_eq_one_of_centralizes (k := ⟨k, hkK⟩) hk
  have h2 : (⟨k, hkK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← s.modO2.2]
    exact h1
  exact (mem_pCoreOf_iff' _).mpr h2

theorem pCoreOf_K_le_P₀ : pCoreOf 2 K ≤ ((radE0 F).comap α).map K.subtype := by
  intro x hx
  have hxK : x ∈ K := pCoreOf_le 2 K hx
  refine mem_P₀.mpr ⟨hxK, ?_⟩
  have h1 : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (mem_pCoreOf_iff' ⟨x, hxK⟩).mp hx
  rw [← s.modO2.2] at h1
  rw [MonoidHom.mem_ker.mp h1]
  exact (radE0 F).one_mem

theorem isPGroup_P₀ : IsPGroup 2 ↥(((radE0 F).comap α).map K.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  intro x
  obtain ⟨hxK, hx⟩ := mem_P₀.mp x.2
  have hsq : α (⟨x, hxK⟩ ^ 2) = 1 := by
    rw [map_pow]
    exact SL3Pt.sq_eq_one_of_mem_radE0 hx
  have hker : (⟨x, hxK⟩ ^ 2 : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← s.modO2.2]
    exact hsq
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup ⟨_, hker⟩
  refine ⟨a + 1, Subtype.ext ?_⟩
  have ha' := congrArg (fun z : ↥(CFSG.pCore 2 ↥K) => ((z : ↥K) : G)) ha
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at ha' ⊢
  rw [pow_succ', pow_mul]
  exact ha'

theorem mem_centralizer_ZS_iff {k : G} (hk : k ∈ K) :
    k ∈ Subgroup.centralizer (ZS : Set G) ↔ α ⟨k, hk⟩ ∈ stE0 F := by
  rw [mem_stE0]
  obtain ⟨z₀, hz₀⟩ := s.β_bij.2 (Multiplicative.ofAdd ![1, 0, 0])
  have hz₀Z : (z₀ : G) ∈ ZS := (s.ZS_iff z₀).mpr ⟨1, by rw [hz₀, toAdd_ofAdd, one_smul]⟩
  constructor
  · intro hkC
    have hc : k * z₀ = z₀ * k := (Subgroup.mem_centralizer_iff.mp hkC (z₀ : G) hz₀Z).symm
    have h1 := s.β_act ⟨k, hk⟩ z₀ z₀ (by
      show (z₀ : G) = k * z₀ * k⁻¹
      rw [hc, mul_inv_cancel_right])
    rw [hz₀, toAdd_ofAdd] at h1
    exact h1.symm
  · intro hkα
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzU := s.ZS_le_U hz
    obtain ⟨c, hc⟩ := (s.ZS_iff ⟨z, hzU⟩).mp hz
    let v : ↥(u4311 I K) :=
      ⟨k * z * k⁻¹, (Subgroup.mem_normalizer_iff.mp (s.K_U hk) z).mp hzU⟩
    have h1 := s.β_act ⟨k, hk⟩ ⟨z, hzU⟩ v rfl
    rw [hc, Matrix.mulVec_smul, hkα, ← hc] at h1
    have h2 : v = ⟨z, hzU⟩ := s.β_bij.1 (Multiplicative.toAdd.injective h1)
    have h3 : k * z * k⁻¹ = z := congrArg Subtype.val h2
    calc z * k = k * z * k⁻¹ * k := by rw [h3]
      _ = k * z := by group

theorem P₀_le : ((radE0 F).comap α).map K.subtype ≤ K ⊓ Subgroup.centralizer (ZS : Set G) := by
  intro x hx
  obtain ⟨hxK, hxr⟩ := mem_P₀.mp hx
  exact ⟨hxK, (s.mem_centralizer_ZS_iff hxK).mpr (SL3Pt.radE0_le_stE0 hxr)⟩

theorem exists_K₂_of_mem_stE0 {g : ↥(StatedSL 3 F)} (hg : g ∈ stE0 F) :
    ∃ (k : G) (hk : k ∈ K₂), α ⟨k, s.K₂_le_K hk⟩ = g := by
  rw [← s.K₂_map] at hg
  obtain ⟨⟨k, hkK⟩, hk, rfl⟩ := hg
  exact ⟨k, hk, rfl⟩

theorem pCoreOf_centralizer_ZS :
    pCoreOf 2 (K ⊓ Subgroup.centralizer (ZS : Set G)) = ((radE0 F).comap α).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  set C := K ⊓ Subgroup.centralizer (ZS : Set G) with hC
  set P₀ := ((radE0 F).comap α).map K.subtype with hP₀
  have hconj : ∀ g ∈ C, ∀ x ∈ P₀, g * x * g⁻¹ ∈ P₀ := by
    intro g hg x hx
    obtain ⟨hxK, hxr⟩ := mem_P₀.mp hx
    have hgα := (s.mem_centralizer_ZS_iff hg.1).mp hg.2
    refine mem_P₀.mpr ⟨K.mul_mem (K.mul_mem hg.1 hxK) (K.inv_mem hg.1), ?_⟩
    have e : (⟨g * x * g⁻¹, K.mul_mem (K.mul_mem hg.1 hxK) (K.inv_mem hg.1)⟩ : ↥K) =
        ⟨g, hg.1⟩ * ⟨x, hxK⟩ * (⟨g, hg.1⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (SL3Pt.stE0_le_normalizer_radE0 hgα) _).mp hxr
  have hCN : C ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj g hg x, fun h => ?_⟩
    have := hconj g⁻¹ (C.inv_mem hg) _ h
    simpa [mul_assoc] using this
  apply le_antisymm
  ·
    set O := pCoreOf 2 C with hO
    set N : Subgroup ↥(StatedSL 3 F) := (O.subgroupOf K).map α with hN
    have hOC : O ≤ C := pCoreOf_le 2 C
    have hNst : N ≤ stE0 F := by
      rintro _ ⟨⟨x, hxK⟩, hx, rfl⟩
      exact (s.mem_centralizer_ZS_iff hxK).mp (hOC hx).2
    have hNn : stE0 F ≤ Subgroup.normalizer (N : Set ↥(StatedSL 3 F)) := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := s.exists_K₂_of_mem_stE0 hg
      have hkC : k ∈ C := ⟨s.K₂_le_K hk, s.K₂_le_centralizer hk⟩
      have hkO : k ∈ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 C hkC
      have key : ∀ (k : G) (hkK : k ∈ K), k ∈ Subgroup.normalizer (O : Set G) →
          ∀ z ∈ N, α ⟨k, hkK⟩ * z * (α ⟨k, hkK⟩)⁻¹ ∈ N := by
        intro k hkK hkO z hz
        obtain ⟨⟨x, hxK⟩, hx, rfl⟩ := hz
        refine ⟨⟨k * x * k⁻¹, K.mul_mem (K.mul_mem hkK hxK) (K.inv_mem hkK)⟩,
          (Subgroup.mem_normalizer_iff.mp hkO x).mp hx, ?_⟩
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨key k _ hkO z, fun h => ?_⟩
      have := key k⁻¹ (K.inv_mem (s.K₂_le_K hk)) (inv_mem hkO) _ h
      have e : α ⟨k⁻¹, K.inv_mem (s.K₂_le_K hk)⟩ = (α ⟨k, s.K₂_le_K hk⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [e] at this
      simpa [mul_assoc] using this
    have hN2 : IsPGroup 2 ↥N := by
      have hO2 : IsPGroup 2 ↥(O.subgroupOf K) :=
        (pCoreOf_isPGroup 2 C).of_equiv (Subgroup.subgroupOfEquivOfLe (hOC.trans inf_le_left)).symm
      exact hO2.map α
    have hNr := SL3Pt.le_radE0_of_isPGroup hNst hNn hN2
    intro x hx
    have hxK : x ∈ K := (hOC hx).1
    exact mem_P₀.mpr ⟨hxK, hNr ⟨⟨x, hxK⟩, hx, rfl⟩⟩
  · exact le_pCoreOf_of_le_normalizer 2 s.P₀_le hCN s.isPGroup_P₀

theorem H_le_normalizer_K (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : H ≤ Subgroup.normalizer (K : Set G) :=
  s.sk.base.le_normalizer_of_cComp hR hC h37 h38 h39 s.sk.cComp s.sk.S_le_normalizer

theorem H_le_normalizer_U (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    H ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) := by
  intro g hg
  have hgK := s.H_le_normalizer_K hR hC h37 h38 h39 hg
  have hgQ : g ∈ Subgroup.normalizer ((q4311 I K : Subgroup G) : Set G) := by
    rw [← s.pCoreOf_K_eq h135 hR hC h37 h38 h39]
    exact normalizer_le_normalizer_pCoreOf 2 K hgK
  exact mem_normalizer_inf hgQ (A4.mem_normalizer_centralizer hgQ)

theorem sup_inf_centralizer_U_le (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    (K ⊔ T ⊓ H) ⊓ Subgroup.centralizer ((u4311 I K : Subgroup G) : Set G) ≤ q4311 I K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := T ⊓ H with hS
  set X := (K ⊔ S) ⊓ Subgroup.centralizer ((u4311 I K : Subgroup G) : Set G) with hX
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := s.sk.S_le_normalizer
  have hS2 : IsPGroup 2 ↥S := s.sk.base.hyp.sylow.1.to_le inf_le_left
  have hKSH : K ⊔ S ≤ H := _root_.sup_le (le_of_mem_cComp s.sk.cComp) inf_le_right
  have hX2 : IsPGroup 2 ↥X := by
    intro c
    obtain ⟨k, hk, x, hx, hkx⟩ : ∃ k ∈ K, ∃ x ∈ S, k * x = (c : G) := by
      have h1 : (c : G) ∈ ((K : Set G) * (S : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S hSK]
        exact c.2.1
      obtain ⟨k, hk, x, hx, h⟩ := h1
      exact ⟨k, hk, x, hx, h⟩
    obtain ⟨b, hb⟩ := hS2 ⟨x, hx⟩
    obtain ⟨k', hk', hpow⟩ := exists_pow_eq_mul_of_mem_normalizer (hSK hx) hk (2 ^ b)
    have hxb : x ^ (2 ^ b) = 1 := by
      have h1 := congrArg Subtype.val hb
      simpa using h1
    have hcK : (c : G) ^ (2 ^ b) ∈ K := by
      rw [← hkx, hpow, hxb, mul_one]
      exact hk'
    have hcC : (c : G) ^ (2 ^ b) ∈ Subgroup.centralizer ((u4311 I K : Subgroup G) : Set G) :=
      Subgroup.pow_mem _ c.2.2 _
    have hcQ := s.mem_pCoreOf_of_centralizes hcK fun u =>
      by rw [(Subgroup.mem_centralizer_iff.mp hcC u u.2).symm, mul_inv_cancel_right]
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 K ⟨_, hcQ⟩
    refine ⟨b + a, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val ha
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1 ⊢
    rw [pow_add, pow_mul]
    exact h1
  have hUN : K ⊔ S ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) :=
    hKSH.trans (s.H_le_normalizer_U h135 hR hC h37 h38 h39)
  have hXN : K ⊔ S ≤ Subgroup.normalizer (X : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (A4.mem_normalizer_centralizer (hUN hg))
  have hle := le_pCoreOf_of_le_normalizer 2 inf_le_left hXN hX2
  rwa [s.pCoreOf_sup_eq h135 hR hC h37 h38 h39] at hle

theorem mem_q4311_of_isPGroup (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {c : G}
    (hcH : c ∈ H) (hcU : c ∈ Subgroup.centralizer ((u4311 I K : Subgroup G) : Set G))
    (hc2 : ∃ a : ℕ, c ^ 2 ^ a = 1) : c ∈ q4311 I K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    obtain ⟨a, ha⟩ := hc2
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hb])
  obtain ⟨S', hS', hcS'⟩ := exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr hcH) hz2
  obtain ⟨h, hh, rfl⟩ := (s.sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39).exists_conj hS'
  obtain ⟨x, hx, hxc⟩ := hcS' (Subgroup.mem_zpowers c)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
  have hhU := s.H_le_normalizer_U h135 hR hC h37 h38 h39 hh
  have hxU : x ∈ Subgroup.centralizer ((u4311 I K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : h * u * h⁻¹ ∈ u4311 I K := (Subgroup.mem_normalizer_iff.mp hhU u).mp hu
    have h1 := Subgroup.mem_centralizer_iff.mp hcU _ hu'
    rw [← hxc] at h1
    have h2 : h * (u * x) * h⁻¹ = h * (x * u) * h⁻¹ := by
      calc h * (u * x) * h⁻¹ = h * u * h⁻¹ * (h * x * h⁻¹) := by group
        _ = h * x * h⁻¹ * (h * u * h⁻¹) := h1
        _ = h * (x * u) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hxQ := s.sup_inf_centralizer_U_le h135 hR hC h37 h38 h39 ⟨Subgroup.mem_sup_right hx, hxU⟩
  have hhQ : h ∈ Subgroup.normalizer ((q4311 I K : Subgroup G) : Set G) := by
    rw [← s.pCoreOf_K_eq h135 hR hC h37 h38 h39]
    exact normalizer_le_normalizer_pCoreOf 2 K (s.H_le_normalizer_K hR hC h37 h38 h39 hh)
  rw [← hxc]
  exact (Subgroup.mem_normalizer_iff.mp hhQ x).mp hxQ

theorem le_normalizer_P₀ :
    K₂ ⊔ T ⊓ H ≤ Subgroup.normalizer (((radE0 F).comap α).map K.subtype : Set G) := by
  rw [← s.pCoreOf_centralizer_ZS]
  refine le_trans ?_ (normalizer_le_normalizer_pCoreOf 2 _)
  refine _root_.sup_le (fun k hk => Subgroup.le_normalizer
    (⟨s.K₂_le_K hk, s.K₂_le_centralizer hk⟩ : k ∈ K ⊓ Subgroup.centralizer (ZS : Set G)))
    fun x hx => ?_
  exact mem_normalizer_inf (s.sk.S_le_normalizer hx)
    (A4.mem_normalizer_centralizer (s.T_le_normalizer_ZS hx.1))

theorem P₀_le_sup (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ((radE0 F).comap α).map K.subtype ≤ K₂ ⊔ T ⊓ H := by
  intro x hx
  obtain ⟨hxK, hxr⟩ := mem_P₀.mp hx
  obtain ⟨k, hk, hkα⟩ := s.exists_K₂_of_mem_stE0 (SL3Pt.radE0_le_stE0 hxr)
  have hq : (⟨k, s.K₂_le_K hk⟩ : ↥K)⁻¹ * ⟨x, hxK⟩ ∈ CFSG.pCore 2 ↥K := by
    rw [← s.modO2.2, MonoidHom.mem_ker, map_mul, map_inv, hkα, inv_mul_cancel]
  have hqS : k⁻¹ * x ∈ T ⊓ H :=
    s.sk.pCoreOf_K_le_S hR hC h37 h38 h39 ((mem_pCoreOf_iff' _).mpr hq)
  have e : x = k * (k⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hqS)

theorem P₀_le_R₂ (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : ((radE0 F).comap α).map K.subtype ≤ R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [s.R₂_eq]
  exact le_pCoreOf_of_le_normalizer 2 (s.P₀_le_sup hR hC h37 h38 h39) s.le_normalizer_P₀
    s.isPGroup_P₀

theorem pCoreOf_K₂_le_P₀ : pCoreOf 2 K₂ ≤ ((radE0 F).comap α).map K.subtype := by
  intro x hx
  have hxK₂ : x ∈ K₂ := pCoreOf_le 2 K₂ hx
  have h1 : (⟨x, hxK₂⟩ : ↥K₂) ∈ s.levi.ker := by
    rw [s.ker_levi]
    exact (mem_pCoreOf_iff' _).mp hx
  refine mem_P₀.mpr ⟨s.K₂_le_K hxK₂, ?_⟩
  rw [← s.coe_αK₂ ⟨x, hxK₂⟩, ← slE_stE0Equiv]
  exact ⟨_, ⟨_, h1, rfl⟩, rfl⟩

theorem mem_P₀_of (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {p : G} (hpH : p ∈ H)
    (hp2 : ∃ a : ℕ, p ^ 2 ^ a = 1)
    (hpN : p ∈ Subgroup.normalizer (((radE0 F).comap α).map K.subtype : Set G))
    (hcomm : ∀ k ∈ K₂, p * k * p⁻¹ * k⁻¹ ∈ ((radE0 F).comap α).map K.subtype) :
    p ∈ ((radE0 F).comap α).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  set P₀ := ((radE0 F).comap α).map K.subtype with hP₀
  have hpK : p ∈ Subgroup.normalizer (K : Set G) := s.H_le_normalizer_K hR hC h37 h38 h39 hpH
  have hpU := s.H_le_normalizer_U h135 hR hC h37 h38 h39 hpH
  obtain ⟨fe, hfe⟩ := L4314.exists_conj_coord (F := F) s.β_bij hpU
  have hconjK : ∀ k : ↥K, p * k * p⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp hpK k).mp k.2
  have hconjK' : ∀ k : ↥K, p⁻¹ * k * p ∈ K := fun k => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hpK) k).mp k.2
    simpa using this
  have hrel : ∀ k k' : ↥K, (k' : G) = p * k * p⁻¹ → FFC.SumNat.RelPair fe (α k) (α k') :=
    L4314.relPair_conj_coord s.β_bij s.K_U s.β_act hpU hfe
  obtain ⟨σ, hσ⟩ := FFC.SumNat.exists_semilinear_of_rel fe
    (fun g => by
      obtain ⟨k, rfl⟩ := s.modO2.1 g
      exact ⟨α ⟨_, hconjK k⟩, hrel k ⟨_, hconjK k⟩ rfl⟩)
    (fun g' => by
      obtain ⟨k', rfl⟩ := s.modO2.1 g'
      exact ⟨α ⟨_, hconjK' k'⟩, hrel ⟨_, hconjK' k'⟩ k' (by
        show (k' : G) = p * (p⁻¹ * k' * p) * p⁻¹
        group)⟩)
  have hrad : ∀ a b : F, ∃ a' b' : F, ∀ x, fe (uMat a' b' 0 *ᵥ x) = uMat a b 0 *ᵥ fe x := by
    intro a b
    set g' : ↥(StatedSL 3 F) := specialLinearGroupEquivStatedSL 3 F (uSL a b 0) with hg'
    have hg'm : ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat a b 0 := by
      rw [hg', specialLinearGroupEquivStatedSL_coe, coe_uSL]
    obtain ⟨k', hk'⟩ := s.modO2.1 g'
    have hk'P : (k' : G) ∈ P₀ := mem_P₀.mpr ⟨k'.2, show α k' ∈ radE0 F by
      rw [hk']
      exact SL3Pt.mem_radE0.mpr ⟨a, b, hg'm⟩⟩
    have hkP : p⁻¹ * k' * p ∈ P₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hpN) k').mp hk'P
      simpa using this
    obtain ⟨hkK, hkr⟩ := mem_P₀.mp hkP
    obtain ⟨a', b', hab⟩ := SL3Pt.mem_radE0.mp hkr
    refine ⟨a', b', fun x => ?_⟩
    have h := hrel ⟨_, hkK⟩ k' (by
      show (k' : G) = p * (p⁻¹ * k' * p) * p⁻¹
      group) x
    rw [hab, hk', hg'm] at h
    exact h
  have hlev : ∀ g : SL(2, F), ∃ a b : F, ∀ x,
      fe (SL3Pt.blk (g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) =
        uMat a b 0 *ᵥ (SL3Pt.blk g *ᵥ fe x) := by
    intro g
    have hgst : specialLinearGroupEquivStatedSL 3 F (SL3Pt.blkSL g) ∈ stE0 F :=
      ⟨SL3Pt.blkSL g, SL3Pt.blkSL_mem_stabE0 g, rfl⟩
    obtain ⟨k, hk, hkα⟩ := s.exists_K₂_of_mem_stE0 hgst
    have hkm : ((α ⟨k, s.K₂_le_K hk⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        SL3Pt.blk g := by
      rw [hkα, specialLinearGroupEquivStatedSL_coe]
      rfl
    obtain ⟨hcK, hcr⟩ := mem_P₀.mp (hcomm k hk)
    obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0.mp hcr
    refine ⟨a, b, fun x => ?_⟩
    have hk' : p * k * p⁻¹ ∈ K := hconjK ⟨k, s.K₂_le_K hk⟩
    have h := hrel ⟨k, s.K₂_le_K hk⟩ ⟨_, hk'⟩ rfl x
    have e : (⟨p * k * p⁻¹, hk'⟩ : ↥K) = ⟨p * k * p⁻¹ * k⁻¹, hcK⟩ * ⟨k, s.K₂_le_K hk⟩ := by
      apply Subtype.ext
      show p * k * p⁻¹ = p * k * p⁻¹ * k⁻¹ * k
      group
    rw [hkm, e, map_mul, Subgroup.coe_mul, Units.val_mul, hab, hkm, ← Matrix.mulVec_mulVec] at h
    exact h
  obtain ⟨a₀, ha₀⟩ := hp2
  have hord : ∀ x, (⇑fe)^[2 ^ a₀] x = x := by
    intro x
    obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β u) := by
      rw [hu]
      rfl
    rw [hx]
    exact L4314.iterate_conj_coord hpU hfe (2 ^ a₀) u u (by rw [ha₀]; group)
  obtain ⟨a, b, hab⟩ := SL3Pt.exists_uMat_of_semilinear hσ hrad hlev hord
  set g₀ : ↥(StatedSL 3 F) := specialLinearGroupEquivStatedSL 3 F (uSL a b 0) with hg₀
  have hg₀m : ((g₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat a b 0 := by
    rw [hg₀, specialLinearGroupEquivStatedSL_coe, coe_uSL]
  obtain ⟨k₀, hk₀⟩ := s.modO2.1 g₀
  have hk₀m : ((α k₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat a b 0 := by
    rw [hk₀, hg₀m]
  have hk₀P : (k₀ : G) ∈ P₀ := mem_P₀.mpr ⟨k₀.2, show α k₀ ∈ radE0 F by
    rw [hk₀]
    exact SL3Pt.mem_radE0.mpr ⟨a, b, hg₀m⟩⟩
  set c := (k₀ : G)⁻¹ * p with hc
  have hcU : c ∈ Subgroup.centralizer ((u4311 I K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    let u' : ↥(u4311 I K) := ⟨u, hu⟩
    let v : ↥(u4311 I K) := ⟨p * u * p⁻¹, (Subgroup.mem_normalizer_iff.mp hpU u).mp hu⟩
    have hwU : (k₀ : G)⁻¹ * v * k₀ ∈ u4311 I K := by
      have := (Subgroup.mem_normalizer_iff.mp (s.K_U (K.inv_mem k₀.2)) v).mp v.2
      simpa using this
    let w : ↥(u4311 I K) := ⟨(k₀ : G)⁻¹ * v * k₀, hwU⟩
    have h1 := s.β_act k₀⁻¹ v w (by
      show (k₀ : G)⁻¹ * v * k₀ = (k₀ : G)⁻¹ * v * ((k₀ : G)⁻¹)⁻¹
      rw [inv_inv])
    have hv : Multiplicative.toAdd (β v) = uMat a b 0 *ᵥ Multiplicative.toAdd (β u') := by
      rw [← hfe u' v rfl, hab]
    rw [hv, ← hk₀m, Matrix.mulVec_mulVec, map_inv, Subgroup.coe_inv, Units.inv_mul,
      Matrix.one_mulVec] at h1
    have hwu : w = u' := s.β_bij.1 (Multiplicative.toAdd.injective h1)
    have hw : (k₀ : G)⁻¹ * (p * u * p⁻¹) * k₀ = u := congrArg Subtype.val hwu
    calc u * ((k₀ : G)⁻¹ * p) = (k₀ : G)⁻¹ * (p * u * p⁻¹) * k₀ * ((k₀ : G)⁻¹ * p) := by
          rw [hw]
      _ = (k₀ : G)⁻¹ * p * u := by group
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers p) := by
    obtain ⟨b', -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha₀)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hb'])
  have hPp : IsPGroup 2 ↥(P₀ ⊔ Subgroup.zpowers p) :=
    IsPGroup.to_sup_of_normal_left' s.isPGroup_P₀ hz2 (Subgroup.zpowers_le.mpr hpN)
  have hcmem : c ∈ P₀ ⊔ Subgroup.zpowers p :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (inv_mem hk₀P))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers p))
  obtain ⟨e, he⟩ := hPp ⟨c, hcmem⟩
  have hc2 : ∃ e : ℕ, c ^ 2 ^ e = 1 := ⟨e, by simpa using congrArg Subtype.val he⟩
  have hcH : c ∈ H := H.mul_mem (H.inv_mem (le_of_mem_cComp s.sk.cComp k₀.2)) hpH
  have hcQ := s.mem_q4311_of_isPGroup h135 hR hC h37 h38 h39 hcH hcU hc2
  rw [← s.pCoreOf_K_eq h135 hR hC h37 h38 h39] at hcQ
  have hpc : p = k₀ * c := by
    rw [hc]
    group
  rw [hpc]
  exact P₀.mul_mem hk₀P (s.pCoreOf_K_le_P₀ hcQ)

theorem R₂_eq_P₀ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    R₂ = ((radE0 F).comap α).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun r hr => ?_) (s.P₀_le_R₂ hR hC h37 h38 h39)
  have hKS : R₂ ≤ K₂ ⊔ T ⊓ H := by
    rw [s.R₂_eq]
    exact pCoreOf_le 2 _
  have hrS := hKS hr
  have hrH : r ∈ H :=
    (_root_.sup_le (s.K₂_le_K.trans (le_of_mem_cComp s.sk.cComp)) inf_le_right) hrS
  have hR2 : IsPGroup 2 ↥R₂ := by
    rw [s.R₂_eq]
    exact pCoreOf_isPGroup 2 _
  have hRN : K₂ ⊔ T ⊓ H ≤ Subgroup.normalizer (R₂ : Set G) := by
    rw [s.R₂_eq]
    exact le_normalizer_pCoreOf 2 _
  have hK₂N : K₂ ⊔ T ⊓ H ≤ Subgroup.normalizer (K₂ : Set G) :=
    _root_.sup_le (fun k hk => Subgroup.le_normalizer hk) s.S_le_normalizer_K₂
  have hRK : R₂ ⊓ K₂ ≤ pCoreOf 2 K₂ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => mem_normalizer_inf (hRN (Subgroup.mem_sup_left hk)) (Subgroup.le_normalizer hk))
      (hR2.to_le inf_le_left)
  refine s.mem_P₀_of h135 hR hC h37 h38 h39 hrH ?_ (s.le_normalizer_P₀ hrS) fun k hk => ?_
  · obtain ⟨a, ha⟩ := hR2 ⟨r, hr⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  · apply s.pCoreOf_K₂_le_P₀
    apply hRK
    refine ⟨?_, ?_⟩
    · have h1 : k * r⁻¹ * k⁻¹ ∈ R₂ :=
        (Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_sup_left hk)) r⁻¹).mp (R₂.inv_mem hr)
      have := R₂.mul_mem hr h1
      simpa [mul_assoc] using this
    · have h1 : r * k * r⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp (hK₂N hrS) k).mp hk
      exact K₂.mul_mem h1 (K₂.inv_mem hk)

end Setting4311

end CFSG.Quasithin.H13.Ch4
