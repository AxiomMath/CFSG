module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Defs
public import CFSG.Quasithin.Background.B1Transvection
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapSec
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem swap_odd_pair_commSub (hW : ∀ w : W, w ^ 2 = 1) {K K' : Subgroup (MulAut W)}
    (hcomm : ⁅K, K'⁆ = ⊥) {x y : MulAut W} (hx : x ∈ K) (hy : y ∈ K')
    (hxo : Odd (orderOf x)) (hyo : Odd (orderOf y)) {U₀ U : Subgroup W} (hle : U₀ ≤ U)
    (hLU : StableUnder (K ⊔ K') U) (hU₀ : commSub U₀ (K ⊔ K') = ⊥)
    (hfx : U ⊓ fixV (Subgroup.zpowers x) ≤ U₀) (hfy : U ⊓ fixV (Subgroup.zpowers y) ≤ U₀) :
    commSub U (Subgroup.zpowers x) = commSub U (Subgroup.zpowers y) ∧
      StableUnder (K ⊔ K') (commSub U (Subgroup.zpowers x)) ∧
      commSub U (Subgroup.zpowers x) ⊓ U₀ = ⊥ ∧ commSub U (Subgroup.zpowers x) ⊔ U₀ = U := by
  have hxodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    exact hxo
  have hyodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    exact hyo
  have hxU : ∀ z ∈ Subgroup.zpowers x, ∀ u ∈ U, z u ∈ U := by
    intro z hz u hu
    exact hLU z (((Subgroup.zpowers_le.mpr hx).trans le_sup_left) hz) u hu
  have hyU : ∀ z ∈ Subgroup.zpowers y, ∀ u ∈ U, z u ∈ U := by
    intro z hz u hu
    exact hLU z (((Subgroup.zpowers_le.mpr hy).trans le_sup_right) hz) u hu
  have hcommK : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
    intro k hk k' hk'
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk) k' hk').symm
  have hU0_fixx : U₀ ≤ fixV (Subgroup.zpowers x) := by
    intro u hu z hz
    exact (commSub_eq_bot_iff.mp hU₀ hu) z
      (((Subgroup.zpowers_le.mpr hx).trans le_sup_left) hz)
  have hU0_fixy : U₀ ≤ fixV (Subgroup.zpowers y) := by
    intro u hu z hz
    exact (commSub_eq_bot_iff.mp hU₀ hu) z
      (((Subgroup.zpowers_le.mpr hy).trans le_sup_right) hz)
  obtain ⟨hsupx, hinfx⟩ := B1.coprime_decomp hW hxodd hxU
  obtain ⟨_, hinfy⟩ := B1.coprime_decomp hW hyodd hyU
  have hsupU0 : commSub U (Subgroup.zpowers x) ⊔ U₀ = U := by
    refine le_antisymm ?_ ?_
    · exact sup_le (commSub_le_of_invariant hxU) hle
    · calc U = (U ⊓ fixV (Subgroup.zpowers x)) ⊔ commSub U (Subgroup.zpowers x) := hsupx.symm
        _ ≤ U₀ ⊔ commSub U (Subgroup.zpowers x) := sup_le_sup_right hfx _
        _ = commSub U (Subgroup.zpowers x) ⊔ U₀ := sup_comm ..
  have hM_inf_U0 : commSub U (Subgroup.zpowers x) ⊓ U₀ = ⊥ := by
    have hMfixx : commSub U (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro m hm
      have hmU : m ∈ U := commSub_le_of_invariant hxU hm.1
      have h2 : m ∈ (U ⊓ fixV (Subgroup.zpowers x)) ⊓ commSub U (Subgroup.zpowers x) :=
        ⟨⟨hmU, hm.2⟩, hm.1⟩
      rw [hinfx] at h2
      exact h2
    refine le_antisymm ?_ bot_le
    intro m hm
    have h2 : m ∈ commSub U (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) :=
      ⟨hm.1, hU0_fixx hm.2⟩
    rw [hMfixx] at h2
    exact h2
  have hN_inf_U0 : commSub U (Subgroup.zpowers y) ⊓ U₀ = ⊥ := by
    have hNfixy : commSub U (Subgroup.zpowers y) ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro m hm
      have hmU : m ∈ U := commSub_le_of_invariant hyU hm.1
      have h2 : m ∈ (U ⊓ fixV (Subgroup.zpowers y)) ⊓ commSub U (Subgroup.zpowers y) :=
        ⟨⟨hmU, hm.2⟩, hm.1⟩
      rw [hinfy] at h2
      exact h2
    refine le_antisymm ?_ bot_le
    intro m hm
    have h2 : m ∈ commSub U (Subgroup.zpowers y) ⊓ fixV (Subgroup.zpowers y) :=
      ⟨hm.1, hU0_fixy hm.2⟩
    rw [hNfixy] at h2
    exact h2
  have hMfpf : commSub U (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro m hm
    have hmU : m ∈ U := commSub_le_of_invariant hxU hm.1
    have hmU0 : m ∈ U₀ := hfy ⟨hmU, hm.2⟩
    have h2 : m ∈ commSub U (Subgroup.zpowers x) ⊓ U₀ := ⟨hm.1, hmU0⟩
    rw [hM_inf_U0] at h2
    exact h2
  have hNfpf : commSub U (Subgroup.zpowers y) ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro m hm
    have hmU : m ∈ U := commSub_le_of_invariant hyU hm.1
    have hmU0 : m ∈ U₀ := hfx ⟨hmU, hm.2⟩
    have h2 : m ∈ commSub U (Subgroup.zpowers y) ⊓ U₀ := ⟨hm.1, hmU0⟩
    rw [hN_inf_U0] at h2
    exact h2
  have key : ∀ {A B : Subgroup (MulAut W)} (hA : A ≤ K ⊔ K')
      (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
      (hBodd : Odd (Nat.card B)) (hBU : StableUnder B U)
      (hfpf : commSub U A ⊓ fixV B = ⊥), commSub U A ≤ commSub U B := by
    intro A B hA hAB hBodd hBU hfpf
    have hAstab : StableUnder B (commSub U A) := by
      intro b hb
      exact B1.commSub_smul_mem b (fun v hv => by
        rw [← hAB v hv b hb, mul_assoc, mul_inv_cancel, mul_one]
        exact hv) (fun u hu => hBU b hb u hu)
    obtain ⟨hsup, -⟩ := B1.coprime_decomp hW hBodd hAstab
    have hcommEq : commSub (commSub U A) B = commSub U A := by
      rw [hfpf, bot_sup_eq] at hsup
      exact hsup
    rw [← hcommEq]
    exact commSub_mono (commSub_le_of_invariant (fun a ha u hu => hLU a (hA ha) u hu)) le_rfl
  have hMleN : commSub U (Subgroup.zpowers x) ≤ commSub U (Subgroup.zpowers y) :=
    key (A := Subgroup.zpowers x) (B := Subgroup.zpowers y)
      ((Subgroup.zpowers_le.mpr hx).trans le_sup_left)
      (fun a ha b hb =>
        hcommK a ((Subgroup.zpowers_le.mpr hx) ha) b ((Subgroup.zpowers_le.mpr hy) hb))
      hyodd (fun b hb u hu =>
        hLU b (((Subgroup.zpowers_le.mpr hy).trans le_sup_right) hb) u hu)
      hMfpf
  have hNleM : commSub U (Subgroup.zpowers y) ≤ commSub U (Subgroup.zpowers x) :=
    key (A := Subgroup.zpowers y) (B := Subgroup.zpowers x)
      ((Subgroup.zpowers_le.mpr hy).trans le_sup_right)
      (fun a ha b hb =>
        (hcommK b ((Subgroup.zpowers_le.mpr hx) hb) a ((Subgroup.zpowers_le.mpr hy) ha)).symm)
      hxodd (fun b hb u hu =>
        hLU b (((Subgroup.zpowers_le.mpr hx).trans le_sup_left) hb) u hu)
      hNfpf
  have hK'M : StableUnder K' (commSub U (Subgroup.zpowers x)) := by
    intro k' hk'
    exact B1.commSub_smul_mem k' (fun v hv => by
      have hvK : v ∈ K := (Subgroup.zpowers_le.mpr hx) hv
      rw [← hcommK v hvK k' hk', mul_assoc, mul_inv_cancel, mul_one]
      exact hv) (fun u hu => hLU k' ((le_sup_right : K' ≤ K ⊔ K') hk') u hu)
  have hKN : StableUnder K (commSub U (Subgroup.zpowers y)) := by
    intro k hk
    exact B1.commSub_smul_mem k (fun v hv => by
      have hvK' : v ∈ K' := (Subgroup.zpowers_le.mpr hy) hv
      rw [hcommK k hk v hvK', mul_assoc, mul_inv_cancel, mul_one]
      exact hv) (fun u hu => hLU k ((le_sup_left : K ≤ K ⊔ K') hk) u hu)
  have hKM : StableUnder K (commSub U (Subgroup.zpowers x)) := by
    rw [le_antisymm hMleN hNleM]
    exact hKN
  refine ⟨le_antisymm hMleN hNleM, ?_, hM_inf_U0, hsupU0⟩
  intro g hg m hm
  have hKM' : K ≤ stabSub (commSub U (Subgroup.zpowers x)) := by
    intro k hk u
    exact Iff.intro
      (fun hku => by
        have h := hKM k⁻¹ (K.inv_mem hk) (k u) hku
        simpa using h)
      (fun hu => hKM k hk u hu)
  have hK'M' : K' ≤ stabSub (commSub U (Subgroup.zpowers x)) := by
    intro k hk u
    exact Iff.intro
      (fun hku => by
        have h := hK'M k⁻¹ (K'.inv_mem hk) (k u) hku
        simpa using h)
      (fun hu => hK'M k hk u hu)
  exact ((sup_le hKM' hK'M' hg) m).mpr hm

private theorem w16f_eq_zero_of_mul_eq_self {F : Type} [Field F] {c x : F} (hc : c ≠ 1)
    (h : c * x = x) : x = 0 := by
  have h1 : (c - 1) * x = 0 := by rw [sub_mul, one_mul, sub_eq_zero]; exact h
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero_of_ne hc)

private theorem w16f_diag2_mul_eq_self {F : Type} [Field F] {c : F} (hc : c ≠ 0) (hc1 : c ≠ 1)
    (X : Matrix (Fin 2) (Fin 2) F)
    (hX : (Matrix.SpecialLinearGroup.diag2 c hc : Matrix (Fin 2) (Fin 2) F) * X = X) :
    X = 0 := by
  have hd := Matrix.SpecialLinearGroup.diag2_coe c hc
  rw [hd] at hX
  have hc1' : c⁻¹ ≠ 1 := fun h => hc1 (inv_eq_one.mp h)
  ext i j
  have h := congrFun (congrFun hX i) j
  rw [Matrix.diagonal_mul] at h
  fin_cases i
  · exact w16f_eq_zero_of_mul_eq_self hc1 h
  · exact w16f_eq_zero_of_mul_eq_self hc1' h

private theorem w16f_diag2_pow_eq_one {F : Type} [Field F] {c : F} (hc : c ≠ 0) {n : ℕ}
    (h : c ^ n = 1) : (Matrix.SpecialLinearGroup.diag2 c hc) ^ n = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    Matrix.SpecialLinearGroup.diag2_coe, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, h, inv_pow]

private theorem w16f_diag2_odd_order {F : Type} [Field F] [Finite F] {c : F} (hc : c ≠ 0)
    (hc1 : c ≠ 1) (h2 : (2 : F) = 0) :
    Odd (orderOf (Matrix.SpecialLinearGroup.diag2 c hc)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F 2
  have hcard' : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hodd' : Odd (Fintype.card F - 1) := by
    rw [hcard]
    exact Nat.Even.sub_odd (Nat.succ_le_of_lt (by positivity : 0 < 2 ^ (n : ℕ)))
      (Even.pow_of_ne_zero (even_two : Even (2 : ℕ)) n.2.ne') odd_one
  have hodd : Odd (Nat.card F - 1) := by
    rwa [Nat.card_eq_fintype_card]
  have hpowc : c ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one c hc
  exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one (w16f_diag2_pow_eq_one hc hpowc))

theorem exists_odd_fpf_lift (hW : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)} {t : MulAut W}
    {U₀ U : Subgroup W} (hKs : K ≤ secStabAll U U₀) (hts : t ∈ secStabAll U U₀)
    (hle : U₀ ≤ U) {F : Type} [Field F]
    [Finite F] (hF : 4 ≤ Nat.card F)
    (h : IsMatTensor2 (secImg K U U₀) (secImg (K.map (MulAut.conj t).toMonoidHom) U U₀) F) :
    ∃ x ∈ K, Odd (orderOf x) ∧ U ⊓ fixV (Subgroup.zpowers x) ≤ U₀ ∧
      U ⊓ fixV (Subgroup.zpowers (t * x * t⁻¹)) ≤ U₀ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨φ₁, φ₂, ψ, h₁, h₂⟩ := h
  have hsec2 : ∀ z : SecT U U₀, z ^ 2 = 1 := by
    intro z
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (U₀.subgroupOf U) z
    rw [← hu, ← map_pow, show u ^ 2 = 1 from Subtype.ext (by simpa using hW (u : W)),
      map_one]
  have h2F : (2 : F) = 0 := by
    have h1 := congrArg (fun z => Multiplicative.toAdd (ψ z))
      (hsec2 (ψ.symm (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F))))
    simp only [map_pow, MulEquiv.apply_symm_apply, toAdd_pow, toAdd_ofAdd, map_one,
      toAdd_one] at h1
    have h3 := congrFun (congrFun h1 0) 0
    simpa using h3
  obtain ⟨c, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro c _
      by_cases hc : c = 0
      · simp [hc]
      · have hc1 : c = 1 := h c hc
        simp [hc1]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ] at hcard
    have h2 : ({0, 1} : Finset F).card ≤ 2 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    have hF' : 4 ≤ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
    omega
  let δ : Matrix.SpecialLinearGroup (Fin 2) F := Matrix.SpecialLinearGroup.diag2 c hc0
  have hδodd : Odd (orderOf δ) := w16f_diag2_odd_order hc0 hc1 h2F
  have hδfpf : ∀ X : Matrix (Fin 2) (Fin 2) F,
      (δ : Matrix (Fin 2) (Fin 2) F) * X = X → X = 0 :=
    fun X hX => w16f_diag2_mul_eq_self hc0 hc1 X hX
  let g : ↥(secImg K U U₀) := φ₁.symm δ
  have hφg : (φ₁ g : Matrix.SpecialLinearGroup (Fin 2) F) = δ := by simp [g]
  have hgfpf : ∀ z : SecT U U₀, (g : MulAut (SecT U U₀)) z = z → z = 1 := by
    intro z hz
    have h1 := h₁ g z
    rw [hz, hφg] at h1
    have hzero : Multiplicative.toAdd (ψ z) = 0 := hδfpf _ h1.symm
    have hψz : ψ z = 1 := by
      have := congrArg Multiplicative.ofAdd hzero
      simpa using this
    have := congrArg ψ.symm hψz
    simpa using this
  obtain ⟨a', ha'K, hsecA⟩ := mem_secImg.mp g.2
  let a : MulAut W := (a' : MulAut W)
  have haK : a ∈ K := ha'K
  have haS : a ∈ secStabAll U U₀ := a'.2
  have hsecA' : secAut U U₀ ⟨a, haS⟩ = (g : MulAut (SecT U U₀)) := by
    simpa [a] using hsecA
  have hord_g : orderOf g = orderOf δ := by
    have h := (orderOf_injective φ₁.toMonoidHom φ₁.injective (φ₁.symm δ)).symm
    simpa [g] using h
  have hord_g1 : orderOf (g : MulAut (SecT U U₀)) = orderOf δ := by
    rw [Subgroup.orderOf_coe, hord_g]
  have hdvd : orderOf δ ∣ orderOf a' := by
    have h1 := orderOf_map_dvd (secAut U U₀) a'
    rw [hsecA, hord_g1] at h1
    exact h1
  have hd_gt_one : 1 < orderOf δ := by
    have hne : δ ≠ 1 := by
      intro h
      have h00 : (δ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by rw [h]; simp
      rw [show (δ : Matrix (Fin 2) (Fin 2) F) = !![c, 0; 0, c⁻¹] from
        Matrix.SpecialLinearGroup.diag2_coe' hc0] at h00
      exact hc1 h00
    have hne' : orderOf δ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    have := orderOf_pos δ
    omega
  obtain ⟨r, m, hm_odd, ha'_eq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a').ne'
  have hcop : Nat.Coprime (2 ^ r) (orderOf δ) :=
    (Nat.coprime_two_left.mpr hδodd).pow_left r
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hd_gt_one
  let k : ℕ := 2 ^ r * j
  let x : MulAut W := a ^ k
  have hxK : x ∈ K := K.pow_mem haK k
  have hxS : x ∈ secStabAll U U₀ := (secStabAll U U₀).pow_mem haS k
  have hgpow : (g : MulAut (SecT U U₀)) ^ k = (g : MulAut (SecT U U₀)) := by
    have hd : (g : MulAut (SecT U U₀)) ^ orderOf δ = 1 := by
      rw [← hord_g1]
      exact pow_orderOf_eq_one _
    have hmod := Nat.mod_add_div k (orderOf δ)
    have hjk : k % orderOf δ = 1 := hj
    have hk_eq : k = orderOf δ * (k / orderOf δ) + 1 := by omega
    rw [hk_eq, pow_add, pow_mul, hd, one_pow, one_mul, pow_one]
  have hsecX : secAut U U₀ ⟨x, hxS⟩ = (g : MulAut (SecT U U₀)) := by
    have heq : (⟨x, hxS⟩ : ↥(secStabAll U U₀)) = (⟨a, haS⟩ : ↥(secStabAll U U₀)) ^ k := by
      ext
      rfl
    rw [heq, map_pow, hsecA', hgpow]
  have hxm : x ^ m = 1 := by
    show (a ^ k) ^ m = 1
    have hkm : k * m = (2 ^ r * m) * j := by
      show (2 ^ r * j) * m = (2 ^ r * m) * j
      ring
    have hord_eq : 2 ^ r * m = orderOf a := by rw [← ha'_eq, Subgroup.orderOf_coe]
    rw [← pow_mul, hkm, pow_mul, hord_eq, pow_orderOf_eq_one, one_pow]
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat hm_odd (orderOf_dvd_of_pow_eq_one hxm)
  have hfx : U ⊓ fixV (Subgroup.zpowers x) ≤ U₀ := by
    intro u hu
    have huU : u ∈ U := hu.1
    have hxu : x u = u := hu.2 x (Subgroup.mem_zpowers x)
    have h1 : secAut U U₀ ⟨x, hxS⟩ (QuotientGroup.mk ⟨u, huU⟩) =
        QuotientGroup.mk ⟨u, huU⟩ := by
      rw [secAut_mk]
      congr 1
      exact Subtype.ext hxu
    have h2 : (g : MulAut (SecT U U₀)) (QuotientGroup.mk ⟨u, huU⟩) =
        QuotientGroup.mk ⟨u, huU⟩ := by
      rw [← hsecX]
      exact h1
    have h3 : (QuotientGroup.mk (⟨u, huU⟩ : ↥U) : SecT U U₀) = 1 :=
      hgfpf (QuotientGroup.mk (⟨u, huU⟩ : ↥U) : SecT U U₀) h2
    rwa [QuotientGroup.eq_one_iff] at h3
  have hfy : U ⊓ fixV (Subgroup.zpowers (t * x * t⁻¹)) ≤ U₀ := by
    intro u hu
    have huU : u ∈ U := hu.1
    have hyu : (t * x * t⁻¹) u = u := hu.2 _ (Subgroup.mem_zpowers _)
    have htu : t⁻¹ u ∈ U := (mem_stabSub.mp (Subgroup.inv_mem _ hts.1) u).mpr huU
    have hxfix : x (t⁻¹ u) = t⁻¹ u := by
      have h1 : t (x (t⁻¹ u)) = t (t⁻¹ u) := by
        simpa [MulAut.mul_apply] using hyu
      exact t.injective h1
    have hfix : t⁻¹ u ∈ fixV (Subgroup.zpowers x) := B1.zpowers_fix hxfix
    have hU0 : t⁻¹ u ∈ U₀ := hfx ⟨htu, hfix⟩
    have : t (t⁻¹ u) ∈ U₀ := (mem_stabSub.mp hts.2 (t⁻¹ u)).mpr hU0
    simpa using this
  exact ⟨x, hxK, hxodd, hfx, hfy⟩

end CFSG.LocalAnalysis.WeakClosure81
