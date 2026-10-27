module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndX
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Subgroup CFSG.ComponentClassification.PresentationLocal
open scoped Matrix commutatorElement IsMulCommutative

section Coord

variable {P : Type*} [Group P] [IsElementaryAbelian 2 (P ⧸ center P)]

@[expose] noncomputable def coord (bs : Module.Basis (Fin 4) (ZMod 2) (Additive (P ⧸ center P)))
    (g : P) : Fin 4 → ZMod 2 :=
  bs.equivFun (Additive.ofMul (g : P ⧸ center P))

variable (bs : Module.Basis (Fin 4) (ZMod 2) (Additive (P ⧸ center P)))

theorem coord_mul (g g' : P) : coord bs (g * g') = coord bs g + coord bs g' := by
  simp only [coord, QuotientGroup.mk_mul, ofMul_mul, map_add]

theorem coord_pow (g : P) (n : ℕ) : coord bs (g ^ n) = n • coord bs g := by
  simp only [coord, QuotientGroup.mk_pow, ofMul_pow, map_nsmul]

theorem exists_coord_eq (v : Fin 4 → ZMod 2) : ∃ g : P, coord bs g = v := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul (bs.equivFun.symm v))
  refine ⟨g, ?_⟩
  rw [coord, hg, ofMul_toMul, LinearEquiv.apply_symm_apply]

theorem coord_eq_single {g : P} {j : Fin 4} (hg : (g : P ⧸ center P) = Additive.toMul (bs j)) :
    coord bs g = fun j' => if j = j' then 1 else 0 := by
  funext j'
  rw [coord, hg, ofMul_toMul, Module.Basis.equivFun_self]

theorem eq_top_of_span {T : Subgroup P} (hZ : center P ≤ T) {g₁ g₂ g₃ g₄ : P} (h₁ : g₁ ∈ T)
    (h₂ : g₂ ∈ T) (h₃ : g₃ ∈ T) (h₄ : g₄ ∈ T)
    (hspan : ∀ v, ∃ c₁ c₂ c₃ c₄ : ZMod 2,
      c₁ • coord bs g₁ + c₂ • coord bs g₂ + c₃ • coord bs g₃ + c₄ • coord bs g₄ = v) :
    T = ⊤ := by
  have hval : ∀ (c : ZMod 2) (w : Fin 4 → ZMod 2), c.val • w = c • w := fun c w => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨c₁, c₂, c₃, c₄, hc⟩ := hspan (coord bs s)
  set t := g₁ ^ c₁.val * g₂ ^ c₂.val * g₃ ^ c₃.val * g₄ ^ c₄.val with htdef
  have htT : t ∈ T :=
    mul_mem (mul_mem (mul_mem (pow_mem h₁ _) (pow_mem h₂ _)) (pow_mem h₃ _)) (pow_mem h₄ _)
  have hts : coord bs t = coord bs s := by
    rw [htdef, coord_mul, coord_mul, coord_mul, coord_pow, coord_pow, coord_pow, coord_pow, hval,
      hval, hval, hval, hc]
  have hq : (t : P ⧸ center P) = s :=
    Additive.ofMul.injective (bs.equivFun.injective hts)
  have hmem := mul_mem htT (hZ (QuotientGroup.eq.mp hq))
  rwa [mul_inv_cancel_left] at hmem

end Coord

theorem exists_minus_vectors : ∀ k : Fin 6, ∃ e f g h : Fin 4 → ZMod 2,
    quadForm (omegaVec k) e = 0 ∧ quadForm (omegaVec k) f = 0 ∧
    quadForm (omegaVec k) g = 1 ∧ quadForm (omegaVec k) h = 1 ∧
    e ⬝ᵥ antidiagGram *ᵥ f = 1 ∧ g ⬝ᵥ antidiagGram *ᵥ h = 1 ∧
    e ⬝ᵥ antidiagGram *ᵥ g = 0 ∧ e ⬝ᵥ antidiagGram *ᵥ h = 0 ∧
    f ⬝ᵥ antidiagGram *ᵥ g = 0 ∧ f ⬝ᵥ antidiagGram *ᵥ h = 0 ∧
    ∀ v, ∃ c₁ c₂ c₃ c₄ : ZMod 2, c₁ • e + c₂ • f + c₃ • g + c₄ • h = v := by
  intro k
  fin_cases k
  · exact ⟨![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 0, 0, 1], ![1, 1, 1, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 1, 1], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 1, 0], ![0, 1, 0, 1], ![0, 0, 0, 1], ![1, 0, 1, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 1], ![1, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], by decide +kernel⟩

theorem pow_four_eq_mul {M : Type*} [Monoid M] (x : M) : x ^ 4 = (x * x) * (x * x) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]

theorem conj_eq_inv_of {P : Type*} [Group P] {z x y : P} (hz : z ∈ center P) (hzz : z * z = 1)
    (hxx : x * x = z) (hyx : y * x = z * (x * y)) : y * x * y⁻¹ = x⁻¹ := by
  have hxinv : z * x = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hxx, hzz])
  have _ := hz
  calc y * x * y⁻¹ = z * (x * y) * y⁻¹ := by rw [hyx]
    _ = z * x := by group
    _ = x⁻¹ := hxinv

theorem center_cases {P : Type*} [Group P] (hcyc : IsCyclic (center P)) {z : P}
    (hzc : z ∈ center P) (hz1 : z ≠ 1) (h4 : ∀ c ∈ center P, c ^ 4 = 1)
    (hinv : ∀ t ∈ center P, t * t = 1 → t = 1 ∨ t = z) :
    center P = zpowers z ∨ ∃ i ∈ center P, i * i = z ∧ center P = zpowers i := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hic : (g : P) ∈ center P := g.2
  have hZ : center P = zpowers (g : P) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact mem_zpowers_iff.mpr ⟨n, by rw [← Subgroup.coe_zpow, hn]⟩
    · exact zpowers_le.mpr hic
  by_cases hii : (g : P) * g = 1
  · left
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hZ ▸ hzc)
    have h2 : (g : P) ^ (2 : ℤ) = 1 := by rw [zpow_two, hii]
    have hn' : (g : P) ^ n = (g : P) ^ (n % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
      rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · rw [hn', h0, zpow_zero] at hn
      exact absurd hn.symm hz1
    · rw [hn', h1, zpow_one] at hn
      rw [hZ, hn]
  · right
    refine ⟨g, hic, ?_, hZ⟩
    have hi4 : ((g : P) * g) * ((g : P) * g) = 1 := by rw [← pow_four_eq_mul, h4 _ hic]
    rcases hinv _ (mul_mem hic hic) hi4 with h | h
    · exact absurd h hii
    · exact h

section Rep

variable {X : Type*} [Group X]

theorem conjNormal_eq_of_mem_center {S : Subgroup X} [S.Normal] {z : S} (hz : (z : X) ∈ center X)
    (γ : X) : (MulAut.conjNormal γ z : S) = z := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, mem_center_iff.mp hz γ, mul_inv_cancel_right]

theorem le_ker_quotConj {S : Subgroup X} [S.Normal] {z : S} (h : CommData S z) :
    S ≤ (quotConj S).ker := by
  intro s hs
  rw [MonoidHom.mem_ker]
  ext q
  induction q using QuotientGroup.induction_on with
  | H t =>
    rw [quotConj_mk, MulAut.one_apply, QuotientGroup.eq]
    have hc := h.comm_mem_center ⟨s, hs⟩ t⁻¹
    have he : (MulAut.conjNormal s t)⁻¹ * t = ⁅(⟨s, hs⟩ : S), t⁻¹⁆ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
        commutatorElement_def]
      group
    rw [he]
    exact hc

theorem exists_sympRep {z₀ : X} (hz₀ : z₀ ∈ center X) (hz : z₀ ∈ pCore 2 X)
    (h : CommData (pCore 2 X) ⟨z₀, hz⟩)
    (ε : zpowers (⟨z₀, hz⟩ : pCore 2 X) ≃* Multiplicative (ZMod 2))
    [IsElementaryAbelian 2 (pCore 2 X ⧸ center (pCore 2 X))]
    (bs : Module.Basis (Fin 4) (ZMod 2) (Additive (pCore 2 X ⧸ center (pCore 2 X))))
    (hbs : ∀ i j, commB h ε (Additive.toMul (bs i)) (Additive.toMul (bs j)) = antidiagGram i j)
    (hC2 : (quotConj (pCore 2 X)).ker ≤ pCore 2 X) :
    ∃ ρ : X →* sympFour, ρ.ker = pCore 2 X ∧
      ∀ (x : X) (q : pCore 2 X ⧸ center (pCore 2 X)),
        ((ρ x : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
            bs.equivFun (Additive.ofMul q) =
          bs.equivFun (Additive.ofMul (quotConj (pCore 2 X) x q)) := by
  have hφ : ∀ (γ : X) (u v : pCore 2 X ⧸ center (pCore 2 X)),
      commB h ε (quotConj (pCore 2 X) γ u) (quotConj (pCore 2 X) γ v) = commB h ε u v :=
    fun γ u v => by
      rw [quotConj_apply]
      exact commB_quotAut h ε (conjNormal_eq_of_mem_center hz₀ γ) u v
  refine ⟨sympRep (commB h ε) (commB_mul_left h ε) (commB_mul_right h ε) bs hbs _ hφ, ?_,
    fun x q => sympRepGL_mulVec bs _ x q⟩
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    apply hC2
    rw [MonoidHom.mem_ker, ← sympRepGL_eq_one_iff bs]
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    exact (sympRepGL_eq_one_iff bs _ x).mpr (MonoidHom.mem_ker.mp (le_ker_quotConj h hx))

end Rep

section Endgame

variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
  [IsSimpleGroup (X ⧸ K)]

include K in
theorem extOf_q8D8 {z₀ : X} (hz₀ : z₀ ∈ center X)
    (hz : z₀ ∈ pCore 2 X) (h : CommData (pCore 2 X) ⟨z₀, hz⟩)
    (hcard16 : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 16)
    (hC2 : (quotConj (pCore 2 X)).ker ≤ pCore 2 X)
    (hZ : center (pCore 2 X) = zpowers ⟨z₀, hz⟩) : IsExtOf X (alternatingGroup (Fin 5)) Q8D8 := by
  set z : pCore 2 X := ⟨z₀, hz⟩ with hzdef
  have : IsElementaryAbelian 2 (pCore 2 X ⧸ center (pCore 2 X)) := isElementaryAbelian_quot h
  obtain ⟨ε⟩ := h.nonempty_mulEquiv
  obtain ⟨bs, hbs⟩ := exists_basis_antidiag hcard16 (commB h ε) (commB_mul_left h ε)
    (commB_mul_right h ε) (commB_self h ε) (eq_one_of_commB h ε)
  obtain ⟨ρ, hker, hρv⟩ := exists_sympRep hz₀ hz h ε bs hbs hC2
  have hne : ρ.range ≠ ⊥ := by
    intro hbot
    apply pCore_two_ne_top (K := K)
    refine eq_top_iff.mpr fun x _ => ?_
    rw [← hker, MonoidHom.mem_ker]
    have : ρ x ∈ ρ.range := ⟨x, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  set H₆ := ρ.range.map omegaPerm with hH₆
  have hH₆p : Group.IsPerfect H₆ := Group.IsPerfect.map _
  have hH₆ne : H₆ ≠ ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ omegaPerm_injective).not.mpr hne
  have eX : X ⧸ pCore 2 X ≃* H₆ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ρ).trans (ρ.range.equivMapOfInjective omegaPerm
      omegaPerm_injective))
  have hbc : ∀ g g' : pCore 2 X, commB h ε g g' = coord bs g ⬝ᵥ antidiagGram *ᵥ coord bs g' :=
    fun g g' => b_eq_dotProduct _ (commB_mul_left h ε) (commB_mul_right h ε) bs hbs _ _
  have hsymm := symm_of_alt (commB h ε) (commB_mul_left h ε) (commB_mul_right h ε)
    (commB_self h ε)
  have hcardS := card_eq_card_quotient_mul_card_subgroup (center (pCore 2 X))
  set q := quadQ h hZ ε with hqdef
  have hqmul : ∀ x y, q (x * y) = q x + q y + commB h ε x y := quadQ_mul h hZ ε
  set a : Fin 4 → ZMod 2 := fun j => q (Additive.toMul (bs j)) with ha
  have hqa : ∀ x, q x = quadForm a (bs.equivFun (Additive.ofMul x)) :=
    quad_eq_quadForm (commB h ε) (commB_mul_left h ε) (commB_mul_right h ε) bs hbs q hqmul
  have hpres : ∀ g ∈ ρ.range, ∀ v, quadForm a
      (((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) = quadForm a v := by
    rintro _ ⟨x, rfl⟩ v
    obtain ⟨u, rfl⟩ : ∃ u, bs.equivFun (Additive.ofMul u) = v :=
      ⟨Additive.toMul (bs.equivFun.symm v), by rw [ofMul_toMul, LinearEquiv.apply_symm_apply]⟩
    rw [hρv, ← hqa, ← hqa, quotConj_apply, hqdef,
      quadQ_quotAut h hZ ε (conjNormal_eq_of_mem_center hz₀ x)]
  have hamem : a ∈ Set.range omegaVec := by
    by_contra ha'
    exact hne (eq_bot_of_perfect_of_quadForm ha' inferInstance hpres)
  obtain ⟨k, hk⟩ := hamem
  have hfix : ∀ σ ∈ H₆, σ k = k := by
    rintro _ ⟨g, hg, rfl⟩
    exact omegaPerm_eq_of_quadForm (by rw [hk]; exact hpres g hg)
  obtain ⟨e₅⟩ := perfect_perm_six_of_fix hH₆p hH₆ne hfix
  refine ⟨pCore 2 X, inferInstance, ?_, ⟨eX.trans e₅⟩⟩
  obtain ⟨ve, vf, vg, vh, hQe, hQf, hQg, hQh, hBef, hBgh, hBeg, hBeh, hBfg, hBfh, hspan⟩ :=
    exists_minus_vectors k
  obtain ⟨u, hu⟩ := exists_coord_eq bs ve
  obtain ⟨v, hv⟩ := exists_coord_eq bs vf
  obtain ⟨x, hx⟩ := exists_coord_eq bs vg
  obtain ⟨y, hy⟩ := exists_coord_eq bs vh
  have hqc : ∀ g : pCore 2 X, q g = quadForm (omegaVec k) (coord bs g) := fun g => by
    rw [hk]
    exact hqa g
  have hsq0 : ∀ g : pCore 2 X, q g = 0 → g * g = 1 := fun g hg =>
    (quadQ_eq_zero_iff h hZ ε g).mp hg
  have hsq1 : ∀ g : pCore 2 X, q g = 1 → g * g = z := by
    intro g hg
    have hmem : g * g ∈ zpowers z := hZ ▸ h.sq_mem g
    rcases h.mem_zpowers_iff.mp hmem with h1 | h1
    · rw [hqdef, quadQ_eq_zero_iff h hZ ε g |>.mpr h1] at hg
      exact absurd hg (by decide)
    · exact h1
  have huu : u * u = 1 := hsq0 u (by rw [hqc, hu, hQe])
  have hvv : v * v = 1 := hsq0 v (by rw [hqc, hv, hQf])
  have hxx : x * x = z := hsq1 x (by rw [hqc, hx, hQg])
  have hyy : y * y = z := hsq1 y (by rw [hqc, hy, hQh])
  have huv : (u * v) * (u * v) = z := hsq1 _ (by
    rw [QuotientGroup.mk_mul, hqmul, hqc, hqc, hu, hv, hQe, hQf, hbc, hu, hv, hBef]
    decide)
  have hcomm0 : ∀ g g' : pCore 2 X, coord bs g ⬝ᵥ antidiagGram *ᵥ coord bs g' = 0 →
      g * g' = g' * g := fun g g' h0 => mul_comm_of_commB_eq_zero h ε (by rw [hbc]; exact h0)
  have hyx : y * x = z * (x * y) := mul_eq_of_commB_eq_one h ε (by
    rw [hsymm, hbc, hx, hy, hBgh])
  have hS32 : Nat.card (pCore 2 X) = 32 := by
    rw [hcardS, hcard16, hZ, h.card_zpowers]
  have hgen : closure {u, v, x, y} = ⊤ := by
    refine eq_top_of_span bs (g₁ := u) (g₂ := v) (g₃ := x) (g₄ := y) ?_
      (subset_closure (by simp)) (subset_closure (by simp)) (subset_closure (by simp))
      (subset_closure (by simp)) (by rw [hu, hv, hx, hy]; exact hspan)
    rw [hZ, zpowers_le, ← hxx]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  exact nonempty_mulEquiv_q8D8 hS32 huu hvv (by rw [sq, sq, huv, hxx])
    (by rw [pow_four_eq_mul, hxx, h.sq_eq_one]) (by rw [sq, hxx]; exact h.ne_one)
    (by rw [sq, sq, hyy, hxx]) (conj_eq_inv_of h.mem_center h.sq_eq_one hxx hyx)
    (hcomm0 _ _ (by rw [hu, hx, hBeg])) (hcomm0 _ _ (by rw [hu, hy, hBeh]))
    (hcomm0 _ _ (by rw [hv, hx, hBfg])) (hcomm0 _ _ (by rw [hv, hy, hBfh])) hgen

include K in
theorem extOf_z4Q8Q8 {z₀ : X} (hz₀ : z₀ ∈ center X)
    (hz : z₀ ∈ pCore 2 X) (h : CommData (pCore 2 X) ⟨z₀, hz⟩)
    (hcard16 : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 16)
    (hC2 : (quotConj (pCore 2 X)).ker ≤ pCore 2 X)
    {E : Subgroup (pCore 2 X)} (hEZ : E ⊔ center (pCore 2 X) = ⊤)
    (hEZ' : E ⊓ center (pCore 2 X) = zpowers ⟨z₀, hz⟩) {i : pCore 2 X}
    (hic : i ∈ center (pCore 2 X)) (hii : i * i = ⟨z₀, hz⟩) (hZi : center (pCore 2 X) = zpowers i) :
    IsExtOf X (alternatingGroup (Fin 5)) Z4Q8Q8 ∨ IsExtOf X (alternatingGroup (Fin 6)) Z4Q8Q8 := by
  set z : pCore 2 X := ⟨z₀, hz⟩ with hzdef
  have : IsElementaryAbelian 2 (pCore 2 X ⧸ center (pCore 2 X)) := isElementaryAbelian_quot h
  obtain ⟨ε⟩ := h.nonempty_mulEquiv
  obtain ⟨bs, hbs⟩ := exists_basis_antidiag hcard16 (commB h ε) (commB_mul_left h ε)
    (commB_mul_right h ε) (commB_self h ε) (eq_one_of_commB h ε)
  obtain ⟨ρ, hker, hρv⟩ := exists_sympRep hz₀ hz h ε bs hbs hC2
  have hne : ρ.range ≠ ⊥ := by
    intro hbot
    apply pCore_two_ne_top (K := K)
    refine eq_top_iff.mpr fun x _ => ?_
    rw [← hker, MonoidHom.mem_ker]
    have : ρ x ∈ ρ.range := ⟨x, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  set H₆ := ρ.range.map omegaPerm with hH₆
  have hH₆p : Group.IsPerfect H₆ := Group.IsPerfect.map _
  have hH₆ne : H₆ ≠ ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ omegaPerm_injective).not.mpr hne
  have eX : X ⧸ pCore 2 X ≃* H₆ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ρ).trans (ρ.range.equivMapOfInjective omegaPerm
      omegaPerm_injective))
  have hcardS := card_eq_card_quotient_mul_card_subgroup (center (pCore 2 X))
  have hlift := exists_lift_sq_eq h hEZ hEZ' hic hii
  obtain ⟨x₁, hx₁q, hx₁⟩ := hlift (Additive.toMul (bs 0))
  obtain ⟨x₂, hx₂q, hx₂⟩ := hlift (Additive.toMul (bs 1))
  obtain ⟨y₂, hy₂q, hy₂⟩ := hlift (Additive.toMul (bs 2))
  obtain ⟨y₁, hy₁q, hy₁⟩ := hlift (Additive.toMul (bs 3))
  have hb : ∀ (g g' : pCore 2 X) (j j' : Fin 4),
      (g : pCore 2 X ⧸ center (pCore 2 X)) = Additive.toMul (bs j) →
      (g' : pCore 2 X ⧸ center (pCore 2 X)) = Additive.toMul (bs j') →
      commB h ε g g' = antidiagGram j j' := fun g g' j j' hg hg' => by rw [hg, hg', hbs]
  have h11 : x₁ * x₂ = x₂ * x₁ :=
    mul_comm_of_commB_eq_zero h ε (by rw [hb _ _ 0 1 hx₁q hx₂q]; decide)
  have h12 : x₁ * y₂ = y₂ * x₁ :=
    mul_comm_of_commB_eq_zero h ε (by rw [hb _ _ 0 2 hx₁q hy₂q]; decide)
  have h21 : y₁ * x₂ = x₂ * y₁ :=
    mul_comm_of_commB_eq_zero h ε (by rw [hb _ _ 3 1 hy₁q hx₂q]; decide)
  have h22 : y₁ * y₂ = y₂ * y₁ :=
    mul_comm_of_commB_eq_zero h ε (by rw [hb _ _ 3 2 hy₁q hy₂q]; decide)
  have hyx₁ : y₁ * x₁ = z * (x₁ * y₁) :=
    mul_eq_of_commB_eq_one h ε (by rw [hb _ _ 3 0 hy₁q hx₁q]; decide)
  have hyx₂ : y₂ * x₂ = z * (x₂ * y₂) :=
    mul_eq_of_commB_eq_one h ε (by rw [hb _ _ 2 1 hy₂q hx₂q]; decide)
  have hord : orderOf i = 4 := by
    have h1 : ¬ i ^ 2 ^ 1 = 1 := by rw [pow_one, sq, hii]; exact h.ne_one
    have h2 : i ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 4 from rfl, pow_four_eq_mul, hii, h.sq_eq_one]
    exact orderOf_eq_prime_pow h1 h2
  have hS64 : Nat.card (pCore 2 X) = 64 := by
    rw [hcardS, hcard16, hZi, Nat.card_zpowers, hord]
  have hgen : closure {i, x₁, y₁, x₂, y₂} = ⊤ := by
    refine eq_top_of_span bs (g₁ := x₁) (g₂ := x₂) (g₃ := y₂) (g₄ := y₁) ?_
      (subset_closure (by simp)) (subset_closure (by simp)) (subset_closure (by simp))
      (subset_closure (by simp)) fun v => ⟨v 0, v 1, v 2, v 3, ?_⟩
    · rw [hZi, zpowers_le]
      exact subset_closure (by simp)
    · rw [coord_eq_single bs hx₁q, coord_eq_single bs hx₂q, coord_eq_single bs hy₂q,
        coord_eq_single bs hy₁q]
      funext j
      fin_cases j <;> simp
  obtain ⟨eS⟩ := nonempty_mulEquiv_z4Q8Q8 hS64
    (fun t => (mem_center_iff.mp hic t).symm) (by rw [sq, sq, hii, hx₁])
    (by rw [pow_four_eq_mul, hx₁, h.sq_eq_one]) (by rw [sq, hx₁]; exact h.ne_one)
    (by rw [sq, sq, hy₁, hx₁]) (conj_eq_inv_of h.mem_center h.sq_eq_one hx₁ hyx₁)
    (by rw [sq, sq, hx₂, hx₁]) (by rw [sq, sq, hy₂, hx₁])
    (conj_eq_inv_of h.mem_center h.sq_eq_one hx₂ hyx₂) h11 h12 h21 h22 hgen
  rcases perfect_perm_six hH₆p hH₆ne with hA6 | he₅
  · exact Or.inr ⟨pCore 2 X, inferInstance, ⟨eS⟩, ⟨eX.trans (MulEquiv.subgroupCongr hA6)⟩⟩
  · obtain ⟨e₅⟩ := he₅
    exact Or.inl ⟨pCore 2 X, inferInstance, ⟨eS⟩, ⟨eX.trans e₅⟩⟩


theorem endgame_of_facts (hK : Group.IsSolvable K) (hO : oddCore X = ⊥)
    (hq : ¬ IsQuasisimple X) {z₀ : X} (hz₀ : z₀ ∈ center X) (hz₀1 : z₀ ≠ 1)
    (hz₀2 : z₀ * z₀ = 1)
    (H1 : ∀ A : Subgroup X, A.Normal → IsPGroup 2 A → IsMulCommutative A → A ≤ center X)
    (H2 : ∀ t ∈ center X, t * t = 1 → t = 1 ∨ t = z₀) (H3 : PairBound X z₀) :
    IsExtOf X (alternatingGroup (Fin 5)) Q8D8 ∨ IsExtOf X (alternatingGroup (Fin 5)) Z4Q8Q8 ∨
      IsExtOf X (alternatingGroup (Fin 6)) Z4Q8Q8 := by
  obtain ⟨hz, h, hcyc, hZX, ⟨E, hEZ, hEZ'⟩, w, -, hcard⟩ :=
    structure_pCore_two hK hO hq hz₀ hz₀1 hz₀2 H1 H2
  have hC2 := ker_quotConj_le hK hO hq hZX
  obtain ⟨hw, h4⟩ := eq_two_of_pairBound (K := K) hz h hEZ hEZ' hcard hC2 H3
  subst hw
  have hcard16 : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 16 := by rw [hcard]; norm_num
  have hinvS : ∀ t ∈ center (pCore 2 X), t * t = 1 → t = 1 ∨ t = ⟨z₀, hz⟩ := by
    intro t ht htt
    rcases H2 _ (hZX t ht) (congrArg Subtype.val htt) with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  rcases center_cases hcyc h.mem_center h.ne_one h4 hinvS with hZ | ⟨i, hic, hii, hZi⟩
  · exact Or.inl (extOf_q8D8 (K := K) hz₀ hz h hcard16 hC2 hZ)
  · exact Or.inr (extOf_z4Q8Q8 (K := K) hz₀ hz h hcard16 hC2 hEZ hEZ' hic hii hZi)

end Endgame

end CFSG.RankThree.PartTwo.Sec4.Census
