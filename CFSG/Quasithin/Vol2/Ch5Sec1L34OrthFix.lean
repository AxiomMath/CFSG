module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FixTwo
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs520
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs522
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative MatrixGroups Matrix
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL fixed_of_unip
  exists_add_frobPow_ne_zero unipSL_mul_self)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField (ringAut_card_and_cyclic
  finite_field_involution_exact)

variable {G : Type} [Group G]

theorem exists_fixed_of_two {V : Type*} [Group V] [Finite V] {Q : Subgroup (MulAut V)}
    (hQ : IsPGroup 2 Q) {M : Subgroup V} (hM2 : ∀ v ∈ M, v ^ 2 = 1) (hM : M ≠ ⊥)
    (hQM : ∀ q ∈ Q, ∀ v ∈ M, q v ∈ M) : ∃ v ∈ M, v ≠ 1 ∧ ∀ q ∈ Q, q v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction ↥Q ↥M :=
    { smul := fun q v => ⟨(q : MulAut V) v, hQM q q.2 v v.2⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun q₁ q₂ v => Subtype.ext rfl }
  have hM2' : IsPGroup 2 M := fun v => ⟨1, Subtype.ext (by simpa using hM2 v v.2)⟩
  have hcard : 2 ∣ Nat.card M := by
    rcases hM2'.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) hM
    · exact h2
  have h1 : (1 : ↥M) ∈ MulAction.fixedPoints ↥Q ↥M := fun q =>
    Subtype.ext (map_one (q : MulAut V))
  obtain ⟨v, hv, hv1⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥M hcard h1
  exact ⟨v, v.2, fun h => hv1 (Subtype.ext h.symm), fun q hq => congrArg Subtype.val (hv ⟨q, hq⟩)⟩

theorem sq_eq_one_of_coord {F : Type} [Field F] [CharP F 2] {V : Type*} [Group V]
    {Y : V →* Multiplicative (Matrix (Fin 2) (Fin 2) F)} (hYinj : Function.Injective Y) (w : V) :
    w ^ 2 = 1 := by
  apply hYinj
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

section Line

variable [Finite G]

theorem IsOrthCh5.exists_lineCoord {L W S : Subgroup G} {m : ℕ}
    (h : IsOrthCh5 L W (2 * m)) (hS : IsSylowTwoOf S L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * m) ∧
      ∃ (ψ : ↥(autOn L W) ≃* SL(2, F)) (Y : ↥W →* Multiplicative (Matrix (Fin 2) (Fin 2) F)),
        Function.Injective Y ∧
        (∀ w, (frobPow m (Multiplicative.toAdd (Y w)))ᵀ = Multiplicative.toAdd (Y w)) ∧
        (∀ X : Matrix (Fin 2) (Fin 2) F, (frobPow m X)ᵀ = X →
          ∃ w, Multiplicative.toAdd (Y w) = X) ∧
        (∀ (x : ↥(autOn L W)) (w : ↥W), Multiplicative.toAdd (Y ((x : MulAut ↥W) w)) =
          (ψ x : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (Y w) *
            (frobPow m (ψ x : Matrix (Fin 2) (Fin 2) F))ᵀ) ∧
        (∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn S W ↔ ∃ b : F, ψ x = unipSL b) ∧
        (∀ v : ↥W, (v : G) ∈ Subgroup.centralizer (S : Set G) →
          (Multiplicative.toAdd (Y v)) 0 1 = 0 ∧ (Multiplicative.toAdd (Y v)) 1 0 = 0 ∧
            (Multiplicative.toAdd (Y v)) 1 1 = 0) ∧
        (∀ v : ↥W, (v : G) ∈ Subgroup.centralizer (S : Set G) → v ≠ 1 →
          (Multiplicative.toAdd (Y v)) 0 0 ≠ 0) := by
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := h.le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, hYherm, hYsurj, hYint, hP⟩ := h.exists_sylowCoord hS
  have := Fintype.ofFinite F
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have h1 := Finite.one_lt_card (α := F)
      rw [hF] at h1
      norm_num at h1
    · exact h0
  have hσ : ∀ x : F, (x ^ 2 ^ m) ^ 2 ^ m = x := fun x => by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hb0 := exists_add_frobPow_ne_zero hm1 hF
  have hline : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer (S : Set G) →
      (Multiplicative.toAdd (Y v)) 0 1 = 0 ∧ (Multiplicative.toAdd (Y v)) 1 0 = 0 ∧
        (Multiplicative.toAdd (Y v)) 1 1 = 0 := by
    intro v hv
    refine fixed_of_unip hσ hb0 (hYherm v) fun b => ?_
    have hxP : ((ψ.symm (unipSL b) : ↥(autOn L W)) : MulAut ↥W) ∈ autOn S W :=
      (hP _).mpr ⟨b, MulEquiv.apply_symm_apply _ _⟩
    have hfix := (mem_centralizer_iff_autOn (hS.1.trans hLW) v).mp hv _ hxP
    have h1 := hYint (ψ.symm (unipSL b)) v
    rw [hfix, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, ψ, Y, hYinj, hYherm, hYsurj, hYint,
    hP, hline, fun v hv hv1 h00 => ?_⟩
  obtain ⟨h01, h10, h11⟩ := hline v hv
  apply hv1
  apply hYinj
  rw [map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact mat2_ext (by rw [h00]; rfl) (by rw [h01]; rfl) (by rw [h10]; rfl) (by rw [h11]; rfl)

end Line

theorem orthKernelFact : OrthKernelFact := by
  intro G _ _ L V S Dm m hV hS hDm hcard v hv
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, -, -, hYint, hP, hline, -⟩ := hV.exists_lineCoord hS
  obtain ⟨hvV, hvS⟩ := hv
  obtain ⟨h01, h10, h11⟩ := hline ⟨v, hvV⟩ hvS
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hdL : d ∈ L := (hDm hd).1
  set xd := autHom hLV ⟨d, hdL⟩ with hxd
  have hxdN : (xd : MulAut ↥V) ∈
      Subgroup.normalizer ((autOn S V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    conjAct_mem_normalizer_autOn ⟨d, hLV hdL⟩ (hDm hd).2
  have hxd10 := upper_of_mem_normalizer ψ hP xd hxdN
  have hpow : (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 *
      (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 ^ m = 1 := by
    have h1 : (⟨d, hdL⟩ : ↥L) ^ (2 ^ m + 1) = 1 := by
      have h2 : (⟨d, hd⟩ : ↥Dm) ^ (2 ^ m + 1) = 1 := by
        rw [← hcard]
        exact pow_card_eq_one'
      apply Subtype.ext
      have := congrArg Subtype.val h2
      simpa using this
    have h3 : ψ xd ^ (2 ^ m + 1) = 1 := by
      rw [hxd, ← map_pow, ← map_pow, h1, map_one, map_one]
    have h4 := (upper_pow hxd10 (2 ^ m + 1)).2
    rw [h3, pow_succ'] at h4
    simpa using h4.symm
  have hY : Y ((xd : MulAut ↥V) ⟨v, hvV⟩) = Y ⟨v, hvV⟩ := by
    apply Multiplicative.toAdd.injective
    obtain ⟨e00, e01, e10, e11⟩ := twist_upper m hxd10 h01 h10 h11
    rw [hYint]
    refine mat2_ext ?_ (by rw [e01, h01]) (by rw [e10, h10]) (by rw [e11, h11])
    rw [e00]
    linear_combination (Multiplicative.toAdd (Y ⟨v, hvV⟩)) 0 0 * hpow
  have h1 := congrArg Subtype.val (hYinj hY)
  rw [hxd, autHom_apply_coe] at h1
  have h1' : d * v * d⁻¹ = v := h1
  calc d * v = (d * v * d⁻¹) * d := by group
    _ = v * d := by rw [h1']

theorem orthTorusFixFact : OrthTorusFixFact := by
  intro G _ _ L W S m d w hW hm hS hC2 hd hd3 hw hwS hdw
  by_contra hw1
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hW.le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, -, -, hYint, hP, hline, hy0⟩ := hW.exists_lineCoord hS
  have hw1' : (⟨w, hw⟩ : ↥W) ≠ 1 := fun h0 => hw1 (congrArg Subtype.val h0)
  obtain ⟨h01, h10, h11⟩ := hline ⟨w, hw⟩ hwS
  have hy := hy0 ⟨w, hw⟩ hwS hw1'
  set xd := autHom hLW ⟨d, hd.1⟩ with hxd
  have hxdN : (xd : MulAut ↥W) ∈
      Subgroup.normalizer ((autOn S W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    conjAct_mem_normalizer_autOn ⟨d, hLW hd.1⟩ hd.2
  have hxd10 := upper_of_mem_normalizer ψ hP xd hxdN
  set c := (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have h3 : ψ xd ^ 3 = 1 := by rw [hxd, ← map_pow, pow_three_autHom hLW hd.1 hd3, map_one]
  have hc3 : c ^ 3 = 1 := by
    have h2 := (upper_pow hxd10 3).2
    rw [h3] at h2
    simpa using h2.symm
  have hc1 : c ≠ 1 := by
    intro hc1
    have hU := eq_unipSL_of_upper hxd10 hc1
    have h2 : ψ xd * ψ xd = 1 := by rw [hU]; exact unipSL_mul_self _
    have h4 : ψ xd = 1 := by
      calc ψ xd = ψ xd ^ 3 * (ψ xd * ψ xd)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; group
    have h5 : xd = 1 := ψ.injective (h4.trans (map_one ψ).symm)
    have hdC := mem_centralizer_of_autHom_eq_one hLW h5
    obtain ⟨k, hk⟩ := hC2 ⟨d, hd.1, hdC⟩
    have hk' : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hd3] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hmod : (2 ^ m + 1) % 3 = 2 := by
    obtain ⟨i, rfl⟩ := hm
    rw [← two_mul, pow_mul, Nat.add_mod, Nat.pow_mod]
    norm_num
  have hcq : c * c ^ 2 ^ m = c ^ 2 := by
    rw [← pow_succ', ← Nat.div_add_mod (2 ^ m + 1) 3, hmod,
      pow_add c (3 * ((2 ^ m + 1) / 3)) 2, pow_mul c 3, hc3, one_pow, one_mul]
  have hfix : (xd : MulAut ↥W) ⟨w, hw⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [hxd, autHom_apply_coe]
    exact hdw
  have h1 := hYint xd ⟨w, hw⟩
  rw [hfix] at h1
  have h2 := congrFun (congrFun h1 0) 0
  rw [(twist_upper m hxd10 h01 h10 h11).1, ← hc] at h2
  have h3' : (c ^ 2 - 1) * (Multiplicative.toAdd (Y ⟨w, hw⟩)) 0 0 = 0 := by
    linear_combination (-(Multiplicative.toAdd (Y ⟨w, hw⟩)) 0 0) * hcq - h2
  have hc2 : c ^ 2 ≠ 1 := by
    intro hc2
    apply hc1
    have : c ^ 3 = c ^ 2 * c := by ring
    rw [hc3, hc2, one_mul] at this
    exact this.symm
  exact hy ((mul_eq_zero.mp h3').resolve_left (sub_ne_zero.mpr hc2))

theorem IsOrthCh5.eq_top_of_invariant [Finite G] {L W S : Subgroup G} {m : ℕ}
    (h : IsOrthCh5 L W (2 * m)) (hS : IsSylowTwoOf S L) (M : Subgroup ↥W) (hM : M ≠ ⊥)
    (hLM : ∀ x ∈ autOn L W, ∀ v ∈ M, x v ∈ M) : M = ⊤ := by
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := h.le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, hYherm, hYsurj, hYint, hP, hline, hy0⟩ :=
    h.exists_lineCoord hS
  have := Fintype.ofFinite F
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have h1 := Finite.one_lt_card (α := F)
      rw [hF] at h1
      norm_num at h1
    · exact h0
  have hσ : ∀ x : F, (x ^ 2 ^ m) ^ 2 ^ m = x := fun x => by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hneg : (-1 : F) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    exact CharTwo.add_self_eq_zero 1
  have hPL : autOn S W ≤ autOn L W := A4.autOn_mono hS.1
  have hPS : IsSylowTwoOf (autOn S W) (autOn L W) := Vol2.Ch10.SecD.isSylowTwoOf_autOn hS hLW
  obtain ⟨v, hvM, hv1, hvP⟩ := exists_fixed_of_two hPS.2.1
    (fun v _ => sq_eq_one_of_coord hYinj v) hM (fun q hq v hv => hLM q (hPL hq) v hv)
  have hvS : (v : G) ∈ Subgroup.centralizer (S : Set G) :=
    (mem_centralizer_iff_autOn (hS.1.trans hLW) v).mpr hvP
  obtain ⟨h01, h10, h11⟩ := hline v hvS
  have hy := hy0 v hvS hv1
  have hyq : (Multiplicative.toAdd (Y v)) 0 0 ^ 2 ^ m = (Multiplicative.toAdd (Y v)) 0 0 := by
    have := congrFun (congrFun (hYherm v) 0) 0
    simpa [frobPow, Matrix.transpose_apply] using this
  have hA : ∀ k : F, k ^ 2 ^ m = k → ∃ w ∈ M, Multiplicative.toAdd (Y w) = !![k, 0; 0, 0] := by
    intro k hk
    by_cases hk0 : k = 0
    · refine ⟨1, M.one_mem, ?_⟩
      rw [map_one, toAdd_one, hk0]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · have hr0 : k / (Multiplicative.toAdd (Y v)) 0 0 ≠ 0 := div_ne_zero hk0 hy
      have hrq : (k / (Multiplicative.toAdd (Y v)) 0 0) ^ 2 ^ m =
          k / (Multiplicative.toAdd (Y v)) 0 0 := by
        rw [div_pow, hk, hyq]
      obtain ⟨c, hc, hcr⟩ := exists_pow_add_one_eq hF hr0 hrq
      have hb : ψ (ψ.symm (diagSL hc)) = diagSL hc := MulEquiv.apply_symm_apply _ _
      have hb10 : (ψ (ψ.symm (diagSL hc)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        rw [hb]; simp [coe_diagSL]
      have hb00 : (ψ (ψ.symm (diagSL hc)) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
        rw [hb]; simp [coe_diagSL]
      refine ⟨((ψ.symm (diagSL hc) : ↥(autOn L W)) : MulAut ↥W) v,
        hLM _ (ψ.symm (diagSL hc)).2 v hvM, ?_⟩
      obtain ⟨e00, e01, e10, e11⟩ := twist_upper m hb10 h01 h10 h11
      rw [hYint]
      refine mat2_ext ?_ (by rw [e01]; rfl) (by rw [e10]; rfl) (by rw [e11]; rfl)
      rw [e00, hb00]
      have hN : c * c ^ 2 ^ m = k / (Multiplicative.toAdd (Y v)) 0 0 := by
        rw [← pow_succ', hcr]
      calc c * (Multiplicative.toAdd (Y v)) 0 0 * c ^ 2 ^ m =
          (c * c ^ 2 ^ m) * (Multiplicative.toAdd (Y v)) 0 0 := by ring
        _ = k := by rw [hN, div_mul_cancel₀ k hy]
  have hdetsw : (!![(0 : F), 1; 1, 0]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp [hneg]
  have hB : ∀ k : F, k ^ 2 ^ m = k → ∃ w ∈ M, Multiplicative.toAdd (Y w) = !![0, 0; 0, k] := by
    intro k hk
    obtain ⟨w, hwM, hw⟩ := hA k hk
    set sw : SL(2, F) := ⟨!![0, 1; 1, 0], hdetsw⟩ with hsw
    refine ⟨((ψ.symm sw : ↥(autOn L W)) : MulAut ↥W) w, hLM _ (ψ.symm sw).2 w hwM, ?_⟩
    rw [hYint, MulEquiv.apply_symm_apply, hw]
    exact twist_swap m k
  have hC : ∀ γ : F, ∃ w ∈ M,
      Multiplicative.toAdd (Y w) = !![1, γ ^ 2 ^ m; γ, γ * γ ^ 2 ^ m] := by
    intro γ
    obtain ⟨w, hwM, hw⟩ := hA 1 (one_pow _)
    have hdetl : (!![(1 : F), 0; γ, 1]).det = 1 := by
      rw [Matrix.det_fin_two_of]
      simp
    set l : SL(2, F) := ⟨!![1, 0; γ, 1], hdetl⟩ with hl
    refine ⟨((ψ.symm l : ↥(autOn L W)) : MulAut ↥W) w, hLM _ (ψ.symm l).2 w hwM, ?_⟩
    rw [hYint, MulEquiv.apply_symm_apply, hw]
    exact twist_lower m γ
  rw [eq_top_iff]
  intro w' _
  have hE : ∀ i j, (Multiplicative.toAdd (Y w')) i j ^ 2 ^ m =
      (Multiplicative.toAdd (Y w')) j i := by
    intro i j
    have := congrFun (congrFun (hYherm w') j) i
    simpa [frobPow, Matrix.transpose_apply] using this
  obtain ⟨w₁, hw₁M, hw₁⟩ := hA ((Multiplicative.toAdd (Y w')) 0 0) (hE 0 0)
  obtain ⟨w₂, hw₂M, hw₂⟩ := hB ((Multiplicative.toAdd (Y w')) 1 1) (hE 1 1)
  obtain ⟨w₃, hw₃M, hw₃⟩ := hC ((Multiplicative.toAdd (Y w')) 1 0)
  obtain ⟨w₄, hw₄M, hw₄⟩ := hA 1 (one_pow _)
  have hN : ((Multiplicative.toAdd (Y w')) 1 0 * (Multiplicative.toAdd (Y w')) 1 0 ^ 2 ^ m) ^
      2 ^ m = (Multiplicative.toAdd (Y w')) 1 0 * (Multiplicative.toAdd (Y w')) 1 0 ^ 2 ^ m := by
    rw [mul_pow, hσ, mul_comm]
  obtain ⟨w₅, hw₅M, hw₅⟩ := hB _ hN
  have hγq := hE 1 0
  have hw' : w' = w₁ * w₂ * w₃ * w₄⁻¹ * w₅⁻¹ := by
    apply hYinj
    apply Multiplicative.toAdd.injective
    rw [map_mul Y, map_mul Y, map_mul Y, map_mul Y, map_inv Y, map_inv Y, toAdd_mul, toAdd_mul,
      toAdd_mul, toAdd_mul, toAdd_inv, toAdd_inv, hw₁, hw₂, hw₃, hw₄, hw₅]
    refine mat2_ext ?_ ?_ ?_ ?_ <;> simp [hγq]
  rw [hw']
  exact M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem hw₁M hw₂M) hw₃M) (M.inv_mem hw₄M))
    (M.inv_mem hw₅M)

theorem orthOddGalFact : OrthOddGalFact := by
  intro G _ _ L T V R n d hV hn4 hT hTL hTV hS hC hd hd3 hRT hdR
  obtain ⟨m, hm2, -⟩ := id hV
  subst hm2
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have hm1 : 1 ≤ m := hmodd.pos
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, -, hYsurj, -, hP, -, -⟩ := hV.exists_lineCoord hS
  set xd := autHom hLV ⟨d, hd.1⟩ with hxd
  have hxdN : (xd : MulAut ↥V) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    conjAct_mem_normalizer_autOn ⟨d, hLV hd.1⟩ hd.2
  have hxd10 := upper_of_mem_normalizer ψ hP xd hxdN
  set c := (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have h3 : ψ xd ^ 3 = 1 := by rw [hxd, ← map_pow, pow_three_autHom hLV hd.1 hd3, map_one]
  have hc3 : c ^ 3 = 1 := by
    have h2 := (upper_pow hxd10 3).2
    rw [h3] at h2
    simpa using h2.symm
  have hc1 : c ≠ 1 := by
    intro hc1
    have hU := eq_unipSL_of_upper hxd10 hc1
    have h2 : ψ xd * ψ xd = 1 := by rw [hU]; exact unipSL_mul_self _
    have h4 : ψ xd = 1 := by
      calc ψ xd = ψ xd ^ 3 * (ψ xd * ψ xd)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; group
    have h5 : xd = 1 := ψ.injective (h4.trans (map_one ψ).symm)
    have hdC := mem_centralizer_of_autHom_eq_one hLV h5
    have hdT : d ∈ T := hC ⟨(le_sup_left : L ≤ L ⊔ T) hd.1, hdC⟩
    obtain ⟨k, hk⟩ := hT ⟨d, hdT⟩
    have hk' : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hd3] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  intro r hr
  have hrT := hRT hr
  set τ : Subgroup.normalizer ((autOn L V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    ⟨conjAct V ⟨r, hTV hrT⟩, conjAct_mem_normalizer_autOn ⟨r, hTV hrT⟩ (hTL hrT)⟩ with hτ
  have hτP : (τ : MulAut ↥V) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    conjAct_mem_normalizer_autOn ⟨r, hTV hrT⟩ (mem_normalizer_inf hrT (hTL hrT))
  obtain ⟨h, σ, hh, hασ, hσN⟩ :=
    exists_upper_of_normalizes (n := 2 * m) (by omega) hF ψ hP τ hτP
  have hrdL : r * d * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL hrT) d).mp hd.1
  have hrd : r * d * r⁻¹ * d⁻¹ ∈ T ⊓ L := by
    refine Subgroup.mem_inf.mpr ⟨hRT ?_, mul_mem hrdL (inv_mem (Subgroup.mem_inf.mp hd).1)⟩
    have h1 : d * r⁻¹ * d⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hdR r⁻¹).mp (inv_mem hr)
    have h2 := mul_mem hr h1
    have e : r * (d * r⁻¹ * d⁻¹) = r * d * r⁻¹ * d⁻¹ := by group
    rwa [e] at h2
  set xrd := autHom hLV ⟨r * d * r⁻¹, hrdL⟩ with hxrd
  have hxrd' : (xrd : MulAut ↥V) = (τ : MulAut ↥V) * xd * (τ : MulAut ↥V)⁻¹ := by
    rw [hxrd, hxd]
    change conjAct V ⟨r * d * r⁻¹, _⟩ = conjAct V ⟨r, hTV hrT⟩ * conjAct V ⟨d, _⟩ *
      (conjAct V ⟨r, hTV hrT⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hψrd : ψ xrd = h * Matrix.SpecialLinearGroup.map σ.toRingHom (ψ xd) * h⁻¹ := by
    have : xrd = (autOn L V).normalizerMonoidHom τ xd := by
      apply Subtype.ext
      rw [hxrd', Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [this, hασ]
  obtain ⟨e1, e2⟩ := upper_conj_map σ hh hxd10
  rw [← hψrd] at e1 e2
  rw [← hc] at e2
  have hxeq : xrd * xd⁻¹ = autHom hLV ⟨r * d * r⁻¹ * d⁻¹, hrd.2⟩ := by
    rw [hxrd, hxd, ← map_inv, ← map_mul]
    rfl
  have hmem : ((xrd * xd⁻¹ : ↥(autOn L V)) : MulAut ↥V) ∈ autOn (T ⊓ L) V := by
    rw [hxeq]
    exact mem_autOn_iff.mpr ⟨⟨r * d * r⁻¹ * d⁻¹, hLV hrd.2⟩, hrd, rfl⟩
  obtain ⟨b, hb⟩ := (hP _).mp hmem
  rw [map_mul, map_inv] at hb
  obtain ⟨f1, f2⟩ := upper_inv hxd10
  obtain ⟨g1, g2⟩ := upper_mul e1 f1
  have h00 : ((ψ xrd * (ψ xd)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [hb]
    simp [coe_unipSL]
  rw [g2, e2, f2] at h00
  have hdet := upper_det hxd10
  rw [← hc] at hdet
  have hσc : σ c = c := by
    have hx11 : (ψ xd : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
    exact mul_right_cancel₀ hx11 (h00.trans hdet.symm)
  obtain ⟨k, hk⟩ := hT ⟨r, hrT⟩
  have hrk : (⟨r, hTV hrT⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hτk : τ ^ 2 ^ k = 1 := by
    apply Subtype.ext
    change (conjAct V ⟨r, hTV hrT⟩) ^ 2 ^ k = 1
    rw [← map_pow, hrk, map_one]
  have hσk : σ ^ 2 ^ k = 1 := hσN _ hτk
  have hcardAut : Nat.card (RingAut F) = 2 * m := (ringAut_card_and_cyclic hF).1
  have : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hσn : σ ^ (2 * m) = 1 := by
    rw [← hcardAut]
    exact pow_card_eq_one'
  have hσ2 : σ ^ 2 = 1 := by
    have hg : σ ^ Nat.gcd (2 ^ k) (2 * m) = 1 := pow_gcd_eq_one.mpr ⟨hσk, hσn⟩
    have hdvd : Nat.gcd (2 ^ k) (2 * m) ∣ 2 := by
      obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ k) (2 * m))
      have h2m := Nat.gcd_dvd_right (2 ^ k) (2 * m)
      rw [ha] at h2m ⊢
      rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · interval_cases a <;> norm_num
      · exfalso
        have h4 : 2 ^ 2 ∣ 2 * m := (pow_dvd_pow 2 ha2).trans h2m
        obtain ⟨t, ht⟩ := hmodd
        rw [ht] at h4
        norm_num at h4
        omega
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, pow_mul, hg, one_pow]
  have hσ1 : σ = 1 := by
    by_contra hne
    obtain ⟨s, -, hs, hσs, -⟩ :=
      finite_field_involution_exact (n := 2 * m) (by omega) hF σ hσ2 hne
    have hsm : s = m := by omega
    rw [hσs, hsm, pow_two_pow_eq_sq_of_odd hc3 hmodd] at hσc
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0] at hc3
      norm_num at hc3
    apply hc1
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hσc, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0)
  set e := ψ.symm h with he
  have hconj : ∀ y : ↥(autOn L V), (autOn L V).normalizerMonoidHom τ y = e * y * e⁻¹ := by
    intro y
    apply ψ.injective
    rw [hασ, hσ1, map_mul, map_mul, map_inv, he, MulEquiv.apply_symm_apply]
    congr 2
  set z : MulAut ↥V := ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (τ : MulAut ↥V) with hz
  have hzc : ∀ y : ↥(autOn L V), z * (y : MulAut ↥V) = (y : MulAut ↥V) * z := by
    intro y
    have h1 := congrArg Subtype.val (hconj y)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hz]
    calc ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (τ : MulAut ↥V) * (y : MulAut ↥V) =
        ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ *
          ((τ : MulAut ↥V) * (y : MulAut ↥V) * (τ : MulAut ↥V)⁻¹) * (τ : MulAut ↥V) := by group
      _ = ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (((e : ↥(autOn L V)) : MulAut ↥V) *
          (y : MulAut ↥V) * ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹) * (τ : MulAut ↥V) := by
            rw [h1]
      _ = (y : MulAut ↥V) * (((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (τ : MulAut ↥V)) := by group
  have hτN : (τ : MulAut ↥V) ^ 2 ^ k = 1 := congrArg Subtype.val hτk
  have hez : Commute ((e : ↥(autOn L V)) : MulAut ↥V) z := (hzc e).symm
  have hτez : (τ : MulAut ↥V) = ((e : ↥(autOn L V)) : MulAut ↥V) * z := by
    rw [hz]
    group
  have heN : ((e : ↥(autOn L V)) : MulAut ↥V) ^ 2 ^ k * z ^ 2 ^ k = 1 := by
    rw [← hez.mul_pow, ← hτez, hτN]
  have heN1 : e ^ 2 ^ k = 1 := by
    have hcent : ψ (e ^ 2 ^ k) ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := ψ.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, eq_inv_of_mul_eq_one_left heN]
      exact ((Commute.pow_left (hzc y) (2 ^ k)).inv_left).eq.symm
    exact ψ.injective ((eq_one_of_mem_center hcent).trans (map_one ψ).symm)
  have hzN : z ^ 2 ^ k = 1 := by
    have h1 : ((e : ↥(autOn L V)) : MulAut ↥V) ^ 2 ^ k = 1 := by
      rw [← Subgroup.coe_pow, heN1, Subgroup.coe_one]
    rw [h1, one_mul] at heN
    exact heN
  have hV1 : ∃ v : ↥V, v ≠ 1 := by
    have h0 : (0 : F) ^ 2 ^ m = 0 := zero_pow (by positivity)
    obtain ⟨w, hw⟩ := hYsurj !![1, 0; 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [frobPow, Matrix.transpose_apply, h0])
    refine ⟨w, fun hw1 => ?_⟩
    rw [hw1, map_one, toAdd_one] at hw
    have := congrFun (congrFun hw 0) 0
    simp at this
  have hz1 : z = 1 := by
    let M : Subgroup ↥V :=
      { carrier := {v | z v = v}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_mul, ha, hb]
        one_mem' := map_one z
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq] at ha ⊢
          rw [map_inv, ha] }
    have hQ : IsPGroup 2 (Subgroup.zpowers z) := by
      rintro ⟨g, hg⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzN, one_zpow]
    have htop : (⊤ : Subgroup ↥V) ≠ ⊥ := by
      obtain ⟨v₀, hv₀⟩ := hV1
      intro htb
      have : v₀ ∈ (⊥ : Subgroup ↥V) := htb ▸ Subgroup.mem_top v₀
      exact hv₀ (Subgroup.mem_bot.mp this)
    obtain ⟨v, -, hv1, hv⟩ := exists_fixed_of_two hQ (M := ⊤)
      (fun v _ => sq_eq_one_of_coord hYinj v) htop (fun _ _ _ _ => Subgroup.mem_top _)
    have hM : M ≠ ⊥ := by
      intro hbot
      have hvM : v ∈ M := hv z (Subgroup.mem_zpowers z)
      rw [hbot] at hvM
      exact hv1 (Subgroup.mem_bot.mp hvM)
    have hLM : ∀ x ∈ autOn L V, ∀ v ∈ M, x v ∈ M := by
      intro x hx v hv
      have hzx := hzc ⟨x, hx⟩
      have hv' : z v = v := hv
      show z (x v) = x v
      calc z (x v) = (z * x) v := rfl
        _ = (x * z) v := by rw [hzx]
        _ = x (z v) := rfl
        _ = x v := by rw [hv']
    have hMtop := hV.eq_top_of_invariant hS M hM hLM
    refine MulEquiv.ext fun v => ?_
    have hvM : v ∈ M := by
      rw [hMtop]
      exact Subgroup.mem_top v
    rw [MulAut.one_apply]
    exact hvM
  have hτe : (τ : MulAut ↥V) = ((e : ↥(autOn L V)) : MulAut ↥V) := by
    rw [hτez, hz1, mul_one]
  have hhN : h ^ 2 ^ k = 1 := by
    have := congrArg ψ heN1
    rw [map_pow, map_one, he, MulEquiv.apply_symm_apply] at this
    exact this
  have hh00 : (h : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    apply eq_one_of_pow_two_pow_eq_one (f := k)
    have := (upper_pow hh (2 ^ k)).2
    rw [hhN] at this
    simpa using this.symm
  have hU := eq_unipSL_of_upper hh hh00
  have heP : ((e : ↥(autOn L V)) : MulAut ↥V) ∈ autOn (T ⊓ L) V :=
    (hP e).mpr ⟨(h : Matrix (Fin 2) (Fin 2) F) 0 1, by
      rw [he, MulEquiv.apply_symm_apply]
      exact hU⟩
  rw [← hτe] at heP
  obtain ⟨p, hp, hpτ⟩ := mem_autOn_iff.mp heP
  have hcent := inv_mul_mem_centralizer (p := p) (c := ⟨r, hTV hrT⟩) hpτ
  have hcent' : (p : G)⁻¹ * r ∈ Subgroup.centralizer (V : Set G) := by
    simpa using hcent
  have hpr : (p : G)⁻¹ * r ∈ T := mul_mem (inv_mem hp.1) hrT
  have hrp : r = (p : G) * ((p : G)⁻¹ * r) := by group
  rw [hrp]
  exact mul_mem ((le_sup_left : T ⊓ L ≤ (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) hp)
    ((le_sup_right : T ⊓ Subgroup.centralizer (V : Set G) ≤ _) ⟨hpr, hcent'⟩)

end CFSG.Quasithin.H13
