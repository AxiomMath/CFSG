module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise
open Matrix

theorem s16c1_isSL2Prime_of_equiv {X X' : Type} [Group X] [Group X'] {p : ℕ}
    (h : IsSL2Prime X p) (e : X ≃* X') : IsSL2Prime X' p := by
  obtain ⟨K, hK, hKf, hc, ⟨f⟩⟩ := h
  exact ⟨K, hK, hKf, hc, ⟨e.symm.trans f⟩⟩

private theorem s16c1_transvection_pow {F : Type*} [Field F] {i j : Fin 2} (hij : i ≠ j) (b : F)
    (n : ℕ) :
    (SpecialLinearGroup.transvection hij b) ^ n =
      SpecialLinearGroup.transvection hij (n • b) := by
  induction n with
  | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
  | succ n ih =>
      rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add]
      congr 1
      rw [succ_nsmul]

theorem s16c1_sl2five_facts {X : Type} [Group X] (h : IsSL2Prime X 5) :
    Nat.card X = 120 ∧ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ ∧
      ∃ u t g : X, orderOf u = 5 ∧ t * u * t⁻¹ = u⁻¹ ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  classical
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hchar : CharP K 5 :=
    charP_of_card_eq_prime (p := 5) (by simpa [Nat.card_eq_fintype_card] using hKcard)
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h2 : (2 : K) ≠ 0 := by
    intro h2z
    have := (CharP.cast_eq_zero_iff K 5 2).mp h2z
    norm_num at this
  have h4 : (4 : K) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    have : (4 : K) + 1 = (5 : K) := by norm_num
    rw [this, h5]
  have h2sq : (2 : K) ^ 2 = -1 := by
    have : (2 : K) ^ 2 = (4 : K) := by norm_num
    rw [this, h4]
  let E : X ≃* SpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have hcardX : Nat.card X = 120 := by
    rw [Nat.card_congr E.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL 2 K,
      CFSG.Open.StatedAPI.card_statedSL_two K, hKcard]
    norm_num
  have h4K : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨x⟩ := (Fintype.card_pos_iff (α := K)).mp
      (by rw [← Nat.card_eq_fintype_card, hKcard]; norm_num)
    refine ⟨Finset.univ.erase x, ?_⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      show Fintype.card K = 5 by simpa [Nat.card_eq_fintype_card] using hKcard]
  have hcommSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect h4K).commutator_eq_top
  have hperfX : commutator X = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hx : E x ∈ commutator (SpecialLinearGroup (Fin 2) K) := by rw [hcommSL]; trivial
    have hmap : (commutator X).map E.toMonoidHom =
        commutator (SpecialLinearGroup (Fin 2) K) := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ E.surjective, ← _root_.commutator_def]
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    exact (E.injective hyx) ▸ hy
  refine ⟨hcardX, ?_, ?_⟩
  · show commutator X = ⊤
    exact hperfX
  ·
    let hij : (0 : Fin 2) ≠ 1 := zero_ne_one
    let u' : SpecialLinearGroup (Fin 2) K := SpecialLinearGroup.transvection hij (1 : K)
    let t' : SpecialLinearGroup (Fin 2) K := SpecialLinearGroup.diag2 (2 : K) h2
    let g' : SpecialLinearGroup (Fin 2) K :=
      ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; norm_num⟩
    have hu'5 : u' ^ 5 = 1 := by
      change (SpecialLinearGroup.transvection hij (1 : K)) ^ 5 = 1
      rw [s16c1_transvection_pow,
        show (5 : ℕ) • (1 : K) = 0 by rw [nsmul_eq_mul, mul_one]; exact h5,
        SpecialLinearGroup.transvection_coeff_zero]
    have hu'1 : u' ≠ 1 := by
      intro hcone
      have hcenter : u' ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
        rw [hcone]; exact Subgroup.one_mem _
      rw [show u' = SpecialLinearGroup.transvection hij (1 : K) from rfl,
        SpecialLinearGroup.transvection_mem_center_iff] at hcenter
      exact one_ne_zero hcenter
    have hu' : orderOf u' = 5 := orderOf_eq_prime hu'5 hu'1
    have ht' : t' * u' * t'⁻¹ = u'⁻¹ := by
      have hcomm :=
        Matrix.commutator_diag2_transvection (2 : K) h2 (1 : K) ((1 : K) * ((2 : K) ^ 2 - 1))
          rfl
      rw [show t' * u' * t'⁻¹ = MulAut.conj t' u' from (MulAut.conj_apply t' u').symm,
        conj_eq_commutatorElement_mul,
        show t' = SpecialLinearGroup.diag2 (2 : K) h2 from rfl,
        show u' = SpecialLinearGroup.transvection hij (1 : K) from rfl, hcomm]
      rw [show u'⁻¹ = SpecialLinearGroup.transvection hij (-1 : K) from by
            rw [show u' = SpecialLinearGroup.transvection hij (1 : K) from rfl]
            exact SpecialLinearGroup.transvection_inv hij 1,
        ← SpecialLinearGroup.transvection_add]
      congr 1
      rw [one_mul, sub_add_cancel, h2sq]
    let φ : Multiplicative K →* SpecialLinearGroup (Fin 2) K :=
      { toFun := fun c => SpecialLinearGroup.transvection hij (Multiplicative.toAdd c)
        map_one' := by
          rw [show Multiplicative.toAdd (1 : Multiplicative K) = 0 from rfl,
            SpecialLinearGroup.transvection_coeff_zero]
        map_mul' := fun a b => by
          rw [toAdd_mul, SpecialLinearGroup.transvection_add] }
    let U : Subgroup (SpecialLinearGroup (Fin 2) K) := φ.range
    have hu'U : u' ∈ U := by
      refine ⟨Multiplicative.ofAdd 1, ?_⟩
      change SpecialLinearGroup.transvection hij
        (Multiplicative.toAdd (Multiplicative.ofAdd 1)) =
        SpecialLinearGroup.transvection hij (1 : K)
      rw [toAdd_ofAdd]
    have hleU : Subgroup.zpowers u' ≤ U := Subgroup.zpowers_le.mpr hu'U
    have hnotU : g' * u' * g'⁻¹ ∉ U := by
      rintro ⟨c, hc⟩
      have hg'M : g'.val = !![0, 1; -1, 0] := rfl
      have hu'M : u'.val = !![1, 1; 0, 1] := by
        rw [show u' = SpecialLinearGroup.transvection hij (1 : K) from rfl,
          SpecialLinearGroup.transvection_coe]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Pi.single_apply]
      have hg'inv : (g'⁻¹).val = !![0, -1; 1, 0] := by
        simp [SpecialLinearGroup.coe_inv, hg'M, Matrix.adjugate_fin_two_of]
      have hgug : g' * u' * g'⁻¹ =
          SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (-1 : K) := by
        apply Subtype.ext
        change g'.val * u'.val * (g'⁻¹).val =
          (1 : Matrix (Fin 2) (Fin 2) K) + Matrix.single (1 : Fin 2) 0 (-1 : K)
        rw [hg'M, hu'M, hg'inv]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp_rw [Matrix.mul_fin_two] <;>
          simp [Matrix.one_apply, Pi.single_apply] <;>
          ring_nf
      have h1 : ((g' * u' * g'⁻¹ : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 1 0 = -1 := by
        rw [hgug, SpecialLinearGroup.transvection_coe]
        simp [Matrix.one_apply, Pi.single_apply]
      have h2c : ((φ c : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
        change ((SpecialLinearGroup.transvection hij (Multiplicative.toAdd c) :
          SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
        rw [SpecialLinearGroup.transvection_coe]
        simp [Matrix.one_apply, Pi.single_apply]
      rw [← hc] at h1
      rw [h2c] at h1
      exact one_ne_zero (neg_eq_zero.mp h1.symm)
    have hgu' : g' * u' * g'⁻¹ ∉ Subgroup.zpowers u' := fun hmem => hnotU (hleU hmem)
    refine ⟨E.symm u', E.symm t', E.symm g', ?_, ?_, ?_⟩
    · rw [E.symm.orderOf_eq u', hu']
    · have h := congrArg E.symm ht'
      simpa using h
    · intro hmem
      have h := Subgroup.mem_map_of_mem E.toMonoidHom hmem
      rw [MonoidHom.map_zpowers] at h
      exact hgu' (by simpa using h)

private theorem s16c1_conj_eq_self_of_prime {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {Z : Subgroup Y} [Z.Normal] {u : Y} (hu : orderOf u = p) (hZ : Nat.card Z = p) :
    ∀ z ∈ Z, u * z * u⁻¹ = z := by
  intro z hz
  let G' := ↥(Subgroup.zpowers u)
  have hcardG' : Nat.card G' = p := by rw [Nat.card_zpowers, hu]
  have hP : IsPGroup p G' := IsPGroup.of_card (n := 1) (by rw [pow_one, hcardG'])
  let ψ : G' →* MulAut ↥Z :=
    (MulAut.conjNormal (H := Z)).comp (Subgroup.zpowers u).subtype
  letI : MulAction G' ↥Z := MulAction.compHom ↥Z ψ
  have hmod := hP.card_modEq_card_fixedPoints ↥Z
  have hF0 : Nat.card (MulAction.fixedPoints G' ↥Z) ≡ 0 [MOD p] := by
    have h := hmod.symm
    rw [hZ] at h
    exact h.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p))
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints G' ↥Z) := Nat.modEq_zero_iff_dvd.mp hF0
  have h1fix : (1 : ↥Z) ∈ MulAction.fixedPoints G' ↥Z := by
    rw [MulAction.mem_fixedPoints]
    intro w
    exact map_one (ψ w)
  have hpos : 0 < Nat.card (MulAction.fixedPoints G' ↥Z) := by
    haveI : Nonempty ↥(MulAction.fixedPoints G' ↥Z) := ⟨⟨1, h1fix⟩⟩
    exact Nat.card_pos
  have hle : Nat.card (MulAction.fixedPoints G' ↥Z) ≤ p := by
    rw [← hZ]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hF : Nat.card (MulAction.fixedPoints G' ↥Z) = p :=
    le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  have hbij : Function.Bijective (Subtype.val : ↥(MulAction.fixedPoints G' ↥Z) → ↥Z) :=
    Subtype.val_injective.bijective_of_nat_card_le (by rw [hF, hZ])
  have hzfix : (⟨z, hz⟩ : ↥Z) ∈ MulAction.fixedPoints G' ↥Z := by
    obtain ⟨y, hy⟩ := hbij.2 ⟨z, hz⟩
    rw [← hy]
    exact y.2
  have hfix : (MulAut.conjNormal (H := Z) u) (⟨z, hz⟩ : ↥Z) = ⟨z, hz⟩ := by
    have h := (MulAction.mem_fixedPoints.mp hzfix) (⟨u, Subgroup.mem_zpowers u⟩ : G')
    simp only [ψ, MulAction.compHom_smul_def, MonoidHom.comp_apply] at h
    exact h
  simpa [MulAut.conjNormal_apply] using congrArg Subtype.val hfix

private theorem s16c1_mulAut_prime_comm {Z : Type*} [Group Z] {p : ℕ} [Fact p.Prime]
    (hZ : Nat.card Z = p) (α β : MulAut Z) : α * β = β * α := by
  have hcyc : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨z0, hz0⟩ := IsCyclic.exists_generator (α := Z)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hz0 (β z0))
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hz0 (α z0))
  have key : α (β z0) = β (α z0) := by
    rw [← hj, ← hi, map_zpow α z0 j, ← hi, map_zpow β z0 i, ← hj,
      ← zpow_mul z0 i j, ← zpow_mul z0 j i, mul_comm]
  apply MulEquiv.ext
  intro z
  show α (β z) = β (α z)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hz0 z)
  rw [map_zpow β z0 n, map_zpow α (β z0) n, map_zpow α z0 n, map_zpow β (α z0) n, key]

private theorem s16c1_mulAut_eq_one_of_pow_prime {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : Nat.card Q = p) (σ : MulAut Q) (hσ : σ ^ p = 1) : σ = 1 := by
  let G := ↥(Subgroup.zpowers σ)
  have hP : IsPGroup p G := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hσ
  letI : MulAction G Q := MulAction.compHom Q (Subgroup.zpowers σ).subtype
  have hmod := hP.card_modEq_card_fixedPoints Q
  have hFix1 : (1 : Q) ∈ MulAction.fixedPoints G Q := by
    rw [MulAction.mem_fixedPoints]
    intro w
    exact map_one ((w : G) : MulAut Q)
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints G Q) := by
    have h : Nat.card (MulAction.fixedPoints G Q) ≡ 0 [MOD p] := by
      have hp : (p : ℕ) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)
      exact hmod.symm.trans (by rw [hQ]; exact hp)
    exact Nat.modEq_zero_iff_dvd.mp h
  have hpos : 1 ≤ Nat.card (MulAction.fixedPoints G Q) := by
    haveI : Nonempty ↥(MulAction.fixedPoints G Q) := ⟨⟨1, hFix1⟩⟩
    have h : 0 < Nat.card (MulAction.fixedPoints G Q) := Nat.card_pos
    omega
  have hle : Nat.card (MulAction.fixedPoints G Q) ≤ p := by
    rw [← hQ]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hFix : Nat.card (MulAction.fixedPoints G Q) = p :=
    Nat.le_antisymm hle (Nat.le_of_dvd (by omega) hdvd)
  have hbij : Function.Bijective (Subtype.val : ↥(MulAction.fixedPoints G Q) → Q) :=
    Subtype.val_injective.bijective_of_nat_card_le (by rw [hFix, hQ])
  apply MulEquiv.ext
  intro q
  have hq : q ∈ MulAction.fixedPoints G Q := by
    obtain ⟨y, hy⟩ := hbij.2 q
    rw [← hy]
    exact y.2
  have hfix := (MulAction.mem_fixedPoints.mp hq) (⟨σ, Subgroup.mem_zpowers σ⟩ : G)
  change σ q = q
  rw [MulAction.compHom_smul_def] at hfix
  exact hfix

private theorem s16c1_perfect_centralizes {Y : Type} [Group Y] {p : ℕ} [Fact p.Prime]
    {Z S : Subgroup Y} [Z.Normal] (hZ : Nat.card Z = p)
    (hS : ⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆ = ⊤) :
    ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ = z := by
  intro s hs z hz
  let ψ : ↥S →* MulAut ↥Z := (MulAut.conjNormal (H := Z)).comp S.subtype
  have hle : ⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (s16c1_mulAut_prime_comm hZ _ _)
  have hψ : ψ ⟨s, hs⟩ = 1 := by
    have h : (⟨s, hs⟩ : ↥S) ∈ ψ.ker := hle (by rw [hS]; exact Subgroup.mem_top _)
    exact h
  have h := congrArg (fun f : MulAut ↥Z => (f ⟨z, hz⟩ : ↥Z).val) hψ
  simpa [ψ, MulAut.conjNormal_apply] using h

private theorem s16c1_neg_branch {Y : Type} [Group Y] [Finite Y] {N Z L : Subgroup Y}
    [N.Normal] {u t : Y}
    (hZcent : ∀ z ∈ Z, ∀ n ∈ N, z * n = n * z)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Z)
    (hZtriv : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n ∈ Z)
    (hexp : ∀ n ∈ N, n ^ 5 = 1)
    (hcardN : Nat.card N = 5 ^ 3) (hcardL : Nat.card L = 5 ^ 2)
    (hZL : Z ≤ L) (hLN : L ≤ N)
    (hLdef : ∀ b, b ∈ L ↔ b ∈ N ∧ ⁅u, b⁆ ∈ Z)
    (huZ : ∀ z ∈ Z, u * z * u⁻¹ = z) (htZ : ∀ z ∈ Z, t * z * t⁻¹ = z)
    (htu : t * u * t⁻¹ = u⁻¹)
    (hNL : ∀ e ∈ N, ⁅u, e⁆ ∈ L)
    (hker : ∀ x ∈ L, ⁅u, x⁆ = 1 → x ∈ Z)
    (hy : ∃ y ∈ L, y ∉ Z) : False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hconj : ∀ z ∈ Z, ∀ n ∈ N, n * z * n⁻¹ = z := fun z hz n hn => by
    rw [← hZcent z hz n hn, mul_inv_cancel_right]
  have huZ' : ∀ z ∈ Z, u⁻¹ * z * u = z := fun z hz => by
    calc u⁻¹ * z * u = u⁻¹ * (u * z * u⁻¹) * u := by rw [huZ z hz]
      _ = z := by group
  have htu' : t * u⁻¹ * t⁻¹ = u := by
    rw [show t * u⁻¹ * t⁻¹ = (t * u * t⁻¹)⁻¹ by group, htu, inv_inv]
  have hcore : ∀ x : Y, ⁅u, t * x * t⁻¹⁆ = t * ⁅u⁻¹, x⁆ * t⁻¹ := by
    intro x
    have h := conjugate_commutatorElement u⁻¹ x t
    rw [htu'] at h
    exact h.symm
  have hux : ∀ x : Y, u * x * u⁻¹ = ⁅u, x⁆ * x := fun x => by
    rw [commutatorElement_def]; group
  have aux1 : ∀ x a : Y, u * x * u⁻¹ = a * x → u⁻¹ * x * u = (u⁻¹ * a * u)⁻¹ * x := by
    intro x a h
    calc u⁻¹ * x * u = (u⁻¹ * a * u)⁻¹ * (u⁻¹ * (a * x) * u) := by group
      _ = (u⁻¹ * a * u)⁻¹ * (u⁻¹ * (u * x * u⁻¹) * u) := by rw [h]
      _ = (u⁻¹ * a * u)⁻¹ * x := by group
  have step1 : ∀ x ∈ L, u⁻¹ * x * u = ⁅u, x⁆⁻¹ * x := by
    intro x hx
    have hcZ : ⁅u, x⁆ ∈ Z := ((hLdef x).1 hx).2
    rw [aux1 x _ (hux x), huZ' _ hcZ]
  have hTN : ∀ x ∈ N, t * x * t⁻¹ ∈ N := fun x hx => (inferInstance : N.Normal).conj_mem x hx t
  have step2 : ∀ x ∈ L, ⁅u, t * x * t⁻¹⁆ = ⁅u, x⁆⁻¹ := by
    intro x hx
    have hcZ : ⁅u, x⁆ ∈ Z := ((hLdef x).1 hx).2
    have h3 : ⁅u⁻¹, x⁆ = ⁅u, x⁆⁻¹ := by
      rw [commutatorElement_def, inv_inv, step1 x hx, mul_inv_cancel_right]
    rw [hcore x, h3]
    exact htZ _ (Z.inv_mem hcZ)
  have hTL : ∀ x ∈ L, t * x * t⁻¹ ∈ L := fun x hx => by
    refine (hLdef _).2 ⟨hTN x (hLN hx), ?_⟩
    rw [step2 x hx]
    exact Z.inv_mem ((hLdef x).1 hx).2
  have step3 : ∀ x ∈ L, t * x * t⁻¹ * x ∈ Z := by
    intro x hx
    have hx' := hTL x hx
    have hcZ : ⁅u, x⁆ ∈ Z := ((hLdef x).1 hx).2
    apply hker _ (L.mul_mem hx' hx)
    rw [commutatorElement_mul_right_eq_mul_conj, step2 x hx]
    calc ⁅u, x⁆⁻¹ * (t * x * t⁻¹) * ⁅u, x⁆ * (t * x * t⁻¹)⁻¹
        = ⁅u, x⁆⁻¹ * ((t * x * t⁻¹) * ⁅u, x⁆ * (t * x * t⁻¹)⁻¹) := by group
      _ = 1 := by rw [hconj _ hcZ _ (hLN hx')]; group
  have hZN : Z ≤ N := hZL.trans hLN
  have hLcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) hcardL
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : L) ⟨b, hb⟩)
  obtain ⟨y, hyL, hyZ⟩ := hy
  have hyN : y ∈ N := hLN hyL
  have hCL : ∀ p ∈ N, ⁅p, y⁆ = 1 → p ∈ L := by
    intro p hpN hpy
    let C : Subgroup Y := N ⊓ Subgroup.centralizer {y}
    have hLC : L ≤ C := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨hLN hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hLcomm _ hyL x hx
    have hCN : C ≤ N := inf_le_left
    have hCne : C ≠ N := by
      intro hCeq
      apply hyZ
      refine hZtriv y hyN fun m hm => ?_
      have hmC : m ∈ C := by rw [hCeq]; exact hm
      exact ((Subgroup.mem_centralizer_iff.mp hmC.2) y (Set.mem_singleton y))
    have hd1 : 5 ^ 2 ∣ Nat.card C := hcardL ▸ Subgroup.card_dvd_of_le hLC
    have hd2 : Nat.card C ∣ 5 ^ 3 := hcardN ▸ Subgroup.card_dvd_of_le hCN
    obtain ⟨k, hk⟩ := hd1
    have hk5 : k ∣ 5 := by
      rw [hk] at hd2
      have h25 : 5 ^ 2 * k ∣ 5 ^ 2 * 5 := by simpa using hd2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h25
    rcases (Nat.dvd_prime Nat.prime_five).1 hk5 with h1 | h5
    · have hC : Nat.card C = 5 ^ 2 := by rw [hk, h1]; norm_num
      have hLeqC : L = C := Subgroup.eq_of_le_of_card_ge hLC (by rw [hC, hcardL])
      rw [hLeqC]
      refine Subgroup.mem_inf.mpr ⟨hpN, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp hpy).symm
    · exfalso
      apply hCne
      exact Subgroup.eq_of_le_of_card_ge hCN (by rw [hcardN, hk, h5]; norm_num)
  have hbil : ∀ m ∈ N, ∀ z ∈ Z, ⁅m, z * y⁻¹⁆ = ⁅m, y⁆⁻¹ := by
    intro m hm z hz
    have hzN : z ∈ N := hZN hz
    have hymZ : ⁅y, m⁆ ∈ Z := hcomm y hyN m hm
    have h1 : ⁅m, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZcent z hz m hm).symm
    rw [commutatorElement_mul_right_eq_mul_conj, h1, one_mul,
      hconj _ (hcomm m hm y⁻¹ (N.inv_mem hyN)) z hzN, commutatorElement_inv_right]
    have h2 := hconj _ hymZ y⁻¹ (N.inv_mem hyN)
    rw [inv_inv] at h2
    rw [h2, commutatorElement_inv]
  have step5 : ∀ n ∈ N, t * n * t⁻¹ * n ∈ L := by
    intro n hn
    have hn' := hTN n hn
    obtain ⟨z₁, hz₁, hy'⟩ : ∃ z₁ ∈ Z, t * y * t⁻¹ = z₁ * y⁻¹ :=
      ⟨t * y * t⁻¹ * y, step3 y hyL, by group⟩
    have hmy : ⁅n, y⁆ ∈ Z := hcomm n hn y hyN
    have hα : ⁅t * n * t⁻¹, t * y * t⁻¹⁆ = ⁅n, y⁆ := by
      rw [← conjugate_commutatorElement n y t]
      exact htZ _ hmy
    have hkey : ⁅t * n * t⁻¹, y⁆ * ⁅n, y⁆ = 1 := by
      have h := hα
      rw [hy', hbil _ hn' z₁ hz₁] at h
      rw [← h]
      exact mul_inv_cancel _
    have hcomm0 : ⁅t * n * t⁻¹ * n, y⁆ = 1 := by
      rw [commutatorElement_mul_left_eq_conj_mul, hconj _ hmy _ hn']
      rw [← hZcent _ (hcomm _ hn' y hyN) _ (hZN hmy)]
      exact hkey
    exact hCL _ (N.mul_mem hn' hn) hcomm0
  obtain ⟨e, heN, heL⟩ : ∃ e ∈ N, e ∉ L := by
    by_contra h
    have hle : N ≤ L := fun x hx => by_contra fun hxL => h ⟨x, hx, hxL⟩
    have := Subgroup.card_le_of_le hle
    rw [hcardN, hcardL] at this
    omega
  obtain ⟨a, ha_def⟩ : ∃ a, a = ⁅u, e⁆ := ⟨_, rfl⟩
  have haL : a ∈ L := ha_def ▸ hNL e heN
  have haZ : a ∉ Z := fun h => heL ((hLdef e).2 ⟨heN, ha_def ▸ h⟩)
  have hae : u * e * u⁻¹ = a * e := by rw [ha_def]; exact hux e
  have haN : a ∈ N := hLN haL
  obtain ⟨z₃, hz₃, hA'⟩ : ∃ z₃ ∈ Z, t * a * t⁻¹ = z₃ * a⁻¹ :=
    ⟨t * a * t⁻¹ * a, step3 a haL, by group⟩
  obtain ⟨l, hl_def⟩ : ∃ l, l = t * e * t⁻¹ * e := ⟨_, rfl⟩
  have hlL : l ∈ L := hl_def ▸ step5 e heN
  have hqN : t * e * t⁻¹ ∈ N := hTN e heN
  have hq : t * e * t⁻¹ = l * e⁻¹ := by rw [hl_def]; group
  have hR : t * a * t⁻¹ * (t * e * t⁻¹) = u⁻¹ * (t * e * t⁻¹) * u := by
    calc t * a * t⁻¹ * (t * e * t⁻¹) = t * (a * e) * t⁻¹ := by group
      _ = t * (u * e * u⁻¹) * t⁻¹ := by rw [hae]
      _ = (t * u * t⁻¹) * (t * e * t⁻¹) * (t * u⁻¹ * t⁻¹) := by group
      _ = u⁻¹ * (t * e * t⁻¹) * u := by rw [htu, htu']
  obtain ⟨q, hq_def⟩ : ∃ q, q = t * e * t⁻¹ := ⟨_, rfl⟩
  rw [← hq_def] at hR hq hqN
  have hRHS : u⁻¹ * q * u = ⁅u, l⁆⁻¹ * q * (⁅u, a⁆⁻¹ * a) := by
    calc u⁻¹ * q * u = u⁻¹ * (l * e⁻¹) * u := by rw [hq]
      _ = (u⁻¹ * l * u) * (u⁻¹ * e * u)⁻¹ := by group
      _ = (⁅u, l⁆⁻¹ * l) * ((⁅u, a⁆⁻¹ * a)⁻¹ * e)⁻¹ := by
          rw [step1 l hlL, aux1 e a hae, step1 a haL]
      _ = ⁅u, l⁆⁻¹ * (l * e⁻¹) * (⁅u, a⁆⁻¹ * a) := by group
      _ = ⁅u, l⁆⁻¹ * q * (⁅u, a⁆⁻¹ * a) := by rw [hq]
  rw [hA', hRHS] at hR
  have hcl : ⁅u, l⁆ ∈ Z := ((hLdef l).1 hlL).2
  have hca : ⁅u, a⁆ ∈ Z := ((hLdef a).1 haL).2
  generalize ⁅u, l⁆ = cl at hR hcl
  generalize ⁅u, a⁆ = ca at hR hca
  have h1 : a⁻¹ * q = z₃⁻¹ * cl⁻¹ * q * (ca⁻¹ * a) := by
    calc a⁻¹ * q = z₃⁻¹ * (z₃ * a⁻¹ * q) := by group
      _ = z₃⁻¹ * (cl⁻¹ * q * (ca⁻¹ * a)) := by rw [hR]
      _ = z₃⁻¹ * cl⁻¹ * q * (ca⁻¹ * a) := by group
  have h2 : ⁅a⁻¹, q⁆ = (z₃⁻¹ * cl⁻¹ * ca⁻¹) * (q * (a * a) * q⁻¹) := by
    calc ⁅a⁻¹, q⁆ = (a⁻¹ * q) * a * q⁻¹ := by
          rw [commutatorElement_def, inv_inv]
      _ = z₃⁻¹ * cl⁻¹ * q * (ca⁻¹ * a) * a * q⁻¹ := by rw [h1]
      _ = z₃⁻¹ * cl⁻¹ * (q * ca⁻¹ * q⁻¹) * (q * (a * a) * q⁻¹) := by group
      _ = (z₃⁻¹ * cl⁻¹ * ca⁻¹) * (q * (a * a) * q⁻¹) := by
          rw [hconj _ (Z.inv_mem hca) q hqN]
  have hζ : z₃⁻¹ * cl⁻¹ * ca⁻¹ ∈ Z :=
    Z.mul_mem (Z.mul_mem (Z.inv_mem hz₃) (Z.inv_mem hcl)) (Z.inv_mem hca)
  have hmem : q * (a * a) * q⁻¹ ∈ Z := by
    have : q * (a * a) * q⁻¹ = (z₃⁻¹ * cl⁻¹ * ca⁻¹)⁻¹ * ⁅a⁻¹, q⁆ := by
      rw [h2]; group
    rw [this]
    exact Z.mul_mem (Z.inv_mem hζ) (hcomm _ (N.inv_mem haN) q hqN)
  have haa : a * a ∈ Z := by
    have h3 := hconj _ hmem q⁻¹ (N.inv_mem hqN)
    rw [inv_inv] at h3
    have h4 : q⁻¹ * (q * (a * a) * q⁻¹) * q = a * a := by group
    rw [h4] at h3
    rw [h3]
    exact hmem
  have h5 : a ^ 5 = 1 := hexp a haN
  have h6 : (a * a) ^ 3 = a := by
    calc (a * a) ^ 3 = (a ^ 2) ^ 3 := by rw [sq]
      _ = a ^ 6 := by rw [← pow_mul]
      _ = a ^ 5 * a := by rw [pow_succ]
      _ = a := by rw [h5, one_mul]
  exact haZ (h6 ▸ Z.pow_mem haa 3)

theorem s16c1_exists_fixed_noncentral {Y : Type} [Group Y] [Finite Y] {N S : Subgroup Y}
    [N.Normal] (hN : IsPOnePlusTwo 5 ↥N) (hS : IsSL2Prime ↥S 5) :
    ∃ u ∈ S, ∃ b ∈ N, orderOf u = 5 ∧ u ∉ N ∧ b ∉ (Subgroup.center ↥N).map N.subtype ∧
      u * b * u⁻¹ = b := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hNext : CFSG.IsExtraspecial 5 ↥N := hN.1
  obtain ⟨hcardS, hperfS, u0, t0, g0, hu0ord, ht0rel, hg0rel⟩ := s16c1_sl2five_facts hS
  let u : Y := u0
  let t : Y := t0
  let g : Y := g0
  have huS : u ∈ S := u0.2
  have htS : t ∈ S := t0.2
  have hgS : g ∈ S := g0.2
  have huo : orderOf u = 5 := by rw [Subgroup.orderOf_coe]; exact hu0ord
  have htu : t * u * t⁻¹ = u⁻¹ := by
    have h := congrArg Subtype.val ht0rel
    simpa [u, t] using h
  have hgu : g * u * g⁻¹ ∉ Subgroup.zpowers u := by
    intro hmem
    apply hg0rel
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    apply Subtype.ext
    simpa [u, t, g, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] using hn
  have huN : u ∉ N := by
    intro huNmem
    have hgugN : g * u * g⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem u huNmem g
    let E : Subgroup Y := Subgroup.closure ({u, g * u * g⁻¹} : Set Y)
    have hE_le_N : E ≤ N := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact huNmem
      · exact hgugN
    have hE_le_S : E ≤ S := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact huS
      · exact S.mul_mem (S.mul_mem hgS huS) (S.inv_mem hgS)
    have hE5 : IsPGroup 5 ↥E := by
      intro x
      have hNp : IsPGroup 5 ↥N := CFSG.IsExtraspecial.isPGroup 5 ↥N
      obtain ⟨k, hk⟩ := hNp ⟨(x : Y), hE_le_N x.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have huE : u ∈ E := Subgroup.subset_closure (by simp)
    have hgugE : g * u * g⁻¹ ∈ E := Subgroup.subset_closure (by simp)
    have hzp_le : Subgroup.zpowers u ≤ E := Subgroup.zpowers_le.mpr huE
    have hzpc : Nat.card (Subgroup.zpowers u) = 5 := by rw [Nat.card_zpowers, huo]
    have hE_gt5 : 5 < Nat.card ↥E := by
      by_contra hle
      push Not at hle
      have hEq : Subgroup.zpowers u = E :=
        Subgroup.eq_of_le_of_card_ge hzp_le (by rw [hzpc]; exact hle)
      exact hgu (hEq.symm ▸ hgugE)
    obtain ⟨m, hm⟩ := hE5.exists_card_eq
    have hm2 : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      have hle : Nat.card ↥E ≤ 5 := by
        rw [hm]
        interval_cases m <;> norm_num
      omega
    have h25dvd : 25 ∣ Nat.card ↥E := by
      rw [hm, show (25 : ℕ) = 5 ^ 2 by norm_num]
      exact pow_dvd_pow 5 hm2
    have hEdvd120 : Nat.card ↥E ∣ 120 := by
      have h := Subgroup.card_dvd_of_le hE_le_S
      rwa [hcardS] at h
    exact absurd (dvd_trans h25dvd hEdvd120) (by norm_num)
  let Z : Subgroup Y := (Subgroup.center ↥N).map N.subtype
  haveI hZn : Z.Normal := by
    change (Subgroup.map N.subtype (Subgroup.center ↥N)).Normal
    rw [← CFSG.GroupTheory.inf_centralizer_eq_map_center (H := Y) N]
    infer_instance
  have hZcard : Nat.card Z = 5 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, IsExtraspecial.center_order_p 5 ↥N]
  have hZleN : Z ≤ N := Subgroup.map_subtype_le _
  have hZcent : ∀ z ∈ Z, ∀ n ∈ N, z * n = n * z := by
    intro z hz n hn
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    exact (congrArg N.subtype (Subgroup.mem_center_iff.mp hc ⟨n, hn⟩)).symm
  have hcommuZ : ∀ z ∈ Z, u * z * u⁻¹ = z :=
    s16c1_conj_eq_self_of_prime (p := 5) huo hZcard
  let L : Subgroup Y :=
    { carrier := {b | b ∈ N ∧ ⁅u, b⁆ ∈ Z}
      one_mem' := by
        refine ⟨N.one_mem, ?_⟩
        rw [commutatorElement_one_right]
        exact Z.one_mem
      mul_mem' := by
        rintro b c ⟨hbN, hbZ⟩ ⟨hcN, hcZ⟩
        refine ⟨N.mul_mem hbN hcN, ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hcomm : b * ⁅u, c⁆ * b⁻¹ = ⁅u, c⁆ := by
          rw [(hZcent ⁅u, c⁆ hcZ b hbN).symm]
          group
        have heq : ⁅u, b⁆ * b * ⁅u, c⁆ * b⁻¹ = ⁅u, b⁆ * ⁅u, c⁆ := by
          rw [show ⁅u, b⁆ * b * ⁅u, c⁆ * b⁻¹ = ⁅u, b⁆ * (b * ⁅u, c⁆ * b⁻¹) by group, hcomm]
        rw [heq]
        exact Z.mul_mem hbZ hcZ
      inv_mem' := by
        rintro b ⟨hbN, hbZ⟩
        refine ⟨N.inv_mem hbN, ?_⟩
        have hbuZ : ⁅b, u⁆ ∈ Z := by
          rw [← commutatorElement_inv]
          exact Z.inv_mem hbZ
        have hcomm : b⁻¹ * ⁅b, u⁆ * b = ⁅b, u⁆ := by
          rw [(hZcent ⁅b, u⁆ hbuZ b⁻¹ (N.inv_mem hbN)).symm]
          group
        rw [commutatorElement_inv_right, hcomm]
        exact hbuZ }
  have hZL : Z ≤ L := by
    intro z hz
    refine ⟨hZleN hz, ?_⟩
    have h1 : ⁅u, z⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((mul_inv_eq_iff_eq_mul).mp (hcommuZ z hz))
    rw [h1]
    exact Z.one_mem
  let ZN : Subgroup ↥N := Subgroup.center ↥N
  haveI hZNN : ZN.Normal := inferInstance
  have hZN_eq : ZN = Z.subgroupOf N := by
    ext x
    simp [ZN, Z, Subgroup.mem_subgroupOf]
  have hUmap : ZN.map (MulAut.conjNormal (H := N) u : ↥N →* ↥N) = ZN :=
    (Subgroup.characteristic_iff_map_eq (H := ZN)).1
      (inferInstance : ZN.Characteristic) (MulAut.conjNormal (H := N) u)
  let Q := ↥N ⧸ ZN
  let U : MulAut Q := QuotientGroup.congr ZN ZN (MulAut.conjNormal u) hUmap
  have hpow : ∀ k : ℕ, ∀ x : ↥N,
      (U ^ k) (QuotientGroup.mk' ZN x) =
        QuotientGroup.mk' ZN (((MulAut.conjNormal (H := N) u) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ]
        change (U ^ k) (U (QuotientGroup.mk' ZN x)) =
          QuotientGroup.mk' ZN (((MulAut.conjNormal (H := N) u) ^ (k + 1)) x)
        rw [QuotientGroup.congr_mk', ih, pow_succ]
        rfl
  have hcu5 : (MulAut.conjNormal (H := N) u : MulAut ↥N) ^ 5 = 1 := by
    rw [← map_pow (MulAut.conjNormal (H := N)) u 5, show u ^ 5 = 1 by
      rw [← huo]; exact pow_orderOf_eq_one u]
    exact map_one _
  have hU5 : U ^ 5 = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    show (U ^ 5) (QuotientGroup.mk' ZN x) = QuotientGroup.mk' ZN x
    rw [hpow 5 x, hcu5]
    simp
  have hQcard : Nat.card Q = 25 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup ZN
    rw [hN.2.1, IsExtraspecial.center_order_p 5 ↥N] at hmul
    have h : Nat.card Q * 5 = 25 * 5 := by rw [← hmul]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : (0 : ℕ) < 5) h
  let Fix : Subgroup Q :=
    { carrier := {q | U q = q}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change U (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change U a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let G'' := ↥(Subgroup.zpowers U)
  have hG''5 : IsPGroup 5 G'' := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hU5
  letI : MulAction G'' Q := MulAction.compHom Q (Subgroup.zpowers U).subtype
  have hfix_action : MulAction.fixedPoints G'' Q = (Fix : Set Q) := by
    ext q
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨U, Subgroup.mem_zpowers U⟩
    · intro h w
      have hw : w.val ∈ MulAction.stabilizer (MulAut Q) q :=
        Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact h) w.2
      exact (MulAction.mem_stabilizer_iff.mp hw)
  have hmod := hG''5.card_modEq_card_fixedPoints Q
  rw [hfix_action, hQcard] at hmod
  have hFixdvd : 5 ∣ Nat.card Fix := by
    have h : Nat.card Fix ≡ 0 [MOD 5] := by
      have h25 : (25 : ℕ) ≡ 0 [MOD 5] := Nat.modEq_zero_iff_dvd.mpr (by norm_num)
      exact hmod.symm.trans h25
    exact Nat.modEq_zero_iff_dvd.mp h
  have hFixpos : 1 ≤ Nat.card Fix := by
    haveI : Nonempty ↥Fix := ⟨⟨1, by simp [Fix]⟩⟩
    have hpos : 0 < Nat.card Fix := Nat.card_pos
    omega
  have hFixge : 5 ≤ Nat.card Fix := Nat.le_of_dvd (by omega) hFixdvd
  have hFixnt : Nontrivial ↥Fix := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have h1 : Nat.card Fix = 1 := (Subgroup.eq_bot_iff_card (H := Fix)).mp hbot
    omega
  obtain ⟨q, hqFix, hq1⟩ := (Subgroup.nontrivial_iff_exists_ne_one Fix).mp hFixnt
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective q
  have hbmk : QuotientGroup.mk' ZN b = q := hb
  have hbFix : U (QuotientGroup.mk' ZN b) = QuotientGroup.mk' ZN b := by
    rw [hbmk]
    exact hqFix
  have hbZN : b ∉ ZN := by
    intro hbZ
    exact hq1 (by rw [← hb]; exact (QuotientGroup.eq_one_iff b).mpr hbZ)
  have hbZ : MulAut.conjNormal (H := N) u b * b⁻¹ ∈ ZN := by
    have h1 : QuotientGroup.mk' ZN (MulAut.conjNormal (H := N) u b) = QuotientGroup.mk' ZN b := by
      rw [← QuotientGroup.congr_mk' ZN ZN (MulAut.conjNormal (H := N) u) hUmap b]
      exact hbFix
    have h2 : (MulAut.conjNormal (H := N) u b) / b ∈ ZN := QuotientGroup.eq_iff_div_mem.mp h1
    rwa [div_eq_mul_inv] at h2
  have hbL : (b : Y) ∈ L := by
    refine ⟨b.2, ?_⟩
    have h := Subgroup.mem_map_of_mem N.subtype hbZ
    have h2 : N.subtype (MulAut.conjNormal (H := N) u b * b⁻¹) = ⁅u, (b : Y)⁆ := by
      rw [map_mul, map_inv, Subgroup.coe_subtype, MulAut.conjNormal_apply, commutatorElement_def]
    rwa [h2] at h
  have hbnotZ : (b : Y) ∉ Z := by
    intro h
    apply hbZN
    rw [hZN_eq]
    exact (Subgroup.mem_subgroupOf).mpr h
  have hLneZ : L ≠ Z := fun h => hbnotZ (h ▸ hbL)
  have hLleN : L ≤ N := fun x hx => hx.1
  let δ : ↥L →* Z :=
    { toFun := fun x => ⟨⁅u, (x : Y)⁆, x.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a c
        apply Subtype.ext
        show ⁅u, ((a * c : ↥L) : Y)⁆ = ⁅u, (a : Y)⁆ * ⁅u, (c : Y)⁆
        rw [Subgroup.coe_mul, commutatorElement_mul_right_eq_mul_conj]
        have hcomm : (a : Y) * ⁅u, (c : Y)⁆ * (a : Y)⁻¹ = ⁅u, (c : Y)⁆ := by
          rw [(hZcent ⁅u, (c : Y)⁆ (c.2).2 (a : Y) (a.2).1).symm]
          group
        rw [show ⁅u, (a : Y)⁆ * (a : Y) * ⁅u, (c : Y)⁆ * (a : Y)⁻¹ =
          ⁅u, (a : Y)⁆ * ((a : Y) * ⁅u, (c : Y)⁆ * (a : Y)⁻¹) by group, hcomm] }
  have hZker : Z.subgroupOf L ≤ δ.ker := by
    intro x hx
    have hz : (x : Y) ∈ Z := (Subgroup.mem_subgroupOf).mp hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ⁅u, (x : Y)⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (mul_inv_eq_iff_eq_mul).mp (hcommuZ (x : Y) hz)
  have key : ∀ x : ↥L, x ∉ Z.subgroupOf L → δ x = 1 →
      ∃ b' ∈ N, b' ∉ Z ∧ u * b' * u⁻¹ = b' := by
    intro x hxZ hx1
    refine ⟨(x : Y), x.2.1, ?_, ?_⟩
    · intro h
      exact hxZ ((Subgroup.mem_subgroupOf).mpr h)
    · have h1 : ⁅u, (x : Y)⁆ = 1 := by
        have h := Subtype.ext_iff.mp hx1
        change ⁅u, (x : Y)⁆ = 1 at h
        exact h
      exact (mul_inv_eq_iff_eq_mul).mpr (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hLge25 : 25 ≤ Nat.card L := by
    have hdvd : Nat.card L ∣ 125 := by
      have h := Subgroup.card_dvd_of_le hLleN
      rwa [hN.2.1] at h
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (p := 5) (m := 3) Nat.prime_five).1
      (by simpa using hdvd)
    have h5le : 5 ≤ Nat.card L := by
      have h : Nat.card Z ≤ Nat.card L := Subgroup.card_le_of_le hZL
      rwa [hZcard] at h
    have hne : Nat.card L ≠ 5 := by
      intro h
      exact hLneZ (Subgroup.eq_of_le_of_card_ge hZL (by rw [hZcard, h])).symm
    have hj2 : 2 ≤ j := by
      by_contra h
      push Not at h
      interval_cases j
      · rw [hj] at h5le
        norm_num at h5le
      · exact hne (by rw [hj]; norm_num)
    calc (25 : ℕ) = 5 ^ 2 := by norm_num
      _ ≤ 5 ^ j := pow_le_pow_right₀ (by norm_num : 1 ≤ (5 : ℕ)) hj2
      _ = Nat.card L := hj.symm
  by_cases hker : ∃ x : ↥L, x ∈ δ.ker ∧ x ∉ Z.subgroupOf L
  · obtain ⟨x, hxker, hxnotZ⟩ := hker
    obtain ⟨b', hb'N, hb'Z, hb'fix⟩ := key x hxnotZ hxker
    exact ⟨u, huS, b', hb'N, huo, huN, hb'Z, hb'fix⟩
  · push Not at hker
    have hker_eq : δ.ker = Z.subgroupOf L := le_antisymm hker hZker
    have hker_card : Nat.card δ.ker = 5 := by
      rw [hker_eq, natCard_subgroupOf_eq Z L hZL, hZcard]
    have hLcard25 : Nat.card L = 25 := by
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv, hker_card] at hcard
      have hrange : Nat.card δ.range ≤ 5 := by
        have h := Subgroup.card_subgroup_dvd_card δ.range
        rw [hZcard] at h
        exact Nat.le_of_dvd (by norm_num) h
      omega
    have hLnorm : (L.subgroupOf N).Normal := by
      refine ⟨fun x hx n => ?_⟩
      have hxL : (x : Y) ∈ L := (Subgroup.mem_subgroupOf).mp hx
      have hmem : ⁅n, x⁆ ∈ commutator ↥N := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top x)
      have hcomm_le : commutator ↥N ≤ Subgroup.center ↥N := by
        letI : IsMulCommutative (↥N ⧸ Subgroup.center ↥N) :=
          (IsExtraspecial.quotient_elementary_abelian 5 ↥N).toIsMulCommutative
        exact (Subgroup.Normal.quotient_commutative_iff_commutator_le
          (N := Subgroup.center ↥N)).mp inferInstance
      have hc : ⁅n, x⁆ ∈ Subgroup.center ↥N := hcomm_le hmem
      have hcZ : ((⁅n, x⁆ : ↥N) : Y) ∈ Z := Subgroup.mem_map_of_mem N.subtype hc
      have hz : ((⁅n, x⁆ : ↥N) : Y) ∈ L := hZL hcZ
      refine (Subgroup.mem_subgroupOf).mpr ?_
      have h0 : n * x * n⁻¹ = ⁅n, x⁆ * x := by rw [commutatorElement_def]; group
      have h1 : ((n * x * n⁻¹ : ↥N) : Y) = ((⁅n, x⁆ : ↥N) : Y) * (x : Y) := by
        rw [h0]; rfl
      rw [h1]
      exact L.mul_mem hz hxL
    haveI : (L.subgroupOf N).Normal := hLnorm
    have hNLcard : Nat.card (↥N ⧸ L.subgroupOf N) = 5 := by
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf N)
      rw [natCard_subgroupOf_eq L N hLleN, hN.2.1, hLcard25] at hcard
      have h : Nat.card (↥N ⧸ L.subgroupOf N) * 25 = 5 * 25 := by rw [← hcard]; norm_num
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    have huL : ∀ x ∈ L, u * x * u⁻¹ ∈ L := by
      intro x hx
      have h1 : u * x * u⁻¹ = ⁅u, x⁆ * x := by rw [commutatorElement_def]; group
      rw [h1]
      exact L.mul_mem (hZL hx.2) hx
    have hLNmap : (L.subgroupOf N).map (MulAut.conjNormal (H := N) u : ↥N →* ↥N) =
        L.subgroupOf N := by
      have hle : (L.subgroupOf N).map (MulAut.conjNormal (H := N) u : ↥N →* ↥N) ≤
          L.subgroupOf N := by
        rw [Subgroup.map_le_iff_le_comap]
        intro x hx
        exact huL (x : Y) (Subgroup.mem_subgroupOf.mp hx)
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_congr (Subgroup.equivMapOfInjective
        (f := (MulAut.conjNormal (H := N) u : ↥N →* ↥N)) (L.subgroupOf N)
        (MulAut.conjNormal (H := N) u).injective).toEquiv]
    let σ : MulAut (↥N ⧸ L.subgroupOf N) :=
      QuotientGroup.congr (L.subgroupOf N) (L.subgroupOf N) (MulAut.conjNormal (H := N) u) hLNmap
    have hσ5 : σ ^ 5 = 1 := by
      have hpow : ∀ k : ℕ, ∀ x : ↥N,
          (σ ^ k) (QuotientGroup.mk' (L.subgroupOf N) x) =
            QuotientGroup.mk' (L.subgroupOf N) (((MulAut.conjNormal (H := N) u) ^ k) x) := by
        intro k
        induction k with
        | zero => intro x; simp
        | succ k ih =>
            intro x
            rw [pow_succ]
            change (σ ^ k) (σ (QuotientGroup.mk' (L.subgroupOf N) x)) =
              QuotientGroup.mk' (L.subgroupOf N) (((MulAut.conjNormal (H := N) u) ^ (k + 1)) x)
            rw [QuotientGroup.congr_mk', ih, pow_succ]
            rfl
      have hcu5 : (MulAut.conjNormal (H := N) u : MulAut ↥N) ^ 5 = 1 := by
        rw [← map_pow (MulAut.conjNormal (H := N)) u 5, show u ^ 5 = 1 by
          rw [← huo]; exact pow_orderOf_eq_one u]
        exact map_one _
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      show (σ ^ 5) (QuotientGroup.mk' (L.subgroupOf N) x) = QuotientGroup.mk' (L.subgroupOf N) x
      rw [hpow 5 x, hcu5]
      simp
    have hσ1 : σ = 1 := s16c1_mulAut_eq_one_of_pow_prime hNLcard σ hσ5
    have hNLtriv : ∀ e : ↥N, ⁅u, (e : Y)⁆ ∈ L := by
      intro e
      have heq : σ (QuotientGroup.mk' (L.subgroupOf N) e) =
          QuotientGroup.mk' (L.subgroupOf N) e := by
        rw [hσ1]; rfl
      have h2 : QuotientGroup.mk' (L.subgroupOf N) (MulAut.conjNormal (H := N) u e) =
          QuotientGroup.mk' (L.subgroupOf N) e := by
        rw [← QuotientGroup.congr_mk' (L.subgroupOf N) (L.subgroupOf N)
          (MulAut.conjNormal (H := N) u) hLNmap e]
        exact heq
      have h3 : (MulAut.conjNormal (H := N) u e) / e ∈ L.subgroupOf N :=
        QuotientGroup.eq_iff_div_mem.mp h2
      have h4 := Subgroup.mem_subgroupOf.mp h3
      simpa [div_eq_mul_inv, MulAut.conjNormal_apply, Subgroup.coe_subtype, commutatorElement_def]
        using h4
    exfalso
    have htZ : ∀ z ∈ Z, t * z * t⁻¹ = z :=
      s16c1_perfect_centralizes (p := 5) hZcard hperfS t htS
    have hcomm_le : commutator ↥N ≤ Subgroup.center ↥N := by
      letI : IsMulCommutative (↥N ⧸ Subgroup.center ↥N) :=
        (IsExtraspecial.quotient_elementary_abelian 5 ↥N).toIsMulCommutative
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := Subgroup.center ↥N)).mp inferInstance
    have hcommZ : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Z := by
      intro a ha b hb
      have hmem : ⁅(⟨a, ha⟩ : ↥N), ⟨b, hb⟩⁆ ∈ commutator ↥N := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      exact Subgroup.mem_map_of_mem N.subtype (hcomm_le hmem)
    have hZtriv : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n ∈ Z := by
      intro n hn hc
      have hmem : (⟨n, hn⟩ : ↥N) ∈ Subgroup.center ↥N := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hc g g.2).symm
      exact Subgroup.mem_map_of_mem N.subtype hmem
    have hexp : ∀ n ∈ N, n ^ 5 = 1 := fun n hn => by
      simpa using congrArg Subtype.val (hN.2.2 ⟨n, hn⟩)
    have hker' : ∀ x ∈ L, ⁅u, x⁆ = 1 → x ∈ Z := by
      intro x hx hx1
      have hmem : (⟨x, hx⟩ : ↥L) ∈ δ.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext hx1
      exact (Subgroup.mem_subgroupOf).mp (hker _ hmem)
    exact s16c1_neg_branch (N := N) (Z := Z) (L := L) (u := u) (t := t) hZcent hcommZ hZtriv hexp
      hN.2.1 (by rw [hLcard25]; norm_num) hZL hLleN (fun b => Iff.rfl) hcommuZ htZ htu
      (fun e he => hNLtriv ⟨e, he⟩) hker' ⟨(b : Y), hbL, hbnotZ⟩


theorem s16c1_exists_elemAbelian_five_cube {Y : Type} [Group Y] [Finite Y] {N S : Subgroup Y}
    [N.Normal] (hN : IsPOnePlusTwo 5 ↥N) (hS : IsSL2Prime ↥S 5) :
    ∃ E : Subgroup Y, IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 3 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hNinst : CFSG.IsExtraspecial 5 ↥N := hN.1
  obtain ⟨u, -, b, hbN, huo, huN, hbZ, hub⟩ := s16c1_exists_fixed_noncentral hN hS
  let Z : Subgroup Y := (Subgroup.center ↥N).map N.subtype
  have hbZ' : b ∉ Z := hbZ
  haveI hZn : Z.Normal := by
    change (Subgroup.map N.subtype (Subgroup.center ↥N)).Normal
    rw [← CFSG.GroupTheory.inf_centralizer_eq_map_center (H := Y) N]
    infer_instance
  have hZcard : Nat.card Z = 5 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, IsExtraspecial.center_order_p 5 ↥N]
  have hZleN : Z ≤ N := Subgroup.map_subtype_le _
  have hb5 : b ^ 5 = 1 := by
    have := hN.2.2 ⟨b, hbN⟩
    simpa using congrArg Subtype.val this
  have hbo : orderOf b = 5 := by
    refine orderOf_eq_prime hb5 ?_
    intro hb1
    exact hbZ' (hb1 ▸ Z.one_mem)
  have hbz : Nat.card (Subgroup.zpowers b) = 5 := by rw [Nat.card_zpowers, hbo]
  have hu5 : u ^ 5 = 1 := by rw [← huo]; exact pow_orderOf_eq_one u
  have hZel : IsElemAbelian 5 Z := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a c
      obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hna, ← hmc, ← map_mul, ← map_mul]
      exact congrArg N.subtype (Subgroup.mem_center_iff.mp hn m).symm
    · intro z hz
      obtain ⟨n, _, hnz⟩ := Subgroup.mem_map.mp hz
      rw [← hnz, ← map_pow]
      exact congrArg N.subtype (hN.2.2 n)
  have hcommZb : ∀ z ∈ Z, ∀ w ∈ Subgroup.zpowers b, z * w = w * z := by
    intro z hz w hw
    obtain ⟨n, hn, hnz⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : Commute (N.subtype n) b := by
      change (N.subtype n) * N.subtype ⟨b, hbN⟩ =
        N.subtype ⟨b, hbN⟩ * N.subtype n
      rw [← map_mul, ← map_mul]
      exact congrArg N.subtype (Subgroup.mem_center_iff.mp hn ⟨b, hbN⟩).symm
    rw [← hnz]
    exact (hc.zpow_right k).eq
  have hEel : IsElemAbelian 5 (Z ⊔ Subgroup.zpowers b : Subgroup Y) :=
    IsElemAbelian.sup_of_commute hZel (isElemAbelian_zpowers hb5) hcommZb
  have hZb : Z ⊓ Subgroup.zpowers b = ⊥ := by
    have hdvd : Nat.card ↥(Z ⊓ Subgroup.zpowers b) ∣ 5 := by
      rw [← hZcard]
      have hle : Z ⊓ Subgroup.zpowers b ≤ Z := inf_le_left
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5
    · exact (Subgroup.eq_bot_iff_card (H := Z ⊓ Subgroup.zpowers b)).mpr h1
    · exfalso
      have heq : Z ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5, hbz])
      have : b ∈ Z ⊓ Subgroup.zpowers b := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hbZ' this.1
  have hEcard : Nat.card (Z ⊔ Subgroup.zpowers b : Subgroup Y) = 5 ^ 2 := by
    obtain ⟨hcard, -⟩ :=
      CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z (Subgroup.zpowers b) hcommZb
    rw [hZb, Subgroup.card_bot, mul_one, hZcard, hbz] at hcard
    rw [hcard]
    norm_num
  have hcommuZ : ∀ z ∈ Z, u * z * u⁻¹ = z :=
    s16c1_conj_eq_self_of_prime (p := 5) huo hZcard
  have hZcent : Z ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro hw hwmem
    rw [Set.mem_singleton_iff] at hwmem
    subst hwmem
    exact (mul_inv_eq_iff_eq_mul).mp (hcommuZ z hz)
  have hbcent : Subgroup.zpowers b ≤ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro hw hwmem
    rw [Set.mem_singleton_iff] at hwmem
    subst hwmem
    exact (mul_inv_eq_iff_eq_mul).mp hub
  have hEcent : (Z ⊔ Subgroup.zpowers b : Subgroup Y) ≤
      Subgroup.centralizer ({u} : Set Y) := sup_le hZcent hbcent
  have hcommE : ∀ e ∈ (Z ⊔ Subgroup.zpowers b : Subgroup Y), e * u = u * e := by
    intro e he
    exact ((Subgroup.mem_centralizer_iff.mp (hEcent he)) u (Set.mem_singleton u)).symm
  have hcommE' : ∀ e ∈ (Z ⊔ Subgroup.zpowers b : Subgroup Y),
      ∀ w ∈ Subgroup.zpowers u, e * w = w * e := by
    intro e he w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (show Commute e u from hcommE e he) k)).eq
  have hEleN : (Z ⊔ Subgroup.zpowers b : Subgroup Y) ≤ N :=
    sup_le hZleN (Subgroup.zpowers_le.mpr hbN)
  have hdisj : (Z ⊔ Subgroup.zpowers b : Subgroup Y) ⊓ Subgroup.zpowers u = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxE, hxu⟩ := hx
    by_contra hx1
    have hx5 : x ^ 5 = 1 := hEel.2 x hxE
    have hxo : orderOf x = 5 := orderOf_eq_prime hx5 hx1
    have hxcard : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hxo]
    have hucard : Nat.card (Subgroup.zpowers u) = 5 := by rw [Nat.card_zpowers, huo]
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers u := Subgroup.zpowers_le.mpr hxu
    have heq : Subgroup.zpowers x = Subgroup.zpowers u :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hxcard, hucard])
    have hxEu : Subgroup.zpowers x ≤ (Z ⊔ Subgroup.zpowers b : Subgroup Y) :=
      Subgroup.zpowers_le.mpr hxE
    have hu_x : u ∈ Subgroup.zpowers x := by rw [heq]; exact Subgroup.mem_zpowers u
    exact huN (hEleN (hxEu hu_x))
  have hsupel : IsElemAbelian 5
      ((Z ⊔ Subgroup.zpowers b : Subgroup Y) ⊔ Subgroup.zpowers u) :=
    IsElemAbelian.sup_of_commute hEel (isElemAbelian_zpowers hu5) hcommE'
  have hsupcard : Nat.card (((Z ⊔ Subgroup.zpowers b : Subgroup Y) ⊔
      Subgroup.zpowers u) : Subgroup Y) = 5 ^ 3 := by
    obtain ⟨hcard, -⟩ :=
      CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Z ⊔ Subgroup.zpowers b)
        (Subgroup.zpowers u) hcommE'
    rw [hdisj, Subgroup.card_bot, mul_one, hEcard, Nat.card_zpowers, huo] at hcard
    rw [hcard]
    norm_num
  exact ⟨_, hsupel, hsupcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
