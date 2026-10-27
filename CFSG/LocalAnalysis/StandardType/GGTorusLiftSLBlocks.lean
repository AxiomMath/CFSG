module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftTorus
public import CFSG.LieType.SteinbergBRBlockParabolic
public import CFSG.RankThree.PartOne.KFCL.BlockSL
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Chevalley Matrix

namespace GGPlusLiftTorus

variable {R : Type} [Group R] {K : Type} [Field K] [CharP K 2] {p d : ℕ}

theorem ggTorusLift_of_commutingSL2_normalizing (hp : p.Prime) (hp2 : p ≠ 2) {s n : SL2 K}
    (hsorder : orderOf s = p) (hconj : n * s * n⁻¹ = s⁻¹) (ρ : Fin d → SL2 K →* R)
    (hρ : ∀ i, Function.Injective (ρ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B)) {U : Subgroup R} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hsU : ∀ i, ρ i s ∈ Subgroup.normalizer (U : Set R)) :
    GGTorusLift p d R := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hs_pow : s ^ p = 1 := by rw [← hsorder]; exact pow_orderOf_eq_one s
  have hpow : ∀ i : Fin d, (ρ i s) ^ p = 1 := fun i => by
    rw [← map_pow, hs_pow, map_one]
  let coord : Fin d → Multiplicative (ZMod p) →* R := fun i => TableBSymp.zmodPowHom (hpow i)
  have coord_apply : ∀ (i : Fin d) (a : Multiplicative (ZMod p)),
      coord i a = ρ i (s ^ (Multiplicative.toAdd a).val) := fun i a => by
    change TableBSymp.zmodPowHom (hpow i) a = ρ i (s ^ (Multiplicative.toAdd a).val)
    rw [TableBSymp.zmodPowHom_apply, map_pow]
  have coord_inj : ∀ i, Function.Injective (coord i) := fun i => by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hto : orderOf (ρ i s) = p := by
      rw [orderOf_injective _ (hρ i), hsorder]
    exact (TableBSymp.zmodPowHom_eq_one_iff (hpow i) hto).mp ha
  have coord_comm : Pairwise fun i j : Fin d => ∀ a b, Commute (coord i a) (coord j b) := by
    intro i j hij a b
    rw [coord_apply, coord_apply]
    exact hc i j hij _ _
  let ePi : (Fin d → Multiplicative (ZMod p)) →* R := MonoidHom.noncommPiCoprod coord coord_comm
  let e : Multiplicative (Fin d → ZMod p) →* R :=
    ePi.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).toMonoidHom
  have e_apply : ∀ v : Fin d → ZMod p, e (.ofAdd v) = ePi (fun j => .ofAdd (v j)) := fun v => rfl
  have coord_indep : iSupIndep fun i => (coord i).range := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := hx
    have hle : (⨆ (j) (_ : j ≠ i), (coord j).range) ≤
        Subgroup.centralizer (Set.range (ρ i)) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨B, rfl⟩ := hy
      rw [coord_apply]
      exact (hc i j (Ne.symm hj) B (s ^ (Multiplicative.toAdd b).val)).eq
    have hcen := hle hx'
    have hs_center : s ^ (Multiplicative.toAdd a).val ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      have h1 := Subgroup.mem_centralizer_iff.mp hcen (ρ i B) ⟨B, rfl⟩
      rw [coord_apply] at h1
      have h2 : ρ i (B * s ^ (Multiplicative.toAdd a).val) =
          ρ i (s ^ (Multiplicative.toAdd a).val * B) := by
        rw [map_mul, map_mul]
        exact h1
      exact hρ i h2
    obtain ⟨r, hr2, hr⟩ :=
      (Matrix.SpecialLinearGroup.mem_center_iff (n := Fin 2) (R := K)).mp hs_center
    have hr1 : r = 1 := by
      have h2 : r ^ 2 = 1 := by simpa using hr2
      have h : (r - 1) ^ 2 = 0 := by
        have h3 : (r - 1) ^ 2 = (2 : K) * (1 - r) := by linear_combination h2
        rw [h3, CharTwo.two_eq_zero, zero_mul]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
    have hs_one : s ^ (Multiplicative.toAdd a).val = 1 := by
      apply Subtype.ext
      rw [← hr, hr1]
      exact map_one (Matrix.scalar (Fin 2))
    have hdvd : p ∣ (Multiplicative.toAdd a).val := by
      have := orderOf_dvd_of_pow_eq_one hs_one
      rwa [hsorder] at this
    have hval0 : (Multiplicative.toAdd a).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have ha1 : a = 1 := by
      rw [← ofAdd_toAdd a, (ZMod.val_eq_zero (Multiplicative.toAdd a)).mp hval0, ofAdd_zero]
    rw [ha1, map_one]
  have ePi_inj : Function.Injective ePi :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep coord coord_indep coord_inj
  have e_inj : Function.Injective e :=
    ePi_inj.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).injective
  have reflGen_conj_coord : ∀ (i j : Fin d) (a : Multiplicative (ZMod p)),
      ρ i n * coord j a * (ρ i n)⁻¹ = coord j (if j = i then a⁻¹ else a) := by
    intro i j a
    split_ifs with hji
    · subst hji
      rw [show coord j a⁻¹ = (coord j a)⁻¹ from map_inv _ a, coord_apply, ← map_inv,
        ← map_mul, ← map_mul, ← map_inv]
      congr 1
      rw [← conj_pow, hconj, inv_pow]
    · rw [coord_apply, (hc i j (fun h => hji h.symm) n (s ^ (Multiplicative.toAdd a).val)).eq,
        mul_inv_cancel_right]
  have reflGen_conj_ePi : ∀ (i : Fin d) (f : Fin d → Multiplicative (ZMod p)),
      ρ i n * ePi f * (ρ i n)⁻¹ = ePi (reflHom i f) := by
    intro i f
    have h : (MulAut.conj (ρ i n)).toMonoidHom.comp ePi = ePi.comp (reflHom i) :=
      MonoidHom.pi_ext fun j a => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ePi,
          MonoidHom.noncommPiCoprod_mulSingle, reflHom_mulSingle]
        exact reflGen_conj_coord i j a
    have h1 := congrArg (fun φ => φ f) h
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  have reflGen_conj_e : ∀ (i : Fin d) (v : Fin d → ZMod p),
      ρ i n * e (.ofAdd v) * (ρ i n)⁻¹ =
        e (.ofAdd (v - reflCoeff i v • Pi.single i (1 : ZMod p))) := by
    intro i v
    rw [e_apply, e_apply, reflGen_conj_ePi, reflHom_ofAdd]
  have hle : ePi.range ≤ Subgroup.normalizer (U : Set R) := by
    change (MonoidHom.noncommPiCoprod coord coord_comm).range ≤ _
    rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    change coord i a ∈ _
    rw [coord_apply, map_pow]
    exact Subgroup.pow_mem _ (hsU i) _
  have hTU : ∀ v, ∀ u ∈ U, e v * u * (e v)⁻¹ ∈ U := fun v u hu =>
    (Subgroup.mem_normalizer_iff.mp (hle ⟨_, rfl⟩) u).mp hu
  exact TableBF4.ggTorusLift_of_reflections hp hp2 e e_inj reflCoeff reflCoeff_single
    (fun i => ρ i n) reflGen_conj_e hU hU2 hTU

end GGPlusLiftTorus

namespace TypeA

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open CFSG.RankThree.PartOne.KFCL.BlockSL

variable {K : Type} [Field K] [CharP K 2] {p : ℕ}

section Blocks

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [CharP K 2] in
theorem levL_commute_levR (A : SpecialLinearGroup (Fin 2) K) (D : SpecialLinearGroup ι K) :
    Commute (levL K ι A) (levR K (Fin 2) D) := by
  apply Subtype.ext
  change fromBlocks A.val 0 0 1 * fromBlocks 1 0 0 D.val =
    fromBlocks 1 0 0 D.val * fromBlocks A.val 0 0 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

omit [CharP K 2] in
theorem levL_mem_normalizer_uni (A : SpecialLinearGroup (Fin 2) K) :
    levL K ι A ∈ Subgroup.normalizer ((uniHom K (Fin 2) ι).range : Set _) := by
  refine CFSG.StandardType.le_normalizer_of_map_conj_le (S := (levL K ι).range) ?_ ⟨A, rfl⟩
  rintro _ ⟨B, rfl⟩ _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨Multiplicative.ofAdd (B.val * Multiplicative.toAdd x), ?_⟩
  change _ = levL K ι B * uniHom K (Fin 2) ι (Multiplicative.ofAdd (Multiplicative.toAdd x)) *
    (levL K ι B)⁻¹
  rw [levL_conj_uni]

omit [CharP K 2] in
theorem levR_mem_normalizer_uni (D : SpecialLinearGroup ι K) :
    levR K (Fin 2) D ∈ Subgroup.normalizer ((uniHom K (Fin 2) ι).range : Set _) := by
  refine CFSG.StandardType.le_normalizer_of_map_conj_le (S := (levR K (Fin 2)).range) ?_
    ⟨D, rfl⟩
  rintro _ ⟨B, rfl⟩ _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd x * (B⁻¹).val), ?_⟩
  change _ = levR K (Fin 2) B * uniHom K (Fin 2) ι (Multiplicative.ofAdd (Multiplicative.toAdd x)) *
    (levR K (Fin 2) B)⁻¹
  rw [levR_conj_uni]

theorem uniHom_sq (x : Multiplicative (Matrix (Fin 2) ι K)) : uniHom K (Fin 2) ι x ^ 2 = 1 := by
  have hx : x ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    ext i j
    simp [CharTwo.add_self_eq_zero]
  rw [← map_pow, hx, map_one]

end Blocks

private theorem eq_scalar_of_proj_reindex_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (eι : Fin 2 ⊕ ι ≃ Fin d) {g : SpecialLinearGroup (Fin 2 ⊕ ι) K}
    (hg : proj d K (reindexSL eι g) = 1) :
    ∃ c : K, ∀ a b, (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) K) a b = if a = b then c else 0 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hg)
  refine ⟨c, fun a b => ?_⟩
  have h : (Matrix.reindex eι eι (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) K)) (eι a) (eι b) =
      scalar (Fin d) (c : K) (eι a) (eι b) :=
    congrArg (fun M : Matrix (Fin d) (Fin d) K => M (eι a) (eι b)) hc
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, scalar_apply,
    diagonal_apply, eι.injective.eq_iff] at h
  exact h

theorem ggTorusLift_of_sl2Blocks
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {d m : ℕ}
    (eι : Fin 2 ⊕ ι ≃ Fin d) (hp : p.Prime) (hp2 : p ≠ 2) {s n : SL2 K} (hs : orderOf s = p)
    (hn : n * s * n⁻¹ = s⁻¹) (ρ' : Fin m → SL2 K →* SpecialLinearGroup ι K)
    (hρ' : ∀ i, Function.Injective (ρ' i))
    (hc' : ∀ i j, i ≠ j → ∀ A B, Commute (ρ' i A) (ρ' j B)) :
    GGTorusLift p (m + 1) (projectiveSL d K) := by
  classical
  set π : SpecialLinearGroup (Fin 2 ⊕ ι) K →* projectiveSL d K :=
    (proj d K).comp (reindexSL eι).toMonoidHom with hπ
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  have hπ1 : ∀ g, π g = 1 →
      ∃ c : K, ∀ a b, (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) K) a b = if a = b then c else 0 :=
    fun g hg => eq_scalar_of_proj_reindex_eq_one eι hg
  have hL : Function.Injective (π.comp (levL K ι)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    obtain ⟨c, hc⟩ := hπ1 _ hA
    have hc1 : c = 1 := by
      have h := hc (Sum.inr j₀) (Sum.inr j₀)
      rw [levL_val, fromBlocks_apply₂₂, one_apply_eq, if_pos rfl] at h
      exact h.symm
    ext a b
    have h := hc (Sum.inl a) (Sum.inl b)
    simp only [levL_val, fromBlocks_apply₁₁, hc1, Sum.inl.injEq] at h
    rw [h, Matrix.SpecialLinearGroup.coe_one, one_apply]
  have hR : ∀ i, Function.Injective (π.comp ((levR K (Fin 2)).comp (ρ' i))) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro A hA
    obtain ⟨c, hc⟩ := hπ1 _ hA
    have hc1 : c = 1 := by
      have h := hc (Sum.inl 0) (Sum.inl 0)
      rw [MonoidHom.comp_apply, levR_val, fromBlocks_apply₁₁, one_apply_eq, if_pos rfl] at h
      exact h.symm
    have hD : ρ' i A = 1 := by
      ext a b
      have h := hc (Sum.inr a) (Sum.inr b)
      simp only [MonoidHom.comp_apply, levR_val, fromBlocks_apply₂₂, hc1, Sum.inr.injEq] at h
      rw [h, Matrix.SpecialLinearGroup.coe_one, one_apply]
    exact (hρ' i) (hD.trans (map_one (ρ' i)).symm)
  let ρ : Fin (m + 1) → SL2 K →* projectiveSL d K :=
    Fin.cons (π.comp (levL K ι)) fun i => π.comp ((levR K (Fin 2)).comp (ρ' i))
  have hρ : ∀ i, Function.Injective (ρ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hL
    · exact hR i
  have hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B) := by
    intro i j hij A B
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j =>
        exact (levL_commute_levR A (ρ' j B)).map π
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        exact ((levL_commute_levR B (ρ' i A)).map π).symm
      | succ j =>
        exact ((hc' i j (fun h => hij (congrArg Fin.succ h)) A B).map (levR K (Fin 2))).map π
  let U : Subgroup (projectiveSL d K) := (uniHom K (Fin 2) ι).range.map π
  have hU : U ≠ ⊥ := by
    intro hbot
    have hmem : π (uniHom K (Fin 2) ι (Multiplicative.ofAdd (Matrix.of fun _ _ => 1))) ∈ U :=
      ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    obtain ⟨c, hc⟩ := hπ1 _ hmem
    have h := hc (Sum.inl 0) (Sum.inr j₀)
    rw [uniHom_val, fromBlocks_apply₁₂, if_neg Sum.inl_ne_inr, Matrix.of_apply] at h
    exact one_ne_zero h
  have hU2 : IsPGroup 2 U := by
    rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← map_pow, uniHom_sq, map_one]
    rfl
  have hsU : ∀ i, ρ i s ∈ Subgroup.normalizer (U : Set (projectiveSL d K)) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Subgroup.le_normalizer_map π ⟨_, levL_mem_normalizer_uni s, rfl⟩
    · exact Subgroup.le_normalizer_map π ⟨_, levR_mem_normalizer_uni (ρ' i s), rfl⟩
  exact GGPlusLiftTorus.ggTorusLift_of_commutingSL2_normalizing hp hp2 hs hn ρ hρ hc hU hU2 hsU

theorem ggTorusLift_four_nonsplit
    [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : GGTorusLift p 2 (projectiveSL 4 K) := by
  obtain ⟨s, n, hs, hn⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 hp hp2 hpq
  exact ggTorusLift_of_sl2Blocks (ι := Fin 2) (m := 1) finSumFinEquiv hp hp2 hs hn
    (fun _ => MonoidHom.id _) (fun _ => Function.injective_id)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)

theorem ggTorusLift_six_nonsplit
    [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : GGTorusLift p 3 (projectiveSL 6 K) := by
  obtain ⟨s, n, hs, hn⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 hp hp2 hpq
  refine ggTorusLift_of_sl2Blocks (ι := Fin 2 ⊕ Fin 2) (m := 2)
    ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv) hp hp2 hs hn
    ![levL K (Fin 2), levR K (Fin 2)] (fun i => ?_) (fun i j hij A B => ?_)
  · fin_cases i
    · exact levL_injective
    · exact levR_injective
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact levL_commute_levR A B
    · exact (levL_commute_levR B A).symm
    · exact absurd rfl hij


omit [CharP K 2] in
private theorem hsl_mul (a b : Kˣ) : (HSL (a * b) : SL2 K) = HSL a * HSL b := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm]

private noncomputable def hslHom : Kˣ →* SL2 K where
  toFun := HSL
  map_one' := by refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]
  map_mul' := hsl_mul

omit [CharP K 2] in
private theorem hslHom_injective : Function.Injective (hslHom : Kˣ →* SL2 K) := by
  intro a b h
  have h00 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  exact Units.ext (by simpa [hslHom, coe_HSL] using h00)

private noncomputable def uslHom : Multiplicative K →* SL2 K where
  toFun x := uSL (Multiplicative.toAdd x)
  map_one' := by refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]
  map_mul' a b := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        add_comm]

omit [CharP K 2] in
private theorem hsl_mem_normalizer_usl (a : Kˣ) :
    (HSL a : SL2 K) ∈ Subgroup.normalizer ((uslHom : Multiplicative K →* SL2 K).range : Set _) := by
  refine CFSG.StandardType.le_normalizer_of_map_conj_le (S := (hslHom : Kˣ →* SL2 K).range) ?_
    ⟨a, rfl⟩
  rintro _ ⟨b, rfl⟩ _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨Multiplicative.ofAdd ((b : K) * Multiplicative.toAdd x * b), ?_⟩
  have h : (HSL b : SL2 K) * uSL (Multiplicative.toAdd x) =
      uSL ((b : K) * Multiplicative.toAdd x * b) * HSL b := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_HSL, coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two]
  change uSL ((b : K) * Multiplicative.toAdd x * b) =
    (HSL b : SL2 K) * uSL (Multiplicative.toAdd x) * (HSL b)⁻¹
  rw [h, mul_inv_cancel_right]

theorem ggTorusLift_two_split
    [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : GGTorusLift p 1 (projectiveSL 2 K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨μ, hμ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpq)
  have hs : orderOf (HSL μ : SL2 K) = p := by
    change orderOf (hslHom μ) = p
    rw [orderOf_injective _ hslHom_injective, hμ]
  have hn : (WSL : SL2 K) * HSL μ * WSL⁻¹ = (HSL μ)⁻¹ := by
    have h1 : (WSL : SL2 K) * HSL μ = HSL μ⁻¹ * WSL := by
      refine SL2_ext ?_ ?_ ?_ ?_ <;>
        simp [coe_WSL, coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
          Fin.sum_univ_two]
    rw [h1, mul_inv_cancel_right]
    exact map_inv (hslHom : Kˣ →* SL2 K) μ
  have hproj1 : ∀ g : SL2 K, proj 2 K g = 1 →
      ∃ c : K, ∀ a b, (g : Matrix (Fin 2) (Fin 2) K) a b = if a = b then c else 0 := by
    intro g hg
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hg)
    exact ⟨c, fun a b => by rw [hc, scalar_apply, diagonal_apply]⟩
  have hinj : Function.Injective (proj 2 K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hg)
    have hdet := g.2
    rw [hc, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      at hdet
    have h1 : (c : K) = 1 := by
      have h : ((c : K) - 1) ^ 2 = 0 := by
        have h3 : ((c : K) - 1) ^ 2 = (2 : K) * (1 - c) := by linear_combination hdet
        rw [h3, CharTwo.two_eq_zero, zero_mul]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
    ext a b
    rw [hc, h1, scalar_apply, Matrix.SpecialLinearGroup.coe_one, diagonal_apply, one_apply]
  let U : Subgroup (projectiveSL 2 K) := (uslHom : Multiplicative K →* SL2 K).range.map (proj 2 K)
  have hU : U ≠ ⊥ := by
    intro hbot
    have hmem : proj 2 K (uslHom (Multiplicative.ofAdd 1)) ∈ U := ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    obtain ⟨c, hc⟩ := hproj1 _ hmem
    have h := hc 0 1
    simp [uslHom, coe_uSL] at h
  have hU2 : IsPGroup 2 U := by
    rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hx : x ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      simp [CharTwo.add_self_eq_zero]
    rw [pow_one, Subgroup.coe_pow, ← map_pow, ← map_pow, hx, map_one, map_one]
    rfl
  exact GGPlusLiftTorus.ggTorusLift_of_commutingSL2_normalizing hp hp2 hs hn
    (fun _ : Fin 1 => proj 2 K) (fun _ => hinj)
    (fun i j hij => absurd (Subsingleton.elim i j) hij) hU hU2
    (fun _ => Subgroup.le_normalizer_map (proj 2 K) ⟨_, hsl_mem_normalizer_usl μ, rfl⟩)

end TypeA

end CFSG.StandardType

end
