module

public import CFSG.Quasithin.Background.HSp4Rel
public import CFSG.Quasithin.Background.HSL3Alpha
public import CFSG.RankThree.SubgroupLists.SymplecticHeisenberg

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Assembly.LowTwoRank Matrix PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)
open CFSG.RankThree.SubgroupLists (spForm spE spForm_spE_left spForm_spE_right spForm_self
  spForm_mulVec exists_mem_statedSp_mulVec_eq)
open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

variable {K : Type} [Field K]

@[expose] def fixLin (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {v | M *ᵥ v = v}
  add_mem' := fun {v w} hv hw => by
    change M *ᵥ (v + w) = v + w
    rw [Matrix.mulVec_add, hv, hw]
  zero_mem' := Matrix.mulVec_zero M
  smul_mem' := fun c v hv => by
    change M *ᵥ (c • v) = c • v
    rw [Matrix.mulVec_smul, hv]

theorem mem_fixLin {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ fixLin M ↔ M *ᵥ v = v := Iff.rfl

theorem card_fix_natAut [Finite K] (γ : StatedSp 2 K) :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // natAut (StatedSp 2 K) γ v = v} =
      Nat.card K ^ Module.finrank K (fixLin (((γ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
  rw [← Module.natCard_eq_pow_finrank (K := K) (V := fixLin _)]
  exact Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd v.1, congrArg Multiplicative.toAdd v.2⟩
      invFun := fun w => ⟨Multiplicative.ofAdd w.1, congrArg Multiplicative.ofAdd w.2⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }

theorem eq_one_of_forall_mulVec {γ : StatedSp 2 K}
    (h : ∀ v, ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v) :
    γ = 1 := by
  refine CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    (Matrix.ext_iff_mulVec.mpr fun v => ?_)
  rw [h v]
  simp

theorem finrank_fixLin_le_three {γ : StatedSp 2 K} (hγ : γ ≠ 1) :
    Module.finrank K (fixLin (((γ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) ≤ 3 := by
  have hne : fixLin (((γ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ≠ ⊤ := by
    intro h
    apply hγ
    refine eq_one_of_forall_mulVec fun v => ?_
    have : v ∈ fixLin (((γ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [h]; trivial
    exact this
  have := Submodule.finrank_lt hne
  rw [Module.finrank_fintype_fun_eq_card] at this
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

theorem eq_upSp_of_sub_mem {g : StatedSp 2 K}
    (hg : ∀ v, ∃ t : K, ((g : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v - v = t • spE) :
    ∃ l : K, g = upSp (sym2_transpose l 0 0) := by
  choose φ hφ using hg
  have hφ' : ∀ v, ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      v + φ v • spE := fun v => (sub_eq_iff_eq_add'.mp (hφ v))
  have key : ∀ v w : Fin 2 ⊕ Fin 2 → K, φ v * w ι₂ = φ w * v ι₂ := by
    intro v w
    have h := spForm_mulVec g.2 v w
    rw [hφ', hφ'] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_self, spForm_spE_left, spForm_spE_right] at h
    linear_combination h
  refine ⟨φ (Pi.single ι₂ 1), ?_⟩
  refine CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    (Matrix.ext_iff_mulVec.mpr fun v => ?_)
  rw [hφ', coe_upSp, up_mulVec]
  have hv := key v (Pi.single ι₂ 1)
  simp only [Pi.single_eq_same, mul_one] at hv
  rw [hv]
  ext i
  simp [spE, Pi.single_apply]

variable [CharP K 2]

theorem card_fix_tauSp_le_of_three [Finite K] {B : StatedSp 2 K} (hB : B ≠ 1)
    (h3 : 3 ≤ Module.finrank K (fixLin (((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))) :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // natAut (StatedSp 2 K) (tauSp B) v = v} ≤
      Nat.card K ^ 2 := by
  classical
  set M := ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  let N : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) := Matrix.toLin' M - LinearMap.id
  have hNv : ∀ v, N v = M *ᵥ v - v := fun v => by simp [N]
  have hker : LinearMap.ker N = fixLin M := by
    ext v
    rw [LinearMap.mem_ker, hNv, sub_eq_zero, mem_fixLin]
  have hrank : Module.finrank K (LinearMap.range N) ≤ 1 := by
    have := LinearMap.finrank_range_add_finrank_ker N
    rw [hker, Module.finrank_fintype_fun_eq_card] at this
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨c₀, hc₀⟩ := finrank_le_one_iff.mp hrank
  set c : Fin 2 ⊕ Fin 2 → K := (c₀ : Fin 2 ⊕ Fin 2 → K) with hc
  have hNc : ∀ v, ∃ t : K, M *ᵥ v - v = t • c := by
    intro v
    obtain ⟨t, ht⟩ := hc₀ ⟨N v, LinearMap.mem_range_self N v⟩
    refine ⟨t, ?_⟩
    have := congrArg Subtype.val ht
    rw [← hNv]
    exact this.symm
  have hc0 : c ≠ 0 := by
    intro h0
    apply hB
    refine eq_one_of_forall_mulVec fun v => ?_
    obtain ⟨t, ht⟩ := hNc v
    rw [h0, smul_zero, sub_eq_zero] at ht
    exact ht
  have hE : (spE : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h ι₀
    simp [spE] at this
  obtain ⟨h, hh, hhc⟩ := exists_mem_statedSp_mulVec_eq hE hc0
  set hS : StatedSp 2 K := ⟨h, hh⟩ with hhS
  set B' := hS⁻¹ * B * hS with hB'
  have hB'M : ((B' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M *
        (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [hB']
    rfl
  have hhinv : ∀ v, ((h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      ((h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinvc : ((h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ c =
      spE := by
    rw [← hhc, hhinv]
  have hB'sub : ∀ v, ∃ t : K, ((B' : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v - v = t • spE := by
    intro v
    obtain ⟨t, ht⟩ := hNc ((h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)
    refine ⟨t, ?_⟩
    rw [hB'M, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e : M *ᵥ ((h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + t • c :=
      (sub_eq_iff_eq_add'.mp ht)
    rw [e, Matrix.mulVec_add, hhinv, Matrix.mulVec_smul, hinvc, add_sub_cancel_left]
  obtain ⟨l, hl⟩ := eq_upSp_of_sub_mem hB'sub
  have hl0 : l ≠ 0 := by
    intro h0
    apply hB
    have : B' = 1 := by
      rw [hl, h0]
      refine eq_one_of_forall_mulVec fun v => ?_
      rw [coe_upSp, up_mulVec]
      simp
    have hBe : B = hS * B' * hS⁻¹ := by rw [hB']; group
    rw [hBe, this, mul_one, mul_inv_cancel]
  have hBe : B = hS * B' * hS⁻¹ := by rw [hB']; group
  have hτ : natAut (StatedSp 2 K) (tauSp B) = natAut (StatedSp 2 K) (tauSp hS) *
      natAut (StatedSp 2 K) (tauSp B') * (natAut (StatedSp 2 K) (tauSp hS))⁻¹ := by
    rw [hBe, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  rw [hτ, card_fix_conj, hl]
  calc Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K //
        natAut (StatedSp 2 K) (tauSp (upSp (sym2_transpose l 0 0))) v = v}
      ≤ Nat.card (K × K) := by
        refine Nat.card_le_card_of_injective
          (fun v => (Multiplicative.toAdd v.1 ι₀, Multiplicative.toAdd v.1 ι₁)) ?_
        intro v w hvw
        have hfix : ∀ z : {v : StdMod (Fin 2 ⊕ Fin 2) K //
            natAut (StatedSp 2 K) (tauSp (upSp (sym2_transpose l 0 0))) v = v},
            Multiplicative.toAdd z.1 ι₂ = 0 ∧ Multiplicative.toAdd z.1 ι₃ = 0 := by
          intro z
          have h1 := congrArg Multiplicative.toAdd z.2
          change (((tauSp (upSp (sym2_transpose l 0 0)) : StatedSp 2 K) :
            GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
              Multiplicative.toAdd z.1 = Multiplicative.toAdd z.1 at h1
          rw [tauSp_upSp_diag_mulVec] at h1
          have e0 := congrFun h1 ι₀
          have e1 := congrFun h1 ι₁
          simp at e0 e1
          exact ⟨e1.resolve_left hl0, e0.resolve_left hl0⟩
        have h0 := congrArg Prod.fst hvw
        have h1 := congrArg Prod.snd hvw
        apply Subtype.ext
        change Multiplicative.toAdd v.1 = Multiplicative.toAdd w.1
        funext i
        rcases i with i | i <;> fin_cases i
        · exact h0
        · exact h1
        · exact (hfix v).1.trans (hfix w).1.symm
        · exact (hfix v).2.trans (hfix w).2.symm
    _ = Nat.card K ^ 2 := by rw [Nat.card_prod, sq]

theorem eq_one_of_pow_four {x : K} (h : x ^ 4 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (x - 1) ^ 4 = 0 := by
    linear_combination h + (-2 * x ^ 3 + 3 * x ^ 2 - 2 * x + 1) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem eq_of_smul_sq {x : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} (B : StatedSp 2 K) (D : K)
    (hx : ∀ v, toAddMap x v = D • (((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)) (hx2 : x * x = 1) :
    x = natAut (StatedSp 2 K) B ∧ B * B = 1 := by
  have hform : ∀ v w, spForm 2 K (toAddMap x v) (toAddMap x w) = D ^ 2 * spForm 2 K v w := by
    intro v w
    rw [hx, hx]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, spForm_mulVec B.2]
    ring
  have hD : D = 1 := by
    have hxx : ∀ v, toAddMap x (toAddMap x v) = v := fun v => by
      rw [← toAddMap_mul, hx2, toAddMap_one]
    have h1 := hform (toAddMap x spE) (toAddMap x (Pi.single ι₂ 1))
    rw [hform spE (Pi.single ι₂ 1), hxx, hxx, spForm_spE_left] at h1
    simp only [Pi.single_eq_same] at h1
    apply eq_one_of_pow_four
    linear_combination -h1
  have hxB : x = natAut (StatedSp 2 K) B := toAddMap_injective fun v => by
    rw [hx, hD, one_smul, toAddMap_natAut]
  refine ⟨hxB, ?_⟩
  apply natAut_injective (StatedSp 2 K)
  rw [map_mul, map_one, ← hxB, hx2]

theorem eq_pairHom_of_linear [Finite K] {a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hx : pairAut a b ∈ pairNormSp K) (hx2 : pairAut a b * pairAut a b = 1)
    (hlin : IsSemilinear a (RingEquiv.refl K)) :
    ∃ B : StatedSp 2 K, B * B = 1 ∧ pairAut a b = pairHom (StatedSp 2 K) tauSp B := by
  obtain ⟨B, σ, D₁, D₂, ha, hb⟩ := exists_eq_of_mem_pairNormSp hx
  rw [pairAut_mul] at hx2
  obtain ⟨ha2, hb2⟩ := pairAut_injective (hx2.trans pairAut_one.symm)
  have hD₁ : D₁ ≠ 0 := by
    intro h0
    have h1 := ha spE
    rw [h0, zero_smul, toAddMap_eq_zero_iff] at h1
    have := congrFun h1 ι₀
    simp [spE] at this
  have hsl : IsSemilinear a σ := by
    intro c v
    rw [ha, ha]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [show (fun i => σ c * σ (v i)) = σ c • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
      smul_comm]
  have hσ : σ = RingEquiv.refl K := hsl.unique hlin
  subst hσ
  have ha' : ∀ v, toAddMap a v = D₁ • (((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := fun v => ha v
  have hb' : ∀ v, toAddMap b v = D₂ • ((((tauSp B : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := fun v => hb v
  obtain ⟨haB, hB2⟩ := eq_of_smul_sq B D₁ ha' ha2
  obtain ⟨hbB, -⟩ := eq_of_smul_sq (tauSp B) D₂ hb' hb2
  exact ⟨B, hB2, by rw [haB, hbB, pairHom_apply]⟩

omit [CharP K 2] in
theorem card_fixV_pairAut (a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) :
    Nat.card ↥(fixV (Subgroup.zpowers (pairAut a b))) =
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // a v = v} *
        Nat.card {w : StdMod (Fin 2 ⊕ Fin 2) K // b w = w} := by
  rw [← card_fix_pairAut]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixV_zpowers_iff)

omit [CharP K 2] in
theorem card_fix_eq_card_fixV (g : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // g v = v} =
      Nat.card ↥(fixV (Subgroup.zpowers g)) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixV_zpowers_iff.symm)

theorem le_rkIdx_fixV_of_involution [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {t : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)} (htN : t ∈ pairNormSp K) (ht : orderOf t = 2) :
    3 * n ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (8 * n) := by
    rw [Nat.card_prod, card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      ← pow_add]
    congr 1
    ring
  have hq : ∀ k : ℕ, Nat.card K ^ k = 2 ^ (n * k) := fun k => by rw [hK, ← pow_mul]
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    rw [← sq]
    exact this
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  suffices h : Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ 2 ^ (5 * n) by
    refine SL3Pair.le_rkIdx_of_card_mul_le hV _ ?_
    calc Nat.card ↥(fixV (Subgroup.zpowers t)) * 2 ^ (3 * n) ≤ 2 ^ (5 * n) * 2 ^ (3 * n) :=
          Nat.mul_le_mul_right _ h
      _ = 2 ^ (8 * n) := by rw [← pow_add]; congr 1; ring
  rcases map_V₁_eq_or htN with h1 | h1
  ·
    obtain ⟨a, b, rfl⟩ := exists_pairAut htN h1
    obtain ⟨B, σ, D₁, D₂, ha, hb⟩ := exists_eq_of_mem_pairNormSp htN
    rw [pairAut_mul] at ht2
    obtain ⟨ha2, hb2⟩ := pairAut_injective (ht2.trans pairAut_one.symm)
    have hslof : ∀ (x : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) (C : StatedSp 2 K) (D : K),
        (∀ v, toAddMap x v = D • (((C : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ fun i => σ (v i))) →
        IsSemilinear x σ := by
      intro x C D hxv c v
      rw [hxv, hxv]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      rw [show (fun i => σ c * σ (v i)) = σ c • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
        smul_comm]
    have hsla := hslof a B D₁ ha
    have hslb := hslof b (tauSp B) D₂ hb
    rw [card_fixV_pairAut]
    by_cases hσ : σ = RingEquiv.refl K
    ·
      subst hσ
      obtain ⟨C, hC2, hCe⟩ := eq_pairHom_of_linear htN
        (by rw [pairAut_mul]; rw [ha2, hb2]; rfl) hsla
      rw [pairHom_apply] at hCe
      obtain ⟨rfl, rfl⟩ := pairAut_injective hCe
      have hC1 : C ≠ 1 := by
        rintro rfl
        apply ht1
        rw [hCe]
        simp only [map_one]
        rfl
      rw [card_fix_natAut, card_fix_natAut, hq, hq, ← pow_add]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have hd₁ := finrank_fixLin_le_three hC1
      have hτ1 : tauSp C ≠ 1 := by
        intro h
        apply hC1
        apply CFSG.QuasithinUnique.Lin2.Five.tauSp_bijective.1
        rw [h, map_one]
      have hd₂ := finrank_fixLin_le_three hτ1
      by_cases h3 : 3 ≤ Module.finrank K (fixLin (((C : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))
      · have hle := card_fix_tauSp_le_of_three hC1 h3
        rw [card_fix_natAut, hq, hq] at hle
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
        nlinarith
      · push Not at h3
        nlinarith
    ·
      have hsl2 : ∀ x : MulAut (StdMod (Fin 2 ⊕ Fin 2) K), IsSemilinear x σ → x * x = 1 →
          Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // x v = v} = 2 ^ (2 * n) := by
        intro x hx hx2
        obtain ⟨-, h⟩ := rkIdx_fixV_of_semilinear_two hn hK hx hσ (by rw [sq]; exact hx2)
        simp only [Fintype.card_sum, Fintype.card_fin] at h
        have hW : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (4 * n) := by
          rw [card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul]
          congr 1
          ring
        rw [card_fix_eq_card_fixV, SL3Pair.card_eq_two_pow_sub_rkIdx hW]
        congr 1
        omega
      rw [hsl2 a hsla ha2, hsl2 b hslb hb2, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    have hinj : Function.Injective (fun x : ↥(fixV (Subgroup.zpowers t)) =>
        ((x : PairMod (Fin 2 ⊕ Fin 2) K).2)) := by
      intro x y hxy
      have hxy' : (x : PairMod (Fin 2 ⊕ Fin 2) K).2 = (y : PairMod (Fin 2 ⊕ Fin 2) K).2 := hxy
      have hx := mem_fixV_zpowers_iff.mp x.2
      have hy := mem_fixV_zpowers_iff.mp y.2
      set z : PairMod (Fin 2 ⊕ Fin 2) K := (x : PairMod (Fin 2 ⊕ Fin 2) K) *
        (y : PairMod (Fin 2 ⊕ Fin 2) K)⁻¹ with hz
      have hzV : z ∈ V₁ (Fin 2 ⊕ Fin 2) K := by
        rw [mem_V₁, hz, Prod.snd_mul, Prod.snd_inv]
        rw [hxy', mul_inv_cancel]
      have hzt : t z = z := by rw [hz, map_mul, map_inv, hx, hy]
      have := eq_one_of_fix_of_map_V₂ h1 hzV hzt
      rw [hz, mul_inv_eq_one] at this
      exact Subtype.ext this
    have h4 := Nat.card_le_card_of_injective _ hinj
    rw [card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul] at h4
    exact h4.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem le_mParam [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hXN : X ≤ pairNormSp K) :
    3 * n ≤ E3.mParam X := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  unfold E3.mParam
  split_ifs with hev
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), t.2,
      by rw [← Subgroup.orderOf_coe] at ht; exact ht, rfl⟩ ?_
    rintro k ⟨s, hsX, hs, rfl⟩
    exact le_rkIdx_fixV_of_involution hn hK (hXN hsX) hs
  · have hV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (8 * n) := by
      rw [Nat.card_prod, card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul,
        ← pow_add]
      congr 1
      ring
    unfold rk
    rw [hV, padicValNat.prime_pow]
    omega

end Sp4

end H

end CFSG.Quasithin
