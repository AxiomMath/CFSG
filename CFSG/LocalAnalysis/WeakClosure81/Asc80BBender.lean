module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BFrame

import CFSG.CGT.T75M.SzOut
import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed
import CFSG.Models.Blueprint
import CFSG.Goldschmidt75.Closure
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiCatalogue
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega4
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.Quasithin.EmptyFaithful.SBd14Ctx
import CFSG.RankThree.S4Free.Stellmacher24Sz
import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

private theorem inl_gammaToMulAut_conj {F : Type} [Field F] (a : Gamma F) (u : SL(2, F)) :
    (SemidirectProduct.inl (gammaToMulAut F a u) : Gamma F) =
      a * SemidirectProduct.inl u * a⁻¹ := by
  have hgen : ∀ A B C : Gamma F, (A * B) * C * (A * B)⁻¹ = A * (B * C * B⁻¹) * A⁻¹ := by
    intro A B C
    group
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right a]
  symm
  calc (SemidirectProduct.inl a.left * SemidirectProduct.inr a.right) *
        SemidirectProduct.inl u *
        (SemidirectProduct.inl a.left * SemidirectProduct.inr a.right)⁻¹
      = SemidirectProduct.inl a.left *
          (SemidirectProduct.inr a.right * SemidirectProduct.inl u *
            (SemidirectProduct.inr a.right)⁻¹) * (SemidirectProduct.inl a.left)⁻¹ :=
        hgen (SemidirectProduct.inl a.left) (SemidirectProduct.inr a.right)
          (SemidirectProduct.inl u)
    _ = SemidirectProduct.inl a.left *
          SemidirectProduct.inl (sl2FieldAction a.right u) *
          (SemidirectProduct.inl a.left)⁻¹ := by
        have hmap : (SemidirectProduct.inr a.right : Gamma F)⁻¹ =
            SemidirectProduct.inr a.right⁻¹ := by
          ext <;> simp
        have h : (SemidirectProduct.inr a.right * SemidirectProduct.inl u *
            (SemidirectProduct.inr a.right)⁻¹ : Gamma F) =
            SemidirectProduct.inl (sl2FieldAction a.right u) := by
          rw [hmap]
          exact (SemidirectProduct.inl_aut (φ := sl2FieldAction) a.right u).symm
        exact congrArg (fun z => SemidirectProduct.inl a.left * z *
          (SemidirectProduct.inl a.left)⁻¹) h
    _ = SemidirectProduct.inl (a.left * sl2FieldAction a.right u * a.left⁻¹) := by
        rw [← map_mul, ← map_inv, ← map_mul]
    _ = SemidirectProduct.inl (gammaToMulAut F a u) := rfl

theorem exists_fixed_involutions_of_outer_sl2 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) (φ : MulAut SL(2, F)) (hφ : φ * φ = 1)
    (hout : φ ∉ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range) :
    ∃ u v : SL(2, F), φ u = u ∧ φ v = v ∧ orderOf u = 2 ∧ orderOf v = 2 ∧
      orderOf (u * v) = 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := char_two_of_card hcard
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨a, rfl⟩ := (gammaToMulAut_bijective_of_card hcard).2 φ
  have haa : a * a = 1 := by
    apply (gammaToMulAut_bijective_of_card hcard).1
    rw [map_mul, hφ, map_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have ha_ne : a ≠ 1 := by
    intro h
    apply hout
    rw [h]
    exact ⟨1, by simp⟩
  have haord : orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha_ne
  have haout : a ∉ linearKernel F := by
    intro hmem
    apply hout
    have hmap : gammaToMulAut F a ∈ (linearKernel F).map (gammaToMulAut F) :=
      Subgroup.mem_map.mpr ⟨a, hmem, rfl⟩
    rwa [linearKernel_map_gammaToMulAut] at hmap
  obtain ⟨-, -, -, -, -, x, -, hcent⟩ :=
    original_outer_involution_field_conjugacy_and_centralizer hn hcard a haord haout
  let u₀ : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let v₀ : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hu₀fix : sl2FieldAction a.right u₀ = u₀ := by
    apply Subtype.ext
    rw [sl2FieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u₀]
  have hv₀fix : sl2FieldAction a.right v₀ = v₀ := by
    apply Subtype.ext
    rw [sl2FieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v₀]
  let u : SL(2, F) := x * u₀ * x⁻¹
  let v : SL(2, F) := x * v₀ * x⁻¹
  have hu_cent : u ∈ centralizerS a := by
    rw [hcent]
    refine Subgroup.mem_map.mpr ⟨u₀, (sl2_field_fixed_iff a.right u₀).mp hu₀fix, ?_⟩
    change (MulAut.conj x) u₀ = u
    rw [MulAut.conj_apply]
  have hv_cent : v ∈ centralizerS a := by
    rw [hcent]
    refine Subgroup.mem_map.mpr ⟨v₀, (sl2_field_fixed_iff a.right v₀).mp hv₀fix, ?_⟩
    change (MulAut.conj x) v₀ = v
    rw [MulAut.conj_apply]
  have hu_comm : (SemidirectProduct.inl u : Gamma F) * a = a * SemidirectProduct.inl u :=
    (mem_centralizerS_iff a u).mp hu_cent
  have hv_comm : (SemidirectProduct.inl v : Gamma F) * a = a * SemidirectProduct.inl v :=
    (mem_centralizerS_iff a v).mp hv_cent
  have hu_fixed : gammaToMulAut F a u = u := by
    have h : (SemidirectProduct.inl (gammaToMulAut F a u) : Gamma F) =
        SemidirectProduct.inl u := by
      rw [inl_gammaToMulAut_conj]
      rw [← hu_comm, mul_assoc, mul_inv_cancel, mul_one]
    exact SemidirectProduct.inl_injective h
  have hv_fixed : gammaToMulAut F a v = v := by
    have h : (SemidirectProduct.inl (gammaToMulAut F a v) : Gamma F) =
        SemidirectProduct.inl v := by
      rw [inl_gammaToMulAut_conj]
      rw [← hv_comm, mul_assoc, mul_inv_cancel, mul_one]
    exact SemidirectProduct.inl_injective h
  have hu₀_sq : u₀ * u₀ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u₀, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination htwo
  have hu₀_ne : u₀ ≠ 1 := by
    intro h
    have h01 := congrFun (congrFun (congrArg
      (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h) 0) 1
    simp [u₀] at h01
  have hv₀_sq : v₀ * v₀ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [v₀, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination htwo
  have hv₀_ne : v₀ ≠ 1 := by
    intro h
    have h10 := congrFun (congrFun (congrArg
      (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h) 1) 0
    simp [v₀] at h10
  have hu₀_ord : orderOf u₀ = 2 := orderOf_eq_prime (by rwa [pow_two]) hu₀_ne
  have hv₀_ord : orderOf v₀ = 2 := orderOf_eq_prime (by rwa [pow_two]) hv₀_ne
  have hu₀v₀ : ((u₀ * v₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u₀, v₀, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination htwo
  have hu₀v₀_ne : u₀ * v₀ ≠ 1 := by
    intro h
    have h00 := congrFun (congrFun (congrArg
      (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h) 0) 0
    rw [hu₀v₀] at h00
    simp at h00
  have hu₀v₀_ord : orderOf (u₀ * v₀) = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      change (((u₀ * v₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) ^ 3 = 1
      rw [hu₀v₀]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination htwo
    · exact hu₀v₀_ne
  refine ⟨u, v, hu_fixed, hv_fixed, ?_, ?_, ?_⟩
  · rw [show u = x * u₀ * x⁻¹ from rfl, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hu₀_ord
  · rw [show v = x * v₀ * x⁻¹ from rfl, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hv₀_ord
  · have huv : u * v = x * (u₀ * v₀) * x⁻¹ := by
      simp only [u, v]
      group
    rw [huv, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hu₀v₀_ord


private noncomputable def conjOnNormal {G : Type} [Group G] {H L : Subgroup G}
    (hLH : L ≤ H) (hLnorm : (L.subgroupOf H).Normal) (a : G) (haH : a ∈ H) : MulAut ↥L :=
  Subgroup.normalizerMonoidHom L
    ⟨a, (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLnorm haH⟩

private theorem conjOnNormal_apply_coe {G : Type} [Group G] {H L : Subgroup G}
    (hLH : L ≤ H) (hLnorm : (L.subgroupOf H).Normal) (a : G) (haH : a ∈ H) (y : ↥L) :
    ((conjOnNormal hLH hLnorm a haH y : ↥L) : G) = a * (y : G) * a⁻¹ := by
  simp [conjOnNormal, Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem conjOnNormal_mul_self {G : Type} [Group G] {H L : Subgroup G}
    (hLH : L ≤ H) (hLnorm : (L.subgroupOf H).Normal) {a : G} (haH : a ∈ H)
    (haa : a * a = 1) :
    conjOnNormal hLH hLnorm a haH * conjOnNormal hLH hLnorm a haH = 1 := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  rw [MulAut.mul_apply, conjOnNormal_apply_coe, conjOnNormal_apply_coe]
  rw [show a * (a * (y : G) * a⁻¹) * a⁻¹ = (a * a) * (y : G) * (a⁻¹ * a⁻¹) from by group,
    haa, hainv, haa]
  simp

private theorem mem_of_conjOnNormal_eq_conj {G : Type} [Group G] {H L : Subgroup G}
    (hLH : L ≤ H) (hLnorm : (L.subgroupOf H).Normal)
    (hinf : H ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {a : G} (haH : a ∈ H) {l : ↥L}
    (hconj : conjOnNormal hLH hLnorm a haH = MulAut.conj l) : a ∈ L := by
  have hcent : (l : G)⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : a * y * a⁻¹ = (l : G) * y * (l : G)⁻¹ := by
      have := congrArg (fun f : MulAut ↥L => ((f ⟨y, hy⟩ : ↥L) : G)) hconj
      simpa [conjOnNormal_apply_coe, MulAut.conj_apply] using this
    have hcy : ((l : G)⁻¹ * a) * y = y * ((l : G)⁻¹ * a) := by
      calc ((l : G)⁻¹ * a) * y = (l : G)⁻¹ * (a * y * a⁻¹) * a := by group
        _ = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * a := by rw [h1]
        _ = y * ((l : G)⁻¹ * a) := by group
    exact hcy.symm
  have hcH : (l : G)⁻¹ * a ∈ H := H.mul_mem (H.inv_mem (hLH l.2)) haH
  have hcbot : (l : G)⁻¹ * a ∈ (⊥ : Subgroup G) := by
    rw [← hinf]
    exact Subgroup.mem_inf.mpr ⟨hcH, hcent⟩
  have hc1 : (l : G)⁻¹ * a = 1 := Subgroup.mem_bot.mp hcbot
  have haeq : a = (l : G) := by
    have := congrArg (fun x => (l : G) * x) hc1
    simpa [mul_assoc] using this
  rw [haeq]
  exact l.2

private theorem asc80B_eq_normalizer {G : Type} [Group G] [Finite G] {H A M : Subgroup G}
    (S : Asc80BSetup H A M) (hAH : A ≤ H) (hHsimple : IsSimpleGroup ↥H)
    {T : Subgroup G} (hT : IsSylowIn 2 T H) (hAT : A ≤ T)
    (B : Sylow 2 ↥H) (hB : (B : Subgroup ↥H) = T.subgroupOf H)
    (hN : ∀ P : Subgroup ↥H, (B : Subgroup ↥H) ≤ P → P ≠ ⊤ →
      P ≤ Subgroup.normalizer (B : Set ↥H)) :
    M = H ⊓ Subgroup.normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTmax := S.maxOver_sylow hT hAT
  have hTM : T ≤ M := (isUniqueMaxOver_iff.mp hTmax).2.1
  have hTlt : T < H := lt_of_le_of_lt hTM (isUniqueMaxOver_iff.mp hTmax).1.1
  have hMmax : IsMaxSubgroupIn H M := (isUniqueMaxOver_iff.mp S.maxOver_eq).1
  have hMH : M ≤ H := hMmax.1.le
  have hMT : T.subgroupOf H ≤ M.subgroupOf H := fun x hx => hTM hx
  have hMtop : M.subgroupOf H ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hMmax.1.ne (le_antisymm h hMH).symm
  have hMle : M ≤ H ⊓ Subgroup.normalizer (T : Set G) := by
    intro x hxM
    have hxH : x ∈ H := hMH hxM
    let xH : ↥H := ⟨x, hxH⟩
    have hxM' : xH ∈ M.subgroupOf H := hxM
    have hxN : xH ∈ Subgroup.normalizer ((B : Subgroup ↥H) : Set ↥H) :=
      hN (M.subgroupOf H) (hB ▸ hMT) hMtop hxM'
    refine ⟨hxH, ?_⟩
    exact CFSG.Goldschmidt75.mem_normalizer_of_mem_normalizer_subgroupOf hT.le (by simpa [hB] using hxN)
  have hAinf : A ≤ H ⊓ Subgroup.normalizer (T : Set G) :=
    le_inf hAH (hAT.trans Subgroup.le_normalizer)
  have hHne : H ⊓ Subgroup.normalizer (T : Set G) ≠ H := by
    intro heq
    have hHnorm : H ≤ Subgroup.normalizer (T : Set G) := heq ▸ inf_le_right
    have hTnormal : ((T.subgroupOf H : Subgroup ↥H)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hT.le).mpr hHnorm
    haveI : ((T.subgroupOf H : Subgroup ↥H)).Normal := hTnormal
    haveI : IsSimpleGroup ↥H := hHsimple
    have hAsub : A.subgroupOf H ≤ T.subgroupOf H := fun x hx => hAT hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf H) with hbot | htop
    · have hAbot : A.subgroupOf H = ⊥ := le_bot_iff.mp (hAsub.trans_eq hbot)
      have hmap := Subgroup.map_subgroupOf_eq_of_le hAH
      rw [hAbot, Subgroup.map_bot] at hmap
      exact S.ne_bot hmap.symm
    · have hTeq : T = H := by
        have h := Subgroup.map_subgroupOf_eq_of_le hT.le
        rw [htop, Subgroup.map_top, Subgroup.range_subtype] at h
        exact h.symm
      exact (ne_of_lt hTlt) hTeq
  have hXlt : H ⊓ Subgroup.normalizer (T : Set G) < H :=
    lt_of_le_of_ne inf_le_left hHne
  exact le_antisymm hMle (S.le_of_lt _ hAinf hXlt)

theorem asc80ThmBCase_l2 :
    Asc80ThmBCase fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSL 2 2 f := by
  intro G _ _ H A M hs hnab hfam hAH hA hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hmod⟩ := hfam
  let L : Subgroup G := Fstar H
  have hsetup := asc80BSetup hs hnab hAH hA hM
  have hL2L : IsL2 ↥L f := CFSG.Models.LieModel.toBlueprint (by decide) hmod
  have hf2 : 2 ≤ f := (P22fin.isL2Ev_of_isL2 hL2L).2
  have hLnorm : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fstar_le_group H)).mp
      (normal_subgroupOf_fstar H)
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hAH hA.isPGroup
  have hAL : A ≤ L := by
    by_contra hnot
    rw [SetLike.not_le_iff_exists] at hnot
    obtain ⟨a, haA, haL⟩ := hnot
    have haH : a ∈ H := hAH haA
    have haa : a * a = 1 := by
      have := hA.2 a haA
      simpa [pow_two] using this
    have hσmul := conjOnNormal_mul_self (fstar_le_group H) (normal_subgroupOf_fstar H) haH haa
    have hσout : conjOnNormal (fstar_le_group H) (normal_subgroupOf_fstar H) a haH ∉
        (MulAut.conj : ↥L →* MulAut ↥L).range := by
      rintro ⟨l, hl⟩
      exact haL (mem_of_conjOnNormal_eq_conj (fstar_le_group H) (normal_subgroupOf_fstar H)
        hsetup.inf_centralizer haH hl.symm)
    obtain ⟨F, hField, hFinite, hCharP, hcardF, ⟨eSL⟩⟩ :=
      P22y.exists_equiv_sl2 (P22fin.isL2Ev_of_isL2 hL2L).1
    letI : Field F := hField
    letI : Finite F := hFinite
    letI : CharP F 2 := hCharP
    let ψ : MulAut SL(2, F) := MulAut.congr eSL
      (conjOnNormal (fstar_le_group H) (normal_subgroupOf_fstar H) a haH)
    have hψψ : ψ * ψ = 1 := by
      change MulAut.congr eSL (conjOnNormal (fstar_le_group H) (normal_subgroupOf_fstar H) a haH) *
          MulAut.congr eSL (conjOnNormal (fstar_le_group H) (normal_subgroupOf_fstar H) a haH) = 1
      rw [← map_mul, hσmul, map_one]
    have hψout : ψ ∉ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
      rintro ⟨g, hg⟩
      refine hσout ⟨eSL.symm g, ?_⟩
      have h1 : (MulAut.congr eSL).symm ψ =
          conjOnNormal (fstar_le_group H) (normal_subgroupOf_fstar H) a haH :=
        (MulAut.congr eSL).symm_apply_apply _
      have h2 : (MulAut.congr eSL).symm (MulAut.conj g) = MulAut.conj (eSL.symm g) := by
        apply MulEquiv.ext
        intro y
        change eSL.symm ((MulAut.conj g) (eSL y)) = MulAut.conj (eSL.symm g) y
        simp [MulAut.conj_apply]
      rw [← h1, ← hg]
      exact h2.symm
    obtain ⟨u, v, hu_fix, hv_fix, hu_ord, hv_ord, huv_ord⟩ :=
      exists_fixed_involutions_of_outer_sl2 (n := f) (by omega) hcardF ψ hψψ hψout
    let u' : ↥L := eSL.symm u
    let v' : ↥L := eSL.symm v
    have hu'_fix : conjOnNormal (fstar_le_group H) (normal_subgroupOf_fstar H) a haH u' = u' := by
      have := congrArg eSL.symm hu_fix
      simpa [u', ψ, MulAut.congr_apply] using this
    have hv'_fix : conjOnNormal (fstar_le_group H) (normal_subgroupOf_fstar H) a haH v' = v' := by
      have := congrArg eSL.symm hv_fix
      simpa [v', ψ, MulAut.congr_apply] using this
    have hu'_ord : orderOf u' = 2 := by
      rw [show u' = eSL.symm u from rfl, MulEquiv.orderOf_eq]
      exact hu_ord
    have hv'_ord : orderOf v' = 2 := by
      rw [show v' = eSL.symm v from rfl, MulEquiv.orderOf_eq]
      exact hv_ord
    have huv'_ord : orderOf (u' * v') = 3 := by
      have h : u' * v' = eSL.symm (u * v) := by simp [u', v']
      rw [h, MulEquiv.orderOf_eq]
      exact huv_ord
    let C : Subgroup G := H ⊓ Subgroup.centralizer ({a} : Set G)
    have hAC : A ≤ C := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨hAH hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, haA⟩ ⟨x, hx⟩)
    have hCne : C ≠ H := by
      intro hCH
      have haC : a ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyH : y ∈ H := fstar_le_group H hy
        have hmem : y ∈ C := hCH ▸ hyH
        exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2) a
          (Set.mem_singleton a)).symm
      have habot : a ∈ (⊥ : Subgroup G) := by
        rw [← hsetup.inf_centralizer]
        exact Subgroup.mem_inf.mpr ⟨haH, haC⟩
      have ha1 : a = 1 := Subgroup.mem_bot.mp habot
      exact haL (ha1 ▸ L.one_mem)
    have hClt : C < H := lt_of_le_of_ne inf_le_left hCne
    have hCM : C ≤ M := hsetup.le_of_lt C hAC hClt
    have hu'cent : (u' : G) ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 : a * (u' : G) * a⁻¹ = (u' : G) := by
        have := congrArg (fun z : ↥L => (z : G)) hu'_fix
        simpa [conjOnNormal_apply_coe] using this
      calc a * (u' : G) = (a * (u' : G) * a⁻¹) * a := by group
        _ = (u' : G) * a := by rw [h1]
    have hv'cent : (v' : G) ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 : a * (v' : G) * a⁻¹ = (v' : G) := by
        have := congrArg (fun z : ↥L => (z : G)) hv'_fix
        simpa [conjOnNormal_apply_coe] using this
      calc a * (v' : G) = (a * (v' : G) * a⁻¹) * a := by group
        _ = (v' : G) * a := by rw [h1]
    have hu'M : (u' : G) ∈ M :=
      hCM (Subgroup.mem_inf.mpr ⟨fstar_le_group H u'.2, hu'cent⟩)
    have hv'M : (v' : G) ∈ M :=
      hCM (Subgroup.mem_inf.mpr ⟨fstar_le_group H v'.2, hv'cent⟩)
    have hTtwo : IsSylowTwoOf T H :=
      ⟨hT.1, hT.2.1, by simpa [Subgroup.relIndex] using hT.2.2⟩
    have hTLsyl : IsSylowTwoOf (T ⊓ L) L :=
      CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hTtwo (fstar_le_group H) hLnorm
    have hTM : T ≤ M := (isUniqueMaxOver_iff.mp (hsetup.maxOver_sylow hT hAT)).2.1
    have hTML : T ⊓ L ≤ M ⊓ L := le_inf (inf_le_left.trans hTM) inf_le_right
    have hMLne : M ⊓ L ≠ L := by
      intro h
      exact hsetup.not_fstar_le (le_of_eq_of_le h.symm inf_le_left)
    have hTLsylIn : IsSylowIn 2 (T ⊓ L) L :=
      ⟨hTLsyl.1, hTLsyl.2.1, by simpa [Subgroup.relIndex] using hTLsyl.2.2⟩
    let B : Sylow 2 ↥L := hTLsylIn.toSylow
    have hBco : (B : Subgroup ↥L) = (T ⊓ L).subgroupOf L := by simp [B]
    have hPtop : (M ⊓ L).subgroupOf L ≠ ⊤ := by
      intro htop
      rw [Subgroup.subgroupOf_eq_top] at htop
      exact hMLne (le_antisymm htop inf_le_right).symm
    have hBP : (B : Subgroup ↥L) ≤ (M ⊓ L).subgroupOf L := by
      rw [hBco]
      exact Subgroup.subgroupOf_mono L hTML
    have hPle := l2_sylow_le_normalizer (m := f) hf2 hL2L B ((M ⊓ L).subgroupOf L) hBP hPtop
    have hMLnorm : M ⊓ L ≤ Subgroup.normalizer ((T ⊓ L) : Set G) := by
      intro x hx
      let xL : ↥L := ⟨x, hx.2⟩
      have hxP : xL ∈ (M ⊓ L).subgroupOf L := hx
      have hxN : xL ∈ Subgroup.normalizer ((B : Subgroup ↥L) : Set ↥L) := hPle hxP
      have hxN' : xL ∈ Subgroup.normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rwa [hBco] at hxN
      exact CFSG.Goldschmidt75.mem_normalizer_of_mem_normalizer_subgroupOf (S := L) (S₀ := T ⊓ L) inf_le_right hxN'
    have hu'T : (u' : G) ∈ T ⊓ L := by
      have hu'Gord : orderOf ((u' : G)) = 2 := (Subgroup.orderOf_coe u').trans hu'_ord
      have hX2 : IsPGroup 2 ↥(Subgroup.zpowers (u' : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu'Gord]; norm_num)
      have hXle : Subgroup.zpowers (u' : G) ≤ L := Subgroup.zpowers_le.mpr u'.2
      have hXN : Subgroup.zpowers (u' : G) ≤
          Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
        Subgroup.zpowers_le.mpr (hMLnorm (Subgroup.mem_inf.mpr ⟨hu'M, u'.2⟩))
      exact SBd14.le_Q_of_two hTLsyl hXle hXN hX2 (Subgroup.mem_zpowers _)
    have hv'T : (v' : G) ∈ T ⊓ L := by
      have hv'Gord : orderOf ((v' : G)) = 2 := (Subgroup.orderOf_coe v').trans hv'_ord
      have hX2 : IsPGroup 2 ↥(Subgroup.zpowers (v' : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv'Gord]; norm_num)
      have hXle : Subgroup.zpowers (v' : G) ≤ L := Subgroup.zpowers_le.mpr v'.2
      have hXN : Subgroup.zpowers (v' : G) ≤
          Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
        Subgroup.zpowers_le.mpr (hMLnorm (Subgroup.mem_inf.mpr ⟨hv'M, v'.2⟩))
      exact SBd14.le_Q_of_two hTLsyl hXle hXN hX2 (Subgroup.mem_zpowers _)
    have huv'T : ((u' * v' : ↥L) : G) ∈ T ⊓ L := by
      have hmem : (u' : G) * (v' : G) ∈ T ⊓ L := (T ⊓ L).mul_mem hu'T hv'T
      simpa [Subgroup.coe_mul] using hmem
    have huv'Gord : orderOf (((u' * v' : ↥L) : G)) = 3 :=
      (Subgroup.orderOf_coe (u' * v')).trans huv'_ord
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTLsyl.2.1) ⟨_, huv'T⟩
    have h3 : 3 = 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_coe, huv'Gord]
    have hdvd : 3 ∣ 2 ^ k := h3 ▸ dvd_refl 3
    have hdiv : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) hdiv
  have hH : H = L := by
    rw [hsetup.eq_sup]
    exact sup_eq_left.mpr hAL
  haveI : IsSimpleGroup ↥L := hs
  have hHsimple : IsSimpleGroup ↥H := (MulEquiv.subgroupCongr hH).isSimpleGroup
  have hL2H : IsL2 ↥H f :=
    CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hH).symm hL2L
  let B : Sylow 2 ↥H := hT.toSylow
  have hB : (B : Subgroup ↥H) = T.subgroupOf H := by simp [B]
  have hN : ∀ P : Subgroup ↥H, (B : Subgroup ↥H) ≤ P → P ≠ ⊤ →
      P ≤ Subgroup.normalizer (B : Set ↥H) := by
    intro P hP hPtop
    exact l2_sylow_le_normalizer hf2 hL2H B P hP hPtop
  refine ⟨⟨f, Or.inl hL2H⟩, T, hT, ?_⟩
  exact asc80B_eq_normalizer hsetup hAH hHsimple hT hAT B hB hN

theorem asc80ThmBCase_sz :
    Asc80ThmBCase fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .twistedB2 n 2 f := by
  intro G _ _ H A M hs hnab hfam hAH hA hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, f, hmod⟩ := hfam
  let L : Subgroup G := Fstar H
  have hsetup := asc80BSetup hs hnab hAH hA hM
  have hSzL : IsSz ↥L f := by
    obtain ⟨-, hcl | ⟨-, d, hnames, ⟨eTAU⟩⟩⟩ := hmod
    · rcases hcl with ⟨-, hfalse⟩
      exact hfalse.elim
    · obtain ⟨idx, hv⟩ := d
      obtain ⟨m, rfl⟩ : ∃ m, idx = .suzuki m := by
        cases idx <;> simp [CFSG.Models.NamesTag] at hnames ⊢
      have hf : f = 2 * m + 1 := by simpa [CFSG.Models.NamesTag] using hnames
      have hm1 : 1 ≤ m :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
          ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      have hcardK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ f := by
        rw [GaloisField.card 2 (2 * m + 1) (by omega), hf]
      have hmodel : CFSG.Blueprint.SuzukiModel ↥L 2 f :=
        ⟨rfl, m, hm1, GaloisField 2 (2 * m + 1), inferInstance, inferInstance, hf, hcardK,
          ⟨eTAU.trans (CFSG.LocalAnalysis.GLTheoremA.suzukiCatalogueEquiv m hv).symm⟩⟩
      exact CFSG.Blueprint.LieModel.twistedB2_iff.mpr ⟨rfl, hmodel⟩
  have hLnorm : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fstar_le_group H)).mp
      (normal_subgroupOf_fstar H)
  have hAL : A ≤ L := by
    by_contra hnot
    rw [SetLike.not_le_iff_exists] at hnot
    obtain ⟨a, haA, haL⟩ := hnot
    have haH : a ∈ H := hAH haA
    have haa : a * a = 1 := by
      have := hA.2 a haA
      simpa [pow_two] using this
    have hσmul := conjOnNormal_mul_self (fstar_le_group H) (normal_subgroupOf_fstar H) haH haa
    obtain ⟨b, hb1, -, ⟨eSz⟩⟩ :=
      CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSzL
    have hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L)) :=
      CFSG.CGT.T75M.sz_outer_odd hb1 eSz
    obtain ⟨g, hg⟩ := CFSG.CGT.T75M.exists_conj_of_mul_self_eq_one hodd hσmul
    exact haL (mem_of_conjOnNormal_eq_conj (fstar_le_group H) (normal_subgroupOf_fstar H)
      hsetup.inf_centralizer haH hg)
  have hH : H = L := by
    rw [hsetup.eq_sup]
    exact sup_eq_left.mpr hAL
  haveI : IsSimpleGroup ↥L := hs
  have hHsimple : IsSimpleGroup ↥H := (MulEquiv.subgroupCongr hH).isSimpleGroup
  have hSzH : IsSz ↥H f :=
    CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hH).symm hSzL
  have hSzModelH : CFSG.Blueprint.SuzukiModel ↥H 2 f :=
    (CFSG.Blueprint.LieModel.suzukiModel hSzH).2
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hAH hA.isPGroup
  let B : Sylow 2 ↥H := hT.toSylow
  have hB : (B : Subgroup ↥H) = T.subgroupOf H := by simp [B]
  have hN : ∀ P : Subgroup ↥H, (B : Subgroup ↥H) ≤ P → P ≠ ⊤ →
      P ≤ Subgroup.normalizer (B : Set ↥H) := by
    intro P hP hPtop
    obtain ⟨-, b, hb1, K, hField, hFinite, hfK, hKcard, ⟨eK⟩⟩ := hSzModelH
    letI : Field K := hField
    letI : Finite K := hFinite
    have hKcard' : Nat.card K = 2 ^ (2 * b + 1) := by
      rw [← hfK]
      exact hKcard
    exact CFSG.RankThree.S4Free.Suzuki.le_normalizer_of_sylow_le hb1 hKcard' eK B hP hPtop
  refine ⟨⟨f, Or.inr hSzH⟩, T, hT, ?_⟩
  exact asc80B_eq_normalizer hsetup hAH hHsimple hT hAT B hB hN

end CFSG.LocalAnalysis.WeakClosure81

end
