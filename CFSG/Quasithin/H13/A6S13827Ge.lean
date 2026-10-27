module

public import CFSG.Quasithin.H13.A6S13827Gd
public import CFSG.Quasithin.H13.A6S13824f
public import CFSG.Quasithin.H13.A6S13824g
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem dk_of_psu33 (h16 : Lem13816) (h21 : Lem13821) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) (hU : IsPSU 3 3 1 ↥(S.KSt H K)) :
    S.DK H K := by
  obtain ⟨hL1K, -, ⟨hKT, -⟩, hUK⟩ := h21 G T L V S hS H hH K hK
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hsimp : IsSimpleGroup ↥(S.KSt H K) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hU).2
  have hnab : ∃ k ∈ K, ∃ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∉ pCoreOf 2 H := by
    obtain ⟨f, hfs, hfk⟩ := exists_kst_hom hS hH hKH
    by_contra hall
    push Not at hall
    have hc : ∀ a b : ↥(S.KSt H K), a * b = b * a := by
      intro a b
      obtain ⟨k, rfl⟩ := hfs a
      obtain ⟨k', rfl⟩ := hfs b
      have h1 : f (k * k' * k⁻¹ * k'⁻¹) = 1 := (hfk _).2 (by simpa using hall k k.2 k' k'.2)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc f k * f k' = f k * f k' * (f k)⁻¹ * (f k')⁻¹ * (f k' * f k) := by group
        _ = f k' * f k := by rw [h1, one_mul]
    have hcard : Nat.card ↥(S.KSt H K) = 6048 := by
      rw [GoldS146R.card_of_isPSU_three Nat.prime_three hU]
      decide
    let _ : CommGroup ↥(S.KSt H K) := { (inferInstance : Group ↥(S.KSt H K)) with mul_comm := hc }
    have := IsSimpleGroup.prime_card (α := ↥(S.KSt H K))
    rw [hcard] at this
    exact absurd this (by norm_num)
  exact ⟨hS, hH, hK, hKn, hKT.symm, hL1K, hUK, hsimp, hnab⟩

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem no_transv_u33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) :
    ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V) := by
  intro h hh ht
  have hF1 := hd.hF.toHypF91
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hd.hF.F911_3.1
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH)
  obtain ⟨c, hc⟩ := ht.2
  have hq := hsV.mem_pCoreOf_of_transvU33 hU (perfect_of_mem_cComp hd.hK) hh hc
  apply ht.1
  intro x hx
  rw [hF1.pCoreOf_eq_centralizerMod] at hq
  exact hq.2.2 x hx

theorem triv_of_max_u33
    (h21 : Lem13821) (h16 : Lem13816) (hU : IsPSU 3 3 1 ↥(S.KSt H K)) {W : Subgroup G}
    (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) :
    ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ fsuV1 T V := by
  by_contra hKW
  push Not at hKW
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) := isPGroup_of_isElemAbelian hF.F911_3
  have hW2 : IsPGroup 2 W := hU2.to_le hWU.le
  have hperf := perfect_of_mem_cComp hd.hK
  obtain ⟨-, -, hnt, hdich⟩ :=
    lem13822_holds h21 h16 G T L V S hd.hS H hd.hH K hd.hK W hV1W hWU hHW hKW
  obtain ⟨γ, γ', g, s, hDγ, hDH, -, hle, -⟩ := S.case2_of_no_transv hF hnt
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  have hsW := hd.secU le_rfl hV1W hWU.le hHW hF1.H_normalizes_V₁ hKW
  have hUγH := hF.Uγ_le_H s
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hr := hd.relIndex_Uγ_eq s
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg (Subtype.val : ↥(conjClosure S.V3 H) → G)
      (hF.F911_3.1.is_comm.comm ⟨a, hWU.le ha⟩ ⟨b, hWU.le hb⟩)
  have : IsMulCommutative ↥W := ⟨⟨fun a b => Subtype.ext (hWc a a.2 b b.2)⟩⟩
  rcases hdich γ γ' g s hDγ hDH hle with ⟨hA, hi, hieq⟩ | ⟨hA, hj, hjeq⟩
  ·
    rcases hi.lt_or_eq with hi | hi
    ·
      have h1 := hsU.relIndex_le_indexU33 hU hmax hUγH
        (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _)
      rw [hr, HypF98.relIndex_eq_two_pow_mIdx hU2] at h1
      have := A6Gen.le_of_two_pow_le h1
      omega
    ·
      obtain ⟨a, -, -, hA2⟩ := A6Gen.exists_gen_of_card_two (hF.card_A₁ (g := g))
      have hAN : F8.A₁ (fsuV1 T V) (g : G) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
        (hF.A₁_le_Uγ.trans hUγH).trans hF1.H_normalizes_V₁
      have hcomm := (hieq hi).2
      have hz : ∀ f ∈ F8.Uγ S.V3 H (g : G), ∀ x ∈ W, f * x * f⁻¹ * x⁻¹ ∈ fsuV1 T V ∨
          f * x * f⁻¹ * x⁻¹ * a⁻¹ ∈ fsuV1 T V := by
        intro f hf x hx
        have h1 := (F8.A₁ (fsuV1 T V) (g : G) ⊔ fsuV1 T V).inv_mem
          (hcomm (Subgroup.commutator_mem_commutator hx hf))
        have e : (⁅x, f⁆)⁻¹ = f * x * f⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
        rw [e] at h1
        exact A6Gen.mem_or_mul_inv_mem_of_sup hAN hA2 h1
      exact hd.not_Uγ_le s hDγ (hsW.le_pCoreOf_of_transvU33 hU hperf hUγH hz)
  ·
    rcases hj.lt_or_eq with hj | hj
    ·
      obtain ⟨W₁, W₂, hV1W₁, hW₁W₂, hW₂W, hHW₁, hHW₂, hirr, hKnt⟩ :=
        exists_chief_sec hd.hKH hperf hV1W hWc hHW hF1.H_normalizes_V₁ hKW
      have hs₂ := hd.secU hV1W₁ hW₁W₂.le (hW₂W.trans hWU.le) hHW₂ hHW₁ hKnt
      have : IsMulCommutative ↥W₂ := ⟨⟨fun a b => Subtype.ext (hWc a (hW₂W a.2) b (hW₂W b.2))⟩⟩
      have h1 := hs₂.relIndex_le_indexU33 hU hirr hUγH
        (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _)
      have hC₁ : (centralizerMod W₁ W₂ (F8.Uγ S.V3 H (g : G))).relIndex W₂ ≤
          (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))).relIndex W :=
        relIndex_le_of_inf_le hW₂W fun x hx =>
          ⟨hx.2, hHW₁ (hd.UH_le_H (hWU.le hx.1.1)), fun u hu => hV1W₁ (hx.1.2.2 u hu)⟩
      rw [hr] at h1
      rw [HypF98.relIndex_eq_two_pow_mIdx hW2] at hC₁
      have := A6Gen.le_of_two_pow_le (h1.trans hC₁)
      omega
    ·
      obtain ⟨a, -, -, hA2⟩ := A6Gen.exists_gen_of_card_two (hF.card_A₁ (g := g))
      have hAN : F8.A₁ (fsuV1 T V) (g : G) ≤ Subgroup.normalizer (W : Set G) :=
        (hF.A₁_le_Uγ.trans hUγH).trans hHW
      have hcomm := (hjeq hj).2
      have hz : ∀ f ∈ F8.Uγ S.V3 H (g : G), ∀ x ∈ conjClosure S.V3 H,
          f * x * f⁻¹ * x⁻¹ ∈ W ∨ f * x * f⁻¹ * x⁻¹ * a⁻¹ ∈ W := by
        intro f hf x hx
        have h1 := (F8.A₁ (fsuV1 T V) (g : G) ⊔ W).inv_mem
          (hcomm (Subgroup.commutator_mem_commutator hx hf))
        have e : (⁅x, f⁆)⁻¹ = f * x * f⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
        rw [e] at h1
        exact A6Gen.mem_or_mul_inv_mem_of_sup hAN hA2 h1
      exact hd.not_Uγ_le s hDγ (hsU.le_pCoreOf_of_transvU33 hU hperf hUγH hz)

theorem relIndex_top_u33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) {W : Subgroup G} (hV1W : fsuV1 T V ≤ W)
    (hWU : W < conjClosure S.V3 H) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) :
    W.relIndex (conjClosure S.V3 H) = 2 ^ 6 := by
  have hF := hd.hF
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  obtain ⟨γ, γ', g, s, hDγ, -, hpos, hle, -⟩ := S.case2_of_no_transv hF (hd.no_transv_u33 hU)
  obtain ⟨hq, -⟩ := hF.F916_2_aux s hpos hle
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  refine hsU.card_eq_64_of_le_sq hU hmax (hF.Uγ_le_H s) (hd.not_Uγ_le s hDγ)
    (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _) ?_
  refine (Subgroup.relIndex_le_of_le_left ?_ (relIndex_ne_zero' _ _)).trans hq.2.2.2.2
  intro x hx
  exact ⟨hx.1, hHW (hd.UH_le_H hx.1), fun u hu => hV1W (hx.2.2 u hu)⟩

theorem natural_u33
    (h21 : Lem13821) (h16 : Lem13816) (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    G2NaturalDerived (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 1 := by
  obtain ⟨W, hV1W, hWU, hHW, hmax⟩ := hd.exists_max
  have htriv := hd.triv_of_max_u33 h21 h16 hU hV1W hWU hHW hmax
  have hW : ∀ u ∈ conjClosure S.V3 H, u ∈ W ↔ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V :=
    fun u hu => hd.mem_max_iff_of_triv hWU hmax htriv hu
  have h64 := hd.relIndex_top_u33 hU hV1W hWU hHW hmax
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  obtain ⟨K', _, _, hK', π, hπ⟩ := u33SixNatural _ (fun v => by rw [pow_two]; exact hsU.sec_sq v)
    (by rw [SecHyp.card_sec]; exact h64) _ (hsU.b42TypeU33 hU)
  have hK2 : Nat.card K' = 2 := by rw [hK', pow_one]
  have := H13.charP_two_of_natCard_two hK2
  obtain ⟨π', hπ'⟩ := hd.exists_realizesVia_top
    (FFModel.zornQ_isActionModel ⁅quasithinG2 K', quasithinG2 K'⁆ (Subgroup.commutator_le_self _))
    hV1W hWU hHW hW hπ
  exact ⟨K', inferInstance, inferInstance, hK', π', hπ'⟩

theorem cover_u33
    (h21 : Lem13821) (h16 : Lem13816) (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥ ∨
      (Nat.card (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) = 2 ∧
        Nat.card (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 2 ^ 7 ∧
        G2WeylDerived (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hd.hF.toHypF91.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH)
  exact VolI.g2NaturalCover_holds _ (fun v => by rw [pow_two]; exact hsV.sec_sq v) _ _ le_rfl
    hd.commV_autSec_eq_top (hd.natural_u33 h21 h16 hU)

end DK

end Setting4

end CFSG.Quasithin.H13.A6
