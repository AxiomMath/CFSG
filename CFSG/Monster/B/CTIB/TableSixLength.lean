module

public import CFSG.Monster.B.CTIB.TableSix
public import CFSG.Monster.B.TwoA.Co2Inv.CentOrder
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3123
public import Certificates.Certificate3027

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA Native Matrix
open CFSG.Monster.B.Co2 (v0 qbW qbWBasis qbWBasis_apply decW decW_xor decW_zero decW_eq_equivFun
  genQuotMatrix)
open CFSG.Monster.B.TwoA.Co2Inv (rK rK_mul_self rK_ne_one wAct_rK rowsEnd_qbW decW_one_shiftLeft
  ncard_conjClass_rK)
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def rKImage : Array ℕ := #[12319, 20511, 61471, 94239, 30750, 30721]

@[expose] def rKDual : Array ℕ := #[20480, 12288, 32768, 61443, 4097, 4098]

@[expose] noncomputable def rKVec (s : Fin 6) : Wv v0 := decW rKImage[(s : ℕ)]!

@[expose] def rKDualMat : Matrix (Fin 6) (Fin 22) (ZMod 2) :=
  Matrix.of fun i t => bvec 22 rKDual[(i : ℕ)]! t

theorem rKDualMat_rKImage : ∀ j : Fin 6,
    rKDualMat.mulVec (bvec 22 rKImage[(j : ℕ)]!) = Pi.single j 1 := by
  decide +kernel

theorem linearIndependent_rKVec : LinearIndependent (ZMod 2) rKVec := by
  refine LinearIndependent.of_comp (rKDualMat.mulVecLin ∘ₗ qbWBasis.equivFun.toLinearMap) ?_
  have : (rKDualMat.mulVecLin ∘ₗ qbWBasis.equivFun.toLinearMap) ∘ rKVec =
      ⇑(Pi.basisFun (ZMod 2) (Fin 6)) := by
    funext j
    change rKDualMat.mulVec (qbWBasis.equivFun (decW rKImage[(j : ℕ)]!)) = _
    rw [decW_eq_equivFun, LinearEquiv.apply_symm_apply, rKDualMat_rKImage, Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun (ZMod 2) (Fin 6)).linearIndependent

theorem rKm1_qbW (t : Fin 22) :
    (wAct v0 rK - 1) (qbW t) = decW ((genQuotMatrix 12)[(t : ℕ)]! ^^^ (1 <<< (t : ℕ))) := by
  rw [LinearMap.sub_apply, wAct_rK, rowsEnd_qbW, Module.End.one_apply, ← decW_one_shiftLeft,
    decW_xor, sub_eq_add_neg, ZModModule.neg_eq_self]

theorem rKm1_rows : ∀ t < 22, (genQuotMatrix 12)[t]! ^^^ (1 <<< t) = 0 ∨
    ∃ s < 6, (genQuotMatrix 12)[t]! ^^^ (1 <<< t) = rKImage[s]! := by
  decide +kernel

theorem rKImage_rows : ∀ s < 6, ∃ t < 22, rKImage[s]! = (genQuotMatrix 12)[t]! ^^^ (1 <<< t) := by
  decide +kernel

theorem range_rKm1 :
    LinearMap.range (wAct v0 rK - 1) = Submodule.span (ZMod 2) (Set.range rKVec) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [← qbWBasis.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [map_smul, qbWBasis_apply, rKm1_qbW]
    refine Submodule.smul_mem _ _ ?_
    rcases rKm1_rows t t.2 with h | ⟨s, hs, h⟩
    · rw [h, decW_zero]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht, h⟩ := rKImage_rows s s.2
    exact ⟨qbW ⟨t, ht⟩, by rw [rKm1_qbW, rKVec, h]⟩

theorem finrank_range_rK :
    Module.finrank (ZMod 2) (LinearMap.range (wAct v0 rK - 1)) = 6 := by
  rw [range_rKm1, finrank_span_eq_card linearIndependent_rKVec, Fintype.card_fin]

@[expose] noncomputable def rKS :
    KS := (MulEquiv.subgroupCongr Kstab_rStar_eq).symm rK

theorem rKS_mul_self :
    rKS * rKS = 1 := by
  rw [rKS, ← map_mul, rK_mul_self, map_one]

theorem rKS_ne_one :
    rKS ≠ 1 := by
  rw [rKS, Ne, MulEquiv.map_eq_one_iff]
  exact rK_ne_one

theorem rkW_rKS :
    rkW rKS = 6 := by
  rw [rkW, ← finrank_wAct_congr hv0 rKS rK rfl, finrank_range_rK]

theorem isConj_piH_hs6 :
    IsConj (piH ⟨hs 6, hs_mem_Jbar (.inl rfl)⟩) rKS :=
  kv_conj_of_rank co2_involution_input (piH_hs_sq (.inl rfl)) (piH_hs_ne_one (.inl rfl))
    rKS_mul_self rKS_ne_one (by rw [rkW_hs (.inl rfl), rkW_rKS])

theorem isConj_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a b : G}
    (h : IsConj a b) : IsConj (e a) (e b) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨e c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem ncard_conjClass_piH_hs6 :
    {κ : KS | IsConj (piH ⟨hs 6, hs_mem_Jbar (.inl rfl)⟩) κ}.ncard = 56925 := by
  set e := MulEquiv.subgroupCongr Kstab_rStar_eq with he
  have hr : e rKS = rK := by rw [rKS, ← he, MulEquiv.apply_symm_apply]
  have hset : {κ : KS | IsConj (piH ⟨hs 6, hs_mem_Jbar (.inl rfl)⟩) κ} =
      e.symm '' {x : Kstab v0 | IsConj rK x} := by
    ext κ
    constructor
    · intro h
      refine ⟨e κ, ?_, e.symm_apply_apply κ⟩
      have h' := isConj_mulEquiv e (isConj_piH_hs6.symm.trans h)
      rwa [hr] at h'
    · rintro ⟨x, hx, rfl⟩
      have h' := isConj_mulEquiv e.symm hx
      rw [show e.symm rK = rKS from rfl] at h'
      exact isConj_piH_hs6.trans h'
  rw [hset, Set.ncard_image_of_injective _ e.symm.injective, ncard_conjClass_rK]

theorem finite_KS :
    Finite KS := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [Nat.card_congr (MulEquiv.subgroupCongr Kstab_rStar_eq).toEquiv, Co2.natCard_Kv]
  norm_num

theorem ncard_eq_mul_of_fibers {α β : Type*} [Finite α] {A : Set α} {B : Set β} (f : α → β)
    (hAB : Set.MapsTo f A B) (hB : B.Finite) {n : ℕ}
    (hn : ∀ b ∈ B, {a | a ∈ A ∧ f a = b}.ncard = n) : A.ncard = B.ncard * n := by
  classical
  have hA : A.Finite := Set.toFinite A
  have hmaps : Set.MapsTo f (hA.toFinset : Set α) (hB.toFinset : Set β) := fun a ha => by
    simpa using hAB (by simpa using ha)
  have hfib : ∀ b ∈ hB.toFinset, (hA.toFinset.filter fun a => f a = b).card = n := by
    intro b hb
    rw [← hn b (by simpa using hb), Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    congr 1
    ext a
    simp
  rw [Set.ncard_eq_toFinset_card A hA, Set.ncard_eq_toFinset_card B hB,
    Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
    smul_eq_mul]

open _root_.Classical in
@[expose] noncomputable def piS (u : Sbp) : KS :=
  if h : u.unop ∈ Jbar then piH ⟨u, h⟩ else 1

theorem piS_of_mem {u : Sbp} (h : u.unop ∈ Jbar) : piS u = piH ⟨u, h⟩ := by
  simp [piS, h]

theorem piS_conj {g u : Sbp} (hg : g.unop ∈ Jbar) (hu : u.unop ∈ Jbar) :
    piS (g * u * g⁻¹) = piH ⟨g, hg⟩ * piH ⟨u, hu⟩ * (piH ⟨g, hg⟩)⁻¹ := by
  have hm : (g * u * g⁻¹).unop ∈ Jbar :=
    Jbar.op.mul_mem (Jbar.op.mul_mem hg hu) (Jbar.op.inv_mem hg)
  rw [piS_of_mem hm, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem unop_mem_Jbar_of_mem_jClass {T u : Sbp} (hT : T.unop ∈ Jbar) (hu : u ∈ jClass T) :
    u.unop ∈ Jbar := by
  obtain ⟨g, hg, rfl⟩ := hu
  exact Jbar.op.mul_mem (Jbar.op.mul_mem (Jbar.op.inv_mem hg) hT) hg

theorem conj_mem_jClass {T u g : Sbp} (hg : g.unop ∈ Jbar) (hu : u ∈ jClass T) :
    g * u * g⁻¹ ∈ jClass T := by
  rw [← jClass_eq_of_mem hu]
  exact ⟨g⁻¹, Jbar.op.inv_mem hg, by group⟩

theorem fiber_jClass_eq
    {k : ℕ} (hk : IsRank k) {T : Sbp} (hT : T ∈ cosetInv k) :
    {u | u ∈ jClass T ∧ piS u = piH ⟨hs k, hs_mem_Jbar hk⟩} = jClass T ∩ cosetInv k := by
  obtain ⟨⟨q, hq, rfl⟩, hT2⟩ := hT
  have hTJ : (hs k * q).unop ∈ Jbar := Jbar.op.mul_mem (hs_mem_Jbar hk) (Ebar_le_Jbar hq)
  ext u
  constructor
  · rintro ⟨hu, hpu⟩
    have huJ := unop_mem_Jbar_of_mem_jClass hTJ hu
    rw [piS_of_mem huJ] at hpu
    have hq' : (hs k)⁻¹ * u ∈ Qs := by
      have h1 : piH (⟨hs k, hs_mem_Jbar hk⟩⁻¹ * ⟨u, huJ⟩) = 1 := by
        rw [map_mul, hpu, ← map_mul, inv_mul_cancel, map_one]
      exact (piH_eq_one_iff _).1 h1
    refine ⟨hu, ⟨(hs k)⁻¹ * u, hq', by group⟩, ?_⟩
    obtain ⟨g, -, rfl⟩ := hu
    calc g⁻¹ * (hs k * q) * g * (g⁻¹ * (hs k * q) * g) =
        g⁻¹ * ((hs k * q) * (hs k * q)) * g := by group
      _ = 1 := by rw [hT2]; group
  · rintro ⟨hu, ⟨q', hq', rfl⟩, -⟩
    refine ⟨hu, ?_⟩
    have hqJ : q'.unop ∈ Jbar := Ebar_le_Jbar hq'
    have hm : (hs k * q').unop ∈ Jbar := Jbar.op.mul_mem (hs_mem_Jbar hk) hqJ
    rw [piS_of_mem hm]
    have e1 : (⟨hs k * q', hm⟩ : Jbar.op) = ⟨hs k, hs_mem_Jbar hk⟩ * ⟨q', hqJ⟩ := rfl
    rw [e1, map_mul, (piH_eq_one_iff ⟨q', hqJ⟩).2 hq', mul_one]

theorem ncard_jClass_eq_mul
    {k : ℕ} (hk : IsRank k) {T : Sbp} (hT : T ∈ cosetInv k) :
    (jClass T).ncard = {κ : KS | IsConj (piH ⟨hs k, hs_mem_Jbar hk⟩) κ}.ncard *
      (jClass T ∩ cosetInv k).ncard := by
  set κ₀ := piH ⟨hs k, hs_mem_Jbar hk⟩ with hκ₀
  have hTJ : T.unop ∈ Jbar := by
    obtain ⟨⟨q, hq, rfl⟩, -⟩ := hT
    exact Jbar.op.mul_mem (hs_mem_Jbar hk) (Ebar_le_Jbar hq)
  have hpT : piS T = κ₀ := by
    have h := fiber_jClass_eq hk hT
    have hmem : T ∈ jClass T ∩ cosetInv k := ⟨mem_jClass_self T, hT⟩
    rw [← h] at hmem
    exact hmem.2
  have := finite_KS
  refine ncard_eq_mul_of_fibers piS ?_ (Set.toFinite _) ?_
  · rintro u ⟨g, hg, rfl⟩
    have hg' : (g⁻¹).unop ∈ Jbar := Jbar.op.inv_mem hg
    have h1 := piS_conj hg' hTJ
    rw [inv_inv] at h1
    have hpT' : piH ⟨T, hTJ⟩ = κ₀ := by
      rw [← piS_of_mem hTJ]
      exact hpT
    rw [hpT'] at h1
    exact isConj_iff.2 ⟨piH ⟨g⁻¹, hg'⟩, h1.symm⟩
  · intro κ hκ
    obtain ⟨c, hc⟩ := isConj_iff.1 hκ
    obtain ⟨g, rfl⟩ := piH_surjective c
    have hset : {u | u ∈ jClass T ∧ piS u = κ} =
        (fun x => g.val * x * g.val⁻¹) '' {u | u ∈ jClass T ∧ piS u = κ₀} := by
      ext y
      constructor
      · rintro ⟨hy, hpy⟩
        have hyJ := unop_mem_Jbar_of_mem_jClass hTJ hy
        have hx : g.val⁻¹ * y * g.val⁻¹⁻¹ ∈ jClass T := conj_mem_jClass (Jbar.op.inv_mem g.2) hy
        have hxJ := unop_mem_Jbar_of_mem_jClass hTJ hx
        refine ⟨g.val⁻¹ * y * g.val⁻¹⁻¹, ⟨hx, ?_⟩, by group⟩
        rw [piS_conj (Jbar.op.inv_mem g.2) hyJ, ← piS_of_mem hyJ, hpy, ← hc]
        have e2 : (⟨g.val⁻¹, Jbar.op.inv_mem g.2⟩ : Jbar.op) = g⁻¹ := rfl
        rw [e2, map_inv]
        group
      · rintro ⟨x, ⟨hx, hpx⟩, rfl⟩
        have hxJ := unop_mem_Jbar_of_mem_jClass hTJ hx
        refine ⟨conj_mem_jClass g.2 hx, ?_⟩
        rw [piS_conj g.2 hxJ, ← piS_of_mem hxJ, hpx, ← hc]
    rw [hset, Set.ncard_image_of_injective _ (fun a b h => by simpa using h),
      fiber_jClass_eq hk hT]

theorem ncard_jClass_rs_six
    {i n m ρ b : ℕ} (h : (i, 6, n, m, ρ, b) ∈ tableSixRows) :
    (jClass (rs i)).ncard = 56925 * n := by
  obtain ⟨-, -, hmem, hn, -⟩ := native_table_six_classes.2.2.2 i 6 n m ρ b h
  rw [ncard_jClass_eq_mul (.inl rfl) hmem, ncard_conjClass_piH_hs6, hn]

theorem native_table_six :
    (∀ t : Sbp, t.unop ∈ Jbar → t * t = 1 → t ∉ Qs →
      ∃! i, i ∈ Finset.Icc 4 13 ∧ t ∈ jClass (rs i)) ∧
    (∀ i ∈ Finset.Icc 4 13, ∀ j ∈ Finset.Icc 4 13, rs i ∈ jClass (rs j) → i = j) ∧
    tableSixRows.map (·.1) = List.range' 4 10 ∧
    (∀ i k n m ρ b : ℕ, (i, k, n, m, ρ, b) ∈ tableSixRows →
      (rs i).unop ∈ Jbar ∧ rs i ∉ Qs ∧ rs i ∈ cosetInv k ∧
        (jClass (rs i) ∩ cosetInv k).ncard = n ∧ (qClass (rs i)).ncard = m ∧
        ((βr (rs i)) - 1).rank = ρ ∧ IsConj (rs i) (rs b)) ∧
    {κ : KS | IsConj (piH ⟨hs 6, hs_mem_Jbar (.inl rfl)⟩) κ}.ncard = 56925 ∧
    ∀ i n m ρ b : ℕ, (i, 6, n, m, ρ, b) ∈ tableSixRows → (jClass (rs i)).ncard = 56925 * n :=
  ⟨native_table_six_classes.1, native_table_six_classes.2.1, native_table_six_classes.2.2.1,
    native_table_six_classes.2.2.2, ncard_conjClass_piH_hs6,
    fun _ _ _ _ _ h => ncard_jClass_rs_six h⟩

end CFSG.Monster.B.CTIB
