module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Core
public import CFSG.RankThree.GF2n.Stroth80.Sec310SLTransv
public import CFSG.RankThree.GF2n.Stroth80.Sec57B
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular
public import CFSG.RankThree.GF2n.Stroth80.Sec311RootOrder
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS6

theorem relIndex_SL (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z)
    {k : ℕ} (hk : 2 ≤ k)
    (hnat : NaturalRep (ι := Fin k) K (StatedSL k K) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ (k - 1) := by
  classical
  have h35all := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n t hs ⟨K, inferInstance, inferInstance, hK, k, hk, hnat⟩
  have hcardV := card_of_naturalRep hnat sec39_Z_le_Vt hK
  obtain ⟨n', γ, M₀, -, hglob⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c e he => hc.smul_mem_img_Vt hglob t c he
  obtain ⟨m', φ', hnorm', ψ', c', hker', hequiv', -, -, hSeq'⟩ :=
    exists_natural_data_of_subspace hc.hyp (hc.Vt_le_Q t) sec39_Z_le_Vt (hc.Rt_le_H0 t)
      (hc.Rt_normalizes_Vt hs.mem) (fun _ => Ctx.mem_CN (hc := hc)) hglob hS
  have hLRB : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  obtain ⟨b, hbV, hb0, hu0, hBb, hP1, hP2, hcount⟩ := hc.matrix_elation_data hs.width hs.n_gt
    hs.noA2 h35all.2.2.1 h35all.2.2.2 hglob (hc.B_le_Vt hs.mem) (le_inf (hc.Vt_le_Q t) hVQB) hS
    (hc.Rt_le_H0 t) (hc.Rt_normalizes_Vt hs.mem) hLRB φ' c' hSeq'
  have hT := hcount (LB M Q B ⊓ hc.CN t) (fun x => by
    rw [Subgroup.mem_inf, Ctx.mem_CN]
    constructor
    · rintro ⟨hx, -, hxv⟩
      exact ⟨hx, hxv⟩
    · rintro ⟨hx, hxv⟩
      exact ⟨hx, hLRB hx, hxv⟩)
  have hq : 2 ≤ Nat.card Z := HS6.two_le_card_Z hc
  have hKg : Nat.card (GaloisField 2 n') = Nat.card Z := hglob.card
  haveI := hnorm'
  have hcardV' : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ m' := by
    have hcardQ : Nat.card (↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t)) =
        Nat.card Z ^ m' := by
      rw [Nat.card_congr ψ'.toEquiv,
        show Nat.card (Multiplicative (Fin m' → GaloisField 2 n')) =
          Nat.card (Fin m' → GaloisField 2 n') from rfl,
        Nat.card_fun, hKg, Nat.card_eq_fintype_card (α := Fin m'), Fintype.card_fin]
    have hcardZ : Nat.card (Z.subgroupOf (Vt M (LB M Q B) B Z t)) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec39_Z_le_Vt).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Z.subgroupOf (Vt M (LB M Q B) B Z t)), hcardQ, hcardZ, mul_comm]
  rw [hcardV'] at hcardV
  have hkm : k = m' := by
    have h1 : Nat.card Z * Nat.card Z ^ m' =
        Nat.card Z * Nat.card Z ^ Fintype.card (Fin k) := hcardV
    rw [Fintype.card_fin] at h1
    exact (Nat.pow_right_injective hq (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1)).symm
  have hrel := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
  rw [inf_comm, hT, hKg, ← hkm] at hrel
  have hA : 0 < Nat.card ↥(LB M Q B ⊓ hc.CN t) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hA ?_
  rw [mul_comm]
  exact hrel

theorem card_map_LB_eq_relIndex (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ι : Type}
    {K : Type} [Field K] [Fintype ι] [DecidableEq ι] (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) :
    Nat.card (((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ) =
      (hc.CN t).relIndex (LB M Q B) := by
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hLR]

theorem relIndex_orth (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hnatSO : SpNat hc t ∨ OmegaNat hc t) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) (h3 : 3 ≤ Module.finrank K (ι → K))
    (hX : AddCommutantScalar X)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    (hc.CN t).relIndex (LB M Q B) = Nat.card K ^ (Module.finrank K (ι → K) - 2) := by
  obtain ⟨φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hnat
  haveI := hn
  obtain ⟨u, hQu, hu0, -, -, hL, -⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK E hQ h3 hX
    φ hφ hker ψ hψ (hc.omega_singular h34 hRoot hs hnatSO hK E hQ h3 hX φ hφ ψ hψ)
  rw [← card_map_LB_eq_relIndex hc hs.mem φ hker, hL]
  exact E.card_LomGL hQ hQu hu0

theorem relIndex_omegaPlus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 3 ≤ m)
    (h : OmegaPlusNat hc t m) :
    (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ (2 * m - 2) := by
  obtain ⟨K, fK, finK, hK, hnat⟩ := h
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
  have h' := relIndex_orth h34 hRoot hc hs hnatSO hK (ElemMatrixIso.plus hm)
    (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm) hnat
  rw [h', hK, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  congr 1
  omega

theorem relIndex_omegaMinus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 2 ≤ m)
    (h : OmegaMinusNat hc t m) :
    (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ (2 * m - 2) := by
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := h
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]; omega
  have h' := relIndex_orth h34 hRoot hc hs hnatSO hK (ElemMatrixIso.minus hm hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
    (addCommutantScalar_statedOmegaMinus hm hirr) hnat
  rw [h', hK, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin]
  congr 1
  omega

theorem not_le_QB_omegaPlus_two (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnat : OmegaPlusNat hc t 2) : ¬ Vt M (LB M Q B) B Z t ≤ QB B := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV := hc.B_le_Vt hs.mem
  have hVQ := hc.Vt_le_Q t
  obtain ⟨K, _, _, hK, φ, hφr, -, hsec⟩ := hnat
  refine hc.not_le_QB_of_natural h35 hLR hZV hBV hVQ hK (ι := Fin 2 ⊕ Fin 2) ?_ φ hsec
    (polarBilin (quadPlus 2 K)) ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rintro A ⟨s, rfl⟩ u hu hrank
    have hA : φ s ∈ StatedOmega (StatedQuadPlus 2 K) := by
      rw [← hφr]
      exact ⟨s, rfl⟩
    exact omega_hform (coe_quadPlus 2 K) (nondegenerate_polarBilin_quadPlus 2 K) hA hu hrank

theorem even_card_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] : Even (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact (Nat.even_pow.mpr ⟨even_two, PNat.ne_zero n⟩)

theorem pow_two_dvd_sq_of_dvd_card {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {j : ℕ}
    (h : 2 ^ j ∣ Nat.card ↥(StatedOmega (StatedQuadPlus 2 K))) : 2 ^ j ∣ Nat.card K ^ 2 := by
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two] at h
  have hev : Even (Nat.card K ^ 2) := (even_card_of_charTwo K).pow_of_ne_zero (by norm_num)
  have hodd : Odd (Nat.card K ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ Nat.card_pos) hev odd_one
  have hcop : Nat.Coprime (2 ^ j) ((Nat.card K ^ 2 - 1) ^ 2) :=
    Nat.Coprime.pow_right 2 (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd))
  have e1 : Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) =
      Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by ring
  rw [e1] at h
  exact hcop.dvd_of_dvd_mul_right h

theorem relIndex_omegaPlus_four_of_ne (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (s5 : Sec5Hyp hc n t) (hR : Rt M (LB M Q B) t ≠ LB M Q B)
    (h : OmegaPlusNat hc t 2) : (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ 2 := by
  have hlow : Nat.card Z ^ 2 ≤ (hc.CN t).relIndex (LB M Q B) :=
    stroth311RootOrder_of_34 h34 G M Q Z B hc n s5.width s5.n_gt s5.noA2 s5.gen t s5.mem s5.notQ
      hR (not_le_QB_omegaPlus_two h34 hc s5 h) h
  have hLB2 : IsPGroup 2 ↥(LB M Q B) :=
    Ctx.isPGroup_LB h34 hc s5.width s5.n_gt s5.noA2 s5.gen
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card (p := 2)).mp hLB2
  have hd1 : (hc.CN t).relIndex (LB M Q B) ∣ 2 ^ i :=
    hi ▸ Subgroup.relIndex_dvd_card (hc.CN t) (LB M Q B)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, -⟩ := h
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hΛX : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ ≤
      StatedOmega (StatedQuadPlus 2 K) := hφ ▸ Subgroup.map_le_range _ _
  have hd2 : (hc.CN t).relIndex (LB M Q B) ∣ Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) := by
    rw [← card_map_LB_eq_relIndex hc s5.mem φ hker]
    exact Subgroup.card_dvd_of_le hΛX
  rw [hj] at hd2
  have hd3 : (hc.CN t).relIndex (LB M Q B) ∣ Nat.card Z ^ 2 := by
    rw [hj, ← hK]
    exact pow_two_dvd_sq_of_dvd_card (hK ▸ hc.hyp.q4) hd2
  exact Nat.le_antisymm (Nat.le_of_dvd (pow_pos (by have := hc.hyp.q4; omega) 2) hd3) hlow

theorem relIndex_omegaPlus_four (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Stroth6Hyp hc n t) (h : OmegaPlusNat hc t 2) :
    (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ 2 :=
  relIndex_omegaPlus_four_of_ne h34 hc hs.toSec5 (Rt_ne_LB h34 hc hs) h

end HS6

end CFSG.RankThree.GF2n.Stroth80
