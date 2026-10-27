
module

public import Certificates.Kernel.Co1ThreeK.GlueSplit
public import Certificates.Kernel.Co1ThreeK.GlueE
public import Certificates.Kernel.Co1ThreeK.GlueLeaf
public import Certificates.Kernel.Co1ThreeK.HypSound
public import Certificates.Kernel.Co1ThreeK.LeafE
public import Certificates.Kernel.Co1ThreeK.LeafD0
public import Certificates.Kernel.Co1ThreeK.LeafD1
public import Certificates.Kernel.Co1ThreeK.LeafD2
public import Certificates.Kernel.Co1ThreeK.LeafD3
import all CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1Leaf
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance Timmesfeld.Co1Leaf
open CertificateChecks.KernelCo1B.Bound17591
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (wG eltG aGA SplitData root Good
  aGA_length)

@[expose] def codeK (e : List ℕ) : ℕ := e.foldr (fun x acc => x + 3 * acc) 0

theorem kEV : ∀ ℓ < 3, ∀ e ∈ LD.EV.getD ℓ [], digK (codeK e) = e ∧
    dotK 3 6 (([243, 81, 190] : List ℕ).getD ℓ 0) (codeK e) = 0 := by
  decide +kernel

theorem dotK_six (c w : ℕ) : dotK 3 6 c w =
    (c % 3 * (w % 3) + (c / 3 % 3 * (w / 3 % 3) + (c / 3 / 3 % 3 * (w / 3 / 3 % 3) +
      (c / 3 / 3 / 3 % 3 * (w / 3 / 3 / 3 % 3) + (c / 3 / 3 / 3 / 3 % 3 * (w / 3 / 3 / 3 / 3 % 3) +
        (c / 3 / 3 / 3 / 3 / 3 % 3 * (w / 3 / 3 / 3 / 3 / 3 % 3) + 0) % 3) % 3) % 3) % 3) % 3) %
      3 := rfl

theorem code_normVec {k : ℕ} (hk : k = 6) {fl : List ℕ} (hfl : fl ∈ normVecs 3 k) :
    1 ≤ codeK fl ∧ codeK fl < 729 ∧ ∀ w, dotK 3 6 (codeK fl) w = 0 →
      ∑ i, Co1T.listVec k fl i * Co1T.listVec k (digK w) i = 0 := by
  subst hk
  obtain ⟨hlen, hlt, -, hp1⟩ := Co1T.normVecs_pivot hfl
  obtain ⟨x0, x1, x2, x3, x4, x5, rfl⟩ := six_of_length hlen
  have h0 := hlt x0 (by simp)
  have h1 := hlt x1 (by simp)
  have h2 := hlt x2 (by simp)
  have h3 := hlt x3 (by simp)
  have h4 := hlt x4 (by simp)
  have h5 := hlt x5 (by simp)
  have hc : codeK [x0, x1, x2, x3, x4, x5] =
      x0 + 3 * (x1 + 3 * (x2 + 3 * (x3 + 3 * (x4 + 3 * (x5 + 3 * 0))))) := rfl
  rw [hc]
  refine ⟨?_, by omega, fun w hw => ?_⟩
  · by_contra hne
    have e0 : x0 = 0 := by omega
    have e1 : x1 = 0 := by omega
    have e2 : x2 = 0 := by omega
    have e3 : x3 = 0 := by omega
    have e4 : x4 = 0 := by omega
    have e5 : x5 = 0 := by omega
    subst e0 e1 e2 e3 e4 e5
    revert hp1
    decide
  · rw [dotK_six] at hw
    generalize hcd : x0 + 3 * (x1 + 3 * (x2 + 3 * (x3 + 3 * (x4 + 3 * (x5 + 3 * 0))))) = c at hw
    have e0 : c % 3 = x0 := by omega
    have e1 : c / 3 % 3 = x1 := by omega
    have e2 : c / 3 / 3 % 3 = x2 := by omega
    have e3 : c / 3 / 3 / 3 % 3 = x3 := by omega
    have e4 : c / 3 / 3 / 3 / 3 % 3 = x4 := by omega
    have e5 : c / 3 / 3 / 3 / 3 / 3 % 3 = x5 := by omega
    rw [e0, e1, e2, e3, e4, e5] at hw
    have hw' := congrArg (Nat.cast : ℕ → ZMod 3) hw
    push_cast [ZMod.natCast_mod] at hw'
    simp only [Fin.sum_univ_six, Co1T.listVec, digK, Fin.val_zero, Fin.val_one, Fin.val_two,
      List.getD_cons_zero, List.getD_cons_succ, ZMod.natCast_mod]
    have i3 : ((3 : Fin 6) : ℕ) = 3 := rfl
    have i4 : ((4 : Fin 6) : ℕ) = 4 := rfl
    have i5 : ((5 : Fin 6) : ℕ) = 5 := rfl
    simp only [i3, i4, i5, List.getD_cons_zero, List.getD_cons_succ, ZMod.natCast_mod]
    linear_combination hw'

@[expose] noncomputable def fsE (ℓ : ℕ) : List ↥GA := (LD.EV.getD ℓ []).map (eltG aGA)

theorem kE_ex {ℓ : ℕ} (hℓ : ℓ < 3) :
    ∃ piM w S B T, leafK XB (GE ℓ) piM w S B T = true := by
  interval_cases ℓ
  · exact ⟨_, _, _, _, _, kE0⟩
  · exact ⟨_, _, _, _, _, kE1⟩
  · exact ⟨_, _, _, _, _, kE2⟩

theorem kD_ex {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    ∃ piM w S B T, leafK XB (GD a b) piM w S B T = true := by
  interval_cases a <;> interval_cases b
  · exact ⟨_, _, _, _, _, kD00⟩
  · exact ⟨_, _, _, _, _, kD01⟩
  · exact ⟨_, _, _, _, _, kD02⟩
  · exact ⟨_, _, _, _, _, kD03⟩
  · exact ⟨_, _, _, _, _, kD10⟩
  · exact ⟨_, _, _, _, _, kD11⟩
  · exact ⟨_, _, _, _, _, kD12⟩
  · exact ⟨_, _, _, _, _, kD13⟩
  · exact ⟨_, _, _, _, _, kD20⟩
  · exact ⟨_, _, _, _, _, kD21⟩
  · exact ⟨_, _, _, _, _, kD22⟩
  · exact ⟨_, _, _, _, _, kD23⟩
  · exact ⟨_, _, _, _, _, kD30⟩
  · exact ⟨_, _, _, _, _, kD31⟩
  · exact ⟨_, _, _, _, _, kD32⟩
  · exact ⟨_, _, _, _, _, kD33⟩

theorem normVecs_two_getD {f : List ℕ} (hf : f ∈ normVecs 3 2) :
    ∃ a < 4, f = (normVecs 3 2).getD a [] := by
  rw [normVecs_two] at hf ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩

section Core

theorem AK_rep : List.Forall₂ (fun A (f : ↥GA) => matK A = ιK f) AK aGA := by
  have hL : ∀ i (hi : i < 6), matK (L.M i) = ιK (aK i hi) := by
    intro i hi
    rw [← TS_LM (k := i) (by omega), matK_nodeK (by omega), nodeK_a hi]
  rw [aGA_eq_aK]
  exact .cons (hL 0 _) (.cons (hL 1 _) (.cons (hL 2 _) (.cons (hL 3 _) (.cons (hL 4 _)
    (.cons (hL 5 _) .nil)))))

theorem GE_rep (ℓ : ℕ) : ∀ g ∈ GE ℓ, ∃ f ∈ fsE ℓ, matK g = ιK f := by
  intro g hg
  unfold GE at hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
  exact ⟨eltG aGA e, List.mem_map_of_mem he, matK_eltWK AK_rep e⟩

theorem fsE_eQ {ℓ : ℕ} (hℓ : ℓ < 3) {f : ↥GA} (hf : f ∈ fsE ℓ) :
    ∃ v, dotK 3 6 (([243, 81, 190] : List ℕ).getD ℓ 0) v = 0 ∧ f = eQ nodeK v := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hf
  obtain ⟨h1, h2⟩ := kEV ℓ hℓ e he
  exact ⟨codeK e, h2, by rw [eQ_eltG, h1]⟩

theorem good_of_conj_leaf {B : Subgroup ↥GA} {ℓ : ℕ} (hℓ : ℓ < 3) (h : ↥GA)
    (hB : ∀ f ∈ fsE ℓ, h⁻¹ * f * h ∈ B) :
    CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer (B : Set ↥GA)) = ⊥ := by
  have := Co1T.finite_GA
  refine gLAPPrimeCoreOf_eq_bot_of_isPGroup Nat.prime_three
    (Co1T.isPGroup_of_coprime_eq_one Nat.prime_three fun n hn hcop => ?_)
  obtain ⟨piM, w, S, Bs, T, hk⟩ := kE_ex hℓ
  have hc : h * n * h⁻¹ = 1 := by
    refine eq_one_of_leafK_GA hk (GE_rep ℓ) (fun f hf => ?_) ?_
    · have hcomm := Subgroup.mem_centralizer_iff.1 hn _ (hB f hf)
      calc h * n * h⁻¹ * f = h * (n * (h⁻¹ * f * h)) * h⁻¹ := by group
        _ = h * (h⁻¹ * f * h * n) * h⁻¹ := by rw [← hcomm]
        _ = f * (h * n * h⁻¹) := by group
    · rwa [Co1T.orderOf_conj_GA]
  have e : n = h⁻¹ * (h * n * h⁻¹) * h := by group
  rw [e, hc]
  group

theorem good_of_ker {B : Subgroup ↥GA} {c : ℕ} (h1 : 1 ≤ c) (h2 : c < 729)
    (hB : ∀ w, dotK 3 6 c w = 0 → eQ nodeK w ∈ B) :
    CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer (B : Set ↥GA)) = ⊥ := by
  obtain ⟨r, hr, h, hh⟩ := hyp_conjK h1 h2
  obtain ⟨ℓ, hℓ, rfl⟩ : ∃ ℓ < 3, ([243, 81, 190] : List ℕ).getD ℓ 0 = r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  refine good_of_conj_leaf hℓ h fun f hf => ?_
  obtain ⟨v, hv, rfl⟩ := fsE_eQ hℓ hf
  obtain ⟨w, hw, he⟩ := hh v hv
  rw [he]
  exact hB w hw

theorem good_of_mem_EK {s : ↥GA} (hs : s ∈ eSplitK.T) (hso : orderOf s = 3) :
    CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥GA)) = ⊥ := by
  have := Co1T.finite_GA
  refine gLAPPrimeCoreOf_eq_bot_of_elemAbelian Nat.prime_three eSplitK.T_elemAbelian hs hso
    (fun B hBT hidx => ?_) ?_
  · obtain ⟨fl, hfl, hB⟩ := @Co1T.exists_normVec_eq_closure ↥GA (Subgroup.toGroup GA)
      aGA.length (Co1T.fnOf aGA) eSplitK.fn_comm eSplitK.fn_cube eSplitK.φ_injective B hBT hidx
    obtain ⟨hc1, hc2, hdot⟩ := code_normVec aGA_length hfl
    refine good_of_ker hc1 hc2 fun w hw => ?_
    rw [hB]
    have hmem := @Co1T.mem_closure_of_dot_eq_zero ↥GA (Subgroup.toGroup GA) aGA.length
      (Co1T.fnOf aGA) eSplitK.fn_comm eSplitK.fn_cube fl hfl
      (Co1T.listVec aGA.length (digK w)) (hdot w hw)
    have hlen : (digK w).length = aGA.length := by rw [aGA_length]; rfl
    have hlt : ∀ x ∈ digK w, x < 3 := by
      intro x hx
      simp only [digK, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    rw [Co3T.vecProdHom_apply, Co1T.vecProd_eq_eltG aGA hlen hlt] at hmem
    rw [eQ_eltG]
    exact hmem
  · refine good_of_conj_leaf (ℓ := 0) (by norm_num) 1 fun f hf => ?_
    obtain ⟨v, -, rfl⟩ := fsE_eQ (by norm_num) hf
    rw [inv_one, one_mul, mul_one]
    exact eQ_mem_T v

theorem orderOf_eQ {v : ℕ} (hv : v < 729) (hv0 : v ≠ 0) : orderOf (eQ nodeK v) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ fun h => hv0 (eQ_injK v hv 0 (by norm_num) (h.trans eQ_zero_K.symm))
  exact eSplitK.T_pow_three _ (eQ_mem_T v)

theorem eQ_81 : eQ nodeK 81 = nodeK 4 := by
  have hd : digK 81 = [0, 0, 0, 0, 1, 0] := rfl
  rw [eQ_eltG, hd, nodeK_a (i := 4) (by norm_num)]
  apply Subtype.ext
  rw [coe_eltG_six]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  rfl

theorem eQ_243 : eQ nodeK 243 = nodeK 5 := by
  have hd : digK 243 = [0, 0, 0, 0, 0, 1] := rfl
  rw [eQ_eltG, hd, nodeK_a (i := 5) (by norm_num)]
  apply Subtype.ext
  rw [coe_eltG_six]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  rfl

theorem good_root_bcK {j : ℕ} (hj : j = 0 ∨ j = 1) :
    CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer ({root j} : Set ↥GA)) = ⊥ := by
  rcases hj with rfl | rfl
  · obtain ⟨nC, hnC⟩ := kdK_ex (k := 88) (by norm_num)
    have e := congrArg matK (Nat.eq_of_beq_eq_true kNC)
    have hL : matK (L.M 4) = ιK (nodeK 4) := by
      rw [← TS_LM (by norm_num)]
      exact matK_nodeK (by norm_num)
    rw [matK_mulWK, matK_mulWK, hnC, matK_RM (by norm_num), hL] at e
    have hcj : nC * nodeK 4 * nC⁻¹ = root 0 := conj_of_mat e
    rw [← hcj, Co1T.good_conj, ← eQ_81]
    exact good_of_mem_EK (eQ_mem_T 81) (orderOf_eQ (by norm_num) (by norm_num))
  · obtain ⟨nB, hnB⟩ := kdK_ex (k := 87) (by norm_num)
    have e := congrArg matK (Nat.eq_of_beq_eq_true kNB)
    have hL : matK (L.M 5) = ιK (nodeK 5) := by
      rw [← TS_LM (by norm_num)]
      exact matK_nodeK (by norm_num)
    rw [matK_mulWK, matK_mulWK, hnB, matK_RM (by norm_num), hL] at e
    have hcj : nB * nodeK 5 * nB⁻¹ = root 1 := conj_of_mat e
    rw [← hcj, Co1T.good_conj, ← eQ_243]
    exact good_of_mem_EK (eQ_mem_T 243) (orderOf_eQ (by norm_num) (by norm_num))

theorem good_root_dK : Good [root 2] := by
  obtain ⟨hS, hc⟩ := dSplitK
  have hlen : (Co1T.Data.planeD.map wG).length = 2 := by rw [planeD_eq]; rfl
  refine good_of_splitData hS hc (by rw [hlen]; norm_num) fun f hf => ?_
  rw [hlen] at hf
  obtain ⟨a, ha, rfl⟩ := normVecs_two_getD hf
  obtain ⟨hS2, hc2⟩ := cSplitK ha
  have hlen2 : ((Co1T.Data.planesD.getD a []).map wG).length = 2 := by
    rw [planesD_eq ha]; rfl
  refine good_of_splitData hS2 hc2 (by rw [hlen2]; norm_num) fun f' hf' => ?_
  rw [hlen2] at hf'
  obtain ⟨b, hb, rfl⟩ := normVecs_two_getD hf'
  obtain ⟨piM, w, S, B, T, hk⟩ := kD_ex ha hb
  rw [kerBasis_DV ha, kerBasis_DV hb, planeD_eq, planesD_eq ha]
  refine good_of_leafK hk fun g hg => ?_
  unfold GD at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨root 2, by simp, matK_RM (by norm_num)⟩
  · exact ⟨eltG [gD 0, gD 1] (LD.DV.getD a []), by simp,
      matK_eltWK (.cons (matK_PD (by norm_num)) (.cons (matK_PD (by norm_num)) .nil)) _⟩
  · exact ⟨eltG [gD (2 + 2 * a), gD (3 + 2 * a)] (LD.DV.getD b []), by simp,
      matK_eltWK (.cons (matK_PD (by omega)) (.cons (matK_PD (by omega)) .nil)) _⟩

theorem oPrimeCoreTrivialAt_GAK : OPrimeCoreTrivialAt 3 ↥GA := by
  intro s hs
  have := Co1T.finite_GA
  obtain ⟨g, -, hg⟩ := @Co3T.exists_conj_mem_of_full ↥GA (Subgroup.toGroup GA) 3
    ⟨Nat.prime_three⟩ ⊤ Co1T.Qg inferInstance le_top
    (by rw [card_QgK, Co1T.factorization_card_GA]) s (Subgroup.mem_top s) hs
  set t := g⁻¹ * s * g with htdef
  have hto : orderOf t = 3 := by
    have := Co1T.orderOf_conj_GA g⁻¹ s
    rw [inv_inv] at this
    rw [htdef, this, hs]
  have hst : s = g * t * g⁻¹ := by rw [htdef]; group
  rw [hst, Co1T.good_conj]
  rcases fusion_rootK hg hto with hE | ⟨j, hj, c, htc⟩
  · exact good_of_mem_EK hE hto
  · rw [htc, Co1T.good_conj]
    rcases hj with rfl | rfl | rfl
    · exact good_root_bcK (Or.inl rfl)
    · exact good_root_bcK (Or.inr rfl)
    · rw [← Co1T.centralizer_singleton_eq]
      exact good_root_dK

end Core

end CertificateChecks.KernelCo1ThreeK

end
