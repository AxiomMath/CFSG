module

public import Certificates.Kernel.Co1ThreeK.GlueQ
public import Certificates.Kernel.Co1ThreeK.Cen
public import CFSG.Certificates.Kernel.Co1Three.CenSound
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co13Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (eltG aGA SplitData Qg aGA_length)

section Cen


theorem T_le_QgK : eSplitK.T ≤ Qg := by
  have hq : ∀ i (hi : i < 6), aK i hi ∈ Qg := fun i hi => by
    rw [← nodeK_a hi, Qg_eq]
    apply Subgroup.subset_closure
    interval_cases i <;> simp
  rw [Co1T.SplitData.T_eq_closure, Subgroup.closure_le]
  intro f hf
  change f ∈ aGA at hf
  rw [aGA_eq_aK] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hq _ _

theorem card_TK : Nat.card eSplitK.T = 729 := by
  rw [SplitData.T, MonoidHom.range_eq_map, Subgroup.card_map_of_injective eSplitK.φ_injective,
    Subgroup.card_top, Co3T.card_vec, aGA_length]
  norm_num

theorem relIndex_T_QgK : eSplitK.T.relIndex Qg = 27 := by
  have h := Subgroup.relIndex_mul_card eSplitK.T Qg
  rw [inf_eq_left.2 T_le_QgK, card_TK, card_QgK] at h
  omega

@[expose] noncomputable def wK (B : List Nat) (a : Nat) : ↥GA := eQ nodeK (actK 3 6 B a 0)

theorem eQ_cube (c : Nat) : eQ nodeK c ^ 3 = 1 := eSplitK.T_pow_three _ (eQ_mem_T c)

theorem wK_eq (B : List Nat) (a : Nat) :
    wK B a = epM (fun c => eQ nodeK c) 3 B a 1 := by
  have e := epM_actK nodeK (p := 3) (by norm_num) [0, 1, 2, 3, 4, 5] qHypK.comm qHypK.cube B a 0
  change eQ nodeK (actK 3 6 B a 0) = eQ nodeK 0 * _ at e
  rw [wK, e, eQ_zero, one_mul]
  rfl

theorem wK_add (B : List Nat) (a x : Nat) :
    wK B (addVK 3 B.length a x) = wK B a * wK B x := by
  rw [wK_eq, wK_eq, wK_eq]
  exact epM_addVK (fun c => eQ nodeK c) (by norm_num) B
    (fun x _ y _ => eQ_comm qHypK x y) (fun x _ => eQ_cube x) a x

theorem card_cen_t_mul_le {l : Nat} (hl : l < 27) {B : List Nat} {n : Nat} (hB : B.length = n)
    (hfix : fixFreeK (getLL CS.TR l) B = true)
    (hsubN : ∀ a < 3 ^ n, ∀ a' < 3 ^ n, addVK 3 n a (addVK 3 n a' (addVK 3 n a a)) = a' ∧
      (addVK 3 n a' (addVK 3 n a a) = 0 → a = a')) :
    Nat.card ↥(eSplitK.T ⊓ Subgroup.centralizer ({nodeK (12 + l)} : Set ↥GA)) * 3 ^ n ≤ 729 := by
  have := CFSG.Sporadic.Co1Schreier.finite_GA
  rw [← card_TK]
  refine card_inf_centralizer_mul_le eSplitK.T_comm (nodeK (12 + l)) (wK B)
    (fun a _ => eQ_mem_T _) (fun a ha a' ha' => ?_) (fun x hx hx0 he => ?_)
  · refine ⟨addVK 3 n a' (addVK 3 n a a), addVK_lt (by norm_num) n _ _, ?_, (hsubN a ha a' ha').2⟩
    rw [← wK_add, hB, (hsubN a ha a' ha').1]
  · have hc := t_conj qHypK hl (actK 3 6 B x 0)
    have hfx : (nodeK (12 + l))⁻¹ * wK B x * nodeK (12 + l) = wK B x := by
      rw [mul_assoc, he, inv_mul_cancel_left]
    rw [← wK, hfx, wK] at hc
    have h1 := actK_lt (n := 6) (show 0 < 3 by norm_num) B x 0 (by norm_num)
    have h2 := actK_lt (n := 6) (show 0 < 3 by norm_num) (getLL CS.TR l) (actK 3 6 B x 0) 0
      (by norm_num)
    norm_num at h1 h2
    exact fixFreeK_sound hfix hx0 (hB ▸ hx) (eQ_injK _ h2 _ h1 hc.symm)

theorem mem_Qg_code {r : ↥GA} (hr : r ∈ Qg) : ∃ c < 729 * 27, r = mdlQ nodeK c := by
  rw [Qg_eq] at hr
  have hr' : r ∈ codeSet nodeK := closure_le_codeSub qHypK hr
  obtain ⟨c, hc, hcr⟩ := mem_codeSet.1 hr'
  exact ⟨c, hc, hcr.symm⟩

theorem card_cen_leK {r : ↥GA} (hrQ : r ∈ Qg) (hrE : r ∉ eSplitK.T) :
    Nat.card ↥(eSplitK.T ⊓ Subgroup.centralizer ({r} : Set ↥GA)) ≤ 27 := by
  have := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨c, hc, rfl⟩ := mem_Qg_code hrQ
  have hk1 : 1 ≤ c / 729 := by
    by_contra hlt
    refine hrE ?_
    have hc7 : c < 729 := by omega
    rw [mdlQ, Nat.div_eq_of_lt hc7, Nat.mod_eq_of_lt hc7, Nat.add_zero, f_twelve qHypK, one_mul]
    exact eQ_mem_T c
  have hk : c / 729 < 27 := Nat.div_lt_of_lt_mul hc
  obtain ⟨l, hl⟩ : ∃ l, l = c / 729 := ⟨_, rfl⟩
  rw [← hl] at hk1 hk
  have hle : eSplitK.T ⊓ Subgroup.centralizer ({mdlQ nodeK c} : Set ↥GA) ≤
      eSplitK.T ⊓ Subgroup.centralizer ({nodeK (12 + l)} : Set ↥GA) := by
    intro s hs
    obtain ⟨hsT, hsC⟩ := Subgroup.mem_inf.1 hs
    refine Subgroup.mem_inf.2 ⟨hsT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 hsC
    rw [mdlQ, ← hl] at h
    have he := eSplitK.T_comm _ hsT _ (eQ_mem_T (c % 729))
    have e : s * nodeK (12 + l) * eQ nodeK (c % 729) =
        nodeK (12 + l) * s * eQ nodeK (c % 729) := by
      calc s * nodeK (12 + l) * eQ nodeK (c % 729)
          = s * (nodeK (12 + l) * eQ nodeK (c % 729)) := mul_assoc _ _ _
        _ = nodeK (12 + l) * eQ nodeK (c % 729) * s := h
        _ = nodeK (12 + l) * s * eQ nodeK (c % 729) := by rw [mul_assoc, he.symm, ← mul_assoc]
    exact mul_right_cancel e
  have hkc := kCen
  simp only [Bool.and_eq_true] at hkc
  have hB := CFSG.KS.Raw.Orb.allN_iff.1 hkc.2 (l - 1) (by omega)
  simp only [Bool.and_eq_true] at hB
  have hlen : (getLL CB.B (l - 1)).length = 3 := by
    rw [← CFSG.KC.Co1Cl.lenL_eq]
    exact Nat.eq_of_beq_eq_true hB.1
  have hsl : Nat.succ (l - 1) = l := by omega
  rw [hsl] at hB
  have h27 : Nat.card ↥(eSplitK.T ⊓ Subgroup.centralizer ({nodeK (12 + l)} : Set ↥GA)) * 27 ≤
      729 := card_cen_t_mul_le hk hlen hB.2 addVK_sub_three
  have hc := Subgroup.card_le_of_le hle
  omega

theorem exists_r0K :
    ∃ r0 ∈ Qg, Nat.card ↥(eSplitK.T ⊓ Subgroup.centralizer ({r0} : Set ↥GA)) ≤ 9 := by
  have h := kR0
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h27⟩, hlen⟩, hfix⟩ := h
  rw [Nat.blt_eq] at h0 h27
  have hlen' : CB.B0.length = 4 := by
    rw [← CFSG.KC.Co1Cl.lenL_eq]
    exact Nat.eq_of_beq_eq_true hlen
  refine ⟨nodeK (12 + CB.K0), ?_, ?_⟩
  · rw [Qg_eq]
    exact codeSub_le_closure qHypK (t_mem_codeSet qHypK h27)
  · have h81 : Nat.card ↥(eSplitK.T ⊓ Subgroup.centralizer ({nodeK (12 + CB.K0)} : Set ↥GA)) *
        81 ≤ 729 := card_cen_t_mul_le h27 hlen' hfix addVK_sub_four
    omega

theorem le_TK {A : Subgroup ↥GA} (hAQ : A ≤ Qg) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h729 : 729 ≤ Nat.card A) : A ≤ eSplitK.T := by
  have := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨r0, hr0, hr0c⟩ := exists_r0K
  exact CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.le_of_comm_of_card2 T_le_QgK relIndex_T_QgK
    eSplitK.T_comm (fun r hr hrE => card_cen_leK hr hrE) hr0 hr0c hAQ hA (by omega) (by omega)

end Cen

end CertificateChecks.KernelCo1ThreeK

end
