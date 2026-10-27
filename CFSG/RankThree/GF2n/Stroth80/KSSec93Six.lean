module

public import CFSG.RankThree.GF2n.Stroth80.KSSec93Grp
import CFSG.RankThree.GF2n.Stroth80.HeringSec95COne
import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB
import CFSG.RankThree.GF2n.Stroth80.Sec78ConjFrame
import CFSG.RankThree.GF2n.Stroth80.Sec711Step3

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace KS93

variable {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {s z : G}

namespace Hyp

variable (H : Hyp hc n t r Z0 s z)
include H

theorem inf_conj_LB_le_Q {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) :
    Z0 ⊓ conjSubgroup (z * ρ) (LB M Q B) ≤ Q := by
  classical
  intro c hc0
  obtain ⟨hcZ0, hcP⟩ := Subgroup.mem_inf.mp hc0
  by_contra hcQ
  have hs5 := H.hs.toSec5
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hzρ : z * ρ ∈ M := M.mul_mem H.z_mem hρM
  set P := conjSubgroup (z * ρ) B with hP
  have hcP' : Ctx M Q Z P := hc.conj_of_mem hzρ
  have hcL : c ∈ LB M Q P := by rw [hP, hc.LB_conj hzρ]; exact hcP
  have hcLB : c ∈ LB M Q B := H.Z0_le_LB hcZ0
  have hcM : c ∈ M := hc.LB_le_M hcLB
  have hcH : c ∈ H0 M Z := hc.LB_le_H0 hcLB
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨K', fK', finK', chK', γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ₀, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hcP'.dictB h
  have hnoP : NoA2 Q Z (LB M Q P) := by
    rw [hP, hc.LB_conj hzρ]
    exact sec7ctr_NoA2_conj hc hzρ hs5.noA2
  obtain ⟨U, hUmem, -, hUperp, hUsing⟩ := hcP'.lagr hs5.width hs5.n_gt hnoP h
  have hTπ : ∀ x ∈ Q, M₀.π (c * x * c⁻¹) = φ₀ ⟨c, hcH⟩ (M₀.π x) := fun x hx =>
    hφπ ⟨c, hcH⟩ x hx
  obtain ⟨-, hTe⟩ := hcP'.LB_act_fix_line h hB hcL
    (T := (φ₀ ⟨c, hcH⟩ : M₀.E →ₗ[K'] M₀.E)) hTπ
  have hV := H.hC.2.2 c hcZ0 hcQ
  have hTU : ∀ u ∈ U, φ₀ ⟨c, hcH⟩ u = u := by
    intro u hu
    obtain ⟨x, hx, hxQ, rfl⟩ := M₀.mem_img.mp ((hUmem u).mpr hu)
    obtain ⟨a, ha⟩ := hTe _ (M₀.pi_mem_img hx hxQ)
    have ha' : φ₀ ⟨c, hcH⟩ (M₀.π x) - M₀.π x = a • b := ha
    have hcxQ : c * x * c⁻¹ ∈ Q := n12l3_normalizes_Q hc hcM hxQ
    have hcom : ⁅c, x⁆ ∈ Vt M (LB M Q B) B Z t := by
      rw [← hV]
      refine Subgroup.mem_sup_left ?_
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hxQ (Subgroup.mem_zpowers c))
    have hcomQ : ⁅c, x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hcxQ (Q.inv_mem hxQ)
    have hπc : M₀.π ⁅c, x⁆ = a • b := by
      rw [← ha']
      have e : ⁅c, x⁆ = (c * x * c⁻¹) * x⁻¹ := by rw [commutatorElement_def]
      rw [e, M₀.π_mul _ hcxQ _ (Q.inv_mem hxQ), M₀.pi_inv hxQ, hTπ x hxQ, sub_eq_add_neg]
    by_contra hne
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hne
      rw [zero_smul] at ha'
      exact sub_eq_zero.mp ha'
    have hbV : b ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
      have h1 : a • b ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
        rw [← hπc]
        exact M₀.pi_mem_img hcom hcomQ
      have h2 := hc.smul_mem_img_Vt h t a⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h2
    apply H.not_conj_le hρ
    intro y hy
    have hyQ : y ∈ Q := hcP'.le hy
    obtain ⟨e, he⟩ := (hB _).mp (M₀.pi_mem_img hy hyQ)
    have hyV : M₀.π y ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
      rw [he]
      exact hc.smul_mem_img_Vt h t e hbV
    exact (M₀.mem_img_iff hZV hyQ).mp hyV
  obtain ⟨c', hc', y, hy, hcy⟩ := hcP'.exists_mul_of_mem_LB hcL
  have hc'' : c' ∈ QB P ⊓ Subgroup.centralizer (Z : Set G) := by
    rw [← hcP'.QB_inf_M_eq]
    exact hc'
  have hc'H : c' ∈ H0 M Z := ⟨hc'.2, hc''.2⟩
  have hyH : y ∈ H0 M Z := hc.LB_le_H0 (sec39_Q_le_LB hy)
  have hφc : φ₀ ⟨c, hcH⟩ = φ₀ ⟨c', hc'H⟩ := by
    have e : (⟨c, hcH⟩ : H0 M Z) = ⟨c', hc'H⟩ * ⟨y, hyH⟩ := Subtype.ext hcy
    rw [e, map_mul, (hφQ ⟨y, hyH⟩).mpr hy, mul_one]
  have hTU' : ∀ u ∈ U, φ₀ ⟨c', hc'H⟩ u = u := fun u hu => by
    rw [← hφc]
    exact hTU u hu
  have hc'Q : c' ∈ Q := HS9.faithful95 hcP' h φ₀ hφπ hφQ hφiso hnoP (fun e => (hUmem e).symm)
    hUsing (fun e he => hUperp e fun u hu => by rw [M₀.B_comm, he u hu, neg_zero]) hb0 hbs hB
    hcent hc' hc'H hTU'
  exact hcQ (by rw [hcy]; exact Q.mul_mem hc'Q hy)

theorem inf_LB_conj_eq_Q {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) :
    LB M Q (conjSubgroup z⁻¹ B) ⊓ LB M Q (conjSubgroup ρ B) = Q :=
  H.inf_LB_eq_Q hρ (H.inf_conj_LB_le_Q hρ)

end Hyp

end KS93

end CFSG.RankThree.GF2n.Stroth80
