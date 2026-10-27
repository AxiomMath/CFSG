module

public import CFSG.LocalAnalysis.WeakClosure81.W16QExcT
public import CFSG.LocalAnalysis.WeakClosure81.W16QGeneric
public import CFSG.LocalAnalysis.WeakClosure81.W16QCoreRank
public import CFSG.LocalAnalysis.WeakClosure81.W16QCoreNorm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_sup_of_le_centralizer {I C K : Subgroup G}
    (hI : K ≤ normalizer (I : Set G)) (hC : C ≤ centralizer (K : Set G)) :
    K ≤ normalizer ((I ⊔ C : Subgroup G) : Set G) := by
  have key : ∀ k ∈ K, I ⊔ C ≤ (I ⊔ C).comap (MulAut.conj k).toMonoidHom := by
    intro k hk
    refine sup_le (fun i hi => ?_) (fun c hc => ?_)
    · exact Subgroup.mem_comap.2
        (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hI hk) i).1 hi))
    · have : k * c * k⁻¹ = c := by
        rw [mul_inv_eq_iff_eq_mul]
        exact Subgroup.mem_centralizer_iff.1 (hC hc) k hk
      exact Subgroup.mem_comap.2
        (by simpa [MulAut.conj_apply, this] using Subgroup.mem_sup_right hc)
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa [MulAut.conj_apply] using Subgroup.mem_comap.1 (key k hk hx)
  · have := key k⁻¹ (K.inv_mem hk) hx
    simpa [MulAut.conj_apply, mul_assoc] using Subgroup.mem_comap.1 this

namespace Exc1616

variable {M V₀ V U S H : Subgroup G}
  {φ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))}

theorem ktCfg16 (e : Exc1616 M V₀ V U S H φ) :
    KTCfg16 U V₀ V (iSub16 V H) (conjClosure V H) (tSub16 V₀ S) (qSub16 V₀ V S H) := by
  obtain ⟨k, g⟩ := e.exists_gen
  have c := e.cfg
  have hV := c.cex.hyp.h6.elemAbelian
  have hI := Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hPC := Cex16.inf_pCoreOf_eq c.one c.five c.std c.cex c.min.fam16 c.not_le
  have hQT := e.qSub16_le_tSub16
  have hZP : U ⊔ V₀ ≤ pCoreOf 2 H := by
    rw [← hPC]
    exact inf_le_right
  exact
    { comm_V := fun x hx y hy => B2F.isElemAbelian_comm hV hx hy
      sq_V := fun x hx => by simpa [pow_two] using hV.2 x hx
      comm_I := fun x hx y hy => B2F.isElemAbelian_comm hI hx hy
      sq_I := fun x hx => by simpa [pow_two] using hI.2 x hx
      le_V := sup_le c.cex.le c.cex.hyp.h6.le
      le_I := c.le_iSub16
      V_le_K := le_conjClosure V H
      I_le_K := c.iSub16_le_conjClosure
      V_le_T := c.V_le_tSub16
      I_le_Q := c.iSub16_le_qSub16
      Q_le_T := hQT
      Q_le := c.qSub16_le_centralizer hQT
      T_le := fun t ht => c.le_normalizer_qSub16 (c.min.fam16.1 ht.1)
      inf_le := fun x hx => by
        rw [← hPC]
        exact ⟨hx.1, c.qSub16_le_pCoreOf hx.2⟩
      comm_mem := fun x hx k hk => e.comm_mem_qSub16 hx hk
      exists_mul := fun t ht => e.exists_mul_qSub16 ht
      mem_of_comm := fun v hv hvZ w hw hc => g.mem_sup_of_comm hv hvZ hw hc
      card_eq := g.card_iSub16_eq
      inf_centralizer_le := e.inf_centralizer_le_sup
      inf_eq_bot := c.inf_centralizer_eq_bot
      comm_mem_V₀ := fun t ht v hv => c.cex.comm_mem_V₀ ht.1 hv
      U_le := fun u hu => Subgroup.mem_centralizer_iff.2 fun k hk =>
        (Subgroup.mem_centralizer_iff.1 (c.conjClosure_le_centralizer hk) u hu).symm
      not_le := fun hVle => c.not_le (hVle.trans hZP)
      sq_C := fun x hx => e.mul_self_eq_one_of_mem hx }

theorem exists_fam16Q (e : Exc1616 M V₀ V U S H φ) {R : Subgroup G}
    (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) (hSR : S ≤ R) :
    ∃ H' : Subgroup G, Fam16Q M V₀ U R H' := by
  have c := e.cfg
  have hQT := e.qSub16_le_tSub16
  by_cases hA : ∀ A ∈ elemFamilyIn 2 (tSub16 V₀ S), A ≤ qSub16 V₀ V S H
  · exact c.exists_fam16Q_of_forall_le hR hSR hQT hA
  obtain ⟨A, hAmem, hAQ⟩ : ∃ A ∈ elemFamilyIn 2 (tSub16 V₀ S), ¬ A ≤ qSub16 V₀ V S H := by
    by_contra hc
    exact hA fun A hA' => by_contra fun h => hc ⟨A, hA', h⟩
  have kt := e.ktCfg16
  have hel := kt.isElementaryAbelian_sup
  have hQ₁T : iSub16 V H ⊔ (tSub16 V₀ S ⊓ centralizer (conjClosure V H : Set G)) ≤
      tSub16 V₀ S := sup_le c.iSub16_le_tSub16 inf_le_left
  obtain ⟨-, -, hAcard⟩ := mem_elemFamilyIn.1 hAmem
  have hcard := (kt.card_le_of_offender hAmem hAQ).trans kt.card_sup_eq.symm.le
  have hQ₁mem : iSub16 V H ⊔ (tSub16 V₀ S ⊓ centralizer (conjClosure V H : Set G)) ∈
      elemFamilyIn 2 (tSub16 V₀ S) := by
    refine mem_elemFamilyIn.2 ⟨hQ₁T, hel, le_antisymm ?_ ?_⟩
    · exact card_le_pow_pRank_of_le hQ₁T hel
    · exact hAcard ▸ hcard
  have hRN : R ≤ normalizer ((iSub16 V H ⊔ (tSub16 V₀ S ⊓ centralizer (conjClosure V H : Set G)) :
      Subgroup G) : Set G) := by
    intro τ hτ
    obtain ⟨hτM, -, hτcomm⟩ := FourteenTwo.mem_cTilde_iff_comm.1 (hR.le hτ)
    refine kt.mem_normalizer_of_mem_elemFamilyIn ?_ ?_ hτcomm hQ₁mem
    · exact Cex16.le_normalizer_tSub16 c.one c.std c.cex hR.isPGroup hR.le hSR hτ
    · rw [c.cex.hyp.h6.normalizer_eq]
      exact hτM
  have hKN : conjClosure V H ≤ normalizer ((iSub16 V H ⊔
      (tSub16 V₀ S ⊓ centralizer (conjClosure V H : Set G)) : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_centralizer
      (c.conjClosure_le_H.trans (le_normalizer_conjClosure _ _)) inf_le_right
  refine ⟨_, fam16Q_normalizer ?_ ?_ hRN hKN c.conjClosure_le_centralizer
    c.not_conjClosure_le⟩
  · exact fun x hx y hy => B2F.isElemAbelian_comm
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).1 hel) hx hy
  · exact c.le_iSub16.trans le_sup_left

end Exc1616

end CFSG.LocalAnalysis.WeakClosure81

end
