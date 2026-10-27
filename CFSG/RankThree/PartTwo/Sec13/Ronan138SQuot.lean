module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SModel
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SField

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)


theorem actsPGL_of_maximal {G : Type} [Group G] [Finite G] {K A : Subgroup G} {e : G}
    (hKq : CFSG.IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hA27 : Nat.card A = 27) (hAN : A ≤ Subgroup.normalizer (K : Set G)) (heA : e ∈ A)
    (he1 : e ≠ 1) (hCA : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e)
    {π : Bool} {p f : ℕ} {F : Type} [Field F] (hK : Sec4.PiField π p f F)
    (hq : Sec4.ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (ψ : K ⧸ aschbacherSolvableCore 3 K ≃*
      CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ f) F)) :
    ∀ x ∈ A, ∃ y, ActsPGL ψ x y := by
  intro x hxA
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hAN hxA
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ₀, hΦ₀⟩ := Sec21.Item211Proof.exists_lEquiv hAN
  have hLq : CFSG.IsQuasisimple (Sec21.Item211Proof.lOne K A) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Φ₀ hKq
  haveI := Sec21.Item211Proof.normal_lOne hAN
  have hmax := Sec21.Item211Proof.maximal_aOne (L := K) hAe hAmax
  have hcard₁ : Nat.card (Sec21.Item211Proof.aOne K A) = 27 := by
    rw [← Nat.card_congr (Sec21.Item211Proof.aEquiv (L := K) hA3).toEquiv, hA27]
  have hc₁ : orderOf (Sec21.Item211Proof.piX K A ⟨e, Subgroup.mem_sup_right heA⟩) = 3 := by
    have h1 : Sec21.Item211Proof.piX K A ⟨e, Subgroup.mem_sup_right heA⟩ =
        ((Sec21.Item211Proof.aEquiv (L := K) hA3 ⟨e, heA⟩ : Sec21.Item211Proof.aOne K A) :
          Sec21.Item211Proof.QuotX K A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 e heA) he1
  have hCA₁ := Sec21.Item211Proof.aOne_inf_centralizer hA3 hAN heA hCA
  let e' : Sec21.Item211Proof.lOne K A ≃* projImage (Sec4.slPi π 3 (p ^ f) F) :=
    Φ₀.symm.trans ψ
  have hPGL := forall_isPGLAtP_of_card_eq hK hq hq2 hLq e' hmax hcard₁ hc₁ hCA₁
  obtain ⟨y, hy⟩ := hPGL (Sec21.Item211Proof.piX K A ⟨x, Subgroup.mem_sup_right hxA⟩)
    (Sec21.Item211Proof.piX_mem_aOne hxA)
  have ha₁ := Sec21.Item211Proof.mem_normalizer_lOne hAN
    (Sec21.Item211Proof.piX K A ⟨x, Subgroup.mem_sup_right hxA⟩)
  refine ⟨y, hxN, hy.1, fun z => ?_⟩
  have hw := Sec21.Item211Proof.lEquiv_conj hΦ₀ hxA hxN ha₁ z
  have hfwd : e' (Φ₀ z) = ψ z := by
    show ψ (Φ₀.symm (Φ₀ z)) = ψ z
    rw [MulEquiv.symm_apply_apply]
  have hsym : e'.symm (ψ z) = Φ₀ z := by
    rw [← hfwd, MulEquiv.symm_apply_apply]
  have hψw : e' (Φ₀ (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) z)) =
      ψ (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) z) := by
    show ψ (Φ₀.symm (Φ₀ _)) = _
    rw [MulEquiv.symm_apply_apply]
  have hz := hy.2 (ψ z)
  rw [Sec4.coe_slAct_eqP, hsym] at hz
  rw [← hz, ← hψw, hw]
  congr 2

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
