module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSCox
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSQX
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSIsoA
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSPhi

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 6)

theorem uIso_comp_permAct (Ψ : C.UIso) {ψ : Equiv.Perm (Fin 6) →* ↥M}
    (hψ : ∀ σ, C.θ (ψ σ) = σ) (σ : Equiv.Perm (Fin 6)) :
    ((Subgroup.inclusion (C.S.W_le_Q.trans (pCoreOf_le_self M))).comp
        Ψ.ψ.toMonoidHom).comp (CFSG.Quasithin.C116Two.permAct 6 σ).toMonoidHom =
      (MulAut.conj (ψ σ)).toMonoidHom.comp
        ((Subgroup.inclusion (C.S.W_le_Q.trans (pCoreOf_le_self M))).comp Ψ.ψ.toMonoidHom) := by
  refine MonoidHom.ext fun v => Subtype.ext ?_
  have h := Ψ.equivar (ψ σ) (Multiplicative.toAdd v)
  rw [hψ σ] at h
  exact h.symm

theorem nonempty_mulEquiv_yamakiHat (Ψ : C.UIso) {ψ : Equiv.Perm (Fin 6) →* ↥M}
    (hψ : ∀ σ, C.θ (ψ σ) = σ) (hker : ∀ m : ↥M, C.θ m = 1 → (m : G) ∈ blockU X) :
    Nonempty (↥M ≃* YamakiHat) := by
  set ι : ↥(blockU X) →* ↥M := Subgroup.inclusion (C.S.W_le_Q.trans (pCoreOf_le_self M))
  set Φ : YamakiHat →* ↥M :=
    SemidirectProduct.lift (ι.comp Ψ.ψ.toMonoidHom) ψ (C.uIso_comp_permAct Ψ hψ)
  have hΦ : ∀ p : YamakiHat, Φ p = ι (Ψ.ψ p.left) * ψ p.right := fun p => rfl
  have hθι : ∀ w, C.θ (ι w) = 1 := fun w => C.theta_Q (by norm_num) (C.S.W_le_Q w.2)
  refine ⟨(MulEquiv.ofBijective Φ ⟨?_, fun m => ?_⟩).symm⟩
  · rw [injective_iff_map_eq_one]
    intro p hp
    have hr : p.right = 1 := by
      have h1 := congrArg C.θ hp
      rwa [hΦ, map_mul, hθι, one_mul, hψ, map_one] at h1
    have hl : ι (Ψ.ψ p.left) = 1 := by
      rw [hΦ, hr, map_one, mul_one] at hp
      exact hp
    have hl1 : Ψ.ψ p.left = 1 := Subgroup.inclusion_injective _ (hl.trans (map_one ι).symm)
    exact SemidirectProduct.ext ((map_eq_one_iff Ψ.ψ Ψ.ψ.injective).1 hl1) hr
  · have hk : C.θ (m * (ψ (C.θ m))⁻¹) = 1 := by rw [map_mul, map_inv, hψ, mul_inv_cancel]
    refine ⟨⟨Ψ.ψ.symm ⟨_, hker _ hk⟩, C.θ m⟩, ?_⟩
    rw [hΦ]
    apply Subtype.ext
    simp [ι]

end Cfg

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

section Residual

variable (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M)
  (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x)
include hR2 hsurj hQ16 hij hπ hK h

theorem sixIso_nonempty (hel : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) :
    Nonempty (↥M ≃* YamakiHat) := by
  obtain ⟨-, -, -, t, ht2, htθ, -, -⟩ := D.sixInv_exists hR2 hsurj hQ16 hx hij hπ hK h
  have hodd : Equiv.Perm.sign (C.θ t) = -1 := by rw [htθ, Equiv.Perm.sign_swap hij]
  have hQX := D.Q_le_X hR2 hsurj hel t ht2 hodd
  obtain ⟨ψ, hψ⟩ := D.sixCox_exists_section hR2 hsurj hQ16 hx hij hπ hK h
  have hQW := D.sixIsoA_eq_blockU hR2 hsurj hel hQX hψ
  have hZR : blockZ X = Rc X := by
    rw [C.S.R_eq_inf, hQW]
    rfl
  obtain ⟨Ψ⟩ := C.nonempty_uIso (hZR ▸ hR2)
  refine C.nonempty_mulEquiv_yamakiHat Ψ hψ fun m hm => ?_
  rw [← hQW, ← Subgroup.mem_subgroupOf, ← C.theta_ker_eq hR2.le]
  exact hm

end Residual

end Cfg.PiData

theorem sixSymResidualElem_holds : SixSymResidualElem :=
  fun _ _ _ _ _ _ D hR2 hsurj _ hx _ _ hij hπ hK h hel =>
    D.sixIso_nonempty hR2 hsurj (D.card_Q_ne_sixteen_of_card_Rc hR2) hx hij hπ hK h hel

end CFSG.RankThree.PartTwo.Sec19.SolEven
