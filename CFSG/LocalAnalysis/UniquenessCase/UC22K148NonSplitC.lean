module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148NonSplitB
import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacData
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Core
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Split
import CFSG.LocalAnalysis.UniquenessCase.UC22K148SplitFac
import CFSG.RankThree.FFModules.FixSubConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem card_mul_card_fixSub_le_of_isFactor148
    [Finite G] [Finite V]
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) {m : ℕ} {Hs : Fin m → Subgroup G} (hD : IsInternalDirect ⊤ Hs)
    (hF : ∀ i, IsFactor148 (Hs i)) (hnc : ∀ i, ¬ IsComponentOf (Hs i) ⊤) {X : Subgroup G}
    (hX : IsElemAbelian 2 X) : Nat.card X * Nat.card (fixSub ρ X) ≤ Nat.card V := by
  obtain ⟨O, J, hJ, -, -, hON, hF0, hfaith, hcompl, hNE, -⟩ :=
    exists_coreData_of_isFactor148 hρ hshape hH hD hF
  have hJu : ∀ i, i ∈ J := fun i => by_contra fun hi => hnc i ((hJ i).1 hi)
  refine card_mul_card_fixSub_le_card (fun k => commOn ρ (O k) ⊤) (fun k => fixSub ρ (O k)) J
    (fun k hk => ⟨hcompl k hk, fun g _ u hu => ?_,
      fun g _ w hw => rep_apply_mem_fixSub_of_normal ρ (hON k hk) g hw,
      fun Y hY => hNE k hk Y (hX.mono hY)⟩) fun x _ hx => ?_
  · have hNN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (O k : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.2 (hON k hk)]
    exact (invariant_commOn_top hNN).2 g (Subgroup.mem_top g) u hu
  · have h := mem_iSup_of_forall_apply_eq hD (N := fun k => commOn ρ (O k) ⊤)
      (fun k _ i hik h hh n hn => hF0 k i (Ne.symm hik) h hh n hn) hfaith hx
    rw [le_bot_iff.1 (iSup₂_le fun i hi => (hi (hJu i)).elim)] at h
    exact (Subgroup.mem_bot).1 h

theorem false_of_pCore_sup_zpowers_eq_bot
    [Finite G] [Finite V]
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G))
    (hinner : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ¬ ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u)
    {N : Subgroup G} {a : G} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hcompl : IsCompl (commOn ρ N ⊤) (fixSub ρ N)) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x)
    (hNE : ∀ X : Subgroup G, IsElemAbelian 2 X → NoExcess ρ X (commOn ρ N ⊤))
    (hO₀ : CFSG.pCore 2 ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊥) : False := by
  have hW : ∀ g : G, ∀ w ∈ fixSub ρ N, ρ g w ∈ fixSub ρ N := fun g w hw =>
    rep_apply_mem_fixSub_of_normal ρ hN g hw
  obtain ⟨m, Hs, hD, hF⟩ := hasFactors148_sup_zpowers hρ hshape hH IH hN hN1 hcompl.sup_eq_top
    ha2 hfa hact hout hO₀
  have hnc := not_isComponentOf_sup_zpowers hρ hH hshape hinner hN hcompl.sup_eq_top
    (sup_sup_zpowers_eq_top hact) hD
  exact false_of_card_fixSub_subRep_le hH hN hW hcompl ha2 hfa hact hout hNE fun X hX =>
    card_mul_card_fixSub_le_of_isFactor148
      (injective_subRep_sup_zpowers hρ hN hW hcompl.sup_eq_top ha2 hO₀)
      (fun L hL => allowed_shape_sup_zpowers (cenOn_commOn_normal hN) hshape hL)
      (hP_subRep_sup_zpowers_eq_top hρ hH hN hW ha2 hfa hact hout) hD hF hnc hX

theorem hasFactors148_of_forall_isFactor148
    [Finite G] [Finite V]
    (hO : CFSG.pCore 2 G = ⊥) (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G))
    (hinner : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ¬ ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u)
    {N : Subgroup G} {a : G} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hcompl : IsCompl (commOn ρ N ⊤) (fixSub ρ N)) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x)
    (hNE : ∀ X : Subgroup G, IsElemAbelian 2 X → NoExcess ρ X (commOn ρ N ⊤))
    (hfac : ∀ r : G, r * r = 1 → r ∈ cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a →
      r ∉ N ⊔ cenOn ρ ⊤ (commOn ρ N ⊤) →
      (N ⊔ Subgroup.zpowers r) ⊓ cenOn ρ ⊤ (commOn ρ N ⊤) = ⊥ →
      IsFactor148 (N ⊔ Subgroup.zpowers r)) :
    HasFactors148 G := by
  rcases split_or_pCore_eq_bot hO hN ha2 hfa hact hout with
    ⟨r, hr2, hrK, hrNK, hMn, hMK, hMKsup, hMc⟩ | hO₀
  · exact hasFactors148_of_split hO hρ hshape hH IH hN hN1 hcompl.sup_eq_top hr2 hMn hMK hMKsup
      hMc (hfac r hr2 hrK hrNK hMK)
  · exact (false_of_pCore_sup_zpowers_eq_bot hρ hshape hH IH hinner hN hN1 hcompl ha2 hfa hact
      hout hNE hO₀).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
