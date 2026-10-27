module

public import CFSG.Quasithin.Background.B69Mod
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem map_fix_eq {L : Subgroup (MulAut V)} {U : Subgroup V} (hL : L ≤ stabSub U) (Ib : Subgroup ↥U) :
    (Ib ⊓ fixV (autSub L U)).map U.subtype = Ib.map U.subtype ⊓ fixV L := by
  have hIU : Ib.map U.subtype ≤ U := Subgroup.map_subtype_le Ib
  rw [Subgroup.map_inf _ _ _ U.subtype_injective, map_subtype_fixV_autSub hL, ← inf_assoc,
    inf_eq_left.2 hIU]

omit [Finite V] in
theorem exists_natural_data {L A : Subgroup (MulAut V)} {I : Subgroup ↥(redU L A)}
    (hI : I ∈ IrrPlus (autSub L (redU L A)) (⊤ : Subgroup ↥(redU L A))) {n : ℕ}
    (hn : BinaryNaturalSL (secL L A I) ⊤ ⊥ 3 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ r : ↥L →* ↥(StatedSL 3 K), Function.Surjective r ∧
        ∃ e₁ : Sec (I.map (redU L A).subtype) (fixV L) ≃* StdMod (Fin 3) K,
          ∀ (hLW : L ≤ stabSub (I.map (redU L A).subtype)) (hLU : L ≤ stabSub (fixV L))
            (l : ↥L) (s : Sec (I.map (redU L A).subtype) (fixV L)),
            e₁ (B5.secHom L hLW hLU l s) = matAut ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) (e₁ s) := by
  classical
  obtain ⟨K, hKf, hKfin, hK, π, hπ⟩ := hn
  have hLU : L ≤ stabSub (redU L A) := le_stabSub_redU L A
  have hinv := (mem_irrPlus_top_iff.1 hI).1
  have hXI : autSub L (redU L A) ≤ stabSub I := B1.le_stabSub_of_invariant hinv
  have hC : ∀ x ∈ autSub L (redU L A), ∀ w ∈ I ⊓ fixV (autSub L (redU L A)),
      x w ∈ I ⊓ fixV (autSub L (redU L A)) := isInv_inf hinv (isInv_fixV _)
  have hXC : autSub L (redU L A) ≤ stabSub (I ⊓ fixV (autSub L (redU L A))) :=
    B1.le_stabSub_of_invariant hC
  let σb := B5.secHom (autSub L (redU L A)) hXI hXC
  let f₁ : ↥L →* ↥(autSub L (redU L A)) :=
    ((resHom (redU L A)).comp (Subgroup.inclusion hLU)).codRestrict (autSub L (redU L A))
      (fun l => mem_autSub.2 ⟨Subgroup.inclusion hLU l, l.2, rfl⟩)
  have hf₁ : Function.Surjective f₁ := by
    intro φ
    obtain ⟨g, hgL, hg⟩ := mem_autSub.1 φ.2
    exact ⟨⟨(g : MulAut V), hgL⟩, Subtype.ext hg⟩
  let ρ₀ : ↥L →* MulAut (Sec I (I ⊓ fixV (autSub L (redU L A)))) := σb.comp f₁
  have hρ₀ : ∀ l, ρ₀ l ∈ secL L A I := fun l => by
    have : ρ₀ l ∈ σb.range := ⟨f₁ l, rfl⟩
    rwa [B5.range_secHom] at this
  let ρ : ↥L →* ↥(secL L A I) := ρ₀.codRestrict (secL L A I) hρ₀
  have hρ : Function.Surjective ρ := by
    intro ψ
    have : (ψ : MulAut (Sec I (I ⊓ fixV (autSub L (redU L A))))) ∈ σb.range := by
      rw [B5.range_secHom]
      exact ψ.2
    obtain ⟨x, hx⟩ := this
    obtain ⟨l, rfl⟩ := hf₁ x
    exact ⟨l, Subtype.ext hx⟩
  have hπinj : Function.Injective π := natRealizes_injective hπ
  let πe : ↥(StatedSL 3 K) ≃* ↥(secL L A I) := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_realizesVia (StatedSL 3 K) hπ
  let r : ↥L →* ↥(StatedSL 3 K) := πe.symm.toMonoidHom.comp ρ
  have hr : Function.Surjective r := πe.symm.surjective.comp hρ
  have hπr : ∀ l, π (r l) = ρ l := fun l => πe.apply_symm_apply (ρ l)
  have hLW : L ≤ stabSub (I.map (redU L A).subtype) := by
    have := (mem_irrPlus_top_iff.1 (B1Red.mem_irrPlus_of_autSub hLU hI)).1
    exact B1.le_stabSub_of_invariant this
  have hfixeq := map_fix_eq hLU I
  have hsub : ((I ⊓ fixV (autSub L (redU L A))).map (redU L A).subtype).subgroupOf
      (I.map (redU L A).subtype) = (fixV L).subgroupOf (I.map (redU L A).subtype) := by
    rw [hfixeq, Subgroup.inf_subgroupOf_left]
  let E : Sec I (I ⊓ fixV (autSub L (redU L A))) ≃* Sec (I.map (redU L A).subtype) (fixV L) :=
    (B1Red.secEquiv (redU L A) I (I ⊓ fixV (autSub L (redU L A)))).trans
      (QuotientGroup.quotientMulEquivOfEq hsub)
  refine ⟨K, hKf, hKfin, hK, r, hr, E.symm.trans e', fun hLW' hLU' l s => ?_⟩
  have hE : ∀ x, E (ρ₀ l x) = B5.secHom L hLW' hLU' l (E x) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H w => rfl
  have h1 : E.symm (B5.secHom L hLW' hLU' l s) = ρ₀ l (E.symm s) := by
    rw [MulEquiv.symm_apply_eq, hE, MulEquiv.apply_symm_apply]
  show e' (E.symm (B5.secHom L hLW' hLU' l s)) = matAut _ (e' (E.symm s))
  rw [h1]
  have h2 : ρ₀ l (E.symm s) = ((π (r l) : ↥(secL L A I)) : MulAut _) (E.symm s) := by
    rw [hπr]
    rfl
  rw [h2]
  exact he' (r l) (E.symm s)

end B69

end CFSG.Quasithin
