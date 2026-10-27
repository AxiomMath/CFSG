module

public import CFSG.Quasithin.Background.B69SL3Bridge

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_natural_data_sp4_gen {L A : Subgroup (MulAut V)} {I : Subgroup ↥(redU L A)}
    (hI : I ∈ IrrPlus (autSub L (redU L A)) (⊤ : Subgroup ↥(redU L A))) {n : ℕ}
    {H : Subgroup (MulAut (Sec I (I ⊓ fixV (autSub L (redU L A)))))} (hLH : secL L A I ≤ H)
    (hn : BinaryNaturalSp4 H ⊤ ⊥ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ r : ↥L →* ↥(StatedSp 2 K), (secL L A I = H → Function.Surjective r) ∧
        (((secL L A I).subgroupOf H).Normal → r.range.Normal) ∧
        (Nontrivial ↥(secL L A I) → r.range ≠ ⊥) ∧
        ∃ e₁ : Sec (I.map (redU L A).subtype) (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K,
          ∀ (hLW : L ≤ stabSub (I.map (redU L A).subtype)) (hLU : L ≤ stabSub (fixV L))
            (l : ↥L) (s : Sec (I.map (redU L A).subtype) (fixV L)),
            e₁ (B5.secHom L hLW hLU l s) =
              matAut ((r l : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s) := by
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
  let πe : ↥(StatedSp 2 K) ≃* ↥H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_realizesVia (StatedSp 2 K) hπ
  let ρH : ↥L →* ↥H := (Subgroup.inclusion hLH).comp ρ
  let r : ↥L →* ↥(StatedSp 2 K) := πe.symm.toMonoidHom.comp ρH
  have hπr : ∀ l, π (r l) = ρH l := fun l => πe.apply_symm_apply (ρH l)
  have hrange : r.range = ((secL L A I).subgroupOf H).map πe.symm.toMonoidHom := by
    rw [show r = πe.symm.toMonoidHom.comp ρH from rfl, MonoidHom.range_comp]
    congr 1
    rw [show ρH = (Subgroup.inclusion hLH).comp ρ from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 hρ, Subgroup.map_top, Subgroup.inclusion_range]
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
  refine ⟨K, hKf, hKfin, hK, r, fun hEq g => ?_, fun hnorm => ?_, fun hnt => ?_, E.symm.trans e',
    fun hLW' hLU' l s => ?_⟩
  ·
    have hmem : ((π g : ↥H) : MulAut (Sec I (I ⊓ fixV (autSub L (redU L A))))) ∈ secL L A I := by
      rw [hEq]
      exact (π g).2
    obtain ⟨l, hl⟩ := hρ ⟨_, hmem⟩
    refine ⟨l, πe.injective ?_⟩
    have h1 : πe (r l) = ρH l := hπr l
    rw [h1]
    apply Subtype.ext
    exact congrArg (fun x : ↥(secL L A I) =>
      ((x : ↥(secL L A I)) : MulAut (Sec I (I ⊓ fixV (autSub L (redU L A)))))) hl
  · rw [hrange]
    exact hnorm.map πe.symm.toMonoidHom πe.symm.surjective
  · intro hbot
    apply (not_nontrivial_iff_subsingleton.2 ?_) hnt
    refine ⟨fun ψ ψ' => ?_⟩
    have hone : ∀ ψ : ↥(secL L A I), ψ = 1 := by
      intro ψ
      obtain ⟨l, rfl⟩ := hρ ψ
      have hrl : r l = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨l, rfl⟩)
      have h1 : ρH l = 1 := by
        rw [← hπr l, hrl]
        exact map_one π
      apply Subtype.ext
      exact congrArg (fun x : ↥H => ((x : ↥H) : MulAut (Sec I (I ⊓ fixV (autSub L (redU L A)))))) h1
    rw [hone ψ, hone ψ']
  · have hE : ∀ x, E (ρ₀ l x) = B5.secHom L hLW' hLU' l (E x) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H w => rfl
    have h1 : E.symm (B5.secHom L hLW' hLU' l s) = ρ₀ l (E.symm s) := by
      rw [MulEquiv.symm_apply_eq, hE, MulEquiv.apply_symm_apply]
    show e' (E.symm (B5.secHom L hLW' hLU' l s)) = matAut _ (e' (E.symm s))
    rw [h1]
    have h2 : ρ₀ l (E.symm s) = ((π (r l) : ↥H) : MulAut _) (E.symm s) := by
      rw [hπr]
      rfl
    rw [h2]
    exact he' (r l) (E.symm s)

omit [Finite V] in
theorem exists_natural_data_sp4 {L A : Subgroup (MulAut V)} {I : Subgroup ↥(redU L A)}
    (hI : I ∈ IrrPlus (autSub L (redU L A)) (⊤ : Subgroup ↥(redU L A))) {n : ℕ}
    (hn : BinaryNaturalSp4 (secL L A I) ⊤ ⊥ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ r : ↥L →* ↥(StatedSp 2 K), Function.Surjective r ∧
        ∃ e₁ : Sec (I.map (redU L A).subtype) (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K,
          ∀ (hLW : L ≤ stabSub (I.map (redU L A).subtype)) (hLU : L ≤ stabSub (fixV L))
            (l : ↥L) (s : Sec (I.map (redU L A).subtype) (fixV L)),
            e₁ (B5.secHom L hLW hLU l s) =
              matAut ((r l : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s) := by
  obtain ⟨K, hKf, hKfin, hK, r, hr, -, -, e₁, he₁⟩ := exists_natural_data_sp4_gen hI le_rfl hn
  exact ⟨K, hKf, hKfin, hK, r, hr rfl, e₁, he₁⟩

end B69

end CFSG.Quasithin
