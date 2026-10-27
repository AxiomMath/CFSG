module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B69Mod
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H

namespace B69

theorem natural_data_sp4_gen {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {n : ℕ}
    {H : Subgroup (MulAut (Sec W (W ⊓ fixV L)))} (hLH : autSec L W (W ⊓ fixV L) ≤ H)
    (hn : BinaryNaturalSp4 H ⊤ ⊥ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ r : ↥L →* ↥(StatedSp 2 K), (autSec L W (W ⊓ fixV L) = H → Function.Surjective r) ∧
        (((autSec L W (W ⊓ fixV L)).subgroupOf H).Normal → r.range.Normal) ∧
        (Nontrivial ↥(autSec L W (W ⊓ fixV L)) → r.range ≠ ⊥) ∧
        ∃ e₁ : Sec W (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K,
          ∀ (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W (fixV L)),
            e₁ (B5.secHom L hLW hLU l s) =
              matAut ((r l : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s) := by
  classical
  obtain ⟨K, hKf, hKfin, hK, π, hπ⟩ := hn
  obtain ⟨hinv, -, -, -⟩ := mem_irrPlus_top_iff.1 hW
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant hinv
  have hLZ : L ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hinv (isInv_fixV L))
  let σ := B5.secHom L hLW hLZ
  have hσ : ∀ l, σ l ∈ autSec L W (W ⊓ fixV L) := fun l => by
    have : σ l ∈ σ.range := ⟨l, rfl⟩
    rwa [B5.range_secHom] at this
  let ρ : ↥L →* ↥(autSec L W (W ⊓ fixV L)) := σ.codRestrict _ hσ
  have hρ : Function.Surjective ρ := by
    intro ψ
    have : (ψ : MulAut (Sec W (W ⊓ fixV L))) ∈ σ.range := by
      rw [B5.range_secHom]
      exact ψ.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  have hπinj : Function.Injective π := natRealizes_injective hπ
  let πe : ↥(StatedSp 2 K) ≃* ↥H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_realizesVia (StatedSp 2 K) hπ
  let ρH : ↥L →* ↥H := (Subgroup.inclusion hLH).comp ρ
  let r : ↥L →* ↥(StatedSp 2 K) := πe.symm.toMonoidHom.comp ρH
  have hπr : ∀ l, π (r l) = ρH l := fun l => πe.apply_symm_apply (ρH l)
  have hrange : r.range = ((autSec L W (W ⊓ fixV L)).subgroupOf H).map πe.symm.toMonoidHom := by
    rw [show r = πe.symm.toMonoidHom.comp ρH from rfl, MonoidHom.range_comp]
    congr 1
    rw [show ρH = (Subgroup.inclusion hLH).comp ρ from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 hρ, Subgroup.map_top, Subgroup.inclusion_range]
  have hsub : (W ⊓ fixV L).subgroupOf W = (fixV L).subgroupOf W := Subgroup.inf_subgroupOf_left _ _
  let E : Sec W (W ⊓ fixV L) ≃* Sec W (fixV L) := QuotientGroup.quotientMulEquivOfEq hsub
  refine ⟨K, hKf, hKfin, hK, r, fun hEq g => ?_, fun hnorm => ?_, fun hnt => ?_, E.symm.trans e',
    fun hLW' hLU' l s => ?_⟩
  · have hmem : ((π g : ↥H) : MulAut (Sec W (W ⊓ fixV L))) ∈ autSec L W (W ⊓ fixV L) := by
      rw [hEq]
      exact (π g).2
    obtain ⟨l, hl⟩ := hρ ⟨_, hmem⟩
    refine ⟨l, πe.injective ?_⟩
    have h1 : πe (r l) = ρH l := hπr l
    rw [h1]
    apply Subtype.ext
    exact congrArg (fun x : ↥(autSec L W (W ⊓ fixV L)) =>
      ((x : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L)))) hl
  · rw [hrange]
    exact hnorm.map πe.symm.toMonoidHom πe.symm.surjective
  · intro hbot
    apply (not_nontrivial_iff_subsingleton.2 ?_) hnt
    refine ⟨fun ψ ψ' => ?_⟩
    have hone : ∀ ψ : ↥(autSec L W (W ⊓ fixV L)), ψ = 1 := by
      intro ψ
      obtain ⟨l, rfl⟩ := hρ ψ
      have hrl : r l = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨l, rfl⟩)
      have h1 : ρH l = 1 := by
        rw [← hπr l, hrl]
        exact map_one π
      apply Subtype.ext
      exact congrArg (fun x : ↥H => ((x : ↥H) : MulAut (Sec W (W ⊓ fixV L)))) h1
    rw [hone ψ, hone ψ']
  · have hE : ∀ x, E (σ l x) = B5.secHom L hLW' hLU' l (E x) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H w => rfl
    have h1 : E.symm (B5.secHom L hLW' hLU' l s) = σ l (E.symm s) := by
      rw [MulEquiv.symm_apply_eq, hE, MulEquiv.apply_symm_apply]
    show e' (E.symm (B5.secHom L hLW' hLU' l s)) = matAut _ (e' (E.symm s))
    rw [h1]
    have h2 : σ l (E.symm s) = ((π (r l) : ↥H) : MulAut _) (E.symm s) := by
      rw [hπr]
      rfl
    rw [h2]
    exact he' (r l) (E.symm s)

end B69

end CFSG.Quasithin
