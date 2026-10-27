module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepN2dA
public import CFSG.Quasithin.Background.GoldschmidtB69DeepHypB
public import CFSG.Quasithin.Background.GoldschmidtB69DeepSwap
public import CFSG.Quasithin.Background.Sp4InfA6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.Quasithin.Background.GoldschmidtB69DeepQ
public import CFSG.Quasithin.Background.GoldschmidtB69DeepSecData

public section

namespace CFSG.Quasithin

open CFSG.Open B6
open scoped commutatorElement

namespace B69

theorem asB69NoRankTwoTripleA6_proved :
    AsB69NoRankTwoTripleA6 := by
  intro V _ _ hV X T M A L hH W hW B hBA hB hc
  obtain ⟨ℓ, hℓs, hcent, hLbq, hIrr, hFstar, hLbn, hℓa⟩ := sectionFittingData hV hH hW
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨-, hcard, hq, K, _, _, Γ₀, hK4, -, hhat, -, π, hreal, -⟩ := hc
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  have hperf : Group.IsPerfect ↥(autSec L W (W ⊓ fixV L)) := hLbq.1
  have hinj : Function.Injective π := natRealizes_injective hreal
  let eπ : ↥Γ₀ ≃* ↥(autSec L W (W ⊓ fixV L)) := MulEquiv.ofBijective π ⟨hinj, hreal.1⟩
  have hcenter : (Subgroup.center ↥Γ₀).map eπ.toMonoidHom =
      Subgroup.center ↥(autSec L W (W ⊓ fixV L)) := Subgroup.map_center_eq eπ
  have hZ : Nat.card ↥(Subgroup.center ↥(autSec L W (W ⊓ fixV L))) = 3 := by
    rw [← hcenter, Subgroup.card_map_of_injective (f := eπ.toMonoidHom) eπ.injective]
    exact hhat.2.1
  let e : ↥(autSec L W (W ⊓ fixV L)) ⧸ Subgroup.center ↥(autSec L W (W ⊓ fixV L)) ≃*
      ↥(alternatingGroup (Fin 6)) :=
    (QuotientGroup.congr _ _ eπ hcenter).symm.trans hhat.2.2.some
  obtain ⟨ρ, hρr, hρx⟩ := Hyp.exists_hyperoval hS2 hcard hperf hZ e
    (CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hIrr)
  have hmem : ∀ l : ↥L, ρ (ℓ l) ∈ alternatingGroup (Fin 6) := fun l => by
    rw [← hρr]
    exact ⟨ℓ l, rfl⟩
  let π₀ : ↥L →* ↥(alternatingGroup (Fin 6)) :=
    (ρ.comp ℓ).codRestrict (alternatingGroup (Fin 6)) hmem
  have hπ₀ : Function.Surjective π₀ := by
    intro y
    have : (y : Equiv.Perm (Fin 6)) ∈ ρ.range := by
      rw [hρr]
      exact y.2
    obtain ⟨m, hm⟩ := this
    obtain ⟨l, rfl⟩ := hℓs m
    exact ⟨l, Subtype.ext hm⟩
  have hcenter6 : Subgroup.center ↥(alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hev : Even (Nat.card ↥(alternatingGroup (Fin 6))) := by
    rw [Sp4Inf.card_alt_six']
    exact ⟨180, by norm_num⟩
  obtain ⟨t, ht, ht', thb, hthb, hnot⟩ :=
    exists_twist_element hmp hL Sp4Inf.swapGeo_alt6 hev hcenter6 π₀ hπ₀
  set W₂ : Subgroup V := W.map (t⁻¹ : MulAut V).toMonoidHom with hW₂
  have hW₂irr : W₂ ∈ IrrPlus L (⊤ : Subgroup V) :=
    irrPlus_map (g := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht' x hx)
      (fun x hx => by rw [inv_inv]; exact ht x hx) hW
  have hne : W ≠ W₂ := by
    intro heq
    have hWt : ∀ w, w ∈ W ↔ t w ∈ W := fun w => by
      have h1 : w ∈ W₂ ↔ t w ∈ W := by rw [hW₂, mem_map_aut_iff, inv_inv]
      rw [← h1, ← heq]
    have hfixt : ∀ w ∈ fixV L, t w ∈ fixV L := fun w hw => mem_fixV_of_conj ht' hw
    have hfixt' : ∀ w ∈ fixV L, t⁻¹ w ∈ fixV L := fun w hw =>
      mem_fixV_of_conj (t := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht x hx) hw
    have hUt : ∀ w, w ∈ W ⊓ fixV L ↔ t w ∈ W ⊓ fixV L := fun w => by
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hWt w]
      refine and_congr_right fun _ => ⟨hfixt w, fun h => ?_⟩
      simpa using hfixt' _ h
    obtain ⟨τ, hτ⟩ := exists_aut_sec hLW hLZ ht hWt hUt
    have hτN := mem_autSec_conj_iff hLW hLZ ht ht' hτ
    obtain ⟨g, hg⟩ := hρx τ hτN
    apply hnot
    refine ⟨g, fun y => ?_⟩
    obtain ⟨l, rfl⟩ := hπ₀ y
    have h1 : thb (π₀ l) = π₀ ⟨t * l * t⁻¹, ht l l.2⟩ := hthb l _ rfl
    rw [h1]
    have hrel : ((ℓ ⟨t * l * t⁻¹, ht l l.2⟩ : ↥(autSec L W (W ⊓ fixV L))) :
        MulAut (Sec W (W ⊓ fixV L))) =
        τ * ((ℓ l : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L))) * τ⁻¹ := by
      rw [hℓa hLW hLZ, hℓa hLW hLZ]
      refine MulEquiv.ext fun s => ?_
      simpa [MulAut.mul_apply] using (hτ l (τ⁻¹ s)).symm
    exact hg (ℓ l) (ℓ ⟨t * l * t⁻¹, ht l l.2⟩) hrel
  exact false_of_one_le_rAV hV hA hLq hLA hW hW₂irr hne
    (one_le_rAV_of_qOf hV hA hLq hLA hW hq.ge)

end B69

end CFSG.Quasithin
