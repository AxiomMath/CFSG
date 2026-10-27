module

public import CFSG.Quasithin.Background.FFC13M
public import CFSG.Quasithin.Background.B69Alt
public import CFSG.Quasithin.Background.FFC11B

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem fixV_eq_bot_of_alt (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (hLq : CFSG.Open.IsQuasisimple ↥L) {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    {J : Subgroup (MulAut (Sec W (W ⊓ fixV L)))} (π : Equiv.Perm (Fin 5) →* ↥J)
    (hπi : Function.Injective π) (hπ : (FFModel.symDn 5).RealizesVia J ⊤ ⊥ π)
    (hLeq : wtL L W = (alternatingGroup (Fin 5)).map (J.subtype.comp π)) :
    W ⊓ fixV L = ⊥ := by
  classical
  obtain ⟨hLW, hLU⟩ := stab_of_irr hW
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  set U : Subgroup V := W ⊓ fixV L with hUdef
  set ψ : Equiv.Perm (Fin 5) →* MulAut (Sec W U) := J.subtype.comp π with hψ
  have hψi : Function.Injective ψ := J.subtype_injective.comp hπi
  let Φ : ↥W →* Sec W U := QuotientGroup.mk' (U.subgroupOf W)
  let actW : ↥L →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hLW)
  let actS : ↥L →* MulAut (Sec W U) := B5.secHom L hLW hLU
  have hΦ : ∀ (g : ↥L) (w : ↥W), Φ (actW g w) = actS g (Φ w) := fun g w => rfl
  have hAeq : autSec L W U = (alternatingGroup (Fin 5)).map ψ := hLeq
  obtain ⟨e0, he0⟩ := exists_core_equiv (by decide : Odd 5) hπ
  let e : Sec W U ≃* ↥(G6.coreMod 5) := Subgroup.topEquiv.symm.trans e0
  have hle : autSec L W U ≤ ψ.range := by
    rw [hAeq]
    exact Subgroup.map_le_range _ _
  let ℓ' : ↥L →* ↥ψ.range := actS.codRestrict ψ.range (fun l => hle (by
    rw [← B5.range_secHom L hLW hLU]
    exact ⟨l, rfl⟩))
  let eψ : Equiv.Perm (Fin 5) ≃* ↥ψ.range := MonoidHom.ofInjective hψi
  let ρ : ↥L →* Equiv.Perm (Fin 5) := eψ.symm.toMonoidHom.comp ℓ'
  have hρψ : ∀ g : ↥L, ψ (ρ g) = actS g := by
    intro g
    have : eψ (ρ g) = ℓ' g := eψ.apply_symm_apply (ℓ' g)
    exact congrArg Subtype.val this
  have hρe : ∀ (g : ↥L) (s : Sec W U), e (actS g s) = G6.coreAct 5 (ρ g) (e s) := by
    intro g s
    have h1 := he0 (ρ g) ⟨s, trivial⟩ trivial
    have h2 : actS g s = ((π (ρ g) : ↥J) : MulAut (Sec W U)) s := by
      rw [← hρψ g]
      rfl
    show e0 ⟨actS g s, trivial⟩ = _
    rw [show (⟨actS g s, trivial⟩ : ↥(⊤ : Subgroup (Sec W U))) =
      ⟨((π (ρ g) : ↥J) : MulAut (Sec W U)) s, trivial⟩ from Subtype.ext h2]
    exact h1
  have hρA : ∀ g : ↥L, ρ g ∈ alternatingGroup (Fin 5) := by
    intro g
    have h1 : actS g ∈ autSec L W U := by
      rw [← B5.range_secHom L hLW hLU]
      exact ⟨g, rfl⟩
    rw [hAeq] at h1
    obtain ⟨τ, hτ, hτg⟩ := Subgroup.mem_map.1 h1
    have : τ = ρ g := hψi (hτg.trans (hρψ g).symm)
    rw [← this]
    exact hτ
  have hρs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ g : ↥L, ρ g = σ := by
    intro σ hσ
    have hσA : ψ σ ∈ autSec L W U := by
      rw [hAeq]
      exact Subgroup.mem_map_of_mem _ hσ
    rw [← B5.range_secHom L hLW hLU] at hσA
    obtain ⟨g, hg⟩ := hσA
    exact ⟨g, hψi ((hρψ g).trans hg)⟩
  have hker : ∀ g : ↥L, ρ g = 1 → ∀ w : ↥W, actW g w = w := by
    intro g hg w
    have h1 : actS g = 1 := by rw [← hρψ g, hg, map_one]
    have h2 : (g : MulAut V) ∈ centSec W U := by
      rw [← B5.mem_ker_secHom L hLW hLU g]
      exact h1
    have h3 := sec_triv_imp_triv hLq (A := L)
      (fun a ha l hl => L.mul_mem (L.mul_mem ha hl) (L.inv_mem ha)) hW
      (fun b hb w hw => hinv b hb w hw) g.2 (fun w hw => (h2.2 w hw).2) w w.2
    exact Subtype.ext h3
  have hrange : ρ.range = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      exact hρA g
    · intro σ hσ
      obtain ⟨g, hg⟩ := hρs σ hσ
      exact ⟨g, hg⟩
  have hQ : ¬ 2 ∣ (kleinStd.comap ρ).index := by
    rw [Subgroup.index_comap, hrange]
    have h1 := Subgroup.relIndex_mul_card kleinStd (alternatingGroup (Fin 5))
    rw [inf_eq_left.2 kleinStd_le_alternatingGroup, card_kleinStd] at h1
    have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [h2] at h1
    omega
  obtain ⟨σQ, hσQs, hσQe⟩ := exists_sec_klein actW actS Φ (QuotientGroup.mk'_surjective _) hΦ
    (B1.sq_eq_one_sub hV W) e ρ hρe (fun σ hσ => hρs σ (kleinStd_le_alternatingGroup hσ)) hker
  obtain ⟨σ', hσ's, hσ'e⟩ := avg_section actW actS Φ hΦ (sq_eq_one_sec hV W U)
    (kleinStd.comap ρ) hQ σQ hσQs (fun q hq s => hσQe q hq s)
  have hcommK : ∀ (l : ↥L) (w : ↥W), actW l w * w⁻¹ ∈ σ'.range := by
    intro l w
    set t : ↥W := σ' (Φ w) with ht
    set u' : ↥W := t⁻¹ * w with hu'
    have hΦu : Φ u' = 1 := by
      rw [hu', map_mul, map_inv, ht, hσ's, inv_mul_cancel]
    have hu'U : (u' : V) ∈ U := by
      have := (QuotientGroup.eq_one_iff u').1 hΦu
      exact this
    have hlu : actW l u' = u' := Subtype.ext ((hu'U.2) l l.2)
    have hw : w = t * u' := by rw [hu']; group
    have h1 : actW l w = σ' (actS l (Φ w)) * u' := by
      conv_lhs => rw [hw]
      rw [map_mul, hlu, ← hσ'e l (Φ w)]
    refine ⟨actS l (Φ w) * (Φ w)⁻¹, ?_⟩
    calc σ' (actS l (Φ w) * (Φ w)⁻¹) = σ' (actS l (Φ w)) * t⁻¹ := by rw [map_mul, map_inv]
      _ = (σ' (actS l (Φ w)) * u') * (u'⁻¹ * t⁻¹) := by group
      _ = actW l w * w⁻¹ := by rw [h1, ← mul_inv_rev, ← hw]
  have hWsub : ∀ w : ↥W, w ∈ σ'.range := by
    intro w
    have hw : (w : V) ∈ commSub W L := by rw [hcomm]; exact w.2
    have hle : commSub W L ≤ σ'.range.map W.subtype := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, v, hv, rfl⟩
      exact ⟨actW ⟨x, hx⟩ ⟨v, hv⟩ * ⟨v, hv⟩⁻¹, hcommK ⟨x, hx⟩ ⟨v, hv⟩, rfl⟩
    obtain ⟨y, hy, hyw⟩ := hle hw
    have : y = w := Subtype.ext hyw
    rw [← this]
    exact hy
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  obtain ⟨s, hs⟩ := hWsub ⟨u, hu.1⟩
  have hΦu : Φ ⟨u, hu.1⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu)
  have hs1 : s = 1 := by rw [← hσ's s, hs, hΦu]
  rw [hs1, map_one] at hs
  exact (congrArg Subtype.val hs).symm

end Main

end B69

end CFSG.Quasithin
