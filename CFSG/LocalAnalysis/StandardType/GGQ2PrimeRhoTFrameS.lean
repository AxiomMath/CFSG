module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameCoord
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInner

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer

theorem rhoTFrame_rho_of_mem
    {G : Type} [Group G] {L : Subgroup G} {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {l : G}
    (hl : l ∈ L) :
    ρ ⟨l, L.le_normalizer hl⟩ = (e (QuotientGroup.mk ⟨l, hl⟩) : Equiv.Perm (Fin 693)) := by
  set u := ρ ⟨l, L.le_normalizer hl⟩ with hu
  set v : Equiv.Perm (Fin 693) := (e (QuotientGroup.mk ⟨l, hl⟩) : Equiv.Perm (Fin 693)) with hv
  have hcent : v⁻¹ * u ∈ centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨q, hq⟩ := e.surjective ⟨t, ht⟩
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q
    have ht' : (e (QuotientGroup.mk l') : Equiv.Perm (Fin 693)) = t := congrArg Subtype.val hq
    have hl' : l * (l' : G) * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl l'.2) (L.inv_mem hl)
    have h1 := hρ.conj ⟨l, L.le_normalizer hl⟩ l' hl'
    have h2 : v * (e (QuotientGroup.mk l') : Equiv.Perm (Fin 693)) * v⁻¹ =
        (e (QuotientGroup.mk (⟨l * l' * l⁻¹, hl'⟩ : L)) : Equiv.Perm (Fin 693)) := by
      have e1 : (⟨l * (l' : G) * l⁻¹, hl'⟩ : L) = ⟨l, hl⟩ * l' * ⟨l, hl⟩⁻¹ := Subtype.ext rfl
      rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
        map_inv]
      rfl
    have h3 : u * t * u⁻¹ = v * t * v⁻¹ := by rw [← ht']; exact h1.trans h2.symm
    calc t * (v⁻¹ * u) = v⁻¹ * (v * t * v⁻¹) * u := by group
      _ = v⁻¹ * (u * t * u⁻¹) * u := by rw [h3]
      _ = v⁻¹ * u * t := by group
  have hbot : v⁻¹ * u ∈ (⊥ : Subgroup (Equiv.Perm (Fin 693))) := by
    rw [← CFSG.EvenSmallLie.UnitarySix.YamadaHAut.centralizer_T46]
    exact hcent
  exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 hbot)).symm

private theorem rhoTFrame_mem_zpowers_Bs {G : Type} [Group G] {Bs : Subgroup G} {x : G}
    (hx : x ∈ Bs) {c : Bs} (hc : (c : G) ∈ zpowers x) : c ∈ zpowers (⟨x, hx⟩ : Bs) := by
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact ⟨t, Subtype.ext (by simpa using ht)⟩

theorem rhoTFrame_exists_s
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m n : Fin 7} (h : CoordCtx B Bs x L A κ m) (hn : n ≠ m) {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ)
    {E : Subgroup (GL (Fin 6) F4)}
    (hE : ∀ a : SU0, (a : GL (Fin 6) F4) ∈ E ↔
      ∃ (b : G) (hb : b ∈ Bs), κ m ⟨b, hb⟩ = 1 ∧ piSU a = ρ ⟨b, h.setting.Bs_norm hb⟩)
    {u : G} (hu : u ∈ Bs) (hucoord : ∀ i, κ i ⟨u, hu⟩ = if i = n then 1 else ω3) :
    ∃ s : Equiv.Perm (Fin 7) → SU0,
      (∀ σ : Equiv.Perm (Fin 7), σ m = m → σ n = n →
        (∀ a : SU0, (a : GL (Fin 6) F4) ∈ E →
          ((s σ * a * (s σ)⁻¹ : SU0) : GL (Fin 6) F4) ∈ E) ∧
        piSU (s σ) * ρ ⟨u, h.setting.Bs_norm hu⟩ = ρ ⟨u, h.setting.Bs_norm hu⟩ * piSU (s σ)) ∧
      ∀ σ σ' : Equiv.Perm (Fin 7), σ m = m → σ n = n → σ' m = m → σ' n = n →
        (∀ a : SU0, (a : GL (Fin 6) F4) ∈ E → s σ * a * (s σ)⁻¹ = s σ' * a * (s σ')⁻¹) →
          σ = σ' := by
  classical
  have hex : ∀ σ : Equiv.Perm (Fin 7), ∃ (s : SU0) (l : G), σ m = m →
      ∃ hlL : l ∈ L, l ∈ normalizer (Bs : Set G) ∧ IsCoordLift Bs κ l σ ∧
        piSU s = ρ ⟨l, L.le_normalizer hlL⟩ := by
    intro σ
    by_cases hσ : σ m = m
    · obtain ⟨l, hlL, hlN, hlc⟩ := rhoTFrame_exists_lift h hσ
      have hT : ρ ⟨l, L.le_normalizer hlL⟩ ∈ piSU.range := by
        rw [range_piSU, rhoTFrame_rho_of_mem hρ hlL]
        exact (e _).2
      obtain ⟨s, hs⟩ := hT
      exact ⟨s, l, fun _ => ⟨hlL, hlN, hlc, hs⟩⟩
    · exact ⟨1, 1, fun h' => absurd h' hσ⟩
  choose s l hsl using hex
  refine ⟨s, fun σ hσm hσn => ?_, fun σ σ' hσm hσn hσ'm hσ'n hcomm => ?_⟩
  · obtain ⟨hlL, hlN, hlc, hs⟩ := hsl σ hσm
    refine ⟨fun a ha => ?_, ?_⟩
    · obtain ⟨b, hb, hκ, hpi⟩ := (hE a).1 ha
      have hb' : l σ * b * (l σ)⁻¹ ∈ Bs := (mem_normalizer_iff.1 hlN b).1 hb
      refine (hE _).2 ⟨l σ * b * (l σ)⁻¹, hb', ?_, ?_⟩
      · rw [hlc m ⟨b, hb⟩ hb', (Equiv.symm_apply_eq σ).2 hσm.symm]
        exact hκ
      · rw [map_mul, map_mul, map_inv, hs, hpi, ← map_inv, ← map_mul, ← map_mul]
        rfl
    · have hc := rhoTFrame_lift_comm h.coords hlN hlc hσn hu hucoord
      rw [hs, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 hc)
  · obtain ⟨hlL, hlN, hlc, hs⟩ := hsl σ hσm
    obtain ⟨hlL', hlN', hlc', hs'⟩ := hsl σ' hσ'm
    let ρB : Bs →* Equiv.Perm (Fin 693) := ρ.comp (Subgroup.inclusion h.setting.Bs_norm)
    let φ : Bs → Bs := fun b => ⟨l σ * b * (l σ)⁻¹, (mem_normalizer_iff.1 hlN b).1 b.2⟩
    let φ' : Bs → Bs := fun b => ⟨l σ' * b * (l σ')⁻¹, (mem_normalizer_iff.1 hlN' b).1 b.2⟩
    refine rhoTFrame_perm_unique h.coords hn hσm hσn hσ'm hσ'n (φ := φ) (φ' := φ')
      (fun j b => hlc j b _) (fun j b => hlc' j b _) (fun b hb => ?_)
    have hT : ρB b ∈ piSU.range := by
      rw [range_piSU]
      exact (rhoT_mem_T46_iff h hρ b.2).2 hb
    obtain ⟨a, ha⟩ := hT
    have haE : (a : GL (Fin 6) F4) ∈ E := (hE a).2 ⟨b, b.2, hb, ha⟩
    have h1 := congrArg piSU (hcomm a haE)
    have e1 : ∀ (c : G) (hc : c ∈ L) (hcN : c ∈ normalizer (Bs : Set G)) (b' : Bs),
        ρB ⟨c * (b' : G) * c⁻¹, (mem_normalizer_iff.1 hcN b').1 b'.2⟩ =
          ρ ⟨c, L.le_normalizer hc⟩ * ρB b' * (ρ ⟨c, L.le_normalizer hc⟩)⁻¹ :=
      fun c hc hcN b' => by
        show ρ _ = ρ _ * ρ _ * (ρ _)⁻¹
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
    have h2 : ρB (φ b) = ρB (φ' b) := by
      rw [show ρB (φ b) = _ from e1 _ hlL hlN b, show ρB (φ' b) = _ from e1 _ hlL' hlN' b, ← hs,
        ← hs', ← ha]
      simpa only [map_mul, map_inv] using h1
    have h3 : ρB (φ b * (φ' b)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact rhoTFrame_mem_zpowers_Bs h.coords.x_mem
      ((rhoT_eq_one_iff_mem_zpowers h hρ (φ b * (φ' b)⁻¹).2).1 h3)

end CFSG.GGQ2Prime
