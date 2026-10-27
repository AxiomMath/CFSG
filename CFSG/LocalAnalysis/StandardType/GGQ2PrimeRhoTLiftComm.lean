module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInnerRad
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate3600

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer

theorem rhoT_lift_commute
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m : Fin 7} (h : CoordCtx B Bs x L A κ m) {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ)
    {K : Subgroup G} (hKB : K ≤ Bs)
    (hKm : ∀ (b : G) (hb : b ∈ Bs), κ m ⟨b, hb⟩ = 1 → b ∈ K)
    (hKT : ∀ (b : G) (hb : b ∈ K), ρ ⟨b, h.setting.Bs_norm (hKB hb)⟩ ∈ T46)
    {a a' : SU0} {b b' : G} (hb : b ∈ K) (hb' : b' ∈ K)
    (ha : piSU a = ρ ⟨b, h.setting.Bs_norm (hKB hb)⟩)
    (ha' : piSU a' = ρ ⟨b', h.setting.Bs_norm (hKB hb')⟩) :
    a * a' = a' * a := by
  classical
  obtain ⟨-, -, -, hLc, -, -, -, -⟩ := ggThmIHyp_unpack h.setting.hyp
  obtain ⟨-, hBab, -, -⟩ := h.setting.bstar
  have hBN : Bs ≤ normalizer (L : Set G) := h.setting.Bs_norm
  have hW : WeylCoords Bs A x κ m := h.coords
  have : IsMulCommutative Bs := hBab.1
  have hB3 : ∀ c : Bs, c ^ 3 = 1 := fun c => Subtype.ext (by simpa using hBab.2 c c.2)
  obtain ⟨Ê, hÊ⟩ := exists_permEquiv_of_ggWeylOfType_A h.weyl5
  have hALcard : Nat.card (ggAutomizer L Bs) = 720 := by
    rw [← Nat.card_congr Ê.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hfixx : ∀ φ ∈ ggAutomizer L Bs, φ ⟨x, hW.x_mem⟩ = ⟨x, hW.x_mem⟩ := fun φ hφ =>
    ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hW.x_mem⟩) hLc.1 hφ
  set R : Bs →* Equiv.Perm (Fin 693) := ρ.comp (inclusion hBN) with hR
  set K' : Subgroup Bs := K.subgroupOf Bs with hK'
  have hcen : ∀ z : SU0, piSU z = 1 → z ∈ center SU0 := fun z hz => by
    rw [← ker_piSU]
    exact hz
  have hcube : ∀ (c : SU0) (d : Bs), piSU c = R d → c ^ 3 = 1 := fun c d hcd =>
    rhoTInner_pow_three_of_piSU_pow (by rw [hcd, ← map_pow, hB3 d, map_one])
  have hlift : ∀ d ∈ K', ∃ c : SU0, piSU c = R d := fun d hd => by
    have hT := hKT d (Subgroup.mem_subgroupOf.1 hd)
    have hr : R d ∈ piSU.range := by
      rw [range_piSU]
      exact hT
    exact MonoidHom.mem_range.1 hr
  set D : Subgroup Bs := rhoTInnerRad piSU R K' with hD
  have hDn : D.Normal := ⟨fun n hn g => by rwa [mul_comm' g n, mul_inv_cancel_right]⟩
  let E : Equiv.Perm (Fin (5 + 1)) →* MulAut Bs := (ggAutomizer L Bs).subtype.comp Ê.toMonoidHom
  have hsw : ∀ i j : Fin (5 + 1), i ≠ j → GGIsReflection 3 (E (Equiv.swap i j)) := fun i j hij =>
    ggIsReflection_swap_of_swap E (Fin.castSucc_lt_succ (i := (0 : Fin 5))).ne (hÊ 0) hij
  have hE : ∀ i j : Fin (5 + 1), i ≠ j → ∀ c : Bs, E (Equiv.swap i j) c * c⁻¹ ∈ D := by
    intro i j hij c
    have hrefl := hsw i j hij
    set φ : MulAut Bs := E (Equiv.swap i j) with hφ
    have hφA : φ ∈ ggAutomizer L Bs := (Ê (Equiv.swap i j)).2
    obtain ⟨q, hq, hqc⟩ := rhoTInner_exists_conj_of_mem_automizer hBN hρ hφA
    obtain ⟨s, hsq⟩ : ∃ s : SU0, piSU s = q := by
      have hr : q ∈ piSU.range := by
        rw [range_piSU]
        exact hq
      exact MonoidHom.mem_range.1 hr
    have hs : ∀ (c : SU0) (d : Bs), piSU c = R d → piSU (s * c * s⁻¹) = R (φ d) :=
      fun c d hcd => by
        rw [map_mul, map_mul, map_inv, hsq, hcd]
        exact hqc d
    have hφ2 : ∀ d, φ (φ d) = d := fun d => by
      have h2 := congrArg (fun ψ : MulAut Bs => ψ d) hrefl.1
      simpa [pow_two] using h2
    have hdK : ∀ d : Bs, φ d * d⁻¹ ∈ K' := fun d => by
      have hκ : κ m (φ d * d⁻¹) = 1 := by
        rw [map_mul, map_inv, rhoTInner_kappa_apply hW (h.AL_le hφA) (hfixx φ hφA) d,
          mul_inv_cancel]
      exact hKm _ (φ d * d⁻¹).2 hκ
    exact rhoTInner_reflection_mem_rad piSU hcen R hB3 hcube K' hlift hφ2 hrefl.2 hs hdK c
  have hall : ∀ φ ∈ ggAutomizer L Bs, ∀ c : Bs, φ c * c⁻¹ ∈ D := fun φ hφ c => by
    have h1 := rhoTInner_mem_of_swaps D E hE (Ê.symm ⟨φ, hφ⟩) c
    have h2 : E (Ê.symm ⟨φ, hφ⟩) = φ := by
      change ((Ê (Ê.symm ⟨φ, hφ⟩) : ↥(ggAutomizer L Bs)) : MulAut Bs) = φ
      rw [MulEquiv.apply_symm_apply]
    rwa [h2] at h1
  have hχ : ∀ c : Bs, κ m c = 1 → c ∈ D := by
    by_cases hDtop : D = ⊤
    · intro c _
      rw [hDtop]
      exact mem_top c
    · obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Bs, c₀ ∉ D := by
        by_contra hcon
        exact hDtop (eq_top_iff.2 fun c _ => Classical.byContradiction fun hc => hcon ⟨c, hc⟩)
      have hinv : ∀ φ ∈ ggAutomizer L Bs, ∀ c : Bs,
          QuotientGroup.mk' D (φ c) = QuotientGroup.mk' D c := fun φ hφ c => by
        change (QuotientGroup.mk (φ c) : Bs ⧸ D) = QuotientGroup.mk c
        rw [QuotientGroup.eq]
        have h1 := D.inv_mem (hall φ hφ c)
        rwa [mul_inv_rev, inv_inv, mul_comm' c] at h1
      have hne : ∃ c : Bs, QuotientGroup.mk' D c ≠ 1 :=
        ⟨c₀, fun h1 => hc₀ ((QuotientGroup.eq_one_iff c₀).1 h1)⟩
      have key := ker_eq_of_invariant hW h.AL_le hfixx hALcard (QuotientGroup.mk' D) hinv hne
      exact fun c hc => (QuotientGroup.eq_one_iff c).1 ((key c).2 hc)
  exact rhoTInner_commute_of_rad piSU hcen R K' (κ m) hχ (b := ⟨b, hKB hb⟩)
    (b' := ⟨b', hKB hb'⟩) hb hb' ha ha'

end CFSG.GGQ2Prime
