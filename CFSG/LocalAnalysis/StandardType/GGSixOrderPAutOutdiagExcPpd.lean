module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def IsTwoPowPpd (f e r : ℕ) : Prop :=
  r.Prime ∧ orderOf (2 : ZMod r) = e * f

@[expose] def ggOutdiagExpsE6 : List ℕ := [9, 12]

@[expose] def ggOutdiagExpsTwE6 : List ℕ := [12, 18]

section Embeds

variable {G : Type} [Group G]

theorem GGCentralizerEmbeds.false_of_ppd {M : Subgroup G} {y b : G}
    (h : GGCentralizerEmbeds M y b) {r : ℕ}
    (hz : ∃ z ∈ M ⊓ Subgroup.centralizer {y}, orderOf z = r)
    (hno : ∀ z' ∈ M ⊓ Subgroup.centralizer {b}, orderOf z' ≠ r) : False := by
  obtain ⟨θ, hinj, hθ, -⟩ := h
  obtain ⟨z, hz, hzr⟩ := hz
  refine hno (θ ⟨z, hz⟩) (hθ ⟨z, hz⟩) ?_
  rw [orderOf_injective θ hinj ⟨z, hz⟩, Subgroup.orderOf_mk, hzr]

theorem GGCentralizerEmbeds.ne_one {M : Subgroup G} {y b : G} (h : GGCentralizerEmbeds M y b)
    (hyM : y ∈ M) (hy : y ≠ 1) : b ≠ 1 := by
  obtain ⟨θ, hinj, -, hθy⟩ := h
  have hyc : y ∈ M ⊓ Subgroup.centralizer {y} :=
    ⟨hyM, Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Set.mem_singleton_iff.mp hg]⟩
  intro hb
  rw [← hθy hyc] at hb
  have : (⟨y, hyc⟩ : ↥(M ⊓ Subgroup.centralizer {y})) = 1 :=
    hinj (hb.trans (map_one θ).symm)
  exact hy (congrArg Subtype.val this)

end Embeds

section Inputs

@[expose] def GGOutdiagTwistedPpdAt (t : StatedLieTag) (es : List ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → GGOutdiagPrimeConfig p t n f →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      (∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
      ∃ r, (∃ e ∈ es, IsTwoPowPpd f e r) ∧
        ∃ z ∈ Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {y}, orderOf z = r

@[expose] def GGOutdiagToralNoPpdAt (t : StatedLieTag) (es : List ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → GGOutdiagPrimeConfig p t n f →
    ∀ b ∈ Bs, b ≠ 1 → ∀ r, (∃ e ∈ es, IsTwoPowPpd f e r) →
      ∀ z ∈ Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {b}, orderOf z ≠ r

theorem ggOrdPOutdiagAt_of_ppd {t : StatedLieTag} {es : List ℕ}
    (hI : GGOutdiagTwistedPpdAt t es) (hII : GGOutdiagToralNoPpdAt t es) : GGOrdPOutdiagAt t := by
  intro G _ _ p Bs G₀ n f ψ hS h4 hcfg b hb y hyN hyo hyi hnc hemb
  obtain ⟨r, hr, z, hz, hzr⟩ := hI G p Bs G₀ n f ψ hS h4 hcfg y hyN hyo hyi hnc
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyo
    exact hS.prime.one_lt.ne hyo
  exact (hemb.false_of_ppd ⟨z, hz, hzr⟩
    (hII G p Bs G₀ n f ψ hS h4 hcfg b hb (hemb.ne_one hyN hy1) r hr)).elim

theorem ggOrdPOutdiagAt_E6_of_ppd (hI : GGOutdiagTwistedPpdAt .E6 ggOutdiagExpsE6)
    (hII : GGOutdiagToralNoPpdAt .E6 ggOutdiagExpsE6) : GGOrdPOutdiagAt .E6 :=
  ggOrdPOutdiagAt_of_ppd hI hII

theorem ggOrdPOutdiagAt_twistedE6_of_ppd (hI : GGOutdiagTwistedPpdAt .twistedE6 ggOutdiagExpsTwE6)
    (hII : GGOutdiagToralNoPpdAt .twistedE6 ggOutdiagExpsTwE6) :
    GGOrdPOutdiagAt .twistedE6 :=
  ggOrdPOutdiagAt_of_ppd hI hII

end Inputs

end CFSG.StandardType
