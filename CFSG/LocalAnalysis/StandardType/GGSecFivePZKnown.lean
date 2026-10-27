module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrderSixPZ
import CFSG.LocalAnalysis.StandardType.GGInnerDiagPowers
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneSix
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwRankOne
import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Component

theorem map_subgroupOf_eq_of_isComponentOf_fix {G S : Type*} [Group G] [Group S]
    {G₀ L : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (G₀ : Set G))
    (π : ↥G₀ →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥G₀)
    (α : MulAut S) (hα : ∀ g h : ↥G₀, (h : G) = x * g * x⁻¹ → π h = α (π g))
    (hL : IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) {T₀ : Subgroup S}
    (hT₀α : ∀ t ∈ T₀, α t = t) (hT₀ : IsSimpleGroup ↥T₀) (hT₀p : ⁅T₀, T₀⁆ = T₀)
    (hperf : ∀ P : Subgroup S, (∀ c ∈ P, α c = c) → ⁅P, P⁆ = P → P ≤ T₀) :
    (L.subgroupOf G₀).map π = T₀ := by
  classical
  have hLG : L ≤ G₀ := hL.1.trans inf_le_left
  have hLx : ∀ l ∈ L, x * l * x⁻¹ = l := fun l hl => by
    have h := Subgroup.mem_centralizer_iff.1
      ((inf_le_right : G₀ ⊓ Subgroup.centralizer {x} ≤ _) (hL.1 hl)) x rfl
    rw [h, mul_inv_cancel_right]
  set H₀ := (G₀ ⊓ Subgroup.centralizer {x}).subgroupOf G₀ with hH₀
  set L₀ := L.subgroupOf G₀ with hL₀
  have hLperf : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator, hL.2.2.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hL₀perf : ⁅L₀, L₀⁆ = L₀ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_commutator, hL₀, Subgroup.map_subgroupOf_eq_of_le hLG, hLperf]
  have hP : L₀.map π ≤ T₀ := by
    refine hperf _ ?_ (by rw [← Subgroup.map_commutator, hL₀perf])
    rintro _ ⟨l, hl, rfl⟩
    exact (hα l l (hLx l (Subgroup.mem_subgroupOf.1 hl)).symm).symm
  have : Group.IsPerfect ↥T₀ := Subgroup.isPerfect_iff.mpr hT₀p
  obtain ⟨-, hmap, hfix⟩ := CFSG.LocalAnalysis.ComponentInitial.fixedPerfectLift
    (a := G₀.normalizerMonoidHom ⟨x, hxN⟩) hπ hker (fun g => hα g _ rfl) T₀ hT₀α
  have hT₀H : T₀ ≤ H₀.map π := by
    rw [← hmap]
    refine Subgroup.map_mono fun g hg => ?_
    have h1 : x * (g : G) * x⁻¹ = g := congrArg Subtype.val (hfix g hg)
    rw [hH₀, Subgroup.mem_subgroupOf]
    refine ⟨g.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.1 hy]
    calc x * (g : G) = x * g * x⁻¹ * x := by group
      _ = g * x := by rw [h1]
  have hsub : IsSubnormal (L₀.map π) (H₀.map π) := (hL.2.1.comap G₀.subtype).map π
  have hsub' : IsSubnormal (L₀.map π) T₀ := by
    have h := hsub.inf_of_le hT₀H
    rwa [inf_eq_left.2 hP] at h
  rcases hsub'.eq_bot_or_eq_of_isSimpleGroup hT₀ with h | h
  · exfalso
    have hcen : ∀ l ∈ L, ∀ l' ∈ G₀, l * l' = l' * l := fun l hl l' hl' => by
      have h0 : (⟨l, hLG hl⟩ : ↥G₀) ∈ π.ker :=
        (Subgroup.map_eq_bot_iff _).1 h (Subgroup.mem_subgroupOf.2 hl)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 (hker h0) ⟨l', hl'⟩).symm
    obtain ⟨-, hs⟩ := hL.2.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    refine hab (QuotientGroup.eq.2 (Subgroup.mem_center_iff.2 fun c => Subtype.ext ?_))
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (hcen _ (a⁻¹ * b).2 _ (hLG c.2)).symm
  · exact h

theorem nonempty_mulEquiv_centerQuot_of_map_eq {G S : Type*} [Group G] [Group S]
    {G₀ L : Subgroup G} (π : ↥G₀ →* S) (hker : π.ker ≤ Subgroup.center ↥G₀) (hLG : L ≤ G₀)
    {T₀ : Subgroup S} (hmap : (L.subgroupOf G₀).map π = T₀) (hT₀ : IsSimpleGroup ↥T₀)
    (hT₀p : ⁅T₀, T₀⁆ = T₀) : Nonempty (↥T₀ ≃* ↥L ⧸ Subgroup.center ↥L) := by
  classical
  let ι : ↥L →* ↥G₀ := Subgroup.inclusion hLG
  let ρ : ↥L →* ↥T₀ := (π.comp ι).codRestrict T₀ fun l => by
    rw [← hmap]
    exact ⟨ι l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨t, ht⟩
    rw [← hmap] at ht
    obtain ⟨g, hg, rfl⟩ := ht
    exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, Subtype.ext rfl⟩
  have hZ : ∀ t : ↥T₀, (∀ s : ↥T₀, t * s = s * t) → t = 1 := by
    intro t ht
    have hcen : Subgroup.center ↥T₀ ≠ ⊤ := by
      intro htop
      have h1 : ⁅T₀, T₀⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have := Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top (⟨a, ha⟩ : ↥T₀)) ⟨b, hb⟩
        exact congrArg Subtype.val this
      have h2 : T₀ = ⊥ := hT₀p.symm.trans h1
      have : Nontrivial ↥T₀ := hT₀.toNontrivial
      obtain ⟨u, hu⟩ := exists_ne (1 : ↥T₀)
      exact hu (Subtype.ext (by simpa [h2] using u.2))
    rcases hT₀.eq_bot_or_eq_top_of_normal (Subgroup.center ↥T₀) with h | h
    · exact (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_center_iff.2 fun s => (ht s).symm))
    · exact absurd h hcen
  have hk : ρ.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hl l'
      have h0 : ι l ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hl
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 (hker h0) (ι l'))
      exact Subtype.ext h1
    · intro hl
      refine hZ _ fun s => ?_
      obtain ⟨l', rfl⟩ := hρ s
      rw [← map_mul, ← map_mul, hl l']
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)).symm⟩

end Component

section Rigidity

omit [Finite G] in
theorem eq_psu_of_mulEquiv_centerQuot_pz {G₀ Bs L : Subgroup G} {x : G} {m : ℕ} (hm : 4 ≤ m)
    (hPZ : GGSecFivePZData G₀ Bs L x m) {T : Type} [Group T]
    (e : T ≃* ↥L ⧸ Subgroup.center ↥L) {t : StatedLieTag} {n f₀ : ℕ}
    (hT : LieModel T t n 2 f₀) : t = .PSU ∧ n = m ∧ f₀ = 1 := by
  obtain ⟨lab, -, R, _, I, F, θ, -, -, ⟨⟨htag, hrank, hn⟩, -⟩, hmod⟩ :=
    largeEvenMarking_exists_markedModel hPZ.1
  have hR : LieModel R .PSU m 2 1 := by
    obtain ⟨tag, rank, k⟩ := lab
    simp only at htag hrank hn
    subst htag hrank hn
    have h1 : m - 1 + 1 = m := by omega
    simpa [MarkedModel, markTag, markRank, markChar, markDeg, h1] using hmod
  exact SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq hm hR hT
    (Nat.card_congr (e.trans θ).toEquiv)

omit [Finite G] in
theorem eq_psu_of_isComponentOf_fix_pz {S : Type} [Group S] {G₀ Bs L : Subgroup G} {x : G}
    {m : ℕ} (hm : 4 ≤ m) (hPZ : GGSecFivePZData G₀ Bs L x m)
    (hxN : x ∈ Subgroup.normalizer (G₀ : Set G)) (π : ↥G₀ →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥G₀) (α : MulAut S)
    (hα : ∀ g h : ↥G₀, (h : G) = x * g * x⁻¹ → π h = α (π g))
    (hL : IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) {T₀ : Subgroup S}
    (hT₀α : ∀ t ∈ T₀, α t = t) (hT₀ : IsSimpleGroup ↥T₀) (hT₀p : ⁅T₀, T₀⁆ = T₀)
    (hperf : ∀ P : Subgroup S, (∀ c ∈ P, α c = c) → ⁅P, P⁆ = P → P ≤ T₀)
    {t : StatedLieTag} {n f₀ : ℕ} (hT : LieModel ↥T₀ t n 2 f₀) :
    t = .PSU ∧ n = m ∧ f₀ = 1 := by
  have hmap := map_subgroupOf_eq_of_isComponentOf_fix hxN π hπ hker α hα hL hT₀α hT₀ hT₀p hperf
  obtain ⟨e⟩ := nonempty_mulEquiv_centerQuot_of_map_eq π hker (hL.1.trans inf_le_left) hmap hT₀
    hT₀p
  exact eq_psu_of_mulEquiv_centerQuot_pz hm hPZ e hT

end Rigidity

section Cells

theorem ggInnerDiagOn_of_psiInnerDiag_pz {B Bs L D J : Subgroup G} {x : G} {m : ℕ}
    (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ)
    (hx : GGPsiInnerDiag (ggU t n f).D ψ x) : GGInnerDiagOn Bs (ggG0 3 B x L D J) := by
  have hMk : GGInnerDiagMarkingInput := ggInnerDiagMarkingInput_of_E6 fun t ht => by
    rcases ht with rfl | rfl
    · exact ggInnerDiagMarkingAt_E6
    · exact ggInnerDiagMarkingAt_twistedE6
  obtain ⟨-, -, ⟨hBs, -⟩, hBsN, -⟩ := hPZ
  have hrange : ψ.range = ggG0 3 B x L D J := hpres.2.1.1
  let T : Subgroup G :=
    { carrier := {b | b ∈ Subgroup.normalizer (ψ.range : Set G) ∧
        GGPsiInnerDiag (ggU t n f).D ψ b}
      mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, ha.2.mul hb.2 hb.1⟩
      one_mem' := ⟨one_mem _, ggPsiInnerDiag_one ψ⟩
      inv_mem' := fun ha => ⟨inv_mem ha.1, ha.2.inv ha.1⟩ }
  have hxBs : x ∈ Bs := by
    rw [hBs]
    exact (le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)
  have hBsT : Bs ≤ T := by
    rw [hBs]
    refine sup_le ((Subgroup.zpowers_le (H := T)).2 ⟨by rw [hrange]; exact hBsN hxBs, hx⟩) ?_
    intro e he
    have heR : e ∈ ψ.range := by
      rw [hrange]
      exact le_ggG0_left 3 B x L D J he.2
    exact ⟨Subgroup.le_normalizer heR, ggPsiInnerDiag_of_mem_range _ heR⟩
  exact ggInnerDiagOn_of_presents_mk hMk hpres hBsN fun b hb => (hBsT hb).2

theorem ggSecFivePZKnownGroupInput_of_psiInnerDiag
    (h : ∀ (G : Type) [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G) (m : ℕ),
      5 ≤ m → 3 ∣ m + 1 → GGConfig 3 B Bs x L D J → GGNoTransvection 3 Bs →
        GGSecFivePZData (ggG0 3 B x L D J) Bs L x m →
          ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
            GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ →
              GGPsiInnerDiag (ggU t n f).D ψ x) :
    GGSecFivePZKnownGroupInput := by
  intro G _ _ B Bs L D J x m hm h3 hcfg hNT hPZ t n f ψ hpres
  exact ggInnerDiagOn_of_psiInnerDiag_pz hPZ hpres
    (h G B Bs L D J x m hm h3 hcfg hNT hPZ t n f ψ hpres)

end Cells

end CFSG.StandardType
