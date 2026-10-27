module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G]

theorem ggTorusWeylReflGen_ggGamma {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hR : GGReflGenerated p (ggAutomizer X Bs)) :
    GGTorusWeylReflGen p (ggGamma X hBsN).range := by
  set A := (ggGamma X hBsN).range with hA
  set W := Subgroup.closure {φ | φ ∈ ggTorusWeylAut p A ∧ GGIsReflection p φ} with hW
  have huniq : ∀ (c : MulAut ↥Bs) (a a' : MulAut ↥A), GGOverGamma hBsN c a →
      GGOverGamma hBsN c a' → a = a' := by
    intro c a a' h h'
    apply MulEquiv.ext
    intro w
    obtain ⟨b, rfl⟩ := (ggGamma X hBsN).rangeRestrict_surjective w
    rw [← h b, ← h' b]
  have key : ∀ c ∈ ggAutomizer X Bs, ∃ a ∈ W, GGOverGamma hBsN c a := by
    intro c hc
    rw [hR] at hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨hcA, hcr⟩ := hc
      obtain ⟨g, hgX, hg, hcg⟩ := mem_ggAutomizer_iff.mp hcA
      have hceq : c = ggConjAut Bs hg := MulEquiv.ext fun b => Subtype.ext (hcg b)
      have hn := conj_mem_normalizer_range_ggGamma hBsN hgX hg
      have hov : GGOverGamma hBsN c (ggConjAut A hn) := by
        rw [hceq]
        exact ggOverGamma_conjAut hgX hg
      rcases isReflection_or_eq_one_of_overGamma hp hp2 hBs hBsN hov hcr with hr | h1
      · exact ⟨_, Subgroup.subset_closure
          ⟨⟨⟨g, hgX⟩, hn, ggTorusWeylElt_of_mem_normalizer hBs hBsN hgX hg, rfl⟩, hr⟩, hov⟩
      · exact ⟨1, W.one_mem, h1 ▸ hov⟩
    | one => exact ⟨1, W.one_mem, GGOverGamma.one⟩
    | mul c d _ _ ihc ihd =>
      obtain ⟨a, ha, hca⟩ := ihc
      obtain ⟨b, hb, hdb⟩ := ihd
      exact ⟨a * b, W.mul_mem ha hb, hca.mul hdb⟩
    | inv c _ ihc =>
      obtain ⟨a, ha, hca⟩ := ihc
      exact ⟨a⁻¹, W.inv_mem ha, hca.inv⟩
  rintro φ ⟨n, hn, hnW, rfl⟩
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_ggTorusWeylElt hBsN hSC hnW
  obtain ⟨a, ha, hca⟩ := key _ (ggConjAut_mem_ggAutomizer n.2 hnN)
  have hov := ggOverGamma_conjAut (hN := hBsN) n.2 hnN
  have heq : ggConjAut A (conj_mem_normalizer_range_ggGamma hBsN n.2 hnN) = ggConjAut A hn := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rfl
  rw [heq] at hov
  rw [huniq _ _ _ hov hca]
  exact ha

theorem ggRootCompGenAvoiding_of_rootGenAvoid {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {z : G} (hzBs : z ∈ Bs)
    (hXz : IsSubnormal X (Subgroup.centralizer ({z} : Set G)))
    (hgen : GGTorusRootGenAvoid p (ggGamma X hBsN).range) : GGRootCompGenAvoiding p Bs X := by
  classical
  have := Fact.mk hp
  intro ρ
  set A := (ggGamma X hBsN).range with hA
  have huniq : ∀ a a' : MulAut ↥A, GGOverGamma hBsN ρ a → GGOverGamma hBsN ρ a' → a = a' := by
    intro a a' h h'
    ext w
    obtain ⟨b, rfl⟩ := (ggGamma X hBsN).rangeRestrict_surjective w
    rw [← h b, ← h' b]
  let ρbar : MulAut ↥A := if h : ∃ a, GGOverGamma hBsN ρ a then h.choose else 1
  have hρbar : ∀ a, GGOverGamma hBsN ρ a → a = ρbar := by
    intro a ha
    have hex : ∃ a, GGOverGamma hBsN ρ a := ⟨a, ha⟩
    simp only [ρbar, dite_eq_left hex]
    exact huniq _ _ ha hex.choose_spec
  apply le_antisymm
  · have hX : X = (⊤ : Subgroup ↥X).map X.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (le_of_eq hX).trans ?_
    rw [Subgroup.map_le_iff_le_comap, ← hgen ρbar]
    refine iSup_le fun n => iSup_le fun hn => iSup_le fun J => iSup_le fun hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨hW, hrefl, hne, hnJ, hcomp, hpJ⟩ := hJ
    obtain ⟨m, hg, htr, hover⟩ :=
      exists_pow_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hBsN hW hn hrefl
    have hgX : (n : G) ^ m ∈ X := X.pow_mem n.2 m
    set t := ggConjAut Bs hg with ht
    have hzt : z ∈ ggFixG Bs t := by
      refine ⟨⟨z, hzBs⟩, ?_, rfl⟩
      apply Subtype.ext
      change (n : G) ^ m * z * ((n : G) ^ m)⁻¹ = z
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hXz.le hgX)
      rw [hc, mul_inv_cancel_right]
    have hCz : Subgroup.centralizer (ggFixG Bs t : Set G) ≤
        Subgroup.centralizer ({z} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzt)
    have hsub : IsSubnormal (X ⊓ Subgroup.centralizer (ggFixG Bs t : Set G))
        (Subgroup.centralizer (ggFixG Bs t : Set G)) := by
      have h := hXz.inf (Subgroup.centralizer (ggFixG Bs t : Set G))
      rwa [inf_eq_right.mpr hCz] at h
    have hmap := map_ggHypCent_eq hp hp2 hBs hBsN hn hgX hg htr.1 hover
    have hJc : IsComponentOf (J.map X.subtype) (X ⊓ Subgroup.centralizer (ggFixG Bs t : Set G)) :=
      hmap ▸ isComponentOf_map_of_injective X.subtype X.subtype_injective hcomp
    have hJC : IsComponentOf (J.map X.subtype) (Subgroup.centralizer (ggFixG Bs t : Set G)) :=
      ⟨hJc.1.trans inf_le_right, hJc.2.1.trans hsub, hJc.2.2⟩
    have hpJ' : p ∣ Nat.card (J.map X.subtype) := by
      rwa [Subgroup.card_map_of_injective X.subtype_injective]
    refine le_iSup_of_le t (le_iSup_of_le (J.map X.subtype)
      (le_iSup_of_le ⟨?_, htr, ?_, Subgroup.map_subtype_le J, hJC.1,
        isPComponent_subgroupOf_of_isComponentOf_of_dvd hJC hpJ'⟩ le_rfl))
    · intro hρ
      apply hne
      exact hρbar _ (hρ ▸ hover)
    · exact ⟨(n : G) ^ m, ⟨n ^ m, J.pow_mem hnJ m, by simp⟩, hg, fun b => rfl⟩
  · exact iSup_le fun t => iSup_le fun Jt => iSup_le fun h => h.2.2.2.1

theorem ggRootCompGenAvoiding_of_marking {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {z : G}
    (hzBs : z ∈ Bs) (hXz : IsSubnormal X (Subgroup.centralizer ({z} : Set G)))
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range)
    (hWR : GGReflGenerated p (ggAutomizer X Bs)) (hT : GGTorusRootGen p r R I) :
    GGRootCompGenAvoiding p Bs X := by
  set γ := ggGamma X hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, hBsI b b.2, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  exact ggRootCompGenAvoiding_of_rootGenAvoid hp hp2 hBs hSC hBsN hzBs hXz
    (hT X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX γ.range hA hAI hr
      h3 (ggTorusSelfCent_ggGamma hBsN hSC) (ggTorusWeylReflGen_ggGamma hp hp2 hBs hSC hBsN hWR))

end CFSG.StandardType

end
