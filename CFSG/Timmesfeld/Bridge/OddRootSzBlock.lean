module

public import CFSG.Timmesfeld.Bridge.OddRootDefs
public import CFSG.Timmesfeld.Bridge.OddLocalBlock
import CFSG.Timmesfeld.Bridge.OddLocalMain
import CFSG.Timmesfeld.Bridge.OddRootBasic
import CFSG.Timmesfeld.Bridge.OddRootSqOut

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal CFSG.BenderSuzuki
open scoped Pointwise

variable {G : Type} [Group G] {D : Set G}

private theorem reach_of_not_disconnected (h : ¬ Connectivity.Disconnected D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) : Reach D a b := by
  by_contra hab
  exact h ⟨a, ha, b, hb, hab⟩

theorem rootSet_subset_F [Finite G] (h : Hyp G D) {c : G} (hc : c ∈ D) {E : Set G}
    (hE : IsMaxOrbit D c E) {f : G} (hf : f ∈ normSet D E \ E) :
    rootSet D f ⊆ normSet D E \ E := by
  intro e he
  have hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b :=
    fun a ha b hb => reach_of_not_disconnected h.conn ha hb
  have heD : e ∈ D := rootSet_subset D f he
  have hcent : ∀ x ∈ E, Commute e x := fun x hx =>
    (he.2 x (subset_commSet h.setup.normal hE hx).1).mpr
      (commute_of_mem_F h.setup hE hf hx)
  refine ⟨⟨heD, mem_normalizer_of_commute hcent⟩, ?_⟩
  intro heE
  obtain ⟨x, hxE, hxne⟩ := exists_not_commute h.setup hc hE hconn heE
  exact hxne (hcent x hxE)

theorem conjSet_subset_of_inter [Finite G] (h : Hyp G D) {c : G} (hc : c ∈ D) {E : Set G}
    (hE : IsMaxOrbit D c E) {g : G}
    (hinter : (OddLocal.conjSet g (normSet D E \ E) ∩ E).Nonempty) :
    OddLocal.conjSet g (normSet D E \ E) ⊆ E := by
  classical
  let F : Set G := normSet D E \ E
  have hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b :=
    fun a ha b hb => reach_of_not_disconnected h.conn ha hb
  have hblock : IsMaxBlock D F := isMaxBlock_normSet_diff h.setup hconn hc hE
  have hFblock : MulAction.IsBlock (ConjAct G) F := hblock.2.2.2.1
  have hFD : F ⊆ D := fun x hx => hx.1.1
  have hsmul : ConjAct.toConjAct g • F = OddLocal.conjSet g F := by
    ext y
    simp only [OddLocal.conjSet, Set.mem_image, Set.mem_smul_set, ConjAct.toConjAct_smul]
  have hblock' : MulAction.IsBlock (ConjAct G) (OddLocal.conjSet g F) := by
    rw [← hsmul]
    exact hFblock.translate (ConjAct.toConjAct g)
  have hdisj : ∀ y ∈ OddLocal.conjSet g F, y ∉ F := by
    intro y hyConj hyF
    have hne : (ConjAct.toConjAct (1 : G) • F ∩ ConjAct.toConjAct g • F).Nonempty :=
      ⟨y, by simpa using hyF, by simpa [hsmul] using hyConj⟩
    have heq : ConjAct.toConjAct (1 : G) • F = ConjAct.toConjAct g • F :=
      hFblock.smul_eq_smul_of_nonempty hne
    have hFeq : F = OddLocal.conjSet g F := by
      rw [← hsmul]
      simpa using heq
    obtain ⟨a, haConj, haE⟩ := hinter
    exact (hFeq.symm ▸ haConj).2 haE
  have hconjD : OddLocal.conjSet g F ⊆ D := by
    rintro y ⟨f, hf, rfl⟩
    exact h.setup.normal g f (hFD hf)
  have hcF : c ∈ F := self_mem_F h.setup.normal hc hE
  have hcN : c ∈ Subgroup.normalizer (OddLocal.conjSet g F) := by
    obtain ⟨a, haConj, haE⟩ := hinter
    exact mem_normalizer_of_commute_of_isBlock hblock' haConj
      (commute_of_mem_F h.setup hE hcF haE)
  have hcNot : c ∉ OddLocal.conjSet g F := fun hc' => hdisj c hc' hcF
  intro y hy
  have hcomm : Commute c y :=
    commute_of_mem_normalizer_of_not_mem h.setup.oddT hblock' hconjD hc hcN hcNot hy
  have hyD : y ∈ D := hconjD hy
  have hynorm : y ∈ normSet D E := mem_normSet_of_commute h.setup.normal hE hyD hcomm.symm
  by_contra hyE
  exact hdisj y hy ⟨hynorm, hyE⟩

private theorem rootSet_subset_E_of_mem_E [Finite G] (h : Hyp G D) {c : G} (hc : c ∈ D)
    {E : Set G} (hE : IsMaxOrbit D c E) {d x : G} (hd : d ∈ E) (hx : x ∈ E)
    (hdx : ¬ Commute d x) : rootSet D d ⊆ E ∧ rootSet D x ⊆ E := by
  have key : ∀ y ∈ D, Commute y c → y ∈ E ∨ y ∈ normSet D E \ E := by
    intro y hyD hyc
    by_cases hyE : y ∈ E
    · exact Or.inl hyE
    · exact Or.inr ⟨mem_normSet_of_commute h.setup.normal hE hyD hyc, hyE⟩
  have hdc : Commute d c := (subset_commSet h.setup.normal hE hd).2.1
  have hxc : Commute x c := (subset_commSet h.setup.normal hE hx).2.1
  have hdD : d ∈ D := (subset_commSet h.setup.normal hE hd).1
  have hxD : x ∈ D := (subset_commSet h.setup.normal hE hx).1
  constructor
  · intro y hy
    have hyD : y ∈ D := rootSet_subset D d hy
    have hyc : Commute y c := (hy.2 c hc).mpr hdc
    rcases key y hyD hyc with hyE | hyF
    · exact hyE
    · exact absurd ((hy.2 x hxD).mp (commute_of_mem_F h.setup hE hyF hx)) hdx
  · intro y hy
    have hyD : y ∈ D := rootSet_subset D x hy
    have hyc : Commute y c := (hy.2 c hc).mpr hxc
    rcases key y hyD hyc with hyE | hyF
    · exact hyE
    · exact absurd ((hy.2 d hdD).mp (commute_of_mem_F h.setup hE hyF hd)).symm hdx

private theorem exists_good_pair_of_mem_F [Finite G] (h : Hyp G D) {c : G} (hc : c ∈ D)
    {E : Set G} (hE : IsMaxOrbit D c E) {d x : G} (hd : d ∈ normSet D E \ E)
    (hx : x ∈ normSet D E \ E) (hdx : ¬ Commute d x) (hsq : SqOut ↥(rootGen D d x)) :
    ∃ e ∈ E, ∃ f ∈ E, ¬ Commute e f ∧ rootSet D e ⊆ E ∧ rootSet D f ⊆ E ∧
      SqOut ↥(rootGen D e f) := by
  obtain ⟨e₀, he₀E⟩ := OddLocal.nonempty hE
  have he₀D : e₀ ∈ D := (subset_commSet h.setup.normal hE he₀E).1
  obtain ⟨g, hg⟩ := isConj_iff.mp (h.setup.isConj hc he₀D)
  have hcF : c ∈ normSet D E \ E := self_mem_F h.setup.normal hc hE
  have hinter : (OddLocal.conjSet g (normSet D E \ E) ∩ E).Nonempty := by
    refine ⟨g * c * g⁻¹, conj_mem_conjSet hcF, ?_⟩
    rwa [hg]
  have hsub : OddLocal.conjSet g (normSet D E \ E) ⊆ E :=
    conjSet_subset_of_inter h hc hE hinter
  have heE : g * d * g⁻¹ ∈ E := hsub (conj_mem_conjSet hd)
  have hfE : g * x * g⁻¹ ∈ E := hsub (conj_mem_conjSet hx)
  have hne : ¬ Commute (g * d * g⁻¹) (g * x * g⁻¹) := fun hconj =>
    hdx ((Commute.conj_iff g).mp hconj)
  have hroot_d : rootSet D (g * d * g⁻¹) ⊆ E := by
    rw [rootSet_conj h.setup.isClass g d]
    rintro y ⟨z, hz, rfl⟩
    exact hsub (conj_mem_conjSet (rootSet_subset_F h hc hE hd hz))
  have hroot_x : rootSet D (g * x * g⁻¹) ⊆ E := by
    rw [rootSet_conj h.setup.isClass g x]
    rintro y ⟨z, hz, rfl⟩
    exact hsub (conj_mem_conjSet (rootSet_subset_F h hc hE hx hz))
  have hsq' : SqOut ↥(rootGen D (g * d * g⁻¹) (g * x * g⁻¹)) := by
    have hmap := map_rootGen_conj h.setup.normal g d x
    let f : G →* G := (MulAut.conj g).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj g).injective
    let e₁ : ↥(rootGen D d x) ≃* ↥((rootGen D d x).map f) :=
      Subgroup.equivMapOfInjective _ f hf
    let e₂ : ↥((rootGen D d x).map f) ≃*
        ↥(rootGen D (g * d * g⁻¹) (g * x * g⁻¹)) :=
      MulEquiv.subgroupCongr hmap
    exact SqOut.of_mulEquiv (e₁.trans e₂) hsq
  exact ⟨g * d * g⁻¹, heE, g * x * g⁻¹, hfE, hne, hroot_d, hroot_x, hsq'⟩

theorem exists_good_pair [Finite G] (h : Hyp G D)
    (hpair : ∃ d₀ ∈ D, ∃ x₀ ∈ D, ¬ Commute d₀ x₀ ∧ SqOut ↥(rootGen D d₀ x₀)) :
    ∃ c ∈ D, ∃ E, IsMaxOrbit D c E ∧ ∃ e ∈ E, ∃ f ∈ E, ¬ Commute e f ∧
      rootSet D e ⊆ E ∧ rootSet D f ⊆ E ∧ SqOut ↥(rootGen D e f) := by
  classical
  obtain ⟨d₀, hd₀, x₀, hx₀, hne, hsq⟩ := hpair
  have hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b :=
    fun a ha b hb => reach_of_not_disconnected h.conn ha hb
  obtain ⟨c, hcD, hcd, hcx⟩ :=
    commonNeighbour G D h.setup hconn h.sq d₀ hd₀ x₀ hx₀ hne
  have hd₀c : d₀ ≠ c := fun hdc => hne (hdc ▸ hcx)
  obtain ⟨E, hE⟩ := exists_isMaxOrbit (⟨d₀, hd₀, hcd.symm, hd₀c⟩ : (commSet D c).Nonempty)
  have hd₀_norm : d₀ ∈ normSet D E := mem_normSet_of_commute h.setup.normal hE hd₀ hcd.symm
  have hx₀_norm : x₀ ∈ normSet D E := mem_normSet_of_commute h.setup.normal hE hx₀ hcx.symm
  have hd₀_or : d₀ ∈ E ∨ d₀ ∈ normSet D E \ E := by
    by_cases h : d₀ ∈ E
    · exact Or.inl h
    · exact Or.inr ⟨hd₀_norm, h⟩
  have hx₀_or : x₀ ∈ E ∨ x₀ ∈ normSet D E \ E := by
    by_cases h : x₀ ∈ E
    · exact Or.inl h
    · exact Or.inr ⟨hx₀_norm, h⟩
  rcases hd₀_or with hd₀E | hd₀F
  · rcases hx₀_or with hx₀E | hx₀F
    · have hroot := rootSet_subset_E_of_mem_E h hcD hE hd₀E hx₀E hne
      exact ⟨c, hcD, E, hE, d₀, hd₀E, x₀, hx₀E, hne, hroot.1, hroot.2, hsq⟩
    · exact absurd ((commute_of_mem_F h.setup hE hx₀F hd₀E).symm) hne
  · rcases hx₀_or with hx₀E | hx₀F
    · exact absurd (commute_of_mem_F h.setup hE hd₀F hx₀E) hne
    · obtain ⟨e, heE, f, hfE, hne', hroot_e, hroot_f, hsq'⟩ :=
        exists_good_pair_of_mem_F h hcD hE hd₀F hx₀F hne hsq
      exact ⟨c, hcD, E, hE, e, heE, f, hfE, hne', hroot_e, hroot_f, hsq'⟩

end CFSG.Timmesfeld.Bridge.OddRoot
