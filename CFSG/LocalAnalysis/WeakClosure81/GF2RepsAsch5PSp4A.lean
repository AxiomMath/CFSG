module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Alm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

@[expose] def AutStab {K : Type} [Group K] (α : MulAut K) (R : Subgroup K) : Prop :=
  ∀ x : K, α x ∈ R ↔ x ∈ R

@[expose] def CanonFor {K : Type} [Group K] (R : Subgroup K) : Prop :=
  ∃ Z₁ Z₂ : Subgroup K, R ≤ Z₁ ∧ R ≤ Z₂ ∧ Z₁ < ⊤ ∧ Z₂ < ⊤ ∧ Z₁ ⊔ Z₂ = ⊤ ∧
    ∀ α : MulAut K, AutStab α R → AutStab α Z₁ ∧ AutStab α Z₂

@[expose] def SylowCanon (K : Type) [Group K] : Prop :=
  ∀ R : Subgroup K, IsSylowIn 2 R ⊤ → CanonFor R

theorem autStab_map_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (α' : MulAut K')
    {Z : Subgroup K} (h : AutStab (e.trans (α'.trans e.symm) : MulAut K) Z) :
    AutStab α' (Z.map e.toMonoidHom) := by
  intro y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simpa using h (e.symm y)

theorem canonFor_of_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {R : Subgroup K} {R' : Subgroup K'} (hR : ∀ x : K, e x ∈ R' ↔ x ∈ R) (h : CanonFor R) :
    CanonFor R' := by
  obtain ⟨Z₁, Z₂, h₁, h₂, hl₁, hl₂, hsup, hcan⟩ := h
  have hle : ∀ {Z : Subgroup K}, R ≤ Z → R' ≤ Z.map e.toMonoidHom := by
    intro Z hZ y hy
    rw [Subgroup.mem_map_equiv]
    apply hZ
    have := hR (e.symm y)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.1 hy
  have hlt : ∀ {Z : Subgroup K}, Z < ⊤ → Z.map e.toMonoidHom < ⊤ := by
    intro Z hZ
    refine lt_top_iff_ne_top.2 fun hmap => (lt_top_iff_ne_top.1 hZ) (eq_top_iff.2 fun x _ => ?_)
    have : e x ∈ Z.map e.toMonoidHom := hmap ▸ Subgroup.mem_top _
    simpa using Subgroup.mem_map_equiv.1 this
  refine ⟨Z₁.map e.toMonoidHom, Z₂.map e.toMonoidHom, hle h₁, hle h₂, hlt hl₁, hlt hl₂, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]
  · intro α' hα'
    have hα : AutStab (e.trans (α'.trans e.symm) : MulAut K) R := by
      intro x
      have h1 := hR ((e.trans (α'.trans e.symm) : MulAut K) x)
      have h2 : e ((e.trans (α'.trans e.symm) : MulAut K) x) = α' (e x) := by simp
      rw [h2] at h1
      rw [← h1, ← hR x]
      exact hα' (e x)
    obtain ⟨hs₁, hs₂⟩ := hcan _ hα
    exact ⟨autStab_map_equiv e α' hs₁, autStab_map_equiv e α' hs₂⟩

theorem isSylowIn_top_comap_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {R' : Subgroup K'} (h : IsSylowIn 2 R' ⊤) : IsSylowIn 2 (R'.comap e.toMonoidHom) ⊤ := by
  refine ⟨le_top, h.isPGroup.comap_of_injective e.toMonoidHom e.injective, ?_⟩
  have h1 := h.not_dvd_relIndex
  have h2 : (R'.comap e.toMonoidHom).index = R'.index :=
    Subgroup.index_comap_of_surjective R' (f := e.toMonoidHom) e.surjective
  rw [Subgroup.relIndex_top_right] at h1
  rw [Subgroup.relIndex_top_right, h2]
  exact h1

theorem isSylowIn_top_subgroupOf_inf {G : Type} [Group G] [Finite G] {S A I : Subgroup G}
    (hS : IsSylowIn 2 S A) (hI : I ≤ A) (hN : (I.subgroupOf A).Normal) :
    IsSylowIn 2 ((S ⊓ I).subgroupOf I) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.inf_normal hI hN
  refine ⟨le_top, h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact h.not_dvd_relIndex

theorem normalizes_map_subtype_of_autStab {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    {Z : Subgroup ↥N} {s : G} (hs : AutStab (MulAut.conjNormal s) Z) :
    s ∈ Subgroup.normalizer ((Z.map N.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨MulAut.conjNormal s z, (hs z).2 hz, MulAut.conjNormal_apply s z⟩
  · rintro ⟨z', hz', hzn⟩
    have hnN : n ∈ N := by
      have h1 : n = s⁻¹ * (z' : G) * s⁻¹⁻¹ := by
        have h2 : (z' : G) = s * n * s⁻¹ := hzn
        rw [h2]
        group
      rw [h1]
      exact Subgroup.Normal.conj_mem ‹N.Normal› _ z'.2 _
    refine ⟨⟨n, hnN⟩, ?_, rfl⟩
    show (⟨n, hnN⟩ : ↥N) ∈ Z
    rw [← hs ⟨n, hnN⟩]
    have h3 : MulAut.conjNormal s ⟨n, hnN⟩ = z' :=
      Subtype.ext ((MulAut.conjNormal_apply s ⟨n, hnN⟩).trans hzn.symm)
    rw [h3]
    exact hz'

theorem inf_sup_normalizing {G : Type} [Group G] {S I : Subgroup G} [I.Normal]
    {Z : Subgroup ↥I} (hRZ : (S ⊓ I).subgroupOf I ≤ Z)
    (hst : ∀ s ∈ S, AutStab (MulAut.conjNormal s) Z) :
    (S ⊔ Z.map I.subtype) ⊓ I = Z.map I.subtype := by
  have hN : S ≤ Subgroup.normalizer ((Z.map I.subtype : Subgroup G) : Set G) :=
    fun s hs => normalizes_map_subtype_of_autStab (hst s hs)
  apply le_antisymm
  · intro g hg
    obtain ⟨hgX, hgI⟩ := hg
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right S (Z.map I.subtype) hN
    have hg' : g ∈ (↑(S ⊔ Z.map I.subtype) : Set G) := hgX
    rw [hmul] at hg'
    obtain ⟨s, hs, n, hn, rfl⟩ := hg'
    have hnI : n ∈ I := Subgroup.map_subtype_le _ hn
    have hsI : s ∈ I := by
      have := I.mul_mem hgI (I.inv_mem hnI)
      simpa using this
    have hsZ : (⟨s, hsI⟩ : ↥I) ∈ Z := hRZ (Subgroup.mem_subgroupOf.2 ⟨hs, hsI⟩)
    exact (Z.map I.subtype).mul_mem ⟨⟨s, hsI⟩, hsZ, rfl⟩ hn
  · exact le_inf le_sup_right (Subgroup.map_subtype_le Z)

theorem exists_overgroups_of_sylowCanon {K : Type} [Group K] [Finite K]
    (hC : SylowCanon ↥(innAutOf K)) {A S : Subgroup (MulAut K)}
    (hA : AlmostSimpleData K A S) :
    ∃ X₁ X₂ : Subgroup (MulAut K), S ≤ X₁ ∧ S ≤ X₂ ∧ X₁ ≤ A ∧ X₂ ≤ A ∧
      ¬ innAutOf K ≤ X₁ ∧ ¬ innAutOf K ≤ X₂ ∧
        (X₁ ⊓ innAutOf K) ⊔ (X₂ ⊓ innAutOf K) = innAutOf K := by
  obtain ⟨hIA, hSA, -⟩ := hA
  haveI : Finite (MulAut K) := MulEquiv.finite_left
  haveI hIn : (innAutOf K).Normal := CFSG.Quasithin.H13.P31Sec.normal_innGroup
  have hSyl := isSylowIn_top_subgroupOf_inf hSA hIA (normal_innAutOf_subgroupOf hIA)
  obtain ⟨Z₁, Z₂, hR₁, hR₂, hl₁, hl₂, hsup, hcan⟩ := hC _ hSyl
  have hst : ∀ s ∈ S, AutStab (MulAut.conjNormal s) ((S ⊓ innAutOf K).subgroupOf (innAutOf K)) := by
    intro s hs x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    simp only [Subgroup.mem_inf]
    refine and_congr ?_ (iff_of_true (hIn.conj_mem _ x.2 s) x.2)
    rw [Subgroup.mul_mem_cancel_right _ (S.inv_mem hs), Subgroup.mul_mem_cancel_left _ hs]
  have key₁ := inf_sup_normalizing hR₁ fun s hs => (hcan _ (hst s hs)).1
  have key₂ := inf_sup_normalizing hR₂ fun s hs => (hcan _ (hst s hs)).2
  have hnot : ∀ Z : Subgroup ↥(innAutOf K), Z < ⊤ →
      (S ⊔ Z.map (innAutOf K).subtype) ⊓ innAutOf K = Z.map (innAutOf K).subtype →
        ¬ innAutOf K ≤ S ⊔ Z.map (innAutOf K).subtype := by
    intro Z hZ key hle
    have h1 : innAutOf K ≤ Z.map (innAutOf K).subtype := by
      rw [← key]
      exact le_inf hle le_rfl
    refine (lt_top_iff_ne_top.1 hZ) (eq_top_iff.2 fun z _ => ?_)
    obtain ⟨z', hz', hzz⟩ := h1 z.2
    have : z' = z := Subtype.ext hzz
    rwa [this] at hz'
  refine ⟨S ⊔ Z₁.map (innAutOf K).subtype, S ⊔ Z₂.map (innAutOf K).subtype, le_sup_left,
    le_sup_left, sup_le hSA.le ((Subgroup.map_subtype_le Z₁).trans hIA),
    sup_le hSA.le ((Subgroup.map_subtype_le Z₂).trans hIA), hnot Z₁ hl₁ key₁,
    hnot Z₂ hl₂ key₂, ?_⟩
  rw [key₁, key₂, ← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.LocalAnalysis.WeakClosure81
