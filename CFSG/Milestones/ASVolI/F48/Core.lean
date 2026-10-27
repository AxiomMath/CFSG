module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.F4Apart
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigFinal
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnGlue
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Rec
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRGD2
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Rec

public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.Quasithin in
@[expose] def burnsideF48_isoSymm {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) : β.Iso α where
  φ1 := ψ.φ1.symm
  φ12 := ψ.φ12.symm
  φ2 := ψ.φ2.symm
  comm1 g := by
    have h := ψ.comm1 (ψ.φ12.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    simp
  comm2 g := by
    have h := ψ.comm2 (ψ.φ12.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    simp

open CFSG.Quasithin CFSG.Quasithin.H13.F48Rig in
@[expose] def burnsideF48_comap {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) {Y : Type} [Group Y]
    (c : β.Completion Y) : α.Completion Y where
  φ1 := c.φ1.comp ψ.φ1.toMonoidHom
  φ12 := c.φ12.comp ψ.φ12.toMonoidHom
  φ2 := c.φ2.comp ψ.φ2.toMonoidHom
  comm1 g := by
    show c.φ1 (ψ.φ1 (α.α1 g)) = c.φ12 (ψ.φ12 g)
    rw [← ψ.comm1 g, c.comm1]
  comm2 g := by
    show c.φ2 (ψ.φ2 (α.α2 g)) = c.φ12 (ψ.φ12 g)
    rw [← ψ.comm2 g, c.comm2]
  inter := by
    rw [range_comp_mulEquiv, range_comp_mulEquiv, range_comp_mulEquiv]
    exact c.inter
  gen := by
    rw [range_comp_mulEquiv, range_comp_mulEquiv]
    exact c.gen

open CFSG.Quasithin CFSG.Quasithin.H13.F48Rig in
theorem burnsideF48_comap_range1 {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) {Y : Type} [Group Y]
    (c : β.Completion Y) : (burnsideF48_comap ψ c).φ1.range = c.φ1.range :=
  range_comp_mulEquiv _ _

open CFSG.Quasithin CFSG.Quasithin.H13.F48Rig in
theorem burnsideF48_comap_range2 {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) {Y : Type} [Group Y]
    (c : β.Completion Y) : (burnsideF48_comap ψ c).φ2.range = c.φ2.range :=
  range_comp_mulEquiv _ _

open CFSG.Quasithin CFSG.Quasithin.H13.F48Rig in
theorem burnsideF48_comap_isFaithful_iff {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) {Y : Type}
    [Group Y] (c : β.Completion Y) :
    (burnsideF48_comap ψ c).IsFaithful ↔ c.IsFaithful := by
  constructor
  · rintro ⟨h1, h12, h2⟩
    refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
    · exact ψ.φ1.symm.injective (h1 (by simpa [burnsideF48_comap] using hab))
    · exact ψ.φ12.symm.injective (h12 (by simpa [burnsideF48_comap] using hab))
    · exact ψ.φ2.symm.injective (h2 (by simpa [burnsideF48_comap] using hab))
  · rintro ⟨h1, h12, h2⟩
    exact ⟨h1.comp ψ.φ1.injective, h12.comp ψ.φ12.injective, h2.comp ψ.φ2.injective⟩

open CFSG.Quasithin CFSG.Quasithin.H13.F48Rig in
theorem burnsideF48_geodUnique_congr {Y : Type} [Group Y] {G₀ G₀' G₁ G₁' G₂ G₂' : Subgroup Y}
    (h0 : G₀ = G₀') (h1 : G₁ = G₁') (h2 : G₂ = G₂') (m : ℕ) :
    GeodUnique G₀ G₁ G₂ m ↔ GeodUnique G₀' G₁' G₂' m := by
  subst h0 h1 h2
  exact Iff.rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.H13.F48Rig in
theorem burnsideF48_comap_isLarge_iff {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) {Y : Type}
    [Group Y] (c : β.Completion Y) (m : ℕ) :
    (burnsideF48_comap ψ c).IsLarge m ↔ c.IsLarge m :=
  burnsideF48_geodUnique_congr
    (by rw [burnsideF48_comap_range1, burnsideF48_comap_range2])
    (burnsideF48_comap_range1 ψ c) (burnsideF48_comap_range2 ψ c) m

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_comap_isSmall_iff {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) {Y : Type}
    [Group Y] (c : β.Completion Y) (m : ℕ) :
    (burnsideF48_comap ψ c).IsSmall m ↔ c.IsSmall m :=
  not_congr (burnsideF48_comap_isLarge_iff ψ c m)

open CFSG.Quasithin in
theorem burnsideF48_isEquivalent_of_phi {α : RankTwoAmalgam.{0}} {Y Y' : Type} [Group Y]
    [Group Y'] (c : α.Completion Y) (c' : α.Completion Y') (φ : Y ≃* Y')
    (h1 : ∀ x, φ (c.φ1 x) = c'.φ1 x) (h2 : ∀ x, φ (c.φ2 x) = c'.φ2 x) :
    Amalgam.Completion.IsEquivalent c.toCompletion c'.toCompletion := by
  refine ⟨φ, fun d x => ?_⟩
  cases d
  · exact h1 x
  · exact h2 x
  · change φ (c.φ12 x) = c'.φ12 x
    have e1 := h1 (α.α1 (show α.G12 from x))
    rw [c.comm1 (show α.G12 from x), c'.comm1 (show α.G12 from x)] at e1
    exact e1

open CFSG.Quasithin in
theorem burnsideF48_isEquivalent_of_comap_symm {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β)
    {Y Y' : Type} [Group Y] [Group Y'] {c : α.Completion Y} {c' : β.Completion Y'}
    (h : Amalgam.Completion.IsEquivalent
      (burnsideF48_comap (burnsideF48_isoSymm ψ) c).toCompletion c'.toCompletion) :
    Amalgam.Completion.IsEquivalent c.toCompletion (burnsideF48_comap ψ c').toCompletion := by
  obtain ⟨φ, hφ⟩ := h
  refine burnsideF48_isEquivalent_of_phi _ _ φ (fun x => ?_) (fun x => ?_)
  · have := hφ RankTwoIndex.one (ψ.φ1 x)
    change φ (c.φ1 (ψ.φ1.symm (ψ.φ1 x))) = c'.φ1 (ψ.φ1 x) at this
    rwa [MulEquiv.symm_apply_apply] at this
  · have := hφ RankTwoIndex.two (ψ.φ2 x)
    change φ (c.φ2 (ψ.φ2.symm (ψ.φ2 x))) = c'.φ2 (ψ.φ2 x) at this
    rwa [MulEquiv.symm_apply_apply] at this

open CFSG.Quasithin in
@[expose] def burnsideF48_toAmIso {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) :
    Amalgam.Iso α.toAmalgam β.toAmalgam where
  toEquiv d := by
    cases d
    · exact ψ.φ1
    · exact ψ.φ2
    · exact ψ.φ12
  comm {d e} h x := by
    cases d <;> cases e <;> first | rfl | exact h.elim | exact ψ.comm1 x | exact ψ.comm2 x

open CFSG.Quasithin in
theorem burnsideF48_comap_toHom {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β) {Y : Type} [Group Y]
    (c : β.Completion Y) (d : RankTwoIndex) (x : α.toAmalgam.X d) :
    (burnsideF48_comap ψ c).toCompletion.toHom d x =
      c.toCompletion.toHom d ((burnsideF48_toAmIso ψ).toEquiv d x) := by
  cases d <;> rfl

open CFSG.Quasithin in
theorem burnsideF48_toAmIso_symm_apply {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β)
    (d : RankTwoIndex) (x : α.toAmalgam.X d) :
    (burnsideF48_toAmIso (burnsideF48_isoSymm ψ)).toEquiv d
      ((burnsideF48_toAmIso ψ).toEquiv d x) = x := by
  cases d <;> exact MulEquiv.symm_apply_apply _ _

open CFSG.Quasithin in
theorem burnsideF48_isQuasiEquivalent_comap {α β : RankTwoAmalgam.{0}} (ψ : α.Iso β)
    {Y Yb : Type} [Group Y] [Group Yb] (c : α.Completion Y) (ι : β.Completion Yb)
    (h : Amalgam.Completion.IsQuasiEquivalent
      (burnsideF48_comap (burnsideF48_isoSymm ψ) c).toCompletion ι.toCompletion) :
    Amalgam.Completion.IsQuasiEquivalent c.toCompletion (burnsideF48_comap ψ ι).toCompletion := by
  obtain ⟨φ, χ, hφ⟩ := h
  let ψA := burnsideF48_toAmIso ψ
  refine ⟨φ, ⟨fun d => (ψA.toEquiv d).trans ((χ.toEquiv d).trans (ψA.toEquiv d).symm), ?_⟩, ?_⟩
  · intro d e h x
    have h1 : ψA.toEquiv e (α.toAmalgam.map h x) = β.toAmalgam.map h (ψA.toEquiv d x) :=
      (ψA.comm h x).symm
    have h2 := χ.comm h (ψA.toEquiv d x)
    have h3 : ∀ w : β.toAmalgam.X d, (ψA.toEquiv e).symm (β.toAmalgam.map h w) =
        α.toAmalgam.map h ((ψA.toEquiv d).symm w) := by
      intro w
      rw [MulEquiv.symm_apply_eq, ← ψA.comm h, MulEquiv.apply_symm_apply]
    simp only [MulEquiv.trans_apply]
    rw [h1, ← h2, h3]
  · intro d x
    have h1 := hφ d ((burnsideF48_toAmIso ψ).toEquiv d x)
    rw [burnsideF48_comap_toHom] at h1
    rw [burnsideF48_comap_toHom]
    rw [burnsideF48_toAmIso_symm_apply] at h1
    rw [h1]
    congr 1
    show _ = ψA.toEquiv d ((ψA.toEquiv d).symm (χ.toEquiv d (ψA.toEquiv d x)))
    rw [MulEquiv.apply_symm_apply]

theorem burnsideF48_isGenLie_of_equiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    {κ : ChF.GLKind} {p f : ℕ} (h : ChF.IsGenLie H κ p f) : ChF.IsGenLie H' κ p f := by
  cases κ
  · obtain ⟨hp, hf, K, hK, hKf, hc, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨hp, hf, K, hK, hKf, hc, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨hp, hf, K, hK, hKf, hc, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨hp, hf, K, hK, hKf, hc, σ, hσ, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, K, hK, hKf, hc, σ, hσ, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨hp, hodd, h1 | h3⟩ := h
    · obtain ⟨hf, K, hK, hKf, hc, ⟨e'⟩⟩ := h1
      exact ⟨hp, hodd, Or.inl ⟨hf, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩⟩
    · obtain ⟨hf, hadm, a, ha, K, hK, hKf, hc, ⟨e'⟩⟩ := h3
      exact ⟨hp, hodd, Or.inr ⟨hf, hadm, a, ha, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩⟩
  · obtain ⟨hp, hf, K, hK, hKf, hc, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨hp, hf, K, hK, hKf, hc, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨hp, hf, K, hK, hKf, hc, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨hp, hf, hadm, a, ha, K, hK, hKf, hc, ⟨e'⟩⟩ := h
    exact ⟨hp, hf, hadm, a, ha, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩

theorem burnsideF48_map_comap_of_le {M E : Type} [Group M] [Group E] (φ : M →* E)
    (hφ : Function.Injective φ) {H : Subgroup M} {A : Subgroup E} (hA : A ≤ H.map φ) :
    A = (A.comap φ).map φ ∧ A.comap φ ≤ H := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.map_comap_eq]
    exact (inf_eq_right.2 (hA.trans (Subgroup.map_le_range φ H))).symm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hA hx
    rwa [← hφ hyx]

theorem burnsideF48_isLieParabolics_map {M E : Type} [Group M] [Group E] (φ : M →* E)
    (hφ : Function.Injective φ) {p : ℕ} {H B P₁ P₂ : Subgroup M}
    (h : ChF.IsLieParabolics p H B P₁ P₂) :
    ChF.IsLieParabolics p (H.map φ) (B.map φ) (P₁.map φ) (P₂.map φ) := by
  obtain ⟨⟨S, ⟨hSle, hSp, hSidx⟩, hB⟩, hne, hinf, hmax⟩ := h
  have hmem : ∀ (A : Subgroup M) (y : M), φ y ∈ A.map φ ↔ y ∈ A := by
    intro A y
    constructor
    · rintro ⟨t, ht, hts⟩
      rwa [← hφ hts]
    · intro hy
      exact ⟨y, hy, rfl⟩
  refine ⟨⟨S.map φ, ⟨Subgroup.map_mono hSle, hSp.map φ, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact hSidx
  · ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine Subgroup.mem_inf.2 ⟨⟨b, ?_, rfl⟩, ?_⟩
      · have hb' : b ∈ H ⊓ Subgroup.normalizer (S : Set M) := hB ▸ hb
        exact (Subgroup.mem_inf.1 hb').1
      · have hb' : b ∈ H ⊓ Subgroup.normalizer (S : Set M) := hB ▸ hb
        exact Subgroup.le_normalizer_map φ ⟨b, (Subgroup.mem_inf.1 hb').2, rfl⟩
    · intro hx
      obtain ⟨⟨m, hmH, rfl⟩, hxN⟩ := Subgroup.mem_inf.1 hx
      refine ⟨m, ?_, rfl⟩
      rw [hB]
      refine Subgroup.mem_inf.2 ⟨hmH, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro s
      have h1 := Subgroup.mem_normalizer_iff.1 hxN (φ s)
      rw [← map_mul, ← map_inv, ← map_mul] at h1
      rw [← hmem S s, h1, hmem S (m * s * m⁻¹)]
  · exact fun e => hne (Subgroup.map_injective hφ e)
  · rw [← Subgroup.map_inf_eq _ _ _ hφ, hinf]
  · intro Q
    have hP1 := (hmax P₁).2 (Or.inl rfl)
    have hP2 := (hmax P₂).2 (Or.inr rfl)
    have hTopInj : ∀ R : Subgroup M, R.map φ = H.map φ → R = H :=
      fun R hR => Subgroup.map_injective hφ hR
    constructor
    · rintro ⟨hBQ, hQH, hQne, hQmax⟩
      obtain ⟨hQe, hQ₀H⟩ := burnsideF48_map_comap_of_le φ hφ hQH
      set Q₀ := Q.comap φ with hQ₀
      have hBQ₀ : B ≤ Q₀ := Subgroup.map_le_iff_le_comap.1 hBQ
      have hQ₀ne : Q₀ ≠ H := by
        intro e
        apply hQne
        rw [hQe, e]
      have hQ₀max : ∀ R₀ : Subgroup M, Q₀ < R₀ → R₀ ≤ H → R₀ = H := by
        rintro R₀ hR₀ hR₀H
        have hlt : Q < R₀.map φ := by
          refine lt_of_le_of_ne ?_ ?_
          · rw [hQe]
            exact Subgroup.map_mono hR₀.le
          · intro e
            have : Q₀ = R₀ := Subgroup.map_injective hφ (by rw [← hQe, e])
            exact hR₀.ne this
        exact hTopInj _ (hQmax _ hlt (Subgroup.map_mono hR₀H))
      rcases (hmax Q₀).1 ⟨hBQ₀, hQ₀H, hQ₀ne, hQ₀max⟩ with e | e
      · exact Or.inl (by rw [hQe, e])
      · exact Or.inr (by rw [hQe, e])
    · intro hQ
      have key : ∀ P : Subgroup M, (B ≤ P ∧ P ≤ H ∧ P ≠ H ∧ ∀ R : Subgroup M, P < R → R ≤ H → R = H) →
          (B.map φ ≤ P.map φ ∧ P.map φ ≤ H.map φ ∧ P.map φ ≠ H.map φ ∧
            ∀ R : Subgroup E, P.map φ < R → R ≤ H.map φ → R = H.map φ) := by
        rintro P ⟨hBP, hPH, hPne, hPmax⟩
        refine ⟨Subgroup.map_mono hBP, Subgroup.map_mono hPH, fun e => hPne (hTopInj _ e), ?_⟩
        intro R hR hRH
        obtain ⟨hRe, hR₀H⟩ := burnsideF48_map_comap_of_le φ hφ hRH
        have hlt : P < R.comap φ := by
          refine lt_of_le_of_ne (Subgroup.map_le_iff_le_comap.1 hR.le) ?_
          intro e
          apply hR.ne
          rw [hRe, ← e]
        have := hPmax _ hlt hR₀H
        rw [hRe, this]
      rcases hQ with rfl | rfl
      · exact key _ hP1
      · exact key _ hP2

theorem burnsideF48_coatom_map_iff {M E : Type} [Group M] [Group E] (φ : M →* E)
    (hφ : Function.Injective φ) {H B Q : Subgroup M} :
    (B.map φ ≤ Q.map φ ∧ Q.map φ ≤ H.map φ ∧ Q.map φ ≠ H.map φ ∧
      ∀ R : Subgroup E, Q.map φ < R → R ≤ H.map φ → R = H.map φ) ↔
    (B ≤ Q ∧ Q ≤ H ∧ Q ≠ H ∧ ∀ R : Subgroup M, Q < R → R ≤ H → R = H) := by
  constructor
  · rintro ⟨hBQ, hQH, hQne, hQmax⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hφ).1 hBQ,
      (Subgroup.map_le_map_iff_of_injective hφ).1 hQH,
      fun e => hQne (by rw [e]), fun R₀ hR₀ hR₀H => ?_⟩
    have hlt : Q.map φ < R₀.map φ := by
      refine lt_of_le_of_ne (Subgroup.map_mono hR₀.le) fun e => hR₀.ne ?_
      exact Subgroup.map_injective hφ e
    exact Subgroup.map_injective hφ (hQmax _ hlt (Subgroup.map_mono hR₀H))
  · rintro ⟨hBP, hPH, hPne, hPmax⟩
    refine ⟨Subgroup.map_mono hBP, Subgroup.map_mono hPH,
      fun e => hPne (Subgroup.map_injective hφ e), ?_⟩
    intro R hR hRH
    obtain ⟨hRe, hR₀H⟩ := burnsideF48_map_comap_of_le φ hφ hRH
    have hlt : Q < R.comap φ := by
      refine lt_of_le_of_ne (Subgroup.map_le_iff_le_comap.1 hR.le) ?_
      intro e
      apply hR.ne
      rw [hRe, ← e]
    have := hPmax _ hlt hR₀H
    rw [hRe, this]

theorem burnsideF48_mem_normalizer_map_iff {M E : Type} [Group M] [Group E] (φ : M →* E)
    (hφ : Function.Injective φ) (S : Subgroup M) (m : M) :
    φ m ∈ Subgroup.normalizer ((S.map φ : Subgroup E) : Set E) ↔
      m ∈ Subgroup.normalizer (S : Set M) := by
  have hmem : ∀ (A : Subgroup M) (y : M), φ y ∈ A.map φ ↔ y ∈ A := by
    intro A y
    constructor
    · rintro ⟨t, ht, hts⟩
      rwa [← hφ hts]
    · intro hy
      exact ⟨y, hy, rfl⟩
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have h1 := Subgroup.mem_normalizer_iff.1 h (φ s)
    rw [← map_mul, ← map_inv, ← map_mul] at h1
    rw [← hmem S s, h1, hmem S (m * s * m⁻¹)]
  · intro h
    exact Subgroup.le_normalizer_map φ ⟨m, h, rfl⟩

theorem burnsideF48_isLieParabolics_of_map {M E : Type} [Group M] [Group E] (φ : M →* E)
    (hφ : Function.Injective φ) {p : ℕ} {H B P₁ P₂ : Subgroup M}
    (h : ChF.IsLieParabolics p (H.map φ) (B.map φ) (P₁.map φ) (P₂.map φ)) :
    ChF.IsLieParabolics p H B P₁ P₂ := by
  obtain ⟨⟨S', ⟨hS'le, hS'p, hS'idx⟩, hB⟩, hne, hinf, hmax⟩ := h
  obtain ⟨hS'e, hS₀H⟩ := burnsideF48_map_comap_of_le φ hφ hS'le
  set S₀ := S'.comap φ with hS₀
  have hmem : ∀ (A : Subgroup M) (y : M), φ y ∈ A.map φ ↔ y ∈ A := by
    intro A y
    constructor
    · rintro ⟨t, ht, hts⟩
      rwa [← hφ hts]
    · intro hy
      exact ⟨y, hy, rfl⟩
  refine ⟨⟨S₀, ⟨hS₀H, hS'p.comap_of_injective φ hφ, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · have := Subgroup.relIndex_map_map_of_injective S₀ H hφ
    rw [← this, ← hS'e]
    exact hS'idx
  · rw [hS'e] at hB
    ext m
    rw [← hmem B m, hB, Subgroup.mem_inf, Subgroup.mem_inf, hmem H m,
      burnsideF48_mem_normalizer_map_iff φ hφ S₀ m]
  · exact fun e => hne (by rw [e])
  · apply Subgroup.map_injective hφ
    rw [Subgroup.map_inf_eq _ _ _ hφ]
    exact hinf
  · intro Q
    rw [← burnsideF48_coatom_map_iff φ hφ, hmax (Q.map φ)]
    constructor
    · rintro (h1 | h2)
      · exact Or.inl (Subgroup.map_injective hφ h1)
      · exact Or.inr (Subgroup.map_injective hφ h2)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem burnsideF48_isLieExtGroup_of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {κ : ChF.GLKind} {p f : ℕ} (h : ChF.IsLieExtGroup G κ p f) : ChF.IsLieExtGroup G' κ p f := by
  obtain ⟨Gq, hGen, hNorm, hcent, B, P₁, P₂, hLP, hdyn⟩ := h
  refine ⟨Gq.map e.toMonoidHom, ?_, ?_, ?_, B.map e.toMonoidHom, P₁.map e.toMonoidHom,
    P₂.map e.toMonoidHom, ?_, ?_⟩
  · exact burnsideF48_isGenLie_of_equiv (e.subgroupMap Gq) hGen
  · exact hNorm.map e.toMonoidHom e.surjective
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : e.symm x ∈ Subgroup.centralizer (Gq : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := Subgroup.mem_centralizer_iff.1 hx (e y) ⟨y, hy, rfl⟩
      have h2 := congrArg e.symm h1
      simpa using h2
    rw [hcent, Subgroup.mem_bot] at hx'
    simpa using congrArg e hx'
  · exact burnsideF48_isLieParabolics_map e.toMonoidHom e.injective hLP
  · intro g hg
    have h1 : e.symm g ∈ Subgroup.normalizer (B : Set G) := by
      have := (burnsideF48_mem_normalizer_map_iff e.toMonoidHom e.injective B (e.symm g)).1
      exact this (by simpa using hg)
    have h2 := hdyn _ h1
    have := (burnsideF48_mem_normalizer_map_iff e.toMonoidHom e.injective P₁ (e.symm g)).2 h2
    simpa using this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_nbrs_finite {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite α.G1]
    [Finite α.G2] {c : α.Completion Y} (hc : c.IsFaithful) (u : c.Γ) :
    (CosetGeom.nbrs u).Finite := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hcard : Nat.card (CosetGeom.nbrs u) =
      Nat.card (CosetGeom.nbrs (c.baseVert (CosetGeom.vtype u))) :=
    calc Nat.card (CosetGeom.nbrs u)
        = Nat.card (CosetGeom.nbrs (g • c.baseVert (CosetGeom.vtype u))) := by rw [hg]
      _ = _ := card_nbrs_smul g _
  refine Set.finite_of_ncard_pos ?_
  rw [← Nat.card_coe_set_eq, hcard]
  generalize CosetGeom.vtype u = b
  cases b
  · have h1 : Nat.card (CosetGeom.nbrs c.xv) = α.α1.range.index := nbrs_xv_card hc
    show 0 < Nat.card (CosetGeom.nbrs c.xv)
    rw [h1]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  · have h1 : Nat.card (CosetGeom.nbrs c.lv) = α.α2.range.index := nbrs_lv_card hc
    show 0 < Nat.card (CosetGeom.nbrs c.lv)
    rw [h1]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_ball_finite {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite α.G1]
    [Finite α.G2] {c : α.Completion Y} (hc : c.IsFaithful) (x : c.Γ) (k : ℕ) :
    {v : c.Γ | c.graph.dist x v ≤ k}.Finite := by
  induction k with
  | zero =>
    refine (Set.finite_singleton x).subset fun v hv => ?_
    have : c.graph.dist x v = 0 := Nat.le_zero.mp hv
    exact ((connected_graph c).dist_eq_zero_iff.mp this).symm
  | succ k ih =>
    refine (ih.union (ih.biUnion fun u _ => burnsideF48_nbrs_finite hc u)).subset fun v hv => ?_
    by_cases hle : c.graph.dist x v ≤ k
    · exact Or.inl hle
    · right
      have hd : c.graph.dist x v = k + 1 := by
        have : c.graph.dist x v ≤ k + 1 := hv
        omega
      obtain ⟨P, hP0, hPv, -⟩ := GPath.exists_geodesic' (connected_graph c) x v hd
      have hgeo : c.graph.dist (P 0) (P (k + 1)) = k + 1 := by rw [hP0, hPv]; exact hd
      have hk : c.graph.dist x (P k) = k := by
        have := GPath.dist_prefix (connected_graph c) P hgeo (show k ≤ k + 1 by omega)
        rwa [hP0] at this
      refine Set.mem_iUnion₂.mpr ⟨P k, le_of_eq hk, ?_⟩
      show c.graph.Adj (P k) v
      have := P.adj k (by omega)
      rwa [hPv] at this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
structure burnsideF48_TC {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    (m : ℕ) : Prop where
  faithful : c.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  trans : ∀ a : c.Γ, c.PathTrans a (m + 1)
  hm : 1 ≤ m

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_TC.hval {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (T : burnsideF48_TC c m) : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  CFSG.ASVolI.ChF.burnsideF4a_hval T.faithful T.thick1 T.thick2

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_TC.f35 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (T : burnsideF48_TC c m) {a : c.Γ} {p : GPath c.graph (m + 1)}
    (hp : p ∈ GPath.nbPaths c.graph a (m + 1)) : GPath.F35Conclusion c.graph c.G0 a m p :=
  GPath.lemma_F35 T.hval (T.trans a) (CosetGeom.connected rfl)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) T.hm hp

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_TC.exists_diam_of_small {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {m : ℕ} (T : burnsideF48_TC c m) (hs : c.IsSmall m) :
    ∃ a : c.Γ, ∀ v, c.graph.dist a v ≤ m := by
  unfold IsSmall IsLarge at hs
  push Not at hs
  obtain ⟨p, q, hp, hq, h0, hm', hne⟩ := hs
  have hpnb : p ∈ GPath.nbPaths c.graph (p 0) m :=
    ⟨rfl, GPath.noBack_of_dist_eq (connected_graph c) p hp⟩
  obtain ⟨r, hr, hrp⟩ := GPath.exists_extend_to T.hval (Nat.le_succ m) hpnb
  have hrm : r m = p m := by rw [← hrp, GPath.take_apply_of_le _ _ _ le_rfl]
  rcases (T.f35 hr).2.2.2.2.2.1 with h | h
  · exfalso
    have e1 := (h r hr).2 p rfl hp (by rw [hrm])
    have e2 := (h r hr).2 q h0.symm hq (by rw [hrm, hm'])
    exact hne (e1.trans e2.symm)
  · exact ⟨p 0, h.1⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_finite_of_small {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite α.G1]
    [Finite α.G2] {c : α.Completion Y} {m : ℕ} (T : burnsideF48_TC c m) (hs : c.IsSmall m) :
    Finite Y := by
  obtain ⟨a, ha⟩ := T.exists_diam_of_small hs
  have hΓ : Finite c.Γ := by
    refine Set.finite_univ_iff.mp ?_
    exact (burnsideF48_ball_finite T.faithful a m).subset fun v _ => ha v
  have h1 : Finite (MulAction.orbit c.G0 c.xv) := inferInstance
  have h2 : Finite (c.G0 ⧸ stv c c.xv) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer c.G0 c.xv)
  have h3 : Finite (stv c c.xv) := by
    rw [stv_xv_eq_range]
    exact Finite.of_surjective (f1 (c := c)).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have h4 : Finite c.G0 :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := stv c c.xv)).symm
  refine Finite.of_surjective (fun g : c.G0 => (g : Y)) fun y => ?_
  have hy : y ∈ c.φ1.range ⊔ c.φ2.range := by rw [c.gen]; exact Subgroup.mem_top y
  exact ⟨⟨y, hy⟩, rfl⟩

theorem burnsideF48_isLieParabolics_swap {E : Type} [Group E] {p : ℕ} {H B P₁ P₂ : Subgroup E}
    (h : ChF.IsLieParabolics p H B P₁ P₂) : ChF.IsLieParabolics p H B P₂ P₁ := by
  obtain ⟨hS, hne, hinf, hmax⟩ := h
  refine ⟨hS, hne.symm, by rw [inf_comm]; exact hinf, fun Q => ?_⟩
  rw [hmax Q, or_comm]

theorem burnsideF48_normalizer_eq_self {D : Type} [Group D] [Finite D] {p : ℕ} (hp : p.Prime)
    {B P₁ P₂ : Subgroup D} (h : ChF.IsLieParabolics p (⊤ : Subgroup D) B P₁ P₂) :
    Subgroup.normalizer (P₁ : Set D) = P₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨S, ⟨-, hSp, hSidx⟩, hB⟩, hne, hinf, hmax⟩ := h
  obtain ⟨hBP₁, -, hP₁ne, hP₁max⟩ := (hmax P₁).2 (Or.inl rfl)
  by_contra hne1
  have hlt : P₁ < Subgroup.normalizer (P₁ : Set D) :=
    lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne1)
  have htop : Subgroup.normalizer (P₁ : Set D) = ⊤ := hP₁max _ hlt le_top
  haveI hnorm : P₁.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hidx : ¬ p ∣ S.index := by
    rwa [Subgroup.relIndex_top_right] at hSidx
  let T : Sylow p D := hSp.toSylow hidx
  have hNB : Subgroup.normalizer (S : Set D) = B := by
    rw [hB, top_inf_eq]
  have hSB : S ≤ B := by
    rw [← hNB]
    exact Subgroup.le_normalizer
  have hT : T ≤ P₁ := fun x hx => hBP₁ (hSB hx)
  have hfr := Sylow.normalizer_sup_eq_top' T hT
  have hle : Subgroup.normalizer (T : Set D) ≤ P₁ := by
    intro x hx
    have : x ∈ B := by rw [← hNB]; exact hx
    exact hBP₁ this
  rw [sup_eq_right.mpr hle] at hfr
  exact hP₁ne hfr

theorem burnsideF48_mem_normalizer_subgroupOf_iff {E : Type} [Group E] {Gp X : Subgroup E}
    (hX : X ≤ Gp) (g : ↥Gp) :
    g ∈ Subgroup.normalizer ((X.subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) ↔
      (g : E) ∈ Subgroup.normalizer (X : Set E) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    by_cases hy : y ∈ Gp
    · have := h ⟨y, hy⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · refine iff_of_false (fun hyX => hy (hX hyX)) (fun hyX => hy ?_)
      have h1 : (g : E)⁻¹ * ((g : E) * y * (g : E)⁻¹) * (g : E) ∈ Gp :=
        Gp.mul_mem (Gp.mul_mem (Gp.inv_mem g.2) (hX hyX)) g.2
      simpa [mul_assoc] using h1
  · intro h y
    simpa [Subgroup.mem_subgroupOf] using h (y : E)

noncomputable abbrev burnsideF48_conj {E : Type} [Group E] (Gp : Subgroup E) [Gp.Normal] :
    E →* MulAut ↥Gp :=
  MulAut.conjNormal

theorem burnsideF48_conj_apply {E : Type} [Group E] (Gp : Subgroup E) [Gp.Normal] (e : E)
    (x : ↥Gp) : ((burnsideF48_conj Gp e x : ↥Gp) : E) = e * (x : E) * e⁻¹ :=
  MulAut.conjNormal_apply e x

theorem burnsideF48_conj_injective {E : Type} [Group E] (Gp : Subgroup E) [Gp.Normal]
    (hC : Subgroup.centralizer (Gp : Set E) = ⊥) : Function.Injective (burnsideF48_conj Gp) := by
  rw [injective_iff_map_eq_one]
  intro e he
  have : e ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun a : MulAut ↥Gp => ((a ⟨x, hx⟩ : ↥Gp) : E)) he
    simp only [burnsideF48_conj_apply, MulAut.one_apply] at h1
    calc x * e = (e * x * e⁻¹) * e := by rw [h1]
      _ = e * x := by group
  rw [hC, Subgroup.mem_bot] at this
  exact this

theorem burnsideF48_conj_mem_autStab_iff {E : Type} [Group E] (Gp : Subgroup E) [Gp.Normal]
    {X : Subgroup E} (hX : X ≤ Gp) (e : E) :
    burnsideF48_conj Gp e ∈ CFSG.Quasithin.autStab (X.subgroupOf Gp) ↔
      e ∈ Subgroup.normalizer (X : Set E) := by
  show (∀ x : ↥Gp, x ∈ X.subgroupOf Gp ↔ burnsideF48_conj Gp e x ∈ X.subgroupOf Gp) ↔ _
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    by_cases hy : y ∈ Gp
    · have := h ⟨y, hy⟩
      simpa [Subgroup.mem_subgroupOf, burnsideF48_conj_apply] using this
    · refine iff_of_false (fun hyX => hy (hX hyX)) (fun hyX => hy ?_)
      have h1 : e⁻¹ * (e * y * e⁻¹) * e ∈ Gp := by
        have := (inferInstance : Gp.Normal).conj_mem _ (hX hyX) e⁻¹
        simpa [mul_assoc] using this
      simpa [mul_assoc] using h1
  · intro h x
    simpa [Subgroup.mem_subgroupOf, burnsideF48_conj_apply] using h (x : E)

@[expose] noncomputable def burnsideF48_restrictEquiv {E F : Type} [Group E] [Group F] (c : E →* F)
    (hc : Function.Injective c) (X : Subgroup E) (N : Subgroup F) (hXN : ∀ e, c e ∈ N ↔ e ∈ X)
    (hN : N ≤ c.range) : ↥X ≃* ↥N :=
  MulEquiv.ofBijective ((c.comp X.subtype).codRestrict N fun x => (hXN x).2 x.2)
    ⟨fun a b hab => Subtype.ext (hc (congrArg Subtype.val hab)), fun n => by
      obtain ⟨e, he⟩ := hN n.2
      exact ⟨⟨e, (hXN e).1 (he ▸ n.2)⟩, Subtype.ext he⟩⟩

theorem burnsideF48_le_normalizer_inf {E : Type} [Group E] (Gp : Subgroup E) [Gp.Normal]
    (M : Subgroup E) : M ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨(inferInstance : Gp.Normal).conj_mem x hx1 a, M.mul_mem (M.mul_mem ha hx2) (M.inv_mem ha)⟩
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · have := (inferInstance : Gp.Normal).conj_mem _ hx1 a⁻¹
      simpa [mul_assoc] using this
    · have := M.mul_mem (M.mul_mem (M.inv_mem ha) hx2) ha
      simpa [mul_assoc] using this

structure burnsideF48_Data {κ : ChF.GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) (T : Subgroup ↥Gp) : Prop where
  yam : CFSG.Quasithin.IsYAmalgamPair T ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp)
  sn1 : ∀ e : E, e ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) → e ∈ M₁
  sn2 : ∀ e : E, e ∈ Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) → e ∈ M₂
  lp : ChF.IsLieParabolics 2 (⊤ : Subgroup ↥Gp) ((Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp)
    ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp)
  nz1 : Subgroup.normalizer (((Gp ⊓ M₁).subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) =
    (Gp ⊓ M₁).subgroupOf Gp
  nz2 : Subgroup.normalizer (((Gp ⊓ M₂).subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) =
    (Gp ⊓ M₂).subgroupOf Gp

@[expose] noncomputable def burnsideF48_lieExt {κ : ChF.GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup ↥Gp}
    (hd : burnsideF48_Data hyp T) : CFSG.Quasithin.H13.F431.LieExt ↥Gp M₁ M₂ :=
  haveI : Gp.Normal := hyp.normal
  { Mbar := (burnsideF48_conj Gp).range
    TD := T
    P1 := (Gp ⊓ M₁).subgroupOf Gp
    P2 := (Gp ⊓ M₂).subgroupOf Gp
    inn_le := by
      rintro _ ⟨d, rfl⟩
      exact ⟨(d : E), MulAut.conjNormal_val⟩
    yam := hd.yam
    diag := by
      rintro _ ⟨e, rfl⟩ h
      have hX : (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) ≤ Gp := inf_le_left
      have hP : ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp : Subgroup ↥Gp) =
          (Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp := by
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
        tauto
      rw [hP] at h
      have h1 := (burnsideF48_conj_mem_autStab_iff Gp hX e).1 h
      exact (burnsideF48_conj_mem_autStab_iff Gp (inf_le_left : Gp ⊓ M₁ ≤ Gp) e).2
        (hyp.dynkin e h1)
    iso :=
      { φ1 := burnsideF48_restrictEquiv (burnsideF48_conj Gp)
          (burnsideF48_conj_injective Gp hyp.centralizer_trivial) M₁ _
          (fun e => ⟨fun ⟨_, hst⟩ => hd.sn1 e
              ((burnsideF48_conj_mem_autStab_iff Gp (inf_le_left : Gp ⊓ M₁ ≤ Gp) e).1 hst),
            fun hm => ⟨⟨e, rfl⟩, (burnsideF48_conj_mem_autStab_iff Gp
              (inf_le_left : Gp ⊓ M₁ ≤ Gp) e).2 (burnsideF48_le_normalizer_inf Gp M₁ hm)⟩⟩)
          inf_le_left
        φ12 := burnsideF48_restrictEquiv (burnsideF48_conj Gp)
          (burnsideF48_conj_injective Gp hyp.centralizer_trivial) (M₁ ⊓ M₂) _
          (fun e => ⟨fun ⟨⟨_, hst1⟩, ⟨_, hst2⟩⟩ => ⟨hd.sn1 e
              ((burnsideF48_conj_mem_autStab_iff Gp (inf_le_left : Gp ⊓ M₁ ≤ Gp) e).1 hst1),
              hd.sn2 e ((burnsideF48_conj_mem_autStab_iff Gp (inf_le_left : Gp ⊓ M₂ ≤ Gp) e).1
                hst2)⟩,
            fun hm => ⟨⟨⟨e, rfl⟩, (burnsideF48_conj_mem_autStab_iff Gp
              (inf_le_left : Gp ⊓ M₁ ≤ Gp) e).2 (burnsideF48_le_normalizer_inf Gp M₁ hm.1)⟩,
              ⟨⟨e, rfl⟩, (burnsideF48_conj_mem_autStab_iff Gp
              (inf_le_left : Gp ⊓ M₂ ≤ Gp) e).2 (burnsideF48_le_normalizer_inf Gp M₂ hm.2)⟩⟩⟩)
          (inf_le_left.trans inf_le_left)
        φ2 := burnsideF48_restrictEquiv (burnsideF48_conj Gp)
          (burnsideF48_conj_injective Gp hyp.centralizer_trivial) M₂ _
          (fun e => ⟨fun ⟨_, hst⟩ => hd.sn2 e
              ((burnsideF48_conj_mem_autStab_iff Gp (inf_le_left : Gp ⊓ M₂ ≤ Gp) e).1 hst),
            fun hm => ⟨⟨e, rfl⟩, (burnsideF48_conj_mem_autStab_iff Gp
              (inf_le_left : Gp ⊓ M₂ ≤ Gp) e).2 (burnsideF48_le_normalizer_inf Gp M₂ hm)⟩⟩)
          inf_le_left
        comm1 := fun g => Subtype.ext rfl
        comm2 := fun g => Subtype.ext rfl } }

theorem burnsideF48_normalizer_le {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hsn : ∀ g : ↥Gp,
      g ∈ Subgroup.normalizer (((Gp ⊓ M₁).subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) →
        g ∈ (Gp ⊓ M₁).subgroupOf Gp)
    (e : E) (he : e ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E)) : e ∈ M₁ := by
  obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
  have hhN : h ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) :=
    burnsideF48_le_normalizer_inf Gp M₁ hh.1
  have hnN : n ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) := by
    have := (Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E)).mul_mem he
      ((Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E)).inv_mem hhN)
    simpa using this
  have hg := hsn ⟨n, hn⟩
    ((burnsideF48_mem_normalizer_subgroupOf_iff (inf_le_left : Gp ⊓ M₁ ≤ Gp) ⟨n, hn⟩).2 hnN)
  exact M₁.mul_mem (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).2 hh.1

theorem burnsideF48_isLieParabolics_subgroupOf {E : Type} [Group E] {p : ℕ} {Gp M₁ M₂ : Subgroup E}
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    ChF.IsLieParabolics p (⊤ : Subgroup ↥Gp) ((Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp)
      ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp) := by
  refine burnsideF48_isLieParabolics_of_map Gp.subtype Gp.subtype_injective ?_
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left : Gp ⊓ (M₁ ⊓ M₂) ≤ Gp),
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left : Gp ⊓ M₁ ≤ Gp),
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left : Gp ⊓ M₂ ≤ Gp)]
  exact hP

@[expose] def burnsideF48_YamPair {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) : Prop :=
  ∃ T : Subgroup ↥Gp, CFSG.Quasithin.IsYAmalgamPair T ((Gp ⊓ M₁).subgroupOf Gp)
    ((Gp ⊓ M₂).subgroupOf Gp)

theorem burnsideF48_exists_data_of_yam {κ : ChF.GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ∃ T : Subgroup ↥Gp, burnsideF48_Data hyp T := by
  haveI : Gp.Normal := hyp.normal
  haveI : Finite E := hyp.finite
  haveI : Finite ↥Gp := inferInstance
  have hPD := burnsideF48_isLieParabolics_subgroupOf hP
  obtain ⟨U, hU⟩ := hY
  have hsn1 := burnsideF48_normalizer_eq_self Nat.prime_two hPD
  have hsn2 := burnsideF48_normalizer_eq_self Nat.prime_two (burnsideF48_isLieParabolics_swap hPD)
  refine ⟨U, hU, ?_, ?_, hPD, hsn1, hsn2⟩
  · refine burnsideF48_normalizer_le hyp.split fun g hg => ?_
    rw [hsn1] at hg
    exact hg
  · refine burnsideF48_normalizer_le (M₁ := M₂) (M₂ := M₁) (fun e => ?_) (fun g hg => ?_)
    · obtain ⟨n, hn, h, hh, he⟩ := hyp.split e
      exact ⟨n, hn, h, by rwa [inf_comm], he⟩
    · rw [hsn2] at hg
      exact hg

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_stv_lv_iff {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (g : c.G0) : g ∈ stv c c.lv ↔ g ∈ (f2 (c := c)).range := by
  constructor
  · intro hg
    exact stv_lv_le_range_f2 c hg
  · rintro ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a)

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_stv_xv_setting {D : Type} [Group D] (A : LieAmalgamExt D) (hfin : Finite D)
    (pm : ℕ) (hpm : 3 ≤ pm) (x : (A.setting hfin pm hpm).ι.G0) :
    x ∈ stv (A.setting hfin pm hpm).ι (A.setting hfin pm hpm).ι.xv ↔
      settingToAut A hfin pm hpm x ∈ A.N1 := by
  rw [stv_xv_eq_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_stv_lv_setting {D : Type} [Group D] (A : LieAmalgamExt D) (hfin : Finite D)
    (pm : ℕ) (hpm : 3 ≤ pm) (x : (A.setting hfin pm hpm).ι.G0) :
    x ∈ stv (A.setting hfin pm hpm).ι (A.setting hfin pm hpm).ι.lv ↔
      settingToAut A hfin pm hpm x ∈ A.N2 := by
  rw [burnsideF48_mem_stv_lv_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩

theorem burnsideF48_center_eq_bot {E : Type} [Group E] {Gp : Subgroup E}
    (hC : Subgroup.centralizer (Gp : Set E) = ⊥) : Subgroup.center ↥Gp = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have : (z : E) ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_center_iff.1 hz ⟨x, hx⟩
    exact congrArg Subtype.val this
  rw [hC, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem burnsideF48_K_eq {κ : ChF.GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup ↥Gp} (hd : burnsideF48_Data hyp T) :
    (burnsideF48_lieExt hyp hd).toLieAmalgamExt.K =
      letI : Gp.Normal := hyp.normal
      (burnsideF48_conj Gp).range := by
  haveI : Gp.Normal := hyp.normal
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  rw [MonoidHom.range_eq_map, ← hyp.gen, Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact (burnsideF48_lieExt hyp hd).iso.φ1 ⟨m, hm⟩ |>.2
  · rintro _ ⟨m, hm, rfl⟩
    exact (burnsideF48_lieExt hyp hd).iso.φ2 ⟨m, hm⟩ |>.2

theorem burnsideF48_conj_mem_autStab_iff' {D : Type} [Group D] (d : D) (P : Subgroup D) :
    (MulAut.conj d : MulAut D) ∈ CFSG.Quasithin.autStab P ↔
      d ∈ Subgroup.normalizer (P : Set D) := by
  show (∀ x : D, x ∈ P ↔ MulAut.conj d x ∈ P) ↔ _
  rw [Subgroup.mem_normalizer_iff]
  simp only [MulAut.conj_apply]

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_isLieExtGroup_of_isExtension {κ : ChF.GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup ↥Gp}
    (hd : burnsideF48_Data hyp T) {hfin : Finite ↥Gp} (pm : ℕ) (hpm : 3 ≤ pm) {Ġ : Type}
    [Group Ġ]
    (hext : ((burnsideF48_lieExt hyp hd).toLieAmalgamExt.setting hfin pm hpm).IsExtension Ġ) :
    ChF.IsLieExtGroup Ġ κ 2 f := by
  haveI : Gp.Normal := hyp.normal
  have hZ : Subgroup.center ↥Gp = ⊥ := burnsideF48_center_eq_bot hyp.centralizer_trivial
  have hKeq := burnsideF48_K_eq hyp hd
  set A : LieAmalgamExt ↥Gp := (burnsideF48_lieExt hyp hd).toLieAmalgamExt with hA
  set S := A.setting hfin pm hpm with hS
  obtain ⟨ν, hνinj, hνnorm, hνcent, hνdyn⟩ := hext
  have hgen : (MulAut.conj : ↥Gp →* MulAut ↥Gp).range ≤ A.K := by
    rw [hA, hKeq]
    rintro _ ⟨d, rfl⟩
    exact ⟨(d : E), MulAut.conjNormal_val⟩
  let eN : ↥Gp ≃* ↥S.N := MulEquiv.ofBijective (toSettingN A hfin pm hpm hgen)
    ⟨toSettingN_injective A hfin pm hpm hZ hgen, toSettingN_surjective A hfin pm hpm hgen⟩
  have hconj : ∀ d : ↥Gp, settingToAut A hfin pm hpm ((eN d : ↥S.N) : S.ι.G0) = MulAut.conj d :=
    fun d => rfl
  have hN1iff : ∀ d : ↥Gp, MulAut.conj d ∈ A.N1 ↔ d ∈ (Gp ⊓ M₁).subgroupOf Gp := by
    intro d
    have hmb : MulAut.conj d ∈ A.Mbar := A.inn_le ⟨d, rfl⟩
    show MulAut.conj d ∈ A.Mbar ⊓ autStab A.P1 ↔ _
    rw [Subgroup.mem_inf, and_iff_right hmb, burnsideF48_conj_mem_autStab_iff']
    show d ∈ Subgroup.normalizer (((Gp ⊓ M₁).subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) ↔ _
    rw [hd.nz1]
  have hN2iff : ∀ d : ↥Gp, MulAut.conj d ∈ A.N2 ↔ d ∈ (Gp ⊓ M₂).subgroupOf Gp := by
    intro d
    have hmb : MulAut.conj d ∈ A.Mbar := A.inn_le ⟨d, rfl⟩
    show MulAut.conj d ∈ A.Mbar ⊓ autStab A.P2 ↔ _
    rw [Subgroup.mem_inf, and_iff_right hmb, burnsideF48_conj_mem_autStab_iff']
    show d ∈ Subgroup.normalizer (((Gp ⊓ M₂).subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) ↔ _
    rw [hd.nz2]
  have hS1 : S.N1 = ((Gp ⊓ M₁).subgroupOf Gp).map eN.toMonoidHom := by
    ext n
    obtain ⟨d, rfl⟩ := eN.surjective n
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    show ((eN d : ↥S.N) : S.ι.G0) ∈ stv S.ι S.ι.xv ↔ _
    rw [burnsideF48_mem_stv_xv_setting A hfin pm hpm, hconj, hN1iff]
  have hS2 : (stv S.ι S.ι.lv).subgroupOf S.N =
      ((Gp ⊓ M₂).subgroupOf Gp).map eN.toMonoidHom := by
    ext n
    obtain ⟨d, rfl⟩ := eN.surjective n
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    show ((eN d : ↥S.N) : S.ι.G0) ∈ stv S.ι S.ι.lv ↔ _
    rw [burnsideF48_mem_stv_lv_setting A hfin pm hpm, hconj, hN2iff]
  have hS12 : S.N12 = ((Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp).map eN.toMonoidHom := by
    ext n
    obtain ⟨d, rfl⟩ := eN.surjective n
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    show ((eN d : ↥S.N) : S.ι.G0) ∈ stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv ↔ _
    rw [Subgroup.mem_inf, burnsideF48_mem_stv_xv_setting A hfin pm hpm,
      burnsideF48_mem_stv_lv_setting A hfin pm hpm, hconj, hN1iff, hN2iff]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    tauto
  have hIL : ChF.IsLieParabolics 2 (⊤ : Subgroup ↥S.N) S.N12 S.N1
      ((stv S.ι S.ι.lv).subgroupOf S.N) := by
    rw [hS12, hS1, hS2, ← Subgroup.map_top_of_surjective eN.toMonoidHom eN.surjective]
    exact burnsideF48_isLieParabolics_map eN.toMonoidHom eN.injective hd.lp
  have hIL' := burnsideF48_isLieParabolics_map ν hνinj hIL
  rw [← MonoidHom.range_eq_map] at hIL'
  exact ⟨ν.range, burnsideF48_isGenLie_of_equiv (eN.trans (MonoidHom.ofInjective hνinj))
    hyp.model, hνnorm, hνcent, S.N12.map ν, S.N1.map ν,
    ((stv S.ι S.ι.lv).subgroupOf S.N).map ν, hIL', hνdyn⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
@[expose] noncomputable def burnsideF48_G0Equiv {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) : c.G0 ≃* Y :=
  (MulEquiv.subgroupCongr c.gen).trans Subgroup.topEquiv

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_of_setting {κ : ChF.GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup ↥Gp}
    (hd : burnsideF48_Data hyp T) {hfin : Finite ↥Gp} (pm : ℕ) (hpm : 3 ≤ pm) (hκ : κ.m = pm)
    (h45 : ((burnsideF48_lieExt hyp hd).toLieAmalgamExt.setting hfin pm hpm).Facts45L)
    (h48 : ∀ (Y : Type) [Group Y] [Finite Y]
      (β : ((burnsideF48_lieExt hyp hd).toLieAmalgamExt.setting hfin pm hpm).α.Completion Y),
      β.IsFaithful → β.IsSmall pm →
        ((burnsideF48_lieExt hyp hd).toLieAmalgamExt.setting hfin pm hpm).F48Concl β) :
    ChF.F48Concl κ 2 f Gp M₁ M₂ := by
  haveI : Gp.Normal := hyp.normal
  set L := burnsideF48_lieExt hyp hd with hL
  set A : LieAmalgamExt ↥Gp := L.toLieAmalgamExt with hA
  set S := A.setting hfin pm hpm with hS
  let ψ : (RankTwoAmalgam.ofSubgroups M₁ M₂).Iso S.α := L.iso
  haveI : Finite (MulAut ↥Gp) := finite_mulAut_of_finite
  haveI hG1 : Finite S.α.G1 := inferInstanceAs (Finite ↥A.N1)
  haveI hG2 : Finite S.α.G2 := inferInstanceAs (Finite ↥A.N2)
  have hN : ∀ (Y : Type) [Group Y] (β : ChF.Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      Finite Y ∧ (burnsideF48_comap (burnsideF48_isoSymm ψ) β).IsFaithful ∧
        (burnsideF48_comap (burnsideF48_isoSymm ψ) β).IsSmall pm := by
    intro Y _ β hβ hs
    have hβN := (burnsideF48_comap_isFaithful_iff (burnsideF48_isoSymm ψ) β).2 hβ
    have hsN := (burnsideF48_comap_isSmall_iff (burnsideF48_isoSymm ψ) β pm).2 (hκ ▸ hs)
    refine ⟨?_, hβN, hsN⟩
    exact burnsideF48_finite_of_small (c := burnsideF48_comap (burnsideF48_isoSymm ψ) β)
      ⟨hβN, h45.thick1, h45.thick2,
        pathTrans_transfer _ hβN S.ι S.hι (S.m + 1) h45.trans, by show 1 ≤ pm; omega⟩ hsN
  have hKeq := burnsideF48_K_eq hyp hd
  refine ⟨fun Y _ β hβ hs => ?_, fun hGp => ?_⟩
  ·
    obtain ⟨hfinY, hβN, hsN⟩ := hN Y β hβ hs
    obtain ⟨⟨Ġ, hĠ, β'N, hβ'N, heq, hext⟩, -⟩ := h48 Y _ hβN hsN
    have heqM := burnsideF48_isEquivalent_of_comap_symm ψ heq
    have hP4 := burnsideF48_isLieExtGroup_of_isExtension hyp hd pm hpm hext
    obtain ⟨φ, hφ⟩ := heqM
    refine ⟨Ġ, hĠ, burnsideF48_comap ψ β'N, ⟨φ, hφ⟩, ?_, ?_⟩
    · exact burnsideF48_isLieExtGroup_of_equiv
        (burnsideF48_G0Equiv (burnsideF48_comap ψ β'N)).symm hP4
    · exact ⟨(burnsideF48_G0Equiv β).trans
        (φ.trans (burnsideF48_G0Equiv (burnsideF48_comap ψ β'N)).symm)⟩
  ·
    have hKmem : ∀ φ : MulAut ↥Gp, φ ∈ A.K → ∃ d : ↥Gp, (MulAut.conj d : MulAut ↥Gp) = φ := by
      intro φ hφ
      have hφ' : φ ∈ (burnsideF48_conj Gp).range := by rw [← hKeq]; exact hφ
      obtain ⟨e, he⟩ := hφ'
      have heGp : e ∈ Gp := by rw [hGp]; trivial
      exact ⟨⟨e, heGp⟩, ((MulAut.conjNormal_val (h := ⟨e, heGp⟩)).symm).trans he⟩
    have hNtop : S.N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hKmem x.1.1 x.1.2
    have hinj := burnsideF48_conj_injective Gp hyp.centralizer_trivial
    let eK : E ≃* ↥A.K :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by rw [hA, hKeq]))
    refine ⟨⟨S.Yb, inferInstance, burnsideF48_comap ψ S.ι,
      (burnsideF48_comap_isFaithful_iff ψ S.ι).2 S.hι,
      (burnsideF48_comap_isSmall_iff ψ S.ι κ.m).2 (hκ ▸ h45.isSmall_iota), ?_⟩, ?_⟩
    · intro Y _ β hβ hs
      obtain ⟨hfinY, hβN, hsN⟩ := hN Y β hβ hs
      have h2 := (h48 Y _ hβN hsN).2 hNtop
      exact burnsideF48_isQuasiEquivalent_comap ψ β S.ι h2
    · intro Y _ β hβ hs
      obtain ⟨hfinY, hβN, hsN⟩ := hN Y β hβ hs
      have h2 := (h48 Y _ hβN hsN).2 hNtop
      obtain ⟨φ, -, -⟩ := burnsideF48_isQuasiEquivalent_comap ψ β S.ι h2
      exact ⟨(burnsideF48_G0Equiv β).trans (φ.trans eK.symm)⟩

theorem burnsideF48_parabolics_of_compat (hcompat : ChF.NativeChartCompatibilityGoal)
    {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) :
    ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨h1, h2, h3⟩ := hyp.toHypF_4_4g.chart_matches
  have hlp := (hcompat κ p f E Gp hyp.toHypF_4_4g.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  exact hlp

open CFSG.Quasithin.H13.F431 CFSG.Blueprint in
theorem burnsideF48_concl_two_of_F431 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    {κ : ChF.GLKind} (hm : F431ModelFacts t m f) (h45 : F431Facts45 t m f hm)
    (h48 : F431F48 t m f hm) (hκ : κ.m = polyNumber t) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) (hlie : LieModel ↥Gp t m 2 f)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl κ 2 f Gp M₁ M₂ := by
  obtain ⟨T, hd⟩ := burnsideF48_exists_data_of_yam hyp hP hY
  exact burnsideF48_concl_of_setting hyp hd (hfin := (hm ↥Gp hlie).1) (polyNumber t)
    (three_le_polyNumber t) hκ (h45 ↥Gp hlie _)
    (fun Y _ _ β hβ hs => h48 ↥Gp hlie _ Y β hβ hs)

open CFSG.Blueprint in
theorem burnsideF48_lieModel_L3 {H : Type} [Group H] {f : ℕ} (h : ChF.IsGenLie H .L3 2 f) :
    LieModel H .PSL 3 2 f := by
  obtain ⟨hp, hf, K, hK, hKf, hc, he⟩ := h
  exact Or.inl ⟨by decide, ⟨hp, hf, by norm_num, by simp [Prod.ext_iff], by simp [Prod.ext_iff]⟩,
    K, hK, hKf, hc, he⟩

open CFSG.Blueprint in
theorem burnsideF48_lieModel_Sp4 {H : Type} [Group H] {f : ℕ} (hf2 : 2 ≤ f)
    (h : ChF.IsGenLie H .Sp4 2 f) : LieModel H .PSp 2 2 f := by
  obtain ⟨hp, hf, K, hK, hKf, hc, he⟩ := h
  refine Or.inl ⟨by decide, ⟨hp, hf, by norm_num, fun e => ?_⟩, K, hK, hKf, hc, he⟩
  have h1 : (2 : ℕ) ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have h2 : 2 ^ f = 2 := (Prod.mk.inj e).2
  omega

open CFSG.Blueprint in
theorem burnsideF48_lieModel_U4 {H : Type} [Group H] {f : ℕ} (h : ChF.IsGenLie H .U4 2 f) :
    LieModel H .PSU 4 2 f := by
  obtain ⟨hp, hf, K, hK, hKf, hc, he⟩ := h
  exact Or.inl ⟨by decide, ⟨hp, hf, by norm_num, by simp [Prod.ext_iff]⟩, K, hK, hKf, hc, he⟩

open CFSG.Blueprint in
theorem burnsideF48_lieModel_U5 {H : Type} [Group H] {f : ℕ} (h : ChF.IsGenLie H .U5 2 f) :
    LieModel H .PSU 5 2 f := by
  obtain ⟨hp, hf, K, hK, hKf, hc, he⟩ := h
  exact Or.inl ⟨by decide, ⟨hp, hf, by norm_num, by simp [Prod.ext_iff]⟩, K, hK, hKf, hc, he⟩

open CFSG.Blueprint in
theorem burnsideF48_lieModel_G2 {H : Type} [Group H] {f : ℕ} (hf2 : 2 ≤ f)
    (h : ChF.IsGenLie H .G2 2 f) : LieModel H .G2 0 2 f := by
  obtain ⟨hp, hf, hm⟩ := h
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨hp, hf, rfl, ?_⟩, hm⟩)
  have h1 : (2 : ℕ) ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  omega

open CFSG.Blueprint in
theorem burnsideF48_lieModel_D4 {H : Type} [Group H] {f : ℕ} (h : ChF.IsGenLie H .D4tw 2 f) :
    LieModel H .trialityD4 0 2 f := by
  obtain ⟨hp, hf, hm⟩ := h
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨hp, hf, rfl⟩, hm⟩)

open CFSG.Blueprint in
theorem burnsideF48_lieModel_F4 {H : Type} [Group H] {f : ℕ} (hf3 : 3 ≤ f) (hodd : Odd f)
    (h : ChF.IsGenLie H .F4tw 2 f) : LieModel H .twistedF4 0 2 f := by
  obtain ⟨hp, hodd', h1 | h3⟩ := h
  · omega
  · obtain ⟨-, hR⟩ := h3
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))

theorem burnsideF48_injective_torusDiag_un5 {F : Type} [Field F] (q N : ℕ) (hq : 4 ≤ q)
    (hN : N + 1 = q * q) (g : Fˣ) (hg : orderOf g = N) :
    Function.Injective ![(g : F), (g : F) ^ q, 1, (g : F)⁻¹, ((g : F) ^ q)⁻¹] := by
  have h4 : 4 * q ≤ N + 1 := by rw [hN]; exact Nat.mul_le_mul_right q hq
  have key : ∀ a b : ℕ, a < N → b < N → ((g ^ a : Fˣ) : F) = ((g ^ b : Fˣ) : F) → a = b := by
    intro a b ha hb h
    have := (pow_eq_pow_iff_modEq.1 (Units.ext h) : a ≡ b [MOD orderOf g])
    rw [hg] at this
    exact Nat.ModEq.eq_of_lt_of_lt this ha hb
  have hgN : g ^ N = 1 := by rw [← hg, pow_orderOf_eq_one]
  have hinv : ((g : F))⁻¹ = ((g ^ (N - 1) : Fˣ) : F) := by
    have h1 : g * g ^ (N - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega), hgN]
    rw [← Units.val_inv_eq_inv_val, inv_eq_of_mul_eq_one_right h1]
  have hinvq : ((g : F) ^ q)⁻¹ = ((g ^ (N - q) : Fˣ) : F) := by
    have h1 : g ^ q * g ^ (N - q) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega), hgN]
    rw [← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val, inv_eq_of_mul_eq_one_right h1]
  have hvec : ![(g : F), (g : F) ^ q, 1, (g : F)⁻¹, ((g : F) ^ q)⁻¹] =
      ![((g ^ 1 : Fˣ) : F), ((g ^ q : Fˣ) : F), ((g ^ 0 : Fˣ) : F), ((g ^ (N - 1) : Fˣ) : F),
        ((g ^ (N - q) : Fˣ) : F)] := by
    rw [hinv, hinvq]
    simp
  rw [hvec]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hij ⊢ <;>
  first
    | rfl
    | (exfalso; have := key _ _ (by omega) (by omega) hij; omega)

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.BorelTits Matrix
  CFSG.Quasithin.H13.F431.Un in
theorem burnsideF48_exists_cartan_un5 {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hf : 2 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2) (ζ : traceZero (unitaryInvolution F 2 f))
    [hζ : Fact ((ζ : F) ≠ 0)] :
    ∃ h ∈ unB hF 5 ⊓ unN hF 5 ζ, ∀ y ∈ unU hF 5, h * y * h⁻¹ = y → y = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ f := ⟨_, rfl⟩
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqq1 : 1 ≤ q * q := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hord : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, hF, ← hq, sq]
  have hN : (q * q - 1) + 1 = q * q := Nat.sub_add_cancel hqq1
  have hσ := unitaryInvolution_involutive hF
  have hgN : (g : F) ^ (q * q - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hord, pow_orderOf_eq_one, Units.val_one]
  have hqq : (g : F) ^ (q * q) = (g : F) := by
    rw [← hN, pow_succ, hgN, one_mul]
  have hσg : unitaryInvolution F 2 f (g : F) = (g : F) ^ q := by
    rw [unitaryInvolution_apply, hq]
  have hσe : unitaryInvolution F 2 f ((g ^ (q + 1) : Fˣ) : F) = ((g ^ (q + 1) : Fˣ) : F) := by
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, ← pow_mul]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hq]
    calc (g : F) ^ ((q + 1) * q) = (g : F) ^ (q * q) * (g : F) ^ q := by
          rw [← pow_add]; congr 1; ring
      _ = (g : F) ^ (q + 1) := by rw [hqq, ← pow_succ']
  have h0 : (0 : ℕ) + 1 < 5 / 2 := by norm_num
  have h1 : ¬ ((1 : ℕ) + 1 < 5 / 2) := by norm_num
  set k0 : Fin (5 / 2) := ⟨0, by norm_num⟩ with hk0
  set k1 : Fin (5 / 2) := ⟨1, by norm_num⟩ with hk1
  have hc0 : (g : F) ≠ 0 := g.ne_zero
  have he0 : ((g ^ (q + 1) : Fˣ) : F) ≠ 0 := (g ^ (q + 1)).ne_zero
  have hmem0 := shortTorus_mem_levelTorus (σ := unitaryInvolution F 2 f) hσ (k := k0) h0 g
  have hmem1 := longTorus_mem_levelTorus (σ := unitaryInvolution F 2 f) (k := k1) h1
    (ζ := ζ) hζ.out (g ^ (q + 1)) hσe
  have hd0 := coe_shortTorus (unitaryInvolution F 2 f) hσ (lowIdx_ne_succ h0)
    (lowIdx_ne_rev k0 k0) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) hc0
  have hd1 := coe_longTorus (unitaryInvolution F 2 f) (lowIdx_ne_rev k1 k1) hζ.out hσe he0
  have hT0 := (le_iSup (fun i => levelTorus (unitaryInvolution F 2 f) i) k0) hmem0
  have hT1 := (le_iSup (fun i => levelTorus (unitaryInvolution F 2 f) i) k1) hmem1
  refine ⟨_, by rw [un5B_inf_N hF ζ]; exact mul_mem hT0 hT1, fun y hy hc => ?_⟩
  have hdiag : mat (unitaryInvolution F 2 f)
      5 (shortTorus (unitaryInvolution F 2 f) hσ (lowIdx_ne_succ h0) (lowIdx_ne_rev k0 k0)
        (lowIdx_ne_rev _ _) (g : F) * longTorus (unitaryInvolution F 2 f) (lowIdx_ne_rev k1 k1) ζ
          hσe) =
      diagonal ![(g : F), (g : F) ^ q, 1, (g : F)⁻¹, ((g : F) ^ q)⁻¹] := by
    rw [map_mul]
    refine (congrArg₂ (· * ·) hd0 hd1).trans ((diagonal_mul_diagonal _ _).trans ?_)
    congr 1
    funext s
    fin_cases s <;> simp [shortTorusFun, longTorusFun, lowIdx, hk0, hk1, Fin.ext_iff, hσg]
    · rw [pow_succ', inv_mul_cancel_left₀ hc0]
    · rw [pow_succ, mul_inv, mul_inv_cancel_left₀ (pow_ne_zero q hc0)]
  exact eq_one_of_comm_diagonal_un5 hF
    (burnsideF48_injective_torusDiag_un5 q (q * q - 1) hq4 hN g hord) hdiag hy hc

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.Quasithin.H13.F48Rig CFSG.Quasithin.H13.F431.F48Rig
  CFSG.QuasithinUnique CFSG.LieType.Universal.Unitary CFSG.GH74.BNPair CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.Quasithin.H13.F431.Un in
theorem burnsideF48_exists_cartan_un5_quot {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hf : 2 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2) (ζ : traceZero (unitaryInvolution F 2 f))
    [hζ : Fact ((ζ : F) ≠ 0)] :
    ∃ h ∈ (un5System hF ζ).B ⊓ (un5System hF ζ).N, ∀ y ∈ (un5System hF ζ).U,
      h * y * h⁻¹ = y → y = 1 := by
  obtain ⟨h0, hh0, hc0⟩ := burnsideF48_exists_cartan_un5 hf hF ζ
  refine ⟨un5Proj h0, ⟨⟨h0, hh0.1, rfl⟩, ⟨h0, hh0.2, rfl⟩⟩, ?_⟩
  rintro _ ⟨u, hu0, rfl⟩ hc
  have hu : u ∈ unU hF 5 := hu0
  have hnorm : h0 * u * h0⁻¹ ∈ unU hF 5 := by
    obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
    have : Fact ((ζ' : F) ≠ 0) := ⟨hζ'⟩
    exact (Subgroup.mem_normalizer_iff.1
      (borel_le_normalizer_posUnipotent (un5_isCTGroupDatum hF ζ') hh0.1) u).1 hu
  have hker : h0 * u * h0⁻¹ * u⁻¹ ∈ (un5Proj (F := F) (f := f)).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc, mul_inv_cancel]
  have hmemU : h0 * u * h0⁻¹ * u⁻¹ ∈ unU hF 5 :=
    (unU hF 5).mul_mem hnorm ((unU hF 5).inv_mem hu)
  have h1 : h0 * u * h0⁻¹ * u⁻¹ = 1 :=
    Subgroup.mem_bot.1 ((un5_U_inf_ker hF).le ⟨hmemU, hker⟩)
  have h2 : h0 * u * h0⁻¹ = u := mul_inv_eq_one.1 h1
  rw [hc0 u hu h2, map_one]

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.Quasithin.H13.F48Rig CFSG.Quasithin.H13.F431.F48Rig
  CFSG.QuasithinUnique CFSG.Open CFSG.LieType.Universal.Unitary CFSG.Quasithin.H13.F431.Un in
theorem burnsideF48_cartanFPF_un5 {f : ℕ} (hf : 2 ≤ f) (hm : F431ModelFacts .PSU 5 f)
    (D : Type) [Group D] (hD : LieModel D .PSU 5 2 f) (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .PSU) (three_le_polyNumber .PSU)).CartanFPF := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_un5 hF
  have hU := isSylowTwoOf_un5System hF ζ
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (un5System hF ζ) hU (hm D hD).1
    (by norm_num) e A
  obtain ⟨h, hh, hc⟩ := burnsideF48_exists_cartan_un5_quot hf hF ζ
  exact cartanFPF_of_rankTwo (un5System hF ζ) hU (hm D hD).1 (by norm_num) A b
    XD hh hc

open CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F48Rig in
theorem burnsideF48_f431F48_un5 {f : ℕ} (hf : 2 ≤ f) (hm : F431ModelFacts .PSU 5 f) :
    F431F48 .PSU 5 f hm :=
  f431F48_of_model hm (Un.f431Facts45_un5 f hm) (Un.f431Generation_un5 f)
    (fun D _ hD A => burnsideF48_cartanFPF_un5 hf hm D hD A)
    (fun D _ hD A => Un.faithfulOnType_un5 f hm D hD A _)

open CFSG.Quasithin.H13.F431 in
theorem burnsideF48_concl_two_L3 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .L3 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl .L3 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_of_F431 (t := .PSL) (m := 3) (f431ModelFacts_psl3 f)
    (f431Facts45_psl f _) (f431F48_psl f hf _) rfl hyp (burnsideF48_lieModel_L3 hyp.model) hP hY

open CFSG.Quasithin.H13.F431 in
theorem burnsideF48_concl_two_Sp4 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .Sp4 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl .Sp4 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_of_F431 (t := .PSp) (m := 2) (f431ModelFacts_psp f)
    (f431Facts45_psp f _) (f431F48_psp f hf _) rfl hyp (burnsideF48_lieModel_Sp4 hf hyp.model)
    hP hY

open CFSG.Quasithin.H13.F431 in
theorem burnsideF48_concl_two_U4 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .U4 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl .U4 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_of_F431 (t := .PSU) (m := 4) (Un.f431ModelFacts_un f)
    (Un.f431Facts45_un f _) (Un.f431F48_un f hf _) rfl hyp (burnsideF48_lieModel_U4 hyp.model)
    hP hY

open CFSG.Quasithin.H13.F431 in
theorem burnsideF48_concl_two_U5 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .U5 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl .U5 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_of_F431 (t := .PSU) (m := 5) (Un.f431ModelFacts_un5 f)
    (Un.f431Facts45_un5 f _) (burnsideF48_f431F48_un5 hf _) rfl hyp
    (burnsideF48_lieModel_U5 hyp.model) hP hY

section G2

open CFSG.Quasithin.H13.F431 in
theorem burnsideF48_concl_two_G2 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .G2 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl .G2 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_of_F431 (t := .G2) (m := 0) (G2.f431ModelFacts_g2 f)
    (G2.f431Facts45_g2 f _) (G2.F48.f431F48_g2 f _) rfl hyp
    (burnsideF48_lieModel_G2 hf hyp.model) hP hY

end G2

section D4

open CFSG.Quasithin.H13.F431 in
theorem burnsideF48_concl_two_D4tw {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .D4tw 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl .D4tw 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_of_F431 (t := .trialityD4) (m := 0) (D4q.Hex.f431ModelFacts_d4 f)
    (D4q.Hex.f431Facts45_d4 f _) (D4q.F48.f431F48_d4q f hf _) rfl hyp
    (burnsideF48_lieModel_D4 hyp.model) hP hY

end D4

section F4

open CFSG.Quasithin.H13.F431 CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431.TwoF4 in
theorem burnsideF48_concl_two_F4tw {f : ℕ} (hf : 3 ≤ f) (hodd : Odd f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .F4tw 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl .F4tw 2 f Gp M₁ M₂ :=
  let oct : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
      (hK : Nat.card K = 2 ^ (2 * a + 1)), 1 ≤ a → OctInput K a hK :=
    fun K _ _ _ a hK ha => haveI := isSimpleGroup_gm ha hK; octInputOf hK (octRGD2 hK)
  burnsideF48_concl_two_of_F431 (t := .twistedF4) (m := 0) (f431ModelFacts_f4 f)
    (f431Facts45_f4 f oct _) (f431F48_f4 f _ oct (f431Facts45_f4 f oct _) (f431Generation_f4 f))
    rfl hyp (burnsideF48_lieModel_F4 hf hodd hyp.model) hP hY

end F4

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose, reducible] noncomputable def burnsideF48_setting {κ : ChF.GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) : LieSetting.{0, 0} :=
  { α := RankTwoAmalgam.ofSubgroups M₁ M₂
    Yb := ↥(M₁ ⊔ M₂)
    grp := inferInstance
    fin := haveI : Finite E := hyp.finite; inferInstance
    ι := RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl
    hι := RankTwoAmalgam.inclusionCompletion_isFaithful M₁ M₂ (M₁ ⊔ M₂) rfl
    N := Gp.comap (ChF.toE (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl))
    hN := haveI : Gp.Normal := hyp.normal; Subgroup.Normal.comap inferInstance _
    p := p
    hp := hp
    m := κ.m
    hm := hm }

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_isLieExtGroup_of_isExtension_M {κ : ChF.GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) {Ġ : Type} [Group Ġ]
    (hext : (burnsideF48_setting hyp hp hm).IsExtension Ġ) : ChF.IsLieExtGroup Ġ κ p f := by
  set S := burnsideF48_setting hyp hp hm with hSdef
  obtain ⟨ν, hνinj, hνnorm, hνcent, hνdyn⟩ := hext
  let ι₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).Completion ↥(M₁ ⊔ M₂) :=
    RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl
  have hS : S.ι = ι₀ := rfl
  have hinj : Function.Injective (ChF.toE ι₀) := fun a b h =>
    Subtype.ext (Subtype.ext h)
  have hsurj : Function.Surjective (ChF.toE ι₀) := fun e =>
    ⟨⟨⟨e, by rw [hyp.gen]; exact Subgroup.mem_top e⟩, by rw [ι₀.gen]; exact Subgroup.mem_top _⟩,
      rfl⟩
  have hx : ∀ x : ι₀.G0, x ∈ stv ι₀ ι₀.xv ↔ ChF.toE ι₀ x ∈ M₁ := by
    intro x
    rw [stv_xv_eq_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩
  have hl : ∀ x : ι₀.G0, x ∈ stv ι₀ ι₀.lv ↔ ChF.toE ι₀ x ∈ M₂ := by
    intro x
    rw [burnsideF48_mem_stv_lv_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩
  let ρ : ↥S.N →* E := (ChF.toE ι₀).comp S.N.subtype
  have hρinj : Function.Injective ρ := hinj.comp Subtype.val_injective
  have hmemN : ∀ x : ι₀.G0, x ∈ S.N ↔ ChF.toE ι₀ x ∈ Gp := fun x => Iff.rfl
  have hρtop : (⊤ : Subgroup ↥S.N).map ρ = Gp := by
    ext g
    constructor
    · rintro ⟨n, -, rfl⟩
      exact (hmemN n.1).1 n.2
    · intro hg
      obtain ⟨x, hx'⟩ := hsurj g
      exact ⟨⟨x, (hmemN x).2 (hx' ▸ hg)⟩, Subgroup.mem_top _, hx'⟩
  have hρ1 : S.N1.map ρ = Gp ⊓ M₁ := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨(hmemN n.1).1 n.2, (hx n.1).1 hn⟩
    · rintro ⟨hgG, hgM⟩
      obtain ⟨x, hx'⟩ := hsurj g
      exact ⟨⟨x, (hmemN x).2 (hx' ▸ hgG)⟩, (hx x).2 (hx' ▸ hgM), hx'⟩
  have hρ2 : ((stv S.ι S.ι.lv).subgroupOf S.N).map ρ = Gp ⊓ M₂ := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨(hmemN n.1).1 n.2, (hl n.1).1 hn⟩
    · rintro ⟨hgG, hgM⟩
      obtain ⟨x, hx'⟩ := hsurj g
      exact ⟨⟨x, (hmemN x).2 (hx' ▸ hgG)⟩, (hl x).2 (hx' ▸ hgM), hx'⟩
  have hρ12 : S.N12.map ρ = Gp ⊓ (M₁ ⊓ M₂) := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨(hmemN n.1).1 n.2, (hx n.1).1 hn.1, (hl n.1).1 hn.2⟩
    · rintro ⟨hgG, hgM1, hgM2⟩
      obtain ⟨x, hx'⟩ := hsurj g
      exact ⟨⟨x, (hmemN x).2 (hx' ▸ hgG)⟩, ⟨(hx x).2 (hx' ▸ hgM1), (hl x).2 (hx' ▸ hgM2)⟩, hx'⟩
  have hIL : ChF.IsLieParabolics p (⊤ : Subgroup ↥S.N) S.N12 S.N1
      ((stv S.ι S.ι.lv).subgroupOf S.N) := by
    refine burnsideF48_isLieParabolics_of_map ρ hρinj ?_
    rw [hρtop, hρ1, hρ2, hρ12]
    exact hP
  have hIL' := burnsideF48_isLieParabolics_map ν hνinj hIL
  rw [← MonoidHom.range_eq_map] at hIL'
  have hρrange : ρ.range = Gp := by rw [MonoidHom.range_eq_map, hρtop]
  exact ⟨ν.range, burnsideF48_isGenLie_of_equiv
    (((MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)).symm.trans
      (MonoidHom.ofInjective hνinj)) hyp.model, hνnorm, hνcent, S.N12.map ν, S.N1.map ν,
    ((stv S.ι S.ι.lv).subgroupOf S.N).map ν, hIL', hνdyn⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_of_setting_M {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (h45 : (burnsideF48_setting hyp hp hm).Facts45L)
    (h48 : ∀ (Y : Type) [Group Y] [Finite Y] (β : (burnsideF48_setting hyp hp hm).α.Completion Y),
      β.IsFaithful → β.IsSmall κ.m → (burnsideF48_setting hyp hp hm).F48Concl β) :
    ChF.F48Concl κ p f Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Gp.Normal := hyp.normal
  set S := burnsideF48_setting hyp hp hm with hSdef
  haveI hG1 : Finite (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 := inferInstanceAs (Finite ↥M₁)
  haveI hG2 : Finite (RankTwoAmalgam.ofSubgroups M₁ M₂).G2 := inferInstanceAs (Finite ↥M₂)
  have hfin : ∀ (Y : Type) [Group Y] (β : ChF.Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      Finite Y := by
    intro Y _ β hβ hs
    exact burnsideF48_finite_of_small (c := β) (m := κ.m)
      ⟨hβ, h45.thick1, h45.thick2, pathTrans_transfer _ hβ S.ι S.hι (S.m + 1) h45.trans,
        by have := S.hm; exact le_trans (by norm_num) this⟩ hs
  refine ⟨fun Y _ β hβ hs => ?_, fun hGp => ?_⟩
  · haveI := hfin Y β hβ hs
    obtain ⟨⟨Ġ, hĠ, β', hβ', heq, hext⟩, -⟩ := h48 Y β hβ hs
    refine ⟨Ġ, hĠ, β', heq, ?_, ?_⟩
    · exact burnsideF48_isLieExtGroup_of_equiv (burnsideF48_G0Equiv β').symm
        (burnsideF48_isLieExtGroup_of_isExtension_M hyp hp hm hP hext)
    · obtain ⟨φ, -⟩ := heq
      exact ⟨(burnsideF48_G0Equiv β).trans (φ.trans (burnsideF48_G0Equiv β').symm)⟩
  · have hNtop : S.N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      show ChF.toE S.ι x ∈ Gp
      rw [hGp]
      exact Subgroup.mem_top _
    refine ⟨⟨S.Yb, inferInstance, S.ι, S.hι, h45.isSmall_iota, fun Y _ β hβ hs => ?_⟩,
      fun Y _ β hβ hs => ?_⟩
    · haveI := hfin Y β hβ hs
      exact (h48 Y β hβ hs).2 hNtop
    · haveI := hfin Y β hβ hs
      obtain ⟨φ, -, -⟩ := (h48 Y β hβ hs).2 hNtop
      exact ⟨(burnsideF48_G0Equiv β).trans (φ.trans
        ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv))⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_isExtension_M {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m) :
    (burnsideF48_setting hyp hp hm).IsExtension (burnsideF48_setting hyp hp hm).Yb := by
  set S := burnsideF48_setting hyp hp hm with hSdef
  let ι₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).Completion ↥(M₁ ⊔ M₂) :=
    RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl
  let ν : ↥S.N →* S.Yb := (ι₀.φ1.range ⊔ ι₀.φ2.range).subtype.comp S.N.subtype
  have hνinj : Function.Injective ν := Subtype.val_injective.comp Subtype.val_injective
  have hmemN : ∀ x : ι₀.G0, x ∈ S.N ↔ ChF.toE ι₀ x ∈ Gp := fun x => Iff.rfl
  have hx : ∀ x : ι₀.G0, x ∈ stv ι₀ ι₀.xv ↔ ChF.toE ι₀ x ∈ M₁ := by
    intro x
    rw [stv_xv_eq_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩
  have hl : ∀ x : ι₀.G0, x ∈ stv ι₀ ι₀.lv ↔ ChF.toE ι₀ x ∈ M₂ := by
    intro x
    rw [burnsideF48_mem_stv_lv_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩
  have hG0 : ∀ y : S.Yb, y ∈ ι₀.φ1.range ⊔ ι₀.φ2.range := fun y => by
    rw [ι₀.gen]; exact Subgroup.mem_top y
  have hrange : ν.range = Gp.comap (M₁ ⊔ M₂).subtype := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact (hmemN n.1).1 n.2
    · intro hy
      exact ⟨⟨⟨y, hG0 y⟩, hy⟩, rfl⟩
  haveI : Gp.Normal := hyp.normal
  have hN1 : S.N1.map ν = (Gp ⊓ M₁).subgroupOf (M₁ ⊔ M₂) := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨(hmemN n.1).1 n.2, (hx n.1).1 hn⟩
    · intro hy
      exact ⟨⟨⟨y, hG0 y⟩, (hmemN ⟨y, hG0 y⟩).2 hy.1⟩, (hx ⟨y, hG0 y⟩).2 hy.2, rfl⟩
  have hN12 : S.N12.map ν = (Gp ⊓ (M₁ ⊓ M₂)).subgroupOf (M₁ ⊔ M₂) := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨(hmemN n.1).1 n.2, (hx n.1).1 hn.1, (hl n.1).1 hn.2⟩
    · intro hy
      exact ⟨⟨⟨y, hG0 y⟩, (hmemN ⟨y, hG0 y⟩).2 hy.1⟩,
        ⟨(hx ⟨y, hG0 y⟩).2 hy.2.1, (hl ⟨y, hG0 y⟩).2 hy.2.2⟩, rfl⟩
  refine ⟨ν, hνinj, ?_, ?_, ?_⟩
  · rw [hrange]
    exact Subgroup.Normal.comap inferInstance _
  · rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz' : z.1 ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgM : g ∈ M₁ ⊔ M₂ := by rw [hyp.gen]; exact Subgroup.mem_top g
      have hmem : (⟨g, hgM⟩ : ↥(M₁ ⊔ M₂)) ∈ ν.range := by
        rw [hrange]; exact hg
      have := Subgroup.mem_centralizer_iff.1 hz _ hmem
      exact congrArg Subtype.val this
    rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hz'
    exact Subtype.ext hz'
  · intro g hg
    rw [hN12] at hg
    rw [hN1]
    exact (burnsideF48_mem_normalizer_subgroupOf_iff
      ((inf_le_right.trans le_sup_left) : Gp ⊓ M₁ ≤ M₁ ⊔ M₂) g).2 (hyp.dynkin _
        ((burnsideF48_mem_normalizer_subgroupOf_iff
          (((inf_le_right.trans inf_le_left).trans le_sup_left) : Gp ⊓ (M₁ ⊓ M₂) ≤ M₁ ⊔ M₂)
          g).1 hg))

open CFSG.Quasithin CFSG.Quasithin.H13.F48Rig in
theorem burnsideF48_concl_of_cartan {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (h45 : (burnsideF48_setting hyp hp hm).Facts45L)
    (hT : (burnsideF48_setting hyp hp hm).CartanFPF)
    (hF : (burnsideF48_setting hyp hp hm).FaithfulOnType
      (decide (Odd (burnsideF48_setting hyp hp hm).m))) :
    ChF.F48Concl κ p f Gp M₁ M₂ :=
  burnsideF48_concl_of_setting_M hyp hp hm hP h45 fun Y _ _ β hβ hs => by
    obtain ⟨θ, h1, h2⟩ := exists_equiv_small h45 β hβ hs hT hF
    exact f48Concl_of_equiv β θ h1 h2 (burnsideF48_isExtension_M hyp hp hm)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_toE_bijective {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hgen : M₁ ⊔ M₂ = ⊤) :
    Function.Bijective (ChF.toE (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl)) := by
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun e => ?_⟩
  exact ⟨⟨⟨e, by rw [hgen]; exact Subgroup.mem_top e⟩, by
    rw [(RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl).gen]; exact Subgroup.mem_top _⟩,
    rfl⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_stv_xv_iff {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (x : (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl).G0) :
    x ∈ stv (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl)
        (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl).xv ↔
      ChF.toE (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl) x ∈ M₁ := by
  rw [stv_xv_eq_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_stv_lv_iff' {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (x : (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl).G0) :
    x ∈ stv (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl)
        (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl).lv ↔
      ChF.toE (RankTwoAmalgam.inclusionCompletion M₁ M₂ (M₁ ⊔ M₂) rfl) x ∈ M₂ := by
  rw [burnsideF48_mem_stv_lv_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩

theorem burnsideF48_pCoreOf_le_sylow {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {H P S : Subgroup E} (hS : ChF.IsSylowOf p S H) (hSP : S ≤ P) (hPH : P ≤ H) :
    pCoreOf p P ≤ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  have h1 : IsPGroup p (S.subgroupOf P) := hSp.comap_subtype
  have hdvd : S.relIndex P ∣ S.relIndex H :=
    ⟨P.relIndex H, (Subgroup.relIndex_mul_relIndex S P H hSP hPH).symm⟩
  have h2 : ¬ p ∣ (S.subgroupOf P).index := fun h => hSidx (h.trans hdvd)
  let T : Sylow p ↥P := h1.toSylow h2
  have hcore : CFSG.pCore p ↥P ≤ (T : Subgroup ↥P) := by
    haveI : (CFSG.pCore p ↥P).Normal := CFSG.LieType.BorelTits.pCore_normal p
    exact (CFSG.LieType.BorelTits.pCore_isPGroup p).le_sylow_of_normal T
  have h3 : (T : Subgroup ↥P) = S.subgroupOf P := rfl
  rw [h3] at hcore
  have := Subgroup.map_mono (f := P.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this

theorem burnsideF48_pCoreOf_le {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {Gp M₁ M₂ : Subgroup E}
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    pCoreOf p (Gp ⊓ M₁) ≤ M₂ ∧ pCoreOf p (Gp ⊓ M₂) ≤ M₁ := by
  obtain ⟨S, hS, hB⟩ := hP.1
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB]; exact le_inf hS.1 Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  · have hSP : S ≤ Gp ⊓ M₁ := hSB.trans (inf_le_inf_left _ inf_le_left)
    exact (burnsideF48_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_right))
  · have hSP : S ≤ Gp ⊓ M₂ := hSB.trans (inf_le_inf_left _ inf_le_right)
    exact (burnsideF48_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_left))

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_Qbar_xv {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (x : (burnsideF48_setting hyp hp hm).ι.G0) :
    x ∈ (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.xv ↔
      ChF.toE (burnsideF48_setting hyp hp hm).ι x ∈ pCoreOf p (Gp ⊓ M₁) := by
  revert x
  set S := burnsideF48_setting hyp hp hm with hS
  let e : S.ι.G0 ≃* E := MulEquiv.ofBijective (ChF.toE S.ι) (burnsideF48_toE_bijective hyp.gen)
  have hN : ∀ y : S.ι.G0, y ∈ S.N ⊓ stv S.ι S.ι.xv ↔ e y ∈ Gp ⊓ M₁ := fun y =>
    Subgroup.mem_inf.trans ((and_congr (show y ∈ S.N ↔ e y ∈ Gp from Iff.rfl)
      (burnsideF48_mem_stv_xv_iff y)).trans Subgroup.mem_inf.symm)
  have h1 : S.N ⊓ stv S.ι S.ι.xv = (Gp ⊓ M₁).map e.symm.toMonoidHom := by
    ext y
    rw [hN, Subgroup.mem_map_equiv]
    simp
  have h2 : S.Qbar S.ι.xv = (pCoreOf p (Gp ⊓ M₁)).map e.symm.toMonoidHom := by
    unfold LieSetting.Qbar
    show pCoreOf p (S.N ⊓ stv S.ι S.ι.xv) = _
    rw [h1]
    exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p e.symm _
  intro x
  show x ∈ S.Qbar S.ι.xv ↔ e x ∈ pCoreOf p (Gp ⊓ M₁)
  rw [h2, Subgroup.mem_map_equiv]
  simp

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_Qbar_lv {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (x : (burnsideF48_setting hyp hp hm).ι.G0) :
    x ∈ (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.lv ↔
      ChF.toE (burnsideF48_setting hyp hp hm).ι x ∈ pCoreOf p (Gp ⊓ M₂) := by
  revert x
  set S := burnsideF48_setting hyp hp hm with hS
  let e : S.ι.G0 ≃* E := MulEquiv.ofBijective (ChF.toE S.ι) (burnsideF48_toE_bijective hyp.gen)
  have hN : ∀ y : S.ι.G0, y ∈ S.N ⊓ stv S.ι S.ι.lv ↔ e y ∈ Gp ⊓ M₂ := fun y =>
    Subgroup.mem_inf.trans ((and_congr (show y ∈ S.N ↔ e y ∈ Gp from Iff.rfl)
      (burnsideF48_mem_stv_lv_iff' y)).trans Subgroup.mem_inf.symm)
  have h1 : S.N ⊓ stv S.ι S.ι.lv = (Gp ⊓ M₂).map e.symm.toMonoidHom := by
    ext y
    rw [hN, Subgroup.mem_map_equiv]
    simp
  have h2 : S.Qbar S.ι.lv = (pCoreOf p (Gp ⊓ M₂)).map e.symm.toMonoidHom := by
    unfold LieSetting.Qbar
    show pCoreOf p (S.N ⊓ stv S.ι S.ι.lv) = _
    rw [h1]
    exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p e.symm _
  intro x
  show x ∈ S.Qbar S.ι.lv ↔ e x ∈ pCoreOf p (Gp ⊓ M₂)
  rw [h2, Subgroup.mem_map_equiv]
  simp

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_Qx_eq_Qbar {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m) :
    ChF.Qx (M₁ := M₁) (M₂ := M₂) p Gp (burnsideF48_setting hyp hp hm).ι =
      (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.xv := by
  ext x
  refine Iff.trans ?_ (burnsideF48_mem_Qbar_xv hyp hp hm x).symm
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp ha
  · intro hx
    have hxM : ChF.toE (burnsideF48_setting hyp hp hm).ι x ∈ M₁ :=
      ((CFSG.LieType.BorelTits.pCoreOf_le p _) hx).2
    have hx' := (burnsideF48_mem_stv_xv_iff (M₁ := M₁) (M₂ := M₂) x).2 hxM
    rw [stv_xv_eq_range] at hx'
    obtain ⟨a, rfl⟩ := hx'
    exact ⟨a, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_Ql_eq_Qbar {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m) :
    ChF.Ql (M₁ := M₁) (M₂ := M₂) p Gp (burnsideF48_setting hyp hp hm).ι =
      (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.lv := by
  ext x
  refine Iff.trans ?_ (burnsideF48_mem_Qbar_lv hyp hp hm x).symm
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp ha
  · intro hx
    have hxM : ChF.toE (burnsideF48_setting hyp hp hm).ι x ∈ M₂ :=
      ((CFSG.LieType.BorelTits.pCoreOf_le p _) hx).2
    have hx' := (burnsideF48_mem_stv_lv_iff' (M₁ := M₁) (M₂ := M₂) x).2 hxM
    rw [burnsideF48_mem_stv_lv_iff] at hx'
    obtain ⟨a, rfl⟩ := hx'
    exact ⟨a, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_Qvert_eq_of_equivariant {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (Q : c.Γ → Subgroup c.G0)
    (hQ : ∀ (g : c.G0) (v : c.Γ), Q (g • v) = conjSub g (Q v)) (u : c.Γ) :
    c.Qvert (Q c.xv) (Q c.lv) u = Q u := by
  have hb : ∀ b : Bool, cond b (Q c.lv) (Q c.xv) = Q (c.baseVert b) := by
    intro b
    cases b <;> rfl
  have hterm : ∀ g : c.G0, g • c.baseVert (CosetGeom.vtype u) = u →
      conjSub g (cond (CosetGeom.vtype u) (Q c.lv) (Q c.xv)) = Q u := by
    intro g hg
    rw [hb, ← hQ, hg]
  obtain ⟨g0, hg0⟩ := exists_smul_eq_baseVert c u
  unfold Completion.Qvert
  exact le_antisymm (iSup₂_le fun g hg => (hterm g hg).le)
    ((hterm g0 hg0).ge.trans (le_iSup₂ (f := fun (g : c.G0)
      (_ : g • c.baseVert (CosetGeom.vtype u) = u) =>
        conjSub g (cond (CosetGeom.vtype u) (Q c.lv) (Q c.xv))) g0 hg0))

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_Qu_eq_Qbar {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (u : (burnsideF48_setting hyp hp hm).ι.Γ) :
    ChF.Qu (M₁ := M₁) (M₂ := M₂) p Gp (burnsideF48_setting hyp hp hm).ι u =
      (burnsideF48_setting hyp hp hm).Qbar u := by
  have h := burnsideF48_Qvert_eq_of_equivariant (burnsideF48_setting hyp hp hm).ι
    (burnsideF48_setting hyp hp hm).Qbar
    (fun g v => (burnsideF48_setting hyp hp hm).Qbar_smul g v) u
  rw [← burnsideF48_Qx_eq_Qbar hyp hp hm, ← burnsideF48_Ql_eq_Qbar hyp hp hm] at h
  exact h

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_Qbar_xv_le_stv {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {w : (burnsideF48_setting hyp hp hm).ι.Γ}
    (hw : (burnsideF48_setting hyp hp hm).ι.graph.Adj (burnsideF48_setting hyp hp hm).ι.xv w) :
    (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.xv ≤
      stv (burnsideF48_setting hyp hp hm).ι w := by
  haveI : Finite E := hyp.finite
  have hcore := (burnsideF48_pCoreOf_le hp hP).1
  have hlv : (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.xv ≤
      stv (burnsideF48_setting hyp hp hm).ι (burnsideF48_setting hyp hp hm).ι.lv := fun x hx =>
    (burnsideF48_mem_stv_lv_iff' x).2 (hcore ((burnsideF48_mem_Qbar_xv hyp hp hm x).1 hx))
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq CosetGeom.adj_γ₀_γ₁ hw
  have hgx : g ∈ stv (burnsideF48_setting hyp hp hm).ι (burnsideF48_setting hyp hp hm).ι.xv :=
    MulAction.mem_stabilizer_iff.mpr hg1
  rw [← hg2, stv_smul]
  have := conjSub_mono g hlv
  rwa [(burnsideF48_setting hyp hp hm).conjSub_Qbar hgx] at this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_Qbar_lv_le_stv {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {w : (burnsideF48_setting hyp hp hm).ι.Γ}
    (hw : (burnsideF48_setting hyp hp hm).ι.graph.Adj (burnsideF48_setting hyp hp hm).ι.lv w) :
    (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.lv ≤
      stv (burnsideF48_setting hyp hp hm).ι w := by
  haveI : Finite E := hyp.finite
  have hcore := (burnsideF48_pCoreOf_le hp hP).2
  have hxv : (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.lv ≤
      stv (burnsideF48_setting hyp hp hm).ι (burnsideF48_setting hyp hp hm).ι.xv := fun x hx =>
    (burnsideF48_mem_stv_xv_iff x).2 (hcore ((burnsideF48_mem_Qbar_lv hyp hp hm x).1 hx))
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq CosetGeom.adj_γ₀_γ₁.symm hw
  have hgl : g ∈ stv (burnsideF48_setting hyp hp hm).ι (burnsideF48_setting hyp hp hm).ι.lv :=
    MulAction.mem_stabilizer_iff.mpr hg1
  rw [← hg2, stv_smul]
  have := conjSub_mono g hxv
  rwa [(burnsideF48_setting hyp hp hm).conjSub_Qbar hgl] at this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_facts45L_of_F45 (hF : F_4_5) {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie) (hp : p.Prime)
    (hm : 3 ≤ κ.m)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    (burnsideF48_setting hyp hp hm).Facts45L := by
  haveI : Finite E := hyp.finite
  obtain ⟨hpoly, -, -, -, h5, -, h7, -, -⟩ :=
    hF κ p f E Gp M₁ M₂ hyp (burnsideF48_setting hyp hp hm).ι rfl
  have hext : ChF.IsLieExtAmalgam M₁ M₂ := ⟨κ, p, f, Gp, hκ, hyp⟩
  have hthick := ChF.burnsideF4a_thick hp hP
  refine LieSetting.Facts45L.ofBase (burnsideF48_setting hyp hp hm) hthick.1 hthick.2 hpoly
    (h7 hext _) (h7 hext _) ?_ ?_ (fun w hw => burnsideF48_Qbar_xv_le_stv hyp hp hm hP hw)
    (fun w hw => burnsideF48_Qbar_lv_le_stv hyp hp hm hP hw)
  · intro v hv
    have := (h5 hext _ v hv).1
    rwa [burnsideF48_Qu_eq_Qbar hyp hp hm] at this
  · intro v hv
    have := (h5 hext _ v hv).1
    rwa [burnsideF48_Qu_eq_Qbar hyp hp hm] at this

theorem burnsideF48_eq_one_of_conj_mem {E : Type} [Group E] {Gp Ms : Subgroup E} [hN : Gp.Normal]
    (hsimple : IsSimpleGroup ↥Gp) (hC : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hGp : ¬ Gp ≤ Ms) {k : E} (hk : ∀ g : E, g⁻¹ * k * g ∈ Ms) : k = 1 := by
  haveI : IsSimpleGroup ↥Gp := hsimple
  have hcore : (Ms.subgroupOf Gp).normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Ms.subgroupOf Gp).normalCore with h | h
    · exact h
    · exfalso
      refine hGp fun x hx => ?_
      have h1 := Subgroup.normalCore_le (Ms.subgroupOf Gp)
        (show (⟨x, hx⟩ : ↥Gp) ∈ (Ms.subgroupOf Gp).normalCore by rw [h]; exact Subgroup.mem_top _)
      exact h1
  have hcomm : ∀ g ∈ Gp, g * k = k * g := by
    intro g hg
    have hmem : (⟨k * g * k⁻¹ * g⁻¹, by
        have h1 : k * g * k⁻¹ ∈ Gp := hN.conj_mem g hg k
        exact Gp.mul_mem h1 (Gp.inv_mem hg)⟩ : ↥Gp) ∈ (Ms.subgroupOf Gp).normalCore := by
      intro b
      show (b : E) * (k * g * k⁻¹ * g⁻¹) * (b : E)⁻¹ ∈ Ms
      have e1 : (b : E) * (k * g * k⁻¹ * g⁻¹) * (b : E)⁻¹ =
          ((b : E) * k * (b : E)⁻¹) * (((b : E) * g) * k⁻¹ * ((b : E) * g)⁻¹) := by group
      rw [e1]
      refine Ms.mul_mem ?_ ?_
      · have := hk (b : E)⁻¹
        simpa using this
      · have h2 := hk (((b : E) * g)⁻¹)
        have h3 := Ms.inv_mem h2
        have e2 : (((((b : E) * g)⁻¹)⁻¹ * k * ((b : E) * g)⁻¹))⁻¹ =
            ((b : E) * g) * k⁻¹ * ((b : E) * g)⁻¹ := by group
        rwa [e2] at h3
    rw [hcore, Subgroup.mem_bot] at hmem
    have h4 : k * g * k⁻¹ * g⁻¹ = 1 := congrArg Subtype.val hmem
    have h5 : k * g = g * k := by
      calc k * g = (k * g * k⁻¹ * g⁻¹) * (g * k) := by group
        _ = g * k := by rw [h4, one_mul]
    exact h5.symm
  have : k ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hcomm
  rw [hC, Subgroup.mem_bot] at this
  exact this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_eq_one_of_fixes_type {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {E : Type} [Group E] (e : c.G0 ≃* E) (s : Bool) (Ms : Subgroup E)
    (hstab : ∀ x : c.G0, x ∈ stv c (c.baseVert s) ↔ e x ∈ Ms)
    (hconj : ∀ k' : E, (∀ g : E, g⁻¹ * k' * g ∈ Ms) → k' = 1) (k : c.G0)
    (hk : ∀ v : c.Γ, CosetGeom.vtype v = s → k • v = v) : k = 1 := by
  have h1 : e k = 1 := by
    refine hconj _ fun g => ?_
    have hv : CosetGeom.vtype (e.symm g • c.baseVert s) = s := by
      rw [CosetGeom.vtype_smul, vtype_baseVert]
    have hfix := hk _ hv
    have hmem : (e.symm g)⁻¹ * k * e.symm g ∈ stv c (c.baseVert s) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hfix, inv_smul_smul]
    have := (hstab _).1 hmem
    simpa [map_mul, map_inv] using this
  exact e.injective (by rw [h1, map_one])

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_faithfulOnType_of_simple {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hsimple : IsSimpleGroup ↥Gp)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) (s : Bool) :
    (burnsideF48_setting hyp hp hm).FaithfulOnType s := by
  haveI : Gp.Normal := hyp.normal
  let e : (burnsideF48_setting hyp hp hm).ι.G0 ≃* E :=
    MulEquiv.ofBijective (ChF.toE (burnsideF48_setting hyp hp hm).ι)
      (burnsideF48_toE_bijective hyp.gen)
  have hnle : ¬ Gp ≤ cond s M₂ M₁ := by
    intro hle
    cases s
    · exact ((hP.2.2.2 (Gp ⊓ M₁)).2 (Or.inl rfl)).2.2.1 (inf_eq_left.2 hle)
    · exact ((hP.2.2.2 (Gp ⊓ M₂)).2 (Or.inr rfl)).2.2.1 (inf_eq_left.2 hle)
  refine burnsideF48_eq_one_of_fixes_type (burnsideF48_setting hyp hp hm).ι e s (cond s M₂ M₁)
    ?_ (fun k' hk' => burnsideF48_eq_one_of_conj_mem hsimple hyp.centralizer_trivial hnle hk') 
  intro x
  cases s
  · exact burnsideF48_mem_stv_xv_iff x
  · exact burnsideF48_mem_stv_lv_iff' x

theorem burnsideF48_three_le_m (κ : ChF.GLKind) : 3 ≤ κ.m := by
  cases κ <;> decide

theorem burnsideF48_concl_of_F45_cartan (hF : F_4_5) {κ : ChF.GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie)
    (hsimple : IsSimpleGroup ↥Gp)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hT : (burnsideF48_setting hyp (ChF.burnsideF4a_prime_of_isGenLie hyp.model)
      (burnsideF48_three_le_m κ)).CartanFPF) :
    ChF.F48Concl κ p f Gp M₁ M₂ :=
  burnsideF48_concl_of_cartan hyp (ChF.burnsideF4a_prime_of_isGenLie hyp.model)
    (burnsideF48_three_le_m κ) hP
    (burnsideF48_facts45L_of_F45 hF hyp hκ (ChF.burnsideF4a_prime_of_isGenLie hyp.model)
      (burnsideF48_three_le_m κ) hP)
    hT
    (burnsideF48_faithfulOnType_of_simple hyp (ChF.burnsideF4a_prime_of_isGenLie hyp.model)
      (burnsideF48_three_le_m κ) hsimple hP _)

section

theorem burnsideF48_concl_two_ge4 {κ : ChF.GLKind} {f : ℕ} (hf : 2 ≤ f)
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂)
    (hP : ChF.IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hY : burnsideF48_YamPair Gp M₁ M₂) : ChF.F48Concl κ 2 f Gp M₁ M₂ := by
  cases κ
  · exact burnsideF48_concl_two_L3 hf hyp hP hY
  · exact burnsideF48_concl_two_Sp4 hf hyp hP hY
  · exact burnsideF48_concl_two_G2 hf hyp hP hY
  · exact burnsideF48_concl_two_D4tw hf hyp hP hY
  · obtain ⟨-, hodd, h | h⟩ := hyp.model
    · omega
    · exact burnsideF48_concl_two_F4tw h.1 hodd hyp hP hY
  · exact burnsideF48_concl_two_U4 hf hyp hP hY
  · exact burnsideF48_concl_two_U5 hf hyp hP hY
  · obtain ⟨-, hf1, -⟩ := hyp.model
    omega
  · obtain ⟨-, hf1, -⟩ := hyp.model
    omega

end

theorem burnsideF48_dist_even_iff {V : Type*} (Γ : SimpleGraph V) (c : V → Bool)
    (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) (hconn : Γ.Connected) (u v : V) :
    Even (Γ.dist u v) ↔ c u = c v := by
  have key : ∀ (u v : V) (p : Γ.Walk u v), Even p.length ↔ c u = c v := by
    intro u v p
    induction p with
    | nil => simp
    | cons h p ih =>
      rename_i a w z
      rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
      have := hc _ _ h
      cases hca : c a <;> cases hcw : c w <;> cases hcz : c z <;> simp_all
  obtain ⟨p, hp⟩ := (hconn.preconnected u v).exists_walk_length_eq_dist
  rw [← hp]
  exact key u v p

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_adj_xv_lv_iff {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (a b : c.G0) :
    c.graph.Adj (a • c.xv) (b • c.lv) ↔
      ∃ k ∈ stv c c.xv, ∃ l ∈ stv c c.lv, a⁻¹ * b = k * l := by
  constructor
  · intro h
    have h1 : c.graph.Adj c.xv ((a⁻¹ * b) • c.lv) := by
      have := (CosetGeom.smul_adj a⁻¹).mpr h
      rwa [inv_smul_smul, ← mul_smul] at this
    obtain ⟨k, hk1, hk2⟩ := CosetGeom.exists_stab_smul_eq CosetGeom.adj_γ₀_γ₁ h1
    refine ⟨k, MulAction.mem_stabilizer_iff.2 hk1, k⁻¹ * (a⁻¹ * b), ?_, by group⟩
    show (k⁻¹ * (a⁻¹ * b)) • c.lv = c.lv
    rw [mul_smul, ← hk2, inv_smul_smul]
  · rintro ⟨k, hk, l, hl, hkl⟩
    have hk' : k • c.xv = c.xv := MulAction.mem_stabilizer_iff.1 hk
    have hl' : l • c.lv = c.lv := MulAction.mem_stabilizer_iff.1 hl
    have hb : b = a * (k * l) := by rw [← hkl]; group
    have h1 : c.graph.Adj c.xv ((k * l) • c.lv) := by
      rw [mul_smul, hl']
      have := (CosetGeom.smul_adj k).mpr (CosetGeom.adj_γ₀_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range)
        (G₁ := c.φ1.range) (G₂ := c.φ2.range))
      rwa [hk'] at this
    have := (CosetGeom.smul_adj a).mpr h1
    rw [← mul_smul] at this
    rw [hb]
    exact this

theorem burnsideF48_exists_mid {V : Type*} (Γ : SimpleGraph V) {u v : V} (h : Γ.dist u v = 2) :
    ∃ z, Γ.Adj u z ∧ Γ.Adj z v := by
  have hr : Γ.Reachable u v := by
    by_contra h'
    rw [SimpleGraph.dist_eq_zero_of_not_reachable h'] at h
    omega
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [h] at hp
  rcases p with _ | ⟨hu, p'⟩
  · simp at hp
  · rename_i z
    rcases p' with _ | ⟨hv, p''⟩
    · simp at hp
    · rcases p'' with _ | ⟨_, _⟩
      · exact ⟨z, hu, hv⟩
      · simp at hp

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_dist_xv_lv_eq_three {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hpoly : IsGenPolygon c.graph 3) (a b : c.G0)
    (hab : ¬ ∃ k ∈ stv c c.xv, ∃ l ∈ stv c c.lv, a⁻¹ * b = k * l) :
    c.graph.dist (a • c.xv) (b • c.lv) = 3 := by
  have hle := hpoly.diam_le (a • c.xv) (b • c.lv)
  have hx : CosetGeom.vtype c.xv = false := rfl
  have hl : CosetGeom.vtype c.lv = true := rfl
  have hodd : ¬ Even (c.graph.dist (a • c.xv) (b • c.lv)) := by
    rw [burnsideF48_dist_even_iff c.graph CosetGeom.vtype
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) hpoly.connected, CosetGeom.vtype_smul,
      CosetGeom.vtype_smul, hx, hl]
    simp
  have hne1 : c.graph.dist (a • c.xv) (b • c.lv) ≠ 1 := fun h1 =>
    hab ((burnsideF48_adj_xv_lv_iff c a b).1 (SimpleGraph.dist_eq_one_iff_adj.1 h1))
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨n, hn⟩ := hodd
  omega

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_dist_xv_xv_eq_four {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hpoly : IsGenPolygon c.graph 4) (a b : c.G0)
    (hab : ¬ ∃ k ∈ stv c c.xv, ∃ l ∈ stv c c.lv, ∃ k' ∈ stv c c.xv, a⁻¹ * b = k * l * k') :
    c.graph.dist (a • c.xv) (b • c.xv) = 4 := by
  have hle := hpoly.diam_le (a • c.xv) (b • c.xv)
  have hx : CosetGeom.vtype c.xv = false := rfl
  have heven : Even (c.graph.dist (a • c.xv) (b • c.xv)) := by
    rw [burnsideF48_dist_even_iff c.graph CosetGeom.vtype
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) hpoly.connected, CosetGeom.vtype_smul,
      CosetGeom.vtype_smul]
  have hne0 : c.graph.dist (a • c.xv) (b • c.xv) ≠ 0 := by
    intro h0
    have := (hpoly.connected.dist_eq_zero_iff).1 h0
    refine hab ⟨a⁻¹ * b, ?_, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← this, inv_smul_smul]
  have hne2 : c.graph.dist (a • c.xv) (b • c.xv) ≠ 2 := by
    intro h2
    obtain ⟨z, h1, h2'⟩ := burnsideF48_exists_mid c.graph h2
    have hz : CosetGeom.vtype z = true := by
      have := CosetGeom.vtype_ne_of_adj h1
      rw [CosetGeom.vtype_smul, hx] at this
      revert this
      cases hzt : CosetGeom.vtype z <;> simp
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hz
    obtain ⟨k₁, hk₁, l₁, hl₁, e₁⟩ := (burnsideF48_adj_xv_lv_iff c a g).1 h1
    obtain ⟨k₂, hk₂, l₂, hl₂, e₂⟩ := (burnsideF48_adj_xv_lv_iff c b g).1 h2'.symm
    refine hab ⟨k₁, hk₁, l₁ * l₂⁻¹, (stv c c.lv).mul_mem hl₁ ((stv c c.lv).inv_mem hl₂), k₂⁻¹,
      (stv c c.xv).inv_mem hk₂, ?_⟩
    calc a⁻¹ * b = (a⁻¹ * g) * (b⁻¹ * g)⁻¹ := by group
      _ = k₁ * l₁ * (k₂ * l₂)⁻¹ := by rw [e₁, e₂]
      _ = k₁ * (l₁ * l₂⁻¹) * k₂⁻¹ := by group
  rw [Nat.even_iff] at heven
  omega

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartan_shape {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {E : Type} [Group E] (e : c.G0 ≃* E) (M₁ M₂ : Subgroup E)
    (hx : ∀ x : c.G0, x ∈ stv c c.xv ↔ e x ∈ M₁) (hl : ∀ x : c.G0, x ∈ stv c c.lv ↔ e x ∈ M₂)
    (m : ℕ) (Q : Subgroup c.G0) (n h : E) (hn1 : n ∈ M₁) (hn2 : n ∉ M₂) (hh1 : h ∈ M₁)
    (hh2 : h ∈ M₂) (hh3 : n⁻¹ * h * n ∈ M₂) (b : c.Γ) (hb : c.graph.dist c.xv b = m)
    (hhb : e.symm h • b = b) (hQ : ∀ q ∈ Q, e.symm h * q * (e.symm h)⁻¹ = q → q = 1) :
    ∃ b u₁ u₂ : c.Γ, c.graph.dist c.xv b = m ∧ c.graph.Adj c.xv u₁ ∧ c.graph.Adj c.xv u₂ ∧
      u₁ ≠ u₂ ∧ ∃ h : c.G0, h • c.xv = c.xv ∧ h • b = b ∧ h • u₁ = u₁ ∧ h • u₂ = u₂ ∧
        ∀ q ∈ Q, h * q * h⁻¹ = q → q = 1 := by
  have hn1' : e.symm n ∈ stv c c.xv := (hx _).2 (by simpa using hn1)
  have hn2' : e.symm n ∉ stv c c.lv := fun h' => hn2 (by simpa using (hl _).1 h')
  have hh1' : e.symm h ∈ stv c c.xv := (hx _).2 (by simpa using hh1)
  have hh2' : e.symm h ∈ stv c c.lv := (hl _).2 (by simpa using hh2)
  have hh3' : (e.symm n)⁻¹ * e.symm h * e.symm n ∈ stv c c.lv := by
    refine (hl _).2 ?_
    simpa [map_mul, map_inv] using hh3
  refine ⟨b, c.lv, e.symm n • c.lv, hb, CosetGeom.adj_γ₀_γ₁, ?_, ?_, e.symm h,
    MulAction.mem_stabilizer_iff.1 hh1', hhb, MulAction.mem_stabilizer_iff.1 hh2', ?_, hQ⟩
  · have := (CosetGeom.smul_adj (e.symm n)).mpr (CosetGeom.adj_γ₀_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range)
      (G₁ := c.φ1.range) (G₂ := c.φ2.range))
    rwa [MulAction.mem_stabilizer_iff.1 hn1'] at this
  · intro heq
    apply hn2'
    rw [MulAction.mem_stabilizer_iff]
    exact heq.symm
  · rw [← mul_smul, show e.symm h * e.symm n = e.symm n * ((e.symm n)⁻¹ * e.symm h * e.symm n) by
      group, mul_smul, MulAction.mem_stabilizer_iff.1 hh3']

@[expose] noncomputable def burnsideF48_toEquiv {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) : (burnsideF48_setting hyp hp hm).ι.G0 ≃* E :=
  MulEquiv.ofBijective (ChF.toE (burnsideF48_setting hyp hp hm).ι)
    (burnsideF48_toE_bijective hyp.gen)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_stv_xv_equiv {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (x : (burnsideF48_setting hyp hp hm).ι.G0) :
    x ∈ stv (burnsideF48_setting hyp hp hm).ι (burnsideF48_setting hyp hp hm).ι.xv ↔
      burnsideF48_toEquiv hyp hp hm x ∈ M₁ :=
  burnsideF48_mem_stv_xv_iff x

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_mem_stv_lv_equiv {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (x : (burnsideF48_setting hyp hp hm).ι.G0) :
    x ∈ stv (burnsideF48_setting hyp hp hm).ι (burnsideF48_setting hyp hp hm).ι.lv ↔
      burnsideF48_toEquiv hyp hp hm x ∈ M₂ :=
  burnsideF48_mem_stv_lv_iff' x

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartan_three {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {E : Type} [Group E] (e : c.G0 ≃* E) (M₁ M₂ : Subgroup E)
    (hx : ∀ x : c.G0, x ∈ stv c c.xv ↔ e x ∈ M₁) (hl : ∀ x : c.G0, x ∈ stv c c.lv ↔ e x ∈ M₂)
    (hpoly : IsGenPolygon c.graph 3) (Q : Subgroup c.G0) (n w h : E) (hn1 : n ∈ M₁)
    (hn2 : n ∉ M₂) (hh1 : h ∈ M₁) (hh2 : h ∈ M₂) (hh3 : n⁻¹ * h * n ∈ M₂)
    (hh4 : w⁻¹ * h * w ∈ M₂) (hw : ¬ ∃ k ∈ M₁, ∃ l ∈ M₂, w = k * l)
    (hQ : ∀ q ∈ Q, e.symm h * q * (e.symm h)⁻¹ = q → q = 1) :
    ∃ b u₁ u₂ : c.Γ, c.graph.dist c.xv b = 3 ∧ c.graph.Adj c.xv u₁ ∧ c.graph.Adj c.xv u₂ ∧
      u₁ ≠ u₂ ∧ ∃ h : c.G0, h • c.xv = c.xv ∧ h • b = b ∧ h • u₁ = u₁ ∧ h • u₂ = u₂ ∧
        ∀ q ∈ Q, h * q * h⁻¹ = q → q = 1 := by
  have hdist : c.graph.dist c.xv (e.symm w • c.lv) = 3 := by
    have := burnsideF48_dist_xv_lv_eq_three c hpoly 1 (e.symm w) (by
      rintro ⟨k, hk, l, hl', hkl⟩
      refine hw ⟨e k, (hx k).1 hk, e l, (hl l).1 hl', ?_⟩
      have := congrArg e hkl
      simpa [map_mul] using this)
    rwa [one_smul] at this
  have hhb : e.symm h • (e.symm w • c.lv) = e.symm w • c.lv := by
    have : (e.symm w)⁻¹ * e.symm h * e.symm w ∈ stv c c.lv := (hl _).2 (by simpa [map_mul, map_inv] using hh4)
    rw [← mul_smul, show e.symm h * e.symm w = e.symm w * ((e.symm w)⁻¹ * e.symm h * e.symm w) by
      group, mul_smul, MulAction.mem_stabilizer_iff.1 this]
  exact burnsideF48_cartan_shape c e M₁ M₂ hx hl 3 Q n h hn1 hn2 hh1 hh2 hh3 _ hdist hhb hQ

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartan_four {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {E : Type} [Group E] (e : c.G0 ≃* E) (M₁ M₂ : Subgroup E)
    (hx : ∀ x : c.G0, x ∈ stv c c.xv ↔ e x ∈ M₁) (hl : ∀ x : c.G0, x ∈ stv c c.lv ↔ e x ∈ M₂)
    (hpoly : IsGenPolygon c.graph 4) (Q : Subgroup c.G0) (n w h : E) (hn1 : n ∈ M₁)
    (hn2 : n ∉ M₂) (hh1 : h ∈ M₁) (hh2 : h ∈ M₂) (hh3 : n⁻¹ * h * n ∈ M₂)
    (hh4 : w⁻¹ * h * w ∈ M₁) (hw : ¬ ∃ k ∈ M₁, ∃ l ∈ M₂, ∃ k' ∈ M₁, w = k * l * k')
    (hQ : ∀ q ∈ Q, e.symm h * q * (e.symm h)⁻¹ = q → q = 1) :
    ∃ b u₁ u₂ : c.Γ, c.graph.dist c.xv b = 4 ∧ c.graph.Adj c.xv u₁ ∧ c.graph.Adj c.xv u₂ ∧
      u₁ ≠ u₂ ∧ ∃ h : c.G0, h • c.xv = c.xv ∧ h • b = b ∧ h • u₁ = u₁ ∧ h • u₂ = u₂ ∧
        ∀ q ∈ Q, h * q * h⁻¹ = q → q = 1 := by
  have hdist : c.graph.dist c.xv (e.symm w • c.xv) = 4 := by
    have := burnsideF48_dist_xv_xv_eq_four c hpoly 1 (e.symm w) (by
      rintro ⟨k, hk, l, hl', k', hk', hkl⟩
      refine hw ⟨e k, (hx k).1 hk, e l, (hl l).1 hl', e k', (hx k').1 hk', ?_⟩
      have := congrArg e hkl
      simpa [map_mul] using this)
    rwa [one_smul] at this
  have hhb : e.symm h • (e.symm w • c.xv) = e.symm w • c.xv := by
    have : (e.symm w)⁻¹ * e.symm h * e.symm w ∈ stv c c.xv := (hx _).2 (by simpa [map_mul, map_inv] using hh4)
    rw [← mul_smul, show e.symm h * e.symm w = e.symm w * ((e.symm w)⁻¹ * e.symm h * e.symm w) by
      group, mul_smul, MulAction.mem_stabilizer_iff.1 this]
  exact burnsideF48_cartan_shape c e M₁ M₂ hx hl 4 Q n h hn1 hn2 hh1 hh2 hh3 _ hdist hhb hQ

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_qbar_centralizer {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (h : E)
    (hQ : ∀ q ∈ pCoreOf p (Gp ⊓ M₁), h * q * h⁻¹ = q → q = 1) :
    ∀ q ∈ (burnsideF48_setting hyp hp hm).Qbar (burnsideF48_setting hyp hp hm).ι.xv,
      (burnsideF48_toEquiv hyp hp hm).symm h * q * ((burnsideF48_toEquiv hyp hp hm).symm h)⁻¹ = q →
        q = 1 := by
  intro q hq hqc
  have hq' := (burnsideF48_mem_Qbar_xv hyp hp hm q).1 hq
  have h1 : h * (ChF.toE (burnsideF48_setting hyp hp hm).ι q) * h⁻¹ =
      ChF.toE (burnsideF48_setting hyp hp hm).ι q := by
    have := congrArg (burnsideF48_toEquiv hyp hp hm) hqc
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at this
    exact this
  have h2 := hQ _ hq' h1
  exact (burnsideF48_toE_bijective hyp.gen).1 (by rw [h2, map_one])

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_three {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hκ : κ.m = 3)
    (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 3) (n w h : E)
    (hn1 : n ∈ M₁) (hn2 : n ∉ M₂) (hh1 : h ∈ M₁) (hh2 : h ∈ M₂) (hh3 : n⁻¹ * h * n ∈ M₂)
    (hh4 : w⁻¹ * h * w ∈ M₂) (hw : ¬ ∃ k ∈ M₁, ∃ l ∈ M₂, w = k * l)
    (hQ : ∀ q ∈ pCoreOf p (Gp ⊓ M₁), h * q * h⁻¹ = q → q = 1) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  obtain ⟨b, u₁, u₂, hb, h1, h2, hne, g, hg⟩ := burnsideF48_cartan_three
    (burnsideF48_setting hyp hp hm).ι (burnsideF48_toEquiv hyp hp hm) M₁ M₂
    (burnsideF48_mem_stv_xv_equiv hyp hp hm) (burnsideF48_mem_stv_lv_equiv hyp hp hm) hpoly _ n w h
    hn1 hn2 hh1 hh2 hh3 hh4 hw (burnsideF48_qbar_centralizer hyp hp hm h hQ)
  exact ⟨b, u₁, u₂, hb.trans hκ.symm, h1, h2, hne, g, hg⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_four {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hκ : κ.m = 4)
    (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 4) (n w h : E)
    (hn1 : n ∈ M₁) (hn2 : n ∉ M₂) (hh1 : h ∈ M₁) (hh2 : h ∈ M₂) (hh3 : n⁻¹ * h * n ∈ M₂)
    (hh4 : w⁻¹ * h * w ∈ M₁) (hw : ¬ ∃ k ∈ M₁, ∃ l ∈ M₂, ∃ k' ∈ M₁, w = k * l * k')
    (hQ : ∀ q ∈ pCoreOf p (Gp ⊓ M₁), h * q * h⁻¹ = q → q = 1) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  obtain ⟨b, u₁, u₂, hb, h1, h2, hne, g, hg⟩ := burnsideF48_cartan_four
    (burnsideF48_setting hyp hp hm).ι (burnsideF48_toEquiv hyp hp hm) M₁ M₂
    (burnsideF48_mem_stv_xv_equiv hyp hp hm) (burnsideF48_mem_stv_lv_equiv hyp hp hm) hpoly _ n w h
    hn1 hn2 hh1 hh2 hh3 hh4 hw (burnsideF48_qbar_centralizer hyp hp hm h hQ)
  exact ⟨b, u₁, u₂, hb.trans hκ.symm, h1, h2, hne, g, hg⟩

theorem burnsideF48_marking {c : ChF.ClassicalRoots.Kind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (h : ChF.HypF_4_4g (ChF.classicalKind c) p f Gp M₁ M₂) :
    ∃ marking : ChF.ClassicalRoots.Marking c p f Gp,
      M₁.subgroupOf Gp = marking.parabolic false ∧ M₂.subgroupOf Gp = marking.parabolic true := by
  obtain ⟨chart, -, hpts, hlines⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · have hc : c' = c := by
      cases c <;> cases c' <;> first | rfl | exact absurd hk (by decide)
    subst hc
    refine ⟨marking, ?_, ?_⟩
    · have : Gp ⊓ M₁ = (marking.parabolic false).map Gp.subtype := hpts.trans h2
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have : Gp ⊓ M₂ = (marking.parabolic true).map Gp.subtype := hlines.trans h3
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  all_goals exact absurd hk (by cases c <;> decide)

end CFSG.ASVolI
