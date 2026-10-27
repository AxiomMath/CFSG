module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Simple
public import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2Sylow
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Grp

variable {X : Type} [Group X]

theorem iSup_eq_top_or_isPGroup [Finite X] {q : ℕ}
    (hgen : ∀ P P' : Subgroup X, IsPGroup 2 P → IsPGroup 2 P' → Nat.card P = q →
      Nat.card P' = q → P ≠ P' → P ⊔ P' = ⊤)
    (𝓖 : Set (Subgroup X)) (h : ∀ T ∈ 𝓖, IsPGroup 2 T ∧ (T = ⊥ ∨ Nat.card T = q)) :
    (⨆ T ∈ 𝓖, T) = ⊤ ∨ IsPGroup 2 ↥(⨆ T ∈ 𝓖, T) := by
  by_cases hP : ∃ P ∈ 𝓖, P ≠ ⊥
  · obtain ⟨P₀, hP₀, hP₀ne⟩ := hP
    have hcard0 : Nat.card P₀ = q := (h P₀ hP₀).2.resolve_left hP₀ne
    by_cases hP' : ∃ P' ∈ 𝓖, P' ≠ ⊥ ∧ P' ≠ P₀
    · obtain ⟨P', hP'𝓖, hP'ne, hP'P₀⟩ := hP'
      left
      have hcard' : Nat.card P' = q := (h P' hP'𝓖).2.resolve_left hP'ne
      have := hgen P₀ P' (h P₀ hP₀).1 (h P' hP'𝓖).1 hcard0 hcard' (Ne.symm hP'P₀)
      rw [eq_top_iff, ← this]
      exact sup_le (le_iSup₂_of_le P₀ hP₀ le_rfl) (le_iSup₂_of_le P' hP'𝓖 le_rfl)
    · right
      push Not at hP'
      have hEq : (⨆ T ∈ 𝓖, T) = P₀ := by
        refine le_antisymm (iSup₂_le fun T hT => ?_) (le_iSup₂_of_le P₀ hP₀ le_rfl)
        by_cases hT0 : T = ⊥
        · rw [hT0]; exact bot_le
        · rw [hP' T hT hT0]
      rw [hEq]
      exact (h P₀ hP₀).1
  · right
    push Not at hP
    have hEq : (⨆ T ∈ 𝓖, T) = ⊥ := by
      refine le_antisymm (iSup₂_le fun T hT => ?_) bot_le
      rw [hP T hT]
    rw [hEq]
    exact IsPGroup.of_card (n := 0) (by simp)

theorem isPGroup_prod_of {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) : IsPGroup 2 (A × B) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hA
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hB
  exact IsPGroup.of_card (n := a + b) (by rw [Nat.card_prod, ha, hb, pow_add])

theorem fst_injective_of_snd_trivial {S : Subgroup (X × X)} (h : ∀ x ∈ S, x.2 = 1) :
    Function.Injective ((MonoidHom.fst X X).comp S.subtype) := by
  intro a b hab
  have h1 : a.1.1 = b.1.1 := hab
  exact Subtype.ext (Prod.ext h1 ((h _ a.2).trans (h _ b.2).symm))

theorem map_eq_bot_or_card {Λ : Subgroup (X × X)} (f : X × X →* X) {q : ℕ}
    (hcard : Nat.card Λ = q)
    (h : (∀ x ∈ Λ, f x = 1) ∨ (∀ x ∈ Λ, f x = 1 → x = 1)) :
    Λ.map f = ⊥ ∨ Nat.card (Λ.map f) = q := by
  rcases h with h | h
  · left
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact h x hx
  · right
    have hinj : Set.InjOn f (Λ : Set (X × X)) := by
      intro a ha b hb hab
      have h1 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      have := h _ (Λ.mul_mem ha (Λ.inv_mem hb)) h1
      exact mul_inv_eq_one.mp this
    have : Nat.card (Λ.map f) = Nat.card Λ := by
      have h2 := Nat.card_image_of_injOn hinj
      exact h2
    rw [this, hcard]

theorem normal_comap_inl {S : Subgroup (X × X)}
    (h1 : S.map (MonoidHom.fst X X) = ⊤) : (S.comap (MonoidHom.inl X X)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨⟨a, b⟩, hab, hag⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h1 g)
  have hn' : (n, (1 : X)) ∈ S := hn
  have hag' : a = g := hag
  rw [Subgroup.mem_comap]
  have h3 : ((a, b) * (n, (1 : X)) * (a, b)⁻¹ : X × X) ∈ S :=
    S.mul_mem (S.mul_mem hab hn') (S.inv_mem hab)
  have e : ((a, b) * (n, (1 : X)) * (a, b)⁻¹ : X × X) = (a * n * a⁻¹, 1) := by
    ext <;> simp
  rw [e] at h3
  rw [← hag']
  exact h3

theorem normal_comap_inr {S : Subgroup (X × X)}
    (h2 : S.map (MonoidHom.snd X X) = ⊤) : (S.comap (MonoidHom.inr X X)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨⟨a, b⟩, hab, hbg⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h2 g)
  have hn' : ((1 : X), n) ∈ S := hn
  have hbg' : b = g := hbg
  rw [Subgroup.mem_comap]
  have h3 : ((a, b) * ((1 : X), n) * (a, b)⁻¹ : X × X) ∈ S :=
    S.mul_mem (S.mul_mem hab hn') (S.inv_mem hab)
  have e : ((a, b) * ((1 : X), n) * (a, b)⁻¹ : X × X) = (1, b * n * b⁻¹) := by
    ext <;> simp
  rw [e] at h3
  rw [← hbg']
  exact h3

theorem snd_injective_of_comap_inl_eq_bot {S : Subgroup (X × X)}
    (hbot : S.comap (MonoidHom.inl X X) = ⊥) :
    Function.Injective ((MonoidHom.snd X X).comp S.subtype) := by
  intro a b hab
  have h2 : a.1.2 = b.1.2 := hab
  have hmem : ((a.1 * b.1⁻¹).1, (1 : X)) ∈ S := by
    have h3 : a.1 * b.1⁻¹ ∈ S := S.mul_mem a.2 (S.inv_mem b.2)
    have e : a.1 * b.1⁻¹ = ((a.1 * b.1⁻¹).1, (1 : X)) := by
      ext
      · rfl
      · simp [h2]
    rw [e] at h3
    exact h3
  have h4 : (a.1 * b.1⁻¹).1 ∈ S.comap (MonoidHom.inl X X) := hmem
  rw [hbot, Subgroup.mem_bot] at h4
  have h5 : a.1 * b.1⁻¹ = 1 := by
    ext
    · exact h4
    · simp [h2]
  exact Subtype.ext (mul_inv_eq_one.mp h5)

theorem fst_injective_of_comap_inr_eq_bot {S : Subgroup (X × X)}
    (hbot : S.comap (MonoidHom.inr X X) = ⊥) :
    Function.Injective ((MonoidHom.fst X X).comp S.subtype) := by
  intro a b hab
  have h2 : a.1.1 = b.1.1 := hab
  have hmem : ((1 : X), (a.1 * b.1⁻¹).2) ∈ S := by
    have h3 : a.1 * b.1⁻¹ ∈ S := S.mul_mem a.2 (S.inv_mem b.2)
    have e : a.1 * b.1⁻¹ = ((1 : X), (a.1 * b.1⁻¹).2) := by
      ext
      · simp [h2]
      · rfl
    rw [e] at h3
    exact h3
  have h4 : (a.1 * b.1⁻¹).2 ∈ S.comap (MonoidHom.inr X X) := hmem
  rw [hbot, Subgroup.mem_bot] at h4
  have h5 : a.1 * b.1⁻¹ = 1 := by
    ext
    · simp [h2]
    · exact h4
  exact Subtype.ext (mul_inv_eq_one.mp h5)

theorem iso_of_both_top [IsSimpleGroup X] {S : Subgroup (X × X)}
    (h1 : S.map (MonoidHom.fst X X) = ⊤) (h2 : S.map (MonoidHom.snd X X) = ⊤) (htop : S ≠ ⊤) :
    Nonempty (↥S ≃* X) := by
  haveI := normal_comap_inl h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.comap (MonoidHom.inl X X)) with
    hbot | hall
  · refine ⟨MulEquiv.ofBijective ((MonoidHom.snd X X).comp S.subtype)
      ⟨snd_injective_of_comap_inl_eq_bot hbot, fun y => ?_⟩⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h2 y)
    exact ⟨⟨x, hx⟩, rfl⟩
  · exfalso
    apply htop
    rw [Subgroup.eq_top_iff']
    intro ⟨a, b⟩
    obtain ⟨⟨a', b'⟩, hab', hb'⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h2 b)
    have hb'' : b' = b := hb'
    have h3 : (a * a'⁻¹, (1 : X)) ∈ S := by
      have : a * a'⁻¹ ∈ S.comap (MonoidHom.inl X X) := by rw [hall]; exact Subgroup.mem_top _
      exact this
    have e : ((a, b) : X × X) = (a * a'⁻¹, (1 : X)) * (a', b') := by
      ext
      · simp
      · simp [hb'']
    rw [e]
    exact S.mul_mem h3 hab'

theorem iso_of_fst_top [IsSimpleGroup X] (hnot : ¬ IsPGroup 2 X) {S : Subgroup (X × X)}
    (h1 : S.map (MonoidHom.fst X X) = ⊤) (h2 : IsPGroup 2 ↥(S.map (MonoidHom.snd X X)))
    (hO2 : ∀ R : Subgroup (X × X), R ≤ S → (∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) →
      IsPGroup 2 R → R = ⊥) : Nonempty (↥S ≃* X) := by
  haveI := normal_comap_inl h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.comap (MonoidHom.inl X X)) with
    hbot | hall
  · exfalso
    have hinj := snd_injective_of_comap_inl_eq_bot hbot
    let φ : ↥S →* ↥(S.map (MonoidHom.snd X X)) := (MonoidHom.snd X X).subgroupMap S
    have hφ : Function.Injective φ := by
      intro a b hab
      apply hinj
      have := congrArg Subtype.val hab
      exact this
    have hS2 : IsPGroup 2 ↥S := h2.of_injective φ hφ
    apply hnot
    refine hS2.of_surjective ((MonoidHom.fst X X).comp S.subtype) ?_
    intro x
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h1 x)
    exact ⟨⟨y, hy⟩, rfl⟩
  · set S₂ := S.map (MonoidHom.snd X X) with hS₂
    let R : Subgroup (X × X) := (⊥ : Subgroup X).prod S₂
    have hRS : R ≤ S := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := Subgroup.mem_prod.mp hr
      obtain ⟨⟨a, b⟩, hab, hb⟩ := Subgroup.mem_map.mp hr2
      have hb' : b = r.2 := hb
      have h3 : (a⁻¹, (1 : X)) ∈ S := by
        have : a⁻¹ ∈ S.comap (MonoidHom.inl X X) := by rw [hall]; exact Subgroup.mem_top _
        exact this
      have hr1' : r.1 = 1 := Subgroup.mem_bot.mp hr1
      have e : r = (a⁻¹, (1 : X)) * (a, b) := by
        ext
        · simp [hr1']
        · simp [hb']
      rw [e]
      exact S.mul_mem h3 hab
    have hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
      intro s hs r hr
      obtain ⟨hr1, hr2⟩ := Subgroup.mem_prod.mp hr
      have hr1' : r.1 = 1 := Subgroup.mem_bot.mp hr1
      refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_bot]
        simp [hr1']
      · have hs2 : s.2 ∈ S₂ := Subgroup.mem_map_of_mem _ hs
        exact S₂.mul_mem (S₂.mul_mem hs2 hr2) (S₂.inv_mem hs2)
    have hRp : IsPGroup 2 ↥R := by
      let ψ : ↥R →* ↥S₂ := ((MonoidHom.snd X X).comp R.subtype).codRestrict S₂
        (fun r => (Subgroup.mem_prod.mp r.2).2)
      refine h2.of_injective ψ ?_
      intro a b hab
      have h4 : a.1.2 = b.1.2 := congrArg Subtype.val hab
      have ha1 : a.1.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp a.2).1
      have hb1 : b.1.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp b.2).1
      exact Subtype.ext (Prod.ext (ha1.trans hb1.symm) h4)
    have hRbot : R = ⊥ := hO2 R hRS hRn hRp
    have hS₂bot : S₂ = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
      have : ((1 : X), y) ∈ R := Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hy⟩
      rw [hRbot, Subgroup.mem_bot] at this
      exact congrArg Prod.snd this
    have hsnd1 : ∀ x ∈ S, x.2 = 1 := by
      intro x hx
      have : x.2 ∈ S₂ := Subgroup.mem_map_of_mem _ hx
      rw [hS₂bot, Subgroup.mem_bot] at this
      exact this
    refine ⟨MulEquiv.ofBijective ((MonoidHom.fst X X).comp S.subtype)
      ⟨fst_injective_of_snd_trivial hsnd1, fun x => ?_⟩⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h1 x)
    exact ⟨⟨y, hy⟩, rfl⟩

theorem iso_of_snd_top [IsSimpleGroup X] (hnot : ¬ IsPGroup 2 X) {S : Subgroup (X × X)}
    (h2 : S.map (MonoidHom.snd X X) = ⊤) (h1 : IsPGroup 2 ↥(S.map (MonoidHom.fst X X)))
    (hO2 : ∀ R : Subgroup (X × X), R ≤ S → (∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) →
      IsPGroup 2 R → R = ⊥) : Nonempty (↥S ≃* X) := by
  haveI := normal_comap_inr h2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.comap (MonoidHom.inr X X)) with
    hbot | hall
  · exfalso
    have hinj := fst_injective_of_comap_inr_eq_bot hbot
    let φ : ↥S →* ↥(S.map (MonoidHom.fst X X)) := (MonoidHom.fst X X).subgroupMap S
    have hφ : Function.Injective φ := by
      intro a b hab
      apply hinj
      have := congrArg Subtype.val hab
      exact this
    have hS2 : IsPGroup 2 ↥S := h1.of_injective φ hφ
    apply hnot
    refine hS2.of_surjective ((MonoidHom.snd X X).comp S.subtype) ?_
    intro x
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h2 x)
    exact ⟨⟨y, hy⟩, rfl⟩
  · set S₁ := S.map (MonoidHom.fst X X) with hS₁
    let R : Subgroup (X × X) := S₁.prod (⊥ : Subgroup X)
    have hRS : R ≤ S := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := Subgroup.mem_prod.mp hr
      obtain ⟨⟨a, b⟩, hab, ha⟩ := Subgroup.mem_map.mp hr1
      have ha' : a = r.1 := ha
      have h3 : ((1 : X), b⁻¹) ∈ S := by
        have : b⁻¹ ∈ S.comap (MonoidHom.inr X X) := by rw [hall]; exact Subgroup.mem_top _
        exact this
      have hr2' : r.2 = 1 := Subgroup.mem_bot.mp hr2
      have e : r = ((1 : X), b⁻¹) * (a, b) := by
        ext
        · simp [ha']
        · simp [hr2']
      rw [e]
      exact S.mul_mem h3 hab
    have hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
      intro s hs r hr
      obtain ⟨hr1, hr2⟩ := Subgroup.mem_prod.mp hr
      have hr2' : r.2 = 1 := Subgroup.mem_bot.mp hr2
      refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
      · have hs1 : s.1 ∈ S₁ := Subgroup.mem_map_of_mem _ hs
        exact S₁.mul_mem (S₁.mul_mem hs1 hr1) (S₁.inv_mem hs1)
      · rw [Subgroup.mem_bot]
        simp [hr2']
    have hRp : IsPGroup 2 ↥R := by
      let ψ : ↥R →* ↥S₁ := ((MonoidHom.fst X X).comp R.subtype).codRestrict S₁
        (fun r => (Subgroup.mem_prod.mp r.2).1)
      refine h1.of_injective ψ ?_
      intro a b hab
      have h4 : a.1.1 = b.1.1 := congrArg Subtype.val hab
      have ha2 : a.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp a.2).2
      have hb2 : b.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp b.2).2
      exact Subtype.ext (Prod.ext h4 (ha2.trans hb2.symm))
    have hRbot : R = ⊥ := hO2 R hRS hRn hRp
    have hS₁bot : S₁ = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
      have : (y, (1 : X)) ∈ R := Subgroup.mem_prod.mpr ⟨hy, Subgroup.one_mem _⟩
      rw [hRbot, Subgroup.mem_bot] at this
      exact congrArg Prod.fst this
    have hfst1 : ∀ x ∈ S, x.1 = 1 := by
      intro x hx
      have : x.1 ∈ S₁ := Subgroup.mem_map_of_mem _ hx
      rw [hS₁bot, Subgroup.mem_bot] at this
      exact this
    have hinj : Function.Injective ((MonoidHom.snd X X).comp S.subtype) := by
      intro a b hab
      have h4 : a.1.2 = b.1.2 := hab
      exact Subtype.ext (Prod.ext ((hfst1 _ a.2).trans (hfst1 _ b.2).symm) h4)
    refine ⟨MulEquiv.ofBijective ((MonoidHom.snd X X).comp S.subtype) ⟨hinj, fun x => ?_⟩⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ((Subgroup.eq_top_iff' _).mp h2 x)
    exact ⟨⟨y, hy⟩, rfl⟩

theorem exists_mulEquiv_of_generated [Finite X] [IsSimpleGroup X] {q : ℕ} (hq : 1 < q)
    (hnot : ¬ IsPGroup 2 X)
    (hgen : ∀ P P' : Subgroup X, IsPGroup 2 P → IsPGroup 2 P' → Nat.card P = q →
      Nat.card P' = q → P ≠ P' → P ⊔ P' = ⊤)
    {S : Subgroup (X × X)} (𝓕 : Set (Subgroup (X × X))) (hS : S = ⨆ Λ ∈ 𝓕, Λ)
    (hF : ∀ Λ ∈ 𝓕, IsPGroup 2 Λ ∧ Nat.card Λ = q ∧
      ((∀ x ∈ Λ, x.2 = 1) ∨ (∀ x ∈ Λ, x.1 = 1) ∨
        ((∀ x ∈ Λ, x.1 = 1 → x = 1) ∧ ∀ x ∈ Λ, x.2 = 1 → x = 1))) (hne : 𝓕.Nonempty)
    (hO2 : ∀ R : Subgroup (X × X), R ≤ S → (∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) →
      IsPGroup 2 R → R = ⊥)
    (htop : S ≠ ⊤) : Nonempty (↥S ≃* X) := by
  classical
  have hmap : ∀ f : X × X →* X,
      S.map f = ⨆ T ∈ ((fun Λ : Subgroup (X × X) => Λ.map f) '' 𝓕), T := by
    intro f
    rw [hS, Subgroup.map_iSup]
    simp only [Subgroup.map_iSup, iSup_image]
  have hproj : ∀ f : X × X →* X, (∀ Λ ∈ 𝓕, (Λ.map f = ⊥ ∨ Nat.card (Λ.map f) = q)) →
      S.map f = ⊤ ∨ IsPGroup 2 ↥(S.map f) := by
    intro f hf
    rw [hmap f]
    refine iSup_eq_top_or_isPGroup hgen _ ?_
    rintro T ⟨Λ, hΛ, rfl⟩
    exact ⟨(hF Λ hΛ).1.map f, hf Λ hΛ⟩
  have hfst : S.map (MonoidHom.fst X X) = ⊤ ∨ IsPGroup 2 ↥(S.map (MonoidHom.fst X X)) := by
    refine hproj _ fun Λ hΛ => ?_
    obtain ⟨-, hc, h⟩ := hF Λ hΛ
    refine map_eq_bot_or_card _ hc ?_
    rcases h with h | h | ⟨h, -⟩
    · exact Or.inr fun x hx hx1 => Prod.ext hx1 (h x hx)
    · exact Or.inl fun x hx => h x hx
    · exact Or.inr h
  have hsnd : S.map (MonoidHom.snd X X) = ⊤ ∨ IsPGroup 2 ↥(S.map (MonoidHom.snd X X)) := by
    refine hproj _ fun Λ hΛ => ?_
    obtain ⟨-, hc, h⟩ := hF Λ hΛ
    refine map_eq_bot_or_card _ hc ?_
    rcases h with h | h | ⟨-, h⟩
    · exact Or.inl fun x hx => h x hx
    · exact Or.inr fun x hx hx2 => Prod.ext (h x hx) hx2
    · exact Or.inr h
  rcases hfst with h1 | h1 <;> rcases hsnd with h2 | h2
  · exact iso_of_both_top h1 h2 htop
  · exact iso_of_fst_top hnot h1 h2 hO2
  · exact iso_of_snd_top hnot h2 h1 hO2
  · exfalso
    have hSp : IsPGroup 2 ↥S := by
      let ϕ : ↥S →* ↥(S.map (MonoidHom.fst X X)) × ↥(S.map (MonoidHom.snd X X)) :=
        ((MonoidHom.fst X X).subgroupMap S).prod ((MonoidHom.snd X X).subgroupMap S)
      refine (isPGroup_prod_of h1 h2).of_injective ϕ ?_
      intro a b hab
      have e1 := congrArg (fun p => (p.1 : X)) hab
      have e2 := congrArg (fun p => (p.2 : X)) hab
      exact Subtype.ext (Prod.ext e1 e2)
    have hSbot := hO2 S le_rfl (fun s hs r hr => S.mul_mem (S.mul_mem hs hr) (S.inv_mem hs)) hSp
    obtain ⟨Λ, hΛ⟩ := hne
    have hΛS : Λ ≤ S := by rw [hS]; exact le_iSup₂_of_le Λ hΛ le_rfl
    have hΛbot : Λ = ⊥ := le_bot_iff.mp (hSbot ▸ hΛS)
    have hc := (hF Λ hΛ).2.1
    rw [hΛbot, Subgroup.card_bot] at hc
    omega

theorem aut_prod_factors [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (α : (X × X) ≃* (X × X)) :
    (((⊤ : Subgroup X).prod ⊥).map α.toMonoidHom = (⊤ : Subgroup X).prod ⊥ ∧
        ((⊥ : Subgroup X).prod ⊤).map α.toMonoidHom = (⊥ : Subgroup X).prod ⊤) ∨
      (((⊤ : Subgroup X).prod ⊥).map α.toMonoidHom = (⊥ : Subgroup X).prod ⊤ ∧
        ((⊥ : Subgroup X).prod ⊤).map α.toMonoidHom = (⊤ : Subgroup X).prod ⊥) := by
  have hX' := hX
  obtain ⟨a, b, hab⟩ := hX
  have ha1 : a ≠ 1 := fun h => hab (by rw [h]; simp)
  have hb1 : b ≠ 1 := fun h => hab (by rw [h]; simp)
  set F₁ : Subgroup (X × X) := (⊤ : Subgroup X).prod ⊥ with hF₁
  set F₂ : Subgroup (X × X) := (⊥ : Subgroup X).prod ⊤ with hF₂
  have hmemF₁ : ∀ p : X × X, p ∈ F₁ ↔ p.2 = 1 := fun p => by
    simp [hF₁, Subgroup.mem_prod]
  have hmemF₂ : ∀ p : X × X, p ∈ F₂ ↔ p.1 = 1 := fun p => by
    simp [hF₂, Subgroup.mem_prod]
  have h1ne : F₁ ≠ ⊥ := fun h => by
    have : (a, (1 : X)) ∈ F₁ := (hmemF₁ _).mpr rfl
    rw [h, Subgroup.mem_bot] at this
    exact ha1 (congrArg Prod.fst this)
  have h1top : F₁ ≠ ⊤ := fun h => by
    have : ((1 : X), b) ∈ F₁ := by rw [h]; exact Subgroup.mem_top _
    exact hb1 ((hmemF₁ _).mp this)
  have h2ne : F₂ ≠ ⊥ := fun h => by
    have : ((1 : X), b) ∈ F₂ := (hmemF₂ _).mpr rfl
    rw [h, Subgroup.mem_bot] at this
    exact hb1 (congrArg Prod.snd this)
  have h2top : F₂ ≠ ⊤ := fun h => by
    have : (a, (1 : X)) ∈ F₂ := by rw [h]; exact Subgroup.mem_top _
    exact ha1 ((hmemF₂ _).mp this)
  have h12 : F₁ ≠ F₂ := fun h => by
    have : (a, (1 : X)) ∈ F₂ := by rw [← h]; exact (hmemF₁ _).mpr rfl
    exact ha1 ((hmemF₂ _).mp this)
  have hcases : ∀ F : Subgroup (X × X), F.Normal → F ≠ ⊥ → F ≠ ⊤ →
      (F.map α.toMonoidHom = F₁ ∨ F.map α.toMonoidHom = F₂) := by
    intro F hF hFbot hFtop
    have hFm : (F.map α.toMonoidHom).Normal := hF.map _ α.surjective
    rcases isSubnormal_prod_cases hX' hX' hFm.isSubnormal with h | h | h | h
    · exact absurd ((Subgroup.map_eq_bot_iff_of_injective F
        (f := α.toMonoidHom) α.injective).mp h) hFbot
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      apply hFtop
      have := Subgroup.map_injective (f := α.toMonoidHom) α.injective
        (h.trans (Subgroup.map_top_of_surjective _ α.surjective).symm)
      exact this
  have hinj : Function.Injective (Subgroup.map α.toMonoidHom : Subgroup (X × X) → _) :=
    Subgroup.map_injective α.injective
  haveI : F₁.Normal := Subgroup.prod_normal _ _
  haveI : F₂.Normal := Subgroup.prod_normal _ _
  rcases hcases F₁ inferInstance h1ne h1top with e1 | e1 <;>
    rcases hcases F₂ inferInstance h2ne h2top with e2 | e2
  · exact absurd (hinj (e1.trans e2.symm)) h12
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (hinj (e1.trans e2.symm)) h12

@[expose] def fac₁ (X : Type) [Group X] : Subgroup (X × X) := (⊤ : Subgroup X).prod ⊥

@[expose] def fac₂ (X : Type) [Group X] : Subgroup (X × X) := (⊥ : Subgroup X).prod ⊤

theorem mem_fac₁ (p : X × X) : p ∈ fac₁ X ↔ p.2 = 1 := by
  simp [fac₁, Subgroup.mem_prod]

theorem mem_fac₂ (p : X × X) : p ∈ fac₂ X ↔ p.1 = 1 := by
  simp [fac₂, Subgroup.mem_prod]

@[expose] def Tri (Λ : Subgroup (X × X)) : Prop :=
  Λ ≤ fac₁ X ∨ Λ ≤ fac₂ X ∨ (Λ ⊓ fac₁ X = ⊥ ∧ Λ ⊓ fac₂ X = ⊥)

theorem tri_map {α : (X × X) ≃* (X × X)}
    (hα : ((fac₁ X).map α.toMonoidHom = fac₁ X ∧ (fac₂ X).map α.toMonoidHom = fac₂ X) ∨
      ((fac₁ X).map α.toMonoidHom = fac₂ X ∧ (fac₂ X).map α.toMonoidHom = fac₁ X))
    {Λ : Subgroup (X × X)} (h : Tri Λ) : Tri (Λ.map α.toMonoidHom) := by
  have hle : ∀ F : Subgroup (X × X), Λ ≤ F → Λ.map α.toMonoidHom ≤ F.map α.toMonoidHom :=
    fun F hF => Subgroup.map_mono hF
  have hinf : ∀ F : Subgroup (X × X), Λ ⊓ F = ⊥ →
      Λ.map α.toMonoidHom ⊓ F.map α.toMonoidHom = ⊥ := by
    intro F hF
    rw [← Subgroup.map_inf_eq _ _ _ α.injective, hF, Subgroup.map_bot]
  rcases hα with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h with h | h | ⟨h3, h4⟩
    · exact Or.inl (h1 ▸ hle _ h)
    · exact Or.inr (Or.inl (h2 ▸ hle _ h))
    · exact Or.inr (Or.inr ⟨h1 ▸ hinf _ h3, h2 ▸ hinf _ h4⟩)
  · rcases h with h | h | ⟨h3, h4⟩
    · exact Or.inr (Or.inl (h1 ▸ hle _ h))
    · exact Or.inl (h2 ▸ hle _ h)
    · exact Or.inr (Or.inr ⟨h2 ▸ hinf _ h4, h1 ▸ hinf _ h3⟩)

theorem tri_iff_elementwise {Λ : Subgroup (X × X)} :
    Tri Λ ↔ ((∀ x ∈ Λ, x.2 = 1) ∨ (∀ x ∈ Λ, x.1 = 1) ∨
        ((∀ x ∈ Λ, x.1 = 1 → x = 1) ∧ ∀ x ∈ Λ, x.2 = 1 → x = 1)) := by
  unfold Tri
  constructor
  · rintro (h | h | ⟨h1, h2⟩)
    · exact Or.inl fun x hx => (mem_fac₁ x).mp (h hx)
    · exact Or.inr (Or.inl fun x hx => (mem_fac₂ x).mp (h hx))
    · refine Or.inr (Or.inr ⟨fun x hx hx1 => ?_, fun x hx hx2 => ?_⟩)
      · have : x ∈ Λ ⊓ fac₂ X := ⟨hx, (mem_fac₂ x).mpr hx1⟩
        rw [h2] at this
        exact Subgroup.mem_bot.mp this
      · have : x ∈ Λ ⊓ fac₁ X := ⟨hx, (mem_fac₁ x).mpr hx2⟩
        rw [h1] at this
        exact Subgroup.mem_bot.mp this
  · rintro (h | h | ⟨h1, h2⟩)
    · exact Or.inl fun x hx => (mem_fac₁ x).mpr (h x hx)
    · exact Or.inr (Or.inl fun x hx => (mem_fac₂ x).mpr (h x hx))
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => h2 x hx.1 ((mem_fac₁ x).mp hx.2)
      · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => h1 x hx.1 ((mem_fac₂ x).mp hx.2)

theorem exists_mulEquiv_of_conj_family [Finite X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) {q : ℕ} (hq : 1 < q) (hnot : ¬ IsPGroup 2 X)
    (hgen : ∀ P P' : Subgroup X, IsPGroup 2 P → IsPGroup 2 P' → Nat.card P = q →
      Nat.card P' = q → P ≠ P' → P ⊔ P' = ⊤)
    {Λ₀ : Subgroup (X × X)} (hΛ₀ : IsPGroup 2 Λ₀) (hcard : Nat.card Λ₀ = q) (htri : Tri Λ₀)
    (𝒜 : Set ((X × X) ≃* (X × X))) (h𝒜 : 𝒜.Nonempty) {S : Subgroup (X × X)}
    (hS : S = ⨆ α ∈ 𝒜, Λ₀.map α.toMonoidHom)
    (hO2 : ∀ R : Subgroup (X × X), R ≤ S → (∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) →
      IsPGroup 2 R → R = ⊥)
    (htop : S ≠ ⊤) : Nonempty (↥S ≃* X) := by
  refine exists_mulEquiv_of_generated hq hnot hgen
    ((fun α : (X × X) ≃* (X × X) => Λ₀.map α.toMonoidHom) '' 𝒜) ?_ ?_ (h𝒜.image _) hO2 htop
  · rw [hS]
    simp only [iSup_image]
  · rintro _ ⟨α, hα, rfl⟩
    refine ⟨hΛ₀.map _, ?_, tri_iff_elementwise.mp (tri_map (aut_prod_factors hX α) htri)⟩
    rw [Subgroup.card_map_of_injective α.injective, hcard]

theorem exists_aut_of_stable {A Γ : Type*} [Group A] [Group Γ] (ρ : A →* Γ)
    (hρ : Function.Injective ρ) (φ : Γ ≃* Γ) (hφ : ∀ z, φ (ρ z) ∈ ρ.range)
    (hφ' : ∀ z, φ.symm (ρ z) ∈ ρ.range) :
    ∃ α : A ≃* A, ∀ z, ρ (α z) = φ (ρ z) := by
  choose f hf using hφ
  let α₀ : A →* A :=
    { toFun := f
      map_one' := by
        apply hρ
        rw [hf, map_one, map_one]
      map_mul' := fun z w => by
        apply hρ
        rw [hf, map_mul, map_mul, map_mul, hf, hf] }
  have hinj : Function.Injective α₀ := by
    intro z w h
    apply hρ
    apply φ.injective
    rw [← hf z, ← hf w]
    exact congrArg ρ h
  have hsurj : Function.Surjective α₀ := by
    intro w
    obtain ⟨z, hz⟩ := hφ' w
    refine ⟨z, hρ ?_⟩
    show ρ (f z) = ρ w
    rw [hf, hz, MulEquiv.apply_symm_apply]
  exact ⟨MulEquiv.ofBijective α₀ ⟨hinj, hsurj⟩, fun z => hf z⟩

theorem perm_of_stable [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) {Γ : Type}
    [Group Γ] (ρ : X × X →* Γ) (hρ : Function.Injective ρ) (φ : Γ ≃* Γ)
    (hφ : ∀ z, φ (ρ z) ∈ ρ.range) (hφ' : ∀ z, φ.symm (ρ z) ∈ ρ.range) :
    (((fac₁ X).map ρ).map φ.toMonoidHom = (fac₁ X).map ρ ∧
        ((fac₂ X).map ρ).map φ.toMonoidHom = (fac₂ X).map ρ) ∨
      (((fac₁ X).map ρ).map φ.toMonoidHom = (fac₂ X).map ρ ∧
        ((fac₂ X).map ρ).map φ.toMonoidHom = (fac₁ X).map ρ) := by
  obtain ⟨α, hα⟩ := exists_aut_of_stable ρ hρ φ hφ hφ'
  have hcomp : φ.toMonoidHom.comp ρ = ρ.comp α.toMonoidHom :=
    MonoidHom.ext fun z => (hα z).symm
  have hmap : ∀ F : Subgroup (X × X),
      (F.map ρ).map φ.toMonoidHom = (F.map α.toMonoidHom).map ρ := by
    intro F
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hmap, hmap]
  rcases aut_prod_factors hX α with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨congrArg (Subgroup.map ρ) h1, congrArg (Subgroup.map ρ) h2⟩
  · right
    exact ⟨congrArg (Subgroup.map ρ) h1, congrArg (Subgroup.map ρ) h2⟩

theorem perm_sq {Γ : Type} [Group Γ] {N₁ N₂ : Subgroup Γ} {φ : Γ ≃* Γ}
    (h : (N₁.map φ.toMonoidHom = N₁ ∧ N₂.map φ.toMonoidHom = N₂) ∨
      (N₁.map φ.toMonoidHom = N₂ ∧ N₂.map φ.toMonoidHom = N₁)) :
    (N₁.map φ.toMonoidHom).map φ.toMonoidHom = N₁ ∧
      (N₂.map φ.toMonoidHom).map φ.toMonoidHom = N₂ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h1, h1], by rw [h2, h2]⟩
  · exact ⟨by rw [h1, h2], by rw [h2, h1]⟩

section XFacts

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sl2_isSimpleGroup (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  haveI := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo (F := K) h4
  exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).isSimpleGroup

theorem sl2_nonabelian :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  refine ⟨Matrix.SpecialLinearGroup.transvection sl2Idx01 1,
    Matrix.SpecialLinearGroup.transvection sl2Idx10 1, fun h => ?_⟩
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    ((g : Matrix (Fin 2) (Fin 2) K) 0 0)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, sl2_coe_t01, sl2_coe_t10] at h1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h1

theorem sl2_not_isPGroup (h4 : 4 ≤ Nat.card K) :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := sl2_finite K
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  rw [sl2_card K] at hn
  have hdvd : Nat.card K ^ 2 - 1 ∣ 2 ^ n :=
    ⟨Nat.card K, by rw [← hn, mul_comm]⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have hq2 : 2 ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self 2 m.ne_zero
  have hsq : 2 ∣ Nat.card K ^ 2 := dvd_pow hq2 two_ne_zero
  have hsq16 : 16 ≤ Nat.card K ^ 2 := by nlinarith
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · rw [h0, pow_zero] at hk
    omega
  · have : 2 ∣ Nat.card K ^ 2 - 1 := by
      rw [hk]
      exact dvd_pow_self 2 h0.ne'
    omega

end XFacts

end CFSG.RankThree.GF2n.Stroth80.SL2Grp
