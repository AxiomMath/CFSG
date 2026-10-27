module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open scoped commutatorElement

section Bar2

variable {X Y : Type} [Group X] [Group Y]

@[expose] noncomputable def bar2Hom (f : X →* Y) (hf : Function.Surjective f) :
    X ⧸ CFSG.pCore 2 X →* Y ⧸ CFSG.pCore 2 Y :=
  QuotientGroup.map (CFSG.pCore 2 X) (CFSG.pCore 2 Y) f (pCore_le_comap_of_surjective f hf)

theorem bar2Hom_mk (f : X →* Y) (hf : Function.Surjective f) (x : X) :
    bar2Hom f hf (QuotientGroup.mk x) = QuotientGroup.mk (f x) :=
  rfl

theorem bar2Hom_surjective (f : X →* Y) (hf : Function.Surjective f) :
    Function.Surjective (bar2Hom f hf) := by
  intro y
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hf y₀
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem ker_bar2Hom_le_center [Finite X] (f : X →* Y) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) :
    (bar2Hom f hf).ker ≤ Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup X := CFSG.pCore 2 X with hN
  set Kq : Subgroup (X ⧸ N) := ((CFSG.pCore 2 Y).comap f).map (QuotientGroup.mk' N) with hKq
  set C : Subgroup (X ⧸ N) := f.ker.map (QuotientGroup.mk' N) with hC
  have hNle : N ≤ (CFSG.pCore 2 Y).comap f := pCore_le_comap_of_surjective f hf
  have hker_eq : (bar2Hom f hf).ker = Kq := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker, bar2Hom_mk, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y⁻¹ * x ∈ N := (QuotientGroup.eq (s := N)).mp hyx
      have h1 : y * (y⁻¹ * x) ∈ (CFSG.pCore 2 Y).comap f := mul_mem hy (hNle hyx')
      rw [mul_inv_cancel_left] at h1
      exact h1
  have hCK : C ≤ Kq := Subgroup.map_mono fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    show f x ∈ CFSG.pCore 2 Y
    rw [hx]
    exact one_mem _
  have hCcent : C ≤ Subgroup.center (X ⧸ N) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have hxy := Subgroup.mem_center_iff.mp (hker hx) y
    change QuotientGroup.mk (y * x) = QuotientGroup.mk (x * y)
    rw [hxy]
  have hKn : Kq.Normal :=
    (Subgroup.Normal.comap CFSG.pCore_normal f).map _ (QuotientGroup.mk'_surjective N)
  have hpow : ∀ k ∈ Kq, ∃ a : ℕ, k ^ (2 ^ a) ∈ C :=
    pow_two_mem_map_of_isPGroup f (CFSG.pCore_isPGroup (p := 2) (G := Y))
  have hbot : CFSG.pCore 2 (X ⧸ N) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨hKC, -⟩ := eq_of_pow_two_mem_of_pCore_eq_bot hCK hCcent hpow hbot
  rw [hker_eq, hKC]
  exact hCcent

end Bar2

section Image

variable {G G' : Type} [Group G] [Group G'] {L : Subgroup G} {L' : Subgroup G'}

@[expose] def imgSub (ψ : ↥L →* ↥L') (A : Subgroup G) : Subgroup G' :=
  ((A.subgroupOf L).map ψ).map L'.subtype

theorem mem_imgSub {ψ : ↥L →* ↥L'} {A : Subgroup G} {y : G'} :
    y ∈ imgSub ψ A ↔ ∃ x : ↥L, (x : G) ∈ A ∧ ((ψ x : ↥L') : G') = y := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩

theorem imgSub_mono (ψ : ↥L →* ↥L') {A B : Subgroup G} (h : A ≤ B) : imgSub ψ A ≤ imgSub ψ B :=
  Subgroup.map_mono (Subgroup.map_mono fun _ hx => h hx)

theorem imgSub_self (ψ : ↥L →* ↥L') (hψ : Function.Surjective ψ) : imgSub ψ L = L' := by
  ext y
  rw [mem_imgSub]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact (ψ x).2
  · intro hy
    obtain ⟨x, hx⟩ := hψ ⟨y, hy⟩
    exact ⟨x, x.2, by rw [hx]⟩

theorem imgSub_sup (ψ : ↥L →* ↥L') {A B : Subgroup G} (hA : A ≤ L) (hB : B ≤ L) :
    imgSub ψ (A ⊔ B) = imgSub ψ A ⊔ imgSub ψ B := by
  rw [imgSub, imgSub, imgSub, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup, Subgroup.map_sup]

theorem imgSub_commutator (ψ : ↥L →* ↥L') {A : Subgroup G} (hA : A ≤ L) :
    imgSub ψ ⁅A, A⁆ = ⁅imgSub ψ A, imgSub ψ A⁆ := by
  have h1 : (⁅A, A⁆).subgroupOf L = ⁅A.subgroupOf L, A.subgroupOf L⁆ := by
    have hA' : (A.subgroupOf L).map L.subtype = A := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA]
    have h0 : ⁅A, A⁆ = (⁅A.subgroupOf L, A.subgroupOf L⁆).map L.subtype := by
      rw [Subgroup.map_commutator, hA']
    rw [h0, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  rw [imgSub, imgSub, h1, Subgroup.map_commutator, Subgroup.map_commutator]

theorem isSubnormal_imgSub (ψ : ↥L →* ↥L') {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B)
    (hB : B ≤ L) : CFSG.Open.IsSubnormal (imgSub ψ A) (imgSub ψ B) := by
  induction h with
  | refl H => exact CFSG.Open.IsSubnormal.refl _
  | @step H M K hHM hHn hMK ih =>
    have hML : M ≤ L := (CFSG.Open.IsSubnormal.le hMK).trans hB
    refine CFSG.Open.IsSubnormal.step (imgSub_mono ψ hHM) ?_ (ih hB)
    rw [Subgroup.normal_subgroupOf_iff (imgSub_mono ψ hHM)]
    intro h m hh hm
    obtain ⟨x, hx, rfl⟩ := mem_imgSub.mp hh
    obtain ⟨y, hy, rfl⟩ := mem_imgSub.mp hm
    refine mem_imgSub.mpr ⟨y * x * y⁻¹, ?_, by simp⟩
    have := (Subgroup.normal_subgroupOf_iff hHM).mp hHn (x : G) (y : G) hx hy
    simpa using this

end Image

section NParam

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

private theorem nontrivial_bar2 {X : Subgroup G'} (hperf : ⁅X, X⁆ = X) (hne : X ≠ ⊥) :
    Nontrivial (Bar2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  apply hne
  have htop : CFSG.pCore 2 ↥X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : (QuotientGroup.mk x : Bar2 X) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp this
  have hp : IsPGroup 2 ↥X := by
    have h := CFSG.pCore_isPGroup (p := 2) (G := ↥X)
    rw [htop] at h
    exact h.of_equiv Subgroup.topEquiv
  exact CFSG.ComponentClassification.CatFactsSmall.eq_bot_of_perfect_of_isPGroup
    (IsPGroup.of_equiv hp (Subgroup.topEquiv).symm |>.of_equiv Subgroup.topEquiv) hperf

private noncomputable def restrictImg {L : Subgroup G} {L' : Subgroup G'} (ψ : ↥L →* ↥L')
    {A : Subgroup G} (hA : A ≤ L) : ↥A →* ↥(imgSub ψ A) :=
  ((L'.subtype.comp ψ).comp (Subgroup.inclusion hA)).codRestrict (imgSub ψ A) fun a =>
    mem_imgSub.mpr ⟨Subgroup.inclusion hA a, a.2, rfl⟩

omit [Finite G] [Finite G'] in
private theorem restrictImg_surjective {L : Subgroup G} {L' : Subgroup G'} (ψ : ↥L →* ↥L')
    {A : Subgroup G} (hA : A ≤ L) : Function.Surjective (restrictImg ψ hA) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_imgSub.mp hy
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rfl

omit [Finite G] [Finite G'] in
private theorem ker_restrictImg_le_center {L : Subgroup G} {L' : Subgroup G'} (ψ : ↥L →* ↥L')
    (hker : ψ.ker ≤ Subgroup.center ↥L) {A : Subgroup G} (hA : A ≤ L) :
    (restrictImg ψ hA).ker ≤ Subgroup.center ↥A := by
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have h1 : ψ (Subgroup.inclusion hA a) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val ha
    simpa [restrictImg] using this
  have h2 := hker (MonoidHom.mem_ker.mpr h1)
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro b
  have := h2 (Subgroup.inclusion hA b)
  apply Subtype.ext
  have := congrArg Subtype.val this
  simpa using this

omit [Finite G] in
private theorem ne_bot_of_mem_calC {L L₁ : Subgroup G} (h : L₁ ∈ calC L) : L₁ ≠ ⊥ := by
  intro hbot
  obtain ⟨-, -, hq⟩ := h
  have : Subsingleton ↥L₁ := by
    rw [hbot]
    infer_instance
  have : Subsingleton (Bar2 L₁) := (QuotientGroup.mk'_surjective _).subsingleton
  have := hq.2
  exact not_subsingleton (Bar2 L₁ ⧸ Subgroup.center (Bar2 L₁))
    (QuotientGroup.mk'_surjective _).subsingleton

private theorem commutator_mul_center {H : Type*} [Group H] {x y z z' : H}
    (hz : z ∈ Subgroup.center H) (hz' : z' ∈ Subgroup.center H) : ⁅x * z, y * z'⁆ = ⁅x, y⁆ := by
  have h1 : ∀ g : H, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  have h2 : ∀ g : H, g * z' = z' * g := fun g => (Subgroup.mem_center_iff.mp hz' g)
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  calc x * z * (y * z') * (z⁻¹ * x⁻¹) * (z'⁻¹ * y⁻¹)
      = x * (z * (y * z')) * z⁻¹ * x⁻¹ * (z'⁻¹ * y⁻¹) := by simp only [mul_assoc]
    _ = x * ((y * z') * z) * z⁻¹ * x⁻¹ * (z'⁻¹ * y⁻¹) := by rw [← h1 (y * z')]
    _ = x * y * (z' * x⁻¹) * z'⁻¹ * y⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = x * y * (x⁻¹ * z') * z'⁻¹ * y⁻¹ := by rw [← h2 x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]

theorem nParam_of_surjective_central {L : Subgroup G} {L' : Subgroup G'} (ψ : ↥L →* ↥L')
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center ↥L) (hperf : ⁅L', L'⁆ = L')
    (hne : L' ≠ ⊥) {n : ℕ} (h : NParam L n) : NParam L' n := by
  rcases h with hs | ⟨L₁, L₂, h₁, h₂, hsup, hne₁₂, htypes⟩
  · exact Or.inl (nParamSingle_of_surjective_central hs (bar2Hom ψ hψ) (bar2Hom_surjective ψ hψ)
      (ker_bar2Hom_le_center ψ hψ hker) (nontrivial_bar2 hperf hne))
  · right
    have hL₁ : L₁ ≤ L := h₁.1.le
    have hL₂ : L₂ ≤ L := h₂.1.le
    have hmem : ∀ {A : Subgroup G}, A ∈ calC L → imgSub ψ A ∈ calC L' ∧
        ∃ β : Bar2 A →* Bar2 (imgSub ψ A), Function.Surjective β ∧
          β.ker ≤ Subgroup.center (Bar2 A) ∧ Nontrivial (Bar2 (imgSub ψ A)) := by
      intro A hA
      have hAL : A ≤ L := hA.1.le
      have hperfA : ⁅imgSub ψ A, imgSub ψ A⁆ = imgSub ψ A := by
        rw [← imgSub_commutator ψ hAL, hA.2.1]
      have hneA : imgSub ψ A ≠ ⊥ := by
        intro hbot
        apply ne_bot_of_mem_calC hA
        have hAz : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
          intro a ha b hb
          have hk : ψ ⟨a, hAL ha⟩ = 1 := by
            have : ((ψ ⟨a, hAL ha⟩ : ↥L') : G') ∈ imgSub ψ A := mem_imgSub.mpr ⟨_, ha, rfl⟩
            rw [hbot, Subgroup.mem_bot] at this
            exact Subtype.ext this
          have := Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hk)) ⟨b, hAL hb⟩
          exact (congrArg Subtype.val this).symm
        rw [← hA.2.1, eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def, hAz a ha b hb, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _
      have hntA := nontrivial_bar2 hperfA hneA
      let β := bar2Hom (restrictImg ψ hAL) (restrictImg_surjective ψ hAL)
      have hβ := bar2Hom_surjective (restrictImg ψ hAL) (restrictImg_surjective ψ hAL)
      have hβker := ker_bar2Hom_le_center (restrictImg ψ hAL) (restrictImg_surjective ψ hAL)
        (ker_restrictImg_le_center ψ hker hAL)
      have hsubA : CFSG.Open.IsSubnormal (imgSub ψ A) L' := by
        have h := isSubnormal_imgSub ψ hA.1 le_rfl
        rwa [imgSub_self ψ hψ] at h
      refine ⟨⟨hsubA, hperfA, ?_⟩, β, hβ, hβker, hntA⟩
      · have hqC : CFSG.IsQuasisimple (Bar2 A) :=
          (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hA.2.2
        have hnt : ∃ x : Bar2 A, β x ≠ 1 := by
          obtain ⟨y, hy⟩ := exists_ne (1 : Bar2 (imgSub ψ A))
          obtain ⟨x, rfl⟩ := hβ y
          exact ⟨x, hy⟩
        exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp
          (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqC (φ := β) hβ hnt)
    obtain ⟨hm₁, β₁, hβ₁, hk₁, hnt₁⟩ := hmem h₁
    obtain ⟨hm₂, β₂, hβ₂, hk₂, hnt₂⟩ := hmem h₂
    refine ⟨imgSub ψ L₁, imgSub ψ L₂, hm₁, hm₂, ?_, ?_, ?_⟩
    · rw [← imgSub_sup ψ hL₁ hL₂, ← hsup, imgSub_self ψ hψ]
    ·
      intro heq
      have hle : ∀ {A B : Subgroup G}, A ∈ calC L → B ∈ calC L → imgSub ψ A = imgSub ψ B →
          A ≤ B := by
        intro A B hA hB hAB
        have hAL : A ≤ L := hA.1.le
        have hlift : ∀ a ∈ A, ∃ b : ↥L, (b : G) ∈ B ∧ ∃ z ∈ Subgroup.center ↥L,
            a = ((b * z : ↥L) : G) := by
          intro a ha
          have : ((ψ ⟨a, hAL ha⟩ : ↥L') : G') ∈ imgSub ψ B := hAB ▸ mem_imgSub.mpr ⟨_, ha, rfl⟩
          obtain ⟨y, hy, hyx⟩ := mem_imgSub.mp this
          refine ⟨y, hy, y⁻¹ * ⟨a, hAL ha⟩, hker ?_, by simp⟩
          rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
          exact Subtype.ext hyx
        rw [← hA.2.1, Subgroup.commutator_le]
        intro a ha a' ha'
        obtain ⟨b, hb, z, hz, rfl⟩ := hlift a ha
        obtain ⟨b', hb', z', hz', rfl⟩ := hlift a' ha'
        have hc : ⁅((b * z : ↥L) : G), ((b' * z' : ↥L) : G)⁆ = ⁅(b : G), (b' : G)⁆ := by
          have := congrArg Subtype.val (commutator_mul_center (x := b) (y := b') hz hz')
          simpa [commutatorElement_def] using this
        rw [hc, ← hB.2.1]
        exact Subgroup.commutator_mem_commutator hb hb'
      exact hne₁₂ (le_antisymm (hle h₁ h₂ heq) (hle h₂ h₁ heq.symm))
    · intro M hM
      rcases hM with rfl | hM
      · rcases htypes L₁ (Or.inl rfl) with hSz | hL2 | ⟨hn3, hSU⟩
        · exact Or.inl (lieModel_of_surjective_of_isSimple
            (uc22p22r_lieModel_isSimple_twistedB2 hSz) β₁ hβ₁ hnt₁ hSz)
        · exact Or.inr (Or.inl (lieModel_of_surjective_of_isSimple
            (uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hL2) β₁ hβ₁ hnt₁ hL2))
        · exact Or.inr (Or.inr ⟨hn3, isSU3_of_surjective_central hSU β₁ hβ₁ hk₁ hnt₁⟩)
      · rw [Set.mem_singleton_iff] at hM
        subst hM
        rcases htypes L₂ (Or.inr rfl) with hSz | hL2 | ⟨hn3, hSU⟩
        · exact Or.inl (lieModel_of_surjective_of_isSimple
            (uc22p22r_lieModel_isSimple_twistedB2 hSz) β₂ hβ₂ hnt₂ hSz)
        · exact Or.inr (Or.inl (lieModel_of_surjective_of_isSimple
            (uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hL2) β₂ hβ₂ hnt₂ hL2))
        · exact Or.inr (Or.inr ⟨hn3, isSU3_of_surjective_central hSU β₂ hβ₂ hk₂ hnt₂⟩)

end NParam

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
