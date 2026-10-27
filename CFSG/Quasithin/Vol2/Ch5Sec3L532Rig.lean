module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigSwapMain
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Rig

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

variable {D : Type} [Group D]

@[expose] noncomputable def innExt [Finite D] {TD P₁ P₂ : Subgroup D}
    (hY : IsYAmalgamPair TD P₁ P₂) : LieAmalgamExt D where
  Mbar := (MulAut.conj : D →* MulAut D).range
  TD := TD
  P1 := P₁
  P2 := P₂
  inn_le := le_rfl
  yam := hY
  diag := by
    rintro _ ⟨d, rfl⟩ hB
    have hd : d ∈ P₁ ⊓ P₂ := by
      rw [← S1421QA18.normalizer_inf_eq hY]
      exact S1421QA18.conj_mem_autStab_iff.mp hB
    refine S1421QA18.conj_mem_autStab_iff.mpr ?_
    rw [S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_left hY)]
    exact hd.1

@[expose] noncomputable def innEquiv (hZ : Subgroup.center D = ⊥) {P : Subgroup D}
    (hP : Subgroup.normalizer (P : Set D) = P) :
    ↥P ≃* ↥((MulAut.conj : D →* MulAut D).range ⊓ autStab P) :=
  MulEquiv.ofBijective
    (((MulAut.conj : D →* MulAut D).comp P.subtype).codRestrict
      ((MulAut.conj : D →* MulAut D).range ⊓ autStab P) fun p =>
        ⟨⟨(p : D), rfl⟩, S1421QA18.conj_mem_autStab_iff.mpr (Subgroup.le_normalizer p.2)⟩)
    ⟨fun p q h => Subtype.ext (F48Rig.conj_injective_of_center hZ (congrArg Subtype.val h)),
      fun ⟨φ, ⟨d, hd⟩, hφ⟩ => by
        subst hd
        have hdP : d ∈ P := hP ▸ S1421QA18.conj_mem_autStab_iff.mp hφ
        exact ⟨⟨d, hdP⟩, rfl⟩⟩

@[expose] noncomputable def innAut (hZ : Subgroup.center D = ⊥) {P : Subgroup D}
    (hP : Subgroup.normalizer (P : Set D) = P) (a : MulAut ↥P) :
    MulAut ↥((MulAut.conj : D →* MulAut D).range ⊓ autStab P) :=
  ((innEquiv hZ hP).symm.trans a).trans (innEquiv hZ hP)

theorem innAut_innEquiv (hZ : Subgroup.center D = ⊥) {P : Subgroup D}
    (hP : Subgroup.normalizer (P : Set D) = P) (a : MulAut ↥P) (p : ↥P) :
    innAut hZ hP a (innEquiv hZ hP p) = innEquiv hZ hP (a p) := by
  simp [innAut]

theorem amalgamRigid_of_f48 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hm : F431ModelFacts t m f) (h45 : F431Facts45 t m f hm) (hgen : F431Generation t m f)
    (hT : ∀ (D : Type) [Group D] (hD : CFSG.Blueprint.LieModel D t m 2 f) (A : LieAmalgamExt D),
      (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).CartanFPF ∨
        (A.swap.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).CartanFPF)
    (hF : ∀ (D : Type) [Group D] (hD : CFSG.Blueprint.LieModel D t m 2 f) (A : LieAmalgamExt D),
      (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).FaithfulOnType
        (decide (Odd (polyNumber t))))
    (D : Type) [Group D] (hD : CFSG.Blueprint.LieModel D t m 2 f) {TD P₁ P₂ : Subgroup D}
    (hY : IsYAmalgamPair TD P₁ P₂) : S1421QA18.AmalgamRigid P₁ P₂ := by
  classical
  have hfin : Finite D := (hm D hD).1
  have hZ : Subgroup.center D = ⊥ := (hm D hD).2
  have : Finite (MulAut D) := finite_mulAut_of_finite
  have hN1 : Subgroup.normalizer (P₁ : Set D) = P₁ :=
    S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_left hY)
  have hN2 : Subgroup.normalizer (P₂ : Set D) = P₂ :=
    S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_right hY)
  let A : LieAmalgamExt D := innExt hY
  have hKinn : A.K ≤ (MulAut.conj : D →* MulAut D).range :=
    sup_le inf_le_left inf_le_left
  have hinnK : (MulAut.conj : D →* MulAut D).range ≤ A.K := hgen D hD A
  let κ : D ≃* ↥A.K := MulEquiv.ofBijective
    ((MulAut.conj : D →* MulAut D).codRestrict A.K fun d => hinnK ⟨d, rfl⟩)
    ⟨fun a b h => F48Rig.conj_injective_of_center hZ (congrArg Subtype.val h), fun k => by
      obtain ⟨d, hd⟩ := hKinn k.2
      exact ⟨d, Subtype.ext hd⟩⟩
  have hsup : P₁ ⊔ P₂ = ⊤ := by
    have hNle : ∀ {P : Subgroup D}, Subgroup.normalizer (P : Set D) = P → P ≤ P₁ ⊔ P₂ →
        (MulAut.conj : D →* MulAut D).range ⊓ autStab P ≤
          (P₁ ⊔ P₂).map (MulAut.conj : D →* MulAut D) := by
      rintro P hP hle _ ⟨⟨d, rfl⟩, hd⟩
      exact ⟨d, hle (hP ▸ S1421QA18.conj_mem_autStab_iff.mp hd), rfl⟩
    have hK : A.K ≤ (P₁ ⊔ P₂).map (MulAut.conj : D →* MulAut D) :=
      sup_le (hNle hN1 le_sup_left) (hNle hN2 le_sup_right)
    rw [eq_top_iff]
    intro d _
    obtain ⟨p, hp, hpd⟩ := hK (hinnK ⟨d, rfl⟩)
    rwa [F48Rig.conj_injective_of_center hZ hpd] at hp
  refine ⟨hsup, fun a₁ a₂ hagr => ?_⟩
  let b₁ : MulAut ↥A.N1 := innAut hZ hN1 a₁
  let b₂ : MulAut ↥A.N2 := innAut hZ hN2 a₂
  have hB12 : ∀ (x : D) (h₁ : x ∈ P₁) (h₂ : x ∈ P₂), ((a₁ ⟨x, h₁⟩ : ↥P₁) : D) ∈ P₂ := by
    intro x h₁ h₂
    rw [hagr x h₁ h₂]
    exact (a₂ ⟨x, h₂⟩).2
  have hsurj12 : ∀ q : D, q ∈ P₁ → q ∈ P₂ →
      ∃ (x : D) (h₁ : x ∈ P₁), x ∈ P₂ ∧ ((a₁ ⟨x, h₁⟩ : ↥P₁) : D) = q := by
    let g : ↥(P₁ ⊓ P₂) → ↥(P₁ ⊓ P₂) := fun b =>
      ⟨((a₁ ⟨b.1, b.2.1⟩ : ↥P₁) : D), (a₁ ⟨b.1, b.2.1⟩).2, hB12 b.1 b.2.1 b.2.2⟩
    have hginj : Function.Injective g := fun b b' h => by
      have h1 : ((a₁ ⟨b.1, b.2.1⟩ : ↥P₁) : D) = ((a₁ ⟨b'.1, b'.2.1⟩ : ↥P₁) : D) :=
        congrArg (fun z : ↥(P₁ ⊓ P₂) => (z : D)) h
      have h2 := a₁.injective (Subtype.ext h1)
      exact Subtype.ext (Subtype.mk.inj h2)
    intro q hq1 hq2
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hginj ⟨q, hq1, hq2⟩
    have hbq := congrArg (fun z : ↥(P₁ ⊓ P₂) => (z : D)) hb
    exact ⟨b.1, b.2.1, b.2.2, hbq⟩
  let β1 : ↥A.N1 →* ↥A.K := (Subgroup.inclusion A.N1_le_K).comp b₁.toMonoidHom
  let β2 : ↥A.N2 →* ↥A.K := (Subgroup.inclusion A.N2_le_K).comp b₂.toMonoidHom
  have hβ1 : ∀ p : ↥P₁, ((β1 (innEquiv hZ hN1 p) : ↥A.K) : MulAut D) =
      MulAut.conj ((a₁ p : ↥P₁) : D) := fun p => by
    show ((b₁ (innEquiv hZ hN1 p) : ↥A.N1) : MulAut D) = _
    rw [show b₁ (innEquiv hZ hN1 p) = innEquiv hZ hN1 (a₁ p) from innAut_innEquiv hZ hN1 a₁ p]
    rfl
  have hβ2 : ∀ p : ↥P₂, ((β2 (innEquiv hZ hN2 p) : ↥A.K) : MulAut D) =
      MulAut.conj ((a₂ p : ↥P₂) : D) := fun p => by
    show ((b₂ (innEquiv hZ hN2 p) : ↥A.N2) : MulAut D) = _
    rw [show b₂ (innEquiv hZ hN2 p) = innEquiv hZ hN2 (a₂ p) from innAut_innEquiv hZ hN2 a₂ p]
    rfl
  have hmemP : ∀ {P : Subgroup D}, Subgroup.normalizer (P : Set D) = P → ∀ d : D,
      MulAut.conj d ∈ autStab P → d ∈ P := fun hP d hd =>
    hP ▸ S1421QA18.conj_mem_autStab_iff.mp hd
  have hag : ∀ (x : MulAut D) (h1 : x ∈ A.N1) (h2 : x ∈ A.N2),
      β1 ⟨x, h1⟩ = β2 ⟨x, h2⟩ := by
    intro x h1 h2
    obtain ⟨d, rfl⟩ := h1.1
    have hd1 : d ∈ P₁ := hmemP hN1 d h1.2
    have hd2 : d ∈ P₂ := hmemP hN2 d h2.2
    have v1 : ((β1 ⟨MulAut.conj d, h1⟩ : ↥A.K) : MulAut D) =
        MulAut.conj ((a₁ ⟨d, hd1⟩ : ↥P₁) : D) := hβ1 ⟨d, hd1⟩
    have v2 : ((β2 ⟨MulAut.conj d, h2⟩ : ↥A.K) : MulAut D) =
        MulAut.conj ((a₂ ⟨d, hd2⟩ : ↥P₂) : D) := hβ2 ⟨d, hd2⟩
    apply Subtype.ext
    show ((β1 ⟨MulAut.conj d, h1⟩ : ↥A.K) : MulAut D) =
      ((β2 ⟨MulAut.conj d, h2⟩ : ↥A.K) : MulAut D)
    rw [v1, v2, hagr d hd1 hd2]
  have hrange1 : β1.range = (Subgroup.inclusion A.N1_le_K).range := by
    show ((Subgroup.inclusion A.N1_le_K).comp b₁.toMonoidHom).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr b₁.surjective, Subgroup.map_top]
  have hrange2 : β2.range = (Subgroup.inclusion A.N2_le_K).range := by
    show ((Subgroup.inclusion A.N2_le_K).comp b₂.toMonoidHom).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr b₂.surjective, Subgroup.map_top]
  have hint : ∀ y : ↥A.K, y ∈ β1.range → y ∈ β2.range →
      ∃ (x : MulAut D) (h1 : x ∈ A.N1) (_ : x ∈ A.N2), β1 ⟨x, h1⟩ = y := by
    rintro y ⟨⟨x₁, hx₁⟩, rfl⟩ ⟨⟨x₂, hx₂⟩, hn₂⟩
    obtain ⟨d₁, rfl⟩ := hx₁.1
    obtain ⟨d₂, rfl⟩ := hx₂.1
    have hd₁ : d₁ ∈ P₁ := hmemP hN1 d₁ hx₁.2
    have hd₂ : d₂ ∈ P₂ := hmemP hN2 d₂ hx₂.2
    have v1 : ((β1 ⟨MulAut.conj d₁, hx₁⟩ : ↥A.K) : MulAut D) =
        MulAut.conj ((a₁ ⟨d₁, hd₁⟩ : ↥P₁) : D) := hβ1 ⟨d₁, hd₁⟩
    have v2 : ((β2 ⟨MulAut.conj d₂, hx₂⟩ : ↥A.K) : MulAut D) =
        MulAut.conj ((a₂ ⟨d₂, hd₂⟩ : ↥P₂) : D) := hβ2 ⟨d₂, hd₂⟩
    have hq : ((a₂ ⟨d₂, hd₂⟩ : ↥P₂) : D) = ((a₁ ⟨d₁, hd₁⟩ : ↥P₁) : D) := by
      apply F48Rig.conj_injective_of_center hZ
      rw [← v1, ← v2]
      exact congrArg Subtype.val hn₂
    have hq2 : ((a₁ ⟨d₁, hd₁⟩ : ↥P₁) : D) ∈ P₂ := hq ▸ (a₂ ⟨d₂, hd₂⟩).2
    obtain ⟨x, hx1, hx2, hxq⟩ := hsurj12 _ (a₁ ⟨d₁, hd₁⟩).2 hq2
    have hmem1 : MulAut.conj x ∈ A.N1 :=
      ⟨⟨x, rfl⟩, S1421QA18.conj_mem_autStab_iff.mpr (Subgroup.le_normalizer hx1)⟩
    have hmem2 : MulAut.conj x ∈ A.N2 :=
      ⟨⟨x, rfl⟩, S1421QA18.conj_mem_autStab_iff.mpr (Subgroup.le_normalizer hx2)⟩
    refine ⟨MulAut.conj x, hmem1, hmem2, Subtype.ext ?_⟩
    have w1 : ((β1 ⟨MulAut.conj x, hmem1⟩ : ↥A.K) : MulAut D) =
        MulAut.conj ((a₁ ⟨x, hx1⟩ : ↥P₁) : D) := hβ1 ⟨x, hx1⟩
    show ((β1 ⟨MulAut.conj x, hmem1⟩ : ↥A.K) : MulAut D) =
      ((β1 ⟨MulAut.conj d₁, hx₁⟩ : ↥A.K) : MulAut D)
    rw [w1, v1, hxq]
  have hgenβ : β1.range ⊔ β2.range = ⊤ := by
    rw [hrange1, hrange2]
    exact RankTwoAmalgam.range_inclusion_sup_eq_top A.N1 A.N2 A.K rfl
  let β := completionOf A β1 β2 hag hint hgenβ
  have hβ1inj : Function.Injective β1 := fun a b h => by
    have h1 : ((b₁ a : ↥A.N1) : MulAut D) = ((b₁ b : ↥A.N1) : MulAut D) :=
      congrArg (fun k : ↥A.K => (k : MulAut D)) h
    exact b₁.injective (Subtype.ext h1)
  have hβ2inj : Function.Injective β2 := fun a b h => by
    have h1 : ((b₂ a : ↥A.N2) : MulAut D) = ((b₂ b : ↥A.N2) : MulAut D) :=
      congrArg (fun k : ↥A.K => (k : MulAut D)) h
    exact b₂.injective (Subtype.ext h1)
  have hβ : β.IsFaithful := by
    refine ⟨hβ1inj, fun (a b : ↥(A.N1 ⊓ A.N2)) h => ?_, hβ2inj⟩
    have h1 : Subgroup.inclusion (inf_le_left : A.N1 ⊓ A.N2 ≤ A.N1) a =
        Subgroup.inclusion (inf_le_left : A.N1 ⊓ A.N2 ≤ A.N1) b := hβ1inj h
    have h2 : (a : MulAut D) = (b : MulAut D) :=
      congrArg (fun k : ↥A.N1 => (k : MulAut D)) h1
    exact Subtype.ext h2
  have hs : β.IsSmall (polyNumber t) :=
    (h45 D hD A).small_of_card_le β hβ le_rfl
  have heq : Amalgam.Completion.IsEquivalent β.toCompletion
      (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).ι.toCompletion := by
    rcases hT D hD A with hC | hC
    · obtain ⟨θ, h1, h2⟩ := F48Rig.exists_equiv_small (h45 D hD A) β hβ hs hC (hF D hD A)
      exact F48Rig.isEquivalent_of_equiv
        (S := A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)) β θ h1 h2
    · exact A.isEquivalent_of_cartan_swap _ _ _ (h45 D hD A.swap) hC (hF D hD A.swap) β hβ hs
  obtain ⟨φ, hφ⟩ := heq
  have hφ1 : ∀ n : ↥A.N1, φ (β1 n) = Subgroup.inclusion A.N1_le_K n := fun n =>
    hφ RankTwoIndex.one n
  have hφ2 : ∀ n : ↥A.N2, φ (β2 n) = Subgroup.inclusion A.N2_le_K n := fun n =>
    hφ RankTwoIndex.two n
  refine ⟨κ.trans (φ.symm.trans κ.symm), fun x h => ?_, fun x h => ?_⟩
  · have e1 : κ x = Subgroup.inclusion A.N1_le_K (innEquiv hZ hN1 ⟨x, h⟩) := Subtype.ext rfl
    have e2 : φ.symm (κ x) = β1 (innEquiv hZ hN1 ⟨x, h⟩) :=
      φ.symm_apply_eq.mpr (e1.trans (hφ1 _).symm)
    have e3 : β1 (innEquiv hZ hN1 ⟨x, h⟩) = κ ((a₁ ⟨x, h⟩ : ↥P₁) : D) :=
      Subtype.ext (hβ1 ⟨x, h⟩)
    show κ.symm (φ.symm (κ x)) = _
    rw [e2, e3, MulEquiv.symm_apply_apply]
  · have e1 : κ x = Subgroup.inclusion A.N2_le_K (innEquiv hZ hN2 ⟨x, h⟩) := Subtype.ext rfl
    have e2 : φ.symm (κ x) = β2 (innEquiv hZ hN2 ⟨x, h⟩) :=
      φ.symm_apply_eq.mpr (e1.trans (hφ2 _).symm)
    have e3 : β2 (innEquiv hZ hN2 ⟨x, h⟩) = κ ((a₂ ⟨x, h⟩ : ↥P₂) : D) :=
      Subtype.ext (hβ2 ⟨x, h⟩)
    show κ.symm (φ.symm (κ x)) = _
    rw [e2, e3, MulEquiv.symm_apply_apply]

end CFSG.Quasithin.H13.L532
