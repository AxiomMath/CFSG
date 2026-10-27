module

public import CFSG.Quasithin.Vol2.Ch12Sec4Mod
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Background.HMathieuStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.H.Mathieu (RealizesBy realizes_iff)

section Models

variable (K : Type) [Field K] [CharP K 2]

theorem zornO0Model_isActionModel {Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hΓ : Γ ≤ quasithinG2 K) : (zornO0Model Γ).IsActionModel where
  act_mul := zornAct_mul Γ
  act_one := zornAct_one Γ
  act_mul_act := zornAct_mul_act Γ
  sec_inv := fun γ _ hm => zornAct_mem_O0 Γ hΓ γ hm
  ker_inv := fun γ m hm => by
    have h1 : m = 1 := Subgroup.mem_bot.1 hm
    subst h1
    exact Subgroup.mem_bot.2 (act_map_one (zornAct Γ) γ (zornAct_mul Γ γ))
  ker_le := bot_le

@[expose] noncomputable def g2QAct :
    ↥(quasithinG2 K) →* MulAut (FFModel.zornQ (quasithinG2 K)).Mod :=
  (FFModel.zornQ_isActionModel (quasithinG2 K) le_rfl).modAct

@[expose] noncomputable def g2OAct :
    ↥(quasithinG2 K) →* MulAut (zornO0Model (quasithinG2 K)).Mod :=
  (zornO0Model_isActionModel K le_rfl).modAct

@[expose] def g2Derived : Subgroup ↥(quasithinG2 K) :=
  ⁅quasithinG2 K, quasithinG2 K⁆.subgroupOf (quasithinG2 K)

end Models

@[expose] def G2DerivedNormalizerZorn : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    (∀ x : MulAut (FFModel.zornQ (quasithinG2 K)).Mod,
      (∀ h, h ∈ (g2Derived K).map (g2QAct K) ↔ x * h * x⁻¹ ∈ (g2Derived K).map (g2QAct K)) →
        x ∈ (g2QAct K).range) ∧
    (∀ x : MulAut (zornO0Model (quasithinG2 K)).Mod,
      (∀ h, h ∈ (g2Derived K).map (g2OAct K) ↔ x * h * x⁻¹ ∈ (g2Derived K).map (g2OAct K)) →
        x ∈ (g2OAct K).range)

@[expose] def G2OffenderZorn : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    (∀ B : Subgroup (MulAut (FFModel.zornQ (quasithinG2 K)).Mod), B ≤ (g2QAct K).range →
      B ≠ ⊥ → IsElemAbelian2 B →
      Nat.card (FFModel.zornQ (quasithinG2 K)).Mod ≤ Nat.card B * Nat.card (fixV B) →
        commV B = fixV B) ∧
    (∀ B : Subgroup (MulAut (zornO0Model (quasithinG2 K)).Mod), B ≤ (g2OAct K).range →
      B ≠ ⊥ → IsElemAbelian2 B →
      Nat.card (zornO0Model (quasithinG2 K)).Mod ≤ Nat.card B * Nat.card (fixV B) →
        commV B = fixV B)

section Transport

variable {W M : Type} [CommGroup W] [CommGroup M] (e : W ≃* M)

theorem congr_apply_eq (a : MulAut W) (w : W) : MulAut.congr e a (e w) = e (a w) := by
  simp [MulAut.congr_apply]

theorem fixV_map_congr (A : Subgroup (MulAut W)) :
    fixV (A.map (MulAut.congr e).toMonoidHom) = (fixV A).map e.toMonoidHom :=
  fixV_map_congr_equiv e A

theorem commV_map_congr (A : Subgroup (MulAut W)) :
    commV (A.map (MulAut.congr e).toMonoidHom) = (commV A).map e.toMonoidHom :=
  commV_map_congr_equiv e A

theorem isElemAbelian2_map_congr {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) :
    IsElemAbelian2 (A.map (MulAut.congr e).toMonoidHom) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]

theorem offender_transport [Finite W] {X L₀ : Subgroup (MulAut W)}
    (hXN : X ≤ Subgroup.normalizer (L₀ : Set (MulAut W))) (Ĝ Ĥ : Subgroup (MulAut M))
    (hL : L₀.map (MulAut.congr e).toMonoidHom = Ĥ)
    (hN : ∀ x : MulAut M, (∀ h, h ∈ Ĥ ↔ x * h * x⁻¹ ∈ Ĥ) → x ∈ Ĝ)
    (hO : ∀ B : Subgroup (MulAut M), B ≤ Ĝ → B ≠ ⊥ → IsElemAbelian2 B →
      Nat.card M ≤ Nat.card B * Nat.card (fixV B) → commV B = fixV B)
    {A : Subgroup (MulAut W)} (hA : IsFFStarOffender X A) : commV A = fixV A := by
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  obtain ⟨hAX, hA1, hAe, hbest⟩ := hA
  have hle : A.map (MulAut.congr e).toMonoidHom ≤ Ĝ := by
    rintro _ ⟨a, ha, rfl⟩
    apply hN
    intro h
    have hx := Subgroup.mem_set_normalizer_iff.1 (hXN (hAX ha))
    rw [← hL]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨a * l * a⁻¹, (hx l).1 hl, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨l, hl, hl'⟩
      refine ⟨a⁻¹ * l * a, ?_, ?_⟩
      · have e1 : a * (a⁻¹ * l * a) * a⁻¹ = l := by group
        exact (hx _).2 (by rw [e1]; exact hl)
      · rw [map_mul, map_mul, map_inv, hl']
        group
  have hne : A.map (MulAut.congr e).toMonoidHom ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h)
  have hff : Nat.card M ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom) *
      Nat.card (fixV (A.map (MulAut.congr e).toMonoidHom)) := by
    have h0 := hbest ⊥ bot_le
    rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at h0
    rw [Subgroup.card_map_of_injective hφinj, fixV_map_congr,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, ← Nat.card_congr e.toEquiv]
    exact h0
  have h := hO _ hle hne (isElemAbelian2_map_congr e hAe) hff
  rw [commV_map_congr, fixV_map_congr] at h
  exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h

end Transport

section Realization

variable {W : Type} [CommGroup W] {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def realizeEquiv {D : FFModel} {L : Subgroup (MulAut W)}
    {π : D.Gam →* ↥L} {β : ↥(⊤ : Subgroup W) →* D.Mod} (h : RealizesBy D L ⊤ ⊥ π β) :
    W ≃* D.Mod :=
  MulEquiv.ofBijective (β.comp (Subgroup.topEquiv : (⊤ : Subgroup W) ≃* W).symm.toMonoidHom)
    ⟨(injective_iff_map_eq_one _).2 fun w hw => by
        have h1 := (h.2.2.2.2.2.2.2.2.1 ⟨w, trivial⟩).1 hw
        exact Subgroup.mem_bot.1 h1,
      fun m => by
        obtain ⟨u, hu⟩ := h.2.2.2.2.2.2.2.1 m
        exact ⟨u.1, by rw [← hu]; rfl⟩⟩

theorem map_congr_eq_of_equivariant {M : Type} [CommGroup M] (e : W ≃* M) {Γ G' : Type}
    [Group Γ] [Group G'] {L₀ : Subgroup (MulAut W)} (π : Γ →* ↥L₀) (hπ : Function.Surjective π)
    (ρ : G' →* MulAut M) (ι : Γ → G') (hρ : ∀ γ w, e ((π γ : MulAut W) w) = ρ (ι γ) (e w))
    (Ĥ : Subgroup (MulAut M)) (hĤ : ∀ g, g ∈ Ĥ ↔ ∃ γ, ρ (ι γ) = g) :
    L₀.map (MulAut.congr e).toMonoidHom = Ĥ := by
  have key : ∀ γ, MulAut.congr e (π γ : MulAut W) = ρ (ι γ) := by
    intro γ
    ext m
    obtain ⟨w, rfl⟩ := e.surjective m
    rw [congr_apply_eq, hρ]
  ext y
  rw [hĤ]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨γ, hγ⟩ := hπ ⟨l, hl⟩
    refine ⟨γ, ?_⟩
    rw [← key γ, hγ]
    rfl
  · rintro ⟨γ, rfl⟩
    exact ⟨_, (π γ).2, key γ⟩

theorem realizeEquiv_zornQ {L₀ : Subgroup (MulAut W)}
    {π : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam →* ↥L₀}
    {β : ↥(⊤ : Subgroup W) →* (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Mod}
    (h : RealizesBy (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) L₀ ⊤ ⊥ π β)
    (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (w : W) :
    (realizeEquiv (D := FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) h :
      W ≃* (FFModel.zornQ (quasithinG2 K)).Mod) ((π γ : MulAut W) w) =
      g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩
        ((realizeEquiv (D := FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) h :
      W ≃* (FFModel.zornQ (quasithinG2 K)).Mod) w) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
  have hm' : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act γ (m : Multiplicative _) ∈
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec :=
    zornAct_mem_O0 _ (Subgroup.commutator_le_self _) γ m.2
  have h1 := h.2.2.2.2.2.2.2.2.2 γ ⟨w, trivial⟩ m trivial hm' hm.symm
  change β ⟨(π γ : MulAut W) w, trivial⟩ = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩
    (β ⟨w, trivial⟩)
  rw [← hm]
  exact h1

theorem realizeEquiv_zornO0 {L₀ : Subgroup (MulAut W)}
    {π : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Gam →* ↥L₀}
    {β : ↥(⊤ : Subgroup W) →* (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Mod}
    (h : RealizesBy (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆) L₀ ⊤ ⊥ π β)
    (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (w : W) :
    (realizeEquiv (D := zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆) h :
      W ≃* (zornO0Model (quasithinG2 K)).Mod) ((π γ : MulAut W) w) =
      g2OAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩
        ((realizeEquiv (D := zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆) h :
      W ≃* (zornO0Model (quasithinG2 K)).Mod) w) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
  have hm' : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).act γ (m : Multiplicative _) ∈
      (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec :=
    zornAct_mem_O0 _ (Subgroup.commutator_le_self _) γ m.2
  have h1 := h.2.2.2.2.2.2.2.2.2 γ ⟨w, trivial⟩ m trivial hm' hm.symm
  change β ⟨(π γ : MulAut W) w, trivial⟩ = g2OAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩
    (β ⟨w, trivial⟩)
  rw [← hm]
  exact h1

omit [CharP K 2] in
theorem mem_map_g2Derived_iff {M : Type} [Group M] (ρ : ↥(quasithinG2 K) →* M) (g : M) :
    g ∈ (g2Derived K).map ρ ↔
      ∃ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆,
        ρ ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.2 γ.2, rfl⟩

end Realization

theorem charP_two_of_natCard_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])

theorem b46OffenderCommEqFix_of (hcov : G2NaturalCover) (hnorm : G2DerivedNormalizerZorn)
    (hoff : G2OffenderZorn) : B46OffenderCommEqFix := by
  intro W _ _ hW X L₀ _ hXN _ hcomm hnat A hA
  rcases hcov W hW L₀ (fixV L₀) le_rfl hcomm hnat with hZ | ⟨-, -, hWeyl⟩
  · rw [hZ] at hnat
    obtain ⟨K, _, _, hK, hR⟩ := hnat
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have := charP_two_of_natCard_two hK2
    obtain ⟨π, β, hβ⟩ := (realizes_iff _ L₀ ⊤ ⊥).1 hR
    let e : W ≃* (FFModel.zornQ (quasithinG2 K)).Mod :=
      realizeEquiv (D := FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) hβ
    refine offender_transport e hXN (g2QAct K).range ((g2Derived K).map (g2QAct K)) ?_
      (hnorm K hK2).1 (hoff K hK2).1 hA
    exact map_congr_eq_of_equivariant e π hβ.1 (g2QAct K)
      (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (realizeEquiv_zornQ hβ) _
      (mem_map_g2Derived_iff (g2QAct K))
  · obtain ⟨K, _, _, hK2, hR⟩ := hWeyl
    have := charP_two_of_natCard_two hK2
    obtain ⟨π, β, hβ⟩ := (realizes_iff _ L₀ ⊤ ⊥).1 hR
    let e : W ≃* (zornO0Model (quasithinG2 K)).Mod :=
      realizeEquiv (D := zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆) hβ
    refine offender_transport e hXN (g2OAct K).range ((g2Derived K).map (g2OAct K)) ?_
      (hnorm K hK2).2 (hoff K hK2).2 hA
    exact map_congr_eq_of_equivariant e π hβ.1 (g2OAct K)
      (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (realizeEquiv_zornO0 hβ) _
      (mem_map_g2Derived_iff (g2OAct K))

end CFSG.Quasithin.H13
