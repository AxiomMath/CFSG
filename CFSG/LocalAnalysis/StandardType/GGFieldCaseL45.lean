module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Choice

theorem ggL45_rawDatum_exists_of {lab : LargeEvenLabel} {Q : LargeEvenRawCont} {α : Type*}
    {Q' : α → LargeEvenRawCont}
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → ∃ a, Q' a R I F)
    (h : LargeEvenRawDatum lab Q) : ∃ a, LargeEvenRawDatum lab (Q' a) := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       obtain ⟨a, ha⟩ := hQ _ _ _ hq
       exact ⟨a, K, i1, i2, hK, b, c, hbc, ha⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       obtain ⟨a, ha⟩ := hQ _ _ _ hq
       exact ⟨a, K, i1, i2, hK, ha⟩)

theorem ggL45_marking_exists_of {X : Type*} [Group X] {P : LargeEvenMarkProp X} {α : Type*}
    {P' : α → LargeEvenMarkProp X}
    (hP : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → ∃ a, P' a lab R I F θ)
    (h : LargeEvenMarking X P) : ∃ a, LargeEvenMarking X (P' a) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨a, ha⟩ := ggL45_rawDatum_exists_of (lab := lab)
    (Q' := fun a R _ I F => IsSimpleGroup R ∧ (∃ g h : R, g * h ≠ h * g) ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* R, P' a lab R I F θ)
    (fun R _ I F hq => by
      obtain ⟨hs, hna, θ, hθ⟩ := hq
      obtain ⟨a, ha⟩ := hP lab R I F θ hθ
      exact ⟨a, hs, hna, θ, ha⟩) hraw
  exact ⟨a, hX, lab, hlab, ha⟩

end Choice

section Part

variable {G : Type} [Group G] {K : Subgroup G} {R : Type} [Group R]
  {θ : K ⧸ Subgroup.center K ≃* R} {I : Set (MulAut R)}

theorem ggL45_mem_ggInndiag_iff (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I)
    (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) (hinn : ∀ r : R, MulAut.conj r ∈ I) {φ : MulAut R} :
    φ ∈ ggInndiag R I ↔ φ ∈ I := by
  refine ⟨fun h => ?_, fun h => subset_ggInndiag h⟩
  let S : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun ha hb => hmul _ ha _ hb
      one_mem' := by simpa using hinn 1
      inv_mem' := fun ha => hinv _ ha }
  have hle : ggInndiag R I ≤ S :=
    sup_le (by rintro _ ⟨r, rfl⟩; exact hinn r) ((Subgroup.closure_le S).mpr fun _ h => h)
  exact hle h

theorem ggL45_exists_induces_iff (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) {u : G}
    (hu : u ∈ Subgroup.normalizer (K : Set G)) :
    (∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ) ↔
      ggLAut K θ ⟨u, hu⟩ ∈ I := by
  have hinvu : ggLAut K θ ⟨u⁻¹, inv_mem hu⟩ = (ggLAut K θ ⟨u, hu⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  constructor
  · rintro ⟨φ, hφ, hind⟩
    rw [eq_ggLAut_of_induces K θ hu hind, hinvu] at hφ
    simpa using hinv _ hφ
  · intro h
    refine ⟨ggLAut K θ ⟨u⁻¹, inv_mem hu⟩, by rw [hinvu]; exact hinv _ h, ?_⟩
    intro k k' hkk'
    rw [ggLAut_apply]
    congr 2
    apply Subtype.ext
    rw [normalizerMonoidHom_coe, hkk', inv_inv]

variable (K θ I) in
@[expose] noncomputable def ggInnerDiagPartOf (U : Subgroup G) : Subgroup G :=
  U ⊓ ggInndiagPre K θ I

theorem mem_ggInnerDiagPartOf_iff (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I)
    (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) (hinn : ∀ r : R, MulAut.conj r ∈ I) {U : Subgroup G}
    (hU : U ≤ Subgroup.normalizer (K : Set G)) {u : G} (hu : u ∈ U) :
    u ∈ ggInnerDiagPartOf K θ I U ↔
      ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ := by
  rw [ggL45_exists_induces_iff hinv (hU hu), ggInnerDiagPartOf, Subgroup.mem_inf,
    mem_ggInndiagPre_iff]
  constructor
  · rintro ⟨-, _, h⟩
    exact (ggL45_mem_ggInndiag_iff hmul hinv hinn).mp h
  · intro h
    exact ⟨hu, hU hu, (ggL45_mem_ggInndiag_iff hmul hinv hinn).mpr h⟩

theorem ggL45_normalizer_le_normalizer_ggInndiagPre (hN : GGInndiagNormal R I) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (ggInndiagPre K θ I : Set G) :=
  Subgroup.le_normalizer_iff.mpr fun _ hn _ hg => conj_mem_ggInndiagPre hN hn hg

theorem normalizer_inf_le_normalizer_ggInnerDiagPartOf (hN : GGInndiagNormal R I)
    (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (ggInnerDiagPartOf K θ I U : Set G) :=
  (inf_le_inf_left _ (ggL45_normalizer_le_normalizer_ggInndiagPre hN)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

end Part

@[expose] def GGL45MovingInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCase p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      GGL44iii p B Bs x D J X d y K → GGL45Setup p Bs X U → GGInnerDiagPart U K U₁ →
      Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer (U₁ : Set G) →
      ∀ r ∈ Subgroup.normalizer (U : Set G) ⊓
          Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
        r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
          r ∈ Subgroup.normalizer (U₁ : Set G)

@[expose] def GGRawInnSubgroup : LargeEvenRawCont :=
  fun R _ I _ => (∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) ∧ (∀ φ ∈ I, φ⁻¹ ∈ I) ∧
    ∀ r : R, MulAut.conj r ∈ I

@[expose] def GGRawInnSubgroupInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGRawInnSubgroup)

theorem ggRawInnSubgroupInput_of_rawInnField (h : GGRawInnFieldInput) :
    GGRawInnSubgroupInput := fun lab hl =>
  (h 3 Nat.prime_three (by decide) lab hl).mono fun _ _ _ _ h hs hna =>
    ⟨(h hs hna).1, (h hs hna).2.1, (h hs hna).2.2.1⟩

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggL45_normalizer_le_of_canonical {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X : Subgroup G} {d y : G} {K : Subgroup G} (hFC : GGFieldCase p B Bs x L D J X)
    (hK : GGL44iii p B Bs x D J X d y K) :
    Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, hBL5, hXN, hCX, hXn, hXp, hXC⟩ := hFC
  have hd : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hK.1]
    exact Subgroup.mem_zpowers d
  exact hBL5 X hXN hCX hXn hXp hXC d hd hK.2.1 y K hK.2.2.1 hK.2.2.2.1

theorem ggL45Input_of_moving (hN : GGInndiagNormalInput) (hsub : GGRawInnSubgroupInput)
    (hmov : GGL45MovingInput) : GGL45Input := by
  intro G _ _ p B Bs x L D J X B₂ d y K U hFC hTBM hL43 hL44 hL44ii hK hsetup hUK
  have hM1 := largeEvenMarking_and_labelAll_simple (S := fun _ => True) (P' := GGRawInnSubgroup)
    (fun lab hl _ => hsub lab hl) (fun _ _ _ _ _ _ _ => trivial) hK.2.2.2.2
  have hM2 := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := fun R _ I _ => GGInndiagNormal R I) (fun lab hl _ => hN lab hl)
    (fun _ _ _ _ _ _ _ => trivial) hM1
  obtain ⟨U₁, hU₁⟩ := ggL45_marking_exists_of (X := ↥K)
    (P' := fun U₁ _ _ _ I _ θ => U₁ ≤ U ∧
      (∀ u ∈ U, u ∈ U₁ ↔
        ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ) ∧
      Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer (U₁ : Set G))
    (fun _ _ _ I _ θ h => by
      obtain ⟨⟨-, hmul, hinv, hinn⟩, hNn⟩ := h
      exact ⟨ggInnerDiagPartOf K θ I U, inf_le_left,
        fun u hu => mem_ggInnerDiagPartOf_iff hmul hinv hinn hUK hu,
        normalizer_inf_le_normalizer_ggInnerDiagPartOf hNn U⟩) hM2
  obtain ⟨-, lab, -, hraw'⟩ := id hU₁
  obtain ⟨R, _, I, F, -, -, θ, hle, -, hon⟩ := largeEvenRawDatum_exists hraw'
  have hpart : GGInnerDiagPart U K U₁ :=
    ⟨hUK, hle, largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2.1) hU₁⟩
  refine ⟨U₁, hpart, fun r hr => ?_⟩
  by_cases hrd : r ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)
  · exact hon ⟨hr.1, ggL45_normalizer_le_of_canonical hFC hK ⟨hr.2, hrd⟩⟩
  · exact hmov G p B Bs x L D J X B₂ d y K U U₁ hFC hTBM hL43 hL44 hL44ii hK hsetup hpart hon
      r hr hrd

theorem ggL45Input_of_moving_rawInnField (hN : GGInndiagNormalInput)
    (hraw : GGRawInnFieldInput) (hmov : GGL45MovingInput) : GGL45Input :=
  ggL45Input_of_moving hN (ggRawInnSubgroupInput_of_rawInnField hraw) hmov

end Main

end CFSG.StandardType

end
