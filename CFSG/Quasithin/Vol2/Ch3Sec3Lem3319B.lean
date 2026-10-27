module

public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.H13.L3319

open CFSG.Open (pCoreOf quasithinOmegaOneCenter quasithinG2)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G]

omit [Group G] in
theorem conjAct_coe {G : Type} [Group G] (V : Subgroup G) (g : Subgroup.normalizer (V : Set G))
    (v : V) : ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g v

noncomputable abbrev conjOf (V H : Subgroup G) (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    ↥H →* MulAut ↥V :=
  (conjAct V).comp (Subgroup.inclusion hH)

theorem conjOf_coe {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) (h : ↥H)
    (v : V) : ((conjOf V H hH h v : V) : G) = h * v * (h : G)⁻¹ :=
  conjAct_coe V (Subgroup.inclusion hH h) v

theorem map_conjOf {V H S : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) (hSH : S ≤ H) :
    (S.subgroupOf H).map (conjOf V H hH) = autOn S V := by
  ext a
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨Subgroup.inclusion hH h,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hh), rfl⟩
  · rintro ⟨n, hn, rfl⟩
    have hnS : (n : G) ∈ S := Subgroup.mem_subgroupOf.mp hn
    exact ⟨⟨n, hSH hnS⟩, Subgroup.mem_subgroupOf.mpr hnS, rfl⟩

theorem range_conjOf {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    (conjOf V H hH).range = autOn H V := by
  rw [MonoidHom.range_eq_map, ← map_conjOf hH le_rfl, Subgroup.subgroupOf_self]

theorem conjOf_eq_one_iff {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) (h : ↥H) :
    conjOf V H hH h = 1 ↔ (h : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h1
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h1
    simp only [conjOf_coe, MulAut.one_apply] at this
    calc v * (h : G) = ((h : G) * v * (h : G)⁻¹) * h := by rw [this]
      _ = h * v := by group
  · intro hc
    ext v
    rw [conjOf_coe, MulAut.one_apply]
    rw [← Subgroup.mem_centralizer_iff.mp hc v v.2, mul_inv_cancel_right]

theorem autOn_le_normalizer {V H P : Subgroup G} (hHP : H ≤ Subgroup.normalizer (P : Set G)) :
    autOn H V ≤ Subgroup.normalizer (autOn P V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hHP

omit [Group G] in
theorem perfectCore_subgroupOf {G : Type} [Group G] [Finite G] {H K : Subgroup G} (hHK : H ≤ K) :
    (perfectCore H).subgroupOf K = perfectCore (H.subgroupOf K) := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le H).trans hHK), map_perfectCore,
    Subgroup.map_subgroupOf_eq_of_le hHK]

theorem autOn_perfectCore [Finite G] {V H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    autOn (perfectCore H) V = perfectCore (autOn H V) := by
  rw [autOn, autOn, perfectCore_subgroupOf hH, map_perfectCore]

theorem isSylowTwoOf_autOn [Finite G] {V L S : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) (hS : IsSylowTwoOf S L) :
    IsSylowTwoOf (autOn S V) (autOn L V) :=
  CFSG.Quasithin.AutOn.isSylowTwoOf_autOn hS hL

theorem exists_hom_perfectCore [Finite G] {H : Subgroup G} {S : Type} [Group S] [Finite S]
    (hS : commutator S = ⊤) (f : ↥H →* S) (hf : Function.Surjective f)
    (hk : IsPGroup 2 ↥f.ker) :
    ∃ ψ : ↥(perfectCore H) →* S, Function.Surjective ψ ∧ IsPGroup 2 ↥ψ.ker := by
  refine ⟨f.comp (Subgroup.inclusion (perfectCore_le H)), ?_, ?_⟩
  · rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range,
      perfectCore_subgroupOf le_rfl, Subgroup.subgroupOf_self, map_perfectCore,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf]
    exact perfectCore_eq_self_of_perfect hS
  · rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective _ (Subgroup.inclusion_injective _)

noncomputable def glEquivSL3 :
    Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := ZMod 2))
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : Matrix.GeneralLinearGroup.det A = 1 := by
        have : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
        exact this _
      have : A ∈ (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) (ZMod 2) →*
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)).range := by
        rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
        exact hdet
      exact this⟩).symm

theorem commutator_sl3 : commutator (SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊤ :=
  Group.isPerfect_def.mp
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2) le_rfl)

theorem ffJ_eq_of_b51 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (h51 : AsB51) {X K : Subgroup (MulAut W)} (hB : B51Hyp X K)
    (hK : Nat.card ↥K = 9999360) : X = K := by
  obtain ⟨⟨-, hc⟩, -⟩ := h51 W hW X K hB
  have hKX : K ≤ X := hB.2.2.2.1
  have hle : Nat.card ↥K ≤ Nat.card ↥X := Subgroup.card_le_of_le hKX
  rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf X
    rcases hi.2.2 S hS with h | ⟨-, ⟨n, -, hn8, π, hπ⟩ | ⟨F, _, _, hF, π, hπ⟩⟩
    · exact h
    · exfalso
      have h1 : Nat.card ↥X ≤ Nat.card (Equiv.Perm (Fin n)) :=
        Nat.card_le_card_of_surjective π hπ.1
      rw [Nat.card_perm, Nat.card_fin] at h1
      have h2 : n.factorial ≤ (8 : ℕ).factorial := Nat.factorial_le hn8
      have h3 : (8 : ℕ).factorial = 40320 := by decide
      omega
    · exfalso
      have h1 : Nat.card ↥X ≤ Nat.card ↥(quasithinG2 F) :=
        Nat.card_le_card_of_surjective π hπ.1
      rw [CFSG.Quasithin.card_quasithinG2_1527d hF, hF] at h1
      norm_num at h1
      omega
  · exact hii.1
  · exact hiii.1
  · exact hiv.1

end CFSG.Quasithin.H13.L3319
