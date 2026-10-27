module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

theorem map_pCore_two (H : Type) [Group H] (σ : MulAut H) :
    (CFSG.Open.pCore 2 H).map σ.toMonoidHom = CFSG.Open.pCore 2 H := by
  have h := CFSG.pCore_map_iso 2 σ
  exact h

@[expose] noncomputable def oTwoQuotAut (H : Type) [Group H] :
    MulAut H →* MulAut (H ⧸ CFSG.Open.pCore 2 H) where
  toFun σ := QuotientGroup.congr _ _ σ (map_pCore_two H σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

variable {G : Type} [Group G]

@[expose] noncomputable def conjOTwoQuot (K N : Subgroup G)
    (hN : N ≤ Subgroup.normalizer (K : Set G)) : ↥N →* MulAut (OTwoQuot K) :=
  (oTwoQuotAut ↥K).comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hN))

theorem conjOTwoQuot_apply_mk {K N : Subgroup G} (hN : N ≤ Subgroup.normalizer (K : Set G))
    (g : ↥N) (k : ↥K) :
    conjOTwoQuot K N hN g (QuotientGroup.mk k : OTwoQuot K) =
      QuotientGroup.mk (⟨(g : G) * k * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hN g.2) k).mp k.2⟩ : ↥K) :=
  rfl

theorem commutator_mem_of_conjOTwoQuot_eq_one {K N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (K : Set G)) {g : ↥N} (hg : conjOTwoQuot K N hN g = 1)
    {k : G} (hk : k ∈ K) : (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have h1 := congrArg (fun σ : MulAut (OTwoQuot K) => σ (QuotientGroup.mk (⟨k, hk⟩ : ↥K))) hg
  simp only [MulAut.one_apply] at h1
  rw [conjOTwoQuot_apply_mk, QuotientGroup.eq] at h1
  have h4 : (g : G) * k⁻¹ * (g : G)⁻¹ * k ∈ pCoreOf 2 K := by
    refine ⟨_, h1, ?_⟩
    simp [mul_assoc]
  have h5 := le_normalizer_pCoreOf 2 K hk
  have h6 := (Subgroup.mem_normalizer_iff.mp h5 _).mp ((pCoreOf 2 K).inv_mem h4)
  have e : k * ((g : G) * k⁻¹ * (g : G)⁻¹ * k)⁻¹ * k⁻¹ = (g : G) * k * (g : G)⁻¹ * k⁻¹ := by group
  rwa [e] at h6

variable [Finite G]

theorem mem_pCoreOf_of_ker {M : Type*} [Group M] {K1 S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) (φ : ↥(K1 ⊔ S) →* M)
    (hφK : ∀ g : ↥(K1 ⊔ S), φ g = 1 → ∀ k ∈ K1, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K1)
    {s : G} (hs : s ∈ S) (hφ : φ ⟨s, Subgroup.mem_sup_right hs⟩ = 1) :
    s ∈ pCoreOf 2 (K1 ⊔ S) := by
  let C : Subgroup G := φ.ker.map (K1 ⊔ S).subtype
  let P := pCoreOf 2 K1
  have hCle : C ≤ K1 ⊔ S := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hCn : ∀ g ∈ K1 ⊔ S, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    rintro g hg _ ⟨c, hc, rfl⟩
    exact ⟨⟨g, hg⟩ * c * ⟨g, hg⟩⁻¹, φ.normal_ker.conj_mem c hc ⟨g, hg⟩, by simp⟩
  have hPn : ∀ g ∈ K1 ⊔ S, ∀ p ∈ P, g * p * g⁻¹ ∈ P := fun g hg p hp =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf_of_le_normalizer hN hg) p).mp hp
  have hcomm : ∀ c ∈ C, ∀ k ∈ K1, c * k * c⁻¹ * k⁻¹ ∈ P := by
    rintro _ ⟨c, hc, rfl⟩ k hk
    exact hφK c (MonoidHom.mem_ker.mp hc) k hk
  let D : Subgroup G := (C ⊓ S) ⊔ P
  have hconj : ∀ g ∈ K1 ⊔ S, (g ∈ K1 ∨ g ∈ S) → ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg hgKS d hd
    have hle : D ≤ D.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le ?_ ?_
      · rintro c ⟨hcC, hcS⟩
        show g * c * g⁻¹ ∈ D
        rcases hgKS with hgK | hgS
        · have h1 : c⁻¹ * g * c⁻¹⁻¹ * g⁻¹ ∈ P := hcomm _ (C.inv_mem hcC) g hgK
          have e : g * c * g⁻¹ = c * (c⁻¹ * g * c⁻¹⁻¹ * g⁻¹) := by group
          rw [e]
          exact D.mul_mem (Subgroup.mem_sup_left ⟨hcC, hcS⟩) (Subgroup.mem_sup_right h1)
        · exact Subgroup.mem_sup_left
            ⟨hCn g hg c hcC, S.mul_mem (S.mul_mem hgS hcS) (S.inv_mem hgS)⟩
      · intro p hp
        exact Subgroup.mem_sup_right (hPn g hg p hp)
    exact hle hd
  have hnorm : K1 ⊔ S ≤ Subgroup.normalizer (D : Set G) := by
    refine sup_le ?_ ?_
    · intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro d
      refine ⟨hconj k (Subgroup.mem_sup_left hk) (Or.inl hk) d, fun h => ?_⟩
      have := hconj k⁻¹ (Subgroup.mem_sup_left (K1.inv_mem hk)) (Or.inl (K1.inv_mem hk)) _ h
      simpa [mul_assoc] using this
    · intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro d
      refine ⟨hconj t (Subgroup.mem_sup_right ht) (Or.inr ht) d, fun h => ?_⟩
      have := hconj t⁻¹ (Subgroup.mem_sup_right (S.inv_mem ht)) (Or.inr (S.inv_mem ht)) _ h
      simpa [mul_assoc] using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥P := pCoreOf_isPGroup 2 K1
  have hCS2 : IsPGroup 2 ↥(C ⊓ S) := hS2.to_le inf_le_right
  have hCSP : C ⊓ S ≤ Subgroup.normalizer (P : Set G) := fun c hc =>
    le_normalizer_pCoreOf_of_le_normalizer hN (hCle hc.1)
  have hD2 : IsPGroup 2 ↥D := IsPGroup.to_sup_of_normal_right' hCS2 hP2 hCSP
  have hDle : D ≤ K1 ⊔ S :=
    sup_le (inf_le_left.trans hCle) ((pCoreOf_le 2 K1).trans le_sup_left)
  have hsC : s ∈ C := ⟨⟨s, Subgroup.mem_sup_right hs⟩, MonoidHom.mem_ker.mpr hφ, rfl⟩
  have hsD : s ∈ D := Subgroup.mem_sup_left ⟨hsC, hs⟩
  exact le_pCoreOf_of_le_normalizer hDle hnorm hD2 hsD

theorem mem_pCoreOf_of_conjOTwoQuot_eq_one {K1 S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {s : G} (hs : s ∈ S)
    (hφ : conjOTwoQuot K1 (K1 ⊔ S) hN ⟨s, Subgroup.mem_sup_right hs⟩ = 1) :
    s ∈ pCoreOf 2 (K1 ⊔ S) :=
  mem_pCoreOf_of_ker hS2 hN (conjOTwoQuot K1 (K1 ⊔ S) hN)
    (fun _ hg _ hk => commutator_mem_of_conjOTwoQuot_eq_one hN hg hk) hs hφ

end CFSG.Quasithin.Background.Harris.R1
