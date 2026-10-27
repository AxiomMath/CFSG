module

public import CFSG.Quasithin.EmptyFaithful.SBd3S8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace CFSG.Quasithin.SBd3XS

open CFSG.Quasithin.SBd3S8

section Aux

theorem mem_normalizer_of_conj_mem' {H₀ : Type} [Group H₀] [Finite H₀] {H : Subgroup H₀} {g : H₀}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set H₀) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = x := by simpa [MulAut.conj_apply] using hyx
  rw [← this]
  exact hy

variable {G : Type} [Group G]

theorem isSylowTwoOf_map_top {H T : Subgroup G} (Φ : ↥H →* S8) (hΦ : Function.Surjective Φ)
    (hT : IsSylowTwoOf T H) : IsSylowTwoOf ((T.subgroupOf H).map Φ) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have h2 : IsPGroup 2 ↥(T.subgroupOf H) :=
      hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact h2.of_surjective (Φ.subgroupMap _) (Φ.subgroupMap_surjective _)
  · show ¬ 2 ∣ ((T.subgroupOf H).map Φ).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    intro hd
    exact hT.2.2 (hd.trans (Subgroup.index_map_dvd _ hΦ))

theorem map_le_normalizer {I : Subgroup G} (Φ : ↥I →* S8) {A B : Subgroup ↥I}
    (h : B ≤ Subgroup.normalizer (A : Set ↥I)) :
    B.map Φ ≤ Subgroup.normalizer ((A.map Φ : Subgroup S8) : Set S8) := by
  rintro _ ⟨b, hb, rfl⟩
  refine mem_normalizer_of_conj_mem' fun y hy => ?_
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨b * a * b⁻¹, (Subgroup.mem_normalizer_iff.mp (h hb) a).1 ha, by simp⟩

theorem subgroupOf_le_normalizer {I A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    B.subgroupOf I ≤ Subgroup.normalizer ((A.subgroupOf I : Subgroup ↥I) : Set ↥I) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  exact Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_subgroupOf.mp hb)) (a : G)

theorem oPrimeResidualOf_subgroupOf [Finite G] {I K : Subgroup G} (hKI : K ≤ I) :
    oPrimeResidualOf 3 (K.subgroupOf I) = (oPrimeResidualOf 3 K).subgroupOf I := by
  have h := SBd3T.map_oPrimeResidualOf I.subtype 3 Nat.prime_three (K.subgroupOf I)
  rw [Subgroup.map_subgroupOf_eq_of_le hKI] at h
  rw [← h]
  exact (Subgroup.comap_map_eq_self_of_injective I.subtype_injective _).symm

theorem map_pCoreOf_le [Finite G] {I H : Subgroup G} (hHI : H ≤ I) (Φ : ↥I →* S8) :
    ((pCoreOf 2 H).subgroupOf I).map Φ ≤ pCoreOf 2 ((H.subgroupOf I).map Φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hPP : (pCoreOf 2 H).subgroupOf I ≤ H.subgroupOf I := fun x hx => hPH hx
  have hNH := Subgroup.map_mono (f := Φ) hPP
  refine le_pCoreOf 2 hNH ?_ ?_
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 ?_
    exact map_le_normalizer Φ (subgroupOf_le_normalizer (le_normalizer_pCoreOf 2 H))
  · have h2 : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf I) :=
      (pCoreOf_isPGroup 2 H).of_equiv
        (Subgroup.subgroupOfEquivOfLe (hPH.trans hHI)).symm
    exact h2.of_surjective (Φ.subgroupMap _) (Φ.subgroupMap_surjective _)

end Aux

variable {G : Type} [Group G] [Finite G]

theorem xs_irreducible_abstract {V I L K S D : Subgroup G}
    (hIV : I ≤ Subgroup.normalizer (V : Set G))
    (e : ↥(autOn I V) ≃* S8)
    (hLI : L ≤ I) (hKL : K ≤ L) (hSI : S ≤ I)
    (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hsyl : IsSylowTwoOf S I)
    (hker : I ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 I)
    (hLp : ⁅autOn L V, autOn L V⁆ = autOn L V) (hL1 : autOn L V ≠ ⊥)
    (hmax : IsMaxParabolic2 (autOn L V) (autOn K V))
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hD1 : pCoreOf 2 I ≤ D) (hD2 : D ≤ pCoreOf 2 (oPrimeResidualOf 3 K ⊔ S))
    (hD3 : oPrimeResidualOf 3 K ⊔ S ≤ Subgroup.normalizer (D : Set G)) :
    D = pCoreOf 2 I ∨ D = pCoreOf 2 (oPrimeResidualOf 3 K ⊔ S) := by
  have hKI : K ≤ I := hKL.trans hLI
  set X := oPrimeResidualOf 3 K with hX
  have hXK : X ≤ K := (Subgroup.closure_le _).2 fun x hx => hx.1
  have hXI : X ≤ I := hXK.trans hKI
  set H := X ⊔ S with hH
  have hHI : H ≤ I := sup_le hXI hSI
  have hPH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  set ρ := Setup.rho V I hIV with hρ
  have hρR : ρ.range = autOn I V := Setup.range_rho hIV
  set f : ↥ρ.range ≃* S8 := (MulEquiv.subgroupCongr hρR).trans e with hf
  set Φ₁ : ↥I →* ↥ρ.range := ρ.rangeRestrict with hΦ₁
  set Φ : ↥I →* S8 := f.toMonoidHom.comp Φ₁ with hΦ
  have hΦ₁surj : Function.Surjective Φ₁ := ρ.rangeRestrict_surjective
  have hΦsurj : Function.Surjective Φ := f.surjective.comp hΦ₁surj
  have hΦker : ∀ i : ↥I, Φ i = 1 ↔ (i : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro i
    rw [← Setup.rho_eq_one_iff hIV i]
    constructor
    · intro h
      have h1 : Φ₁ i = 1 := f.injective (by rw [map_one]; exact h)
      have h2 := congrArg Subtype.val h1
      exact h2
    · intro h
      have h1 : Φ₁ i = 1 := Subtype.ext h
      show f (Φ₁ i) = 1
      rw [h1, map_one]
  have hautOn : ∀ A : Subgroup G, A ≤ I → autOn A V = ((A.subgroupOf I).map Φ₁).map ρ.range.subtype := by
    intro A hAI
    ext φ
    rw [Setup.mem_autOn_iff_rho hIV hAI]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Φ₁ p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  set LL := L.subgroupOf I with hLL
  set KK := K.subgroupOf I with hKK
  set SS := S.subgroupOf I with hSS
  set DD := D.subgroupOf I with hDD
  set HH := H.subgroupOf I with hHH
  have hmaxΦ : IsMaxParabolic2 (LL.map Φ) (KK.map Φ) := by
    rw [hautOn L hLI, hautOn K hKI] at hmax
    have h1 := (SBd3T.isMaxParabolic2_map_iff ρ.range.subtype (Subgroup.subtype_injective _)
      _ _).1 hmax
    have h2 := (SBd3T.isMaxParabolic2_map_iff f.toMonoidHom f.injective _ _).2 h1
    rwa [Subgroup.map_map, Subgroup.map_map] at h2
  have hLn : (LL.map Φ).Normal := by
    have : LL.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLI).2 hIL
    exact this.map Φ hΦsurj
  have hLpΦ : ⁅LL.map Φ, LL.map Φ⁆ = LL.map Φ := by
    rw [hautOn L hLI, ← Subgroup.map_commutator] at hLp
    have h1 := Subgroup.map_injective (Subgroup.subtype_injective _) hLp
    have h2 : LL.map Φ = (LL.map Φ₁).map f.toMonoidHom := (Subgroup.map_map _ _ _).symm
    rw [h2, ← Subgroup.map_commutator, h1]
  have hL1Φ : LL.map Φ ≠ ⊥ := by
    intro h
    apply hL1
    rw [hautOn L hLI]
    have h1 : (LL.map Φ₁).map f.toMonoidHom = ⊥ := by rw [Subgroup.map_map]; exact h
    have h2 : LL.map Φ₁ = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ f.injective).1 h1
    rw [h2, Subgroup.map_bot]
  have hSylΦ : IsSylowTwoOf (SS.map Φ) ⊤ := isSylowTwoOf_map_top Φ hΦsurj hsyl
  have hSKΦ : SS.map Φ ≤ Subgroup.normalizer ((KK.map Φ : Subgroup S8) : Set S8) :=
    map_le_normalizer Φ (subgroupOf_le_normalizer hSK)
  have hX_eq : oPrimeResidualOf 3 (KK.map Φ) = (X.subgroupOf I).map Φ := by
    rw [← SBd3T.map_oPrimeResidualOf Φ 3 Nat.prime_three KK, hKK,
      oPrimeResidualOf_subgroupOf hKI]
  have hHeq : oPrimeResidualOf 3 (KK.map Φ) ⊔ SS.map Φ = HH.map Φ := by
    rw [hX_eq, ← Subgroup.map_sup, hHH, hH, Subgroup.subgroupOf_sup hXI hSI]
  have hD1Φ : DD.map Φ ≤ pCoreOf 2 (oPrimeResidualOf 3 (KK.map Φ) ⊔ SS.map Φ) := by
    rw [hHeq]
    refine (Subgroup.map_mono ?_).trans (map_pCoreOf_le hHI Φ)
    exact fun x hx => hD2 hx
  have hD2Φ : oPrimeResidualOf 3 (KK.map Φ) ⊔ SS.map Φ ≤
      Subgroup.normalizer ((DD.map Φ : Subgroup S8) : Set S8) := by
    rw [hHeq]
    exact map_le_normalizer Φ (subgroupOf_le_normalizer hD3)
  have key := s8_irreducible hLn hLpΦ hL1Φ hmaxΦ hSylΦ hSKΦ hD1Φ hD2Φ
  rw [hHeq] at key
  rcases key with h | h
  · left
    refine le_antisymm (fun d hd => ?_) hD1
    have hdI : d ∈ I := hHI (pCoreOf_le 2 H (hD2 hd))
    have hmem : Φ ⟨d, hdI⟩ ∈ DD.map Φ := ⟨⟨d, hdI⟩, hd, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    rw [← hker]
    exact ⟨hdI, (hΦker ⟨d, hdI⟩).1 hmem⟩
  · right
    refine le_antisymm hD2 (fun p hp => ?_)
    have hpI : p ∈ I := hHI (pCoreOf_le 2 H hp)
    have hmem : Φ ⟨p, hpI⟩ ∈ pCoreOf 2 (HH.map Φ) :=
      map_pCoreOf_le hHI Φ ⟨⟨p, hpI⟩, hp, rfl⟩
    rw [← h] at hmem
    obtain ⟨d, hd, hdp⟩ := hmem
    have h1 : Φ (d⁻¹ * ⟨p, hpI⟩) = 1 := by rw [map_mul, map_inv, hdp, inv_mul_cancel]
    have h2 : ((d⁻¹ * ⟨p, hpI⟩ : ↥I) : G) ∈ pCoreOf 2 I := by
      rw [← hker]
      exact ⟨(d⁻¹ * ⟨p, hpI⟩).2, (hΦker _).1 h1⟩
    have h3 : ((d⁻¹ * ⟨p, hpI⟩ : ↥I) : G) ∈ D := hD1 h2
    have h4 : (d : G) ∈ D := hd
    have h5 : p = (d : G) * ((d⁻¹ * ⟨p, hpI⟩ : ↥I) : G) := by
      show p = (d : G) * ((d : G)⁻¹ * p)
      group
    rw [h5]
    exact D.mul_mem h4 h3

end CFSG.Quasithin.SBd3XS
