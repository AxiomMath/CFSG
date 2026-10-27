module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique

namespace S153M

section Sigma

variable {G : Type} [Group G]

@[expose] noncomputable def starMapK (M' H K : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  (((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M' H K) fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)

theorem starMapK_surjective (M' H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starMapK M' H K hKH) := by
  rintro ⟨y, x, hx, rfl⟩
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem starMapK_eq_one_iff (M' H K : Subgroup G) (hKH : K ≤ H) (k : ↥K) :
    starMapK M' H K hKH k = 1 ↔ Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem ker_le_kerIn_of_action [Finite G] {M' H K : Subgroup G} (hKH : K ≤ H) (hsub : IsSubnormal K H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) {L : Type} [Group L]
    (ρ : ↥K →* L) (hO2 : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → ρ k = 1) (hne : ∃ k : ↥K, ρ k ≠ 1)
    (hkerchar : ∀ x : G, x ∈ kerIn M' H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    ∀ k : ↥K, ρ k = 1 → Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H := by
  intro k hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker0 : (pCoreOf 2 K).subgroupOf K ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hO2 x (Subgroup.mem_subgroupOf.mp hx)
  let π : ↥K →* ↥K ⧸ (pCoreOf 2 K).subgroupOf K := QuotientGroup.mk' _
  let φ : ↥K ⧸ (pCoreOf 2 K).subgroupOf K →* L := QuotientGroup.lift _ ρ hker0
  have hφnt : ∃ x, φ x ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨QuotientGroup.mk x, hx⟩
  have hcen := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hφnt
  have hkc' : π k ∈ Subgroup.center (↥K ⧸ (pCoreOf 2 K).subgroupOf K) :=
    hcen (by rw [MonoidHom.mem_ker]; exact hk)
  have hkc : ∀ k₁ : ↥K, (k : G) * (k₁ : G) * (k : G)⁻¹ * (k₁ : G)⁻¹ ∈ pCoreOf 2 H := by
    intro k₁
    have hc := Subgroup.mem_center_iff.mp hkc' (π k₁)
    have h1 : π (k * k₁ * k⁻¹ * k₁⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hc]
      group
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact A4.pCoreOf_le_of_subnormal 2 hsub (Subgroup.mem_subgroupOf.mp h2)
  let Ck : Subgroup ↥H :=
    { carrier := {y | (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 H}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have hQn : (a : G) ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H a.2
        have e : (k : G) * ((a * b : ↥H) : G) * (k : G)⁻¹ * ((a * b : ↥H) : G)⁻¹ =
            ((k : G) * (a : G) * (k : G)⁻¹ * (a : G)⁻¹) *
              ((a : G) * ((k : G) * (b : G) * (k : G)⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [Set.mem_ofPred_eq, e]
        refine (pCoreOf 2 H).mul_mem ha ?_
        exact (Subgroup.mem_normalizer_iff.mp hQn _).mp hb
      inv_mem' := by
        intro a ha
        have hQn : (a : G) ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H a.2
        have e : (k : G) * ((a⁻¹ : ↥H) : G) * (k : G)⁻¹ * ((a⁻¹ : ↥H) : G)⁻¹ =
            (a : G)⁻¹ * ((k : G) * (a : G) * (k : G)⁻¹ * (a : G)⁻¹)⁻¹ * ((a : G)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv]
          group
        rw [Set.mem_ofPred_eq, e]
        have hQn' : (a : G)⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
          Subgroup.inv_mem _ hQn
        exact (Subgroup.mem_normalizer_iff.mp hQn' _).mp ((pCoreOf 2 H).inv_mem ha) }
  have hKCk : K.subgroupOf H ≤ Ck := fun y hy => hkc ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
  have hQCk : (pCoreOf 2 H).subgroupOf H ≤ Ck := by
    intro y hy
    have hyQ : (y : G) ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hy
    have hkn : (k : G) ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH k.2)
    have h1 : (k : G) * (y : G) * (k : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp hkn _).mp hyQ
    exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hyQ)
  have hKQ : (K ⊔ pCoreOf 2 H).subgroupOf H ≤ Ck := by
    rw [Subgroup.subgroupOf_sup hKH (CFSG.LieType.BorelTits.pCoreOf_le 2 H)]
    exact sup_le hKCk hQCk
  rw [Subgroup.mem_subgroupOf]
  refine (hkerchar _).mpr ⟨Subgroup.mem_sup_left k.2, fun y hy => ?_⟩
  have hyH : y ∈ H := sup_le hKH (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hy
  exact hKQ (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hyH⟩ : ↥H) ∈ (K ⊔ pCoreOf 2 H).subgroupOf H)

theorem exists_sigma_central_of_action' {M' H K : Subgroup G} (hKH : K ≤ H) {L : Type} [Group L]
    (ρ : ↥K →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ k : ↥K, ρ k = 1 → Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H)
    (hkerchar : ∀ x : G, x ∈ kerIn M' H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hQ : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 H → ρ k = 1) :
    ∃ σ : L →* ↥(E2.star M' H K), Function.Surjective σ ∧ σ.ker ≤ Subgroup.center L ∧
      ∀ k : ↥K, σ (ρ k) = starMapK M' H K hKH k := by
  have hq := starMapK_surjective M' H K hKH
  have hkq : ρ.ker ≤ (starMapK M' H K hKH).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starMapK_eq_one_iff]
    exact hker k hk
  let σ : L →* ↥(E2.star M' H K) :=
    ρ.liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
      ⟨starMapK M' H K hKH, hkq⟩
  have hσρ : ∀ k, σ (ρ k) = starMapK M' H K hKH k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hkq⟩ k
  have hσs : Function.Surjective σ := by
    intro y
    obtain ⟨k, rfl⟩ := hq y
    exact ⟨ρ k, hσρ k⟩
  refine ⟨σ, hσs, ?_, hσρ⟩
  intro l hl
  obtain ⟨k, rfl⟩ := hρ l
  have hk1 : starMapK M' H K hKH k = 1 := by
    rw [← hσρ]
    exact hl
  have hkK : (k : G) ∈ kerIn M' H :=
    Subgroup.mem_subgroupOf.mp ((starMapK_eq_one_iff M' H K hKH k).mp hk1)
  have hkc := (hkerchar _).mp hkK
  rw [Subgroup.mem_center_iff]
  intro l'
  obtain ⟨k', rfl⟩ := hρ l'
  have hmem : ((k * k' * k⁻¹ * k'⁻¹ : ↥K) : G) ∈ pCoreOf 2 H := by
    have := hkc.2 (k' : G) (Subgroup.mem_sup_left k'.2)
    simpa using this
  have h1 : ρ (k * k' * k⁻¹ * k'⁻¹) = 1 := hQ _ hmem
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  exact h2.symm

end Sigma

end S153M

end CFSG.Quasithin
