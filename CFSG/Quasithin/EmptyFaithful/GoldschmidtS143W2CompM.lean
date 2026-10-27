module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompL
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompI
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

theorem mem_pCore_iff {G : Type} [Group G] {H : Subgroup G} (a : ↥H) :
    a ∈ CFSG.pCore 2 ↥H ↔ (a : G) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff a).symm

section Edata

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem orderOf_x_mk (h : Ctx T M g A t d x) :
    orderOf (gwMk d x ⟨x, h.x_mem_Gw⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (gwMk d x ⟨x, h.x_mem_Gw⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, h.x_mem_Gw⟩ : ↥(Gw d x)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← h.hx3]
      exact pow_orderOf_eq_one x
    rw [this, map_one]
  refine orderOf_eq_prime h3 fun h1 => ?_
  have hxP := (mem_pCore_iff_mk_eq_one _).mp h1
  have hp2 := pCoreOf_isPGroup 2 (Gw d x)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp2) ⟨x, hxP⟩
  have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_mk _ _).symm.trans hk
  rw [h.hx3] at hk'
  have : (3 : ℕ) ∣ 2 ^ k := hk' ▸ dvd_refl 3
  have h3' : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

theorem exists_E_data (h : Ctx T M g A t d x) (hf : Wp1 T d x) :
    ∃ (E : Subgroup (GwQ d x)) (y : GwQ d x),
      E ≤ ((Tw T d x).subgroupOf (Gw d x)).map (gwMk d x) ∧
        Nonempty (↥E ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧ orderOf y = 3 ∧
        y ∈ Subgroup.normalizer (E : Set (GwQ d x)) ∧ ∀ e ∈ E, y * e * y⁻¹ = e → e = 1 := by
  set E0 : Subgroup G := rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G) with hE0
  have hE0Gw : E0 ≤ Gw d x := inf_le_right
  set E0' : Subgroup ↥(Gw d x) := E0.subgroupOf (Gw d x) with hE0'
  set xG : ↥(Gw d x) := ⟨x, h.x_mem_Gw⟩ with hxG
  have hxN := x_mem_normalizer_E0 h
  have hker : E0' ⊓ (gwMk d x).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨he, hek⟩
    have heP : (e : G) ∈ pCoreOf 2 (Gw d x) := (mem_pCore_iff e).mp (by
      rwa [QuotientGroup.ker_mk'] at hek)
    have : (e : G) ∈ E0 ⊓ pCoreOf 2 (Gw d x) := ⟨Subgroup.mem_subgroupOf.mp he, heP⟩
    rw [E0_inf_P h hf, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨eE⟩ := exists_mulEquiv_map E0' (gwMk d x) hker
  obtain ⟨eZ⟩ := h.hR
  have e1 : ↥E0' ≃* ↥E0 := Subgroup.subgroupOfEquivOfLe hE0Gw
  have hconj : ∀ e : ↥(Gw d x), e ∈ E0' → xG * e * xG⁻¹ ∈ E0' := fun e he =>
    Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hxN _).mp
      (Subgroup.mem_subgroupOf.mp he))
  have hconj' : ∀ e : ↥(Gw d x), e ∈ E0' → xG⁻¹ * e * xG ∈ E0' := fun e he =>
    Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * (e : G) * x)).mpr
      (by
        have e : x * (x⁻¹ * (e : G) * x) * x⁻¹ = e := by group
        rw [e]; exact Subgroup.mem_subgroupOf.mp he))
  refine ⟨E0'.map (gwMk d x), gwMk d x xG, ?_, ⟨(eE.symm.trans e1).trans eZ⟩,
    orderOf_x_mk h, ?_, ?_⟩
  · refine Subgroup.map_mono fun e he => Subgroup.mem_subgroupOf.mpr
      (E0_le_Tw h (Subgroup.mem_subgroupOf.mp he))
  · rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨xG * e * xG⁻¹, hconj e he, ?_⟩
      simp only [map_mul, map_inv]
    · rintro ⟨e', he', hq⟩
      refine ⟨xG⁻¹ * e' * xG, hconj' e' he', ?_⟩
      simp only [map_mul, map_inv]
      rw [hq]; group
  · rintro _ ⟨e, he, rfl⟩ hfix
    have h1 : gwMk d x (xG * e * xG⁻¹) = gwMk d x e := by simpa [map_mul, map_inv] using hfix
    have h2 := (QuotientGroup.eq (s := CFSG.pCore 2 ↥(Gw d x))).mp h1
    have hu : (xG * e * xG⁻¹)⁻¹ * e ∈ E0' := E0'.mul_mem (E0'.inv_mem (hconj e he)) he
    have hP : (((xG * e * xG⁻¹)⁻¹ * e : ↥(Gw d x)) : G) ∈ pCoreOf 2 (Gw d x) :=
      (mem_pCore_iff _).mp h2
    have h3 : (((xG * e * xG⁻¹)⁻¹ * e : ↥(Gw d x)) : G) ∈ E0 ⊓ pCoreOf 2 (Gw d x) :=
      ⟨Subgroup.mem_subgroupOf.mp hu, hP⟩
    rw [E0_inf_P h hf, Subgroup.mem_bot] at h3
    have h4 : xG * e * xG⁻¹ = e := by
      have : (xG * e * xG⁻¹)⁻¹ * e = 1 := Subtype.ext h3
      exact inv_mul_eq_one.mp this
    have h5 : x * (e : G) * x⁻¹ = (e : G) := congrArg Subtype.val h4
    have h6 : (e : G) = 1 := E0_fpf h (Subgroup.mem_subgroupOf.mp he) h5
    have : e = 1 := Subtype.ext h6
    rw [this, map_one]

end Edata

end InspW2

end S143

end CFSG.Quasithin
