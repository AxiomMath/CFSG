module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompJ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

section Quot

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

@[expose] def zQ (h : Ctx T M g A t d x) : GwQ d x := gwMk d x ⟨d * d, h.z_mem_Gw⟩

omit [Finite G] in
theorem mem_pCore_iff_mk_eq_one (a : ↥(Gw d x)) :
    gwMk d x a = 1 ↔ (a : G) ∈ pCoreOf 2 (Gw d x) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, pCoreOf_eq_map_pCore]
  constructor
  · intro ha; exact ⟨a, ha, rfl⟩
  · rintro ⟨b, hb, hba⟩
    have : b = a := Subtype.ext hba
    rwa [this] at hb

theorem centralizer_zQ (h : Ctx T M g A t d x) (hf : Wp1 T d x) :
    Subgroup.centralizer ({zQ h} : Set (GwQ d x)) =
      ((Cw T d x).subgroupOf (Gw d x)).map (gwMk d x) := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : gwMk d x (a * ⟨d * d, h.z_mem_Gw⟩) = gwMk d x (⟨d * d, h.z_mem_Gw⟩ * a) := by
      rw [map_mul, map_mul]; exact Subgroup.mem_centralizer_singleton_iff.mp hq
    have h2 := (QuotientGroup.eq (s := CFSG.pCore 2 ↥(Gw d x))).mp h1
    have h3 : ((a * ⟨d * d, h.z_mem_Gw⟩)⁻¹ * (⟨d * d, h.z_mem_Gw⟩ * a) : ↥(Gw d x)) ∈
        CFSG.pCore 2 ↥(Gw d x) := h2
    have h4 := (mem_pCore_iff_mk_eq_one _).mp ((QuotientGroup.eq_one_iff _).mpr h3)
    have h5 : (d * d)⁻¹ * (a : G)⁻¹ * (d * d) * (a : G) ∈ pCoreOf 2 (Gw d x) := by
      have e : (((a * ⟨d * d, h.z_mem_Gw⟩)⁻¹ * (⟨d * d, h.z_mem_Gw⟩ * a) : ↥(Gw d x)) : G) =
          (d * d)⁻¹ * (a : G)⁻¹ * (d * d) * (a : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rwa [e] at h4
    exact ⟨a, Subgroup.mem_subgroupOf.mpr (mem_Cw_of_commutator_mem_P h hf a.2 h5), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    show gwMk d x a * gwMk d x ⟨d * d, h.z_mem_Gw⟩ = gwMk d x ⟨d * d, h.z_mem_Gw⟩ * gwMk d x a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.comm_z_of_mem_Cw (Subgroup.mem_subgroupOf.mp ha))

omit [Finite G] in
theorem card_map_mk (K : Subgroup ↥(Gw d x)) (hK : CFSG.pCore 2 ↥(Gw d x) ≤ K) :
    Nat.card ↥(K.map (gwMk d x)) * Nat.card ↥(CFSG.pCore 2 ↥(Gw d x)) = Nat.card K := by
  have h1 := Subgroup.relIndex_ker (K := K) (gwMk d x)
  rw [QuotientGroup.ker_mk'] at h1
  have h2 := Subgroup.relIndex_mul_card (H := CFSG.pCore 2 ↥(Gw d x)) (K := K)
  rw [inf_eq_left.mpr hK, h1] at h2
  exact h2

omit [Finite G] in
theorem card_pCore_eq (d x : G) :
    Nat.card ↥(CFSG.pCore 2 ↥(Gw d x)) = Nat.card ↥(pCoreOf 2 (Gw d x)) := by
  rw [pCoreOf_eq_map_pCore, Subgroup.card_map_of_injective (Gw d x).subtype_injective]

omit [Finite G] in
theorem card_subgroupOf_Gw {K : Subgroup G} (hK : K ≤ Gw d x) :
    Nat.card ↥(K.subgroupOf (Gw d x)) = Nat.card ↥K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

omit [Finite G] in
theorem pCore_le_subgroupOf {K : Subgroup G} (hK : pCoreOf 2 (Gw d x) ≤ K) :
    CFSG.pCore 2 ↥(Gw d x) ≤ K.subgroupOf (Gw d x) := by
  intro p hp
  rw [Subgroup.mem_subgroupOf]
  apply hK
  rw [pCoreOf_eq_map_pCore]
  exact ⟨p, hp, rfl⟩

theorem card_centralizer_zQ_mul (h : Ctx T M g A t d x) (hf : LocalFacts T d x) :
    Nat.card ↥(Subgroup.centralizer ({zQ h} : Set (GwQ d x))) *
      Nat.card ↥(pCoreOf 2 (Gw d x)) = 384 := by
  rw [centralizer_zQ h hf.wp1, ← card_pCore_eq,
    card_map_mk _ (pCore_le_subgroupOf (P_le_Cw hf.wp1)),
    card_subgroupOf_Gw inf_le_right]
  exact hf.wp0.card_Cw

theorem card_Shat_mul (h : Ctx T M g A t d x) (hf : LocalFacts T d x) :
    Nat.card ↥(((Tw T d x).subgroupOf (Gw d x)).map (gwMk d x)) *
      Nat.card ↥(pCoreOf 2 (Gw d x)) = 2 ^ 7 := by
  rw [← card_pCore_eq, card_map_mk _ (pCore_le_subgroupOf (P_le_Tw h)),
    card_subgroupOf_Gw inf_le_right]
  exact hf.wp0.card_Tw

theorem card_P_cases (h : Ctx T M g A t d x) (hf : LocalFacts T d x) :
    Nat.card ↥(pCoreOf 2 (Gw d x)) = 2 ∨ Nat.card ↥(pCoreOf 2 (Gw d x)) = 4 := by
  have hdvd : Nat.card ↥(pCoreOf 2 (Gw d x)) ∣ 2 ^ 7 := by
    rw [← hf.wp0.card_Tw]; exact Subgroup.card_dvd_of_le (P_le_Tw h)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hle := hf.wp1.card_P
  have hne : pCoreOf 2 (Gw d x) ≠ ⊥ := fun hbot => h.w_ne (by
    have := hf.wp1.w_mem_P (Subgroup.mem_zpowers (wOfX d x))
    rw [hbot, Subgroup.mem_bot] at this; exact this)
  have hlt : 1 < Nat.card ↥(pCoreOf 2 (Gw d x)) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  rw [hk'] at hle hlt ⊢
  interval_cases k <;> simp_all

end Quot

end InspW2

end S143

end CFSG.Quasithin
