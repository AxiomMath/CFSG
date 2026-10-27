module

public import CFSG.Quasithin.EmptyFaithful.SBc16GAct
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G]

@[expose] noncomputable def actO2 (H : Subgroup G) : ↥H →* MulAut (OTwoQuot (oTwoUpper H)) :=
  (SBc16.actHom (oTwoUpper H)).comp (Subgroup.inclusion (le_normalizer_oTwoUpper H))

theorem actO2_eq_one_iff_forall (H : Subgroup G) (h : ↥H) :
    actO2 H h = 1 ↔
      ∀ k ∈ oTwoUpper H, (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
  SBc16.actHom_eq_one_iff (oTwoUpper H) (le_normalizer_oTwoUpper H h.2)

theorem inter_pCoreOf_le_pCoreOf_of_le [Finite G] {K H : Subgroup G} (hKH : K ≤ H) :
    K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 H (hKH hx)⟩

theorem commutator_mem_pCoreOf_oTwoUpper [Finite G] {H : Subgroup G} {h k : G}
    (hh : h ∈ pCoreOf 2 H) (hk : k ∈ oTwoUpper H) :
    h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hhH : h ∈ H := pCoreOf_le 2 H hh
  have h1 : h * k * h⁻¹ * k⁻¹ ∈ oTwoUpper H :=
    (oTwoUpper H).mul_mem
      ((mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hhH) k).mp hk)
      ((oTwoUpper H).inv_mem hk)
  have h2 : h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    have h3 := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH hk)) h⁻¹).mp
      ((pCoreOf 2 H).inv_mem hh)
    have e : h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hh h3
  exact inter_pCoreOf_le_pCoreOf_of_le hKH ⟨h1, h2⟩

theorem mem_pCoreOf_of_commutators_a5 [Finite G] {K : Subgroup G}
    (e : OTwoQuot K ≃* alternatingGroup (Fin 5)) {d : G} (hd : d ∈ K)
    (h : ∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : d ∈ pCoreOf 2 K := by
  have hKO : K ≤ normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hcen : e (QuotientGroup.mk ⟨d, hd⟩ : OTwoQuot K) ∈ center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    induction y using QuotientGroup.induction_on with | H y => ?_
    obtain ⟨k, hk⟩ := y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      SBc16.mem_pCore_iff_coe]
    have hc : d * k⁻¹ * d⁻¹ * k⁻¹⁻¹ ∈ pCoreOf 2 K := h k⁻¹ (K.inv_mem hk)
    have h3 := (mem_normalizer_iff.mp (hKO (K.inv_mem hd)) _).mp ((pCoreOf 2 K).inv_mem hc)
    have e' : (k * d)⁻¹ * (d * k) = d⁻¹ * (d * k⁻¹ * d⁻¹ * k⁻¹⁻¹)⁻¹ * d⁻¹⁻¹ := by group
    show (k * d)⁻¹ * (d * k) ∈ pCoreOf 2 K
    rw [e']
    exact h3
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff] at hcen
  exact (SBc16.mem_pCore_iff_coe K ⟨d, hd⟩).mp hcen

theorem actO2_eq_one_iff [Finite G] {H : Subgroup G}
    (e : OTwoQuot (oTwoUpper H) ≃* alternatingGroup (Fin 5)) (h : ↥H) :
    actO2 H h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [actO2_eq_one_iff_forall]
  constructor
  · intro hh
    set C : Subgroup G := (actO2 H).ker.map H.subtype with hC
    have hCH : C ≤ H := Subgroup.map_subtype_le _
    have hHC : H ≤ normalizer (C : Set G) := by
      have key : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
        intro g hg c hc
        obtain ⟨c0, hc0, rfl⟩ := hc
        refine ⟨⟨g, hg⟩ * c0 * ⟨g, hg⟩⁻¹, ?_, rfl⟩
        have hc0' : actO2 H c0 = 1 := hc0
        show actO2 H (⟨g, hg⟩ * c0 * ⟨g, hg⟩⁻¹) = 1
        rw [map_mul, map_mul, hc0', mul_one, map_inv, mul_inv_cancel]
      intro g hg
      rw [mem_normalizer_iff]
      intro c
      refine ⟨key g hg c, fun hc => ?_⟩
      have := key g⁻¹ (H.inv_mem hg) _ hc
      simpa [mul_assoc] using this
    have hCp : IsPGroup 2 C := by
      rw [IsPGroup.iff_orderOf]
      intro c
      obtain ⟨h0, hh0', hcg⟩ := c.2
      have hh0 : actO2 H h0 = 1 := hh0'
      rw [← Subgroup.orderOf_coe, ← hcg]
      change ∃ n : ℕ, orderOf (h0 : G) = 2 ^ n
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H h0.2
      have h1 : actO2 H (h0 ^ 2 ^ k) = 1 := by rw [map_pow, hh0, one_pow]
      have hd : (h0 : G) ^ 2 ^ k ∈ pCoreOf 2 (oTwoUpper H) :=
        mem_pCoreOf_of_commutators_a5 e hk (by
          have := (actO2_eq_one_iff_forall H _).mp h1
          simpa only [Subgroup.coe_pow] using this)
      obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 (oTwoUpper H))
        ⟨(h0 : G) ^ 2 ^ k, hd⟩
      rw [Subgroup.orderOf_mk] at hj
      have hdvd : orderOf (h0 : G) ∣ 2 ^ (k + j) := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [pow_add, pow_mul, ← hj, pow_orderOf_eq_one]
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact ⟨m, hm⟩
    have hhk : h ∈ (actO2 H).ker := (actO2_eq_one_iff_forall H h).mpr hh
    exact le_pCoreOf_of_le_normalizer 2 hCH hHC hCp ⟨h, hhk, rfl⟩
  · intro hh k hk
    exact commutator_mem_pCoreOf_oTwoUpper hh hk

theorem pRank_quotient_pCore_le_three [Finite G] {H : Subgroup G}
    (e : OTwoQuot (oTwoUpper H) ≃* alternatingGroup (Fin 5)) :
    CFSG.pRank 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : CFSG.pCore 2 ↥H = CFSG.Open.pCore 2 ↥H := CFSG.pCore_eq_open _ 2
  have hker : ∀ h : ↥H, h ∈ CFSG.pCore 2 ↥H ↔ actO2 H h = 1 := fun h => by
    rw [actO2_eq_one_iff e h]
    exact SBc16.mem_pCore_iff_coe H h
  let ψ : ↥H ⧸ CFSG.pCore 2 ↥H →* MulAut (OTwoQuot (oTwoUpper H)) :=
    QuotientGroup.lift _ (actO2 H) fun h hh => (hker h).mp hh
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    induction q using QuotientGroup.induction_on with | H h => ?_
    have h1 : actO2 H h = 1 := hq
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact (hker h).mpr h1
  have hcard : Nat.card (MulAut (OTwoQuot (oTwoUpper H))) = 120 := by
    rw [Nat.card_congr (CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm e).toEquiv,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two (k := 3) fun A hA => ?_
  have := hA
  obtain ⟨r, hr⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hdvd : Nat.card A ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card (A.map ψ)
    rwa [Subgroup.card_map_of_injective hψ, hcard] at this
  rw [hr] at hdvd ⊢
  have hr3 : r ≤ 3 := by
    by_contra hlt
    have h16 : (2 : ℕ) ^ 4 ∣ 120 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h16
  exact Nat.pow_le_pow_right (by norm_num) hr3

end CFSG.Quasithin.H13.U3
