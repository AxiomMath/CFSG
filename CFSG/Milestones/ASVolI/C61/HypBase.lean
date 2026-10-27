module

public import CFSG.Milestones.ASVolI.C6
public import CFSG.Milestones.ASVolI.C5Blocks
public import CFSG.Quasithin.EmptyFaithful.S152Y22

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

@[expose] def burnsideC56_HypI {G : Type} [Group G] (H : Subgroup G) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
    QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
    QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2))

section General

variable {G : Type} [Group G]

theorem burnsideC56_subgroupOf_eq_pCore {K P : Subgroup G} (hKP : pCoreOf 2 K = K ⊓ P) :
    P.subgroupOf K = CFSG.pCore 2 ↥K := by
  have h1 : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K :=
    A4.subgroupOf_map_subtype' K (CFSG.pCore 2 ↥K)
  rw [← h1, hKP]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem burnsideC56_ker_comp_inclusion {K M P : Subgroup G} (hKM : K ≤ M) {Y : Type} [Group Y]
    (φ : ↥M →* Y) (hker : φ.ker = P.subgroupOf M) :
    (φ.comp (Subgroup.inclusion hKM)).ker = P.subgroupOf K := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  rfl

theorem burnsideC56_index_pCore_dvd {K M P : Subgroup G} (hKM : K ≤ M) {Y : Type} [Group Y]
    [Finite Y] (φ : ↥M →* Y) (hker : φ.ker = P.subgroupOf M) (hKP : pCoreOf 2 K = K ⊓ P) :
    (CFSG.pCore 2 ↥K).index ∣ Nat.card Y := by
  have h1 : (φ.comp (Subgroup.inclusion hKM)).ker = CFSG.pCore 2 ↥K := by
    rw [burnsideC56_ker_comp_inclusion hKM φ hker, burnsideC56_subgroupOf_eq_pCore hKP]
  rw [← h1, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem burnsideC56_index_pCore_eq_card {M : Subgroup G} {Y : Type} [Group Y] (φ : ↥M →* Y)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥M) :
    (CFSG.pCore 2 ↥M).index = Nat.card Y := by
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]

theorem burnsideC56_card_alt_three : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem burnsideC56_card_alt_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem burnsideC56_index_of_alt {K : Subgroup G} {m : ℕ} (h : IsAltType K m) :
    (CFSG.pCore 2 ↥K).index = Nat.card ↥(alternatingGroup (Fin m)) := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact burnsideC56_index_pCore_eq_card α hα hker

theorem burnsideC56_index_of_lin2 {K : Subgroup G} {n : ℕ} (hn : 1 < n) (h : IsLin2Type K n) :
    60 ≤ (CFSG.pCore 2 ↥K).index := by
  obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := h
  rw [burnsideC56_index_pCore_eq_card α hα hker, burnsideC5h_p1_sl2_card F, hF]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ (2 ^ n) ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h4 2
  calc 60 = 4 * 15 := by norm_num
    _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h4 (by omega)

theorem burnsideC56_three_dvd_of_alt3 {K : Subgroup G} (h : IsAltType K 3) : 3 ∣ Nat.card K := by
  have h1 := burnsideC56_index_of_alt h
  rw [burnsideC56_card_alt_three] at h1
  rw [← h1]
  exact Subgroup.index_dvd_card _

end General

section Finite

variable {G : Type} [Group G] [Finite G]

theorem burnsideC56_not_le_of_three_dvd {K P : Subgroup G} (hP : IsPGroup 2 P)
    (h3 : 3 ∣ Nat.card K) : ¬ K ≤ P := by
  intro hKP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hP.to_le hKP).exists_card_eq
  rw [hk] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem burnsideC56_pCoreOf_block {H K : Subgroup G} (hK : IsBlock2 H K) :
    pCoreOf 2 K = K ⊓ pCoreOf 2 H :=
  C1Pack.blockQ_eq_inf_pCoreOf hK

theorem burnsideC56_pCoreOf_oTwoUpper (H : Subgroup G) :
    pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
  S152Y.pCoreOf_eq_inf_of_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)

theorem burnsideC56_oTwoUpper_subgroupOf (H : Subgroup G) :
    (oTwoUpper H).subgroupOf H = oTwoUpper (⊤ : Subgroup ↥H) := by
  have h1 := oTwoUpper_map H.subtype (⊤ : Subgroup ↥H)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  rw [h1]
  exact A4.subgroupOf_map_subtype' H _

theorem burnsideC56_map_oTwoUpper {H : Subgroup G} {Y : Type} [Group Y] (ψ : ↥H →* Y)
    (hψ : Function.Surjective ψ) :
    ((oTwoUpper H).subgroupOf H).map ψ = oTwoUpper (⊤ : Subgroup Y) := by
  rw [burnsideC56_oTwoUpper_subgroupOf, ← oTwoUpper_map ψ ⊤, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hψ]

theorem burnsideC56_sup_eq {H T : Subgroup G} (hT : IsSylowTwoOf T H) : oTwoUpper H ⊔ T = H :=
  burnsideC5h_c53_sup_eq hT

theorem burnsideC56_umax_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (hZ : ∀ S : Subgroup Z, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S) :
    ∀ S : Subgroup Y, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S := by
  intro S hS hSi
  have hS' : IsPGroup 2 (S.map e.toMonoidHom) := hS.map _
  have hSi' : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_eq _ e.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      exact bot_le)]
    exact hSi
  refine burnsideC5h_p1_umax_of_surjective e.toMonoidHom e.surjective ?_ (hZ _ hS' hSi')
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
  exact bot_le

theorem burnsideC56_uniqueMax_of_quot {H T K : Subgroup G} (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hsup : K ⊔ T = H) {Y : Type} [Group Y]
    (φ : ↥K →* Y) (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥K)
    (hY : ∀ S : Subgroup Y, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S) :
    ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hT hKH hHK
  have hU : burnsideC5h_p1_UMaxIn K (T ⊓ K) :=
    burnsideC5h_p1_umaxIn_of_quotient hTK φ hφ hker hY
  have hU' : burnsideC5h_p1_UMaxIn K (K ⊓ T) := by rwa [inf_comm]
  obtain ⟨N, hN⟩ := burnsideC5h_p1_uniqueMax_sup (A := K) (B := T) (hT.1.trans hHK) hU'
  rw [hsup] at hN
  exact ⟨N, hN⟩

theorem burnsideC56_not_normal_of_quot {H T K : Subgroup G} (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {Y : Type} [Group Y] (φ : ↥K →* Y)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥K) (hY2 : 2 ∣ Nat.card Y) :
    ¬ H ≤ Subgroup.normalizer (T : Set G) := by
  intro hHT
  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hT hKH hHK
  have hnorm : K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro k hk
    exact A4.mem_normalizer_inf (hHT (hKH hk)) (hHK (hKH hk))
  have hle : T ⊓ K ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hTK.2.1
  have hle' : (T ⊓ K).subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 K := hle hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hdvd : (CFSG.pCore 2 ↥K).index ∣ ((T ⊓ K).subgroupOf K).index :=
    Subgroup.index_dvd_of_le hle'
  rw [burnsideC56_index_pCore_eq_card φ hφ hker] at hdvd
  exact hTK.2.2 (hY2.trans hdvd)

theorem burnsideC56_minParabolic_of_quot {H T K : Subgroup G} (hT : IsSylowTwoOf T H)
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hsup : K ⊔ T = H) {Y : Type}
    [Group Y] (φ : ↥K →* Y) (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥K)
    (hY : ∀ S : Subgroup Y, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S)
    (hY2 : 2 ∣ Nat.card Y) : IsMinimalParabolic T H := by
  obtain ⟨N, hN⟩ := burnsideC56_uniqueMax_of_quot hT hKH hHK hsup φ hφ hker hY
  obtain ⟨hNmax, hTN, -⟩ := isUniqueMaxOver_iff.mp hN
  exact ⟨hT, burnsideC56_not_normal_of_quot hT hKH hHK φ hφ hker hY2, N, hTN, hNmax.1,
    fun X hTX hXH => burnsideC5h_c53_le_of_lt hN hTX hXH⟩

end Finite

end CFSG.ASVolI
