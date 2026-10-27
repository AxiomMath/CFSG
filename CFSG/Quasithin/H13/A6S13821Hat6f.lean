module

public import CFSG.Quasithin.H13.A6S13821Hat6a
public import CFSG.Quasithin.H13.A6S13821Hat6d
public import CFSG.Quasithin.H13.A6S13821Hat6e
public import CFSG.Quasithin.H13.A6S13821e
public import CFSG.Quasithin.H13.A6S13821Hat6c
public import CFSG.Quasithin.H13.A6S13821HatMA

public section

namespace CFSG.Quasithin.H13.A6

open Equiv Equiv.Perm CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.H13.L32A.C.Alt6
open CFSG.Quasithin.H13.A6.Hat6
open CFSG.Quasithin.E1.LiftS5 (quotConj)
open scoped IsMulCommutative commutatorElement

namespace Hat6

theorem exists_phi_D0 {G : Type} [Group G] [Finite G] {K T : Subgroup G}
    (hHat : IsHat (Kq K) A6) (hTsyl : IsSylowTwoOf (T ⊓ K) K) (hT2 : IsPGroup 2 T) :
    ∃ φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6, (T.subgroupOf K).map (piOf φ) = D0 := by
  obtain ⟨-, -, ⟨φ₀⟩⟩ := hHat
  have hTK' : (T ⊓ K).subgroupOf K = T.subgroupOf K := Subgroup.inf_subgroupOf_right T K
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hT2.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := hTK' ▸ hTsyl.2.2
  obtain ⟨h, hhD⟩ := exists_conj_map_eq_D0 (piOf φ₀) (piOf_surjective φ₀) hS2 hSi
  refine ⟨φ₀.trans (MulAut.conj h⁻¹), ?_⟩
  rw [← hhD, Subgroup.map_map]
  rfl

end Hat6

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

omit S in
theorem exists_card_of_hat6 {K : Subgroup G} (hHat : IsHat (Kq K) A6) :
    ∃ c : ℕ, Nat.card K = 1080 * 2 ^ c := by
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  refine ⟨c, ?_⟩
  obtain ⟨-, h3, ⟨φ⟩⟩ := hHat
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hc,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (Kq K)), h3,
    Nat.card_congr φ.toEquiv, card_A6]

theorem false_of_hat6_central (h13 : Lem13813)
    (hFine : F918Fine4Hat6) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) (hF918 : HypF918 T V L (fsuV1 T V) S.V3 H K)
    (hHat : IsHat (Kq K) A6) (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6)
    (hD : (T.subgroupOf K).map (piOf φ) = D0) (hL1Z : S.L1 ≤ oTwoZIn K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKn
  have hF := (hS.hF H hH).toHypF91
  have hT2 : IsPGroup 2 T := hF.sylow_H.2.1
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF918
  have hnf := hFine G T V L (fsuV1 T V) S.V3 H K hF918 (S.sqtkGroup_of_mem_Hz hH)
    (L32A.C.conjClosure_T_eq_self hTK) (IsHat.of_mulEquiv eA hHat)
  have hπ : Function.Surjective (piOf φ) := piOf_surjective φ
  have hker : ∀ k : ↥K, piOf φ k = 1 ↔ (k : G) ∈ oTwoZIn K := piOf_eq_one_iff φ
  have hfus : ∀ t (ht : t ∈ T) (x : ↥K), orderOf (piOf φ x) = 3 →
      ∃ k : ↥K, piOf φ (conjK (hTK ht) x) = piOf φ (k * x * k⁻¹) := by
    intro t ht x hx
    by_contra hne
    push Not at hne
    apply hnf t ht
    refine ⟨x, x.2, ?_, ?_, fun k hk hZ => ?_⟩
    · have := (hker (x ^ 3)).mp (by rw [map_pow, ← hx, pow_orderOf_eq_one])
      simpa using this
    · intro hxZ
      rw [(hker x).mpr hxZ, orderOf_one] at hx
      omega
    · apply hne ⟨k, hk⟩
      have h1 := (hker ((⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹ * conjK (hTK ht) x)).mpr hZ
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.mp h1).symm
  obtain ⟨hT1, hT2', hZ1, hZ2, hKB⟩ := exists_parabolics (piOf φ) hπ (oTwoZIn_le_self K) hker
    hTK (hTK.trans (normalizer_le_normalizer_oTwoZIn K)) hD hfus
  obtain ⟨c, hcK⟩ := exists_card_of_hat6 hHat
  have hsolv1 := L32A.C.isSolvable_parab_sup hπ card_N1 hT2 hT1 hcK
  have hsolv2 := L32A.C.isSolvable_parab_sup hπ card_N2 hT2 hT2' hcK
  have hBK : ∀ N : Subgroup A6, parab (piOf φ) N ≤ K := fun N => Subgroup.map_subtype_le _
  have hM1 := h13 G T L V S hS (parab (piOf φ) N1 ⊔ T)
    (sup_le (hL1Z.trans (hZ1.trans le_sup_left)) le_sup_right)
    ((sup_le ((hBK N1).trans hKH) hTH).trans hH.2.1) hsolv1
  have hM2 := h13 G T L V S hS (parab (piOf φ) N2 ⊔ T)
    (sup_le (hL1Z.trans (hZ2.trans le_sup_left)) le_sup_right)
    ((sup_le ((hBK N2).trans hKH) hTH).trans hH.2.1) hsolv2
  apply hH.2.2
  rw [hHK]
  exact sup_le (hKB.trans (sup_le (le_sup_left.trans hM1) (le_sup_left.trans hM2)))
    (sup_le (hL1Z.trans (hZ1.trans (le_sup_left.trans hM1))) (le_sup_right.trans hM1))

theorem false_of_hat6_noncentral
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) (hHat : IsHat (Kq K) A6) (hL1K : S.L1 ≤ K)
    (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6) (hD : (T.subgroupOf K).map (piOf φ) = D0)
    (hL1Z : ¬ S.L1 ≤ oTwoZIn K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (Kq K) := hHat.1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hLTH : S.L1 ⊔ T ≤ H := hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hLTH
  have hHT : H = K ⊔ T := by rw [hHK, ← sup_assoc, sup_eq_left.mpr hL1K]
  have hF := (hS.hF H hH).toHypF91
  have hT2 : IsPGroup 2 T := hF.sylow_H.2.1
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  have hRH : R ≤ H := (pCoreOf_le 2 _).trans hLTH
  have hRN : R ≤ Subgroup.normalizer (K : Set G) := hRH.trans hKn
  have hLTR : S.L1 ⊔ T ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
  have hX := A6Hat7.oTwoRes_solvRad_ne_bot hK hHat.2.1
  have hA := S.not_transv_R_of_solvRad h139 h1334 h13 hS hH hX
  obtain ⟨Y, hYR, hYq, hY4, hYinv⟩ := S.exists_quad_VH_elem h36c h139 h1334 h13 h13314 h13315
    h1356two hS hH hK hKn hHK hA
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := hYR.trans hRN
  set ER : Subgroup A6 :=
    ((R.subgroupOf (Subgroup.normalizer (K : Set G))).map (sigOf φ)).comap MulAut.conj with hER
  set EY : Subgroup A6 :=
    ((Y.subgroupOf (Subgroup.normalizer (K : Set G))).map (sigOf φ)).comap MulAut.conj with hEY
  have hinner : ∀ (y : G) (hy : y ∈ Y), ∃ a : A6, sigOf φ ⟨y, hYN hy⟩ = MulAut.conj a := by
    intro y hy
    refine exists_inner_sigOf hHat.2.1 φ (g := ⟨y, hYN hy⟩) (Subtype.ext (hYinv y hy)) ?_
    exact S.quotConj_center_of_mem_R h139 h1334 h13 hS hH hK hL1K hHat (hYR hy) (hYN hy)
  have hYmap : (Y.subgroupOf (Subgroup.normalizer (K : Set G))).map (sigOf φ) ≤
      (MulAut.conj : A6 →* MulAut A6).range := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, ha⟩ := hinner y (Subgroup.mem_subgroupOf.mp hy)
    exact ⟨a, ha.symm⟩
  have hk : Y.subgroupOf (Subgroup.normalizer (K : Set G)) ⊓ (sigOf φ).ker ≤
      (pCoreOf 2 H).subgroupOf (Subgroup.normalizer (K : Set G)) := by
    intro g hg
    have hgY : (g : G) ∈ Y := Subgroup.mem_subgroupOf.mp hg.1
    have hgk : sigOf φ g = 1 := MonoidHom.mem_ker.mp hg.2
    exact Subgroup.mem_subgroupOf.mpr (S.mem_QH_of_sigOf_eq_one hS hH hKn hHK hK φ (hYR hgY) hgk)
  have hEY4 : 4 ≤ Nat.card EY := by
    have h1 : Nat.card ↥(EY.map (MulAut.conj : A6 →* MulAut A6)) = Nat.card EY :=
      Subgroup.card_map_of_injective Hat6.conj_injective
    have h2 : EY.map MulAut.conj = (Y.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (sigOf φ) := Subgroup.map_comap_eq_self hYmap
    rw [h2, ← Subgroup.relIndex_ker] at h1
    rw [← h1]
    calc 4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y := hY4
      _ = (pCoreOf 2 H).relIndex Y := by rw [Subgroup.inf_relIndex_left]
      _ = ((pCoreOf 2 H).subgroupOf (Subgroup.normalizer (K : Set G))).relIndex
          (Y.subgroupOf (Subgroup.normalizer (K : Set G))) :=
        (Subgroup.relIndex_subgroupOf hYN).symm
      _ = (Y.subgroupOf (Subgroup.normalizer (K : Set G)) ⊓
          (pCoreOf 2 H).subgroupOf (Subgroup.normalizer (K : Set G))).relIndex
          (Y.subgroupOf (Subgroup.normalizer (K : Set G))) := by
        rw [Subgroup.inf_relIndex_left]
      _ ≤ (Y.subgroupOf (Subgroup.normalizer (K : Set G)) ⊓ (sigOf φ).ker).relIndex
          (Y.subgroupOf (Subgroup.normalizer (K : Set G))) :=
        Subgroup.relIndex_le_of_le_left (le_inf inf_le_left hk) Subgroup.index_ne_zero_of_finite
      _ = (sigOf φ).ker.relIndex (Y.subgroupOf (Subgroup.normalizer (K : Set G))) := by
        rw [Subgroup.inf_relIndex_left]
  have hER2 : IsPGroup 2 ER :=
    (((pCoreOf_isPGroup 2 (S.L1 ⊔ T)).comap_of_injective
      (Subgroup.normalizer (K : Set G)).subtype
      (Subgroup.normalizer (K : Set G)).subtype_injective).map (sigOf φ)).comap_of_injective _
      Hat6.conj_injective
  have hEYR : EY ≤ ER := by
    rintro e ⟨y, hy, hye⟩
    exact ⟨y, hYR hy, hye⟩
  have hpres : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)),
      g ∈ Subgroup.normalizer (R : Set G) → ∀ e ∈ ER, sigOf φ ⟨g, hg⟩ e ∈ ER := by
    intro g hg hgR e he
    obtain ⟨r, hr, hre⟩ := he
    refine ⟨⟨g, hg⟩ * r * (⟨g, hg⟩)⁻¹, ?_, ?_⟩
    · have hr' : (r : G) ∈ R := hr
      show ((⟨g, hg⟩ * r * (⟨g, hg⟩)⁻¹ : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ R
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hgR _).mp hr'
    · rw [map_mul, map_mul, map_inv, hre, conj_apply_aut]
  have hnormER : ∀ u : A6, (∀ e ∈ ER, u * e * u⁻¹ ∈ ER) →
      u ∈ Subgroup.normalizer (ER : Set A6) := fun u hu => Subgroup.mem_normalizer_fintype hu
  have hmemN : ∀ (g : G) (hgK : g ∈ K), g ∈ Subgroup.normalizer (R : Set G) →
      piOf φ ⟨g, hgK⟩ ∈ Subgroup.normalizer (ER : Set A6) := by
    intro g hgK hgR
    apply hnormER
    intro e he
    have h1 := hpres g (hKn (hKH hgK)) hgR e he
    rwa [sigOf_of_mem φ ⟨g, hKn (hKH hgK)⟩ hgK, MulAut.conj_apply] at h1
  obtain ⟨l, hlL, hl3, hlZ⟩ : ∃ l ∈ S.L1, l ^ 3 = 1 ∧ l ∉ oTwoZIn K := by
    by_contra hcon
    push Not at hcon
    apply hL1Z
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxLN, m, hm, hxm⟩
    have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨hxLN, m, hm, hxm⟩
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, S.cube_mem_pCoreOf_L1' hxL1⟩
      have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
        (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk')
    exact hcon x hxL1 hx3
  have hlK : l ∈ K := hL1K hlL
  have hx3 : orderOf (piOf φ ⟨l, hlK⟩) = 3 := by
    have h3 : piOf φ ⟨l, hlK⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨l, hlK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simp [hl3])
      rw [this, map_one]
    exact orderOf_eq_prime h3 fun h => hlZ ((piOf_eq_one_iff φ _).mp h)
  have hxN := hmemN l hlK (hLTR (Subgroup.mem_sup_left hlL))
  have hD0N : D0 ≤ Subgroup.normalizer (ER : Set A6) := by
    rw [← hD]
    rintro _ ⟨t, ht, rfl⟩
    exact hmemN t t.2 (hLTR (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp ht)))
  have hERD : ER ≤ D0 := le_D0_of_normalizes hER2 hD0N
  have hERne : ER ≠ D0 := ne_D0_of_normalizes hx3 hxN
  have hER4 : Nat.card ER ≤ 4 := by
    have hdvd : Nat.card ER ∣ 2 ^ 3 := by
      have := Subgroup.card_dvd_of_le hERD
      rwa [card_D0] at this
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj3 : j ≠ 3 := by
      rintro rfl
      exact hERne (Subgroup.eq_of_le_of_card_ge hERD (by rw [hj', card_D0]; norm_num))
    rw [hj']
    calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hEYeq : EY = ER := Subgroup.eq_of_le_of_card_ge hEYR (by omega)
  have hEY4' : Nat.card EY = 4 := by
    have := Subgroup.card_le_of_le hEYR
    omega
  have hEYinv : ∀ e ∈ EY, e * e = 1 := by
    rintro e ⟨y, hy, hye⟩
    apply Hat6.conj_injective
    have hyy : y * y = 1 := Subtype.ext (hYinv _ (Subgroup.mem_subgroupOf.mp hy))
    rw [map_mul, ← hye, ← map_mul, hyy, map_one, map_one]
  obtain ⟨N, α, β, hNE, hN24, hαE, hβE, hconst⟩ : ∃ (N : Subgroup A6) (α β : A6),
      N = Subgroup.normalizer (ER : Set A6) ∧ Nat.card N = 24 ∧ α ∈ ER ∧ β ∈ ER ∧
      ∀ (W : Type) [CommGroup W] (w : A6 → W), (∀ g : A6, ∀ n ∈ N, w (g * n) = w g) →
        (∀ h g : A6, w g * w (h * α * h⁻¹ * g) * w (h * β * h⁻¹ * g) *
          w (h * β * h⁻¹ * (h * α * h⁻¹) * g) = 1) → ∀ g : A6, w g = w 1 := by
    rcases eq_E1_or_E2 (hEYR.trans hERD) hEY4' hEYinv with hE | hE
    · have hE' : ER = L32A.C.Alt6.E1 := hEYeq.symm.trans hE
      refine ⟨N1, zA, aA, by rw [hE']; rfl, card_N1, ?_, ?_,
        fun W _ w hN hrel g => const_of_rel_E1 w hN hrel g⟩
      · rw [hE']
        exact mem_E1.mpr (by
          show L32A.C.Alt6.z6 ∈ L32A.C.Alt6.e1List
          simp [L32A.C.Alt6.e1List])
      · rw [hE']
        exact mem_E1.mpr (by
          show L32A.C.Alt6.a6 ∈ L32A.C.Alt6.e1List
          simp [L32A.C.Alt6.e1List])
    · have hE' : ER = L32A.C.Alt6.E2 := hEYeq.symm.trans hE
      refine ⟨N2, zA, bA, by rw [hE']; rfl, card_N2, ?_, ?_,
        fun W _ w hN hrel g => const_of_rel_E2 w hN hrel g⟩
      · rw [hE']
        exact mem_E2.mpr (by
          show L32A.C.Alt6.z6 ∈ L32A.C.Alt6.e2List
          simp [L32A.C.Alt6.e2List])
      · rw [hE']
        exact mem_E2.mpr (by
          show L32A.C.Alt6.b6 ∈ L32A.C.Alt6.e2List
          simp [L32A.C.Alt6.e2List])
  set X₀ : Subgroup G := parab (piOf φ) N with hX₀
  have hL1X : S.L1 ≤ X₀ := fun l' hl' => mem_parab.mpr ⟨hL1K hl', by
    rw [hNE]
    exact hmemN l' (hL1K hl') (hLTR (Subgroup.mem_sup_left hl'))⟩
  have hpresT : ∀ (t : G) (ht : t ∈ T), ∀ n ∈ N, sigOf φ ⟨t, hKn (hTH ht)⟩ n ∈ N := by
    intro t ht n hn
    have htN := hKn (hTH ht)
    have htR := hLTR (Subgroup.mem_sup_right ht)
    have hle : ER.map (sigOf φ ⟨t, htN⟩).toMonoidHom ≤ ER := by
      rintro _ ⟨e, he, rfl⟩
      exact hpres t htN htR e he
    have heq := map_eq_of_le (sigOf φ ⟨t, htN⟩).toMonoidHom (sigOf φ ⟨t, htN⟩).injective hle
      le_rfl
    rw [hNE] at hn ⊢
    exact hnormER _ fun e he => map_normalizes _ heq hn he
  have hTX : T ≤ Subgroup.normalizer (X₀ : Set G) := by
    have one_dir : ∀ t ∈ T, ∀ k ∈ X₀, t * k * t⁻¹ ∈ X₀ := by
      intro t ht k hk
      obtain ⟨hkK, hkN⟩ := mem_parab.mp hk
      have htN := hKn (hTH ht)
      have hk' : t * k * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htN k).mp hkK
      refine mem_parab.mpr ⟨hk', ?_⟩
      have h1 : piOf φ ⟨t * k * t⁻¹, hk'⟩ = sigOf φ ⟨t, htN⟩ (piOf φ ⟨k, hkK⟩) :=
        (sigOf_piOf φ ⟨t, htN⟩ ⟨k, hkK⟩).symm
      rw [h1]
      exact hpresT t ht _ hkN
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨one_dir t ht g, fun hg => ?_⟩
    have := one_dir t⁻¹ (T.inv_mem ht) _ hg
    simpa [mul_assoc] using this
  obtain ⟨c, hcK⟩ := exists_card_of_hat6 hHat
  have hsolv := L32A.C.isSolvable_parab_sup (piOf_surjective φ) hN24 hT2 hTX hcK
  have hXM : X₀ ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    h13 G T L V S hS (X₀ ⊔ T) (sup_le (hL1X.trans le_sup_left) le_sup_right)
      ((sup_le ((Subgroup.map_subtype_le _).trans hKH) hTH).trans hH.2.1) hsolv
  have hkerM : ∀ (m : G) (hm : m ∈ H), sigOf φ ⟨m, hKn hm⟩ = 1 →
      m ∈ Subgroup.normalizer (L : Set G) := by
    intro m hm h1
    have hm' : m ∈ ((K ⊔ T : Subgroup G) : Set G) := by rw [← hHT]; exact hm
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K T (hTH.trans hKn)] at hm'
    obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hm'
    have hkN := hKn (hKH hk)
    have htN := hKn (hTH ht)
    have h2 : sigOf φ ⟨k, hkN⟩ * sigOf φ ⟨t, htN⟩ = 1 := by rw [← map_mul]; exact h1
    rw [sigOf_of_mem φ ⟨k, hkN⟩ hk] at h2
    have hst : sigOf φ ⟨t, htN⟩ = MulAut.conj (piOf φ ⟨k, hk⟩)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right h2
    have hkE : (piOf φ ⟨k, hk⟩)⁻¹ ∈ Subgroup.normalizer (ER : Set A6) := by
      apply hnormER
      intro e he
      have h3 := hpres t htN (hLTR (Subgroup.mem_sup_right ht)) e he
      rwa [hst, MulAut.conj_apply] at h3
    have hkX : k ∈ X₀ := mem_parab.mpr ⟨hk, by
      rw [hNE]
      have := Subgroup.inv_mem _ hkE
      rwa [inv_inv] at this⟩
    exact Subgroup.mul_mem _ (hXM (Subgroup.mem_sup_left hkX)) (S.T_le_NL ht)
  have hquad : ∀ v ∈ conjClosure V H, ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ⁅⁅v, y₁⁆, y₂⁆ = 1 := by
    intro v hv y₁ hy₁ y₂ hy₂
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hv hy₁) hy₂
    rw [hYq] at h1
    exact h1
  have hVab : IsElemAbelian 2 (conjClosure V H) :=
    HypF91.isElemAbelian_conjClosure_of_forall S.elemAbelian_V fun k hk v hv => by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : v ∈ conjClosure V S.G1 := le_conjClosure V S.G1 hv
      have h2 : w ∈ conjClosure V S.G1 := HypF91.conjSub_le_conjClosure (hH.2.1 hk) hw
      exact congrArg Subtype.val (hS.hab.is_comm.comm ⟨w, h2⟩ ⟨v, h1⟩)
  set VH := conjClosure V H with hVHdef
  set UH := conjClosure S.V3 H with hUHdef
  have hUN : H ≤ Subgroup.normalizer (UH : Set G) := le_normalizer_conjClosure S.V3 H
  have hVN : H ≤ Subgroup.normalizer (VH : Set G) := le_normalizer_conjClosure V H
  have hconjG : ∀ g : G, g ∈ H → ∀ x ∈ VH, g * x * g⁻¹ ∈ VH := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hVN hg) x).mp hx
  obtain ⟨v₀, hv₀V, hv₀U⟩ :=
    IsConcreteLE.not_le_iff_exists.mp (S.V_not_le_UH hS.hNS h13315 h1356two hH h13314)
  have hv₀VH : v₀ ∈ VH := le_conjClosure V H hv₀V
  have hidx : (S.V3.subgroupOf V).index = 2 := S.relIndex_V3_V
  have hV3U : S.V3 ≤ UH := le_conjClosure _ _
  have hmodV : ∀ u ∈ V, ∀ v ∈ V, u ∉ UH → v ∉ UH → u * v⁻¹ ∈ UH := by
    intro u hu v hv huU hvU
    have hu3 : (⟨u, hu⟩ : ↥V) ∉ S.V3.subgroupOf V := fun h =>
      huU (hV3U (Subgroup.mem_subgroupOf.mp h))
    have hv3 : (⟨v, hv⟩ : ↥V)⁻¹ ∉ S.V3.subgroupOf V := fun h => hvU (by
      have h1 := UH.inv_mem (hV3U (Subgroup.mem_subgroupOf.mp h))
      simpa using h1)
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hu3 hv3)
    exact hV3U (Subgroup.mem_subgroupOf.mp h1)
  have : IsMulCommutative ↥VH := hVab.1
  set NW : Subgroup ↥VH := UH.subgroupOf VH with hNW
  let mkW : ∀ x : G, x ∈ VH → ↥VH ⧸ NW := fun x hx => QuotientGroup.mk ⟨x, hx⟩
  have mkW_congr : ∀ (x y : G) (hx : x ∈ VH) (hy : y ∈ VH), x = y → mkW x hx = mkW y hy := by
    intro x y hx hy h
    subst h
    rfl
  have mkW_eq : ∀ (x y : G) (hx : x ∈ VH) (hy : y ∈ VH), mkW x hx = mkW y hy ↔ x⁻¹ * y ∈ UH := by
    intro x y hx hy
    show (QuotientGroup.mk _ : ↥VH ⧸ NW) = QuotientGroup.mk _ ↔ _
    rw [QuotientGroup.eq, hNW, Subgroup.mem_subgroupOf]
    rfl
  have mkW_mul : ∀ (x y : G) (hx : x ∈ VH) (hy : y ∈ VH),
      mkW (x * y) (VH.mul_mem hx hy) = mkW x hx * mkW y hy := fun _ _ _ _ => rfl
  have mkW_inv : ∀ (x : G) (hx : x ∈ VH), mkW x⁻¹ (VH.inv_mem hx) = (mkW x hx)⁻¹ :=
    fun _ _ => rfl
  have hW2 : ∀ q : ↥VH ⧸ NW, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul]
      have h1 : x * x = 1 := Subtype.ext (by
        have := hVab.2 x x.2
        rw [sq] at this
        simpa using this)
      rw [h1, QuotientGroup.mk_one]
  have hinv : ∀ q : ↥VH ⧸ NW, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (hW2 q)
  have hRt : ∀ (h m : G) (hh : h ∈ H) (hmH : m ∈ H), m ∈ Subgroup.normalizer (L : Set G) →
      mkW ((h * m) * v₀ * (h * m)⁻¹) (hconjG _ (H.mul_mem hh hmH) v₀ hv₀VH) =
        mkW (h * v₀ * h⁻¹) (hconjG h hh v₀ hv₀VH) := by
    intro h m hh hmH hmM
    have hmV : m ∈ Subgroup.normalizer (V : Set G) := S.inf_M_le_NV' hH ⟨hmH, hmM⟩
    set u := m * v₀ * m⁻¹ with hu
    have huV : u ∈ V := (Subgroup.mem_normalizer_iff.mp hmV v₀).mp hv₀V
    have huU : u ∉ UH := by
      intro hU
      apply hv₀U
      have h1 := (Subgroup.mem_normalizer_iff.mp (hUN (H.inv_mem hmH)) u).mp hU
      have e' : m⁻¹ * u * m⁻¹⁻¹ = v₀ := by rw [hu]; group
      rwa [e'] at h1
    have h1 : u⁻¹ * v₀ ∈ UH := by
      have h2 := hmodV u⁻¹ (V.inv_mem huV) v₀⁻¹ (V.inv_mem hv₀V)
        (fun h => huU (by simpa using UH.inv_mem h)) (fun h => hv₀U (by simpa using UH.inv_mem h))
      simpa using h2
    rw [mkW_eq]
    have e' : ((h * m) * v₀ * (h * m)⁻¹)⁻¹ * (h * v₀ * h⁻¹) = h * (u⁻¹ * v₀) * h⁻¹ := by
      rw [hu]
      group
    rw [e']
    exact (Subgroup.mem_normalizer_iff.mp (hUN hh) _).mp h1
  have hlift : ∀ a : A6, ∃ k : G, ∃ hk : k ∈ K, piOf φ ⟨k, hk⟩ = a := fun a => by
    obtain ⟨k, hk⟩ := piOf_surjective φ a
    exact ⟨k, k.2, hk⟩
  choose kq hkqK hkq using hlift
  have hkqH : ∀ a, kq a ∈ H := fun a => hKH (hkqK a)
  have hσkq : ∀ a, sigOf φ ⟨kq a, hKn (hkqH a)⟩ = MulAut.conj a := fun a => by
    rw [sigOf_of_mem φ _ (hkqK a), hkq]
  let w : A6 → ↥VH ⧸ NW := fun a => mkW (kq a * v₀ * (kq a)⁻¹) (hconjG _ (hkqH a) v₀ hv₀VH)
  have hinn : ∀ (h : G) (hh : h ∈ H) (a : A6), sigOf φ ⟨h, hKn hh⟩ = MulAut.conj a →
      mkW (h * v₀ * h⁻¹) (hconjG h hh v₀ hv₀VH) = w a := by
    intro h hh a ha
    have hmH : (kq a)⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hkqH a)) hh
    have hσm : sigOf φ ⟨(kq a)⁻¹ * h, hKn hmH⟩ = 1 := by
      have e1 : (⟨(kq a)⁻¹ * h, hKn hmH⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          (⟨kq a, hKn (hkqH a)⟩)⁻¹ * ⟨h, hKn hh⟩ := rfl
      rw [e1, map_mul, map_inv, hσkq, ha, inv_mul_cancel]
    have h1 := hRt (kq a) ((kq a)⁻¹ * h) (hkqH a) hmH (hkerM _ hmH hσm)
    show mkW (h * v₀ * h⁻¹) _ = mkW (kq a * v₀ * (kq a)⁻¹) _
    rw [← h1]
    exact mkW_congr _ _ _ _ (by group)
  have hNw : ∀ g : A6, ∀ n ∈ N, w (g * n) = w g := by
    intro g n hn
    have hnX : kq n ∈ X₀ := mem_parab.mpr ⟨hkqK n, by rw [hkq]; exact hn⟩
    have hnM : kq n ∈ Subgroup.normalizer (L : Set G) := hXM (Subgroup.mem_sup_left hnX)
    have hgn : kq g * kq n ∈ H := H.mul_mem (hkqH g) (hkqH n)
    have h1 := hinn (kq g * kq n) hgn (g * n) (by
      have e1 : (⟨kq g * kq n, hKn hgn⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨kq g, hKn (hkqH g)⟩ * ⟨kq n, hKn (hkqH n)⟩ := rfl
      rw [e1, map_mul, hσkq, hσkq, map_mul])
    rw [← h1, hRt (kq g) (kq n) (hkqH g) (hkqH n) hnM]
  have h4term : ∀ (a b x : G) (ha : a ∈ H) (hb : b ∈ H) (hx : x ∈ VH),
      (∀ v ∈ VH, ⁅⁅v, a⁆, b⁆ = 1) →
      mkW x hx * mkW (a * x * a⁻¹) (hconjG a ha x hx) * mkW (b * x * b⁻¹) (hconjG b hb x hx) *
        mkW (b * (a * x * a⁻¹) * b⁻¹) (hconjG b hb _ (hconjG a ha x hx)) = 1 := by
    intro a b x ha hb hx hab
    have hcomm : b * (x * (a * x * a⁻¹)⁻¹) * b⁻¹ = x * (a * x * a⁻¹)⁻¹ := by
      have hc := hab x hx
      have h1 : ⁅x, a⁆ = x * (a * x * a⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [h1] at hc
      rw [← (commutatorElement_eq_one_iff_commute.mp hc).eq, mul_inv_cancel_right]
    have hrel : mkW (b * x * b⁻¹) (hconjG b hb x hx) *
        (mkW (b * (a * x * a⁻¹) * b⁻¹) (hconjG b hb _ (hconjG a ha x hx)))⁻¹ =
        mkW x hx * (mkW (a * x * a⁻¹) (hconjG a ha x hx))⁻¹ := by
      rw [← mkW_inv, ← mkW_inv, ← mkW_mul, ← mkW_mul]
      exact mkW_congr _ _ _ _ (by rw [← hcomm]; group)
    rw [hinv, hinv] at hrel
    rw [mul_assoc (mkW x hx * mkW (a * x * a⁻¹) (hconjG a ha x hx)), hrel]
    exact hW2 _
  obtain ⟨yα, hyαY, hyα⟩ : ∃ y : G, ∃ hy : y ∈ Y, sigOf φ ⟨y, hYN hy⟩ = MulAut.conj α := by
    rw [← hEYeq] at hαE
    obtain ⟨y, hy, hye⟩ := hαE
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hye⟩
  obtain ⟨yβ, hyβY, hyβ⟩ : ∃ y : G, ∃ hy : y ∈ Y, sigOf φ ⟨y, hYN hy⟩ = MulAut.conj β := by
    rw [← hEYeq] at hβE
    obtain ⟨y, hy, hye⟩ := hβE
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hye⟩
  have hrelw : ∀ h g : A6, w g * w (h * α * h⁻¹ * g) * w (h * β * h⁻¹ * g) *
      w (h * β * h⁻¹ * (h * α * h⁻¹) * g) = 1 := by
    intro h g
    have hkH : kq h ∈ H := hkqH h
    have hyαH : yα ∈ H := hRH (hYR hyαY)
    have hyβH : yβ ∈ H := hRH (hYR hyβY)
    have ha'H : kq h * yα * (kq h)⁻¹ ∈ H := H.mul_mem (H.mul_mem hkH hyαH) (H.inv_mem hkH)
    have hb'H : kq h * yβ * (kq h)⁻¹ ∈ H := H.mul_mem (H.mul_mem hkH hyβH) (H.inv_mem hkH)
    have hσa : sigOf φ ⟨kq h * yα * (kq h)⁻¹, hKn ha'H⟩ = MulAut.conj (h * α * h⁻¹) := by
      have e1 : (⟨kq h * yα * (kq h)⁻¹, hKn ha'H⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨kq h, hKn hkH⟩ * ⟨yα, hYN hyαY⟩ * (⟨kq h, hKn hkH⟩)⁻¹ := rfl
      rw [e1, map_mul (sigOf φ), map_mul (sigOf φ), map_inv (sigOf φ), hσkq, hyα]
      simp only [map_mul, map_inv]
    have hσb : sigOf φ ⟨kq h * yβ * (kq h)⁻¹, hKn hb'H⟩ = MulAut.conj (h * β * h⁻¹) := by
      have e1 : (⟨kq h * yβ * (kq h)⁻¹, hKn hb'H⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨kq h, hKn hkH⟩ * ⟨yβ, hYN hyβY⟩ * (⟨kq h, hKn hkH⟩)⁻¹ := rfl
      rw [e1, map_mul (sigOf φ), map_mul (sigOf φ), map_inv (sigOf φ), hσkq, hyβ]
      simp only [map_mul, map_inv]
    have hq : ∀ v ∈ VH, ⁅⁅v, kq h * yα * (kq h)⁻¹⁆, kq h * yβ * (kq h)⁻¹⁆ = 1 := by
      intro v hv
      have hv' : (kq h)⁻¹ * v * kq h ∈ VH := by
        simpa using hconjG (kq h)⁻¹ (H.inv_mem hkH) v hv
      have h1 := hquad _ hv' yα hyαY yβ hyβY
      have e' : ⁅⁅v, kq h * yα * (kq h)⁻¹⁆, kq h * yβ * (kq h)⁻¹⁆ =
          kq h * ⁅⁅(kq h)⁻¹ * v * kq h, yα⁆, yβ⁆ * (kq h)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e', h1, mul_one, mul_inv_cancel]
    have hgH := hkqH g
    have hxVH : kq g * v₀ * (kq g)⁻¹ ∈ VH := hconjG _ hgH v₀ hv₀VH
    have e1 : w (h * α * h⁻¹ * g) = mkW ((kq h * yα * (kq h)⁻¹) * (kq g * v₀ * (kq g)⁻¹) *
        (kq h * yα * (kq h)⁻¹)⁻¹) (hconjG _ ha'H _ hxVH) := by
      have hh : (kq h * yα * (kq h)⁻¹) * kq g ∈ H := H.mul_mem ha'H hgH
      rw [← hinn _ hh (h * α * h⁻¹ * g) (by
        have e : (⟨(kq h * yα * (kq h)⁻¹) * kq g, hKn hh⟩ :
            ↥(Subgroup.normalizer (K : Set G))) =
            ⟨kq h * yα * (kq h)⁻¹, hKn ha'H⟩ * ⟨kq g, hKn hgH⟩ := rfl
        rw [e, map_mul (sigOf φ), hσa, hσkq]
        exact (map_mul MulAut.conj _ _).symm)]
      exact mkW_congr _ _ _ _ (by group)
    have e2 : w (h * β * h⁻¹ * g) = mkW ((kq h * yβ * (kq h)⁻¹) * (kq g * v₀ * (kq g)⁻¹) *
        (kq h * yβ * (kq h)⁻¹)⁻¹) (hconjG _ hb'H _ hxVH) := by
      have hh : (kq h * yβ * (kq h)⁻¹) * kq g ∈ H := H.mul_mem hb'H hgH
      rw [← hinn _ hh (h * β * h⁻¹ * g) (by
        have e : (⟨(kq h * yβ * (kq h)⁻¹) * kq g, hKn hh⟩ :
            ↥(Subgroup.normalizer (K : Set G))) =
            ⟨kq h * yβ * (kq h)⁻¹, hKn hb'H⟩ * ⟨kq g, hKn hgH⟩ := rfl
        rw [e, map_mul (sigOf φ), hσb, hσkq]
        exact (map_mul MulAut.conj _ _).symm)]
      exact mkW_congr _ _ _ _ (by group)
    have e3 : w (h * β * h⁻¹ * (h * α * h⁻¹) * g) =
        mkW ((kq h * yβ * (kq h)⁻¹) * ((kq h * yα * (kq h)⁻¹) * (kq g * v₀ * (kq g)⁻¹) *
          (kq h * yα * (kq h)⁻¹)⁻¹) * (kq h * yβ * (kq h)⁻¹)⁻¹)
          (hconjG _ hb'H _ (hconjG _ ha'H _ hxVH)) := by
      have hh : (kq h * yβ * (kq h)⁻¹) * (kq h * yα * (kq h)⁻¹) * kq g ∈ H :=
        H.mul_mem (H.mul_mem hb'H ha'H) hgH
      rw [← hinn _ hh (h * β * h⁻¹ * (h * α * h⁻¹) * g) (by
        have e : (⟨(kq h * yβ * (kq h)⁻¹) * (kq h * yα * (kq h)⁻¹) * kq g, hKn hh⟩ :
            ↥(Subgroup.normalizer (K : Set G))) =
            ⟨kq h * yβ * (kq h)⁻¹, hKn hb'H⟩ * ⟨kq h * yα * (kq h)⁻¹, hKn ha'H⟩ *
              ⟨kq g, hKn hgH⟩ := rfl
        rw [e, map_mul (sigOf φ), map_mul (sigOf φ), hσa, hσb, hσkq]
        simp only [map_mul])]
      exact mkW_congr _ _ _ _ (by group)
    have e0 : w g = mkW (kq g * v₀ * (kq g)⁻¹) hxVH := rfl
    rw [e0, e1, e2, e3]
    exact h4term _ _ _ ha'H hb'H hxVH hq
  have hc := hconst (↥VH ⧸ NW) w hNw hrelw
  have hw₀ : ∀ h ∈ H, (h * v₀ * h⁻¹)⁻¹ * v₀ ∈ UH := by
    intro h hh
    have hh' : h ∈ ((K ⊔ T : Subgroup G) : Set G) := by rw [← hHT]; exact hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K T (hTH.trans hKn)] at hh'
    obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hh'
    have hkH := hKH hk
    have h1 := hRt k t hkH (hTH ht) (S.T_le_NL ht)
    have h2 := hinn k hkH (piOf φ ⟨k, hk⟩) (sigOf_of_mem φ ⟨k, hKn hkH⟩ hk)
    have h3 := hinn 1 H.one_mem 1 (by
      rw [show (⟨1, hKn H.one_mem⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 from rfl, map_one,
        map_one])
    rw [hc, ← h3] at h2
    rw [h2] at h1
    have h4 := (mkW_eq _ _ _ _).mp h1
    rwa [one_mul, inv_one, mul_one] at h4
  have hfinal : conjClosure V H ≤ V ⊔ UH := by
    refine conjClosure_le fun g hg v hv => ?_
    by_cases hvU : v ∈ UH
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hUN hg) v).mp hvU)
    · have h1 : v * v₀⁻¹ ∈ UH := hmodV v hv v₀ hv₀V hvU hv₀U
      have h2 := hw₀ g hg
      have e' : g * v * g⁻¹ = (g * (v * v₀⁻¹) * g⁻¹) * (v₀ * ((g * v₀ * g⁻¹)⁻¹ * v₀)⁻¹) := by
        group
      rw [e']
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hUN hg) _).mp h1))
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left hv₀V) (Subgroup.mem_sup_right (UH.inv_mem h2)))
  exact S.VH_not_le_V_sup_UH hS.hNS h13315 h1356two hH h13314 hfinal

theorem false_of_hat6
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hFine : F918Fine4Hat6) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) (hF918 : HypF918 T V L (fsuV1 T V) S.V3 H K)
    (hHat : IsHat (Kq K) A6) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hF := (hS.hF H hH).toHypF91
  have hL1K := S.L1_le_of_hat6 hF318 h36 h38 hH hK hKn hHat
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hF.sylow_H hKH hKn
  obtain ⟨φ, hD⟩ := Hat6.exists_phi_D0 hHat hTsyl hF.sylow_H.2.1
  by_cases hL1Z : S.L1 ≤ oTwoZIn K
  · exact S.false_of_hat6_central h13 hFine hS hH hK hKn hHK hF918 hHat φ hD hL1Z
  · exact S.false_of_hat6_noncentral h36c h139 h1334 h13 h13314 h13315 h1356two hS hH hK hKn hHK
      hHat hL1K φ hD hL1Z

end Setting4

theorem case13821Hat6_holds (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hFine : F918Fine4Hat6) : Case13821Hat6 := by
  intro G _ _ T L V S hS H hH K hK hHat
  obtain ⟨-, hH₀z, -, hK₀, hKn₀, hF₀⟩ := S.reduce13821 h16 h36c h37 h38 h139 h1334 h13 hS hH hK
  exact S.false_of_hat6 h36c h36 h38 hF318 h139 h1334 h13 h13314 h13315 h1356two hFine hS hH₀z
    hK₀ hKn₀ rfl hF₀ hHat

end CFSG.Quasithin.H13.A6
