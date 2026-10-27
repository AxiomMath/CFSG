module

public import CFSG.Quasithin.H13.A6S13821zc
public import CFSG.Quasithin.H13.A6S1372L74i
public import CFSG.Quasithin.H13.A6S1372L76Y

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.E1.LiftS5

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_p0_l24
    (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) :
    ∃ p₀ : Fin 5,
      (∀ x (hx : x ∈ T ⊓ K), A6L24.IsV4 p₀ (quotPerm hKn e ⟨x, le_of_mem_cComp hK hx.2⟩)) ∧
      (∀ τ, A6L24.IsV4 p₀ τ →
        ∃ x, ∃ hx : x ∈ T ⊓ K, quotPerm hKn e ⟨x, le_of_mem_cComp hK hx.2⟩ = τ) ∧
      (∀ g : ↥H, quotPerm hKn e g p₀ = p₀ ↔
        (g : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) ∧
      ∀ g : ↥H, (g : G) ∈ S.L1 ⊔ T → quotPerm hKn e g p₀ = p₀ := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hsyl := S.isSylowTwoOf_TK hH hKH hKn
  obtain ⟨p₀, hp₀, hp₀'⟩ := A6L24.exists_p0 hKH hKn e hsyl
  have hiff := A6L24.fix_iff hKH hKn e hsyl (S.pCoreOf_le_TK hH hKH hKn) hp₀ hp₀'
  exact ⟨p₀, hp₀, hp₀', hiff, fun g hg =>
    (hiff g).mpr (S.L1T_le_normalizer_TK h1334 hS hH hKH hKn hn hLie hg)⟩

theorem false_of_hat_l24
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (hhat : IsHatA6 L) {t : G}
    (htT : t ∈ T) (htL : t ∈ L)
    (hout : ∀ k ∈ K, ∃ y ∈ K, (t * k⁻¹) * y * (t * k⁻¹)⁻¹ * y⁻¹ ∉ pCoreOf 2 K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  obtain ⟨p₀, -, -, -, hfix⟩ := S.exists_p0_l24 h1334 hS hH hK hKn hn hLie e
  have htH := hTH htT
  have hts : Perm.sign (quotPerm hKn e ⟨t, htH⟩) = -1 :=
    A6L24.sign_eq_neg_one hKH hKn e ⟨t, htH⟩ hout
  have htp : quotPerm hKn e ⟨t, htH⟩ p₀ = p₀ := hfix _ (Subgroup.mem_sup_right htT)
  obtain ⟨c, hcL0, hc3, -, hdec⟩ := l0_decomp hhat
  have hcL1 : c ∈ S.L1 := S.l0_le_L1 hcL0
  have hcH := hL1H hcL1
  have hcp : quotPerm hKn e ⟨c, hcH⟩ p₀ = p₀ := hfix _ (Subgroup.mem_sup_left hcL1)
  have hψc3 : quotPerm hKn e ⟨c, hcH⟩ ^ 3 = 1 := by
    have h1 : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [← map_pow, h1, map_one]
  by_cases hc1 : quotPerm hKn e ⟨c, hcH⟩ = 1
  ·
    have hker : l0 L ≤ (quotPerm hKn e).ker.map H.subtype := by
      rw [l0, oTwoRes, Subgroup.closure_le]
      rintro w ⟨hwZ, m, hm, hwm⟩
      have hwL0 : w ∈ l0 L := Subgroup.subset_closure ⟨hwZ, m, hm, hwm⟩
      have hwH : w ∈ H := hL1H (S.l0_le_L1 hwL0)
      refine ⟨⟨w, hwH⟩, ?_, rfl⟩
      have h2 : quotPerm hKn e ⟨w, hwH⟩ ^ 4 = 1 := by
        rcases hdec w hwL0 with h | h | h
        · obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (l0 L) ⟨w, h⟩
          exact A6L24.pow_four_eq_one hKn e (k := k) (by simpa using congrArg Subtype.val hk)
        · obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (l0 L) ⟨_, h⟩
          have h1 := A6L24.pow_four_eq_one hKn e
            (g := ⟨c, hcH⟩ * ⟨c, hcH⟩ * ⟨w, hwH⟩) (k := k) (by simpa using congrArg Subtype.val hk)
          rwa [map_mul, map_mul, hc1, one_mul, one_mul] at h1
        · obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (l0 L) ⟨_, h⟩
          have h1 := A6L24.pow_four_eq_one hKn e (g := ⟨c, hcH⟩ * ⟨w, hwH⟩) (k := k)
            (by simpa using congrArg Subtype.val hk)
          rwa [map_mul, hc1, one_mul] at h1
      have hm' : quotPerm hKn e ⟨w, hwH⟩ ^ m = 1 := by
        have h1 : (⟨w, hwH⟩ : ↥H) ^ m = 1 := Subtype.ext (by simpa using hwm)
        rw [← map_pow, h1, map_one]
      have hcop : Nat.gcd 4 m = 1 := by
        have h1 := (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)).gcd_eq_one
        norm_num at h1
        exact h1
      have h3 := pow_gcd_eq_one.mpr ⟨h2, hm'⟩
      rw [hcop, pow_one] at h3
      exact h3
    have h0 : l0 L ≤ centralizerMod (pCoreOf 2 K) S.L1 K := by
      intro w hw
      obtain ⟨g, hg, rfl⟩ := hker hw
      have hchar : (CFSG.Open.pCore 2 ↥K).Characteristic := by
        infer_instance
      refine ⟨S.l0_le_L1 hw, ?_, (A6L24.quotPerm_eq_one_iff hKn e g).mp hg⟩
      exact (hKn.trans (normalizer_le_normalizer_map_of_characteristic
        (CFSG.Open.pCore 2 ↥K))) g.2
    have hKM : K ≤ Subgroup.normalizer (L : Set G) :=
      (S.le_normalizer_l0_of hH hK h0).trans (S.normalizer_l0_le_M hhat)
    exact (S.lem13812_one h139 h37 h38 hH hK).1 hKM
  ·
    obtain ⟨-, hcomm⟩ := mem_o2Z_iff.mp (oTwoRes_le _ hcL0)
    have h1 : c * t * c⁻¹ * t⁻¹ ∈ pCoreOf 2 L := hcomm t htL
    have h2 : t * c * t⁻¹ * c⁻¹ ∈ pCoreOf 2 L := by
      have h3 := (pCoreOf 2 L).inv_mem h1
      rwa [show (c * t * c⁻¹ * t⁻¹)⁻¹ = t * c * t⁻¹ * c⁻¹ by group] at h3
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, h2⟩
    have h3 := A6L24.pow_four_eq_one hKn e
      (g := ⟨t, htH⟩ * ⟨c, hcH⟩ * (⟨t, htH⟩ : ↥H)⁻¹ * (⟨c, hcH⟩ : ↥H)⁻¹) (k := k)
      (by simpa using congrArg Subtype.val hk)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    exact A6L24.comm_pow_four_ne p₀ _ ⟨hcp, hψc3, hc1⟩ _ ⟨htp, hts⟩ h3

theorem L1_le_of_l24
    (h1337 : Stmt13_3_7) (h13 : Lem13813) (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (hhat : ¬ IsHatA6 L) :
    S.L1 ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hL1K
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨p₀, -, -, hiff, -⟩ := S.exists_p0_l24 h1334 hS hH hK hKn hn hLie e
  obtain ⟨c, hcp, hcs, hc3, hc1⟩ := A6L24.exists_three p₀
  obtain ⟨k, hkK, hkc⟩ := A6L24.exists_lift hKH hKn e (Perm.mem_alternatingGroup.mpr hcs)
  have hkN := (hiff k).mp (by rw [hkc]; exact hcp)
  have hkM : (k : G) ∈ Subgroup.normalizer (L : Set G) :=
    S.borel_le_M h13 h1334 hS hH hKH hKn hn hLie ⟨hkK, hkN⟩
  have hk3 : (k : G) ^ 3 ∈ pCoreOf 2 K := by
    have h1 := (A6L24.quotPerm_eq_one_iff_of_mem hKn e (k ^ 3) (by simpa using K.pow_mem hkK 3)).mp
      (by rw [map_pow, hkc, hc3])
    simpa using h1
  obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 K ⟨_, hk3⟩
  have ha' : ((k : G) ^ 3) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hd3 : ((k : G) ^ 2 ^ a) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha']
  have hd1 := Setting4.eq_one_of_cube_of_mem_M hH h1337 hhat hKH hKn hL1K (K.pow_mem hkK _) hd3
    ((Subgroup.normalizer (L : Set G)).pow_mem hkM _)
  have hc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have h1 : c ^ 2 ^ a = 1 := by
    have h2 : k ^ 2 ^ a = 1 := Subtype.ext (by simpa using hd1)
    rw [← hkc, ← map_pow, h2, map_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hc] at h2
  have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h2)
  omega

end Setting4

end CFSG.Quasithin.H13.A6
