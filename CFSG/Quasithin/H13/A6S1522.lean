module

public import CFSG.Quasithin.H13.A6S1514Core
public import CFSG.Quasithin.H13.A5S1522
public import CFSG.Quasithin.Background.G2A5CoreWrap
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A6S1512

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

theorem K4L_inter_conj : ∀ σ : Perm (Fin 6), σ 5 = 5 → σ 4 ≠ 4 → ∀ k ∈ K4L, k ≠ 1 →
    σ * k * σ⁻¹ ∉ K4L := by
  decide +kernel

theorem s3401_facts : (swap (3 : Fin 6) 4 * swap 0 1 : Perm (Fin 6)) 5 = 5 ∧
    Perm.sign (swap (3 : Fin 6) 4 * swap 0 1 : Perm (Fin 6)) = 1 ∧
    (swap (3 : Fin 6) 4 * swap 0 1 : Perm (Fin 6)) 4 ≠ 4 := by
  decide

theorem c012_ne_one : (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) ≠ 1 := by
  decide

@[expose] def Input13521Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) →
    (¬ IsHatA6 L → ∀ H' ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H') →
      ¬ H' ≤ Subgroup.normalizer (S.L1 : Set G)) →
    ∀ H ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H) →
      ⁅conjClosure S.V3 H, S.L1⁆ ⊔ fsuV1 T V = conjClosure S.V3 H

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_L5_not_normalizer_V1 (hhat : ¬ IsHatA6 L) :
    ∃ x ∈ S.L5, x ∉ Subgroup.normalizer (fsuV1 T V : Set G) := by
  obtain ⟨h5, hs, h4⟩ := s3401_facts
  obtain ⟨x, hxL5, hρx⟩ := S.exists_L5_rho hhat h5 hs
  refine ⟨(x : G), hxL5, fun hxN => h4 ?_⟩
  have hfix := S.fix_e0123 x (S.conj_z_of_normalizes hxN)
  rw [hρx] at hfix
  exact fix4_of_e0123 _ hfix h5

theorem almostSpecialA5Core_L5 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hhat : ¬ IsHatA6 L) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
    (hle : conjClosure S.V3 H ≤ S.L1) :
    AlmostSpecialA5Core S.V3 (fsuV1 T V) S.L5 S.T5 H := by
  have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
    have := S.card_V1
    rw [h, Subgroup.card_bot] at this
    omega
  exact ⟨⟨hV1, S.V1_le_V2.trans S.V2_le_V3, S.oTwoUpper_L5, S.V3_le_V.trans S.V_le_T5,
    S.T5_le_NV1, S.T5_le_normalizer_L5, S.isSylowTwoOf_T5 hhat, S.lOne_T5_le_H hH⟩,
    S.g22_T5 hNS h13315 h1356two hH hle, S.isA5ModuleFor_L5 hhat, S.card_V1,
    S.V3_eq_commutator_L5 hhat, S.not_UH_le_pCoreOf_L5T5 hhat hna⟩

theorem sq_eq_one_of_mem_S2_six (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hle : conjClosure S.V3 H ≤ S.L1) {x : G}
    (hx : x ∈ S.L5) (hxN : x ∉ Subgroup.normalizer (fsuV1 T V : Set G)) {y : G}
    (hy : y ∈ V ⊔ (conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) x)) : y ^ 2 = 1 := by
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.L5_le_NV hx
  have hzx : x * S.z * x⁻¹ = S.z → False := by
    intro hxz
    apply hxN
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc x * S.z = x * S.z * x⁻¹ * x := by group
      _ = S.z * x := by rw [hxz]
  have h5 : S.frame.ρ ⟨x, hxV⟩ 5 = 5 := (S.rho_L5 (x := ⟨x, hxV⟩) hx).1
  have h4 : S.frame.ρ ⟨x, hxV⟩ 4 ≠ 4 := by
    intro h4
    apply hzx
    refine (S.conj_eq_iff ⟨x, hxV⟩ ⟨S.z, S.z_mem_V⟩).2 ?_
    rw [S.psi_z]
    exact Subtype.ext (fix_e0123_of _ h4 h5)
  have hK := (S.lemma13_5_14_two hNS h1356two h13315 hH hle hna).1
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.L_le (S.L1_le.trans inf_le_left (hle hu))
  have hcent : ∀ w ∈ conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) x,
      w ∈ Subgroup.centralizer (V : Set G) := by
    intro w hw
    obtain ⟨hwU, hwg⟩ := Subgroup.mem_inf.mp hw
    rw [mem_rconj] at hwg
    have h1 := hK w hwU
    have h2 := hK _ hwg
    have e : S.frame.ρ ⟨x * w * x⁻¹, hUN _ hwg⟩ =
        S.frame.ρ ⟨x, hxV⟩ * S.frame.ρ ⟨w, hUN w hwU⟩ * (S.frame.ρ ⟨x, hxV⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at h2
    refine S.mem_centralizer_of_rho ⟨w, hUN w hwU⟩ rfl ?_
    by_contra hne
    exact K4L_inter_conj _ h5 h4 _ h1 hne h2
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hsq : ∀ w ∈ conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) x, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨hwU, hwg⟩ := Subgroup.mem_inf.mp hw
    rw [mem_rconj] at hwg
    have h1 := S.mem_V1_iff.mp (hF.sq_mem_conjClosure w hwU)
    have h2 := S.mem_V1_iff.mp (hF.sq_mem_conjClosure _ hwg)
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      have e : (x * w * x⁻¹) ^ 2 = x * w ^ 2 * x⁻¹ := by rw [pow_two, pow_two]; group
      rw [e, h1] at h2
      rcases h2 with h2 | h2
      · apply S.z_ne_one
        have : x⁻¹ * (x * S.z * x⁻¹) * x = S.z := by group
        rw [h2] at this
        simpa using this.symm
      · exact hzx h2
  have hle' : conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) x ≤
      Subgroup.normalizer (V : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (hcent w hw)
  have hy' : y ∈ (V : Set G) *
      ((conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) x : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V _ hle']
    exact hy
  obtain ⟨v, hv, w, hw, rfl⟩ := Set.mem_mul.mp hy'
  have hvw : v * w = w * v := Subgroup.mem_centralizer_iff.mp (hcent w hw) v hv
  have hv2 : v ^ 2 = 1 := S.elemAbelian_V.2 v hv
  calc (v * w) ^ 2 = v ^ 2 * w ^ 2 := by
        rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc w, ← hvw, mul_assoc, mul_assoc]
    _ = 1 := by rw [hv2, hsq w hw, mul_one]

theorem sq_eq_one_of_comm_L1 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hhat : ¬ IsHatA6 L) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
    (hU : ⁅conjClosure S.V3 H, S.L1⁆ ⊔ fsuV1 T V = conjClosure S.V3 H) {c : G} (hc : c ∈ S.L1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {u : G} (hu : u ∈ conjClosure S.V3 H) (huc : u * c = c * u) :
    u ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := (S.lemma13_5_14_one hNS h1356two h13315 hH hU).2
  have hyp := S.almostSpecialA5Core_L5 hNS h13315 h1356two hhat hH hna hle
  obtain ⟨x, hx, hxN⟩ := S.exists_L5_not_normalizer_V1 hhat
  obtain ⟨⟨s, hs⟩, -⟩ := hyp.G24_six' rfl hx hxN rfl rfl rfl
  have hI := hyp.G24_two hx hxN
  have hcI : c ∈ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) x := by
    rw [hI]
    exact Subgroup.mem_sup_left (S.L1_le_L5 hc)
  have huI : u ∈ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) x := Subgroup.mem_sup_left hu
  have hcS : c ∉ pCoreOf 2 (conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) x) := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 _ ⟨_, h⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    apply hc1
    have h1 : orderOf c ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hk')
    rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    exact h1
  obtain ⟨k, hk⟩ := S.isPGroup_T5 ⟨u, hyp.g22.three.1 hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hS2 := A5.mem_of_comm_of_isSum hs (c := ⟨c, hcI⟩) (x := ⟨u, huI⟩) (Subtype.ext hc3) hcS
    (k := k) (Subtype.ext hk') (Subtype.ext huc.symm)
  rw [S.conjClosure_V1_L5 hhat] at hS2
  exact S.sq_eq_one_of_mem_S2_six hNS h13315 h1356two hH hna hle hx hxN hS2

theorem exists_L1_order_three : ∃ c ∈ S.L1, c ^ 3 = 1 ∧ c ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hs, h4, h5, h3⟩, -⟩ := three_cycles
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three hs h4 h5 h3
  have h3o : orderOf (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) = 3 :=
    orderOf_eq_prime h3 c012_ne_one
  have hdvd : 3 ∣ orderOf g := by
    rw [← h3o, ← hg]
    exact orderOf_map_dvd _ _
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < orderOf g := orderOf_pos g
  refine ⟨((g ^ m : ↥(Subgroup.normalizer (V : Set G))) : G), ?_, ?_, ?_⟩
  · simpa using S.L1.pow_mem hgL1 m
  · have h1 : (g ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
    simpa using congrArg Subtype.val h1
  · intro h1
    have h1' : g ^ m = 1 := Subtype.ext (by simpa using h1)
    have hm0 : 0 < m := by omega
    have := orderOf_le_of_pow_eq_one hm0 h1'
    omega

theorem exists_lside (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hhat : ¬ IsHatA6 L) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
    (hU : ⁅conjClosure S.V3 H, S.L1⁆ ⊔ fsuV1 T V = conjClosure S.V3 H) :
    ∃ c ∈ S.L1, c ^ 3 = 1 ∧ c ≠ 1 ∧ ∀ u ∈ conjClosure S.V3 H, u * c = c * u → u ^ 2 = 1 := by
  obtain ⟨c, hc, hc3, hc1⟩ := S.exists_L1_order_three
  exact ⟨c, hc, hc3, hc1, fun u hu huc =>
    S.sq_eq_one_of_comm_L1 hNS h13315 h1356two hhat hH hna hU hc hc3 hc1 hu huc⟩

end Setting4

theorem input13518Six_of_13521
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h38 : A38ForSQTK)
    (hF : A5.Facts1321) (hR : A5.FactRankRows1321) (hA7 : A5.FactA7Grp1321)
    (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321) (h6 : Input13521Six) :
    Input13518Six := by
  intro G _ _ T L V S hNS hhat hna
  by_contra hcon
  push Not at hcon
  have hG1 := S.G1_mem_Hz_of_nonabelian hna
  obtain ⟨c, hcL1, hc3, hc1, hsq⟩ := S.exists_lside hNS h13315 h1356two hhat hG1 hna
    (h6 G T L V S hNS hna (fun _ => hcon) S.G1 hG1 hna)
  have hcQ : c ∉ pCoreOf 2 S.G1 := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.G1 ⟨c, h⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf c ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hk')
    rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    exact hc1 h1
  obtain ⟨u, hu, huc, hu2⟩ := (S.toA5Sit hNS h13315 h1356two hG1 hna).exists_comm_sq_ne_one
    VolI.stmtF956i h38 (S.toA5SitY hNS h13315 h1356two hG1 hna hhat)
    (S.lemma13_5_19_two_L1 hNS h13315 h1356two hcon hG1)
    (fun _ hl => S.cube_mem_pCoreOf_L1 hhat hl) hF hR hA7 hL3 hO A5.factQuadRows1321 hcL1 hc3
    hcQ
  exact hu2 (hsq u hu huc)

theorem stmt13_5_12_six_of_13521
    (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hobl : Obl13_5_14Six)
    (hctk : Input13515CTK) (hU43 : StmtU43Type) (h38 : A38ForSQTK) (hF : A5.Facts1321)
    (hR : A5.FactRankRows1321) (hA7 : A5.FactA7Grp1321) (hL3 : A5.FactL3Grp1321)
    (hO : A5.FactOutRows1321) (h4 : Input13521Four) (h6 : Input13521Six) : Stmt13_5_12_six :=
  stmt13_5_12_six_of_inputs h1332 h13316 h1341 h13315 h1356two hobl hctk hU43 h4
    (input13518Six_of_13521 h13315 h1356two h38 hF hR hA7 hL3 hO h6)

end CFSG.Quasithin.H13.A6
