module

public import CFSG.Quasithin.H13.A6S1372L76Of3
public import CFSG.Quasithin.H13.A6S1372L76Oe2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76Of

theorem inv_c012 : (swap (0 : Fin 6) 1 * swap 4 5) * (swap 0 1 * swap 1 2) *
    (swap 0 1 * swap 4 5)⁻¹ * (swap 0 1 * swap 1 2) = 1 := by
  decide

open CFSG.SectionRank.ClassicalEven in
theorem two_le_pRank_statedSL3 {F : Type} [Field F] [Finite F] {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rwa [Nat.card_units])
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hr.one_lt.ne hζ
  let x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    ⟨torusDiag (torusVec ζ 0 2), torusDiag_mem_SL (prod_torusVec ζ _ _)⟩
  let y : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    ⟨torusDiag (torusVec ζ 1 2), torusDiag_mem_SL (prod_torusVec ζ _ _)⟩
  have hpow : ∀ n : ℕ, ∀ j : Fin 3, torusDiag (torusVec ζ j 2) ^ n =
      torusDiag (torusVec (ζ ^ n) j 2) := fun n j => by rw [← map_pow, torusVec_pow]
  have hent {d d' : Fin 3 → Fˣ} (h : torusDiag d = torusDiag d') (i : Fin 3) : d i = d' i :=
    congrFun (torusDiag_injective h) i
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens (x := x) (y := y)
    ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, hpow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
    rfl
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, hpow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
    rfl
  · exact Subtype.ext ((Commute.all (torusVec ζ 0 2) (torusVec ζ 1 2)).map torusDiag).eq
  · intro h
    have h1 : (torusDiag (torusVec ζ (0 : Fin 3) 2) : GL (Fin 3) F) = torusDiag 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := hent h1 0
    rw [torusVec_apply_left ζ (by decide)] at h2
    exact hζ1 h2
  · intro n h
    have h1 : (torusDiag (torusVec (ζ ^ n) (0 : Fin 3) 2) : GL (Fin 3) F) =
        torusDiag (torusVec ζ 1 2) := by
      rw [← hpow n 0]
      exact congrArg Subtype.val h
    have h2 := hent h1 1
    rw [torusVec_apply_of_ne _ (by decide) (by decide), torusVec_apply_left ζ (by decide)] at h2
    exact hζ1 h2.symm

end A6L76Of

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem plusData_X1375 : S14.PlusData S S.X1375 := by
  by_cases hhat : IsHatA6 L
  · rw [S.X1375_of_hat hhat]
    exact S14.plusData_l1plus S (S.hatL1Plus hhat)
  · rw [S.X1375_of_not_hat hhat]
    exact S14.plusData_L1 S hhat

theorem exists_inverting {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgX : (g : G) ∈ S.X1375) (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    ∃ t ∈ T, ∃ j : ℕ, (t * (g : G) * t⁻¹ * g) ^ (2 ^ j) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, ht⟩ := S.frame.DA_T _ gens_DA.2.2.1 gens_DA.2.2.2
  have P := S.plusData_X1375
  have hrρ : S.frame.ρ (t * g * t⁻¹ * g) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, ht, hg]
    exact A6L76Of.inv_c012
  have hrC := (S.rho_eq_one_iff (t * g * t⁻¹ * g)).1 hrρ
  have h1 : (t : G) * g * (t : G)⁻¹ ∈ S.X1375 :=
    (Subgroup.mem_normalizer_iff.mp (P.T_le htT) g).mp hgX
  have hrX : ((t * g * t⁻¹ * g : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.X1375 :=
    S.X1375.mul_mem h1 hgX
  have hrO := P.cent ⟨hrX, hrC⟩
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hrO⟩
  refine ⟨t, htT, j, ?_⟩
  have h2 := congrArg Subtype.val hj
  simpa using h2

theorem normal_of_natSL3 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h38 : A38ForSQTK) {H : Subgroup G}
    (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G}
    (hK : K ∈ cComp H) {F : Type} [Field F] [Finite F] {n : ℕ} (hn3 : 3 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    {U Z : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hR : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Realizes
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) U Z) :
    ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨eK⟩ := S.exists_quotEquiv_of_realizes hNS h13315 h1356two hH hK
    (FFModel.nat_faithful _) hR
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  have hK₀ : K.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK
  obtain ⟨r, hr, hrd, -⟩ := A3Facts.exists_prime_dvd_two_pow_sub_one hn3
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hrank : 1 < CFSG.Open.pRank r (K.subgroupOf H) := by
    rw [Vol2.Ch11.SecA.pRank_subgroupOf_eq hKH hr hr2]
    have : Finite (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Gam :=
      Finite.of_equiv _ eK.toEquiv
    have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := r) hr.one_lt eK
    have h2 := A6L76Of.two_le_pRank_statedSL3 (F := F) hr (by rw [hF]; exact hrd)
    have h3 : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) := by
      rw [h1]
      exact h2
    omega
  have hKn : (K.subgroupOf H).Normal := A318.normal_of_pRank_gt_one hSQ
    (h38 _ (SQTKHyp.of_sqtkGroup ↥H hSQ)) hK₀ hr hr2 hrank
  intro h hh k hk
  have := Subgroup.mem_subgroupOf.1 (hKn.conj_mem ⟨k, hKH hk⟩ hk ⟨h, hh⟩)
  simpa using this

theorem false_of_natSL3_odd (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  obtain ⟨g, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, rfl, -, -, haY, -, hP2, hPodd, hPv, hPa, ha2, hv⟩ :=
    S.exists_odd_config_of hH hK rfl h139 h37 h38 h13315 hgX hg
  obtain ⟨t, htT, j, hj⟩ := S.exists_inverting hgX hg
  have hHK := S.normal_of_natSL3 hNS h13315 h1356two h38 hH hK hn3 hF ⟨π, hπ⟩
  have htH : t ∈ H := hTH htT
  refine A6L76Of.false_of_natSL3 (S.isPerfect_tilde hH hK) hn hn3 hF hπ haY hP2 hPodd hPv
    hPa ha2 hv (t := A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
      ⟨t, htH⟩) (fun y hy => ?_) (j := j) ?_
  ·
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) hKH).1 hy
    refine (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
      hKH).2 ⟨⟨t, htH⟩ * f * ⟨t, htH⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hHK t htH f hfK
  ·
    have h1 : ((⟨t, htH⟩ : ↥H) * ⟨(g : G), X1375_le_H hH hgX⟩ * (⟨t, htH⟩ : ↥H)⁻¹ *
        ⟨(g : G), X1375_le_H hH hgX⟩) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h1, map_one]

end Setting4

theorem lem1376OddNCBig_of (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) :
    Lem1376OddNCBig := by
  intro G _ _ T L V S hNS _ H hH _ _ K hK hmod _
  obtain ⟨n, hn, hn3, hSL⟩ := hmod
  exact (S.false_of_natSL3_odd h139 h37 h38 h13315 h1356two hNS hH hK hn hn3 hSL).elim

end CFSG.Quasithin.H13.A6
