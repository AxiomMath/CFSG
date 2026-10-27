module

public import CFSG.Quasithin.H13.A6S13821m
public import CFSG.Quasithin.H13.A6S13821zh

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace L32HatStep

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_pi_sl3 {H K T : Subgroup G} (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hTsylH : IsSylowTwoOf T H)
    (hP : IsPSL 3 2 1 (L32A.cStar K)) :
    ∃ π : ↥K →* SL3.S, Function.Surjective π ∧
      (∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K) ∧
      (T.subgroupOf K).map π = SL3.P0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  set π₀ : ↥K →* SL3.S := φ.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTsylH hKH hKn
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hTsylH.2.1.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := Subgroup.inf_subgroupOf_right T K ▸ hTsyl.2.2
  obtain ⟨h, hhD⟩ := L32A.C.exists_conj_map_eq_of_sylow π₀ hπ₀ hS2 hSi SL3.P0_sylow.1
    SL3.P0_sylow.2
  set π : ↥K →* SL3.S := (MulAut.conj h⁻¹).toMonoidHom.comp π₀ with hπdef
  have hπ : Function.Surjective π := (MulAut.conj h⁻¹).surjective.comp hπ₀
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]
  have hD : (T.subgroupOf K).map π = SL3.P0 := by
    rw [← hhD, Subgroup.map_map]
  exact ⟨π, hπ, hker, hD⟩

theorem image_le_oTwoUpper {K : Subgroup G} {f : ↥K →* SL3.S} {Z : Subgroup G} (hZK : Z ≤ K)
    (hZ : Z ≤ oTwoUpper Z) : (Z.subgroupOf K).map f ≤ oTwoUpper ((Z.subgroupOf K).map f) := by
  rw [Subgroup.map_le_iff_le_comap]
  have hZW : oTwoUpper Z ≤ ((oTwoUpper ((Z.subgroupOf K).map f)).comap f).map K.subtype := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxZ, hxo⟩ := hx
    refine ⟨⟨x, hZK hxZ⟩, ?_, rfl⟩
    show f ⟨x, hZK hxZ⟩ ∈ oTwoUpper ((Z.subgroupOf K).map f)
    unfold oTwoUpper
    refine Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem f ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hxZ
    · have hd := orderOf_map_dvd f (⟨x, hZK hxZ⟩ : ↥K)
      rw [Subgroup.orderOf_mk] at hd
      exact Odd.of_dvd_nat hxo hd
  intro z hz
  obtain ⟨m, hm, hmz⟩ := hZW (hZ (Subgroup.mem_subgroupOf.mp hz))
  have hmz' : m = z := Subtype.ext hmz
  exact hmz' ▸ hm

theorem P0_le_normalizer_image {K T : Subgroup G} {f : ↥K →* SL3.S}
    (hf : (T.subgroupOf K).map f = SL3.P0) {Z : Subgroup G} (hZK : Z ≤ K)
    (hTZ : ∀ t ∈ T, ∀ z ∈ Z, t * z * t⁻¹ ∈ Z) :
    SL3.P0 ≤ Subgroup.normalizer ((((Z.subgroupOf K).map f : Subgroup SL3.S)) : Set SL3.S) := by
  have fwd : ∀ t : ↥K, t ∈ T.subgroupOf K → ∀ w ∈ (Z.subgroupOf K).map f,
      f t * w * (f t)⁻¹ ∈ (Z.subgroupOf K).map f := by
    rintro t ht w ⟨x, hx, rfl⟩
    refine ⟨t * x * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hxZ : (x : G) ∈ Z := Subgroup.mem_subgroupOf.mp hx
    have := hTZ _ htT _ hxZ
    simpa using this
  intro p hp
  rw [← hf] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact fwd t ht w
  · intro hw
    have h := fwd t⁻¹ (Subgroup.inv_mem _ ht) _ hw
    simpa [map_inv, mul_assoc] using h

theorem step21_of_not_le {S : Setting4 G T L V}
    {H K : Subgroup G} (hH : H ∈ S.Hz) (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) (hnot : ¬ S.X13820 ≤ K) :
    ∀ x ∈ S.X13820, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := S.plusData_X13820
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hXH : S.X13820 ≤ H := P.le_L1.trans (le_sup_left.trans hH.1.1)
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  have hX3 : (pCoreOf 2 (oTwoUpper S.X13820)).relIndex (oTwoUpper S.X13820) = 3 := by
    rw [← P.eq]
    exact P.Lp3
  have hc := A6L32.comm_of_not_le hKc hKn hTsylH hP' hX3 (by rw [← P.eq]; exact hXH)
    (by rw [← P.eq]; exact P.T_le) (by rw [← P.eq]; exact hnot)
  intro x hx k hk
  rw [P.eq] at hx
  exact hc x hx k hk

end L32HatStep

end CFSG.Quasithin.H13.A6
