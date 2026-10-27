module

public import CFSG.Quasithin.EmptyFaithful.A38c5Hom
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace CFSG.Quasithin.A38c5

section Aut

variable {G : Type} [Group G] [Finite G] {U : Subgroup G} (hV : IsElemAbelian 2 U)

theorem isSylowTwoOf_autI {S I : Subgroup G} (hS : IsSylowTwoOf S I)
    (hIN : I ≤ Subgroup.normalizer (U : Set G))
    (hC : I ⊓ Subgroup.centralizer (U : Set G) ≤ S) :
    IsSylowTwoOf (autI hV S) (autI hV I) := by
  refine ⟨autI_mono hV hS.1, isPGroup_autOn hS.2.1 (hS.1.trans hIN), ?_⟩
  have h := relIndex_autOn hS.1 hIN hC
  have h2 := hS.2.2
  change ¬ 2 ∣ (autOn S U).relIndex (autOn I U)
  rw [h]
  exact h2

theorem autI_pCoreOf {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (U : Set G))
    (hC : IsPGroup 2 ↥(H ⊓ Subgroup.centralizer (U : Set G))) :
    autI hV (pCoreOf 2 H) = pCoreOf 2 (autI hV H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (IntMod U hV)) := MulEquiv.finite_left
  have hPH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf 2 (autI_mono hV hPH) ?_
      (isPGroup_autOn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) (hPH.trans hHN))
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨p, hp, hpx⟩ := (mem_autI hV).1 hx
    obtain ⟨h, hh, hgh⟩ := (mem_autI hV).1 g.2
    have hh' : (h : G) * p * (h : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) (p : G)).1 hp
    have key : convI hV (h * p * h⁻¹) =
        (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hgh, hpx]
    show (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ ∈ autI hV (pCoreOf 2 H)
    rw [← key]
    exact convI_mem_autI hV hh' (h * p * h⁻¹).2
  · set Q := pCoreOf 2 (autI hV H) with hQ
    have hQH : Q ≤ autI hV H := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    set Qt := preI hV H hHN Q with hQt
    have hQtH : Qt ≤ H := preI_le hV
    have hQtn : (Qt.subgroupOf H).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxH, hxQ⟩ := (mem_preI hV).1 hx
      refine (mem_preI hV).2 ⟨(g * x * g⁻¹).2, ?_⟩
      show convHom hV H hHN (g * x * g⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      have hgmem : convHom hV H hHN g ∈ autI hV H := by
        rw [← range_convHom hV H hHN]
        exact ⟨g, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (autI hV H) hgmem)
          (convHom hV H hHN x)).1 hxQ
    have hQt2 : IsPGroup 2 ↥Qt := by
      have hcard : Nat.card Qt = Nat.card Q * Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)) :=
        card_preI hV hQH
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autI hV H))
      obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hC
      exact IsPGroup.of_card (n := a + b) (by rw [hcard, ha, hb, pow_add])
    have hle : Qt ≤ pCoreOf 2 H := CFSG.LieType.BorelTits.le_pCoreOf 2 hQtH hQtn hQt2
    calc Q = autI hV Qt := (autI_preI hV hQH).symm
      _ ≤ autI hV (pCoreOf 2 H) := autI_mono hV hle

theorem autI_oPrimeResidualOf {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (U : Set G)) :
    autI hV (oPrimeResidualOf 3 K) = oPrimeResidualOf 3 (autI hV K) := by
  set N := Subgroup.normalizer (U : Set G) with hN
  have hOK : oPrimeResidualOf 3 K ≤ K := by
    unfold oPrimeResidualOf
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have h1 : (oPrimeResidualOf 3 K).subgroupOf N = oPrimeResidualOf 3 (K.subgroupOf N) := by
    have := map_oPrimeResidualOf N.subtype 3 Nat.prime_three (K.subgroupOf N)
    rw [Subgroup.map_subgroupOf_eq_of_le hK] at this
    rw [← this]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  rw [autI_eq_map_convHom hV le_rfl (hOK.trans hK), autI_eq_map_convHom hV le_rfl hK, h1,
    map_oPrimeResidualOf _ 3 Nat.prime_three]

omit [Finite G] in
theorem autI_inf_eq {S A P : Subgroup G} (hAS : A ≤ S) (hPS : P ≤ S)
    (hSC : S ⊓ Subgroup.centralizer (U : Set G) ≤ P) :
    autI hV (A ⊓ P) = autI hV A ⊓ autI hV P := by
  apply le_antisymm
  · exact le_inf (autI_mono hV inf_le_left) (autI_mono hV inf_le_right)
  · intro φ hφ
    obtain ⟨hφA, hφP⟩ := hφ
    obtain ⟨a, haA, rfl⟩ := (mem_autI hV).1 hφA
    obtain ⟨p, hpP, hp⟩ := (mem_autI hV).1 hφP
    have hc : (a : G) * (p : G)⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      have : convI hV (a * p⁻¹) = 1 := by rw [map_mul, map_inv, hp, mul_inv_cancel]
      exact (convI_eq_one_iff hV _).1 this
    have haP : (a : G) ∈ P := by
      have h1 : (a : G) * (p : G)⁻¹ ∈ P :=
        hSC (show (a : G) * (p : G)⁻¹ ∈ S ⊓ Subgroup.centralizer (U : Set G) from
          ⟨S.mul_mem (hAS haA) (S.inv_mem (hPS hpP)), hc⟩)
      have := P.mul_mem h1 hpP
      simpa using this
    exact convI_mem_autI hV (K := A ⊓ P) ⟨haA, haP⟩ a.2

theorem rk_autI_add {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (U : Set G)) :
    rk ↥(autI hV A) + rk ↥(A ⊓ Subgroup.centralizer (U : Set G)) = rk ↥A := by
  have h := card_autI_mul_card_inf hV hA
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h]

theorem rkIdx_fixV_autI {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (U : Set G)) :
    rkIdx (fixV (autI hV A)) = rk ↥U - rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) := by
  have h1 := rk_add_rkIdx (fixV (autI hV A))
  have h2 : rk ↥(fixV (autI hV A)) = rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) := by
    unfold rk
    rw [card_fixV_autI hV hA]
  have h3 : rk (IntMod U hV) = rk ↥U := rfl
  omega

omit [Finite G] in
theorem autI_le_normalizer {S K : Subgroup G} (hSK : S ≤ Subgroup.normalizer (K : Set G)) :
    autI hV S ≤ Subgroup.normalizer ((autI hV K : Subgroup (MulAut (IntMod U hV))) :
      Set (MulAut (IntMod U hV))) := by
  intro φ hφ
  obtain ⟨s, hs, rfl⟩ := (mem_autI hV).1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨k, hk, rfl⟩ := (mem_autI hV).1 hψ
    have h1 : (s : G) * k * (s : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hSK hs) k).1 hk
    have h2 := convI_mem_autI hV h1 (s * k * s⁻¹).2
    rwa [show (⟨(s : G) * k * (s : G)⁻¹, (s * k * s⁻¹).2⟩ : Subgroup.normalizer (U : Set G)) =
      s * k * s⁻¹ from rfl, map_mul, map_mul, map_inv] at h2
  · intro hψ
    obtain ⟨k, hk, hkψ⟩ := (mem_autI hV).1 hψ
    have h1 : (s : G)⁻¹ * k * (s : G) ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hSK (S.inv_mem hs)) k).1 hk
      simpa using this
    have h2 := convI_mem_autI hV h1 (s⁻¹ * k * s).2
    have h3 : convI hV (s⁻¹ * k * s) = ψ := by
      rw [map_mul, map_mul, map_inv, hkψ]
      group
    rwa [show (⟨(s : G)⁻¹ * k * (s : G), (s⁻¹ * k * s).2⟩ : Subgroup.normalizer (U : Set G)) =
      s⁻¹ * k * s from rfl, h3] at h2

theorem rAV_autI_lt_one {X A : Subgroup G} (hA : IsA2 (autI hV X) (autI hV A))
    (hAN : A ≤ Subgroup.normalizer (U : Set G))
    (h : rk ↥U - rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) <
      rk ↥A - rk ↥(A ⊓ Subgroup.centralizer (U : Set G))) : rAV (autI hV A) < 1 := by
  have hr : (0 : ℚ) < (rk ↥(autI hV A) : ℚ) := by exact_mod_cast hA.rk_pos
  unfold rAV
  rw [div_lt_one hr, rkIdx_fixV_autI hV hAN]
  have := rk_autI_add hV hAN
  exact_mod_cast (by omega : rk ↥U - rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) <
    rk ↥(autI hV A))

end Aut
end CFSG.Quasithin.A38c5
