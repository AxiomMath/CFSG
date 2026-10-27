module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

variable {I : Type} [Group I] [Finite I]

omit [Finite I] in
theorem normal_perfectCore_top : (perfectCore (⊤ : Subgroup I)).Normal := by
  have h := normalizer_le_normalizer_perfectCore (⊤ : Subgroup I)
  refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
  intro g _
  exact h (by rw [Subgroup.mem_normalizer_iff]; intro y; simp)

theorem mem_perfectCore_of_map_pPrimeCore {x : I} (hx : x ^ 3 = 1)
    (h : (QuotientGroup.mk' (CFSG.pPrimeCore 3 I)) x ∈
      perfectCore (⊤ : Subgroup (I ⧸ CFSG.pPrimeCore 3 I))) :
    x ∈ perfectCore (⊤ : Subgroup I) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := CFSG.pPrimeCore 3 I with hX
  set π := QuotientGroup.mk' X with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective X
  have hmap := map_perfectCore π (⊤ : Subgroup I)
  rw [Subgroup.map_top_of_surjective π hπs] at hmap
  rw [← hmap] at h
  obtain ⟨y, hy, hyx⟩ := h
  have hN := normal_perfectCore_top (I := I)
  set N := perfectCore (⊤ : Subgroup I) with hNdef
  have hu : y⁻¹ * x ∈ X := by
    have : π y = π x := hyx
    exact (QuotientGroup.eq.mp this)
  let ρ : I →* I ⧸ N := QuotientGroup.mk' N
  have h1 : ρ x = ρ (y⁻¹ * x) := by
    have : ρ y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [map_mul, map_inv, this, inv_one, one_mul]
  have h2 : orderOf (ρ x) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h3 : orderOf (ρ x) ∣ Nat.card X := by
    rw [h1]
    refine (orderOf_map_dvd ρ (y⁻¹ * x)).trans ?_
    have := orderOf_dvd_natCard (⟨y⁻¹ * x, hu⟩ : X)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime 3 (Nat.card X) := CFSG.pPrimeCore_coprime_card
  have h4 : orderOf (ρ x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3 |> fun h => by omega
  have : ρ x = 1 := orderOf_eq_one_iff.mp h4
  exact (QuotientGroup.eq_one_iff x).mp this



omit [Finite I] in
theorem commutator_eq_self_of_perfect' {K : Subgroup I} (hK : Group.IsPerfect K) : ⁅K, K⁆ = K := by
  have h := congrArg (Subgroup.map K.subtype) hK.commutator_eq_top
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

end Y15111

end CFSG.Quasithin
