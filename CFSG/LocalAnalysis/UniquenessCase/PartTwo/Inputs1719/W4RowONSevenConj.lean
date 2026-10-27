module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Model
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier
open CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7

private theorem card_centralizer_seven_eq_of_even
    {y : Pv}
    (hy : orderOf y = 7)
    (h2 : 2 ∣ Nat.card (Subgroup.centralizer ({y} : Set Pv))) :
    Nat.card (Subgroup.centralizer ({y} : Set Pv)) = 7 ^ 3 * 4 := by
  rcases card_centralizer_seven_Pv hy with h | h
  · rw [h]
    norm_num
  · rw [h] at h2
    norm_num at h2

private theorem exists_conj_mem_centralizer_on7F_zero
    {y : Pv}
    (hcard : Nat.card (Subgroup.centralizer ({y} : Set Pv)) = 7 ^ 3 * 4) :
    ∃ g : Pv, g⁻¹ * y * g ∈ Subgroup.centralizer (on7F 0 : Set Pv) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set C : Subgroup Pv := Subgroup.centralizer ({y} : Set Pv) with hC
  have hdvd : 7 ^ 3 ∣ Nat.card C := by
    rw [hcard]
    norm_num
  obtain ⟨L, hLcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 7 (n := 3) hdvd
  set K : Subgroup Pv := Subgroup.map C.subtype L with hK
  have hKcard : Nat.card K = 7 ^ 3 := by
    rw [hK, Subgroup.card_subtype, hLcard]
  have hKC : K ≤ C := by
    intro k hk
    rw [hK] at hk
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hk
    exact c.2
  have hKfac : Nat.card K = 7 ^ (Nat.card Pv).factorization 7 := by
    rw [hKcard, factorization_card_Pv_seven]
  let PK : Sylow 7 Pv := Sylow.ofCard K hKfac
  have hPK : (PK : Subgroup Pv) = K := Sylow.coe_ofCard K hKfac
  obtain ⟨P₀, hP₀⟩ := on7F0_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Pv P₀ PK
  have hKconj : K = (on7F 0).map (MulAut.conj g).toMonoidHom := by
    rw [← hPK, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP₀]
    rfl
  refine ⟨g, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hkK : g * f * g⁻¹ ∈ K := by
    rw [hKconj]
    exact Subgroup.mem_map.2 ⟨f, hf, by simp [MulAut.conj_apply]⟩
  have hcent : (g * f * g⁻¹) * y = y * (g * f * g⁻¹) := by
    have h := hKC hkK
    rw [hC] at h
    exact Subgroup.mem_centralizer_singleton_iff.1 h
  have h1 : f * (g⁻¹ * y * g) = g⁻¹ * ((g * f * g⁻¹) * y) * g := by group
  have h2 : (g⁻¹ * y * g) * f = g⁻¹ * (y * (g * f * g⁻¹)) * g := by group
  rw [h1, h2, hcent]

theorem on_exists_conj_pow_on7W_zero
    {y : Pv} (hy7 : y ^ 7 = 1)
    (hy1 : y ≠ 1) {u : Pv} (hu2 : u * u = 1) (hu1 : u ≠ 1) (huy : u * y = y * u) :
    ∃ (g : Pv) (k : ℕ), ¬ 7 ∣ k ∧ y = g * on7W 0 ^ k * g⁻¹ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hy : orderOf y = 7 := orderOf_eq_prime hy7 hy1
  have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have h2dvd : 2 ∣ Nat.card (Subgroup.centralizer ({y} : Set Pv)) := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({y} : Set Pv))
      (Subgroup.mem_centralizer_singleton_iff.2 huy)
    rwa [hu] at h
  have hcard := card_centralizer_seven_eq_of_even hy h2dvd
  obtain ⟨g, hcent⟩ := exists_conj_mem_centralizer_on7F_zero hcard
  set y' : Pv := g⁻¹ * y * g with hy'def
  have hy'cent : y' ∈ Subgroup.centralizer (on7F 0 : Set Pv) := by
    rwa [hy'def]
  have hy'centw : y' ∈ Subgroup.centralizer ({on7W 0} : Set Pv) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hy'cent (on7W 0) (on7_sevenLine 0).mem).symm
  have hy'Z : y' ∈ Subgroup.zpowers (on7W 0) :=
    (on7_sevenLine 0).cent y' hy'centw fun f hf =>
      (Subgroup.mem_centralizer_iff.1 hy'cent f hf).symm
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff y' (on7W 0)).1
    (mem_powers_iff_mem_zpowers.2 hy'Z)
  have hy_eq : y = g * y' * g⁻¹ := by
    rw [hy'def]
    group
  refine ⟨g, k, ?_, ?_⟩
  · intro h7k
    have hwk : on7W 0 ^ k = 1 := by
      obtain ⟨m, rfl⟩ := h7k
      rw [pow_mul, on7W_pow_seven, one_pow]
    have hy'1 : y' = 1 := by rw [← hk, hwk]
    have hy1' : y = 1 := by
      rw [hy_eq, hy'1, mul_one]
      simp
    exact hy1 hy1'
  · rw [hy_eq, hk]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
