module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontQField
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontQKlein
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontQInvol
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontQComm
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

variable {G : Type} [Group G] [Finite G]

private theorem qTwoFrontQ_core_centralizes {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (h4 : 4 ≤ n) {ψ : Su K 2 f n →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n))
    {Bs : Subgroup G} (hacts : GGActsUnitarily (p := 2) (f := f) ψ Bs)
    {H : Subgroup G} (hH : H ≤ Bs) {s : Su K 2 f n} {t : G} (hst : ψ s = t)
    (ht2 : t * t = 1) (htC : t ∈ Subgroup.centralizer (H : Set G)) {k : ℕ} {u v : Su K 2 f n}
    (hu : u = s ^ k)
    (hcomm : ∀ g : Matrix (Fin n) (Fin n) K,
        g * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g →
        g * ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g) :
    ψ v ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨g, -, hind⟩ := hacts b (hH hb)
  obtain ⟨y, hy, hby⟩ := hind s
  have hs2 : ψ s * ψ s = 1 := by rw [hst, ht2]
  have hbt : b * t = t * b := Subgroup.mem_centralizer_iff.mp htC b hb
  have hbconj : b * t * b⁻¹ = t := by rw [hbt, mul_assoc, mul_inv_cancel, mul_one]
  have hψ : ψ y = ψ s := by rw [← hby, hst, hbconj]
  have hgs : Commute g (s : GL (Fin n) K) := qTwoFrontQ_commute hK hf h4 hker hs2 hy hψ
  have hgu : Commute g (u : GL (Fin n) K) := by
    have hcoe : (u : GL (Fin n) K) = (s : GL (Fin n) K) ^ k := by
      rw [hu]
      exact map_pow (Subgroup.subtype (SUid (unitaryInvolution K 2 f) n)) s k
    rw [hcoe]
    exact hgs.pow_right k
  have hmat_u : (g : Matrix (Fin n) (Fin n) K) *
        ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) := by
    simpa only [Units.val_mul] using
      congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hgu.eq
  have hgv : g * (v : GL (Fin n) K) = (v : GL (Fin n) K) * g := by
    apply Units.ext
    simpa only [Units.val_mul] using hcomm (g : Matrix (Fin n) (Fin n) K) hmat_u
  obtain ⟨y', hy', hby'⟩ := hind v
  have hy'v : y' = v :=
    Subtype.ext (by rw [hy', hgv, mul_assoc, mul_inv_cancel, mul_one])
  have hbyv : b * ψ v * b⁻¹ = ψ v := by rw [hby', hy'v]
  have hthis := congrArg (fun z : G => z * b) hbyv
  simpa [mul_assoc] using hthis

theorem qTwoFrontQ_core {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (h4 : 4 ≤ n) {ψ : Su K 2 f n →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {Bs L : Subgroup G} (hrange : ψ.range = L)
    (hacts : GGActsUnitarily (p := 2) (f := f) ψ Bs) {H : Subgroup G} (hH : H ≤ Bs)
    (hS : Nat.card (ggOTwoPrime (L ⊓ Subgroup.centralizer (H : Set G))) = 6) : False := by
  classical
  set S : Subgroup G := ggOTwoPrime (L ⊓ Subgroup.centralizer (H : Set G)) with hSdef
  have hS' : Nat.card S = 6 := by rw [hSdef]; exact hS
  have h2dvd : 2 ∣ Nat.card S := by rw [hS']; norm_num
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 h2dvd
  set t : G := (t₀ : G) with htdef
  have ht_order : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe, ht₀]
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht_order]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht_order
    omega
  have htS : t ∈ S := by rw [htdef]; exact t₀.2
  have htSexpr : t ∈ ggOTwoPrime (L ⊓ Subgroup.centralizer (H : Set G)) := by
    rw [← hSdef]; exact htS
  have htL : t ∈ L := (ggOTwoPrime_le _ htSexpr).1
  have htC : t ∈ Subgroup.centralizer (H : Set G) := (ggOTwoPrime_le _ htSexpr).2
  have ht_range : t ∈ ψ.range := by rw [hrange]; exact htL
  obtain ⟨s, hs_eq⟩ := MonoidHom.mem_range.mp ht_range
  have hs2 : ψ s * ψ s = 1 := by rw [hs_eq, ht2]
  obtain ⟨k, hk_odd, hk_u⟩ := qTwoFrontQ_odd_power hK hf h4 hker hs2
  set u : Su K 2 f n := s ^ k with hudef
  have hu2 : u * u = 1 := by rw [hudef]; exact hk_u
  have ht_pow : t ^ k = t := by
    obtain ⟨j, rfl⟩ := hk_odd
    rw [pow_succ, pow_mul, pow_two, ht2, one_pow, one_mul]
  have hu_psi : ψ u = t := by rw [hudef, map_pow, hs_eq, ht_pow]
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, map_one] at hu_psi
    exact ht1 hu_psi.symm
  obtain ⟨ω, hω, hω0, hω1⟩ := qTwoFrontQ_exists_fixed hK hf
  obtain ⟨v, hv2, huv, hcomm, hv_non, huv_non⟩ :=
    qTwoFrontQ_second_involution hK hω hω0 hω1 hu2 hu1
  have hBcent : ψ v ∈ Subgroup.centralizer (H : Set G) :=
    qTwoFrontQ_core_centralizes hK hf h4 hker hacts hH hs_eq ht2 htC hudef hcomm
  have hv2psi : ψ v * ψ v = 1 := by rw [← map_mul, hv2, map_one]
  have hB_range : ψ v ∈ L := by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨v, rfl⟩
  have hB_mem : ψ v ∈ S := by
    rw [hSdef]
    refine Subgroup.subset_closure ⟨⟨hB_range, hBcent⟩, 1, ?_⟩
    rw [pow_one, pow_two, hv2psi]
  have hA_mem : ψ u ∈ S := by rw [hu_psi]; exact htS
  have hA2 : ψ u * ψ u = 1 := by rw [hu_psi, ht2]
  have hAB : ψ u * ψ v = ψ v * ψ u := by rw [← map_mul, ← map_mul, huv]
  have hA1 : ψ u ≠ 1 := by rw [hu_psi]; exact ht1
  have hB1 : ψ v ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := qTwoFrontQ_ker_scalar hK hf h4 hker h
    exact hv_non c hc
  have hne : ψ u ≠ ψ v := by
    intro h
    have huv1 : ψ (u * v) = 1 := by rw [map_mul, h, hv2psi]
    obtain ⟨c, hc⟩ := qTwoFrontQ_ker_scalar hK hf h4 hker huv1
    exact huv_non c hc
  exact qTwoFrontQ_no_klein hS' hA_mem hB_mem hA2 hv2psi hAB hA1 hB1 hne

end CFSG.StandardType.QTwo

end
