module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aC
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Case2a

section Generic

variable {X : Type*} [Group X] [Finite X]

theorem eq_one_of_central_pow {z : X ⧸ CFSG.Open.pCore 2 X}
    (hz : z ∈ Subgroup.center (X ⧸ CFSG.Open.pCore 2 X)) {k : ℕ} (hk : z ^ 2 ^ k = 1) :
    z = 1 := by
  have h2 : IsPGroup 2 (Subgroup.zpowers z) := by
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hWn : ((Subgroup.zpowers z).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 X))).Normal :=
    (Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)).comap _
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.Open.pCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hW2 := h2.comap_of_ker_isPGroup (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) hker
  have hWle := CFSG.LieType.BorelTits.le_pCore 2 hWn hW2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  exact (QuotientGroup.eq_one_iff x).mpr (hWle (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)))

theorem odd_orderOf_of_central {z : X ⧸ CFSG.Open.pCore 2 X}
    (hz : z ∈ Subgroup.center (X ⧸ CFSG.Open.pCore 2 X)) : Odd (orderOf z) := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 2 (by norm_num)
  have h1 : (z ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have h2 : z ^ m = 1 := eq_one_of_central_pow (Subgroup.pow_mem _ hz m) h1
  have h3 : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one h2
  exact Odd.of_dvd_nat (Nat.odd_iff.mpr (by omega)) h3

end Generic

section Cover

variable {G : Type} [Group G] [Finite G] {T M H K : Subgroup G}

theorem Setting.inf_pCore_le (c : Setting T M H K) : pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (c.le_H hk), Subgroup.le_normalizer hk⟩

omit [Finite G] in
theorem mem_pCore_of_mem_pCoreOf {e : ↥K} (h : (e : G) ∈ pCoreOf 2 K) :
    e ∈ CFSG.Open.pCore 2 ↥K := (CFSG.mem_openPCoreOf_iff_open e).mp h

theorem Setting.exists_cover (c : Setting T M H K) :
    ∃ π : OTwoQuot K →* ↥(E2.star (H ⊓ M) H K), Function.Surjective π ∧
      π.ker ≤ Subgroup.center (OTwoQuot K) ∧ ∀ x ∈ π.ker, Odd (orderOf x) := by
  have hKH := c.le_H
  have hψ : CFSG.Open.pCore 2 ↥K ≤ (starHom (M := H ⊓ M) hKH).ker := by
    intro y hy
    rw [MonoidHom.mem_ker, starHom_eq_one_iff]
    exact c.pCore_le_kerIn
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp c.comp) ⟨y, hy, rfl⟩)
  let π : OTwoQuot K →* ↥(E2.star (H ⊓ M) H K) :=
    QuotientGroup.lift _ (starHom (M := H ⊓ M) hKH) hψ
  have hcen : π.ker ≤ Subgroup.center (OTwoQuot K) := by
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have hy : (y : G) ∈ kerIn (H ⊓ M) H := (starHom_eq_one_iff hKH y).mp hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply mem_pCore_of_mem_pCoreOf
    have h1 := ((c.ker _).mp (inv_mem hy)).2 ((y' : G)⁻¹)
      (Subgroup.mem_sup_left (inv_mem y'.2))
    have h2 : (y : G)⁻¹ * (y' : G)⁻¹ * (y : G)⁻¹⁻¹ * (y' : G)⁻¹⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem y.2) (K.inv_mem y'.2)) (K.inv_mem (K.inv_mem y.2)))
        (K.inv_mem (K.inv_mem y'.2))
    have h3 := c.inf_pCore_le ⟨h1, h2⟩
    simpa [mul_assoc] using h3
  refine ⟨π, ?_, hcen, fun z hz => odd_orderOf_of_central (hcen hz)⟩
  intro w
  obtain ⟨y, rfl⟩ := starHom_surjective hKH w
  exact ⟨QuotientGroup.mk y, rfl⟩

end Cover

end Case2a

end CFSG.Quasithin.F146Field
