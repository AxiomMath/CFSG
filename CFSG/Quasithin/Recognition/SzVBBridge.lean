module

public import CFSG.Quasithin.Recognition.SzVBFam
public import CFSG.Quasithin.Recognition.SzVBBenderData
public import CFSG.Quasithin.Recognition.SzVBBridgeAux

public section


namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Holt.H78

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem ker_le_normalizer_of_central {K : Type*} [Group K] (hSyl : IsSylowTwoOf (S ⊓ K1) K1)
    (ψ : OTwoQuot K1 →* K) (hker : ψ.ker ≤ Subgroup.center (OTwoQuot K1)) (Qs : Sylow 2 ↥K1)
    (hQs : (Qs : Subgroup ↥K1) = (S ⊓ K1).subgroupOf K1) :
    (ψ.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1))).ker ≤
      Subgroup.normalizer ((Qs : Subgroup ↥K1) : Set ↥K1) := by
  have hO2 : CFSG.Open.pCore 2 ↥K1 ≤ (Qs : Subgroup ↥K1) := by
    intro x hx
    rw [hQs, Subgroup.mem_subgroupOf]
    exact CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hSyl ⟨x, hx, rfl⟩
  have hconj : ∀ y ∈ (ψ.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1))).ker,
      ∀ q ∈ (Qs : Subgroup ↥K1), y * q * y⁻¹ ∈ (Qs : Subgroup ↥K1) := by
    intro y hy q hq
    have hc : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1)) y ∈ Subgroup.center (OTwoQuot K1) :=
      hker hy
    have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1)) (y * q * y⁻¹) =
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1)) q := by
      rw [map_mul, map_mul, map_inv]
      have := Subgroup.mem_center_iff.mp hc ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1)) q)
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have h2 : (y * q * y⁻¹)⁻¹ * q ∈ CFSG.Open.pCore 2 ↥K1 := QuotientGroup.eq.mp h1
    have h3 := hO2 h2
    have e : y * q * y⁻¹ = q * ((y * q * y⁻¹)⁻¹ * q)⁻¹ := by group
    rw [e]
    exact Qs.mul_mem hq (Qs.inv_mem h3)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hconj y hy x hx, fun hx => by
    have := hconj y⁻¹ ((ψ.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1))).ker.inv_mem hy) _ hx
    simpa [mul_assoc] using this⟩

theorem exists_isBenderAction_imgK (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1)) :
    ∃ n' i e : ℕ, IsBenderAction ↥(imgK K1 (K1 ⊔ S) (conjClosure Zs L2))
        (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) n' i e ∧
      (¬ IsL2Quot 2 (OTwoQuot K1) → 9 ≤ Nat.card (ConjSet (K1 ⊔ S) (conjClosure Zs L2))) := by
  obtain ⟨K, _, ψ, e, i, hψ, hker, hB, hcase⟩ := exists_benderData hn hX
  have hSyl : IsSylowTwoOf (S ⊓ K1) K1 := h.hyp.h1.sylow
  have hP : IsPGroup 2 ((S ⊓ K1).subgroupOf K1) := hSyl.2.1.comap_subtype
  obtain ⟨Qs, hQs⟩ : ∃ Qs : Sylow 2 ↥K1, (Qs : Subgroup ↥K1) = (S ⊓ K1).subgroupOf K1 :=
    ⟨hP.toSylow hSyl.2.2, rfl⟩
  have hπ : Function.Surjective (ψ.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1))) :=
    hψ.comp (QuotientGroup.mk'_surjective _)
  have hY := ker_le_normalizer_of_central hSyl ψ hker Qs hQs
  have hIB : IsBenderAction ↥(imgK K1 (K1 ⊔ S) (conjClosure Zs L2))
      (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) n i e :=
    exists_isBenderAction_imgK_of_bender (B := borelOf K1 S) le_sup_left
      (fun k hk k' hk' => conjSub_eq_iff_mem_borelOf hRO h hk hk')
      (fun x hx => exists_mem_K1_conjSub h hRO hx)
      (ψ.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1))) hπ Qs
      (fun k => by
        rw [hQs]
        exact (CFSG.Quasithin.Background.Harris.R1.mem_borelOf_iff_mem_normalizer k).symm)
      hY hB
  refine ⟨n, i, e, hIB, fun hL => ?_⟩
  rw [hIB.card_eq]
  have h4 : 4 ≤ 2 ^ n := hIB.four_le_q
  rcases hcase with ⟨hi1, hL2⟩ | hi2
  · have hn3 : 3 ≤ n := by
      by_contra hlt
      have hn2 : n = 2 := by omega
      rw [hn2] at hL2
      exact hL hL2
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    rw [hi1, pow_one]
    omega
  · have h16 : 16 ≤ (2 ^ n) ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h4 2
    have h2i : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ i := Nat.pow_le_pow_right (by positivity) hi2
    omega

end CFSG.Quasithin.SzVB
