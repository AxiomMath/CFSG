module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveMain
public import CFSG.Quasithin.H13.NQCatT513L35
public import CFSG.Quasithin.H13.NQCatT513U35

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513

theorem exists_zpow_mul_of_card {G : Type*} [Group G] [Finite G] {S H : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSH : S ≤ H) (hcard : Nat.card H = 5 * Nat.card S) {g : G}
    (hgH : g ∈ H) (hg : orderOf g = 5) : ∀ h ∈ H, ∃ a : ℤ, ∃ s ∈ S, h = g ^ a * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP5 : Nat.card (Subgroup.zpowers g) = 5 := by rw [Nat.card_zpowers, hg]
  have hbot : Subgroup.zpowers g ⊓ S = ⊥ := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers g)) (Nat.card S) := by
      rw [hP5, hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  let f : ↥(Subgroup.zpowers g) × ↥S → ↥H := fun p =>
    ⟨p.1 * p.2, H.mul_mem (Subgroup.zpowers_le.mpr hgH p.1.2) (hSH p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, s⟩ ⟨b, t⟩ h
    have h1 : (a : G) * s = b * t := congrArg Subtype.val h
    have h2 : (b : G)⁻¹ * a = t * (s : G)⁻¹ := by
      calc (b : G)⁻¹ * a = (b : G)⁻¹ * (a * s) * (s : G)⁻¹ := by group
        _ = (b : G)⁻¹ * (b * t) * (s : G)⁻¹ := by rw [h1]
        _ = t * (s : G)⁻¹ := by group
    have hmem : (b : G)⁻¹ * a ∈ Subgroup.zpowers g ⊓ S :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.zpowers g).mul_mem ((Subgroup.zpowers g).inv_mem b.2) a.2,
        h2 ▸ S.mul_mem t.2 (S.inv_mem s.2)⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hab : a = b := Subtype.ext hmem.symm
    subst hab
    have hst : (s : G) = t := mul_left_cancel h1
    rw [Subtype.ext hst]
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hP5, hcard])
  intro h hh
  obtain ⟨⟨a, s⟩, hp⟩ := hbij.2 ⟨h, hh⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
  refine ⟨n, s, s.2, ?_⟩
  have h3 : (a : G) * s = h := congrArg Subtype.val hp
  rw [← h3, hn]

theorem noFiveOver_G35 : NoFiveOver L35.G35 := by
  intro S H hS hSH hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨h1, h2⟩ := isSylowTwoOf_top_index hS
  obtain ⟨⟨g, hgH⟩, hg5⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5
    (by rw [hcard]; exact dvd_mul_right 5 _)
  have hgo : orderOf g = 5 := by rw [← Subgroup.orderOf_mk g hgH]; exact hg5
  have hprod := exists_zpow_mul_of_card h1 hSH hcard hgH hgo
  obtain ⟨c, hcT⟩ := MulAction.exists_smul_eq L35.G35 (h1.toSylow h2) L35.T0Sylow
  have hmap : S.map (MulAut.conj c).toMonoidHom = L35.T0 := by
    have h3 := congrArg (fun P : Sylow 2 L35.G35 => (P : Subgroup L35.G35)) hcT
    simp only [Sylow.coe_subgroup_smul, L35.coe_T0Sylow, IsPGroup.toSylow_coe] at h3
    rw [← h3, Subgroup.pointwise_smul_def]
    rfl
  have hmemT0 : ∀ t₀ ∈ L35.T0, c⁻¹ * t₀ * c ∈ S := by
    intro t₀ ht₀
    rw [← hmap] at ht₀
    obtain ⟨t, ht, rfl⟩ := ht₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c⁻¹ * (c * t * c⁻¹) * c = t by group]
    exact ht
  have hT0mem : ∀ t ∈ S, c * t * c⁻¹ ∈ L35.T0 := by
    intro t ht
    rw [← hmap]
    exact ⟨t, ht, rfl⟩
  set g₀ := c * g * c⁻¹ with hg₀
  have hg₀o : orderOf g₀ = 5 := by
    rw [hg₀, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hgo]
  have hg₀pow : g₀ ^ 11625 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hg₀o]
    norm_num
  have hperm₀ : ∀ t ∈ L35.T0, ∃ a : ℤ, ∃ t' ∈ L35.T0, t * g₀ = g₀ ^ a * t' := by
    intro t₀ ht₀
    have hu := hmemT0 t₀ ht₀
    obtain ⟨a, s, hs, he⟩ := hprod _ (H.mul_mem (hSH hu) hgH)
    refine ⟨a, c * s * c⁻¹, hT0mem s hs, ?_⟩
    have hg₀a : g₀ ^ a = c * g ^ a * c⁻¹ := by
      rw [hg₀, ← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
    rw [hg₀a]
    calc t₀ * g₀ = c * (c⁻¹ * t₀ * c * g) * c⁻¹ := by rw [hg₀]; group
      _ = c * (g ^ a * s) * c⁻¹ := by rw [he]
      _ = c * g ^ a * c⁻¹ * (c * s * c⁻¹) := by group
  have h3 := Certificates.certificate7155 _ hg₀pow hperm₀
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hg₀o] at h4
  norm_num at h4

theorem fiveRigid_G35 : FiveRigid L35.G35 :=
  ⟨center_G35, fiveInner_of_oddInner inner_of_odd_sl35, noFiveOver_G35⟩

theorem quot_G35_of {X : Type} [Group X] (h : IsPSLEps3 true 5 1 X ∨ IsSLEps3 true 5 X) :
    Nonempty (X ⧸ Subgroup.center X ≃* L35.G35) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK5 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 5 → Nonempty (K ≃+* ZMod 5) := by
    intro K _ _ hK
    let _ : Fintype K := Fintype.ofFinite K
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Nat.card_zmod])⟩
  rcases h with hQ | hQ
  · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨σ⟩ := hK5 K (by rw [hK, pow_one])
    let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5) ≃* L35.G35 :=
      (QuotientGroup.quotientMulEquivOfEq center_G35).trans QuotientGroup.quotientBot
    exact (nonempty_quotCenter_equiv (e₀.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3)
          σ).trans e₂))) center_G35).2
  · obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨σ⟩ := hK5 K hK
    exact (nonempty_quotCenter_equiv (e₀.trans
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.trans
        (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 3) σ)))
      center_G35).2

theorem quot_PU_of {X : Type} [Group X] (h : IsPSLEps3 false 5 1 X ∨ IsSLEps3 false 5 X) :
    Nonempty (X ⧸ Subgroup.center X ≃* U35.PU) := by
  rcases h with hQ | hQ
  ·
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨φ⟩ := nonempty_ringEquiv_f25 K (by rw [hK]; norm_num)
    let E : X ≃* U35.PU := e₀.trans
      ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (5 ^ 1))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv CFSG.Quasithin.H13.KGU35.f25Data
          (n := 3) (by norm_num)).symm)
    exact (nonempty_quotCenter_equiv E U35.center_PU).2
  ·
    obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨φ⟩ := nonempty_ringEquiv_f25 K (by rw [hK]; norm_num)
    let E : X ≃* ↥U35.SU := e₀.trans
      (((CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ).subgroupMap
        (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K)).trans
        (MulEquiv.subgroupCongr (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 5)))
    exact ⟨(QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)).trans
      (CFSG.RankThree.PartTwo.KFacts.suCenterEquiv CFSG.Quasithin.H13.KGU35.f25Data
        (by norm_num))⟩

theorem fiveRigidQFive_of (hU : FiveRigid U35.PU) :
    FiveRigidQFive := by
  intro X _ _ h
  have hG : ∀ h : IsPSLEps3 true 5 1 X ∨ IsSLEps3 true 5 X, FiveRigid (X ⧸ Subgroup.center X) :=
    fun h => by
      obtain ⟨e⟩ := quot_G35_of h
      exact fiveRigid_of_mulEquiv e.symm fiveRigid_G35
  rcases h with ⟨s, hs⟩ | hs | hs
  · cases s
    · obtain ⟨e⟩ := quot_PU_of hs
      exact fiveRigid_of_mulEquiv e.symm hU
    · exact hG hs
  · exact hG (Or.inl hs)
  · exact hG (Or.inr hs)

end CFSG.Quasithin.H13.FiveNorm
