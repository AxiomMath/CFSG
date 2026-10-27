module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GA
public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4P

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def ModelM24 (X : Type) [Group X] : Prop :=
  ∀ (Y V S : Subgroup X) (z : X), ⁅Y, Y⁆ = Y → IsSporadic .M24 (↥Y ⧸ CFSG.pCore 2 ↥Y) →
    V ≤ centerOf (pCoreOf 2 Y) → V ≠ ⊥ → V = ⁅V, Y⁆ → IsSylowTwoOf S Y → z ∈ V → z ≠ 1 →
    z ∈ Subgroup.centralizer (S : Set X) →
    IsHat (↥(perfectCore (Subgroup.centralizer ({z} : Set X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (Subgroup.centralizer ({z} : Set X))))
      (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
    (⊤ : Subgroup X) = Y ⊔ perfectCore (Subgroup.centralizer ({z} : Set X))

theorem modelM24_of {X : Type} [Group X] [Finite X]
    {P0 Hj B0 V0 : Subgroup X} {z0 : X} (hP0 : Nat.card P0 = 2 ^ 21)
    (hXfac : (Nat.card X).factorization 2 = 21)
    (hconj : ∀ A : Subgroup X, IsPGroup 2 ↥A → ∃ g : X, ∀ x ∈ A, g⁻¹ * x * g ∈ P0)
    (hZ : ∀ x ∈ centerOf P0, x = 1 ∨ x = z0)
    (h23 : ¬ 23 ∣ Nat.card ↥(Subgroup.centralizer ({z0} : Set X)))
    (hover : ∀ Y : Subgroup X, P0 ≤ Y → ∀ N : Subgroup X, IsPGroup 2 ↥N → N ≠ ⊥ →
      (∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N) →
      Y ≤ Hj ∨ Y ≤ Subgroup.centralizer ({z0} : Set X) ∨ Y ≤ Subgroup.normalizer (V0 : Set X))
    (hV0 : Nat.card V0 = 8) (hz0V0 : z0 ∈ V0) (hHj : Nat.card Hj = 501397585920)
    (hB0 : perfectCore (Subgroup.centralizer ({z0} : Set X)) = B0)
    (hhat : IsHat (↥B0 ⧸ CFSG.pCore 2 ↥B0) (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    (htop : Hj ⊔ B0 = ⊤) : ModelM24 X := by
  intro Y V S z hYp hYq hV hV1 hVY hS hzV hz1 hzS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨eY⟩ := hYq
  set g : ↥Y →* CFSG.Blueprint.NativeSporadic.Carrier .M24 :=
    eY.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) with hg
  have hgs : Function.Surjective g := eY.surjective.comp (QuotientGroup.mk'_surjective _)
  have hgk : ∀ b : ↥Y, g b = 1 ↔ b ∈ CFSG.pCore 2 ↥Y := fun b => by
    rw [hg, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hgsolv : Group.IsSolvable ↥g.ker := by
    have hk : g.ker = CFSG.pCore 2 ↥Y := by
      ext b
      exact hgk b
    rw [hk]
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).isNilpotent
    infer_instance
  have hM24 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040 :=
    CFSG.Sporadic.Mathieu.card_M24
  have hcardY : Nat.card ↥Y = Nat.card ↥(CFSG.pCore 2 ↥Y) * 244823040 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y),
      Nat.card_congr eY.toEquiv, hM24, mul_comm]
  have hVO : V ≤ pCoreOf 2 Y := fun v hv => (hV hv).1
  have hV2 : IsPGroup 2 ↥V := (pCoreOf_isPGroup 2 Y).to_le hVO
  have hYV : Y ≤ Subgroup.normalizer (V : Set X) := by
    have h := Subgroup.normalizer_commutator_ge_right (H₁ := V) (H₂ := Y)
    rwa [← hVY] at h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 23
    (show 23 ∣ Nat.card ↥Y by rw [hcardY]; exact Dvd.dvd.mul_left (by norm_num) _)
  have hy' : orderOf (y : X) = 23 := by rw [Subgroup.orderOf_coe, hy]
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hyc : ¬ V ≤ Subgroup.centralizer ({(y : X)} : Set X) := by
    intro hle
    have hNn : Y ≤ Subgroup.normalizer
        ((Y ⊓ Subgroup.centralizer (V : Set X) : Subgroup X) : Set X) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
        normalizer_le_normalizer_centralizer V (hYV hx)⟩
    rcases eq_or_le_ker hYp g hgs hgsolv inf_le_left hNn with h | h
    · have hYC : Y ≤ Subgroup.centralizer (V : Set X) := by
        rw [← h]
        exact inf_le_right
      exact hV1 (hVY.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp hYC)))
    · have hyN : (y : X) ∈ Y ⊓ Subgroup.centralizer (V : Set X) :=
        ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun v hv =>
          Subgroup.mem_centralizer_singleton_iff.mp (hle hv)⟩
      have hyO := (hgk y).mp (h y hyN)
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨y, hyO⟩
      have h0 : y ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have h1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h0
      rw [hy] at h1
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h1))
      omega
  have hV11 := two_pow_eleven_le_card hV2 hy' (hYV y.2) hyc
  have hO2 : Nat.card ↥(CFSG.pCore 2 ↥Y) = Nat.card ↥(pCoreOf 2 Y) := by
    rw [pCoreOf, Subgroup.card_map_of_injective Y.subtype_injective]
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).exists_card_eq
  have hc11 : 11 ≤ c := by
    have h0 : Nat.card ↥V ≤ 2 ^ c := by
      rw [← hc, hO2]
      exact Subgroup.card_le_of_le hVO
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hV11.trans h0)
  have hYfac : (Nat.card ↥Y).factorization 2 = c + 10 := by
    rw [hcardY, hc, show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num, ← mul_assoc, ← pow_add,
      factorization_two_pow_mul (by norm_num) (by norm_num)]
  have hScard : Nat.card ↥S = 2 ^ (c + 10) := by rw [hS.card_eq, twoPart, hYfac]
  have hc11' : c = 11 := by
    have h1 : 2 ^ (c + 10) ∣ Nat.card X := hScard ▸ Subgroup.card_subgroup_dvd_card S
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h1
    rw [hXfac] at h2
    omega
  subst hc11'
  obtain ⟨g₀, hg₀⟩ := hconj S hS.2.1
  set cg := MulAut.conj g₀⁻¹ with hcg
  have hcg_apply : ∀ x, cg x = g₀⁻¹ * x * g₀ := fun x => by
    rw [hcg, MulAut.conj_apply, inv_inv]
  have hSP : S.map cg.toMonoidHom = P0 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hcg_apply]
      exact hg₀ x hx
    · rw [hP0, Subgroup.card_map_of_injective cg.injective, hScard]
  have hzS' : z ∈ S := B6.pCoreOf_two_le_of_isSylowTwoOf hS (hVO hzV)
  have hzP : cg z ∈ P0 := by
    rw [← hSP]
    exact Subgroup.mem_map_of_mem cg.toMonoidHom hzS'
  have hz₁ : cg z = z0 := by
    have hz₁P : cg z ∈ centerOf P0 := by
      refine ⟨hzP, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro t ht
      rw [← hSP] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_iff.mp hzS s hs]
    rcases hZ _ hz₁P with h | h
    · exact absurd (cg.injective (h.trans (map_one cg).symm)) hz1
    · exact h
  set Y₁ := Y.map cg.toMonoidHom with hY₁
  have hPY₁ : P0 ≤ Y₁ := hSP ▸ Subgroup.map_mono hS.1
  have hV₁2 : IsPGroup 2 ↥(V.map cg.toMonoidHom) := hV2.map _
  have hV₁ : V.map cg.toMonoidHom ≠ ⊥ := fun h =>
    hV1 ((Subgroup.map_eq_bot_iff_of_injective V cg.injective).mp h)
  have hY₁N : Y₁ ≤ Subgroup.normalizer ((V.map cg.toMonoidHom : Subgroup X) : Set X) := by
    rw [hY₁, ← Subgroup.map_equiv_normalizer_eq V cg]
    exact Subgroup.map_mono hYV
  have hNY : ∀ u ∈ Y₁, ∀ x ∈ V.map cg.toMonoidHom, u * x * u⁻¹ ∈ V.map cg.toMonoidHom :=
    fun u hu x hx => (Subgroup.mem_normalizer_iff.mp (hY₁N hu) x).mp hx
  have hy₁ : cg y ∈ Y₁ := Subgroup.mem_map_of_mem _ y.2
  have hy₁o : orderOf (cg y) = 23 := by rw [MulEquiv.orderOf_eq, hy']
  have hnot : ¬ cg y ∈ Subgroup.centralizer ({z0} : Set X) := fun h =>
    h23 (hy₁o ▸ Subgroup.orderOf_dvd_natCard _ h)
  have hY₁H : Y₁ = Hj := by
    rcases hover Y₁ hPY₁ _ hV₁2 hV₁ hNY with h | h | h
    · refine Subgroup.eq_of_le_of_card_ge h ?_
      rw [hHj, hY₁, Subgroup.card_map_of_injective cg.injective, hcardY, hc]
      norm_num
    · exact absurd (h hy₁) hnot
    · exfalso
      have hV0' := le_centralizer_of_card_lt hy₁o (h hy₁) (by rw [hV0]; norm_num)
      exact hnot (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hV0' hz0V0)).symm)
  have hC : (Subgroup.centralizer ({z} : Set X)).map cg.toMonoidHom =
      Subgroup.centralizer ({z0} : Set X) := by
    rw [J4.map_centralizer_singleton cg z, hz₁]
  have hKZ : (perfectCore (Subgroup.centralizer ({z} : Set X))).map cg.toMonoidHom = B0 := by
    rw [map_perfectCore, hC, hB0]
  refine ⟨?_, ?_⟩
  · let e : ↥(perfectCore (Subgroup.centralizer ({z} : Set X))) ≃* ↥B0 :=
      ((perfectCore (Subgroup.centralizer ({z} : Set X))).equivMapOfInjective cg.toMonoidHom
        cg.injective).trans (MulEquiv.subgroupCongr hKZ)
    exact IsHat.of_mulEquiv (J4.pCoreQuotEquiv e).symm hhat
  · symm
    apply Subgroup.map_injective (f := cg.toMonoidHom) cg.injective
    rw [Subgroup.map_sup, ← hY₁, hY₁H, hKZ, htop, Subgroup.map_top_of_surjective _ cg.surjective]

end CFSG.Quasithin.H13.Ch4.G443J4
