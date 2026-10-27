module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512FF
public import CFSG.Quasithin.Vol2.Ch5ModulesFFGrp
public import CFSG.Quasithin.Vol2.Ch5ModulesFFA5
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem eq_five_of_factorial_eq {k e : ℕ} (h5 : 5 ≤ k) (h8 : k ≤ 8)
    (h : k.factorial = 60 * 2 ^ e) : k = 5 := by
  have hc : Nat.Coprime 9 (2 ^ e) := Nat.Coprime.pow_right e (by norm_num)
  have key : ¬ 9 ∣ 60 * 2 ^ e := fun hd => absurd (hc.dvd_of_dvd_mul_right hd) (by norm_num)
  interval_cases k
  · rfl
  all_goals exfalso; apply key; rw [← h]; decide

theorem not_seven_dvd_sixty_mul (e : ℕ) : ¬ 7 ∣ 60 * 2 ^ e := fun hd =>
  absurd ((Nat.Coprime.pow_right e (by norm_num : Nat.Coprime 7 2)).dvd_of_dvd_mul_right hd)
    (by norm_num)

section Groups

variable {G : Type*} [Group G] [Finite G]

theorem exists_card_eq_mul_two_pow {K J : Subgroup G} (hKJ : K ≤ J)
    (hJK : J ≤ Subgroup.normalizer (K : Set G)) (h2 : ∀ j ∈ J, ∃ e : ℕ, j ^ 2 ^ e ∈ K) :
    ∃ e : ℕ, Nat.card J = Nat.card K * 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (K.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hJK
  have hp : IsPGroup 2 (↥J ⧸ K.subgroupOf J) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H j =>
      obtain ⟨e, he⟩ := h2 j j.2
      refine ⟨e, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using he
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hp
  refine ⟨e, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf J), he, mul_comm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv]

omit [Finite G] in
theorem inf_centralizer_eq_bot {K X : Subgroup G}
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K)
    (hO2 : pCoreOf 2 X = ⊥) (hZ : Subgroup.center ↥K = ⊥) :
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  set N := X ⊓ Subgroup.centralizer (K : Set G) with hN
  have key : ∀ x ∈ X, ∀ c ∈ N, x * c * x⁻¹ ∈ N := by
    intro x hx c hc
    obtain ⟨hcX, hcC⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hx hcX) (X.inv_mem hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : x⁻¹ * k * x ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hXK (X.inv_mem hx)) k).mp hk
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hcC _ hk'
    calc k * (x * c * x⁻¹) = x * ((x⁻¹ * k * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * k * x)) * x⁻¹ := by rw [hc]
      _ = x * c * x⁻¹ * k := by group
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key x hx c, fun hc => ?_⟩
    have := key x⁻¹ (X.inv_mem hx) _ hc
    simpa [mul_assoc] using this
  have hp : IsPGroup 2 ↥N := by
    intro c
    obtain ⟨e, he⟩ := h2 c c.2.1
    refine ⟨e, Subtype.ext ?_⟩
    have hcC : (c : G) ^ 2 ^ e ∈ Subgroup.centralizer (K : Set G) := Subgroup.pow_mem _ c.2.2 _
    have hz : (⟨(c : G) ^ 2 ^ e, he⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC k k.2)
    rw [hZ, Subgroup.mem_bot] at hz
    simpa using congrArg Subtype.val hz
  have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hXN hp
  rw [hO2] at h1
  exact le_bot_iff.mp h1

omit [Finite G] in
theorem card_le_card_mulAut_of {K X : Subgroup G} (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hC : X ⊓ Subgroup.centralizer (K : Set G) = ⊥) [Finite (MulAut ↥K)] :
    Nat.card X ≤ Nat.card (MulAut ↥K) := by
  let φ : ↥X →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : Subgroup.inclusion hXK x ∈ K.normalizerMonoidHom.ker := hx
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    have h2 : (x : G) ∈ X ⊓ Subgroup.centralizer (K : Set G) := ⟨x.2, h1⟩
    rw [hC, Subgroup.mem_bot] at h2
    exact (Subgroup.mem_bot).mpr (Subtype.ext h2)
  exact Nat.card_le_card_of_injective φ hφ

end Groups

section B51

variable {V : Type} [CommGroup V] [Finite V]

theorem b51Hyp_ffJ_of {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K) (hO2 : pCoreOf 2 X = ⊥)
    (hq : CFSG.IsQuasisimple ↥K) (hS : SQTKGroup ↥K) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hKA : ⁅K, A⁆ = K) :
    B51Hyp (ffJ X) K ∧ A ≤ ffJ X := by
  have hKJ : K ≤ ffJ X := B1Red.K_le_ffJ hKX hA hKA
  have hJX : ffJ X ≤ X := B6.ffJ_le X
  have hJn : ((ffJ X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ X)
  have hQ : pCoreOf 2 (ffJ X) = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 (ffJ X) X
      hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hF : quasithinGenFitting (ffJ X) = K :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hKJ
      (fun y hy l hl => (Subgroup.mem_normalizer_iff.mp (hXK (hJX hy)) l).mp hl)
      (B1Red.isQuasisimple_to_open hq) (fun y hy => h2 y (hJX hy)) hQ
  have hZ : centerOf (ffJ X) ≤ K := hF ▸ InternalSec.centerOf_le_quasithinGenFitting (ffJ X)
  exact ⟨⟨by rw [hF, sup_eq_left.2 hZ], hq, hS, hKJ, hQ, (InternalSec.ffJ_ffJ _).symm⟩,
    B6.le_ffJ hA⟩

end B51

section Exclusions

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {n : ℕ} {U Z : Subgroup V}

theorem card_eq_card_gam {D : FFModel} (hD : D.Faithful) (h : D.Realizes K U Z) :
    Nat.card K = Nat.card D.Gam := by
  obtain ⟨e⟩ := Ch3Sec3.nonempty_mulEquiv_of_realizes hD h
  exact Nat.card_congr e.toEquiv

theorem one_le_of_card_field {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) :
    1 ≤ m := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rw [hF, pow_zero] at h1
    omega
  · exact h

theorem false_of_card_eq (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) {c : ℕ}
    (hc : c < 16776960) (hk : ∀ k < 8, 2 ^ k * ((2 ^ k) ^ 2 - 1) ≠ c) (hKc : Nat.card K = c) :
    False := by
  rw [hcK] at hKc
  exact hk n (by have := le_seven_of_l2Order_lt hKc hc; omega) hKc

theorem false_of_natSL3 (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (hn : 1 ≤ n)
    {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (h : (FFModel.nat (StatedSL 3 F)).Realizes K U Z) : False := by
  have h1 := card_eq_card_gam (FFModel.nat_faithful _) h
  have h2 : Nat.card (FFModel.nat (StatedSL 3 F)).Gam =
      Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
    CFSG.SectionRank.OddCover.card_statedSL_three
  rw [h2, hF, hcK] at h1
  exact l2Order_ne_sl3 (one_le_of_card_field hF) hn h1.symm

theorem false_of_natSp4 (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (hn : 1 ≤ n)
    {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (h : (FFModel.nat (StatedSp 2 F)).Realizes K U Z) : False := by
  have h1 := card_eq_card_gam (FFModel.nat_faithful _) h
  have h2 : Nat.card (FFModel.nat (StatedSp 2 F)).Gam =
      Nat.card F ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, (Nat.card F ^ (2 * j) - 1) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 2
  rw [h2, hF, hcK] at h1
  exact l2Order_ne_sp4 (one_le_of_card_field hF) hn h1.symm

theorem false_of_natSL_two (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) {d : ℕ}
    (hd : d = 3 ∨ d = 4 ∨ d = 5) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (h : (FFModel.nat (StatedSL d F)).Realizes K U Z) : False := by
  have h1 := card_eq_card_gam (FFModel.nat_faithful _) h
  have h2 : Nat.card (FFModel.nat (StatedSL d F)).Gam = Nat.card (StatedSL d (ZMod 2)) :=
    (Nat.card_congr (statedSLEquivZModTwo hF).toEquiv).trans
      (Nat.card_congr (specialLinearGroupEquivStatedSL d (ZMod 2)).toEquiv)
  rw [h2] at h1
  rcases hd with rfl | rfl | rfl
  · rw [card_statedSL_three_zmodTwo] at h1
    exact false_of_card_eq hcK (by norm_num) (by decide) h1
  · rw [card_statedSL_four_zmodTwo] at h1
    exact false_of_card_eq hcK (by norm_num) (by decide) h1
  · rw [card_statedSL_five_zmodTwo] at h1
    exact false_of_card_eq hcK (by norm_num) (by decide) h1

theorem false_of_alt (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) {k : ℕ}
    (hk : k = 6 ∨ k = 7 ∨ k = 8) (h : AlternatingNatural K U Z k) : False := by
  have h1 := card_eq_card_gam (G64.altDn_faithful (by omega)) h
  change Nat.card K = Nat.card ↥(alternatingGroup (Fin k)) at h1
  rcases hk with rfl | rfl | rfl <;> rw [nat_card_alternatingGroup, Nat.card_fin] at h1
  · exact false_of_card_eq hcK (c := 360) (by norm_num) (by decide) (by rw [h1]; decide)
  · exact false_of_card_eq hcK (c := 2520) (by norm_num) (by decide) (by rw [h1]; decide)
  · exact false_of_card_eq hcK (c := 20160) (by norm_num) (by decide) (by rw [h1]; decide)

theorem false_of_a7Four (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (h : A7Four K U Z) :
    False := by
  obtain ⟨α, hα⟩ := h
  have h1 := card_eq_card_gam (a7Four_faithful α) hα
  change Nat.card K = Nat.card ↥(alternatingGroup (Fin 7)) at h1
  rw [nat_card_alternatingGroup, Nat.card_fin] at h1
  exact false_of_card_eq hcK (c := 2520) (by norm_num) (by decide) (by rw [h1]; decide)

theorem false_of_tripleA6 (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1))
    (h : TripleA6Six K U Z) : False := by
  obtain ⟨F, _, _, Γ₀, -, -, hhat, -, hR⟩ := h
  have h1 := card_eq_card_gam (FFModel.nat_faithful _) hR
  change Nat.card K = Nat.card ↥Γ₀ at h1
  obtain ⟨-, hZ3, ⟨eQ⟩⟩ := hhat
  have h2 : Nat.card ↥Γ₀ = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Γ₀), hZ3,
      Nat.card_congr eQ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact false_of_card_eq hcK (c := 1080) (by norm_num) (by decide) (h1.trans h2)

theorem false_of_extSq (hcK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) {d : ℕ}
    (hd : d = 4 ∨ d = 5) (h : SLExteriorTwo K U Z d) : False := by
  have h1 := card_eq_card_gam (G64.extSq_faithful (by omega)) h
  change Nat.card K = Nat.card (StatedSL d (ZMod 2)) at h1
  rcases hd with rfl | rfl
  · rw [card_statedSL_four_zmodTwo] at h1
    exact false_of_card_eq hcK (by norm_num) (by decide) h1
  · rw [card_statedSL_five_zmodTwo] at h1
    exact false_of_card_eq hcK (by norm_num) (by decide) h1

theorem false_of_g2 (hn : 2 ≤ n)
    (eK : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) {m : ℕ}
    (h : G2Natural K U Z m) : False := by
  obtain ⟨F, _, _, hF, hR⟩ := h
  obtain ⟨eG⟩ := Ch3Sec3.nonempty_mulEquiv_of_realizes (zornQ_faithful le_rfl) hR
  exact false_of_mulEquiv_psl2_g2 hn eK hF eG

theorem false_of_g2Derived (hn : 2 ≤ n)
    (eK : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (h : G2NaturalDerived K U Z 1) : False := by
  obtain ⟨F, _, _, hF, hR⟩ := h
  have hle : ⁅quasithinG2 F, quasithinG2 F⁆ ≤ quasithinG2 F :=
    Subgroup.commutator_le.mpr fun a ha b hb =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)
  obtain ⟨eG⟩ := Ch3Sec3.nonempty_mulEquiv_of_realizes (zornQ_faithful hle) hR
  exact false_of_mulEquiv_psl2_g2_commutator hn eK hF eG

end Exclusions

theorem l2FFModuleFact_of (h51 : AsB51) : L2FFModuleFact := by
  intro V _ _ hV2 X K n hn hKX hXK h2X hO2 ⟨eK⟩ hcK hq hS hFF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨A, hA⟩ := ((B1_4_5 hV2 X).out 1 2).1 hFF
  have hKA : ⁅K, A⁆ = K := Ch3Sec3.commutator_eq_of_two hXK h2X hO2 hq hA.1 hA.2.1
    fun a ha => hA.2.2.1.2 a ha
  obtain ⟨hB51, hAJ⟩ := b51Hyp_ffJ_of hKX hXK h2X hO2 hq hS hA hKA
  set J := ffJ X with hJdef
  have hKJ : K ≤ J := hB51.2.2.2.1
  have hJX : J ≤ X := B6.ffJ_le X
  obtain ⟨hP1, hP2, -, hP4, hP5, -⟩ := h51 V hV2 J K hB51
  set U := commV K with hUdef
  have hCinv : ∀ k : ↥K, ∀ c ∈ fixV K, (k : MulAut V) c ∈ fixV K := fun k c hc => by
    rw [(mem_fixV.mp hc) k k.2]
    exact hc
  have hVK : U ⊔ fixV K = ⊤ := by
    rcases hP5 with h | ⟨-, hL5, -⟩
    · exact eq_top_iff.mpr (h ▸ sup_le_sup_left (B1.fixV_le_fixV hKJ) U)
    · exfalso
      rcases hL5 with ⟨m, F, _, _, hF, hR⟩ | h | h | ⟨F, _, _, hF, hR⟩
      · exact false_of_natSp4 hcK hn1 hF hR
      · exact false_of_alt hcK (Or.inl rfl) h
      · exact false_of_alt hcK (Or.inr (Or.inr rfl)) h
      · exact false_of_natSL_two hcK (Or.inl rfl) (by rw [hF, pow_one]) hR
  have hnat : ∀ m, BinaryNaturalSL K U (fixV K ⊓ U) 2 m → BinaryNaturalSL K ⊤ (fixV K) 2 n := by
    rintro m ⟨F, _, _, hF, hR⟩
    have h1 := card_eq_card_gam (FFModel.nat_faithful _) hR
    have h2 : Nat.card (FFModel.nat (StatedSL 2 F)).Gam = Nat.card F * (Nat.card F ^ 2 - 1) :=
      card_statedSL_two
    rw [h2, hF, hcK] at h1
    have hmn : m = n := (l2Order_inj h1).symm
    refine ⟨F, inferInstance, inferInstance, hmn ▸ hF, ?_⟩
    rw [inf_comm] at hR
    have := Ch3Sec3.realizes_sup_of_inf hCinv hR
    rwa [hVK] at this
  by_cases hInt : IsIntDirect U (fixV K) ⊤
  swap
  · left
    obtain ⟨-, hL2⟩ := hP2.2 hInt
    rcases hL2 with ⟨m, hm⟩ | ⟨m, F, _, _, hF, hR⟩ | h | h | h | h | ⟨F, _, _, hF, hR⟩
    · exact hnat m hm
    · exact (false_of_natSp4 hcK hn1 hF hR).elim
    · obtain ⟨m, hm⟩ := h
      exact (false_of_g2 hn eK hm).elim
    · exact (false_of_alt hcK (Or.inl rfl) h).elim
    · exact (false_of_alt hcK (Or.inr (Or.inr rfl)) h).elim
    · exact (false_of_g2Derived hn eK h).elim
    · exact (false_of_natSL_two hcK (Or.inl rfl) (by rw [hF, pow_one]) hR).elim
  have hZ : fixV K ⊓ U = ⊥ := by rw [inf_comm]; exact hInt.2
  obtain ⟨-, hc⟩ := hP1
  rcases hc with ⟨-, hpair, hT⟩ | ⟨-, m, F, _, _, hF, I, π, -, -, hreal, -⟩ |
      ⟨m, -, hm45, π, U₁, U₂, -, hreal, -⟩ | ⟨-, m, hm45, k, hk1, -, I, π, -, -, -, hreal⟩
  rotate_left
  · exact (false_of_natSL3 hcK hn1 hF ⟨π, hreal 0⟩).elim
  · exact (false_of_natSL_two hcK (by omega) (Nat.card_zmod 2)
      ⟨π, hreal⟩).elim
  · exact (false_of_natSL_two hcK (by omega) (Nat.card_zmod 2)
      ⟨π, hreal ⟨0, hk1⟩⟩).elim
  rcases hpair with ⟨m, hm⟩ | ⟨m, F, _, _, hF, hR⟩ | ⟨m, F, _, _, hF, hR⟩ | ⟨m, hm⟩ | h |
      h5 | h | h | h | h | ⟨F, _, _, hF, hR⟩ | ⟨F, _, _, hF, hR⟩ | h | h
  · exact Or.inl (hnat m hm)
  · exact (false_of_natSL3 hcK hn1 hF hR).elim
  · exact (false_of_natSp4 hcK hn1 hF hR).elim
  · exact (false_of_g2 hn eK hm).elim
  · exact (false_of_g2Derived hn eK h).elim
  rotate_left
  · exact (false_of_alt hcK (Or.inl rfl) h).elim
  · exact (false_of_alt hcK (Or.inr (Or.inl rfl)) h).elim
  · exact (false_of_a7Four hcK h).elim
  · exact (false_of_tripleA6 hcK h).elim
  · exact (false_of_natSL_two hcK (Or.inr (Or.inl rfl)) (by rw [hF, pow_one]) hR).elim
  · exact (false_of_natSL_two hcK (Or.inr (Or.inr rfl)) (by rw [hF, pow_one]) hR).elim
  · exact (false_of_extSq hcK (Or.inl rfl) h).elim
  · exact (false_of_extSq hcK (Or.inr rfl) h).elim
  right
  rw [hZ] at h5 hT
  obtain ⟨eA⟩ : Nonempty (↥K ≃* ↥(alternatingGroup (Fin 5))) :=
    Ch3Sec3.nonempty_mulEquiv_of_realizes (G64.altDn_faithful (by norm_num)) h5
  have hK60 : Nat.card K = 60 := by
    rw [Nat.card_congr eA.toEquiv]
    exact SteinbergCB.nat_card_alternating_five
  have hn2 : n = 2 := l2Order_inj (hcK.symm.trans (hK60.trans (by norm_num)))
  obtain ⟨T, hTJ⟩ := exists_isSylowTwoOf J
  rcases hT T hTJ with hJK | ⟨-, hcase⟩
  ·
    exfalso
    have hAK : A ≤ K := hJK ▸ hAJ
    have h1 := hA.2.2.2 ⊥ bot_le
    rw [B1.card_bot_mul_card_fixV] at h1
    have h2 := card_mul_card_fixV_lt_of_altDn_five hInt h5 hAK hA.2.1 hA.2.2.1
    omega
  obtain ⟨e, he⟩ := exists_card_eq_mul_two_pow hKJ (hJX.trans hXK) fun j hj => h2X j (hJX hj)
  rw [hK60] at he
  rcases hcase with ⟨k, hk5, hk8, hsym⟩ | ⟨F, _, _, hF, hR⟩
  swap
  ·
    exfalso
    have := charP_two_of_card hF
    have h1 := card_eq_card_gam (zornQ_faithful le_rfl) hR
    change Nat.card J = Nat.card ↥(quasithinG2 F) at h1
    have h7 := seven_dvd_card_g2 (F := F)
    rw [← h1, he] at h7
    exact not_seven_dvd_sixty_mul e h7
  have hJk : Nat.card J = k.factorial := by
    rw [card_eq_card_gam (G64.symDn_faithful hk5) hsym]
    exact (Nat.card_perm (α := Fin k)).trans (by rw [Nat.card_fin])
  have hk : k = 5 := eq_five_of_factorial_eq hk5 hk8 (hJk.symm.trans he)
  subst hk
  have hJ120 : Nat.card J = 120 := by rw [hJk]; decide
  obtain ⟨eJ⟩ : Nonempty (↥J ≃* Equiv.Perm (Fin 5)) :=
    Ch3Sec3.nonempty_mulEquiv_of_realizes (G64.symDn_faithful le_rfl) hsym
  have hcen : Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eA z ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := eA.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), Subgroup.mem_bot,
      MulEquiv.map_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hCX := inf_centralizer_eq_bot hXK h2X hO2 hcen
  have eAut := CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm eA
  have : Finite (MulAut ↥K) := Finite.of_equiv _ eAut.symm.toEquiv
  have hAut : Nat.card (MulAut ↥K) = 120 := by
    rw [Nat.card_congr eAut.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hX := card_le_card_mulAut_of hXK hCX
  have hXJ : X = J := (Subgroup.eq_of_le_of_card_ge hJX (by omega)).symm
  have hIntJ : IsIntDirect U (fixV J) ⊤ := by
    by_contra hnot
    obtain ⟨-, h4 | ⟨-, ⟨k, hk, hsym'⟩, -⟩⟩ := hP4 hnot
    · exact h4 hInt
    · have h1 := card_eq_card_gam (G64.symDn_faithful (by omega)) hsym'
      have h2 : Nat.card (FFModel.symDn k).Gam = k.factorial :=
        (Nat.card_perm (α := Fin k)).trans (by rw [Nat.card_fin])
      rw [h2, hJ120] at h1
      rcases hk with rfl | rfl <;> revert h1 <;> decide
  refine ⟨hn2, ?_, ⟨(MulEquiv.subgroupCongr hXJ).trans eJ⟩, ?_⟩
  · rw [hXJ]
    exact hIntJ
  · rw [hXJ]
    exact hsym

theorem stmt5_1_2_FF_of_asB51 (h51 : AsB51) : Stmt5_1_2_FF :=
  stmt5_1_2_FF_of (l2FFModuleFact_of h51)

theorem stmt5_1_2_of_asB51 (h331 : Stmt3_3_1) (h51 : AsB51) : Stmt5_1_2 :=
  stmt5_1_2_of h331 (stmt5_1_2_FF_of_asB51 h51)

end CFSG.Quasithin.H13
