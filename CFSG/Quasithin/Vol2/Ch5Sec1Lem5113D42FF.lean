module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Para
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8A
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

namespace FF3D42

theorem sl2_ne {n N : ℕ} (hN : N = 211341312) : (2 ^ n) * ((2 ^ n) ^ 2 - 1) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 1024 ≤ 2 ^ n := by
      calc 1024 = 2 ^ 10 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 1073740800 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      le_trans (by norm_num) (Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    omega

theorem sl3_ne {n N : ℕ} (hN : N = 211341312) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4277145600 ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      le_trans (by norm_num) (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1)))
    omega

theorem sp4_ne {n N : ℕ} (hN : N = 211341312) :
    (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 1056706560 ≤ (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) :=
      le_trans (by norm_num) (Nat.mul_le_mul (Nat.pow_le_pow_left hq _)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)))
    omega

theorem g2_ne {n N : ℕ} (hN : N = 211341312) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 251596800 ≤ (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      le_trans (by norm_num) (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)))
    omega

section Models

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem not_sl2 (hN : Nat.card ↥L = 211341312) {n : ℕ}
    (h : BinaryNaturalSL L U Z 2 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hc := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_two1527d, hF] at hc
  exact sl2_ne hN hc.symm

theorem not_sl3 (hN : Nat.card ↥L = 211341312) {n : ℕ}
    (h : BinaryNaturalSL L U Z 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hc := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_three1527d, hF] at hc
  exact sl3_ne hN hc.symm

theorem not_sp4 (hN : Nat.card ↥L = 211341312) {n : ℕ}
    (h : BinaryNaturalSp4 L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hc := card_eq_of_nat_realizes1527d hπ
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  have hX : Nat.card ↥(Assembly.LowTwoRank.StatedSp 2 F) =
      (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
    rw [hI, Finset.prod_pair (by norm_num)]
  rw [hX] at hc
  exact sp4_ne hN hc.symm

theorem not_g2 (hN : Nat.card ↥L = 211341312) {n : ℕ}
    (h : G2Natural L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    have := FFC.charP_two_of_card_pow hF
    exact (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
  rw [card_quasithinG2_1527d hF, hF] at hcard
  exact g2_ne hN hcard.symm

theorem not_g2d (hN : Nat.card ↥L = 211341312)
    (h : G2NaturalDerived L U Z 1) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hG2 := card_quasithinG2_1527d hF
  rw [hF] at hG2
  have hfin : Finite ↥(CFSG.Open.quasithinG2 F) :=
    Nat.finite_of_card_ne_zero (by rw [hG2]; norm_num)
  have h1 : Nat.card ↥L ∣
      Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    Subgroup.card_dvd_of_surjective hπ.1
  have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ∣
      Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    refine Subgroup.card_dvd_of_le ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Open.quasithinG2 F).mul_mem
      ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
        ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
  have h3 := h1.trans h2
  rw [hG2] at h3
  have h4 := Nat.le_of_dvd (by norm_num) h3
  norm_num at h4
  omega

theorem not_surj_sl {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hN : Nat.card ↥L = 211341312)
    (π : ↥(Assembly.LowTwoRank.StatedSL d (ZMod 2)) →* ↥L) (hπ : Function.Surjective π) :
    False := by
  have hs := B69.isSimpleGroup_statedSL_two (K := ZMod 2) (Nat.card_zmod 2) (n := d)
    (by omega)
  rcases hs.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hk
    have hc := (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)).symm
    rcases hd with rfl | rfl
    · rw [card_statedSL_four_zmod1527d] at hc
      omega
    · rw [card_statedSL_five_zmod1527d] at hc
      omega
  · have h1 : Nat.card ↥L = 1 := by
      refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
      obtain ⟨a, rfl⟩ := hπ x
      obtain ⟨b, rfl⟩ := hπ y
      rw [MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top a),
        MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top b)]
    omega

theorem not_pair (hN : Nat.card ↥L = 211341312)
    (h : B42ModulePair L U Z) : False := by
  have hbig : 10000 < Nat.card ↥L := by omega
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact not_sl2 hN h
  · exact not_sl3 hN h
  · exact not_sp4 hN h
  · exact not_g2 hN h
  · exact not_g2d hN h
  · exact not_alternatingNatural1527d (by norm_num) (lt_of_lt_of_le (by decide) hbig.le) h
  · exact not_alternatingNatural1527d (by norm_num) (lt_of_lt_of_le (by decide) hbig.le) h
  · exact not_alternatingNatural1527d (by norm_num) (lt_of_lt_of_le (by decide) hbig.le) h
  · have h1 := Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four h
    omega
  · obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
    have h1 : Nat.card ↥L ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective π hπ.1
    have h2 : Nat.card ↥Γ₀ = 1080 :=
      card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        decide)
    omega
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact not_surj_sl (Or.inl rfl) hN π hπ.1
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact not_surj_sl (Or.inr rfl) hN π hπ.1
  · obtain ⟨π, hπ⟩ := h
    exact not_surj_sl (Or.inl rfl) hN π hπ.1
  · obtain ⟨π, hπ⟩ := h
    exact not_surj_sl (Or.inr rfl) hN π hπ.1

theorem not_part1 [Finite V] {H : Subgroup (MulAut V)} (h1 : B51Part1 H L)
    (hN : Nat.card ↥L = 211341312) : False := by
  obtain ⟨-, hc⟩ := h1
  rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
  · exact not_pair hN hi.2.1
  · obtain ⟨-, n, K, hF, hFin, hK, I, π, -, -, hreal, -⟩ := hii
    have hc := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hK] at hc
    exact sl3_ne hN hc.symm
  · obtain ⟨-, hn, π, U₁, U₂, -, hr1, -⟩ := hiii
    exact not_surj_sl hn hN π hr1.1
  · obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
    exact not_surj_sl hn hN π (hreal ⟨0, hk1⟩).1

end Models

end FF3D42

theorem thompsonJ_le_centralizer_of_is3D4
    (h51 : AsB51) {G : Type} [Group G] [Finite G] {K Q W : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hD4 : Is3D4 2 1 (O2Q K)) (hQS : IsSylowTwoOf Q (K ⊔ Q))
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hSQ : SQTKGroup ↥(K ⊔ Q))
    (hred : IsTwoReducedIn (K ⊔ Q) W) (hKW : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    thompsonJ Q ≤ Subgroup.centralizer (W : Set G) := by
  by_contra hJW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have := hWe.1
  have hYK : K ⊔ Q ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hQK
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hred.2.1
  have hY2 : ∀ y ∈ K ⊔ Q, ∃ e : ℕ, y ^ 2 ^ e ∈ K := InternalSec.two_of_sup hQS.2.1 hQK
  have hSQK : SQTKGroup ↥K := Vol2.Ch10.SecB.C11AmS.K8.sqtkGroup_of_le hSQ le_sup_left
  have hO2 : pCoreOf 2 (autOn (K ⊔ Q) W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2K : pCoreOf 2 (autOn K W) = ⊥ := pCoreOf_autOn_L_eq_bot1527d le_sup_left hYK hO2
  have hperf : Group.IsPerfect (O2Q K) := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
    exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hs : IsSimpleGroup (O2Q K) := D42.isSimpleGroup_of_perfect hD4
  have hN : Nat.card (O2Q K) = 211341312 := by
    rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD4]
    show ordTrialityD4 (2 ^ 1) = 211341312
    decide
  have hq : CFSG.IsQuasisimple (O2Q K) := isQuasisimple_of_isSimpleGroup_of_isPerfect
  have hqa : CFSG.IsQuasisimple ↥(autOn K W) := InternalSec.isQuasisimple_autOn hKN hq hO2K hKW
  have hle := InternalSec.pCore_le_ker_autOnHom hKN hO2K
  set ρ : O2Q K →* ↥(autOn K W) := QuotientGroup.lift _ (InternalSec.autOnHom hKN) hle with hρ
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hKN y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hρi : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hs.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      apply InternalSec.ker_autOnHom_ne_top hKN hKW
      rw [eq_top_iff]
      intro l _
      have h1 : ρ (QuotientGroup.mk l) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      exact h1
  have hQ : SQTKGroup (O2Q K) :=
    InternalSec.sqtkGroup_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup) hSQK
  have hSQa : SQTKGroup ↥(autOn K W) := by
    refine InternalSec.sqtkGroup_of_surjective ρ hρs ?_ hQ
    rw [(MonoidHom.ker_eq_bot_iff ρ).2 hρi]
    exact IsPGroup.of_bot
  have hNa : Nat.card ↥(autOn K W) = 211341312 := by
    rw [← Nat.card_congr (Equiv.ofBijective ρ ⟨hρi, hρs⟩)]
    exact hN
  obtain ⟨A, -, hA, hLA⟩ :=
    Vol2.Ch10.SecC.C10KH.exists_offender_of_thompsonJ hWe hred hQS hYK hY2 hqa hJW
  have h2 : ∀ y ∈ K ⊔ Q, ∃ e : ℕ, y ^ 2 ^ e ∈ K ⊔ Subgroup.centralizer (W : Set G) :=
    fun y hy => by
      obtain ⟨e, he⟩ := hY2 y hy
      exact ⟨e, Subgroup.mem_sup_left he⟩
  have hB := (InternalSec.b51Hyp_ffJ_autOn hred.2.1 le_sup_left hYK h2 hO2 hqa hSQa hA hLA).1
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  obtain ⟨hP1, -, -⟩ := h51 ↥W hV2 _ _ hB
  exact FF3D42.not_part1 hP1 hNa

end CFSG.Quasithin.H13
