module

public import CFSG.Quasithin.Vol2.Ch9KGFFG2Model
public import CFSG.Quasithin.Vol2.Ch9KGFFB51

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Explicit
open Vol2.Ch10.SecB.C11AmS
open scoped IsMulCommutative Matrix

section Num

theorem sl2_ne_g24 (n : ℕ) : (2 ^ n) * ((2 ^ n) ^ 2 - 1) ≠ 251596800 := by
  intro h
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 1024 ≤ 2 ^ n := by
      calc 1024 = 2 ^ 10 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 1024 * (1024 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega

theorem sp4_ne_g24 (n : ℕ) :
    (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) ≠ 251596800 := by
  intro h
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 8 ^ (2 ^ 2) * (((8 ^ 2 - 1)) * (8 ^ 4 - 1)) ≤
        (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq _)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1))
    omega

theorem eq_two_of_g2_eq_g24 (n : ℕ)
    (h : (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) = 251596800) : n = 2 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · norm_num at h
    · norm_num at h
    · rfl
  · exfalso
    have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 8 ^ 6 * ((8 ^ 6 - 1) * (8 ^ 2 - 1)) ≤
        (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    omega

theorem card_quasithinG2_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card ↥(CFSG.Open.quasithinG2 F) = 251596800 := by
  rw [card_quasithinG2_1527d (n := 2) (by rw [hF]; norm_num), hF]
  norm_num

end Num

section Part2

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

theorem natural_of_card_g24 [Finite V] (h2 : B51Part2 L) (hN : Nat.card ↥L = 251596800)
    (hnd : ¬ IsIntDirect (commV L) (fixV L) ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      ∃ π : ↥(CFSG.Open.quasithinG2 F) →* ↥L,
        (FFModel.zornQ (CFSG.Open.quasithinG2 F)).RealizesVia L (commV L)
          (fixV L ⊓ commV L) π := by
  have hl := (h2.2 hnd).2
  rcases hl with ⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ |
    h | h | ⟨F, _, _, hF, π, hπ⟩ | ⟨F, _, _, hF, π, hπ⟩
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hF, hN] at hc
    exact absurd hc.symm (sl2_ne_g24 n)
  · have hc := card_eq_of_nat_realizes1527d hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF, hN, hI,
      Finset.prod_pair (by norm_num)] at hc
    exact absurd hc.symm (sp4_ne_g24 n)
  · have := FFC.charP_two_of_card_pow hF
    have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) :=
      (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hF, hF, hN] at hcard
    have hn := eq_two_of_g2_eq_g24 n hcard.symm
    subst hn
    exact ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num, π, hπ⟩
  · exact (not_alternatingNatural1527d (n := 6) (by norm_num) (by rw [hN]; decide) h).elim
  · obtain ⟨π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
    have hc : Nat.card ↥(alternatingGroup (Fin 8)) = Nat.card ↥L :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
    rw [card_alternatingGroup1527d 8 (by norm_num), hN] at hc
    exact absurd hc (by decide)
  · have hG2 := card_quasithinG2_1527d hF
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
    rw [hG2, hN] at h3
    norm_num at h3
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hF, hN] at hc
    exact absurd hc (by norm_num)

end Part2

theorem notB56Factor_of_card_g24 {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}
    (hcardK : Nat.card ↥K = 251596800)
    (hK4 : ¬ CFSG.QuasithinUnique.L246C127.NoOrderFour ↥K) :
    InternalSec.NotB56Factor K := by
  intro X hKX _ hX
  have hX4 : ¬ CFSG.QuasithinUnique.L246C127.NoOrderFour ↥X := fun h => hK4
    ((FFD.noOrderFour_subgroup h (K.subgroupOf X)).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKX).symm)
  have hfinK : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hcardK]; norm_num)
  rcases hX with (⟨n, F, _, _, -, hF, he⟩ | he | ⟨m, F, _, _, -, hmo, hF, he⟩) | he | he |
      ⟨n, F, _, _, hF, π, hπ⟩
  · obtain ⟨e⟩ := he
    have := Fintype.ofFinite F
    have : CharP F 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    exact hX4 (FFD.noOrderFour_of_surjective e.symm.toMonoidHom e.symm.surjective)
  · obtain ⟨e⟩ := he
    have hdvd : 251596800 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e⟩ := he
    have hdvd : 251596800 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    have h5 : 5 ∣ Nat.card ↥X := (by norm_num : 5 ∣ 251596800).trans hdvd
    rw [Nat.card_congr e.toEquiv] at h5
    exact FFD.not_five_dvd_card_sl3 hmo hF h5
  · obtain ⟨e⟩ := he
    have hdvd : 251596800 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e⟩ := he
    have hdvd : 251596800 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three,
      Nat.card_zmod] at hdvd
    exact absurd hdvd (by decide)
  · have := Fintype.ofFinite F
    have : CharP F 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    exact hX4 (FFD.noOrderFour_of_surjective π hπ)

section OrderFour

open CFSG.Quasithin.JonesParshall

variable {F : Type} [Field F]

theorem g2A_injective' : Function.Injective (g2A : SL3 F →* ↥(cayleyGroup F)) := by
  intro A B h
  have hu : ∀ u : Fin 3 → F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ u =
      (B : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
    intro u
    have h1 := congrArg (fun g : ↥(cayleyGroup F) =>
      (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ((0 : F), u, (0 : Fin 3 → F), (0 : F))) h
    simp only [g2A_apply, gAFun] at h1
    exact congrArg (fun x : quasithinZorn F => x.2.1) h1
  exact Subtype.ext (Matrix.ext_iff_mulVec.mpr hu)

theorem not_noOrderFour_cayley [CharP F 2] :
    ¬ CFSG.QuasithinUnique.L246C127.NoOrderFour ↥(cayleyGroup F) := by
  intro h
  apply not_noOrderFour_sl3_charTwo (F := F)
  intro g hg
  apply g2A_injective'
  rw [map_pow, map_one]
  exact h _ (by rw [← map_pow, hg, map_one])

end OrderFour

section G24

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.QuasithinUnique.Setup.X6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem g24_facts
    {Y KY U : Subgroup G} (hKYc : KY ∈ cComp Y)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hqKY : CFSG.IsQuasisimple (O2Q KY)) (hqA : CFSG.IsQuasisimple ↥(autOn KY U))
    (hG2 : IsG2 2 2 (O2Q KY)) :
    IsPGroup 2 ↥(KY ⊓ Subgroup.centralizer (U : Set G)) ∧
      Nat.card ↥(autOn KY U) = 251596800 ∧
      ¬ CFSG.QuasithinUnique.L246C127.NoOrderFour ↥(autOn KY U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYU : Y ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hYU
  have hO2 : pCoreOf 2 (autOn Y U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hle : autOn KY U ≤ autOn Y U := InternalSec.autOn_le_autOn_of_le hKYY
  have hn : ((autOn KY U).subgroupOf (autOn Y U)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hle).mpr fun k a hk ha => ?_
    exact InternalSec.autOn_normal_of (U := U) hYKY a ha k hk
  have hO2KY : pCoreOf 2 (autOn KY U) = ⊥ := by
    have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hle hn
    rw [hO2] at h
    exact le_bot_iff.1 h
  set π : O2Q KY →* ↥(autOn KY U) := QuotientGroup.lift (CFSG.pCore 2 ↥KY)
    (InternalSec.autOnHom hKYN) (InternalSec.pCore_le_ker_autOnHom hKYN hO2KY) with hπdef
  have hπs : Function.Surjective π :=
    QuotientGroup.lift_surjective_of_surjective _ _ (InternalSec.autOnHom_surjective hKYN) _
  have hπne : π.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hqA
    obtain ⟨x, rfl⟩ := hπs a
    obtain ⟨y, rfl⟩ := hπs b
    have hx : x ∈ π.ker := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ π.ker := by rw [htop]; exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy] at hab
    exact hab rfl
  obtain ⟨hf, F', _, _, _, hF', ⟨e3⟩⟩ := exists_mulEquiv_G2_model hG2
  have hZ : Subgroup.center (O2Q KY) = ⊥ := by
    have h1 := Subgroup.map_center_eq e3
    rw [center_adjointGroup_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e3.injective).mp h1
  have hπZ : π.ker ≤ Subgroup.center (O2Q KY) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqKY inferInstance).resolve_left hπne
  have hπi : π.ker = ⊥ := le_bot_iff.mp (hZ ▸ hπZ)
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hπi
  set eA : O2Q KY ≃* ↥(autOn KY U) := MulEquiv.ofBijective π ⟨hπinj, hπs⟩ with heA
  obtain ⟨ψ, -⟩ := G2M.exists_psiEquiv (F := F') hF' (le_refl 2)
  set eS : ↥(cayleyGroup F') ≃* ↥(autOn KY U) := ψ.symm.trans (e3.symm.trans eA) with heS
  have hcard : Nat.card ↥(autOn KY U) = 251596800 := by
    rw [← Nat.card_congr eS.toEquiv,
      ← CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      card_quasithinG2_four (by rw [hF']; norm_num)]
  have h4 : ¬ CFSG.QuasithinUnique.L246C127.NoOrderFour ↥(autOn KY U) := fun h =>
    not_noOrderFour_cayley (F := F') (h.of_mulEquiv eS)
  have hker : IsPGroup 2 ↥(KY ⊓ Subgroup.centralizer (U : Set G)) := by
    intro x
    have hx1 : (⟨(x : G), x.2.1⟩ : ↥KY) ∈ (InternalSec.autOnHom hKYN).ker :=
      (InternalSec.mem_ker_autOnHom hKYN _).2 x.2.2
    have hx2 : (QuotientGroup.mk ⟨(x : G), x.2.1⟩ : O2Q KY) ∈ π.ker := by
      rw [MonoidHom.mem_ker, hπdef, QuotientGroup.lift_mk]
      exact hx1
    rw [hπi, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hx2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥KY)) ⟨_, hx2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (⟨(x : G), x.2.1⟩ : ↥KY) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val h1
    simpa using h2
  exact ⟨hker, hcard, h4⟩

theorem isIntDirect_or_natural_of_g24
    (h51 : AsB51) (h56 : AsB56) {Y T KY U : Subgroup G}
    [IsMulCommutative ↥U] (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKYc : KY ∈ cComp Y)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hqKY : CFSG.IsQuasisimple (O2Q KY)) (hqA : CFSG.IsQuasisimple ↥(autOn KY U))
    (hG2 : IsG2 2 2 (O2Q KY)) :
    IsIntDirect (commV (autOn KY U)) (fixV (autOn KY U)) ⊤ ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        ∃ π : ↥(CFSG.Open.quasithinG2 F) →* ↥(autOn KY U),
          (FFModel.zornQ (CFSG.Open.quasithinG2 F)).RealizesVia (autOn KY U)
            (commV (autOn KY U)) (fixV (autOn KY U) ⊓ commV (autOn KY U)) π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 U := hred.2.2.1
  have hYU : Y ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hYU
  have hO2 : pCoreOf 2 (autOn Y U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  obtain ⟨hker, hcard, h4⟩ := g24_facts hKYc hYKY hred hqKY hqA hG2
  have hSA : SQTKGroup ↥(autOn KY U) :=
    InternalSec.sqtkGroup_autOn hKYN (K8.sqtkGroup_of_le hSQ hKYY) hker
  obtain ⟨A, -, hA, hLA⟩ := FFD.exists_offender_of_commutator hVe hred hT hKYY hYKY hqA le_rfl hJ
  have hV2 : ∀ w ∈ U, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hVe.2 w hw
  obtain ⟨hB, -⟩ := InternalSec.b51Hyp_ffJ_autOn_of_b56_of_notFactor h56 hV2 hYU hKYY hYKY
    hSQ hO2 hqA hSA hA hLA (notB56Factor_of_card_g24 hcard h4)
  have hV2' : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  obtain ⟨-, hP2, -⟩ := h51 ↥U hV2' _ _ hB
  by_cases hdir : IsIntDirect (commV (autOn KY U)) (fixV (autOn KY U)) ⊤
  · exact Or.inl hdir
  · exact Or.inr (natural_of_card_g24 hP2 hcard hdir)

end G24

end CFSG.Quasithin.H13.Ch9.KGFF
