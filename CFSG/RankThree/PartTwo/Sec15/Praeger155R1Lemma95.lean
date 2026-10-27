module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.GroupTheory.HuppertProduct.Quotient

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof1515
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma95KQuotient (K : Subgroup G) : Prop :=
  Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))

theorem eq_bot_of_normal_isPGroup_two_alternatingGroup_seven
    {Q : Subgroup (alternatingGroup (Fin 7))} [Q.Normal] (hQ : IsPGroup 2 Q) : Q = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  rcases Subgroup.Normal.eq_bot_or_eq_top Q with h | h
  · exact h
  · exfalso
    have h2 : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 7))) := h ▸ hQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
      KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
    rw [Subgroup.card_top, hc] at hn
    have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn]; norm_num
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem le_normalizer_of_mem_scriptY0Star_of_a7 {A : Subgroup G} {c : G} {L K : Subgroup G}
    (h : Sec15R G A c L)
    (hL7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hK : K ∈ scriptY0Star A (lB A))
    (hcover : K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K)
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h142 : Concl142 A (lB A))
    (h135 : Item135) (hKbar : Lemma95KQuotient K) :
    L ≤ Subgroup.normalizer (K : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Subgroup.zpowers c ∈ omegaA A := h.zpowers_mem_omegaA
  have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  set H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set X : Subgroup G :=
    oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (K : Set G))) with hX
  have hK4 : K ∈ scriptY4 A (lB A) := hK.prop.1
  have hbot : (⊥ : Subgroup G) ∈
      scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  have hSG : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := ((h153 K hK).2.1 S hS).1
  have hSle : S ≤ Subgroup.normalizer (K : Set G) := hobs K hK S hS
  have hSH : S ⊓ H ∈ scriptQPiStar A (lB A) H (piOf 2) :=
    inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hWH h1411 hSG
  have hLH : L ≤ H :=
    (le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1).trans
      (centralizer_singleton_le_normalizer_zpowers c)
  have hVLleL : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have h3L : 3 ∣ Nat.card L := by
    obtain ⟨φ⟩ := hL7
    exact three_dvd_card_of_mulEquiv φ (by rw [hcard7]; norm_num)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3L
  have hVLleH : CFSG.Open.pCoreOf 2 L ≤ H := hVLleL.trans hLH
  have hHVVL : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hHL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAVL : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    h.mem_lA.2.1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAVS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hc).1
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (h.toSec13Data.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hAH : A ≤ H := hAc.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hVL2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hSH2 : IsPGroup 2 ↥(S ⊓ H) :=
    isPGroup_of_mem_scriptQPi Nat.prime_two hSH.prop
  have hO2S : CFSG.Open.pCoreOf 2 L ≤ S := by
    have hT2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) :=
      IsPGroup.to_sup_of_normal_left' hVL2 hSH2 (inf_le_right.trans hHVVL)
    have hTH : CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H) ≤ H := sup_le hVLleH inf_le_right
    have hAT : A ≤ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H) : Subgroup G) : Set G) :=
      CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hAVL
        (Late.le_normalizer_inf hAVS (hAH.trans Subgroup.le_normalizer))
    have hT3' : IsPiSubgroup (piCompl 3) (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) := by
      rw [isPiSubgroup_piCompl_iff Nat.prime_three]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
      rw [hn]
      intro h3
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
    have hTQ : (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) ∈ scriptQ A (lB A) := by
      obtain ⟨Q, hQ, hTle⟩ := exists_le_mem_maxInvariantPiSubgroups
        (H := H) (A := A) (π := piCompl 3) ⟨hTH, hT3', hAT⟩
      exact mem_scriptQ_of_le (h142 c hc Q hQ).1 hTle hAT
    have hTqpi : (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) ∈
        scriptQPi A (lB A) H (piOf 2) :=
      ⟨⟨hTQ, hTH⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hT2⟩
    have heq : (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) = S ⊓ H :=
      le_antisymm (hSH.2 hTqpi le_sup_right) le_sup_right
    exact (le_sup_left.trans heq.le).trans inf_le_left
  set R : Subgroup G := L ⊓ K with hRdef
  set VK : Subgroup G := CFSG.Open.pCoreOf 2 K with hVKdef
  set VL : Subgroup G := CFSG.Open.pCoreOf 2 L with hVLdef
  set Z1 : Subgroup G := R ⊓ VK with hZ1def
  set Z2 : Subgroup G := R ⊓ VL with hZ2def
  have hRK : R ≤ K := inf_le_right
  have hRL : R ≤ L := inf_le_left
  have hRLK : L ⊓ K = R := rfl
  have hRVK : R ≤ Subgroup.normalizer (VK : Set G) :=
    hRK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hRVL : R ≤ Subgroup.normalizer (VL : Set G) :=
    hRL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hsupK : R ⊔ VK = K := hcover.symm
  have hVKleK : VK ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hLVL : L ≤ Subgroup.normalizer (VL : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hcardVK : Nat.card ↥(CFSG.pCore 2 ↥K) = Nat.card ↥VK := by
    rw [hVKdef, CFSG.Open.pCoreOf, CFSG.Open.pCore_eq_pCore]
    exact (Subgroup.card_map_of_injective K.subtype_injective).symm
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    theta_eq_pCore_two_of_multFree
      (h135 G A c L h.toSec13Data h.hypS_or_hypT) hL7 multFree_alternatingGroup_seven
  have hcardVL : Nat.card ↥(aschbacherSolvableCore 3 ↥L) = Nat.card ↥VL := by
    rw [hθ, hVLdef, CFSG.Open.pCoreOf, CFSG.Open.pCore_eq_pCore]
    exact (Subgroup.card_map_of_injective L.subtype_injective).symm
  have hKcard : Nat.card ↥K = 2520 * Nat.card ↥VK := by
    obtain ⟨e⟩ := hKbar
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    rw [Nat.card_congr e.toEquiv, hcard7, hcardVK] at h1
    exact h1
  have hLcard : Nat.card ↥L = 2520 * Nat.card ↥VL := by
    obtain ⟨e⟩ := hL7
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)
    rw [Nat.card_congr e.toEquiv, hcard7, hcardVL] at h1
    exact h1
  have hZ2sub : IsPGroup 2 ↥(Z2.subgroupOf R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L).to_le (inf_le_right : Z2 ≤ VL))
    refine IsPGroup.iff_card.mpr ⟨n, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z2 ≤ R)).toEquiv, hn]
  have hZ2Z1 : Z2 ≤ Z1 := by
    obtain ⟨e⟩ := hKbar
    set f : ↥R →* alternatingGroup (Fin 7) :=
      e.toMonoidHom.comp
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hRK)) with hf
    have hVKmap : VK = (CFSG.pCore 2 ↥K).map K.subtype := by
      rw [hVKdef, CFSG.Open.pCoreOf, CFSG.Open.pCore_eq_pCore]
    have hmemV : ∀ y : ↥K, (y : G) ∈ VK ↔ y ∈ CFSG.pCore 2 ↥K := by
      intro y
      rw [hVKmap, Subgroup.mem_map]
      exact ⟨fun ⟨z, hz, hzy⟩ => (show z = y from Subtype.ext hzy) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩
    have hsurjπ : Function.Surjective (fun x : ↥R =>
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) (Subgroup.inclusion hRK x)) := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
      have hxK : (x : G) ∈ R ⊔ VK := by rw [hsupK]; exact x.2
      have hx : (x : G) ∈ (R : Set G) * (VK : Set G) := by
        rwa [← Subgroup.coe_mul_of_left_le_normalizer_right R VK hRVK]
      obtain ⟨r, hr, v, hv, hrv⟩ := Set.mem_mul.mp hx
      refine ⟨⟨r, hr⟩, ?_⟩
      have hval : ((Subgroup.inclusion hRK ⟨r, hr⟩ * x⁻¹ : ↥K) : G) = r * v⁻¹ * r⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        have h1 : ((Subgroup.inclusion hRK ⟨r, hr⟩ : ↥K) : G) = r := rfl
        rw [h1, show (x : G) = r * v from hrv.symm]
        group
      have hmem : ((Subgroup.inclusion hRK ⟨r, hr⟩ * x⁻¹ : ↥K) : G) ∈ VK := by
        rw [hval]
        exact (Subgroup.mem_normalizer_iff.mp (hRVK hr) v⁻¹).mp (inv_mem hv)
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K)
          (Subgroup.inclusion hRK ⟨r, hr⟩ * x⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ((hmemV _).mp hmem)
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨z, hz⟩ := e.surjective y
      obtain ⟨x, hx⟩ := hsurjπ z
      have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (Subgroup.inclusion hRK x) = z := hx
      refine ⟨x, ?_⟩
      show e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (Subgroup.inclusion hRK x)) = y
      rw [hx', hz]
    have hZ2eq : Z2.subgroupOf R = VL.subgroupOf R := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    have hVLsub_eq : VL.subgroupOf R = (VL.subgroupOf L).comap (Subgroup.inclusion hRL) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rfl
    have hVLsub : (VL.subgroupOf R).Normal := by
      rw [hVLsub_eq]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVLleL).mpr hLVL |>.comap _
    have hZ2n : (Z2.subgroupOf R).Normal := hZ2eq ▸ hVLsub
    have hPn : ((Z2.subgroupOf R).map f).Normal :=
      hZ2n.map f hfsurj
    have hPp : IsPGroup 2 ((Z2.subgroupOf R).map f) := hZ2sub.map f
    have hPbot : (Z2.subgroupOf R).map f = ⊥ :=
      eq_bot_of_normal_isPGroup_two_alternatingGroup_seven hPp
    have hker : Z2.subgroupOf R ≤ f.ker :=
      (Subgroup.map_eq_bot_iff (Z2.subgroupOf R) (f := f)).mp hPbot
    intro y hy
    have hyR : y ∈ R := hy.1
    have hy' : (⟨y, hyR⟩ : ↥R) ∈ Z2.subgroupOf R := by
      rw [Subgroup.mem_subgroupOf, hZ2def]
      exact ⟨hyR, hy.2⟩
    have h1 : f ⟨y, hyR⟩ = 1 := hker hy'
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (Subgroup.inclusion hRK ⟨y, hyR⟩) = 1 := by
      have h3 : e (QuotientGroup.mk' (CFSG.pCore 2 ↥K)
          (Subgroup.inclusion hRK ⟨y, hyR⟩)) = 1 := h1
      exact e.map_eq_one_iff.mp h3
    have h2' : Subgroup.inclusion hRK ⟨y, hyR⟩ ∈ CFSG.pCore 2 ↥K :=
      (QuotientGroup.eq_one_iff _).mp h2
    refine ⟨hyR, ?_⟩
    have h4 : ((Subgroup.inclusion hRK ⟨y, hyR⟩ : ↥K) : G) ∈ VK := (hmemV _).mpr h2'
    rwa [show ((Subgroup.inclusion hRK ⟨y, hyR⟩ : ↥K) : G) = y from rfl] at h4
  have hcard1 : Nat.card ↥R * Nat.card ↥VK = Nat.card ↥K * Nat.card ↥Z1 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := R) (K := VK) hRVK
    rw [hsupK, ← hZ1def] at h
    exact h.symm
  have hRcard : Nat.card ↥R * Nat.card ↥VK = (2520 * Nat.card ↥Z1) * Nat.card ↥VK := by
    rw [hcard1, hKcard]
    ring
  have hcard2 : Nat.card ↥(R ⊔ VL) * Nat.card ↥Z2 = Nat.card ↥R * Nat.card ↥VL := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := R) (K := VL) hRVL
    rw [← hZ2def] at h
    exact h
  have hfinal : Nat.card ↥(R ⊔ VL) * Nat.card ↥Z2 * Nat.card ↥VK =
      Nat.card ↥L * Nat.card ↥Z1 * Nat.card ↥VK := by
    rw [hcard2, hLcard]
    calc Nat.card ↥R * Nat.card ↥VL * Nat.card ↥VK
        = (Nat.card ↥R * Nat.card ↥VK) * Nat.card ↥VL := by ring
      _ = ((2520 * Nat.card ↥Z1) * Nat.card ↥VK) * Nat.card ↥VL := by rw [hRcard]
      _ = (2520 * Nat.card ↥VL) * Nat.card ↥Z1 * Nat.card ↥VK := by ring
  have hZle : Nat.card ↥Z2 ≤ Nat.card ↥Z1 :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hZ2Z1)
  have hle : R ⊔ VL ≤ L := sup_le hRL hVLleL
  have hkey : Nat.card ↥L ≤ Nat.card ↥(R ⊔ VL) := by
    have h1 : Nat.card ↥L * Nat.card ↥Z2 * Nat.card ↥VK ≤
        Nat.card ↥L * Nat.card ↥Z1 * Nat.card ↥VK :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZle)
    rw [← hfinal] at h1
    have h2 : Nat.card ↥L * Nat.card ↥Z2 ≤ Nat.card ↥(R ⊔ VL) * Nat.card ↥Z2 :=
      Nat.le_of_mul_le_mul_right h1 Nat.card_pos
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have hLsplit : L = R ⊔ VL :=
    (Subgroup.eq_of_le_of_card_ge hle hkey).symm
  rw [hLsplit]
  refine sup_le (inf_le_right.trans Subgroup.le_normalizer) ?_
  exact hO2S.trans hSle


theorem oTwo_le_of_mem_scriptQPiStar {A : Subgroup G} {c : G} {L K : Subgroup G}
    (h : Sec15R G A c L) (hK : K ∈ scriptY0Star A (lB A))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h142 : Concl142 A (lB A)) (h135 : Item135)
    (h3L : 3 ∣ Nat.card L) :
    ∀ S : Subgroup G, Maximal (fun T : Subgroup G =>
        T ∈ scriptQPi A (lB A)
          (Subgroup.normalizer (oPrimeResidualOf 3
            (delta A (lB A) (Subgroup.normalizer (K : Set G))) : Set G)) (piOf 2)) S →
      CFSG.Open.pCoreOf 2 L ≤ S ∧ S ≤ Subgroup.normalizer (K : Set G) := by
  classical
  intro S hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Subgroup.zpowers c ∈ omegaA A := h.zpowers_mem_omegaA
  set H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hK4 : K ∈ scriptY4 A (lB A) := hK.prop.1
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Subgroup.zpowers c ∈ omegaA A := h.zpowers_mem_omegaA
  have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  set H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hK4 : K ∈ scriptY4 A (lB A) := hK.prop.1
  have hSG : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := ((h153 K hK).2.1 S hS).1
  have hSle : S ≤ Subgroup.normalizer (K : Set G) := hobs K hK S hS
  have hSH : S ⊓ H ∈ scriptQPiStar A (lB A) H (piOf 2) :=
    inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hWH h1411 hSG
  have hLH : L ≤ H :=
    (le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1).trans
      (centralizer_singleton_le_normalizer_zpowers c)
  have hVLleL : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3L
  have hVLleH : CFSG.Open.pCoreOf 2 L ≤ H := hVLleL.trans hLH
  have hHVVL : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hHL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAVL : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    h.mem_lA.2.1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAVS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hc).1
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (h.toSec13Data.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hAH : A ≤ H := hAc.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hVL2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hSH2 : IsPGroup 2 ↥(S ⊓ H) :=
    isPGroup_of_mem_scriptQPi Nat.prime_two hSH.prop
  have hO2S : CFSG.Open.pCoreOf 2 L ≤ S := by
    have hT2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) :=
      IsPGroup.to_sup_of_normal_left' hVL2 hSH2 (inf_le_right.trans hHVVL)
    have hTH : CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H) ≤ H := sup_le hVLleH inf_le_right
    have hAT : A ≤ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H) : Subgroup G) : Set G) :=
      CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hAVL
        (Late.le_normalizer_inf hAVS (hAH.trans Subgroup.le_normalizer))
    have hT3' : IsPiSubgroup (piCompl 3) (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) := by
      rw [isPiSubgroup_piCompl_iff Nat.prime_three]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
      rw [hn]
      intro h3
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
    have hTQ : (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) ∈ scriptQ A (lB A) := by
      obtain ⟨Q, hQ, hTle⟩ := exists_le_mem_maxInvariantPiSubgroups
        (H := H) (A := A) (π := piCompl 3) ⟨hTH, hT3', hAT⟩
      exact mem_scriptQ_of_le (h142 c hc Q hQ).1 hTle hAT
    have hTqpi : (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) ∈
        scriptQPi A (lB A) H (piOf 2) :=
      ⟨⟨hTQ, hTH⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hT2⟩
    have heq : (CFSG.Open.pCoreOf 2 L ⊔ (S ⊓ H)) = S ⊓ H :=
      le_antisymm (hSH.2 hTqpi le_sup_right) le_sup_right
    exact (le_sup_left.trans heq.le).trans inf_le_left
  exact ⟨hO2S, hSle⟩


theorem pCoreOf_two_le_normalizer_of_mem_scriptY0Star {A : Subgroup G} {c : G} {L K : Subgroup G}
    (h : Sec15R G A c L) (hK : K ∈ scriptY0Star A (lB A))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h142 : Concl142 A (lB A)) (h135 : Item135)
    (h3L : 3 ∣ Nat.card L) :
    CFSG.Open.pCoreOf 2 L ≤ Subgroup.normalizer (K : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : (⊥ : Subgroup G) ∈
      scriptQPi A (lB A)
        (Subgroup.normalizer (oPrimeResidualOf 3
          (delta A (lB A) (Subgroup.normalizer (K : Set G))) : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A)
      (Subgroup.normalizer (oPrimeResidualOf 3
        (delta A (lB A) (Subgroup.normalizer (K : Set G))) : Set G)) (piOf 2))) hbot
  exact (oTwo_le_of_mem_scriptQPiStar h hK hWH h153 hobs h1411 h142 h135 h3L S hS).1.trans
    (oTwo_le_of_mem_scriptQPiStar h hK hWH h153 hobs h1411 h142 h135 h3L S hS).2

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

