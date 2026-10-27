module

public import CFSG.RankThree.PartTwo.Sec17.C174Five
public import CFSG.RankThree.PartTwo.Sec17.C174Case
public import CFSG.RankThree.PartTwo.Sec14.Item148StepsNHJ
public import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1421
public import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
public import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem isPiSubgroup_piOf_two_of_isPGroup {H : Subgroup G} (hH : IsPGroup 2 H) :
    IsPiSubgroup (piOf 2) H := by
  intro p hp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  rw [hn] at hp
  have h2 : (p : ℕ) ∣ 2 := p.2.dvd_of_dvd_pow hp
  exact (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp h2

theorem pPrimeCoreOf_three_le (K : Subgroup G) : pPrimeCoreOf 3 K ≤ K :=
  Subgroup.map_subtype_le _

theorem not_three_dvd_of_oPrimeResidualOf_eq_bot {Y : Subgroup G}
    (hY : oPrimeResidualOf 3 Y = ⊥) : ¬ 3 ∣ Nat.card Y := by
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 h3
  have hmem : (x : G) ∈ oPrimeResidualOf 3 Y := by
    rw [oPrimeResidualOf_eq_closure]
    apply Subgroup.subset_closure
    refine ⟨x.2, 1, ?_⟩
    have h1 : x ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have h2 : (x : G) ^ 3 = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    simpa using h2
  rw [hY, Subgroup.mem_bot] at hmem
  have hx1 : x = 1 := Subtype.ext (by simpa using hmem)
  rw [hx1, orderOf_one] at hx
  norm_num at hx

theorem conj_mem_pCoreOf {Z : Subgroup G} {z r : G} (hz : z ∈ Z)
    (hr : r ∈ CFSG.Open.pCoreOf 2 Z) : z * r * z⁻¹ ∈ CFSG.Open.pCoreOf 2 Z := by
  rw [CFSG.openPCoreOf_eq_map_pCore] at hr ⊢
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hr
  have hn : (CFSG.pCore 2 Z).Normal := CFSG.pCore_normal
  exact Subgroup.mem_map.mpr ⟨(⟨z, hz⟩ : Z) * p * (⟨z, hz⟩ : Z)⁻¹, hn.conj_mem p hp _, rfl⟩

theorem commutator_pCoreOf_le (Z : Subgroup G) :
    ⁅CFSG.Open.pCoreOf 2 Z, Z⁆ ≤ CFSG.Open.pCoreOf 2 Z := by
  rw [Subgroup.commutator_le]
  intro r hr z hz
  rw [commutatorElement_def]
  have h1 := conj_mem_pCoreOf hz ((CFSG.Open.pCoreOf 2 Z).inv_mem hr)
  have h2 := (CFSG.Open.pCoreOf 2 Z).mul_mem hr h1
  convert h2 using 1
  group

theorem le_centralizer_of_piOf_two (h1411 : Item1411_1 A (lB A)) {T U : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hTC : T ≤ Subgroup.centralizer (A : Set G))
    (hU : U ∈ scriptQPi A (lB A) ⊤ (piOf 2)) : U ≤ Subgroup.centralizer (A : Set G) := by
  obtain ⟨T'', hT'', hUT''⟩ := Sec14.Proof1413.exists_scriptQPiStar_top hU
  obtain ⟨w, hw, hT''eq⟩ := h1411 T hT T'' hT''
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  intro x hx
  rw [hT''eq] at hUT''
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp (hUT'' hx)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : w⁻¹ * a * w⁻¹⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set G)).inv_mem hwN) a).mp ha
  have key := Subgroup.mem_centralizer_iff.mp (hTC ht) _ ha'
  show a * (w * t * w⁻¹) = w * t * w⁻¹ * a
  calc a * (w * t * w⁻¹) = w * (w⁻¹ * a * w⁻¹⁻¹ * t) * w⁻¹ := by group
    _ = w * (t * (w⁻¹ * a * w⁻¹⁻¹)) * w⁻¹ := by rw [key]
    _ = w * t * w⁻¹ * a := by group

theorem eq_bot_of_structure {Z : Subgroup G} (hZA : Z = ⁅Z, A⁆)
    (hF : generalizedFitting ↥Z = CFSG.pCore 2 ↥Z)
    (hRC : CFSG.Open.pCoreOf 2 Z ≤ Subgroup.centralizer (A : Set G)) : Z = ⊥ := by
  have hRA : ⁅CFSG.Open.pCoreOf 2 Z, A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRC
  have hAR : ⁅A, CFSG.Open.pCoreOf 2 Z⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hRA
  have h1 : ⁅⁅A, CFSG.Open.pCoreOf 2 Z⁆, Z⁆ = ⊥ := by
    rw [hAR, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅CFSG.Open.pCoreOf 2 Z, Z⁆, A⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono (commutator_pCoreOf_le Z) le_rfl).trans hRA.le)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [← hZA] at h3
  have hZR : Z ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Z : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hZR' : Z ≤ CFSG.Open.pCoreOf 2 Z := by
    intro z hz
    have hxc : (⟨z, hz⟩ : Z) ∈ Subgroup.centralizer (generalizedFitting ↥Z : Set ↥Z) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [hF] at hk
      apply Subtype.ext
      have hkR : (k : G) ∈ CFSG.Open.pCoreOf 2 Z := (CFSG.mem_openPCoreOf_iff k).mpr hk
      exact Subgroup.mem_centralizer_iff.mp (hZR hz) (k : G) hkR
    have hx : (⟨z, hz⟩ : Z) ∈ generalizedFitting ↥Z := centralizer_generalizedFitting_le ↥Z hxc
    rw [hF] at hx
    exact (CFSG.mem_openPCoreOf_iff (⟨z, hz⟩ : Z)).mpr hx
  have hZA_bot : ⁅Z, A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hZR'.trans hRC)
  exact hZA.trans hZA_bot

theorem pCoreOf_mem_scriptQPi {Y Z : Subgroup G} (hYQ : Y ∈ scriptQ A (lB A))
    (hZY : Z ≤ Y) (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) :
    CFSG.Open.pCoreOf 2 Z ∈ scriptQPi A (lB A) ⊤ (piOf 2) := by
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Z) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Z
  have hRQ : CFSG.Open.pCoreOf 2 Z ∈ scriptQ A (lB A) :=
    Sec14.mem_scriptQ_of_le hYQ ((CFSG.openPCoreOf_le 2 Z).trans hZY)
      (hAZ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Z))
  exact ⟨⟨hRQ, le_top⟩, isPiSubgroup_piOf_two_of_isPGroup hR2⟩

theorem deltaZero_cQuot_sup_ne_bot (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h1411 : Item1411_1 A (lB A))
    (h167 : Item167 A (lB A) c L) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) (hYM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)) :
    deltaZero A (lB A) (cQuot Y₀ ⊔ T) ≠ ⊥ := by
  intro hne
  have hA : IsE27 A := Sec17Std.isE27 h
  have hdY' := (Sec14.rank3II_14_5_lB hA hbot (mem_scriptY_cQuot_sup h hT).2).1
  rw [hne, bot_sup_eq] at hdY'
  have hTQ : T ∈ scriptQ A (lB A) := hT.1.1.1
  have hTC : T ≤ Subgroup.centralizer (A : Set G) :=
    (Sec14.le_delta hTQ le_sup_right).trans
      ((hdY'.le.trans inf_le_left).trans (pPrimeCoreOf_three_le _))
  have hY1 : Y ∈ scriptY1 A (lB A) := hY.1
  have hY3 : Y ∈ scriptY3 A (lB A) := hY1.1
  have hYres : oPrimeResidualOf 3 Y = ⊥ := hY1.2
  have hYΔ : Y = delta A (lB A) Y := hY3.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hYQ : Y ∈ scriptQ A (lB A) :=
    Sec16.Proof165.mem_scriptQ_of_three hA h146 hYΔ hAY
      (not_three_dvd_of_oPrimeResidualOf_eq_bot hYres)
  have hZbot : deltaZero A (lB A) Y = ⊥ :=
    eq_bot_of_structure (Sec16.deltaZero_eq_commutator Y) (h167 Y hY).1
      (le_centralizer_of_piOf_two h1411 hT hTC
        (pCoreOf_mem_scriptQPi hYQ (Sec14.deltaZero_le Y) (Sec16.le_normalizer_deltaZero Y)))
  have hdY := (Sec14.rank3II_14_5_lB hA hbot hAY).1
  rw [hZbot, bot_sup_eq] at hdY
  have hYI : Y ≤ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    rw [hYΔ, hdY]
    exact inf_le_left
  exact hYM (hYI.trans (((pPrimeCoreOf_three_le _).trans
    (Subgroup.centralizer_le_normalizer (A : Set G))).trans h.normalizer_le))

theorem c174F3_pCoreOf_ne_bot {H Z : Subgroup G}
    (hZH : Z ≤ H) (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hfit : generalizedFitting ↥Z = CFSG.pCore 2 ↥Z) :
    CFSG.Open.pCoreOf 2 H ≠ ⊥ := by
  have hF : generalizedFitting ↥Z ≠ ⊥ := by
    intro hF0
    have hc := CFSG.centralizer_generalizedFitting_le ↥Z
    rw [hF0] at hc
    apply hZne
    rw [eq_bot_iff]
    intro z hz
    have hmem : (⟨z, hz⟩ : ↥Z) ∈ Subgroup.centralizer ((⊥ : Subgroup ↥Z) : Set ↥Z) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
      simp [hx]
    have h1 : (⟨z, hz⟩ : ↥Z) = 1 := Subgroup.mem_bot.mp (hc hmem)
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val h1
  have hp : CFSG.pCore 2 ↥Z ≠ ⊥ := by
    rw [← hfit]
    exact hF
  have hNne : (CFSG.pCore 2 ↥Z).map Z.subtype ≠ ⊥ := by
    intro h0
    apply hp
    exact Subgroup.map_injective (Subgroup.subtype_injective Z)
      (h0.trans (Subgroup.map_bot Z.subtype).symm)
  have hNle : (CFSG.pCore 2 ↥Z).map Z.subtype ≤ H :=
    (Subgroup.map_subtype_le _).trans hZH
  have hNp : IsPGroup 2 ((CFSG.pCore 2 ↥Z).map Z.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Z)).map Z.subtype
  have hHN : H ≤ Subgroup.normalizer ((CFSG.pCore 2 ↥Z).map Z.subtype : Set G) := by
    intro g hg
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Z) (CFSG.pCore 2 ↥Z) (hHZ hg)
  have hkey : (CFSG.pCore 2 ↥Z).map Z.subtype ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hNle hHN hNp
  intro hbot0
  rw [hbot0] at hkey
  exact hNne (le_bot_iff.mp hkey)

theorem pCoreOf_delta_cQuot_sup_ne_bot (h : Sec17Std G A c L Y₀) (h149 : Item149 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {T : Subgroup G} (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hne : deltaZero A (lB A) (cQuot Y₀ ⊔ T) ≠ ⊥) :
    CFSG.Open.pCoreOf 2 (delta A (lB A) (cQuot Y₀ ⊔ T)) ≠ ⊥ := by
  have hY' : cQuot Y₀ ⊔ T ∈ scriptY A := mem_scriptY_cQuot_sup h hT
  have hfit : generalizedFitting ↥(cQuot Y₀ ⊔ T) = CFSG.pCore 2 ↥(cQuot Y₀ ⊔ T) :=
    fstar_cQuot_sup h hT
  have hZfit : generalizedFitting ↥(deltaZero A (lB A) (cQuot Y₀ ⊔ T)) =
      CFSG.pCore 2 ↥(deltaZero A (lB A) (cQuot Y₀ ⊔ T)) :=
    ((h149 _ hY').2.2.2 hfit).2
  obtain ⟨hdecomp, -, hnorm⟩ :=
    CFSG.RankThree.PartTwo.Sec14.rank3II_14_5_lB h.isE27 hbot hY'.2
  have hZH : deltaZero A (lB A) (cQuot Y₀ ⊔ T) ≤ delta A (lB A) (cQuot Y₀ ⊔ T) := by
    rw [hdecomp]
    exact le_sup_left
  exact c174F3_pCoreOf_ne_bot hZH hnorm hne hZfit

theorem oPrimeResidualOf_bot_aux {Y : Subgroup G} (hY3 : ¬ 3 ∣ Nat.card Y) :
    oPrimeResidualOf 3 Y = ⊥ := by
  have key : oPrimeResidual 3 ↥Y = ⊥ := by
    unfold oPrimeResidual
    rw [Subgroup.closure_eq_bot_iff]
    rintro x ⟨k, hk⟩
    have hdvd : orderOf x ∣ Nat.gcd (3 ^ k) (Nat.card ↥Y) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_natCard x)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)), Nat.dvd_one,
      orderOf_eq_one_iff] at hdvd
    exact hdvd
  unfold oPrimeResidualOf
  rw [key, Subgroup.map_bot]

theorem delta_mem_scriptY1 (hA : IsE27 A) (h146 : Item146 A (lB A)) {Z M : Subgroup G}
    (hZM : Z ≤ M) (hM : M ≠ ⊤) (h3 : ¬ 3 ∣ Nat.card ↥(delta A (lB A) Z))
    (h2 : CFSG.Open.pCoreOf 2 (delta A (lB A) Z) ≠ ⊥) :
    delta A (lB A) Z ∈ scriptY1 A (lB A) := by
  have hDM : delta A (lB A) Z ≤ M := (delta_le Z).trans hZM
  have hDtop : delta A (lB A) Z ≠ ⊤ := by
    intro htop
    apply hM
    rw [htop] at hDM
    exact top_le_iff.mp hDM
  have hAD : A ≤ Subgroup.normalizer ((delta A (lB A) Z : Subgroup G) : Set G) :=
    le_normalizer_delta Z
  have hDD : delta A (lB A) Z = delta A (lB A) (delta A (lB A) Z) :=
    (delta_delta Z).symm
  have hO : oPrimeResidualOf 3 (delta A (lB A) Z) = ⊥ := oPrimeResidualOf_bot_aux h3
  exact ⟨⟨⟨⟨hDtop, hAD⟩, h2⟩, hDD⟩, hO⟩

theorem exists_conjugateJoin_le {X K C : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hKX : K ≤ X) (hAC : A ≤ Subgroup.normalizer (C : Set G)) (hKC : K ≤ C) :
    ∃ KA : Subgroup G, K ≤ KA ∧ KA ≤ X ∧ KA ≤ C ∧ A ≤ Subgroup.normalizer (KA : Set G) := by
  have hcj : ∀ (a b : G) (S : Subgroup G),
      (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom ≤
        S.map (MulAut.conj (b * a)).toMonoidHom := by
    intro a b S
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hstab : ∀ (T : Subgroup G), A ≤ Subgroup.normalizer (T : Set G) →
      ∀ a ∈ A, ∀ S : Subgroup G, S ≤ T → S.map (MulAut.conj a).toMonoidHom ≤ T := by
    intro T hAT a ha S hS
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAT ha) x).mp (hS hx)
  obtain ⟨KA, hKA⟩ : ∃ KA : Subgroup G,
      KA = ⨆ a : ↥A, K.map (MulAut.conj (a : G)).toMonoidHom := ⟨_, rfl⟩
  have hKA_le_X : KA ≤ X := by
    rw [hKA]
    exact iSup_le fun a => hstab X hAX (a : G) a.2 K hKX
  have hKA_le_C : KA ≤ C := by
    rw [hKA]
    exact iSup_le fun a => hstab C hAC (a : G) a.2 K hKC
  have hKA_sub : K ≤ KA := by
    rw [hKA]
    refine le_iSup_of_le ⟨1, A.one_mem⟩ ?_
    rintro x hx
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hconj : ∀ b ∈ A, KA.map (MulAut.conj b).toMonoidHom ≤ KA := by
    intro b hb
    rw [hKA, Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    exact (hcj (a : G) b K).trans (le_iSup_of_le ⟨b * a, A.mul_mem hb a.2⟩ le_rfl)
  refine ⟨KA, hKA_sub, hKA_le_X, hKA_le_C, ?_⟩
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h' : (MulAut.conj b).toMonoidHom h ∈ KA.map (MulAut.conj b).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (show h ∈ KA from hh)
    exact hconj b hb h'
  · intro hh
    have h' : (MulAut.conj b⁻¹).toMonoidHom (b * h * b⁻¹) ∈
        KA.map (MulAut.conj b⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (show b * h * b⁻¹ ∈ KA from hh)
    have h'' := hconj b⁻¹ (A.inv_mem hb) h'
    simpa [MulAut.conj_apply, mul_assoc] using h''

theorem not_three_dvd_of_normal_sup {D N C : Subgroup G} (hsup : N ⊔ C = D) (hND : N ≤ D)
    (hCD : C ≤ D) (hnorm : D ≤ Subgroup.normalizer (N : Set G))
    (hN : Nat.Coprime 3 (Nat.card ↥N)) (hC : Nat.Coprime 3 (Nat.card ↥C)) :
    ¬ 3 ∣ Nat.card ↥D := by
  have hnormal : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).mpr hnorm
  haveI := hnormal
  have hsupD : N.subgroupOf D ⊔ C.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hND hCD, hsup, Subgroup.subgroupOf_self]
  let f : ↥C →* ↥D ⧸ (N.subgroupOf D) :=
    (QuotientGroup.mk' (N.subgroupOf D)).comp (Subgroup.inclusion hCD)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ N.subgroupOf D ⊔ C.subgroupOf D := by
      rw [hsupD]
      exact Subgroup.mem_top x
    obtain ⟨n, hn, z, hz, hnz⟩ := (Subgroup.mem_sup_of_normal_left).mp hx
    refine ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, ?_⟩
    show (QuotientGroup.mk (z : ↥D) : ↥D ⧸ N.subgroupOf D) = QuotientGroup.mk x
    rw [← hnz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have hcard : Nat.card ↥D = Nat.card ↥N * Nat.card (↥D ⧸ N.subgroupOf D) := by
    have h1 := Subgroup.card_mul_index (N.subgroupOf D)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv] at h1
    exact h1.symm
  have hquot : Nat.card (↥D ⧸ N.subgroupOf D) ∣ Nat.card ↥C :=
    Subgroup.card_dvd_of_surjective hf
  have hdvd : Nat.card ↥D ∣ Nat.card ↥N * Nat.card ↥C := by
    rw [hcard]
    exact Nat.mul_dvd_mul_left _ hquot
  intro h3
  have h3' : 3 ∣ Nat.card ↥N * Nat.card ↥C := h3.trans hdvd
  have hcop : Nat.Coprime 3 (Nat.card ↥N * Nat.card ↥C) := Nat.Coprime.mul_right hN hC
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3') (by norm_num)

theorem not_three_dvd_delta_of_case148One (hA : IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (h1 : Case148One A (lB A) Y) :
    ¬ 3 ∣ Nat.card ↥(delta A (lB A) Y) := by
  obtain ⟨hsup, -, hnorm⟩ := rank3II_14_5_lB hA hbot hAY
  have hN₀le : deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y := h1
  have hN₀cop : Nat.Coprime 3 (Nat.card ↥(deltaZero A (lB A) Y)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hN₀le) (coprime_card_pPrimeCoreOf 3 Y)
  have hC'cop : Nat.Coprime 3
      (Nat.card ↥(pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
  refine not_three_dvd_of_normal_sup hsup.symm (deltaZero_le_delta Y) ?_ hnorm hN₀cop hC'cop
  rw [hsup]
  exact le_sup_right

theorem not_allPointsHJ_of_sec17 (h : Sec17Std G A c L Y₀)
    (hJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ AllPointsHJ A := by
  intro hall
  obtain ⟨Le, hLe, ⟨φ⟩⟩ := hall c h.zpowers_mem_omegaA
  have hcard : Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = 604800 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.J2.card_J2]
  have h3 : 3 ∣ Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) := by
    rw [hcard]
    norm_num
  have h3Le : 3 ∣ Nat.card ↥Le := h3.trans (Subgroup.card_quotient_dvd_card _)
  have hLeL : Le = L :=
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 Le hLe.1 h3Le
  subst hLeL
  exact hJ ⟨φ⟩

theorem mem_scriptY_of_eq_delta (hA : IsE27 A) {X : Subgroup G} (hX : X = delta A (lB A) X)
    (h3 : ¬ 3 ∣ Nat.card X) : X ∈ scriptY A := by
  have h27 : 3 ∣ Nat.card A := by
    rw [hA.2]
    norm_num
  have hG : 3 ∣ Nat.card G := h27.trans (Subgroup.card_subgroup_dvd_card A)
  refine ⟨?_, ?_⟩
  · intro htop
    apply h3
    rw [htop, Subgroup.card_top]
    exact hG
  · have hN := le_normalizer_delta (A := A) (LB := lB A) X
    rw [← hX] at hN
    exact hN

section Certificates

theorem not_three_dvd_delta_cQuot_sup
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {T : Subgroup G} (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) :
    ¬ 3 ∣ Nat.card ↥(delta A (lB A) (cQuot Y₀ ⊔ T)) := by
  have hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (lBar_simple_and_pRank h.toSec14Std).1
  have hna : ∃ a b : ↥L ⧸ aschbacherSolvableCore 3 ↥L, a * b ≠ b * a :=
    lBar_nonabelian h.toSec14Std
  have hd : LemmaEData A c L Y₀ (cQuot Y₀ ⊔ T) :=
    ⟨h, hΩ, hJ, mem_scriptY_cQuot_sup h hT, pRank_three_cQuot_sup_le_one h hT,
      not_three_dvd_inf_cQuot_sup h hs hna hT, solvMod3'_cQuot_sup_inf_nH h hT⟩
  have h1 : Case148One A (lB A) (cQuot Y₀ ⊔ T) := case148One_of_lemmaE h148 hd
  exact not_three_dvd_delta_of_case148One h.isE27 hbot hd.mem.2 h1

theorem claim174_of_inputs
    (h135 : Item135) (h145 : Item145BotS14) (h146 : Item146S14) (h148 : Item148NHJS14)
    (h149 : Item149S14) (h1411 : Item1411_1S17) (h166 : Item166S17) (h167 : Item167R) :
    Claim174 := by
  intro G _ _ A c L Y₀ h X hX h3X K hK hSz Y hY hYM S hS
  have h146' := h146 G A c L h.toSec14Std
  have hbot := h145 G A c L h.toSec14Std
  have h149' := h149 G A c L h.toSec14Std
  have h1411' := h1411 G A c L Y₀ h
  have h166' := h166 G A c L Y₀ h
  have h167' := h167 G A c L h.toSec15R
  have hA : IsE27 A := h.isE27
  have hM : Subgroup.normalizer (Y₀ : Set G) ≠ ⊤ := (normalizer_ne_top_and_fstar h).1
  have hC : cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := by
    intro z hz
    have hz' : z ∈ (cQuot Y₀ : Set G) := hz
    rw [coe_cQuot] at hz'
    exact hz'.1
  have hAN : A ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (Subgroup.le_normalizer (H := A)).trans h.normalizer_le
  have hAC : A ≤ Subgroup.normalizer ((cQuot Y₀ : Subgroup G) : Set G) :=
    hAN.trans (normalizer_le_normalizer_cQuot Y₀)
  have hXY : X ∈ scriptY A := mem_scriptY_of_eq_delta hA hX h3X
  rcases h.a10_or_omega with hA10 | hΩ
  · exact absurd (five_dvd_card_cQuot_of_suzuki h166' h hX h3X hK hSz)
      (not_five_dvd_cQuot_of_a10 h hA10)
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact absurd (five_dvd_card_cQuot_of_suzuki h166' h hX h3X hK hSz)
      (not_five_dvd_cQuot_of_j2 h135 h hJ)
  have h148' : Item148 A (lB A) := h148 G A c L h.toSec14Std (not_allPointsHJ_of_sec17 h hJ)
  obtain ⟨T, hT, hST⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Proof1413.exists_scriptQPiStar_top (A := A) (Y := Y) hS.prop
  have hTM : T ≤ Subgroup.normalizer (Y₀ : Set G) := h.qStar_le T hT
  have hTQ : T ∈ scriptQ A (lB A) := hT.prop.1.1
  have hY''M : cQuot Y₀ ⊔ T ≤ Subgroup.normalizer (Y₀ : Set G) := sup_le hC hTM
  have h3' : ¬ 3 ∣ Nat.card ↥(delta A (lB A) (cQuot Y₀ ⊔ T)) :=
    not_three_dvd_delta_cQuot_sup h148' hbot h hΩ hJ hT
  have hne : deltaZero A (lB A) (cQuot Y₀ ⊔ T) ≠ ⊥ :=
    deltaZero_cQuot_sup_ne_bot h h146' hbot h1411' h167' hT hY hYM
  have h2 : CFSG.Open.pCoreOf 2 (delta A (lB A) (cQuot Y₀ ⊔ T)) ≠ ⊥ :=
    pCoreOf_delta_cQuot_sup_ne_bot h h149' hbot hT hne
  have hY1 : delta A (lB A) (cQuot Y₀ ⊔ T) ∈ scriptY1 A (lB A) :=
    delta_mem_scriptY1 hA h146' hY''M hM h3' h2
  refine ⟨delta A (lB A) (cQuot Y₀ ⊔ T), hY1, ?_, ?_⟩
  ·
    have hKθ := (h166' Y₀ h.mem_y0Star).1 X hXY hX K hK hSz
    have hKC0 : K ≤ cQuot Y₀ := by
      have hsub : (K : Set G) ⊆ (cQuot Y₀ : Set G) := by
        rw [coe_cQuot]
        exact hKθ.2
      exact SetLike.coe_subset_coe.mp hsub
    have hXQ : X ∈ scriptQ A (lB A) :=
      CFSG.RankThree.PartTwo.Sec16.Proof165.mem_scriptQ_of_three hA h146' hX hXY.2 h3X
    obtain ⟨KA, hKKA, hKAX, hKAC, hAKA⟩ :=
      exists_conjugateJoin_le hXY.2 (le_of_mem_thetaComponentsIn hK) hAC hKC0
    have hKAQ : KA ∈ scriptQ A (lB A) :=
      CFSG.RankThree.PartTwo.Sec14.mem_scriptQ_of_le hXQ hKAX hAKA
    exact hKKA.trans (CFSG.RankThree.PartTwo.Sec14.le_delta hKAQ (hKAC.trans le_sup_left))
  ·
    exact hST.trans (CFSG.RankThree.PartTwo.Sec14.le_delta hTQ le_sup_right)

end Certificates

end CFSG.RankThree.PartTwo.Sec17.C174
