module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res4ProofA10
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofDefs
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofPerm
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec17.Proof171Gen

variable {G : Type} [Group G] [Finite G]

theorem kF_sq : ∀ m : Fin 4, kOneF m ^ 2 = 1 ∧ kTwoF m ^ 2 = 1 ∧ kThreeF m ^ 2 = 1 := by
  decide +kernel

theorem isPGroup_kOne : IsPGroup 2 kOne := by
  rintro ⟨x, m, rfl⟩
  exact ⟨1, Subtype.ext (by simpa using (kF_sq m).1)⟩

theorem isPGroup_kTwo : IsPGroup 2 kTwo := by
  rintro ⟨x, m, rfl⟩
  exact ⟨1, Subtype.ext (by simpa using (kF_sq m).2.1)⟩

theorem kOne_kTwo_le {K : Subgroup (Perm (Fin 10))} (hK : K = kOne ∨ K = kTwo) :
    K ≤ Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10) ∧
      ¬ 3 ∣ Nat.card K := by
  rcases hK with rfl | rfl
  · refine ⟨?_, Proof171.not_three_dvd_of_isPGroup_two isPGroup_kOne⟩
    rintro _ ⟨m, rfl⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (kOneF_kTwoF_comm_dThree m).1,
      (kF_sign m).1⟩
  · refine ⟨?_, Proof171.not_three_dvd_of_isPGroup_two isPGroup_kTwo⟩
    rintro _ ⟨m, rfl⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (kOneF_kTwoF_comm_dThree m).2,
      (kF_sign m).2.1⟩

@[expose] noncomputable def cimg (Y₀ : Subgroup G)
    (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) (g : Perm (Fin 10))
    (X : Subgroup G) : Subgroup (Perm (Fin 10)) :=
  (imgTen Y₀ φ X).map (MulAut.conj g).toMonoidHom

variable {Y₀ : Subgroup G} {φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)}
  {g : Perm (Fin 10)}

omit [Finite G] in
theorem mem_cimg {X : Subgroup G} {z : Perm (Fin 10)} :
    z ∈ cimg Y₀ φ g X ↔ ∃ y : ↥Y₀, (y : G) ∈ X ∧ g * projTen Y₀ φ y * g⁻¹ = z := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_imgTen Y₀ φ).mp hw
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (mem_imgTen Y₀ φ).mpr ⟨y, hy, rfl⟩, rfl⟩

theorem not_three_dvd_card_cimg {X : Subgroup G} (hXY : X ≤ Y₀) (hX : ¬ 3 ∣ Nat.card X) :
    ¬ 3 ∣ Nat.card (cimg Y₀ φ g X) := by
  rw [cimg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact fun h3 => hX (h3.trans (card_imgTen_dvd Y₀ φ hXY))

variable {A : Subgroup G} {c : G} {L : Subgroup G}

omit [Finite G] in
theorem projTen_eq_one_of_mem {y : ↥Y₀} (hy : (y : G) ∈ CFSG.Open.pCoreOf 2 Y₀) :
    projTen Y₀ φ y = 1 :=
  (projTen_eq_one_iff Y₀ φ y).mpr ((Step163Alt.mem_pCore_two_iff y).mpr hy)

omit [Finite G] in
theorem inv_mul_mem_of_projTen_eq {y y' : ↥Y₀} (h : projTen Y₀ φ y = projTen Y₀ φ y') :
    ((y⁻¹ * y' : ↥Y₀) : G) ∈ CFSG.Open.pCoreOf 2 Y₀ :=
  Res162b.mem_pCoreOf_of_projTen_eq_one (by rw [map_mul, map_inv, h, inv_mul_cancel])

omit [Finite G] in
theorem eTwentySeven_le_normalizer_cimg (hP : A10Pic A c L Y₀ φ g) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    eTwentySeven ≤ Subgroup.normalizer (cimg Y₀ φ g X : Set (Perm (Fin 10))) := by
  refine le_normalizer_of_conj fun x hx z hz => ?_
  obtain ⟨a, ha, rfl⟩ := hP.surj x hx
  obtain ⟨y, hy, rfl⟩ := mem_cimg.mp hz
  refine mem_cimg.mpr ⟨a * y * a⁻¹, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (hAX ha) (y : G)).mp hy
    simpa using this
  · rw [map_mul, map_mul, map_inv]
    group

omit [Finite G] in
theorem inf_L_le_of_le_kThree (hP : A10Pic A c L Y₀ φ g) {S : Subgroup G}
    (hR : cimg Y₀ φ g (S ⊓ Y₀) ≤ kThree) : S ⊓ L ≤ CFSG.Open.pCoreOf 2 Y₀ := by
  intro x hx
  have hxY : x ∈ Y₀ := hP.L_le hx.2
  obtain ⟨m, hm⟩ := hR (mem_cimg.mpr ⟨⟨x, hxY⟩, ⟨hx.1, hxY⟩, rfl⟩)
  have hc := hP.L_cent ⟨x, hxY⟩ hx.2
  rw [hm] at hc
  have hm0 := kThreeF_comm_dThree m hc
  subst hm0
  have h1 : g * projTen Y₀ φ ⟨x, hxY⟩ * g⁻¹ = 1 := hm
  rw [conj_eq_one_iff] at h1
  exact Res162b.mem_pCoreOf_of_projTen_eq_one h1

theorem false_of_inf_L_le {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) (hSL : S ⊓ L ≤ CFSG.Open.pCoreOf 2 Y₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set π := projTen Y₀ φ with hπ
  set T : Subgroup G := ((kOne.comap (MulAut.conj g).toMonoidHom).comap π).map Y₀.subtype
    with hT
  have hmemT : ∀ y : ↥Y₀, (y : G) ∈ T ↔ g * π y * g⁻¹ ∈ kOne := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  set L₁ := L ⊓ T with hL₁
  have hT2 : IsPGroup 2 T :=
    ((isPGroup_kOne.comap_of_injective _ (MulAut.conj g).injective).comap_of_ker_isPGroup π
      (Res162b.projTen_ker_isPGroup Y₀ φ)).map Y₀.subtype
  have hL₁2 : IsPGroup 2 L₁ := hT2.to_le inf_le_right
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_conj fun a ha t ht => ?_
    obtain ⟨y, hy, rfl⟩ := ht
    have haY : a ∈ Y₀ := hP.le_y0 ha
    have hy' : g * π y * g⁻¹ ∈ kOne := hy
    have hk := (Subgroup.mem_normalizer_iff.mp
      (eTwentySeven_le_normalizer_k.1 (hP.mem ⟨a, haY⟩ ha)) _).mp hy'
    have hya : g * π (⟨a, haY⟩ * y * ⟨a, haY⟩⁻¹) * g⁻¹ =
        (g * π ⟨a, haY⟩ * g⁻¹) * (g * π y * g⁻¹) * (g * π ⟨a, haY⟩ * g⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      group
    have hmem := (hmemT (⟨a, haY⟩ * y * ⟨a, haY⟩⁻¹)).mpr (by rw [hya]; exact hk)
    simpa using hmem
  have hAL₁ : A ≤ Subgroup.normalizer (L₁ : Set G) := Late.le_normalizer_inf hD.le_normalizer hAT
  have hL₁H : L₁ ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    inf_le_left.trans (h.le_centralizer_c.trans (centralizer_singleton_le_normalizer_zpowers c))
  have hL₁inv : L₁ ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hL₁H, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      (Proof171.not_three_dvd_of_isPGroup_two hL₁2), hAL₁⟩
  obtain ⟨Q, hQ, hL₁Q⟩ := exists_le_mem_maxInvariantPiSubgroups hL₁inv
  have hQQ := (h142 c h.zpowers_mem_omegaA Q hQ).1
  have hL₁P : L₁ ∈ scriptQPi A (lB A) L (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hQQ hL₁Q hAL₁, inf_le_left⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hL₁2⟩
  have hSLL₁ : S ⊓ L ≤ L₁ := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    have hxO := hSL hx
    have hxY : x ∈ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀ hxO
    refine (hmemT ⟨x, hxY⟩).mpr ?_
    rw [show π ⟨x, hxY⟩ = 1 from projTen_eq_one_of_mem hxO, mul_one, mul_inv_cancel]
    exact ⟨0, rfl⟩
  have hle : L₁ ≤ S ⊓ L := h.inf_L_mem_qStar_two.2 hL₁P hSLL₁
  obtain ⟨hK1c, hK13⟩ := kOne_kTwo_le (Or.inl rfl)
  obtain ⟨l, hl, hlz⟩ := hP.L_cover kOne hK1c hK13 (kOneF 1) ⟨1, rfl⟩
  have hlL₁ : (l : G) ∈ L₁ := ⟨hl, (hmemT l).mpr (by rw [hlz]; exact ⟨1, rfl⟩)⟩
  have h1 : π l = 1 := projTen_eq_one_of_mem (hSL (hle hlL₁))
  rw [h1, mul_one, mul_inv_cancel] at hlz
  exact absurd hlz.symm (by decide)

theorem cimg_eq {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) :
    cimg Y₀ φ g (S ⊓ Y₀) = kOne ∨ cimg Y₀ φ g (S ⊓ Y₀) = kTwo := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := cimg Y₀ φ g (S ⊓ Y₀) with hR
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hR3 : ¬ 3 ∣ Nat.card R := not_three_dvd_card_cimg inf_le_right
    (Proof171.not_three_dvd_of_isPGroup_two (hS2.to_le inf_le_left))
  have hAS : A ≤ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0
  have hER := eTwentySeven_le_normalizer_cimg hP hAS
  have hbad : ¬ R ≤ kThree := fun h3 => false_of_inf_L_le h hP h142 (inf_L_le_of_le_kThree hP h3)
  have hR0 : R ≠ ⊥ := fun h0 => hbad (h0 ▸ bot_le)
  rcases le_kOne_or_le_kTwo_or_le_kThree hR3 hER with h1 | h1 | h1
  · exact Or.inl (kF_irreducible (Or.inl rfl) h1 hER hR0)
  · exact Or.inr (kF_irreducible (Or.inr (Or.inl rfl)) h1 hER hR0)
  · exact (hbad h1).elim

theorem inf_y0_le_sup {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) : S ⊓ Y₀ ≤ L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  intro x hx
  have hxY : x ∈ Y₀ := hx.2
  have hz : g * projTen Y₀ φ ⟨x, hxY⟩ * g⁻¹ ∈ cimg Y₀ φ g (S ⊓ Y₀) :=
    mem_cimg.mpr ⟨_, hx, rfl⟩
  obtain ⟨K, hK, hRK⟩ : ∃ K : Subgroup (Perm (Fin 10)), (K = kOne ∨ K = kTwo) ∧
      cimg Y₀ φ g (S ⊓ Y₀) = K := by
    rcases cimg_eq h hP h142 with h1 | h1
    · exact ⟨kOne, Or.inl rfl, h1⟩
    · exact ⟨kTwo, Or.inr rfl, h1⟩
  obtain ⟨hKc, hK3⟩ := kOne_kTwo_le hK
  rw [hRK] at hz
  obtain ⟨l, hl, hlz⟩ := hP.L_cover K hKc hK3 _ hz
  have he : projTen Y₀ φ l = projTen Y₀ φ ⟨x, hxY⟩ := by
    have := congrArg (fun z => g⁻¹ * z * g) hlz
    simpa [mul_assoc] using this
  have hO := inv_mul_mem_of_projTen_eq he
  have hx' : x = (l : G) * ((l⁻¹ * ⟨x, hxY⟩ : ↥Y₀) : G) := by simp
  rw [hx']
  exact Subgroup.mul_mem_sup hl hO

theorem inf_y0_le_sup_inf {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) (hO2 : CFSG.Open.pCoreOf 2 Y₀ ≤ S) :
    S ⊓ Y₀ ≤ (S ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  have hLO : L ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    hP.L_le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  calc S ⊓ Y₀ ≤ S ⊓ (L ⊔ CFSG.Open.pCoreOf 2 Y₀) := le_inf inf_le_left (inf_y0_le_sup h hP h142)
    _ ≤ (S ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₀ := Proof1712.inf_sup_le_of_le hO2 hLO

end CFSG.RankThree.PartTwo.Sec17.Proof17Res4

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

theorem claim1720A10_proof (h1715 : Item1715) (h142 : Concl142S14) (hO2 : Claim17O2Y0) :
    Claim1720A10 := by
  intro G _ _ A c L Y₀ Y₁ S p P h hA10
  have hs := h.toSec17Std
  have hKS := hO2 G A c L Y₀ Y₁ S p P h
  rcases h1715 G A c L Y₀ hs with ⟨-, hY, -, -⟩ | ⟨-, ⟨φL⟩, -, -, hT⟩
  · have hLK : L ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
      hs.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
    have e : S ⊓ Y₀ = S ⊓ (L ⊔ CFSG.Open.pCoreOf 2 Y₀) := by
      conv_lhs => rw [hY]
    rw [e]
    exact Proof1712.inf_sup_le_of_le hKS hLK
  · obtain ⟨φ⟩ := hA10
    obtain ⟨g, hP⟩ := Proof17Res4.exists_a10Pic hs φ φL hT.1
    exact Proof17Res4.inf_y0_le_sup_inf h hP (h142 G A c L hs.toSec14Std) hKS

end CFSG.RankThree.PartTwo.Sec17
