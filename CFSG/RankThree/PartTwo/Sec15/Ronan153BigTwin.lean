module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers
public import CFSG.RankThree.PartTwo.Sec15.Gagen153Case7
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec18.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan153Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof153Twin2
  CFSG.RankThree.PartTwo.Sec15.Proof153Twin3
open scoped commutatorElement

section Big

variable {G : Type} [Group G] [Finite G]

section Twin

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem le_normalizer_map_conj_of_hasNonCentralThree_big (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hYb : Big152 Y) (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) {t : G}
    (ht : t ∈ M) :
    A ≤ Subgroup.normalizer ((Y.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYM, hAM, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.toSec13Data.isElemAbelian.2
  intro a ha
  by_contra haZ
  set Z := Y.map (MulAut.conj t).toMonoidHom with hZ
  have hconj : ∀ (u : G), u ∈ A → Y.map (MulAut.conj u).toMonoidHom = Y := fun u hu =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAY hu)
  have hZa : Z.map (MulAut.conj a).toMonoidHom ≠ Z := fun he =>
    haZ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hYZ : Y ≠ Z := fun he => haZ (he ▸ hAY ha)
  have hmapinj : ∀ (u : G) (P Q : Subgroup G), P.map (MulAut.conj u).toMonoidHom =
      Q.map (MulAut.conj u).toMonoidHom → P = Q := fun u P Q he =>
    Subgroup.map_injective (MulAut.conj u).injective he
  have ha2 : a * a ∈ A := A.mul_mem ha ha
  have hYZb : ∀ b ∈ A, Y ≠ Z.map (MulAut.conj b).toMonoidHom := by
    intro b hb he
    apply hYZ
    apply hmapinj b
    rw [← he, hconj b hb]
  set g : Fin 4 → G := ![1, t, a * t, a * a * t] with hg
  have hgM : ∀ i, g i ∈ M := by
    intro i
    fin_cases i
    · exact M.one_mem
    · exact ht
    · exact M.mul_mem (hAM ha) ht
    · exact M.mul_mem (M.mul_mem (hAM ha) (hAM ha)) ht
  have hYg : ∀ i, Y.map (MulAut.conj (g i)).toMonoidHom =
      ![Y, Z, Z.map (MulAut.conj a).toMonoidHom,
        Z.map (MulAut.conj (a * a)).toMonoidHom] i := by
    intro i
    fin_cases i
    · exact Late.map_conj_one Y
    · rfl
    · exact (Late.map_conj_map_conj Y a t).symm
    · exact (Late.map_conj_map_conj Y (a * a) t).symm
  have hZa2 : Z.map (MulAut.conj (a * a)).toMonoidHom ≠ Z := by
    intro he
    apply hZa
    have h3 : a * (a * a) = 1 := by rw [← pow_three]; exact hA3 a ha
    calc Z.map (MulAut.conj a).toMonoidHom
        = (Z.map (MulAut.conj (a * a)).toMonoidHom).map (MulAut.conj a).toMonoidHom := by rw [he]
      _ = Z := by rw [Late.map_conj_map_conj, h3, Late.map_conj_one]
  have hZaa : Z.map (MulAut.conj (a * a)).toMonoidHom ≠ Z.map (MulAut.conj a).toMonoidHom := by
    intro he
    apply hZa
    apply hmapinj a
    rw [Late.map_conj_map_conj, ← he]
  have hdist : ∀ i j : Fin 4, i ≠ j → Y.map (MulAut.conj (g i)).toMonoidHom ≠
      Y.map (MulAut.conj (g j)).toMonoidHom := by
    intro i j hij
    rw [hYg i, hYg j]
    exact vec_four_ne hYZ (hYZb a ha) (hYZb (a * a) ha2) hZa.symm hZa2.symm hZaa.symm i j hij
  obtain ⟨Y', hY', hYY'⟩ := Ronan152Six.mem_thetaComponentsIn_of_big h h152 hY hYb hM
  change Y'.map M.subtype = Y at hYY'
  set σ : Fin 4 → (↥M ≃* ↥M) := fun i => MulAut.conj (⟨g i, hgM i⟩ : M) with hσ
  have hσY : ∀ i, (Y'.map (σ i).toMonoidHom).map M.subtype =
      Y.map (MulAut.conj (g i)).toMonoidHom := by
    intro i
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨x, hxY, hx3, y, hyY, hxy⟩ := hN
  have hxY0 := hxY
  have hyY0 := hyY
  rw [← hYY'] at hxY0 hyY0
  obtain ⟨x', hxY', rfl⟩ := hxY0
  obtain ⟨y', hyY', rfl⟩ := hyY0
  obtain ⟨hθN, hθs, hθ3⟩ := map_aschbacherSolvableCore_facts M
  obtain ⟨-, hθc, hθ3', -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hxyM : ⁅x', y'⁆ ∉ aschbacherSolvableCore 3 ↥M := by
    intro hmem
    apply hxy
    have hmemG : (x' : G) * y' * (x' : G)⁻¹ * (y' : G)⁻¹ ∈
        (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y := by
      refine ⟨?_, Y.mul_mem (Y.mul_mem (Y.mul_mem hxY hyY) (Y.inv_mem hxY)) (Y.inv_mem hyY)⟩
      have := Subgroup.mem_map_of_mem M.subtype hmem
      rwa [commutatorElement_def] at this
    exact inf_le_map_aschbacherSolvableCore (hYM.trans hθN) hθs hθ3 hmemG
  have h4 := four_le_pRank_of_thetaComponents (fun i => Y'.map (σ i).toMonoidHom)
    (fun i => map_mulEquiv_mem_thetaComponents Nat.prime_three (σ i) hY')
    (fun i j hij he => hdist i j hij (by rw [← hσY i, ← hσY j, he]))
    (fun i => σ i x') (fun i => σ i y')
    (fun i => Subgroup.mem_map_of_mem _ hxY') (fun i => Subgroup.mem_map_of_mem _ hyY')
    (fun i => by
      rw [← map_pow]
      have : x' ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one])
    (fun i hmem => by
      apply hxyM
      rw [← map_commutatorElement] at hmem
      have hchar : (aschbacherSolvableCore 3 ↥M).map (σ i).toMonoidHom =
          aschbacherSolvableCore 3 ↥M :=
        Subgroup.characteristic_iff_map_eq.mp hθc (σ i)
      have := Subgroup.mem_map_of_mem (σ i).symm.toMonoidHom hmem
      rw [← hchar, Subgroup.map_map] at this
      simpa using this)
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

theorem oPrimeResidualOf_delta_le_of_hasNonCentralThree_big (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (h152 : Item152Big A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y) (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    oPrimeResidualOf 3 (delta A (lB A) M) ≤
      oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) :=
  oPrimeResidualOf_delta_le_of_forall_conj h149
    (facts_of_mem_maximalTwoLocalsContaining h hM).2.2.1.1
    fun _ ht => le_normalizer_map_conj_of_hasNonCentralThree_big h h152 hY hYb hN hM ht

theorem oPrimeResidualOf_delta_eq_iff_big (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    (h152 : Item152Big A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hYb : Big152 Y) (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    oPrimeResidualOf 3 (delta A (lB A) M) =
        oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) ↔
      Subgroup.normalizer (Y : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := oPrimeResidualOf_delta_le_of_hasNonCentralThree_big h h149 h152 hY hYb hN hM
  have hMY : M ∈ scriptY A := (facts_of_mem_maximalTwoLocalsContaining h hM).2.2.1.1
  obtain ⟨hNX, -, -, hX2⟩ := facts153 h h149 hY
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  constructor
  · intro heq
    have hMX : M ≤ Subgroup.normalizer (X : Set G) := by
      rw [← heq]
      exact normalizer_le_normalizer_oPrimeResidualOf_delta h149 hMY
    have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) :=
      CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX2
    have hNXle : Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
    have hMeq : M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
      by_contra hne
      exact hM.1.2 _ (lt_of_le_of_ne (hMX.trans hNXle) hne) hloc
    rw [hMeq]
    exact hNX.trans hNXle
  · intro hNM
    exact le_antisymm hle (oPrimeResidualOf_mono 3 (delta_mono hNM))

end Twin

theorem normalizer_le_of_norm_big {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hYb : Big152 Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    (hnorm : ∀ m ∈ M, Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 Y with hP
  set K : Subgroup G := ⨆ m : M, P.map (MulAut.conj (m : G)).toMonoidHom with hK
  have hPM : P ≤ CFSG.Open.pCoreOf 2 M := by
    obtain ⟨Y', hY', hYY'⟩ := Ronan152Six.mem_thetaComponentsIn_of_big h h152 hY hYb hM
    change Y'.map M.subtype = Y at hYY'
    have h1 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hY'.2.1
    have h2 := Subgroup.map_mono (f := M.subtype) h1
    rw [← Sec18.pCoreOf_map M.subtype M.subtype_injective, hYY'] at h2
    exact h2
  have hMO : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hKO : K ≤ CFSG.Open.pCoreOf 2 M := by
    refine iSup_le fun m => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMO m.2) x).mp (hPM hx)
  have hK2 : IsPGroup 2 K := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le hKO
  have hK1 : K ≠ ⊥ := by
    intro h0
    apply hY.prop.2.2
    rw [eq_bot_iff]
    have hle : P.map (MulAut.conj ((1 : M) : G)).toMonoidHom ≤ K :=
      le_iSup (fun m : M => P.map (MulAut.conj (m : G)).toMonoidHom) 1
    rw [h0, Subgroup.coe_one, Late.map_conj_one] at hle
    exact hle
  have hmap : ∀ g : G, K.map (MulAut.conj g).toMonoidHom =
      ⨆ m : M, P.map (MulAut.conj (g * m)).toMonoidHom := by
    intro g
    rw [hK, Subgroup.map_iSup]
    congr 1
    funext m
    rw [Late.map_conj_map_conj]
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := by
    have hle : ∀ g ∈ M, K.map (MulAut.conj g).toMonoidHom ≤ K := fun g hg => by
      rw [hmap]
      exact iSup_le fun m => le_iSup (fun m : M => P.map (MulAut.conj (m : G)).toMonoidHom)
        ⟨g * m, M.mul_mem hg m.2⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hle g hg) ?_
    have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (hle g⁻¹ (M.inv_mem hg))
    rwa [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one] at h2
  have hNK : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hK, Subgroup.map_iSup]
    congr 1
    funext m
    have hnm := hnorm m m.2 hn
    have hO : n ∈ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 (Y.map (MulAut.conj (m : G)).toMonoidHom) : Subgroup G) :
          Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hnm
    rw [Sec18.pCoreOf_map _ (MulAut.conj (m : G)).injective] at hO
    exact Late.map_conj_eq_of_mem_normalizer hO
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hK2 hK1
  have hMeq : M = Subgroup.normalizer (K : Set G) := by
    by_contra hne
    exact hM.1.2 _ (lt_of_le_of_ne hMK hne) hloc
  rw [hMeq]
  exact hNK

theorem normalizer_map_conj_le_big
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A)) (h152 : Item152Big A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y)
    (h7 : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ¬ M ≤ Subgroup.normalizer (Y : Set G) →
      ∀ hAN : A ≤ Subgroup.normalizer (M : Set G),
        letI := ker148_normal hAN
        ¬ Case1487 A (lB A) M)
    {M : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    {m : G} (hm : m ∈ M) :
    Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro n hn
  by_contra hnY
  set Y₁ := Y.map (MulAut.conj m).toMonoidHom with hY₁
  obtain ⟨hYM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hnc := Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hY.prop.1
  have horb : ∀ t ∈ M, A ≤ Subgroup.normalizer
      ((Y.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    fun t ht => le_normalizer_map_conj_of_hasNonCentralThree_big h h152 hY hYb hnc hM ht
  have hMX₀ : M ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A) M) : Set G) :=
    normalizer_le_normalizer_oPrimeResidualOf_delta h149 hM2.1
  have hYX₀ : Y ≤ oPrimeResidualOf 3 (delta A (lB A) M) := le_oPrimeResidualOf_delta hY.prop.1 hYM
  have hconj : ∀ g ∈ M, Y.map (MulAut.conj g).toMonoidHom ≤
      oPrimeResidualOf 3 (delta A (lB A) M) := by
    rintro g hg _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMX₀ hg) y).mp (hYX₀ hy)
  have hX₀N : oPrimeResidualOf 3 (delta A (lB A) M) ≤ Subgroup.normalizer (Y : Set G) :=
    (oPrimeResidualOf_delta_le_of_forall_conj h149 hM2.1 horb).trans
      ((Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le _))
  have hY₁N : Y₁ ≤ Subgroup.normalizer (Y : Set G) := (hconj m hm).trans hX₀N
  have hYN₁ : Y ≤ Subgroup.normalizer (Y₁ : Set G) := by
    intro y hy
    have h1 : m⁻¹ * y * m ∈ Subgroup.normalizer (Y : Set G) :=
      (hconj m⁻¹ (M.inv_mem hm)).trans hX₀N ⟨y, hy, by simp⟩
    have h2 : Y.map (MulAut.conj (m⁻¹ * y * m)).toMonoidHom = Y :=
      Late.map_conj_eq_of_mem_normalizer h1
    have h3 : Y₁.map (MulAut.conj y).toMonoidHom = Y₁ := by
      rw [hY₁, Late.map_conj_map_conj]
      calc Y.map (MulAut.conj (y * m)).toMonoidHom
          = (Y.map (MulAut.conj (m⁻¹ * y * m)).toMonoidHom).map
              (MulAut.conj m).toMonoidHom := by
            rw [Late.map_conj_map_conj, show m * (m⁻¹ * y * m) = y * m by group]
        _ = Y.map (MulAut.conj m).toMonoidHom := by rw [h2]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3
  have hAN₁ : A ≤ Subgroup.normalizer (Y₁ : Set G) := horb m hm
  have hYY₁ : Y ≠ Y₁ := by
    intro he
    apply hnY
    rw [he]
    exact hn
  have hP₁ : CFSG.Open.pCoreOf 2 Y₁ ≠ ⊥ := by
    rw [hY₁, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj m) Y, Ne,
      Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj m).injective]
    exact hY.prop.2.2
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁) hP₁
  obtain ⟨M₁, hle, hM₁⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hN₁ : Subgroup.normalizer (Y₁ : Set G) ≤ M₁ :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₁).trans hle
  have hM₁m : M₁ ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM₁, fun x hx => hN₁ (sup_le hYN₁ hAN₁ hx)⟩
  have hnM₁ : n ∈ M₁ := hN₁ hn
  have hM₁Y : ¬ M₁ ≤ Subgroup.normalizer (Y : Set G) := fun hle' => hnY (hle' hnM₁)
  obtain ⟨hYM₁, hAM₁, hM₁2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM₁m
  have hAN : A ≤ Subgroup.normalizer (M₁ : Set G) := hM₁2.1.2
  let := ker148_normal hAN
  set Yn := Y.map (MulAut.conj n).toMonoidHom with hYn
  have hYθ₁ : Y ∈ thetaComponentsIn M₁ :=
    Ronan152Six.mem_thetaComponentsIn_of_big h h152 hY hYb hM₁m
  have hYnθ₁ : Yn ∈ thetaComponentsIn M₁ :=
    map_conj_mem_thetaComponentsIn (Subgroup.le_normalizer hnM₁) hYθ₁
  have hYYn : Y ≠ Yn := fun he =>
    hnY (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hYθ : Y ∈ thetaComponentsIn M := Ronan152Six.mem_thetaComponentsIn_of_big h h152 hY hYb hM
  have hY₁θ : Y₁ ∈ thetaComponentsIn M :=
    map_conj_mem_thetaComponentsIn (Subgroup.le_normalizer hm) hYθ
  obtain ⟨heq149, -, -⟩ := h149 M₁ hM₁2.1
  have hX₁D : oPrimeResidualOf 3 (delta A (lB A) M₁) ≤ deltaZero A (lB A) M₁ := by
    rw [heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hM₁X₁ : M₁ ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A) M₁) : Set G) :=
    normalizer_le_normalizer_oPrimeResidualOf_delta h149 hM₁2.1
  have hYX₁ : Y ≤ oPrimeResidualOf 3 (delta A (lB A) M₁) :=
    le_oPrimeResidualOf_delta hY.prop.1 hYM₁
  have hYD : Y ≤ deltaZero A (lB A) M₁ := hYX₁.trans hX₁D
  have hYnD : Yn ≤ deltaZero A (lB A) M₁ := by
    refine le_trans ?_ hX₁D
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hM₁X₁ hnM₁) y).mp (hYX₁ hy)
  have hY₁D : Y₁ ≤ deltaZero A (lB A) M₁ := by
    have horb₁ : ∀ t ∈ M, A ≤ Subgroup.normalizer
        ((Y₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
      intro t ht
      rw [hY₁, Late.map_conj_map_conj]
      exact horb (t * m) (M.mul_mem ht hm)
    refine ((hconj m hm).trans ?_).trans hX₁D
    exact (oPrimeResidualOf_delta_le_of_forall_conj h149 hM2.1 horb₁).trans
      (oPrimeResidualOf_mono 3 (delta_mono hN₁))
  have hDM : deltaZero A (lB A) M₁ ≤ M₁ ⊔ A := (deltaZero_le M₁).trans le_sup_left
  have hcYYn : ⁅Y, Yn⁆ ≤ pPrimeCoreOf 3 M₁ :=
    (commutator_le_of_mem_thetaComponentsIn hYθ₁ hYnθ₁ hYYn).trans
      (map_aschbacherSolvableCore_le_pPrimeCoreOf M₁)
  have hcYY₁ : ⁅Y, Y₁⁆ ≤ pPrimeCoreOf 3 M₁ := by
    obtain ⟨hθN, -, hθ3⟩ := map_aschbacherSolvableCore_facts M
    have h1 : ⁅Y, Y₁⁆ ≤ (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y :=
      le_inf (commutator_le_of_mem_thetaComponentsIn hYθ hY₁θ hYY₁)
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hY₁N)
    have h2 : (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y ≤ pPrimeCoreOf 3 Y := by
      refine Sec14.le_pPrimeCoreOf inf_le_right
        (Late.le_normalizer_inf (hYM.trans hθN) Subgroup.le_normalizer) ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
        hθ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact (h1.trans h2).trans (pPrimeCoreOf_le_of_mem_thetaComponentsIn hYθ₁)
  have hcYnY₁ : ⁅Yn, Y₁⁆ ≤ pPrimeCoreOf 3 M₁ := by
    have hY₁n : Y₁.map (MulAut.conj n).toMonoidHom = Y₁ := Late.map_conj_eq_of_mem_normalizer hn
    have hOn : (pPrimeCoreOf 3 M₁).map (MulAut.conj n).toMonoidHom = pPrimeCoreOf 3 M₁ :=
      Late.map_conj_eq_of_mem_normalizer (Sec14.le_normalizer_pPrimeCoreOf 3 M₁ hnM₁)
    rw [hYn, ← hY₁n, ← Subgroup.map_commutator, ← hOn]
    exact Subgroup.map_mono hcYY₁
  have hYp : Group.IsPerfect ↥Y := isPerfect_of_mem_scriptY4 hY.prop.1
  have hYnp : Group.IsPerfect ↥Yn := Group.IsPerfect.map _
  have hY₁p : Group.IsPerfect ↥Y₁ := Group.IsPerfect.map _
  obtain ⟨x, hxY, hx3, y, hyY, hxy⟩ := hnc
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hxy
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _
  have hconj1 : ∀ g : G, MulAut.conj g x ≠ 1 := fun g h1 =>
    hx1 ((MulAut.conj g).injective (h1.trans (map_one _).symm))
  have hconj3 : ∀ g : G, (MulAut.conj g x) ^ 3 = 1 := fun g => by rw [← map_pow, hx3, map_one]
  exact false_of_triple_of_item148 h148 hM₁2.1 (h7 M₁ hM₁m hM₁Y hAN) _ _ _
    (isSubnormal_img_subgroupOf hAM₁ hYθ₁) (isSubnormal_img_subgroupOf hAM₁ hYnθ₁)
    (isPerfect_img_subgroupOf hYD hDM) (isPerfect_img_subgroupOf hYnD hDM)
    (isPerfect_img_subgroupOf hY₁D hDM)
    (img_subgroupOf_ne_bot hYD hDM hxY hx3 hx1)
    (img_subgroupOf_ne_bot hYnD hDM ⟨x, hxY, rfl⟩ (hconj3 n) (hconj1 n))
    (img_subgroupOf_ne_bot hY₁D hDM ⟨x, hxY, rfl⟩ (hconj3 m) (hconj1 m))
    (commutator_img_subgroupOf_eq_bot hYD hYnD hDM hcYYn)
    (commutator_img_subgroupOf_eq_bot hYD hY₁D hDM hcYY₁)
    (commutator_img_subgroupOf_eq_bot hYnD hY₁D hDM hcYnY₁)

theorem claim153TwinNorm_of_big
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A)) (h152 : Item152Big A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y)
    (h7 : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ¬ M ≤ Subgroup.normalizer (Y : Set G) →
      ∀ hAN : A ≤ Subgroup.normalizer (M : Set G),
        letI := ker148_normal hAN
        ¬ Case1487 A (lB A) M) :
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ¬ M ≤ Subgroup.normalizer (Y : Set G) → ∀ m ∈ M,
        Subgroup.normalizer (Y : Set G) ≤
          Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) := by
  intro M hM _ m hm
  have hle := normalizer_map_conj_le_big h h148 h149 h152 hY hYb h7 hM hm
  have hmap : (Subgroup.normalizer (Y : Set G)).map (MulAut.conj m).toMonoidHom =
      Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq Y (MulAut.conj m)
  have hcard : Nat.card (Subgroup.normalizer (Y : Set G)) ≤
      Nat.card (Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) :
        Set G)) := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj m).injective]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge

end Big

theorem twinAt_of_big
    (h148 : Item148R) (h149 : Sec16.Item149S14) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (h152 : Item152Big A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hYb : Big152 Y) : TwinAt A Y := by
  intro M hM hMY
  have h := hR.toSec14Std
  have h149' : Item149 A (lB A) := h149 G A c L h
  have hE : ¬ HasFaithfulE9 Y := by
    intro hE
    apply hMY
    intro t ht
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Ronan152Six.map_conj_eq_of_hasFaithfulE9_big h h152 hY hYb hE hM ht)
  have hnorm := claim153TwinNorm_of_big h (h148 G A c L hR) h149' h152 hY hYb
    (claim153TwinCase7_of_item148R h148 G A c L hR Y hY hE) M hM hMY
  have hNM := normalizer_le_of_norm_big h h152 hY hYb hM hnorm
  have hnc := Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hY.prop.1
  show M ≤ Subgroup.normalizer
    (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)
  rw [← (oPrimeResidualOf_delta_eq_iff_big h h149' h152 hY hYb hnc hM).mpr hNM]
  exact normalizer_le_normalizer_oPrimeResidualOf_delta h149'
    (facts_of_mem_maximalTwoLocalsContaining h hM).2.2.1.1

end CFSG.RankThree.PartTwo.Sec15.Ronan153Big
