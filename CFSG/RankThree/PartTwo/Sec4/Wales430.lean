module

public import CFSG.RankThree.PartTwo.Sec4.Statements430L3
public import CFSG.RankThree.PartTwo.KFacts.KF430LieP
public import CFSG.RankThree.PartTwo.KFacts.KF430ON
import CFSG.RankThree.PartTwo.Sec4.Wales430Heis
import CFSG.RankThree.PartTwo.Sec4.Wales430Inner
import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailPoint
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.RankThree.PartTwo.Sec4.Statements417
public import CFSG.RankThree.PartTwo.Sec4.Statements430

public section

namespace CFSG.RankThree.PartTwo.Sec4.Proof430

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem zmod4_pow_six_ne_one : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 6 ≠ 1 := by
  decide

private theorem quaternion_pow_six_ne_one : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 6 ≠ 1 := by
  decide

private theorem dihedral_pow_six_ne_one : (DihedralGroup.r 1 : DihedralGroup 4) ^ 6 ≠ 1 := by
  decide

private theorem semidihedral_pow_six_ne_one : (CFSG.Semidihedral.r 4) ^ 6 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by norm_num) (by
    rw [CFSG.Semidihedral.orderOf_r 4 (by norm_num)]
    decide)

private theorem exists_GL_pow_six_ne_one : ∃ g : GL (Fin 2) (ZMod 3), g ^ 6 ≠ 1 := by
  let J : GL (Fin 2) (ZMod 3) := ⟨!![0, 2; 1, 0], !![0, 1; 2, 0], by decide, by decide⟩
  refine ⟨J, fun h => ?_⟩
  have := congrArg (fun u : GL (Fin 2) (ZMod 3) => (u : Matrix (Fin 2) (Fin 2) (ZMod 3))) h
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
  revert this
  decide

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (h : Subgroup.center Y = ⊥) (e : X ≃* Y) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [h, Subgroup.mem_bot] at hez
  exact Subgroup.mem_bot.mpr (e.injective (by rw [hez, map_one]))

private theorem center_M24_eq_bot :
    Subgroup.center NativeSporadic.M24 = ⊥ := by
  have : IsSimpleGroup NativeSporadic.M24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.Mathieu.card_M24]
  norm_num

private theorem center_He_eq_bot :
    Subgroup.center NativeSporadic.He = ⊥ := by
  have : IsSimpleGroup NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.He.card_He]
  norm_num

private theorem not_mem_of_center_eq_bot {L : Subgroup G} {a : G}
    (haC : a ∈ Subgroup.centralizer (L : Set G)) (ha1 : a ≠ 1) (hcen : Subgroup.center ↥L = ⊥) :
    a ∉ L := by
  intro haL
  have hmem : (⟨a, haL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp haC g g.2)
  rw [hcen, Subgroup.mem_bot] at hmem
  exact ha1 (congrArg Subtype.val hmem)

theorem item4_30_of
    (h417 : Item4_17) (h45 : Item4_5) (hLieP : KF430LieP) (hON : KF430ON)
    (hL3 : Step430L3) : Item4_30 := by
  intro G _ _ hG hEF hθ A hA L hL a hCA ha3 c hcA hca B hsup hinf hWc hWB R hR hR1 hRc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAab, h27⟩ := id hA
  obtain ⟨hRL, hRpi, hAR⟩ := id hR
  have haA : a ∈ A := (hCA ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).1
  have haC : a ∈ Subgroup.centralizer (L : Set G) :=
    (hCA ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).2
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha3
    omega
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hc3 : c ^ 3 = 1 := hAab.2 c hcA
  have hLa : L ≤ Subgroup.centralizer ({a} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp haC l hl)
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRpi
  have hAE : A ∈ partTwoE G := ⟨hAab, h27, R, hR1, hR2, hAR⟩
  have hAF : A ∈ partTwoF G := hEF ▸ hAE
  have hAmax : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A := fun x hx3 hxA =>
    Sec15.mem_of_mem_partTwoF hAF hx3 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hxA y hy).symm
  have hO2 : CFSG.pCore 2 G = ⊥ := by
    have h := (solvable_prime_complement_core_characterization (H := G)
      Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
    rw [hθ] at h
    exact le_bot_iff.mp h
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A hA3 (Or.inr ⟨hAab, 3, le_rfl, h27.trans (by norm_num)⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have hBA : B ≤ A := (le_sup_right : B ≤ Subgroup.zpowers c ⊔ B).trans hsup.le
  have hB9 : Nat.card B = 9 := by
    have hc' : ∀ u ∈ Subgroup.zpowers c, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
      hcomm u (Subgroup.zpowers_le.mpr hcA hu) v (hBA hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc'
    rw [hsup, h27, hinf, Subgroup.card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hc3 hc1] at hcard
    omega
  have hcB : c ∉ B := fun h => by
    have hmem : c ∈ Subgroup.zpowers c ⊓ B := ⟨Subgroup.mem_zpowers c, h⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hac : a ∉ Subgroup.zpowers c := by
    intro h
    apply hca
    have heq : Subgroup.zpowers a = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h) (le_of_eq (by
        rw [Sec13.card_zpowers_of_pow_three hc3 hc1, Nat.card_zpowers, ha3]))
    rw [heq]
    exact Subgroup.mem_zpowers c
  have hRA : ¬ R ≤ Subgroup.centralizer (A : Set G) := by
    intro hle
    have h : ⁅R, Subgroup.zpowers c⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hle.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
          (Subgroup.zpowers_le.mpr hcA))))
    rw [hRc] at h
    exact hR1 h
  have hquad : IsQuad417 L A A a 3 :=
    ⟨⟨hAab, fun ⦃X⦄ hX hAX => (hAF.2.1 X hX hAX).le⟩, h27.trans (by norm_num), hCA, ha3,
      ⟨hAab, h27⟩, le_rfl, R, hR, hRA⟩
  have hstar : ∀ (A' E' : Subgroup G) (c' : G) (m : ℕ), IsQuad417 L A' E' c' m → m ≤ 4 := by
    rintro A' E' c' m ⟨hA'max, hA'card, -, -, ⟨hE'ab, hE'27⟩, hE'A', T, ⟨-, hTpi, hE'T⟩, hTE'⟩
    have hT1 : T ≠ ⊥ := by
      rintro rfl
      exact hTE' bot_le
    have hE'E : E' ∈ partTwoE G :=
      ⟨hE'ab, hE'27, T, hT1, (isPiSubgroup_piOf_iff Nat.prime_two T).mp hTpi, hE'T⟩
    have hE'F : E' ∈ partTwoF G := hEF ▸ hE'E
    have heq : A' = E' := hE'F.2.1 A' hA'max.prop hE'A'
    rw [heq, hE'27] at hA'card
    have h3 : (3 : ℕ) ^ 3 = 3 ^ m := by
      rw [← hA'card]
      norm_num
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
    omega
  have hdih : Subgroup.center ↥L = ⊥ → autIn L A ≃* DihedralGroup 6 → False := fun hcen e =>
    false_of_autIn_dihedral hAab h27 haA hcA ha1 hc1 hca hAL hLa hWc hWB hBA hB9 hcB
      (not_mem_of_center_eq_bot haC ha1 hcen) e
  have hsix : ∀ {Q : Type} [Group Q], autIn L A ≃* Q → ∀ q : Q, q ^ 6 ≠ 1 → False :=
    fun e _ hq => Sec13.Item134Arg128Fail.false_of_autIn_pow_six hAab h27 hWc haA hcA hc1 hac
      hLa e hq
  have hGL : autIn L A ≃* GL (Fin 2) (ZMod 3) → False := fun e => by
    obtain ⟨g, hg⟩ := exists_GL_pow_six_ne_one
    exact hsix e g hg
  have hlie : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      (ChevalleyExceptionalModel ↥L .G2 p 1 ∨ Nonempty (L ≃* projSp 2 (GaloisField p 1)) ∨
        (p % 3 = 1 ∧ Nonempty (L ≃* projSU 4 p 1)) ∨
        (p % 3 = 2 ∧ Nonempty (L ≃* projSL 4 (GaloisField p 1)))) → False := by
    intro p _ hp3 hcase
    obtain ⟨hinn, hcen, hV⟩ := hLieP p hp3 ↥L hcase
    exact false_of_inner_of_automizer hAab h27 hAmax hAL hcA hCA ha3 hca hWc hWB hBA hB9 hcB
      (not_mem_of_center_eq_bot haC ha1 hcen) hcen hinn hV
  have hres : IsL3Case417 L A →
      (∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) ∨
        Nonempty (L ≃* NativeSporadic.M12) ∨ Nonempty (L ≃* NativeSporadic.J2) :=
    hL3 G hG hEF hθ A hA L hL a hCA ha3 c hcA hca B hsup hinf hWc hWB R hR hR1 hRc
  rcases h417 G hG hO2 L hL hstar A A a 3 hquad with h1 | ⟨-, hH, -⟩ | ⟨-, p, hp, hp3, hLie⟩ |
      ⟨-, -, ⟨e4⟩⟩ | ⟨h5, -⟩ | ⟨-, htab⟩ | ⟨h7, -⟩ | ⟨-, hT⟩ | ⟨-, h9, hS3⟩ |
      ⟨-, ⟨n, -, -, h10⟩, ⟨e10⟩⟩ | ⟨-, -, ⟨e11⟩⟩ | ⟨h12, -⟩ | ⟨h13, -⟩
  · exact Or.inl h1
  · exact (false_of_isHeisCentral hAab h27 hAmax hL.1.1 haA hcA hCA ha3 hca hWc hH).elim
  · rcases hLie with h | h | h | h | h
    · exact (hlie p hp3 (Or.inl h)).elim
    · exact (hlie p hp3 (Or.inr (Or.inl h))).elim
    · exact (hlie p hp3 (Or.inr (Or.inr (Or.inl h)))).elim
    · exact (hlie p hp3 (Or.inr (Or.inr (Or.inr h)))).elim
    · exact hres (Or.inl ⟨p, hp, hp3, h⟩)
  · exact (hsix e4 _ zmod4_pow_six_ne_one).elim
  · exact absurd h5 (by norm_num)
  · rcases htab with ⟨hM12, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨⟨eM⟩, hMe⟩ | ⟨hJ2, -⟩ |
        ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨⟨eH⟩, hHe⟩ | ⟨-, ⟨e⟩⟩
    · exact Or.inr (Or.inl hM12)
    · exact (hsix e _ quaternion_pow_six_ne_one).elim
    · exact (hsix e _ semidihedral_pow_six_ne_one).elim
    · have hcen : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv center_M24_eq_bot eM
      rcases hMe with he | he
      · obtain ⟨e⟩ := he
        exact (hdih hcen e).elim
      · obtain ⟨e⟩ := he
        exact (hGL e).elim
    · exact Or.inr (Or.inr hJ2)
    · exact (hGL e).elim
    · exact (hsix e _ semidihedral_pow_six_ne_one).elim
    · have hcen : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv center_He_eq_bot eH
      rcases hHe with he | he
      · obtain ⟨e⟩ := he
        exact (hdih hcen e).elim
      · obtain ⟨e⟩ := he
        exact (hGL e).elim
    · exact (hGL e).elim
  · exact absurd h7 (by norm_num)
  · exact (hON G A L a c hAab h27 hAmax hAL hL.1.1 hT hCA ha3 hcA hca
      (fun n hn => hWc hn.2)).elim
  · exact hres (Or.inr ⟨h9, hS3⟩)
  · have hcen : Subgroup.center ↥L = ⊥ := by
      rcases h10 with h | h
      · exact (CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions h).1
      · exact (CFSG.QuasithinUnique.Setup.X6.even_triality_model_two_extensions h).1
    exact (hdih hcen e10).elim
  · exact (hsix e11 _ dihedral_pow_six_ne_one).elim
  · exact absurd h12 (by norm_num)
  · exact absurd h13 (by norm_num)

end CFSG.RankThree.PartTwo.Sec4.Proof430
