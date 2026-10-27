module

public import CFSG.RankThree.PartTwo.Sec15.Read148PerfProofPGL
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProofPGU
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.Sporadic.ON
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec15.Read148Perf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Gen

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_sSup_le {S : Set (Subgroup G)} (hS : ∀ Q ∈ S, Q ≤ Y ⊔ A) :
    img148 A Y (sSup S) ≤ sSup (img148 A Y '' S) := by
  set T := sSup (img148 A Y '' S)
  set T' : Subgroup G := (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype
  have hST : sSup S ≤ T' := sSup_le fun Q hQ q hq => by
    refine Subgroup.mem_map.mpr ⟨⟨q, hS Q hQ hq⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    exact le_sSup (Set.mem_image_of_mem (img148 A Y) hQ)
      (mem_img148_iff.mpr ⟨q, hS Q hQ hq, hq, rfl⟩)
  refine (img148_mono hST).trans fun x hx => ?_
  obtain ⟨g, hg, ⟨m, hm, hmg⟩, rfl⟩ := mem_img148_iff.mp hx
  have hm' : m = ⟨g, hg⟩ := Subtype.ext hmg
  rw [← hm']
  exact hm

omit [Finite G] in
theorem img148_deltaZero_le (LB : Subgroup G → Subgroup G) :
    img148 A Y (deltaZero A LB Y) ≤ sSup (img148 A Y '' collectionIn (scriptQZero A LB) Y) :=
  img148_sSup_le fun _ hQ => hQ.2.trans le_sup_left

omit [Finite G] in
theorem img148_gen {LB : Subgroup G → Subgroup G} {Q' : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hQ' : Q' ∈ img148 A Y '' collectionIn (scriptQZero A LB) Y) :
    Q' ≤ img148 A Y (deltaZero A LB Y) ∧ Nat.Coprime (Nat.card Q') 3 ∧
      img148 A Y A ≤ Subgroup.normalizer (Q' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  obtain ⟨Q, hQ, rfl⟩ := hQ'
  obtain ⟨hpi, hAQ, -⟩ := mem_scriptQ_iff.mp hQ.1.1
  refine ⟨img148_mono (le_deltaZero hQ.1 hQ.2), ?_, img148_le_normalizer hAQ⟩
  have h3 := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hpi
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    (Item148PtRes.not_three_dvd_card_img148 h3)).symm

end Gen

theorem isPerfect_of_isSimpleGroup {T : Type*} [Group T] [IsSimpleGroup T]
    (h : ∃ a b : T, a * b ≠ b * a) : Group.IsPerfect T := by
  refine ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T)).resolve_left fun hb => ?_⟩
  obtain ⟨a, b, hab⟩ := h
  rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
  exact hab (Subgroup.mem_centralizer_iff.mp (hb (Subgroup.mem_top b)) a (Subgroup.mem_top a))

theorem isPerfect_of_isSimpleGroup_of_not_prime {T : Type*} [Group T] [IsSimpleGroup T]
    (h : ¬ (Nat.card T).Prime) : Group.IsPerfect T := by
  refine isPerfect_of_isSimpleGroup ?_
  by_contra hc
  push Not at hc
  have : IsMulCommutative T := ⟨⟨fun a b => hc a b⟩⟩
  exact h (Group.is_simple_iff_prime_card.mp inferInstance)

theorem cubeComm_alternatingGroup (n : ℕ) (hn : 5 ≤ n) : CubeComm (alternatingGroup (Fin n)) :=
  have := Y4Core.isSimpleGroup_alternatingGroup n hn
  CubeComm.of_isSimpleGroup (Y4Core.three_dvd_card_alternatingGroup n (by omega))

theorem isPerfect_alternatingGroup_six : Group.IsPerfect (alternatingGroup (Fin 6)) :=
  have := Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)
  isPerfect_of_isSimpleGroup Y4Core.alternatingGroup_six_nonabelian

theorem cube_mem_of_nonempty_mulEquiv {Γ T : Type*} [Group Γ] [Group T] {X : Subgroup Γ}
    (hT : CubeComm T) (h : Nonempty (↥X ≃* T)) : ∀ x ∈ X, x ^ 3 ∈ ⁅X, X⁆ :=
  cubeComm_subgroup_iff.mp (hT.of_mulEquiv h.some)

@[expose] def SevenQAt (A Y : Subgroup G) [(ker148 A Y).Normal] : Prop :=
  ∀ (a₁ a₂ : G) (L₁ L₂ J₁ J₂ : Subgroup G) (p₁ f₁ e₁ p₂ f₂ e₂ : ℕ)
      (_ : Fact p₁.Prime) (_ : Fact p₂.Prime),
    Subgroup.zpowers a₁ ∈ omegaA A → Subgroup.zpowers a₂ ∈ omegaA A →
    L₁ ∈ lA A a₁ → L₂ ∈ lA A a₂ → J₁ ≤ L₁ ⊓ Y → J₂ ≤ L₂ ⊓ Y →
    img148 A Y J₁ ⊔ img148 A Y J₂ = img148 A Y (deltaZero A (lB A) Y) →
    img148 A Y J₁ ⊓ img148 A Y J₂ = ⊥ → ⁅img148 A Y J₁, img148 A Y J₂⁆ = ⊥ →
    1 ≤ f₁ → 1 ≤ e₁ → 1 ≤ f₂ → 1 ≤ e₂ →
    IsZ3PGLThreeAt ↥(img148 A Y (J₁ ⊔ A)) p₁ f₁ →
    IsZ3PGLThreeAt ↥(img148 A Y (J₂ ⊔ A)) p₂ f₂ →
    Sec4.IsoLThreePi (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁) p₁ (f₁ * e₁) →
    Sec4.IsoLThreePi (↥L₂ ⧸ aschbacherSolvableCore 3 ↥L₂) p₂ (f₂ * e₂) →
    2 < p₁ ^ f₁ ∧ 2 < p₂ ^ f₂

theorem sevenQAt {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) :
    letI := ker148_normal hY.2
    SevenQAt A Y := by
  let := ker148_normal hY.2
  intro a₁ a₂ L₁ L₂ J₁ J₂ p₁ f₁ e₁ p₂ f₂ e₂ hp₁ hp₂ _ _ _ _ hJ₁ hJ₂ hsup hinf hcomm hf₁ _ hf₂ _
    hZ₁ hZ₂ _ _
  have hAab : IsMulCommutative A := h.isElemAbelian.1
  have hB : IsMulCommutative ↥(img148 A Y A) := ⟨⟨Sec15.img148_comm hAab⟩⟩
  have hAD : A ≤ Subgroup.normalizer ((deltaZero A (lB A) Y : Subgroup G) : Set G) :=
    le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2
  have hBX := img148_le_normalizer (A := A) (Y := Y) hAD
  have hB27 : Nat.card ↥(img148 A Y A) = 27 :=
    (img148_isE27 (Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE)).2
  rw [img148_sup ((hJ₁.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₁
  rw [img148_sup ((hJ₂.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₂
  have hXS := img148_deltaZero_le (A := A) (Y := Y) (lB A)
  have hSX := fun Q (hQ : Q ∈ img148 A Y '' collectionIn (scriptQZero A (lB A)) Y) =>
    (img148_gen hQ).1
  have hS3 := fun Q (hQ : Q ∈ img148 A Y '' collectionIn (scriptQZero A (lB A)) Y) =>
    (img148_gen hQ).2.1
  have hSB := fun Q (hQ : Q ∈ img148 A Y '' collectionIn (scriptQZero A (lB A)) Y) =>
    (img148_gen hQ).2.2
  have hq : ∀ (p f : ℕ), p.Prime → 1 ≤ f → p ^ f = 2 ∨ 2 < p ^ f := fun p f hp hf => by
    have : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    omega
  rcases hq p₁ f₁ hp₁.out hf₁ with hq₁ | hq₁
  · exact (false_of_isZ3PGLThreeAt_two hsup hinf hcomm hB hBX hB27 hXS hSX hS3 hSB hZ₁
      hq₁).elim
  rcases hq p₂ f₂ hp₂.out hf₂ with hq₂ | hq₂
  · exact (false_of_isZ3PGLThreeAt_two ((sup_comm _ _).trans hsup)
      ((inf_comm _ _).trans hinf) ((Subgroup.commutator_comm _ _).trans hcomm) hB hBX
      hB27 hXS hSX hS3 hSB hZ₂ hq₂).elim
  exact ⟨hq₁, hq₂⟩

section Cases

theorem cube_mem_img148
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (h7 : letI := ker148_normal hY.2; SevenQAt A Y) :
    letI := ker148_normal hY.2
    ∀ x ∈ img148 A Y (deltaZero A (lB A) Y),
      x ^ 3 ∈ ⁅img148 A Y (deltaZero A (lB A) Y), img148 A Y (deltaZero A (lB A) Y)⁆ := by
  let := ker148_normal hY.2
  have hA6 := isPerfect_alternatingGroup_six
  have hA5 := cubeComm_alternatingGroup 5 le_rfl
  rcases (h148 Y hY).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    intro x hx
    rw [Sec15.img148_eq_bot_of_le h1, Subgroup.mem_bot] at hx
    rw [hx, one_pow]
    exact one_mem _
  ·
    obtain ⟨c', -, -, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p, f, e, hp, hf, -, -, hε⟩ | ⟨-, h6' | hφ⟩
    · exact cube_mem_of_nonempty_mulEquiv
        (CubeComm.of_isPerfect (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1).1) hφ
    · exact cube_mem_of_nonempty_mulEquiv (cubeComm_alternatingGroup 7 (by norm_num)) hφ
    · have := Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε
      exact cubeComm_subgroup_iff.mp
        (CubeComm.of_isSimpleGroup (Main148.three_dvd_card_of_isLThreeEpsAt148 hf hε))
    · exact cubeComm_subgroup_iff.mp (CubeComm.of_isTripleCover h6' hA6)
    · exact cube_mem_of_nonempty_mulEquiv hA5 hφ
  ·
    obtain ⟨c', d, L', -, -, -, -, -, -, -, hcases⟩ := h3
    rcases hcases with hON | hCP | hA6A5 | hφ | hφ | ⟨h7'', ⟨φ⟩⟩
    · have := CFSG.Sporadic.ON.fam_on_simplicity.2.2
      have hONp : Group.IsPerfect CFSG.Blueprint.NativeSporadic.ON :=
        isPerfect_of_isSimpleGroup_of_not_prime (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
      exact cubeComm_subgroup_iff.mp (CubeComm.of_isTripleCover hON hONp)
    · obtain ⟨U, V, -, -, hsup, hcomm, -, hU6, hV6⟩ := hCP
      exact cubeComm_subgroup_iff.mp (CubeComm.of_sup hsup hcomm
        (CubeComm.of_isTripleCover hU6 hA6) (CubeComm.of_isTripleCover hV6 hA6))
    · obtain ⟨U, V, hU, hV, hUV, hsup, hU6, ⟨eV⟩⟩ := hA6A5
      have hcomm : ⁅U, V⁆ = ⊥ := le_bot_iff.mp (hUV ▸ Subgroup.commutator_le_inf U V)
      exact cubeComm_subgroup_iff.mp (CubeComm.of_sup hsup hcomm
        (CubeComm.of_isTripleCover hU6 hA6) (hA5.of_mulEquiv eV))
    · exact cube_mem_of_nonempty_mulEquiv (hA5.prod hA5) hφ
    · exact cube_mem_of_nonempty_mulEquiv (cubeComm_alternatingGroup 7 (by norm_num)) hφ
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      have : IsSimpleGroup ↥(img148 A Y (deltaZero A (lB A) Y)) := φ.isSimpleGroup
      exact cubeComm_subgroup_iff.mp
        (CubeComm.of_isSimpleGroup (KFacts.three_dvd_card_of_mulEquiv_projSL φ))
  ·
    obtain ⟨hφ, -, -⟩ := h4
    exact cube_mem_of_nonempty_mulEquiv (cubeComm_alternatingGroup 10 (by norm_num)) hφ
  ·
    obtain ⟨c', -, L', n, m, -, -, hn, -, hiso, -⟩ := h5
    have h3 := Main148.three_dvd_card_of_isoLThreePi148 (by omega) hiso
    have h8 : 2 ^ (3 * n) ≠ 2 := by
      have : 2 ^ 3 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : IsSimpleGroup ↥(img148 A Y (deltaZero A (lB A) Y)) := by
      rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field
          (GaloisField 2 (3 * n))
        exact φ.isSimpleGroup
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n)
          (by omega) h8
        exact φ.isSimpleGroup
    exact cubeComm_subgroup_iff.mp (CubeComm.of_isSimpleGroup h3)
  ·
    obtain ⟨hφ, -, -⟩ := h6
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    have hJ2 : CubeComm CFSG.Blueprint.NativeSporadic.J2 :=
      CubeComm.of_isSimpleGroup (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
    exact cube_mem_of_nonempty_mulEquiv (hA5.prod hJ2) hφ
  ·
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, ha₁, ha₂, hL₁, hL₂, hJ₁,
      hJ₂, hsup, hinf, hcomm, hf₁, he₁, hf₂, he₂, hZ₁, hZ₂, hi₁, hi₂⟩ := h7'
    obtain ⟨hq₁, hq₂⟩ := h7 a₁ a₂ L₁ L₂ J₁ J₂ p₁ f₁ e₁ p₂ f₂ e₂ hp₁ hp₂ ha₁ ha₂ hL₁ hL₂ hJ₁ hJ₂
      hsup hinf hcomm hf₁ he₁ hf₂ he₂ hZ₁ hZ₂ hi₁ hi₂
    have hAab : IsMulCommutative A := h.isElemAbelian.1
    have hB : IsMulCommutative ↥(img148 A Y A) := ⟨⟨Sec15.img148_comm hAab⟩⟩
    have hAD : A ≤ Subgroup.normalizer ((deltaZero A (lB A) Y : Subgroup G) : Set G) :=
      le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2
    rw [img148_sup ((hJ₁.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₁
    rw [img148_sup ((hJ₂.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₂
    exact cube_mem_of_case7 hsup hcomm hB (img148_le_normalizer hAD) hZ₁ hZ₂ hq₁ hq₂

theorem isPerfect_img148
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY A) :
    letI := ker148_normal hY.2
    Group.IsPerfect ↥(img148 A Y (deltaZero A (lB A) Y)) := by
  let := ker148_normal hY.2
  exact Subgroup.isPerfect_iff.mpr (commutator_eq_self_of_cube (img148_deltaZero_le (lB A))
    (fun _ hQ => (img148_gen hQ).1) (fun _ hQ => (img148_gen hQ).2.1)
    (cube_mem_img148 h h148 hY (sevenQAt h hY)))

theorem read148PerfR_of_item148R
    (h148 : Item148R) : Read148PerfR := by
  intro G _ _ A c L h Y hY
  let := ker148_normal hY.2
  obtain ⟨e₀⟩ := Y4Core.nonempty_img148_equiv_map hY.2 (deltaZero_le (LB := lB A) Y)
  have := isPerfect_img148 h.toSec14Std (h148 G A c L h) hY
  exact Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective

theorem y4CoreReadR_from_item148R
    (hSz : KFacts.KPSz)
    (hbot : Item145BotS14) (h148 : Item148R) : Y4CoreReadR :=
  Y4Core.y4CoreReadR_of_item148R hSz hbot h148 (read148PerfR_of_item148R h148)

end Cases

end CFSG.RankThree.PartTwo.Sec15.Read148Perf
