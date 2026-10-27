module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JA5Type
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJExcl
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJSix
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
public import Certificates.Data.A5

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_j2_factor_and_a5_elem {Γ : Type} [Group Γ]
    [Finite Γ] {Z : Subgroup Γ}
    (ψ : ↥Z ≃* alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2) :
    ∃ V : Subgroup Γ, V ≤ Z ∧ Nonempty (↥V ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      (∀ a ∈ Subgroup.normalizer (Z : Set Γ), a ∈ Subgroup.normalizer (V : Set Γ)) ∧
      ∃ u ∈ Z, u ^ 3 = 1 ∧ u ≠ 1 ∧ u ∉ V ∧ ∀ v ∈ V, u * v = v * u := by
  set K : Subgroup ↥Z :=
    ((MonoidHom.fst (alternatingGroup (Fin 5)) CFSG.Blueprint.NativeSporadic.J2).comp
      ψ.toMonoidHom).ker with hKdef
  have hK : ∀ x : ↥Z, x ∈ K ↔ (ψ x).1 = 1 := fun x => MonoidHom.mem_ker
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_mem_iff ψ K hK
  set V : Subgroup Γ := K.map Z.subtype with hVdef
  have eV : ↥V ≃* ↥K := (K.equivMapOfInjective Z.subtype Z.subtype_injective).symm
  have hVZ : V ≤ Z := Subgroup.map_subtype_le K
  have hVmem : ∀ g (hg : g ∈ Z), g ∈ V ↔ (ψ ⟨g, hg⟩).1 = 1 := by
    intro g hg
    constructor
    · rintro ⟨x, hx, hxg⟩
      have : x = ⟨g, hg⟩ := Subtype.ext hxg
      rw [← this]
      exact (hK x).mp hx
    · intro h
      exact ⟨⟨g, hg⟩, (hK _).mpr h, rfl⟩
  have hkey : ∀ g ∈ Z, g ^ 7 = 1 → g ∈ V := by
    intro g hg h7
    have hx : (⟨g, hg⟩ : ↥Z) ^ 7 = 1 := Subtype.ext (by simpa using h7)
    have hψ : ψ ⟨g, hg⟩ ^ 7 = 1 := by rw [← map_pow, hx, map_one]
    exact (hVmem g hg).mpr (fst_eq_one_of_pow_seven_eq_one
      CFSG.RankThree.PartTwo.Sec14.Item148HJ.card_alternatingGroup_five hψ)
  have e := eV.trans eK
  have hs : IsSimpleGroup ↥V := isSimpleGroup_of_mulEquiv_j2 e
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN := mem_normalizer_of_pow_seven hVZ hkey (closure_pow_eq_top (seven_dvd_card_of_mulEquiv_j2 e))
  set σ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := Subtype.ext (by decide)
  have hσ1 : σ ≠ 1 := fun h => by
    have h' := congrArg Subtype.val h
    revert h'
    decide
  set u' : ↥Z := ψ.symm (σ, 1) with hu'
  have hψu : ψ u' = (σ, 1) := MulEquiv.apply_symm_apply ψ _
  refine ⟨V, hVZ, ⟨e⟩, hN, (u' : Γ), u'.2, ?_, ?_, ?_, ?_⟩
  · have h1 : u' ^ 3 = 1 := by
      apply ψ.injective
      rw [map_pow, hψu, map_one, Prod.pow_mk, hσ3, one_pow]
      rfl
    simpa using congrArg Subtype.val h1
  · intro h
    apply hσ1
    have h1 : u' = 1 := Subtype.ext h
    have h2 := congrArg ψ h1
    rw [hψu, map_one] at h2
    exact congrArg Prod.fst h2
  · intro h
    have h1 := (hVmem _ u'.2).mp h
    apply hσ1
    have : (⟨(u' : Γ), u'.2⟩ : ↥Z) = u' := rfl
    rw [this, hψu] at h1
    exact h1
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hx1 : (ψ x).1 = 1 := (hK x).mp hx
    have hcomm : u' * x = x * u' := by
      apply ψ.injective
      rw [map_mul, map_mul, hψu]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul, hx1, mul_one, one_mul]
      · simp only [Prod.snd_mul, one_mul, mul_one]
    exact congrArg Subtype.val hcomm

section Certificates


@[expose] def Step148HJA5Cent2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → ∀ hAJ : A ≤ Subgroup.normalizer (J : Set G),
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)) →
        b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        img148 A Y (deltaZero A (lB A) Y) =
          img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) →
        img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≠ ⊥ →
        (letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ);
          ¬ Case148Three A (lB A) (centPre148 A Y J)) ∧
          (Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
              CFSG.Blueprint.NativeSporadic.J2) → (omegaA A).ncard = 6)

theorem not_case148Six_of_a5
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {J Yd : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hYdJ : Yd ≤ J) (hYdt : YdType148 d Yd)
    (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    letI := ker148_normal hY.2
    img148 A Y Yd = img148 A Y J →
    Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
    b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
    (letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ);
      ¬ Case148Six A (lB A) (centPre148 A Y J)) := by
  intro heq hJ5 hbc
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  obtain ⟨φ⟩ := hJ5
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h60 : Nat.card (img148 A Y J) = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [h60]; norm_num
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hbJ := HJRes2.le_centralizer_of_theta hYdM heq hJθ hbA hbc.2
  have hdJ := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hBJ : img148 A Y B ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hc.1]
    have hS' : ({b, d} : Set G) ⊆ (Y ⊔ A : Subgroup G) := by
      rintro g (rfl | rfl)
      · exact Subgroup.mem_sup_right hbA
      · exact Subgroup.mem_sup_right hdA
    refine img148_closure_le_centralizer hS' fun g hg => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hbJ hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hdJ hx)
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAp : IsPGroup 3 ↥(img148 A Y A) := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hjJ, hj1, hj3, hjC⟩ := exists_pow_eq_one_mem_centralizer hAp hAJα h3Jα
  have hjA : j ∈ img148 A Y A := hF3 j hjC hj3
  have hjZ : ∃ y ∈ img148 A Y J, j * y ≠ y * j := by
    by_contra hcon
    push Not at hcon
    apply hj1
    have hz : (⟨j, hjJ⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcon g g.2).symm
    rw [hJZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hjB : j ∉ img148 A Y B := fun hjB' => by
    obtain ⟨y, hy, hjy⟩ := hjZ
    exact hjy (Subgroup.mem_centralizer_iff.mp (hBJ hjB') y hy).symm
  obtain ⟨hBA, -, hmax⟩ := img148_hyperplane_max (Y := Y) hA hB
  have hAeq : img148 A Y B ⊔ Subgroup.zpowers j = img148 A Y A := by
    rcases hmax _ le_sup_left (sup_le hBA (Subgroup.zpowers_le.mpr hjA)) with h | h
    · exact absurd (h ▸ (le_sup_right : Subgroup.zpowers j ≤ _) (Subgroup.mem_zpowers j)) hjB
    · exact h
  have hCB : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = img148 A Y B := by
    rcases hmax _ (le_inf hBA hBJ) inf_le_left with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hjy⟩ := hjZ
      have hjC' : j ∈ img148 A Y A ⊓
          Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [h]; exact hjA
      exact hjy (Subgroup.mem_centralizer_iff.mp hjC'.2 y hy).symm
  have hB9 : Nat.card (img148 A Y B) = 9 := by
    rw [card_img148_of_le hA.1.2 hB.1]
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hZC : Zα ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((Zα : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  have hAZB : img148 A Y A ⊓ Zα ≤ img148 A Y B := fun x hx => hCB ▸ ⟨hx.1, hZC hx.2⟩
  have hjZα : ∀ z ∈ Zα, j * z = z * j := fun z hz =>
    Subgroup.mem_centralizer_iff.mp (hZC hz) j hjJ
  intro h6
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  obtain ⟨⟨χ⟩, -, -⟩ := h6
  obtain ⟨V, hVZ, ⟨ψV⟩, hVN, u, huZ, hu3, hu1, huV, huc⟩ :=
    exists_j2_factor_and_a5_elem (e.symm.trans χ)
  have hAV : img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun a ha => hVN a (hAN ha)
  have hAVB : img148 A Y A ⊓ V ≤ img148 A Y B := fun x hx => hAZB ⟨hx.1, hVZ hx.2⟩
  rcases card_le_of_le_isE27 hAE (inf_le_left : img148 A Y A ⊓ V ≤ img148 A Y A) with
    h | h | h | h
  ·
    have hj3' : Nat.card (Subgroup.zpowers j) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hj3 hj1
    refine false_of_j2_of_le hAab hA3 hF3 hj3' ?_ hAV ψV
    rw [Subgroup.eq_bot_of_card_eq _ h]
    exact bot_le
  · exact false_of_j2_of_le hAab hA3 hF3 h le_rfl hAV ψV
  ·
    have hVB : img148 A Y A ⊓ V = img148 A Y B :=
      Subgroup.eq_of_le_of_card_ge hAVB (by rw [h, hB9])
    have huA : u ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      have hle : img148 A Y A ≤ Subgroup.centralizer ({u} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [← hAeq]
        refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.mpr ?_)
        · have hxV : x ∈ V := (hVB ▸ hx : x ∈ img148 A Y A ⊓ V).2
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (huc x hxV).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hjZα u huZ
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    have huB : u ∈ img148 A Y B := hAZB ⟨hF3 u huA hu3, huZ⟩
    exact huV (hVB ▸ huB : u ∈ img148 A Y A ⊓ V).2
  · have := Subgroup.card_le_of_le hAVB
    rw [h, hB9] at this
    omega

theorem step148HJA5Cent_of_cent2
    (hR : Step148HJA5Cent2) :
    Step148HJA5Cent := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne
  obtain ⟨h3, h6⟩ := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
    hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne
  exact ⟨⟨h3, not_case148Six_of_a5 hS hY hB hc hJ hAJ hYdJ hYdt hdc heq hJ5 hbc⟩, h6⟩

theorem step148HJA5Inner2_of_cent2
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Step148HJA5Cent2) :
    Step148HJA5Inner2 :=
  step148HJA5Inner2_of_cent h142 h134 h48 (step148HJA5Cent_of_cent2 hR)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
