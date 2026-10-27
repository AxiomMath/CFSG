module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item14J2

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof15Res4

open Proof152ResW

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem isThreeCentralIn_of_isZCentral {L : Subgroup G} {d : G} (h : IsZCentral L d) :
    ∃ hd : d ∈ L, ∃ S : Sylow 3 ↥L, (⟨d, hd⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hd⟩ : ↥L)} := by
  obtain ⟨S, ⟨S', rfl⟩, hZ⟩ := h
  have hd : d ∈ (Subgroup.center ↥((S' : Subgroup ↥L).map L.subtype)).map
      ((S' : Subgroup ↥L).map L.subtype).subtype := hZ ▸ Subgroup.mem_zpowers d
  obtain ⟨z, hz, rfl⟩ := hd
  obtain ⟨s, hs, hsz⟩ := z.2
  have hdL : ((z : G)) ∈ L := hsz ▸ s.2
  refine ⟨hdL, S', ?_, ?_⟩
  · have : s = ⟨(z : G), hdL⟩ := Subtype.ext hsz
    exact this ▸ hs
  · intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have htS : (t : G) ∈ (S' : Subgroup ↥L).map L.subtype := ⟨t, ht, rfl⟩
    have hc := Subgroup.mem_center_iff.mp hz ⟨t, htS⟩
    apply Subtype.ext
    have := congrArg Subtype.val hc
    simpa using this

theorem exists_conj_of_case2 (hA : Late.IsE27 A) {c' d : G} (hc'A : c' ∈ A) (hc'1 : c' ≠ 1)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : d ∉ Subgroup.zpowers c')
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hab : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)) (h9 : Nat.card (oThreeWStar A) = 9)
    (hΩ : (omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c') ∧ (omegaA A).ncard = 3) ∨
      ∃ a ∈ A, a ∉ Subgroup.zpowers d ∧
        omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c') ∪
          orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6) :
    ∀ b ∈ Subgroup.zpowers d, ∃ w ∈ oThreeWPre A,
      (Subgroup.zpowers c').map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (c' * b) := by
  classical
  set P := oThreeWPre A with hP
  set F := Subgroup.zpowers c' with hF
  set D := Subgroup.zpowers d with hD
  set E := F ⊔ D with hE
  have hc'3 : c' ^ 3 = 1 := hA.1.2 c' hc'A
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hcd : c' ∉ D := not_mem_zpowers_symm hA hc'1 hdA hdc
  have hFD : F ≠ D := fun h => hdc (h ▸ Subgroup.mem_zpowers d)
  have hPN : P ≤ Subgroup.normalizer (A : Set G) := fun w hw =>
    (Holds134.mem_oThreeWPre_iff.mp hw).1
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := hPN.trans hWd
  have hρ : ∀ w (hw : w ∈ P), A.normalizerMonoidHom ⟨w, hPN hw⟩ ∈ oThreeWStar A := fun w hw =>
    (Holds134.mem_oThreeWPre_iff.mp hw).2
  have hfix : ∀ w ∈ P, ∀ g ∈ A, g ^ 3 = 1 → g ≠ 1 →
      w ∈ Subgroup.normalizer (Subgroup.zpowers g : Set G) → w * g * w⁻¹ = g :=
    fun w hw g hgA hg3 hg1 hwg =>
      conj_eq_of_mem_normalizer (hPN hw) (hab.2 _ (hρ w hw)) hgA hg3 hg1 hwg
  have hfixd : ∀ w ∈ P, w * d * w⁻¹ = d := fun w hw => hfix w hw d hdA hd3 hd1 (hPD hw)
  have hcomm : ∀ w₁ ∈ P, ∀ w₂ ∈ P, ∀ y ∈ A,
      w₁ * (w₂ * y * w₂⁻¹) * w₁⁻¹ = w₂ * (w₁ * y * w₁⁻¹) * w₂⁻¹ := by
    intro w₁ h₁ w₂ h₂ y hy
    have hc := congrArg Subtype.val (hab.1.is_comm.comm ⟨_, hρ w₁ h₁⟩ ⟨_, hρ w₂ h₂⟩)
    have hcy := congrArg (fun σ : MulAut ↥A => ((σ ⟨y, hy⟩ : ↥A) : G)) hc
    simpa [Sec4.normalizerMonoidHom_apply_coe] using hcy
  have hfin : (omegaA A).Finite := Set.toFinite _
  have hOF : orbitIn P F ⊆ omegaA A := by
    rcases hΩ with ⟨h, -⟩ | ⟨a, -, -, h, -⟩
    · rw [h]
    · rw [h]
      exact Set.subset_union_left
  have hle6 : (omegaA A).ncard ≤ 6 := by
    rcases hΩ with ⟨-, h⟩ | ⟨a, -, -, -, h⟩ <;> omega
  have hmapF : ∀ w, F.map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (w * c' * w⁻¹) :=
    fun w => by rw [hF, MonoidHom.map_zpowers]; rfl
  have hcardF : ∀ w, Nat.card (F.map (MulAut.conj w).toMonoidHom) = 3 := fun w => by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hF]
    exact Sec13.card_zpowers_of_pow_three hc'3 hc'1
  have hnorm : ∀ w : G, F.map (MulAut.conj w).toMonoidHom = F →
      w ∈ Subgroup.normalizer (F : Set G) := fun w h =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  obtain ⟨h, hhP, hhF, hhA⟩ : ∃ h ∈ P, F.map (MulAut.conj h).toMonoidHom = F ∧
      ¬ ∀ y ∈ A, h * y * h⁻¹ = y := by
    by_contra hno
    push Not at hno
    have h1 : Nat.card (oThreeWStar A) ≤ (orbitIn P F).ncard :=
      card_le_ncard_orbitIn (A := A) (F := F) fun w hw hwF => hno w hw hwF
    have h2 := Set.ncard_le_ncard hOF hfin
    rw [h9] at h1
    omega
  have hhc : h * c' * h⁻¹ = c' := hfix h hhP c' hc'A hc'3 hc'1 (hnorm h hhF)
  have hhd : h * d * h⁻¹ = d := hfixd h hhP
  have hmemE : ∀ w ∈ P, w * c' * w⁻¹ ∈ E := by
    intro w hw
    by_contra hnot
    apply hhA
    have hwc : w * c' * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hPN hw) c').mp hc'A
    have hAeq := eq_sup_of_not_mem hA hc'A hc'1 hdA hd1 hdc hwc hnot
    have hhw : h * (w * c' * w⁻¹) * h⁻¹ = w * c' * w⁻¹ := by
      rw [hcomm h hhP w hw c' hc'A, hhc]
    intro y hy
    rw [hAeq] at hy
    have hyc := mem_centralizer_of_fix hhw hhc hhd hy
    have : h * y = y * h := (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
    rw [this, mul_inv_cancel_right]
  have hpt : ∀ w ∈ P, ∃ b ∈ D, F.map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (c' * b) := by
    intro w hw
    refine exists_eq_zpowers_mul hA hc'A hdA hd1 hcd ?_ (hcardF w) ?_
    · rw [hmapF]
      exact Subgroup.zpowers_le.mpr (hmemE w hw)
    · intro h'
      exact not_mem_orbitIn hPD hFD ⟨w, hw, h'.symm⟩
  obtain ⟨x, hxP, hxF⟩ : ∃ x ∈ P, F.map (MulAut.conj x).toMonoidHom ≠ F := by
    by_contra hno
    push Not at hno
    have horb : orbitIn P F = {F} := by
      ext F'
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hno w hw
      · intro hF'
        rw [Set.mem_singleton_iff] at hF'
        refine ⟨1, one_mem _, ?_⟩
        rw [hF']
        have e : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
          ext y
          simp
        rw [e, Subgroup.map_id]
    rcases hΩ with ⟨hΩe, h3⟩ | ⟨a, haA, had, hΩe, h6⟩
    · rw [hΩe, horb, Set.ncard_singleton] at h3
      omega
    · have hfixc : ∀ w ∈ P, w * c' * w⁻¹ = c' := fun w hw =>
        hfix w hw c' hc'A hc'3 hc'1 (hnorm w (hno w hw))
      have ha1 : a ≠ 1 := fun h1 => had (h1 ▸ one_mem _)
      have ha3 : a ^ 3 = 1 := hA.1.2 a haA
      by_cases haE : a ∈ E
      ·
        have hEc : ∀ w ∈ P, E ≤ Subgroup.centralizer ({w} : Set G) := fun w hw =>
          le_sup_right.trans (mem_centralizer_of_fix (a := 1) (by group) (hfixc w hw)
            (hfixd w hw))
        have horba : orbitIn P (Subgroup.zpowers a) ⊆ {Subgroup.zpowers a} := by
          rintro _ ⟨w, hw, rfl⟩
          rw [Set.mem_singleton_iff, MonoidHom.map_zpowers]
          congr 1
          have : w * a = a * w := (Subgroup.mem_centralizer_singleton_iff.mp
            (hEc w hw haE)).symm
          change w * a * w⁻¹ = a
          rw [this, mul_inv_cancel_right]
        have hsub : omegaA A ⊆ {F, Subgroup.zpowers a} := by
          rw [hΩe, horb]
          exact Set.union_subset (fun _ h => Or.inl h) (horba.trans fun _ h => Or.inr h)
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h2 := Set.ncard_insert_le F {Subgroup.zpowers a}
        rw [Set.ncard_singleton] at h2
        omega
      ·
        have hAeq := eq_sup_of_not_mem hA hc'A hc'1 hdA hd1 hdc haA haE
        have h1 : Nat.card (oThreeWStar A) ≤ (orbitIn P (Subgroup.zpowers a)).ncard :=
          card_le_ncard_orbitIn (A := A) (F := Subgroup.zpowers a) fun w hw hwa y hy => by
            have hwa' : w * a * w⁻¹ = a := hfix w hw a haA ha3 ha1
              (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hwa)
            rw [hAeq] at hy
            have hyc := mem_centralizer_of_fix hwa' (hfixc w hw) (hfixd w hw) hy
            have : w * y = y * w := (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
            rw [this, mul_inv_cancel_right]
        have h2 : orbitIn P (Subgroup.zpowers a) ⊆ omegaA A := by
          rw [hΩe]
          exact Set.subset_union_right
        have h3 := Set.ncard_le_ncard h2 hfin
        rw [h9] at h1
        omega
  have hx3 : x ^ 3 ∈ Subgroup.normalizer (F : Set G) := by
    have hcent : x ^ 3 * c' * (x ^ 3)⁻¹ = c' := by
      have h' := congrArg (fun σ : MulAut ↥A => ((σ ⟨c', hc'A⟩ : ↥A) : G))
        (hab.2 _ (hρ x hxP))
      simp only [MulAut.one_apply] at h'
      rw [← map_pow, show (⟨x, hPN hxP⟩ : ↥(Subgroup.normalizer (A : Set G))) ^ 3 =
        ⟨x ^ 3, pow_mem (hPN hxP) 3⟩ from Subtype.ext (by simp)] at h'
      exact h'
    refine centralizer_singleton_le_normalizer_zpowers c' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 3 * c' = x ^ 3 * c' * (x ^ 3)⁻¹ * x ^ 3 := by group
      _ = c' * x ^ 3 := by rw [hcent]
  have hx2F : F.map (MulAut.conj (x * x)).toMonoidHom ≠ F := by
    intro h'
    apply hxF
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    have h2 := mul_mem (inv_mem (hnorm _ h')) hx3
    have e : (x * x)⁻¹ * x ^ 3 = x := by group
    rwa [e] at h2
  have hx12 : F.map (MulAut.conj (x * x)).toMonoidHom ≠ F.map (MulAut.conj x).toMonoidHom := by
    intro h'
    apply hxF
    have h'' := map_conj_inv_mul_eq h'
    have e : x⁻¹ * (x * x) = x := by group
    rwa [e] at h''
  obtain ⟨b₁, hb₁D, hb₁⟩ := hpt x hxP
  obtain ⟨b₂, hb₂D, hb₂⟩ := hpt (x * x) (mul_mem hxP hxP)
  have hb₁1 : b₁ ≠ 1 := by
    rintro rfl
    apply hxF
    rw [hb₁, mul_one]
  have hb₂1 : b₂ ≠ 1 := by
    rintro rfl
    apply hx2F
    rw [hb₂, mul_one]
  have hb₁₂ : b₁ ≠ b₂ := by
    rintro rfl
    apply hx12
    rw [hb₁, hb₂]
  have hF1 : F.map (MulAut.conj (1 : G)).toMonoidHom = Subgroup.zpowers (c' * 1) := by
    have e : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext y
      simp
    rw [e, Subgroup.map_id, mul_one]
  intro b hb
  rcases eq_of_mem_zpowers_of_pow_three hd3 hb with rfl | rfl | rfl
  · exact ⟨1, one_mem _, hF1⟩
  · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₁D with h1 | h1 | h1
    · exact absurd h1 hb₁1
    · exact ⟨x, hxP, h1 ▸ hb₁⟩
    · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₂D with h2 | h2 | h2
      · exact absurd h2 hb₂1
      · exact ⟨x * x, mul_mem hxP hxP, h2 ▸ hb₂⟩
      · exact absurd (h1.trans h2.symm) hb₁₂
  · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₁D with h1 | h1 | h1
    · exact absurd h1 hb₁1
    · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₂D with h2 | h2 | h2
      · exact absurd h2 hb₂1
      · exact absurd (h1.trans h2.symm) hb₁₂
      · exact ⟨x * x, mul_mem hxP hxP, h2 ▸ hb₂⟩
    · exact ⟨x, hxP, h1 ▸ hb₁⟩

end Proof15Res4

open Proof15Res4 Proof152ResW

theorem step1515HJTrans_of
    (h134 : Item134)
    (h48 : Sec4.Item4_8) : Step1515HJTrans := by
  intro G _ _ A c L hR hJ hΩ d hdA hd1 hdZ a haB had
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD := hR.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA := hD.mem_A
  have hc1 := hD.ne_one
  have hcL : c ∉ L := (j2_point_facts hD hJ).1
  obtain ⟨hdL, S3, hdS, hSd⟩ := isThreeCentralIn_of_isZCentral hdZ
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have hdc : d ∉ Subgroup.zpowers c := by
    intro h
    apply hcd
    rcases eq_of_mem_zpowers_of_pow_three (hA.1.2 c hcA) h with h1 | h1 | h1
    · exact absurd h1 hd1
    · rw [h1]
      exact Subgroup.mem_zpowers c
    · have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
      have : c = d ^ 2 := by
        rw [h1, ← pow_mul]
        calc c = c ^ 3 * c := by rw [hc3, one_mul]
          _ = c ^ (2 * 2) := by rw [← pow_succ]
      rw [this]
      exact pow_mem (Subgroup.mem_zpowers d) 2
  have ha1 : a ≠ 1 := fun h1 => had (h1 ▸ one_mem _)
  have hBA : Subgroup.closure {c, d} ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have haA : a ∈ A :=
    (sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)) (hBA haB)
  obtain ⟨b, hbD, hab⟩ := exists_eq_zpowers_mul hA hcA hdA hd1 hcd
    (Subgroup.zpowers_le.mpr (hBA haB)) (Sec13.card_zpowers_of_pow_three (hA.1.2 a haA) ha1)
    (fun h => had (h ▸ Subgroup.mem_zpowers a))
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hD.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S3, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hD.mem_lA.1 hJq
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hWd, hab', h9, -, hΩ'⟩ | ⟨-, hWd, hΩ', h12⟩
  · exact absurd h1 hΩ
  · have hΩ'' : (omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∧
        (omegaA A).ncard = 3) ∨
        ∃ a ∈ A, a ∉ Subgroup.zpowers d ∧
          omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∪
            orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6 := by
      rcases hΩ' with h3 | ⟨I, -, -, -, a', haAK, had', hΩe, h6, -⟩
      · exact Or.inl h3
      · exact Or.inr ⟨a', haAK.1, had', hΩe, h6⟩
    obtain ⟨w, hwP, hw⟩ := exists_conj_of_case2 hA hcA hc1 hdA hd1 hdc hWd hab' h9 hΩ'' b hbD
    have hwN : w ∈ Subgroup.normalizer (A : Set G) := (Holds134.mem_oThreeWPre_iff.mp hwP).1
    exact ⟨w, hwN, hWd hwN, hw.trans hab.symm⟩
  · obtain ⟨-, hmem⟩ := omegaA_facts_of_case3 hA hcA hc1 hdA hd1 hdc hWd hΩ' h12
    have hb := hmem b hbD
    rw [hΩ'] at hb
    obtain ⟨w, hw, hweq⟩ := hb
    exact ⟨w, hw, hWd hw, hweq.symm.trans hab.symm⟩

end CFSG.RankThree.PartTwo.Sec15
