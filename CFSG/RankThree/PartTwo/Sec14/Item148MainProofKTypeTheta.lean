module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

namespace Main148

theorem isSimpleGroup_of_isQuasisimple_of_center148 {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (hZ : Subgroup.center Q = ⊥) : IsSimpleGroup Q := by
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  exact MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

noncomputable abbrev phi148 {K : Subgroup G} (hKM : K ≤ Y ⊔ A) :
    ↥K →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
  (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hKM)

omit [Finite G] in
theorem range_phi148 {K : Subgroup G} (hKM : K ≤ Y ⊔ A) : (phi148 hKM).range = img148 A Y K := by
  rw [phi148, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

omit [Finite G] in
theorem phi148_eq_one_iff {K : Subgroup G} (hKM : K ≤ Y ⊔ A) (k : ↥K) :
    phi148 hKM k = 1 ↔ (k : G) ∈ pPrimeCoreOf 3 Y := by
  rw [phi148, MonoidHom.comp_apply, mk'_ker148_eq_one_iff]
  rfl

theorem not_three_dvd_card_ker_phi148 {K : Subgroup G} (hKM : K ≤ Y ⊔ A) :
    ¬ 3 ∣ Nat.card ↥(phi148 hKM).ker := by
  intro h3
  have hle : ((phi148 hKM).ker).map K.subtype ≤ pPrimeCoreOf 3 Y := by
    rintro _ ⟨k, hk, rfl⟩
    exact (phi148_eq_one_iff hKM k).mp hk
  rw [← Subgroup.card_map_of_injective K.subtype_injective] at h3
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
    (h3.trans (Subgroup.card_dvd_of_le hle))

theorem nonempty_img148_equiv_theta {K : Subgroup G} (hKM : K ≤ Y ⊔ A)
    (hθ : inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y)
    (hs : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (h3 : 3 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K)) :
    Nonempty (↥(img148 A Y K) ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  set φ := phi148 (A := A) (Y := Y) hKM with hφ
  have hker : φ.ker = aschbacherSolvableCore 3 ↥K := by
    apply le_antisymm
    ·
      have hn : (φ.ker.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K))).Normal :=
        (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective _)
      rcases hn.eq_bot_or_eq_top with hb | ht
      · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
      · exfalso
        have h1 : 3 ∣ Nat.card ↥(φ.ker.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K))) := by
          rw [ht, Subgroup.card_top]
          exact h3
        exact not_three_dvd_card_ker_phi148 hKM (h1.trans (Subgroup.card_map_dvd _ _))
    · intro k hk
      rw [MonoidHom.mem_ker, hφ, phi148_eq_one_iff]
      exact hθ ⟨k, hk, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans
      (MulEquiv.subgroupCongr (range_phi148 hKM)))).symm⟩

theorem theta_le_of_isSimpleGroup_img148 {K : Subgroup G} (hKM : K ≤ Y ⊔ A)
    (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (hs : IsSimpleGroup ↥(img148 A Y K)) (hnc : ∃ a b : ↥(img148 A Y K), a * b ≠ b * a) :
    inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y ∧
      Nonempty (↥(img148 A Y K) ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  set φ := phi148 (A := A) (Y := Y) hKM with hφ
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  obtain ⟨hθs, -, -, -⟩ := solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have hθn : θK.Normal := by
    have := (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.1
    exact Subgroup.normal_of_characteristic θK
  have hns : ¬ Group.IsSolvable ↥(img148 A Y K) := by
    intro hsol
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hθker : θK ≤ φ.ker := by
    set ψ := φ.rangeRestrict with hψ
    have hn : (θK.map ψ).Normal := hθn.map ψ φ.rangeRestrict_surjective
    have hsr : IsSimpleGroup ↥φ.range := by
      rw [range_phi148 hKM]
      exact hs
    rcases hn.eq_bot_or_eq_top with hb | ht
    · rw [Subgroup.map_eq_bot_iff] at hb
      intro k hk
      have := hb hk
      rw [MonoidHom.mem_ker] at this ⊢
      exact congrArg Subtype.val this
    · exfalso
      apply hns
      have hsol : Group.IsSolvable ↥(θK.map ψ) :=
        Group.isSolvable_of_surjective (f := ψ.subgroupMap θK) (ψ.subgroupMap_surjective θK)
      rw [ht] at hsol
      have hsol' : Group.IsSolvable ↥φ.range :=
        Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥φ.range) ≃* _).toMonoidHom)
          (MulEquiv.surjective _)
      have e : ↥φ.range ≃* ↥(img148 A Y K) := MulEquiv.subgroupCongr (range_phi148 hKM)
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hkerθ : φ.ker ≤ θK := by
    set T := φ.ker.map (QuotientGroup.mk' θK) with hT
    have hTn : T.Normal := (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective _)
    have hT3 : ¬ 3 ∣ Nat.card ↥T := fun h3 =>
      not_three_dvd_card_ker_phi148 hKM (h3.trans (Subgroup.card_map_dvd _ _))
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hTn with htop | hcen
    · exfalso
      have hall : ∀ k : ↥K, φ k = 1 := by
        intro k
        have hk : (QuotientGroup.mk' θK k) ∈ T := htop ▸ Subgroup.mem_top _
        obtain ⟨k', hk', hkk'⟩ := hk
        have h1 : k'⁻¹ * k ∈ θK := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkk'
          exact hkk'
        have h2 := hθker h1
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp hk', inv_one, one_mul] at h2
        exact h2
      have hbot : img148 A Y K = ⊥ := by
        rw [← range_phi148 hKM, eq_bot_iff]
        rintro _ ⟨k, rfl⟩
        exact Subgroup.mem_bot.mpr (hall k)
      have : Nontrivial ↥(img148 A Y K) := hs.toNontrivial
      exact (Subgroup.nontrivial_iff_ne_bot _).mp this hbot
    ·
      have hTs : Group.IsSolvable ↥T := by
        refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
        exact (Subgroup.mem_center_iff.mp (hcen b.2) a)
      have hle := (solvable_prime_complement_core_characterization (H := ↥K ⧸ θK)
        Nat.prime_three).2.2.2.1 T hTn hTs hT3
      rw [(theta_quotient_core_and_ranks (G := ↥K)).1, le_bot_iff, hT, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk'] at hle
      exact hle
  have hker : φ.ker = θK := le_antisymm hkerθ hθker
  refine ⟨fun x hx => ?_, ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans
      (MulEquiv.subgroupCongr (range_phi148 hKM)))).symm⟩⟩
  obtain ⟨k, hk, rfl⟩ := hx
  exact (phi148_eq_one_iff hKM k).mp (hθker hk)

end Quot

theorem isSimpleGroup_of_isLThreeEpsAt148 {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (h : IsLThreeEpsAt X p f) : IsSimpleGroup X := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
    exact MulEquiv.isSimpleGroup φ
  · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
    exact MulEquiv.isSimpleGroup φ

theorem isLThreeEpsAt_congr148 {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {p f : ℕ}
    [Fact p.Prime] (h : IsLThreeEpsAt X p f) : IsLThreeEpsAt X' p f := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Or.inl ⟨e.symm.trans φ⟩
  · exact Or.inr ⟨hq, ⟨e.symm.trans φ⟩⟩

theorem isSimpleGroup_of_mem_lA148
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {e : G} {Le : Subgroup G} (he : Subgroup.zpowers e ∈ omegaA A)
    (hLe : Le ∈ lA A e) : IsSimpleGroup (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) :=
  isSimpleGroup_of_isQuasisimple_of_center148 (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe.1)
    (Sec15.center_eq_bot_of_types hLe.1 (h.chosen136.2 e he Le hLe).1)

theorem isSimpleGroup_a7_148 :
    IsSimpleGroup (alternatingGroup (Fin 7)) ∧ 3 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  refine ⟨alternatingGroup.isSimpleGroup (by simp), ?_⟩
  rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  norm_num

theorem isSimpleGroup_l37_148 (h7 : Fact (Nat.Prime 7)) :
    IsSimpleGroup (projSL 3 (GaloisField 7 1)) ∧ 3 ∣ Nat.card (projSL 3 (GaloisField 7 1)) :=
  ⟨Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1),
    KFacts.three_dvd_card_of_mulEquiv_projSL (MulEquiv.refl _)⟩

theorem img148_equiv_of_theta {A Y K : Subgroup G} [(ker148 A Y).Normal] (hKM : K ≤ Y ⊔ A)
    (hθ : inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y) {X : Type} [Group X]
    (hX : IsSimpleGroup X) (hX3 : 3 ∣ Nat.card X)
    (φ : ↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* X) : Nonempty (↥(img148 A Y K) ≃* X) := by
  have hs : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := MulEquiv.isSimpleGroup φ
  have h3 : 3 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
    rwa [Nat.card_congr φ.toEquiv]
  obtain ⟨ψ⟩ := nonempty_img148_equiv_theta hKM hθ hs h3
  exact ⟨ψ.trans φ⟩

theorem theta_equiv_of_img148 {A Y K : Subgroup G} [(ker148 A Y).Normal] (hKM : K ≤ Y ⊔ A)
    (hKp : Group.IsPerfect ↥K) (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    {X : Type} [Group X] (hX : IsSimpleGroup X) (φ : ↥(img148 A Y K) ≃* X) :
    inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y ∧
      Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* X) := by
  have hs : IsSimpleGroup ↥(img148 A Y K) := MulEquiv.isSimpleGroup φ
  have : Nontrivial ↥(img148 A Y K) := hs.toNontrivial
  obtain ⟨hθ, ⟨ψ⟩⟩ := theta_le_of_isSimpleGroup_img148 hKM hKq hs
    (exists_ne_comm_of_isPerfect (isPerfect_img148 hKM))
  exact ⟨hθ, ⟨ψ.symm.trans φ⟩⟩

end Main148

open Main148

@[expose] def Step148KTheta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
        inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y

@[expose] def Step148KThetaOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
          ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                projSL 3 (GaloisField 5 2))) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                projSU 3 5 1))) ∧
            Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* alternatingGroup (Fin 7))) ∨
          (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
            Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
            IsLThreeEpsAt (↥K ⧸ aschbacherSolvableCore 3 ↥K) p f)

@[expose] def Step148KThetaON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → c' ∈ B →
        L' ∈ lA A c' →
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        IsThreeCentralIn L' e →
        Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON →
        Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃*
            projSL 3 (GaloisField 7 1)))

theorem step148KType_of_theta
    (hθ : Step148KTheta) (hΩ : Step148KThetaOmega)
    (hON : Step148KThetaON) : Step148KType := by
  refine step148KType_of ?_ ?_
  · intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe
    let := ker148_normal hY.2
    have hKM : K ≤ Y ⊔ A :=
      ((le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1).trans inf_le_left).trans le_sup_left
    have hθK := hθ G A c L h Y hY hs hYB B Q e K Le hP
    rcases hΩ G A c L h Y hY hs hYB B Q e K Le hP he hLe with ⟨⟨φ⟩⟩ | ⟨hL, ⟨φ⟩⟩ |
        ⟨p, f, e', hp, hf, he', hiso, hL3⟩
    · exact Or.inl (img148_equiv_of_theta hKM hθK (isSimpleGroup_of_mem_lA148 h he hLe)
        (three_dvd_card_of_types136 (h.chosen136.2 e he Le hLe).1) φ)
    · exact Or.inr (Or.inl ⟨hL, img148_equiv_of_theta hKM hθK isSimpleGroup_a7_148.1
        isSimpleGroup_a7_148.2 φ⟩)
    · have hs' := isSimpleGroup_of_isLThreeEpsAt148 hf hL3
      have h3 := three_dvd_card_of_isLThreeEpsAt148 hf hL3
      obtain ⟨ψ⟩ := img148_equiv_of_theta hKM hθK hs' h3 (MulEquiv.refl _)
      exact Or.inr (Or.inr ⟨p, f, e', hp, hf, he', hiso, isLThreeEpsAt_congr148 ψ.symm hL3⟩)
  · intro G _ _ A c L h Y hY hs hYB B Q e K Le hP c' L' hc' hc'B hL' hJ2 hd hON3
    let := ker148_normal hY.2
    have hKM : K ≤ Y ⊔ A :=
      ((le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1).trans inf_le_left).trans le_sup_left
    have hθK := hθ G A c L h Y hY hs hYB B Q e K Le hP
    rcases hON G A c L h Y hY hs hYB B Q e K Le hP c' L' hc' hc'B hL' hJ2 hd hON3 with
      ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩
    · exact Or.inl (img148_equiv_of_theta hKM hθK isSimpleGroup_a7_148.1
        isSimpleGroup_a7_148.2 φ)
    · exact Or.inr ⟨h7, img148_equiv_of_theta hKM hθK (isSimpleGroup_l37_148 h7).1
        (isSimpleGroup_l37_148 h7).2 φ⟩

theorem isSimpleGroup_img148_of_kType148
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} [(ker148 A Y).Normal] {e : G} {K Le : Subgroup G}
    (hkt : KType148 A Y e K Le) : IsSimpleGroup ↥(img148 A Y K) := by
  rcases hkt.2 with ⟨he, hLe, ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hL3⟩⟩ |
      ⟨-, ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩⟩
  · have := isSimpleGroup_of_mem_lA148 h he hLe
    exact MulEquiv.isSimpleGroup φ
  · have := isSimpleGroup_a7_148.1
    exact MulEquiv.isSimpleGroup φ
  · exact isSimpleGroup_of_isLThreeEpsAt148 hf hL3
  · have := isSimpleGroup_a7_148.1
    exact MulEquiv.isSimpleGroup φ
  · have := (isSimpleGroup_l37_148 h7).1
    exact MulEquiv.isSimpleGroup φ

theorem step148KTheta_of_step148KType
    (hKT : Step148KType) :
    Step148KTheta := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP
  let := ker148_normal hY.2
  have hK := hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := ((le_of_mem_thetaComponentsIn hK).trans inf_le_left).trans le_sup_left
  have hkt := hKT G A c L h Y hY hs hYB B Q e K Le hP
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  exact (theta_equiv_of_img148 hKM hKp (Sec6.isQuasisimple_of_mem_thetaComponentsIn hK)
    (isSimpleGroup_img148_of_kType148 h hkt) (MulEquiv.refl _)).1

theorem step148KThetaOmega_of_step148KType
    (hKT : Step148KType) :
    Step148KThetaOmega := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe
  let := ker148_normal hY.2
  have hK := hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := ((le_of_mem_thetaComponentsIn hK).trans inf_le_left).trans le_sup_left
  have hkt := hKT G A c L h Y hY hs hYB B Q e K Le hP
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  obtain ⟨-, ⟨ψ⟩⟩ := theta_equiv_of_img148 hKM hKp hKq (isSimpleGroup_img148_of_kType148 h hkt)
    (MulEquiv.refl _)
  rcases hkt.2 with ⟨-, -, ⟨⟨φ⟩⟩ | ⟨hL, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', hiso, hL3⟩⟩ |
      ⟨hON3, -⟩
  · exact Or.inl ⟨ψ.trans φ⟩
  · exact Or.inr (Or.inl ⟨hL, ⟨ψ.trans φ⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, e', hp, hf, he', hiso, isLThreeEpsAt_congr148 ψ.symm hL3⟩)
  · exact absurd hON3 (not_isTripleCover_of_mem_lA148 h he hLe)

theorem step148KThetaON_of_step148KType
    (hKT : Step148KType) :
    Step148KThetaON := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP _ _ _ _ _ _ _ hON3
  let := ker148_normal hY.2
  have hK := hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := ((le_of_mem_thetaComponentsIn hK).trans inf_le_left).trans le_sup_left
  have hkt := hKT G A c L h Y hY hs hYB B Q e K Le hP
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  obtain ⟨-, ⟨ψ⟩⟩ := theta_equiv_of_img148 hKM hKp hKq (isSimpleGroup_img148_of_kType148 h hkt)
    (MulEquiv.refl _)
  rcases hkt.2 with ⟨he, hLe, -⟩ | ⟨-, ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩⟩
  · exact absurd hON3 (not_isTripleCover_of_mem_lA148 h he hLe)
  · exact Or.inl ⟨ψ.trans φ⟩
  · exact Or.inr ⟨h7, ⟨ψ.trans φ⟩⟩

end CFSG.RankThree.PartTwo.Sec14
