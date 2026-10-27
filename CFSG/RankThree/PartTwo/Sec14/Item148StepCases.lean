module

public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Delta

variable {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem deltaZero_mono148 {S T : Subgroup G} (h : S ≤ T) : deltaZero A LB S ≤ deltaZero A LB T :=
  sSup_le fun _ hQ => le_deltaZero hQ.1 (hQ.2.trans h)

theorem deltaZero_eq_sup_of_img148_le {Y K S : Subgroup G} [(ker148 A Y).Normal]
    (hXK : img148 A Y (deltaZero A LB Y) ≤ img148 A Y K) (hKS : K ≤ deltaZero A LB S)
    (hSY : S ≤ Y) :
    deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔ deltaZero A LB S := by
  set X := deltaZero A LB Y with hXdef
  have hSX : deltaZero A LB S ≤ X := deltaZero_mono148 hSY
  refine le_antisymm (fun x hx => ?_) (sup_le (pPrimeCoreOf_le 3 X) hSX)
  have hxY : x ∈ Y := deltaZero_le Y hx
  have hxM : x ∈ Y ⊔ A := Subgroup.mem_sup_left hxY
  obtain ⟨k, hkM, hkK, hk⟩ := mem_img148_iff.mp (hXK (mem_img148_iff.mpr ⟨x, hxM, hx, rfl⟩))
  have hkx : k⁻¹ * x ∈ pPrimeCoreOf 3 Y := mk'_ker148_eq_iff.mp hk
  have hkX : k ∈ X := hSX (hKS hkK)
  have hcore : pPrimeCoreOf 3 Y ⊓ X ≤ pPrimeCoreOf 3 X := by
    refine le_pPrimeCoreOf inf_le_right (fun y hy => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pPrimeCoreOf 3 Y (deltaZero_le Y hy), Subgroup.le_normalizer hy⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 Y)
  have h1 : k⁻¹ * x ∈ pPrimeCoreOf 3 X :=
    hcore (Subgroup.mem_inf.mpr ⟨hkx, X.mul_mem (X.inv_mem hkX) hx⟩)
  have hxk : x = k * (k⁻¹ * x) := by group
  rw [hxk, sup_comm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hKS hkK)) (Subgroup.mem_sup_right h1)

end Delta

section Cases

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem case148Two_of_img148_eq {e : G} {K Le : Subgroup G}
    (hXK : img148 A Y (deltaZero A (lB A) Y) = img148 A Y K)
    (hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G)) (hKΔ : K = deltaZero A (lB A) K)
    (he : Subgroup.zpowers e ∈ omegaA A) (hLe : Le ∈ lA A e)
    (htype : Nonempty (↥(img148 A Y K) ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
      ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
          (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
          (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
            CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
        Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7))) ∨
      (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
        Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
        IsLThreeEpsAt ↥(img148 A Y K) p f)) :
    Case148Two A (lB A) Y := by
  have hKH : K ≤ deltaZero A (lB A)
      (Y ⊓ Subgroup.normalizer (Subgroup.zpowers e : Set G)) := by
    rw [hKΔ]
    refine deltaZero_mono148 (hKY.trans (inf_le_inf_left _ ?_))
    refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hx
  refine ⟨e, he, deltaZero_eq_sup_of_img148_le hXK.le hKH inf_le_left, Le, hLe, ?_⟩
  rw [hXK]
  rcases htype with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))

theorem case148Two_or_of_img148_eq {e : G} {K Le : Subgroup G}
    (hXK : img148 A Y (deltaZero A (lB A) Y) = img148 A Y K)
    (hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G)) (hKΔ : K = deltaZero A (lB A) K)
    (hkt : KType148 A Y e K Le) :
    Case148Two A (lB A) Y ∨
      (Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON ∧
        (Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))))) := by
  rcases hkt.2 with ⟨he, hLe, htype⟩ | ⟨hON, htype⟩
  · exact Or.inl (case148Two_of_img148_eq hXK hKY hKΔ he hLe htype)
  · right
    rw [hXK]
    exact ⟨hON, htype⟩


theorem case148Three_of_img148_eq {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G}
    (hXK : img148 A Y (deltaZero A (lB A) Y) = img148 A Y K)
    (hP : IsPoint148 A (lB A) Y B Q e K Le)
    (hON : Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le)
      CFSG.Blueprint.NativeSporadic.ON)
    (htype : Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))) :
    Case148Three A (lB A) Y := by
  obtain ⟨hB, -, -, heB, he1, hK, hKΔ, -, hLe, halt⟩ := hP
  have hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  rcases halt with ⟨heΩ, hLeA⟩ | ⟨c', L', hc'Ω, -, hL'A, hJ2, hd, -⟩
  · exfalso
    have hZ := Sec15.center_eq_bot_of_types hLe (h.chosen136.2 e heΩ Le hLeA).1
    have h3 := hON.1
    rw [hZ] at h3
    simp at h3
  · refine ⟨c', e, L', hc'Ω, hL'A, hJ2, hB.1 heB, he1, hd, ?_, ?_⟩
    · have hKS : K ≤ deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({e} : Set G)) := by
        rw [hKΔ]
        exact deltaZero_mono148 hKY
      exact deltaZero_eq_sup_of_img148_le hXK.le hKS inf_le_left
    · rcases htype with h7 | h7
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7))))

end Cases

section Five

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_zpowers_le {e : G} (he : e ∈ A) :
    img148 A Y (Subgroup.zpowers e) ≤ Subgroup.zpowers (alpha148 A Y e he) := by
  intro x hx
  obtain ⟨g, hgM, hg, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [alpha148_eq_mk', ← map_zpow]
  rfl

omit [Finite G] in
theorem img148_sup_eq_zpowers {X J : Subgroup G} (hXM : X ≤ Y ⊔ A) {e : G} (he : e ∈ A)
    (hA : A = Subgroup.zpowers e ⊔ (A ⊓ J)) (hXJ : img148 A Y X = img148 A Y J) :
    img148 A Y (X ⊔ A) = img148 A Y X ⊔ Subgroup.zpowers (alpha148 A Y e he) := by
  rw [img148_sup hXM le_sup_right]
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · have hle : img148 A Y A ≤
        img148 A Y (Subgroup.zpowers e) ⊔ img148 A Y (A ⊓ J) := by
      rw [← img148_sup ((Subgroup.zpowers_le.mpr he).trans le_sup_right)
        (inf_le_left.trans le_sup_right)]
      exact img148_mono hA.le
    refine hle.trans (sup_le ((img148_zpowers_le he).trans le_sup_right) ?_)
    rw [hXJ]
    exact (img148_mono inf_le_right).trans le_sup_left
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right (alpha148_mem_img148 he)

omit [Finite G] in
theorem not_inducesOuterTheta_of_mem148 {Γ : Type*} [Group Γ] [Finite Γ] {X : Subgroup Γ}
    {x : Γ} (hx : x ∈ X) : ¬ Sec4.InducesOuterTheta x X := by
  rintro ⟨hxN, hout⟩
  apply hout
  refine ⟨((⟨x, hx⟩ : X) : ↥X ⧸ aschbacherSolvableCore 3 ↥X), ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl


theorem not_mem_of_inducesStdKind148 {Γ : Type*} [Group Γ] [Finite Γ] {X : Subgroup Γ} {x : Γ}
    {k : KFacts.AutKind} (h : KFacts.InducesStdKind X x k) (hk : k ≠ .inner) : x ∉ X :=
  fun hx => not_inducesOuterTheta_of_mem148 hx (KFacts.InducesStdKind.inducesOuterTheta X h hk)

end Five

omit [Finite G] in
theorem isLThreeEpsAt_of_isoLThreePi148 {X : Type} [Group X] [Nontrivial X] [Group.IsPerfect X]
    {p e : ℕ} [hp : Fact p.Prime] (h : Sec4.IsoLThreePi X p e) : IsLThreeEpsAt X p e := by
  rcases h with ⟨-, hφ⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Or.inl hφ
  · refine Or.inr ⟨?_, ⟨φ⟩⟩
    by_contra h2
    have hpe : p ^ e = 2 := by
      have : 2 ≤ p ^ e := by
        rcases Nat.eq_zero_or_pos e with he | he
        · subst he
          simp at hq
        · exact le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
      omega
    obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out hpe
    have := isSolvable_projSU_two
    have hsol : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    exact Group.IsPerfect.not_isSolvable X hsol

end CFSG.RankThree.PartTwo.Sec14
