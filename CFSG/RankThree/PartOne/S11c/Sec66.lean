module

public import CFSG.RankThree.PartOne.S11.Sec11Two
public import CFSG.RankThree.PartOne.S11c.Sec66Plane
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def EvenOuterElementIsFieldAut : Prop :=
  ∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 →
    ∀ (p : ℕ) (J : Subgroup H) (a c d : H), p.Prime → 5 ≤ p → CFSG.IsQuasisimple ↥J →
      EvenLieType (↥J ⧸ Subgroup.center ↥J) → ¬ p ∣ Nat.card (Subgroup.center ↥J) →
      a ∈ Subgroup.normalizer (J : Set H) → a ∉ J ⊔ Subgroup.centralizer (J : Set H) →
      a ^ p = 1 → c ∈ Subgroup.centralizer (J : Set H) → c ≠ 1 → c ^ p = 1 → d ∈ J → d ≠ 1 →
      d ^ p = 1 → a * c = c * a → a * d = d * a →
      (∃ S : Subgroup H, S ≤ J ∧ ¬ S ≤ (Subgroup.center ↥J).map J.subtype ∧ IsPGroup 2 S ∧
        a ∈ Subgroup.normalizer (S : Set H) ∧ c ∈ Subgroup.normalizer (S : Set H) ∧
        d ∈ Subgroup.normalizer (S : Set H) ∧
        ∃ s ∈ S, (a * s * a⁻¹)⁻¹ * s ∉ (Subgroup.center ↥J).map J.subtype ∨
          (d * s * d⁻¹)⁻¹ * s ∉ (Subgroup.center ↥J).map J.subtype) →
      InducesFieldAut p a J

@[expose] def EvenOuterPlaneNoInnerPart : Prop :=
  ∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 →
    ∀ (p : ℕ) (J A : Subgroup H) (c : H), p.Prime → 5 ≤ p → CFSG.IsQuasisimple ↥J →
      EvenLieType (↥J ⧸ Subgroup.center ↥J) → ¬ p ∣ Nat.card (Subgroup.center ↥J) →
      A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
      c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
      (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) →
      (∃ S : Subgroup H, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set H)) →
      False

@[expose] def EvenOuterElementIsFieldAutTag (t : StatedLieTag) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 →
    ∀ (p : ℕ) (J : Subgroup H) (a c d : H), p.Prime → 5 ≤ p → CFSG.IsQuasisimple ↥J →
      (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧ LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f) →
      ¬ p ∣ Nat.card (Subgroup.center ↥J) →
      a ∈ Subgroup.normalizer (J : Set H) → a ∉ J ⊔ Subgroup.centralizer (J : Set H) →
      a ^ p = 1 → c ∈ Subgroup.centralizer (J : Set H) → c ≠ 1 → c ^ p = 1 → d ∈ J → d ≠ 1 →
      d ^ p = 1 → a * c = c * a → a * d = d * a →
      (∃ S : Subgroup H, S ≤ J ∧ ¬ S ≤ (Subgroup.center ↥J).map J.subtype ∧ IsPGroup 2 S ∧
        a ∈ Subgroup.normalizer (S : Set H) ∧ c ∈ Subgroup.normalizer (S : Set H) ∧
        d ∈ Subgroup.normalizer (S : Set H) ∧
        ∃ s ∈ S, (a * s * a⁻¹)⁻¹ * s ∉ (Subgroup.center ↥J).map J.subtype ∨
          (d * s * d⁻¹)⁻¹ * s ∉ (Subgroup.center ↥J).map J.subtype) →
      InducesFieldAut p a J

theorem evenOuterElementIsFieldAut_of_tags (h : ∀ t, EvenOuterElementIsFieldAutTag t) :
    EvenOuterElementIsFieldAut := by
  intro H _ _ he p J a c d hp hp5 hq hEven hnZ
  obtain ⟨t, n, f, hadm, hmodel⟩ := hEven
  exact h t H he p J a c d hp hp5 hq ⟨n, f, hadm, hmodel⟩ hnZ

@[expose] def EvenOuterPlaneNoInnerPartTag (t : StatedLieTag) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 →
    ∀ (p : ℕ) (J A : Subgroup H) (c : H), p.Prime → 5 ≤ p → CFSG.IsQuasisimple ↥J →
      (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧ LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f) →
      ¬ p ∣ Nat.card (Subgroup.center ↥J) →
      A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
      c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
      (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) →
      (∃ S : Subgroup H, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set H)) →
      False

theorem evenOuterPlaneNoInnerPart_of_tags (h : ∀ t, EvenOuterPlaneNoInnerPartTag t) :
    EvenOuterPlaneNoInnerPart := by
  intro H _ _ he p J A c hp hp5 hq hEven hnZ
  obtain ⟨t, n, f, hadm, hmodel⟩ := hEven
  exact h t H he p J A c hp hp5 hq ⟨n, f, hadm, hmodel⟩ hnZ

section Glue

variable {G : Type} [Group G]

theorem thetaQuotientAction_inner_of_mem_sup {p : ℕ} {A L : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (L : Set G)) (a : A)
    (ha : (a : G) ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    ∃ q : L ⧸ aschbacherSolvableCore p L, thetaQuotientAction p hA a = MulAut.conj q := by
  obtain ⟨j, hj, z, hz, hjz⟩ := PlaneInner.exists_mul_of_mem_sup_centralizer ha
  refine ⟨((⟨j, hj⟩ : L) : L ⧸ aschbacherSolvableCore p L), ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    change thetaQuotientConj p L ⟨a, hA a.2⟩ _ = _
    rw [thetaQuotientConj_mk, MulAut.conj_apply]
    have hzl : (l : G) * z = z * l := (Subgroup.mem_centralizer_iff.mp hz) l l.2
    have : (L.normalizerMonoidHom ⟨a, hA a.2⟩ l : L) = ⟨j, hj⟩ * l * ⟨j, hj⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hjz]
      calc j * z * l * (j * z)⁻¹ = j * (z * l) * z⁻¹ * j⁻¹ := by group
        _ = j * (l * z) * z⁻¹ * j⁻¹ := by rw [hzl]
        _ = j * l * j⁻¹ := by group
    rw [this]
    rfl

end Glue

open scoped commutatorElement in
theorem exists_moved_mod_center {H : Type*} [Group H] {J S A : Subgroup H} {a c d : H}
    (hSJ : S ≤ J) (haS : a ∈ Subgroup.normalizer (S : Set H))
    (hcS : c ∈ Subgroup.normalizer (S : Set H)) (hdS : d ∈ Subgroup.normalizer (S : Set H))
    (hcC : c ∈ Subgroup.centralizer (J : Set H))
    (hAeq : A = Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (hSA : S = ⁅S, A⁆)
    (hnot : ¬ S ≤ (Subgroup.center J).map J.subtype) :
    ∃ s ∈ S, (a * s * a⁻¹)⁻¹ * s ∉ (Subgroup.center J).map J.subtype ∨
      (d * s * d⁻¹)⁻¹ * s ∉ (Subgroup.center J).map J.subtype := by
  by_contra hall
  push Not at hall
  let B : Subgroup H :=
    { carrier := {x | x ∈ Subgroup.normalizer (S : Set H) ∧
        ∀ s ∈ S, (x * s * x⁻¹)⁻¹ * s ∈ (Subgroup.center J).map J.subtype}
      one_mem' := ⟨Subgroup.one_mem _, fun s _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨Subgroup.mul_mem _ hxN hyN, fun s hs => ?_⟩
        have hs'' : y * s * y⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hyN s).mp hs
        have h1 := hx _ hs''
        have h2 := hy s hs
        have : ((x * y) * s * (x * y)⁻¹)⁻¹ * s =
            ((x * (y * s * y⁻¹) * x⁻¹)⁻¹ * (y * s * y⁻¹)) * ((y * s * y⁻¹)⁻¹ * s) := by group
        rw [this]
        exact Subgroup.mul_mem _ h1 h2
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        refine ⟨Subgroup.inv_mem _ hxN, fun s hs => ?_⟩
        have hs'' : x⁻¹ * s * x ∈ S := by
          have := (Subgroup.mem_normalizer_iff.mp
            (Subgroup.inv_mem _ hxN : x⁻¹ ∈ Subgroup.normalizer (S : Set H)) s).mp hs
          simpa using this
        have h1 := hx _ hs''
        have : (x⁻¹ * s * x⁻¹⁻¹)⁻¹ * s = ((x * (x⁻¹ * s * x) * x⁻¹)⁻¹ * (x⁻¹ * s * x))⁻¹ := by
          group
        rw [this]
        exact Subgroup.inv_mem _ h1 }
  have haB : a ∈ B := ⟨haS, fun s hs => (hall s hs).1⟩
  have hdB : d ∈ B := ⟨hdS, fun s hs => (hall s hs).2⟩
  have hcB : c ∈ B := by
    refine ⟨hcS, fun s hs => ?_⟩
    have hsc : s * c = c * s := (Subgroup.mem_centralizer_iff.mp hcC) s (hSJ hs)
    have : (c * s * c⁻¹)⁻¹ * s = 1 := by
      rw [show c * s * c⁻¹ = s by rw [← hsc]; group]
      group
    rw [this]
    exact Subgroup.one_mem _
  have hAB : A ≤ B := by
    rw [hAeq]
    exact sup_le (sup_le ((Subgroup.zpowers_le).mpr haB) ((Subgroup.zpowers_le).mpr hcB))
      ((Subgroup.zpowers_le).mpr hdB)
  apply hnot
  rw [hSA]
  refine Subgroup.commutator_le.mpr fun s hs x hx => ?_
  obtain ⟨hxN, hxs⟩ := hAB hx
  have hw : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxN s).mp hs
  obtain ⟨z, hz, hzeq⟩ := hxs s hs
  have hzc : (z : H) ∈ Subgroup.centralizer (J : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  have hscomm : ⁅s, x⁆ = (z : H) := by
    have h1 : (z : H) = (x * s * x⁻¹)⁻¹ * s := hzeq
    have h2 : (x * s * x⁻¹) * (z : H) = s := by rw [h1]; group
    have h3 : (x * s * x⁻¹) * (z : H) = (z : H) * (x * s * x⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hzc) _ (hSJ hw)
    calc ⁅s, x⁆ = s * (x * s * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      _ = ((x * s * x⁻¹) * (z : H)) * (x * s * x⁻¹)⁻¹ := by rw [h2]
      _ = ((z : H) * (x * s * x⁻¹)) * (x * s * x⁻¹)⁻¹ := by rw [h3]
      _ = (z : H) := by group
  rw [hscomm]
  exact ⟨z, hz, rfl⟩

theorem not_le_center_of_vanishing {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {L : Subgroup G}
    {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hLc : L ∈ thetaComponentsAt p c) {S : Subgroup G}
    (hSL : S ≤ L) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hSA : S = ⁅S, A⁆) :
    ¬ S ≤ (Subgroup.center L).map L.subtype := by
  intro hSZ
  have hp := sectionTenSetup_prime h
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hAcard : Nat.card A = p ^ 3 := h.2.2.2.2.2.2.2.1
  have hSθ : S ≤ inSubgroup (aschbacherSolvableCore p) L := by
    set N : Subgroup L := S.subgroupOf L with hN
    have hNc : N ≤ Subgroup.center L := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hSZ (Subgroup.mem_subgroupOf.mp hx)
      have : z = x := Subtype.ext hzx
      rw [← this]
      exact hz
    have hNn : N.Normal := ⟨fun n hn g => by
      have hg := Subgroup.mem_center_iff.mp (hNc hn) g
      rw [show g * n * g⁻¹ = n by rw [hg]; group]
      exact hn⟩
    have hN2 : IsPGroup 2 N := hS2.comap_subtype
    have := hN2.isNilpotent
    have hNsol : Group.IsSolvable N := inferInstance
    have hNp : ¬ p ∣ Nat.card N := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
      rw [hk]
      intro hdvd
      have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
      have h3 := sectionTenSetup_three_lt h
      omega
    have hle := (solvable_prime_complement_core_characterization (H := L) hp).2.2.2.1 N hNn
      hNsol hNp
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hSL hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSθ' : S ≤ inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({c} : Set G)) := by
    rw [theta_eq_inf_of_mem_thetaComponentsAt hp hLc] at hSθ
    exact fun x hx => (hSθ hx).2
  have hcomm := vanishing_centralizes_invariant_two_subgroups hp (sectionTenSetup_vanishing h)
    hAe hAcard hcA hc1 hSθ' hS2 hAS
  exact hS1 (by rw [hSA, hcomm])

theorem sec6Six_of_inputs (hS : SchreierFor InCatalog) (h1 : EvenOuterElementIsFieldAut)
    (h2 : EvenOuterPlaneNoInnerPart) : Sec6SixFieldAutomorphismPlane := by
  intro G _ _ p A h c hcA hc1 J hJ hEven hnZ
  have hJ02 : J ∈ sectionTenZeroStar p A := hJ.1.1
  have hJ2 : J ∈ sectionTenTwo p A := hJ.1.2
  have hJc : J ∈ thetaComponentsAt p c := hJ.2
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  obtain ⟨hq, hAN, hker⟩ := moving_maximal_data_at hS h hJ02 hcA hc1 hJc
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hAcard : Nat.card A = p ^ 3 := h.2.2.2.2.2.2.2.1
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := A) x hx
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq h).le
  have hcC : c ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp hJc).1 hx)
  have hCA : ∀ x ∈ A, x ∈ Subgroup.centralizer (J : Set G) → x ∈ Subgroup.zpowers c := by
    intro x hxA hxC
    rw [← hker, mem_thetaQuotientCentralizer_iff]
    refine ⟨hxA, hAN hxA, fun k hk => ?_⟩
    have hxk : x * k * x⁻¹ * k⁻¹ = 1 := by
      rw [← (Subgroup.mem_centralizer_iff.mp hxC) k hk]
      group
    rw [hxk]
    exact Subgroup.one_mem _
  obtain ⟨-, S, hSL, hS1, hS2, hAS, hSA⟩ := hJ02.1
  have hS1' : ¬ S ≤ (Subgroup.center J).map J.subtype :=
    not_le_center_of_vanishing h hcA hc1 hJc hSL hS1 hS2 hAS hSA
  have hout : ¬ A ≤ J ⊔ Subgroup.centralizer (J : Set G) := fun hle => by
    refine hJ2.2 ⟨hJ2.1, hAN, ?_⟩
    rintro _ ⟨a, rfl⟩
    obtain ⟨q, hq'⟩ := thetaQuotientAction_inner_of_mem_sup hAN a (hle a.2)
    exact ⟨q, hq'.symm⟩
  by_cases hx : ∃ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set G) ∧ x ∉ Subgroup.zpowers c
  · obtain ⟨x, hxA, hxJ, hxc⟩ := hx
    obtain ⟨d, hdA, hdJ, hd1, hdp⟩ := PlaneInner.exists_inner_part he hp hp2 hnZ hAN hAcomm hApow
      hAcard hCA hSL hS1 hS2 hAS hxA hxJ hxc
    obtain ⟨a, haA, haJ⟩ := IsConcreteLE.not_le_iff_exists.mp hout
    obtain ⟨hAeq, hdeq⟩ := PlaneInner.decomposition hp hnZ hApow hAcard hcA hc1 hcC hdA hdJ hd1 haA
      haJ
    refine ⟨a, d, haA, hdA, hd1, hAeq, hdeq, ?_⟩
    exact h1 G he p J a c d hp hp5 hq hEven hnZ (hAN haA) haJ (hApow a haA) hcC hc1
      (hApow c hcA) hdJ hd1 hdp (hAcomm a haA c hcA) (hAcomm a haA d hdA)
      ⟨S, hSL, hS1', hS2, hAS haA, hAS hcA, hAS hdA,
        exists_moved_mod_center hSL (hAS haA) (hAS hcA) (hAS hdA) hcC hAeq hSA hS1'⟩
  · exfalso
    refine h2 G he p J A c hp hp5 hq hEven hnZ hAN hAe hAcard hcA hc1 hcC
      (fun x hxA hxJ => ?_) ⟨S, hSL, hS1, hS2, hAS⟩
    by_contra hxc
    exact hx ⟨x, hxA, hxJ, hxc⟩

end CFSG.RankThree.PartOne
