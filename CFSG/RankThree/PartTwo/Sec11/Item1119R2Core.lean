module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymAY
import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119R2

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem mem_commutator_iff_of_equiv {M X : Type*} [Group M] [Group X]
    (e : M ≃* Multiplicative (ZMod 3) × X) (m : M) :
    m ∈ _root_.commutator M ↔ (e m).1 = 1 ∧ (e m).2 ∈ _root_.commutator X := by
  have hPc : _root_.commutator (Multiplicative (ZMod 3) × X) =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (_root_.commutator X) := by
    have : IsMulCommutative (Multiplicative (ZMod 3)) := ⟨⟨mul_comm⟩⟩
    rw [_root_.commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod,
      ← _root_.commutator_def, ← _root_.commutator_def, commutator_eq_bot]
  have hmemP : ∀ p : Multiplicative (ZMod 3) × X,
      p ∈ _root_.commutator (Multiplicative (ZMod 3) × X) ↔
        p.1 = 1 ∧ p.2 ∈ _root_.commutator X := by
    intro p
    rw [hPc, Subgroup.mem_prod, Subgroup.mem_bot]
  have hec : (_root_.commutator M).map e.toMonoidHom =
      _root_.commutator (Multiplicative (ZMod 3) × X) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective,
      _root_.commutator_def]
  rw [← hmemP, ← hec, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem card_comap_commutator_aux {A M X : Type*} [Group A] [Finite A] [Group M] [Group X]
    (hXc : Subgroup.center X = ⊥) (e : M ≃* Multiplicative (ZMod 3) × X)
    (ψ : A →* M) (a₀ : A) (hψa : ψ a₀ ≠ 1) (hψc : ∀ q : M, ψ a₀ * q = q * ψ a₀)
    (hF : ∀ u : A, (e (ψ u)).2 ∈ _root_.commutator X) :
    Nat.card ↥((_root_.commutator M).comap ψ) * 3 = Nat.card A ∧
      a₀ ∉ (_root_.commutator M).comap ψ := by
  have hmemM := mem_commutator_iff_of_equiv e
  obtain ⟨φ, hφ⟩ : ∃ φ : A →* Multiplicative (ZMod 3), ∀ u, φ u = (e (ψ u)).1 :=
    ⟨(MonoidHom.fst _ _).comp (e.toMonoidHom.comp ψ), fun u => rfl⟩
  have hK : (_root_.commutator M).comap ψ = φ.ker := by
    ext u
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, hmemM, hφ]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, hF u⟩
  have hne : e (ψ a₀) ≠ 1 := by
    intro h
    apply hψa
    apply e.injective
    rw [h, map_one]
  have hcenter : (e (ψ a₀)).2 ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg e (hψc (e.symm (1, x)))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
    exact (congrArg Prod.snd h).symm
  have hyc : (e (ψ a₀)).2 = 1 := by
    have h := hcenter
    rw [hXc, Subgroup.mem_bot] at h
    exact h
  have hφa : φ a₀ ≠ 1 := by
    rw [hφ]
    intro h1
    apply hne
    exact Prod.ext h1 hyc
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 :=
    (Nat.card_congr Multiplicative.ofAdd).symm.trans (Nat.card_zmod 3)
  haveI : Fact (Nat.card (Multiplicative (ZMod 3))).Prime :=
    ⟨by rw [hcard]; exact Nat.prime_three⟩
  have hrange : φ.range = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card φ.range with h | h
    · exfalso
      apply hφa
      have hmem : φ a₀ ∈ φ.range := MonoidHom.mem_range.mpr ⟨a₀, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exact h
  have hcardK : Nat.card (↥φ.ker) * 3 = Nat.card A := by
    have h := Subgroup.card_mul_index (H := φ.ker)
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hcard] at h
    exact h
  rw [hK]
  refine ⟨hcardK, ?_⟩
  rw [MonoidHom.mem_ker]
  exact hφa

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def toSec (a : G) (Y A B : Subgroup G)
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G)) (hB : B ≤ Y ⊔ A) : B →* sec11YA a Y A :=
  MonoidHom.codRestrict
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G)))).comp
      (Subgroup.inclusion hBC))
    (sec11YA a Y A) (fun u => ⟨Subgroup.inclusion hBC u,
      Subgroup.mem_subgroupOf.mpr (hB u.2), rfl⟩)

theorem toSec_coe (a : G) (Y A B : Subgroup G) (hBC : B ≤ Subgroup.centralizer ({a} : Set G))
    (hB : B ≤ Y ⊔ A) (u : B) :
    ((toSec a Y A B hBC hB u : sec11YA a Y A) :
      Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))) =
      QuotientGroup.mk (Subgroup.inclusion hBC u) := rfl

noncomputable abbrev toYA (a : G) (Y A : Subgroup G)
    (hAC : A ≤ Subgroup.centralizer ({a} : Set G)) : A →* sec11YA a Y A :=
  toSec a Y A A hAC le_sup_right

theorem commutator_sec11YA_eq {a : G} {Y A : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) :
    ⁅sec11YA a Y A, sec11YA a Y A⁆ =
      (Y.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G)))) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set π : C →* C ⧸ aschbacherSolvableCore 3 C := QuotientGroup.mk' _ with hπ
  have hYC : Y ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  set Y' := Y.subgroupOf C with hY'
  set A' := A.subgroupOf C with hA'
  have hM : sec11YA a Y A = (Y' ⊔ A').map π := by
    rw [sec11YA, Subgroup.subgroupOf_sup hYC hAC]
  have hA'Y' : A' ≤ Subgroup.normalizer (Y' : Set C) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact Subgroup.mem_normalizer_iff.mp (hAY (Subgroup.mem_subgroupOf.mp hu)) (z : G)
  have hA'c : ∀ u ∈ A', ∀ v ∈ A', u * v = v * u := fun u hu v hv =>
    Subtype.ext (hA _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
  have hYp : Group.IsPerfect Y := Sec6.isPerfect_of_mem_thetaComponentsAt hY
  have hY'p : Group.IsPerfect Y' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYC).symm.surjective
  have hYM : Y'.map π ≤ sec11YA a Y A := by
    rw [hM]
    exact Subgroup.map_mono le_sup_left
  apply le_antisymm
  · rw [hM, ← Subgroup.map_commutator]
    exact Subgroup.map_mono (Item1116Proof.commutator_sup_le_of_comm hA'Y' hA'c)
  · have : Group.IsPerfect (Y'.map π) := Group.IsPerfect.map π
    calc Y'.map π = ⁅Y'.map π, Y'.map π⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅sec11YA a Y A, sec11YA a Y A⁆ := Subgroup.commutator_mono hYM hYM

theorem mem_sup_theta_iff {a : G} {Y A B : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G)) (hB : B ≤ Y ⊔ A) (u : B) :
    (u : G) ∈ Y ⊔ sym1119Theta a ↔
      toSec a Y A B hBC hB u ∈ _root_.commutator (sec11YA a Y A) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set π : C →* C ⧸ aschbacherSolvableCore 3 C := QuotientGroup.mk' _ with hπ
  have hYC : Y ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  have h1 : Y ⊔ sym1119Theta a =
      ((Y.subgroupOf C) ⊔ aschbacherSolvableCore 3 C).map C.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYC]
    rfl
  have h2 : (Y.subgroupOf C ⊔ aschbacherSolvableCore 3 C) =
      Subgroup.comap π ((Y.subgroupOf C).map π) := by
    rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
  have key : (u : G) ∈ Y ⊔ sym1119Theta a ↔
      Subgroup.inclusion hBC u ∈ Y.subgroupOf C ⊔ aschbacherSolvableCore 3 C := by
    rw [h1, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwu⟩
      have : w = Subgroup.inclusion hBC u := Subtype.ext hwu
      rwa [this] at hw
    · intro h
      exact ⟨_, h, rfl⟩
  rw [key, h2, Subgroup.mem_comap]
  have hcomm := commutator_sec11YA_eq hY hAC hAY hA
  have h3 : ∀ z : sec11YA a Y A, z ∈ _root_.commutator (sec11YA a Y A) ↔
      (z : C ⧸ aschbacherSolvableCore 3 C) ∈ ⁅sec11YA a Y A, sec11YA a Y A⁆ := by
    intro z
    rw [← Subgroup.map_subtype_commutator]
    exact (Subgroup.mem_map_iff_mem (sec11YA a Y A).subtype_injective).symm
  rw [h3, hcomm, toSec_coe]
  exact Iff.rfl

theorem not_three_dvd_card_thetaG (a : G) : ¬ 3 ∣ Nat.card (sym1119Theta a) := by
  unfold sym1119Theta
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact KFacts.not_three_dvd_card_aschbacherSolvableCore _

theorem split_of_equiv {a : G} {Y A : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hA3 : ∀ u ∈ A, u ^ 3 = 1) (hAcard : Nat.card A = 27) (haA : a ∈ A) (ha1 : a ≠ 1)
    {X : Type} [Group X] (hXc : Subgroup.center X = ⊥)
    (e : sec11YA a Y A ≃* Multiplicative (ZMod 3) × X)
    (hF : ∀ u : A, (e (toYA a Y A hAC u)).2 ∈ _root_.commutator X) :
    Nat.card ↥(A ⊓ (Y ⊔ sym1119Theta a)) = 9 ∧ a ∉ A ⊓ (Y ⊔ sym1119Theta a) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set ψ := toYA a Y A hAC with hψ
  set a₀ : A := ⟨a, haA⟩ with ha₀
  have haθ : a ∉ sym1119Theta a := by
    intro h
    have h3 : orderOf a = 3 := orderOf_eq_prime (hA3 a haA) ha1
    have hdvd : orderOf a ∣ Nat.card (sym1119Theta a) :=
      Subgroup.orderOf_dvd_natCard (sym1119Theta a) h
    rw [h3] at hdvd
    exact not_three_dvd_card_thetaG a hdvd
  have hψa : ψ a₀ ≠ 1 := by
    intro h1
    apply haθ
    have h2 : ((ψ a₀ : sec11YA a Y A) : C ⧸ aschbacherSolvableCore 3 C) = 1 := by
      rw [h1]; rfl
    rw [hψ, toYA, toSec_coe] at h2
    have h3 := (QuotientGroup.eq_one_iff _).mp h2
    exact ⟨_, h3, rfl⟩
  have hψc : ∀ q : sec11YA a Y A, ψ a₀ * q = q * ψ a₀ := by
    intro q
    obtain ⟨c', hc'⟩ := QuotientGroup.mk_surjective q.1
    apply Subtype.ext
    show ((ψ a₀ : sec11YA a Y A) : C ⧸ aschbacherSolvableCore 3 C) * q.1 =
      q.1 * ((ψ a₀ : sec11YA a Y A) : C ⧸ aschbacherSolvableCore 3 C)
    rw [← hc', hψ, toYA, toSec_coe, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have h4 := c'.2
    rw [Subgroup.mem_centralizer_singleton_iff] at h4
    exact h4.symm
  obtain ⟨hcard, hnot⟩ := card_comap_commutator_aux hXc e ψ a₀ hψa hψc hF
  have hcomap : (_root_.commutator (sec11YA a Y A)).comap ψ =
      (A ⊓ (Y ⊔ sym1119Theta a)).subgroupOf A := by
    ext u
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      ← mem_sup_theta_iff hY hAC hAY hA hAC le_sup_right u]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  rw [hcomap] at hcard hnot
  have hcard' : Nat.card ↥((A ⊓ (Y ⊔ sym1119Theta a)).subgroupOf A) =
      Nat.card ↥(A ⊓ (Y ⊔ sym1119Theta a)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  refine ⟨by omega, fun h => hnot ?_⟩
  exact Subgroup.mem_subgroupOf.mpr h

end CFSG.RankThree.PartTwo.Sec11.Item1119R2
