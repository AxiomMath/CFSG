module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofUnitary
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryComp
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace HeringUnitary

theorem unitary_setup {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsComponent L)
    {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G)))) {m : ℕ}
    (hm : Odd m) (e : K ≃* projSU 3 2 m) :
    3 ≤ m ∧ Subgroup.center (projSU 3 2 m) = ⊥ ∧
    ∃ ι : projSU 3 2 m →* L ⧸ aschbacherSolvableCore 3 L, Function.Injective ι ∧
      (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) ^ 3 = 1 ∧
      thetaQuotMulAut L (compAction L ⟨a, haN⟩) ≠ 1 ∧
      (∀ u, thetaQuotMulAut L (compAction L ⟨a, haN⟩) (ι u) = ι u) ∧
      IsComponent (ι.range.subgroupOf
        (Item426.fixSub (thetaQuotMulAut L (compAction L ⟨a, haN⟩)))) := by
  obtain ⟨hm3, -⟩ := Item419Res3.unitary_component_facts hKle hKc hm e
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hq : IsQuasisimple K := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hKle) hKc.1
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : Group.IsPerfect K := hq.1
  have hnsol : ¬ Group.IsSolvable K := fun h => Group.IsPerfect.not_isSolvable K h
  have hs : IsSimpleGroup (projSU 3 2 m) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 m (by omega) (by
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      omega)
  have hsK : IsSimpleGroup K := e.isSimpleGroup
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  set f : K →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL) with hf
  have hker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      apply hnsol
      have hle : ∀ k : K, Subgroup.inclusion hKL k ∈ aschbacherSolvableCore 3 L := by
        intro k
        have hk : k ∈ f.ker := h ▸ Subgroup.mem_top k
        rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk
        exact hk
      let g : K →* aschbacherSolvableCore 3 L :=
        (Subgroup.inclusion hKL).codRestrict _ hle
      exact Group.isSolvable_of_isSolvable_injective (f := g) fun x y hxy =>
        Subgroup.inclusion_injective hKL (congrArg Subtype.val hxy)
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hLq : IsQuasisimple L := hL.1
  have hUperf : Group.IsPerfect (projSU 3 2 m) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hUZ : Subgroup.center (projSU 3 2 m) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projSU 3 2 m)) with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : projSU 3 2 m, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
      have htop : commutator (projSU 3 2 m) = ⊤ := Group.IsPerfect.commutator_eq_top
      have hbot : commutator (projSU 3 2 m) = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hcomm y x
      obtain ⟨a, b, hab⟩ := exists_pair_ne (projSU 3 2 m)
      apply hab
      have ha : a ∈ (⊥ : Subgroup (projSU 3 2 m)) := by
        rw [← hbot, htop]; exact Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup (projSU 3 2 m)) := by
        rw [← hbot, htop]; exact Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
  have ha3' : a ^ 3 = 1 := by
    rw [← ha3]
    exact pow_orderOf_eq_one a
  have hcomp : IsComponent ((f.comp e.symm.toMonoidHom).range.subgroupOf
      (Item426.fixSub (thetaQuotMulAut L (compAction L ⟨a, haN⟩)))) := by
    set M := L ⊓ Subgroup.centralizer ({a} : Set G) with hM
    set K' := K.subgroupOf M with hK'
    have hf' : Function.Injective ((Sec11.cMap L a).comp K'.subtype) := by
      intro x y hxy
      have hxy' : f (Subgroup.subgroupOfEquivOfLe hKle x) =
          f (Subgroup.subgroupOfEquivOfLe hKle y) := hxy
      exact (Subgroup.subgroupOfEquivOfLe hKle).injective (hinj hxy')
    have h1 := isComponent_map_subgroupOf_range (Sec11.cMap L a) hKc hf'
    have h2 := isComponent_subgroupOf_congr (Sec11.range_cMap haN ha3') h1
    have hι : (f.comp e.symm.toMonoidHom).range = K'.map (Sec11.cMap L a) := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨⟨((e.symm u : K) : G), hKle (e.symm u).2⟩,
          Subgroup.mem_subgroupOf.mpr (e.symm u).2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨e ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
        change f (e.symm (e ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩)) = _
        rw [MulEquiv.symm_apply_apply]
        rfl
    rw [hι]
    exact h2
  refine ⟨hm3, hUZ, f.comp e.symm.toMonoidHom, hinj.comp e.symm.injective, ?_, ?_, ?_, hcomp⟩
  · rw [← map_pow, ← map_pow]
    have h : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← ha3]
      exact pow_orderOf_eq_one a
    rw [h, map_one, map_one]
  · intro h1
    apply haC
    have hσ := eq_one_of_thetaQuotMulAut_eq_one hLq h1
    have hmem : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ∈ (compAction L).ker :=
      MonoidHom.mem_ker.mpr hσ
    rw [compAction_ker, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  · intro u
    have hk : ((e.symm u : K) : G) ∈ Subgroup.centralizer ({a} : Set G) := (hKle (e.symm u).2).2
    have ha1 : a * ((e.symm u : K) : G) * a⁻¹ = ((e.symm u : K) : G) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hk
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    change thetaQuotMulAut L (compAction L ⟨a, haN⟩)
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)) (Subgroup.inclusion hKL (e.symm u))) = _
    rw [QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    exact ha1

end HeringUnitary

end CFSG.RankThree.PartTwo.Sec4
