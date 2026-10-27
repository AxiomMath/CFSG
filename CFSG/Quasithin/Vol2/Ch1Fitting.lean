module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Foundations.Basic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

variable {Q : Type} [Group Q] [Finite Q]

theorem map_fittingSubgroup_le_fittingSubgroup (N : Subgroup Q) [N.Normal] :
    (CFSG.fittingSubgroup ↥N).map N.subtype ≤ CFSG.fittingSubgroup Q := by
  refine le_sSup ⟨?_, ?_⟩
  · have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.fittingSubgroup ↥N)
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance] at h1
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  · exact (Group.isNilpotent_congr ((CFSG.fittingSubgroup ↥N).equivMapOfInjective N.subtype
      N.subtype_injective)).mp inferInstance

theorem centralizer_fittingSubgroup_le_of_not_isQuasisimple (hperf : Group.IsPerfect Q)
    (hmax : ∀ P : Subgroup Q, P.Normal → P = ⊤ ∨ Group.IsSolvable P)
    (hns : ¬ Group.IsSolvable Q) (hq : ¬ CFSG.IsQuasisimple Q) :
    Subgroup.centralizer (CFSG.fittingSubgroup Q : Set Q) ≤ CFSG.fittingSubgroup Q := by
  classical
  set F := CFSG.fittingSubgroup Q with hF
  set C := Subgroup.centralizer (F : Set Q) with hC
  have hCn : C.Normal := inferInstance
  by_cases hCtop : C = ⊤
  · exfalso
    apply hq
    have hFZ : F ≤ Subgroup.center Q := by
      intro f hf
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := by rw [hCtop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg f hf).symm
    have hA : ∀ P : Subgroup Q, P.Normal → Group.IsSolvable P → P ≤ Subgroup.center Q := by
      intro P hPn hPs x hx
      have hFP : (CFSG.fittingSubgroup ↥P).map P.subtype ≤ F :=
        map_fittingSubgroup_le_fittingSubgroup P
      have hxF : (⟨x, hx⟩ : ↥P) ∈ CFSG.fittingSubgroup ↥P := by
        apply CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hPs
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        apply Subtype.ext
        have hfZ : (f : Q) ∈ Subgroup.center Q := hFZ (hFP ⟨f, hf, rfl⟩)
        exact (Subgroup.mem_center_iff.mp hfZ x).symm
      exact hFZ (hFP ⟨_, hxF, rfl⟩)
    have hZne : Subgroup.center Q ≠ ⊤ := by
      intro h
      apply hns
      refine Group.isSolvable_of_comm fun a b => ?_
      have : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
    refine ⟨hperf, ?_, ?_⟩
    · have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := by
        obtain ⟨x, hx⟩ : ∃ x : Q, x ∉ Subgroup.center Q := by
          by_contra h
          push Not at h
          exact hZne (top_unique fun x _ => h x)
        exact ⟨⟨QuotientGroup.mk x, 1, fun h => hx ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
      refine ⟨fun T hT => ?_⟩
      let P : Subgroup Q := T.comap (QuotientGroup.mk' (Subgroup.center Q))
      have hPn : P.Normal := hT.comap _
      rcases hmax P hPn with hP | hP
      · right
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        have : x ∈ P := hP ▸ Subgroup.mem_top x
        exact this
      · left
        have hPZ : P ≤ Subgroup.center Q := hA P hPn hP
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        have hxP : x ∈ P := hy
        exact (QuotientGroup.eq_one_iff x).mpr (hPZ hxP)
    · by_contra hcomm
      push Not at hcomm
      apply hns
      have h1 : Group.IsSolvable (Q ⧸ Subgroup.center Q) := Group.isSolvable_of_comm hcomm
      have h2 : Group.IsSolvable (Subgroup.center Q) := inferInstance
      exact Group.isSolvable_of_subgroup_quotient (Subgroup.center Q)
  ·
    have hCs : Group.IsSolvable C := (hmax C hCn).resolve_left hCtop
    have hFC : (CFSG.fittingSubgroup ↥C).map C.subtype ≤ F :=
      map_fittingSubgroup_le_fittingSubgroup C
    have hle : ∀ c : ↥C, c ∈ CFSG.fittingSubgroup ↥C := by
      intro c
      apply CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCs
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      apply Subtype.ext
      have hfF : (f : Q) ∈ F := hFC ⟨f, hf, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp c.2 (f : Q) hfF
    intro y hy
    exact hFC ⟨⟨y, hy⟩, hle ⟨y, hy⟩, rfl⟩

theorem mem_centralizer_fittingSubgroup_of_centralizes_pCores {y : Q}
    (hy : ∀ p : ℕ, p.Prime → ∀ x ∈ CFSG.pCore p Q, x * y = y * x) :
    y ∈ Subgroup.centralizer (CFSG.fittingSubgroup Q : Set Q) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hle : CFSG.fittingSubgroup Q ≤ Subgroup.centralizer ({y} : Set Q) := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hy p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) x hx).symm
  have := Subgroup.mem_centralizer_iff.mp (hle hf) y rfl
  exact this.symm

theorem mem_pCore_two_of_centralizes_pCores (hperf : Group.IsPerfect Q)
    (hmax : ∀ P : Subgroup Q, P.Normal → P = ⊤ ∨ Group.IsSolvable P)
    (hns : ¬ Group.IsSolvable Q) (hq : ¬ CFSG.IsQuasisimple Q) {y : Q} (hy2 : y ^ 2 = 1)
    (hy : ∀ p : ℕ, p.Prime → ∀ x ∈ CFSG.pCore p Q, x * y = y * x) : y ∈ CFSG.pCore 2 Q := by
  classical
  set F := CFSG.fittingSubgroup Q with hF
  set C := Subgroup.centralizer (F : Set Q) with hC
  have hCn : C.Normal := inferInstance
  have hCF : C ≤ F := centralizer_fittingSubgroup_le_of_not_isQuasisimple hperf hmax hns hq
  have hyC : y ∈ C := mem_centralizer_fittingSubgroup_of_centralizes_pCores hy
  have hcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb a (hCF ha)
  let N : Subgroup Q :=
    { carrier := {x | x ∈ C ∧ x ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => ⟨C.mul_mem ha.1 hb.1, by
        have hab : Commute a b := hcomm a ha.1 b hb.1
        rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨C.one_mem, one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hNn : N.Normal :=
    ⟨fun n hn g => ⟨hCn.conj_mem n hn.1 g, by rw [conj_pow, hn.2, mul_one, mul_inv_cancel]⟩⟩
  have hN2 : IsPGroup 2 N := fun x => ⟨1, Subtype.ext (by simpa using x.2.2)⟩
  exact (le_sSup ⟨hNn, hN2⟩ : N ≤ CFSG.pCore 2 Q) ⟨hyC, hy2⟩

end CFSG.Quasithin
