module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKMatrix
public import CFSG.LocalAnalysis.StandardType.GGE6DepKReflEquiv
public import CFSG.LocalAnalysis.StandardType.GGE6DepKGramBlock
public import CFSG.LocalAnalysis.StandardType.GGE6DepKGramOne
public import CFSG.LocalAnalysis.StandardType.GGE6DepKMa
public import CFSG.LocalAnalysis.StandardType.GGE6DepKGenTransport
public import CFSG.LocalAnalysis.StandardType.GGE6DepKNoTv
public import CFSG.LocalAnalysis.StandardType.GGE6DepKRefl
public import CFSG.LocalAnalysis.StandardType.GGE6DepExtractK
public import CFSG.LocalAnalysis.StandardType.GGE6DepKClassForm

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly
open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private lemma card_gS (i : Fin 5) :
    Fintype.card {v : Vec6 // (gS i).mulVec v = v} * 3 = 3 ^ 6 := by
  fin_cases i <;> decide +kernel

private lemma hJ_norm (i : Fin 5) : norm6 (hJ i) = 1 := by
  fin_cases i <;> decide +kernel

private lemma gS_eq_reflNorm_hJ (i : Fin 5) : gS i = reflNorm (hJ i) := by
  fin_cases i <;> decide +kernel

theorem ggE6Dep_glueK_gen {Bs K : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) (hcardBs : Nat.card Bs = 3 ^ 6)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G))
    {ι : Additive ↥Bs ≃+ Vec6} {c : ZMod 3}
    (hyι : ι (Additive.ofMul ⟨y, hyBs⟩) = xs + c • xx)
    {κ : Additive ↥Bs →+ Vec6} (hκ : GGE6DepKFrame Bs K y κ)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ρ : Λ → MulAut ↥Bs} {ρa : MulAut ↥Bs}
    (hρrefl : ∀ l, GGIsReflection 3 (ρ l)) (hρa : GGIsReflection 3 ρa)
    (hKgen : ggAutomizer K Bs =
      Subgroup.closure (Set.range (fun l : {l : Λ // l ≠ b} => ρ l) ∪ {ρa}))
    {g : Λ → Mat6} (hg : ∀ l, g l ∈ refl36 ∧ ActsAs ι (ρ l) (g l))
    (hgfix : ∀ l, l ≠ b → g l ∈ reflFix xs)
    (hS : ∀ i : Fin 5, ∃ φ ∈ Subgroup.closure (Set.range fun l : {l : Λ // l ≠ b} => ρ l),
      ActsAs ι φ (gS i)) :
    ∃ (Ma : Mat6) (h : Vec6), ActsAs ι ρa Ma ∧ Ma = rK c h ∧ normK c h = 1 ∧ KGen c h := by
  classical
  let ρ' : Option {l : Λ // l ≠ b} → MulAut ↥Bs :=
    fun o => o.elim ρa (fun l => ρ l.1)
  have hρ'mem : ∀ o, ρ' o ∈ ggAutomizer K Bs := by
    intro o
    rw [hKgen]
    cases o with
    | none => exact Subgroup.subset_closure (Or.inr rfl)
    | some l => exact Subgroup.subset_closure (Or.inl ⟨l, rfl⟩)
  have hrange : Set.range ρ' =
      Set.range (fun l : {l : Λ // l ≠ b} => ρ l) ∪ {ρa} := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr rfl
      | some l => exact Or.inl ⟨l, rfl⟩
    · rintro (⟨l, rfl⟩ | rfl)
      · exact ⟨some l, rfl⟩
      · exact ⟨none, rfl⟩
  have hgen' : ggAutomizer K Bs = Subgroup.closure (Set.range ρ') := by
    rw [hKgen, hrange]
  have hρ'refl : ∀ o, GGIsReflection 3 (ρ' o) := by
    intro o
    cases o with
    | none => exact hρa
    | some l => exact hρrefl l.1
  have hρ'y : ∀ o, ρ' o ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := fun o =>
    ggAutomizer_fix_of_centralizes hyBs hKy (ρ' o) (hρ'mem o)
  obtain ⟨k, hk, hkgen⟩ :=
    ggE6Dep_extractK hyBs hy1 hy3 hcardBs hκ ρ' hρ'refl hρ'y hgen'
  obtain ⟨M, hκM, hM5, hMonto, hMy, hMker⟩ := kappa_matrix hyBs hκ hyι
  have hiso : ∀ i : Fin 5, ∀ v, bil6 (M.mulVec v) (M.mulVec (hJ i)) = bil6 v (hJ i) := by
    intro i
    obtain ⟨φ, hφcl, hφact⟩ := hS i
    have hφA : φ ∈ ggAutomizer K Bs := by
      rw [hKgen]
      exact Subgroup.closure_mono Set.subset_union_left hφcl
    have hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
      ggAutomizer_fix_of_centralizes hyBs hKy φ hφA
    have hφrefl : GGIsReflection 3 φ :=
      ggIsReflection_of_actsAs hφact (gS_mul_self i) (card_gS i)
    obtain ⟨k_i, hk_i_mem, hk_i_act⟩ := hκ.2.2.2.1 φ hφA
    have hk_i_refl36 : k_i ∈ refl36 :=
      ggE6Dep_frameK_refl hyBs hy1 hy3 hcardBs hκ hφrefl hφy hk_i_mem hk_i_act
    have hcomm : M * gS i = k_i * M := mat_comm_of_acts hκM hφact hk_i_act
    have hconj : M * reflNorm (hJ i) = k_i * M := by
      rw [← gS_eq_reflNorm_hJ i]
      exact hcomm
    exact (refl_equivariance hMonto (hJ_norm i) hk_i_refl36 hconj).1
  obtain ⟨r, hr⟩ := gram_block hMy hiso
  have hr1 : r = 1 := gbetaR_scale hr hMonto hM5 hMy hMker
  have hG : Mᵀ * gram6 * M = gbeta c := by
    rw [hr, hr1, gbetaR_one]
  obtain ⟨Ma, hMa⟩ := exists_actsAs ι ρa
  have hMa2 : Ma * Ma = 1 := by
    have hmul : ActsAs ι (ρa * ρa) (Ma * Ma) := hMa.mul hMa
    have hρa2 : ρa * ρa = 1 := by rw [← pow_two]; exact hρa.1
    rw [hρa2] at hmul
    exact actsAs_inj hmul (ActsAs.one ι)
  have hMay : Ma.mulVec (kY c) = kY c := by
    have h := hMa ⟨y, hyBs⟩
    rw [show ρa ⟨y, hyBs⟩ = ⟨y, hyBs⟩ from
      ggAutomizer_fix_of_centralizes hyBs hKy ρa (by
        rw [hKgen]
        exact Subgroup.subset_closure (Or.inr rfl)), hyι] at h
    rw [← kY_eq c] at h
    exact h.symm
  have hk_none_mem : k none ∈ refl36 := (hk none).1
  rw [refl36] at hk_none_mem
  obtain ⟨d, hd, hdk⟩ := Finset.mem_image.mp hk_none_mem
  rw [Finset.mem_filter] at hd
  obtain ⟨-, hd5, hdn⟩ := hd
  have hd_eq : k none = reflNorm d := hdk.symm
  have hconj : M * Ma = reflNorm d * M := by
    have h := mat_comm_of_acts hκM hMa (hk none).2
    rw [hd_eq] at h
    exact h
  obtain ⟨h, hn, hMah, hMh⟩ :=
    refl_eq_rK hMy hMker hMonto hG hMa2 hMay hd5 hdn hconj
  have hcov : ∀ o : Option {l : Λ // l ≠ b},
      ∃ u, (u ∈ cS ∨ u = h) ∧ k o = reflNorm (M.mulVec u) := by
    intro o
    cases o with
    | none =>
        exact ⟨h, Or.inr rfl, by rw [hd_eq, hMh]⟩
    | some l =>
        obtain ⟨u, hu, hgu⟩ := reflFix_xs_centre (g l.1) (hgfix l.1 l.2)
        refine ⟨u, Or.inl hu, ?_⟩
        have hnu : norm6 u = 1 := by
          rw [cS] at hu
          exact (Finset.mem_filter.mp hu).2.2.2
        have hcomm : M * g l.1 = k (some l) * M :=
          mat_comm_of_acts hκM (hg l.1).2 (hk (some l)).2
        have hconj : M * reflNorm u = k (some l) * M := by
          rw [← hgu]
          exact hcomm
        exact (refl_equivariance hMonto hnu (hk (some l)).1 hconj).2.2
  have hKGen : KGen c h :=
    kgen_of_conjGenerates hMy hMker hM5 hG k hkgen hcov
  exact ⟨Ma, h, hMa, hMah, hn, hKGen⟩

end E6Dep

end CFSG.StandardType

end
