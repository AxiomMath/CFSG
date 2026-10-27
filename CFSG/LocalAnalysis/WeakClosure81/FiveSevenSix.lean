module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveBase
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenAltSub
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenAutSix
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenEmb
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenSixCent
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenSixSyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Equiv

variable {G : Type} [Group G] [Finite G]

theorem exists_embedding_of_six {H M A : Subgroup G} (h : Sec5Hyp H M A)
    (hM : maxOver H A = {M}) (hHA : H = Fstar H ⊔ A) (e : ↥(Fstar H) ≃* alternatingGroup (Fin 6)) :
    ∃ ι : ↥H →* Perm (Fin 6), Function.Injective ι ∧
      ((Fstar H).subgroupOf H).map ι = alternatingGroup (Fin 6) := by
  obtain ⟨φ, hφinj, hφ, hφapp⟩ :=
    exists_injective_conj_apply_of_fstar_alt (by norm_num : 5 ≤ 6) e
  refine exists_embedding_of_forall_mem_range (by norm_num) hHA e φ hφinj hφ (fun a ha => ?_)
  by_contra hnot
  obtain ⟨hMmax, -, -⟩ := isUniqueMaxOver_iff.1 hM
  have hMH : M ≤ H := hMmax.le
  have hFH : Fstar H ≤ H := fstar_le_group H
  have haa : a * a = 1 := by
    apply Subtype.ext
    simpa [pow_two] using h.isElemAbelian.2 (a : G) ha
  have h2 : φ a * φ a = 1 := by rw [← map_mul, haa, map_one]
  have hten : Nat.card {l : alternatingGroup (Fin 6) // φ a l = l} = 10 :=
    card_fixedPoints_eq_ten_of_not_mem_range_conjNormal h2 hnot
  have hcent : Nat.card ↥(Fstar H ⊓ Subgroup.centralizer ({(a : G)} : Set G)) = 10 := by
    rw [card_fstar_inf_centralizer_eq_card_fixedPoints e φ hφapp a, hten]
  have hFcard : Nat.card ↥(Fstar H) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hAC : A ≤ H ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨h.le_group hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨(a : G), ha⟩)
  have hCH : H ⊓ Subgroup.centralizer ({(a : G)} : Set G) ≠ H := by
    intro hCeq
    have hFC : Fstar H ⊓ Subgroup.centralizer ({(a : G)} : Set G) = Fstar H := by
      refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.2 ⟨hx, ?_⟩
      have hxC : x ∈ H ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
        rw [hCeq]
        exact hFH hx
      exact (Subgroup.mem_inf.1 hxC).2
    rw [hFC, hFcard] at hcent
    omega
  have hCM : H ⊓ Subgroup.centralizer ({(a : G)} : Set G) ≤ M := by
    rcases le_or_eq_of_maxOver_eq_singleton hM inf_le_left hAC with hle | heq
    · exact hle
    · exact absurd heq hCH
  have h5 : 5 ∣ Nat.card ↥(Fstar H ⊓ M) := by
    have hle : Fstar H ⊓ Subgroup.centralizer ({(a : G)} : Set G) ≤ Fstar H ⊓ M := by
      intro x hx
      obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxF, hCM (Subgroup.mem_inf.2 ⟨hFH hxF, hxC⟩)⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcent] at hdvd
    exact (by norm_num : 5 ∣ 10).trans hdvd
  have hFnormal : ((Fstar H).subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using conj_mem_fstar g.2 hx
  have h8 : 8 ∣ Nat.card ↥(Fstar H ⊓ M) := by
    have hdvd := two_pow_factorization_dvd_card_inf hMH h.odd_relIndex hFH hFnormal
    have hf : (360 : ℕ).factorization 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      decide +kernel
    rw [hFcard, hf] at hdvd
    simpa using hdvd
  have hcard : Nat.card ↥((Fstar H ⊓ M).subgroupOf (Fstar H)) = Nat.card ↥(Fstar H ⊓ M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hN : (Fstar H ⊓ M).subgroupOf (Fstar H) = ⊤ :=
    eq_top_of_dvd_card_of_mulEquiv_alternatingGroup_six e (by rw [hcard]; exact h8)
      (by rw [hcard]; exact h5)
  have hFM : Fstar H ≤ M := by
    intro x hx
    have hxN : (⟨x, hx⟩ : ↥(Fstar H)) ∈ (Fstar H ⊓ M).subgroupOf (Fstar H) := by
      rw [hN]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hxN)).2
  exact h.not_le (hHA.le.trans (sup_le hFM h.le_M))

end CFSG.LocalAnalysis.WeakClosure81
