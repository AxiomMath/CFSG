module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828J
public import CFSG.Quasithin.Vol2.Ch8Sec2L827G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section L828F

variable {G : Type} [Group G] [Finite G]

theorem concl828_aux {V U X : Subgroup G} {h : G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hNX : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hperf : ⁅X, X⁆ = X) (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X))
    (hXC : ¬ X ≤ Subgroup.centralizer (U : Set G))
    (hJU : ch82I V h ≤ Subgroup.centralizer (U : Set G)) (hhJ : h ∈ ch82I V h) :
    ⁅X, Subgroup.centralizer (U : Set G)⁆ ≤ pCoreOf 2 X ∧
      X ≤ Subgroup.normalizer (ch82I V h : Set G) ∧
      X ≤ Subgroup.normalizer (pCoreOf 2 (ch82I V h) : Set G) ∧
      ⁅V, X⁆ ≤ ch82B V h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.centralizer_le_normalizer _).trans hNX
  have hNC : Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have h2 : ⁅X, Subgroup.centralizer (U : Set G)⁆ ≤ pCoreOf 2 X := by
    refine commutator_le_pCoreOf_828 (D := X ⊓ Subgroup.centralizer (U : Set G)) hq hperf hCN
      inf_le_left ?_ ?_ ?_
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        ((le_inf Subgroup.le_normalizer (hXU.trans hNC)).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
    · intro e
      apply hXC
      rw [← e]
      exact inf_le_right
    · exact le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hCN)
        (Subgroup.le_normalizer_iff_commutator_le_right.mp (hXU.trans hNC))
  have hhX : h ∈ Subgroup.normalizer (X : Set G) := hCN (hJU hhJ)
  have hconj : ∀ x ∈ X, h⁻¹ * x * h ∈ X := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhX) x).mp hx
    simpa using this
  have hXVh : X ≤ Subgroup.normalizer (B6.conjSub h V : Set G) := by
    intro x hx
    have hx1 := hconj x hx
    have hx2 := hconj x⁻¹ (X.inv_mem hx)
    refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
    · rw [B6.mem_conjSub] at hy ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXV hx1) _).mp hy
      have e : h⁻¹ * (x * y * x⁻¹) * h =
          h⁻¹ * x * h * (h⁻¹ * y * h) * (h⁻¹ * x * h)⁻¹ := by group
      rw [e]
      exact h1
    · rw [B6.mem_conjSub] at hy ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXV hx2) _).mp hy
      have e : h⁻¹ * (x⁻¹ * y * x) * h =
          h⁻¹ * x⁻¹ * h * (h⁻¹ * y * h) * (h⁻¹ * x⁻¹ * h)⁻¹ := by group
      rw [e]
      exact h1
  have hXJ : X ≤ Subgroup.normalizer (ch82I V h : Set G) := by
    intro x hx
    have h1 := hXV hx
    have h2 := hXVh hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    show (V ⊔ B6.conjSub h V).map _ = V ⊔ B6.conjSub h V
    rw [Subgroup.map_sup, h1, h2]
  have hJX : ⁅ch82I V h, X⁆ ≤ pCoreOf 2 (ch82I V h) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hXJ)
      (Subgroup.normalizer_commutator_ge_left _ _) ?_
    refine (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le ?_
    calc ⁅ch82I V h, X⁆ ≤ ⁅Subgroup.centralizer (U : Set G), X⁆ :=
          Subgroup.commutator_mono hJU le_rfl
      _ = ⁅X, Subgroup.centralizer (U : Set G)⁆ := Subgroup.commutator_comm _ _
      _ ≤ pCoreOf 2 X := h2
  exact ⟨h2, hXJ, hXJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _),
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hXV)
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans hJX)⟩

theorem stmt8_2_8_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (h734 : Stmt7_3_4) (h822 : Stmt8_2_2) (h825 : Stmt8_2_5) (hxi : Step827Xi)
    (hOneB : Step828OneB) : Stmt8_2_8 := by
  have hLU : HLU82 := hLU82_holds
  have h827 : Step827 := step827_of h37 h38 hmod h711n hcard h734 h822 h825 hxi
  have hOneA : Step828OneA := step828OneA_holds h37 h38 hmod h711n hcard h825 h827
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, hIU, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, hcoc⟩ :=
    lu_facts_828 hLU hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe hLUT
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ x.2.1)⟩
  have hLUU : ch82LU L (ch82U (fsuV T I) h) ≤
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hS : QuasithinUnique.IsSylowTwoOf T
      (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) :=
    ⟨hTU, hyp.fsu.sylow.1, fun h2 =>
      hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTU))⟩
  obtain ⟨K, hK, hLUK, hKn⟩ := exists_k_828 h37 h38 h39 hyp hU2 hU1 hTU hLUU hfam hLUT
  have hq := h827 G T L I hyp h731 h821 hc hrow H h k hH hh hC K hK hLUK
  obtain ⟨-, hhI, -, -, -, -, -, -, -, hdisj, -⟩ := id hC
  have hdih : k = 1 → ∃ m : ℕ, Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h)
      (ch82I (fsuV T I) h) ≃* DihedralGroup m) := by
    intro hk
    subst hk
    rcases hdisj with ⟨-, m, -, -, hm⟩ | hP | hSz
    · exact ⟨m, hm⟩
    · obtain ⟨⟨-, -, -, h22, -⟩, -⟩ := hP
      exact absurd rfl h22
    · obtain ⟨-, a, ha, -, -, -, he, -⟩ := hSz
      omega
  have hk1 : wParam T (fsuV T I) = 1 → k = 1 := fun hw => by
    have h1 := hC5.1
    rw [hw] at h1
    exact_mod_cast h1.symm
  have hKeq : K = ch82LU L (ch82U (fsuV T I) h) := by
    rcases id hrow with hr | hr | hr | hr
    · obtain ⟨m, hm⟩ := hdih (hk1 (hC5.2.2.2.1 hr).1)
      by_cases h3 : 3 ∣ m
      · exact hOneA G T L I hyp h731 h821 hc hrow H h k hH hh hC ⟨Or.inl hr, m, h3, hm⟩ K hK
          hLUK
      · exact hOneB G T L I hyp h731 h821 hc hrow H h k hH hh hC
          (Or.inl ⟨Or.inl hr, m, h3, hm⟩) K hK hLUK
    · obtain ⟨m, hm⟩ := hdih (hk1 (hC5.2.2.2.2.1 hr).1)
      by_cases h3 : 3 ∣ m
      · exact hOneA G T L I hyp h731 h821 hc hrow H h k hH hh hC ⟨Or.inr hr, m, h3, hm⟩ K hK
          hLUK
      · exact hOneB G T L I hyp h731 h821 hc hrow H h k hH hh hC
          (Or.inl ⟨Or.inr hr, m, h3, hm⟩) K hK hLUK
    · exact hOneB G T L I hyp h731 h821 hc hrow H h k hH hh hC (Or.inr hr) K hK hLUK
    · have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
      have hfam' : ch82LU L (ch82U (fsuV T I) h) ∈ cComp (ch82LU L (ch82U (fsuV T I) h) ⊔ T) :=
        hfam
      exact eq_of_autSub_eq_top_828 (V := fsuV T I) hUV hfam' hLUK hK hKn hS hq hLUC (hcoc hr)
  subst hKeq
  have hNX : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤
      Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLUU).mp hKn
  obtain ⟨h2, h4a, h4b, h5⟩ := concl828_aux ((perfectCore_le _).trans (inf_le_left.trans hLN))
    hLUU hNX (perfectCore_perfect _) hq hLUC hIU hhI
  exact ⟨hNX, h2, h4a, h4b, h5⟩

end L828F

end CFSG.Quasithin.H13
