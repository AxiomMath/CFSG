module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Vol2.Ch11SecA11Comp
public import CFSG.Quasithin.Vol2.Ch11SecA11Point
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n i : ℕ} {U K : Subgroup G}

theorem charTwo_normalizer (h : Hyp11 G T L I n) (hU : IsVi T L I n i U) (hi : 1 ≤ i) :
    QuasithinUnique.CharTwo (Subgroup.normalizer (U : Set G)) := by
  refine charTwo_of_inH h.fsu.qtke.2.1 (h.fsu.sylow.1.toSylow h.fsu.sylow.2)
    ⟨IsVi.le_normalizer hU, fun h0 => IsVi.ne_bot h hU hi (eq_bot_iff.mpr ?_)⟩
  rw [← h0]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    ((isPGroup_fsuV h).to_le (IsVi.le_fsuV hU))

theorem charTwo_of_cComp (h : Hyp11 G T L I n) (hU : IsVi T L I n i U) (hi : 1 ≤ i)
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    QuasithinUnique.CharTwo K := by
  have hle := le_of_mem_cComp hK
  have hn : (K.subgroupOf (Subgroup.normalizer (U : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hNK
  exact QuasithinUnique.CharTwo.of_isSubnormal (charTwo_normalizer h hU hi) hle hn.isSubnormal

theorem lOf_ne_bot (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n i U) (hi : i = 1 ∨ i = 2) : LOf L U ≠ ⊥ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h hi hU
  obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_of_mulEquiv_SL2 h.one_lt hK e
  intro hbot
  have : Subsingleton ↥(LOf L U) := by
    rw [hbot]
    infer_instance
  exact hab (Subsingleton.elim _ _)

omit [Finite G] in
theorem le_conjClosure (K X : Subgroup G) : K ≤ conjClosure K X := fun k hk =>
  Subgroup.subset_closure ⟨1, X.one_mem, k, hk, by group⟩

omit [Finite G] in
theorem commutator_le_of_le_normalizer {K X : Subgroup G}
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) : ⁅K, X⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro k hk x hx
  rw [commutatorElement_def]
  exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKX hk) x).mp hx) (X.inv_mem hx)

theorem le_of_cComp_of_perfect {Y X B : Subgroup G} (hK : K ∈ cComp Y) (hXY : X ≤ Y)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hBne : B ≠ ⊥) (hB : ⁅B, B⁆ = B) (hBK : B ≤ K)
    (hBX : B ≤ X) : K ≤ X := by
  rcases cComp_commutator_dichotomy_of_le hK hXY with ⟨-, hs⟩ | heq
  · have hle : B ≤ ⁅K, X⁆ := hB ▸ Subgroup.commutator_mono hBK hBX
    exact (hBne (eq_bot_of_perfect_of_le_solvable hle hB)).elim
  · exact (le_conjClosure K X).trans (heq ▸ commutator_le_of_le_normalizer hKX)

theorem le_centralizer_of_cComp (hF11 : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 U)
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G))) (hLK : LOf L U ≤ K) :
    K ≤ Subgroup.centralizer (U : Set G) := by
  have hKN := le_of_mem_cComp hK
  refine le_of_cComp_of_perfect hK (Subgroup.centralizer_le_normalizer _)
    (fun k hk => mem_normalizer_centralizer (hKN hk)) (lOf_ne_bot hN h1102 h hU (Or.inl rfl))
    (perfectCore_perfect _) hLK (lOf_one_le_centralizer hF11 h1102 h hU)

theorem not_le_normalizer_of_lt (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n i U) (hi : i = 1 ∨ i = 2)
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G))) (hlt : LOf L U < K) :
    ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hKN := le_of_mem_cComp hK
  have hKX : K ≤ L ⊓ Subgroup.normalizer (U : Set G) := by
    refine le_of_cComp_of_perfect hK inf_le_right ?_ (lOf_ne_bot hN h1102 h hU hi)
      (perfectCore_perfect _) hlt.le (perfectCore_le _)
    exact (le_inf hKM (hKN.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKL : K ≤ LOf L U := by
    rw [← perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK)]
    exact perfectCore_mono hKX
  exact hlt.not_ge hKL

end CFSG.Quasithin.Vol2.Ch11.SecA
