module

public import CFSG.Timmesfeld.ARS.QDCentralizer
public import CFSG.Timmesfeld.ARS.Sec3Pairs
public import CFSG.Timmesfeld.ARS.Sec4RootClosure

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace QD

theorem le_of_forall_le_sup_mem_lambdaSet [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {D B C K : Subgroup G} (hD : D ∈ R) (hB : B ∈ R) (hCB : C ∈ lambdaSet R B)
    (hline : ∀ P ∈ R, P ≤ B ⊔ C → P ∈ lambdaSet R D) (hCK : C ≤ K)
    (hK : ∀ g ∈ Subgroup.centralizer (D : Set G), conjSub K g ≤ K) : B ≤ K := by
  have hCR : C ∈ R := hCB.1.1
  have hBl : B ∈ lambdaSet R C := mem_lambdaSet_comm hB hCB
  have hCD : C ∈ lambdaSet R D := hline C hCR le_sup_right
  have hBD : B ∈ lambdaSet R D := hline B hB le_sup_left
  obtain ⟨A, hA, hAn⟩ := Set.not_subset.1 (not_subset_centralSet_union_psiSet hR hiso hD hCD)
  have hAR : A ∈ R := by rcases hA with h | h <;> exact h.1
  have hCA : Opposite C A := by
    have hne : C ≠ A := fun e => hAn (Or.inl ⟨hAR, e ▸ hR.commuting_self hCR⟩)
    rcases hR.rel C hCR A hAR hne with h | h | h
    · exact absurd (Or.inl ⟨hAR, h⟩) hAn
    · exact h
    · exact absurd (Or.inr ⟨hAR, h⟩) hAn
  have hAD : Special R A D := by
    have hnc : ¬ Commuting A D :=
      not_commuting_of_opposite_of_mem_lambdaSet hR hAR hCA.symm (mem_lambdaSet_comm hD hCD)
    rcases hA with h | h
    · exact absurd h.2.symm hnc
    · exact h.2.symm
  have hAB : ¬ Commuting A B := not_commuting_of_opposite_of_mem_lambdaSet hR hAR hCA.symm hBl
  obtain ⟨B₀, ⟨hB₀R, hB₀le, hB₀A⟩, huniq⟩ :=
    existsUnique_mem_psiSet_of_le hR hiso hCR hAR hCA hBl
  have hN : Commuting (D ⊔ ⁅A, D⁆) (B₀ ⊔ ⁅A, B₀⁆) := by
    have hne : A ≠ B := fun e => hAB (e ▸ hR.commuting_self hAR)
    rcases hR.rel A hAR B hB hne with h | h | h
    · exact absurd h hAB
    · exact (natural_modules_of_opposite_opposite hR hiso hAR hCR hB hCA.symm h ⟨hD, hAD⟩ hCB hCD
        hBD hB₀le hB₀A).2.2.1
    · have hB₀B : B = B₀ := huniq B ⟨hB, le_sup_right, hB, h⟩
      obtain ⟨Q, hQ, hQle, hQC, hQB⟩ := exists_mem_le_sup_ne_ne hR hiso hCR hBl C B
      have := (natural_modules_of_opposite_special hR hiso hAR hCR hCA.symm ⟨hB, h⟩ ⟨hD, hAD⟩
        hCB hCD ⟨Q, hQ, hQle, hQC, hQB, hline Q hQ (sup_comm C B ▸ hQle)⟩).2.2.1
      rwa [hB₀B] at this
  have hB₀C : C ≠ B₀ := fun e => Special.not_opposite hR hAR hB₀A.2 (e ▸ hCA.symm)
  obtain ⟨hB₀l, hsup⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hCR hBl hCR le_sup_left hB₀R hB₀le hB₀C
  have hS := Sec3.setOf_mem_le_sup_eq hR hiso hCR hAR hCA hB₀l hB₀A
  rw [hsup] at hS
  have hpt : ∀ P ∈ R, P ≤ C ⊔ B → P ≠ B₀ → P ≤ K := by
    intro P hP hPle hPB₀
    have hmem : P ∈ {E | E ∈ R ∧ E ≤ C ⊔ B} := ⟨hP, hPle⟩
    rw [hS] at hmem
    rcases hmem with h | ⟨⟨n, hn⟩, rfl⟩
    · exact absurd h hPB₀
    · have hnD : n ∈ Subgroup.centralizer (D : Set G) := Subgroup.mem_centralizer_iff.2
        fun d hd => (hN d (Subgroup.mem_sup_left hd) n hn).eq
      exact (Subgroup.map_mono hCK).trans (hK n hnD)
  obtain ⟨Q, hQ, hQle, hQC, hQB₀⟩ := exists_mem_le_sup_ne_ne hR hiso hCR hBl C B₀
  have hQsup := (mem_lambdaSet_of_le_sup hR hiso hCR hBl hQ hQle hCR le_sup_left hQC).2
  calc B ≤ C ⊔ B := le_sup_right
    _ = Q ⊔ C := hQsup.symm
    _ ≤ K := sup_le (hpt Q hQ hQle hQB₀) hCK

@[expose] def zTwo (R : Set (Subgroup G)) (D : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Q R D ∧ ∀ x ∈ Q R D, ⁅y, x⁆ ∈ D}
  one_mem' := ⟨one_mem _, fun x _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
  mul_mem' := by
    rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
    refine ⟨mul_mem hy hz, fun x hx => ?_⟩
    have e : ⁅y * z, x⁆ = y * ⁅z, x⁆ * y⁻¹ * ⁅y, x⁆ := by
      simp only [commutatorElement_def]
      group
    have hc : y * ⁅z, x⁆ * y⁻¹ = ⁅z, x⁆ := by
      rw [← Subgroup.mem_centralizer_iff.1 (Q_le_centralizer hy) _ (hz' x hx),
        mul_inv_cancel_right]
    rw [e, hc]
    exact mul_mem (hz' x hx) (hy' x hx)
  inv_mem' := by
    rintro y ⟨hy, hy'⟩
    refine ⟨inv_mem hy, fun x hx => ?_⟩
    have e : ⁅y⁻¹, x⁆ = y⁻¹ * (⁅y, x⁆⁻¹ * y) := by
      simp only [commutatorElement_def]
      group
    rw [e, Subgroup.mem_centralizer_iff.1 (Q_le_centralizer hy) _ (inv_mem (hy' x hx)),
      inv_mul_cancel_left]
    exact inv_mem (hy' x hx)

section ZTwo

variable {D : Subgroup G}

theorem mem_zTwo {y : G} : y ∈ zTwo R D ↔ y ∈ Q R D ∧ ∀ x ∈ Q R D, ⁅y, x⁆ ∈ D := Iff.rfl

theorem zTwo_le_Q : zTwo R D ≤ Q R D := fun _ hy => hy.1

variable (hR : IsRootClass R)
include hR

theorem le_zTwo_self (hD : D ∈ R) : D ≤ zTwo R D := by
  intro d hd
  refine ⟨le_Q_self hR hD hd, fun x hx => ?_⟩
  have h1 : d * x = x * d := Subgroup.mem_centralizer_iff.1 (Q_le_centralizer hx) d hd
  rw [(commutatorElement_eq_one_iff_mul_comm).2 h1]
  exact one_mem _

theorem conjSub_zTwo_le {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    conjSub (zTwo R D) g ≤ zTwo R D := by
  rintro _ ⟨y, ⟨hy, hy'⟩, rfl⟩
  change g * y * g⁻¹ ∈ zTwo R D
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← conjSub_Q hR hg]
    exact conj_mem_conjSub g hy
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ Q R D := by
    rw [← conjSub_Q hR (Subgroup.inv_mem _ hg)]
    exact conj_mem_conjSub g⁻¹ hx
  have e : ⁅g * y * g⁻¹, x⁆ = g * ⁅y, g⁻¹ * x * g⁻¹⁻¹⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 hg _).1 (hy' _ hx')

omit hR in
theorem le_zTwo_iff {B : Subgroup G} (hB : B ∈ isolatedSet R D) :
    B ≤ zTwo R D ↔ ∀ X ∈ isolatedSet R D, ⁅B, X⁆ ≤ D := by
  constructor
  · intro h X hX
    rw [Subgroup.commutator_le]
    intro b hb x hx
    exact (h hb).2 x (le_Q hX hx)
  · intro h b hb
    refine ⟨le_Q hB hb, fun x hx => ?_⟩
    refine (gen_induction (p := fun x => x ∈ Q R D ∧ ⁅b, x⁆ ∈ D) hx
      (fun X hX y hy => ⟨le_Q hX hy, h X hX (Subgroup.commutator_mem_commutator hb hy)⟩)
      ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩ ?_).2
    rintro y z ⟨hy, hby⟩ ⟨hz, hbz⟩
    refine ⟨mul_mem hy hz, ?_⟩
    have e : ⁅b, y * z⁆ = ⁅b, y⁆ * (y * ⁅b, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, ← Subgroup.mem_centralizer_iff.1 (Q_le_centralizer hy) _ hbz, mul_inv_cancel_right]
    exact mul_mem hby hbz

theorem commutator_eq_of_le_zTwo [Finite G] (hiso : NoIsolated R) (hD : D ∈ R)
    {B X : Subgroup G} (hB : B ∈ isolatedSet R D) (hBz : B ≤ zTwo R D)
    (hX : X ∈ isolatedSet R D) (h : ¬ Commuting B X) : ⁅B, X⁆ = D :=
  eq_of_le_of_mem hR hiso (special_of_mem_isolatedSet hR hB hX h).1.1 hD
    ((le_zTwo_iff hB).1 hBz X hX)

end ZTwo

section Class

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {D : Subgroup G} (hD : D ∈ R)
include hR hiso hnd hΩ hD

theorem mem_lambdaSet_of_le_zTwo {B : Subgroup G} (hB : B ∈ isolatedSet R D)
    (hBz : B ≤ zTwo R D) (hBD : B ≠ D) : B ∈ lambdaSet R D := by
  obtain ⟨X, hX, hBX⟩ : ∃ X ∈ isolatedSet R D, ¬ Commuting B X := by
    by_contra! h
    exact hBD (eq_of_mem_isolatedSet_of_forall_commuting hR hiso hnd hΩ hD hB h)
  exact mem_lambdaSet_of_commutator_eq hR hiso hD hB.1.1 hX.1.1
    (commutator_eq_of_le_zTwo hR hiso hD hB hBz hX hBX)

omit hnd hΩ hD in
theorem mem_lambdaSet_of_le_sup_commutator {X Y : Subgroup G} (hXl : X ∈ lambdaSet R D)
    (hY : Y ∈ isolatedSet R D) (hs : Special R X Y) (hCl : ⁅X, Y⁆ ∈ lambdaSet R D) :
    ∀ P ∈ R, P ≤ X ⊔ ⁅X, Y⁆ → P ∈ lambdaSet R D := by
  intro P hP hPle
  by_cases hPC : P = ⁅X, Y⁆
  · rw [hPC]
    exact hCl
  obtain ⟨y, hy, rfl⟩ := exists_eq_conjSub_of_le_sup hR hiso hXl.1.1 hY.1.1 hs hP
    (sup_comm X _ ▸ hPle) hPC
  have := conjSub_mem_lambdaSet hR hXl y
  rwa [conjSub_of_forall_commute fun d hd => (hY.1.2 d hd y hy).symm] at this

theorem mem_lambdaSet_of_forall_commutator_le_zTwo {E : Subgroup G} (hE : E ∈ isolatedSet R D)
    (hED : E ≠ D) (h : ∀ Y ∈ isolatedSet R D, ¬ Commuting E Y → ⁅E, Y⁆ ≤ zTwo R D) :
    E ∈ lambdaSet R D := by
  by_contra hEl
  have hER : E ∈ R := hE.1.1
  obtain ⟨B, hBl, hEB⟩ : ∃ B ∈ lambdaSet R D, ¬ Commuting E B := by
    by_contra! hall
    have hM : Commuting E (M R D) := commuting_iff_le_centralizer.2
      (sup_le (commuting_iff_le_centralizer.1 hE.1.2.symm)
        (iSup₂_le fun B hB => commuting_iff_le_centralizer.1 (hall B hB)))
    have hmem : E ∈ {B | B ∈ R ∧ Commuting B (M R D)} := ⟨hER, hM⟩
    rw [setOf_commuting_M_eq_singleton hR hiso hnd hΩ hD, Set.mem_singleton_iff] at hmem
    exact hED hmem
  have hBI := lambdaSet_subset_isolatedSet hR hD hBl
  obtain ⟨hs, hCI⟩ := special_of_mem_isolatedSet hR hE hBI hEB
  have hCz : ⁅E, B⁆ ≤ zTwo R D := h B hBI hEB
  have hCD : ⁅E, B⁆ ≠ D := fun e => hEl (mem_lambdaSet_of_commutator_eq hR hiso hD hER hBI.1.1 e)
  have hCl := mem_lambdaSet_of_le_zTwo hR hiso hnd hΩ hD hCI hCz hCD
  have hcomm : ⁅B, E⁆ = ⁅E, B⁆ := Subgroup.commutator_comm B E
  have hBz : B ≤ zTwo R D := by
    refine le_of_forall_le_sup_mem_lambdaSet hR hiso hD hBI.1.1
      (mem_lambdaSet_comm hs.1 (mem_lambdaSet_commutator hR hiso hER hBI.1.1 hs).2) ?_ hCz
      fun g hg => conjSub_zTwo_le hR ((Subgroup.centralizer_le_normalizer _) hg)
    rw [← hcomm]
    exact mem_lambdaSet_of_le_sup_commutator hR hiso hBl hE hs.symm (hcomm ▸ hCl)
  rw [← hcomm] at hCD
  exact hCD (commutator_eq_of_le_zTwo hR hiso hD hBI hBz hE fun h' => hEB h'.symm)

theorem le_zTwo {E : Subgroup G} (hE : E ∈ isolatedSet R D) : E ≤ zTwo R D := by
  by_contra hEz
  obtain ⟨E₁, ⟨hE₁I, hE₁z⟩, hmin⟩ := exists_forall_not_le_commutator (isPGroup_Q hR)
    (P := {E | E ∈ isolatedSet R D ∧ ¬ E ≤ zTwo R D}) (fun X hX => le_Q hX.1)
    (fun X hX => hR.ne_bot X hX.1.1.1) ⟨hE, hEz⟩
  have hlev : ∀ Y ∈ isolatedSet R D, ¬ Commuting E₁ Y → ⁅E₁, Y⁆ ≤ zTwo R D := by
    intro Y hY hnc
    by_contra hz
    exact hmin _ ⟨(special_of_mem_isolatedSet hR hE₁I hY hnc).2, hz⟩
      (Subgroup.commutator_mono le_rfl (le_Q hY))
  have hE₁D : E₁ ≠ D := fun e => hE₁z (by rw [e]; exact le_zTwo_self hR hD)
  have hE₁l := mem_lambdaSet_of_forall_commutator_le_zTwo hR hiso hnd hΩ hD hE₁I hE₁D hlev
  obtain ⟨F, hF, hEF⟩ : ∃ F ∈ isolatedSet R D, ¬ ⁅E₁, F⁆ ≤ D := by
    by_contra! h
    exact hE₁z ((le_zTwo_iff hE₁I).2 h)
  have hnc : ¬ Commuting E₁ F := fun h' => hEF (by
    rw [commuting_iff_commutator_eq_bot.1 h']
    exact bot_le)
  obtain ⟨hs, hCI⟩ := special_of_mem_isolatedSet hR hE₁I hF hnc
  have hCz := hlev F hF hnc
  have hCD : ⁅E₁, F⁆ ≠ D := fun e => hEF e.le
  have hCl := mem_lambdaSet_of_le_zTwo hR hiso hnd hΩ hD hCI hCz hCD
  exact hE₁z (le_of_forall_le_sup_mem_lambdaSet hR hiso hD hE₁I.1.1
    (mem_lambdaSet_comm hs.1 (mem_lambdaSet_commutator hR hiso hE₁I.1.1 hF.1.1 hs).1)
    (mem_lambdaSet_of_le_sup_commutator hR hiso hE₁l hF hs hCl) hCz
    fun g hg => conjSub_zTwo_le hR ((Subgroup.centralizer_le_normalizer _) hg))

theorem isolatedSet_eq : isolatedSet R D = insert D (lambdaSet R D) := by
  ext E
  refine ⟨fun hE => ?_, ?_⟩
  · by_cases hED : E = D
    · exact Or.inl hED
    · exact Or.inr (mem_lambdaSet_of_le_zTwo hR hiso hnd hΩ hD hE
        (le_zTwo hR hiso hnd hΩ hD hE) hED)
  · rintro (rfl | hE)
    · exact mem_isolatedSet_self hR hD
    · exact lambdaSet_subset_isolatedSet hR hD hE

end Class

end QD

open QD

theorem Q_eq_M_of_omegaSet [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hnd : IsNondegenerate R) (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
    {D : Subgroup G} (hD : D ∈ R) :
    Q R D = M R D ∧ {B | B ∈ R ∧ B ≤ M R D} = insert D (lambdaSet R D) ∧
      ⁅M R D, M R D⁆ = D ∧ {B | B ∈ R ∧ Commuting B (M R D)} = {D} ∧ IsPGroup 2 ↥(M R D) := by
  have hI := isolatedSet_eq hR hiso hnd hΩ hD
  have hQM : Q R D = M R D := by
    refine le_antisymm (gen_le fun B hB => ?_) (M_le_Q hR hD)
    rw [hI] at hB
    rcases hB with rfl | hB
    · exact le_M_self
    · exact le_M hB
  have hQz : Q R D ≤ zTwo R D := gen_le fun B hB => le_zTwo hR hiso hnd hΩ hD hB
  refine ⟨hQM, Set.ext fun B => ⟨fun hB => ?_, fun hB => ?_⟩, le_antisymm ?_ ?_,
    setOf_commuting_M_eq_singleton hR hiso hnd hΩ hD, (isPGroup_M hR hD).1⟩
  · rw [← hI]
    exact mem_isolatedSet_of_le hR hB.1 (hQM ▸ hB.2)
  · rw [← hI] at hB
    exact ⟨hB.1.1, hQM ▸ le_Q hB⟩
  · rw [← hQM, Subgroup.commutator_le]
    intro x hx y hy
    exact (hQz hx).2 y hy
  · obtain ⟨E, hE⟩ := lambdaSet_nonempty hR hiso hnd hD
    obtain ⟨E', hE', hnc⟩ := exists_mem_lambdaSet_not_commuting hR hiso hD hE
    have hEI := lambdaSet_subset_isolatedSet hR hD hE
    have heq := commutator_eq_of_le_zTwo hR hiso hD hEI (le_zTwo hR hiso hnd hΩ hD hEI)
      (lambdaSet_subset_isolatedSet hR hD hE') hnc
    calc D = ⁅E, E'⁆ := heq.symm
      _ ≤ ⁅M R D, M R D⁆ := Subgroup.commutator_mono (le_M hE) (le_M hE')

theorem Q_eq_M_of_rootClosure [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hnd : IsNondegenerate R) (hRad : ∀ A ∈ R, rootClosure R A = {A}) {D : Subgroup G}
    (hD : D ∈ R) :
    Q R D = M R D ∧ {B | B ∈ R ∧ B ≤ M R D} = insert D (lambdaSet R D) ∧
      ⁅M R D, M R D⁆ = D ∧ {B | B ∈ R ∧ Commuting B (M R D)} = {D} ∧ IsPGroup 2 ↥(M R D) := by
  refine Q_eq_M_of_omegaSet hR hiso hnd (fun A hA B hB h => ?_) hD
  have := mem_rootClosure_of_omegaSet_eq hR hiso hA hB h
  rwa [hRad A hA, Set.mem_singleton_iff] at this

theorem Q_eq_M (h : Hyp G R) {D : Subgroup G} (hD : D ∈ R) :
    Q R D = M R D ∧ {B | B ∈ R ∧ B ≤ M R D} = insert D (lambdaSet R D) ∧
      ⁅M R D, M R D⁆ = D ∧ {B | B ∈ R ∧ Commuting B (M R D)} = {D} ∧ IsPGroup 2 ↥(M R D) := by
  have := h.finite
  exact Q_eq_M_of_omegaSet h.root h.noIsolated h.nondeg
    (fun A hA B hB hΩ => eq_of_omegaSet_eq h hA hB hΩ) hD

end CFSG.Timmesfeld.ARS
