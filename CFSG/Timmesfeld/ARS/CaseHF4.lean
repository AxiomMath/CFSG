module

public import CFSG.Timmesfeld.ARS.CaseHNb

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

theorem commute_x2_x3 (v : F) (r : E) : Commute (c.x2 v) (c.x3 r) :=
  ((positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP').2.2.2.2.2.2.2.2.2.2.1 _
    (c.x3_mem r) _ (c.x2_mem v)).symm

omit [CharP E 2] in
theorem commute_x2_x5 (v : F) (w : E) : Commute (c.x2 v) (c.x5 w) :=
  ((positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP').2.2.2.2.2.2.2.2.1 _
    (c.x5_mem w) _ (c.x2_mem v)).symm

omit [CharP E 2] in
theorem commute_x4 (z : F) {g : G} (hg : g ∈ M R A) : Commute (c.x4 z) g := by
  have := S.hyp.finite
  exact QD.commuting_M S.hyp.root S.hA _ (c.x4_mem z) g hg

theorem x3_inv (r : E) : (c.x3 r)⁻¹ = c.x3 r :=
  inv_eq_of_mul_eq_one_right (by rw [← c.x3_add, CharTwo.add_self_eq_zero, c.x3_zero])

theorem x5_inv (w : E) : (c.x5 w)⁻¹ = c.x5 w :=
  inv_eq_of_mul_eq_one_right (by rw [← c.x5_add, CharTwo.add_self_eq_zero, c.x5_zero])

omit [CharP E 2] in
theorem x2_inv [CharP F 2] (v : F) : (c.x2 v)⁻¹ = c.x2 v :=
  inv_eq_of_mul_eq_one_right (by rw [← c.x2_add, CharTwo.add_self_eq_zero, c.x2_zero])

theorem x5_mul_x3 [CharP F 2] (w r : E) :
    c.x5 w * c.x3 r = c.x4 (c.Tp r w) * (c.x3 r * c.x5 w) := by
  rw [← c.x4_inv, c.x4_Tp, commutatorElement_def]
  group

@[expose] noncomputable def y (v : F) (r : E) (z : F) : G := c.x2 v * c.x3 r * c.x4 z

@[expose] noncomputable def nf (v : F) (r : E) (z : F) (w : E) : G := c.y v r z * c.x5 w

theorem y_mem (v : F) (r : E) (z : F) : c.y v r z ∈ M R A :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (S.P'_le_M (c.x2_mem v)) (Setup.U3_le_M (c.x3_mem r)))
    (QD.le_M_self (c.x4_mem z))

theorem nf_mem (v : F) (r : E) (z : F) (w : E) : c.nf v r z w ∈ M R A :=
  Subgroup.mul_mem _ (c.y_mem v r z) (Setup.U5_le_M (c.x5_mem w))

theorem y_zero : c.y 0 0 0 = 1 := by
  rw [y, c.x2_zero, c.x3_zero, c.x4_zero, one_mul, one_mul]

theorem nf_zero_right (v : F) (r : E) (z : F) : c.nf v r z 0 = c.y v r z := by
  rw [nf, c.x5_zero, mul_one]

theorem y_mul (v : F) (r : E) (z v' : F) (r' : E) (z' : F) :
    c.y v r z * c.y v' r' z' = c.y (v + v') (r + r') (z + z') := by
  have h1 := (c.commute_x4 z (S.P'_le_M (c.x2_mem v'))).eq
  have h2 := (c.commute_x2_x3 v' r).eq
  have h3 := (c.commute_x4 z (Setup.U3_le_M (c.x3_mem r'))).eq
  rw [y, y, y, c.x2_add, c.x3_add, c.x4_add]
  calc c.x2 v * c.x3 r * c.x4 z * (c.x2 v' * c.x3 r' * c.x4 z') =
      c.x2 v * (c.x3 r * (c.x4 z * c.x2 v')) * c.x3 r' * c.x4 z' := by group
    _ = c.x2 v * ((c.x3 r * c.x2 v') * c.x4 z) * c.x3 r' * c.x4 z' := by rw [h1]; group
    _ = c.x2 v * c.x2 v' * c.x3 r * (c.x4 z * c.x3 r') * c.x4 z' := by rw [← h2]; group
    _ = c.x2 v * c.x2 v' * (c.x3 r * c.x3 r') * (c.x4 z * c.x4 z') := by rw [h3]; group

theorem y_inv [CharP F 2] (v : F) (r : E) (z : F) : (c.y v r z)⁻¹ = c.y v r z :=
  inv_eq_of_mul_eq_one_right (by
    rw [c.y_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      c.y_zero])

theorem x5_mul_y [CharP F 2] (w : E) (v : F) (r : E) (z : F) :
    c.x5 w * c.y v r z = c.y v r (z + c.Tp r w) * c.x5 w := by
  have h1 := (c.commute_x2_x5 v w).eq
  have h2 := c.x5_mul_x3 w r
  have h3 := (c.commute_x4 z (Setup.U5_le_M (c.x5_mem w))).eq
  have h4 := (c.commute_x4 (c.Tp r w) (Setup.U3_le_M (c.x3_mem r))).eq
  rw [y, y, c.x4_add]
  calc c.x5 w * (c.x2 v * c.x3 r * c.x4 z) = (c.x5 w * c.x2 v) * c.x3 r * c.x4 z := by group
    _ = c.x2 v * (c.x5 w * c.x3 r) * c.x4 z := by rw [← h1]; group
    _ = c.x2 v * (c.x4 (c.Tp r w) * c.x3 r) * (c.x5 w * c.x4 z) := by rw [h2]; group
    _ = c.x2 v * (c.x3 r * c.x4 (c.Tp r w)) * (c.x4 z * c.x5 w) := by rw [h4, ← h3]
    _ = c.x2 v * c.x3 r * (c.x4 (c.Tp r w) * c.x4 z) * c.x5 w := by group
    _ = c.x2 v * c.x3 r * (c.x4 z * c.x4 (c.Tp r w)) * c.x5 w := by
        rw [← c.x4_add, ← c.x4_add, add_comm]

theorem nf_mul [CharP F 2] (v : F) (r : E) (z : F) (w : E) (v' : F) (r' : E) (z' : F) (w' : E) :
    c.nf v r z w * c.nf v' r' z' w' = c.nf (v + v') (r + r') (z + z' + c.Tp r' w) (w + w') := by
  calc c.nf v r z w * c.nf v' r' z' w' = c.y v r z * (c.x5 w * c.y v' r' z') * c.x5 w' := by
        rw [nf, nf]; group
    _ = c.y v r z * c.y v' r' (z' + c.Tp r' w) * (c.x5 w * c.x5 w') := by
        rw [c.x5_mul_y]; group
    _ = c.nf (v + v') (r + r') (z + z' + c.Tp r' w) (w + w') := by
        rw [c.y_mul, nf, c.x5_add, add_assoc]

theorem proj_nf (v : F) (r : E) (z : F) (w : E) :
    S.proj ⟨c.nf v r z w, c.nf_mem v r z w⟩ = c.vc 0 w r v := by
  have e : (⟨c.nf v r z w, c.nf_mem v r z w⟩ : ↥(M R A)) =
      ⟨c.x2 v, S.P'_le_M (c.x2_mem v)⟩ * ⟨c.x3 r, Setup.U3_le_M (c.x3_mem r)⟩ *
        ⟨c.x4 z, QD.le_M_self (c.x4_mem z)⟩ * ⟨c.x5 w, Setup.U5_le_M (c.x5_mem w)⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, S.proj_P' (c.x2_mem v), S.proj_U3 (c.x3_mem r),
    S.proj_A (c.x4_mem z), S.proj_U5 (c.x5_mem w)]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> apply Subtype.ext <;>
    simp [vc, c.x6_zero]

theorem nf_injective {v v' : F} {r r' : E} {z z' : F} {w w' : E}
    (h : c.nf v r z w = c.nf v' r' z' w') : v = v' ∧ r = r' ∧ z = z' ∧ w = w' := by
  have := S.hyp.finite
  have hp : S.proj ⟨c.nf v r z w, c.nf_mem v r z w⟩ =
      S.proj ⟨c.nf v' r' z' w', c.nf_mem v' r' z' w'⟩ :=
    congrArg S.proj (Subtype.ext h)
  rw [c.proj_nf, c.proj_nf] at hp
  obtain ⟨-, rfl, rfl, rfl⟩ := c.vc_injective hp
  refine ⟨rfl, rfl, c.x4_injective ?_, rfl⟩
  rw [nf, nf, y, y] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem y_injective {v v' : F} {r r' : E} {z z' : F} (h : c.y v r z = c.y v' r' z') :
    v = v' ∧ r = r' ∧ z = z' := by
  rw [← c.nf_zero_right, ← c.nf_zero_right] at h
  obtain ⟨h1, h2, h3, -⟩ := c.nf_injective h
  exact ⟨h1, h2, h3⟩

theorem exists_comm15_eq (s w : E) :
    ∃ z, ⁅c.x1 s, c.x5 w⁆ = c.y (c.F2 s w) (c.F3 s w) z := by
  have hk := c.comm15_mem s w
  obtain ⟨a, ha, hg⟩ := S.exists_eq_mul ⟨_, hk.1⟩
  obtain ⟨z, rfl⟩ := c.x4_surjective ha
  refine ⟨z, ?_⟩
  obtain ⟨hk1, hk2⟩ := S.proj_K hk
  have hk1' : ((S.proj ⟨_, hk.1⟩).1 : G) = 1 := by rw [hk1]; rfl
  have hk2' : ((S.proj ⟨_, hk.1⟩).2.1 : G) = 1 := by rw [hk2]; rfl
  have hg' : ⁅c.x1 s, c.x5 w⁆ = c.x3 (c.F3 s w) * c.x2 (c.F2 s w) * c.x4 z := by
    rw [c.x3_F3, c.x2_F2]
    simpa only [hk1', hk2', one_mul] using hg
  rw [hg', y, (c.commute_x2_x3 _ _).eq]

@[expose] noncomputable def F4 (s w : E) : F := Classical.choose (c.exists_comm15_eq s w)

theorem comm15_eq (s w : E) : ⁅c.x1 s, c.x5 w⁆ = c.y (c.F2 s w) (c.F3 s w) (c.F4 s w) :=
  Classical.choose_spec (c.exists_comm15_eq s w)

theorem x1_conj_y (s : E) (v : F) (r : E) (z : F) :
    c.x1 s * c.y v r z * (c.x1 s)⁻¹ = c.y (v + c.T s r) r z := by
  obtain ⟨-, hU1P', hU1A, -⟩ := positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  have h2 : c.x1 s * c.x2 v * (c.x1 s)⁻¹ = c.x2 v := by
    rw [(hU1P' _ (c.x1_mem s) _ (c.x2_mem v)).eq, mul_inv_cancel_right]
  have h4 : c.x1 s * c.x4 z * (c.x1 s)⁻¹ = c.x4 z := by
    rw [(hU1A _ (c.x1_mem s) _ (c.x4_mem z)).eq, mul_inv_cancel_right]
  have h3 : c.x1 s * c.x3 r * (c.x1 s)⁻¹ = c.x2 (c.T s r) * c.x3 r := by
    rw [c.x2_T, commutatorElement_def]
    group
  rw [y, y, c.x2_add, show c.x1 s * (c.x2 v * c.x3 r * c.x4 z) * (c.x1 s)⁻¹ =
    (c.x1 s * c.x2 v * (c.x1 s)⁻¹) * (c.x1 s * c.x3 r * (c.x1 s)⁻¹) *
      (c.x1 s * c.x4 z * (c.x1 s)⁻¹) by group, h2, h3, h4]
  group

theorem x1_conj_x5 (s w : E) :
    c.x1 s * c.x5 w * (c.x1 s)⁻¹ = c.y (c.F2 s w) (c.F3 s w) (c.F4 s w) * c.x5 w := by
  rw [← c.comm15_eq, commutatorElement_def]
  group

theorem x1_conj_nf [CharP F 2] (s : E) (v : F) (r : E) (z : F) (w : E) :
    c.x1 s * c.nf v r z w * (c.x1 s)⁻¹ =
      c.nf (v + c.T s r + c.F2 s w) (r + c.F3 s w) (z + c.F4 s w) w := by
  rw [nf, nf, show c.x1 s * (c.y v r z * c.x5 w) * (c.x1 s)⁻¹ =
    (c.x1 s * c.y v r z * (c.x1 s)⁻¹) * (c.x1 s * c.x5 w * (c.x1 s)⁻¹) by group, c.x1_conj_y,
    c.x1_conj_x5, ← mul_assoc, c.y_mul]

theorem nb_conj_y [CharP F 2] (v : F) (r : E) (z : F) :
    c.nb * c.y v r z * c.nb⁻¹ = c.y z r v := by
  rw [y, y, show c.nb * (c.x2 v * c.x3 r * c.x4 z) * c.nb⁻¹ = (c.nb * c.x2 v * c.nb⁻¹) *
    (c.nb * c.x3 r * c.nb⁻¹) * (c.nb * c.x4 z * c.nb⁻¹) by group, c.nb_conj_x2, c.nb_conj_x3,
    c.nb_conj_x4, mul_assoc, (c.commute_x4 v (Subgroup.mul_mem _ (Setup.U3_le_M (c.x3_mem r))
      (S.P'_le_M (c.x2_mem z)))).eq, ← (c.commute_x2_x3 z r).eq]

theorem F4_F3 [CharP F 2] (hβ : ∀ s, c.beta s = s) (s w : E) :
    c.F4 s w = c.F2 w s ∧ c.F3 s w = c.F3 w s := by
  have hconj : ∀ g a b : G, g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := fun g a b => by
    simp only [commutatorElement_def]
    group
  have h : c.nb * ⁅c.x1 s, c.x5 w⁆ * c.nb⁻¹ =
      c.nb * c.y (c.F2 s w) (c.F3 s w) (c.F4 s w) * c.nb⁻¹ := by
    rw [c.comm15_eq]
  rw [hconj, c.nb_conj_x1 hβ, c.nb_conj_x5 hβ, c.nb_conj_y, ← commutatorElement_inv,
    c.comm15_eq, c.y_inv] at h
  obtain ⟨h1, h2, -⟩ := c.y_injective h
  exact ⟨h1.symm, h2.symm⟩

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
