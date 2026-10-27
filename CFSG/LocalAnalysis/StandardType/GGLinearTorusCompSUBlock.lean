module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUFrame
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.SeitzReduction.LinearPilot
open scoped commutatorElement

namespace SUTorus

variable {K : Type} [Field K] {f n : ℕ} {G : Type*} [Group G]

abbrev conjN {D : GL (Fin n) K}
    (hD : D ∈ Subgroup.normalizer ((unitarySU 2 f K n : Set (GL (Fin n) K)))) :
    ↥(unitarySU 2 f K n) →* ↥(unitarySU 2 f K n) :=
  ((unitarySU 2 f K n).normalizerMonoidHom ⟨D, hD⟩).toMonoidHom

theorem coe_conjN {D : GL (Fin n) K}
    (hD : D ∈ Subgroup.normalizer ((unitarySU 2 f K n : Set (GL (Fin n) K))))
    (u : ↥(unitarySU 2 f K n)) : ((conjN hD u : ↥(unitarySU 2 f K n)) : GL (Fin n) K) =
      D * u * D⁻¹ :=
  rfl

theorem map_conjN {ψ : ↥(unitarySU 2 f K n) →* G} {e : G} {D : GL (Fin n) K}
    (hD : (e, D) ∈ suPairs ψ) (u : ↥(unitarySU 2 f K n)) :
    ψ (conjN hD.1 u) = e * ψ u * e⁻¹ :=
  (hD.2 u _ rfl).symm

omit [Field K] in
theorem isBlockOn_iff [Field K] {I : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K} :
    TableBUE.IsBlockOn I M ↔ M * blockComplProj I = blockComplProj I ∧
      blockComplProj I * M = blockComplProj I :=
  agrees_one_iff I M

theorem isBlockOn_conj {I : Finset (Fin n)} {Z W U : Matrix (Fin n) (Fin n) K}
    (hZ : Z * blockComplProj I = blockComplProj I * Z) (hZW : Z * W = 1) (hWZ : W * Z = 1)
    (hU : TableBUE.IsBlockOn I U) : TableBUE.IsBlockOn I (Z * U * W) := by
  rw [isBlockOn_iff] at hU ⊢
  have hW : W * blockComplProj I = blockComplProj I * W := by
    calc W * blockComplProj I = W * blockComplProj I * (Z * W) := by rw [hZW, Matrix.mul_one]
      _ = W * (Z * blockComplProj I) * W := by rw [hZ]; simp only [Matrix.mul_assoc]
      _ = blockComplProj I * W := by rw [← Matrix.mul_assoc, hWZ, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · calc Z * U * W * blockComplProj I = Z * (U * (W * blockComplProj I)) := by
          simp only [Matrix.mul_assoc]
      _ = Z * ((U * blockComplProj I) * W) := by rw [hW, ← Matrix.mul_assoc U]
      _ = blockComplProj I * (Z * W) := by
          rw [hU.1, ← Matrix.mul_assoc, hZ, Matrix.mul_assoc]
      _ = blockComplProj I := by rw [hZW, Matrix.mul_one]
  · calc blockComplProj I * (Z * U * W) = ((blockComplProj I * Z) * U) * W := by
          simp only [Matrix.mul_assoc]
      _ = Z * (blockComplProj I * U) * W := by rw [← hZ, Matrix.mul_assoc Z]
      _ = Z * (blockComplProj I * W) := by rw [hU.2, Matrix.mul_assoc]
      _ = Z * W * blockComplProj I := by rw [← hW, Matrix.mul_assoc]
      _ = blockComplProj I := by rw [hZW, Matrix.one_mul]

theorem blockSU_univ : TableBUE.blockSU (K := K) (n := f) (Finset.univ : Finset (Fin n)) = ⊤ :=
  eq_top_iff.mpr fun _ _ i j hij => by simp at hij

theorem blockSU_mono {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    TableBUE.blockSU (K := K) (n := f) I ≤ TableBUE.blockSU J :=
  fun _ hx i j hij => hx i j (hij.imp (fun hi hiI => hi (hIJ hiI)) (fun hj hjI => hj (hIJ hjI)))

theorem blockSU_singleton (h : UnitaryFieldData 2 f K) (i : Fin n) :
    TableBUE.blockSU (K := K) (n := f) ({i} : Finset (Fin n)) = ⊥ := by
  refine eq_bot_iff.mpr fun u hu => ?_
  have hout : ∀ a b, (a ≠ i ∨ b ≠ i) → ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      (1 : Matrix (Fin n) (Fin n) K) a b := fun a b hab =>
    hu a b (by simpa only [Finset.mem_singleton] using hab)
  have hdet := ((mem_unitarySU_iff h).mp u.2).1
  have hoff : ∀ a b, a ≠ b → ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b = 0 := by
    intro a b hab
    rw [hout a b (by by_contra h'; push Not at h'; exact hab (h'.1.trans h'.2.symm)),
      one_apply_ne hab]
  rw [TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero hoff, det_diagonal,
    Finset.prod_eq_single i (fun k _ hk => by rw [hout k k (Or.inl hk), one_apply_eq])
      (fun h' => absurd (Finset.mem_univ i) h')] at hdet
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  ext a b
  simp only [OneMemClass.coe_one, Units.val_one]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = i
    · subst ha
      rw [hdet, one_apply_eq]
    · exact hout a a (Or.inl ha)
  · rw [hoff a b hab, one_apply_ne hab]

theorem mul_comm_of_offDiag_eq_zero {z w : ↥(unitarySU 2 f K n)}
    (hz : ∀ a b, a ≠ b → ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b = 0)
    (hw : ∀ a b, a ≠ b → ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b = 0) :
    z * w = w * z := by
  have e1 := TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero hz
  have e2 := TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero hw
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, e1, e2,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

section Classes

variable {m : ℕ}

variable (f) in
@[expose] def diagCentU (S : Set G) (δ : G → Fin (m + 1) → Kˣ) :
    Subgroup ↥(unitarySU 2 f K (m + 1)) where
  carrier := {z | ∀ e ∈ S, Commute (diagHom (m + 1) (δ e)) (z : GL (Fin (m + 1)) K)}
  one_mem' := fun _ _ => Commute.one_right _
  mul_mem' := fun ha hb e he => (ha e he).mul_right (hb e he)
  inv_mem' := fun ha e he => (ha e he).inv_right

omit [Group G] in
theorem mem_diagCentU {S : Set G} {δ : G → Fin (m + 1) → Kˣ}
    {z : ↥(unitarySU 2 f K (m + 1))} :
    z ∈ diagCentU f S δ ↔ ∀ e ∈ S, Commute (diagHom (m + 1) (δ e)) (z : GL (Fin (m + 1)) K) :=
  Iff.rfl

omit [Group G] in
theorem eq_of_mem_diagCentU {S : Set G} {δ : G → Fin (m + 1) → Kˣ}
    {z : ↥(unitarySU 2 f K (m + 1))} (hz : z ∈ diagCentU f S δ) {i j : Fin (m + 1)}
    (hij : ((z : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j ≠ 0) {e : G}
    (he : e ∈ S) : δ e i = δ e j := by
  by_contra hne
  exact hij (TableBUE.entry_eq_zero_of_commute (hz e he).eq.symm hne)

omit [Group G] in
theorem blockSU_le_diagCentU (S : Set G) (δ : G → Fin (m + 1) → Kˣ) (i : Fin (m + 1)) :
    TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i) ≤ diagCentU f S δ :=
  fun _ hu _ he => TableBUE.diagHom_mul_comm_of_isBlockOn
    (fun _ hj _ hk => LinTorus.eq_of_mem_diagClass hj hk he) hu

omit [Group G] in
theorem blockComplProj_mul_eq_of_mem_diagCentU {S : Set G} {δ : G → Fin (m + 1) → Kˣ}
    {z : ↥(unitarySU 2 f K (m + 1))} (hz : z ∈ diagCentU f S δ) (i : Fin (m + 1)) :
    blockComplProj (LinTorus.diagClass S δ i) *
        ((z : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      ((z : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        blockComplProj (LinTorus.diagClass S δ i) := by
  ext a b
  rw [blockComplProj, diagonal_mul, mul_diagonal]
  by_cases hab : ((z : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a b = 0
  · rw [hab, mul_zero, zero_mul]
  · have hiff : a ∈ LinTorus.diagClass S δ i ↔ b ∈ LinTorus.diagClass S δ i := by
      rw [LinTorus.mem_diagClass, LinTorus.mem_diagClass]
      constructor
      · intro ha e he
        rw [← eq_of_mem_diagCentU hz hab he]
        exact ha e he
      · intro hb e he
        rw [eq_of_mem_diagCentU hz hab he]
        exact hb e he
    by_cases ha : a ∈ LinTorus.diagClass S δ i
    · rw [ite_eq_left ha, ite_eq_left (hiff.mp ha), zero_mul, mul_zero]
    · rw [ite_eq_right ha, ite_eq_right fun hb => ha (hiff.mpr hb), one_mul, mul_one]

omit [Group G] in
theorem conj_mem_blockSU_of_mem_diagCentU {S : Set G} {δ : G → Fin (m + 1) → Kˣ}
    {i : Fin (m + 1)} {z u : ↥(unitarySU 2 f K (m + 1))} (hz : z ∈ diagCentU f S δ)
    (hu : u ∈ TableBUE.blockSU (LinTorus.diagClass S δ i)) :
    z * u * z⁻¹ ∈ TableBUE.blockSU (LinTorus.diagClass S δ i) := by
  rw [TableBUE.mem_blockSU, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
    Units.val_mul]
  exact isBlockOn_conj (blockComplProj_mul_eq_of_mem_diagCentU hz i).symm
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hu

section Psi

variable {ψ : ↥(unitarySU 2 f K (m + 1)) →* G} {S : Set G} {δ : G → Fin (m + 1) → Kˣ}

theorem mem_centralizer_map_blockSU {e : G} {d : Fin (m + 1) → Kˣ}
    (he : (e, diagHom (m + 1) d) ∈ suPairs ψ) {I : Finset (Fin (m + 1))}
    (hd : ∀ i ∈ I, ∀ j ∈ I, d i = d j) :
    e ∈ Subgroup.centralizer
      (((TableBUE.blockSU (K := K) (n := f) I).map ψ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have h1 := he.2 u u (by rw [TableBUE.diagHom_mul_comm_of_isBlockOn hd hu, mul_inv_cancel_right])
  calc ψ u * e = e * ψ u * e⁻¹ * e := by rw [h1]
    _ = e * ψ u := by group

theorem map_diagCentU_le (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) :
    (diagCentU f S δ).map ψ ≤ ψ.range ⊓ Subgroup.centralizer S := by
  rintro _ ⟨z, hz, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
  have h := (hδ e he).2 z z (by rw [(hz e he).eq, mul_inv_cancel_right])
  calc e * ψ z = e * ψ z * e⁻¹ * e := by group
    _ = ψ z * e := by rw [h]

theorem conjN_mul_inv_mem_center (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    {e : G} {D : GL (Fin (m + 1)) K} (hD : (e, D) ∈ suPairs ψ) {w : ↥(unitarySU 2 f K (m + 1))}
    (hw : ψ w ∈ Subgroup.centralizer S) (he : e ∈ S) :
    conjN hD.1 w * w⁻¹ ∈ Subgroup.center ↥(unitarySU 2 f K (m + 1)) := by
  apply hker
  have hc : e * ψ w = ψ w * e := Subgroup.mem_centralizer_iff.mp hw e he
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_conjN hD, hc, mul_inv_cancel_right, mul_inv_cancel]

theorem commute_of_conjN_eq {D : GL (Fin (m + 1)) K}
    {hD : D ∈ Subgroup.normalizer ((unitarySU 2 f K (m + 1) : Set (GL (Fin (m + 1)) K)))}
    {x : ↥(unitarySU 2 f K (m + 1))} (hx : conjN hD x = x) :
    Commute D (x : GL (Fin (m + 1)) K) := by
  have h2 := congrArg Subtype.val hx
  rw [coe_conjN] at h2
  show D * (x : GL (Fin (m + 1)) K) = x * D
  calc D * (x : GL (Fin (m + 1)) K) = D * x * D⁻¹ * D := by group
    _ = x * D := by rw [h2]

theorem conj_mem_diagCentU (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) {w : ↥(unitarySU 2 f K (m + 1))}
    (hw : ψ w ∈ Subgroup.centralizer S) {z : ↥(unitarySU 2 f K (m + 1))}
    (hz : z ∈ diagCentU f S δ) : w * z * w⁻¹ ∈ diagCentU f S δ := by
  intro e he
  have hD := hδ e he
  set c := conjN hD.1 w * w⁻¹ with hc
  have hcz := conjN_mul_inv_mem_center hker hD hw he
  have hw' : conjN hD.1 w = c * w := by rw [hc, inv_mul_cancel_right]
  have hzD : conjN hD.1 z = z := Subtype.ext (by rw [coe_conjN, (hz e he).eq, mul_inv_cancel_right])
  refine commute_of_conjN_eq (hD := hD.1) ?_
  rw [map_mul, map_mul, map_inv, hw', hzD]
  have h1 : (w * z * w⁻¹) * c = c * (w * z * w⁻¹) := Subgroup.mem_center_iff.mp hcz _
  calc c * w * z * (c * w)⁻¹ = c * (w * z * w⁻¹) * c⁻¹ := by group
    _ = w * z * w⁻¹ := by rw [← h1]; group

theorem isSubnormal_map_diagCentU (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) :
    IsSubnormal ((diagCentU f S δ).map ψ) (ψ.range ⊓ Subgroup.centralizer S) := by
  refine IsSubnormal.step (map_diagCentU_le hδ) ⟨fun x hx y => ?_⟩ (IsSubnormal.refl _)
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨⟨w, hw⟩, hyC⟩ := Subgroup.mem_inf.mp y.2
  refine ⟨w * z * w⁻¹, conj_mem_diagCentU hker hδ (by rw [hw]; exact hyC) hz, ?_⟩
  simp only [map_mul, map_inv, hw, hzx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSubnormal_map_blockSU (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) (i : Fin (m + 1)) :
    IsSubnormal ((TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ)
      (ψ.range ⊓ Subgroup.centralizer S) := by
  refine IsSubnormal.step (Subgroup.map_mono (blockSU_le_diagCentU S δ i))
    ⟨fun x hx y => ?_⟩ (isSubnormal_map_diagCentU hker hδ)
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨z, hz, hzy⟩ := y.2
  refine ⟨z * u * z⁻¹, conj_mem_blockSU_of_mem_diagCentU hz hu, ?_⟩
  simp only [map_mul, map_inv, hzy, hux, Subgroup.coe_mul, Subgroup.coe_inv]

theorem commutator_comap_centralizer_le
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) :
    ⁅(Subgroup.centralizer S).comap ψ, (Subgroup.centralizer S).comap ψ⁆ ≤ diagCentU f S δ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy e he
  have hD := hδ e he
  have key : ∀ w : ↥(unitarySU 2 f K (m + 1)), ψ w ∈ Subgroup.centralizer S →
      ∃ c ∈ Subgroup.center ↥(unitarySU 2 f K (m + 1)), conjN hD.1 w = c * w :=
    fun w hw => ⟨_, conjN_mul_inv_mem_center hker hD hw he, by group⟩
  obtain ⟨c, hc, hcx⟩ := key x hx
  obtain ⟨c', hc', hcy⟩ := key y hy
  refine commute_of_conjN_eq (hD := hD.1) ?_
  rw [map_commutatorElement, hcx, hcy, LinTorus.commutatorElement_mul_left_of_mem_center hc,
    LinTorus.commutatorElement_mul_right_of_mem_center hc']

theorem le_map_diagCentU (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) {J : Subgroup G}
    (hJY : J ≤ ψ.range ⊓ Subgroup.centralizer S) (hJJ : ⁅J, J⁆ = J) :
    J ≤ (diagCentU f S δ).map ψ := by
  have hJr : J ≤ ψ.range := hJY.trans inf_le_left
  have hJC : J.comap ψ ≤ (Subgroup.centralizer S).comap ψ :=
    Subgroup.comap_mono (hJY.trans inf_le_right)
  calc J = ⁅J, J⁆ := hJJ.symm
    _ = ⁅(J.comap ψ).map ψ, (J.comap ψ).map ψ⁆ := by rw [Subgroup.map_comap_eq_self hJr]
    _ = (⁅J.comap ψ, J.comap ψ⁆).map ψ := (Subgroup.map_commutator _ _ _).symm
    _ ≤ (diagCentU f S δ).map ψ := Subgroup.map_mono
      ((Subgroup.commutator_mono hJC hJC).trans (commutator_comap_centralizer_le hker hδ))

end Psi

end Classes

end SUTorus

end CFSG.StandardType
