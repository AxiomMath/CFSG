module

public import CFSG.Walter.Ree.Thompson2.BaseFin.HatCheck
public import CFSG.Walter.Ree.Thompson2.BaseFin.Pres
public import CFSG.Walter.Ree.Thompson2.BaseRel.Iso

public section

namespace CFSG.Walter.Ree.T2.BaseFin

open CFSG.Certificates.CosetEnumeration CFSG.Walter.J1Recog Word BaseRel

theorem card_presHat : Finite PresHat ∧ Nat.card PresHat ≤ 1512 := by
  have h := card_le_of_facts_presented (rels := relSet relsHat) (N := 1512) (F := 6048)
    (fx := HatData.fx) (fc := HatData.fc) (fy := HatData.fy) (kind := HatData.kind)
    (wi := HatData.wi) (fs := HatData.fs) (ft := HatData.ft) (fo := HatData.fo)
    (refs := HatData.refs) (pl := HatData.pl) (ffi := HatData.ffi)
    (live := HatData.live) relsHat HatData.words (fun _ hw => mk_mem_relSet hw)
    (by decide +kernel) HatData.live_zero (by norm_num) HatData.facts_all HatData.cover_all
  rw [HatData.liveCount_eq] at h
  exact h

instance : Finite PresHat := card_presHat.1

theorem card_presHat_le : Nat.card (PresentedGroup (relSet relsHat)) ≤ 1512 := card_presHat.2

@[expose] def pglC : Equiv.Perm (Fin 9) :=
  ⟨mobius 2 0 0 1, mobius 5 0 0 1, by decide, by decide⟩

@[expose] def pglW : Equiv.Perm (Fin 9) :=
  ⟨mobius 0 1 1 0, mobius 0 1 1 0, by decide, by decide⟩

theorem pglK_eq : pglK = pglC * pglJ * pglC⁻¹ := by decide

theorem pglY_eq : pglY = pglC * pglJ * pglC * pglT * pglW * pglJ * pglC * pglT⁻¹ := by decide

theorem pglC_eq : pglC = pglJ * pglT * pglY⁻¹ * pglK * pglT⁻¹ * pglK * pglY := by decide

theorem pglW_eq : pglW = pglJ * pglY⁻¹ * pglY⁻¹ * pglY⁻¹ := by decide

theorem pglJ_mem : pglJ ∈ PGammaL28 := Subgroup.subset_closure (by simp)

theorem pglK_mem : pglK ∈ PGammaL28 := Subgroup.subset_closure (by simp)

theorem pglT_mem : pglT ∈ PGammaL28 := Subgroup.subset_closure (by simp)

theorem pglY_mem : pglY ∈ PGammaL28 := Subgroup.subset_closure (by simp)

theorem pglC_mem : pglC ∈ PGammaL28 := by
  rw [pglC_eq]
  have hY := PGammaL28.inv_mem pglY_mem
  exact PGammaL28.mul_mem (PGammaL28.mul_mem (PGammaL28.mul_mem (PGammaL28.mul_mem
    (PGammaL28.mul_mem (PGammaL28.mul_mem pglJ_mem pglT_mem) hY) pglK_mem)
    (PGammaL28.inv_mem pglT_mem)) pglK_mem) pglY_mem

theorem pglW_mem : pglW ∈ PGammaL28 := by
  rw [pglW_eq]
  have hY := PGammaL28.inv_mem pglY_mem
  exact PGammaL28.mul_mem (PGammaL28.mul_mem (PGammaL28.mul_mem pglJ_mem hY) hY) hY

@[expose] def hatC : PGammaL28 := ⟨pglC, pglC_mem⟩

@[expose] def hatW : PGammaL28 := ⟨pglW, pglW_mem⟩

theorem k_eq : PGammaL28.k = hatC * PGammaL28.j * hatC⁻¹ := Subtype.ext pglK_eq

theorem y_eq : PGammaL28.y =
    hatC * PGammaL28.j * hatC * PGammaL28.t * hatW * PGammaL28.j * hatC * PGammaL28.t⁻¹ :=
  Subtype.ext pglY_eq

@[expose] def hatGen : Fin 4 → Equiv.Perm (Fin 9) := ![pglJ, pglC, pglT, pglW]

theorem hatGen_relsHat : ∀ w ∈ relsHat, ev hatGen w = 1 := by
  intro w hw
  rw [ev_eq_evList]
  revert w
  decide +kernel

theorem closure_hatGen : Subgroup.closure (Set.range hatGen) = PGammaL28 := by
  set S := Subgroup.closure (Set.range hatGen)
  have hJ : pglJ ∈ S := Subgroup.subset_closure ⟨0, rfl⟩
  have hC : pglC ∈ S := Subgroup.subset_closure ⟨1, rfl⟩
  have hT : pglT ∈ S := Subgroup.subset_closure ⟨2, rfl⟩
  have hW : pglW ∈ S := Subgroup.subset_closure ⟨3, rfl⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [pglJ_mem, pglC_mem, pglT_mem, pglW_mem]
  · rw [PGammaL28, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact hJ
    · rw [pglK_eq]
      exact S.mul_mem (S.mul_mem hC hJ) (S.inv_mem hC)
    · exact hT
    · rw [pglY_eq]
      exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem hC hJ)
        hC) hT) hW) hJ) hC) (S.inv_mem hT)

noncomputable def toPermHat : PresHat →* Equiv.Perm (Fin 9) :=
  lift relsHat hatGen hatGen_relsHat

theorem range_toPermHat : toPermHat.range = PGammaL28 := by
  rw [toPermHat, range_lift, closure_hatGen]

noncomputable def toPGLHat : PresHat →* PGammaL28 :=
  toPermHat.codRestrict PGammaL28 fun x => range_toPermHat ▸ ⟨x, rfl⟩

theorem toPGLHat_bijective : Function.Bijective toPGLHat := by
  have hsurj : Function.Surjective toPGLHat := by
    rintro ⟨g, hg⟩
    rw [← range_toPermHat] at hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨x, rfl⟩
  exact hsurj.bijective_of_nat_card_le (by rw [card_PGammaL28]; exact card_presHat_le)

noncomputable def isoHat : PresentedGroup (relSet relsHat) ≃* PGammaL28 :=
  MulEquiv.ofBijective toPGLHat toPGLHat_bijective

theorem isoHat_of (i : Fin 4) :
    ((isoHat (PresentedGroup.of i) : PGammaL28) : Equiv.Perm (Fin 9)) = hatGen i := by
  change toPermHat (PresentedGroup.of i) = hatGen i
  rw [toPermHat, lift_of]

theorem isoHat_symm_j : isoHat.symm PGammaL28.j = PresentedGroup.of 0 :=
  isoHat.symm_apply_eq.mpr (Subtype.ext (isoHat_of 0).symm)

theorem isoHat_symm_c : isoHat.symm hatC = PresentedGroup.of 1 :=
  isoHat.symm_apply_eq.mpr (Subtype.ext (isoHat_of 1).symm)

theorem isoHat_symm_t : isoHat.symm PGammaL28.t = PresentedGroup.of 2 :=
  isoHat.symm_apply_eq.mpr (Subtype.ext (isoHat_of 2).symm)

theorem isoHat_symm_w : isoHat.symm hatW = PresentedGroup.of 3 :=
  isoHat.symm_apply_eq.mpr (Subtype.ext (isoHat_of 3).symm)

section Lift

variable {H : Type*} [Group H]

structure HatRels (J' c' T' u' : H) : Prop where
  j_sq : J' ^ 2 = 1
  c_pow_seven : c' ^ 7 = 1
  t_pow_three : T' ^ 3 = 1
  j_t : J' * T' = T' * J'
  t_c : T'⁻¹ * c' * T' = c' ^ 2
  j_conj_one : J' * (c'⁻¹ * J' * c') = c'⁻¹ * J' * c' * J'
  j_conj_three : J' * ((c' ^ 3)⁻¹ * J' * c' ^ 3) = (c' ^ 3)⁻¹ * J' * c' ^ 3 * J'
  j_conj_five : J' * (c'⁻¹ * J' * c') * ((c' ^ 5)⁻¹ * J' * c' ^ 5) = 1
  u_sq : u' ^ 2 = 1
  u_t : u' * T' = T' * u'
  u_c : u' * c' * u' = c'⁻¹
  u_j : (u' * J') ^ 3 = 1

theorem mul_sq_eq_one {a b : H} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    (a * b) ^ 2 = 1 := by
  rw [(Commute.mul_pow hab 2), ha, hb, one_mul]

theorem HatRels.ev {J' c' T' u' : H} (h : HatRels J' c' T' u') :
    ∀ w ∈ relsHat, CFSG.Walter.J1Recog.ev ![J', c', T', u'] w = 1 := by
  have hJinv : J'⁻¹ = J' := inv_eq_of_mul_eq_one_right (by rw [← sq, h.j_sq])
  have huinv : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right (by rw [← sq, h.u_sq])
  have hconj : ∀ n : ℕ, ((c' ^ n)⁻¹ * J' * c' ^ n) ^ 2 = 1 := fun n => by
    rw [sq, show (c' ^ n)⁻¹ * J' * c' ^ n * ((c' ^ n)⁻¹ * J' * c' ^ n) =
      (c' ^ n)⁻¹ * (J' * J') * c' ^ n by group, ← sq, h.j_sq, mul_one, inv_mul_cancel]
  intro w hw
  simp only [relsHat, relsB, relsW, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [ev_pow, ev_append, ev_gen, ev_inv, wj, wc, wt, ww, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  · exact h.j_sq
  · exact h.c_pow_seven
  · exact h.t_pow_three
  · rw [h.j_t]; group
  · rw [h.t_c, inv_pow, mul_inv_cancel]
  · have := mul_sq_eq_one h.j_sq (by simpa using hconj 1) (by simpa using h.j_conj_one)
    simpa [mul_assoc] using this
  · have := mul_sq_eq_one h.j_sq (hconj 3) h.j_conj_three
    simpa [mul_assoc, inv_pow] using this
  · have := h.j_conj_five
    simpa [mul_assoc, inv_pow] using this
  · exact h.u_sq
  · rw [h.u_t]; group
  · rw [sq, ← mul_assoc, h.u_c, inv_mul_cancel]
  · exact h.u_j

noncomputable def liftHat {J' c' T' u' : H} (h : HatRels J' c' T' u') : PGammaL28 →* H :=
  (lift relsHat ![J', c', T', u'] h.ev).comp isoHat.symm.toMonoidHom

variable {J' c' T' u' : H} (h : HatRels J' c' T' u')

theorem liftHat_j : liftHat h PGammaL28.j = J' := by
  simp only [liftHat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, isoHat_symm_j, lift_of]
  rfl

theorem liftHat_c : liftHat h hatC = c' := by
  simp only [liftHat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, isoHat_symm_c, lift_of]
  rfl

theorem liftHat_t : liftHat h PGammaL28.t = T' := by
  simp only [liftHat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, isoHat_symm_t, lift_of]
  rfl

theorem liftHat_w : liftHat h hatW = u' := by
  simp only [liftHat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, isoHat_symm_w, lift_of]
  rfl

theorem liftHat_k : liftHat h PGammaL28.k = c' * J' * c'⁻¹ := by
  rw [k_eq, map_mul, map_mul, map_inv, liftHat_c, liftHat_j]

theorem liftHat_y : liftHat h PGammaL28.y = c' * J' * c' * T' * u' * J' * c' * T'⁻¹ := by
  simp only [y_eq, map_mul, map_inv, liftHat_c, liftHat_j, liftHat_t, liftHat_w]

theorem range_liftHat : (liftHat h).range = Subgroup.closure {J', c', T', u'} := by
  have htop : isoHat.symm.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr isoHat.symm.surjective
  rw [liftHat, MonoidHom.range_comp, htop, ← MonoidHom.range_eq_map, range_lift]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem liftHat_injective (hJ : J' ≠ 1) : Function.Injective (liftHat h) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra ha1
  have hj := j_mem_of_normal (MonoidHom.normal_ker (liftHat h)) (MonoidHom.mem_ker.mpr ha) ha1
  rw [MonoidHom.mem_ker, liftHat_j] at hj
  exact hJ hj

end Lift

end CFSG.Walter.Ree.T2.BaseFin
