module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515bBlk

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem val_a2 (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) :
    valence Γ (T.line.vert (a + 2)) = 3 := by
  simpa using v3 F C 0

theorem val_a3 (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) :
    valence Γ (T.line.vert (a + 3)) = 5 := by
  have := v5 F C 1
  rwa [show a + 1 + 2 * 1 = a + 3 by ring] at this

theorem adj_a12 (T : Track Γ G) (a : ℤ) :
    Γ.Adj (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
  have := T.line.adj (a + 1)
  rwa [show a + 1 + 1 = a + 2 by ring] at this

theorem adj_a23 (T : Track Γ G) (a : ℤ) :
    Γ.Adj (T.line.vert (a + 2)) (T.line.vert (a + 3)) := by
  have := T.line.adj (a + 2)
  rwa [show a + 2 + 1 = a + 3 by ring] at this

theorem mkBlk (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) {z' : G}
    (hz'3 : z' • T.line.vert (a + 3) = T.line.vert (a + 3))
    (hzb : z ∈ ballStab Γ G 2 (T.line.vert (a + 3))) :
    ∃ (αs α's : V) (d zz : G), d = Lb z (T.line.vert (a + 1)) (T.line.vert (a + 3)) ∧
      zz = z' * z * z'⁻¹ ∧
      Blk Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2)) (T.line.vert (a + 3))
        (z' • T.line.vert (a + 2)) (z' • T.line.vert (a + 1)) αs α's d zz := by
  set α := T.line.vert (a + 1) with hα
  set β := T.line.vert (a + 2) with hβ
  set δ := T.line.vert (a + 3) with hδ
  have hvα := C.val
  have hvβ := val_a2 F C
  have hvδ := val_a3 F C
  have hβα : Γ.Adj β α := (adj_a12 T a).symm
  have hβδ : Γ.Adj β δ := adj_a23 T a
  have hαδ : α ≠ δ := by
    have := T.line.nb (a + 1)
    rwa [show a + 1 + 2 = a + 3 by ring] at this
  have hvβ' : valence Γ (z' • β) = 3 := by rw [F.valence_smul_eq]; exact hvβ
  have hβ'δ : Γ.Adj (z' • β) δ := by
    have := (F.adj_smul z' β δ).2 hβδ
    rwa [hz'3] at this
  have hβ'α' : Γ.Adj (z' • β) (z' • α) := (F.adj_smul z' β α).2 hβα
  have hα'δ : z' • α ≠ δ := fun h => hαδ (MulAction.injective z' (h.trans hz'3.symm))
  obtain ⟨αs, hset1, hαsα, hαsδ⟩ := exists_third_neighbor hvβ hβα hβδ hαδ
  obtain ⟨α's, hset2, hα'sδ, hα'sα'⟩ := exists_third_neighbor hvβ' hβ'δ hβ'α' (Ne.symm hα'δ)
  have hβαs : Γ.Adj β αs := by
    have : αs ∈ Γ.neighborSet β := by rw [hset1]; simp
    exact this
  have hβ'α's : Γ.Adj (z' • β) α's := by
    have : α's ∈ Γ.neighborSet (z' • β) := by rw [hset2]; simp
    exact this
  have hδorb : ∃ g : G, g • α = δ := ⟨T.τ, by
    have := T.trans (a + 1)
    rwa [show a + 1 + 2 = a + 3 by ring] at this⟩
  set d := Lb z α δ with hd
  set zz := Lb z α (z' • α) with hzz
  have hdcin : d ∈ Cinv G δ := Lb_cinv C.cinv hδorb
  have hzzval : zz = z' * z * z'⁻¹ := by
    have h := Lb_conj C.cinv ⟨1, one_smul G α⟩ z'
    rw [Lb_self C.cinv] at h
    exact h.symm
  have hzδ : z ∈ MulAction.stabilizer G δ :=
    F.nbrStab_le_stabilizer δ ((F.mem_ballStab_two_iff).1 hzb).1
  have hz'δ : z' ∈ MulAction.stabilizer G δ := MulAction.mem_stabilizer_iff.2 hz'3
  have hzzb : zz ∈ ballStab Γ G 2 δ := by
    rw [hzzval]
    exact F.conj_mem_ballStab_two hz'δ hzb
  have hzzδ : zz ∈ MulAction.stabilizer G δ :=
    F.nbrStab_le_stabilizer δ ((F.mem_ballStab_two_iff).1 hzzb).1
  have c2 : z * d = d * z := hdcin.2.2.2 z hzδ
  have c3 : zz * d = d * zz := hdcin.2.2.2 zz hzzδ
  have hzα' : z • (z' • α) = z' • α :=
    mem_nbrStab.1 (((F.mem_ballStab_two_iff).1 hzb).2 (z' • β) hβ'δ.symm) (z' • α) hβ'α'
  have hα'orb : ∃ g : G, g • α = z' • α := ⟨z', rfl⟩
  have hα'cin : zz ∈ Cinv G (z' • α) := Lb_cinv C.cinv hα'orb
  have c1 : z * zz = zz * z := hα'cin.2.2.2 z (MulAction.mem_stabilizer_iff.2 hzα')
  have dd : d * d = 1 := Lb_mul_self C.cinv hδorb
  have zz2 : zz * zz = 1 := Lb_mul_self C.cinv hα'orb
  have z2 : z * z = 1 := C.cinv.2.1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right z2
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right dd
  have hzzinv : zz⁻¹ = zz := inv_eq_of_mul_eq_one_right zz2
  obtain ⟨hp1, -, -, -⟩ := three_labels F C.cinv C.val hvβ C.f2 hβα hβδ hβαs hαδ hαsα hαsδ
  obtain ⟨hp2, -, -, -⟩ := three_labels F C.cinv C.val hvβ' C.f2 hβ'δ hβ'α' hβ'α's
    (Ne.symm hα'δ) hα'sδ hα'sα'
  rw [Lb_self C.cinv] at hp1
  have hLαs : Lb z α αs = z * d := by
    rw [eq_inv_of_mul_eq_one_right hp1, mul_inv_rev, hdinv, hzinv]
    exact c2.symm
  have hLα's : Lb z α α's = zz * d := by
    rw [eq_inv_of_mul_eq_one_right hp2, mul_inv_rev, hzzinv, hdinv]
  exact ⟨αs, α's, d, zz, rfl, hzzval,
    { cinv := C.cinv
      orb' := hα'orb
      hset1 := hset1
      hset2 := hset2
      hαδ := hαδ
      hα'δ := hα'δ
      hzz := rfl
      Lαs := hLαs
      Lα's := hLα's
      c1 := c1
      c2 := c2
      c3 := c3
      dd := dd
      dcin := hdcin }⟩

end P515

end CFSG.Quasithin.Fan86
