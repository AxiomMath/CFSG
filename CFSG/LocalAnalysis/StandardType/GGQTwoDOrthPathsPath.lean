module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsMoves

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus

variable {p r : ℕ}

private theorem plh_exists_other {x : OmPlusIdx r} {b : Fin r} (hb : b ∈ omSupp x) :
    ∃ a, a ≠ b ∧ omSupp x = {a, b} := by
  simp only [omSupp, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact ⟨x.1.1.2, (ne_of_lt x.1.2).symm, by rw [Finset.pair_comm]; rfl⟩
  · exact ⟨x.1.1.1, ne_of_lt x.1.2, rfl⟩

private theorem plh_injective_vec3 {β : Type*} {p q s : β} (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) : Function.Injective ![p, q, s] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> tauto

private theorem plh_injective_vec4 {β : Type*} {p q s t : β} (hpq : p ≠ q) (hps : p ≠ s)
    (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) :
    Function.Injective ![p, q, s, t] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> tauto

theorem exists_coords_chain {x y z : OmPlusIdx r} (hxz : Disjoint (omSupp x) (omSupp z))
    (hxy : ¬ Disjoint (omSupp x) (omSupp y)) (hyz : ¬ Disjoint (omSupp y) (omSupp z)) :
    ∃ a b c d : Fin r, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      omSupp x = {a, b} ∧ omSupp y = {b, c} ∧ omSupp z = {c, d} := by
  obtain ⟨b, hbx, hby⟩ := Finset.not_disjoint_iff.mp hxy
  obtain ⟨a, hab, hxab⟩ := plh_exists_other hbx
  obtain ⟨c, hcb, hycb⟩ := plh_exists_other hby
  have hybc : omSupp y = {b, c} := by rw [hycb, Finset.pair_comm]
  obtain ⟨e, hey, hez⟩ := Finset.not_disjoint_iff.mp hyz
  have heb : e ≠ b := fun h => (Finset.disjoint_left.mp hxz hbx) (h ▸ hez)
  have hec : e = c := by
    rw [hybc, Finset.mem_insert, Finset.mem_singleton] at hey
    rcases hey with h | h
    · exact absurd h heb
    · exact h
  have hcz : c ∈ omSupp z := by rw [← hec]; exact hez
  obtain ⟨d, hdc, hzdc⟩ := plh_exists_other hcz
  have hzcd : omSupp z = {c, d} := by rw [hzdc, Finset.pair_comm]
  have hac : a ≠ c := by
    intro h
    have hax : a ∈ omSupp x := by rw [hxab]; simp
    have haz : a ∈ omSupp z := by rw [h]; exact hcz
    exact (Finset.disjoint_left.mp hxz hax) haz
  have had : a ≠ d := by
    intro h
    have hax : a ∈ omSupp x := by rw [hxab]; simp
    have hdz : d ∈ omSupp z := by rw [hzcd]; simp
    have haz : a ∈ omSupp z := by rw [h]; exact hdz
    exact (Finset.disjoint_left.mp hxz hax) haz
  have hbd : b ≠ d := by
    intro h
    have hdz : d ∈ omSupp z := by rw [hzcd]; simp
    have hbz : b ∈ omSupp z := by rw [h]; exact hdz
    exact (Finset.disjoint_left.mp hxz hbx) hbz
  exact ⟨a, b, c, d, hab, hac, had, fun h => hcb h.symm, hbd, fun h => hdc h.symm,
    hxab, hybc, hzcd⟩

theorem exists_coords_fork {x y z : OmPlusIdx r} (hxz : omSupp x = omSupp z)
    (hxy : omSupp x ≠ omSupp y) (hnd : ¬ Disjoint (omSupp x) (omSupp y)) :
    ∃ a b c : Fin r, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ omSupp x = {a, b} ∧ omSupp z = {a, b} ∧
      omSupp y = {b, c} := by
  obtain ⟨b, hbx, hby⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨a, hab, hxab⟩ := plh_exists_other hbx
  obtain ⟨c, hcb, hycb⟩ := plh_exists_other hby
  have hybc : omSupp y = {b, c} := by rw [hycb, Finset.pair_comm]
  have hac : a ≠ c := by
    intro h
    apply hxy
    rw [hxab, hybc, h, Finset.pair_comm]
  exact ⟨a, b, c, hab, fun h => hcb h.symm, hac, hxab, hxz ▸ hxab, hybc⟩

private theorem plh_togIf_sign_mem {p : ℕ} {b : Bool} {i : Fin r} {q : OmPlusIdx r}
    (h : i ∈ omSupp q) : ((OmMove.togIf (p := p) b i).f q).2 = Bool.xor q.2 b := by
  rw [OmMove.togIf_f_sign]
  simp [h]

private theorem plh_togIf_sign_not_mem {p : ℕ} {b : Bool} {i : Fin r} {q : OmPlusIdx r}
    (h : i ∉ omSupp q) : ((OmMove.togIf (p := p) b i).f q).2 = q.2 := by
  rw [OmMove.togIf_f_sign]
  simp [h]

theorem omMove_chain (hr : 4 ≤ r) {x y z : OmPlusIdx r}
    (hxz : Disjoint (omSupp x) (omSupp z)) (hxy : ¬ Disjoint (omSupp x) (omSupp y))
    (hyz : ¬ Disjoint (omSupp y) (omSupp z)) :
    ∃ m : OmMove p r, m.f x = omStd r (by omega) ⟨0, by omega⟩ ∧
      m.f y = omStd r (by omega) ⟨1, by omega⟩ ∧ m.f z = omStd r (by omega) ⟨2, by omega⟩ := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hxab, hybc, hzcd⟩ :=
    exists_coords_chain hxz hxy hyz
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  let i2 : Fin r := ⟨2, by omega⟩
  let i3 : Fin r := ⟨3, by omega⟩
  have hf : Function.Injective ![a, b, c, d] := plh_injective_vec4 hab hac had hbc hbd hcd
  have hg : Function.Injective ![i0, i1, i2, i3] :=
    plh_injective_vec4 (by simp [i0, i1, Fin.ext_iff]) (by simp [i0, i2, Fin.ext_iff])
      (by simp [i0, i3, Fin.ext_iff]) (by simp [i1, i2, Fin.ext_iff])
      (by simp [i1, i3, Fin.ext_iff]) (by simp [i2, i3, Fin.ext_iff])
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (α := Fin 4) (β := Fin r)
    ![a, b, c, d] ![i0, i1, i2, i3] hf hg
  have hσa : σ a = i0 := by simpa using hσ 0
  have hσb : σ b = i1 := by simpa using hσ 1
  have hσc : σ c = i2 := by simpa using hσ 2
  have hσd : σ d = i3 := by simpa using hσ 3
  have hx1 : omSupp (omPerm σ x) = {i0, i1} := by
    rw [omSupp_omPerm, hxab]; simp [hσa, hσb]
  have hy1 : omSupp (omPerm σ y) = {i1, i2} := by
    rw [omSupp_omPerm, hybc]; simp [hσb, hσc]
  have hz1 : omSupp (omPerm σ z) = {i2, i3} := by
    rw [omSupp_omPerm, hzcd]; simp [hσc, hσd]
  have hlt0 : i0.val + 1 < r := by simp only [i0, Fin.val_mk]; omega
  have hlt1 : i1.val + 1 < r := by simp only [i1, Fin.val_mk]; omega
  have hlt2 : i2.val + 1 < r := by simp only [i2, Fin.val_mk]; omega
  have hstd0 : omSupp (omStd r (by omega) i0) = {i0, i1} :=
    (omSupp_omStd_chain (hr := by omega) (k := i0) (h := hlt0)).trans
      (by simp [i0, i1, Fin.ext_iff])
  have hstd0s : (omStd r (by omega) i0).2 = false :=
    omStd_sign_chain (hr := by omega) (k := i0) (h := hlt0)
  have hstd1 : omSupp (omStd r (by omega) i1) = {i1, i2} :=
    (omSupp_omStd_chain (hr := by omega) (k := i1) (h := hlt1)).trans
      (by simp [i1, i2, Fin.ext_iff])
  have hstd1s : (omStd r (by omega) i1).2 = false :=
    omStd_sign_chain (hr := by omega) (k := i1) (h := hlt1)
  have hstd2 : omSupp (omStd r (by omega) i2) = {i2, i3} :=
    (omSupp_omStd_chain (hr := by omega) (k := i2) (h := hlt2)).trans
      (by simp [i2, i3, Fin.ext_iff])
  have hstd2s : (omStd r (by omega) i2).2 = false :=
    omStd_sign_chain (hr := by omega) (k := i2) (h := hlt2)
  refine ⟨(OmMove.togIf y.2 i0).comp ((OmMove.togIf y.2 i1).comp
      ((OmMove.togIf z.2 i3).comp ((OmMove.togIf x.2 i0).comp (OmMove.perm σ)))), ?_, ?_, ?_⟩
  · apply omPlusIdx_ext
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, hx1]
      exact hstd0.symm
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        plh_togIf_sign_mem (h := by
          rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hx1]
          simp),
        plh_togIf_sign_mem (h := by
          rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hx1]; simp),
        plh_togIf_sign_not_mem (h := by
          rw [OmMove.omSupp_togIf_f, hx1]; simp [i0, i1, i3, Fin.ext_iff]),
        plh_togIf_sign_mem (h := by rw [hx1]; simp),
        omPerm_sign σ x]
      rw [show (omStd r (by omega) ⟨0, by omega⟩).2 = false from hstd0s]
      simp [Bool.xor_self, Bool.false_xor, Bool.xor_false]
  · apply omPlusIdx_ext
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, hy1]
      exact hstd1.symm
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        plh_togIf_sign_not_mem (h := by
          rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hy1]
          simp [i0, i1, i2, Fin.ext_iff]),
        plh_togIf_sign_mem (h := by
          rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hy1]; simp),
        plh_togIf_sign_not_mem (h := by
          rw [OmMove.omSupp_togIf_f, hy1]; simp [i1, i2, i3, Fin.ext_iff]),
        plh_togIf_sign_not_mem (h := by rw [hy1]; simp [i0, i1, i2, Fin.ext_iff]),
        omPerm_sign σ y]
      rw [show (omStd r (by omega) ⟨1, by omega⟩).2 = false from hstd1s]
      simp [Bool.xor_self, Bool.false_xor, Bool.xor_false]
  · apply omPlusIdx_ext
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, hz1]
      exact hstd2.symm
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        plh_togIf_sign_not_mem (h := by
          rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hz1]
          simp [i0, i2, i3, Fin.ext_iff]),
        plh_togIf_sign_not_mem (h := by
          rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hz1]; simp [i1, i2, i3, Fin.ext_iff]),
        plh_togIf_sign_mem (h := by
          rw [OmMove.omSupp_togIf_f, hz1]; simp),
        plh_togIf_sign_not_mem (h := by rw [hz1]; simp [i0, i2, i3, Fin.ext_iff]),
        omPerm_sign σ z]
      rw [show (omStd r (by omega) ⟨2, by omega⟩).2 = false from hstd2s]
      simp [Bool.xor_self, Bool.false_xor, Bool.xor_false]

theorem omMove_fork (hr : 4 ≤ r) {x y z : OmPlusIdx r} (hxz : omSupp x = omSupp z) (hne : x ≠ z)
    (hxy : omSupp x ≠ omSupp y) (hnd : ¬ Disjoint (omSupp x) (omSupp y)) :
    ∃ m : OmMove p r, m.f x = omStd r (by omega) ⟨r - 2, by omega⟩ ∧
      m.f y = omStd r (by omega) ⟨r - 3, by omega⟩ ∧
      m.f z = omStd r (by omega) ⟨r - 1, by omega⟩ := by
  obtain ⟨a, b, c, hab, hbc, hac, hxab, hzab, hybc⟩ := exists_coords_fork hxz hxy hnd
  let j1 : Fin r := ⟨r - 1, by omega⟩
  let j2 : Fin r := ⟨r - 2, by omega⟩
  let j3 : Fin r := ⟨r - 3, by omega⟩
  have hf : Function.Injective ![c, b, a] :=
    plh_injective_vec3 (fun h => hbc h.symm) (fun h => hac h.symm) (fun h => hab h.symm)
  have hj32 : j3 ≠ j2 := by
    intro h
    have h' : j3.val = j2.val := congrArg Fin.val h
    simp only [j3, j2, Fin.val_mk] at h'
    omega
  have hj31 : j3 ≠ j1 := by
    intro h
    have h' : j3.val = j1.val := congrArg Fin.val h
    simp only [j3, j1, Fin.val_mk] at h'
    omega
  have hj21 : j2 ≠ j1 := by
    intro h
    have h' : j2.val = j1.val := congrArg Fin.val h
    simp only [j2, j1, Fin.val_mk] at h'
    omega
  have hg : Function.Injective ![j3, j2, j1] := plh_injective_vec3 hj32 hj31 hj21
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (α := Fin 3) (β := Fin r)
    ![c, b, a] ![j3, j2, j1] hf hg
  have hσc : σ c = j3 := by simpa using hσ 0
  have hσb : σ b = j2 := by simpa using hσ 1
  have hσa : σ a = j1 := by simpa using hσ 2
  have hx1 : omSupp (omPerm σ x) = {j1, j2} := by
    rw [omSupp_omPerm, hxab]; simp [hσa, hσb]
  have hz1 : omSupp (omPerm σ z) = {j1, j2} := by
    rw [omSupp_omPerm, hzab]; simp [hσa, hσb]
  have hy1 : omSupp (omPerm σ y) = {j2, j3} := by
    rw [omSupp_omPerm, hybc]; simp [hσb, hσc]
  have hsu : x.2 ≠ z.2 := by
    intro h
    exact hne (omPlusIdx_ext hxz h)
  have hltj1 : ¬ j1.val + 1 < r := by simp only [j1, Fin.val_mk]; omega
  have hltj2 : j2.val + 1 < r := by simp only [j2, Fin.val_mk]; omega
  have hltj3 : j3.val + 1 < r := by simp only [j3, Fin.val_mk]; omega
  have hstdj2 : omSupp (omStd r (by omega) j2) = {j1, j2} := by
    rw [omSupp_omStd_chain (hr := by omega) (k := j2) (h := hltj2)]
    rw [show (⟨j2.val + 1, hltj2⟩ : Fin r) = j1 from
      Fin.ext (by simp only [j2, j1, Fin.val_mk]; omega)]
    exact Finset.pair_comm _ _
  have hstdj2s : (omStd r (by omega) j2).2 = false :=
    omStd_sign_chain (hr := by omega) (k := j2) (h := hltj2)
  have hstdj3 : omSupp (omStd r (by omega) j3) = {j2, j3} := by
    rw [omSupp_omStd_chain (hr := by omega) (k := j3) (h := hltj3)]
    rw [show (⟨j3.val + 1, hltj3⟩ : Fin r) = j2 from
      Fin.ext (by simp only [j3, j2, Fin.val_mk]; omega)]
    exact Finset.pair_comm _ _
  have hstdj3s : (omStd r (by omega) j3).2 = false :=
    omStd_sign_chain (hr := by omega) (k := j3) (h := hltj3)
  have hstdj1 : omSupp (omStd r (by omega) j1) = {j1, j2} := by
    rw [omSupp_omStd_last (hr := by omega) (k := j1) (h := hltj1)]
    simp only [j1, j2]
    exact Finset.pair_comm _ _
  have hstdj1s : (omStd r (by omega) j1).2 = true :=
    omStd_sign_last (hr := by omega) (k := j1) (h := hltj1)
  refine ⟨(OmMove.togIf x.2 j1).comp ((OmMove.togIf y.2 j3).comp (OmMove.perm σ)), ?_, ?_, ?_⟩
  · apply omPlusIdx_ext
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, hx1]
      exact hstdj2.symm
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        plh_togIf_sign_mem (h := by rw [OmMove.omSupp_togIf_f, hx1]; simp),
        plh_togIf_sign_not_mem (h := by rw [hx1]; simp [j1, j2, j3, Fin.ext_iff]; omega),
        omPerm_sign σ x]
      rw [show (omStd r (by omega) ⟨r - 2, by omega⟩).2 = false from hstdj2s]
      simp [Bool.xor_self]
  · apply omPlusIdx_ext
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, hy1]
      exact hstdj3.symm
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        plh_togIf_sign_not_mem (h := by
          rw [OmMove.omSupp_togIf_f, hy1]; simp [j1, j2, j3, Fin.ext_iff]; omega),
        plh_togIf_sign_mem (h := by rw [hy1]; simp),
        omPerm_sign σ y]
      rw [show (omStd r (by omega) ⟨r - 3, by omega⟩).2 = false from hstdj3s]
      simp [Bool.xor_self]
  · apply omPlusIdx_ext
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, hz1]
      exact hstdj1.symm
    · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f,
        plh_togIf_sign_mem (h := by rw [OmMove.omSupp_togIf_f, hz1]; simp),
        plh_togIf_sign_not_mem (h := by rw [hz1]; simp [j1, j2, j3, Fin.ext_iff]; omega),
        omPerm_sign σ z]
      rw [show (omStd r (by omega) ⟨r - 1, by omega⟩).2 = true from hstdj1s]
      rw [Bool.xor_comm]
      cases hx : x.2 <;> cases hz : z.2 <;> simp_all [Bool.xor]

end CFSG.StandardType.QTwo

end
