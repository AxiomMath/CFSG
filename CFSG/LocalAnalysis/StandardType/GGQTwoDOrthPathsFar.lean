module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsPair
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus

variable {p r : ℕ}

private theorem plh_injective_vec6 {β : Type*} {a b c d e f : β}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Injective ![a, b, c, d, e, f] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> tauto

private theorem plh_ne_of_disjoint {s t : Finset (Fin r)} (h : Disjoint s t) {a b : Fin r}
    (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
  h.forall_ne_finset ha hb

private theorem plh_far_coords {x₁ x₂ x₃ x₄ : OmPlusIdx r}
    (h12 : omSupp x₁ ≠ omSupp x₂) (h12' : ¬ Disjoint (omSupp x₁) (omSupp x₂))
    (h34 : omSupp x₃ ≠ omSupp x₄) (h34' : ¬ Disjoint (omSupp x₃) (omSupp x₄))
    (h13 : Disjoint (omSupp x₁) (omSupp x₃)) (h14 : Disjoint (omSupp x₁) (omSupp x₄))
    (h23 : Disjoint (omSupp x₂) (omSupp x₃)) (h24 : Disjoint (omSupp x₂) (omSupp x₄)) :
    ∃ a b c d e f : Fin r, omSupp x₁ = {a, b} ∧ omSupp x₂ = {b, c} ∧
      omSupp x₃ = {d, e} ∧ omSupp x₄ = {e, f} ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
      c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  obtain ⟨a, b, c, hab, hbc, hac, hx1, hx2⟩ := exists_coords_pair h12 h12'
  obtain ⟨d, e, f, hde, hef, hdf, hx3, hx4⟩ := exists_coords_pair h34 h34'
  have ha1 : a ∈ omSupp x₁ := by rw [hx1]; simp
  have hb1 : b ∈ omSupp x₁ := by rw [hx1]; simp
  have hb2 : b ∈ omSupp x₂ := by rw [hx2]; simp
  have hc2 : c ∈ omSupp x₂ := by rw [hx2]; simp
  have hd3 : d ∈ omSupp x₃ := by rw [hx3]; simp
  have he3 : e ∈ omSupp x₃ := by rw [hx3]; simp
  have hf4 : f ∈ omSupp x₄ := by rw [hx4]; simp
  exact ⟨a, b, c, d, e, f, hx1, hx2, hx3, hx4, hab, hac,
    plh_ne_of_disjoint h13 ha1 hd3, plh_ne_of_disjoint h13 ha1 he3,
    plh_ne_of_disjoint h14 ha1 hf4, hbc,
    plh_ne_of_disjoint h23 hb2 hd3, plh_ne_of_disjoint h13 hb1 he3,
    plh_ne_of_disjoint h24 hb2 hf4, plh_ne_of_disjoint h23 hc2 hd3,
    plh_ne_of_disjoint h23 hc2 he3, plh_ne_of_disjoint h24 hc2 hf4, hde, hdf, hef⟩

private theorem plh_omStd_supp_zero {r : ℕ} (hr : 6 ≤ r) :
    omSupp (omStd r (by omega) ⟨0, by omega⟩) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
  have h : 1 < r := by omega
  rw [omSupp_omStd_chain (hr := by omega) (k := (⟨0, by omega⟩ : Fin r)) h]

private theorem plh_omStd_supp_one {r : ℕ} (hr : 6 ≤ r) :
    omSupp (omStd r (by omega) ⟨1, by omega⟩) = {⟨1, by omega⟩, ⟨2, by omega⟩} := by
  have h : 2 < r := by omega
  rw [omSupp_omStd_chain (hr := by omega) (k := (⟨1, by omega⟩ : Fin r)) h]

private theorem plh_omStd_supp_three {r : ℕ} (hr : 6 ≤ r) :
    omSupp (omStd r (by omega) ⟨3, by omega⟩) = {⟨3, by omega⟩, ⟨4, by omega⟩} := by
  have h : 4 < r := by omega
  rw [omSupp_omStd_chain (hr := by omega) (k := (⟨3, by omega⟩ : Fin r)) h]

private theorem plh_omStd_supp_four {r : ℕ} (hr : 6 ≤ r) :
    omSupp (omStd r (by omega) ⟨4, by omega⟩) = {⟨4, by omega⟩, ⟨5, by omega⟩} := by
  have h : 5 < r := by omega
  rw [omSupp_omStd_chain (hr := by omega) (k := (⟨4, by omega⟩ : Fin r)) h]

private theorem plh_omStd_sign_zero {r : ℕ} (hr : 6 ≤ r) :
    (omStd r (by omega) ⟨0, by omega⟩).2 = false := by
  have h : 1 < r := by omega
  exact omStd_sign_chain (hr := by omega) (k := (⟨0, by omega⟩ : Fin r)) h

private theorem plh_omStd_sign_one {r : ℕ} (hr : 6 ≤ r) :
    (omStd r (by omega) ⟨1, by omega⟩).2 = false := by
  have h : 2 < r := by omega
  exact omStd_sign_chain (hr := by omega) (k := (⟨1, by omega⟩ : Fin r)) h

private theorem plh_omStd_sign_three {r : ℕ} (hr : 6 ≤ r) :
    (omStd r (by omega) ⟨3, by omega⟩).2 = false := by
  have h : 4 < r := by omega
  exact omStd_sign_chain (hr := by omega) (k := (⟨3, by omega⟩ : Fin r)) h

private theorem plh_omStd_sign_four {r : ℕ} (hr : 6 ≤ r) :
    (omStd r (by omega) ⟨4, by omega⟩).2 = false := by
  have h : 5 < r := by omega
  exact omStd_sign_chain (hr := by omega) (k := (⟨4, by omega⟩ : Fin r)) h

private theorem plh_togIf_sign_mem {b : Bool} {i : Fin r} {x : OmPlusIdx r}
    (h : i ∈ omSupp x) : ((OmMove.togIf (p := p) b i).f x).2 = Bool.xor x.2 b := by
  rw [OmMove.togIf_f_sign, decide_eq_true h, Bool.and_true]

private theorem plh_togIf_sign_notMem {b : Bool} {i : Fin r} {x : OmPlusIdx r}
    (h : i ∉ omSupp x) : ((OmMove.togIf (p := p) b i).f x).2 = x.2 := by
  rw [OmMove.togIf_f_sign, decide_eq_false h, Bool.and_false, Bool.xor_false]

theorem omFar_six_le {x₁ x₂ x₃ x₄ : OmPlusIdx r} (h12 : omSupp x₁ ≠ omSupp x₂)
    (h12' : ¬ Disjoint (omSupp x₁) (omSupp x₂)) (h34 : omSupp x₃ ≠ omSupp x₄)
    (h34' : ¬ Disjoint (omSupp x₃) (omSupp x₄)) (h13 : Disjoint (omSupp x₁) (omSupp x₃))
    (h14 : Disjoint (omSupp x₁) (omSupp x₄)) (h23 : Disjoint (omSupp x₂) (omSupp x₃))
    (h24 : Disjoint (omSupp x₂) (omSupp x₄)) : 6 ≤ r := by
  obtain ⟨a, b, c, d, e, f, -, -, -, -, hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
    hcd, hce, hcf, hde, hdf, hef⟩ :=
    plh_far_coords h12 h12' h34 h34' h13 h14 h23 h24
  have hinj : Function.Injective ![a, b, c, d, e, f] :=
    plh_injective_vec6 hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
  have hcard := Fintype.card_le_of_injective ![a, b, c, d, e, f] hinj
  simpa using hcard

theorem omMove_far (hr : 6 ≤ r) {x₁ x₂ x₃ x₄ : OmPlusIdx r} (h12 : omSupp x₁ ≠ omSupp x₂)
    (h12' : ¬ Disjoint (omSupp x₁) (omSupp x₂)) (h34 : omSupp x₃ ≠ omSupp x₄)
    (h34' : ¬ Disjoint (omSupp x₃) (omSupp x₄)) (h13 : Disjoint (omSupp x₁) (omSupp x₃))
    (h14 : Disjoint (omSupp x₁) (omSupp x₄)) (h23 : Disjoint (omSupp x₂) (omSupp x₃))
    (h24 : Disjoint (omSupp x₂) (omSupp x₄)) :
    ∃ m : OmMove p r, m.f x₁ = omStd r (by omega) ⟨0, by omega⟩ ∧
      m.f x₂ = omStd r (by omega) ⟨1, by omega⟩ ∧ m.f x₃ = omStd r (by omega) ⟨3, by omega⟩ ∧
      m.f x₄ = omStd r (by omega) ⟨4, by omega⟩ := by
  obtain ⟨a, b, c, d, e, f, hx1ab, hx2bc, hx3de, hx4ef, hab, hac, had, hae, haf, hbc, hbd,
    hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ :=
    plh_far_coords h12 h12' h34 h34' h13 h14 h23 h24
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  let i2 : Fin r := ⟨2, by omega⟩
  let i3 : Fin r := ⟨3, by omega⟩
  let i4 : Fin r := ⟨4, by omega⟩
  let i5 : Fin r := ⟨5, by omega⟩
  have hf : Function.Injective ![a, b, c, d, e, f] :=
    plh_injective_vec6 hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
  have hg : Function.Injective ![i0, i1, i2, i3, i4, i5] :=
    plh_injective_vec6
      (by simp [i0, i1, Fin.ext_iff]) (by simp [i0, i2, Fin.ext_iff])
      (by simp [i0, i3, Fin.ext_iff]) (by simp [i0, i4, Fin.ext_iff])
      (by simp [i0, i5, Fin.ext_iff]) (by simp [i1, i2, Fin.ext_iff])
      (by simp [i1, i3, Fin.ext_iff]) (by simp [i1, i4, Fin.ext_iff])
      (by simp [i1, i5, Fin.ext_iff]) (by simp [i2, i3, Fin.ext_iff])
      (by simp [i2, i4, Fin.ext_iff]) (by simp [i2, i5, Fin.ext_iff])
      (by simp [i3, i4, Fin.ext_iff]) (by simp [i3, i5, Fin.ext_iff])
      (by simp [i4, i5, Fin.ext_iff])
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (α := Fin 6) (β := Fin r)
    ![a, b, c, d, e, f] ![i0, i1, i2, i3, i4, i5] hf hg
  have hσa : σ a = i0 := by simpa using hσ 0
  have hσb : σ b = i1 := by simpa using hσ 1
  have hσc : σ c = i2 := by simpa using hσ 2
  have hσd : σ d = i3 := by simpa using hσ 3
  have hσe : σ e = i4 := by simpa using hσ 4
  have hσf : σ f = i5 := by simpa using hσ 5
  have hx1 : omSupp (omPerm σ x₁) = {i0, i1} := by
    rw [omSupp_omPerm, hx1ab]; simp [hσa, hσb]
  have hx2 : omSupp (omPerm σ x₂) = {i1, i2} := by
    rw [omSupp_omPerm, hx2bc]; simp [hσb, hσc]
  have hx3 : omSupp (omPerm σ x₃) = {i3, i4} := by
    rw [omSupp_omPerm, hx3de]; simp [hσd, hσe]
  have hx4 : omSupp (omPerm σ x₄) = {i4, i5} := by
    rw [omSupp_omPerm, hx4ef]; simp [hσe, hσf]
  let M1 : OmMove p r := OmMove.togIf (p := p) x₁.2 i0
  let M2 : OmMove p r := OmMove.togIf (p := p) x₂.2 i2
  let M3 : OmMove p r := OmMove.togIf (p := p) x₃.2 i3
  let M4 : OmMove p r := OmMove.togIf (p := p) x₄.2 i5
  let m : OmMove p r := M4.comp (M3.comp (M2.comp (M1.comp (OmMove.perm (p := p) σ))))
  have hs1 : (M1.f ((OmMove.perm (p := p) σ).f x₁)).2 = false := by
    rw [plh_togIf_sign_mem (x := (OmMove.perm (p := p) σ).f x₁) (b := x₁.2) (i := i0)
      (by rw [OmMove.perm_f, hx1]; simp)]
    rw [OmMove.perm_f, omPerm_sign, Bool.xor_self]
  have hs2 : (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₁))).2 = false := by
    rw [plh_togIf_sign_notMem (x := M1.f ((OmMove.perm (p := p) σ).f x₁)) (b := x₂.2) (i := i2)
      (by rw [OmMove.omSupp_togIf_f, OmMove.perm_f, hx1]; simp [i0, i1, i2, Fin.ext_iff])]
    exact hs1
  have hs3 : (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₁)))).2 = false := by
    rw [plh_togIf_sign_notMem (x := M2.f (M1.f ((OmMove.perm (p := p) σ).f x₁))) (b := x₃.2)
      (i := i3)
      (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.perm_f, hx1];
          simp [i0, i1, i3, Fin.ext_iff])]
    exact hs2
  have hs4 : (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₁))))).2 = false := by
    rw [plh_togIf_sign_notMem (x := M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₁)))) (b := x₄.2)
      (i := i5) (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
          OmMove.perm_f, hx1]; simp [i0, i1, i5, Fin.ext_iff])]
    exact hs3
  have ht1 : (M1.f ((OmMove.perm (p := p) σ).f x₂)).2 = x₂.2 := by
    rw [plh_togIf_sign_notMem (x := (OmMove.perm (p := p) σ).f x₂) (b := x₁.2) (i := i0)
      (by rw [OmMove.perm_f, hx2]; simp [i0, i1, i2, Fin.ext_iff])]
    rw [OmMove.perm_f, omPerm_sign]
  have ht2 : (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₂))).2 = false := by
    rw [plh_togIf_sign_mem (x := M1.f ((OmMove.perm (p := p) σ).f x₂)) (b := x₂.2) (i := i2)
      (by rw [OmMove.omSupp_togIf_f, OmMove.perm_f, hx2]; simp)]
    rw [ht1, Bool.xor_self]
  have ht3 : (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₂)))).2 = false := by
    rw [plh_togIf_sign_notMem (x := M2.f (M1.f ((OmMove.perm (p := p) σ).f x₂))) (b := x₃.2)
      (i := i3)
      (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.perm_f, hx2];
          simp [i1, i2, i3, Fin.ext_iff])]
    exact ht2
  have ht4 : (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₂))))).2 = false := by
    rw [plh_togIf_sign_notMem (x := M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₂)))) (b := x₄.2)
      (i := i5) (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
          OmMove.perm_f, hx2]; simp [i1, i2, i5, Fin.ext_iff])]
    exact ht3
  have hu1 : (M1.f ((OmMove.perm (p := p) σ).f x₃)).2 = x₃.2 := by
    rw [plh_togIf_sign_notMem (x := (OmMove.perm (p := p) σ).f x₃) (b := x₁.2) (i := i0)
      (by rw [OmMove.perm_f, hx3]; simp [i0, i3, i4, Fin.ext_iff])]
    rw [OmMove.perm_f, omPerm_sign]
  have hu2 : (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₃))).2 = x₃.2 := by
    rw [plh_togIf_sign_notMem (x := M1.f ((OmMove.perm (p := p) σ).f x₃)) (b := x₂.2) (i := i2)
      (by rw [OmMove.omSupp_togIf_f, OmMove.perm_f, hx3]; simp [i2, i3, i4, Fin.ext_iff])]
    exact hu1
  have hu3 : (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₃)))).2 = false := by
    rw [plh_togIf_sign_mem (x := M2.f (M1.f ((OmMove.perm (p := p) σ).f x₃))) (b := x₃.2)
      (i := i3)
      (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.perm_f, hx3]; simp)]
    rw [hu2, Bool.xor_self]
  have hu4 : (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₃))))).2 = false := by
    rw [plh_togIf_sign_notMem (x := M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₃)))) (b := x₄.2)
      (i := i5) (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
          OmMove.perm_f, hx3]; simp [i3, i4, i5, Fin.ext_iff])]
    exact hu3
  have hv1 : (M1.f ((OmMove.perm (p := p) σ).f x₄)).2 = x₄.2 := by
    rw [plh_togIf_sign_notMem (x := (OmMove.perm (p := p) σ).f x₄) (b := x₁.2) (i := i0)
      (by rw [OmMove.perm_f, hx4]; simp [i0, i4, i5, Fin.ext_iff])]
    rw [OmMove.perm_f, omPerm_sign]
  have hv2 : (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₄))).2 = x₄.2 := by
    rw [plh_togIf_sign_notMem (x := M1.f ((OmMove.perm (p := p) σ).f x₄)) (b := x₂.2) (i := i2)
      (by rw [OmMove.omSupp_togIf_f, OmMove.perm_f, hx4]; simp [i2, i4, i5, Fin.ext_iff])]
    exact hv1
  have hv3 : (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₄)))).2 = x₄.2 := by
    rw [plh_togIf_sign_notMem (x := M2.f (M1.f ((OmMove.perm (p := p) σ).f x₄))) (b := x₃.2)
      (i := i3)
      (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.perm_f, hx4];
          simp [i3, i4, i5, Fin.ext_iff])]
    exact hv2
  have hv4 : (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₄))))).2 = false := by
    rw [plh_togIf_sign_mem (x := M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₄)))) (b := x₄.2)
      (i := i5) (by rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
          OmMove.perm_f, hx4]; simp)]
    rw [hv3, Bool.xor_self]
  refine ⟨m, ?_, ?_, ?_, ?_⟩
  · apply omPlusIdx_ext
    · change omSupp (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₁))))) =
        omSupp (omStd r (by omega) ⟨0, by omega⟩)
      rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, OmMove.perm_f, hx1]
      exact (plh_omStd_supp_zero hr).symm
    · rw [plh_omStd_sign_zero hr]
      exact hs4
  · apply omPlusIdx_ext
    · change omSupp (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₂))))) =
        omSupp (omStd r (by omega) ⟨1, by omega⟩)
      rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, OmMove.perm_f, hx2]
      exact (plh_omStd_supp_one hr).symm
    · rw [plh_omStd_sign_one hr]
      exact ht4
  · apply omPlusIdx_ext
    · change omSupp (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₃))))) =
        omSupp (omStd r (by omega) ⟨3, by omega⟩)
      rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, OmMove.perm_f, hx3]
      exact (plh_omStd_supp_three hr).symm
    · rw [plh_omStd_sign_three hr]
      exact hu4
  · apply omPlusIdx_ext
    · change omSupp (M4.f (M3.f (M2.f (M1.f ((OmMove.perm (p := p) σ).f x₄))))) =
        omSupp (omStd r (by omega) ⟨4, by omega⟩)
      rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f,
        OmMove.omSupp_togIf_f, OmMove.perm_f, hx4]
      exact (plh_omStd_supp_four hr).symm
    · rw [plh_omStd_sign_four hr]
      exact hv4

end CFSG.StandardType.QTwo

end
