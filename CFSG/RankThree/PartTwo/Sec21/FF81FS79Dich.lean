module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Frame
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Frm

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace J6

theorem conj_to_v1 : ∀ s ∈ ({v1, v2, v3, e1 * pp, e1 * qq, pp * qq} : Finset S6),
    ∃ γ : S6, γ * s * γ⁻¹ = v1 := by decide +kernel

theorem mem_T1fin_cases : ∀ s ∈ T1fin, s = 1 ∨ s = e1 ∨ s = v1 ∨ s = v2 ∨ s = v3 ∨
    s = e1 * v1 ∨ s = e1 * v2 ∨ s = e1 * v3 := by decide +kernel

theorem mem_V1fin_cases : ∀ s ∈ V1fin, s = 1 ∨ s = e1 ∨ s = pp ∨ s = qq ∨ s = e1 * pp ∨
    s = e1 * qq ∨ s = pp * qq ∨ s = e1 * pp * qq := by decide +kernel

theorem x1_mem_T1 : e1 * v1 ∈ T1 := (by decide +kernel : e1 * v1 ∈ T1fin)

theorem x2_mem_T1 : e1 * v2 ∈ T1 := (by decide +kernel : e1 * v2 ∈ T1fin)

theorem x3_mem_T1 : e1 * v3 ∈ T1 := (by decide +kernel : e1 * v3 ∈ T1fin)

theorem e1_mem_V1 : e1 ∈ V1 := (by decide +kernel : e1 ∈ V1fin)

theorem pp_mem_V1 : pp ∈ V1 := (by decide +kernel : pp ∈ V1fin)

theorem qq_mem_V1 : qq ∈ V1 := (by decide +kernel : qq ∈ V1fin)

end J6

namespace Std

variable (S : Std b t b₁ b₂ J)

def Xi (A₁ : Subgroup J6.S6) : Prop :=
  ∀ n ∈ Nor (S.frame A₁), n ∈ Nor (A₁.map S.ι)

include S

theorem Xi_of_gens {A₁ : Subgroup J6.S6} {G : Finset J6.S6}
    (hgen : ∀ s ∈ A₁, ∃ a ∈ G, ∃ c ∈ G, ∃ d ∈ G, s = a * c * d)
    (hG : ∀ n ∈ Nor (S.frame A₁), ∀ a ∈ G, n * S.ι a * n⁻¹ ∈ A₁.map S.ι) : S.Xi A₁ := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨s, hs, rfl⟩ := hy
  obtain ⟨a, ha, c, hc, d, hd, rfl⟩ := hgen s hs
  have e : n * S.ι (a * c * d) * n⁻¹ =
      (n * S.ι a * n⁻¹) * (n * S.ι c * n⁻¹) * (n * S.ι d * n⁻¹) := by
    rw [map_mul, map_mul]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hG n hn a ha) (hG n hn c hc)) (hG n hn d hd)

theorem T_orbit (h34 : R34Stmt b b₁ b₂) {x : J6.S6} (hx : J6.Cl3 x) (hxT : x ∈ J6.T1) {n : H}
    (hn : n ∈ Nor (S.frame J6.T1)) :
    n * S.ι x * n⁻¹ ∈ J6.T1.map S.ι ∨ ∃ v ∈ ({J6.v1, J6.v2, J6.v3} : Finset J6.S6),
      HC (S.ι x) (t * S.ι v) := by
  have hmem : n * S.ι x * n⁻¹ ∈ S.frame J6.T1 :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (S.ι_mem_frame hxT)
  obtain ⟨s, hs, hy | hy⟩ := (S.mem_frame_iff J6.T1 _).mp hmem
  · left
    rw [hy]
    exact ⟨s, hs, rfl⟩
  · right
    have hHC : HC (S.ι x) (t * S.ι s) := ⟨n, hy⟩
    rcases J6.mem_T1fin_cases s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      rw [map_one, mul_one] at hHC
      exact S.nf_t_cl3 hx hHC.symm
    · exact absurd hHC.symm (S.nf_tcl1_cl3 J6.cl1_e1 hx)
    · exact ⟨J6.v1, by simp, hHC⟩
    · exact ⟨J6.v2, by simp, hHC⟩
    · exact ⟨J6.v3, by simp, hHC⟩
    · exact absurd hHC.symm (S.nf_tcl3_cl3 h34 J6.cl3_x1 hx)
    · exact absurd hHC.symm (S.nf_tcl3_cl3 h34 J6.cl3_x2 hx)
    · exact absurd hHC.symm (S.nf_tcl3_cl3 h34 J6.cl3_x3 hx)

theorem V_orbit (h34 : R34Stmt b b₁ b₂) {f : J6.S6} (hf : J6.Cl1 f) (hfV : f ∈ J6.V1) {n : H}
    (hn : n ∈ Nor (S.frame J6.V1)) :
    n * S.ι f * n⁻¹ ∈ J6.V1.map S.ι ∨ ∃ s ∈ ({J6.e1 * J6.pp, J6.e1 * J6.qq, J6.pp * J6.qq} :
      Finset J6.S6), HC (S.ι f) (t * S.ι s) := by
  have hmem : n * S.ι f * n⁻¹ ∈ S.frame J6.V1 :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (S.ι_mem_frame hfV)
  obtain ⟨s, hs, hy | hy⟩ := (S.mem_frame_iff J6.V1 _).mp hmem
  · left
    rw [hy]
    exact ⟨s, hs, rfl⟩
  · right
    have hHC : HC (S.ι f) (t * S.ι s) := ⟨n, hy⟩
    rcases J6.mem_V1fin_cases s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      rw [map_one, mul_one] at hHC
      exact S.nf_t_cl1 hf hHC.symm
    · exact absurd hHC.symm (S.nf_tcl1_cl1 J6.cl1_e1 hf)
    · exact absurd hHC.symm (S.nf_tcl1_cl1 J6.cl1_pp hf)
    · exact absurd hHC.symm (S.nf_tcl1_cl1 J6.cl1_qq hf)
    · exact ⟨J6.e1 * J6.pp, by simp, hHC⟩
    · exact ⟨J6.e1 * J6.qq, by simp, hHC⟩
    · exact ⟨J6.pp * J6.qq, by simp, hHC⟩
    · exact absurd hHC.symm (S.nf_tcl3_cl1 J6.cl3_y hf)

theorem not_both {x f v s : J6.S6} (hx : J6.Cl3 x) (hf : J6.Cl1 f)
    (hv : v ∈ ({J6.v1, J6.v2, J6.v3} : Finset J6.S6))
    (hs : s ∈ ({J6.e1 * J6.pp, J6.e1 * J6.qq, J6.pp * J6.qq} : Finset J6.S6))
    (h1 : HC (S.ι x) (t * S.ι v)) (h2 : HC (S.ι f) (t * S.ι s)) : False := by
  obtain ⟨γ, hγ⟩ := J6.conj_to_v1 v (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    tauto)
  obtain ⟨δ, hδ⟩ := J6.conj_to_v1 s (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
    tauto)
  have h3 : HC (t * S.ι v) (t * S.ι J6.v1) := S.HC_tι ⟨γ, hγ⟩
  have h4 : HC (t * S.ι s) (t * S.ι J6.v1) := S.HC_tι ⟨δ, hδ⟩
  have h5 : HC (S.ι x) (S.ι f) :=
    h1.trans (h3.trans (h4.symm.trans h2.symm))
  exact S.nf_cl1_cl3 hf hx h5.symm

theorem dichotomy (h34 : R34Stmt b b₁ b₂) : S.Xi J6.T1 ∨ S.Xi J6.V1 := by
  by_contra hcon
  obtain ⟨hT, hV⟩ := not_or.mp hcon
  have hT' : ∃ n ∈ Nor (S.frame J6.T1), ∃ x ∈ ({J6.e1 * J6.v1, J6.e1 * J6.v2, J6.e1 * J6.v3} :
      Finset J6.S6), n * S.ι x * n⁻¹ ∉ J6.T1.map S.ι := by
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    refine hT (S.Xi_of_gens (G := {1, J6.e1 * J6.v1, J6.e1 * J6.v2, J6.e1 * J6.v3}) ?_ ?_)
    · intro s hs
      obtain ⟨a, ha, c, hc, d, hd, h⟩ := J6.T1_gen s hs
      refine ⟨a, ?_, c, ?_, d, ?_, h⟩ <;>
      · simp only [Finset.mem_insert, Finset.mem_singleton] at ha hc hd ⊢
        tauto
    · intro n hn a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | ha
      · rw [map_one]
        simpa using (J6.T1.map S.ι).one_mem
      · exact hno n hn a (by simpa using ha)
  have hV' : ∃ n ∈ Nor (S.frame J6.V1), ∃ f ∈ ({J6.e1, J6.pp, J6.qq} : Finset J6.S6),
      n * S.ι f * n⁻¹ ∉ J6.V1.map S.ι := by
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    refine hV (S.Xi_of_gens (G := {1, J6.e1, J6.pp, J6.qq}) ?_ ?_)
    · intro s hs
      obtain ⟨a, ha, c, hc, d, hd, h⟩ := J6.V1_gen s hs
      refine ⟨a, ?_, c, ?_, d, ?_, h⟩ <;>
      · simp only [Finset.mem_insert, Finset.mem_singleton] at ha hc hd ⊢
        tauto
    · intro n hn a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | ha
      · rw [map_one]
        simpa using (J6.V1.map S.ι).one_mem
      · exact hno n hn a (by simpa using ha)
  obtain ⟨n, hn, x, hx, hnx⟩ := hT'
  obtain ⟨m, hm, f, hf, hmf⟩ := hV'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hf
  have hx' : J6.Cl3 x ∧ x ∈ J6.T1 := by
    rcases hx with rfl | rfl | rfl
    · exact ⟨J6.cl3_x1, J6.x1_mem_T1⟩
    · exact ⟨J6.cl3_x2, J6.x2_mem_T1⟩
    · exact ⟨J6.cl3_x3, J6.x3_mem_T1⟩
  have hf' : J6.Cl1 f ∧ f ∈ J6.V1 := by
    rcases hf with rfl | rfl | rfl
    · exact ⟨J6.cl1_e1, J6.e1_mem_V1⟩
    · exact ⟨J6.cl1_pp, J6.pp_mem_V1⟩
    · exact ⟨J6.cl1_qq, J6.qq_mem_V1⟩
  rcases S.T_orbit h34 hx'.1 hx'.2 hn with h1 | ⟨v, hv, h1⟩
  · exact hnx h1
  rcases S.V_orbit h34 hf'.1 hf'.2 hm with h2 | ⟨s', hs', h2⟩
  · exact hmf h2
  exact S.not_both hx'.1 hf'.1 hv hs' h1 h2

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
