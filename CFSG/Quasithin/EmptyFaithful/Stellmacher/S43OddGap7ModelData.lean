module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7ModelHyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod Equiv
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Gap7

namespace Model

private theorem S5SylF_cases : ∀ k ∈ S5SylF,
    (k ∈ S5ThatF ∧ S5g⁻¹ * k * S5g ∈ S5ThatF) ∨ (S5g⁻¹ * k ∈ S5ThatF ∧ k * S5g ∈ S5ThatF) := by
  decide +kernel

theorem S5Syl_cases {k : Perm (Fin 5)} (hk : k ∈ S5Syl) :
    (k ∈ S5That ∧ S5g⁻¹ * k * S5g ∈ S5That) ∨ (S5g⁻¹ * k ∈ S5That ∧ k * S5g ∈ S5That) := by
  simp only [mem_S5That_iff]
  exact S5SylF_cases k ((mem_S5Syl_iff k).mp hk)

theorem S5g_mem_S5Syl : S5g ∈ S5Syl := (mem_S5Syl_iff _).mpr (by decide +kernel)

theorem S5g_not_mem_S5That : S5g ∉ S5That := by
  rw [mem_S5That_iff]
  decide +kernel

variable {G : Type} [Group G]

section Dict

variable {X S Z : Subgroup G} (D : Dict5 X S Z)

@[expose] noncomputable def dictLift (h : Perm (Fin 5)) : ↥X := Function.surjInv D.surj h

theorem ψ_dictLift (h : Perm (Fin 5)) : D.ψ (dictLift D h) = h := Function.surjInv_eq D.surj h

@[expose] noncomputable def dictPre (z : G) : orth.W := Function.invFun D.φ z

theorem φ_dictPre {z : G} (hz : z ∈ Z) : D.φ (dictPre D z) = z :=
  Function.invFun_eq (MonoidHom.mem_range.mp (D.range_eq.ge hz))

theorem dictPre_φ (w : orth.W) : dictPre D (D.φ w) = w := Function.leftInverse_invFun D.inj w

theorem dictPre_mul {z z' : G} (hz : z ∈ Z) (hz' : z' ∈ Z) :
    dictPre D (z * z') = dictPre D z * dictPre D z' :=
  D.inj (by rw [φ_dictPre D (Z.mul_mem hz hz'), map_mul, φ_dictPre D hz, φ_dictPre D hz'])

theorem dictPre_inv {z : G} (hz : z ∈ Z) : dictPre D z⁻¹ = (dictPre D z)⁻¹ :=
  D.inj (by rw [φ_dictPre D (Z.inv_mem hz), map_inv, φ_dictPre D hz])

theorem dictPre_one : dictPre D 1 = 1 := D.inj (by rw [φ_dictPre D Z.one_mem, map_one])

theorem dictPre_mem_iff {V : Subgroup orth.W} {z : G} (hz : z ∈ Z) :
    dictPre D z ∈ V ↔ z ∈ V.map D.φ := by
  constructor
  · intro h
    exact ⟨_, h, φ_dictPre D hz⟩
  · rintro ⟨w, hw, rfl⟩
    rwa [dictPre_φ]

theorem exists_eq_mul_of_ψ_eq {a b : ↥X} (h : D.ψ a = D.ψ b) :
    ∃ q ∈ pCoreOf 2 X, (b : G) = a * q :=
  ⟨((a⁻¹ * b : ↥X) : G), (D.ker_iff _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel]),
    by simp⟩

end Dict

variable {H M : Subgroup G}

structure Data (ρ : Geo H M) where
  δ₀ : Geo H M
  hδ₀ : δ₀ ∈ nbrs ρ
  D : Dict5 (stab ρ) (stab ρ ⊓ stab δ₀) (Zv ρ)
  u : G
  hu : u ∈ Vn δ₀
  hgu : ⁅u, (dictLift D S5g : G)⁆ ∉ Zv ρ

namespace Data

variable {ρ : Geo H M} (d : Data ρ)

@[expose] noncomputable def pt (h : Perm (Fin 5)) : G :=
  (dictLift d.D h : G) * d.u * (dictLift d.D h : G)⁻¹

@[expose] noncomputable def form (h h' : Perm (Fin 5)) : orth.W :=
  dictPre d.D ⁅d.pt h, d.pt h'⁆

@[expose] noncomputable def nb (h : Perm (Fin 5)) : Geo H M :=
  (⟨(dictLift d.D h : G), stab_le ρ (dictLift d.D h).2⟩ : ↥(H ⊔ M)) • d.δ₀

theorem lift_mem_edge {k : Perm (Fin 5)} (hk : k ∈ S5Syl) :
    (dictLift d.D k : G) ∈ stab ρ ⊓ stab d.δ₀ :=
  (d.D.mem_S_iff _).mpr (by rw [ψ_dictLift]; exact hk)

theorem pt_mem_V0 {k : Perm (Fin 5)} (hk : k ∈ S5Syl) : d.pt k ∈ Vn d.δ₀ :=
  conj_mem_Vn (d.lift_mem_edge hk).2 d.hu

theorem pt_mem_nb (h : Perm (Fin 5)) : d.pt h ∈ Vn (d.nb h) := by
  rw [nb, Vn_smul]
  exact mul_mem_conjSub d.hu

variable [Finite G] {S : Subgroup G}

theorem nb_mem (h : Perm (Fin 5)) : d.nb h ∈ nbrs ρ :=
  smul_mem_nbrs_of_mem_stab _ (dictLift d.D h).2 d.hδ₀

theorem u_mem_Wn (hy : Hyp S ρ) : d.u ∈ Wn ρ := hy.Vn_le_Wn d.hδ₀ d.hu

theorem pt_mem_Wn (hy : Hyp S ρ) (h : Perm (Fin 5)) : d.pt h ∈ Wn ρ :=
  conj_mem_Wn (dictLift d.D h).2 (d.u_mem_Wn hy)

theorem pt_mem_Qv (hy : Hyp S ρ) (h : Perm (Fin 5)) : d.pt h ∈ Qv ρ :=
  hy.Wn_le_Qv (d.pt_mem_Wn hy h)

theorem pt_sq (hy : Hyp S ρ) (h : Perm (Fin 5)) : d.pt h * d.pt h = 1 := by
  have hu2 := hy.Vn_sq d.hu
  unfold pt
  calc (dictLift d.D h : G) * d.u * (dictLift d.D h : G)⁻¹ *
        ((dictLift d.D h : G) * d.u * (dictLift d.D h : G)⁻¹) =
        (dictLift d.D h : G) * (d.u * d.u) * (dictLift d.D h : G)⁻¹ := by group
    _ = 1 := by rw [hu2]; group

theorem u_not_mem (hy : Hyp S ρ) : d.u ∉ Zv ρ := fun hu => d.hgu (by
  have e : ⁅d.u, (dictLift d.D S5g : G)⁆ =
      d.u * ((dictLift d.D S5g : G) * d.u⁻¹ * (dictLift d.D S5g : G)⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e]
  exact (Zv ρ).mul_mem hu (hy.conj_mem_Zv (dictLift d.D S5g).2 ((Zv ρ).inv_mem hu)))

theorem pt_not_mem (hy : Hyp S ρ) (h : Perm (Fin 5)) : d.pt h ∉ Zv ρ := fun hp => d.u_not_mem hy (by
  have e : d.u = (dictLift d.D h : G)⁻¹ * d.pt h * (dictLift d.D h : G)⁻¹⁻¹ := by
    unfold pt; group
  rw [e]
  exact hy.conj_mem_Zv ((stab ρ).inv_mem (dictLift d.D h).2) hp)

theorem comm_pt_mem (hy : Hyp S ρ) (h h' : Perm (Fin 5)) : ⁅d.pt h, d.pt h'⁆ ∈ Zv ρ :=
  hy.comm_mem (d.pt_mem_Wn hy h) (d.pt_mem_Wn hy h')

theorem φ_form (hy : Hyp S ρ) (h h' : Perm (Fin 5)) :
    d.D.φ (d.form h h') = ⁅d.pt h, d.pt h'⁆ :=
  φ_dictPre d.D (d.comm_pt_mem hy h h')

theorem pt_conj (hy : Hyp S ρ) (y : ↥(stab ρ)) (h : Perm (Fin 5)) :
    ∃ z ∈ Zv ρ, d.pt (d.D.ψ y * h) = z * ((y : G) * d.pt h * (y : G)⁻¹) := by
  obtain ⟨q, hq, hqe⟩ := exists_eq_mul_of_ψ_eq d.D (a := y * dictLift d.D h)
    (b := dictLift d.D (d.D.ψ y * h)) (by rw [map_mul, ψ_dictLift, ψ_dictLift])
  obtain ⟨z, hz, hze⟩ := hy.conj_eq_of_mem_Qv hq (d.u_mem_Wn hy)
  refine ⟨((y * dictLift d.D h : ↥(stab ρ)) : G) * z * ((y * dictLift d.D h : ↥(stab ρ)) : G)⁻¹,
    hy.conj_mem_Zv (y * dictLift d.D h).2 hz, ?_⟩
  unfold pt
  rw [hqe]
  simp only [Subgroup.coe_mul]
  calc (y : G) * (dictLift d.D h : G) * q * d.u * ((y : G) * (dictLift d.D h : G) * q)⁻¹ =
        ((y : G) * (dictLift d.D h : G)) * (q * d.u * q⁻¹) *
          ((y : G) * (dictLift d.D h : G))⁻¹ := by group
    _ = ((y : G) * (dictLift d.D h : G)) * (z * d.u) * ((y : G) * (dictLift d.D h : G))⁻¹ := by
        rw [hze]
    _ = _ := by group

theorem pt_That (hy : Hyp S ρ) {t : Perm (Fin 5)} (ht : t ∈ S5That) :
    ∃ z ∈ Zv ρ, d.pt t = z * d.u := by
  have hδv := hy.vtype_nbr d.hδ₀
  have hρδ : ρ ∈ nbrs d.δ₀ := nbrs_symm d.hδ₀
  have h1 := (d.D.mem_centralizer_Y_iff (dictLift d.D t)).mpr (by rw [ψ_dictLift]; exact ht)
  rw [← hy.hs.Yv_eq_comm_comm hy.hA hy.h26 hδv hρδ,
    ← hy.hs.Qv_sup_Qst hy.hA hy.h26 hδv hρδ] at h1
  obtain ⟨q1, hq1, q2, hq2, he⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    (((inf_le_left : Qst d.δ₀ ≤ Qv d.δ₀).trans (Qv_le_stab_of_mem_nbrs hy.hA hρδ)).trans
      (le_normalizer_pCoreOf 2 (stab ρ)))).mp h1
  have hY : ⁅d.u, q2⁆ ∈ Yv d.δ₀ := hy.hs.comm_Vn_Qst hy.hA hy.h26 hδv hρδ ▸
    Subgroup.commutator_mem_commutator d.hu hq2
  have hYZ : ⁅d.u, q2⁆⁻¹ ∈ Zv ρ := (Zv ρ).inv_mem (Yv_le_Zv hρδ hY)
  obtain ⟨z1, hz1, hz1e⟩ := hy.conj_eq_of_mem_Qv hq1 (d.u_mem_Wn hy)
  refine ⟨⁅d.u, q2⁆⁻¹ * z1, (Zv ρ).mul_mem hYZ hz1, ?_⟩
  have e2 : q2 * d.u * q2⁻¹ = ⁅d.u, q2⁆⁻¹ * d.u := by rw [commutatorElement_def]; group
  have e3 : d.pt t = q1 * (q2 * d.u * q2⁻¹) * q1⁻¹ := by
    unfold pt
    rw [he]
    group
  rw [e3, e2, show q1 * (⁅d.u, q2⁆⁻¹ * d.u) * q1⁻¹ =
      (q1 * ⁅d.u, q2⁆⁻¹ * q1⁻¹) * (q1 * d.u * q1⁻¹) by group, hy.conj_eq_self hq1 hYZ, hz1e,
    mul_assoc]

theorem pt_mul_That (hy : Hyp S ρ) (h : Perm (Fin 5)) {t : Perm (Fin 5)} (ht : t ∈ S5That) :
    ∃ z ∈ Zv ρ, d.pt (h * t) = z * d.pt h := by
  obtain ⟨z1, hz1, e1⟩ := d.pt_conj hy (dictLift d.D h) t
  rw [ψ_dictLift] at e1
  obtain ⟨z2, hz2, e2⟩ := d.pt_That hy ht
  refine ⟨z1 * ((dictLift d.D h : G) * z2 * (dictLift d.D h : G)⁻¹),
    (Zv ρ).mul_mem hz1 (hy.conj_mem_Zv (dictLift d.D h).2 hz2), ?_⟩
  rw [e1, e2]
  unfold pt
  group

theorem form_equi (hy : Hyp S ρ) (k h h' : Perm (Fin 5)) :
    d.form (k * h) (k * h') = orth.act k (d.form h h') := by
  obtain ⟨z1, hz1, e1⟩ := d.pt_conj hy (dictLift d.D k) h
  obtain ⟨z2, hz2, e2⟩ := d.pt_conj hy (dictLift d.D k) h'
  rw [ψ_dictLift] at e1 e2
  have hA1 := hy.Wn_le_Qv (conj_mem_Wn (dictLift d.D k).2 (d.pt_mem_Wn hy h))
  have hA2 := hy.Wn_le_Qv (conj_mem_Wn (dictLift d.D k).2 (d.pt_mem_Wn hy h'))
  show dictPre d.D ⁅d.pt (k * h), d.pt (k * h')⁆ = orth.act k (d.form h h')
  rw [e1, e2, Three.commutatorElement_mul_mul (hy.cen hA1 hz1).symm (hy.cen hA2 hz1).symm
    (hy.Zv_comm hz1 hz2) (hy.cen hA1 hz2).symm (hy.cen hA2 hz2).symm, ← conj_comm_eq,
    ← d.φ_form hy h h', ← d.D.act_eq, ψ_dictLift, dictPre_φ]

theorem form_right (hy : Hyp S ρ) (h h' t : Perm (Fin 5)) (ht : t ∈ S5That) :
    d.form (h * t) h' = d.form h h' := by
  obtain ⟨z, hz, e⟩ := d.pt_mul_That hy h ht
  show dictPre d.D ⁅d.pt (h * t), d.pt h'⁆ = dictPre d.D ⁅d.pt h, d.pt h'⁆
  rw [e, comm_mul_left_central (hy.cen (d.pt_mem_Qv hy h) hz).symm
    (hy.cen (d.pt_mem_Qv hy h') hz).symm]

theorem form_symm (hy : Hyp S ρ) (h h' : Perm (Fin 5)) : d.form h h' = d.form h' h := by
  show dictPre d.D ⁅d.pt h, d.pt h'⁆ = dictPre d.D ⁅d.pt h', d.pt h⁆
  rw [comm_swap_of_sq (hy.Zv_sq (d.comm_pt_mem hy h h'))]

omit [Finite G] in
theorem form_diag (h : Perm (Fin 5)) : d.form h h = 1 := by
  show dictPre d.D ⁅d.pt h, d.pt h⁆ = 1
  rw [commutatorElement_self, dictPre_one]

theorem form_block (hy : Hyp S ρ) (h k : Perm (Fin 5)) (hk : k ∈ S5Syl) :
    d.form h (h * k) = 1 := by
  obtain ⟨z1, hz1, e1⟩ := d.pt_conj hy (dictLift d.D h) 1
  obtain ⟨z2, hz2, e2⟩ := d.pt_conj hy (dictLift d.D h) k
  rw [ψ_dictLift, mul_one] at e1
  rw [ψ_dictLift] at e2
  have hA1 := hy.Wn_le_Qv (conj_mem_Wn (dictLift d.D h).2 (d.pt_mem_Wn hy 1))
  have hA2 := hy.Wn_le_Qv (conj_mem_Wn (dictLift d.D h).2 (d.pt_mem_Wn hy k))
  have hc : ⁅d.pt 1, d.pt k⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).mpr
    (hy.Vn_comm (d.pt_mem_V0 (one_mem S5Syl)) (d.pt_mem_V0 hk))
  show dictPre d.D ⁅d.pt h, d.pt (h * k)⁆ = 1
  rw [e1, e2, Three.commutatorElement_mul_mul (hy.cen hA1 hz1).symm (hy.cen hA2 hz1).symm
    (hy.Zv_comm hz1 hz2) (hy.cen hA1 hz2).symm (hy.cen hA2 hz2).symm, ← conj_comm_eq, hc,
    mul_one, mul_inv_cancel, dictPre_one]

theorem formHyp (hy : Hyp S ρ) : FormHyp d.form :=
  ⟨d.form_equi hy, d.form_right hy, d.form_symm hy, d.form_diag, d.form_block hy⟩

end Data

end Model

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
