module

public import CFSG.RankThree.PartOne.CTP.AsmComm
public import CFSG.RankThree.PartOne.CTP.AsmTorus

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

section Pair

variable {L B K : Subgroup G} {f₀ : ℕ} {b : G} {c : G} {F : LFam L B f₀ b K} {I : Subgroup G}

@[expose] def IsMP (F : LFam L B f₀ b K) (I : Subgroup G) (u v : Fin 5) (M : Subgroup G) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 5)) (x y : Fin 3), x ≠ y ∧ σ (e3 x) = u ∧ σ (e3 y) = v ∧
    M = Msg F I σ x y

omit [Finite G] in
theorem IsMP.ne {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) : u ≠ v := by
  obtain ⟨σ, x, y, hxy, rfl, rfl, -⟩ := h
  exact σ.injective.ne (e3_ne hxy)

theorem IsMP.eq (A : Asm c F I) {u v : Fin 5} {M M' : Subgroup G} (h : IsMP F I u v M)
    (h' : IsMP F I u v M') : M = M' := by
  obtain ⟨σ, x, y, hxy, h1, h2, rfl⟩ := h
  obtain ⟨τ, x', y', hxy', h1', h2', rfl⟩ := h'
  exact A.Msg_eq_of_pair hxy hxy' (h1.trans h1'.symm) (h2.trans h2'.symm)

omit [Finite G] in
theorem IsMP.J_le (A : Asm c F I) {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) :
    F.J u v ≤ M := by
  obtain ⟨σ, x, y, hxy, rfl, rfl, rfl⟩ := h
  exact (Jsg_eq F σ x y).symm.le.trans ((A.facts σ).J_le_M x y hxy)

omit [Finite G] in
theorem IsMP.model (A : Asm c F I) {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) :
    StatedClassicalModel ↥M .PSL 2 2 (5 * f₀) := by
  obtain ⟨σ, x, y, hxy, -, -, rfl⟩ := h
  exact (A.facts σ).M_model x y hxy

omit [Finite G] in
theorem IsMP.c_norm (A : Asm c F I) {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) :
    c ∈ Subgroup.normalizer (M : Set G) := by
  obtain ⟨σ, x, y, hxy, -, -, rfl⟩ := h
  exact (A.facts σ).c_norm_M x y hxy

omit [Finite G] in
theorem IsMP.c_outer (A : Asm c F I) {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) :
    c ∉ M ⊔ Subgroup.centralizer (M : Set G) := by
  obtain ⟨σ, x, y, hxy, -, -, rfl⟩ := h
  exact (A.facts σ).c_outer_M x y hxy

omit [Finite G] in
theorem IsMP.center_trivial (A : Asm c F I) {u v : Fin 5} {M : Subgroup G}
    (h : IsMP F I u v M) : M ⊓ Subgroup.centralizer (M : Set G) = ⊥ := by
  have hc := psl2_model_center_eq_bot (h.model A)
  rw [eq_bot_iff]
  intro x hx
  have hx1 : (⟨x, hx.1⟩ : ↥M) ∈ Subgroup.center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp hx.2 g g.2))
  rw [hc] at hx1
  have := congrArg Subtype.val (Subgroup.mem_bot.mp hx1)
  simpa using this

omit [Finite G] in
theorem Msg_swap (σ : Equiv.Perm (Fin 5)) (x y : Fin 3) : Msg F I σ x y = Msg F I σ y x := by
  unfold Msg
  rw [Jsg_eq, Jsg_eq, F.J_symm]

omit [Finite G] in
theorem Asm.adj_sup (A : Asm c F I) (σ : Equiv.Perm (Fin 5)) :
    Msg F I σ 0 1 ⊔ Msg F I σ 1 2 = Isg F I σ := by
  have := (A.facts σ).M_sup 1 0 2 (by decide) (by decide) (by decide)
  calc Msg F I σ 0 1 ⊔ Msg F I σ 1 2 = Msg F I σ 1 0 ⊔ Msg F I σ 1 2 := by
        rw [Msg_swap σ 0 1]
    _ = Isg F I σ := this

theorem IsMP.cent_B (A : Asm c F I) {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) :
    B ⊓ Subgroup.centralizer (M : Set G) = B ⊓ Subgroup.centralizer (F.J u v : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left B (Subgroup.centralizer_le (h.J_le A))
  · obtain ⟨σ', h3, h4⟩ := exists_perm_34 h.ne
    have hM : M = Msg F I (tauC σ' * σ') 0 1 :=
      h.eq A ⟨tauC σ' * σ', 0, 1, by decide, by
        show tauC σ' (σ' 0) = u
        rw [tauC_apply_zero, h3], by
        show tauC σ' (σ' 1) = v
        rw [tauC_apply_one, h4], rfl⟩
    have hR := R_eq_BK F σ'
    rw [h3, h4] at hR
    rw [hR]
    intro x hx
    refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
    rw [hM] at hm
    exact A.Msg_comm_Isg σ' m hm x ((A.cfg σ').K_le hx.2)

omit [Finite G] in
theorem IsMP.line_le (A : Asm c F I) {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) :
    B ⊓ F.J u v ≤ B ⊓ M :=
  inf_le_inf_left B (h.J_le A)

theorem IsMP.ct_single (A : Asm c F I) {u v : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) :
    B = (B ⊓ Subgroup.centralizer (M : Set G)) ⊔ (B ⊓ M) ∧
      (B ⊓ Subgroup.centralizer (M : Set G)).relIndex B = 5 := by
  rw [h.cent_B A]
  refine ⟨?_, relIndex_R F h.ne⟩
  apply le_antisymm
  · calc B = (B ⊓ Subgroup.centralizer (F.J u v : Set G)) ⊔ (B ⊓ F.J u v) :=
          (R_sup_line F h.ne).symm
      _ ≤ _ := sup_le_sup_left (h.line_le A) _
  · exact sup_le inf_le_left inf_le_left

theorem IsMP.ct_pair (A : Asm c F I) {u v u' v' : Fin 5} {M M' : Subgroup G}
    (h : IsMP F I u v M) (h' : IsMP F I u' v' M')
    (hne : ¬ ((u = u' ∧ v = v') ∨ (u = v' ∧ v = u'))) :
    (B ⊓ Subgroup.centralizer ((M ⊔ M' : Subgroup G) : Set G)).relIndex B = 25 := by
  have e : B ⊓ Subgroup.centralizer ((M ⊔ M' : Subgroup G) : Set G) =
      (B ⊓ Subgroup.centralizer (M : Set G)) ⊓ (B ⊓ Subgroup.centralizer (M' : Set G)) := by
    rw [centralizer_sup, inf_inf_distrib_left]
  rw [e, h.cent_B A, h'.cent_B A]
  exact relIndex_R_inf F h.ne h'.ne (F.hyper_ne u v u' v' h.ne h'.ne hne)

theorem IsMP.comm_of (A : Asm c F I) {σ : Equiv.Perm (Fin 5)} {x y : Fin 3} (hxy : x ≠ y)
    {M M' : Subgroup G} (hM : M = Msg F I σ x y) (hM' : IsMP F I (σ 3) (σ 4) M') :
    ∀ m ∈ M', ∀ n ∈ M, m * n = n * m := by
  obtain ⟨τ, x', y', hxy', h1, h2, rfl⟩ := hM'
  rw [hM]
  exact A.Msg_comm hxy hxy' h1 h2

end Pair

end CFSG.RankThree.PartOne.CTP
