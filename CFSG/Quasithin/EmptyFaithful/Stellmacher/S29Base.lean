module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29Mod
public import CFSG.Quasithin.EmptyFaithful.SzF53MConj
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvEdgeCentralizer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S29

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

namespace Sit29

omit [Finite G] in
theorem Zv_conj (g : ↥(H ⊔ M)) (a : Geo H M) :
    conjSub (g : G) (Zv a) = Zv (g • a) := (Zv_smul g a).symm

omit [Finite G] in
theorem hmod_smul (g : ↥(H ⊔ M)) {a : Geo H M}
    (h : IsOrthSec (stab a) ⊥ (Zv a) ∨ IsNatSec (stab a) ⊥ (Zv a)) :
    IsOrthSec (stab (g • a)) ⊥ (Zv (g • a)) ∨ IsNatSec (stab (g • a)) ⊥ (Zv (g • a)) := by
  rw [stab_smul, Zv_smul]
  rcases h with h | h
  · left
    have := IsOrthSec.conj h (g : G)
    rwa [conjSub_bot] at this
  · right
    have := IsNatSec.conj h (g : G)
    rwa [conjSub_bot] at this

theorem n₁ (hs : Sit29 H M S α a₂ a₃ β) : α ∈ nbrs β := hs.adj.symm

theorem n₀ (hs : Sit29 H M S α a₂ a₃ β) : β ∈ nbrs α := hs.adj

theorem swap₁₂ (hs : Sit29 H M S α a₂ a₃ β) : Sit29 H M S a₂ α a₃ β := by
  obtain ⟨g, hg, hgα⟩ := stab_transitive_on_nbrs hs.n₁ hs.n₂
  refine ⟨hs.amalg, hs.h28, hs.h26, hs.b1, SimpleGraph.Adj.symm hs.n₂, ?_, ?_, hs.hz, ?_,
    hs.n₁, hs.n₃, hs.ne₁₂.symm, hs.ne₂₃, hs.ne₁₃⟩
  · rw [← hgα, vtype_smul]; exact hs.vα
  · rw [← hgα, bAt_smul]; exact hs.bα
  · rw [← hgα]; exact hmod_smul g hs.hmod

theorem swap₂₃ (hs : Sit29 H M S α a₂ a₃ β) : Sit29 H M S α a₃ a₂ β :=
  ⟨hs.amalg, hs.h28, hs.h26, hs.b1, hs.adj, hs.vα, hs.bα, hs.hz, hs.hmod, hs.n₃, hs.n₂,
    hs.ne₁₃, hs.ne₁₂, hs.ne₂₃.symm⟩

theorem vβ (hs : Sit29 H M S α a₂ a₃ β) : vtype β = true := by
  have h := vtype_ne_of_adj hs.adj
  rw [hs.vα] at h
  cases hv : vtype β
  · exact absurd hv.symm h
  · rfl

theorem nbrs_eq (hs : Sit29 H M S α a₂ a₃ β) : ∀ w ∈ nbrs β, w = α ∨ w = a₂ ∨ w = a₃ := by
  obtain ⟨ν, hν, hνα, hνa, hall⟩ := exists_third_nbr hs.amalg hs.vβ hs.n₁ hs.n₂ hs.ne₁₂
  have h3 : a₃ = ν := by
    rcases hall a₃ hs.n₃ with h | h | h
    · exact absurd h.symm hs.ne₁₃
    · exact absurd h.symm hs.ne₂₃
    · exact h
  intro w hw
  rcases hall w hw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.trans h3.symm))

theorem smul_nbr (_hs : Sit29 H M S α a₂ a₃ β) (g : ↥(H ⊔ M)) (hg : (g : G) ∈ stab β)
    {a : Geo H M} (ha : a ∈ nbrs β) : g • a ∈ nbrs β := by
  have := (smul_mem_nbrs_iff g (l := β) (δ := a)).mpr ha
  rwa [smul_eq_of_mem_stab hg] at this

theorem mod₁ (hs : Sit29 H M S α a₂ a₃ β) :
    ModFacts (stab α) (stab α ⊓ stab β) (Zv α) :=
  modFacts_of (sylow_stab_inf_left hs.amalg hs.n₀) (quot_stab_five hs.amalg hs.vα) hs.hmod

theorem mod₂ (hs : Sit29 H M S α a₂ a₃ β) :
    ModFacts (stab a₂) (stab a₂ ⊓ stab β) (Zv a₂) := hs.swap₁₂.mod₁

theorem Zv_le_Qv_right (hs : Sit29 H M S α a₂ a₃ β) : Zv α ≤ Qv β := by
  refine Zv_le_Qv_of_dist_lt ?_
  rw [dist_eq_one_iff_adj.mpr hs.adj, hs.bα]
  exact hs.b1

theorem sup_Qv (hs : Sit29 H M S α a₂ a₃ β) : Qv α ⊔ Qv β = stab α ⊓ stab β :=
  hs.h28 hs.b1 α β hs.adj hs.bα

theorem relIndex_Qv_right (hs : Sit29 H M S α a₂ a₃ β) :
    (Qv β).relIndex (stab α ⊓ stab β) = 2 := by
  rw [inf_comm]
  exact relIndex_Qv_inf_true hs.amalg hs.n₁ hs.vβ

theorem exists_q (hs : Sit29 H M S α a₂ a₃ β) : ∃ q ∈ Qv α, q ∉ Qv β := by
  by_contra hcon
  push Not at hcon
  have hle : Qv α ≤ Qv β := fun q hq => hcon q hq
  have h1 : stab α ⊓ stab β = Qv β := by rw [← hs.sup_Qv, sup_eq_right.mpr hle]
  have h2 := hs.relIndex_Qv_right
  rw [h1, Subgroup.relIndex_self] at h2
  omega

theorem mem_Qv_of_fixes (hs : Sit29 H M S α a₂ a₃ β) (g : ↥(H ⊔ M)) (hg : (g : G) ∈ stab β)
    (hfix : ∀ w ∈ nbrs β, g • w = w) : (g : G) ∈ Qv β := by
  rw [Qv_eq_iInf hs.amalg β]
  exact Subgroup.mem_iInf.mpr fun w => Subgroup.mem_iInf.mpr fun hw =>
    ⟨hg, mem_stab_of_smul_eq (hfix w hw)⟩

theorem smul_swap (hs : Sit29 H M S α a₂ a₃ β) (g : ↥(H ⊔ M)) (hα : (g : G) ∈ stab α)
    (hβ : (g : G) ∈ stab β) (hq : (g : G) ∉ Qv β) : g • a₂ = a₃ ∧ g • a₃ = a₂ := by
  have hgα : g • α = α := smul_eq_of_mem_stab hα
  have hinj : ∀ x y : Geo H M, g • x = g • y → x = y := fun x y h => smul_left_cancel g h
  have h2 := hs.smul_nbr g hβ hs.n₂
  have h3 := hs.smul_nbr g hβ hs.n₃
  have h2ne : g • a₂ ≠ α := fun h => hs.ne₁₂ (hinj _ _ (h.trans hgα.symm)).symm
  have h3ne : g • a₃ ≠ α := fun h => hs.ne₁₃ (hinj _ _ (h.trans hgα.symm)).symm
  have hne23 : g • a₂ ≠ g • a₃ := fun h => hs.ne₂₃ (hinj _ _ h)
  have key : g • a₂ = a₃ := by
    rcases hs.nbrs_eq _ h2 with h | h | h
    · exact absurd h h2ne
    · exfalso
      apply hq
      refine hs.mem_Qv_of_fixes g hβ fun w hw => ?_
      rcases hs.nbrs_eq w hw with hw' | hw' | hw'
      · rw [hw']; exact hgα
      · rw [hw']; exact h
      · rw [hw']
        rcases hs.nbrs_eq _ h3 with h' | h' | h'
        · exact absurd h' h3ne
        · exact absurd (h.trans h'.symm) hne23
        · exact h'
    · exact h
  refine ⟨key, ?_⟩
  rcases hs.nbrs_eq _ h3 with h' | h' | h'
  · exact absurd h' h3ne
  · exact h'
  · exact absurd (key.trans h'.symm) hne23

theorem Zv_conj_swap (hs : Sit29 H M S α a₂ a₃ β) {g : G} (hα : g ∈ stab α) (hβ : g ∈ stab β)
    (hq : g ∉ Qv β) : conjSub g (Zv a₂) = Zv a₃ ∧ conjSub g (Zv a₃) = Zv a₂ := by
  have hg : g ∈ H ⊔ M := stab_le β hβ
  obtain ⟨h2, h3⟩ := hs.smul_swap ⟨g, hg⟩ hα hβ hq
  have e2 := Zv_conj (⟨g, hg⟩ : ↥(H ⊔ M)) a₂
  have e3 := Zv_conj (⟨g, hg⟩ : ↥(H ⊔ M)) a₃
  rw [h2] at e2
  rw [h3] at e3
  exact ⟨e2, e3⟩

theorem R_eq₁ (hs : Sit29 H M S α a₂ a₃ β) : Zv α ⊓ Zv a₂ = Zv α ⊓ Zv a₃ := by
  obtain ⟨q, hqα, hqβ⟩ := hs.exists_q
  have hqs : q ∈ stab β := Qv_le_stab_of_mem_nbrs hs.amalg hs.n₀ hqα
  have hqa : q ∈ stab α := pCoreOf_le 2 _ hqα
  have hconj := hs.Zv_conj_swap hqa hqs hqβ
  have hnorm : q ∈ Subgroup.normalizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hs.amalg α hx.1).2 q hqα).symm
  have h1 := conjSub_eq_of_mem_normalizer hnorm
  rw [conjSub_inf, conjSub_eq_of_mem_normalizer (stab_le_normalizer_Zv hs.amalg α hqa),
    hconj.1] at h1
  exact h1.symm

theorem R_eq₂ (hs : Sit29 H M S α a₂ a₃ β) : Zv α ⊓ Zv a₂ = Zv a₂ ⊓ Zv a₃ := by
  have h := hs.swap₁₂.R_eq₁
  rwa [inf_comm] at h

theorem inf_eq_R (hs : Sit29 H M S α a₂ a₃ β) {x y : Geo H M} (hx : x ∈ nbrs β)
    (hy : y ∈ nbrs β) (hxy : x ≠ y) : Zv x ⊓ Zv y = Zv α ⊓ Zv a₂ := by
  rcases hs.nbrs_eq x hx with h1 | h1 | h1 <;> rcases hs.nbrs_eq y hy with h2 | h2 | h2 <;>
    subst h1 <;> subst h2
  · exact absurd rfl hxy
  · rfl
  · exact hs.R_eq₁.symm
  · rw [inf_comm]
  · exact absurd rfl hxy
  · exact hs.R_eq₂.symm
  · rw [inf_comm]; exact hs.R_eq₁.symm
  · rw [inf_comm]; exact hs.R_eq₂.symm
  · exact absurd rfl hxy

theorem R_normal (hs : Sit29 H M S α a₂ a₃ β) :
    stab β ≤ Subgroup.normalizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) := by
  intro g hg
  have hgH : g ∈ H ⊔ M := stab_le β hg
  have h1 : conjSub g (Zv α ⊓ Zv a₂) = Zv α ⊓ Zv a₂ := by
    have e1 := Zv_conj (⟨g, hgH⟩ : ↥(H ⊔ M)) α
    have e2 := Zv_conj (⟨g, hgH⟩ : ↥(H ⊔ M)) a₂
    rw [conjSub_inf]
    refine Eq.trans (congrArg₂ (· ⊓ ·) e1 e2) ?_
    exact hs.inf_eq_R (hs.smul_nbr ⟨g, hgH⟩ hg hs.n₁) (hs.smul_nbr ⟨g, hgH⟩ hg hs.n₂)
      (fun h => hs.ne₁₂ (smul_left_cancel (⟨g, hgH⟩ : ↥(H ⊔ M)) h))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have := conj_mem_conjSub_iff (g := g) (y := y) (C := Zv α ⊓ Zv a₂)
  rw [h1] at this
  exact this.symm

theorem Zv_right_le (hs : Sit29 H M S α a₂ a₃ β) : Zv β ≤ Zv α :=
  (Zv_eq_omegaOneCenter_inf hs.amalg hs.n₁ hs.hz).2

theorem Zv_right_le_R (hs : Sit29 H M S α a₂ a₃ β) : Zv β ≤ Zv α ⊓ Zv a₂ :=
  le_inf hs.Zv_right_le hs.swap₁₂.Zv_right_le

theorem card_Zv_right (hs : Sit29 H M S α a₂ a₃ β) : Nat.card (Zv β) = 2 := by
  have hS := sylow_stab_inf_left hs.amalg hs.n₀
  have hcen := EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_edge_eq
    hs.amalg hs.adj hs.hz
  rcases hs.hmod with h | h
  · have := IsModelSec.card_fix_sylow (Or.inl rfl) h hS
    rwa [hcen] at this
  · have := IsModelSec.card_fix_sylow (Or.inr rfl) h hS
    rwa [hcen] at this

theorem card_Zv (hs : Sit29 H M S α a₂ a₃ β) : Nat.card (Zv α) = 16 := hs.mod₁.card_Z

theorem not_Zv_le (hs : Sit29 H M S α a₂ a₃ β) : ¬ Zv α ≤ Zv a₂ := by
  intro h
  have hR : Zv α ⊓ Zv a₂ = Zv α := inf_eq_left.mpr h
  have hβ : stab β ≤ Subgroup.normalizer (Zv α : Set G) := by
    have := hs.R_normal
    rwa [hR] at this
  have hU : Zv α ≤ stab α ⊓ stab β :=
    le_inf ((Zv_le_Qv hs.amalg α).trans (pCoreOf_le 2 _))
      (hs.Zv_le_Qv_right.trans (pCoreOf_le 2 _))
  exact Zv_ne_bot hs.amalg α
    (eq_bot_of_normalizes_both hs.amalg hs.adj hU (stab_le_normalizer_Zv hs.amalg α) hβ)

theorem card_R (hs : Sit29 H M S α a₂ a₃ β) :
    Nat.card ↥(Zv α ⊓ Zv a₂) = 2 ∨ Nat.card ↥(Zv α ⊓ Zv a₂) = 4 ∨
      Nat.card ↥(Zv α ⊓ Zv a₂) = 8 := by
  have hRZ : Zv α ⊓ Zv a₂ ≤ Zv α := inf_le_left
  have h16 := hs.card_Zv
  have h2 := hs.card_Zv_right
  have hdvd16 : Nat.card ↥(Zv α ⊓ Zv a₂) ∣ 16 := h16 ▸ Subgroup.card_dvd_of_le hRZ
  have hdvd2 : 2 ∣ Nat.card ↥(Zv α ⊓ Zv a₂) := h2 ▸ Subgroup.card_dvd_of_le hs.Zv_right_le_R
  have hne : Nat.card ↥(Zv α ⊓ Zv a₂) ≠ 16 := by
    intro h
    have heq : Zv α ⊓ Zv a₂ = Zv α := Subgroup.eq_of_le_of_card_ge hRZ (by rw [h, h16])
    exact hs.not_Zv_le (heq ▸ inf_le_right)
  have hle : Nat.card ↥(Zv α ⊓ Zv a₂) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd16
  generalize Nat.card ↥(Zv α ⊓ Zv a₂) = k at *
  interval_cases k <;> omega

theorem R_eq_right (hs : Sit29 H M S α a₂ a₃ β) (h : Nat.card ↥(Zv α ⊓ Zv a₂) = 2) :
    Zv α ⊓ Zv a₂ = Zv β :=
  (Subgroup.eq_of_le_of_card_ge hs.Zv_right_le_R (by rw [h, hs.card_Zv_right])).symm

theorem Zv_le_Qv_other (hs : Sit29 H M S α a₂ a₃ β) (hb : 2 < bMin H M) :
    Zv α ≤ Qv a₂ := by
  refine Zv_le_Qv_of_dist_lt ?_
  have h1 : dist α β = 1 := dist_eq_one_iff_adj.mpr hs.adj
  have h2 : dist β a₂ = 1 :=
    dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj β a₂ from hs.n₂)
  have h3 := dist_triangle (rfl : H ⊔ M = H ⊔ M) α β a₂
  rw [hs.bα]
  omega

end Sit29

end F53.Stellmacher.S29

end CFSG.Quasithin
