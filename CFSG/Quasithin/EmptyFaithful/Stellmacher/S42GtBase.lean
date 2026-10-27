module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1Tri
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.SzF53MConj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S42Gt

open CosetGeom F53 S42B1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

structure Sit (H M S : Subgroup G) (α a₂ a₃ β : Geo H M) : Prop where
  amalg : F53Amalgam H M S
  h28 : Hss28At H M
  b1 : 1 < bMin H M
  adj : (graph (H ⊔ M) H M).Adj α β
  vα : vtype α = false
  bα : bAt α = bMin H M
  hz : Zv β ≤ centerOf (stab β)
  tri : Tri β α a₂ a₃

namespace Sit

theorem n₀ (hs : Sit H M S α a₂ a₃ β) : β ∈ nbrs α := hs.adj

theorem n₁ (hs : Sit H M S α a₂ a₃ β) : α ∈ nbrs β := hs.tri.ha

theorem vβ (hs : Sit H M S α a₂ a₃ β) : vtype β = true := by
  have h := vtype_ne_of_adj hs.adj
  rw [hs.vα] at h
  cases hv : vtype β
  · exact absurd hv.symm h
  · rfl

theorem swap₁₂ (hs : Sit H M S α a₂ a₃ β) : Sit H M S a₂ α a₃ β := by
  have hv₂ : vtype a₂ = false := vtype_false_of_nbr hs.vβ hs.tri.hb
  have hv := hs.vα.trans hv₂.symm
  exact ⟨hs.amalg, hs.h28, hs.b1, (hs.tri.hb : (graph (H ⊔ M) H M).Adj β a₂).symm, hv₂,
    (bAt_eq_of_vtype_eq hv.symm).trans hs.bα, hs.hz, hs.tri.swap₁₂⟩

theorem vtype₂ (hs : Sit H M S α a₂ a₃ β) : vtype a₂ = false :=
  vtype_false_of_nbr hs.vβ hs.tri.hb

theorem sup_Qv (hs : Sit H M S α a₂ a₃ β) : Qv α ⊔ Qv β = stab α ⊓ stab β :=
  hs.h28 hs.b1 α β hs.adj hs.bα

theorem exists_q (hs : Sit H M S α a₂ a₃ β) : ∃ q ∈ Qv α, q ∉ Qv β := by
  by_contra hcon
  push Not at hcon
  have hle : Qv α ≤ Qv β := fun q hq => hcon q hq
  have h1 : stab α ⊓ stab β = Qv β := by rw [← hs.sup_Qv, sup_eq_right.mpr hle]
  have h2 : (Qv β).relIndex (stab α ⊓ stab β) = 2 := by
    rw [inf_comm]
    exact relIndex_Qv_inf_true hs.amalg hs.n₁ hs.vβ
  rw [h1, Subgroup.relIndex_self] at h2
  omega

theorem R_eq₁ (hs : Sit H M S α a₂ a₃ β) : Zv α ⊓ Zv a₂ = Zv α ⊓ Zv a₃ := by
  obtain ⟨q, hqα, hqβ⟩ := hs.exists_q
  have hqs : q ∈ stab β := Qv_le_stab_of_mem_nbrs hs.amalg hs.n₀ hqα
  have hqa : q ∈ stab α := pCoreOf_le 2 _ hqα
  have hg : q ∈ H ⊔ M := stab_le β hqs
  obtain ⟨h2, -⟩ := hs.tri.swap hs.amalg (g := ⟨q, hg⟩) hqs (smul_eq_of_mem_stab hqa) hqβ
  have e2 : conjSub q (Zv a₂) = Zv a₃ := by
    have := (Zv_smul (⟨q, hg⟩ : ↥(H ⊔ M)) a₂).symm
    rwa [h2] at this
  have hnorm : q ∈ Subgroup.normalizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hs.amalg α hx.1).2 q hqα).symm
  have h1 := conjSub_eq_of_mem_normalizer hnorm
  rw [conjSub_inf, conjSub_eq_of_mem_normalizer (stab_le_normalizer_Zv hs.amalg α hqa), e2] at h1
  exact h1.symm

theorem R_eq₂ (hs : Sit H M S α a₂ a₃ β) : Zv α ⊓ Zv a₂ = Zv a₂ ⊓ Zv a₃ := by
  have h := hs.swap₁₂.R_eq₁
  rwa [inf_comm] at h

theorem inf_eq_R (hs : Sit H M S α a₂ a₃ β) {x y : Geo H M} (hx : x ∈ nbrs β)
    (hy : y ∈ nbrs β) (hxy : x ≠ y) : Zv x ⊓ Zv y = Zv α ⊓ Zv a₂ := by
  rcases hs.tri.all x hx with h1 | h1 | h1 <;> rcases hs.tri.all y hy with h2 | h2 | h2 <;>
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

theorem R_normal (hs : Sit H M S α a₂ a₃ β) :
    stab β ≤ Subgroup.normalizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) := by
  intro g hg
  have hgH : g ∈ H ⊔ M := stab_le β hg
  have h1 : conjSub g (Zv α ⊓ Zv a₂) = Zv α ⊓ Zv a₂ := by
    have e1 := (Zv_smul (⟨g, hgH⟩ : ↥(H ⊔ M)) α).symm
    have e2 := (Zv_smul (⟨g, hgH⟩ : ↥(H ⊔ M)) a₂).symm
    rw [conjSub_inf]
    refine Eq.trans (congrArg₂ (· ⊓ ·) e1 e2) ?_
    exact hs.inf_eq_R (smul_mem_nbrs_of_mem_stab hg hs.n₁)
      (smul_mem_nbrs_of_mem_stab hg hs.tri.hb)
      (fun h => hs.tri.hab (MulAction.injective (⟨g, hgH⟩ : ↥(H ⊔ M)) h))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have := conj_mem_conjSub_iff (g := g) (y := y) (C := Zv α ⊓ Zv a₂)
  rw [h1] at this
  exact this.symm

theorem not_Zv_le (hs : Sit H M S α a₂ a₃ β) : ¬ Zv α ≤ Zv a₂ := by
  intro h
  have hR : Zv α ⊓ Zv a₂ = Zv α := inf_eq_left.mpr h
  have hβ : stab β ≤ Subgroup.normalizer (Zv α : Set G) := by
    have := hs.R_normal
    rwa [hR] at this
  have hU : Zv α ≤ stab α ⊓ stab β := by
    have := Zv_le_edge hs.amalg hs.n₁
    rw [inf_comm] at this
    exact this
  exact Zv_ne_bot hs.amalg α
    (eq_bot_of_normalizes_both hs.amalg hs.adj hU (stab_le_normalizer_Zv hs.amalg α) hβ)

end Sit

end F53.Stellmacher.S42Gt

end CFSG.Quasithin
