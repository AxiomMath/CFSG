module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61TwoCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Idx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P61

open P514

theorem exists_two_trans (F : FanTree Γ G) {o a : V} (hoa : Γ.Adj o a) (hv5 : valence Γ o = 5)
    (h4 : (nbrStab Γ G o).relIndex (MulAction.stabilizer G o ⊓ MulAction.stabilizer G a) = 4)
    {b c : V} (hb : Γ.Adj o b) (hc : Γ.Adj o c) (hba : b ≠ a) (hca : c ≠ a) :
    ∃ g ∈ MulAction.stabilizer G o ⊓ MulAction.stabilizer G a, g • b = c := by
  classical
  set H : Subgroup G := MulAction.stabilizer G o ⊓ MulAction.stabilizer G a with hH
  set S : Set V := {w | Γ.Adj o w ∧ w ≠ a} with hS
  have hstab : MulAction.stabilizer H b = (nbrStab Γ G o).subgroupOf H := by
    ext e
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro he
      have hea : (e : G) • a = a := MulAction.mem_stabilizer_iff.1 e.2.2
      have heb : (e : G) • b = b := he
      exact F.fix_two_nbrs hb hoa hba heb hea
    · intro he
      exact mem_nbrStab.1 he b hb
  have hidx : (MulAction.orbit H b).ncard = 4 := by
    rw [← MulAction.index_stabilizer H b, hstab]
    exact h4
  have hsub : MulAction.orbit H b ⊆ S := by
    rintro _ ⟨e, rfl⟩
    have heo : (e : G) • o = o := MulAction.mem_stabilizer_iff.1 e.2.1
    have hea : (e : G) • a = a := MulAction.mem_stabilizer_iff.1 e.2.2
    refine ⟨?_, fun h => hba (MulAction.injective (e : G) ((show (e : G) • b = (e : G) • a by
      rw [hea]; exact h).trans rfl))⟩
    have := (F.adj_smul (e : G) o b).2 hb
    rwa [heo] at this
  have hSfin : S.Finite := by
    refine (finite_nbr hv5).subset fun w hw => hw.1
  have hScard : S.ncard = 4 := by
    have h1 : S = Γ.neighborSet o \ {a} := by
      ext w
      simp [hS, SimpleGraph.mem_neighborSet]
    rw [h1, Set.ncard_sdiff_singleton_of_mem (show a ∈ Γ.neighborSet o from hoa),
      ncard_nbr hv5]
  have heq : MulAction.orbit H b = S :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hidx, hScard]) hSfin
  have hcS : c ∈ MulAction.orbit H b := by
    rw [heq]
    exact ⟨hc, hca⟩
  obtain ⟨e, he⟩ := hcS
  exact ⟨(e : G), e.2, he⟩

theorem r2_f20 (F : FanTree Γ G) {z : G} {α o : V} (C : LblCtx Γ z α o)
    (h4 : (nbrStab Γ G o).relIndex (MulAction.stabilizer G o ⊓ MulAction.stabilizer G α) = 4)
    {u₁ : V} (hu₁ : Γ.Adj o u₁) (hne : u₁ ≠ α) (hK : Lb z α u₁ ∈ nbrStab Γ G α)
    {v₂ v₃ : V} (h₂ : Γ.Adj α v₂) (h₃ : Γ.Adj v₂ v₃) (hn₂ : α ≠ v₃) {t : G}
    (ht2 : t * t = 1) (hto : t • o = o) (htK : t ∉ nbrStab Γ G o) (ht₁ : t • α = α)
    (htc : ∀ h : G, h • v₂ = v₂ → h • v₃ = v₃ → h * t = t * h) : False := by
  refine r2_core F C C.adj.symm h₂ h₃ hn₂ ht2 hto htK ht₁ htc fun u hu => ?_
  by_cases hua : u = α
  · rw [hua, Lb_self C.cinv]
    exact P73.ballStab_le_nbrStab F α C.ball
  · obtain ⟨g, hg, hgu⟩ := exists_two_trans F C.adj.symm C.v5 h4 hu₁ hu hne hua
    have hgα : g • α = α := MulAction.mem_stabilizer_iff.1 hg.2
    have := P58.conj_mem_nbrStab F hgα hK
    rw [Lb_conj C.cinv (C.conj_ex F hu₁) g, hgu] at this
    exact this

end P61

end CFSG.Quasithin.Fan86
