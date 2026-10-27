module

public import CFSG.Quasithin.Background.ShultG53CoverCU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv


theorem cover_five_dim (k : Fin 2) :
    ∃ (C : Md ↥(alternatingGroup (Fin 6))) (π : ↥(Nk k 0) →+ C.carrier), Function.Surjective π ∧
      (∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2) ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
        π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = C.ρ g (π n)) ∧
      C.IsFiveDimCover (Mk k) := by
  obtain ⟨C, π, hs, hk, he⟩ := exists_quot_md (permRep (Mk k)) (N0_inv k) (N2_inv k)
    ((N2_le_N1 k).trans (N1_le_N0 k))
  exact ⟨C, π, hs, hk, he, isFiveDimCover_of_quot k C π hs hk he⟩

theorem part6_model (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6))) (w : W.carrier)
    (hw0 : w ≠ 0) (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hgen : AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g w) = ⊤)
    (hline : Nat.card ↥(AddSubgroup.closure
      (Set.range fun g : ↥(Hl k) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w)) = 4) :
    W.Iso (Mk k) ∨ W.IsFiveDimCover (Mk k) := by
  obtain ⟨π, hs, he, hN2⟩ := cover_theorem k W w hw0 hHx hgen hline
  let K : AddSubgroup Fn := π.ker.map (Nk k 0).subtype
  have hKmem : ∀ y : ↥(Nk k 0), (y : Fn) ∈ K ↔ π y = 0 := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      exact AddMonoidHom.mem_ker.mp hy'
    · intro hy
      exact ⟨y, AddMonoidHom.mem_ker.mpr hy, rfl⟩
  have hK0 : K ≤ Nk k 0 := AddSubgroup.map_subtype_le _
  have hKinv : InvSub (permAct (Mk k)) K := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : π ⟨permAct (Mk k) g y, N0_inv k g y y.2⟩ = 0 := by
      rw [he, AddMonoidHom.mem_ker.mp hy, map_zero]
    exact (hKmem ⟨permAct (Mk k) g y, N0_inv k g y y.2⟩).mpr h1
  have hN2K : Nk k 2 ≤ K := by
    intro x hx
    have hx0 : x ∈ Nk k 0 := N1_le_N0 k (N2_le_N1 k hx)
    exact (hKmem ⟨x, hx0⟩).mpr (hN2 ⟨x, hx0⟩ hx)
  obtain ⟨n, hn5, hKn⟩ := eq_chain_of_invSub (Nk k) (chain_isTop k) (Nk_five k) hKinv hK0
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    apply hw0
    have hzero : ∀ y : ↥(Nk k 0), π y = 0 := fun y => (hKmem y).mp (by rw [hKn]; exact y.2)
    obtain ⟨y, hy⟩ := hs w
    rw [← hy]
    exact hzero y
  · left
    have hΦs : Function.Surjective ((Phi).comp (Nk k 0).subtype) := fun v => by
      obtain ⟨y, hy⟩ := Phi_surj_N0 k v
      exact ⟨y, hy⟩
    have hkΦ : ∀ n : ↥(Nk k 0), π n = 0 ↔ ((Phi).comp (Nk k 0).subtype) n = 0 := by
      intro n
      rw [← hKmem, hKn]
      show (n : Fn) ∈ Nk k 1 ↔ Phi (n : Fn) = 0
      constructor
      · intro h
        exact AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp h).2
      · intro h
        exact AddSubgroup.mem_inf.mpr ⟨n.2, AddMonoidHom.mem_ker.mpr h⟩
    refine iso_of_equivariant_surj (M₁ := W) (M₂ := Mk k)
      (fun g n => ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩) π ((Phi).comp (Nk k 0).subtype) hs hΦs
      hkΦ he ?_
    intro g n
    exact phi_equiv k g n
  · right
    refine isFiveDimCover_of_quot k W π hs (fun n => ?_) he
    rw [← hKmem, hKn]
  · exfalso
    have h := AddSubgroup.card_le_of_le (show Nk k 2 ≤ Nk k 3 from hKn ▸ hN2K)
    rw [card_N2, card_N3] at h
    norm_num at h
  · exfalso
    have h := AddSubgroup.card_le_of_le (show Nk k 2 ≤ Nk k 4 from hKn ▸ hN2K)
    rw [card_N2, card_N4] at h
    norm_num at h
  · exfalso
    have h := AddSubgroup.card_le_of_le (show Nk k 2 ≤ Nk k 5 from hKn ▸ hN2K)
    rw [card_N2, Nk_five, AddSubgroup.card_bot] at h
    norm_num at h

end CFSG.Quasithin.ShultG53
