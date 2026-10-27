module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Hyp
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] {S : Subgroup G}

structure OmSet (S : Subgroup G) (e : ↥S ≃* Multiplicative F6) (ψ : ↥(Nor S) →* OmG) : Prop where
  surj : Function.Surjective ψ
  ker : ψ.ker = S.subgroupOf (Nor S)
  equiv : ∀ (n : G) (hn : n ∈ Nor S) (x : ↥S), ∃ hx : n * (x : G) * n⁻¹ ∈ S,
    e ⟨n * (x : G) * n⁻¹, hx⟩ =
      Multiplicative.ofAdd ((ψ ⟨n, hn⟩ : F6 ≃ₗ[ZMod 2] F6) (Multiplicative.toAdd (e x)))
  hq : ∀ x : ↥S, (x : G) ≠ 1 →
    (qMinus (Multiplicative.toAdd (e x)) = 1 ↔ Op 2 (Cen (x : G)) = S)

theorem exists_omSet {e : ↥S ≃* Multiplicative F6} (h : FF84OmegaDataFor S e) :
    ∃ ψ, OmSet S e ψ := by
  obtain ⟨ψ, h1, h2, h3, h4⟩ := h
  exact ⟨ψ, ⟨h1, h2, h3, h4⟩⟩

variable {e : ↥S ≃* Multiplicative F6} {ψ : ↥(Nor S) →* OmG}

theorem toAdd_e_eq_iff (x y : ↥S) :
    Multiplicative.toAdd (e x) = Multiplicative.toAdd (e y) ↔ x = y :=
  Multiplicative.toAdd.injective.eq_iff.trans e.injective.eq_iff

theorem OmSet.smul_eq (H : OmSet S e ψ) (n : ↥(Nor S)) (x : ↥S) :
    ψ n • Multiplicative.toAdd (e x) =
      Multiplicative.toAdd (e ⟨(n : G) * (x : G) * (n : G)⁻¹, (n.2 (x : G)).mp x.2⟩) := by
  obtain ⟨hx, h⟩ := H.equiv n n.2 x
  have := congrArg Multiplicative.toAdd h
  rw [toAdd_ofAdd] at this
  exact this.symm

theorem OmSet.comm_iff (H : OmSet S e ψ) (n : ↥(Nor S)) (x : ↥S) :
    (n : G) * (x : G) = (x : G) * (n : G) ↔
      ψ n • Multiplicative.toAdd (e x) = Multiplicative.toAdd (e x) := by
  rw [H.smul_eq, toAdd_e_eq_iff]
  constructor
  · intro h
    refine Subtype.ext ?_
    show (n : G) * (x : G) * (n : G)⁻¹ = (x : G)
    rw [h]
    group
  · intro h
    have := congrArg Subtype.val h
    have h2 : (n : G) * (x : G) * (n : G)⁻¹ = (x : G) := this
    exact mul_inv_eq_iff_eq_mul.1 h2

theorem OmSet.psi_eq_one_iff (H : OmSet S e ψ) (n : ↥(Nor S)) : ψ n = 1 ↔ (n : G) ∈ S := by
  rw [← MonoidHom.mem_ker, H.ker, Subgroup.mem_subgroupOf]

theorem cenS_pair (a c : G) :
    CenS (Subgroup.closure ({a, c} : Set G)) = Subgroup.centralizer ({a, c} : Set G) :=
  Subgroup.centralizer_closure _

theorem OmSet.mem_cen_pair_iff (H : OmSet S e ψ) (n : ↥(Nor S)) (s t : ↥S) :
    ((n : G) ∈ CenS (Subgroup.closure {(s : G), (t : G)})) ↔
      (ψ n • Multiplicative.toAdd (e s) = Multiplicative.toAdd (e s) ∧
        ψ n • Multiplicative.toAdd (e t) = Multiplicative.toAdd (e t)) := by
  rw [cenS_pair, Subgroup.mem_centralizer_iff, ← H.comm_iff, ← H.comm_iff]
  constructor
  · intro h
    exact ⟨(h _ (by simp)).symm, (h _ (by simp)).symm⟩
  · rintro ⟨h1, h2⟩ y hy
    rcases hy with rfl | hy
    · exact h1.symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h2.symm

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
