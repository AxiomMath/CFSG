module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops
public import CFSG.RankThree.GF2n.Smith81.S81D6Basic
public import CFSG.RankThree.GF2n.Smith81.S81E7Hwl
public import CFSG.RankThree.GF2n.Smith81.S81XE7Def
public import CFSG.RankThree.GF2n.Smith81.S81XE7Grp

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6Spin


variable {K : Type} [Field K]

@[expose] def LamG (K : Type) [Field K] : Subgroup (Gp K) :=
  (Lam K).comap (e7Data_valid.minGroup K).subtype

@[expose] def ULG (K : Type) [Field K] : Subgroup (Gp K) :=
  (UL K).comap (e7Data_valid.minGroup K).subtype

theorem mem_LamG {g : Gp K} : g ∈ LamG K ↔ (g : (Module.End K (V K))ˣ) ∈ Lam K := Iff.rfl

theorem mem_ULG {g : Gp K} : g ∈ ULG K ↔ (g : (Module.End K (V K))ˣ) ∈ UL K := Iff.rfl

@[expose] def IndW (g : Gp K) (x : W K ≃ₗ[K] W K) : Prop :=
  ∀ w : W K, emb K (x w) = endoE g (emb K w)

theorem IndW.one : IndW (1 : Gp K) 1 := fun _ => rfl

theorem IndW.mul {g g' : Gp K} {x x' : W K ≃ₗ[K] W K} (h : IndW g x) (h' : IndW g' x') :
    IndW (g * g') (x * x') := fun w => by
  show emb K (x (x' w)) = endoE g (endoE g' (emb K w))
  rw [h, h']

theorem IndW.inv {g : Gp K} {x : W K ≃ₗ[K] W K} (h : IndW g x) : IndW g⁻¹ x⁻¹ := fun w => by
  have h1 := h (x⁻¹ w)
  have h2 : x (x⁻¹ w) = w := by
    show (x * x⁻¹) w = w
    rw [mul_inv_cancel]
    rfl
  rw [h2] at h1
  rw [h1]
  show emb K (x⁻¹ w) = endoE g⁻¹ (endoE g (emb K (x⁻¹ w)))
  rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]

theorem IndW.unique {g : Gp K} {x x' : W K ≃ₗ[K] W K} (h : IndW g x) (h' : IndW g x') : x = x' :=
  LinearEquiv.ext fun w => emb_injective ((h w).trans (h' w).symm)

theorem indW_one_iff {x : W K ≃ₗ[K] W K} : IndW (1 : Gp K) x ↔ x = 1 :=
  ⟨fun h => h.unique IndW.one, fun h => h ▸ IndW.one⟩

theorem exists_indW [CharP K 2] {g : Gp K} (hg : g ∈ LamG K) : ∃ x : W K ≃ₗ[K] W K, IndW g x := by
  refine ⟨vAut0 K (resV0 K ⟨(g : (Module.End K (V K))ˣ), hg⟩), fun w => ?_⟩
  exact resV0_induces ⟨(g : (Module.End K (V K))ˣ), hg⟩ w

theorem mem_EAut0_iff [CharP K 2] {x : W K ≃ₗ[K] W K} :
    x ∈ EAut0 K ↔ ∃ g ∈ LamG K, IndW g x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨l, rfl⟩ := mem_LamW_iff.1 hy
    exact ⟨⟨l.1, Lam_le_E l.2⟩, l.2, fun w => resV0_induces l w⟩
  · rintro ⟨g, hg, h⟩
    refine ⟨resV0 K ⟨(g : (Module.End K (V K))ˣ), hg⟩, mem_LamW_iff.2 ⟨_, rfl⟩, ?_⟩
    exact IndW.unique (fun w => resV0_induces ⟨(g : (Module.End K (V K))ˣ), hg⟩ w) h

end CFSG.RankThree.GF2n.Smith81.D6X
