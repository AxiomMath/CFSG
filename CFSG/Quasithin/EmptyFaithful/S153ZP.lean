module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.Z391

open CFSG.QuasithinUnique

theorem isInv_iff_of_surj {Λ' Λ : Type*} [Group Λ'] [Group Λ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Λ' Q] [MulDistribMulAction Λ Q] (φ : Λ' → Λ) (hφ : Function.Surjective φ)
    (hact : ∀ (l : Λ') (q : Q), l • q = φ l • q) (J : Subgroup Q) :
    XMod.IsInv Λ' J ↔ XMod.IsInv Λ J := by
  constructor
  · intro h l x hx
    obtain ⟨l', rfl⟩ := hφ l
    rw [← hact]
    exact h l' x hx
  · intro h l' x hx
    rw [hact]
    exact h (φ l') x hx

theorem isIrr_of_surj {Λ' Λ : Type*} [Group Λ'] [Group Λ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Λ' Q] [MulDistribMulAction Λ Q] (φ : Λ' → Λ) (hφ : Function.Surjective φ)
    (hact : ∀ (l : Λ') (q : Q), l • q = φ l • q) {V : Subgroup Q} (hV : XMod.IsIrr Λ V) :
    XMod.IsIrr Λ' V :=
  ⟨(isInv_iff_of_surj φ hφ hact V).2 hV.1, hV.2.1, fun J hJ h1 h2 =>
    hV.2.2 J ((isInv_iff_of_surj φ hφ hact J).1 hJ) h1 h2⟩

section Conj

variable {W : Type*} [CommGroup W]

theorem commSub_map_conj (g : MulAut W) (J : Subgroup W) (A : Subgroup (MulAut W)) :
    commSub (J.map g.toMonoidHom) (A.map (MulAut.conj g).toMonoidHom) =
      (commSub J A).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, w', ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨c₀, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj g).toMonoidHom x, ⟨x, hx, rfl⟩, g w, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]

theorem commIter_map_conj (g : MulAut W) (J : Subgroup W) (A : Subgroup (MulAut W)) (k : ℕ) :
    commIter (J.map g.toMonoidHom) (A.map (MulAut.conj g).toMonoidHom) k =
      (commIter J A k).map g.toMonoidHom := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [commIter]
    rw [ih, commSub_map_conj]

theorem commSeries_map_conj (g : MulAut W) (A : Subgroup (MulAut W)) (k : ℕ) :
    commSeries (A.map (MulAut.conj g).toMonoidHom) k = (commSeries A k).map g.toMonoidHom := by
  unfold commSeries
  rw [← commIter_map_conj]
  congr 1
  exact (Subgroup.map_top_of_surjective _ g.surjective).symm

theorem map_subtype_conj {M : Subgroup (MulAut W)} (A₁ : Subgroup ↥M) (g : ↥M) :
    (A₁.map (MulAut.conj g).toMonoidHom).map M.subtype =
      (A₁.map M.subtype).map (MulAut.conj (g : MulAut W)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

end Conj

theorem isSylowTwoOf_subgroupOf_top {G : Type*} [Group G] {T M : Subgroup G} (h : IsSylowTwoOf T M) :
    IsSylowTwoOf (T.subgroupOf M) (⊤ : Subgroup ↥M) := by
  obtain ⟨hTM, hTp, hidx⟩ := h
  refine ⟨le_top, hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm, ?_⟩
  show ¬ 2 ∣ (T.subgroupOf M).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact hidx

end CFSG.Quasithin.Z391
