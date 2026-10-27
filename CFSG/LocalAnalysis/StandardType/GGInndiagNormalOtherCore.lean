module

public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Core

variable {M : Type} [Group M] {H : Subgroup M}

@[expose] def IsConjOn (H : Subgroup M) (φ : MulAut (LargeEvenCenterQuot H)) (x : M) : Prop :=
  (∀ h ∈ H, x * h * x⁻¹ ∈ H) ∧
    ∀ (h : H) (hh : x * h * x⁻¹ ∈ H), φ (LargeEvenCenterMk H h) = LargeEvenCenterMk H ⟨_, hh⟩

@[expose] def DiagNF {ι : Type*} (H : Subgroup M) (D : ι → M) : Prop :=
  ∀ (α : MulAut H) (a : ι), (∀ h ∈ H, D a * h * (D a)⁻¹ ∈ H) →
    (∀ h ∈ H, (D a)⁻¹ * h * D a ∈ H) →
    ∃ g ∈ H, ∃ a' : ι, (∀ h ∈ H, D a' * h * (D a')⁻¹ ∈ H) ∧
      (∀ h ∈ H, (D a')⁻¹ * h * D a' ∈ H) ∧
      ∀ (h : H) (hh : D a * h * (D a)⁻¹ ∈ H),
        ((α ⟨_, hh⟩ : H) : M) = g * D a' * g⁻¹ * (α h : M) * (g * D a' * g⁻¹)⁻¹

@[expose] noncomputable def centerQuotEquivOfBot (hZ : Subgroup.center H = ⊥) :
    LargeEvenCenterQuot H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem centerQuotEquivOfBot_mk (hZ : Subgroup.center H = ⊥) (h : H) :
    centerQuotEquivOfBot hZ (LargeEvenCenterMk H h) = h :=
  rfl

theorem centerQuotEquivOfBot_symm (hZ : Subgroup.center H = ⊥) (h : H) :
    (centerQuotEquivOfBot hZ).symm h = LargeEvenCenterMk H h := by
  rw [MulEquiv.symm_apply_eq, centerQuotEquivOfBot_mk]

theorem congr_centerQuotEquivOfBot_mk (hZ : Subgroup.center H = ⊥)
    (α : MulAut (LargeEvenCenterQuot H)) (h : H) :
    α (LargeEvenCenterMk H h) =
      LargeEvenCenterMk H (MulAut.congr (centerQuotEquivOfBot hZ) α h) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← centerQuotEquivOfBot_symm hZ
      ((centerQuotEquivOfBot hZ) (α ((centerQuotEquivOfBot hZ).symm h))),
    MulEquiv.symm_apply_apply, centerQuotEquivOfBot_symm]

theorem conj_mk_centerQuot (g h : H) :
    MulAut.conj (LargeEvenCenterMk H g) (LargeEvenCenterMk H h) =
      LargeEvenCenterMk H (g * h * g⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem exists_conj_isConjOn_of_diagNF {ι : Type*} {D : ι → M} (hZ : Subgroup.center H = ⊥)
    (hNF : DiagNF H D) (α : MulAut (LargeEvenCenterQuot H)) {φ : MulAut (LargeEvenCenterQuot H)}
    {a : ι} (hφ : IsConjOn H φ (D a)) (hinv : ∀ h ∈ H, (D a)⁻¹ * h * D a ∈ H) :
    ∃ (r : LargeEvenCenterQuot H) (φ' : MulAut (LargeEvenCenterQuot H)) (a' : ι),
      IsConjOn H φ' (D a') ∧ (∀ h ∈ H, (D a')⁻¹ * h * D a' ∈ H) ∧
        α * φ * α⁻¹ = MulAut.conj r * φ' * (MulAut.conj r)⁻¹ := by
  set α' := MulAut.congr (centerQuotEquivOfBot hZ) α with hα'
  have hαmk : ∀ z : H, α (LargeEvenCenterMk H z) = LargeEvenCenterMk H (α' z) :=
    congr_centerQuotEquivOfBot_mk hZ α
  have hαinv : ∀ y : H, α⁻¹ (LargeEvenCenterMk H y) = LargeEvenCenterMk H (α'⁻¹ y) := by
    intro y
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hαmk, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  obtain ⟨g, hg, a', h1, h2, hform⟩ := hNF α' a hφ.1 hinv
  set g₀ : H := ⟨g, hg⟩
  set r := LargeEvenCenterMk H g₀
  refine ⟨r, (MulAut.conj r)⁻¹ * (α * φ * α⁻¹) * MulAut.conj r, a', ⟨h1, fun h hh => ?_⟩, h2,
    by group⟩
  have hy : g * (h : M) * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg h.2) (H.inv_mem hg)
  set y : H := ⟨g * h * g⁻¹, hy⟩
  have hcr : MulAut.conj r (LargeEvenCenterMk H h) = LargeEvenCenterMk H y := by
    rw [conj_mk_centerQuot]
    rfl
  set z : H := α'⁻¹ y
  have hz : D a * (z : M) * (D a)⁻¹ ∈ H := hφ.1 z z.2
  have hαz : α' z = y := by
    change α' (α'⁻¹ y) = y
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hw : (α' ⟨_, hz⟩ : M) = g * D a' * g⁻¹ * (y : M) * (g * D a' * g⁻¹)⁻¹ := by
    rw [hform z hz, hαz]
  have hconj : (MulAut.conj r)⁻¹ (LargeEvenCenterMk H (α' ⟨_, hz⟩)) =
      LargeEvenCenterMk H ⟨_, hh⟩ := by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, conj_mk_centerQuot]
    congr 1
    apply Subtype.ext
    rw [hw]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, g₀, y]
    group
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hcr, hαinv,
    hφ.2 z hz, hαmk, hconj]

end Core

section Chev

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
  {H : Subgroup (LargeEvenChevGL A K)}

theorem mem_chevDiagImage_of_isConjOn {φ : MulAut (LargeEvenCenterQuot H)} {a : Fin r → Kˣ}
    (h1 : IsConjOn H φ (TableB.diagHom A K a))
    (h2 : ∀ h ∈ H, (TableB.diagHom A K a)⁻¹ * h * TableB.diagHom A K a ∈ H) :
    φ ∈ LargeEvenChevDiagImage A K H := by
  refine ⟨a, fun h => ⟨⟨_, h1.1 h h.2⟩, (TableB.diag_rel_iff a _ _).2 rfl⟩,
    fun h' => ⟨⟨_, h2 h' h'.2⟩, (TableB.diag_rel_iff a _ _).2 (by group)⟩,
    fun h h' hrel => ?_⟩
  have e := (TableB.diag_rel_iff a _ _).1 hrel
  rw [h1.2 h (h1.1 h h.2)]
  congr 1
  exact Subtype.ext e.symm

theorem exists_isConjOn_of_mem_chevDiagImage {φ : MulAut (LargeEvenCenterQuot H)}
    (hφ : φ ∈ LargeEvenChevDiagImage A K H) :
    ∃ a : Fin r → Kˣ, IsConjOn H φ (TableB.diagHom A K a) ∧
      ∀ h ∈ H, (TableB.diagHom A K a)⁻¹ * h * TableB.diagHom A K a ∈ H := by
  obtain ⟨a, hN, hN', hG⟩ := hφ
  have hfwd : ∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H := by
    intro h hh
    obtain ⟨h', hh'⟩ := hN ⟨h, hh⟩
    rw [← (TableB.diag_rel_iff a _ _).1 hh']
    exact h'.2
  refine ⟨a, ⟨hfwd, fun h hh => hG h ⟨_, hh⟩ ((TableB.diag_rel_iff a _ _).2 rfl)⟩,
    fun h hh => ?_⟩
  obtain ⟨h₀, hh₀⟩ := hN' ⟨h, hh⟩
  have e := (TableB.diag_rel_iff a _ _).1 hh₀
  have e' : (TableB.diagHom A K a)⁻¹ * h * TableB.diagHom A K a = h₀ := by
    rw [show (h : LargeEvenChevGL A K) = ((⟨h, hh⟩ : H) : LargeEvenChevGL A K) from rfl, e]
    group
  rw [e']
  exact h₀.2

theorem ggInndiagNormal_chevID_of_diagNF (hZ : Subgroup.center H = ⊥)
    (hNF : DiagNF H (TableB.diagHom A K)) :
    GGInndiagNormal (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H) := by
  intro α φ hφ
  apply subset_ggInndiag
  set X := LargeEvenInnSet (LargeEvenCenterQuot H) ∪ LargeEvenChevDiagImage A K H
  have hle : Subgroup.closure X ≤ (Subgroup.closure X).comap (MulAut.conj α).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro ψ (⟨x, rfl⟩ | hψ)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ggMulAut_conj_inn_outdiag]
      exact Subgroup.subset_closure (Or.inl ⟨α x, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      obtain ⟨a, ha, hinv⟩ := exists_isConjOn_of_mem_chevDiagImage hψ
      obtain ⟨r, φ', a', h1, h2, e⟩ := exists_conj_isConjOn_of_diagNF hZ hNF α ha hinv
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨r, rfl⟩))
        (Subgroup.subset_closure (Or.inr (mem_chevDiagImage_of_isConjOn h1 h2))))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)))
  have := hle hφ
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

end Chev

end CFSG.StandardType
