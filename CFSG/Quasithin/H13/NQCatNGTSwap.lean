module

public import CFSG.Quasithin.H13.NQCatNGTMod
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

section Max

variable {G : Type*} [Group G]

theorem subgroupOf_covBy_top {X M : Subgroup G} (hMX : M < X)
    (hmax : ∀ M' : Subgroup G, M ≤ M' → M' < X → M' = M) : M.subgroupOf X ⋖ ⊤ := by
  have hne : M.subgroupOf X ≠ ⊤ := by
    intro h
    refine hMX.ne (le_antisymm hMX.le fun x hx => ?_)
    have : (⟨x, hx⟩ : X) ∈ M.subgroupOf X := h ▸ Subgroup.mem_top _
    exact this
  refine ⟨lt_top_iff_ne_top.mpr hne, fun N hMN hN => ?_⟩
  have hle : M ≤ N.map X.subtype := fun x hx => ⟨⟨x, hMX.le hx⟩, hMN.le hx, rfl⟩
  have hlt : N.map X.subtype < X := by
    refine lt_of_le_of_ne (Subgroup.map_subtype_le N) fun h => hN.ne ?_
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ N.map X.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have e : y = x := Subtype.ext hyx
    exact e ▸ hy
  have heq := hmax _ hle hlt
  refine hMN.ne (le_antisymm hMN.le fun y hy => ?_)
  have : (y : G) ∈ M := heq ▸ ⟨y, hy, rfl⟩
  exact this

theorem conj_maximal {X S M : Subgroup G} {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (hSM : S ≤ M) (hMX : M < X)
    (hmax : ∀ M' : Subgroup G, M ≤ M' → M' < X → M' = M) :
    S ≤ M.map (MulAut.conj g).toMonoidHom ∧ M.map (MulAut.conj g).toMonoidHom < X ∧
      ∀ M' : Subgroup G, M.map (MulAut.conj g).toMonoidHom ≤ M' → M' < X →
        M' = M.map (MulAut.conj g).toMonoidHom := by
  have hX : X.map (MulAut.conj g).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.1 hgX
  have hS : S.map (MulAut.conj g).toMonoidHom = S := Subgroup.mem_normalizer_iff_map_conj_eq.1 hgS
  have hmono : ∀ A B : Subgroup G, A.map (MulAut.conj g).toMonoidHom ≤
      B.map (MulAut.conj g).toMonoidHom ↔ A ≤ B :=
    fun A B => Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective
  refine ⟨hS ▸ Subgroup.map_mono hSM, ?_, fun M' hM' hM'X => ?_⟩
  · conv_rhs => rw [← hX]
    exact lt_of_le_of_ne ((hmono M X).2 hMX.le) fun h =>
      hMX.ne (Subgroup.map_injective (MulAut.conj g).injective h)
  · set M'' := M'.map (MulAut.conj g⁻¹).toMonoidHom with hM''
    have hM'eq : M' = M''.map (MulAut.conj g).toMonoidHom := by
      rw [hM'', Subgroup.map_map]
      convert (Subgroup.map_id M').symm
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hM'eq] at hM' hM'X ⊢
    have h1 : M ≤ M'' := (hmono M M'').1 hM'
    have h2 : M'' < X := by
      rw [← hX] at hM'X
      exact lt_of_le_of_ne ((hmono M'' X).1 hM'X.le) fun h => hM'X.ne (by rw [h])
    rw [hmax M'' h1 h2]

end Max

section Swap

variable {V : Type*} [CommGroup V] [Finite V] {ι : Type} [Fintype ι] [DecidableEq ι]
  {K : Type} [Field K]

theorem conj_inv_sub {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {Q : Subgroup ↥Γ}
    {S : AddSubgroup (ι → K)}
    (hS : ∀ γ ∈ Q, ∀ v ∈ S, ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S)
    (c : ↥Γ) :
    ∀ γ ∈ Q.map (MulAut.conj c).toMonoidHom,
      ∀ v ∈ S.map (Matrix.mulVecLin ((c : Matrix.GeneralLinearGroup ι K) :
        Matrix ι ι K)).toAddMonoidHom,
      ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈
        S.map (Matrix.mulVecLin ((c : Matrix.GeneralLinearGroup ι K) :
          Matrix ι ι K)).toAddMonoidHom := by
  rintro _ ⟨δ, hδ, rfl⟩ _ ⟨v, hv, rfl⟩
  refine ⟨((δ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v, hS δ hδ v hv, ?_⟩
  simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem card_map_mulVecLin (c : Matrix.GeneralLinearGroup ι K) (S : AddSubgroup (ι → K)) :
    Nat.card (S.map (Matrix.mulVecLin (c : Matrix ι ι K)).toAddMonoidHom) = Nat.card S := by
  refine AddSubgroup.card_map_of_injective fun v w hvw => ?_
  have h := congrArg (fun u => ((c⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec u)
    hvw
  simpa [Matrix.mulVec_mulVec] using h

theorem no_swap_generic {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} [Finite Γ]
    {X : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥Γ →* ↥X}
    (hT : NatTransfer X U Z Γ π)
    {U₀ : Subgroup ↥Γ} (hU₀ : IsSylowTwoOf U₀ ⊤)
    {Q : Fin 2 → Subgroup ↥Γ} (hR : ResidualOvergroupsAt ↥Γ U₀ Q) (q : ℕ)
    (hsmall : ∃ S : AddSubgroup (ι → K), S ≠ ⊥ ∧ Nat.card S ≤ q ∧
      ∀ γ ∈ Q 0, ∀ v ∈ S, ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S)
    (hbig : ∀ S : AddSubgroup (ι → K), S ≠ ⊥ →
      (∀ γ ∈ Q 1, ∀ v ∈ S, ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) →
        q < Nat.card S)
    {S M₀ M₁ : Subgroup (MulAut V)} (hS : IsSylowTwoOf S X)
    (hM₀ : S ≤ M₀ ∧ M₀ < X ∧ ∀ M' : Subgroup (MulAut V), M₀ ≤ M' → M' < X → M' = M₀)
    (hM₁ : S ≤ M₁ ∧ M₁ < X ∧ ∀ M' : Subgroup (MulAut V), M₁ ≤ M' → M' < X → M' = M₁)
    (hne : M₀ ≠ M₁) (g : MulAut V) (hgU : U.map g.toMonoidHom = U)
    (hgZ : Z.map g.toMonoidHom = Z) (hg : M₀.map (MulAut.conj g).toMonoidHom = M₁) : False := by
  classical
  obtain ⟨hsurj, hinj, hA, hB⟩ := hT
  let ψ : ↥Γ ≃* ↥X := MulEquiv.ofBijective π ⟨hinj, hsurj⟩
  have hψ : ∀ γ, (ψ γ : MulAut V) = (π γ : MulAut V) := fun γ => rfl
  have hSX : IsSylowTwoOf (S.subgroupOf X) ⊤ := Setup.Layer.isSylowTwoOf_subgroupOf_top' hS
  have hS' : IsSylowTwoOf ((S.subgroupOf X).map ψ.symm.toMonoidHom) ⊤ :=
    B113Lie.isSylowTwoOf_map_top ψ.symm hSX
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hU₀ hS'
  have hR' := hR.map (MulAut.conj c)
  have hcS : U₀.map (MulAut.conj c).toMonoidHom = (S.subgroupOf X).map ψ.symm.toMonoidHom :=
    hc.symm
  rw [hcS] at hR'
  have hpre : ∀ M : Subgroup (MulAut V), S ≤ M → M < X →
      (∀ M' : Subgroup (MulAut V), M ≤ M' → M' < X → M' = M) →
      ∃ k : Fin 2, (M.subgroupOf X).map ψ.symm.toMonoidHom =
        (Q k).map (MulAut.conj c).toMonoidHom := by
    intro M hSM hMX hmax
    have hcov := subgroupOf_covBy_top hMX hmax
    have hcov' : (M.subgroupOf X).map ψ.symm.toMonoidHom ⋖ ⊤ := by
      have := (apply_covBy_apply_iff (MulEquiv.mapSubgroup ψ.symm)).2 hcov
      have h2 : (⊤ : Subgroup X).map ψ.symm.toMonoidHom = ⊤ :=
        Subgroup.map_top_of_surjective ψ.symm.toMonoidHom fun y => ⟨ψ y, ψ.symm_apply_apply y⟩
      change (M.subgroupOf X).map ψ.symm.toMonoidHom ⋖ (⊤ : Subgroup X).map ψ.symm.toMonoidHom
        at this
      rwa [h2] at this
    have hle : (S.subgroupOf X).map ψ.symm.toMonoidHom ≤ (M.subgroupOf X).map ψ.symm.toMonoidHom :=
      Subgroup.map_mono fun x hx => hSM hx
    exact (hR'.2.2.1 _ hle).1 hcov'
  obtain ⟨k₀, hk₀⟩ := hpre M₀ hM₀.1 hM₀.2.1 hM₀.2.2
  obtain ⟨k₁, hk₁⟩ := hpre M₁ hM₁.1 hM₁.2.1 hM₁.2.2
  have hk : k₀ ≠ k₁ := by
    intro hkk
    apply hne
    have h1 : M₀.subgroupOf X = M₁.subgroupOf X := by
      apply Subgroup.map_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective
      rw [hk₀, hk₁, hkk]
    rw [← Subgroup.map_subgroupOf_eq_of_le hM₀.2.1.le, ← Subgroup.map_subgroupOf_eq_of_le
      hM₁.2.1.le, h1]
  have hmem : ∀ (M : Subgroup (MulAut V)) (k : Fin 2), M ≤ X →
      (M.subgroupOf X).map ψ.symm.toMonoidHom = (Q k).map (MulAut.conj c).toMonoidHom →
      ∀ γ : ↥Γ, ((π γ : X) : MulAut V) ∈ M ↔ γ ∈ (Q k).map (MulAut.conj c).toMonoidHom := by
    intro M k hMX hMk γ
    rw [← hMk, Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf, hψ]
  have key : ∀ (Ma Mb : Subgroup (MulAut V)) (g' : MulAut V), Ma ≤ X → Mb ≤ X →
      (Ma.subgroupOf X).map ψ.symm.toMonoidHom = (Q 0).map (MulAut.conj c).toMonoidHom →
      (Mb.subgroupOf X).map ψ.symm.toMonoidHom = (Q 1).map (MulAut.conj c).toMonoidHom →
      U.map g'.toMonoidHom = U → Z.map g'.toMonoidHom = Z →
      Ma.map (MulAut.conj g').toMonoidHom = Mb → False := by
    intro Ma Mb g' hMa hMb hka hkb hgU' hgZ' hg'
    refine no_swap_of_transfer hA hB hMa hMb q ?_ ?_ g' hgU' hgZ' hg'
    · obtain ⟨S₀, hS₀, hS₀q, hS₀inv⟩ := hsmall
      refine ⟨S₀.map (Matrix.mulVecLin ((c : Matrix.GeneralLinearGroup ι K) :
        Matrix ι ι K)).toAddMonoidHom, ?_, ?_, fun γ hγ => ?_⟩
      · intro h0
        apply hS₀
        have := card_map_mulVecLin (c : Matrix.GeneralLinearGroup ι K) S₀
        rw [h0, AddSubgroup.card_bot] at this
        exact AddSubgroup.eq_bot_of_card_eq S₀ this.symm
      · rw [card_map_mulVecLin]
        exact hS₀q
      · exact conj_inv_sub hS₀inv c γ ((hmem Ma 0 hMa hka γ).1 hγ)
    · intro S₁ hS₁ hS₁inv
      set S₂ := S₁.map (Matrix.mulVecLin (((c⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) :
        Matrix ι ι K)).toAddMonoidHom with hS₂
      have hS₂inv : ∀ δ ∈ Q 1, ∀ v ∈ S₂,
          ((δ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S₂ := by
        have h1 := conj_inv_sub (Q := (Q 1).map (MulAut.conj c).toMonoidHom) (S := S₁)
          (fun γ hγ v hv => hS₁inv γ ((hmem Mb 1 hMb hkb γ).2 hγ) v hv) c⁻¹
        intro δ hδ v hv
        refine h1 δ ?_ v hv
        refine ⟨c * δ * c⁻¹, ⟨δ, hδ, rfl⟩, ?_⟩
        simp [mul_assoc]
      have hS₂0 : S₂ ≠ ⊥ := by
        intro h0
        apply hS₁
        have := card_map_mulVecLin ((c⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) S₁
        rw [← hS₂, h0, AddSubgroup.card_bot] at this
        exact AddSubgroup.eq_bot_of_card_eq S₁ this.symm
      have := hbig S₂ hS₂0 hS₂inv
      rwa [hS₂, card_map_mulVecLin] at this
  have hgg : g⁻¹.toMonoidHom.comp g.toMonoidHom = MonoidHom.id V := by
    ext x
    exact MulAut.inv_apply_self V g x
  have hgU' : U.map g⁻¹.toMonoidHom = U := by
    calc U.map g⁻¹.toMonoidHom = (U.map g.toMonoidHom).map g⁻¹.toMonoidHom := by rw [hgU]
      _ = U := by rw [Subgroup.map_map, hgg, Subgroup.map_id]
  have hgZ' : Z.map g⁻¹.toMonoidHom = Z := by
    calc Z.map g⁻¹.toMonoidHom = (Z.map g.toMonoidHom).map g⁻¹.toMonoidHom := by rw [hgZ]
      _ = Z := by rw [Subgroup.map_map, hgg, Subgroup.map_id]
  have hcc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (MulAut V) := by
    ext x : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hg' : M₁.map (MulAut.conj g⁻¹).toMonoidHom = M₀ := by
    rw [← hg, Subgroup.map_map, hcc, Subgroup.map_id]
  have hk01 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  rcases hk01 k₀ k₁ hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key M₀ M₁ g hM₀.2.1.le hM₁.2.1.le hk₀ hk₁ hgU hgZ hg
  · exact key M₁ M₀ g⁻¹ hM₁.2.1.le hM₀.2.1.le hk₁ hk₀ hgU' hgZ' hg'

end Swap

end CFSG.Quasithin.H13.NQCat.NGT
