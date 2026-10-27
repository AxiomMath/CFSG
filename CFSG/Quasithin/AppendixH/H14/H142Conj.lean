module

public import CFSG.Quasithin.AppendixH.H14.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Open

variable {X : Type*} [Group X]

@[expose] def conjOnSub {G K : Subgroup X} (hGK : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (g : ↥G) :
    MulAut ↥K where
  toFun k := ⟨(g : X) * k * (g : X)⁻¹, hGK g g.2 k k.2⟩
  invFun k := ⟨(g : X)⁻¹ * k * (g : X), by simpa using hGK (g⁻¹) (inv_mem g.2) k k.2⟩
  left_inv k := by ext; simp [mul_assoc]
  right_inv k := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[expose] def actHom {G K : Subgroup X} (hGK : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    {A : Type*} [CommGroup A] (φ : ↥K ≃* A) : ↥G →* MulAut A where
  toFun g := φ.symm.trans ((conjOnSub hGK g).trans φ)
  map_one' := by ext a; simp [conjOnSub]
  map_mul' g h := by ext a; simp [conjOnSub, mul_assoc]

theorem actHom_apply {G K : Subgroup X} (hGK : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    {A : Type*} [CommGroup A] (φ : ↥K ≃* A) (g : ↥G) (k : ↥K) :
    actHom hGK φ g (φ k) = φ ⟨(g : X) * k * (g : X)⁻¹, hGK g g.2 k k.2⟩ := by
  simp [actHom, conjOnSub]

theorem conjIso_of_actHom {G K : Subgroup X} (hKG : K ≤ G)
    (hGK : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) {A : Type*} [CommGroup A] (φ : ↥K ≃* A)
    (Γ : Set (MulAut A)) (h1 : ∀ g : ↥G, actHom hGK φ g ∈ Γ)
    (h2 : ∀ γ ∈ Γ, ∃ g : ↥G, actHom hGK φ g = γ)
    (h3 : ∀ g ∈ G, (∀ k ∈ K, g * k = k * g) → g ∈ K) :
    ConjIso G K A Γ φ (actHom hGK φ) := by
  refine ⟨hKG, h1, h2, ?_, ?_⟩
  · intro g
    constructor
    · intro hπ
      apply h3 g g.2
      intro k hk
      have hk' : actHom hGK φ g (φ ⟨k, hk⟩) = φ ⟨k, hk⟩ := by
        rw [hπ]; rfl
      rw [actHom_apply] at hk'
      have hval : (g : X) * k * (g : X)⁻¹ = k :=
        congrArg Subtype.val (φ.injective hk')
      calc (g : X) * k = ((g : X) * k * (g : X)⁻¹) * (g : X) := by group
        _ = k * (g : X) := by rw [hval]
    · intro hgK
      ext a
      obtain ⟨k, rfl⟩ := φ.surjective a
      rw [actHom_apply]
      have hsub : (⟨(g : X) * (k : X) * (g : X)⁻¹, hGK g g.2 k k.2⟩ : ↥K) =
          (⟨(g : X), hgK⟩ * k * ⟨(g : X), hgK⟩⁻¹ : ↥K) := by
        ext; simp [mul_assoc]
      rw [hsub, map_mul, map_mul, map_inv, MulAut.one_apply,
        mul_comm (φ ⟨(g : X), hgK⟩) (φ k), mul_assoc, mul_inv_cancel, mul_one]
  · intro g k k' h
    rw [actHom_apply]
    exact congrArg φ (Subtype.ext h)

theorem isElemAbelian_map_conj (p : ℕ) (c : X) {E : Subgroup X} (h : IsElemAbelian p E) :
    IsElemAbelian p (E.map (MulAut.conj c).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · haveI : IsMulCommutative E := h.1
    infer_instance
  · rintro x ⟨y, hy, rfl⟩
    rw [← map_pow, h.2 y hy, map_one]

theorem isElemAbelian_of_map_conj (p : ℕ) (c : X) {E : Subgroup X}
    (h : IsElemAbelian p (E.map (MulAut.conj c).toMonoidHom)) : IsElemAbelian p E := by
  have h' := isElemAbelian_map_conj p c⁻¹ h
  have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id X := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h'

theorem card_map_conj (c : X) (E : Subgroup X) :
    Nat.card ↥(E.map (MulAut.conj c).toMonoidHom) = Nat.card ↥E := by
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem map_conj_inf_stabilizer {α : Type*} [MulAction X α] (c : X) (G : Subgroup X) (Y : α) :
    (G ⊓ MulAction.stabilizer X Y).map (MulAut.conj c).toMonoidHom =
      G.map (MulAut.conj c).toMonoidHom ⊓ MulAction.stabilizer X (c • Y) := by
  rw [Subgroup.map_inf G (MulAction.stabilizer X Y) (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj c Y]

theorem conjIsoModel_of_map_conj (c : X) {G K : Subgroup X} {A : Type*} [CommGroup A]
    {Γ : Set (MulAut A)}
    (h : ConjIsoModel (G.map (MulAut.conj c).toMonoidHom) (K.map (MulAut.conj c).toMonoidHom)
      A Γ) : ConjIsoModel G K A Γ := by
  have hf : Function.Injective (MulAut.conj c).toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom] using (MulAut.conj c).injective
  unfold ConjIsoModel at h
  obtain ⟨φ', π', h'⟩ := h
  refine ⟨(Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf).trans φ',
    π'.comp (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf).toMonoidHom, ?_⟩
  unfold ConjIso at h'
  unfold ConjIso
  obtain ⟨hKG', h1', h2', hker', hact'⟩ := h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_map_iff_of_injective hf).mp hKG'
  · intro g
    exact h1' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g)
  · intro γ hγ
    obtain ⟨g', hg'⟩ := h2' γ hγ
    refine ⟨(Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf).symm g', ?_⟩
    change π' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf
      ((Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf).symm g')) = γ
    rw [MulEquiv.apply_symm_apply]
    exact hg'
  · intro g
    have hstep := hker' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g)
    change (π' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g) = 1) ↔
      (g : X) ∈ K
    rw [hstep, Subgroup.coe_equivMapOfInjective_apply]
    exact Subgroup.mem_map_iff_mem hf
  · intro g k k' hk
    have hkk : ((Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k' :
          ↥(K.map (MulAut.conj c).toMonoidHom)) : X) =
        ((Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g :
            ↥(G.map (MulAut.conj c).toMonoidHom)) : X) *
          ((Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k :
            ↥(K.map (MulAut.conj c).toMonoidHom)) : X) *
          ((Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g :
            ↥(G.map (MulAut.conj c).toMonoidHom)) : X)⁻¹ := by
      simp only [Subgroup.coe_equivMapOfInjective_apply]
      rw [hk]
      simp only [map_mul, map_inv]
    have hact := hact' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g)
      (Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k)
      (Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k') hkk
    exact hact

theorem exists_surj_ker_of_map_conj (c : X) {M K : Subgroup X} {R : Type*} [Group R]
    (h : ∃ π : ↥(M.map (MulAut.conj c).toMonoidHom) →* R, Function.Surjective π ∧
      π.ker = (K.map (MulAut.conj c).toMonoidHom).subgroupOf (M.map (MulAut.conj c).toMonoidHom)) :
    ∃ π : ↥M →* R, Function.Surjective π ∧ π.ker = K.subgroupOf M := by
  have hf : Function.Injective (MulAut.conj c).toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom] using (MulAut.conj c).injective
  obtain ⟨π', hsurj, hker⟩ := h
  refine ⟨π'.comp (Subgroup.equivMapOfInjective M (MulAut.conj c).toMonoidHom hf).toMonoidHom,
    ?_, ?_⟩
  · exact hsurj.comp (Subgroup.equivMapOfInjective M (MulAut.conj c).toMonoidHom hf).surjective
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_equivMapOfInjective_apply]
    exact Subgroup.mem_map_iff_mem hf

theorem irreducible_of_map_conj (c : X) {M K : Subgroup X}
    (h : ∀ W : Subgroup X, W ≤ K.map (MulAut.conj c).toMonoidHom → W ≠ ⊥ →
      (∀ g ∈ M.map (MulAut.conj c).toMonoidHom, W.map (MulAut.conj g).toMonoidHom = W) →
        W = K.map (MulAut.conj c).toMonoidHom) :
    ∀ W : Subgroup X, W ≤ K → W ≠ ⊥ → (∀ g ∈ M, W.map (MulAut.conj g).toMonoidHom = W) → W = K := by
  intro W hWK hWne hWin
  have hW' : W.map (MulAut.conj c).toMonoidHom = K.map (MulAut.conj c).toMonoidHom := by
    apply h
    · exact Subgroup.map_mono hWK
    · intro hbot
      exact hWne ((Subgroup.map_eq_bot_iff_of_injective W (MulAut.conj c).injective).mp hbot)
    · intro g' hg'
      obtain ⟨g, hgM, rfl⟩ := Subgroup.mem_map.mp hg'
      have hcomp : (MulAut.conj ((MulAut.conj c).toMonoidHom g)).toMonoidHom.comp
              (MulAut.conj c).toMonoidHom =
          (MulAut.conj c).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hWin g hgM]
  exact Subgroup.map_injective (MulAut.conj c).injective hW'

theorem map_conj_injective (c : X) {A B : Subgroup X}
    (h : A.map (MulAut.conj c).toMonoidHom = B.map (MulAut.conj c).toMonoidHom) : A = B := by
  exact Subgroup.map_injective (MulAut.conj c).injective h

theorem exists_mul_of_card_le [Finite X] {M E : Subgroup X} {N : ℕ} (g : Fin N → X) {Y : Type*}
    (act : X → Y) (hgM : ∀ k, g k ∈ M) (hE : E ≤ M)
    (hact : ∀ k, ∀ e ∈ E, act (g k * e) = act (g k))
    (hinj : Function.Injective (fun k => act (g k))) (hcard : Nat.card ↥M ≤ N * Nat.card ↥E) :
    ∀ x ∈ M, ∃ k, ∃ e ∈ E, x = g k * e := by
  intro x hx
  let F : Fin N × ↥E → ↥M :=
    fun ke => ⟨g ke.1 * (ke.2 : X), mul_mem (hgM ke.1) (hE ke.2.2)⟩
  have hF_inj : Function.Injective F := by
    rintro ⟨k, e⟩ ⟨k', e'⟩ h
    have h1 : g k * (e : X) = g k' * (e' : X) := by
      simpa [F] using congrArg Subtype.val h
    have h2 : act (g k) = act (g k') := by
      calc act (g k) = act (g k * (e : X)) := (hact k e e.2).symm
        _ = act (g k' * (e' : X)) := by rw [h1]
        _ = act (g k') := hact k' e' e'.2
    have hk : k = k' := hinj h2
    subst hk
    have he : e = e' := Subtype.ext (mul_left_cancel h1)
    subst he
    rfl
  have hcard' : Nat.card ↥M ≤ Nat.card (Fin N × ↥E) := by
    rw [Nat.card_prod, Nat.card_fin]
    exact hcard
  have hbij : Function.Bijective F := hF_inj.bijective_of_nat_card_le hcard'
  obtain ⟨ke, hke⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨ke.1, ke.2, by simpa [F] using (congrArg Subtype.val hke).symm⟩

end CFSG.Quasithin.AppendixH.H14