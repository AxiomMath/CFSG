module

public import CFSG.Milestones.ASVolI.C61.Tr2
public import CFSG.Milestones.ASVolI.C6

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {A B : Type} [Group A] [Group B] {f : A →* B} (hf : Function.Injective f)
include hf

@[expose] noncomputable def burnsideC56_tr_eU (L : Subgroup A) : ↥(blockU L) ≃* ↥(blockU (L.map f)) :=
  ((blockU L).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (burnsideC56_tr_blockU hf L).symm)

theorem burnsideC56_tr_eU_coe (L : Subgroup A) (u : ↥(blockU L)) :
    ((burnsideC56_tr_eU hf L u : ↥(blockU (L.map f))) : B) = f u := rfl

theorem burnsideC56_tr_eU_blockZ (L : Subgroup A) :
    ((blockZ L).subgroupOf (blockU L)).map (burnsideC56_tr_eU hf L).toMonoidHom =
      (blockZ (L.map f)).subgroupOf (blockU (L.map f)) := by
  ext u'
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ∈ (blockZ L).subgroupOf (blockU L) := hu
    rw [Subgroup.mem_subgroupOf] at hu'
    show burnsideC56_tr_eU hf L u ∈ (blockZ (L.map f)).subgroupOf (blockU (L.map f))
    rw [Subgroup.mem_subgroupOf, burnsideC56_tr_eU_coe, burnsideC56_tr_blockZ hf]
    exact Subgroup.mem_map_of_mem f hu'
  · intro hu'
    obtain ⟨u, rfl⟩ := (burnsideC56_tr_eU hf L).surjective u'
    refine ⟨u, ?_, rfl⟩
    show u ∈ (blockZ L).subgroupOf (blockU L)
    rw [Subgroup.mem_subgroupOf] at hu' ⊢
    rw [burnsideC56_tr_eU_coe, burnsideC56_tr_blockZ hf] at hu'
    exact (Subgroup.mem_map_iff_mem hf).mp hu'

omit hf in
theorem burnsideC56_tr_ker_comp {X Y Z : Type*} [Group X] [Group Y] [Group Z] (e : X ≃* Y)
    (φ : Y →* Z) (K : Subgroup Y) (hK : φ.ker = K) :
    (φ.comp e.toMonoidHom).ker = K.comap e.toMonoidHom := by
  rw [← MonoidHom.comap_ker, hK]

omit hf in
theorem burnsideC56_tr_comap_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (K : Subgroup X) :
    (K.map e.toMonoidHom).comap e.toMonoidHom = K :=
  Subgroup.comap_map_eq_self_of_injective e.injective K

omit hf in
theorem burnsideC56_tr_comap_symm {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (K : Subgroup X) :
    K.comap e.symm.toMonoidHom = K.map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    exact ⟨e.symm y, hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem burnsideC56_tr_typeWitness {T M : Type*} [Group T] [Group M] (R : T → M → M → Prop)
    (L : Subgroup A) :
    (∃ α : ↥(L.map f) →* T, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥(L.map f) ∧
      ∃ β : ↥(blockU (L.map f)) →* M, Function.Surjective β ∧
        β.ker = (blockZ (L.map f)).subgroupOf (blockU (L.map f)) ∧
        ∀ (ℓ : ↥(L.map f)) (u v : ↥(blockU (L.map f))), (v : B) = ℓ * u * ℓ⁻¹ →
          R (α ℓ) (β u) (β v)) ↔
    (∃ α : ↥L →* T, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      ∃ β : ↥(blockU L) →* M, Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
        ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : A) = ℓ * u * ℓ⁻¹ → R (α ℓ) (β u) (β v)) := by
  set eL : L ≃* (L.map f) := L.equivMapOfInjective f hf with heL
  set eU := burnsideC56_tr_eU hf L with heU
  have hP : (CFSG.pCore 2 ↥L).map eL.toMonoidHom = CFSG.pCore 2 ↥(L.map f) := CFSG.pCore_map_iso 2 eL
  have hZ := burnsideC56_tr_eU_blockZ hf L
  have hcoeL : ∀ ℓ : ↥L, ((eL ℓ : ↥(L.map f)) : B) = f ℓ := fun ℓ =>
    Subgroup.coe_equivMapOfInjective_apply L f hf ℓ
  constructor
  · rintro ⟨α, hαs, hαk, β, hβs, hβk, hR⟩
    refine ⟨α.comp eL.toMonoidHom, hαs.comp eL.surjective, ?_, β.comp eU.toMonoidHom,
      hβs.comp eU.surjective, ?_, fun ℓ u v huv => ?_⟩
    · rw [burnsideC56_tr_ker_comp eL α _ hαk, ← hP, burnsideC56_tr_comap_map]
    · rw [burnsideC56_tr_ker_comp eU β _ hβk, ← hZ, burnsideC56_tr_comap_map]
    · refine hR (eL ℓ) (eU u) (eU v) ?_
      rw [heU, burnsideC56_tr_eU_coe, burnsideC56_tr_eU_coe, huv]
      simp only [map_mul, map_inv, Subgroup.coe_inv, hcoeL]
  · rintro ⟨α, hαs, hαk, β, hβs, hβk, hR⟩
    refine ⟨α.comp eL.symm.toMonoidHom, hαs.comp eL.symm.surjective, ?_, β.comp eU.symm.toMonoidHom,
      hβs.comp eU.symm.surjective, ?_, fun ℓ u v huv => ?_⟩
    · rw [burnsideC56_tr_ker_comp eL.symm α _ hαk, burnsideC56_tr_comap_symm, hP]
    · rw [burnsideC56_tr_ker_comp eU.symm β _ hβk, burnsideC56_tr_comap_symm, hZ]
    · refine hR (eL.symm ℓ) (eU.symm u) (eU.symm v) (hf ?_)
      have h1 : f (eU.symm v : A) = v := by
        rw [← burnsideC56_tr_eU_coe hf L, ← heU, eU.apply_symm_apply]
      have h2 : f (eU.symm u : A) = u := by
        rw [← burnsideC56_tr_eU_coe hf L, ← heU, eU.apply_symm_apply]
      have h3 : f (eL.symm ℓ : A) = ℓ := by
        rw [← hcoeL, eL.apply_symm_apply]
      rw [h1, map_mul, map_mul, Subgroup.coe_inv, map_inv, h2, h3, huv, Subgroup.coe_inv]

theorem burnsideC56_tr_isLin2Type (L : Subgroup A) (n : ℕ) :
    IsLin2Type (L.map f) n ↔ IsLin2Type L n := by
  unfold IsLin2Type
  constructor
  · rintro ⟨F, hF, hFt, hcard, hw⟩
    exact ⟨F, hF, hFt, hcard, (burnsideC56_tr_typeWitness hf
      (fun (t : Matrix.SpecialLinearGroup (Fin 2) F) (x y : Multiplicative (Fin 2 → F)) =>
        Multiplicative.toAdd y = (t : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x))
      L).mp hw⟩
  · rintro ⟨F, hF, hFt, hcard, hw⟩
    exact ⟨F, hF, hFt, hcard, (burnsideC56_tr_typeWitness hf
      (fun (t : Matrix.SpecialLinearGroup (Fin 2) F) (x y : Multiplicative (Fin 2 → F)) =>
        Multiplicative.toAdd y = (t : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x))
      L).mpr hw⟩

theorem burnsideC56_tr_isAltType (L : Subgroup A) (m : ℕ) :
    IsAltType (L.map f) m ↔ IsAltType L m := by
  unfold IsAltType
  exact burnsideC56_tr_typeWitness hf
    (fun (t : alternatingGroup (Fin m)) (x y : Multiplicative (evenWeight m)) =>
      ∀ i : Fin m, ((Multiplicative.toAdd y : evenWeight m) : Fin m → ZMod 2) i =
        ((Multiplicative.toAdd x : evenWeight m) : Fin m → ZMod 2) ((t : Equiv.Perm (Fin m))⁻¹ i)) L

theorem burnsideC56_tr_le_centralizer (K₁ K₂ : Subgroup A) :
    K₁.map f ≤ Subgroup.centralizer ((K₂.map f : Subgroup B) : Set B) ↔
      K₁ ≤ Subgroup.centralizer (K₂ : Set A) := by
  have h := burnsideC56_tr_centralizer hf K₁ K₂
  constructor
  · intro h1
    have h2 : (K₁ ⊓ Subgroup.centralizer (K₂ : Set A)).map f = K₁.map f := by
      rw [h]; exact inf_eq_left.mpr h1
    exact inf_eq_left.mp ((Subgroup.map_injective hf) h2)
  · intro h1
    have : K₁ ⊓ Subgroup.centralizer (K₂ : Set A) = K₁ := inf_eq_left.mpr h1
    rw [this] at h
    rw [h]
    exact inf_le_right

theorem burnsideC56_tr_isA3Product (X L : Subgroup A) (s : ℕ) :
    IsA3Product (X.map f) (L.map f) s ↔ IsA3Product X L s := by
  unfold IsA3Product
  constructor
  · rintro ⟨K₁', hb1, ha1, h⟩
    have hK₁ := burnsideC56_tr_eq_map_comap hf hb1.2.1
    rw [← hK₁] at hb1 ha1 h
    rw [burnsideC56_tr_isBlock2 hf] at hb1
    rw [burnsideC56_tr_isAltType hf] at ha1
    refine ⟨K₁'.comap f, hb1, ha1, ?_⟩
    rcases h with ⟨hs, hL⟩ | ⟨hs, K₂', hne, hb2, ha2, hc, hL⟩
    · exact Or.inl ⟨hs, (Subgroup.map_injective hf) hL⟩
    · have hK₂ := burnsideC56_tr_eq_map_comap hf hb2.2.1
      rw [← hK₂] at hne hb2 ha2 hc hL
      rw [burnsideC56_tr_isBlock2 hf] at hb2
      rw [burnsideC56_tr_isAltType hf] at ha2
      rw [burnsideC56_tr_le_centralizer hf] at hc
      rw [← Subgroup.map_sup] at hL
      refine Or.inr ⟨hs, K₂'.comap f, fun h' => hne (by rw [h']), hb2, ha2, hc,
        (Subgroup.map_injective hf) hL⟩
  · rintro ⟨K₁, hb1, ha1, h⟩
    refine ⟨K₁.map f, (burnsideC56_tr_isBlock2 hf X K₁).mpr hb1,
      (burnsideC56_tr_isAltType hf K₁ 3).mpr ha1, ?_⟩
    rcases h with ⟨hs, hL⟩ | ⟨hs, K₂, hne, hb2, ha2, hc, hL⟩
    · exact Or.inl ⟨hs, by rw [hL]⟩
    · refine Or.inr ⟨hs, K₂.map f, fun h' => hne ((Subgroup.map_injective hf) h'),
        (burnsideC56_tr_isBlock2 hf X K₂).mpr hb2, (burnsideC56_tr_isAltType hf K₂ 3).mpr ha2,
        (burnsideC56_tr_le_centralizer hf K₁ K₂).mpr hc, by rw [hL, Subgroup.map_sup]⟩

theorem burnsideC56_tr_nonempty_mulEquiv (X : Subgroup A) (W : Type*) [Group W] :
    Nonempty (↥(X.map f) ≃* W) ↔ Nonempty (↥X ≃* W) := by
  let e : X ≃* (X.map f) := X.equivMapOfInjective f hf
  exact ⟨fun ⟨e'⟩ => ⟨e.trans e'⟩, fun ⟨e'⟩ => ⟨e.symm.trans e'⟩⟩

theorem burnsideC56_tr_isDihedralOrSemidihedral (P : Subgroup A) :
    IsDihedralOrSemidihedral (P.map f) ↔ IsDihedralOrSemidihedral P := by
  unfold IsDihedralOrSemidihedral
  simp only [burnsideC56_tr_nonempty_mulEquiv hf]

end CFSG.ASVolI
