module

public import CFSG.Sporadic.Co1Patterson.TitsMulti
public import CFSG.Sporadic.SuzRecog.ModelBase

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Sporadic.Co1Patterson

variable {P G : Type*} [Group P] [Group G]

theorem hom_ext_of_le_sup {K A B : Subgroup P} (hK : K ≤ (K ⊓ A) ⊔ (K ⊓ B)) {f g : ↥K →* G}
    (hA : ∀ x (hx : x ∈ K), x ∈ A → f ⟨x, hx⟩ = g ⟨x, hx⟩)
    (hB : ∀ x (hx : x ∈ K), x ∈ B → f ⟨x, hx⟩ = g ⟨x, hx⟩) : f = g := by
  have hle : K ≤ (MonoidHom.eqLocus f g).map K.subtype := by
    refine hK.trans (sup_le ?_ ?_)
    · rintro x ⟨hxK, hxA⟩
      exact ⟨⟨x, hxK⟩, hA x hxK hxA, rfl⟩
    · rintro x ⟨hxK, hxB⟩
      exact ⟨⟨x, hxK⟩, hB x hxK hxB, rfl⟩
  ext ⟨x, hx⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hx⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

@[expose] def resHom {S N : Subgroup P} (f : ↥N →* G) (Y : Subgroup ↥S)
    (h : ∀ a ∈ Y, (a : P) ∈ N) : ↥Y →* G where
  toFun a := f ⟨((a : ↥S) : P), h a a.2⟩
  map_one' := by
    rw [← map_one f]
    rfl
  map_mul' a b := by
    rw [← map_mul]
    rfl

theorem resHom_apply {S N : Subgroup P} (f : ↥N →* G) (Y : Subgroup ↥S)
    (h : ∀ a ∈ Y, (a : P) ∈ N) (a : ↥Y) : resHom f Y h a = f ⟨((a : ↥S) : P), h a a.2⟩ := rfl

theorem mem_of_mem_subgroupOf {S Y X : Subgroup P} {Y' : Subgroup ↥S} (hY : Y' = Y.subgroupOf S)
    (hYX : Y ≤ X) {a : ↥S} (ha : a ∈ Y') : (a : P) ∈ X :=
  hYX (by rw [hY] at ha; exact ha)

theorem mem_or_mul_mem_of_mem_sup {K : Subgroup P} {ι : P} (hιι : ι * ι = 1)
    (hιK : ∀ c ∈ K, ι * c * ι⁻¹ ∈ K) {x : P} (hx : x ∈ K ⊔ zpowers ι) : x ∈ K ∨ x * ι ∈ K := by
  have hinv : ι⁻¹ = ι := inv_eq_of_mul_eq_one_right hιι
  let L : Subgroup P :=
    { carrier := {x | x ∈ K ∨ x * ι ∈ K}
      one_mem' := Or.inl K.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (K.mul_mem ha hb)
        · exact Or.inr (by simpa [mul_assoc] using K.mul_mem ha hb)
        · refine Or.inr ?_
          have h := K.mul_mem ha (hιK _ hb)
          rw [hinv] at h
          have e : a * ι * (ι * b * ι) = a * (ι * ι) * b * ι := by group
          rwa [e, hιι, mul_one] at h
        · refine Or.inl ?_
          have h := K.mul_mem ha (hιK _ hb)
          rw [hinv] at h
          have e : a * ι * (ι * (b * ι) * ι) = a * (ι * ι) * b * (ι * ι) := by group
          rwa [e, hιι, mul_one, mul_one] at h
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (K.inv_mem ha)
        · refine Or.inr ?_
          have h := K.inv_mem (hιK _ ha)
          have e : (ι * (a * ι) * ι⁻¹)⁻¹ = a⁻¹ * ι⁻¹ := by group
          rwa [e, hinv] at h }
  have hle : K ⊔ zpowers ι ≤ L := sup_le (fun c hc => Or.inl hc)
    ((zpowers_le (H := L)).2 (Or.inr (by rw [hιι]; exact K.one_mem)))
  exact hle hx

theorem conj_mem_centralizer_inf {S : Subgroup P} {ρ ι : P} (hι : ι ∈ S)
    (hρ : ι * ρ * ι⁻¹ = ρ⁻¹) {c : P} (hc : c ∈ centralizer {ρ} ⊓ S) :
    ι * c * ι⁻¹ ∈ centralizer {ρ} ⊓ S := by
  refine ⟨mem_centralizer_singleton_iff.2 ?_, S.mul_mem (S.mul_mem hι hc.2) (S.inv_mem hι)⟩
  have hcρ : c * ρ = ρ * c := mem_centralizer_singleton_iff.1 hc.1
  have hρ' : ρ = ι * ρ⁻¹ * ι⁻¹ :=
    calc ρ = (ρ⁻¹)⁻¹ := (inv_inv ρ).symm
      _ = (ι * ρ * ι⁻¹)⁻¹ := by rw [hρ]
      _ = ι * ρ⁻¹ * ι⁻¹ := by group
  have hcρ' : c * ρ⁻¹ = ρ⁻¹ * c :=
    calc c * ρ⁻¹ = ρ⁻¹ * (ρ * c) * ρ⁻¹ := by group
      _ = ρ⁻¹ * (c * ρ) * ρ⁻¹ := by rw [hcρ]
      _ = ρ⁻¹ * c := by group
  calc ι * c * ι⁻¹ * ρ = ι * c * ι⁻¹ * (ι * ρ⁻¹ * ι⁻¹) := by rw [← hρ']
    _ = ι * (c * ρ⁻¹) * ι⁻¹ := by group
    _ = ι * (ρ⁻¹ * c) * ι⁻¹ := by rw [hcρ']
    _ = ι * ρ⁻¹ * ι⁻¹ * (ι * c * ι⁻¹) := by group
    _ = ρ * (ι * c * ι⁻¹) := by rw [← hρ']

section Vertex

variable {C1 NR Cr Nv : Subgroup P} {M : Subgroup G} (σ : ↥M ≃* ↥C1) (ψ : ↥NR →* G)
  (Φ₂ : ↥Cr →* G) {ι : P} (hι1 : ι ∈ C1) (hιN : ι ∈ NR) (hιι : ι * ι = 1)
  (hιCr : ∀ c ∈ Cr, ι * c * ι⁻¹ ∈ Cr)
  (hC : ∀ x (hx : x ∈ C1) (hxN : x ∈ NR), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G))
  (hA : ∀ x (hx : x ∈ C1) (hxC : x ∈ Cr), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G))
  (hB : ∀ x (hxN : x ∈ NR) (hxC : x ∈ Cr), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩)

include hιι in
theorem inv_iota : ι⁻¹ = ι := inv_eq_of_mul_eq_one_right hιι

include hιι hιN in
theorem psi_iota_mul_self : ψ ⟨ι, hιN⟩ * ψ ⟨ι, hιN⟩ = 1 := by
  rw [← map_mul, ← map_one ψ]
  congr 1
  exact Subtype.ext hιι

@[expose] def conjIotaHom : ↥Cr →* G :=
  MonoidHom.mk' (fun c => Φ₂ ⟨ι * c * ι⁻¹, hιCr c c.2⟩) fun a b => by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_mul]
    group

include hι1 hιN hC hA hB in
theorem map_conj_iota (hCr : Cr ≤ (Cr ⊓ C1) ⊔ (Cr ⊓ NR)) {c : P} (hc : c ∈ Cr) :
    Φ₂ ⟨ι * c * ι⁻¹, hιCr c hc⟩ = ψ ⟨ι, hιN⟩ * Φ₂ ⟨c, hc⟩ * (ψ ⟨ι, hιN⟩)⁻¹ := by
  have key := hom_ext_of_le_sup hCr (f := conjIotaHom Φ₂ hιCr)
    (g := (MulAut.conj (ψ ⟨ι, hιN⟩)).toMonoidHom.comp Φ₂) (fun x hx hx1 => ?_) (fun x hx hxN => ?_)
  · exact DFunLike.congr_fun key ⟨c, hc⟩
  · have hx' : ι * x * ι⁻¹ ∈ C1 := C1.mul_mem (C1.mul_mem hι1 hx1) (C1.inv_mem hι1)
    change Φ₂ ⟨ι * x * ι⁻¹, _⟩ = ψ ⟨ι, hιN⟩ * Φ₂ ⟨x, hx⟩ * (ψ ⟨ι, hιN⟩)⁻¹
    rw [hA _ hx', hA _ hx1, hC _ hι1]
    have : (⟨ι * x * ι⁻¹, hx'⟩ : ↥C1) = ⟨ι, hι1⟩ * ⟨x, hx1⟩ * (⟨ι, hι1⟩ : ↥C1)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    simp
  · have hx' : ι * x * ι⁻¹ ∈ NR := NR.mul_mem (NR.mul_mem hιN hxN) (NR.inv_mem hιN)
    change Φ₂ ⟨ι * x * ι⁻¹, _⟩ = ψ ⟨ι, hιN⟩ * Φ₂ ⟨x, hx⟩ * (ψ ⟨ι, hιN⟩)⁻¹
    rw [hB _ hx', hB _ hxN]
    have : (⟨ι * x * ι⁻¹, hx'⟩ : ↥NR) = ⟨ι, hιN⟩ * ⟨x, hxN⟩ * (⟨ι, hιN⟩ : ↥NR)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]

open scoped Classical in
@[expose] noncomputable def vertexMap (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) : ↥Nv → G :=
  fun x => if h : (x : P) ∈ Cr then Φ₂ ⟨x, h⟩
    else Φ₂ ⟨x * ι, (hNv x x.2).resolve_left h⟩ * ψ ⟨ι, hιN⟩

theorem vertexMap_of_mem (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) {x : P} (hx : x ∈ Nv)
    (hxC : x ∈ Cr) : vertexMap ψ Φ₂ hιN hNv ⟨x, hx⟩ = Φ₂ ⟨x, hxC⟩ := by
  unfold vertexMap
  rw [dite_eq_left hxC]

theorem vertexMap_of_not_mem (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) {x : P} (hx : x ∈ Nv)
    (hxC : x ∉ Cr) :
    vertexMap ψ Φ₂ hιN hNv ⟨x, hx⟩ = Φ₂ ⟨x * ι, (hNv x hx).resolve_left hxC⟩ * ψ ⟨ι, hιN⟩ := by
  unfold vertexMap
  rw [dite_eq_right hxC]

include hι1 hιι hιCr hC hA hB in
theorem vertexMap_mul (hCr : Cr ≤ (Cr ⊓ C1) ⊔ (Cr ⊓ NR))
    (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) (x y : ↥Nv) :
    vertexMap ψ Φ₂ hιN hNv (x * y) = vertexMap ψ Φ₂ hιN hNv x * vertexMap ψ Φ₂ hιN hNv y := by
  have hinv := inv_iota hιι
  have htw := fun {c : P} (hc : c ∈ Cr) => map_conj_iota σ ψ Φ₂ hι1 hιN hιCr hC hA hB hCr hc
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  have hxy : x * y ∈ Nv := Nv.mul_mem hx hy
  change vertexMap ψ Φ₂ hιN hNv ⟨x * y, hxy⟩ = _
  by_cases hxC : x ∈ Cr <;> by_cases hyC : y ∈ Cr
  · rw [vertexMap_of_mem _ _ _ _ hxy (Cr.mul_mem hxC hyC), vertexMap_of_mem _ _ _ _ hx hxC,
      vertexMap_of_mem _ _ _ _ hy hyC, ← map_mul]
    rfl
  · have hxyC : x * y ∉ Cr := fun h => hyC (by simpa using Cr.mul_mem (Cr.inv_mem hxC) h)
    have hyι := (hNv y hy).resolve_left hyC
    rw [vertexMap_of_not_mem _ _ _ _ hxy hxyC, vertexMap_of_mem _ _ _ _ hx hxC,
      vertexMap_of_not_mem _ _ _ _ hy hyC, ← mul_assoc, ← map_mul]
    congr 2
    exact Subtype.ext (mul_assoc _ _ _)
  · have hxyC : x * y ∉ Cr := fun h => hxC (by simpa using Cr.mul_mem h (Cr.inv_mem hyC))
    have hxι := (hNv x hx).resolve_left hxC
    have hc := hιCr y hyC
    rw [vertexMap_of_not_mem _ _ _ _ hxy hxyC, vertexMap_of_not_mem _ _ _ _ hx hxC,
      vertexMap_of_mem _ _ _ _ hy hyC]
    have h1 : (⟨x * y * ι, (hNv _ hxy).resolve_left hxyC⟩ : ↥Cr) =
        ⟨x * ι, hxι⟩ * ⟨ι * y * ι⁻¹, hc⟩ := by
      apply Subtype.ext
      simp only [coe_mul]
      rw [hinv]
      calc x * y * ι = x * (ι * ι) * y * ι := by rw [hιι, mul_one]
        _ = x * ι * (ι * y * ι) := by group
    rw [h1, map_mul, htw hyC]
    group
  · have hxyC : x * y ∈ Cr := by
      have h := Cr.mul_mem ((hNv x hx).resolve_left hxC) (hιCr _ ((hNv y hy).resolve_left hyC))
      rw [hinv] at h
      have e : x * ι * (ι * (y * ι) * ι) = x * (ι * ι) * y * (ι * ι) := by group
      rwa [e, hιι, mul_one, mul_one] at h
    have hxι := (hNv x hx).resolve_left hxC
    have hyι := (hNv y hy).resolve_left hyC
    rw [vertexMap_of_mem _ _ _ _ hxy hxyC, vertexMap_of_not_mem _ _ _ _ hx hxC,
      vertexMap_of_not_mem _ _ _ _ hy hyC]
    have hc := hιCr _ hyι
    have h1 : (⟨x * y, hxyC⟩ : ↥Cr) = ⟨x * ι, hxι⟩ * ⟨ι * (y * ι) * ι⁻¹, hc⟩ := by
      apply Subtype.ext
      simp only [coe_mul]
      rw [hinv]
      calc x * y = x * (ι * ι) * y * (ι * ι) := by rw [hιι, mul_one, mul_one]
        _ = x * ι * (ι * (y * ι) * ι) := by group
    rw [h1, map_mul, htw hyι]
    have hψ := psi_iota_mul_self ψ hιN hιι
    calc Φ₂ ⟨x * ι, hxι⟩ * (ψ ⟨ι, hιN⟩ * Φ₂ ⟨y * ι, hyι⟩ * (ψ ⟨ι, hιN⟩)⁻¹)
        = Φ₂ ⟨x * ι, hxι⟩ * ψ ⟨ι, hιN⟩ * Φ₂ ⟨y * ι, hyι⟩ * (ψ ⟨ι, hιN⟩)⁻¹ := by group
      _ = Φ₂ ⟨x * ι, hxι⟩ * ψ ⟨ι, hιN⟩ * (Φ₂ ⟨y * ι, hyι⟩ * ψ ⟨ι, hιN⟩) := by
        rw [inv_eq_of_mul_eq_one_right hψ]
        group

@[expose] noncomputable def vertexHom (hCr : Cr ≤ (Cr ⊓ C1) ⊔ (Cr ⊓ NR))
    (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) : ↥Nv →* G :=
  MonoidHom.mk' (vertexMap ψ Φ₂ hιN hNv) (vertexMap_mul σ ψ Φ₂ hι1 hιN hιι hιCr hC hA hB hCr hNv)

theorem vertexHom_apply (hCr : Cr ≤ (Cr ⊓ C1) ⊔ (Cr ⊓ NR))
    (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) (x : ↥Nv) :
    vertexHom σ ψ Φ₂ hι1 hιN hιι hιCr hC hA hB hCr hNv x = vertexMap ψ Φ₂ hιN hNv x := rfl

include hιι hB in
theorem vertexMap_eq_psi (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) {x : P} (hx : x ∈ Nv)
    (hxN : x ∈ NR) : vertexMap ψ Φ₂ hιN hNv ⟨x, hx⟩ = ψ ⟨x, hxN⟩ := by
  by_cases hxC : x ∈ Cr
  · rw [vertexMap_of_mem _ _ _ _ hx hxC, hB _ hxN hxC]
  · have hxι := (hNv x hx).resolve_left hxC
    rw [vertexMap_of_not_mem _ _ _ _ hx hxC, hB _ (NR.mul_mem hxN hιN) hxι, ← map_mul]
    congr 1
    apply Subtype.ext
    change x * ι * ι = x
    rw [mul_assoc, hιι, mul_one]

include hι1 hιι hC hA in
theorem vertexMap_eq_sigma (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr) {x : P} (hx : x ∈ Nv)
    (hx1 : x ∈ C1) : vertexMap ψ Φ₂ hιN hNv ⟨x, hx⟩ = (σ.symm ⟨x, hx1⟩ : G) := by
  by_cases hxC : x ∈ Cr
  · rw [vertexMap_of_mem _ _ _ _ hx hxC, hA _ hx1 hxC]
  · have hxι := (hNv x hx).resolve_left hxC
    rw [vertexMap_of_not_mem _ _ _ _ hx hxC, hA _ (C1.mul_mem hx1 hι1) hxι, hC _ hι1,
      ← coe_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    change x * ι * ι = x
    rw [mul_assoc, hιι, mul_one]

end Vertex

section Extension

variable {V : Type*} {Γ : SimpleGraph V} {T : Set V → Prop}
  {S C1 NR Cr Nv PS TS T1 : Subgroup P} [MulAction ↥S V]

theorem exists_hom_of_amalgam (D : TitsDataBy Γ T ↥S (Fin 2))
    (hXv : D.Xv = Nv.subgroupOf S) (hXe : D.Xe = PS.subgroupOf S)
    (hXt0 : D.Xt 0 = TS.subgroupOf S) (hXt1 : D.Xt 1 = T1.subgroupOf S)
    {ι : P} (hι1 : ι ∈ C1) (hιN : ι ∈ NR) (hιι : ι * ι = 1)
    (hιCr : ∀ c ∈ Cr, ι * c * ι⁻¹ ∈ Cr) (hCrNv : Cr ≤ Nv) (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr)
    (hCr : Cr ≤ (Cr ⊓ C1) ⊔ (Cr ⊓ NR)) (hPS : PS ≤ NR) (hTS : TS ≤ NR) (hT1 : T1 ≤ C1)
    {M : Subgroup G} (σ : ↥M ≃* ↥C1) (ψ : ↥NR →* G) (Φ₂ : ↥Cr →* G)
    (hC : ∀ x (hx : x ∈ C1) (hxN : x ∈ NR), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hA : ∀ x (hx : x ∈ C1) (hxC : x ∈ Cr), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hB : ∀ x (hxN : x ∈ NR) (hxC : x ∈ Cr), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩) :
    ∃ Φ : ↥S →* G,
      (∀ x (hxS : x ∈ S) (hxC : x ∈ Cr), Φ ⟨x, hxS⟩ = Φ₂ ⟨x, hxC⟩) ∧
      (∀ x (hxS : x ∈ S) (hxP : x ∈ PS), Φ ⟨x, hxS⟩ = ψ ⟨x, hPS hxP⟩) ∧
      (∀ x (hxS : x ∈ S) (hxT : x ∈ TS), Φ ⟨x, hxS⟩ = ψ ⟨x, hTS hxT⟩) ∧
      ∀ x (hxS : x ∈ S) (hxT : x ∈ T1), Φ ⟨x, hxS⟩ = (σ.symm ⟨x, hT1 hxT⟩ : G) := by
  set σi : ↥C1 →* G := M.subtype.comp σ.symm.toMonoidHom with hσi
  set φv : ↥D.Xv →* G := resHom (vertexHom σ ψ Φ₂ hι1 hιN hιι hιCr hC hA hB hCr hNv) D.Xv
    (fun a ha => mem_of_mem_subgroupOf hXv le_rfl ha) with hφv
  set φe : ↥D.Xe →* G := resHom ψ D.Xe (fun a ha => mem_of_mem_subgroupOf hXe hPS ha) with hφe
  have h0 : ∀ j : Fin 2, j = 0 → ∀ a ∈ D.Xt j, (a : P) ∈ NR := by
    rintro j rfl a ha
    exact mem_of_mem_subgroupOf hXt0 hTS ha
  have h1 : ∀ j : Fin 2, j ≠ 0 → ∀ a ∈ D.Xt j, (a : P) ∈ C1 := by
    intro j hj a ha
    have hj1 : j = 1 := by omega
    subst hj1
    exact mem_of_mem_subgroupOf hXt1 hT1 ha
  set φt : ∀ j, ↥(D.Xt j) →* G := fun j =>
    if hj : j = 0 then resHom ψ (D.Xt j) (h0 j hj) else resHom σi (D.Xt j) (h1 j hj) with hφt
  have hφt0 : ∀ j (hj : j = 0) (a : ↥(D.Xt j)), φt j a = ψ ⟨((a : ↥S) : P), h0 j hj a a.2⟩ := by
    intro j hj a
    rw [hφt]
    dsimp only
    rw [dite_eq_left hj]
    rfl
  have hφt1 : ∀ j (hj : j ≠ 0) (a : ↥(D.Xt j)),
      φt j a = (σ.symm ⟨((a : ↥S) : P), h1 j hj a a.2⟩ : G) := by
    intro j hj a
    rw [hφt]
    dsimp only
    rw [dite_eq_right hj]
    rfl
  have hve : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩ := by
    intro a ha hb
    rw [hφv, hφe, resHom_apply, resHom_apply, vertexHom_apply]
    exact vertexMap_eq_psi ψ Φ₂ hιN hιι hB hNv _ _
  have hvt : ∀ j a (ha : a ∈ D.Xv) (hb : a ∈ D.Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩ := by
    intro j a ha hb
    rw [hφv, resHom_apply, vertexHom_apply]
    by_cases hj : j = 0
    · rw [hφt0 j hj]
      exact vertexMap_eq_psi ψ Φ₂ hιN hιι hB hNv _ _
    · rw [hφt1 j hj]
      exact vertexMap_eq_sigma σ ψ Φ₂ hι1 hιN hιι hC hA hNv _ _
  have het : ∀ j a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩ := by
    intro j a ha hb
    rw [hφe, resHom_apply]
    by_cases hj : j = 0
    · rw [hφt0 j hj]
    · rw [hφt1 j hj]
      exact hC _ _ _
  obtain ⟨Φ, ⟨hΦv, hΦe, hΦt⟩, -⟩ := D.existsUnique_hom φv φe φt hve hvt het
  refine ⟨Φ, fun x hxS hxC => ?_, fun x hxS hxP => ?_, fun x hxS hxT => ?_,
    fun x hxS hxT => ?_⟩
  · have hmem : (⟨x, hxS⟩ : ↥S) ∈ D.Xv := by
      rw [hXv]
      exact hCrNv hxC
    rw [show (⟨x, hxS⟩ : ↥S) = ((⟨⟨x, hxS⟩, hmem⟩ : ↥D.Xv) : ↥S) from rfl, hΦv, hφv,
      resHom_apply, vertexHom_apply]
    exact vertexMap_of_mem ψ Φ₂ hιN hNv _ hxC
  · have hmem : (⟨x, hxS⟩ : ↥S) ∈ D.Xe := by
      rw [hXe]
      exact hxP
    rw [show (⟨x, hxS⟩ : ↥S) = ((⟨⟨x, hxS⟩, hmem⟩ : ↥D.Xe) : ↥S) from rfl, hΦe, hφe,
      resHom_apply]
  · have hmem : (⟨x, hxS⟩ : ↥S) ∈ D.Xt 0 := by
      rw [hXt0]
      exact hxT
    rw [show (⟨x, hxS⟩ : ↥S) = ((⟨⟨x, hxS⟩, hmem⟩ : ↥(D.Xt 0)) : ↥S) from rfl, hΦt,
      hφt0 0 rfl]
  · have hmem : (⟨x, hxS⟩ : ↥S) ∈ D.Xt 1 := by
      rw [hXt1]
      exact hxT
    rw [show (⟨x, hxS⟩ : ↥S) = ((⟨⟨x, hxS⟩, hmem⟩ : ↥(D.Xt 1)) : ↥S) from rfl, hΦt,
      hφt1 1 (by decide)]

theorem exists_hom_eq_sigma (D : TitsDataBy Γ T ↥S (Fin 2))
    (hXv : D.Xv = Nv.subgroupOf S) (hXe : D.Xe = PS.subgroupOf S)
    (hXt0 : D.Xt 0 = TS.subgroupOf S) (hXt1 : D.Xt 1 = T1.subgroupOf S)
    {ι : P} (hι1 : ι ∈ C1) (hιN : ι ∈ NR) (hιι : ι * ι = 1)
    (hιCr : ∀ c ∈ Cr, ι * c * ι⁻¹ ∈ Cr) (hCrNv : Cr ≤ Nv) (hNv : ∀ x ∈ Nv, x ∈ Cr ∨ x * ι ∈ Cr)
    (hCr : Cr ≤ (Cr ⊓ C1) ⊔ (Cr ⊓ NR)) (hPS : PS ≤ NR) (hTS : TS ≤ NR) (hT1 : T1 ≤ C1)
    (hC1S : C1 ≤ S) (hgen : C1 ≤ (C1 ⊓ Cr) ⊔ (C1 ⊓ PS))
    {M : Subgroup G} (σ : ↥M ≃* ↥C1) (ψ : ↥NR →* G) (Φ₂ : ↥Cr →* G)
    (hC : ∀ x (hx : x ∈ C1) (hxN : x ∈ NR), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hA : ∀ x (hx : x ∈ C1) (hxC : x ∈ Cr), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hB : ∀ x (hxN : x ∈ NR) (hxC : x ∈ Cr), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩) :
    ∃ Φ : ↥S →* G, ∀ x (hxS : x ∈ S) (hx : x ∈ C1), Φ ⟨x, hxS⟩ = (σ.symm ⟨x, hx⟩ : G) := by
  obtain ⟨Φ, hΦC, hΦP, -, -⟩ := exists_hom_of_amalgam D hXv hXe hXt0 hXt1 hι1 hιN hιι hιCr hCrNv
    hNv hCr hPS hTS hT1 σ ψ Φ₂ hC hA hB
  refine ⟨Φ, fun x hxS hx => ?_⟩
  have key := hom_ext_of_le_sup hgen (f := Φ.comp (inclusion hC1S))
    (g := M.subtype.comp σ.symm.toMonoidHom) (fun y hy hyC => ?_) (fun y hy hyP => ?_)
  · exact DFunLike.congr_fun key ⟨x, hx⟩
  · change Φ ⟨y, hC1S hy⟩ = (σ.symm ⟨y, hy⟩ : G)
    rw [hΦC y _ hyC, hA]
  · change Φ ⟨y, hC1S hy⟩ = (σ.symm ⟨y, hy⟩ : G)
    rw [hΦP y _ hyP, hC]

open CFSG.Sporadic.SuzOddCore in
theorem exists_hom_of_gluing_model {V : Type*} {Γ : SimpleGraph V} {T : Set V → Prop}
    [MulAction ↥suzM V] {Nv PS TS T1 : Subgroup (Equiv.Perm (Fin 1782))}
    {ι : Equiv.Perm (Fin 1782)} (D : TitsDataBy Γ T ↥suzM (Fin 2))
    (hXv : D.Xv = Nv.subgroupOf suzM) (hXe : D.Xe = PS.subgroupOf suzM)
    (hXt0 : D.Xt 0 = TS.subgroupOf suzM) (hXt1 : D.Xt 1 = T1.subgroupOf suzM)
    (hιB : ι ∈ Model.B0) (hιι : ι * ι = 1) (hιρ : ι * Model.rho1 * ι⁻¹ = Model.rho1⁻¹)
    (hNv : Nv = Model.Crho1 ⊔ zpowers ι)
    (hCr : Model.Crho1 = (Model.Crho1 ⊓ invE 1) ⊔ (Model.Crho1 ⊓ Model.NR0))
    (hPS : PS ≤ Model.NR0) (hTS : TS ≤ Model.NR0) (hT1 : T1 ≤ invE 1) (hE : invE 1 ≤ suzM)
    (hgen : invE 1 = (invE 1 ⊓ Model.Crho1) ⊔ (invE 1 ⊓ PS))
    {G : Type*} [Group G] {M : Subgroup G} (σ : ↥M ≃* ↥(invE 1)) (ψ : ↥Model.NR0 →* G)
    (Φ₂ : ↥Model.Crho1 →* G)
    (hC : ∀ x (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hA : ∀ x (hx : x ∈ invE 1) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hB : ∀ x (hxN : x ∈ Model.NR0) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩) :
    ∃ Φ : ↥suzM →* G, ∀ x (hxM : x ∈ suzM) (hx : x ∈ invE 1),
      Φ ⟨x, hxM⟩ = (σ.symm ⟨x, hx⟩ : G) := by
  have hι1 : ι ∈ invE 1 := hιB.1
  have hιS : ι ∈ suzM := hE hι1
  have hιN : ι ∈ Model.NR0 := ⟨hιS, hιB.2⟩
  have hιCr : ∀ c ∈ Model.Crho1, ι * c * ι⁻¹ ∈ Model.Crho1 := fun c hc =>
    conj_mem_centralizer_inf hιS hιρ hc
  refine exists_hom_eq_sigma D hXv hXe hXt0 hXt1 hι1 hιN hιι hιCr
    (hNv ▸ le_sup_left) (fun x hx => mem_or_mul_mem_of_mem_sup hιι hιCr (hNv ▸ hx)) hCr.le hPS
    hTS hT1 hE hgen.le σ ψ Φ₂ hC hA hB

end Extension

end CFSG.Sporadic.SuzRecog
