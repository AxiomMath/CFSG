module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch11SecOE3D
public import CFSG.Quasithin.Vol2.Ch11SecOE3F

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem conj_mem_cent {R K : Subgroup G} {k : G} (hk : k ∈ K) {c : G}
    (hc : c ∈ R ⊓ Subgroup.centralizer (K : Set G)) :
    k * c * k⁻¹ ∈ R ⊓ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff.mp hc.2 k hk, mul_inv_cancel_right]
  exact hc

theorem apply_mem_fixV_iff {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {b : MulAut V}
    (hb : b ∈ Subgroup.centralizer (H : Set (MulAut V))) (v : V) :
    b v ∈ fixV H ↔ v ∈ fixV H := by
  constructor
  · intro hv x hx
    apply b.injective
    rw [← MulAut.mul_apply _ b x, ← Subgroup.mem_centralizer_iff.mp hb x hx, MulAut.mul_apply]
    exact hv x hx
  · intro hv x hx
    rw [← MulAut.mul_apply _ x b, Subgroup.mem_centralizer_iff.mp hb x hx, MulAut.mul_apply,
      hv x hx]

variable [Finite G]

namespace Setting

variable {T K I : Subgroup G} {r : ℕ} (h : Setting G T K I r)
include h

theorem homog (J : Subgroup G)
    (hCJ : reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G) ≤ J)
    (hJV : J ≤ fsuV T I ⊔ reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G))
    (hKJ : K ≤ Subgroup.normalizer (J : Set G))
    (hiso : IsXSectionIso K (reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G)) J
      (I ⊔ reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G))) :
    J ≤ I ⊔ reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G) := by
  have := h.fsu.irrPlus.2.2.2.2.2.2
  rw [show conjClosure K T = K from h.fsuL0_eq] at this
  exact this J hCJ hJV hKJ hiso

theorem comm_mem_of_mem_sup {g : G}
    (hg : g ∈ I ⊔ reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G)) {k : G}
    (hk : k ∈ K) : k * g * k⁻¹ * g⁻¹ ∈ I := by
  have hR := (Vol2.Ch11.SecA.reducedAggregate_props (K ⊔ T)).2.1
  have hIR : I ≤ reducedAggregate (K ⊔ T) := h.fsu.irrPlus.1
  let D : Subgroup G :=
    { carrier := {g | g ∈ reducedAggregate (K ⊔ T) ∧ ∀ k ∈ K, k * g * k⁻¹ * g⁻¹ ∈ I}
      one_mem' := ⟨Subgroup.one_mem _, fun k _ => by simp⟩
      mul_mem' := by
        rintro a c ⟨ha, ha'⟩ ⟨hc, hc'⟩
        refine ⟨Subgroup.mul_mem _ ha hc, fun k hk => ?_⟩
        have h1 := ha' k hk
        have h2 := hc' k hk
        have hcomm : a * (k * c * k⁻¹ * c⁻¹) = (k * c * k⁻¹ * c⁻¹) * a := hR _ ha _ (hIR h2)
        have e : k * (a * c) * k⁻¹ * (a * c)⁻¹ =
            (k * a * k⁻¹ * a⁻¹) * (a * (k * c * k⁻¹ * c⁻¹) * a⁻¹) := by group
        rw [e, hcomm, mul_inv_cancel_right]
        exact I.mul_mem h1 h2
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun k hk => ?_⟩
        have h1 := ha' k hk
        have hcomm : a⁻¹ * (k * a * k⁻¹ * a⁻¹)⁻¹ = (k * a * k⁻¹ * a⁻¹)⁻¹ * a⁻¹ :=
          hR _ (Subgroup.inv_mem _ ha) _ (Subgroup.inv_mem _ (hIR h1))
        have e : k * a⁻¹ * k⁻¹ * a⁻¹⁻¹ = a⁻¹ * (k * a * k⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e, hcomm, inv_mul_cancel_right]
        exact I.inv_mem h1 }
  have hle : I ⊔ reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G) ≤ D := by
    refine sup_le (fun i hi => ⟨hIR hi, fun k hk => I.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer_I hk) i).mp hi) (I.inv_mem hi)⟩)
      (fun c hc => ⟨hc.1, fun k hk => ?_⟩)
    rw [Subgroup.mem_centralizer_iff.mp hc.2 k hk, mul_inv_cancel_right, mul_inv_cancel]
    exact I.one_mem
  exact (hle hg).2 k hk

theorem coe_apply_conj {b : MulAut ↥(fsuV T I)}
    (hb : b ∈ Subgroup.centralizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I)))) {k : G}
    (hk : k ∈ K) (v : ↥(fsuV T I)) (hv : k * v * k⁻¹ ∈ fsuV T I) :
    ((b ⟨k * v * k⁻¹, hv⟩ : ↥(fsuV T I)) : G) = k * (b v : G) * k⁻¹ := by
  have hkN := h.le_normalizer_V hk
  have hx : conjAct (fsuV T I) ⟨k, hkN⟩ ∈ autOn K (fsuV T I) :=
    Ch10.SecA.mem_autOn_iff'.mpr ⟨⟨k, hkN⟩, hk, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp hb _ hx
  have e : (⟨k * v * k⁻¹, hv⟩ : ↥(fsuV T I)) = conjAct (fsuV T I) ⟨k, hkN⟩ v :=
    Subtype.ext (Ch10.SecA.coe_conjAct_apply' ⟨k, hkN⟩ v).symm
  rw [e, ← MulAut.mul_apply, ← hc, MulAut.mul_apply, Ch10.SecA.coe_conjAct_apply']

variable [IsMulCommutative ↥(fsuV T I)]

theorem coe_mem_cent_iff (v : ↥(fsuV T I)) :
    (v : G) ∈ reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G) ↔
      v ∈ fixV (autOn K (fsuV T I)) := by
  rw [Ch10.SecA.mem_fixV_autOn h.le_normalizer_V v, Subgroup.mem_inf]
  exact ⟨fun hv => hv.2, fun hv => ⟨h.le_reducedAggregate v.2, hv⟩⟩

omit [IsMulCommutative ↥(fsuV T I)] in
theorem le_normalizer_sup {b : MulAut ↥(fsuV T I)}
    (hb : b ∈ Subgroup.centralizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I)))) :
    K ≤ Subgroup.normalizer
      ((((I.subgroupOf (fsuV T I)).map b.toMonoidHom).map (fsuV T I).subtype ⊔
        reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  have hmap : ∀ W : Subgroup ↥(fsuV T I), (W.map (fsuV T I).subtype).subgroupOf (fsuV T I) = W :=
    fun W => Subgroup.comap_map_eq_self_of_injective (fsuV T I).subtype_injective W
  refine le_trans (le_inf ?_ ?_) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  · rw [← inv_autOn_iff h.le_normalizer_V (Subgroup.map_subtype_le _), hmap]
    rintro x hx _ ⟨i, hi, rfl⟩
    refine ⟨x i, (inv_autOn_iff h.le_normalizer_V (I_le_V T I)).mpr h.le_normalizer_I x hx i hi,
      ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← MulAut.mul_apply _ b x, ← Subgroup.mem_centralizer_iff.mp hb x hx, MulAut.mul_apply]
  · intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => conj_mem_cent hk hc, fun hc => ?_⟩
    have := conj_mem_cent (K.inv_mem hk) hc
    simpa [mul_assoc] using this

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE3
