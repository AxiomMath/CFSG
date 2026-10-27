module

public import CFSG.Quasithin.Recognition.F112J2Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F112W

namespace F112J2

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem borelOf_L2_le_S (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) : borelOf L2 S ≤ S := by
  rw [borelOf_eq_inf_of_perm3 h.hyp.h2.sylow h.s3 hR.r2.borel_ne]
  exact inf_le_left

theorem bigB_le_centralizer_Z (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    bigB K1 L2 S ≤ Subgroup.centralizer (Zs : Set G) := by
  have hS := S_le_centralizer_Z h
  have h1 : borelOf K1 S ≤ Subgroup.centralizer (Zs : Set G) :=
    (F1.borelOf_le K1 S).trans h.K1_cent_Z
  have h2 : borelOf L2 S ≤ Subgroup.centralizer (Zs : Set G) :=
    (borelOf_L2_le_S h hR).trans hS
  exact sup_le (sup_le h1 h2) hS

omit [Finite G] in
theorem mem_normalizer_conjClosure_of {b : G} {Z H : Subgroup G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G)) (hbZ : b ∈ Subgroup.centralizer (Z : Set G)) :
    b ∈ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ c : G, c ∈ Subgroup.normalizer (H : Set G) →
      c ∈ Subgroup.centralizer (Z : Set G) →
      ∀ x ∈ conjClosure Z H, c * x * c⁻¹ ∈ conjClosure Z H := by
    intro c hcH hcZ x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, z, hz, rfl⟩ := hx
      have hcz : z * c = c * z := Subgroup.mem_centralizer_iff.mp hcZ z hz
      have hk' : c * k * c⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hcH k).mp hk
      have hcz' : c * z * c⁻¹ = z := by
        rw [← hcz]
        group
      have e : c * (k * z * k⁻¹) * c⁻¹ = (c * k * c⁻¹) * z * (c * k * c⁻¹)⁻¹ := by
        calc c * (k * z * k⁻¹) * c⁻¹ = (c * k * c⁻¹) * (c * z * c⁻¹) * (c * k * c⁻¹)⁻¹ := by group
          _ = (c * k * c⁻¹) * z * (c * k * c⁻¹)⁻¹ := by rw [hcz']
      rw [e]
      exact mem_conjClosure hk' hz
    | one => simp
    | mul x y _ _ ihx ihy =>
      simpa [mul_assoc] using (conjClosure Z H).mul_mem ihx ihy
    | inv x _ ih =>
      simpa [mul_assoc] using (conjClosure Z H).inv_mem ih
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key b hbH hbZ x
  · intro hx
    have := key b⁻¹ ((Subgroup.normalizer (H : Set G)).inv_mem hbH)
      ((Subgroup.centralizer (Z : Set G)).inv_mem hbZ) _ hx
    simpa [mul_assoc] using this

theorem bigB_le_normalizer_V (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    bigB K1 L2 S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) := fun _ hb =>
  mem_normalizer_conjClosure_of ((F1.bigB_le_normalizer_left hR).2 hb) (bigB_le_centralizer_Z h hR hb)

omit [Finite G] in
theorem inv_mul_mem_of_not_mem {V Z : Subgroup G} (hidx : (Z.subgroupOf V).index = 2)
    {x w : G} (hx : x ∈ V) (hw : w ∈ V) (hxZ : x ∉ Z) (hwZ : w ∉ Z) : x⁻¹ * w ∈ Z := by
  have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x⁻¹, V.inv_mem hx⟩)
    (b := ⟨w, hw⟩)).mpr (by
      constructor
      · intro ha
        have h1 : x⁻¹ ∈ Z := Subgroup.mem_subgroupOf.mp ha
        exact absurd (by simpa using Z.inv_mem h1) hxZ
      · intro hb
        exact absurd (Subgroup.mem_subgroupOf.mp hb) hwZ)
  exact Subgroup.mem_subgroupOf.mp h1

end F112J2

end CFSG.Quasithin
