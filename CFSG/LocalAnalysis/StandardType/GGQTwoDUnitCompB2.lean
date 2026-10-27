module
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.LocalCores.Fitting
public section
namespace CFSG.StandardType.QTwo
open CFSG
open scoped commutatorElement
private theorem qtwoDB7_b2_mem_sup_iff_of_commute {G : Type} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ K, Commute x y) {z : G} :
    z ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, x * y = z := by
  constructor
  · intro hz
    let P : Subgroup G :=
      { carrier := {z | ∃ x ∈ H, ∃ y ∈ K, x * y = z}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
        mul_mem' := by
          rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
          refine ⟨x₁ * x₂, H.mul_mem hx₁ hx₂, y₁ * y₂, K.mul_mem hy₁ hy₂, ?_⟩
          have hc : x₂ * y₁ = y₁ * x₂ := (h x₂ hx₂ y₁ hy₁).eq
          calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
            _ = x₁ * (y₁ * x₂) * y₂ := by rw [hc]
            _ = x₁ * y₁ * (x₂ * y₂) := by group
        inv_mem' := by
          rintro _ ⟨x, hx, y, hy, rfl⟩
          refine ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, ?_⟩
          have hc : x * y = y * x := (h x hx y hy).eq
          calc x⁻¹ * y⁻¹ = (y * x)⁻¹ := by group
            _ = (x * y)⁻¹ := by rw [hc] }
    have hle : H ⊔ K ≤ P := sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun y hy => ⟨1, H.one_mem, y, hy, one_mul y⟩)
    exact hle hz
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
private theorem qtwoDB7_b2_mem_sup3_iff_of_commute {G : Type} [Group G]
    {A0 A1 A2 : Subgroup G}
    (h01 : ∀ x ∈ A0, ∀ y ∈ A1, Commute x y)
    (h02 : ∀ x ∈ A0, ∀ y ∈ A2, Commute x y)
    (h12 : ∀ x ∈ A1, ∀ y ∈ A2, Commute x y) {z : G} :
    z ∈ A0 ⊔ A1 ⊔ A2 ↔ ∃ a ∈ A0, ∃ b ∈ A1, ∃ c ∈ A2, a * b * c = z := by
  have hA0A1 : ∀ x ∈ A0 ⊔ A1, ∀ y ∈ A2, Commute x y := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (qtwoDB7_b2_mem_sup_iff_of_commute h01).mp hx
    exact (h02 a ha y hy).mul_left (h12 b hb y hy)
  constructor
  · intro hz
    obtain ⟨x, hx, c, hc, rfl⟩ := (qtwoDB7_b2_mem_sup_iff_of_commute hA0A1).mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := (qtwoDB7_b2_mem_sup_iff_of_commute h01).mp hx
    exact ⟨a, ha, b, hb, c, hc, rfl⟩
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right hc)
private theorem qtwoDB7_b2_commute_of_isComponent_ne {G : Type} [Group G] [Finite G]
    {K L : Subgroup G} (hK : CFSG.IsComponent K) (hL : CFSG.IsComponent L) (hne : K ≠ L) :
    ∀ x ∈ K, ∀ y ∈ L, Commute x y := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · intro x hx y hy
    have hc : K ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (Subgroup.mem_centralizer_iff.mp (hc hx) y hy).symm
private theorem qtwoDB7_b2_mul_rearrange {G : Type} [Group G] {x y a1 a2 b1 b2 : G}
    (hy1 : Commute y a1) (hy2 : Commute y a2) (hyb1 : Commute y b1)
    (hb1a2 : Commute b1 a2) :
    (x * y) * (a1 * b1) * (a2 * b2) = (x * a1 * a2) * (y * b1 * b2) := by
  calc (x * y) * (a1 * b1) * (a2 * b2)
      = x * (y * (a1 * (b1 * (a2 * b2)))) := by group
    _ = x * (a1 * (y * (b1 * (a2 * b2)))) := by
          rw [← mul_assoc y a1 (b1 * (a2 * b2)), hy1.eq, mul_assoc]
    _ = x * (a1 * (b1 * (y * (a2 * b2)))) := by rw [← mul_assoc y b1 (a2 * b2), hyb1.eq, mul_assoc]
    _ = x * (a1 * (b1 * (a2 * (y * b2)))) := by rw [← mul_assoc y a2 b2, hy2.eq, mul_assoc]
    _ = x * (a1 * (a2 * (b1 * (y * b2)))) := by rw [← mul_assoc b1 a2 (y * b2), hb1a2.eq, mul_assoc]
    _ = x * (a1 * (a2 * (y * (b1 * b2)))) := by rw [← mul_assoc b1 y b2, hyb1.eq.symm, mul_assoc]
    _ = (x * a1 * a2) * (y * b1 * b2) := by group
private theorem qtwoDB7_b2_mul_commute_cycle {G : Type} [Group G] {u v w : G}
    (huv : Commute u v) (huw : Commute u w) (hvw : Commute v w) :
    u * v * w = w * u * v := by
  calc u * v * w = (u * v) * w := rfl
    _ = (v * u) * w := by rw [huv.eq]
    _ = v * (u * w) := by group
    _ = v * (w * u) := by rw [huw.eq]
    _ = (v * w) * u := by group
    _ = (w * v) * u := by rw [hvw.eq]
    _ = w * (v * u) := by group
    _ = w * (u * v) := by rw [huv.eq]
    _ = w * u * v := by group
private theorem qtwoDB7_b2_commutator_mul_of_central {G : Type} [Group G] {a b r s : G}
    (hrb : r * b = b * r) (hrs : r * s = s * r) (hsa : s * a = a * s) :
    ⁅a * r, b * s⁆ = ⁅a, b⁆ := by
  have hrb' : r * b⁻¹ = b⁻¹ * r := by
    calc r * b⁻¹ = b⁻¹ * (b * r) * b⁻¹ := by group
      _ = b⁻¹ * (r * b) * b⁻¹ := by rw [hrb]
      _ = b⁻¹ * r := by group
  have hsa' : s * a⁻¹ = a⁻¹ * s := by
    calc s * a⁻¹ = a⁻¹ * (a * s) * a⁻¹ := by group
      _ = a⁻¹ * (s * a) * a⁻¹ := by rw [hsa]
      _ = a⁻¹ * s := by group
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * r * (b * s) * (r⁻¹ * a⁻¹) * (s⁻¹ * b⁻¹)
      = a * (r * b) * s * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by group
    _ = a * (b * r) * s * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by rw [hrb]
    _ = a * b * (r * s) * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by group
    _ = a * b * (s * r) * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by rw [hrs]
    _ = a * b * s * a⁻¹ * s⁻¹ * b⁻¹ := by group
    _ = a * b * (s * a⁻¹) * s⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * s) * s⁻¹ * b⁻¹ := by rw [hsa']
    _ = a * b * a⁻¹ * b⁻¹ := by group
private theorem qtwoDB7_b2_commutator_eq_self_of_isPerfect {G : Type} [Group G]
    {S : Subgroup G} (hS : Group.IsPerfect S) : ⁅S, S⁆ = S := by
  have h := congrArg (Subgroup.map S.subtype) (Group.isPerfect_def.1 hS)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h
private theorem qtwoDB7_b2_subnormal_eq_top_or_le_center {Q : Type} [Group Q]
    (hq : CFSG.IsQuasisimple Q) {H : Subgroup Q} (hH : H.IsSubnormal) :
    H = ⊤ ∨ H ≤ Subgroup.center Q := by
  induction hH with
  | top => exact Or.inl rfl
  | step H K hle hK hN ih =>
    rcases ih with rfl | hKc
    · have hHn : H.Normal := by
        refine ⟨fun n hn g => ?_⟩
        have := (Subgroup.normal_subgroupOf_iff (H := H) (K := ⊤) hle).1 hN n g hn
          (Subgroup.mem_top g)
        exact this
      exact CFSG.LocalCores.quasisimple_normal_subgroups hq hHn
    · exact Or.inr (hle.trans hKc)
private theorem qtwoDB7_b2_sup_le_centralizer {G : Type} [Group G] {A B C : Subgroup G}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, Commute x y) (hAC : ∀ x ∈ A, ∀ y ∈ C, Commute x y) :
    B ⊔ C ≤ Subgroup.centralizer (A : Set G) := by
  refine sup_le ?_ ?_
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hAB a ha b hb).eq
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hAC a ha c hc).eq
private theorem qtwoDB7_b2_commutator_sup_le {G : Type} [Group G] {D Z : Subgroup G}
    (hZ : Z ≤ Subgroup.centralizer ((D ⊔ Z : Subgroup G) : Set G)) :
    ⁅D ⊔ Z, D ⊔ Z⁆ ≤ D := by
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  have hcomm : ∀ u ∈ D, ∀ v ∈ Z, Commute u v := fun u hu v hv =>
    Subgroup.mem_centralizer_iff.mp (hZ hv) u (Subgroup.mem_sup_left hu)
  obtain ⟨dx, hdx, zx, hzx, rfl⟩ := (qtwoDB7_b2_mem_sup_iff_of_commute hcomm).mp hx
  obtain ⟨dy, hdy, zy, hzy, rfl⟩ := (qtwoDB7_b2_mem_sup_iff_of_commute hcomm).mp hy
  have hzx_c : ∀ w ∈ D ⊔ Z, zx * w = w * zx := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp (hZ hzx) w hw).symm
  have hzy_c : ∀ w ∈ D ⊔ Z, zy * w = w * zy := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp (hZ hzy) w hw).symm
  rw [qtwoDB7_b2_commutator_mul_of_central
    (hzx_c dy (Subgroup.mem_sup_left hdy))
    (hzx_c zy (Subgroup.mem_sup_right hzy))
    (hzy_c dx (Subgroup.mem_sup_left hdx))]
  exact Subgroup.commutator_le_self D (Subgroup.commutator_mem_commutator hdx hdy)
theorem qtwoDB7_diag_cover {Y : Type} [Group Y] [Finite Y] {τ : Y} (hτ : τ ^ 3 = 1)
    {A Jb : Subgroup Y} (hA : CFSG.IsComponent A)
    (h01 : A ≠ A.map (MulAut.conj τ).toMonoidHom)
    (h02 : A ≠ A.map (MulAut.conj (τ ^ 2)).toMonoidHom)
    (h12 : A.map (MulAut.conj τ).toMonoidHom ≠ A.map (MulAut.conj (τ ^ 2)).toMonoidHom)
    (hJq : CFSG.IsQuasisimple Jb) (hJC : Jb ≤ Subgroup.centralizer ({τ} : Set Y))
    (hJs : CFSG.IsComponent (Jb.subgroupOf (Subgroup.centralizer ({τ} : Set Y))))
    (hJA : Jb ≤ A ⊔ A.map (MulAut.conj τ).toMonoidHom ⊔ A.map (MulAut.conj (τ ^ 2)).toMonoidHom) :
    ∃ φ : ↥A →* ↥Jb, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥A ∧
      ∀ a : ↥A, ((φ a : ↥Jb) : Y) =
        (a : Y) * (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) := by
  set A1 : Subgroup Y := A.map (MulAut.conj τ).toMonoidHom with hA1def
  set A2 : Subgroup Y := A.map (MulAut.conj (τ ^ 2)).toMonoidHom with hA2def
  have hA1c : CFSG.IsComponent A1 := by
    rw [hA1def]; exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj τ) hA
  have hA2c : CFSG.IsComponent A2 := by
    rw [hA2def]; exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (τ ^ 2)) hA
  have c01 : ∀ x ∈ A, ∀ y ∈ A1, Commute x y :=
    qtwoDB7_b2_commute_of_isComponent_ne hA hA1c h01
  have c02 : ∀ x ∈ A, ∀ y ∈ A2, Commute x y :=
    qtwoDB7_b2_commute_of_isComponent_ne hA hA2c h02
  have c12 : ∀ x ∈ A1, ∀ y ∈ A2, Commute x y :=
    qtwoDB7_b2_commute_of_isComponent_ne hA1c hA2c h12
  have hmem1 : ∀ a ∈ A, τ * a * τ⁻¹ ∈ A1 := by
    intro a ha; rw [hA1def]; exact Subgroup.mem_map_of_mem ((MulAut.conj τ).toMonoidHom) ha
  have hmem2 : ∀ a ∈ A, τ ^ 2 * a * (τ ^ 2)⁻¹ ∈ A2 := by
    intro a ha; rw [hA2def]
    exact Subgroup.mem_map_of_mem ((MulAut.conj (τ ^ 2)).toMonoidHom) ha
  have hmem1' : ∀ a ∈ A1, τ * a * τ⁻¹ ∈ A2 := by
    intro a ha; rw [hA1def] at ha
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp ha
    rw [hA2def]
    have h2 : τ ^ 2 * a' * (τ ^ 2)⁻¹
        ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (τ ^ 2))) A :=
      Subgroup.mem_map_of_mem ((MulAut.conj (τ ^ 2)).toMonoidHom) ha'
    rw [← haeq]
    change τ * (τ * a' * τ⁻¹) * τ⁻¹
      ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (τ ^ 2))) A
    convert h2 using 1
    rw [pow_two]; group
  have hmem0 : ∀ a ∈ A2, τ * a * τ⁻¹ ∈ A := by
    intro a ha; rw [hA2def] at ha
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp ha
    rw [← haeq]
    change τ * (τ ^ 2 * a' * (τ ^ 2)⁻¹) * τ⁻¹ ∈ A
    convert ha' using 1
    calc τ * (τ ^ 2 * a' * (τ ^ 2)⁻¹) * τ⁻¹ = τ ^ 3 * a' * (τ ^ 3)⁻¹ := by group
      _ = a' := by rw [hτ]; group
  let d : ↥A →* Y :=
    { toFun := fun a => (a : Y) * (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hy1 : Commute (b : Y) (τ * (a : Y) * τ⁻¹) :=
          c01 (b : Y) b.2 _ (hmem1 (a : Y) a.2)
        have hy2 : Commute (b : Y) (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) :=
          c02 (b : Y) b.2 _ (hmem2 (a : Y) a.2)
        have hyb1 : Commute (b : Y) (τ * (b : Y) * τ⁻¹) :=
          c01 (b : Y) b.2 _ (hmem1 (b : Y) b.2)
        have hb1a2 : Commute (τ * (b : Y) * τ⁻¹) (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) :=
          c12 _ (hmem1 (b : Y) b.2) _ (hmem2 (a : Y) a.2)
        have e1 : τ * ((a : Y) * (b : Y)) * τ⁻¹ =
            (τ * (a : Y) * τ⁻¹) * (τ * (b : Y) * τ⁻¹) := by group
        have e2 : τ ^ 2 * ((a : Y) * (b : Y)) * (τ ^ 2)⁻¹ =
            (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) * (τ ^ 2 * (b : Y) * (τ ^ 2)⁻¹) := by group
        simp only [Subgroup.coe_mul]
        rw [e1, e2]
        exact qtwoDB7_b2_mul_rearrange hy1 hy2 hyb1 hb1a2 }
  have hd : ∀ a : ↥A,
      d a = (a : Y) * (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) :=
    fun a => rfl
  have hd_conj : ∀ a : ↥A, τ * d a * τ⁻¹ = d a := by
    intro a
    have h2 : τ * (τ * (a : Y) * τ⁻¹) * τ⁻¹ = τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹ := by rw [pow_two]; group
    have h3 : τ * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) * τ⁻¹ = (a : Y) := by
      calc τ * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) * τ⁻¹ = τ ^ 3 * (a : Y) * (τ ^ 3)⁻¹ := by group
        _ = (a : Y) := by rw [hτ]; group
    have hdist : τ * d a * τ⁻¹
        = (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) * (a : Y) := by
      rw [hd a]
      calc τ * ((a : Y) * (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹)) * τ⁻¹
          = (τ * (a : Y) * τ⁻¹) * (τ * (τ * (a : Y) * τ⁻¹) * τ⁻¹)
              * (τ * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) * τ⁻¹) := by group
        _ = (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) * (a : Y) := by rw [h2, h3]
    have hcyc : (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) * (a : Y)
        = (a : Y) * (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹) :=
      qtwoDB7_b2_mul_commute_cycle (c12 _ (hmem1 (a : Y) a.2) _ (hmem2 (a : Y) a.2))
        (c01 (a : Y) a.2 _ (hmem1 (a : Y) a.2)).symm
        (c02 (a : Y) a.2 _ (hmem2 (a : Y) a.2)).symm
    exact hdist.trans (hcyc.trans (hd a).symm)
  have hDcent : d.range ≤ Subgroup.centralizer ({τ} : Set Y) := by
    rintro _ ⟨a, rfl⟩; rw [Subgroup.mem_centralizer_iff]
    intro t ht; rw [Set.mem_singleton_iff] at ht; rw [ht]
    calc τ * d a = (τ * d a * τ⁻¹) * τ := by group
      _ = d a * τ := by rw [hd_conj a]
  have hA1A2_cent : A1 ⊔ A2 ≤ Subgroup.centralizer (A : Set Y) :=
    qtwoDB7_b2_sup_le_centralizer c01 c02
  have hAA2_cent : A ⊔ A2 ≤ Subgroup.centralizer (A1 : Set Y) :=
    qtwoDB7_b2_sup_le_centralizer (fun x hx y hy => (c01 y hy x hx).symm) c12
  have hAA1_cent : A ⊔ A1 ≤ Subgroup.centralizer (A2 : Set Y) :=
    qtwoDB7_b2_sup_le_centralizer (fun x hx y hy => (c02 y hy x hx).symm)
      (fun x hx y hy => (c12 y hy x hx).symm)
  have hker : d.ker ≤ Subgroup.center ↥A := by
    intro a ha; rw [MonoidHom.mem_ker] at ha
    rw [Subgroup.mem_center_iff]; intro g
    apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have ha_eq : (a : Y) = ((τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹))⁻¹ := by
      have h := ha
      rw [hd a] at h
      calc (a : Y) = ((a : Y) * (τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹))
            * ((τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹))⁻¹ := by group
        _ = ((τ * (a : Y) * τ⁻¹) * (τ ^ 2 * (a : Y) * (τ ^ 2)⁻¹))⁻¹ := by rw [h]; group
    have hmem : (a : Y) ∈ A1 ⊔ A2 := by
      rw [ha_eq]
      exact Subgroup.inv_mem _ (mul_mem (Subgroup.mem_sup_left (hmem1 (a : Y) a.2))
        (Subgroup.mem_sup_right (hmem2 (a : Y) a.2)))
    exact Subgroup.mem_centralizer_iff.mp (hA1A2_cent hmem) (g : Y) g.2
  have hDq : CFSG.IsQuasisimple ↥(d.range) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hA.1 d.rangeRestrict
      d.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
  set Z0 : Subgroup Y := A ⊓ (A1 ⊔ A2) with hZ0def
  set Z1 : Subgroup Y := A1 ⊓ (A ⊔ A2) with hZ1def
  set Z2 : Subgroup Y := A2 ⊓ (A ⊔ A1) with hZ2def
  set Z : Subgroup Y := Z0 ⊔ Z1 ⊔ Z2 with hZdef
  have hZ0cent : Z0 ≤ Subgroup.centralizer ((A ⊔ A1 ⊔ A2 : Subgroup Y) : Set Y) := by
    intro z hz
    rw [hZ0def] at hz; rw [Subgroup.mem_centralizer_iff]; intro x hx
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ :=
      (qtwoDB7_b2_mem_sup3_iff_of_commute c01 c02 c12).mp hx
    have hza : Commute z a := (Subgroup.mem_centralizer_iff.mp (hA1A2_cent hz.2) a ha).symm
    have hzb : Commute z b := c01 z hz.1 b hb
    have hzc : Commute z c := c02 z hz.1 c hc
    exact ((hza.mul_right hzb).mul_right hzc).eq.symm
  have hZ1cent : Z1 ≤ Subgroup.centralizer ((A ⊔ A1 ⊔ A2 : Subgroup Y) : Set Y) := by
    intro z hz
    rw [hZ1def] at hz; rw [Subgroup.mem_centralizer_iff]; intro x hx
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ :=
      (qtwoDB7_b2_mem_sup3_iff_of_commute c01 c02 c12).mp hx
    have hza : Commute z a := (c01 a ha z hz.1).symm
    have hzb : Commute z b := (Subgroup.mem_centralizer_iff.mp (hAA2_cent hz.2) b hb).symm
    have hzc : Commute z c := c12 z hz.1 c hc
    exact ((hza.mul_right hzb).mul_right hzc).eq.symm
  have hZ2cent : Z2 ≤ Subgroup.centralizer ((A ⊔ A1 ⊔ A2 : Subgroup Y) : Set Y) := by
    intro z hz
    rw [hZ2def] at hz; rw [Subgroup.mem_centralizer_iff]; intro x hx
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ :=
      (qtwoDB7_b2_mem_sup3_iff_of_commute c01 c02 c12).mp hx
    have hza : Commute z a := (c02 a ha z hz.1).symm
    have hzb : Commute z b := (c12 b hb z hz.1).symm
    have hzc : Commute z c := (Subgroup.mem_centralizer_iff.mp (hAA1_cent hz.2) c hc).symm
    exact ((hza.mul_right hzb).mul_right hzc).eq.symm
  have hZcent : Z ≤ Subgroup.centralizer ((A ⊔ A1 ⊔ A2 : Subgroup Y) : Set Y) := by
    rw [hZdef]; exact sup_le (sup_le hZ0cent hZ1cent) hZ2cent
  have hDrange_le : d.range ≤ A ⊔ A1 ⊔ A2 := by
    rintro _ ⟨a, rfl⟩
    rw [hd a]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left a.2))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hmem1 (a : Y) a.2))))
      (Subgroup.mem_sup_right (hmem2 (a : Y) a.2))
  have hZ0_le : Z0 ≤ A ⊔ A1 ⊔ A2 :=
    inf_le_right.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hZ1_le : Z1 ≤ A ⊔ A1 ⊔ A2 :=
    inf_le_right.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hZ2_le : Z2 ≤ A ⊔ A1 ⊔ A2 := inf_le_right.trans le_sup_left
  have hZ_le : Z ≤ A ⊔ A1 ⊔ A2 := by rw [hZdef]; exact sup_le (sup_le hZ0_le hZ1_le) hZ2_le
  have hZcent' : Z ≤ Subgroup.centralizer ((d.range ⊔ Z : Subgroup Y) : Set Y) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxbig : x ∈ A ⊔ A1 ⊔ A2 := by
      obtain ⟨d1, hd1, z1, hz1, rfl⟩ :=
        (qtwoDB7_b2_mem_sup_iff_of_commute
          (fun u hu v hv =>
            Subgroup.mem_centralizer_iff.mp (hZcent hv) u (hDrange_le hu))).mp hx
      exact mul_mem (hDrange_le hd1) (hZ_le hz1)
    exact Subgroup.mem_centralizer_iff.mp (hZcent hz) x hxbig
  have hJb_le : Jb ≤ d.range ⊔ Z := by
    intro j hj
    obtain ⟨a, ha, b, hb, c, hc, hjc⟩ :=
      (qtwoDB7_b2_mem_sup3_iff_of_commute c01 c02 c12).mp (hJA hj)
    have hfix : τ * j * τ⁻¹ = j := by
      rw [Subgroup.mem_centralizer_iff.mp (hJC hj) τ (Set.mem_singleton τ)]; group
    have hconj : (τ * a * τ⁻¹) * (τ * b * τ⁻¹) * (τ * c * τ⁻¹) = a * b * c := by
      rw [← hjc] at hfix
      have h1 : τ * (a * b * c) * τ⁻¹
          = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) * (τ * c * τ⁻¹) := by group
      rw [← h1]; exact hfix
    have hcycle : (τ * a * τ⁻¹) * (τ * b * τ⁻¹) * (τ * c * τ⁻¹)
        = (τ * c * τ⁻¹) * (τ * a * τ⁻¹) * (τ * b * τ⁻¹) :=
      qtwoDB7_b2_mul_commute_cycle (c12 _ (hmem1 a ha) _ (hmem1' b hb))
        ((c01 (τ * c * τ⁻¹) (hmem0 c hc) _ (hmem1 a ha)).symm)
        ((c02 (τ * c * τ⁻¹) (hmem0 c hc) _ (hmem1' b hb)).symm)
    have hcba : (τ * c * τ⁻¹) * (τ * a * τ⁻¹) * (τ * b * τ⁻¹) = a * b * c := by
      rw [← hcycle]; exact hconj
    let z1 : Y := b⁻¹ * (τ * a * τ⁻¹)
    let z2 : Y := (τ * b * τ⁻¹) * c⁻¹
    let z2' : Y := τ * z1 * τ⁻¹
    have hz1eq : z1 = b⁻¹ * (τ * a * τ⁻¹) := rfl
    have hz2eq : z2 = (τ * b * τ⁻¹) * c⁻¹ := rfl
    have hz2'eq : z2' = τ * z1 * τ⁻¹ := rfl
    have hz1 : z1 ∈ Z1 := by
      rw [hZ1def]
      have ha1eq : (τ * a * τ⁻¹)
          = (τ * c * τ⁻¹)⁻¹ * a * b * c * (τ * b * τ⁻¹)⁻¹ := by
        calc (τ * a * τ⁻¹)
            = (τ * c * τ⁻¹)⁻¹ * ((τ * c * τ⁻¹) * (τ * a * τ⁻¹) * (τ * b * τ⁻¹))
                * (τ * b * τ⁻¹)⁻¹ := by group
          _ = (τ * c * τ⁻¹)⁻¹ * (a * b * c) * (τ * b * τ⁻¹)⁻¹ := by rw [hcba]
          _ = (τ * c * τ⁻¹)⁻¹ * a * b * c * (τ * b * τ⁻¹)⁻¹ := by group
      have hb_c1 : Commute b (τ * c * τ⁻¹) := (c01 (τ * c * τ⁻¹) (hmem0 c hc) b hb).symm
      have hb_a : Commute b a := (c01 a ha b hb).symm
      have hz1eq' : z1 = (τ * c * τ⁻¹)⁻¹ * a * c * (τ * b * τ⁻¹)⁻¹ := by
        calc z1 = b⁻¹ * ((τ * c * τ⁻¹)⁻¹ * a * b * c * (τ * b * τ⁻¹)⁻¹) := by
              rw [hz1eq, ha1eq]
          _ = (b⁻¹ * (τ * c * τ⁻¹)⁻¹) * a * b * c * (τ * b * τ⁻¹)⁻¹ := by group
          _ = ((τ * c * τ⁻¹)⁻¹ * b⁻¹) * a * b * c * (τ * b * τ⁻¹)⁻¹ := by
                rw [(hb_c1.inv_left.inv_right).eq]
          _ = (τ * c * τ⁻¹)⁻¹ * (b⁻¹ * a) * b * c * (τ * b * τ⁻¹)⁻¹ := by group
          _ = (τ * c * τ⁻¹)⁻¹ * (a * b⁻¹) * b * c * (τ * b * τ⁻¹)⁻¹ := by rw [(hb_a.inv_left).eq]
          _ = (τ * c * τ⁻¹)⁻¹ * a * c * (τ * b * τ⁻¹)⁻¹ := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact mul_mem (Subgroup.inv_mem _ hb) (hmem1 a ha)
      · rw [hz1eq']
        exact mul_mem (mul_mem (mul_mem
          (Subgroup.mem_sup_left (Subgroup.inv_mem _ (hmem0 c hc)))
          (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right hc))
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ (hmem1' b hb)))
    have hz2 : z2 ∈ Z2 := by
      rw [hZ2def]
      have hb1eq : (τ * b * τ⁻¹) * c⁻¹
          = (τ * a * τ⁻¹)⁻¹ * (τ * c * τ⁻¹)⁻¹ * a * b := by
        calc (τ * b * τ⁻¹) * c⁻¹
            = ((τ * c * τ⁻¹) * (τ * a * τ⁻¹))⁻¹
                * ((τ * c * τ⁻¹) * (τ * a * τ⁻¹) * (τ * b * τ⁻¹)) * c⁻¹ := by group
          _ = ((τ * c * τ⁻¹) * (τ * a * τ⁻¹))⁻¹ * (a * b * c) * c⁻¹ := by rw [hcba]
          _ = (τ * a * τ⁻¹)⁻¹ * (τ * c * τ⁻¹)⁻¹ * a * b := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hz2eq]
        exact mul_mem (hmem1' b hb) (Subgroup.inv_mem _ hc)
      · rw [hz2eq, hb1eq]
        exact mul_mem (mul_mem (mul_mem
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ (hmem1 a ha)))
          (Subgroup.mem_sup_left (Subgroup.inv_mem _ (hmem0 c hc)))) (Subgroup.mem_sup_left ha))
          (Subgroup.mem_sup_right hb)
    have hz2' : z2' ∈ Z2 := by
      rw [hZ2def]
      have hz1A1 : z1 ∈ A1 := (Subgroup.mem_inf.mp (by rw [← hZ1def]; exact hz1)).1
      have hz1A2 : z1 ∈ A ⊔ A2 := (Subgroup.mem_inf.mp (by rw [← hZ1def]; exact hz1)).2
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hz2'eq]
        exact hmem1' z1 hz1A1
      · rw [hz2'eq]
        obtain ⟨x, hx, y, hy, hxy⟩ := (qtwoDB7_b2_mem_sup_iff_of_commute c02).mp hz1A2
        have hdist : τ * z1 * τ⁻¹ = (τ * x * τ⁻¹) * (τ * y * τ⁻¹) := by rw [← hxy]; group
        rw [hdist]
        exact mul_mem (Subgroup.mem_sup_right (hmem1 x hx)) (Subgroup.mem_sup_left (hmem0 y hy))
    have hz1Z : z1 ∈ Z := by rw [hZdef]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hz1)
    have hz2Z : z2 ∈ Z := by rw [hZdef]; exact Subgroup.mem_sup_right hz2
    have hz2'Z : z2' ∈ Z := by rw [hZdef]; exact Subgroup.mem_sup_right hz2'
    have hcommZ : ∀ w ∈ Z, ∀ x ∈ A ⊔ A1 ⊔ A2, w * x = x * w := fun w hw x hx =>
      (Subgroup.mem_centralizer_iff.mp (hZcent hw) x hx).symm
    have hc0 : c = z2⁻¹ * (τ * b * τ⁻¹) := by rw [hz2eq]; group
    have ha1 : (τ * a * τ⁻¹) = b * z1 := by rw [hz1eq]; group
    have ha2 : (τ ^ 2 * a * (τ ^ 2)⁻¹) = (τ * b * τ⁻¹) * z2' := by
      rw [hz2'eq]
      calc τ ^ 2 * a * (τ ^ 2)⁻¹ = τ * (τ * a * τ⁻¹) * τ⁻¹ := by rw [pow_two]; group
        _ = τ * (b * z1) * τ⁻¹ := by rw [ha1]
        _ = (τ * b * τ⁻¹) * (τ * z1 * τ⁻¹) := by group
    have hL : j = a * b * (τ * b * τ⁻¹) * z2⁻¹ := by
      calc j = a * b * c := hjc.symm
        _ = a * b * (z2⁻¹ * (τ * b * τ⁻¹)) := by rw [hc0]
        _ = a * b * (τ * b * τ⁻¹) * z2⁻¹ := by
              rw [hcommZ z2⁻¹ (Z.inv_mem hz2Z) (τ * b * τ⁻¹)
                (Subgroup.mem_sup_right (hmem1' b hb))]
              group
    have hR : d ⟨a, ha⟩ * ((z1 * z2')⁻¹ * z2⁻¹) = a * b * (τ * b * τ⁻¹) * z2⁻¹ := by
      rw [hd ⟨a, ha⟩, ha1, ha2]
      calc (a * (b * z1) * ((τ * b * τ⁻¹) * z2')) * ((z1 * z2')⁻¹ * z2⁻¹)
          = a * b * (z1 * (τ * b * τ⁻¹)) * (z2' * ((z1 * z2')⁻¹ * z2⁻¹)) := by group
        _ = a * b * ((τ * b * τ⁻¹) * z1) * (z2' * ((z1 * z2')⁻¹ * z2⁻¹)) := by
              rw [hcommZ z1 hz1Z (τ * b * τ⁻¹) (Subgroup.mem_sup_right (hmem1' b hb))]
        _ = a * b * (τ * b * τ⁻¹) * z2⁻¹ := by group
    have hz_eq : j = d ⟨a, ha⟩ * ((z1 * z2')⁻¹ * z2⁻¹) := hL.trans hR.symm
    rw [hz_eq]
    exact mul_mem (Subgroup.mem_sup_left ⟨⟨a, ha⟩, rfl⟩)
      (Subgroup.mem_sup_right (Z.mul_mem (Z.inv_mem (Z.mul_mem hz1Z hz2'Z))
        (Z.inv_mem hz2Z)))
  have hJb_le_D : Jb ≤ d.range := by
    have hperf : ⁅Jb, Jb⁆ = Jb := qtwoDB7_b2_commutator_eq_self_of_isPerfect hJq.1
    calc Jb = ⁅Jb, Jb⁆ := hperf.symm
      _ ≤ ⁅d.range ⊔ Z, d.range ⊔ Z⁆ := Subgroup.commutator_mono hJb_le hJb_le
      _ ≤ d.range := qtwoDB7_b2_commutator_sup_le hZcent'
  have hDJ : d.range = Jb := by
    refine le_antisymm ?_ hJb_le_D
    set C : Subgroup Y := Subgroup.centralizer ({τ} : Set Y) with hCdef
    let Dc : Subgroup ↥C := d.range.subgroupOf C
    let H : Subgroup ↥Dc := (Jb.subgroupOf C).subgroupOf Dc
    have hHsn : H.IsSubnormal := hJs.2.subgroupOf
    have hQq : CFSG.IsQuasisimple ↥Dc :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDcent).symm hDq
    rcases qtwoDB7_b2_subnormal_eq_top_or_le_center hQq hHsn with htop | hcent
    · intro x hx
      have hxDc : (⟨⟨x, hDcent hx⟩, hx⟩ : ↥Dc) ∈ H := by rw [htop]; exact Subgroup.mem_top _
      exact hxDc
    · exfalso
      have hab_comm : ∀ a b : ↥Jb, a * b = b * a := by
        intro a b
        let qa : ↥Dc := ⟨⟨(a : Y), hDcent (hJb_le_D a.2)⟩, hJb_le_D a.2⟩
        let qb : ↥Dc := ⟨⟨(b : Y), hDcent (hJb_le_D b.2)⟩, hJb_le_D b.2⟩
        have hqa : qa ∈ H := by
          change (⟨(a : Y), hDcent (hJb_le_D a.2)⟩ : ↥C) ∈ Jb.subgroupOf C; exact a.2
        have hqb : qb ∈ H := by
          change (⟨(b : Y), hDcent (hJb_le_D b.2)⟩ : ↥C) ∈ Jb.subgroupOf C; exact b.2
        have hval : (b : Y) * (a : Y) = (a : Y) * (b : Y) :=
          congrArg (fun z : ↥Dc => (z : Y)) (Subgroup.mem_center_iff.mp (hcent hqa) qb)
        exact Subtype.ext hval.symm
      have hcenter : Jb ≤ Subgroup.centralizer (Jb : Set Y) := by
        intro a ha; rw [Subgroup.mem_centralizer_iff]; intro b hb
        exact congrArg Subtype.val (hab_comm ⟨b, hb⟩ ⟨a, ha⟩)
      have hbot : ⁅Jb, Jb⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcenter
      have hperf : ⁅Jb, Jb⁆ = Jb := qtwoDB7_b2_commutator_eq_self_of_isPerfect hJq.1
      have hJbbot : Jb = ⊥ := by rw [← hperf, hbot]
      haveI : Nontrivial ↥Jb := CFSG.LocalCores.isQuasisimple_nontrivial hJq
      have hsub : Subsingleton ↥Jb := by rw [hJbbot]; infer_instance
      exact not_subsingleton ↥Jb hsub
  refine ⟨d.codRestrict Jb (fun a => hDJ ▸ (⟨a, rfl⟩ : d a ∈ d.range)), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hDJ ▸ y.2 : (y : Y) ∈ d.range)
    exact ⟨a, Subtype.ext (by rw [MonoidHom.codRestrict_apply]; exact ha)⟩
  · intro a ha; rw [MonoidHom.mem_ker] at ha
    have hda : d a = 1 := by have := congrArg (fun z : ↥Jb => (z : Y)) ha; simpa using this
    exact hker (MonoidHom.mem_ker.mpr hda)
  · intro a; simpa using hd a
end CFSG.StandardType.QTwo
end
