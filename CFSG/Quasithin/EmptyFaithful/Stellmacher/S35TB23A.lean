module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.TB23

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem le_normalizer_of_conj {X E : Subgroup G} (h : ∀ g ∈ X, ∀ x ∈ E, g * x * g⁻¹ ∈ E) :
    X ≤ Subgroup.normalizer (E : Set G) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => h g hg x hx, fun hx => by
      have := h g⁻¹ (X.inv_mem hg) _ hx
      simpa [mul_assoc] using this⟩

omit [Finite G] in
@[expose] def Nst (X V : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G)) (r : G) :
    Subgroup G where
  carrier := {g | g ∈ X ∧ g * r * g⁻¹ * r⁻¹ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨X.mul_mem ha hb, ?_⟩
    have h1 : a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hX ha) _).mp hb'
    have := V.mul_mem h1 ha'
    convert this using 1
    group
  one_mem' := ⟨X.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨X.inv_mem ha, ?_⟩
    have h1 : a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * a⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hX (X.inv_mem ha)) _).mp (V.inv_mem ha')
    convert h1 using 1
    group

omit [Finite G] in
theorem mem_Nst {X V : Subgroup G} {hX : X ≤ Subgroup.normalizer (V : Set G)} {r g : G} :
    g ∈ Nst X V hX r ↔ g ∈ X ∧ g * r * g⁻¹ * r⁻¹ ∈ V := Iff.rfl

omit [Finite G] in
theorem Nst_le {X V : Subgroup G} {hX : X ≤ Subgroup.normalizer (V : Set G)} {r : G} :
    Nst X V hX r ≤ X := fun _ hg => hg.1

theorem relIndex_sup_eq {N K : Subgroup G} (hK : N ≤ Subgroup.normalizer (K : Set G)) :
    N.relIndex (N ⊔ K) = (N ⊓ K).relIndex K := by
  have hKrel : K.relIndex (N ⊔ K) = (N ⊓ K).relIndex N := by
    let NG : Subgroup G := Subgroup.normalizer (K : Set G)
    have hHleNG : N ≤ NG := hK
    have hKleNG : K ≤ NG := Subgroup.le_normalizer
    have hHKleNG : N ⊔ K ≤ NG := sup_le hHleNG hKleNG
    let : (K.subgroupOf NG).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := NG) hKleNG).2 le_rfl
    calc
      K.relIndex (N ⊔ K)
          = (K.subgroupOf NG).relIndex ((N ⊔ K).subgroupOf NG) :=
            (Subgroup.relIndex_subgroupOf (H := K) (K := N ⊔ K) (L := NG) hHKleNG).symm
      _ = (K.subgroupOf NG).relIndex ((N.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
            rw [Subgroup.subgroupOf_sup (A := N) (A' := K) (B := NG) hHleNG hKleNG]
      _ = ((N.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (N.subgroupOf NG) := by
            calc
              (K.subgroupOf NG).relIndex ((N.subgroupOf NG) ⊔ (K.subgroupOf NG))
                  = (K.subgroupOf NG).relIndex (N.subgroupOf NG) :=
                    Subgroup.relIndex_sup_right (H := N.subgroupOf NG) (K := K.subgroupOf NG)
              _ = ((N.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (N.subgroupOf NG) :=
                    (Subgroup.inf_relIndex_left (H := N.subgroupOf NG)
                      (K := K.subgroupOf NG)).symm
      _ = ((N ⊓ K).subgroupOf NG).relIndex (N.subgroupOf NG) := by
            rw [show (N.subgroupOf NG) ⊓ (K.subgroupOf NG) = (N ⊓ K).subgroupOf NG by
              ext x
              simp [Subgroup.mem_subgroupOf]]
      _ = (N ⊓ K).relIndex N :=
            Subgroup.relIndex_subgroupOf (H := N ⊓ K) (K := N) (L := NG) hHleNG
  have hmul :
      (N ⊓ K).relIndex N * N.relIndex (N ⊔ K) = (N ⊓ K).relIndex K * (N ⊓ K).relIndex N := by
    calc
      (N ⊓ K).relIndex N * N.relIndex (N ⊔ K) = (N ⊓ K).relIndex (N ⊔ K) :=
        Subgroup.relIndex_mul_relIndex (H := N ⊓ K) (K := N) (L := N ⊔ K)
          inf_le_left le_sup_left
      _ = (N ⊓ K).relIndex K * K.relIndex (N ⊔ K) :=
        (Subgroup.relIndex_mul_relIndex (H := N ⊓ K) (K := K) (L := N ⊔ K)
          inf_le_right le_sup_right).symm
      _ = (N ⊓ K).relIndex K * (N ⊓ K).relIndex N := by rw [hKrel]
  have hpos : 0 < (N ⊓ K).relIndex N :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (N ⊓ K).subgroupOf N))
  have hmul' : (N ⊓ K).relIndex N * N.relIndex (N ⊔ K) =
      (N ⊓ K).relIndex N * (N ⊓ K).relIndex K := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.eq_of_mul_eq_mul_left hpos hmul'

theorem relIndex_le_of_sup {N K P T : Subgroup G} (hK : N ≤ Subgroup.normalizer (K : Set G))
    (hT : N ⊔ K = T) (hP : P ≤ N ⊓ K) : N.relIndex T ≤ P.relIndex K := by
  rw [← hT, relIndex_sup_eq hK]
  exact Subgroup.relIndex_le_of_le_left hP (Subgroup.index_ne_zero_of_finite)

theorem false_of_Lr (hS : Sit H M S) (hII : CaseII H M) (h6b : Claim6b H M)
    {γ lb α' : Geo H M} (hγ : vtype γ = false) (hlb : lb ∈ nbrs γ) (hlb' : lb ∈ nbrs α')
    (hne : α' ≠ γ) {r : G} (hrα : r ∈ Vn α') (hrW : r ∈ Wb γ) (hrZ : r ∉ Zv lb)
    (hrC : ∀ v ∈ Vn γ, r * v * r⁻¹ * v⁻¹ = 1)
    (hL : ∀ l ∈ Lr γ, l * r * l⁻¹ * r⁻¹ ∈ Vn γ) : False := by
  have hVn : stab γ ≤ Subgroup.normalizer (Vn γ : Set G) := Std.Vn_normal γ
  have hLs : Lr γ ≤ stab γ := oTwoRes_le _
  have hLnorm : stab γ ≤ Subgroup.normalizer (Lr γ : Set G) := le_normalizer_oTwoRes _
  let E : Subgroup G :=
    { carrier := {x | x ∈ Wb γ ∧ x ∈ Subgroup.normalizer (Vn γ : Set G) ∧
        ∀ l ∈ Lr γ, x * l * x⁻¹ * l⁻¹ ∈ Vn γ}
      mul_mem' := by
        rintro x y ⟨hxW, hxN, hxL⟩ ⟨hyW, hyN, hyL⟩
        refine ⟨(Wb γ).mul_mem hxW hyW, (Subgroup.normalizer (Vn γ : Set G)).mul_mem hxN hyN, ?_⟩
        intro l hl
        have h1 : x * (y * l * y⁻¹ * l⁻¹) * x⁻¹ ∈ Vn γ :=
          (Subgroup.mem_normalizer_iff.mp hxN _).mp (hyL l hl)
        have := (Vn γ).mul_mem h1 (hxL l hl)
        convert this using 1
        group
      one_mem' := ⟨(Wb γ).one_mem, (Subgroup.normalizer (Vn γ : Set G)).one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hxW, hxN, hxL⟩
        refine ⟨(Wb γ).inv_mem hxW, (Subgroup.normalizer (Vn γ : Set G)).inv_mem hxN, ?_⟩
        intro l hl
        have h1 : x⁻¹ * (x * l * x⁻¹ * l⁻¹)⁻¹ * x⁻¹⁻¹ ∈ Vn γ :=
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Vn γ : Set G)).inv_mem hxN) _).mp
            ((Vn γ).inv_mem (hxL l hl))
        convert h1 using 1
        group }
  have hEW : E ≤ Wb γ := fun x hx => hx.1
  have hVE : Vn γ ≤ E := fun v hv =>
    ⟨Std.Vn_le_Wb_self hS hγ hv, Subgroup.le_normalizer hv, fun l hl => by
      have h1 : l * v⁻¹ * l⁻¹ ∈ Vn γ :=
        (Subgroup.mem_normalizer_iff.mp (hVn (hLs hl)) _).mp ((Vn γ).inv_mem hv)
      have := (Vn γ).mul_mem hv h1
      convert this using 1
      group⟩
  have hEL : ⁅E, Lr γ⁆ ≤ Vn γ := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    rw [commutatorElement_def]
    exact hx.2.2 l hl
  have hEn : stab γ ≤ Subgroup.normalizer (E : Set G) := by
    refine le_normalizer_of_conj fun g hg x hx => ?_
    obtain ⟨hxW, hxN, hxL⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (Std.Wb_normal γ hg) x).mp hxW,
      (Subgroup.normalizer (Vn γ : Set G)).mul_mem
        ((Subgroup.normalizer (Vn γ : Set G)).mul_mem (hVn hg) hxN)
        ((Subgroup.normalizer (Vn γ : Set G)).inv_mem (hVn hg)), ?_⟩
    intro l hl
    have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ Lr γ :=
      (Subgroup.mem_normalizer_iff.mp (hLnorm ((stab γ).inv_mem hg))) l |>.mp hl
    have h1 := hxL _ hl'
    have h2 : g * (x * (g⁻¹ * l * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * l * g⁻¹⁻¹)⁻¹) * g⁻¹ ∈ Vn γ :=
      (Subgroup.mem_normalizer_iff.mp (hVn hg) _).mp h1
    convert h2 using 1
    group
  have hrN : r ∈ Subgroup.normalizer (Vn γ : Set G) := by
    refine Subgroup.centralizer_le_normalizer (Vn γ : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h := hrC v hv
    have h2 : r * v * r⁻¹ = v := mul_inv_eq_one.mp h
    calc v * r = (r * v * r⁻¹) * r := by rw [h2]
      _ = r * v := by group
  have hrE : r ∈ E := ⟨hrW, hrN, fun l hl => by
    have h1 := (Vn γ).inv_mem (hL l hl)
    convert h1 using 1
    group⟩
  have hres := h6b γ lb α' E hγ hlb hlb' hne hEn hVE hEW hEL
  have hmem : r ∈ Vn α' ⊓ E := ⟨hrα, hrE⟩
  rw [hres] at hmem
  have := hII γ lb α' hγ hlb hlb' hne
  exact hrZ (this ▸ ⟨hmem.2, hmem.1⟩)

end S35.TB23

end F53.Stellmacher

end CFSG.Quasithin
