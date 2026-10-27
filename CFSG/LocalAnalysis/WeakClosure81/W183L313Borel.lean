module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Goldschmidt
open CFSG.ComponentClassification.AschbacherToolkit.Bender
  (sylowCenter mem_sylowCenter sylowCenter_le)
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

structure BorelU34 (Q S D : Subgroup Γ) : Prop where
  le_Q : D ≤ Q
  le_normalizer : D ≤ Subgroup.normalizer (S : Set Γ)
  odd : Odd (Nat.card D)
  sup_eq : S ⊔ D = Q ⊓ Subgroup.normalizer (S : Set Γ)
  inf_centralizer : D ⊓ Subgroup.centralizer (S : Set Γ) = ⊥
  card_center : Nat.card (sylowCenter S) = 4
  sq_center : ∀ x ∈ sylowCenter S, x * x = 1
  omega_le : ∀ x ∈ S, x * x = 1 → x ∈ sylowCenter S
  comm_mem : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ sylowCenter S
  sq_mem : ∀ x ∈ S, x * x ∈ sylowCenter S
  nonabelian : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x
  trans_center : ∀ x ∈ sylowCenter S, ∀ y ∈ sylowCenter S, x ≠ 1 → y ≠ 1 →
    ∃ d ∈ D, d⁻¹ * x * d = y
  irred : ∀ X : Subgroup Γ, sylowCenter S ≤ X → X ≤ S → D ≤ Subgroup.normalizer (X : Set Γ) →
    X = sylowCenter S ∨ X = S
  ti : ∀ S' S'' : Subgroup Γ, IsSylowIn 2 S' Q → IsSylowIn 2 S'' Q → S' ⊓ S'' ≠ ⊥ → S' = S''
  trans : ∀ S' S'' : Subgroup Γ, IsSylowIn 2 S' Q → IsSylowIn 2 S'' Q → S' ≠ S → S'' ≠ S →
    ∃ s ∈ S, conjSubgroup S' s = S''

variable [Finite Γ]

theorem w183l313_center_map_eq (S : Subgroup Γ) :
    (Subgroup.center ↥S).map S.subtype = sylowCenter S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_sylowCenter]
    refine ⟨y.2, fun t ht => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy (⟨t, ht⟩ : ↥S))
  · intro hx
    rw [mem_sylowCenter] at hx
    exact ⟨⟨x, hx.1⟩, Subgroup.mem_center_iff.mpr (fun z => Subtype.ext (hx.2 z z.2)), rfl⟩

private theorem w183l313_normalizes_center_aux {S : Subgroup Γ} {y : Γ}
    (hy : y ∈ Subgroup.normalizer (S : Set Γ)) :
    y ∈ Subgroup.normalizer ((sylowCenter S : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro z
  rw [mem_sylowCenter, mem_sylowCenter]
  constructor
  · rintro ⟨hzS, hzC⟩
    refine ⟨(hy z).mp hzS, fun t ht => ?_⟩
    have h1 := hzC (y⁻¹ * t * y) ((hy (y⁻¹ * t * y)).mpr (by
      rwa [show y * (y⁻¹ * t * y) * y⁻¹ = t by group]))
    calc t * (y * z * y⁻¹) = y * ((y⁻¹ * t * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * t * y)) * y⁻¹ := by rw [h1]
      _ = (y * z * y⁻¹) * t := by group
  · rintro ⟨hzS, hzC⟩
    refine ⟨(hy z).mpr hzS, fun t ht => ?_⟩
    have h1 := hzC (y * t * y⁻¹) ((hy t).mp ht)
    calc t * z = y⁻¹ * ((y * t * y⁻¹) * (y * z * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * z * y⁻¹) * (y * t * y⁻¹)) * y := by rw [h1]
      _ = z * t := by group

private theorem w183l313_smul_inv_eq_conjSub {Y : Type} [Group Y] (g : Y) (T : Sylow 2 Y) :
    ((g⁻¹ • T : Sylow 2 Y) : Subgroup Y) = CFSG.Goldschmidt.conjSub g (T : Subgroup Y) := by
  ext x
  rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff,
    CFSG.Goldschmidt.mem_conjSub, inv_inv]

private theorem w183l313_smul_eq_conjSub_inv {Y : Type} [Group Y] (g : Y) (T : Sylow 2 Y) :
    ((g • T : Sylow 2 Y) : Subgroup Y) = CFSG.Goldschmidt.conjSub g⁻¹ (T : Subgroup Y) := by
  have h := w183l313_smul_inv_eq_conjSub (g := g⁻¹) T
  rwa [inv_inv] at h

private theorem w183l313_exists_conjSub_eq {Y : Type} [Group Y] [Finite Y]
    (T P : Sylow 2 Y) :
    ∃ b : Y, (P : Subgroup Y) = CFSG.Goldschmidt.conjSub b (T : Subgroup Y) := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq Y T P
  exact ⟨a⁻¹, by rw [← ha, w183l313_smul_eq_conjSub_inv]⟩

private theorem w183l313_ti_of_conj_ti {Y : Type} [Group Y] [Finite Y] (T : Sylow 2 Y)
    (hti : ∀ g : Y, (T : Subgroup Y) ⊓ CFSG.Goldschmidt.conjSub g (T : Subgroup Y) ≠ ⊥ →
      CFSG.Goldschmidt.conjSub g (T : Subgroup Y) = (T : Subgroup Y))
    {P Q : Sylow 2 Y} (h : (P : Subgroup Y) ⊓ (Q : Subgroup Y) ≠ ⊥) : P = Q := by
  obtain ⟨b, hb⟩ := w183l313_exists_conjSub_eq T P
  obtain ⟨c, hc⟩ := w183l313_exists_conjSub_eq T Q
  have hb' : (P : Subgroup Y) = conjSubgroup (T : Subgroup Y) b := hb
  have hc' : (Q : Subgroup Y) = conjSubgroup (T : Subgroup Y) c := hc
  have h' : (T : Subgroup Y) ⊓ CFSG.Goldschmidt.conjSub (c * b⁻¹) (T : Subgroup Y) ≠ ⊥ := by
    have hconj : conjSubgroup ((P : Subgroup Y) ⊓ (Q : Subgroup Y)) b⁻¹ ≠ ⊥ := by
      intro hbot
      apply h
      have h1 := congrArg (conjSubgroup · b) hbot
      rw [E3.conjSubgroup_bot, conjSubgroup_conjSubgroup] at h1
      rwa [inv_mul_cancel, conjSubgroup_one] at h1
    rw [E3.conjSubgroup_inf, hb', hc'] at hconj
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at hconj
    rwa [mul_inv_cancel, conjSubgroup_one] at hconj
  have hT : CFSG.Goldschmidt.conjSub (c * b⁻¹) (T : Subgroup Y) = (T : Subgroup Y) := hti _ h'
  have hT' : conjSubgroup (T : Subgroup Y) (c * b⁻¹) = (T : Subgroup Y) := hT
  have hQP : (Q : Subgroup Y) = (P : Subgroup Y) := by
    rw [hc, hb]
    change conjSubgroup (T : Subgroup Y) c = conjSubgroup (T : Subgroup Y) b
    have hcb : c * b⁻¹ * b = c := by group
    rw [← hcb, ← conjSubgroup_conjSubgroup, hT']
  exact Sylow.ext hQP.symm

private theorem w183l313_map_conjSub {Y Z : Type} [Group Y] [Group Z] (φ : Y →* Z)
    (A : Subgroup Y) (g : Y) :
    (CFSG.Goldschmidt.conjSub g A).map φ = conjSubgroup (A.map φ) (φ g) := by
  have hf : (φ.comp (MulAut.conj g⁻¹).toMonoidHom : Y →* Z) =
      ((MulAut.conj (φ g)⁻¹).toMonoidHom.comp φ : Y →* Z) := by
    ext x
    simp [MulAut.conj_apply, map_mul]
  rw [CFSG.Goldschmidt.conjSub, conjSubgroup, Subgroup.map_map, Subgroup.map_map, hf]

section Certified


theorem w183l313_borel_exists {Q S : Subgroup Γ} (hQ : IsU3 ↥Q 2) (hS : IsSylowIn 2 S Q) :
    ∃ D : Subgroup Γ, BorelU34 Q S D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := ↥Q
  let φ : X →* Γ := Q.subtype
  have hφ : Function.Injective φ := Q.subtype_injective
  have hsimple : IsSimpleGroup X :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hQ
  have hnabX : ∃ a b : X, a * b ≠ b * a :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hQ
  have hcenter : Subgroup.center X = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot X hnabX
  obtain ⟨e⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_psu3_of_lieModel_PSU3 hQ
  have hI : IsGoldTypeI X := by
    have e₁ : X ⧸ Subgroup.center X ≃* PSU3 2 2 :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans
        ((QuotientGroup.quotientBot : X ⧸ (⊥ : Subgroup X) ≃* X).trans e)
    exact Or.inr (Or.inr ⟨2, le_rfl, ⟨e₁⟩⟩)
  let T : Sylow 2 X := hS.toSylow
  have hTcoe : (T : Subgroup X) = S.subgroupOf Q := IsSylowIn.coe_toSylow hS
  have hTmap : (T : Subgroup X).map φ = S := by
    rw [hTcoe, Subgroup.map_subgroupOf_eq_of_le hS.le]
  have hmemT : ∀ y : X, φ y ∈ S ↔ y ∈ (T : Subgroup X) := by
    intro y
    rw [← hTmap]
    exact ⟨fun h => by obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp h; rwa [hφ hzy] at hz,
      fun h => ⟨y, h, rfl⟩⟩
  obtain ⟨D₀, hDN, hDcyc, hDodd, hinf, hsup, hinfC, hcomm, hOmega, htrans, hnab, hPSL, hSz,
    hPSU, hti, htrans2, hfixed, hcoat, hmax⟩ := CFSG.Goldschmidt.G32 X hI T
  let Z : Subgroup X := (T : Subgroup X) ⊓ Subgroup.centralizer ((T : Subgroup X) : Set X)
  let D : Subgroup Γ := D₀.map φ
  obtain ⟨hZcard, hTcard, -⟩ := hPSU 2 le_rfl ⟨e⟩
  norm_num at hZcard hTcard
  have hnabT : ¬ IsMulCommutative (T : Subgroup X) := by
    intro hcommT
    have hle : (T : Subgroup X) ≤ Subgroup.centralizer ((T : Subgroup X) : Set X) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hcommT
    have hZT : Z = (T : Subgroup X) := by simp only [Z, inf_eq_left.mpr hle]
    change Nat.card Z = 4 at hZcard
    rw [hZT] at hZcard
    rw [hZcard] at hTcard
    norm_num at hTcard
  obtain ⟨hcommT, hsqT, hirrT⟩ := hnab hnabT
  have hcommZ : ⁅(T : Subgroup X), (T : Subgroup X)⁆ = Z := hcommT
  have hOmegaZ : CFSG.Goldschmidt.Omega1 (T : Subgroup X) = Z := hOmega
  have hCmap : (Subgroup.centralizer ((T : Subgroup X) : Set X)).map φ =
      Subgroup.centralizer (S : Set Γ) ⊓ Q := by
    refine le_antisymm (le_inf ?_ (Subgroup.map_subtype_le _)) ?_
    · have h := Subgroup.map_centralizer_le_centralizer_image ((T : Subgroup X) : Set X) φ
      have hφT : φ '' ((T : Subgroup X) : Set X) = (S : Set Γ) := by
        rw [← Subgroup.coe_map, hTmap]
      rwa [hφT] at h
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgC, hgQ⟩ := hg
      have hgQ' : g ∈ φ.range := by rwa [Subgroup.range_subtype]
      obtain ⟨g₀, rfl⟩ := hgQ'
      refine ⟨g₀, ?_, rfl⟩
      change g₀ ∈ Subgroup.centralizer ((T : Subgroup X) : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      apply hφ
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hgC (φ t) ((hmemT t).mpr ht)
  have hZmap : Z.map φ = sylowCenter S := by
    have h1 : Z.map φ = (T : Subgroup X).map φ ⊓
        (Subgroup.centralizer ((T : Subgroup X) : Set X)).map φ :=
      Subgroup.map_inf _ _ φ hφ
    rw [h1, hTmap, hCmap]
    show S ⊓ (Subgroup.centralizer (S : Set Γ) ⊓ Q) = sylowCenter S
    rw [sylowCenter, ← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hS.le)]
  have hNmap : (Subgroup.normalizer ((T : Subgroup X) : Set X)).map φ =
      Q ⊓ Subgroup.normalizer (S : Set Γ) := by
    refine le_antisymm (le_inf (Subgroup.map_subtype_le _) ?_) ?_
    · calc (Subgroup.normalizer ((T : Subgroup X) : Set X)).map φ
          ≤ Subgroup.normalizer (((T : Subgroup X)).map φ : Set Γ) := Subgroup.le_normalizer_map φ
        _ = Subgroup.normalizer (S : Set Γ) := by rw [hTmap]
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgQ, hgN⟩ := hg
      have hgQ' : g ∈ φ.range := by rwa [Subgroup.range_subtype]
      obtain ⟨g₀, rfl⟩ := hgQ'
      refine ⟨g₀, ?_, rfl⟩
      change g₀ ∈ Subgroup.normalizer ((T : Subgroup X) : Set X)
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        have h1 : φ g₀ * φ t * (φ g₀)⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp hgN (φ t)).mp ((hmemT t).mpr ht)
        exact (hmemT _).mp (by simpa only [map_mul, map_inv] using h1)
      · intro ht
        have h1 : φ t ∈ S := (Subgroup.mem_normalizer_iff.mp hgN (φ t)).mpr
          (by simpa only [map_mul, map_inv] using (hmemT _).mpr ht)
        exact (hmemT t).mp h1
  have htiX : ∀ P Q : Sylow 2 X, (P : Subgroup X) ⊓ (Q : Subgroup X) ≠ ⊥ → P = Q :=
    fun P Q h => w183l313_ti_of_conj_ti (T := T) hti h
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le D₀
  · calc D₀.map φ ≤ (Subgroup.normalizer ((T : Subgroup X) : Set X)).map φ := Subgroup.map_mono hDN
      _ ≤ Subgroup.normalizer (((T : Subgroup X)).map φ : Set Γ) := Subgroup.le_normalizer_map φ
      _ = Subgroup.normalizer (S : Set Γ) := by rw [hTmap]
  · have hcard : Nat.card D = Nat.card D₀ := Subgroup.card_map_of_injective hφ
    rw [hcard]; exact hDodd
  · calc S ⊔ D = (T : Subgroup X).map φ ⊔ D₀.map φ := by rw [hTmap]
      _ = ((T : Subgroup X) ⊔ D₀).map φ := (Subgroup.map_sup _ _ φ).symm
      _ = (Subgroup.normalizer ((T : Subgroup X) : Set X)).map φ := by rw [hsup]
      _ = Q ⊓ Subgroup.normalizer (S : Set Γ) := hNmap
  · have hmap : (D₀ ⊓ Subgroup.centralizer ((T : Subgroup X) : Set X)).map φ = ⊥ := by
      rw [hinfC, Subgroup.map_bot]
    rw [Subgroup.map_inf D₀ _ φ hφ, hCmap] at hmap
    have hDQ : D₀.map φ ≤ Q := Subgroup.map_subtype_le D₀
    rwa [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hDQ)] at hmap
  · rw [← hZmap, Subgroup.card_map_of_injective hφ]
    exact hZcard
  · intro x hx
    have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
    let W : Subgroup X :=
      { carrier := {z | z ∈ Z ∧ z * z = 1}
        mul_mem' := by
          intro a b ha hb
          refine ⟨Z.mul_mem ha.1 hb.1, ?_⟩
          calc (a * b) * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hZab a ha.1 b hb.1]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha.2, hb.2, one_mul]
        one_mem' := ⟨Z.one_mem, mul_one 1⟩
        inv_mem' := by
          intro a ha
          refine ⟨Z.inv_mem ha.1, ?_⟩
          rw [inv_eq_of_mul_eq_one_right ha.2, ha.2] }
    have hOmegaW : Omega1 (T : Subgroup X) ≤ W := by
      rw [Omega1]
      refine (Subgroup.closure_le W).mpr ?_
      intro x hx
      refine ⟨?_, by simpa [pow_two] using hx.2⟩
      rw [← hOmegaZ]
      exact Subgroup.subset_closure hx
    have hZW : Z ≤ W := by rw [← hOmegaZ]; exact hOmegaW
    rw [← hZmap] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← map_mul, (hZW hz).2, map_one]
  · intro x hx hx2
    rw [← hTmap] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have ht2 : t * t = 1 := by
      apply hφ
      rw [map_mul, map_one]
      exact hx2
    rw [← hZmap]
    refine ⟨t, ?_, rfl⟩
    rw [← hOmegaZ]
    exact Subgroup.subset_closure (show t ∈ {x | x ∈ (T : Subgroup X) ∧ x ^ 2 = 1} from
      ⟨ht, by simpa [pow_two] using ht2⟩)
  · intro x hx y hy
    rw [← hTmap] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : ⁅a, b⁆ ∈ Z := by
      rw [← hcommZ]
      exact (Subgroup.commutator_le.mp le_rfl) a ha b hb
    rw [← hZmap]
    exact ⟨⁅a, b⁆, hab, by simp only [commutatorElement_def, map_mul, map_inv]⟩
  · intro x hx
    rw [← hTmap] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← hZmap]
    exact ⟨a ^ 2, hsqT a ha, by simp [map_pow, pow_two]⟩
  · have h : ∃ a : ↥(T : Subgroup X), ∃ b : ↥(T : Subgroup X), a * b ≠ b * a := by
      have h' : ¬ ∀ a b : ↥(T : Subgroup X), a * b = b * a :=
        fun h => hnabT (isMulCommutative_iff.mpr h)
      rw [not_forall] at h'
      obtain ⟨a, h'⟩ := h'
      rw [not_forall] at h'
      obtain ⟨b, hb⟩ := h'
      exact ⟨a, b, hb⟩
    obtain ⟨a, b, hab⟩ := h
    refine ⟨φ (a : X), ?_, φ (b : X), ?_, ?_⟩
    · rw [← hTmap]; exact ⟨a, a.2, rfl⟩
    · rw [← hTmap]; exact ⟨b, b.2, rfl⟩
    · intro hc
      apply hab
      apply Subtype.ext
      apply hφ
      change φ ((a : X) * (b : X)) = φ ((b : X) * (a : X))
      rw [map_mul, map_mul]
      exact hc
  · intro x hx y hy hx1 hy1
    rw [← hZmap] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hx₀Ω : x₀ ∈ Omega1 (T : Subgroup X) := by rwa [hOmegaZ]
    have hy₀Ω : y₀ ∈ Omega1 (T : Subgroup X) := by rwa [hOmegaZ]
    have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy₀1 : y₀ ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨d₀, hd₀, hd₀eq⟩ := htrans x₀ hx₀Ω y₀ hy₀Ω hx₀1 hy₀1
    exact ⟨φ d₀, ⟨d₀, hd₀, rfl⟩, by rw [← map_inv, ← map_mul, ← map_mul, hd₀eq]⟩
  · intro X' hZX' hX'S hDX'
    let X₀ : Subgroup X := X'.comap φ
    have hX₀T : X₀ ≤ (T : Subgroup X) := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      exact (hmemT x).mp (hX'S hx)
    have hZ₀X₀ : Z ≤ X₀ := by
      intro z hz
      rw [Subgroup.mem_comap]
      apply hZX'
      rw [← hZmap]
      exact ⟨z, hz, rfl⟩
    have hD₀X₀ : D₀ ≤ Subgroup.normalizer (X₀ : Set X) := by
      intro d hd
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [Subgroup.mem_comap] at hx ⊢
        have hd' : φ d ∈ D := ⟨d, hd, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hDX' hd') (φ x)).mp hx
      · intro hx
        rw [Subgroup.mem_comap] at hx ⊢
        have hd' : φ d ∈ D := ⟨d, hd, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hDX' hd') (φ x)).mpr
          (by simpa only [map_mul, map_inv] using hx)
    have hX'map : X₀.map φ = X' := Subgroup.map_comap_eq_self (by
      rw [Subgroup.range_subtype]
      exact hX'S.trans hS.le)
    rcases hirrT X₀ hZ₀X₀ hX₀T hD₀X₀ with hX₀Z | hX₀T
    · left
      rw [← hX'map, hX₀Z, hZmap]
    · right
      rw [← hX'map, hX₀T, hTmap]
  · intro S' S'' hS' hS'' hne
    let P' : Sylow 2 X := hS'.toSylow
    let P'' : Sylow 2 X := hS''.toSylow
    have hP'map : (P' : Subgroup X).map φ = S' := Subgroup.map_subgroupOf_eq_of_le hS'.le
    have hP''map : (P'' : Subgroup X).map φ = S'' := Subgroup.map_subgroupOf_eq_of_le hS''.le
    have hPne : (P' : Subgroup X) ⊓ (P'' : Subgroup X) ≠ ⊥ := by
      intro hbot
      apply hne
      have h1 := congrArg (Subgroup.map φ) hbot
      rw [Subgroup.map_inf (P' : Subgroup X) (P'' : Subgroup X) φ hφ, Subgroup.map_bot,
        hP'map, hP''map] at h1
      exact h1
    have hEq : P' = P'' := htiX P' P'' hPne
    rw [← hP'map, ← hP''map, hEq]
  · intro S' S'' hS' hS'' hS'ne hS''ne
    let P' : Sylow 2 X := hS'.toSylow
    let P'' : Sylow 2 X := hS''.toSylow
    have hP'map : (P' : Subgroup X).map φ = S' := Subgroup.map_subgroupOf_eq_of_le hS'.le
    have hP''map : (P'' : Subgroup X).map φ = S'' := Subgroup.map_subgroupOf_eq_of_le hS''.le
    have hP'ne : P' ≠ T := by
      intro h
      apply hS'ne
      have h1 : (P' : Subgroup X) = (T : Subgroup X) := by rw [h]
      rw [← hP'map, ← hTmap, h1]
    have hP''ne : P'' ≠ T := by
      intro h
      apply hS''ne
      have h1 : (P'' : Subgroup X) = (T : Subgroup X) := by rw [h]
      rw [← hP''map, ← hTmap, h1]
    obtain ⟨t, ht, htP⟩ := htrans2 P' P'' hP'ne hP''ne
    refine ⟨(φ t)⁻¹, S.inv_mem (by rw [← hTmap]; exact ⟨t, ht, rfl⟩), ?_⟩
    have hsmul : ((t • P' : Sylow 2 X) : Subgroup X) =
        CFSG.Goldschmidt.conjSub t⁻¹ (P' : Subgroup X) :=
      w183l313_smul_eq_conjSub_inv t P'
    rw [htP] at hsmul
    have hgoal : S'' = conjSubgroup S' (φ t)⁻¹ := by
      rw [← hP''map, hsmul]
      rw [w183l313_map_conjSub, hP'map]
      rfl
    exact hgoal.symm

private theorem w183l313_center_inf_normalizer {Q S D S' D' : Subgroup Γ}
    (hB : BorelU34 Q S D) (hB' : BorelU34 Q S' D') (hS : IsSylowIn 2 S Q)
    (hS' : IsSylowIn 2 S' Q) (hne : S ≠ S') :
    sylowCenter S ⊓ Subgroup.normalizer ((sylowCenter S' : Subgroup Γ) : Set Γ) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxZ, hxN⟩ := hx
  have hxS : x ∈ S := (mem_sylowCenter.mp hxZ).1
  have hxQ : x ∈ Q := hS.le hxS
  have hxNQ : x ∈ Subgroup.normalizer (Q : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact Q.mul_mem (Q.mul_mem hxQ hq) (Q.inv_mem hxQ)
    · intro hq
      have h1 : x⁻¹ * (x * q * x⁻¹) * x ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem hxQ) hq) hxQ
      simpa [mul_assoc] using h1
  have hxN' : x ∈ Subgroup.normalizer (S' : Set Γ) := by
    have hS'x : IsSylowIn 2 (conjSubgroup S' x) Q := by
      have hQx : Q.map (MulAut.conj x⁻¹).toMonoidHom = Q :=
        conjSubgroup_eq_iff_mem_normalizer.mpr hxNQ
      have h := (E1.isSylowIn_map_mulEquiv (MulAut.conj x⁻¹)).mpr hS'
      rwa [hQx] at h
    have hZle : sylowCenter S' ≤ conjSubgroup S' x := by
      have hmono := E3.conjSubgroup_mono_left x (sylowCenter_le S')
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hxN] at hmono
    have hne' : S' ⊓ conjSubgroup S' x ≠ ⊥ := by
      intro hbot
      have hZne : sylowCenter S' ≠ ⊥ := by
        intro hb
        have := hB'.card_center
        rw [hb] at this
        simp at this
      apply hZne
      apply le_bot_iff.mp
      rw [← hbot]
      exact le_inf (sylowCenter_le S') hZle
    have hS'eq : conjSubgroup S' x = S' :=
      (hB'.ti S' (conjSubgroup S' x) hS' hS'x hne').symm
    exact conjSubgroup_eq_iff_mem_normalizer.mp hS'eq
  have hxS' : x ∈ S' := by
    let X := ↥Q
    let φ : X →* Γ := Q.subtype
    let x' : X := ⟨x, hxQ⟩
    have hx'T : x' ∈ (hS.toSylow : Subgroup X) := by
      rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf]
      exact hxS
    have hP : IsPGroup 2 (Subgroup.zpowers x') :=
      hS.toSylow.isPGroup'.to_le (Subgroup.zpowers_le.mpr hx'T)
    have hx'N : x' ∈ Subgroup.normalizer ((hS'.toSylow : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      change z ∈ S'.subgroupOf Q ↔ x' * z * x'⁻¹ ∈ S'.subgroupOf Q
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      change (z : Γ) ∈ S' ↔ x * (z : Γ) * x⁻¹ ∈ S'
      exact Subgroup.mem_normalizer_iff.mp hxN' (z : Γ)
    have hfix : hS'.toSylow ∈ MulAction.fixedPoints (Subgroup.zpowers x') (Sylow 2 X) :=
      (Subgroup.sylow_mem_fixedPoints_iff (Subgroup.zpowers x')).mpr
        (Subgroup.zpowers_le.mpr hx'N)
    have hle : Subgroup.zpowers x' ≤ (hS'.toSylow : Subgroup X) :=
      (IsPGroup.sylow_mem_fixedPoints_iff hP).mp hfix
    have hx' : x' ∈ (hS'.toSylow : Subgroup X) := hle (Subgroup.mem_zpowers x')
    rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hx'
    exact hx'
  have hSS' : S ⊓ S' = ⊥ := by
    by_contra h
    exact hne (hB.ti S S' hS hS' h)
  have : x ∈ S ⊓ S' := ⟨hxS, hxS'⟩
  rwa [hSS'] at this

theorem w183l313_center_pair {Q S S' : Subgroup Γ} (hQ : IsU3 ↥Q 2) (hS : IsSylowIn 2 S Q)
    (hS' : IsSylowIn 2 S' Q) (hne : S ≠ S') :
    Nat.card (sylowCenter S) = 4 ∧
      sylowCenter S ⊓ Subgroup.normalizer ((sylowCenter S' : Subgroup Γ) : Set Γ) = ⊥ ∧
      sylowCenter S' ⊓ Subgroup.normalizer ((sylowCenter S : Subgroup Γ) : Set Γ) = ⊥ := by
  obtain ⟨D, hB⟩ := w183l313_borel_exists hQ hS
  obtain ⟨D', hB'⟩ := w183l313_borel_exists hQ hS'
  refine ⟨hB.card_center, ?_, ?_⟩
  · exact w183l313_center_inf_normalizer hB hB' hS hS' hne
  · exact w183l313_center_inf_normalizer hB' hB hS' hS (Ne.symm hne)

theorem w183l313_center_normalized {Q S T : Subgroup Γ} (hQ : IsU3 ↥Q 2) (hS : IsSylowIn 2 S Q)
    (hTQ : IsSylowIn 2 (T ⊓ Q) Q) (hZT : sylowCenter S ≤ T)
    (hTn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) :
    S = T ⊓ Q ∧ ∀ t ∈ T, t ∈ Subgroup.normalizer ((sylowCenter S : Subgroup Γ) : Set Γ) := by
  obtain ⟨D, hB⟩ := w183l313_borel_exists hQ hS
  have hZne : sylowCenter S ≠ ⊥ := by
    intro hbot
    have := hB.card_center
    rw [hbot] at this
    simp at this
  have hne : S ⊓ (T ⊓ Q) ≠ ⊥ := by
    intro hbot
    apply hZne
    apply le_bot_iff.mp
    rw [← hbot]
    exact le_inf (sylowCenter_le S) (le_inf hZT (sylowCenter_le S |>.trans hS.le))
  have hSeq : S = T ⊓ Q := hB.ti S (T ⊓ Q) hS hTQ hne
  refine ⟨hSeq, fun t ht => ?_⟩
  have htN : t ∈ Subgroup.normalizer ((T ⊓ Q : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht), hTn t ht x hx.2⟩
    · intro hx
      rw [Subgroup.mem_inf] at hx ⊢
      refine ⟨?_, ?_⟩
      · have h1 := T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht
        simpa [mul_assoc] using h1
      · have h1 := hTn t⁻¹ (T.inv_mem ht) (t * x * t⁻¹) hx.2
        simpa [mul_assoc] using h1
  rw [hSeq]
  exact w183l313_normalizes_center_aux htN

theorem w183l313_normalizes_sylow {Q S : Subgroup Γ} (hQ : IsU3 ↥Q 2) (hS : IsSylowIn 2 S Q)
    {y : Γ} (hyQ : y ∈ Subgroup.normalizer (Q : Set Γ))
    (hyZ : y ∈ Subgroup.normalizer ((sylowCenter S : Subgroup Γ) : Set Γ)) :
    y ∈ Subgroup.normalizer (S : Set Γ) := by
  obtain ⟨D, hB⟩ := w183l313_borel_exists hQ hS
  have hS' : IsSylowIn 2 (conjSubgroup S y) Q := by
    have hQy : Q.map (MulAut.conj y⁻¹).toMonoidHom = Q :=
      conjSubgroup_eq_iff_mem_normalizer.mpr hyQ
    have h := (E1.isSylowIn_map_mulEquiv (MulAut.conj y⁻¹)).mpr hS
    rwa [hQy] at h
  have hne : S ⊓ conjSubgroup S y ≠ ⊥ := by
    intro hbot
    have hZle : sylowCenter S ≤ S ⊓ conjSubgroup S y := by
      refine le_inf (sylowCenter_le S) ?_
      have hmono := E3.conjSubgroup_mono_left y (sylowCenter_le S)
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hyZ] at hmono
    rw [hbot] at hZle
    have hZbot : sylowCenter S = ⊥ := le_bot_iff.mp hZle
    have := hB.card_center
    rw [hZbot] at this
    simp at this
  exact conjSubgroup_eq_iff_mem_normalizer.mp (hB.ti S (conjSubgroup S y) hS hS' hne).symm

end Certified

theorem w183l313_normalizes_center {S : Subgroup Γ} {y : Γ}
    (hy : y ∈ Subgroup.normalizer (S : Set Γ)) :
    y ∈ Subgroup.normalizer ((sylowCenter S : Subgroup Γ) : Set Γ) :=
  w183l313_normalizes_center_aux hy

end CFSG.LocalAnalysis.WeakClosure81

end
