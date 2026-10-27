module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSplitData
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSec

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

section Entries

variable {F : Type} [Field F]

theorem natE_torusElt_mulVec_zero (a : Fˣ) (u : Fin 2 → F) :
    (((torusElt a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 0 = (a : F) * u 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, torusElt_apply_00, torusElt_apply_01]

theorem natE_torusElt_mulVec_one (a : Fˣ) (u : Fin 2 → F) :
    (((torusElt a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 1 = ((a⁻¹ : Fˣ) : F) * u 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, torusElt_apply_10, torusElt_apply_11]

theorem natE_mulVec_one_of_mem_utri {g : SL(2, F)} (hg : g ∈ utri F) (u : Fin 2 → F) :
    ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 1 = u 1 := by
  rw [eq_utriElt_of_mem_utri hg]
  exact utriElt_mulVec_apply_one _ u

end Entries

section Coord

variable {L E N : Subgroup G} {F : Type} [Field F] {α : ↥L →* SL(2, F)}

theorem isNatSecCoord_natSecVec {β : ↥E →* Multiplicative (Fin 2 → F)}
    (hβs : Function.Surjective β) (hβk : β.ker = N.subgroupOf E)
    (hβe : ∀ l : ↥L, ∀ u w : ↥E, (w : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β w) =
        (α l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hE : ∀ l ∈ L, ∀ x ∈ E, l * x * l⁻¹ ∈ E) : IsNatSecCoord L E N α (natSecVec β) :=
  ⟨fun _ hx _ hy => natSecVec_mul β hx hy, fun _ hx => natSecVec_eq_zero_iff hβk hx,
    exists_natSecVec_eq hβs, fun l x hx => hE l l.2 x hx,
    fun l x hx => natSecVec_conj hβe l hx (hE l l.2 x hx)⟩

namespace IsNatSecCoord

variable {v : G → Fin 2 → F}

theorem commutator_left_mem (hv : IsNatSecCoord L E N α v) (l : ↥L) {x : G} (hx : x ∈ E) :
    ⁅(l : G), x⁆ ∈ E := by
  rw [commutatorElement_def]
  exact mul_mem (hv.conj_mem l x hx) (inv_mem hx)

theorem map_commutator_left (hv : IsNatSecCoord L E N α v) (l : ↥L) {x : G} (hx : x ∈ E) :
    v ⁅(l : G), x⁆ = (α l : Matrix (Fin 2) (Fin 2) F) *ᵥ v x - v x := by
  rw [commutatorElement_def, hv.map_mul _ (hv.conj_mem l x hx) _ (inv_mem hx), hv.conj l x hx,
    hv.map_inv hx, sub_eq_add_neg]

theorem map_commutator_left_apply_one (hv : IsNatSecCoord L E N α v) {l : ↥L}
    (hl : α l ∈ utri F) {x : G} (hx : x ∈ E) : v ⁅(l : G), x⁆ 1 = 0 := by
  rw [hv.map_commutator_left l hx, Pi.sub_apply, natE_mulVec_one_of_mem_utri hl, sub_self]

theorem mulVec_eq_of_commutator_mem (hv : IsNatSecCoord L E N α v) (l : ↥L) {x : G}
    (hx : x ∈ E) (hc : ⁅(l : G), x⁆ ∈ N) : (α l : Matrix (Fin 2) (Fin 2) F) *ᵥ v x = v x := by
  have h := (hv.eq_zero_iff _ (hv.commutator_left_mem l hx)).mpr hc
  rw [hv.map_commutator_left l hx] at h
  exact sub_eq_zero.mp h

theorem apply_one_eq_zero_of_commutator_mem (hv : IsNatSecCoord L E N α v)
    (hα : Function.Surjective α) {S : Subgroup G} (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F)
    {x : G} (hx : x ∈ E) (hc : ∀ s : ↥L, (s : G) ∈ S → ⁅(s : G), x⁆ ∈ N) : v x 1 = 0 := by
  obtain ⟨s, hs⟩ := hα (utriElt 1)
  have hsS : (s : G) ∈ S := (hmem s).mpr (by rw [hs]; exact utriElt_mem_utri 1)
  have h := congrFun (hv.mulVec_eq_of_commutator_mem s hx (hc s hsS)) 0
  rw [hs, utriElt_mulVec_apply_zero, one_mul, add_eq_left] at h
  exact h

end IsNatSecCoord

end Coord

private theorem natE_sq_add_add_one {F : Type} [Field F] [CharP F 2] {ψ : F → F}
    (hadd : ∀ x y, ψ (x + y) = ψ x + ψ y) (hmul : ∀ c : F, c ≠ 0 → ∀ x, ψ (c * x) = c⁻¹ * ψ x)
    (hg : ψ 1 ≠ 0) {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) : c ^ 2 + c + 1 = 0 := by
  have hc1' : c + 1 ≠ 0 := by
    intro h
    apply hc1
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have h1 : ψ (c + 1) = (c + 1)⁻¹ * ψ 1 := by simpa using hmul (c + 1) hc1' 1
  have h2 : ψ c = c⁻¹ * ψ 1 := by simpa using hmul c hc0 1
  have h3 := hadd c 1
  rw [h1, h2] at h3
  have h4 : (c + 1)⁻¹ = c⁻¹ + 1 := mul_right_cancel₀ hg (h3.trans (by ring))
  have h5 : c = (c + 1) + c * (c + 1) := by
    calc c = c * ((c + 1) * (c + 1)⁻¹) := by rw [mul_inv_cancel₀ hc1', mul_one]
      _ = c * (c + 1) * (c⁻¹ + 1) := by rw [h4]; ring
      _ = (c + 1) * (c * c⁻¹) + c * (c + 1) := by ring
      _ = (c + 1) + c * (c + 1) := by rw [mul_inv_cancel₀ hc0, mul_one]
  linear_combination (-1 : F) * h5

theorem natE_eq_zero_of_map_mul_inv {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 5 ≤ Nat.card F) {ψ : F → F} (hadd : ∀ x y, ψ (x + y) = ψ x + ψ y)
    (hmul : ∀ c : F, c ≠ 0 → ∀ x, ψ (c * x) = c⁻¹ * ψ x) (x : F) : ψ x = 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hg : ψ 1 = 0 := by
    by_contra hg
    set T : Finset F := Finset.univ \ {0, 1} with hT
    have hTcard : 2 < T.card := by
      have h01 : ({0, 1} : Finset F).card = 2 := Finset.card_pair zero_ne_one
      rw [hT, Finset.card_sdiff, Finset.inter_univ, h01, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.mp hTcard
    have hmemT : ∀ y ∈ T, y ≠ 0 ∧ y ≠ 1 := fun y hy => by
      rw [hT, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hy
      exact ⟨fun h => hy.2 (Or.inl h), fun h => hy.2 (Or.inr h)⟩
    have hroot : ∀ y ∈ T, y ^ 2 + y + 1 = 0 := fun y hy =>
      natE_sq_add_add_one hadd hmul hg (hmemT y hy).1 (hmemT y hy).2
    have hpair : ∀ y ∈ T, ∀ z ∈ T, y ≠ z → z = y + 1 := by
      intro y hy z hz hyz
      have h : (y - z) * (y + z + 1) = 0 := by
        linear_combination hroot y hy - hroot z hz
      have h' : y + z + 1 = 0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hyz)
      linear_combination h' - (y + 1) * CharTwo.two_eq_zero (R := F)
    exact hbd ((hpair a ha b hb hab).trans (hpair a ha d hd had).symm)
  by_cases hx : x = 0
  · have h := hadd 0 0
    rw [add_zero] at h
    rw [hx]
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  · have h := hmul x hx 1
    rw [mul_one, hg, mul_zero] at h
    exact h

structure G2qNatEConf (L1 L2 S Q1 Q2 Z1 Z2 W E : Subgroup G) {F₁ F₂ : Type} [Field F₁]
    [Field F₂] (α₁ : ↥L1 →* SL(2, F₁)) (α₂ : ↥L2 →* SL(2, F₂)) (vE : G → Fin 2 → F₁)
    (nv zv : G → Fin 2 → F₂) : Prop where
  split : G2qSplitData L2 Q2 Z2 W α₂ nv zv
  natE : IsNatSecCoord L1 E Z1 α₁ vE
  surj_left : Function.Surjective α₁
  memS_left : ∀ x : ↥L1, (x : G) ∈ S ↔ α₁ x ∈ utri F₁
  memS_right : ∀ x : ↥L2, (x : G) ∈ S ↔ α₂ x ∈ utri F₂
  ker_right : ∀ x : ↥L2, α₂ x = 1 ↔ (x : G) ∈ Q2
  le_left : S ≤ L1
  le_right : S ≤ L2
  core_left : Q1 ≤ S
  core_right : Q2 ≤ S
  conj_left : ∀ l ∈ L1, ∀ x ∈ Q1, l * x * l⁻¹ ∈ Q1
  center_left : ∀ z ∈ Z1, ∀ l ∈ L1, l * z = z * l
  comm_left : ∀ x ∈ Q1, ∀ y ∈ Q1, ⁅x, y⁆ ∈ Z1
  le_center : Z1 ≤ Z2
  W_le_left : W ≤ Q1
  mem_left_iff : ∀ z ∈ Z2, z ∈ Z1 ↔ zv z 1 = 0
  E_le : E ≤ Q1
  center_le_E : Z1 ≤ E
  exists_z₀ : ∃ z ∈ Z2, z ∈ E ∧ vE z = ![1, 0]
  R_comm : ∀ a ∈ ⁅Q2, L2⁆, ∀ b ∈ ⁅Q2, L2⁆, a * b = b * a
  R_inf_W : ⁅Q2, L2⁆ ⊓ W = Z2
  YS : ∀ s ∈ S, ∀ y ∈ ⁅Q2, L2⁆ ⊓ Q1, ⁅s, y⁆ ∈ Z1
  borel_left : ∀ b : ↥L1, α₁ b ∈ borel F₁ →
    (b : G) ∈ Subgroup.normalizer (L2 : Set G) ∧ (b : G) ∈ Subgroup.normalizer (Q2 : Set G)
  borel_right : ∀ l : ↥L2, α₂ l ∈ borel F₂ → (l : G) ∈ Subgroup.normalizer (Q1 : Set G)
  card_eq : Nat.card F₁ = Nat.card F₂
  five_le : 5 ≤ Nat.card F₂

namespace G2qNatEConf

variable {L1 L2 S Q1 Q2 Z1 Z2 W E : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {α₁ : ↥L1 →* SL(2, F₁)} {α₂ : ↥L2 →* SL(2, F₂)} {vE : G → Fin 2 → F₁}
  {nv zv : G → Fin 2 → F₂}

theorem commutator_mem_left_of_mem_center
    (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) {s z : G} (hs : s ∈ S)
    (hz : z ∈ Z2) : ⁅s, z⁆ ∈ Z1 :=
  (hC.mem_left_iff _ (hC.split.nat.commutator_left_mem ⟨s, hC.le_right hs⟩ hz)).mpr
    (hC.split.nat.map_commutator_left_apply_one
      ((hC.memS_right ⟨s, hC.le_right hs⟩).mp hs) hz)

private theorem exists_mem_center_vE_eq
    (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) (a : F₁) :
    ∃ z ∈ Z2, z ∈ E ∧ vE z = ![a, 0] := by
  obtain ⟨z₀, hz₀Z, hz₀E, hz₀v⟩ := hC.exists_z₀
  by_cases ha : a = 0
  · refine ⟨1, one_mem _, one_mem _, ?_⟩
    rw [hC.natE.map_one, ha]
    funext i
    fin_cases i <;> rfl
  obtain ⟨b, hb⟩ := hC.surj_left (torusElt (Units.mk0 a ha))
  have hbB : α₁ b ∈ borel F₁ := by rw [hb]; exact torusElt_mem_borel _
  refine ⟨(b : G) * z₀ * (b : G)⁻¹, hC.split.torus_conj_mem_Z (hC.borel_left b hbB).2 hz₀Z,
    hC.natE.conj_mem b z₀ hz₀E, ?_⟩
  rw [hC.natE.conj b z₀ hz₀E, hb, hz₀v]
  funext i
  fin_cases i
  · simp [natE_torusElt_mulVec_zero]
  · simp [natE_torusElt_mulVec_one]

theorem mem_center_right_iff (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    {x : G} (hx : x ∈ E) : x ∈ Z2 ↔ vE x 1 = 0 := by
  constructor
  · intro hxZ
    exact hC.natE.apply_one_eq_zero_of_commutator_mem hC.surj_left hC.memS_left hx
      fun s hs => hC.commutator_mem_left_of_mem_center hs hxZ
  · intro h1
    obtain ⟨z, hzZ, hzE, hzv⟩ := hC.exists_mem_center_vE_eq (vE x 0)
    have hv : vE z = vE x := by
      rw [hzv]
      funext i
      fin_cases i
      · rfl
      · exact h1.symm
    have hm := hC.natE.inv_mul_mem hzE hx hv
    rw [show x = z * (z⁻¹ * x) by group]
    exact mul_mem hzZ (hC.le_center hm)

theorem commute_center_of_commute (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    {x : G} (hx : x ∈ E) (hx1 : vE x 1 ≠ 0) (hxc : ∀ z ∈ Z2, x * z = z * x) {y : G}
    (hy : y ∈ E) {z : G} (hz : z ∈ Z2) : y * z = z * y := by
  by_cases hy1 : vE y 1 = 0
  · exact hC.split.comm z hz y (hC.split.Z_le_Q ((hC.mem_center_right_iff hy).mpr hy1))
  obtain ⟨b, hb⟩ := hC.surj_left (torusElt (Units.mk0 (vE x 1 / vE y 1) (div_ne_zero hx1 hy1)))
  have hbB : α₁ b ∈ borel F₁ := by rw [hb]; exact torusElt_mem_borel _
  have hbQ := (hC.borel_left b hbB).2
  have hx'E : (b : G) * x * (b : G)⁻¹ ∈ E := hC.natE.conj_mem b x hx
  have hx'1 : vE ((b : G) * x * (b : G)⁻¹) 1 = vE y 1 := by
    rw [hC.natE.conj b x hx, hb, natE_torusElt_mulVec_one, Units.val_inv_eq_inv_val,
      Units.val_mk0, inv_div]
    field_simp
  have hyx' : ((b : G) * x * (b : G)⁻¹)⁻¹ * y ∈ Z2 :=
    (hC.mem_center_right_iff (mul_mem (inv_mem hx'E) hy)).mpr
      (by rw [hC.natE.map_inv_mul hx'E hy, Pi.sub_apply, hx'1, sub_self])
  have hz' : (b : G)⁻¹ * z * (b : G) ∈ Z2 := by
    simpa using hC.split.torus_conj_mem_Z (inv_mem hbQ) hz
  have hcx' : (b : G) * x * (b : G)⁻¹ * z = z * ((b : G) * x * (b : G)⁻¹) := by
    have h := hxc _ hz'
    calc (b : G) * x * (b : G)⁻¹ * z = (b : G) * (x * ((b : G)⁻¹ * z * (b : G))) * (b : G)⁻¹ := by
          group
      _ = (b : G) * (((b : G)⁻¹ * z * (b : G)) * x) * (b : G)⁻¹ := by rw [h]
      _ = z * ((b : G) * x * (b : G)⁻¹) := by group
  have hcz := hC.split.comm z hz _ (hC.split.Z_le_Q hyx')
  calc y * z = ((b : G) * x * (b : G)⁻¹) * ((((b : G) * x * (b : G)⁻¹)⁻¹ * y) * z) := by group
    _ = ((b : G) * x * (b : G)⁻¹) * (z * (((b : G) * x * (b : G)⁻¹)⁻¹ * y)) := by rw [hcz]
    _ = ((b : G) * x * (b : G)⁻¹ * z) * (((b : G) * x * (b : G)⁻¹)⁻¹ * y) := by group
    _ = (z * ((b : G) * x * (b : G)⁻¹)) * (((b : G) * x * (b : G)⁻¹)⁻¹ * y) := by rw [hcx']
    _ = z * y := by group

theorem mem_core_right_of_commute (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    {e : G} (he : e ∈ S) (hc : ∀ z ∈ Z2, e * z = z * e) : e ∈ Q2 := by
  have heL : e ∈ L2 := hC.le_right he
  obtain ⟨z, hz, hzv⟩ := hC.split.nat.surj ![0, 1]
  obtain ⟨r, hr⟩ := mem_utri_iff.mp ((hC.memS_right ⟨e, heL⟩).mp he)
  have h1 : zv (e * z * e⁻¹) = zv z := by rw [hc z hz, mul_inv_cancel_right]
  have h2 := hC.split.nat.conj ⟨e, heL⟩ z hz
  rw [h1, hr, hzv] at h2
  have h0 := congrFun h2 0
  rw [utriElt_mulVec_apply_zero] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, zero_add] at h0
  refine (hC.ker_right ⟨e, heL⟩).mp ?_
  rw [hr, ← h0, utriElt_zero]

theorem E_le_core_right (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) :
    E ≤ Q2 := by
  by_contra hle
  have hinf : ∀ y ∈ E, y ∈ Q2 → y ∈ Z2 := by
    intro y hyE hyQ
    by_contra hyZ
    have hy1 : vE y 1 ≠ 0 := fun h => hyZ ((hC.mem_center_right_iff hyE).mpr h)
    refine hle fun e he => hC.mem_core_right_of_commute (hC.core_left (hC.E_le he))
      fun z hz => ?_
    exact hC.commute_center_of_commute hyE hy1 (fun z hz => hC.split.comm z hz y hyQ) he hz
  obtain ⟨x, hxE, hxQ⟩ := SetLike.not_le_iff_exists.mp hle
  have hxS : x ∈ S := hC.core_left (hC.E_le hxE)
  have hxL : x ∈ L2 := hC.le_right hxS
  obtain ⟨r, hr⟩ := mem_utri_iff.mp ((hC.memS_right ⟨x, hxL⟩).mp hxS)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hr
    exact hxQ ((hC.ker_right _).mp hr)
  obtain ⟨a, haQ, hav⟩ := hC.split.natW.surj ![0, 1]
  have hcE : ⁅x, a⁆ ∈ E := hC.natE.commutator_mem hxE ⟨a, hC.le_left (hC.core_right haQ)⟩
  have hcQ : ⁅x, a⁆ ∈ Q2 := hC.split.natW.commutator_left_mem ⟨x, hxL⟩ haQ
  have h0 := (hC.split.natW.eq_zero_iff _ hcQ).mpr (hC.split.center_le (hinf _ hcE hcQ))
  rw [hC.split.natW.map_commutator_left ⟨x, hxL⟩ haQ, hr, hav] at h0
  have k := congrFun h0 0
  rw [Pi.sub_apply, utriElt_mulVec_apply_zero] at k
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, zero_add, sub_zero,
    Pi.zero_apply] at k
  exact hr0 k

end G2qNatEConf

end CFSG.Quasithin.F112R.St84

end
