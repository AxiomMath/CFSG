module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSplitCoord

import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocalAbelian

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F]

open Classical in
noncomputable def natSecScalar (E : Subgroup G) (v φ : G → Fin 2 → F) : F :=
  if h : ∃ s : F, ∀ x ∈ E, φ x = s • v x then h.choose else 0

theorem natSecScalar_spec {E : Subgroup G} {v φ : G → Fin 2 → F}
    (h : ∃ s : F, ∀ x ∈ E, φ x = s • v x) : ∀ x ∈ E, φ x = natSecScalar E v φ • v x := by
  rw [natSecScalar, dif_pos h]
  exact h.choose_spec

noncomputable def natSecConjScalar (E : Subgroup G) (v : G → Fin 2 → F) (k : G) : F :=
  natSecScalar E v fun x => v (k * x * k⁻¹)

theorem natSecConjScalar_spec {E : Subgroup G} {v : G → Fin 2 → F} {k : G}
    (h : ∃ s : F, ∀ x ∈ E, v (k * x * k⁻¹) = s • v x) :
    ∀ x ∈ E, v (k * x * k⁻¹) = natSecConjScalar E v k • v x :=
  natSecScalar_spec h

namespace IsNatSecCoord

variable {L E N : Subgroup G} {α : ↥L →* SL(2, F)} {v : G → Fin 2 → F}

theorem natSecConjScalar_one (hv : IsNatSecCoord L E N α v) : natSecConjScalar E v 1 = 1 := by
  have h : ∃ s : F, ∀ x ∈ E, v (1 * x * 1⁻¹) = s • v x :=
    ⟨1, fun x _ => by rw [one_mul, inv_one, mul_one, one_smul]⟩
  refine hv.smul_injective fun x hx => ?_
  rw [← natSecConjScalar_spec h x hx, one_mul, inv_one, mul_one, one_smul]

theorem natSecConjScalar_mul (hv : IsNatSecCoord L E N α v) {k k' : G}
    (hk'E : ∀ x ∈ E, k' * x * k'⁻¹ ∈ E) (hk : ∃ s : F, ∀ x ∈ E, v (k * x * k⁻¹) = s • v x)
    (hk' : ∃ s : F, ∀ x ∈ E, v (k' * x * k'⁻¹) = s • v x)
    (hkk' : ∃ s : F, ∀ x ∈ E, v (k * k' * x * (k * k')⁻¹) = s • v x) :
    natSecConjScalar E v (k * k') = natSecConjScalar E v k * natSecConjScalar E v k' := by
  refine hv.smul_injective fun x hx => ?_
  rw [← natSecConjScalar_spec hkk' x hx, mul_smul, ← natSecConjScalar_spec hk' x hx,
    ← natSecConjScalar_spec hk _ (hk'E x hx),
    show k * k' * x * (k * k')⁻¹ = k * (k' * x * k'⁻¹) * k⁻¹ by group]

end IsNatSecCoord

structure G2qSplitData (L Q Z W : Subgroup G) (α : ↥L →* SL(2, F)) (nv zv : G → Fin 2 → F) :
    Prop where
  surj : Function.Surjective α
  le : Q ≤ L
  center_le : Z ≤ W
  le_Q : W ≤ Q
  comm : ∀ z ∈ Z, ∀ a ∈ Q, a * z = z * a
  mem_center : ∀ a ∈ Q, (∀ b ∈ Q, b * a = a * b) → a ∈ Z
  commutator_mem : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z
  commutator_W : ∀ w ∈ W, ∀ ℓ ∈ L, ⁅w, ℓ⁆ ∈ Z
  natW : IsNatSecCoord L Q W α nv
  nat : IsNatSecCoord L Z ⊥ α zv

private theorem conj_eq_mul_commutator (ℓ w : G) : ℓ * w * ℓ⁻¹ = w * ⁅w⁻¹, ℓ⁆ := by
  rw [commutatorElement_def]
  group

private theorem conj_conj_eq (k ℓ x : G) :
    k * (ℓ * x * ℓ⁻¹) * k⁻¹ = (k * ℓ * k⁻¹ * ℓ⁻¹) * (ℓ * (k * x * k⁻¹) * ℓ⁻¹) *
      (k * ℓ * k⁻¹ * ℓ⁻¹)⁻¹ := by
  group

namespace G2qSplitData

variable {L Q Z W : Subgroup G} {α : ↥L →* SL(2, F)} {nv zv : G → Fin 2 → F}

theorem conj_mem_commutator_of_conj_mem {k : G}
    (hkQ : ∀ a ∈ Q, k * a * k⁻¹ ∈ Q) (hkL : ∀ ℓ ∈ L, k * ℓ * k⁻¹ ∈ L) {y : G}
    (hy : y ∈ ⁅Q, L⁆) : k * y * k⁻¹ ∈ ⁅Q, L⁆ := by
  have hle : ⁅Q, L⁆ ≤ ⁅Q, L⁆.comap (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha ℓ hℓ
    rw [Subgroup.mem_comap]
    change k * ⁅a, ℓ⁆ * k⁻¹ ∈ ⁅Q, L⁆
    rw [conjugate_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hkQ a ha) (hkL ℓ hℓ)
  exact hle hy

theorem Z_le_Q (hd : G2qSplitData L Q Z W α nv zv) : Z ≤ Q :=
  hd.center_le.trans hd.le_Q

theorem conj_mem_Q (hd : G2qSplitData L Q Z W α nv zv) {ℓ a : G} (hℓ : ℓ ∈ L) (ha : a ∈ Q) :
    ℓ * a * ℓ⁻¹ ∈ Q :=
  hd.natW.conj_mem ⟨ℓ, hℓ⟩ a ha

theorem conj_eq_of_mem (hd : G2qSplitData L Q Z W α nv zv) {a z : G} (ha : a ∈ Q)
    (hz : z ∈ Z) : a * z * a⁻¹ = z := by
  rw [hd.comm z hz a ha, mul_inv_cancel_right]

theorem commutator_mul_left (hd : G2qSplitData L Q Z W α nv zv) {a b c : G} (ha : a ∈ Q)
    (hb : b ∈ Q) (hc : c ∈ Z) : ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have h : c * b * c⁻¹ = b := by
    rw [← hd.comm c hc b hb, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * b * (a * c)⁻¹ * b⁻¹ = a * (c * b * c⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem commutator_mul_right (hd : G2qSplitData L Q Z W α nv zv) {a b c : G} (ha : a ∈ Q)
    (hb : b ∈ Q) (hc : c ∈ Z) : ⁅a, b * c⁆ = ⁅a, b⁆ := by
  have h : c * a⁻¹ * c⁻¹ = a⁻¹ := by
    rw [← hd.comm c hc a⁻¹ (inv_mem ha), mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * (c * a⁻¹ * c⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem conj_mem_W (hd : G2qSplitData L Q Z W α nv zv) {ℓ w : G} (hℓ : ℓ ∈ L) (hw : w ∈ W) :
    ℓ * w * ℓ⁻¹ ∈ W := by
  rw [conj_eq_mul_commutator]
  exact mul_mem hw (hd.center_le (hd.commutator_W _ (inv_mem hw) ℓ hℓ))

theorem mem_W (hd : G2qSplitData L Q Z W α nv zv) {x : G} (hx : x ∈ Q)
    (h : ∀ ℓ ∈ L, ⁅ℓ, x⁆ ∈ Z) : x ∈ W := by
  refine hd.natW.mem_of_conj_eq hd.surj hx fun ℓ => ?_
  have hc := h ℓ ℓ.2
  have hcQ := hd.Z_le_Q hc
  rw [show (ℓ : G) * x * (ℓ : G)⁻¹ = ⁅(ℓ : G), x⁆ * x by rw [commutatorElement_def]; group,
    hd.natW.map_mul _ hcQ _ hx, (hd.natW.eq_zero_iff _ hcQ).mpr (hd.center_le hc), zero_add]

theorem commutator_W_eq_one (hd : G2qSplitData L Q Z W α nv zv) {w w' : G} (hw : w ∈ W)
    (hw' : w' ∈ W) : ⁅w, w'⁆ = 1 := by
  have hc : ⁅w, w'⁆ ∈ Z := hd.commutator_W w hw w' (hd.le (hd.le_Q hw'))
  have hfix : ∀ ℓ : ↥L, zv ((ℓ : G) * ⁅w, w'⁆ * (ℓ : G)⁻¹) = zv ⁅w, w'⁆ := by
    intro ℓ
    have h1 := hd.commutator_W _ (inv_mem hw) ℓ ℓ.2
    have h2 := hd.commutator_W _ (inv_mem hw') ℓ ℓ.2
    rw [conjugate_commutatorElement, conj_eq_mul_commutator (ℓ : G) w,
      conj_eq_mul_commutator (ℓ : G) w',
      hd.commutator_mul_left (hd.le_Q hw) (mul_mem (hd.le_Q hw') (hd.Z_le_Q h2)) h1,
      hd.commutator_mul_right (hd.le_Q hw) (hd.le_Q hw') h2]
  have h := hd.nat.mem_of_conj_eq hd.surj hc hfix
  rwa [Subgroup.mem_bot] at h

theorem commutator_le_Q (hd : G2qSplitData L Q Z W α nv zv) : ⁅Q, L⁆ ≤ Q :=
  Subgroup.commutator_le.mpr fun _ ha ℓ hℓ => hd.natW.commutator_mem ha ⟨ℓ, hℓ⟩

theorem center_le_commutator (hd : G2qSplitData L Q Z W α nv zv) : Z ≤ ⁅Q, L⁆ := by
  intro z hz
  obtain ⟨y, hyR, hyZ, hyv⟩ := hd.nat.exists_mem_commutator hd.surj (zv z)
  rw [← hd.nat.eq_of_eq hyZ hz hyv]
  exact Subgroup.commutator_mono hd.Z_le_Q le_rfl hyR

theorem exists_pair (hd : G2qSplitData L Q Z W α nv zv) {w : G} (hw : w ∈ W) :
    ∃ s : F, ∀ a ∈ Q, zv ⁅w, a⁆ = s • nv a := by
  have hwQ := hd.le_Q hw
  have hcZ : ∀ a ∈ Q, ⁅w, a⁆ ∈ Z := fun a ha => hd.commutator_W w hw a (hd.le ha)
  refine hd.natW.exists_eq_smul hd.surj (fun a ha b hb => ?_) (fun a _ haW => ?_)
    (fun ℓ a ha => ?_)
  · rw [show ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) by simp only [commutatorElement_def]; group,
      hd.conj_eq_of_mem ha (hcZ b hb), hd.nat.map_mul _ (hcZ a ha) _ (hcZ b hb)]
  · rw [hd.commutator_W_eq_one hw haW, hd.nat.map_one]
  · have hc : ⁅w⁻¹, (ℓ : G)⁆ ∈ Z := hd.commutator_W _ (inv_mem hw) ℓ ℓ.2
    rw [← hd.nat.conj ℓ _ (hcZ a ha), conjugate_commutatorElement,
      conj_eq_mul_commutator (ℓ : G) w, hd.commutator_mul_left hwQ (hd.conj_mem_Q ℓ.2 ha) hc]

theorem pair_eq_zero_iff (hd : G2qSplitData L Q Z W α nv zv) {w : G} (hw : w ∈ W) {s : F}
    (hs : ∀ a ∈ Q, zv ⁅w, a⁆ = s • nv a) : s = 0 ↔ w ∈ Z := by
  constructor
  · intro h0
    refine hd.mem_center w (hd.le_Q hw) fun b hb => ?_
    have h1 : ⁅w, b⁆ = 1 := hd.nat.eq_of_eq (hd.commutator_W w hw b (hd.le hb)) (one_mem _)
      (by rw [hs b hb, h0, zero_smul, hd.nat.map_one])
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · intro hwZ
    refine hd.natW.smul_injective fun a ha => ?_
    rw [← hs a ha, zero_smul,
      commutatorElement_eq_one_iff_mul_comm.mpr (hd.comm w hwZ a ha).symm, hd.nat.map_one]

theorem inv_mul_mem_of_pair_eq (hd : G2qSplitData L Q Z W α nv zv) {w w' : G} (hw : w ∈ W)
    (hw' : w' ∈ W) {s : F} (hs : ∀ a ∈ Q, zv ⁅w, a⁆ = s • nv a)
    (hs' : ∀ a ∈ Q, zv ⁅w', a⁆ = s • nv a) : w⁻¹ * w' ∈ Z := by
  refine hd.mem_center _ (mul_mem (inv_mem (hd.le_Q hw)) (hd.le_Q hw')) fun b hb => ?_
  have h := hd.nat.eq_of_eq (hd.commutator_W w hw b (hd.le hb))
    (hd.commutator_W w' hw' b (hd.le hb)) (by rw [hs b hb, hs' b hb])
  rw [commutatorElement_def, commutatorElement_def] at h
  have h1 : w * b * w⁻¹ = w' * b * w'⁻¹ := mul_right_cancel h
  calc b * (w⁻¹ * w') = w⁻¹ * (w * b * w⁻¹) * w' := by group
    _ = w⁻¹ * (w' * b * w'⁻¹) * w' := by rw [h1]
    _ = w⁻¹ * w' * b := by group

variable {k : G}

theorem torus_conj_mem_Z (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) {z : G} (hz : z ∈ Z) : k * z * k⁻¹ ∈ Z := by
  refine hd.mem_center _ ((Subgroup.mem_normalizer_iff.mp hkQ z).mp (hd.Z_le_Q hz))
    fun b hb => ?_
  have hb' : k⁻¹ * b * k ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hkQ _).mpr (by rwa [show k * (k⁻¹ * b * k) * k⁻¹ = b by group])
  calc b * (k * z * k⁻¹) = k * ((k⁻¹ * b * k) * z) * k⁻¹ := by group
    _ = k * (z * (k⁻¹ * b * k)) * k⁻¹ := by rw [hd.comm z hz _ hb']
    _ = k * z * k⁻¹ * b := by group

theorem torus_conj_mem_W (hd : G2qSplitData L Q Z W α nv zv)
    (hkL : k ∈ Subgroup.normalizer (L : Set G)) (hkQ : k ∈ Subgroup.normalizer (Q : Set G))
    {w : G} (hw : w ∈ W) : k * w * k⁻¹ ∈ W := by
  refine hd.mem_W ((Subgroup.mem_normalizer_iff.mp hkQ w).mp (hd.le_Q hw)) fun ℓ hℓ => ?_
  have hℓ' : k⁻¹ * ℓ * k ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hkL _).mpr (by rwa [show k * (k⁻¹ * ℓ * k) * k⁻¹ = ℓ by group])
  have e : ⁅ℓ, k * w * k⁻¹⁆ = k * ⁅w, k⁻¹ * ℓ * k⁆⁻¹ * k⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hd.torus_conj_mem_Z hkQ (inv_mem (hd.commutator_W w hw _ hℓ'))

theorem natW_conj_of_mem (hd : G2qSplitData L Q Z W α nv zv) {q y : G} (hq : q ∈ Q)
    (hy : y ∈ Q) : nv (q * y * q⁻¹) = nv y := by
  have hc := hd.commutator_mem q hq y hy
  rw [show q * y * q⁻¹ = ⁅q, y⁆ * y by rw [commutatorElement_def]; group,
    hd.natW.map_mul _ (hd.Z_le_Q hc) _ hy,
    (hd.natW.eq_zero_iff _ (hd.Z_le_Q hc)).mpr (hd.center_le hc), zero_add]

theorem exists_torus_natW (hd : G2qSplitData L Q Z W α nv zv)
    (hkL : k ∈ Subgroup.normalizer (L : Set G)) (hkQ : k ∈ Subgroup.normalizer (Q : Set G))
    (hkt : ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q) :
    ∃ s : F, ∀ a ∈ Q, nv (k * a * k⁻¹) = s • nv a := by
  have hkQ' : ∀ a ∈ Q, k * a * k⁻¹ ∈ Q := fun a ha => (Subgroup.mem_normalizer_iff.mp hkQ a).mp ha
  refine hd.natW.exists_eq_smul hd.surj (fun a ha b hb => ?_) (fun a ha haW => ?_)
    (fun ℓ a ha => ?_)
  · rw [show k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) by group,
      hd.natW.map_mul _ (hkQ' a ha) _ (hkQ' b hb)]
  · exact (hd.natW.eq_zero_iff _ (hkQ' a ha)).mpr (hd.torus_conj_mem_W hkL hkQ haW)
  · rw [conj_conj_eq, hd.natW_conj_of_mem (hkt ℓ ℓ.2) (hd.conj_mem_Q ℓ.2 (hkQ' a ha)),
      hd.natW.conj ℓ _ (hkQ' a ha)]

theorem exists_torus_nat (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) (hkt : ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q) :
    ∃ s : F, ∀ z ∈ Z, zv (k * z * k⁻¹) = s • zv z := by
  refine hd.nat.exists_eq_smul hd.surj (fun a ha b hb => ?_) (fun a _ ha1 => ?_)
    (fun ℓ a ha => ?_)
  · rw [show k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) by group,
      hd.nat.map_mul _ (hd.torus_conj_mem_Z hkQ ha) _ (hd.torus_conj_mem_Z hkQ hb)]
  · rw [Subgroup.mem_bot] at ha1
    rw [ha1, mul_one, mul_inv_cancel, hd.nat.map_one]
  · have hb := hd.torus_conj_mem_Z hkQ ha
    rw [conj_conj_eq, hd.conj_eq_of_mem (hkt ℓ ℓ.2) (hd.nat.conj_mem ℓ _ hb), hd.nat.conj ℓ _ hb]

theorem torus_pair (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) {μ ν s s' : F}
    (hμ : ∀ a ∈ Q, nv (k * a * k⁻¹) = μ • nv a) (hν : ∀ z ∈ Z, zv (k * z * k⁻¹) = ν • zv z)
    {w : G} (hw : w ∈ W) (hs : ∀ a ∈ Q, zv ⁅w, a⁆ = s • nv a)
    (hs' : ∀ a ∈ Q, zv ⁅k * w * k⁻¹, a⁆ = s' • nv a) : s' * μ = ν * s := by
  refine hd.natW.smul_injective fun a ha => ?_
  have hka : k * a * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hkQ a).mp ha
  rw [mul_smul, mul_smul, ← hμ a ha, ← hs' _ hka, ← hs a ha,
    ← hν _ (hd.commutator_W w hw a (hd.le ha)), conjugate_commutatorElement]

private theorem conj_mem_commutator (hd : G2qSplitData L Q Z W α nv zv) {ℓ y : G} (hℓ : ℓ ∈ L)
    (hy : y ∈ ⁅Q, L⁆) : ℓ * y * ℓ⁻¹ ∈ ⁅Q, L⁆ :=
  conj_mem_commutator_of_conj_mem (fun _ ha => hd.conj_mem_Q hℓ ha)
    (fun _ hm => mul_mem (mul_mem hℓ hm) (inv_mem hℓ)) hy

private theorem commutator_eq_of_split (hd : G2qSplitData L Q Z W α nv zv)
    (hsplit : ⁅Q, L⁆ ⊓ W = Z) {r : (Fin 2 → F) → G} (hrR : ∀ u, r u ∈ ⁅Q, L⁆)
    (hrQ : ∀ u, r u ∈ Q) (hrv : ∀ u, nv (r u) = u) {a b : G} (ha : a ∈ ⁅Q, L⁆)
    (hb : b ∈ ⁅Q, L⁆) : ⁅a, b⁆ = ⁅r (nv a), r (nv b)⁆ := by
  have hrep : ∀ a ∈ ⁅Q, L⁆, (r (nv a))⁻¹ * a ∈ Z := fun a ha => by
    rw [← hsplit]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hrR _)) ha,
      hd.natW.inv_mul_mem (hrQ _) (hd.commutator_le_Q ha) (hrv (nv a))⟩
  have ea : a = r (nv a) * ((r (nv a))⁻¹ * a) := (mul_inv_cancel_left _ _).symm
  have eb : b = r (nv b) * ((r (nv b))⁻¹ * b) := (mul_inv_cancel_left _ _).symm
  conv_lhs => rw [ea, eb]
  rw [hd.commutator_mul_left (hrQ _) (mul_mem (hrQ _) (hd.Z_le_Q (hrep b hb))) (hrep a ha),
    hd.commutator_mul_right (hrQ _) (hrQ _) (hrep b hb)]

private theorem pair_add_of_split (hd : G2qSplitData L Q Z W α nv zv)
    (hsplit : ⁅Q, L⁆ ⊓ W = Z) {r : (Fin 2 → F) → G} (hrR : ∀ u, r u ∈ ⁅Q, L⁆)
    (hrQ : ∀ u, r u ∈ Q) (hrv : ∀ u, nv (r u) = u) :
    (∀ x x' y, zv ⁅r (x + x'), r y⁆ = zv ⁅r x, r y⁆ + zv ⁅r x', r y⁆) ∧
      ∀ x y y', zv ⁅r x, r (y + y')⁆ = zv ⁅r x, r y⁆ + zv ⁅r x, r y'⁆ := by
  have hcZ : ∀ a ∈ ⁅Q, L⁆, ∀ b ∈ ⁅Q, L⁆, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hd.commutator_mem a (hd.commutator_le_Q ha) b (hd.commutator_le_Q hb)
  refine ⟨fun x x' y => ?_, fun x y y' => ?_⟩
  · have h := hd.commutator_eq_of_split hsplit hrR hrQ hrv (mul_mem (hrR x) (hrR x')) (hrR y)
    rw [hd.natW.map_mul _ (hrQ x) _ (hrQ x'), hrv, hrv, hrv] at h
    rw [← h, show ⁅r x * r x', r y⁆ = r x * ⁅r x', r y⁆ * (r x)⁻¹ * ⁅r x, r y⁆ by group,
      hd.conj_eq_of_mem (hrQ x) (hcZ _ (hrR x') _ (hrR y)),
      hd.nat.map_mul _ (hcZ _ (hrR x') _ (hrR y)) _ (hcZ _ (hrR x) _ (hrR y)), add_comm]
  · have h := hd.commutator_eq_of_split hsplit hrR hrQ hrv (hrR x) (mul_mem (hrR y) (hrR y'))
    rw [hd.natW.map_mul _ (hrQ y) _ (hrQ y'), hrv, hrv, hrv] at h
    rw [← h, show ⁅r x, r y * r y'⁆ = ⁅r x, r y⁆ * (r y * ⁅r x, r y'⁆ * (r y)⁻¹) by group,
      hd.conj_eq_of_mem (hrQ y) (hcZ _ (hrR x) _ (hrR y')),
      hd.nat.map_mul _ (hcZ _ (hrR x) _ (hrR y)) _ (hcZ _ (hrR x) _ (hrR y'))]

theorem commute_of_commutator_inf_eq [Finite F] [CharP F 2]
    (hd : G2qSplitData L Q Z W α nv zv) (hsplit : ⁅Q, L⁆ ⊓ W = Z) :
    ∀ a ∈ ⁅Q, L⁆, ∀ b ∈ ⁅Q, L⁆, a * b = b * a := by
  choose r hrR hrQ hrv using hd.natW.exists_mem_commutator hd.surj
  have hcZ : ∀ a ∈ ⁅Q, L⁆, ∀ b ∈ ⁅Q, L⁆, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hd.commutator_mem a (hd.commutator_le_Q ha) b (hd.commutator_le_Q hb)
  obtain ⟨hBadd₁, hBadd₂⟩ := hd.pair_add_of_split hsplit hrR hrQ hrv
  have hBalt : ∀ x, zv ⁅r x, r x⁆ = 0 := fun x => by
    rw [commutatorElement_self, hd.nat.map_one]
  have hBequiv : ∀ (A : SL(2, F)) x y,
      zv ⁅r ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x), r ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ y)⁆ =
        (A : Matrix (Fin 2) (Fin 2) F) *ᵥ zv ⁅r x, r y⁆ := by
    intro A x y
    obtain ⟨ℓ, rfl⟩ := hd.surj A
    have h := hd.commutator_eq_of_split hsplit hrR hrQ hrv (hd.conj_mem_commutator ℓ.2 (hrR x))
      (hd.conj_mem_commutator ℓ.2 (hrR y))
    rw [hd.natW.conj ℓ _ (hrQ x), hd.natW.conj ℓ _ (hrQ y), hrv, hrv,
      ← conjugate_commutatorElement] at h
    rw [← h, hd.nat.conj ℓ _ (hcZ _ (hrR x) _ (hrR y))]
  have hB0 : ∀ x y, zv ⁅r x, r y⁆ = 0 :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.pair_eq_zero _ hBadd₁ hBadd₂ hBalt hBequiv
  intro a ha b hb
  have h1 : ⁅a, b⁆ = 1 := hd.nat.eq_of_eq (hcZ a ha b hb) (one_mem _)
    (by rw [hd.commutator_eq_of_split hsplit hrR hrQ hrv ha hb, hB0, hd.nat.map_one])
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end G2qSplitData

end CFSG.Quasithin.F112R.St84

end
