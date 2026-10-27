module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LLam
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2WedgeP2

public section

namespace CFSG.Quasithin.H13.NFa2

open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

structure VMod (V L Z : Subgroup G) where
  α : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)
  Φ : ↥V →* Multiplicative (Fin 6 → ZMod 2)
  inj : Function.Injective Φ
  surj : Function.Surjective α
  hLV : L ≤ Subgroup.normalizer (V : Set G)
  equiv : ∀ (l : ↥L) (y y' : ↥V), (y' : G) = (l : G) * (y : G) * (l : G)⁻¹ →
    Multiplicative.toAdd (Φ y') = B5FinWedge.wedgeMat4
      ((α l : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (Φ y)
  z₀ : G
  z₀_Z : z₀ ∈ Z
  z₀_V : z₀ ∈ V
  Φz₀ : Multiplicative.toAdd (Φ ⟨z₀, z₀_V⟩) = Pi.single 0 1
  cent : ∀ l : ↥L, α l ∈ L3321.P2 → (l : G) ∈ Subgroup.centralizer (Z : Set G)

private theorem vmod_vec_neg : ∀ a : Fin 6 → ZMod 2, -a = a := by
  decide +kernel

private theorem vmod_vec_add_self : ∀ a : Fin 6 → ZMod 2, a + a = 0 := by
  decide +kernel

private theorem vmod_vec_cancel (A B C D : Fin 6 → ZMod 2) (h : A + B = C + D) :
    A = C + (D + B) := by
  calc A = A + (B + B) := by rw [vmod_vec_add_self, add_zero]
    _ = (A + B) + B := by rw [add_assoc]
    _ = (C + D) + B := by rw [h]
    _ = C + (D + B) := by rw [add_assoc]

private theorem vmod_vec_sum_zero (D B : Fin 6 → ZMod 2) (h : D + B = 0) : B = D := by
  calc B = (D + D) + B := by rw [vmod_vec_add_self, zero_add]
    _ = D + (D + B) := by rw [add_assoc]
    _ = D := by rw [h, add_zero]

private def vmodPhi {V L Z : Subgroup G} (m : VMod V L Z) (y : ↥V) : Fin 6 → ZMod 2 :=
  Multiplicative.toAdd (m.Φ y)

private theorem vmodPhi_mul {V L Z : Subgroup G} (m : VMod V L Z) (y y' : ↥V) :
    vmodPhi m (y * y') = vmodPhi m y + vmodPhi m y' := by
  simp [vmodPhi]

private theorem vmodPhi_one {V L Z : Subgroup G} (m : VMod V L Z) : vmodPhi m 1 = 0 := by
  simp [vmodPhi]

private theorem vmodPhi_inv {V L Z : Subgroup G} (m : VMod V L Z) (y : ↥V) :
    vmodPhi m y⁻¹ = vmodPhi m y := by
  simp [vmodPhi, vmod_vec_neg]

private theorem vmodPhi_eq_of_eq {V L Z : Subgroup G} (m : VMod V L Z) {y y' : ↥V}
    (h : vmodPhi m y = vmodPhi m y') : y = y' :=
  m.inj (Multiplicative.toAdd.injective h)

private theorem vmodPhi_eq_zero {V L Z : Subgroup G} (m : VMod V L Z) {y : ↥V}
    (h : vmodPhi m y = 0) : y = 1 := by
  apply vmodPhi_eq_of_eq m
  rw [vmodPhi_one]
  exact h

private def vmodZ0 {V L Z : Subgroup G} (m : VMod V L Z) : ↥V := ⟨m.z₀, m.z₀_V⟩

private theorem vmodPhi_z0 {V L Z : Subgroup G} (m : VMod V L Z) :
    vmodPhi m (vmodZ0 m) = Pi.single 0 1 :=
  m.Φz₀

private theorem vmod_conj_mem {V L Z : Subgroup G} (m : VMod V L Z) (l : ↥L) (y : ↥V) :
    (l : G) * (y : G) * (l : G)⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.1 (m.hLV l.2) (y : G)).1 y.2

private def vmodConj {V L Z : Subgroup G} (m : VMod V L Z) (l : ↥L) (y : ↥V) : ↥V :=
  ⟨(l : G) * (y : G) * (l : G)⁻¹, vmod_conj_mem m l y⟩

private theorem vmodPhi_conj {V L Z : Subgroup G} (m : VMod V L Z) (l : ↥L) (y : ↥V) :
    vmodPhi m (vmodConj m l y) =
      B5FinWedge.wedgeMat4 ((m.α l : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ vmodPhi m y :=
  m.equiv l y (vmodConj m l y) rfl

private def vmodXconj {V : Subgroup G} {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (v : ↥V) : ↥V :=
  ⟨x * (v : G) * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxV (v : G)).1 v.2⟩

private def vmodComm {V L Z : Subgroup G} (m : VMod V L Z) (l : ↥L) (v : ↥V) : ↥V :=
  v * vmodConj m l v⁻¹

private theorem vmodComm_val {V L Z : Subgroup G} (m : VMod V L Z) (l : ↥L) (v : ↥V) :
    ((vmodComm m l v : ↥V) : G) = ⁅(v : G), (l : G)⁆ := by
  rw [commutatorElement_def]
  simp [vmodComm, vmodConj, mul_assoc]

private theorem vmodPhi_comm {V L Z : Subgroup G} (m : VMod V L Z) (l : ↥L) (v : ↥V) :
    vmodPhi m (vmodComm m l v) = vmodPhi m v +
      B5FinWedge.wedgeMat4 ((m.α l : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ vmodPhi m v := by
  rw [vmodComm, vmodPhi_mul, vmodPhi_conj, vmodPhi_inv]

private theorem vmod_exists_of_g {V L Z : Subgroup G} (m : VMod V L Z) {w : Fin 6 → ZMod 2}
    {g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hg : B5FinWedge.wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 = w) :
    ∃ v : ↥V, vmodPhi m v = w := by
  obtain ⟨l, hl⟩ := m.surj g
  refine ⟨vmodConj m l (vmodZ0 m), ?_⟩
  rw [vmodPhi_conj, vmodPhi_z0, hl]
  exact hg

private theorem vmod_exists_basis {V L Z : Subgroup G} (m : VMod V L Z) (k : Fin 6) :
    ∃ v : ↥V, vmodPhi m v = Pi.single k 1 := by
  obtain ⟨g, hg⟩ := exists_g_basis k
  exact vmod_exists_of_g m hg

private theorem vmod_Z_fixed {V L Z : Subgroup G} (m : VMod V L Z) (hZV : Z ≤ V) (z : ↥Z)
    (g : L3321.SL4) (hg : g ∈ L3321.P2) :
    B5FinWedge.wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      vmodPhi m ⟨(z : G), hZV z.2⟩ = vmodPhi m ⟨(z : G), hZV z.2⟩ := by
  obtain ⟨l, hl⟩ := m.surj g
  have hlg : m.α l ∈ L3321.P2 := by
    rw [hl]
    exact hg
  have hc : (l : G) ∈ Subgroup.centralizer (Z : Set G) := m.cent l hlg
  have hcomm : (l : G) * (z : G) * (l : G)⁻¹ = (z : G) := by
    have h := Subgroup.mem_centralizer_iff.1 hc (z : G) z.2
    rw [← h, mul_inv_cancel_right]
  have key := m.equiv l ⟨(z : G), hZV z.2⟩ ⟨(z : G), hZV z.2⟩ hcomm.symm
  rw [hl] at key
  exact key.symm

theorem VMod.card_Z_eq_two {V L Z : Subgroup G} (m : VMod V L Z) (hZV : Z ≤ V) :
    Nat.card Z = 2 := by
  have hcase : ∀ z : ↥Z, z = 1 ∨ (z : G) = m.z₀ := by
    intro z
    rcases wedge_P2_fixed (vmodPhi m ⟨(z : G), hZV z.2⟩)
        (fun g hg => vmod_Z_fixed m hZV z g hg) with h | h
    · left
      have h1 : (⟨(z : G), hZV z.2⟩ : ↥V) = 1 := vmodPhi_eq_zero m h
      have h2 : (z : G) = 1 := congrArg (Subtype.val : ↥V → G) h1
      exact Subtype.ext h2
    · right
      have h1 : (⟨(z : G), hZV z.2⟩ : ↥V) = vmodZ0 m :=
        vmodPhi_eq_of_eq m (h.trans (vmodPhi_z0 m).symm)
      have h2 : (z : G) = m.z₀ := congrArg (Subtype.val : ↥V → G) h1
      exact h2
  have hne : m.z₀ ≠ 1 := by
    intro h
    have h1 : vmodZ0 m = 1 := Subtype.ext h
    have h2 := vmodPhi_z0 m
    rw [h1, vmodPhi_one] at h2
    exact (by decide : (Pi.single 0 1 : Fin 6 → ZMod 2) ≠ 0) h2.symm
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨m.z₀, m.z₀_Z⟩, fun h => hne (congrArg Subtype.val h).symm, ?_⟩
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hcase z with h | h
  · exact Or.inl h
  · exact Or.inr (Subtype.ext h)

theorem VMod.centralizes {V L Z Yb : Subgroup G} (m : VMod V L Z) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxZ : x ∈ Subgroup.centralizer (Z : Set G))
    (hxY : x ∈ Subgroup.centralizer ((⁅V, Yb⁆ : Subgroup G) : Set G))
    (hY : ∃ y₀ ∈ Yb, ∃ hy : y₀ ∈ L, m.α ⟨y₀, hy⟩ = gA) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨y₀, hy₀Yb, hy₀L, hαy⟩ := hY
  have hM : ((m.α ⟨y₀, hy₀L⟩ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = gAmat :=
    congrArg Subtype.val hαy
  have hxz0 : Commute x m.z₀ := (Subgroup.mem_centralizer_iff.1 hxZ m.z₀ m.z₀_Z).symm
  obtain ⟨E, hE⟩ : ∃ E : AddSubgroup (Fin 6 → ZMod 2),
      ∀ vec, vec ∈ E ↔ ∃ y : ↥V, vmodPhi m y = vec ∧ Commute x (y : G) :=
    ⟨{ carrier := {vec | ∃ y : ↥V, vmodPhi m y = vec ∧ Commute x (y : G)}
       add_mem' := by
         rintro _ _ ⟨y, rfl, hy⟩ ⟨y', rfl, hy'⟩
         exact ⟨y * y', vmodPhi_mul m y y', hy.mul_right hy'⟩
       zero_mem' := ⟨1, vmodPhi_one m, Commute.one_right x⟩
       neg_mem' := by
         rintro _ ⟨y, rfl, hy⟩
         exact ⟨y⁻¹, by rw [vmodPhi_inv, vmod_vec_neg], hy.inv_right⟩ }, fun _ => Iff.rfl⟩
  have hcomm : ∀ v : ↥V, Commute x ((vmodComm m ⟨y₀, hy₀L⟩ v : ↥V) : G) := by
    intro v
    rw [vmodComm_val]
    have hmem : ⁅(v : G), y₀⁆ ∈ (⁅V, Yb⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator v.2 hy₀Yb
    exact (Subgroup.mem_centralizer_iff.1 hxY _ hmem).symm
  obtain ⟨v1, hv1⟩ := vmod_exists_basis m 1
  obtain ⟨v2, hv2⟩ := vmod_exists_basis m 2
  obtain ⟨v3, hv3⟩ := vmod_exists_basis m 3
  obtain ⟨v4, hv4⟩ := vmod_exists_basis m 4
  have hc1 : vmodPhi m (vmodComm m ⟨y₀, hy₀L⟩ v1) = Pi.single 1 1 + Pi.single 3 1 := by
    rw [vmodPhi_comm, hv1, hM, wedgeMat4_gA_basis.1]
  have hc2 : vmodPhi m (vmodComm m ⟨y₀, hy₀L⟩ v2) = Pi.single 2 1 + Pi.single 4 1 := by
    rw [vmodPhi_comm, hv2, hM, wedgeMat4_gA_basis.2.2.1]
  have hc3 : vmodPhi m (vmodComm m ⟨y₀, hy₀L⟩ v3) = Pi.single 1 1 := by
    rw [vmodPhi_comm, hv3, hM, wedgeMat4_gA_basis.2.1] <;> decide +kernel
  have hc4 : vmodPhi m (vmodComm m ⟨y₀, hy₀L⟩ v4) = Pi.single 2 1 := by
    rw [vmodPhi_comm, hv4, hM, wedgeMat4_gA_basis.2.2.2] <;> decide +kernel
  have hs0 : (Pi.single 0 1 : Fin 6 → ZMod 2) ∈ E :=
    (hE _).2 ⟨vmodZ0 m, vmodPhi_z0 m, hxz0⟩
  have hs1 : (Pi.single 1 1 : Fin 6 → ZMod 2) ∈ E :=
    (hE _).2 ⟨vmodComm m ⟨y₀, hy₀L⟩ v3, hc3, hcomm v3⟩
  have hs2 : (Pi.single 2 1 : Fin 6 → ZMod 2) ∈ E :=
    (hE _).2 ⟨vmodComm m ⟨y₀, hy₀L⟩ v4, hc4, hcomm v4⟩
  have hs3 : (Pi.single 3 1 : Fin 6 → ZMod 2) ∈ E :=
    (hE _).2 ⟨vmodComm m ⟨y₀, hy₀L⟩ v1 * vmodComm m ⟨y₀, hy₀L⟩ v3,
      by rw [vmodPhi_mul, hc1, hc3] <;> decide +kernel,
      (hcomm v1).mul_right (hcomm v3)⟩
  have hs4 : (Pi.single 4 1 : Fin 6 → ZMod 2) ∈ E :=
    (hE _).2 ⟨vmodComm m ⟨y₀, hy₀L⟩ v2 * vmodComm m ⟨y₀, hy₀L⟩ v4,
      by rw [vmodPhi_mul, hc2, hc4] <;> decide +kernel,
      (hcomm v2).mul_right (hcomm v4)⟩
  have hdecomp : ∀ vec : Fin 6 → ZMod 2, vec 5 = 0 →
      vec = (if vec 0 = 0 then 0 else Pi.single 0 1) + (if vec 1 = 0 then 0 else Pi.single 1 1) +
        (if vec 2 = 0 then 0 else Pi.single 2 1) + (if vec 3 = 0 then 0 else Pi.single 3 1) +
        (if vec 4 = 0 then 0 else Pi.single 4 1) := by
    decide +kernel
  have hterm : ∀ (vec : Fin 6 → ZMod 2) (i : Fin 6),
      (Pi.single i (1 : ZMod 2) : Fin 6 → ZMod 2) ∈ E →
      (if vec i = 0 then 0 else Pi.single i 1) ∈ E := by
    intro vec i hi
    split_ifs
    · exact E.zero_mem
    · exact hi
  have hall : ∀ vec : Fin 6 → ZMod 2, vec 5 = 0 → vec ∈ E := by
    intro vec h5
    rw [hdecomp vec h5]
    exact E.add_mem (E.add_mem (E.add_mem (E.add_mem (hterm vec 0 hs0) (hterm vec 1 hs1))
      (hterm vec 2 hs2)) (hterm vec 3 hs3)) (hterm vec 4 hs4)
  have hstar : ∀ y : ↥V, vmodPhi m y 5 = 0 → Commute x (y : G) := by
    intro y hy5
    obtain ⟨y', hy', hc⟩ := (hE _).1 (hall (vmodPhi m y) hy5)
    have hyy : y' = y := vmodPhi_eq_of_eq m hy'
    rw [← hyy]
    exact hc
  choose lp hlp using fun i : Fin 5 => m.surj ⟨lamG i, lamG_det i⟩
  have hMlp : ∀ i : Fin 5, ((m.α (lp i) : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = lamG i :=
    fun i => congrArg Subtype.val (hlp i)
  have hsphi : ∀ i : Fin 5, vmodPhi m (vmodConj m (lp i) (vmodZ0 m)) = lamS i := by
    intro i
    rw [vmodPhi_conj, vmodPhi_z0, hMlp i, wedgeMat4_lamG i]
  obtain ⟨s, hs⟩ : ∃ s : Fin 5 → ↥V, ∀ i, s i = vmodConj m (lp i) (vmodZ0 m) :=
    ⟨fun i => vmodConj m (lp i) (vmodZ0 m), fun i => rfl⟩
  have hsphi' : ∀ i : Fin 5, vmodPhi m (s i) = lamS i := fun i => by
    rw [hs i]
    exact hsphi i
  have hC1 : ∀ l : ↥L, pluck (vmodPhi m (vmodXconj hxV (vmodConj m l (vmodZ0 m)))) = 0 := by
    intro l
    have hl'' : x * (l : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hxL (l : G)).1 l.2
    have hz : x * m.z₀ * x⁻¹ = m.z₀ := by
      rw [hxz0.eq, mul_inv_cancel_right]
    have heq : vmodXconj hxV (vmodConj m l (vmodZ0 m)) =
        vmodConj m ⟨x * (l : G) * x⁻¹, hl''⟩ (vmodZ0 m) := by
      apply Subtype.ext
      show x * ((l : G) * m.z₀ * (l : G)⁻¹) * x⁻¹ =
        (x * (l : G) * x⁻¹) * m.z₀ * (x * (l : G) * x⁻¹)⁻¹
      calc x * ((l : G) * m.z₀ * (l : G)⁻¹) * x⁻¹
          = (x * (l : G) * x⁻¹) * (x * m.z₀ * x⁻¹) * (x * (l : G) * x⁻¹)⁻¹ := by group
        _ = (x * (l : G) * x⁻¹) * m.z₀ * (x * (l : G) * x⁻¹)⁻¹ := by rw [hz]
    rw [heq, vmodPhi_conj, vmodPhi_z0, pluck_wedgeMat4_e0]
  have hpl : ∀ i : Fin 5, pluck (vmodPhi m (vmodXconj hxV (s i))) = 0 := fun i => by
    rw [hs i]
    exact hC1 (lp i)
  have hprod : ∀ a b : ↥V, Commute x ((a * b : ↥V) : G) →
      vmodXconj hxV a * vmodXconj hxV b = a * b := by
    intro a b hc
    apply Subtype.ext
    have hc2 : x * ((a : G) * (b : G)) = ((a : G) * (b : G)) * x := hc.eq
    show x * (a : G) * x⁻¹ * (x * (b : G) * x⁻¹) = (a : G) * (b : G)
    calc x * (a : G) * x⁻¹ * (x * (b : G) * x⁻¹) = x * ((a : G) * (b : G)) * x⁻¹ := by group
      _ = ((a : G) * (b : G)) * x * x⁻¹ := by rw [hc2]
      _ = (a : G) * (b : G) := mul_inv_cancel_right _ _
  have h5 : ∀ i : Fin 5, vmodPhi m (s i * s 0) 5 = 0 := by
    intro i
    rw [vmodPhi_mul, Pi.add_apply, hsphi' i, hsphi' 0, lamS_k1, lamS_k1] <;> decide
  have hrel : ∀ i : Fin 5, vmodPhi m (vmodXconj hxV (s i)) + vmodPhi m (vmodXconj hxV (s 0)) =
      vmodPhi m (s i) + vmodPhi m (s 0) := by
    intro i
    have hc : Commute x ((s i * s 0 : ↥V) : G) := hstar (s i * s 0) (h5 i)
    have h := congrArg (vmodPhi m) (hprod (s i) (s 0) hc)
    rwa [vmodPhi_mul, vmodPhi_mul] at h
  obtain ⟨w, hw⟩ : ∃ w : Fin 6 → ZMod 2,
      w = vmodPhi m (s 0) + vmodPhi m (vmodXconj hxV (s 0)) := ⟨_, rfl⟩
  have hform : ∀ i : Fin 5, vmodPhi m (vmodXconj hxV (s i)) = lamS i + w := by
    intro i
    have h := vmod_vec_cancel _ _ _ _ (hrel i)
    rw [hsphi' i] at h
    rw [hw]
    exact h
  have hw0 : w = 0 :=
    no_transvection w (fun i => by
      rw [← hform i]
      exact hpl i)
  have h00 : vmodPhi m (s 0) + vmodPhi m (vmodXconj hxV (s 0)) = 0 := by
    rw [← hw]
    exact hw0
  have h00' : vmodPhi m (vmodXconj hxV (s 0)) = vmodPhi m (s 0) :=
    vmod_vec_sum_zero _ _ h00
  have hxs0 : vmodXconj hxV (s 0) = s 0 := vmodPhi_eq_of_eq m h00'
  have hcs0 : Commute x (s 0 : G) := by
    have h1 : x * (s 0 : G) * x⁻¹ = (s 0 : G) := congrArg Subtype.val hxs0
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hD : ∀ v : ↥V, Commute x (v : G) := by
    intro v
    by_cases h5v : vmodPhi m v 5 = 0
    · exact hstar v h5v
    · have h1 : vmodPhi m v 5 = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ h5v
      have h2 : vmodPhi m (v * s 0) 5 = 0 := by
        rw [vmodPhi_mul, Pi.add_apply, h1, hsphi' 0, lamS_k1] <;> decide
      have hc : Commute x ((v * s 0 : ↥V) : G) := hstar (v * s 0) h2
      have h3 : Commute x ((v : G) * (s 0 : G) * (s 0 : G)⁻¹) := hc.mul_right hcs0.inv_right
      rwa [mul_inv_cancel_right] at h3
  exact Subgroup.mem_centralizer_iff.2 fun g hg => (hD ⟨g, hg⟩).eq.symm

end CFSG.Quasithin.H13.NFa2
