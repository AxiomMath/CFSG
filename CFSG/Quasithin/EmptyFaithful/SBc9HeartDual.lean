module

public import CFSG.Quasithin.EmptyFaithful.SBc9Heart

public section

namespace CFSG.Quasithin

namespace SBc9

open CFSG.QuasithinUnique

private theorem exists_hom_zmodTwo {A : Type} [AddGroup A] (hc : ∀ a b : A, a + b = b + a)
    (hA : ∀ a : A, a + a = 0) (B : AddSubgroup A) {z : A} (hz : z ∉ B) :
    ∃ g : A →+ ZMod 2, (∀ b ∈ B, g b = 0) ∧ g z ≠ 0 := by
  let _ : AddCommGroup A := { ‹AddGroup A› with add_comm := hc }
  let _ : Module (ZMod 2) (A ⧸ B) :=
    QuotientAddGroup.zmodModule (n := 2) (H := B) (fun x => by rw [two_nsmul, hA]; exact B.zero_mem)
  have hz' : (QuotientAddGroup.mk z : A ⧸ B) ≠ 0 := fun h =>
    hz ((QuotientAddGroup.eq_zero_iff z).1 h)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hz'
  refine ⟨φ.toAddMonoidHom.comp (QuotientAddGroup.mk' B), fun b hb => ?_, hφ⟩
  simp [(QuotientAddGroup.eq_zero_iff b).2 hb]

private theorem evenWeight_add_comm (a b : ↥(evenWeight 6)) : a + b = b + a :=
  Subtype.ext (add_comm a.1 b.1)

private theorem evenWeight_add_self (a : ↥(evenWeight 6)) : a + a = 0 := by
  apply Subtype.ext
  funext i
  have h : ∀ t : ZMod 2, t + t = 0 := by decide
  exact h (a.1 i)

private theorem mem_evenWeight_six {x : Fin 6 → ZMod 2} : x ∈ evenWeight 6 ↔ ∑ i, x i = 0 :=
  Iff.rfl

private def pairVec (i j : Fin 6) : ↥(evenWeight 6) :=
  ⟨fun l => (if l = i then 1 else 0) + (if l = j then 1 else 0), by
    rw [mem_evenWeight_six, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    decide⟩

private theorem pairVec_apply (i j l : Fin 6) :
    (pairVec i j).1 l = (if l = i then 1 else 0) + (if l = j then 1 else 0) := rfl

private def oneVec : ↥(evenWeight 6) :=
  ⟨fun _ => 1, by rw [mem_evenWeight_six]; decide⟩

private theorem oneVec_mem_constWeight : oneVec ∈ constWeight 6 := fun _ _ => rfl

private theorem eq_sum_pairVec (x : ↥(evenWeight 6)) :
    x = ∑ i : Fin 6, (x.1 i).val • pairVec i 5 := by
  apply Subtype.ext
  funext j
  have hx : ∑ i, x.1 i = 0 := mem_evenWeight_six.1 x.2
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  have h3 : ∀ i : Fin 6, ((x.1 i).val • pairVec i 5).1 j =
      x.1 i * ((if j = i then 1 else 0) + (if j = 5 then 1 else 0)) := by
    intro i
    show (x.1 i).val • ((if j = i then (1 : ZMod 2) else 0) + (if j = 5 then 1 else 0)) = _
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [Finset.sum_congr rfl (fun i _ => h3 i)]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hx, zero_mul, add_zero]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem exists_dot_of_hom (g : ↥(evenWeight 6) →+ ZMod 2) :
    ∃ c : Fin 6 → ZMod 2, ∀ x : ↥(evenWeight 6), g x = ∑ i, c i * x.1 i := by
  refine ⟨fun i => g (pairVec i 5), fun x => ?_⟩
  calc g x = g (∑ i : Fin 6, (x.1 i).val • pairVec i 5) := congrArg g (eq_sum_pairVec x)
    _ = ∑ i, (fun i => g (pairVec i 5)) i * x.1 i := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

private theorem forall_dot_eq_zero_iff (w : Fin 6 → ZMod 2) :
    (∀ x : ↥(evenWeight 6), ∑ i, w i * x.1 i = 0) ↔ ∀ i j, w i = w j := by
  constructor
  · intro h i j
    have h1 := h (pairVec i j)
    simp only [pairVec_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h2 _ _ h1
  · intro h x
    have hx : ∑ i, x.1 i = 0 := mem_evenWeight_six.1 x.2
    calc ∑ i, w i * x.1 i = ∑ i, w 0 * x.1 i := Finset.sum_congr rfl fun i _ => by rw [h i 0]
      _ = w 0 * ∑ i, x.1 i := (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hx, mul_zero]

private theorem const_of_dot_perm (c : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6))
    (hx : ∀ x : ↥(evenWeight 6), ∑ i, c i * x.1 (σ i) = ∑ i, c i * x.1 i) :
    ∀ i j, c (σ.symm i) - c i = c (σ.symm j) - c j := by
  refine (forall_dot_eq_zero_iff fun j => c (σ.symm j) - c j).1 fun x => ?_
  have h5 := Equiv.sum_comp σ (fun j => c (σ.symm j) * x.1 j)
  simp only [Equiv.symm_apply_apply] at h5
  calc ∑ j, (c (σ.symm j) - c j) * x.1 j
      = ∑ j, (c (σ.symm j) * x.1 j - c j * x.1 j) := Finset.sum_congr rfl fun j _ => sub_mul _ _ _
    _ = ∑ j, c (σ.symm j) * x.1 j - ∑ j, c j * x.1 j := Finset.sum_sub_distrib _ _
    _ = 0 := sub_eq_zero.2 (h5.symm.trans (hx x))

theorem heart_eq_top_of_commutators {Y : Subgroup (alternatingGroup (Fin 6))}
    (hY : ∀ u : AltHeart 6, (∀ y ∈ Y, heartAct (y : Equiv.Perm (Fin 6)) u = u) → u = 0)
    (H : AddSubgroup (AltHeart 6))
    (hH : ∀ y ∈ Y, ∀ u : AltHeart 6, heartAct (y : Equiv.Perm (Fin 6)) u - u ∈ H) : H = ⊤ := by
  by_contra hne
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : AltHeart 6, u₀ ∉ H := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun u _ => h u)
  obtain ⟨x₀, rfl⟩ := QuotientAddGroup.mk_surjective u₀
  let Ht : AddSubgroup ↥(evenWeight 6) := H.comap (QuotientAddGroup.mk' (constWeight 6))
  have hmem : ∀ x : ↥(evenWeight 6), x ∈ Ht ↔ (QuotientAddGroup.mk x : AltHeart 6) ∈ H :=
    fun _ => Iff.rfl
  obtain ⟨g, hgH, hgx₀⟩ :=
    exists_hom_zmodTwo (A := ↥(evenWeight 6)) evenWeight_add_comm evenWeight_add_self Ht
      ((hmem x₀).not.2 hu₀)
  obtain ⟨c, hc⟩ := exists_dot_of_hom g
  have hone : ∑ i, c i = 0 := by
    have h0 : g oneVec = 0 := hgH oneVec (by
      rw [hmem, (QuotientAddGroup.eq_zero_iff oneVec).2 oneVec_mem_constWeight]
      exact H.zero_mem)
    rw [hc] at h0
    have h1 : ∀ i, oneVec.1 i = 1 := fun _ => rfl
    simpa only [h1, mul_one] using h0
  let c' : ↥(evenWeight 6) := ⟨c, mem_evenWeight_six.2 hone⟩
  have hfix : ∀ y ∈ Y, heartAct (y : Equiv.Perm (Fin 6)) (QuotientAddGroup.mk c' : AltHeart 6) =
      QuotientAddGroup.mk c' := by
    intro y hy
    have hy' : y⁻¹ ∈ Y := Y.inv_mem hy
    have hx : ∀ x : ↥(evenWeight 6), ∑ i, c i * x.1 ((y : Equiv.Perm (Fin 6)) i) =
        ∑ i, c i * x.1 i := by
      intro x
      have h1 := hH y⁻¹ hy' (QuotientAddGroup.mk x)
      have h2 : permWeight 6 ((y⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) x - x ∈
          Ht := by
        rw [hmem, QuotientAddGroup.mk_sub, ← heartAct_mk]
        exact h1
      have h4 := sub_eq_zero.1 ((map_sub g _ _).symm.trans (hgH _ h2))
      rw [hc, hc] at h4
      exact h4
    show (QuotientAddGroup.mk (permWeight 6 (y : Equiv.Perm (Fin 6)) c') : AltHeart 6) =
      QuotientAddGroup.mk c'
    rw [QuotientAddGroup.eq_iff_sub_mem]
    exact const_of_dot_perm c (y : Equiv.Perm (Fin 6)) hx
  have hu0 := hY (QuotientAddGroup.mk c') hfix
  have hconst : c' ∈ constWeight 6 := (QuotientAddGroup.eq_zero_iff c').1 hu0
  apply hgx₀
  rw [hc]
  exact (forall_dot_eq_zero_iff c).2 hconst x₀

end SBc9

end CFSG.Quasithin
