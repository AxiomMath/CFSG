module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin10
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin4

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem mem_sylow_std_iff_comm (x : Perm (Fin 5)) : x ∈ S5Syl ↔ x * zStd = zStd * x := by
  have h : ∀ x : Perm (Fin 5), x ∈ S5SylF ↔ x * zStd = zStd * x := by
    unfold zStd; decide +kernel
  rw [mem_S5Syl_iff]; exact h x

theorem mem_sylow_iff_comm {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) (x : Perm (Fin 5)) : x ∈ D ↔ x * z = z * x := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hz' := isCentInv_cj_std_iff.mp hz
  rw [mem_cj, mem_sylow_std_iff_comm, hz']
  constructor
  · intro h
    calc x * (g * zStd * g⁻¹) = g * ((g⁻¹ * x * g) * zStd) * g⁻¹ := by group
      _ = g * (zStd * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = (g * zStd * g⁻¹) * x := by group
  · intro h
    calc (g⁻¹ * x * g) * zStd = g⁻¹ * (x * (g * zStd * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * zStd * g⁻¹) * x) * g := by rw [h]
      _ = zStd * (g⁻¹ * x * g) := by group

theorem isDoubleSwap_zStd' : IsDoubleSwap zStd := by
  unfold IsDoubleSwap zStd
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem isDoubleSwap_conj' {x : Perm (Fin 5)} (hx : IsDoubleSwap x) (g : Perm (Fin 5)) :
    IsDoubleSwap (g * x * g⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · intro h; apply h1
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]; group
  · rw [conj_pow, h2]; group
  · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm, ← mul_assoc, Int.units_mul_self,
      one_mul, h3]

theorem IsCentInv.isDoubleSwap {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) : IsDoubleSwap z := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [isCentInv_cj_std_iff.mp hz]
  exact isDoubleSwap_conj' isDoubleSwap_zStd' g

theorem exists_decomp_of_centInv {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) :
    ∃ a b c d p : Fin 5, [a, b, c, d, p].Nodup ∧ z = swap a b * swap c d :=
  exists_swap_mul_swap (hz.isDoubleSwap hD)

theorem isFixPt_of_decomp {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
    (hdec : z = swap a b * swap c d) : IsFixPt D p := by
  have key : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup → ∀ x : Perm (Fin 5),
      x * (swap a b * swap c d) = (swap a b * swap c d) * x → x p = p := by
    decide +kernel
  intro x hx
  subst hdec
  exact key a b c d p h x ((mem_sylow_iff_comm hD hz x).mp hx)

theorem That_set_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
    (hdec : z = swap a b * swap c d) :
    {g | g ∈ D ∧ g.IsSwap} = ({swap a b, swap c d} : Set (Perm (Fin 5))) := by
  have key : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup → ∀ g : Perm (Fin 5),
      (g * (swap a b * swap c d) = (swap a b * swap c d) * g ∧
        (g ≠ 1 ∧ g ^ 2 = 1 ∧ Perm.sign g ≠ 1)) ↔ (g = swap a b ∨ g = swap c d) := by
    decide +kernel
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [mem_sylow_iff_comm hD hz, isSwap_iff, hdec]
  exact key a b c d p h g

theorem That_eq_closure {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
    (hdec : z = swap a b * swap c d) :
    That D = Subgroup.closure ({swap a b, swap c d} : Set (Perm (Fin 5))) := by
  unfold That
  rw [That_set_eq hD hz h hdec]

theorem mem_That_iff {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
    (hdec : z = swap a b * swap c d) (x : Perm (Fin 5)) :
    x ∈ That D ↔ x = 1 ∨ x = swap a b ∨ x = swap c d ∨ x = z := by
  have hsq : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup →
      swap a b * swap a b = 1 ∧ swap c d * swap c d = 1 ∧
      swap a b * swap c d = swap c d * swap a b := by decide +kernel
  obtain ⟨h1, h2, h3⟩ := hsq a b c d p h
  rw [That_eq_closure hD hz h hdec, mem_closure_pair h1 h2 h3, kl, hdec]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem act_ep_of_mem {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
    (hdec : z = swap a b * swap c d) {x : Perm (Fin 5)} (hx : x ∈ D) :
    (orth.act x (ep a b) = ep a b ∧ orth.act x (ep c d) = ep c d) ∨
    (orth.act x (ep a b) = ep c d ∧ orth.act x (ep c d) = ep a b) := by
  have key : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup → ∀ x : Perm (Fin 5),
      x * (swap a b * swap c d) = (swap a b * swap c d) * x →
      (orth.act x (ep a b) = ep a b ∧ orth.act x (ep c d) = ep c d) ∨
      (orth.act x (ep a b) = ep c d ∧ orth.act x (ep c d) = ep a b) := by
    decide +kernel
  subst hdec
  exact key a b c d p h x ((mem_sylow_iff_comm hD hz x).mp hx)

theorem mem_That_iff_act {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
    (hdec : z = swap a b * swap c d) {x : Perm (Fin 5)} (hx : x ∈ D) :
    x ∈ That D ↔ orth.act x (ep a b) = ep a b := by
  have key : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup → ∀ x : Perm (Fin 5),
      x * (swap a b * swap c d) = (swap a b * swap c d) * x →
      ((x = 1 ∨ x = swap a b ∨ x = swap c d ∨ x = swap a b * swap c d) ↔
        orth.act x (ep a b) = ep a b) := by
    decide +kernel
  rw [mem_That_iff hD hz h hdec]
  subst hdec
  exact key a b c d p h x ((mem_sylow_iff_comm hD hz x).mp hx)

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
