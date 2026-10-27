module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6S

public section

namespace CFSG.Quasithin.H13
namespace N1246
open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem index_subgroupOf_eq_of_forall {X L H : Subgroup G} (hLX : L ≤ X)
    (hX : ∀ x ∈ X, ∃ l ∈ L, l⁻¹ * x ∈ H) :
    (H.subgroupOf L).index = (H.subgroupOf X).index := by
  unfold Subgroup.index
  let f : (↥L ⧸ H.subgroupOf L) → (↥X ⧸ H.subgroupOf X) :=
    Quotient.map' (fun a : ↥L => (Subgroup.inclusion hLX a : ↥X)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [Subgroup.mem_subgroupOf] at hab ⊢
      simpa using hab)
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn' with
    | h a =>
      induction q₂ using Quotient.inductionOn' with
      | h b =>
        have h' : ((Subgroup.inclusion hLX a : ↥X) : ↥X ⧸ H.subgroupOf X) =
            (Subgroup.inclusion hLX b : ↥X) := h
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
        apply QuotientGroup.eq.2
        rw [Subgroup.mem_subgroupOf]
        simpa using h'
  · intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      obtain ⟨l, hlL, hl⟩ := hX (x : G) x.2
      refine ⟨((⟨l, hlL⟩ : ↥L) : ↥L ⧸ H.subgroupOf L), ?_⟩
      show ((Subgroup.inclusion hLX ⟨l, hlL⟩ : ↥X) : ↥X ⧸ H.subgroupOf X) =
        (x : ↥X ⧸ H.subgroupOf X)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hl

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

private theorem comm_z_of_mem_L {h : G} (hL : h ∈ L) : h * z = z * h :=
  Subgroup.mem_centralizer_iff.1 c.f.mem_zV.2 h hL

private theorem exists_inv_mul_mem_Hp {x : G} (hx : x ∈ L ⊔ T) :
    ∃ l ∈ L, l⁻¹ * x ∈ c.Hp := by
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := c.LT_le_NV hx
  have ha : conjAct V ⟨x, hxN⟩ ∈ autOn L V :=
    c.autOn_sup_le (CFSG.Quasithin.AutOn.conjAct_mem_autOn_of_mem hxN hx)
  obtain ⟨l, hlL, hlN, hl⟩ := exists_of_mem_autOn ha
  have hcent : l⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    have h1 : l * u * l⁻¹ = x * u * x⁻¹ := by
      have h2 := congrArg (fun φ : MulAut V => ((φ ⟨u, hu⟩ : ↥V) : G)) hl
      simp only [CFSG.Quasithin.AutOn.coe_conjAct_apply] at h2
      exact h2
    calc u * (l⁻¹ * x) = l⁻¹ * (l * u * l⁻¹) * x := by group
      _ = l⁻¹ * (x * u * x⁻¹) * x := by rw [h1]
      _ = l⁻¹ * x * u := by group
  have hcentE : l⁻¹ * x ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le c.EV hcent)
  refine ⟨l, hlL, Subgroup.mem_inf.2 ⟨?_, hcentE⟩⟩
  exact (L ⊔ T).mul_mem ((L ⊔ T).inv_mem ((le_sup_left : L ≤ L ⊔ T) hlL)) hx

private theorem mem_centralizer_E_of_comm {g : G} (hgv : g * v = v * g) (hgz : g * z = z * g) :
    g ∈ Subgroup.centralizer (E : Set G) := by
  refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
  rcases c.mem_E he with h1 | h1 | h1 | h1 <;> rw [h1]
  · simp
  · exact hgz.symm
  · exact hgv.symm
  · calc v * z * g = v * (z * g) := by group
      _ = v * (g * z) := by rw [hgz]
      _ = (v * g) * z := by group
      _ = (g * v) * z := by rw [← hgv]
      _ = g * (v * z) := by group

private theorem conj_v_mem {h : G} (hL : h ∈ L) (hN : h ∈ Subgroup.normalizer (E : Set G)) :
    h * v * h⁻¹ = v ∨ h * v * h⁻¹ = v * z := by
  have hzh : h⁻¹ * z * h = z := by
    rw [mul_assoc, ← c.comm_z_of_mem_L hL, ← mul_assoc, inv_mul_cancel, one_mul]
  have hvE : h * v * h⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hN v).1 c.vE
  rcases c.mem_E hvE with h1 | h1 | h1 | h1
  · exfalso
    apply c.v_ne_one
    calc v = h⁻¹ * (h * v * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  · exfalso
    apply c.v_ne_z
    calc v = h⁻¹ * (h * v * h⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [h1]
      _ = z := hzh
  · exact Or.inl h1
  · exact Or.inr h1

private theorem conj_v_eq_of_not_mem {x : G} (hxL : x ∈ L)
    (hxN : x ∈ Subgroup.normalizer (E : Set G)) (hx' : x ∉ L ⊓ Subgroup.centralizer (E : Set G)) :
    x * v * x⁻¹ = v * z := by
  rcases c.conj_v_mem hxL hxN with h | h
  · exfalso
    apply hx'
    refine ⟨hxL, c.mem_centralizer_E_of_comm ?_ (c.comm_z_of_mem_L hxL)⟩
    calc x * v = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [h]
  · exact h

theorem NE_mul_mem_CE {x y : G} (hx : x ∈ L ⊓ Subgroup.normalizer (E : Set G))
    (hy : y ∈ L ⊓ Subgroup.normalizer (E : Set G)) (hx' : x ∉ L ⊓ Subgroup.centralizer (E : Set G))
    (hy' : y ∉ L ⊓ Subgroup.centralizer (E : Set G)) :
    x * y ∈ L ⊓ Subgroup.centralizer (E : Set G) := by
  have hxv := c.conj_v_eq_of_not_mem hx.1 hx.2 hx'
  have hyv := c.conj_v_eq_of_not_mem hy.1 hy.2 hy'
  have hxz : x * z * x⁻¹ = z := by
    rw [c.comm_z_of_mem_L hx.1, mul_inv_cancel_right]
  have hxyL : x * y ∈ L := L.mul_mem hx.1 hy.1
  have hxyz : x * y * z = z * (x * y) := c.comm_z_of_mem_L hxyL
  have hconj : x * y * v * (x * y)⁻¹ = v := by
    calc x * y * v * (x * y)⁻¹ = x * (y * v * y⁻¹) * x⁻¹ := by group
      _ = x * (v * z) * x⁻¹ := by rw [hyv]
      _ = (x * v * x⁻¹) * (x * z * x⁻¹) := by group
      _ = v * z * z := by rw [hxv, hxz]
      _ = v := by rw [mul_assoc, c.z_sq, mul_one]
  have hgv : x * y * v = v * (x * y) := by
    calc x * y * v = (x * y * v * (x * y)⁻¹) * (x * y) := by group
      _ = v * (x * y) := by rw [hconj]
  exact ⟨hxyL, c.mem_centralizer_E_of_comm hgv hxyz⟩

theorem NE_index_odd : ¬ 2 ∣ ((L ⊓ Subgroup.normalizer (E : Set G)).subgroupOf L).index := by
  have hA : (L ⊓ Subgroup.normalizer (E : Set G)).subgroupOf L = c.Hp.subgroupOf L := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨(le_sup_left : L ≤ L ⊔ T) h.1, h.2⟩
    · intro h
      exact ⟨x.2, h.2⟩
  rw [hA, index_subgroupOf_eq_of_forall (le_sup_left : L ≤ L ⊔ T)
    (fun x hx => c.exists_inv_mul_mem_Hp hx)]
  exact c.Hp_odd

end Ctx

end N1246

end CFSG.Quasithin.H13

end
