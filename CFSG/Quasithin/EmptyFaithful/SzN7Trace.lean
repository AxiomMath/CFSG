module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

open scoped BigOperators

section Trace

variable {G : Type} [Group G] [Finite G]

theorem szN7_trace {L Rl W : Subgroup G} {v : G}
    (hodd : ¬ 2 ∣ (Rl.subgroupOf L).index) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hLW : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) (hv : v ∈ W) (hv2 : v ^ 2 = 1)
    (hvR : ∀ r ∈ Rl, r * v * r⁻¹ = v) :
    ∃ c ∈ W, (∀ l ∈ L, l * c * l⁻¹ = c) ∧
      ∀ P : Subgroup G, (∀ l ∈ L, v * (l * v * l⁻¹)⁻¹ ∈ P) → v * c⁻¹ ∈ P := by
  classical
  let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with
    mul_comm := fun a b => Subtype.ext (hWc a.1 a.2 b.1 b.2) }
  let H : Subgroup ↥L := Rl.subgroupOf L
  let _ : Fintype (↥L ⧸ H) := Fintype.ofFinite _
  let f : (↥L ⧸ H) → ↥W := fun q =>
    ⟨(q.out : G) * v * (q.out : G)⁻¹, hLW _ q.out.2 v hv⟩
  let φ : ∀ l ∈ L, ↥W →* ↥W := fun l hl =>
    { toFun := fun w => ⟨l * (w : G) * l⁻¹, hLW l hl w w.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : ∀ (l : ↥L) (q : ↥L ⧸ H), φ l l.2 (f q) = f (l • q) := by
    intro l q
    refine Subtype.ext ?_
    have hq : (((l • q).out)⁻¹ * (l * q.out) : ↥L) ∈ H := by
      have h1 : ((l • q) : ↥L ⧸ H) = ((l * q.out : ↥L) : ↥L ⧸ H) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h2 := QuotientGroup.eq.mp (by rw [← h1]; exact (QuotientGroup.out_eq' _) :
        (((l • q).out : ↥L) : ↥L ⧸ H) = ((l * q.out : ↥L) : ↥L ⧸ H))
      exact h2
    have hr : (((l • q).out : ↥L)⁻¹ * (l * q.out) : ↥L).1 ∈ Rl := Subgroup.mem_subgroupOf.mp hq
    have hrv := hvR _ hr
    show (l : G) * ((q.out : G) * v * (q.out : G)⁻¹) * (l : G)⁻¹ =
      ((l • q).out : G) * v * ((l • q).out : G)⁻¹
    have e : (l : G) * (q.out : G) = ((l • q).out : G) * ((((l • q).out : ↥L)⁻¹ * (l * q.out) : ↥L) : G) := by
      simp
    calc (l : G) * ((q.out : G) * v * (q.out : G)⁻¹) * (l : G)⁻¹
        = ((l : G) * (q.out : G)) * v * ((l : G) * (q.out : G))⁻¹ := by group
      _ = (((l • q).out : G) * ((((l • q).out : ↥L)⁻¹ * (l * q.out) : ↥L) : G)) * v *
            (((l • q).out : G) * ((((l • q).out : ↥L)⁻¹ * (l * q.out) : ↥L) : G))⁻¹ := by rw [e]
      _ = ((l • q).out : G) * (((((l • q).out : ↥L)⁻¹ * (l * q.out) : ↥L) : G) * v *
            ((((l • q).out : ↥L)⁻¹ * (l * q.out) : ↥L) : G)⁻¹) * ((l • q).out : G)⁻¹ := by group
      _ = ((l • q).out : G) * v * ((l • q).out : G)⁻¹ := by rw [hrv]
  let c' : ↥W := ∏ q, f q
  refine ⟨(c' : G), c'.2, ?_, ?_⟩
  · intro l hl
    have h1 : φ l hl c' = c' := by
      have e1 : φ l hl c' = ∏ q, φ l hl (f q) := map_prod (φ l hl) f Finset.univ
      have e2 : ∏ q, φ l hl (f q) = ∏ q, f ((⟨l, hl⟩ : ↥L) • q) :=
        Finset.prod_congr rfl fun q _ => hφ ⟨l, hl⟩ q
      have e3 : ∏ q, f ((⟨l, hl⟩ : ↥L) • q) = ∏ q, f q :=
        Equiv.prod_comp (MulAction.toPerm (⟨l, hl⟩ : ↥L)) f
      rw [e1, e2, e3]
    have h2 := congrArg Subtype.val h1
    exact h2
  · intro P hP
    have hk : Odd (Nat.card (↥L ⧸ H)) := by
      have : Nat.card (↥L ⧸ H) = H.index := (Subgroup.index_eq_card H).symm
      rw [this]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    obtain ⟨m, hm⟩ := hk
    let v' : ↥W := ⟨v, hv⟩
    have hv'2 : v' ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    have hv'k : v' ^ Fintype.card (↥L ⧸ H) = v' := by
      have : Fintype.card (↥L ⧸ H) = Nat.card (↥L ⧸ H) := (Nat.card_eq_fintype_card).symm
      rw [this, hm, pow_succ, pow_mul, hv'2, one_pow, one_mul]
    have hprod : v' * c'⁻¹ = ∏ q : ↥L ⧸ H, (v' * (f q)⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hv'k, Finset.prod_inv_distrib]
    have hmem : v' * c'⁻¹ ∈ P.subgroupOf W := by
      rw [hprod]
      refine Subgroup.prod_mem _ fun q _ => ?_
      rw [Subgroup.mem_subgroupOf]
      have := hP (q.out : G) q.out.2
      simpa [f, v'] using this
    exact Subgroup.mem_subgroupOf.mp hmem

end Trace

end CFSG.Quasithin
