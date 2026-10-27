module

public import CFSG.Monster.GMS.S365Leech
public import CFSG.Monster.GMS.Facts.Section37
public import CFSG.Monster.GMS.Leech.OddLift
import CFSG.Assembly.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def U6OddFact : Prop :=
  ∀ u₁ u₂ : Fin 24 → ZMod 2, u₁ ∈ co1Orbit 0 → u₂ ∈ co1Orbit 0 → u₁ + u₂ ∈ co1Orbit 0 →
    ∀ M : Subgroup Co1, M ≤ co1Stab u₁ ⊓ co1Stab u₂ → Odd (Nat.card M) → Nat.card M < 3000

namespace U6Odd

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem commute_of_mem_cosetSet {x y t s m : G} (hs : s ∈ S365.cosetSet x y t)
    (hmx : m * x = x * m) (hmy : m * y = y * m) (hmt : m * t = t * m) : m * s = s * m := by
  obtain ⟨c, hc, rfl⟩ := S365.mem_cosetSet_iff.1 hs
  have cx : Commute m x := hmx
  have cy : Commute m y := hmy
  have ct : Commute m t := hmt
  have hcc : Commute m c := by
    rcases hc with rfl | rfl | rfl | rfl
    · exact Commute.one_right m
    · exact cx
    · exact cy
    · exact cx.mul_right cy
  exact (ct.mul_right hcc).eq

theorem line_mem_leechQ
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x y t w : G}
    (hl : IsLineTriple a x y) (hw : IsConj z₀ w) (hwc : w ∈ S365.cosetSet x y t)
    (hxw : x * w = w * x) (hyw : y * w = w * y) (hcount : twoBCount z₀ x y t = 1) :
    x ∈ leechQ w ∧ y ∈ leechQ w ∧ x * y ∈ leechQ w := by
  classical
  have hK := S365.isKlein_of_isLineTriple hG.1.1 hl
  have hcnt : twoBCount z₀ x y w = 1 := by
    rw [S365.twoBCount_eq_of_mem_cosetSet hK hwc]
    exact hcount
  have hexp := S365.twoBCount_eq_of_twoB I hG hl hw hxw hyw
  rw [hcnt] at hexp
  by_cases hx : x ∈ leechQ w <;> by_cases hy : y ∈ leechQ w <;>
    by_cases hxy : x * y ∈ leechQ w <;> simp [hx, hy, hxy] at hexp ⊢

theorem eightOneOddOrder_of_co1
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (h : U6OddFact) : EightOneOddOrder a z₀ := by
  intro x y t hl he hcount M hM hodd
  obtain ⟨w, hw, hwc⟩ := S365.exists_twoB_mem_cosetSet I hG hl he
  have hK := S365.isKlein_of_isLineTriple hG.1.1 hl
  obtain ⟨hwx, hwy⟩ := S365.commute_of_mem_cosetSet hK.comm he.2.1 he.2.2.1 hwc
  obtain ⟨hxQ, hyQ, hxyQ⟩ := line_mem_leechQ I hG hl hw hwc hwx.symm hwy.symm hcount
  obtain ⟨L⟩ := S365.exists_leechSystem_of_isConj hG hw
  have hMx : ∀ m ∈ M, m * x = x * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.1 (hM hm).1.1
  have hMy : ∀ m ∈ M, m * y = y * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.1 (hM hm).1.2
  have hMt : ∀ m ∈ M, m * t = t * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.1 (hM hm).2
  have hMw : ∀ m ∈ M, m * w = w * m := fun m hm =>
    commute_of_mem_cosetSet hwc (hMx m hm) (hMy m hm) (hMt m hm)
  have hMle : M ≤ Subgroup.centralizer ({w} : Set G) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.2 (hMw m hm)
  let ψ : M →* Co1 := L.φ.comp (Subgroup.inclusion hMle)
  have hψ : ∀ m : M, ψ m = L.φ ⟨(m : G), hMle m.2⟩ := fun m => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    rw [hψ] at hm
    have hmQ : (m : G) ∈ leechQ w := (L.φ_ker ⟨(m : G), hMle m.2⟩).1 hm
    have hord : Odd (orderOf (m : G)) := by
      rw [Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hodd (orderOf_dvd_natCard m)
    exact Subtype.ext (L.eq_one_of_odd_orderOf hmQ hord)
  have hcard : Nat.card ψ.range = Nat.card M :=
    Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv
  have hfix : ∀ (z : G), z ∈ leechQ w → (∀ m ∈ M, m * z = z * m) →
      ∀ n ∈ ψ.range, co1Act n (L.vec z) = L.vec z := by
    intro z hz hcomm n hn
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 hn
    rw [hψ, ← L.vec_conj ⟨(m : G), hMle m.2⟩ z hz]
    congr 1
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm m m.2
  have hx0 := S365.mem_typeSet_zero_of_isConj I hG hw L hxQ hl.1
  have hy0 := S365.mem_typeSet_zero_of_isConj I hG hw L hyQ hl.2.1
  have hxy0 := S365.mem_typeSet_zero_of_isConj I hG hw L hxyQ hl.2.2
  rw [L.mem_typeSet, L.vec_mul x hxQ y hyQ] at hxy0
  have hN : ψ.range ≤ co1Stab (L.vec x) ⊓ co1Stab (L.vec y) := fun n hn =>
    ⟨hfix x hxQ hMx n hn, hfix y hyQ hMy n hn⟩
  rw [← hcard] at hodd ⊢
  exact h _ _ hx0.2 (S365.mem_typeSet_zero_of_isConj I hG hw L hyQ hl.2.1).2 hxy0.2 _ hN hodd

end U6Odd

end CFSG.Monster.GMS
