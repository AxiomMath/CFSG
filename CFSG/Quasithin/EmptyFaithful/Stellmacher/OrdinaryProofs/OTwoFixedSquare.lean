module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.A4Defs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Quasithin

variable {G : Type} [Group G]

theorem comm_of_mem_isElemAbelian {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) {x y : G}
    (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hV hx hy

theorem inf_centralizer_ne_bot_of_oTwoRes [Finite G] {X V : Subgroup G}
    (_hVX : V ≤ X) (hV : IsPGroup 2 V) (hn : X ≤ Subgroup.normalizer (V : Set G))
    (h : V ⊓ Subgroup.centralizer (oTwoRes X : Set G) ≠ ⊥) :
    V ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
  have hbotP : IsPGroup 2 (⊥ : Subgroup G) := fun g =>
    ⟨0, Subtype.ext (by simp [Subgroup.mem_bot.mp g.2])⟩
  obtain ⟨S, hS, -⟩ := CFSG.Quasithin.A4.exists_isSylowTwoOf_ge (H := X) bot_le hbotP
  have hX : X ≤ oTwoRes X ⊔ S := le_oTwoRes_sup_of_isSylowTwoOf hS
  obtain ⟨hSX, hSp, -⟩ := hS
  set K : Subgroup G := V ⊓ Subgroup.centralizer (oTwoRes X : Set G) with hKdef
  have hKV : K ≤ V := inf_le_left
  have hKp : IsPGroup 2 K := hV.to_le hKV
  have fwd : ∀ y ∈ X, ∀ m ∈ K, y * m * y⁻¹ ∈ K := by
    intro y hy m hm
    have hmV : m ∈ V := (Subgroup.mem_inf.mp hm).1
    have hmC : m ∈ Subgroup.centralizer (oTwoRes X : Set G) := (Subgroup.mem_inf.mp hm).2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hn hy) m).mp hmV
    · rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have ho' : y⁻¹ * o * y ∈ oTwoRes X := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes X (inv_mem hy)) o).mp ho
        simpa using this
      have key : (y⁻¹ * o * y) * m = m * (y⁻¹ * o * y) :=
        Subgroup.mem_centralizer_iff.mp hmC _ ho'
      calc o * (y * m * y⁻¹) = y * ((y⁻¹ * o * y) * m) * y⁻¹ := by group
        _ = y * (m * (y⁻¹ * o * y)) * y⁻¹ := by rw [key]
        _ = (y * m * y⁻¹) * o := by group
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fwd x hx n, fun hn' => ?_⟩
    have := fwd x⁻¹ (inv_mem hx) _ hn'
    rwa [inv_inv, show x⁻¹ * (x * n * x⁻¹) * x = n by group] at this
  have hSn : S ≤ Subgroup.normalizer (K : Set G) := hSX.trans hXK
  have hQp : IsPGroup 2 (K ⊔ S : Subgroup G) := hKp.to_sup_of_normal_left' hSp hSn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (K ⊔ S : Subgroup G) := hQp.isNilpotent
  have : (K.subgroupOf (K ⊔ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hSn
  have hne : K.subgroupOf (K ⊔ S) ≠ ⊥ := by
    intro hb
    have hd := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
    rw [inf_eq_left.mpr le_sup_left] at hd
    exact h hd
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hzK, hzc⟩ := Subgroup.mem_inf.mp hzmem
  have hzK' : (z : G) ∈ K := Subgroup.mem_subgroupOf.mp hzK
  have hwC : ∀ q : (K ⊔ S : Subgroup G), q * z = z * q := Subgroup.mem_center_iff.mp hzc
  have hw1 : (z : G) ≠ 1 := fun e => hz1 (Subtype.ext (Subtype.ext e))
  have hwV : (z : G) ∈ V := (Subgroup.mem_inf.mp hzK').1
  have hwOC : ∀ g ∈ oTwoRes X, g * (z : G) = (z : G) * g := fun g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzK').2 g hg
  have hSw : ∀ s ∈ S, s * (z : G) = (z : G) * s := by
    intro s hs
    have hsKS : s ∈ K ⊔ S := (le_sup_right : S ≤ K ⊔ S) hs
    have := hwC ⟨s, hsKS⟩
    simpa using congrArg Subtype.val this
  have hCw : oTwoRes X ⊔ S ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    refine sup_le ?_ ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      exact (hwOC g hg).symm
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      exact (hSw s hs).symm
  have hzC : (z : G) ∈ Subgroup.centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg =>
      ((Subgroup.mem_centralizer_iff.mp (hCw (hX hg))) (z : G) (Set.mem_singleton _)).symm
  exact Subgroup.ne_bot_iff_exists_ne_one.mpr
    ⟨⟨(z : G), Subgroup.mem_inf.mpr ⟨hwV, hzC⟩⟩, fun e => hw1 (congrArg Subtype.val e)⟩

theorem sq_mem_centralizer_of_relIndex_le_two [Finite G] {V : Subgroup G} {t : G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (ht : t ∈ Subgroup.normalizer (V : Set G))
    (hi : (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V ≤ 2) :
    t ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
  have hmemH : ∀ g, g ∈ V ⊓ Subgroup.centralizer ({t} : Set G) ↔ g ∈ V ∧ t * g = g * t := by
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp
  have hconj : ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp ht v).mp hv
  set H : Subgroup G := V ⊓ Subgroup.centralizer ({t} : Set G) with hHdef
  have hne0 : H.relIndex V ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hcases : H.relIndex V = 1 ∨ H.relIndex V = 2 := by omega
  rcases hcases with h1 | h2
  ·
    have hVH : V ≤ H := Subgroup.relIndex_eq_one.mp h1
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have htv : t * v = v * t := ((hmemH v).mp (hVH hv)).2
    calc v * t ^ 2 = v * (t * t) := by rw [pow_two]
      _ = (v * t) * t := by rw [mul_assoc]
      _ = (t * v) * t := by rw [htv]
      _ = t * (v * t) := by rw [mul_assoc]
      _ = t * (t * v) := by rw [htv]
      _ = t ^ 2 * v := by rw [pow_two, mul_assoc]
  ·
    obtain ⟨a, haV, ha⟩ := Subgroup.relIndex_eq_two_iff.mp h2
    have haH : a ∉ H := by
      intro haH
      have h1 := ha 1 (one_mem V)
      rw [xor_iff_iff_not, one_mul] at h1
      exact h1.mp haH (one_mem H)
    set f : G → G := fun v => v⁻¹ * (t * v * t⁻¹) with hfdef
    have hfV : ∀ v ∈ V, f v ∈ V := fun v hv => mul_mem (inv_mem hv) (hconj v hv)
    have hfmul : ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w := by
      intro v hv w hw
      have hu : (v⁻¹ * (t * v * t⁻¹)) * w⁻¹ = w⁻¹ * (v⁻¹ * (t * v * t⁻¹)) :=
        comm_of_mem_isElemAbelian hV (mul_mem (inv_mem hv) (hconj v hv)) (inv_mem hw)
      calc f (v * w) = w⁻¹ * (v⁻¹ * (t * v * t⁻¹)) * (t * w * t⁻¹) := by
            simp only [hfdef]; group
        _ = (v⁻¹ * (t * v * t⁻¹)) * w⁻¹ * (t * w * t⁻¹) := by rw [hu]
        _ = f v * f w := by simp only [hfdef]; group
    have hfone_eq : ∀ v, f v = 1 ↔ t * v = v * t := by
      intro v
      simp only [hfdef, inv_mul_eq_one]
      rw [eq_mul_inv_iff_mul_eq]
      exact eq_comm
    have hfone : ∀ v ∈ V, f v = 1 ↔ v ∈ H := fun v hv => by
      rw [hmemH, hfone_eq]
      exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
    set x : G := f a with hxdef
    have hx1 : x ≠ 1 := fun e => haH ((hfone a haV).mp e)
    have hxV : x ∈ V := hfV a haV
    have hxx : x * x = 1 := by
      have := hV.2 x hxV
      rwa [pow_two] at this
    have hval : ∀ b ∈ V, f b = 1 ∨ f b = x := by
      intro b hb
      by_cases hbH : b ∈ H
      · exact Or.inl ((hfone b hb).mpr hbH)
      · right
        have hba : b * a ∈ H := by
          have h1 := ha b hb
          rw [xor_iff_iff_not] at h1
          exact h1.mpr hbH
        have h1 : f (b * a) = 1 := (hfone (b * a) (mul_mem hb haV)).mpr hba
        rw [hfmul b hb a haV] at h1
        have h1' : f b * x = 1 := h1
        calc f b = f b * (x * x) := by rw [hxx, mul_one]
          _ = (f b * x) * x := (mul_assoc _ _ _).symm
          _ = x := by rw [h1', one_mul]
    have htx : t * x * t⁻¹ = x := by
      have hcalc : f (t * a * t⁻¹) = t * x * t⁻¹ := by
        simp only [hxdef, hfdef]; group
      rcases hval (t * a * t⁻¹) (hconj a haV) with h0 | h0
      · exfalso
        have h1 : t * x * t⁻¹ = 1 := by rw [← hcalc, h0]
        apply hx1
        calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
          _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
      · rw [← hcalc, h0]
    have hxH : x ∈ H := by
      refine (hmemH x).mpr ⟨hxV, ?_⟩
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [htx]
    have hfH : ∀ v ∈ V, f v ∈ H := by
      intro v hv
      rcases hval v hv with h0 | h0
      · rw [h0]; exact one_mem H
      · rw [h0]; exact hxH
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hTv : t * v * t⁻¹ = v * f v := by simp only [hfdef]; group
    have hv' : t * v = v * f v * t := by rw [← hTv]; group
    have hwt : t * f v = f v * t := ((hmemH (f v)).mp (hfH v hv)).2
    have hww : f v * f v = 1 := by
      have := hV.2 (f v) (hfV v hv)
      rwa [pow_two] at this
    have h2 : t ^ 2 * v = v * t ^ 2 := by
      calc t ^ 2 * v = t * (t * v) := by rw [pow_two, mul_assoc]
        _ = t * (v * f v * t) := by rw [hv']
        _ = (t * v) * f v * t := by group
        _ = (v * f v * t) * f v * t := by rw [hv']
        _ = v * f v * (t * f v) * t := by group
        _ = v * f v * (f v * t) * t := by rw [hwt]
        _ = v * (f v * f v) * (t * t) := by group
        _ = v * t ^ 2 := by rw [hww, mul_one, pow_two]
    exact h2.symm

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
