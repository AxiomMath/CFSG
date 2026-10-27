module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6F2

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSub_le_centralizer {A B : Subgroup G} (h : G)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    B6.conjSub h A ≤ Subgroup.centralizer (B6.conjSub h B : Set G) := by
  rw [centralizer_conjSub]
  exact (B6.conjSub h).monotone hAB

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V]

namespace Cyc

variable {c : Ctx T L V E z v} {g : G} (hg : c.Cyc g)
include hg

theorem conj_mem_CE {h k : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    (hk : k ∈ Subgroup.centralizer (E : Set G)) : h * k * h⁻¹ ∈ Subgroup.centralizer (E : Set G) :=
  (Subgroup.mem_normalizer_iff.1 (F7.normalizer_le_normalizer_centralizer E hh) k).1 hk

theorem conjSub_inv_le_CE {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G)) {P : Subgroup G}
    (hPK : P ≤ Subgroup.centralizer (E : Set G)) :
    B6.conjSub h⁻¹ P ≤ Subgroup.centralizer (E : Set G) := by
  intro x hx
  rw [B6.mem_conjSub, inv_inv] at hx
  have := hg.conj_mem_CE (Subgroup.inv_mem _ hh) (hPK hx)
  simpa [mul_assoc] using this

theorem comm_cube (h12210 : Stmt12_2_10) {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    {P : Subgroup G} (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P)
    {s s' : G} (hs : s ∈ P) (hs' : s' ∈ P) :
    s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∧
      s * s * s ∈ Subgroup.centralizer (B6.conjSub h V : Set G) := by
  have hP'K := hg.conjSub_inv_le_CE hh hPK
  have hP'3 : IsPGroup 3 (B6.conjSub h⁻¹ P) := hP3.map _
  obtain ⟨h1, h2, -⟩ := c.three_sub_facts h12210 hP'K hP'3
  have hmem : ∀ x ∈ P, h⁻¹ * x * h ∈ B6.conjSub h⁻¹ P := fun x hx => by
    rw [B6.mem_conjSub, inv_inv]; simpa [mul_assoc] using hx
  rw [centralizer_conjSub, B6.mem_conjSub, B6.mem_conjSub]
  refine ⟨?_, ?_⟩
  · have := h1 _ (hmem s hs) _ (hmem s' hs')
    convert this using 1
    group
  · have := h2 _ (hmem s hs)
    convert this using 1
    group

theorem idx3 (h12210 : Stmt12_2_10) {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    {P : Subgroup G} (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P)
    {s y : G} (hs : s ∈ P) (hy : y ∈ P)
    (hsV : s ∉ Subgroup.centralizer (B6.conjSub h V : Set G)) :
    y ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∨
      s⁻¹ * y ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∨
      (s * s)⁻¹ * y ∈ Subgroup.centralizer (B6.conjSub h V : Set G) := by
  have hP'K := hg.conjSub_inv_le_CE hh hPK
  have hP'3 : IsPGroup 3 (B6.conjSub h⁻¹ P) := hP3.map _
  obtain ⟨-, -, h3⟩ := c.three_sub_facts h12210 hP'K hP'3
  have hmem : ∀ x ∈ P, h⁻¹ * x * h ∈ B6.conjSub h⁻¹ P := fun x hx => by
    rw [B6.mem_conjSub, inv_inv]; simpa [mul_assoc] using hx
  rw [centralizer_conjSub] at hsV ⊢
  rw [B6.mem_conjSub] at hsV
  rw [B6.mem_conjSub, B6.mem_conjSub, B6.mem_conjSub]
  rcases h3 _ (hmem s hs) hsV _ (hmem y hy) with h4 | h4 | h4
  · exact Or.inl h4
  · refine Or.inr (Or.inl ?_)
    convert h4 using 1
    group
  · refine Or.inr (Or.inr ?_)
    convert h4 using 1
    group

theorem isElemAbelian (h12210 : Stmt12_2_10) (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    {P : Subgroup G} (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P) :
    IsElemAbelian 3 P := by
  have hgE := hg.NR1_le_NE hg.mem
  have hggE : g * g ∈ Subgroup.normalizer (E : Set G) := Subgroup.mul_mem _ hgE hgE
  have hodd : ∀ x ∈ P, Odd (orderOf x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    have h1 : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h1)
  have key : ∀ s ∈ P, ∀ s' ∈ P, s * s' * s⁻¹ * s'⁻¹ = 1 ∧ s * s * s = 1 := by
    intro s hs s' hs'
    obtain ⟨h0, h0'⟩ := hg.comm_cube h12210 (Subgroup.one_mem _) hPK hP3 hs hs'
    obtain ⟨h1, h1'⟩ := hg.comm_cube h12210 hgE hPK hP3 hs hs'
    obtain ⟨h2, h2'⟩ := hg.comm_cube h12210 hggE hPK hP3 hs hs'
    rw [B6.conjSub_one] at h0 h0'
    have hm : s * s' * s⁻¹ * s'⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hs hs') (P.inv_mem hs)) (P.inv_mem hs')
    have hm' : s * s * s ∈ P := P.mul_mem (P.mul_mem hs hs) hs
    exact ⟨hg.eq_one_of_odd hcomm h0 h1 h2 (hodd _ hm),
      hg.eq_one_of_odd hcomm h0' h1' h2' (hodd _ hm')⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := (key a a.2 b b.2).1
    show (a : G) * b = b * a
    calc (a : G) * b = ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by
          group
      _ = b * a := by rw [h1, one_mul]
  · rw [pow_three']
    exact (key x hx x hx).2

theorem conjL1_le_of_mem {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G)) {N : Subgroup G}
    (hN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (N : Set G)) {x : G}
    (hx : x ∈ B6.conjSub h c.L1) (hxN : x ∈ N) (hx3 : x * x * x = 1)
    (hx1 : x ∉ Subgroup.centralizer (B6.conjSub h V : Set G)) : B6.conjSub h c.L1 ≤ N := by
  rw [B6.mem_conjSub] at hx
  rw [centralizer_conjSub, B6.mem_conjSub] at hx1
  have hN' : L ⊓ Subgroup.centralizer (E : Set G) ≤
      Subgroup.normalizer (B6.conjSub h⁻¹ N : Set G) := by
    intro y hy
    apply mem_normalizer_conjSub
    rw [inv_inv]
    exact hN (hg.conj_mem_CE hh hy.2)
  have hxN' : h⁻¹ * x * h ∈ B6.conjSub h⁻¹ N := by
    rw [B6.mem_conjSub, inv_inv]; simpa [mul_assoc] using hxN
  have hx3' : (h⁻¹ * x * h) * (h⁻¹ * x * h) * (h⁻¹ * x * h) = 1 := by
    rw [show (h⁻¹ * x * h) * (h⁻¹ * x * h) * (h⁻¹ * x * h) = h⁻¹ * (x * x * x) * h by group, hx3]
    group
  have h1 := c.L1_le_of_mem hN' (c.L1_le hx) hxN' hx3' hx1
  have h2 := (B6.conjSub h).monotone h1
  rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one] at h2

theorem cube_conjSub : B6.conjSub (g * g * g) V = V ∧ B6.conjSub (g * g * g) c.L1 = c.L1 := by
  have hm : g * g * g ∈ Subgroup.normalizer (c.R1 : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.mem hg.mem) hg.mem
  obtain ⟨h1, h2⟩ := hg.fix_z hm hg.cube_z
  exact ⟨B6.conjSub_eq_self h1, B6.conjSub_eq_self h2⟩

theorem table : ∃ t₀ : G,
    B6.conjSub t₀ V = V ∧ B6.conjSub t₀ c.L1 = c.L1 ∧
    B6.conjSub t₀ (B6.conjSub g V) = B6.conjSub (g * g) V ∧
    B6.conjSub t₀ (B6.conjSub (g * g) V) = B6.conjSub g V ∧
    B6.conjSub g (B6.conjSub g V) = B6.conjSub (g * g) V ∧
    B6.conjSub g (B6.conjSub (g * g) V) = V ∧
    B6.conjSub (g * g) (B6.conjSub g V) = V ∧
    B6.conjSub (g * g) (B6.conjSub (g * g) V) = B6.conjSub g V ∧
    B6.conjSub g (B6.conjSub g c.L1) = B6.conjSub (g * g) c.L1 ∧
    B6.conjSub g (B6.conjSub (g * g) c.L1) = c.L1 ∧
    B6.conjSub (g * g) (B6.conjSub g c.L1) = c.L1 := by
  obtain ⟨t₀, ht₀, ht₀v⟩ := c.exists_t0
  have ht₀z := c.conj_z ht₀
  have ht₀R := c.T_le_NR1 ht₀
  have hgg := Subgroup.mul_mem _ hg.mem hg.mem
  obtain ⟨h3V, h3L⟩ := hg.cube_conjSub
  obtain ⟨ht₀V, ht₀L⟩ := hg.fix_z ht₀R ht₀z
  refine ⟨t₀, B6.conjSub_eq_self ht₀V, B6.conjSub_eq_self ht₀L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [← B6.conjSub_mul]
    refine (hg.conjSub_eq_of_conj_z (Subgroup.mul_mem _ ht₀R hg.mem) hgg ?_).1
    rw [hg.sq_z]
    calc t₀ * g * z * (t₀ * g)⁻¹ = t₀ * (g * z * g⁻¹) * t₀⁻¹ := by group
      _ = v * z := by rw [hg.hz, ht₀v]
  · rw [← B6.conjSub_mul]
    refine (hg.conjSub_eq_of_conj_z (Subgroup.mul_mem _ ht₀R hgg) hg.mem ?_).1
    rw [hg.hz]
    calc t₀ * (g * g) * z * (t₀ * (g * g))⁻¹ = t₀ * ((g * g) * z * (g * g)⁻¹) * t₀⁻¹ := by group
      _ = (t₀ * v * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by rw [hg.sq_z]; group
      _ = v := by rw [ht₀v, ht₀z, mul_assoc, c.z_sq, mul_one]
  · rw [← B6.conjSub_mul]
  · rw [← B6.conjSub_mul, ← mul_assoc, h3V]
  · rw [← B6.conjSub_mul, h3V]
  · rw [← B6.conjSub_mul]
    refine (hg.conjSub_eq_of_conj_z (Subgroup.mul_mem _ hgg hgg) hg.mem ?_).1
    calc g * g * (g * g) * z * (g * g * (g * g))⁻¹ =
        g * ((g * g * g) * z * (g * g * g)⁻¹) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hg.cube_z]
  · rw [← B6.conjSub_mul]
  · rw [← B6.conjSub_mul, ← mul_assoc, h3L]
  · rw [← B6.conjSub_mul, h3L]

theorem sym (hα : c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)) :
    c.L1 ≤ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) ∧
    B6.conjSub g c.L1 ≤ Subgroup.centralizer (V : Set G) ∧
    B6.conjSub g c.L1 ≤ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) ∧
    B6.conjSub (g * g) c.L1 ≤ Subgroup.centralizer (V : Set G) ∧
    B6.conjSub (g * g) c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G) := by
  obtain ⟨t₀, -, ht₀L, ht₀g, -, hgg1, hgg2, hg2g, hg2g2, -, -, -⟩ := hg.table
  have h1 : c.L1 ≤ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) := by
    have := conjSub_le_centralizer t₀ hα
    rwa [ht₀L, ht₀g] at this
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · have := conjSub_le_centralizer g h1
    rwa [hgg2] at this
  · have := conjSub_le_centralizer g hα
    rwa [hgg1] at this
  · have := conjSub_le_centralizer (g * g) hα
    rwa [hg2g] at this
  · have := conjSub_le_centralizer (g * g) h1
    rwa [hg2g2] at this

theorem sym' :
    (c.L1 ≤ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) →
      c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)) ∧
    (B6.conjSub g c.L1 ≤ Subgroup.centralizer (V : Set G) →
      c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)) ∧
    (B6.conjSub g c.L1 ≤ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) →
      c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)) ∧
    (B6.conjSub (g * g) c.L1 ≤ Subgroup.centralizer (V : Set G) →
      c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)) ∧
    (B6.conjSub (g * g) c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G) →
      c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)) := by
  obtain ⟨t₀, -, ht₀L, -, ht₀gg, hgg1, -, -, hg2g2, -, hgL2, hg2L1⟩ := hg.table
  have h0 : c.L1 ≤ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) →
      c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G) := by
    intro h
    have := conjSub_le_centralizer t₀ h
    rwa [ht₀L, ht₀gg] at this
  refine ⟨h0, fun h => h0 ?_, fun h => ?_, fun h => ?_, fun h => h0 ?_⟩
  · have := conjSub_le_centralizer (g * g) h
    rwa [hg2L1] at this
  · have := conjSub_le_centralizer (g * g) h
    rwa [hg2L1, hg2g2] at this
  · have := conjSub_le_centralizer g h
    rwa [hgL2] at this
  · have := conjSub_le_centralizer g h
    rwa [hgL2, hgg1] at this

end Cyc

end Ctx

end N1246

end CFSG.Quasithin.H13
