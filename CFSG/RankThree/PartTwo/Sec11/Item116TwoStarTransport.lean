module

public import CFSG.RankThree.PartTwo.Sec11.Item116TheoremOP2
public import CFSG.RankThree.Theta.TwoPlaneAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

namespace TwoStarTransport

section General

variable {X Y : Type*} [Group X] [Group Y]

theorem twoStarConditionAt_of_mulEquiv {A : Subgroup X} {a : X} {B : Subgroup Y} {b : Y}
    (ψ : Subgroup.centralizer ({a} : Set X) ≃* Subgroup.centralizer ({b} : Set Y))
    (hline : (centralLine a).map ψ.toMonoidHom = centralLine b)
    (hA : (A.subgroupOf (Subgroup.centralizer ({a} : Set X))).map ψ.toMonoidHom =
      B.subgroupOf (Subgroup.centralizer ({b} : Set Y)))
    (h : TwoStarConditionAt A a) : TwoStarConditionAt B b := by
  unfold TwoStarConditionAt at h ⊢
  set ψ' := QuotientGroup.congr (centralLine a) (centralLine b) ψ hline with hψ'
  have hcomp : ψ'.toMonoidHom.comp (QuotientGroup.mk' (centralLine a)) =
      (QuotientGroup.mk' (centralLine b)).comp ψ.toMonoidHom := by
    ext x
    rfl
  have hP : ((A.subgroupOf (Subgroup.centralizer ({a} : Set X))).map
      (QuotientGroup.mk' (centralLine a))).map ψ'.toMonoidHom =
      (B.subgroupOf (Subgroup.centralizer ({b} : Set Y))).map
        (QuotientGroup.mk' (centralLine b)) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hA]
  rw [← hP, ← twoAlpha_map_equiv, ← CFSG.pCore_map_iso 2 ψ']
  exact Subgroup.map_mono h

theorem twoStarConditionAt_map {A : Subgroup X} {a : X} (φ : X ≃* Y)
    (h : TwoStarConditionAt A a) : TwoStarConditionAt (A.map φ.toMonoidHom) (φ a) := by
  have hC : (Subgroup.centralizer ({a} : Set X)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ a} : Set Y) := map_centralizer_singleton φ a
  set ψ : Subgroup.centralizer ({a} : Set X) ≃* Subgroup.centralizer ({φ a} : Set Y) :=
    ((Subgroup.centralizer ({a} : Set X)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hC) with hψ
  have hψv : ∀ x, ((ψ x : Subgroup.centralizer ({φ a} : Set Y)) : Y) = φ x := fun x => rfl
  refine twoStarConditionAt_of_mulEquiv ψ ?_ ?_ h
  · rw [centralLine, centralLine, MonoidHom.map_zpowers]
    congr 1
  · apply Subgroup.map_injective (Subgroup.centralizer ({φ a} : Set Y)).subtype_injective
    rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    have hcomp : (Subgroup.centralizer ({φ a} : Set Y)).subtype.comp ψ.toMonoidHom =
        φ.toMonoidHom.comp (Subgroup.centralizer ({a} : Set X)).subtype := by
      ext x
      exact hψv x
    rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      Subgroup.map_inf_eq A _ φ.toMonoidHom φ.injective, hC]

theorem twoStarConditionAt_of_zpowers_eq {A : Subgroup X} {a b : X}
    (hab : Subgroup.zpowers a = Subgroup.zpowers b) (h : TwoStarConditionAt A a) :
    TwoStarConditionAt A b := by
  have hC : Subgroup.centralizer ({a} : Set X) = Subgroup.centralizer ({b} : Set X) := by
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
      GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hab]
  set ψ := MulEquiv.subgroupCongr hC with hψ
  have hψv : ∀ x, ((ψ x : Subgroup.centralizer ({b} : Set X)) : X) = x := fun x => rfl
  refine twoStarConditionAt_of_mulEquiv ψ ?_ ?_ h
  · apply Subgroup.map_injective (Subgroup.centralizer ({b} : Set X)).subtype_injective
    rw [Subgroup.map_map, centralLine, centralLine, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    have h1 : ((Subgroup.centralizer ({b} : Set X)).subtype.comp ψ.toMonoidHom)
        ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = a := rfl
    rw [h1]
    exact hab
  · apply Subgroup.map_injective (Subgroup.centralizer ({b} : Set X)).subtype_injective
    rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    have hcomp : (Subgroup.centralizer ({b} : Set X)).subtype.comp ψ.toMonoidHom =
        (Subgroup.centralizer ({a} : Set X)).subtype := by
      ext x
      exact hψv x
    rw [hcomp, Subgroup.subgroupOf_map_subtype, hC]

theorem twoStarConditionAt_conj {A : Subgroup X} {a g : X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) (h : TwoStarConditionAt A a) :
    TwoStarConditionAt A (g * a * g⁻¹) := by
  have h1 := twoStarConditionAt_map (MulAut.conj g) h
  rwa [GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer hg, MulAut.conj_apply] at h1

end General

end TwoStarTransport

section Points

variable {G : Type} [Group G] [Finite G]

namespace TwoStarTransport

theorem zpowers_zpow_eq {x : G} (hx3 : x ^ 3 = 1) {k : ℤ} (hk : x ^ k ≠ 1) :
    Subgroup.zpowers (x ^ k) = Subgroup.zpowers x :=
  TheoremO.zpowers_eq_of_mem_of_ne_one hx3 (Subgroup.zpow_mem_zpowers x k) hk

theorem zpowers_eq_of_mem_closure_pair {c d : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.closure ({c, d} : Set G)) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Subgroup.zpowers c ∨ Subgroup.zpowers x = Subgroup.zpowers d ∨
      Subgroup.zpowers x = Subgroup.zpowers (c * d) ∨
        Subgroup.zpowers x = Subgroup.zpowers (c * d⁻¹) := by
  obtain ⟨i, j, rfl⟩ := TheoremO.exists_zpow_mul_zpow_of_mem_closure_pair hcd hx
  have hc3' : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
  have hd3' : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
  have hcomm : ∀ k l : ℤ, c ^ k * d ^ l = d ^ l * c ^ k := fun k l =>
    (Commute.zpow_zpow (hcd : Commute c d) k l).eq
  have hi := zpow_eq_zpow_emod i hc3'
  have hj := zpow_eq_zpow_emod j hd3'
  have hi0 : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
  have hi3 : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
  have hj0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
  have hj3 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
  have hcd' : Commute c d := hcd
  have hcd3 : (c * d) ^ 3 = 1 := by
    rw [hcd'.mul_pow, hc3, hd3, one_mul]
  have hcdi3 : (c * d⁻¹) ^ 3 = 1 := by
    rw [hcd'.inv_right.mul_pow, hc3, inv_pow, hd3, inv_one, one_mul]
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h0 | h1 | h2 <;>
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with k0 | k1 | k2
  · exact absurd (by rw [hi, hj, h0, k0, zpow_zero, zpow_zero, one_mul]) hx1
  · right; left
    rw [hi, hj, h0, k1, zpow_zero, zpow_one, one_mul]
  · right; left
    rw [hi, hj, h0, k2, zpow_zero, one_mul]
    exact zpowers_zpow_eq hd3 (by rwa [hi, hj, h0, k2, zpow_zero, one_mul] at hx1)
  · left
    rw [hi, hj, h1, k0, zpow_zero, zpow_one, mul_one]
  · right; right; left
    rw [hi, hj, h1, k1, zpow_one, zpow_one]
  · right; right; right
    have he : c ^ (1 : ℤ) * d ^ (2 : ℤ) = c * d⁻¹ := by
      rw [zpow_one, show (2 : ℤ) = 3 + (-1) by norm_num, zpow_add, hd3', one_mul, zpow_neg,
        zpow_one]
    rw [hi, hj, h1, k2, he]
  · left
    rw [hi, hj, h2, k0, zpow_zero, mul_one]
    exact zpowers_zpow_eq hc3 (by rwa [hi, hj, h2, k0, zpow_zero, mul_one] at hx1)
  · right; right; right
    have he : c ^ (2 : ℤ) * d ^ (1 : ℤ) = (c * d⁻¹) ^ (2 : ℤ) := by
      rw [hcd'.inv_right.mul_zpow, zpow_one, inv_zpow',
        show (-(2 : ℤ)) = (-3) + 1 by norm_num, zpow_add, zpow_neg, hd3', inv_one, one_mul,
        zpow_one]
    rw [hi, hj, h2, k1, he]
    exact zpowers_zpow_eq hcdi3 (by rwa [hi, hj, h2, k1, he] at hx1)
  · right; right; left
    have he : c ^ (2 : ℤ) * d ^ (2 : ℤ) = (c * d) ^ (2 : ℤ) :=
      (hcd'.mul_zpow 2).symm
    rw [hi, hj, h2, k2, he]
    exact zpowers_zpow_eq hcd3 (by rwa [hi, hj, h2, k2, he] at hx1)

end TwoStarTransport

end Points

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem TwoStarTransport.exists_transvection_zpowers_eq (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) {x : G} (hx : x ∈ A)
    (hxB : x ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      Subgroup.zpowers x = Subgroup.zpowers (w * a * w⁻¹) := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have hBA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h.mem_A
    · exact hdA
  have htr := Item116Fusion.exists_transvection_eq h hdL hWB hirr hdc
  obtain ⟨b, hb, k, hk3, rfl⟩ := Item116Fusion.exists_mem_closure_mul_pow h hdL hdc hx
  have ha3 := hexp a h.a_mem
  have hab : a * b = b * a := hcomm a h.a_mem b (hBA hb)
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact absurd (by rw [pow_zero, mul_one]; exact hb) hxB
  · obtain ⟨w, hwW, -, hwa⟩ := htr b hb
    exact ⟨w, hwW, by rw [hwa, pow_one, hab]⟩
  · obtain ⟨w, hwW, -, hwa⟩ := htr b⁻¹ (Subgroup.inv_mem _ hb)
    refine ⟨w, hwW, ?_⟩
    rw [hwa, ← Subgroup.zpowers_inv]
    congr 1
    have hai : a⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', ha3])
    calc (b * a ^ 2)⁻¹ = (a ^ 2)⁻¹ * b⁻¹ := by group
      _ = a * b⁻¹ := by
          rw [← hai, inv_inv]

theorem TwoStarTransport.twoStar_of_points (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) (hc : TwoStarConditionAt A c)
    (hd : TwoStarConditionAt A d) (hcd : TwoStarConditionAt A (c * d))
    (hcdi : TwoStarConditionAt A (c * d⁻¹)) (ha : TwoStarConditionAt A a) :
    ∀ x ∈ A, x ≠ 1 → TwoStarConditionAt A x := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  intro x hx hx1
  by_cases hxB : x ∈ Subgroup.closure ({c, d} : Set G)
  · rcases TwoStarTransport.zpowers_eq_of_mem_closure_pair (hcomm c h.mem_A d hdA)
        (hexp c h.mem_A) (hexp d hdA) hxB hx1 with h1 | h1 | h1 | h1
    · exact TwoStarTransport.twoStarConditionAt_of_zpowers_eq h1.symm hc
    · exact TwoStarTransport.twoStarConditionAt_of_zpowers_eq h1.symm hd
    · exact TwoStarTransport.twoStarConditionAt_of_zpowers_eq h1.symm hcd
    · exact TwoStarTransport.twoStarConditionAt_of_zpowers_eq h1.symm hcdi
  · obtain ⟨w, hwW, hxw⟩ :=
      TwoStarTransport.exists_transvection_zpowers_eq h hdL hWB hirr hdc hx hxB
    exact TwoStarTransport.twoStarConditionAt_of_zpowers_eq hxw.symm
      (TwoStarTransport.twoStarConditionAt_conj hwW ha)

theorem TwoStarTransport.twoStar_at_d_of_conj (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G))
    (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d) (hc : TwoStarConditionAt A c) :
    TwoStarConditionAt A d := by
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have hnc1 : n * c * n⁻¹ ≠ 1 := fun h1 => h.ne_one (by
    calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  exact TwoStarTransport.twoStarConditionAt_of_zpowers_eq
    (TheoremO.zpowers_eq_of_mem_of_ne_one (h.mem_partTwoF.1.2 d hdA) hnc hnc1)
    (TwoStarTransport.twoStarConditionAt_conj hnW hc)

theorem TwoStarTransport.twoStar_at_cd_inv (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) {x : G} (hx : TwoStarConditionAt A (c * x))
    (hxd : x = d ∨ x = d⁻¹) : TwoStarConditionAt A (c * x⁻¹) := by
  obtain ⟨m, hmW, hmc, hmd, -⟩ := TheoremO.exists_inverting_fixing h hdL hWB hirr hdc
  have h1 := TwoStarTransport.twoStarConditionAt_conj hmW hx
  have hmx : m * x * m⁻¹ = x⁻¹ := by
    rcases hxd with rfl | rfl
    · exact hmd
    · rw [show m * d⁻¹ * m⁻¹ = (m * d * m⁻¹)⁻¹ by group, hmd]
  rwa [show m * (c * x) * m⁻¹ = (m * c * m⁻¹) * (m * x * m⁻¹) by group, hmc, hmx] at h1

end Certified

end CFSG.RankThree.PartTwo.Sec11
