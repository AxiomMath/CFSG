module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusInvolutionDerived
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open

section

theorem mem_or_mem_mul_of_mem_sup_zpowers614 {G : Type*} [Group G] {U : Subgroup G} {w : G}
    (hw2 : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) {g : G}
    (hg : g ∈ U ⊔ Subgroup.zpowers w) : g ∈ U ∨ ∃ u ∈ U, g = u * w := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwx : ∀ x ∈ U, w * x = x⁻¹ * w := fun x hx => by
    rw [← hwinv x hx]; group
  let S : Subgroup G :=
    { carrier := {g | g ∈ U ∨ ∃ u ∈ U, g = u * w}
      mul_mem' := by
        rintro a b (ha | ⟨u, hu, rfl⟩) (hb | ⟨v, hv, rfl⟩)
        · exact Or.inl (U.mul_mem ha hb)
        · exact Or.inr ⟨a * v, U.mul_mem ha hv, by group⟩
        · refine Or.inr ⟨u * b⁻¹, U.mul_mem hu (U.inv_mem hb), ?_⟩
          rw [mul_assoc, hwx b hb, ← mul_assoc]
        · refine Or.inl ?_
          have e : u * w * (v * w) = u * v⁻¹ := by
            calc u * w * (v * w) = u * (w * v) * w := by group
              _ = u * (v⁻¹ * w) * w := by rw [hwx v hv]
              _ = u * v⁻¹ * (w * w) := by group
              _ = u * v⁻¹ := by rw [hw2, mul_one]
          rw [e]
          exact U.mul_mem hu (U.inv_mem hv)
      one_mem' := Or.inl U.one_mem
      inv_mem' := by
        rintro a (ha | ⟨u, hu, rfl⟩)
        · exact Or.inl (U.inv_mem ha)
        · refine Or.inr ⟨u, hu, ?_⟩
          rw [mul_inv_rev, hwi, hwx _ (U.inv_mem hu), inv_inv] }
  have hUS : U ≤ S := fun x hx => Or.inl hx
  have hwS : Subgroup.zpowers w ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Or.inr ⟨1, U.one_mem, by rw [one_mul]⟩
  exact (sup_le hUS hwS) hg

variable {F : Type*} [Field F] [Finite F]

theorem pgl2_inner_involution_data614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {z : PGL2 F}
    (hzJ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) :
    ∃ (U : Subgroup (PGL2 F)) (w : PGL2 F), IsCyclic U ∧ z ∈ U ∧ w * w = 1 ∧ w ∉ U ∧
      (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({z} : Set (PGL2 F)) = U ⊔ Subgroup.zpowers w ∧
      ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  classical
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three F hK hcard
  have hJidx : (commutator (PGL2 F)).index = 2 := hJ ▸ pgl2_psl2Range_index_eq_two F hK
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hpo, -, hq⟩ := hK
    rw [hq]
    exact hpo.pow
  have hdata : ∃ (U : Subgroup (PGL2 F)) (s w : PGL2 F), IsCyclic U ∧ s ∈ U ∧ s * s = 1 ∧
      s ≠ 1 ∧ w ∉ U ∧ w * w = 1 ∧ (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({s} : Set (PGL2 F)) = U ⊔ Subgroup.zpowers w ∧
      ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
      s ∈ commutator (PGL2 F) := by
    rcases Nat.even_or_odd ((Nat.card F - 1) / 2) with hev | hev
    · obtain ⟨U, s, w, hUc, hUcard, hsU, hss, hs1, hwU, hww, hwinv, hC, hUJ⟩ :=
        pgl2_split_torus_centralizer_data F hodd
      refine ⟨U, s, w, hUc, hsU, hss, hs1, hwU, hww, hwinv, hC, hUJ hodd, ?_⟩
      refine pgl2_torus_involution_mem_commutator hJidx U hUc hsU hss hs1
        (m := (Nat.card F - 1) / 2) ?_ hev (hJ ▸ hUJ hodd)
      rw [hUcard]
      obtain ⟨k, hk⟩ := hodd
      omega
    · obtain ⟨U, s, w, hUc, hUcard, hsU, hss, hs1, hwU, hww, hwinv, hC, hUJ⟩ :=
        pgl2_nonsplit_torus_centralizer_data F hodd
      refine ⟨U, s, w, hUc, hsU, hss, hs1, hwU, hww, hwinv, hC, hUJ hodd, ?_⟩
      refine pgl2_torus_involution_mem_commutator hJidx U hUc hsU hss hs1
        (m := (Nat.card F + 1) / 2) ?_ ?_ (hJ ▸ hUJ hodd)
      · rw [hUcard]
        obtain ⟨k, hk⟩ := hodd
        omega
      · obtain ⟨k, hk⟩ := hodd
        obtain ⟨j, hj⟩ := hev
        refine ⟨(k + 1) / 2, ?_⟩
        omega
  obtain ⟨U, s, w, hUc, hsU, hss, hs1, hwU, hww, hwinv, hC, hUJ, hsJ⟩ := hdata
  have hsI : BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [pow_two]; exact hss⟩
  obtain ⟨g, -, hg⟩ := pgl2_inner_involutions_conjugate hK hcard hsJ hsI (hJ ▸ hzJ) hz
  set c := (MulAut.conj g).toMonoidHom with hc
  have hrange : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.Normal :=
    Subgroup.normal_of_index_eq_two (pgl2_psl2Range_index_eq_two F hK)
  refine ⟨U.map c, g * w * g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : IsCyclic ↥U := hUc
    exact isCyclic_of_surjective (c.subgroupMap U) (c.subgroupMap_surjective U)
  · exact ⟨s, hsU, by rw [← hg]; rfl⟩
  · rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, hww]
    group
  · rintro ⟨x, hx, hxe⟩
    have : x = w := by
      have hxe' : g * x * g⁻¹ = g * w * g⁻¹ := hxe
      simpa using hxe'
    exact hwU (this ▸ hx)
  · rintro _ ⟨x, hx, rfl⟩
    show g * w * g⁻¹ * (g * x * g⁻¹) * (g * w * g⁻¹)⁻¹ = (g * x * g⁻¹)⁻¹
    have := hwinv x hx
    calc g * w * g⁻¹ * (g * x * g⁻¹) * (g * w * g⁻¹)⁻¹ = g * (w * x * w⁻¹) * g⁻¹ := by group
      _ = (g * x * g⁻¹)⁻¹ := by rw [this]; group
  · have e1 : Subgroup.centralizer ({z} : Set (PGL2 F)) =
        (Subgroup.centralizer ({s} : Set (PGL2 F))).map c := by
      ext x
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
      constructor
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by simp [hc, MulAut.conj_apply, mul_assoc]⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hg] at hx
        calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [hx]
          _ = s * (g⁻¹ * x * g) := by group
      · rintro ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hy
        rw [← hg]
        show g * y * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * y * g⁻¹)
        calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
          _ = g * (s * y) * g⁻¹ := by rw [hy]
          _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e1, hC, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  · intro hle
    apply hUJ
    intro x hx
    have h1 : g * x * g⁻¹ ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := F)).range := hle ⟨x, hx, rfl⟩
    have := hrange.conj_mem _ h1 g⁻¹
    simpa [mul_assoc] using this

theorem pgl2_inner_order_five614 (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    {y z : PGL2 F} (hy : orderOf y = 5)
    (hyJ : y ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hzJ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) (hyz : Commute y z) :
    (∀ e : PGL2 F, e ^ 2 = 1 → Commute e y → e = 1 ∨ e = z) ∧
      ∃ r ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range,
        r ^ 2 = 1 ∧ r * y * r⁻¹ = y⁻¹ := by
  classical
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨U, w, hUc, hzU, hww, hwU, hwinv, hC, hUJ⟩ := pgl2_inner_involution_data614 hK hcard hzJ hz
  set J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hJdef
  have hJidx : J.index = 2 := pgl2_psl2Range_index_eq_two F hK
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJidx
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have : IsCyclic ↥U := hUc
    let _ : CommGroup ↥U := IsCyclic.commGroup
    have := mul_comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hy1 : y ≠ y⁻¹ := by
    intro h
    have h2 : y ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h]; exact mul_inv_cancel y
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy] at this
    norm_num at this
  have hUw : ∀ u ∈ U, ∀ x ∈ U, (u * w) * x * (u * w)⁻¹ = x⁻¹ := by
    intro u hu x hx
    calc (u * w) * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hwinv x hx]
      _ = x⁻¹ := by rw [hUcomm u hu _ (U.inv_mem hx)]; group
  have hyU : y ∈ U := by
    have hyC : y ∈ U ⊔ Subgroup.zpowers w := by
      rw [← hC, Subgroup.mem_centralizer_singleton_iff]
      exact hyz.eq
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv hyC with h | ⟨u, hu, rfl⟩
    · exact h
    · exfalso
      have h2 : (u * w) ^ 2 = 1 := by
        rw [pow_two]
        calc u * w * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
          _ = u * u⁻¹ * (w * w) := by rw [hwinv u hu]
          _ = 1 := by rw [hww]; group
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hy] at this
      norm_num at this
  have hCU : ∀ g ∈ Subgroup.centralizer ({z} : Set (PGL2 F)), Commute g y → g ∈ U := by
    intro g hg hgy
    rw [hC] at hg
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv hg with h | ⟨u, hu, rfl⟩
    · exact h
    · exfalso
      apply hy1
      have := hUw u hu y hyU
      rw [hgy.eq, mul_inv_cancel_right] at this
      exact this
  have hCJ : ∀ g ∈ J, Commute g y → g ∈ U := by
    intro g hgJ hgy
    obtain ⟨g₁, rfl⟩ := hgJ
    obtain ⟨y₁, rfl⟩ := hyJ
    obtain ⟨z₁, rfl⟩ := hzJ
    have hinj := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F)
    have hz₁ : BenderSuzuki.PFAppendixIII.IsInvolution z₁ := by
      refine ⟨fun h => hz.1 (by rw [h, map_one]), hinj ?_⟩
      rw [map_pow, hz.2, map_one]
    have hyz₁ : Commute y₁ z₁ := hinj (by rw [map_mul, map_mul]; exact hyz.eq)
    have hgy₁ : Commute g₁ y₁ := hinj (by rw [map_mul, map_mul]; exact hgy.eq)
    have hy₁ : orderOf y₁ = 5 := by
      rw [← orderOf_injective _ hinj y₁]
      exact hy
    have hXne : Subgroup.zpowers y₁ ≠ ⊥ := by
      intro h
      rw [Subgroup.zpowers_eq_bot] at h
      rw [h, orderOf_one] at hy₁
      norm_num at hy₁
    have hXodd : ∀ x ∈ Subgroup.zpowers y₁, Odd (orderOf x) := by
      intro x hx
      have := orderOf_dvd_of_mem_zpowers hx
      rw [hy₁] at this
      exact Odd.of_dvd_nat (by norm_num) this
    have hXcent : Subgroup.zpowers y₁ ≤ Subgroup.centralizer ({z₁} : Set (PSL2 F)) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hyz₁.eq
    have hN := psl2_odd_centralizer_normalizer hK hz₁ (Subgroup.zpowers y₁) hXne hXodd hXcent
    have hg₁N : g₁ ∈ Subgroup.normalizer (Subgroup.zpowers y₁ : Set (PSL2 F)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        rw [show g₁ * y₁ ^ k * g₁⁻¹ = y₁ ^ k by rw [(hgy₁.zpow_right k).eq]; group]
        exact Subgroup.zpow_mem_zpowers _ _
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hc : Commute g₁ (y₁ ^ k) := hgy₁.zpow_right k
        have : h = y₁ ^ k := by
          have e : h = g₁⁻¹ * (g₁ * h * g₁⁻¹) * g₁ := by group
          rw [e, ← hk]
          calc g₁⁻¹ * y₁ ^ k * g₁ = g₁⁻¹ * (y₁ ^ k * g₁) := by group
            _ = g₁⁻¹ * (g₁ * y₁ ^ k) := by rw [hc.eq]
            _ = y₁ ^ k := by group
        rw [this]
        exact Subgroup.zpow_mem_zpowers _ _
    rw [hN, Subgroup.mem_centralizer_singleton_iff] at hg₁N
    apply hCU _ _ hgy
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg₁N]
  refine ⟨fun e he hey => ?_, ?_⟩
  ·
    have hzez : e * z * e⁻¹ = z := by
      have h1 : e * z * e⁻¹ ∈ J := hJn.conj_mem z hzJ e
      have h2 : Commute (e * z * e⁻¹) y := by
        have hey' : e * y * e⁻¹ = y := by rw [hey.eq]; group
        calc (e * z * e⁻¹) * y = (e * z * e⁻¹) * (e * y * e⁻¹) := by rw [hey']
          _ = e * (z * y) * e⁻¹ := by group
          _ = e * (y * z) * e⁻¹ := by rw [hyz.eq]
          _ = (e * y * e⁻¹) * (e * z * e⁻¹) := by group
          _ = y * (e * z * e⁻¹) := by rw [hey']
      have h3 := hCJ _ h1 h2
      refine pgl2_unique_involution_of_cyclic_subgroup U hUc hzU ?_ hz.1 h3 ?_ ?_
      · rw [← pow_two]; exact hz.2
      · rw [show e * z * e⁻¹ * (e * z * e⁻¹) = e * (z * z) * e⁻¹ by group, ← pow_two, hz.2]
        group
      · intro h
        apply hz.1
        have : z = e⁻¹ * (e * z * e⁻¹) * e := by group
        rw [this, h]
        group
    have heC : e ∈ Subgroup.centralizer ({z} : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc e * z = e * z * e⁻¹ * e := by group
        _ = z * e := by rw [hzez]
    have heU := hCU e heC hey
    by_cases he1 : e = 1
    · exact Or.inl he1
    · exact Or.inr (pgl2_unique_involution_of_cyclic_subgroup U hUc heU
        (by rw [← pow_two]; exact he) he1 hzU (by rw [← pow_two]; exact hz.2) hz.1).symm
  ·
    have hrefl : ∀ u ∈ U, (u * w) ^ 2 = 1 ∧ (u * w) * y * (u * w)⁻¹ = y⁻¹ := by
      intro u hu
      refine ⟨?_, hUw u hu y hyU⟩
      rw [pow_two]
      calc u * w * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
        _ = u * u⁻¹ * (w * w) := by rw [hwinv u hu]
        _ = 1 := by rw [hww]; group
    obtain ⟨u₁, hu₁, hu₁J⟩ := Set.not_subset.mp hUJ
    by_cases hwJ : w ∈ J
    · refine ⟨1 * w, by rwa [one_mul], hrefl 1 U.one_mem⟩
    · refine ⟨u₁ * w, ?_, hrefl u₁ hu₁⟩
      rw [Subgroup.mul_mem_iff_of_index_two hJidx]
      exact iff_of_false hu₁J hwJ

end

section

theorem conj_eq_or_eq_inv_of_sq614 {G : Type*} [Group G] {y d : G} (hy : y ^ 5 = 1)
    (hd : d ^ 2 = 1) (hdy : d ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) :
    d * y * d⁻¹ = y ∨ d * y * d⁻¹ = y⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hdy y).mp (Subgroup.mem_zpowers y))
  have hdd : d * d = 1 := by rw [← pow_two, hd]
  have h1 : y = y ^ (k * k) := by
    have e1 : y = d * (d * y * d⁻¹) * d⁻¹ := by
      calc y = (d * d) * y * (d * d)⁻¹ := by rw [hdd]; group
        _ = d * (d * y * d⁻¹) * d⁻¹ := by group
    rw [zpow_mul]
    calc y = d * (d * y * d⁻¹) * d⁻¹ := e1
      _ = d * y ^ k * d⁻¹ := by rw [hk]
      _ = (d * y * d⁻¹) ^ k := conj_zpow.symm
      _ = (y ^ k) ^ k := by rw [hk]
  have ho : orderOf y ∣ 5 := orderOf_dvd_of_pow_eq_one hy
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp ho with h | h
  · rw [orderOf_eq_one_iff] at h
    subst h
    left
    group
  · have h2 : y ^ (k * k - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← h1, mul_inv_cancel]
    rw [zpow_eq_one_iff_modEq, h] at h2
    have h3 : (5 : ℤ) ∣ (k - 1) * (k + 1) := by
      have := Int.modEq_iff_dvd.mp h2
      have e : (k - 1) * (k + 1) = -(0 - (k * k - 1)) := by ring
      rw [e]
      exact dvd_neg.mpr (by exact_mod_cast this)
    have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    rcases hp5.dvd_or_dvd h3 with h4 | h4
    · left
      rw [← hk]
      have : y ^ k = y ^ (1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq, h, Int.modEq_iff_dvd]
        have e : (1 : ℤ) - k = -(k - 1) := by ring
        rw [e]
        exact dvd_neg.mpr (by exact_mod_cast h4)
      rw [this, zpow_one]
    · right
      rw [← hk]
      have : y ^ k = y ^ (-1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq, h, Int.modEq_iff_dvd]
        have e : (-1 : ℤ) - k = -(k + 1) := by ring
        rw [e]
        exact dvd_neg.mpr (by exact_mod_cast h4)
      rw [this, zpow_neg, zpow_one]

theorem dihedral_commuting_involutions614 {m : ℕ} (hm : 1 ≤ m) :
    ∃ a b : DihedralGroup (2 ^ m), a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧
      a * b = b * a := by
  set k : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with hk
  have h2k : k + k = 0 := by
    rw [hk, ← Nat.cast_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hm]
    exact ZMod.natCast_self _
  have hk0 : k ≠ 0 := by
    rw [hk, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by positivity) h
    have : 2 ^ m ≤ 2 ^ (m - 1) := this
    have h3 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨DihedralGroup.r k, DihedralGroup.sr 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [DihedralGroup.one_def, Ne, DihedralGroup.r.injEq]
    exact hk0
  · rw [DihedralGroup.one_def]
    intro h
    cases h
  · intro h
    cases h
  · rw [pow_two, DihedralGroup.r_mul_r, h2k, DihedralGroup.one_def]
  · rw [pow_two, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.one_def]
  · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add]
    congr 1
    rw [neg_eq_iff_add_eq_zero, h2k]

variable {F : Type*} [Field F] [Finite F]

noncomputable abbrev iotaPSL614 (F : Type*) [Field F] : PSL2 F →* PGammaL2 F :=
  (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))

omit [Finite F] in
theorem iotaPSL614_injective : Function.Injective (iotaPSL614 F) :=
  SemidirectProduct.inl_injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

theorem card_le_four_of_subset614 {G : Type*} [Group G] {V : Subgroup G} {a b c d : G}
    (h : ∀ v ∈ V, v = a ∨ v = b ∨ v = c ∨ v = d) : Nat.card V ≤ 4 := by
  classical
  have hsub : (V : Set G) ⊆ ({a, b, c, d} : Finset G) := by
    intro v hv
    rcases h v hv with h | h | h | h <;> simp [h]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  calc (V : Set G).ncard ≤ ((({a, b, c, d} : Finset G) : Set G)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({a, b, c, d} : Finset G).card := Set.ncard_coe_finset _
    _ ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp

theorem card_le_four_of_isElemAbelian_pgl614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) (V : Subgroup (PGL2 F))
    (hV : V ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hVe : IsElemAbelian 2 V) : Nat.card V ≤ 4 := by
  classical
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have := hVe.1.is_comm.comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩
    exact congrArg Subtype.val this
  by_cases hVb : ∀ v ∈ V, v = 1
  · exact card_le_four_of_subset614 (a := 1) (b := 1) (c := 1) (d := 1)
      fun v hv => Or.inl (hVb v hv)
  push Not at hVb
  obtain ⟨u, huV, hu1⟩ := hVb
  have huI : BenderSuzuki.PFAppendixIII.IsInvolution u := ⟨hu1, hVe.2 u huV⟩
  obtain ⟨U, w, hUc, huU, hww, -, hwinv, hC, -⟩ :=
    pgl2_inner_involution_data614 hK hcard (hV huV) huI
  have hVC : ∀ v ∈ V, v ∈ U ⊔ Subgroup.zpowers w := by
    intro v hv
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact hVc v hv u huV
  have hA : ∀ v ∈ V, v ∈ U → v = 1 ∨ v = u := by
    intro v hv hvU
    by_cases hv1 : v = 1
    · exact Or.inl hv1
    · exact Or.inr (pgl2_unique_involution_of_cyclic_subgroup U hUc hvU
        (by rw [← pow_two]; exact hVe.2 v hv) hv1 huU (by rw [← pow_two]; exact huI.2) hu1).symm
  by_cases hB : ∀ v ∈ V, v ∈ U
  · exact card_le_four_of_subset614 (a := 1) (b := u) (c := 1) (d := 1) fun v hv => by
      rcases hA v hv (hB v hv) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  push Not at hB
  obtain ⟨b, hbV, hbU⟩ := hB
  have hbw : ∃ u₀ ∈ U, b = u₀ * w := by
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv (hVC b hbV) with h | h
    · exact absurd h hbU
    · exact h
  obtain ⟨u₀, hu₀, rfl⟩ := hbw
  refine card_le_four_of_subset614 (a := 1) (b := u) (c := u₀ * w) (d := u * (u₀ * w))
    fun v hv => ?_
  rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv (hVC v hv) with h | ⟨u₁, hu₁, rfl⟩
  · rcases hA v hv h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  ·
    have hprod : u₁ * w * (u₀ * w) ∈ U := by
      have e : u₁ * w * (u₀ * w) = u₁ * (w * u₀ * w⁻¹) * (w * w) := by group
      rw [e, hwinv u₀ hu₀, hww, mul_one]
      exact U.mul_mem hu₁ (U.inv_mem hu₀)
    have hb2 : (u₀ * w) * (u₀ * w) = 1 := by rw [← pow_two]; exact hVe.2 _ hbV
    rcases hA _ (V.mul_mem hv hbV) hprod with h' | h'
    · right; right; left
      calc u₁ * w = u₁ * w * (u₀ * w) * (u₀ * w) := by rw [mul_assoc (u₁ * w), hb2, mul_one]
        _ = u₀ * w := by rw [h', one_mul]
    · right; right; right
      calc u₁ * w = u₁ * w * (u₀ * w) * (u₀ * w) := by rw [mul_assoc (u₁ * w), hb2, mul_one]
        _ = u * (u₀ * w) := by rw [h']

theorem card_le_four_of_isElemAbelian614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F)
    (V : Subgroup (PGammaL2 F)) (hV : V ≤ pGammaL2PSLRange F) (hVe : IsElemAbelian 2 V) :
    Nat.card V ≤ 4 := by
  classical
  set ι := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hinj : Function.Injective ι := SemidirectProduct.inl_injective
  set W := V.comap ι with hW
  have hVι : V ≤ ι.range := fun v hv => by
    obtain ⟨x, rfl⟩ := hV hv
    exact ⟨_, rfl⟩
  have hWV : W.map ι = V := Subgroup.map_comap_eq_self hVι
  have hcardW : Nat.card W = Nat.card V := by
    rw [← hWV]
    exact (Subgroup.card_map_of_injective hinj).symm
  rw [← hcardW]
  refine card_le_four_of_isElemAbelian_pgl614 hK hcard W ?_ ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hV hx
    exact ⟨y, hinj hy⟩
  · apply Subtype.ext
    apply hinj
    show ι (a * b) = ι (b * a)
    rw [map_mul, map_mul]
    have := hVe.1.is_comm.comm (⟨ι a, a.2⟩ : ↥V) ⟨ι b, b.2⟩
    exact congrArg Subtype.val this
  · intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hVe.2 _ hx

theorem mem_normalizer_of_commute614 (hK : IsOddPrimePower (Nat.card F)) {y u g : PGammaL2 F}
    (hy : y ∈ pGammaL2PSLRange F) (hu : u ∈ pGammaL2PSLRange F) (hg : g ∈ pGammaL2PSLRange F)
    (hy5 : orderOf y = 5) (hu2 : orderOf u = 2) (hyu : Commute y u) (hgu : Commute g u) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) := by
  classical
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PSL2 F) := Finite.of_injective _
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F))
  set ι := iotaPSL614 F
  have hinj : Function.Injective ι := iotaPSL614_injective
  obtain ⟨y₁, rfl⟩ := hy
  obtain ⟨u₁, rfl⟩ := hu
  obtain ⟨g₁, rfl⟩ := hg
  have hu₁ : BenderSuzuki.PFAppendixIII.IsInvolution u₁ := by
    have : orderOf u₁ = 2 := by rw [← orderOf_injective _ hinj u₁]; exact hu2
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, orderOf_one] at this; norm_num at this
    · have h := pow_orderOf_eq_one u₁
      simp only [this] at h
      exact h
  have hy₁ : orderOf y₁ = 5 := by rw [← orderOf_injective _ hinj y₁]; exact hy5
  have hyu₁ : Commute y₁ u₁ := hinj (by rw [map_mul, map_mul]; exact hyu.eq)
  have hgu₁ : Commute g₁ u₁ := hinj (by rw [map_mul, map_mul]; exact hgu.eq)
  have hXne : Subgroup.zpowers y₁ ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hy₁
    norm_num at hy₁
  have hXodd : ∀ x ∈ Subgroup.zpowers y₁, Odd (orderOf x) := by
    intro x hx
    have := orderOf_dvd_of_mem_zpowers hx
    rw [hy₁] at this
    exact Odd.of_dvd_nat (by norm_num) this
  have hXcent : Subgroup.zpowers y₁ ≤ Subgroup.centralizer ({u₁} : Set (PSL2 F)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hyu₁.eq
  have hN := psl2_odd_centralizer_normalizer hK hu₁ (Subgroup.zpowers y₁) hXne hXodd hXcent
  have hg₁ : g₁ ∈ Subgroup.normalizer (Subgroup.zpowers y₁ : Set (PSL2 F)) := by
    rw [hN, Subgroup.mem_centralizer_singleton_iff]
    exact hgu₁.eq
  have := Subgroup.le_normalizer_map ι ⟨g₁, hg₁, rfl⟩
  rwa [MonoidHom.map_zpowers] at this

end

end CFSG.Quasithin.H13
