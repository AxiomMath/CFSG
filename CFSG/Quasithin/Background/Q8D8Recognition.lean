module

public import CFSG.RankThree.GroupTheory.SteinbergBMExtraspecialThirtyTwoFive
public import CFSG.GH74.Uniqueness.Section15GL32
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.Quasithin.EmptyFaithful.S1421QA16Cnt
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Monster.B.Short.Extraspecial
public import CFSG.Quasithin.EmptyFaithful.S1421QA16Perf
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Q8D8Rec

theorem q8d8_pow_val_eq_one {W : Type} [Group W] {x z : W} (hzz : z * z = 1)
    (hz1 : z ≠ 1) (hx : x * x = z) {k : ZMod 4} (hk : x ^ k.val = 1) : k = 0 := by
  have hx4 : x ^ 4 = 1 := by
    rw [show x ^ 4 = (x * x) * (x * x) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq], hx, hzz]
  have hx2 : x ^ 2 ≠ 1 := by rw [sq, hx]; exact hz1
  have hord : orderOf x = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using hx2)
      (by simpa using hx4)
    simpa using h
  have hdvd : orderOf x ∣ k.val := orderOf_dvd_of_pow_eq_one hk
  rw [hord] at hdvd
  exact (ZMod.val_eq_zero k).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt k))

theorem q8d8_eq_one_of_commute {W : Type} [Group W] {x y z : W}
    (hxy : x * y = z * (y * x)) (hc : y * x = x * y) : z = 1 := by
  have h : z * (x * y) = 1 * (x * y) := by
    rw [one_mul]
    calc z * (x * y) = z * (y * x) := by rw [hc]
      _ = x * y := hxy.symm
  exact mul_right_cancel h

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices in
theorem q8d8_q8_hom {W : Type} [Group W] {z x y : W} (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hx : x * x = z) (hy : y * y = z) (hxy : x * y = z * (y * x)) :
    ∃ f : QuaternionGroup 2 →* W, Function.Injective f ∧
      (∀ k : ZMod 4, f (QuaternionGroup.a k) = x ^ k.val) ∧
      (∀ k : ZMod 4, f (QuaternionGroup.xa k) = y * x ^ k.val) := by
  have hx4 : x ^ 4 = 1 := by
    rw [show x ^ 4 = (x * x) * (x * x) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq], hx, hzz]
  have hy2 : y ^ 2 = x ^ 2 := by rw [sq, sq, hx, hy]
  have hxinv : x⁻¹ = z * x := by
    have h : z * x * x = 1 := by rw [mul_assoc, hx, hzz]
    exact (eq_inv_of_mul_eq_one_left h).symm
  have hyx' : y * x = z * (x * y) := by
    calc y * x = (z * z) * (y * x) := by rw [hzz, one_mul]
      _ = z * (z * (y * x)) := mul_assoc _ _ _
      _ = z * (x * y) := by rw [← hxy]
  have hyx : y * x * y⁻¹ = x⁻¹ := by
    rw [hxinv, hyx', mul_assoc, mul_inv_cancel_right]
  refine ⟨quaternionLift hx4 hyx hy2, ?_, fun k => rfl, fun k => rfl⟩
  · rw [injective_iff_map_eq_one]
    rintro (k | k) hk
    · have hk' : x ^ k.val = 1 := (quaternionLift_a hx4 hyx hy2 k).symm.trans hk
      rw [q8d8_pow_val_eq_one hzz hz1 hx hk']
      exact QuaternionGroup.one_def.symm
    · exfalso
      have hk' : y * x ^ k.val = 1 := (quaternionLift_xa hx4 hyx hy2 k).symm.trans hk
      have hy' : y = (x ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left hk'
      have hc : y * x = x * y := by
        rw [hy']
        exact ((Commute.pow_self x k.val).inv_left).eq
      exact hz1 (q8d8_eq_one_of_commute hxy hc)

theorem q8d8_uv_sq {W : Type} [Group W] {z u v : W} (hzz : z * z = 1)
    (hzu : z * u = u * z) (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = z * (v * u)) :
    u * v * (u * v) = z := by
  have hvu : v * u = z * (u * v) := by
    calc v * u = (z * z) * (v * u) := by rw [hzz, one_mul]
      _ = z * (z * (v * u)) := mul_assoc _ _ _
      _ = z * (u * v) := by rw [← huv]
  calc u * v * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
    _ = u * (z * (u * v)) * v := by rw [hvu]
    _ = (u * z) * (u * v) * v := by simp only [mul_assoc]
    _ = (z * u) * (u * v) * v := by rw [← hzu]
    _ = z * (u * u) * (v * v) := by simp only [mul_assoc]
    _ = z := by rw [hu, hv, mul_one, mul_one]

open CFSG.GH74.Uniqueness.Section15GL32 in
theorem q8d8_d8_hom {W : Type} [Group W] {z u v : W} (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hzu : z * u = u * z) (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = z * (v * u)) :
    ∃ f : DihedralGroup 4 →* W, Function.Injective f ∧
      (∀ k : ZMod 4, f (DihedralGroup.r k) = (u * v) ^ k.val) ∧
      (∀ k : ZMod 4, f (DihedralGroup.sr k) = u * (u * v) ^ k.val) := by
  have hr2 : u * v * (u * v) = z := q8d8_uv_sq hzz hzu hu hv huv
  have ha4 : (u * v) ^ 4 = 1 := by
    rw [show (u * v) ^ 4 = (u * v * (u * v)) * (u * v * (u * v)) by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq], hr2, hzz]
  have hba : u * (u * v) * u = (u * v)⁻¹ := by
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
    rw [mul_inv_rev, hu', hv']
    calc u * (u * v) * u = (u * u) * v * u := by simp only [mul_assoc]
      _ = v * u := by rw [hu, one_mul]
  refine ⟨dihedralLift (u * v) u ha4 hu hba, ?_, fun k => rfl, fun k => rfl⟩
  · rw [injective_iff_map_eq_one]
    rintro (k | k) hk
    · have hk' : (u * v) ^ k.val = 1 := (dihedralLift_r (u * v) u ha4 hu hba k).symm.trans hk
      rw [q8d8_pow_val_eq_one hzz hz1 hr2 hk']
      exact DihedralGroup.one_def.symm
    · exfalso
      have hk' : u * (u * v) ^ k.val = 1 :=
        (dihedralLift_sr (u * v) u ha4 hu hba k).symm.trans hk
      have hy' : u = ((u * v) ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left hk'
      have hc : Commute u (u * v) := by
        have h := (Commute.pow_self (u * v) k.val).inv_left
        rw [← hy'] at h
        exact h
      have hvu' : v * u = u * v := by
        have h1 : u * (u * v) = (u * v) * u := hc.eq
        calc v * u = (u * u) * v * u := by rw [hu, one_mul]
          _ = u * (u * v) * u := by simp only [mul_assoc]
          _ = (u * v) * u * u := by rw [h1]
          _ = u * v := by rw [mul_assoc, hu, mul_one]
      exact hz1 (q8d8_eq_one_of_commute huv hvu')

theorem q8d8_q8_central :
    ∀ q : QuaternionGroup 2, (∀ r : QuaternionGroup 2, r * q = q * r) →
      q = 1 ∨ q = QuaternionGroup.a 2 := by decide

theorem q8d8_gens {W : Type} [Group W] {z x y u v : W}
    (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hx : x * x = z) (hy : y * y = z) (hxy : x * y = z * (y * x))
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = z * (v * u))
    (hxu : x * u = u * x) (hxv : x * v = v * x) (hyu : y * u = u * y) (hyv : y * v = v * y) :
    ∃ Q E : Subgroup W, Nonempty (↥Q ≃* QuaternionGroup 2) ∧ Nonempty (↥E ≃* DihedralGroup 4) ∧
      (∀ q ∈ Q, ∀ e ∈ E, q * e = e * q) ∧ Nat.card ↥(Q ⊓ E) = 2 ∧
      x ∈ Q ∧ y ∈ Q ∧ u ∈ E ∧ v ∈ E ∧ z ∈ Q ∧ z ∈ E := by
  have hzu : z * u = u * z := by
    calc z * u = x * (x * u) := by rw [← hx, mul_assoc]
      _ = x * (u * x) := by rw [hxu]
      _ = (u * x) * x := by rw [← mul_assoc, hxu]
      _ = u * z := by rw [mul_assoc, hx]
  obtain ⟨fQ, hQinj, hfQa, hfQxa⟩ := q8d8_q8_hom hzz hz1 hx hy hxy
  obtain ⟨fD, hDinj, hfDr, hfDsr⟩ := q8d8_d8_hom hzz hz1 hzu hu hv huv
  have hr2 : u * v * (u * v) = z := q8d8_uv_sq hzz hzu hu hv huv
  have cxu : Commute x u := hxu
  have cxv : Commute x v := hxv
  have cyu : Commute y u := hyu
  have cyv : Commute y v := hyv
  have cxr : Commute x (u * v) := cxu.mul_right cxv
  have cyr : Commute y (u * v) := cyu.mul_right cyv
  have hcomm : ∀ q d, Commute (fQ q) (fD d) := by
    intro q d
    rcases q with k | k <;> rcases d with m | m
    · rw [hfQa, hfDr]
      exact cxr.pow_pow _ _
    · rw [hfQa, hfDsr]
      exact (cxu.pow_left _).mul_right (cxr.pow_pow _ _)
    · rw [hfQxa, hfDr]
      exact (cyr.pow_right _).mul_left (cxr.pow_pow _ _)
    · rw [hfQxa, hfDsr]
      exact (cyu.mul_left (cxu.pow_left _)).mul_right
        ((cyr.pow_right _).mul_left (cxr.pow_pow _ _))
  have hzQ : z ∈ fQ.range :=
    ⟨QuaternionGroup.a 2, by rw [hfQa, show (2 : ZMod 4).val = 2 from rfl, sq, hx]⟩
  have hzE : z ∈ fD.range :=
    ⟨DihedralGroup.r 2, by rw [hfDr, show (2 : ZMod 4).val = 2 from rfl, sq, hr2]⟩
  have hw : ∀ w ∈ fQ.range ⊓ fD.range, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨⟨q, rfl⟩, ⟨d, hd⟩⟩ := Subgroup.mem_inf.mp hw
    have hq : ∀ r : QuaternionGroup 2, r * q = q * r := by
      intro r
      apply hQinj
      rw [map_mul, map_mul, ← hd]
      exact (hcomm r d).eq
    rcases q8d8_q8_central q hq with rfl | rfl
    · left
      exact map_one fQ
    · right
      rw [hfQa, show (2 : ZMod 4).val = 2 from rfl, sq, hx]
  refine ⟨fQ.range, fD.range, ⟨(MonoidHom.ofInjective hQinj).symm⟩,
    ⟨(MonoidHom.ofInjective hDinj).symm⟩, ?_, ?_, ?_, ?_, ?_, ?_, hzQ, hzE⟩
  · rintro _ ⟨q, rfl⟩ _ ⟨d, rfl⟩
    exact (hcomm q d).eq
  · rw [Nat.card_eq_two_iff' (1 : ↥(fQ.range ⊓ fD.range))]
    refine ⟨⟨z, Subgroup.mem_inf.mpr ⟨hzQ, hzE⟩⟩, fun h => hz1 (congrArg Subtype.val h),
      fun w hw1 => ?_⟩
    exact Subtype.ext ((hw w.1 w.2).resolve_left fun h => hw1 (Subtype.ext h))
  · exact ⟨QuaternionGroup.a 1, by
      rw [hfQa, show (1 : ZMod 4).val = 1 from rfl, pow_one]⟩
  · exact ⟨QuaternionGroup.xa 0, by rw [hfQxa, ZMod.val_zero, pow_zero, mul_one]⟩
  · exact ⟨DihedralGroup.sr 0, by rw [hfDsr, ZMod.val_zero, pow_zero, mul_one]⟩
  · refine ⟨DihedralGroup.sr 1, ?_⟩
    rw [hfDsr, show (1 : ZMod 4).val = 1 from rfl, pow_one]
    calc u * (u * v) = (u * u) * v := by rw [mul_assoc]
      _ = v := by rw [hu, one_mul]

theorem q8d8_center_two {S : Type} [Group S] (h : Nat.card (Subgroup.center S)
    = 2) :
    ∃ z : S, z ≠ 1 ∧ Subgroup.center S = Subgroup.zpowers z ∧
      ∀ w ∈ Subgroup.center S, w = 1 ∨ w = z := by
  obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center S))).mp h
  have hw : ∀ w ∈ Subgroup.center S, w = 1 ∨ w = (y : S) := by
    intro w hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · right
      exact congrArg Subtype.val (hyu ⟨w, hw⟩ (fun h' => hw1 (congrArg Subtype.val h')))
  refine ⟨(y : S), fun h' => hy1 (Subtype.ext h'), ?_, hw⟩
  apply le_antisymm
  · intro w hwc
    rcases hw w hwc with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr y.2

theorem q8d8_card_inf_centralizer {Bg : Type} [Group Bg] [Finite Bg] (V :
    Subgroup Bg)
    [V.Normal] (hcard : Nat.card ↥V = 32) (hS : CFSG.IsExtraspecialPGroup 2 ↥V)
    (hs : IsSimpleGroup (Bg ⧸ V)) (hperf : commutator Bg = ⊤) {c : Bg} (hc5 : c ^ 5 = 1)
    (hcV : c ∉ V) {z : ↥V} (hz1 : z ≠ 1) (hz : Subgroup.center ↥V = Subgroup.zpowers z)
    (hZ : ∀ w ∈ Subgroup.center ↥V, w = 1 ∨ w = z) :
    (∀ s : ↥V, c * (s : Bg) * c⁻¹ = (s : Bg) → s ∈ Subgroup.center ↥V) ∧
      ∀ w ∈ Subgroup.center ↥V, c * (w : Bg) * c⁻¹ = (w : Bg) := by
  have hzc : z ∈ Subgroup.center ↥V := hz ▸ Subgroup.mem_zpowers z
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 5) (hcard.trans (by norm_num))
  have hcn : c ∈ Subgroup.normalizer (V : Set Bg) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top c
  have hmod := CFSG.Quasithin.Q16.card_modEq_card_inf_centralizer (p := 5) (n := 1) V hcn
    (by simpa using hc5)
  rw [hcard] at hmod
  have hzfix : c * (z : Bg) * c⁻¹ = (z : Bg) := by
    let α : MulAut ↥V := MulAut.conjNormal c
    have hαz : α z ∈ Subgroup.center ↥V := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := α.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc g']
    have hα1 : α z ≠ 1 := fun h => hz1 (α.injective (h.trans (map_one α).symm))
    have : α z = z := (hZ _ hαz).resolve_left hα1
    have h2 := congrArg Subtype.val this
    rwa [MulAut.conjNormal_apply] at h2
  have hz2 : orderOf (z : Bg) = 2 := by
    have hzo : orderOf z = 2 := by
      have hcz : Nat.card (Subgroup.center ↥V) = 2 := hS.natCard_center
      have hdvd : orderOf z ∣ 2 := hcz ▸ (Subgroup.orderOf_mk (z : ↥V) hzc ▸ orderOf_dvd_natCard
        (⟨z, hzc⟩ : ↥(Subgroup.center ↥V)))
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    rw [Subgroup.orderOf_coe, hzo]
  have hZle : Subgroup.zpowers (z : Bg) ≤ V ⊓ Subgroup.centralizer ({c} : Set Bg) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (z : Bg) * c = c * (z : Bg) * c⁻¹ * c := by rw [hzfix]
      _ = c * z := by group
  have hdvd : Nat.card ↥(V ⊓ Subgroup.centralizer ({c} : Set Bg)) ∣ 32 :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2dvd : 2 ∣ Nat.card ↥(V ⊓ Subgroup.centralizer ({c} : Set Bg)) := by
    have := Subgroup.card_dvd_of_le hZle
    rwa [Nat.card_zpowers, hz2] at this
  have hwfix : ∀ w ∈ Subgroup.center ↥V, c * (w : Bg) * c⁻¹ = (w : Bg) := by
    intro w hw
    rcases hZ w hw with rfl | rfl
    · simp
    · exact hzfix
  refine ⟨?_, hwfix⟩
  rcases CFSG.Quasithin.Q16.eq_two_or_eq_thirtyTwo_of_modEq_five hdvd h2dvd hmod with h | h
  · intro s hs'
    have hsC : (s : Bg) ∈ V ⊓ Subgroup.centralizer ({c} : Set Bg) := by
      refine Subgroup.mem_inf.mpr ⟨s.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (s : Bg) * c = c * s * c⁻¹ * c := by rw [hs']
        _ = c * s := by group
    have hEq : Subgroup.zpowers (z : Bg) = V ⊓ Subgroup.centralizer ({c} : Set Bg) :=
      Subgroup.eq_of_le_of_card_ge hZle (by rw [Nat.card_zpowers, hz2, h])
    rw [← hEq] at hsC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsC
    rw [hz]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow]
    exact hk
  · exfalso
    have hVC : V ⊓ Subgroup.centralizer ({c} : Set Bg) = V :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, h])
    have hVle : V ≤ Subgroup.centralizer ({c} : Set Bg) := inf_eq_left.mp hVC
    have hcc : c ∈ Subgroup.centralizer (V : Set Bg) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      exact Subgroup.mem_centralizer_singleton_iff.mp (hVle hh')
    have htop := CFSG.Quasithin.Q16.centralizer_eq_top_of_perfect V hV2 hs hperf hcV hcc
    have hcen : Subgroup.center ↥V = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_center_iff]
      intro g'
      have hg : (g : Bg) ∈ Subgroup.centralizer (V : Set Bg) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg g' g'.2)
    have h32 := hS.natCard_center
    rw [hcen, Subgroup.card_top, hcard] at h32
    omega

theorem q8d8_closure_top {S : Type} [Group S] {x y u v z : S}
    (hzK : z ∈ Subgroup.closure ({x, y, u, v} : Set S))
    (hZ : ∀ w ∈ Subgroup.center S, w = 1 ∨ w = z)
    (hbij : Function.Bijective (fun c : Fin 4 → ZMod 2 =>
      ((x ^ (c 0).val * y ^ (c 1).val * u ^ (c 2).val * v ^ (c 3).val : S) :
        S ⧸ Subgroup.center S))) :
    Subgroup.closure ({x, y, u, v} : Set S) = ⊤ := by
  set K := Subgroup.closure ({x, y, u, v} : Set S)
  have hxK : x ∈ K := Subgroup.subset_closure (by simp)
  have hyK : y ∈ K := Subgroup.subset_closure (by simp)
  have huK : u ∈ K := Subgroup.subset_closure (by simp)
  have hvK : v ∈ K := Subgroup.subset_closure (by simp)
  rw [eq_top_iff]
  intro s _
  obtain ⟨c, hc⟩ := hbij.2 (s : S ⧸ Subgroup.center S)
  set p := x ^ (c 0).val * y ^ (c 1).val * u ^ (c 2).val * v ^ (c 3).val
  have hpK : p ∈ K := mul_mem (mul_mem (mul_mem (pow_mem hxK _) (pow_mem hyK _))
    (pow_mem huK _)) (pow_mem hvK _)
  have hw : p⁻¹ * s ∈ Subgroup.center S := QuotientGroup.eq.mp hc
  have hs : s = p * (p⁻¹ * s) := by group
  rw [hs]
  refine mul_mem hpK ?_
  rcases hZ _ hw with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact hzK

open scoped commutatorElement in
theorem q8d8_isQ8D8 {Bg : Type} [Group Bg] [Finite Bg] (V : Subgroup Bg) [V.Normal]
    (hV : CFSG.Quasithin.IsExtraspecial2 2 ↥V) (hA : CFSG.Quasithin.IsAlt 5 (Bg ⧸ V))
    (hperf : commutator Bg = ⊤) :
    ∃ Q E : Subgroup ↥V, Nonempty (↥Q ≃* QuaternionGroup 2) ∧ Nonempty (↥E ≃* DihedralGroup 4) ∧
      (∀ q ∈ Q, ∀ e ∈ E, q * e = e * q) ∧ Q ⊔ E = ⊤ ∧ Nat.card ↥(Q ⊓ E) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hVe, hVc⟩ := hV
  have hcard : Nat.card ↥V = 32 := by rw [hVc]; norm_num
  have hS : CFSG.IsExtraspecialPGroup 2 ↥V := CFSG.isExtraspecialPGroup_iff_isExtraspecial.mpr hVe
  have hs : IsSimpleGroup (Bg ⧸ V) := by
    obtain ⟨e⟩ := hA
    exact e.isSimpleGroup
  obtain ⟨z, hz1, hz, hZ⟩ := q8d8_center_two hS.natCard_center
  have hzc : z ∈ Subgroup.center ↥V := hz ▸ Subgroup.mem_zpowers z
  obtain ⟨hz2, -⟩ := CFSG.RankThree.GroupTheory.extraspecial_commutator_eq_one_or hS hz
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have h5 : 5 ∣ Nat.card Bg := by
    have h60 : Nat.card (Bg ⧸ V) = 60 := CFSG.Quasithin.A314.card_isAlt_five hA
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [h60, hcard] at h
    exact ⟨384, by omega⟩
  obtain ⟨c, hc5⟩ := exists_prime_orderOf_dvd_card' (G := Bg) 5 h5
  have hc : c ^ 5 = 1 := hc5 ▸ pow_orderOf_eq_one c
  have hcV : c ∉ V := fun h => by
    have := orderOf_dvd_natCard (⟨c, h⟩ : ↥V)
    rw [Subgroup.orderOf_mk, hc5, hcard] at this
    omega
  obtain ⟨hCV, hwfix⟩ := q8d8_card_inf_centralizer V hcard hS hs hperf hc hcV hz1 hz hZ
  let α : MulAut ↥V := MulAut.conjNormal c
  have hαapp : ∀ s : ↥V, ((α s : ↥V) : Bg) = c * (s : Bg) * c⁻¹ := fun s =>
    MulAut.conjNormal_apply c s
  have hαfix : ∀ s : ↥V, α s = s → s ∈ Subgroup.center ↥V := fun s h =>
    hCV s (by rw [← hαapp, h])
  have hαz : α z = z := Subtype.ext (by rw [hαapp]; exact hwfix z hzc)
  have hα5 : α ^ 5 = 1 := by
    rw [← map_pow, hc, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    have hcen : Subgroup.center ↥V = ⊤ := by
      rw [eq_top_iff]
      intro s _
      exact hαfix s (by rw [h]; rfl)
    have h32 := hS.natCard_center
    rw [hcen, Subgroup.card_top, hcard] at h32
    omega
  have hα : orderOf α = 5 := orderOf_eq_prime hα5 hα1
  have hfix : ∀ s : ↥V, ((α s : ↥V) : ↥V ⧸ Subgroup.center ↥V) = (s : ↥V ⧸ Subgroup.center ↥V) →
      s ∈ Subgroup.center ↥V := by
    intro s hsq
    have hw : (α s)⁻¹ * s ∈ Subgroup.center ↥V := QuotientGroup.eq.mp hsq
    rcases hZ _ hw with h1 | h1
    · apply hαfix
      exact inv_mul_eq_one.mp h1
    · exfalso
      have hαs : α s = s * z := by
        have h2 : s = α s * z := by
          calc s = α s * ((α s)⁻¹ * s) := by group
            _ = α s * z := by rw [h1]
        calc α s = α s * z * z := by rw [mul_assoc, hzz, mul_one]
          _ = s * z := by rw [← h2]
      have hpow : ∀ n : ℕ, (α ^ n) s = s * z ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', MulAut.mul_apply, ih, map_mul, hαs, map_pow, hαz, mul_assoc, ← pow_succ']
      have h5s := hpow 5
      rw [hα5, MulAut.one_apply] at h5s
      have hz5 : z ^ 5 = z := by
        calc z ^ 5 = (z * z) * (z * z) * z := by
              rw [show (5 : ℕ) = 2 + 2 + 1 from rfl, pow_succ, pow_add, sq]
          _ = z := by rw [hzz, one_mul, one_mul]
      rw [hz5] at h5s
      have : z = 1 := by
        have h3 : s * z = s * 1 := by rw [mul_one, ← h5s]
        exact mul_left_cancel h3
      exact hz1 this
  obtain ⟨-, x, y, u, v, hbij, hx2, hy2, hu2, hv2, hxy, huv, hxu, hxv, hyu, hyv, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.extraspecial_thirty_two_five_recognition hS hcard hz α
      hα hfix
  have hgen : Subgroup.closure ({x, y, u, v} : Set ↥V) = ⊤ :=
    q8d8_closure_top (by
      rw [← hx2]
      exact pow_mem (Subgroup.subset_closure (by simp)) 2) hZ hbij
  have hxx : x * x = z := by rw [← sq, hx2]
  have hyy : y * y = z := by rw [← sq, hy2]
  have huu : u * u = 1 := by rw [← sq, hu2]
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hcom : ∀ a b : ↥V, ⁅a, b⁆ = z → a * b = z * (b * a) := fun a b h => by
    calc a * b = ⁅a, b⁆ * (b * a) := by rw [commutatorElement_def]; group
      _ = z * (b * a) := by rw [h]
  obtain ⟨Q, E, hQ, hE, hQE, hn, hxQ, hyQ, huE, hvE, -, -⟩ := q8d8_gens hzz hz1 hxx hyy
    (hcom x y hxy) huu hvv (hcom u v huv)
    (commutatorElement_eq_one_iff_mul_comm.mp hxu) (commutatorElement_eq_one_iff_mul_comm.mp hxv)
    (commutatorElement_eq_one_iff_mul_comm.mp hyu) (commutatorElement_eq_one_iff_mul_comm.mp hyv)
  refine ⟨Q, E, hQ, hE, hQE, ?_, hn⟩
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro w (rfl | rfl | rfl | rfl)
  · exact Subgroup.mem_sup_left hxQ
  · exact Subgroup.mem_sup_left hyQ
  · exact Subgroup.mem_sup_right huE
  · exact Subgroup.mem_sup_right hvE

theorem isQ8D8_of_perfect_alt5 {X : Type} [Group X] [Finite X] (V : Subgroup X) [V.Normal]
    (hV : CFSG.Quasithin.IsExtraspecial2 2 ↥V) (hA : CFSG.Quasithin.IsAlt 5 (X ⧸ V))
    (hperf : commutator X = ⊤) : CFSG.Quasithin.IsQ8D8 ↥V := by
  obtain ⟨Q, E, hQ, hE, hQE, hsup, -⟩ := q8d8_isQ8D8 V hV hA hperf
  refine ⟨by rw [hV.2]; norm_num, Q, E, ⟨fun q hq => Subgroup.mem_centralizer_iff.mpr
    fun e he => (hQE q hq e he).symm, hsup⟩, hQ, hE⟩

end CFSG.Quasithin.Q8D8Rec
