module

public import CFSG.GroupTheory.PCore.CharacteristicQuotient
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance

public section

namespace CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof

open CFSG

theorem isCharacteristicP_of_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ} (e : A ≃* B)
    (h : IsCharacteristicP p A) : IsCharacteristicP p B := by
  unfold IsCharacteristicP at h ⊢
  intro b hb
  rw [← pCore_map_iso p e] at hb ⊢
  refine ⟨e.symm b, h ?_, by simp⟩
  rw [Subgroup.mem_centralizer_iff] at hb ⊢
  intro a ha
  have h1 := hb (e a) ⟨a, ha, rfl⟩
  apply e.injective
  simpa using h1

theorem isCharacteristicP_of_normal {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : IsCharacteristicP p H) (N : Subgroup H) (hN : N.Normal) : IsCharacteristicP p N := by
  have h1 : Subgroup.centralizer (Open.pCore p H : Set H) ≤ Open.pCore p H := by
    exact hH
  have h2 := RankThreeCoreUniqueness.Helpers.normal_subgroup_self_centralizing_pCore p hp h1 N hN
  change Subgroup.centralizer (pCore p N : Set N) ≤ pCore p N
  exact h2

theorem isCharacteristicP_of_surjective {C D : Type*} [Group C] [Group D] {p : ℕ}
    (f : C →* D) (hf : Function.Surjective f) (hker : IsPGroup p f.ker)
    (hD : IsCharacteristicP p D) : IsCharacteristicP p C := by
  unfold IsCharacteristicP at hD ⊢
  have hpre : (pCore p D).comap f ≤ pCore p C :=
    le_sSup ⟨Subgroup.Normal.comap inferInstance f,
      IsPGroup.comap_of_ker_isPGroup pCore_isPGroup f hker⟩
  have hmap : pCore p D ≤ (pCore p C).map f := by
    intro d hd
    obtain ⟨c, rfl⟩ := hf d
    exact ⟨c, hpre hd, rfl⟩
  intro x hx
  apply hpre
  rw [Subgroup.mem_comap]
  apply hD
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  obtain ⟨q, hq, rfl⟩ := hmap hd
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx q hq]

theorem inf_centralizer_le_of_isCharacteristicP {X : Type*} [Group X] {p : ℕ} {H : Subgroup X}
    (h : IsCharacteristicP p H) :
    H ⊓ Subgroup.centralizer (inSubgroup (pCore p) H : Set X) ≤ inSubgroup (pCore p) H := by
  rintro g ⟨hgH, hgC⟩
  have hmem : (⟨g, hgH⟩ : H) ∈ Subgroup.centralizer (pCore p H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC _ ⟨y, hy, rfl⟩)
  exact ⟨_, h hmem, rfl⟩

theorem map_centralizer_subgroupOf {X : Type*} [Group X] {H Q : Subgroup X} (hQH : Q ≤ H) :
    (Subgroup.centralizer ((Q.subgroupOf H : Subgroup H) : Set H)).map H.subtype =
      Subgroup.centralizer (Q : Set X) ⊓ H := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun q hq => ?_, x.2⟩
    have := Subgroup.mem_centralizer_iff.mp hx ⟨q, hQH hq⟩ (Subgroup.mem_subgroupOf.mpr hq)
    exact congrArg Subtype.val this
  · rintro ⟨hg, hgH⟩
    refine ⟨⟨g, hgH⟩, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg q (Subgroup.mem_subgroupOf.mp hq))

theorem isCharacteristicP_centralizer_inf {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {H Q : Subgroup X} (hH : IsCharacteristicP p H) (hQH : Q ≤ H)
    (hQ : IsPGroup p Q) :
    IsCharacteristicP p ↥(Subgroup.centralizer (Q : Set X) ⊓ H) := by
  have hQ' : IsPGroup p (Q.subgroupOf H) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have h := isCharacteristicP_centralizer H p hH (Q.subgroupOf H) hQ'
  refine isCharacteristicP_of_mulEquiv ?_ h
  exact ((Subgroup.centralizer ((Q.subgroupOf H : Subgroup H) : Set H)).equivMapOfInjective
    H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr (map_centralizer_subgroupOf hQH))

theorem isCharacteristicP_centralizer_of_surjective {X Xb : Type*} [Group X] [Group Xb]
    [Finite X] {p : ℕ} [hp : Fact p.Prime] (π : X →* Xb) (hπ : Function.Surjective π)
    (hkerZ : π.ker ≤ Subgroup.center X) (hkerp : IsPGroup p π.ker)
    (hXb : ∀ z : Xb, orderOf z = p → IsCharacteristicP p ↥(Subgroup.centralizer ({z} : Set Xb)))
    {Y : Subgroup X} (hY : CFSG.Assembly.IsElemAbelian p Y) (hYK : ¬ Y ≤ π.ker) :
    IsCharacteristicP p ↥(Subgroup.centralizer (Y : Set X)) := by
  have : Finite Xb := Finite.of_surjective π hπ
  obtain ⟨y, hyY, hyK⟩ := Set.not_subset.mp hYK
  set z := π y with hz
  have hz1 : z ≠ 1 := fun h => hyK (MonoidHom.mem_ker.mpr h)
  have hzp : orderOf z = p := by
    refine orderOf_eq_prime ?_ hz1
    rw [hz, ← map_pow, hY.2 y hyY, map_one]
  set Yb := Y.map π with hYb
  have hYbp : IsPGroup p Yb := by
    refine IsPGroup.map (fun g => ⟨1, ?_⟩) π
    exact Subtype.ext (by simpa using hY.2 g g.2)
  have hYbH : Yb ≤ Subgroup.centralizer ({z} : Set Xb) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hz, ← map_mul, ← map_mul]
    exact congrArg π (congrArg Subtype.val (hY.1.is_comm.comm ⟨w, hw⟩ ⟨y, hyY⟩))
  set Cb := Subgroup.centralizer (Yb : Set Xb) ⊓ Subgroup.centralizer ({z} : Set Xb) with hCb
  have hCbchar : IsCharacteristicP p Cb := isCharacteristicP_centralizer_inf (hXb z hzp) hYbH hYbp
  set C := Subgroup.centralizer (Y : Set X) with hC
  have hkerC : π.ker ≤ C := fun k hk =>
    Subgroup.mem_centralizer_iff.mpr fun w _ => (Subgroup.mem_center_iff.mp (hkerZ hk) w)
  have hDle : C.map π ≤ Cb := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc w hw]
    · rw [hz, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc y hyY]
  have hDnorm : ((C.map π).subgroupOf Cb).Normal := by
    refine ⟨fun d hd g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    obtain ⟨c, hc, hcd⟩ := hd
    obtain ⟨x, hx⟩ := hπ (g : Xb)
    refine ⟨x * c * x⁻¹, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_, ?_⟩
    ·
      have hgw : π (x⁻¹ * w * x) = π w := by
        rw [map_mul, map_mul, map_inv, hx]
        have h1 := Subgroup.mem_centralizer_iff.mp g.2.1 (π w) ⟨w, hw, rfl⟩
        calc (g : Xb)⁻¹ * π w * g = (g : Xb)⁻¹ * (g * π w) := by rw [mul_assoc, h1]
          _ = π w := by group
      set k := w⁻¹ * (x⁻¹ * w * x) with hk
      have hkK : k ∈ π.ker := by
        rw [MonoidHom.mem_ker, hk, map_mul, hgw, map_inv, inv_mul_cancel]
      have hkc : c * k = k * c := Subgroup.mem_center_iff.mp (hkerZ hkK) c
      have hwc : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc w hw).symm
      have hxw : x⁻¹ * w * x = w * k := by rw [hk]; group
      have key : c * (x⁻¹ * w * x) * c⁻¹ = x⁻¹ * w * x := by
        rw [hxw]
        calc c * (w * k) * c⁻¹ = (c * w) * k * c⁻¹ := by group
          _ = (w * c) * k * c⁻¹ := by rw [hwc]
          _ = w * (c * k) * c⁻¹ := by group
          _ = w * (k * c) * c⁻¹ := by rw [hkc]
          _ = w * k := by group
      calc w * (x * c * x⁻¹) = x * (x⁻¹ * w * x) * c * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * w * x) * c⁻¹) * c * x⁻¹ := by rw [key]
        _ = x * c * x⁻¹ * w := by group
    · rw [map_mul, map_mul, map_inv, hx, hcd]
      rfl
  have hDchar : IsCharacteristicP p ↥((C.map π).subgroupOf Cb) :=
    isCharacteristicP_of_normal hp.out hCbchar _ hDnorm
  have hDchar' : IsCharacteristicP p ↥(C.map π) :=
    isCharacteristicP_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDle) hDchar
  set f : C →* C.map π := (π.comp C.subtype).codRestrict (C.map π) fun c => ⟨c, c.2, rfl⟩
    with hf
  have hfapp : ∀ c : C, ((f c : C.map π) : Xb) = π c := fun c => rfl
  have hfsurj : Function.Surjective f := by
    rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, Subtype.ext (hfapp ⟨c, hc⟩)⟩
  have hfker : IsPGroup p f.ker := by
    intro k
    have hk1 : π ((k : C) : X) = 1 := by
      rw [← hfapp]
      have h1 : f k = 1 := k.2
      rw [h1]
      rfl
    obtain ⟨n, hn⟩ := hkerp ⟨((k : C) : X), hk1⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h2 := congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2 ⊢
    exact h2
  exact isCharacteristicP_of_surjective f hfsurj hfker hDchar'

end CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof
