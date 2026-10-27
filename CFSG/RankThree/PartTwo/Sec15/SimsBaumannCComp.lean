module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneCComp
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

private theorem oResidual_le_iff {Y : Type*} [Group Y] (K : Subgroup Y) :
    oResidual 2 Y ≤ K ↔ ∀ x : Y, Nat.Coprime (orderOf x) 2 → x ∈ K :=
  Subgroup.closure_le K

private theorem mem_oResidual_of_coprime {Y : Type*} [Group Y] {x : Y}
    (hx : Nat.Coprime (orderOf x) 2) : x ∈ oResidual 2 Y :=
  Subgroup.subset_closure hx

private theorem oResidual_normal_aux (Y : Type*) [Group Y] : (oResidual 2 Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ?_
    have h1 : orderOf ((MulAut.conj g).toMonoidHom x) = orderOf x :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    have h2 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [h2] at h1
    show Nat.Coprime (orderOf (g * x * g⁻¹)) 2
    rw [h1]
    exact hx
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ iha

private theorem map_oResidual_le_aux {Y Y' : Type*} [Group Y] [Group Y'] (f : Y →* Y') :
    (oResidual 2 Y).map f ≤ oResidual 2 Y' := by
  rw [Subgroup.map_le_iff_le_comap, oResidual_le_iff]
  intro x hx
  rw [Subgroup.mem_comap]
  exact mem_oResidual_of_coprime (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f x) hx)

omit [Finite X] in
private theorem no_proper_normal_of_isPGroup_quotient :
    ∀ (N : Subgroup ↥(oResidual 2 X)) [N.Normal], IsPGroup 2 (↥(oResidual 2 X) ⧸ N) → N = ⊤ := by
  intro N _ hp
  have hle : oResidual 2 X ≤ N.map (oResidual 2 X).subtype := by
    rw [oResidual_le_iff]
    intro x hx
    have hxL : x ∈ oResidual 2 X := mem_oResidual_of_coprime hx
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    obtain ⟨k, hk⟩ := hp (QuotientGroup.mk ⟨x, hxL⟩)
    have h1 : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥(oResidual 2 X)) :
        ↥(oResidual 2 X) ⧸ N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥(oResidual 2 X)) :
        ↥(oResidual 2 X) ⧸ N) ∣ orderOf x := by
      rw [← Subgroup.orderOf_mk x hxL]
      exact orderOf_map_dvd (QuotientGroup.mk' N) ⟨x, hxL⟩
    have h3 : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥(oResidual 2 X)) :
        ↥(oResidual 2 X) ⧸ N) = 1 := by
      have := Nat.dvd_gcd h2 h1
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hx), Nat.dvd_one] at this
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  rw [eq_top_iff]
  intro l _
  obtain ⟨n, hn, hnl⟩ := hle l.2
  exact (Subtype.ext hnl : n = l) ▸ hn

omit [Finite X] in
private theorem exists_pow_two_pow_eq_one (x : X) (m : ℕ)
    (hx : (QuotientGroup.mk' (CFSG.pCore 2 X) x) ^ m = 1) :
    ∃ k : ℕ, (x ^ 2 ^ k) ^ m = 1 := by
  have hxm : x ^ m ∈ CFSG.pCore 2 X := by
    have h : (QuotientGroup.mk' (CFSG.pCore 2 X)) (x ^ m) = 1 := by rw [map_pow]; exact hx
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨x ^ m, hxm⟩
  refine ⟨k, ?_⟩
  have hk' : (x ^ m) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [← pow_mul, mul_comm, pow_mul]
  exact hk'

omit [Finite X] in
private theorem oResidual_quotient_le_map :
    oResidual 2 (X ⧸ CFSG.pCore 2 X) ≤
      (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
  rw [oResidual_le_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) y
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one x _
    (pow_orderOf_eq_one (QuotientGroup.mk' (CFSG.pCore 2 X) x))
  have hz : x ^ 2 ^ k ∈ oResidual 2 X :=
    mem_oResidual_of_coprime (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk) hy)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime (x := QuotientGroup.mk' (CFSG.pCore 2 X) x)
    (n := 2 ^ k) (Nat.Coprime.pow_left k hy.symm)
  refine ⟨(x ^ 2 ^ k) ^ j, Subgroup.pow_mem _ hz j, ?_⟩
  simpa only [map_pow] using hj

private theorem isQuasisimple_quotient_pCore
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) :
    CFSG.IsQuasisimple (↥(oResidual 2 X) ⧸ CFSG.pCore 2 ↥(oResidual 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn : (oResidual 2 X).Normal := oResidual_normal_aux X
  let π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X)
  let φ : ↥(oResidual 2 X) →* ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) :=
    (π.comp (oResidual 2 X).subtype).codRestrict _ fun l => map_oResidual_le_aux π ⟨l, l.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := oResidual_quotient_le_map y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφk : ∀ l : ↥(oResidual 2 X), φ l = 1 ↔ (l : X) ∈ CFSG.pCore 2 X := fun l => by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 X) (l : X), Subtype.ext_iff]
    rfl
  have hker : φ.ker = CFSG.pCore 2 ↥(oResidual 2 X) := by
    refine le_antisymm ?_ ?_
    · refine CFSG.LieType.BorelTits.le_pCore 2 inferInstance ?_
      intro g
      have hgQ : ((g : ↥(oResidual 2 X)) : X) ∈ CFSG.pCore 2 X :=
        (hφk g).mp (MonoidHom.mem_ker.mp g.2)
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X))
        ⟨((g : ↥(oResidual 2 X)) : X), hgQ⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hk
    · intro l hl
      refine MonoidHom.mem_ker.mpr ((hφk l).mpr ?_)
      have hN : (CFSG.Open.pCoreOf 2 (oResidual 2 X)).Normal := by
        have h1 : Subgroup.normalizer ((oResidual 2 X : Subgroup X) : Set X) = ⊤ :=
          Subgroup.normalizer_eq_top_iff.mpr hLn
        have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oResidual 2 X)
        rw [h1] at h2
        exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h2)
      exact CFSG.LieType.BorelTits.le_pCore 2 hN
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oResidual 2 X))
        ((CFSG.mem_openPCoreOf_iff l).mpr hl)
  exact CFSG.IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)) hq

theorem oResidual_mem_cComp (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) :
    oResidual 2 X ∈ CFSG.Quasithin.cComp ⊤ :=
  CFSG.Quasithin.H13.mem_cComp_of_quasisimple_quotient no_proper_normal_of_isPGroup_quotient
    (isQuasisimple_quotient_pCore hq)
    (CFSG.Quasithin.A3.subnormal_of_normal le_top
      (Subgroup.Normal.subgroupOf (oResidual_normal_aux X) _))

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
