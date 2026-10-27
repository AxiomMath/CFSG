module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.A4

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

variable {Y : Type*} [Group Y] [Finite Y] {f : MulAut Y}

theorem commute_of_mem_fixedFitting {x y : Y} (hx : x ∈ fixedFitting f) (hy : y ∈ fixedFitting f)
    (hxy : (orderOf x).Coprime (orderOf y)) : Commute x y := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have : Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f)) := inferInstance
  have hx2 : orderOf (⟨x', hx'⟩ : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f))) =
      orderOf (x' : Y) := by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have hy2 : orderOf (⟨y', hy'⟩ : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f))) =
      orderOf (y' : Y) := by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have hc : Commute (⟨x', hx'⟩ : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f)))
      ⟨y', hy'⟩ := Group.IsNilpotent.commute_of_orderOf_coprime (by rw [hx2, hy2]; exact hxy)
  have h := congrArg (fun z : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f)) =>
    ((z : ↥(signalizerFixedSubgroup f)) : Y)) hc.eq
  exact h

namespace IsA4Subgroup

variable (h : IsA4Subgroup (signalizerFixedSubgroup f))

include h

omit [Finite Y] in
theorem klein_le_fixedFitting : h.klein ≤ fixedFitting f := by
  have hle : h.klein ≤ signalizerFixedSubgroup f := h.klein_le
  have hnorm : (h.klein.subgroupOf (signalizerFixedSubgroup f)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.conj_mem_klein g.2 hn
  have hcomm : IsMulCommutative (h.klein.subgroupOf (signalizerFixedSubgroup f)) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (h.klein_comm a.2 b.2))⟩⟩
  have hnil : Group.IsNilpotent ↥(h.klein.subgroupOf (signalizerFixedSubgroup f)) :=
    inferInstance
  have hle' : h.klein.subgroupOf (signalizerFixedSubgroup f) ≤
      CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f) := le_sSup ⟨hnorm, hnil⟩
  intro x hx
  exact ⟨⟨x, hle hx⟩, hle' (by rwa [Subgroup.mem_subgroupOf]), rfl⟩

theorem fixedFitting_eq : fixedFitting f = h.klein := by
  refine le_antisymm ?_ h.klein_le_fixedFitting
  intro x hx
  by_contra hxK
  have hxC : x ∈ signalizerFixedSubgroup f := fixedFitting_le f hx
  have hx2 : x ^ 2 ≠ 1 := fun h2 => hxK ⟨hxC, h2⟩
  obtain ⟨v, hv, hv1⟩ := h.exists_ne_one_mem_klein
  have hcomm : Commute x v := commute_of_mem_fixedFitting hx (h.klein_le_fixedFitting hv) (by
    rw [h.orderOf_eq_three hxC hx2, h.orderOf_eq_two hv hv1]; norm_num)
  exact hv1 (h.fpf x hxC v hv.1 hx2 hv.2 hcomm.eq)

theorem fixedCore1_eq : fixedCore1 f = signalizerFixedSubgroup f := by
  refine le_antisymm (fun x hx => hx.1) fun x hx => ⟨hx, fun y hy => ?_⟩
  rw [h.fixedFitting_eq, mem_klein, commutatorElement_def]
  exact ⟨(signalizerFixedSubgroup f).mul_mem ((signalizerFixedSubgroup f).mul_mem
    ((signalizerFixedSubgroup f).mul_mem hx hy) ((signalizerFixedSubgroup f).inv_mem hx))
    ((signalizerFixedSubgroup f).inv_mem hy), h.comm_sq x hx y hy⟩

theorem fixedNormalizer_eq (hsimple : IsSimpleGroup Y)
    (hmax : ∀ H : Subgroup Y, signalizerFixedSubgroup f ≤ H → H ≠ ⊤ →
      H = signalizerFixedSubgroup f) :
    fixedNormalizer f = signalizerFixedSubgroup f := by
  have hne : fixedNormalizer f ≠ ⊤ := by
    intro htop
    have hnorm : (fixedFitting f).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rw [h.fixedFitting_eq] at hnorm
    rcases hsimple.eq_bot_or_eq_top_of_normal h.klein with h1 | h1
    · have := h.card_klein
      rw [h1, Subgroup.card_bot] at this
      omega
    · have h2 : signalizerFixedSubgroup f = ⊤ := top_le_iff.mp (h1 ▸ h.klein_le)
      have h3 := h.card
      have h4 := h.card_klein
      rw [h1, Subgroup.card_top] at h4
      rw [h2, Subgroup.card_top] at h3
      omega
  exact hmax _ (fixed_le_fixedNormalizer f) hne

theorem centralizer_fixedFitting_eq (hM : fixedNormalizer f = signalizerFixedSubgroup f) :
    Subgroup.centralizer (fixedFitting f : Set Y) = fixedFitting f := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have hxM : x ∈ fixedNormalizer f := Subgroup.centralizer_le_normalizer _ hx
    rw [hM] at hxM
    rw [h.fixedFitting_eq]
    refine ⟨hxM, h.centralizer_sq x hxM fun v hv hv2 => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hx v (by rw [h.fixedFitting_eq]; exact ⟨hv, hv2⟩)
    exact this.symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [h.fixedFitting_eq] at hx hv
    exact h.klein_comm hv hx

theorem fixedFitting_le_of_normal {N : Subgroup Y} (hNC : N ≤ signalizerFixedSubgroup f)
    (hN : (N.subgroupOf (signalizerFixedSubgroup f)).Normal) (hbot : N ≠ ⊥) :
    fixedFitting f ≤ N := by
  have hconj : ∀ x ∈ signalizerFixedSubgroup f, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mp hN hx) n).mp hn
  obtain ⟨n, hn, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall N).mpr hcon)
  have hnC := hNC hn
  obtain ⟨n', hn'N, hn'K, hn'1⟩ : ∃ n' ∈ N, n' ∈ h.klein ∧ n' ≠ 1 := by
    by_cases hnK : n ∈ h.klein
    · exact ⟨n, hn, hnK, hn1⟩
    · have hn2 : n ^ 2 ≠ 1 := fun h2 => hnK ⟨hnC, h2⟩
      obtain ⟨v, hv, hv1⟩ := h.exists_ne_one_mem_klein
      have hvC := h.klein_le hv
      refine ⟨v * n * v⁻¹ * n⁻¹, N.mul_mem (hconj v hvC n hn) (N.inv_mem hn), ?_, fun h1 => ?_⟩
      · have hK : n * v⁻¹ * n⁻¹ ∈ h.klein := h.conj_mem_klein hnC (h.klein.inv_mem hv)
        have := h.klein.mul_mem hv hK
        simpa [mul_assoc] using this
      · have hcomm : n * v = v * n := by
          have : v * n * v⁻¹ * n⁻¹ * (n * v) = v * n := by group
          rw [h1, one_mul] at this
          exact this.symm.symm ▸ this
        exact hv1 (h.fpf n hnC v hvC hn2 hv.2 hcomm)
  intro v hv
  rw [h.fixedFitting_eq] at hv
  obtain ⟨x, hxC, hx⟩ := h.normal_gen n' (h.klein_le hn'K) hn'1 v hv.1 hv.2
  rcases hx with hx | hx | hx
  · rw [hx]; exact N.one_mem
  · rw [hx]; exact hconj x hxC n' hn'N
  · rw [hx]; exact N.mul_mem (hconj x hxC n' hn'N) (N.inv_mem hn'N)

end IsA4Subgroup

theorem frame_of_isA4 {p : ℕ} (hp : p.Prime) (hf : orderOf f = p)
    (hcop : Nat.Coprime p (Nat.card Y)) (hsimple : IsSimpleGroup Y)
    (hsolv : Group.IsSolvable (signalizerFixedSubgroup f))
    (h : IsA4Subgroup (signalizerFixedSubgroup f))
    (hmax : ∀ H : Subgroup Y, signalizerFixedSubgroup f ≤ H → H ≠ ⊤ →
      H = signalizerFixedSubgroup f)
    (hsyl : ∀ S : Sylow 2 Y, Nat.card S = 4) : Frame p 2 f := by
  have hM := h.fixedNormalizer_eq hsimple hmax
  have hZ := h.centralizer_fixedFitting_eq hM
  have hFK := h.fixedFitting_eq
  refine
    { prime := hp
      prime_ℓ := Nat.prime_two
      ord := hf
      coprime := hcop
      simple := hsimple
      nonabelian := ?_
      fixed_solvable := hsolv
      C0_ne_bot := ?_
      C0_pgroup := ?_
      C0_comm := ?_
      C0_sylow := ?_
      C0_ne := ?_
      C1_ne := ?_
      minimal := fun N hNC hN hbot => h.fixedFitting_le_of_normal hNC hN hbot
      centralizer_comm := ?_
      fpf := ?_
      normalizer_le := ?_
      overgroup := ?_ }
  · obtain ⟨a, -, b, -, hab⟩ := h.nonabelian
    exact ⟨a, b, hab⟩
  · rw [hFK]
    intro hbot
    have := h.card_klein
    rw [hbot, Subgroup.card_bot] at this
    omega
  · rw [hFK]
    exact IsPGroup.of_card (n := 2) (by rw [h.card_klein]; norm_num)
  · rw [hFK]
    infer_instance
  · intro P hP hle
    rw [hFK] at hle ⊢
    obtain ⟨S, hS⟩ := hP.exists_le_sylow
    have h1 : Nat.card P ≤ 4 := (hsyl S) ▸ Subgroup.card_le_of_le hS
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_klein]; exact h1)).symm
  · rw [hFK]
    intro heq
    have h1 := h.card_klein
    rw [heq, h.card] at h1
    omega
  · rw [h.fixedCore1_eq, hFK]
    intro heq
    have h1 := h.card_klein
    rw [← heq, h.card] at h1
    omega
  · rw [hZ, hFK]
    infer_instance
  · intro v hv hvK z hz hvz
    rw [hZ, hFK] at hz
    rw [hFK] at hvK
    have hv2 : v ^ 2 ≠ 1 := fun h2 => hvK ⟨hv, h2⟩
    exact h.fpf v hv z hz.1 hv2 hz.2 hvz
  · intro x hx
    rw [hM] at hx
    exact ⟨1, Subgroup.one_mem _, x, hx, (one_mul x).symm⟩
  · intro H hCH hH
    exact (hmax H hCH hH).le.trans (fixed_le_fixedNormalizer f)

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
