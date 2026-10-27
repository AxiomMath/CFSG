module

public import CFSG.Quasithin.H13.J4Cover
public import CFSG.Monster.B.TwoA.Fischer.M22Aut

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.ComponentClassification.OuterAutomorphisms

theorem conjNormal_map_ZC
    (g : QW) :
    ZC.map (MulAut.conjNormal (H := CQ) g).toMonoidHom = ZC := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_ZC_iff] at hc
    rw [mem_ZC_iff]
    exact Zq_normal.conj_mem _ hc g
  · intro c hc
    refine ⟨MulAut.conjNormal (H := CQ) g⁻¹ c, ?_, ?_⟩
    · rw [mem_ZC_iff] at hc
      rw [SetLike.mem_coe, mem_ZC_iff]
      exact Zq_normal.conj_mem _ hc g⁻¹
    · apply Subtype.ext
      show g * (g⁻¹ * (c : QW) * g⁻¹⁻¹) * g⁻¹ = c
      group

@[expose] def conjCmodZ
    (g : QW) : MulAut (CQ ⧸ ZC) :=
  QuotientGroup.congr ZC ZC (MulAut.conjNormal (H := CQ) g) (conjNormal_map_ZC g)

theorem conjCmodZ_mk
    (g : QW) (c : CQ) :
    conjCmodZ g (QuotientGroup.mk c) =
      QuotientGroup.mk (⟨g * c * g⁻¹, CQ_normal.conj_mem _ c.2 g⟩ : CQ) := rfl

@[expose] def conjHom
    : QW →* MulAut (CQ ⧸ ZC) where
  toFun := conjCmodZ
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H c =>
      rw [conjCmodZ_mk]
      congr 1
      apply Subtype.ext
      show 1 * (c : QW) * 1⁻¹ = c
      group
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H c =>
      rw [MulAut.mul_apply, conjCmodZ_mk, conjCmodZ_mk, conjCmodZ_mk]
      congr 1
      apply Subtype.ext
      show g * h * (c : QW) * (g * h)⁻¹ = g * (h * c * h⁻¹) * g⁻¹
      group

@[expose] def qToAut
    : QW →* MulAut ↥CFSG.Blueprint.NativeSporadic.M22 :=
  (MulAut.congr m22EquivC.symm).toMonoidHom.comp conjHom

theorem conjHom_of_mem
    (c : CQ) : conjHom c = MulAut.conj (QuotientGroup.mk c) := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H d =>
    show conjCmodZ c _ = _
    rw [conjCmodZ_mk]
    rfl

theorem qToAut_of_mem
    (c : CQ) :
    qToAut c = MulAut.conj (m22EquivC.symm (QuotientGroup.mk c)) := by
  rw [qToAut, MonoidHom.comp_apply, conjHom_of_mem]
  exact congr_conj m22EquivC.symm _

theorem map_qToAut_CQ
    : CQ.map qToAut = inner ↥CFSG.Blueprint.NativeSporadic.M22 := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [show qToAut g = qToAut (⟨g, hg⟩ : CQ) from rfl, qToAut_of_mem]
    exact ⟨_, rfl⟩
  · rintro _ ⟨m, rfl⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (m22EquivC m)
    refine ⟨c, c.2, ?_⟩
    rw [show qToAut (c : QW) = qToAut c from rfl, qToAut_of_mem, hc, MulEquiv.symm_apply_apply]

theorem not_mem_CQ_of_mul
    {c : CQ} {g : QW} (hg : g ∉ CQ) : (c : QW)⁻¹ * g ∉ CQ := by
  intro h
  apply hg
  have : g = c * ((c : QW)⁻¹ * g) := by group
  rw [this]
  exact CQ.mul_mem c.2 h

theorem centralizes_of_conjHom_eq_one
    {g : QW} (hg : conjHom g = 1) (d : CQ) :
    g * d * g⁻¹ = d := by
  have hZ : ∀ d : CQ, ((d : QW)⁻¹ * (g * d * g⁻¹)) ∈ Zq := by
    intro d
    have h1 : conjCmodZ g (QuotientGroup.mk d) = QuotientGroup.mk d :=
      congrArg (fun f : MulAut (CQ ⧸ ZC) => f (QuotientGroup.mk d)) hg
    rw [conjCmodZ_mk, QuotientGroup.eq, mem_ZC_iff] at h1
    have h2 := Zq.inv_mem h1
    have e : ((((⟨g * d * g⁻¹, CQ_normal.conj_mem _ d.2 g⟩ : CQ)⁻¹ * d : CQ) : QW))⁻¹ =
        (d : QW)⁻¹ * (g * d * g⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    rw [e] at h2
    exact h2
  let φ : CQ →* CQ :=
    { toFun := fun d => ⟨(d : QW)⁻¹ * (g * d * g⁻¹), Zq_le_CQ (hZ d)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc : Commute ((a : QW)⁻¹ * (g * a * g⁻¹)) (b : QW)⁻¹ :=
          Subgroup.mem_centralizer_iff.1 (CQ.inv_mem b.2) _ (hZ a)
        show ((a : QW) * b)⁻¹ * (g * (a * b) * g⁻¹) =
          (a : QW)⁻¹ * (g * a * g⁻¹) * ((b : QW)⁻¹ * (g * b * g⁻¹))
        calc ((a : QW) * b)⁻¹ * (g * (a * b) * g⁻¹)
            = (b : QW)⁻¹ * ((a : QW)⁻¹ * (g * a * g⁻¹)) * (g * b * g⁻¹) := by group
          _ = ((a : QW)⁻¹ * (g * a * g⁻¹)) * (b : QW)⁻¹ * (g * b * g⁻¹) := by rw [← hc.eq]
          _ = (a : QW)⁻¹ * (g * a * g⁻¹) * ((b : QW)⁻¹ * (g * b * g⁻¹)) := by group }
  have hcentral : ∀ d, φ d ∈ Subgroup.center CQ := fun d => ZC_le_center (mem_ZC_iff.2 (hZ d))
  have hker : commutator CQ ≤ φ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.1 (hcentral b) (φ a)
  have h1 : φ d = 1 := by
    have : d ∈ φ.ker := hker (commutator_CQ ▸ Subgroup.mem_top d)
    exact this
  have h2 := congrArg Subtype.val h1
  change (d : QW)⁻¹ * (g * d * g⁻¹) = 1 at h2
  rw [inv_mul_eq_one] at h2
  exact h2.symm

theorem not_inner_of_not_mem
    {g : QW} (hg : g ∉ CQ) :
    qToAut g ∉ inner ↥CFSG.Blueprint.NativeSporadic.M22 := by
  rintro ⟨m, hm⟩
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (m22EquivC m)
  have hcm : qToAut (c : QW) = MulAut.conj m := by
    rw [show qToAut (c : QW) = qToAut c from rfl, qToAut_of_mem, hc, MulEquiv.symm_apply_apply]
  have h1 : qToAut ((c : QW)⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hcm, ← hm, inv_mul_cancel]
  have h2 : conjHom ((c : QW)⁻¹ * g) = 1 := by
    apply (MulAut.congr m22EquivC.symm).injective
    rw [map_one]
    exact h1
  have hz := centralizes_of_conjHom_eq_one h2 zC
  apply not_mem_CQ_of_mul (c := c) hg
  rw [mem_CQ_iff]
  calc (c : QW)⁻¹ * g * zq = (c : QW)⁻¹ * g * zq * ((c : QW)⁻¹ * g)⁻¹ * ((c : QW)⁻¹ * g) := by
        group
    _ = zq * ((c : QW)⁻¹ * g) := by rw [show zq = (zC : QW) from rfl, hz]

theorem card_inner_M22
    : Nat.card (inner ↥CFSG.Blueprint.NativeSporadic.M22) = 443520 := by
  obtain ⟨h1, h2, -⟩ := CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (inner ↥CFSG.Blueprint.NativeSporadic.M22)
  rw [h1] at h
  have h2' : Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M22 ⧸
      inner ↥CFSG.Blueprint.NativeSporadic.M22) = 2 := h2
  rw [h2'] at h
  omega

theorem qToAut_surjective
    : Function.Surjective qToAut := by
  obtain ⟨h1, -, -⟩ := CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order
  rw [← MonoidHom.range_eq_top]
  have hle : inner ↥CFSG.Blueprint.NativeSporadic.M22 ≤ qToAut.range := by
    rw [← map_qToAut_CQ]
    exact Subgroup.map_le_range _ _
  have hlt : inner ↥CFSG.Blueprint.NativeSporadic.M22 < qToAut.range :=
    lt_of_le_of_ne hle fun h => not_inner_of_not_mem Uq_not_mem_CQ (h ▸ ⟨Uq, rfl⟩)
  have hfin : Finite (MulAut ↥CFSG.Blueprint.NativeSporadic.M22) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
  have hdvd : Nat.card (inner ↥CFSG.Blueprint.NativeSporadic.M22) ∣ Nat.card qToAut.range :=
    Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card qToAut.range ∣ 887040 := h1 ▸ Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card (inner ↥CFSG.Blueprint.NativeSporadic.M22) ≠ Nat.card qToAut.range :=
    fun e => (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge hle e.symm.le)
  rw [card_inner_M22] at hdvd hne
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : k = 2 := by
    obtain ⟨j, hj⟩ := hdvd2
    rw [hk] at hj
    have : k * j = 2 := by
      have h887 : (887040 : ℕ) = 443520 * 2 := by norm_num
      rw [h887, mul_assoc] at hj
      exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hj).symm
    rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro j this) with h | h
    · rw [h, mul_one] at hk; exact absurd hk.symm hne
    · exact h
  apply Subgroup.eq_top_of_card_eq
  rw [h1, hk, hk2]

theorem ker_qToAut
    : qToAut.ker = Zq := by
  obtain ⟨h1, -, -⟩ := CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order
  have hZle : Zq ≤ qToAut.ker := by
    intro g hg
    have hgC : g ∈ CQ := Zq_le_CQ hg
    rw [MonoidHom.mem_ker, show qToAut g = qToAut (⟨g, hgC⟩ : CQ) from rfl, qToAut_of_mem]
    have : (QuotientGroup.mk (⟨g, hgC⟩ : CQ) : CQ ⧸ ZC) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_ZC_iff.2 hg)
    rw [this, map_one, map_one]
  have hcard : Nat.card qToAut.ker = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup qToAut.ker
    rw [card_QW, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      qToAut_surjective).toEquiv, h1] at h
    omega
  exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [hcard, card_Zq])).symm

end CFSG.Quasithin.H13.J4
