module

public import CFSG.Quasithin.EmptyFaithful.S153NBb1

public section

namespace CFSG.Quasithin.S153N.Bb

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_le [Finite G] {H : Subgroup G} {c : G}
    (h : ∀ v ∈ H, c * v * c⁻¹ ∈ H) : c ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj c).toMonoidHom ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have hcard : Nat.card ↥(H.map (MulAut.conj c).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have heq : H.map (MulAut.conj c).toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 : c * x * c⁻¹ ∈ H.map (MulAut.conj c).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨w, hw, hwx⟩ := h1
  have : w = x := by
    have h2 : c * w * c⁻¹ = c * x * c⁻¹ := hwx
    simpa using h2
  exact this ▸ hw

section Abstract

variable {V0 V E A : Subgroup G} [IsMulCommutative ↥V]

theorem card_inf_centralizer_le [Finite G] (hEV : E ≤ V)
    (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hAE : A ≤ Subgroup.centralizer (E : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card E * Nat.card ↥(@fixV (Qt V E) (cgQt V E)
        ((A.subgroupOf (Subgroup.centralizer (E : Set G))).map (rhoC V E hN))) := by
  have hDV : V ⊓ Subgroup.centralizer (A : Set G) ≤ V := inf_le_left
  have hED : E ≤ V ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf hEV fun e he => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hAE ha) e he).symm
  have hcard := card_eq_mul_range hDV hED
  have hle : (projOn V E (V ⊓ Subgroup.centralizer (A : Set G)) hDV).range ≤
      @fixV (Qt V E) (cgQt V E)
        ((A.subgroupOf (Subgroup.centralizer (E : Set G))).map (rhoC V E hN)) := by
    rintro _ ⟨d, rfl⟩ x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hcomm : (a : G) * d = d * a := Subgroup.mem_centralizer_iff.mp d.2.2 a ha
    rw [projOn_apply, rhoC_mk]
    congr 1
    apply Subtype.ext
    show (a : G) * d * (a : G)⁻¹ = d
    rw [hcomm]
    group
  rw [hcard]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)

theorem stab_iff_abstract [Finite G] (hEV0 : E ≤ V0) (hV0V : V0 ≤ V)
    (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (c : ↥(Subgroup.centralizer (E : Set G))) :
    (∀ u ∈ imgQ V E V0 hV0V, rhoC V E hN c u ∈ imgQ V E V0 hV0V) ↔
      (c : G) ∈ Subgroup.normalizer (V0 : Set G) := by
  constructor
  · intro h
    apply mem_normalizer_of_conj_le
    intro v hv
    have h1 := h _ (mkQ_mem_imgQ hV0V hv)
    rw [rhoC_mk] at h1
    obtain ⟨v', hv', hv'eq⟩ := (mem_imgQ hV0V).1 h1
    have h2 := (mkQ_eq_iff V E _ _).1 hv'eq
    have e : (c : G) * v * (c : G)⁻¹ = v' * (((c : G) * v * (c : G)⁻¹)⁻¹ * v')⁻¹ := by group
    rw [e]
    exact V0.mul_mem hv' (V0.inv_mem (hEV0 h2))
  · intro hc u hu
    obtain ⟨v, hv, rfl⟩ := (mem_imgQ hV0V).1 hu
    rw [rhoC_mk]
    exact mkQ_mem_imgQ hV0V ((Subgroup.mem_normalizer_iff.mp hc v).mp hv)


theorem closure_rhoC_eq_top {Vc : Subgroup G} [IsMulCommutative ↥Vc]
    (hVc : Vc = conjClosure V0 (Subgroup.normalizer (E : Set G)))
    (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Vc : Set G)) (hV0 : V0 ≤ Vc)
    (hconj : ∀ g ∈ Subgroup.normalizer (E : Set G), ∀ v ∈ V0,
      ∃ c ∈ Subgroup.centralizer (E : Set G), ∃ v' ∈ V0, g * v * g⁻¹ = c * v' * c⁻¹) :
    Subgroup.closure {u : Qt Vc E | ∃ (c : ↥(Subgroup.centralizer (E : Set G))) (v : Qt Vc E),
      v ∈ imgQ Vc E V0 hV0 ∧ u = rhoC Vc E hN c v} = ⊤ := by
  set H := Subgroup.closure {u : Qt Vc E | ∃ (c : ↥(Subgroup.centralizer (E : Set G))) (v : Qt Vc E),
      v ∈ imgQ Vc E V0 hV0 ∧ u = rhoC Vc E hN c v} with hH
  have hle : Vc ≤ (H.comap (mkQ Vc E)).map Vc.subtype := by
    refine hVc.le.trans (conjClosure_le fun g hg z hz => ?_)
    obtain ⟨c, hc, v', hv', he⟩ := hconj g hg z hz
    have hmem : g * z * g⁻¹ ∈ Vc := hVc.ge (mem_conjClosure hg hz)
    refine ⟨⟨g * z * g⁻¹, hmem⟩, ?_, rfl⟩
    show mkQ Vc E ⟨g * z * g⁻¹, hmem⟩ ∈ H
    refine Subgroup.subset_closure ⟨⟨c, hc⟩, mkQ Vc E ⟨v', hV0 hv'⟩, mkQ_mem_imgQ hV0 hv', ?_⟩
    rw [rhoC_mk]
    congr 1
    exact Subtype.ext he
  refine eq_top_iff.2 fun u _ => ?_
  obtain ⟨x, rfl⟩ := mkQ_surjective Vc E u
  obtain ⟨w, hw, hwx⟩ := hle x.2
  have : w = x := Subtype.ext hwx
  rw [← this]
  exact hw


theorem Qt_sq (hV2 : ∀ v ∈ V, v ^ 2 = 1) (u : Qt V E) : u ^ 2 = 1 := by
  induction u using QuotientGroup.induction_on with
  | H v =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : v ^ 2 = 1 := Subtype.ext (by simpa using hV2 v v.2)
    rw [this]
    exact Subgroup.one_mem _

theorem actN_mem_imgQ (hV0V : V0 ≤ V)
    (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (g : ↥(Subgroup.normalizer (E : Set G))) (hg : (g : G) ∈ Subgroup.normalizer (V0 : Set G))
    {u : Qt V E} (hu : u ∈ imgQ V E V0 hV0V) : actN V E hN g u ∈ imgQ V E V0 hV0V := by
  obtain ⟨v, hv, rfl⟩ := (mem_imgQ hV0V).1 hu
  rw [actN_mk]
  exact mkQ_mem_imgQ hV0V ((Subgroup.mem_normalizer_iff.mp hg v).mp hv)

theorem exists_moved_of_comm_not_mem (hV0V : V0 ≤ V)
    (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (g : ↥(Subgroup.normalizer (E : Set G)))
    (h : ∃ v ∈ V0, (g : G) * v * (g : G)⁻¹ * v⁻¹ ∉ E) :
    ∃ u ∈ imgQ V E V0 hV0V, actN V E hN g u ≠ u := by
  obtain ⟨v, hv, hvE⟩ := h
  have hvV : v ∈ V := hV0V hv
  set b : ↥V := ⟨v, hvV⟩ with hb
  set a : ↥V := ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN g.2) b).mp hvV⟩
    with ha
  refine ⟨mkQ V E b, mkQ_mem_imgQ hV0V hv, fun heq => hvE ?_⟩
  rw [actN_mk, mkQ_eq_iff] at heq
  have hcomm : (a : G) * (b : G)⁻¹ = (b : G)⁻¹ * (a : G) :=
    congrArg Subtype.val (mul_comm' a b⁻¹)
  have e : (g : G) * v * (g : G)⁻¹ * v⁻¹ = ((a : G)⁻¹ * (b : G))⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact hcomm
  rw [e]
  exact E.inv_mem heq

end Abstract

end CFSG.Quasithin.S153N.Bb
