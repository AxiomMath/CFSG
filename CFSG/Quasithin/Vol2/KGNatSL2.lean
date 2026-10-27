module

public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Vol2.Ch11SecCFacts3

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

section Conj

variable {G : Type*} [Group G]

theorem conjSubgroup_conjSubgroup (a b : G) (T : Subgroup G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup a (CFSG.CGT.Timmesfeld75.conjSubgroup b T) =
      CFSG.CGT.Timmesfeld75.conjSubgroup (a * b) T := by
  ext x
  simp only [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
  rw [show (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b by group]

theorem conjSubgroup_eq_of_mem_normalizer {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) : CFSG.CGT.Timmesfeld75.conjSubgroup g T = T := by
  ext x
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) x
  rw [inv_inv] at this
  exact this.symm

theorem mem_normalizer_conjSubgroup {T : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup g T : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (T : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
  constructor
  · intro h t
    have := h (g * t * g⁻¹)
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group,
      show g⁻¹ * (x * (g * t * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * t * (g⁻¹ * x * g)⁻¹ by group]
      at this
    exact this
  · intro h y
    have := h (g⁻¹ * y * g)
    rw [show g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * y * x⁻¹) * g by group]
      at this
    exact this

end Conj

section SL2

variable {F : Type} [Field F]

theorem borel_le_normalizer_utri : borel F ≤ Subgroup.normalizer (utri F : Set SL(2, F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_utri_of_mem_borel hg hh, fun hh => ?_⟩
  have := conj_mem_utri_of_mem_borel (Subgroup.inv_mem _ hg) hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem normalizer_utri_le_borel : Subgroup.normalizer (utri F : Set SL(2, F)) ≤ borel F := by
  intro g hg
  by_contra hgb
  have h1 := utri_inf_conj_eq_bot hgb
  have h2 : CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) = utri F := by
    ext x
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) x
    rw [inv_inv] at this
    exact this.symm
  rw [h2, inf_idem] at h1
  have h3 : (utriElt 1 : SL(2, F)) ∈ utri F := utriElt_mem_utri 1
  rw [h1, Subgroup.mem_bot] at h3
  exact utriElt_ne_one one_ne_zero h3

theorem normalizer_utri_eq_borel :
    Subgroup.normalizer (utri F : Set SL(2, F)) = borel F :=
  le_antisymm normalizer_utri_le_borel borel_le_normalizer_utri

@[expose] noncomputable def torusHom : Fˣ →* SL(2, F) :=
  MonoidHom.mk' torusElt torusElt_mul

theorem orderOf_torusElt_generator [Finite F] {a : Fˣ} (ha : ∀ x, x ∈ Subgroup.zpowers a) :
    orderOf (torusElt a : SL(2, F)) = Nat.card F - 1 := by
  rw [show (torusElt a : SL(2, F)) = torusHom a from rfl,
    orderOf_injective torusHom torusElt_injective a, orderOf_eq_card_of_forall_mem_zpowers ha,
    Nat.card_units]

theorem utri_sup_conj_eq_top {h : SL(2, F)} (hh : h ∉ borel F) :
    utri F ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup h (utri F) = ⊤ := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_borel_mul_wElt_mul_borel hh
  rw [← conjSubgroup_conjSubgroup, ← conjSubgroup_conjSubgroup,
    conjSubgroup_eq_of_mem_normalizer (borel_le_normalizer_utri hb₂), conjSubgroup_wElt_utri]
  have e : CFSG.CGT.Timmesfeld75.conjSubgroup b₁ (utri F) = utri F :=
    conjSubgroup_eq_of_mem_normalizer (borel_le_normalizer_utri hb₁)
  calc utri F ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup b₁ (ltri F) =
        CFSG.CGT.Timmesfeld75.conjSubgroup b₁ (utri F) ⊔
          CFSG.CGT.Timmesfeld75.conjSubgroup b₁ (ltri F) := by rw [e]
    _ = ⊤ := by rw [← conjSubgroup_sup_eq_sup, utri_sup_ltri, conjSubgroup_top]

theorem center_SL2_eq_bot [CharP F 2] : Subgroup.center SL(2, F) = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  have h1 := (Subgroup.mem_center_iff.mp hz) (utriElt 1)
  have h2 := (Subgroup.mem_center_iff.mp hz) (ltriElt 1)
  have e10 : z 1 0 = 0 := by
    have := congrArg (fun g : SL(2, F) => g 1 1) h1
    simp only [mul_apply_11, utriElt_apply_01, utriElt_apply_10, utriElt_apply_11] at this
    linear_combination -this
  have e01 : z 0 1 = 0 := by
    have := congrArg (fun g : SL(2, F) => g 0 0) h2
    simp only [mul_apply_00, ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10] at this
    linear_combination -this
  have e11 : z 1 1 = z 0 0 := by
    have := congrArg (fun g : SL(2, F) => g 0 1) h1
    simp only [mul_apply_01, utriElt_apply_00, utriElt_apply_01, utriElt_apply_11] at this
    linear_combination this
  have hdet := sl2_det z
  rw [e10, e01, e11, mul_zero, sub_zero] at hdet
  have h2z : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have e00 : z 0 0 = 1 := by
    have h2' : (z 0 0 + 1) ^ 2 = 0 := by linear_combination hdet + (z 0 0) * h2z + h2z
    have h3 : z 0 0 + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2'
    linear_combination h3 - h2z
  rw [Subgroup.mem_bot]
  exact sl2_ext (by rw [e00, one_apply_00]) (by rw [e01, one_apply_01])
    (by rw [e10, one_apply_10]) (by rw [e11, e00, one_apply_11])

variable [Finite F] [CharP F 2]

theorem exists_conj_utri_eq {U : Subgroup SL(2, F)} (hU : IsPGroup 2 U)
    (hcard : Nat.card U = Nat.card F) :
    ∃ g : SL(2, F), CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) = U := by
  have h := Subgroup.card_mul_index U
  rw [card_sl2, hcard] at h
  have hidx : U.index = Nat.card F ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  obtain ⟨n, hn1, hn⟩ := exists_natCard_eq_two_pow (F := F)
  have hodd : Odd U.index := by
    rw [hidx, hn]
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) ?_ odd_one
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn1.ne'⟩, two_ne_zero⟩
  obtain ⟨g, hg⟩ := exists_conjSubgroup_utri_eq_of_sylow (hU.toSylow (by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd))
  exact ⟨g, hg⟩

omit [CharP F 2] in
theorem normalizer_conj_utri (g : SL(2, F)) :
    Subgroup.normalizer
        (CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) : Set SL(2, F)) ≠ ⊤ ∧
      ∃ d ∈ Subgroup.normalizer
        (CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) : Set SL(2, F)),
        orderOf d = Nat.card F - 1 := by
  refine ⟨fun htop => ?_, ?_⟩
  · have hw : g * wElt * g⁻¹ ∈ Subgroup.normalizer
        (CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) : Set SL(2, F)) := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [mem_normalizer_conjSubgroup, show g⁻¹ * (g * wElt * g⁻¹) * g = wElt by group,
      normalizer_utri_eq_borel] at hw
    exact wElt_not_mem_borel hw
  · obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
    refine ⟨g * torusElt a * g⁻¹, ?_, ?_⟩
    · rw [mem_normalizer_conjSubgroup, show g⁻¹ * (g * torusElt a * g⁻¹) * g = torusElt a by
        group, normalizer_utri_eq_borel]
      exact torusElt_mem_borel a
    · have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
        (torusElt a)
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at h
      rw [h, orderOf_torusElt_generator ha]

theorem exists_conj_utri_eq_of_index {U : Subgroup SL(2, F)} (hU : IsPGroup 2 U)
    (hidx : ¬ 2 ∣ U.index) :
    ∃ g : SL(2, F), CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) = U :=
  exists_conjSubgroup_utri_eq_of_sylow (hU.toSylow hidx)

end SL2

theorem factSL2SylowNormalizer_holds : Ch11.SecC.FactSL2SylowNormalizer := by
  intro F _ _ n hn hF U hU hcard
  have : CharP F 2 := charP_two_of_card (by omega) hF
  rw [← hF] at hcard ⊢
  obtain ⟨g, rfl⟩ := exists_conj_utri_eq hU hcard
  exact normalizer_conj_utri g

theorem center_bot_and_dvd_card_normalizer_SL2 :
    ∀ (k : ℕ) (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ k → 2 ≤ k →
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ ∧
      ∀ S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
        CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
          (2 ^ k - 1) ∣
            Nat.card ↥(Subgroup.normalizer (S : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  intro k F _ _ hF hk
  have : CharP F 2 := charP_two_of_card (by omega) hF
  refine ⟨center_SL2_eq_bot, fun S hS => ?_⟩
  obtain ⟨-, hS2, hidx⟩ := hS
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hidx
  obtain ⟨g, rfl⟩ := exists_conj_utri_eq_of_index hS2 hidx
  obtain ⟨-, d, hd, hord⟩ := normalizer_conj_utri g
  rw [← hF, ← hord]
  have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥(Subgroup.normalizer
    (CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) : Set SL(2, F))))
  rwa [Subgroup.orderOf_mk] at this

end CFSG.Quasithin.Vol2.KGNat
