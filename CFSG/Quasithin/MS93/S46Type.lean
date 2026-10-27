module

public import CFSG.Quasithin.MS93.S46TypeLin
public import CFSG.Quasithin.MS93.S46Crit
public import CFSG.Quasithin.MS93.S4A42Coc

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped Matrix commutatorElement

section Image

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]
  {ψ : ↥K →* ↥(StatedSL 3 F)}

theorem isPGroup_natImage {P : Subgroup G} (hP : IsPGroup 2 P) (hPK : P ≤ K) :
    IsPGroup 2 (natImage ψ P) :=
  (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm).map (toSL3 ψ)

theorem conj_mem_natImage {A : Subgroup G} {a : ↥K}
    (ha : (a : G) ∈ Subgroup.normalizer (A : Set G)) {e : SL3 F} (he : e ∈ natImage ψ A) :
    toSL3 ψ a * e * (toSL3 ψ a)⁻¹ ∈ natImage ψ A := by
  obtain ⟨b, hbA, rfl⟩ := mem_natImage.mp he
  refine mem_natImage.mpr ⟨a * b * a⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.mp ha b).mp hbA
  simpa using this

theorem inv_conj_mem_natImage {A : Subgroup G} {a : ↥K}
    (ha : (a : G) ∈ Subgroup.normalizer (A : Set G)) {e : SL3 F} (he : e ∈ natImage ψ A) :
    (toSL3 ψ a)⁻¹ * e * toSL3 ψ a ∈ natImage ψ A := by
  have ha' : ((a⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.coe_inv]
    exact Subgroup.inv_mem _ ha
  have := conj_mem_natImage ha' he
  rwa [map_inv, inv_inv] at this

theorem toSL3_pow_two_pow {a : ↥K} {k : ℕ} (ha : (a : G) ^ 2 ^ k = 1) :
    toSL3 ψ a ^ 2 ^ k = 1 := by
  rw [← map_pow, show a ^ 2 ^ k = 1 from Subtype.ext (by simpa using ha), map_one]

end Image

section Field

variable {G : Type} [Group G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem charP_two_of_isSL3FullVia (hφ : IsSL3FullVia M T L φ) : CharP F 2 := by
  obtain ⟨n, hn⟩ := hφ.1
  exact FFC.charP_two_of_card_pow (n := n) (by rw [Nat.card_eq_fintype_card, hn])

theorem four_le_card_of_isSL3FullVia (hφ : IsSL3FullVia M T L φ) (hq : Nat.card F ≠ 2) :
    4 ≤ Nat.card F := by
  obtain ⟨n, hn⟩ := hφ.1
  have hq1 : 2 ≤ Nat.card F := Finite.one_lt_card
  rw [Nat.card_eq_fintype_card, hn] at hq hq1 ⊢
  rcases n with _ | _ | n
  · simp at hq1
  · simp at hq
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Field

section Crit

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L) {F : Type}
  [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))
include h hφ hC

theorem crit_dims {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    {ψ' : ↥(stab (puAmalgam h.le) α') →* ↥(StatedSL 3 F)}
    (hψ' : IsSumOfNaturalModulesVia (stab _ α') (Uloc h.le L α') ⊥ ψ' false 1) :
    Module.finrank F (fixN (natImage ψ' (ZM (puAmalgam h.le) α))) =
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) =
        Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      1 ≤ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤ 2 ∧
      (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) =
        Nat.card F ^ (3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α')))) ∧
      (Qv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α') =
        Nat.card F ^ (3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α')))) ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') =
        Nat.card F ^ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) α')) =
        (Qv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α') := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨hff', -, haE, hR, hw'f', hE'ne⟩ := s35_core h hC hφ hc hψ hψ'
  obtain ⟨-, hcardE', haE', hR', -, -⟩ := s35_core h hC hφ hc' hψ' hψ
  have hRR : Nat.card ↥(critR (puAmalgam h.le) α' α) =
      Nat.card ↥(critR (puAmalgam h.le) α α') := by
    rw [critR, critR, Subgroup.commutator_comm]
  have hpow : Nat.card F ^ Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) =
      Nat.card F ^ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) := by
    rw [← hR', hRR, hR]
  have hww' := Nat.pow_right_injective hq hpow
  have hne : (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact hc.2.2
  have hf2 : Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤ 2 := by
    by_contra hcon
    apply hne
    rw [haE, show 3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) = 0 by
      omega, pow_zero]
  have hw1 : 1 ≤ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact commN_ne_bot hE'ne
  refine ⟨hff', hww', hw1, hw'f', hf2, haE, ?_, hR, hcardE'⟩
  rw [haE', hff']

theorem relIndex_zm_comm {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) =
      (Qv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α') := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ :=
    exists_natural_Uloc h hφ (ms22_iii _ h.hyp20 h.critDist_pos hC hc).1
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := crit_dims h hφ hC hc hψ hψ'
  rw [h6, h7]

theorem crit_type {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ((Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ^ 2 ∧
        Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F) ∨
      ((Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
        Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F) ∨
      ((Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
        Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F ^ 2 ∧
        4 ≤ Fintype.card F) := by
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hc
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hc'.1
  obtain ⟨-, -, hw1, hwf, hf2, hcf, hcf', hrw, hcard⟩ := crit_dims h hφ hC hc hψ hψ'
  simp only [← Nat.card_eq_fintype_card]
  rw [hcf, hrw]
  set f := Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) with hfdef
  set w := Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) with hwdef
  rcases (by omega : (f = 1 ∧ w = 1) ∨ (f = 2 ∧ w = 1) ∨ (f = 2 ∧ w = 2)) with
    ⟨hf, hw⟩ | ⟨hf, hw⟩ | ⟨hf, hw⟩
  · left
    rw [hf, hw]
    exact ⟨rfl, pow_one _⟩
  · right; left
    rw [hf, hw]
    exact ⟨pow_one _, pow_one _⟩
  · right; right
    rw [hf, hw]
    refine ⟨pow_one _, rfl, four_le_card_of_isSL3FullVia hφ fun hq2 => ?_⟩
    have h2 : Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) α')) = 2 := by
      rw [hcard, hcf', hf, hq2]
      norm_num
    have := finrank_commN_le_one_of_card_eq_two (natImage_zm_sq h hc'.1) h2
    omega

omit hC in
theorem critR_eq_commutator_uloc {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ∧
      ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ Uloc h.le L α := by
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α :=
    zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  exact ⟨commutator_zm_eq_uloc h hfull hc.1 hZs,
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hψ.1)⟩

theorem uloc_inf_centralizer_eq_critR {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hnot : ¬ ((Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F)) :
    Uloc h.le L α ⊓
        Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) =
      critR (puAmalgam h.le) α α' := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hc'.1
  obtain ⟨-, -, hw1, hwf, hf2, hcf, -, hrw, -⟩ := crit_dims h hφ hC hc hψ hψ'
  rw [← Nat.card_eq_fintype_card, hcf, hrw] at hnot
  have hwf' : Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) =
      Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) := by
    by_contra hne
    exact hnot ⟨by rw [show 3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) =
      1 by omega, pow_one], by
        rw [show Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) = 1 by omega,
          pow_one]⟩
  have heq := commN_eq_fixN_of_finrank_eq (natImage_zm_sq h hc'.1) (natImage_zm_comm h hc'.1)
    hwf'
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb hc
  obtain ⟨hR, hRU⟩ := critR_eq_commutator_uloc h hφ hc
  rw [hR]
  ext x
  constructor
  · rintro ⟨hxU, hxC⟩
    have h1 := (mem_centralizer_iff_natVec hψ hZs ⟨x, hxU⟩).mp hxC
    rw [← heq] at h1
    exact (mem_commutator_iff_natVec hψ hZs ⟨x, hxU⟩).mpr h1
  · intro hx
    have hxU := hRU hx
    have h1 := (mem_commutator_iff_natVec hψ hZs ⟨x, hxU⟩).mp hx
    rw [heq] at h1
    exact ⟨hxU, (mem_centralizer_iff_natVec hψ hZs ⟨x, hxU⟩).mpr h1⟩

theorem card_uloc_inf_centralizer_typeII {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hII : (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F) :
    Nat.card ↥(Uloc h.le L α ⊓
        Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal)) =
      Fintype.card F ^ 2 := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hc'.1
  obtain ⟨-, -, -, -, hf2, hcf, -, -, -⟩ := crit_dims h hφ hC hc hψ hψ'
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb hc
  have h1 := hII.1
  rw [← Nat.card_eq_fintype_card, hcf] at h1
  have hf : Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) = 2 := by
    have := Nat.pow_right_injective hq (h1.trans (pow_one _).symm)
    omega
  rw [card_inf_centralizer_eq hψ hZs, card_fixN, hf, Nat.card_eq_fintype_card]

theorem natImage_zm_le_natImage_uloc {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1) :
    natImage ψ (ZM (puAmalgam h.le) α') ≤ natImage ψ (Uloc h.le L α') := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb hc
  have hUK : Uloc h.le L α' ≤ stab _ α := (uloc_le_zm h hfull hc'.1).trans hZs
  have hZK : Zloc h.le L α' ≤ stab _ α := (zloc_le_zm h hfull hc'.1).trans hZs
  have hZQ : Zloc h.le L α' ≤ Qv _ α := zloc_le_qv_of_isCritical h hfull hc'
  have hQU : Qv (puAmalgam h.le) α ≤
      Subgroup.centralizer (Uloc h.le L α : Set (puAmalgam h.le).Universal) :=
    (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hc.1)).trans
      (Subgroup.centralizer_le (uloc_le_zm h hfull hc.1))
  unfold natImage
  rw [zm_eq_uloc_sup_zloc h hfull hc'.1, Subgroup.subgroupOf_sup hUK hZK, Subgroup.map_sup]
  refine sup_le le_rfl ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : (a : (puAmalgam h.le).Universal) ∈ Zloc h.le L α' := ha
  have h1 : toSL3 ψ a = 1 := by
    refine (toSL3_eq_one_iff hψ a).mpr fun v hv => ?_
    have := Subgroup.mem_centralizer_iff.mp (hQU (hZQ ha')) v hv
    rw [← this, mul_inv_cancel_right]
  rw [h1]
  exact Subgroup.one_mem _

theorem commutator_mem_qv_of_commute {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    {ψ' : ↥(stab (puAmalgam h.le) α') →* ↥(StatedSL 3 F)}
    (hψ' : IsSumOfNaturalModulesVia (stab _ α') (Uloc h.le L α') ⊥ ψ' false 1)
    {z g : (puAmalgam h.le).Universal} (hz : z ∈ ZM (puAmalgam h.le) α)
    (hzs : z ∈ stab (puAmalgam h.le) α') (hgα : g ∈ stab (puAmalgam h.le) α)
    (hgs : g ∈ stab (puAmalgam h.le) α')
    (hcomm : toSL3 ψ' ⟨g, hgs⟩ * toSL3 ψ' ⟨z, hzs⟩ = toSL3 ψ' ⟨z, hzs⟩ * toSL3 ψ' ⟨g, hgs⟩) :
    ⁅z, g⁆ ∈ Qv (puAmalgam h.le) α' := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  have hZ : ⁅z, g⁆ ∈ ZM (puAmalgam h.le) α := by
    have h1 : g * z⁻¹ * g⁻¹ ∈ ZM (puAmalgam h.le) α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α hgα) _).mp
        (Subgroup.inv_mem _ hz)
    have e : ⁅z, g⁆ = z * (g * z⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ hz h1
  have hs : ⁅z, g⁆ ∈ stab (puAmalgam h.le) α' := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hzs hgs)
      (Subgroup.inv_mem _ hzs)) (Subgroup.inv_mem _ hgs)
  have h1 : toSL3 ψ' ⟨⁅z, g⁆, hs⟩ = 1 := by
    have e : (⟨⁅z, g⁆, hs⟩ : ↥(stab (puAmalgam h.le) α')) =
        ⁅(⟨z, hzs⟩ : ↥(stab (puAmalgam h.le) α')), ⟨g, hgs⟩⁆ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have hcU : ⁅z, g⁆ ∈
      Subgroup.centralizer (Uloc h.le L α' : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := (toSL3_eq_one_iff hψ' ⟨⁅z, g⁆, hs⟩).mp h1 v hv
    calc v * ⁅z, g⁆ = ⁅z, g⁆ * v * ⁅z, g⁆⁻¹ * ⁅z, g⁆ := by rw [this]
      _ = ⁅z, g⁆ * v := by group
  have hcZ := (mem_centralizer_zm_iff h hfull hc'.1 hs).mpr hcU
  have key := zm_inf_centralizer_eq_inf_qv _ h.hyp20 hb hC hc
  have hmem : ⁅z, g⁆ ∈ ZM (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' := by
    rw [← key]
    exact ⟨hZ, hcZ⟩
  exact hmem.2

theorem commutator_zm_qv_mid_le (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hnotI : ¬ (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) =
      Fintype.card F ^ 2) :
    ⁅ZM (puAmalgam h.le) α, Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2)⁆ ≤
      Qv (puAmalgam h.le) α' := by
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h20 hb hC hc
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hc'.1
  obtain ⟨hfE, hwE, hw1, hwf, hf2, hcf, -, -, -⟩ := crit_dims h hφ hC hc hψ hψ'
  have hf : Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) = 2 := by
    by_contra hne
    apply hnotI
    rw [← Nat.card_eq_fintype_card, hcf,
      show 3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) = 2 by omega]
  have hαβ := adj_geo_one_of_isCritical _ hb hc
  have hβγ := adj_geo_crit hb4 hc (i := 1) (by norm_num)
  have hγε := adj_geo_crit hb4 hc (i := 2) (by norm_num)
  have hεα' := adj_geo_crit hb4 hc (i := 3) (by norm_num)
  rw [show (3 : ℕ) + 1 = 4 from rfl, geo_four hb4 hc] at hεα'
  have hγ := isMVtx_geo_two' hb4 hc
  have hQβ : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) ≤
      Qv _ (geo (puAmalgam h.le) α α' 1) := qv_le_qv _ h20 hγ hβγ.symm
  have hQα : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) ≤ stab _ α :=
    hQβ.trans (qv_le_stab_of_adj _ hαβ.symm)
  have hQα' : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) ≤ stab _ α' :=
    (qv_le_qv _ h20 hγ hγε).trans (qv_le_stab_of_adj _ hεα')
  have h2 : ∀ g ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2), ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := isPGroup_qv _ h20 (not_isMVtx_geo_one hb4 hc) ⟨g, hQβ hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb hc
  have hZs' : ZM (puAmalgam h.le) α ≤ stab _ α' := zm_le_stab_right _ h20 hb hC hc
  suffices key : ∀ g (hg : g ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2)),
      ∀ e ∈ natImage ψ' (ZM (puAmalgam h.le) α),
        toSL3 ψ' ⟨g, hQα' hg⟩ * e = e * toSL3 ψ' ⟨g, hQα' hg⟩ by
    rw [Subgroup.commutator_le]
    intro z hz g hg
    exact commutator_mem_qv_of_commute h hφ hC hc hψ' hz (hZs' hz) (hQα hg) (hQα' hg)
      (key g hg _ (mem_natImage.mpr ⟨⟨z, hZs' hz⟩, hz, rfl⟩))
  rcases (by omega : Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) = 1 ∨
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) = 2) with hw | hw
  ·
    intro g hg e he
    obtain ⟨k, hk⟩ := h2 g hg
    have hnZ : g ∈ Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
      stab_le_normalizer_zm _ α (hQα hg)
    exact commute_of_normalizes (hwE.trans hw).le (hfE.trans hf) (toSL3_pow_two_pow hk)
      (fun _ he' => conj_mem_natImage hnZ he') (fun _ he' => inv_conj_mem_natImage hnZ he') he
  have hW := commN_eq_fixN_of_finrank_eq (natImage_zm_sq h hc'.1) (natImage_zm_comm h hc'.1)
    (hw.trans hf.symm)
  have hW' := commN_eq_fixN_of_finrank_eq (natImage_zm_sq h hc.1) (natImage_zm_comm h hc.1)
    ((hwE.trans hw).trans (hfE.trans hf).symm)
  obtain ⟨hR, hRU⟩ := critR_eq_commutator_uloc h hφ hc
  have hR' : critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ := by
    rw [critR, Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hc'.1 hZs']
  have hRU' : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ≤ Uloc h.le L α' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs'.trans hψ'.1)
  have hZab : ∀ a ∈ ZM (puAmalgam h.le) α', ∀ b ∈ ZM (puAmalgam h.le) α', a * b = b * a := by
    intro a ha b hb'
    have hcomm := (isElemAbelian_zm _ h20 hb hc'.1).1
    have := hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩
    simpa using congrArg Subtype.val this
  have hRker : ∀ r ∈ critR (puAmalgam h.le) α α', ∀ hr : r ∈ stab (puAmalgam h.le) α',
      toSL3 ψ' ⟨r, hr⟩ = 1 := by
    intro r hrR hr
    have hrZ : r ∈ ZM (puAmalgam h.le) α' := uloc_le_zm h hfull hc'.1 (hRU' (hR' ▸ hrR))
    refine (toSL3_eq_one_iff hψ' ⟨r, hr⟩).mpr fun v hv => ?_
    have := hZab r hrZ v (uloc_le_zm h hfull hc'.1 hv)
    change r * v * r⁻¹ = v
    rw [this, mul_inv_cancel_right]
  have hEU := natImage_zm_le_natImage_uloc h hφ hC hc hψ
  have hcentR : ∀ g ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2),
      ∀ s ∈ critR (puAmalgam h.le) α α', g * s = s * g := by
    intro g hg
    obtain ⟨k, hk⟩ := h2 g hg
    have hgk : toSL3 ψ (⟨g, hQα hg⟩ : ↥(stab (puAmalgam h.le) α)) ^ 2 ^ k = 1 :=
      toSL3_pow_two_pow hk
    have hgk' : toSL3 ψ' (⟨g, hQα' hg⟩ : ↥(stab (puAmalgam h.le) α')) ^ 2 ^ k = 1 :=
      toSL3_pow_two_pow hk
    have hnZ' : g ∈ Subgroup.normalizer
        (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :=
      stab_le_normalizer_zm _ α' (hQα' hg)
    have hsub : ∀ x, (toSL3 ψ (⟨g, hQα hg⟩ : ↥(stab (puAmalgam h.le) α)) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ fixN (natImage ψ (ZM (puAmalgam h.le) α')) :=
      sub_mem_of_finrank_eq_two hgk hf fun _ hy =>
        mulVec_mem_fixN_of_normalizes (fun _ he => inv_conj_mem_natImage hnZ' he) hy
    obtain ⟨v, hv⟩ := exists_not_mem_of_finrank_eq_two hf
    obtain ⟨z₀, rfl⟩ := natVec_surjective hψ v
    have hz₀Z : (z₀ : (puAmalgam h.le).Universal) ∈ ZM (puAmalgam h.le) α :=
      uloc_le_zm h hfull hc.1 z₀.2
    have hz₀s := hZs' hz₀Z
    have hgz : g * z₀ * g⁻¹ * (z₀ : (puAmalgam h.le).Universal)⁻¹ ∈
        critR (puAmalgam h.le) α α' := by
      have hmem : g * z₀ * g⁻¹ ∈ Uloc h.le L α :=
        (Subgroup.mem_normalizer_iff.mp (hψ.1 (hQα hg)) _).mp z₀.2
      have hy : natVec hψ ((⟨_, hmem⟩ : ↥(Uloc h.le L α)) * z₀⁻¹) =
          (toSL3 ψ (⟨g, hQα hg⟩ : ↥(stab (puAmalgam h.le) α)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            natVec hψ z₀ - natVec hψ z₀ := by
        rw [natVec_mul, natVec_inv, natVec_conj hψ ⟨g, hQα hg⟩ z₀ ⟨_, hmem⟩ rfl, sub_eq_add_neg]
      rw [hR]
      exact (mem_commutator_iff_natVec hψ hZs _).mpr (by rw [hy, hW]; exact hsub _)
    have hgt : toSL3 ψ' (⟨g, hQα' hg⟩ : ↥(stab (puAmalgam h.le) α')) *
        toSL3 ψ' (⟨z₀, hz₀s⟩ : ↥(stab (puAmalgam h.le) α')) =
        toSL3 ψ' (⟨z₀, hz₀s⟩ : ↥(stab (puAmalgam h.le) α')) *
          toSL3 ψ' (⟨g, hQα' hg⟩ : ↥(stab (puAmalgam h.le) α')) := by
      have hrs : g * z₀ * g⁻¹ * (z₀ : (puAmalgam h.le).Universal)⁻¹ ∈
          stab (puAmalgam h.le) α' :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQα' hg) hz₀s)
          (Subgroup.inv_mem _ (hQα' hg))) (Subgroup.inv_mem _ hz₀s)
      have hr1 := hRker _ hgz hrs
      have e : (⟨g, hQα' hg⟩ : ↥(stab (puAmalgam h.le) α')) * ⟨z₀, hz₀s⟩ =
          ⟨_, hrs⟩ * ⟨z₀, hz₀s⟩ * ⟨g, hQα' hg⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
      rw [← map_mul, e, map_mul, map_mul, hr1, one_mul]
    have htt : toSL3 ψ' (⟨z₀, hz₀s⟩ : ↥(stab (puAmalgam h.le) α')) *
        toSL3 ψ' (⟨z₀, hz₀s⟩ : ↥(stab (puAmalgam h.le) α')) = 1 :=
      natImage_zm_sq h hc.1 _ (mem_natImage.mpr ⟨⟨z₀, hz₀s⟩, hz₀Z, rfl⟩)
    have hfixc : ∀ a ∈ Uloc h.le L α',
        g * ⁅(z₀ : (puAmalgam h.le).Universal), a⁆ * g⁻¹ =
          ⁅(z₀ : (puAmalgam h.le).Universal), a⁆ := by
      intro a ha
      have hmem : (z₀ : (puAmalgam h.le).Universal) * a * (z₀ : (puAmalgam h.le).Universal)⁻¹ ∈
          Uloc h.le L α' := (Subgroup.mem_normalizer_iff.mp (hψ'.1 hz₀s) a).mp ha
      have hnat : natVec hψ' ((⟨_, hmem⟩ : ↥(Uloc h.le L α')) * (⟨a, ha⟩ : ↥(Uloc h.le L α'))⁻¹) =
          (toSL3 ψ' (⟨z₀, hz₀s⟩ : ↥(stab (puAmalgam h.le) α')) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            natVec hψ' ⟨a, ha⟩ - natVec hψ' ⟨a, ha⟩ := by
        rw [natVec_mul, natVec_inv, natVec_conj hψ' ⟨z₀, hz₀s⟩ ⟨a, ha⟩ ⟨_, hmem⟩ rfl,
          sub_eq_add_neg]
      have h1 := mulVec_eq_of_finrank_le_one hgk' (finrank_range_sub_one_le_one htt)
        (fun _ hy => mulVec_mem_range_of_commute hgt hy)
        (hnat ▸ sub_mem_range_sub_one _ (natVec hψ' ⟨a, ha⟩))
      have h2 := (commute_iff_natVec hψ' ⟨g, hQα' hg⟩ _).mpr h1
      have hu : (((⟨_, hmem⟩ : ↥(Uloc h.le L α')) * (⟨a, ha⟩ : ↥(Uloc h.le L α'))⁻¹ :
          ↥(Uloc h.le L α')) : (puAmalgam h.le).Universal) =
          ⁅(z₀ : (puAmalgam h.le).Universal), a⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      rw [hu] at h2
      change g * ⁅(z₀ : (puAmalgam h.le).Universal), a⁆ = ⁅(z₀ : (puAmalgam h.le).Universal), a⁆ * g
        at h2
      rw [h2, mul_inv_cancel_right]
    have hfixv : ∀ e ∈ natImage ψ (ZM (puAmalgam h.le) α'),
        (toSL3 ψ (⟨g, hQα hg⟩ : ↥(stab (puAmalgam h.le) α)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            ((e : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ z₀ - natVec hψ z₀) =
          (e : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ z₀ - natVec hψ z₀ := by
      intro e he
      obtain ⟨a, haU, rfl⟩ := mem_natImage.mp (hEU he)
      have hmem : ⁅(z₀ : (puAmalgam h.le).Universal), (a : (puAmalgam h.le).Universal)⁆ ∈
          Uloc h.le L α := by
        have h1 : (a : (puAmalgam h.le).Universal) * (z₀ : (puAmalgam h.le).Universal)⁻¹ *
            (a : (puAmalgam h.le).Universal)⁻¹ ∈ Uloc h.le L α :=
          (Subgroup.mem_normalizer_iff.mp (hψ.1 a.2) _).mp (Subgroup.inv_mem _ z₀.2)
        have e1 : ⁅(z₀ : (puAmalgam h.le).Universal), (a : (puAmalgam h.le).Universal)⁆ =
            (z₀ : (puAmalgam h.le).Universal) * ((a : (puAmalgam h.le).Universal) *
              (z₀ : (puAmalgam h.le).Universal)⁻¹ * (a : (puAmalgam h.le).Universal)⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e1]
        exact Subgroup.mul_mem _ z₀.2 h1
      have hnat := natVec_commutator hψ a z₀ ⟨_, hmem⟩ rfl
      have h2 := (natVec_conj hψ ⟨g, hQα hg⟩ ⟨_, hmem⟩ ⟨_, hmem⟩ (hfixc _ haU).symm).symm
      rw [hnat] at h2
      have h3 := congrArg Neg.neg h2
      rwa [← Matrix.mulVec_neg, neg_sub] at h3
    intro s hs
    rw [hR] at hs
    have hsU := hRU hs
    have h1 := (mem_commutator_iff_natVec hψ hZs ⟨s, hsU⟩).mp hs
    have h2 := mulVec_eq_of_mem_commN le_rfl (sup_span_eq_top hf hv) hfixv h1
    exact (commute_iff_natVec hψ ⟨g, hQα hg⟩ ⟨s, hsU⟩).mpr h2
  intro g hg e he
  obtain ⟨k, hk⟩ := h2 g hg
  have hgk' : toSL3 ψ' (⟨g, hQα' hg⟩ : ↥(stab (puAmalgam h.le) α')) ^ 2 ^ k = 1 :=
    toSL3_pow_two_pow hk
  have hfixW : ∀ y ∈ commN (natImage ψ' (ZM (puAmalgam h.le) α)),
      (toSL3 ψ' (⟨g, hQα' hg⟩ : ↥(stab (puAmalgam h.le) α')) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
        y := by
    intro y hy
    obtain ⟨u, rfl⟩ := natVec_surjective hψ' y
    have hu : (u : (puAmalgam h.le).Universal) ∈ critR (puAmalgam h.le) α α' := by
      rw [hR']
      exact (mem_commutator_iff_natVec hψ' hZs' u).mpr hy
    exact (commute_iff_natVec hψ' ⟨g, hQα' hg⟩ u).mp (hcentR g hg u hu)
  have hsub' := sub_mem_of_finrank_eq_two hgk' (hwE.trans hw)
    (fun y hy => by rw [hfixW y hy]; exact hy)
  exact commute_of_sub_mem (X := commN (natImage ψ' (ZM (puAmalgam h.le) α)))
    (Y := commN (natImage ψ' (ZM (puAmalgam h.le) α))) (fun x => sub_mem_commN he x)
    (fun y hy => by rw [hW'] at hy; exact hy e he) hfixW hsub'

omit hC in
theorem card_commutator_uloc_le {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ρ : Vtx (puAmalgam h.le)} (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ)
    {P : Subgroup (puAmalgam h.le).Universal} (hP : P ≤ Qv (puAmalgam h.le) ρ) :
    ∃ d ≤ 2, Nat.card ↥⁅Uloc h.le L δ, P⁆ = Fintype.card F ^ d := by
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hδ
  have hPK : P ≤ stab _ δ := hP.trans (qv_le_stab_of_adj _ hρ.symm)
  have hPp : IsPGroup 2 P :=
    (isPGroup_qv _ h.hyp20 ((isMVtx_iff_of_adj _ hρ).mp hδ)).to_le hP
  refine ⟨Module.finrank F (commN (natImage ψ P)),
    finrank_commN_le_two_of_pGroup (isPGroup_natImage hPp hPK), ?_⟩
  rw [card_commutator_eq hψ hPK, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card]

omit hC in
theorem commutator_uloc_eq_of_le {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ρ : Vtx (puAmalgam h.le)} (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ)
    {P : Subgroup (puAmalgam h.le).Universal} (hP : P ≤ Qv (puAmalgam h.le) ρ)
    {R H : Subgroup (puAmalgam h.le).Universal} (hR : Nat.card ↥R = Fintype.card F)
    (hH : Nat.card ↥H = Fintype.card F ^ 2) (hRP : R ≤ ⁅Uloc h.le L δ, P⁆)
    (hPH : ⁅Uloc h.le L δ, P⁆ ≤ H) :
    ⁅Uloc h.le L δ, P⁆ = R ∨ ⁅Uloc h.le L δ, P⁆ = H := by
  obtain ⟨d, hd, hcard⟩ := card_commutator_uloc_le h hφ hδ hρ hP
  have hq : 2 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have hfin : Finite ↥⁅Uloc h.le L δ, P⁆ :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  interval_cases d
  · exfalso
    have := Subgroup.card_le_of_le hRP
    rw [hcard, hR, pow_zero] at this
    omega
  · left
    exact (Subgroup.eq_of_le_of_card_ge hRP (by rw [hcard, hR, pow_one])).symm
  · right
    have : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hH]; positivity)
    exact Subgroup.eq_of_le_of_card_ge hPH (by rw [hcard, hH])

end Crit

end CFSG.Quasithin.MS93.S46
