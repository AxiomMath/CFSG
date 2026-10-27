module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G26
public import CFSG.Quasithin.Vol2.Ch10SecQ9G14
public import CFSG.Quasithin.Vol2.Ch10SecQ9G25

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

omit [Finite G] in
theorem image_le_normalizer {S : Type*} [Group S] (π : ↥J →* S) (hLJ : L ≤ J) {R : Subgroup G}
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) :
    (R.subgroupOf J).map π ≤ Subgroup.normalizer ((piL π hLJ).range : Set S) := by
  have key : ∀ r : ↥J, (r : G) ∈ R → ∀ l : ↥L, ∃ l' : ↥L,
      piL π hLJ l' = π r * piL π hLJ l * (π r)⁻¹ := by
    intro r hr l
    refine ⟨⟨r * l * (r : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hRL hr) l).mp l.2⟩, ?_⟩
    rw [piL_apply, piL_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rintro _ ⟨r, hr', rfl⟩
  have hr : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨l, rfl⟩
    obtain ⟨l', hl'⟩ := key r hr l
    exact ⟨l', hl'⟩
  · rintro ⟨l, hl⟩
    obtain ⟨l', hl'⟩ := key r⁻¹ (R.inv_mem hr) l
    refine ⟨l', ?_⟩
    rw [hl', hl, map_inv]
    group

theorem Conf.false_of_case5_L4 (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (h1011 : Stmt10_1_1) (h318 : A318Facts) (h36' : A36ForSQTK)
    (hE : Ch11.SecA.FactA318ExclTwo) (hK7L4 : FactK7L4) (hL4A : FactL4Aut)
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (e : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (h5 : Case10_1_1Five T L I) : False := by
  have hyp := c.hyp
  have hwt : t * w * t⁻¹ ∈ fsuUL T L I := by
    have h1 := c.claim.1
    rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L c.ht),
      SecA.mem_conjugate_iff] at h1
    exact h1
  rcases dichotomy_case5 h37 h38 h322 h1011 hyp h5 hwt with ⟨l, hl, hl3, hlc⟩ | ⟨g₀, hg₀, hT1⟩
  ·
    have hyLt : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
      rw [SecA.mem_conjugate_iff]
      simpa [mul_assoc] using hl
    have hy3 : orderOf (t⁻¹ * l * t) = 3 := by
      have := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective l
      rw [← hl3, ← this]
      simp
    have hyw : t⁻¹ * l * t ∈ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t⁻¹ * l * t * w = t⁻¹ * (l * (t * w * t⁻¹)) * t := by group
        _ = t⁻¹ * ((t * w * t⁻¹) * l) * t := by rw [hlc]
        _ = w * (t⁻¹ * l * t) := by group
    have hyJ := Conf.mem_J_of_L4 c h38 h318 h36' hE hK7L4 hVe hq hCJ e hyw hy3
    exact Conf.false_of_y c h37 hVe hCJ eL e (fun a b ha hb hab => sl4_false ha hb hab) hyLt hy3
      hyJ
  have hTw := Conf.Tw_eq_T1_of_flag c h37 h38 (x := g₀ * t) (by
    rw [show g₀ * t * w * (g₀ * t)⁻¹ = g₀ * (t * w * t⁻¹) * g₀⁻¹ by group]
    exact hT1)
  obtain ⟨-, s, hsT, hsL, W, hWV1, hLW, -, -, -, hni⟩ := h5
  have hsTw : s ∈ T ⊓ Subgroup.centralizer ({w} : Set G) := hTw ▸ ⟨hsT, hsL⟩
  have hsJ : s ∈ Subgroup.normalizer (J : Set G) := c.Tw_le_normalizer hsTw
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨eJ⟩ := nonempty_quotient_equiv hVe hJN hCJ e
  have hR : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G) ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal c.sylow c.J_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer c.J_le).mp c.normal)
  have hRL : T ⊓ Subgroup.centralizer ({w} : Set G) ⊓ J ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans ((c.Tw_le_T1 h37 h38).trans inf_le_right)
  obtain ⟨l₀, hl₀, hinner⟩ := exists_inner_of_aut eJ c.le (fun α hα => hL4A _ _
    (image_isSylowTwoOf hR (piJ eJ) (piJ_surjective eJ)) (image_le_normalizer _ c.le hRL)
    (image_perfect _ c.le (SecA.perfect_L hyp.fsu.maximal.1))
    (image_quot_equiv _ c.le (piJ_ker eJ) eL) α hα) hsJ hsL
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) :=
    (pCoreOf_L_le_centralizer hyp h1011).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hWV1.trans hV1V)))
  exact hni (SecB.isXSectionIso_of_inner hl₀ hLW hO hinner)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
