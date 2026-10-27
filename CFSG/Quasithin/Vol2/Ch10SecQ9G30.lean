module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G10

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] {T L I : Subgroup G}

noncomputable abbrev Kw (T L I : Subgroup G) (w : ↥(fsuVM T L I)) :
    Subgroup (MulAut ↥(fsuVM T L I)) :=
  autOn (fsuL0 T L ⊔ T) (fsuVM T L I) ⊓ MulAction.stabilizer (MulAut ↥(fsuVM T L I)) w

@[expose] noncomputable def autW {w : ↥(fsuVM T L I)} (g : G)
    (hgN : g ∈ Subgroup.normalizer (fsuVM T L I : Set G)) (hgL : g ∈ fsuL0 T L ⊔ T)
    (hgw : g * (w : G) * g⁻¹ = w) : ↥(Kw T L I w) :=
  ⟨conjAct (fsuVM T L I) ⟨g, hgN⟩, ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hgL, rfl⟩,
    by
      show conjAct (fsuVM T L I) ⟨g, hgN⟩ w = w
      exact Subtype.ext (by rw [coe_conjAct_apply]; exact hgw)⟩

theorem autW_val {w : ↥(fsuVM T L I)} (g : G)
    (hgN : g ∈ Subgroup.normalizer (fsuVM T L I : Set G)) (hgL : g ∈ fsuL0 T L ⊔ T)
    (hgw : g * (w : G) * g⁻¹ = w) :
    ((autW g hgN hgL hgw : ↥(Kw T L I w)) : MulAut ↥(fsuVM T L I)) =
      conjAct (fsuVM T L I) ⟨g, hgN⟩ := rfl

theorem autW_eq_one_iff {w : ↥(fsuVM T L I)} {g : G}
    (hgN : g ∈ Subgroup.normalizer (fsuVM T L I : Set G)) (hgL : g ∈ fsuL0 T L ⊔ T)
    (hgw : g * (w : G) * g⁻¹ = w) :
    autW g hgN hgL hgw = 1 ↔ g ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  rw [← conjAct_eq_one_iff' (fsuVM T L I) ⟨g, hgN⟩]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [autW_val] at this
  · intro h
    apply Subtype.ext
    rw [autW_val]
    exact h

theorem exists_thetaL [Finite G] (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I)
    {w : ↥(fsuVM T L I)} (hwL : (w : G) ∈ Subgroup.centralizer (L : Set G)) :
    ∃ θ : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(Kw T L I w), Function.Injective θ ∧
      ∀ l : ↥L, ((θ (l : ↥L ⧸ CFSG.pCore 2 ↥L) : ↥(Kw T L I w)) : MulAut ↥(fsuVM T L I)) =
        conjAct (fsuVM T L I) ⟨l, (SecA.le_fsuL0 T L).trans
          (SecA.fsuL0_le_normalizer_fsuVM T L I) l.2⟩ := by
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hmem : ∀ l : ↥L, (conjAct (fsuVM T L I)).comp (Subgroup.inclusion hLN) l ∈ Kw T L I w :=
    fun l => (autW (w := w) (l : G) (hLN l.2) (Subgroup.mem_sup_left (SecA.le_fsuL0 T L l.2))
      (by rw [Subgroup.mem_centralizer_iff.mp hwL l l.2, mul_inv_cancel_right])).2
  set lamL : ↥L →* ↥(Kw T L I w) :=
    ((conjAct (fsuVM T L I)).comp (Subgroup.inclusion hLN)).codRestrict _ hmem with hlam
  have hker : CFSG.pCore 2 ↥L ≤ lamL.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show conjAct (fsuVM T L I) ⟨(x : G), hLN x.2⟩ = 1
    rw [conjAct_eq_one_iff']
    refine pCoreOf_L_le_centralizer hyp h1011 ?_
    exact ⟨x, hx, rfl⟩
  refine ⟨QuotientGroup.lift _ lamL hker, ?_, fun l => rfl⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [QuotientGroup.lift_mk] at hq
    have h1 : conjAct (fsuVM T L I) ⟨(l : G), hLN l.2⟩ = 1 := congrArg Subtype.val hq
    rw [conjAct_eq_one_iff'] at h1
    have hLNV1 : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
    have h2 := mem_pCoreOf_of_centralizer h37 h38 h1011 hyp l.2
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLNV1) h1)
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨l', hl', hl'l⟩ := h2
    have : l = l' := Subtype.ext hl'l.symm
    rw [this]
    exact hl'

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
