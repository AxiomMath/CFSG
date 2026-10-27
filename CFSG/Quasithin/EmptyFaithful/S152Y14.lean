module

public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.EmptyFaithful.S14117Star
public import CFSG.Quasithin.EmptyFaithful.S152Y02

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G]

section General

variable {T Mc M : Subgroup G}

theorem isSylowTwoOf_Tb (h : Data T Mc M) :
    IsSylowTwoOf (autOn T (V154 T Mc M)) (autOn M (V154 T Mc M)) :=
  B2F.isSylowTwoOf_autI h.hV h.hMV (isSylowTwoOf_of_le151 h.qtfe.sylow h.T_le)

theorem Tb_le (h : Data T Mc M) : autOn T (V154 T Mc M) ≤ autOn M (V154 T Mc M) :=
  A4.autOn_mono h.T_le

theorem mBar0_normalized (T Mc M : Subgroup G) :
    ∀ g ∈ autOn M (V154 T Mc M), ∀ y ∈ mBar0 T Mc M, g * y * g⁻¹ ∈ mBar0 T Mc M :=
  fun _ hg _ hy => JhatOn_normalized hg hy

theorem mBar0_normalizer (T Mc M : Subgroup G) :
    autOn M (V154 T Mc M) ≤ Subgroup.normalizer (mBar0 T Mc M : Set (MulAut (V154 T Mc M))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => mBar0_normalized T Mc M g hg x hx, fun hx => ?_⟩
  have := mBar0_normalized T Mc M g⁻¹ ((autOn M (V154 T Mc M)).inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem centralizes_field (h : Data T Mc M) :
    ⁅rcOf Mc M ⊔ yOf152 T Mc M, M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)⁆ ≤ pCoreOf 2 M := by
  have hc := Hyp14117.commutator_conjClosure_le h.qtfe h.hyp (y0Of_le T Mc M)
  rw [Subgroup.commutator_comm]
  refine le_trans (Subgroup.commutator_mono le_rfl ?_) hc
  exact sup_le (le_conjClosure _ _) (oTwoUpper_le _)

theorem unique_of_Yb_eq (hs : Setting152 T Mc M) (h : Data T Mc M) (h2 : StageLemma15202)
    (hYb : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M)) :
    IsUniqueM (yOf152 T Mc M ⊔ T) M := by
  have hTM : T ≤ M := h.T_le
  have hsyl0 := A4.isSylowTwoOf_inf_normal (isSylowTwoOf_Tb h) (mBar0_le T Mc M)
    (mBar0_normalizer T Mc M)
  set Eb : Subgroup (MulAut (V154 T Mc M)) := oTwoUpper (mBar0 T Mc M) with hEb
  set S0 : Subgroup (MulAut (V154 T Mc M)) := autOn T (V154 T Mc M) ⊓ mBar0 T Mc M with hS0
  have hM0 : mBar0 T Mc M = Eb ⊔ S0 := eq_oTwoUpper_sup_of_isSylowTwoOf hsyl0
  refine h2 G T Mc M hs (yOf152 T Mc M ⊔ T) le_sup_right (sup_le h.yOf_le_M hTM) (Or.inl ?_)
  intro m hm
  have hmM : m ∈ M := preOn_le _ _ _ hm
  obtain ⟨-, hmN, hmb⟩ := mem_preOn.mp hm
  have hSN : S0 ≤ Subgroup.normalizer (Eb : Set (MulAut (V154 T Mc M))) :=
    inf_le_right.trans (le_normalizer_oTwoUpper _)
  have hmul : ((Eb ⊔ S0 : Subgroup (MulAut (V154 T Mc M))) : Set (MulAut (V154 T Mc M))) =
      (Eb : Set (MulAut (V154 T Mc M))) * (S0 : Set (MulAut (V154 T Mc M))) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSN
  have hmb' : conjAct (V154 T Mc M) ⟨m, hmN⟩ ∈
      (Eb : Set (MulAut (V154 T Mc M))) * (S0 : Set (MulAut (V154 T Mc M))) := by
    rw [← hmul, ← hM0]
    exact hmb
  obtain ⟨eb, heb, sb, hsb, hes⟩ := hmb'
  rw [← hYb] at heb
  obtain ⟨y, hyN, hyY, hye⟩ := mem_autOn_iff_exists.mp heb
  obtain ⟨t, htN, htT, hts⟩ := mem_autOn_iff_exists.mp hsb.1
  have hytN : y * t ∈ Subgroup.normalizer (V154 T Mc M : Set G) := Subgroup.mul_mem _ hyN htN
  have hconj : conjAct (V154 T Mc M) ⟨y * t, hytN⟩ = conjAct (V154 T Mc M) ⟨m, hmN⟩ := by
    have : (⟨y * t, hytN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) = ⟨y, hyN⟩ * ⟨t, htN⟩ := rfl
    rw [this, map_mul, hye, hts]
    exact hes
  have hc : (y * t)⁻¹ * m ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
    (conjAct_eq_iff hytN hmN).mp hconj
  have hyM : y ∈ M := h.yOf_le_M hyY
  have hcM : (y * t)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (M.mul_mem hyM (h.T_le htT))) hmM
  exact ⟨y * t, Subgroup.mul_mem_sup hyY htT, (y * t)⁻¹ * m, ⟨hcM, hc⟩, mul_inv_cancel_left _ _⟩

theorem normal_of_frattini (h : Data T Mc M)
    (hF : (M : Set G) = ((M ⊓ Mc : Subgroup G) : Set G) * (oTwoUpper (m0Of T Mc M) : Set G)) :
    M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := by
  intro x hx
  have hx' : x ∈ ((M ⊓ Mc : Subgroup G) : Set G) * (oTwoUpper (m0Of T Mc M) : Set G) := by
    rw [← hF]; exact hx
  obtain ⟨a, ha, y0, hy0, rfl⟩ := hx'
  exact Subgroup.mul_mem _ (h.inf_le_normalizer_yOf ha) (y0Of_le_normalizer_yOf T Mc M hy0)

end General

end S152Y

end CFSG.Quasithin
