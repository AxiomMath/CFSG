module

public import CFSG.Quasithin.EmptyFaithful.S152He9Y2
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.EmptyFaithful.S152Y02

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjAct_comm_of_mem {V : Subgroup G} {y r : G} (hy : y ∈ Subgroup.normalizer (V : Set G))
    (hr : r ∈ Subgroup.normalizer (V : Set G))
    (h : y * r * y⁻¹ * r⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    conjAct V ⟨y, hy⟩ * conjAct V ⟨r, hr⟩ = conjAct V ⟨r, hr⟩ * conjAct V ⟨y, hy⟩ := by
  have h1 : conjAct V (⟨y, hy⟩ * ⟨r, hr⟩ * ⟨y, hy⟩⁻¹ * ⟨r, hr⟩⁻¹) = 1 := by
    apply A4.conjAct_eq_one_iff.mpr
    simpa using h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h1)

structure YCtx (T Mc M : Subgroup G) : Prop where
  data : S152Y.Data T Mc M
  c3 : Lemma15203Concl T Mc M
  card_five : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 5
  cent_le : yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M

namespace YCtx

variable {T Mc M : Subgroup G} (c : YCtx T Mc M)

include c

theorem hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := c.data.hMV

theorem normal : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := c.c3.normal

theorem hYM : yOf152 T Mc M ≤ M := c.data.yOf_le_M

theorem hYV : yOf152 T Mc M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := c.hYM.trans c.hMV

theorem hRM : rcOf Mc M ≤ M := c.data.rc_le_M

theorem hRY : rcOf Mc M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := c.hRM.trans c.normal

theorem hO2 : pCoreOf 2 M ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
  refine c.data.h1515.reduced.2.2.2 (pCoreOf 2 M) (pCoreOf_le 2 M) (le_normalizer_pCoreOf 2 M)
    fun d hd => ?_
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 M) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

theorem O2M_le_rc : pCoreOf 2 M ≤ rcOf Mc M := by
  have hle : pCoreOf 2 M ≤ Mc ⊓ M :=
    le_inf (c.hO2.trans c.data.h1515.centralizer_le) (pCoreOf_le 2 M)
  exact le_pCoreOf_of_le_normalizer hle (inf_le_right.trans (le_normalizer_pCoreOf 2 M))
    (pCoreOf_isPGroup 2 M)

theorem pCoreY_le : pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 M :=
  le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 _).trans c.hYM)
    (c.normal.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem pCoreY_eq : pCoreOf 2 (yOf152 T Mc M) =
    yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
  apply le_antisymm
  · exact le_inf (pCoreOf_le 2 _) (c.pCoreY_le.trans c.hO2)
  · have hp : IsPGroup 2 (yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) :=
      (pCoreOf_isPGroup 2 M).to_le c.cent_le
    refine le_pCoreOf_of_le_normalizer inf_le_left ?_ hp
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgN : g ∈ Subgroup.normalizer (V154 T Mc M : Set G) := c.hYV hg
    constructor
    · intro hx
      obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x).mp hxY, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
      have h1 : g⁻¹ * v * g ∈ V154 T Mc M := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
        simpa using this
      have h2 := Subgroup.mem_centralizer_iff.mp hxC (g⁻¹ * v * g) h1
      calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
        _ = (g * x * g⁻¹) * v := by group
    · intro hx
      obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x).mpr hxY, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
      have h1 : g * v * g⁻¹ ∈ V154 T Mc M := (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
      have h2 := Subgroup.mem_centralizer_iff.mp hxC (g * v * g⁻¹) h1
      calc v * x = g⁻¹ * ((g * v * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h2]
        _ = x * v := by group

theorem relIndex_five : (pCoreOf 2 (yOf152 T Mc M)).relIndex (yOf152 T Mc M) = 5 := by
  rw [c.pCoreY_eq, ← card_autOn_eq_relIndex c.hYV]
  exact c.card_five

theorem pCoreY_le_rc : pCoreOf 2 (yOf152 T Mc M) ≤ rcOf Mc M := c.pCoreY_le.trans c.O2M_le_rc

theorem inf_rc_le_centralizer :
    yOf152 T Mc M ⊓ rcOf Mc M ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
  have hp : IsPGroup 2 (yOf152 T Mc M ⊓ rcOf Mc M : Subgroup G) :=
    (pCoreOf_isPGroup 2 _).to_le inf_le_right
  have hI : yOf152 T Mc M ⊓ rcOf Mc M ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    inf_le_left.trans c.hYV
  have h2 : IsPGroup 2 (autOn (yOf152 T Mc M ⊓ rcOf Mc M) (V154 T Mc M)) := isPGroup_autOn hp hI
  have h3 : autOn (yOf152 T Mc M ⊓ rcOf Mc M) (V154 T Mc M) ≤ autOn (yOf152 T Mc M) (V154 T Mc M) :=
    A4.autOn_mono inf_le_left
  have hdvd : Nat.card (autOn (yOf152 T Mc M ⊓ rcOf Mc M) (V154 T Mc M)) ∣ 5 := by
    rw [← c.card_five]
    exact Subgroup.card_dvd_of_le h3
  have hbot : autOn (yOf152 T Mc M ⊓ rcOf Mc M) (V154 T Mc M) = ⊥ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h2
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h5 : 2 ∣ 5 := (dvd_pow_self 2 hk0).trans hdvd
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  intro x hx
  have hmem : conjAct (V154 T Mc M) ⟨x, hI hx⟩ ∈ autOn (yOf152 T Mc M ⊓ rcOf Mc M) (V154 T Mc M) :=
    mem_autOn_iff_exists.mpr ⟨x, hI hx, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact A4.conjAct_eq_one_iff.mp hmem

theorem nt : ∃ r ∈ rcOf Mc M, ∃ y ∈ yOf152 T Mc M,
    r * y * r⁻¹ * y⁻¹ ∉ pCoreOf 2 (yOf152 T Mc M) := by
  by_contra hcon
  push Not at hcon
  have hbot : ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨y, hyN, hyY, rfl⟩ := mem_autOn_iff_exists.mp ha
    obtain ⟨r, hrN, hrR, rfl⟩ := mem_autOn_iff_exists.mp hb
    rw [Subgroup.mem_bot]
    have hmem : y * r * y⁻¹ * r⁻¹ ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
      have h1 := Subgroup.inv_mem _ (hcon r hrR y hyY)
      have h2 : (r * y * r⁻¹ * y⁻¹)⁻¹ = y * r * y⁻¹ * r⁻¹ := by group
      rw [h2, c.pCoreY_eq] at h1
      exact (Subgroup.mem_inf.1 h1).2
    have := conjAct_comm_of_mem hyN hrN hmem
    exact commutatorElement_eq_one_iff_mul_comm.mpr this
  have h2 := c.c3.comm_eq
  rw [le_bot_iff.mp hbot] at h2
  have h3 := c.card_five
  rw [h2, Subgroup.card_bot] at h3
  omega

theorem iso : IsSylowTwoOf (rcOf Mc M) (yOf152 T Mc M ⊔ rcOf Mc M) ∧
    (rcOf Mc M).relIndex (yOf152 T Mc M ⊔ rcOf Mc M) = 5 ∧
    (Nonempty (OTwoQuot (yOf152 T Mc M ⊔ rcOf Mc M) ≃* DihedralGroup 5) ∨
      Nonempty (OTwoQuot (yOf152 T Mc M ⊔ rcOf Mc M) ≃* ↥(CFSG.Open.Sz 0))) :=
  oTwoQuot_sup_iso (pCoreOf_isPGroup 2 _) c.hRY c.relIndex_five c.pCoreY_le_rc c.nt

theorem normalizer_rc_le : (yOf152 T Mc M ⊔ rcOf Mc M) ⊓
    Subgroup.normalizer (rcOf Mc M : Set G) ≤ rcOf Mc M := by
  intro g hg
  obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.1 hg
  have hset : ((yOf152 T Mc M ⊔ rcOf Mc M : Subgroup G) : Set G) =
      (yOf152 T Mc M : Set G) * (rcOf Mc M : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ c.hRY
  have hg' : g ∈ (yOf152 T Mc M : Set G) * (rcOf Mc M : Set G) := by rw [← hset]; exact hgL
  obtain ⟨y, hyY, r, hrR, rfl⟩ := hg'
  have hyN : y ∈ Subgroup.normalizer (rcOf Mc M : Set G) := by
    have : y = (y * r) * r⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hgN (Subgroup.inv_mem _ (Subgroup.le_normalizer hrR))
  suffices hy : y ∈ rcOf Mc M from (rcOf Mc M).mul_mem hy hrR
  have hyVN : y ∈ Subgroup.normalizer (V154 T Mc M : Set G) := c.hYV hyY
  set Cy : Subgroup (MulAut (V154 T Mc M)) := autOn (yOf152 T Mc M) (V154 T Mc M) ⊓
    Subgroup.centralizer (autOn (rcOf Mc M) (V154 T Mc M) : Set (MulAut (V154 T Mc M))) with hCy
  have hCybot : Cy = ⊥ := by
    have hdvd : Nat.card Cy ∣ 5 := by
      rw [← c.card_five]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hle : Cy ≤ autOn (yOf152 T Mc M) (V154 T Mc M) := inf_le_left
      have heq : Cy = autOn (yOf152 T Mc M) (V154 T Mc M) :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h5, c.card_five])
      have hc : ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (heq ▸ inf_le_right)
      have h2 := c.c3.comm_eq
      rw [hc] at h2
      have h3 := c.card_five
      rw [h2, Subgroup.card_bot] at h3
      omega
  have hy1 : conjAct (V154 T Mc M) ⟨y, hyVN⟩ ∈ Cy := by
    refine Subgroup.mem_inf.2 ⟨mem_autOn_iff_exists.mpr ⟨y, hyVN, hyY, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
    obtain ⟨r', hr'N, hr'R, rfl⟩ := mem_autOn_iff_exists.mp hb
    have hmem : y * r' * y⁻¹ * r'⁻¹ ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
      apply c.inf_rc_le_centralizer
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have e : y * r' * y⁻¹ * r'⁻¹ = y * (r' * y⁻¹ * r'⁻¹) := by group
        rw [e]
        exact (yOf152 T Mc M).mul_mem hyY
          ((Subgroup.mem_normalizer_iff.mp (c.hRY hr'R) y⁻¹).mp ((yOf152 T Mc M).inv_mem hyY))
      · exact (rcOf Mc M).mul_mem
          ((Subgroup.mem_normalizer_iff.mp hyN r').mp hr'R) ((rcOf Mc M).inv_mem hr'R)
    exact (conjAct_comm_of_mem hyVN hr'N hmem).symm
  rw [hCybot, Subgroup.mem_bot] at hy1
  have hyC : y ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
    A4.conjAct_eq_one_iff.mp hy1
  exact c.O2M_le_rc (c.cent_le ⟨hyY, hyC⟩)

end YCtx

end CFSG.Quasithin.He9
