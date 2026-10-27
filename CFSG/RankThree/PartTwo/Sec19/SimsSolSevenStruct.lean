module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenDefs
public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenA7
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolSeven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjOn {K R : Subgroup G} (h : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) :
    ↥K →* MulAut ↥R where
  toFun k :=
    { toFun := fun r => ⟨(k : G) * r * (k : G)⁻¹, h k k.2 r r.2⟩
      invFun := fun r => ⟨(k : G)⁻¹ * r * (k : G), by
        have := h (k : G)⁻¹ (K.inv_mem k.2) r r.2
        simpa using this⟩
      left_inv := fun r => by ext; simp [mul_assoc]
      right_inv := fun r => by ext; simp [mul_assoc]
      map_mul' := fun r r' => by ext; simp [mul_assoc] }
  map_one' := by ext r; simp
  map_mul' := fun k k' => by ext r; simp [mul_assoc]

theorem conj_mem_blockU {X : Subgroup G} {x : G} (hx : x ∈ X) {w : G} (hw : w ∈ blockU X) :
    x * w * x⁻¹ ∈ blockU X :=
  (Subgroup.mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_right (blockQ X) X hx) w).mp
    hw

theorem mem_pCore_iff {X : Subgroup G} (x : ↥X) :
    x ∈ CFSG.pCore 2 ↥X ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 X := by
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

@[expose] def actX (X : Subgroup G) : ↥X →* MulAut ↥(blockU X) :=
  conjOn (K := X) (R := blockU X) fun _ hx _ hw => conj_mem_blockU hx hw

theorem actX_apply {X : Subgroup G} (x : ↥X) (w : ↥(blockU X)) :
    ((actX X x w : ↥(blockU X)) : G) = (x : G) * w * (x : G)⁻¹ := rfl

namespace Setting

section Basic

variable [Finite G] {M X : Subgroup G} (S : Setting G M X)
include S

theorem W_le_Y : blockU X ≤ blockQ X := fun _ hw => (S.block.1.blockU_le_center hw).1

theorem W_le_X : blockU X ≤ X := blockU_le_self X

theorem Y_comm_W {y w : G} (hy : y ∈ blockQ X) (hw : w ∈ blockU X) : y * w = w * y :=
  Subgroup.mem_centralizer_iff.mp (S.block.1.blockU_le_center hw).2 y hy

theorem W_comm {a b : G} (ha : a ∈ blockU X) (hb : b ∈ blockU X) : a * b = b * a :=
  S.Y_comm_W (S.W_le_Y ha) hb

theorem W_sq {w : G} (hw : w ∈ blockU X) : w ^ 2 = 1 := S.elemU.2 w hw

theorem Y_isPGroup : IsPGroup 2 (blockQ X) :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X

theorem commutator_W_eq : ⁅blockU X, X⁆ = blockU X :=
  SimsTheoremC.commutator_commutator_eq_of_twoResidual S.block.1.eq_twoResidual S.Y_isPGroup
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)

theorem M_normalizes_W {m : G} (hm : m ∈ M) {w : G} (hw : w ∈ blockU X) :
    m * w * m⁻¹ ∈ blockU X := by
  revert w
  have key : blockU X ≤ (blockU X).comap (MulAut.conj m).toMonoidHom := by
    rw [blockU, Subgroup.commutator_le]
    intro y hy x hx
    show m * ⁅y, x⁆ * m⁻¹ ∈ ⁅blockQ X, X⁆
    have e : m * ⁅y, x⁆ * m⁻¹ = ⁅m * y * m⁻¹, m * x * m⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator (S.xnorm.Y_normalized hm hy) (S.normal hm hx)
  intro w hw
  exact key hw

end Basic

variable [Finite G] {M X : Subgroup G}

@[expose] def actM (S : Setting G M X) : ↥M →* MulAut ↥(blockU X) :=
  conjOn (K := M) (R := blockU X) fun _ hm _ hw => S.M_normalizes_W hm hw

theorem actM_apply (S : Setting G M X) (m : ↥M) (w : ↥(blockU X)) :
    ((S.actM m w : ↥(blockU X)) : G) = (m : G) * w * (m : G)⁻¹ := rfl

theorem pCore_le_ker_actX (S : Setting G M X) : CFSG.pCore 2 ↥X ≤ (actX X).ker := by
  intro y hy
  rw [MonoidHom.mem_ker]
  ext w
  rw [actX_apply, MulAut.one_apply, S.Y_comm_W ((mem_pCore_iff y).mp hy) w.2,
    mul_inv_cancel_right]

@[expose] noncomputable def phi (S : Setting G M X) :
    ↥X ⧸ CFSG.pCore 2 ↥X →* MulAut ↥(blockU X) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥X) (actX X) S.pCore_le_ker_actX

theorem phi_mk (S : Setting G M X) (x : ↥X) (w : ↥(blockU X)) :
    ((S.phi (x : ↥X ⧸ CFSG.pCore 2 ↥X) w : ↥(blockU X)) : G) = (x : G) * w * (x : G)⁻¹ := rfl

section Action

variable (S : Setting G M X)
include S

theorem nonempty_theta :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(alternatingGroup (Fin 7))) := by
  obtain ⟨⟨α, hα, hker⟩, -⟩ := S.type
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

theorem isSimpleGroup_Xbar : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := by
  obtain ⟨θ⟩ := S.nonempty_theta
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  exact θ.isSimpleGroup

theorem exists_not_comm : ∃ x ∈ X, ∃ w ∈ blockU X, x * w * x⁻¹ * w⁻¹ ∉ blockZ X := by
  by_contra hcon'
  have hcon : ∀ x ∈ X, ∀ w ∈ blockU X, x * w * x⁻¹ * w⁻¹ ∈ blockZ X := fun x hx w hw => by
    by_contra h
    exact hcon' ⟨x, hx, w, hw, h⟩
  have hle : ⁅blockU X, X⁆ ≤ blockZ X := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    have h1 := hcon x hx (w⁻¹) ((blockU X).inv_mem hw)
    have h2 : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹ * (w⁻¹)⁻¹) * w⁻¹ := by
      simp only [commutatorElement_def, inv_inv]; group
    rw [h2]
    have hZn : w * (x * w⁻¹ * x⁻¹ * (w⁻¹)⁻¹) * w⁻¹ = x * w⁻¹ * x⁻¹ * (w⁻¹)⁻¹ := by
      have hz := h1
      have hzU : x * w⁻¹ * x⁻¹ * (w⁻¹)⁻¹ ∈ blockU X := hz.1
      rw [S.W_comm hw hzU, mul_inv_cancel_right]
    rw [hZn]
    exact h1
  rw [S.commutator_W_eq] at hle
  exact (lt_irrefl _ (lt_of_lt_of_le S.block.1.blockZ_lt_blockU hle))

theorem phi_injective : Function.Injective S.phi := by
  have := S.isSimpleGroup_Xbar
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.phi.ker with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx, w, hw, hne⟩ := S.exists_not_comm
    have hmem : ((⟨x, hx⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ S.phi.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have h1 := congrArg Subtype.val (congrArg (fun f : MulAut ↥(blockU X) => f ⟨w, hw⟩) hmem)
    simp only [MulAut.one_apply] at h1
    rw [S.phi_mk] at h1
    apply hne
    rw [h1, mul_inv_cancel]
    exact (blockZ X).one_mem

abbrev Zw (X : Subgroup G) : Subgroup ↥(blockU X) := (blockZ X).subgroupOf (blockU X)

theorem phi_fix (γ : ↥X ⧸ CFSG.pCore 2 ↥X) {z : ↥(blockU X)} (hz : z ∈ Zw X) : S.phi γ z = z := by
  induction γ using QuotientGroup.induction_on with
  | H x =>
    apply Subtype.ext
    rw [S.phi_mk]
    have hz' : (z : G) ∈ blockZ X := hz
    rw [Subgroup.mem_centralizer_iff.mp hz'.2 x x.2, mul_inv_cancel_right]

theorem faithful_quot (γ : ↥X ⧸ CFSG.pCore 2 ↥X)
    (hγ : ∀ u : ↥(blockU X), S.phi γ u * u⁻¹ ∈ Zw X) : γ = 1 := by
  have := S.isSimpleGroup_Xbar
  let K0 : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
    { carrier := {δ | ∀ u : ↥(blockU X), S.phi δ u * u⁻¹ ∈ Zw X}
      one_mem' := fun u => by simp
      mul_mem' := fun {a b} ha hb u => by
        have h1 := ha (S.phi b u)
        have h2 := hb u
        have e : S.phi (a * b) u * u⁻¹ = (S.phi a (S.phi b u) * (S.phi b u)⁻¹) *
            (S.phi b u * u⁻¹) := by
          rw [map_mul, MulAut.mul_apply]; group
        rw [e]
        exact (Zw X).mul_mem h1 h2
      inv_mem' := fun {a} ha u => by
        have h1 := ha (S.phi a⁻¹ u)
        have e : S.phi a (S.phi a⁻¹ u) = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
        rw [e] at h1
        have h2 := (Zw X).inv_mem h1
        rwa [mul_inv_rev, inv_inv] at h2 }
  have hK0 : K0.Normal := by
    refine ⟨fun a ha b u => ?_⟩
    have h1 := ha (S.phi b⁻¹ u)
    have h2 := S.phi_fix b h1
    have e : S.phi (b * a * b⁻¹) u * u⁻¹ =
        S.phi b (S.phi a (S.phi b⁻¹ u) * (S.phi b⁻¹ u)⁻¹) := by
      rw [map_mul, map_inv, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
      have e2 : S.phi b ((S.phi b)⁻¹ u) = u := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      rw [map_inv, e2]
    rw [e, h2]
    exact h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K0 with h | h
  · have hm : γ ∈ K0 := hγ
    rw [h] at hm
    exact (Subgroup.mem_bot.mp hm)
  · exfalso
    obtain ⟨x, hx, w, hw, hne⟩ := S.exists_not_comm
    have hmem : ((⟨x, hx⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ K0 := h ▸ Subgroup.mem_top _
    have h1 := hmem ⟨w, hw⟩
    exact hne h1

theorem isElementaryAbelian_tildeU : CFSG.IsElementaryAbelian 2 (tildeU X) := by
  have hcomm : ∀ a b : tildeU X, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (S.W_comm a.2 b.2)
  refine { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    have h2 : a ^ 2 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact S.W_sq a.2)
    rw [h2]
    rfl

theorem card_tildeU : Nat.card (tildeU X) = 16 := by
  haveI := S.isElementaryAbelian_tildeU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 (tildeU X)).exists_card_eq
  have h := CFSG.pRank_eq_of_card_eq_pow Nat.one_lt_two hn
  rw [S.type.2] at h
  rw [hn, ← h]
  norm_num

theorem card_W_eq : Nat.card ↥(blockU X) = 16 * Nat.card ↥(Zw X) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Zw X)]
  congr 1
  exact S.card_tildeU

theorem invariant_char_trivial (χ : ↥(blockU X) →* Multiplicative (ZMod 2))
    (hχ : ∀ (γ : ↥X ⧸ CFSG.pCore 2 ↥X) (u : ↥(blockU X)), χ (S.phi γ u) = χ u) : χ = 1 := by
  have hle : ⁅blockU X, X⁆ ≤ χ.ker.map (blockU X).subtype := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    have hw' : x * w⁻¹ * x⁻¹ ∈ blockU X := conj_mem_blockU hx ((blockU X).inv_mem hw)
    refine ⟨⟨w, hw⟩ * ⟨x * w⁻¹ * x⁻¹, hw'⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul]
      have e : (⟨x * w⁻¹ * x⁻¹, hw'⟩ : ↥(blockU X)) =
          S.phi ((⟨x, hx⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ⟨w, hw⟩⁻¹ := by
        apply Subtype.ext
        rw [S.phi_mk]
        rfl
      rw [e, hχ, map_inv]
      exact mul_inv_cancel _
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, commutatorElement_def]
      group
  ext u
  have hu : (u : G) ∈ ⁅blockU X, X⁆ := by rw [S.commutator_W_eq]; exact u.2
  obtain ⟨u', hu', hu'u⟩ := hle hu
  have : u' = u := Subtype.ext hu'u
  rw [this] at hu'
  rw [MonoidHom.one_apply]
  exact hu'

theorem blockZ_eq_bot : blockZ X = ⊥ := by
  obtain ⟨θ⟩ := S.nonempty_theta
  have hZ := eq_bot_of_forall_invariant_trivial θ (U := ↥(blockU X))
    (fun a b => Subtype.ext (S.W_comm a.2 b.2))
    (fun a => Subtype.ext (by rw [SubgroupClass.coe_pow]; exact S.W_sq a.2))
    S.phi (Zw X) (fun z hz γ => S.phi_fix γ hz) S.card_W_eq S.faithful_quot
    S.invariant_char_trivial
  rw [eq_bot_iff]
  intro z hz
  have hzm : (⟨z, hz.1⟩ : ↥(blockU X)) ∈ Zw X := hz
  rw [hZ, Subgroup.mem_bot] at hzm
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hzm

theorem eq_one_of_mem_W_of_mem_C {w : G} (hw : w ∈ blockU X)
    (hc : w ∈ Subgroup.centralizer (X : Set G)) : w = 1 := by
  have h : w ∈ blockZ X := ⟨hw, hc⟩
  rw [S.blockZ_eq_bot, Subgroup.mem_bot] at h
  exact h

theorem card_blockU : Nat.card ↥(blockU X) = 16 := by
  rw [S.card_W_eq]
  have : Zw X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : G) ∈ blockZ X := hz
    rw [S.blockZ_eq_bot, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (Subtype.ext hz')
  rw [this, Subgroup.card_bot, mul_one]

theorem Y_le_Q : blockQ X ≤ CFSG.Open.pCoreOf 2 M := S.xnorm.Y_le_Q

theorem W_le_Q : blockU X ≤ CFSG.Open.pCoreOf 2 M := S.W_le_Y.trans S.Y_le_Q

theorem hom_eq_one {B : Type*} [Group B] (hB : IsPGroup 2 B) (f : ↥X →* B) : f = 1 := by
  have hq : IsPGroup 2 (↥X ⧸ f.ker) :=
    (hB.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have h := S.block.1.eq_twoResidual f.ker hq
  ext l
  have : l ∈ f.ker := by rw [h]; exact Subgroup.mem_top l
  simpa using this

theorem comm_mem_W {m : G} (hmY : ∀ x ∈ X, ⁅m, x⁆ ∈ blockQ X) {x : G} (hx : x ∈ X) :
    ⁅m, x⁆ ∈ blockU X := by
  classical
  have : ((blockU X).subgroupOf (blockQ X)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [S.Y_comm_W g.2 hn]
      group
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ blockU X
    rw [h1]
    exact hn⟩
  have hq2 : IsPGroup 2 (↥(blockQ X) ⧸ (blockU X).subgroupOf (blockQ X)) :=
    S.Y_isPGroup.to_quotient _
  have hY : ∀ x' : ↥X, ⁅m, (x' : G)⁆ ∈ blockQ X := fun x' => hmY x' x'.2
  let f : ↥X →* (↥(blockQ X) ⧸ (blockU X).subgroupOf (blockQ X)) :=
    { toFun := fun x' => QuotientGroup.mk ⟨⁅m, (x' : G)⁆, hY x'⟩
      map_one' := by
        have : (⟨⁅m, ((1 : ↥X) : G)⁆, hY 1⟩ : ↥(blockQ X)) = 1 := Subtype.ext (by simp)
        rw [this]
        exact QuotientGroup.mk_one _
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        set y : G := ⁅m, (b : G)⁆ with hy
        have hyY : y ∈ blockQ X := hY b
        have hxy : ⁅(a : G), y⁆ ∈ blockU X := by
          rw [blockU, Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator a.2 hyY
        have hcalc : (⁅m, (a : G)⁆ * ⁅m, (b : G)⁆)⁻¹ * ⁅m, ((a * b : ↥X) : G)⁆ =
            ⁅(a : G), y⁆ := by
          have e1 : ⁅m, ((a * b : ↥X) : G)⁆ = ⁅m, (a : G)⁆ * ((a : G) * y * (a : G)⁻¹) := by
            rw [Subgroup.coe_mul, hy]
            simp only [commutatorElement_def]
            group
          have e2 : (a : G) * y * (a : G)⁻¹ = ⁅(a : G), y⁆ * y := by
            simp only [commutatorElement_def]; group
          rw [e1, e2]
          have hc := S.Y_comm_W hyY hxy
          calc (⁅m, (a : G)⁆ * y)⁻¹ * (⁅m, (a : G)⁆ * (⁅(a : G), y⁆ * y))
              = y⁻¹ * (⁅(a : G), y⁆ * y) := by group
            _ = ⁅(a : G), y⁆ := by rw [← hc]; group
        have hmem : (⁅m, (a : G)⁆ * ⁅m, (b : G)⁆)⁻¹ * ⁅m, ((a * b : ↥X) : G)⁆ ∈ blockU X := by
          rw [hcalc]
          exact hxy
        have hmem' := (blockU X).inv_mem hmem
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at hmem' ⊢
        exact hmem' }
  have h1 := S.hom_eq_one hq2 f
  have h2 : f ⟨x, hx⟩ = 1 := DFunLike.congr_fun h1 ⟨x, hx⟩
  have h3 : (⟨⁅m, x⁆, hY ⟨x, hx⟩⟩ : ↥(blockQ X)) ∈ (blockU X).subgroupOf (blockQ X) :=
    (QuotientGroup.eq_one_iff _).1 h2
  exact h3

theorem comm_Y_eq_one {m : G} (hmW : ∀ w ∈ blockU X, m * w * m⁻¹ = w)
    (hmY : ∀ x ∈ X, ⁅m, x⁆ ∈ blockQ X) {y : G} (hy : y ∈ blockQ X) : ⁅m, y⁆ = 1 := by
  have hyX : y ∈ X := CFSG.CGT.PushingUpLit.SolK.pCoreOf_le_self X hy
  have hv : ⁅m, y⁆ ∈ blockU X := S.comm_mem_W hmY hyX
  refine S.eq_one_of_mem_W_of_mem_C hv (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
  have hu : ⁅m, x⁆ ∈ blockU X := S.comm_mem_W hmY hx
  have hxy : ⁅x, y⁆ ∈ blockU X := by
    rw [blockU, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hx hy
  have hyc : x * y * x⁻¹ ∈ blockQ X := S.xnorm.Y_normalized (S.le hx) hy
  have hxv : x * ⁅m, y⁆ * x⁻¹ ∈ blockU X := conj_mem_blockU hx hv
  have e1 : ⁅m, x * y * x⁻¹⁆ = x * ⁅m, y⁆ * x⁻¹ := by
    have hc1 : ⁅m, x⁆ * (x * ⁅m, y⁆ * x⁻¹) = (x * ⁅m, y⁆ * x⁻¹) * ⁅m, x⁆ := S.W_comm hu hxv
    have hc2 : ⁅m, x⁆ * (x * y * x⁻¹) = (x * y * x⁻¹) * ⁅m, x⁆ := (S.Y_comm_W hyc hu).symm
    have key : m * (x * y * x⁻¹) * m⁻¹ = (x * ⁅m, y⁆ * x⁻¹) * (x * y * x⁻¹) := by
      have : m * (x * y * x⁻¹) * m⁻¹ = ⁅m, x⁆ * (x * ⁅m, y⁆ * x⁻¹) * (x * y * x⁻¹) * ⁅m, x⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this, hc1, mul_assoc (x * ⁅m, y⁆ * x⁻¹) ⁅m, x⁆, hc2]
      group
    simp only [commutatorElement_def] at key ⊢
    rw [key]
    group
  have e2 : x * y * x⁻¹ = ⁅x, y⁆ * y := by simp only [commutatorElement_def]; group
  have e3 : ⁅m, ⁅x, y⁆ * y⁆ = ⁅m, y⁆ := by
    have hmw := hmW _ hxy
    have hcomm : ⁅x, y⁆ * ⁅m, y⁆ = ⁅m, y⁆ * ⁅x, y⁆ := S.W_comm hxy hv
    have : ⁅m, ⁅x, y⁆ * y⁆ = (m * ⁅x, y⁆ * m⁻¹) * ⁅m, y⁆ * ⁅x, y⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this, hmw, hcomm]
    group
  have h4 : x * ⁅m, y⁆ * x⁻¹ = ⁅m, y⁆ := by rw [← e1, e2, e3]
  calc x * ⁅m, y⁆ = (x * ⁅m, y⁆ * x⁻¹) * x := by group
    _ = ⁅m, y⁆ * x := by rw [h4]

theorem exists_inv_mul_mem_centralizer {m : G} (hmW : ∀ w ∈ blockU X, m * w * m⁻¹ = w)
    (hmY : ∀ x ∈ X, ⁅m, x⁆ ∈ blockQ X) :
    ∃ v ∈ blockU X, v⁻¹ * m ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨θ⟩ := S.nonempty_theta
  have hc0 : ∀ x : ↥X, ⁅m, (x : G)⁆ ∈ blockU X := fun x => S.comm_mem_W hmY x.2
  let c0 : ↥X → ↥(blockU X) := fun x => ⟨⁅m, (x : G)⁆, hc0 x⟩
  have hc0mul : ∀ a b : ↥X, c0 (a * b) = c0 a * S.phi (a : ↥X ⧸ CFSG.pCore 2 ↥X) (c0 b) := by
    intro a b
    apply Subtype.ext
    rw [Subgroup.coe_mul, S.phi_mk]
    show ⁅m, ((a * b : ↥X) : G)⁆ = ⁅m, (a : G)⁆ * ((a : G) * ⁅m, (b : G)⁆ * (a : G)⁻¹)
    rw [Subgroup.coe_mul]
    simp only [commutatorElement_def]
    group
  have hc0Y : ∀ a b : ↥X, b ∈ CFSG.pCore 2 ↥X → c0 (a * b) = c0 a := by
    intro a b hb
    rw [hc0mul]
    have hb1 : c0 b = 1 := Subtype.ext (S.comm_Y_eq_one hmW hmY ((mem_pCore_iff b).mp hb))
    rw [hb1, map_one, mul_one]
  let c : ↥X ⧸ CFSG.pCore 2 ↥X → ↥(blockU X) := fun γ =>
    Quotient.liftOn' γ c0 (fun a b hab => by
      have hab' : a⁻¹ * b ∈ CFSG.pCore 2 ↥X := QuotientGroup.leftRel_apply.mp hab
      have := hc0Y a (a⁻¹ * b) hab'
      rw [mul_inv_cancel_left] at this
      exact this.symm)
  have hcmk : ∀ x : ↥X, c (x : ↥X ⧸ CFSG.pCore 2 ↥X) = c0 x := fun x => rfl
  have hc : ∀ γ δ, c (γ * δ) = c γ * S.phi γ (c δ) := by
    intro γ δ
    induction γ using QuotientGroup.induction_on with
    | H a =>
      induction δ using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, hcmk, hcmk, hcmk, hc0mul]
  obtain ⟨v, hv⟩ := exists_coboundary θ (V := ↥(blockU X))
    (fun a b => Subtype.ext (S.W_comm a.2 b.2))
    (fun a => Subtype.ext (by rw [SubgroupClass.coe_pow]; exact S.W_sq a.2))
    (by rw [S.card_blockU]) S.phi S.phi_injective c hc
  refine ⟨(v : G), v.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have h1 := congrArg Subtype.val (hv ((⟨x, hx⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X))
  rw [hcmk] at h1
  have h2 : ⁅m, x⁆ = (v : G) * (x * (v : G) * x⁻¹)⁻¹ := by
    rw [← S.phi_mk ⟨x, hx⟩ v]
    exact h1
  have h3 : m * x * m⁻¹ = (v : G) * x * (v : G)⁻¹ := by
    have : m * x * m⁻¹ = ⁅m, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [this, h2]
    group
  calc x * ((v : G)⁻¹ * m) = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * m := by group
    _ = (v : G)⁻¹ * (m * x * m⁻¹) * m := by rw [h3]
    _ = (v : G)⁻¹ * m * x := by group

theorem conj_eq_of_mem_Q {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) {w : G} (hw : w ∈ blockU X) :
    q * w * q⁻¹ = w := by
  obtain ⟨θ⟩ := S.nonempty_theta
  have hqM : q ∈ M := CFSG.CGT.PushingUpLit.SolK.pCoreOf_le_self M hq
  have hcomm : ∀ γ, S.actM ⟨q, hqM⟩ * S.phi γ = S.phi γ * S.actM ⟨q, hqM⟩ := by
    intro γ
    induction γ using QuotientGroup.induction_on with
    | H x =>
      ext u
      rw [MulAut.mul_apply, MulAut.mul_apply, S.actM_apply, S.phi_mk, S.phi_mk, S.actM_apply]
      have hy : ⁅q, (x : G)⁆ ∈ blockQ X := S.xnorm.commutator_Q_X_le_Y hq x.2
      have hqu : q * (u : G) * q⁻¹ ∈ blockU X := S.M_normalizes_W hqM u.2
      have hxqu : (x : G) * (q * (u : G) * q⁻¹) * (x : G)⁻¹ ∈ blockU X :=
        conj_mem_blockU x.2 hqu
      have hc := S.Y_comm_W hy hxqu
      have e : q * ((x : G) * (u : G) * (x : G)⁻¹) * q⁻¹ =
          ⁅q, (x : G)⁆ * ((x : G) * (q * (u : G) * q⁻¹) * (x : G)⁻¹) * ⁅q, (x : G)⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e, hc]
      group
  have h1 := eq_one_of_forall_commute θ (V := ↥(blockU X))
    (fun a b => Subtype.ext (S.W_comm a.2 b.2))
    (fun a => Subtype.ext (by rw [SubgroupClass.coe_pow]; exact S.W_sq a.2))
    (by rw [S.card_blockU]) S.phi S.phi_injective hcomm
  have h2 := congrArg Subtype.val (congrArg (fun f : MulAut ↥(blockU X) => f ⟨w, hw⟩) h1)
  simpa [S.actM_apply] using h2

theorem exists_eq_mul_of_mem_Q {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) :
    ∃ v ∈ blockU X, ∃ r ∈ CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (X : Set G), q = v * r := by
  obtain ⟨v, hv, hvc⟩ := S.exists_inv_mul_mem_centralizer (fun w hw => S.conj_eq_of_mem_Q hq hw)
    (fun x hx => S.xnorm.commutator_Q_X_le_Y hq hx)
  refine ⟨v, hv, v⁻¹ * q, ⟨(CFSG.Open.pCoreOf 2 M).mul_mem
    ((CFSG.Open.pCoreOf 2 M).inv_mem (S.W_le_Q hv)) hq, hvc⟩, by group⟩

theorem actM_mem_range (m : ↥M) : S.actM m ∈ S.phi.range := by
  obtain ⟨θ⟩ := S.nonempty_theta
  have hg : ∀ γ, ∃ γ', S.actM m * S.phi γ * (S.actM m)⁻¹ = S.phi γ' := by
    intro γ
    induction γ using QuotientGroup.induction_on with
    | H x =>
      have hxX : (m : G) * x * (m : G)⁻¹ ∈ X := S.normal m.2 x.2
      refine ⟨((⟨(m : G) * x * (m : G)⁻¹, hxX⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X), ?_⟩
      ext u
      rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, S.actM_apply, S.phi_mk, S.actM_apply,
        S.phi_mk]
      simp only [InvMemClass.coe_inv]
      group
  obtain ⟨γ₀, hγ₀⟩ := exists_eq_of_mem_normalizer θ (V := ↥(blockU X))
    (fun a b => Subtype.ext (S.W_comm a.2 b.2))
    (fun a => Subtype.ext (by rw [SubgroupClass.coe_pow]; exact S.W_sq a.2))
    (by rw [S.card_blockU]) S.phi S.phi_injective hg
  exact ⟨γ₀, hγ₀.symm⟩

end Action

@[expose] noncomputable def pi (S : Setting G M X) : ↥M →* ↥X ⧸ CFSG.pCore 2 ↥X :=
  (MonoidHom.ofInjective S.phi_injective).symm.toMonoidHom.comp
    (S.actM.codRestrict S.phi.range S.actM_mem_range)

section Pi

variable (S : Setting G M X)
include S

theorem phi_pi (m : ↥M) : S.phi (S.pi m) = S.actM m := by
  have h := MonoidHom.ofInjective_apply S.phi_injective (x := S.pi m)
  have h2 : MonoidHom.ofInjective S.phi_injective (S.pi m) =
      ⟨S.actM m, S.actM_mem_range m⟩ := by
    simp only [pi, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply]
    rfl
  rw [h2] at h
  exact h.symm

theorem pi_of_mem_X {x : G} (hx : x ∈ X) :
    S.pi ⟨x, S.le hx⟩ = ((⟨x, hx⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) := by
  apply S.phi_injective
  rw [S.phi_pi]
  ext u
  rw [S.actM_apply, S.phi_mk]

theorem exists_of_pi_eq_one {m : ↥M} (hm : S.pi m = 1) :
    ∃ v ∈ blockU X, v⁻¹ * (m : G) ∈ Subgroup.centralizer (X : Set G) := by
  have hact : S.actM m = 1 := by rw [← S.phi_pi, hm, map_one]
  have hmW : ∀ w ∈ blockU X, (m : G) * w * (m : G)⁻¹ = w := by
    intro w hw
    have h := congrArg Subtype.val (congrArg (fun f : MulAut ↥(blockU X) => f ⟨w, hw⟩) hact)
    simpa [S.actM_apply] using h
  have hmY : ∀ x ∈ X, ⁅(m : G), x⁆ ∈ blockQ X := by
    intro x hx
    have hxX : (m : G) * x * (m : G)⁻¹ ∈ X := S.normal m.2 hx
    have h1 : S.pi (m * ⟨x, S.le hx⟩ * m⁻¹) = S.pi ⟨x, S.le hx⟩ := by
      rw [map_mul, map_mul, map_inv, hm, one_mul, inv_one, mul_one]
    have h2 : (m * ⟨x, S.le hx⟩ * m⁻¹ : ↥M) = ⟨(m : G) * x * (m : G)⁻¹, S.le hxX⟩ :=
      Subtype.ext rfl
    rw [h2, S.pi_of_mem_X hxX, S.pi_of_mem_X hx, QuotientGroup.eq] at h1
    have h3 := (mem_pCore_iff _).mp h1
    simp only [InvMemClass.coe_inv, Subgroup.coe_mul] at h3
    have h4 : x * ((m : G) * x * (m : G)⁻¹)⁻¹ ∈ blockQ X := by
      have h6 := S.xnorm.Y_normalized (S.le hx) h3
      have e : x * (((m : G) * x * (m : G)⁻¹)⁻¹ * x) * x⁻¹ = x * ((m : G) * x * (m : G)⁻¹)⁻¹ := by
        group
      rw [e] at h6
      exact h6
    have h5 : ⁅(m : G), x⁆ = (x * ((m : G) * x * (m : G)⁻¹)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h5]
    exact (blockQ X).inv_mem h4
  exact S.exists_inv_mul_mem_centralizer hmW hmY

end Pi

end Setting

end CFSG.RankThree.PartTwo.Sec19.SolSeven
