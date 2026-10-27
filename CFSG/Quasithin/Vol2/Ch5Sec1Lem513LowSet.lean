module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSecHom
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.InternalSecIrr
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512FF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

structure L2Set (V : Type) [CommGroup V] [Finite V] (X K : Subgroup (MulAut V)) (n : ℕ) :
    Prop where
  sq : ∀ v : V, v ^ 2 = 1
  two_le : 2 ≤ n
  le : K ≤ X
  norm : X ≤ Subgroup.normalizer (K : Set (MulAut V))
  two : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K
  o2 : pCoreOf 2 X = ⊥
  iso : Nonempty (↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
  card : Nat.card ↥K = 2 ^ n * ((2 ^ n) ^ 2 - 1)
  quasi : CFSG.IsQuasisimple ↥K
  sqtk : SQTKGroup ↥K
  simple : IsSimpleGroup ↥K

namespace L2Set

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)} {n : ℕ}

theorem normal (h : L2Set V X K n) : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K :=
  fun _ hx k hk => (Subgroup.mem_normalizer_iff.mp (h.norm hx) k).mp hk

theorem exists_noncomm (h : L2Set V X K n) : ∃ a b : ↥K, a * b ≠ b * a :=
  InternalSec.exists_noncomm_of_isQuasisimple h.quasi

theorem eq_bot_of_normal (h : L2Set V X K n) {N : Subgroup (MulAut V)} (hNX : N ≤ X)
    (hN : ∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N) (hK : ¬ K ≤ N) : N = ⊥ := by
  have := h.simple
  have hn : (N.subgroupOf K).Normal := ⟨fun y hy k => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hN k (h.le k.2) y hy⟩
  rcases hn.eq_bot_or_eq_top with h1 | h1
  · have hp : IsPGroup 2 ↥N := by
      intro y
      obtain ⟨e, he⟩ := h.two y (hNX y.2)
      refine ⟨e, Subtype.ext ?_⟩
      have hyK : (⟨(y : MulAut V) ^ 2 ^ e, he⟩ : ↥K) ∈ N.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        exact N.pow_mem y.2 _
      rw [h1, Subgroup.mem_bot] at hyK
      simpa using congrArg Subtype.val hyK
    have hXN : X ≤ Subgroup.normalizer (N : Set (MulAut V)) := fun x hx =>
      B6.mem_normalizer_of_forall_mem (hN x hx) fun y hy => by
        simpa using hN x⁻¹ (X.inv_mem hx) y hy
    have h2 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNX hXN hp
    rw [h.o2] at h2
    exact le_bot_iff.mp h2
  · exfalso
    apply hK
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := h1 ▸ Subgroup.mem_top _
    exact this

theorem inf_centSec_eq_bot (h : L2Set V X K n) {U Y : Subgroup V} (hXU : X ≤ stabSub U)
    (hXY : X ≤ stabSub Y) (hK : ¬ K ≤ centSec U Y) : X ⊓ centSec U Y = ⊥ :=
  h.eq_bot_of_normal inf_le_left
    (fun _ hx _ hy => ⟨X.mul_mem (X.mul_mem hx hy.1) (X.inv_mem hx),
      conj_mem_centSec (hXU hx) (hXY hx) hy.2⟩)
    (fun hle => hK (hle.trans inf_le_right))

theorem sec (h : L2Set V X K n) {U Y : Subgroup V} (hXU : X ≤ stabSub U)
    (hXY : X ≤ stabSub Y) (hf : X ⊓ centSec U Y = ⊥) :
    L2Set (Sec U Y) (autSec X U Y) (autSec K U Y) n := by
  have hKU : K ≤ stabSub U := h.le.trans hXU
  have hKY : K ≤ stabSub Y := h.le.trans hXY
  have hfK : K ⊓ centSec U Y = ⊥ := le_bot_iff.mp (hf ▸ inf_le_inf_right _ h.le)
  have hXs : X ≤ stabSub U ⊓ stabSub Y := le_inf hXU hXY
  have hKs : K ≤ stabSub U ⊓ stabSub Y := le_inf hKU hKY
  set eX := B5.secEquiv X hXU hXY hf with heX
  set eK := B5.secEquiv K hKU hKY hfK with heK
  have hconj : ∀ y ∈ autSec X U Y, ∀ l ∈ autSec K U Y, y * l * y⁻¹ ∈ autSec K U Y := by
    intro y hy l hl
    obtain ⟨g, hgX, rfl⟩ := (Bridge.mem_autSec_iff_secHom hXs).1 hy
    obtain ⟨k, hkK, rfl⟩ := (Bridge.mem_autSec_iff_secHom hKs).1 hl
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Bridge.secHom_mem_autSec hKs (g := g * k * g⁻¹) (h.normal _ hgX _ hkK)
  have := h.simple
  refine ⟨Bridge.sec_sq_eq_one h.sq U Y, h.two_le, autSec_mono h.le U Y, ?_, ?_, ?_,
    ⟨eK.symm.trans h.iso.some⟩, (Nat.card_congr eK.toEquiv).symm.trans h.card,
    B5.isQuasisimple_autSec hKU hKY hfK h.quasi, B5.sqtk_autSec hKU hKY hfK h.sqtk,
    eK.symm.isSimpleGroup⟩
  · intro y hy
    exact B6.mem_normalizer_of_forall_mem (hconj y hy) fun l hl => by
      simpa using hconj y⁻¹ ((autSec X U Y).inv_mem hy) l hl
  · intro y hy
    obtain ⟨g, hgX, rfl⟩ := (Bridge.mem_autSec_iff_secHom hXs).1 hy
    obtain ⟨e, he⟩ := h.two _ hgX
    refine ⟨e, ?_⟩
    rw [← map_pow]
    exact Bridge.secHom_mem_autSec hKs (g := g ^ 2 ^ e) he
  · have h1 : CFSG.Open.pCore 2 ↥X = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h.o2
    show (CFSG.Open.pCore 2 ↥(autSec X U Y)).map (autSec X U Y).subtype = ⊥
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eX, h1, Subgroup.map_bot, Subgroup.map_bot]

theorem b4Hyp (h : L2Set V X K n) (hirr : XMod.IsIrrSec ↥K (⊥ : Subgroup V) ⊤) :
    B4Hyp X K :=
  ⟨InternalSec.sqtkGroup_of_two_pow h.le h.normal h.two h.sqtk,
    (InternalSec.quasithinGenFitting_eq_of_two_pow h.le h.normal
      (B1Red.isQuasisimple_to_open h.quasi) h.two h.o2).symm, h.quasi, hirr⟩

theorem ff (hF : L2FFModuleFact) (h : L2Set V X K n) (hFF : IsFFModule X) :
    BinaryNaturalSL K ⊤ (fixV K) 2 n ∨
      (n = 2 ∧ IsIntDirect (commV K) (fixV X) ⊤ ∧ Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧
        SymmetricNatural X (commV K) ⊥ 5) :=
  hF V h.sq X K n h.two_le h.le h.norm h.two h.o2 h.iso h.card h.quasi h.sqtk hFF

end L2Set

end CFSG.Quasithin.H13
