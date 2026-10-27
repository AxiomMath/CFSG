module

public import CFSG.RankThree.PartOne.SolD3.Block
public import CFSG.CGT.PushingUpLit.SolK.Tight
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK
  CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Assembly (InCatalog KProper pCoreOf)
open scoped commutatorElement

structure Hyp3 (G : Type) [Group G] [Finite G] (M X : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  charTwo : CFSG.Assembly.IsCharTwoType G
  maxLocal : CFSG.IsMaximalTwoLocal M
  le : X ≤ M
  normal : (X.subgroupOf M).Normal
  unique : CFSG.maximalTwoLocalsContaining (X : Set G) = {M}
  short : IsShortGroup ↥X
  nat : IsNaturalAltModule ↥X 1

namespace Hyp3

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (h : Hyp3 G M X) {a : G}
include h

theorem xnorm : XNorm M X where
  le := h.le
  normal := fun m hm x hx => by
    have h1 := h.normal.conj_mem ⟨x, h.le hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
    simpa using Subgroup.mem_subgroupOf.1 h1

theorem W_normalized {m w : G} (hm : m ∈ M) (hw : w ∈ pCoreOf 2 X) :
    m * w * m⁻¹ ∈ pCoreOf 2 X :=
  XNorm.Y_normalized h.xnorm hm hw

theorem M_normalizes_W : ∀ m ∈ M, ∀ w ∈ pCoreOf 2 X, m * w * m⁻¹ ∈ pCoreOf 2 X :=
  fun _ hm _ hw => h.W_normalized hm hw

theorem W_le_Q : pCoreOf 2 X ≤ pCoreOf 2 M :=
  le_pCoreOf_of_normalized ((pCoreOf_le_self X).trans h.le)
    (fun _ hm _ hw => h.W_normalized hm hw) (isPGroup_pCoreOf' X)

theorem normalizer_Q_eq (hb : Blk3 X a) :
    Subgroup.normalizer (pCoreOf 2 M : Set G) = M := by
  have hM : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => pCoreOf_normalized M hm hq, fun hq => ?_⟩
    have h1 := pCoreOf_normalized M (M.inv_mem hm) hq
    have e : m⁻¹ * (m * q * m⁻¹) * (m⁻¹)⁻¹ = q := by group
    rwa [e] at h1
  have hne : pCoreOf 2 M ≠ ⊥ := by
    intro hbot
    apply hb.W_ne_bot
    exact le_bot_iff.1 (hbot ▸ h.W_le_Q)
  have hloc : IsPLocal 2 (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hne, isPGroup_pCoreOf' M, rfl⟩
  by_contra hne'
  exact h.maxLocal.2 _ (lt_of_le_of_ne hM (Ne.symm hne')) hloc

theorem mem_of_conj_le (hb : Blk3 X a) (g : G) (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ M) : g ∈ M := by
  set M' : Subgroup G := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'
  have hmax : IsMaximalTwoLocal M' := isMaximalTwoLocal_conj h.maxLocal g⁻¹
  have hXM' : (X : Set G) ⊆ M' := fun x hx => ⟨g * x * g⁻¹, hg x hx, by
    simp
    group⟩
  have hmem : M' ∈ maximalTwoLocalsContaining (X : Set G) := ⟨hmax, hXM'⟩
  rw [h.unique] at hmem
  have hM'M : M' = M := hmem
  have hconj : ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro m hm
    rw [← hM'M] at hm
    obtain ⟨m', hm', hm'e⟩ := hm
    have : g * m * g⁻¹ = m' := by
      rw [← hm'e]
      simp
      group
    rw [this]
    exact hm'
  have hconj' : ∀ m ∈ M, g⁻¹ * m * g ∈ M := by
    intro m hm
    have : g⁻¹ * m * g ∈ M' := ⟨m, hm, by simp⟩
    rwa [hM'M] at this
  have hgN : g ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff.2 fun m => ⟨fun hm => hconj m hm, fun hm => by
      have := hconj' _ hm
      simpa [mul_assoc] using this⟩
  have hgN' : g⁻¹ ∈ Subgroup.normalizer (M : Set G) := (Subgroup.normalizer _).inv_mem hgN
  have hnormM : ∀ n ∈ Subgroup.normalizer (M : Set G), ∀ k ∈ M, n * k * n⁻¹ ∈ M :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk
  rw [← h.normalizer_Q_eq hb]
  refine Subgroup.mem_normalizer_iff.2 fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · exact pCoreOf_normalized_of_normal hnormM hgN hq
  · have := pCoreOf_normalized_of_normal hnormM hgN' hq
    simpa [mul_assoc] using this

theorem centralizer_X_le_M (hb : Blk3 X a) : Subgroup.centralizer (X : Set G) ≤ M := by
  have hX : X ≤ Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => pCoreOf_normalized X hx hy, fun hy => ?_⟩
    have := pCoreOf_normalized X (X.inv_mem hx) hy
    simpa [mul_assoc] using this
  have hloc : IsPLocal 2 (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, hb.W_ne_bot, isPGroup_pCoreOf' X, rfl⟩
  have hle := local_le_of_unique h.unique hloc hX
  intro c hc
  have hcN : c ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) hc
  have hnormX : ∀ n ∈ Subgroup.normalizer (X : Set G), ∀ k ∈ X, n * k * n⁻¹ ∈ X :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk
  refine hle ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => pCoreOf_normalized_of_normal hnormX hcN hy, fun hy => ?_⟩
  have hcN' : c⁻¹ ∈ Subgroup.normalizer (X : Set G) := (Subgroup.normalizer _).inv_mem hcN
  have := pCoreOf_normalized_of_normal hnormX hcN' hy
  simpa [mul_assoc] using this

theorem mem_of_common_involution (hb : Blk3 X a) {g z : G}
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) (hz2 : orderOf z = 2)
    (hgz : g * z * g⁻¹ ∈ Subgroup.centralizer (X : Set G)) : g ∈ M := by
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    omega
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; simp)
  have hZ : Subgroup.zpowers z ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hz1
  have hloc : IsPLocal 2 (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :=
    ⟨_, hZ, hZ2, rfl⟩
  have hCN : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hxz : ∀ x ∈ X, x * z * x⁻¹ = z := fun x hx => by
    have := Subgroup.mem_centralizer_iff.1 hzC x hx
    rw [this]
    group
  have hXN : X ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun x hx =>
    hCN (mem_centralizer_zpowers_iff.2 (hxz x hx))
  have hle := local_le_of_unique h.unique hloc hXN
  have hconj : ∀ x ∈ X, g⁻¹ * x * g⁻¹⁻¹ ∈ M := by
    intro x hx
    rw [inv_inv]
    have hc := Subgroup.mem_centralizer_iff.1 hgz x hx
    refine hle (hCN (mem_centralizer_zpowers_iff.2 ?_))
    calc g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by group
      _ = z := by rw [hc]; group
  have h1 : g⁻¹ ∈ M := h.mem_of_conj_le hb g⁻¹ hconj
  simpa using M.inv_mem h1

theorem M_le_normalizer_C :
    M ≤ Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ c ∈ Subgroup.centralizer (X : Set G),
      m * c * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : m⁻¹ * x * m ∈ X := by
      have := h.xnorm.normal m⁻¹ (M.inv_mem hm) x hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * x := by group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨key m hm c, fun h' => by
    have := key m⁻¹ (M.inv_mem hm) _ h'
    simpa [mul_assoc] using this⟩

theorem normalizer_C_eq (hb : Blk3 X a)
    (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) = M := by
  refine le_antisymm (fun g hg => ?_) h.M_le_normalizer_C
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (X : Set G))) 2
    (even_iff_two_dvd.1 hev)
  have hz2 : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  exact h.mem_of_common_involution hb z.2 hz2 ((Subgroup.mem_normalizer_iff.1 hg (z : G)).1 z.2)

theorem tightlyEmbedded_C (hb : Blk3 X a)
    (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    TightlyEmbedded (Subgroup.centralizer (X : Set G)) :=
  StandardSubgroupAPI.tightlyEmbedded_of_involution hev fun g _ hz hz2 =>
    h.M_le_normalizer_C (h.mem_of_common_involution hb (Subgroup.mem_inf.1 hz).1 hz2
      ((mem_rightConjugate_iff _ g _).1 (Subgroup.mem_inf.1 hz).2))

theorem rOf_eq_pCoreOf_C (hb : Blk3 X a) :
    rOf M X = pCoreOf 2 (Subgroup.centralizer (X : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hCM : C ≤ M := h.centralizer_X_le_M hb
  have hCnorm : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := fun m hm c hc =>
    (Subgroup.mem_normalizer_iff.1 (h.M_le_normalizer_C hm) c).1 hc
  refine le_antisymm ?_ ?_
  · refine le_pCoreOf_of_normalized (fun r hr => hr.2) (fun c hc r hr => ?_)
      (isPGroup_of_le (isPGroup_pCoreOf' M) inf_le_left)
    exact Subgroup.mem_inf.2 ⟨pCoreOf_normalized M (hCM hc) hr.1, hCnorm c (hCM hc) r hr.2⟩
  · intro x hx
    have hQ : pCoreOf 2 C ≤ pCoreOf 2 M :=
      le_pCoreOf_of_normalized ((pCoreOf_le_self C).trans hCM)
        (fun m hm y hy => pCoreOf_normalized_of_normal hCnorm hm hy) (isPGroup_pCoreOf' C)
    exact ⟨hQ hx, pCoreOf_le_self C hx⟩

theorem R_normalized {m r : G} (hm : m ∈ M) (hr : r ∈ rOf M X) : m * r * m⁻¹ ∈ rOf M X := by
  refine Subgroup.mem_inf.2 ⟨pCoreOf_normalized M hm hr.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : m⁻¹ * x * m ∈ X := by
    have := h.xnorm.normal m⁻¹ (M.inv_mem hm) x hx
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.1 hr.2 _ h1
  calc x * (m * r * m⁻¹) = m * ((m⁻¹ * x * m) * r) * m⁻¹ := by group
    _ = m * (r * (m⁻¹ * x * m)) * m⁻¹ := by rw [h2]
    _ = m * r * m⁻¹ * x := by group

omit [Finite G] h in
theorem W_inf_C (hb : Blk3 X a) {w : G} (hw : w ∈ pCoreOf 2 X)
    (hC : w ∈ Subgroup.centralizer (X : Set G)) : w = 1 := by
  refine hb.fix w hw ?_
  have := Subgroup.mem_centralizer_iff.1 hC a hb.mem
  rw [this, mul_inv_cancel_right]

omit [Finite G] h in
theorem W_comm_R {w r : G} (hw : w ∈ pCoreOf 2 X) (hr : r ∈ rOf M X) : w * r = r * w :=
  Subgroup.mem_centralizer_iff.1 hr.2 w (pCoreOf_le_self X hw)

theorem q_comm_W (hb : Blk3 X a) {q : G} (hq : q ∈ pCoreOf 2 M) :
    ∀ w ∈ pCoreOf 2 X, q * w * q⁻¹ = w := by
  have hqM : q ∈ M := pCoreOf_le_self M hq
  refine centralizes_of_commutator hb h.M_normalizes_W (h.le hb.mem) hqM ?_ ?_
  · obtain ⟨k, hk⟩ := isPGroup_pCoreOf' M ⟨q, hq⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · have := XNorm.commutator_Q_X_le_Y h.xnorm hq hb.mem
    simpa [commutatorElement_def] using this

theorem exists_mul_centralizer (hb : Blk3 X a) {k : G} (hkM : k ∈ M)
    (hkW : ∀ w ∈ pCoreOf 2 X, k * w * k⁻¹ = w) :
    ∃ w ∈ pCoreOf 2 X, w⁻¹ * k ∈ Subgroup.centralizer (X : Set G) := by
  classical
  set W : Subgroup G := pCoreOf 2 X with hW
  have hWX : W ≤ X := pCoreOf_le_self X
  obtain ⟨w₀, hw₀, hw₀1⟩ := hb.exists_ne_one
  have haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun w hw => hb.conj_mem hw
  have haW' : ∀ w ∈ W, a⁻¹ * w * a ∈ W := fun w hw => hb.conj_mem' hw
  set z : G := k * a * k⁻¹ * a⁻¹ with hz
  have hzX : z ∈ X := X.mul_mem (h.xnorm.normal k hkM a hb.mem) (X.inv_mem hb.mem)
  have hzW : ∀ w ∈ W, z * w * z⁻¹ = w := by
    intro w hw
    have hw' : a⁻¹ * w * a ∈ W := haW' w hw
    have h1 : k * (a⁻¹ * w * a) * k⁻¹ = a⁻¹ * w * a := hkW _ hw'
    have h2 : k⁻¹ * (a⁻¹ * w * a) * k = a⁻¹ * w * a := by
      calc k⁻¹ * (a⁻¹ * w * a) * k = k⁻¹ * (k * (a⁻¹ * w * a) * k⁻¹) * k := by rw [h1]
        _ = a⁻¹ * w * a := by group
    calc z * w * z⁻¹ = k * a * (k⁻¹ * (a⁻¹ * w * a) * k) * a⁻¹ * k⁻¹ := by rw [hz]; group
      _ = k * a * (a⁻¹ * w * a) * a⁻¹ * k⁻¹ := by rw [h2]
      _ = k * w * k⁻¹ := by group
      _ = w := hkW w hw
  have hzWmem : z ∈ W := by
    obtain ⟨y, hy, j, hyj⟩ := hb.dec z hzX
    have hajW : ∀ w ∈ W, a ^ j * w * (a ^ j)⁻¹ = w := by
      intro w hw
      have hconj : ∀ i : ℕ, ∀ v ∈ W, a ^ i * v * (a ^ i)⁻¹ ∈ W := by
        intro i
        induction i with
        | zero => intro v hv; simpa using hv
        | succ i ih =>
          intro v hv
          have h1 := haW _ (ih v hv)
          have e : a ^ (i + 1) * v * (a ^ (i + 1))⁻¹ = a * (a ^ i * v * (a ^ i)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
          rw [e]
          exact h1
      have hyc : y * (a ^ j * w * (a ^ j)⁻¹) * y⁻¹ = a ^ j * w * (a ^ j)⁻¹ := by
        have := hb.comm y hy _ (hconj j w hw)
        rw [this]
        group
      calc a ^ j * w * (a ^ j)⁻¹ = y * (a ^ j * w * (a ^ j)⁻¹) * y⁻¹ := hyc.symm
        _ = (y * a ^ j) * w * (y * a ^ j)⁻¹ := by group
        _ = z * w * z⁻¹ := by rw [← hyj]
        _ = w := hzW w hw
    have hj : j % 3 = 0 := by
      by_contra hne
      have hj12 : j % 3 = 1 ∨ j % 3 = 2 := by omega
      have haj : a ^ j = a ^ (j % 3) := by
        conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hb.cube, one_pow, one_mul]
      rcases hj12 with h12 | h12
      · rw [haj, h12, pow_one] at hajW
        exact hw₀1 (hb.fix w₀ hw₀ (hajW w₀ hw₀))
      · rw [haj, h12] at hajW
        apply hw₀1
        apply hb.fix w₀ hw₀
        have h2 := hajW w₀ hw₀
        have ha2 : a ^ 2 = a⁻¹ := by
          calc a ^ 2 = a ^ 3 * a⁻¹ := by group
            _ = a⁻¹ := by rw [hb.cube, one_mul]
        rw [ha2, inv_inv] at h2
        calc a * w₀ * a⁻¹ = a * (a⁻¹ * w₀ * a) * a⁻¹ := by
              rw [h2]
          _ = w₀ := by group
    have haj0 : a ^ j = 1 := by
      have : a ^ j = a ^ (j % 3) := by
        conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hb.cube, one_pow, one_mul]
      rw [this, hj, pow_zero]
    rw [hyj, haj0, mul_one]
    exact hy
  let hmap : ↥W → ↥W := fun w => ⟨(w : G) * a * (w : G)⁻¹ * a⁻¹, by
    have : (w : G) * a * (w : G)⁻¹ * a⁻¹ = (w : G) * (a * (w : G)⁻¹ * a⁻¹) := by group
    rw [this]
    exact W.mul_mem w.2 (haW _ (W.inv_mem w.2))⟩
  have hinj : Function.Injective hmap := by
    intro w₁ w₂ hw
    have hw' : (w₁ : G) * a * (w₁ : G)⁻¹ * a⁻¹ = (w₂ : G) * a * (w₂ : G)⁻¹ * a⁻¹ :=
      congrArg Subtype.val hw
    have h1 : (w₁ : G) * a * (w₁ : G)⁻¹ = (w₂ : G) * a * (w₂ : G)⁻¹ := mul_right_cancel hw'
    have hva : (w₂ : G)⁻¹ * (w₁ : G) * a * ((w₂ : G)⁻¹ * (w₁ : G))⁻¹ = a := by
      calc (w₂ : G)⁻¹ * (w₁ : G) * a * ((w₂ : G)⁻¹ * (w₁ : G))⁻¹
          = (w₂ : G)⁻¹ * ((w₁ : G) * a * (w₁ : G)⁻¹) * (w₂ : G) := by group
        _ = a := by rw [h1]; group
    have hcomm : (w₂ : G)⁻¹ * (w₁ : G) * a = a * ((w₂ : G)⁻¹ * (w₁ : G)) :=
      mul_inv_eq_iff_eq_mul.1 hva
    have hc : a * ((w₂ : G)⁻¹ * (w₁ : G)) * a⁻¹ = (w₂ : G)⁻¹ * (w₁ : G) := by
      rw [← hcomm]
      group
    have hmem : (w₂ : G)⁻¹ * (w₁ : G) ∈ W := W.mul_mem (W.inv_mem w₂.2) w₁.2
    have h1' := hb.fix _ hmem hc
    exact Subtype.ext (by
      calc (w₁ : G) = (w₂ : G) * ((w₂ : G)⁻¹ * (w₁ : G)) := by group
        _ = (w₂ : G) := by rw [h1', mul_one])
  have hsurj : Function.Surjective hmap := Finite.injective_iff_surjective.1 hinj
  obtain ⟨w', hw'⟩ := hsurj ⟨z, hzWmem⟩
  have hw'z : (w' : G) * a * (w' : G)⁻¹ * a⁻¹ = z := congrArg Subtype.val hw'
  have hw'W : (w' : G) ∈ W := w'.2
  have hk'a : (w' : G)⁻¹ * k * a * ((w' : G)⁻¹ * k)⁻¹ = a := by
    have e : k * a * k⁻¹ = z * a := by rw [hz]; group
    have e2 : z * a = (w' : G) * a * (w' : G)⁻¹ := by
      rw [← hw'z]
      group
    calc (w' : G)⁻¹ * k * a * ((w' : G)⁻¹ * k)⁻¹
        = (w' : G)⁻¹ * (k * a * k⁻¹) * (w' : G) := by group
      _ = (w' : G)⁻¹ * ((w' : G) * a * (w' : G)⁻¹) * (w' : G) := by rw [e, e2]
      _ = a := by group
  have hk'W : ∀ w ∈ W, ((w' : G)⁻¹ * k) * w * ((w' : G)⁻¹ * k)⁻¹ = w := by
    intro w hw
    calc ((w' : G)⁻¹ * k) * w * ((w' : G)⁻¹ * k)⁻¹
        = (w' : G)⁻¹ * (k * w * k⁻¹) * (w' : G) := by group
      _ = (w' : G)⁻¹ * w * (w' : G) := by rw [hkW w hw]
      _ = w := by
        have := hb.comm _ (W.inv_mem hw'W) w hw
        rw [this]
        group
  refine ⟨(w' : G), hw'W, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨y, hy, j, rfl⟩ := hb.dec x hx
  have hk'X : ((w' : G)⁻¹ * k) * (y * a ^ j) * ((w' : G)⁻¹ * k)⁻¹ = y * a ^ j := by
    calc ((w' : G)⁻¹ * k) * (y * a ^ j) * ((w' : G)⁻¹ * k)⁻¹
        = (((w' : G)⁻¹ * k) * y * ((w' : G)⁻¹ * k)⁻¹) *
          (((w' : G)⁻¹ * k) * a * ((w' : G)⁻¹ * k)⁻¹) ^ j := by
          rw [conj_pow]
          group
      _ = y * a ^ j := by rw [hk'W y hy, hk'a]
  exact (comm_of_conj_eq hk'X).symm

theorem q_eq_W_mul_R (hb : Blk3 X a) {q : G} (hq : q ∈ pCoreOf 2 M) :
    ∃ w ∈ pCoreOf 2 X, ∃ r ∈ rOf M X, q = w * r := by
  obtain ⟨w, hw, hwC⟩ := h.exists_mul_centralizer hb (pCoreOf_le_self M hq) (h.q_comm_W hb hq)
  refine ⟨w, hw, w⁻¹ * q, Subgroup.mem_inf.2 ⟨?_, hwC⟩, by group⟩
  exact (pCoreOf 2 M).mul_mem ((pCoreOf 2 M).inv_mem (h.W_le_Q hw)) hq

end Hyp3

end CFSG.RankThree.PartOne.SolD3
