module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec32a_mem_normalizer_conj_iff {A : Subgroup G} {s z : G}
    (hs : s ∈ Subgroup.normalizer (A : Set G)) :
    s⁻¹ * z * s ∈ Subgroup.normalizer (A : Set G) ↔ z ∈ Subgroup.normalizer (A : Set G) := by
  have hsA : conjSubgroup s A = A := conjSubgroup_eq_self_iff.mpr hs
  have hsA' : conjSubgroup s⁻¹ A = A := by
    conv_lhs => rw [← hsA]
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hinv : ∀ X : Subgroup G, conjSubgroup s (conjSubgroup s⁻¹ X) = X := by
    intro X
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have e : conjSubgroup (s⁻¹ * z * s) A = conjSubgroup s⁻¹ (conjSubgroup z A) := by
    rw [conjSubgroup_mul (s⁻¹ * z) s, hsA, conjSubgroup_mul]
  rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_eq_self_iff, e]
  constructor
  · intro h
    rw [← hinv (conjSubgroup z A), h, hsA]
  · intro h
    rw [h, hsA']

theorem sec32a_le_normalizer_of_forall {X N : Subgroup G}
    (h : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    X ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact h x hx n hn
  · intro hn
    have := h x⁻¹ (X.inv_mem hx) _ hn
    simpa [mul_assoc] using this

theorem sec32a_conj_mem_of_sup {P Q N : Subgroup G} {x : G}
    (hP : ∀ p ∈ P, x * p * x⁻¹ ∈ N) (hQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ N) :
    ∀ n ∈ P ⊔ Q, x * n * x⁻¹ ∈ N := by
  intro n hn
  have hle : P ⊔ Q ≤ N.comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun p hp => by simpa using hP p hp) (fun q hq => by simpa using hQ q hq)
  simpa using hle hn

theorem sec32a_comm_commutator {x y l : G} (hyl : y * l = l * y)
    (hyw : y * (x⁻¹ * l * x) = (x⁻¹ * l * x) * y) :
    (x * y * x⁻¹ * y⁻¹) * l = l * (x * y * x⁻¹ * y⁻¹) := by
  have h1 : y⁻¹ * l = l * y⁻¹ := by
    calc y⁻¹ * l = y⁻¹ * (l * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * l) * y⁻¹ := by rw [← hyl]
      _ = l * y⁻¹ := by group
  calc (x * y * x⁻¹ * y⁻¹) * l = x * y * x⁻¹ * (y⁻¹ * l) := by group
    _ = x * y * x⁻¹ * (l * y⁻¹) := by rw [h1]
    _ = x * (y * (x⁻¹ * l * x)) * x⁻¹ * y⁻¹ := by group
    _ = x * ((x⁻¹ * l * x) * y) * x⁻¹ * y⁻¹ := by rw [hyw]
    _ = l * (x * y * x⁻¹ * y⁻¹) := by group

theorem sec32a_comm_conj_of_order_four {x b : G} (hx : x * x = 1) (hb : b * b = 1)
    (h4 : (x * b) ^ 4 = 1) : x * (b * x * b) = (b * x * b) * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e1 : x * (b * x * b) = (x * b) * (x * b) := by group
  have e2 : (b * x * b) * x = ((x * b) * (x * b))⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hxi, hbi]
    group
  have h8 : (x * b) * (x * b) * ((x * b) * (x * b)) = 1 := by
    rw [← h4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [e1, e2, inv_eq_of_mul_eq_one_right h8]

theorem sec32a_isPGroup_of_coe_le {H S : Subgroup G} (hS : IsPGroup 2 S) {K : Subgroup H}
    (hK : ∀ w ∈ K, ((w : H) : G) ∈ S) : IsPGroup 2 K := by
  intro w
  obtain ⟨k, hk⟩ := hS ⟨((w : H) : G), hK w w.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun t : S => (t : G)) hk
  simpa using this

theorem sec32a_inv_conj_eq_of_comm {s a : G} (h : s * a = a * s) : s⁻¹ * a * s = a := by
  calc s⁻¹ * a * s = s⁻¹ * (a * s) := by group
    _ = s⁻¹ * (s * a) := by rw [h]
    _ = a := by group

theorem sec32a_conj_eq_of_comm {s a : G} (h : s * a = a * s) : s * a * s⁻¹ = a := by
  calc s * a * s⁻¹ = (a * s) * s⁻¹ := by rw [h]
    _ = a := by group

theorem sec32a_comm_inv_of_comm {s a : G} (h : s * a = a * s) : a * s⁻¹ = s⁻¹ * a := by
  calc a * s⁻¹ = s⁻¹ * (s * a) * s⁻¹ := by group
    _ = s⁻¹ * (a * s) * s⁻¹ := by rw [h]
    _ = s⁻¹ * a := by group

theorem sec32a_exists_mem_ne_one {H : Subgroup G} (hH : H ≠ ⊥) : ∃ x ∈ H, x ≠ 1 := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩

theorem sec32a_core [Finite G] {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
    {s : G} (hsN : s ∈ Subgroup.normalizer (A : Set G)) (hsA : ∀ a ∈ A, s * a = a * s)
    (hK : ∀ y ∈ Lb, ∀ z ∈ conjSubgroup s Lb, y * z = z * y) :
    L ⊔ Lb ⊔ conjSubgroup s Lb ≤ A ⊔ Ab ⊔ conjSubgroup s Ab ∧
      (∀ y ∈ A ⊔ Ab ⊔ conjSubgroup s Ab,
        y ∈ Subgroup.normalizer ((L ⊔ Lb ⊔ conjSubgroup s Lb : Subgroup G) : Set G)) ∧
      IsElemAbelian 2 (L ⊔ Lb ⊔ conjSubgroup s Lb) := by
  have hLA : L ≤ A := S.L_le
  have hLN : L ≤ L ⊔ Lb ⊔ conjSubgroup s Lb := le_sup_left.trans le_sup_left
  have hLbN : Lb ≤ L ⊔ Lb ⊔ conjSubgroup s Lb := le_sup_right.trans le_sup_left
  have hZN : conjSubgroup s Lb ≤ L ⊔ Lb ⊔ conjSubgroup s Lb := le_sup_right
  have hZsub : conjSubgroup s Lb ≤ conjSubgroup s Ab := fun z hz =>
    mem_conjSubgroup.mpr (S.Lb_le (mem_conjSubgroup.mp hz))
  have hmemZ : ∀ z : G, z ∈ conjSubgroup s Lb ↔
      z ∈ conjSubgroup s Ab ∧ z ∈ Subgroup.normalizer (A : Set G) := by
    intro z
    rw [mem_conjSubgroup, mem_conjSubgroup, S.mem_Lb, sec32a_mem_normalizer_conj_iff hsN]
  have hsL : ∀ l ∈ L, s * l * s⁻¹ = l := fun l hl => sec32a_conj_eq_of_comm (hsA l (hLA hl))
  have hLZ : ∀ l ∈ L, ∀ z ∈ conjSubgroup s Lb, l * z = z * l := by
    intro l hl z hz
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ Lb, z = s * y * s⁻¹ :=
      ⟨s⁻¹ * z * s, mem_conjSubgroup.mp hz, by group⟩
    have hl' := hsA l (hLA hl)
    calc l * (s * y * s⁻¹) = s * (s⁻¹ * l * s) * y * s⁻¹ := by group
      _ = s * (l * y) * s⁻¹ := by rw [sec32a_inv_conj_eq_of_comm hl']; group
      _ = s * (y * l) * s⁻¹ := by rw [S.comm_L_Lb hl hy]
      _ = s * y * (l * s⁻¹) := by group
      _ = s * y * (s⁻¹ * l) := by rw [sec32a_comm_inv_of_comm hl']
      _ = (s * y * s⁻¹) * l := by group
  have hwMu : ∀ u ∈ Ab, ∀ l ∈ L, u⁻¹ * l * u ∈ M := by
    intro u hu l hl
    have h1 := (Subgroup.mem_normalizer_iff.mp (S.Ab_le_normalizer_M (Ab.inv_mem hu)) l).mp
      (S.L_le_M hl)
    rw [inv_inv] at h1
    exact h1
  have hzM : ∀ z ∈ conjSubgroup s Lb, ∀ w ∈ M, z * w = w * z := by
    intro z hz w hw
    obtain ⟨l', hl', lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hw
    calc z * (l' * lb) = (z * l') * lb := by group
      _ = (l' * z) * lb := by rw [hLZ l' hl' z hz]
      _ = l' * (z * lb) := by group
      _ = l' * (lb * z) := by rw [hK lb hlb z hz]
      _ = (l' * lb) * z := by group
  have hP2 : ∀ u ∈ Ab, ∀ z ∈ conjSubgroup s Lb, u * z * u⁻¹ * z⁻¹ ∈ Lb := by
    intro u hu z hz
    obtain ⟨y₀, hy₀, hy₀1⟩ := sec32a_exists_mem_ne_one S.Lb_ne_bot
    have hzN : z ∈ Subgroup.normalizer (Ab : Set G) :=
      mem_normalizer_of_commute_of_isTI S.ti_Ab (S.Lb_le hy₀) hy₀1 (hK y₀ hy₀ z hz).symm
    have hzu : z * u⁻¹ * z⁻¹ ∈ Ab :=
      (Subgroup.mem_normalizer_iff.mp hzN u⁻¹).mp (Ab.inv_mem hu)
    have hcAb : u * z * u⁻¹ * z⁻¹ ∈ Ab := by
      rw [show u * z * u⁻¹ * z⁻¹ = u * (z * u⁻¹ * z⁻¹) by group]
      exact Ab.mul_mem hu hzu
    have hcomL : ∀ l ∈ L, (u * z * u⁻¹ * z⁻¹) * l = l * (u * z * u⁻¹ * z⁻¹) := by
      intro l hl
      exact sec32a_comm_commutator (hLZ l hl z hz).symm (hzM z hz _ (hwMu u hu l hl))
    obtain ⟨a₀, ha₀, ha₀1⟩ := sec32a_exists_mem_ne_one S.ne_bot
    exact S.mem_Lb.mpr
      ⟨hcAb, mem_normalizer_of_commute_of_isTI S.ti (hLA ha₀) ha₀1 (hcomL a₀ ha₀)⟩
  have hconjL : ∀ u ∈ Ab, ∀ l ∈ L, ∃ l' ∈ L, ∃ z' ∈ conjSubgroup s Lb,
      (s * u * s⁻¹)⁻¹ * l * (s * u * s⁻¹) = l' * z' := by
    intro u hu l hl
    obtain ⟨l'', hl'', lb, hlb, heq⟩ := S.exists_mul_of_mem_M (hwMu u hu l hl)
    refine ⟨l'', hl'', s * lb * s⁻¹, mem_conjSubgroup.mpr ?_, ?_⟩
    · rw [show s⁻¹ * (s * lb * s⁻¹) * s = lb by group]
      exact hlb
    · calc (s * u * s⁻¹)⁻¹ * l * (s * u * s⁻¹)
          = s * (u⁻¹ * (s⁻¹ * l * s) * u) * s⁻¹ := by group
        _ = s * (u⁻¹ * l * u) * s⁻¹ := by rw [sec32a_inv_conj_eq_of_comm (hsA l (hLA hl))]
        _ = s * (l'' * lb) * s⁻¹ := by rw [heq]
        _ = (s * l'' * s⁻¹) * (s * lb * s⁻¹) := by group
        _ = l'' * (s * lb * s⁻¹) := by rw [hsL l'' hl'']
  have hP3 : ∀ x ∈ conjSubgroup s Ab, ∀ y ∈ Lb, x * y * x⁻¹ * y⁻¹ ∈ conjSubgroup s Lb := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ Ab, x = s * u * s⁻¹ :=
      ⟨s⁻¹ * x * s, mem_conjSubgroup.mp hx, by group⟩
    obtain ⟨y₀, hy₀, hy₀1⟩ := sec32a_exists_mem_ne_one S.Lb_ne_bot
    have hz₀L : s * y₀ * s⁻¹ ∈ conjSubgroup s Lb :=
      mem_conjSubgroup.mpr (by rw [show s⁻¹ * (s * y₀ * s⁻¹) * s = y₀ by group]; exact hy₀)
    have hz₀1 : s * y₀ * s⁻¹ ≠ 1 := by
      intro h
      apply hy₀1
      calc y₀ = s⁻¹ * (s * y₀ * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    have hyN : y ∈ Subgroup.normalizer (conjSubgroup s Ab : Set G) :=
      mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup S.ti_Ab s) (hZsub hz₀L) hz₀1
        (hK y hy _ hz₀L)
    have hcAb : (s * u * s⁻¹) * y * (s * u * s⁻¹)⁻¹ * y⁻¹ ∈ conjSubgroup s Ab := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hyN (s * u * s⁻¹)⁻¹).mp
        ((conjSubgroup s Ab).inv_mem hx)
      rw [show (s * u * s⁻¹) * y * (s * u * s⁻¹)⁻¹ * y⁻¹
          = (s * u * s⁻¹) * (y * (s * u * s⁻¹)⁻¹ * y⁻¹) by group]
      exact (conjSubgroup s Ab).mul_mem hx h1
    obtain ⟨a₀, ha₀, ha₀1⟩ := sec32a_exists_mem_ne_one S.ne_bot
    have hcomL : ((s * u * s⁻¹) * y * (s * u * s⁻¹)⁻¹ * y⁻¹) * a₀
        = a₀ * ((s * u * s⁻¹) * y * (s * u * s⁻¹)⁻¹ * y⁻¹) := by
      obtain ⟨l', hl', z', hz', hw⟩ := hconjL u hu a₀ ha₀
      have hyw : y * ((s * u * s⁻¹)⁻¹ * a₀ * (s * u * s⁻¹))
          = ((s * u * s⁻¹)⁻¹ * a₀ * (s * u * s⁻¹)) * y := by
        rw [hw]
        calc y * (l' * z') = (y * l') * z' := by group
          _ = (l' * y) * z' := by rw [S.comm_L_Lb hl' hy]
          _ = l' * (y * z') := by group
          _ = l' * (z' * y) := by rw [hK y hy z' hz']
          _ = (l' * z') * y := by group
      exact sec32a_comm_commutator (S.comm_L_Lb ha₀ hy).symm hyw
    exact (hmemZ _).mpr
      ⟨hcAb, mem_normalizer_of_commute_of_isTI S.ti (hLA ha₀) ha₀1 hcomL⟩
  have hP4 : ∀ x ∈ conjSubgroup s Ab, ∀ l ∈ L, x * l * x⁻¹ ∈ L ⊔ Lb ⊔ conjSubgroup s Lb := by
    intro x hx l hl
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ Ab, x = s * u * s⁻¹ :=
      ⟨s⁻¹ * x * s, mem_conjSubgroup.mp hx, by group⟩
    have hc0 : u * l * u⁻¹ * l⁻¹ ∈ Lb := S.commutator_mem_Lb hu hl
    have hz' : s * (u * l * u⁻¹ * l⁻¹) * s⁻¹ ∈ conjSubgroup s Lb :=
      mem_conjSubgroup.mpr (by rw [show s⁻¹ * (s * (u * l * u⁻¹ * l⁻¹) * s⁻¹) * s
          = u * l * u⁻¹ * l⁻¹ by group]; exact hc0)
    have hid : (s * u * s⁻¹) * l * (s * u * s⁻¹)⁻¹
        = (s * (u * l * u⁻¹ * l⁻¹) * s⁻¹) * l := by
      calc (s * u * s⁻¹) * l * (s * u * s⁻¹)⁻¹
          = s * (u * (s⁻¹ * l * s) * u⁻¹) * s⁻¹ := by group
        _ = s * (u * l * u⁻¹) * s⁻¹ := by rw [sec32a_inv_conj_eq_of_comm (hsA l (hLA hl))]
        _ = s * (u * l * u⁻¹ * l⁻¹) * l * s⁻¹ := by group
        _ = (s * (u * l * u⁻¹ * l⁻¹) * s⁻¹) * (s * l * s⁻¹) := by group
        _ = (s * (u * l * u⁻¹ * l⁻¹) * s⁻¹) * l := by rw [hsL l hl]
    rw [hid]
    exact Subgroup.mul_mem _ (hZN hz') (hLN hl)
  have fwdA : ∀ x ∈ A, ∀ n ∈ L ⊔ Lb ⊔ conjSubgroup s Lb,
      x * n * x⁻¹ ∈ L ⊔ Lb ⊔ conjSubgroup s Lb := by
    intro x hx
    refine sec32a_conj_mem_of_sup (P := L ⊔ Lb) (Q := conjSubgroup s Lb) ?_ ?_
    · refine sec32a_conj_mem_of_sup (P := L) (Q := Lb) ?_ ?_
      · intro l hl
        have e : x * l * x⁻¹ = l := by rw [S.comm_A hx (hLA hl)]; group
        rw [e]; exact hLN hl
      · intro y hy
        have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
        rw [e]; exact Subgroup.mul_mem _ (hLN (S.commutator_mem_L hx hy)) (hLbN hy)
    · intro z hz
      obtain ⟨y, hy, rfl⟩ : ∃ y ∈ Lb, z = s * y * s⁻¹ :=
        ⟨s⁻¹ * z * s, mem_conjSubgroup.mp hz, by group⟩
      have hc : x * y * x⁻¹ * y⁻¹ ∈ L := S.commutator_mem_L hx hy
      have hxs : x * s = s * x := (hsA x hx).symm
      have hsx' : s⁻¹ * x⁻¹ = x⁻¹ * s⁻¹ := by
        calc s⁻¹ * x⁻¹ = (x * s)⁻¹ := by group
          _ = (s * x)⁻¹ := by rw [hxs]
          _ = x⁻¹ * s⁻¹ := by group
      have e : x * (s * y * s⁻¹) * x⁻¹ = (s * (x * y * x⁻¹ * y⁻¹) * s⁻¹) * (s * y * s⁻¹) := by
        calc x * (s * y * s⁻¹) * x⁻¹ = (x * s) * y * s⁻¹ * x⁻¹ := by group
          _ = (s * x) * y * s⁻¹ * x⁻¹ := by rw [hxs]
          _ = s * x * y * (s⁻¹ * x⁻¹) := by group
          _ = s * x * y * (x⁻¹ * s⁻¹) := by rw [hsx']
          _ = (s * (x * y * x⁻¹ * y⁻¹) * s⁻¹) * (s * y * s⁻¹) := by group
      rw [e, sec32a_conj_eq_of_comm (hsA _ (S.L_le hc))]
      exact Subgroup.mul_mem _ (hLN hc) (hZN hz)
  have fwdAb : ∀ x ∈ Ab, ∀ n ∈ L ⊔ Lb ⊔ conjSubgroup s Lb,
      x * n * x⁻¹ ∈ L ⊔ Lb ⊔ conjSubgroup s Lb := by
    intro x hx
    refine sec32a_conj_mem_of_sup (P := L ⊔ Lb) (Q := conjSubgroup s Lb) ?_ ?_
    · refine sec32a_conj_mem_of_sup (P := L) (Q := Lb) ?_ ?_
      · intro l hl
        have e : x * l * x⁻¹ = (x * l * x⁻¹ * l⁻¹) * l := by group
        rw [e]; exact Subgroup.mul_mem _ (hLbN (S.commutator_mem_Lb hx hl)) (hLN hl)
      · intro y hy
        have e : x * y * x⁻¹ = y := by
          rw [CFSG.Open.IsElemAbelian.comm S.elem_Ab hx (S.Lb_le hy)]; group
        rw [e]; exact hLbN hy
    · intro z hz
      have e : x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
      rw [e]; exact Subgroup.mul_mem _ (hLbN (hP2 x hx z hz)) (hZN hz)
  have fwdAs : ∀ x ∈ conjSubgroup s Ab, ∀ n ∈ L ⊔ Lb ⊔ conjSubgroup s Lb,
      x * n * x⁻¹ ∈ L ⊔ Lb ⊔ conjSubgroup s Lb := by
    intro x hx
    refine sec32a_conj_mem_of_sup (P := L ⊔ Lb) (Q := conjSubgroup s Lb) ?_ ?_
    · refine sec32a_conj_mem_of_sup (P := L) (Q := Lb) ?_ ?_
      · intro l hl; exact hP4 x hx l hl
      · intro y hy
        have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
        rw [e]; exact Subgroup.mul_mem _ (hZN (hP3 x hx y hy)) (hLbN hy)
    · intro z hz
      obtain ⟨u, hu, rfl⟩ : ∃ u ∈ Ab, x = s * u * s⁻¹ :=
        ⟨s⁻¹ * x * s, mem_conjSubgroup.mp hx, by group⟩
      obtain ⟨y, hy, rfl⟩ : ∃ y ∈ Lb, z = s * y * s⁻¹ :=
        ⟨s⁻¹ * z * s, mem_conjSubgroup.mp hz, by group⟩
      have huy : u * y = y * u := CFSG.Open.IsElemAbelian.comm S.elem_Ab hu (S.Lb_le hy)
      have e : (s * u * s⁻¹) * (s * y * s⁻¹) * (s * u * s⁻¹)⁻¹ = s * y * s⁻¹ := by
        calc (s * u * s⁻¹) * (s * y * s⁻¹) * (s * u * s⁻¹)⁻¹
            = s * (u * y * u⁻¹) * s⁻¹ := by group
          _ = s * (y * u * u⁻¹) * s⁻¹ := by rw [huy]
          _ = s * y * s⁻¹ := by group
      rw [e]; exact hZN hz
  have hY : A ⊔ Ab ⊔ conjSubgroup s Ab ≤
      Subgroup.normalizer ((L ⊔ Lb ⊔ conjSubgroup s Lb : Subgroup G) : Set G) :=
    sup_le (sup_le (sec32a_le_normalizer_of_forall fwdA)
      (sec32a_le_normalizer_of_forall fwdAb)) (sec32a_le_normalizer_of_forall fwdAs)
  refine ⟨?_, fun y hy => hY hy, ?_⟩
  · exact sup_le (sup_le (le_trans hLA (le_sup_left.trans le_sup_left))
      (le_trans S.Lb_le (le_sup_right.trans le_sup_left))) (le_trans hZsub le_sup_right)
  · have hM' : IsElemAbelian 2 (L ⊔ Lb) := by
      rw [← S.hM]; exact S.isElemAbelian_M
    have hZel : IsElemAbelian 2 (conjSubgroup s Lb) :=
      CFSG.Open.IsElemAbelian.mono (isElemAbelian_conj S.elem_Ab s) hZsub
    have hc : ∀ m ∈ L ⊔ Lb, ∀ z ∈ conjSubgroup s Lb, m * z = z * m := by
      intro m hm z hz
      have hmM : m ∈ M := by rw [S.hM]; exact hm
      obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hmM
      have h1 := hLZ l hl z hz
      have h2 := hK lb hlb z hz
      calc l * lb * z = l * (lb * z) := by group
        _ = l * (z * lb) := by rw [h2]
        _ = (l * z) * lb := by group
        _ = (z * l) * lb := by rw [h1]
        _ = z * (l * lb) := by group
    exact CFSG.Open.IsElemAbelian.sup_of_commute hM' hZel hc

theorem sec32a_commute_of_involution [Finite G] {A Abar S₀ B : Subgroup G}
    (h : Sec3Ctx A Abar S₀ B) {b x₀ : G} (hb : b ∈ B) (hx₀ : x₀ ∈ Section3.Abar0 A Abar)
    (hx₁ : x₀ ≠ 1) (hxo : orderOf (x₀ * b) = 2 ∨ orderOf (x₀ * b) = 4) :
    ∀ y ∈ Section3.Abar0 A Abar, ∀ z ∈ conjSubgroup b (Section3.Abar0 A Abar), y * z = z * y := by
  have S : Prop24Setup A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
      (Section3.M A Abar) := h.setup
  have hbN : b ∈ Subgroup.normalizer (A : Set G) := h.s0_le_normalizer (h.b_le_s0 hb)
  have elemB : IsElemAbelian 2 B := by
    obtain ⟨g, hg⟩ := h.nota.conj
    rw [hg]
    exact isElemAbelian_conj h.hyp.elemAbelian g
  have hbb : b * b = 1 := by rw [← sq]; exact elemB.2 b hb
  have hxx : x₀ * x₀ = 1 := by rw [← sq]; exact S.elem_Ab.2 x₀ (S.Lb_le hx₀)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hdvd : orderOf (x₀ * b) ∣ 4 := by
    rcases hxo with h' | h' <;> rw [h'] <;> norm_num
  have h4 : (x₀ * b) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hLbN : Section3.Abar0 A Abar ≤ Subgroup.normalizer (A : Set G) :=
    fun y hy => (S.mem_Lb.mp hy).2
  have hx₀A : x₀ ∈ Subgroup.normalizer (A : Set G) := hLbN hx₀
  have hcomm : x₀ * (b * x₀ * b⁻¹) = (b * x₀ * b⁻¹) * x₀ := by
    rw [hbi]; exact sec32a_comm_conj_of_order_four hxx hbb h4
  have hcj : b * x₀ * b⁻¹ ∈ conjSubgroup b Abar :=
    mem_conjSubgroup.mpr (by
      rw [show b⁻¹ * (b * x₀ * b⁻¹) * b = x₀ by group]
      exact S.Lb_le hx₀)
  have hne1 : b * x₀ * b⁻¹ ≠ 1 := by
    intro e
    apply hx₁
    calc x₀ = b⁻¹ * (b * x₀ * b⁻¹) * b := by group
      _ = 1 := by rw [e]; group
  have hx₀Nj : x₀ ∈ Subgroup.normalizer (conjSubgroup b Abar : Set G) :=
    mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup S.ti_Ab b) hcj hne1 hcomm
  have hb_conj : ∀ m : G, b⁻¹ * m * b ∈ Section3.Abar0 A Abar ↔
      m ∈ conjSubgroup b Abar ∧ m ∈ Subgroup.normalizer (A : Set G) := by
    intro m
    rw [S.mem_Lb, mem_conjSubgroup, sec32a_mem_normalizer_conj_iff hbN]
  have hA_iff : ∀ m : G, m ∈ conjSubgroup b Abar ↔ x₀ * m * x₀⁻¹ ∈ conjSubgroup b Abar :=
    fun m => Subgroup.mem_normalizer_iff.mp hx₀Nj m
  have hN_iff : ∀ m : G, m ∈ Subgroup.normalizer (A : Set G) ↔
      x₀ * m * x₀⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
    intro m
    have key := sec32a_mem_normalizer_conj_iff (s := x₀⁻¹) (z := m)
      ((Subgroup.normalizer (A : Set G)).inv_mem hx₀A)
    rw [inv_inv] at key
    exact key.symm
  have hGnorm : ∀ n₀ : G, b⁻¹ * n₀ * b ∈ Section3.Abar0 A Abar ↔
      b⁻¹ * (x₀ * n₀ * x₀⁻¹) * b ∈ Section3.Abar0 A Abar := by
    intro n₀
    rw [hb_conj, hb_conj]
    exact and_congr (hA_iff n₀) (hN_iff n₀)
  obtain ⟨b', hb'⟩ : ∃ b' : ↥(Subgroup.normalizer (A : Set G)), (b' : G) = b :=
    ⟨⟨b, hbN⟩, rfl⟩
  set T : Subgroup ↥(Subgroup.normalizer (A : Set G)) :=
    (Section3.Abar0 A Abar).subgroupOf (Subgroup.normalizer (A : Set G)) with hT
  have hTel : IsElemAbelian 2 T :=
    CFSG.Open.IsElemAbelian.subgroupOf (CFSG.Open.IsElemAbelian.mono S.elem_Ab S.Lb_le) _
  have hTI : IsTI T := by
    intro k
    by_cases hne : Abar ⊓ conjSubgroup (k : G) Abar = ⊥
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwT, hwc⟩ := Subgroup.mem_inf.mp hw
      have h1 : (w : G) ∈ Abar := S.Lb_le (Subgroup.mem_subgroupOf.mp hwT)
      have h2 : (k : G)⁻¹ * (w : G) * (k : G) ∈ Abar :=
        S.Lb_le (Subgroup.mem_subgroupOf.mp (mem_conjSubgroup.mp hwc))
      have h3 : (w : G) ∈ Abar ⊓ conjSubgroup (k : G) Abar :=
        Subgroup.mem_inf.mpr ⟨h1, mem_conjSubgroup.mpr h2⟩
      rw [hne, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by simpa using h3)
    · right
      have hk : conjSubgroup (k : G) Abar = Abar := conjSubgroup_eq_of_isTI S.ti_Ab hne
      refine inf_eq_left.mpr ?_
      intro w hw
      rw [mem_conjSubgroup, hT, Subgroup.mem_subgroupOf]
      rw [hT, Subgroup.mem_subgroupOf] at hw
      have hwc : (w : G) ∈ conjSubgroup (k : G) Abar := by
        rw [hk]; exact S.Lb_le hw
      refine S.mem_Lb.mpr ⟨mem_conjSubgroup.mp hwc, ?_⟩
      exact (sec32a_mem_normalizer_conj_iff k.2).mpr (hLbN hw)
  have hT3 : IsPGroup 2 ↥(conjSubgroup 1 T ⊔ conjSubgroup b' T) := by
    apply sec32a_isPGroup_of_coe_le h.isPGroup_s0
    intro w hw
    have hbS : b ∈ S₀ := h.b_le_s0 hb
    have hle : conjSubgroup 1 T ⊔ conjSubgroup b' T ≤
        S₀.comap (Subgroup.normalizer (A : Set G)).subtype := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [conjSubgroup_one, hT, Subgroup.mem_subgroupOf] at hx
        exact Subgroup.mem_comap.mpr (h.abar0_le_s0 hx)
      · intro x hx
        rw [mem_conjSubgroup, hT, Subgroup.mem_subgroupOf] at hx
        have h1 : b⁻¹ * (x : G) * b ∈ S₀ := by simpa [hb'] using h.abar0_le_s0 hx
        have h3 : b * (b⁻¹ * (x : G) * b) * b⁻¹ ∈ S₀ :=
          S₀.mul_mem (S₀.mul_mem hbS h1) (S₀.inv_mem hbS)
        rw [show b * (b⁻¹ * (x : G) * b) * b⁻¹ = (x : G) by group] at h3
        exact Subgroup.mem_comap.mpr h3
    exact hle hw
  have hT4 : normalizerIn (conjSubgroup 1 T) (conjSubgroup b' T) ≠ ⊥ := by
    rw [conjSubgroup_one]
    intro hbot
    set x' : ↥(Subgroup.normalizer (A : Set G)) := ⟨x₀, hx₀A⟩ with hx'
    have hx'T : x' ∈ T := by rw [hT, Subgroup.mem_subgroupOf]; exact hx₀
    have hx'N : x' ∈ Subgroup.normalizer
        ((conjSubgroup b' T : Subgroup ↥(Subgroup.normalizer (A : Set G))) :
          Set ↥(Subgroup.normalizer (A : Set G))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      rw [mem_conjSubgroup, mem_conjSubgroup, hT, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      have := hGnorm (n : G)
      simpa [hb', hx'] using this
    have hmem : x' ∈ normalizerIn T (conjSubgroup b' T) := by
      unfold normalizerIn
      exact Subgroup.mem_inf.mpr ⟨hx'T, hx'N⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hx₁
    have h5 := congrArg (fun k : ↥(Subgroup.normalizer (A : Set G)) => (k : G)) hmem
    simpa [hx'] using h5
  have hK2 := commute_of_isPGroup hTel hTI hT3 hT4
  intro y hy z hz
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := hLbN hy
  have hzN : z ∈ Subgroup.normalizer (A : Set G) :=
    (sec32a_mem_normalizer_conj_iff hbN).mp (hLbN (mem_conjSubgroup.mp hz))
  have hy' : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (A : Set G))) ∈ conjSubgroup 1 T := by
    rw [conjSubgroup_one, hT, Subgroup.mem_subgroupOf]; exact hy
  have hz' : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (A : Set G))) ∈ conjSubgroup b' T := by
    rw [mem_conjSubgroup, hT, Subgroup.mem_subgroupOf]
    simpa [hb'] using mem_conjSubgroup.mp hz
  exact congrArg Subtype.val (hK2 _ hy' _ hz')

theorem sec32a_s_facts [Finite G] {A Abar S₀ B : Subgroup G} {s : G} (h : Sec3Ctx A Abar S₀ B)
    (hs : Section3.IsSChoice A Abar S₀ B s) :
    s ∈ Subgroup.normalizer (A : Set G) ∧ ∀ a ∈ A, s * a = a * s := by
  obtain ⟨b, hb, _, hcase⟩ := hs
  rcases hcase with ⟨_, hsb⟩ | ⟨_, x₀, hx₀, hx₁, hcl, hsS, hsC, hne, hcomm, hord⟩
  · subst hsb
    exact ⟨h.s0_le_normalizer (h.b_le_s0 hb), fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (h.b_le_centralizer hb) a ha).symm⟩
  · exact ⟨h.s0_le_normalizer hsS, fun a ha =>
      (Subgroup.mem_centralizer_iff.mp hsC a ha).symm⟩

theorem sec32a_K2 [Finite G] {A Abar S₀ B : Subgroup G} {s : G} (h : Sec3Ctx A Abar S₀ B)
    (hs : Section3.IsSChoice A Abar S₀ B s) :
    ∀ y ∈ Section3.Abar0 A Abar, ∀ z ∈ conjSubgroup s (Section3.Abar0 A Abar), y * z = z * y := by
  obtain ⟨b, hb, _, hcase⟩ := hs
  rcases hcase with ⟨⟨x₀, hx₀, hx₁, hxo⟩, hsb⟩ | ⟨_, x₀, hx₀, hx₁, _, _, _, _, hcomm, _⟩
  · subst hsb
    exact sec32a_commute_of_involution h hb hx₀ hx₁ hxo
  · exact hcomm

theorem tim77Sec32a_holds : Tim77Sec32aStatement := by
  intro G _ _ A Abar S₀ B s h hs
  obtain ⟨hsN, hsA⟩ := sec32a_s_facts h hs
  exact sec32a_core h.setup hsN hsA (sec32a_K2 h hs)


end CFSG.RankThree.GF2n.Tim77
