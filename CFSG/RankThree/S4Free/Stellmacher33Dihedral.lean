module

public import CFSG.Open.LocalVocabulary
import TauCeti.Algebra.Group.Coprime

public section

namespace CFSG.RankThree.S4Free.Stell33

open Subgroup

variable {G : Type*} [Group G]

theorem mem_map_conj_iff {H : Subgroup G} {u x : G} :
    x ∈ H.map (MulAut.conj u).toMonoidHom ↔ u⁻¹ * x * u ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro hx
    exact ⟨u⁻¹ * x * u, hx, by simp [mul_assoc]⟩

theorem conj_mem_map_conj {H : Subgroup G} {u h : G} (hh : h ∈ H) :
    u * h * u⁻¹ ∈ H.map (MulAut.conj u).toMonoidHom :=
  ⟨h, hh, rfl⟩

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {u : G}
    (hu : u ∈ normalizer (H : Set G)) : H.map (MulAut.conj u).toMonoidHom = H := by
  ext x
  rw [mem_map_conj_iff]
  constructor
  · intro hx
    have := (mem_normalizer_iff.mp hu (u⁻¹ * x * u)).mp hx
    simpa [mul_assoc] using this
  · intro hx
    have := (mem_normalizer_iff.mp (inv_mem hu) x).mp hx
    simpa [mul_assoc] using this

theorem map_conj_inf (H K : Subgroup G) (u : G) :
    (H ⊓ K).map (MulAut.conj u).toMonoidHom =
      H.map (MulAut.conj u).toMonoidHom ⊓ K.map (MulAut.conj u).toMonoidHom :=
  map_inf_eq _ _ _ (MulAut.conj u).injective

theorem map_conj_map_conj (H : Subgroup G) (u v : G) :
    (H.map (MulAut.conj u).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      H.map (MulAut.conj (v * u)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem le_normalizer_of_forall_conj_mem {H K : Subgroup G}
    (hK : ∀ g ∈ K, ∀ x ∈ H, g * x * g⁻¹ ∈ H) : K ≤ normalizer (H : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hK g hg x hx, fun hx => ?_⟩
  have := hK g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_sup_zpowers {X : Subgroup G} {s g : G} (hg : g ∈ normalizer (X : Set G))
    (h₁ : g * s * g⁻¹ ∈ X ⊔ zpowers s) (h₂ : g⁻¹ * s * g ∈ X ⊔ zpowers s) :
    g ∈ normalizer ((X ⊔ zpowers s : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ normalizer (X : Set G) → g' * s * g'⁻¹ ∈ X ⊔ zpowers s →
      X ⊔ zpowers s ≤ (X ⊔ zpowers s).comap (MulAut.conj g').toMonoidHom := fun g' hg' hs =>
    sup_le (fun y hy => mem_sup_left ((mem_normalizer_iff.mp hg' y).mp hy)) (zpowers_le.mpr hs)
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg h₁ hx, fun hx => ?_⟩
  have h₂' : g⁻¹ * s * g⁻¹⁻¹ ∈ X ⊔ zpowers s := by rwa [inv_inv]
  have := key g⁻¹ (inv_mem hg) h₂' hx
  change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ X ⊔ zpowers s at this
  simpa [mul_assoc] using this

theorem mem_of_odd_pow_mem {K : Subgroup G} {g : G} {k m : ℕ} (hk : g ^ 2 ^ k = 1) (hm : Odd m)
    (hgm : g ^ m ∈ K) : g ∈ K := by
  obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := G)
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm))
  rw [← hij g, hk, one_zpow, one_mul]
  exact zpow_mem hgm j

def fixMod (K N : Subgroup G) (hN : K ≤ normalizer (N : Set G)) (c : G) : Subgroup G where
  carrier := {g | g ∈ K ∧ c⁻¹ * (g * c * g⁻¹) ∈ N}
  one_mem' := ⟨K.one_mem, by simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
    refine ⟨K.mul_mem hg₁ hg₂, ?_⟩
    have e : c⁻¹ * (g₁ * g₂ * c * (g₁ * g₂)⁻¹) =
        (c⁻¹ * (g₁ * c * g₁⁻¹)) * (g₁ * (c⁻¹ * (g₂ * c * g₂⁻¹)) * g₁⁻¹) := by group
    rw [e]
    exact N.mul_mem h₁ ((mem_normalizer_iff.mp (hN hg₁) _).mp h₂)
  inv_mem' := by
    rintro g ⟨hg, h₁⟩
    refine ⟨K.inv_mem hg, ?_⟩
    have e : c⁻¹ * (g⁻¹ * c * g⁻¹⁻¹) = g⁻¹ * (c⁻¹ * (g * c * g⁻¹))⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hN (K.inv_mem hg)) _).mp (N.inv_mem h₁)

theorem exists_pow_mem_fixMod [Finite G] {K N Y : Subgroup G} (hN : K ≤ normalizer (N : Set G))
    {g v : G} (hg : g ∈ K) (hgY : g ∈ normalizer (Y : Set G)) (hv : v ∈ Y)
    (hidx : N.relIndex Y ≤ 4) : ∃ d : ℕ, 0 < d ∧ d ≤ 4 ∧ g ^ d ∈ fixMod K N hN v := by
  have hmem : ∀ k : ℕ, g ^ k * v * (g ^ k)⁻¹ ∈ Y := fun k =>
    (mem_normalizer_iff.mp (pow_mem hgY k) v).mp hv
  let f : Fin 5 → Y ⧸ N.subgroupOf Y := fun k => QuotientGroup.mk ⟨_, hmem k⟩
  have hni : ¬ Function.Injective f := by
    intro hinj
    have h5 := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_fin] at h5
    have h4 : Nat.card (Y ⧸ N.subgroupOf Y) ≤ 4 := hidx
    omega
  have key : ∀ i j : ℕ, i < j → j ≤ 4 →
      (QuotientGroup.mk ⟨_, hmem i⟩ : Y ⧸ N.subgroupOf Y) = QuotientGroup.mk ⟨_, hmem j⟩ →
      ∃ d : ℕ, 0 < d ∧ d ≤ 4 ∧ g ^ d ∈ fixMod K N hN v := by
    intro i j hij hj heq
    refine ⟨j - i, by omega, by omega, ⟨pow_mem hg _, ?_⟩⟩
    rw [QuotientGroup.eq] at heq
    have heq' : (g ^ i * v * (g ^ i)⁻¹)⁻¹ * (g ^ j * v * (g ^ j)⁻¹) ∈ N := heq
    have h1 := (mem_normalizer_iff.mp (hN (inv_mem (pow_mem hg i))) _).mp heq'
    have e : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add]; congr 1; omega
    have e2 : ∀ a b : G, a⁻¹ * ((a * v * a⁻¹)⁻¹ * (a * b * v * (a * b)⁻¹)) * a⁻¹⁻¹ =
        v⁻¹ * (b * v * b⁻¹) := fun a b => by group
    rw [e, e2] at h1
    exact h1
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hni
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i j hlt (Nat.le_of_lt_succ j.isLt) hij
  · exact key j i hlt (Nat.le_of_lt_succ i.isLt) hij.symm

theorem card_le_of_hom_mod [Finite G] {Y Y' D : Subgroup G} (hDY : D ≤ Y) (hDY' : D ≤ Y')
    (hDn : ∀ g ∈ Y', ∀ d ∈ D, g * d * g⁻¹ ∈ D) (f : G → G) (hf : ∀ y ∈ Y, f y ∈ Y')
    (hmul : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, (f (y₁ * y₂))⁻¹ * (f y₁ * f y₂) ∈ D)
    (hker : ∀ y ∈ Y, f y ∈ D → y ∈ D) : Nat.card Y ≤ Nat.card Y' := by
  haveI : (D.subgroupOf Y').Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hDn g g.2 n hn⟩
  have h1 : f 1 ∈ D := by simpa using hmul 1 Y.one_mem 1 Y.one_mem
  let φ : Y →* Y' ⧸ D.subgroupOf Y' :=
    { toFun := fun y => QuotientGroup.mk (⟨f y, hf y y.2⟩ : Y')
      map_one' := by
        rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact h1
      map_mul' := by
        intro y₁ y₂
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        exact hmul y₁ y₁.2 y₂ y₂.2 }
  have hker' : φ.ker ≤ D.subgroupOf Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    change QuotientGroup.mk (⟨f y, hf y y.2⟩ : Y') = 1 at hy
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at hy
    rw [mem_subgroupOf]
    exact hker y y.2 hy
  have e1 : Nat.card Y = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have e2 : Nat.card Y' = Nat.card (Y' ⧸ D.subgroupOf Y') * Nat.card D := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf Y'),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY').toEquiv]
  rw [e1, e2]
  refine Nat.mul_le_mul (Subgroup.card_le_card_group _) ?_
  calc Nat.card φ.ker ≤ Nat.card (D.subgroupOf Y) := Subgroup.card_le_of_le hker'
    _ = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv

structure LCfgCore (L W P : Subgroup G) (u : G) : Prop where
  W_le : W ≤ L
  elemAb : CFSG.Open.IsElemAbelian 2 W
  P_le : P ≤ L
  L_le_normalizer_P : L ≤ normalizer (P : Set G)
  isPGroup_P : IsPGroup 2 P
  P_le_normalizer_W : P ≤ normalizer (W : Set G)
  u_mem : u ∈ L
  u_mul_u_mem : u * u ∈ P
  sup_eq : W ⊔ W.map (MulAut.conj u).toMonoidHom = L

structure LCfg (L W P : Subgroup G) (u : G) : Prop extends LCfgCore L W P u where
  relIndex_eq : (W ⊓ P).relIndex W = 2

namespace LCfg

abbrev Wu (W : Subgroup G) (u : G) : Subgroup G := W.map (MulAut.conj u).toMonoidHom

abbrev A (W P : Subgroup G) : Subgroup G := W ⊓ P

abbrev B (W P : Subgroup G) (u : G) : Subgroup G := Wu W u ⊓ P

abbrev D (W P : Subgroup G) (u : G) : Subgroup G := A W P ⊓ B W P u

abbrev X (W P : Subgroup G) (u : G) : Subgroup G := A W P ⊔ B W P u

end LCfg

namespace LCfgCore

open LCfg (Wu A B D X)

variable {L W P : Subgroup G} {u : G} (h : LCfgCore L W P u)

include h

theorem u_mem_normalizer_P : u ∈ normalizer (P : Set G) := h.L_le_normalizer_P h.u_mem

theorem map_conj_P : P.map (MulAut.conj u).toMonoidHom = P :=
  map_conj_eq_of_mem_normalizer h.u_mem_normalizer_P

theorem u_mul_u_mem_normalizer_W : u * u ∈ normalizer (W : Set G) :=
  h.P_le_normalizer_W h.u_mul_u_mem

theorem map_conj_Wu : (Wu W u).map (MulAut.conj u).toMonoidHom = W := by
  rw [Wu, map_conj_map_conj]
  exact map_conj_eq_of_mem_normalizer h.u_mul_u_mem_normalizer_W

theorem P_le_normalizer_Wu : P ≤ normalizer (Wu W u : Set G) := by
  intro p hp
  rw [mem_normalizer_iff]
  intro x
  rw [Wu, mem_map_conj_iff, mem_map_conj_iff]
  have hp' : u⁻¹ * p * u ∈ P := by
    have hu := h.u_mem_normalizer_P
    have := (mem_normalizer_iff''.mp hu p).mp hp
    simpa [mul_assoc] using this
  have key := mem_normalizer_iff.mp (h.P_le_normalizer_W hp') (u⁻¹ * x * u)
  have e : u⁻¹ * p * u * (u⁻¹ * x * u) * (u⁻¹ * p * u)⁻¹ = u⁻¹ * (p * x * p⁻¹) * u := by
    group
  rw [e] at key
  exact key

theorem map_conj_A : (A W P).map (MulAut.conj u).toMonoidHom = B W P u := by
  rw [A, map_conj_inf, h.map_conj_P]

theorem map_conj_B : (B W P u).map (MulAut.conj u).toMonoidHom = A W P := by
  rw [B, map_conj_inf, h.map_conj_Wu, h.map_conj_P]

theorem elemAb_Wu : CFSG.Open.IsElemAbelian 2 (Wu W u) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    apply Subtype.ext
    have hxy : x * y = y * x := congrArg Subtype.val (h.elemAb.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    change (MulAut.conj u) x * (MulAut.conj u) y = (MulAut.conj u) y * (MulAut.conj u) x
    rw [← map_mul, hxy, map_mul]
  · rintro _ ⟨x, hx, rfl⟩
    change (MulAut.conj u) x ^ 2 = 1
    rw [← map_pow, h.elemAb.2 x hx, map_one]

theorem comm_W {a b : G} (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a :=
  congrArg Subtype.val (h.elemAb.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem comm_Wu {a b : G} (ha : a ∈ Wu W u) (hb : b ∈ Wu W u) : a * b = b * a :=
  congrArg Subtype.val (h.elemAb_Wu.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem P_le_normalizer_A : P ≤ normalizer (A W P : Set G) := by
  intro p hp
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxW, hxP⟩
    exact ⟨(mem_normalizer_iff.mp (h.P_le_normalizer_W hp) x).mp hxW,
      P.mul_mem (P.mul_mem hp hxP) (P.inv_mem hp)⟩
  · rintro ⟨hxW, hxP⟩
    refine ⟨(mem_normalizer_iff.mp (h.P_le_normalizer_W hp) x).mpr hxW, ?_⟩
    have := P.mul_mem (P.mul_mem (P.inv_mem hp) hxP) hp
    simpa [mul_assoc] using this

theorem P_le_normalizer_B : P ≤ normalizer (B W P u : Set G) := by
  intro p hp
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxW, hxP⟩
    exact ⟨(mem_normalizer_iff.mp (h.P_le_normalizer_Wu hp) x).mp hxW,
      P.mul_mem (P.mul_mem hp hxP) (P.inv_mem hp)⟩
  · rintro ⟨hxW, hxP⟩
    refine ⟨(mem_normalizer_iff.mp (h.P_le_normalizer_Wu hp) x).mpr hxW, ?_⟩
    have := P.mul_mem (P.mul_mem (P.inv_mem hp) hxP) hp
    simpa [mul_assoc] using this

theorem A_le_P : A W P ≤ P := inf_le_right

theorem B_le_P : B W P u ≤ P := inf_le_right

theorem X_le_P : X W P u ≤ P := sup_le h.A_le_P h.B_le_P

theorem comm_A_B_mem_D {a b : G} (ha : a ∈ A W P) (hb : b ∈ B W P u) :
    a * b * a⁻¹ * b⁻¹ ∈ D W P u := by
  refine ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A W P :=
      (mem_normalizer_iff.mp (h.P_le_normalizer_A (h.B_le_P hb)) a⁻¹).mp (inv_mem ha)
    simpa [mul_assoc] using (A W P).mul_mem ha h1
  · have h1 : a * b * a⁻¹ ∈ B W P u :=
      (mem_normalizer_iff.mp (h.P_le_normalizer_B (h.A_le_P ha)) b).mp hb
    exact (B W P u).mul_mem h1 (inv_mem hb)

theorem L_le_centralizer_D : L ≤ centralizer (D W P u : Set G) := by
  rw [← h.sup_eq]
  refine sup_le ?_ ?_
  · intro w hw d hd
    exact (h.comm_W hw hd.1.1).symm
  · intro w hw d hd
    exact (h.comm_Wu hw hd.2.1).symm

theorem comm_D {d g : G} (hd : d ∈ D W P u) (hg : g ∈ L) : g * d = d * g :=
  ((mem_centralizer_iff.mp (h.L_le_centralizer_D hg)) d hd).symm

theorem comm_P_W_mem_A {x w : G} (hx : x ∈ P) (hw : w ∈ W) : w * x * w⁻¹ * x⁻¹ ∈ A W P := by
  refine ⟨?_, ?_⟩
  · have h1 : x * w⁻¹ * x⁻¹ ∈ W :=
      (mem_normalizer_iff.mp (h.P_le_normalizer_W hx) w⁻¹).mp (inv_mem hw)
    simpa [mul_assoc] using W.mul_mem hw h1
  · have h1 : w * x * w⁻¹ ∈ P :=
      (mem_normalizer_iff.mp (h.L_le_normalizer_P (h.W_le hw)) x).mp hx
    exact P.mul_mem h1 (inv_mem hx)

theorem comm_P_Wu_mem_B {x w : G} (hx : x ∈ P) (hw : w ∈ Wu W u) :
    w * x * w⁻¹ * x⁻¹ ∈ B W P u := by
  have hwL : w ∈ L := h.sup_eq ▸ mem_sup_right hw
  refine ⟨?_, ?_⟩
  · have h1 : x * w⁻¹ * x⁻¹ ∈ Wu W u :=
      (mem_normalizer_iff.mp (h.P_le_normalizer_Wu hx) w⁻¹).mp (inv_mem hw)
    simpa [mul_assoc] using (Wu W u).mul_mem hw h1
  · have h1 : w * x * w⁻¹ ∈ P := (mem_normalizer_iff.mp (h.L_le_normalizer_P hwL) x).mp hx
    exact P.mul_mem h1 (inv_mem hx)

theorem W_le_normalizer_X : W ≤ normalizer (X W P u : Set G) := by
  refine le_normalizer_of_forall_conj_mem (fun w hw x hx => ?_)
  have hsub : X W P u ≤ (X W P u).comap (MulAut.conj w).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · change w * a * w⁻¹ ∈ X W P u
      rw [h.comm_W hw ha.1, mul_inv_cancel_right]
      exact mem_sup_left ha
    · change w * b * w⁻¹ ∈ X W P u
      have hc := h.comm_P_W_mem_A (h.B_le_P hb) hw
      have : w * b * w⁻¹ = (w * b * w⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact mul_mem (mem_sup_left hc) (mem_sup_right hb)
  exact hsub hx

theorem Wu_le_normalizer_X : Wu W u ≤ normalizer (X W P u : Set G) := by
  refine le_normalizer_of_forall_conj_mem (fun w hw x hx => ?_)
  have hsub : X W P u ≤ (X W P u).comap (MulAut.conj w).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · change w * a * w⁻¹ ∈ X W P u
      have hc := h.comm_P_Wu_mem_B (h.A_le_P ha) hw
      have : w * a * w⁻¹ = (w * a * w⁻¹ * a⁻¹) * a := by group
      rw [this]
      exact mul_mem (mem_sup_right hc) (mem_sup_left ha)
    · change w * b * w⁻¹ ∈ X W P u
      rw [h.comm_Wu hw hb.1, mul_inv_cancel_right]
      exact mem_sup_right hb
  exact hsub hx

theorem L_le_normalizer_X : L ≤ normalizer (X W P u : Set G) := by
  rw [← h.sup_eq]
  exact sup_le h.W_le_normalizer_X h.Wu_le_normalizer_X

theorem A_le_normalizer_B : A W P ≤ normalizer (B W P u : Set G) :=
  h.A_le_P.trans h.P_le_normalizer_B

theorem mem_X_iff {x : G} : x ∈ X W P u ↔ ∃ a ∈ A W P, ∃ b ∈ B W P u, x = a * b := by
  rw [X, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ h.A_le_normalizer_B,
    Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem D_le_A : D W P u ≤ A W P := inf_le_left

theorem D_le_B : D W P u ≤ B W P u := inf_le_right

theorem A_le_X : A W P ≤ X W P u := le_sup_left

theorem B_le_X : B W P u ≤ X W P u := le_sup_right

theorem X_le_L : X W P u ≤ L := h.X_le_P.trans h.P_le

theorem A_le_W : A W P ≤ W := inf_le_left

theorem Wu_le_L : Wu W u ≤ L := h.sup_eq ▸ le_sup_right

theorem conj_D {d g : G} (hd : d ∈ D W P u) (hg : g ∈ L) : g * d * g⁻¹ = d := by
  rw [h.comm_D hd hg, mul_inv_cancel_right]

def commD (x : G) (hx : x ∈ L) : Subgroup G where
  carrier := {y | y ∈ L ∧ x * y * x⁻¹ * y⁻¹ ∈ D W P u}
  one_mem' := ⟨L.one_mem, by simp⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
    refine ⟨L.mul_mem hy₁ hy₂, ?_⟩
    have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
        (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
    rw [e, h.conj_D h₂ hy₁]
    exact mul_mem h₁ h₂
  inv_mem' := by
    rintro y ⟨hy, h₁⟩
    refine ⟨L.inv_mem hy, ?_⟩
    have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
    rw [e]
    have := h.conj_D (inv_mem h₁) (L.inv_mem hy)
    rw [inv_inv] at this
    rw [this]
    exact inv_mem h₁

theorem comm_mem_D_symm {x y : G} (h₁ : x * y * x⁻¹ * y⁻¹ ∈ D W P u) :
    y * x * y⁻¹ * x⁻¹ ∈ D W P u := by
  have e : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h₁

theorem comm_mul_mem_D {g x y : G} (hx : x ∈ L) (h₁ : g * x * g⁻¹ * x⁻¹ ∈ D W P u)
    (h₂ : g * y * g⁻¹ * y⁻¹ ∈ D W P u) : g * (x * y) * g⁻¹ * (x * y)⁻¹ ∈ D W P u := by
  have e : g * (x * y) * g⁻¹ * (x * y)⁻¹ =
      (g * x * g⁻¹ * x⁻¹) * (x * (g * y * g⁻¹ * y⁻¹) * x⁻¹) := by group
  rw [e, h.conj_D h₂ hx]
  exact mul_mem h₁ h₂

theorem X_le_commD_of_A {a : G} (ha : a ∈ A W P) :
    X W P u ≤ h.commD a (h.X_le_L (h.A_le_X ha)) := by
  refine sup_le (fun a' ha' => ⟨h.X_le_L (h.A_le_X ha'), ?_⟩)
    (fun b hb => ⟨h.X_le_L (h.B_le_X hb), ?_⟩)
  · rw [h.comm_W ha.1 ha'.1]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · exact h.comm_A_B_mem_D ha hb

theorem X_le_commD_of_B {b : G} (hb : b ∈ B W P u) :
    X W P u ≤ h.commD b (h.X_le_L (h.B_le_X hb)) := by
  refine sup_le (fun a ha => ⟨h.X_le_L (h.A_le_X ha), ?_⟩)
    (fun b' hb' => ⟨h.X_le_L (h.B_le_X hb'), ?_⟩)
  · exact h.comm_mem_D_symm (h.comm_A_B_mem_D ha hb)
  · rw [h.comm_Wu hb.1 hb'.1]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem comm_X_mem_D {x y : G} (hx : x ∈ X W P u) (hy : y ∈ X W P u) :
    x * y * x⁻¹ * y⁻¹ ∈ D W P u := by
  have hyL := h.X_le_L hy
  have key : X W P u ≤ h.commD y hyL := by
    refine sup_le (fun a ha => ⟨h.X_le_L (h.A_le_X ha), ?_⟩)
      (fun b hb => ⟨h.X_le_L (h.B_le_X hb), ?_⟩)
    · exact h.comm_mem_D_symm (h.X_le_commD_of_A ha hy).2
    · exact h.comm_mem_D_symm (h.X_le_commD_of_B hb hy).2
  exact h.comm_mem_D_symm (key hx).2

theorem sq_X_mem_D {x : G} (hx : x ∈ X W P u) : x * x ∈ D W P u := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_X_iff.mp hx
  have ha2 : a * a = 1 := by rw [← sq]; exact h.elemAb.2 a ha.1
  have hb2 : b * b = 1 := by rw [← sq]; exact h.elemAb_Wu.2 b hb.1
  have hc := h.comm_mem_D_symm (h.comm_A_B_mem_D ha hb)
  set c := b * a * b⁻¹ * a⁻¹ with hcdef
  have hca : a * c = c * a := h.comm_D hc (h.X_le_L (h.A_le_X ha))
  have e : a * b * (a * b) = c * (a * a) * (b * b) := by
    calc a * b * (a * b) = a * (c * a * b) * b := by rw [hcdef]; group
      _ = (a * c) * a * (b * b) := by group
      _ = c * (a * a) * (b * b) := by rw [hca]; group
  rw [e, ha2, hb2, mul_one, mul_one]
  exact hc

theorem mem_D_of_conj_mem_D {x g : G} (hg : g ∈ L) (hx : g * x * g⁻¹ ∈ D W P u) : x ∈ D W P u := by
  have := h.conj_D hx (L.inv_mem hg)
  rw [inv_inv] at this
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e] at this
  rw [this]
  exact hx

theorem L_le_commD {x : G} (hx : x ∈ L) (hW : W ≤ h.commD x hx) (hWu : Wu W u ≤ h.commD x hx) :
    L ≤ h.commD x hx :=
  le_trans (le_of_eq h.sup_eq.symm) (sup_le hW hWu)

theorem mem_D_of_comm_mem_D {x : G} (hx : x ∈ X W P u)
    (hc : ∀ g ∈ L, g * x * g⁻¹ * x⁻¹ ∈ D W P u) : x ∈ D W P u := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_X_iff.mp hx
  have haL := h.X_le_L (h.A_le_X ha)
  have hbL := h.X_le_L (h.B_le_X hb)
  have hW : ∀ g ∈ W, g * b * g⁻¹ * b⁻¹ ∈ D W P u := by
    intro g hg
    have h1 := hc g (h.W_le hg)
    have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ = a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ := by
      have hga : g * a = a * g := h.comm_W hg ha.1
      calc g * (a * b) * g⁻¹ * (a * b)⁻¹ = (g * a) * b * g⁻¹ * b⁻¹ * a⁻¹ := by group
        _ = a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ := by rw [hga]; group
    rw [e] at h1
    exact h.mem_D_of_conj_mem_D haL h1
  have hWu : ∀ g ∈ Wu W u, g * a * g⁻¹ * a⁻¹ ∈ D W P u := by
    intro g hg
    have h1 := hc g (h.Wu_le_L hg)
    have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ = g * a * g⁻¹ * a⁻¹ := by
      have hgb : g * b = b * g := h.comm_Wu hg hb.1
      have hgb' : b * g⁻¹ = g⁻¹ * b := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hgb, ← mul_assoc, inv_mul_cancel, one_mul]
      calc g * (a * b) * g⁻¹ * (a * b)⁻¹ = g * a * (b * g⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = g * a * (g⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hgb']
        _ = g * a * g⁻¹ * a⁻¹ := by group
    rwa [e] at h1
  have hLa : L ≤ h.commD a haL := by
    refine h.L_le_commD haL (fun g hg => ⟨h.W_le hg, ?_⟩) (fun g hg => ⟨h.Wu_le_L hg, ?_⟩)
    · rw [h.comm_W ha.1 hg]
      simp only [mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · exact h.comm_mem_D_symm (hWu g hg)
  have hLb : L ≤ h.commD b hbL := by
    refine h.L_le_commD hbL (fun g hg => ⟨h.W_le hg, ?_⟩) (fun g hg => ⟨h.Wu_le_L hg, ?_⟩)
    · exact h.comm_mem_D_symm (hW g hg)
    · rw [h.comm_Wu hb.1 hg]
      simp only [mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hua : u * a * u⁻¹ ∈ D W P u := by
    have hcu := h.comm_mem_D_symm (hLa h.u_mem).2
    refine ⟨?_, ?_⟩
    · have e : u * a * u⁻¹ = (u * a * u⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact mul_mem (h.D_le_A hcu) ha
    · have := conj_mem_map_conj (u := u) ha
      rwa [h.map_conj_A] at this
  have hub : u * b * u⁻¹ ∈ D W P u := by
    have hcu := h.comm_mem_D_symm (hLb h.u_mem).2
    refine ⟨?_, ?_⟩
    · have := conj_mem_map_conj (u := u) hb
      rwa [h.map_conj_B] at this
    · have e : u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b := by group
      rw [e]
      exact mul_mem (h.D_le_B hcu) hb
  exact mul_mem (h.mem_D_of_conj_mem_D h.u_mem hua) (h.mem_D_of_conj_mem_D h.u_mem hub)

theorem card_A_eq_card_B : Nat.card (A W P) = Nat.card (B W P u) := by
  rw [← h.map_conj_A, Subgroup.card_map_of_injective (MulAut.conj u).injective]

end LCfgCore

namespace LCfg

variable {L W P : Subgroup G} {u : G} (h : LCfg L W P u)

include h

theorem sup_zpowers_eq {v : G} (hv : v ∈ W) (hvA : v ∉ A W P) :
    A W P ⊔ zpowers v = W := by
  have hle : A W P ⊔ zpowers v ≤ W := sup_le h.A_le_W (zpowers_le.mpr hv)
  have hAle : A W P ≤ A W P ⊔ zpowers v := le_sup_left
  have hmul := relIndex_mul_relIndex _ _ _ hAle hle
  have hidx : (A W P).relIndex W = 2 := h.relIndex_eq
  rw [hidx] at hmul
  have hne : (A W P).relIndex (A W P ⊔ zpowers v) ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    intro hle'
    exact hvA (hle' (mem_sup_right (mem_zpowers v)))
  have h2 : (A W P ⊔ zpowers v).relIndex W = 1 := by
    rcases Nat.eq_zero_or_pos ((A W P ⊔ zpowers v).relIndex W) with h0 | hpos
    · rw [h0, mul_zero] at hmul
      exact absurd hmul (by norm_num)
    · have hd : (A W P ⊔ zpowers v).relIndex W ∣ 2 := ⟨_, by rw [mul_comm]; exact hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
      · exact h1
      · rw [h1] at hmul
        exact absurd (by omega : (A W P).relIndex (A W P ⊔ zpowers v) = 1) hne
  exact le_antisymm hle (relIndex_eq_one.mp h2)

theorem L_le_commD_of_B {b v : G} (hb : b ∈ B W P u) (hv : v ∈ W) (hvA : v ∉ A W P)
    (hvb : v * b * v⁻¹ * b⁻¹ ∈ D W P u) : L ≤ h.commD b (h.X_le_L (h.B_le_X hb)) := by
  refine h.L_le_commD _ ?_ (fun g hg => ⟨h.Wu_le_L hg, ?_⟩)
  · refine le_trans (le_of_eq (h.sup_zpowers_eq hv hvA).symm) ?_
    refine sup_le (fun a ha => ⟨h.W_le ha.1, h.comm_mem_D_symm (h.comm_A_B_mem_D ha hb)⟩) ?_
    rw [zpowers_le]
    exact ⟨h.W_le hv, h.comm_mem_D_symm hvb⟩
  · rw [h.comm_Wu hb.1 hg]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem A_le_sup_of_not_le [Finite G] {V : Subgroup G} (hVW : V ≤ W)
    (hXV : X W P u ≤ normalizer (V : Set G)) (hV : ¬ V ≤ X W P u) :
    A W P ≤ (V ⊓ A W P) ⊔ D W P u := by
  obtain ⟨v, hvV, hvX⟩ := Set.not_subset.mp hV
  have hvW : v ∈ W := hVW hvV
  have hvA : v ∉ A W P := fun h' => hvX (h.A_le_X h')
  set A' := (V ⊓ A W P) ⊔ D W P u with hA'
  have hA'A : A' ≤ A W P := sup_le inf_le_right h.D_le_A
  have hDA' : D W P u ≤ A' := le_sup_right
  have hcV : ∀ b ∈ B W P u, v * b * v⁻¹ * b⁻¹ ∈ V ⊓ A W P := by
    intro b hb
    refine ⟨?_, h.comm_P_W_mem_A (h.B_le_P hb) hvW⟩
    have h1 : b * v⁻¹ * b⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (hXV (h.B_le_X hb)) v⁻¹).mp (inv_mem hvV)
    have e : v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem hvV h1
  have hmul : ∀ b₁ ∈ B W P u, ∀ b₂ ∈ B W P u,
      (v * (b₁ * b₂) * v⁻¹ * (b₁ * b₂)⁻¹)⁻¹ * ((v * b₁ * v⁻¹ * b₁⁻¹) * (v * b₂ * v⁻¹ * b₂⁻¹)) ∈
        D W P u := by
    intro b₁ hb₁ b₂ hb₂
    set c₁ := v * b₁ * v⁻¹ * b₁⁻¹ with hc₁
    set c₂ := v * b₂ * v⁻¹ * b₂⁻¹ with hc₂
    have hc₂A : c₂ ∈ A W P := (hcV b₂ hb₂).2
    set k := b₁ * c₂ * b₁⁻¹ * c₂⁻¹ with hk
    have hkD : k ∈ D W P u := h.comm_mem_D_symm (h.comm_A_B_mem_D hc₂A hb₁)
    have hc₁L : c₁ ∈ L := h.X_le_L (h.A_le_X (hcV b₁ hb₁).2)
    have e1 : v * (b₁ * b₂) * v⁻¹ * (b₁ * b₂)⁻¹ = c₁ * (k * c₂) := by
      rw [hc₁, hk, hc₂]
      group
    have e2 : c₁ * (k * c₂) = k * (c₁ * c₂) := by
      rw [← mul_assoc, h.comm_D hkD hc₁L, mul_assoc]
    rw [e1, e2]
    have hc12L : c₁ * c₂ ∈ L := L.mul_mem hc₁L (h.X_le_L (h.A_le_X hc₂A))
    have e3 : (k * (c₁ * c₂))⁻¹ * (c₁ * c₂) = (c₁ * c₂)⁻¹ * k⁻¹ * (c₁ * c₂) := by group
    rw [e3]
    have := h.conj_D (inv_mem hkD) (L.inv_mem hc12L)
    rw [inv_inv] at this
    rw [this]
    exact inv_mem hkD
  have hcard := card_le_of_hom_mod h.D_le_B hDA'
    (fun g hg d hd => by rw [h.conj_D hd (h.X_le_L (h.A_le_X (hA'A hg)))]; exact hd)
    (fun b => v * b * v⁻¹ * b⁻¹) (fun b hb => mem_sup_left (hcV b hb)) hmul
    (fun b hb hbD => h.mem_D_of_comm_mem_D (h.B_le_X hb)
      (fun g hg => h.comm_mem_D_symm ((h.L_le_commD_of_B hb hvW hvA hbD) hg).2))
  rw [Subgroup.eq_of_le_of_card_ge hA'A (h.card_A_eq_card_B.le.trans hcard)]

omit h in
abbrev rot (w u : G) : G := w * (u * w * u⁻¹)

theorem mul_self_eq_one {w : G} (hw : w ∈ W) : w * w = 1 := by
  rw [← sq]
  exact h.elemAb.2 w hw

theorem exists_mem_not_mem_A : ∃ w ∈ W, w ∉ A W P := by
  have h2 : (A W P).relIndex W = 2 := h.relIndex_eq
  refine Set.not_subset.mp (fun hle => ?_)
  have h1 : (A W P).relIndex W = 1 := relIndex_eq_one.mpr hle
  omega

theorem rot_mem_L {w : G} (hw : w ∈ W) : rot w u ∈ L :=
  L.mul_mem (h.W_le hw) (h.Wu_le_L (conj_mem_map_conj hw))

theorem conj_rot {w : G} (hw : w ∈ W) : w * rot w u * w⁻¹ = (rot w u)⁻¹ := by
  have hww := h.mul_self_eq_one hw
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  calc w * (w * (u * w * u⁻¹)) * w⁻¹ = (w * w) * (u * w * u⁻¹) * w⁻¹ := by group
    _ = u * w * u⁻¹ * w := by rw [hww, one_mul, hwi]
    _ = (w * (u * w * u⁻¹))⁻¹ := by
      rw [show (w * (u * w * u⁻¹))⁻¹ = u * w⁻¹ * u⁻¹ * w⁻¹ by group, hwi]

theorem rot_mul {w : G} (hw : w ∈ W) : rot w u * w = w * (rot w u)⁻¹ := by
  have hww := h.mul_self_eq_one hw
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  rw [← h.conj_rot hw]
  calc rot w u * w = (w * w) * rot w u * w⁻¹ := by rw [hww, one_mul, hwi]
    _ = w * (w * rot w u * w⁻¹) := by group

theorem L_le_sup_rot {w : G} (hw : w ∈ W) (hwA : w ∉ A W P) :
    L ≤ X W P u ⊔ zpowers w ⊔ zpowers (rot w u) := by
  have hwT : w ∈ X W P u ⊔ zpowers w ⊔ zpowers (rot w u) :=
    mem_sup_left (mem_sup_right (mem_zpowers w))
  have hcT : rot w u ∈ X W P u ⊔ zpowers w ⊔ zpowers (rot w u) := mem_sup_right (mem_zpowers _)
  have hXT : X W P u ≤ X W P u ⊔ zpowers w ⊔ zpowers (rot w u) := le_sup_left.trans le_sup_left
  have hW : W ≤ X W P u ⊔ zpowers w ⊔ zpowers (rot w u) := by
    refine le_trans (le_of_eq (h.sup_zpowers_eq hw hwA).symm) (sup_le (h.A_le_X.trans hXT) ?_)
    rw [zpowers_le]
    exact hwT
  have hWu : Wu W u ≤ X W P u ⊔ zpowers w ⊔ zpowers (rot w u) := by
    have e : Wu W u = B W P u ⊔ zpowers (u * w * u⁻¹) := by
      conv_lhs => rw [Wu, ← h.sup_zpowers_eq hw hwA]
      rw [Subgroup.map_sup, h.map_conj_A, MonoidHom.map_zpowers]
      rfl
    rw [e]
    refine sup_le (h.B_le_X.trans hXT) ?_
    rw [zpowers_le]
    have e2 : u * w * u⁻¹ = w⁻¹ * rot w u := by
      show u * w * u⁻¹ = w⁻¹ * (w * (u * w * u⁻¹))
      group
    rw [e2]
    exact mul_mem (inv_mem hwT) hcT
  exact le_trans (le_of_eq h.sup_eq.symm) (sup_le hW hWu)

theorem exists_odd_pow_rot_mem_X {w : G} (hw : w ∈ W) (hwA : w ∉ A W P) :
    ∃ m : ℕ, Odd m ∧ rot w u ^ m ∈ X W P u := by
  have hwL := h.W_le hw
  have hcL := h.rot_mem_L hw
  have hww := h.mul_self_eq_one hw
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hconj := h.conj_rot hw
  have hcw := h.rot_mul hw
  have hgen := h.L_le_sup_rot hw hwA
  set c := rot w u with hcdef
  set E := X W P u ⊔ zpowers (c ^ 2) with hE
  have hsq : w * c ^ 2 * w⁻¹ = (c ^ 2)⁻¹ := by
    calc w * c ^ 2 * w⁻¹ = (w * c * w⁻¹) * (w * c * w⁻¹) := by rw [sq]; group
      _ = c⁻¹ * c⁻¹ := by rw [hconj]
      _ = (c ^ 2)⁻¹ := by rw [sq]; exact (mul_inv_rev c c).symm
  have hEn : L ≤ normalizer (E : Set G) := by
    refine hgen.trans (sup_le (sup_le (le_sup_left.trans le_normalizer) ?_) ?_)
    · rw [zpowers_le]
      refine mem_normalizer_sup_zpowers (h.L_le_normalizer_X hwL) ?_ ?_
      · rw [hsq]
        exact mem_sup_right (inv_mem (mem_zpowers _))
      · have hsq' := hsq
        rw [hwi] at hsq' ⊢
        rw [hsq']
        exact mem_sup_right (inv_mem (mem_zpowers _))
    · rw [zpowers_le]
      refine mem_normalizer_sup_zpowers (h.L_le_normalizer_X hcL) ?_ ?_
      · rw [show c * c ^ 2 * c⁻¹ = c ^ 2 by simp [sq, mul_assoc]]
        exact mem_sup_right (mem_zpowers _)
      · rw [show c⁻¹ * c ^ 2 * c = c ^ 2 by simp [sq, mul_assoc]]
        exact mem_sup_right (mem_zpowers _)
  have hF : L ≤ fixMod L E hEn w := by
    refine hgen.trans (sup_le (sup_le ?_ ?_) ?_)
    · intro x hx
      refine ⟨h.X_le_L hx, mem_sup_left ?_⟩
      have h1 : w⁻¹ * x * w⁻¹⁻¹ ∈ X W P u :=
        (mem_normalizer_iff.mp (h.L_le_normalizer_X (inv_mem hwL)) x).mp hx
      have e : w⁻¹ * (x * w * x⁻¹) = (w⁻¹ * x * w⁻¹⁻¹) * x⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem hx)
    · rw [zpowers_le]
      refine ⟨hwL, ?_⟩
      rw [mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _
    · rw [zpowers_le]
      refine ⟨hcL, mem_sup_right ?_⟩
      have e : w⁻¹ * (c * w * c⁻¹) = (c ^ 2)⁻¹ := by
        rw [hcw]
        simp [sq, mul_assoc]
      rw [e]
      exact inv_mem (mem_zpowers _)
  have hcE : c ∈ E := by
    have h1 := (hF h.u_mem).2
    have e : w⁻¹ * (u * w * u⁻¹) = c := by
      rw [hcdef]
      calc w⁻¹ * (u * w * u⁻¹) = (w * w)⁻¹ * (w * (u * w * u⁻¹)) := by group
        _ = w * (u * w * u⁻¹) := by rw [hww, inv_one, one_mul]
    rwa [e] at h1
  have hle : zpowers (c ^ 2) ≤ normalizer (X W P u : Set G) := by
    rw [zpowers_le]
    exact h.L_le_normalizer_X (pow_mem hcL 2)
  rw [← SetLike.mem_coe, hE, coe_mul_of_right_le_normalizer_left _ _ hle, Set.mem_mul] at hcE
  obtain ⟨x, hx, z, hz, hxz⟩ := hcE
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hxc : c ^ (1 - 2 * k) ∈ X W P u := by
    have e : x = c * ((c ^ 2) ^ k)⁻¹ := eq_mul_inv_of_mul_eq hxz
    have e2 : c ^ (1 - 2 * k) = c * ((c ^ 2) ^ k)⁻¹ := by group
    rw [e2, ← e]
    exact hx
  rcases le_or_gt 0 (1 - 2 * k) with hk | hk
  · have ht := Int.toNat_of_nonneg hk
    refine ⟨(1 - 2 * k).toNat, ?_, ?_⟩
    · rw [Nat.odd_iff]
      omega
    · rw [← zpow_natCast, ht]
      exact hxc
  · have hk' : 0 ≤ 2 * k - 1 := by omega
    have ht := Int.toNat_of_nonneg hk'
    refine ⟨(2 * k - 1).toNat, ?_, ?_⟩
    · rw [Nat.odd_iff]
      omega
    · rw [← zpow_natCast, ht]
      have e : c ^ (2 * k - 1) = (c ^ (1 - 2 * k))⁻¹ := by
        rw [← zpow_neg, neg_sub]
      rw [e]
      exact inv_mem hxc

theorem mem_D_of_comm_rot_mem_D {w : G} (hw : w ∈ W) (hwA : w ∉ A W P) {v : G}
    (hv : v ∈ X W P u) (hc : rot w u * v * (rot w u)⁻¹ * v⁻¹ ∈ D W P u) : v ∈ D W P u := by
  have hwL := h.W_le hw
  have hcL := h.rot_mem_L hw
  have hvL := h.X_le_L hv
  have hww := h.mul_self_eq_one hw
  have hcw := h.rot_mul hw
  have hgen := h.L_le_sup_rot hw hwA
  set c := rot w u with hcdef
  have hL : ∀ x (hx : x ∈ X W P u), w ∈ h.commD x (h.X_le_L hx) →
      c ∈ h.commD x (h.X_le_L hx) → x ∈ D W P u := by
    intro x hx h1 h2
    have hLx : L ≤ h.commD x (h.X_le_L hx) := by
      refine hgen.trans (sup_le (sup_le (fun y hy => ⟨h.X_le_L hy, h.comm_X_mem_D hx hy⟩) ?_) ?_)
      · rw [zpowers_le]
        exact h1
      · rw [zpowers_le]
        exact h2
    exact h.mem_D_of_comm_mem_D hx (fun g hg => h.comm_mem_D_symm (hLx hg).2)
  set p := w * v * w⁻¹ with hp
  have hpX : p ∈ X W P u := (mem_normalizer_iff.mp (h.L_le_normalizer_X hwL) v).mp hv
  have hwp : w * p * w⁻¹ = v := by
    calc w * (w * v * w⁻¹) * w⁻¹ = (w * w) * v * (w * w)⁻¹ := by group
      _ = v := by rw [hww]; group
  have hc' : c⁻¹ * v * c * v⁻¹ ∈ D W P u := by
    have h1 : c⁻¹ ∈ h.commD v hvL := (h.commD v hvL).inv_mem ⟨hcL, h.comm_mem_D_symm hc⟩
    simpa using h.comm_mem_D_symm h1.2
  have hcp : c * p * c⁻¹ * p⁻¹ ∈ D W P u := by
    have e : c * p * c⁻¹ * p⁻¹ = w * (c⁻¹ * v * c * v⁻¹) * w⁻¹ := by
      calc c * (w * v * w⁻¹) * c⁻¹ * (w * v * w⁻¹)⁻¹
          = (c * w) * v * (c * w)⁻¹ * (w * v⁻¹ * w⁻¹) := by group
        _ = (w * c⁻¹) * v * (w * c⁻¹)⁻¹ * (w * v⁻¹ * w⁻¹) := by rw [hcw]
        _ = w * (c⁻¹ * v * c * v⁻¹) * w⁻¹ := by group
    rw [e, h.conj_D hc' hwL]
    exact hc'
  have hv'D : v * p ∈ D W P u := by
    refine hL (v * p) (mul_mem hv hpX) ⟨hwL, h.comm_mem_D_symm ?_⟩
      ⟨hcL, h.comm_mem_D_symm (h.comm_mul_mem_D hvL hc hcp)⟩
    have e : w * (v * p) * w⁻¹ * (v * p)⁻¹ = p * v * p⁻¹ * v⁻¹ := by
      calc w * (v * p) * w⁻¹ * (v * p)⁻¹ = (w * v * w⁻¹) * (w * p * w⁻¹) * p⁻¹ * v⁻¹ := by
            group
        _ = p * v * p⁻¹ * v⁻¹ := by rw [hwp, ← hp]
    rw [e]
    exact h.comm_X_mem_D hpX hv
  refine hL v hv ⟨hwL, h.comm_mem_D_symm ?_⟩ ⟨hcL, h.comm_mem_D_symm hc⟩
  have e : w * v * w⁻¹ * v⁻¹ = (v⁻¹ * (v * p)) * v⁻¹ := by
    rw [hp]
    group
  rw [e, h.comm_D hv'D (L.inv_mem hvL), mul_assoc (v * p), ← mul_inv_rev]
  exact mul_mem hv'D (inv_mem (h.sq_X_mem_D hv))

theorem isPGroup_of_rot_mem_X {w : G} (hw : w ∈ W) (hwA : w ∉ A W P) (hc : rot w u ∈ X W P u) :
    IsPGroup 2 L := by
  have hW2 : IsPGroup 2 W := fun g => ⟨1, Subtype.ext (by simpa using h.elemAb.2 g g.2)⟩
  have hXW : IsPGroup 2 (X W P u ⊔ W : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (h.isPGroup_P.to_le h.X_le_P) hW2 h.W_le_normalizer_X
  refine hXW.to_le ((h.L_le_sup_rot hw hwA).trans (sup_le (sup_le le_sup_left ?_) ?_))
  · exact (zpowers_le.mpr hw).trans le_sup_right
  · exact (zpowers_le.mpr hc).trans le_sup_left

theorem P_le_X [Finite G] (hL : ¬ IsPGroup 2 L) : P ≤ X W P u := by
  obtain ⟨w, hw, hwA⟩ := h.exists_mem_not_mem_A
  have hwL := h.W_le hw
  have hww := h.mul_self_eq_one hw
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hcL := h.rot_mem_L hw
  have hconj := h.conj_rot hw
  have hgen := h.L_le_sup_rot hw hwA
  obtain ⟨m, hm, hcm⟩ := h.exists_odd_pow_rot_mem_X hw hwA
  have hcX : rot w u ∉ X W P u := fun hc => hL (h.isPGroup_of_rot_mem_X hw hwA hc)
  set c := rot w u with hcdef
  have h2 : ∀ g ∈ P, ∀ k : ℕ, Odd k → g ^ k ∈ X W P u → g ∈ X W P u := by
    intro g hg k hk hgk
    obtain ⟨e, he⟩ := h.isPGroup_P ⟨g, hg⟩
    exact mem_of_odd_pow_mem (by simpa using congrArg Subtype.val he) hk hgk
  have hXc : zpowers c ≤ normalizer (X W P u : Set G) :=
    zpowers_le.mpr (h.L_le_normalizer_X hcL)
  have hmemY : ∀ y ∈ X W P u ⊔ zpowers c, ∃ x ∈ X W P u, ∃ k : ℤ, y = x * c ^ k := by
    intro y hy
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hXc, Set.mem_mul] at hy
    obtain ⟨x, hx, z, hz, rfl⟩ := hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact ⟨x, hx, k, rfl⟩
  have hPY : ∀ p ∈ P, p ∈ X W P u ⊔ zpowers c → p ∈ X W P u := by
    intro p hp hpY
    obtain ⟨x, hx, k, rfl⟩ := hmemY p hpY
    have hck : c ^ k ∈ P := by
      have := P.mul_mem (P.inv_mem (h.X_le_P hx)) hp
      rwa [inv_mul_cancel_left] at this
    refine mul_mem hx (h2 _ hck m hm ?_)
    rw [show (c ^ k) ^ m = (c ^ m) ^ k by group]
    exact zpow_mem hcm k
  intro p hp
  by_cases hpY : p ∈ X W P u ⊔ zpowers c
  · exact hPY p hp hpY
  exfalso
  have hwc' : w * c⁻¹ * w⁻¹ = c := by
    rw [show w * c⁻¹ * w⁻¹ = (w * c * w⁻¹)⁻¹ by group, hconj, inv_inv]
  have hwY : w ∈ normalizer ((X W P u ⊔ zpowers c : Subgroup G) : Set G) := by
    refine mem_normalizer_sup_zpowers (h.L_le_normalizer_X hwL) ?_ ?_
    · rw [hconj]
      exact mem_sup_right (inv_mem (mem_zpowers c))
    · rw [show w⁻¹ * c * w = w * c * w⁻¹ by rw [hwi], hconj]
      exact mem_sup_right (inv_mem (mem_zpowers c))
  have hpL : p ∈ (X W P u ⊔ zpowers c) ⊔ zpowers w := by
    have := hgen (h.P_le hp)
    rwa [sup_right_comm] at this
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr hwY),
    Set.mem_mul] at hpL
  obtain ⟨y, hy, z, hz, hyz⟩ := hpL
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
  rcases Int.even_or_odd j with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · apply hpY
    rw [← hyz, ← two_mul, zpow_mul, zpow_two, hww, one_zpow, mul_one]
    exact hy
  rw [zpow_add, zpow_mul, zpow_two, hww, one_zpow, one_mul, zpow_one] at hyz
  have ht : c * y * c * y⁻¹ ∈ X W P u := by
    refine hPY _ ?_ (mul_mem (mul_mem (mul_mem (mem_sup_right (mem_zpowers c)) hy)
      (mem_sup_right (mem_zpowers c))) (inv_mem hy))
    have h1 : c * p * c⁻¹ * p⁻¹ ∈ P :=
      mul_mem ((mem_normalizer_iff.mp (h.L_le_normalizer_P hcL) p).mp hp) (inv_mem hp)
    have e : c * p * c⁻¹ * p⁻¹ = c * y * c * y⁻¹ := by
      rw [← hyz]
      calc c * (y * w) * c⁻¹ * (y * w)⁻¹ = c * y * (w * c⁻¹ * w⁻¹) * y⁻¹ := by group
        _ = c * y * c * y⁻¹ := by rw [hwc']
    rwa [e] at h1
  obtain ⟨x, hx, k, rfl⟩ := hmemY y hy
  have hcx : c⁻¹ * x * c ∈ X W P u := by
    have := (mem_normalizer_iff.mp (h.L_le_normalizer_X (inv_mem hcL)) x).mp hx
    rwa [inv_inv] at this
  have hc2 : c ^ 2 ∈ X W P u := by
    have e1 : c * (x * c ^ k) * c * (x * c ^ k)⁻¹ = c * x * c * x⁻¹ := by group
    rw [e1] at ht
    have e2 : c ^ 2 = (c * x * c * x⁻¹) * (c⁻¹ * x * c * x⁻¹)⁻¹ := by rw [sq]; group
    rw [e2]
    exact mul_mem ht (inv_mem (mul_mem hcx (inv_mem hx)))
  obtain ⟨t', rfl⟩ := hm
  apply hcX
  have e3 : c = c ^ (2 * t' + 1) * ((c ^ 2) ^ t')⁻¹ := by group
  rw [e3]
  exact mul_mem hcm (inv_mem (pow_mem hc2 t'))

theorem false_of_centralizes [Finite G] (hL : ¬ IsPGroup 2 L) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hCQ : centralizer (Q : Set G) ≤ Q)
    (hQL : ∀ q ∈ Q, ∀ g ∈ L, q * g * q⁻¹ * g⁻¹ ∈ P) {v : G} (hv : v ∈ W) (hvA : v ∉ A W P)
    (hvX : ∀ x ∈ X W P u, v * x = x * v) : False := by
  have hPX := h.P_le_X hL
  obtain ⟨m, hm, hcm⟩ := h.exists_odd_pow_rot_mem_X hv hvA
  have hcL := h.rot_mem_L hv
  have hcX : rot v u ∉ X W P u := fun hc => hL (h.isPGroup_of_rot_mem_X hv hvA hc)
  set c := rot v u with hcdef
  have hcP : ∀ x ∈ P, c * x = x * c := by
    intro x hxP
    have hx := hPX hxP
    have hux : u⁻¹ * x * u ∈ X W P u := by
      have := (mem_normalizer_iff.mp (h.L_le_normalizer_X (inv_mem h.u_mem)) x).mp hx
      rwa [inv_inv] at this
    have h1 : (u * v * u⁻¹) * x = x * (u * v * u⁻¹) := by
      calc u * v * u⁻¹ * x = u * (v * (u⁻¹ * x * u)) * u⁻¹ := by group
        _ = u * ((u⁻¹ * x * u) * v) * u⁻¹ := by rw [hvX _ hux]
        _ = x * (u * v * u⁻¹) := by group
    calc c * x = v * ((u * v * u⁻¹) * x) := by rw [hcdef]; group
      _ = v * (x * (u * v * u⁻¹)) := by rw [h1]
      _ = (v * x) * (u * v * u⁻¹) := by group
      _ = x * c := by rw [hvX x hx, hcdef]; group
  obtain ⟨a, n', hn', hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hgL : c ^ 2 ^ a ∈ L := pow_mem hcL _
  have hgn : (c ^ 2 ^ a) ^ n' = 1 := by rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hgP : ∀ x ∈ P, c ^ 2 ^ a * x = x * c ^ 2 ^ a := fun x hx =>
    ((Commute.pow_left (hcP x hx) (2 ^ a)) : _)
  set g := c ^ 2 ^ a with hg
  have hgQ : g ∈ centralizer (Q : Set G) := by
    rw [mem_centralizer_iff]
    intro q hq
    set e := q⁻¹ * g * q * g⁻¹ with he
    have heP : e ∈ P := by
      have := hQL q⁻¹ (inv_mem hq) g hgL
      rwa [inv_inv] at this
    have hge : g * e = e * g := hgP e heP
    have hk : ∀ k : ℕ, g ^ k * q * (g ^ k)⁻¹ = q * e ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hgek : g * e ^ k * g⁻¹ = e ^ k := by
          rw [((Commute.pow_right hge k) : g * e ^ k = e ^ k * g), mul_inv_cancel_right]
        have hgq : g * q * g⁻¹ = q * e := by rw [he]; group
        calc g ^ (k + 1) * q * (g ^ (k + 1))⁻¹ = g * (g ^ k * q * (g ^ k)⁻¹) * g⁻¹ := by group
          _ = (g * q * g⁻¹) * (g * e ^ k * g⁻¹) := by rw [ih]; group
          _ = q * e ^ (k + 1) := by rw [hgq, hgek]; group
    have hen : e ^ n' = 1 := by
      have := hk n'
      rw [hgn, one_mul, inv_one, mul_one] at this
      exact (mul_eq_left.mp this.symm)
    obtain ⟨b, hb⟩ := h.isPGroup_P ⟨e, heP⟩
    have he1 : e = 1 := by
      have := mem_of_odd_pow_mem (K := ⊥) (by simpa using congrArg Subtype.val hb) hn'
        (by rw [hen]; exact one_mem _)
      rwa [mem_bot] at this
    rw [he] at he1
    have h3 : q⁻¹ * g * q = g := mul_inv_eq_one.mp he1
    calc q * g = q * (q⁻¹ * g * q) := by rw [h3]
      _ = g * q := by group
  obtain ⟨b, hb⟩ := hQ ⟨g, hCQ hgQ⟩
  have hg1 : g = 1 := by
    have := mem_of_odd_pow_mem (K := ⊥) (by simpa using congrArg Subtype.val hb) hn'
      (by rw [hgn]; exact one_mem _)
    rwa [mem_bot] at this
  exact hcX (mem_of_odd_pow_mem (by rw [← hg, hg1]) hm hcm)

theorem X_le_of_relIndex_le_four [Finite G] {X₁ : Subgroup G}
    (hX₁ : L ≤ normalizer (X₁ : Set G)) (hDX₁ : D W P u ≤ X₁)
    (hidx : X₁.relIndex (X W P u) ≤ 4) (h3 : ¬ 3 ∣ Nat.card L) : X W P u ≤ X₁ := by
  obtain ⟨w, hw, hwA⟩ := h.exists_mem_not_mem_A
  have hcL := h.rot_mem_L hw
  obtain ⟨m, hm, hcm⟩ := h.exists_odd_pow_rot_mem_X hw hwA
  set c := rot w u with hcdef
  have hcX : c ∈ normalizer (X W P u : Set G) := h.L_le_normalizer_X hcL
  have hDX : D W P u ≤ X W P u := h.D_le_A.trans h.A_le_X
  have hcF : ∀ v ∈ X W P u, c ∈ fixMod L X₁ hX₁ v := by
    intro v hv
    obtain ⟨d, hd0, hd4, hdF⟩ := exists_pow_mem_fixMod hX₁ hcL hcX hv hidx
    refine Subgroup.mem_of_forall_prime_exists_pow_mem (fun p hp => ?_)
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨m, fun h2 => by have := Nat.odd_iff.mp hm; omega, ⟨pow_mem hcL m, hDX₁ ?_⟩⟩
      have e : v⁻¹ * (c ^ m * v * (c ^ m)⁻¹) = v⁻¹ * c ^ m * v⁻¹⁻¹ * (c ^ m)⁻¹ := by group
      rw [e]
      exact h.comm_X_mem_D (inv_mem hv) hcm
    by_cases hp3 : p = 3
    · subst hp3
      refine ⟨orderOf c, fun h3' => h3 (h3'.trans (Subgroup.orderOf_dvd_natCard L hcL)), ?_⟩
      rw [pow_orderOf_eq_one]
      exact one_mem _
    refine ⟨d, fun hpd => ?_, hdF⟩
    have hp4 : p ≤ 4 := (Nat.le_of_dvd hd0 hpd).trans hd4
    have hp2' := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · norm_num at hp
  have hf : ∀ v ∈ X W P u, c * v * c⁻¹ * v⁻¹ ∈ X₁ ⊓ X W P u := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem ((mem_normalizer_iff.mp hcX v).mp hv) (inv_mem hv)⟩
    have h1 := (mem_normalizer_iff.mp (hX₁ (h.X_le_L hv)) _).mp (hcF v hv).2
    have e : v * (v⁻¹ * (c * v * c⁻¹)) * v⁻¹ = c * v * c⁻¹ * v⁻¹ := by group
    rwa [e] at h1
  have hmul : ∀ v₁ ∈ X W P u, ∀ v₂ ∈ X W P u,
      (c * (v₁ * v₂) * c⁻¹ * (v₁ * v₂)⁻¹)⁻¹ * ((c * v₁ * c⁻¹ * v₁⁻¹) * (c * v₂ * c⁻¹ * v₂⁻¹)) ∈
        D W P u := by
    intro v₁ hv₁ v₂ hv₂
    have hq : c * v₂ * c⁻¹ ∈ X W P u := (mem_normalizer_iff.mp hcX v₂).mp hv₂
    have ht := h.comm_X_mem_D (inv_mem hq) (inv_mem hv₁)
    have e : (c * (v₁ * v₂) * c⁻¹ * (v₁ * v₂)⁻¹)⁻¹ *
          ((c * v₁ * c⁻¹ * v₁⁻¹) * (c * v₂ * c⁻¹ * v₂⁻¹)) =
        ((v₁ * v₂) * ((c * v₂ * c⁻¹)⁻¹ * v₁⁻¹ * (c * v₂ * c⁻¹)⁻¹⁻¹ * v₁⁻¹⁻¹) * (v₁ * v₂)⁻¹) *
          (v₁ * v₂ * v₁⁻¹ * v₂⁻¹) := by
      group
    rw [e, h.conj_D ht (L.mul_mem (h.X_le_L hv₁) (h.X_le_L hv₂))]
    exact mul_mem ht (h.comm_X_mem_D hv₁ hv₂)
  have hcard := card_le_of_hom_mod hDX (le_inf hDX₁ hDX)
    (fun g hg d hd => by rw [h.conj_D hd (h.X_le_L (Subgroup.mem_inf.mp hg).2)]; exact hd)
    (fun v => c * v * c⁻¹ * v⁻¹) hf hmul
    (fun v hv hvD => h.mem_D_of_comm_rot_mem_D hw hwA hv hvD)
  have := Subgroup.eq_of_le_of_card_ge (inf_le_right : X₁ ⊓ X W P u ≤ X W P u) hcard
  calc X W P u = X₁ ⊓ X W P u := this.symm
    _ ≤ X₁ := inf_le_left

end LCfg

end CFSG.RankThree.S4Free.Stell33
