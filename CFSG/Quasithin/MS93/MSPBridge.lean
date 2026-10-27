module

public import CFSG.Quasithin.MS93.MSPBasic
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {G : Type} [Group G] {F : Type} [Field F]

structure NatCoord (A V Z : Subgroup G) (α : ↥A →* Sp4 F) where
  toVec : ↥V →* Multiplicative (V4 F)
  surj : Function.Surjective toVec
  ker_eq : toVec.ker = Z.subgroupOf V
  equiv : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
    Multiplicative.toAdd (toVec v) = mat (α a) *ᵥ Multiplicative.toAdd (toVec u)

theorem nonempty_natCoord {A V Z : Subgroup G} {α : ↥A →* Sp4 F}
    (h : IsSumOfNaturalModulesVia A V Z α false 1) : Nonempty (NatCoord A V Z α) := by
  obtain ⟨-, -, β, hβs, hβk, hβeq⟩ := h
  let π : Multiplicative (Fin 1 → V4 F) →* Multiplicative (V4 F) :=
    { toFun := fun x => Multiplicative.ofAdd (Multiplicative.toAdd x 0)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπinj : Function.Injective π := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact congrArg Multiplicative.toAdd hxy
  refine ⟨⟨π.comp β, ?_, ?_, fun a u v huv => ?_⟩⟩
  · intro y
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd fun _ => Multiplicative.toAdd y)
    exact ⟨u, by rw [MonoidHom.comp_apply, hu]; rfl⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ hπinj, hβk]
  · have := hβeq a u v huv 0
    simpa [π, moduleAct] using this

namespace NatCoord

variable {A V Z : Subgroup G} {α : ↥A →* Sp4 F} (c : NatCoord A V Z α)

@[expose] def vec (u : ↥V) : V4 F := Multiplicative.toAdd (c.toVec u)

theorem vec_mul (u u' : ↥V) : c.vec (u * u') = c.vec u + c.vec u' := by
  simp [vec]

theorem vec_inv (u : ↥V) : c.vec u⁻¹ = -c.vec u := by
  simp [vec]

theorem vec_eq_zero_iff (u : ↥V) : c.vec u = 0 ↔ (u : G) ∈ Z := by
  rw [vec, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← MonoidHom.mem_ker, c.ker_eq,
    Subgroup.mem_subgroupOf]

theorem exists_vec_eq (w : V4 F) : ∃ u : ↥V, c.vec u = w := by
  obtain ⟨u, hu⟩ := c.surj (Multiplicative.ofAdd w)
  exact ⟨u, by rw [vec, hu]; rfl⟩

theorem vec_conj (a : ↥A) (u : ↥V) (hu : (a : G) * u * (a : G)⁻¹ ∈ V) :
    c.vec ⟨_, hu⟩ = mat (α a) *ᵥ c.vec u :=
  c.equiv a u ⟨_, hu⟩ rfl

theorem vec_commutator (a : ↥A) (u : ↥V) (hu : (a : G) * u * (a : G)⁻¹ ∈ V) :
    c.vec ⟨(a : G) * u * (a : G)⁻¹ * (u : G)⁻¹, mul_mem hu (inv_mem u.2)⟩ =
      mat (α a) *ᵥ c.vec u - c.vec u := by
  have h := c.vec_mul ⟨_, hu⟩ u⁻¹
  rw [c.vec_inv, c.vec_conj a u hu] at h
  rw [← sub_eq_add_neg] at h
  exact h

theorem vec_mem_fixSp_iff (hAV : A ≤ Subgroup.normalizer (V : Set G)) (B : Subgroup ↥A)
    (u : ↥V) :
    c.vec u ∈ fixSp (B.map α) ↔ ∀ b ∈ B, ((b : G) * u * (b : G)⁻¹ * (u : G)⁻¹) ∈ Z := by
  have hconj : ∀ b : ↥A, (b : G) * u * (b : G)⁻¹ ∈ V := fun b =>
    (Subgroup.mem_normalizer_iff.1 (hAV b.2) u).1 u.2
  constructor
  · intro h b hb
    have h1 := h _ (Subgroup.mem_map_of_mem α hb)
    rw [← c.vec_eq_zero_iff ⟨_, mul_mem (hconj b) (inv_mem u.2)⟩, c.vec_commutator b u (hconj b),
      h1, sub_self]
  · rintro h _ ⟨b, hb, rfl⟩
    have h1 := (c.vec_eq_zero_iff ⟨_, mul_mem (hconj b) (inv_mem u.2)⟩).2 (h b hb)
    rw [c.vec_commutator b u (hconj b), sub_eq_zero] at h1
    exact h1

theorem vec_mem_fixSp (hAV : A ≤ Subgroup.normalizer (V : Set G)) (B : Subgroup ↥A) (u : ↥V)
    (hu : ∀ b ∈ B, (b : G) * u = u * b) : c.vec u ∈ fixSp (B.map α) := by
  rw [c.vec_mem_fixSp_iff hAV]
  intro b hb
  rw [hu b hb, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem Z

theorem mem_commSp_iff (hAV : A ≤ Subgroup.normalizer (V : Set G)) (B : Subgroup ↥A)
    (w : V4 F) :
    w ∈ commSp (B.map α) ↔ ∃ u : ↥V, (u : ↥V) ∈ Subgroup.closure
      {x : ↥V | ∃ b ∈ B, ∃ v : ↥V, (x : G) = (b : G) * v * (b : G)⁻¹ * (v : G)⁻¹} ∧
        c.vec u = w := by
  have hconj : ∀ (b : ↥A) (v : ↥V), (b : G) * v * (b : G)⁻¹ ∈ V := fun b v =>
    (Subgroup.mem_normalizer_iff.1 (hAV b.2) v).1 v.2
  set S : Set ↥V := {x : ↥V | ∃ b ∈ B, ∃ v : ↥V, (x : G) = (b : G) * v * (b : G)⁻¹ * (v : G)⁻¹}
  have himage : ∀ u ∈ Subgroup.closure S, c.vec u ∈ commSp (B.map α) := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, hxv⟩ := hx
      have : x = ⟨(b : G) * v * (b : G)⁻¹ * (v : G)⁻¹, mul_mem (hconj b v) (inv_mem v.2)⟩ :=
        Subtype.ext hxv
      rw [this, c.vec_commutator b v (hconj b v)]
      exact sub_mem_commSp (Subgroup.mem_map_of_mem α hb) _
    | one => simp [vec]
    | mul x y _ _ hx hy =>
      rw [c.vec_mul]
      exact add_mem hx hy
    | inv x _ hx =>
      rw [c.vec_inv]
      exact neg_mem hx
  have hsmul : ∀ u ∈ Subgroup.closure S, ∀ k : F, ∃ u' ∈ Subgroup.closure S,
      c.vec u' = k • c.vec u := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      intro k
      obtain ⟨b, hb, v, hxv⟩ := hx
      obtain ⟨v', hv'⟩ := c.exists_vec_eq (k • c.vec v)
      refine ⟨⟨(b : G) * v' * (b : G)⁻¹ * (v' : G)⁻¹, mul_mem (hconj b v') (inv_mem v'.2)⟩,
        Subgroup.subset_closure ⟨b, hb, v', rfl⟩, ?_⟩
      have hx' : x = ⟨(b : G) * v * (b : G)⁻¹ * (v : G)⁻¹, mul_mem (hconj b v) (inv_mem v.2)⟩ :=
        Subtype.ext hxv
      rw [hx', c.vec_commutator b v' (hconj b v'), c.vec_commutator b v (hconj b v), hv',
        mulVec_smul, smul_sub]
    | one =>
      intro k
      exact ⟨1, one_mem _, by simp [vec]⟩
    | mul x y _ _ hx hy =>
      intro k
      obtain ⟨x', hx', ex⟩ := hx k
      obtain ⟨y', hy', ey⟩ := hy k
      exact ⟨x' * y', mul_mem hx' hy', by rw [c.vec_mul, c.vec_mul, ex, ey, smul_add]⟩
    | inv x _ hx =>
      intro k
      obtain ⟨x', hx', ex⟩ := hx k
      exact ⟨x'⁻¹, inv_mem hx', by rw [c.vec_inv, c.vec_inv, ex, smul_neg]⟩
  let W : Submodule F (V4 F) :=
    { carrier := {w | ∃ u : ↥V, u ∈ Subgroup.closure S ∧ c.vec u = w}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', mul_mem hu hu', c.vec_mul u u'⟩
      zero_mem' := ⟨1, one_mem _, by simp [vec]⟩
      smul_mem' := by
        rintro k _ ⟨u, hu, rfl⟩
        exact hsmul u hu k }
  constructor
  · intro hw
    have hle : commSp (B.map α) ≤ W := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨b, hb, rfl⟩, w, rfl⟩
      obtain ⟨v, rfl⟩ := c.exists_vec_eq w
      refine ⟨⟨(b : G) * v * (b : G)⁻¹ * (v : G)⁻¹, mul_mem (hconj b v) (inv_mem v.2)⟩,
        Subgroup.subset_closure ⟨b, hb, v, rfl⟩, ?_⟩
      exact c.vec_commutator b v (hconj b v)
    exact hle hw
  · rintro ⟨u, hu, rfl⟩
    exact himage u hu

include c in
theorem card_eq [Finite G] : Nat.card ↥V = Nat.card ↥(V ⊓ Z) * Nat.card (V4 F) := by
  have h1 := Subgroup.card_mul_index c.toVec.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 c.surj, Subgroup.card_top, c.ker_eq] at h1
  have h2 : Nat.card ↥(Z.subgroupOf V) = Nat.card ↥(V ⊓ Z) := by
    rw [← Subgroup.inf_subgroupOf_left, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, h2]
  rfl

include c in
theorem card_le_relIndex [Finite G] [Finite F] (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (E : Subgroup G) :
    Nat.card (V4 F) ≤ Nat.card (fixSp ((E.subgroupOf A).map α)) *
      (Subgroup.centralizer (E : Set G)).relIndex V := by
  set CE : Subgroup ↥V := (Subgroup.centralizer (E : Set G)).subgroupOf V
  have h1 := Subgroup.relIndex_mul_card (H := c.toVec.ker) (K := CE)
  rw [Subgroup.relIndex_ker] at h1
  have hmap : Nat.card (CE.map c.toVec) ≤ Nat.card (fixSp ((E.subgroupOf A).map α)) := by
    let f : ↥(CE.map c.toVec) → ↥(fixSp ((E.subgroupOf A).map α)) := fun x =>
      ⟨Multiplicative.toAdd (x : Multiplicative (V4 F)), by
        obtain ⟨_, ⟨u, hu, rfl⟩⟩ := x
        refine c.vec_mem_fixSp hAV _ u fun b hb => ?_
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hu) b
          (Subgroup.mem_subgroupOf.1 hb)⟩
    refine Nat.card_le_card_of_injective f fun x y hxy => Subtype.ext ?_
    exact Multiplicative.toAdd.injective (congrArg Subtype.val hxy :)
  have hker : Nat.card ↥(c.toVec.ker ⊓ CE) ≤ Nat.card ↥(V ⊓ Z) := by
    have hle : c.toVec.ker ⊓ CE ≤ Z.subgroupOf V := by
      rw [c.ker_eq]
      exact inf_le_left
    calc Nat.card ↥(c.toVec.ker ⊓ CE) ≤ Nat.card ↥(Z.subgroupOf V) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥(V ⊓ Z) := by
        rw [← Subgroup.inf_subgroupOf_left, inf_comm]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hCE : Nat.card CE * (Subgroup.centralizer (E : Set G)).relIndex V = Nat.card ↥V := by
    have := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (E : Set G)) (K := V)
    rw [mul_comm, ← this]
    congr 1
    have e1 : Nat.card CE = Nat.card ↥((Subgroup.centralizer (E : Set G) ⊓ V).subgroupOf V) := by
      rw [Subgroup.inf_subgroupOf_right]
    rw [e1, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hZ : 0 < Nat.card ↥(V ⊓ Z) := Nat.card_pos
  have key : Nat.card ↥(V ⊓ Z) * Nat.card (V4 F) ≤ Nat.card ↥(V ⊓ Z) *
      (Nat.card (fixSp ((E.subgroupOf A).map α)) *
        (Subgroup.centralizer (E : Set G)).relIndex V) := by
    rw [← c.card_eq, ← hCE, ← h1]
    calc Nat.card ↥(CE.map c.toVec) * Nat.card ↥(c.toVec.ker ⊓ CE) *
          (Subgroup.centralizer (E : Set G)).relIndex V
        ≤ Nat.card (fixSp ((E.subgroupOf A).map α)) * Nat.card ↥(V ⊓ Z) *
          (Subgroup.centralizer (E : Set G)).relIndex V :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hmap hker)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left key hZ

end NatCoord

end CFSG.Quasithin.MS93.MSP
