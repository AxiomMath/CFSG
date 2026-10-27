module

public import CFSG.Quasithin.Background.G2A5Core
public import CFSG.Quasithin.Background.G2A5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

structure RawData5 (A K VL : Subgroup G) where
  hnorm : A ≤ Subgroup.normalizer (VL : Set G)
  θ : A →* alternatingGroup (Fin 5)
  ψ : VL ≃* W5
  surj : Function.Surjective θ
  ker_eq : θ.ker = K.subgroupOf A
  equiv : ∀ (a : A) (v : VL), ψ (conjAct VL ⟨a, hnorm a.2⟩ v) = pact (θ a : Equiv.Perm (Fin 5)) (ψ v)

@[expose] def IsA5ModuleFor (A K VL : Subgroup G) : Prop := Nonempty (RawData5 A K VL)

structure NatData5 (A K VL V V₁ : Subgroup G) extends RawData5 A K VL where
  line : ∀ v : VL, (v : G) ∈ V₁ ↔ ψ v = 1 ∨ ψ v = W4
  hV : ∀ v : VL, (v : G) ∈ V ↔ ((Multiplicative.toAdd (ψ v) : ↥Ev) : Fin 5 → ZMod 2) 4 = 0

structure AlmostSpecialA5Hyp (V V₁ L T H : Subgroup G) : Prop where
  base : AlmostSpecialHyp V V₁ L T H
  natural : IsA5ModuleFor L (pCoreOf 2 (L ⊔ T)) (conjClosure V₁ L)
  card_V₁ : Nat.card V₁ = 2
  V_eq : V = ⁅conjClosure V₁ L, lOne L V₁⁆
  U_ne : ¬ conjClosure V H ≤ pCoreOf 2 (L ⊔ T)

structure A5Setting (V V₁ L T H : Subgroup G) where
  hyp : AlmostSpecialA5Hyp V V₁ L T H
  D : NatData5 L (pCoreOf 2 (L ⊔ T)) (conjClosure V₁ L) V V₁

structure AlmostSpecialA5Core (V V₁ L T H : Subgroup G) : Prop where
  base : AlmostSpecialCoreBase V V₁ L T H
  g22 : G22Conclusion V V₁ T H
  natural : IsA5ModuleFor L (pCoreOf 2 (L ⊔ T)) (conjClosure V₁ L)
  card_V₁ : Nat.card V₁ = 2
  V_eq : V = ⁅conjClosure V₁ L, lOne L V₁⁆
  U_ne : ¬ conjClosure V H ≤ pCoreOf 2 (L ⊔ T)

structure A5SettingCore (V V₁ L T H : Subgroup G) where
  hyp : AlmostSpecialA5Core V V₁ L T H
  D : NatData5 L (pCoreOf 2 (L ⊔ T)) (conjClosure V₁ L) V V₁

theorem AlmostSpecialA5Hyp.toCore [Finite G] {V V₁ L T H : Subgroup G}
    (h : AlmostSpecialA5Hyp V V₁ L T H) : AlmostSpecialA5Core V V₁ L T H :=
  ⟨h.base.toCoreBase, h.base.g22, h.natural, h.card_V₁, h.V_eq, h.U_ne⟩

@[expose] def A5Setting.toCore [Finite G] {V V₁ L T H : Subgroup G} (S : A5Setting V V₁ L T H) :
    A5SettingCore V V₁ L T H :=
  ⟨S.hyp.toCore, S.D⟩

namespace AlmostSpecialA5Core

variable {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G22_three :
    conjClosure V H ≤ T ∧ T ≤ Subgroup.normalizer (conjClosure V H : Set G) := hyp.g22.three

theorem G22_commutator_mem {x y : G} (hx : x ∈ conjClosure V H) (hy : y ∈ conjClosure V H) :
    x * y * x⁻¹ * y⁻¹ ∈ V₁ :=
  hyp.base.G22_commutator_mem hyp.g22 hx hy

theorem G22_sq_mem {x : G} (hx : x ∈ conjClosure V H) : x ^ 2 ∈ V₁ :=
  hyp.base.G22_sq_mem hyp.g22 hx

end AlmostSpecialA5Core

@[expose] def conjA (τ : Equiv.Perm (Fin 5)) : A5 →* A5 where
  toFun σ := ⟨τ * (σ : Equiv.Perm (Fin 5)) * τ⁻¹, by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h := Equiv.Perm.mem_alternatingGroup.1 σ.2
    simp [h]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := fun σ ρ => by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjA_coe (τ : Equiv.Perm (Fin 5)) (σ : A5) :
    ((conjA τ σ : A5) : Equiv.Perm (Fin 5)) = τ * (σ : Equiv.Perm (Fin 5)) * τ⁻¹ := rfl

theorem conjA_injective (τ : Equiv.Perm (Fin 5)) : Function.Injective (conjA τ) := by
  intro σ ρ h
  apply Subtype.ext
  have := congrArg Subtype.val h
  simpa [conjA_coe] using this

theorem conjA_surjective (τ : Equiv.Perm (Fin 5)) : Function.Surjective (conjA τ) := by
  intro σ
  refine ⟨conjA τ⁻¹ σ, ?_⟩
  apply Subtype.ext
  simp [conjA_coe, mul_assoc]

namespace RawData5

variable {A K VL : Subgroup G} (D : RawData5 A K VL)

@[expose] noncomputable def comm (v : VL) (l : A) : VL := v * conjAct VL ⟨l, D.hnorm l.2⟩ v⁻¹

theorem coe_comm (v : VL) (l : A) : ((D.comm v l : VL) : G) = ⁅(v : G), (l : G)⁆ := by
  unfold comm
  rw [Subgroup.coe_mul, conjAct_coe_apply, commutatorElement_def, Subgroup.coe_inv]
  group

theorem psi_comm (v : VL) (l : A) :
    D.ψ (D.comm v l) = D.ψ v * (pact (D.θ l : Equiv.Perm (Fin 5)) (D.ψ v))⁻¹ := by
  unfold comm
  rw [map_mul, map_inv, map_inv, D.equiv]

theorem coord_psi_comm (v : VL) (l : A) (i : Fin 5)
    (hi : (D.θ l : Equiv.Perm (Fin 5)) i = i) :
    ((Multiplicative.toAdd (D.ψ (D.comm v l)) : ↥Ev) : Fin 5 → ZMod 2) i = 0 := by
  rw [psi_comm, toAdd_mul, toAdd_inv, toAdd_pact]
  have hi' : (D.θ l : Equiv.Perm (Fin 5))⁻¹ i = i := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hi.symm
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply, pw_coe, hi']
  ring

@[expose] def coordSub (i : Fin 5) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ VL,
    ((Multiplicative.toAdd (D.ψ ⟨g, hg⟩) : ↥Ev) : Fin 5 → ZMod 2) i = 0}
  one_mem' := by
    refine ⟨VL.one_mem, ?_⟩
    have : (⟨1, VL.one_mem⟩ : VL) = 1 := rfl
    rw [this, map_one]
    rfl
  mul_mem' := by
    rintro g h ⟨hg, hgi⟩ ⟨hh, hhi⟩
    refine ⟨VL.mul_mem hg hh, ?_⟩
    have : (⟨g * h, VL.mul_mem hg hh⟩ : VL) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
    rw [this, map_mul, toAdd_mul]
    simp [hgi, hhi]
  inv_mem' := by
    rintro g ⟨hg, hgi⟩
    refine ⟨VL.inv_mem hg, ?_⟩
    have : (⟨g⁻¹, VL.inv_mem hg⟩ : VL) = ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_inv, toAdd_inv]
    simp [hgi]

theorem mem_coordSub {i : Fin 5} {g : G} : g ∈ D.coordSub i ↔
    ∃ hg : g ∈ VL, ((Multiplicative.toAdd (D.ψ ⟨g, hg⟩) : ↥Ev) : Fin 5 → ZMod 2) i = 0 := Iff.rfl

theorem pact_fix_of_normalizes {L V₁ : Subgroup G} (D : RawData5 L K VL) (w' : W5) (hw'1 : w' ≠ 1)
    (hline : ∀ v : VL, (v : G) ∈ V₁ ↔ D.ψ v = 1 ∨ D.ψ v = w') (x : L)
    (hx : (x : G) ∈ Subgroup.normalizer (V₁ : Set G)) :
    pact (D.θ x : Equiv.Perm (Fin 5)) w' = w' := by
  obtain ⟨v₁, hv₁⟩ := D.ψ.surjective w'
  have hv₁V₁ : (v₁ : G) ∈ V₁ := (hline v₁).2 (Or.inr hv₁)
  have h1 : (x : G) * v₁ * (x : G)⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 hx _).1 hv₁V₁
  have hxVL : (x : G) * v₁ * (x : G)⁻¹ ∈ VL := by
    have := (Subgroup.mem_normalizer_iff.1 (D.hnorm x.2) (v₁ : G)).1 v₁.2
    exact this
  have h2 := (hline ⟨(x : G) * v₁ * (x : G)⁻¹, hxVL⟩).1 h1
  have h3 : conjAct VL ⟨x, D.hnorm x.2⟩ v₁ = ⟨(x : G) * v₁ * (x : G)⁻¹, hxVL⟩ :=
    Subtype.ext (by rw [conjAct_coe_apply])
  have h4 := D.equiv x v₁
  rw [h3, hv₁] at h4
  rcases h2 with h2 | h2
  · exfalso
    have : D.ψ ⟨(x : G) * v₁ * (x : G)⁻¹, hxVL⟩ = D.ψ 1 := by rw [h2, map_one]
    have h5 := D.ψ.injective this
    have h6 : conjAct VL ⟨x, D.hnorm x.2⟩ v₁ = 1 := by rw [h3]; exact h5
    have h7 : v₁ = 1 := by simpa using h6
    apply hw'1
    rw [← hv₁, h7, map_one]
  · rw [h2] at h4
    exact h4.symm

theorem exists_wA_of_line {L V V₁ : Subgroup G} (D : RawData5 L K VL) (hV₁V : V₁ ≤ V)
    (hV : V = ⁅VL, lOne L V₁⁆) (w' : W5) (hw'1 : w' ≠ 1)
    (hline : ∀ v : VL, (v : G) ∈ V₁ ↔ D.ψ v = 1 ∨ D.ψ v = w') :
    ∃ i : Fin 5, w' = Multiplicative.ofAdd (wA i) := by
  rcases eq_zero_or_e2_or_wA (Multiplicative.toAdd w') with h0 | ⟨a, b, hab, he⟩ | ⟨i, hi⟩
  · exact absurd (Multiplicative.toAdd.injective (by simpa using h0)) hw'1
  · exfalso
    obtain ⟨v₁, hv₁⟩ := D.ψ.surjective w'
    have hv₁V₁ : (v₁ : G) ∈ V₁ := (hline v₁).2 (Or.inr hv₁)
    have hfixw : ∀ (x : L), (x : G) ∈ Subgroup.normalizer (V₁ : Set G) →
        pact (D.θ x : Equiv.Perm (Fin 5)) w' = w' := fun x hx =>
      pact_fix_of_normalizes D w' hw'1 hline x hx
    let M : Subgroup G :=
      { carrier := {g | ∃ hg : g ∈ L, g ∈ Subgroup.normalizer (V₁ : Set G) ∧
          (D.θ ⟨g, hg⟩ : Equiv.Perm (Fin 5)) a = a ∧ (D.θ ⟨g, hg⟩ : Equiv.Perm (Fin 5)) b = b}
        one_mem' := by
          refine ⟨L.one_mem, Subgroup.one_mem _, ?_, ?_⟩ <;>
          · have : (⟨1, L.one_mem⟩ : L) = 1 := rfl
            rw [this, map_one]
            rfl
        mul_mem' := by
          rintro g h ⟨hg, hgN, hga, hgb⟩ ⟨hh, hhN, hha, hhb⟩
          refine ⟨L.mul_mem hg hh, Subgroup.mul_mem _ hgN hhN, ?_, ?_⟩
          · have : (⟨g * h, L.mul_mem hg hh⟩ : L) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
            rw [this, map_mul]
            show (D.θ ⟨g, hg⟩ : Equiv.Perm (Fin 5)) ((D.θ ⟨h, hh⟩ : Equiv.Perm (Fin 5)) a) = a
            rw [hha, hga]
          · have : (⟨g * h, L.mul_mem hg hh⟩ : L) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
            rw [this, map_mul]
            show (D.θ ⟨g, hg⟩ : Equiv.Perm (Fin 5)) ((D.θ ⟨h, hh⟩ : Equiv.Perm (Fin 5)) b) = b
            rw [hhb, hgb]
        inv_mem' := by
          rintro g ⟨hg, hgN, hga, hgb⟩
          refine ⟨L.inv_mem hg, Subgroup.inv_mem _ hgN, ?_, ?_⟩
          · have : (⟨g⁻¹, L.inv_mem hg⟩ : L) = ⟨g, hg⟩⁻¹ := rfl
            rw [this, map_inv]
            show (D.θ ⟨g, hg⟩ : Equiv.Perm (Fin 5))⁻¹ a = a
            rw [Equiv.Perm.inv_eq_iff_eq]
            exact hga.symm
          · have : (⟨g⁻¹, L.inv_mem hg⟩ : L) = ⟨g, hg⟩⁻¹ := rfl
            rw [this, map_inv]
            show (D.θ ⟨g, hg⟩ : Equiv.Perm (Fin 5))⁻¹ b = b
            rw [Equiv.Perm.inv_eq_iff_eq]
            exact hgb.symm }
    have hL₁M : lOne L V₁ ≤ M := by
      refine oTwoUpper_le_of_pow_mem fun x hx => ⟨1, ?_⟩
      have hxσ := hfixw ⟨x, hx.1⟩ hx.2
      have hpw : pw (D.θ ⟨x, hx.1⟩ : Equiv.Perm (Fin 5)) (e2 a b) = e2 a b := by
        have h1 := congrArg Multiplicative.toAdd hxσ
        rw [toAdd_pact, he] at h1
        exact h1
      have hcases := perm_of_pw_e2 _ a b hab hpw
      have hx2 : x ^ 2 ^ 1 ∈ L := L.pow_mem hx.1 _
      refine ⟨hx2, Subgroup.pow_mem _ hx.2 _, ?_, ?_⟩
      · have : (⟨x ^ 2 ^ 1, hx2⟩ : L) = ⟨x, hx.1⟩ ^ 2 := rfl
        rw [this, map_pow]
        show ((D.θ ⟨x, hx.1⟩ : Equiv.Perm (Fin 5)) ^ 2) a = a
        rw [pow_two, Equiv.Perm.mul_apply]
        rcases hcases with ⟨h1, _⟩ | ⟨h1, h2⟩
        · rw [h1, h1]
        · rw [h1, h2]
      · have : (⟨x ^ 2 ^ 1, hx2⟩ : L) = ⟨x, hx.1⟩ ^ 2 := rfl
        rw [this, map_pow]
        show ((D.θ ⟨x, hx.1⟩ : Equiv.Perm (Fin 5)) ^ 2) b = b
        rw [pow_two, Equiv.Perm.mul_apply]
        rcases hcases with ⟨_, h1⟩ | ⟨h1, h2⟩
        · rw [h1, h1]
        · rw [h2, h1]
    have hcommY : ⁅VL, lOne L V₁⁆ ≤ D.coordSub a := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      obtain ⟨hlL, -, hla, -⟩ := hL₁M hl
      have hmem : ((D.comm ⟨v, hv⟩ ⟨l, hlL⟩ : VL) : G) ∈ D.coordSub a :=
        ⟨(D.comm ⟨v, hv⟩ ⟨l, hlL⟩).2, D.coord_psi_comm ⟨v, hv⟩ ⟨l, hlL⟩ a hla⟩
      rwa [coe_comm] at hmem
    have hv₁Y : (v₁ : G) ∈ D.coordSub a := hcommY (hV ▸ hV₁V hv₁V₁)
    obtain ⟨hv₁VL, hya⟩ := hv₁Y
    have hψ : (⟨(v₁ : G), hv₁VL⟩ : VL) = v₁ := rfl
    rw [hψ, hv₁, he] at hya
    have : ((e2 a b : ↥Ev) : Fin 5 → ZMod 2) a = 1 := by
      simp [e2, hab]
    rw [this] at hya
    exact one_ne_zero hya
  · exact ⟨i, by rw [← hi]; rfl⟩

theorem mem_normalizer_of_stab {L V₁ : Subgroup G} (D : RawData5 L K VL) (hV₁VL : V₁ ≤ VL)
    (hline : ∀ v : VL, (v : G) ∈ V₁ ↔ D.ψ v = 1 ∨ D.ψ v = W4) (l : L) (hl : D.θ l ∈ A4s) :
    (l : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
  have key : ∀ (l : L), D.θ l ∈ A4s → ∀ v : G, v ∈ V₁ → (l : G) * v * (l : G)⁻¹ ∈ V₁ := by
    intro l hl v hv
    have hvVL : v ∈ VL := hV₁VL hv
    have hlv : (l : G) * v * (l : G)⁻¹ ∈ VL :=
      (Subgroup.mem_normalizer_iff.1 (D.hnorm l.2) v).1 hvVL
    have h1 := (hline ⟨v, hvVL⟩).1 hv
    have h2 := D.equiv l ⟨v, hvVL⟩
    have h3 : conjAct VL ⟨l, D.hnorm l.2⟩ ⟨v, hvVL⟩ = ⟨(l : G) * v * (l : G)⁻¹, hlv⟩ :=
      Subtype.ext (by rw [conjAct_coe_apply])
    rw [h3] at h2
    refine (hline ⟨(l : G) * v * (l : G)⁻¹, hlv⟩).2 ?_
    rw [h2]
    rcases h1 with h1 | h1
    · left
      rw [h1, map_one]
    · right
      rw [h1]
      exact pact_W4 hl
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key l hl h
  · intro hh
    have hl' : D.θ l⁻¹ ∈ A4s := by
      rw [map_inv]
      exact inv_mem hl
    have := key l⁻¹ hl' _ hh
    simpa [mul_assoc] using this

theorem exists_l1_of_odd [Finite G] {L V₁ : Subgroup G} (D : RawData5 L K VL) (hV₁VL : V₁ ≤ VL)
    (hline : ∀ v : VL, (v : G) ∈ V₁ ↔ D.ψ v = 1 ∨ D.ψ v = W4) (σ : A5) (hσ : σ ∈ A4s)
    (h3 : σ ^ 3 = 1) : ∃ l : L, (l : G) ∈ lOne L V₁ ∧ D.θ l = σ := by
  obtain ⟨l₀, hl₀⟩ := D.surj σ
  have hl₀N := mem_normalizer_of_stab D hV₁VL hline l₀ (hl₀ ▸ hσ)
  let N₀ : Subgroup L := (L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L
  have hσmem : σ ∈ oTwoUpper (N₀.map D.θ) := by
    refine mem_oTwoUpper_of_odd ⟨l₀, Subgroup.mem_subgroupOf.2 ⟨l₀.2, hl₀N⟩, hl₀⟩ ?_
    have : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    exact Odd.of_dvd_nat (by decide) this
  rw [oTwoUpper_map D.θ N₀] at hσmem
  obtain ⟨a₁, ha₁, ha₁σ⟩ := hσmem
  refine ⟨a₁, ?_, ha₁σ⟩
  have h3' := oTwoUpper_map L.subtype N₀
  have h4 : N₀.map L.subtype = L ⊓ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 inf_le_left
  rw [h4] at h3'
  have h5 : (a₁ : G) ∈ (oTwoUpper N₀).map L.subtype := ⟨a₁, ha₁, rfl⟩
  rw [← h3'] at h5
  exact h5

theorem exists_mem_comm_of_e2 [Finite G] {L V₁ : Subgroup G} (D : RawData5 L K VL)
    (hV₁VL : V₁ ≤ VL) (hline : ∀ v : VL, (v : G) ∈ V₁ ↔ D.ψ v = 1 ∨ D.ψ v = W4)
    (a b : Fin 5) (hab : a ≠ b) (ha : a ≠ 4) (hb : b ≠ 4) :
    ∃ v : VL, D.ψ v = Multiplicative.ofAdd (e2 a b) ∧ (v : G) ∈ ⁅VL, lOne L V₁⁆ := by
  obtain ⟨x, σ, hσ, h3, hx⟩ := exists_sub_pw_of_e2 a b hab ha hb
  obtain ⟨l, hl, hθl⟩ := exists_l1_of_odd D hV₁VL hline σ hσ h3
  obtain ⟨u, hu⟩ := D.ψ.surjective (Multiplicative.ofAdd x)
  refine ⟨D.comm u l, ?_, ?_⟩
  · rw [psi_comm, hu, hθl, pact_ofAdd, hx]
    apply Multiplicative.toAdd.injective
    simp [sub_eq_add_neg]
  · rw [coe_comm]
    exact Subgroup.commutator_mem_commutator u.2 hl

theorem mem_V_iff [Finite G] {L V V₁ : Subgroup G} (D : RawData5 L K VL) (hV₁VL : V₁ ≤ VL)
    (hV : V = ⁅VL, lOne L V₁⁆) (hline : ∀ v : VL, (v : G) ∈ V₁ ↔ D.ψ v = 1 ∨ D.ψ v = W4)
    (v : VL) :
    (v : G) ∈ V ↔ ((Multiplicative.toAdd (D.ψ v) : ↥Ev) : Fin 5 → ZMod 2) 4 = 0 := by
  constructor
  · intro hv
    have hcomm : ⁅VL, lOne L V₁⁆ ≤ D.coordSub 4 := by
      rw [Subgroup.commutator_le]
      intro v' hv' l hl
      have hl' : l ∈ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _ hl
      have hfix := pact_fix_of_normalizes D W4 W4_ne_one hline ⟨l, hl'.1⟩ hl'.2
      have hmem : ((D.comm ⟨v', hv'⟩ ⟨l, hl'.1⟩ : VL) : G) ∈ D.coordSub 4 :=
        ⟨(D.comm ⟨v', hv'⟩ ⟨l, hl'.1⟩).2,
          D.coord_psi_comm ⟨v', hv'⟩ ⟨l, hl'.1⟩ 4 (fix_four_of_pact_W4 hfix)⟩
      rwa [coe_comm] at hmem
    obtain ⟨hvVL, h4⟩ := hcomm (hV ▸ hv)
    exact h4
  · intro h4
    rcases eq_of_coord_four_eq_zero _ h4 with h | ⟨a, b, hab, ha, hb, h⟩ | h
    · have : v = 1 := D.ψ.injective (by
        have : D.ψ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
        rw [this, map_one])
      rw [this]
      exact V.one_mem
    · obtain ⟨v', hv', hv'V⟩ := exists_mem_comm_of_e2 D hV₁VL hline a b hab ha hb
      have : v = v' := D.ψ.injective (by
        rw [hv']
        have : D.ψ v = Multiplicative.ofAdd (Multiplicative.toAdd (D.ψ v)) := rfl
        rw [this, h])
      rw [this, hV]
      exact hv'V
    · obtain ⟨v₁, hv₁, hv₁V⟩ := exists_mem_comm_of_e2 D hV₁VL hline 0 1 (by decide) (by decide)
        (by decide)
      obtain ⟨v₂, hv₂, hv₂V⟩ := exists_mem_comm_of_e2 D hV₁VL hline 2 3 (by decide) (by decide)
        (by decide)
      have : v = v₁ * v₂ := D.ψ.injective (by
        rw [map_mul, hv₁, hv₂, ← ofAdd_add]
        have : D.ψ v = Multiplicative.ofAdd (Multiplicative.toAdd (D.ψ v)) := rfl
        rw [this, h])
      rw [this, Subgroup.coe_mul, hV]
      exact Subgroup.mul_mem _ hv₁V hv₂V

end RawData5

theorem IsA5ModuleFor.nonempty_natData5 [Finite G] {L K VL V V₁ : Subgroup G} (h : IsA5ModuleFor L K VL)
    (hV₁V : V₁ ≤ V) (hV₁VL : V₁ ≤ VL) (hcard : Nat.card V₁ = 2) (hV : V = ⁅VL, lOne L V₁⁆) :
    Nonempty (NatData5 L K VL V V₁) := by
  obtain ⟨D₀⟩ := h
  obtain ⟨y, hy1, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : V₁)).1 hcard
  have hV₁elts : ∀ z ∈ V₁, z = 1 ∨ z = (y : G) := by
    intro z hz
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    · right
      have : (⟨z, hz⟩ : V₁) = y := hyuniq ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  set w' : W5 := D₀.ψ ⟨(y : G), hV₁VL y.2⟩ with hw'
  have hw'1 : w' ≠ 1 := by
    intro h
    apply hy1
    have h1 : (⟨(y : G), hV₁VL y.2⟩ : VL) = 1 := D₀.ψ.injective (h.trans (map_one D₀.ψ).symm)
    have h2 : ((⟨(y : G), hV₁VL y.2⟩ : VL) : G) = ((1 : VL) : G) := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hline₀ : ∀ v : VL, (v : G) ∈ V₁ ↔ D₀.ψ v = 1 ∨ D₀.ψ v = w' := by
    intro v
    constructor
    · intro hv
      rcases hV₁elts v hv with h | h
      · left
        have : v = 1 := Subtype.ext h
        rw [this, map_one]
      · right
        have : v = ⟨(y : G), hV₁VL y.2⟩ := Subtype.ext h
        rw [this]
    · rintro (h | h)
      · have : v = 1 := D₀.ψ.injective (h.trans (map_one D₀.ψ).symm)
        rw [this]
        exact V₁.one_mem
      · have : v = ⟨(y : G), hV₁VL y.2⟩ := D₀.ψ.injective h
        rw [this]
        exact y.2
  obtain ⟨i, hi⟩ := D₀.exists_wA_of_line hV₁V hV w' hw'1 hline₀
  let τ : Equiv.Perm (Fin 5) := Equiv.swap i 4
  have hτi : τ i = 4 := Equiv.swap_apply_left i 4
  let D₁ : RawData5 L K VL :=
    { hnorm := D₀.hnorm
      θ := (conjA τ).comp D₀.θ
      ψ := D₀.ψ.trans (pact τ)
      surj := (conjA_surjective τ).comp D₀.surj
      ker_eq := by
        rw [← D₀.ker_eq]
        ext x
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
        constructor
        · intro hx
          exact (conjA_injective τ) (by rw [hx, map_one])
        · intro hx
          rw [hx, map_one]
      equiv := fun a v => by
        show pact τ (D₀.ψ (conjAct VL ⟨a, D₀.hnorm a.2⟩ v)) =
          pact (((conjA τ) (D₀.θ a) : A5) : Equiv.Perm (Fin 5)) (pact τ (D₀.ψ v))
        rw [D₀.equiv, conjA_coe, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
        congr 2
        group }
  have hW4 : W4 = pact τ w' := by
    rw [hi, pact_wA, hτi]
    rfl
  have hline₁ : ∀ v : VL, (v : G) ∈ V₁ ↔ D₁.ψ v = 1 ∨ D₁.ψ v = W4 := by
    intro v
    rw [hline₀ v]
    show _ ↔ pact τ (D₀.ψ v) = 1 ∨ pact τ (D₀.ψ v) = W4
    rw [hW4]
    constructor
    · rintro (h | h)
      · left
        rw [h, map_one]
      · right
        rw [h]
    · rintro (h | h)
      · left
        exact (pact τ).injective (h.trans (map_one (pact τ)).symm)
      · right
        exact (pact τ).injective h
  exact ⟨{ toRawData5 := D₁, line := hline₁, hV := D₁.mem_V_iff hV₁VL hV hline₁ }⟩

theorem AlmostSpecialA5Core.nonempty_setting [Finite G] {V V₁ L T H : Subgroup G}
    (hyp : AlmostSpecialA5Core V V₁ L T H) : Nonempty (A5SettingCore V V₁ L T H) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  exact ⟨⟨hyp, D⟩⟩

namespace RawData5

variable {A K VL : Subgroup G} (D : RawData5 A K VL)

@[expose] noncomputable def alpha : Subgroup.normalizer (VL : Set G) →* MulAut W5 :=
  (MulAut.congr D.ψ).toMonoidHom.comp (conjAct VL)

theorem alpha_psi (x : Subgroup.normalizer (VL : Set G)) (v : VL) :
    D.alpha x (D.ψ v) = D.ψ (conjAct VL x v) := by
  simp [alpha, MulAut.congr_apply]

theorem alpha_of_mem (a : A) :
    D.alpha ⟨a, D.hnorm a.2⟩ = pact (D.θ a : Equiv.Perm (Fin 5)) := by
  ext w
  obtain ⟨v, rfl⟩ := D.ψ.surjective w
  rw [alpha_psi, D.equiv]

theorem alpha_eq_one_iff (x : Subgroup.normalizer (VL : Set G)) :
    D.alpha x = 1 ↔ ∀ v : VL, (x : G) * v * (x : G)⁻¹ = v := by
  constructor
  · intro h v
    have h1 := alpha_psi D x v
    rw [h, MulAut.one_apply] at h1
    have h2 := D.ψ.injective h1
    have h3 := congrArg (fun v : VL => (v : G)) h2
    simpa [conjAct_coe_apply] using h3.symm
  · intro h
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := D.ψ.surjective w
    rw [alpha_psi, MulAut.one_apply]
    have : conjAct VL x v = v := Subtype.ext (by rw [conjAct_coe_apply]; exact h v)
    rw [this]

end RawData5

namespace RawData5

variable {A K VL : Subgroup G} (D : RawData5 A K VL)

include D

theorem isPGroup_VL : IsPGroup 2 VL := by
  refine isPGroup_two_of_forall fun c hc => ⟨1, ?_⟩
  have h : D.ψ ⟨c, hc⟩ ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, two_nsmul]
    exact Ev_add_self _
  have h2 : (⟨c, hc⟩ : VL) ^ 2 = 1 := D.ψ.injective (by rw [map_pow, h, map_one])
  have := congrArg Subtype.val h2
  simpa using this

theorem irreducible_of_normalizes {Y : Subgroup G} (hYV : Y ≤ VL)
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) : Y = ⊥ ∨ Y = VL := by
  let Yw : Subgroup W5 := (Y.subgroupOf VL).map D.ψ.toMonoidHom
  have hinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ x ∈ Yw, pact σ x ∈ Yw := by
    intro σ hσ x hx
    obtain ⟨a, ha⟩ := D.surj ⟨σ, hσ⟩
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨conjAct VL ⟨a, D.hnorm a.2⟩ y, ?_, ?_⟩
    · show (conjAct VL ⟨a, D.hnorm a.2⟩ y : VL) ∈ Y.subgroupOf VL
      rw [Subgroup.mem_subgroupOf, conjAct_coe_apply]
      exact (Subgroup.mem_normalizer_iff.1 (hY a.2) y).1 hy
    · show D.ψ (conjAct VL ⟨a, D.hnorm a.2⟩ y) = pact σ (D.ψ y)
      rw [D.equiv, ha]
  rcases irreducible Yw hinv with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have hyV : y ∈ VL := hYV hy
    have h1 : D.ψ ⟨y, hyV⟩ ∈ Yw := ⟨⟨y, hyV⟩, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨y, hyV⟩ : VL) = 1 :=
      D.ψ.injective (h1.trans (map_one D.ψ).symm)
    have := congrArg Subtype.val h2
    simpa using this
  · right
    apply le_antisymm hYV
    intro v hv
    have h1 : D.ψ ⟨v, hv⟩ ∈ Yw := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyv⟩ := h1
    have h2 : y = ⟨v, hv⟩ := D.ψ.injective hyv
    have h3 : (y : G) ∈ Y := hy
    rwa [h2] at h3

end RawData5

namespace NatData5

variable {A K VL V V₁ : Subgroup G} (D : NatData5 A K VL V V₁)

theorem theta_mem_A4s_of_normalizer (a : A) (ha : (a : G) ∈ Subgroup.normalizer (V₁ : Set G)) :
    D.θ a ∈ A4s :=
  fix_four_of_pact_W4 (RawData5.pact_fix_of_normalizes D.toRawData5 W4 W4_ne_one D.line a ha)

theorem theta_not_mem_A4s (hV₁VL : V₁ ≤ VL) {g : G} (hg : g ∈ A)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) : D.θ ⟨g, hg⟩ ∉ A4s := fun h =>
  hgN (RawData5.mem_normalizer_of_stab D.toRawData5 hV₁VL D.line ⟨g, hg⟩ h)

end NatData5

namespace A5SettingCore

section NoFinite

variable {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

theorem LT_le_normVL : L ⊔ T ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
  sup_le S.D.hnorm (le_normalizer_conjClosure_of_normalizes S.hyp.base.T_le_normV₁
    S.hyp.base.T_le_normL)

theorem isPGroup_VL : IsPGroup 2 (conjClosure V₁ L) := S.D.isPGroup_VL

theorem VL_le_LT : conjClosure V₁ L ≤ L ⊔ T := S.hyp.base.VL_le_LT

theorem VL_ne_bot : conjClosure V₁ L ≠ ⊥ := S.hyp.base.VL_ne_bot

theorem VL_le_O : conjClosure V₁ L ≤ pCoreOf 2 (L ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 S.VL_le_LT S.LT_le_normVL S.isPGroup_VL

end NoFinite

section WithFinite

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

theorem O_le_T : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf S.hyp.base.sylow_LT

omit [Finite G] in
theorem irreducible_L {Y : Subgroup G} (hYV : Y ≤ conjClosure V₁ L)
    (hY : L ≤ Subgroup.normalizer (Y : Set G)) : Y = ⊥ ∨ Y = conjClosure V₁ L :=
  S.D.irreducible_of_normalizes hYV hY

theorem O_centralizes_VL :
    ∀ x ∈ pCoreOf 2 (L ⊔ T), ∀ v ∈ conjClosure V₁ L, x * v * x⁻¹ = v := by
  let Z : Subgroup G := conjClosure V₁ L ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G)
  have hZne : Z ≠ ⊥ := by
    obtain ⟨z, hzV, hz1, hz⟩ := exists_ne_one_mem_centralizer S.hyp.base.isPGroup_T
      (S.VL_le_O.trans S.O_le_T) (fun t ht => (S.LT_le_normVL ((le_sup_right : T ≤ L ⊔ T) ht)))
      S.VL_ne_bot
    intro h
    have : z ∈ Z := ⟨hzV, Subgroup.mem_centralizer_iff.2 fun o ho => hz o (S.O_le_T ho)⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  have hZV : Z ≤ conjClosure V₁ L := inf_le_left
  have hZL : L ≤ Subgroup.normalizer (Z : Set G) := by
    intro l hl
    have h1 : l ∈ Subgroup.normalizer (conjClosure V₁ L : Set G) := S.D.hnorm hl
    have h2 : l ∈ Subgroup.normalizer (Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) : Set G) :=
      normalizer_le_normalizer_centralizer'' _
        (le_normalizer_pCoreOf 2 (L ⊔ T) ((le_sup_left : L ≤ L ⊔ T) hl))
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  rcases S.irreducible_L hZV hZL with h | h
  · exact absurd h hZne
  · intro x hx v hv
    have hvZ : v ∈ Z := by rw [h]; exact hv
    have h1 := Subgroup.mem_centralizer_iff.1 hvZ.2 x hx
    calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [h1]
      _ = v := by group

theorem alpha_eq_one_iff_mem_O {x : G} (hx : x ∈ L ⊔ T) :
    S.D.alpha ⟨x, S.LT_le_normVL hx⟩ = 1 ↔ x ∈ pCoreOf 2 (L ⊔ T) := by
  rw [RawData5.alpha_eq_one_iff]
  constructor
  · intro h
    let C : Subgroup G := (L ⊔ T) ⊓ Subgroup.centralizer (conjClosure V₁ L : Set G)
    have hxC : x ∈ C := by
      refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      have := h ⟨v, hv⟩
      calc v * x = (x * v * x⁻¹) * x := by rw [this]
        _ = x * v := by group
    have hCnorm : L ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
      fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy,
          normalizer_le_normalizer_centralizer'' _ (S.LT_le_normVL hy)⟩
    have hCle : C ≤ L ⊔ T := inf_le_left
    have hLC : ∀ l ∈ L, l ∈ C → l ∈ pCoreOf 2 (L ⊔ T) := by
      intro l hl hlC
      have h1 : S.D.alpha ⟨l, S.LT_le_normVL ((le_sup_left : L ≤ L ⊔ T) hl)⟩ = 1 := by
        rw [RawData5.alpha_eq_one_iff]
        intro v
        have := Subgroup.mem_centralizer_iff.1 hlC.2 v v.2
        calc l * v * l⁻¹ = v * l * l⁻¹ := by rw [← this]
          _ = v := by group
      have h2 := S.D.alpha_of_mem ⟨l, hl⟩
      have h3 : pact (S.D.θ ⟨l, hl⟩ : Equiv.Perm (Fin 5)) = 1 := by rw [← h2]; exact h1
      have h4 : S.D.θ ⟨l, hl⟩ = 1 :=
        Subtype.ext (pact_injective (h3.trans (map_one pact).symm))
      have h5 : (⟨l, hl⟩ : L) ∈ S.D.θ.ker := h4
      rw [S.D.ker_eq] at h5
      exact h5
    have hpg : IsPGroup 2 C := by
      refine isPGroup_two_of_forall fun c hc => ?_
      obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_le_normalizer S.hyp.base.T_le_normL
        S.hyp.base.isPGroup_T (hCle hc)
      have hkC : c ^ 2 ^ k ∈ C := C.pow_mem hc _
      have hkO := hLC _ hk hkC
      obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one_of_mem (pCoreOf_isPGroup 2 (L ⊔ T)) hkO
      exact ⟨j + k, by rw [pow_add, mul_comm, pow_mul, hj]⟩
    exact le_pCoreOf_of_le_normalizer 2 hCle hCnorm hpg hxC
  · intro hxO v
    exact S.O_centralizes_VL x hxO v v.2

end WithFinite

end A5SettingCore

namespace A5Setting

section NoFinite

variable {V V₁ L T H : Subgroup G} (S : A5Setting V V₁ L T H)

include S

theorem LT_le_normVL : L ⊔ T ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
  sup_le S.D.hnorm (le_normalizer_conjClosure_of_normalizes S.hyp.base.T_le_normV₁
    S.hyp.base.T_le_normL)

theorem isPGroup_VL : IsPGroup 2 (conjClosure V₁ L) := S.D.isPGroup_VL

theorem VL_le_LT : conjClosure V₁ L ≤ L ⊔ T := S.hyp.base.toCoreBase.VL_le_LT

theorem VL_ne_bot : conjClosure V₁ L ≠ ⊥ := S.hyp.base.toCoreBase.VL_ne_bot

theorem VL_le_O : conjClosure V₁ L ≤ pCoreOf 2 (L ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 S.VL_le_LT S.LT_le_normVL S.isPGroup_VL

end NoFinite

section WithFinite

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5Setting V V₁ L T H)

include S

theorem O_le_T : pCoreOf 2 (L ⊔ T) ≤ T := S.toCore.O_le_T

omit [Finite G] in
theorem irreducible_L {Y : Subgroup G} (hYV : Y ≤ conjClosure V₁ L)
    (hY : L ≤ Subgroup.normalizer (Y : Set G)) : Y = ⊥ ∨ Y = conjClosure V₁ L :=
  S.D.irreducible_of_normalizes hYV hY

theorem O_centralizes_VL :
    ∀ x ∈ pCoreOf 2 (L ⊔ T), ∀ v ∈ conjClosure V₁ L, x * v * x⁻¹ = v := S.toCore.O_centralizes_VL

theorem alpha_eq_one_iff_mem_O {x : G} (hx : x ∈ L ⊔ T) :
    S.D.alpha ⟨x, S.LT_le_normVL hx⟩ = 1 ↔ x ∈ pCoreOf 2 (L ⊔ T) :=
  S.toCore.alpha_eq_one_iff_mem_O hx

end WithFinite

end A5Setting

namespace RawData5

variable {A K VL : Subgroup G} (D : RawData5 A K VL)

theorem alpha_fix_W4 {V₁ : Subgroup G}
    (hline : ∀ v : VL, (v : G) ∈ V₁ ↔ D.ψ v = 1 ∨ D.ψ v = W4)
    (x : Subgroup.normalizer (VL : Set G)) (hx : (x : G) ∈ Subgroup.normalizer (V₁ : Set G)) :
    D.alpha x W4 = W4 := by
  obtain ⟨v₁, hv₁⟩ := D.ψ.surjective W4
  have hv₁V₁ : (v₁ : G) ∈ V₁ := (hline v₁).2 (Or.inr hv₁)
  have h1 : (x : G) * v₁ * (x : G)⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 hx _).1 hv₁V₁
  have hxVL : (x : G) * v₁ * (x : G)⁻¹ ∈ VL :=
    (Subgroup.mem_normalizer_iff.1 x.2 (v₁ : G)).1 v₁.2
  have h2 := (hline ⟨(x : G) * v₁ * (x : G)⁻¹, hxVL⟩).1 h1
  have h3 : conjAct VL x v₁ = ⟨(x : G) * v₁ * (x : G)⁻¹, hxVL⟩ :=
    Subtype.ext (by rw [conjAct_coe_apply])
  have h4 := alpha_psi D x v₁
  rw [h3, hv₁] at h4
  rcases h2 with h2 | h2
  · exfalso
    have : D.ψ ⟨(x : G) * v₁ * (x : G)⁻¹, hxVL⟩ = D.ψ 1 := by rw [h2, map_one]
    have h5 := D.ψ.injective this
    have h6 : conjAct VL x v₁ = 1 := by rw [h3]; exact h5
    have h7 : v₁ = 1 := by simpa using h6
    apply W4_ne_one
    rw [← hv₁, h7, map_one]
  · rw [h2] at h4
    exact h4

theorem alpha_conj {u : G} (hu : u ∈ Subgroup.normalizer (VL : Set G))
    (huA : u ∈ Subgroup.normalizer (A : Set G)) (a : A) :
    D.alpha ⟨u, hu⟩ * pact (D.θ a : Equiv.Perm (Fin 5)) =
      pact (D.θ ⟨u * a * u⁻¹, (Subgroup.mem_normalizer_iff.1 huA a).1 a.2⟩ :
        Equiv.Perm (Fin 5)) * D.alpha ⟨u, hu⟩ := by
  have huaL : u * a * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 huA a).1 a.2
  have h1 : D.alpha ⟨u, hu⟩ * D.alpha ⟨a, D.hnorm a.2⟩ =
      D.alpha ⟨u * a * u⁻¹, D.hnorm huaL⟩ * D.alpha ⟨u, hu⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp
  rw [D.alpha_of_mem a, D.alpha_of_mem ⟨u * a * u⁻¹, huaL⟩] at h1
  exact h1

end RawData5

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

omit [Finite G] in
theorem U_le_T : conjClosure V H ≤ T := S.hyp.G22_three.1

omit [Finite G] in
theorem U_le_normVL {u : G} (hu : u ∈ conjClosure V H) :
    u ∈ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
  S.LT_le_normVL ((le_sup_right : T ≤ L ⊔ T) (S.U_le_T hu))

omit [Finite G] in
theorem U_le_normL {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (L : Set G) :=
  S.hyp.base.T_le_normL (S.U_le_T hu)

omit [Finite G] in
theorem U_le_normV₁ {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (V₁ : Set G) :=
  S.hyp.base.T_le_normV₁ (S.U_le_T hu)

omit [Finite G] in
theorem alpha_U_eq_pact {u : G} (hu : u ∈ conjClosure V H) :
    ∃ σ : A5, σ ∈ K4 ∧
      S.D.alpha ⟨u, S.U_le_normVL hu⟩ = pact (σ : Equiv.Perm (Fin 5)) := by
  set D := S.D
  set ρ := D.alpha ⟨u, S.U_le_normVL hu⟩ with hρ
  have huN : u ∈ Subgroup.normalizer (L : Set G) := S.U_le_normL hu
  have hu'N : u⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem huN
  have h1 : ∀ σ ∈ alternatingGroup (Fin 5), ∃ τ ∈ alternatingGroup (Fin 5),
      ∀ x, ρ (pact σ x) = pact τ (ρ x) := by
    intro σ hσ
    obtain ⟨a, ha⟩ := D.surj ⟨σ, hσ⟩
    refine ⟨(D.θ ⟨u * a * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN a).1 a.2⟩ : A5), ?_, fun x => ?_⟩
    · exact (D.θ ⟨u * a * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN a).1 a.2⟩).2
    · have := D.alpha_conj (S.U_le_normVL hu) huN a
      rw [ha] at this
      have h := congrArg (fun f : MulAut W5 => f x) this
      simpa using h
  have h2 : ∀ τ ∈ alternatingGroup (Fin 5), ∃ σ ∈ alternatingGroup (Fin 5),
      ∀ x, ρ (pact σ x) = pact τ (ρ x) := by
    intro τ hτ
    obtain ⟨b, hb⟩ := D.surj ⟨τ, hτ⟩
    have hbu : u⁻¹ * b * u⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hu'N b).1 b.2
    refine ⟨(D.θ ⟨u⁻¹ * b * u, by simpa using hbu⟩ : A5), ?_, fun x => ?_⟩
    · exact (D.θ ⟨u⁻¹ * b * u, by simpa using hbu⟩).2
    · have := D.alpha_conj (S.U_le_normVL hu) huN ⟨u⁻¹ * b * u, by simpa using hbu⟩
      have e : (⟨u * (u⁻¹ * b * u) * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN _).1
          (by simpa using hbu : u⁻¹ * b * u ∈ L)⟩ : L) = b := Subtype.ext (by simp [mul_assoc])
      rw [e, hb] at this
      have h := congrArg (fun f : MulAut W5 => f x) this
      simpa using h
  obtain ⟨π, hπ⟩ := exists_pact_of_normalizes ρ h1 h2
  have hfix : ρ W4 = W4 := D.alpha_fix_W4 D.line _ (S.U_le_normV₁ hu)
  have hπ4 : π 4 = 4 := by
    apply fix_four_of_pact_W4
    rw [← hπ]
    exact hfix
  have hcomm : ∀ x : ↥Ev, (x : Fin 5 → ZMod 2) 4 = 0 →
      pw π x - x = 0 ∨ pw π x - x = wA 4 := by
    intro x hx4
    obtain ⟨v, hv⟩ := D.ψ.surjective (Multiplicative.ofAdd x)
    have hvV : (v : G) ∈ V := (D.hV v).2 (by rw [hv]; exact hx4)
    have hvU : (v : G) ∈ conjClosure V H := le_conjClosure V H hvV
    have hc : u * (v : G) * u⁻¹ * (v : G)⁻¹ ∈ V₁ := S.hyp.G22_commutator_mem hu hvU
    have huv : u * (v : G) * u⁻¹ ∈ conjClosure V₁ L :=
      (Subgroup.mem_normalizer_iff.1 (S.U_le_normVL hu) (v : G)).1 v.2
    have hcVL : u * (v : G) * u⁻¹ * (v : G)⁻¹ ∈ conjClosure V₁ L :=
      Subgroup.mul_mem _ huv (inv_mem v.2)
    have h3 := (D.line ⟨_, hcVL⟩).1 hc
    have h4 : (⟨u * (v : G) * u⁻¹ * (v : G)⁻¹, hcVL⟩ : conjClosure V₁ L) =
        ⟨u * (v : G) * u⁻¹, huv⟩ * v⁻¹ := rfl
    have h5 : D.ψ ⟨u * (v : G) * u⁻¹, huv⟩ = Multiplicative.ofAdd (pw π x) := by
      have e : (⟨u * (v : G) * u⁻¹, huv⟩ : conjClosure V₁ L) =
          conjAct (conjClosure V₁ L) ⟨u, S.U_le_normVL hu⟩ v :=
        Subtype.ext (by rw [conjAct_coe_apply])
      rw [e, ← RawData5.alpha_psi, hv, hπ]
      rfl
    rw [h4, map_mul, map_inv, h5, hv] at h3
    rcases h3 with h3 | h3
    · left
      have := congrArg Multiplicative.toAdd h3
      simpa [sub_eq_add_neg] using this
    · right
      have := congrArg Multiplicative.toAdd h3
      simpa [sub_eq_add_neg, W4] using this
  have hmem := perm_mem_K4_of_comm π hπ4 hcomm
  have hsign : π.sign = 1 := sign_klein π hmem
  refine ⟨⟨π, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, hmem, ?_⟩
  refine MulEquiv.ext fun x => ?_
  exact hπ x

end A5SettingCore

namespace A5Setting

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5Setting V V₁ L T H)

include S

theorem U_le_T : conjClosure V H ≤ T := S.toCore.U_le_T

theorem U_le_normVL {u : G} (hu : u ∈ conjClosure V H) :
    u ∈ Subgroup.normalizer (conjClosure V₁ L : Set G) := S.toCore.U_le_normVL hu

theorem U_le_normL {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (L : Set G) :=
  S.toCore.U_le_normL hu

theorem U_le_normV₁ {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (V₁ : Set G) :=
  S.toCore.U_le_normV₁ hu

theorem alpha_U_eq_pact {u : G} (hu : u ∈ conjClosure V H) :
    ∃ σ : A5, σ ∈ K4 ∧
      S.D.alpha ⟨u, S.U_le_normVL hu⟩ = pact (σ : Equiv.Perm (Fin 5)) := S.toCore.alpha_U_eq_pact hu

end A5Setting

namespace RawData5

variable {A K VL : Subgroup G} (D : RawData5 A K VL)

@[expose] noncomputable def actA (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (VL : Set G))
    (hr : ∀ x : X, D.alpha ⟨x, hX x.2⟩ ∈ pactA.range) : X →* A5 :=
  (MonoidHom.ofInjective pactA_injective).symm.toMonoidHom.comp
    ((D.alpha.comp (Subgroup.inclusion hX)).codRestrict _ hr)

theorem pactA_actA (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (VL : Set G))
    (hr : ∀ x : X, D.alpha ⟨x, hX x.2⟩ ∈ pactA.range) (x : X) :
    pactA (D.actA X hX hr x) = D.alpha ⟨x, hX x.2⟩ := by
  have h1 := (MonoidHom.ofInjective pactA_injective).apply_symm_apply
    ⟨D.alpha ⟨x, hX x.2⟩, hr x⟩
  have h2 := congrArg Subtype.val h1
  exact h2

end RawData5

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

omit [Finite G] in
theorem LU_le_normVL :
    L ⊔ conjClosure V H ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
  sup_le S.D.hnorm fun _ hu => S.U_le_normVL hu

omit [Finite G] in
theorem LU_le_LT : L ⊔ conjClosure V H ≤ L ⊔ T := sup_le_sup_left S.U_le_T L

omit [Finite G] in
theorem alpha_mem_range (x : ↥(L ⊔ conjClosure V H)) :
    S.D.alpha ⟨x, S.LU_le_normVL x.2⟩ ∈ pactA.range := by
  let Zs : Subgroup G :=
    (pactA.range.comap S.D.alpha).map (Subgroup.normalizer (conjClosure V₁ L : Set G)).subtype
  have hL : L ≤ Zs := fun l hl =>
    ⟨⟨l, S.D.hnorm hl⟩, Subgroup.mem_comap.2 (by
      rw [S.D.alpha_of_mem ⟨l, hl⟩]
      exact ⟨S.D.θ ⟨l, hl⟩, rfl⟩), rfl⟩
  have hU : conjClosure V H ≤ Zs := fun u hu =>
    ⟨⟨u, S.U_le_normVL hu⟩, Subgroup.mem_comap.2 (by
      obtain ⟨σ, -, hσ⟩ := S.alpha_U_eq_pact hu
      rw [hσ]
      exact ⟨σ, rfl⟩), rfl⟩
  obtain ⟨y, hy, hyx⟩ := (sup_le hL hU) x.2
  have : y = ⟨x, S.LU_le_normVL x.2⟩ := Subtype.ext hyx
  rw [← this]
  exact Subgroup.mem_comap.1 hy

@[expose] noncomputable def Phi : ↥(L ⊔ conjClosure V H) →* A5 :=
  S.D.actA _ S.LU_le_normVL S.alpha_mem_range

omit [Finite G] in
theorem pactA_Phi (x : ↥(L ⊔ conjClosure V H)) :
    pactA (S.Phi x) = S.D.alpha ⟨x, S.LU_le_normVL x.2⟩ :=
  S.D.pactA_actA _ S.LU_le_normVL S.alpha_mem_range x

omit [Finite G] in
theorem Phi_of_L (a : L) :
    S.Phi ⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩ = S.D.θ a := by
  apply pactA_injective
  rw [S.pactA_Phi]
  exact S.D.alpha_of_mem a

theorem Phi_eq_one_iff (x : ↥(L ⊔ conjClosure V H)) :
    S.Phi x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) := by
  have h1 : S.Phi x = 1 ↔ S.D.alpha ⟨x, S.LU_le_normVL x.2⟩ = 1 := by
    rw [← S.pactA_Phi]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      apply pactA_injective
      rw [h, map_one]
  rw [h1]
  exact S.alpha_eq_one_iff_mem_O (S.LU_le_LT x.2)

omit [Finite G] in
theorem Phi_of_U {u : G} (hu : u ∈ conjClosure V H) :
    ∃ σ : A5, σ ∈ K4 ∧
      S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu⟩ = σ := by
  obtain ⟨σ, hσK, hσ⟩ := S.alpha_U_eq_pact hu
  refine ⟨σ, hσK, pactA_injective ?_⟩
  rw [S.pactA_Phi]
  exact hσ

omit [Finite G] in
theorem Phi_surjective : Function.Surjective S.Phi := by
  intro A
  obtain ⟨a, rfl⟩ := S.D.surj A
  exact ⟨⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩, S.Phi_of_L a⟩

omit [Finite G] in
theorem theta_mem_A4s_of_normalizer (a : L) (ha : (a : G) ∈ Subgroup.normalizer (V₁ : Set G)) :
    S.D.θ a ∈ A4s := S.D.theta_mem_A4s_of_normalizer a ha

theorem map_theta_lOne :
    ((lOne L V₁).subgroupOf L).map S.D.θ = A4s := by
  ext σ
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ L ⊓ Subgroup.normalizer (V₁ : Set G) :=
      oTwoUpper_le _ (Subgroup.mem_subgroupOf.1 ha)
    exact S.theta_mem_A4s_of_normalizer a ha'.2
  · intro hσ
    obtain ⟨α, β, hα, hβ, hα3, hβ3, hσαβ⟩ := A4s_prod_three σ hσ
    obtain ⟨l₁, hl₁, hθ₁⟩ := S.D.exists_l1_of_odd (le_conjClosure V₁ L) S.D.line α hα hα3
    obtain ⟨l₂, hl₂, hθ₂⟩ := S.D.exists_l1_of_odd (le_conjClosure V₁ L) S.D.line β hβ hβ3
    refine ⟨l₁ * l₂, Subgroup.mem_subgroupOf.2 ((lOne L V₁).mul_mem hl₁ hl₂), ?_⟩
    rw [map_mul, hθ₁, hθ₂, hσαβ]

omit [Finite G] in
theorem U_le_LT : conjClosure V H ≤ L ⊔ T := (S.U_le_T).trans le_sup_right

omit [Finite G] in
theorem isPGroup_U : IsPGroup 2 (conjClosure V H) := S.hyp.base.isPGroup_T.to_le S.U_le_T

@[expose] noncomputable def betaU : ↥(conjClosure V H) →* A5 :=
  S.Phi.comp (Subgroup.inclusion (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H))

omit [Finite G] in
theorem betaU_apply (u : ↥(conjClosure V H)) :
    S.betaU u = S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩ := rfl

omit [Finite G] in
theorem betaU_mem_K4 (u : ↥(conjClosure V H)) : S.betaU u ∈ K4 := by
  obtain ⟨σ, hσ, h⟩ := S.Phi_of_U u.2
  rw [betaU_apply, h]
  exact hσ

theorem betaU_eq_one_iff (u : ↥(conjClosure V H)) :
    S.betaU u = 1 ↔ (u : G) ∈ pCoreOf 2 (L ⊔ T) :=
  S.Phi_eq_one_iff _

@[expose] noncomputable def Ubar : Subgroup A5 := S.betaU.range

omit [Finite G] in
theorem Ubar_le_K4 : S.Ubar ≤ K4 := by
  rintro _ ⟨u, rfl⟩
  exact S.betaU_mem_K4 u

theorem Ubar_ne_bot : S.Ubar ≠ ⊥ := by
  intro h
  apply S.hyp.U_ne
  intro u hu
  have h1 : S.betaU ⟨u, hu⟩ ∈ S.Ubar := ⟨⟨u, hu⟩, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact (S.betaU_eq_one_iff ⟨u, hu⟩).1 h1

theorem Ubar_conj (x : A5) (hx : x ∈ S.Ubar) : c3A * x * c3A⁻¹ ∈ S.Ubar := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨a, ha1, haθ⟩ := S.D.exists_l1_of_odd (le_conjClosure V₁ L) S.D.line c3A c3A_mem c3A_pow
  have haH : (a : G) ∈ H :=
    S.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) ha1)
  have hU : (a : G) * u * (a : G)⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H haH) u).1 u.2
  refine ⟨⟨(a : G) * u * (a : G)⁻¹, hU⟩, ?_⟩
  have hL : (a : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2
  have hu' : (u : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2
  have h1 : (⟨(a : G) * u * (a : G)⁻¹, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hU⟩ :
      ↥(L ⊔ conjClosure V H)) = ⟨a, hL⟩ * ⟨u, hu'⟩ * ⟨a, hL⟩⁻¹ := Subtype.ext (by simp)
  rw [betaU_apply, betaU_apply, h1, map_mul, map_mul, map_inv]
  have h2 : S.Phi ⟨a, hL⟩ = c3A := by rw [S.Phi_of_L a, haθ]
  rw [h2]

theorem Ubar_eq_K4 : S.Ubar = K4 := by
  rcases K4_irred S.Ubar S.Ubar_le_K4 S.Ubar_conj with h | h
  · exact absurd h S.Ubar_ne_bot
  · exact h

end A5SettingCore

namespace A5Setting

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5Setting V V₁ L T H)

include S

theorem LU_le_normVL :
    L ⊔ conjClosure V H ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) := S.toCore.LU_le_normVL

theorem LU_le_LT : L ⊔ conjClosure V H ≤ L ⊔ T := S.toCore.LU_le_LT

theorem alpha_mem_range (x : ↥(L ⊔ conjClosure V H)) :
    S.D.alpha ⟨x, S.LU_le_normVL x.2⟩ ∈ pactA.range := S.toCore.alpha_mem_range x

@[expose] noncomputable def Phi : ↥(L ⊔ conjClosure V H) →* A5 :=
  S.D.actA _ S.LU_le_normVL S.alpha_mem_range

theorem pactA_Phi (x : ↥(L ⊔ conjClosure V H)) :
    pactA (S.Phi x) = S.D.alpha ⟨x, S.LU_le_normVL x.2⟩ := S.toCore.pactA_Phi x

theorem Phi_of_L (a : L) :
    S.Phi ⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩ = S.D.θ a := S.toCore.Phi_of_L a

theorem Phi_eq_one_iff (x : ↥(L ⊔ conjClosure V H)) :
    S.Phi x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) := S.toCore.Phi_eq_one_iff x

theorem Phi_of_U {u : G} (hu : u ∈ conjClosure V H) :
    ∃ σ : A5, σ ∈ K4 ∧
      S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu⟩ = σ :=
  S.toCore.Phi_of_U hu

theorem Phi_surjective : Function.Surjective S.Phi := S.toCore.Phi_surjective

omit [Finite G] in
theorem theta_mem_A4s_of_normalizer (a : L) (ha : (a : G) ∈ Subgroup.normalizer (V₁ : Set G)) :
    S.D.θ a ∈ A4s := S.D.theta_mem_A4s_of_normalizer a ha

theorem map_theta_lOne :
    ((lOne L V₁).subgroupOf L).map S.D.θ = A4s := S.toCore.map_theta_lOne

theorem U_le_LT : conjClosure V H ≤ L ⊔ T := S.toCore.U_le_LT

theorem isPGroup_U : IsPGroup 2 (conjClosure V H) := S.toCore.isPGroup_U

@[expose] noncomputable def betaU : ↥(conjClosure V H) →* A5 :=
  S.Phi.comp (Subgroup.inclusion (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H))

theorem betaU_apply (u : ↥(conjClosure V H)) :
    S.betaU u = S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩ :=
  S.toCore.betaU_apply u

theorem betaU_mem_K4 (u : ↥(conjClosure V H)) : S.betaU u ∈ K4 := S.toCore.betaU_mem_K4 u

theorem betaU_eq_one_iff (u : ↥(conjClosure V H)) :
    S.betaU u = 1 ↔ (u : G) ∈ pCoreOf 2 (L ⊔ T) := S.toCore.betaU_eq_one_iff u

@[expose] noncomputable def Ubar : Subgroup A5 := S.betaU.range

theorem Ubar_le_K4 : S.Ubar ≤ K4 := S.toCore.Ubar_le_K4

theorem Ubar_ne_bot : S.Ubar ≠ ⊥ := S.toCore.Ubar_ne_bot

theorem Ubar_conj (x : A5) (hx : x ∈ S.Ubar) : c3A * x * c3A⁻¹ ∈ S.Ubar := S.toCore.Ubar_conj x hx

theorem Ubar_eq_K4 : S.Ubar = K4 := S.toCore.Ubar_eq_K4

end A5Setting

theorem isPGroup_le_K4 (X : Subgroup A5) (hX : X ≤ A4s) (hp : IsPGroup 2 X) : X ≤ K4 := by
  intro x hx
  obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  apply mem_K4_of_pow_four x (hX hx)
  have h12 := A4s_pow_twelve x (hX hx)
  refine eq_one_of_pow_three_of_pow_two_pow (x := x ^ 4) (k := k) ?_ ?_
  · rw [← pow_mul]
    exact h12
  · rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]

theorem lOne_le_sup_conjClosure (L V₁ V H : Subgroup G) : lOne L V₁ ≤ L ⊔ conjClosure V H :=
  (oTwoUpper_le _).trans (inf_le_left.trans le_sup_left)

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

theorem star_iso : ∃ e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5,
    ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x :=
  secImg_equiv_of_hom S.LU_le_LT S.Phi S.Phi_surjective S.Phi_eq_one_iff

omit [Finite G] in
theorem Ubar_eq_map : S.Ubar =
    ((conjClosure V H).subgroupOf (L ⊔ conjClosure V H)).map S.Phi := by
  ext A
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩,
      Subgroup.mem_subgroupOf.2 u.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

omit [Finite G] in
theorem star_map_eq {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    {X : Subgroup G} (hX : X ≤ L ⊔ conjClosure V H) :
    ((starImg L T X).subgroupOf (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom =
      (X.subgroupOf (L ⊔ conjClosure V H)).map S.Phi := by
  ext A
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hxX, hxy⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hy)
    have hxLU : (x : G) ∈ L ⊔ conjClosure V H := hX hxX
    have hyx : y = ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT hxLU⟩,
        secMk_mem_secImg hxLU⟩ := Subtype.ext hxy.symm
    refine ⟨⟨x, hxLU⟩, Subgroup.mem_subgroupOf.2 hxX, ?_⟩
    rw [hyx]
    exact (he ⟨x, hxLU⟩).symm
  · rintro ⟨x, hx, rfl⟩
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.1 hx
    refine ⟨⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩,
      Subgroup.mem_subgroupOf.2 (secMk_mem_secImg hxX), ?_⟩
    exact he x

theorem star_map_U {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T (conjClosure V H)).subgroupOf
      (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = K4 := by
  rw [S.star_map_eq he le_sup_right, ← S.Ubar_eq_map, S.Ubar_eq_K4]

theorem Phi_lOne :
    ((lOne L V₁).subgroupOf (L ⊔ conjClosure V H)).map S.Phi = A4s := by
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ L ⊓ Subgroup.normalizer (V₁ : Set G) :=
      oTwoUpper_le _ (Subgroup.mem_subgroupOf.1 hx)
    have hxL : (x : G) ∈ L := hx'.1
    have h1 : S.Phi x = S.D.θ ⟨x, hxL⟩ := S.Phi_of_L ⟨x, hxL⟩
    rw [h1]
    exact S.theta_mem_A4s_of_normalizer ⟨x, hxL⟩ hx'.2
  · intro hσ
    obtain ⟨α, β, hα, hβ, hα3, hβ3, hσαβ⟩ := A4s_prod_three σ hσ
    obtain ⟨l₁, hl₁, hθ₁⟩ := S.D.exists_l1_of_odd (le_conjClosure V₁ L) S.D.line α hα hα3
    obtain ⟨l₂, hl₂, hθ₂⟩ := S.D.exists_l1_of_odd (le_conjClosure V₁ L) S.D.line β hβ hβ3
    have hl₁₂ : (l₁ : G) * l₂ ∈ lOne L V₁ := (lOne L V₁).mul_mem hl₁ hl₂
    refine ⟨⟨(l₁ : G) * l₂, (lOne_le_sup_conjClosure L V₁ V H) hl₁₂⟩, Subgroup.mem_subgroupOf.2 hl₁₂, ?_⟩
    have h1 : (⟨(l₁ : G) * l₂, (lOne_le_sup_conjClosure L V₁ V H) hl₁₂⟩ : ↥(L ⊔ conjClosure V H)) =
        ⟨l₁, (le_sup_left : L ≤ L ⊔ conjClosure V H) l₁.2⟩ *
          ⟨l₂, (le_sup_left : L ≤ L ⊔ conjClosure V H) l₂.2⟩ := rfl
    rw [h1, map_mul, S.Phi_of_L l₁, S.Phi_of_L l₂, hθ₁, hθ₂, hσαβ]

theorem star_map_lOne {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T (lOne L V₁)).subgroupOf
      (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = A4s := by
  rw [S.star_map_eq he (lOne_le_sup_conjClosure L V₁ V H), S.Phi_lOne]

omit [Finite G] in
theorem star_map_L {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T L).subgroupOf (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = ⊤ := by
  rw [S.star_map_eq he le_sup_left, eq_top_iff]
  intro A _
  obtain ⟨a, rfl⟩ := S.D.surj A
  exact ⟨⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩,
    Subgroup.mem_subgroupOf.2 a.2, S.Phi_of_L a⟩

theorem mem_star_U_iff {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    (y : ↥(starImg L T (L ⊔ conjClosure V H))) :
    (y : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈ starImg L T (conjClosure V H) ↔ e y ∈ K4 := by
  rw [← S.star_map_U he]
  constructor
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  · rintro ⟨y', hy', hyy⟩
    have : y' = y := e.injective hyy
    rw [← this]
    exact Subgroup.mem_subgroupOf.1 hy'

theorem mem_star_lOne_iff {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    (y : ↥(starImg L T (L ⊔ conjClosure V H))) :
    (y : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈ starImg L T (lOne L V₁) ↔ e y ∈ A4s := by
  rw [← S.star_map_lOne he]
  constructor
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  · rintro ⟨y', hy', hyy⟩
    have : y' = y := e.injective hyy
    rw [← this]
    exact Subgroup.mem_subgroupOf.1 hy'

theorem star_U_eq : starImg L T (conjClosure V H) =
    pCoreOf 2 (starImg L T (lOne L V₁)) := by
  obtain ⟨e, he⟩ := S.star_iso
  have hUY : starImg L T (conjClosure V H) ≤ starImg L T (L ⊔ conjClosure V H) :=
    secImg_mono le_sup_right
  have hNY : starImg L T (lOne L V₁) ≤ starImg L T (L ⊔ conjClosure V H) :=
    secImg_mono (lOne_le_sup_conjClosure L V₁ V H)
  apply le_antisymm
  ·
    have hUN : starImg L T (conjClosure V H) ≤ starImg L T (lOne L V₁) := by
      intro z hz
      exact (S.mem_star_lOne_iff he ⟨z, hUY hz⟩).2
        (K4_le_A4s ((S.mem_star_U_iff he ⟨z, hUY hz⟩).1 hz))
    have key : ∀ m ∈ starImg L T (lOne L V₁), ∀ z ∈ starImg L T (conjClosure V H),
        m * z * m⁻¹ ∈ starImg L T (conjClosure V H) := by
      intro m hm z hz
      have hmY := hNY hm
      have hzY := hUY hz
      have hw : m * z * m⁻¹ ∈ starImg L T (L ⊔ conjClosure V H) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hmY hzY) (Subgroup.inv_mem _ hmY)
      have h1 : e ⟨m * z * m⁻¹, hw⟩ = e ⟨m, hmY⟩ * e ⟨z, hzY⟩ * (e ⟨m, hmY⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      apply (S.mem_star_U_iff he ⟨m * z * m⁻¹, hw⟩).2
      rw [h1]
      exact K4_norm _ ((S.mem_star_lOne_iff he ⟨m, hmY⟩).1 hm) _
        ((S.mem_star_U_iff he ⟨z, hzY⟩).1 hz)
    have hnorm : starImg L T (lOne L V₁) ≤
        Subgroup.normalizer (starImg L T (conjClosure V H) :
          Set (SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T)))) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨fun hz => key m hm z hz, fun hz => ?_⟩
      have := key m⁻¹ (Subgroup.inv_mem _ hm) _ hz
      simpa [mul_assoc] using this
    exact le_pCoreOf_of_le_normalizer 2 hUN hnorm (isPGroup_secImg S.U_le_LT S.isPGroup_U)
  ·
    set Z := pCoreOf 2 (starImg L T (lOne L V₁)) with hZ
    have hZN : Z ≤ starImg L T (lOne L V₁) := pCoreOf_le 2 _
    have hZY : Z ≤ starImg L T (L ⊔ conjClosure V H) := hZN.trans hNY
    let Z' : Subgroup A5 := (Z.subgroupOf (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom
    have hZ'A : Z' ≤ A4s := by
      rintro _ ⟨z, hz, rfl⟩
      exact (S.mem_star_lOne_iff he z).1 (hZN (Subgroup.mem_subgroupOf.1 hz))
    have hZ'p : IsPGroup 2 Z' :=
      ((pCoreOf_isPGroup 2 _).of_equiv (Subgroup.subgroupOfEquivOfLe hZY).symm).map e.toMonoidHom
    have hle := isPGroup_le_K4 Z' hZ'A hZ'p
    intro z hz
    have hzY : z ∈ starImg L T (L ⊔ conjClosure V H) := hZY hz
    have : e ⟨z, hzY⟩ ∈ Z' := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    exact (S.mem_star_U_iff he ⟨z, hzY⟩).2 (hle this)

theorem star_L_eq : starImg L T L = starImg L T (L ⊔ conjClosure V H) := by
  obtain ⟨e, he⟩ := S.star_iso
  apply le_antisymm (secImg_mono le_sup_left)
  intro z hz
  have h1 := S.star_map_L he
  have h2 : e ⟨z, hz⟩ ∈ ((starImg L T L).subgroupOf (starImg L T (L ⊔ conjClosure V H))).map
      e.toMonoidHom := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyz⟩ := h2
  have hyz' : y = ⟨z, hz⟩ := e.injective hyz
  have h3 : (y : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈ starImg L T L :=
    Subgroup.mem_subgroupOf.1 hy
  rw [hyz'] at h3
  exact h3

theorem star_sylow :
    IsSylowTwoOf (starImg L T (conjClosure V H)) (starImg L T L) := by
  rw [S.star_L_eq]
  obtain ⟨e, he⟩ := S.star_iso
  refine ⟨secImg_mono le_sup_right, isPGroup_secImg S.U_le_LT S.isPGroup_U, ?_⟩
  set P' : Subgroup ↥(starImg L T (L ⊔ conjClosure V H)) :=
    (starImg L T (conjClosure V H)).subgroupOf (starImg L T (L ⊔ conjClosure V H)) with hP'
  have hmap : P'.map e.toMonoidHom = K4 := S.star_map_U he
  have h1 : (P'.map e.toMonoidHom).index = P'.index := Subgroup.index_map_equiv P' e
  rw [hmap] at h1
  change ¬ 2 ∣ P'.index
  rw [← h1]
  exact K4_index_odd

end A5SettingCore

namespace A5Setting

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5Setting V V₁ L T H)

include S

theorem star_iso : ∃ e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5,
    ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x :=
  S.toCore.star_iso

theorem Ubar_eq_map : S.Ubar =
    ((conjClosure V H).subgroupOf (L ⊔ conjClosure V H)).map S.Phi := S.toCore.Ubar_eq_map

theorem star_map_eq {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    {X : Subgroup G} (hX : X ≤ L ⊔ conjClosure V H) :
    ((starImg L T X).subgroupOf (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom =
      (X.subgroupOf (L ⊔ conjClosure V H)).map S.Phi := S.toCore.star_map_eq he hX

theorem star_map_U {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T (conjClosure V H)).subgroupOf
      (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = K4 := S.toCore.star_map_U he

theorem Phi_lOne :
    ((lOne L V₁).subgroupOf (L ⊔ conjClosure V H)).map S.Phi = A4s := S.toCore.Phi_lOne

theorem star_map_lOne {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T (lOne L V₁)).subgroupOf
      (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = A4s := S.toCore.star_map_lOne he

theorem star_map_L {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T L).subgroupOf (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = ⊤ :=
  S.toCore.star_map_L he

theorem mem_star_U_iff {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    (y : ↥(starImg L T (L ⊔ conjClosure V H))) :
    (y : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈ starImg L T (conjClosure V H) ↔ e y ∈ K4 :=
  S.toCore.mem_star_U_iff he y

theorem mem_star_lOne_iff {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* A5}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    (y : ↥(starImg L T (L ⊔ conjClosure V H))) :
    (y : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈ starImg L T (lOne L V₁) ↔ e y ∈ A4s :=
  S.toCore.mem_star_lOne_iff he y

theorem star_U_eq : starImg L T (conjClosure V H) =
    pCoreOf 2 (starImg L T (lOne L V₁)) := S.toCore.star_U_eq

theorem star_L_eq : starImg L T L = starImg L T (L ⊔ conjClosure V H) := S.toCore.star_L_eq

theorem star_sylow :
    IsSylowTwoOf (starImg L T (conjClosure V H)) (starImg L T L) := S.toCore.star_sylow

end A5Setting

namespace AlmostSpecialA5Core

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G24_one :
    starImg L T (conjClosure V H) = pCoreOf 2 (starImg L T (lOne L V₁)) ∧
      IsSylowTwoOf (starImg L T (conjClosure V H)) (starImg L T L) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  let S : A5SettingCore V V₁ L T H := ⟨hyp, D⟩
  exact ⟨S.star_U_eq, S.star_sylow⟩

end AlmostSpecialA5Core

namespace AlmostSpecialA5Hyp

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Hyp V V₁ L T H)

include hyp

theorem G24_one :
    starImg L T (conjClosure V H) = pCoreOf 2 (starImg L T (lOne L V₁)) ∧
      IsSylowTwoOf (starImg L T (conjClosure V H)) (starImg L T L) := hyp.toCore.G24_one

end AlmostSpecialA5Hyp

end CFSG.Quasithin
