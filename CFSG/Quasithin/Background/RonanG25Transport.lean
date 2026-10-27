module

public import CFSG.Quasithin.Background.RonanG25TransportBasic

public section

namespace CFSG.Quasithin.RonanG25

section Transport

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G} {E : Type} [AddCommGroup E]

variable {B : Subgroup G} {φ : ↥B →* Multiplicative E} {act : ↥X → E →+ E}

theorem mem_pre_iff_toAdd {M : AddSubgroup E} (y : ↥B) :
    (y : G) ∈ pre B φ M ↔ Multiplicative.toAdd (φ y) ∈ M := by
  rw [mem_pre]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨y.2, h⟩⟩

theorem commutator_mem_B (hE : Equivariant X B φ act) (x : ↥X) (y : ↥B) :
    (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ B :=
  B.mul_mem (hE.normalizes (x : G) x.2 (y : G) y.2) (B.inv_mem y.2)

theorem toAdd_phi_commutator (hE : Equivariant X B φ act) (x : ↥X) (y w : ↥B)
    (hw : (w : G) = (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) :
    Multiplicative.toAdd (φ w) =
      act x (Multiplicative.toAdd (φ y)) - Multiplicative.toAdd (φ y) := by
  have h1 : φ ⟨(x : G) * (y : G) * (x : G)⁻¹, hE.normalizes (x : G) x.2 (y : G) y.2⟩ =
      Multiplicative.ofAdd (act x (Multiplicative.toAdd (φ y))) :=
    hE.equiv x y ⟨(x : G) * (y : G) * (x : G)⁻¹, hE.normalizes (x : G) x.2 (y : G) y.2⟩ rfl
  have h2 : w = (⟨(x : G) * (y : G) * (x : G)⁻¹, hE.normalizes (x : G) x.2 (y : G) y.2⟩ : ↥B) *
      y⁻¹ :=
    Subtype.ext hw
  rw [h2, map_mul, map_inv, h1, sub_eq_add_neg]
  rfl

theorem ModStep.chiefStep {N : AddSubgroup E}
    (hN : ∀ e, e ∈ N ↔ ∃ y, φ y = Multiplicative.ofAdd e) (hE : Equivariant X B φ act)
    {M₁ M₂ : AddSubgroup E} (hs : ModStep act M₁ M₂) (hM₂ : M₂ ≤ N) :
    ChiefStep X (pre B φ M₁) (pre B φ M₂) := by
  have hM₁N : M₁ ≤ N := hs.lt.le.trans hM₂
  have hlt : pre B φ M₁ < pre B φ M₂ :=
    lt_of_le_of_ne (pre_mono hs.lt.le) fun h => hs.lt.ne (pre_inj hN hM₁N hM₂ h)
  refine ⟨hlt, inv_pre hE hs.inv₁, inv_pre hE hs.inv₂, ?_, ?_⟩
  ·
    intro y hy z hz
    have hyB : y ∈ B := pre_le M₂ hy
    have hzB : z ∈ B := pre_le M₁ hz
    have hyzB : y * z * y⁻¹ ∈ B := B.mul_mem (B.mul_mem hyB hzB) (B.inv_mem hyB)
    obtain ⟨hz', hzM⟩ := mem_pre.mp hz
    rw [mem_pre]
    refine ⟨hyzB, ?_⟩
    have key : φ ⟨y * z * y⁻¹, hyzB⟩ = φ ⟨z, hz'⟩ := by
      have e : (⟨y * z * y⁻¹, hyzB⟩ : ↥B) =
          (⟨y, hyB⟩ : ↥B) * ⟨z, hz'⟩ * ⟨y, hyB⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, mul_comm (φ ⟨y, hyB⟩) (φ ⟨z, hz'⟩),
        mul_inv_cancel_right]
    rw [key]
    exact hzM
  ·
    intro Q hQ1 hQ2 hQinv _
    obtain ⟨M, hM⟩ : ∃ M : AddSubgroup E, ∀ e, e ∈ M ↔
        ∃ w : ↥B, (w : G) ∈ Q ∧ φ w = Multiplicative.ofAdd e :=
      ⟨{ carrier := {e | ∃ w : ↥B, (w : G) ∈ Q ∧ φ w = Multiplicative.ofAdd e}
         add_mem' := by
           rintro _ _ ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
           exact ⟨w₁ * w₂, Q.mul_mem hw₁ hw₂, by rw [map_mul, h₁, h₂, ofAdd_add]⟩
         zero_mem' := ⟨1, Q.one_mem, map_one φ⟩
         neg_mem' := by
           rintro _ ⟨w, hw, h⟩
           exact ⟨w⁻¹, Q.inv_mem hw, by rw [map_inv, h, ofAdd_neg]⟩ }, fun _ => Iff.rfl⟩
    have hM₁M : M₁ ≤ M := by
      intro e he
      obtain ⟨w, hw⟩ := (hN e).mp (hM₁N he)
      have hwpre : (w : G) ∈ pre B φ M₁ :=
        (mem_pre_iff_toAdd w).mpr (by rw [hw, toAdd_ofAdd]; exact he)
      exact (hM e).mpr ⟨w, hQ1 hwpre, hw⟩
    have hMM₂ : M ≤ M₂ := by
      intro e he
      obtain ⟨w, hwQ, hw⟩ := (hM e).mp he
      have h := (mem_pre_iff_toAdd w).mp (hQ2 hwQ)
      rw [hw, toAdd_ofAdd] at h
      exact h
    have hMinv : AInv act M := by
      intro x e he
      obtain ⟨w, hwQ, hw⟩ := (hM e).mp he
      have hxwB : (x : G) * (w : G) * (x : G)⁻¹ ∈ B := hE.normalizes (x : G) x.2 (w : G) w.2
      have hxwQ : (x : G) * (w : G) * (x : G)⁻¹ ∈ Q := hQinv (x : G) x.2 (w : G) hwQ
      have hφ : φ ⟨(x : G) * (w : G) * (x : G)⁻¹, hxwB⟩ = Multiplicative.ofAdd (act x e) := by
        rw [hE.equiv x w ⟨(x : G) * (w : G) * (x : G)⁻¹, hxwB⟩ rfl, hw, toAdd_ofAdd]
      exact (hM _).mpr ⟨⟨_, hxwB⟩, hxwQ, hφ⟩
    have hMeq : M = M₁ ∨ M = M₂ := hs.simple M hM₁M hMM₂ hMinv
    have hQeq : Q = pre B φ M := by
      apply le_antisymm
      · intro q hq
        have hqB : q ∈ B := pre_le M₂ (hQ2 hq)
        rw [mem_pre]
        exact ⟨hqB, (hM _).mpr ⟨⟨q, hqB⟩, hq, (ofAdd_toAdd _).symm⟩⟩
      · intro y hy
        obtain ⟨hyB, hyM⟩ := mem_pre.mp hy
        obtain ⟨w, hwQ, hw⟩ := (hM _).mp hyM
        have hv : φ ((⟨y, hyB⟩ : ↥B) * w⁻¹) = 1 := by
          rw [map_mul, map_inv, hw, ofAdd_toAdd, mul_inv_cancel]
        have hvM₁ : (((⟨y, hyB⟩ : ↥B) * w⁻¹ : ↥B) : G) ∈ pre B φ M₁ := by
          rw [mem_pre_iff_toAdd, hv, toAdd_one]
          exact M₁.zero_mem
        have hy_eq : y = (((⟨y, hyB⟩ : ↥B) * w⁻¹ : ↥B) : G) * (w : G) := by
          simp
        rw [hy_eq]
        exact Q.mul_mem (hQ1 hvM₁) hwQ
    rcases hMeq with h | h
    · left
      rw [hQeq, h]
    · right
      rw [hQeq, h]

theorem ModNatural.factorNatural {N : AddSubgroup E}
    (hN : ∀ e, e ∈ N ↔ ∃ y, φ y = Multiplicative.ofAdd e) (hE : Equivariant X B φ act)
    {M₁ M₂ : AddSubgroup E} (hs : ModStep act M₁ M₂) (hn : ModNatural F act M₁ M₂)
    (hM₂ : M₂ ≤ N) : FactorNatural F X (pre B φ M₁) (pre B φ M₂) := by
  obtain ⟨c, β, hsurj, hker, hequiv, h4, h5⟩ := hn
  let φ' : ↥(pre B φ M₂) →* Multiplicative (Fin 2 → F) :=
    (AddMonoidHom.toMultiplicative c).comp (φ.comp (Subgroup.inclusion (pre_le M₂)))
  have hval : ∀ y : ↥(pre B φ M₂),
      φ' y = Multiplicative.ofAdd
        (c (Multiplicative.toAdd (φ (Subgroup.inclusion (pre_le M₂) y)))) :=
    fun y => rfl
  have hmemy : ∀ y : ↥(pre B φ M₂),
      Multiplicative.toAdd (φ (Subgroup.inclusion (pre_le M₂) y)) ∈ M₂ := fun y =>
    (mem_pre_iff_toAdd (Subgroup.inclusion (pre_le M₂) y)).mp y.2
  refine ⟨φ', β, ?_, ?_, ?_, h4, h5⟩
  ·
    intro w
    obtain ⟨e, he, hce⟩ := hsurj (Multiplicative.toAdd w)
    obtain ⟨y, hy⟩ := (hN e).mp (hM₂ he)
    have hypre : (y : G) ∈ pre B φ M₂ :=
      (mem_pre_iff_toAdd y).mpr (by rw [hy, toAdd_ofAdd]; exact he)
    refine ⟨⟨y, hypre⟩, ?_⟩
    show Multiplicative.ofAdd (c (Multiplicative.toAdd (φ y))) = w
    rw [hy, toAdd_ofAdd, hce, ofAdd_toAdd]
  ·
    intro y
    have h1 : φ' y = 1 ↔
        c (Multiplicative.toAdd (φ (Subgroup.inclusion (pre_le M₂) y))) = 0 := by
      rw [hval]
      exact ofAdd_eq_one
    rw [h1, hker _ (hmemy y)]
    exact (mem_pre_iff_toAdd (Subgroup.inclusion (pre_le M₂) y)).symm
  ·
    intro x y y' hyy'
    have hyy'' : (x : G) * ((Subgroup.inclusion (pre_le M₂) y : ↥B) : G) * (x : G)⁻¹ =
        ((Subgroup.inclusion (pre_le M₂) y' : ↥B) : G) := hyy'
    have hφ' : Multiplicative.toAdd (φ (Subgroup.inclusion (pre_le M₂) y')) =
        act x (Multiplicative.toAdd (φ (Subgroup.inclusion (pre_le M₂) y))) := by
      rw [hE.equiv x _ _ hyy'', toAdd_ofAdd]
    show c (Multiplicative.toAdd (φ (Subgroup.inclusion (pre_le M₂) y'))) =
      ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (c (Multiplicative.toAdd (φ (Subgroup.inclusion (pre_le M₂) y))))
    rw [hφ']
    exact hequiv x _ (hmemy y)

theorem ModAdditional.factor [Finite G] {N : AddSubgroup E}
    (hN : ∀ e, e ∈ N ↔ ∃ y, φ y = Multiplicative.ofAdd e) (hE : Equivariant X B φ act)
    {M₁ M₂ : AddSubgroup E} (hn : ModAdditional F act M₁ M₂) (hM₁₂ : M₁ ≤ M₂) (hM₂ : M₂ ≤ N) :
    (∀ y ∈ pre B φ M₂, ∀ z ∈ pre B φ M₂, y * z * y⁻¹ * z⁻¹ ∈ pre B φ M₁) ∧
      ¬ FactorCentral X (pre B φ M₁) (pre B φ M₂) ∧
      Nat.card (pre B φ M₂) = Nat.card F * Nat.card (pre B φ M₁) := by
  obtain ⟨hcard, hnc⟩ := hn
  refine ⟨?_, ?_, ?_⟩
  ·
    intro y hy z hz
    have hyB : y ∈ B := pre_le M₂ hy
    have hzB : z ∈ B := pre_le M₂ hz
    have hcB : y * z * y⁻¹ * z⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (B.mul_mem hyB hzB) (B.inv_mem hyB)) (B.inv_mem hzB)
    rw [mem_pre]
    refine ⟨hcB, ?_⟩
    have hφc : φ ⟨y * z * y⁻¹ * z⁻¹, hcB⟩ = 1 := by
      have e' : (⟨y * z * y⁻¹ * z⁻¹, hcB⟩ : ↥B) =
          (⟨y, hyB⟩ : ↥B) * ⟨z, hzB⟩ * ⟨y, hyB⟩⁻¹ * ⟨z, hzB⟩⁻¹ := rfl
      rw [e', map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_comm (φ ⟨y, hyB⟩) (φ ⟨z, hzB⟩), mul_inv_cancel_right, mul_inv_cancel]
    rw [hφc, toAdd_one]
    exact M₁.zero_mem
  ·
    intro hc
    obtain ⟨x, e, he, hxe⟩ := hnc
    obtain ⟨y0, hy0⟩ := (hN e).mp (hM₂ he)
    have hy0pre : (y0 : G) ∈ pre B φ M₂ :=
      (mem_pre_iff_toAdd y0).mpr (by rw [hy0, toAdd_ofAdd]; exact he)
    obtain ⟨hwB, hwM⟩ := mem_pre.mp (hc (x : G) x.2 (y0 : G) hy0pre)
    have h3 := toAdd_phi_commutator hE x y0 ⟨_, hwB⟩ rfl
    rw [hy0, toAdd_ofAdd] at h3
    rw [h3] at hwM
    exact hxe hwM
  ·
    rw [card_pre hN hM₂, card_pre hN (hM₁₂.trans hM₂), hcard]
    ring

theorem ModCentral.factor [Finite G] {N : AddSubgroup E}
    (hN : ∀ e, e ∈ N ↔ ∃ y, φ y = Multiplicative.ofAdd e) (hE : Equivariant X B φ act)
    {M₁ M₂ : AddSubgroup E} (hn : ModCentral act M₁ M₂) (hM₁₂ : M₁ ≤ M₂) (hM₂ : M₂ ≤ N) :
    FactorCentral X (pre B φ M₁) (pre B φ M₂) ∧
      ∃ p : ℕ, p.Prime ∧ Nat.card (pre B φ M₂) = p * Nat.card (pre B φ M₁) := by
  obtain ⟨hact, p, hp, hcard⟩ := hn
  refine ⟨?_, p, hp, ?_⟩
  · intro x hx y hy
    have hyB : y ∈ B := pre_le M₂ hy
    have he : Multiplicative.toAdd (φ ⟨y, hyB⟩) ∈ M₂ := (mem_pre_iff_toAdd ⟨y, hyB⟩).mp hy
    have hw : x * y * x⁻¹ * y⁻¹ ∈ B := commutator_mem_B hE ⟨x, hx⟩ ⟨y, hyB⟩
    rw [mem_pre]
    refine ⟨hw, ?_⟩
    have h3 := toAdd_phi_commutator hE ⟨x, hx⟩ ⟨y, hyB⟩ ⟨x * y * x⁻¹ * y⁻¹, hw⟩ rfl
    rw [h3]
    exact hact ⟨x, hx⟩ _ he
  · rw [card_pre hN hM₂, card_pre hN (hM₁₂.trans hM₂), hcard]
    ring

theorem ModChain.transport [Finite G] {ord : Bool} {N : AddSubgroup E}
    (hN : ∀ e, e ∈ N ↔ ∃ y, φ y = Multiplicative.ofAdd e) (hE : Equivariant X B φ act)
    {M₁ M₂ : AddSubgroup E} {a b : ℕ} (h : ModChain F act M₁ M₂ a b) (hM₂ : M₂ ≤ N) :
    ChainCounts F X ord (pre B φ M₁) (pre B φ M₂) a b := by
  revert hM₂
  induction h with
  | refl M hM =>
    intro _
    exact ChainCounts.refl _ (inv_pre hE hM)
  | @natural M₁' M₂' M₃' a' b' hs hn rest ih =>
    intro hM₃
    have hM₂N : M₂' ≤ N := (ModChain.le rest).trans hM₃
    exact ChainCounts.natural (ModStep.chiefStep hN hE hs hM₂N)
      (ModNatural.factorNatural hN hE hs hn hM₂N) (ih hM₃)
  | @additional M₁' M₂' M₃' a' b' hs hn rest ih =>
    intro hM₃
    have hM₂N : M₂' ≤ N := (ModChain.le rest).trans hM₃
    obtain ⟨h1, h2, h3⟩ := ModAdditional.factor hN hE hn hs.lt.le hM₂N
    exact ChainCounts.additional (ModStep.chiefStep hN hE hs hM₂N) h1 h2 h3 (ih hM₃)
  | @central M₁' M₂' M₃' a' b' hs hn rest ih =>
    intro hM₃
    have hM₂N : M₂' ≤ N := (ModChain.le rest).trans hM₃
    obtain ⟨h1, p', hp', h2⟩ := ModCentral.factor hN hE hn hs.lt.le hM₂N
    exact ChainCounts.central (ModStep.chiefStep hN hE hs hM₂N) h1 hp' h2 (ih hM₃)

end Transport

end CFSG.Quasithin.RonanG25
