module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xc
import CFSG.Quasithin.SteinbergCFOneFactorFixedKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem rep_inv_apply_apply (ρ : Representation (ZMod 2) G V) (g : G) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rep_apply_inv_apply (ρ : Representation (ZMod 2) G V) (g : G) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rep_injective (ρ : Representation (ZMod 2) G V) (g : G) : Function.Injective (ρ g) :=
  fun v w h => by rw [← rep_inv_apply_apply ρ g v, h, rep_inv_apply_apply]

theorem isInvariant_sup {H₁ H₂ : Subgroup G} {W : Submodule (ZMod 2) V} (h₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ W)
    (h₂ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₂ W) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (H₁ ⊔ H₂) W := by
  have key : ∀ g ∈ H₁ ⊔ H₂, (∀ w ∈ W, ρ g w ∈ W) ∧ ∀ w ∈ W, ρ g⁻¹ w ∈ W := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨h₁ x hx, h₁ x⁻¹ (inv_mem hx)⟩
      · exact ⟨h₂ x hx, h₂ x⁻¹ (inv_mem hx)⟩
    | one => exact ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rw [map_mul, Module.End.mul_apply]
        exact hx.1 _ (hy.1 w hw)
      · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
        exact hy.2 _ (hx.2 w hw)
    | inv x _ hx => exact ⟨hx.2, by simpa using hx.1⟩
  exact fun g hg => (key g hg).1

theorem isInvariant_map {H : Subgroup G} {W : Submodule (ZMod 2) V} (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H W) {g : G}
    (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H (W.map (ρ g)) := by
  rintro h hh _ ⟨w, hw, rfl⟩
  refine ⟨ρ (g⁻¹ * h * g) w, hW _ (hg h hh) w hw, ?_⟩
  change ρ g (ρ (g⁻¹ * h * g) w) = ρ h (ρ g w)
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, rep_apply_inv_apply]

theorem modFix_mono_left {Z Z' : Submodule (ZMod 2) V} (h : Z ≤ Z') (D : Subgroup G) :
    P22x.modFix ρ Z D ≤ P22x.modFix ρ Z' D :=
  fun _ hv a ha => h (hv a ha)

theorem modFix_anti {D D' : Subgroup G} (h : D ≤ D') (Z : Submodule (ZMod 2) V) :
    P22x.modFix ρ Z D' ≤ P22x.modFix ρ Z D :=
  fun _ hv a ha => hv a (h ha)

theorem le_modFix {D : Subgroup G} {Z : Submodule (ZMod 2) V} (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ D Z) :
    Z ≤ P22x.modFix ρ Z D :=
  fun v hv a ha => Z.sub_mem (hZ a ha v hv) hv

theorem modFix_bot (D : Subgroup G) : P22x.modFix ρ ⊥ D = fixSub ρ D := by
  ext v
  simp only [P22x.mem_modFix, Submodule.mem_bot, sub_eq_zero, mem_fixSub]

theorem fixSub_le_modFix (D : Subgroup G) (Z : Submodule (ZMod 2) V) : fixSub ρ D ≤ P22x.modFix ρ Z D := by
  rw [← modFix_bot]
  exact modFix_mono_left bot_le D

@[expose] def vecStab (ρ : Representation (ZMod 2) G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' {a b} ha hb := by
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, show ρ b v = v from hb, show ρ a v = v from ha]
  one_mem' := by
    change ρ 1 v = v
    rw [map_one, Module.End.one_apply]
  inv_mem' {a} ha := by
    change ρ a⁻¹ v = v
    conv_lhs => rw [← show ρ a v = v from ha]
    exact rep_inv_apply_apply ρ a v

theorem mem_fixSub_zpowers {s : G} {v : V} : v ∈ fixSub ρ (Subgroup.zpowers s) ↔ ρ s v = v := by
  refine ⟨fun h => h s (Subgroup.mem_zpowers s), fun h a ha => ?_⟩
  have hle : Subgroup.zpowers s ≤ vecStab ρ v := (Subgroup.zpowers_le).2 h
  exact hle ha

theorem mem_modFix_zpowers {s : G} {Z : Submodule (ZMod 2) V} (hZ : ∀ z ∈ Z, ρ s z ∈ Z)
    (hZ' : ∀ z ∈ Z, ρ s⁻¹ z ∈ Z) {v : V} :
    v ∈ P22x.modFix ρ Z (Subgroup.zpowers s) ↔ ρ s v - v ∈ Z := by
  refine ⟨fun h => h s (Subgroup.mem_zpowers s), fun h a ha => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hinv : ρ s⁻¹ v - v ∈ Z := by
    have : ρ s⁻¹ v - v = -ρ s⁻¹ (ρ s v - v) := by
      rw [map_sub, rep_inv_apply_apply]
      abel
    rw [this]
    exact Z.neg_mem (hZ' _ h)
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : ρ (s ^ ((i : ℤ) + 1)) v - v = ρ s (ρ (s ^ (i : ℤ)) v - v) + (ρ s v - v) := by
      rw [add_comm, zpow_add, zpow_one, map_mul, Module.End.mul_apply, map_sub]
      abel
    rw [this]
    exact Z.add_mem (hZ _ (ih (Subgroup.zpow_mem_zpowers s _))) h
  | pred i ih =>
    have : ρ (s ^ (-(i : ℤ) - 1)) v - v = ρ s⁻¹ (ρ (s ^ (-(i : ℤ))) v - v) + (ρ s⁻¹ v - v) := by
      rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by ring, zpow_add, zpow_neg_one, map_mul,
        Module.End.mul_apply, map_sub]
      abel
    rw [this]
    exact Z.add_mem (hZ' _ (ih (Subgroup.zpow_mem_zpowers s _))) hinv

theorem nsmul_two_eq_zero (w : V) : (2 : ℕ) • w = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul]

theorem modFix_zpowers_le_fixSub {s : G} (hs : Odd (orderOf s)) {X : Submodule (ZMod 2) V}
    (hX : ∀ x ∈ X, ρ s x = x) : P22x.modFix ρ X (Subgroup.zpowers s) ≤ fixSub ρ (Subgroup.zpowers s) := by
  intro v hv
  rw [mem_fixSub_zpowers]
  set x := ρ s v - v with hx
  have hxX : x ∈ X := hv s (Subgroup.mem_zpowers s)
  have hpow : ∀ k : ℕ, ρ (s ^ k) v = v + k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih, map_add, map_nsmul, hX x hxX, succ_nsmul]
      rw [hx]
      abel
  have h1 := hpow (orderOf s)
  rw [pow_orderOf_eq_one, map_one, Module.End.one_apply, left_eq_add] at h1
  obtain ⟨j, hj⟩ := hs
  rw [hj, add_nsmul, one_nsmul, mul_nsmul', nsmul_two_eq_zero, zero_add] at h1
  rw [← sub_eq_zero]
  exact h1

theorem finrank_inf_fixSub_conj [Finite V] {U : Submodule (ZMod 2) V} {g : G}
    (hU : ∀ u ∈ U, ρ g u ∈ U) (hU' : ∀ u ∈ U, ρ g⁻¹ u ∈ U) (s : G) :
    finrank (ZMod 2) ↥(U ⊓ fixSub ρ (Subgroup.zpowers (g * s * g⁻¹))) =
      finrank (ZMod 2) ↥(U ⊓ fixSub ρ (Subgroup.zpowers s)) := by
  have key : ∀ (x t : G), (∀ u ∈ U, ρ x u ∈ U) →
      (U ⊓ fixSub ρ (Subgroup.zpowers t)).map (ρ x) ≤ U ⊓ fixSub ρ (Subgroup.zpowers (x * t * x⁻¹)) := by
    rintro x t hx _ ⟨v, ⟨hvU, hvt⟩, rfl⟩
    refine ⟨hx v hvU, mem_fixSub_zpowers.2 ?_⟩
    replace hvt : ρ t v = v := mem_fixSub_zpowers.1 hvt
    change ρ (x * t * x⁻¹) (ρ x v) = ρ x v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, rep_inv_apply_apply, hvt]
  have h1 := Submodule.finrank_mono (key g s hU)
  have h2 := Submodule.finrank_mono (key g⁻¹ (g * s * g⁻¹) hU')
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rep_injective ρ g) _).symm] at h1
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rep_injective ρ g⁻¹) _).symm] at h2
  have h3 : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
  rw [h3] at h2
  omega

@[expose] noncomputable def secCost (ρ : Representation (ZMod 2) G V) (D : Subgroup G)
    (Y Z : Submodule (ZMod 2) V) : ℕ :=
  finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z D)

theorem secCost_superadd [Finite V] {D : Subgroup G} {Y M Z : Submodule (ZMod 2) V} (hZM : Z ≤ M)
    (hMY : M ≤ Y) (hM : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ D M) : secCost ρ D Y M + secCost ρ D M Z ≤ secCost ρ D Y Z := by
  set F := Y ⊓ P22x.modFix ρ Z D with hF
  have h1 : F ⊓ M = M ⊓ P22x.modFix ρ Z D := by
    rw [hF, inf_right_comm, inf_eq_right.2 hMY, inf_comm]
  have h2 : F ⊔ M ≤ Y ⊓ P22x.modFix ρ M D :=
    sup_le (inf_le_inf_left Y (modFix_mono_left hZM D)) (le_inf hMY (le_modFix hM))
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq F M
  have h4 := Submodule.finrank_mono h2
  have h5 := Submodule.finrank_mono (inf_le_left : Y ⊓ P22x.modFix ρ M D ≤ Y)
  have h6 := Submodule.finrank_mono (inf_le_left : F ⊓ M ≤ F)
  have h7 := Submodule.finrank_mono (inf_le_right : F ⊓ M ≤ M)
  have h8 := Submodule.finrank_mono (inf_le_left : F ≤ Y)
  rw [h1] at h3 h6 h7
  unfold secCost
  rw [← hF]
  omega

theorem secCost_mono [Finite V] {D D' : Subgroup G} (h : D ≤ D') (Y Z : Submodule (ZMod 2) V) :
    secCost ρ D Y Z ≤ secCost ρ D' Y Z := by
  unfold secCost
  have := Submodule.finrank_mono (inf_le_inf_left Y (modFix_anti (ρ := ρ) h Z))
  omega

theorem secCost_bot (D : Subgroup G) (Y : Submodule (ZMod 2) V) :
    secCost ρ D Y ⊥ = finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥(Y ⊓ fixSub ρ D) := by
  rw [secCost, modFix_bot]

theorem secCost_eq_of_isCompl [Finite V] {D : Subgroup G} {Y Y₁ W Z : Submodule (ZMod 2) V}
    (hsup : W ⊔ Y₁ = Y) (hinf : W ⊓ Y₁ = Z) (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ D W) (hY₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ D Y₁) :
    secCost ρ D Y Y₁ = secCost ρ D W Z := by
  have hZY₁ : Z ≤ Y₁ := hinf ▸ inf_le_right
  have e1 : W ⊓ P22x.modFix ρ Z D = W ⊓ P22x.modFix ρ Y₁ D := by
    refine le_antisymm (inf_le_inf_left W (modFix_mono_left hZY₁ D)) fun w hw' => ?_
    obtain ⟨hw, hwf⟩ := Submodule.mem_inf.1 hw'
    refine Submodule.mem_inf.2 ⟨hw, fun a ha => ?_⟩
    rw [← hinf]
    exact ⟨W.sub_mem (hW a ha w hw) hw, hwf a ha⟩
  have e2 : Y ⊓ P22x.modFix ρ Y₁ D = (W ⊓ P22x.modFix ρ Y₁ D) ⊔ Y₁ := by
    refine le_antisymm (fun y hy' => ?_) (sup_le (inf_le_inf_right _ (hsup ▸ le_sup_left))
      (le_inf (hsup ▸ le_sup_right) (le_modFix hY₁)))
    obtain ⟨hy, hyf⟩ := Submodule.mem_inf.1 hy'
    rw [← hsup] at hy
    obtain ⟨w, hw, y₁, hy₁, rfl⟩ := Submodule.mem_sup.1 hy
    refine Submodule.add_mem_sup ⟨hw, fun a ha => ?_⟩ hy₁
    have h1 := hyf a ha
    have h2 : ρ a (w + y₁) - (w + y₁) - (ρ a y₁ - y₁) = ρ a w - w := by
      rw [map_add]
      abel
    rw [← h2]
    exact Y₁.sub_mem h1 (Y₁.sub_mem (hY₁ a ha y₁ hy₁) hy₁)
  have e3 : (W ⊓ P22x.modFix ρ Y₁ D) ⊓ Y₁ = Z := by
    rw [inf_right_comm, hinf]
    exact inf_eq_left.2 (hZY₁.trans (le_modFix hY₁))
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Y₁
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ P22x.modFix ρ Y₁ D) Y₁
  rw [hsup, hinf] at h1
  rw [← e2, e3] at h2
  have h3 := Submodule.finrank_mono (inf_le_left : W ⊓ P22x.modFix ρ Y₁ D ≤ W)
  unfold secCost
  rw [e1]
  omega

theorem secCost_map [Finite V] {D : Subgroup G} {g : G} (hg : ∀ a ∈ D, g * a = a * g)
    (Y Z : Submodule (ZMod 2) V) : secCost ρ D (Y.map (ρ g)) (Z.map (ρ g)) = secCost ρ D Y Z := by
  have hinj := rep_injective ρ g
  have e : Y.map (ρ g) ⊓ P22x.modFix ρ (Z.map (ρ g)) D = (Y ⊓ P22x.modFix ρ Z D).map (ρ g) := by
    ext v
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyf⟩
      refine ⟨y, ⟨hy, fun a ha => ?_⟩, rfl⟩
      obtain ⟨z, hz, hze⟩ := hyf a ha
      have : ρ g (ρ a y - y) = ρ a (ρ g y) - ρ g y := by
        rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg a ha]
      rw [← this] at hze
      rw [← hinj hze]
      exact hz
    · rintro ⟨y, ⟨hy, hyf⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, fun a ha => ⟨ρ a y - y, hyf a ha, ?_⟩⟩
      change ρ g (ρ a y - y) = ρ a (ρ g y) - ρ g y
      rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg a ha]
  unfold secCost
  rw [e, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)]

@[expose] def secKer (ρ : Representation (ZMod 2) G V) (Y Z : Submodule (ZMod 2) V) : Subgroup G where
  carrier := {g | (∀ y ∈ Y, ρ g y - y ∈ Z) ∧ (∀ z ∈ Z, ρ g z ∈ Z) ∧ ∀ z ∈ Z, ρ g⁻¹ z ∈ Z}
  mul_mem' {a b} ha hb := by
    refine ⟨fun y hy => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · have : ρ (a * b) y - y = ρ a (ρ b y - y) + (ρ a y - y) := by
        rw [map_mul, Module.End.mul_apply, map_sub]
        abel
      rw [this]
      exact Z.add_mem (ha.2.1 _ (hb.1 y hy)) (ha.1 y hy)
    · rw [map_mul, Module.End.mul_apply]
      exact ha.2.1 _ (hb.2.1 z hz)
    · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
      exact hb.2.2 _ (ha.2.2 z hz)
  one_mem' := ⟨fun y _ => by simp, fun z hz => by simpa using hz, fun z hz => by simpa using hz⟩
  inv_mem' {a} ha := by
    refine ⟨fun y hy => ?_, ha.2.2, fun z hz => by simpa using ha.2.1 z hz⟩
    have : ρ a⁻¹ y - y = -ρ a⁻¹ (ρ a y - y) := by
      rw [map_sub, rep_inv_apply_apply]
      abel
    rw [this]
    exact Z.neg_mem (ha.2.2 _ (ha.1 y hy))

theorem mem_secKer {Y Z : Submodule (ZMod 2) V} {g : G} :
    g ∈ secKer ρ Y Z ↔ (∀ y ∈ Y, ρ g y - y ∈ Z) ∧ (∀ z ∈ Z, ρ g z ∈ Z) ∧ ∀ z ∈ Z, ρ g⁻¹ z ∈ Z :=
  Iff.rfl

theorem mem_secKer_of {H : Subgroup G} {Y Z : Submodule (ZMod 2) V} (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) {g : G}
    (hg : g ∈ H) (h : ∀ y ∈ Y, ρ g y - y ∈ Z) : g ∈ secKer ρ Y Z :=
  ⟨h, hZ g hg, hZ g⁻¹ (inv_mem hg)⟩

theorem conj_mem_secKer {Y Z : Submodule (ZMod 2) V} {g k : G} (hY : ∀ y ∈ Y, ρ g⁻¹ y ∈ Y)
    (hZ : ∀ z ∈ Z, ρ g z ∈ Z) (hZ' : ∀ z ∈ Z, ρ g⁻¹ z ∈ Z) (hk : k ∈ secKer ρ Y Z) :
    g * k * g⁻¹ ∈ secKer ρ Y Z := by
  refine ⟨fun y hy => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have : ρ (g * k * g⁻¹) y - y = ρ g (ρ k (ρ g⁻¹ y) - ρ g⁻¹ y) := by
      rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, rep_apply_inv_apply]
    rw [this]
    exact hZ _ (hk.1 _ (hY y hy))
  · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact hZ _ (hk.2.1 _ (hZ' z hz))
  · rw [show (g * k * g⁻¹)⁻¹ = g * k⁻¹ * g⁻¹ by group, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply]
    exact hZ _ (hk.2.2 _ (hZ' z hz))

theorem eq_one_of_mem_secKer {L : Subgroup G} [IsSimpleGroup ↥L] {Y Z : Submodule (ZMod 2) V}
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z) (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) {l : G}
    (hl : l ∈ L) (hk : l ∈ secKer ρ Y Z) : l = 1 := by
  let N : Subgroup ↥L := (secKer ρ Y Z).subgroupOf L
  have hN : N.Normal := ⟨fun n hn g => by
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ secKer ρ Y Z
    exact conj_mem_secKer (fun y hy => hY _ (inv_mem g.2) y hy) (hZ _ g.2)
      (fun z hz => hZ _ (inv_mem g.2) z hz) hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · have : (⟨l, hl⟩ : ↥L) ∈ N := hk
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    obtain ⟨l', hl', y, hy, hne⟩ := hnt
    have : (⟨l', hl'⟩ : ↥L) ∈ N := by rw [h]; trivial
    exact hne (this.1 y hy)

theorem commute_of_mem_secKer {L : Subgroup G} [IsSimpleGroup ↥L] {Y Z : Submodule (ZMod 2) V}
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z) (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb : b ∈ secKer ρ Y Z) :
    ∀ l ∈ L, l * b = b * l := by
  intro l hl
  have h1 : l * b * l⁻¹ ∈ secKer ρ Y Z :=
    conj_mem_secKer (fun y hy => hY _ (inv_mem hl) y hy) (hZ l hl) (hZ _ (inv_mem hl)) hb
  have h2 : l * b * l⁻¹ * b⁻¹ ∈ secKer ρ Y Z := mul_mem h1 (inv_mem hb)
  have h3 : l * b * l⁻¹ * b⁻¹ ∈ L := by
    have : b * l⁻¹ * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hbN _).1 (inv_mem hl)
    rw [show l * b * l⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) by group]
    exact mul_mem hl this
  have h4 := eq_one_of_mem_secKer hY hZ hnt h3 h2
  calc l * b = l * b * l⁻¹ * b⁻¹ * (b * l) := by group
    _ = b * l := by rw [h4, one_mul]

theorem exists_maximal_invariant [Finite V] {H : Subgroup G} {X : Submodule (ZMod 2) V}
    (hX : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H X) (hne : X ≠ ⊥) :
    ∃ X' : Submodule (ZMod 2) V, X' < X ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H X' ∧
      ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H W → X' ≤ W → W ≤ X → W = X' ∨ W = X := by
  let M : Set (Submodule (ZMod 2) V) := {W | CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H W ∧ W < X}
  have hM : M.Nonempty := ⟨⊥, fun h _ w hw => by
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero], bot_lt_iff_ne_bot.2 hne⟩
  obtain ⟨X', ⟨hX'inv, hX'lt⟩, hX'max⟩ := set_has_maximal_iff_noetherian.2 inferInstance M hM
  refine ⟨X', hX'lt, hX'inv, fun W hW hX'W hWX => ?_⟩
  by_cases hWe : W = X
  · exact Or.inr hWe
  · exact Or.inl (eq_of_le_of_not_lt hX'W (hX'max W ⟨hW, lt_of_le_of_ne hWX hWe⟩)).symm

theorem exists_irr_section [Finite V] {H L : Subgroup G} (hLH : L ≤ H) (hLp : Group.IsPerfect ↥L)
    {X : Submodule (ZMod 2) V} (hX : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H X) (hnt : ∃ l ∈ L, ∃ x ∈ X, ρ l x ≠ x) :
    ∃ Y Z : Submodule (ZMod 2) V, Z ≤ Y ∧ Y ≤ X ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z ∧
      (∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y) ∧
      ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z := by
  induction hn : finrank (ZMod 2) ↥X using Nat.strong_induction_on generalizing X with
  | _ k ih =>
  have hne : X ≠ ⊥ := by
    rintro rfl
    obtain ⟨l, -, x, hx, hlx⟩ := hnt
    rw [Submodule.mem_bot] at hx
    exact hlx (by rw [hx, map_zero])
  obtain ⟨X', hlt, hX', hmax⟩ := exists_maximal_invariant hX hne
  by_cases hA : ∃ l ∈ L, ∃ x ∈ X, ρ l x - x ∉ X'
  · exact ⟨X, X', hlt.le, le_rfl, hX, hX', hmax, hA⟩
  push Not at hA
  by_cases hB : ∃ l ∈ L, ∃ x ∈ X', ρ l x ≠ x
  · obtain ⟨Y, Z, hZY, hYX', hY, hZ, hirr, hmov⟩ :=
      ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) hX' hB rfl
    exact ⟨Y, Z, hZY, hYX'.trans hlt.le, hY, hZ, hirr, hmov⟩
  push Not at hB
  exfalso
  obtain ⟨l, hl, x, hx, hlx⟩ := hnt
  have h := CFSG.Quasithin.SteinbergCF.sub_mem_of_isPerfect ρ hLp (U := X') (Z := ⊥)
    (fun l hl u hu => by rw [hB l hl u hu, sub_self]; exact Submodule.zero_mem _)
    (x := x) (fun l hl => hA l hl x hx) l hl
  rw [Submodule.mem_bot, sub_eq_zero] at h
  exact hlx h

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
