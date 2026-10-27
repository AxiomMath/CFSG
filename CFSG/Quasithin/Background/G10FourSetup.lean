module

public import CFSG.Quasithin.Background.G10FourBasic
public import CFSG.Quasithin.Background.G10Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace G101Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
  (h : G101Hyp B Γ v₁ W X X₀)

include h

theorem B_apply_fix {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X) (v : V) : B v₁ (x v) = B v₁ v := by
  have := h.isometry x (h.X_le hx) v₁ v
  rwa [h.X_fixes x hx] at this

variable (Z : Submodule (ZMod 2) V)

theorem inf_eq_bot (hZ : Invariant X Z) (h1 : v₁ ∉ Z) : W ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwW, hwZ⟩
  by_contra hw0
  have hw0' : w ≠ 0 := fun h0 => hw0 (by simp [h0])
  have hwv : w ≠ v₁ := fun hwv => h1 (hwv ▸ hwZ)
  have hnot : (⟨w, hwW⟩ : W) ∉ Submodule.span (ZMod 2) {(⟨v₁, h.mem_W⟩ : W)} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    rcases g10Four_zmod_two_cases a with rfl | rfl
    · apply hw0'
      have := congrArg Subtype.val ha
      simpa using this.symm
    · apply hwv
      have := congrArg Subtype.val ha
      simpa using this.symm
  obtain ⟨f, hf, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0 : f ⟨v₁, h.mem_W⟩ = 0 := by
    have : f ⟨v₁, h.mem_W⟩ ∈ (Submodule.span (ZMod 2) {(⟨v₁, h.mem_W⟩ : W)}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    rw [hfmap] at this
    simpa using this
  have hf1 : f ⟨w, hwW⟩ = 1 := by
    rcases g10Four_zmod_two_cases (f ⟨w, hwW⟩) with h0 | h0
    · exact absurd h0 hf
    · exact h0
  obtain ⟨x, hx, hxf⟩ := h.transvection_full f hf0
  have hxw := hxf ⟨w, hwW⟩
  simp only [hf1, one_smul] at hxw
  have hxZ := hZ x hx w hwZ
  rw [hxw] at hxZ
  apply h1
  have := Z.sub_mem hxZ hwZ
  simpa using this

theorem fix_of_perp (hZ : Invariant X Z) (h1 : v₁ ∉ Z) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X)
    {z : V} (hz : z ∈ Z) (hB : B v₁ z = 0) : x z = z := by
  have hW : x z - z ∈ W := h.commutator_le x hx z hB
  have hZ' : x z - z ∈ Z := Z.sub_mem (hZ x hx z hz) hz
  have : x z - z ∈ W ⊓ Z := ⟨hW, hZ'⟩
  rw [h.inf_eq_bot Z hZ h1, Submodule.mem_bot] at this
  exact sub_eq_zero.1 this

omit [Finite V] h in
theorem exists_one (h2 : ∃ z ∈ Z, B v₁ z ≠ 0) : ∃ z₀ ∈ Z, B v₁ z₀ = 1 := by
  obtain ⟨z, hz, hne⟩ := h2
  refine ⟨z, hz, ?_⟩
  rcases g10Four_zmod_two_cases (B v₁ z) with h0 | h0
  · exact absurd h0 hne
  · exact h0

theorem act_eq (hZ : Invariant X Z) (h1 : v₁ ∉ Z) {z₀ : V} (hz₀ : z₀ ∈ Z) (hB : B v₁ z₀ = 1)
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X) {z : V} (hz : z ∈ Z) :
    x z = z + B v₁ z • (x z₀ - z₀) := by
  have hmem : z - B v₁ z • z₀ ∈ Z := Z.sub_mem hz (Z.smul_mem _ hz₀)
  have hperp : B v₁ (z - B v₁ z • z₀) = 0 := by
    rw [map_sub, map_smul, hB, smul_eq_mul, mul_one]
    exact sub_self _
  have := h.fix_of_perp Z hZ h1 hx hmem hperp
  rw [map_sub, map_smul] at this
  have h' : x z = z - B v₁ z • z₀ + B v₁ z • x z₀ := by
    rw [← this]
    abel
  rw [h', smul_sub]
  abel

theorem center_mem (hZ : Invariant X Z) {z₀ : V} (hz₀ : z₀ ∈ Z) (hB : B v₁ z₀ = 1)
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X) : x z₀ - z₀ ∈ Z ∧ B v₁ (x z₀ - z₀) = 0 := by
  refine ⟨Z.sub_mem (hZ x hx z₀ hz₀) hz₀, ?_⟩
  rw [map_sub, h.B_apply_fix hx, hB]
  exact sub_self _

theorem centralizerOn_le (h2 : ∃ z ∈ Z, B v₁ z ≠ 0) : centralizerOn X Z ≤ X₀ := by
  obtain ⟨z₀, hz₀, hB⟩ := G101Hyp.exists_one Z h2
  intro k hk
  by_contra hk0
  have := h.centralizer_le k hk.1 hk0 z₀ (hk.2 z₀ hz₀)
  rw [hB] at this
  exact one_ne_zero this

theorem relIndex_eq_pow : X₀.relIndex X = 2 ^ Nat.log 2 (X₀.relIndex X) := by
  obtain ⟨k, hk⟩ := h.exists_card_X
  have hdvd : X₀.relIndex X ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card X₀ X
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hjeq, Nat.log_pow Nat.one_lt_two]

omit h in
theorem finrank_ker_lt (h2 : ∃ z ∈ Z, B v₁ z ≠ 0) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker ((B v₁).domRestrict Z)) <
      Module.finrank (ZMod 2) Z := by
  apply Submodule.finrank_lt
  intro htop
  obtain ⟨z, hz, hne⟩ := h2
  have hmem : (⟨z, hz⟩ : Z) ∈ LinearMap.ker ((B v₁).domRestrict Z) := by
    rw [htop]
    trivial
  exact hne hmem

theorem exists_centerHom (hZ : Invariant X Z) (h1 : v₁ ∉ Z) {z₀ : V} (hz₀ : z₀ ∈ Z)
    (hB : B v₁ z₀ = 1) :
    ∃ φ : ↥X →* Multiplicative ↥(LinearMap.ker ((B v₁).domRestrict Z)),
      (∀ x : ↥X, (((Multiplicative.toAdd (φ x) : ↥(LinearMap.ker ((B v₁).domRestrict Z))) :
        ↥Z) : V) = (x : V ≃ₗ[ZMod 2] V) z₀ - z₀) ∧
      φ.ker = (centralizerOn X Z).subgroupOf X := by
  have hmem : ∀ x : ↥X, (⟨(x : V ≃ₗ[ZMod 2] V) z₀ - z₀,
      (h.center_mem Z hZ hz₀ hB x.2).1⟩ : ↥Z) ∈ LinearMap.ker ((B v₁).domRestrict Z) := by
    intro x
    exact (h.center_mem Z hZ hz₀ hB x.2).2
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd ⟨_, hmem x⟩) ?_, fun x => rfl, ?_⟩
  · intro x y
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Subtype.ext
    show (x * y : ↥X).1 z₀ - z₀ = ((x : V ≃ₗ[ZMod 2] V) z₀ - z₀) + ((y : V ≃ₗ[ZMod 2] V) z₀ - z₀)
    have hy := h.center_mem Z hZ hz₀ hB y.2
    have hfix := h.fix_of_perp Z hZ h1 x.2 hy.1 hy.2
    have hxy : (x * y : ↥X).1 z₀ = x.1 (y.1 z₀) := rfl
    rw [hxy]
    have : y.1 z₀ = z₀ + (y.1 z₀ - z₀) := by abel
    conv_lhs => rw [this, map_add, hfix]
    abel
  · ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h0 : (x : V ≃ₗ[ZMod 2] V) z₀ - z₀ = 0 := by
        have := congrArg (fun a : Multiplicative ↥(LinearMap.ker ((B v₁).domRestrict Z)) =>
          (((Multiplicative.toAdd a : ↥(LinearMap.ker ((B v₁).domRestrict Z))) : ↥Z) : V)) hx
        simpa using this
      refine ⟨x.2, fun u hu => ?_⟩
      rw [h.act_eq Z hZ h1 hz₀ hB x.2 hu, h0]
      simp
    · intro hx
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      apply Subtype.ext
      show (x : V ≃ₗ[ZMod 2] V) z₀ - z₀ = 0
      rw [hx.2 z₀ hz₀]
      exact sub_self _

theorem counting (hZ : Invariant X Z) (h1 : v₁ ∉ Z) (h2 : ∃ z ∈ Z, B v₁ z ≠ 0) :
    Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) Z = Module.finrank (ZMod 2) V ∧
    Module.finrank (ZMod 2) Z = Nat.log 2 (X₀.relIndex X) + 1 ∧
    centralizerOn X Z = X₀ ∧
    (∀ a : Z, B v₁ a = 0 → ∃ x ∈ X, ∀ u : Z, x u = u + B v₁ u • (a : V)) ∧
    Module.finrank (ZMod 2) ↥(LinearMap.ker ((B v₁).domRestrict Z)) + 1 =
      Module.finrank (ZMod 2) Z := by
  obtain ⟨z₀, hz₀, hB⟩ := G101Hyp.exists_one Z h2
  obtain ⟨φ, hφval, hφker⟩ := h.exists_centerHom Z hZ h1 hz₀ hB
  let A : Submodule (ZMod 2) ↥Z := LinearMap.ker ((B v₁).domRestrict Z)
  set C := centralizerOn X Z with hC
  have hCX₀ : C ≤ X₀ := h.centralizerOn_le Z h2
  have hX₀X : X₀ ≤ X := h.X₀_le
  have hr : X₀.relIndex X = 2 ^ Nat.log 2 (X₀.relIndex X) := h.relIndex_eq_pow
  have hc : C.relIndex X = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hφker, Subgroup.index_ker]
  have hAcard : Nat.card A = 2 ^ Module.finrank (ZMod 2) A :=
    (FiniteField.pow_finrank_eq_natCard 2 A).symm
  have hrange : Nat.card φ.range ≤ Nat.card A := by
    calc Nat.card φ.range ≤ Nat.card (Multiplicative ↥A) := Subgroup.card_le_card_group _
      _ = Nat.card A := Nat.card_congr Multiplicative.toAdd
  have hmul : C.relIndex X₀ * X₀.relIndex X = C.relIndex X :=
    Subgroup.relIndex_mul_relIndex C X₀ X hCX₀ hX₀X
  have hcpos : 0 < C.relIndex X := by
    rw [hc]
    exact Nat.card_pos
  have hrpos : 0 < X₀.relIndex X := by
    rw [hr]
    exact pow_pos (by norm_num) _
  have hrc : X₀.relIndex X ≤ C.relIndex X := by
    rw [← hmul]
    exact Nat.le_mul_of_pos_left _ (by
      rcases Nat.eq_zero_or_pos (C.relIndex X₀) with h0 | h0
      · rw [h0, zero_mul] at hmul
        omega
      · exact h0)
  have hle : 2 ^ Nat.log 2 (X₀.relIndex X) ≤ 2 ^ Module.finrank (ZMod 2) A := by
    calc 2 ^ Nat.log 2 (X₀.relIndex X) = X₀.relIndex X := hr.symm
      _ ≤ C.relIndex X := hrc
      _ = Nat.card φ.range := hc
      _ ≤ Nat.card A := hrange
      _ = 2 ^ Module.finrank (ZMod 2) A := hAcard
  have hk : Nat.log 2 (X₀.relIndex X) ≤ Module.finrank (ZMod 2) A :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hle
  have hAlt : Module.finrank (ZMod 2) A < Module.finrank (ZMod 2) Z :=
    G101Hyp.finrank_ker_lt Z h2
  have hWZ : Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) Z ≤ Module.finrank (ZMod 2) V := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W Z
    rw [h.inf_eq_bot Z hZ h1, finrank_bot] at this
    have h3 := Submodule.finrank_le (W ⊔ Z)
    omega
  have hrank := h.rank
  have hd : 0 < Module.finrank (ZMod 2) V :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨v₁, h.point⟩
  have hkA : Nat.log 2 (X₀.relIndex X) = Module.finrank (ZMod 2) A := by omega
  have hrEq : X₀.relIndex X = C.relIndex X := by
    apply le_antisymm hrc
    calc C.relIndex X = Nat.card φ.range := hc
      _ ≤ Nat.card A := hrange
      _ = 2 ^ Module.finrank (ZMod 2) A := hAcard
      _ = 2 ^ Nat.log 2 (X₀.relIndex X) := by rw [hkA]
      _ = X₀.relIndex X := hr.symm
  have hA5 : Module.finrank (ZMod 2) A + 1 = Module.finrank (ZMod 2) Z := by omega
  refine ⟨by omega, by omega, ?_, ?_, hA5⟩
  ·
    have h11 : C.relIndex X₀ = 1 := by
      have : C.relIndex X₀ * X₀.relIndex X = 1 * X₀.relIndex X := by
        rw [hmul, one_mul, hrEq]
      exact Nat.eq_of_mul_eq_mul_right hrpos this
    exact le_antisymm hCX₀ (Subgroup.relIndex_eq_one.1 h11)
  ·
    have hcardeq : Nat.card φ.range = Nat.card (Multiplicative ↥A) := by
      rw [← hc, ← hrEq]
      calc X₀.relIndex X = 2 ^ Nat.log 2 (X₀.relIndex X) := hr
        _ = 2 ^ Module.finrank (ZMod 2) A := by rw [hkA]
        _ = Nat.card A := hAcard.symm
        _ = Nat.card (Multiplicative ↥A) := (Nat.card_congr Multiplicative.toAdd).symm
    have htop : φ.range = ⊤ := (Subgroup.card_eq_iff_eq_top φ.range).1 hcardeq
    intro a ha
    have hmem : a ∈ A := by
      rw [LinearMap.mem_ker]
      exact ha
    have : Multiplicative.ofAdd (⟨a, hmem⟩ : ↥A) ∈ φ.range := by
      rw [htop]
      trivial
    obtain ⟨x, hx⟩ := this
    have hxa : (x : V ≃ₗ[ZMod 2] V) z₀ - z₀ = (a : V) := by
      rw [← hφval x, hx]
      rfl
    refine ⟨x, x.2, fun u => ?_⟩
    rw [h.act_eq Z hZ h1 hz₀ hB x.2 u.2, hxa]

theorem notMem_of_invariant {U : Submodule (ZMod 2) V} (hU : Invariant Γ U) (hU1 : U ≠ ⊤) :
    v₁ ∉ U := by
  intro hv
  apply hU1
  rw [eq_top_iff, ← h.span_orbit, Submodule.span_le]
  rintro w ⟨γ, rfl⟩
  exact hU γ γ.2 v₁ hv

theorem exists_not_perp_of_invariant {U : Submodule (ZMod 2) V} (hU : Invariant Γ U)
    (hU0 : U ≠ ⊥) : ∃ u ∈ U, B v₁ u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hU0
  rw [eq_bot_iff]
  intro u hu
  have hperp : ∀ w ∈ Submodule.span (ZMod 2) (MulAction.orbit Γ v₁), B u w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      have hinv : (γ : V ≃ₗ[ZMod 2] V)⁻¹ ∈ Γ := Γ.inv_mem γ.2
      have h1 : B v₁ ((γ : V ≃ₗ[ZMod 2] V)⁻¹ u) = 0 := hcon _ (hU _ hinv u hu)
      have h2 := h.isometry (γ : V ≃ₗ[ZMod 2] V) γ.2 ((γ : V ≃ₗ[ZMod 2] V)⁻¹ u) v₁
      have h3 : (γ : V ≃ₗ[ZMod 2] V) ((γ : V ≃ₗ[ZMod 2] V)⁻¹ u) = u := by simp
      rw [h3] at h2
      have h4 : B ((γ : V ≃ₗ[ZMod 2] V)⁻¹ u) v₁ = 0 := h.isRefl _ _ h1
      show B u ((γ : V ≃ₗ[ZMod 2] V) v₁) = 0
      rw [h2, h4]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  rw [h.span_orbit] at hperp
  have : u = 0 := h.nondegenerate u (fun w => hperp w trivial)
  simp [this]

theorem exists_not_perp_of_comm {U : Submodule (ZMod 2) V} (hU : Invariant X U) (h1 : v₁ ∉ U)
    (hc : commSpace X U ≠ ⊥) : ∃ u ∈ U, B v₁ u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hc
  rw [commSpace, Submodule.span_eq_bot]
  rintro w ⟨k, hk, u, hu, rfl⟩
  have := h.fix_of_perp U hU h1 hk hu (hcon u hu)
  simp [this]

end G101Hyp

end CFSG.Quasithin
