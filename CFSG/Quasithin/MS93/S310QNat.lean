module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S310Mod

public section

namespace CFSG.Quasithin.MS93.S310Q

open Matrix CFSG.Quasithin.MS93.MSP CFSG.Quasithin.MS93.S310
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {F : Type} [Field F]
  {A Lt V Bk : Subgroup Γ} {a : ↥A →* Sp4 F} {βv : Γ → V4 F}

section CharTwo

variable [CharP F 2]

theorem exists_mulVec_e₁_eq_of_coord (hs : Setup A Lt V Bk a βv) {v : V4 F}
    (hv : v (.inr 0) ≠ 0) : ∃ l : ↥A, (l : Γ) ∈ Lt ∧ mat (a l) *ᵥ e₁ F = v := by
  have hw : ((v (.inr 0))⁻¹ • v) (.inr 0) = 1 := by
    rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hv]
  obtain ⟨l, hl, hle⟩ := hs.exists_mulVec_e₁ hv hw
  exact ⟨l, hl, by rw [hle, smul_smul, mul_inv_cancel₀ hv, one_smul]⟩

theorem exists_mulVec_e₁_eq (hs : Setup A Lt V Bk a βv) {v : V4 F} (hv : v ≠ 0) :
    ∃ l : ↥A, (l : Γ) ∈ Lt ∧ mat (a l) *ᵥ e₁ F = v := by
  by_cases h0 : v (.inr 0) ≠ 0
  · exact exists_mulVec_e₁_eq_of_coord hs h0
  rw [not_not] at h0
  obtain ⟨u, hu⟩ : ∃ u : V4 F, form F u v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (form_nondegenerate.1 v fun n => by rw [form_swap, hall n, neg_zero])
  obtain ⟨v₁, hv₁, hv₁v⟩ : ∃ v₁ : V4 F, v₁ (.inr 0) ≠ 0 ∧ form F v₁ v ≠ 0 := by
    by_cases hu0 : u (.inr 0) ≠ 0
    · exact ⟨u, hu0, hu⟩
    rw [not_not] at hu0
    by_cases hf : form F (f₁ F) v ≠ 0
    · exact ⟨f₁ F, by simp, hf⟩
    rw [not_not] at hf
    refine ⟨u + f₁ F, by simp [hu0], ?_⟩
    rw [LinearMap.map_add₂, hf, add_zero]
    exact hu
  obtain ⟨l₁, hl₁, he₁⟩ := exists_mulVec_e₁_eq_of_coord hs hv₁
  have hv' : (mat (a l₁⁻¹) *ᵥ v) (.inr 0) ≠ 0 := by
    rw [← form_e₁ (mat (a l₁⁻¹) *ᵥ v), ← form_mat (a l₁), map_inv, mat_mulVec_inv, he₁]
    exact hv₁v
  obtain ⟨l₂, hl₂, he₂⟩ := exists_mulVec_e₁_eq_of_coord hs hv'
  refine ⟨l₁ * l₂, mul_mem hl₁ hl₂, ?_⟩
  rw [map_mul, mat_mul_mulVec, he₂, map_inv, mat_mulVec_inv]

theorem exists_mem_of_not_le (hs : Setup A Lt V Bk a βv) {X : Subgroup Γ} (hXV : X ≤ V)
    (hXn : A ≤ Subgroup.normalizer (X : Set Γ)) (hXB : ¬ X ≤ Bk) (w : V4 F) :
    ∃ x ∈ X, βv x = w := by
  by_cases hw : w = 0
  · exact ⟨1, one_mem _, by rw [hs.map_one, hw]⟩
  obtain ⟨x₀, hx₀, hx₀B⟩ := Set.not_subset.1 hXB
  have hx₀0 : βv x₀ ≠ 0 := fun h0 => hx₀B ((hs.ker x₀ (hXV hx₀)).1 h0)
  obtain ⟨l₁, -, h₁⟩ := exists_mulVec_e₁_eq hs hx₀0
  obtain ⟨l₂, -, h₂⟩ := exists_mulVec_e₁_eq hs hw
  refine ⟨((l₂ * l₁⁻¹ : ↥A) : Γ) * x₀ * ((l₂ * l₁⁻¹ : ↥A) : Γ)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (hXn (l₂ * l₁⁻¹).2) x₀).1 hx₀, ?_⟩
  rw [hs.equiv _ x₀ (hXV hx₀), map_mul, mat_mul_mulVec, ← h₁, map_inv, mat_inv_mulVec, h₂]

end CharTwo

section Comm

variable [CharP F 2] [Fintype F]

theorem commutator_ne_one (hs : Setup A Lt V Bk a βv) (hcomm : ⁅⁅V, Lt⁆, Bk⁆ = ⊥)
    (hD : ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ Subgroup.centralizer (Lt : Set Γ))
    (hV₀ : ⁅⁅V, Lt⁆, Lt⁆ = ⁅V, Lt⁆)
    (hcard : Fintype.card F ≤ Nat.card ↥⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆) {u x : Γ} (hu : u ∈ ⁅V, Lt⁆)
    (hx : x ∈ ⁅V, Lt⁆) (hf : form F (βv x) (βv u) ≠ 0) : ⁅u, x⁆ ≠ 1 := by
  have hx0 : βv x ≠ 0 := fun h0 => hf (by rw [h0, map_zero, LinearMap.zero_apply])
  obtain ⟨l, -, hl⟩ := exists_mulVec_e₁_eq hs hx0
  have hn := hs.le_normalizer_comm (inv_mem l.2)
  set x' := ((l⁻¹ : ↥A) : Γ) * x * ((l⁻¹ : ↥A) : Γ)⁻¹ with hx'def
  set u' := ((l⁻¹ : ↥A) : Γ) * u * ((l⁻¹ : ↥A) : Γ)⁻¹ with hu'def
  have hx' : x' ∈ ⁅V, Lt⁆ := Setup.conj_mem hn hx
  have hu' : u' ∈ ⁅V, Lt⁆ := Setup.conj_mem hn hu
  have hx'e : βv x' = e₁ F := by
    rw [hx'def, hs.equiv _ x (hs.comm_le hx), ← hl, map_inv, mat_inv_mulVec]
  have hu'c : βv u' (.inr 0) ≠ 0 := by
    rw [← form_e₁ (βv u'), ← hx'e, hx'def, hu'def, hs.equiv _ x (hs.comm_le hx),
      hs.equiv _ u (hs.comm_le hu), form_mat]
    exact hf
  have hconj : ⁅u', x'⁆ = ((l⁻¹ : ↥A) : Γ) * ⁅u, x⁆ * ((l⁻¹ : ↥A) : Γ)⁻¹ := by
    rw [hx'def, hu'def]
    simp only [commutatorElement_def]
    group
  intro h1
  have h1' : ⁅u', x'⁆ = 1 := by rw [hconj, h1, mul_one, mul_inv_cancel]
  choose w hw hw' using fun s : F => hs.exists_comm_vec (s • f₁ F)
  have hinv : ∀ y ∈ ⁅V, Lt⁆, ⁅y⁻¹, x'⁆ = ⁅y, x'⁆⁻¹ := fun y hy => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← Setup.commutator_mul_left hD hV₀ hx' (inv_mem hy) hy, inv_mul_cancel,
      commutatorElement_one_left]
  let R : Subgroup Γ :=
    { carrier := {g | ∃ y ∈ ⁅V, Lt⁆, ⁅y, x'⁆ = g}
      one_mem' := ⟨1, one_mem _, commutatorElement_one_left x'⟩
      mul_mem' := by
        rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y * y', mul_mem hy hy', Setup.commutator_mul_left hD hV₀ hx' hy hy'⟩
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, inv_mem hy, hinv y hy⟩ }
  have hle : ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro y hy y' hy'
    obtain ⟨u'', hu''V, he⟩ := Setup.exists_eq_commutator hs hcomm hD hV₀ hx' hx'e hy hy'
    exact ⟨u'', hu''V, he.symm⟩
  have hcoord : ∀ y ∈ ⁅V, Lt⁆, ⁅y, x'⁆ = ⁅w (βv y (.inr 0)), x'⁆ := fun y hy =>
    Setup.commutator_eq_of_coord hs hcomm hD hV₀ hx' hx'e hy (hw _) (by rw [hw']; simp)
  have hsub : ((⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ : Subgroup Γ) : Set Γ) ⊆
      Set.range fun s : F => ⁅w s, x'⁆ := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hle hg
    exact ⟨βv y (.inr 0), (hcoord y hy).symm⟩
  have hcardr : Nat.card F = Nat.card ↥(Set.range fun s : F => ⁅w s, x'⁆) := by
    refine le_antisymm ?_ (Finite.card_range_le _)
    calc Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
      _ ≤ Nat.card ↥⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ := hcard
      _ ≤ Nat.card ↥(Set.range fun s : F => ⁅w s, x'⁆) :=
        Nat.card_mono (Set.finite_range _) hsub
  obtain ⟨e⟩ := Finite.card_eq.1 hcardr
  have hinj := (Finite.injective_iff_surjective_of_equiv e).2
    (Set.rangeFactorization_surjective (f := fun s : F => ⁅w s, x'⁆))
  have h0 : ⁅w 0, x'⁆ = 1 := by
    have := hcoord 1 (one_mem _)
    rw [hs.map_one, commutatorElement_one_left] at this
    exact this.symm
  have heq : Set.rangeFactorization (fun s : F => ⁅w s, x'⁆) (βv u' (.inr 0)) =
      Set.rangeFactorization (fun s : F => ⁅w s, x'⁆) 0 := by
    apply Subtype.ext
    change ⁅w (βv u' (.inr 0)), x'⁆ = ⁅w 0, x'⁆
    rw [← hcoord u' hu', h1', h0]
  exact hu'c (hinj heq)

theorem exists_form_ne_zero (hs : Setup A Lt V Bk a βv) [Finite ↥⁅V, Lt⁆] {K : Subgroup Γ}
    (hK : K.relIndex ⁅V, Lt⁆ ≤ Fintype.card F) :
    ∃ u ∈ K ⊓ ⁅V, Lt⁆, ∃ x ∈ K ⊓ ⁅V, Lt⁆, form F (βv x) (βv u) ≠ 0 := by
  by_contra hall
  push Not at hall
  set S : Set (V4 F) := βv '' ((K ⊓ ⁅V, Lt⁆ : Subgroup Γ) : Set Γ) with hSdef
  set W := Submodule.span F S with hWdef
  have hS : ∀ s ∈ S, ∀ t ∈ S, form F t s = 0 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨x, hx, rfl⟩
    exact hall u hu x hx
  have hW : ∀ v ∈ W, ∀ w ∈ W, form F w v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem s hs' =>
      intro w hw
      induction hw using Submodule.span_induction with
      | mem t ht => exact hS s hs' t ht
      | zero => simp
      | add x y _ _ hx hy => rw [LinearMap.map_add₂, hx, hy, add_zero]
      | smul c x _ hx => rw [LinearMap.map_smul₂, hx, smul_zero]
    | zero => intro w _; simp
    | add x y _ _ hx hy => intro w hw; rw [map_add, hx w hw, hy w hw, add_zero]
    | smul c x _ hx => intro w hw; rw [map_smul, hx w hw, smul_zero]
  have hWperp : W ≤ perp W := fun v hv => mem_perp.2 fun w hw => hW v hv w hw
  have hdim : Module.finrank F W ≤ 2 := by
    have h1 := finrank_perp W
    have h2 := Submodule.finrank_mono hWperp
    omega
  let ψ : ↥⁅V, Lt⁆ →* Multiplicative (V4 F) :=
    { toFun := fun x => Multiplicative.ofAdd (βv x)
      map_one' := by
        change Multiplicative.ofAdd (βv 1) = 1
        rw [hs.map_one]
        rfl
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (βv ((x : Γ) * y)) =
          Multiplicative.ofAdd (βv x) * Multiplicative.ofAdd (βv y)
        rw [hs.map_mul _ (hs.comm_le x.2) _ (hs.comm_le y.2)]
        rfl }
  have hψ : Function.Surjective ψ := fun w => by
    obtain ⟨x, hx, hxw⟩ := hs.exists_comm_vec (Multiplicative.toAdd w)
    exact ⟨⟨x, hx⟩, by
      change Multiplicative.ofAdd (βv x) = w
      rw [hxw]
      rfl⟩
  set W' : Subgroup (Multiplicative (V4 F)) := AddSubgroup.toSubgroup W.toAddSubgroup with hW'
  have hle : K.subgroupOf ⁅V, Lt⁆ ≤ W'.comap ψ := by
    intro x hx
    change βv x ∈ W
    exact Submodule.subset_span ⟨x, ⟨Subgroup.mem_subgroupOf.1 hx, x.2⟩, rfl⟩
  have hidx : (W'.comap ψ).index = W.toAddSubgroup.index := by
    rw [Subgroup.index_comap_of_surjective _ hψ, hW', AddSubgroup.index_toSubgroup]
  have hcardW : W.toAddSubgroup.index * Fintype.card F ^ Module.finrank F W =
      Fintype.card F ^ 4 := by
    have h1 := AddSubgroup.index_mul_card W.toAddSubgroup
    have h2 : Nat.card ↥W.toAddSubgroup = Fintype.card F ^ Module.finrank F W := by
      rw [show Nat.card ↥W.toAddSubgroup = Nat.card ↥W from rfl,
        Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card]
    have h3 : Nat.card (V4 F) = Fintype.card F ^ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card]
      congr 1
      simp
    rw [h2, h3] at h1
    exact h1
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hidx2 : Fintype.card F ^ 2 ≤ W.toAddSubgroup.index := by
    have hpow : Fintype.card F ^ Module.finrank F W ≤ Fintype.card F ^ 2 :=
      Nat.pow_le_pow_right (by omega) hdim
    by_contra hlt
    push Not at hlt
    have h4 : W.toAddSubgroup.index * Fintype.card F ^ Module.finrank F W <
        Fintype.card F ^ 2 * Fintype.card F ^ 2 :=
      Nat.mul_lt_mul_of_lt_of_le hlt hpow (by positivity)
    rw [hcardW, ← pow_add] at h4
    exact lt_irrefl _ h4
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  have hpos : 0 < (K.subgroupOf ⁅V, Lt⁆).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have h5 := Nat.le_of_dvd hpos hdvd
  have h6 : Fintype.card F ^ 2 ≤ Fintype.card F := (hidx2.trans h5).trans hK
  nlinarith

end Comm

end CFSG.Quasithin.MS93.S310Q
