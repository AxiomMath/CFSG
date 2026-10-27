module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQGamma

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace V2InQ

variable {G : Type} [Group G]

theorem cube_centralizes {V : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (V : Set G))
    (hc3 : conjAct V ⟨c, hcN⟩ ^ 3 = 1) : ∀ a ∈ V, c ^ 3 * a * (c ^ 3)⁻¹ = a := by
  intro a ha
  have hc3N : c ^ 3 ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hcN 3
  have h1 : conjAct V ⟨c ^ 3, hc3N⟩ = conjAct V ⟨c, hcN⟩ ^ 3 := by
    rw [← map_pow]
    rfl
  have h2 := conj_coe_apply V ⟨c ^ 3, hc3N⟩ ⟨a, ha⟩
  rw [h1, hc3] at h2
  exact h2.symm

theorem normalizes_W {V W : Subgroup G} (hVe : IsElemAbelian 2 V) (hWV : W ≤ V)
    {y γ : MulAut ↥V} (hker : (@normOf ↥V (commGroupOfElemAbelian hVe) y).ker = W.subgroupOf V)
    (hγy : γ * y = y * γ) {c : G} (hcN : c ∈ Subgroup.normalizer (V : Set G))
    (hγ : γ = conjAct V ⟨c, hcN⟩) : ∀ a ∈ W, c * a * c⁻¹ ∈ W := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  intro a ha
  let u : ↥V := ⟨a, hWV ha⟩
  have hu : u ∈ (normOf y).ker := by
    rw [hker]
    exact ha
  have hcomm : ∀ v : ↥V, γ (y v) = y (γ v) := fun v => by
    have h := congrArg (fun φ : MulAut ↥V => φ v) hγy
    simpa only [MulAut.mul_apply] using h
  have hγu : γ u ∈ (normOf y).ker := by
    show normOf y (γ u) = 1
    rw [normOf_apply, ← hcomm, ← hcomm, ← map_mul, ← map_mul]
    have h1 : normOf y u = 1 := hu
    rw [normOf_apply] at h1
    rw [h1, map_one]
  rw [hker] at hγu
  have h3 := conj_coe_apply V ⟨c, hcN⟩ u
  rw [← hγ] at h3
  have h4 : ((γ u : ↥V) : G) ∈ W := hγu
  rw [h3] at h4
  exact h4

theorem centralizes_of_comm {L V₂ : Subgroup G} {c : G}
    (hcL : ∀ ℓ ∈ L, c * ℓ * c⁻¹ * ℓ⁻¹ ∈ blockQ L)
    (hcU : ∀ u ∈ blockU L, u⁻¹ * (c * u * c⁻¹) ∈ blockZ L) (hV2L : V₂ ≤ L)
    (hV2sq : ∀ a ∈ V₂, a * a = 1) (hcV : ∀ a ∈ V₂, c * a * c⁻¹ ∈ V₂)
    (hVQ : V₂ ⊓ blockQ L ≤ blockU L) (hVZ : ∀ a ∈ V₂, a ∈ blockZ L → a = 1)
    (hc3 : ∀ a ∈ V₂, c ^ 3 * a * (c ^ 3)⁻¹ = a) : ∀ a ∈ V₂, c * a * c⁻¹ = a := by
  have hsq : ∀ a ∈ V₂, c * (c * a * c⁻¹) * c⁻¹ = a := by
    intro a ha
    set w := c * a * c⁻¹ * a⁻¹ with hw
    have hwV : w ∈ V₂ := V₂.mul_mem (hcV a ha) (V₂.inv_mem ha)
    have hwQ : w ∈ blockQ L := hcL a (hV2L ha)
    have hwU : w ∈ blockU L := hVQ ⟨hwV, hwQ⟩
    have hcw : c * w * c⁻¹ ∈ V₂ := hcV w hwV
    have hz : w⁻¹ * (c * w * c⁻¹) = 1 :=
      hVZ _ (V₂.mul_mem (V₂.inv_mem hwV) hcw) (hcU w hwU)
    have hfix : c * w * c⁻¹ = w := by
      have : c * w * c⁻¹ = w * (w⁻¹ * (c * w * c⁻¹)) := by group
      rw [this, hz, mul_one]
    have hca : c * a * c⁻¹ = w * a := by rw [hw]; group
    have hww : w * w = 1 := hV2sq w hwV
    calc c * (c * a * c⁻¹) * c⁻¹ = c * (w * a) * c⁻¹ := by rw [hca]
      _ = (c * w * c⁻¹) * (c * a * c⁻¹) := by group
      _ = w * (w * a) := by rw [hfix, hca]
      _ = (w * w) * a := by group
      _ = a := by rw [hww, one_mul]
  intro a ha
  calc c * a * c⁻¹ = c * (c * (c * a * c⁻¹) * c⁻¹) * c⁻¹ := by rw [hsq a ha]
    _ = c ^ 3 * a * (c ^ 3)⁻¹ := by
      rw [show c ^ 3 = c * (c * c) by simp [pow_succ, mul_assoc]]
      group
    _ = a := hc3 a ha

end V2InQ

section Select

open V2InQ

variable {A : Type*} [Group A] {B C : Type*} [Group B] [Group C]

theorem card_range_dvd_of_ker_le (f : A →* B) (g : A →* C) (h : f.ker ≤ g.ker) :
    Nat.card g.range ∣ Nat.card f.range := by
  let φ : (A ⧸ f.ker) →* C := QuotientGroup.lift f.ker g h
  have hφ : φ.range = g.range := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : A ⧸ f.ker), rfl⟩
  rw [← hφ]
  exact (Subgroup.card_range_dvd φ).trans
    (dvd_of_eq (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv))

theorem exists_ker_ne_one (f : A →* B) (g : A →* C)
    (h : ¬ Nat.card g.range ∣ Nat.card f.range) : ∃ a, f a = 1 ∧ g a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (card_range_dvd_of_ker_le f g fun a ha =>
    MonoidHom.mem_ker.2 (hcon a (MonoidHom.mem_ker.1 ha)))

theorem exists_ker_ne_one_of_card (f : A →* B) (g : A →* C) {n m : ℕ}
    (hf : Nat.card f.range ∣ n) (hg : Nat.card g.range ∣ m) (h : Nat.gcd n m = 3)
    (hlt : 3 < Nat.card g.range) : ∃ a, f a = 1 ∧ g a ≠ 1 := by
  refine exists_ker_ne_one f g fun hd => ?_
  have h1 : Nat.card g.range ∣ Nat.gcd n m := Nat.dvd_gcd (hd.trans hf) hg
  rw [h] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

end Select

end CFSG.Quasithin
