module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace V2InQ

section Split

variable {V : Type*} [CommGroup V]

theorem fixOf_eq_of_split {y : MulAut V} {Z W : Subgroup V} (hsup : Z ⊔ W = ⊤)
    (hZ : ∀ a ∈ Z, y a = a) (hfpf : ∀ a ∈ W, y a = a → a = 1) : fixOf y = Z := by
  apply le_antisymm
  · intro v hv
    have hv' : v ∈ Z ⊔ W := by rw [hsup]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv'
    have h1 : y (a * b) = a * b := hv
    rw [map_mul, hZ a ha] at h1
    have h2 : y b = b := mul_left_cancel h1
    have : b = 1 := hfpf b hb h2
    rw [this, mul_one]
    exact ha
  · intro a ha
    exact hZ a ha

theorem ker_normOf_eq_of_split {y : MulAut V} {Z W : Subgroup V} (hsup : Z ⊔ W = ⊤)
    (hy3 : y ^ 3 = 1) (hsq : ∀ v : V, v * v = 1) (hZ : ∀ a ∈ Z, y a = a)
    (hfpf : ∀ a ∈ W, y a = a → a = 1) (hW : ∀ a ∈ W, y a ∈ W) : (normOf y).ker = W := by
  have hW1 : ∀ b ∈ W, normOf y b = 1 := by
    intro b hb
    have h1 : normOf y b ∈ fixOf y := normOf_mem_fixOf hy3 b
    have h2 : normOf y b ∈ W := by
      rw [normOf_apply]
      exact W.mul_mem (W.mul_mem hb (hW b hb)) (hW _ (hW b hb))
    exact hfpf _ h2 h1
  apply le_antisymm
  · intro v hv
    have hv' : v ∈ Z ⊔ W := by rw [hsup]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv'
    have h1 : normOf y (a * b) = 1 := hv
    rw [map_mul, hW1 b hb, mul_one, normOf_apply_of_mem hsq (hZ a ha)] at h1
    rw [h1, one_mul]
    exact hb
  · intro b hb
    exact hW1 b hb

end Split

section Transport

variable {G : Type} [Group G]

theorem card_subgroupOf_of_le {V X : Subgroup G} (hXV : X ≤ V) :
    Nat.card (X.subgroupOf V) = Nat.card X := by
  have h := Subgroup.card_map_of_injective (K := X.subgroupOf V) V.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hXV] at h
  exact h.symm

theorem conjAct_mem_oTwoUpper_of_oPrime {V M X : Subgroup G} (hXM : X ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {y : G} (hy : y ∈ oPrimeResidualOf 3 X) :
    ∃ hyN : y ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨y, hyN⟩ ∈ oTwoUpper (autOn M V) := by
  have hle : oPrimeResidualOf 3 X ≤ preOn M V (oTwoUpper (autOn M V)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxX, k, hxk⟩
    have hxM : x ∈ M := hXM hxX
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hMN hxM
    refine mem_preOn.2 ⟨hxM, hxN, ?_⟩
    have hmem : conjAct V ⟨x, hxN⟩ ∈ autOn M V := mem_autOn_iff_exists.2 ⟨x, hxN, hxM, rfl⟩
    refine mem_oTwoUpper_of_odd hmem ?_
    have hdvd : orderOf (conjAct V ⟨x, hxN⟩) ∣ 3 ^ k := by
      have h1 := orderOf_map_dvd (conjAct V) (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G))
      rwa [← Subgroup.orderOf_coe, show (((⟨x, hxN⟩ : Subgroup.normalizer (V : Set G))) : G) = x
        from rfl, hxk] at h1
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hdvd
  obtain ⟨-, hyN, hyP⟩ := mem_preOn.1 (hle hy)
  exact ⟨hyN, hyP⟩

theorem normalizes_of_commute {V Z : Subgroup G} (hVe : IsElemAbelian 2 V) (hZV : Z ≤ V)
    {y : MulAut ↥V} (hfix : @fixOf ↥V (commGroupOfElemAbelian hVe) y = Z.subgroupOf V) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hcomm : conjAct V ⟨x, hx⟩ * y = y * conjAct V ⟨x, hx⟩) :
    x ∈ Subgroup.normalizer (Z : Set G) := by
  have key : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)),
      conjAct V ⟨x, hx⟩ * y = y * conjAct V ⟨x, hx⟩ → ∀ a ∈ Z, x * a * x⁻¹ ∈ Z := by
    intro x hx hcomm a ha
    have haV : a ∈ V := hZV ha
    let u : ↥V := ⟨a, haV⟩
    have hu : u ∈ @fixOf ↥V (commGroupOfElemAbelian hVe) y := by
      rw [hfix]
      exact ha
    have hyu : y u = u := hu
    have h1 : y (conjAct V ⟨x, hx⟩ u) = conjAct V ⟨x, hx⟩ u := by
      have := congrArg (fun φ : MulAut ↥V => φ u) hcomm
      simp only [MulAut.mul_apply] at this
      rw [← this, hyu]
    have h2 : conjAct V ⟨x, hx⟩ u ∈ @fixOf ↥V (commGroupOfElemAbelian hVe) y := h1
    rw [hfix] at h2
    have h3 := conj_coe_apply V ⟨x, hx⟩ u
    have h4 : ((conjAct V ⟨x, hx⟩ u : ↥V) : G) ∈ Z := h2
    rw [h3] at h4
    exact h4
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key x hx hcomm a, fun ha => ?_⟩
  have hx' : x⁻¹ ∈ Subgroup.normalizer (V : Set G) := (Subgroup.normalizer (V : Set G)).inv_mem hx
  have hc' : conjAct V ⟨x⁻¹, hx'⟩ * y = y * conjAct V ⟨x⁻¹, hx'⟩ := by
    have h1 : conjAct V ⟨x⁻¹, hx'⟩ = (conjAct V ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h1]
    exact (show Commute (conjAct V ⟨x, hx⟩) y from hcomm).inv_left.eq
  have := key x⁻¹ hx' hc' _ ha
  simpa [mul_assoc] using this

end Transport

end V2InQ

end CFSG.Quasithin
