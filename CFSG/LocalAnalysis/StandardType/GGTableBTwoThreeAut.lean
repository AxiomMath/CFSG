module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeBasis
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndNode

public section

namespace CFSG.StandardType.TwoThree

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly CFSG.StandardType.TypeA

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem units_eq_one (hK : Nat.card K = 2) (u : Kˣ) : u = 1 := by
  apply Units.ext
  rcases eq_zero_or_eq_one_of_card hK (u : K) with h | h
  · exact absurd h u.ne_zero
  · rw [h, Units.val_one]

theorem conjAut_injective (hK : Nat.card K = 2) (hd : 0 < d) :
    Function.Injective (conjAut d K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one hA
  obtain ⟨u, hu⟩ := exists_unit_of_scalar hd hc
  rw [hu, units_eq_one hK u, map_one]

theorem card_le_pow_half {G : Type*} [Group G] {X : Subgroup G} (hX : IsElemAbelian 3 X)
    (h : Nat.card X ^ 2 ≤ 3 ^ d) : Nat.card X ≤ 3 ^ (d / 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases finite_or_infinite X with hfin | hinf
  swap
  · rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hX)
  rw [hk, ← pow_mul] at h
  rw [hk]
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

variable [CharP K 2]

theorem card_sq_le_of_subset_conjAut (hK : Nat.card K = 2) (hd : 0 < d)
    {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian 3 X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card X ^ 2 ≤ 3 ^ d := by
  have hinj := conjAut_injective hK hd (d := d)
  set Xt := X.comap (conjAut d K) with hXt
  have hcardt : Nat.card Xt = Nat.card X := by
    refine Nat.card_congr (Equiv.ofBijective (fun A : Xt => (⟨conjAut d K A, A.2⟩ : X)) ⟨?_, ?_⟩)
    · intro A B hAB
      exact Subtype.ext (hinj (congrArg Subtype.val hAB))
    · rintro ⟨x, hx⟩
      obtain ⟨A, rfl⟩ := hXI hx
      exact ⟨⟨A, hx⟩, rfl⟩
  set e := (Matrix.GeneralLinearGroup.toLin : GL (Fin d) K ≃* _) with he
  set Y : Subgroup (Module.End K (Fin d → K))ˣ := Xt.map e.toMonoidHom with hY
  have hcardY : Nat.card Y = Nat.card Xt :=
    (Nat.card_congr (Xt.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply hinj
    rw [map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hX hA hB
  have hexp : ∀ x ∈ Y, x ^ 3 = 1 := by
    rintro _ ⟨A, hA, rfl⟩
    rw [← map_pow]
    have : A ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hX.2 _ hA)
    rw [this, map_one]
  have h := card_sq_le_top hK Y hcomm hexp
  rwa [Module.finrank_fin_fun, hcardY, hcardt] at h

theorem ggBstarBound_two (hK : Nat.card K = 2) (hd : 3 ≤ d) :
    GGBstarBound 3 (d / 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have h1 := card_le_mul_card_inf_linear Nat.prime_three (by norm_num) hd hEh
  have hD : IsElemAbelian 3 (Eh ⊓ linearAutGroup d K : Subgroup _) :=
    TableB.isElemAbelian_mono hEh inf_le_left
  have h2 : Nat.card (Eh ⊓ linearAutGroup d K : Subgroup _) ≤ 3 ^ (d / 2) :=
    card_le_pow_half hD (card_sq_le_of_subset_conjAut hK (by omega) hD
      (fun x hx => mem_linearAutGroup_iff.mp hx.2))
  have h4 : 3 ^ (d / 2 + 2) ≤ Nat.card Eh :=
    calc 3 ^ (d / 2 + 2) = 3 ^ 2 * 3 ^ (d / 2) := by rw [← pow_add, add_comm]
      _ ≤ 3 ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
  have h5 : Nat.card Eh ≤ 3 ^ (d / 2 + 1) :=
    calc Nat.card Eh ≤ 3 * Nat.card (Eh ⊓ linearAutGroup d K : Subgroup _) := h1
      _ ≤ 3 * 3 ^ (d / 2) := Nat.mul_le_mul_left _ h2
      _ = 3 ^ (d / 2 + 1) := by rw [pow_succ']
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (h4.trans h5)
  omega

theorem card_lt_of_subset_conjAut (hK : Nat.card K = 2) (hd : 0 < d) (hd5 : d ≤ 5)
    {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian 3 X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card X < 3 ^ 3 := by
  have h := card_le_pow_half hX (card_sq_le_of_subset_conjAut hK hd hX hXI)
  have h2 : 3 ^ (d / 2) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (3 : ℕ) ^ 2 < 3 ^ 3 := by norm_num
  omega

theorem ggBstarBound_two_small (hK : Nat.card K = 2) (hd : 0 < d) (hd5 : d ≤ 5) :
    GGBstarBound 3 0 (projectiveSL d K) (Set.range (conjAut d K)) :=
  ggBstarBound_of_card_lt fun _ hXI hX => card_lt_of_subset_conjAut hK hd hd5 hX hXI

theorem ggEndNode_two_small (hK : Nat.card K = 2) (hd : 0 < d) (hd5 : d ≤ 5) :
    GGEndNode 3 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hlt := card_lt_of_subset_conjAut hK hd hd5 hX hXI
  rw [hcard] at hlt
  omega

end CFSG.StandardType.TwoThree
