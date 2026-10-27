module

public import CFSG.RankThree.GF2n.Smith81.S81QIdeal
public import CFSG.RankThree.GF2n.Smith81.S81ZStep

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z
open CFSG.RankThree.GF2n.Smith81.S81Z.IdealEnum


theorem Rd6_subset_Rpos : Rd6 ⊆ Rpos := fun γ hγ =>
  mem_Rpos.2 ⟨(perp_iff.1 (mem_Rd6.1 hγ).1).1, (mem_Rd6.1 hγ).2⟩

theorem Rd6_coord_le_one {γ : Rt} (hγ : γ ∈ Rd6) :
    (γ nodeA2 = 0 ∨ γ nodeA2 = 1) ∧ (γ nodeNu = 0 ∨ γ nodeNu = 1) := by
  have h := mem_Rd6.1 hγ
  have h' := perp_iff.1 h.1
  obtain ⟨i, hi, rfl⟩ := exists_rtD6 h'.1 h'.2 h.2
  have key : ∀ i < 30, (rtD6 i nodeA2 = 0 ∨ rtD6 i nodeA2 = 1) ∧
      (rtD6 i nodeNu = 0 ∨ rtD6 i nodeNu = 1) := by decide +kernel
  exact key i hi

theorem hfA2 : ∀ γ ∈ Rd6, fA2 γ = 0 ∨ fA2 γ = 1 := fun γ hγ => (Rd6_coord_le_one hγ).1

theorem hfNu : ∀ γ ∈ Rd6, fNu γ = 0 ∨ fNu γ = 1 := fun γ hγ => (Rd6_coord_le_one hγ).2

theorem ht_le_Rd6 : ∀ α ∈ Rd6, ht α ≤ 17 := fun α hα => ht_le_seventeen α (Rd6_subset_Rpos hα)

theorem chars_Rd6 {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : Chars K Rd6 :=
  ⟨fun α hα => (chars_Rpos hq).surj α (Rd6_subset_Rpos hα),
   fun α hα β hβ hne σ => (chars_Rpos hq).ne α (Rd6_subset_Rpos hα) β (Rd6_subset_Rpos hβ) hne σ⟩

theorem Rn_eq_image (n : Fin (Tag.rank .E7)) :
    Rn (Pi.evalAddMonoidHom (fun _ => ℤ) n) Rd6 =
      ((Finset.range 30).filter fun i => rtD6 i n = 1).image rtD6 := by
  classical
  ext γ
  rw [Finset.mem_image]
  constructor
  · intro hγ
    obtain ⟨hγR, hγ1⟩ := Finset.mem_filter.1 hγ
    have h := mem_Rd6.1 hγR
    have h' := perp_iff.1 h.1
    obtain ⟨i, hi, rfl⟩ := exists_rtD6 h'.1 h'.2 h.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hγ1⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hi30, hpr⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨rtD6_mem_Rd6 (Finset.mem_range.1 hi30), hpr⟩

theorem card_Rn_fA2 : (Rn fA2 Rd6).card = 15 := by
  rw [show fA2 = Pi.evalAddMonoidHom (fun _ => ℤ) nodeA2 from rfl, Rn_eq_image,
    Finset.card_image_of_injOn]
  · decide +kernel
  · intro i hi j hj hij
    exact rtD6_inj i (Finset.mem_range.1 (Finset.mem_filter.1 hi).1) j
      (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) hij

theorem card_Rn_fNu : (Rn fNu Rd6).card = 15 := by
  rw [show fNu = Pi.evalAddMonoidHom (fun _ => ℤ) nodeNu from rfl, Rn_eq_image,
    Finset.card_image_of_injOn]
  · decide +kernel
  · intro i hi j hj hij
    exact rtD6_inj i (Finset.mem_range.1 (Finset.mem_filter.1 hi).1) j
      (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) hij

theorem abelian_Rn {f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ} (hf : ∀ γ ∈ Rd6, f γ = 0 ∨ f γ = 1) :
    ∀ α ∈ Rn f Rd6, ∀ β ∈ Rn f Rd6, ¬ IsRoot .E7 (α + β) := by
  intro α hα β hβ hroot
  obtain ⟨hαR, hα1⟩ := Finset.mem_filter.1 hα
  obtain ⟨hβR, hβ1⟩ := Finset.mem_filter.1 hβ
  rcases hf _ (closed_Rd6.add α hαR β hβR hroot) with h | h <;>
    rw [map_add, hα1, hβ1] at h <;> omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_URge_le {N : Finset Rt} (hN : Closed N) (hab : ∀ α ∈ N, ∀ β ∈ N, ¬ IsRoot .E7 (α + β))
    (hC : Chars K N) (hH : ∀ α ∈ N, ht α ≤ 17) :
    Nat.card ↥(URge K N 1) ≤ Nat.card K ^ N.card := by
  have hstab := isStab_URge (K := K) hN hab
  rw [card_E_eq_pow_Aset hN hH hstab hC]
  exact Nat.pow_le_pow_right Nat.card_pos (Finset.card_le_card fun α hα => (mem_Aset.1 hα).mem)

theorem step1_D6 (hq : 4 ≤ Nat.card K) {E : Subgroup (Gp K)} (hE : IsStab Rd6 E)
    (hcard : Nat.card K ^ 15 ≤ Nat.card ↥E) :
    E = URge K (Rn fA2 Rd6) 1 ∨ E = URge K (Rn fNu Rd6) 1 := by
  have hC := chars_Rd6 (K := K) hq
  have hR := closed_Rd6
  have hq2 : 2 ≤ Nat.card K := by omega
  have hpow := card_E_eq_pow_Aset hR ht_le_Rd6 hE hC
  have hA15 : 15 ≤ (Aset hR E).card := by
    rw [hpow] at hcard
    exact (Nat.pow_le_pow_iff_right hq2).1 hcard
  have hAeq : Aset hR E = Rn fA2 Rd6 ∨ Aset hR E = Rn fNu Rd6 := by
    refine hIdeal_D6 _ ?_ ?_ ?_ hA15
    · intro α hα
      exact (mem_Aset.1 hα).mem
    · intro α hα β hβ
      exact InA.abelian hR hE hC (mem_Aset.1 hα) (mem_Aset.1 hβ)
    · intro α hα β hβ hroot
      exact mem_Aset.2 (InA.upper hR hE hC (mem_Aset.1 hα) hβ hroot)
  have key : ∀ f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ, (∀ γ ∈ Rd6, f γ = 0 ∨ f γ = 1) →
      Aset hR E = Rn f Rd6 → (Rn f Rd6).card = 15 → E = URge K (Rn f Rd6) 1 := by
    intro f hf hAf hcardN
    have hsupp : ∀ α, InA hR E α → f α = 1 := by
      intro α hα
      have : α ∈ Rn f Rd6 := by rw [← hAf]; exact mem_Aset.2 hα
      exact (Finset.mem_filter.1 this).2
    have hle : E ≤ URge K (Rn f Rd6) 1 := E_le_Rn hf hR hE hC ht_le_Rd6 hsupp
    have hRn : Closed (Rn f Rd6) := closed_Rn hf hR
    have hCn : Chars K (Rn f Rd6) :=
      ⟨fun α hα => hC.surj α (Rn_subset _ hα),
       fun α hα β hβ hne σ => hC.ne α (Rn_subset _ hα) β (Rn_subset _ hβ) hne σ⟩
    have hle2 := card_URge_le hRn (abelian_Rn hf) hCn
      (fun α hα => ht_le_Rd6 α (Rn_subset _ hα))
    rw [hcardN] at hle2
    exact Subgroup.eq_of_le_of_card_ge hle (le_trans hle2 hcard)
  rcases hAeq with h | h
  · exact Or.inl (key fA2 hfA2 h card_Rn_fA2)
  · exact Or.inr (key fNu hfNu h card_Rn_fNu)

end CFSG.RankThree.GF2n.Smith81.D6Spin
