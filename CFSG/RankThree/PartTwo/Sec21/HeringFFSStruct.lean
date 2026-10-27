module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFSCent
public import CFSG.RankThree.PartTwo.Sec21.HeringFFSConj
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank
  (eq_one_of_mem_center_of_pow_eq_one)

open CFSG.Open (IsElemAbelian)

theorem ffs_decomp {G : Type} [Group G] [Finite G] {C X B : Subgroup G}
    (hXC : X ≤ C) (hCN : C ≤ Subgroup.normalizer (X : Set G)) (P : Sylow 3 C)
    (hPB : (P : Subgroup C).map C.subtype = B)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥X))
    (hE : ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hQ : ∀ R : Subgroup (↥X ⧸ Subgroup.center ↥X), IsPGroup 3 R → Nat.card R ≤ 9)
    (hI : ∀ b ∈ B, ∃ x ∈ X, x⁻¹ * b ∈ Subgroup.centralizer (X : Set G)) :
    IsElemAbelian 3 (B ⊓ X) ∧ Nat.card ↥(B ⊓ X) = 9 ∧
      ∀ b ∈ B, ∃ t ∈ B ⊓ X, ∃ s ∈ B ⊓ Subgroup.centralizer (X : Set G), b = t * s := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBC : B ≤ C := hPB ▸ Subgroup.map_subtype_le _
  have hB3 : IsPGroup 3 B := hPB ▸ P.isPGroup'.map C.subtype
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBC.trans hCN
  obtain ⟨E, hEX, hEab, hE9⟩ := hE
  obtain ⟨c, hcC, hc⟩ := ffs_exists_conj_map_le P (hEX.trans hXC) hEab.isPGroup
  rw [hPB] at hc
  set E' : Subgroup G := E.map (MulAut.conj c).toMonoidHom with hE'
  have hE'B : E' ≤ B ⊓ X := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hc x hx, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hCN hcC) x).mp (hEX hx)
  have hE'card : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hE9
  have hT3 : IsPGroup 3 (B ⊓ X : Subgroup G) := hB3.to_inf_left
  have hTle : Nat.card ↥(B ⊓ X) ≤ 9 := ffs_card_le_nine_of_isPGroup hZ hQ inf_le_right hT3
  have hTE : E' = B ⊓ X := Subgroup.eq_of_le_of_card_ge hE'B (by rw [hE'card]; exact hTle)
  have hTel : IsElemAbelian 3 (B ⊓ X) := hTE ▸ hEab.map (MulAut.conj c).toMonoidHom
  have hT9 : Nat.card ↥(B ⊓ X) = 9 := hTE ▸ hE'card
  refine ⟨hTel, hT9, ?_⟩
  set Θ : ↥B →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hBN) with hΘ
  have hΘapp : ∀ (b : ↥B) (y : ↥X), ((Θ b y : ↥X) : G) = (b : G) * (y : G) * (b : G)⁻¹ :=
    fun b y => rfl
  set ρ : ↥X →* MulAut ↥X := MulAut.conj with hρ
  have hInn : ∀ b : ↥B, Θ b ∈ ρ.range := by
    intro b
    obtain ⟨x, hx, hd⟩ := hI b b.2
    refine ⟨⟨x, hx⟩, ?_⟩
    ext y
    have hcomm : (y : G) * (x⁻¹ * (b : G)) = (x⁻¹ * (b : G)) * y :=
      Subgroup.mem_centralizer_iff.mp hd y y.2
    have h2 : (x⁻¹ * (b : G)) * y * (x⁻¹ * (b : G))⁻¹ = y := by
      rw [← hcomm, mul_inv_cancel_right]
    have h1 : (b : G) * y * (b : G)⁻¹ =
        x * ((x⁻¹ * (b : G)) * y * (x⁻¹ * (b : G))⁻¹) * x⁻¹ := by
      group
    rw [hΘapp, h1, h2]
    simp [hρ, MulAut.conj_apply]
  let e := CFSG.RankThree.PartTwo.Sec4.innerEquivQuotientCenter ↥X
  set Θ' : ↥B →* ↥ρ.range := Θ.codRestrict ρ.range hInn with hΘ'
  set χ : ↥B →* (↥X ⧸ Subgroup.center ↥X) := e.symm.toMonoidHom.comp Θ' with hχ
  have hker : ∀ b : ↥B, χ b = 1 → (b : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro b hb
    have h1 : Θ' b = 1 := by
      have : e.symm (Θ' b) = e.symm 1 := by rw [map_one]; exact hb
      exact e.symm.injective this
    have h2 : Θ b = 1 := congrArg Subtype.val h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h3 := congrArg (fun f : MulAut ↥X => ((f ⟨y, hy⟩ : ↥X) : G)) h2
    simp only [hΘapp, MulAut.one_apply] at h3
    exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  set T' : Subgroup ↥B := (B ⊓ X).subgroupOf B with hT'
  set φ : ↥T' →* (↥X ⧸ Subgroup.center ↥X) := χ.comp T'.subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have hker' := hker (t : ↥B) ht
    have htX : ((t : ↥B) : G) ∈ X := (Subgroup.mem_subgroupOf.mp t.2).2
    have hcent : (⟨((t : ↥B) : G), htX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hker' g g.2)
    obtain ⟨k, hk⟩ := hB3 (t : ↥B)
    have hxk : (⟨((t : ↥B) : G), htX⟩ : ↥X) ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg (fun z : ↥B => (z : G)) hk
      simpa using this
    have h1 := eq_one_of_mem_center_of_pow_eq_one Nat.prime_three hZ hcent hxk
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg (fun z : ↥X => (z : G)) h1
  have hrange3 : IsPGroup 3 χ.range := by
    rintro ⟨y, b, rfl⟩
    obtain ⟨k, hk⟩ := hB3 b
    exact ⟨k, Subtype.ext (by simp [← map_pow, hk])⟩
  have hR9 : Nat.card χ.range ≤ 9 := hQ _ hrange3
  have hφcard : Nat.card φ.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ⊓ X ≤ B)).toEquiv]
    exact hT9
  have hφle : φ.range ≤ χ.range := by
    rintro _ ⟨t, rfl⟩
    exact ⟨T'.subtype t, rfl⟩
  have hφeq : φ.range = χ.range :=
    Subgroup.eq_of_le_of_card_ge hφle (by rw [hφcard]; exact hR9)
  intro b hb
  obtain ⟨t, ht⟩ : χ ⟨b, hb⟩ ∈ φ.range := by
    rw [hφeq]
    exact ⟨⟨b, hb⟩, rfl⟩
  have htB : ((t : ↥B) : G) ∈ B := (t : ↥B).2
  have htT : ((t : ↥B) : G) ∈ B ⊓ X := Subgroup.mem_subgroupOf.mp t.2
  refine ⟨((t : ↥B) : G), htT, ((t : ↥B) : G)⁻¹ * b, ⟨B.mul_mem (B.inv_mem htB) hb, ?_⟩, ?_⟩
  · have h1 : χ ((t : ↥B)⁻¹ * ⟨b, hb⟩) = 1 := by
      rw [map_mul, map_inv]
      have : χ (t : ↥B) = χ ⟨b, hb⟩ := ht
      rw [this, inv_mul_cancel]
    exact hker _ h1
  · simp

end CFSG.RankThree.PartTwo.Sec21
