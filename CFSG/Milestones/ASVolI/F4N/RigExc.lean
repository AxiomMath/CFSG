module

public import CFSG.Milestones.ASVolI.F4N.BId
public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Milestones.ASVolI.F4N.Cor

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section U33

theorem burnsideF4n_u33z_sq :
    u33z * u33z = 1 := by
  apply u33PresHom_injective
  rw [map_mul, u33PresHom_z, map_one]
  decide +kernel

theorem burnsideF4n_u33z_ne_one : u33z ≠ 1 := by
  intro h
  apply u33P_Z.2
  rw [← u33PresHom_z, h, map_one]

theorem burnsideF4n_u33z_central_B :
    ∀ b ∈ u33Data.B, b * u33z = u33z * b := by
  have key : ∀ k ∈ [0, 1, 2, 4], u33GenPG k ∈ Subgroup.centralizer ({u33z} : Set U33G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply u33PresHom_injective
    rw [map_mul, map_mul, u33PresHom_genPG, u33PresHom_z]
    have h := (u33P_Z.1 k hk).1
    calc u33GenP k * u33Z = (u33GenP k * u33Z * (u33GenP k)⁻¹) * u33GenP k := by group
      _ = u33Z * u33GenP k := by rw [h]
  have hle : u33Data.B ≤ Subgroup.centralizer ({u33z} : Set U33G) := by
    show Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 4} : Set U33G) ≤ _
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact key 0 (by simp)
    · exact key 1 (by simp)
    · exact key 2 (by simp)
    · exact key 4 (by simp)
  intro b hb
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)

theorem burnsideF4n_u33_B_not_equiv_A
    (χ : ↥u33Data.B ≃* ↥u33Data.A) : False := by
  let z₀ : ↥u33Data.B := ⟨u33z, u33Data.T_le_B u33z_mem_T⟩
  have hz₀ : z₀ * z₀ = 1 := Subtype.ext burnsideF4n_u33z_sq
  refine burnsideF4c_u33_no_x u33Data.A u33Data.T_le_A u33Data.x_mem_A (χ z₀ : U33G) ?_ ?_ ?_
  · intro h
    apply burnsideF4n_u33z_ne_one
    have h1 : χ z₀ = χ 1 := by rw [map_one]; exact Subtype.ext h
    exact congrArg Subtype.val (χ.injective h1)
  · have h1 : χ z₀ * χ z₀ = 1 := by rw [← map_mul, hz₀, map_one]
    exact congrArg Subtype.val h1
  · intro q hq
    obtain ⟨b, hb⟩ := χ.surjective ⟨q, hq⟩
    have hbz : b * z₀ = z₀ * b := Subtype.ext (burnsideF4n_u33z_central_B b b.2)
    have h1 := congrArg (fun t => ((χ t : ↥u33Data.A) : U33G)) hbz
    simp only [map_mul, Subgroup.coe_mul] at h1
    rw [hb] at h1
    exact h1

end U33

section Overgroups

theorem burnsideF4n_overgroups_g2d
    {p f : ℕ} {E : Type} [Group E] {M₁ M₂ : Subgroup E} (hyp : HypF_4_4 GLKind.G2d p f ⊤ M₁ M₂) :
    (∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₁) → X = M₁) ∧
      (∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₂) → X = M₂) := by
  obtain ⟨Φ, hT, hB, hA⟩ := burnsideF4nB_ident hyp
  have hmap : ∀ X : Subgroup E, (X.comap Φ.toMonoidHom).map Φ.toMonoidHom = X := fun X =>
    Subgroup.map_comap_eq_self_of_surjective Φ.surjective X
  have hcard : ∀ X : Subgroup E, Nat.card (X.comap Φ.toMonoidHom) = Nat.card X := fun X => by
    conv_rhs => rw [← hmap X]
    rw [Subgroup.card_map_of_injective Φ.injective]
  have hcardB : Nat.card M₁ = 96 := by
    rw [← hB, Subgroup.card_map_of_injective Φ.injective, CFSG.Quasithin.H13.U3.card_u33_B]
  have hcardA : Nat.card M₂ = 96 := by
    rw [← hA, Subgroup.card_map_of_injective Φ.injective, CFSG.Quasithin.H13.U3.card_u33_A]
  have hcardT : Nat.card u33Data.T = 32 := u33_card_T
  have hcardtop : Nat.card (⊤ : Subgroup U33G) = 6048 := by
    rw [Subgroup.card_top, card_u33Pres]
  have key : ∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nat.card X = 96 →
      (X.comap Φ.toMonoidHom = u33Data.B ∧ X = M₁) ∨ (X.comap Φ.toMonoidHom = u33Data.A ∧ X = M₂) := by
    intro X hX h96
    have hTX : u33Data.T ≤ X.comap Φ.toMonoidHom := by
      intro t ht
      exact hX (hT ▸ Subgroup.mem_map_of_mem _ ht)
    rcases u33Data.lattice _ hTX with h | h | h | h
    · rw [← hcard X, h, hcardT] at h96
      omega
    · right
      exact ⟨h, by rw [← hmap X, h, hA]⟩
    · left
      exact ⟨h, by rw [← hmap X, h, hB]⟩
    · rw [← hcard X, h, hcardtop] at h96
      omega
  refine ⟨fun X hX ⟨χ⟩ => ?_, fun X hX ⟨χ⟩ => ?_⟩
  · have h96 : Nat.card X = 96 := by rw [Nat.card_congr χ.toEquiv, hcardB]
    rcases key X hX h96 with ⟨-, h⟩ | ⟨hXA, -⟩
    · exact h
    ·
      exfalso
      have e1 : ↥u33Data.B ≃* ↥M₁ := (Φ.subgroupMap u33Data.B).trans (MulEquiv.subgroupCongr hB)
      have e2 : ↥X ≃* ↥u33Data.A :=
        (MulEquiv.subgroupCongr (hmap X).symm).trans
          ((Φ.subgroupMap (X.comap Φ.toMonoidHom)).symm.trans (MulEquiv.subgroupCongr hXA))
      exact burnsideF4n_u33_B_not_equiv_A ((e1.trans χ.symm).trans e2)
  · have h96 : Nat.card X = 96 := by rw [Nat.card_congr χ.toEquiv, hcardA]
    rcases key X hX h96 with ⟨hXB, -⟩ | ⟨-, h⟩
    ·
      exfalso
      have e1 : ↥u33Data.A ≃* ↥M₂ := (Φ.subgroupMap u33Data.A).trans (MulEquiv.subgroupCongr hA)
      have e2 : ↥X ≃* ↥u33Data.B :=
        (MulEquiv.subgroupCongr (hmap X).symm).trans
          ((Φ.subgroupMap (X.comap Φ.toMonoidHom)).symm.trans (MulEquiv.subgroupCongr hXB))
      exact burnsideF4n_u33_B_not_equiv_A ((e1.trans χ.symm).trans e2).symm
    · exact h

open CFSG.Sporadic.Schreier.Tits in
theorem burnsideF4n_tits_overgroup_eq
    {X X' : Subgroup titsD} (hX : titsSD ≤ X) (hX' : titsSD ≤ X')
    (hc : Nat.card X = Nat.card X') : X = X' := by
  have hS := card_titsSD
  have hH := card_titsHD
  have hN := card_titsND
  have hD : Nat.card (⊤ : Subgroup titsD) = 17971200 := by rw [Subgroup.card_top, card_titsD]
  rcases titsD_overgroups X hX with h | h | h | h <;>
    rcases titsD_overgroups X' hX' with h' | h' | h' | h' <;>
    first
    | (rw [h, h'] at hc; omega)
    | (rw [h, h'])

open CFSG.Sporadic.Schreier.Tits in
theorem burnsideF4n_overgroups_tits
    {p f : ℕ} {E : Type} [Group E] {M₁ M₂ : Subgroup E} (hyp : HypF_4_4 GLKind.Tits p f ⊤ M₁ M₂) :
    (∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₁) → X = M₁) ∧
      (∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₂) → X = M₂) := by
  haveI : Finite E := hyp.finite
  obtain ⟨hp2, -, hmodel⟩ := hyp.model
  subst hp2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ₀⟩ := titsModelEquiv _ 2 f hmodel
  let ψ₁ : E ≃* ↥titsD := Subgroup.topEquiv.symm.trans ψ₀
  obtain ⟨⟨S₀, ⟨-, hSp, hSi⟩, hB⟩, -⟩ := burnsideF4n_parabolics_at hyp
  rw [top_inf_eq, top_inf_eq] at hB
  rw [Subgroup.relIndex_top_right] at hSi
  have hS₀B : S₀ ≤ M₁ ⊓ M₂ := hB ▸ Subgroup.le_normalizer
  let S₁ : Subgroup ↥titsD := S₀.map ψ₁.toMonoidHom
  have hcS₁ : Nat.card S₁ = Nat.card S₀ := Subgroup.card_map_of_injective ψ₁.injective
  have hS₁p : IsPGroup 2 S₁ := hSp.map _
  have hS₁i : ¬ 2 ∣ S₁.index := by
    have h1 := Subgroup.card_mul_index S₁
    have h2 := Subgroup.card_mul_index S₀
    rw [hcS₁, ← Nat.card_congr ψ₁.toEquiv] at h1
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)]
    exact hSi
  have hSp' : IsPGroup 2 titsSD := IsPGroup.of_card (n := 11) (by rw [card_titsSD]; norm_num)
  have hSi' : ¬ 2 ∣ titsSD.index := by
    have h := Subgroup.card_mul_index titsSD
    rw [card_titsSD, card_titsD] at h
    have : titsSD.index = 8775 := by omega
    rw [this]
    decide
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq (↥titsD) (hS₁p.toSylow hS₁i) (hSp'.toSylow hSi')
  let ψ : E ≃* ↥titsD := ψ₁.trans (MulAut.conj d)
  have hψS : S₀.map ψ.toMonoidHom = titsSD := by
    have h1 : ((d • hS₁p.toSylow hS₁i : Sylow 2 ↥titsD) : Subgroup ↥titsD) = titsSD := by
      rw [hd, IsPGroup.toSylow_coe]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨ψ₁ s, ⟨s, hs, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hover : ∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → titsSD ≤ X.map ψ.toMonoidHom := fun X hX =>
    hψS ▸ Subgroup.map_mono (hS₀B.trans hX)
  have hcard : ∀ X : Subgroup E, Nat.card (X.map ψ.toMonoidHom) = Nat.card X := fun X =>
    Subgroup.card_map_of_injective ψ.injective
  have hmapinj : Function.Injective (Subgroup.map ψ.toMonoidHom) :=
    Subgroup.map_injective ψ.injective
  refine ⟨fun X hX ⟨χ⟩ => hmapinj ?_, fun X hX ⟨χ⟩ => hmapinj ?_⟩
  · refine burnsideF4n_tits_overgroup_eq (hover X hX) (hover M₁ inf_le_left) ?_
    rw [hcard, hcard, Nat.card_congr χ.toEquiv]
  · refine burnsideF4n_tits_overgroup_eq (hover X hX) (hover M₂ inf_le_right) ?_
    rw [hcard, hcard, Nat.card_congr χ.toEquiv]

end Overgroups

end CFSG.ASVolI
