module

public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s16ae_stab3_stab_of_map_eq {T : Type} [CommGroup T] {W : Subgroup T}
    {φ : MulAut T} (h : W.map φ.toMonoidHom = W) : φ ∈ stabSub W := by
  intro u
  constructor
  · intro hu
    have hu' : φ u ∈ W.map φ.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := φ.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : φ u ∈ W.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [h] at hu'
    exact hu'

private lemma s16ae_stab3_card_le_two_of_isPGroup_perm {H : Subgroup (Equiv.Perm (Fin 3))}
    (hH : IsPGroup 2 H) : Nat.card H ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hH
  have hdvd : 2 ^ k ∣ 6 := by
    have h1 := Subgroup.card_subgroup_dvd_card H
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)), Fintype.card_perm,
      Fintype.card_fin, hk] at h1
    simpa [Nat.factorial] using h1
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans hdvd
    omega
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := pow_one 2

theorem s16ae_card_le_two_mul_cent_of_rank_two {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {Y : Subgroup T} (hY : rk ↥Y = 2) {A : Subgroup (MulAut T)}
    (hA : IsElemAbelian2 A) (hAY : ∀ a ∈ A, Y.map a.toMonoidHom = Y) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ centSub Y) := by
  classical
  haveI : Fintype ↥Y := Fintype.ofFinite ↥Y
  have hcardY : Nat.card ↥Y = 4 := by
    rw [card_eq_two_pow hT Y, hY]
    norm_num
  have hAY' : A ≤ stabSub Y := fun a ha => s16ae_stab3_stab_of_map_eq (hAY a ha)
  have hle : Nat.card (autSub A Y) ≤ 2 := by
    let S : Set ↥Y := {y | y ≠ 1}
    have hcardS : Fintype.card S = 3 := by
      show Fintype.card {y : ↥Y // y ≠ 1} = 3
      rw [Fintype.card_subtype_compl (fun y : ↥Y => y = 1),
        Fintype.card_subtype_eq (1 : ↥Y), Fintype.card_eq_nat_card, hcardY]
    let eS : S ≃ Fin 3 := Fintype.equivFinOfCardEq hcardS
    let ρ : MulAut ↥Y →* Equiv.Perm S :=
      { toFun := fun g => Equiv.Perm.subtypePerm (g : ↥Y ≃ ↥Y) (fun y => by
          have hy1 : g y = 1 ↔ y = 1 := by
            calc g y = 1 ↔ g y = g 1 := by rw [map_one]
              _ ↔ y = 1 := g.injective.eq_iff
          exact not_congr hy1)
        map_one' := Equiv.ext (fun x => Subtype.ext rfl)
        map_mul' := by intro g h; exact Equiv.ext (fun x => Subtype.ext rfl) }
    have hρinj : Function.Injective ρ := by
      intro g h hgh
      ext y
      by_cases hy : y = 1
      · simp [hy]
      · have h2 := congrArg (fun (σ : Equiv.Perm S) => ((σ ⟨y, hy⟩ : S) : ↥Y)) hgh
        dsimp only [ρ] at h2
        simpa using h2
    let eρ : Equiv.Perm S ≃* Equiv.Perm (Fin 3) := eS.permCongrHom
    let H : Subgroup (Equiv.Perm (Fin 3)) := (autSub A Y).map (eρ.toMonoidHom.comp ρ)
    have hHcard : Nat.card H = Nat.card (autSub A Y) := by
      show Nat.card ((autSub A Y).map (eρ.toMonoidHom.comp ρ)) = Nat.card (autSub A Y)
      exact Subgroup.card_map_of_injective (eρ.injective.comp hρinj)
    have hAstab : IsPGroup 2 ↥(A.subgroupOf (stabSub Y)) := by
      obtain ⟨n, hn⟩ := (E3.isPGroup_of_isElemAbelian2 hA).exists_card_dvd_pow
      refine IsPGroup.of_card_dvd_pow (n := n) ?_
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY').toEquiv]
    have hHp : IsPGroup 2 H := (hAstab.map (resHom Y)).map (eρ.toMonoidHom.comp ρ)
    rw [← hHcard]
    exact s16ae_stab3_card_le_two_of_isPGroup_perm hHp
  rw [← card_autSub_mul hAY']
  exact Nat.mul_le_mul_right _ hle

theorem s16ae_exists_index_two_fix_ne_of_stab_three {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} {Y : ι → Subgroup T} (hsup : ⨆ i, Y i = ⊤)
    (hrk : ∀ i, rk ↥(Y i) = 2) {A : Subgroup (MulAut T)} (hA : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) (hstab : ∀ a ∈ A, ∀ i, (Y i).map a.toMonoidHom = Y i) :
    ∃ B : Subgroup (MulAut T), B ≤ A ∧ E3.mQuot A B ≤ 1 ∧ fixV B ≠ fixV A := by
  classical
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have hmove : ∃ i, ∃ y ∈ Y i, a y ≠ y := by
    by_contra hcon
    apply ha1
    have hle : ⨆ i, Y i ≤ MonoidHom.eqLocus a.toMonoidHom (MonoidHom.id T) :=
      iSup_le fun i y hy => by
        by_contra hy'
        exact hcon ⟨i, y, hy, hy'⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    have hv : v ∈ ⨆ i, Y i := by rw [hsup]; exact Subgroup.mem_top v
    exact hle hv
  obtain ⟨i, y, hyY, hay⟩ := hmove
  have hcard := s16ae_card_le_two_mul_cent_of_rank_two hT (hrk i) hA fun b hb => hstab b hb i
  set B : Subgroup (MulAut T) := A ⊓ centSub (Y i) with hB
  refine ⟨B, inf_le_left, ?_, ?_⟩
  · have hmul : B.relIndex A * Nat.card B = Nat.card A := by
      have h := Subgroup.relIndex_mul_card (H := B) (K := A)
      rwa [inf_eq_left.2 (inf_le_left : B ≤ A)] at h
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hle : B.relIndex A ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ B.relIndex A := by omega
      have := Nat.mul_le_mul_right (Nat.card B) h3
      omega
    have hne : B.relIndex A ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      have : 0 < Nat.card A := Nat.card_pos
      omega
    show padicValNat 2 (B.relIndex A) ≤ 1
    have h12 : B.relIndex A = 1 ∨ B.relIndex A = 2 := by omega
    rcases h12 with h | h
    · rw [h]; simp
    · rw [h]; simp
  · intro hfix
    have hy : y ∈ fixV B := fun x hx => mem_centSub.1 hx.2 y hyY
    rw [hfix] at hy
    exact hay (hy a haA)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
