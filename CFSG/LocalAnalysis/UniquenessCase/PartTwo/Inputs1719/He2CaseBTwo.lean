module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.He2CaseA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.InFSqSolvableCalN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB
open CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He1 CFSG.Quasithin.RonanE114.HeOver
  CFSG.Quasithin.ModH.He2
open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

theorem key_he_caseB_two : ∀ j : Fin 11, 2 ∈ heIncl[(j : ℕ)]! →
    (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ (j : ℕ) = 6 := by
  decide

theorem he_Y2_map_of_normalizes_S {J : Type} [Group J] [Finite J] (hl : HeLat J)
    {α : MulAut J} (hα : hl.S.map α.toMonoidHom = hl.S) :
    (hl.Y 2).map α.toMonoidHom = hl.Y 2 := by
  rw [← he_Y3_inf_Y4 hl, Subgroup.map_inf_eq _ _ _ α.injective]
  rcases aut_Y34 hl hα with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h3, h4]
  · rw [h3, h4, inf_comm]

theorem he2_map_Y2_of_mem {Y J : Type} [Group Y] [Group J] [Finite J] {K S : Subgroup Y}
    [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S) :
    ∀ t ∈ S, (hl.Y 2).map (autK e t).toMonoidHom = hl.Y 2 := by
  intro t ht
  exact he_Y2_map_of_normalizes_S hl (he2_map_S_of_mem hl e he t ht)

theorem he2_le_normalizer_pull {Y J : Type} [Group Y] [Group J] [Finite J] {K S : Subgroup Y}
    [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S) :
    S ≤ Subgroup.normalizer ((((hl.Y 2).map e.symm.toMonoidHom).map K.subtype :
      Subgroup Y) : Set Y) := by
  intro t ht
  exact mem_normalizer_pull e (he2_map_Y2_of_mem hl e he t ht)

theorem he2_card_sup {Y J : Type} [Group Y] [Finite Y] [Group J] [Finite J] {K S : Subgroup Y}
    [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S) :
    Nat.card ↥(S ⊔ ((hl.Y 2).map e.symm.toMonoidHom).map K.subtype) = 9 * Nat.card S := by
  have hSc : Nat.card ↥hl.S = 1024 := by
    rw [← Y0_eq_S hl, card_Y_idx hl (by norm_num)]; norm_num [heIdx]
  obtain ⟨_, -, -, -, -, rfl, h⟩ := exists_overgroup_of_invariant_data e he (hl.S_le_Y 2) 9
    (by rw [card_Y2 hl, hSc]) (he2_map_Y2_of_mem hl e he)
  exact h

theorem he2_lt_sup {Y J : Type} [Group Y] [Finite Y] [Group J] [Finite J] {K S : Subgroup Y}
    [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S) :
    S < S ⊔ ((hl.Y 2).map e.symm.toMonoidHom).map K.subtype := by
  refine lt_of_le_of_ne le_sup_left fun hEq => ?_
  have h := he2_card_sup hl e he
  rw [← hEq] at h
  have : 0 < Nat.card S := Nat.card_pos
  omega

theorem he2_calNIn_sup {Y J : Type} [Group Y] [Finite Y] [Group J] [Finite J] {K S : Subgroup Y}
    [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S) {s : Y} (hsS : s ∈ S)
    (hswap : (hl.Y 3).map (autK e s).toMonoidHom = hl.Y 4) :
    calNIn (S ⊔ ((hl.Y 2).map e.symm.toMonoidHom).map K.subtype) S = {S} := by
  classical
  set P : Subgroup Y := ((hl.Y 2).map e.symm.toMonoidHom).map K.subtype with hP
  have hSinv : ∀ t ∈ S, hl.S.map (autK e t).toMonoidHom = hl.S := he2_map_S_of_mem hl e he
  have h4 : (hl.Y 4).map (autK e s).toMonoidHom = hl.Y 3 := by
    rcases aut_Y34 hl (hSinv s hsS) with ⟨h3, -⟩ | ⟨-, h4⟩
    · exact absurd (h3.symm.trans hswap) (Y3_ne_Y4 hl)
    · exact h4
  have hY1Y6 : (hl.Y 1).map (autK e s).toMonoidHom = hl.Y 6 :=
    map_Y1_of_swaps_Y3 hl (hSinv s hsS) hswap h4
  have hSKleP : S ⊓ K ≤ P := by
    rw [hP]
    exact (le_pull_iff e inf_le_right).mpr (he ▸ hl.S_le_Y 2)
  have hforward : ∀ X : Subgroup Y, X ∈ calNIn (S ⊔ P) S → X = S := by
    intro X hX
    obtain ⟨hSX, hXlt, -⟩ := hX
    have hsX : s ∈ X := hSX hsS
    have hXKleP : X ⊓ K ≤ P := by
      intro x hx
      have hxSP : x ∈ S ⊔ P := hXlt.le hx.1
      change x ∈ (↑(S ⊔ P) : Set Y) at hxSP
      rw [Subgroup.coe_mul_of_left_le_normalizer_right S P
        (he2_le_normalizer_pull hl e he)] at hxSP
      obtain ⟨a, haS, b, hbP, hab⟩ := hxSP
      have hbK : b ∈ K := pull_le e (hl.Y 2) hbP
      have haK : a ∈ K := by
        have hae : a = x * b⁻¹ := by rw [← hab]; group
        rw [hae]
        exact K.mul_mem hx.2 (K.inv_mem hbK)
      have haP : a ∈ P := hSKleP ⟨haS, haK⟩
      rw [← hab]
      exact P.mul_mem haP hbP
    set R : Subgroup J := ((X ⊓ K).subgroupOf K).map e.toMonoidHom with hR
    have hSR : hl.S ≤ R := by
      rw [hR, ← he]
      exact Subgroup.map_mono fun x hx => ⟨hSX hx.1, hx.2⟩
    have hRY : R ≤ hl.Y 2 := by
      rw [hR, ← map_pull e (hl.Y 2)]
      exact Subgroup.map_mono fun x hx => hXKleP hx
    have hRne : R ≠ ⊤ := by
      intro htop
      have hY2top : hl.Y 2 = ⊤ := top_le_iff.mp (htop ▸ hRY)
      have hcard := congrArg (fun H : Subgroup J => Nat.card ↥H) hY2top
      rw [card_Y2 hl, card_top hl] at hcard
      norm_num at hcard
    obtain ⟨j, hj, hRj⟩ := (hl.complete R hSR).resolve_right hRne
    have hj2 : 2 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hRj ▸ hRY)
    have hαR : R.map (autK e s).toMonoidHom = R := by
      have hnorm : s ∈ Subgroup.normalizer ((X ⊓ K : Subgroup Y) : Set Y) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨hyX, hyK⟩
          exact ⟨X.mul_mem (X.mul_mem hsX hyX) (X.inv_mem hsX),
            ‹K.Normal›.conj_mem y hyK s⟩
        · rintro ⟨hyX, hyK⟩
          have e : y = s⁻¹ * (s * y * s⁻¹) * s := by group
          refine ⟨?_, ?_⟩
          · rw [e]
            exact X.mul_mem (X.mul_mem (X.inv_mem hsX) hyX) hsX
          · rw [e]
            simpa using ‹K.Normal›.conj_mem (s * y * s⁻¹) hyK s⁻¹
      rw [hR]
      exact map_autK_of_mem_normalizer' e inf_le_right hnorm
    rcases key_he_caseB_two ⟨j, hj⟩ hj2 with rfl | rfl | rfl | rfl
    · have hXK : X ⊓ K = S ⊓ K := by
        have h1 : (X ⊓ K).subgroupOf K = (S ⊓ K).subgroupOf K := by
          apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
          rw [← hR, hRj, Y0_eq_S hl]
          exact he.symm
        have h2 := Subgroup.subgroupOf_inj.mp h1
        rwa [inf_of_le_left inf_le_right, inf_of_le_left inf_le_right] at h2
      refine le_antisymm ?_ hSX
      intro x hx
      have hxSP : x ∈ S ⊔ P := hXlt.le hx
      change x ∈ (↑(S ⊔ P) : Set Y) at hxSP
      rw [Subgroup.coe_mul_of_left_le_normalizer_right S P
        (he2_le_normalizer_pull hl e he)] at hxSP
      obtain ⟨a, haS, b, hbP, hab⟩ := hxSP
      have hbK : b ∈ K := pull_le e (hl.Y 2) hbP
      have hbX : b ∈ X := by
        have hbe : b = a⁻¹ * x := by rw [← hab]; group
        rw [hbe]
        exact X.mul_mem (X.inv_mem (hSX haS)) hx
      have hbSK : b ∈ S ⊓ K := hXK ▸ ⟨hbX, hbK⟩
      rw [← hab]
      exact S.mul_mem haS hbSK.1
    · have hαY1 : (hl.Y 1).map (autK e s).toMonoidHom = hl.Y 1 := by
        simpa only [hRj] using hαR
      have h16 : hl.Y 1 = hl.Y 6 := hαY1.symm.trans hY1Y6
      exact absurd h16 fun h => Y_not_le hl (j := 1) (jj := 6) (by norm_num) (by norm_num)
        (by decide) h.le
    · have hPK : P ≤ K := pull_le e (hl.Y 2)
      have hXK : X ⊓ K = P := by
        have h1 : (X ⊓ K).subgroupOf K = P.subgroupOf K := by
          apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
          rw [← hR, hRj, hP, map_pull e (hl.Y 2)]
        have h2 := Subgroup.subgroupOf_inj.mp h1
        rwa [inf_of_le_left inf_le_right, inf_of_le_left hPK] at h2
      have hPX : P ≤ X := hXK ▸ inf_le_left
      exact absurd (le_antisymm hXlt.le (sup_le hSX hPX)) hXlt.ne
    · have hαY6 : (hl.Y 6).map (autK e s).toMonoidHom = hl.Y 6 := by
        simpa only [hRj] using hαR
      have h16 : hl.Y 1 = hl.Y 6 :=
        Subgroup.map_injective (autK e s).injective (hY1Y6.trans hαY6.symm)
      exact absurd h16 fun h => Y_not_le hl (j := 1) (jj := 6) (by norm_num) (by norm_num)
        (by decide) h.le
  have hlt : S < S ⊔ P := he2_lt_sup hl e he
  ext X
  constructor
  · exact hforward X
  · intro hX
    rw [Set.mem_singleton_iff] at hX
    rw [hX]
    refine ⟨le_rfl, hlt, ?_⟩
    intro M hSM hMle
    by_contra hne
    have hMlt : M < S ⊔ P := lt_of_le_of_ne hMle hne
    obtain ⟨Z, hZ, hMZ⟩ := exists_mem_calNIn_of_lt hSM.le hMlt
    have hZeq : Z = S := hforward Z hZ
    exact absurd (hMZ.trans hZeq.le) (not_le_of_gt hSM)

theorem he2_caseB_two {Y J : Type} [Group Y] [Finite Y] [Group J] [Finite J]
    {K S : Subgroup Y} [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {s : Y} (hsS : s ∈ S)
    (hswap : (hl.Y 3).map (autK e s).toMonoidHom = hl.Y 4) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 1
      (S ⊔ ((hl.Y 2).map e.symm.toMonoidHom).map K.subtype) := by
  classical
  set P : Subgroup Y := ((hl.Y 2).map e.symm.toMonoidHom).map K.subtype with hP
  have hcalN : calNIn (S ⊔ P) S = {S} := he2_calNIn_sup hl e he hsS hswap
  have hS' : CFSG.Quasithin.IsSylowIn 2 S ⊤ := hS
  have hSyl : CFSG.Quasithin.IsSylowIn 2 S (S ⊔ P) :=
    isSylowIn_of_le_of_le hS' le_sup_left le_top
  have hsol : Group.IsSolvable ↥(S ⊔ P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS.2.1
    refine CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_card_two_three
      (a := k) (b := 2) ?_
    rw [he2_card_sup hl e he, hk]
    ring
  exact inFSq_one_of_isSolvable_of_calNIn hSyl hcalN hsol

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
