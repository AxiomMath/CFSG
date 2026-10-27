module

public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentGroup
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lat
public import Certificates.Data.J4ZCent.Rho

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat CFSG.Blueprint
open CFSG.Quasithin.J4M2 (Phi Phi_injective RN_enc_Phi range_Phi MbarP Tbar mem_Tbar_iff chkT_tGens
  tGens_closure_le_M22 phiRN)
open scoped commutatorElement

theorem solvable_of_card_two_three {X : Type*} [Group X] [Finite X] {a b : ℕ}
    (h : Nat.card X = 2 ^ a * 3 ^ b) : Group.IsSolvable X := by
  let _ : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

section M22


theorem perfect_overgroups_M22 {Λ : Subgroup (Equiv.Perm (Fin 22))}
    (hΛM : Λ ≤ NativeSporadic.M22) (hperf : ⁅Λ, Λ⁆ = Λ) (hne : Λ ≠ ⊥)
    (hT : ∀ t ∈ Subgroup.closure {g | g ∈ cert.tGens}, ∀ x ∈ Λ, t * x * t⁻¹ ∈ Λ) :
    Λ = Subgroup.closure {g | g ∈ p5Gens} ∨ Λ = Subgroup.closure {g | g ∈ l6Gens} ∨
      Λ = NativeSporadic.M22 := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hTM := CFSG.Quasithin.J4M2.tGens_closure_le_M22
  have hTcard : Nat.card (Subgroup.closure {g | g ∈ cert.tGens}) = 128 := by
    rw [cert.card_t (rawIsEnc 22) hcl hsz]
    rfl
  have hTsolv : Group.IsSolvable (Subgroup.closure {g | g ∈ cert.tGens}) :=
    solvable_of_card_two_three (a := 7) (b := 0) (by rw [hTcard]; norm_num)
  have hYM : Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens} ≤
      Subgroup.closure {g | g ∈ cert.mGens} := by
    rw [mGens_closure]
    exact sup_le hΛM hTM
  obtain ⟨L, hL, hYL⟩ := cert.overgroups (rawIsEnc 22) hck _ le_sup_right hYM
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hL
  have hcardY : Nat.card ↥(Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens}) = cert.sizes.getD j 0 := by
    rw [hYL]
    exact cert.card_member_idx (rawIsEnc 22) hcl hsz j hj
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  rw [hlen] at hj
  have hsolv : Group.IsSolvable ↥(Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens}) → False :=
    fun hs => hne (eq_bot_of_perfect_of_le_solvable hs le_sup_left hperf)
  have hprod : ∀ p ∈ Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens},
      ∃ n ∈ Λ, ∃ k ∈ Subgroup.closure {g | g ∈ cert.tGens}, p = n * k :=
    fun p hp => (mem_sup_iff_of_conj hT).1 hp
  interval_cases j
  · exfalso
    apply hsolv
    have h128 : cert.sizes.getD 0 0 = 128 := rfl
    rw [h128] at hcardY
    exact solvable_of_card_two_three (a := 7) (b := 0) (by rw [hcardY]; norm_num)
  · exfalso
    apply hsolv
    have h384 : cert.sizes.getD 1 0 = 384 := rfl
    rw [h384] at hcardY
    exact solvable_of_card_two_three (a := 7) (b := 1) (by rw [hcardY]; norm_num)
  ·
    have h1920 : cert.sizes.getD 2 0 = 1920 := rfl
    rw [h1920] at hcardY
    have ha := List.all_eq_true.mp incl5 2 (by simp)
    simp only [h1920, bne_self_eq_false, Bool.false_or] at ha
    have hlen2 : 2 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[2] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen2
    have hAL : Subgroup.closure {g | g ∈ p5Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen2] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, -⟩ := ext5
    have hperfA : ⁅Subgroup.closure {g | g ∈ p5Gens}, Subgroup.closure {g | g ∈ p5Gens}⁆ =
        Subgroup.closure {g | g ∈ p5Gens} := perfect_of_perfOK (rawIsEnc 22) perf5_ok
    have hAY : Subgroup.closure {g | g ∈ p5Gens} ≤
        Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens} := by rw [hYL]; exact hAL
    have hAΛ : Subgroup.closure {g | g ∈ p5Gens} ≤ Λ :=
      le_of_perfect_of_solvable hTsolv hT (fun p hp => hprod p (hAY hp)) hperfA
    have hcomm : ⁅Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens},
        Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens}⁆ ≤ Subgroup.closure {g | g ∈ p5Gens} := by
      rw [hYL]
      exact commutator_le_of_card_eq_two_mul hAL (by rw [← hYL, hcardY, hAcard])
    have hΛA : Λ ≤ Subgroup.closure {g | g ∈ p5Gens} :=
      calc Λ = ⁅Λ, Λ⁆ := hperf.symm
        _ ≤ ⁅Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens},
            Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens}⁆ :=
          Subgroup.commutator_mono le_sup_left le_sup_left
        _ ≤ _ := hcomm
    exact Or.inl (le_antisymm hΛA hAΛ)
  ·
    have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
    rw [h5760] at hcardY
    have ha := List.all_eq_true.mp incl6 3 (by simp)
    simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
    have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
    have hAL : Subgroup.closure {g | g ∈ l6Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen3] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, -⟩ := ext6
    have hperfA : ⁅Subgroup.closure {g | g ∈ l6Gens}, Subgroup.closure {g | g ∈ l6Gens}⁆ =
        Subgroup.closure {g | g ∈ l6Gens} := perfect_of_perfOK (rawIsEnc 22) perf6_ok
    have hLA : Subgroup.closure {g | g ∈ l6Gens} =
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} :=
      Subgroup.eq_of_le_of_card_ge hAL (by
        rw [hAcard, ← hYL, hcardY])
    have hAY : Subgroup.closure {g | g ∈ l6Gens} ≤
        Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens} := by rw [hYL, ← hLA]
    have hAΛ : Subgroup.closure {g | g ∈ l6Gens} ≤ Λ :=
      le_of_perfect_of_solvable hTsolv hT (fun p hp => hprod p (hAY hp)) hperfA
    have hΛY : Λ ≤ Subgroup.closure {g | g ∈ l6Gens} := by
      rw [hLA, ← hYL]
      exact le_sup_left
    exact Or.inr (Or.inl (le_antisymm hΛY hAΛ))
  ·
    have h443520 : cert.sizes.getD 4 0 = 443520 := rfl
    rw [h443520] at hcardY
    have hM : Nat.card (Subgroup.closure {g | g ∈ cert.mGens}) = 443520 :=
      cert.card_m (rawIsEnc 22) hcl hsz
    have hYeq : Λ ⊔ Subgroup.closure {g | g ∈ cert.tGens} =
        Subgroup.closure {g | g ∈ cert.mGens} :=
      Subgroup.eq_of_le_of_card_ge hYM (by rw [hM, hcardY])
    rw [mGens_closure] at hYeq
    have hnorm : NativeSporadic.M22 ≤ Subgroup.normalizer (Λ : Set (Equiv.Perm (Fin 22))) := by
      rw [← hYeq]
      exact sup_le Subgroup.le_normalizer (le_normalizer_of_conj_mem hT)
    have hΛn : (Λ.subgroupOf NativeSporadic.M22).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hΛM).2 hnorm
    have hsimple : IsSimpleGroup NativeSporadic.M22 :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple (Λ.subgroupOf NativeSporadic.M22)
      hΛn with h | h
    · exfalso
      apply hne
      have := Subgroup.map_subgroupOf_eq_of_le hΛM
      rw [h, Subgroup.map_bot] at this
      exact this.symm
    · refine Or.inr (Or.inr (le_antisymm hΛM ?_))
      intro x hx
      have : (⟨x, hx⟩ : ↥NativeSporadic.M22) ∈ Λ.subgroupOf NativeSporadic.M22 := by
        rw [h]; trivial
      exact this
  · exfalso
    apply hsolv
    have h384 : cert.sizes.getD 5 0 = 384 := rfl
    rw [h384] at hcardY
    exact solvable_of_card_two_three (a := 7) (b := 1) (by rw [hcardY]; norm_num)

end M22

section Perm77


theorem perfect_overgroups_77 (hphi : ∀ g ∈ p5Gens, RN.enc (phiPerm g) = phiRN g)
    {Λ : Subgroup (Equiv.Perm (Fin 77))} (hΛP : Λ ≤ MbarP) (hperf : ⁅Λ, Λ⁆ = Λ) (hne : Λ ≠ ⊥)
    (hT : ∀ t ∈ Tbar, ∀ x ∈ Λ, t * x * t⁻¹ ∈ Λ) :
    Λ = Subgroup.closure {p | p ∈ p5Phi} ∨ Nat.card Λ = 5760 ∨ Nat.card Λ = 443520 := by
  classical
  let Λ' : Subgroup ↥NativeSporadic.M22 := Λ.comap Phi
  have hmapΛ : Λ'.map Phi = Λ := by
    rw [Subgroup.map_comap_eq, range_Phi]
    exact inf_eq_right.2 hΛP
  have hperf' : ⁅Λ', Λ'⁆ = Λ' := by
    apply Subgroup.map_injective Phi_injective
    rw [Subgroup.map_commutator, hmapΛ]
    exact hperf
  have hne' : Λ' ≠ ⊥ := by
    intro h
    apply hne
    rw [← hmapΛ, h, Subgroup.map_bot]
  let Λ'' : Subgroup (Equiv.Perm (Fin 22)) := Λ'.map NativeSporadic.M22.subtype
  have hΛ''M : Λ'' ≤ NativeSporadic.M22 := Subgroup.map_subtype_le _
  have hperf'' : ⁅Λ'', Λ''⁆ = Λ'' := by
    show ⁅Λ'.map NativeSporadic.M22.subtype, Λ'.map NativeSporadic.M22.subtype⁆ = _
    rw [← Subgroup.map_commutator, hperf']
  have hne'' : Λ'' ≠ ⊥ := fun h =>
    hne' ((Subgroup.map_eq_bot_iff_of_injective Λ' NativeSporadic.M22.subtype_injective).1 h)
  have hTmem : ∀ t ∈ Subgroup.closure {g | g ∈ cert.tGens}, ∀ htM : t ∈ NativeSporadic.M22,
      Phi ⟨t, htM⟩ ∈ Tbar := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem g hg =>
      intro htM
      refine (mem_Tbar_iff _).2 ?_
      rw [RN_enc_Phi]
      exact Std.HashSet.contains_iff_mem.1 (chkT_tGens g hg)
    | one =>
      intro htM
      exact (show (⟨1, htM⟩ : ↥NativeSporadic.M22) = 1 from rfl) ▸
        (map_one Phi ▸ Subgroup.one_mem _)
    | mul x y hx hy ihx ihy =>
      intro htM
      have hxM : x ∈ NativeSporadic.M22 := tGens_closure_le_M22 hx
      have hyM : y ∈ NativeSporadic.M22 := tGens_closure_le_M22 hy
      have : (⟨x * y, htM⟩ : ↥NativeSporadic.M22) = ⟨x, hxM⟩ * ⟨y, hyM⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ (ihx hxM) (ihy hyM)
    | inv x hx ih =>
      intro htM
      have hxM : x ∈ NativeSporadic.M22 := tGens_closure_le_M22 hx
      have : (⟨x⁻¹, htM⟩ : ↥NativeSporadic.M22) = (⟨x, hxM⟩)⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ (ih hxM)
  have hT'' : ∀ t ∈ Subgroup.closure {g | g ∈ cert.tGens}, ∀ x ∈ Λ'', t * x * t⁻¹ ∈ Λ'' := by
    intro t ht x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have htM : t ∈ NativeSporadic.M22 := tGens_closure_le_M22 ht
    refine ⟨⟨t, htM⟩ * y * ⟨t, htM⟩⁻¹, ?_, rfl⟩
    show Phi (⟨t, htM⟩ * y * ⟨t, htM⟩⁻¹) ∈ Λ
    rw [map_mul, map_mul, map_inv]
    exact hT _ (hTmem t ht htM) _ hy
  have hcardΛ : Nat.card Λ = Nat.card Λ'' := by
    rw [← hmapΛ, Subgroup.card_map_of_injective Phi_injective]
    exact (Subgroup.card_map_of_injective NativeSporadic.M22.subtype_injective).symm
  rcases perfect_overgroups_M22 hΛ''M hperf'' hne'' hT'' with h | h | h
  · left
    have hmemM : ∀ z ∈ Subgroup.closure {g | g ∈ p5Gens}, z ∈ NativeSporadic.M22 :=
      fun z hz => hΛ''M (h ▸ hz)
    have hgen : ∀ g ∈ p5Gens, ∀ hg : g ∈ NativeSporadic.M22, Phi ⟨g, hg⟩ = phiPerm g := by
      intro g hg hgM
      apply RN.enc_inj
      rw [RN_enc_Phi, hphi g hg]
    apply le_antisymm
    · rw [← hmapΛ]
      rintro _ ⟨y, hy, rfl⟩
      have hy'' : (y : Equiv.Perm (Fin 22)) ∈ Subgroup.closure {g | g ∈ p5Gens} :=
        h ▸ ⟨y, hy, rfl⟩
      have key : ∀ z ∈ Subgroup.closure {g | g ∈ p5Gens}, ∀ hz : z ∈ NativeSporadic.M22,
          Phi ⟨z, hz⟩ ∈ Subgroup.closure {p | p ∈ p5Phi} := by
        intro z hz
        induction hz using Subgroup.closure_induction with
        | mem g hg =>
          intro hgM
          rw [hgen g hg hgM]
          exact Subgroup.subset_closure (List.mem_map.2 ⟨g, hg, rfl⟩)
        | one =>
          intro hz1
          rw [show (⟨1, hz1⟩ : ↥NativeSporadic.M22) = 1 from rfl, map_one]
          exact Subgroup.one_mem _
        | mul x y hx hy ihx ihy =>
          intro hz1
          have : (⟨x * y, hz1⟩ : ↥NativeSporadic.M22) = ⟨x, hmemM x hx⟩ * ⟨y, hmemM y hy⟩ := rfl
          rw [this, map_mul]
          exact Subgroup.mul_mem _ (ihx _) (ihy _)
        | inv x hx ih =>
          intro hz1
          have : (⟨x⁻¹, hz1⟩ : ↥NativeSporadic.M22) = (⟨x, hmemM x hx⟩)⁻¹ := rfl
          rw [this, map_inv]
          exact Subgroup.inv_mem _ (ih _)
      exact key _ hy'' y.2
    · rw [Subgroup.closure_le]
      intro p hp
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hp
      have hgM : g ∈ NativeSporadic.M22 := hmemM g (Subgroup.subset_closure hg)
      rw [← hmapΛ, SetLike.mem_coe]
      refine ⟨⟨g, hgM⟩, ?_, hgen g hg hgM⟩
      show (⟨g, hgM⟩ : ↥NativeSporadic.M22) ∈ Λ'
      have : g ∈ Λ'' := h ▸ Subgroup.subset_closure hg
      obtain ⟨z, hz, hzg⟩ := this
      have hzz : z = ⟨g, hgM⟩ := Subtype.ext hzg
      rw [← hzz]
      exact hz
  · right; left
    rw [hcardΛ, h]
    exact (ext6).1
  · right; right
    rw [hcardΛ, h]
    exact CFSG.Sporadic.Mathieu.card_M22

end Perm77

end CFSG.Quasithin.J4ZCent
