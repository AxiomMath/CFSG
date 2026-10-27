module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple

public section

open scoped commutatorElement

open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents)

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace SchurReduction

section Cover

variable {Y Q : Type*} [Group Y] [Group Q]

@[expose] def derivedPreimage (π : Y →* Q) (J : Subgroup Q) : Subgroup Y :=
  ⁅J.comap π, J.comap π⁆

theorem derivedPreimage_le_comap (π : Y →* Q) (J : Subgroup Q) :
    derivedPreimage π J ≤ J.comap π :=
  Subgroup.commutator_le_self _

theorem map_derivedPreimage {π : Y →* Q} (hπ : Function.Surjective π) {J : Subgroup Q}
    (hJ : ⁅J, J⁆ = J) : (derivedPreimage π J).map π = J := by
  rw [derivedPreimage, Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ, hJ]

theorem exists_mul_of_mem_comap {π : Y →* Q} (hπ : Function.Surjective π) {J : Subgroup Q}
    (hJ : ⁅J, J⁆ = J) {x : Y} (hx : x ∈ J.comap π) :
    ∃ k ∈ derivedPreimage π J, ∃ z ∈ π.ker, k * z = x := by
  have h : π x ∈ (derivedPreimage π J).map π := by
    rw [map_derivedPreimage hπ hJ]
    exact hx
  obtain ⟨k, hk, hkx⟩ := h
  refine ⟨k, hk, k⁻¹ * x, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]

theorem commutator_derivedPreimage {π : Y →* Q} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) {J : Subgroup Q} (hJ : ⁅J, J⁆ = J) :
    ⁅derivedPreimage π J, derivedPreimage π J⁆ = derivedPreimage π J := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨k, hk, z, hz, rfl⟩ := exists_mul_of_mem_comap hπ hJ hx
  obtain ⟨k', hk', z', hz', rfl⟩ := exists_mul_of_mem_comap hπ hJ hy
  rw [CFSG.SectionRank.commutatorElement_mul_mem_center k k' (hker hz) (hker hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

@[expose] def derivedPreimageHom (π : Y →* Q) (J : Subgroup Q) :
    ↥(derivedPreimage π J) →* ↥J :=
  (π.comp (derivedPreimage π J).subtype).codRestrict J fun x => derivedPreimage_le_comap π J x.2

theorem coe_derivedPreimageHom (π : Y →* Q) (J : Subgroup Q) (x : derivedPreimage π J) :
    ((derivedPreimageHom π J x : J) : Q) = π x :=
  rfl

theorem mem_ker_derivedPreimageHom {π : Y →* Q} {J : Subgroup Q} {x : derivedPreimage π J} :
    x ∈ (derivedPreimageHom π J).ker ↔ (x : Y) ∈ π.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem surjective_derivedPreimageHom {π : Y →* Q} (hπ : Function.Surjective π)
    {J : Subgroup Q} (hJ : ⁅J, J⁆ = J) : Function.Surjective (derivedPreimageHom π J) := by
  intro j
  have h : (j : Q) ∈ (derivedPreimage π J).map π := by
    rw [map_derivedPreimage hπ hJ]
    exact j.2
  obtain ⟨k, hk, hkj⟩ := h
  exact ⟨⟨k, hk⟩, Subtype.ext hkj⟩

theorem card_derivedPreimage {π : Y →* Q} (hπ : Function.Surjective π) {J : Subgroup Q}
    (hJ : ⁅J, J⁆ = J) (h : derivedPreimage π J ⊓ π.ker = ⊥) :
    Nat.card (derivedPreimage π J) = Nat.card J := by
  refine Nat.card_congr (Equiv.ofBijective (derivedPreimageHom π J)
    ⟨(injective_iff_map_eq_one _).mpr fun x hx => ?_, surjective_derivedPreimageHom hπ hJ⟩)
  have hx' : (x : Y) ∈ derivedPreimage π J ⊓ π.ker :=
    ⟨x.2, mem_ker_derivedPreimageHom.mp hx⟩
  rw [h, Subgroup.mem_bot] at hx'
  exact Subtype.ext hx'

theorem commutator_derivedPreimage_le_ker {π : Y →* Q} {J J' : Subgroup Q}
    (h : ∀ x ∈ J, ∀ y ∈ J', Commute x y) :
    ⁅derivedPreimage π J, derivedPreimage π J'⁆ ≤ π.ker := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have ha' := derivedPreimage_le_comap π J ha
  have hb' := derivedPreimage_le_comap π J' hb
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (h _ ha' _ hb').eq

theorem commutator_derivedPreimage_eq_bot {π : Y →* Q} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) {J J' : Subgroup Q} (hJ : ⁅J, J⁆ = J)
    (h : ∀ x ∈ J, ∀ y ∈ J', Commute x y) :
    ⁅derivedPreimage π J, derivedPreimage π J'⁆ = ⊥ := by
  have hZ : ⁅derivedPreimage π J, derivedPreimage π J'⁆ ≤ Subgroup.center Y :=
    (commutator_derivedPreimage_le_ker h).trans hker
  have hZ' : ⁅derivedPreimage π J', derivedPreimage π J⁆ ≤ Subgroup.center Y := by
    rw [Subgroup.commutator_comm]
    exact hZ
  have h1 : ⁅⁅derivedPreimage π J, derivedPreimage π J'⁆, derivedPreimage π J⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono_left hZ).trans (Subgroup.commutator_center_left _).le)
  have h2 : ⁅⁅derivedPreimage π J', derivedPreimage π J⁆, derivedPreimage π J⁆ = ⊥ :=
    le_bot_iff.mp
      ((Subgroup.commutator_mono_left hZ').trans (Subgroup.commutator_center_left _).le)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [commutator_derivedPreimage hπ hker hJ] at h3

theorem iSup_derivedPreimage_eq_top {π : Y →* Q} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (hY : Group.IsPerfect Y) {S : Set (Subgroup Q)}
    (hS : IsDirectProduct S ⊤) (hSp : ∀ J ∈ S, ⁅J, J⁆ = J) :
    (⨆ J : S, derivedPreimage π J.1) = ⊤ := by
  have h1 : (⨆ J : S, derivedPreimage π J.1).map π = ⊤ := by
    rw [Subgroup.map_iSup]
    have h : ∀ J : S, (derivedPreimage π J.1).map π = J.1 := fun J =>
      map_derivedPreimage hπ (hSp J.1 J.2)
    simp_rw [h]
    exact hS.iSup_eq
  have h2 : (⨆ J : S, derivedPreimage π J.1) ⊔ π.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, h1, Subgroup.comap_top]
  refine (CFSG.SectionRank.perfect_central_supplement hY).1 _ (eq_top_iff.mpr ?_)
  rw [← h2]
  exact sup_le_sup_left hker _

theorem ker_eq_bot_of_forall_inf_eq_bot [Finite Y] {π : Y →* Q} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (hY : Group.IsPerfect Y) {S : Set (Subgroup Q)}
    (hS : IsDirectProduct S ⊤) (hSp : ∀ J ∈ S, ⁅J, J⁆ = J)
    (h : ∀ J ∈ S, derivedPreimage π J ⊓ π.ker = ⊥) : π.ker = ⊥ := by
  classical
  have hQ : Finite Q := Finite.of_surjective π hπ
  have hSfin : Finite S := Set.toFinite S
  have : Fintype S := Fintype.ofFinite S
  have hcomm : Pairwise fun J J' : S => ∀ x y : Y, x ∈ derivedPreimage π J.1 →
      y ∈ derivedPreimage π J'.1 → Commute x y := by
    intro J J' hne x y hx hy
    have hne' : J.1 ≠ J'.1 := fun h => hne (Subtype.ext h)
    have h0 := commutator_derivedPreimage_eq_bot hπ hker (hSp J.1 J.2)
      (hS.commute J.1 J.2 J'.1 J'.2 hne')
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  let Φ : (∀ J : S, derivedPreimage π J.1) →* Y :=
    Subgroup.noncommPiCoprod (H := fun J : S => derivedPreimage π J.1) hcomm
  have hΦ : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]
    exact iSup_derivedPreimage_eq_top hπ hker hY hS hSp
  have h1 : Nat.card Y ≤ ∏ J : S, Nat.card J.1 := by
    calc Nat.card Y ≤ Nat.card (∀ J : S, derivedPreimage π J.1) :=
          Nat.card_le_card_of_surjective Φ hΦ
      _ = ∏ J : S, Nat.card (derivedPreimage π J.1) := Nat.card_pi
      _ = ∏ J : S, Nat.card J.1 :=
          Finset.prod_congr rfl fun J _ => card_derivedPreimage hπ (hSp J.1 J.2) (h J.1 J.2)
  have h2 : Nat.card Q = ∏ J : S, Nat.card J.1 := by
    calc Nat.card Q = Nat.card (⊤ : Subgroup Q) := Subgroup.card_top.symm
      _ = Nat.card (∀ J : S, (J.1 : Subgroup Q)) := (Nat.card_congr hS.equiv.toEquiv).symm
      _ = ∏ J : S, Nat.card J.1 := Nat.card_pi
  have h3 : Nat.card Y = Nat.card Q * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have h4 : Nat.card Q * Nat.card π.ker ≤ Nat.card Q * 1 := by
    rw [← h3, mul_one, h2]
    exact h1
  exact (Subgroup.card_le_one_iff_eq_bot _).mp (Nat.le_of_mul_le_mul_left h4 hpos)

theorem exists_factor_central_cover_of_surjective {r : ℕ} [Finite Y] {π : Y →* Q}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y) (hr : IsPGroup r π.ker)
    (hker1 : π.ker ≠ ⊥) (hY : Group.IsPerfect Y) {S : Set (Subgroup Q)}
    (hS : IsDirectProduct S ⊤) (hSp : ∀ J ∈ S, Group.IsPerfect ↥J) :
    ∃ J ∈ S, ∃ K : Subgroup Y, ∃ ρ : ↥K →* ↥J,
      Group.IsPerfect ↥K ∧ Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center ↥K ∧ ρ.ker ≠ ⊥ ∧
        IsPGroup r ρ.ker := by
  have hSp' : ∀ J ∈ S, ⁅J, J⁆ = J := fun J hJ => Subgroup.isPerfect_iff.mp (hSp J hJ)
  have hex : ∃ J ∈ S, derivedPreimage π J ⊓ π.ker ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hker1 (ker_eq_bot_of_forall_inf_eq_bot hπ hker hY hS hSp' hcon)
  obtain ⟨J, hJ, hne⟩ := hex
  refine ⟨J, hJ, derivedPreimage π J, derivedPreimageHom π J,
    Subgroup.isPerfect_iff.mpr (commutator_derivedPreimage hπ hker (hSp' J hJ)),
    surjective_derivedPreimageHom hπ (hSp' J hJ), ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (mem_ker_derivedPreimageHom.mp hx)) g)
  · intro hbot
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hmem : (⟨x, hx.1⟩ : derivedPreimage π J) ∈ (derivedPreimageHom π J).ker :=
      mem_ker_derivedPreimageHom.mpr hx.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · intro g
    obtain ⟨k, hk⟩ := hr ⟨((g : derivedPreimage π J) : Y), mem_ker_derivedPreimageHom.mp g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h := congrArg (fun z : π.ker => (z : Y)) hk
    simpa using h

end Cover

theorem isPerfect_of_mem_simpleComponents_top {H : Type*} [Group H] {J : Subgroup H}
    (hJ : J ∈ simpleComponents (⊤ : Subgroup H)) : Group.IsPerfect ↥J := by
  obtain ⟨-, -, hs, x, hx, y, hy, hxy⟩ := hJ
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩).1.1

end SchurReduction

open SchurReduction

theorem exists_factor_central_cover {r : ℕ} {Y : Type*} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal] (hLc : L ≤ Subgroup.center Y) (hLr : IsPGroup r L)
    (hL1 : L ≠ ⊥) (hY : Group.IsPerfect Y) (hss : IsSemisimple (⊤ : Subgroup (Y ⧸ L))) :
    ∃ J ∈ lcalOf (Y ⧸ L), ∃ K : Subgroup Y, ∃ ρ : ↥K →* ↥J,
      Group.IsPerfect ↥K ∧ Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center ↥K ∧ ρ.ker ≠ ⊥ ∧
        IsPGroup r ρ.ker := by
  have hker : (QuotientGroup.mk' L).ker = L := QuotientGroup.ker_mk' L
  obtain ⟨J, hJ, h⟩ := exists_factor_central_cover_of_surjective (r := r)
    (π := QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L) (by rwa [hker])
    (by rwa [hker]) (by rwa [hker]) hY hss fun J hJ => isPerfect_of_mem_simpleComponents_top hJ
  exact ⟨J, mem_lcalOf_of_mem_simpleComponents_top hJ, h⟩

end CFSG.SignalizerFunctorTheorem.McBride
