module

public import CFSG.Quasithin.H13.A6S13821zz23
public import CFSG.Quasithin.EmptyFaithful.S153LKsB
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.S153L

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem natural_su3_of_d3Std
    (hA21 : AsA21SQTKSection) (h42 : AsB42) (h45 : AsB45) (hD310 : D310)
    (hD : D3Std M Mp T L V) (hMp : Mp = L) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ))
    (hfaith : L ⊓ centSub V = ⊥) (hKs : KsCover ↥L)
    (hc : Nat.card ↥L = 5515776 ∨ Nat.card ↥L = 16547328) :
    T ≤ stabSub V ∧ BinaryNaturalSU3 L V (V ⊓ fixV L) 3 ∧ Nat.card ↥L = 16547328 := by
  rcases hD310 W M Mp T L V hD hMp hqM with hT | ⟨hfirst, -, -⟩
  · have hT' : T ≤ stabSub V := fun t ht => hT t ht
    obtain ⟨h1, h2⟩ :=
      natural_su3_of_types (typesFour_natW_of_stab hA21 h42 h45 hD hMp hT' hq hfaith hKs) hc
    exact ⟨hT', h1, h2⟩
  · exact (false_of_d310Two_card_su3 hc hfirst).elim

omit [Finite W] in
theorem faithful_of_simple_d3Std [Finite W] (hD : D3Std M Mp T L V) (hMp : Mp = L)
    (hs : IsSimpleGroup ↥L) : L ⊓ centSub V = ⊥ := by
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD.hyp
  obtain ⟨l₀, hl₀, v₀, hv₀, hne⟩ : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
    obtain ⟨w, hwV, hwf⟩ := IsConcreteLE.not_le_iff_exists.mp (not_le_of_gt hD.irrT.1.2.2.2.1)
    by_contra hcon
    push Not at hcon
    exact hwf ⟨hwV, fun a => hcon a (hMp ▸ a.2) w hwV⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resHomOn V hLs).ker with hk | hk
  · rw [eq_bot_iff]
    intro g hg
    have hmem : (⟨g, hg.1⟩ : ↥L) ∈ (resHomOn V hLs).ker := by
      rw [MonoidHom.mem_ker]
      ext u
      exact hg.2 u u.2
    rw [hk, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  · exfalso
    have hmem : (⟨l₀, hl₀⟩ : ↥L) ∈ (resHomOn V hLs).ker := by rw [hk]; trivial
    rw [MonoidHom.mem_ker] at hmem
    exact hne (congrArg (fun φ : MulAut ↥V => ((φ ⟨v₀, hv₀⟩ : ↥V) : W)) hmem)

omit [Finite W] in
theorem ksCover_of_isPSU38 {Y : Type} [Group Y] (hU : IsPSU 3 2 3 Y) : KsCover Y :=
  ⟨Y, inferInstance, ⊤, 3, (Subgroup.topEquiv (G := Y)).symm.toMonoidHom, le_rfl, ⟨1, rfl⟩,
    Or.inr (Or.inr (Or.inl (IsPSU.of_mulEquiv (Subgroup.topEquiv (G := Y)).symm hU))),
    (Subgroup.topEquiv (G := Y)).symm.surjective, fun x hx => by
      have hx1 : x = 1 := (Subgroup.topEquiv (G := Y)).symm.injective (by simpa using hx)
      rw [hx1]
      exact Subgroup.one_mem _⟩

theorem card_of_isPSU38 {Y : Type} [Group Y] (hU : IsPSU 3 2 3 Y) :
    Nat.card Y = 5515776 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight hU

theorem false_of_insp4_u38
    (hA21 : AsA21SQTKSection) (h42 : AsB42) (h45 : AsB45) (hD310 : D310)
    (hD : D3Std M Mp T L V) (hMp : Mp = L) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ))
    (hU : IsPSU 3 2 3 ↥L) : False := by
  have hs : IsSimpleGroup ↥L := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 3 hU).2
  have hc := card_of_isPSU38 hU
  obtain ⟨-, -, h⟩ := natural_su3_of_d3Std hA21 h42 h45 hD310 hD hMp hqM hq
    (faithful_of_simple_d3Std hD hMp hs) (ksCover_of_isPSU38 hU) (Or.inl hc)
  omega

end CFSG.Quasithin.H13.A6.A6S20
