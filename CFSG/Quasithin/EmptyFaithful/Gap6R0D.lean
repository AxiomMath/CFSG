module

public import CFSG.Quasithin.EmptyFaithful.Gap6R0A
public import CFSG.Quasithin.EmptyFaithful.Gap6R0B
public import CFSG.Quasithin.EmptyFaithful.Gap6R0C

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V]

section Restrict

variable {X : Subgroup (MulAut V)} {U : Subgroup V}

theorem le_stabSub_of_invariant (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : X ≤ stabSub U := by
  intro g hg u
  refine ⟨fun hu => ?_, fun hu => hU g hg u hu⟩
  have := hU g⁻¹ (X.inv_mem hg) (g u) hu
  simpa using this

@[expose] def restHom (U : Subgroup V) (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) :
    ↥X →* MulAut ↥U :=
  (resHom U).comp (Subgroup.inclusion (le_stabSub_of_invariant hU))

theorem restHom_eq_one_iff (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) {x : ↥X} :
    restHom U hU x = 1 ↔ ∀ u ∈ U, (x : MulAut V) u = u := by
  constructor
  · intro h u hu
    have h1 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : V)) h
    simp only [MulAut.one_apply] at h1
    exact h1
  · intro h
    ext u
    exact h u u.2

theorem restHom_range (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : (restHom U hU).range = autSub X U := by
  ext φ
  rw [MonoidHom.mem_range, mem_autSub]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, le_stabSub_of_invariant hU x.2⟩, x.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

end Restrict

section Transvection

variable [Finite V]

theorem exists_transvection_of_rk_comm (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {t : MulAut V}
    (hrk : rk ↥(commSub U (Subgroup.zpowers t)) = 1) :
    ∃ w : V, w ≠ 1 ∧ ∀ u ∈ U, t u = u ∨ t u = u * w := by
  have hcard : Nat.card ↥(commSub U (Subgroup.zpowers t)) = 2 := by
    rw [card_eq_two_pow hV, hrk]
    norm_num
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(commSub U (Subgroup.zpowers t)))).mp hcard
  refine ⟨(y : V), fun h => hy (Subtype.ext h), fun u hu => ?_⟩
  have hc : t u * u⁻¹ ∈ commSub U (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, hu, rfl⟩
  by_cases h1 : t u * u⁻¹ = 1
  · left
    exact mul_inv_eq_one.mp h1
  · right
    have := huniq ⟨t u * u⁻¹, hc⟩ (fun h => h1 (congrArg Subtype.val h))
    have h2 : t u * u⁻¹ = (y : V) := congrArg Subtype.val this
    calc t u = (t u * u⁻¹) * u := by group
      _ = (y : V) * u := by rw [h2]
      _ = u * y := mul_comm _ _

end Transvection

section Claim

variable [Finite V] {X Tb : Subgroup (MulAut V)}

theorem claimA2 (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X) (hO2 : pCoreOf 2 X = ⊥)
    (hsyl : Tb ∈ sylow2Of X)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    {t : MulAut V} (ht : t ∈ Jhat X) (ht2 : t ^ 2 = 1)
    (hμ : rk ↥(commV (fittingOf (Jhat X))) =
      rk ↥(commV (fittingOf (Jhat X)) ⊓ fixV (Subgroup.zpowers t)) + 1) :
    ∀ c ∈ fixV (fittingOf (Jhat X)), t c = c := by
  set J : Subgroup (MulAut V) := Jhat X with hJ
  set F : Subgroup (MulAut V) := fittingOf J with hF
  have hJX : J ≤ X := Jhat_le X
  have htX : t ∈ X := hJX ht
  obtain ⟨hsup, hinf⟩ := commV_sup_fixV hV hO2
  have hV₀ : ∀ g ∈ X, ∀ v ∈ commV F, g v ∈ commV F := fun g hg v hv => apply_mem_commV_F hg hv
  have hC : ∀ g ∈ X, ∀ v ∈ fixV F, g v ∈ fixV F := fun g hg v hv => apply_mem_fixV_F hg hv
  have htz : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ commV F, x w ∈ commV F := fun x hx w hw => by
    have hxX : x ∈ X := (Subgroup.zpowers_le.mpr htX) hx
    exact hV₀ x hxX w hw
  have hcomm1 : rk ↥(commSub (commV F) (Subgroup.zpowers t)) = 1 := by
    have := rk_commSub_add_rk_inf_fixV htz
    omega
  obtain ⟨w, hw1, hw⟩ := exists_transvection_of_rk_comm hV hcomm1
  have hwV₀ : w ∈ commV F := by
    by_contra hwn
    have hfixall : ∀ v ∈ commV F, t v = v := by
      intro v hv
      rcases hw v hv with h | h
      · exact h
      · exfalso
        apply hwn
        have : w = v⁻¹ * t v := by rw [h]; group
        rw [this]
        exact (commV F).mul_mem ((commV F).inv_mem hv) (hV₀ t htX v hv)
    have h0 : rk ↥(commSub (commV F) (Subgroup.zpowers t)) = 0 := by
      have : commSub (commV F) (Subgroup.zpowers t) = ⊥ :=
        commSub_eq_bot_iff.mpr fun v hv => mem_fixV_zpowers_iff.mpr (hfixall v hv)
      rw [this]
      exact rk_bot
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm_inf : commV F ⊓ fixV F = ⊥ := hinf
  have hO₀ : pCoreOf 2 (restHom (commV F) hV₀ : ↥X →* MulAut ↥(commV F)).range = ⊥ := by
    rw [restHom_range]
    exact pCoreOf_two_autSub_eq_bot hsyl hgen (U := fixV F) (W := commV F)
      (by rw [sup_comm]; exact hsup) (by rw [inf_comm]; exact hinf) hC hV₀
  have hOC : CFSG.pCore 2 ↥(restHom (fixV F) hC : ↥X →* MulAut ↥(fixV F)).range = ⊥ := by
    have h1 : pCoreOf 2 (autSub X (fixV F)) = ⊥ :=
      pCoreOf_two_autSub_eq_bot hsyl hgen (U := commV F) (W := fixV F) hsup hinf hV₀ hC
    rw [restHom_range]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (autSub X (fixV F)).subtype_injective).mp h1
  have hJn : ((Jhat X).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_Jhat g.2 hn
    simpa using this
  have hfaith : ∀ j ∈ (Jhat X).subgroupOf X, restHom (commV F) hV₀ j = 1 → j = 1 := by
    intro j hj hj1
    apply Subtype.ext
    exact eq_one_of_fix_commV hV hsolv hO2 (Subgroup.mem_subgroupOf.mp hj)
      ((restHom_eq_one_iff hV₀).mp hj1)
  have hFN : ∀ N : Subgroup ↥X, N ≤ (Jhat X).subgroupOf X → N.Normal → IsPGroup 3 ↥N →
      N ≤ (restHom (fixV F) hC).ker := by
    intro N hNJ hNn hN3
    set N' : Subgroup (MulAut V) := N.map X.subtype with hN'
    have hN'J : N' ≤ Jhat X := by
      rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hNJ hn)
    have hN'3 : IsPGroup 3 ↥N' :=
      hN3.of_equiv (Subgroup.equivMapOfInjective N X.subtype X.subtype_injective)
    have hN'n : ∀ x ∈ Jhat X, ∀ g ∈ N', x * g * x⁻¹ ∈ N' := by
      rintro x hx _ ⟨n, hn, rfl⟩
      have hxX : x ∈ X := hJX hx
      refine ⟨⟨x, hxX⟩ * n * ⟨x, hxX⟩⁻¹, hNn.conj_mem n hn _, ?_⟩
      simp
    have hN'F : N' ≤ fittingOf (Jhat X) := le_fittingOf_of_normal hN'J hN'3 hN'n
    intro n hn
    rw [MonoidHom.mem_ker, restHom_eq_one_iff hC]
    intro c hc
    exact hc _ (hN'F ⟨n, hn, rfl⟩)
  have key := claim_A2_abstract (Γ := ↥X) (W₀ := ↥(commV F)) (WC := ↥(fixV F))
    (fun v => Subtype.ext (by simpa using hV v)) (restHom (commV F) hV₀) (restHom (fixV F) hC)
    hsolv hO₀ hOC hJn hfaith hFN (t := ⟨t, htX⟩) (Subgroup.mem_subgroupOf.mpr ht)
    (Subtype.ext (by simpa using ht2))
    ⟨⟨w, hwV₀⟩, fun h => hw1 (congrArg Subtype.val h), fun v => by
      rcases hw v v.2 with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h⟩
  intro c hc
  have := (restHom_eq_one_iff hC).mp key c hc
  exact this

end Claim

end Gap6

end CFSG.Quasithin
