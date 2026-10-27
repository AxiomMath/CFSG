module

public import CFSG.Quasithin.Vol2.Ch3B513NCase245
public import CFSG.Quasithin.Vol2.Ch3B513NAltA
public import CFSG.Quasithin.Vol2.Ch3B513NAltC
public import CFSG.Quasithin.Background.B3ThreeCore

public section

namespace CFSG.Quasithin.B513N

open CFSG.Quasithin.B3

variable {W : Type} [CommGroup W] [Finite W] {n : ℕ} {L : Subgroup (MulAut W)}
  {π : LG n →* ↥L}

@[expose] def actW (π : LG n →* ↥L) : LG n →* MulAut W := L.subtype.comp π

omit [Finite W] in
theorem actW_mul_inv_mem (g : LG n) (w : W) : actW π g w * w⁻¹ ∈ commV L :=
  Subgroup.subset_closure ⟨_, (π g).2, w, rfl⟩

@[expose] noncomputable def actU (π : LG n →* ↥L) : LG n →* MulAut ↥(commV L) :=
  resAct (actW π) (commV L) (isInv_of_trivQ actW_mul_inv_mem)

omit [Finite W] in
theorem coe_actU (g : LG n) (u : ↥(commV L)) :
    ((actU π g u : ↥(commV L)) : W) = ((π g : ↥L) : MulAut W) (u : W) := rfl

omit [Finite W] in
theorem extBot_of_realizes (hW : ∀ w : W, w ^ 2 = 1)
    (hr : (FFModel.altDn n).RealizesVia L (commV L) (fixV L ⊓ commV L) π) :
    ∃ p : ↥(commV L) →* Mod.V n Mod.ut0,
      ExtBot n (actU π) ((fixV L ⊓ commV L).subgroupOf (commV L)) p := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hr
  refine ⟨dnEquiv.toMonoidHom.comp β, ⟨fun m => ?_, dnEquiv.surjective.comp hβs, fun g m => ?_,
    fun m => ?_, fun g a ha => ?_⟩⟩
  · apply Subtype.ext
    simpa using hW m
  · obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β m)
    have hgm : ((π g : ↥L) : MulAut W) (m : W) ∈ commV L := (actU π g m).2
    have hx' : (FFModel.altDn n).act g (x : (FFModel.altDn n).Amb) ∈ (FFModel.altDn n).sec :=
      hsec g x x.2
    have h1 := hβe g m x hgm hx' hx.symm
    have h2 : actU π g m = ⟨((π g : ↥L) : MulAut W) (m : W), hgm⟩ := Subtype.ext rfl
    have h3 : β (actU π g m) = QuotientGroup.mk ⟨(FFModel.altDn n).act g x, hx'⟩ := by
      rw [h2]
      exact h1
    show dnEquiv (β (actU π g m)) = actL n Mod.ut0 g (dnEquiv (β m))
    rw [h3, ← hx, dnEquiv_mk_act]
  · show dnEquiv (β m) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, hβk, Subgroup.mem_subgroupOf]
  · apply Subtype.ext
    exact (Subgroup.mem_subgroupOf.1 ha).1 _ (π g).2

omit [Finite W] in
theorem commG_actU_eq_top (hπ : Function.Surjective π)
    (hcomm : XMod.commOf ↥L (commV L) = commV L) : commG (actU π) = ⊤ := by
  have hle : commV L ≤ (commG (actU π)).map (commV L).subtype := by
    conv_lhs => rw [← hcomm]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨l, u, hu, rfl⟩
    obtain ⟨g, rfl⟩ := hπ l
    refine ⟨actU π g ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(commV L))⁻¹, mul_inv_mem_commG g _, ?_⟩
    rfl
  rw [eq_top_iff]
  intro u _
  obtain ⟨u', hu', hu'u⟩ := hle u.2
  have : u' = u := Subtype.ext hu'u
  rw [← this]
  exact hu'

theorem exists_modIso (hW : ∀ w : W, w ^ 2 = 1) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (hr : (FFModel.altDn n).RealizesVia L (commV L) (fixV L ⊓ commV L) π)
    (hcomm : XMod.commOf ↥L (commV L) = commV L) :
    ∃ k, (k = Mod.u0 ∨ k = Mod.ut0) ∧ ∃ Φ : ↥(commV L) ≃* Mod.V n k,
      IsModIso (actU π) (actL n k) Φ ∧ (ZeroClass (actL n k) ∨ TwoClass (actL n k) (d0 n k)) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨p, E⟩ := extBot_of_realizes hW hr
  have hA : (fixV L ⊓ commV L).subgroupOf (commV L) ≤ commG (actU π) := by
    rw [commG_actU_eq_top hr.1 hcomm]
    exact le_top
  have hbot : (fixV L ⊓ commV L).subgroupOf (commV L) = ⊥ →
      ∃ Φ : ↥(commV L) ≃* Mod.V n Mod.ut0, IsModIso (actU π) (actL n Mod.ut0) Φ := by
    intro h0
    have hinj : Function.Injective p := by
      rw [injective_iff_map_eq_one]
      intro m hm
      have := (E.ker m).1 hm
      rw [h0, Subgroup.mem_bot] at this
      exact this
    exact ⟨MulEquiv.ofBijective p ⟨hinj, E.surj⟩, fun g m => E.equiv g m⟩
  rcases hn with h5 | h6 | h7 | h8
  · obtain ⟨Φ, hΦ⟩ := hbot (eq_bot_of_zeroClass hn5 E hA (H1_natural_odd (Or.inl h5)))
    exact ⟨Mod.ut0, Or.inr rfl, Φ, hΦ, Or.inl (H1_natural_odd (Or.inl h5))⟩
  · have hle := card_le_two_of_twoClass hn5 E hA (H1_natural_even (Or.inl h6))
    rcases Nat.lt_or_ge (Nat.card ↥((fixV L ⊓ commV L).subgroupOf (commV L))) 2 with h1 | h2
    · have hc1 : Nat.card ↥((fixV L ⊓ commV L).subgroupOf (commV L)) = 1 := by
        have := Nat.card_pos (α := ↥((fixV L ⊓ commV L).subgroupOf (commV L)))
        omega
      obtain ⟨Φ, hΦ⟩ := hbot (Subgroup.eq_bot_of_card_eq _ hc1)
      exact ⟨Mod.ut0, Or.inr rfl, Φ, hΦ, Or.inr (H1_natural_even (Or.inl h6))⟩
    · obtain ⟨Φ, hΦ⟩ := exists_iso_core hn5 (Or.inl h6) E hA (le_antisymm hle h2)
      exact ⟨Mod.u0, Or.inl rfl, Φ, hΦ, Or.inr (H1_core_even (Or.inl h6))⟩
  · obtain ⟨Φ, hΦ⟩ := hbot (eq_bot_of_zeroClass hn5 E hA (H1_natural_odd (Or.inr h7)))
    exact ⟨Mod.ut0, Or.inr rfl, Φ, hΦ, Or.inl (H1_natural_odd (Or.inr h7))⟩
  · have hle := card_le_two_of_twoClass hn5 E hA (H1_natural_even (Or.inr h8))
    rcases Nat.lt_or_ge (Nat.card ↥((fixV L ⊓ commV L).subgroupOf (commV L))) 2 with h1 | h2
    · have hc1 : Nat.card ↥((fixV L ⊓ commV L).subgroupOf (commV L)) = 1 := by
        have := Nat.card_pos (α := ↥((fixV L ⊓ commV L).subgroupOf (commV L)))
        omega
      obtain ⟨Φ, hΦ⟩ := hbot (Subgroup.eq_bot_of_card_eq _ hc1)
      exact ⟨Mod.ut0, Or.inr rfl, Φ, hΦ, Or.inr (H1_natural_even (Or.inr h8))⟩
    · obtain ⟨Φ, hΦ⟩ := exists_iso_core hn5 (Or.inr h8) E hA (le_antisymm hle h2)
      exact ⟨Mod.u0, Or.inl rfl, Φ, hΦ, Or.inr (H1_core_even (Or.inr h8))⟩

theorem toV_three_ne_one (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    (hk : k = Mod.u0 ∨ k = Mod.ut0) : toV n k 3 ≠ 1 := by
  have hW3 : inWk n k 3 = true := by
    rcases hk with rfl | rfl <;> rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel
  rw [Ne, toV_eq_one_iff hW3]
  rcases hk with rfl | rfl <;> rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

omit [CommGroup W] [Finite W] in
private theorem comm_aux {M : Type*} [CommGroup M] (A v C t : M) :
    A * v⁻¹ * (C * t⁻¹)⁻¹ = A * C⁻¹ * (v * t⁻¹)⁻¹ := by
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_comm, mul_left_comm]

theorem exists_inv_alt (hW : ∀ w : W, w ^ 2 = 1) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (hr : (FFModel.altDn n).RealizesVia L (commV L) (fixV L ⊓ commV L) π)
    (hcomm : XMod.commOf ↥L (commV L) = commV L) :
    ∃ a ∈ L, a ≠ 1 ∧ a ^ 2 = 1 ∧ Nat.card (commV (Subgroup.zpowers a)) ≤ 4 := by
  obtain ⟨k, hk, Φ, hΦ, hcls⟩ := exists_modIso hW hn hr hcomm
  set a₀ : LG n := a0 n (by omega) with ha₀
  set a : MulAut W := ((π a₀ : ↥L) : MulAut W) with ha
  have haL : a ∈ L := (π a₀).2
  have hΦcm : ∀ u : ↥(commV L),
      Φ (actU π a₀ u * u⁻¹) = actL n k a₀ (Φ u) * (Φ u)⁻¹ := fun u => by
    rw [map_mul, map_inv, hΦ]
  have key : ∀ w : W, ∃ u ∈ commV L, cmHom a w = cmHom a u := by
    intro w
    set d : LG n → ↥(commV L) := dsM (actW π) actW_mul_inv_mem w with hd_def
    have hd : IsDer (actU π) d := isDer_dsM _ _ w
    have hd' : IsDer (actL n k) (fun x => Φ (d x)) := hΦ.isDer hd
    obtain ⟨v', hv'⟩ : ∃ v' : Mod.V n k, Φ (d a₀) = actL n k a₀ v' * v'⁻¹ := by
      rcases hcls with hz | ht
      · obtain ⟨v, hv⟩ := hz _ hd'
        exact ⟨v, congrFun hv a₀⟩
      · rcases ht.2.2 _ hd' with ⟨v, hv⟩ | ⟨v, hv⟩
        · exact ⟨v, congrFun hv a₀⟩
        · have h1 : Φ (d a₀) * d0 n k a₀ = actL n k a₀ v * v⁻¹ := congrFun hv a₀
          have hd0 : d0 n k a₀ = actL n k a₀ (toV n k 17) * (toV n k 17)⁻¹ := d0_a0_eq hn hk
          rw [hd0] at h1
          have e := eq_mul_inv_of_mul_eq h1
          refine ⟨v * (toV n k 17)⁻¹, ?_⟩
          rw [map_mul, map_inv, e]
          exact comm_aux _ _ _ _
    refine ⟨(Φ.symm v' : W), (Φ.symm v').2, ?_⟩
    have h2 : d a₀ = actU π a₀ (Φ.symm v') * (Φ.symm v')⁻¹ := by
      apply Φ.injective
      rw [hv', hΦcm, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    exact h3
  set R : Subgroup W := (commV L).map (cmHom a) with hR
  have hRU : R ≤ commV L := by
    rintro _ ⟨u, -, rfl⟩
    exact cmHom_mem_commV haL u
  have hrange : commV (Subgroup.zpowers a) ≤ R := by
    refine (commV_zpowers_le_range a).trans ?_
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, hu, hwu⟩ := key w
    exact ⟨u, hu, hwu.symm⟩
  have hRcard : Nat.card R ≤ 4 := by
    let f : ↥R →* Mod.V n k := Φ.toMonoidHom.comp (Subgroup.inclusion hRU)
    have hf : Function.Injective f :=
      Φ.injective.comp (Subgroup.inclusion_injective hRU)
    have hcardR : Nat.card R = Nat.card f.range := (Nat.card_congr
      (MonoidHom.ofInjective hf).toEquiv)
    rw [hcardR]
    refine card_le_four_of_mem (by rcases hn with h | h | h | h <;> omega) k f.range ?_
    · rintro _ ⟨⟨x, u, hu, rfl⟩, rfl⟩
      refine ⟨Φ ⟨u, hu⟩, ?_⟩
      have e1 : (⟨cmHom a u, hRU ⟨u, hu, rfl⟩⟩ : ↥(commV L)) =
          actU π a₀ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(commV L))⁻¹ := Subtype.ext rfl
      show Φ ⟨cmHom a u, hRU ⟨u, hu, rfl⟩⟩ = _
      rw [e1, hΦcm]
      rfl
  refine ⟨a, haL, fun h1 => ?_, ?_, (Subgroup.card_le_of_le hrange).trans hRcard⟩
  ·
    apply toV_three_ne_one hn hk
    have h17 : actL n k a₀ (toV n k 17) = toV n k 17 := by
      rw [← MulEquiv.apply_symm_apply Φ (toV n k 17), ← hΦ]
      congr 1
      apply Subtype.ext
      rw [coe_actU]
      show a _ = _
      rw [h1]
      rfl
    have hd0 : d0 n k a₀ = actL n k a₀ (toV n k 17) * (toV n k 17)⁻¹ := d0_a0_eq hn hk
    rw [h17, mul_inv_cancel] at hd0
    have h3 : d0 n k a₀ = toV n k 3 := by
      show toV n k (actM n (tab (a0 n (by omega)).1) 1 ^^^ 1) = toV n k 3
      rw [actM_a0_one hn]
    rw [← h3, hd0]
  · rw [ha, ← Subgroup.coe_pow, ← map_pow, a0_sq, map_one, Subgroup.coe_one]

end CFSG.Quasithin.B513N
