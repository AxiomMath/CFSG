module

public import CFSG.OddTranspositions.SixSixKernel
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.OddTranspositions.PSL2InvolutionTriple
public import CFSG.OddTranspositions.SixSix
public import CFSG.OddTranspositions.SixSixSimple

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem rad_of_normal (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} [N.Normal] :
    ∀ L : Subgroup N, L.Normal → Group.IsSolvable L → L = ⊥ := by
  intro L hLn hLs
  set R := CFSG.solvableRadical N
  have hchar : R.Characteristic :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_characteristic
  have hRn : (R.map N.subtype).Normal := ⟨fun x hx g => by
    obtain ⟨r, hr, rfl⟩ := hx
    let φ : MulAut N := MulAut.conjNormal g
    have hφ : φ r ∈ R := by
      have h := hchar.fixed φ
      have : r ∈ R.comap φ.toMonoidHom := by rw [h]; exact hr
      simpa using this
    exact ⟨φ r, hφ, by simp [φ, MulAut.conjNormal_apply]⟩⟩
  have hRs : Group.IsSolvable (R.map N.subtype) := by
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := N)
    let f := (R.equivMapOfInjective N.subtype N.subtype_injective).symm
    exact solvable_of_solvable_injective (f := f.toMonoidHom) f.injective
  have hR : R = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp (hrad _ hRn hRs)
  exact le_bot_iff.mp (hR ▸ CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hLn hLs)

theorem not_mem_centralizer_of_normal (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) {u : G} (hu : u ∈ D) :
    u ∉ Subgroup.centralizer (N : Set G) := by
  intro hu'
  have hD : D ⊆ Subgroup.centralizer (N : Set G) := by
    intro d hd
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hu hd)
    exact (Subgroup.normal_centralizer (H := N)).conj_mem u hu' c
  have htop : Subgroup.centralizer (N : Set G) = ⊤ := by
    rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]; exact hD
  have hcomm : ∀ a b : N, a * b = b * a := by
    intro a b
    have hb : (b : G) ∈ Subgroup.centralizer (N : Set G) := htop ▸ Subgroup.mem_top _
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hb a a.2)
  exact hN (hrad N inferInstance (isSolvable_of_comm hcomm))

theorem exists_conj_not_commute (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) {u : G} (hu : u ∈ D) :
    ∃ n ∈ N, ¬ Commute (n * u * n⁻¹) u := by
  classical
  by_contra h
  push Not at h
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set k : Set G := {x | ∃ n ∈ N, n * u * n⁻¹ = x}
  have hpair : k.Pairwise Commute := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩ -
    have h1 := (h (n⁻¹ * n') (N.mul_mem (N.inv_mem hn) hn')).conj n
    have e1 : n * (n⁻¹ * n' * u * (n⁻¹ * n')⁻¹) * n⁻¹ = n' * u * n'⁻¹ := by group
    rw [e1] at h1
    exact h1.symm
  set E := Subgroup.closure k
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    Set.centralizer_centralizer_comm_of_comm hpair x
      (Subgroup.closure_le_centralizer_centralizer k hx) y
      (Subgroup.closure_le_centralizer_centralizer k hy)
  have hEN : ∀ n ∈ N, ∀ x ∈ E, n * x * n⁻¹ ∈ E := by
    intro n hn x hx
    have hle : E ≤ E.comap (MulAut.conj n).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨m, hm, rfl⟩
      simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, SetLike.mem_coe]
      exact Subgroup.subset_closure ⟨n * m, N.mul_mem hn hm, by group⟩
    simpa [MulAut.conj_apply] using hle hx
  set L : Subgroup N := (E ⊓ N).subgroupOf N
  have hLn : L.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨by simpa using hEN g g.2 x hx.1, (g * x * g⁻¹).2⟩⟩
  have hLs : Group.IsSolvable L := isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (hEc _ (Subgroup.mem_subgroupOf.mp a.2).1 _
      (Subgroup.mem_subgroupOf.mp b.2).1))
  have hL := rad_of_normal hrad L hLn hLs
  have hnc := not_mem_centralizer_of_normal hS hrad hN hu
  rw [Subgroup.mem_centralizer_iff] at hnc
  push Not at hnc
  obtain ⟨n, hn, hnu⟩ := hnc
  have hxE : u * (n * u * n⁻¹) ∈ E :=
    E.mul_mem (Subgroup.subset_closure ⟨1, N.one_mem, by group⟩)
      (Subgroup.subset_closure ⟨n, hn, rfl⟩)
  have hxN : u * (n * u * n⁻¹) ∈ N := by
    have : u * (n * u * n⁻¹) = (u * n * u⁻¹) * n⁻¹ := by rw [huinv]; group
    rw [this]
    exact N.mul_mem (‹N.Normal›.conj_mem n hn u) (N.inv_mem hn)
  have hmem : (⟨_, hxN⟩ : N) ∈ L := Subgroup.mem_subgroupOf.mpr ⟨hxE, hxN⟩
  rw [hL, Subgroup.mem_bot] at hmem
  have h1 : u * (n * u * n⁻¹) = 1 := congrArg Subtype.val hmem
  apply hnu
  have h2 : n * u * n⁻¹ = u := by
    have := eq_inv_of_mul_eq_one_right h1
    rw [this, huinv]
  calc n * u = n * u * n⁻¹ * n := by group
    _ = u * n := by rw [h2]

theorem exists_conj_commute_ne (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) {u : G} (hu : u ∈ D) :
    ∃ n ∈ N, n * u * n⁻¹ ≠ u ∧ Commute (n * u * n⁻¹) u := by
  classical
  by_contra h
  push Not at h
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set X : Subgroup G := N ⊔ Subgroup.zpowers u
  letI : Fintype X := Fintype.ofFinite X
  have huX : u ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  set t : X := ⟨u, huX⟩
  have ht1 : t ≠ 1 := fun h1 => hS.oddT.ne_one hu (congrArg Subtype.val h1)
  have ht2 : t * t = 1 := Subtype.ext hu2
  have hiso : ∀ g : X, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_left).mp g.2
    have hzu : Commute z u := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.refl u).zpow_left i
    have hconj : (g : G) * u * (g : G)⁻¹ = y * u * y⁻¹ := by
      rw [← hyz]
      calc y * z * u * (y * z)⁻¹ = y * (z * u) * z⁻¹ * y⁻¹ := by group
        _ = y * (u * z) * z⁻¹ * y⁻¹ := by rw [hzu.eq]
        _ = y * u * y⁻¹ := by group
    apply Subtype.ext
    show (g : G) * u * (g : G)⁻¹ = u
    have hg' : ((g : G) * u * (g : G)⁻¹) * u = u * ((g : G) * u * (g : G)⁻¹) := by
      have := congrArg Subtype.val hg
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, t] at this
      exact this
    rw [hconj] at hg' ⊢
    by_contra hne
    exact h y hy hne hg'
  obtain ⟨O, hOn, hOodd, hO⟩ := CFSG.ZStar.glauberman_zStar X t ht1 ht2 hiso
  set O' : Subgroup G := O.map X.subtype
  set L : Subgroup N := (O' ⊓ N).subgroupOf N
  have hLn : L.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨⟨o, ho, hox⟩, -⟩ := hx
    refine ⟨⟨⟨g, Subgroup.mem_sup_left g.2⟩ * o * ⟨g, Subgroup.mem_sup_left g.2⟩⁻¹,
      hOn.conj_mem o ho _, ?_⟩, (g * x * g⁻¹).2⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hox ⊢
    rw [hox]⟩
  have hLodd : Odd (Nat.card L) := by
    have h1 : Nat.card L = Nat.card (O' ⊓ N :) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h2 : Nat.card (O' ⊓ N :) ∣ Nat.card O' := Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card O' = Nat.card O := Subgroup.card_map_of_injective X.subtype_injective
    rw [h1]
    exact Odd.of_dvd_nat hOodd (h3 ▸ h2)
  have hL := rad_of_normal hrad L hLn (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hLodd)
  apply not_mem_centralizer_of_normal hS hrad hN hu
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hmemO : n * u * n⁻¹ * u⁻¹ ∈ O' :=
    ⟨_, hO ⟨n, Subgroup.mem_sup_left hn⟩, by simp [t]⟩
  have hmemN : n * u * n⁻¹ * u⁻¹ ∈ N := by
    have : n * u * n⁻¹ * u⁻¹ = n * (u * n⁻¹ * u⁻¹) := by group
    rw [this]
    exact N.mul_mem hn (‹N.Normal›.conj_mem _ (N.inv_mem hn) u)
  have hmem : (⟨_, hmemN⟩ : N) ∈ L := Subgroup.mem_subgroupOf.mpr ⟨hmemO, hmemN⟩
  rw [hL, Subgroup.mem_bot] at hmem
  have h1 : n * u * n⁻¹ * u⁻¹ = 1 := congrArg Subtype.val hmem
  calc n * u = n * u * n⁻¹ * u⁻¹ * (u * n) := by group
    _ = u * n := by rw [h1, one_mul]

theorem centralizer_eq_bot_of_isSimpleGroup (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {M : Subgroup G} (hM : Asc72.IsMinimalNormal M) (hMs : IsSimpleGroup M) :
    Subgroup.centralizer (M : Set G) = ⊥ := by
  haveI : M.Normal := hM.1
  by_contra hC
  obtain ⟨u, hu⟩ := hS.nonempty
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  obtain ⟨m, hm, hne, hvu⟩ := exists_conj_commute_ne hS hrad hM.2.1 hu
  obtain ⟨c, hc, hxu⟩ := exists_conj_not_commute hS hrad hC hu
  set v := m * u * m⁻¹
  set x := c * u * c⁻¹
  have hv : v ∈ D := hS.normal m u hu
  have hx : x ∈ D := hS.normal c u hu
  have huvM : u * v ∈ M := by
    have : u * v = (u * m * u⁻¹) * m⁻¹ := by simp only [v, huinv]; group
    rw [this]; exact M.mul_mem (hM.1.conj_mem m hm u) (M.inv_mem hm)
  have hcuv : c * (u * v) * c⁻¹ = u * v := by
    rw [(Subgroup.mem_centralizer_iff.mp hc _ huvM).symm]; group
  have huv_comm : u * v = v * u := hvu.eq.symm
  have e1 : u * (u * v) * u⁻¹ = u * v := by
    rw [huinv]
    calc u * (u * v) * u = (u * u) * (v * u) := by group
      _ = u * v := by rw [hu2, one_mul, huv_comm]
  have hc' : c⁻¹ * (u * v) * c = u * v := by
    calc c⁻¹ * (u * v) * c = c⁻¹ * (c * (u * v) * c⁻¹) * c := by rw [hcuv]
      _ = u * v := by group
  have hconj : x * (u * v) * x⁻¹ = u * v := by
    calc x * (u * v) * x⁻¹ = c * (u * (c⁻¹ * (u * v) * c) * u⁻¹) * c⁻¹ := by
          simp only [x]; group
      _ = u * v := by rw [hc', e1, hcuv]
  have hxuv : Commute x (u * v) := mul_inv_eq_iff_eq_mul.mp hconj
  have huv1 : u * v ≠ 1 := fun h1 => hne (by
    have := eq_inv_of_mul_eq_one_right h1; rw [this, huinv])
  have huv2 : orderOf (u * v) = 2 := by
    refine orderOf_eq_prime ?_ huv1
    rw [sq]
    calc u * v * (u * v) = (u * u) * (v * v) := by
          rw [mul_assoc u v, ← mul_assoc v u v, ← huv_comm]; group
      _ = 1 := by rw [hu2, hS.oddT.mul_self_eq_one hv, one_mul]
  have hux : ¬ Commute u x := fun h => hxu h.symm
  have hodd : Odd (orderOf (u * x)) := hS.oddT.odd_of_not_commute hu hx hux
  have hcomm2 : Commute (u * v) (u * x) :=
    ((Commute.refl u).mul_left hvu).mul_right hxuv.symm
  have hvx : v * x = (u * v) * (u * x) := by
    calc v * x = (u * u) * v * x := by rw [hu2, one_mul]
      _ = u * (u * v) * x := by group
      _ = u * (v * u) * x := by rw [huv_comm]
      _ = (u * v) * (u * x) := by group
  have hcop : (orderOf (u * v)).Coprime (orderOf (u * x)) := by
    rw [huv2]; exact Nat.coprime_two_left.mpr hodd
  have hord : orderOf (v * x) = 2 * orderOf (u * x) := by
    rw [hvx, hcomm2.orderOf_mul_eq_mul_orderOf_of_coprime hcop, huv2]
  rcases hS.oddT.2 v hv x hx with h2 | h2
  · rw [hord] at h2
    have h1 : orderOf (u * x) = 1 := by
      have := Nat.le_of_dvd two_pos h2
      have hpos := orderOf_pos (u * x)
      omega
    rw [orderOf_eq_one_iff] at h1
    apply hux
    have : x = u⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, huinv]
  · rw [hord] at h2
    exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) h2

theorem blockKernel_eq_bot_of_simple_minimalNormal (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {M : Subgroup G} (hM : Asc72.IsMinimalNormal M) (hMs : IsSimpleGroup M)
    (hMc : Subgroup.centralizer (M : Set G) = ⊥) : blockKernel hC.alpha = ⊥ := by
  classical
  haveI : (blockKernel hC.alpha).Normal := blockKernel_normal hC.alpha
  by_contra hK
  haveI : M.Normal := hM.1
  have hMK : M ≤ blockKernel hC.alpha := le_blockKernel_of_ne_bot hC hrad hK hM
  have hMα : M ≤ Subgroup.normalizer hC.alpha := hMK.trans (blockKernel_le_normalizer hC)
  have hMcl := le_closure_alpha_of_le_normalizer hC hMs hMc hMα
  obtain ⟨b, hbD, hb⟩ := exists_mem_D_centralizes_alpha hC
  have hcl : Subgroup.closure hC.alpha ≤ Subgroup.centralizer {b} := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hb a ha).eq
  have hbM : b ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := hcl (hMcl hm)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  rw [hMc, Subgroup.mem_bot] at hbM
  exact hC.setup.oddT.ne_one hbD hbM

theorem sixSix_dichotomy_of_rad
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    (∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n)) ∨ FaithfulOnBlocks hC.alpha := by
  classical
  have hS := hC.setup
  obtain ⟨u, hu⟩ := hS.nonempty
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    apply hS.oddT.ne_one hu
    have : u ∈ (⊤ : Subgroup G) := Subgroup.mem_top u
    rwa [h, Subgroup.mem_bot] at this
  obtain ⟨M, -, hMmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) ⊤ ⟨inferInstance, htop⟩
  have hM : Asc72.IsMinimalNormal M := by
    refine ⟨hMmin.prop.1, hMmin.prop.2, fun N hN hNM => ?_⟩
    by_cases hN1 : N = ⊥
    · exact Or.inl hN1
    · exact Or.inr (le_antisymm hNM (hMmin.2 ⟨hN, hN1⟩ hNM))
  by_cases hMs : IsSimpleGroup M
  · refine Or.inr (faithfulOnBlocks_iff_blockKernel_eq_bot.mpr ?_)
    exact blockKernel_eq_bot_of_simple_minimalNormal hC hrad hM hMs
      (centralizer_eq_bot_of_isSimpleGroup hS hrad hM hMs)
  · exact Or.inl (exists_l2Wreath_of_not_isSimpleGroup_minimalNormal hC hrad hM hMs)

theorem exists_isMinimalNormal (h : (⊤ : Subgroup G) ≠ ⊥) :
    ∃ M : Subgroup G, Asc72.IsMinimalNormal M := by
  obtain ⟨M, -, hMmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) ⊤ ⟨inferInstance, h⟩
  refine ⟨M, hMmin.prop.1, hMmin.prop.2, fun N hN hNM => ?_⟩
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  · exact Or.inr (le_antisymm hNM (hMmin.2 ⟨hN, hN1⟩ hNM))

theorem faithfulOnBlocks_of_localSecond (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hL : LocalSecond D) :
    FaithfulOnBlocks hC.alpha := by
  have hS := hC.setup
  obtain ⟨u, hu⟩ := hS.nonempty
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    apply hS.oddT.ne_one hu
    have : u ∈ (⊤ : Subgroup G) := Subgroup.mem_top u
    rwa [h, Subgroup.mem_bot] at this
  obtain ⟨M, hM⟩ := exists_isMinimalNormal htop
  by_cases hMs : IsSimpleGroup M
  · exact faithfulOnBlocks_iff_blockKernel_eq_bot.mpr
      (blockKernel_eq_bot_of_simple_minimalNormal hC hrad hM hMs
        (centralizer_eq_bot_of_isSimpleGroup hS hrad hM hMs))
  · obtain ⟨W⟩ := nonempty_wreathData hS hrad hM hMs
    exact absurd hL (localSecond_fails_of_wreathData hS W)

end CFSG.OddTranspositions.QZ
