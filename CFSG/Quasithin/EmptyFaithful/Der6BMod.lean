module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.EmptyFaithful.T1531O4Line

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.S1417

namespace Der6B

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem sup_stab (h : OfourStruct X L₁ L₂ t) {z : MulAut W} (hz : z ∈ L₁ ⊔ L₂) :
    (∀ u ∈ commV L₁, z u ∈ commV L₁) ∧ (∀ u ∈ commV L₂, z u ∈ commV L₂) :=
  ⟨fun u hu => (mem_stabSub.1 (h.sup_le_stab₁ hz) u).2 hu,
    fun u hu => (mem_stabSub.1 (h.sup_le_stab₂ hz) u).2 hu⟩

theorem eq_one_of_fix (h : OfourStruct X L₁ L₂ t) {z : MulAut W}
    (h₁ : ∀ u ∈ commV L₁, z u = u) (h₂ : ∀ u ∈ commV L₂, z u = u) : z = 1 := by
  ext w
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
  rw [map_mul, h₁ u₁ hu₁, h₂ u₂ hu₂]
  rfl

theorem exists_moved (h : OfourStruct X L₁ L₂ t) {z : MulAut W} (hz1 : z ≠ 1) :
    (∃ u ∈ commV L₁, z u * u⁻¹ ≠ 1) ∨ (∃ u ∈ commV L₂, z u * u⁻¹ ≠ 1) := by
  by_contra hcon
  push Not at hcon
  exact hz1 (eq_one_of_fix h (fun u hu => mul_inv_eq_one.mp (hcon.1 u hu))
    fun u hu => mul_inv_eq_one.mp (hcon.2 u hu))

theorem inf_sup_eq_bot_of_totSing (h : OfourStruct X L₁ L₂ t) {Y : Subgroup (MulAut W)}
    (h₁ : commV Y ⊓ commV L₁ = ⊥) (h₂ : commV Y ⊓ commV L₂ = ⊥) : Y ⊓ (L₁ ⊔ L₂) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzY, hzS⟩
  rw [Subgroup.mem_bot]
  by_contra hz1
  obtain ⟨hs₁, hs₂⟩ := sup_stab h hzS
  rcases exists_moved h hz1 with ⟨u, hu, hne⟩ | ⟨u, hu, hne⟩
  · have hm : z u * u⁻¹ ∈ commV Y ⊓ commV L₁ :=
      ⟨Subgroup.subset_closure ⟨z, hzY, u, rfl⟩,
        Subgroup.mul_mem _ (hs₁ u hu) (Subgroup.inv_mem _ hu)⟩
    rw [h₁, Subgroup.mem_bot] at hm
    exact hne hm
  · have hm : z u * u⁻¹ ∈ commV Y ⊓ commV L₂ :=
      ⟨Subgroup.subset_closure ⟨z, hzY, u, rfl⟩,
        Subgroup.mul_mem _ (hs₂ u hu) (Subgroup.inv_mem _ hu)⟩
    rw [h₂, Subgroup.mem_bot] at hm
    exact hne hm

theorem card_le_two_of_inf_sup (h : OfourStruct X L₁ L₂ t) {Y : Subgroup (MulAut W)} (hY : Y ≤ X)
    (hb : Y ⊓ (L₁ ⊔ L₂) = ⊥) : Nat.card Y ≤ 2 := by
  have h1 := h.relIndex_sup
  have h2 : (L₁ ⊔ L₂).relIndex Y ≤ (L₁ ⊔ L₂).relIndex X :=
    Subgroup.relIndex_le_of_le_right hY (by rw [h1]; norm_num)
  have h3 : (L₁ ⊔ L₂).relIndex Y = Nat.card Y := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hb, Subgroup.relIndex_bot_left]
  rw [h3, h1] at h2
  exact h2

theorem card_le_two_of_fix_line [Finite W] (h : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : T1531O4.IsLine (commV L₁) (commV L₂) E) {Y : Subgroup (MulAut W)} (hY : Y ≤ X)
    (hfix : ∀ y ∈ Y, ∀ e ∈ E, y e = e) : Nat.card Y ≤ 2 := by
  refine card_le_two_of_inf_sup h hY (eq_bot_iff.mpr ?_)
  rintro z ⟨hzY, hzS⟩
  rw [Subgroup.mem_bot]
  obtain ⟨hs₁, hs₂⟩ := sup_stab h hzS
  refine eq_one_of_fix h (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨y, hyU, hxy⟩ := T1531O4.exists_partner₂ h hE x
    have h1 := hfix z hzY _ hxy
    rw [map_mul] at h1
    have hxm : x ∈ commV L₁ := hx
    obtain ⟨e1, -⟩ := eq_of_mul_eq_of_inf_eq_bot h.inf (hs₁ x hxm) hxm (hs₂ y hyU) hyU h1
    exact e1
  · obtain ⟨x, hxU, hxy⟩ := T1531O4.exists_partner₁ h hE y
    have h1 := hfix z hzY _ hxy
    rw [map_mul] at h1
    obtain ⟨-, e2⟩ := eq_of_mul_eq_of_inf_eq_bot h.inf (hs₁ x hxU) hxU (hs₂ y hy) hy h1
    exact e2

theorem card_fixV_le_four_of_totSing [Finite W] (h : OfourStruct X L₁ L₂ t) {Y : Subgroup (MulAut W)}
    (hY : Y ≤ X) (hY1 : Y ≠ ⊥) (h₁ : commV Y ⊓ commV L₁ = ⊥) (h₂ : commV Y ⊓ commV L₂ = ⊥) :
    Nat.card ↥(fixV Y) ≤ 4 := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY1
  have hb := inf_sup_eq_bot_of_totSing h h₁ h₂
  have hxN : (x : MulAut W) ∉ L₁ ⊔ L₂ := fun hmem => hx1 (Subtype.ext (by
    have : (x : MulAut W) ∈ Y ⊓ (L₁ ⊔ L₂) := ⟨x.2, hmem⟩
    rw [hb, Subgroup.mem_bot] at this
    exact this))
  exact h.card_fixV_le_four_of_swap (hY x.2) hxN x.2

theorem mem_fixV_zpowers {x : MulAut W} {w : W} : w ∈ fixV (Subgroup.zpowers x) ↔ x w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

variable [Finite W]

omit [Finite W] in
theorem S_comm {T' : Subgroup (MulAut W)} {s₁ s₂ τ : MulAut W} {a₁ a₂ : W}
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) :
    ∀ x ∈ T' ⊓ (L₁ ⊔ L₂), ∀ y ∈ T' ⊓ (L₁ ⊔ L₂), x * y = y * x := by
  intro x hx y hy
  have e1 : s₁ * (s₁ * s₂) = s₂ := by rw [← mul_assoc, hF.s₁_sq, one_mul]
  have e2 : (s₁ * s₂) * s₁ = s₂ := by rw [hF.comm, mul_assoc, hF.s₁_sq, mul_one]
  have e3 : s₂ * (s₁ * s₂) = s₁ := by rw [hF.comm, ← mul_assoc, hF.s₂_sq, one_mul]
  have e4 : (s₁ * s₂) * s₂ = s₁ := by rw [mul_assoc, hF.s₂_sq, mul_one]
  rcases (hF.S_eq x).1 hx with h1 | h1 | h1 | h1 <;>
    rcases (hF.S_eq y).1 hy with h2 | h2 | h2 | h2 <;>
    rw [h1, h2] <;>
    first
      | rfl
      | simp only [one_mul, mul_one]
      | exact hF.comm
      | exact hF.comm.symm
      | rw [e1, e2]
      | rw [e3, e4]

theorem swap_conj (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X)
    {s₁ s₂ τ : MulAut W} {a₁ a₂ : W} (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂)
    {x : MulAut W} (hxT : x ∈ T') (hxS : x ∉ T' ⊓ (L₁ ⊔ L₂)) :
    x * s₁ * x⁻¹ = s₂ ∧ x * s₂ * x⁻¹ = s₁ ∧ x a₁ = a₂ ∧ x a₂ = a₁ := by
  have hw : x * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) :=
    (coset_of_relIndex_two (h.relIndex_S hT) hxT hF.τ_T
      (fun hτS => hF.τ_N hτS.2)).resolve_left hxS
  have c₂ : (x * τ⁻¹) * s₂ = s₂ * (x * τ⁻¹) := S_comm hF _ hw _ hF.sylow.s₂_mem_S
  have c₁ : (x * τ⁻¹) * s₁ = s₁ * (x * τ⁻¹) := S_comm hF _ hw _ hF.sylow.s₁_mem_S
  have hfa₁ : (x * τ⁻¹) a₁ = a₁ :=
    ((hF.sylow.fixS a₁).2 (Or.inr (Or.inl rfl))) _ hw
  have hfa₂ : (x * τ⁻¹) a₂ = a₂ :=
    ((hF.sylow.fixS a₂).2 (Or.inr (Or.inr (Or.inl rfl)))) _ hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc x * s₁ * x⁻¹ = (x * τ⁻¹) * (τ * s₁ * τ⁻¹) * (x * τ⁻¹)⁻¹ := by group
      _ = (x * τ⁻¹) * s₂ * (x * τ⁻¹)⁻¹ := by rw [hF.τs₁]
      _ = s₂ := by rw [c₂]; group
  · calc x * s₂ * x⁻¹ = (x * τ⁻¹) * (τ * s₂ * τ⁻¹) * (x * τ⁻¹)⁻¹ := by group
      _ = (x * τ⁻¹) * s₁ * (x * τ⁻¹)⁻¹ := by rw [hF.τs₂]
      _ = s₁ := by rw [c₁]; group
  · have : x a₁ = (x * τ⁻¹) (τ a₁) := by
      rw [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [this, hF.τa₁, hfa₂]
  · have : x a₂ = (x * τ⁻¹) (τ a₂) := by
      rw [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [this, hF.τa₂, hfa₁]

omit [Finite W] in
theorem swap_mem (h : OfourStruct X L₁ L₂ t) {x : MulAut W} (hxX : x ∈ X) (hxN : x ∉ L₁ ⊔ L₂)
    {u : W} (hu : u ∈ commV L₂) : x u ∈ commV L₁ := by
  rcases h.perm x hxX with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd ((h.mem_sup_iff hxX).2 fun u hu => OfourStruct.commV_apply_mem x L₁ L₁ h1 hu) hxN
  · exact OfourStruct.commV_apply_mem x L₂ L₁ h2 hu

theorem four_le_card_fixV_swap (h : OfourStruct X L₁ L₂ t) {x : MulAut W} (hxX : x ∈ X)
    (hxN : x ∉ L₁ ⊔ L₂) (hx2 : x * x = 1) : 4 ≤ Nat.card ↥(fixV (Subgroup.zpowers x)) := by
  have hmem : ∀ u : ↥(commV L₂), x u * u ∈ fixV (Subgroup.zpowers x) := fun u => by
    rw [mem_fixV_zpowers, map_mul]
    have h1 : x (x u) = u := by
      rw [← MulAut.mul_apply, hx2]
      rfl
    rw [h1, mul_comm]
  have hinj : Function.Injective
      (fun u : ↥(commV L₂) => (⟨x u * u, hmem u⟩ : ↥(fixV (Subgroup.zpowers x)))) := by
    intro u u' hu
    have h1 : x u * u = x u' * u' := congrArg Subtype.val hu
    obtain ⟨-, h2⟩ := eq_of_mul_eq_of_inf_eq_bot h.inf (swap_mem h hxX hxN u.2)
      (swap_mem h hxX hxN u'.2) u.2 u'.2 h1
    exact Subtype.ext h2
  have := Nat.card_le_card_of_injective _ hinj
  rwa [(card_of_actsAsNaturalL2 h.nat₂).2] at this

theorem exists_fix_sup (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {Y : Subgroup (MulAut W)} (hYT : Y ≤ T') (hYe : IsElemAbelian2 Y)
    (hY4 : 4 ≤ Nat.card Y) {N : Subgroup W} (hN : N ≠ ⊤)
    (hP : ∀ y ∈ Y, y ≠ 1 → ∀ w, y w = w → w ∈ N) :
    ∃ U ≤ N, 4 * Nat.card ↥(U ⊓ fixV Y) ≤ Nat.card U := by
  classical
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  by_cases hYS : Y ≤ T' ⊓ (L₁ ⊔ L₂)
  · exfalso
    have hYeq : Y = T' ⊓ (L₁ ⊔ L₂) :=
      Subgroup.eq_of_le_of_card_ge hYS (by rw [h.card_S hT]; exact hY4)
    have hs₁Y : s₁ ∈ Y := hYeq ▸ hF.sylow.s₁_mem_S
    have hs₂Y : s₂ ∈ Y := hYeq ▸ hF.sylow.s₂_mem_S
    apply hN
    rw [eq_top_iff]
    intro w _
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
    refine N.mul_mem ?_ ?_
    · exact hP s₂ hs₂Y hF.sylow.s₂_ne u₁ (h.L₂_fix₁ hF.sylow.s₂_mem_L hu₁)
    · exact hP s₁ hs₁Y hF.sylow.s₁_ne u₂ (h.L₁_fix₂ hF.sylow.s₁_mem_L hu₂)
  · obtain ⟨x₀, hx₀Y, hx₀S⟩ := Set.not_subset.mp hYS
    have hx₀T : x₀ ∈ T' := hYT hx₀Y
    have hx₀X : x₀ ∈ X := hT.1 hx₀T
    have hx₀N : x₀ ∉ L₁ ⊔ L₂ := fun hmem => hx₀S ⟨hx₀T, hmem⟩
    have hx₀1 : x₀ ≠ 1 := fun e => hx₀S (e ▸ Subgroup.one_mem _)
    obtain ⟨hc₁, hc₂, hxa₁, hxa₂⟩ := swap_conj h hT hF hx₀T hx₀S
    have hx₀2 : x₀ * x₀ = 1 := by
      have := hYe.2 x₀ hx₀Y
      rwa [pow_two] at this
    have hSY : 2 ≤ Nat.card ↥(Y ⊓ (T' ⊓ (L₁ ⊔ L₂))) := by
      have h1 : (T' ⊓ (L₁ ⊔ L₂)).relIndex Y ≤ (T' ⊓ (L₁ ⊔ L₂)).relIndex T' :=
        Subgroup.relIndex_le_of_le_right hYT (by rw [h.relIndex_S hT]; norm_num)
      rw [h.relIndex_S hT] at h1
      have h2 : (Y ⊓ (T' ⊓ (L₁ ⊔ L₂))).relIndex Y = (T' ⊓ (L₁ ⊔ L₂)).relIndex Y :=
        Subgroup.inf_relIndex_left Y _
      have h3 := Subgroup.relIndex_mul_card (Y ⊓ (T' ⊓ (L₁ ⊔ L₂))) Y
      rw [inf_of_le_left inf_le_left] at h3
      have h4 : Nat.card Y ≤ 2 * Nat.card ↥(Y ⊓ (T' ⊓ (L₁ ⊔ L₂))) := by
        rw [← h3]
        exact Nat.mul_le_mul_right _ (h2 ▸ h1)
      omega
    have hSYne : Y ⊓ (T' ⊓ (L₁ ⊔ L₂)) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hSY
      omega
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSYne
    have hyY : (y : MulAut W) ∈ Y := y.2.1
    have hy1' : (y : MulAut W) ≠ 1 := fun e => hy1 (Subtype.ext e)
    have hcY : s₁ * s₂ ∈ Y := by
      rcases (hF.S_eq y).1 y.2.2 with h1 | h1 | h1 | h1
      · exact absurd h1 hy1'
      · exfalso
        rw [h1] at hyY
        have hcomm := hYe.1 x₀ hx₀Y s₁ hyY
        have : s₂ = s₁ := by rw [← hc₁, hcomm]; group
        exact hF.ne this.symm
      · exfalso
        rw [h1] at hyY
        have hcomm := hYe.1 x₀ hx₀Y s₂ hyY
        have : s₁ = s₂ := by rw [← hc₂, hcomm]; group
        exact hF.ne this
      · rw [h1] at hyY
        exact hyY
    have hfixc : fixV (Subgroup.zpowers (s₁ * s₂)) ≤ fixV (T' ⊓ (L₁ ⊔ L₂)) := by
      intro w hw
      have hcw : (s₁ * s₂) w = w := mem_fixV_zpowers.1 hw
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
      have h1 : (s₁ * s₂) (u₁ * u₂) = (s₁ u₁) * (s₂ u₂) := by
        rw [MulAut.mul_apply, map_mul, map_mul, h.L₂_fix₁ hF.sylow.s₂_mem_L hu₁,
          h.L₁_fix₂ hF.sylow.s₁_mem_L (commV_stable L₂ hF.sylow.s₂_mem_L hu₂)]
      rw [h1] at hcw
      obtain ⟨e1, e2⟩ := eq_of_mul_eq_of_inf_eq_bot h.inf (commV_stable L₁ hF.sylow.s₁_mem_L hu₁)
        hu₁ (commV_stable L₂ hF.sylow.s₂_mem_L hu₂) hu₂ hcw
      have hs₁w : s₁ (u₁ * u₂) = u₁ * u₂ := by
        rw [map_mul, e1, h.L₁_fix₂ hF.sylow.s₁_mem_L hu₂]
      have hs₂w : s₂ (u₁ * u₂) = u₁ * u₂ := by
        rw [map_mul, e2, h.L₂_fix₁ hF.sylow.s₂_mem_L hu₁]
      rw [mem_fixV]
      intro x hx
      rcases (hF.S_eq x).1 hx with rfl | rfl | rfl | rfl
      · rfl
      · exact hs₁w
      · exact hs₂w
      · rw [MulAut.mul_apply, hs₂w, hs₁w]
    have hF₁N : fixV (T' ⊓ (L₁ ⊔ L₂)) ≤ N := fun w hw =>
      hP (s₁ * s₂) hcY hF.mul_ne w
        (mem_fixV.1 hw _ (Subgroup.mul_mem _ hF.sylow.s₁_mem_S hF.sylow.s₂_mem_S))
    have hF₂N : fixV (Subgroup.zpowers x₀) ≤ N := fun w hw =>
      hP x₀ hx₀Y hx₀1 w (mem_fixV_zpowers.1 hw)
    refine ⟨fixV (T' ⊓ (L₁ ⊔ L₂)) ⊔ fixV (Subgroup.zpowers x₀), sup_le hF₁N hF₂N, ?_⟩
    have hprod := B2F.card_sup_mul_card_inf_of_commute
      (A := fixV (T' ⊓ (L₁ ⊔ L₂))) (B := fixV (Subgroup.zpowers x₀)) fun a _ b _ => mul_comm a b
    have h4 : 4 ≤ Nat.card ↥(fixV (Subgroup.zpowers x₀)) :=
      four_le_card_fixV_swap h hx₀X hx₀N hx₀2
    have hinf2 : Nat.card ↥(fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀)) ≤ 2 := by
      have hsub : ((fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀) : Subgroup W) : Set W) ⊆
          {1, a₁ * a₂} := by
        rintro w ⟨hw1, hw2⟩
        have hw2' : x₀ w = w := mem_fixV_zpowers.1 hw2
        rcases (hF.sylow.fixS w).1 (fun x hx => mem_fixV.1 hw1 x hx) with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exfalso
          rw [hxa₁] at hw2'
          exact hF.a_ne hw2'.symm
        · exfalso
          rw [hxa₂] at hw2'
          exact hF.a_ne hw2'
        · exact Or.inr rfl
      have hcard : Nat.card ↥(fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀)) =
          ((fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀) : Subgroup W) : Set W).ncard :=
        Nat.card_coe_set_eq _
      rw [hcard]
      calc _ ≤ Set.ncard ({1, a₁ * a₂} : Set W) := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]
    have hfixY : fixV Y ≤ fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀) := by
      refine le_inf ?_ ?_
      · refine le_trans ?_ hfixc
        intro w hw
        rw [mem_fixV_zpowers]
        exact mem_fixV.1 hw _ hcY
      · intro w hw
        rw [mem_fixV_zpowers]
        exact mem_fixV.1 hw _ hx₀Y
    have hUY : Nat.card ↥((fixV (T' ⊓ (L₁ ⊔ L₂)) ⊔ fixV (Subgroup.zpowers x₀)) ⊓ fixV Y) ≤
        Nat.card ↥(fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀)) :=
      Subgroup.card_le_of_le (inf_le_right.trans hfixY)
    rw [hF.card_fix] at hprod
    have hd1 : 1 ≤ Nat.card ↥(fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀)) := Nat.card_pos
    generalize Nat.card ↥(fixV (T' ⊓ (L₁ ⊔ L₂)) ⊓ fixV (Subgroup.zpowers x₀)) = d at *
    generalize Nat.card ↥(fixV (T' ⊓ (L₁ ⊔ L₂)) ⊔ fixV (Subgroup.zpowers x₀)) = u at *
    generalize Nat.card ↥(fixV (Subgroup.zpowers x₀)) = f₂ at *
    interval_cases d <;> omega

theorem card_le_four_of_elemAbelian (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {Y : Subgroup (MulAut W)} (hYT : Y ≤ T') (hYe : IsElemAbelian2 Y) :
    Nat.card Y ≤ 4 := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have h8 : Nat.card T' = 8 := h.card_T hT
  have hdvd : Nat.card Y ∣ 2 ^ 3 := by
    have := Subgroup.card_dvd_of_le hYT
    rw [h8] at this
    simpa using this
  by_contra hgt
  obtain ⟨i, hi, hiY⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hY8 : Nat.card Y = 8 := by
    interval_cases i <;> simp_all
  have hYeq : Y = T' := Subgroup.eq_of_le_of_card_ge hYT (by rw [h8, hY8])
  have hτ : τ ∈ Y := hYeq ▸ hF.τ_T
  have hs₁ : s₁ ∈ Y := hYeq ▸ hF.sylow.s₁_mem_S.1
  have hcomm := hYe.1 τ hτ s₁ hs₁
  have : s₂ = s₁ := by rw [← hF.τs₁, hcomm]; group
  exact hF.ne this.symm

end Der6B

end CFSG.Quasithin
