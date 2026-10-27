module

public import CFSG.RankThree.PartOne.S15K.AllSplit
public import CFSG.RankThree.PartOne.S15K.SplitRows
public import CFSG.RankThree.PartOne.S13K.KF132At

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem r2s4_order_six : ∀ x : R2S4, x ^ 6 = 1 → x ^ 3 ≠ 1 → x ^ 2 ≠ 1 → x ^ 3 = zz := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem r2s4_dt_not_invert : ∀ x y : R2S4, y ^ 6 = 1 → y ^ 3 ≠ 1 → y ^ 2 ≠ 1 → IsDT x.2 →
    x * y * x⁻¹ ≠ y⁻¹ := by
  decide +kernel

theorem dihedral_twelve_invert : ∀ x : DihedralGroup 6, x * x = 1 → x ≠ 1 →
    x ≠ (DihedralGroup.r 1) ^ 3 → x * DihedralGroup.r 1 * x⁻¹ = (DihedralGroup.r 1)⁻¹ := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem false_of_dihedral_twelve {p : ℕ} {E : Subgroup G} (C : ReflCtx p E)
    (hirr : torusIrreducible E) (hE3 : Nat.card E = p ^ 3)
    (σ : ↥(reflectionGroup p E) ≃* R2S4) {Γ : Subgroup (MulAut E)}
    (hΓ : Γ ≤ reflectionGroup p E)
    (hclos : Γ = Subgroup.closure (reflectionSet p E ∩ (Γ : Set (MulAut E))))
    (e : ↥Γ ≃* DihedralGroup 6) : False := by
  have hZ := central_unique σ
  have hnc : ∀ x ∈ refSetR p E, ¬ ∀ g, g * x = x * g := fun x hx =>
    refSetR_not_central C hirr hE3 hZ hx
  have hnc2 : ∀ {x y : ↥(reflectionGroup p E)}, x ∈ refSetR p E → y ∈ refSetR p E → x ≠ y →
      x * y = y * x → ¬ ∀ g, g * (x * y) = (x * y) * g :=
    fun hx hy hne hcomm => refSetR_not_central_mul C hirr hE3 hZ hx hy hne hcomm
  have hcentral : ∀ x : ↥(reflectionGroup p E), σ x = zz → ∀ g, g * x = x * g := by
    intro x hx g
    apply σ.injective
    rw [map_mul, map_mul, hx]
    exact r2_central (σ g)
  let ρΓ : ↥Γ := e.symm (DihedralGroup.r 1)
  have heρ : e ρΓ = DihedralGroup.r 1 := e.apply_symm_apply _
  have hρΓ : orderOf ρΓ = 6 := by
    rw [MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_r_one
  let ρ : ↥(reflectionGroup p E) := ⟨(ρΓ : MulAut E), hΓ ρΓ.2⟩
  have hρ : orderOf ρ = 6 := by
    have h1 : orderOf (ρ : MulAut E) = orderOf ρ := Subgroup.orderOf_coe ρ
    have h2 : orderOf ((ρΓ : ↥Γ) : MulAut E) = orderOf ρΓ := Subgroup.orderOf_coe ρΓ
    rw [← h1]
    exact h2.trans hρΓ
  have hr6 : orderOf (σ ρ) = 6 := by rw [MulEquiv.orderOf_eq]; exact hρ
  have hr6' : σ ρ ^ 6 = 1 := by
    have := pow_orderOf_eq_one (σ ρ)
    rwa [hr6] at this
  have hr3' : σ ρ ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hr6]; norm_num)
  have hr2' : σ ρ ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hr6]; norm_num)
  have hcube : σ (ρ ^ 3) = zz := by
    rw [map_pow]
    exact r2s4_order_six _ hr6' hr3' hr2'
  have hρ3 : ∀ g, g * ρ ^ 3 = ρ ^ 3 * g := hcentral (ρ ^ 3) hcube
  have hgen : ∀ s : MulAut E, s ∈ reflectionSet p E → ∀ hsΓ : s ∈ Γ,
      (⟨s, hΓ hsΓ⟩ : ↥(reflectionGroup p E)) ∈ refSetR p E ∧
        IsSw (σ ⟨s, hΓ hsΓ⟩).2 := by
    intro s hs hsΓ
    have hsD : (⟨s, hΓ hsΓ⟩ : ↥(reflectionGroup p E)) ∈ refSetR p E := hs
    refine ⟨hsD, ?_⟩
    set sR : ↥(reflectionGroup p E) := ⟨s, hΓ hsΓ⟩ with hsRdef
    set sΓ : ↥Γ := ⟨s, hsΓ⟩ with hsΓdef
    have hsq : sR * sR = 1 := refSetR_sq hsD
    have hsq' : s * s = 1 := congrArg Subtype.val hsq
    have hsΓsq : sΓ * sΓ = 1 := Subtype.ext hsq'
    have hs1 : sΓ ≠ 1 := by
      intro h
      have h' : s = 1 := congrArg Subtype.val h
      exact refSetR_ne_one hsD (Subtype.ext h')
    have hsne : sΓ ≠ ρΓ ^ 3 := by
      intro h
      apply hnc sR hsD
      have h' : s = ((ρΓ ^ 3 : ↥Γ) : MulAut E) := congrArg Subtype.val h
      have : sR = ρ ^ 3 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow] at h' ⊢
        exact h'
      rw [this]
      exact hρ3
    have h1 : e sΓ * e sΓ = 1 := by rw [← map_mul, hsΓsq, map_one]
    have h2 : e sΓ ≠ 1 := fun h => hs1 (e.injective (by rw [h, map_one]))
    have h3 : e sΓ ≠ (DihedralGroup.r 1) ^ 3 := by
      intro h
      apply hsne
      apply e.injective
      rw [h, map_pow, heρ]
    have h4 := dihedral_twelve_invert (e sΓ) h1 h2 h3
    have h5 : sΓ * ρΓ * sΓ⁻¹ = ρΓ⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, heρ]
      exact h4
    have h5' : s * (ρΓ : MulAut E) * s⁻¹ = (ρΓ : MulAut E)⁻¹ := congrArg Subtype.val h5
    have h6 : sR * ρ * sR⁻¹ = ρ⁻¹ := Subtype.ext h5'
    have h7 : σ sR * σ ρ * (σ sR)⁻¹ = (σ ρ)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, h6, map_inv]
    have h8 : σ sR * σ sR = 1 := by rw [← map_mul, hsq, map_one]
    have h9 : σ sR ≠ 1 := fun h => refSetR_ne_one hsD (σ.injective (by rw [h, map_one]))
    rcases r2_invol (σ sR) h8 h9 with hz | hsw | hdt
    · exact absurd (hcentral sR hz) (hnc sR hsD)
    · exact hsw
    · exact absurd h7 (r2s4_dt_not_invert (σ sR) (σ ρ) hr6' hr3' hr2' hdt)
  have hsame : ∀ s s' : MulAut E, ∀ (hs : s ∈ reflectionSet p E) (hsΓ : s ∈ Γ)
      (hs' : s' ∈ reflectionSet p E) (hsΓ' : s' ∈ Γ),
      (σ ⟨s, hΓ hsΓ⟩).1 = (σ ⟨s', hΓ hsΓ'⟩).1 := by
    intro s s' hs hsΓ hs' hsΓ'
    by_contra hne
    obtain ⟨hsD, hsw⟩ := hgen s hs hsΓ
    obtain ⟨hsD', hsw'⟩ := hgen s' hs' hsΓ'
    set x : ↥(reflectionGroup p E) := ⟨s, hΓ hsΓ⟩ with hx
    set y : ↥(reflectionGroup p E) := ⟨s', hΓ hsΓ'⟩ with hy
    obtain ⟨g, hg⟩ := r2_swap_conj (σ y).1 (σ y).2 (σ x).2 hsw' hsw
    obtain ⟨y', hy'⟩ : ∃ y' : ↥(reflectionGroup p E),
        y' = σ.symm (1, g) * y * (σ.symm (1, g))⁻¹ := ⟨_, rfl⟩
    have hy'D : y' ∈ refSetR p E := by
      rw [hy']
      exact refSetR_conj C.prime _ _ hsD'
    have hσy' : σ y' = ((σ y).1, (σ x).2) := by
      rw [hy', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hg
    obtain ⟨hpair1, hpair2, hpair3⟩ := r2_swap_pair (σ x).1 (σ y).1 (σ x).2 hsw hne
    have hxy' : x ≠ y' := by
      intro h
      apply hpair3
      have h1 : σ x = σ y' := by rw [h]
      rw [hσy'] at h1
      exact h1
    have hcomm : x * y' = y' * x := by
      apply σ.injective
      rw [map_mul, map_mul, hσy']
      exact hpair2
    apply hnc2 hsD hy'D hxy' hcomm
    apply hcentral
    rw [map_mul, hσy']
    exact hpair1
  by_cases hS : ∃ s : MulAut E, s ∈ reflectionSet p E ∧ s ∈ Γ
  swap
  ·
    push Not at hS
    have hbot : Γ = ⊥ := by
      rw [hclos, Subgroup.closure_eq_bot_iff]
      intro s hs
      exact (hS s hs.1 hs.2).elim
    have h1 : (ρΓ : MulAut E) = 1 := Subgroup.mem_bot.1 (hbot.le ρΓ.2)
    have h2 : ρΓ = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hρΓ
    exact absurd hρΓ (by norm_num)
  obtain ⟨s₀, hs₀, hs₀Γ⟩ := hS
  set a₀ : Multiplicative (ZMod 2) := (σ ⟨s₀, hΓ hs₀Γ⟩).1 with ha₀
  let H : Subgroup (MulAut E) :=
    ((kerPsi a₀).comap σ.toMonoidHom).map (reflectionGroup p E).subtype
  have hSle : (reflectionSet p E ∩ (Γ : Set (MulAut E))) ⊆ H := by
    rintro s ⟨hs, hsΓ⟩
    refine ⟨⟨s, hΓ hsΓ⟩, ?_, rfl⟩
    obtain ⟨-, hsw⟩ := hgen s hs hsΓ
    have hfirst : (σ ⟨s, hΓ hsΓ⟩).1 = a₀ := hsame s s₀ hs hsΓ hs₀ hs₀Γ
    have heq : σ ⟨s, hΓ hsΓ⟩ = (a₀, (σ ⟨s, hΓ hsΓ⟩).2) := Prod.ext hfirst rfl
    show psiR a₀ (σ ⟨s, hΓ hsΓ⟩) = 1
    rw [heq]
    exact r2_psi_sw a₀ _ hsw
  have hΓH : Γ ≤ H := hclos.le.trans ((Subgroup.closure_le H).2 hSle)
  have hρ3Γ : ((ρΓ ^ 3 : ↥Γ) : MulAut E) ∈ H := hΓH (ρΓ ^ 3).2
  obtain ⟨x, hx, hxρ⟩ := Subgroup.mem_map.1 hρ3Γ
  have hxρ' : x = ρ ^ 3 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    have := hxρ
    simp only [Subgroup.subtype_apply, Subgroup.coe_pow] at this
    exact this
  have hx' : psiR a₀ (σ x) = 1 := hx
  rw [hxρ', hcube] at hx'
  exact r2_psi_zz a₀ hx'

@[expose] def KF158NoRowSixEight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
    (Outcome152Two p E A (lieGenerated p E) ∨ Outcome152Three p E A (lieGenerated p E)) →
    ∀ J ∈ thetaCompZeroStarE p E, J ≤ lieGenerated p E → ¬ RowModel p J 6 ∧ ¬ RowModel p J 8

theorem kf158AllSplitBC_of_rows (hS13 : Sec13Avail) (hN156 : Node156)
    (hAt : ∀ r : ℕ, (r = 1 ∨ r = 5 ∨ r = 7) → KF132At r) (hNo : KF158NoRowSixEight) :
    KF158AllSplitBC := by
  intro G _ _ p A c L E h15 hF hout s hs
  have h := h15.h12
  have hEA : E = A := by
    rcases hout with h | h
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hp34 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne hEA
  have hF13 := hS13 G p A c L E h hnot5
  have hout' : Outcome152 p E A (lieGenerated p E) := by
    rcases hout with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨X, hX, hsX⟩ := hs.2
  have hXI : X ≤ lieGenerated p E := hN156 G p A c L E h15 hF hout' X hX
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate X hX
  have hnot5' : ¬ Outcome152Five p E B (lieGenerated p E) := by
    rintro ⟨-, -, -, -, -, hE4, -, -⟩
    rw [hE3] at hE4
    omega
  have hF13' := hS13 G p B c' X E h' hnot5'
  obtain ⟨hclos, r, hr1, hr12, hrow, hweyl, hrB, hr9⟩ := hF'.three
  have hr8 : r ≤ 8 := by
    by_contra hlt
    have h4 := hr9 (by omega)
    rw [hE3] at h4
    omega
  have hEB : E = B := hrB hr8
  have hstar : torusImage E X ≤ reflectionGroup p E :=
    calc torusImage E X = Subgroup.closure (reflectionSet p E ∩ (torusImage E X : Set (MulAut E))) :=
          hclos
      _ ≤ reflectionGroup p E := Subgroup.closure_mono Set.inter_subset_left
  have hirr : torusIrreducible E := hF13.irreducible
  have C := reflCtx_of_hyp h
  obtain ⟨σ⟩ : Nonempty (↥(reflectionGroup p E) ≃* R2S4) := by
    rcases hout with ⟨-, -, -, -, hσ, -⟩ | ⟨-, -, -, -, hσ, -⟩ <;> exact hσ
  have hexp : ∀ x ∈ reflectionGroup p E, x ^ 12 = 1 := reflectionGroup_pow_twelve (Or.inr ⟨σ⟩)
  have hno := hNo G p A c L E h15 hF hout X hX hXI
  have h6 : r ≠ 6 := by
    rintro rfl
    exact hno.1 hrow
  have h8 : r ≠ 8 := by
    rintro rfl
    exact hno.2 hrow
  have h4 : r ≠ 4 := by
    rintro rfl
    obtain ⟨e⟩ : Nonempty (↥(torusImage E X) ≃* DihedralGroup 8) := hweyl
    exact false_of_dihedral_eight hstar hexp e
  have h2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨e⟩ : Nonempty (↥(torusImage E X) ≃* DihedralGroup 6) := hweyl
    exact false_of_dihedral_twelve C hirr hE3 σ hstar hclos e
  have h3 : r ≠ 3 := by
    rintro rfl
    obtain ⟨e⟩ : Nonempty (↥(torusImage E X) ≃* DihedralGroup 6) := hweyl
    exact false_of_dihedral_twelve C hirr hE3 σ hstar hclos e
  have hr157 : r = 1 ∨ r = 5 ∨ r = 7 := by omega
  have hrr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  exact kf132At_split hrr (hAt r hr157) h' hF' hF13' hnot5' hrow hEB hs hsX

theorem kf158AllSplitBC_of_rows157 (hS13 : Sec13Avail) (hN156 : Node156) (h1 : KF132At 1)
    (h5 : KF132At 5) (h7 : KF132At 7) (hNo : KF158NoRowSixEight) : KF158AllSplitBC :=
  kf158AllSplitBC_of_rows hS13 hN156 (by rintro r (rfl | rfl | rfl) <;> assumption) hNo

end CFSG.RankThree.PartOne.S13K
