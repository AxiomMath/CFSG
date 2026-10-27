module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Six
public import CFSG.ClassicalInvolution.Q3.TL4E3C269G9A
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.PGL29Facts

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155KA6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.ClassicalInvolution.Q3.TL4.E3C269G9 (m10_le_autA6)

section Abstract

variable {G : Type*} [Group G]

theorem apply_mem_iff_of_finite [Finite G] (f : G ≃* G) {L : Subgroup G}
    (hf : ∀ l ∈ L, f l ∈ L) (x : G) : f x ∈ L ↔ x ∈ L := by
  refine ⟨fun hx => ?_, hf x⟩
  have hinj : Function.Injective (fun l : L => (⟨f l, hf l l.2⟩ : L)) := fun a b h =>
    Subtype.ext (f.injective (congrArg Subtype.val h))
  obtain ⟨l, hl⟩ := Finite.surjective_of_injective hinj ⟨f x, hx⟩
  have h2 : f l = f x := congrArg Subtype.val hl
  rw [← f.injective h2]
  exact l.2

theorem card_le_sixty [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 360) {L : Subgroup G}
    (hL : L ≠ ⊤) : Nat.card L ≤ 60 := by
  have hnc : L.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.2 (h.symm.le.trans L.normalCore_le)) hL
  have h1 := L.index_normalCore_dvd_factorial_index
  rw [hnc, Subgroup.index_bot, hG] at h1
  have h6 : 6 ≤ L.index := by
    by_contra hcon
    have h2 : Nat.factorial L.index ≤ Nat.factorial 5 := Nat.factorial_le (by omega)
    have h3 : 360 ≤ Nat.factorial L.index := Nat.le_of_dvd (Nat.factorial_pos _) h1
    have h4 : Nat.factorial 5 = 120 := by decide
    omega
  have h7 := Subgroup.card_mul_index L
  rw [hG] at h7
  by_contra hcon
  have : 61 * 6 ≤ Nat.card L * L.index := Nat.mul_le_mul (by omega) h6
  omega

theorem mem_of_normalizes [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 360) {L : Subgroup G}
    (hL : Nat.card L = 60) {g : G} (hg : ∀ l ∈ L, g * l * g⁻¹ ∈ L) : g ∈ L := by
  have hgN : g ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mem_normalizer_iff.2 fun x =>
      (apply_mem_iff_of_finite (MulAut.conj g) hg x).symm
  have hNtop : Subgroup.normalizer (L : Set G) ≠ ⊤ := by
    intro htop
    haveI : L.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
    · rw [h, Subgroup.card_bot] at hL
      omega
    · rw [h, Subgroup.card_top, hG] at hL
      omega
  have hle := card_le_sixty hG hNtop
  have heq : L = Subgroup.normalizer (L : Set G) :=
    Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by omega)
  exact heq.symm.le hgN

end Abstract

theorem exists_swap_three_cycle {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 6) (b₀ : Ω) (π : Equiv.Perm Ω) (hπ : π b₀ = b₀) :
    ∃ a : Equiv.Perm Ω, a ∈ alternatingGroup Ω ∧ a b₀ = b₀ ∧ (π * a) * (π * a) = 1 ∧
      ∃ c : Equiv.Perm Ω, c ∈ alternatingGroup Ω ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧
        (π * a) * c = c * (π * a) := by
  obtain ⟨e, he⟩ : ∃ e : Ω ≃ Fin 6, e b₀ = 5 := by
    let e₀ := Fintype.equivFinOfCardEq hΩ
    exact ⟨e₀.trans (Equiv.swap (e₀ b₀) 5), by simp⟩
  have hne : ∀ i j : Fin 6, i ≠ j → e.symm i ≠ e.symm j := fun i j h h' =>
    h (e.symm.injective h')
  have hb5 : ∀ i : Fin 6, i ≠ 5 → e.symm i ≠ b₀ := by
    intro i hi h
    apply hi
    have h2 := congrArg e h
    rwa [Equiv.apply_symm_apply, he] at h2
  set τ : Equiv.Perm Ω := Equiv.swap (e.symm 0) (e.symm 1) with hτ
  set c : Equiv.Perm Ω :=
    Equiv.swap (e.symm 2) (e.symm 3) * Equiv.swap (e.symm 2) (e.symm 4) with hc
  have hc3cyc : c.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (hne 2 3 (by decide)) (hne 2 4 (by decide))
      (hne 3 4 (by decide))
  have hcA : c ∈ alternatingGroup Ω := hc3cyc.mem_alternatingGroup
  have hc3 : c ^ 3 = 1 := by
    rw [← hc3cyc.orderOf]
    exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    have := hc3cyc.orderOf
    rw [h, orderOf_one] at this
    omega
  have hτb : τ b₀ = b₀ :=
    Equiv.swap_apply_of_ne_of_ne (hb5 0 (by decide)).symm (hb5 1 (by decide)).symm
  have hτsign : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap (hne 0 1 (by decide))
  have hτ2 : τ * τ = 1 := Equiv.swap_mul_self _ _
  have hcomm_swap : ∀ z w : Ω, τ z = z → τ w = w →
      τ * Equiv.swap z w = Equiv.swap z w * τ := by
    intro z w hz hw
    have h := Equiv.swap_apply_apply τ z w
    rw [hz, hw] at h
    calc τ * Equiv.swap z w = (τ * Equiv.swap z w * τ⁻¹) * τ := by group
      _ = Equiv.swap z w * τ := by rw [← h]
  have hτfix : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → τ (e.symm i) = e.symm i := fun i h0 h1 =>
    Equiv.swap_apply_of_ne_of_ne (hne i 0 h0) (hne i 1 h1)
  have hτc : τ * c = c * τ := by
    have h1 := hcomm_swap (e.symm 2) (e.symm 3) (hτfix 2 (by decide) (by decide))
      (hτfix 3 (by decide) (by decide))
    have h2 := hcomm_swap (e.symm 2) (e.symm 4) (hτfix 2 (by decide) (by decide))
      (hτfix 4 (by decide) (by decide))
    rw [hc, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  have key : ∃ a : Equiv.Perm Ω, a ∈ alternatingGroup Ω ∧ a b₀ = b₀ ∧ (π * a = 1 ∨ π * a = τ) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
    · refine ⟨π⁻¹, ?_, ?_, Or.inl (mul_inv_cancel π)⟩
      · rw [Equiv.Perm.mem_alternatingGroup, map_inv, hs]
        rfl
      · rw [Equiv.Perm.inv_eq_iff_eq]
        exact hπ.symm
    · refine ⟨π⁻¹ * τ, ?_, ?_, Or.inr (mul_inv_cancel_left π τ)⟩
      · rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, hτsign]
        decide
      · rw [Equiv.Perm.mul_apply, hτb, Equiv.Perm.inv_eq_iff_eq]
        exact hπ.symm
  obtain ⟨a, haA, hab, hπa⟩ := key
  refine ⟨a, haA, hab, ?_, c, hcA, hc1, hc3, ?_⟩
  · rcases hπa with h | h
    · rw [h, mul_one]
    · rw [h, hτ2]
  · rcases hπa with h | h
    · rw [h, one_mul, mul_one]
    · rw [h, hτc]

section Cosets

variable {G : Type*} [Group G]

@[expose] def cosetPerm (L : Subgroup G) (α : G ≃* G) (hα : ∀ l ∈ L, α l ∈ L)
    (hα' : ∀ l ∈ L, α.symm l ∈ L) : Equiv.Perm (G ⧸ L) where
  toFun := Quotient.map' α fun a b h => QuotientGroup.leftRel_apply.mpr <| by
    have h' : a⁻¹ * b ∈ L := QuotientGroup.leftRel_apply.mp h
    have e : (α a)⁻¹ * α b = α (a⁻¹ * b) := by rw [map_mul, map_inv]
    rw [e]
    exact hα _ h'
  invFun := Quotient.map' α.symm fun a b h => QuotientGroup.leftRel_apply.mpr <| by
    have h' : a⁻¹ * b ∈ L := QuotientGroup.leftRel_apply.mp h
    have e : (α.symm a)⁻¹ * α.symm b = α.symm (a⁻¹ * b) := by rw [map_mul, map_inv]
    rw [e]
    exact hα' _ h'
  left_inv q := QuotientGroup.induction_on q fun g => by
    show (QuotientGroup.mk (α.symm (α g)) : G ⧸ L) = QuotientGroup.mk g
    rw [MulEquiv.symm_apply_apply]
  right_inv q := QuotientGroup.induction_on q fun g => by
    show (QuotientGroup.mk (α (α.symm g)) : G ⧸ L) = QuotientGroup.mk g
    rw [MulEquiv.apply_symm_apply]

theorem cosetPerm_mk (L : Subgroup G) (α : G ≃* G) (hα : ∀ l ∈ L, α l ∈ L)
    (hα' : ∀ l ∈ L, α.symm l ∈ L) (g : G) :
    cosetPerm L α hα hα' (QuotientGroup.mk g) = QuotientGroup.mk (α g) :=
  rfl

theorem cosetPerm_smul (L : Subgroup G) (α : G ≃* G) (hα : ∀ l ∈ L, α l ∈ L)
    (hα' : ∀ l ∈ L, α.symm l ∈ L) (g : G) (x : G ⧸ L) :
    cosetPerm L α hα hα' (g • x) = α g • cosetPerm L α hα hα' x := by
  refine QuotientGroup.induction_on x fun h => ?_
  show (QuotientGroup.mk (α (g * h)) : G ⧸ L) = QuotientGroup.mk (α g * α h)
  rw [map_mul α g h]

end Cosets

theorem exists_involutory_coset {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) {L : Subgroup G} (hL : Nat.card L = 60)
    (α : G ≃* G) (hα : ∀ l ∈ L, α l ∈ L) :
    ∃ l ∈ L, (∀ g : G, α (l * α (l * g * l⁻¹) * l⁻¹) = g) ∧
      ∃ x : G, x ≠ 1 ∧ x ^ 3 = 1 ∧ α (l * x * l⁻¹) = x := by
  classical
  have hα' : ∀ l ∈ L, α.symm l ∈ L := fun l hl =>
    (apply_mem_iff_of_finite α hα (α.symm l)).1 (by simpa using hl)
  have hidx : L.index = 6 := by
    have h := Subgroup.index_mul_card L
    rw [hL, hG] at h
    omega
  have hX : Nat.card (G ⧸ L) = 6 := hidx
  have hLtop : L ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top] at hL
    omega
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ L)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.2 (h.symm.le.trans L.normalCore_le)) hLtop
  have : Fintype (G ⧸ L) := Fintype.ofFinite _
  have hindex2 : (MulAction.toPermHom G (G ⧸ L)).range.index = 2 := by
    have h1 := Subgroup.index_mul_card (MulAction.toPermHom G (G ⧸ L)).range
    have h2 := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have h3 : Nat.card (Equiv.Perm (G ⧸ L)) = 720 := by
      rw [Nat.card_perm, hX]
      decide
    rw [h2, hG, h3] at h1
    omega
  have hrange : (MulAction.toPermHom G (G ⧸ L)).range = alternatingGroup (G ⧸ L) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex2
  obtain ⟨b₀, hb₀⟩ : ∃ b : G ⧸ L, b = QuotientGroup.mk 1 := ⟨_, rfl⟩
  have hstab : ∀ g : G, g • b₀ = b₀ → g ∈ L := by
    intro g hg
    rw [hb₀] at hg
    have h : (QuotientGroup.mk (g * 1) : G ⧸ L) = QuotientGroup.mk 1 := hg
    have h2 := QuotientGroup.eq.1 h
    simpa using h2
  obtain ⟨π, hπb, hπsmul⟩ : ∃ π : Equiv.Perm (G ⧸ L), π b₀ = b₀ ∧
      ∀ (g : G) (x : G ⧸ L), π (g • x) = α g • π x := by
    refine ⟨cosetPerm L α hα hα', ?_, cosetPerm_smul L α hα hα'⟩
    rw [hb₀, cosetPerm_mk, map_one α]
  have hconj : ∀ g : G, MulAction.toPermHom G (G ⧸ L) (α g) =
      π * MulAction.toPermHom G (G ⧸ L) g * π⁻¹ := by
    intro g
    refine Equiv.ext fun y => ?_
    have h := hπsmul g (π⁻¹ y)
    have h0 : π (π⁻¹ y) = y := by simp
    rw [h0] at h
    exact h.symm
  obtain ⟨a, haA, hab, hsq, c, hcA, hc1, hc3, hcomm⟩ :=
    exists_swap_three_cycle (Ω := G ⧸ L) (by rw [Fintype.card_eq_nat_card]; exact hX) b₀ π hπb
  have haR : a ∈ (MulAction.toPermHom G (G ⧸ L)).range := by rw [hrange]; exact haA
  obtain ⟨l, hl⟩ := haR
  have hlL : l ∈ L := by
    refine hstab l ?_
    have h : (MulAction.toPermHom G (G ⧸ L)) l b₀ = b₀ := by rw [hl]; exact hab
    exact h
  have hconjT : ∀ g : G, MulAction.toPermHom G (G ⧸ L) (α (l * g * l⁻¹)) =
      (π * a) * MulAction.toPermHom G (G ⧸ L) g * (π * a)⁻¹ := by
    intro g
    rw [hconj]
    simp only [map_mul, map_inv, hl]
    group
  refine ⟨l, hlL, ?_, ?_⟩
  · intro g
    apply hinj
    rw [hconjT, hconjT]
    have h1 : (π * a)⁻¹ * (π * a)⁻¹ = 1 := by rw [← mul_inv_rev, hsq, inv_one]
    calc (π * a) * ((π * a) * MulAction.toPermHom G (G ⧸ L) g * (π * a)⁻¹) * (π * a)⁻¹
        = ((π * a) * (π * a)) * MulAction.toPermHom G (G ⧸ L) g *
            ((π * a)⁻¹ * (π * a)⁻¹) := by group
      _ = MulAction.toPermHom G (G ⧸ L) g := by rw [hsq, h1]; simp
  · have hcR : c ∈ (MulAction.toPermHom G (G ⧸ L)).range := by rw [hrange]; exact hcA
    obtain ⟨x, hx⟩ := hcR
    refine ⟨x, ?_, ?_, ?_⟩
    · intro hx1
      apply hc1
      rw [← hx, hx1, map_one]
    · apply hinj
      rw [map_pow, hx, hc3, map_one]
    · apply hinj
      rw [hconjT, hx, hcomm]
      group

section Model

theorem exists_involution_of_normalizes {b : P10} (hb : b ∈ A6Models.autA6)
    {L : Subgroup ↥A6Models.psl29} (hL : Nat.card L = 60)
    (hbL : ∀ l ∈ L, DoubleA3.conjAut ⟨b, hb⟩ l ∈ L) :
    ∃ l ∈ L, (b * (l : P10)) * (b * (l : P10)) = 1 ∧
      ∃ x ∈ A6Models.psl29, x ≠ 1 ∧ x ^ 3 = 1 ∧ (b * (l : P10)) * x = x * (b * (l : P10)) := by
  haveI : IsSimpleGroup ↥A6Models.psl29 :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.isSimpleGroup_psl29
  obtain ⟨l, hlL, hsq, x, hx1, hx3, hxα⟩ :=
    exists_involutory_coset card_psl29 hL (DoubleA3.conjAut ⟨b, hb⟩) hbL
  refine ⟨l, hlL, ?_, (x : P10), x.2, ?_, ?_, ?_⟩
  · have hlA : (l : P10) ∈ A6Models.autA6 := psl29_le_autA6 l.2
    refine centralizer_psl29 (Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hlA)
      (Subgroup.mul_mem _ hb hlA)) fun y hy => ?_
    have h := congrArg (fun z : ↥A6Models.psl29 => (z : P10)) (hsq ⟨y, hy⟩)
    simp only [DoubleA3.conjAut_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc b * (l : P10) * (b * (l : P10)) * y
        = (b * ((l : P10) * (b * ((l : P10) * y * (l : P10)⁻¹) * b⁻¹) * (l : P10)⁻¹) * b⁻¹) *
            (b * (l : P10) * (b * (l : P10))) := by group
      _ = y * (b * (l : P10) * (b * (l : P10))) := by rw [h]
  · exact fun h => hx1 (Subtype.ext h)
  · have := congrArg Subtype.val hx3
    simpa using this
  · have h := congrArg (fun z : ↥A6Models.psl29 => (z : P10)) hxα
    simp only [DoubleA3.conjAut_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc b * (l : P10) * (x : P10)
        = (b * ((l : P10) * (x : P10) * (l : P10)⁻¹) * b⁻¹) * (b * (l : P10)) := by group
      _ = (x : P10) * (b * (l : P10)) := by rw [h]

theorem exists_mem_of_mem_m10 {b : P10} (hb : b ∈ A6Models.m10)
    {L : Subgroup ↥A6Models.psl29} (hL : Nat.card L = 60)
    (hbL : ∀ l ∈ L, DoubleA3.conjAut ⟨b, m10_le_autA6 hb⟩ l ∈ L) :
    ∃ g ∈ L, (g : P10) = b := by
  haveI : IsSimpleGroup ↥A6Models.psl29 :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.isSimpleGroup_psl29
  obtain ⟨l, hlL, hsq, -⟩ := exists_involution_of_normalizes (m10_le_autA6 hb) hL hbL
  have hu : b * (l : P10) ∈ A6Models.m10 :=
    Subgroup.mul_mem _ hb (Out21.A6.psl29_le_m10 l.2)
  have hupsl : b * (l : P10) ∈ A6Models.psl29 := Out21.A6.m10_involution_mem_psl29 hu hsq
  have hbpsl : b ∈ A6Models.psl29 := by
    have := Subgroup.mul_mem _ hupsl (Subgroup.inv_mem _ l.2)
    simpa using this
  refine ⟨⟨b, hbpsl⟩, mem_of_normalizes card_psl29 hL fun l' hl' => ?_, rfl⟩
  exact hbL l' hl'

end Model

theorem exists_inner_of_fixes_center {Q : Type} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) (hZ : Nat.card (Subgroup.center Q) = 3)
    (hcard : Nat.card Q = 1080) (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29)
    {σ : MulAut Q} (hfix : ∀ z ∈ Subgroup.center Q, σ z = z)
    {σ' : MulAut (Q ⧸ Subgroup.center Q)}
    (hσ' : ∀ q : Q, σ' (QuotientGroup.mk q) = QuotientGroup.mk (σ q))
    {H : Subgroup (Q ⧸ Subgroup.center Q)} (hH60 : Nat.card H = 60)
    (hσH : ∀ y ∈ H, σ' y ∈ H) :
    ∃ h ∈ H, ∀ y ∈ H, σ' y = h * y * h⁻¹ := by
  obtain ⟨⟨b, hbA⟩, hb⟩ := DoubleA3.conjAut_surjective (MulAut.congr ψ6 σ')
  have hbψ : ∀ y : Q ⧸ Subgroup.center Q,
      ((ψ6 (σ' y) : ↥A6Models.psl29) : P10) = b * ((ψ6 y : ↥A6Models.psl29) : P10) * b⁻¹ := by
    intro y
    have h := congrArg (fun f : MulAut ↥A6Models.psl29 => ((f (ψ6 y) : ↥A6Models.psl29) : P10)) hb
    simp only [DoubleA3.conjAut_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h
    exact h.symm
  set L : Subgroup ↥A6Models.psl29 := H.map ψ6.toMonoidHom with hLdef
  have hL : Nat.card L = 60 := by
    rw [hLdef, Subgroup.card_map_of_injective (f := ψ6.toMonoidHom) ψ6.injective]
    exact hH60
  have hbL : ∀ l ∈ L, DoubleA3.conjAut ⟨b, hbA⟩ l ∈ L := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hl
    refine Subgroup.mem_map.2 ⟨σ' y, hσH y hy, ?_⟩
    apply Subtype.ext
    rw [DoubleA3.conjAut_apply]
    exact hbψ y
  obtain ⟨l, hlL, -, x, hxpsl, hx1, hx3, hcomm⟩ := exists_involution_of_normalizes hbA hL hbL
  obtain ⟨y₀, hy₀H, hy₀⟩ := Subgroup.mem_map.1 hlL
  obtain ⟨q₀, rfl⟩ := QuotientGroup.mk_surjective y₀
  have hbl : b * (l : P10) ∈ A6Models.m10 := by
    refine CFSG.LocalAnalysis.GLTheoremB.Prop95I1921.mem_m10_of_fixes_center hperf hZ hcard ψ6
      (σ := σ * MulAut.conj q₀) ?_ (b := b * (l : P10))
      (Subgroup.mul_mem _ hbA (psl29_le_autA6 l.2)) ?_ hxpsl hx3 hx1 hcomm
    · intro z hz
      have hq : q₀ * z * q₀⁻¹ = z := by
        rw [Subgroup.mem_center_iff.1 hz q₀, mul_inv_cancel_right]
      show σ (q₀ * z * q₀⁻¹) = z
      rw [hq]
      exact hfix z hz
    · intro q
      have h1 : ((ψ6 (QuotientGroup.mk (σ (q₀ * q * q₀⁻¹))) : ↥A6Models.psl29) : P10) =
          b * ((ψ6 (QuotientGroup.mk (q₀ * q * q₀⁻¹)) : ↥A6Models.psl29) : P10) * b⁻¹ := by
        rw [← hσ', hbψ]
      have h0 : (ψ6 (QuotientGroup.mk q₀) : ↥A6Models.psl29) = l := hy₀
      have h2 : ((ψ6 (QuotientGroup.mk (q₀ * q * q₀⁻¹)) : ↥A6Models.psl29) : P10) =
          (l : P10) * ((ψ6 (QuotientGroup.mk q) : ↥A6Models.psl29) : P10) * (l : P10)⁻¹ := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv,
          Subgroup.coe_mul, Subgroup.coe_inv, h0]
      show ((ψ6 (QuotientGroup.mk (σ (q₀ * q * q₀⁻¹))) : ↥A6Models.psl29) : P10) = _
      rw [h1, h2]
      group
  have hbm : b ∈ A6Models.m10 := by
    have := Subgroup.mul_mem _ hbl (Subgroup.inv_mem _ (Out21.A6.psl29_le_m10 l.2))
    simpa using this
  obtain ⟨g, hgL, hgb⟩ := exists_mem_of_mem_m10 hbm hL hbL
  obtain ⟨y₁, hy₁H, hy₁⟩ := Subgroup.mem_map.1 hgL
  refine ⟨y₁, hy₁H, fun y _ => ?_⟩
  apply ψ6.injective
  apply Subtype.ext
  have hy₁' : ((ψ6 y₁ : ↥A6Models.psl29) : P10) = b := by
    rw [← hgb, ← hy₁]
    rfl
  rw [hbψ y]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hy₁']

end CFSG.RankThree.PartTwo.Sec15.Sylow155KA6
