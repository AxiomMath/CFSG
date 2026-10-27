module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Outer

variable {W : Type} [CommGroup W] [Finite W] {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}

private lemma s16e_twoO_two_mul_le {Γ : Type} [Group Γ] [Finite Γ] {H N : Subgroup Γ}
    (hlt : H < N) : 2 * Nat.card H ≤ Nat.card N := by
  have h1 : Nat.card H ∣ Nat.card N := Subgroup.card_dvd_of_le hlt.le
  have h2 : Nat.card H < Nat.card N := Subgroup.card_lt_of_lt hlt
  by_contra hcon
  have h3 : Nat.card N < 2 * Nat.card H := not_le.1 hcon
  have := Nat.eq_of_dvd_of_lt_two_mul (Nat.card_pos.ne') h1 h3
  omega

private lemma s16e_twoO_mul_injective {Γ : Type} [Group Γ] {K N : Subgroup Γ}
    (h : K ⊓ N = ⊥) :
    Function.Injective (fun p : ↥K × ↥N => (p.1 : Γ) * (p.2 : Γ)) := by
  rintro ⟨k, n⟩ ⟨k', n'⟩ h1
  have h1 : (k : Γ) * (n : Γ) = (k' : Γ) * (n' : Γ) := h1
  have h2 : (k' : Γ)⁻¹ * (k : Γ) = (n' : Γ) * (n : Γ)⁻¹ := by
    calc (k' : Γ)⁻¹ * (k : Γ) = (k' : Γ)⁻¹ * ((k : Γ) * (n : Γ)) * (n : Γ)⁻¹ := by group
      _ = (k' : Γ)⁻¹ * ((k' : Γ) * (n' : Γ)) * (n : Γ)⁻¹ := by rw [h1]
      _ = (n' : Γ) * (n : Γ)⁻¹ := by group
  have h3 : (k' : Γ)⁻¹ * (k : Γ) ∈ K ⊓ N :=
    ⟨K.mul_mem (K.inv_mem k'.2) k.2, h2 ▸ N.mul_mem n'.2 (N.inv_mem n.2)⟩
  rw [h, Subgroup.mem_bot] at h3
  have hk : k = k' := Subtype.ext (inv_mul_eq_one.1 h3).symm
  subst hk
  have hn : n = n' := Subtype.ext (mul_left_cancel h1)
  rw [hn]

private lemma s16e_twoO_sup_of_card {Γ : Type} [Group Γ] [Finite Γ] {X K N : Subgroup Γ}
    (hK : K ≤ X) (hN : N ≤ X) (h : K ⊓ N = ⊥) (hc : Nat.card X ≤ Nat.card K * Nat.card N) :
    K ⊔ N = X := by
  apply le_antisymm (sup_le hK hN)
  let f : ↥K × ↥N → ↥X := fun p =>
    ⟨(p.1 : Γ) * (p.2 : Γ), X.mul_mem (hK p.1.2) (hN p.2.2)⟩
  have hf : Function.Injective f := fun p q hpq =>
    s16e_twoO_mul_injective h (congrArg Subtype.val hpq)
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [Nat.card_prod]; exact hc)
  intro x hx
  obtain ⟨⟨k, n⟩, hkn⟩ := hbij.2 ⟨x, hx⟩
  have : (k : Γ) * (n : Γ) = x := congrArg Subtype.val hkn
  rw [← this]
  exact Subgroup.mul_mem_sup k.2 n.2

private lemma s16e_twoO_map_mul (x y : MulAut W) (I : Subgroup W) :
    I.map (x * y).toMonoidHom = (I.map y.toMonoidHom).map x.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private lemma s16e_twoO_mem_stabSub {U : Subgroup W} {g : MulAut W}
    (hg : U.map g.toMonoidHom = U) : g ∈ stabSub U := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 (hg.ge hu)
    have : v = u := g.injective hvu
    rw [← this]
    exact hv
  · intro hu
    exact hg.le (Subgroup.mem_map_of_mem g.toMonoidHom hu)

private lemma s16e_twoO_mem_cent_of_fix (F : Cfg2Setting X H J₀ J₁) {c : MulAut W}
    (hcX : c ∈ X) (hfix : ∀ u ∈ J₀, c u = u) : c ∈ s16e_two_cent X H := by
  refine ⟨hcX, ?_⟩
  have hirr := s16e_two_isIrrOn_of_mem F F.irr₀
  refine s16c167_cfg2_cent_of_fix F hirr.2.1 hirr.1.ne' hcX ?_
  intro u hu
  rw [mem_fixV]
  intro g hg
  have hmem : c ∈ MulAction.stabilizer (MulAut W) u := hfix u hu
  exact Subgroup.zpowers_le.2 hmem hg

private lemma s16e_twoO_exists_stab (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (h3 : 3 ∣ Nat.card ↥(s16e_two_cent X H)) {x : MulAut W} (hx : x ∈ X) :
    ∃ k ∈ s16e_two_cent X H, J₀.map (k * x).toMonoidHom = J₀ := by
  have hI := s16e_two_map_mem_irrSet F hx F.irr₀
  obtain ⟨k, hk, hkI⟩ := s16e_two_transitive_of_three_dvd F hE₀ hE₁ h3 _ hI J₀ F.irr₀
  refine ⟨k, hk, ?_⟩
  rw [s16e_twoO_map_mul]
  exact hkI.symm

private lemma s16e_twoO_autSub_le_normalizer (F : Cfg2Setting X H J₀ J₁) :
    autSub X J₀ ≤ Subgroup.normalizer (autSub H J₀ : Set (MulAut ↥J₀)) := by
  have hnorm : ∀ y ∈ X, ∀ h ∈ H, y * h * y⁻¹ ∈ H := fun y hy h hh => by
    have := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hh
    rwa [F.norm y hy] at this
  have key : ∀ g : ↥(stabSub J₀), (g : MulAut W) ∈ X → ∀ φ ∈ autSub H J₀,
      resHom J₀ g * φ * (resHom J₀ g)⁻¹ ∈ autSub H J₀ := by
    intro g hgX φ hφ
    obtain ⟨g', hg'H, rfl⟩ := mem_autSub.1 hφ
    refine mem_autSub.2 ⟨g * g' * g⁻¹, ?_, ?_⟩
    · exact hnorm _ hgX _ hg'H
    · rw [map_mul, map_mul, map_inv]
  intro r hr
  obtain ⟨g, hgX, rfl⟩ := mem_autSub.1 hr
  rw [Subgroup.mem_normalizer_iff]
  intro φ
  constructor
  · exact key g hgX φ
  · intro h
    have hgXinv : ((g⁻¹ : ↥(stabSub J₀)) : MulAut W) ∈ X := X.inv_mem hgX
    have h1 := key g⁻¹ hgXinv _ h
    rw [map_inv, inv_inv] at h1
    have e : (resHom J₀ g)⁻¹ * (resHom J₀ g * φ * (resHom J₀ g)⁻¹) * resHom J₀ g = φ := by
      group
    rwa [e] at h1

theorem s16e_two_mem_fixIrr_of_rk (F : Cfg2Setting X H J₀ J₁) (hE₀ : Z391.EndUnitsTrivial H J₀)
    {m : ℕ} (h₀ : m ≤ rk ↥J₀) (h₁ : m ≤ rk ↥J₁) {t : MulAut W} (htX : t ∈ X)
    (htrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) < m) : t ∈ s16e_two_fixIrr X H := by
  refine ⟨htX, fun I hI => ?_⟩
  by_contra hmove
  have h1 := s16e_two_rk_comm_of_moves F htX hI hmove
  have h2 := s16e_two_rk_irr_ge F hE₀ h₀ h₁ I hI
  omega

theorem s16e_two_card_le_of_aut (F : Cfg2Setting X H J₀ J₁)
    (hAut : Nat.card (MulAut ↥H) ≤ 2 * Nat.card ↥H) :
    Nat.card ↥X ≤ 2 * Nat.card ↥(s16e_two_cent X H) * Nat.card ↥H := by
  have hdvd := s16e_two_card_dvd_mul_aut F
  have hpos : 0 < Nat.card ↥(s16e_two_cent X H) * Nat.card (MulAut ↥H) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  calc Nat.card ↥X ≤ Nat.card ↥(s16e_two_cent X H) * Nat.card (MulAut ↥H) :=
        Nat.le_of_dvd hpos hdvd
    _ ≤ Nat.card ↥(s16e_two_cent X H) * (2 * Nat.card ↥H) := Nat.mul_le_mul_left _ hAut
    _ = 2 * Nat.card ↥(s16e_two_cent X H) * Nat.card ↥H := by ring

theorem s16e_two_sup_of_outer (F : Cfg2Setting X H J₀ J₁) (hHX : H ≤ X)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (h₀ : 4 ≤ rk ↥J₀) (h₁ : 4 ≤ rk ↥J₁)
    (hinv : ∀ h ∈ H, h ≠ 1 → h ^ 2 = 1 → 4 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers h)))
    (hcard : Nat.card ↥X ≤ 2 * Nat.card ↥(s16e_two_cent X H) * Nat.card ↥H)
    {t : MulAut W} (htX : t ∈ X) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) :
    s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X ∧ H < s16e_two_fixIrr X H := by
  have htN : t ∈ s16e_two_fixIrr X H :=
    s16e_two_mem_fixIrr_of_rk F hE₀ (m := 4) h₀ h₁ htX (by omega)
  have htH : t ∉ H := fun htH => by
    have := hinv t htH ht1 ht2
    omega
  have hlt : H < s16e_two_fixIrr X H :=
    lt_of_le_of_ne (s16e_two_le_fixIrr hHX) (fun h => htH (h.ge htN))
  have h2 : 2 * Nat.card H ≤ Nat.card (s16e_two_fixIrr X H) := s16e_twoO_two_mul_le hlt
  refine ⟨s16e_twoO_sup_of_card (inf_le_left : s16e_two_cent X H ≤ X) (fun x hx => hx.1)
    (s16e_two_cent_inf_fixIrr F hE₀ hE₁) ?_, hlt⟩
  calc Nat.card ↥X ≤ 2 * Nat.card ↥(s16e_two_cent X H) * Nat.card ↥H := hcard
    _ = Nat.card ↥(s16e_two_cent X H) * (2 * Nat.card ↥H) := by ring
    _ ≤ Nat.card ↥(s16e_two_cent X H) * Nat.card ↥(s16e_two_fixIrr X H) :=
        Nat.mul_le_mul_left _ h2

theorem s16e_two_equiv_aut_of_outer (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (hlt : H < s16e_two_fixIrr X H) (hAut : Nat.card (MulAut ↥H) ≤ 2 * Nat.card ↥H) :
    Nonempty (↥(s16e_two_fixIrr X H) ≃* MulAut ↥H) := by
  have hNX : s16e_two_fixIrr X H ≤ X := fun x hx => hx.1
  let φ : ↥(s16e_two_fixIrr X H) →* MulAut ↥H :=
    (s16e_two_conjAut F).comp (Subgroup.inclusion hNX)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hn' : Subgroup.inclusion hNX n ∈ (s16e_two_conjAut F).ker := hn
    rw [s16e_two_conjAut_ker, Subgroup.mem_subgroupOf] at hn'
    have hnK : (n : MulAut W) ∈ s16e_two_cent X H := hn'
    have h1 : (n : MulAut W) ∈ s16e_two_cent X H ⊓ s16e_two_fixIrr X H := ⟨hnK, n.2⟩
    rw [s16e_two_cent_inf_fixIrr F hE₀ hE₁, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hbij : Function.Bijective φ :=
    hφ.bijective_of_nat_card_le (hAut.trans (s16e_twoO_two_mul_le hlt))
  exact ⟨MulEquiv.ofBijective φ hbij⟩

theorem s16e_two_sup_H_of_inner {Γ : Type*} [Group Γ] {X H : Subgroup Γ} (hHX : H ≤ X)
    (hinn : ∀ y ∈ X, ∃ h₀ ∈ H, ∀ h ∈ H, y * h * y⁻¹ = h₀ * h * h₀⁻¹) :
    (X ⊓ Subgroup.centralizer (H : Set Γ)) ⊔ H = X := by
  apply le_antisymm
  · exact sup_le inf_le_left hHX
  · intro y hy
    obtain ⟨h₀, hh₀, hconj⟩ := hinn y hy
    have hk : h₀⁻¹ * y ∈ X ⊓ Subgroup.centralizer (H : Set Γ) := by
      refine ⟨X.mul_mem (X.inv_mem (hHX hh₀)) hy, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro h hh
      calc h * (h₀⁻¹ * y) = h₀⁻¹ * (h₀ * h * h₀⁻¹) * y := by group
        _ = h₀⁻¹ * (y * h * y⁻¹) * y := by rw [hconj h hh]
        _ = (h₀⁻¹ * y) * h := by group
    have h := Subgroup.mul_mem_sup hh₀ hk
    rw [mul_inv_cancel_left, sup_comm] at h
    exact h

theorem s16e_two_direct_of_sup_H {Γ : Type*} [Group Γ] {X H : Subgroup Γ} (hHX : H ≤ X)
    (hsimple : IsSimpleGroup ↥H) (hperf : ⁅H, H⁆ = H)
    (hsup : (X ⊓ Subgroup.centralizer (H : Set Γ)) ⊔ H = X) :
    IsInternalDirect (X ⊓ Subgroup.centralizer (H : Set Γ)) H X := by
  refine ⟨?_, ?_, hsup⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro k hk h hh
    have h1 : h * k = k * h := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2 h hh
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 h1.symm
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxH⟩ := hx
    have hxc : x ∈ Subgroup.centralizer (H : Set Γ) := (Subgroup.mem_inf.1 hxK).2
    have hz : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)
    haveI := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥H) with h | h
    · rw [h, Subgroup.mem_bot] at hz
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hz
    · exfalso
      have hcomm : ⁅H, H⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hz₁ : (⟨g₁, hg₁⟩ : ↥H) ∈ Subgroup.center ↥H := by rw [h]; trivial
        have := Subgroup.mem_center_iff.1 hz₁ ⟨g₂, hg₂⟩
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val this).symm
      rw [hperf] at hcomm
      obtain ⟨y, hy⟩ := exists_ne (1 : ↥H)
      have hy1 : (y : Γ) ∈ (⊥ : Subgroup Γ) := hcomm ▸ y.2
      rw [Subgroup.mem_bot] at hy1
      exact hy (Subtype.ext hy1)

theorem s16e_two_sup_H_of_autFromGroup (F : Cfg2Setting X H J₀ J₁) (hHX : H ≤ X)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (hA : Z391.AutFromGroup H J₀) (h3 : 3 ∣ Nat.card ↥(s16e_two_cent X H)) :
    s16e_two_cent X H ⊔ H = X := by
  apply le_antisymm
  · exact sup_le inf_le_left hHX
  · intro x hx
    obtain ⟨k, hk, hy⟩ := s16e_twoO_exists_stab F hE₀ hE₁ h3 hx
    have hkX : k ∈ X := (Subgroup.mem_inf.1 hk).1
    have hyX : k * x ∈ X := X.mul_mem hkX hx
    let φ : ↥J₀ ≃* ↥J₀ :=
      (MulEquiv.subgroupMap (k * x) J₀).trans (MulEquiv.subgroupCongr hy)
    obtain ⟨l, hl, hφ⟩ := hA φ
    have hφ' : ∀ u ∈ J₀, (k * x) u = l u := fun u hu => hφ ⟨u, hu⟩
    have hlX : l ∈ X := hHX hl
    have hcX : l⁻¹ * (k * x) ∈ X := X.mul_mem (X.inv_mem hlX) hyX
    have hcfix : ∀ u ∈ J₀, (l⁻¹ * (k * x)) u = u := by
      intro u hu
      show l⁻¹ ((k * x) u) = u
      rw [hφ' u hu]
      exact l.symm_apply_apply u
    have hcK : l⁻¹ * (k * x) ∈ s16e_two_cent X H :=
      s16e_twoO_mem_cent_of_fix F hcX hcfix
    have hcomm : ∀ k' ∈ s16e_two_cent X H, ∀ h ∈ H, k' * h = h * k' := fun k' hk' h hh =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk').2 h hh).symm
    have hxe : x = (k⁻¹ * (l⁻¹ * (k * x))) * l := by
      have h1 : (l⁻¹ * (k * x)) * l = l * (l⁻¹ * (k * x)) := hcomm _ hcK l hl
      calc x = k⁻¹ * (l * (l⁻¹ * (k * x))) := by group
        _ = k⁻¹ * ((l⁻¹ * (k * x)) * l) := by rw [h1]
        _ = (k⁻¹ * (l⁻¹ * (k * x))) * l := by group
    rw [hxe]
    exact Subgroup.mul_mem_sup ((s16e_two_cent X H).mul_mem ((s16e_two_cent X H).inv_mem hk) hcK)
      hl

theorem s16e_two_inner_of_aut (F : Cfg2Setting X H J₀ J₁)
    (hinn : ∀ φ : MulAut ↥H, ∃ h₀ : ↥H, ∀ h : ↥H, φ h = h₀ * h * h₀⁻¹) :
    ∀ y ∈ X, ∃ h₀ ∈ H, ∀ h ∈ H, y * h * y⁻¹ = h₀ * h * h₀⁻¹ := by
  intro y hy
  let φ : MulAut ↥H :=
    (MulEquiv.subgroupMap (MulAut.conj y) H).trans (MulEquiv.subgroupCongr (F.norm y hy))
  obtain ⟨h₀, hh₀⟩ := hinn φ
  refine ⟨(h₀ : MulAut W), h₀.2, fun h hh => ?_⟩
  have h1 := congrArg (fun z : ↥H => (z : MulAut W)) (hh₀ ⟨h, hh⟩)
  exact h1

theorem s16e_two_card_le_of_normalizer (F : Cfg2Setting X H J₀ J₁) (hHX : H ≤ X)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (h3 : 3 ∣ Nat.card ↥(s16e_two_cent X H)) :
    Nat.card ↥X ≤ Nat.card ↥(s16e_two_cent X H) *
      Nat.card ↥(normalizer (autSub H J₀ : Set (MulAut ↥J₀))) := by
  have hKX : s16e_two_cent X H ≤ X := inf_le_left
  have hsurj : ∀ r : ↥(autSub X J₀),
      ∃ g : ↥(stabSub J₀), (g : MulAut W) ∈ X ∧ resHom J₀ g = (r : MulAut ↥J₀) :=
    fun r => mem_autSub.1 r.2
  choose s hsX hsr using hsurj
  let Φ : ↥(s16e_two_cent X H) × ↥(autSub X J₀) → ↥X := fun p =>
    ⟨(p.1 : MulAut W) * ((s p.2 : ↥(stabSub J₀)) : MulAut W),
      X.mul_mem (hKX p.1.2) (hsX p.2)⟩
  have hΦ : Function.Surjective Φ := by
    intro x
    obtain ⟨k, hk, hy⟩ := s16e_twoO_exists_stab F hE₀ hE₁ h3 x.2
    have hkX : k ∈ X := hKX hk
    have hyX : k * (x : MulAut W) ∈ X := X.mul_mem hkX x.2
    let gy : ↥(stabSub J₀) := ⟨k * (x : MulAut W), s16e_twoO_mem_stabSub hy⟩
    let r : ↥(autSub X J₀) := ⟨resHom J₀ gy, mem_autSub.2 ⟨gy, hyX, rfl⟩⟩
    have hsr' : resHom J₀ (s r) = resHom J₀ gy := hsr r
    have hσJ : ∀ u, ((s r : ↥(stabSub J₀)) : MulAut W) u ∈ J₀ ↔ u ∈ J₀ :=
      mem_stabSub.1 (s r).2
    have hcX : k * (x : MulAut W) * ((s r : ↥(stabSub J₀)) : MulAut W)⁻¹ ∈ X :=
      X.mul_mem hyX (X.inv_mem (hsX r))
    have hcfix : ∀ u ∈ J₀,
        (k * (x : MulAut W) * ((s r : ↥(stabSub J₀)) : MulAut W)⁻¹) u = u := by
      intro u hu
      have hv : ((s r : ↥(stabSub J₀)) : MulAut W)⁻¹ u ∈ J₀ := by
        refine (hσJ _).1 ?_
        rw [MulAut.apply_inv_self]
        exact hu
      have h1 : ((s r : ↥(stabSub J₀)) : MulAut W)
            (((s r : ↥(stabSub J₀)) : MulAut W)⁻¹ u) =
          (k * (x : MulAut W)) (((s r : ↥(stabSub J₀)) : MulAut W)⁻¹ u) :=
        congrArg (fun φ : MulAut ↥J₀ => (φ ⟨_, hv⟩ : W)) hsr'
      show (k * (x : MulAut W)) (((s r : ↥(stabSub J₀)) : MulAut W)⁻¹ u) = u
      rw [← h1]
      exact MulAut.apply_inv_self _ _ _
    have hcK : k * (x : MulAut W) * ((s r : ↥(stabSub J₀)) : MulAut W)⁻¹ ∈
        s16e_two_cent X H := s16e_twoO_mem_cent_of_fix F hcX hcfix
    refine ⟨(⟨k⁻¹ * (k * (x : MulAut W) * ((s r : ↥(stabSub J₀)) : MulAut W)⁻¹),
      (s16e_two_cent X H).mul_mem ((s16e_two_cent X H).inv_mem hk) hcK⟩, r), ?_⟩
    apply Subtype.ext
    show k⁻¹ * (k * (x : MulAut W) * ((s r : ↥(stabSub J₀)) : MulAut W)⁻¹) *
      ((s r : ↥(stabSub J₀)) : MulAut W) = (x : MulAut W)
    group
  have h1 : Nat.card ↥X ≤ Nat.card (↥(s16e_two_cent X H) × ↥(autSub X J₀)) :=
    Nat.card_le_card_of_surjective Φ hΦ
  rw [Nat.card_prod] at h1
  have h2 : Nat.card ↥(autSub X J₀) ≤
      Nat.card ↥(normalizer (autSub H J₀ : Set (MulAut ↥J₀))) :=
    Subgroup.card_le_of_le (s16e_twoO_autSub_le_normalizer F)
  exact h1.trans (Nat.mul_le_mul_left _ h2)

theorem s16e_two_equiv_normalizer_of_outer (F : Cfg2Setting X H J₀ J₁) (hHX : H ≤ X)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (hlt : H < s16e_two_fixIrr X H)
    (hN : Nat.card ↥(normalizer (autSub H J₀ : Set (MulAut ↥J₀))) ≤ 2 * Nat.card ↥H) :
    Nonempty (↥(s16e_two_fixIrr X H) ≃* ↥(normalizer (autSub H J₀ : Set (MulAut ↥J₀)))) := by
  have hNstab : s16e_two_fixIrr X H ≤ stabSub J₀ := fun n hn =>
    s16e_twoO_mem_stabSub (hn.2 J₀ F.irr₀)
  let ρ : ↥(s16e_two_fixIrr X H) →* MulAut ↥J₀ :=
    (resHom J₀).comp (Subgroup.inclusion hNstab)
  have hρmem : ∀ n, ρ n ∈ normalizer (autSub H J₀ : Set (MulAut ↥J₀)) := fun n =>
    s16e_twoO_autSub_le_normalizer F (mem_autSub.2 ⟨Subgroup.inclusion hNstab n, n.2.1, rfl⟩)
  let ρ' : ↥(s16e_two_fixIrr X H) →*
      ↥(normalizer (autSub H J₀ : Set (MulAut ↥J₀))) := ρ.codRestrict _ hρmem
  have hρ'inj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : ρ n = 1 := congrArg Subtype.val hn
    have hfix : ∀ u ∈ J₀, (n : MulAut W) u = u := by
      intro u hu
      exact congrArg (fun φ : MulAut ↥J₀ => (φ ⟨u, hu⟩ : W)) h1
    have hnK : (n : MulAut W) ∈ s16e_two_cent X H :=
      s16e_twoO_mem_cent_of_fix F n.2.1 hfix
    have h2 : (n : MulAut W) ∈ s16e_two_cent X H ⊓ s16e_two_fixIrr X H := ⟨hnK, n.2⟩
    rw [s16e_two_cent_inf_fixIrr F hE₀ hE₁, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hbij : Function.Bijective ρ' :=
    hρ'inj.bijective_of_nat_card_le (hN.trans (s16e_twoO_two_mul_le hlt))
  exact ⟨MulEquiv.ofBijective ρ' hbij⟩

end Outer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
