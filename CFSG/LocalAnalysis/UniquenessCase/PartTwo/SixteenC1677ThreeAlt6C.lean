module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAlt6A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {W : Type} [CommGroup W]

private lemma s168e3_alt6C_two_mul_le {Γ : Type*} [Group Γ] [Finite Γ] {H N : Subgroup Γ}
    (hlt : H < N) : 2 * Nat.card H ≤ Nat.card N := by
  have h1 : Nat.card H ∣ Nat.card N := Subgroup.card_dvd_of_le hlt.le
  have h2 : Nat.card H < Nat.card N := Subgroup.card_lt_of_lt hlt
  by_contra hcon
  have h3 : Nat.card N < 2 * Nat.card H := not_le.1 hcon
  have := Nat.eq_of_dvd_of_lt_two_mul (Nat.card_pos.ne') h1 h3
  omega

private lemma s168e3_alt6C_mem_stabSub {W : Type} [CommGroup W] {U : Subgroup W}
    {g : MulAut W} (hg : U.map g.toMonoidHom = U) : g ∈ stabSub U := by
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

private lemma s168e3_alt6C_autSub_le_normalizer {W : Type} [CommGroup W]
    {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X H J₀ J₁) :
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

theorem s168e3_alt6_equiv_aut [Finite W] {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X H J₀ J₁) (hHX : H ≤ X) (hA : UC22.IsAlt ↥H 6)
    (hn₀ : AlternatingNatural H J₀ ⊥ 6) (hn₁ : AlternatingNatural H J₁ ⊥ 6)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (htrans : ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H, ∃ g ∈ X, I₂ = I₁.map g.toMonoidHom)
    (ht : ∃ t ∈ X, t ^ 2 = 1 ∧ t ≠ 1 ∧ rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hne : ∀ ψ ∈ Subgroup.centralizer (H : Set (MulAut W)), J₀.map ψ.toMonoidHom ≠ J₁) :
    Nonempty (↥X ≃* MulAut ↥H) := by
  classical
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  have hirr : irrSet H = {J₀, J₁} := s168e3_alt6_irr_eq_pair F hne
  have hJ₀ne : J₀ ≠ ⊥ := by
    obtain ⟨-, hirrJ⟩ := F.irr₀
    rw [F.fix, inf_bot_eq] at hirrJ
    exact hirrJ.1.ne'
  have hJ01 : J₀ ≠ J₁ := by
    intro h
    have h1 : J₀ ⊓ J₁ = J₀ := by rw [h, inf_idem]
    rw [F.inf_eq] at h1
    exact hJ₀ne h1.symm
  have hcard_irr : Nat.card ↥(irrSet H) = 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_two]
    exact ⟨J₀, J₁, hJ01, hirr⟩
  have hcent_bot : s16e_two_cent X H = ⊥ := by
    apply le_antisymm _ bot_le
    intro k hk
    have hkX : k ∈ X := (Subgroup.mem_inf.1 hk).1
    have hkc : k ∈ Subgroup.centralizer (H : Set (MulAut W)) := (Subgroup.mem_inf.1 hk).2
    have hfix₀ : J₀.map k.toMonoidHom = J₀ := by
      have h := s16e_two_map_mem_irrSet F hkX F.irr₀
      rw [hirr] at h
      rcases h with h | h
      · exact h
      · exact absurd h (hne k hkc)
    have hfix₁ : J₁.map k.toMonoidHom = J₁ := by
      have h := s16e_two_map_mem_irrSet F hkX F.irr₁
      rw [hirr] at h
      rcases h with h | h
      · exfalso
        exact hJ01 (s16e_two_map_injective k (h.trans hfix₀.symm)).symm
      · exact h
    rw [Subgroup.mem_bot]
    exact s16e_two_eq_one_of_fixes F hE₀ hE₁ hkc hfix₀ hfix₁
  have hconj_inj : Function.Injective (s16e_two_conjAut F) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ (s16e_two_conjAut F).ker := hx
    rw [s16e_two_conjAut_ker, Subgroup.mem_subgroupOf] at hx'
    rw [hcent_bot, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hker : (s16e_two_irrAct F).ker = (s16e_two_fixIrr X H).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      refine ⟨x.2, fun I hI => ?_⟩
      have h1 := congrArg (fun σ : Equiv.Perm ↥(irrSet H) => (σ ⟨I, hI⟩ : Subgroup W)) hx
      simpa [s16e_two_irrAct_apply] using h1
    · rintro ⟨-, hfix⟩
      apply Equiv.ext
      intro I
      apply Subtype.ext
      simpa [s16e_two_irrAct_apply] using hfix (I : Subgroup W) I.2
  have hperm_card : Nat.card (Equiv.Perm ↥(irrSet H)) = 2 := by
    rw [Nat.card_perm, hcard_irr]
    norm_num [Nat.factorial]
  obtain ⟨g, hgX, hgmap⟩ := htrans J₀ F.irr₀ J₁ F.irr₁
  have hfg_ne : s16e_two_irrAct F ⟨g, hgX⟩ ≠ 1 := by
    intro h
    have h1 := congrArg (fun σ : Equiv.Perm ↥(irrSet H) => (σ ⟨J₀, F.irr₀⟩ : Subgroup W)) h
    simp only [Equiv.Perm.one_apply, s16e_two_irrAct_apply] at h1
    exact hJ01 (hgmap.trans h1).symm
  have hnt : Nontrivial ↥((s16e_two_irrAct F).range) :=
    ⟨⟨1, Subgroup.one_mem _⟩,
      ⟨s16e_two_irrAct F ⟨g, hgX⟩, MonoidHom.mem_range.mpr ⟨⟨g, hgX⟩, rfl⟩⟩,
      fun h => hfg_ne (Subtype.ext_iff.mp h).symm⟩
  have hrange_ge : 2 ≤ Nat.card ↥((s16e_two_irrAct F).range) := by
    have h1 : 1 < Nat.card ↥((s16e_two_irrAct F).range) :=
      (Finite.one_lt_card_iff_nontrivial (α := ↥((s16e_two_irrAct F).range))).mpr hnt
    omega
  have hrange_dvd : Nat.card ↥((s16e_two_irrAct F).range) ∣ 2 := by
    have h1 := Subgroup.card_subgroup_dvd_card ((s16e_two_irrAct F).range)
    rwa [hperm_card] at h1
  have hrange : Nat.card ↥((s16e_two_irrAct F).range) = 2 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hrange_dvd) hrange_ge
  have hcardX : Nat.card ↥X = Nat.card ↥(s16e_two_fixIrr X H) * 2 := by
    have h1 := Subgroup.card_ker_mul_card_range (s16e_two_irrAct F)
    rw [hker] at h1
    have h2 : Nat.card ↥((s16e_two_fixIrr X H).subgroupOf X) =
        Nat.card ↥(s16e_two_fixIrr X H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show s16e_two_fixIrr X H ≤ X from fun x hx => hx.1)).toEquiv
    rw [h2, hrange] at h1
    exact h1.symm
  have hU : StableUnder H J₀ := (s16e_two_isIrrOn_of_mem F F.irr₀).2.1
  have hK₀stab : s16e_two_fixIrr X H ≤ stabSub J₀ :=
    fun n hn => s168e3_alt6C_mem_stabSub (hn.2 J₀ F.irr₀)
  have hρmem : ∀ n : ↥(s16e_two_fixIrr X H),
      (resHom J₀).comp (Subgroup.inclusion hK₀stab) n ∈
        Subgroup.normalizer (autSub H J₀ : Set (MulAut ↥J₀)) :=
    fun n => s168e3_alt6C_autSub_le_normalizer F
      (mem_autSub.2 ⟨Subgroup.inclusion hK₀stab n, n.2.1, rfl⟩)
  let ρ : ↥(s16e_two_fixIrr X H) →*
      ↥(Subgroup.normalizer (autSub H J₀ : Set (MulAut ↥J₀))) :=
    ((resHom J₀).comp (Subgroup.inclusion hK₀stab)).codRestrict _ hρmem
  have hρ_inj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : ((resHom J₀).comp (Subgroup.inclusion hK₀stab)) n = 1 :=
      congrArg Subtype.val hn
    have hfix : ∀ u ∈ J₀, (n : MulAut W) u = u := fun u hu =>
      congrArg (fun φ : MulAut ↥J₀ => (φ ⟨u, hu⟩ : W)) h1
    have hUt : J₀ ≤ fixV (Subgroup.zpowers (n : MulAut W)) := by
      intro u hu
      rw [mem_fixV]
      intro z hz
      exact Subgroup.zpowers_le.2
        (show (n : MulAut W) ∈ MulAction.stabilizer (MulAut W) u from hfix u hu) hz
    have hnK : (n : MulAut W) ∈ s16e_two_cent X H :=
      ⟨n.2.1, s16c167_cfg2_cent_of_fix F hU hJ₀ne n.2.1 hUt⟩
    have h2 : (n : MulAut W) ∈ s16e_two_cent X H ⊓ s16e_two_fixIrr X H := ⟨hnK, n.2⟩
    rw [s16e_two_cent_inf_fixIrr F hE₀ hE₁, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hNcard : Nat.card ↥(Subgroup.normalizer (autSub H J₀ : Set (MulAut ↥J₀))) = 720 := by
    obtain ⟨e⟩ := s16e_two_alt6_normalizer_isSym hn₀
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    norm_num [Nat.card_fin, Nat.factorial]
  have hK₀le : Nat.card ↥(s16e_two_fixIrr X H) ≤ 720 := by
    have h1 := Nat.card_le_card_of_injective ρ hρ_inj
    rwa [hNcard] at h1
  obtain ⟨t, htX, ht2, ht1, htrk⟩ := ht
  have h4₀ : 4 ≤ rk ↥J₀ := s16e_two_alt_rk_ge (n := 6) (by norm_num) hn₀
  have h4₁ : 4 ≤ rk ↥J₁ := s16e_two_alt_rk_ge (n := 6) (by norm_num) hn₁
  have htK₀ : t ∈ s16e_two_fixIrr X H := by
    refine ⟨htX, fun I hI => ?_⟩
    by_contra hmove
    have h1 := s16e_two_rk_comm_of_moves F htX hI hmove
    have h2 := s16e_two_rk_irr_ge F hE₀ (m := 4) h4₀ h4₁ I hI
    omega
  have hinv : ∀ h ∈ H, h ≠ 1 → h ^ 2 = 1 →
      4 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers h)) := by
    intro h hh hh1 hh2
    have h0 := s16e_two_alt_comm_rk_ge (n := 6) (by norm_num) hn₀ hh hh1 hh2
    have h1 := s16e_two_alt_comm_rk_ge (n := 6) (by norm_num) hn₁ hh hh1 hh2
    have h2 := s16e_two_rk_comm_ge F hh h0 h1
    omega
  have htH : t ∉ H := fun hh => by
    have h := hinv t hh ht1 ht2
    omega
  have hHcard : Nat.card ↥H = 360 := by
    rw [s15k_six_alt_card hA (by norm_num : 2 ≤ 6)]
    norm_num [Nat.factorial]
  have hHK₀ : H ≤ s16e_two_fixIrr X H := s16e_two_le_fixIrr hHX
  have hHK₀_lt : H < s16e_two_fixIrr X H :=
    lt_of_le_of_ne hHK₀ (fun h => htH (h.symm ▸ htK₀))
  have h2H : 2 * Nat.card ↥H ≤ Nat.card ↥(s16e_two_fixIrr X H) :=
    s168e3_alt6C_two_mul_le hHK₀_lt
  have hK₀ge : 720 ≤ Nat.card ↥(s16e_two_fixIrr X H) := by
    rw [hHcard] at h2H
    omega
  have hK₀card : Nat.card ↥(s16e_two_fixIrr X H) = 720 := le_antisymm hK₀le hK₀ge
  have hXcard : Nat.card ↥X = 1440 := by
    rw [hcardX, hK₀card]
  have hAutH : Nat.card (MulAut ↥H) = 1440 := by
    obtain ⟨e⟩ := hA
    exact CFSG.QuasithinUnique.DoubleA3.card_mulAut_alt6 e
  have hbij : Function.Bijective (s16e_two_conjAut F) :=
    hconj_inj.bijective_of_nat_card_le (le_of_eq (by rw [hAutH, hXcard]))
  exact ⟨MulEquiv.ofBijective (s16e_two_conjAut F) hbij⟩

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
