module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Orbit
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Lift
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Diagonal

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {Γ : Type u} [Group Γ] {p : ℕ} {A W Z : Subgroup Γ} {T : Γ → Subgroup Γ}

namespace Setup

theorem liftOf_inf_eq_bot [Finite Γ] [Z.Normal] (h : Setup p A W Z T)
    {J : Subgroup (Γ ⧸ Z)} (hJ : J ∈ simpleComponents (W.map (QuotientGroup.mk' Z))) {a : Γ}
    (ha : a ∈ A) (haZ : ∀ z ∈ Z, z * a = a * z) (hmove : a ∉ stab A Z J) :
    liftOf W Z J ⊓ Z = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hmove (one_mem _)
  have hAs := h.isASimple
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hJg : ∀ g ∈ A, J.map (MulAut.conj (QuotientGroup.mk' Z g)).toMonoidHom ∈
      simpleComponents (W.map (QuotientGroup.mk' Z)) := fun g hg =>
    map_conj_mem_simpleComponents hJ (hAs.1 (Subgroup.mem_map_of_mem _ hg))
  have hR : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h.pow_eq_one ha) ha1
  have hdisj : stab A Z J ⊓ Subgroup.zpowers a = ⊥ :=
    CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le hp hR
      fun hle => hmove (hle (Subgroup.mem_zpowers a))
  have hne : ∀ g g' : Subgroup.zpowers a, g ≠ g' →
      J.map (MulAut.conj (QuotientGroup.mk' Z g)).toMonoidHom ≠
        J.map (MulAut.conj (QuotientGroup.mk' Z g')).toMonoidHom := by
    intro g g' hgg' hJeq
    apply hgg'
    have e1 := congrArg (fun K => K.map (MulAut.conj (QuotientGroup.mk' Z (g : Γ)⁻¹)).toMonoidHom)
      hJeq
    simp only [map_conj_map_conj, ← map_mul] at e1
    rw [inv_mul_cancel, map_one, map_conj_one] at e1
    have hmem : (g : Γ)⁻¹ * g' ∈ stab A Z J ⊓ Subgroup.zpowers a := by
      refine Subgroup.mem_inf.mpr ⟨mem_stab_iff.mpr
        ⟨mul_mem (inv_mem (hzA g.2)) (hzA g'.2), ?_⟩, mul_mem (inv_mem g.2) g'.2⟩
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact e1.symm
    rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem
  have hcomm : ∀ g g' : Subgroup.zpowers a, g ≠ g' → ∀ x ∈ liftOf W Z J, ∀ y ∈ liftOf W Z J,
      Commute ((g : Γ) * x * (g : Γ)⁻¹) ((g' : Γ) * y * (g' : Γ)⁻¹) := by
    intro g g' hgg' x hx y hy
    have hbot := commutator_liftOf_eq_bot h (hJg g (hzA g.2)) (hJg g' (hzA g'.2)) (hne g g' hgg')
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact (Subgroup.mem_centralizer_iff.mp (hbot (conj_mem_liftOf h (hzA g.2) hx)) _
      (conj_mem_liftOf h (hzA g'.2) hy)).symm
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_diagonalHom (liftOf W Z J) hcomm
  have hPW : δ.range ≤ W := by
    rintro _ ⟨w, rfl⟩
    exact hδ2 W (fun g hg x hx => h.conj_mem_W (hzA hg) (liftOf_le hx)) w
  have : Group.IsPerfect (liftOf W Z J) :=
    Subgroup.isPerfect_iff.mpr (commutator_liftOf_self h.le h.central hJ.1
      (commutator_eq_self_of_mem_simpleComponents hJ))
  have : Group.IsPerfect δ.range := Group.IsPerfect.range δ
  have hPperf : ⁅δ.range, δ.range⁆ = δ.range := Subgroup.commutator_eq_self
  obtain ⟨hTW, hTZ, hfix⟩ := h.fixed a ha ha1
  have hPS : ∀ x ∈ δ.range, ∃ z ∈ Z, ∃ s ∈ T a, x = z * s := by
    rintro _ ⟨w, rfl⟩
    refine hfix _ (Subgroup.mem_inf.mpr ⟨hPW ⟨w, rfl⟩, ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp (hδ1 w)).symm
  have hPT : δ.range ≤ T a :=
    calc δ.range = ⁅δ.range, δ.range⁆ := hPperf.symm
      _ ≤ ⁅T a, T a⁆ := commutator_le_of_forall_mul h.le hTW h.central hPS
      _ ≤ T a := Subgroup.commutator_le_of_le le_rfl le_rfl
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨hzV, hzZ⟩ := Subgroup.mem_inf.mp hz
  have hfixz : a * z * a⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr (haZ z hzZ).symm
  have hpow := hδ3 ⟨z, hzV⟩ hfixz
  rw [hR] at hpow
  have hzp : z ^ p ∈ T a ⊓ Z :=
    Subgroup.mem_inf.mpr ⟨hPT ⟨⟨z, hzV⟩, hpow⟩, pow_mem hzZ p⟩
  rw [hTZ, Subgroup.mem_bot] at hzp
  have hdvd1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have hdvd2 : orderOf z ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W (liftOf_le hzV)
  have hord : orderOf z = 1 :=
    Nat.Coprime.eq_one_of_dvd (h.coprime.coprime_dvd_left hdvd1) hdvd2
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord)

theorem false_of_liftOf_inf_eq_bot [Finite Γ] [Z.Normal] (h : Setup p A W Z T)
    (hbot : ∀ J ∈ simpleComponents (W.map (QuotientGroup.mk' Z)), liftOf W Z J ⊓ Z = ⊥) :
    False := by
  classical
  have hAs := h.isASimple
  have : Fintype (simpleComponents (W.map (QuotientGroup.mk' Z))) := Fintype.ofFinite _
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup Γ, Y = ⨆ i : simpleComponents (W.map (QuotientGroup.mk' Z)),
    liftOf W Z i.1 := ⟨_, rfl⟩
  let φ : ∀ i : simpleComponents (W.map (QuotientGroup.mk' Z)), ↥(liftOf W Z i.1) →* Γ :=
    fun i => (liftOf W Z i.1).subtype
  have hcomm : Pairwise fun i j : simpleComponents (W.map (QuotientGroup.mk' Z)) =>
      ∀ x y, Commute (φ i x) (φ j y) := by
    intro i j hij x y
    have hbot' := commutator_liftOf_eq_bot h i.2 j.2 fun e => hij (Subtype.ext e)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot'
    exact (Subgroup.mem_centralizer_iff.mp (hbot' x.2) y y.2).symm
  let Δ := MonoidHom.noncommPiCoprod φ hcomm
  have hrange : Δ.range = Y := by
    rw [hY, MonoidHom.noncommPiCoprod_range]
    exact iSup_congr fun i => Subgroup.range_subtype _
  have hmapi : ∀ i : simpleComponents (W.map (QuotientGroup.mk' Z)),
      (liftOf W Z i.1).map (QuotientGroup.mk' Z) = i.1 := fun i =>
    map_liftOf i.2.1 (commutator_eq_self_of_mem_simpleComponents i.2)
  have hind : iSupIndep fun i : simpleComponents (W.map (QuotientGroup.mk' Z)) =>
      ((QuotientGroup.mk' Z).comp (φ i)).range := by
    have : (fun i : simpleComponents (W.map (QuotientGroup.mk' Z)) =>
        ((QuotientGroup.mk' Z).comp (φ i)).range) = fun i => (i.1 : Subgroup (Γ ⧸ Z)) := by
      funext i
      rw [MonoidHom.range_comp, show (φ i).range = liftOf W Z i.1 from Subgroup.range_subtype _,
        hmapi i]
    rw [this]
    exact iSupIndep_simpleComponents hAs
  have hinj : ∀ i : simpleComponents (W.map (QuotientGroup.mk' Z)),
      Function.Injective ((QuotientGroup.mk' Z).comp (φ i)) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : Γ) ∈ liftOf W Z i.1 ⊓ Z :=
      Subgroup.mem_inf.mpr ⟨x.2, mk'_eq_one_iff.mp hx⟩
    rw [hbot i.1 i.2, Subgroup.mem_bot] at hx1
    exact Subtype.ext hx1
  have hΔinj : Function.Injective ((QuotientGroup.mk' Z).comp Δ) := by
    rw [MonoidHom.comp_noncommPiCoprod φ (f := QuotientGroup.mk' Z) (hcomm := hcomm)]
    exact MonoidHom.injective_noncommPiCoprod_of_iSupIndep _ hind hinj
  have hYZ : Y ⊓ Z = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hyY, hyZ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨f, rfl⟩ : y ∈ Δ.range := hrange ▸ hyY
    have h1 : (QuotientGroup.mk' Z).comp Δ f = (QuotientGroup.mk' Z).comp Δ 1 := by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_one, map_one]
      exact mk'_eq_one_iff.mpr hyZ
    rw [hΔinj h1, map_one]
    exact one_mem _
  have hYW : Y ≤ W := hY ▸ iSup_le fun i => liftOf_le
  have hmapY : Y.map (QuotientGroup.mk' Z) = W.map (QuotientGroup.mk' Z) := by
    rw [hY, Subgroup.map_iSup]
    calc _ = ⨆ i : simpleComponents (W.map (QuotientGroup.mk' Z)), (i.1 : Subgroup (Γ ⧸ Z)) :=
          iSup_congr hmapi
      _ = W.map (QuotientGroup.mk' Z) := by
          have := hAs.iSup_components
          rwa [iSup_subtype'] at this
  have hcover : ∀ w ∈ W, ∃ z ∈ Z, ∃ y ∈ Y, w = z * y := by
    intro w hw
    have hw' : QuotientGroup.mk' Z w ∈ Y.map (QuotientGroup.mk' Z) := by
      rw [hmapY]
      exact Subgroup.mem_map_of_mem _ hw
    obtain ⟨y, hy, hyw⟩ := hw'
    exact ⟨w * y⁻¹, mem_of_mk'_eq hyw.symm, y, hy, by group⟩
  have hWY : W ≤ Y :=
    calc W = ⁅W, W⁆ := h.perfect.symm
      _ ≤ ⁅Y, Y⁆ := commutator_le_of_forall_mul h.le hYW h.central hcover
      _ ≤ Y := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hZY : Z ≤ Y ⊓ Z := le_inf (h.le.trans hWY) le_rfl
  rw [hYZ] at hZY
  exact h.ne_bot (eq_bot_iff.mpr hZY)

end Setup

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral
