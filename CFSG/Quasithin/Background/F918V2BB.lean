module

public import CFSG.Quasithin.Background.F918H0
public import CFSG.Quasithin.Background.F918XN2
public import CFSG.Quasithin.Background.F918XN3
public import CFSG.Quasithin.Background.F918XAL2Six
public import CFSG.Quasithin.Background.FFC2Core

public section

namespace CFSG.Quasithin.Z391

open CFSG.Quasithin

theorem realizesVia_descend {V₁ Y : Type*} [CommGroup V₁] [CommGroup Y] {D : FFModel}
    {H : Subgroup (MulAut V₁)} {H' : Subgroup (MulAut Y)} {U Z : Subgroup V₁}
    {π : D.Gam →* ↥H} (e : ↥H →* ↥H') (he : Function.Surjective e) (q : ↥U →* Y)
    (hq : Function.Surjective q) (hqk : ∀ u : ↥U, q u = 1 ↔ (u : V₁) ∈ Z)
    (heq : ∀ (h : ↥H) (u : ↥U) (hu : ((h : ↥H) : MulAut V₁) (u : V₁) ∈ U),
      q ⟨((h : ↥H) : MulAut V₁) (u : V₁), hu⟩ = ((e h : ↥H') : MulAut Y) (q u))
    (h : D.RealizesVia H U Z π) : D.RealizesVia H' ⊤ ⊥ (e.comp π) := by
  obtain ⟨hsurj, hZU, hkerle, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  let q' : ↥U →* ↥(⊤ : Subgroup Y) := (Subgroup.topEquiv (G := Y)).symm.toMonoidHom.comp q
  have hq' : Function.Surjective q' := fun y => by
    obtain ⟨u, hu⟩ := hq (y : Y)
    exact ⟨u, Subtype.ext hu⟩
  have hker : q'.ker ≤ β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h1 : q u = 1 := by
      have := congrArg Subtype.val hu
      simpa [q'] using this
    exact (hβk u).2 ((hqk u).1 h1)
  let β' : ↥(⊤ : Subgroup Y) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (q'.liftOfSurjective hq') ⟨β, hker⟩
  have hβ' : ∀ u, β' (q' u) = β u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨β, hker⟩ u
  refine ⟨he.comp hsurj, bot_le, hkerle, fun _ _ _ => trivial, fun _ z hz => ?_, hsec, hkerinv, β',
    ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact map_one _
  · intro z
    obtain ⟨u, hu⟩ := hβs z
    exact ⟨q' u, by rw [hβ']; exact hu⟩
  · intro y
    obtain ⟨u, rfl⟩ := hq' y
    rw [hβ', hβk, ← hqk, Subgroup.mem_bot]
    exact ⟨fun h1 => by simp [q', h1], fun h1 => by simpa [q'] using h1⟩
  · intro γ y m hy hm hym
    obtain ⟨u, rfl⟩ := hq' y
    rw [hβ'] at hym
    have hu : ((π γ : ↥H) : MulAut V₁) (u : V₁) ∈ U := hUinv _ _ u.2
    have h1 := hβe γ u m hu hm hym
    have h2 : (⟨(((e.comp π) γ : ↥H') : MulAut Y) ((q' u : ↥(⊤ : Subgroup Y)) : Y), hy⟩ :
        ↥(⊤ : Subgroup Y)) = q' ⟨((π γ : ↥H) : MulAut V₁) (u : V₁), hu⟩ :=
      Subtype.ext (heq (π γ) u hu).symm
    rw [h2, hβ']
    exact h1

theorem twoClassMod_altDn6 {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (hq : CFSG.IsQuasisimple ↥H) {π : ↥(alternatingGroup (Fin 6)) →* ↥H}
    (hπ : (FFModel.altDn 6).RealizesVia H ⊤ ⊥ π) : F918X.TwoClassMod H := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hbij : Function.Bijective π :=
    F918X.AL2.bijective_of_surjective_of_quasisimple (A := ↥(alternatingGroup (Fin 6))) hq π hπ.1
  let e : ↥(alternatingGroup (Fin 6)) ≃* ↥H := MulEquiv.ofBijective π hbij
  have hle : Sp4Inf.conjAlt6.range.map
      (MulAut.congr e : MulAut ↥(alternatingGroup (Fin 6)) →* MulAut ↥H) ≤ F918X.realized H := by
    rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
    exact F918X.AL2.mem_realized_conj hπ e (fun γ => rfl) τ (Sp4Inf.conjAlt6 τ)
      (fun γ => Sp4Inf.coe_conjAlt6 τ γ)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_map_equiv, Sp4Inf.index_range_conjAlt6] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem twoClassMod_a7Four {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    (hq : CFSG.IsQuasisimple ↥H)
    {α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    {π : ↥(alternatingGroup (Fin 7)) →* ↥H}
    (hπ : (FFModel.a7Four α).RealizesVia H ⊤ ⊥ π) : F918X.TwoClassMod H := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hbij : Function.Bijective π :=
    F918X.AL2.bijective_of_surjective_of_quasisimple (A := ↥(alternatingGroup (Fin 7))) hq π hπ.1
  let e : ↥(alternatingGroup (Fin 7)) ≃* ↥H := MulEquiv.ofBijective π hbij
  have hZ : Subgroup.center ↥H = ⊥ :=
    F918X.AL2.center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp))
  refine F918X.twoClassMod_of_inner hZ ?_
  have hcard := FFC.card_mulAut_alternating_le (n := 7) (Or.inr le_rfl)
  rwa [← Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr e.toEquiv]

theorem injective_and_twoClass_of_d35Five
    {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V : Subgroup W}
    {G : Type} [Group G] (φ : G ≃* ↥L) {Y : Type} [CommGroup Y] [Finite Y]
    (q : ↥V →* Y) (hq : Function.Surjective q)
    (hqk : ∀ v : ↥V, q v = 1 ↔ (v : W) ∈ V ⊓ fixV L) (ρ : G →* MulAut Y)
    (heq : ∀ (g : G) (v : ↥V) (hv : ((φ g : ↥L) : MulAut W) (v : W) ∈ V),
      q ⟨((φ g : ↥L) : MulAut W) (v : W), hv⟩ = ρ g (q v))
    (hL : CFSG.IsQuasisimple ↥L) (hnt : ∃ g, ρ g ≠ 1) (h5 : D35Five L V) :
    Function.Injective ρ ∧ F918X.TwoClassMod ρ.range := by
  let e : ↥L →* ↥ρ.range := ρ.rangeRestrict.comp φ.symm.toMonoidHom
  have he : Function.Surjective e :=
    MonoidHom.rangeRestrict_surjective ρ |>.comp φ.symm.surjective
  have heq' : ∀ (h : ↥L) (u : ↥V) (hu : ((h : ↥L) : MulAut W) (u : W) ∈ V),
      q ⟨((h : ↥L) : MulAut W) (u : W), hu⟩ = ((e h : ↥ρ.range) : MulAut Y) (q u) := by
    intro h u hu
    have := heq (φ.symm h) u (by simpa using hu)
    simpa [e] using this
  have hqr : CFSG.IsQuasisimple ↥ρ.range := by
    obtain ⟨g, hg⟩ := hnt
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hL he ⟨φ g, fun h1 => hg ?_⟩
    have h2 : (ρ.rangeRestrict g : MulAut Y) = 1 := by
      have := congrArg Subtype.val h1
      simpa [e] using this
    simpa using h2
  have hinj_of : ∀ {Γ' : Type} [Group Γ'] (π_D : Γ' →* ↥L), Function.Surjective π_D →
      Function.Injective (e.comp π_D) → Function.Injective ρ := by
    intro Γ' _ π_D hs hi
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨γ, hγ⟩ := hs (φ g)
    have h1 : (e.comp π_D) γ = 1 := by
      show e (π_D γ) = 1
      rw [hγ]
      apply Subtype.ext
      simpa [e] using hg
    have hγ1 : γ = 1 := (injective_iff_map_eq_one _).1 hi γ h1
    rw [hγ1, map_one] at hγ
    exact φ.injective (hγ.symm.trans (map_one φ).symm)
  rcases h5 with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  · have h' := realizesVia_descend e he q hq hqk heq' hπ
    exact ⟨hinj_of π hπ.1 (h'.injective_of_faithful (FFModel.nat_faithful _)),
      F918X.SLTwist.twoClassMod_of_natural (by norm_num) h'⟩
  · have h' := realizesVia_descend e he q hq hqk heq' hπ
    exact ⟨hinj_of π hπ.1 (h'.injective_of_faithful (FFModel.nat_faithful _)),
      (F918X.twoClassMod_centralData_of_binaryNaturalSp4
        (H := ρ.range) (n := n) ⟨K, inferInstance, inferInstance, hK, e.comp π, h'⟩).1⟩
  · have h' := realizesVia_descend e he q hq hqk heq' hπ
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact ⟨hinj_of π hπ.1 (F918X.AL2.bijective_of_surjective_of_quasisimple
      (A := ↥(alternatingGroup (Fin 6))) hqr _ h'.1).1, twoClassMod_altDn6 hqr h'⟩
  · have h' := realizesVia_descend e he q hq hqk heq' hπ
    exact ⟨hinj_of π hπ.1 (h'.injective_of_faithful (FFModel.nat_faithful _)),
      F918X.SLTwist.twoClassMod_of_natural (by norm_num) h'⟩
  · have h' := realizesVia_descend e he q hq hqk heq' hπ
    exact ⟨hinj_of π hπ.1 (h'.injective_of_faithful (FFModel.nat_faithful _)),
      F918X.SLTwist.twoClassMod_of_natural (by norm_num) h'⟩
  · have h' := realizesVia_descend e he q hq hqk heq' hπ
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact ⟨hinj_of π hπ.1 (F918X.AL2.bijective_of_surjective_of_quasisimple
      (A := ↥(alternatingGroup (Fin 7))) hqr _ h'.1).1, twoClassMod_a7Four hqr h'⟩

end CFSG.Quasithin.Z391
