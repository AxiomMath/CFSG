module

public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.F918H0
public import CFSG.Quasithin.Background.F918XAL2Six
public import CFSG.Quasithin.Background.F918XN2
public import CFSG.Quasithin.Background.F918XN3
public import CFSG.Quasithin.Background.FFC2Core
public import CFSG.Quasithin.EmptyFaithful.SmithD391Twist
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Quasithin.F918X CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Models

variable {Y : Type} [CommGroup Y] {H : Subgroup (MulAut Y)}

theorem twoClassMod_of_alt6 {π : ↥(alternatingGroup (Fin 6)) →* ↥H}
    (hπ : (FFModel.altDn 6).RealizesVia H ⊤ ⊥ π) : TwoClassMod H := by
  have hbij : Function.Bijective π :=
    ⟨hπ.injective_of_faithful (FFC.altDn_faithful (by norm_num)), hπ.1⟩
  let e : ↥(alternatingGroup (Fin 6)) ≃* ↥H := MulEquiv.ofBijective π hbij
  have hle : Sp4Inf.conjAlt6.range.map
      (MulAut.congr e : MulAut ↥(alternatingGroup (Fin 6)) →* MulAut ↥H) ≤ realized H := by
    rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
    exact AL2.mem_realized_conj hπ e (fun γ => rfl) τ (Sp4Inf.conjAlt6 τ)
      (fun γ => Sp4Inf.coe_conjAlt6 τ γ)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_map_equiv, Sp4Inf.index_range_conjAlt6] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem twoClassMod_of_a7Four
    {α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    {π : (FFModel.a7Four α).Gam →* ↥H} (hπ : (FFModel.a7Four α).RealizesVia H ⊤ ⊥ π) :
    TwoClassMod H := by
  have hbij : Function.Bijective π :=
    ⟨hπ.injective_of_faithful (FFC.a7Four_faithful α), hπ.1⟩
  let e : ↥(alternatingGroup (Fin 7)) ≃* ↥H := MulEquiv.ofBijective π hbij
  have hZ : Subgroup.center ↥H = ⊥ :=
    AL2.center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp))
  have : Finite ↥H := Finite.of_equiv _ e.toEquiv
  refine twoClassMod_of_inner hZ ?_
  have hcard := FFC.card_mulAut_alternating_le (n := 7) (Or.inr le_rfl)
  rwa [← Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr e.toEquiv]

end Models

section Transport

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V : Subgroup W}
  {Γ : Type*} [Group Γ] {Q : Type} [CommGroup Q] [MulDistribMulAction Γ Q] {Λ : Subgroup Γ}
  {Vt : Subgroup Q} (hVt : ∀ l : ↥Λ, ∀ v ∈ Vt, l • v ∈ Vt)

theorem actAut_injective_of_realizesVia {D : FFModel} (hDf : D.Faithful) {π₀ : D.Gam →* ↥Λ}
    (hπ₀ : Function.Surjective π₀)
    (hR : D.RealizesVia (actAut Λ Vt hVt).range ⊤ ⊥ ((actAut Λ Vt hVt).rangeRestrict.comp π₀)) :
    Function.Injective (actAut Λ Vt hVt) := by
  have hinj := hR.injective_of_faithful hDf
  intro l l' hll'
  obtain ⟨γ, rfl⟩ := hπ₀ l
  obtain ⟨γ', rfl⟩ := hπ₀ l'
  have : ((actAut Λ Vt hVt).rangeRestrict.comp π₀) γ =
      ((actAut Λ Vt hVt).rangeRestrict.comp π₀) γ' := Subtype.ext hll'
  rw [hinj this]

theorem twoClass_injective_of_d35Five (h5 : D35Five L V) (ψ : ↥L →* ↥Λ)
    (hψ : Function.Surjective ψ) (f : ↥V →* ↥Vt) (hf : Function.Surjective f)
    (hfker : ∀ u : ↥V, f u = 1 ↔ (u : W) ∈ V ⊓ fixV L)
    (hfeq : ∀ (h : ↥L) (u : ↥V) (hu : (h : MulAut W) (u : W) ∈ V),
      f ⟨_, hu⟩ = actAut Λ Vt hVt (ψ h) (f u)) :
    Function.Injective (actAut Λ Vt hVt) ∧ TwoClassMod (actAut Λ Vt hVt).range := by
  have key : ∀ {D : FFModel} {π₀ : D.Gam →* ↥L}, D.RealizesVia L V (V ⊓ fixV L) π₀ →
      D.RealizesVia (actAut Λ Vt hVt).range ⊤ ⊥
        ((actAut Λ Vt hVt).rangeRestrict.comp (ψ.comp π₀)) :=
    fun hR => realizesVia_actAut hVt hR ψ hψ f hf hfker hfeq
  have hsurj : ∀ {D : FFModel} {π₀ : D.Gam →* ↥L}, D.RealizesVia L V (V ⊓ fixV L) π₀ →
      Function.Surjective (ψ.comp π₀) := fun hR => hψ.comp hR.1
  rcases h5 with ⟨n, K, _, _, hK, π₀, hR⟩ | ⟨n, K, _, _, hK, π₀, hR⟩ | ⟨π₀, hR⟩ |
      ⟨K, _, _, hK, π₀, hR⟩ | ⟨K, _, _, hK, π₀, hR⟩ | ⟨α, π₀, hR⟩
  · exact ⟨actAut_injective_of_realizesVia hVt (FFModel.nat_faithful _) (hsurj hR) (key hR),
      SLTwist.twoClassMod_of_natural (by norm_num) (key hR)⟩
  · refine ⟨actAut_injective_of_realizesVia hVt (FFModel.nat_faithful _) (hsurj hR) (key hR), ?_⟩
    exact (twoClassMod_centralData_of_binaryNaturalSp4 ⟨K, inferInstance, inferInstance, hK, _,
      key hR⟩).1
  · exact ⟨actAut_injective_of_realizesVia hVt (FFC.altDn_faithful (by norm_num)) (hsurj hR)
      (key hR), twoClassMod_of_alt6 (key hR)⟩
  · exact ⟨actAut_injective_of_realizesVia hVt (FFModel.nat_faithful _) (hsurj hR) (key hR),
      SLTwist.twoClassMod_of_natural (by norm_num) (key hR)⟩
  · exact ⟨actAut_injective_of_realizesVia hVt (FFModel.nat_faithful _) (hsurj hR) (key hR),
      SLTwist.twoClassMod_of_natural (by norm_num) (key hR)⟩
  · exact ⟨actAut_injective_of_realizesVia hVt (FFC.a7Four_faithful α) (hsurj hR) (key hR),
      twoClassMod_of_a7Four (key hR)⟩

end Transport

end CFSG.Quasithin.SmithD391
