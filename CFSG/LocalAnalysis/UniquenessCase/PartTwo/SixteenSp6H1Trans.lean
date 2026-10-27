module

public import CFSG.Quasithin.Background.B4L3Coord
import CFSG.Quasithin.Background.JonesParshallBasic
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Adapters.RankTwoModelTransports Subgroup
open scoped Matrix

theorem s16sp_realizes_congr {K K' : Type} [Field K] [Field K'] (σ : K ≃+* K') {n : ℕ}
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (h : (FFModel.nat (StatedSp n K)).Realizes H U Z) :
    (FFModel.nat (StatedSp n K')).Realizes H U Z := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSp n K)) rfl rfl hπ
  obtain ⟨hπs, hZU, -, hUinv, hZinv, -, -, -⟩ := hπ
  let ε : ↥(StatedSp n K) ≃* ↥(StatedSp n K') :=
    ((glCongr (ι := Fin n ⊕ Fin n) σ).subgroupMap (StatedSp n K)).trans
      (MulEquiv.subgroupCongr (glCongr_statedSp (φ := σ) n))
  let π' : ↥(StatedSp n K') →* ↥H := π.comp ε.symm.toMonoidHom
  let Φβ : Multiplicative (Fin n ⊕ Fin n → K) →* Multiplicative (Fin n ⊕ Fin n → K') :=
    AddMonoidHom.toMultiplicative
      (AddMonoidHom.compLeft (σ.toRingHom.toAddMonoidHom) (Fin n ⊕ Fin n))
  let β' : ↥U →* Multiplicative (Fin n ⊕ Fin n → K') := Φβ.comp β
  have hΦβ : ∀ x : Multiplicative (Fin n ⊕ Fin n → K),
      Φβ x = Multiplicative.ofAdd (σ ∘ Multiplicative.toAdd x) := by
    intro x
    simp only [Φβ, AddMonoidHom.coe_toMultiplicative, Function.comp_apply]
    rfl
  have hΦβinj : Function.Injective Φβ := by
    intro x y hxy
    rw [hΦβ, hΦβ] at hxy
    have h1 := Multiplicative.ofAdd.injective hxy
    apply Multiplicative.toAdd.injective
    funext i
    exact σ.injective (congrFun h1 i)
  have hΦβs : Function.Surjective Φβ := by
    intro y
    refine ⟨Multiplicative.ofAdd (σ.symm ∘ Multiplicative.toAdd y), ?_⟩
    rw [hΦβ, toAdd_ofAdd]
    have hcomp : (σ ∘ ⇑(σ.symm) ∘ Multiplicative.toAdd y : Fin n ⊕ Fin n → K') =
        Multiplicative.toAdd y := by
      funext i
      simp
    rw [hcomp, ofAdd_toAdd]
  have hβ's : Function.Surjective β' := hΦβs.comp hβs
  have hβ'k : ∀ u : ↥U, β' u = 1 ↔ (u : W) ∈ Z := by
    intro u
    show Φβ (β u) = 1 ↔ (u : W) ∈ Z
    exact (map_eq_one_iff Φβ hΦβinj).trans (hβk u)
  have hΦβ_act : ∀ (A : GL (Fin n ⊕ Fin n) K) (v : Multiplicative (Fin n ⊕ Fin n → K)),
      Φβ (Multiplicative.ofAdd
          ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ Multiplicative.toAdd v)) =
      Multiplicative.ofAdd
        (((glCongr (ι := Fin n ⊕ Fin n) σ A : GL (Fin n ⊕ Fin n) K') :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K') *ᵥ
          (σ ∘ Multiplicative.toAdd v)) := by
    intro A v
    rw [hΦβ]
    apply congrArg Multiplicative.ofAdd
    funext i
    have h := RingHom.map_mulVec (σ.toRingHom)
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Multiplicative.toAdd v) i
    have hco : ((glCongr (ι := Fin n ⊕ Fin n) σ A : GL (Fin n ⊕ Fin n) K') :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K') =
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map σ := glCongr_coe σ A
    rw [hco]
    simpa using h
  have hεA : ∀ A : ↥(StatedSp n K),
      ((ε A : ↥(StatedSp n K')) : GL (Fin n ⊕ Fin n) K') =
      glCongr (ι := Fin n ⊕ Fin n) σ (A : GL (Fin n ⊕ Fin n) K) := by
    intro A
    change (glCongr (ι := Fin n ⊕ Fin n) σ (A : GL (Fin n ⊕ Fin n) K) :
      GL (Fin n ⊕ Fin n) K') = _
    rfl
  have hΦβ_natAct : ∀ (A : ↥(StatedSp n K)) (v : Multiplicative (Fin n ⊕ Fin n → K)),
      Φβ (natAct (StatedSp n K) A v) =
      natAct (StatedSp n K') (ε A) (Φβ v) := by
    intro A v
    change Φβ (Multiplicative.ofAdd
        (((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
          Multiplicative.toAdd v)) =
      Multiplicative.ofAdd
        ((((ε A : ↥(StatedSp n K')) : GL (Fin n ⊕ Fin n) K') :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K') *ᵥ Multiplicative.toAdd (Φβ v))
    conv_rhs => rw [hΦβ]
    rw [toAdd_ofAdd, hεA A]
    exact hΦβ_act (A : GL (Fin n ⊕ Fin n) K) v
  have hβ'e : ∀ (γ : ↥(StatedSp n K')) (u : ↥U)
      (hu : ((π' γ : ↥H) : MulAut W) (u : W) ∈ U),
      β' ⟨((π' γ : ↥H) : MulAut W) (u : W), hu⟩ =
        (FFModel.nat (StatedSp n K')).act γ (β' u) := by
    intro γ u hu
    have h1 := hβe (ε.symm γ) u hu
    have h2 : β' ⟨((π' γ : ↥H) : MulAut W) (u : W), hu⟩ =
        Φβ ((FFModel.nat (StatedSp n K)).act (ε.symm γ) (β u)) := by
      show Φβ (β ⟨((π (ε.symm γ) : ↥H) : MulAut W) (u : W), hu⟩) =
        Φβ ((FFModel.nat (StatedSp n K)).act (ε.symm γ) (β u))
      rw [h1]
    have h3 : Φβ ((FFModel.nat (StatedSp n K)).act (ε.symm γ) (β u)) =
        (FFModel.nat (StatedSp n K')).act γ (Φβ (β u)) := by
      have h1' := hΦβ_natAct (ε.symm γ) (β u)
      rw [show ε (ε.symm γ) = γ from MulEquiv.apply_symm_apply ε γ] at h1'
      simpa only [FFModel.nat] using h1'
    rw [h2, h3]
    rfl
  have hs : (FFModel.nat (StatedSp n K')).sec = ⊤ := rfl
  have hk : (FFModel.nat (StatedSp n K')).ker = ⊥ := rfl
  let β_quot : ↥U →* (FFModel.nat (StatedSp n K')).Sec :=
    ((CFSG.Quasithin.JonesParshall.secEquivAmb
      (FFModel.nat (StatedSp n K')) hs hk).symm).toMonoidHom.comp β'
  have hβ_quots : Function.Surjective β_quot :=
    (EquivLike.surjective
      (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).symm).comp hβ's
  have hβ_quotk : ∀ u : ↥U, β_quot u = 1 ↔ (u : W) ∈ Z := by
    intro u
    show (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).symm
      (β' u) = 1 ↔ _
    exact (MulEquiv.map_eq_one_iff
      (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).symm).trans
      (hβ'k u)
  have hβ_quota : ∀ (γ : ↥(StatedSp n K')) (u : ↥U)
      (m : ↥(FFModel.nat (StatedSp n K')).sec)
      (hu : ((π' γ : ↥H) : MulAut W) (u : W) ∈ U)
      (hm : (FFModel.nat (StatedSp n K')).act γ (m : (FFModel.nat (StatedSp n K')).Amb) ∈
        (FFModel.nat (StatedSp n K')).sec),
      β_quot u = QuotientGroup.mk m →
        β_quot ⟨((π' γ : ↥H) : MulAut W) (u : W), hu⟩ =
          QuotientGroup.mk
            ⟨(FFModel.nat (StatedSp n K')).act γ (m : (FFModel.nat (StatedSp n K')).Amb), hm⟩ := by
    intro γ u m hu hm hβ
    have hm_eq : β' u = (m : (FFModel.nat (StatedSp n K')).Amb) := by
      have h := congrArg
        (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk) hβ
      change (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk)
          ((CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).symm
            (β' u)) =
        (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk)
          (QuotientGroup.mk m) at h
      have h1 : (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk)
          ((CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).symm
            (β' u)) = β' u :=
        MulEquiv.apply_symm_apply
          (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk) (β' u)
      have h2 : (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk)
          (QuotientGroup.mk m) = (m : (FFModel.nat (StatedSp n K')).Amb) :=
        CFSG.Quasithin.JonesParshall.secEquivAmb_mk
          (FFModel.nat (StatedSp n K')) hs hk m
      rw [h1, h2] at h
      exact h
    have h := hβ'e γ u hu
    rw [hm_eq] at h
    have he : (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).symm
        ((FFModel.nat (StatedSp n K')).act γ (m : (FFModel.nat (StatedSp n K')).Amb)) =
        QuotientGroup.mk
          ⟨(FFModel.nat (StatedSp n K')).act γ (m : (FFModel.nat (StatedSp n K')).Amb), hm⟩ := by
      apply (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).injective
      rw [MulEquiv.apply_symm_apply, CFSG.Quasithin.JonesParshall.secEquivAmb_mk]
    change (CFSG.Quasithin.JonesParshall.secEquivAmb (FFModel.nat (StatedSp n K')) hs hk).symm
        (β' ⟨((π' γ : ↥H) : MulAut W) (u : W), hu⟩) = _
    rw [h, he]
  refine ⟨π', ?_⟩
  refine ⟨?_, hZU, bot_le, hUinv, hZinv, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hπs y
    refine ⟨ε (x : ↥(StatedSp n K)), ?_⟩
    show π (ε.symm (ε (x : ↥(StatedSp n K)))) = y
    rw [show ε.symm (ε (x : ↥(StatedSp n K))) = (x : ↥(StatedSp n K)) from
      MulEquiv.symm_apply_apply ε (x : ↥(StatedSp n K))]
    exact hx
  · intro γ m _
    exact Subgroup.mem_top _
  · intro γ m hm
    simp only [FFModel.nat, Subgroup.mem_bot] at hm
    subst hm
    change natAct (StatedSp n K') (γ : ↥(StatedSp n K'))
      (1 : Multiplicative (Fin n ⊕ Fin n → K')) ∈
      (⊥ : Subgroup (Multiplicative (Fin n ⊕ Fin n → K')))
    rw [Subgroup.mem_bot]
    simp [natAct]
  · exact ⟨β_quot, hβ_quots, hβ_quotk, hβ_quota⟩

theorem s16sp_realizes_zmod2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (h : (FFModel.nat (StatedSp n K)).Realizes H U Z) :
    (FFModel.nat (StatedSp n (ZMod 2))).Realizes H U Z := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  exact s16sp_realizes_congr (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
