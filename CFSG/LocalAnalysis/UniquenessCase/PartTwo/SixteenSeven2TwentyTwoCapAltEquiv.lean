module

public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)

private theorem capAlt_constWeight_eq_evenWeightOnes (m : ℕ) :
    CFSG.Quasithin.constWeight m = CFSG.RankThree.PartTwo.evenWeightOnes m := by
  ext x
  rw [CFSG.RankThree.PartTwo.evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hx
    by_cases hm : Nonempty (Fin m)
    · obtain ⟨i₀⟩ := hm
      refine ⟨((x : Fin m → ZMod 2) i₀).val, funext fun i => ?_⟩
      simp [CFSG.RankThree.PartTwo.allOnes, hx i i₀]
    · refine ⟨0, funext fun i => ?_⟩
      exact absurd ⟨i⟩ hm
  · rintro ⟨k, hk⟩
    have hi : ∀ i, (x : Fin m → ZMod 2) i = (k : ZMod 2) := fun i => by
      rw [← hk]
      simp [CFSG.RankThree.PartTwo.allOnes]
    intro i j
    exact (hi i).trans (hi j).symm

private noncomputable def capAlt_heartEquivAlt (m : ℕ) :
    CFSG.Quasithin.AltHeart m ≃+ CFSG.RankThree.PartTwo.altHeart m :=
  QuotientAddGroup.quotientAddEquivOfEq (capAlt_constWeight_eq_evenWeightOnes m)

private theorem capAlt_heartEquivAlt_mk {m : ℕ}
    (x : ↥(CFSG.QuasithinUnique.evenWeight m)) :
    capAlt_heartEquivAlt m (QuotientAddGroup.mk x : CFSG.Quasithin.AltHeart m) =
      (QuotientAddGroup.mk x : CFSG.RankThree.PartTwo.altHeart m) :=
  QuotientAddGroup.quotientAddEquivOfEq_mk _ x

private theorem capAlt_heartEquivAlt_hAct {m : ℕ} (σ : Equiv.Perm (Fin m))
    (y : CFSG.Quasithin.AltHeart m) :
    capAlt_heartEquivAlt m (CFSG.Quasithin.C41Pf.AltN.hAct m σ y) =
      CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ
        (capAlt_heartEquivAlt m y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [CFSG.Quasithin.C41Pf.AltN.hAct_mk]
  simp only [capAlt_heartEquivAlt_mk, CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_mk]
  rw [show CFSG.Quasithin.permWeight m σ x =
      CFSG.RankThree.PartTwo.evenWeightPerm σ x from Subtype.ext (funext fun _ => rfl)]

theorem s16c167_altNatural_equiv {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {E : Subgroup W} {n : ℕ} (hn : 0 < n) (hE : AlternatingNatural L E ⊥ n) :
    ∃ (π : alternatingGroup (Fin n) →* ↥L) (ψ : ↥E ≃* Multiplicative (altHeart n)),
      Function.Surjective π ∧
      ∀ (γ : alternatingGroup (Fin n)) (u : ↥E)
        (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ E),
        ψ ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (ψ u))) := by
  obtain ⟨π, hπ⟩ := hE
  obtain ⟨hsurj, -, -, hUinv, -, hsecinv, -, β, hβsurj, hβker, hβeq⟩ := hπ
  let e : (↥(G6.coreMod n) ⧸ (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃*
      Multiplicative (AltHeart n) := CFSG.Quasithin.C124.altQuotEquiv n hn
  let β' : ↥E →* Multiplicative (AltHeart n) := e.toMonoidHom.comp β
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥E) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hβ'inj : Function.Injective β' := e.injective.comp hβinj
  have hβ'surj : Function.Surjective β' := e.surjective.comp hβsurj
  let βe : ↥E ≃* Multiplicative (AltHeart n) :=
    MulEquiv.ofBijective β' ⟨hβ'inj, hβ'surj⟩
  have hβ'e : ∀ (γ : alternatingGroup (Fin n)) (u : ↥E)
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ E),
      βe ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (βe u))) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
        (FFModel.altDn n).sec := hsecinv γ m m.2
    have h1 := hβeq γ u m hu hsec hmu
    change e (β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) =
      Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd (e (β u))))
    rw [h1, hmu]
    rfl
  let c : CFSG.Quasithin.AltHeart n ≃+ CFSG.RankThree.PartTwo.altHeart n :=
    capAlt_heartEquivAlt n
  let ψ : ↥E ≃* Multiplicative (altHeart n) := βe.trans (AddEquiv.toMultiplicative c)
  let π' : alternatingGroup (Fin n) →* ↥L :=
    { toFun := fun γ => π γ
      map_one' := map_one π
      map_mul' := fun a b => map_mul π a b }
  refine ⟨π', ψ, hsurj, ?_⟩
  intro γ u hu
  have hψu : Multiplicative.toAdd (ψ u) = c (Multiplicative.toAdd (βe u)) := rfl
  calc ψ ⟨((π' γ : ↥L) : MulAut W) (u : W), hu⟩
      = (AddEquiv.toMultiplicative c) (βe ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) := rfl
    _ = (AddEquiv.toMultiplicative c) (Multiplicative.ofAdd
          (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (βe u)))) := by rw [hβ'e γ u hu]
    _ = Multiplicative.ofAdd (c (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (βe u)))) := rfl
    _ = Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
          (c (Multiplicative.toAdd (βe u)))) :=
          congrArg (fun z => Multiplicative.ofAdd z)
            (capAlt_heartEquivAlt_hAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (βe u)))
    _ = Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (ψ u))) :=
          congrArg (fun z => Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n)) z)) hψu.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
