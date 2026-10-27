module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel
import CFSG.LocalAnalysis.StandardType.GGTBTorDatum

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Assembly TableB NbrInnerRest

theorem exists_innerModel_of_forall_inner {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    (hZ : Subgroup.center R = ⊥) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcpL : ¬ p ∣ Nat.card (Subgroup.center L'))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hinner : ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range)
    (hsc : GGTorusSelfCent p A) :
    ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ (e : R) (l : L'), ψ (Λ e l) = e * ψ l * e⁻¹) ∧ (∀ a ∈ A, ∃ e : R, Λ e = a) ∧
      IsElemAbelian p (A.comap Λ) ∧ Nat.card (A.comap Λ) = Nat.card A ∧
      (∀ g : R, (∀ e ∈ A.comap Λ, g * e = e * g) → g ^ p = 1 → g ∈ A.comap Λ) := by
  classical
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a := by
    intro a ha
    obtain ⟨x, hx⟩ := hinner a ha
    exact ⟨ψ x, (hΛn x).trans hx⟩
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  exact ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hE ▸ hEab, hE ▸ hcardE, hE ▸ hscE⟩

theorem exists_innerModel {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I) (hcp : GGCenterPrime p R)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent p A) :
    ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ (e : R) (l : L'), ψ (Λ e l) = e * ψ l * e⁻¹) ∧ (∀ a ∈ A, ∃ e : R, Λ e = a) ∧
      IsElemAbelian p (A.comap Λ) ∧ Nat.card (A.comap Λ) = Nat.card A ∧
      (∀ g : R, (∀ e ∈ A.comap Λ, g * e = e * g) → g ^ p = 1 → g ∈ A.comap Λ) := by
  classical
  unfold GGOutdiagPrime at hIp
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  have hinner : ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range := by
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    obtain ⟨x, hx⟩ := hψ e
    exact ⟨x, (hΛeq hx).symm.trans he⟩
  exact exists_innerModel_of_forall_inner hp hZ ψ hψ hker hcpL hA hinner hsc

end TwE6TB


open CFSG CFSG.Assembly

theorem ggCover_innerModel {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {R : Type} [Group R] (ψ : ↥X →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥X) (hZR : Subgroup.center R = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ∃ E : Subgroup R, IsElemAbelian p E ∧
      Nat.card E = Nat.card (ggGamma X hN).range ∧
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma X hN).range = E.map (ReflInner.liftConj ψ hψ hker) := by
  classical
  have hp : p.Prime := Fact.out
  have hcpX : ¬ p ∣ Nat.card (Subgroup.center ↥X) := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥X)) p hdvd
    have hzp : (z : ↥X) ^ p = 1 := by
      have h : z ^ p = 1 := by rw [← hz, pow_orderOf_eq_one]
      simpa using congrArg (fun w : ↥(Subgroup.center ↥X) => (w : ↥X)) h
    have hz1 : z = 1 := Subtype.ext (hZp (z : ↥X) z.2 hzp)
    rw [hz1, orderOf_one] at hz
    exact hp.ne_one hz.symm
  have hA : IsElemAbelian p (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hAinner : ∀ a ∈ (ggGamma X hN).range,
      a ∈ (MulAut.conj : ↥X →* MulAut ↥X).range := by
    rintro a ⟨b, rfl⟩
    obtain ⟨x, hxX, hx⟩ := hinner (b : G) b.2
    refine ⟨⟨x, hxX⟩, ?_⟩
    refine MulEquiv.ext fun y => Subtype.ext ?_
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe]
    exact (hx (y : G) y.2).symm
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hEab, hEcard, hEsc⟩ :=
    TwE6TB.exists_innerModel_of_forall_inner hp hZR ψ hψ hker hcpX hA hAinner
      (ggTorusSelfCent_ggGamma hN hSC)
  let E : Subgroup R := (ggGamma X hN).range.comap Λ
  have hΛid : Λ = ReflInner.liftConj ψ hψ hker := by
    apply MonoidHom.ext
    intro r
    obtain ⟨x, hx⟩ := hψ r
    rw [hΛeq hx, ReflInner.liftConj_eq hψ hker hx]
  have hArange : (ggGamma X hN).range = E.map Λ := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he⟩ := hAΛ a ha
      refine Subgroup.mem_map.mpr ⟨e, ?_, he⟩
      change Λ e ∈ (ggGamma X hN).range
      rw [he]
      exact ha
    · rintro ⟨e, he, rfl⟩
      exact he
  refine ⟨E, hEab, hEcard, hEsc, ?_⟩
  rw [← hΛid]
  exact hArange

end CFSG.StandardType
