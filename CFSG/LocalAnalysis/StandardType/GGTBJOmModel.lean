module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvMoves
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModelLift
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModelMap
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModelWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggTBJ_om_stdModel_of_mulEquiv {p r₀ : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hpq' : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1)
    {R : Type} [Group R] (eR : R ≃* ↥(orthDerived Q))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* R)
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ R
      (Set.range (MulAut.conj : R →* MulAut R)) L' ψ₀ A) :
    ∃ (r : ℕ) (E : Subgroup (V ≃ₗ[K] V))
      (Δ : OrthTorus.TBJOmData Q p E r)
      (hE : E ≤ orthDerived Q)
      (σ : (Fin r → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A),
      (∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f)) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hψ, hker, hperf, hAab, hAI, -, h3, hsc⟩ := hA
  have hcpL := hcp L' ψ₀ hψ hker hperf
  obtain ⟨Λ, E₀, hΛn, hΛinj, -, hE₀, hAΛ, hE₀ab, hcard, hscE⟩ :=
    exists_liftConj_comap_model hp subset_rfl hZ hψ hker hperf hcpL hAab hAI hsc
  set E₁ : Subgroup ↥(orthDerived Q) := E₀.map eR.toMonoidHom with hE₁
  have hE₁ab : IsElemAbelian p E₁ := hE₀ab.map eR.toMonoidHom
  have hE₁sc := selfCent_map_mulEquiv eR hscE
  have hcard₁ : Nat.card E₁ = Nat.card A := (natCard_map_mulEquiv eR E₀).trans hcard
  have hne₁ : ∃ b ∈ E₁, b ≠ 1 := exists_ne_one_of_pow_le_card hp (hcard₁ ▸ h3)
  obtain ⟨hAΩ, hApow, hAcomm, hmax, hneA⟩ := map_subtype_hyps E₁ hE₁ab hne₁ hE₁sc
  obtain ⟨r, τ, F, D, i₁, i₂, i₃, c', θ, hτF, hinj, hrange, hdim, hcp', hfix', hT', hroots,
    hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsign, hnoFix, hexFix⟩ :=
    OrthTorus.exists_torus_blocks hp2 hpq' hQ hT hAΩ hApow hAcomm hmax hneA
  let Δ : OrthTorus.TBJOmData Q p (E₁.map (orthDerived Q).subtype) r :=
    { τ := τ, F := F, D := D, c := c', θ := θ, τ_eq := hτF, τ_inj := hinj, τ_range := hrange,
      finrank_D := hdim, c_pow := hcp', c_fix := hfix', c_twist := hT', c_roots := hroots,
      θ_inj := hθinj, θ_range := hθrange, θ_act := hθact, normalizer := hnorm,
      swapMove := hswap, dinvMove := hdinv, signMove := hsign, noFixed := hnoFix,
      exFixed := hexFix }
  have hEΩ : E₁.map (orthDerived Q).subtype ≤ orthDerived Q := hAΩ
  have hτΩ : ∀ f, Δ.τ f ∈ orthDerived Q := fun f => by
    have h : Δ.τ f ∈ Δ.τ.range := ⟨f, rfl⟩
    rw [hrange] at h
    exact hEΩ h
  have hrangeΩ : Δ.τ.range = (E₀.map eR.toMonoidHom).map (orthDerived Q).subtype := hrange
  have hiff := mem_range_iff_mem_comap_model eR E₀ Δ.τ hτΩ hrangeΩ
  set τ' : (Fin r → Multiplicative (ZMod p)) →* R :=
    eR.symm.toMonoidHom.comp (Δ.τ.codRestrict (orthDerived Q) hτΩ) with hτ'
  have hτ'E : ∀ f, τ' f ∈ E₀ := fun f => (hiff _).mpr ⟨f, rfl⟩
  have hrange' : ∀ x ∈ E₀, x ∈ τ'.range := fun x hx => (hiff x).mp hx
  have hτ'inj : Function.Injective τ' := fun f g hfg =>
    hinj (congrArg Subtype.val (eR.symm.injective hfg))
  obtain ⟨σ, hσψ, hσp⟩ := exists_section_of_centerPrime hp hψ hker hcpL
    (fun v : Fin r → Multiplicative (ZMod p) => ReflInner.pow_eq_one_of_zmod v) τ'
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_of_range_comap Λ hΛinj hAΛ τ' hτ'inj
    (fun f => (hE₀ _).mp (hτ'E f)) fun x hx => hrange' x ((hE₀ x).mpr hx)
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f => by
    rw [hΘ f, ← hΛn (σ f), hσψ f]
  refine ⟨r, E₁.map (orthDerived Q).subtype, Δ, hEΩ, σ, Θ, fun f => ?_, hΘσ, fun n hn => ?_⟩
  · rw [hσψ f]
    rfl
  · refine ggTorusWeylElt_of_section hker σ hσp (fun a ha => ?_) fun v => ?_
    · obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      exact ⟨f, by rw [← hΘσ f, hf]⟩
    · obtain ⟨f', hf'⟩ := exists_torus_conj_of_normalizer Λ hΛn hE₀ τ' hτ'E hrange' hn v
      exact ⟨f', by rw [hσψ v, hσψ f']; exact hf'⟩

theorem ggTBJ_om_stdModel {p m r₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : 3 ≤ m)
    (hpq : p ∣ Nat.card K - 1 ∨ (Odd m ∧ p ∣ Nat.card K + 1))
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RMinus K m b c)
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ (OrthRest.RMinus K m b c)
      (Set.range (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)))
      L' ψ₀ A) :
    ∃ (r : ℕ) (E : Subgroup ((LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K)))
      (Δ : OrthTorus.TBJOmData (TableBOrth.qMinusForm K m b c) p E r)
      (hE : E ≤ orthDerived (TableBOrth.qMinusForm K m b c))
      (σ : (Fin r → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A),
      (∀ f, ψ₀ (σ f) = (OrthTorus.rMinusEquiv K m b c).symm (Δ.τΩ hE f)) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∃ v : LargeEvenMinusIdx m → K, v ≠ 0 ∧ ∀ a ∈ E, a v = v) := by
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus hp hp2 hm hbc
  obtain ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW⟩ :=
    ggTBJ_om_stdModel_of_mulEquiv (V := LargeEvenMinusIdx m → K)
      (Q := TableBOrth.qMinusForm K m b c) hp hp2
      (TableBOrth.nondegenerate_qMinusForm m hbc) ((OrthTorus.charSum_qMinusForm m hbc).2 hm)
      (hpq.imp id fun h => h.2) (OrthTorus.rMinusEquiv K m b c) hZ hcp ψ₀ A hA
  refine ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW, Δ.exFixed ?_⟩
  rw [(OrthTorus.charSum_qMinusForm m hbc).1]
  exact modEq_neg_one_charSum hpq

theorem ggTBJ_om_stdModel_nf
    {p m r₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : 3 ≤ m)
    (hme : Even m) (hpq : p ∣ Nat.card K + 1)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RMinus K m b c)
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ (OrthRest.RMinus K m b c)
      (Set.range (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)))
      L' ψ₀ A) :
    ∃ (r : ℕ) (E : Subgroup ((LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K)))
      (Δ : OrthTorus.TBJOmData (TableBOrth.qMinusForm K m b c) p E r)
      (hE : E ≤ orthDerived (TableBOrth.qMinusForm K m b c))
      (σ : (Fin r → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A),
      (∀ f, ψ₀ (σ f) = (OrthTorus.rMinusEquiv K m b c).symm (Δ.τΩ hE f)) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ v : LargeEvenMinusIdx m → K, (∀ a ∈ E, a v = v) → v = 0) := by
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus hp hp2 hm hbc
  obtain ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW⟩ :=
    ggTBJ_om_stdModel_of_mulEquiv (V := LargeEvenMinusIdx m → K)
      (Q := TableBOrth.qMinusForm K m b c) hp hp2
      (TableBOrth.nondegenerate_qMinusForm m hbc) ((OrthTorus.charSum_qMinusForm m hbc).2 hm)
      (Or.inr hpq) (OrthTorus.rMinusEquiv K m b c) hZ hcp ψ₀ A hA
  refine ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW, Δ.noFixed ?_⟩
  rw [(OrthTorus.charSum_qMinusForm m hbc).1]
  exact modEq_one_charSum hme hpq

theorem ggTBJ_omPlus_stdModel_nf
    {p m r₀ : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hm : 3 ≤ m) (hpq : p ∣ Nat.card K - 1)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RPlus K (m + 1))
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ (OrthRest.RPlus K (m + 1))
      (Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →* MulAut (OrthRest.RPlus K (m + 1))))
      L' ψ₀ A) :
    ∃ (r : ℕ) (E : Subgroup ((Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K]
        (Fin (m + 1) ⊕ Fin (m + 1) → K)))
      (Δ : OrthTorus.TBJOmData (TableBOrth.qPlusForm K (m + 1)) p E r)
      (hE : E ≤ orthDerived (TableBOrth.qPlusForm K (m + 1)))
      (σ : (Fin r → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A),
      (∀ f, ψ₀ (σ f) = (OrthTorus.rPlusEquiv K (Nat.le_add_left 1 m)).symm (Δ.τΩ hE f)) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ v : Fin (m + 1) ⊕ Fin (m + 1) → K, (∀ a ∈ E, a v = v) → v = 0) := by
  have hp2 : p ≠ 2 := OrthTorus.ne_two_of_dvd_card_sub_one hpq
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m + 1)
  obtain ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW⟩ :=
    ggTBJ_om_stdModel_of_mulEquiv (V := Fin (m + 1) ⊕ Fin (m + 1) → K)
      (Q := TableBOrth.qPlusForm K (m + 1)) hp hp2
      (TableBOrth.nondegenerate_qPlusForm (m + 1))
      (OrthTorus.exists_totallySingular_qPlusForm (n := m) hm)
      (Or.inl hpq) (OrthTorus.rPlusEquiv K (Nat.le_add_left 1 m)) hZ hcp ψ₀ A hA
  refine ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW, Δ.noFixed ?_⟩
  rw [OrthTorus.charSum_qPlusForm m]
  simpa using (OrthTorus.modEq_one_of_dvd Nat.card_pos hpq).pow (m + 1)

end CFSG.StandardType

end
