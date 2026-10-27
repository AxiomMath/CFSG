module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDAssembly
public import CFSG.LocalAnalysis.StandardType.GGTBTorInnModel
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsFrame
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsTorus
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsCent
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGTBTorRel
public import CFSG.LocalAnalysis.StandardType.Marking

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RelDNs

open CFSG.Assembly QuadraticMap Module
open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

theorem conj_frameTorusFull_of_conj_e {F V : Type} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ}
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}
    {u : Fin k → V} {c t : F} [Fact (Irreducible (OmNsRootGen.framePoly t))]
    (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {g : ↥(orthDerived Q)} (π : Equiv.Perm (Fin k)) (ε : Fin k → ℤ)
    (hconj : ∀ a, g * e a * g⁻¹ = e (π a) ^ ε a) (x : Fin k → normOne t) (hx : x ^ p = 1) :
    g * frameTorusFull hF hQ hT x * g⁻¹ =
      frameTorusFull hF hQ hT (fun i => x (π.symm i) ^ ε (π.symm i)) := by
  classical
  let σ : (Fin k → normOne t) →* (Fin k → normOne t) :=
    { toFun := fun y i => y (π.symm i) ^ ε (π.symm i)
      map_one' := by
        funext i
        simp
      map_mul' := by
        intro y y'
        funext i
        simp [mul_zpow] }
  let φ₁ : (Fin k → normOne t) →* ↥(orthDerived Q) :=
    (MulAut.conj g).toMonoidHom.comp (frameTorusFull hF hQ hT)
  let φ₂ : (Fin k → normOne t) →* ↥(orthDerived Q) := (frameTorusFull hF hQ hT).comp σ
  have hgen : ∀ a, φ₁ (Pi.mulSingle a (rootNormOne (F := F) (t := t)) : Fin k → normOne t) =
      φ₂ (Pi.mulSingle a (rootNormOne (F := F) (t := t)) : Fin k → normOne t) := by
    intro a
    have hσ : σ (Pi.mulSingle a (rootNormOne (F := F) (t := t)) : Fin k → normOne t) =
        (Pi.mulSingle (π a) (rootNormOne (F := F) (t := t)) : Fin k → normOne t) ^ ε a := by
      funext i
      change ((Pi.mulSingle a (rootNormOne (F := F) (t := t)) : Fin k → normOne t) (π.symm i)) ^
          ε (π.symm i) =
        ((Pi.mulSingle (π a) (rootNormOne (F := F) (t := t)) : Fin k → normOne t) ^ ε a) i
      rw [Pi.pow_apply]
      by_cases hi : i = π a
      · subst hi
        simp
      · have hi' : π.symm i ≠ a := fun h => hi (by rw [← h, Equiv.apply_symm_apply])
        simp [Pi.mulSingle_eq_of_ne hi', Pi.mulSingle_eq_of_ne hi]
    change g * frameTorusFull hF hQ hT
        (Pi.mulSingle a (rootNormOne (F := F) (t := t)) : Fin k → normOne t) * g⁻¹ =
      frameTorusFull hF hQ hT
        (σ (Pi.mulSingle a (rootNormOne (F := F) (t := t)) : Fin k → normOne t))
    rw [hσ, map_zpow, frameTorusFull_mulSingle, frameTorusFull_mulSingle, hconj]
  have hmem : x ∈ MonoidHom.eqLocus φ₁ φ₂ := by
    rw [← Finset.univ_prod_mulSingle x]
    refine Subgroup.prod_mem _ fun a _ => ?_
    have hxa : x a ^ p = 1 := by simpa using congrFun hx a
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_rootNormOne hF a hxa)
    have hsingle : (Pi.mulSingle a (x a) : Fin k → normOne t) =
        (Pi.mulSingle a (rootNormOne (F := F) (t := t)) : Fin k → normOne t) ^ n := by
      rw [← hn]
      exact map_zpow (MonoidHom.mulSingle (fun _ => ↥(normOne t)) a) _ n
    rw [hsingle]
    exact Subgroup.zpow_mem _ (hgen a) n
  exact hmem

theorem torData_of_relFrame {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ)
    (hS : OrdPNsOm.charSum Q ⊤ ≠ (-(Nat.card F : ℤ)) ^ ℓ)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hcenter : Subgroup.center ↥(orthDerived Q) = ⊥)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    GGTorusTorData (Nat.card F + 1) (ℓ - 1) (CartanMatrix.B (ℓ - 1)) (CoxeterMatrix.B (ℓ - 1))
      ↥(orthDerived Q) (E.map (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, e, u, c, t, f, f', hF, hf, hf', hQf, hQf', hff'⟩ :=
    exists_relFrame hQ hp hp2 hpq hdim hℓ hS hE hsc
  have hk : 0 < ℓ - 1 := by omega
  haveI : Fact (Irreducible (OmNsRootGen.framePoly t)) := ⟨framePoly_irreducible hF ⟨0, hk⟩⟩
  have hM : Odd (Nat.card F + 1) := by
    letI := Fintype.ofFinite F
    have h2 : 2 ∣ Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff F 2 _).mp (FiniteField.cast_card_eq_zero (K := F))
    exact (even_iff_two_dvd.mpr h2).add_one
  let l : normOne t ≃* Multiplicative (ZMod (Nat.card F + 1)) :=
    (zmodCyclicMulEquiv (isCyclic_normOne (F := F) (t := t))).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr (natCard_normOne (F := F) (t := t))).toAddEquiv)
  have hv : f + f' ∈ polarPerp Q (⨆ j, U j) := Submodule.add_mem _ hf hf'
  have hQv : Q (f + f') ≠ 0 := by
    rw [QuadraticMap.map_add (⇑Q) f f', hQf, hQf', hff']
    simp
  have hdim' : Module.finrank F V = 2 * (ℓ - 1) + 2 := by omega
  let w : Fin (ℓ - 1) → ↥(orthDerived Q) := fun k =>
    if hk : k.val + 1 < ℓ - 1 then
      ⟨OmNsRootGen.frameSwap Q e u c t k ⟨k.val + 1, hk⟩,
        OmNsRootGen.frameSwap_mem_orthDerived hQ hdim (by omega)⟩
    else ⟨OmNsRootGen.signChange Q u (f + f') k, OmNsRootGen.signChange_mem_orthDerived hQ hF hQv⟩
  refine RelD.ggTorusTorData_of_blockModel (M := Nat.card F + 1) hp2 hM (by omega) hcenter l
    (frameTorusFull hF hQ hT) (frameTorusFull_injective hF hQ hT) E
    (mem_iff_frameTorusFull hF hQ hT) (rootNormOne (F := F) (t := t))
    (orderOf_rootNormOne hF ⟨0, hk⟩) w ?_ ?_ ?_ ?_ ?_
  ·
    intro k hk x
    simp only [w, dif_pos hk]
    exact frameSwap_conj_frameTorusFull hF hQ hT hdim (by omega)
      (fun h => by simpa using congrArg Fin.val h) x
  ·
    intro k hk x
    have hk' : ¬ k.val + 1 < ℓ - 1 := by omega
    simp only [w, dif_neg hk']
    exact signChange_conj_frameTorusFull hF hQ hT hv hQv k x
  ·
    intro g hc x
    exact commute_frameTorusFull_of_commute hF hQ hT hc x
  ·
    intro g hc hpow
    exact mem_range_frameTorusFull_of_commute hF hQ hT hdim' hf hf' hQf hQf' hff' hc hpow
  ·
    intro g hg
    obtain ⟨π, ε, hε, hconj⟩ := conj_e_of_mem_normalizer hQ hp hp2 hF hg
    exact ⟨π, ε, hε, fun x hx => conj_frameTorusFull_of_conj_e hF hQ hT π ε hconj x hx⟩

theorem ggTorusTorW_of_orthDerived {R : Type} [Group R] {F V : Type} [Field F] [Finite F]
    [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (eR : R ≃* ↥(orthDerived Q))
    (hcover : ∀ (L : Type) [Group L] [Finite L] (ψ : L →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L → commutator L = ⊤ → Function.Injective ψ)
    (hcenterR : Subgroup.center R = ⊥)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ)
    (hS : OrdPNsOm.charSum Q ⊤ ≠ (-(Nat.card F : ℤ)) ^ ℓ)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    GGTorusTorW p (ℓ - 1) (Nat.card F + 1) (ℓ - 1) (CartanMatrix.B (ℓ - 1))
      (CoxeterMatrix.B (ℓ - 1)) R (LargeEvenInnSet R) := by
  intro L _ _ ψ A hTB
  have hinj : Function.Injective ψ := hcover L ψ hTB.1 hTB.2.1 hTB.2.2.1
  obtain ⟨e, -, E, hE, -, hsc, hA⟩ := exists_innModel_of_tbGroup
    (I := LargeEvenInnSet R) (fun φ ⟨x, hx⟩ => ⟨x, hx.symm⟩) hcenterR ψ hinj A hTB
  refine torData_of_innModel e hA ?_
  refine torData_of_mulEquiv_map eR rfl ?_
  have hcenter : Subgroup.center ↥(orthDerived Q) = ⊥ := by
    have h1 := Subgroup.map_center_eq eR.symm
    rw [hcenterR] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (f := (eR.symm : ↥(orthDerived Q) →* R))
      eR.symm.injective).mp h1
  refine torData_of_relFrame hQ hp hp2 hpq hdim hℓ hS hT hcenter (hE.map _) ?_
  intro g hc hgp
  have hc' : ∀ x ∈ E, eR.symm g * x = x * eR.symm g := by
    intro x hx
    apply eR.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc (eR x) ⟨x, hx, rfl⟩
  have hgp' : (eR.symm g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
  exact ⟨eR.symm g, hsc _ hc' hgp', MulEquiv.apply_symm_apply eR g⟩

theorem ggTorusTorW_relDNs_plus {K : Type} [Field K] [Finite K] [CharP K 2] {f ℓ p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hℓ : 5 ≤ ℓ) (hodd : Odd ℓ) :
    GGTorusTorW p (ℓ - 1) (Nat.card K + 1) (ℓ - 1) (CartanMatrix.B (ℓ - 1))
      (CoxeterMatrix.B (ℓ - 1)) (OrthRest.RPlus K ℓ) (LargeEvenInnSet (OrthRest.RPlus K ℓ)) := by
  refine ggTorusTorW_of_orthDerived (OrthTorus.rPlusEquiv K (by omega)) ?_
    (OrthNs.center_data_omegaPlus hp hp2 (by omega)).1 (TableBOrth.nondegenerate_qPlusForm ℓ)
    hp hp2 hpq (finrank_qPlusForm ℓ) (by omega) (charSum_qPlusForm_ne hodd) ?_
  · intro L _ _ ψ hψ hker hperf
    rcases (show f = 1 ∨ 2 ≤ f by omega) with h | h
    · subst h
      exact rPlus_injective_of_cover_two (by rw [hK]; norm_num) (by omega) L ψ hψ hker hperf
    · exact rPlus_injective_of_cover hK h (by omega) L ψ hψ hker hperf
  · have h := OrthTorus.exists_totallySingular_qPlusForm (K := K) (n := ℓ - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at h

theorem ggTorusTorW_relDNs_minus {K : Type} [Field K] [Finite K] [CharP K 2] {f m p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hm : 3 ≤ m) (heven : Even (m + 1)) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusTorW p m (Nat.card K + 1) m (CartanMatrix.B m) (CoxeterMatrix.B m)
      (OrthRest.RMinus K m b c) (LargeEvenInnSet (OrthRest.RMinus K m b c)) := by
  have hS := charSum_qMinusForm_ne (K := K) (ℓ := m + 1) (by omega) heven hirr
  rw [Nat.add_sub_cancel] at hS
  have h := ggTorusTorW_of_orthDerived (ℓ := m + 1) (OrthTorus.rMinusEquiv K m b c) ?_
    (OrthExc.center_data_omegaMinus hp hp2 hm hirr).1 (TableBOrth.nondegenerate_qMinusForm m hirr)
    hp hp2 hpq (finrank_qMinusForm m) (by omega) hS ((OrthTorus.charSum_qMinusForm m hirr).2 hm)
  · simpa using h
  · intro L _ _ ψ hψ hker hperf
    rcases (show f = 1 ∨ 2 ≤ f by omega) with h | h
    · subst h
      exact rMinus_injective_of_cover_two (by rw [hK]; norm_num) hm hirr L ψ hψ hker hperf
    · exact rMinus_injective_of_cover hK h hm hirr L ψ hψ hker hperf

end RelDNs

theorem not_dvd_two_pow_sub_one_of_dvd_add_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) : ¬ p ∣ 2 ^ n - 1 := by
  intro h
  have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  have hd := Nat.dvd_sub hpn h
  rw [h2] at hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)


theorem largeEvenLabelAll_relD_D_ns {p n ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn1 : 1 ≤ n)
    (hℓ : 5 ≤ ℓ) (hodd : Odd ℓ) (hpn : p ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.D, ℓ, n⟩ fun R _ I _ =>
      GGTorusTorW p (ℓ - 1) (ggTorMpm p ⟨.D, ℓ, n⟩) (ℓ - 1)
        (CartanMatrix.B (ℓ - 1)) (CoxeterMatrix.B (ℓ - 1)) R I := by
  intro Q hQ
  have h3 : ℓ ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [h3, ↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card (m := n) hK
  have hM : ggTorMpm p ⟨.D, ℓ, n⟩ = Nat.card K + 1 := by
    rw [ggTorMpm, if_neg (not_dvd_two_pow_sub_one_of_dvd_add_one hp hp2 hpn), hK]
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  rw [hM]
  exact RelDNs.ggTorusTorW_relDNs_plus hK hn1 hp hp2 (by rw [hK]; exact hpn) hℓ hodd

theorem largeEvenLabelAll_relD_twD_ns {p n ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn1 : 1 ≤ n)
    (hℓ : 4 ≤ ℓ) (heven : Even ℓ) (hpn : p ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twD, ℓ, n⟩ fun R _ I _ =>
      GGTorusTorW p (ℓ - 1) (ggTorMpm p ⟨.twD, ℓ, n⟩) (ℓ - 1)
        (CartanMatrix.B (ℓ - 1)) (CoxeterMatrix.B (ℓ - 1)) R I := by
  intro Q hQ
  have h2 : ℓ ≠ 2 := by omega
  have h3 : ℓ ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [h2, h3, ↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, b, c, hirr, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card (m := n) hK
  have hM : ggTorMpm p ⟨.twD, ℓ, n⟩ = Nat.card K + 1 := by
    rw [ggTorMpm, if_neg (not_dvd_two_pow_sub_one_of_dvd_add_one hp hp2 hpn), hK]
  refine ⟨K, i1, i2, hK, b, c, hirr, hQ', ?_⟩
  rw [hM]
  exact RelDNs.ggTorusTorW_relDNs_minus hK hn1 hp hp2 (by rw [hK]; exact hpn) (by omega)
    (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]) hirr

end CFSG.StandardType
