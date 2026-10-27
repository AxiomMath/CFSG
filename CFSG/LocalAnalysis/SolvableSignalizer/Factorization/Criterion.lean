module

public import CFSG.LocalAnalysis.SolvableSignalizer.Factorization.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible
import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
import CFSG.LocalAnalysis.SolvableSignalizer.Factorization.Products

public section

namespace CFSG.SolvableSignalizer

open scoped Pointwise

variable {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p q : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G} {M Q₀ : Subgroup G}

theorem exists_compatibleAt_singleton_ne_bot (d : Datum p α θ)
    (hq : q ∈ spectrum θ) : ∃ W : Subgroup G, CompatibleAt p α θ {q} W ∧ W ≠ ⊥ := by
  classical
  obtain ⟨a, ha, hdvd⟩ := hq.2
  let _ : MulDistribMulAction A G := actionAsDistrib α
  have : CFSG.IsInvariant A G (θ a) :=
    IsInvariant.toFeitThompson α (θ a) (d.invariant a ha)
  have : Fact p.Prime := ⟨d.prime⟩
  have : Fact q.Prime := ⟨hq.1⟩
  have : Fact (IsPGroup p A) := ⟨d.isElementaryAbelian.isPGroup⟩
  obtain ⟨P, hPinv⟩ :=
    CFSG.exists_invariant_sylow (G := θ a) (A := A) (p := p) (q := q) (d.coprime a ha)
  have hWinv : IsInvariant α ((P : Subgroup (θ a)).map (θ a).subtype) :=
    IsInvariant.of_feitThompson α _ (CFSG.isInvariant_map_subtype (θ a) (P : Subgroup (θ a)))
  refine ⟨(P : Subgroup (θ a)).map (θ a).subtype,
    ⟨Compatible.of_le_of_isInvariant d ((compatible_values_and_commonSignalizer d).1 a ha)
      (Subgroup.map_subtype_le _) hWinv,
      (CFSG.primeSupported_singleton_iff_isPGroup q hq.1).mpr (P.isPGroup'.map _)⟩, fun h => ?_⟩
  exact Sylow.ne_bot_of_dvd_card P hdvd
    ((Subgroup.map_eq_bot_iff_of_injective _ (θ a).subtype_injective).mp h)

private lemma twoStageCore_characteristic (q : ℕ) (H : Type*) [Group H] [Finite H] :
    (twoStageCore q H).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk (H := CFSG.pPrimeCore q H)
    (inferInstance : (CFSG.pCore q (H ⧸ CFSG.pPrimeCore q H)).Characteristic)

private theorem exists_factorizationDatum (d : Datum p α θ)
    (hloc : LocallyComplete p α θ) (hrank : p ^ 3 ≤ Nat.card A)
    (hq : q ∈ spectrum θ) (hM : Compatible p α θ M)
    (hcontrol : ∀ W : Subgroup G, CompatibleAt p α θ {q} W → W ≠ ⊥ →
      ∃ c : G, c ∈ commonSignalizerWhole θ ∧
        let U := completionIn θ (Subgroup.normalizer (W : Set G))
        (U : Set G) = (factorizationComplementCore q U : Set G) *
          ((U ⊓ conjugate M c : Subgroup G) : Set G)) :
    ∃ Q₀ : Subgroup G, FactorizationDatum p α θ q M Q₀ := by
  classical
  have hqprime : q.Prime := hq.1
  have : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨W, hWCA, hWne⟩ := exists_compatibleAt_singleton_ne_bot d hq
  have hWq : IsPGroup q W := (CFSG.primeSupported_singleton_iff_isPGroup q hqprime).mp hWCA.2
  obtain ⟨c, -, hfac⟩ := hcontrol W hWCA hWne
  have hqM : q ∣ Nat.card M := by
    set U := completionIn θ (Subgroup.normalizer (W : Set G))
    have hfac : (U : Set G) = (factorizationComplementCore q U : Set G) *
        ((U ⊓ conjugate M c : Subgroup G) : Set G) := hfac
    obtain ⟨-, hWU, hWnormal, -, -⟩ := compatible_completionIn_normalizer d hloc hWCA.1 hWne
    let R : Subgroup U := pPrimeCore q U
    let V : Subgroup U := (U ⊓ conjugate M c).subgroupOf U
    have : R.Normal := pPrimeCore_normal
    have hRcop : Nat.Coprime q (Nat.card R) := pPrimeCore_coprime_card
    have hprod : (R : Set U) * (V : Set U) = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun x => ?_
      have hxU : (x : G) ∈ (U : Set G) := x.property
      rw [hfac] at hxU
      obtain ⟨r, hr, v, hv, hrv⟩ := hxU
      obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
      exact ⟨r', hr', ⟨v, hv.1⟩, Subgroup.mem_subgroupOf.mpr hv, Subtype.ext hrv⟩
    have hle := (pCore_le_of_coprime_normal_mul_eq_univ q hqprime R V hRcop hprod).1
      (W.subgroupOf U) hWnormal (hWq.of_equiv (Subgroup.subgroupOfEquivOfLe hWU).symm)
    have hWconj : W ≤ conjugate M c := fun w hw =>
      (Subgroup.mem_subgroupOf.mp (hle (show (⟨w, hWU hw⟩ : U) ∈ W.subgroupOf U from hw))).2
    have hcarddvd : Nat.card W ∣ Nat.card M := by
      have h := Subgroup.card_dvd_of_le hWconj
      rwa [show Nat.card (conjugate M c) = Nat.card M from
        Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective] at h
    obtain ⟨n, hn⟩ := hWq.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hWne ((Subgroup.eq_bot_iff_card W).mpr (by rwa [pow_zero] at hn))
    exact (show q ∣ Nat.card W by rw [hn]; exact dvd_pow_self q hn0).trans hcarddvd
  let _ : MulDistribMulAction A G := actionAsDistrib α
  have hMinv : CFSG.IsInvariant A G M := IsInvariant.toFeitThompson α M hM.1
  have := twoStageCore_characteristic q M
  have hcoreInv : CFSG.IsInvariant A M (twoStageCore q M) :=
    CFSG.isInvariant_of_characteristic (twoStageCore q M)
  have : Fact p.Prime := ⟨d.prime⟩
  have : Fact (IsPGroup p A) := ⟨d.isElementaryAbelian.isPGroup⟩
  obtain ⟨S, hSinv⟩ := CFSG.exists_invariant_sylow (G := twoStageCore q M) (A := A)
    (p := p) (q := q) (hM.2.2.1.of_dvd_right (Subgroup.card_subgroup_dvd_card _))
  set S' := (S : Subgroup (twoStageCore q M)).map (twoStageCore q M).subtype
  have h1 : CFSG.IsInvariant A M S' :=
    @CFSG.isInvariant_map_subtype M A _ _ _ (twoStageCore q M) hcoreInv _ hSinv
  have hinv : IsInvariant α (S'.map M.subtype) := IsInvariant.of_feitThompson α _
    (@CFSG.isInvariant_map_subtype G A _ _ _ M hMinv S' h1)
  have hnt : S'.map M.subtype ≠ ⊥ := fun h =>
    (pCore_ne_bot_and_twoStageCore_sylow_ne_bot q M hqprime hM.2.1 hqM).2 S
      ((Subgroup.map_eq_bot_iff_of_injective _ (twoStageCore q M).subtype_injective).mp
        ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h))
  exact ⟨S'.map M.subtype, d, hloc, hrank, hq, hM, ⟨S, rfl⟩, hnt, hinv, hcontrol⟩

omit [Finite G] in
private theorem map_iSup_conjugate (f : MulAut G) (H Z : Subgroup G)
    (hH : H.map f.toMonoidHom = H) (hZ : Z.map f.toMonoidHom = Z) :
    (⨆ g : H, conjugate Z (g : G)).map f.toMonoidHom =
      ⨆ g : H, conjugate Z (g : G) := by
  rw [Subgroup.map_iSup]
  simp only [map_conjugate, hZ]
  have hHsymm : H.map f.symm.toMonoidHom = H := by
    rw [← congrArg (Subgroup.map f.symm.toMonoidHom) hH, Subgroup.map_map]
    convert Subgroup.map_id H
    ext x
    simp
  have hmem : ∀ g ∈ H, f g ∈ H := fun g hg => by
    rw [← hH]
    exact Subgroup.mem_map_of_mem f.toMonoidHom hg
  have hmem' : ∀ g ∈ H, f.symm g ∈ H := fun g hg => by
    rw [← hHsymm]
    exact Subgroup.mem_map_of_mem f.symm.toMonoidHom hg
  let F : H → H := fun g => ⟨f g, hmem g g.2⟩
  have hF : Function.Surjective F := fun y =>
    ⟨⟨f.symm y, hmem' y y.2⟩, Subtype.ext (f.apply_symm_apply y)⟩
  exact hF.iSup_comp (fun y : H => conjugate Z (y : G))

omit [Finite G] in
private theorem le_normalizer_iSup_conjugate_self (H Z : Subgroup G) :
    H ≤ Subgroup.normalizer ((⨆ g : H, conjugate Z (g : G) : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  simp only [← MulEquiv.toMonoidHom_eq_coe, map_conj_conjugate]
  let F : H → H := fun g => ⟨(g : G) * h⁻¹, H.mul_mem g.2 (H.inv_mem hh)⟩
  have hF : Function.Surjective F := fun y =>
    ⟨⟨(y : G) * h, H.mul_mem y.2 hh⟩, Subtype.ext (by simp [F])⟩
  exact hF.iSup_comp (fun y : H => conjugate Z (y : G))

private theorem FactorizationDatum.isComplete (f : FactorizationDatum p α θ q M Q₀) :
    IsComplete p α θ := by
  set G₀ := factorizationG₀ α θ q Q₀
  set D := factorizationD α θ q Q₀
  set K := factorizationK α θ q
  set L := factorizationL θ Q₀
  set Q := factorizationQ Q₀
  obtain ⟨hQne, -, ⟨⟨hQinv, -⟩, -⟩, hLcompat, ⟨hKcompat, -⟩, -, hCoreK⟩ :=
    FactorizationDatum.basic_subgroups f
  have hG₀inv : IsInvariant α G₀ := (FactorizationDatum.coe_factorizationG₀_eq_mul f).2.2.1
  have hQG₀ : Q ≤ G₀ := le_sup_right
  have hDinv : IsInvariant α D :=
    fun a => map_iSup_conjugate (α a) G₀ Q (hG₀inv a) (hQinv a)
  have hDG₀ : D ≤ G₀ := by
    refine iSup_le fun g => ?_
    rw [conjugate, Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem g.2) (hQG₀ hx)) g.2
  have hDnorm : G₀ ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_iSup_conjugate_self G₀ Q
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hQD : Q ≤ D := le_iSup_of_le (1 : G₀) (conjugate_one Q).ge
    exact hQne (le_bot_iff.mp (hbot ▸ hQD))
  have hDcompat : Compatible p α θ D :=
    Compatible.of_le_of_isInvariant f.solvable (FactorizationDatum.compatible_factorizationG₀ f)
      hDG₀ hDinv
  obtain ⟨hUcompat, -, -, hcontains, -⟩ :=
    compatible_completionIn_normalizer f.solvable f.locally_complete hDcompat hDne
  set U := completionIn θ (Subgroup.normalizer (D : Set G))
  have hKU : K ≤ U := hcontains _ hKcompat ((le_sup_left : K ≤ G₀).trans hDnorm)
  have hLU : L ≤ U :=
    hcontains _ hLcompat (FactorizationDatum.factorizationL_le_normalizer_factorizationD f)
  have hcomplU : completion θ ≤ U := by
    refine iSup_le fun a => iSup_le fun ha x hx => ?_
    rw [← SetLike.mem_coe, FactorizationDatum.coe_value_eq_mul f a ha] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    exact U.mul_mem (hKU (hCoreK a ha hy)) (hLU hz.2)
  exact Compatible.of_le_of_isInvariant f.solvable hUcompat hcomplU
    (IsInvariant.iSup fun a => IsInvariant.iSup fun ha => f.solvable.invariant a ha)

theorem isComplete_of_normalizer_factorization (d : Datum p α θ)
    (hloc : LocallyComplete p α θ) (hrank : p ^ 3 ≤ Nat.card A)
    (hq : q ∈ spectrum θ) (hM : Compatible p α θ M)
    (hcontrol : ∀ W : Subgroup G, CompatibleAt p α θ {q} W → W ≠ ⊥ →
      ∃ c : G, c ∈ commonSignalizerWhole θ ∧
        let U := completionIn θ (Subgroup.normalizer (W : Set G))
        (U : Set G) = (factorizationComplementCore q U : Set G) *
          ((U ⊓ conjugate M c : Subgroup G) : Set G)) :
    IsComplete p α θ := by
  obtain ⟨Q₀, f⟩ := exists_factorizationDatum d hloc hrank hq hM hcontrol
  exact f.isComplete

end CFSG.SolvableSignalizer
