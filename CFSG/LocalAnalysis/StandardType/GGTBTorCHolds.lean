module

public import CFSG.LocalAnalysis.StandardType.GGTorCWitness
public import CFSG.LocalAnalysis.StandardType.GGTorCTori
public import CFSG.LocalAnalysis.StandardType.GGTorusTorLiftTwo
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGSpJoinMaxElemSp
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherTrace
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest
public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherRead
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.G11Stmts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open TorC SpJoin

theorem map_congr_scalarA {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (E : Subgroup G) :
    (scalarA E).map (MulAut.congr e).toMonoidHom = scalarA (E.map e.toMonoidHom) := by
  rw [scalarA, scalarA, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x : 1
  exact congr_conj e x

section Certificates


theorem ggTorusTorData_symplectic_of_selfCentralizing {K : Type} [Field K] [Finite K]
    {f m p n : ℕ} (hK : Nat.card K = 2 ^ f) (hn2 : 2 ≤ n) (hm : Odd m)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ m) (D : SpTorusData K m p)
    (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K n))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hAe : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K n))
        (LargeEvenGSpSet K n), ∀ l : L', φ (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    GGTorusTorData m n (CartanMatrix.C n) (CoxeterMatrix.B n) L' A := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K n)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot
  have : Finite (LargeEvenProj (LargeEvenSpGroup K n)) := Finite.of_surjective ψ hψ
  have h2 : IsPGroup 2 ψ.ker := by
    have hZ : IsPGroup 2 (Subgroup.center L') := by
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
      intro q hq hqd
      by_contra hq2
      exact ggCenterPrime_sp (K := K) (m := n) hq hq2 L' ψ hψ hker hperf hqd
    exact hZ.to_le hker
  obtain ⟨Λ, -, -, hΛmap, hAΛ, hER, -, hERsc⟩ :=
    TwE6TB.exists_innerModel hp hZR
      (fun _ hφ _ => TableBSymp.sp_I_subset_inn hφ)
      (ggCenterPrime_sp (K := K) (m := n) hp hp2)
      ψ hψ hker hperf hAe hAI hsc
  let ER := A.comap Λ
  have hAbER : TypeA.inducedSub ψ A = scalarA ER :=
    TypeA.inducedSub_eq_map_conj_of_lift hψ Λ hΛmap hAΛ
  have hAind : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (LargeEvenSpGroup K n)),
      ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨x, -, hx⟩ := hAI a ha
    exact ⟨x, hx⟩
  let θ : LargeEvenProj (LargeEvenSpGroup K n) ≃* StatedSp n K :=
    CFSG.SeitzReduction.OmegaPilot.spProjEquivCharTwo K n
  set E' := ER.map θ.toMonoidHom with hE'
  have hE'p : ∀ a ∈ E', a ^ p = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    show θ s ^ p = 1
    rw [← map_pow, hER.2 s hs, map_one]
  have hE'c : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    show θ s * θ s' = θ s' * θ s
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hER hs hs']
  have hE'max : ∀ g : StatedSp n K, g ^ p = 1 → (∀ a ∈ E', g * a = a * g) → g ∈ E' := by
    intro g hgp hg
    refine ⟨θ.symm g, ?_, θ.apply_symm_apply g⟩
    refine hERsc (θ.symm g) (fun s hs => ?_) (by rw [← map_pow, hgp, map_one])
    apply θ.injective
    simpa only [map_mul, θ.apply_symm_apply] using hg (θ s) ⟨s, hs, rfl⟩
  have hE'ea : IsElemAbelian p E' :=
    ⟨⟨⟨fun a b => Subtype.ext (hE'c a.1 a.2 b.1 b.2)⟩⟩, hE'p⟩
  have hDp := spPlaneTorus_injective D.inj_p n
  set E₀ := (spPlaneTorus n D.ζp).range with hE₀
  have hE₀p : ∀ a ∈ E₀, a ^ p = 1 := fun a ha =>
    ((mem_range_spPlaneTorus_iff n D.inj_m D.mem_m D.tors a).mp ha).1
  have hE₀c : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    rintro _ ⟨f, rfl⟩ _ ⟨f', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have htr := trace_ne_zero_of_pow_eq_one (g := D.ζp (Multiplicative.ofAdd 1)) (p := p)
    (fun h => one_ne_zero (ofAdd_eq_one.mp (D.inj_p (h.trans (map_one _).symm))))
    (hp.odd_of_ne_two hp2) (by
      rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero, map_one])
  have hE₀max : ∀ g : StatedSp n K, g ^ p = 1 → (∀ a ∈ E₀, g * a = a * g) → g ∈ E₀ := by
    intro g hgp hg
    refine (mem_range_spPlaneTorus_iff n D.inj_m D.mem_m D.tors g).mpr ⟨hgp, ?_⟩
    refine mem_range_spPlaneTorus_of_commute htr D.cent n g fun i => ?_
    exact hg _ ⟨Pi.mulSingle i (Multiplicative.ofAdd 1), spPlaneTorus_mulSingle D.ζp i _⟩
  have hE₀ne : E₀ ≠ ⊥ := by
    intro h
    have hmem : spPlaneTorus n D.ζp (Pi.mulSingle ⟨0, by omega⟩ (Multiplicative.ofAdd 1)) ∈ E₀ :=
      ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one (spPlaneTorus n D.ζp)] at hmem
    have h1 := congrFun (hDp hmem) ⟨0, by omega⟩
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)
  have hcard₀ : Nat.card E₀ = p ^ n := by
    rw [hE₀, Nat.card_congr (MonoidHom.ofInjective hDp).toEquiv.symm, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod,
      Nat.card_fin]
  have hcard : p ^ n ≤ Nat.card E' :=
    (hcard₀.symm.trans (OrdPNsSp.card_eq_of_maximal hp hp2 hE₀p hE₀c hE₀max hE'p hE'c hE'max
      hE₀ne)).le
  obtain ⟨c, hc⟩ := D.conj n E' hE'ea hcard
  obtain ⟨w₀, hw₀, hT₀, hTsc₀⟩ := exists_ggTorusTorWit_sp hm hp hp2 hpm hn2 D.inj_m D.inv_m D.inj_p
    D.mem_m D.tors D.cent
  let e : StatedSp n K ≃* LargeEvenProj (LargeEvenSpGroup K n) := (MulAut.conj c⁻¹).trans θ.symm
  have hEe : E₀.map e.toMonoidHom = ER := by
    rw [hE₀, ← hc, Subgroup.map_map, hE', Subgroup.map_map]
    convert Subgroup.map_id ER using 2
    refine MonoidHom.ext fun s => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, e,
      MulEquiv.trans_apply, MulAut.conj_apply, MonoidHom.id_apply]
    rw [show c⁻¹ * (c * θ s * c⁻¹) * c⁻¹⁻¹ = θ s by group, θ.symm_apply_apply]
  have hA2 : (scalarA E₀).map (MulAut.congr e).toMonoidHom = TypeA.inducedSub ψ A := by
    rw [map_congr_scalarA, hEe, hAbER]
  refine ggTorusTorData_liftTwo hψ hker h2 hperf hZR hm hAind hA2 (w₀.transport e)
    (w₀.holds_transport e hw₀) ?_ ?_
  · rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hT₀ τ hτ
    exact ⟨e s, ⟨s, hs, rfl⟩, congr_conj e s⟩
  · rw [GGTorusTorWit.transport_Tsc, Subgroup.card_map_of_injective e.injective]
    exact hTsc₀

theorem ggTorusTorW_symplectic {K : Type} [Field K] [Finite K] {f m p n : ℕ}
    (hK : Nat.card K = 2 ^ f) (hn2 : 2 ≤ n) (hm : Odd m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (D : SpTorusData K m p) (r : ℕ) :
    GGTorusTorW p r m n (CartanMatrix.C n) (CoxeterMatrix.B n)
      (LargeEvenProj (LargeEvenSpGroup K n))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K n)) (LargeEvenGSpSet K n)) := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, -, hsc⟩ := hTB
  exact ggTorusTorData_symplectic_of_selfCentralizing hK hn2 hm hp hp2 hpm D L' ψ hψ hker hperf
    hAe hAI hsc

theorem ggTBTorC_holds : GGTBTorC := by
  intro p hp hp2 lab hlab htag hpq
  obtain ⟨t, l, f⟩ := lab
  dsimp only at htag hpq ⊢
  have hf : 1 ≤ f := hlab.1
  have hl : 2 ≤ l := by
    rcases htag with rfl | rfl
    · exact hlab.2.1
    · exact hlab.2.1
  have hq : 2 ≤ 2 ^ f := le_self_pow₀ (by norm_num) (by omega)
  have hoddm : Odd (2 ^ f - 1) := by
    have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨k, hk⟩ := this
    exact ⟨k - 1, by omega⟩
  have hoddp : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hmain : ∀ {m : ℕ} (hm : Odd m) (hpm : p ∣ m), (∀ {K : Type} [Field K] [Finite K],
      Nat.card K = 2 ^ f → Nonempty (SpTorusData K m p)) →
      LargeEvenLabelAll ⟨t, l, f⟩ fun R _ I _ =>
        GGTorusTorW p (l - ggTorEnn p ⟨t, l, f⟩) m l (CartanMatrix.C l) (CoxeterMatrix.B l)
          R I := by
    intro m hm hpm hD Q hQ
    have hQ' : LargeEvenRecipeSymplectic l (2 ^ f) false Q := by
      rcases htag with rfl | rfl <;> exact hQ
    obtain ⟨K, i1, i2, hK, hQK⟩ := hQ'
    have hgoal : LargeEvenRecipeSymplectic l (2 ^ f) false fun R _ I F => Q R I F ∧
        GGTorusTorW p (l - ggTorEnn p ⟨t, l, f⟩) m l (CartanMatrix.C l) (CoxeterMatrix.B l)
          R I :=
      ⟨K, i1, i2, hK, hQK, ggTorusTorW_symplectic hK hl hm hp hp2 hpm (hD hK).some _⟩
    rcases htag with rfl | rfl <;> exact hgoal
  rcases (Nat.Prime.dvd_mul hp).mp hpq with h | h
  · have hE : ggTorMpm p ⟨t, l, f⟩ = 2 ^ f - 1 := by
      unfold ggTorMpm
      dsimp only
      rw [if_pos h]
    rw [hE]
    exact hmain hoddm h fun hK => by
      have : CharP _ 2 := charP_two_of_card hK
      have h' := TorC.nonempty_spTorusData_split hp hp2 (by rw [hK]; exact h)
      rwa [hK] at h'
  · have hn1 : ¬ p ∣ 2 ^ f - 1 := by
      intro h1
      have h3 : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h h1
      have h4 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
      rw [h4] at h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
    have hE : ggTorMpm p ⟨t, l, f⟩ = 2 ^ f + 1 := by
      unfold ggTorMpm
      dsimp only
      rw [if_neg hn1]
    rw [hE]
    exact hmain hoddp h fun hK => by
      have : CharP _ 2 := charP_two_of_card hK
      have h' := TorC.nonempty_spTorusData_nonsplit hp hp2 (by rw [hK]; exact h)
      rwa [hK] at h'

end Certificates

end CFSG.StandardType

end
