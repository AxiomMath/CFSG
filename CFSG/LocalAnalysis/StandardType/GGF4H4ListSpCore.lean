module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListFamilies
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate117
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace F4H4Sp

theorem card_coxeterB_three : Nat.card (CoxeterMatrix.B 3).Group = 48 := by
  have h : Nat.card (CoxeterMatrix.B 3).Group = 2 ^ 3 * (3).factorial :=
    le_antisymm (card_coxeterB_le 3) (SpFrame.card_coxeterB_ge 3 (by norm_num))
  norm_num at h
  exact h

theorem eq_three_of_two_pow_mul_factorial {l : ℕ} (h : 2 ^ l * l.factorial = 48) : l = 3 := by
  rcases Nat.lt_or_ge l 4 with hl | hl
  · interval_cases l <;> first | rfl | (exfalso; norm_num [Nat.factorial] at h)
  · exfalso
    have h1 : 2 ^ 4 * (4).factorial ≤ 2 ^ l * l.factorial :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hl) (Nat.factorial_le hl)
    rw [h] at h1
    norm_num [Nat.factorial] at h1

theorem not_two_pow_pred_mul_factorial_dvd {l : ℕ} (hl : 4 ≤ l) :
    ¬ 2 ^ (l - 1) * l.factorial ∣ 48 := by
  intro h
  have h1 : 2 ^ 3 * (4).factorial ≤ 2 ^ (l - 1) * l.factorial :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.factorial_le hl)
  have h2 := Nat.le_of_dvd (by norm_num) h
  norm_num [Nat.factorial] at h1
  omega

theorem dvd_of_halfSplit_classical {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (ht : GGF4TagClassical lab.tag) (hs : LargeEvenHalfSplit p lab c) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  rcases hs with hs | ⟨-, h⟩ | ⟨ht', -⟩ | ⟨ht', -⟩ | ⟨ht', -⟩ | ⟨ht', -⟩
  · rcases hs with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨hn, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
    · right
      rw [hn]
      norm_num
  · exact Or.inr h
  · exfalso
    rcases ht' with ⟨h, -⟩ | h <;> simp [GGF4TagClassical, h] at ht
  · exfalso
    simp [GGF4TagClassical, ht'] at ht
  · exfalso
    simp [GGF4TagClassical, ht'] at ht
  · exfalso
    simp [GGF4TagClassical, ht'] at ht

theorem classical_of_ggLabelIso {lab lab₁ : LargeEvenLabel} (ht : GGF4TagClassical lab.tag)
    (hr : lab.tag = .B ∨ lab.tag = .C ∨ 4 ≤ lab.rank) (hiso : GGLabelIso lab lab₁) :
    GGF4TagClassical lab₁.tag ∧ lab₁.n = lab.n := by
  rcases hiso with rfl | ⟨-, ht₁, -, hn⟩ | ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨heq, -⟩ |
    ⟨heq, -⟩ | ⟨-, heq⟩
  · exact ⟨ht, rfl⟩
  · exact ⟨by rcases ht₁ with h | h <;> simp [GGF4TagClassical, h], hn.symm⟩
  all_goals exfalso
  all_goals
    have h1 := congrArg LargeEvenLabel.tag heq
    have h2 := congrArg LargeEvenLabel.rank heq
    simp only at h1 h2
  · rcases hr with h | h | h
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
    · omega
  · simp [GGF4TagClassical, h1] at ht
  · rcases hr with h | h | h
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
    · omega
  · simp [GGF4TagClassical, h1] at ht
  · rcases hr with h | h | h
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
    · omega
  · simp [GGF4TagClassical, h1] at ht

theorem ggHasLabel_C_of_tag {X : Type} [Group X] {lab : LargeEvenLabel}
    (ht : lab.tag = .B ∨ lab.tag = .C) (h : GGHasLabel lab X) :
    GGHasLabel ⟨.C, lab.rank, lab.n⟩ X := by
  obtain ⟨t, l, n⟩ := lab
  rcases ht with ht | ht <;> dsimp only at ht <;> subst ht <;> exact h

theorem exists_selfCent_preimage {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hcpL : ¬ p ∣ Nat.card (Subgroup.center L'))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent p A) :
    ∃ E : Subgroup R, IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
      ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
  classical
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
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
  refine ⟨E, hEab, hcardE, fun g hg hgp => ?_⟩
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

theorem card_inf_centralizer_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) :
    Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hbot : Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨⟨hsB, hsK⟩, hsC⟩ := hs
    have hzc : (⟨s, hsK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hsC) k k.2)
    set z : Subgroup.center K := ⟨⟨s, hsK⟩, hzc⟩ with hz
    have hzp : z ^ p = 1 := Subtype.ext (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
      exact hBs.2 s hsB))
    rw [Subgroup.mem_bot]
    by_contra hs1
    have hz1 : z ≠ 1 := fun h => hs1 (by
      have h' := congrArg (fun w : Subgroup.center K => ((w : K) : G)) h
      simpa [hz] using h')
    exact hZ ((orderOf_eq_prime hzp hz1) ▸ orderOf_dvd_natCard z)
  rw [hbot, Subgroup.card_bot]
  exact hp.one_lt.le

section Nbr


variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {ks : Finset (Subgroup G)}

theorem exists_model_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) {K : Subgroup G}
    (hK : K ∈ ks) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (K ⧸ Subgroup.center K)) {P : LargeEvenRawCont}
    (hP : LargeEvenLabelAll lab P)
    (hPcp : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → GGCenterPrime p R) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      P R I F ∧ GGTorusTBGroup p 3 R I K (ggQuotHom θ) (ggGamma K hN).range ∧
      Nat.card (ggAutomizer K Bs) = 48 ∧
      48 ∣ Nat.card (ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range) ∧
      ((∀ n : K, MulAut.conj n ∈ Subgroup.normalizer
          ((ggGamma K hN).range : Set (MulAut K)) → GGTorusWeylElt p (ggGamma K hN).range n) →
        Nat.card (ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range) =
          48) := by
  classical
  have hrest : GGSecFiveRestHyp p B Bs x L D J := hres.1.1
  have hcfg : GGConfig p B Bs x L D J := hrest.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hrest.2.2.1.2 y K hnb
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNoTr : GGNoTransvection p Bs := hrest.2.2.2.1
  have hmark := ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hΛ hlab
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = lab) (P' := P)
    (fun lab' _ h' => by rw [h']; exact hP) (fun lab' R _ I F θ hPm => hPm.1) hmark
  obtain ⟨hperf, lab', -, hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hN, hind⟩, hPR⟩ := largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hN hind hb
  have hZK : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    card_inf_centralizer_le hp hBs (hPcp R I F hPR K (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hperf)
  have h3 := pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) hp hBs hSC hperf θ hN hBsI h3 h3
  have h48 : Nat.card (ggAutomizer K Bs) = 48 := by
    obtain ⟨e, -⟩ := hB K hK
    rw [← Nat.card_congr e.toEquiv]
    exact card_coxeterB_three
  have hinj := ggAutomizerGammaHom_injective hp hBs hNoTr hN hZK
  refine ⟨R, inferInstance, I, F, θ, hN, hPR, hTB, h48, ?_, fun hW => ?_⟩
  · rw [← h48]
    exact Subgroup.card_dvd_of_injective _ hinj
  · rw [← h48]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,
      ggAutomizerGammaHom_surjective_of_weyl_normalizers hN hSC hW⟩)).symm

section HalfSplit


theorem halfSplit_dvd_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks) {K : Subgroup G}
    (hK : K ∈ ks) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (ht : GGF4TagClassical lab.tag) (hr : lab.tag = .B ∨ lab.tag = .C ∨ 4 ≤ lab.rank)
    (hlab : GGHasLabel lab (K ⧸ Subgroup.center K)) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  have hrest : GGSecFiveRestHyp p B Bs x L D J := hres.1.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  obtain ⟨lab₁, hΛ₁, hhas₁, -, -, -, -, -, hHS⟩ :=
    largeEvenMarking_exists_hasLabel (ggNbr_halfSplit_of_secFiveRest hraw hiso hrest hnb)
  obtain ⟨ht₁, hn₁⟩ :=
    classical_of_ggLabelIso ht hr (ggLabelRigidInput_holds lab lab₁ _ hΛ hΛ₁ hlab hhas₁)
  rw [← hn₁]
  exact dvd_of_halfSplit_classical ht₁ hHS

end HalfSplit

theorem false_of_card_lt_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks) {K : Subgroup G}
    (hK : K ∈ ks) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (K ⧸ Subgroup.center K))
    (hb : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
        Nat.card E < p ^ 3) : False := by
  have hrest : GGSecFiveRestHyp p B Bs x L D J := hres.1.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hrest.2.2.1.2 y K hnb
  have hInn' : GGInnerDiagOnLabel (fun _ l => l = lab) p Bs K :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hΛ hlab
  obtain ⟨-, lab₃, -, hraw₃⟩ := ggInnerDiagOnLabel_nbr_pRank_ge_three hrest.1 hnb hInn'
  obtain ⟨R, _, I, F, -, -, θ, heq₃, -⟩ := largeEvenRawDatum_exists hraw₃
  subst heq₃
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, E, hEI, hEab, hE3⟩, hR⟩ :=
    largeEvenRawDatum_exists (hb _ hraw₃)
  exact absurd (hR hs hna E hEI hEab) (not_lt.mpr hE3)

end Nbr

end F4H4Sp

end CFSG.StandardType

end
