module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwCard
public import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
public import CFSG.LocalAnalysis.StandardType.GGTwOmPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGR4PumpTransfer
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

open scoped Pointwise

private theorem ggPumpTw_finish {G : Type} [Group G] [Finite G] {Bs X J : Subgroup G}
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : ↥X ⧸ Subgroup.center ↥X ≃* R)
    (hBsEA : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hXperf : commutator ↥X = ⊤)
    (hcp : GGCenterPrime 3 R) (hIinn : GGOutdiagPrime 3 R I)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {z : G} (hzBs : z ∈ Bs) (hzC : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1)
    (hJX : J ≤ X) (hEJ : 3 ≤ Nat.log 3 (Nat.card ↥(Bs ⊓ J))) :
    (∃ A : Subgroup (MulAut ↥X), IsElemAbelian 3 A ∧
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥X, φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      3 ^ 3 ≤ Nat.card ↥A ∧ GGTorusSelfCent 3 A ∧
      Nat.card ↥(ggAutomizer X Bs) =
        Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A) ∧
      Nat.card ↥A = Nat.card ↥(Bs ⊓ X) ∧ Nat.card ↥(Bs ⊓ X) * 3 ≤ Nat.card ↥Bs) ∧
      ∀ b ∈ Bs, ∃ k ∈ Bs ⊓ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹ := by
  have : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  have hZ' : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    have h := hcp ↥X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hXperf
    have hdvd : orderOf g ∣ Nat.card ↥(Subgroup.center ↥X) := Subgroup.orderOf_dvd_natCard _ hg
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => h (h3.trans hdvd)
  have hBs3' : ∀ b ∈ Bs, ∃ φ ∈ {φ ∈ I | φ ^ 3 = 1},
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hBs3 b hb
    refine ⟨φ, ⟨hφI, ?_⟩, hφ⟩
    rw [eq_ggLAut_of_induces X θ (hBsN hb) hφ, ← map_pow]
    have h1 : (⟨b⁻¹, inv_mem (hBsN hb)⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simp [inv_pow, hBsEA.2 b hb])
    rw [h1, map_one]
  have hInn : ∀ b ∈ Bs, ∃ k ∈ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹ :=
    r4m_inn_of_subset_inn (I := {φ ∈ I | φ ^ 3 = 1}) θ hXperf hBsN
      (fun φ hφ => hIinn φ hφ.1 hφ.2) hBs3'
  obtain ⟨hsup, -, -, -, -⟩ := ggLemma47c hBsEA hSC hZ' hInn
  obtain ⟨A, hAabel, hAind, hp3A, hAself, hcardAutEq, hBXcard, hcardBs, hpC, -⟩ :=
    r4m_finish (I := {φ ∈ I | φ ^ 3 = 1}) θ hBsEA hSC hBsN hXperf hZ'
      (fun φ hφ => hIinn φ hφ.1 hφ.2) hBs3' z hzBs hzC hz1 hJX hEJ
  have hleBX : (Bs ⊓ X) ≤
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (IsElemAbelian.comm hBsEA hb.1 hc.1).symm
  refine ⟨⟨A, hAabel, fun a ha => ?_, hp3A, hAself, hcardAutEq, hBXcard, ?_⟩, fun b hb => ?_⟩
  · obtain ⟨φ, hφ, h⟩ := hAind a ha
    exact ⟨φ, hφ.1, h⟩
  · rw [hcardBs]
    exact Nat.mul_le_mul_left _ hpC
  · have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Bs ⊓ X)
      (Bs ⊓ Subgroup.centralizer (X : Set G)) hleBX
    have hbsup : b ∈ ((Bs ⊓ X : Subgroup G) : Set G) *
        ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
      rw [← hcoe, ← hsup]
      exact hb
    obtain ⟨b1, hb1, c, hc, hbc⟩ := Set.mem_mul.mp hbsup
    refine ⟨b1, hb1, fun l hl => ?_⟩
    have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc.2 l hl
    have hcl' : c * l * c⁻¹ = l := by
      calc c * l * c⁻¹ = (l * c) * c⁻¹ := by rw [hcl]
        _ = l := by group
    rw [← hbc]
    calc b1 * c * l * (b1 * c)⁻¹ = b1 * (c * l * c⁻¹) * b1⁻¹ := by group
      _ = b1 * l * b1⁻¹ := by rw [hcl']

private theorem ggPumpTw_classical
    {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) {lab : LargeEvenLabel}
    (h : (lab = ⟨.A, 5 + 2 * k, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
      (lab = ⟨.twA, 5 + 2 * k, f⟩ ∧ 3 ∣ 2 ^ f - 1) ∨
      (lab = ⟨.twD, 4 + k, f⟩ ∧ (3 ∣ 2 ^ f - 1 ∨ (3 ∣ 2 ^ f + 1 ∧ Even k))) ∨
      (lab = ⟨.D, 4 + k, f⟩ ∧ 3 ∣ 2 ^ f + 1 ∧ Odd k)) :
    LargeEvenLabelAll lab fun R _ I _ => GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
      GGTorusAutCardSC 3 R I (3 + k) (2 ^ (3 + k) * (3 + k).factorial) := by
  rcases h with ⟨rfl, h3⟩ | ⟨rfl, h3⟩ | ⟨rfl, h3⟩ | ⟨rfl, h3, hodd⟩
  · have hfa : LargeEvenLabelAll ⟨.A, 2 * (3 + k) - 1, f⟩ fun R _ I _ =>
        GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I :=
      ggTwSL_label_of_rec (ε := 0) (P := fun R _ I => GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I) (by omega) (by omega)
        fun K _ _ _ hK => by
          have h := ggTwSL_facts_rec (d := 2 * (3 + k) - 1 + 1) (r := 3 + k) (by omega)
            (by omega) (by rw [hK]; exact h3)
          exact ⟨h.2.2, h.2.1⟩
    have e : 2 * (3 + k) - 1 = 5 + 2 * k := by omega
    have h' : LargeEvenLabelAll ⟨.A, 2 * (3 + k) - 1, f⟩ fun R _ I _ => GGCenterPrime 3 R ∧
        GGOutdiagPrime 3 R I ∧ GGTorusAutCardSC 3 R I (3 + k) (2 ^ (3 + k) * (3 + k).factorial) :=
      LargeEvenLabelAll.mono (fun _ _ _ _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩)
        (largeEvenLabelAll_and hfa (ggTwSL_label (r := 3 + k) (by omega) h3))
    rwa [e] at h'
  · have hfa : LargeEvenLabelAll ⟨.twA, 2 * (3 + k) - 1, f⟩ fun R _ I _ =>
        GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I :=
      ggTwSU_label_of_rec (ε := 0) (P := fun R _ I => GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I) (by omega) (by omega)
        fun K _ _ _ hK => by
          have h := ggTwSU_facts_rec (n := f) (d := 2 * (3 + k) - 1 + 1) (r := 3 + k) hK hf
            (by omega) (by omega) h3
          exact ⟨h.2.2, h.2.1⟩
    have e : 2 * (3 + k) - 1 = 5 + 2 * k := by omega
    have h' : LargeEvenLabelAll ⟨.twA, 2 * (3 + k) - 1, f⟩ fun R _ I _ => GGCenterPrime 3 R ∧
        GGOutdiagPrime 3 R I ∧ GGTorusAutCardSC 3 R I (3 + k) (2 ^ (3 + k) * (3 + k).factorial) :=
      LargeEvenLabelAll.mono (fun _ _ _ _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩)
        (largeEvenLabelAll_and hfa (ggTwSU_label (r := 3 + k) hf (by omega) h3))
    rwa [e] at h'
  · have h3' : 3 ∣ 2 ^ f - 1 ∨ (Odd (3 + k) ∧ 3 ∣ 2 ^ f + 1) := by
      rcases h3 with h3 | ⟨h3, ⟨j, hj⟩⟩
      · exact Or.inl h3
      · exact Or.inr ⟨⟨1 + j, by omega⟩, h3⟩
    have hfa : LargeEvenLabelAll ⟨.twD, 3 + k + 1, f⟩ fun R _ I _ =>
        GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I :=
      ggTwOm_label_of_rec (r := 3 + k) (P := fun R _ I => GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I)
        (by omega) fun K _ _ _ hK b c hbc => by
          have h := ggTwOm_facts_rec (m := 3 + k + 1 - 1) hK hbc (by omega : 3 ≤ 3 + k) rfl h3'
          exact ⟨h.2.2, h.2.1⟩
    have e : 3 + k + 1 = 4 + k := by omega
    have h' : LargeEvenLabelAll ⟨.twD, 3 + k + 1, f⟩ fun R _ I _ => GGCenterPrime 3 R ∧
        GGOutdiagPrime 3 R I ∧ GGTorusAutCardSC 3 R I (3 + k) (2 ^ (3 + k) * (3 + k).factorial) :=
      LargeEvenLabelAll.mono (fun _ _ _ _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩)
        (largeEvenLabelAll_and hfa (ggTwOm_label (r := 3 + k) hf (by omega) h3'))
    rwa [e] at h'
  · have hev : Even (3 + k) := by
      obtain ⟨j, hj⟩ := hodd
      exact ⟨2 + j, by omega⟩
    have hfa : LargeEvenLabelAll ⟨.D, 3 + k + 1, f⟩ fun R _ I _ =>
        GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I :=
      ggTwOmPlus_label_of_rec (r := 3 + k)
        (P := fun R _ I => GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I) (by omega) fun K _ _ _ hK => by
          have h := ggTwOmPlus_facts_rec (K := K) (m := 3 + k + 1) (r := 3 + k) (by omega) rfl
          exact ⟨h.2.2, h.2.1⟩
    have e : 3 + k + 1 = 4 + k := by omega
    have h' : LargeEvenLabelAll ⟨.D, 3 + k + 1, f⟩ fun R _ I _ => GGCenterPrime 3 R ∧
        GGOutdiagPrime 3 R I ∧ GGTorusAutCardSC 3 R I (3 + k) (2 ^ (3 + k) * (3 + k).factorial) :=
      LargeEvenLabelAll.mono (fun _ _ _ _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩)
        (largeEvenLabelAll_and hfa (ggTwOmPlus_label (r := 3 + k) (by omega) hev h3))
    rwa [e] at h'

theorem ggPumpTwNotFive_of_known
    (hL : GGPumpTwLabelKnown) (hE : GGPumpTwExcKnown)
    (hZ : GGCentreTrivialTwKnown) : GGPumpTwNotFive := by
  intro G _ _ p B Bs x L D J hcfg hp3 hBs5 f hJlab z hzD hz1 X hX hJX hJc hmark hEJ hnot
  subst hp3
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hBS : B ≤ Bs := hcfg.2.1.1
  have hBsEA : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hxBs : x ∈ Bs := hBS hS.2.1
  have hDB : D ≤ B := hcfg.2.2.1.1
  have hzBs : z ∈ Bs := hBS (hDB hzD)
  have hJq : CFSG.Assembly.IsQuasisimple J := (hcfg.2.2.1.2.2.2.2.2.1).2.2
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hX.1 hl)
  have hJlab' : GGPumpTwJLab f (J ⧸ Subgroup.center J) := hJlab
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := fun j hj => (hJc.1 hj).2
  obtain ⟨hXperf, lab, hlab2, hraw0⟩ := hmark
  obtain ⟨R₀, _, I₀, _, hq₀⟩ := largeEvenRawDatum_exists (hL lab hlab2 _ hraw0)
  obtain ⟨_, _, θ₀, hBsN₀, hBs3₀⟩ := hq₀.1
  let e₀ : MulAut ↥X := ggGamma X hBsN₀ ⟨x, hxBs⟩
  have he1 : e₀ ≠ 1 := by
    intro he
    apply hnot
    have hxC : x ∈ Subgroup.centralizer (X : Set G) :=
      (ggGamma_eq_one_iff X hBsN₀ ⟨x, hxBs⟩).mp he
    have hcomm : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.mpr hxC
    rw [hcomm]
    exact bot_le
  have hep : e₀ ^ 3 = 1 := by
    have h1 : (⟨x, hxBs⟩ : ↥Bs) ^ 3 = 1 := Subtype.ext (by simpa using hBsEA.2 x hxBs)
    show (ggGamma X hBsN₀ ⟨x, hxBs⟩) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hφe : ∃ φ ∈ I₀, ∀ l : ↥X, φ (ggQuotHom θ₀ l) = ggQuotHom θ₀ (e₀ l) :=
    ⟨ggBeta X θ₀ hBsN₀ ⟨x, hxBs⟩, ggBeta_mem X θ₀ hBsN₀ hBs3₀ ⟨x, hxBs⟩,
      fun l => ggBeta_ggQuotHom X hBsN₀ θ₀ ⟨x, hxBs⟩ l⟩
  have hJ'comp₀ : IsComponentOf (J.subgroupOf X) (ggFixSub e₀) :=
    r4m_component_J hBsN₀ hxBs hJc hJq
  have hlab' : GGPumpTwJLab f (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) := by
    rcases hJlab' with ⟨h3, h⟩ | ⟨h3, h⟩ | h
    · exact Or.inl ⟨h3, r4m_hasLabel_subgroupOf hJX h⟩
    · exact Or.inr (Or.inl ⟨h3, r4m_hasLabel_subgroupOf hJX h⟩)
    · exact Or.inr (Or.inr (r4m_hasLabel_subgroupOf hJX h))
  obtain ⟨hn, hcases⟩ := hq₀.2 X (ggQuotHom θ₀) (ggQuotHom_surjective θ₀)
    (by rw [ker_ggQuotHom]) hXperf e₀ (J.subgroupOf X) f he1 hep hφe hJ'comp₀ hlab'
  have hf1 : 1 ≤ f := hn ▸ hlab2.1
  rcases hcases with ⟨k, hk1, hform⟩ | ⟨hlabE, h3⟩ | ⟨hlabE, h3⟩
  ·
    obtain ⟨R, _, I, _, hq2⟩ :=
      largeEvenRawDatum_exists (ggPumpTw_classical hf1 hk1 hform _ hraw0)
    obtain ⟨⟨_, _, θ, hBsN, hBs3⟩, hcp, hIinn, hAut⟩ := hq2
    obtain ⟨⟨A, hAabel, hAind, hp3A, hAself, hcardAut, hBXcard, hle⟩, -⟩ :=
      ggPumpTw_finish θ hBsEA hSC hBsN hXperf hcp hIinn hBs3 hzBs hzC hz1 hJX hEJ
    have hA := hAut X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hXperf A
      hAabel hAind hp3A hAself
    have h1 : 3 ^ (3 + k) ≤ Nat.card ↥(Bs ⊓ X) := hBXcard ▸ hA.1
    have h2 : 3 ^ (3 + k + 1) ≤ 3 ^ 5 :=
      calc 3 ^ (3 + k + 1) = 3 ^ (3 + k) * 3 := pow_succ _ _
        _ ≤ Nat.card ↥(Bs ⊓ X) * 3 := Nat.mul_le_mul_right 3 h1
        _ ≤ Nat.card ↥Bs := hle
        _ = 3 ^ 5 := hBs5
    have hk : k = 1 := by
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h2
      omega
    subst hk
    rw [hcardAut, hA.2]
    decide
  all_goals
    obtain ⟨R, _, I, _, hq2⟩ :=
      largeEvenRawDatum_exists (hE f hf1 lab (by tauto) _ hraw0)
    obtain ⟨⟨_, _, θ, hBsN, hBs3⟩, hcp, hIinn, hAut⟩ := hq2
    obtain ⟨⟨A, hAabel, hAind, hp3A, hAself, hcardAut, hBXcard, hle⟩, hact⟩ :=
      ggPumpTw_finish θ hBsEA hSC hBsN hXperf hcp hIinn hBs3 hzBs hzC hz1 hJX hEJ
    have hxk := hact x hxBs
    have h4 := ggPumpTw_card_ge_four hZ hf1 hJlab' hJq hJX hJx hBsEA hxk hnot hEJ
    have hAcard : 3 ^ 4 ≤ Nat.card ↥A := hBXcard ▸ h4
    have h5 := hAut X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hXperf A
      hAabel hAind hAcard hAself
    rw [hcardAut, h5]
    decide

end CFSG.StandardType

end
