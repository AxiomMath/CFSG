module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace TwE6TB

@[expose] def GGTorusIrredSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        (∀ A' : Subgroup (MulAut L'), A' ≤ A →
          (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → A' = ⊥ ∨ A' = A) ∧
        (∃ n ∈ W, ∃ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ≠ a) ∧
        ∀ f : MulAut L' → MulAut L', (∀ a ∈ A, f a ∈ A) →
          (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
          (∀ n ∈ W, ∀ a ∈ A, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
            MulAut.conj n * f a * (MulAut.conj n)⁻¹) →
          ∃ c : ℕ, ∀ a ∈ A, f a = a ^ c

theorem ggNoInvariantLineSCr_of_irredSCr {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGTorusIrredSCr p r R I) : GGNoInvariantLineSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI hr h3 hsc
  refine ⟨W, hW1, fun Λ hΛA hΛ => ?_⟩
  by_contra hcon
  push Not at hcon
  rcases hW2 Λ hΛA (fun n hn e he => hcon n hn e he) with h0 | h0
  · have h1 : Nat.card Λ = 1 := by rw [h0]; exact Subgroup.card_bot
    rw [h1] at hΛ
    exact hp.one_lt.ne hΛ
  · rw [h0] at hΛ
    have h4 : p ^ 3 ≤ p := hΛ ▸ h3
    have h5 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h5
    omega

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBIrred_of_irredSCr {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hT : GGTorusIrredSCr p r R I) :
    GGTableBIrred Bs x L := by
  classical
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  obtain ⟨hr, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  obtain ⟨W, hW1, hW2, ⟨n₀, hn₀, a₀, ha₀, hna₀⟩, hW4⟩ := hT L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr h3'
    (ggTorusSelfCent_ggGamma hBsN hSC)
  have hker : ∀ b : Bs, γ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := fun b => by
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro n hn b hb
    obtain ⟨htp, htA⟩ := hW1 n hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hWN : ∀ n ∈ W, (n : G) ∈ L ⊓ Subgroup.normalizer (Bs : Set G) := by
    intro n hn
    refine ⟨n.2, ?_⟩
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB n hn w hw)
    simpa using Subgroup.inv_mem _ h
  have hconj : ∀ n ∈ W, ∀ b : Bs, ∃ hnb : (n : G) * b * (n : G)⁻¹ ∈ Bs,
      γ ⟨(n : G) * b * (n : G)⁻¹, hnb⟩ = MulAut.conj n * γ b * (MulAut.conj n)⁻¹ :=
    fun n hn b => ⟨hWB n hn b b.2, ggGamma_conj L hBsN n b (hWB n hn b b.2)⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro S hxS hSB hSinv
    set A' : Subgroup (MulAut L) := (S.subgroupOf Bs).map γ with hA'
    have hA'A : A' ≤ γ.range := by
      rintro _ ⟨s, -, rfl⟩
      exact ⟨s, rfl⟩
    have hA'inv : ∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
      rintro n hn _ ⟨s, hs, rfl⟩
      obtain ⟨hns, he⟩ := hconj n hn s
      exact ⟨⟨_, hns⟩, Subgroup.mem_subgroupOf.mpr
        (hSinv n (hWN n hn) s (Subgroup.mem_subgroupOf.mp hs)), he⟩
    rcases hW2 A' hA'A hA'inv with h | h
    · left
      refine le_antisymm (fun s hs => ?_) hxS
      have h1 : γ ⟨s, hSB hs⟩ ∈ A' := ⟨⟨s, hSB hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (hker _).mp h1
    · right
      refine le_antisymm hSB (fun b hb => ?_)
      have h1 : γ ⟨b, hb⟩ ∈ A' := h ▸ ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨s, hs, hsb⟩ := h1
      have h2 : γ (⟨b, hb⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hsb, mul_inv_cancel]
      have h3 : (b : G) * (s : G)⁻¹ ∈ S := hxS ((hker _).mp h2)
      have e : b = (b * (s : G)⁻¹) * s := by group
      rw [e]
      exact S.mul_mem h3 (Subgroup.mem_subgroupOf.mp hs)
  ·
    obtain ⟨b, rfl⟩ := ha₀
    refine ⟨n₀, hWN n₀ hn₀, b, b.2, fun hcomm => hna₀ ?_⟩
    obtain ⟨hnb, he⟩ := hconj n₀ hn₀ b
    rw [← he]
    congr 1
    exact Subtype.ext (show (n₀ : G) * b * (n₀ : G)⁻¹ = b by rw [hcomm, mul_inv_cancel_right])
  ·
    intro H hHB hHinv hHsup hHinf φ hφH hφmul hφN
    have hH1 : ∀ h (hh : h ∈ H), γ ⟨h, hHB hh⟩ = 1 → h = 1 := by
      intro h hh h1
      have h2 : h ∈ H ⊓ Subgroup.zpowers x := ⟨hh, (hker _).mp h1⟩
      rw [hHinf] at h2
      exact Subgroup.mem_bot.mp h2
    have huniq : ∀ h (hh : h ∈ H) h' (hh' : h' ∈ H), γ ⟨h, hHB hh⟩ = γ ⟨h', hHB hh'⟩ →
        h = h' := by
      intro h hh h' hh' he
      have h1 : γ ⟨h * h'⁻¹, hHB (H.mul_mem hh (H.inv_mem hh'))⟩ = 1 := by
        have e : (⟨h * h'⁻¹, hHB (H.mul_mem hh (H.inv_mem hh'))⟩ : Bs) =
            ⟨h, hHB hh⟩ * (⟨h', hHB hh'⟩ : Bs)⁻¹ := rfl
        rw [e, map_mul, map_inv, he, mul_inv_cancel]
      have h2 := hH1 _ (H.mul_mem hh (H.inv_mem hh')) h1
      rw [mul_inv_eq_one] at h2
      exact h2
    have hex : ∀ a ∈ γ.range, ∃ h, ∃ hh : h ∈ H, γ ⟨h, hHB hh⟩ = a := by
      rintro _ ⟨b, rfl⟩
      have hxH : ∀ h ∈ H, x * h = h * x := fun h hh =>
        mul_comm_of_isElemAbelian hBs hxB (hHB hh)
      have hbsup : (b : G) ∈ H ⊔ Subgroup.zpowers x := by
        rw [hHsup]
        exact b.2
      obtain ⟨h, hh, j, hj⟩ := exists_mem_mul_pow_of_mem_sup hxH hbsup
      refine ⟨h, hh, ?_⟩
      have e : b = ⟨h, hHB hh⟩ * (⟨x, hxB⟩ : Bs) ^ j := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hj)
      have hx1 : γ ⟨x, hxB⟩ = 1 := (hker _).mpr (Subgroup.mem_zpowers x)
      rw [e, map_mul, map_pow, hx1, one_pow, mul_one]
    let f : MulAut L → MulAut L := fun a =>
      if ha : ∃ h, ∃ hh : h ∈ H, γ ⟨h, hHB hh⟩ = a then
        γ ⟨φ ha.choose, hHB (hφH _ ha.choose_spec.choose)⟩
      else a
    have hf : ∀ h (hh : h ∈ H), f (γ ⟨h, hHB hh⟩) = γ ⟨φ h, hHB (hφH h hh)⟩ := by
      intro h hh
      have hex' : ∃ h', ∃ hh' : h' ∈ H, γ ⟨h', hHB hh'⟩ = γ ⟨h, hHB hh⟩ := ⟨h, hh, rfl⟩
      have heq : hex'.choose = h :=
        huniq _ hex'.choose_spec.choose _ hh hex'.choose_spec.choose_spec
      change (if ha : ∃ h', ∃ hh' : h' ∈ H, γ ⟨h', hHB hh'⟩ = γ ⟨h, hHB hh⟩ then
        γ ⟨φ ha.choose, hHB (hφH _ ha.choose_spec.choose)⟩ else γ ⟨h, hHB hh⟩) = _
      rw [dite_eq_left hex']
      congr 1
      exact Subtype.ext (congrArg φ heq)
    obtain ⟨c, hc⟩ := hW4 f
      (by
        intro a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        rw [hf h hh]
        exact ⟨_, rfl⟩)
      (by
        intro a ha b hb
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨h', hh', rfl⟩ := hex b hb
        have e : γ ⟨h, hHB hh⟩ * γ ⟨h', hHB hh'⟩ = γ ⟨h * h', hHB (H.mul_mem hh hh')⟩ := by
          rw [← map_mul]
          rfl
        rw [e, hf _ (H.mul_mem hh hh'), hf h hh, hf h' hh', ← map_mul]
        congr 1
        exact Subtype.ext (hφmul h hh h' hh'))
      (by
        intro n hn a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨hnh, he⟩ := hconj n hn ⟨h, hHB hh⟩
        have hnhH : (n : G) * h * (n : G)⁻¹ ∈ H := hHinv n (hWN n hn) h hh
        obtain ⟨hnφ, he'⟩ := hconj n hn ⟨φ h, hHB (hφH h hh)⟩
        have e1 : γ ⟨(n : G) * h * (n : G)⁻¹, hnh⟩ = γ ⟨(n : G) * h * (n : G)⁻¹, hHB hnhH⟩ :=
          rfl
        rw [← he, e1, hf _ hnhH, hf h hh, ← he']
        congr 1
        exact Subtype.ext (hφN n (hWN n hn) h hh))
    refine ⟨c, fun h hh => ?_⟩
    have h1 := hc _ ⟨⟨h, hHB hh⟩, rfl⟩
    rw [hf h hh, ← map_pow] at h1
    have hhc : h ^ c ∈ H := H.pow_mem hh c
    have e : ((⟨h, hHB hh⟩ : Bs) ^ c) = ⟨h ^ c, hHB hhc⟩ := rfl
    rw [e] at h1
    exact huniq _ (hφH h hh) _ hhc h1

end Config

theorem ggTableBIrredInputOn_of_labelsSCr {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrredSCr p r R I) :
    GGTableBIrredInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, hBs3⟩, r, hlift, hirr⟩ :=
    largeEvenRawDatum_exists hraw
  exact ggTableBIrred_of_irredSCr hcfg hL θ hBsN hBs3 hlift hirr

theorem ggLTransvectionCenterInputOn_of_labelsSCr' (ha₀ : GGLNoncyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCr p r R I) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, htvt⟩ := largeEvenRawDatum_exists hraw
  exact mem_zpowers_of_noTransvectionSCr hC (ha₀ G p B x L hC.1) hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift htvt hφ htv b

end TwE6TB

end CFSG.StandardType

end
