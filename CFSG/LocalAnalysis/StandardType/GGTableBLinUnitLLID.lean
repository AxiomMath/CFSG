module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLIDProof
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_zpowers_of_pow {p : ℕ} {n : G} (hn : n ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers n) := CFSG.Open.isElemAbelian_zpowers hn

theorem bstar_innerDiag_of_twoLocalSCr {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hT : GGBstarTwoLocalSCr p r R I) :
    Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  classical
  have hBsN := hC.bstar_le_normalizer hnc
  obtain ⟨hp, hBs, -, hLx, -⟩ := hC.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hC.2.1.1
  have hBA : IsElemAbelian p B := hS.1.1
  set γB := ggGamma L hBN with hγB
  set γs := ggGamma L hBsN with hγs
  have hle : γB.range ≤ γs.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hAs : IsElemAbelian p γs.range := isElemAbelian_range hBc hBp γs
  have hAI : ∀ a ∈ γB.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBN b, ggBeta_mem L θ hBN h3 b, fun l => ggBeta_ggQuotHom L hBN θ b l⟩
  have hAsI : ∀ a ∈ γs.range, ∃ φ : MulAut R, ∀ l : L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hcB := card_range_ggGamma_mul L hBN hp hS
  have hr : p ^ r ≤ Nat.card γB.range := by
    have h1 := succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card γB.range * p := by
      rw [hcB, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  have h3' : p ^ 3 ≤ Nat.card γB.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hC.1.2.2.2.2.2.1.2.2.2
    rw [← hcB, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  have hmax : ∀ n : L, n ^ p = 1 → (∀ a ∈ γB.range, a n = n) → ∀ U : Subgroup L, U ≠ ⊥ →
      IsPGroup 2 U → (∀ a ∈ γB.range, ∀ u ∈ U, a u ∈ U) → (∀ u ∈ U, n * u * n⁻¹ ∈ U) →
      MulAut.conj n ∈ γB.range := by
    intro n hnp hnfix U hU hU2 hUA hUn
    have hnB : ∀ b ∈ B, b * (n : G) = (n : G) * b := by
      intro b hb
      have h1 := congrArg Subtype.val (hnfix (γB ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩)
      rw [hγB, ggGamma_coe] at h1
      calc b * (n : G) = b * n * b⁻¹ * b := by group
        _ = n * b := by rw [h1]
    set T : Subgroup G := U.map L.subtype with hT'
    have hTne : T ≠ ⊥ := by
      rw [hT', Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
      exact hU
    have hT2 : IsPGroup 2 T := hU2.map _
    have hnp' : (n : G) ^ p = 1 := by
      have := congrArg Subtype.val hnp
      simpa using this
    have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers (n : G)) := by
      refine isElemAbelian_sup hBA (isElemAbelian_zpowers_of_pow hnp') fun b hb c hc => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact (Commute.zpow_right (hnB b hb : Commute b (n : G)) k).eq
    have hET : B ⊔ Subgroup.zpowers (n : G) ≤ Subgroup.normalizer (T : Set G) := by
      refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.mpr ?_)
      · have h := mem_normalizer_of_forall_conj_mem (W := T) (g := b⁻¹) (fun t ht => by
          obtain ⟨u, hu, rfl⟩ := ht
          refine ⟨_, hUA (γB ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ u hu, ?_⟩
          simp only [Subgroup.coe_subtype, hγB, ggGamma_coe, inv_inv])
        simpa using Subgroup.inv_mem _ h
      · have h := mem_normalizer_of_forall_conj_mem (W := T) (g := (n : G)⁻¹) (fun t ht => by
          obtain ⟨u, hu, rfl⟩ := ht
          refine ⟨_, hUn u hu, ?_⟩
          simp)
        simpa using Subgroup.inv_mem _ h
    have hc := card_le_of_twoLocal hp ⟨T, hTne, hT2, rfl⟩ hET hE
    rw [← hS.1.2.1] at hc
    have heq : B = B ⊔ Subgroup.zpowers (n : G) := Subgroup.eq_of_le_of_card_ge le_sup_left hc
    have hnB' : (n : G) ∈ B := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    refine ⟨⟨n, hnB'⟩, ?_⟩
    ext l
    rw [hγB, ggGamma_coe, MulAut.conj_apply]
    rfl
  obtain ⟨U, hU, hU2, hUA⟩ := hT L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL γB.range γs.range hle hAs hAI hAsI hr h3' hmax
  obtain ⟨T, hTne, hT2, hBsT⟩ := exists_twoSubgroup_of_normalizes θ hBsN hU hU2
    (fun e he u hu => hUA _ ⟨⟨e, he⟩, rfl⟩ (ggBeta L θ hBsN ⟨e, he⟩)
      (fun l => ggBeta_ggQuotHom L hBsN θ ⟨e, he⟩ l) u hu)
  have hc := card_le_of_twoLocal hp ⟨T, hTne, hT2, rfl⟩ hBsT hBs
  rw [← hS.1.2.1] at hc
  have heq : B = Bs := Subgroup.eq_of_le_of_card_ge hBBs hc
  refine ⟨hBsN, fun b hb => h3 b (heq ▸ hb)⟩

end Config

theorem ggBstarInnerDiagLInputOn_of_labelsTwoLocal {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGBstarTwoLocalSCr p r R I) :
    GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hnc := ggLNoncyclicInputOn_pilot G p B x L hC.1
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2⟩) hM)
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  refine ⟨hL, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hSl, hsplit, hBN, h3⟩, r, hlift, hT⟩
  exact ⟨hs, hna, θ, hSl, hsplit, bstar_innerDiag_of_twoLocalSCr hC hnc hL θ hBN h3 hlift hT⟩

end CFSG.StandardType

end
