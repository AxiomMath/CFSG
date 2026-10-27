module

public import CFSG.LocalAnalysis.StandardType.ExcPay.E7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxElem
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7E8Five

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.GGFinModel
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem card_range_ggGamma_le_card_inf {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G)) :
    Nat.card (ggGamma X hN).range ≤ Nat.card ↥(X ⊓ Bs : Subgroup G) := by
  let f' : ↥(X ⊓ Bs) → (ggGamma X hN).range :=
    fun z => ⟨ggGamma X hN ⟨z.1, z.2.2⟩, ⟨⟨z.1, z.2.2⟩, rfl⟩⟩
  refine Nat.card_le_card_of_surjective f' ?_
  rintro ⟨y, hy⟩
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
  obtain ⟨z, hz, hc⟩ := hsplit b b.2
  let c : Bs := ⟨(b : G) * z⁻¹, Bs.mul_mem b.2 (Bs.inv_mem hz.2)⟩
  have hc1 : ggGamma X hN c = 1 := (ggGamma_eq_one_iff X hN c).2 hc
  have hb_eq : b = c * ⟨z, hz.2⟩ := by
    apply Subtype.ext
    simp [c]
  refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  change (ggGamma X hN) ⟨z, hz.2⟩ = y
  rw [← hb, hb_eq, map_mul, hc1, one_mul]

theorem isToralSubgroup_E7_three {f : ℕ} (A : Subgroup (ModGL (langTag .E7) GGL))
    (hA : A ≤ ggFixGp .E7 f) (hAel : IsElemAbelian 3 A) (hcard : 3 ^ 7 ≤ Nat.card A) :
    IsToralSubgroup .E7 GGL A := by
  have h2 : ¬ 3 ∣ Nat.card (ZMod 2) := by
    rw [Nat.card_zmod]
    norm_num
  exact ExcFramesHalf.bigElemAbelianToralBar_E7_three (ZMod 2) h2 A (hA.trans inf_le_left)
    (fun a ha b hb => congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    hAel.2 (le_trans (Nat.pow_le_pow_right (by norm_num) (by decide)) hcard)

private theorem pow_six_le_card_range_ggGamma_E7_three {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {k : ℕ} (hk : 1 ≤ k)
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr 3 B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ k ≤ lab.n) 3 Bs X) :
    ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 6 ≤ Nat.card (ggGamma X hN).range := by
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, hGR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  have htag : lab.tag = .E7 := hP.1.1.1
  have hF : LargeEvenLabelAll lab (fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 3 r R I L' ψ A → 3 ^ 6 ≤ Nat.card A) :=
    (largeEvenLabelAll_torusLift_excPlus (p := 3) Nat.prime_three (by decide)
      ⟨Or.inl htag, hP.1.1.2⟩).mono fun R _ I _ hR =>
        ⟨ggNbrExcPlusRank lab.tag, hR, fun L' _ _ ψ A hA => by
          have h6 : ggNbrExcPlusRank lab.tag = 6 := by rw [htag]; rfl
          rw [h6] at hA
          exact hA.2.2.2.2.2.1⟩
  obtain ⟨hN, hQ6, -⟩ := ggX_exists_overGamma_lift ggLabelRigidInput_holds hcfg hX hInn hΛ hhas
    (fun _ _ A => 3 ^ 6 ≤ Nat.card A) hF
  exact ⟨hN, hQ6⟩

theorem pow_seven_le_card_inf_of_route_E7_three_of_le {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {k : ℕ} (hk : 1 ≤ k)
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr 3 B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ k ≤ lab.n) 3 Bs X) :
    3 ^ 7 ≤ Nat.card ↥(X ⊓ Bs : Subgroup G) := by
  obtain ⟨hN, hQ6⟩ := pow_six_le_card_range_ggGamma_E7_three hk hcfg hX hmark
  have hBs : IsElemAbelian 3 Bs := hcfg.1.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.1.1.2.1.2.2.2
  obtain ⟨f, hkf, hplus, κ, hinn⟩ := exists_e7Equiv_of_marking_of_le hk hmark
  have hinn' : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ := fun b hb => (hinn b hb).2
  have hZ : Subgroup.center ↥X = ⊥ := by
    have h1 := Subgroup.map_center_eq κ.symm
    rw [center_adjointGroup_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ κ.symm.injective).1 h1
  have hle := card_range_ggGamma_le_card_inf hN (excPay_inner_split hBs hSC hZ hinn').1
  obtain ⟨E, hEel, hcardE, hESC⟩ := exists_excPay_image_inf_E7 hBs hSC hZ κ hinn'
  have hE6 : 3 ^ (Tag.E7.rank - 1) ≤ Nat.card E := by
    rw [show Tag.E7.rank - 1 = 6 from rfl, hcardE]
    exact hQ6.trans hle
  rw [← hcardE]
  exact ExcFramesHalf.ggExcHalfMaxElemInput_E7 ExcFramesHalf.bigElemAbelianToralBar_E7_three
    ExcFramesHalf.bigElemAbelianToralBar_E7_five (GaloisField 2 f) 3 Nat.prime_three (by decide)
    (by rw [GaloisField.card 2 f (by omega)]; exact hplus) (Or.inl rfl) E hEel hE6
    (fun g hg hgp => hESC g (fun y hy => ((Subgroup.mem_centralizer_iff.mp hg) y hy).symm) hgp)

theorem exists_excPaySquare_of_route_E7_three {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {k : ℕ} (hk : 1 ≤ k)
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr 3 B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ k ≤ lab.n) 3 Bs X)
    (ht : GGExcFive .E7) :
    ∃ f : ℕ, k ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧
      ∃ _ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X,
        Subgroup.center ↥X = ⊥ ∧ Nonempty (ExcPaySquare .E7 ht f 3 Bs X) := by
  obtain ⟨f, hkf, hplus, κ, hinn⟩ := exists_e7Equiv_of_marking_of_le hk hmark
  have hf : 1 ≤ f := le_trans hk hkf
  have hZ : Subgroup.center ↥X = ⊥ := by
    have h1 := Subgroup.map_center_eq κ.symm
    rw [center_adjointGroup_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ κ.symm.injective).1 h1
  obtain ⟨S⟩ := exists_excPaySquare_E7_of_toral (ht := ht)
    Nat.prime_three le_rfl hf hplus hcfg.1.1.2.1.2.1 hcfg.1.1.2.1.2.2.2 κ hinn
    (pow_seven_le_card_inf_of_route_E7_three_of_le hk hcfg hX hmark)
    (fun A hA hAel hcard => isToralSubgroup_E7_three A hA hAel hcard)
  exact ⟨f, hkf, hplus, κ, hZ, ⟨S⟩⟩

theorem exists_excPhanPayload_of_route_E7_three {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr 3 B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) 3 Bs X) :
    GGExcPhanPayloadOf 7 CoxeterMatrix.E₇ .E7 3 Bs X := by
  obtain ⟨f, hf, hplus, κ, -, ⟨S⟩⟩ := exists_excPaySquare_of_route_E7_three (k := 2)
    (by norm_num) hcfg hX hmark (ht := Or.inr (Or.inr (Or.inl rfl)))
  exact excPhanPayloadOf_E7_of_square Nat.prime_three (by norm_num) hf hplus
    (isCentralQuotientOf_E7_of_equiv κ) S

end CFSG.StandardType.ExcPay
