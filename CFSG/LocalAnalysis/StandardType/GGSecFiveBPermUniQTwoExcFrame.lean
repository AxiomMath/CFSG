module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootRed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.Line63.H5

theorem map_redMk_subgroupOf_self {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    (L.subgroupOf (Subgroup.normalizer (L : Set G))).map (redMk L) = (redMkL L).range := by
  ext q
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨⟨l, Subgroup.le_normalizer l.2⟩, l.2, rfl⟩

theorem card_redB_inf_centralizer {G : Type} [Group G] [Finite G] {L Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hBs : IsElemAbelian 3 Bs)
    (hLp : commutator L = ⊤)
    (hNbar : (redMkB hN).range ≤ Subgroup.normalizer ((redMkL L).range : Set (RedGrp L))) :
    Nat.card ↥((redMkB hN).range ⊓ Subgroup.centralizer ((redMkL L).range : Set (RedGrp L))) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨hbar, hc⟩ := card_range_ggGamma_eq_redMk hN le_rfl hN hLp
  have key : ∀ (X₁ X₂ : Subgroup (RedGrp L)) (_ : X₁ = X₂)
      (h₁ : (redMkB hN).range ≤ Subgroup.normalizer (X₁ : Set (RedGrp L)))
      (h₂ : (redMkB hN).range ≤ Subgroup.normalizer (X₂ : Set (RedGrp L))),
      Nat.card (ggGamma X₁ h₁).range = Nat.card (ggGamma X₂ h₂).range := by
    rintro X₁ X₂ rfl h₁ h₂
    rfl
  have hc' : Nat.card (ggGamma L hN).range = Nat.card (ggGamma (redMkL L).range hNbar).range :=
    hc.trans (key _ _ (map_redMk_subgroupOf_self L) hbar hNbar)
  have hker : ∀ {H : Type} [Group H] (X Y : Subgroup H)
      (hY : Y ≤ Subgroup.normalizer (X : Set H)),
      Nat.card (ggGamma X hY).ker = Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set H)) := by
    intro H _ X Y hY
    have hk : (ggGamma X hY).ker = (Subgroup.centralizer (X : Set H)).subgroupOf Y := by
      ext b
      rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf]
    rw [hk, inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective Y.subtype_injective]
  have h1 := Subgroup.card_ker_mul_card_range (ggGamma L hN)
  have h2 := Subgroup.card_ker_mul_card_range (ggGamma (redMkL L).range hNbar)
  rw [card_redB hN hBs, ← hc'] at h2
  rw [hker] at h1 h2
  have hpos : 0 < Nat.card (ggGamma L hN).range := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)

theorem exists_redUniLFrame_of_model
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hLp : commutator L = ⊤)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3)
    {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    {F : Type} [Field F] [Finite F] {f : ℕ}
    (hNbar : (redMkB hN).range ≤
      Subgroup.normalizer ((redMkL L).range : Set (RedGrp L)))
    (φ : ↥(unitarySU 2 f F n) →* (redMkL L).range)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma (redMkL L).range hNbar).range, ∃ t : Fin n → F,
      LineU.ActsDiagU φ a t) :
    ∃ (eta' : ↥(redMkB hN).range ≃* (Fin n → Multiplicative (ZMod 3)))
      (σ : ↥(unitarySU 2 f F n) →* RedGrp L)
      (χ : Multiplicative (ZMod 3) →* Fˣ),
      (∀ b : ↥Bs, eta' ⟨redMkB hN b, b, rfl⟩ = eta b) ∧
        GGSecFiveBPermUniLFrame (redMkB hN).range (redMkL L).range eta' 1 σ χ := by
  classical
  let ι : ↥Bs ≃* ↥(redMkB hN).range := MonoidHom.ofInjective (redMkB_injective hN hBs)
  let eta' : ↥(redMkB hN).range ≃* (Fin n → Multiplicative (ZMod 3)) := ι.symm.trans eta
  have hι : ∀ b : ↥Bs, ι b = ⟨redMkB hN b, b, rfl⟩ := fun b =>
    Subtype.ext (MonoidHom.ofInjective_apply _)
  have heta' : ∀ b : ↥Bs, eta' ⟨redMkB hN b, b, rfl⟩ = eta b := by
    intro b
    rw [← hι b]
    simp [eta']
  have hA' : (ggAutomizer (redMkL L).range (redMkB hN).range).map
      (MulAut.congr eta').toMonoidHom = aPermutationFull n 3 := by
    have h := ggAutomizer_redMk_eq hBs hN Subgroup.le_normalizer hN
    rw [map_redMk_subgroupOf_self L] at h
    rw [h, Subgroup.map_map]
    have he : (MulAut.congr eta').toMonoidHom.comp (MulAut.congr ι).toMonoidHom =
        (MulAut.congr eta).toMonoidHom := by
      ext a b
      simp [eta', ι, MulAut.congr_apply]
    rw [he, hA]
  have hC' : Nat.card ↥((redMkB hN).range ⊓
      Subgroup.centralizer ((redMkL L).range : Set (RedGrp L))) ≤ 3 := by
    rw [card_redB_inf_centralizer hN hBs hLp hNbar]
    exact hC
  obtain ⟨σ, χ, hframe⟩ := exists_uniLFrame_of_model Nat.prime_three (by norm_num)
    (isElemAbelian_redB hN hBs) (redSC hN hBs hSC) hC' hn eta' hA' hNbar φ hM hdiag 1
  exact ⟨eta', σ, χ, heta', hframe⟩


theorem exists_redUniLFrame_of_uniQTwoSix (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod p)))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 p)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel 6 p lab ∧ lab.n ≤ 1)
      p Bs L) :
    p = 3 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (eta' : ↥(redMkB hN).range ≃* (Fin 6 → Multiplicative (ZMod p)))
      (σ : ↥(unitarySU 2 1 K 6) →* RedGrp L) (χ : Multiplicative (ZMod p) →* Kˣ),
      Nat.card K = 4 ∧ (∀ b : ↥Bs, eta' ⟨redMkB hN b, b, rfl⟩ = eta b) ∧
        GGSecFiveBPermUniLFrame (redMkB hN).range (redMkL L).range eta' 1 σ χ := by
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hInn : GGInnerDiagOn Bs L := hR.1.2.2.1.1
  have hmark : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => GGSecFiveBPermUniLabel 6 p lab ∧ lab.n ≤ 1) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hLab
  obtain ⟨lab, -, hhas, -, -, -, -, -, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨hUni, hm⟩ := hP
  obtain ⟨tag, rank, m⟩ := lab
  have hUni' : tag = .twA ∧ rank = 6 - 1 ∧ p ∣ 2 ^ m + 1 := hUni
  obtain ⟨htag, hrank, hpq⟩ := hUni'
  have hm1 : m ≤ 1 := hm
  have hm' : m = 1 := by
    rcases Nat.lt_or_ge m 1 with h0 | h1
    · have hm0 : m = 0 := by omega
      rw [hm0] at hpq
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using hpq)) hp2
    · omega
  subst tag
  have hrank5 : rank = 5 := by omega
  subst rank
  subst m
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq)
  subst hp3
  refine ⟨rfl, ?_⟩
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  obtain ⟨F, hField, hFinite, hChar, hLp, θ, hN, hF, hBsI⟩ :=
    unitaryTwoRawDatum (r := 5) hRig hInn hhas hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hγ := four_le_card_ggGamma_of_unitary_six_L_of_cfg hRig hcfg hInn (by norm_num) hhas hΛ hN
  obtain ⟨hNbar, φ, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF hLp θ hN hBs hBsI hγ
  have hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 :=
    hcfg.card_bstar_inf_centralizer_L.le
  obtain ⟨eta', σ, χ, heta', hframe⟩ :=
    exists_redUniLFrame_of_model hN hBs hLp hSC hC (by norm_num : 4 ≤ 6) eta hA
      hNbar φ hM hdiag
  exact ⟨F, hField, hFinite, hChar, hN, eta', σ, χ, hF, heta', hframe⟩

end CFSG.StandardType

end
