module

public import CFSG.Quasithin.H13.NQCatC2J1F
public import CFSG.Quasithin.H13.NQCatC2L2p
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113J1ZK
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Simplicity.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.EmptyFaithful.R3c2Excl
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152He9Y1
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.SBc5Common
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.A6S4L1
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.U3L14E
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrth
public import CFSG.Quasithin.Vol2.Ch10SecBL32O2
public import CFSG.Quasithin.Vol2.Ch10SecBL32Prod
public import CFSG.Quasithin.Vol2.Ch10SecC8Main12
public import CFSG.Quasithin.Vol2.Ch10SecC9Entry
public import CFSG.Quasithin.Vol2.Ch10SecC9L32
public import CFSG.Quasithin.Vol2.Ch10SecC9S5c
public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdC
public import CFSG.Quasithin.Vol2.Ch10SecQ9G10
public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.Quasithin.Vol2.Ch10SecQ9H9
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Main
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Lift
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeC2
public import CFSG.Quasithin.Vol2.Ch6Sec1G22
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem11
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12
public import CFSG.Sporadic.Schreier.M23

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513 CFSG.GorensteinWalter CFSG.Walter
  CFSG.Walter.J1Props CFSG.Blueprint

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

@[expose] def OddInner (G : Type) [Group G] : Prop :=
  ∀ α : MulAut G, Odd (orderOf α) → ∃ g : G, α = MulAut.conj g

theorem OddInner.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G' ≃* G)
    (h : OddInner G) : OddInner G' := by
  intro α hα
  obtain ⟨g, hg⟩ := h (MulAut.congr e α) (by rwa [MulEquiv.orderOf_eq])
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun f : MulAut G => e.symm (f (e x))) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply, map_mul, map_inv] at h1
  rw [MulAut.conj_apply]
  exact h1

variable {A : Type} [Group A]

theorem centerFree_of_mulEquiv {Q : Subgroup A} {G : Type} [Group G] (e : ↥Q ≃* G)
    (hc : ∀ z : G, (∀ y : G, z * y = y * z) → z = 1) : CenterFree Q := by
  intro z hz hzc
  have h1 : e ⟨z, hz⟩ = 1 := hc _ fun y => by
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hzc y y.2))
  exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))

theorem CenterFree.map_conj {Q : Subgroup A} (hZ : CenterFree Q) (g : A) :
    CenterFree (Q.map (MulAut.conj g).toMonoidHom) := by
  intro z hz hzc
  rw [mem_map_conj_iff] at hz
  have h1 : g⁻¹ * z * g = 1 := hZ _ hz fun x hx => by
    have hx' : g * x * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom :=
      mem_map_conj_iff.mpr (by rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]; exact hx)
    have := hzc _ hx'
    calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [this]
      _ = x * (g⁻¹ * z * g) := by group
  calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem factC2Hall_holds :
    H13.FactC2Hall := by
  intro A _ _ Q₁ Q₂ R₁ R₂ S B D s hQ hs hQ₂ hR₂ hc hi hS2 hSN hSQ hRQ _ hRL hSR hB hDc hDo
    hDN hBD hDS
  have h : CommPair Q₁ Q₂ := CommPair.of_commutator hc hi
  let e₂₁ : ↥Q₂ ≃* ↥Q₁ := (MulEquiv.subgroupCongr hQ₂).trans
    (Subgroup.equivMapOfInjective Q₁ (MulAut.conj s).toMonoidHom (MulAut.conj s).injective).symm
  obtain ⟨hsimp₁, hZ₁, hinn₁⟩ : IsSimpleGroup ↥Q₁ ∧ CenterFree Q₁ ∧ OddInner ↥Q₁ := by
    rcases hQ with hJ | ⟨p, hp, h5, h8, hPSL⟩
    · obtain ⟨e⟩ : Nonempty (↥Q₁ ≃* NativeSporadic.Carrier .J1) := hJ
      refine ⟨(jankoHypOfMulEquiv jankoHyp (e.trans walterJ1EquivNative.symm)).isSimpleGroup,
        fun z hz hzc => ?_, fun α _ => exists_eq_conj_of_j1 e α⟩
      exact congrArg Subtype.val
        (eq_one_of_forall_commute_of_j1 e (z := ⟨z, hz⟩) fun k => Subtype.ext (hzc k k.2))
    · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hPSL
      let e : ↥Q₁ ≃* PSL2 K := e₀.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
      have hK' : Nat.card K = p := by rw [hK, pow_one]
      have hodd : IsOddPrimePower (Nat.card K) :=
        ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, hK⟩
      have hp11 := eleven_le hp h5 h8
      have : IsSimpleGroup (PSL2 K) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK']; omega)
      refine ⟨e.isSimpleGroup, centerFree_of_mulEquiv e fun z hz => ?_,
        OddInner.of_mulEquiv e
          (inner_of_odd_psl2 hodd (ringAut_mul_self hp le_rfl (by norm_num) hK))⟩
      have hmem : z ∈ Subgroup.center (PSL2 K) :=
        Subgroup.mem_center_iff.mpr fun y => (hz y).symm
      rw [psl2_center_eq_bot K, Subgroup.mem_bot] at hmem
      exact hmem
  have hZ₂ : CenterFree Q₂ := by
    rw [hQ₂]
    exact hZ₁.map_conj s
  have hsimp₂ : IsSimpleGroup ↥Q₂ := e₂₁.isSimpleGroup
  have hinn₂ : OddInner ↥Q₂ := hinn₁.of_mulEquiv e₂₁
  have hsw₁ : ∀ z ∈ Q₁, s * z * s⁻¹ ∈ Q₂ := fun z hz => by
    rw [hQ₂]
    exact ⟨z, hz, rfl⟩
  have hsw₂ : ∀ z ∈ Q₂, s * z * s⁻¹ ∈ Q₁ := by
    have hne : Q₁ ≠ Q₂ := fun he => by
      have : Q₁ = ⊥ := by rw [← hi, ← he, inf_idem]
      exact (Subgroup.nontrivial_iff_ne_bot Q₁).mp inferInstance this
    rcases h.conj_eq_or_eq hZ₁ (hSN hs) (Q' := Q₂) (Or.inr rfl) with h1 | h1
    · intro z hz
      rw [← h1]
      exact ⟨z, hz, rfl⟩
    · exfalso
      apply hne
      have : Q₁.map (MulAut.conj s).toMonoidHom = Q₂.map (MulAut.conj s).toMonoidHom := by
        rw [← hQ₂, h1]
      exact Subgroup.map_injective (MulAut.conj s).injective this
  have hDo' : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    Odd.of_dvd_nat hDo (Subgroup.orderOf_dvd_natCard D hd)
  have hDN₁ : D ≤ Subgroup.normalizer (Q₁ : Set A) := fun d hd =>
    h.mem_normalizer_of_odd hZ₁ (hDN hd) (hDo' d hd)
  have hDN₂ : D ≤ Subgroup.normalizer (Q₂ : Set A) := fun d hd =>
    h.symm.mem_normalizer_of_odd hZ₂ (by rw [sup_comm]; exact hDN hd) (hDo' d hd)
  have hinnD : InnerOn (Q₁ ⊔ Q₂) D :=
    h.innerOn_sup (innerOn_of_odd hDN₁ hDo hinn₁) (innerOn_of_odd hDN₂ hDo hinn₂)
  have hZQ : CenterFree (Q₁ ⊔ Q₂) := h.centerFree_sup hZ₁ hZ₂
  have hD₀Q : img hinnD hZQ hDN ≤ Q₁ ⊔ Q₂ := img_le hinnD hZQ hDN
  have hD₀c : IsCyclic ↥(img hinnD hZQ hDN) := isCyclic_img hinnD hZQ hDN hDc
  have hD₀o : Odd (Nat.card (img hinnD hZQ hDN)) := odd_card_img hinnD hZQ hDN hDo
  have hR₂Q : R₂ ≤ Q₂ := by
    rw [hR₂, hQ₂]
    exact Subgroup.map_mono hRQ
  have hBQ : B ≤ Q₁ ⊔ Q₂ := hB.1.trans (inf_le_left.trans (sup_le_sup hRQ hR₂Q))
  have hBD₀ : B ≤ Subgroup.normalizer (img hinnD hZQ hDN : Set A) := fun b hb =>
    mem_normalizer_of_conj_mem' fun x hx => conj_mem_img hinnD hZQ hDN (hBQ hb) (hBD hb) hx
  have hT : ∀ X : Subgroup A, X ≤ Q₁ ⊔ Q₂ → IsPGroup 2 ↥X → S ⊓ (Q₁ ⊔ Q₂) ≤ X →
      X = S ⊓ (Q₁ ⊔ Q₂) := fun X hXQ hX2 hSX => hSQ.eq_of_le hSX hXQ hX2
  have hperm : ∀ t ∈ S ⊓ (Q₁ ⊔ Q₂), ∀ x ∈ img hinnD hZQ hDN, ∃ x' ∈ img hinnD hZQ hDN,
      ∃ t' ∈ S ⊓ (Q₁ ⊔ Q₂), t * x = x' * t' := by
    intro t ht x hx
    obtain ⟨x', hx', t'', ht'', he⟩ :=
      conj_mem_img_mul hinnD hZQ hDN hSN hS2 hDS hT (Subgroup.mem_inf.mp ht).1 hx
    refine ⟨x', hx', t'' * t, mul_mem ht'' ht, ?_⟩
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = x' * t'' * t := by rw [he]
      _ = x' * (t'' * t) := by group
  have hsD : ∀ x ∈ img hinnD hZQ hDN, ∃ x' ∈ img hinnD hZQ hDN, ∃ t ∈ S ⊓ (Q₁ ⊔ Q₂),
      s * x * s⁻¹ = x' * t := fun x hx =>
    conj_mem_img_mul hinnD hZQ hDN hSN hS2 hDS hT hs hx
  obtain ⟨hP₁, hP₂, hB9, hB₁, hB₂⟩ := b_facts h hs hR₂ hRQ hR₂Q hRL hSR hB
  have hPF : h.img₁ (img hinnD hZQ hDN) ≤
        R₁ ⊓ Subgroup.normalizer ((S ⊓ R₁ : Subgroup A) : Set A) ∧
      h.img₂ (img hinnD hZQ hDN) ≤ R₂ ⊓ Subgroup.normalizer ((S ⊓ R₂ : Subgroup A) : Set A) := by
    rcases hQ with hJ | ⟨p, hp, h5, h8, hPSL⟩
    ·
      obtain ⟨e⟩ : Nonempty (↥Q₁ ≃* NativeSporadic.Carrier .J1) := hJ
      have hJ₁ : J1.JankoHyp ↥Q₁ :=
        jankoHypOfMulEquiv jankoHyp (e.trans walterJ1EquivNative.symm)
      obtain ⟨h1, h2⟩ := j1_img_le h hJ₁ (jankoHypOfMulEquiv hJ₁ e₂₁) hsw₁ hsw₂ hSQ hD₀Q hD₀c
        hD₀o hperm hsD hBQ hBD₀ hB9 hB₁ hB₂
      exact ⟨h1.trans hP₁, h2.trans hP₂⟩
    ·
      obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hPSL
      let e : ↥Q₁ ≃* PSL2 K := e₀.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
      have hK' : Nat.card K = p := by rw [hK, pow_one]
      obtain ⟨eR₁⟩ := nonempty_l24_of_le hp hK' h8 e hRQ hRL
      let eR₂ : ↥R₂ ≃* L24 := (MulEquiv.subgroupCongr hR₂).trans
        ((Subgroup.equivMapOfInjective R₁ (MulAut.conj s).toMonoidHom
          (MulAut.conj s).injective).symm.trans eR₁)
      have eS₁ : S ⊓ (Q₁ ⊔ Q₂) ⊓ Q₁ = S ⊓ Q₁ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂)]
      have eS₂ : S ⊓ (Q₁ ⊔ Q₂) ⊓ Q₂ = S ⊓ Q₂ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Q₂ ≤ Q₁ ⊔ Q₂)]
      have eT₁ : S ⊓ (R₁ ⊔ R₂) ⊓ R₁ = S ⊓ R₁ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_left : R₁ ≤ R₁ ⊔ R₂)]
      have eT₂ : S ⊓ (R₁ ⊔ R₂) ⊓ R₂ = S ⊓ R₂ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : R₂ ≤ R₁ ⊔ R₂)]
      have hperm₁ := h.perm_img₁ hSQ.1 hD₀Q (h.img_le_of_sylow le_rfl le_rfl hSQ).1 hperm
      rw [eS₁] at hperm₁
      have hperm₂ := h.perm_img₂ hSQ.1 hD₀Q (h.img_le_of_sylow le_rfl le_rfl hSQ).2 hperm
      rw [eS₂] at hperm₂
      have hp11 := eleven_le hp h5 h8
      refine ⟨psl2_factor hp hK' h8 hp11 e (eS₁ ▸ h.isSylowTwoOf_inf₁ le_rfl le_rfl hSQ) hRQ eR₁
        (eT₁ ▸ h.isSylowTwoOf_inf₁ hRQ hR₂Q hSR) (h.img₁_le _) (h.isCyclic_img₁ hD₀Q hD₀c)
        (Odd.of_dvd_nat hD₀o (h.card_img₁_dvd hD₀Q)) hperm₁ hP₁ hB₁ fun a ha => ?_,
        psl2_factor hp hK' h8 hp11 (e₂₁.trans e) (eS₂ ▸ h.isSylowTwoOf_inf₂ le_rfl le_rfl hSQ)
        hR₂Q eR₂ (eT₂ ▸ h.isSylowTwoOf_inf₂ hRQ hR₂Q hSR) (h.img₂_le _)
        (h.isCyclic_img₂ hD₀Q hD₀c) (Odd.of_dvd_nat hD₀o (h.card_img₂_dvd hD₀Q)) hperm₂ hP₂ hB₂
        fun b hb => ?_⟩
      · obtain ⟨b', hb', hab⟩ := h.exists_of_mem_img₁ ha
        exact h.mem_normalizer_img₁ (h.img₁_le B ha) hb' (hBD₀ hab)
      · obtain ⟨a, ha, hab⟩ := h.exists_of_mem_img₂ hb
        exact h.mem_normalizer_img₂ ha (h.img₂_le B hb) (hBD₀ hab)
  have hD₀B := le_of_isHallTwoPrimeOf hB
    (le_inf_normalizer_of_img h hRQ hR₂Q hSR hD₀Q hPF.1 hPF.2) hD₀o hBD₀
  exact (le_img_sup hinnD hZQ hDN).trans (sup_le_sup_right hD₀B _)

end CFSG.Quasithin.H13.NQCat.C2
