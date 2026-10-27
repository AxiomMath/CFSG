module

public import CFSG.OddTranspositions.SixSeven
public import CFSG.OddTranspositions.SixNineUnconditional
public import CFSG.OddTranspositions.SixFiveInputs
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.BlockAction

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem conj_mul_conj_of_comm {a q₁ q₂ : G} (ha : a * a = 1) (h1 : q₁ * q₁ = 1)
    (h2 : q₂ * q₂ = 1) (h12 : Commute q₁ q₂) (hp : Commute (a * q₁ * a) q₂) :
    (q₁ * a * q₁⁻¹) * a * (q₂ * a * q₂⁻¹) = (q₁ * q₂) * a * (q₁ * q₂)⁻¹ := by
  have hq1 : q₁⁻¹ = q₁ := inv_eq_of_mul_eq_one_right h1
  have hq2 : q₂⁻¹ = q₂ := inv_eq_of_mul_eq_one_right h2
  rw [mul_inv_rev, hq1, hq2]
  have key : (a * q₁ * a) * q₂ = q₂ * (a * q₁ * a) := hp.eq
  calc q₁ * a * q₁ * a * (q₂ * a * q₂) = q₁ * ((a * q₁ * a) * q₂) * a * q₂ := by group
    _ = q₁ * (q₂ * (a * q₁ * a)) * a * q₂ := by rw [key]
    _ = q₁ * q₂ * a * q₁ * (a * a) * q₂ := by group
    _ = q₁ * q₂ * a * (q₁ * q₂) := by rw [ha, mul_one]; group
    _ = q₁ * q₂ * a * (q₂ * q₁) := by rw [h12.eq]

theorem commute_conj_of_orderOf_mul_eq_four {t b : G} (ht : t * t = 1) (hb : b * b = 1)
    (h4 : orderOf (t * b) = 4) : Commute (t * b * t⁻¹) b := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hpow : (t * b) ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one _
  have h4' : (t * b * t * b) * (t * b * t * b) = 1 := by
    rw [← hpow]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hinv : t * b * t * b = (t * b * t * b)⁻¹ := (inv_eq_of_mul_eq_one_right h4').symm
  rw [hti]
  show t * b * t * b = b * (t * b * t)
  calc t * b * t * b = (t * b * t * b)⁻¹ := hinv
    _ = b⁻¹ * t⁻¹ * b⁻¹ * t⁻¹ := by group
    _ = b * (t * b * t) := by rw [hti, hbi]; group

section LocalStep

variable (hC : HypothesisC D) {β : Set G} (hβ : β ∈ Aalpha D hC.alpha) {a b c : G}
  (ha : a ∈ hC.alpha) (hc : c ∈ hC.alpha) (hac : Commute a c) (hane : a ≠ c) (hb : b ∈ β)
  (h4 : orderOf (a * c * b) = 4)
  (hno : ∀ x ∈ D, x ∈ Subgroup.closure {a, b} → IsTriangle D a x c → ¬ IsThirdKind a x c)
include hβ ha hc hac hane hb h4 hno

theorem exists_Q_conj_of_mem_secondKindS {y : G} (hyD : y ∈ D) (hyS : y ∈ Subgroup.zpowers a ⊔ conjClosure (Subgroup.closure {a, b}) (a * c))
    {x : G} (hx : x ∈ Subgroup.closure ({a, b, c} : Set G)) (hxy : x * a * x⁻¹ = y) :
    ∃ q ∈ conjClosure (Subgroup.closure {a, b}) (a * c), q * a * q⁻¹ = y := by
  classical
  have hD := hC.setup.oddT
  have hN := hC.setup.normal
  have htri : IsTriangle D a b c :=
    isTriangle_of_mem_Aalpha hD hN hC.isBlock_alpha hβ ha hc hac hane hb
  have SK : SecondKindStructure a b c := OddTransp.secondKind_structure hD hN htri h4 hno
  set Q := conjClosure (Subgroup.closure {a, b}) (a * c) with hQ
  set A := Subgroup.closure ({a, b} : Set G) with hA
  have hAX : A ≤ Subgroup.closure ({a, b, c} : Set G) :=
    Subgroup.closure_mono (by intro z hz; rcases hz with rfl | rfl <;> simp)
  have hAN : A ≤ Subgroup.normalizer (Q : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact SK.normal g (hAX hg) h
    · intro hh
      have := SK.normal g⁻¹ (Subgroup.inv_mem _ (hAX hg)) _ hh
      simpa [mul_assoc] using this
  have hxAQ : x ∈ ((A ⊔ Q : Subgroup G) : Set G) := by
    rw [secondKind_closure_eq hD hN htri h4 hno]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hxAQ
  obtain ⟨g, hg, q₀, hq₀, rfl⟩ := hxAQ
  set q := g * q₀ * g⁻¹ with hqdef
  have hqQ : q ∈ Q := SK.normal g (hAX hg) q₀ hq₀
  set v := g * a * g⁻¹ with hv
  have hvD : v ∈ D := hN g a htri.1
  have hvA : v ∈ A :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (Subgroup.subset_closure (by simp)))
      (Subgroup.inv_mem _ hg)
  have hyv : y = q * v * q⁻¹ := by rw [← hxy, hqdef, hv]; group
  have hQS : Q ≤ Subgroup.zpowers a ⊔ Q := le_sup_right
  have haS : a ∈ Subgroup.zpowers a ⊔ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hvS : v ∈ Subgroup.zpowers a ⊔ Q := by
    have : v = q⁻¹ * y * q := by rw [hyv]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQS hqQ)) hyS) (hQS hqQ)
  have hva : Commute v a := commute_of_mem_sup_D hD hN htri h4 hno hvD htri.1 hvS haS
  rcases eq_one_or_eq_of_mem_closure_pair hD htri.1 htri.2.2.1 htri.2.2.2.2.2.1 hvA hva with
    h | h
  · exact absurd h (hD.ne_one hvD)
  · exact ⟨q, hqQ, by rw [hyv, h]⟩

theorem mem_alpha_of_conj_mem_secondKindS {d : G} (hdD : d ∈ D)
    (hdS : d ∈ Subgroup.zpowers a ⊔ conjClosure (Subgroup.closure {a, b}) (a * c))
    {x : G} (hx : x ∈ Subgroup.closure ({a, b, c} : Set G)) (hxd : x * a * x⁻¹ = d) :
    d ∈ hC.alpha := by
  classical
  have hD := hC.setup.oddT
  have hN := hC.setup.normal
  have hblock := hC.isBlock_alpha
  have htri : IsTriangle D a b c := isTriangle_of_mem_Aalpha hD hN hblock hβ ha hc hac hane hb
  have SK : SecondKindStructure a b c := OddTransp.secondKind_structure hD hN htri h4 hno
  set Q := conjClosure (Subgroup.closure {a, b}) (a * c) with hQ
  have haD : a ∈ D := htri.1
  have hcD : c ∈ D := htri.2.1
  have ha2 : a * a = 1 := hD.mul_self_eq_one haD
  have hai : a⁻¹ = a := hD.inv_eq haD
  have hQS : Q ≤ Subgroup.zpowers a ⊔ Q := le_sup_right
  have haS : a ∈ Subgroup.zpowers a ⊔ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  obtain ⟨qd, hqd, hqdd⟩ := exists_Q_conj_of_mem_secondKindS hC hβ ha hc hac hane hb h4 hno
    hdD hdS hx hxd
  obtain ⟨qc, hqc', hqcc⟩ := SK.conj
  have hqc : qc ∈ Q := secondKind_commutator_zpowers_le hD hN htri h4 hno hqc'
  set e := d * a * c with he
  have hqQ : qd * qc ∈ Q := Subgroup.mul_mem _ hqd hqc
  have heq : e = (qd * qc) * a * (qd * qc)⁻¹ := by
    rw [he, ← hqdd, ← hqcc]
    refine conj_mul_conj_of_comm ha2 (SK.sq qd hqd) (SK.sq qc hqc) (SK.comm qd hqd qc hqc) ?_
    have : a * qd * a ∈ Q := by
      have := SK.normal a (Subgroup.subset_closure (by simp)) qd hqd
      rwa [hai] at this
    exact SK.comm _ this qc hqc
  have heD : e ∈ D := by rw [heq]; exact (orbit_u_spec hD hN htri h4 hno hqQ).1
  have heS : e ∈ Subgroup.zpowers a ⊔ Q := by
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQS hqQ) haS) (Subgroup.inv_mem _ (hQS hqQ))
  have hde : Commute d e := commute_of_mem_sup_D hD hN htri h4 hno hdD heD hdS heS
  have hdne : d ≠ e := by
    intro h
    apply hane
    have h1 : a * c = 1 := by
      have : d * (a * c) = d * 1 := by rw [mul_one, ← mul_assoc]; exact (h.trans he).symm
      exact mul_left_cancel this
    calc a = a * (a * c) := by rw [h1, mul_one]
      _ = c := by rw [← mul_assoc, ha2, one_mul]
  have hacde : a * c = d * e := by
    rw [he, ← mul_assoc, ← mul_assoc, hD.mul_self_eq_one hdD, one_mul]
  have hC31 : ∀ y ∈ D, Commute a y → Commute c y → Commute y d := by
    intro y hyD hay hcy
    have hy : Commute y (d * e) := by
      rw [← hacde]; exact (hay.symm.mul_right hcy.symm)
    exact ((hD.commute_mul_iff hdD heD hyD hdne hde).mp hy).1
  by_contra hdα
  set δ := (fun z => qd * z * qd⁻¹) '' hC.alpha with hδ
  have hdδ : d ∈ δ := ⟨a, ha, hqdd⟩
  have hδclass : δ ∈ blockClass hC.alpha := mem_blockClass_iff.mpr ⟨qd, rfl⟩
  have hδne : δ ≠ hC.alpha := fun h => hdα (h ▸ hdδ)
  have had : Commute a d := commute_of_mem_sup_D hD hN htri h4 hno haD hdD haS hdS
  have hδD : δ ∈ Dalpha D hC.alpha := by
    refine ⟨hδclass, subset_of_mem_blockClass hN hblock hδclass, hδne, ?_⟩
    exact commute_block_of_mem_apply hN hD hblock hδne ha hdδ had
  have hδblock : IsBlock D δ := isBlock_of_mem_blockClass hN hblock hδclass
  have hsub : perp D hC.alpha ⊆ perp D δ := by
    intro γ hγ
    rcases mem_perp_iff.mp hγ with hγD | rfl
    · by_cases hγδ : γ = δ
      · exact mem_perp_iff.mpr (Or.inr hγδ)
      · obtain ⟨y, hy⟩ := blockClass_nonempty hblock.nonempty hγD.1
        have hyD : y ∈ D := hγD.2.1 hy
        have hyd : Commute y d := hC31 y hyD (hγD.2.2.2 a ha y hy) (hγD.2.2.2 c hc y hy)
        have hγδc : γ ∈ blockClass δ := mem_blockClass_of_mem_blockClass hδclass hγD.1
        obtain ⟨k, hk⟩ := mem_blockClass_iff'.mp hγδc
        have hkne : k • δ ≠ δ := by rwa [hk] at hγδ
        refine mem_perp_iff.mpr (Or.inl ⟨hγδc, hγD.2.1, hγδ, ?_⟩)
        intro z hz w hw
        exact commute_block_of_mem hN hD hδblock hkne hdδ (show y ∈ k • δ by rw [← hk]; exact hy)
          hyd.symm z hz w (show w ∈ k • δ by rw [← hk]; exact hw)
    · refine mem_perp_iff.mpr (Or.inl ⟨mem_blockClass_of_mem_blockClass hδclass
        (mem_blockClass_self _), hblock.subset, hδne.symm, ?_⟩)
      intro z hz w hw
      exact (hδD.2.2.2 w hw z hz).symm
  have hcard : (perp D δ).ncard ≤ (perp D hC.alpha).ncard := by
    rw [hδ, ncard_perp_conj hN]
  have hperp : perp D hC.alpha = perp D δ :=
    Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hδV : δ ∈ Valpha D hC.alpha := ⟨hδclass, hperp.symm⟩
  have hVne : Valpha D hC.alpha ≠ blockClass hC.alpha := by
    intro hV
    have hβV : β ∈ Valpha D hC.alpha := by rw [hV]; exact hβ.1
    have : β ∈ perp D hC.alpha := by rw [← hβV.2]; exact mem_perp_iff.mpr (Or.inr rfl)
    exact hβ.2 this
  rw [Valpha_eq_singleton_of_isMaxBlock_of_ne hN hC.isMaxBlock_alpha hVne] at hδV
  exact hδne hδV

theorem conj_mul_mem_of_mem_Aalpha : (a * c) * b * (a * c)⁻¹ ∈ β := by
  classical
  have hD := hC.setup.oddT
  have hN := hC.setup.normal
  have hblock := hC.isBlock_alpha
  have htri : IsTriangle D a b c := isTriangle_of_mem_Aalpha hD hN hblock hβ ha hc hac hane hb
  have haD : a ∈ D := htri.1
  have hbD : b ∈ D := htri.2.2.1
  have ha2 : a * a = 1 := hD.mul_self_eq_one haD
  have hb2 : b * b = 1 := hD.mul_self_eq_one hbD
  have hodd : Odd (orderOf (a * b)) := hD.odd_of_not_commute haD hbD htri.2.2.2.2.2.1
  obtain ⟨j, hj⟩ := OddTransp.exists_zpow_conj_eq ha2 hb2 hodd (-1)
  set g := (a * b) ^ j with hg
  have hgab : g * a * g⁻¹ = b := by
    rw [hj, zpow_neg_one, mul_inv_rev, hD.inv_eq haD, hD.inv_eq hbD, mul_assoc, ha2, mul_one]
  set X := Subgroup.closure ({a, b, c} : Set G) with hX
  have haX : a ∈ X := Subgroup.subset_closure (by simp)
  have hbX : b ∈ X := Subgroup.subset_closure (by simp)
  have hcX : c ∈ X := Subgroup.subset_closure (by simp)
  have hgX : g ∈ X := Subgroup.zpow_mem _ (Subgroup.mul_mem _ haX hbX) j
  set t := a * c with ht
  have htX : t ∈ X := Subgroup.mul_mem _ haX hcX
  have ht2 : t * t = 1 := htri.uv_mul_self hD
  set y := t * b * t⁻¹ with hy
  set d' := g⁻¹ * y * g with hd'
  have hd'D : d' ∈ D := by
    have := hN g⁻¹ y (hN t b hbD); simpa [inv_inv] using this
  have hd'X : d' ∈ X :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgX)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ htX hbX) (Subgroup.inv_mem _ htX))) hgX
  have hyb : Commute y b := commute_conj_of_orderOf_mul_eq_four ht2 hb2 h4
  have hd'a : Commute d' a := by
    have hb' : g⁻¹ * b * g = a := by rw [← hgab]; group
    have h : Commute d' (g⁻¹ * b * g) := by
      show d' * (g⁻¹ * b * g) = (g⁻¹ * b * g) * d'
      rw [hd']
      calc g⁻¹ * y * g * (g⁻¹ * b * g) = g⁻¹ * (y * b) * g := by group
        _ = g⁻¹ * (b * y) * g := by rw [hyb.eq]
        _ = g⁻¹ * b * g * (g⁻¹ * y * g) := by group
    rwa [hb'] at h
  have hd'S := secondKind_mem_sup_Q hD hN htri h4 hno hd'D hd'X hd'a
  have hx' : g⁻¹ * t * g ∈ X :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgX) htX) hgX
  have hd'conj : (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ = d' := by
    rw [hd', hy, ← hgab]; group
  have hd'α : d' ∈ hC.alpha :=
    mem_alpha_of_conj_mem_secondKindS hC hβ ha hc hac hane hb h4 hno hd'D hd'S hx' hd'conj
  have hβclass : β ∈ blockClass hC.alpha := hβ.1
  have hβ'class : (fun x => g * x * g⁻¹) '' hC.alpha ∈ blockClass hC.alpha :=
    mem_blockClass_iff.mpr ⟨g, rfl⟩
  have hbβ' : b ∈ (fun x => g * x * g⁻¹) '' hC.alpha := ⟨a, ha, hgab⟩
  have hβeq : β = (fun x => g * x * g⁻¹) '' hC.alpha :=
    eq_of_mem_of_mem_blockClass hblock hβclass hβ'class ⟨b, hb, hbβ'⟩
  rw [hβeq]
  exact ⟨d', hd'α, by rw [hd']; group⟩

end LocalStep

theorem conj_image_mem_blockClass {α γ : Set G} (hγ : γ ∈ blockClass α) (x : G) :
    (fun y => x * y * x⁻¹) '' γ ∈ blockClass α := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hγ
  refine mem_blockClass_iff.mpr ⟨x * g, ?_⟩
  rw [Set.image_image]
  congr 1
  funext y
  group

theorem sixSeven (hC : HypothesisC D) (hfaith : FaithfulOnBlocks hC.alpha)
    (hsecond : ∀ u ∈ hC.alpha, ∀ v ∈ hC.alpha, ∀ w : G, IsTriangle D u w v →
      orderOf (u * v * w) = 4) :
    ∀ a ∈ hC.alpha, ∀ c ∈ hC.alpha, Commute a c → a = c := by
  classical
  intro a ha c hc hac
  by_contra hane
  have hD := hC.setup.oddT
  have hblock := hC.isBlock_alpha
  have haD : a ∈ D := hblock.subset ha
  have ha2 : a * a = 1 := hD.mul_self_eq_one haD
  have htriv : ActsTriviallyOnBlocks hC.alpha (a * c) := by
    intro γ hγ
    have hγ' : γ ∈ perp D hC.alpha ∪ Aalpha D hC.alpha := by
      rw [perp_union_Aalpha_eq_blockClass]; exact hγ
    rcases hγ' with hγp | hγA
    · rcases mem_perp_iff.mp hγp with hγD | rfl
      · ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          have h1 : Commute a z := hγD.2.2.2 a ha z hz
          have h2 : Commute c z := hγD.2.2.2 c hc z hz
          have : a * c * z * (a * c)⁻¹ = z := by
            rw [((h1.mul_left h2)).eq]; group
          change a * c * z * (a * c)⁻¹ ∈ γ
          rw [this]; exact hz
        · intro hy
          refine ⟨y, hy, ?_⟩
          have h1 : Commute a y := hγD.2.2.2 a ha y hy
          have h2 : Commute c y := hγD.2.2.2 c hc y hy
          change a * c * y * (a * c)⁻¹ = y
          rw [((h1.mul_left h2)).eq]; group
      · have hN : a * c ∈ Subgroup.normalizer hC.alpha :=
          Subgroup.mul_mem _ (mem_normalizer_of_mem_alpha hblock ha)
            (mem_normalizer_of_mem_alpha hblock hc)
        exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hN
    · obtain ⟨b, hb⟩ := blockClass_nonempty hblock.nonempty hγA.1
      have htri : IsTriangle D a b c :=
        isTriangle_of_mem_Aalpha hD hC.setup.normal hblock hγA ha hc hac hane hb
      have hy := conj_mul_mem_of_mem_Aalpha hC hγA ha hc hac hane hb
        (hsecond a ha c hc b htri)
        (fun x _ _ hx => not_isThirdKind_of_all_secondKind hsecond ha hc hx)
      exact eq_of_mem_of_mem_blockClass hblock (conj_image_mem_blockClass hγA.1 _) hγA.1
        ⟨_, ⟨b, hb, rfl⟩, hy⟩
  have h1 := hfaith _ htriv
  apply hane
  calc a = a * (a * c) := by rw [h1, mul_one]
    _ = c := by rw [← mul_assoc, ha2, one_mul]

end CFSG.OddTranspositions

