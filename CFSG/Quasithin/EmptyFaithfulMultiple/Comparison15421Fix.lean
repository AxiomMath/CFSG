module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421B56
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420B56

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open (pCoreOf quasithinGenFitting quasithinG2 IsElemAbelian)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace FFL

variable {V : Type} [CommGroup V] [Finite V]

theorem fix_or_lin2_of_b42_all
    (hD : FixG2Derived) (hE : FixA7Four)
    (hF : FixTripleA6) (hV : ∀ v : V, v * v = 1) {L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) (hB : B42ModulePair L (commV L) (fixV L ⊓ commV L)) :
    (∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v) ∨
      ∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n := by
  rcases hB with ⟨n, hn⟩ | ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ |
    ⟨m, K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨K, _, _, Γ₀, hcard, hdet, hhat, hcen, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact Or.inr ⟨n, hn⟩
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_nat hV hS le_rfl hπ)
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_sp4 hV hS hπ)
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_g2 hV hS hπ)
  ·
    left
    have := charP_two_of_card hK
    have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
      Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    obtain ⟨T₀, hT₀, γ, hγ3, hγ1, hfix⟩ := hD K (by simpa using hK)
    have hinj := G64.RealizesVia.injective_of_faithful' (zornQ_faithful hle) hπ
    exact exists_fix_of_realizesVia hV hS hπ hT₀ hγ3
      (fun h => hγ1 (hinj (h.trans (map_one π).symm))) hfix
  ·
    left
    obtain ⟨T₀, hT₀, γ, hγ3, hD'⟩ := exists_fixesFixed_altDn (m := 5) le_rfl (by norm_num)
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful le_rfl) hπ
    have hγ3' : γ ^ 3 = 1 := by rw [← hγ3, pow_orderOf_eq_one]
    refine exists_fix_of_realizesVia hV hS hπ hT₀ hγ3' ?_ hD'
    intro h
    have h1 : γ = 1 := hinj (h.trans (map_one π).symm)
    rw [h1, orderOf_one] at hγ3
    omega
  ·
    left
    obtain ⟨T₀, hT₀, γ, hγ3, hD'⟩ := exists_fixesFixed_altDn (m := 6) (by norm_num)
      (by norm_num)
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
    have hγ3' : γ ^ 3 = 1 := by rw [← hγ3, pow_orderOf_eq_one]
    refine exists_fix_of_realizesVia hV hS hπ hT₀ hγ3' ?_ hD'
    intro h
    have h1 : γ = 1 := hinj (h.trans (map_one π).symm)
    rw [h1, orderOf_one] at hγ3
    omega
  ·
    left
    obtain ⟨T₀, hT₀, γ, hγ3, hD'⟩ := exists_fixesFixed_altDn (m := 7) (by norm_num)
      (by norm_num)
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
    have hγ3' : γ ^ 3 = 1 := by rw [← hγ3, pow_orderOf_eq_one]
    refine exists_fix_of_realizesVia hV hS hπ hT₀ hγ3' ?_ hD'
    intro h
    have h1 : γ = 1 := hinj (h.trans (map_one π).symm)
    rw [h1, orderOf_one] at hγ3
    omega
  ·
    left
    obtain ⟨T₀, hT₀, γ, hγ3, hγ1, hfix⟩ := hE α
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.a7Four_faithful α) hπ
    exact exists_fix_of_realizesVia hV hS hπ hT₀ hγ3
      (fun h => hγ1 (hinj (h.trans (map_one π).symm))) hfix
  ·
    left
    obtain ⟨T₀, hT₀, γ, hγ3, hγ1, hfix⟩ := hF K hcard Γ₀ hdet hhat hcen
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    exact exists_fix_of_realizesVia hV hS hπ hT₀ hγ3
      (fun h => hγ1 (hinj (h.trans (map_one π).symm))) hfix
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_nat hV hS (by norm_num) hπ)
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_nat hV hS (by norm_num) hπ)
  · exact Or.inl (fix_of_extSq4 hV hS hπ)
  · exact Or.inl (fix_of_extSq5 hV hS hπ)

theorem fix_or_lin2_of_b51_all
    (hD : FixG2Derived) (hE : FixA7Four)
    (hF : FixTripleA6) (hV : ∀ v : V, v * v = 1) {G L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) (h : B51Part1 G L) :
    (∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v) ∨
      ∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ |
    ⟨n, -, hn, π, U₁, U₂, ⟨hU, hU0⟩, h₁, h₂⟩ | ⟨-, n, hn, k, hk1, -, I, π, -, hind, hsup, hreal⟩
  · exact fix_or_lin2_of_b42_all hD hE hF hV hS hB
  ·
    left
    have := charP_two_of_card hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) (hreal 0)
    refine fix_of_sum hS le_rfl hinj fun v hv hT => ?_
    rw [← hsup] at hv
    refine fix_of_iSup I (fun i => disjoint_iff.mp (hind i)) (fun t ht i w hw => ?_)
      (fun i => fix_nat_summand (hreal i) _ (by simp) (by simp)) v hv hT
    obtain ⟨τ, -, rfl⟩ := ht
    exact (hreal i).2.2.2.1 (π τ) w hw
  ·
    left
    have hn4 : 4 ≤ n := by omega
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) h₁
    refine fix_of_sum hS (by omega) hinj fun v hv hT => ?_
    rw [← hU] at hv
    refine fix_of_sup hU0 (fun t ht w hw => ?_) (fun t ht w hw => ?_)
      (fix_nat_summand h₁ _ (by simp) (by simp))
      (fix_dualNat_summand h₂ _ (by simp; omega) (by simp; omega)) v hv hT
    · obtain ⟨τ, -, rfl⟩ := ht
      exact h₁.2.2.2.1 (π τ) w hw
    · obtain ⟨τ, -, rfl⟩ := ht
      exact h₂.2.2.2.1 (π τ) w hw
  ·
    left
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _)
      (hreal ⟨0, hk1⟩)
    refine fix_of_sum hS (by omega) hinj fun v hv hT => ?_
    rw [← hsup, bot_sup_eq] at hv
    refine fix_of_iSup I (fun i => by simpa using hind i) (fun t ht i w hw => ?_)
      (fun i => fix_nat_summand (hreal i) _ (by simp) (by simp)) v hv hT
    obtain ⟨τ, -, rfl⟩ := ht
    exact (hreal i).2.2.2.1 (π τ) w hw

end FFL

namespace C421

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_map_subtype {I : Subgroup G} {Q : Subgroup ↥I} (hQ : Q.Normal) :
    I ≤ Subgroup.normalizer ((Q.map I.subtype : Subgroup G) : Set G) := by
  intro i hi
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨i, hi⟩ * q * ⟨i, hi⟩⁻¹, hQ.conj_mem q hq _, rfl⟩
  · rintro ⟨q, hq, hqe⟩
    have hhI : h ∈ I := by
      have : h = i⁻¹ * (i * h * i⁻¹) * i := by group
      rw [this, ← hqe]
      exact I.mul_mem (I.mul_mem (I.inv_mem hi) q.2) hi
    refine ⟨⟨h, hhI⟩, ?_, rfl⟩
    have : (⟨h, hhI⟩ : ↥I) = ⟨i, hi⟩⁻¹ * q * (⟨i, hi⟩⁻¹)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      have hq' : (q : G) = i * h * i⁻¹ := hqe
      rw [hq']
      group
    rw [this]
    exact hQ.conj_mem q hq _

section Main

variable {I V G₁ G₂ : Subgroup G} (hV : IsElemAbelian 2 V)
  (hIV : I ≤ Subgroup.normalizer (V : Set G))
  (hC : I ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 I)
  (hI : CFSG.SectionRank.IsSQTKCat ↥I) (htr : F6.IsGoldschmidtTripleIn I G₁ G₂)
  (ham : IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
    ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))))
  (hF618 : F6.TheoremF618Cat) (hA : F618ComponentInspection)

include hIV hC hI ham hF618 hA htr in
theorem exists_fix_of_isComponent
    (h56 : AsB56) (hD : FixG2Derived) (hE : FixA7Four)
    (hF : FixTripleA6) (hFF : IsFFModule (autI hV I)) {K : Subgroup ↥(autI hV I)}
    (hK : CFSG.IsComponent K) :
    ∃ F : Subgroup (MulAut (IntMod V hV)), F ≤ autI hV I ∧
      autI hV I ≤ Subgroup.normalizer (F : Set (MulAut (IntMod V hV))) ∧
      ∀ S : Subgroup (MulAut (IntMod V hV)), IsSylowTwoOf S F →
        ∃ g ∈ F, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV F, g v = v := by
  obtain ⟨hqF, h1⟩ := b51Part1_of_isComponent hV hIV hC hI htr ham hF618 hA h56 hFF hK
  have hFX : quasithinGenFitting (ffJ (autI hV I)) ≤ autI hV I :=
    (quasithinGenFitting_le _).trans (FFL.ffJ_le _)
  have hXF : autI hV I ≤ Subgroup.normalizer
      (quasithinGenFitting (ffJ (autI hV I)) : Set (MulAut (IntMod V hV))) :=
    (FFL.le_normalizer_ffJ (autI hV I)).trans (normalizer_le_normalizer_quasithinGenFitting _)
  refine ⟨_, hFX, hXF, fun S hS => ?_⟩
  have hV2 : ∀ v : IntMod V hV, v * v = 1 := fun v => by
    rw [← sq]
    exact IntMod.sq_eq_one v
  rcases FFL.fix_or_lin2_of_b51_all hD hE hF hV2 hS h1 with hfix | ⟨n, K', _, _, hK', π, hπ⟩
  · exact hfix
  · exfalso
    have := FFL.charP_two_of_card hK'
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hFn : ((quasithinGenFitting (ffJ (autI hV I))).subgroupOf (autI hV I)).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hXF g.2) n).mp hn
    have hFq : CFSG.IsQuasisimple ↥((quasithinGenFitting (ffJ (autI hV I))).subgroupOf
        (autI hV I)) :=
      FFL.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFX).symm hqF
    exact false_of_mulEquiv_sl2 hV hIV hC hI htr ham hF618 hA hFn hFq
      ((Subgroup.subgroupOfEquivOfLe hFX).trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm)

include hIV hC hI ham hF618 hA htr in
theorem not_isPGroup_of_isComponent
    (h56 : AsB56) (hD : FixG2Derived) (hE : FixA7Four)
    (hF : FixTripleA6) (hFF : IsFFModule (autI hV I)) {K : Subgroup ↥(autI hV I)}
    (hK : CFSG.IsComponent K) {Z : Subgroup G} (hZV : Z ≤ V)
    (hZT : ∀ z ∈ Z, ∀ t ∈ G₁ ⊓ G₂, t * z = z * t) :
    ¬ IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (Z : Set G)) := by
  obtain ⟨F, hFX, hXF, hfix⟩ :=
    exists_fix_of_isComponent hV hIV hC hI htr ham hF618 hA h56 hD hE hF hFF hK
  have hFXn : (F.subgroupOf (autI hV I)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXF g.2) n).mp hn
  set Q : Subgroup ↥I := (F.subgroupOf (autI hV I)).comap (conjI hV hIV) with hQdef
  have hQn : Q.Normal := hFXn.comap _
  set Fh : Subgroup G := Q.map I.subtype with hFhdef
  have hFhI : Fh ≤ I := Subgroup.map_subtype_le _
  have hFhV : Fh ≤ Subgroup.normalizer (V : Set G) := hFhI.trans hIV
  have hautF : autI hV Fh = F := by
    ext φ
    rw [mem_autI]
    constructor
    · rintro ⟨g, ⟨i, hi, hig⟩, rfl⟩
      have h1 : convI hV g = ((conjI hV hIV i : ↥(autI hV I)) : MulAut (IntMod V hV)) := by
        rw [conjI_apply]
        congr 1
        exact Subtype.ext hig.symm
      rw [h1]
      exact hi
    · intro hφ
      obtain ⟨i, hi⟩ := conjI_surjective hV hIV ⟨φ, hFX hφ⟩
      refine ⟨⟨i, hIV i.2⟩, ⟨i, ?_, rfl⟩, congrArg Subtype.val hi⟩
      change conjI hV hIV i ∈ F.subgroupOf (autI hV I)
      rw [hi]
      exact hφ
  have hFhn : I ≤ Subgroup.normalizer (Fh : Set G) := le_normalizer_map_subtype hQn
  have hT₀ : IsSylowTwoOf (G₁ ⊓ G₂) I := htr.2.2.2
  have hTK : IsSylowTwoOf (G₁ ⊓ G₂ ⊓ Fh) Fh := A4.isSylowTwoOf_inf_normal hT₀ hFhI hFhn
  have hS := L15420.isSylowTwoOf_autOn hTK hFhV
  change IsSylowTwoOf (autI hV (G₁ ⊓ G₂ ⊓ Fh)) (autI hV Fh) at hS
  rw [hautF] at hS
  obtain ⟨g, hgF, hg3, hgfix⟩ := hfix _ hS
  obtain ⟨k₀, hk₀, hk₀2, hfix'⟩ := L15420.exists_fix_of_autI (TK := G₁ ⊓ G₂ ⊓ Fh) hV hFhV
    ⟨g, by rw [hautF]; exact hgF, hg3, by rw [hautF]; exact hgfix⟩
  obtain ⟨k, hk, hk2, hkZ⟩ :=
    exists_centralizer_of_fix hV hFhV hTK.1 hTK.2.2 hk₀ hk₀2 hfix'
  intro h2
  have hkC : k ∈ I ⊓ Subgroup.centralizer (Z : Set G) :=
    ⟨hFhI hk, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      hkZ z (hZV hz) fun t ht => hZT z hz t ht.1⟩
  obtain ⟨n, hn⟩ := h2 ⟨k, hkC⟩
  exact hk2 n (by
    have := congrArg Subtype.val hn
    simpa using this)

end Main

end C421

end CFSG.Quasithin.EmptyFaithfulMultiple
