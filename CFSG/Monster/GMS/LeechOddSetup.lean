module

public import CFSG.Monster.GMS.S365Leech
public import CFSG.Monster.GMS.Leech.OddType
public import CFSG.Sporadic.Co1.Module.LeechOddFacts

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechOdd

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ w b x : G}

theorem lift_left
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (hY : IsOddPair a w b x) : IsLeechCentralLift w b :=
  S365.isLeechCentralLift_of_isConj I hG hw hY.1 hY.2.2.1 (not_mem_leechQ_of_odd hG.1.1 hY).1

theorem lift_right
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (hY : IsOddPair a w b x) : IsLeechCentralLift w x :=
  S365.isLeechCentralLift_of_isConj I hG hw hY.2.1 hY.2.2.2.1 (not_mem_leechQ_of_odd hG.1.1 hY).2.1

theorem oddPairHyp
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (hY : IsOddPair a w b x) (L : LeechSystem w) :
    CFSG.Sporadic.Co1.Module.Odd.OddPairHyp (L.φ ⟨b, hY.1⟩) (L.φ ⟨x, hY.2.1⟩) := by
  have hI : Co1InvolutionFacts := co1InvolutionFacts
  have hlb := lift_left I hG hw hY
  have hlx := lift_right I hG hw hY
  refine ⟨L.isCo1TwoA_phi hI hlb, ?_, ?_, ?_⟩
  · obtain ⟨-, -, g, hg, hgx⟩ := not_mem_leechQ_of_odd hG.1.1 hY
    refine isConj_iff.2 ⟨L.φ ⟨g, hg⟩, ?_⟩
    have h := L.phi_conj hg hY.1
    have e : (⟨g * b * g⁻¹, mul_mem (mul_mem hg hY.1) (inv_mem hg)⟩ :
        Subgroup.centralizer ({w} : Set G)) = ⟨x, hY.2.1⟩ := Subtype.ext hgx
    rw [e] at h
    exact h.symm
  · intro heq
    exact hY.2.2.2.2.1 (L.eq_of_phi_eq hlb hlx hY.2.2.2.2.2 heq).symm
  · exact (L.hasCommonLeechFour_iff hI hlb hlx).1
      (hasCommonLeechFour_of_isOddPair I.sls I.tableV I.leech I.tableIV hG hw hY)

theorem oddType
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (hY : IsOddPair a w b x) (L : LeechSystem w) {k : Fin 3} (hty : LeechOddType w b x k) :
    Co1OddType (L.φ ⟨b, hY.1⟩) (L.φ ⟨x, hY.2.1⟩) k :=
  (L.leechOddType_iff co1InvolutionFacts (lift_left I hG hw hY) (lift_right I hG hw hY)
    hY.2.2.2.2.2 k).1 hty

theorem mem_inf_iff_vec
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (hY : IsOddPair a w b x) (L : LeechSystem w) {q : G} (hq : q ∈ leechQ w) :
    q ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ↔
      L.vec q ∈ co1Fix (L.φ ⟨b, hY.1⟩) ∩ co1Fix (L.φ ⟨x, hY.2.1⟩) := by
  have hI : Co1InvolutionFacts := co1InvolutionFacts
  have hlb := lift_left I hG hw hY
  have hlx := lift_right I hG hw hY
  constructor
  · intro h
    obtain ⟨hb, hx⟩ := Subgroup.mem_inf.1 h
    exact ⟨L.vec_mem_co1Fix_of_comm hY.1 hq (Subgroup.mem_centralizer_singleton_iff.1 hb).symm,
      L.vec_mem_co1Fix_of_comm hY.2.1 hq (Subgroup.mem_centralizer_singleton_iff.1 hx).symm⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.2
      ⟨Subgroup.mem_centralizer_singleton_iff.2 (L.commute_of_vec_mem_co1Fix hI hlb hq h1).symm,
        Subgroup.mem_centralizer_singleton_iff.2 (L.commute_of_vec_mem_co1Fix hI hlx hq h2).symm⟩

theorem exists_lift
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (hY : IsOddPair a w b x) (L : LeechSystem w) {z : Co1}
    (hz : z ∈ Subgroup.centralizer ({L.φ ⟨b, hY.1⟩} : Set Co1) ⊓
      Subgroup.centralizer ({L.φ ⟨x, hY.2.1⟩} : Set Co1)) :
    ∃ (c : G) (hc : c ∈ Subgroup.centralizer ({w} : Set G)),
      c ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ∧
        L.φ ⟨c, hc⟩ = z := by
  rw [← L.image_triple co1InvolutionFacts (lift_left I hG hw hY) (lift_right I hG hw hY)
    hY.2.2.2.2.2, L.mem_image] at hz
  obtain ⟨c, hcD, hcz⟩ := hz
  have h1 := Subgroup.mem_inf.1 hcD
  have h2 := Subgroup.mem_inf.1 h1.1
  exact ⟨c, c.2, Subgroup.mem_inf.2 ⟨h2.2, h1.2⟩, hcz⟩

omit [Finite G] in
theorem phi_mem_inf (hY : IsOddPair a w b x) (L : LeechSystem w) {t : G}
    (htC : t ∈ Subgroup.centralizer ({w} : Set G))
    (ht : t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :
    L.φ ⟨t, htC⟩ ∈ Subgroup.centralizer ({L.φ ⟨b, hY.1⟩} : Set Co1) ⊓
      Subgroup.centralizer ({L.φ ⟨x, hY.2.1⟩} : Set Co1) := by
  have key : ∀ {c : G} (hc : c ∈ Subgroup.centralizer ({w} : Set G)),
      c ∈ Subgroup.centralizer ({t} : Set G) →
      L.φ ⟨t, htC⟩ ∈ Subgroup.centralizer ({L.φ ⟨c, hc⟩} : Set Co1) := by
    intro c hc hct
    rw [Subgroup.mem_centralizer_singleton_iff, ← L.phi_mul htC hc, ← L.phi_mul hc htC]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hct).symm
  have hbt : b ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).1).symm
  have hxt : x ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).2).symm
  exact Subgroup.mem_inf.2 ⟨key hY.1 hbt, key hY.2.1 hxt⟩

theorem exists_conj_mem_centralizer
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hw : IsConj z₀ w) (hY : IsOddPair a w b x) {k : Fin 3} (hk : k ≠ 0)
    (hty : LeechOddType w b x k)
    {t : G} (ht : t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
    (ht2 : orderOf t = 2) :
    ∃ h ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G),
      h * t * h⁻¹ ∈ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨S, hSw, -⟩ := s347_sylow I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hw hY hk hty
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨t, ht⟩ :
      ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)))) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) Q S
  refine ⟨(g : G), g.2, ?_⟩
  have hmem : (MulAut.conj g) (⟨t, ht⟩ :
      ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))) ∈
      (S : Subgroup ↥(Subgroup.centralizer ({b} : Set G) ⊓
        Subgroup.centralizer ({x} : Set G))) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers _))
  have := hSw _ hmem
  simpa using this

end LeechOdd

end CFSG.Monster.GMS
