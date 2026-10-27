module

public import CFSG.LocalAnalysis.StandardType.GGFrameReflTransport
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly TableB CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem frameEL_card_ker_ggGamma {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥((ggGamma L hN).ker) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
  have hker : (ggGamma L hN).ker = (Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hEq : (Subgroup.centralizer (L : Set G)).subgroupOf Bs =
      (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  rw [hker, hEq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

private theorem frameEL_card_range_ggGamma {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥Bs = Nat.card ↥((ggGamma L hN).range) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
  have h := card_range_mul_card_ker (ggGamma L hN)
  rw [frameEL_card_ker_ggGamma hN] at h
  exact h.symm

theorem largeEvenMarking_torusTBGroup_of_qTwo {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (r : ℕ)
    (hcard : 3 ^ r ≤ Nat.card (ggGamma L hN).range)
    (hcard3 : 3 ^ 3 ≤ Nat.card (ggGamma L hN).range) :
    LargeEvenMarking L (fun lab R _ I _ θ => GGLabQTwo 3 lab ∧
      GGTorusTBGroup 3 r R I L (ggQuotHom θ) (ggGamma L hN).range) := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hR.1.2.1.2.2.2
  have hBp : ∀ b : Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hA : IsElemAbelian 3 (ggGamma L hN).range := isElemAbelian_range hBc hBp _
  refine largeEvenMarking_mono ?_ hq
  rintro lab R _ I F θ ⟨hlab, -, h3⟩
  refine ⟨hlab, ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hq.1, hA, ?_, hcard, hcard3,
    ggTorusSelfCent_ggGamma hN hSC⟩
  rintro _ ⟨b, rfl⟩
  exact ⟨ggBeta L θ hN b, ggLAut_mem_of_induces L θ hN h3 b.2,
    fun l => ggBeta_ggQuotHom L hN θ b l⟩

omit [Finite G] in
theorem ggAutomizer_apply_eq_of_mem_centralizer {Bs L : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer L Bs) {b : ↥Bs}
    (hb : (b : G) ∈ Subgroup.centralizer (L : Set G)) : φ b = b := by
  obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  apply Subtype.ext
  rw [hg]
  have hcomm : g * (b : G) = (b : G) * g :=
    Subgroup.mem_centralizer_iff.mp hb g hgL
  calc g * (b : G) * g⁻¹ = (b : G) * g * g⁻¹ := by rw [hcomm]
    _ = (b : G) := by group

omit [Finite G] in
private theorem frameEL_apply_eq_of_rangeRestrict_eq {Bs L : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (φ : ↥(ggAutomizer L Bs)) (hφ : (φ : MulAut ↥Bs) ^ 2 = 1) {b : ↥Bs}
    (hb : (ggGamma L hN) ((φ : MulAut ↥Bs) b) = (ggGamma L hN) b) :
    (φ : MulAut ↥Bs) b = b := by
  let k : ↥Bs := b⁻¹ * (φ : MulAut ↥Bs) b
  have hk_mem : k ∈ (ggGamma L hN).ker := by
    rw [MonoidHom.mem_ker]
    change (ggGamma L hN) k = 1
    dsimp [k]
    rw [map_mul, map_inv, hb, inv_mul_cancel]
  have hk_cent : (k : G) ∈ Subgroup.centralizer (L : Set G) :=
    (ggGamma_eq_one_iff L hN k).mp (MonoidHom.mem_ker.mp hk_mem)
  have hk_fix : (φ : MulAut ↥Bs) k = k :=
    ggAutomizer_apply_eq_of_mem_centralizer φ.2 hk_cent
  have hk3 : k ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 (k : G) k.2
  have hφ2 : (φ : MulAut ↥Bs) ((φ : MulAut ↥Bs) b) = b := by
    have h := congrArg (fun f : MulAut ↥Bs => f b) hφ
    simpa [pow_two] using h
  have hk_inv : (φ : MulAut ↥Bs) k = k⁻¹ := by
    dsimp [k]
    rw [map_mul, map_inv, hφ2]
    group
  have hk_eq_inv : k = k⁻¹ := by
    calc k = (φ : MulAut ↥Bs) k := hk_fix.symm
      _ = k⁻¹ := hk_inv
  have hk2 : k ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 2 [hk_eq_inv]
    exact mul_inv_cancel k
  have hk1 : k = 1 := by
    have h : k ^ 3 = k := by
      rw [pow_succ, hk2]
      simp
    rw [← h]
    exact hk3
  have hb1 : b⁻¹ * (φ : MulAut ↥Bs) b = 1 := by simpa [k] using hk1
  exact (inv_mul_eq_one.mp hb1).symm

theorem card_fix_eq_card_fix_ggAutomizerGammaHom_mul {Bs L : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (φ : ↥(ggAutomizer L Bs)) (hφ : (φ : MulAut ↥Bs) ^ 2 = 1) :
    Nat.card {b : ↥Bs // (φ : MulAut ↥Bs) b = b} =
      Nat.card {a : ↥(ggGamma L hN).range //
          (ggAutomizerGammaHom hN φ : MulAut ↥(ggGamma L hN).range) a = a} *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  let F : Subgroup ↥Bs := ggFix (φ : MulAut ↥Bs)
  let K : Subgroup ↥Bs := (ggGamma L hN).ker
  let FixA : Subgroup ↥((ggGamma L hN).range) :=
    ggFix (ggAutomizerGammaHom hN φ : MulAut ↥(ggGamma L hN).range)
  let f : F →* ↥((ggGamma L hN).range) :=
    (ggGamma L hN).rangeRestrict.comp F.subtype
  have hKF : K ≤ F := by
    intro k hk
    rw [mem_ggFix]
    exact ggAutomizer_apply_eq_of_mem_centralizer φ.2
      ((ggGamma_eq_one_iff L hN k).mp (MonoidHom.mem_ker.mp hk))
  have hfker : f.ker = K.subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    show f x = 1 ↔ (ggGamma L hN) (x : F) = 1
    rw [Subtype.ext_iff]
    simp [f]
  have hcardF : Nat.card ↥F = Nat.card ↥f.range * Nat.card ↥f.ker :=
    (card_range_mul_card_ker f).symm
  have hrange : f.range = FixA := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [mem_ggFix]
      have hy : (φ : MulAut ↥Bs) (y : F) = (y : F) := mem_ggFix.mp y.2
      have hov := ggAutomizerGammaHom_overGamma hN φ (y : F)
      rw [hy] at hov
      exact hov.symm
    · intro hx
      rw [mem_ggFix] at hx
      obtain ⟨b, hb⟩ := (ggGamma L hN).rangeRestrict_surjective x
      have hbF : (φ : MulAut ↥Bs) b = b := by
        apply frameEL_apply_eq_of_rangeRestrict_eq hBs hN φ hφ
        have hov := ggAutomizerGammaHom_overGamma hN φ b
        rw [hb] at hov
        exact congrArg Subtype.val (hov.trans (hx.trans hb.symm))
      refine ⟨⟨b, ?_⟩, hb⟩
      rw [mem_ggFix]
      exact hbF
  have hkerCard : Nat.card ↥f.ker = Nat.card ↥K := by
    rw [hfker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKF).toEquiv
  change Nat.card ↥F =
    Nat.card ↥FixA * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G))
  rw [hcardF, hrange, hkerCard, frameEL_card_ker_ggGamma hN]

theorem ggIsReflection_iff_ggAutomizerGammaHom {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (φ : ↥(ggAutomizer L Bs)) :
    GGIsReflection 3 (φ : MulAut ↥Bs) ↔
      GGIsReflection 3 ((ggAutomizerGammaHom hN φ : MulAut ↥(ggGamma L hN).range)) := by
  classical
  obtain ⟨-, hBs, -, -, -⟩ := hR.1.tableB_facts
  have hNoTr : GGNoTransvection 3 Bs := hR.2.2.2.1
  have hKcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 3 := by
    simpa using hR.1.card_bstar_inf_centralizer_L
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
    have h := Subgroup.card_le_of_le hle
    rwa [hKcard] at h
  have hinj : Function.Injective (ggAutomizerGammaHom hN) :=
    ggAutomizerGammaHom_injective Nat.prime_three hBs hNoTr hN hZ
  have hBcard : Nat.card ↥Bs =
      Nat.card ↥((ggGamma L hN).range) * 3 := by
    rw [frameEL_card_range_ggGamma hN, hKcard]
  have hFixCard : ∀ ψ : ↥(ggAutomizer L Bs), (ψ : MulAut ↥Bs) ^ 2 = 1 →
      Nat.card {b : ↥Bs // (ψ : MulAut ↥Bs) b = b} =
        Nat.card {a : ↥(ggGamma L hN).range //
          (ggAutomizerGammaHom hN ψ : MulAut ↥(ggGamma L hN).range) a = a} * 3 := by
    intro ψ hψ
    rw [card_fix_eq_card_fix_ggAutomizerGammaHom_mul hBs hN ψ hψ, hKcard]
  constructor
  · rintro ⟨hφ2, hφfix⟩
    constructor
    · have hφ2' : φ ^ 2 = 1 := Subtype.ext hφ2
      have h1 : ggAutomizerGammaHom hN (φ ^ 2) = 1 := by rw [hφ2']; simp
      have h2 := congrArg
        (fun x : ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (ggGamma L hN).range) => (x : MulAut ↥(ggGamma L hN).range)) h1
      simpa [map_pow] using h2
    · have h := hφfix
      rw [hFixCard φ hφ2, hBcard] at h
      exact Nat.mul_right_cancel (by norm_num : 0 < 3) h
  · rintro ⟨ha2, hafix⟩
    have hφ2_sub : φ ^ 2 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact Subtype.ext ha2
    have hφ2 : (φ : MulAut ↥Bs) ^ 2 = 1 := by
      simpa using congrArg (fun x : ↥(ggAutomizer L Bs) => (x : MulAut ↥Bs)) hφ2_sub
    refine ⟨hφ2, ?_⟩
    have h := hFixCard φ hφ2
    rw [h, hafix, hBcard]

theorem frameNumIs_frameConn_of_ggAutomizerGammaHom {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hbij : Function.Bijective (ggAutomizerGammaHom hN)) (N : ℕ) (d : Option ℕ)
    (h : FrameNumIs (ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hN).range) N d ∧
      FrameConn (ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hN).range)) :
    FrameNumIs (ggAutomizer L Bs) N d ∧ FrameConn (ggAutomizer L Bs) := by
  let e : ↥(ggAutomizer L Bs) ≃*
      ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hN).range) :=
    MulEquiv.ofBijective (ggAutomizerGammaHom hN) hbij
  have he : ∀ φ : ↥(ggAutomizer L Bs),
      GGIsReflection 3 (φ : MulAut ↥Bs) ↔
        GGIsReflection 3 (e φ : MulAut ↥(ggGamma L hN).range) := by
    intro φ
    simpa [e] using ggIsReflection_iff_ggAutomizerGammaHom hR hN φ
  exact ⟨frameNumIs_of_mulEquiv e he h.1, frameConn_of_mulEquiv e he h.2⟩

end CFSG.StandardType.FrameRoute

end
