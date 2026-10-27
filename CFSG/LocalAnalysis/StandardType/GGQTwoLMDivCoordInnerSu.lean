module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTlift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTid
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTker
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTcl
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerW
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerWf
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerQuot
import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

private lemma qTwoLMDivCoordInner_su_oneVec_ne_one {m : ℕ} (hm : 0 < m) (h3 : 3 ∣ m) :
    qTwoOneVec m h3 ≠ 1 := by
  intro h
  have h0 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := by
    have h1 := congrFun (congrArg Subtype.val h) ⟨0, hm⟩
    simpa [qTwoOneVec] using h1
  exact one_ne_zero (ofAdd_eq_one.mp h0)

theorem qTwoLMDivCoordInner_su_assembly {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 6 ≤ m)
    (h3 : 3 ∣ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hk : QTwoDivKind.facts .suInner m Bs L) :
    ∃ C : QTwoDivCoords m (QTwoHm m h3) ↥(sumZero m 3) Bs L x hN,
      IsHmModel m h3 (QTwoHm m h3) C.permV ∧ IsAugModel m ↥(sumZero m 3) C.permVT := by
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨δ, hδ⟩ := qTwoLMDivCoordInner_torus hU.card h3
  obtain ⟨τ, hτ⟩ := qTwoLMDivCoordInner_tlift hBs hN hU hδ
  obtain ⟨hrange, hsplit⟩ := qTwoLMDivCoordInner_tident hG hBs hN hm h3 hU hδ hτ h2
  obtain ⟨hinj, -, hcent⟩ := qTwoLMDivCoordInner_tker hG hN hm h3 hU hδ hτ
  have hcl := qTwoLMDivCoordInner_tclauses hG hBs hN hm h3 hU hδ hτ hrange hsplit
  have hker' : ∀ f, ((τ f : ↥L) : G) ∈ Subgroup.zpowers x ↔
      f ∈ Subgroup.zpowers (qTwoOneVec m h3) := by
    let τG : ↥(sumZero m 3) →* G := (Subgroup.subtype L).comp τ
    have hτG_apply : ∀ f, τG f = ((τ f : ↥L) : G) := fun f => rfl
    have hS : CFSG.Assembly.LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
    obtain ⟨⟨-, -, -⟩, hxB, hx1, -, -⟩ := hS
    have hxBs : x ∈ Bs := hBs.1 hxB
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hxord : orderOf x = 3 := orderOf_eq_prime (hBs.2.1.2 x hxBs) hx1
    have hv1ne : qTwoOneVec m h3 ≠ 1 := qTwoLMDivCoordInner_su_oneVec_ne_one (by omega) h3
    have hτ1mem : ((τ (qTwoOneVec m h3) : ↥L) : G) ∈ Subgroup.zpowers x := by
      have hmem : ((τ (qTwoOneVec m h3) : ↥L) : G) ∈
          Bs ⊓ Subgroup.centralizer (L : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨hτ.mem _, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        simpa only [Subgroup.coe_mul] using
          congrArg (fun z : ↥L => (z : G)) (hcent ⟨l, hl⟩).symm
      rwa [qTwoLMPrimeC_ker hG hBs] at hmem
    have hτ1ne : τ (qTwoOneVec m h3) ≠ 1 := by
      intro h
      exact hv1ne (hinj h1 (h.trans (map_one τ).symm))
    have hzpx : Subgroup.zpowers x =
        Subgroup.zpowers ((τ (qTwoOneVec m h3) : ↥L) : G) := by
      have hle : Subgroup.zpowers ((τ (qTwoOneVec m h3) : ↥L) : G) ≤
          Subgroup.zpowers x := Subgroup.zpowers_le.mpr hτ1mem
      have hcard : Nat.card (Subgroup.zpowers x) ≤
          Nat.card (Subgroup.zpowers ((τ (qTwoOneVec m h3) : ↥L) : G)) := by
        have hord : orderOf ((τ (qTwoOneVec m h3) : ↥L) : G) = 3 :=
          (Subgroup.orderOf_mk ((τ (qTwoOneVec m h3) : ↥L) : G)
            (τ (qTwoOneVec m h3)).2).symm.trans
            (orderOf_eq_prime (hτ.cube (qTwoOneVec m h3)) hτ1ne)
        rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hord]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
    intro f
    constructor
    · intro hf
      have hf2 : τG f ∈ Subgroup.zpowers ((τ (qTwoOneVec m h3) : ↥L) : G) := by
        rw [← hzpx]
        simpa [hτG_apply] using hf
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hf2
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      apply hinj h1
      apply Subtype.ext
      rw [map_zpow, Subgroup.coe_zpow]
      simpa only [hτG_apply] using hk
    · intro hf
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hf
      have hmem : τG f ∈ Subgroup.zpowers (τG (qTwoOneVec m h3)) := by
        rw [← hk, map_zpow]
        exact Subgroup.zpow_mem_zpowers (τG (qTwoOneVec m h3)) k
      have hgoal : τG f ∈ Subgroup.zpowers x := by
        rw [hzpx]
        simpa [hτG_apply] using hmem
      simpa [hτG_apply] using hgoal
  obtain ⟨θ, hθ⟩ := qTwoLMDivCoordInner_wtheta hG hBs hN h3 τ hτ.mem hrange hsplit hker'
  obtain ⟨ρ, hρ, hρe⟩ := qTwoLMDivCoordInner_permHm m h3
  have hwn : ∀ n : ↥L, MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    fun n hn => qTwoLMDivCoordInner_wnorm hG hBs hN (by omega) hU hsplit n hn
  have hwl := qTwoLMDivCoordInner_wfields hN h3 τ hτ.mem θ hθ ρ hρe hwn hcl.1 hcl.2
  let φT : ↥(sumZero m 3) →* ↥(Bs ⊓ L) :=
    { toFun := fun f => ⟨(τ f : G), Subgroup.mem_inf.mpr ⟨hτ.mem f, (τ f).2⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun f g => by apply Subtype.ext; simp }
  have hφT_apply : ∀ f, ((φT f : ↥(Bs ⊓ L)) : G) = (τ f : G) := fun f => rfl
  have hinjT : Function.Injective φT := by
    intro f g hfg
    apply hinj h1
    apply Subtype.ext
    simpa [hφT_apply] using congrArg (fun y : ↥(Bs ⊓ L) => (y : G)) hfg
  have hsurjT : Function.Surjective φT := by
    intro y
    obtain ⟨f, hf⟩ := hrange ⟨(y : G), y.2.2⟩ y.2.1
    refine ⟨f, Subtype.ext ?_⟩
    rw [hφT_apply]
    exact congrArg (fun z : ↥L => (z : G)) hf
  let thetaT : ↥(sumZero m 3) ≃* ↥(Bs ⊓ L) :=
    MulEquiv.ofBijective φT ⟨hinjT, hsurjT⟩
  have hthetaT_apply : ∀ f, ((thetaT f : ↥(Bs ⊓ L)) : G) = (τ f : G) := by
    intro f
    show ((φT f : ↥(Bs ⊓ L)) : G) = (τ f : G)
    rfl
  refine ⟨⟨ρ, permAutVHom m 3, θ, hwl.1, hwl.2, thetaT, ?_, ?_⟩, hρ, ?_⟩
  · intro n hnBs
    obtain ⟨π', hπ'⟩ := hcl.1 n hnBs
    exact ⟨π', fun v => by
      simp only [hthetaT_apply, permAutVHom_apply]
      exact hπ' v⟩
  · intro σ
    obtain ⟨n, hnBs, hnτ⟩ := hcl.2 σ
    exact ⟨n, hnBs, fun v => by
      simp only [hthetaT_apply, permAutVHom_apply]
      exact hnτ v⟩
  · refine ⟨MulEquiv.refl _, fun σ v => ?_⟩
    simp [permAutVHom_apply]

end CFSG.StandardType.QTwo

end
