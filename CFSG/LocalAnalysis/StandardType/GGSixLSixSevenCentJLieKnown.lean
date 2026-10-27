module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCentJLie
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenRootNormCtx
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagCases
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3BstarCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.LocalAnalysis.StandardType.GGSixCtxKnownSupply

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.not_le_centralizer_L (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    ¬ D ≤ Subgroup.centralizer (L : Set G) := by
  intro hD
  have hp := h.prime
  have hcyc : IsCyclic ↥D := h.sstar.2.2.2.2 D hD (IsPGroup.of_card h.card_d)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card ↥D := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using h.d_elem.2 g g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rw [hord, h.card_d] at hdvd
  have hle := Nat.le_of_dvd hp.pos hdvd
  have h2 := hp.two_le
  nlinarith

theorem GGSixCtxV2.ggKd_x_ne (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    ggKd p B x L D J x ≠ J := by
  rw [h.ggKd_eq_of_mem_zpowers (Subgroup.mem_zpowers x) h.sstar.2.2.1]
  rintro rfl
  exact h.not_le_centralizer_L h.le_centralizer_J

theorem GGSixCtxV2.ggSR_le_of_perD_ne (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {R : Subgroup G} (hRJ : R ≤ J) {x₀ : G} (hx₀ : x₀ ∈ D) (hx₀1 : x₀ ≠ 1)
    (hx₀J : ggKd p B x L D J x₀ ≠ J)
    (hN : ∀ d ∈ D, d ≠ 1 → ggKd p B x L D J d = J →
      ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤ Subgroup.normalizer (J : Set G))
    (hper : ∀ d ∈ D, d ≠ 1 → ggKd p B x L D J d ≠ J →
      ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
        (ggSR p B x L D J R ⊓ ggKd p B x L D J d) ⊔
          (ggSR p B x L D J R ⊓ Subgroup.centralizer (ggKd p B x L D J d : Set G))) :
    ggSR p B x L D J R ≤ (ggSR p B x L D J R ⊓ ggQR p B x L D J R) ⊔
      (ggSR p B x L D J R ⊓ Subgroup.centralizer (J : Set G)) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set S := ggSR p B x L D J R with hSdef
  set X := (S ⊓ ggQR p B x L D J R) ⊔ (S ⊓ Subgroup.centralizer (J : Set G)) with hX
  have hDR : D ≤ Subgroup.normalizer (R : Set G) :=
    (h.le_centralizer_J.trans (Subgroup.centralizer_le hRJ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := by
    intro d hd
    have hdR := hDR hd
    have hdP : d ∈ Subgroup.normalizer (ggPR R : Set G) := mem_normalizer_pCoreOf hdR
    have hdN₀ : d ∈ Subgroup.normalizer
        ((ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf (h.d_le_ggM hd) (Subgroup.le_normalizer hdR)
    have hdQ : d ∈ Subgroup.normalizer (ggQR p B x L D J R : Set G) :=
      ggMem_normalizer_pCoreOf_two hdN₀
    exact mem_normalizer_inf hdP (Subgroup.le_normalizer hdQ)
  have hS2' : IsPGroup 2 S := (ggPCoreOf_two_isPGroup _).to_le inf_le_left
  have hS2 : ¬ p ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := hS2'.exists_card_eq
    rw [hk]
    intro hd
    exact h.ne_two ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      (h.prime.dvd_of_dvd_pow hd))
  have hold : ∀ d ∈ D, d ≠ 1 → ggKd p B x L D J d ≠ J →
      S ⊓ Subgroup.centralizer {d} ≤ X := by
    intro d hd hd1 hK
    refine (hper d hd hd1 hK).trans (sup_le_sup (le_inf inf_le_left ?_)
      (inf_le_inf_left _ (Subgroup.centralizer_le (le_ggKd p B x L D J d))))
    intro s hs
    obtain ⟨hsS, hsK⟩ := Subgroup.mem_inf.mp hs
    have hsP : s ∈ ggPR R := (Subgroup.mem_inf.mp hsS).1
    exact ggPR_inf_le_ggQR p B x L D J R (Subgroup.mem_inf.mpr ⟨hsP,
      Subgroup.mem_inf.mpr ⟨h.ggKd_le_ggG0 hd hsK, ggPR_le_normalizer R hsP⟩⟩)
  refine ggLe_of_coprime_generation h.d_elem h.card_d hS2 hDS fun d hd hd1 => ?_
  by_cases hK : ggKd p B x L D J d = J
  swap
  · exact hold d hd hd1 hK
  set Y := S ⊓ Subgroup.centralizer {d} with hYdef
  have hDcomm : ∀ a ∈ D, a * d = d * a := fun a ha =>
    congrArg Subtype.val (h.d_elem.1.is_comm.comm (⟨a, ha⟩ : ↥D) ⟨d, hd⟩)
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    refine mem_normalizer_inf (hDS ha) (Subgroup.le_normalizer ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hDcomm a ha
  let : MulDistribMulAction ↥D ↥Y := MulDistribMulAction.compHom ↥Y (Subgroup.inclusion hDY)
  have hsmul : ∀ (b : ↥D) (y : ↥Y), ((b • y : ↥Y) : G) = (b : G) * y * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hY2 : IsPGroup 2 Y := hS2'.to_le inf_le_left
  have hsolv : Group.IsSolvable ↥Y := by
    have := hY2.isNilpotent
    infer_instance
  have hDp : IsPGroup p D := IsPGroup.of_card h.card_d
  have hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Y) :=
    IsPGroup.coprime_card_of_ne p 2 h.ne_two D Y hDp hY2
  have htop := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥D) (G := ↥Y) hsolv hcop
  have hfix : CFSG.fixedPointSubgroup ↥D ↥Y ≤ X.subgroupOf Y := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    refine hold x₀ hx₀ hx₀1 hx₀J (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp y.2).1, ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := congrArg Subtype.val (hy ⟨x₀, hx₀⟩)
    rw [hsmul] at hc
    calc (y : G) * x₀ = (x₀ * y * x₀⁻¹) * x₀ := by rw [hc]
      _ = x₀ * y := by group
  have hcom : CFSG.commutatorAction ↥D ↥Y ≤ X.subgroupOf Y := by
    rw [CFSG.commutatorAction, CFSG.commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨b, y, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, hsmul]
    refine Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have hyS : (y : G) ∈ S := (Subgroup.mem_inf.mp y.2).1
      exact S.mul_mem (S.inv_mem hyS)
        ((Subgroup.mem_normalizer_iff.mp (hDS b.2) _).mp hyS)
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hyN : (y : G) ∈ Subgroup.normalizer (J : Set G) := hN d hd hd1 hK y.2
      set j₁ := (y : G) * j * (y : G)⁻¹ with hj₁
      have hj₁J : j₁ ∈ J := (Subgroup.mem_normalizer_iff.mp hyN j).mp hj
      have hbC : (b : G) ∈ Subgroup.centralizer (J : Set G) := h.le_centralizer_J b.2
      have e1 : j * (b : G) = b * j := Subgroup.mem_centralizer_iff.mp hbC j hj
      have e2 : j₁ * (b : G) = b * j₁ := Subgroup.mem_centralizer_iff.mp hbC j₁ hj₁J
      have e1' : j * (b : G)⁻¹ = (b : G)⁻¹ * j := by
        calc j * (b : G)⁻¹ = (b : G)⁻¹ * (b * j) * (b : G)⁻¹ := by group
          _ = (b : G)⁻¹ * (j * b) * (b : G)⁻¹ := by rw [e1]
          _ = (b : G)⁻¹ * j := by group
      calc j * ((y : G)⁻¹ * ((b : G) * y * (b : G)⁻¹))
          = (y : G)⁻¹ * (j₁ * b) * y * (b : G)⁻¹ := by rw [hj₁]; group
        _ = (y : G)⁻¹ * (b * j₁) * y * (b : G)⁻¹ := by rw [e2]
        _ = (y : G)⁻¹ * b * y * (j * (b : G)⁻¹) := by rw [hj₁]; group
        _ = (y : G)⁻¹ * b * y * ((b : G)⁻¹ * j) := by rw [e1']
        _ = ((y : G)⁻¹ * ((b : G) * y * (b : G)⁻¹)) * j := by group
  intro s hs
  have hmem : (⟨s, hs⟩ : ↥Y) ∈ X.subgroupOf Y :=
    sup_le hfix hcom (htop ▸ Subgroup.mem_top _)
  rwa [Subgroup.mem_subgroupOf] at hmem

end Ctx

section CtxKnown

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}

theorem GGSixCtxV2.ggSR_le_of_items {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hZJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hZ : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    {R : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hper : ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup G, K ≤ ggG0 p B x L D J →
      IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
      Odd (Nat.card (Subgroup.center ↥K)) → GGRootInnerAt K R ∧ GGRootNoCentralAt K R) :
    ggSR p B x L D J R ≤ (ggSR p B x L D J R ⊓ ggQR p B x L D J R) ⊔
      (ggSR p B x L D J R ⊓ Subgroup.centralizer (J : Set G)) := by
  have hperd : ∀ d ∈ D, d ≠ 1 → ggKd p B x L D J d ≠ J →
      ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
        (ggSR p B x L D J R ⊓ ggKd p B x L D J d) ⊔
          (ggSR p B x L D J R ⊓ Subgroup.centralizer (ggKd p B x L D J d : Set G)) := by
    intro d hd hd1 hKd
    obtain ⟨hI, hNC⟩ := hper d hd hd1 (ggKd p B x L D J d) (hctx.ggKd_le_ggG0 hd)
      (hcomp d hd hd1) (le_ggKd p B x L D J d) hKd (hZ d hd hd1)
    have hin := hI (ggSR p B x L D J R ⊓ Subgroup.centralizer {d})
      ((ggSR_isPGroup R).to_le inf_le_left)
      (hctx.ggSRd_le_normalizer_ggKd hRJ hR1 hR2 hZJ (hcomp d hd hd1))
      (inf_le_left.trans (ggSR_le_normalizer R))
      (hctx.ggKd_inf_normalizer_le_normalizer_ggSRd hd R)
    exact hctx.perD_of_inner hRJ hR2 hd (hctx.perD_pOne_of_inner hRJ hd (hZ d hd hd1) hin) hNC
  have hN : ∀ d ∈ D, d ≠ 1 → ggKd p B x L D J d = J →
      ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤ Subgroup.normalizer (J : Set G) := by
    intro d hd hd1 hKd
    have := hctx.ggSRd_le_normalizer_ggKd hRJ hR1 hR2 hZJ (hcomp d hd hd1)
    rwa [hKd] at this
  exact hctx.ggSR_le_of_perD_ne hRJ hctx.x_mem_d hctx.sstar.2.2.1 hctx.ggKd_x_ne hN hperd

theorem GGSixCtxV2.typeA_hN {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) :
    ((t = .PSL ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ 2 ^ f + 1) →
      B ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ ∧ p ^ (n - 3) ≤ Nat.card B) := by
  intro hcase
  have hp : p.Prime := hctx.prime
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  refine ⟨eq_bot_iff.mpr ((inf_le_inf_right _ hctx.bstar.1).trans
    (bstar_inf_centralizer_ggG0_eq_bot hctx.config).le), ?_⟩
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  rw [hBcard]
  refine Nat.pow_le_pow_right hp.pos ?_
  rcases hcase with ⟨rfl, hpq⟩ | ⟨rfl, hpq⟩
  ·
    have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by
      rw [GaloisField.card 2 f (by omega)]
      exact hpq
    rcases n with _ | m
    · omega
    · by_cases hm : 1 ≤ m
      · have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 f)) := hctx.2.2.2.2.1.2
        have := RootPlaneA.sub_one_le_twoLocalRank (F := GaloisField 2 f) (ψ := ψ) hp hpK hm hker
        omega
      · omega
  ·
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    by_cases hn4 : 4 ≤ n
    · have hF : Nat.card (GaloisField 2 (2 * (f' + 1))) = (2 ^ (f' + 1)) ^ 2 :=
        CFSG.LieType.Universal.card_galoisField_two_mul 2 (f' + 1) (Nat.le_add_left 1 f')
      have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f' + 1)
          (GaloisField 2 (2 * (f' + 1))) :=
        ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
      have hnq : (n, 2 ^ (f' + 1)) ≠ (3, 2) := fun h' => by
        have : n = 3 := congrArg Prod.fst h'
        omega
      have : NeZero n := ⟨by omega⟩
      obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
      have hker₁ := SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hctx.2.2.2.2.1.2
      exact SURep.sub_three_le_twoLocalRankU h hp hctx.ne_two hpq hn4
        (SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁)
    · omega

theorem GGSixCtxV2.typeE_hE {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) :
    (t = .E6 ∨ t = .twistedE6) → ∃ A : Subgroup G, B ≤ A ∧ IsElemAbelian p A ∧
      A ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
      (∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a) ∧
      A ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ ∧
      (∀ y ∈ (A ⊔ ggG0 p B x L D J) ⊓ Subgroup.centralizer (A : Set G), orderOf y = p → y ∈ A) ∧
      p ^ LargeEvenTwoLocalRank p ↥(A ⊔ ggG0 p B x L D J) ≤ Nat.card A :=
  fun _ => ⟨Bs, ggSixCtx_bstar_rank_facts hctx⟩

theorem GGSixCtxV2.centralizer_le_ggM_of_knownAt {ψ : (ggU t n f).K →* G}
    (hK : GGSixLieKnown t) (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    (hZJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hZ : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    (hA : ¬ GGSixLSevenA3Case J) (hE : ¬ GGSixLSevenE6Case p L J t f)
    (hA6 : IsEmpty (↥J ≃* alternatingGroup (Fin 6))) (hF : ¬ GGSixLSevenFieldExtCase J t f) :
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J := by
  obtain ⟨-, -, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf0, hmodel⟩, ⟨hBsN, hVI⟩, -, -⟩ := hctx.2
  have hBBs : B ≤ Bs := hctx.bstar.1
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hctx.sstar.2.2.2.1
  have hLc : IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL
      (le_inf le_sup_left hL.1) inf_le_right
  have hmkL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hctx.stdType.1
  have hHL := ggSixCtx_normalizer_and_innerDiag_on_L hctx
  obtain ⟨R, J₀, hRJ, hR1, hR2, hJ₀J, hgen, hper, h3, h4⟩ :=
    hK G n f ψ p (ggG0 p B x L D J) B D J L x hrange hker hmodel hodd hctx.prime hctx.ne_two
      (hBBs.trans hBsN) (fun b hb => hVI b (hBBs hb)) hctx.sstar.1.1 hctx.pow_four_le_card_b
      hctx.stdSub.1.1 hctx.card_d hBJ hctx.stdSub.1.2.2.2.2.2.2.symm hctx.j_isComponentOf_inf
      hZJ hctx.x_mem_d hctx.sstar.2.2.1 le_sup_left hLc (hctx.j_le_inf.trans inf_le_left)
      hctx.not_le_centralizer_L hmkL hHL.1 hHL.2 hA hE hA6 hF hctx.typeA_hN hctx.typeE_hE
  have h67i := hctx.ggSR_le_of_items hZJ hZ hcomp hRJ hR1 hR2 hper
  exact hctx.centralizer_le_ggM_of_data hodd hRJ hR1 hR2 hJ₀J hgen h67i
    (fun hSM hSQ => hctx.sQC_of_inner hRJ hodd
      (h3 _ (ggSR_isPGroup R) hSM (ggSR_le_normalizer R) hSQ))
    (ggSixLSevenItemFour_of_alt p B x L D J R h4)

end CtxKnown

end CFSG.StandardType
