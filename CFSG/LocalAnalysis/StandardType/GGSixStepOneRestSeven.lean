module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompCentJ
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallBasic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G]

theorem ggLe_of_coprime_generation {p : ℕ} [Fact p.Prime] {D S X : Subgroup G}
    (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) (hS : ¬ p ∣ Nat.card S)
    (hDS : D ≤ Subgroup.normalizer (S : Set G))
    (hX : ∀ d ∈ D, d ≠ 1 → S ⊓ Subgroup.centralizer {d} ≤ X) : S ≤ X := by
  have : CFSG.IsElementaryAbelian p ↥D := ggIsElementaryAbelian hD
  let : MulDistribMulAction ↥D ↥S := MulDistribMulAction.compHom ↥S (Subgroup.inclusion hDS)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥D) (H := ↥S)
    (le_of_eq hDc.symm) hS
  have hC : (⊤ : Subgroup ↥S) ≤ X.subgroupOf S := by
    rw [← hgen]
    refine iSup₂_le fun a ha => ?_
    intro y hy
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a y).1 hy
    have hc : (a : G) * y * (a : G)⁻¹ = y := congrArg Subtype.val hfix
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hyC : (y : G) ∈ S ⊓ Subgroup.centralizer {(a : G)} := by
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * a = (a : G) * y * (a : G)⁻¹ * a := by rw [hc]
        _ = a * y := by rw [inv_mul_cancel_right]
    rw [Subgroup.mem_subgroupOf]
    exact hX a a.2 ha1 hyC
  intro s hs
  have := hC (Subgroup.mem_top (⟨s, hs⟩ : ↥S))
  rwa [Subgroup.mem_subgroupOf] at this

omit [Finite G] in
theorem ggMem_normalizer_pCoreOf_two {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H hg

omit [Finite G] in
theorem ggPR_le_normalizer (R : Subgroup G) :
    ggPR R ≤ Subgroup.normalizer (R : Set G) :=
  Subgroup.map_subtype_le _

theorem ggPR_inf_le_ggQR (p : ℕ) (B : Subgroup G) (x : G) (L D J R : Subgroup G) :
    ggPR R ⊓ (ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G)) ≤ ggQR p B x L D J R := by
  refine ggLe_pCoreOf_two inf_le_right (fun g hg => ?_)
    ((ggPCoreOf_two_isPGroup _).to_le inf_le_left)
  have h1 : g ∈ Subgroup.normalizer (ggPR R : Set G) :=
    mem_normalizer_pCoreOf (Subgroup.mem_inf.mp hg).2
  exact mem_normalizer_inf h1 (Subgroup.le_normalizer hg)

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.centralizer_le_ggM_of_conj (_h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hC2 : Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J) {g : G}
    (hg : g ∈ ggG0 p B x L D J) (hDg : D.map (MulAut.conj g).toMonoidHom ≤ J) :
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J := by
  intro c hc
  have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hgd : g * d * g⁻¹ ∈ J := hDg ⟨d, hd, by simp [MulAut.conj_apply]⟩
    have hcd := Subgroup.mem_centralizer_iff.mp hc _ hgd
    calc d * (g⁻¹ * c * g) = g⁻¹ * ((g * d * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * d * g⁻¹)) * g := by rw [hcd]
      _ = g⁻¹ * c * g * d := by group
  have hm := hC2 hc'
  have hgM : g ∈ ggM p B x L D J := Subgroup.le_normalizer hg
  have := (ggM p B x L D J).mul_mem ((ggM p B x L D J).mul_mem hgM hm)
    ((ggM p B x L D J).inv_mem hgM)
  simpa [mul_assoc] using this

theorem GGSixCtxV2.ggSR_le_of_perD (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {R : Subgroup G}
    (hRJ : R ≤ J)
    (hper : ∀ d ∈ D, d ≠ 1 → ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      (ggSR p B x L D J R ⊓ ggKd p B x L D J d) ⊔
        (ggSR p B x L D J R ⊓ Subgroup.centralizer (ggKd p B x L D J d : Set G))) :
    ggSR p B x L D J R ≤ (ggSR p B x L D J R ⊓ ggQR p B x L D J R) ⊔
      (ggSR p B x L D J R ⊓ Subgroup.centralizer (J : Set G)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hDR : D ≤ Subgroup.normalizer (R : Set G) :=
    (h.le_centralizer_J.trans (Subgroup.centralizer_le hRJ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDS : D ≤ Subgroup.normalizer (ggSR p B x L D J R : Set G) := by
    intro d hd
    have hdR := hDR hd
    have hdP : d ∈ Subgroup.normalizer (ggPR R : Set G) := mem_normalizer_pCoreOf hdR
    have hdN₀ : d ∈ Subgroup.normalizer
        ((ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf (h.d_le_ggM hd) (Subgroup.le_normalizer hdR)
    have hdQ : d ∈ Subgroup.normalizer (ggQR p B x L D J R : Set G) :=
      ggMem_normalizer_pCoreOf_two hdN₀
    exact mem_normalizer_inf hdP (Subgroup.le_normalizer hdQ)
  have hS2 : ¬ p ∣ Nat.card (ggSR p B x L D J R) := by
    have hSp : IsPGroup 2 (ggSR p B x L D J R) :=
      (ggPCoreOf_two_isPGroup _).to_le inf_le_left
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    rw [hk]
    intro hd
    exact h.ne_two ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      (h.prime.dvd_of_dvd_pow hd))
  refine ggLe_of_coprime_generation h.d_elem h.card_d hS2 hDS fun d hd hd1 =>
    (hper d hd hd1).trans (sup_le_sup (le_inf inf_le_left ?_)
      (inf_le_inf_left _ (Subgroup.centralizer_le (le_ggKd p B x L D J d))))
  intro s hs
  obtain ⟨hsS, hsK⟩ := Subgroup.mem_inf.mp hs
  have hsP : s ∈ ggPR R := (Subgroup.mem_inf.mp hsS).1
  exact ggPR_inf_le_ggQR p B x L D J R (Subgroup.mem_inf.mpr ⟨hsP,
    Subgroup.mem_inf.mpr ⟨h.ggKd_le_ggG0 hd hsK, ggPR_le_normalizer R hsP⟩⟩)

theorem GGSixCtxV2.centralizer_le_ggM_of_data (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    {R J₀ : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hJ₀J : J₀ ≤ J)
    (hgen : ggQR p B x L D J R ⊔ J₀ = ggG0 p B x L D J)
    (h67i : ggSR p B x L D J R ≤ (ggSR p B x L D J R ⊓ ggQR p B x L D J R) ⊔
      (ggSR p B x L D J R ⊓ Subgroup.centralizer (J : Set G)))
    (hSQC : ggSR p B x L D J R ≤ ggM p B x L D J →
      ⁅ggSR p B x L D J R, ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G)⁆ ≤
        ggQR p B x L D J R →
      ggSR p B x L D J R ≤
        ggQR p B x L D J R ⊔ Subgroup.centralizer (ggG0 p B x L D J : Set G))
    (hcase : ggCenterOf (ggQR p B x L D J R) ≤ ggPR R → ggPR R ≤ ggQR p B x L D J R →
      ggPR R ≠ ggQR p B x L D J R →
      ¬ ggQR p B x L D J R ≤ Subgroup.centralizer (ggPR R : Set G) →
        (⁅ggQR p B x L D J R, ggQR p B x L D J R⁆ ≤ R ∧
          ggQR p B x L D J R ≤ Subgroup.centralizer (R : Set G)) ∨
        J ⊔ ggPR R = ggG0 p B x L D J) :
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J := by
  set G₀ := ggG0 p B x L D J with hG₀
  set N := Subgroup.normalizer (R : Set G) with hN
  set P := ggPR R with hP
  set N₀ := G₀ ⊓ N with hN₀
  set Q := ggQR p B x L D J R with hQ
  set S := ggSR p B x L D J R with hS
  have hQN₀ : Q ≤ N₀ := Subgroup.map_subtype_le _
  have hQG₀ : Q ≤ G₀ := hQN₀.trans inf_le_left
  have hQN : Q ≤ N := hQN₀.trans inf_le_right
  have hPN : P ≤ N := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := ggPCoreOf_two_isPGroup N
  have hQ2 : IsPGroup 2 Q := ggPCoreOf_two_isPGroup N₀
  have hNP : N ≤ Subgroup.normalizer (P : Set G) := fun g hg => mem_normalizer_pCoreOf hg
  have hchar : N ⊓ Subgroup.centralizer (P : Set G) ≤ P := hctx.charTwo N ⟨R, hR1, hR2, rfl⟩
  have hCJN : Subgroup.centralizer (J : Set G) ≤ N :=
    (Subgroup.centralizer_le hRJ).trans (Subgroup.centralizer_le_normalizer _)
  have hCJ₀ : Subgroup.centralizer (J : Set G) ≤ Subgroup.normalizer (J₀ : Set G) :=
    (Subgroup.centralizer_le hJ₀J).trans (Subgroup.centralizer_le_normalizer _)
  have hSM : S ≤ ggM p B x L D J := by
    refine h67i.trans (sup_le ?_ ?_)
    · exact (inf_le_right.trans hQG₀).trans Subgroup.le_normalizer
    · intro s hs
      show s ∈ Subgroup.normalizer ((G₀ : Subgroup G) : Set G)
      rw [← hgen]
      exact ggMem_normalizer_sup ((inf_le_left : S ⊓ _ ≤ S).trans inf_le_right hs) (hCJ₀ hs.2)
  have hPN₀ : P ⊓ N₀ ≤ Q := ggPR_inf_le_ggQR p B x L D J R
  have hSN₀ : ⁅S, N₀⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr fun s hs m hm => ?_
    have hsP : s ∈ P := hs.1
    have hsM : s ∈ ggM p B x L D J := hSM hs
    refine hPN₀ ⟨ggCommutatorElement_mem_left hsP (hNP hm.2), ?_, ?_⟩
    · exact ggCommutatorElement_mem_right hm.1 hsM
    · exact N.mul_mem (N.mul_mem (N.mul_mem (hPN hsP) hm.2) (N.inv_mem (hPN hsP)))
        (N.inv_mem hm.2)
  have hSQ : S ≤ Q := by
    refine ggLe_of_le_sup_of_odd (hP2.to_le inf_le_left) hQ2 inf_le_right ?_ hodd (hSQC hSM hSN₀)
    exact hQG₀.trans fun g hg => mem_normalizer_centralizer (Subgroup.le_normalizer hg)
  have hPQ : P ≤ Q := ggLe_of_inf_normalizer_le hP2 hQ2 (hQN.trans hNP) hSQ
  have hCJP : Subgroup.centralizer (J : Set G) ≤ Subgroup.normalizer (P : Set G) := hCJN.trans hNP
  by_cases hPQe : P = Q
  · intro g hg
    show g ∈ Subgroup.normalizer ((G₀ : Subgroup G) : Set G)
    rw [← hgen]
    exact ggMem_normalizer_sup (hPQe ▸ hCJP hg) (hCJ₀ hg)
  · by_cases hQcent : Q ≤ Subgroup.centralizer (P : Set G)
    · exact absurd (le_antisymm hPQ (le_inf hQN hQcent |>.trans hchar)) hPQe
    · have hZ : ggCenterOf Q ≤ P := by
        refine le_trans (le_inf ((Subgroup.map_subtype_le _).trans hQN) ?_) hchar
        rw [Subgroup.le_centralizer_iff]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨z, hz, rfl⟩
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, hPQ ha⟩)).symm
      rcases hcase hZ hPQ hPQe hQcent with ⟨hQQ, hQR⟩ | hJP
      · exfalso
        apply hPQe
        refine le_antisymm hPQ (le_pCoreOf_of_stability le_rfl hR2 hchar hQN (fun q hq a ha => ?_)
          hQR)
        have : q * a * q⁻¹ * a⁻¹ = ⁅q, a⁆ := by rw [commutatorElement_def]
        rw [this]
        exact hQQ (Subgroup.commutator_mem_commutator hq (hPQ ha))
      · intro g hg
        show g ∈ Subgroup.normalizer ((G₀ : Subgroup G) : Set G)
        rw [← hJP]
        exact ggMem_normalizer_sup (Subgroup.centralizer_le_normalizer _ hg) (hCJP hg)

end Ctx

end CFSG.StandardType
