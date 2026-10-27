module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22so
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_conjClosure_of_commutator_le {N H T B W : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hchar : N ⊓ centralizer (CFSG.Open.pCoreOf 2 N : Set G) ≤ CFSG.Open.pCoreOf 2 N)
    (hTN : CFSG.ABGLocalTools.IsSylowOf 2 T N) (hHN : H ≤ N) (hTH : T ≤ H) (hBH : B ≤ H)
    (hBp : Nat.card B = p) (hWT : W ≤ T) (hWH : H ≤ normalizer (W : Set G))
    (hTBW : ⁅T, B⁆ ≤ W)
    (hBZ : B ≤ centralizer (CFSG.RankThree.PartOne.omegaOneCenterIn T : Set G)) :
    B ≤ centralizer
      (UC22.conjClosure H (CFSG.RankThree.PartOne.omegaOneCenterIn T) : Set G) := by
  classical
  set Z : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn T with hZ
  set V : Subgroup G := UC22.conjClosure H Z with hV
  have hT2 : IsPGroup 2 T := hTN.isPGroup
  have hO2T : CFSG.Open.pCoreOf 2 N ≤ T := UC22.P22so.pCoreOf_le_of_isSylowOf hTN
  have hZT : Z ≤ T := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T
  have hZcent : Z ≤ centralizer (CFSG.Open.pCoreOf 2 N : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro x hx
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 x (hO2T hx)
  have hZO : Z ≤ CFSG.Open.pCoreOf 2 N :=
    (le_inf (hZT.trans hTN.le) hZcent).trans hchar
  set F : Subgroup G :=
    CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 N) with hF
  have hconjF : ∀ g ∈ H, ∀ y ∈ F, g * y * g⁻¹ ∈ F := by
    intro g hg y hy
    rw [hF, CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff] at hy ⊢
    obtain ⟨hyO, hyC, hy2⟩ := hy
    refine ⟨UC22.uc22main1_conj_mem_pCoreOf_self (hHN hg) hyO, ?_, ?_⟩
    · intro k hk
      have hk' : g⁻¹ * k * g ∈ CFSG.Open.pCoreOf 2 N := by
        simpa using UC22.uc22main1_conj_mem_pCoreOf_self (hHN (H.inv_mem hg)) hk
      have hfk := hyC _ hk'
      calc k * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [hfk]
        _ = (g * y * g⁻¹) * k := by group
    · calc (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hy2]; group
  have hHF : H ≤ normalizer (F : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hconjF g hg x hx, fun hx => by
      have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ F := by
        simpa using hconjF g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
      have he : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [he] at h1⟩
  have hZF : Z ≤ F := by
    intro z hz
    rw [hF, CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff]
    refine ⟨hZO hz, ?_,
      (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.2⟩
    intro x hx
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 x (hO2T hx)
  have hVF : V ≤ F := UC22.uc22p22v_conjClosure_le hHF hZF
  have hVT : V ≤ T :=
    (hVF.trans (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le _)).trans hO2T
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hCVT : ∀ v ∈ V, (∀ t ∈ T, t * v * t⁻¹ = v) → v ∈ Z := by
    intro v hv hfixT
    rw [hZ, CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff]
    refine ⟨hVT hv, ?_, (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp
      (hVF hv)).2.2⟩
    intro k hk
    calc k * v = (k * v * k⁻¹) * k := by group
      _ = v * k := by rw [hfixT k hk]
  have hZCW : Z ≤ centralizer (W : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro w hw
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 w (hWT hw)
  have hHNC : H ≤ normalizer (centralizer (W : Set G) : Set G) :=
    fun h hh => UC22.P22so.mem_normalizer_centralizer_of (hWH hh)
  have hVCW : V ≤ centralizer (W : Set G) := UC22.uc22p22v_conjClosure_le hHNC hZCW
  have hWV : W ≤ centralizer (V : Set G) :=
    (Subgroup.le_centralizer_iff (H := W) (K := V)).mpr hVCW
  have hHV : H ≤ normalizer (V : Set G) := UC22.uc22p22v_le_normalizer_conjClosure H Z
  let φ : H →* MulAut V := (normalizerMonoidHom V).comp (inclusion hHV)
  let α : B.subgroupOf H →* MulAut V := φ.comp (B.subgroupOf H).subtype
  let β : T.subgroupOf H →* MulAut V := φ.comp (T.subgroupOf H).subtype
  have hφ_coe : ∀ (h : H) (v : V), (((φ h) v : V) : G) = (h : G) * (v : G) * (h : G)⁻¹ := by
    intro h v
    dsimp only [φ]
    rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hφ_one : ∀ c : H, (c : G) ∈ centralizer (V : Set G) → φ c = 1 := by
    intro c hc
    ext v
    rw [hφ_coe]
    change (c : G) * (v : G) * (c : G)⁻¹ = (v : G)
    have hcv : (v : G) * (c : G) = (c : G) * (v : G) :=
      (Subgroup.mem_centralizer_iff.mp hc) (v : G) v.2
    rw [← hcv]
    group
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    change φ a.1 * φ b.1 = φ b.1 * φ a.1
    rw [← map_mul, ← map_mul]
    set c : H := a.1 * b.1 * (b.1 * a.1)⁻¹ with hc
    have hcW : (c : G) ∈ W := by
      have hmem : ⁅((b.1 : H) : G), ((a.1 : H) : G)⁆ ∈ ⁅T, B⁆ :=
        Subgroup.commutator_mem_commutator b.2 a.2
      have hc_eq : (c : G) = ⁅((b.1 : H) : G), ((a.1 : H) : G)⁆⁻¹ := by
        rw [hc, commutatorElement_def]
        push_cast
        group
      rw [hc_eq]
      exact W.inv_mem (hTBW hmem)
    have hφc : φ c = 1 := hφ_one c (hWV hcW)
    have heq : a.1 * b.1 = c * (b.1 * a.1) := by
      rw [hc]
      group
    rw [heq, map_mul, hφc, one_mul]
  have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    intro a r hr
    have hrT : ∀ t ∈ T, t * (r : G) * t⁻¹ = (r : G) := by
      intro t ht
      have h1 : (((β ⟨⟨t, hTH ht⟩, ht⟩) r : V) : G) = (r : G) := by
        simpa using congrArg (fun x : V => (x : G)) (hr ⟨⟨t, hTH ht⟩, ht⟩)
      have h2 : (((β ⟨⟨t, hTH ht⟩, ht⟩) r : V) : G) = t * (r : G) * t⁻¹ := by
        change (((φ ((⟨⟨t, hTH ht⟩, ht⟩ : T.subgroupOf H).1)) r : V) : G) =
          t * (r : G) * t⁻¹
        rw [hφ_coe]
      rw [h2] at h1
      exact h1
    have hrZ : (r : G) ∈ Z := hCVT r r.2 hrT
    apply Subtype.ext
    change (((φ a.1) r : V) : G) = (r : G)
    rw [hφ_coe]
    have hza : (r : G) * (a.1 : G) = (a.1 : G) * (r : G) :=
      (Subgroup.mem_centralizer_iff.mp (hBZ a.2)) (r : G) hrZ
    rw [← hza]
    group
  have hcard : Nat.card (B.subgroupOf H) = p := by
    rw [← hBp]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hA : ¬ 2 ∣ Nat.card (B.subgroupOf H) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).not_two_dvd_nat
  have hB2 : IsPGroup 2 (T.subgroupOf H) := hT2.comap_subtype
  have key := CFSG.GroupTheory.thompson_A_times_B (p := 2) hV2 hA hB2 α β hcomm hfix
  intro b hb
  rw [mem_centralizer_iff]
  intro v hv
  have h2 : b * v * b⁻¹ = v := by
    have h1 : ((φ (⟨b, hBH hb⟩ : H)) ⟨v, hv⟩ : V) = ⟨v, hv⟩ := by
      have hk := congrArg (fun f : MulAut V => f ⟨v, hv⟩) (key ⟨⟨b, hBH hb⟩, hb⟩)
      simpa [α] using hk
    have h3 := congrArg (fun x : V => (x : G)) h1
    rw [hφ_coe] at h3
    simpa using h3
  calc v * b = (b * v * b⁻¹) * b := by rw [h2]
    _ = b * v := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
