module

public import CFSG.RankThree.PartOne.S15K.LayerData
public import CFSG.RankThree.PartOne.S15K.Row2
public import CFSG.RankThree.PartOne.S15K.PSylowSpBlocks
import CFSG.RankThree.PartOne.S15K.LayerFactor
import CFSG.RankThree.PartOne.S15K.ProjComm
import CFSG.RankThree.PartOne.S15K.SpLayer
import CFSG.RankThree.PartOne.S15K.LayerTransport

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.ComponentClassification CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {G : Type} [Group G] [Finite G]

theorem layerData_of_lifts_sp {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E I : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 3 < 2 ^ f) (hpq : p ∣ 2 ^ f - 1) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (φ : ↥I ≃* StatedProj (StatedSp 3 K)) (x : ↥E → StatedSp 3 K) (hxp : ∀ e, x e ^ p = 1)
    (hxc : ∀ e : ↥E, MulAut.conj (proj 3 K (x e)) = actP φ ⟨(e : G), hEI e.2⟩)
    (hxcomm : ∀ e e' : ↥E, x e * x e' = x e' * x e) (hxo : ∀ e : ↥E, e ≠ 1 → orderOf (x e) = p)
    (hord : ∀ e : ↥E, e ≠ 1 → orderOf (actP φ ⟨(e : G), hEI e.2⟩) = p) : LayerDataP p E I := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  obtain ⟨-, -, hTinj⟩ := spProj_facts (ℓ := 2) (f := f) Nat.prime_two hf hK
    (by norm_num : 2 ≤ 3) (by omega)
  let ψ : ↥I →* MulAut (StatedProj (StatedSp 3 K)) :=
    (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut (StatedProj (StatedSp 3 K))).comp
      φ.toMonoidHom
  have hψ : Function.Injective ψ := hTinj.comp φ.injective
  have hψrange : ψ.range = (MulAut.conj : StatedProj (StatedSp 3 K) →*
      MulAut (StatedProj (StatedSp 3 K))).range := by
    ext y
    constructor
    · rintro ⟨y', rfl⟩
      exact ⟨φ y', rfl⟩
    · rintro ⟨p0, rfl⟩
      exact ⟨φ.symm p0, by simp [ψ]⟩
  have hInnB : (MulAut.conj : StatedProj (StatedSp 3 K) →*
      MulAut (StatedProj (StatedSp 3 K))).range ≤ ψ.range := hψrange.ge
  have hBD : ψ.range ≤ (SymplecticHigher.conjAut 3 K).range := by
    rw [hψrange, ← SymplecticHigher.spLinearAutGroup_eq_range, UnitaryHigher.spLinearAutGroup_eq_inner_of_charTwo]
    exact le_rfl
  intro b hb hb1
  have hbI : b ∈ Subgroup.normalizer (I : Set G) := hEI hb
  set bE : ↥E := ⟨b, hb⟩ with hbE
  have hbne : bE ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨-, hD⟩ := KCSpComm.exists_unique_lift (ℓ := 2) (f := f) Nat.prime_two hf
    (by norm_num : 2 ≤ 3) hK hq hp hp3 hp2 (actP φ ⟨(bE : G), hEI bE.2⟩)
    ⟨proj 3 K (x bE), hxc bE⟩ (hord bE hbne)
  obtain ⟨D, blocks⟩ := hD (x bE) (hxo bE hbne) (hxc bE)
  have S := spProjSetting D blocks ψ.range hInnB
  have hcompb : ∀ y : ↥I, ψ (I.normalizerMonoidHom ⟨b, hbI⟩ y) =
      SymplecticHigher.conjAut 3 K (spXg (x bE)) * ψ y *
        (SymplecticHigher.conjAut 3 K (spXg (x bE)))⁻¹ :=
    compat_of_actP φ ((conjAut_statedSp (x bE)).trans (hxc bE)).symm
  obtain ⟨Q, hQH, hQc, hder, hmem⟩ := layer_of_projSetting ψ hψ hbI hcompb hBD S
  have hq2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have h42 : ¬ (spFixedDim (x bE) = 4 ∧ Nat.card K = 2) := fun h => by
    have := h.2
    rw [hK] at this
    omega
  have hpm : ∀ h : primaryFactors (spEnd (x bE)), (h : K[X]) ≠ X - 1 →
      ¬ p ∣ primaryMultiplicity (spEnd (x bE)) (h : K[X]) := fun h _ =>
    sp_not_dvd_mult hp hp5 blocks D.squarefree h
  have hMder := S.M_derived
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp (by rw [hK]; exact hpq)
  refine ⟨_, Q, hQH, hQc, hder, fun i => ⟨?_, ?_⟩, fun i => ?_⟩
  · intro e' he'
    set eE : ↥E := ⟨e', he'⟩ with heE
    have hcompe : ∀ y : ↥I, ψ (I.normalizerMonoidHom ⟨e', hEI he'⟩ y) =
        SymplecticHigher.conjAut 3 K (spXg (x eE)) * ψ y *
          (SymplecticHigher.conjAut 3 K (spXg (x eE)))⁻¹ :=
      compat_of_actP φ ((conjAut_statedSp (x eE)).trans (hxc eE)).symm
    have hv : x eE ∈ Subgroup.centralizer ({x bE} : Set (StatedSp 3 K)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hxcomm eE bE)
    obtain ⟨z, k, w, hvzkw, -, hzc, -, hkK, hwW, hwp⟩ :=
      spFactorization hp hp5 hq2 blocks hpm hv (hxp eE)
    refine exists_mul_mem_centralizer_of_factor ψ hψ (SymplecticHigher.conjAut 3 K)
      (fun a : SpBlockIdx (x bE) => spBlockGSp (x bE) (a.1 : K[X])) i (hmem i) (S.map_le_B i)
      (fun j hj => projSetting_commute_of_ne S i j hj) (hEI he') hcompe
      (m := spXg (x eE)) (z := spXg z) (k := spXg k * spXg w) ?_
      (fun f hf => spXg_commute_of_mem_block hzc hf) ?_
    · apply Subtype.ext
      have h1 := congrArg (fun s : StatedSp 3 K => (s : GL (Fin 3 ⊕ Fin 3) K)) hvzkw
      simpa [spXg, mul_assoc] using h1
    · have hkM := spXg_mul_mem_derived Nat.prime_two hf hK hp hp5 hq2 h42 blocks hkK hwW hwp
      rw [hMder] at hkM
      exact hkM
  · refine not_dvd_card_inf_centralizer ψ hψ (SymplecticHigher.conjAut 3 K) (hmem i)
      (S.map_le_B i) (fun u hu hu1 => spBlockGSp_conjAut_inj hTinj hu hu1) hp ?_
    exact spBlockGSp_center_pow hp hp5 hq hK D.primaryData blocks i.1
      (sp_not_dvd_mult hp hp5 blocks D.squarefree i.1)
  · exact psylowIn_of_transport ψ hψ (SymplecticHigher.conjAut 3 K) (hmem i) (S.map_le_B i)
      (fun u hu hu1 => spBlockGSp_conjAut_inj hTinj hu hu1)
      (psylowSub_spBlockGSp hp hp5 hζ blocks (by positivity) hpq
        (fun h => sp_not_dvd_mult hp hp5 blocks D.squarefree h) i.1)

theorem layerRowTwo : LayerRowTwo := by
  intro G _ _ p A c L E h15 hF h13 hout
  obtain ⟨f, hf, hpq, ⟨φ₀⟩, -, hEA, -⟩ := hout
  have h := h15.h12
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq : 3 < 2 ^ f := by
    have hpos : 0 < 2 ^ f - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
    have := Nat.le_of_dvd hpos hpq
    omega
  obtain ⟨φ, -⟩ : ∃ φ : ↥(lieGenerated p E) ≃* StatedProj (StatedSp 3 (GaloisField 2 f)), True :=
    ⟨φ₀.trans (statedProjEquivProjSp 3 (GaloisField 2 f)).symm, trivial⟩
  exact (row2_lifts_of_field h h13 hEA hf hK hq hpq φ).elim fun x hx =>
    layerData_of_lifts_sp hp h5 hf hK hq hpq (E_le_normalizer_lieGenerated hp) φ x hx.1 hx.2.1
      hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2

end CFSG.RankThree.PartOne.S15K
