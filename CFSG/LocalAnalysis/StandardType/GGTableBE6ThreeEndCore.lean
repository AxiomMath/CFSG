module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndAut
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.LocalAnalysis.StandardType.GGTableBExcEndNode
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
  CFSG.SeitzReduction CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TableBExc.E6Three

namespace E6ThreeEnd

section Weyl

variable {τ : Tag} {K : Type} [Field K]

theorem psiHat_eq_one_of_conj_pinnedX (j₀ : Fin τ.rank) {x : monoHat τ K} (h3 : x ^ 3 = 1)
    (hc : ∀ i, i ≠ j₀ → (x : ModGL τ K) * pinnedX τ K (Pi.single i 1) 1 * (x : ModGL τ K)⁻¹ =
      pinnedX τ K (Pi.single i 1) 1) :
    psiHat τ K x = 1 := by
  obtain ⟨n, hn, a, hna⟩ := x.2
  have hψ : psiHat τ K x = weylQuotientHom τ K ⟨n, hn⟩ := by
    rw [← psiHat_mul_rootDiagUnit hn a (hna ▸ x.2)]
    congr 1
    exact Subtype.ext hna
  have hfix : ∀ i, i ≠ j₀ → weylQuotientHom τ K ⟨n, hn⟩ • (Pi.single i 1 : Fin τ.rank → ℤ) =
      Pi.single i 1 := by
    intro i hi
    have hr := isRoot_single τ i
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hr
    have e1 := hc i hi
    rw [hna] at e1
    have e2 : n * rootDiagUnit τ a * pinnedX τ K (Pi.single i 1) 1 * (n * rootDiagUnit τ a)⁻¹ =
        n * (rootDiagUnit τ a * pinnedX τ K (Pi.single i 1) 1 * (rootDiagUnit τ a)⁻¹) * n⁻¹ := by
      group
    rw [e2, rootDiagUnit_conj_pinnedX a hr, hμ] at e1
    exact CFSG.SeitzReduction.EPilot.eq_of_pinnedX_eq_pinnedX_of_pos (IsRoot.smul hr _) hr
      (by simp) one_ne_zero e1
  have hw3 : weylQuotientHom τ K ⟨n, hn⟩ ^ 3 = 1 := by
    rw [← hψ, ← map_pow, h3, map_one]
  rw [hψ]
  exact eq_one_of_fix_of_pow_three j₀ hfix hw3

end Weyl

section Diag

variable {τ : Tag} {K : Type} [Field K]

theorem exists_eq_pow_of_conj_pinnedX {ζ : Kˣ} (hζo : orderOf ζ = 3) {b : Fin τ.rank → Kˣ}
    (hb3 : b ^ 3 = 1)
    (hc : ∀ i, i ≠ highNode τ → rootDiagUnit τ b * pinnedX τ K (Pi.single i 1) 1 *
      (rootDiagUnit τ b)⁻¹ = pinnedX τ K (Pi.single i 1) 1) :
    ∃ k : ℕ, rootDiagUnit τ b = rootDiagUnit τ (highDiag τ ζ) ^ k := by
  have hbi : ∀ i, i ≠ highNode τ → b i = 1 := by
    intro i hi
    have h := hc i hi
    rw [rootDiagUnit_conj_pinnedX b (isRoot_single τ i), TableBExc.rootChar_single,
      mul_one] at h
    exact Units.ext (pinnedX_injective τ K _ h)
  have hb3' : b (highNode τ) ^ 3 = 1 := by
    have h := congrFun hb3 (highNode τ)
    rwa [Pi.pow_apply, Pi.one_apply] at h
  obtain ⟨m, hm⟩ := CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζo hb3'
  refine ⟨m.val, ?_⟩
  rw [rootDiagUnit_pow, highDiag, ← Pi.mulSingle_pow, hm]
  congr 1
  funext j
  by_cases hj : j = highNode τ
  · rw [hj, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hj, hbi j hj]

end Diag

section Elt

variable {K : Type} [Field K]

@[expose] noncomputable def endNodeHat (ζ : Kˣ) : hatGroup .E6 K :=
  ⟨rootDiagUnit .E6 (highDiag .E6 ζ), rootDiagUnit_mem_hatGroup _⟩

theorem coe_endNodeHat (ζ : Kˣ) :
    (endNodeHat ζ : ModGL .E6 K) = rootDiagUnit .E6 (highDiag .E6 ζ) :=
  rfl

theorem hatAut_endNodeHat (ζ : Kˣ) :
    hatAut .E6 K (endNodeHat ζ) =
      MulAut.conj (TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ) := by
  ext h
  rw [coe_hatAut_apply]
  rfl

end Elt

section Core

variable {K : Type} [Field K]

theorem autEndNode_of_le_monoHat [Finite K] [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3)
    {P : Subgroup (hatGroup .E6 K)} (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPm : ∀ x ∈ P, (x : ModGL .E6 K) ∈ monoHat .E6 K) (ht : endNodeHat ζ ∈ P) :
    AutEndNode (P.map (hatAut .E6 K)) := by
  have hζ3 : 3 ≤ orderOf ζ := hζo.ge
  obtain ⟨hlay, hcomp⟩ := TableBExc.layer_centralizer_endNodeElt (τ := .E6) (Or.inl rfl)
    (ringChar.eq K 2) hζ3 E6Pilot.isQuasisimple_a5Levi
  refine ⟨MulAut.conj (TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ),
    ⟨endNodeHat ζ, ht, hatAut_endNodeHat ζ⟩, ?_, ?_, ?_⟩
  · intro h1
    have hc : TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ ∈
        Subgroup.center (adjointGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := DFunLike.congr_fun h1 g
      rw [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ =
          TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ * g *
            (TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ)⁻¹ *
              TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ := by rw [h2]
        _ = TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ * g := by group
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    have h2 : rootDiagUnit .E6 (highDiag .E6 ζ) = rootDiagUnit .E6 1 := by
      rw [rootDiagUnit_one]
      exact congrArg Subtype.val hc
    have h3 := congrFun (rootDiagUnit_injective h2) (highNode .E6)
    rw [highDiag, Pi.mulSingle_eq_same, Pi.one_apply] at h3
    rw [h3, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  · rw [ggFix_conj, hlay]
    exact hcomp
  · rintro _ ⟨s, hs, rfl⟩
    rw [ggFix_conj, hlay]
    have hs3 : (s : ModGL .E6 K) ^ 3 = 1 := by
      have h := congrArg Subtype.val (hP3 s hs)
      simpa using h
    constructor
    · intro hfix
      have hcent : ∀ i, i ≠ highNode .E6 →
          (s : ModGL .E6 K) * pinnedX .E6 K (Pi.single i 1) 1 * (s : ModGL .E6 K)⁻¹ =
            pinnedX .E6 K (Pi.single i 1) 1 := by
        intro i hi
        have h := congrArg Subtype.val (hfix (pinnedElt .E6 (Pi.single i 1) 1)
          (pinnedElt_mem_perpLevi (single_mem_perpRoots hi) 1))
        rw [coe_hatAut_apply] at h
        exact h
      have hsm := hPm s hs
      have hs3' : (⟨(s : ModGL .E6 K), hsm⟩ : monoHat .E6 K) ^ 3 = 1 :=
        Subtype.ext (by simpa using hs3)
      have hψ := psiHat_eq_one_of_conj_pinnedX (highNode .E6) hs3' hcent
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hψ
      have hb' : (s : ModGL .E6 K) = rootDiagUnit .E6 b := hb
      have hb3 : b ^ 3 = 1 := by
        rw [hb', rootDiagUnit_pow] at hs3
        exact rootDiagUnit_injective (hs3.trans rootDiagUnit_one.symm)
      obtain ⟨k, hk⟩ := exists_eq_pow_of_conj_pinnedX hζo hb3 (fun i hi => by
        rw [← hb']
        exact hcent i hi)
      refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), ?_⟩
      rw [zpow_natCast, ← hatAut_endNodeHat, ← map_pow]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_pow, hb', hk]
      rfl
    · intro hmem j hj
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk, ← map_zpow, MulAut.conj_apply]
      have hj' : (j : ModGL .E6 K) ∈ rootSpan .E6 K (perpRoots .E6) := by
        rw [perpLevi, Subgroup.mem_subgroupOf] at hj
        exact hj
      have ht' : ((TableBExc.endNodeElt (τ := .E6) (Or.inl rfl) ζ ^ k : adjointGroup .E6 K) :
          ModGL .E6 K) ∈ highTorusLine .E6 K := by
        rw [Subgroup.coe_zpow]
        exact zpow_mem (rootDiagUnit_highDiag_mem_highTorusLine ζ) k
      have hc := (commute_of_mem_highTorusLine_of_mem_rootSpan ht' hj').eq
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, Subgroup.coe_inv, mul_inv_cancel_right]

end Core

end E6ThreeEnd

end CFSG.StandardType
