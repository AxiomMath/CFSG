module

public import CFSG.Milestones.ASVolI.F437U.Top
public import CFSG.Milestones.ASVolI.F431.RonanOddU5Syl
public import CFSG.Milestones.ASVolI.F431.RonanOddU5Tr
public import CFSG.Milestones.ASVolI.F431.RonanOddU5Mod
public import CFSG.Milestones.ASVolI.F431.RonanOddU5Card
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def OddIndexU5 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 GLKind.U5 1 Gp M₁ M₂ β ε z → ¬ IsL43 M → Odd Gp.index

theorem ronOdd5_two_pow_dvd_720 {n : ℕ} (h : 2 ^ n ∣ 720) : 2 ^ n ≤ 16 := by
  by_contra hlt
  push Not at hlt
  have hn : 5 ≤ n := by
    by_contra h5
    push Not at h5
    have h4 : n ≤ 4 := by omega
    have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
    omega
  have h32 : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 hn
  have := h32.trans h
  omega

section Main

set_option linter.unusedSectionVars false



theorem oddIndex_U5 : OddIndexU5 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp _hL
  classical
  by_contra hev
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  haveI := hyp.finite_M
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGp : Gp ≠ ⊤ := fun h => hev (by rw [h, Subgroup.index_top]; exact odd_one)
  have hidx2 : Gp.index = 2 := by
    rcases burnsideF429_F429_one_Un_two (Or.inr rfl) hyp.amalgam with h | h
    · exact absurd h hGp
    · exact h.1
  obtain ⟨s, hsM, hsG, hs2, -⟩ := burnsideF4r_u5_graph_exists hyp.amalgam hGp
  obtain ⟨Tb, hTb, fb, hfT, hf2, hfG', hsyl⟩ := ronOdd5_extremal hyp.amalgam hsM hs2
  have hfG : fb ∉ Gp := hfG' hsG
  have hTb12 : Tb ≤ M₁ ⊓ M₂ := hTb.1
  have hTb1 : Tb ≤ M₁ := hTb12.trans inf_le_left
  have hfM : fb ∈ M₁ ⊓ M₂ := hTb12 hfT
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSTb : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Tb := burnsideF4j_S_le_sylow hyp.amalgam hTb
  have hSS : fb ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := fun h => hfG (hSB h).1
  have hidx : ∀ e : E, e ∉ Gp → e * fb ∈ Gp := fun e he =>
    burnsideF4r_u5_mul_mem hyp.amalgam.toHypF_4_4g he hfG
  obtain ⟨hFG, hQ, -, -, -, h4⟩ := burnsideF437U_F437KindDeg_U5 E Gp M₁ M₂ Y β M ε z hyp Tb hTb
    ⟨fb, hfM⟩ hfT hSS hf2 (fun h => absurd h.1 (by decide)) hsyl
  have hgraph : hyp.amalgam.toHypF_4_4g.chart.IsGraphInv fb := by
    rcases hFG with h | h
    · exact absurd rfl (burnsideF437_field_kind h).2
    · exact h
  have hLie : IsGenLie (cenIn Gp fb) .Sp4 2 1 := by
    rcases hQ with ⟨sd, hsd, hdeg, -⟩ | ⟨-, -, hL, -⟩
    · omega
    · exact hL
  have hTf : IsSylowTwoOf (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε ⟨fb, hfM⟩} : Set M))
      (Subgroup.centralizer ({bM β ε ⟨fb, hfM⟩} : Set M)) := by
    rcases h4 with h | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  have h36 := burnsideF4m_F_4_36 .U5 1 E Gp M₁ M₂ Y β M ε z hyp (Or.inr rfl) rfl Tb hTb
    ⟨fb, hfM⟩ hfT hgraph
  obtain ⟨t₀, ht₀S, ht₀1, ht₀2, ht₀L, P, hPS, hPC, hP256⟩ := ronOdd5_short hyp.amalgam hgraph
  have ht₀12 : t₀ ∈ M₁ ⊓ M₂ := (hSB ht₀S).2
  have hP1 : P ≤ M₁ := fun x hx => (hSB (hPS hx)).2.1
  have hP2 : IsPGroup 2 ↥P := hTb.2.1.to_le (hPS.trans hSTb)
  set b1 := burnsideF4d_bOne β ε with hb1def
  have hb1 : Function.Injective b1 := burnsideF4j_bOne_injective hyp
  have hfM1 : fb ∈ M₁ := hfM.1
  have hTf_eq : imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε ⟨fb, hfM⟩} : Set M) =
      subImg b1 (Tb ⊓ Subgroup.centralizer ({fb} : Set E)) := by
    rw [burnsideF437_imB_eq β ε hTb12, burnsideF437_bM_eq,
      CFSG.Quasithin.H13.F431.L3.subImg_inf_centralizer b1 hb1 hfM1]
  have hcardTf :
      Nat.card ↥(imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε ⟨fb, hfM⟩} : Set M)) ≤ 32 := by
    rw [hTf_eq, card_subImg hb1 (inf_le_left.trans hTb1)]
    have hcard2 := burnsideF437U_card_eq_two_mul hidx2
      (X := Tb ⊓ Subgroup.centralizer ({fb} : Set E))
      ⟨hfT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ hfG
    have hGX : Gp ⊓ (Tb ⊓ Subgroup.centralizer ({fb} : Set E)) =
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) := by
      rw [← burnsideF4j_sylow_inf_Gp hyp.amalgam hTb]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [hGX] at hcard2
    have hSC :
        Nat.card ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E)) ≤ 16 := by
      have hp : IsPGroup 2
          ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E)) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
      have hdvd :
          Nat.card ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E)) ∣ 720 := by
        rw [← ronOdd5_card_sp42 hLie]
        exact Subgroup.card_dvd_of_le (fun x hx => ⟨(hSB hx.1).1, hx.2⟩)
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
      rw [hn] at hdvd ⊢
      exact ronOdd5_two_pow_dvd_720 hdvd
    omega
  set t : M := bM β ε ⟨fb, hfM⟩ with ht
  have key : ∀ c' : M, c' * t * c'⁻¹ ≠ bM β ε ⟨t₀, ht₀12⟩ := by
    intro c' hc'
    have h1 : Nat.card (Subgroup.centralizer ({bM β ε ⟨t₀, ht₀12⟩} : Set M)) =
        Nat.card (Subgroup.centralizer ({t} : Set M)) := card_centralizer_eq_of_conj hc'
    have h2 : twoPart (Subgroup.centralizer ({bM β ε ⟨t₀, ht₀12⟩} : Set M)) =
        twoPart (Subgroup.centralizer ({t} : Set M)) := by
      unfold twoPart
      rw [h1]
    have h3 := hTf.card_eq
    have hτ : bM β ε ⟨t₀, ht₀12⟩ = b1 ⟨t₀, ht₀12.1⟩ := burnsideF4j_bM_eq_bOne β ε ⟨t₀, ht₀12⟩
    have hle : subImg b1 P ≤ Subgroup.centralizer ({bM β ε ⟨t₀, ht₀12⟩} : Set M) := by
      intro y hy
      obtain ⟨p, hpM, hpP, rfl⟩ := mem_subImg.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff, hτ]
      exact (commute_iff_of_injective hb1 ht₀12.1 hpM).mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hPC hpP))
    have h4' : 256 ≤ twoPart (Subgroup.centralizer ({bM β ε ⟨t₀, ht₀12⟩} : Set M)) := by
      have := card_le_twoPart hle (CFSG.Quasithin.H13.F431.L3.isPGroup_subImg b1 hb1 hP1 hP2)
      rwa [card_subImg hb1 hP1, hP256] at this
    omega
  have hgc : ∀ g : M, IsConj (g⁻¹ * t * g) t := fun g => isConj_iff.mpr ⟨g, by group⟩
  refine ronOdd5_transfer hyp hfM hfG hf2 hidx hTb hfT ?_
  intro g x hxS hx1 hx2 hxe
  have hxGp : (x : E) ∈ Gp := (hSB hxS).1
  have hxE1 : (x : E) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxE2 : (x : E) * x = 1 := congrArg Subtype.val hx2
  by_cases hL : ∃ c ∈ Gp, c * (x : E) * c⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
  ·
    obtain ⟨x₀, hx₀Z, hx₀z, hx₀1, hx₀2⟩ := burnsideF4r_zbar hyp (by decide)
    have hx₀S : (x₀ : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := hx₀Z.1
    have hsame := burnsideF4r_conj_of_same_type hyp.amalgam (by decide) (by decide)
      hyp.not_G2d hxGp (hSB hx₀S).1 hxE1 hxE2 (fun h => hx₀1 (Subtype.ext h))
      (congrArg Subtype.val hx₀2)
      ⟨fun _ => ⟨1, Gp.one_mem, by rw [one_mul, inv_one, mul_one]; exact hx₀Z⟩, fun _ => hL⟩
    have hc : IsConj (bM β ε x) (bM β ε x₀) :=
      burnsideF4j_F_4_35_forward hyp x x₀ hxS hx₀S hsame
    rw [hx₀z, hxe] at hc
    exact h36 (((hgc g).symm.trans hc).symm)
  ·
    have ht₀Gp : t₀ ∈ Gp := (hSB ht₀S).1
    have hsame := burnsideF4r_conj_of_same_type hyp.amalgam (by decide) (by decide)
      hyp.not_G2d hxGp ht₀Gp hxE1 hxE2 ht₀1 ht₀2
      ⟨fun h => absurd h hL, fun h => absurd h ht₀L⟩
    have hc : IsConj (bM β ε x) (bM β ε ⟨t₀, ht₀12⟩) :=
      burnsideF4j_F_4_35_forward hyp x ⟨t₀, ht₀12⟩ hxS ht₀S hsame
    rw [hxe] at hc
    obtain ⟨c', hc'⟩ := isConj_iff.mp ((hgc g).symm.trans hc)
    exact key c' hc'

end Main

end CFSG.ASVolI
