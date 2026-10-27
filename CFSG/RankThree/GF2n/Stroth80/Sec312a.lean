module

public import CFSG.RankThree.GF2n.Stroth80.Sec312SLData
public import CFSG.RankThree.GF2n.Stroth80.Sec312Elat
public import CFSG.RankThree.GF2n.Stroth80.Sec312Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec57B

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

theorem stroth312a_of_311a (h34 : Stroth34Statement)
    (ha : Stroth311aStatement) : Stroth312aStatement := by
  classical
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ 𝓛 hL hcard m hm ⟨K₀, fK₀, finK₀, hK₀, hnat⟩
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  choose! mm hmmM hLeq using fun (L : Subgroup G) (hL' : L ∈ 𝓛) => (hL L hL').1
  have hLt : ∀ L ∈ 𝓛, t ∈ conjSubgroup (mm L) (LB M Q B) := fun L hL' => by
    rw [← hLeq L hL']
    exact (hL L hL').2
  have hLR : ∀ L ∈ 𝓛, L ≤ Rt M (LB M Q B) t := fun L hL' => by
    rw [hLeq L hL']
    exact conjSubgroup_le_Rt (hmmM L hL') (hLt L hL')
  obtain ⟨L₁, h₁, L₂, h₂, h12⟩ := Finset.one_lt_card.mp hcard
  have hR : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro hRL
    apply h12
    have c₁ : Nat.card L₁ = Nat.card (LB M Q B) := by
      rw [hLeq L₁ h₁]
      exact card_conjSubgroup _ _
    have c₂ : Nat.card L₂ = Nat.card (LB M Q B) := by
      rw [hLeq L₂ h₂]
      exact card_conjSubgroup _ _
    have e₁ : L₁ = LB M Q B := Subgroup.eq_of_le_of_card_ge ((hLR L₁ h₁).trans hRL.le) c₁.ge
    have e₂ : L₂ = LB M Q B := Subgroup.eq_of_le_of_card_ge ((hLR L₂ h₂).trans hRL.le) c₂.ge
    exact e₁.trans e₂.symm
  have hV : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n t hs ⟨K₀, fK₀, finK₀, hK₀, m, hm, hnat⟩
  have hN2 : IsPGroup 2 ↥(hc.CN t) :=
    hc.isPGroup_CN_of_311 h34 hs (ha G M Q Z B hc n hw hn hno hgen t ht htQ hR)
  obtain ⟨K, fK, finK, chK, hK, m₁, hm₁, φ, hker, hsec, -, u, hu, hcross⟩ :=
    stroth310SLTransvConj_of_34 h34 G M Q Z B hc n t hs hR hV
  have hmm : m₁ = m := by
    obtain ⟨φ₀, -, -, hsec₀⟩ := hnat
    have hc1 := card_eq_of_sectionAct
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hsec
    have hc2 := card_eq_of_sectionAct
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hsec₀
    rw [hc1] at hc2
    have h3 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hc2
    simp only [Fintype.card_fin] at h3
    rw [hK, hK₀] at h3
    have h4 : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    exact Nat.pow_right_injective h4 h3
  subst hmm
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨k, hk2, hkm, hQS⟩ := elat_quotSat (Rt M (LB M Q B) t) 𝓛 hLR hq4 φ (fun L => u (mm L))
    (fun L hL' => (hu (mm L) (hmmM L hL') (hLt L hL')).1)
    (fun L hL' l hl => by
      have hl' : l ∈ conjSubgroup (mm L) (LB M Q B) := by rw [← hLeq L hL']; exact hl
      exact (hu (mm L) (hmmM L hL') (hLt L hL')).2.1 ⟨l, hLR L hL' hl⟩ hl')
    (fun L hL' f hf => by
      obtain ⟨l, hl, hlf⟩ := (hu (mm L) (hmmM L hL') (hLt L hL')).2.2 f hf
      exact ⟨(l : G), by rw [hLeq L hL']; exact hl, hlf⟩)
    ⟨L₁, h₁, L₂, h₂, fun c hc' => h12 (by
      rw [hLeq L₁ h₁, hLeq L₂ h₂]
      exact hcross (mm L₁) (hmmM L₁ h₁) (mm L₂) (hmmM L₂ h₂) (hLt L₁ h₁) (hLt L₂ h₂) ⟨c, hc'⟩)⟩
    (fun s hsS hs2 => by
      have hker2 : s * s ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul]
        apply Units.ext
        rw [Units.val_mul, Units.val_one]
        exact hs2
      rw [hker, Subgroup.mem_subgroupOf] at hker2
      obtain ⟨j, hj⟩ := hN2 ⟨((s * s : ↥(Rt M (LB M Q B) t)) : G), hker2⟩
      refine ⟨j + 1, ?_⟩
      have hj' : ((s : G) * s) ^ 2 ^ j = 1 := by
        simpa using congrArg (fun z : ↥(hc.CN t) => (z : G)) hj
      rw [pow_succ, pow_mul', pow_two]
      exact hj')
  rw [hK] at hQS
  exact ⟨k, hk2, hkm, hQS⟩

end CFSG.RankThree.GF2n.Stroth80
