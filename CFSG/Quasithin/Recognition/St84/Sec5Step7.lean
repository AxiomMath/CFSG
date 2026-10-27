module

public import CFSG.Quasithin.Recognition.St84.Sec5Step46
public import CFSG.Quasithin.SteinbergCDIndexThreeTripleCores
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

private theorem isMaxRegLen_reverse (Y : Setup Γ G) {r : ℕ} (hr : Y.IsMaxRegLen r) :
    Y.reverse.IsMaxRegLen r := by
  obtain ⟨⟨a, hL, hR⟩, hmax⟩ := hr
  refine ⟨⟨-(a + (r : ℤ)), ?_, ?_⟩, ?_⟩
  · rw [show -(a + (r : ℤ)) + (r : ℤ) = -a by ring]
    intro b c hbm hbn hcm hcn
    have hbm' : Γ.Adj (Y.vert (a + (r : ℤ))) b := by
      simpa [Setup.reverse_vert] using hbm
    have hbn' : b ≠ Y.vert (a + (r : ℤ) - 1) := by
      intro h
      apply hbn
      rw [Setup.reverse_vert, h]
      congr 1
      ring
    have hcm' : Γ.Adj (Y.vert (a + (r : ℤ))) c := by
      simpa [Setup.reverse_vert] using hcm
    have hcn' : c ≠ Y.vert (a + (r : ℤ) - 1) := by
      intro h
      apply hcn
      rw [Setup.reverse_vert, h]
      congr 1
      ring
    obtain ⟨g, hg, hgc⟩ := hR b c hbm' hbn' hcm' hcn'
    refine ⟨g, ?_, hgc⟩
    rw [Setup.reverse_arcStab]
    simpa using hg
  · rw [show -(a + (r : ℤ)) + (r : ℤ) = -a by ring]
    intro b c hbm hbn hcm hcn
    have hbm' : Γ.Adj (Y.vert a) b := by
      simpa [Setup.reverse_vert] using hbm
    have hbn' : b ≠ Y.vert (a + 1) := by
      intro h
      apply hbn
      rw [Setup.reverse_vert, h]
      congr 1
      ring
    have hcm' : Γ.Adj (Y.vert a) c := by
      simpa [Setup.reverse_vert] using hcm
    have hcn' : c ≠ Y.vert (a + 1) := by
      intro h
      apply hcn
      rw [Setup.reverse_vert, h]
      congr 1
      ring
    obtain ⟨g, hg, hgc⟩ := hL b c hbm' hbn' hcm' hcn'
    refine ⟨g, ?_, hgc⟩
    rw [Setup.reverse_arcStab]
    simpa using hg
  · intro c k hk
    rw [Setup.reverse_arcStab, Setup.reverse_GT]
    have h := hmax (-(c + (k : ℤ))) k hk
    rwa [show -(c + (k : ℤ)) + (k : ℤ) = -c by ring] at h

private theorem card_inf_centralizer_K_le_four (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) ≤ 4 := by
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  have hcent4 : Nat.card (centerOf (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) ≤ 4 :=
    (goldschmidt_small_apply Y H hdJ hd3).2.2.1
  haveI : Finite ↥Y.K := finite_of_le_stabilizer Y.hyp (Y.K_le_Gi 0)
  have hKne : Y.K ≠ ⊥ := Y.K_ne_bot H
  haveI hKnt : Nontrivial ↥Y.K := (Subgroup.nontrivial_iff_ne_bot Y.K).mpr hKne
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥Y.K)
  have hkx : (x : G) ∈ Y.K := x.2
  have hkx1 : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hStQ : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Q 0 := by
    intro e he
    obtain ⟨heS, heC⟩ := Subgroup.mem_inf.mp he
    have hcomm : ⁅e, (x : G)⁆ = 1 := by
      have hk : (x : G) * e = e * (x : G) :=
        Subgroup.mem_centralizer_iff.mp heC (x : G) hkx
      rw [commutatorElement_def, ← hk]
      group
    exact Y.K_fixFree_S H hkx hkx1 e heS (by rw [hcomm]; exact (Y.Q 0).one_mem)
  have hWSt : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
    le_inf (((inf_le_left : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Z 0).trans
      (Y.Z_le_Q 0)).trans (Y.Q_le_edgeSylow_left 0)) inf_le_right
  have hWcent : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Subgroup.centralizer
      ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
    refine (inf_le_left : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Z 0).trans ?_
    refine ((Y.Z_le_center 0).trans inf_le_right).trans ?_
    exact Subgroup.centralizer_le hStQ
  have hWleCenter : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      centerOf (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) := by
    rw [centerOf]
    exact le_inf hWSt hWcent
  haveI hCenterFin : Finite ↥(centerOf (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 0) (H := _)
      (inf_le_left.trans (inf_le_left.trans
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.Gi 0 ⊓ Y.Gi 1)).trans inf_le_left)))
  exact (Subgroup.card_le_of_le hWleCenter).trans hcent4

private theorem inf_centralizer_eq_sup_of_not_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (he : Y.ZtExt 0 r₀ r₀)
    (h6 : ⁅Y.Zt 0, Y.Zt r₀⁆ ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G))
    (hZ1R : ¬ Y.Z 1 ≤ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) :
    Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) =
      Y.Z 1 ⊔ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ := by
  have hZ1card : Nat.card (Y.Z 1) = 2 := (s52_step4 Y H hZ h3).2
  have hZ1W : Y.Z 1 ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := Z_one_le Y H hZ h3
  have hRZ0 : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z 0 := h6.trans inf_le_left
  have hRCK : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Subgroup.centralizer (Y.K : Set G) :=
    h6.trans inf_le_right
  have hRW : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) :=
    le_inf hRZ0 hRCK
  have hRne : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≠ ⊥ := comm_Zt_ne_bot_of_ZtExt Y H hZ he
  have hZ1fin : Finite ↥(Y.Z 1) := finite_of_le_stabilizer Y.hyp (Y.Z_le_Gi 1)
  have hZ1Rfin : Finite ↥(Y.Z 1 ⊓ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) :=
    finite_of_le_stabilizer Y.hyp (inf_le_left.trans (Y.Z_le_Gi 1))
  have hZ1Rbot : Y.Z 1 ⊓ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ = ⊥ := by
    have hlt : Y.Z 1 ⊓ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ < Y.Z 1 := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      exact hZ1R (h ▸ inf_le_right)
    have hcard : Nat.card ↥(Y.Z 1 ⊓ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) <
        Nat.card ↥(Y.Z 1) := Subgroup.card_lt_of_lt hlt
    rw [hZ1card] at hcard
    have hpos := Nat.card_pos (α := ↥(Y.Z 1 ⊓ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆))
    exact Subgroup.eq_bot_of_card_eq _ (by omega)
  have hRC : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Subgroup.centralizer (Y.Z 1 : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Y.Z_commute 0 r (hRZ0 hr) z ((Subgroup.mem_inf.mp (hZ1W hz)).1)).symm
  have hRN : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Subgroup.normalizer (Y.Z 1 : Set G) :=
    hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hsupcard : Nat.card ↥(Y.Z 1 ⊔ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) =
      2 * Nat.card ↥⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ := by
    have h :=
      CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_sup_mul_card_inf_of_le_normalizer
        (L := Y.Z 1) (E := ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) hRN
    rw [hZ1Rbot, Subgroup.card_bot, mul_one, hZ1card] at h
    exact h
  have hRfin : Finite ↥⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ :=
    finite_of_le_stabilizer Y.hyp (hRZ0.trans (Y.Z_le_Gi 0))
  have hRcard : 2 ≤ Nat.card ↥⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ := by
    have := (Subgroup.one_lt_card_iff_ne_bot ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆).mpr hRne
    omega
  have hWfin : Finite ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (inf_le_left.trans (Y.Z_le_Gi 0))
  have hSupFin : Finite ↥(Y.Z 1 ⊔ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) :=
    finite_of_le_stabilizer Y.hyp ((sup_le hZ1W hRW).trans (inf_le_left.trans (Y.Z_le_Gi 0)))
  have hWRsup : Y.Z 1 ⊔ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤
      Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := sup_le hZ1W hRW
  refine (Subgroup.eq_of_le_of_card_ge hWRsup ?_).symm
  have hle : Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) ≤
      Nat.card ↥(Y.Z 1 ⊔ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) := by
    rw [hsupcard]
    have := card_inf_centralizer_K_le_four Y H
    omega
  exact hle

private theorem Zt_le_Q_one (Y : Setup Γ G) {r₀ : ℕ}
    (he : Y.ZtExt 0 r₀ r₀) (heven : Even r₀) (hr0 : 1 ≤ r₀) :
    Y.Zt (r₀ : ℤ) ≤ Y.Q 1 := by
  obtain ⟨m, hm⟩ := heven
  have hcast : (r₀ : ℤ) = 2 * (m : ℤ) := by
    have h : (r₀ : ℤ) = (m : ℤ) + (m : ℤ) := by exact_mod_cast hm
    linarith
  have hZtr0G0 : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := he.Zt_le_Gi_zero ⟨m, hm⟩
  have hZtr0G1 : Y.Zt (r₀ : ℤ) ≤ Y.Gi 1 := by
    have h := he.Zt_two_mul_le_Gi (m : ℤ) (1 - (r₀ : ℤ))
      (by omega) (by omega)
    rw [show 2 * (m : ℤ) + (1 - (r₀ : ℤ)) = 1 by linarith, ← hcast] at h
    exact h
  have hZtr0G2 : Y.Zt (r₀ : ℤ) ≤ Y.Gi 2 := by
    have h := he.Zt_two_mul_le_Gi (m : ℤ) (2 - (r₀ : ℤ))
      (by omega) (by omega)
    rw [show 2 * (m : ℤ) + (2 - (r₀ : ℤ)) = 2 by linarith, ← hcast] at h
    exact h
  have hZtr0pg : IsPGroup 2 (Y.Zt (r₀ : ℤ)) := Y.isPGroup_Zt (r₀ : ℤ)
  have h := le_pCoreOf_of_isPGroup_fixes_two Y.hyp hZtr0pg (α := Y.vert 1) hZtr0G1
    (a := Y.vert 0) (b := Y.vert 2) (Y.adj 0).symm (Y.adj 1)
    (by
      intro h
      have := Y.vert_injective h
      omega)
    (fun y hy => MulAction.mem_stabilizer_iff.mp (hZtr0G0 hy))
    (fun y hy => MulAction.mem_stabilizer_iff.mp (hZtr0G2 hy))
  simpa [Setup.Q] using h

private theorem comm_Zt_le_inf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hext : Y.ZtExt 0 r₀ r₀)
    (h6 : ⁅Y.Zt 0, Y.Zt r₀⁆ ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G))
    (hWCZt : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G)) :
    ∀ z ∈ Y.Z 0, ∀ e ∈ Y.Zt (r₀ : ℤ), ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ) := by
  intro z hz e he
  have hWleZ : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Z 0 := inf_le_left
  have hRZ0 : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z 0 := h6.trans inf_le_left
  have hRZr : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z (r₀ : ℤ) := comm_Zt_Zt_le_Z Y hext
  have hZ0eq : Y.Z 0 = (Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.Zt 0 :=
    (Zt_eq Y H 0).1
  have hZt0C : Y.Zt 0 ≤ Subgroup.centralizer
      ((Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Y.Z_commute 0 t (Zt_le_Z Y 0 ht) w (hWleZ hw)).symm
  have hZt0N : Y.Zt 0 ≤ Subgroup.normalizer
      ((Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) :=
    hZt0C.trans (Subgroup.centralizer_le_normalizer _)
  have hz' : z ∈ (Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.Zt 0 := hZ0eq ▸ hz
  obtain ⟨w, hwW, t, htZt, hwt⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hZt0N).mp hz'
  replace hwt := hwt.symm
  have hwZ : w ∈ Y.Z 0 := hWleZ hwW
  have hwe : w * e = e * w :=
    (Subgroup.mem_centralizer_iff.mp (hWCZt hwW) e he).symm
  have hwe1 : ⁅w, e⁆ = 1 := by
    rw [commutatorElement_def, hwe]
    group
  have hteR : ⁅t, e⁆ ∈ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ :=
    Subgroup.commutator_mem_commutator htZt he
  have hw_hte : w * ⁅t, e⁆ * w⁻¹ = ⁅t, e⁆ := by
    have hmemZ : ⁅t, e⁆ ∈ Y.Z 0 := hRZ0 hteR
    calc w * ⁅t, e⁆ * w⁻¹ = ⁅t, e⁆ * w * w⁻¹ := by
          rw [Y.Z_commute 0 w hwZ ⁅t, e⁆ hmemZ]
      _ = ⁅t, e⁆ := by group
  have hfinal : ⁅w * t, e⁆ = ⁅t, e⁆ := by
    have hsplit : ⁅w * t, e⁆ = w * ⁅t, e⁆ * w⁻¹ * ⁅w, e⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hsplit, hw_hte, hwe1, mul_one]
  rw [← hwt, hfinal]
  exact Subgroup.mem_inf.mpr ⟨hRZ0 hteR, hRZr hteR⟩

private theorem false_of_Z_one_le_comm_Zt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (h3 : Y.Zt 1 = ⊥) (hr : Y.IsMaxRegLen r) (he : Y.ZtExt 0 r₀ r₀)
    (h2 : Y.Step2Conclusion s r r₀)
    (heven : Even r₀) (hZ1card : Nat.card (Y.Z 1) = 2)
    (hZt0G3 : Y.Zt 0 ≤ Y.Gi 3) (hZ2 : Y.Z 0 ≤ Y.Gi 2)
    (hZ1R : Y.Z 1 ≤ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) : False := by
  set W : Subgroup G := Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) with hWdef
  have hWleZ : W ≤ Y.Z 0 := inf_le_left
  have hWQ0 : W ≤ Y.Q 0 := hWleZ.trans (Y.Z_le_Q 0)
  have hWpg : IsPGroup 2 W := (pCoreOf_isPGroup' (Y.Gi 0)).to_le hWQ0
  have hWK : ⁅W, Y.K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hWQ2 : W ≤ Y.Q 2 :=
    le_Q_of_comm_K_eq_bot Y H (j := 2) (by norm_num) (hWleZ.trans hZ2) hWpg hWK
  have hQ2G3 : Y.Q 2 ≤ Y.Gi 3 := by
    intro x hx
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 2 (Y.vert 3) (Y.adj 2) x hx)
  have hZ0G3 : Y.Z 0 ≤ Y.Gi 3 := by
    rw [(Zt_eq Y H 0).1]
    exact sup_le (hWQ2.trans hQ2G3) hZt0G3
  obtain ⟨m, hm⟩ := heven
  have hcast : (r₀ : ℤ) = 2 * (m : ℤ) := by
    have h : (r₀ : ℤ) = (m : ℤ) + (m : ℤ) := by exact_mod_cast hm
    linarith
  have hZrG : Y.Z (r₀ : ℤ) ≤ Y.Gi ((r₀ : ℤ) + 3) := by
    have hZ : Y.Z (r₀ : ℤ) = conjSub (Y.τ ^ (m : ℤ)) (Y.Z 0) := by
      rw [show (r₀ : ℤ) = 0 + 2 * (m : ℤ) by rw [hcast]; ring, Y.Z_add]
    have hG : Y.Gi ((r₀ : ℤ) + 3) = conjSub (Y.τ ^ (m : ℤ)) (Y.Gi 3) := by
      rw [show (r₀ : ℤ) + 3 = 3 + 2 * (m : ℤ) by rw [hcast]; ring, Y.Gi_add]
    rw [hZ, hG]
    exact conjSub_mono _ hZ0G3
  have hRZr : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z (r₀ : ℤ) := comm_Zt_Zt_le_Z Y he
  have hZ1G3 : Y.Z 1 ≤ Y.Gi ((r₀ : ℤ) + 3) := hZ1R.trans (hRZr.trans hZrG)
  have hK1 : ⁅Y.Z 1, Y.K⁆ = ⊥ := by simpa [Setup.Zt] using h3
  have hZ1neg : Y.Z 1 ≤ Y.Gi (-(r₀ : ℤ) - 1) := by
    have hstep : Y.Z 1 ≤ Y.Gi (1 + ((r₀ : ℤ) + 2)) := by
      rwa [show (1 : ℤ) + ((r₀ : ℤ) + 2) = (r₀ : ℤ) + 3 by ring]
    have h := (Y.Z_fix_symm H 1 hK1 ((r₀ : ℤ) + 2)).mp hstep
    rwa [show (1 : ℤ) - ((r₀ : ℤ) + 2) = -(r₀ : ℤ) - 1 by ring] at h
  have hZ1arc : Y.Z 1 ≤ Y.arcStab (-(r₀ : ℤ) - 1) ((r₀ : ℤ) + 3) := by
    rw [Y.arcStab_eq_inf (by linarith)]
    exact le_inf hZ1neg hZ1G3
  have hGT : Y.arcStab (-(r₀ : ℤ) - 1) ((r₀ : ℤ) + 3) = Y.GT := by
    have hr2 : r ≤ 2 * r₀ + 2 := by
      rcases h2 with h | h | h <;> omega
    have hlt : r < 2 * r₀ + 4 := by omega
    have h := hr.2 (-(r₀ : ℤ) - 1) (2 * r₀ + 4) hlt
    rwa [show -(r₀ : ℤ) - 1 + ((2 * r₀ + 4 : ℕ) : ℤ) = (r₀ : ℤ) + 3 by
      push_cast; ring] at h
  have hZ1GT : Y.Z 1 ≤ Y.GT := hGT ▸ hZ1arc
  haveI : Finite ↥Y.GT := finite_of_le_stabilizer Y.hyp (Y.GT_le_Gi 0)
  have hdvd : Nat.card ↥(Y.Z 1) ∣ Nat.card ↥Y.GT := Subgroup.card_dvd_of_le hZ1GT
  rw [hZ1card] at hdvd
  exact (Nat.not_even_iff_odd.mpr H.odd_GT) (even_iff_two_dvd.mpr hdvd)

private theorem false_of_not_Z_one_le_comm_Zt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (he : Y.ZtExt 0 r₀ r₀)
    (heven : Even r₀) (hr0 : 1 ≤ r₀)
    (h6 : ⁅Y.Zt 0, Y.Zt r₀⁆ ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G))
    (hHQ : HigmanQuad n₀) (hZ1R : ¬ Y.Z 1 ≤ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆) : False := by
  have hWsup := inf_centralizer_eq_sup_of_not_le Y H hZ h3 he h6 hZ1R
  have hZtr0Q1 : Y.Zt (r₀ : ℤ) ≤ Y.Q 1 := Zt_le_Q_one Y he heven hr0
  have hQ1L1 : Y.Q 1 ≤ Y.L 1 := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le
  have hZ1CQ1 : Y.Z 1 ≤ Subgroup.centralizer (Y.Q 1 : Set G) := by
    rw [(s52_step4 Y H hZ h3).1]
    exact (inf_le_right : centerOf (Y.L 1) ≤ _).trans (Subgroup.centralizer_le hQ1L1)
  have hRZr : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z (r₀ : ℤ) := comm_Zt_Zt_le_Z Y he
  have hR_CZt : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤
      Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Y.Z_commute (r₀ : ℤ) r (hRZr hr) e (Zt_le_Z Y (r₀ : ℤ) he)).symm
  have hWCZt : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) := by
    rw [hWsup]
    exact sup_le (hZ1CQ1.trans (Subgroup.centralizer_le hZtr0Q1)) hR_CZt
  exact false_of_comm_Zt_le Y H hZ h3 he hHQ (comm_Zt_le_inf Y H he h6 hWCZt)

private theorem step7_right (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (hr : Y.IsMaxRegLen r)
    (he : Y.ZtExt 0 r₀ r₀) (h2 : Y.Step2Conclusion s r r₀)
    (h5 : ¬ Y.Z 0 ≤ Y.Gi (r₀ : ℤ) ∧ ¬ Y.Z 0 ≤ Y.Gi (-(r₀ : ℤ)))
    (h6 : ⁅Y.Zt 0, Y.Zt r₀⁆ ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G))
    (hHQ : HigmanQuad n₀) : ¬ Y.Z 0 ≤ Y.Gi 2 := by
  intro hZ2
  have heven : Even r₀ := (s52_step1 Y H hZ he).2
  have hr0pos : 1 ≤ r₀ := by
    rcases Nat.eq_zero_or_pos r₀ with h | h
    · exfalso
      apply he.2.1
      subst h
      refine (Zt_le_Z Y 0).trans ((Y.Z_le_Q 0).trans ?_)
      intro x hx
      exact MulAction.mem_stabilizer_iff.mpr
        (Y.Q_fixes_neighbors_vert 0 (Y.vert 1) (Y.adj 0) x hx)
    · exact h
  have hr0ge2 : 2 ≤ r₀ := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hZ1card : Nat.card (Y.Z 1) = 2 := (s52_step4 Y H hZ h3).2
  have hr0ne2 : r₀ ≠ 2 := by
    intro h
    exact h5.1 (by simpa [h] using hZ2)
  have hr0ge4 : 4 ≤ r₀ := by
    have hgt : 2 < r₀ := lt_of_le_of_ne hr0ge2 (Ne.symm hr0ne2)
    obtain ⟨k, hk⟩ := heven
    omega
  have hZt0G3 : Y.Zt 0 ≤ Y.Gi 3 := by
    have h := he.1 3 (by linarith) (by omega)
    simpa using h
  by_cases hZ1R : Y.Z 1 ≤ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆
  · exact false_of_Z_one_le_comm_Zt Y H h3 hr he h2 heven hZ1card hZt0G3 hZ2 hZ1R
  · exact false_of_not_Z_one_le_comm_Zt Y H hZ h3 he heven (by omega) h6 hHQ hZ1R

theorem s52_step7 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hr : Y.IsMaxRegLen r) (he : Y.ZtExt 0 r₀ r₀)
    (h2 : Y.Step2Conclusion s r r₀)
    (h5 : ¬ Y.Z 0 ≤ Y.Gi (r₀ : ℤ) ∧ ¬ Y.Z 0 ≤ Y.Gi (-(r₀ : ℤ)))
    (h6 : ⁅Y.Zt 0, Y.Zt r₀⁆ ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G))
    (hHQ : HigmanQuad n₀) : Y.HasB 0 1 := by
  have hW2 : ¬ Y.Z 0 ≤ Y.Gi 2 := step7_right Y H hZ h3 hr he h2 h5 h6 hHQ
  have hQ0Gi1 : Y.Q 0 ≤ Y.Gi 1 := by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 0 (Y.vert 1) (Y.adj 0) q hq)
  have hQ0GiNeg1 : Y.Q 0 ≤ Y.Gi (-1) := by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 0 (Y.vert (-1)) (by simpa using (Y.adj (-1)).symm) q hq)
  have hZr : Y.reverse.Zt 0 ≠ ⊥ := by
    rw [Setup.reverse_Zt]
    simpa using hZ
  have h3rev : Y.reverse.Zt 1 = ⊥ := by
    rw [Setup.reverse_Zt]
    have h := Zt_add_two Y 1 (-1)
    rw [show (1 : ℤ) + 2 * (-1) = -1 by ring] at h
    rw [h, h3, Subgroup.map_bot]
  have herev : Y.reverse.ZtExt 0 r₀ r₀ := he.reverse
  have hrrev : Y.reverse.IsMaxRegLen r := isMaxRegLen_reverse Y hr
  have h2rev : Y.reverse.Step2Conclusion s r r₀ :=
    s52_step2 Y.reverse H.reverse hZr hrrev herev
  have h5rev : ¬ Y.reverse.Z 0 ≤ Y.reverse.Gi (r₀ : ℤ) ∧
      ¬ Y.reverse.Z 0 ≤ Y.reverse.Gi (-(r₀ : ℤ)) := by
    constructor
    · simpa using h5.2
    · simpa using h5.1
  have h6rev : ⁅Y.reverse.Zt 0, Y.reverse.Zt r₀⁆ ≤
      Y.reverse.Z 0 ⊓ Subgroup.centralizer (Y.reverse.K : Set G) :=
    s52_step6 Y.reverse H.reverse hZr h3rev hrrev herev h2rev h5rev
  have hWrev : ¬ Y.reverse.Z 0 ≤ Y.reverse.Gi 2 :=
    step7_right Y.reverse H.reverse hZr h3rev hrrev herev h2rev h5rev h6rev hHQ
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hj1 : j ≤ 1 := by
      have h := Int.le_natAbs (a := j)
      omega
    have hj2 : -1 ≤ j := by
      have h := Int.le_natAbs (a := -j)
      rw [Int.natAbs_neg] at h
      omega
    rcases (by omega : j = -1 ∨ j = 0 ∨ j = 1) with h | h | h
    · subst h
      exact (Y.Z_le_Q 0).trans (by simpa using hQ0GiNeg1)
    · subst h
      simpa using Y.Z_le_Gi 0
    · subst h
      exact (Y.Z_le_Q 0).trans (by simpa using hQ0Gi1)
  · simpa using hW2
  · simpa using hWrev

private theorem eq_one_of_isL2Quot_of_card {P N : Type*} [Group P] [Finite P] [Group N]
    [Finite N] {n f : ℕ} (hn : 2 ≤ n) (hfn : f < 2 * n)
    (hL : IsL2Quot n P) (ρ : P →* MulAut N) (hN : Nat.card N = 2 ^ f) : ρ = 1 := by
  obtain ⟨e⟩ := hL
  let π : P →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.toMonoidHom
  have hπinj : Function.Injective π := e.injective
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hπs : Function.Surjective π := e.surjective
  have : (ρ.ker.map π).Normal := (MonoidHom.normal_ker ρ).map π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π) with hb | ht
  ·
    have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hxm : π x ∈ ρ.ker.map π := ⟨x, hx, rfl⟩
      rw [hb] at hxm
      have hx0 : π x = 1 := Subgroup.mem_bot.mp hxm
      apply e.injective
      rw [map_one]
      simpa [π] using hx0
    by_cases hn3 : n = 3
    · subst hn3
      have := CGT.Timmesfeld75.lemma27_psl2_eight π hπs ρ hρinj hN
      omega
    · have hcard : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card P := by
        rw [Nat.card_congr e.toEquiv, card_psl_two_gf2 n (by omega)]
        rw [show (2 ^ n) ^ 2 = 4 ^ n by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num]
      have := CGT.Timmesfeld75.lemma27_psl2 hn hn3 hcard ρ hρinj hN
      omega
  ·
    have hkertop : ρ.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxm : π x ∈ ρ.ker.map π := by rw [ht]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hxm
      have hkx' : k = x := hπinj hkx
      simpa [hkx'] using hk
    refine MonoidHom.ext fun x => ?_
    have hx : ρ x = 1 := by
      have hmem : x ∈ ρ.ker := by rw [hkertop]; exact Subgroup.mem_top x
      simpa using hmem
    exact hx

private theorem Z_zero_le_centralizer_Q_zero (Y : Setup Γ G) :
    Y.Z 0 ≤ Subgroup.centralizer (Y.Q 0 : Set G) :=
  (Y.Z_le_center 0).trans inf_le_right

private theorem Q_zero_le_centralizer_Z_zero (Y : Setup Γ G) :
    Y.Q 0 ≤ Subgroup.centralizer (Y.Z 0 : Set G) :=
  Subgroup.le_centralizer_iff.mp (Z_zero_le_centralizer_Q_zero Y)

private theorem Zt_eq_bot_of_le_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h : Y.L 0 ≤ Subgroup.centralizer (Y.Z 0 : Set G)) : Y.Zt 0 = ⊥ := by
  rw [Setup.Zt, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact ((Subgroup.mem_centralizer_iff.mp (h (Y.K_le_L_zero H hk))) z hz).symm

private theorem notNatSec_of_n0_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (hn₀ : n₀ = 2) :
    ¬ NatSec (Y.L 0) ⊥ (Y.Z 0) := by
  obtain ⟨k, hkK, hkord⟩ := Y.exists_orderOf_three_K H hn₀
  have hkL : k ∈ Y.L 0 := Y.K_le_L_zero H hkK
  have hZ1card : Nat.card (Y.Z 1) = 2 := (s52_step4 Y H hZ h3).2
  have hZ1le : Y.Z 1 ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := Z_one_le Y H hZ h3
  haveI : Finite ↥(Y.Z 1) := finite_of_le_stabilizer Y.hyp (H := Y.Z 1) (Y.Z_le_Gi 1)
  haveI : Nontrivial ↥(Y.Z 1) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ1card]; norm_num)
  obtain ⟨z, hzne⟩ := exists_ne (1 : ↥(Y.Z 1))
  have hz0 : (z : G) ∈ Y.Z 0 := (hZ1le z.2).1
  have hzcent : (z : G) ∈ Subgroup.centralizer (Y.K : Set G) := (hZ1le z.2).2
  have hzk : ⁅(z : G), k⁆ = 1 :=
    Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hzcent k hkK
  intro hsec
  have hff : FixFree (⊥ : Subgroup G) (Y.Z 0) k := hsec k hkL hkord
  have hmem : (z : G) ∈ (⊥ : Subgroup G) := by
    refine hff (z : G) hz0 ?_
    rw [hzk]
    exact Subgroup.one_mem ⊥
  exact hzne (Subtype.ext (Subgroup.mem_bot.mp hmem))

private theorem Q_one_le_normalizer_Q_zero_inf_Q_two (Y : Setup Γ G) :
    Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
  intro q hq
  have hq0 : q ∈ Subgroup.normalizer ((Y.Q 0 : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0)
      ((Y.Q_le_Gi_adj 1 hq).1)
  have hq2 : q ∈ Subgroup.normalizer ((Y.Q 2 : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 2)
      ((Y.Q_le_Gi_adj 1 hq).2)
  rw [Subgroup.mem_normalizer_iff] at hq0 hq2 ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun hx => ⟨(hq0 x).mp hx.1, (hq2 x).mp hx.2⟩,
    fun hx => ⟨(hq0 x).mpr hx.1, (hq2 x).mpr hx.2⟩⟩

private theorem le_normalizer_inf_centralizer {G : Type*} [Group G] {L A : Subgroup G}
    (h : L ≤ Subgroup.normalizer (A : Set G)) :
    L ≤ Subgroup.normalizer (L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have hconj : ∀ l ∈ L, ∀ c ∈ L ⊓ Subgroup.centralizer (A : Set G),
      l * c * l⁻¹ ∈ L ⊓ Subgroup.centralizer (A : Set G) := by
    intro l hl c hc
    obtain ⟨hcL, hccent⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact L.mul_mem (L.mul_mem hl hcL) (L.inv_mem hl)
    · rw [Subgroup.mem_centralizer_iff] at hccent ⊢
      intro a ha
      have hla : l⁻¹ * a * l ∈ A := by
        have hlN : l ∈ Subgroup.normalizer (A : Set G) := h hl
        rw [Subgroup.mem_normalizer_iff''] at hlN
        exact (hlN a).mp ha
      calc a * (l * c * l⁻¹) = l * (l⁻¹ * a * l) * c * l⁻¹ := by group
        _ = l * ((l⁻¹ * a * l) * c) * l⁻¹ := by group
        _ = l * (c * (l⁻¹ * a * l)) * l⁻¹ := by rw [hccent (l⁻¹ * a * l) hla]
        _ = (l * c * l⁻¹) * a := by group
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact hconj l hl c
  · intro hc
    have h' := hconj l⁻¹ (L.inv_mem hl) (l * c * l⁻¹) hc
    rwa [show l⁻¹ * (l * c * l⁻¹) * (l⁻¹)⁻¹ = c by group] at h'

private theorem exists_two_pow_mem_inf_centralizer (Y : Setup Γ G)
    (hL : Y.L 1 ≤ Y.Z 0 ⊔ Y.Z 2 ⊔ Y.Q 1)
    (hQ1N : Y.Q 1 ≤ Subgroup.normalizer ((Y.Z 0 ⊔ Y.Z 2 : Subgroup G) : Set G))
    (hZ0 : Y.Z 0 ≤ Subgroup.centralizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G))
    (hZ2 : Y.Z 2 ≤ Subgroup.centralizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G))
    (hLC : Y.L 1 ≤ Subgroup.normalizer
      ((Y.L 1 ⊓ Subgroup.centralizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) :
        Subgroup G) : Set G)) :
    ∀ g ∈ Y.L 1, ∃ k : ℕ,
      g ^ 2 ^ k ∈ (Y.L 1 ⊓ Subgroup.centralizer
        ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) : Subgroup G) := by
  have hQleL : Y.Q 1 ≤ Y.L 1 := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le
  have hQpg : IsPGroup 2 (Y.Q 1) := pCoreOf_isPGroup' (Y.Gi 1)
  intro g hg
  obtain ⟨a, ha, q, hq, haq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQ1N).mp (hL hg)
  replace haq := haq.symm
  have haC : a ∈ (Y.L 1 ⊓ Subgroup.centralizer
      ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) : Subgroup G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have haeq : a = g * q⁻¹ := by rw [← haq]; group
      rw [haeq]
      exact (Y.L 1).mul_mem hg ((Y.L 1).inv_mem (hQleL hq))
    · exact (sup_le hZ0 hZ2) ha
  obtain ⟨k, hk⟩ := hQpg.exists_pow_pow_eq_one ⟨q, hq⟩
  have hkq : q ^ 2 ^ k = 1 := by simpa using hk
  obtain ⟨c', hc', heq⟩ :=
    CFSG.Quasithin.pow_mul_mem_of_normalizes haC (hLC (hQleL hq)) (2 ^ k)
  exact ⟨k, by rw [← haq, heq, hkq, mul_one]; exact hc'⟩

theorem caseA_normal (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hb : Y.HasB 0 1) :
    Y.L 1 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) ∧
      ⁅Y.Q 0 ⊓ Y.Q 2, pResidualOf 2 (Y.L 1)⁆ = ⊥ := by
  have hL : Y.L 1 ≤ Y.Z 0 ⊔ Y.Z 2 ⊔ Y.Q 1 := L_one_le_sup_of_hasB_one Y H hb
  have hZ0 : Y.Z 0 ≤ Subgroup.centralizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
    refine (Y.Z_le_center 0).trans ?_
    rw [centerOf]
    refine inf_le_right.trans (Subgroup.centralizer_le ?_)
    intro x hx
    exact (Subgroup.mem_inf.mp hx).1
  have hZ2 : Y.Z 2 ≤ Subgroup.centralizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
    refine (Y.Z_le_center 2).trans ?_
    rw [centerOf]
    refine inf_le_right.trans (Subgroup.centralizer_le ?_)
    intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  have hQ1 := Q_one_le_normalizer_Q_zero_inf_Q_two Y
  have hLnorm : Y.L 1 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
    refine hL.trans (sup_le (sup_le ?_ ?_) hQ1)
    · exact hZ0.trans (Subgroup.centralizer_le_normalizer _)
    · exact hZ2.trans (Subgroup.centralizer_le_normalizer _)
  have hLC := le_normalizer_inf_centralizer hLnorm
  have hQ1N : Y.Q 1 ≤ Subgroup.normalizer ((Y.Z 0 ⊔ Y.Z 2 : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub q (Y.Z 0 ⊔ Y.Z 2) = Y.Z 0 ⊔ Y.Z 2
    rw [conjSub_sup, Y.Z_normal 0 q ((Y.Q_le_Gi_adj 1 hq).1),
      Y.Z_normal 2 q ((Y.Q_le_Gi_adj 1 hq).2)]
  have hpow := exists_two_pow_mem_inf_centralizer Y hL hQ1N hZ0 hZ2 hLC
  have hres : pResidualOf 2 (Y.L 1) ≤
      (Y.L 1 ⊓ Subgroup.centralizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) :
        Subgroup G) :=
    CFSG.Quasithin.SteinbergCD.pResidualOf_le_of inf_le_left hLC hpow
  refine ⟨hLnorm, ?_⟩
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hres.trans inf_le_right

theorem caseA_Z_inf_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h4 : Y.Z 1 = centerOf (Y.L 1)) (hb : Y.HasB 0 1) :
    Y.Z 0 ⊓ Y.Q 2 = Y.Z 1 := by
  have hZI : Y.Z 0 ⊓ Y.Z 2 = Y.Z 1 := Z_inf_Z_eq Y H h4 hb
  have hnotQ1 : ¬ Y.Z 0 ≤ Y.Q 1 := fun h =>
    hb.2.1 (h.trans ((Y.Q_le_Gi_adj 1).trans inf_le_right))
  have hle : Y.Z 0 ⊓ Y.Q 2 ≤ Y.Z 2 := Z_zero_inf_Q_two_le_Z_two Y H hnotQ1
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← hZI]
    exact Subgroup.mem_inf.mpr ⟨hx.1, hle hx⟩
  · intro x hx
    rw [← hZI] at hx
    exact Subgroup.mem_inf.mpr ⟨hx.1, Y.Z_le_Q 2 hx.2⟩

private theorem r0_lt_four (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hZtZ : Y.Zt 0 ≤ Y.Z 0) :
    r₀ < 4 := by
  have hZt2 : IsPGroup 2 (Y.Zt 0) := Y.isPGroup_Zt 0
  by_contra hge
  push Not at hge
  have hZtQ2 : Y.Zt 0 ≤ Y.Q 2 := by
    refine le_pCoreOf_of_isPGroup_fixes_two Y.hyp hZt2
      (he.1 2 (by omega) (by omega)) (Y.adj 1).symm (Y.adj 2)
      (by intro h; have := Y.vert_injective h; omega) ?_ ?_
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mp (he.1 1 (by omega) (by omega) hy)
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mp (he.1 3 (by omega) (by omega) hy)
  have hZtZ1 : Y.Zt 0 ≤ Y.Z 1 := by
    rw [← caseA_Z_inf_Q Y H h4 hb]
    exact le_inf hZtZ hZtQ2
  have hZtcent : Y.Zt 0 ≤ Subgroup.centralizer (Y.K : Set G) :=
    hZtZ1.trans (fun x hx => (Z_one_le Y H hZ h3 hx).2)
  have hcomm : ⁅Y.Zt 0, Y.K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZtcent
  exact hZ (by rw [← (Zt_eq Y H 0).2.2]; exact hcomm)

private theorem Z_one_le_Q_one_of_eq_centerOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1)) :
    Y.Z 1 ≤ Y.Q 1 := by
  have hZ1L : Y.Z 1 ≤ Y.L 1 := by
    rw [h4]
    exact inf_le_left
  have hZ1norm : Y.L 1 ≤ Subgroup.normalizer ((Y.Z 1) : Set G) := by
    rw [h4]; exact le_normalizer_centerOf_self (Y.L 1)
  have hZ1pg : IsPGroup 2 (Y.Z 1) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [(s52_step4 Y H hZ h3).2]; norm_num)
  have hN := Y.hyp.isLocL2_oTwoPrime (Y.vert 1)
  have hpc : CFSG.Open.pCoreOf 2 (Y.L 1) = Y.Q 1 := hN.pCoreOf_eq
  rw [← hpc]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZ1L hZ1norm hZ1pg

private theorem edgeSylow_one_le_Q_two_sup (Y : Setup Γ G)
    (hZtnotQ2 : ¬ Y.Zt 0 ≤ Y.Q 2)
    (hA_le_E1 : Y.Z 0 ⊓ Y.Q 1 ≤ Y.edgeSylow 1)
    (hZtA : Y.Zt 0 ≤ Y.Z 0 ⊓ Y.Q 1)
    (hKA : Y.K ≤ Subgroup.normalizer ((Y.Z 0 ⊓ Y.Q 1 : Subgroup G) : Set G)) :
    Y.edgeSylow 1 ≤ Y.Q 2 ⊔ (Y.Z 0 ⊓ Y.Q 1) := by
  intro y hy
  by_cases hyQ : y ∈ Y.Q 2
  · exact Subgroup.mem_sup_left hyQ
  · obtain ⟨x, hxA, hxQ⟩ := Set.not_subset.mp hZtnotQ2
    have hxE1 : x ∈ Y.edgeSylow 1 := hA_le_E1 (hZtA hxA)
    obtain ⟨k, hkK, hkq⟩ := Y.exists_conj_mem_pCoreOf 1 hxE1 hy hxQ hyQ
    have hxkA : k * x * k⁻¹ ∈ Y.Z 0 ⊓ Y.Q 1 := by
      have hN := hKA hkK.1
      exact (Subgroup.mem_normalizer_iff.mp hN x).mp (hZtA hxA)
    have hy_eq : y = (k * x * k⁻¹ * y⁻¹)⁻¹ * (k * x * k⁻¹) := by group
    rw [hy_eq]
    exact Subgroup.mul_mem_sup ((Y.Q 2).inv_mem hkq) hxkA

private theorem card_Z_zero_inf_Q_one_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hAN : Y.Z 0 ⊓ Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 2) : Set G))
    (hSup2 : Y.Q 2 ⊔ (Y.Z 0 ⊓ Y.Q 1) = Y.edgeSylow 1)
    (hBinf : (Y.Q 2 ⊓ (Y.Z 0 ⊓ Y.Q 1) : Subgroup G) = Y.Z 0 ⊓ Y.Q 2) :
    Nat.card ↥(Y.Z 0 ⊓ Y.Q 1 : Subgroup G) =
      2 ^ n₀ * Nat.card ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G) := by
  haveI : Finite ↥(Y.Q 2) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 2) (Y.Q_le_Gi 2)
  have hQ2_le_E1 : Y.Q 2 ≤ Y.edgeSylow 1 := Y.Q_le_edgeSylow_right 2
  have hrelE : (Y.Q 2).relIndex (Y.edgeSylow 1) = 2 ^ n₀ := by
    have hn2 : Y.n (2 : ℤ) = n₀ := by
      rw [show (2 : ℤ) = 0 + 2 * 1 by norm_num, Y.n_add, H.n_zero]
    simpa [hn2] using Y.relIndex_Q_succ_edgeSylow 1
  have hprod :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_sup_mul_card_inf_of_le_normalizer
      (L := Y.Q 2) (E := Y.Z 0 ⊓ Y.Q 1) hAN
  rw [hSup2, hBinf] at hprod
  have hmul := Subgroup.relIndex_mul_card (H := Y.Q 2) (K := Y.edgeSylow 1)
  rw [inf_eq_left.mpr hQ2_le_E1, hrelE] at hmul
  rw [← hmul] at hprod
  have hprod' : (2 ^ n₀ * Nat.card ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G)) * Nat.card (Y.Q 2) =
      Nat.card ↥(Y.Z 0 ⊓ Y.Q 1 : Subgroup G) * Nat.card (Y.Q 2) := by
    calc (2 ^ n₀ * Nat.card ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G)) * Nat.card (Y.Q 2)
        = (2 ^ n₀ * Nat.card (Y.Q 2)) * Nat.card ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G) := by ring
      _ = Nat.card (Y.Q 2) * Nat.card ↥(Y.Z 0 ⊓ Y.Q 1 : Subgroup G) := hprod
      _ = Nat.card ↥(Y.Z 0 ⊓ Y.Q 1 : Subgroup G) * Nat.card (Y.Q 2) := by ring
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hprod').symm

theorem caseA_card_Z (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) :
    r₀ = 2 ∧ Nat.card (Y.Z 0) = 2 ^ (n₀ + 2) := by
  have heven : Even r₀ := (s52_step1 Y H hZ he).2
  have hZtZ : Y.Zt 0 ≤ Y.Z 0 := Zt_le_Z Y 0
  have hZt2 : IsPGroup 2 (Y.Zt 0) := Y.isPGroup_Zt 0
  have hr0pos : 1 ≤ r₀ := by
    rcases Nat.eq_zero_or_pos r₀ with h | h
    · exfalso
      apply he.2.1
      subst h
      refine hZtZ.trans ((Y.Z_le_Q 0).trans ?_)
      intro x hx
      exact MulAction.mem_stabilizer_iff.mpr
        (Y.Q_fixes_neighbors_vert 0 (Y.vert 1) (Y.adj 0) x hx)
    · exact h
  obtain ⟨m, hm⟩ := heven
  have hr0ge2 : 2 ≤ r₀ := by omega
  have hZtQ1 : Y.Zt 0 ≤ Y.Q 1 := by
    refine le_pCoreOf_of_isPGroup_fixes_two Y.hyp hZt2
      (he.1 1 (by omega) (by omega)) (Y.adj 0).symm (Y.adj 1)
      (by intro h; have := Y.vert_injective h; omega) ?_ ?_
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mp (he.1 0 (by omega) (by omega) hy)
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mp (he.1 2 (by omega) (by omega) hy)
  have hZtA : Y.Zt 0 ≤ Y.Z 0 ⊓ Y.Q 1 := le_inf hZtZ hZtQ1
  have hr0lt : r₀ < 4 := r0_lt_four Y H hZ h3 h4 hb he hZtZ
  have hr2 : r₀ = 2 := by omega
  have hZtnotQ2 : ¬ Y.Zt 0 ≤ Y.Q 2 := by
    intro hle
    have hQ2G3 : Y.Q 2 ≤ Y.Gi 3 := by
      intro x hx
      exact MulAction.mem_stabilizer_iff.mpr
        (Y.Q_fixes_neighbors_vert 2 (Y.vert 3) (Y.adj 2) x hx)
    exact he.2.1 (by simpa [hr2] using hle.trans hQ2G3)
  haveI hZ0fin : Finite ↥(Y.Z 0) := finite_of_le_stabilizer Y.hyp (Y.Z_le_Gi 0)
  refine ⟨hr2, ?_⟩
  have hnotQ1 : ¬ Y.Z 0 ≤ Y.Q 1 := by
    intro h
    exact hb.2.1 (h.trans ((Y.Q_le_Gi_adj 1).trans inf_le_right))
  have hArel : (Y.Z 0 ⊓ Y.Q 1).relIndex (Y.Z 0) = 2 :=
    relIndex_Z_zero_inf_Q_one Y H hnotQ1
  have hZ1Q1 : Y.Z 1 ≤ Y.Q 1 := Z_one_le_Q_one_of_eq_centerOf Y H hZ h3 h4
  have hB : Y.Z 0 ⊓ Y.Q 2 = Y.Z 1 := caseA_Z_inf_Q Y H h4 hb
  haveI hBfin : Finite ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G) :=
    Finite.of_injective (fun x : ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G) =>
      (⟨x.1, x.2.1⟩ : ↥(Y.Z 0))) (fun x y h =>
        Subtype.ext (congrArg (fun z : ↥(Y.Z 0) => (z : G)) h))
  have hBcard : Nat.card ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G) = 2 := by
    rw [hB]
    exact (s52_step4 Y H hZ h3).2
  have hBleQ1 : Y.Z 0 ⊓ Y.Q 2 ≤ Y.Q 1 := hB.trans_le hZ1Q1
  have hBleA : Y.Z 0 ⊓ Y.Q 2 ≤ Y.Z 0 ⊓ Y.Q 1 := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hx.1, hBleQ1 hx⟩
  have hA_le_E1 : Y.Z 0 ⊓ Y.Q 1 ≤ Y.edgeSylow 1 :=
    inf_le_right.trans (Y.Q_le_edgeSylow_left 1)
  have hQ2_le_E1 : Y.Q 2 ≤ Y.edgeSylow 1 := Y.Q_le_edgeSylow_right 2
  have hKA : Y.K ≤ Subgroup.normalizer ((Y.Z 0 ⊓ Y.Q 1 : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (Y.Z 0 ⊓ Y.Q 1) = Y.Z 0 ⊓ Y.Q 1
    rw [conjSub_inf, Y.Z_normal 0 k (Y.K_le_Gi 0 hk)]
    have hkQ1 : conjSub k (Y.Q 1) = Y.Q 1 := by
      have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) (Y.K_le_Gi 1 hk)
      simpa [Setup.Q, conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp this)
    rw [hkQ1]
  have hE1_le : Y.edgeSylow 1 ≤ Y.Q 2 ⊔ (Y.Z 0 ⊓ Y.Q 1) :=
    edgeSylow_one_le_Q_two_sup Y hZtnotQ2 hA_le_E1 hZtA hKA
  have hSup2 : Y.Q 2 ⊔ (Y.Z 0 ⊓ Y.Q 1) = Y.edgeSylow 1 :=
    le_antisymm (sup_le hQ2_le_E1 hA_le_E1) hE1_le
  have hAG2 : Y.Z 0 ⊓ Y.Q 1 ≤ Y.Gi 2 := by
    intro x hx
    exact (Y.Q_le_Gi_adj 1 hx.2).2
  have hAN : Y.Z 0 ⊓ Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 2) : Set G) :=
    hAG2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 2))
  have hBinf : (Y.Q 2 ⊓ (Y.Z 0 ⊓ Y.Q 1) : Subgroup G) = Y.Z 0 ⊓ Y.Q 2 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxQ2, hxZ, hxQ1⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxZ, hxQ2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hx.2, Subgroup.mem_inf.mpr ⟨hx.1, hBleQ1 hx⟩⟩
  have hABcard : Nat.card ↥(Y.Z 0 ⊓ Y.Q 1 : Subgroup G) =
      2 ^ n₀ * Nat.card ↥(Y.Z 0 ⊓ Y.Q 2 : Subgroup G) :=
    card_Z_zero_inf_Q_one_eq Y H hAN hSup2 hBinf
  have hBrel : (Y.Z 0 ⊓ Y.Q 2).relIndex (Y.Z 0 ⊓ Y.Q 1) = 2 ^ n₀ := by
    have h := Subgroup.relIndex_mul_card (H := Y.Z 0 ⊓ Y.Q 2) (K := Y.Z 0 ⊓ Y.Q 1)
    rw [inf_eq_left.mpr hBleA] at h
    rw [hABcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hcardZ : Nat.card (Y.Z 0) = 2 ^ (n₀ + 2) := by
    have hmulA := Subgroup.relIndex_mul_card (H := Y.Z 0 ⊓ Y.Q 1) (K := Y.Z 0)
    rw [inf_eq_left.mpr inf_le_left, hArel] at hmulA
    have hmulB := Subgroup.relIndex_mul_card (H := Y.Z 0 ⊓ Y.Q 2) (K := Y.Z 0 ⊓ Y.Q 1)
    rw [inf_eq_left.mpr hBleA, hBrel] at hmulB
    rw [← hmulA, ← hmulB, hBcard]
    rw [pow_add]
    ring
  exact hcardZ

private theorem L_zero_le_centralizer_of_card (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {N : Subgroup G} {f : ℕ} (hNZ : N ≤ Y.Z 0)
    (hN : Y.L 0 ≤ Subgroup.normalizer (N : Set G))
    (hNcard : Nat.card ↥N = 2 ^ f) (hf : f < 2 * n₀) :
    Y.L 0 ≤ Subgroup.centralizer (N : Set G) := by
  haveI : Finite ↥(Y.L 0) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 0)
  haveI : Finite ↥N := finite_of_le_stabilizer Y.hyp (hNZ.trans (Y.Z_le_Gi 0))
  let φ : ↥(Y.L 0) →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom (H := N)).comp (Subgroup.inclusion hN)
  have hQ0ker : CFSG.pCore 2 ↥(Y.L 0) ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun z => ?_
    apply Subtype.ext
    have hxQ : ((x : ↥(Y.L 0)) : G) ∈ Y.Q 0 := by
      have hmap : ((x : ↥(Y.L 0)) : G) ∈ CFSG.Open.pCoreOf 2 (Y.L 0) :=
        Subgroup.mem_map_of_mem _ hx
      rwa [(Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).pCoreOf_eq] at hmap
    have hcent := Y.Q_zero_le_centralizer_Z_zero hxQ
    have hzN : (z : G) ∈ Y.Z 0 := hNZ z.2
    have hcomm : ((x : ↥(Y.L 0)) : G) * (z : G) = (z : G) * ((x : ↥(Y.L 0)) : G) :=
      (Subgroup.mem_centralizer_iff.mp hcent (z : G) hzN).symm
    change ((x : ↥(Y.L 0)) : G) * (z : G) * (((x : ↥(Y.L 0)) : G))⁻¹ = (z : G)
    rw [hcomm]
    group
  let P := oTwoQuot ↥(Y.L 0)
  let ρ : P →* MulAut ↥N := QuotientGroup.lift _ φ hQ0ker
  have hL2 : IsL2Quot n₀ P := by simpa [P] using Y.isL2Quot_L_zero H
  have hρ : ρ = 1 := eq_one_of_isL2Quot_of_card H.two_le hf hL2 ρ hNcard
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hφ : φ ⟨l, hl⟩ = 1 := by
    have h := congrArg (fun f : P →* MulAut ↥N =>
      f (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y.L 0)) ⟨l, hl⟩)) hρ
    have h2 : ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y.L 0)) ⟨l, hl⟩) = φ ⟨l, hl⟩ :=
      QuotientGroup.lift_mk' (φ := φ) (N := CFSG.pCore 2 ↥(Y.L 0)) hQ0ker ⟨l, hl⟩
    rw [h2] at h
    exact h
  have hz' : φ ⟨l, hl⟩ ⟨z, hz⟩ = ⟨z, hz⟩ := by rw [hφ]; rfl
  have hcoe := congrArg (fun w : ↥N => (w : G)) hz'
  have hlr : l * z * l⁻¹ = z := by
    simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] using hcoe
  calc z * l = (l * z * l⁻¹) * l := by rw [hlr]
    _ = l * z := by group

private theorem n0_le_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) : n₀ ≤ 2 := by
  by_contra hn
  have hcardZ : Nat.card ↥(Y.Z 0) = 2 ^ (n₀ + 2) := (caseA_card_Z Y H hZ h3 h4 hb he).2
  have hLZ : Y.L 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub l (Y.Z 0) = Y.Z 0
    exact Y.Z_normal 0 l (Y.L_le_Gi 0 hl)
  exact hZ (Zt_eq_bot_of_le_centralizer Y H
    (L_zero_le_centralizer_of_card Y H le_rfl hLZ hcardZ (by omega)))

private def Ztwo (Y : Setup Γ G) : Subgroup G where
  carrier := {x | x ∈ Y.Z 0 ∧ x ^ 2 = 1}
  one_mem' := ⟨(Y.Z 0).one_mem, one_pow 2⟩
  mul_mem' := by
    rintro a b ⟨haZ, ha2⟩ ⟨hbZ, hb2⟩
    refine ⟨(Y.Z 0).mul_mem haZ hbZ, ?_⟩
    have hcomm : a * b = b * a := Y.Z_commute 0 a haZ b hbZ
    rw [pow_two] at ha2 hb2 ⊢
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm]
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  inv_mem' := by
    rintro a ⟨haZ, ha2⟩
    refine ⟨(Y.Z 0).inv_mem haZ, ?_⟩
    rw [inv_pow, ha2, inv_one]

private def Zsq (Y : Setup Γ G) : Subgroup G where
  carrier := {x | ∃ z ∈ Y.Z 0, z ^ 2 = x}
  one_mem' := ⟨1, (Y.Z 0).one_mem, one_pow 2⟩
  mul_mem' := by
    rintro a b ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨z * w, (Y.Z 0).mul_mem hz hw, ?_⟩
    have hcomm : w * z = z * w := Y.Z_commute 0 w hw z hz
    simp only [pow_two]
    calc z * w * (z * w) = z * (w * z) * w := by group
      _ = z * (z * w) * w := by rw [hcomm]
      _ = z * z * (w * w) := by group
  inv_mem' := by
    rintro a ⟨z, hz, rfl⟩
    exact ⟨z⁻¹, (Y.Z 0).inv_mem hz, inv_pow z 2⟩

private theorem Ztwo_le_Z (Y : Setup Γ G) : Y.Ztwo ≤ Y.Z 0 := fun _ hx => hx.1

private theorem Zsq_le_Z (Y : Setup Γ G) : Y.Zsq ≤ Y.Z 0 := by
  rintro x ⟨z, hz, rfl⟩
  exact (Y.Z 0).pow_mem hz 2

private theorem conj_mem_Z_zero (Y : Setup Γ G) {l x : G} (hl : l ∈ Y.Gi 0)
    (hx : x ∈ Y.Z 0) : l * x * l⁻¹ ∈ Y.Z 0 := by
  have h := Subgroup.mem_map_of_mem (MulAut.conj l).toMonoidHom hx
  rw [show (Y.Z 0).map (MulAut.conj l).toMonoidHom = Y.Z 0 from Y.Z_normal 0 l hl] at h
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

private theorem L_zero_le_normalizer_Ztwo (Y : Setup Γ G) :
    Y.L 0 ≤ Subgroup.normalizer (Y.Ztwo : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxZ, hx2⟩
    refine ⟨conj_mem_Z_zero Y (Y.L_le_Gi 0 hl) hxZ, ?_⟩
    have hpow : (l * x * l⁻¹) ^ 2 = l * x ^ 2 * l⁻¹ := by
      simp only [pow_two]; group
    rw [hpow, hx2]
    group
  · rintro ⟨hxZ, hx2⟩
    have hxZ0 : x ∈ Y.Z 0 := by
      have h := conj_mem_Z_zero Y ((Y.Gi 0).inv_mem (Y.L_le_Gi 0 hl)) hxZ
      have hx_eq : l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x := by group
      rwa [hx_eq] at h
    refine ⟨hxZ0, ?_⟩
    calc x ^ 2 = l⁻¹ * (l * x * l⁻¹) ^ 2 * l := by
          simp only [pow_two]; group
      _ = l⁻¹ * 1 * l := by rw [hx2]
      _ = 1 := by group

private theorem L_zero_le_normalizer_Zsq (Y : Setup Γ G) :
    Y.L 0 ≤ Subgroup.normalizer (Y.Zsq : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨l * z * l⁻¹, conj_mem_Z_zero Y (Y.L_le_Gi 0 hl) hz, ?_⟩
    simp only [pow_two]; group
  · rintro ⟨z, hz, hzx⟩
    refine ⟨l⁻¹ * z * l, ?_, ?_⟩
    · have h := conj_mem_Z_zero Y ((Y.Gi 0).inv_mem (Y.L_le_Gi 0 hl)) hz
      simpa using h
    · calc (l⁻¹ * z * l) ^ 2 = l⁻¹ * z ^ 2 * l := by
            simp only [pow_two]; group
        _ = l⁻¹ * (l * x * l⁻¹) * l := by rw [hzx]
        _ = x := by group

private theorem zpowers_le_centralizer_of_torsion_and_squares (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀)
    (hΩ : Y.L 0 ≤ Subgroup.centralizer (Y.Ztwo : Set G))
    (hM : Y.L 0 ≤ Subgroup.centralizer (Y.Zsq : Set G))
    {k : G} (hkK : k ∈ Y.K) (hkord : orderOf k = 3) :
    Subgroup.zpowers k ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
  have hkL : k ∈ Y.L 0 := Y.K_le_L_zero H hkK
  have hkGi : k ∈ Y.Gi 0 := Y.L_le_Gi 0 hkL
  have hk3 : k ^ 3 = 1 := by rw [← hkord]; exact pow_orderOf_eq_one k
  have hkk : k * k = k⁻¹ := by
    have h : k * (k * k) = 1 := by
      rw [show k * (k * k) = k ^ 3 by rw [pow_succ, pow_two]; group]
      exact hk3
    exact mul_eq_one_iff_eq_inv'.mp h
  have hkinv2 : k⁻¹ * k⁻¹ = k := by
    rw [← mul_inv_rev, hkk, inv_inv]
  refine Subgroup.zpowers_le.mpr ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  set w : G := k * z * k⁻¹ with hwdef
  have hwZ : w ∈ Y.Z 0 := conj_mem_Z_zero Y hkGi hz
  have hw2 : w ^ 2 = z ^ 2 := by
    have hz2M : z ^ 2 ∈ Y.Zsq := ⟨z, hz, rfl⟩
    have hcomm : z ^ 2 * k = k * z ^ 2 :=
      Subgroup.mem_centralizer_iff.mp (hM hkL) (z ^ 2) hz2M
    have hwdef' : w = k * z * k⁻¹ := hwdef
    calc w ^ 2 = k * z ^ 2 * k⁻¹ := by rw [hwdef']; simp only [pow_two]; group
      _ = z ^ 2 * k * k⁻¹ := by rw [← hcomm]
      _ = z ^ 2 := by group
  set ω : G := w * z⁻¹ with hωdef
  have hωZ : ω ∈ Y.Z 0 := (Y.Z 0).mul_mem hwZ ((Y.Z 0).inv_mem hz)
  have hω2 : ω ^ 2 = 1 := by
    have hcomm : w * z⁻¹ = z⁻¹ * w := Y.Z_commute 0 w hwZ z⁻¹ ((Y.Z 0).inv_mem hz)
    calc ω ^ 2 = w * (z⁻¹ * w) * z⁻¹ := by rw [hωdef]; simp only [pow_two]; group
      _ = w * (w * z⁻¹) * z⁻¹ := by rw [← hcomm]
      _ = w ^ 2 * (z⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = z ^ 2 * (z⁻¹) ^ 2 := by rw [hw2]
      _ = 1 := by simp only [pow_two]; group
  have hkω : k * ω * k⁻¹ = ω := by
    have hcomm : ω * k = k * ω :=
      Subgroup.mem_centralizer_iff.mp (hΩ hkL) ω ⟨hωZ, hω2⟩
    rw [← hcomm]
    group
  have hkw : k * w * k⁻¹ = z := by
    have hw : w = ω * z := by rw [hωdef]; group
    calc k * w * k⁻¹ = k * (ω * z) * k⁻¹ := by rw [hw]
      _ = (k * ω * k⁻¹) * (k * z * k⁻¹) := by group
      _ = ω * w := by rw [hkω, hwdef]
      _ = ω * (ω * z) := by rw [hw]
      _ = ω ^ 2 * z := by simp only [pow_two]; group
      _ = z := by rw [hω2, one_mul]
  have hz4 : k⁻¹ * z * k = z := by
    have h2 : k * k * z * (k⁻¹ * k⁻¹) = z := by
      calc k * k * z * (k⁻¹ * k⁻¹) = k * w * k⁻¹ := by rw [hwdef]; group
        _ = z := hkw
    rw [hkk, hkinv2] at h2
    exact h2
  calc z * k = k * (k⁻¹ * z * k) := by group
    _ = k * z := by rw [hz4]

private theorem card_Zsq_lt (Y : Setup Γ G) (hcard16 : Nat.card (Y.Z 0) = 2 ^ 4) :
    Nat.card ↥(Y.Zsq) < 2 ^ 4 := by
  haveI : Finite ↥(Y.Z 0) := finite_of_le_stabilizer Y.hyp (Y.Z_le_Gi 0)
  by_contra hge
  push Not at hge
  have hlecard : Nat.card ↥(Y.Zsq) ≤ Nat.card ↥(Y.Z 0) :=
    Subgroup.card_le_of_le Y.Zsq_le_Z
  rw [hcard16] at hlecard
  have hcard_eq : Nat.card ↥(Y.Zsq) = Nat.card ↥(Y.Z 0) := by
    rw [hcard16]; omega
  have hMeq : Y.Zsq = Y.Z 0 :=
    Subgroup.eq_of_le_of_card_ge Y.Zsq_le_Z (le_of_eq hcard_eq.symm)
  let sq : ↥(Y.Z 0) → ↥(Y.Z 0) :=
    fun z => ⟨(z : G) ^ 2, Y.Zsq_le_Z ⟨(z : G), z.2, rfl⟩⟩
  have hsurj : Function.Surjective sq := by
    intro x
    have hx : (x : G) ∈ Y.Zsq := by rw [hMeq]; exact x.2
    obtain ⟨z, hzz, hzx⟩ := hx
    exact ⟨⟨z, hzz⟩, Subtype.ext hzx⟩
  have hinj : Function.Injective sq := Finite.injective_iff_surjective.mpr hsurj
  have h2dvd : 2 ∣ Nat.card ↥(Y.Z 0) := by rw [hcard16]; norm_num
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Y.Z 0)) 2 h2dvd
  have hxne : x ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  have hx2' : x ^ 2 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hx2 : (x : G) ^ 2 = 1 := by
    have h := congrArg (fun y : ↥(Y.Z 0) => (y : G)) hx2'
    simpa using h
  have hsq1 : sq x = sq 1 := by
    apply Subtype.ext
    simp [sq, hx2]
  exact hxne (hinj hsq1)

private theorem exists_card_eq_two_pow_lt_four (Y : Setup Γ G) {N : Subgroup G} {n : ℕ}
    (hNZ : N ≤ Y.Z 0) (hcard16 : Nat.card (Y.Z 0) = 2 ^ 4)
    (hNlt : Nat.card ↥N < 2 ^ 4) (hn : n = 2) :
    ∃ f : ℕ, Nat.card ↥N = 2 ^ f ∧ f < 2 * n := by
  have hdvd : Nat.card ↥N ∣ 2 ^ 4 := by
    rw [← hcard16]
    exact Subgroup.card_dvd_of_le hNZ
  obtain ⟨f, -, hfc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨f, hfc, ?_⟩
  have hlt : 2 ^ f < 2 ^ 4 := hfc ▸ hNlt
  have hf4 : f < 4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  omega

private theorem isElemAbelian_Z_zero_of_n0_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hn₀ : n₀ = 2) :
    IsElemAbelian 2 (Y.Z 0) := by
  have hcard16 : Nat.card (Y.Z 0) = 2 ^ 4 := by
    calc Nat.card (Y.Z 0) = 2 ^ (n₀ + 2) := (caseA_card_Z Y H hZ h3 h4 hb he).2
      _ = 2 ^ 4 := by rw [hn₀]
  haveI : Finite ↥(Y.Z 0) := finite_of_le_stabilizer Y.hyp (Y.Z_le_Gi 0)
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (Y.Z_commute 0 a a.2 b b.2),
    ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀, hz₀ne⟩ := hcon
  have hΩlt : Nat.card ↥(Y.Ztwo) < 2 ^ 4 := by
    have hlt : Y.Ztwo < Y.Z 0 := by
      refine lt_of_le_of_ne Y.Ztwo_le_Z ?_
      intro heq
      exact hz₀ne ((heq.symm ▸ hz₀ : z₀ ∈ Y.Ztwo).2)
    exact hcard16 ▸ Subgroup.card_lt_of_lt hlt
  have hMlt : Nat.card ↥(Y.Zsq) < 2 ^ 4 := card_Zsq_lt Y hcard16
  obtain ⟨fΩ, hfΩcard, hfΩlt⟩ :=
    exists_card_eq_two_pow_lt_four Y Y.Ztwo_le_Z hcard16 hΩlt hn₀
  obtain ⟨fM, hfMcard, hfMlt⟩ :=
    exists_card_eq_two_pow_lt_four Y Y.Zsq_le_Z hcard16 hMlt hn₀
  have hL0Ω : Y.L 0 ≤ Subgroup.centralizer (Y.Ztwo : Set G) :=
    L_zero_le_centralizer_of_card Y H Y.Ztwo_le_Z (L_zero_le_normalizer_Ztwo Y)
      hfΩcard hfΩlt
  have hL0M : Y.L 0 ≤ Subgroup.centralizer (Y.Zsq : Set G) :=
    L_zero_le_centralizer_of_card Y H Y.Zsq_le_Z (L_zero_le_normalizer_Zsq Y)
      hfMcard hfMlt
  obtain ⟨k, hkK, hkord⟩ := Y.exists_orderOf_three_K H hn₀
  have hkC := zpowers_le_centralizer_of_torsion_and_squares Y H hL0Ω hL0M hkK hkord
  haveI : Finite ↥Y.K := finite_of_le_stabilizer Y.hyp (Y.K_le_Gi 0)
  have hKcard : Nat.card ↥Y.K = 3 := by rw [Y.card_K_eq H, hn₀]; norm_num
  have hKle : Y.K ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
    have hcardz : Nat.card ↥(Subgroup.zpowers k) = Nat.card ↥Y.K := by
      rw [Nat.card_zpowers, hkord, hKcard]
    have hzeq : Subgroup.zpowers k = Y.K :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkK) (le_of_eq hcardz.symm)
    rw [← hzeq]
    exact hkC
  have hZtbot : Y.Zt 0 = ⊥ := by
    rw [Setup.Zt, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    exact (Subgroup.mem_centralizer_iff.mp (hKle hk') z hz).symm
  exact hZ hZtbot

theorem caseA_n (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) :
    n₀ = 2 ∧ IsElemAbelian 2 (Y.Z 0) ∧ Nat.card (Y.Z 0) = 2 ^ 4 ∧
      ¬ NatSec (Y.L 0) ⊥ (Y.Z 0) := by
  have hn0 : n₀ = 2 := le_antisymm (n0_le_two Y H hZ h3 h4 hb he) H.two_le
  exact ⟨hn0, isElemAbelian_Z_zero_of_n0_two Y H hZ h3 h4 hb he hn0, by
    simpa [hn0] using (caseA_card_Z Y H hZ h3 h4 hb he).2,
    notNatSec_of_n0_two Y H hZ h3 hn0⟩

end Setup

end CFSG.Quasithin.St84
