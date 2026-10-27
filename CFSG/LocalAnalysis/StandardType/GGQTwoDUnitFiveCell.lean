module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGen
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveSetup
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveLabel
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveUnit
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveFrame
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoord
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShape
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUC
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTableP
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrBA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbr
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTorus
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXTransA
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMember
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Odd
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Edge
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1BaseU
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1LocalO
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPair
import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary Additive


theorem ggQTwoCellInputOn_unit_five (hBal : GGLBalanceInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hRM : GGQTwoRMInputOn fun m => m = 5) :
    GGQTwoCellInputOn (fun m => m = 5) qtwoOrthL.compl := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hcell
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F0, _, _, _, ψ, ε, hbase⟩ := ggQTwoDUnit_base_of_ne_six ggLabelRigidInput_holds hTBF
    hWI hcfg e' (by omega) (by omega) hM hcell
  obtain ⟨βL, ω, hcoords⟩ := ggQTwoDUnit_coords hTBF hWI hcfg e' (by omega) hM hbase
  have hp3 : p = 3 := hbase.p_eq
  subst hp3
  have hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have h3 := qtwo_label_le_three e' hM
  have hC : GGConfig 3 B Bs x L D J := hcfg.1.1.1
  have hBsE : CFSG.Open.IsElemAbelian 3 Bs := hbase.hyp.bstar.2.1
  have hNoTr : GGNoTransvection 3 Bs := hcfg.1.1.2.2.2.1
  have hlt : B < Bs := ggQTwoDUnit_B_lt_Bs hroute (by omega) (by omega) hbase
  have hodd := qtwoDL1_odd_centralizer_of_ne hroute hlt.ne
  have hrefl : ∀ {r : MulAut ↥Bs}, r ∈ ggCoxRefl M e → GGIsReflection 3 r :=
    fun hr => ggCoxRefl_isReflection hpres.2 hr
  obtain ⟨c, b', hb', hb'B, hD, hJ⟩ := qtwoDU5_DJ hcfg hm hbase hcoords
  obtain ⟨a, b, hab, hca, hcb⟩ : ∃ a b : Fin m, a ≠ b ∧ c ≠ a ∧ c ≠ b := by
    subst hm
    exact (by decide : ∀ c : Fin 5, ∃ a b : Fin 5, a ≠ b ∧ c ≠ a ∧ c ≠ b) c
  obtain ⟨α, g, hdel, -⟩ := qtwoDU5_exists_del hcoords hab hca hcb hb'
  obtain ⟨N, hnbr, hJ₁N, hJ₂N, hNc⟩ :=
    qtwoDU5_nbr hBal hcfg hm hM hbase hcoords hodd hdel hb'B hD hJ
  have hNA : ggAutomizer N Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    hRM G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM b' N hnbr
  have hBsN : Bs ≤ Subgroup.normalizer (N : Set G) :=
    ggQTwoDUnit_normalizer_N (by omega) hbase b'.2 hNc hJ₁N
  obtain ⟨hkerΓ, hcardΓ, -, -, -⟩ := qtwoDB36_gamma (by omega) hbase hcoords hdel hNc hJ₁N hJ₂N hBsN
  have hXN : ggAutomizer (qtwoDelJ ψ c ⊔ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom) Bs ≤
      ggAutomizer N Bs := ggAutomizer_mono Bs (sup_le hJ₁N hJ₂N)
  have h192 : 192 ∣ Nat.card ↥(ggAutomizer N Bs) := by
    let S₀ : Subgroup (MulAut ↥Bs) := ggAutomizerJoin L Bs 𝒦 ⊓
      (dEvenStab m (Pi.single c 1)).comap (ggLin (p := 3) βL)
    have hS₀N : S₀ ≤ ggAutomizer N Bs := by
      rintro a' ⟨ha'J, ha'S⟩
      exact hXN (ggQTwoDUnit_weyl_X (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign
        hdel.norm hdel.conj ha'J ha'S.1 ha'S.2 fun s => (ggLin_apply_ofMul βL a' s).symm)
    have hmap : S₀.map (ggLin (p := 3) βL) = dEvenStab m (Pi.single c 1) := by
      refine le_antisymm ?_ fun w hw => ?_
      · rintro w ⟨a', ⟨-, ha'⟩, rfl⟩
        exact ha'
      · obtain ⟨a', ha'J, ha'⟩ := hcoords.join_onto w hw.1
        have hlin : ggLin (p := 3) βL a' = w := LinearEquiv.ext fun v => by
          rw [ggLin_apply, ha']
          simp
        refine ⟨a', ⟨ha'J, ?_⟩, hlin⟩
        change ggLin (p := 3) βL a' ∈ dEvenStab m (Pi.single c 1)
        rw [hlin]
        exact hw
    have hS₀card : Nat.card ↥S₀ = 192 := by
      rw [← Subgroup.card_map_of_injective (ggLin_injective (p := 3) βL), hmap,
        qtwoDB36_card_dEvenStab (by omega) c]
      subst hm
      decide
    rw [← hS₀card]
    exact Subgroup.card_dvd_of_le hS₀N
  have hb'ord : orderOf (b' : G) = 3 := by
    have hb'3 : (b' : G) ^ 3 = 1 := hBsE.2 _ b'.2
    have hb'1 : (b' : G) ≠ 1 := by
      intro h1
      have h1' : b' = 1 := Subtype.ext h1
      have h2 := congrFun hb' c
      rw [h1', ofMul_one, map_zero, Pi.single_eq_same] at h2
      exact zero_ne_one h2
    exact orderOf_eq_prime hb'3 hb'1
  have hcentN : ∀ s : ↥Bs, (s : G) ∈ Subgroup.centralizer (N : Set G) →
      (s : G) ∈ Subgroup.zpowers (b' : G) := by
    intro s hs
    have hk := (hkerΓ s).mp ((ggGamma_eq_one_iff N hBsN s).mpr hs)
    have hv : βL (Additive.ofMul s) = βL (Additive.ofMul (b' ^ (βL (Additive.ofMul s) c).val)) := by
      rw [ofMul_pow, map_nsmul, hb']
      funext k
      by_cases hkc : k = c
      · subst hkc
        simp
      · rw [hk k hkc]
        simp [Pi.single_eq_of_ne hkc]
    have hs' : s = b' ^ (βL (Additive.ofMul s) c).val :=
      Additive.ofMul.injective (βL.injective hv)
    rw [hs', SubmonoidClass.coe_pow]
    exact Subgroup.npow_mem_zpowers _ _
  have hZ : Nat.card ↥(Bs ⊓ N ⊓ Subgroup.centralizer (N : Set G)) ≤ 3 := by
    have hle : Bs ⊓ N ⊓ Subgroup.centralizer (N : Set G) ≤ Subgroup.zpowers (b' : G) := by
      rintro z ⟨⟨hzBs, -⟩, hzC⟩
      exact hcentN ⟨z, hzBs⟩ hzC
    calc Nat.card ↥(Bs ⊓ N ⊓ Subgroup.centralizer (N : Set G))
        ≤ Nat.card ↥(Subgroup.zpowers (b' : G)) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [Nat.card_zpowers, hb'ord]
  have hγ : ∀ hN : Bs ≤ Subgroup.normalizer (N : Set G),
      Nat.card (ggGamma N hN).range = 3 ^ 4 := fun _ => by
    rw [show (3 : ℕ) ^ 4 = 3 ^ (m - 1) by subst hm; rfl]
    exact hcardΓ
  have hact : ∀ hN : Bs ≤ Subgroup.normalizer (N : Set G), ∃ s : ↥Bs, ggGamma N hN s ≠ 1 :=
    fun _ => ⟨⟨x, hbase.x_mem⟩, fun h => by
      have h0 := (hkerΓ ⟨x, hbase.x_mem⟩).mp h a hca.symm
      rw [hcoords.x_coord hbase.x_mem] at h0
      exact one_ne_zero h0⟩
  have hJN : J ≤ N := hJ ▸ hJ₁N
  have hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
    rw [hJ, hD, ggQTwoDUnit_cent_J (by omega) hbase hcoords hb']
  have hpJ : 3 ∣ Nat.card ↥J := hJ ▸ qtwoDB17_three_dvd_J (by omega) hbase hdel.hca hdel.hcb
    hdel.hab
  have hcard : Nat.card ↥Bs = 3 ^ 5 := hm ▸ hbase.card_bs
  have hJlab : GGHasLabel ⟨.twA, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
    have h := ggQTwoDUnit_label_J (by omega) hbase c
    subst hJ hm
    exact h
  have hmark3 := qtwoDU5_nbr_marking hroute hpres h3 hnbr hNA hI1 hJN hpJ hBal hcard hJlab
  have hmarkD : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.D, 4, 1⟩) 3 Bs N := by
    have hsplit : GGInnerDiagOnLabel
        (fun _ lab => (lab = ⟨.twA, 4, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩) ∨ lab = ⟨.D, 4, 1⟩) 3 Bs N :=
      GGInnerDiagOnLabel.mono_label (fun _ h => or_assoc.mpr h) hmark3
    rcases GGInnerDiagOnLabel.elim_or hsplit with hU | hDm
    · exact (qtwoDU5_not_twA45 hC hNoTr hU hγ hZ h192).elim
    · exact hDm
  obtain ⟨Φ, hF, -, hZN⟩ := qtwoDU5_frameCore_D4 ggLabelRigidInput_holds hC hlt hmarkD hact
  have hMF := qtwoOrthMemberFacts_of_frameCore hBsE Φ hF hZN
  refine ⟨N, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, le_ggG0_of_neighbor hnbr⟩
  ·
    intro r hr hrC
    exact (qtwoDL1_rankOne_of_odd ggLNoncyclicInput_holds hcfg hM hodd (Or.inr ⟨b', hnbr⟩) hr
      hrC).1
  ·
    intro r hr hrC r' hr' hr'C hne
    obtain ⟨r₀, hr₀A, hr₀, r₀', hr₀'A, hr₀', hne₀, hcard₀⟩ :=
      qtwoDL1_base_unit ggLNoncyclicInput_holds hroute hodd hbase.card_field hbase.hyp
        hbase.range hbase.diag (hbase.card_bs_eq (by omega))
    have hr₀C := ggCoxRefl_of_cfg hroute (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) hr₀
    have hr₀'C := ggCoxRefl_of_cfg hroute (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀'A) hr₀'
    have hedge : ∃ i j : ι, M.M i j = 3 := by
      obtain ⟨j₀, hj₀⟩ := ggCoxeterMatrixD_exists_three (m := m) (by omega) ⟨0, by omega⟩
      exact ⟨e' ⟨0, by omega⟩, e' j₀, by
        rw [hM, CoxeterMatrix.reindex_apply]
        simpa using hj₀⟩
    have hcardeq := qtwoDL1_card_rankTwo_eq hpres h3 hedge hr₀C hr₀'C hne₀ hrC hr'C hne
    have hloc := qtwoDL1_local_orth qtwoDL1OrthPair_holds Φ hF hZN hr hr' (hrefl hrC)
      (hrefl hr'C) hne
    exact qtwoDL1_rankTwo_eq_of_card_le (by rw [hcardeq]; exact hcard₀.trans hloc)
  · intro r hr hrC r' hr' hr'C hne _
    exact hMF.1 r hr (hrefl hrC) r' hr' (hrefl hr'C) hne
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ h12 h23 h13 hne _
    exact hMF.2.1 r₁ h₁ (hrefl hr₁) r₂ h₂ (hrefl hr₂) r₃ h₃ (hrefl hr₃) h12 h23 h13 hne
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ r₄ h₄ hr₄ h12 h34 h13 h14 h23 h24
    exact hMF.2.2 r₁ h₁ (hrefl hr₁) r₂ h₂ (hrefl hr₂) r₃ h₃ (hrefl hr₃) r₄ h₄ (hrefl hr₄)
      h12 h34 h13 h14 h23 h24
  ·
    obtain ⟨c₀, hnode⟩ := hcoords.node
    obtain ⟨a₀, ha₀J, ha₀⟩ :=
      hcoords.join_onto (dPerm m (Equiv.swap c₀ c)) (dPerm_mem_dEven m _)
    have hlin₀ : ggLin (p := 3) βL a₀ = dPerm m (Equiv.swap c₀ c) := LinearEquiv.ext fun v => by
      rw [ggLin_apply, ha₀]
      simp
    have hP : dPerm m (Equiv.swap c₀ c) (dBasis m c₀) = dBasis m c := by
      rw [dPerm_apply, Equiv.swap_apply_left]
    have hPinv : (dPerm m (Equiv.swap c₀ c))⁻¹ (dBasis m c) = dBasis m c₀ := by
      rw [← hP, ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    refine ⟨e.symm ⟨a₀, ha₀J⟩, fun i hi => ?_⟩
    obtain ⟨sgn, a₁, b₁, hab₁, ha₁, hb₁, hact₁⟩ := hnode i hi
    set t : MulAut ↥Bs := ((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
      with ht
    have hcoe : ((e (e.symm ⟨a₀, ha₀J⟩ * M.simple (e' i) * (e.symm ⟨a₀, ha₀J⟩)⁻¹) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = a₀ * t * a₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    rw [hcoe]
    have hlint : ggLin (p := 3) βL t = dTau m sgn a₁ b₁ := LinearEquiv.ext fun v => by
      rw [ggLin_apply, ht, hact₁]
      simp
    have hmemJ : a₀ * t * a₀⁻¹ ∈ ggAutomizerJoin L Bs 𝒦 :=
      (ggAutomizerJoin L Bs 𝒦).mul_mem ((ggAutomizerJoin L Bs 𝒦).mul_mem ha₀J (e _).2)
        ((ggAutomizerJoin L Bs 𝒦).inv_mem ha₀J)
    have hwE : dPerm m (Equiv.swap c₀ c) * dTau m sgn a₁ b₁ * (dPerm m (Equiv.swap c₀ c))⁻¹ ∈
        dEven m :=
      (dEven m).mul_mem ((dEven m).mul_mem (dPerm_mem_dEven m _) (dTau_mem_dEven m sgn hab₁))
        ((dEven m).inv_mem (dPerm_mem_dEven m _))
    have hwc : (dPerm m (Equiv.swap c₀ c) * dTau m sgn a₁ b₁ * (dPerm m (Equiv.swap c₀ c))⁻¹)
        (Pi.single c 1) = Pi.single c 1 := by
      rw [← qtwoDB20_dBasis_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hPinv,
        dTau_apply_of_ne m sgn (Ne.symm ha₁) (Ne.symm hb₁), hP]
    have hwlin : ggLin (p := 3) βL (a₀ * t * a₀⁻¹) =
        dPerm m (Equiv.swap c₀ c) * dTau m sgn a₁ b₁ * (dPerm m (Equiv.swap c₀ c))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hlin₀, hlint]
    exact hXN (ggQTwoDUnit_weyl_X (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign
      hdel.norm hdel.conj hmemJ hwE hwc fun s => by rw [← hwlin, ggLin_apply_ofMul])

end CFSG.StandardType.QTwo

end
