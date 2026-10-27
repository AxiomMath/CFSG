module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteStd
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux6
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}

private theorem qtwoDB15_dSign_single {m : ℕ} {a b c : Fin m} (hca : c ≠ a) (hcb : c ≠ b) :
    dSign m a b (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
  have hsingle : Pi.single c (1 : ZMod 3) = dBasis m c :=
    (Pi.basisFun_apply (ZMod 3) (Fin m) c).symm
  have hnot : ¬ (c = a ∨ c = b) := by tauto
  have hfix : dSign m a b (dBasis m c) = dBasis m c := by
    rw [dSign_apply, if_neg hnot, one_smul]
  rw [hsingle]
  exact hfix

theorem ggQTwoDUnit_layer (hBal : GGLBalanceInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {a b c : Fin m} (hca : c ≠ a)
    (hcb : c ≠ b) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) {g : G}
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) :
    (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ≤
        LargeEvenPLayer 3 (Subgroup.centralizer ({(b' : G)} : Set G)) ∧
      ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map (MulAut.conj g).toMonoidHom ≤
        LargeEvenPLayer 3 (Subgroup.centralizer ({(b' : G)} : Set G)) := by
  have hThmI : GGThmIHyp p B x L := hcfg.1.1.1.1
  have hBstar : GGBstar p B Bs := hcfg.1.1.1.2.1
  haveI : IsSimpleGroup G := hThmI.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBsE : CFSG.Open.IsElemAbelian p Bs := hBstar.2.1
  have hb'1 : (b' : G) ≠ 1 := by
    intro h1
    have hzero : Pi.single c (1 : ZMod 3) = (0 : DVec m) := by
      calc Pi.single c (1 : ZMod 3) = βL (Additive.ofMul b') := hb'.symm
        _ = βL (Additive.ofMul (1 : ↥Bs)) := by rw [show b' = 1 from Subtype.ext h1]
        _ = βL 0 := rfl
        _ = 0 := map_zero βL
    have hc := congrFun hzero c
    simp only [Pi.single_eq_same, Pi.zero_apply] at hc
    exact one_ne_zero hc
  have hHne : Subgroup.centralizer ({(b' : G)} : Set G) ≠ ⊤ :=
    centralizer_singleton_ne_top_of_isSimpleGroup hThmI.2.1 hb'1
  have hKH : CFSG.Open.lBalanceIsKGroup ↥(Subgroup.centralizer ({(b' : G)} : Set G)) :=
    lBalanceIsKGroup_of_kProper hThmI.2.2.1 hHne
  have hxH : x ∈ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hBsE hbase.x_mem b'.2
  have hxp : x ^ 3 = 1 := by
    simpa [hbase.x_order] using pow_orderOf_eq_one x
  have hαb' : α b' = b' := by
    have h2 : Additive.ofMul (α b') = Additive.ofMul b' := by
      apply βL.injective
      rw [hα b', hb']
      exact qtwoDB15_dSign_single hca hcb
    exact Additive.ofMul.injective h2
  have hgb' : g * (b' : G) * g⁻¹ = (b' : G) := by
    rw [← hg b', hαb']
  have hginv : g⁻¹ * (b' : G) = (b' : G) * g⁻¹ := by
    have h := congrArg (fun z => g⁻¹ * z) hgb'
    rw [show g⁻¹ * (g * (b' : G) * g⁻¹) = (b' : G) * g⁻¹ by group] at h
    exact h.symm
  have hx'H : g * x * g⁻¹ ∈ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * x * g⁻¹) * (b' : G) = g * x * (g⁻¹ * (b' : G)) := by group
      _ = g * x * ((b' : G) * g⁻¹) := by rw [hginv]
      _ = g * (x * (b' : G)) * g⁻¹ := by group
      _ = g * ((b' : G) * x) * g⁻¹ := by
            rw [CFSG.Open.IsElemAbelian.comm hBsE hbase.x_mem b'.2]
      _ = (g * (b' : G) * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (b' : G) * (g * x * g⁻¹) := by rw [hgb']
  have hx'p : (g * x * g⁻¹) ^ 3 = 1 := by
    have h1 : (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ := by
      rw [← MulAut.conj_apply g x, ← map_pow, MulAut.conj_apply]
    rw [h1, hxp]
    group
  have hdvd₁ : 3 ∣ Nat.card ↥((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) := by
    obtain ⟨θ, hθinj, hθrange, -⟩ := ggQTwoDUnit_J_iso (by omega) hbase c g
    have hcard : Nat.card ↥((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) =
        Nat.card (Su F0 2 1 (m - 1)) := by
      rw [← hθrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hθinj,
        Subgroup.card_top]
    rw [hcard]
    let J : Finset (Fin (m - 1)) := Finset.univ.map (Fin.castLEEmb (by omega : 3 ≤ m - 1))
    have hJcard : J.card = 3 := by
      dsimp only [J]
      rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have h216 : Nat.card ↥(coordBlockSU F0 2 1 J) = 216 :=
      qTwoS34_card_coordBlockSU_three (K := F0) hbase.card_field hJcard
    have hdvd216 : 3 ∣ Nat.card ↥(coordBlockSU F0 2 1 J) := by rw [h216]; norm_num
    have htop : coordBlockSU F0 2 1 J ≤ (⊤ : Subgroup (Su F0 2 1 (m - 1))) := le_top
    have hdiv := Subgroup.card_dvd_of_le htop
    rw [Subgroup.card_top] at hdiv
    exact dvd_trans hdvd216 hdiv
  have hdvd₂ : 3 ∣ Nat.card
      ↥(((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map
        (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hdvd₁
  have hJcomp := ggQTwoDUnit_J_comp hcfg (by omega) hbase hcoords hca hcb hα hg hb' hb'B
  have hJ₁le : (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ≤
      CFSG.Open.lBalancePLayer 3 (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
        Subgroup.centralizer ({x} : Set G)) :=
    le_sSup (lBalanceIsPComponent_of_isComponentOf hJcomp.1
      (not_le_lBalancePrimeCore_of_dvd hdvd₁))
  have hJ₂le : (((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map
        (MulAut.conj g).toMonoidHom) ≤
      CFSG.Open.lBalancePLayer 3 (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
        Subgroup.centralizer ({g * x * g⁻¹} : Set G)) :=
    le_sSup (lBalanceIsPComponent_of_isComponentOf hJcomp.2
      (not_le_lBalancePrimeCore_of_dvd hdvd₂))
  have hJ₁le' : (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ≤
      CFSG.Open.lBalancePLayer 3 (Subgroup.centralizer ({(b' : G)} : Set G)) :=
    hJ₁le.trans (lBalancePLayer_inf_centralizer_le_of_input hBal Nat.prime_three hKH hxH hxp)
  have hJ₂le' : (((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map
        (MulAut.conj g).toMonoidHom) ≤
      CFSG.Open.lBalancePLayer 3 (Subgroup.centralizer ({(b' : G)} : Set G)) :=
    hJ₂le.trans (lBalancePLayer_inf_centralizer_le_of_input hBal Nat.prime_three hKH hx'H hx'p)
  exact ⟨by rw [largeEvenPLayer_eq_lBalancePLayer]; exact hJ₁le',
    by rw [largeEvenPLayer_eq_lBalancePLayer]; exact hJ₂le'⟩

theorem ggQTwoDUnit_rank_bound_of_card (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hp : p = 3)
    {n : ℕ} (hcard : Nat.card ↥Bs = 3 ^ n) (E : Subgroup G) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hU : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥E ≤ 3 ^ n := by
  have hThmI : GGThmIHyp p B x L := hcfg.1.1.1.1
  have hBstar : GGBstar p B Bs := hcfg.1.1.1.2.1
  have hBmax : LargeEvenIsBmax p B := hThmI.2.2.2.2.2.2.1.1
  have hBmax3 : LargeEvenIsBmax 3 B := hp ▸ hBmax
  obtain ⟨U, hUbot, hU2, hEU⟩ := hU
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hE)
  have hk_le : k ≤ LargeEvenTwoLocalRank 3 G :=
    le_twoLocalRank_of_normalizes Nat.prime_three hUbot hU2 hE hEU hk
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hBmax3.2.1
  calc Nat.card ↥E = 3 ^ k := hk
    _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hk_le
    _ = Nat.card B := hBcard.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hBstar.1
    _ = 3 ^ n := hcard

theorem ggQTwoDUnit_rank_bound (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (E : Subgroup G) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hU : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥E ≤ 3 ^ m :=
  ggQTwoDUnit_rank_bound_of_card hcfg hbase.p_eq hbase.card_bs E hE hU

end CFSG.StandardType.QTwo

end
