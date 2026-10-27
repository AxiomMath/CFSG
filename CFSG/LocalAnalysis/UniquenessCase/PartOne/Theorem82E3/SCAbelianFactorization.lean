module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsCore
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic
import CFSG.Quasithin.Vol2.KGFactC31NoM22FusBurnside
import CFSG.LocalAnalysis.UniquenessCase.UC6S19
import CFSG.GroupTheory.BurnsideNormalComplement
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CentC
import CFSG.RankThree.PartOne.ZR7.Cyc
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GL83PartI.I_7_13
import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFixedCentralizers

open Subgroup
open scoped commutatorElement
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {X : Type} [Group X] [Finite X]

theorem isWeaklyClosedIn_of_abelian_sylow_normalizer
    {S Z : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤)
    (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hZS : Z ≤ S)
    (hN : Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (Z : Set X)) :
    IsWeaklyClosedIn Z S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSidx : ¬ 3 ∣ S.index := by
    simpa [Subgroup.relIndex_top_right] using
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
  let P : Sylow 3 X := hS.isPGroup.toSylow hSidx
  have hPcoe : (P : Subgroup X) = S := hS.isPGroup.toSylow_coe hSidx
  intro g hg
  have hX : ∀ x ∈ Z, ∀ y ∈ (P : Subgroup X), x * y = y * x := by
    intro x hx y hy
    exact hSab x (hZS hx) y (hPcoe ▸ hy)
  have hY : ∀ x ∈ Z, ∀ y ∈ (P : Subgroup X),
      (g⁻¹ * x * g) * y = y * (g⁻¹ * x * g) := by
    intro x hx y hy
    have hh : g⁻¹ * x * g ∈ CFSG.conjugate Z g := by
      refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      simp
    exact hSab _ (hg hh) y (hPcoe ▸ hy)
  obtain ⟨n, hn, heq⟩ := CFSG.Quasithin.KGC31.burnside_fusion_subgroup P Z hX g hY
  have hnZ : n ∈ Subgroup.normalizer (Z : Set X) := hN (hPcoe ▸ hn)
  have hniZ : n⁻¹ ∈ Subgroup.normalizer (Z : Set X) := Subgroup.inv_mem _ hnZ
  have hnmap : Z.map (MulAut.conj n⁻¹).toMonoidHom = Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hniZ
  change Z.map (MulAut.conj g⁻¹).toMonoidHom = Z
  calc Z.map (MulAut.conj g⁻¹).toMonoidHom = Z.map (MulAut.conj n⁻¹).toMonoidHom := ?_
    _ = Z := hnmap
  apply le_antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨z, hz, by simpa [MulAut.conj_apply] using (heq z hz).symm⟩
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨z, hz, by simpa [MulAut.conj_apply] using heq z hz⟩

theorem centralizer_sup_pPrimeCore_eq_top_of_abelian_sylow_normalizer
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hK : CFSG.Open.IsKGroup X) {S Z : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤)
    (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hSr : CFSG.Open.pRank 3 S ≤ 3)
    (hZS : Z ≤ S) (hZ : Nat.card Z = 3)
    (hN : Subgroup.normalizer (S : Set X) ≤ Subgroup.centralizer (Z : Set X)) :
    Subgroup.centralizer (Z : Set X) ⊔ CFSG.pPrimeCore 3 X = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSidx : ¬ 3 ∣ S.index := by
    have hrel := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
    simpa [Subgroup.relIndex_top_right] using hrel
  let P : Sylow 3 X := hS.isPGroup.toSylow hSidx
  have hPcoe : (P : Subgroup X) = S := hS.isPGroup.toSylow_coe hSidx
  have hw : IsWeaklyClosedIn Z S := by
    intro g hg
    have hXcomm : ∀ x ∈ Z, ∀ y ∈ (P : Subgroup X), x * y = y * x := by
      intro x hx y hy
      exact hSab x (hZS hx) y (by rwa [hPcoe] at hy)
    have hgcomm : ∀ x ∈ Z, ∀ y ∈ (P : Subgroup X),
        (g⁻¹ * x * g) * y = y * (g⁻¹ * x * g) := by
      intro x hx y hy
      have hxW : g⁻¹ * x * g ∈ CFSG.conjugate Z g := by
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        simp
      exact hSab _ (hg hxW) y (by rwa [hPcoe] at hy)
    obtain ⟨n, hnN, hncomm⟩ :=
      CFSG.Quasithin.KGC31.burnside_fusion_subgroup P Z hXcomm g hgcomm
    have hnS : n ∈ Subgroup.normalizer (S : Set X) := by
      rwa [hPcoe] at hnN
    have hnC : n ∈ Subgroup.centralizer (Z : Set X) := hN hnS
    have hcent : ∀ x ∈ Z, n⁻¹ * x * n = x := by
      intro x hx
      have hcomm : x * n = n * x := Subgroup.mem_centralizer_iff.mp hnC x hx
      calc n⁻¹ * x * n = n⁻¹ * (x * n) := by rw [mul_assoc]
        _ = n⁻¹ * (n * x) := by rw [hcomm]
        _ = x := by rw [inv_mul_cancel_left]
    apply le_antisymm
    · intro w hwmem
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hwmem
      have h1 : g⁻¹ * x * g = n⁻¹ * x * n := hncomm x hx
      have h2 : n⁻¹ * x * n = x := hcent x hx
      simpa [MulAut.conj_apply, h1, h2] using hx
    · intro x hx
      have hmem : g⁻¹ * x * g ∈ CFSG.conjugate Z g := by
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        simp
      have hlin : g⁻¹ * x * g = x := (hncomm x hx).trans (hcent x hx)
      rwa [hlin] at hmem
  have hΩ : ∀ x ∈ S, x ^ 3 = 1 → ∀ y ∈ S, y ^ 3 = 1 → x * y = y * x :=
    fun x hx _ y hy _ => hSab x hx y hy
  have hr : CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set X)) = 1 :=
    hK332 X hK S hS hΩ hSr Z hZS hZ hw
  let R : Subgroup X := Subgroup.normalClosure (Z : Set X)
  let T : Subgroup X := S ⊓ R
  have hRnorm : R.Normal := Subgroup.normalClosure_normal
  have : R.Normal := hRnorm
  have hTS : T ≤ S := inf_le_left
  have hTR : T ≤ R := inf_le_right
  have hZT : Z ≤ T := le_inf hZS Subgroup.le_normalClosure
  have hTp : IsPGroup 3 T := hS.isPGroup.to_le hTS
  have hTcyc : IsCyclic T :=
    CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hTp hTR hr.le
  have hSylT : IsSylowOf 3 T R :=
    hS.inf_of_le_normalizer (K := ⊤) (N := R) le_top
      (Subgroup.le_normalizer_of_normal (H := R))
  set C : Subgroup X := Subgroup.centralizer (Z : Set X)
  set L : Subgroup X := Subgroup.normalizer (Z : Set X)
  have hSC : S ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hSab z (hZS hz) s hs
  have hSylCS : IsSylowOf 3 S C := hS.of_le hSC le_top
  have hCL : C ≤ L := Subgroup.centralizer_le_normalizer (Z : Set X)
  have hLC : L ≤ Subgroup.normalizer (C : Set X) := by
    have hnorm : (C.subgroupOf L).Normal :=
      Subgroup.normal_subgroupOf_centralizer_normalizer (Z : Set X)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCL).mp hnorm
  have hfr := CFSG.LocalAnalysis.UniquenessCase.UC6.frattini_of_isSylowOf hCL hLC hSylCS
  have hLCle : L ≤ C := by
    rw [hfr]
    exact sup_le le_rfl (inf_le_right.trans hN)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hZ])
  let zR : R := ⟨(z : X), Subgroup.le_normalClosure z.2⟩
  obtain ⟨Q, hQ⟩ := hSylT.exists_sylow_eq_subgroupOf
  have hQmap : (Q : Subgroup R).map R.subtype = T := by
    rw [hQ, Subgroup.map_subgroupOf_eq_of_le hTR]
  have hQcyc : IsCyclic (Q : Subgroup R) := by
    rw [hQ]
    have : IsCyclic T := hTcyc
    exact isCyclic_of_injective
      (Subgroup.subgroupOfEquivOfLe hTR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTR).injective
  have hzQ : zR ∈ (Q : Subgroup R) := by
    rw [hQ]
    exact hZT z.2
  have hzRord : orderOf zR = 3 := by
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_mk (z : X) z.2]
    exact hz
  have hQN : ∀ g ∈ Subgroup.normalizer ((Q : Subgroup R) : Set R),
      g * zR * g⁻¹ = zR := by
    intro g hg
    have hgT : (g : X) ∈ Subgroup.normalizer (T : Set X) := by
      rw [hQ, ← Subgroup.subgroupOf_normalizer_eq hTR] at hg
      exact hg
    have hgZ : (g : X) ∈ Subgroup.normalizer (Z : Set X) :=
      CFSG.GorensteinWalter.normalizer_le_normalizer_of_le_cyclic hTcyc hZT hgT
    have hgz := Subgroup.mem_centralizer_iff.mp (hLCle hgZ) (z : X) z.2
    apply Subtype.ext
    change (g : X) * (z : X) * (g : X)⁻¹ = (z : X)
    rw [← hgz, mul_assoc, mul_inv_cancel, mul_one]
  have hQNC : Subgroup.normalizer ((Q : Subgroup R) : Set R) ≤
      Subgroup.centralizer ((Q : Subgroup R) : Set R) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.fr_normalizer_le_centralizer_cyclic_sylow
      Q hQcyc hzQ (by intro h; rw [h, orderOf_one] at hzRord; omega)
      (by rw [← hzRord]; exact pow_orderOf_eq_one zR) hQN
  obtain ⟨K, _, hKp, _, _, hKchar, _, hKsup, _, _, _⟩ :=
    CFSG.GroupTheory.burnside_normal_complement Q hQNC
  have : K.Characteristic := hKchar
  let K₀ : Subgroup X := K.map R.subtype
  have hK₀normal : K₀.Normal := ConjAct.normal_of_characteristic_of_normal
    (H := R) (K := K)
  have hK₀cop : Nat.Coprime 3 (Nat.card K₀) := by
    rw [show Nat.card K₀ = Nat.card K from Subgroup.card_map_of_injective R.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hKp
  have hK₀le : K₀ ≤ CFSG.pPrimeCore 3 X :=
    CFSG.le_pPrimeCore_of_normal_coprime hK₀normal hK₀cop
  have hKT : K₀ ⊔ T = R := by
    rw [← hQmap, ← Subgroup.map_sup, hKsup, Subgroup.map_top, Subgroup.range_subtype]
  have hRle : R ≤ C ⊔ CFSG.pPrimeCore 3 X := by
    rw [← hKT]
    exact sup_le (hK₀le.trans le_sup_right) ((hTS.trans hSC).trans le_sup_left)
  have hNX : Subgroup.normalizer (T : Set X) ≤ C :=
    (CFSG.GorensteinWalter.normalizer_le_normalizer_of_le_cyclic hTcyc hZT).trans hLCle
  have hfrR := CFSG.LocalAnalysis.UniquenessCase.UC6.frattini_of_isSylowOf
    (H := ⊤) (L := R) le_top (by rw [Subgroup.normalizer_eq_top]) hSylT
  apply top_unique
  rw [hfrR]
  exact sup_le hRle (inf_le_right.trans (hNX.trans le_sup_left))

theorem inf_le_pPrimeCore_of_rank_one_normalClosures
    {S Z₁ Z₂ N₁ N₂ : Subgroup X} (hS : IsSylowOf 3 S ⊤)
    (hN₁ : N₁.Normal) (hN₂ : N₂.Normal)
    (hZ₁S : Z₁ ≤ S) (hZ₂S : Z₂ ≤ S)
    (hZ₁N : Z₁ ≤ N₁) (hZ₂N : Z₂ ≤ N₂)
    (hZ₁ : Nat.card Z₁ = 3) (hZ₂ : Nat.card Z₂ = 3) (hZ₁₂ : Z₁ ≠ Z₂)
    (hr₁ : CFSG.Open.pRank 3 N₁ = 1) (hr₂ : CFSG.Open.pRank 3 N₂ = 1) :
    N₁ ⊓ N₂ ≤ CFSG.pPrimeCore 3 X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : N₁.Normal := hN₁
  have : N₂.Normal := hN₂
  let T₁ : Subgroup X := S ⊓ N₁
  let T₂ : Subgroup X := S ⊓ N₂
  have hTp₁ : IsPGroup 3 T₁ := hS.isPGroup.to_le inf_le_left
  have hTp₂ : IsPGroup 3 T₂ := hS.isPGroup.to_le inf_le_left
  have hTc₁ : IsCyclic T₁ := CFSG.isCyclic_of_le_of_pRank_le_one
    Nat.prime_three (by norm_num) hTp₁ inf_le_right hr₁.le
  have hTc₂ : IsCyclic T₂ := CFSG.isCyclic_of_le_of_pRank_le_one
    Nat.prime_three (by norm_num) hTp₂ inf_le_right hr₂.le
  have : IsCyclic T₁ := hTc₁
  have : IsCyclic T₂ := hTc₂
  have hZT₁ : Z₁ ≤ T₁ := le_inf hZ₁S hZ₁N
  have hZT₂ : Z₂ ≤ T₂ := le_inf hZ₂S hZ₂N
  have hdisj : T₁ ⊓ T₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hZ₁])
    obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hZ₂])
    have hzo : orderOf (z : X) = 3 := (Subgroup.orderOf_coe z).trans hz
    have hz'o : orderOf (z' : X) = 3 := (Subgroup.orderOf_coe z').trans hz'
    have hzne : (z : X) ≠ 1 := by intro h; rw [h, orderOf_one] at hzo; omega
    have hz'ne : (z' : X) ≠ 1 := by intro h; rw [h, orderOf_one] at hz'o; omega
    have hsame := CFSG.RankThree.PartOne.ZR7.inf_eq_bot_of_cyclic Nat.prime_three hTp₁
      (hZT₁ z.2) (hZT₂ z'.2)
      (by rw [← hzo]; exact pow_orderOf_eq_one (z : X))
      (by rw [← hz'o]; exact pow_orderOf_eq_one (z' : X)) hzne hz'ne
      (by
        intro hmem
        have hz₁gen : zpowers (z : X) = Z₁ := Subgroup.eq_of_le_of_card_ge
          (zpowers_le.mpr z.2) (by rw [Nat.card_zpowers, hzo, hZ₁])
        have hz₂gen : zpowers (z' : X) = Z₂ := Subgroup.eq_of_le_of_card_ge
          (zpowers_le.mpr z'.2) (by rw [Nat.card_zpowers, hz'o, hZ₂])
        have hle : Z₂ ≤ Z₁ := by rw [← hz₂gen, ← hz₁gen]; exact zpowers_le.mpr hmem
        exact hZ₁₂ (Subgroup.eq_of_le_of_card_ge hle (by rw [hZ₁, hZ₂])).symm)
    have hh : x ∈ T₁ ⊓ T₂ := hx
    rw [hsame, Subgroup.mem_bot] at hh
    exact hx1 hh
  have hbot : S ⊓ (N₁ ⊓ N₂) = ⊥ := by
    have h : S ⊓ (N₁ ⊓ N₂) = T₁ ⊓ T₂ := by
      ext x
      simp only [T₁, T₂, mem_inf]
      tauto
    exact h.trans hdisj
  have hSyl := hS.inf_of_le_normalizer (K := ⊤) (N := N₁ ⊓ N₂) le_top
    (Subgroup.le_normalizer_of_normal (H := N₁ ⊓ N₂))
  have hcard := hSyl.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hno3 : ¬ 3 ∣ Nat.card (N₁ ⊓ N₂ : Subgroup X) := by
    intro hd
    have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hd
    have hlt : 1 < 3 ^ (Nat.card (N₁ ⊓ N₂ : Subgroup X)).factorization 3 :=
      Nat.one_lt_pow (by omega) (by norm_num)
    omega
  exact CFSG.le_pPrimeCore_of_normal_coprime inferInstance
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hno3)

theorem top_le_sup_pPrimeCore_of_abelian_sylow_weaklyClosed
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hK : CFSG.Open.IsKGroup X) {S A Z₁ Z₂ B Y : Subgroup X}
    (hS : IsSylowOf 3 S ⊤) (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hrS : CFSG.Open.pRank 3 S ≤ 3)
    (hAS : A ≤ S) (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hAcube : ∀ x ∈ S, x ^ 3 = 1 → x ∈ A)
    (hZ₁A : Z₁ ≤ A) (hZ₂A : Z₂ ≤ A) (hZ₁ : Nat.card Z₁ = 3) (hZ₂ : Nat.card Z₂ = 3)
    (hZ₁₂ : Z₁ ≠ Z₂) (hw₁ : IsWeaklyClosedIn Z₁ S) (hw₂ : IsWeaklyClosedIn Z₂ S)
    (hB : B ≤ Subgroup.center X) (hgen : A ≤ Z₁ ⊔ Z₂ ⊔ B)
    (hC₁ : centralizer (Z₁ : Set X) ≤ Y) (hC₂ : centralizer (Z₂ : Set X) ≤ Y)
    (hNA : normalizer (A : Set X) ≤ Y) : (⊤ : Subgroup X) ≤ Y ⊔ CFSG.pPrimeCore 3 X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N₁ : Subgroup X := normalClosure (Z₁ : Set X)
  let N₂ : Subgroup X := normalClosure (Z₂ : Set X)
  have hN₁norm : N₁.Normal := Subgroup.normalClosure_normal
  have hN₂norm : N₂.Normal := Subgroup.normalClosure_normal
  have : N₁.Normal := hN₁norm
  have : N₂.Normal := hN₂norm
  have : B.Normal := Subgroup.normal_of_le_center hB
  have hΩ : ∀ x ∈ S, x ^ 3 = 1 → ∀ y ∈ S, y ^ 3 = 1 → x * y = y * x :=
    fun x hx _ y hy _ => hSab x hx y hy
  have hr₁ : CFSG.Open.pRank 3 N₁ = 1 :=
    hK332 X hK S hS hΩ hrS Z₁ (hZ₁A.trans hAS) hZ₁ hw₁
  have hr₂ : CFSG.Open.pRank 3 N₂ = 1 :=
    hK332 X hK S hS hΩ hrS Z₂ (hZ₂A.trans hAS) hZ₂ hw₂
  have hO := inf_le_pPrimeCore_of_rank_one_normalClosures hS hN₁norm hN₂norm
    (hZ₁A.trans hAS) (hZ₂A.trans hAS) Subgroup.le_normalClosure Subgroup.le_normalClosure
    hZ₁ hZ₂ hZ₁₂ hr₁ hr₂
  have hcomm : ⁅N₁, N₂⁆ ≤ CFSG.pPrimeCore 3 X :=
    (Subgroup.commutator_le_inf N₁ N₂).trans hO
  have hp₁ : IsPGroup 3 Z₁ := IsPGroup.of_card (n := 1) (by rw [hZ₁, pow_one])
  have hp₂ : IsPGroup 3 Z₂ := IsPGroup.of_card (n := 1) (by rw [hZ₂, pow_one])
  have hn₂ : N₂ ≤ centralizer (Z₁ : Set X) ⊔ CFSG.pPrimeCore 3 X :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.le_centralizer_sup_pPrimeCore_of_commutator_le
      Subgroup.le_normalClosure hp₁ hcomm
  have hn₁ : N₁ ≤ centralizer (Z₂ : Set X) ⊔ CFSG.pPrimeCore 3 X :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.le_centralizer_sup_pPrimeCore_of_commutator_le
      Subgroup.le_normalClosure hp₂ (by rwa [Subgroup.commutator_comm])
  let N₀ : Subgroup X := (N₁ ⊔ N₂) ⊔ B
  have hN₀ : N₀.Normal := inferInstance
  have : N₀.Normal := hN₀
  have hAN : A ≤ N₀ := hgen.trans (sup_le_sup_right
    (sup_le_sup Subgroup.le_normalClosure Subgroup.le_normalClosure) B)
  have hn₀ : N₀ ≤ Y ⊔ CFSG.pPrimeCore 3 X := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hn₁.trans (sup_le_sup_right hC₂ _)
    · exact hn₂.trans (sup_le_sup_right hC₁ _)
    · exact ((hB.trans (Subgroup.center_le_centralizer (Z₁ : Set X))).trans hC₁).trans le_sup_left
  let T : Subgroup X := S ⊓ N₀
  have hAT : A ≤ T := le_inf hAS hAN
  have hT : IsSylowOf 3 T N₀ := hS.inf_of_le_normalizer (K := ⊤) (N := N₀) le_top
    (Subgroup.le_normalizer_of_normal (H := N₀))
  have hNT : normalizer (T : Set X) ≤ normalizer (A : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨a, ha, rfl⟩
      have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      have hgt : (MulAut.conj g) a ∈ T := by
        rw [← hmap]
        exact ⟨a, hAT ha, rfl⟩
      apply hAcube _ hgt.1
      rw [← map_pow, hAe.2 a ha, map_one]
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hfr := CFSG.LocalAnalysis.UniquenessCase.UC6.frattini_of_isSylowOf
    (H := ⊤) (L := N₀) le_top (by rw [Subgroup.normalizer_eq_top]) hT
  rw [hfr]
  exact sup_le hn₀ (inf_le_right.trans ((hNT.trans hNA).trans le_sup_left))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFixedCentralizers
