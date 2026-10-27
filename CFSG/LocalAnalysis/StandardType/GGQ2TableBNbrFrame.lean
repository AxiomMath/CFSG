module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs
import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin
import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrame
import CFSG.LocalAnalysis.StandardType.GGQ2CensusBridge
import CFSG.CGT.PushingUpLit.SYMB.ProdCard

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

section Nbr

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {y : G} {K : Subgroup G}

private theorem tbnb_barCentralizer_le_centralizer (hS : GGQTwoSetting 3 B Bs x L D J)
    (hnb : GGNbr 3 B x D J y K) {b : G} (hb : b ∈ ggBarCentralizer 3 Bs K) :
    b ∈ Subgroup.centralizer (K : Set G) := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  obtain ⟨hKc, hBK⟩ := isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hDJ hnb)
  have hxB : x ∈ B := hI.2.2.2.2.2.2.1.2.1
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBK hxB
  have hyB : y ∈ B := hnb.1.2.1
  have hx_not_zp : x ∉ Subgroup.zpowers y := by
    intro hx
    have hDc : D = Subgroup.zpowers y := by
      rw [hnb.2.1]
      refine le_antisymm ((Subgroup.closure_le _).mpr ?_)
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)))
      rintro z (rfl | hzy)
      · exact hx
      · rw [hzy]; exact Subgroup.mem_zpowers y
    have hcard : 3 ^ 2 ≤ 3 := by
      calc 3 ^ 2 = Nat.card D := hDJ.1.2.2.1.symm
        _ = Nat.card (Subgroup.zpowers y) := by rw [hDc]
        _ = orderOf y := Nat.card_zpowers y
        _ ≤ 3 := Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (hI.2.2.2.2.2.2.1.1.1.2 y hyB))
    norm_num at hcard
  have hO_ne : LargeEvenPPrimeCoreOf 3 K ≠ K := by
    intro hO
    have hcomm : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 K := by
      rw [hO, Subgroup.commutator_le]
      intro k hk z hz
      have hzN : z ∈ Subgroup.normalizer (K : Set G) := (Subgroup.zpowers_le.mpr hxN) hz
      have hkz : k * z * k⁻¹ * z⁻¹ = k * (z * k⁻¹ * z⁻¹) := by group
      rw [commutatorElement_def, hkz]
      exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hzN k⁻¹).mp (K.inv_mem hk))
    exact hx_not_zp ((hnb.1.2.2.2.2.2 x).mp ⟨hxB, hxN, hcomm⟩)
  have hZ : LargeEvenPPrimeCoreOf 3 K ≤ (Subgroup.center K).map K.subtype := by
    have hPle : LargeEvenPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
      CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hKc.2.2 _
        (by
          intro htop
          exact hO_ne (by
            rw [show LargeEvenPPrimeCoreOf 3 K =
              (LargeEvenPPrimeCore 3 ↥K).map K.subtype from rfl, htop,
              ← MonoidHom.range_eq_map, Subgroup.range_subtype]))
    exact Subgroup.map_mono hPle
  have hA : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ (Subgroup.center K).map K.subtype :=
    hb.2.2.trans hZ
  have hdouble : ⁅⁅K, Subgroup.zpowers b⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨z, hz, rfl⟩ := hA ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
  have hperfK : Group.IsPerfect ↥K := (Group.isPerfect_def).2 hKc.2.2.1
  have hKK : ⁅K, K⁆ = K := @Subgroup.commutator_eq_self G _ K hperfK
  have hbot : ⁅K, Subgroup.zpowers b⁆ = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.perfect_double_commutator hKK hdouble
  rw [Subgroup.commutator_comm] at hbot
  exact Subgroup.zpowers_le.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)

private theorem tbnb_five_le_card_bstar (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : ¬ GGQTwoI1 Bs D J) : 3 ^ 5 ≤ Nat.card Bs := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hBs : GGBstar 3 B Bs := hS.1.1.2.1
  have hne : B ≠ Bs := by
    rintro rfl
    refine hI1 fun b hb hc => ?_
    rw [hDJ.1.2.2.2.2.2.2]
    exact ⟨hb, Subgroup.mem_centralizer_iff.mpr fun j hj => (hc j hj).symm⟩
  have hlt : Nat.card B < Nat.card Bs :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hBs.1) fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hBs.1 h.ge)
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G :=
    hI.2.2.2.2.2.2.1.1.2.1
  have hm4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hI.2.2.2.2.2.1.2.2.2
  have hBsP : IsPGroup 3 Bs := fun g =>
    ⟨1, Subtype.ext (by simpa using hBs.2.1.2 g g.2)⟩
  obtain ⟨n, hn⟩ := hBsP.exists_card_eq
  rw [hBcard, hn] at hlt
  have hmn : LargeEvenTwoLocalRank 3 G < n :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
  have hdle : 3 ^ n ≤ 3 ^ (LargeEvenTwoLocalRank 3 G + 1) := by
    calc 3 ^ n = Nat.card Bs := hn.symm
      _ ≤ 3 * Nat.card B := hBs.2.2.1
      _ = 3 * 3 ^ LargeEvenTwoLocalRank 3 G := by rw [hBcard]
      _ = 3 ^ (LargeEvenTwoLocalRank 3 G + 1) := by rw [pow_succ]; ring
  have hnle : n ≤ LargeEvenTwoLocalRank 3 G + 1 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hdle
  calc 3 ^ 5 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = Nat.card Bs := hn.symm

private theorem tbnb_finrank_cent_le_two {R : RawFrameData}
    (real : Realization (ggG0 3 B x L D J) Bs R) (hS : GGQTwoSetting 3 B Bs x L D J)
    (hnb : GGNbr 3 B x D J y K) {k : R.Code} (hkadm : R.admissible k)
    (hkcomp : real.component k = K) :
    finrank (ZMod 3) (R.cent k) ≤ 2 := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hBs : GGBstar 3 B Bs := hS.1.1.2.1
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G) with hCdef
  have hBsP : IsPGroup 3 Bs := fun g =>
    ⟨1, Subtype.ext (by simpa using hBs.2.1.2 g g.2)⟩
  have hC3 : IsPGroup 3 ↥C := by
    intro c
    obtain ⟨n, hn⟩ := hBsP ⟨c.1, (Subgroup.mem_inf.mp c.2).1⟩
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨n, hn⟩ := hC3.exists_card_eq
  have hyB : y ∈ B := hnb.1.2.1
  have hCB : C ⊓ B ≤ Subgroup.zpowers y := by
    intro b hb
    obtain ⟨hbC, hbB⟩ := Subgroup.mem_inf.mp hb
    have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.centralizer_le_normalizer (K : Set G) hbC.2
    have hcomm : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 K := by
      rw [Subgroup.commutator_le]
      intro k hk z hz
      have hzk : k * z = z * k :=
        Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hbC.2) hz) k hk
      have h1 : k * z * k⁻¹ * z⁻¹ = 1 := by rw [hzk]; group
      rw [commutatorElement_def, h1]
      exact one_mem _
    exact (hnb.1.2.2.2.2.2 b).mp ⟨hbB, hbN, hcomm⟩
  have hcardCB : Nat.card ↥(C ⊓ B) ≤ 3 := by
    calc Nat.card ↥(C ⊓ B) ≤ Nat.card ↥(Subgroup.zpowers y) := Subgroup.card_le_of_le hCB
      _ = orderOf y := Nat.card_zpowers y
      _ ≤ 3 := Nat.le_of_dvd (by norm_num)
        (orderOf_dvd_of_pow_eq_one (hI.2.2.2.2.2.2.1.1.1.2 y hyB))
  have hcommCB : ∀ c ∈ C, ∀ d ∈ B, c * d = d * c := by
    intro c hc d hd
    exact congrArg Subtype.val (hBs.2.1.1.is_comm.comm ⟨c, (Subgroup.mem_inf.mp hc).1⟩
      ⟨d, hBs.1 hd⟩)
  have hprod := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute hcommCB
  have hsup_le : Nat.card ↥(C ⊔ B) ≤ 3 * Nat.card B := by
    calc Nat.card ↥(C ⊔ B) ≤ Nat.card Bs := Subgroup.card_le_of_le (sup_le inf_le_left hBs.1)
      _ ≤ 3 * Nat.card B := hBs.2.2.1
  have hCle : Nat.card ↥C ≤ 9 := by
    have h1 : Nat.card ↥C * Nat.card B ≤ 9 * Nat.card B := by
      calc Nat.card ↥C * Nat.card B = Nat.card ↥(C ⊔ B) * Nat.card ↥(C ⊓ B) := hprod.symm
        _ ≤ (3 * Nat.card B) * 3 := Nat.mul_le_mul hsup_le hcardCB
        _ = 9 * Nat.card B := by ring
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hcent : R.cent k = ggLinImage (p := 3) real.coord C := by
    rw [← real.cent_eq k hkadm, hkcomp, hCdef, ← ggLinImage_inf_left (p := 3) real.coord
      (Subgroup.centralizer (K : Set G))]
  have hfr : finrank (ZMod 3) (R.cent k) = n := by
    rw [hcent]
    exact finrank_ggLinImage_of_card (p := 3) real.coord inf_le_left hn
  have hn2 : n ≤ 2 := by
    have h1 : 3 ^ n ≤ 3 ^ 2 := by
      calc 3 ^ n = Nat.card ↥C := hn.symm
        _ ≤ 9 := hCle
        _ = 3 ^ 2 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
  omega

private theorem tbnb_finrank_five_le {R : RawFrameData}
    (real : Realization (ggG0 3 B x L D J) Bs R) (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : ¬ GGQTwoI1 Bs D J) : 5 ≤ finrank (ZMod 3) R.V := by
  have h5 := tbnb_five_le_card_bstar hS hI1
  have hcard : Nat.card R.V = Nat.card Bs := by
    rw [← Nat.card_congr real.coord.toEquiv, ← Nat.card_congr Additive.ofMul]
  have hV : Nat.card R.V = 3 ^ finrank (ZMod 3) R.V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  rw [hV] at hcard
  have h1 : 3 ^ 5 ≤ 3 ^ finrank (ZMod 3) R.V := by rwa [← hcard] at h5
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1

theorem tableBNbrAtFrame_of_nbrWeylData {R : RawFrameData} (h : NbrWeylData R) :
    TableBNbrAtFrame R := by
  intro G _ _ p B Bs x L D J hS hp hI1 hF
  subst p
  intro _ y K hnb
  obtain ⟨real⟩ := hF
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hBs : GGBstar 3 B Bs := hS.1.1.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hBs.1 hyB
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hDJ hnb)
  have hKcomp : IsComponentOf K (ggG0 3 B x L D J ⊓
      Subgroup.centralizer (Subgroup.zpowers y : Set G)) := by
    have h1 : IsComponentOf K (ggG0 3 B x L D J ⊓
        Subgroup.centralizer ({y} : Set G)) :=
      hKc.of_le_of_le (le_inf (le_ggG0_of_ggNbr hnb) hKc.1) inf_le_right
    have hEq : Subgroup.centralizer (Subgroup.zpowers y : Set G)
        = Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rwa [← hEq] at h1
  obtain ⟨k, hkadm, hkocc₀, hkcomp'⟩ :=
    (real.occurs_iff (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyBs) K).mp hKcomp
  have hkcomp : real.component k = K := hkcomp'.symm
  have hkocc : R.occurs ((ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) k := by
    rw [span_singleton_eq_ggLinImage (p := 3) real.coord hyBs]
    exact hkocc₀
  set v : R.V := real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : (⟨y, hyBs⟩ : ↥Bs) = 1 := by
      have h2 := real.coord.injective (h0.trans (map_zero real.coord).symm)
      exact Additive.ofMul.injective h2
    exact hnb.1.2.2.1 (Subtype.ext_iff.mp h1)
  have hcodim : 3 + finrank (ZMod 3) (R.cent k) ≤ finrank (ZMod 3) R.V := by
    have h5 := tbnb_finrank_five_le real hS hI1
    have h2 := tbnb_finrank_cent_le_two real hS hnb hkadm hkcomp
    omega
  obtain ⟨W⟩ := h v k hv0 hkadm hkocc hcodim
  have hauto : ggAutomizer K Bs =
      Subgroup.closure (Set.range (fun i => ggLinInv real.coord (W.refl i))) := by
    have hnorm : (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) =
        R.normalizerGroup k := by
      rw [← real.normalizer_eq k hkadm, hkcomp]
    have h1 := eq_closure_ggLinInv_of_map_eq (p := 3) real.coord
      (hnorm.trans W.closure_refl.symm)
    have h2 : Set.range (fun i => ggLinInv real.coord (W.refl i)) =
        ggLinInv real.coord '' Set.range W.refl := by
      ext u
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨W.refl i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨T, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    exact h1.trans (congrArg Subgroup.closure h2.symm)
  have hfix : ∀ b : ↥Bs, real.coord (Additive.ofMul b) ∈
      ggFixedSubmodule (p := 3) real.coord (ggAutomizer K Bs) ↔
      (b : G) ∈ ggBarCentralizer 3 Bs K := by
    intro b
    have hmem := mem_ggFixedSubmodule_closure_iff (p := 3) (by norm_num) real.coord
      (fun i => ggLinInv real.coord (W.refl i)) W.coroot W.root
      (fun i w => by rw [ggLin_ggLinInv]; exact W.refl_apply i w)
      (fun i => by rw [W.pairing, W.isCartan.1 i]; norm_num) Set.univ
      (real.coord (Additive.ofMul b))
    rw [hauto, ← Set.image_univ, hmem]
    simp only [Set.mem_univ, true_implies]
    rw [W.ker_iff, ← real.cent_eq k hkadm, hkcomp,
      ← ggLinImage_inf_left (p := 3) real.coord (Subgroup.centralizer (K : Set G)),
      ofMul_mem_ggLinImage]
    refine ⟨fun hb => ⟨b.2, Subgroup.centralizer_le_normalizer (K : Set G) hb.2, ?_⟩,
      fun hb => ⟨b.2, tbnb_barCentralizer_le_centralizer hS hnb hb⟩⟩
    have hbot : (⁅K, Subgroup.zpowers (b : G)⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.zpowers_le.mpr hb.2
    rw [hbot]
    exact bot_le
  let N : GGQ2NbrDatum 3 Bs K :=
    { Λ := W.ι
      coxeter := W.coxeter
      cartan := W.cartan
      V := R.V
      model := real.coord
      simple := fun i => ggLinInv real.coord (W.refl i)
      coroot := W.coroot
      root := W.root
      isWeyl := W.isWeyl
      isCartan := W.isCartan
      pairing := W.pairing
      simple_apply := fun i w => by
        rw [ggLin_ggLinInv]
        exact W.refl_apply i w
      automizer_K := hauto
      fixed_ZK := hfix }
  refine ⟨N, ?_⟩
  have hfin : 3 ≤ Fintype.card W.ι := by
    let φ : R.V →+ (W.ι → ZMod 3) :=
      { toFun := fun u i => W.root i u
        map_zero' := by funext i; simp
        map_add' := fun u v => by funext i; simp }
    have hmem : ∀ u : R.V, u ∈ φ.ker ↔ u ∈ R.cent k := by
      intro u
      rw [AddMonoidHom.mem_ker]
      exact ⟨fun hu => (W.ker_iff u).mp fun i => congrFun hu i,
        fun hu => by ext i; exact (W.ker_iff u).mpr hu i⟩
    have hcardV : Nat.card R.V = 3 ^ finrank (ZMod 3) R.V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
    have hcardker : Nat.card ↥φ.ker = 3 ^ finrank (ZMod 3) (R.cent k) := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight hmem)]
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
    have hcardrange : Nat.card ↥φ.range ≤ 3 ^ Fintype.card W.ι := by
      calc Nat.card ↥φ.range ≤ Nat.card (W.ι → ZMod 3) := Finite.card_subtype_le _
        _ = 3 ^ Fintype.card W.ι := by
          rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
    have hprod := AddSubgroup.card_ker_mul_card_range φ
    have hcomb : 3 ^ finrank (ZMod 3) R.V ≤
        3 ^ (finrank (ZMod 3) (R.cent k) + Fintype.card W.ι) := by
      calc 3 ^ finrank (ZMod 3) R.V = Nat.card R.V := hcardV.symm
        _ = Nat.card ↥φ.ker * Nat.card ↥φ.range := hprod.symm
        _ ≤ 3 ^ finrank (ZMod 3) (R.cent k) * 3 ^ Fintype.card W.ι :=
            Nat.mul_le_mul (le_of_eq hcardker) hcardrange
        _ = 3 ^ (finrank (ZMod 3) (R.cent k) + Fintype.card W.ι) := by rw [← pow_add]
    have h5 := tbnb_finrank_five_le real hS hI1
    have h2 := tbnb_finrank_cent_le_two real hS hnb hkadm hkcomp
    have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcomb
    omega
  simpa [N] using hfin


end Nbr

end CFSG.StandardType.GGQ2Frame

end
