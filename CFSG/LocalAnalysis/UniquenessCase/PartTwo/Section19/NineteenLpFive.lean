module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
public import CFSG.GroupTheory.AltFiveConjCommutator

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem le_oTwoEOf_of_mem_calC {D : Data G} {J : Subgroup G} (hJ : J ∈ calC D.M) :
    J ≤ oTwoEOf D.M := by
  intro x hx
  have hc : CFSG.IsComponent (barImage D.M J) := by
    obtain ⟨hsnTop, -, hqsub, -⟩ := UC6S846.calC_subgroupOf hJ
    exact UC6S846.isComponent_image (Y := ↥D.M) hsnTop hqsub
  have hJl : barImage D.M J ≤ CFSG.layer (Bar2 D.M) := CFSG.LocalCores.component_le_layer hc
  exact uc22p21c_mem_barPreimage.2
    ⟨hJ.1.le hx, hJl (uc22p21c_mem_barImage.2 ⟨⟨x, hJ.1.le hx⟩, hx, rfl⟩)⟩

theorem barImage_Hinf_oTwoEOf (M : Subgroup G) :
    barImage M (Hinf (oTwoEOf M)) = CFSG.layer (Bar2 M) := by
  have hoM : oTwoEOf M ≤ M := s13_barPreimage_le M _
  set K' : Subgroup ↥M := (oTwoEOf M).subgroupOf M
  have hK'map : K'.map M.subtype = oTwoEOf M := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hoM]
  have ha : (Hinf K').map M.subtype = Hinf (oTwoEOf M) := by
    rw [Hinf_map, hK'map]
  have hb : (Hinf (oTwoEOf M)).subgroupOf M = Hinf K' := by
    rw [← ha]; exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hlay : Hinf (CFSG.layer (Bar2 M)) = CFSG.layer (Bar2 M) :=
    le_antisymm (uc22p21c_Hinf_le _) (uc22p21c_le_Hinf le_rfl CFSG.LocalCores.layer_perfect)
  show ((Hinf (oTwoEOf M)).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = _
  rw [hb, Hinf_map]
  have hc : K'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = CFSG.layer (Bar2 M) :=
    s13_barImage_barPreimage M (CFSG.layer (Bar2 M))
  rw [hc, hlay]

theorem barImage_eq_layer_of_ctx1768 (D : Data G) {V₀ V : Subgroup G} {L L' : Subgroup G}
    (c : S17.Ctx1768 D L L') (hL : L ∈ S17.calLp D 5)
    (hX0 : UC22.conjClosure D.M L ∈ S17.calL0Star D 5) (h68 : S17.R17_68At D V₀ V) :
    barImage D.M (UC22.conjClosure D.M L) = CFSG.layer (Bar2 D.M) ∧
      CFSG.layer (Bar2 D.M) ≤
        CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, -, hP5, hHinf⟩ := h68 5 c.h5 L hL _ rfl hX0 c.hAlt
  have hXo : UC22.conjClosure D.M L ≤ oTwoEOf D.M := by
    rw [c.hX]; exact sup_le (le_oTwoEOf_of_mem_calC c.hL) (le_oTwoEOf_of_mem_calC c.hL')
  have hXH : UC22.conjClosure D.M L ≤ Hinf (oTwoEOf D.M) := uc22p21c_le_Hinf hXo c.perfect
  have hHbar := barImage_Hinf_oTwoEOf D.M
  have hlayP5 : CFSG.layer (Bar2 D.M) ≤
      CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)) := by
    rw [← hHbar, ← s13_barImage_self D.M, ← s13_barImage_opp Nat.prime_five le_rfl]
    exact barImage_mono hHinf
  obtain ⟨e, -, ⟨eP⟩⟩ := hP5
  have hlaycard : Nat.card (CFSG.layer (Bar2 D.M)) ≤ 3600 := by
    set P5 := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
    have hperf : ⁅(CFSG.layer (Bar2 D.M)).subgroupOf P5, (CFSG.layer (Bar2 D.M)).subgroupOf P5⁆ =
        (CFSG.layer (Bar2 D.M)).subgroupOf P5 := by
      apply Subgroup.map_injective P5.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hlayP5]
      exact CFSG.LocalCores.layer_perfect
    have h := CFSG.GroupTheory.card_le_of_isPerfect_of_mulEquiv eP hperf
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlayP5).toEquiv] at h
  have hXcard : Nat.card (barImage D.M (UC22.conjClosure D.M L)) = 3600 := by
    obtain ⟨eX⟩ := c.isA5xA5_barImage
    rw [Nat.card_congr eX.toEquiv, Nat.card_prod, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hle : barImage D.M (UC22.conjClosure D.M L) ≤ CFSG.layer (Bar2 D.M) :=
    hHbar ▸ barImage_mono hXH
  exact ⟨Subgroup.eq_of_le_of_card_ge hle (hXcard ▸ hlaycard), hlayP5⟩

theorem lp_five_eq_sup_of_ctx1768 (D : Data G) {V₀ V : Subgroup G} {L L' : Subgroup G}
    (c : S17.Ctx1768 D L L') (hL : L ∈ S17.calLp D 5)
    (hX0 : UC22.conjClosure D.M L ∈ S17.calL0Star D 5) (h68 : S17.R17_68At D V₀ V) :
    S17.Lp D 5 = L ⊔ L' := by
  classical
  have hXlay := (barImage_eq_layer_of_ctx1768 D c hL hX0 h68).1
  have hLpX : S17.Lp D 5 ≤ UC22.conjClosure D.M L := by
    unfold S17.Lp Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxo, k, hk⟩ := hx
    obtain ⟨hxM, hxl⟩ := uc22p21c_mem_barPreimage.1 hxo
    exact s13_mem_of_barImage_of_pPart c.conjClosure_le c.normal Nat.prime_five (by norm_num) hxM
      ⟨k, hk ▸ pow_orderOf_eq_one x⟩ (hXlay.symm ▸ hxl)
  have hle : ∀ {J : Subgroup G}, J ∈ calC D.M → IsAlt (Bar2 J) 5 → J ≤ S17.Lp D 5 := by
    intro J hJ hA
    have hopp : Opp 5 J = J := S17.opp_eq_self_of_calC hJ (isSimpleGroup_bar2_of_isAlt_five hA)
      Nat.prime_five (by norm_num) (by rw [card_bar2_of_isAlt_five hA]; norm_num)
    rw [← hopp]
    unfold S17.Lp Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact Subgroup.closure_mono fun x hx => ⟨le_oTwoEOf_of_mem_calC hJ hx.1, hx.2⟩
  exact le_antisymm (hLpX.trans c.hX.le) (sup_le (hle c.hL c.hAlt) (hle c.hL' c.hAlt'))

theorem sp_five_ne_bot_of_ctx1768 (D : Data G) {V₀ V : Subgroup G} {L L' : Subgroup G}
    (c : S17.Ctx1768 D L L') (hL : L ∈ S17.calLp D 5)
    (hX0 : UC22.conjClosure D.M L ∈ S17.calL0Star D 5) (h68 : S17.R17_68At D V₀ V) :
    S17.Sp D 5 ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hXlay, hlayP5⟩ := barImage_eq_layer_of_ctx1768 D c hL hX0 h68
  have hLp : S17.Lp D 5 = UC22.conjClosure D.M L :=
    (lp_five_eq_sup_of_ctx1768 D c hL hX0 h68).trans c.hX.symm
  obtain ⟨-, -, ⟨e, he1, ⟨eP⟩⟩, -⟩ := h68 5 c.h5 L hL _ rfl hX0 c.hAlt
  set P5 := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  have : Fact (1 < 5 ^ e) := ⟨Nat.one_lt_pow (by omega) (by norm_num)⟩
  let g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) × Multiplicative (ZMod (5 ^ e)) :=
    (1, 1, Multiplicative.ofAdd 1)
  have hg1 : g ≠ 1 := by
    intro h
    have h2 : (Multiplicative.ofAdd (1 : ZMod (5 ^ e))) = 1 := congrArg (fun x => x.2.2) h
    exact one_ne_zero (Multiplicative.ofAdd.injective (h2.trans ofAdd_zero.symm))
  have hgpow : g ^ (5 ^ e) = 1 := by
    have h3 : (Multiplicative.ofAdd (1 : ZMod (5 ^ e))) ^ (5 ^ e) = 1 := by
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]
    simp only [g, Prod.pow_mk, one_pow, h3]
    rfl
  have hgcomm : ∀ q, g * q = q * g := by
    intro q
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [g, mul_comm]
  set z : ↥P5 := eP.symm g
  have hz1 : z ≠ 1 := fun h => hg1 (by simpa [z] using congrArg eP h)
  have hzpow : z ^ (5 ^ e) = 1 := by
    rw [show z = eP.symm g from rfl, ← map_pow, hgpow, map_one]
  have hzcomm : ∀ q : ↥P5, z * q = q * z := by
    intro q
    apply eP.injective
    rw [map_mul, map_mul, show eP z = g from eP.apply_symm_apply g, hgcomm]
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D.M) (z : Bar2 D.M)
  have hm5 : m ^ (5 ^ e) ∈ CFSG.pCore 2 ↥D.M := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥D.M), MonoidHom.mem_ker, map_pow, hm]
    exact_mod_cast congrArg Subtype.val hzpow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp CFSG.pCore_isPGroup)
    (⟨m ^ (5 ^ e), hm5⟩ : ↥(CFSG.pCore 2 ↥D.M))
  have ha' : orderOf (m ^ (5 ^ e)) = 2 ^ a :=
    (Subgroup.orderOf_coe (⟨m ^ (5 ^ e), hm5⟩ : ↥(CFSG.pCore 2 ↥D.M))).trans ha
  set y : ↥D.M := m ^ (2 ^ a)
  have hy5 : y ^ (5 ^ e) = 1 := by
    rw [show y = m ^ (2 ^ a) from rfl, ← pow_mul, mul_comm, pow_mul, ← ha', pow_orderOf_eq_one]
  have hπy : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y = ((z ^ (2 ^ a) : ↥P5) : Bar2 D.M) := by
    rw [show y = m ^ (2 ^ a) from rfl, map_pow, hm]; rfl
  have hza : z ^ (2 ^ a) ≠ 1 := by
    intro h
    have h1 : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf z ∣ 5 ^ e := orderOf_dvd_of_pow_eq_one hzpow
    have hcop : Nat.Coprime (2 ^ a) (5 ^ e) := Nat.Coprime.pow _ _ (by norm_num)
    have h3 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact hz1 (orderOf_eq_one_iff.mp h3)
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have hy : y = 1 := Subtype.ext h
    rw [hy, map_one] at hπy
    exact hza (Subtype.ext (by exact_mod_cast hπy.symm))
  have hnormLp : D.M ≤ normalizer (S17.Lp D 5 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (S17.Lp_le_M D 5)).mp (s13_Lp_normal D.M 5)
  have hyM : (y : G) ∈ D.M := y.2
  have hcent : (y : G) ∈ S17.centSection D.M (S17.Lp D 5) (pCoreOf 2 (S17.Lp D 5)) := by
    refine ⟨hyM, hnormLp hyM,
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (S17.Lp D 5) (hnormLp hyM),
      fun x hx => ?_⟩
    have hxM : x ∈ D.M := S17.Lp_le_M D 5 hx
    have hwLp : (y : G) * x * (y : G)⁻¹ * x⁻¹ ∈ S17.Lp D 5 :=
      (S17.Lp D 5).mul_mem ((Subgroup.mem_normalizer_iff.mp (hnormLp hyM) x).mp hx)
        ((S17.Lp D 5).inv_mem hx)
    have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ ∈ P5 := by
      apply hlayP5
      rw [← hXlay, ← hLp]
      exact uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx, rfl⟩
    have hwO2 : (y : G) * x * (y : G)⁻¹ * x⁻¹ ∈ pCoreOf 2 D.M := by
      have hw : y * ⟨x, hxM⟩ * y⁻¹ * ⟨x, hxM⟩⁻¹ ∈ CFSG.pCore 2 ↥D.M := by
        rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥D.M), MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hπy]
        have hc := congrArg Subtype.val (Commute.pow_left (hzcomm ⟨_, hxbar⟩) (2 ^ a)).eq
        simp only [Subgroup.coe_mul] at hc
        rw [hc]; group
      exact (CFSG.mem_openPCoreOf_iff (y * ⟨x, hxM⟩ * y⁻¹ * ⟨x, hxM⟩⁻¹)).2 hw
    refine uc22p21c_le_pCoreOf (P := pCoreOf 2 D.M ⊓ S17.Lp D 5) inf_le_right
      ((uc22p21c_isPGroup_pCoreOf D.M).to_le inf_le_left) ?_ ⟨hwO2, hwLp⟩
    intro k hk w hw
    exact ⟨uc22p21c_conj_mem_pCoreOf_self (S17.Lp_le_M D 5 hk) hw.1,
      (S17.Lp D 5).mul_mem ((S17.Lp D 5).mul_mem hk hw.2) ((S17.Lp D 5).inv_mem hk)⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1
    (orderOf_dvd_of_pow_eq_one
      (show (y : G) ^ (5 ^ e) = 1 by exact_mod_cast congrArg Subtype.val hy5))
  have hmem : (y : G) ∈ S17.Sp D 5 := by
    unfold S17.Sp Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact Subgroup.subset_closure ⟨hcent, k, hk⟩
  intro h
  rw [h] at hmem
  exact hy1 (Subgroup.mem_bot.mp hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
