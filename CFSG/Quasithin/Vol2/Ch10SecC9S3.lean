module

public import CFSG.Quasithin.Vol2.Ch10SecC9S3a
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Vol2.Ch10SecC9Comp
public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx
public import CFSG.Quasithin.Vol2.Ch10SecCFacts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem cV1_eq (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    cV1 T L I = (Subgroup.centralizer (L : Set G)).subgroupOf (fsuUL T L I) := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, -, -⟩ := hdec t ht htn
  ext ⟨v, hv⟩
  simp only [Subgroup.mem_subgroupOf]
  constructor
  · exact fun h => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (SecA.le_fsuL0 T L)) h
  · intro h
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact mem_centralizer_sup h (hV1 hv)

theorem modCase_of (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1027 : Stmt10_2_7) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ModCase L (fsuUL T L I) := by
  have heq := cV1_eq h37 h38 hyp h1011 ht htn
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hc : IsMulCommutative ↥(fsuUL T L I) :=
    ⟨⟨fun a b => Subtype.ext (fsuVM_comm hyp (hV1V a.2) (hV1V b.2))⟩⟩
  obtain ⟨-, -, -, hcases⟩ := h1011 G T L I hyp
  rcases hcases with ⟨n, hn, hK, hc1, hnat⟩ | ⟨hiso, hc1, halt⟩ | ⟨hiso, hc1, hnat⟩ |
    ⟨n, hn, hK, hc1, horth⟩ | ⟨hiso, s, -, hsN, W, hW⟩ | h6 | ⟨n, hSz, hc1, hsz⟩
  · exact ⟨hc1, Or.inl ⟨n, hn, hK, heq ▸ hnat⟩⟩
  · exact ⟨hc1, Or.inr (Or.inl ⟨hiso, halt⟩)⟩
  · exact ⟨hc1, Or.inr (Or.inr (Or.inl ⟨hiso, heq ▸ hnat⟩))⟩
  · exact ⟨hc1, Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hK, horth⟩)))⟩
  · exact ⟨hc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hiso, s, hsN, W, hW⟩))))⟩
  · exact absurd h6 (h1027 G T L I hyp).1
  · exact ⟨hc1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hSz, hsz⟩))))⟩

theorem card_sub_one_dvd_card_SL (F : Type) [Field F] [Finite F] :
    Nat.card F - 1 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card (α := F)]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  set q := Fintype.card F with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hsq : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, pow_two]
  rcases Nat.eq_or_lt_of_le hq1 with h | h
  · rw [← h]
    simp
  · have hpos : 0 < q - 1 := by omega
    rw [hsq, ← mul_assoc, Nat.mul_div_cancel _ hpos]
    have key : ∀ r : ℕ, (r + 1) ^ 2 - 1 = r * (r + 2) := fun r => by
      rw [show (r + 1) ^ 2 = r * (r + 2) + 1 by ring, Nat.add_sub_cancel]
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h1 := key (q - 1)
      rwa [Nat.sub_add_cancel hq1, show q - 1 + 2 = q + 1 by omega] at h1
    rw [this]
    exact Dvd.dvd.mul_right (Dvd.intro _ rfl) _

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem L_mem_lFamily : L ∈ lFamily (T ⊓ Subgroup.centralizer ({w} : Set G)) :=
  cComp_mem_of_le c.hyp.fsu.maximal.1.2.1 le_sup_left (sup_le_sup_left inf_le_left _)

theorem le_normalizer_fsuUL' (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) :
    L ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  sup_le (le_normalizer_fsuUL T L I) (SecA.le_normalizer_commutator
    (fun _ hs => SecA.le_normalizer_fsuVM T L I hs.1)
    (fun _ hs => ((c.Tw_le_T1 h37 h38) hs).2))

theorem false_of_isQuasisimple
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1013 : Stmt10_1_3)
    (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7) (hK1 : FactK1) (hK3 : FactK3Sp4)
    (hSp4 : ASInputs.AS_I_1_3_Sp4) (hq : CFSG.Open.IsQuasisimple ↥J) : False := by
  have hyp := c.hyp
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hH := pCoreOf_centralizer_ne_bot c.w_ne_one c.w_sq
  have hSQ := InternalSec.sqtkGroup_of_localSQTK hK hH
  have hTwL : T ⊓ Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (c.Tw_le_T1 h37 h38).trans inf_le_right
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2, -⟩ := hdec t c.ht c.htn
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hVL : fsuVM T L I ≤ Subgroup.normalizer (L : Set G) :=
    (fsuVM_le_Q hyp).trans (Q_le_T1 h37 h38 hyp h1011) |>.trans inf_le_right
  have hV1L : fsuUL T L I ≤ L := by
    rw [fsuUL, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer hVL
  have hV1el : IsElemAbelian 2 (fsuUL T L I) :=
    B2F.isElemAbelian_mono hV1V (SecA.isElemAbelian_fsuVM hyp)
  have hJN : J ⊓ Subgroup.normalizer (fsuUL T L I : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun g hg => fsuM_inf_centralizer_le h37 h38 hyp c.ht c.htn c.claim.1 c.claim.2.1
      ⟨(h1026 G T L I hyp).2.1 L (Or.inl rfl) hg.2, c.J_le hg.1⟩
  have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (fsuUL T L I : Set G) :=
    (pCoreOf_L_le_centralizer hyp h1011).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV1V))
  rcases hK1 G _ _ J L _ hSQ hH c.sylow c.mem hq c.L_mem_lFamily c.le c.ne hTwL hsimp hV1L hV1el
    (c.le_normalizer_fsuUL' h37 h38) (commutator_fsuUL_eq hyp) hOC hJN
    (modCase_of h37 h38 hyp h1011 h1027 c.ht c.htn) with hC | ⟨n, hn, F, _, _, hF, ⟨eJ⟩, ⟨eL⟩⟩
  ·
    have hLtN : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      (SecA.conjugate_le_fsuL0 c.ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
    have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
      commutator_le_left_of_le_normalizer hLtN
    have hV2C : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ Subgroup.centralizer (J : Set G) := by
      intro x hx
      refine hC ⟨⟨SecA.fsuVM_le_T hyp (hV2V hx), ?_⟩, hV2 hx⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (fsuVM_comm hyp (hV2V hx) c.w_mem_V)
    apply c.not_le
    refine (Subgroup.le_centralizer_iff.mp hV2C).trans ?_
    exact (Subgroup.centralizer_le_normalizer _).trans
      ((h1026 G T L I hyp).2.1 _ (Or.inr ⟨t, c.ht, c.htn, rfl⟩))
  ·
    let φ : ↥J →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
      eJ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J))
    have hφs : Function.Surjective φ :=
      eJ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hφk : φ.ker ≤ Subgroup.center ↥J := by
      intro x hx
      have h1 : eJ (QuotientGroup.mk' (Subgroup.center ↥J) x) = 1 := hx
      rw [MulEquiv.map_eq_one_iff] at h1
      exact (QuotientGroup.eq_one_iff x).mp h1
    have hφi := hSp4 n hn F hF ↥J φ hφs hq.1 hφk
    obtain ⟨X, hXJ, hXcard, hXL, hXc⟩ := hK3 G _ _ J L _ n F hSQ hH c.sylow c.mem c.L_mem_lFamily
      c.le c.ne hTwL hsimp hV1L hV1el (c.le_normalizer_fsuUL' h37 h38) (commutator_fsuUL_eq hyp)
      hOC hJN (modCase_of h37 h38 hyp h1011 h1027 c.ht c.htn) hn hF
      ⟨MulEquiv.ofBijective φ ⟨hφi, hφs⟩⟩ ⟨eL⟩
    have hXM : X ≤ fsuM T L := hXJ.trans (inf_le_right.trans (h1026 G T L I hyp).2.2)
    have hXL0 : X ≤ fsuL0 T L := by
      refine le_fsuL0_of_dvd hyp h1013 hXM (dvd_of_eq hXcard) fun p hp hpN => ⟨?_, ?_⟩
      · rintro rfl
        have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
        have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      · rw [Nat.card_congr eL.toEquiv]
        exact hpN.trans (hF ▸ card_sub_one_dvd_card_SL F)
    have hXC := le_centralizer_of_le_fsuL0 h37 h38 hyp h1011 c.ht c.htn hXL0 hXL
    have hXb : X = ⊥ := le_bot_iff.mp (hXc ▸ le_inf le_rfl hXC)
    rw [hXb, Subgroup.card_bot] at hXcard
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
