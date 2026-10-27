module

public import CFSG.Quasithin.EmptyFaithful.S1421QA26Mod
public import CFSG.Quasithin.EmptyFaithful.S1421QA26B5
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Defs
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Sub
public import CFSG.Quasithin.EmptyFaithful.S1421QA23U33
public import CFSG.Quasithin.EmptyFaithful.S1421QA15SLe
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Setup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.QA26

theorem five_dvd_benderOrder_of_le {n i : ℕ} (hn : 2 ≤ n) (hi : i = 1 ∨ i = 2 ∨ i = 3)
    (hodd : i = 2 → n % 2 = 1) (h : QA19.benderOrder n i ≤ 360) : 5 ∣ QA19.benderOrder n i := by
  have h2 := QA19.two_pow_le_benderOrder (by omega : 1 ≤ n) i
  have hn8 : n ≤ 8 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  revert h hodd
  interval_cases n <;> rcases hi with rfl | rfl | rfl <;> decide

namespace QA26

section Generic

variable {V : Type} [CommGroup V]

theorem commV_apply_mem_of_normalizes {K : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) {u : V} (hu : u ∈ commV K) : g u ∈ commV K :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hg hu

end Generic

end QA26

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.exists_order_five
    (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hA7 : IsAlt 7 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) :
    ∃ x : ↥L ⧸ CFSG.pCore 2 ↥L, x ∈ modO2Image L K1 ∧
      orderOf (QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) x) = 5 := by
  have : IsSimpleGroup ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    hq.2.1
  obtain ⟨P, hKP, hUP, hP⟩ := QA23.exists_overgroup_bar hq c.bar_sup_ne_top
  obtain ⟨h60, hcard, hm, hfac, -⟩ := QA23.overgroup_numbers hP hKP hUP
    (QA23.sixty_le_card_map_center c.bar_perfect c.bar_ne_bot)
  have hN : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 2520 := by
    obtain ⟨e⟩ := hA7
    rw [Nat.card_congr e.toEquiv, CFSG.QuasithinUnique.Bridge.card_alt_seven]
  rw [hN] at hcard hfac
  have hm7 : 7 ≤ P.index := by
    by_contra hlt
    push Not at hlt
    have h1 : (P.index).factorial ≤ 720 := by
      have : (P.index).factorial ≤ (6 : ℕ).factorial := Nat.factorial_le (by omega)
      simpa [Nat.factorial] using this
    have h2 := Nat.le_of_dvd (Nat.factorial_pos _) hfac
    omega
  have hPle : Nat.card P ≤ 360 := by
    by_contra hgt
    push Not at hgt
    have : 361 * 7 ≤ Nat.card P * P.index := Nat.mul_le_mul hgt hm7
    omega
  obtain ⟨n, i, hn, hi, hodd, hdvd⟩ := QA23.benderOrder_dvd_card_map_center c.bar_bender
  have hdvdP : Nat.card ↥((modO2Image L K1).map (QuotientGroup.mk' (Subgroup.center
      (↥L ⧸ CFSG.pCore 2 ↥L)))) ∣ Nat.card P := Subgroup.card_dvd_of_le hKP
  have h5 := five_dvd_benderOrder_of_le hn hi hodd
    ((Nat.le_of_dvd (by omega) (hdvd.trans hdvdP)).trans hPle)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨q, hq5⟩ := exists_prime_orderOf_dvd_card' (G := ↥((modO2Image L K1).map
    (QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))))) 5 (h5.trans hdvd)
  obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 q.2
  refine ⟨x, hx, ?_⟩
  rw [hxq, Subgroup.orderOf_coe]
  exact hq5

end S1421

open scoped IsMulCommutative in
theorem core3HeA7_of_inputs (h56 : AsB56) (h210 : Lemma14210)
    (h209 : Lemma14209Used) : Core3HeA7 := by
  intro G _ _ T M H K1 L M₁ c hchar hq hY hA7
  set S := S1421.sOf T K1 with hSdef
  have hG0 := c.g0Of_eq_of_le hY
  have hLX : L ∈ cComp (L ⊔ S) := hG0 ▸ c.mem
  have hSyl : IsSylowTwoOf S (L ⊔ S) := hG0 ▸ S1421.isSylowTwoOf_g0 c.inM c.sylow
  have hX : CharTwo (L ⊔ S) := hG0 ▸ hchar
  have hpcX : pCoreOf 2 (L ⊔ S) ≠ ⊥ := hG0 ▸ c.pCore_ne
  have hred := C1GN.isTwoReducedIn_VZ hX hSyl
  set W := VZ S (L ⊔ S) with hWdef
  set K := autOn L W with hKdef
  have hVe : IsElemAbelian 2 W := hred.2.2.1
  have : IsMulCommutative ↥W := hVe.1
  have hO2 := LJ.pCoreOf_le_centralizer hred
  have hLnV : ¬ L ≤ Subgroup.centralizer (W : Set G) := by
    intro hLV
    apply c.not_le_mc
    intro x hx
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.omegaOneCenter_le_vz) (hLV hx)
  have hSQ : SQTKGroup ↥(L ⊔ S) :=
    sqtkGroup_of_pCoreOf_ne_bot c.st.hyp.qtke c.st.hyp.simple c.st.hyp.nonabelian hpcX
  have hJX : thompsonJ S ≤ thompsonJ (L ⊔ S) := thompsonJ_le_thompsonJ_of_isSylowTwoOf hSyl
  have hJ : ⁅L, thompsonJ S⁆ = L := c.commutator_thompsonJ_eq h210 hq hY
  have hLJ : L ≤ thompsonJ (L ⊔ S) := by
    have h1 : ⁅L, thompsonJ S⁆ ≤ thompsonJ (L ⊔ S) := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      have hl' : l ∈ Subgroup.normalizer (thompsonJ (L ⊔ S) : Set G) :=
        GammaExtra.normalizer_le_normalizer_thompsonJ (L ⊔ S)
          (Subgroup.le_normalizer ((le_sup_left : L ≤ L ⊔ S) hl))
      have h2 := (Subgroup.mem_normalizer_iff.mp hl' j).1 (hJX hj)
      rw [commutatorElement_def]
      exact (thompsonJ (L ⊔ S)).mul_mem h2 ((thompsonJ (L ⊔ S)).inv_mem (hJX hj))
    rwa [hJ] at h1
  have hLN : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hred.2.1
  have hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) := fun x hx =>
    hO2 (S151S5.pCoreOf_le_of_isSubnormal' (subnormal_of_mem_cComp hLX) hx)
  have hle : CFSG.pCore 2 ↥L ≤ (InternalSec.autOnHom hLN).ker := by
    intro x hx
    rw [InternalSec.mem_ker_autOnHom]
    exact hO2L ⟨x, by assumption, rfl⟩
  let ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L (W)) :=
    QuotientGroup.lift _ (InternalSec.autOnHom hLN) hle
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLN y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hne : ∃ k, ρ k ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hLnV
    intro l hl
    have h1 : ρ (QuotientGroup.mk ⟨l, hl⟩) = 1 := hall _
    have h2 : (InternalSec.autOnHom hLN) ⟨l, hl⟩ = 1 := h1
    exact (InternalSec.mem_ker_autOnHom hLN ⟨l, hl⟩).1 h2
  have hY' : CFSG.IsQuasisimple ↥(autOn L (W)) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hρs hne
  have hker : ρ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hne
  obtain ⟨xb, hxbK, hxb5⟩ := c.exists_order_five hq hA7
  obtain ⟨eA⟩ := hA7
  have hIN : L ⊔ S ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := le_sup_right.trans hIN
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    ((le_sup_right : S ≤ L ⊔ S).trans hG0.symm.le).trans c.g0Of_le_normalizer
  have hIL : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSL
  have hV : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hVe.2 v v.2)
  obtain ⟨cq⟩ := lred3_cq_of_quasisimple hq hY' ρ hρs
  have hA7K : QA26.IsA7Cover (autOn L W) := ⟨cq.symm.trans eA⟩
  set J := ffJ (autOn (L ⊔ S) W) with hJdef
  have hKJ : K ≤ J :=
    (InternalSec.autOn_le_autOn_of_le hLJ).trans (SBc3.autOn_thompsonJ_le_ffJ hVe hred.1 hIN)
  have hKn : ∀ x ∈ autOn (L ⊔ S) W, ∀ k ∈ K, x * k * x⁻¹ ∈ K :=
    InternalSec.autOn_normal_of (U := W) hIL
  have hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk => hKn x (B6.ffJ_le _ hx) k hk
  have hKne : K ≠ ⊥ := QA26.ne_bot_of_quasisimple hY'
  have hJne : J ≠ ⊥ := fun h => hKne (le_bot_iff.1 (h ▸ hKJ))
  have hO2' : pCoreOf 2 (autOn (L ⊔ S) W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hb : B53Hyp J := InternalSec.b53Hyp_ffJ_autOn hIN hSQ hO2'
  obtain ⟨hsplit, hmod⟩ := QA26.a7ModData_of_b56 h56 hV hJne hb hKJ hn hY' hA7K
  obtain ⟨eK⟩ := QA26.equiv_alt7_of_modData hKne hmod
  have hcardK : Nat.card ↥K = 2 ^ 3 * 315 := by
    rw [Nat.card_congr eK.toEquiv, CFSG.QuasithinUnique.Bridge.card_alt_seven]
    norm_num
  set Ū := autOn (S ⊓ L) W with hŪdef
  have hŪK : Ū ≤ K := InternalSec.autOn_le_autOn_of_le inf_le_right
  let f : ↥L →* ↥K := InternalSec.autOnHom hLN
  have hfs : Function.Surjective f := InternalSec.autOnHom_surjective hLN
  have hP0 : IsSylowTwoOf ((S ⊓ L).subgroupOf L) ⊤ := isSylowTwoOf_top_subgroupOf c.sylow_inf
  have hSylK : IsSylowTwoOf (((S ⊓ L).subgroupOf L).map f) ⊤ :=
    isSylowTwoOf_top_map_of_surjective hP0 f hfs
  have hcard8 : Nat.card ↥(((S ⊓ L).subgroupOf L).map f) = 2 ^ 3 :=
    QA23.card_eq_of_isSylowTwoOf_top hSylK (by norm_num) hcardK
  have hŪeq : (((S ⊓ L).subgroupOf L).map f).map K.subtype = Ū := by
    ext φ
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨k, ⟨l, hl, rfl⟩, rfl⟩
      exact Setup.mem_autOn_iff.2 ⟨⟨l, hLN l.2⟩, Subgroup.mem_subgroupOf.1 hl, rfl⟩
    · intro hφ
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hφ
      exact ⟨f ⟨g, hg.2⟩, ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩, rfl⟩
  have hŪ8 : Nat.card ↥Ū = 8 := by
    rw [← hŪeq, Subgroup.card_map_of_injective K.subtype_injective, hcard8]
    norm_num
  have hŜ2 : IsPGroup 2 ↥(autOn S W) := by
    intro φ
    obtain ⟨g, hgS, hφ⟩ := Setup.mem_autOn_iff.1 φ.2
    obtain ⟨k, hk⟩ := S1421.isPGroup_sOf c.st ⟨(g : G), hgS⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    show (φ : MulAut ↥W) ^ 2 ^ k = 1
    rw [← hφ, ← map_pow, h1, map_one]
  have hŜK : ∀ s ∈ autOn S W, ∀ k ∈ K, s * k * s⁻¹ ∈ K := fun s hs k hk =>
    hKn s (InternalSec.autOn_le_autOn_of_le (le_sup_right : S ≤ L ⊔ S) hs) k hk
  have hSSL : S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hSL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hŜŪ : ∀ s ∈ autOn S W, ∀ k ∈ Ū, s * k * s⁻¹ ∈ Ū :=
    InternalSec.autOn_normal_of (U := W) hSSL
  have hŜU : ∀ s ∈ autOn S W, ∀ u ∈ commV K, s u ∈ commV K := fun s hs u hu =>
    QA26.commV_apply_mem_of_normalizes (hŜK s hs) hu
  have hKU : ∀ k ∈ K, ∀ u ∈ commV K, k u ∈ commV K := fun k hk u hu =>
    QA26.commV_apply_mem_of_normalizes
      (fun k' hk' => K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) hu
  have hWS : W ≤ S :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1
      (isPGroup_of_isElemAbelian hVe)).trans
      (pCoreOf_two_le_of_isSylowTwoOf hSyl)
  have hρl : ∀ l : ↥L, ((ρ (QuotientGroup.mk l) : ↥K) : MulAut ↥W) = Setup.rho W L hLN l :=
    fun l => rfl
  have hfixρ : ∀ u : ↥W, (∀ s ∈ autOn S W, s u = u) →
      ((ρ xb : ↥K) : MulAut ↥W) u = u := by
    intro u hSu
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hxbK
    have hlK1 : (l : G) ∈ K1 := Subgroup.mem_subgroupOf.1 hl
    have hcomm : ∀ g ∈ S, g * (u : G) * g⁻¹ = (u : G) := by
      intro g hg
      have hgmem : conjAct W ⟨g, hSW hg⟩ ∈ autOn S W :=
        Setup.mem_autOn_iff.2 ⟨⟨g, hSW hg⟩, hg, rfl⟩
      have := congrArg Subtype.val (hSu _ hgmem)
      rwa [Setup.coe_conjAct_apply] at this
    have hu_cent : (u : G) ∈ omegaOneCenterOf S := by
      refine Subgroup.subset_closure ⟨⟨hWS u.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩, ?_⟩
      · exact mul_inv_eq_iff_eq_mul.1 (hcomm g hg)
      · simpa using congrArg Subtype.val (hV u)
    have hc := c.oTwoUpper_le_centralizer h209 (c.st.notation_.le_K hlK1)
    have h1 : (u : G) * (l : G) = (l : G) * (u : G) := Subgroup.mem_centralizer_iff.1 hc _ hu_cent
    rw [QuotientGroup.mk'_apply, hρl]
    apply Subtype.ext
    rw [Setup.rho_apply_coe]
    rw [← h1]
    group
  let y : ↥K := ρ xb
  have h5y : 5 ∣ orderOf y := by
    have h1 : (QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) xb) ^ orderOf y = 1 := by
      rw [← map_pow]
      have hm : xb ^ orderOf y ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        exact pow_orderOf_eq_one y
      exact (QuotientGroup.eq_one_iff _).2 (hker hm)
    rw [← hxb5]
    exact orderOf_dvd_of_pow_eq_one h1
  have hypos : 0 < orderOf y := orderOf_pos y
  obtain ⟨t, ht⟩ := h5y
  have ht0 : t ≠ 0 := by
    rintro rfl
    omega
  have hx5 : (y ^ t) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, ← ht]
    exact pow_orderOf_eq_one y
  have hx1 : y ^ t ≠ 1 := pow_ne_one_of_lt_orderOf ht0 (by omega)
  have hx5' : ((y ^ t : ↥K) : MulAut ↥W) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, hx5]
    rfl
  have hx1' : ((y ^ t : ↥K) : MulAut ↥W) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hfix : ∀ u ∈ commV K, (∀ s ∈ autOn S W, s u = u) →
      ((y ^ t : ↥K) : MulAut ↥W) u = u := by
    intro u _ hSu
    have hys : (y : MulAut ↥W) ∈ MulAction.stabilizer (MulAut ↥W) u := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfixρ u hSu
    have := Subgroup.pow_mem _ hys t
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← Subgroup.coe_pow] at this
  exact QA26.false_of_a7Config hKU hsplit hmod hŪK hŪ8 hŜ2 hŜK hŜŪ hŜU (y ^ t).2 hx5' hx1' hfix

end CFSG.Quasithin
