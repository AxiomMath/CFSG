module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825M
public import CFSG.Quasithin.Vol2.Ch8Sec2L823Div
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalAct
public import CFSG.Quasithin.Background.HFL3PRank
public import CFSG.Quasithin.Background.HFL3Cover

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L824Res

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_inf_centralizer_824 {T L I : Subgroup G} (hfsu : FSU G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G)) {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
    (e : IntMod (fsuV T I) hV ≃* L3Nine.HMod n K)
    (hLe : (autI hV L).map (congrHom e) = L3Nine.img hK) (hne : L3Nine.img hK ≠ ⊥) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    ¬ p ∣ Nat.card ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' p hdvd
  rw [Subgroup.orderOf_mk] at hxo
  set φ : ↥L →* MulAut (L3Nine.HMod n K) := (congrHom e).comp (convHom hV L hLN) with hφ
  have hrange : φ.range = (L3Nine.rho hK).range := by
    rw [hφ, MonoidHom.range_comp, range_convHom]
    exact hLe
  have hQL : pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    refine le_trans ?_ (pCoreOf_sup_le_centralizer_of_fsu hfsu)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hmemQ : ∀ l : ↥L, l ∈ CFSG.pCore 2 ↥L → (l : G) ∈ pCoreOf 2 L := by
    intro l hl
    rw [pCoreOf]
    exact ⟨l, hl, rfl⟩
  have hN : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, convHom_apply,
      (convI_eq_one_iff hV _).mpr (hQL (hmemQ l hl)), map_one]
  have he : ∀ g ∈ (L3Nine.rho hK).ker, g ^ (2 ^ n + 1) = 1 := by
    intro g hg
    have hg' : L3Nine.rhoT hK (Matrix.SpecialLinearGroup.toGL g) = 1 := hg
    obtain ⟨d, hd⟩ := L3Nine.scalar_of_rhoT_eq_one hK hg'
    have hdd := L3Nine.norm_eq_one_of_rhoT_smul hK hd hg'
    have hdq : d ^ (2 ^ n + 1) = 1 := by
      rw [pow_succ, ← SU3.bar_apply, mul_comm]
      exact hdd
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    have hd' : (g : Matrix (Fin 3) (Fin 3) K) = d • 1 := hd
    rw [hd', smul_pow, one_pow, hdq, one_smul]
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith
  have hxk : (⟨x, hx.1⟩ : ↥L) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, convHom_apply,
      (convI_eq_one_iff hV _).mpr hx.2, map_one]
  have h1 := L3Cover.pow_mem_of_mem_ker (CFSG.pCore 2 ↥L) hfsu.quasisimple hK5 φ hN
    (L3Nine.rho hK) hrange (fun h => hne h) he _ hxk
  have h2 : x ^ (2 ^ n + 1) ∈ pCoreOf 2 L := by
    have := hmemQ _ h1
    simpa using this
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, h2⟩
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have h3 : orderOf (x ^ (2 ^ n + 1)) ∣ Nat.gcd (2 ^ a) p := by
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_of_pow_eq_one ?_)
    · have := congrArg Subtype.val ha
      simpa using this
    · rw [← pow_mul, mul_comm, pow_mul, hxp, one_pow]
  have hcop : Nat.gcd (2 ^ a) p = 1 :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hxo] at h4
  exact L3Nine.not_dvd_two_pow_add_one hp hp2 hpq h4

theorem res824L3_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h734 : Stmt7_3_4) (h756 : Stmt7_5_6_two) (hE214 : AS_E_2_14) (htab : HTab82)
    (hL9 : HL3Nine82) (hdiv : Step823L3Div) (hres : Res823L3) : Res824L3 := by
  intro G _ _ T L I hyp h731 h821 hc hcase H h k hH hhH hC n hrow
  by_contra hn1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hLM := isOver_autI_82 hV hNM
  obtain ⟨hkn, -, hrkA4, hrkU, hZeq, -, -⟩ := l3_rk_82 h37 h38 h39 hmod h325 hin h711n h734
    h756 hE214 htab hL9 hdiv hres hyp h731 h821 hrow hH hhH hC hV
  subst hkn
  have hk2 : 2 ≤ k := by have := hrow.1; omega
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hcase
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [← hL0]
    exact le_sup_left.trans hN
  obtain ⟨K, _, _, _, hK, e, hLe, hMe⟩ := exists_model_l3nine hLM hrow.2
  rw [hL0] at hLe
  obtain ⟨-, hhI, -, hZ1, hZc, hSyl, hMIeq, hker, -, hcases, hVZ, hBor, hA7, -, -, -, -, -, -,
    -, -⟩ := hC
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hAel2 := isElemAbelian2_autI hV hAel hAN
  obtain ⟨-, -, -, hL6, -⟩ := hL9 (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤) hLM k
    hrow.1 hrow.2
  have hAL : autI hV (ch82A (fsuV T I) h) ≤ autI hV L := by
    rw [← hL0]
    exact hL6 _ (autI_mono hV le_top) hAel2 (by omega)
  have hcardA : 2 ^ (3 * k) < Nat.card ↥(autI hV (ch82A (fsuV T I) h)) := by
    rw [card_eq_two_pow_rk hAel2, hrkA4]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hfixA : fixV (autI hV (ch82A (fsuV T I) h)) =
      (ch82ZI (fsuV T I) h).comap (E3.valHom hV) := by
    rw [fixV_autI_eq_comap hV hAN, hZeq]
    rfl
  have hcardZ : 2 ^ (3 * k) < Nat.card ↥(fixV (autI hV (ch82A (fsuV T I) h))) := by
    rw [card_eq_two_pow (fun v => IntMod.sq_eq_one v), hrkU]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hI : IsPSL 2 2 k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) ∨
      IsSz k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
    rcases hcases with ⟨h1, -⟩ | hP | hS
    · omega
    · exact Or.inl hP
    · exact Or.inr hS
  have hVZ' : E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) (fsuV T I) ≤
      E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
        (T ⊓ ch82I (fsuV T I) h) := by
    rw [hVZ]
    exact inf_le_left
  have hK2 : IsPGroup 2 ↥(kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (ch82I (fsuV T I) h)
  obtain ⟨X, hXMI, hXcyc, hXc, hXK⟩ := exists_cartan_82 hK2 hSyl hBor hk2 hI
  obtain ⟨x, hxX, -, hxo⟩ := exists_zpowers_eq_82 hXcyc
  rw [hXc] at hxo
  have hNV : fsuM T L ⊓ ch82I (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hMIeq]
    exact inf_le_right
  have hXN : X ≤ Subgroup.normalizer (fsuV T I : Set G) := hXMI.trans hNV
  have hnt : Nontrivial (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
    rcases hI with hP | hS
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 k hP).1
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 k hS).1
  have hV1 := star_ne_bot_82 hhI hker hnt
  have hodd : Odd (Nat.card ↥X) := by
    rw [hXc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hf : ∀ y ∈ X, y ∈ Subgroup.centralizer (fsuV T I : Set G) → y = 1 := by
    intro y hy hyc
    rcases hI with hP | hS
    · exact eq_one_of_cent_cartan_82 hk2 hP hSyl hBor hVZ' hV1 hXMI hXK hodd hy hyc
    · exact eq_one_of_cent_cartan_sz_82 hV hS hV1 hXMI hXK hodd hy hyc
  have hxN : x ∈ Subgroup.normalizer (fsuV T I : Set G) := hXN hxX
  set xb := convI hV ⟨x, hxN⟩ with hxb
  have hxbo : orderOf xb = 2 ^ k - 1 := (orderOf_convI_82 hV hXN hf hxX).trans hxo
  have hZx : fixV (autI hV (ch82A (fsuV T I) h)) ≤ fixV (Subgroup.zpowers xb) := by
    rw [hfixA]
    intro v hv
    rw [mem_fixV_zpowers_iff]
    apply Subtype.ext
    show (convI hV ⟨x, hxN⟩ v).val = v.val
    rw [convI_apply_val]
    have hxI : x ∈ ch82I (fsuV T I) h := (hXMI hxX).2
    have hvZ : E3.valHom hV v ∈ ch82ZI (fsuV T I) h := hv
    have h1 := Subgroup.mem_centralizer_iff.mp (hZc hvZ) x hxI
    have h2 : E3.valHom hV v = v.val := rfl
    rw [h2] at h1
    rw [h1, mul_inv_cancel_right]
  have hNodd : Odd (2 ^ k - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hg := Nat.gcd_dvd_left (2 ^ k - 1) (2 * k)
  have hg2 := Nat.gcd_dvd_right (2 ^ k - 1) (2 * k)
  set N₂ := (2 ^ k - 1) / Nat.gcd (2 ^ k - 1) (2 * k) with hN₂
  have hxbo2 : orderOf (xb ^ (2 * k)) = N₂ := by rw [orderOf_pow' xb (by omega), hxbo]
  have hxo2 : orderOf (x ^ (2 * k)) = N₂ := by rw [orderOf_pow' x (by omega), hxo]
  have hk4 : k + 2 ≤ 2 ^ k := by
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
    have := Nat.lt_two_pow_self (n := i)
    rw [pow_add]
    omega
  have hN₂1 : N₂ ≠ 1 := by
    intro h1
    have hgN : Nat.gcd (2 ^ k - 1) (2 * k) = 2 ^ k - 1 := by
      have := Nat.div_mul_cancel hg
      rw [← hN₂, h1, one_mul] at this
      exact this
    rw [hgN] at hg2
    have hNk : 2 ^ k - 1 ∣ k :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hNodd) hg2
    have := Nat.le_of_dvd (by omega) hNk
    omega
  obtain ⟨p, hp, hpN₂⟩ := Nat.exists_prime_and_dvd hN₂1
  have : Fact p.Prime := ⟨hp⟩
  have hN₂0 : N₂ ≠ 0 := by
    rw [← hxbo2]
    exact (orderOf_pos _).ne'
  have hpN : p ∣ 2 ^ k - 1 := hpN₂.trans (Nat.div_dvd_of_dvd hg)
  have hp2 : p ≠ 2 := fun h2 => by
    rw [h2] at hpN
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hpN)
  have hq0 : N₂ / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN₂0) hpN₂)
    hp.pos).ne'
  have hord : ∀ {M : Type _} [Monoid M] (z : M), orderOf (z ^ (2 * k)) = N₂ →
      orderOf (z ^ (2 * k * (N₂ / p))) = p := by
    intro M _ z hz
    rw [pow_mul, orderOf_pow' _ hq0, hz, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpN₂),
      Nat.div_div_self hpN₂ hN₂0]
  set y := x ^ (2 * k * (N₂ / p)) with hy
  have hyo : orderOf y = p := hord x hxo2
  have hyN : y ∈ Subgroup.normalizer (fsuV T I : Set G) := pow_mem hxN _
  have hyb : convI hV ⟨y, hyN⟩ = xb ^ (2 * k * (N₂ / p)) := by
    rw [hxb, ← map_pow]
    rfl
  have hybo : orderOf (convI hV ⟨y, hyN⟩) = p := by rw [hyb]; exact hord xb hxbo2
  have hxbM : congrHom e xb ∈ L3Nine.norm hK :=
    hMe ⟨xb, convI_mem_autI hV (Subgroup.mem_top x) hxN, rfl⟩
  have hlin : congrHom e (convI hV ⟨y, hyN⟩) ∈ L3Nine.linImg hK := by
    rw [hyb, pow_mul, map_pow, map_pow]
    exact pow_mem (L3Nine.pow_mem_linImg (by omega) hK hxbM) _
  have hyom : orderOf (congrHom e (convI hV ⟨y, hyN⟩)) = p := by
    rw [orderOf_injective _ (congrHom_injective e), hybo]
  set Am := (autI hV (ch82A (fsuV T I) h)).map (congrHom e) with hAm
  have hAmL : Am ≤ L3Nine.img hK := by
    rw [← hLe]
    exact Subgroup.map_mono hAL
  have hAme : IsElemAbelian2 Am := (isElemAbelian2_map_congrHom e).2 hAel2
  have hcardAm : 2 ^ (3 * k) < Nat.card Am := by
    rw [hAm, card_map_congrHom]
    exact hcardA
  set Zm := (fixV (autI hV (ch82A (fsuV T I) h))).map e.toMonoidHom with hZm
  have hZmA : Zm ≤ fixV Am := by rw [hAm, fixV_map_congrHom]
  have hZmy : Zm ≤ fixV (Subgroup.zpowers (congrHom e (convI hV ⟨y, hyN⟩))) := by
    rw [← MonoidHom.map_zpowers, fixV_map_congrHom]
    refine Subgroup.map_mono (hZx.trans (fixV_anti ?_))
    rw [Subgroup.zpowers_le, hyb]
    exact pow_mem (Subgroup.mem_zpowers xb) _
  have hcardZm : 2 ^ (3 * k) < Nat.card Zm := by
    rw [hZm, Subgroup.card_map_of_injective e.injective]
    exact hcardZ
  obtain ⟨hnotI, hrk3⟩ := L3Nine.three_le_pRank_of_large (by omega) hK hAmL hAme hcardAm hp2 hpN
    hlin hyom hZmA hZmy hcardZm
  have hne : L3Nine.img hK ≠ ⊥ := by
    intro hbot
    have h1 : Am = ⊥ := le_bot_iff.mp (hbot ▸ hAmL)
    rw [h1, Subgroup.card_bot] at hcardAm
    have : 1 ≤ 2 ^ (3 * k) := Nat.one_le_two_pow
    omega
  have hyL : y ∈ Subgroup.normalizer (L : Set G) := by
    have := hNM hyN
    rwa [fsuM, hL0] at this
  have hynot : convI hV ⟨y, hyN⟩ ∉ autI hV L := by
    intro hmem
    apply hnotI
    rw [← hLe]
    exact ⟨_, hmem, rfl⟩
  have hyp1 : y ^ p = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  set M' := L ⊔ Subgroup.zpowers y with hM'
  have hM'N : M' ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le hLN (Subgroup.zpowers_le.mpr hyN)
  have hC' : M' ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
      L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    le_inf (L3Cover.sup_inf_centralizer_le hV hLN hyN hyL hp hyp1 hynot) inf_le_right
  have hpC : ¬ p ∣ Nat.card ↥(M' ⊓ Subgroup.centralizer (fsuV T I : Set G)) := fun hd =>
    not_dvd_card_inf_centralizer_824 hyp.fsu hTL hV hLN hk2 hK e hLe hne hp hp2 hpN
      (hd.trans (Subgroup.card_dvd_of_le hC'))
  have hVne : fsuV T I ≠ ⊥ := fun hb => hZ1 (le_bot_iff.mp (hb ▸ inf_le_left))
  have hVp : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have h1 := L3Cover.pRank_autI_le_of_not_dvd hV hM'N hpC
  have h2 : CFSG.Open.pRank p M' ≤ 2 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hM'N).trans
      (pRank_le_two_of_isTwoLocal hyp.fsu.qtke ⟨fsuV T I, hVne, hVp, rfl⟩ hp hp2)
  have h3 : 3 ≤ CFSG.Open.pRank p (autI hV M') := by
    refine hrk3.trans ?_
    have hle : L3Nine.img hK ⊔ Subgroup.zpowers (congrHom e (convI hV ⟨y, hyN⟩)) ≤
        (autI hV M').map (congrHom e) := by
      refine sup_le ?_ ?_
      · rw [← hLe]
        exact Subgroup.map_mono (autI_mono hV le_sup_left)
      · rw [Subgroup.zpowers_le]
        exact ⟨_, convI_mem_autI hV (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hyN, rfl⟩
    refine (CFSG.SectionRank.pRank_mono hp.one_lt hle).trans ?_
    have h4 := CFSG.SectionRank.pRank_le_map hp.one_lt (MulAut.congr e).symm.toMonoidHom
      (MulAut.congr e).symm.injective ((autI hV M').map (congrHom e))
    have h5 : ((autI hV M').map (congrHom e)).map (MulAut.congr e).symm.toMonoidHom =
        autI hV M' := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id (autI hV M')
      ext φ v
      simp
    rwa [h5] at h4
  omega

end L824Res

end CFSG.Quasithin.H13
