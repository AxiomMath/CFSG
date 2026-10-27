module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zm
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zd

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem eq_of_central_sylow {H C U : Subgroup G} (hCH : C ≤ H)
    (hHC : H ≤ Subgroup.normalizer (C : Set G)) (hUC : U ≤ C) (hU2 : IsPGroup 2 U)
    (hcen : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c) (hodd : ¬ 2 ∣ U.relIndex C)
    (hchar : QuasithinUnique.CharTwo H) : C = U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(U.subgroupOf C) := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUC).symm
  set P : Sylow 2 ↥C := hP2.toSylow hodd with hP
  have hPC : Subgroup.normalizer (P : Set ↥C) ≤ Subgroup.centralizer (P : Set ↥C) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : ((p : ↥C) : G) ∈ U := hp
    exact Subtype.ext (hcen _ g.2 _ hp').symm
  set N := (MonoidHom.transferSylow P hPC).ker with hN
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hPC
  have hcard := hcompl.card_mul_card
  have hPcard : Nat.card ↥(P : Subgroup ↥C) = Nat.card ↥U := by
    show Nat.card ↥(U.subgroupOf C) = _
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv
  have hrel : U.relIndex C * Nat.card ↥U = Nat.card ↥C := by
    have := Subgroup.relIndex_mul_card U C
    rwa [inf_of_le_left hUC] at this
  have hNcard : Nat.card ↥N = U.relIndex C := by
    have hUpos : 0 < Nat.card ↥U := Nat.card_pos
    rw [hPcard] at hcard
    exact Nat.eq_of_mul_eq_mul_right hUpos (hcard.trans hrel.symm)
  have hNodd : ∀ n ∈ N, Odd (orderOf n) := fun n hn => by
    have h1 : orderOf (⟨n, hn⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hNcard] at h1
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr (by omega)) h1
  have hoddN : ∀ g : ↥C, Odd (orderOf g) → g ∈ N := by
    intro g hg
    rw [hN, MonoidHom.mem_ker]
    set y := MonoidHom.transferSylow P hPC g with hy
    obtain ⟨k, hk⟩ := (P.isPGroup') y
    have h1 : orderOf y ∣ orderOf g := orderOf_map_dvd _ g
    have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime (2 ^ k) (orderOf g) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hg)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h2 h1))
  set N' := N.map C.subtype with hN'
  have hmemN' : ∀ x, x ∈ N' ↔ ∃ hx : x ∈ C, Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n.2, ?_⟩
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact hNodd n hn
    · rintro ⟨hx, hxo⟩
      exact ⟨⟨x, hx⟩, hoddN _ (by rwa [Subgroup.orderOf_mk]), rfl⟩
  have hHN' : H ≤ Subgroup.normalizer (N' : Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxC, hxo⟩ := (hmemN' x).mp hx
    refine (hmemN' _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hHC hh) x).mp hxC, ?_⟩
    rw [show h * x * h⁻¹ = MulAut.conj h x from rfl, MulEquiv.orderOf_eq]
    exact hxo
  have hN'1 : ∀ x ∈ N', x = 1 := by
    intro x hx
    obtain ⟨hxC, hxo⟩ := (hmemN' x).mp hx
    have hxH : x ∈ H := hCH hxC
    have hxO : x ∈ pCoreOf 2 H := by
      refine hchar ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have hqH : q ∈ H := pCoreOf_le 2 H hq
      set c := q * x * q⁻¹ * x⁻¹ with hc
      have hc1 : c ∈ N' :=
        Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hHN' hqH) x).mp hx)
          (Subgroup.inv_mem _ hx)
      have hc2 : c ∈ pCoreOf 2 H := by
        have hxq : x * q⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hxH) _).mp
            (Subgroup.inv_mem _ hq)
        have e : c = q * (x * q⁻¹ * x⁻¹) := by rw [hc]; group
        rw [e]
        exact Subgroup.mul_mem _ hq hxq
      have hco := ((hmemN' c).mp hc1).2
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨c, hc2⟩
      have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hc1' : c = 1 := by
        have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
        have hcop : Nat.Coprime (2 ^ k) (orderOf c) :=
          Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hco)
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h2 dvd_rfl))
      calc q * x = c * (x * q) := by rw [hc]; group
        _ = x * q := by rw [hc1', one_mul]
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨x, hxO⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hxo)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h2 dvd_rfl))
  have hN1 : Nat.card ↥N = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩, ⟨1⟩⟩
    have ha := hN'1 _ ⟨a, a.2, rfl⟩
    have hb := hN'1 _ ⟨b, b.2, rfl⟩
    simp only [Subgroup.coe_subtype] at ha hb
    rw [ha, hb]
  rw [hN1] at hNcard
  rw [← hNcard, one_mul] at hrel
  exact (Subgroup.eq_of_le_of_card_ge hUC (le_of_eq hrel.symm)).symm

variable {T L V : Subgroup G}

theorem card_T_le
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) (hCV : Subgroup.centralizer (V : Set G) = V) :
    Nat.card ↥T ≤ 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy := h.hyp
  obtain ⟨hcomm, hV64, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hVT : V ≤ T := S127.L713.V_le_T h1222 h
  have h1 := card_autOn_eq_relIndex hTV
  rw [hCV, inf_of_le_right hVT] at h1
  have h2 := Subgroup.relIndex_mul_card V T
  rw [inf_of_le_left hVT, ← h1, hV64] at h2
  have hT2 : IsPGroup 2 ↥(autOn T V) := by
    rintro ⟨a, ha⟩
    obtain ⟨t, htN, htT, rfl⟩ := S127.Mod.mem_autOn'.1 ha
    obtain ⟨k, hk⟩ := hy.sylow.1 ⟨t, htT⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    have e : (⟨t, htN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk')
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, e, map_one]
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hTM : autOn T V ≤ hy.MVbar := A4.autOn_mono (le_inf hy.normalizes hTV)
  have hdvd := Subgroup.card_dvd_of_le hTM
  rw [hk] at hdvd h2
  have hk4 : k ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have h32 : 2 ^ 5 ∣ Nat.card ↥hy.MVbar := (Nat.pow_dvd_pow 2 hlt).trans hdvd
    rcases S127.Mod.lemma12_7_2_one h1222 h with hM | ⟨-, ⟨e⟩⟩
    · rw [hM, card_autOn_L h.hatA6 (S127.Mod.L_le_normalizer h)] at h32
      norm_num at h32
    · have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 3 ↥hy.MVbar)
      have h6 : Nat.card (Fin 6) = 6 := by simp
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, h6] at hc
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥hy.MVbar)).exists_card_eq
      rw [ha] at hc
      rw [hc] at h32
      have hcop : Nat.Coprime (2 ^ 5) (3 ^ a) := Nat.Coprime.pow 5 a (by norm_num)
      have := hcop.dvd_of_dvd_mul_right h32
      norm_num [Nat.factorial] at this
  calc Nat.card ↥T = 2 ^ k * 2 ^ 6 := h2.symm
    _ ≤ 2 ^ 4 * 2 ^ 6 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk4)
    _ = 2 ^ 10 := by norm_num

namespace L715.Set714

open S127.L716 G31 CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

variable {t z : G} (s : Set714 G T L V t z)
include s

theorem mem_ker_rho
    (h1222 : Stmt12_2_2) (h : ↥(H714 T L V z)) :
    s.rho h1222 h = 1 ↔ (h : G) ∈ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) := by
  have hhN := s.H_le_N h1222 h.2
  constructor
  · intro h1
    refine ⟨h.2, fun u hu => ?_⟩
    have huN : u ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := s.U_le_N h1222 hu
    have hw : secMk (Subgroup.normalizer (Subgroup.zpowers z : Set G)) (Subgroup.zpowers z)
        ⟨u, huN⟩ ∈ Ut T L V z := secMk_mem_secImg hu
    have h2 := congrArg (fun f : MulAut ↥(Ut T L V z) => ((f ⟨_, hw⟩ : ↥(Ut T L V z)) : Gt z)) h1
    simp only [s.rho_apply h1222, MulAut.one_apply] at h2
    have h3 : tmk (Subgroup.zpowers z) (⟨h, hhN⟩ * ⟨u, huN⟩ * ⟨h, hhN⟩⁻¹ * ⟨u, huN⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [show (⟨h, hhN⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers z : Set G))) =
        Subgroup.inclusion (s.H_le_N h1222) h from rfl, h2, mul_inv_cancel]
    exact secMk_eq_one_iff.1 h3
  · intro hc
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    rw [s.rho_apply h1222, MulAut.one_apply]
    obtain ⟨u, hu, hwu⟩ := mem_secImg.1 w.2
    rw [← hwu]
    have h1 : tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h * u *
        (Subgroup.inclusion (s.H_le_N h1222) h)⁻¹ * u⁻¹) = 1 :=
      secMk_eq_one_iff.2 (hc.2 _ hu)
    simp only [map_mul, map_inv] at h1
    rw [← mul_inv_eq_one]
    exact h1

theorem card_H_eq
    (h1222 : Stmt12_2_2) : Nat.card ↥(H714 T L V z) = Nat.card ↥(Hs T L V z) *
      Nat.card ↥(cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)) := by
  have hker : (s.rho h1222).ker =
      (cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)).subgroupOf (H714 T L V z) := by
    ext h
    rw [MonoidHom.mem_ker, s.mem_ker_rho h1222, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (s.rho h1222).ker
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange (s.rho h1222)).toEquiv,
    s.range_rho h1222, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (fun x hx => hx.1 : cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) ≤
        H714 T L V z)).toEquiv] at h1

theorem card_cTil_eq
    (h1222 : Stmt12_2_2) :
    Nat.card ↥(cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)) =
      Nat.card ↥(((cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)).subgroupOf
        (H714 T L V z)).map (s.psiH h1222)) *
      Nat.card ↥(H714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G)) := by
  set cT := cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hcT
  set E := cT.subgroupOf (H714 T L V z) with hE
  have hcTH : cT ≤ H714 T L V z := fun x hx => hx.1
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((s.psiH h1222).comp E.subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, MonoidHom.range_comp,
    Subgroup.range_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcTH).toEquiv] at h1
  rw [h1]
  congr 1
  refine Nat.card_congr (Equiv.ofBijective
    (fun k => (⟨((k : E) : G), Subgroup.mem_inf.mpr ⟨((k : E) : ↥(H714 T L V z)).2, ?_⟩⟩ :
      ↥(H714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G)))) ⟨fun a b hab => ?_, ?_⟩)
  · rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hk := k.2
    rw [MonoidHom.mem_ker] at hk
    have h2 := congrArg (fun φ : MulAut ↥(U714 T L V z) => ((φ ⟨u, hu⟩ : ↥(U714 T L V z)) : G)) hk
    simp only [MonoidHom.comp_apply, MulAut.one_apply] at h2
    rw [s.psiH_apply] at h2
    calc u * ((k : E) : G) = ((k : E) : G) * u * ((k : E) : G)⁻¹ * ((k : E) : G) := by
          rw [show ((k : E) : G) * u * ((k : E) : G)⁻¹ = u from h2]
      _ = ((k : E) : G) * u := by group
  · exact Subtype.ext (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  · rintro ⟨c, hcH, hcU⟩
    have hcT' : c ∈ cT := ⟨hcH, fun u hu => by
      rw [← Subgroup.mem_centralizer_iff.mp hcU u hu, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _⟩
    refine ⟨⟨⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hcT'⟩, ?_⟩, rfl⟩
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, s.psiH_apply, MulAut.one_apply]
    show c * u * c⁻¹ = u
    rw [← Subgroup.mem_centralizer_iff.mp hcU u u.2, mul_inv_cancel_right]

theorem isPGroup_map_cTil
    (h1222 : Stmt12_2_2) : IsPGroup 2 ↥(((cTil (s.H_le_Gz h1222)
      (s.H_le_normalizer_U h1222)).subgroupOf (H714 T L V z)).map (s.psiH h1222)) := by
  rintro ⟨_, c, hc, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hz2 : z * z = 1 := by rw [← pow_two, ← s.orderOf_z]; exact pow_orderOf_eq_one z
  have hcz : (c : G) * z = z * c :=
    Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 c.2)
  refine MulEquiv.ext fun u => Subtype.ext ?_
  simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one, MulAut.one_apply]
  rw [pow_two, ← map_mul, s.psiH_apply]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((Subgroup.mem_subgroupOf.mp hc).2 u u.2)
  have h1 : (c : G) * u * (c : G)⁻¹ = z ^ k * u := by
    rw [hk]
    group
  have hczk : (c : G) * z ^ k * (c : G)⁻¹ = z ^ k := by
    rw [((Commute.zpow_right (show Commute (c : G) z from hcz) k)).eq, mul_inv_cancel_right]
  calc ((c * c : ↥(H714 T L V z)) : G) * u * ((c * c : ↥(H714 T L V z)) : G)⁻¹ =
      (c : G) * ((c : G) * u * (c : G)⁻¹) * (c : G)⁻¹ := by
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group
    _ = ((c : G) * z ^ k * (c : G)⁻¹) * ((c : G) * u * (c : G)⁻¹) := by
        conv_lhs => rw [h1]
        group
    _ = z ^ k * (z ^ k * u) := by rw [hczk, h1]
    _ = u := by
        rw [← mul_assoc, ← zpow_add]
        obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
        · rw [hm, show 2 * m + 2 * m = 2 * (2 * m) by ring, zpow_mul,
            show z ^ (2 : ℤ) = 1 by exact_mod_cast (show z ^ 2 = 1 by rw [pow_two]; exact hz2),
            one_zpow, one_mul]
        · rw [hm, show 2 * m + 1 + (2 * m + 1) = 2 * (2 * m + 1) by ring, zpow_mul,
            show z ^ (2 : ℤ) = 1 by exact_mod_cast (show z ^ 2 = 1 by rw [pow_two]; exact hz2),
            one_zpow, one_mul]

theorem centralizer_U_eq
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6)
    (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 3) :
    H714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G) = U714 T L V z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.setting.hyp
  have hy := h.hyp
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hTL := hy.normalizes
  have hQL := s.comm_le_V h1222 hU hd (by norm_num)
  have hOQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
      (pCoreOf_isPGroup 2 L)
  have hcommL : ⁅pCoreOf 2 L, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro q hq l' hl'
    rw [commutatorElement_def]
    have e : q * l' * q⁻¹ * l'⁻¹ = (l' * q * l'⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact V.inv_mem (hQL q (hOQ hq) l' hl')
  have hCV := centralizer_V_eq h1222 h1226 h129 h1241 h10 h11 s.setting hcommL
  have hT := card_T_le h1222 h hCV
  set cT := cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hcT
  set R := (cT.subgroupOf (H714 T L V z)).map (s.psiH h1222) with hR
  set C := H714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G) with hC
  have hH := s.card_H_eq h1222
  rw [s.card_Hs h1222 h37 h38 h39 hU hd, s.card_cTil_eq h1222] at hH
  obtain ⟨j, hj⟩ := (s.isPGroup_map_cTil h1222).exists_card_eq
  have h8 := s.eight_le_card_map_cTil h1222 h37 h38 h39 hU hd
  rw [hj] at h8 hH
  have hj3 : 3 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hUH : U714 T L V z ≤ H714 T L V z := (s.U_le_T h1222).1.trans T_le_H
  have hsq := s.sq_eq_one_U h1222 h37 h38 h39 hU
  have hUab : ∀ a ∈ U714 T L V z, ∀ b ∈ U714 T L V z, a * b = b * a := fun a ha b hb => by
    have hinv : ∀ x ∈ U714 T L V z, x⁻¹ = x := fun x hx =>
      inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hsq x hx)
    have := hinv (a * b) (Subgroup.mul_mem _ ha hb)
    rw [mul_inv_rev, hinv a ha, hinv b hb] at this
    exact this.symm
  have hUC : U714 T L V z ≤ C := fun u hu =>
    ⟨hUH hu, Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w hw u hu⟩
  have hU16 : Nat.card ↥(U714 T L V z) = 16 := by
    rw [s.card_U h1222, hd]
    norm_num
  have hTH := s.odd_index_T
  have h3 := Subgroup.card_mul_index (T.subgroupOf (H714 T L V z))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le_H).toEquiv, hH] at h3
  obtain ⟨k, hk⟩ := hy.sylow.1.exists_card_eq
  rw [hk] at h3 hT
  have hk10 : k ≤ 10 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hT
  have hrel := Subgroup.relIndex_mul_card (U714 T L V z) C
  rw [inf_of_le_left hUC, hU16] at hrel
  rw [← hrel] at h3
  have hodd : ¬ 2 ∣ (U714 T L V z).relIndex C := by
    intro h2
    obtain ⟨c, hc⟩ := h2
    rw [hc] at h3
    have hcop : Nat.Coprime (2 ^ 11) (T.subgroupOf (H714 T L V z)).index :=
      Nat.Coprime.pow_left 11 (Nat.coprime_two_left.mpr hTH)
    have hdvd : 2 ^ 11 ∣ 2 ^ k * (T.subgroupOf (H714 T L V z)).index := by
      rw [h3]
      exact ⟨21 * 2 ^ (j - 3) * c, by
        rw [show 2 ^ j = 2 ^ 3 * 2 ^ (j - 3) by rw [← pow_add]; congr 1; omega]
        ring⟩
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop.dvd_of_dvd_mul_right hdvd)
    omega
  exact eq_of_central_sylow (H := H714 T L V z) inf_le_left
    (fun h hh => Subgroup.mem_normalizer_fintype fun c hc =>
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hc.1) (Subgroup.inv_mem _ hh),
        conj_mem_centralizer (s.H_le_normalizer_U h1222 hh) hc.2⟩)
    hUC (hy.sylow.1.to_le ((s.U_le_T h1222).1))
    (fun c hc u hu => (Subgroup.mem_centralizer_iff.mp hc.2 u hu).symm) hodd
    (charTwo_of_inH hy.qtke.2.1 (hy.sylow.1.toSylow hy.sylow.2) ⟨T_le_H, s.pCoreOf_H_ne_bot h1222⟩)

theorem card_cTil_eq_and
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6)
    (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 3) :
    Nat.card ↥(cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)) = 2 ^ 7 ∧
      Nat.card ↥(H714 T L V z) = 2 ^ 10 * 21 ∧
      pCoreOf 2 (H714 T L V z) = cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.setting.hyp
  have hy := h.hyp
  have hC := s.centralizer_U_eq h1222 h1226 h129 h1241 h10 h11 h37 h38 h39 hU hd
  have hU16 : Nat.card ↥(U714 T L V z) = 16 := by
    rw [s.card_U h1222, hd]
    norm_num
  have hc := s.card_cTil_eq h1222
  rw [hC, hU16] at hc
  obtain ⟨j, hj⟩ := (s.isPGroup_map_cTil h1222).exists_card_eq
  have h8 := s.eight_le_card_map_cTil h1222 h37 h38 h39 hU hd
  rw [hj] at h8 hc
  have hH := s.card_H_eq h1222
  rw [s.card_Hs h1222 h37 h38 h39 hU hd, hc] at hH
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hTL := hy.normalizes
  have hQL := s.comm_le_V h1222 hU hd (by norm_num)
  have hOQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
      (pCoreOf_isPGroup 2 L)
  have hcommL : ⁅pCoreOf 2 L, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro q hq l' hl'
    rw [commutatorElement_def]
    have e : q * l' * q⁻¹ * l'⁻¹ = (l' * q * l'⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact V.inv_mem (hQL q (hOQ hq) l' hl')
  have hT := card_T_le h1222 h (centralizer_V_eq h1222 h1226 h129 h1241 h10 h11 s.setting hcommL)
  have h3 := Subgroup.card_mul_index (T.subgroupOf (H714 T L V z))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le_H).toEquiv, hH] at h3
  obtain ⟨k, hk⟩ := hy.sylow.1.exists_card_eq
  rw [hk] at h3 hT
  have hk10 : k ≤ 10 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hT
  have hj3 : j = 3 := by
    have hj3' : 3 ≤ j := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hcop : Nat.Coprime (2 ^ (7 + j)) (T.subgroupOf (H714 T L V z)).index :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr s.odd_index_T)
    have hdvd : 2 ^ (7 + j) ∣ 2 ^ k * (T.subgroupOf (H714 T L V z)).index := by
      rw [h3]
      exact ⟨21, by rw [pow_add]; ring⟩
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop.dvd_of_dvd_mul_right hdvd)
    omega
  subst hj3
  refine ⟨by rw [hc]; norm_num, by rw [hH]; norm_num, ?_⟩
  set cT := cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hcT
  have hcTH : cT ≤ H714 T L V z := fun x hx => hx.1
  apply le_antisymm
  · intro x hx
    have hx' : (⟨x, pCoreOf_le 2 _ hx⟩ : ↥(H714 T L V z)) ∈ CFSG.pCore 2 ↥(H714 T L V z) := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [show (⟨x, pCoreOf_le 2 _ hx⟩ : ↥(H714 T L V z)) = y from Subtype.ext hyx.symm]
      exact hy
    have := s.pCore_le_ker_rho h1222 hx'
    rw [MonoidHom.mem_ker, s.mem_ker_rho h1222] at this
    exact this
  · refine le_pCoreOf_of_le_normalizer 2 hcTH (le_normalizer_cTil _ _) ?_
    exact IsPGroup.of_card (n := 7) (by rw [hc]; norm_num)

end L715.Set714

end CFSG.Quasithin.H13.S127
