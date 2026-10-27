module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14LU
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_ch6 {K R : Subgroup G} (hRK : R ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ K ⊔ R) : ∃ k ∈ K, ∃ r ∈ R, x = k * r := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, R.one_mem, by rw [mul_one]⟩
    · exact ⟨1, K.one_mem, y, hy, by rw [one_mul]⟩
  | one => exact ⟨1, K.one_mem, 1, R.one_mem, by rw [mul_one]⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨k, hk, r, hr, rfl⟩ := ihy
    obtain ⟨k', hk', r', hr', rfl⟩ := ihz
    refine ⟨k * (r * k' * r⁻¹), K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hRK hr) k').mp hk'),
      r * r', R.mul_mem hr hr', by group⟩
  | inv y _ ih =>
    obtain ⟨k, hk, r, hr, rfl⟩ := ih
    refine ⟨r⁻¹ * k⁻¹ * r⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (hRK (R.inv_mem hr)) k⁻¹).mp
      (K.inv_mem hk), r⁻¹, R.inv_mem hr, by group⟩

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq_ch6 {X : Subgroup G} {x : G}
    (h : X.map (MulAut.conj x).toMonoidHom = X) : x ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ X.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have e : x * z * x⁻¹ = x * y * x⁻¹ := hzy
    have : z = y := mul_left_cancel (mul_right_cancel e)
    rw [← this]
    exact hz

namespace Hyp611Nat

variable {T M L V : Subgroup G} {n : ℕ}

theorem normalizer_R_le (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    Subgroup.normalizer ((ch6Q T V ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤ M := by
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  have htU : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  have hQU : ch6Q T V ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le inf_le_left)
  have hRT : ch6Q T V ⊔ Subgroup.zpowers t ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)
  have hRU : ch6Q T V ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer (U : Set G) :=
    sup_le hQU (Subgroup.zpowers_le.mpr htU)
  have hJR := h.thompsonJ_eq_Q htT ht le_sup_left hRT
    (hRU.trans (Subgroup.centralizer_le_normalizer _))
  refine (GammaExtra.normalizer_le_normalizer_thompsonJ _).trans ?_
  rw [hJR]
  exact h.normalizer_thompsonJ_Q_le h432

theorem solvable_le_M (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h : Hyp611Nat G T M L V n)
    {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)))
    (hn : 2 < n) {X : Subgroup G} (hRX : ch6Q T V ⊔ Subgroup.zpowers t ≤ X)
    (hXC : X ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) (hX : Group.IsSolvable ↥X) : X ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have hV := h.toHyp611.isElemAbelian
  have hs : sParam hV = n := ((h6110 _ T M L V n h).2.1 hV).1
  have h1 := h.lemma_6_1_14_one h432 htT ht hSyl
  have hRsyl : IsSylowIn 2 R X := E6.isSylowIn_of_le h1.1 hRX hXC
  have hj0 : E1.nParam X ≤ 1 := E1.solvable_nParam_le_one hX
  obtain ⟨j, hjX⟩ : ∃ j : ℕ, E1.nParam X = j :=
    ⟨(E1.nParam X).toNat, (ENat.natCast_toNat (ne_top_of_le_ne_top ENat.one_ne_top hj0)).symm⟩
  have hj : j ≤ 1 := by
    rw [hjX] at hj0
    exact_mod_cast hj0
  have h319 := e3_19 hV hRsyl (i := 0) hjX (by rw [hs]; omega)
  have hU := h.toHyp611.isUniqueM h432
  have hQ := h.toHyp611.centralizer_eq
  have hQ1 : ch6Q T V ≠ ⊥ := by rw [hQ]; exact h.maximal.1.2.2.2
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hNQ : IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M :=
    ⟨⟨h.maxTwoLocal, le_of_isUniqueM_of_le_twoLocal hU hLTQ ⟨_, hQ1, hQ2, rfl⟩⟩,
      fun M' hM' => hU.2 M' ⟨hM'.1, hLTQ.trans hM'.2⟩⟩
  have hQX : ch6Q T V ≤ X := le_sup_left.trans hRX
  have hW := h.lemma_6_1_14_three h6110 htT ht
  have hrk : 1 < rk ↥V := by
    have hc : Nat.card V = 2 ^ (n + n) := by rw [pow_add]; exact h.natural.card_eq
    unfold rk
    rw [hc, padicValNat.prime_pow]
    omega
  have hVR : V ≤ R := h.le_Q.trans le_sup_left
  have hWne : ∀ i, i ≤ 1 → wClos V i R ≠ ⊥ := by
    intro i hi h0
    have := le_wClos_of_mQuot_le_self hV hVR le_rfl (k := i) (by rw [mQuot_self]; omega)
      (by omega)
    rw [h0] at this
    exact h.toHyp611.ne_bot (eq_bot_iff.mpr this)
  have hWQ : ∀ i, i ≤ 1 → wClos V i R ≤ ch6Q T V := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact hW.1
    · exact hW.2 hn
  have hC : Subgroup.centralizer (cClos V (0 + j) R : Set G) ≤ M := by
    rw [zero_add]
    exact e3_16_three hRsyl hQX hQ2 (hWQ _ hj) (hWne _ hj) hNQ
  have hN : Subgroup.normalizer (wClos V 0 R : Set G) ≤ M :=
    (e3_16_one hRsyl hQX hQ2 (hWQ 0 (by omega)) (hWne 0 (by omega)) hNQ).2
  rw [← h319]
  exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hN)

omit [Finite G] in
theorem conjAct_eq_one_iff {U : Subgroup G} (x : Subgroup.normalizer (U : Set G)) :
    conjAct U x = 1 ↔ (x : G) ∈ Subgroup.centralizer (U : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff x

theorem lOne_fix_mem_cComp_normalizer (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)))
    (hn4 : 4 ≤ n) :
    lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) ∈
      cComp (Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set LU := lOne L U with hLU
  set TU := T ⊓ Subgroup.normalizer (U : Set G) with hTU
  set NU := Subgroup.normalizer (U : Set G) with hNU
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have hUcard : Nat.card U = 2 ^ n := h.card_fix_of_fieldAut htT ht
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hUcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  have hU2 : IsPGroup 2 U :=
    (F7.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le inf_le_left
  have hUO : U ≤ pCoreOf 2 NU := le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hU2
  have hNU1 : pCoreOf 2 NU ≠ ⊥ := fun h0 => hU1 (eq_bot_iff.mpr (h0 ▸ hUO))
  have h1 := h.lemma_6_1_14_one h432 htT ht hSyl
  have hLUNU : LU ≤ NU := (oTwoUpper_le _).trans inf_le_right
  have hLUfam : LU ∈ lFamily TU := by
    rw [lFamily, Set.mem_ofPred_eq]
    exact h.lOne_fix_mem_cComp htT ht hn4
  obtain ⟨K, hKc, hLUK⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hNU1 h1.2.2 hLUNU hLUfam
  have hKNU : K ≤ NU := le_of_mem_cComp hKc
  have hTUK : TU ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (NU : Set G) := Subgroup.le_normalizer hx.2
    have hKx : K.map (MulAut.conj x).toMonoidHom ∈ cComp NU := by
      have := quasithinIsCComponent_map (MulAut.conj x) hKc
      rwa [map_conj_eq_of_mem_normalizer_ch6 hxN] at this
    have hLUx : LU ≤ K.map (MulAut.conj x).toMonoidHom :=
      calc LU = LU.map (MulAut.conj x).toMonoidHom :=
            (map_conj_eq_of_mem_normalizer_ch6 (h.le_normalizer_lOne_fix hx)).symm
        _ ≤ K.map (MulAut.conj x).toMonoidHom := Subgroup.map_mono hLUK
    exact mem_normalizer_of_map_conj_eq_ch6
      (Vol2Native.lemma_1_2_4_unique hK h37 hNU1 hLUfam hKx hKc hLUx hLUK)
  have hRTU : R ≤ TU := by
    refine le_inf (sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)) ?_
    exact h1.1.le.trans (Subgroup.centralizer_le_normalizer _)
  have hRU : R ≤ Subgroup.centralizer (U : Set G) := h1.1.le
  have hCKn : K ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, F7.normalizer_le_normalizer_centralizer _ (hKNU hx)⟩
  have hCKsub : IsSubnormal (K ⊓ Subgroup.centralizer (U : Set G)) K :=
    A3.subnormal_of_normal inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hCKn)
  have hCKlt : K ⊓ Subgroup.centralizer (U : Set G) < K := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    apply h.false_of_lOne_fix_comm_mod htT ht hn4
    intro a ha b hb
    have hKC : K ≤ Subgroup.centralizer (U : Set G) := heq ▸ inf_le_right
    exact hKC (K.mul_mem (K.mul_mem (K.mul_mem (hLUK ha) (hLUK hb)) (K.inv_mem (hLUK ha)))
      (K.inv_mem (hLUK hb)))
  have hCKsolv : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer (U : Set G)) :=
    (isSolvable_iff_perfectCore_eq_bot _).mpr (perfectCore_eq_bot_of_subnormal_lt hKc hCKsub hCKlt)
  have hRN : R ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hTUK (hRTU hx), F7.normalizer_le_normalizer_centralizer _
      (Subgroup.centralizer_le_normalizer _ (hRU hx))⟩
  have hR2 : IsPGroup 2 R := h1.1.isPGroup
  have : Group.IsNilpotent ↥R := hR2.isNilpotent
  have : Group.IsSolvable ↥R := inferInstance
  have : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer (U : Set G)) := hCKsolv
  have hXsolv := A3.isSolvable_sup_of_le_normalizer hRN
  have hXM := h.solvable_le_M h432 h6110 htT ht hSyl (by omega)
    (X := (K ⊓ Subgroup.centralizer (U : Set G)) ⊔ R) le_sup_right (sup_le inf_le_right hRU)
    hXsolv
  have hCKM : K ⊓ Subgroup.centralizer (U : Set G) ≤ M := le_sup_left.trans hXM
  have hRM : R ≤ M := (sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)).trans h.T_le
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := fun x hx => hTUK (hRTU hx)
  have hYN : K ⊔ R ≤ NU := sup_le hKNU (hRU.trans (Subgroup.centralizer_le_normalizer _))
  have hYCn : K ⊔ R ≤ Subgroup.normalizer
      (((K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, F7.normalizer_le_normalizer_centralizer _ (hYN hx)⟩
  have hRYC : R ≤ (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) := le_inf le_sup_right hRU
  have hodd : ¬ 2 ∣ R.relIndex ((K ⊔ R) ⊓ Subgroup.centralizer (U : Set G)) :=
    (E6.isSylowIn_of_le h1.1 hRYC inf_le_right).not_dvd_relIndex
  have hfrat := exists_mul_of_sylow inf_le_left hYCn hRYC hR2 hodd
  have hNR := h.normalizer_R_le h432 htT ht
  have hYCM : (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) ≤ M := by
    intro c hc
    obtain ⟨k, hk, r, hr, rfl⟩ := exists_mul_of_mem_sup_ch6 hRK hc.1
    have hkC : k ∈ Subgroup.centralizer (U : Set G) := by
      have e : k = (k * r) * r⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hc.2 (Subgroup.inv_mem _ (hRU hr))
    exact M.mul_mem (hCKM ⟨hk, hkC⟩) (hRM hr)
  have hYM : K ⊔ R ≤ M := by
    intro y hy
    obtain ⟨m, hm, c, hc, rfl⟩ := hfrat y hy
    exact M.mul_mem (hNR hm.2) (hYCM hc)
  have hKM : K ≤ M := le_sup_left.trans hYM
  have hKLU : K ≤ Subgroup.normalizer (LU : Set G) := fun x hx =>
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.normal (hKM hx), Subgroup.le_normalizer (hKNU hx)⟩)
  have hLUsub : IsSubnormal LU NU :=
    A3.subnormal_trans (A3.subnormal_of_normal hLUK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLUK).mpr hKLU))
      (subnormal_of_mem_cComp hKc)
  by_cases heq : LU = K
  · rw [heq]
    exact hKc
  · exact absurd hLUsub ((mem_cComp_iff.mp hKc).2.2.2 LU (lt_of_le_of_ne hLUK heq)
      (h.lOne_fix_ne_bot htT ht hn4) (h.lOne_fix_perfect htT ht hn4))

theorem centralizer_le_normalizer_lOne_fix (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)))
    (hn4 : 4 ≤ n) :
    Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) : Subgroup G) :
        Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set LU := lOne L U with hLU
  set NU := Subgroup.normalizer (U : Set G) with hNU
  have hUcard : Nat.card U = 2 ^ n := h.card_fix_of_fieldAut htT ht
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hUcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  have hU2 : IsPGroup 2 U :=
    (F7.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le inf_le_left
  have hUO : U ≤ pCoreOf 2 NU := le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hU2
  have hNU1 : pCoreOf 2 NU ≠ ⊥ := fun h0 => hU1 (eq_bot_iff.mpr (h0 ▸ hUO))
  have hLUc := h.lOne_fix_mem_cComp_normalizer h432 h6110 h37 h39 htT ht hSyl hn4
  have hLUNU : LU ≤ NU := (oTwoUpper_le _).trans inf_le_right
  intro a ha
  have haN : a ∈ NU := Subgroup.centralizer_le_normalizer _ ha
  have hLUa : LU.map (MulAut.conj a).toMonoidHom ∈ cComp NU := by
    have := quasithinIsCComponent_map (MulAut.conj a) hLUc
    rwa [map_conj_eq_of_mem_normalizer_ch6 (Subgroup.le_normalizer haN)] at this
  by_contra hna
  have hne : LU ≠ LU.map (MulAut.conj a).toMonoidHom := fun heq =>
    hna (mem_normalizer_of_map_conj_eq_ch6 heq.symm)
  obtain ⟨hcomm, -⟩ := Vol2Native.lemma_1_2_1_two hK h37 hNU1 hLUc hLUa hne
  have hO := h.pCoreOf_lOne_fix_le htT ht hn4
  apply h.false_of_lOne_fix_comm_mod htT ht hn4
  intro b hb c hc
  have hbN : b ∈ NU := hLUNU hb
  have hcN : c ∈ NU := hLUNU hc
  have hw : ⁅b, a * c * a⁻¹⁆ ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.centralizer_le inf_le_left (hO (hcomm
      (Subgroup.commutator_mem_commutator hb ⟨c, hc, rfl⟩)).1)
  set b' : NU := ⟨b, hbN⟩
  set c' : NU := ⟨c, hcN⟩
  set a' : NU := ⟨a, haN⟩
  have ha' : conjAct U a' = 1 := (conjAct_eq_one_iff a').mpr ha
  have hw' : conjAct U ⁅b', a' * c' * a'⁻¹⁆ = 1 := (conjAct_eq_one_iff _).mpr hw
  rw [map_commutatorElement, map_mul, map_mul, map_inv, ha', one_mul, inv_one, mul_one,
    ← map_commutatorElement] at hw'
  exact (conjAct_eq_one_iff _).mp hw'

end Hyp611Nat

end CFSG.Quasithin.H13
