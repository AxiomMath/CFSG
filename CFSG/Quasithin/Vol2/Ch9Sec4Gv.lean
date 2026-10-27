module

public import CFSG.Quasithin.Vol2.Ch9Sec4Pts2
public import CFSG.Quasithin.Vol2.Ch9Sec4Facts
public import CFSG.Quasithin.Vol2.Ch1Eleven
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch9Sec3KX

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem normalizer_zpowers_eq_centralizer {G : Type*} [Group G] {v : G} (hv : v ^ 2 = 1)
    (hv1 : v ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers v : Set G) = Subgroup.centralizer ({v} : Set G) := by
  have hconj : ∀ x : G, x * v = v * x → ∀ k : ℤ, x * v ^ k * x⁻¹ = v ^ k := by
    intro x hx k
    have h1 : x * v * x⁻¹ = v := by rw [hx, mul_inv_cancel_right]
    rw [← conj_zpow, h1]
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((h v).mp (Subgroup.mem_zpowers v))
    rw [zpow_eq_zpow_emod' k (n := 2) (by exact_mod_cast hv)] at hk
    simp only [Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · exfalso
      rw [h0, zpow_zero] at hk
      apply hv1
      have : x * v * x⁻¹ * x = x := by rw [← hk, one_mul]
      simpa [mul_assoc] using this
    · rw [h0, zpow_one] at hk
      calc x * v = (x * v * x⁻¹) * x := by group
        _ = v * x := by rw [← hk]
  · intro hx y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hconj x hx k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk' : v ^ k = x * y * x⁻¹ := hk
      have := hconj x hx k
      show v ^ k = y
      have h2 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [h2, ← hk']
      calc v ^ k = x⁻¹ * (x * v ^ k * x⁻¹) * x := by group
        _ = x⁻¹ * v ^ k * x := by rw [this]

theorem isElemAbelian_of_le {G : Type*} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    (h : IsElemAbelian 2 B) : IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono h hAB

theorem mem_pCoreOf_of_le_centralizer {G : Type*} [Group G] [Finite G] {v : G} (hv2 : v ^ 2 = 1)
    (hv1 : v ≠ 1) {X : Subgroup G} (hvX : v ∈ X)
    (hXC : X ≤ Subgroup.centralizer ({v} : Set G)) : v ∈ pCoreOf 2 X := by
  have h1 : Subgroup.zpowers v ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((Subgroup.zpowers_le).mpr hvX)
      (fun x hx => by
        rw [normalizer_zpowers_eq_centralizer hv2 hv1]
        exact hXC hx)
      (by
        rintro ⟨y, k, rfl⟩
        refine ⟨1, Subtype.ext ?_⟩
        show ((fun m : ℤ => v ^ m) k) ^ 2 ^ 1 = 1
        simp only [pow_one]
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hv2,
          _root_.one_zpow])
  exact h1 (Subgroup.mem_zpowers v)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem isVplus_V : IsVplus T L I (fsuV T I) := by
  by_cases hc' : L ≠ conjClosure L T ∧ Case326VM T L I
  · exact Or.inl ⟨hc'.1, hc'.2, S.hVM⟩
  · exact Or.inr ⟨hc', rfl⟩

theorem isSylowTwoOf_centralizer (h3104 : Stmt3_2_10_four) {v : G} (hv : v ∈ fsuV T I)
    (hv1 : v ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G))) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G)) (Subgroup.centralizer ({v} : Set G)) := by
  have hv2 : v ^ 2 = 1 := S.hV.2 v hv
  have hU : Subgroup.zpowers v ≤ fsuV T I := (Subgroup.zpowers_le).mpr hv
  have hodd := h3104 G T L I (fsuV T I) S.hyp.fsu S.isVplus_V S.hJ _ hU
  rw [normalizer_zpowers_eq_centralizer hv2 hv1] at hodd
  refine ⟨hsyl.1.trans inf_le_right, hsyl.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ Subgroup.centralizer ({v} : Set G))
    (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G)) (Subgroup.centralizer ({v} : Set G))
    hsyl.1 inf_le_right
  have h2 := hsyl.2.2
  intro h3
  rw [← Subgroup.relIndex] at h2 h3
  rw [← h1] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h4 | h4
  · exact h2 h4
  · exact hodd h4

end Setup

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {X₀ : Matrix (Fin 2) (Fin 2) K}

theorem inV_line_le_lPt (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    inV e (Om4Pt.lineM X₀) ≤ lPt T L (inV e (Om4Pt.lineM X₀)) :=
  (inV_line_le_perp (e := e)).trans ((hc.perp_le_commutator hK4 hX).trans
    (hc.commutator_perp_le hX))

theorem inV_perp_le_lPt (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    inV e (Om4Pt.perpM X₀) ≤ lPt T L (inV e (Om4Pt.lineM X₀)) :=
  (hc.perp_le_commutator hK4 hX).trans (hc.commutator_perp_le hX)

theorem exists_mem_inf_lPt (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G))) :
    ∃ (u : G) (hu : u ∈ fsuL0 T L), u ∈ T ⊓ Subgroup.centralizer ({v} : Set G) ∧
      u ∈ lPt T L (inV e (Om4Pt.lineM X₀)) ∧ ψ ⟨u, hu⟩ ≠ 1 ∧ ψ ⟨u, hu⟩ * ψ ⟨u, hu⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := inV e (Om4Pt.lineM X₀) with hW
  set LW := lPt T L W with hLW
  set Gv := Subgroup.centralizer ({v} : Set G) with hGv
  have hLWGv : LW ≤ fsuM T L ⊓ Gv := by
    refine le_inf ((lPt_le_L0 T L W).trans Setup.L0_le_fsuM) fun l hl => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp (hc.lPt_le_centralizer hK4 hX hl) v hv
    exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
  have hnorm : fsuM T L ⊓ Gv ≤ Subgroup.normalizer (LW : Set G) := fun x hx =>
    hc.mem_normalizer_lPt hx.1 hv hv1 (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rw [this, mul_inv_cancel_right])
  have hS := A4.isSylowTwoOf_inf_normal hsyl hLWGv hnorm
  obtain ⟨s, hsT, hsL, hψs⟩ : ∃ s ∈ T ⊓ Gv, ∃ hs : s ∈ LW,
      ψ ⟨s, lPt_le_L0 T L W hs⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨e5⟩, hker⟩ := hc.lPt_quot h37c h38c hK4 hX
    have hle : ((T ⊓ Gv) ⊓ LW).subgroupOf LW ≤ CFSG.pCore 2 ↥LW := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [hker, MonoidHom.mem_ker]
      exact hcon x hx.1 x.2
    have hidx : (CFSG.pCore 2 ↥LW).index = 60 := by
      rw [Subgroup.index_eq_card, Nat.card_congr e5.toEquiv]
      rw [Nat.card_eq_fintype_card]
      rfl
    have h1 := Subgroup.relIndex_mul_index hle
    apply hS.2.2
    rw [← h1, hidx]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨s, hsT.1⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set ss : ↥(fsuL0 T L) := ⟨s, lPt_le_L0 T L W hsL⟩ with hssdef
  have hord : orderOf (ψ ss) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : ss ^ 2 ^ k = 1 := Subtype.ext (by simpa [hssdef] using hk')
    rw [this, map_one]
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hψs (orderOf_eq_one_iff.mp (by simpa using hj))
  set u : G := s ^ 2 ^ (j - 1) with hudef
  have huL0 : u ∈ fsuL0 T L := Subgroup.pow_mem _ (lPt_le_L0 T L W hsL) _
  have huss : (⟨u, huL0⟩ : ↥(fsuL0 T L)) = ss ^ 2 ^ (j - 1) := Subtype.ext (by
    rw [SubgroupClass.coe_pow])
  refine ⟨u, huL0, Subgroup.pow_mem _ hsT _, Subgroup.pow_mem _ hsL _, ?_, ?_⟩
  · rw [huss, map_pow]
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at this
    have h3 := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.mp this
    omega
  · rw [huss, map_pow, ← pow_two, ← pow_mul]
    have : 2 ^ (j - 1) * 2 = 2 ^ j := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this, ← hj, pow_orderOf_eq_one]

theorem prop941_setup (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (hFa : A314QuasiRankFact) (h2 : n = 2) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G)))
    {Lv : Subgroup G} (hLv : Lv ∈ cComp (Subgroup.centralizer ({v} : Set G)))
    (hlt : lPt T L (inV e (Om4Pt.lineM X₀)) < Lv)
    (hGvLv : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (Lv : Set G)) :
    ¬ Lv ≤ fsuM T L ∧ ¬ CFSG.IsQuasisimple ↥Lv ∧
      CharTwo (Lv ⊔ (T ⊓ Subgroup.centralizer ({v} : Set G))) ∧
      inV e (Om4Pt.perpM X₀) ≤ conjClosure (quasithinOmegaOneCenter T)
        (Lv ⊔ (T ⊓ Subgroup.centralizer ({v} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  set W := inV e (Om4Pt.lineM X₀) with hW
  set Wp := inV e (Om4Pt.perpM X₀) with hWp
  set LW := lPt T L W with hLW
  set Gv := Subgroup.centralizer ({v} : Set G) with hGv
  set Tv := T ⊓ Gv with hTv
  set H := Lv ⊔ Tv with hH
  have hvV : v ∈ fsuV T I := inV_le e _ hv
  have hv2 : v ^ 2 = 1 := S.hV.2 v hvV
  have hTvG : IsSylowTwoOf Tv Gv := S.isSylowTwoOf_centralizer h3104 hvV hv1 hsyl
  have hLvG : Lv ≤ Gv := le_of_mem_cComp hLv
  have hTvGv : Tv ≤ Gv := inf_le_right
  have hHG : H ≤ Gv := sup_le hLvG hTvGv
  have hvO : ∀ X : Subgroup G, v ∈ X → X ≤ Gv → v ∈ pCoreOf 2 X := by
    intro X hvX hXG
    have h1 : Subgroup.zpowers v ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((Subgroup.zpowers_le).mpr hvX)
        (fun x hx => by
          rw [normalizer_zpowers_eq_centralizer hv2 hv1]
          exact hXG hx)
        (by
          rintro ⟨y, k, rfl⟩
          refine ⟨1, Subtype.ext ?_⟩
          show ((fun m : ℤ => v ^ m) k) ^ 2 ^ 1 = 1
          simp only [pow_one]
          rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hv2,
            _root_.one_zpow])
    exact h1 (Subgroup.mem_zpowers v)
  have hvGv : v ∈ Gv := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hOGv : pCoreOf 2 Gv ≠ ⊥ := fun h => hv1 (by
    have := hvO Gv hvGv le_rfl
    rwa [h, Subgroup.mem_bot] at this)
  have hLWG : LW ≤ Gv := hlt.le.trans hLvG
  have hnormLW : fsuM T L ⊓ Gv ≤ Subgroup.normalizer (LW : Set G) := fun x hx =>
    hc.mem_normalizer_lPt hx.1 hv hv1 (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rw [this, mul_inv_cancel_right])
  have hTvN : Tv ≤ Subgroup.normalizer (LW : Set G) := hsyl.1.trans hnormLW
  have hLWl : LW ∈ lFamily Tv := hc.mem_lFamily_lPt h37c h38c hK4 hX hTvN
  have hA := (hc.lPt_quot h37c h38c hK4 hX).1
  have hLvM : ¬ Lv ≤ fsuM T L := by
    intro hle
    have hLvN : Lv ≤ Subgroup.normalizer (LW : Set G) := (le_inf hle hLvG).trans hnormLW
    have hsub : IsSubnormal LW Gv := A4.subnormal_trans (A4.subnormal_of_normal hlt.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hlt.le).mpr hLvN))
      (subnormal_of_mem_cComp hLv)
    exact not_subnormal_of_mem_cComp hLv hlt (ne_bot_of_mem_cComp (hLWl))
      (hc.perfect_lPt h37c h38c hK4 hX) hsub
  have hVG : fsuV T I ≤ Gv := fun x hx => by
    have h := S.hV.1.is_comm.comm ⟨x, hx⟩ ⟨v, hvV⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  have hq : ¬ CFSG.IsQuasisimple ↥Lv := by
    intro hq
    obtain ⟨-, hA314⟩ := a314Statement_bar hfsu.qtke hfsu.simple hfsu.nonabelian h36 h312 h314
      hOGv hTvG hLWG hLWl hLv hlt hTvN hA
    have hVC : fsuV T I ⊓ Subgroup.centralizer (Lv : Set G) ≤ Lv := by
      intro x hx
      refine hlt.le (hc.inV_line_le_lPt hK4 hX
        (hc.mem_inV_of_centralizes hK4 hX hx.1 fun l hl => ?_))
      have := Subgroup.mem_centralizer_iff.mp hx.2 l (hlt.le hl)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hVC1 : fsuV T I ⊓ Subgroup.centralizer (Lv : Set G) ≠ ⊥ := by
      intro h0
      apply hv1
      have : v ∈ fsuV T I ⊓ Subgroup.centralizer (Lv : Set G) :=
        ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun l hl =>
          Subgroup.mem_centralizer_singleton_iff.mp (hLvG hl)⟩
      rwa [h0, Subgroup.mem_bot] at this
    have h7 := hFa G Gv Tv LW Lv (fsuV T I)
      (sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hOGv) hOGv hTvG hLWl
      hTvN hA hLv hlt hA314 hq (hVG.trans hGvLv) S.hV hVC hVC1
    have h8 : rk ↥(fsuV T I) = 8 := by
      unfold rk
      have hcard : Nat.card ↥(fsuV T I) = 2 ^ 8 := by
        rw [Nat.card_congr e.toEquiv]
        show Nat.card (Fin 2 → Fin 2 → K) = 2 ^ 8
        rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K), hK4]
        simp
      rw [hcard, padicValNat.prime_pow]
    omega
  have hvTv : v ∈ Tv := ⟨S.fsuV_le_T hvV, hvGv⟩
  have hTvH : IsSylowTwoOf Tv H := A4.isSylowTwoOf_mono hTvG le_sup_right hHG
  have hTH : T ⊓ H = Tv := le_antisymm (le_inf inf_le_left (inf_le_right.trans hHG))
    (le_inf inf_le_left le_sup_right)
  have hLvH : Lv ∈ cComp H := cComp_mem_of_le hLv le_sup_left hHG
  have hvOH : v ∈ pCoreOf 2 H := hvO H (Subgroup.mem_sup_right hvTv) hHG
  have hOH : pCoreOf 2 H ≠ ⊥ := fun h => hv1 (by rwa [h, Subgroup.mem_bot] at hvOH)
  obtain ⟨⟨z, hzV, hzZ⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Vol2.Ch11.SecS.inf_omegaOneCenter_ne_bot' hfsu.sylow.1 S.hV S.fsuV_le_T S.T_le_normalizer_V
      S.fsuV_ne_bot)
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzTC := E3.omegaOneCenter_le_inf_centralizer T hzZ
  obtain ⟨u, huL0, huTv, huLW, hψu1, hψu2⟩ := hc.exists_mem_inf_lPt h37c h38c hK4 hX hv hv1 hsyl
  have hψu : ψ ⟨u, huL0⟩ ∈ Om4Pt.dgM X₀ := by
    rw [← hc.map_lPt hK4 hX]
    exact ⟨⟨u, huL0⟩, Subgroup.mem_subgroupOf.mpr huLW, rfl⟩
  have hzWp : z ∈ Wp := hc.mem_perp_of_fix hX ⟨u, huL0⟩ hψu hψu1 hψu2 hzV (by
    have := Subgroup.mem_centralizer_iff.mp hzTC.2 u huTv.1
    show u * z * u⁻¹ = z
    rw [this, mul_inv_cancel_right])
  have hzV1 : z ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
    ⟨hzV, Subgroup.centralizer_le inf_le_left hzTC.2⟩
  have hzd : ∀ hz : z ∈ fsuV T I, (Multiplicative.toAdd (e ⟨z, hz⟩)).det = 0 := by
    intro hz
    rw [hc.toAdd_e_eq hzV1, Matrix.det_smul]
    simp [Matrix.det_fin_two_of]
  have hzLW : z ∈ LW := hc.inV_perp_le_lPt hK4 hX hzWp
  have hLWopr : LW ≤ opResidual 2 (H ⊓ Subgroup.normalizer (Wp : Set G)) := by
    show oTwoUpper _ ≤ _
    rw [oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hx, hxo⟩
    have hxLW : x ∈ LW := Subgroup.subset_closure ⟨hx, hxo⟩
    exact Subgroup.subset_closure ⟨⟨Subgroup.mem_sup_left (hlt.le hxLW),
      hc.lPt_le_normalizer_perp hK4 hX hxLW⟩, Nat.coprime_two_right.mpr hxo⟩
  have hchar : CharTwo H := by
    refine (lemma_1_2_11 hfsu.qtke hfsu.sylow hOH (hTH ▸ hTvH) hLvH hzZ hz1 (hlt.le hzLW)
      (hTH ▸ ⟨hzTC.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
      ⟨Wp, (hc.inV_perp_le_lPt hK4 hX).trans (hlt.le.trans le_sup_left),
        isElemAbelian_of_le (inV_le e _) S.hV,
        Subgroup.commutator_mono le_rfl hLWopr (hc.mem_commutator_perp hK4 hX hzWp hzd hz1)⟩
      ?_).resolve_left hq
    · have := S.hV.1.is_comm.comm ⟨z, hzV⟩ ⟨v, hvV⟩
      exact congrArg Subtype.val this
    · rintro x ⟨hxT, hxC⟩
      refine hTH ▸ ⟨hxT, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp hxC v hvOH).symm
  refine ⟨hLvM, hq, hchar, (hc.perp_le_closure hK4 hX hzWp hzd hz1).trans ?_⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact mem_conjClosure (Subgroup.mem_sup_left (hlt.le hl)) hzZ

theorem prop941_aut (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight)
    (hFb : A314FFCohomFact) (h2 : n = 2) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G)))
    {Lv : Subgroup G} (hLv : Lv ∈ cComp (Subgroup.centralizer ({v} : Set G)))
    (hlt : lPt T L (inV e (Om4Pt.lineM X₀)) < Lv)
    (hGvLv : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (Lv : Set G))
    (hchar : CharTwo (Lv ⊔ (T ⊓ Subgroup.centralizer ({v} : Set G))))
    (hWpU : inV e (Om4Pt.perpM X₀) ≤ conjClosure (quasithinOmegaOneCenter T)
      (Lv ⊔ (T ⊓ Subgroup.centralizer ({v} : Set G)))) :
    Lv ≤ lPt T L (inV e (Om4Pt.lineM X₀)) ⊔ (Lv ⊓ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (Lv ⊔ (T ⊓ Subgroup.centralizer ({v} : Set G))) :
        Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  set W := inV e (Om4Pt.lineM X₀) with hW
  set Wp := inV e (Om4Pt.perpM X₀) with hWp
  set LW := lPt T L W with hLW
  set Gv := Subgroup.centralizer ({v} : Set G) with hGv
  set Tv := T ⊓ Gv with hTv
  set H := Lv ⊔ Tv with hH
  set Z := quasithinOmegaOneCenter T with hZ
  set U := conjClosure Z H with hU
  have hvV : v ∈ fsuV T I := inV_le e _ hv
  have hTvG : IsSylowTwoOf Tv Gv := S.isSylowTwoOf_centralizer h3104 hvV hv1 hsyl
  have hLvG : Lv ≤ Gv := le_of_mem_cComp hLv
  have hHG : H ≤ Gv := sup_le hLvG inf_le_right
  have hTvH : IsSylowTwoOf Tv H := A4.isSylowTwoOf_mono hTvG le_sup_right hHG
  have hLvH : Lv ∈ cComp H := cComp_mem_of_le hLv le_sup_left hHG
  have hTvLv : Tv ≤ Subgroup.normalizer (Lv : Set G) := inf_le_right.trans hGvLv
  have hnormLW : fsuM T L ⊓ Gv ≤ Subgroup.normalizer (LW : Set G) := fun x hx =>
    hc.mem_normalizer_lPt hx.1 hv hv1 (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rw [this, mul_inv_cancel_right])
  have hTvN : Tv ≤ Subgroup.normalizer (LW : Set G) := hsyl.1.trans hnormLW
  have hZT := E3.omegaOneCenter_le_inf_centralizer T
  have hZTv : Z ≤ quasithinOmegaOneCenter Tv := by
    rw [hZ, quasithinOmegaOneCenter, Subgroup.closure_le]
    rintro z ⟨⟨hzT, hzC⟩, hz2⟩
    refine Subgroup.subset_closure ⟨⟨⟨hzT, ?_⟩, Subgroup.centralizer_le inf_le_left hzC⟩, hz2⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hzC v (S.fsuV_le_T hvV)).symm)
  obtain ⟨-, -, hUr⟩ := conjClosure_isTwoReducedIn_of_charTwo hTvH hchar hZTv
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Z H
  have hHCU : H ≤ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
    intro h hh
    have hhU := hHU hh
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have key : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ c ∈ Subgroup.centralizer (U : Set G),
        g * c * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      intro g hg c hc'
      rw [Subgroup.mem_centralizer_iff] at hc' ⊢
      intro u hu
      have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ hg) u).mp hu
      have h1 := hc' _ hu'
      calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g⁻¹⁻¹) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * u := by group
    refine ⟨key h hhU c, fun hc' => ?_⟩
    have := key h⁻¹ (Subgroup.inv_mem _ hhU) _ hc'
    simpa [mul_assoc] using this
  have hJTv : thompsonJ T ≤ Tv := le_inf (thompsonJ_le_self T) fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (S.hJ hj) v hvV).symm)
  have hTv2 : IsPGroup 2 ↥Tv := hfsu.sylow.1.to_le inf_le_left
  obtain ⟨hJeq, -⟩ := h3108 G T L I (fsuV T I) hfsu S.isVplus_V S.hJ Tv hTv2 hJTv
  by_contra hne
  by_cases hJU : thompsonJ T ≤ Subgroup.centralizer (U : Set G)
  ·
    set C := H ⊓ Subgroup.centralizer (U : Set G) with hC
    have hCH : C ≤ H := inf_le_left
    have hCn : H ≤ Subgroup.normalizer (C : Set G) := fun h hh =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hh, hHCU hh⟩
    have hSC : IsSylowTwoOf (Tv ⊓ C) C := A4.isSylowTwoOf_inf_normal hTvH hCH hCn
    have hJSC : thompsonJ T ≤ Tv ⊓ C :=
      le_inf hJTv (le_inf (hJTv.trans le_sup_right) hJU)
    obtain ⟨-, hNSC⟩ := h3108 G T L I (fsuV T I) hfsu S.isVplus_V S.hJ (Tv ⊓ C)
      (hTv2.to_le inf_le_left) hJSC
    have hfr := B6.frattini_two hCH hCn hSC
    have hLWH : LW ≤ H := hlt.le.trans le_sup_left
    have hLWC : H ≤ Subgroup.normalizer ((LW ⊔ C : Subgroup G) : Set G) := by
      intro h hh
      obtain ⟨c, hcC, m, hm, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer
        (fun x (hx : x ∈ H ⊓ Subgroup.normalizer ((Tv ⊓ C : Subgroup G) : Set G)) =>
          hCn hx.1)).mp (hfr hh)
      refine Subgroup.mul_mem _ ?_ ?_
      · refine mem_normalizer_sup_of_map_le ?_ ?_
        · rintro _ ⟨l, hl, rfl⟩
          have hlc : l⁻¹ * c * l ∈ C := by
            have := (Subgroup.mem_normalizer_iff.mp (hCn (hLWH (LW.inv_mem hl))) c).mp hcC
            simpa using this
          have e1 : (MulAut.conj c).toMonoidHom l = l * (l⁻¹ * c * l) * c⁻¹ := by
            simp [mul_assoc]
          rw [e1]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
            (Subgroup.mem_sup_right hlc)) (Subgroup.mem_sup_right (C.inv_mem hcC))
        · rintro _ ⟨c', hc', rfl⟩
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hCn (hCH hcC)) c').mp hc')
      · have hmM : m ∈ fsuM T L := hNSC hm.2
        have hmLW : m ∈ Subgroup.normalizer (LW : Set G) := hnormLW ⟨hmM, hHG hm.1⟩
        refine mem_normalizer_sup_of_map_le ?_ ?_
        · rintro _ ⟨l, hl, rfl⟩
          exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hmLW l).mp hl)
        · rintro _ ⟨c', hc', rfl⟩
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hCn hm.1) c').mp hc')
    set R := (LW ⊔ C) ⊓ Lv with hR
    have hRn : (R.subgroupOf Lv).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hLWC (Subgroup.mem_sup_left hx),
          Subgroup.le_normalizer hx⟩
    have hLWR : LW ≤ R := le_inf le_sup_left hlt.le
    have hRL : R = Lv := by
      by_contra hRne
      have hRlt : R < Lv := lt_of_le_of_ne inf_le_right hRne
      have h0 := perfectCore_eq_bot_of_subnormal_lt hLv (A4.subnormal_of_normal inf_le_right hRn)
        hRlt
      have hLWp := le_perfectCore_of_perfect hLWR (hc.perfect_lPt h37c h38c hK4 hX)
      rw [h0, le_bot_iff] at hLWp
      exact ne_bot_of_mem_cComp (hc.mem_lFamily_lPt h37c h38c hK4 hX hTvN) hLWp
    apply hne
    intro x hx
    have hx' : x ∈ C ⊔ LW := by
      rw [sup_comm]
      exact (hRL.symm ▸ hx : x ∈ R).1
    obtain ⟨c, hcC, l, hl, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer
      (fun y hy => hCn (hLWH hy))).mp hx'
    have hcLv : c ∈ Lv := by
      have := Lv.mul_mem hx (Lv.inv_mem (hlt.le hl))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hcLv, hcC.2⟩) (Subgroup.mem_sup_left hl)
  ·
    have hv2 : v ^ 2 = 1 := S.hV.2 v hvV
    have hvH : v ∈ H := Subgroup.mem_sup_right ⟨S.fsuV_le_T hvV,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hvOH := mem_pCoreOf_of_le_centralizer hv2 hv1 hvH hHG
    apply hFb G H Tv LW Lv U Wp v
      (sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian (by
        intro h0
        rw [h0, Subgroup.mem_bot] at hvOH
        exact hv1 hvOH))
      hTvH (hlt.le.trans le_sup_left) (hc.mem_lFamily_lPt h37c h38c hK4 hX hTvN) hTvN
      (hc.lPt_quot h37c h38c hK4 hX).1 hLvH hlt
      (sup_le Subgroup.le_normalizer hTvLv) hUr ?_ hne hWpU (hc.perp_le_commutator hK4 hX) ?_
      (inV_line_le_perp (e := e) hv) hv1
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.mp (hLvG hl) |>
        Subgroup.mem_centralizer_singleton_iff.mpr)
    · rw [← hJeq]
      intro hJL
      apply hJU
      have hUle : U ≤ Subgroup.centralizer (thompsonJ T : Set G) := by
        rw [hU, conjClosure, Subgroup.closure_le]
        rintro _ ⟨h, hh, z, hzZ, rfl⟩
        obtain ⟨l, hl, t, ht, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hTvLv).mp hh
        have hzT := hZT hzZ
        have htz : t * z * t⁻¹ = z := by
          rw [Subgroup.mem_centralizer_iff.mp hzT.2 t ht.1, mul_inv_cancel_right]
        have e1 : l * t * z * (l * t)⁻¹ = l * z * l⁻¹ := by
          calc l * t * z * (l * t)⁻¹ = l * (t * z * t⁻¹) * l⁻¹ := by group
            _ = l * z * l⁻¹ := by rw [htz]
        rw [e1]
        show l * z * l⁻¹ ∈ Subgroup.centralizer (thompsonJ T : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hc' : l⁻¹ * j * l * j⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
          have := hJL (Subgroup.commutator_mem_commutator (Lv.inv_mem hl) hj)
          simpa [commutatorElement_def] using this
        have hzU : z ∈ U := by
          have := mem_conjClosure (Subgroup.one_mem H) hzZ
          simpa using this
        have hjz : j * z = z * j :=
          (Subgroup.mem_centralizer_iff.mp hzT.2 j (thompsonJ_le_self T hj))
        have hcz := Subgroup.mem_centralizer_iff.mp hc' z hzU
        calc j * (l * z * l⁻¹) = (l * (l⁻¹ * j * l * j⁻¹)) * (j * z) * l⁻¹ := by group
          _ = (l * (l⁻¹ * j * l * j⁻¹)) * (z * j) * l⁻¹ := by rw [hjz]
          _ = l * ((l⁻¹ * j * l * j⁻¹) * z) * j * l⁻¹ := by group
          _ = l * (z * (l⁻¹ * j * l * j⁻¹)) * j * l⁻¹ := by rw [hcz]
          _ = l * z * l⁻¹ * j := by group
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp (hUle hu) j hj).symm
    · intro k hk
      obtain ⟨k', hk', rfl⟩ := hk
      rw [(hc.lPt_quot h37c h38c hK4 hX).2] at hk'
      have hk'' : lPtHom ψ (inV e (Om4Pt.lineM X₀)) k' = 1 := hk'
      have hq := hc.mem_Q_of_psi_eq_one h37c h38c (Subgroup.inclusion (lPt_le_L0 T L W) k') hk''
      exact Subgroup.centralizer_le (inV_le e _) hq.2

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
