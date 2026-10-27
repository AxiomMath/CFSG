module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptY2
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptSyl
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314E

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.Ins314
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3319
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G}

theorem inf_centralizer_mPlus_vPlus_eq_bot {T L : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hVT : vPlus L T ≤ T) (hV2 : ∀ x ∈ vPlus L T, x ^ 2 = 1)
    (hC0 : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G) = ⊥) :
    Subgroup.centralizer (mPlus L T : Set G) ⊓ vPlus L T = ⊥ := by
  by_contra hne
  set N := Subgroup.centralizer (mPlus L T : Set G) ⊓ vPlus L T with hN
  have hNT : N ≤ T := inf_le_right.trans hVT
  have hTM : T ≤ Subgroup.normalizer (mPlus L T : Set G) := le_normalizer_conjClosure_right L T
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ T, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
      intro y hy n hn
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have hm' : y⁻¹ * m * y ∈ mPlus L T :=
          (Subgroup.mem_normalizer_iff.mp (hTM (T.inv_mem hy)) m).mp hm |> fun h => by
            simpa using h
        have h1 := Subgroup.mem_centralizer_iff.mp hn.1 _ hm'
        calc m * (y * n * y⁻¹) = y * ((y⁻¹ * m * y) * n) * y⁻¹ := by group
          _ = y * (n * (y⁻¹ * m * y)) * y⁻¹ := by rw [← h1]
          _ = y * n * y⁻¹ * m := by group
      · exact (Subgroup.mem_normalizer_iff.mp (Hyp331.le_normalizer_vPlus L T hy) n).mp hn.2
    intro n
    refine ⟨fun hn => key x hx n hn, fun hn => ?_⟩
    have := key x⁻¹ (T.inv_mem hx) _ hn
    simpa [mul_assoc] using this
  have hNn : (N.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr hTN
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hbot : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hn1
    have : (⟨n.1, hNT n.2⟩ : ↥T) ∈ N.subgroupOf T := n.2
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext (show (n : G) = 1 from congrArg (fun x : ↥T => (x : G)) this)
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hbot
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hc
  have hx := x.2
  have hxN : ((x : ↥T) : G) ∈ N := hx.1
  have hxZ : (x : ↥T) ∈ Subgroup.center ↥T := hx.2
  have hxV : ((x : ↥T) : G) ∈ vPlus L T := hxN.2
  have hxZ' : ((x : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
    apply Subgroup.subset_closure
    refine ⟨⟨(x : ↥T).2, ?_⟩, hV2 _ hxV⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨y, hy⟩)
  have h5 : ((x : ↥T) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hC0]
    exact ⟨hxZ', hxN.1⟩
  apply hx1
  exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp h5))

theorem commute_of_two_power_odd {y w : G} {V₁ : Subgroup G} (hy : Odd (orderOf y)) (k : ℕ)
    (hw : w ^ 2 ^ k = 1) (hV : ∀ v ∈ V₁, y⁻¹ * v * y ∈ V₁)
    (hconj : ∀ v ∈ V₁, w * v * w⁻¹ = y⁻¹ * v * y) : ∀ v ∈ V₁, y * v = v * y := by
  have hpow : ∀ (j : ℕ) (v : G), v ∈ V₁ →
      (y⁻¹ ^ j * v * y ^ j ∈ V₁) ∧ w ^ j * v * (w ^ j)⁻¹ = y⁻¹ ^ j * v * y ^ j := by
    intro j
    induction j with
    | zero => intro v hv; simpa using hv
    | succ j ih =>
      intro v hv
      obtain ⟨h1, h2⟩ := ih v hv
      refine ⟨?_, ?_⟩
      · have e : y⁻¹ ^ (j + 1) * v * y ^ (j + 1) = y⁻¹ * (y⁻¹ ^ j * v * y ^ j) * y := by
          rw [pow_succ', pow_succ]; group
        rw [e]
        exact hV _ h1
      · have h3 := hconj _ h1
        calc w ^ (j + 1) * v * (w ^ (j + 1))⁻¹
            = w * (w ^ j * v * (w ^ j)⁻¹) * w⁻¹ := by group
          _ = w * (y⁻¹ ^ j * v * y ^ j) * w⁻¹ := by rw [h2]
          _ = y⁻¹ * (y⁻¹ ^ j * v * y ^ j) * y := h3
          _ = y⁻¹ ^ (j + 1) * v * y ^ (j + 1) := by rw [pow_succ', pow_succ]; group
  intro v hv
  obtain ⟨-, h2⟩ := hpow (2 ^ k) v hv
  rw [hw] at h2
  simp only [inv_one, mul_one, one_mul] at h2
  have ha : y ^ 2 ^ k * v = v * y ^ 2 ^ k := by
    have : v * y ^ 2 ^ k = y ^ 2 ^ k * v := by
      calc v * y ^ 2 ^ k = (y⁻¹ ^ 2 ^ k)⁻¹ * (y⁻¹ ^ 2 ^ k * v * y ^ 2 ^ k) := by group
        _ = (y⁻¹ ^ 2 ^ k)⁻¹ * v := by rw [← h2]
        _ = y ^ 2 ^ k * v := by group
    exact this.symm
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hy)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact (Commute.pow_left (show Commute (y ^ 2 ^ k) v from ha) u).eq

theorem oTwoUpper_le_mPlus {t : G} (e : Sett T M L t) (hHLT : H ≤ L ⊔ T) :
    oTwoUpper H ≤ mPlus L T := by
  unfold oTwoUpper
  rw [Subgroup.closure_le]
  rintro x ⟨hxH, hxo⟩
  obtain ⟨b, hb⟩ := e.exists_two_pow_mem_mPlus x (hHLT hxH)
  have hcop : Nat.Coprime (2 ^ b) (orderOf x) :=
    Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hxo)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact Subgroup.pow_mem _ hb u

theorem mPlus_le_normalizer_V1 {t : G} (e : Sett T M L t) :
    mPlus L T ≤ Subgroup.normalizer (⁅vPlus L T, L⁆ : Subgroup G) := by
  rw [e.hM]
  exact sup_le (fun x hx => e.L_le_N_V1 hx) (fun x hx => e.L2_le_N_V1 hx)

theorem TC_le_normalizer_L {t : G} (c : NFConfig G T M L D H K) (e : Sett T M L t)
    {y : G} (hyY : y ∈ oTwoUpper H) (hyo : Odd (orderOf y))
    (hy2 : y ∈ Subgroup.centralizer ((⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G))
    (hy1 : y ∉ Subgroup.centralizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G)) :
    pCoreOf 2 (conjClosure K T ⊔ T) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  by_contra hsn
  have hTsyl : IsSylowTwoOf T (conjClosure K T ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow le_sup_right
  have hsT : s ∈ T := pCoreOf_le_of_isSylowTwoOf hTsyl hs
  have hsn' : s⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun h => hsn (by simpa using Subgroup.inv_mem _ h)
  obtain ⟨hs1, hs2⟩ := e.swap_V hsT hsn
  obtain ⟨hs1', hs2'⟩ := e.swap_V (T.inv_mem hsT) hsn'
  have hyN : y ∈ Subgroup.normalizer (⁅vPlus L T, L⁆ : Subgroup G) :=
    mPlus_le_normalizer_V1 e (oTwoUpper_le_mPlus e c.HLT hyY)
  set TC := pCoreOf 2 (conjClosure K T ⊔ T) with hTC
  have hTH : T ≤ H := c.inH.1
  have hsY : s ∈ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H (hTH hsT)
  have hyK : y ∈ conjClosure K T ⊔ T := Subgroup.mem_sup_left (c.YK hyY)
  have hwY : s * y * s⁻¹ * y⁻¹ ∈ oTwoUpper H := by
    have h1 : s * y * s⁻¹ ∈ oTwoUpper H := (Subgroup.mem_normalizer_iff.mp hsY y).mp hyY
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hyY)
  have hwTC : s * y * s⁻¹ * y⁻¹ ∈ TC := by
    have h1 : y * s⁻¹ * y⁻¹ ∈ TC :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure K T ⊔ T) hyK) s⁻¹).mp
        (TC.inv_mem hs)
    have := TC.mul_mem hs h1
    simpa [mul_assoc] using this
  have hw2 : s * y * s⁻¹ * y⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    have hle : (oTwoUpper H ⊓ TC) ≤ pCoreOf 2 (oTwoUpper H) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_right
      intro u hu
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hu, ?_⟩
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure K T ⊔ T)
        (Subgroup.mem_sup_left (c.YK hu))
    exact hle ⟨hwY, hwTC⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oTwoUpper H)
    ⟨_, hw2⟩
  have hwk : (s * y * s⁻¹ * y⁻¹) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hVinv : ∀ v ∈ (⁅vPlus L T, L⁆ : Subgroup G), y⁻¹ * v * y ∈ (⁅vPlus L T, L⁆ : Subgroup G) := by
    intro v hv
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) v).mp hv
    simpa using this
  have hconj : ∀ v ∈ (⁅vPlus L T, L⁆ : Subgroup G),
      (s * y * s⁻¹ * y⁻¹) * v * (s * y * s⁻¹ * y⁻¹)⁻¹ = y⁻¹ * v * y := by
    intro v hv
    have hv' := hVinv v hv
    have hu : s⁻¹ * (y⁻¹ * v * y) * s ∈ (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) := by
      have h3 : (MulAut.conj s⁻¹).toMonoidHom (y⁻¹ * v * y) ∈
          (⁅vPlus L T, L⁆ : Subgroup G).map (MulAut.conj s⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hv'
      rw [hs1'] at h3
      simpa using h3
    have hyu : y * (s⁻¹ * (y⁻¹ * v * y) * s) * y⁻¹ = s⁻¹ * (y⁻¹ * v * y) * s := by
      have := (Subgroup.mem_centralizer_iff.mp hy2 _ hu)
      calc y * (s⁻¹ * (y⁻¹ * v * y) * s) * y⁻¹
          = (y * (s⁻¹ * (y⁻¹ * v * y) * s)) * y⁻¹ := rfl
        _ = ((s⁻¹ * (y⁻¹ * v * y) * s) * y) * y⁻¹ := by rw [this]
        _ = s⁻¹ * (y⁻¹ * v * y) * s := by group
    calc (s * y * s⁻¹ * y⁻¹) * v * (s * y * s⁻¹ * y⁻¹)⁻¹
        = s * (y * (s⁻¹ * (y⁻¹ * v * y) * s) * y⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * (y⁻¹ * v * y) * s) * s⁻¹ := by rw [hyu]
      _ = y⁻¹ * v * y := by group
  have hcomm := commute_of_two_power_odd hyo k hwk hVinv hconj
  apply hy1
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (hcomm v hv).symm

omit [Finite G] in
theorem cComp_of_le_of_le' {H X K : Subgroup G} (hK : K ∈ cComp H) (hKX : K ≤ X)
    (hXH : X ≤ H) : K ∈ cComp X :=
  ⟨hK.1, hK.2.1, A3.subnormal_of_le_of_le hK.2.2.1 hKX hXH, fun J hJK hJ1 hJp hJX =>
    hK.2.2.2 J hJK hJ1 hJp (A3.subnormal_trans (A3.subnormal_of_le_of_le hJX hJK.le hKX)
      hK.2.2.1)⟩

theorem L2_isLocal {t : G} (e : Sett T M L t) (hT2 : IsPGroup 2 ↥T) {e₀ : G}
    (he₀TL : e₀ ∈ T ⊓ Subgroup.normalizer (L : Set G)) (he₀1 : e₀ ≠ 1)
    (he₀T : ∀ s ∈ T ⊓ Subgroup.normalizer (L : Set G), s * e₀ = e₀ * s)
    (he₀L2 : ∀ m ∈ CFSG.conjugate L t, m * e₀ = e₀ * m) :
    quasithinIsLocal (T ⊓ Subgroup.normalizer (L : Set G)) (CFSG.conjugate L t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set TL := T ⊓ Subgroup.normalizer (L : Set G) with hTL
  set L2 := CFSG.conjugate L t with hL2
  have hTL2 : IsPGroup 2 ↥TL := hT2.to_le inf_le_left
  have hTLN : TL ≤ Subgroup.normalizer (L2 : Set G) := fun s hs =>
    e.TL_le_normalizer_L2 hs.1 hs.2
  have hSyl : IsSylowTwoOf (T ⊓ L2) L2 :=
    CFSG.QuasithinUnique.L246C127.isSylowTwoOf_inf_of_isSubnormal'
      (subnormal_of_mem_cComp e.L2_mem_cComp) e.s.isSylowTwoOf
  have hSTL : T ⊓ L2 ≤ TL :=
    le_inf inf_le_left (inf_le_right.trans (fun x hx => e.L2_le_normalizer_L hx))
  have hSyl2 : IsSylowTwoOf TL (L2 ⊔ TL) := isSylowTwoOf_sup_of_normalizer hTL2 hTLN hSyl hSTL
  refine ⟨hTL2, ?_, hSyl2.2.2, ?_⟩
  · exact cComp_of_le_of_le' e.L2_mem_cComp le_sup_left
      (sup_le e.L2_le (inf_le_left.trans le_sup_right))
  · intro hbot
    have hC : L2 ⊔ TL ≤ Subgroup.centralizer ({e₀} : Set G) := by
      refine sup_le (fun m hm => ?_) (fun s hs => ?_)
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff.mp hh]
        exact (he₀L2 m hm).symm
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff.mp hh]
        exact (he₀T s hs).symm
    have hnorm : L2 ⊔ TL ≤ Subgroup.normalizer ((Subgroup.zpowers e₀ : Subgroup G) : Set G) := by
      intro x hx
      have hxc := Subgroup.mem_centralizer_iff.mp (hC hx) e₀ (Set.mem_singleton _)
      have : x ∈ Subgroup.centralizer ((Subgroup.zpowers e₀ : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact (Commute.zpow_left (show Commute e₀ x from hxc) k).eq
      exact Subgroup.centralizer_le_normalizer _ this
    have hz : Subgroup.zpowers e₀ ≤ pCoreOf 2 (L2 ⊔ TL) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right he₀TL)) hnorm
        (hTL2.to_le (Subgroup.zpowers_le.mpr he₀TL))
    rw [hbot] at hz
    have : e₀ ∈ (⊥ : Subgroup G) := hz (Subgroup.mem_zpowers e₀)
    exact he₀1 (Subgroup.mem_bot.mp this)

theorem obl3_3_13D12NF_314pt_of
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (lA : LeafYO2) (lB : LeafVY) (lC : LeafYsplit) (lS : LeafS) (lF2 : LeafF2) (lF3 : LeafF3) :
    Obl3_3_13D12NF_314pt := by
  intro G _ _ T M L D H K h hP hH hHLT hwr hO hK hKq hYK hTK hKf hin hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have c : NFConfig G T M L D H K := ⟨h, hH, hHLT, hwr, hO, hK, hKq, hYK, hTK, hKf, hq⟩
  have cfg : Cfg G T M L D H K := ⟨c, hP, hin⟩
  obtain ⟨⟨hTL, hcomm, hcase, hPSL⟩, hfix⟩ := hP
  obtain ⟨t, ht, htn, hM, hcommA, hbot, -, htc, htcI, hmod⟩ := hcase
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 168 := by
    obtain ⟨e⟩ := nonempty_equiv_of_isPSL hPSL
    rw [Nat.card_congr e.toEquiv, card_L3Γ]
  have sett : Sett T M L t := ⟨h.toSetup331, ht, htn, hM, hcommA, hbot, h37, h38, hcard⟩
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hV2 : ∀ x ∈ vPlus L T, x ^ 2 = 1 := hred.2.1.2
  have hTsylLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right
  have hTH : T ≤ H := hH.1
  have hVO : vPlus L T ≤ pCoreOf 2 (L ⊔ T) := hred.1.trans inf_le_left
  have hVT : vPlus L T ≤ T := hVO.trans (pCoreOf_le_of_isSylowTwoOf hTsylLT)
  have hC0 := c.inf_centralizer_mPlus_eq_bot h36 h5 h128 h37 h38 h39
  have h74 : vPlus L T = ⁅vPlus L T, mPlus L T⁆ := by
    have := (h7 G T M L D h).2.2.2.2
    rwa [hC0, sup_bot_eq] at this
  have hCV := inf_centralizer_mPlus_vPlus_eq_bot h.sylow.1 hVT hV2 hC0
  have hI := sett.V1_inf_V2 htcI hCV
  have hVs := sett.V_eq_sup h74
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (quasithinOmegaOneCenter_ne_bot h.sylow.1 h.toSetup331.T_ne_bot)
  have hzZ : (a : G) ∈ quasithinOmegaOneCenter T := a.2
  have hz1 : (a : G) ≠ 1 := fun h1 => ha (Subtype.ext h1)
  obtain ⟨e₀, he₀V1, he₀1, he₀2, he₀TL, he₀L2, he₀T⟩ := sett.exists_e hV2 hVs hI hzZ hz1
  have he₀V : e₀ ∈ vPlus L T :=
    commutator_le_of_le_normalizer (le_sup_left.trans sett.hX) he₀V1
  have hVY : vPlus L T = ⁅vPlus L T, oTwoUpper H⁆ := lB G T M L D H K cfg
  have hYO2 : ⁅pCoreOf 2 (oTwoUpper H), oTwoUpper H⁆ ≤ pCoreOf 2 (conjClosure K T) :=
    lA G T M L D H K c hin
  obtain ⟨y, hyY, hyo, -, hy2, hy1⟩ := lC G T M L D H K cfg t ht htn
  set K0 := conjClosure K T with hK0
  set TC := pCoreOf 2 (K0 ⊔ T) with hTC
  have hVH : vPlus L T ≤ pCoreOf 2 H := by
    refine hVO.trans ?_
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    · exact (pCoreOf_le_of_isSylowTwoOf hTsylLT).trans hTH
    · exact hHLT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hVYsub : vPlus L T ≤ pCoreOf 2 (oTwoUpper H) := by
    have hle : (⁅vPlus L T, oTwoUpper H⁆ : Subgroup G) ≤ pCoreOf 2 (oTwoUpper H) := by
      rw [Subgroup.commutator_le]
      intro v hv u hu
      have hvH : v ∈ H := hTH (hVT hv)
      have h1 : ⁅v, u⁆ ∈ pCoreOf 2 H := by
        have := Subgroup.mul_mem _ (hVH hv)
          ((Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hYH hu)) v⁻¹).mp
            ((pCoreOf 2 H).inv_mem (hVH hv)))
        simpa [commutatorElement_def, mul_assoc] using this
      have h2 : ⁅v, u⁆ ∈ oTwoUpper H := by
        have := Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_oTwoUpper H hvH) u).mp hu) ((oTwoUpper H).inv_mem hu)
        simpa [commutatorElement_def, mul_assoc] using this
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_right : pCoreOf 2 H ⊓ oTwoUpper H ≤ oTwoUpper H) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left ⟨h1, h2⟩
      intro w hw
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hw⟩
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hYH hw)
    rw [← hVY] at hle
    exact hle
  have hK0T : T ≤ Subgroup.normalizer (K0 : Set G) := le_normalizer_conjClosure K T
  have hO2K0 : pCoreOf 2 K0 ≤ TC := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K0)
    · exact (Subgroup.map_subtype_le _ : pCoreOf 2 K0 ≤ K0).trans le_sup_left
    · refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K0) ?_
      exact fun x hx => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K0 (hK0T hx)
  have hVTC : vPlus L T ≤ TC :=
    calc vPlus L T = ⁅vPlus L T, oTwoUpper H⁆ := hVY
      _ ≤ ⁅pCoreOf 2 (oTwoUpper H), oTwoUpper H⁆ := Subgroup.commutator_mono hVYsub le_rfl
      _ ≤ pCoreOf 2 K0 := hYO2
      _ ≤ TC := hO2K0
  have hTCL : TC ≤ Subgroup.normalizer (L : Set G) :=
    TC_le_normalizer_L c sett hyY hyo hy2 hy1
  have hTCT : TC ≤ T := pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
  have he₀TC : e₀ ∈ TC := hVTC he₀V
  have hcentTC : ∀ x ∈ TC, x * e₀ = e₀ * x := fun x hx => he₀TL x ⟨hTCT hx, hTCL hx⟩
  have hK0e : K0 ≤ Subgroup.centralizer ({e₀} : Set G) :=
    lS G T M L D H K c e₀ he₀TC he₀2 hcentTC
  have hTe : T ⊓ Subgroup.centralizer ({e₀} : Set G) = T ⊓ Subgroup.normalizer (L : Set G) := by
    ext s
    constructor
    · rintro ⟨hsT, hsC⟩
      refine ⟨hsT, he₀T s hsT ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp hsC e₀ (Set.mem_singleton _)).symm
    · rintro ⟨hsT, hsN⟩
      refine ⟨hsT, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      rw [Set.mem_singleton_iff.mp hx]
      exact (he₀TL s ⟨hsT, hsN⟩).symm
  have hL2e : CFSG.conjugate L t ≤ Subgroup.centralizer ({e₀} : Set G) := by
    intro m hm
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    rw [Set.mem_singleton_iff.mp hx]
    exact (he₀L2 m hm).symm
  have hL2M : ¬ CFSG.conjugate L t ≤ Subgroup.normalizer (K0 : Set G) := by
    intro hle
    apply c.not_le_normalizer h5 h128 h37 h38 h39
    refine sup_le ?_ (le_normalizer_conjClosure K T)
    rw [hM]
    refine sup_le (fun x hx => ?_) hle
    have hx' : t⁻¹ * x * t ∈ CFSG.conjugate L t := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK0T ht) (hle hx')) (Subgroup.inv_mem _ (hK0T ht))
    simpa [mul_assoc] using h1
  have hF : FCfg G T M L D H K (T ⊓ Subgroup.normalizer (L : Set G)) (CFSG.conjugate L t) e₀ :=
    { nf := c
      TL_le := inf_le_left
      TL_idx := sett.card_le_two_mul_TL
      e_T := hVT he₀V
      e_ne := he₀1
      e_sq := he₀2
      K0_e := hK0e
      T_e := hTe
      L2_e := hL2e
      L2_notM := hL2M }
  by_cases hcen : ∃ g : G, g⁻¹ * e₀ * g ∈ quasithinOmegaOneCenter T
  · exact lF2 G T M L D H K _ _ e₀ hF hcen
  ·
    have hy'K : t * y * t⁻¹ ∈ K0 :=
      (Subgroup.mem_normalizer_iff.mp (hK0T ht) y).mp (c.YK hyY)
    have hy'M : t * y * t⁻¹ ∈ mPlus L T :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure_right L T ht) y).mp
        (oTwoUpper_le_mPlus sett hHLT hyY)
    have hy'2 : t * y * t⁻¹ ∉
        Subgroup.centralizer ((⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
      intro hc
      apply hy1
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨h1, -⟩ := sett.swap_V ht htn
      have hv' : t * v * t⁻¹ ∈ (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) := by
        have h3 : (MulAut.conj t).toMonoidHom v ∈
            (⁅vPlus L T, L⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hv
        rw [h1] at h3
        simpa using h3
      have h4 := Subgroup.mem_centralizer_iff.mp hc _ hv'
      have h5 : t * (v * y) * t⁻¹ = t * (y * v) * t⁻¹ := by
        calc t * (v * y) * t⁻¹ = (t * v * t⁻¹) * (t * y * t⁻¹) := by group
          _ = (t * y * t⁻¹) * (t * v * t⁻¹) := h4
          _ = t * (y * v) * t⁻¹ := by group
      have h6 := mul_left_cancel (mul_right_cancel h5)
      exact h6
    refine lF3 G T M L D H K _ _ e₀ hF
      (L2_isLocal sett h.sylow.1 ⟨hVT he₀V, hTCL (hVTC he₀V)⟩ he₀1 he₀TL he₀L2)
      (fun s hs => sett.TL_le_normalizer_L2 hs.1 hs.2) (sett.isPSL_modO2_L2 hPSL) ?_ hcen
    intro hle
    exact sett.false_of_commutator_le hPSL hI hL2e hy'K hy'M hy'2 hle

end CFSG.Quasithin.H13.NF314pt
