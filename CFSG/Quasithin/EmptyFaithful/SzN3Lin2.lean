module

public import CFSG.Quasithin.EmptyFaithful.S153F18B
public import CFSG.Quasithin.EmptyFaithful.SzN3V2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem szN3_oTwoUpper_le_of_decomp [Finite G] {B Z K : Subgroup G}
    (hN : Z ≤ Subgroup.normalizer (B : Set G)) (hK : IsPGroup 2 K) (hKZ : K ≤ Z)
    (hdec : ∀ z ∈ Z, ∃ b ∈ B, ∃ k ∈ K, z = b * k) : oTwoUpper Z ≤ B := by
  refine oTwoUpper_le_of_pow_mem fun z hz => ?_
  obtain ⟨b, hb, k, hk, rfl⟩ := hdec z hz
  obtain ⟨j, hj⟩ := hK ⟨k, hk⟩
  have hkj : k ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  refine ⟨j, ?_⟩
  have key : ∀ m : ℕ, ∃ b' ∈ B, (b * k) ^ m = b' * k ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, B.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨b', hb', e⟩ := ih
      refine ⟨b' * (k ^ m * b * (k ^ m)⁻¹), B.mul_mem hb' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hN (Z.pow_mem (hKZ hk) m)) b).mp hb
      · rw [pow_succ, e, pow_succ]; group
  obtain ⟨b', hb', e⟩ := key (2 ^ j)
  rw [e, hkj, mul_one]
  exact hb'

theorem szN3_oTwoUpper_le_oTwoUpper {A B : Subgroup G} (h : oTwoUpper A ≤ B) :
    oTwoUpper A ≤ oTwoUpper B := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, hodd⟩
  exact mem_oTwoUpper_of_odd (h (mem_oTwoUpper_of_odd hx hodd)) hodd

theorem szN3_eq_of_le_of_ne_bot {A P : Subgroup G} (hAP : A ≤ P) (hA : A ≠ ⊥)
    (hP : Nat.card P ∣ 3) : A = P := by
  have hP0 : Nat.card P ≠ 0 := fun h => by rw [h] at hP; omega
  have : Finite P := Nat.finite_of_card_ne_zero hP0
  have h1 : Nat.card A ∣ Nat.card P := Subgroup.card_dvd_of_le hAP
  have h2 : Nat.card A ≠ 1 := fun h => hA (Subgroup.card_eq_one.mp h)
  have h3 : Nat.card A ∣ 3 := h1.trans hP
  have h4 : Nat.card A = 3 := ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left h2
  have h5 : Nat.card P ≤ 3 := Nat.le_of_dvd (by norm_num) hP
  exact Subgroup.eq_of_le_of_card_ge hAP (by omega)

end Generic

section Model

variable {W : Type} [CommGroup W] [Finite W] {X La Lb : Subgroup (MulAut W)} {t : MulAut W}

theorem szN3_card_inf_oTwoUpper_dvd (h : OfourStruct X La Lb t) :
    Nat.card ↥(Lb ⊓ oTwoUpper X) ∣ 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPG : IsPGroup 3 ↥(Lb ⊓ oTwoUpper X) := fun x =>
    ⟨1, Subtype.ext (by simpa using h.pow_three_of_mem_oTwoUpper x.2.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hPG
  have hd : Nat.card ↥(Lb ⊓ oTwoUpper X) ∣ 6 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Lb ⊓ oTwoUpper X ≤ Lb)
    rwa [h.card_L₂] at this
  rw [hn] at hd ⊢
  rcases n with _ | _ | n
  · simp
  · simp
  · exfalso
    have : 9 ∣ 3 ^ (n + 2) := by
      rw [pow_add]; exact Dvd.intro_left _ rfl
    have h9 : 9 ∣ 6 := this.trans hd
    omega

end Model

section Action

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}

theorem szN3_exists_commutator_eq {U : Subgroup (IntMod V hV)} {y : G}
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hst : ∀ u ∈ U, convI hV ⟨y, hyN⟩ u ∈ U)
    (hfix : ∀ u ∈ U, convI hV ⟨y, hyN⟩ u = u → u = 1) :
    ∀ u₀ ∈ U, ∃ u ∈ U, ⁅u.val, y⁆ = u₀.val := by
  intro u₀ hu₀
  obtain ⟨u, hu, hu0⟩ := szN3_exists_mul_inv_apply_eq hst hfix u₀ hu₀
  refine ⟨u, hu, ?_⟩
  have h2 : (convI hV ⟨y, hyN⟩ u).val = y * u.val * y⁻¹ := convI_apply_val hV ⟨y, hyN⟩ u
  rw [← hu0, IntMod.val_mul, IntMod.val_inv, h2, commutatorElement_def]
  group

end Action

section Decomp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem szN3_decomp {V Y B Z : Subgroup G} {hV : IsElemAbelian 2 V}
    (hYN : Y ≤ Subgroup.normalizer (V : Set G))
    (hcore : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (V : Set G)) (hBY : B ≤ Y) (hZY : Z ≤ Y)
    (hZ : ∀ z (hz : z ∈ Z), convI hV ⟨z, hYN (hZY hz)⟩ ∈ autI hV B) :
    ∀ z ∈ Z, ∃ b ∈ B, ∃ k ∈ pCoreOf 2 Y, z = b * k := by
  intro z hz
  obtain ⟨b, hbB, hb⟩ := (mem_autI hV).1 (hZ z hz)
  refine ⟨b, hbB, (b : G)⁻¹ * z, ?_, by group⟩
  have hc1 : convI hV (b⁻¹ * ⟨z, hYN (hZY hz)⟩) = 1 := by
    rw [map_mul, map_inv, hb, inv_mul_cancel]
  have hkC := (convI_eq_one_iff hV _).1 hc1
  rw [hcore]
  exact ⟨Y.mul_mem (Y.inv_mem (hBY hbB)) (hZY hz), hkC⟩

end Decomp

section Key

variable {G : Type} [Group G] [Finite G] {T Mc M L : Subgroup G}

theorem szN3_key (h113 : StageLemma14113) (hyp : Hyp153 G T Mc M) {hV : IsElemAbelian 2 (VZ T M)}
    {La Lb : Subgroup (MulAut (IntMod (VZ T M) hV))} {tb : MulAut (IntMod (VZ T M) hV)}
    (hS : OfourStruct (autI hV M) La Lb tb) {Va Vb : Subgroup G}
    (hVa : Va = (commV La).map (inclMod hV)) (hVb : Vb = (commV Lb).map (inclMod hV))
    (hcore : pCoreOf 2 (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G))
    (hYpeq : Y153 Mc M = YL153 (Y153 Mc M) L ⊔ YC153 (Y153 Mc M) L)
    (hYC : YC153 (Y153 Mc M) L ≤ Subgroup.centralizer (L : Set G))
    (hVL : VZ T M ≤ Subgroup.normalizer (L : Set G))
    (hYLne : YL153 (Y153 Mc M) L ≠ ⊥)
    (hYLa : YL153 (Y153 Mc M) L ≤ Subgroup.centralizer (Va : Set G)) :
    YL153 (Y153 Mc M) L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (Va : Set G)) ∧
      YC153 (Y153 Mc M) L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (Vb : Set G)) := by
  classical
  subst hVa hVb
  have hMN := hyp.le_normalizer
  set Y := Y153 Mc M with hY
  set YL := YL153 Y L with hYL
  set YC := YC153 Y L with hYCdef
  set X := autI hV M with hX
  have hYM : Y ≤ M := Y153_le Mc M
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hMN
  have hYe : autI hV Y = oTwoUpper X := hyp.autOn_Y153 h113
  have hYLle : YL ≤ Y ⊓ L := oTwoUpper_le _
  have hYLY : YL ≤ Y := hYLle.trans inf_le_left
  have hYLL : YL ≤ L := hYLle.trans inf_le_right
  have hYCsec : YC ≤ centralizerSection Y L (pCoreOf 2 L) := oTwoUpper_le _
  have hYCY : YC ≤ Y := fun y hy => (hYCsec hy).1
  have hYNYL : Y ≤ Subgroup.normalizer (YL : Set G) := by
    have h : YL ⊔ YC ≤ Subgroup.normalizer (YL : Set G) :=
      sup_le Subgroup.le_normalizer fun g hg =>
        S153F.mem_normalizer_of_le_centralizer (hYC hg) hYLL
    rwa [← hYpeq] at h
  have hYNYC : Y ≤ Subgroup.normalizer (YC : Set G) := by
    have h : YL ⊔ YC ≤ Subgroup.normalizer (YC : Set G) := by
      refine sup_le (fun g hg => ?_) Subgroup.le_normalizer
      refine S153F.mem_normalizer_of_le_centralizer (P := YC) (C := YC) ?_ le_rfl
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hYC hy) g (hYLL hg)).symm
    rwa [← hYpeq] at h
  have hautY : autI hV Y = autI hV YL ⊔ autI hV YC := by
    have := autI_sup hV (hYLY.trans hYN) (hYCY.trans hYN)
    rwa [← hYpeq] at this
  obtain ⟨y, hyY, hyo, hy1⟩ : ∃ y ∈ Y ⊓ L, Odd (orderOf y) ∧ y ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hYLne
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, ho⟩
    exact Subgroup.mem_bot.mpr (hno x hx ho)
  have hyYL : y ∈ YL := mem_oTwoUpper_of_odd hyY hyo
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hyY.1
  have hconv1 : convI hV ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 h1
    have hyP : y ∈ pCoreOf 2 Y := by rw [hcore]; exact ⟨hyY.1, hyC⟩
    exact hy1 (S153F.eq_one_of_mem_pCoreOf_of_odd hyP hyo)
  have hautL_le : autI hV YL ≤ Lb ⊓ oTwoUpper X := by
    intro φ hφ
    obtain ⟨g, hgYL, rfl⟩ := (mem_autI hV).1 hφ
    have hφY : convI hV g ∈ autI hV Y := convI_mem_autI hV (hYLY hgYL) g.2
    rw [hYe] at hφY
    have hφX : convI hV g ∈ X := oTwoUpper_le _ hφY
    refine ⟨(hS.mem_L₂_iff hφX).2 fun u hu => ?_, hφY⟩
    exact (mem_centralizer_map_inclMod_iff hV g.2 (commV La)).1 (hYLa hgYL) u hu
  have hbotL : autI hV YL ≠ ⊥ := by
    intro hb
    have : convI hV ⟨y, hyN⟩ ∈ autI hV YL := convI_mem_autI hV hyYL hyN
    rw [hb, Subgroup.mem_bot] at this
    exact hconv1 this
  have hautL : autI hV YL = Lb ⊓ oTwoUpper X :=
    szN3_eq_of_le_of_ne_bot hautL_le hbotL (szN3_card_inf_oTwoUpper_dvd hS)
  have hx'mem : convI hV ⟨y, hyN⟩ ∈ Lb ⊓ oTwoUpper X := hautL ▸ convI_mem_autI hV hyYL hyN
  have hx'L : convI hV ⟨y, hyN⟩ ∈ Lb := hx'mem.1
  have hx'3 : (convI hV ⟨y, hyN⟩) ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper hx'mem.2
  have hx'odd : Odd (orderOf (convI hV ⟨y, hyN⟩)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx'3)
  have hVbL : ((commV Lb).map (inclMod hV) : Subgroup G) ≤ L := by
    have hst : ∀ u ∈ commV Lb, convI hV ⟨y, hyN⟩ u ∈ commV Lb :=
      fun u hu => commV_stable Lb hx'L hu
    have hfix : ∀ u ∈ commV Lb, convI hV ⟨y, hyN⟩ u = u → u = 1 := by
      intro u hu hxu
      by_contra hu1
      exact hconv1 (eq_one_of_odd_of_fixed hS.nat₂
        (fun l hl u hu => commV_stable Lb hl hu) hx'L hx'odd hu hu1 hxu)
    intro v hv
    obtain ⟨u₀, hu₀, rfl⟩ := hv
    obtain ⟨u, hu, hcomm⟩ := szN3_exists_commutator_eq hyN hst hfix u₀ hu₀
    have hu' : u.val ∈ Subgroup.normalizer (L : Set G) := hVL u.val_mem
    have h1 : u.val * y * u.val⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hu' y).mp hyY.2
    have : ⁅u.val, y⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem h1 (L.inv_mem hyY.2)
    rw [hcomm] at this
    exact this
  have hYCVb : YC ≤ Subgroup.centralizer (((commV Lb).map (inclMod hV) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.centralizer_le hVbL (hYC hg)
  have hautC_le : autI hV YC ≤ La ⊓ oTwoUpper X := by
    intro φ hφ
    obtain ⟨g, hgYC, rfl⟩ := (mem_autI hV).1 hφ
    have hφY : convI hV g ∈ autI hV Y := convI_mem_autI hV (hYCY hgYC) g.2
    rw [hYe] at hφY
    have hφX : convI hV g ∈ X := oTwoUpper_le _ hφY
    refine ⟨(hS.mem_L₁_iff hφX).2 fun u hu => ?_, hφY⟩
    exact (mem_centralizer_map_inclMod_iff hV g.2 (commV Lb)).1 (hYCVb hgYC) u hu
  have hbotC : autI hV YC ≠ ⊥ := by
    intro hb
    obtain ⟨a, haL, ha3, ha1⟩ := exists_orderThree hS.nat₁
    have haX : a ∈ X := hS.L₁_le haL
    have haO : a ∈ oTwoUpper X := mem_oTwoUpper_of_odd haX
      (Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ha3))
    rw [← hYe, hautY, hb, sup_bot_eq, hautL] at haO
    have : a ∈ La ⊓ Lb := ⟨haL, haO.1⟩
    rw [hS.Linf, Subgroup.mem_bot] at this
    exact ha1 this
  have hautC : autI hV YC = La ⊓ oTwoUpper X :=
    szN3_eq_of_le_of_ne_bot hautC_le hbotC (szN3_card_inf_oTwoUpper_dvd hS.symm)
  have hKle : ∀ {V' : Subgroup G}, V' ≤ VZ T M →
      pCoreOf 2 Y ≤ Y ⊓ Subgroup.centralizer (V' : Set G) := by
    intro V' hV'
    rw [hcore]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hV')
  refine ⟨le_antisymm (szN3_oTwoUpper_le_oTwoUpper (le_inf hYLY hYLa)) ?_,
    le_antisymm (szN3_oTwoUpper_le_oTwoUpper (le_inf hYCY hYCVb)) ?_⟩
  · refine szN3_oTwoUpper_le_of_decomp (inf_le_left.trans hYNYL) (pCoreOf_isPGroup 2 Y)
      (hKle (map_inclMod_le hV _)) (szN3_decomp (hV := hV) hYN hcore hYLY inf_le_left ?_)
    intro z hz
    have hzN : z ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hz.1
    have hzy : convI hV ⟨z, hzN⟩ ∈ autI hV Y := convI_mem_autI hV hz.1 hzN
    rw [hYe] at hzy
    have hzX : convI hV ⟨z, hzN⟩ ∈ X := oTwoUpper_le _ hzy
    rw [hautL]
    exact ⟨(hS.mem_L₂_iff hzX).2 fun u hu =>
      (mem_centralizer_map_inclMod_iff hV hzN (commV La)).1 hz.2 u hu, hzy⟩
  · refine szN3_oTwoUpper_le_of_decomp (inf_le_left.trans hYNYC) (pCoreOf_isPGroup 2 Y)
      (hKle (map_inclMod_le hV _)) (szN3_decomp (hV := hV) hYN hcore hYCY inf_le_left ?_)
    intro z hz
    have hzN : z ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hz.1
    have hzy : convI hV ⟨z, hzN⟩ ∈ autI hV Y := convI_mem_autI hV hz.1 hzN
    rw [hYe] at hzy
    have hzX : convI hV ⟨z, hzN⟩ ∈ X := oTwoUpper_le _ hzy
    rw [hautC]
    exact ⟨(hS.mem_L₁_iff hzX).2 fun u hu =>
      (mem_centralizer_map_inclMod_iff hV hzN (commV Lb)).1 hz.2 u hu, hzy⟩

end Key

@[expose] def Lin2YLLabel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G) →
        YL153 Yp L ≤ Subgroup.centralizer (V₁ : Set G) ∨
          YL153 Yp L ≤ Subgroup.centralizer (V₂ : Set G)

section Normalizer

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN3_S_le_normalizer_oTwoUpper (hyp : Hyp153 G T Mc M) {S Vx : Subgroup G} (hST : S ≤ T)
    (hSV : S ≤ Subgroup.normalizer (Vx : Set G)) :
    S ≤ Subgroup.normalizer
      (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (Vx : Set G)) : Set G) := by
  intro s hs
  have h1 : s ∈ Subgroup.normalizer (Y153 Mc M : Set G) :=
    le_normalizer_Y153 Mc M (hyp.T_le (hST hs))
  have h2 : s ∈ Subgroup.normalizer ((Subgroup.centralizer (Vx : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_centralizer hSV hs
  exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩)

theorem szN3_S_le_normalizer_L (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer (YL153 Yp L : Set G)) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hq := hh.hyp.qtfe
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.ctx.inH.1.1
  have hYLL : YL153 Yp L ≤ L := (oTwoUpper_le _).trans inf_le_right
  intro s hs
  by_contra hsn
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 c.ctx.inH.1.2 hLI with
    hn | ⟨-, htypes⟩
  · exact hsn ((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn (hSI hs))
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
  set L' := L.map (MulAut.conj s).toMonoidHom with hL'
  have hL'c : L' ∈ cComp I := map_conj_mem_cComp hLI (hSI hs)
  have hne' : L ≠ L' := fun h' => hsn (A38.map_conj_eq_iff.mp h'.symm)
  obtain ⟨hc1, -⟩ := lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 c.ctx.inH.1.2 hLI hL'c hne'
  have key : ∀ y ∈ YL153 Yp L, Odd (orderOf y) → y = 1 := by
    intro y hy hodd
    have hyL : y ∈ L := hYLL hy
    have hsinv : s⁻¹ ∈ Subgroup.normalizer (YL153 Yp L : Set G) :=
      (Subgroup.normalizer (YL153 Yp L : Set G)).inv_mem (hSYL hs)
    have hy' : s⁻¹ * y * s ∈ YL153 Yp L := by
      have := (Subgroup.mem_normalizer_iff.mp hsinv y).mp hy
      simpa using this
    have hyL' : y ∈ L' := by
      rw [hL', A38.mem_map_conj]
      exact hYLL hy'
    have hcomm : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := fun l hl =>
      (hc1 (Subgroup.commutator_mem_commutator hl hyL')).1
    have hyO : y ∈ pCoreOf 2 L := S153D.mem_pCoreOf_of_commutators hLI hsimple hyL hcomm
    exact S153F.eq_one_of_mem_pCoreOf_of_odd hyO hodd
  apply c.c16.YL_ne
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, ho⟩
  exact Subgroup.mem_bot.mpr (key x (mem_oTwoUpper_of_odd hx ho) ho)

end Normalizer

section Swap

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem szN3_conjSub_centralizer (g : G) (V : Subgroup G) :
    B6.conjSub g (Subgroup.centralizer (V : Set G)) =
      Subgroup.centralizer ((B6.conjSub g V : Subgroup G) : Set G) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have h1 := h (g⁻¹ * w * g) (B6.mem_conjSub.mp hw)
    have e1 : g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ = w * x := by group
    have e2 : g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ = x * w := by group
    rw [← e1, ← e2, h1]
  · intro h v hv
    have hmem : g * v * g⁻¹ ∈ B6.conjSub g V := by
      rw [B6.mem_conjSub]
      have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      rw [e]
      exact hv
    have h1 := h (g * v * g⁻¹) hmem
    have e1 : g⁻¹ * ((g * v * g⁻¹) * x) * g = v * (g⁻¹ * x * g) := by group
    have e2 : g⁻¹ * (x * (g * v * g⁻¹)) * g = (g⁻¹ * x * g) * v := by group
    rw [← e1, ← e2, h1]

theorem szN3_oTwoUpper_conjSub (g : G) (X : Subgroup G) :
    oTwoUpper (B6.conjSub g X) = B6.conjSub g (oTwoUpper X) :=
  oTwoUpper_map (MulAut.conj g).toMonoidHom X

theorem szN3_conj_V_swap (hyp : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {t₁ : G}
    (ht₁ : t₁ ∈ T) (ht₁S : t₁ ∉ Sgp153 T V₁) :
    B6.conjSub t₁ V₁ = V₂ ∧ B6.conjSub t₁ V₂ = V₁ := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := D.model
  have hMN := hyp.le_normalizer
  have ht₁N : t₁ ∈ Subgroup.normalizer (VZ T M : Set G) := hMN (hyp.T_le ht₁)
  have hxX : convI hV ⟨t₁, ht₁N⟩ ∈ autI hV M := convI_mem_autI hV (hyp.T_le ht₁) ht₁N
  have hxN : convI hV ⟨t₁, ht₁N⟩ ∉ L₁ ⊔ L₂ := by
    intro hx
    apply ht₁S
    refine ⟨ht₁, ?_⟩
    rw [hV₁]
    exact (mem_normalizer_map_inclMod_iff hV ht₁N (commV L₁)).2 (hS.sup_le_stab₁ hx)
  obtain ⟨hsw1, hsw2⟩ := hS.swap_apply_mem hxX hxN
  have h12 : ∀ v ∈ V₁, t₁ * v * t₁⁻¹ ∈ V₂ := by
    intro v hv
    rw [hV₁] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [hV₂]
    refine ⟨convI hV ⟨t₁, ht₁N⟩ u, hsw1 u hu, ?_⟩
    exact (convI_apply_val hV ⟨t₁, ht₁N⟩ u).symm ▸ rfl
  have h21 : ∀ v ∈ V₂, t₁ * v * t₁⁻¹ ∈ V₁ := by
    intro v hv
    rw [hV₂] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [hV₁]
    refine ⟨convI hV ⟨t₁, ht₁N⟩ u, hsw2 u hu, ?_⟩
    exact (convI_apply_val hV ⟨t₁, ht₁N⟩ u).symm ▸ rfl
  have hcard : ∀ V : Subgroup G, Nat.card (B6.conjSub t₁ V) = Nat.card V := fun V =>
    Subgroup.card_map_of_injective (f := (MulAut.conj t₁).toMonoidHom)
      (fun a b h => (MulAut.conj t₁).injective h)
  refine ⟨Subgroup.eq_of_le_of_card_ge (fun w hw => ?_) ?_,
    Subgroup.eq_of_le_of_card_ge (fun w hw => ?_) ?_⟩
  · have := h12 _ (B6.mem_conjSub.mp hw)
    have e : t₁ * (t₁⁻¹ * w * t₁) * t₁⁻¹ = w := by group
    rwa [e] at this
  · rw [hcard, D.card₁, D.card₂]
  · have := h21 _ (B6.mem_conjSub.mp hw)
    have e : t₁ * (t₁⁻¹ * w * t₁) * t₁⁻¹ = w := by group
    rwa [e] at this
  · rw [hcard, D.card₁, D.card₂]

theorem szN3_exists_swap (hyp : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {YL YC : Subgroup G}
    (hLC : (YL = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ∧
        YC = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G))) ∨
      (YL = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G)) ∧
        YC = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))) :
    ∃ t₁ ∈ T, t₁ ∉ Sgp153 T V₁ ∧ B6.conjSub t₁ YL = YC := by
  have hidx := D.relIndex_nS hyp
  obtain ⟨t₁, ht₁, ht₁S⟩ : ∃ t₁ ∈ T, t₁ ∉ Sgp153 T V₁ := by
    by_contra hno
    push Not at hno
    have h1 : (Sgp153 T V₁).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr fun x hx => hno x hx
    rw [h1] at hidx
    omega
  obtain ⟨hc1, hc2⟩ := szN3_conj_V_swap hyp D ht₁ ht₁S
  refine ⟨t₁, ht₁, ht₁S, ?_⟩
  have hYt : B6.conjSub t₁ (Y153 Mc M) = Y153 Mc M :=
    B6.conjSub_eq_self (le_normalizer_Y153 Mc M (hyp.T_le ht₁))
  have key : ∀ Va Vb : Subgroup G, B6.conjSub t₁ Va = Vb →
      B6.conjSub t₁ (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (Va : Set G))) =
        oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (Vb : Set G)) := by
    intro Va Vb h
    rw [← szN3_oTwoUpper_conjSub, OrderIso.map_inf, hYt, szN3_conjSub_centralizer, h]
  rcases hLC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact key V₁ V₂ hc1
  · rw [h1, h2]; exact key V₂ V₁ hc2

end Swap

section NotCentralized

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem szN3_mem_normalizer_of_conjSub {g t₁ : G} {V : Subgroup G}
    (h : g ∈ Subgroup.normalizer ((B6.conjSub t₁ V : Subgroup G) : Set G)) :
    t₁⁻¹ * g * t₁ ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro x
  have h1 := h (t₁ * x * t₁⁻¹)
  rw [B6.mem_conjSub, B6.mem_conjSub] at h1
  have e1 : t₁⁻¹ * (t₁ * x * t₁⁻¹) * t₁ = x := by group
  have e2 : t₁⁻¹ * (g * (t₁ * x * t₁⁻¹) * g⁻¹) * t₁ =
      (t₁⁻¹ * g * t₁) * x * (t₁⁻¹ * g * t₁)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem szN3_normalizer_V₂_le (hyp : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (h : Subgroup.normalizer (V₁ : Set G) ≤ M) : Subgroup.normalizer (V₂ : Set G) ≤ M := by
  have hidx := D.relIndex_nS hyp
  obtain ⟨t₁, ht₁, ht₁S⟩ : ∃ t₁ ∈ T, t₁ ∉ Sgp153 T V₁ := by
    by_contra hno
    push Not at hno
    have h1 : (Sgp153 T V₁).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr fun x hx => hno x hx
    rw [h1] at hidx
    omega
  obtain ⟨hc1, -⟩ := szN3_conj_V_swap hyp D ht₁ ht₁S
  intro g hg
  rw [← hc1] at hg
  have h2 : t₁⁻¹ * g * t₁ ∈ M := h (szN3_mem_normalizer_of_conjSub hg)
  have e : g = t₁ * (t₁⁻¹ * g * t₁) * t₁⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (hyp.T_le ht₁) h2) (M.inv_mem (hyp.T_le ht₁))

end NotCentralized

end CFSG.Quasithin
