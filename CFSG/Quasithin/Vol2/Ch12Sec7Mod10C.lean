module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10B

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem one_two_oVecL : 1 ∈ oVecL ∧ 2 ∈ oVecL ∧ 3 ∈ oVecL ∧ 1 ∈ l2c ∧ 2 ∈ l2c := by decide

theorem oVecL_pn : ∀ d ∈ oVecL, pn d ∈ oPts ∧ ptSetEq (ptOf d) (ptOf (pn d)) = true := by decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem R2_le_normalizer_L (h : Hyp1271 G T L V) :
    R2 T L V ≤ Subgroup.normalizer (L : Set G) := by
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer h.hyp.normalizes
  intro r hr
  have hr1 : r ∈ L ⊔ pCoreOf 2 (L ⊔ T) := ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) hr).1
  exact sup_le Subgroup.le_normalizer ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hLT) hr1

omit [Finite G] in
theorem card_le_filter {C : Coding ↥V} {U : Subgroup G} (hUV : U ≤ V) {l : List ℕ}
    (hl : l.Nodup) (hUl : ∀ u : ↥V, (u : G) ∈ U → C.cd u ∈ l) {B : B6}
    (hfix : ∀ u : ↥V, (u : G) ∈ U → B.app (C.cd u) = C.cd u) :
    Nat.card U ≤ (l.filter fun c => B.app c == c).length := by
  classical
  have hinj : Function.Injective (fun u : ↥U =>
      (⟨C.cd ⟨u, hUV u.2⟩, List.mem_filter.2 ⟨hUl _ u.2, by simpa using hfix _ u.2⟩⟩ :
        {c : ℕ // c ∈ l.filter fun c => B.app c == c})) := by
    intro a b hab
    have := C.cd_injective (congrArg Subtype.val hab)
    exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) this)
  have hle := Nat.card_le_card_of_injective _ hinj
  have e2 : {c : ℕ // c ∈ l.filter fun c => B.app c == c} ≃
      ↥(l.filter fun c => B.app c == c).toFinset :=
    Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup (hl.filter _)] at hle
  exact hle

omit [Finite G] in
theorem card_map_conj (U : Subgroup G) (l : G) :
    Nat.card ↥(U.map (MulAut.conj l).toMonoidHom) = Nat.card U :=
  Subgroup.card_map_of_injective (MulAut.conj l).injective

theorem exists_invol_of_corank_three
    (h1222 : Stmt12_2_2)
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {U : Subgroup G}
    (hUV : U ≤ V) (hU8 : Nat.card U = 8)
    (hne : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ≠
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) :
    ∃ m, ∃ hmN : m ∈ Subgroup.normalizer (V : Set G),
      m ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ∧ ∃ k : ℕ,
      (conjAct V ⟨m, hmN⟩) ^ k ≠ 1 ∧ ((conjAct V ⟨m, hmN⟩) ^ k) ^ 2 = 1 ∧
      (conjAct V ⟨m, hmN⟩) ^ k ∈ h.hyp.MVbar ∧
      ∀ u : ↥V, (u : G) ∈ U → (C.cB ((conjAct V ⟨m, hmN⟩) ^ k)).app (C.cd u) = C.cd u := by
  have hU0 : U ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hU8
    norm_num at hU8
  obtain ⟨m, hmN, hmU, hm1⟩ := exists_autOn_fix_of_ne h1222 h hUV hU0 hne
  exact ⟨m, hmN, hmU, exists_invol_fix h hC hUV (by omega) hmN hmU hm1⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem conjAct_pow' {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G)) (k : ℕ) :
    conjAct V ⟨m ^ k, Subgroup.pow_mem _ hm k⟩ = (conjAct V ⟨m, hm⟩) ^ k := by
  rw [← map_pow]
  rfl

theorem exists_conj_le_V2
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    {U : Subgroup G} (hUV : U ≤ V) {y : MulAut ↥V} (hyM : y ∈ autOn L V)
    (hy1 : y ≠ 1) (hy2 : y ^ 2 = 1)
    (hfix : ∀ u : ↥V, (u : G) ∈ U → (C.cB y).app (C.cd u) = C.cd u) :
    ∃ l ∈ L, U.map (MulAut.conj l).toMonoidHom ≤ V2 T L V := by
  have hB := (hC.1.1 y).1 hyM
  have hBsq : (C.cB y).comp (C.cB y) = B6.id := by rw [← C.cB_mul, ← pow_two, hy2, C.cB_one]
  obtain ⟨g, hg, hgax⟩ := cert4_axis _ hB hBsq (fun e => hy1 (C.cB_eq_one.1 e))
  obtain ⟨a, rfl⟩ := hC.1.2 g hg
  obtain ⟨l, hl, hlL, rfl⟩ := mem_autOn'.1 ((hC.1.1 _).2 hg)
  refine ⟨l, hlL, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have huV := hUV hu
  rw [V2_eq h hC]
  refine ⟨(Subgroup.mem_normalizer_iff.1 hl u).1 huV, ?_⟩
  have e := cd_conj C hl ⟨u, huV⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [e]
  exact (hgax _ (List.mem_range.2 (C.cd_lt _))).1 (hfix _ hu)

theorem exists_oVecL_of_le_V2
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    {W : Subgroup G} (hWV2 : W ≤ V2 T L V) (hW8 : Nat.card W = 8) :
    ∃ w : ↥V, (w : G) ∈ W ∧ C.cd w ∈ oVecL := by
  obtain ⟨h1o, h2o, h3o, h1l, h2l⟩ := one_two_oVecL
  have hV2 := V2_eq h hC
  have hcard2 : Nat.card ↥(V2 T L V) = 16 := (lemma12_7_2_four h1222 h).1.2
  have hidx : (W.subgroupOf (V2 T L V)).index = 2 := by
    have e := Subgroup.relIndex_mul_card W (V2 T L V)
    rw [inf_eq_left.2 hWV2, hW8, hcard2] at e
    have : W.relIndex (V2 T L V) = 2 := by omega
    exact this
  have hmem : ∀ c ∈ l2c, (C.dc c : G) ∈ V2 T L V := fun c hc => by
    rw [hV2]
    exact (C.mem_subG (C.dc c)).2 (by rw [C.cd_dc c (l2c_lt c hc)]; exact hc)
  by_cases hw1 : (C.dc 1 : G) ∈ W
  · exact ⟨C.dc 1, hw1, by rw [C.cd_dc 1 (by norm_num)]; exact h1o⟩
  by_cases hw2 : (C.dc 2 : G) ∈ W
  · exact ⟨C.dc 2, hw2, by rw [C.cd_dc 2 (by norm_num)]; exact h2o⟩
  have h1' : (⟨_, hmem 1 h1l⟩ : ↥(V2 T L V)) ∉ W.subgroupOf (V2 T L V) := hw1
  have h2' : (⟨_, hmem 2 h2l⟩ : ↥(V2 T L V)) ∉ W.subgroupOf (V2 T L V) := hw2
  have hmul := (Subgroup.mul_mem_iff_of_index_two hidx).2 ⟨fun h' => absurd h' h1',
    fun h' => absurd h' h2'⟩
  refine ⟨C.dc 1 * C.dc 2, hmul, ?_⟩
  rw [C.cd_mul, C.cd_dc 1 (by norm_num), C.cd_dc 2 (by norm_num)]
  exact h3o

omit [Finite G] in
theorem eq_fixV_map {C : Coding ↥V} {U : Subgroup G} (hUV : U ≤ V) {y : MulAut ↥V}
    (hfix : ∀ u : ↥V, (u : G) ∈ U → (C.cB y).app (C.cd u) = C.cd u)
    (hcard : fixCount (C.cB y) ≤ Nat.card U) :
    U = (fixV (Subgroup.zpowers y)).map V.subtype := by
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, hUV hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixV_zpowers]
    exact (C.apply_eq_self_iff y _).2 (hfix _ hg)
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_fixV_zpowers] at hv
    have hc := (C.apply_eq_self_iff y v).1 hv
    have := mem_of_fixCount_le hUV hfix hcard (C.cd_lt v) hc
    rwa [C.dc_cd] at this

omit [Finite G] in
theorem centralizer_le_of_conj {U : Subgroup G} {l : G} (hlL : l ∈ L)
    (h : Subgroup.centralizer (U.map (MulAut.conj l).toMonoidHom : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  have hlx : l * x * l⁻¹ ∈ Subgroup.centralizer (U.map (MulAut.conj l).toMonoidHom : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.1 hx u hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc l * u * l⁻¹ * (l * x * l⁻¹) = l * (u * x) * l⁻¹ := by group
      _ = l * (x * u) * l⁻¹ := by rw [hc]
      _ = l * x * l⁻¹ * (l * u * l⁻¹) := by group
  have hlM : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hlM) (h hlx)) hlM
  simpa [mul_assoc] using this

theorem lemma12_7_10_four
    (h1222 : Stmt12_2_2) {t : G} (hS : Setting1273 G T L V t)
    (U : Subgroup G) (hUV : U ≤ V) (hU3 : E3.mQuot V U = 3) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) =
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) ∨
      (∃ l ∈ L, U.map (MulAut.conj l).toMonoidHom ≤ V2 T L V ∧
        E3.mQuot (V2 T L V) (U.map (MulAut.conj l).toMonoidHom) = 1 ∧
        Subgroup.normalizer (L : Set G) ⊓
            Subgroup.centralizer (U.map (MulAut.conj l).toMonoidHom : Set G) =
          (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V) ∨
      (∃ y ∈ hS.hyp.hyp.MVbar, y ∉ autOn L V ∧ orderOf y = 2 ∧
        U = (fixV (Subgroup.zpowers y)).map V.subtype ∧
        ∃ i ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G),
          (∀ v : ↥V, ((y v : ↥V) : G) = i * v * i⁻¹) ∧
          Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) =
            Subgroup.zpowers i ⊔
              (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G))) := by
  have h := hS.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hV2 := isPGroup_V' h
  have hV64 := card_V h1222 h
  have hU8 : Nat.card U = 8 := by
    have e := E3.card_eq_two_pow_mul hV2 hUV
    rw [hV64, hU3] at e
    omega
  have hU0 : U ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hU8
    norm_num at hU8
  have hV2V : V2 T L V ≤ V := (lemma12_7_2_four h1222 h).1.1.1
  by_cases heq : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)
  · exact Or.inl heq
  right
  obtain ⟨m, hmN, hmU, k, hk1, hk2, hkM, hkfix⟩ :=
    exists_invol_of_corank_three h1222 h hC.1 hUV hU8 heq
  set y := (conjAct V ⟨m, hmN⟩) ^ k with hyd
  have hB := (MVbar_code h hC.1 hkM).1
  have hBsq : (C.cB y).comp (C.cB y) = B6.id := by
    rw [← C.cB_mul, ← pow_two, hk2, C.cB_one]
  have hB1 : C.cB y ≠ B6.id := fun e => hk1 (C.cB_eq_one.1 e)
  by_cases hyL : y ∈ autOn L V
  ·
    left
    obtain ⟨l, hlL, hle⟩ := exists_conj_le_V2 h hC hUV hyL hk1 hk2 hkfix
    have hUl8 : Nat.card ↥(U.map (MulAut.conj l).toMonoidHom) = 8 :=
      (card_map_conj U l).trans hU8
    have hcard2 : Nat.card ↥(V2 T L V) = 16 := (lemma12_7_2_four h1222 h).1.2
    have hUlV : U.map (MulAut.conj l).toMonoidHom ≤ V := hle.trans hV2V
    have hUl0 : U.map (MulAut.conj l).toMonoidHom ≠ ⊥ := fun hb => by
      rw [hb, Subgroup.card_bot] at hUl8
      norm_num at hUl8
    refine ⟨l, hlL, hle, ?_, le_antisymm ?_ ?_⟩
    · unfold E3.mQuot
      have e := Subgroup.relIndex_mul_card (U.map (MulAut.conj l).toMonoidHom) (V2 T L V)
      rw [inf_eq_left.2 hle, hUl8, hcard2] at e
      have : (U.map (MulAut.conj l).toMonoidHom).relIndex (V2 T L V) = 2 := by omega
      rw [this, padicValNat.self (by norm_num : 1 < 2)]
    · intro m' hm'
      have hm'N := mem_normalizer_of_mem_inf_centralizer h1222 h hUlV hUl0 hm'
      have hfix' : ∀ u : ↥V, (u : G) ∈ U.map (MulAut.conj l).toMonoidHom →
          (C.cB (conjAct V ⟨m', hm'N⟩)).app (C.cd u) = C.cd u := by
        intro u hu
        have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hm').2 _ hu
        exact (commute_iff_code C hm'N u).1 this.symm
      have hl2 : ∀ u : ↥V, (u : G) ∈ U.map (MulAut.conj l).toMonoidHom → C.cd u ∈ l2c := by
        intro u hu
        have := hle hu
        rw [V2_eq h hC] at this
        exact (C.mem_subG u).1 this
      have h8 := card_le_filter hUlV l2c_nodup hl2 hfix'
      rw [hUl8] at h8
      have hm'M : conjAct V ⟨m', hm'N⟩ ∈ h.hyp.MVbar :=
        conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hm').1, hm'N⟩) hm'N
      have hBr := cert4_r2_of_fix8 _ (MVbar_code h hC.1 hm'M).1 h8
      obtain ⟨a', ha'⟩ := hC.1.2 _ (r2_sub _ hBr).1
      obtain ⟨r, hr, hrR, hra⟩ :=
        mem_autOn'.1 ((mem_autOn_R2_iff h1222 h hC a').2 (by rw [ha']; exact hBr))
      have hcv : m' * r⁻¹ ∈
          Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
        have hN : m' * r⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
          Subgroup.mul_mem _ hm'N (Subgroup.inv_mem _ hr)
        refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mem_inf.1 hm').1
          (Subgroup.inv_mem _ (R2_le_normalizer_L h hrR)), ?_⟩
        rw [← conjAct_eq_one' hN]
        have e1 : conjAct V ⟨m' * r⁻¹, hN⟩ =
            conjAct V ⟨m', hm'N⟩ * (conjAct V ⟨r, hr⟩)⁻¹ := by
          rw [← map_inv, ← map_mul]
          rfl
        have e2 : conjAct V ⟨r, hr⟩ = conjAct V ⟨m', hm'N⟩ :=
          C.cB_injective (by rw [hra, ha'])
        rw [e1, e2, mul_inv_cancel]
      have := Subgroup.mul_mem_sup hcv hrR
      simpa using this
    · apply sup_le
      · exact inf_le_inf_left _ (Subgroup.centralizer_le hUlV)
      · intro r hr
        have hrN : r ∈ Subgroup.normalizer (V : Set G) :=
          (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (pof_le_normalizer h1222 h _) hr
        have hrc := (mem_autOn_R2_iff h1222 h hC _).1 (conjAct_mem_autOn hr hrN)
        refine Subgroup.mem_inf.2 ⟨R2_le_normalizer_L h hr, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwV := hUlV hw
        have hwl : C.cd ⟨w, hwV⟩ ∈ l2c := by
          have := hle hw
          rw [V2_eq h hC] at this
          exact (C.mem_subG ⟨w, hwV⟩).1 this
        exact ((commute_iff_code C hrN ⟨w, hwV⟩).2
          ((r2_fixAll _ (C.cd_lt _)).2 hwl _ hrc)).symm
  ·
    right
    have h8' := cert4_semi_fix8 _ hB (fun hg => hyL ((hC.1.1 y).2 hg)) hBsq
    have hmM := (Subgroup.mem_inf.1 hmU).1
    have hiMN : m ^ k ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
      Subgroup.pow_mem _ (Subgroup.mem_inf.2 ⟨hmM, hmN⟩) k
    have hyi : y = conjAct V ⟨m ^ k, Subgroup.pow_mem _ hmN k⟩ := (conjAct_pow' hmN k).symm
    refine ⟨y, hkM, hyL, orderOf_eq_prime hk2 hk1, eq_fixV_map hUV hkfix (by rw [h8', hU8]),
      m ^ k, hiMN, fun v => by rw [hyi, conjAct_val], le_antisymm ?_ ?_⟩
    · intro m' hm'
      have hm'N := mem_normalizer_of_mem_inf_centralizer h1222 h hUV hU0 hm'
      have hm'M : conjAct V ⟨m', hm'N⟩ ∈ h.hyp.MVbar :=
        conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hm').1, hm'N⟩) hm'N
      have hfix2 : ∀ c ∈ List.range 64, (C.cB y).app c = c →
          (C.cB (conjAct V ⟨m', hm'N⟩)).app c = c := by
        intro c hc hcy
        have hc64 := List.mem_range.1 hc
        have hcU := mem_of_fixCount_le hUV hkfix (by rw [h8', hU8]) hc64 hcy
        have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hm').2 _ hcU
        have := (commute_iff_code C hm'N (C.dc c)).1 this.symm
        rwa [C.cd_dc c hc64] at this
      have hyn : C.cB y ∉ gm6 := fun hg => hyL ((hC.1.1 y).2 hg)
      rcases cert4_cent_semi _ hB hyn hBsq _ (MVbar_code h hC.1 hm'M).1 hfix2 with e | e
      · refine Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hm').1, ?_⟩)
        exact (conjAct_eq_one' hm'N).1 (C.cB_eq_one.1 e)
      · have hN : (m ^ k)⁻¹ * m' ∈ Subgroup.normalizer (V : Set G) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hmN k)) hm'N
        have hc : (m ^ k)⁻¹ * m' ∈
            Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
          refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _
            (Subgroup.pow_mem _ hmM k)) (Subgroup.mem_inf.1 hm').1, ?_⟩
          rw [← conjAct_eq_one' hN]
          have e1 : conjAct V ⟨(m ^ k)⁻¹ * m', hN⟩ =
              (conjAct V ⟨m ^ k, Subgroup.pow_mem _ hmN k⟩)⁻¹ * conjAct V ⟨m', hm'N⟩ := by
            rw [← map_inv, ← map_mul]
            rfl
          have e2 : conjAct V ⟨m', hm'N⟩ = conjAct V ⟨m ^ k, Subgroup.pow_mem _ hmN k⟩ := by
            rw [← hyi]
            exact C.cB_injective e
          rw [e1, e2, inv_mul_cancel]
        have := Subgroup.mul_mem_sup (Subgroup.mem_zpowers (m ^ k)) hc
        simpa using this
    · apply sup_le
      · rw [Subgroup.zpowers_le]
        exact Subgroup.pow_mem _ hmU k
      · exact inf_le_inf_left _ (Subgroup.centralizer_le hUV)

theorem lemma12_7_10_five
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h3228 : Stmt3_2_2_eight) (hE612 : ASInputs.AS_E_6_12) {t : G}
    (hS : Setting1273 G T L V t) (U : Subgroup G) (hUV : U ≤ V) (hU3 : E3.mQuot V U = 3)
    (hno : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ y ∈ hS.hyp.hyp.MVbar, y ∉ autOn L V ∧ orderOf y = 2 ∧
      (∀ l ∈ L, ¬ Acts y ((Vt L t).map (MulAut.conj l).toMonoidHom)) ∧
      U = (fixV (Subgroup.zpowers y)).map V.subtype := by
  have h := hS.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hct := cd_t_mem_oVecL h1222 h hC hS.t_mem hS.orbit_t
  have hV2 := isPGroup_V' h
  have hV64 := card_V h1222 h
  have hU8 : Nat.card U = 8 := by
    have e := E3.card_eq_two_pow_mul hV2 hUV
    rw [hV64, hU3] at e
    omega
  have hU0 : U ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hU8
    norm_num at hU8
  have heq : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ≠
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
    intro heq
    obtain ⟨⟨U₁, -, hU₁V, hm₁, hno₁⟩, -⟩ :=
      hE612 G T (Subgroup.normalizer (L : Set G)) V U (hypE61_1271 h331 h1222 h3228 h) hU0 hUV
        heq hno
    exact hno₁ (centralizer_le_M_of_mQuot_le_two h331 h1222 h3228 hE612 hS hU₁V (by omega))
  obtain ⟨m, hmN, hmU, k, hk1, hk2, hkM, hkfix⟩ :=
    exists_invol_of_corank_three h1222 h hC.1 hUV hU8 heq
  set y := (conjAct V ⟨m, hmN⟩) ^ k with hyd
  have hB := (MVbar_code h hC.1 hkM).1
  have hBsq : (C.cB y).comp (C.cB y) = B6.id := by
    rw [← C.cB_mul, ← pow_two, hk2, C.cB_one]
  have hyL : y ∉ autOn L V := by
    intro hyL
    obtain ⟨l, hlL, hle⟩ := exists_conj_le_V2 h hC hUV hyL hk1 hk2 hkfix
    obtain ⟨w, hwU, hw⟩ := exists_oVecL_of_le_V2 h1222 h hC hle ((card_map_conj U l).trans hU8)
    exact hno (centralizer_le_of_conj hlL (centralizer_le_of_mem_oVecL hS hC.1 hct hwU hw))
  have hyn : C.cB y ∉ gm6 := fun hg => hyL ((hC.1.1 y).2 hg)
  have h8' := cert4_semi_fix8 _ hB hyn hBsq
  refine ⟨y, hkM, hyL, orderOf_eq_prime hk2 hk1, fun l hlL hact => ?_,
    eq_fixV_map hUV hkfix (by rw [h8', hU8])⟩
  have hlN := L_le_normalizer h hlL
  rw [Vt_eq_ptOf h1222 h hC.1 hS.t_mem, map_subG_ptOf hC.1 hlN hlL (C.cd_lt _)] at hact
  set d := (C.cB (conjAct V ⟨l, hlN⟩)).app (C.cd ⟨t, hS.t_mem⟩) with hdd
  have hLM : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
  have hd : d ∈ oVecL := (MVbar_code h hC.1 (hLM (conjAct_mem_autOn hlL hlN))).2.1 _ hct
  have hd64 := oVecL_lt d hd
  obtain ⟨hpd, hpeq⟩ := oVecL_pn d hd
  have hpres : presv (ptOf (pn d)) (C.cB y) = true := by
    rw [presv_iff]
    intro c hc
    have hc' := (mem_iff_of_ptSetEq hpeq c).2 hc
    have hc64 := ptOf_lt_all d hd64 c hc'
    have hv : ((C.dc c : ↥V) : G) ∈ C.subG (ptOf d) (ptOf_zero d) (ptOf_xor_all d hd64) :=
      (C.mem_subG _).2 (by rw [C.cd_dc c hc64]; exact hc')
    have himg := (C.mem_subG _).1 (hact _ hv)
    rw [C.cd_apply, C.cd_dc c hc64] at himg
    exact (mem_iff_of_ptSetEq hpeq _).1 himg
  obtain ⟨c, hc, hcy⟩ := cert4_semi_pt _ hB hyn hBsq _ hpd hpres
  have hcU := mem_of_fixCount_le hUV hkfix (by rw [h8', hU8]) (oVecL_lt c hc) hcy
  exact hno (centralizer_le_of_mem_oVecL hS hC.1 hct hcU
    (by rw [C.cd_dc c (oVecL_lt c hc)]; exact hc))

end CFSG.Quasithin.H13.S127.Mod

end
