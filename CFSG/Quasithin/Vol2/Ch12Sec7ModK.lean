module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModJ

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem T_le_normalizer_V1 (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    T ≤ Subgroup.normalizer (V1 T L V : Set G) := by
  have hTV := T_le_normalizer h1222 h
  apply le_normalizer_of_maps
  intro t ht w hw
  obtain ⟨hwV, hwC⟩ := Subgroup.mem_inf.1 hw
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hTV ht) w).1 hwV, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hwC ⊢
  intro x hx
  have hx' : t⁻¹ * x * t ∈ T ⊓ L := by
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) (Subgroup.mem_inf.1 hx).1) ht,
      ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (h.hyp.normalizes (T.inv_mem ht)) x).1
      (Subgroup.mem_inf.1 hx).2
    simpa using this
  have hc := hwC _ hx'
  calc x * (t * w * t⁻¹) = t * ((t⁻¹ * x * t) * w) * t⁻¹ := by group
    _ = t * (w * (t⁻¹ * x * t)) * t⁻¹ := by rw [hc]
    _ = t * w * t⁻¹ * x := by group

theorem T_le_normalizer_V2 (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    T ≤ Subgroup.normalizer (V2 T L V : Set G) := by
  have hTV := T_le_normalizer h1222 h
  apply le_normalizer_of_maps
  intro t ht w hw
  have hle : V2 T L V ≤ (V2 T L V).comap (MulAut.conj t).toMonoidHom := by
    rw [V2, Subgroup.commutator_le]
    intro v hv x hx
    show t * ⁅v, x⁆ * t⁻¹ ∈ ⁅V, T ⊓ L⁆
    have e : t * ⁅v, x⁆ * t⁻¹ = ⁅t * v * t⁻¹, t * x * t⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hTV ht) v).1 hv)
      (Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem ht (Subgroup.mem_inf.1 hx).1) (T.inv_mem ht), ?_⟩)
    exact (Subgroup.mem_normalizer_iff.1 (h.hyp.normalizes ht) x).1 (Subgroup.mem_inf.1 hx).2
  exact hle hw

theorem sup_inf_normalizer (h : Hyp1271 G T L V) {W : Subgroup G}
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) :
    (L ⊔ T) ⊓ Subgroup.normalizer (W : Set G) = Pof T L W ⊔ T := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxLT, hxW⟩ := Subgroup.mem_inf.1 hx
    have hx' : x ∈ ((L ⊔ T : Subgroup G) : Set G) := hxLT
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T h.hyp.normalizes] at hx'
    obtain ⟨l, hl, t, ht, rfl⟩ := hx'
    have hlW : l ∈ Subgroup.normalizer (W : Set G) := by
      have := Subgroup.mul_mem _ hxW (Subgroup.inv_mem _ (hTW ht))
      simpa using this
    exact Subgroup.mul_mem _ (le_sup_left (a := Pof T L W)
      (Subgroup.mem_inf.2 ⟨le_sup_left (a := L) hl, hlW⟩)) (le_sup_right (b := T) ht)
  · refine sup_le (inf_le_inf_right _ (sup_le le_sup_left
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _))) (le_inf le_sup_right hTW)

theorem pCoreOf_L_le_T (h : Hyp1271 G T L V) : pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_of_isPGroup_of_le_normalizer h.hyp.sylow
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (h.hyp.normalizes.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))

theorem Q_le_T (h : Hyp1271 G T L V) : pCoreOf 2 (L ⊔ T) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_of_isPGroup_of_le_normalizer h.hyp.sylow
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem LQ_inf_centralizer_le (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    (L ⊔ pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  intro x hx
  obtain ⟨hxLQ, hxC⟩ := Subgroup.mem_inf.1 hx
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hx' : x ∈ ((L ⊔ pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) := hxLQ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLQ] at hx'
  obtain ⟨l, hl, q, hq, rfl⟩ := hx'
  have hqC := Q_le_centralizer h1222 h hq
  have hlC : l ∈ Subgroup.centralizer (V : Set G) := by
    have := Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ hqC)
    simpa using this
  have hlO : l ∈ pCoreOf 2 L := by
    rw [← inf_centralizer_eq_of_1222 h1222 h]
    exact Subgroup.mem_inf.2 ⟨hl, hlC⟩
  exact T.mul_mem (pCoreOf_L_le_T h hlO) (Q_le_T h hq)

theorem pof_inf_centralizer_isPGroup (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V)
    (W : Subgroup G) :
    IsPGroup 2 (Pof T L W ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
  h.hyp.sylow.1.to_le ((inf_le_inf_right _ inf_le_left).trans
    (LQ_inf_centralizer_le h1222 h))

theorem pof_le_normalizer (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) (W : Subgroup G) :
    Pof T L W ≤ Subgroup.normalizer (V : Set G) :=
  inf_le_left.trans (LQ_le_normalizer h1222 h)

variable [IsMulCommutative ↥V]

theorem mem_autOn_Pof (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) {l : List ℕ} {h0 : 0 ∈ l} {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l}
    (hl : ∀ c ∈ l, c < 64) (a : MulAut ↥V) :
    a ∈ autOn (Pof T L (C.subG l h0 hx)) V ↔ C.cB a ∈ gm6 ∧ presv l (C.cB a) = true := by
  rw [presv_iff]
  constructor
  · intro ha
    obtain ⟨x, hxN, hxP, rfl⟩ := mem_autOn'.1 ha
    obtain ⟨hxLQ, hxW⟩ := Subgroup.mem_inf.1 hxP
    refine ⟨(hC.1 _).1 (by rw [← autOn_LQ h1222 h]; exact conjAct_mem_autOn hxLQ hxN),
      fun c hc => ?_⟩
    have hw := (C.mem_subG (h0 := h0) (hx := hx) (C.dc c)).2 (by rw [C.cd_dc c (hl c hc)]; exact hc)
    have hw' := (Subgroup.mem_normalizer_iff.1 hxW _).1 hw
    have hv := (C.mem_subG (h0 := h0) (hx := hx)
      ⟨_, (Subgroup.mem_normalizer_iff.1 hxN _).1 (C.dc c).2⟩).1 hw'
    rw [cd_conj C hxN (C.dc c), C.cd_dc c (hl c hc)] at hv
    exact hv
  · rintro ⟨hgm, hpres⟩
    obtain ⟨y, hyN, hyL, rfl⟩ := mem_autOn'.1 ((hC.1 _).2 hgm)
    refine conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨le_sup_left (a := L) hyL, ?_⟩) hyN
    apply normalizer_of_maps
    intro w hw
    obtain ⟨hwV, hwl⟩ := hw
    have hm := (Subgroup.mem_normalizer_iff.1 hyN w).1 hwV
    have e : C.cd ⟨y * w * y⁻¹, hm⟩ = (C.cB (conjAct V ⟨y, hyN⟩)).app (C.cd ⟨w, hwV⟩) :=
      cd_conj C hyN ⟨w, hwV⟩
    exact ⟨hm, by rw [e]; exact hpres _ hwl⟩

theorem mem_autOn_R (h1222 : Stmt12_2_2)
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {l : List ℕ}
    {h0 : 0 ∈ l} {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l} (hl : ∀ c ∈ l, c < 64) {rl : List B6}
    (h1 : B6.id ∈ rl) (hcl : ∀ x ∈ rl, ∀ y ∈ rl, x.comp y ∈ rl)
    (hsub : ∀ r ∈ rl, r ∈ gm6 ∧ presv l r = true) (hsq : ∀ r ∈ rl, r.comp r = B6.id)
    (hnorm : ∀ g ∈ gm6, presv l g = true → ∀ r ∈ rl, (g.comp r).comp (inv6 g) ∈ rl)
    (hmax : ∀ u ∈ gm6, presv l u = true → two6 u = true → u ∉ rl →
      ∃ g ∈ gm6, presv l g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false)
    (a : MulAut ↥V) :
    a ∈ autOn (pCoreOf 2 (Pof T L (C.subG l h0 hx))) V ↔ C.cB a ∈ rl := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Pof T L (C.subG l h0 hx) with hP
  rw [autOn_pCoreOf (pof_le_normalizer h1222 h _) (pof_inf_centralizer_isPGroup h1222 h _)]
  set Pb := autOn P V with hPb
  have hmemP := mem_autOn_Pof h1222 h hC hl (h0 := h0) (hx := hx)
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyP : C.cB y ∈ gm6 ∧ presv l (C.cB y) = true := (hmemP y).1 y.2
    by_contra hnot
    have htwo : two6 (C.cB y) = true := by
      apply pow_four_of_isPGroup C (H := (CFSG.Open.pCore 2 ↥Pb).map Pb.subtype)
        ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map _) ⟨y, hy, rfl⟩ hyP.1
    obtain ⟨g, hg, hgl, hg2⟩ := hmax _ hyP.1 hyP.2 htwo hnot
    obtain ⟨b, rfl⟩ := hC.2 g hg
    have hbP : b ∈ Pb := (hmemP b).2 ⟨hg, hgl⟩
    have hnormal := (CFSG.LieType.BorelTits.pCore_normal 2 (G := ↥Pb)).conj_mem y hy ⟨b, hbP⟩
    have hprod := (CFSG.Open.pCore 2 ↥Pb).mul_mem hy hnormal
    set z : ↥Pb := y * (⟨b, hbP⟩ * y * ⟨b, hbP⟩⁻¹) with hz
    have hzc : (z : MulAut ↥V) ∈ (CFSG.Open.pCore 2 ↥Pb).map Pb.subtype := ⟨z, hprod, rfl⟩
    have h2 := pow_four_of_isPGroup C ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map _) hzc
      ((hmemP _).1 z.2).1
    have e : C.cB (z : MulAut ↥V) =
        (C.cB y).comp (((C.cB b).comp (C.cB y)).comp (inv6 (C.cB b))) := by
      show C.cB ((y : MulAut ↥V) * (b * y * b⁻¹)) = _
      rw [C.cB_mul, C.cB_mul, C.cB_mul, cB_inv_eq C hg]
    rw [e, hg2] at h2
    exact Bool.false_ne_true h2
  · intro ha
    set R := C.subOf rl h1 hcl with hR
    have hRP : R ≤ Pb := fun r hr => (hmemP r).2 (hsub _ hr)
    have hRn : (R.subgroupOf Pb).Normal := by
      refine ⟨fun r hr b => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      have hb := (hmemP b).1 b.2
      show C.cB ((b : MulAut ↥V) * r * (b : MulAut ↥V)⁻¹) ∈ rl
      rw [C.cB_mul, C.cB_mul, cB_inv_eq C hb.1]
      exact hnorm _ hb.1 hb.2 _ hr
    have hRp : IsPGroup 2 (R.subgroupOf Pb) := by
      intro r
      refine ⟨1, ?_⟩
      have hr : C.cB ((r : ↥Pb) : MulAut ↥V) ∈ rl := Subgroup.mem_subgroupOf.1 r.2
      have h1' : ((r : ↥Pb) : MulAut ↥V) ^ 2 = 1 := by
        apply C.cB_injective
        rw [pow_two, C.cB_mul, C.cB_one]
        exact hsq _ hr
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1'
    have hle := CFSG.LieType.BorelTits.le_pCore 2 hRn hRp
    have haP : a ∈ Pb := hRP ha
    exact ⟨⟨a, haP⟩, hle (Subgroup.mem_subgroupOf.2 ha), rfl⟩

end CFSG.Quasithin.H13.S127.Mod

end
