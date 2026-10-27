module

public import CFSG.Quasithin.MS93.S4A42Cob

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix commutatorElement

section Gw

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def gwSub (α : Vtx X) (w : X.Universal) : Subgroup ↥(stab X α) where
  carrier := {a | ⁅(a : X.Universal), w⁆ ∈ ZM X α}
  mul_mem' := by
    intro a b ha hb
    have hrw : ⁅((a * b : ↥(stab X α)) : X.Universal), w⁆ =
        (a : X.Universal) * ⁅(b : X.Universal), w⁆ * (a : X.Universal)⁻¹ *
          ⁅(a : X.Universal), w⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    show _ ∈ ZM X α
    rw [hrw]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm X α a.2)
      _).mp hb) ha
  one_mem' := by
    show ⁅((1 : ↥(stab X α)) : X.Universal), w⁆ ∈ ZM X α
    rw [Subgroup.coe_one, commutatorElement_one_left]
    exact Subgroup.one_mem _
  inv_mem' := by
    intro a ha
    have hrw : ⁅((a⁻¹ : ↥(stab X α)) : X.Universal), w⁆ =
        (a : X.Universal)⁻¹ * (⁅(a : X.Universal), w⁆)⁻¹ * (a : X.Universal)⁻¹⁻¹ := by
      simp only [Subgroup.coe_inv, commutatorElement_def]
      group
    show _ ∈ ZM X α
    rw [hrw]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm X α (inv_mem a.2)) _).mp
      (Subgroup.inv_mem _ ha)

theorem mem_gwSub {α : Vtx X} {w : X.Universal} {a : ↥(stab X α)} :
    a ∈ gwSub X α w ↔ ⁅(a : X.Universal), w⁆ ∈ ZM X α :=
  Iff.rfl

end Gw

section Zvec

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] noncomputable def zvec {hTM : T ≤ M} {α : Vtx (puAmalgam hTM)} {F : Type} [Field F]
    {ψ : ↥(stab (puAmalgam hTM) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc hTM L α) ⊥ ψ false 1)
    (x : (puAmalgam hTM).Universal) : Fin 3 → F :=
  natVecG hψ (uProj (Uloc hTM L α) (Zloc hTM L α) x)

variable (h : PUHyp M T L) (hfull : IsSL3Full M T L)
include h hfull

theorem uProj_zm {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ ZM (puAmalgam h.le) α) :
    uProj (Uloc h.le L α) (Zloc h.le L α) x ∈ Uloc h.le L α ∧
      (uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x ∈ Zloc h.le L α := by
  refine uProj_spec ?_
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Uloc h.le L α) (Zloc h.le L α)
    ((puTrans_le_stab h.le _ α).trans (stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) α))
  have hx' : x ∈ ((Uloc h.le L α ⊔ Zloc h.le L α : Subgroup _) : Set _) :=
    zm_eq_uloc_sup_zloc h hfull hα ▸ hx
  rw [hset] at hx'
  obtain ⟨u, hu, z, hz, rfl⟩ := hx'
  exact ⟨u, hu, by simpa using hz⟩

variable {F : Type} [Field F] {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
  {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
  (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
include hα

theorem zvec_mul {x y : (puAmalgam h.le).Universal} (hx : x ∈ ZM (puAmalgam h.le) α)
    (hy : y ∈ ZM (puAmalgam h.le) α) : zvec hψ (x * y) = zvec hψ x + zvec hψ y := by
  obtain ⟨hux, hzx⟩ := uProj_zm h hfull hα hx
  obtain ⟨huy, hzy⟩ := uProj_zm h hfull hα hy
  have hc := Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hα hzx)
    (uProj (Uloc h.le L α) (Zloc h.le L α) y) (puTrans_le_stab h.le _ α huy)
  have hmem : (uProj (Uloc h.le L α) (Zloc h.le L α) x *
      uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ * (x * y) ∈ Zloc h.le L α := by
    have : (uProj (Uloc h.le L α) (Zloc h.le L α) x *
        uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ * (x * y) =
        ((uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ *
          (uProj (Uloc h.le L α) (Zloc h.le L α) y *
            ((uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x))) *
          ((uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ * y) := by
      rw [hc]
      group
    rw [this, inv_mul_cancel_left]
    exact Subgroup.mul_mem _ hzx hzy
  unfold zvec
  rw [uProj_eq (uloc_inf_zloc h hfull α) (Subgroup.mul_mem _ hux huy) hmem,
    natVecG_mul hψ hux huy]

theorem zvec_conj (g : ↥(stab (puAmalgam h.le) α)) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ ZM (puAmalgam h.le) α) :
    zvec hψ ((g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹) =
      ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ zvec hψ x := by
  obtain ⟨hux, hzx⟩ := uProj_zm h hfull hα hx
  have hgu := (Subgroup.mem_normalizer_iff.mp
    (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α g.2) _).mp hux
  have hmem : ((g : (puAmalgam h.le).Universal) * uProj (Uloc h.le L α) (Zloc h.le L α) x *
      (g : (puAmalgam h.le).Universal)⁻¹)⁻¹ *
        ((g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹) ∈
          Zloc h.le L α := by
    have : ((g : (puAmalgam h.le).Universal) * uProj (Uloc h.le L α) (Zloc h.le L α) x *
        (g : (puAmalgam h.le).Universal)⁻¹)⁻¹ *
          ((g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹) =
        (g : (puAmalgam h.le).Universal) *
          ((uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x) *
            (g : (puAmalgam h.le).Universal)⁻¹ := by
      group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) α g.2) _).mp hzx
  unfold zvec
  rw [uProj_eq (uloc_inf_zloc h hfull α) hgu hmem, natVecG_conj hψ g hux]

omit hα in
theorem zvec_one : zvec hψ (1 : (puAmalgam h.le).Universal) = 0 := by
  unfold zvec
  rw [uProj_eq (uloc_inf_zloc h hfull α) (Subgroup.one_mem _) (by simp), natVecG_one]

theorem zvec_comm_mul {w : (puAmalgam h.le).Universal} (a b : ↥(stab (puAmalgam h.le) α))
    (ha : a ∈ gwSub _ α w) (hb : b ∈ gwSub _ α w) :
    zvec hψ ⁅((a * b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal), w⁆ =
      zvec hψ ⁅(a : (puAmalgam h.le).Universal), w⁆ +
        ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          zvec hψ ⁅(b : (puAmalgam h.le).Universal), w⁆ := by
  have hrw : ⁅((a * b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal), w⁆ =
      (a : (puAmalgam h.le).Universal) * ⁅(b : (puAmalgam h.le).Universal), w⁆ *
        (a : (puAmalgam h.le).Universal)⁻¹ * ⁅(a : (puAmalgam h.le).Universal), w⁆ := by
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  have hconj := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α a.2) _).mp
    (mem_gwSub _ |>.mp hb)
  rw [hrw, zvec_mul h hfull hα hψ hconj ((mem_gwSub _).mp ha),
    zvec_conj h hfull hα hψ a ((mem_gwSub _).mp hb), add_comm]

end Zvec

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

omit hfull in
theorem exists_odd_pow_mem_qv {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {F : Type}
    [Field F] {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    (k : ↥(stab (puAmalgam h.le) α)) (hk1 : toSL3 ψ k = 1) :
    ∃ b : ℕ, Odd b ∧ k ^ b ∈ (Qv (puAmalgam h.le) α).subgroupOf (stab _ α) := by
  have := finite_stab h hα
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  refine ⟨b, hb, Subgroup.mem_subgroupOf.mpr ?_⟩
  refine mem_qv_of_centralizer_uloc h hα (k ^ b).2 ?_ ⟨a, ?_⟩
  · have h1 : toSL3 ψ (k ^ b) = 1 := by rw [map_pow, hk1, one_pow]
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := (toSL3_eq_one_iff hψ _).mp h1 u hu
    calc u * ((k ^ b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal) =
        ((k ^ b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal) * u *
          ((k ^ b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal)⁻¹ *
            ((k ^ b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal) := by
          rw [this]
      _ = _ := by group
  · rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one, Subgroup.coe_one]

theorem mem_uloc_sup_dloc {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {F : Type} [Field F]
    [Finite F] [CharP F 2] {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hsurj : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    {w : (puAmalgam h.le).Universal} (hwQ : w ∈ Qv _ α)
    (hwL : ∀ l ∈ Ltil h.le L α, ⁅l, w⁆ ∈ ZM (puAmalgam h.le) α)
    {Y : Subgroup (puAmalgam h.le).Universal} (hYs : Y ≤ stab _ α)
    (hYw : ∀ y ∈ Y, y * w = w * y)
    (hQY : Qv (puAmalgam h.le) α ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal))
    (hY2 : IsPGroup 2 Y)
    (hYU : ¬ Y ≤ Subgroup.centralizer (Uloc h.le L α : Set (puAmalgam h.le).Universal)) :
    w ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
  have hQs : Qv (puAmalgam h.le) α ≤ stab (puAmalgam h.le) α := qv_le_stab _ α
  have hf : ∀ a ∈ gwSub _ α w, ∀ b ∈ gwSub _ α w,
      zvec hψ ⁅((a * b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal), w⁆ =
        zvec hψ ⁅(a : (puAmalgam h.le).Universal), w⁆ +
          ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            zvec hψ ⁅(b : (puAmalgam h.le).Universal), w⁆ :=
    fun a ha b hb => zvec_comm_mul h hfull hα hψ a b ha hb
  have hYw' : ∀ y ∈ Y, ⁅y, w⁆ = 1 := fun y hy => by
    rw [commutatorElement_def, hYw y hy, mul_inv_cancel_right, mul_inv_cancel]
  have hYH : Y.subgroupOf (stab _ α) ≤ gwSub _ α w := fun y hy => by
    rw [mem_gwSub, hYw' _ (Subgroup.mem_subgroupOf.mp hy)]
    exact Subgroup.one_mem _
  have hfY : ∀ y ∈ Y.subgroupOf (stab _ α), zvec hψ ⁅(y : (puAmalgam h.le).Universal), w⁆ = 0 :=
    fun y hy => by rw [hYw' _ (Subgroup.mem_subgroupOf.mp hy), zvec_one h hfull hψ]
  have hρH : ∀ g : SL3 F, ∃ a ∈ gwSub _ α w, toSL3 ψ a = g := by
    intro g
    obtain ⟨l, hl, hlg⟩ := exists_ltil_toSL3_eq h hfull hα hsurj hψ g
    exact ⟨l, hwL _ hl, hlg⟩
  have hP : ∀ k ∈ gwSub _ α w, toSL3 ψ k = 1 →
      ∃ b : ℕ, Odd b ∧ k ^ b ∈ (Qv (puAmalgam h.le) α).subgroupOf (stab _ α) :=
    fun k _ hk1 => exists_odd_pow_mem_qv h hα hψ k hk1
  have hPY : (Qv (puAmalgam h.le) α).subgroupOf (stab _ α) ≤
      Subgroup.normalizer ((Y.subgroupOf (stab _ α) : Subgroup _) : Set ↥(stab _ α)) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hQY (Subgroup.mem_subgroupOf.mp hq)) _)
  have hYρ : (Y.subgroupOf (stab _ α)).map (toSL3 ψ) ≠ ⊥ := by
    intro hbot
    apply hYU
    intro y hy
    have h1 : toSL3 ψ ⟨y, hYs hy⟩ = 1 := by
      have : toSL3 ψ ⟨y, hYs hy⟩ ∈ (Y.subgroupOf (stab _ α)).map (toSL3 ψ) :=
        ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := (toSL3_eq_one_iff hψ _).mp h1 u hu
    calc u * y = y * u * y⁻¹ * y := by rw [show y * u * y⁻¹ = u from this]
      _ = y * u := by group
  have hY2' : IsPGroup 2 ↥(Y.subgroupOf (stab (puAmalgam h.le) α)) :=
    hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYs).symm
  obtain ⟨n, hn⟩ := exists_coboundary_of_cocycle hf hYH hfY hρH hP hPY hYρ hY2'
  obtain ⟨u₀, hu₀⟩ := natVec_surjective hψ n
  have hUs : Uloc h.le L α ≤ stab (puAmalgam h.le) α := puTrans_le_stab h.le _ α
  have hcomm_l : ∀ l ∈ Ltil h.le L α, ⁅l, (u₀ : (puAmalgam h.le).Universal)⁻¹ * w⁆ ∈
      Zloc h.le L α := by
    intro l hl
    have hls := ltil_le_stab h α hl
    have hlu : l * (u₀ : (puAmalgam h.le).Universal) * l⁻¹ ∈ Uloc h.le L α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α hls)
        _).mp u₀.2
    have hU1 : ⁅l, (u₀ : (puAmalgam h.le).Universal)⁆ ∈ Uloc h.le L α := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ hlu (Subgroup.inv_mem _ u₀.2)
    obtain ⟨hpU, hpZ⟩ := uProj_zm h hfull hα (hwL l hl)
    have hproj_eq : uProj (Uloc h.le L α) (Zloc h.le L α) ⁅l, w⁆ =
        ⁅l, (u₀ : (puAmalgam h.le).Universal)⁆ := by
      apply natVecG_injective hψ hpU hU1
      have h1 := hn ⟨l, hls⟩ (hwL l hl)
      have h2 : natVecG hψ (l * (u₀ : (puAmalgam h.le).Universal) * l⁻¹) =
          ((toSL3 ψ ⟨l, hls⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            natVecG hψ (u₀ : (puAmalgam h.le).Universal) :=
        natVecG_conj hψ ⟨l, hls⟩ u₀.2
      have h3 : natVecG hψ (u₀ : (puAmalgam h.le).Universal)⁻¹ = -n := by
        rw [natVecG_of_mem hψ (Subgroup.inv_mem _ u₀.2),
          show (⟨(u₀ : (puAmalgam h.le).Universal)⁻¹, Subgroup.inv_mem _ u₀.2⟩ :
            ↥(Uloc h.le L α)) = u₀⁻¹ from rfl, natVec_inv, hu₀]
      have h4 : natVecG hψ (u₀ : (puAmalgam h.le).Universal) = n := by
        rw [natVecG_of_mem hψ u₀.2]
        exact hu₀
      change zvec hψ ⁅l, w⁆ = _
      rw [h1, commutatorElement_def, natVecG_mul hψ hlu (Subgroup.inv_mem _ u₀.2), h2, h3, h4,
        sub_eq_add_neg]
    rw [hproj_eq] at hpZ
    have hrw : ⁅l, (u₀ : (puAmalgam h.le).Universal)⁻¹ * w⁆ =
        (u₀ : (puAmalgam h.le).Universal)⁻¹ *
          (⁅l, (u₀ : (puAmalgam h.le).Universal)⁆⁻¹ * ⁅l, w⁆) *
            ((u₀ : (puAmalgam h.le).Universal)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) α
      (Subgroup.inv_mem _ (hUs u₀.2))) _).mp hpZ
  have hUQ : Uloc h.le L α ≤ Qv (puAmalgam h.le) α :=
    (uloc_le_zm h hfull hα).trans (zm_le_qv_self _ hα h.critDist_pos)
  have hw'Q : (u₀ : (puAmalgam h.le).Universal)⁻¹ * w ∈ Qv (puAmalgam h.le) α :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUQ u₀.2)) hwQ
  have hclQ : Subgroup.closure {(u₀ : (puAmalgam h.le).Universal)⁻¹ * w} ≤
      Qv (puAmalgam h.le) α := by
    rw [Subgroup.closure_le]
    rintro _ rfl
    exact hw'Q
  have hcl : ⁅Subgroup.closure {(u₀ : (puAmalgam h.le).Universal)⁻¹ * w}, Ltil h.le L α⁆ ≤
      Dloc h.le L α := by
    refine commutator_closure_le_of (fun s hs l hl => ?_)
      (hclQ.trans (hQs.trans (stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α)))
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (zloc_le_dloc h α (hcomm_l l hl))
  have hw'D : (u₀ : (puAmalgam h.le).Universal)⁻¹ * w ∈ Dloc h.le L α :=
    le_dloc_of_commutator_le h hα hclQ hcl (Subgroup.subset_closure rfl)
  have hw : w = (u₀ : (puAmalgam h.le).Universal) * ((u₀ : (puAmalgam h.le).Universal)⁻¹ * w) := by
    group
  rw [hw]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left u₀.2) (Subgroup.mem_sup_right hw'D)

end Main

end CFSG.Quasithin.MS93.S4A
