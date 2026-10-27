module

public import CFSG.Quasithin.H13.A7BlkV
public import CFSG.Quasithin.H13.A7BlkFin
public import CFSG.Quasithin.Background.B3Two

public section

namespace CFSG.Quasithin.H13.A7Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

@[expose] def u0Equiv : ↥(B3.U0 7) ≃* Multiplicative ↥(evenWeight 7) where
  toFun w := Multiplicative.ofAdd ⟨(w : B3.U 7).val, by
    have h : Multiplicative.ofAdd (∑ i, (w : B3.U 7).val i) = 1 := w.2
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    exact ofAdd_eq_one.mp h⟩
  invFun x := ⟨⟨((Multiplicative.toAdd x : ↥(evenWeight 7)) : Fin 7 → ZMod 2)⟩, by
    show Multiplicative.ofAdd (∑ i, ((Multiplicative.toAdd x : ↥(evenWeight 7)) :
      Fin 7 → ZMod 2) i) = 1
    rw [sum_eq_zero_of_evenWeight]
    rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def modEquiv : B3.Mod.V 7 B3.Mod.u0 ≃* Multiplicative ↥(evenWeight 7) :=
  ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (B3.U0 7))).trans
    QuotientGroup.quotientBot).trans u0Equiv

theorem modEquiv_act (σ : Perm (Fin 7)) (w : B3.Mod.V 7 B3.Mod.u0) :
    modEquiv (B3.Mod.act 7 B3.Mod.u0 σ w) =
      Multiplicative.ofAdd (permWeight 7 σ (Multiplicative.toAdd (modEquiv w))) := by
  induction w using QuotientGroup.induction_on with
  | H w => rfl

theorem act_modEquiv_symm (σ : Perm (Fin 7)) (y : Multiplicative ↥(evenWeight 7)) :
    B3.Mod.act 7 B3.Mod.u0 σ (modEquiv.symm y) =
      modEquiv.symm (Multiplicative.ofAdd (permWeight 7 σ (Multiplicative.toAdd y))) := by
  apply modEquiv.injective
  rw [modEquiv_act, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} (D : AltData K) (hshort : IsShort2 K)

omit [Finite G] in
include hshort in
theorem isElemAbelian_blockV : IsElemAbelian 2 (blockV K) :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_blockU hshort (blockV_le_blockU a.2) (blockV_le_blockU b.2))⟩⟩,
    fun _ hx => sq_blockU hshort (blockV_le_blockU hx)⟩

@[expose] noncomputable def thetaI :
    IntMod (blockV K) (isElemAbelian_blockV hshort) ≃* Multiplicative ↥(evenWeight 7) where
  toFun v := theta D hshort v
  invFun x := (theta D hshort).symm x
  left_inv := (theta D hshort).left_inv
  right_inv := (theta D hshort).right_inv
  map_mul' a b := (theta D hshort).map_mul a b

@[expose] noncomputable def phi :
    IntMod (blockV K) (isElemAbelian_blockV hshort) ≃* B3.Mod.V 7 B3.Mod.u0 :=
  (thetaI D hshort).trans modEquiv.symm

theorem congrHom_convI (g : ↥(Subgroup.normalizer (K : Set G))) :
    H.congrHom (phi D hshort) (convI (isElemAbelian_blockV hshort)
      ⟨g, mem_normalizer_blockV g.2⟩) = B3.Mod.act 7 B3.Mod.u0 (D.act g) := by
  refine MulEquiv.ext fun w => ?_
  rw [H.congrHom_apply]
  obtain ⟨v, rfl⟩ := (phi D hshort).surjective w
  rw [MulEquiv.symm_apply_apply]
  have hv : (convI (isElemAbelian_blockV hshort) ⟨g, mem_normalizer_blockV g.2⟩ v :
      ↥(blockV K)) = ⟨(g : G) * v.val * (g : G)⁻¹, conj_mem_blockV g.2 v.val_mem⟩ :=
    Subtype.ext (convI_apply_val _ _ _)
  show modEquiv.symm (theta D hshort (convI (isElemAbelian_blockV hshort)
    ⟨g, mem_normalizer_blockV g.2⟩ v)) = B3.Mod.act 7 B3.Mod.u0 (D.act g)
      (modEquiv.symm (theta D hshort v))
  rw [hv, act_modEquiv_symm]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  exact theta_conj D hshort g v

@[expose] noncomputable def img (M : Subgroup G) : Subgroup (Perm (Fin 7)) :=
  (M.subgroupOf (Subgroup.normalizer (K : Set G))).map D.act

omit [Finite G] in
theorem mem_img {M : Subgroup G} {τ : Perm (Fin 7)} :
    τ ∈ img D M ↔ ∃ g : ↥(Subgroup.normalizer (K : Set G)), (g : G) ∈ M ∧ D.act g = τ := by
  unfold img
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem act_mem_img {M : Subgroup G} {g : ↥(Subgroup.normalizer (K : Set G))}
    (hg : (g : G) ∈ M) : D.act g ∈ img D M :=
  (mem_img D).mpr ⟨g, hg, rfl⟩

omit [Finite G] in
theorem img_mono {M M' : Subgroup G} (h : M ≤ M') : img D M ≤ img D M' := by
  intro τ hτ
  obtain ⟨g, hg, rfl⟩ := (mem_img D).mp hτ
  exact act_mem_img D (h hg)

theorem autI_map_congrHom {M : Subgroup G} (hH : M ≤ Subgroup.normalizer (K : Set G)) :
    (autI (isElemAbelian_blockV hshort) M).map (H.congrHom (phi D hshort)) =
      (img D M).map (B3.Mod.act 7 B3.Mod.u0) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, hgH, rfl⟩ := (mem_autI _).mp hx
    have hgK : (g : G) ∈ Subgroup.normalizer (K : Set G) := hH hgH
    have e : g = ⟨(⟨(g : G), hgK⟩ : ↥(Subgroup.normalizer (K : Set G))),
        mem_normalizer_blockV hgK⟩ := rfl
    rw [e, congrHom_convI]
    exact ⟨_, act_mem_img D (g := ⟨g, hgK⟩) hgH, rfl⟩
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨g, hgH, rfl⟩ := (mem_img D).mp hτ
    rw [← congrHom_convI D hshort g]
    exact ⟨_, convI_mem_autI _ hgH _, rfl⟩

omit [Finite G] in
theorem isFFStarOffender_map_congrHom {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    {X A : Subgroup (MulAut V)} (h : IsFFStarOffender X A) :
    IsFFStarOffender (X.map (H.congrHom e)) (A.map (H.congrHom e)) :=
  isFFStarOffender_map_congr_equiv e h

theorem exists_offender_perm {M : Subgroup G} (hH : M ≤ Subgroup.normalizer (K : Set G))
    {B : Subgroup (MulAut (IntMod (blockV K) (isElemAbelian_blockV hshort)))}
    (hB : IsFFStarOffender (autI (isElemAbelian_blockV hshort) M) B) :
    ∃ B' : Subgroup (Perm (Fin 7)), B' ≤ img D M ∧
      B'.map (B3.Mod.act 7 B3.Mod.u0) = B.map (H.congrHom (phi D hshort)) ∧
      B3.IsOffG 7 B3.Mod.u0 B' := by
  have hBle : B.map (H.congrHom (phi D hshort)) ≤ (img D M).map (B3.Mod.act 7 B3.Mod.u0) := by
    rw [← autI_map_congrHom D hshort hH]
    exact Subgroup.map_mono hB.1
  have heq : ((B.map (H.congrHom (phi D hshort))).comap (B3.Mod.act 7 B3.Mod.u0)).map
      (B3.Mod.act 7 B3.Mod.u0) = B.map (H.congrHom (phi D hshort)) :=
    Subgroup.map_comap_eq_self (hBle.trans (Subgroup.map_le_range _ _))
  refine ⟨(B.map (H.congrHom (phi D hshort))).comap (B3.Mod.act 7 B3.Mod.u0), ?_, heq, ?_⟩
  · intro σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := hBle hσ
    rw [← B3.act_injective (n := 7) (by norm_num) B3.Mod.u0 hτσ]
    exact hτ
  · have h1 := isFFStarOffender_map_congrHom (phi D hshort) hB
    rw [autI_map_congrHom D hshort hH, ← heq] at h1
    exact ⟨Subgroup.map_mono le_top, h1.2⟩

theorem isOffG_seven {B' : Subgroup (Perm (Fin 7))}
    (h : B3.IsOffG 7 B3.Mod.u0 B') : ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ B' ∈ B3.conjClass (B3.Am 7 m) := by
  have hn : B3.SQTKn 7 := Or.inr (Or.inr (Or.inl rfl))
  have hA : B3.CaseA 7 B3.Mod.u0 := Or.inl rfl
  obtain ⟨m, hm1, hm3, hm⟩ := ((B3.B3_2_4 hn B3.Mod.u0 hA).1 B').mp h
  exact ⟨m, hm1, hm3, hm⟩

theorem ti_seven {i : ℕ} (hi : i < 3) :
    B3.ti 7 i = swap (⟨2 * i, by omega⟩ : Fin 7) ⟨2 * i + 1, by omega⟩ := by
  unfold B3.ti B3.swapN
  rw [dite_eq_left ⟨by omega, by omega⟩]

theorem cj_swap (γ : Perm (Fin 7)) (a b : Fin 7) :
    (MulAut.conj γ).toMonoidHom (swap a b) = swap (γ a) (γ b) := by
  rw [swap_apply_apply]
  rfl

theorem swap_mem_of_isOffG {B' : Subgroup (Perm (Fin 7))}
    (h : B3.IsOffG 7 B3.Mod.u0 B') : ∃ a b : Fin 7, a ≠ b ∧ swap a b ∈ B' := by
  obtain ⟨m, hm1, hm3, γ, rfl⟩ := isOffG_seven h
  refine ⟨γ 0, γ 1, γ.injective.ne (by decide), ?_⟩
  rw [← cj_swap]
  refine Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ?_)
  show swap 0 1 ∈ B3.gensAm 7 m
  unfold B3.gensAm
  rw [List.mem_map]
  exact ⟨0, List.mem_range.mpr (by omega), by rw [ti_seven (by norm_num)]; rfl⟩

theorem le_closure_swaps_of_isOffG {B' : Subgroup (Perm (Fin 7))}
    (h : B3.IsOffG 7 B3.Mod.u0 B') :
    B' ≤ Subgroup.closure {τ | τ ∈ B' ∧ ∃ a b : Fin 7, a ≠ b ∧ τ = swap a b} := by
  obtain ⟨m, hm1, hm3, γ, hγ⟩ := isOffG_seven h
  have e : B' = Subgroup.closure ((MulAut.conj γ).toMonoidHom '' {g | g ∈ B3.gensAm 7 m}) := by
    rw [hγ, B3.cj, B3.Am, MonoidHom.map_closure]
  calc B' = Subgroup.closure ((MulAut.conj γ).toMonoidHom '' {g | g ∈ B3.gensAm 7 m}) := e
    _ ≤ _ := by
      apply Subgroup.closure_mono
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Subgroup.subset_closure ⟨g, hg, rfl⟩
      · have hg' : g ∈ (List.range m).map (B3.ti 7) := hg
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg'
        have hi3 : i < 3 := by have := List.mem_range.mp hi; omega
        rw [ti_seven hi3, cj_swap]
        refine ⟨_, _, γ.injective.ne ?_, rfl⟩
        intro h'
        have := congrArg Fin.val h'
        simp at this

structure StdPos (T : Subgroup G) : Prop where
  le_normalizer : T ≤ Subgroup.normalizer (K : Set G)
  isPGroup : IsPGroup 2 T
  pstd_le : ∀ σ ∈ pstd, ∃ k : ↥K, (k : G) ∈ T ∧ (D.α k : Perm (Fin 7)) = σ
  ker_le : ∀ k : ↥K, D.α k = 1 → (k : G) ∈ T

variable {D} {T : Subgroup G}

omit [Finite G] in
theorem StdPos.isPGroup_img (hT : StdPos D T) : IsPGroup 2 (img D T) :=
  (hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT.le_normalizer).symm).map _

omit [Finite G] in
theorem act_of_mem (k : ↥K) :
    D.act ⟨k, Subgroup.le_normalizer k.2⟩ = (D.α k : Perm (Fin 7)) :=
  permAct_of_mem D.α D.surj D.ker (by norm_num) (by norm_num) k

omit [Finite G] in
theorem StdPos.pstd_le_img (hT : StdPos D T) : pstd ≤ img D T := by
  intro σ hσ
  obtain ⟨k, hkT, rfl⟩ := hT.pstd_le σ hσ
  rw [← act_of_mem]
  exact act_mem_img D hkT

omit [Finite G] in
theorem StdPos.blockQ_le (hT : StdPos D T) : blockQ K ≤ T := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := hq
  refine hT.ker_le k ?_
  have hk' : k ∈ CFSG.pCore 2 ↥K := by exact hk
  rw [← D.ker] at hk'
  exact hk'

include hshort in
omit [Finite G] in
theorem StdPos.blockV_le (hT : StdPos D T) : blockV K ≤ T :=
  blockV_le_blockU.trans ((blockU_le_blockQ hshort).trans hT.blockQ_le)

omit [Finite G] in
theorem StdPos.le_normalizer_blockV (hT : StdPos D T) :
    T ≤ Subgroup.normalizer (blockV K : Set G) :=
  fun _ ht => mem_normalizer_blockV (hT.le_normalizer ht)

omit [Finite G] in
omit [Finite G] in
theorem StdPos.img_inf_alt (hT : StdPos D T) : img D T ⊓ alternatingGroup (Fin 7) = pstd := by
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hT.pstd_le_img pstd_le_alternatingGroup) ?_).symm
  rw [card_pstd]
  exact card_le_eight inf_le_right hT.isPGroup_img.to_inf_left

omit [Finite G] in
theorem StdPos.mem_of_act_mem (hT : StdPos D T) {k t : G} (hk : k ∈ K) (ht : t ∈ T)
    (h : D.act ⟨k * t, Subgroup.mul_mem _ (Subgroup.le_normalizer hk) (hT.le_normalizer ht)⟩ ∈
      img D T) : k ∈ T := by
  have e : D.act ⟨k * t, Subgroup.mul_mem _ (Subgroup.le_normalizer hk) (hT.le_normalizer ht)⟩ =
      D.act ⟨k, Subgroup.le_normalizer hk⟩ * D.act ⟨t, hT.le_normalizer ht⟩ := by
    rw [← map_mul]
    rfl
  rw [e] at h
  have h1 : D.act ⟨k, Subgroup.le_normalizer hk⟩ ∈ img D T := by
    have h2 := (img D T).mul_mem h
      ((img D T).inv_mem (act_mem_img D (g := ⟨t, hT.le_normalizer ht⟩) ht))
    rwa [mul_inv_cancel_right] at h2
  rw [show (⟨k, Subgroup.le_normalizer hk⟩ : ↥(Subgroup.normalizer (K : Set G))) =
    ⟨((⟨k, hk⟩ : ↥K) : G), Subgroup.le_normalizer hk⟩ from rfl, act_of_mem] at h1
  have h3 : ((D.α ⟨k, hk⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ pstd := by
    rw [← hT.img_inf_alt]
    exact ⟨h1, (D.α ⟨k, hk⟩).2⟩
  obtain ⟨k₁, hk₁T, hk₁⟩ := hT.pstd_le _ h3
  have h4 : D.α (k₁⁻¹ * ⟨k, hk⟩) = 1 := by
    rw [map_mul, map_inv]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hk₁, inv_mul_cancel]
    rfl
  have h5 := hT.ker_le _ h4
  have e2 : k = (k₁ : G) * ((k₁⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e2]
  exact T.mul_mem hk₁T h5

omit [Finite G] in
theorem StdPos.swap_mem_tL (hT : StdPos D T) {a b : Fin 7} (hab : a ≠ b)
    (h : swap a b ∈ img D T) : swap a b ∈ tL :=
  A7Blk.swap_mem_tL hab fun _ hp =>
    pow_sixteen hT.isPGroup_img ((img D T).mul_mem h (hT.pstd_le_img hp))

theorem dstd_le_of_tL {X : Subgroup (Perm (Fin 7))} (h : ∀ τ ∈ tL, τ ∈ X) : dstd ≤ X := by
  have h1 : t01 ∈ X := h _ (by simp [tL])
  have h2 : t23 ∈ X := h _ (by simp [tL])
  have h3 : t45 ∈ X := h _ (by simp [tL])
  intro d hd
  simp only [mem_dstd, dstdL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X.one_mem
  · exact h1
  · exact h2
  · exact h3
  · exact X.mul_mem h1 h2
  · exact X.mul_mem h1 h3
  · exact X.mul_mem h2 h3
  · exact X.mul_mem (X.mul_mem h1 h2) h3

include hshort in
theorem StdPos.img_thompsonJ_le (hT : StdPos D T) :
    img D (thompsonJ T) ≤ dstd := by
  have hV := isElemAbelian_blockV hshort
  have hJK : thompsonJ T ≤ Subgroup.normalizer (K : Set G) :=
    (thompsonJ_le_self T).trans hT.le_normalizer
  rw [← Subgroup.map_le_map_iff_of_injective (B3.act_injective (n := 7) (by norm_num) B3.Mod.u0),
    ← autI_map_congrHom D hshort hJK, autI_thompsonJ hV hT.le_normalizer_blockV, ffJP,
    Subgroup.map_iSup]
  refine iSup_le fun B => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hB => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun _ => ?_
  have hoff := offenderImages_isFFStarOffender hV (hT.blockV_le hshort) hT.le_normalizer_blockV hB
  obtain ⟨B', hB'T, hB'e, hB'o⟩ := exists_offender_perm D hshort hT.le_normalizer hoff
  rw [← hB'e]
  refine Subgroup.map_mono
    ((le_closure_swaps_of_isOffG hB'o).trans ((Subgroup.closure_le _).mpr ?_))
  rintro τ ⟨hτ, a, b, hab, rfl⟩
  exact tL_sub (hT.swap_mem_tL hab (hB'T hτ))

omit [Finite G] in
theorem act_conj (c : ↥K) (a : G) (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    D.act ⟨(c : G) * a * (c : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.le_normalizer c.2) ha) (Subgroup.inv_mem _ (Subgroup.le_normalizer c.2))⟩ =
      (D.α c : Perm (Fin 7)) * D.act ⟨a, ha⟩ * (D.α c : Perm (Fin 7))⁻¹ := by
  rw [← act_of_mem, ← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite G] in
theorem StdPos.isFFOffender_cjSub (hT : StdPos D T) {A : Subgroup G}
    (hA : IsFFOffender T (blockV K) A) (hAd : img D A ≤ dstd) (hdT : dstd ≤ img D T) (c : ↥K)
    (hc : (D.α c : Perm (Fin 7)) ∈ Subgroup.normalizer (dstd : Set (Perm (Fin 7)))) :
    IsFFOffender T (blockV K) (cjSub (c : G) A) := by
  have hAT : A ≤ T := hA.1.1
  have hle : cjSub (c : G) A ≤ T := by
    intro x hx
    rw [mem_cjSub] at hx
    set a := (c : G)⁻¹ * x * c with ha
    have haN : a ∈ Subgroup.normalizer (K : Set G) := hT.le_normalizer (hAT hx)
    have hxe : x = (c : G) * a * (c : G)⁻¹ := by rw [ha]; group
    have hk : (c : G) * (a * (c : G)⁻¹ * a⁻¹) ∈ K :=
      K.mul_mem c.2 ((Subgroup.mem_normalizer_iff.mp haN _).mp (K.inv_mem c.2))
    have hkt : x = ((c : G) * (a * (c : G)⁻¹ * a⁻¹)) * a := by rw [hxe]; group
    rw [hkt]
    refine T.mul_mem (hT.mem_of_act_mem hk (hAT hx) ?_) (hAT hx)
    have e : (⟨(c : G) * (a * (c : G)⁻¹ * a⁻¹) * a, Subgroup.mul_mem _ (Subgroup.le_normalizer hk)
        (hT.le_normalizer (hAT hx))⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨(c : G) * a * (c : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _
          (Subgroup.le_normalizer c.2) haN) (Subgroup.inv_mem _ (Subgroup.le_normalizer c.2))⟩ :=
      Subtype.ext (by group)
    rw [e, act_conj (D := D) c a haN]
    apply hdT
    have hd : D.act ⟨a, haN⟩ ∈ dstd := hAd (act_mem_img D (g := ⟨a, haN⟩) hx)
    exact (Subgroup.mem_normalizer_iff.mp hc _).mp hd
  refine ⟨⟨hle, isElemAbelian_cjSub hA.1.2.1, fun B hB hBe => ?_⟩, ?_⟩
  · rw [card_cjSub]
    exact hA.1.2.2 B hB hBe
  · exact not_cjSub_le_centralizer (mem_normalizer_blockV (Subgroup.le_normalizer c.2)) hA.2

include hshort in
theorem StdPos.img_thompsonJ_eq (hT : StdPos D T)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (blockV K : Set G)) :
    img D (thompsonJ T) = dstd := by
  have hV := isElemAbelian_blockV hshort
  obtain ⟨A, hA⟩ := (offenderImages_nonempty_iff hV).mp
    ((offenderImages_nonempty_iff_not_le hV).mpr hJ)
  have hAT : A ≤ T := hA.1.1
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAT.trans hT.le_normalizer
  have hoff := offenderImages_isFFStarOffender hV (hT.blockV_le hshort) hT.le_normalizer_blockV
    ⟨A, hA, rfl⟩
  obtain ⟨B', hB'T, hB'e, hB'o⟩ := exists_offender_perm D hshort hT.le_normalizer hoff
  have hB'A : B' = img D A := by
    apply Subgroup.map_injective (B3.act_injective (n := 7) (by norm_num) B3.Mod.u0)
    rw [hB'e, autI_map_congrHom D hshort hAK]
  have hAd : img D A ≤ dstd := by
    rw [← hB'A]
    refine (le_closure_swaps_of_isOffG hB'o).trans ((Subgroup.closure_le _).mpr ?_)
    rintro τ ⟨hτ, a, b, hab, rfl⟩
    exact tL_sub (hT.swap_mem_tL hab (hB'T hτ))
  obtain ⟨a, b, hab, hτ⟩ := swap_mem_of_isOffG hB'o
  have hτL : swap a b ∈ tL := hT.swap_mem_tL hab (hB'T hτ)
  have hdT : dstd ≤ img D T := by
    refine dstd_le_of_tL fun σ hσ => ?_
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mem_pstd_mul hτL hσ
    exact (img D T).mul_mem ((img D T).mul_mem (hT.pstd_le_img hp) (hB'T hτ))
      (hT.pstd_le_img hq)
  obtain ⟨g, hg⟩ := D.surj ⟨pi3, pi3_mem⟩
  have hg' : (D.α g : Perm (Fin 7)) = pi3 := by rw [hg]
  have hgg : (D.α (g * g) : Perm (Fin 7)) = pi3 * pi3 := by rw [map_mul, Subgroup.coe_mul, hg']
  have hgN : pi3 ∈ Subgroup.normalizer (dstd : Set (Perm (Fin 7))) := pi3_mem_normalizer_dstd
  have hA₁ := hT.isFFOffender_cjSub hA hAd hdT g (by rw [hg']; exact hgN)
  have hA₂ := hT.isFFOffender_cjSub hA hAd hdT (g * g)
    (by rw [hgg]; exact Subgroup.mul_mem _ hgN hgN)
  have hJle : ∀ {X : Subgroup G}, IsFFOffender T (blockV K) X → img D X ≤ img D (thompsonJ T) :=
    fun hX => img_mono D (le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) _
      hX.1)
  rw [hB'A] at hτ
  obtain ⟨a₀, ha₀A, ha₀⟩ := (mem_img D).mp hτ
  have hconj : ∀ c : ↥K, (D.α c : Perm (Fin 7)) * swap a b * (D.α c : Perm (Fin 7))⁻¹ ∈
      img D (cjSub (c : G) A) := by
    intro c
    have h1 := act_conj (D := D) c a₀ a₀.2
    rw [show (⟨(a₀ : G), a₀.2⟩ : ↥(Subgroup.normalizer (K : Set G))) = a₀ from rfl, ha₀] at h1
    rw [← h1]
    refine act_mem_img D ?_
    rw [mem_cjSub]
    simpa [mul_assoc] using ha₀A
  refine le_antisymm (hT.img_thompsonJ_le hshort) (dstd_le_of_tL fun σ hσ => ?_)
  rcases tL_orbit hτL hσ with rfl | rfl | rfl
  · exact hJle hA ((mem_img D).mpr ⟨a₀, ha₀A, ha₀⟩)
  · have := hconj g
    rw [hg'] at this
    exact hJle hA₁ this
  · have := hconj (g * g)
    rw [hgg] at this
    exact hJle hA₂ this

@[expose] def ePair (i : Fin 3) : ↥(evenWeight 7) :=
  ⟨fun j => if (j : ℕ) / 2 = i then 1 else 0, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    fin_cases i <;> decide⟩

theorem ePair_fixed : ∀ i : Fin 3, (dstdL.all fun d =>
    decide (∀ j : Fin 7, (ePair i : Fin 7 → ZMod 2) (d⁻¹ j) = (ePair i : Fin 7 → ZMod 2) j)) =
      true := by
  decide +kernel

theorem permWeight_ePair {d : Perm (Fin 7)} (hd : d ∈ dstd) (i : Fin 3) :
    permWeight 7 d (ePair i) = ePair i := by
  have h := of_decide_eq_true (all_true (ePair_fixed i) hd)
  exact Subtype.ext (funext h)

theorem div_two_eq_of_ePair : ∀ a j : Fin 7,
    (∀ i : Fin 3, (ePair i : Fin 7 → ZMod 2) a = (ePair i : Fin 7 → ZMod 2) j) →
      (a : ℕ) / 2 = (j : ℕ) / 2 := by
  decide

include hshort in
theorem StdPos.img_baum (hT : StdPos D T) :
    img D (baum T) = ⊥ ∨ img D (baum T) = dstd := by
  have hV := isElemAbelian_blockV hshort
  have key : ∀ x ∈ baum T, ∀ v ∈ blockV K, v ∈ Subgroup.centralizer (thompsonJ T : Set G) →
      x * v = v * x := by
    intro x hx v hv hvJ
    have h1 := inf_centralizer_thompsonJ_le hV (hT.blockV_le hshort) ⟨hv, hvJ⟩
    exact (Subgroup.mem_centralizer_iff.mp hx.2 v h1).symm
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (blockV K : Set G)
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    obtain ⟨x, hxB, rfl⟩ := (mem_img D).mp hσ
    have hxC : (x : G) ∈ Subgroup.centralizer (blockV K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (key x hxB v hv (Subgroup.le_centralizer_iff.mp hJ hv)).symm
    have h1 := congrHom_convI D hshort x
    rw [(convI_eq_one_iff hV _).mpr hxC, map_one] at h1
    exact B3.act_injective (n := 7) (by norm_num) B3.Mod.u0 (h1.symm.trans (map_one _).symm)
  · right
    have hJd := hT.img_thompsonJ_eq hshort hJ
    refine le_antisymm ?_ (hJd ▸ img_mono D (B2F.thompsonJ_le_baum T))
    intro σ hσ
    obtain ⟨x, hxB, rfl⟩ := (mem_img D).mp hσ
    have hfix : ∀ i : Fin 3, permWeight 7 (D.act x) (ePair i) = ePair i := by
      intro i
      set v : ↥(blockV K) := (theta D hshort).symm (Multiplicative.ofAdd (ePair i)) with hv
      have hvJ : (v : G) ∈ Subgroup.centralizer (thompsonJ T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hjK : j ∈ Subgroup.normalizer (K : Set G) := (thompsonJ_le_self T).trans
          hT.le_normalizer hj
        have h1 := theta_conj D hshort ⟨j, hjK⟩ v
        rw [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd,
          permWeight_ePair (hJd ▸ act_mem_img D (g := ⟨j, hjK⟩) hj) i] at h1
        have h2 : (⟨j * v * j⁻¹, conj_mem_blockV hjK v.2⟩ : ↥(blockV K)) = v := by
          apply (theta D hshort).injective
          apply Multiplicative.toAdd.injective
          rw [h1, hv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
        have h3 : j * (v : G) * j⁻¹ = v := congrArg Subtype.val h2
        calc j * (v : G) = j * v * j⁻¹ * j := by group
          _ = v * j := by rw [h3]
      have h1 := key x hxB v v.2 hvJ
      have h2 := theta_conj D hshort x v
      have h3 : (⟨(x : G) * v * (x : G)⁻¹, conj_mem_blockV x.2 v.2⟩ : ↥(blockV K)) = v :=
        Subtype.ext (show (x : G) * v * (x : G)⁻¹ = v by rw [h1, mul_inv_cancel_right])
      rw [h3, hv, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h2
      exact h2.symm
    have hpair : ∀ j, (((D.act x)⁻¹ j : Fin 7) : ℕ) / 2 = (j : ℕ) / 2 := by
      intro j
      refine div_two_eq_of_ePair _ _ fun i => ?_
      have := congrArg (fun y : ↥(evenWeight 7) => (y : Fin 7 → ZMod 2) j) (hfix i)
      exact this
    have h := mem_dstd_of_pairs _ hpair
    simpa using dstd.inv_mem h

include hshort in
theorem StdPos.exists_mem_normalizer_baum (hT : StdPos D T) :
    ∃ k : ↥K, (D.α k : Perm (Fin 7)) = pi3 ∧
      (k : G) ∈ Subgroup.normalizer (baum T : Set G) := by
  set Sp := img D (baum T) with hSp
  have hN : pi3 ∈ Subgroup.normalizer (Sp : Set (Perm (Fin 7))) := by
    rcases hT.img_baum hshort with h | h
    · rw [hSp, h]
      exact Subgroup.mem_normalizer_iff.mpr fun y => by simp
    · rw [hSp, h]
      exact pi3_mem_normalizer_dstd
  obtain ⟨k, hk⟩ := D.surj ⟨pi3, pi3_mem⟩
  have hk' : (D.α k : Perm (Fin 7)) = pi3 := by rw [hk]
  set Q : Subgroup G := T ⊓ (Sp.comap D.act).map (Subgroup.normalizer (K : Set G)).subtype
    with hQ
  have hBQ : baum T ≤ Q := fun x hx =>
    ⟨B2F.baum_le T hx, ⟨⟨x, hT.le_normalizer (B2F.baum_le T hx)⟩, act_mem_img D hx, rfl⟩⟩
  have hQT : Q ≤ T := inf_le_left
  have hconj : ∀ c : ↥K, (D.α c : Perm (Fin 7)) ∈ Subgroup.normalizer (Sp : Set (Perm (Fin 7))) →
      ∀ y ∈ Q, (c : G) * y * (c : G)⁻¹ ∈ Q := by
    intro c hc y hy
    obtain ⟨hyT', ⟨y', hy', rfl⟩⟩ := hy
    have hyT : (y' : G) ∈ T := hyT'
    have hyN := y'.2
    have hkK : (c : G) * ((y' : G) * (c : G)⁻¹ * (y' : G)⁻¹) ∈ K :=
      K.mul_mem c.2 ((Subgroup.mem_normalizer_iff.mp hyN _).mp (K.inv_mem c.2))
    have hmem : D.act ⟨(c : G) * y' * (c : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.le_normalizer c.2) hyN) (Subgroup.inv_mem _ (Subgroup.le_normalizer c.2))⟩ ∈
          Sp := by
      rw [act_conj (D := D) c y' hyN]
      exact (Subgroup.mem_normalizer_iff.mp hc _).mp hy'
    refine ⟨?_, ⟨⟨_, _⟩, hmem, rfl⟩⟩
    have e : (c : G) * y' * (c : G)⁻¹ = ((c : G) * ((y' : G) * (c : G)⁻¹ * (y' : G)⁻¹)) * y' := by
      group
    show (c : G) * y' * (c : G)⁻¹ ∈ T
    rw [e]
    refine T.mul_mem (hT.mem_of_act_mem hkK hyT ?_) hyT
    have e2 : (⟨(c : G) * ((y' : G) * (c : G)⁻¹ * (y' : G)⁻¹) * y', Subgroup.mul_mem _
        (Subgroup.le_normalizer hkK) (hT.le_normalizer hyT)⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨(c : G) * y' * (c : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _
          (Subgroup.le_normalizer c.2) hyN) (Subgroup.inv_mem _ (Subgroup.le_normalizer c.2))⟩ :=
      Subtype.ext (by group)
    rw [e2]
    exact img_mono D (B2F.baum_le T) hmem
  have hkQ : (k : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj k (by rw [hk']; exact hN) y
    · intro hy
      have h1 := hconj k⁻¹ (by
        rw [map_inv, Subgroup.coe_inv, hk']
        exact Subgroup.inv_mem _ hN) _ hy
      simpa [mul_assoc] using h1
  refine ⟨k, hk', ?_⟩
  rw [baum_eq_of_le hBQ hQT]
  exact normalizer_le_normalizer_baum Q hkQ

end CFSG.Quasithin.H13.A7Blk

end
