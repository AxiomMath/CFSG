module

public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.F9Geometry

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def IsTransvectionGroupOn (X Y C : Subgroup G) : Prop :=
  X ≤ Subgroup.normalizer (Y : Set G) ∧ Nat.card C = 2 ∧ ⁅X, Y⁆ = C

section Fin

variable [Finite G]

omit [Finite G] in
theorem le_normalizer_of_commutator_le {X Y : Subgroup G} (h : ⁅X, Y⁆ ≤ Y) :
    X ≤ Subgroup.normalizer (Y : Set G) := by
  intro x hx
  have key : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
    intro x hx y hy
    have := h (Subgroup.commutator_mem_commutator hx hy)
    have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact Y.mul_mem this hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hy
  have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
  rwa [e] at this

namespace F9

omit [Finite G] in
theorem relIndex_conjSub (y : G) (X Y : Subgroup G) :
    (conjSub y X).relIndex (conjSub y Y) = X.relIndex Y :=
  Subgroup.relIndex_map_map_of_injective X Y (MulAut.conj y).injective

omit [Finite G] in
theorem mIdx_conjSub (y : G) (X Y : Subgroup G) :
    mIdx (conjSub y X) (conjSub y Y) = mIdx X Y := by
  unfold mIdx
  rw [relIndex_conjSub]

end F9

namespace HypF98

variable {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem Vγ_le_H (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Uγ V H (g : G) ≤ H := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have := (h.F913_2 s).2 γ₂ hγ₂nb hd
  rw [stab_γ₁ h.amalgamHypV.le₂] at this
  exact this.trans ((pCoreOf_le 2 _).trans inf_le_left)

theorem Uγ_le_H (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Uγ Vp H (g : G) ≤ H := h.Uγ_le_Vγ.trans (h.Vγ_le_H s)

omit [Finite G] in
theorem isElemAbelian_Vγ (h : HypF98 T V L V₁ Vp H) :
    IsElemAbelian 2 (F8.Uγ V H (g : G)) := isElemAbelian_conjSub h.F911_2

omit [Finite G] in
theorem isElemAbelian_Uγ (h : HypF98 T V L V₁ Vp H) :
    IsElemAbelian 2 (F8.Uγ Vp H (g : G)) := isElemAbelian_conjSub h.F911_3

omit [Finite G] in
theorem card_A₁ (h : HypF98 T V L V₁ Vp H) : Nat.card (F8.A₁ V₁ (g : G)) = 2 :=
  (card_conjSub _ _).trans h.card_V₁

omit [Finite G] in
theorem A₁_le_Uγ (h : HypF98 T V L V₁ Vp H) :
    F8.A₁ V₁ (g : G) ≤ F8.Uγ Vp H (g : G) :=
  conjSub_mono _ (h.V₁_le_Vp.trans (le_conjClosure Vp H))

theorem F916_1 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hD : F8.Uγ Vp H (g : G) = F8.Dγ Vp V₁ H (g : G)) :
    (F8.DH Vp V₁ H (g : G) < conjClosure Vp H ∧
        IsTransvectionGroupOn (conjClosure Vp H) (F8.Uγ Vp H (g : G)) V₁) ∨
      (F8.DH Vp V₁ H (g : G) = conjClosure Vp H ∧ ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ = ⊥ ∧
        IsTransvectionGroupOn V (F8.Uγ Vp H (g : G)) V₁) := by
  have h3 := h.F913_3 s (X := Vp) (Y := Vp) (Or.inl rfl) (Or.inl rfl)
  have h3V := h.F913_3 s (X := V) (Y := Vp) (Or.inr rfl) (Or.inl rfl)
  have h5a := h.F913_5a s
  have h5b := h.F913_5b s
  have hV₁ne : V₁ ≠ ⊥ := h.V₁_ne_bot
  have hUgH := h.Uγ_le_H s
  have hA₁U := h.A₁_le_Uγ (g := g)
  have hcomm₁ : ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ ≤ V₁ := by
    refine Subgroup.commutator_le.mpr fun u hu x hx => ?_
    have hxD : x ∈ F8.Dγ Vp V₁ H (g : G) := hD.le hx
    have := V₁.inv_mem (hxD.2.2 u hu)
    have e : (x * u * x⁻¹ * u⁻¹)⁻¹ = u * x * u⁻¹ * x⁻¹ := by group
    rwa [e] at this
  by_cases hn : ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ = ⊥
  ·
    right
    have hUC : conjClosure Vp H ≤ Subgroup.centralizer (F8.Uγ Vp H (g : G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hn
    have hDH : F8.DH Vp V₁ H (g : G) = conjClosure Vp H := by
      refine le_antisymm (centralizerMod_le_left _ _ _) fun u hu => ?_
      have hcen := Subgroup.mem_centralizer_iff.mp (hUC hu)
      refine ⟨hu, ?_, fun x hx => ?_⟩
      · have h1 : u ∈ Subgroup.centralizer (F8.A₁ V₁ (g : G) : Set G) :=
          Subgroup.centralizer_le (fun a ha => hA₁U ha) (hUC hu)
        exact Subgroup.centralizer_le_normalizer _ h1
      · have : u * x * u⁻¹ * x⁻¹ = 1 := by
          have := hcen x hx
          rw [← this]; group
        rw [this]; exact (F8.A₁ V₁ (g : G)).one_mem
    have hUgC : F8.Uγ Vp H (g : G) ≤ H ⊓ Subgroup.centralizer (Vp : Set G) := by
      intro x hx
      refine ⟨hUgH hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp (hUC (le_conjClosure Vp H hz)) x hx
      exact this.symm
    have hVU : ⁅V, F8.Uγ Vp H (g : G)⁆ ≤ F8.Uγ Vp H (g : G) :=
      ((Subgroup.commutator_mono (le_conjClosure V H) le_rfl).trans h3V).trans inf_le_right
    refine ⟨hDH, hn, ?_⟩
    rcases h.case_g with hi | hii
    · have hle : ⁅F8.Uγ Vp H (g : G), V⁆ ≤ V₁ := by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl hUgC).trans hi
      rcases eq_bot_or_eq_of_card_eq_two h.card_V₁ hle with hb | he
      · exact absurd (by rw [hb]; exact bot_le) h5a
      · refine ⟨le_normalizer_of_commutator_le hVU, h.card_V₁, ?_⟩
        rw [Subgroup.commutator_comm]; exact he
    · exfalso
      obtain ⟨x, hx, hxne⟩ : ∃ x ∈ F8.Uγ Vp H (g : G), ⁅V, Subgroup.zpowers x⁆ ≠ ⊥ := by
        by_contra hall
        push Not at hall
        apply h5a
        refine Subgroup.commutator_le.mpr fun x hx v hv => ?_
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall x hx) hv
        have h1 := Subgroup.mem_centralizer_iff.mp this x (Subgroup.mem_zpowers x)
        have h2 : x * v * x⁻¹ * v⁻¹ = 1 := by rw [h1]; group
        change x * v * x⁻¹ * v⁻¹ ∈ F8.A₁ V₁ (g : G)
        rw [h2]; exact (F8.A₁ V₁ (g : G)).one_mem
      have hY : ⁅V, Subgroup.zpowers x⁆ ≤ F8.Uγ V H (g : G) :=
        (((Subgroup.commutator_mono (le_conjClosure V H) ((Subgroup.zpowers_le).mpr hx)).trans
          h3V).trans inf_le_right).trans h.Uγ_le_Vγ
      have hVγab := h.isElemAbelian_Vγ (g := g)
      have hVγN : F8.Uγ V H (g : G) ≤ Subgroup.normalizer
          ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
        intro w hw
        refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
        exact isElemAbelian_comm hVγab (hY hy) hw
      have hVγC : F8.Uγ V H (g : G) ≤ Subgroup.centralizer (V : Set G) := by
        unfold F8.Uγ
        rw [conjSub_le_iff]
        refine conjClosure_le fun k hk v hv => ?_
        rw [mem_conjSub, inv_inv]
        have hmem : (g : G) * k * v * ((g : G) * k)⁻¹ ∈ conjSub ((g : G) * k) V :=
          mul_mem_conjSub hv
        have hle : conjSub ((g : G) * k) V ≤ F8.Uγ V H (g : G) := by
          rw [conjSub_mul]
          exact conjSub_mono _ (HypF91.conjSub_le_conjClosure hk)
        have := hii x ⟨hUgH hx, hUgC hx |>.2⟩ hxne ((g : G) * k)⁻¹
          (by rw [inv_inv]; exact hle.trans hVγN)
        rw [inv_inv] at this
        have h2 := this hmem
        have e : (g : G) * (k * v * k⁻¹) * (g : G)⁻¹ =
            (g : G) * k * v * ((g : G) * k)⁻¹ := by group
        rw [e]; exact h2
      apply h5a
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (h.Uγ_le_Vγ.trans hVγC)]
      exact bot_le
  ·
    left
    have hUN : conjClosure Vp H ≤ Subgroup.normalizer (F8.Uγ Vp H (g : G) : Set G) :=
      le_normalizer_of_commutator_le (h3.trans inf_le_right)
    have heq : ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ = V₁ := by
      rcases eq_bot_or_eq_of_card_eq_two h.card_V₁ hcomm₁ with hb | he
      · exact absurd hb hn
      · exact he
    refine ⟨lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hDH => ?_,
      hUN, h.card_V₁, heq⟩
    have hle : ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) := by
      refine Subgroup.commutator_le.mpr fun u hu x hx => ?_
      have hu' : u ∈ F8.DH Vp V₁ H (g : G) := hDH ▸ hu
      exact hu'.2.2 x hx
    rw [heq] at hle
    exact hV₁ne ((inf_eq_left.mpr hle).symm.trans h5b)

omit [Finite G] in
theorem relIndex_eq_two_pow_mIdx [Finite G] {X Y : Subgroup G} (hX : IsPGroup 2 X) :
    Y.relIndex X = 2 ^ mIdx X Y := by
  obtain ⟨n, hn⟩ := IsPGroup.index (p := 2) (G := ↥X) hX (Y.subgroupOf X)
  unfold mIdx Subgroup.relIndex
  rw [hn, padicValNat.prime_pow]

theorem Dγ_eq_inf_pCoreOf (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Dγ Vp V₁ H (g : G) = F8.Uγ Vp H (g : G) ⊓ pCoreOf 2 H := by
  have hUgH := h.Uγ_le_H s
  ext x
  rw [Subgroup.mem_inf, h.toHypF91.pCoreOf_eq_centralizerMod]
  constructor
  · rintro ⟨hx, hxN, hxc⟩
    exact ⟨hx, hUgH hx, hxN, hxc⟩
  · rintro ⟨hx, -, hxN, hxc⟩
    exact ⟨hx, hxN, hxc⟩

theorem rk_autOn_tilde_Uγ (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    rk (autOn (tildeOf V₁ (F8.Uγ Vp H (g : G))) (tildeOf V₁ (conjClosure Vp H))) =
      mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) := by
  unfold rk mIdx
  rw [h.toHypF91.card_autOn_tilde (h.Uγ_le_H s), h.Dγ_eq_inf_pCoreOf s]

theorem F916_2_aux (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)))
    (hle : mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ≤
      mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G))) :
    QCrit V₁ Vp H (F8.Uγ Vp H (g : G)) ∧
      (2 * mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
          mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) (F8.Uγ Vp H (g : G))) →
        mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
            mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∧
          centralizerMod V₁ (F8.Uγ Vp H (g : G)) (F8.DH Vp V₁ H (g : G)) =
            F8.Dγ Vp V₁ H (g : G) ∧
          ⁅F8.Uγ Vp H (g : G), F8.DH Vp V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) ∧
          Nat.card (F8.A₁ V₁ (g : G)) = 2 ∧ F8.A₁ V₁ (g : G) ⊓ V₁ = ⊥ ∧
          F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G)) := by
  have hUgH := h.Uγ_le_H s
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hUH : conjClosure Vp H ≤ H := hUQ.trans (pCoreOf_le 2 H)
  have h3 := h.F913_3 s (X := Vp) (Y := Vp) (Or.inl rfl) (Or.inl rfl)
  have h5b := h.F913_5b s
  have hcardA := h.card_A₁ (g := g)
  have hUgab := h.isElemAbelian_Uγ (g := g)
  have hA₁U := h.A₁_le_Uγ (g := g)
  have hDγ : F8.Dγ Vp V₁ H (g : G) = F8.Uγ Vp H (g : G) ⊓ pCoreOf 2 H := by
    ext x
    rw [Subgroup.mem_inf, h.pCoreOf_eq_centralizerMod]
    constructor
    · rintro ⟨hx, hxN, hxc⟩
      exact ⟨hx, hUgH hx, hxN, hxc⟩
    · rintro ⟨hx, -, hxN, hxc⟩
      exact ⟨hx, hxN, hxc⟩
  have hDU : F8.DH Vp V₁ H (g : G) ≤ conjClosure Vp H := centralizerMod_le_left _ _ _
  have hDcomm : ⁅F8.DH Vp V₁ H (g : G), F8.Uγ Vp H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) :=
    Subgroup.commutator_le.mpr fun d hd x hx => hd.2.2 x hx
  have hCX : F8.A₁ V₁ (g : G) ≤ Subgroup.centralizer (F8.DH Vp V₁ H (g : G) : Set G) := by
    intro a ha
    have hd : F8.DH Vp V₁ H (g : G) ≤ Subgroup.normalizer (F8.A₁ V₁ (g : G) : Set G) :=
      fun d hd => hd.2.1
    rw [normalizer_eq_centralizer_of_card_eq_two hcardA] at hd
    refine Subgroup.mem_centralizer_iff.mpr fun d hd' => ?_
    have := Subgroup.mem_centralizer_iff.mp (hd hd') a ha
    exact this.symm
  have hCY : F8.A₁ V₁ (g : G) ≤ Subgroup.centralizer (F8.Uγ Vp H (g : G) : Set G) := by
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact isElemAbelian_comm hUgab (hA₁U ha) hx |>.symm
  have hpair := relIndex_eq_of_commutator_le (X := F8.DH Vp V₁ H (g : G)) hUgab hcardA hDcomm
    hCX hCY
  have hF7 := h.F913_7 s
  set U := conjClosure Vp H with hU
  set Ug := F8.Uγ Vp H (g : G) with hUg
  set D := F8.DH Vp V₁ H (g : G) with hD
  set Dg := F8.Dγ Vp V₁ H (g : G) with hDg
  set A := F8.A₁ V₁ (g : G) with hA
  set cM := centralizerMod V₁ U Ug with hcM
  have hrp : ∀ X Y : Subgroup G, 0 < Y.relIndex X := fun X Y =>
    Nat.pos_of_ne_zero (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
  have hDgC : Dg ≤ Ug ⊓ Subgroup.centralizer (D : Set G) := by
    refine le_inf (centralizerMod_le_left _ _ _) ?_
    rw [Subgroup.commutator_comm] at hF7
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hF7
  have hCDcM : D ⊓ Subgroup.centralizer (Ug : Set G) ≤ cM := by
    intro x hx
    refine ⟨hDU hx.1, h.H_normalizes_V₁ (hUH (hDU hx.1)), fun y hy => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hx.2 y hy
    have e : x * y * x⁻¹ * y⁻¹ = 1 := by rw [← this]; group
    rw [e]; exact V₁.one_mem
  have hpU : IsPGroup 2 U := h.toHypF91.isPGroup_conjClosure
  have hpUg : IsPGroup 2 Ug := isPGroup_of_isElemAbelian hUgab
  have ha : Dg.relIndex Ug = 2 ^ mIdx Ug Dg := relIndex_eq_two_pow_mIdx hpUg
  have hd : D.relIndex U = 2 ^ mIdx U D := relIndex_eq_two_pow_mIdx hpU
  have hc : cM.relIndex U = 2 ^ mIdx U cM := relIndex_eq_two_pow_mIdx hpU
  have t1 := Subgroup.relIndex_mul_relIndex Dg (Ug ⊓ Subgroup.centralizer (D : Set G)) Ug hDgC
    inf_le_left
  have t2 := Subgroup.relIndex_mul_relIndex (D ⊓ Subgroup.centralizer (Ug : Set G)) D U
    inf_le_left hDU
  have t3 := Subgroup.relIndex_mul_relIndex (D ⊓ Subgroup.centralizer (Ug : Set G)) cM U hCDcM
    (centralizerMod_le_left _ _ _)
  have hdle : D.relIndex U ≤ Dg.relIndex Ug := by
    rw [hd, ha]; exact Nat.pow_le_pow_right (by norm_num) hle
  have hfle : (Ug ⊓ Subgroup.centralizer (D : Set G)).relIndex Ug ≤ Dg.relIndex Ug := by
    rw [← t1]
    exact Nat.le_mul_of_pos_left _ (hrp _ _)
  have hcle : cM.relIndex U ≤ (D ⊓ Subgroup.centralizer (Ug : Set G)).relIndex D * D.relIndex U := by
    rw [t2, ← t3]
    exact Nat.le_mul_of_pos_left _ (hrp _ _)
  have hcle2 : cM.relIndex U ≤ Dg.relIndex Ug * Dg.relIndex Ug := by
    refine hcle.trans ?_
    rw [hpair]
    exact Nat.mul_le_mul hfle hdle
  have hDgne : Dg ≠ Ug := fun hEq => by
    have h1 : Dg.relIndex Ug = 1 := Subgroup.relIndex_eq_one.mpr hEq.ge
    unfold mIdx at hpos
    rw [h1] at hpos
    simp at hpos
  have hnt : ¬ Ug ≤ pCoreOf 2 H := by
    intro hle'
    exact hDgne (by rw [hDγ]; exact inf_eq_left.mpr hle')
  have hquad : ∀ b₁ ∈ Ug, ∀ b₂ ∈ Ug, ∀ u ∈ U,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ V₁ := by
    intro b₁ hb₁ b₂ hb₂ u hu
    have hc0 : b₁ * u * b₁⁻¹ * u⁻¹ ∈ Ug := by
      have := Subgroup.commutator_mem_commutator hb₁ hu
      rw [Subgroup.commutator_comm] at this
      exact (h3.trans inf_le_right) this
    have := isElemAbelian_comm hUgab hb₂ hc0
    have e : b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ = 1 := by
      rw [this]; group
    rw [e]; exact V₁.one_mem
  have hr : cM.relIndex U ≤ ((Ug ⊓ pCoreOf 2 H).relIndex Ug) ^ 2 := by
    rw [← hDγ, sq]; exact hcle2
  refine ⟨⟨hUgH, hUgab, hnt, hquad, hr⟩, fun heq => ?_⟩
  have hcEq : cM.relIndex U = Dg.relIndex Ug * Dg.relIndex Ug := by
    rw [hc, ← heq, ha, ← pow_add, two_mul]
  have hge : Dg.relIndex Ug * Dg.relIndex Ug ≤
      (Ug ⊓ Subgroup.centralizer (D : Set G)).relIndex Ug * D.relIndex U := by
    have := hcle
    rw [hpair, hcEq] at this
    exact this
  have hfpos := hrp Ug (Ug ⊓ Subgroup.centralizer (D : Set G))
  have hdpos := hrp U D
  have hapos := hrp Ug Dg
  have hfa : (Ug ⊓ Subgroup.centralizer (D : Set G)).relIndex Ug = Dg.relIndex Ug := by
    by_contra hne
    have hlt : (Ug ⊓ Subgroup.centralizer (D : Set G)).relIndex Ug + 1 ≤ Dg.relIndex Ug :=
      Nat.succ_le_of_lt (lt_of_le_of_ne hfle hne)
    nlinarith [Nat.mul_le_mul_right (D.relIndex U) hlt, Nat.mul_le_mul_left (Dg.relIndex Ug) hdle]
  have hda : D.relIndex U = Dg.relIndex Ug := by
    by_contra hne
    have hlt : D.relIndex U + 1 ≤ Dg.relIndex Ug := Nat.succ_le_of_lt (lt_of_le_of_ne hdle hne)
    nlinarith [Nat.mul_le_mul_left ((Ug ⊓ Subgroup.centralizer (D : Set G)).relIndex Ug) hlt,
      Nat.mul_le_mul_right (Dg.relIndex Ug) hfle]
  have hDgEq : Dg = Ug ⊓ Subgroup.centralizer (D : Set G) := by
    refine le_antisymm hDgC ?_
    have hj : Dg.relIndex (Ug ⊓ Subgroup.centralizer (D : Set G)) = 1 := by
      have := t1
      rw [hfa] at this
      have h1 : Dg.relIndex (Ug ⊓ Subgroup.centralizer (D : Set G)) * Dg.relIndex Ug =
          1 * Dg.relIndex Ug := by rw [this, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hapos h1
    exact Subgroup.relIndex_eq_one.mp hj
  have hcMD : centralizerMod V₁ Ug D = Ug ⊓ Subgroup.centralizer (D : Set G) := by
    ext x
    constructor
    · rintro ⟨hxU, hxN, hxc⟩
      refine ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have h1 := hxc d hd
      have h2 := hd.2.2 x hxU
      have h2' : x * d * x⁻¹ * d⁻¹ ∈ A := by
        have := A.inv_mem (hd.2.2 x hxU)
        have e : (d * x * d⁻¹ * x⁻¹)⁻¹ = x * d * x⁻¹ * d⁻¹ := by group
        rwa [e] at this
      have h3' : x * d * x⁻¹ * d⁻¹ ∈ V₁ ⊓ A := ⟨h1, h2'⟩
      rw [h5b, Subgroup.mem_bot] at h3'
      calc d * x = (x * d * x⁻¹ * d⁻¹)⁻¹ * (x * d) := by group
        _ = x * d := by rw [h3']; group
    · rintro ⟨hxU, hxc⟩
      refine ⟨hxU, h.H_normalizes_V₁ (hUgH hxU), fun d hd => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hxc d hd
      have e : x * d * x⁻¹ * d⁻¹ = 1 := by
        have : d * x = x * d := this
        rw [← this]; group
      rw [e]; exact V₁.one_mem
  refine ⟨?_, ?_, ?_, hcardA, ?_, lt_of_le_of_ne (centralizerMod_le_left _ _ _) hDgne⟩
  · unfold mIdx; rw [hda]
  · rw [hcMD, ← hDgEq]
  · rw [Subgroup.commutator_comm]; exact hDcomm
  · rw [inf_comm]; exact h5b

theorem F916_2 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)))
    (hle : mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ≤
      mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G))) :
    autOn (tildeOf V₁ (F8.Uγ Vp H (g : G))) (tildeOf V₁ (conjClosure Vp H)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure Vp H))
          (commGroupOfElemAbelian h.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) ∧
      (2 * mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
          mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) (F8.Uγ Vp H (g : G))) →
        mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
            mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∧
          centralizerMod V₁ (F8.Uγ Vp H (g : G)) (F8.DH Vp V₁ H (g : G)) =
            F8.Dγ Vp V₁ H (g : G) ∧
          ⁅F8.Uγ Vp H (g : G), F8.DH Vp V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) ∧
          Nat.card (F8.A₁ V₁ (g : G)) = 2 ∧ F8.A₁ V₁ (g : G) ⊓ V₁ = ⊥ ∧
          F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G)) := by
  obtain ⟨hq, hr⟩ := h.F916_2_aux s hpos hle
  exact ⟨h.toHypF91.mem_Qset_of_qcrit hq, hr⟩

theorem exists_F8Setup_of_critical (h : HypF98 T V L V₁ Vp H) {γ : F8.Geom T L H}
    (hγ : IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V γ) :
    ∃ (γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g := by
  have hyp := h.amalgamHypV
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  have hodd : Odd (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V) := h.three_le_b_and_odd.2
  obtain ⟨⟨γ', hγ'nb, hd'⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega)
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  have hadj : (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj γ γ' := SimpleGraph.Adj.symm hγ'nb
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hadj
  · exfalso
    have := congrArg vtype hg0
    rw [vtype_smul, vtype_γ₀, hvt] at this
    exact absurd this (by decide)
  · exact ⟨γ', g, ⟨hγ, hγ'nb, hd', hg0, hg1⟩⟩

theorem not_Vγ_le_ballStab_of_lt (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hlt : F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G)) :
    ¬ F8.Uγ V H (g : G) ≤ ballStab 1 (F8.γ₁ T L H) := by
  intro hle
  have h15 := h.F915_2 s
  rw [inf_eq_left.mpr hle] at h15
  refine absurd hlt (not_lt_of_ge fun x hx => ?_)
  have hxE : x ∈ F9.Eγ V Vp V₁ H (g : G) := h15 ▸ h.Uγ_le_Vγ hx
  exact ⟨hx, hxE.2.1, hxE.2.2⟩

theorem exists_nbr_not_le_ballStab (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hn : ¬ F8.Uγ V H (g : G) ≤ ballStab 1 (F8.γ₁ T L H)) :
    ∃ β ∈ nbrs γ, ¬ Vv V β ≤ ballStab 1 (F8.γ₁ T L H) := by
  by_contra hall
  push Not at hall
  apply hn
  rw [h.Vγ_eq_Vv s]
  obtain ⟨y, hy⟩ : ∃ y, γ = Sum.inr y := ⟨(g : ↥((L ⊔ T) ⊔ H) ⧸ H.subgroupOf _), by
    rw [← s.edge₁, smul_γ₁]⟩
  rw [hy, Vv_inr]
  refine iSup₂_le fun x hx => ?_
  have := hall (Sum.inl x) (by rw [hy]; exact hx)
  exact this

theorem dist_eq_of_not_le_ballStab (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    {β : F8.Geom T L H} (hβ : β ∈ nbrs γ)
    (hnl : ¬ Vv V β ≤ ballStab 1 (F8.γ₁ T L H)) :
    CosetGeom.dist β (F8.γ₁ T L H) = F8.b T V L H := by
  have hyp := h.amalgamHypV
  have hV := h.V_ne_bot
  have hvtγ : vtype γ = true := by rw [← s.edge₁, vtype_smul, vtype_γ₁]
  have hvtβ : vtype β = false := by
    have := vtype_ne_of_adj (show (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj γ β from hβ)
    rw [hvtγ] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := exists_smul_eq_γ₀ hvtβ
  have hVβ : Vv V β = conjSub (x : G) V := by rw [hx, Vv_smul_γ₀ hyp.normalizes]
  have hnl' : ¬ V ≤ ballStab 1 (x⁻¹ • F8.γ₁ T L H) := by
    intro hle
    apply hnl
    rw [hVβ]
    have := conjSub_mono (x : G) hle
    rwa [← ballStab_smul, smul_inv_smul] at this
  have hb : F8.b T V L H ≤ CosetGeom.dist β (F8.γ₁ T L H) := by
    have hmem : CosetGeom.dist (F8.γ₀ T L H) (x⁻¹ • F8.γ₁ T L H) ∈
        {n : ℕ | ∃ γ ∈ sphere n (F8.γ₀ T L H), ¬ V ≤ ballStab 1 γ} :=
      ⟨x⁻¹ • F8.γ₁ T L H, rfl, hnl'⟩
    have := (isLeast_critDist hyp hV).2 hmem
    have hd := dist_smul x (F8.γ₀ T L H) (x⁻¹ • F8.γ₁ T L H)
    rw [smul_inv_smul, ← hx] at hd
    rw [← hd] at this
    exact this
  have hle : CosetGeom.dist β (F8.γ₁ T L H) ≤ F8.b T V L H := by
    have t := dist_triangle hyp.gen β γ (F8.γ₁ T L H)
    have d1 : CosetGeom.dist β γ = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hβ
    have d2 : CosetGeom.dist γ (F8.γ₁ T L H) + 1 = F8.b T V L H := by
      rw [CosetGeom.dist_comm]; exact s.critical.geodesic
    omega
  exact le_antisymm hle hb

theorem exists_symmetric_setup (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hn : ¬ F8.Uγ V H (g : G) ≤ ballStab 1 (F8.γ₁ T L H)) :
    ∃ (δ δ' : F8.Geom T L H) (k y : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H δ δ' k ∧
      y • γ = F8.γ₁ T L H ∧ y • F8.γ₁ T L H = δ ∧
      F8.Uγ Vp H (k : G) = conjSub (y : G) (conjClosure Vp H) ∧
      conjSub (y : G) (F8.Uγ Vp H (g : G)) = conjClosure Vp H ∧
      F8.DH Vp V₁ H (k : G) = conjSub (y : G) (F8.Dγ Vp V₁ H (g : G)) ∧
      F8.Dγ Vp V₁ H (k : G) = conjSub (y : G) (F8.DH Vp V₁ H (g : G)) := by
  have hyp := h.amalgamHypV
  have hvtγ : vtype γ = true := by rw [← s.edge₁, vtype_smul, vtype_γ₁]
  obtain ⟨β, hβ, hnl⟩ := h.exists_nbr_not_le_ballStab s hn
  have hdβ := h.dist_eq_of_not_le_ballStab s hβ hnl
  have hadj : (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj β γ := SimpleGraph.Adj.symm hβ
  obtain ⟨x, ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩⟩ := exists_smul_edge hadj
  swap
  · exfalso
    have := congrArg vtype hx0
    rw [vtype_smul, vtype_γ₀, hvtγ] at this
    exact absurd this (by decide)
  have hyγ : x⁻¹ • γ = F8.γ₁ T L H := by rw [← hx1, inv_smul_smul]
  have hcrit : IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V (x⁻¹ • F8.γ₁ T L H) := by
    refine ⟨?_, ?_, ?_⟩
    · have hd := dist_smul x (F8.γ₀ T L H) (x⁻¹ • F8.γ₁ T L H)
      rw [hx0, smul_inv_smul] at hd
      exact hd.symm.trans hdβ
    · intro hle
      apply hnl
      rw [← hx0, Vv_smul_γ₀ hyp.normalizes]
      have := conjSub_mono (x : G) hle
      rwa [← ballStab_smul, smul_inv_smul] at this
    · have hd := dist_smul x (F8.γ₁ T L H) (x⁻¹ • F8.γ₁ T L H)
      rw [hx1, smul_inv_smul] at hd
      have := s.critical.geodesic
      rw [CosetGeom.dist_comm] at hd
      rw [← hd]; exact this
  obtain ⟨δ', k, sk⟩ := h.exists_F8Setup_of_critical hcrit
  refine ⟨x⁻¹ • F8.γ₁ T L H, δ', k, x⁻¹, sk, hyγ, rfl, ?_⟩
  have hk₁ : (((x⁻¹ * g : ↥((L ⊔ T) ⊔ H)) : ↥((L ⊔ T) ⊔ H)) : G) ∈ H := by
    have h1 : (x⁻¹ * g) • F8.γ₁ T L H = F8.γ₁ T L H := by
      rw [mul_smul, s.edge₁, hyγ]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₁ hyp.le₂] at this
  have hk₂ : (((k⁻¹ * x⁻¹ : ↥((L ⊔ T) ⊔ H)) : ↥((L ⊔ T) ⊔ H)) : G) ∈ H := by
    have h1 : (k⁻¹ * x⁻¹) • F8.γ₁ T L H = F8.γ₁ T L H := by
      rw [mul_smul, ← sk.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₁ hyp.le₂] at this
  have hk₁' : ((x : G))⁻¹ * (g : G) ∈ H := by simpa using hk₁
  have hk₂' : ((k : G))⁻¹ * ((x : G))⁻¹ ∈ H := by simpa using hk₂
  have hxy : ((x⁻¹ : ↥((L ⊔ T) ⊔ H)) : G) = (x : G)⁻¹ := rfl
  rw [hxy]
  have eU : conjSub (x : G)⁻¹ (conjClosure Vp H) = F8.Uγ Vp H (k : G) := by
    have e : (x : G)⁻¹ = (k : G) * ((k : G)⁻¹ * (x : G)⁻¹) := by group
    rw [F8.Uγ, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (le_normalizer_conjClosure Vp H hk₂')]
  have eV : conjSub (x : G)⁻¹ V₁ = conjSub (k : G) V₁ := by
    have e : (x : G)⁻¹ = (k : G) * ((k : G)⁻¹ * (x : G)⁻¹) := by group
    rw [e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ hk₂')]
  have eB : conjSub (x : G)⁻¹ (F8.Uγ Vp H (g : G)) = conjClosure Vp H := by
    rw [F8.Uγ, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (le_normalizer_conjClosure Vp H hk₁')]
  have eA : conjSub (x : G)⁻¹ (F8.A₁ V₁ (g : G)) = V₁ := by
    rw [F8.A₁, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ hk₁')]
  refine ⟨eU.symm, eB, ?_, ?_⟩
  ·
    rw [F8.DH, F8.Dγ, conjSub_centralizerMod, eB, ← eU, eV]
    rfl
  · rw [F8.Dγ, F8.DH, conjSub_centralizerMod, eA, eB, ← eU]

theorem conjSub_inv_V_le_pCoreOf_L₁T (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    {W : Subgroup G} (hW : W ≤ conjClosure V H) :
    conjSub (g : G)⁻¹ W ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) := by
  have h1 := (h.F913_2 s).1
  have hstab : stab γ' ⊓ stab γ = conjSub (g : G) (L₁Of L V₁ ⊔ T) := by
    rw [← s.edge₁, ← s.edge₀, stab_smul, stab_smul, ← conjSub_inf, h.F913_1]
  rw [hstab, pCoreOf_conjSub] at h1
  exact (le_conjSub_iff (g : G)).mp (hW.trans h1)

theorem exists_qcrit_of_transvection (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    {W : Subgroup G} (hW : IsElemAbelian 2 W) (hV₁W : V₁ ≤ W) (hWV : W ≤ conjClosure V H)
    (hcomm : ⁅W, F8.Uγ Vp H (g : G)⁆ = V₁) :
    conjSub (g : G)⁻¹ W ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧ QCrit V₁ Vp H (conjSub (g : G)⁻¹ W) := by
  have hBL := h.conjSub_inv_V_le_pCoreOf_L₁T s hWV
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hBH : conjSub (g : G)⁻¹ W ≤ H :=
    hBL.trans ((pCoreOf_le 2 _).trans h.L₁T_le_H)
  have hUab := h.F911_3
  have hBel := isElemAbelian_conjSub (g := (g : G)⁻¹) hW
  have hcardV₁' : Nat.card (conjSub (g : G)⁻¹ V₁) = 2 := (card_conjSub _ _).trans h.card_V₁
  have hUconj : conjSub (g : G)⁻¹ (F8.Uγ Vp H (g : G)) = conjClosure Vp H := by
    rw [F8.Uγ, conjSub_conjSub_inv]
  have hBU : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ = conjSub (g : G)⁻¹ V₁ := by
    rw [← hUconj, conjSub_commutator, hcomm]
  have hV₁'inf : conjSub (g : G)⁻¹ V₁ ⊓ V₁ = ⊥ := by
    have h5b := h.F913_5b s
    have := congrArg (conjSub (g : G)⁻¹) h5b
    rw [conjSub_inf, conjSub_bot] at this
    have e : conjSub (g : G)⁻¹ (F8.A₁ V₁ (g : G)) = V₁ := by
      rw [F8.A₁, conjSub_conjSub_inv]
    rwa [e] at this
  have hV₁'B : conjSub (g : G)⁻¹ V₁ ≤ conjSub (g : G)⁻¹ W := conjSub_mono _ hV₁W
  have hBUU : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ ≤ conjClosure Vp H := by
    refine Subgroup.commutator_le.mpr fun b hb u hu => ?_
    have hbH := hBH hb
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hbH) u).mp hu
    show b * u * b⁻¹ * u⁻¹ ∈ conjClosure Vp H
    exact (conjClosure Vp H).mul_mem (by simpa using this) ((conjClosure Vp H).inv_mem hu)
  refine ⟨hBL, hBH, hBel, ?_, ?_, ?_⟩
  ·
    intro hle
    have h1 : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun b hb u hu => ?_
      have := V₁.inv_mem (h.commutator_conjClosure_le u hu b (hle hb))
      have e : (u * b * u⁻¹ * b⁻¹)⁻¹ = b * u * b⁻¹ * u⁻¹ := by group
      rwa [e] at this
    rw [hBU] at h1
    have : conjSub (g : G)⁻¹ V₁ = ⊥ := le_bot_iff.mp (hV₁'inf ▸ le_inf le_rfl h1)
    have h2 : Nat.card (conjSub (g : G)⁻¹ V₁) = 1 := by rw [this]; simp
    omega
  ·
    intro b₁ hb₁ b₂ hb₂ u hu
    have hc0 : b₁ * u * b₁⁻¹ * u⁻¹ ∈ conjSub (g : G)⁻¹ W := by
      have := Subgroup.commutator_mem_commutator hb₁ hu
      rw [hBU] at this
      exact hV₁'B this
    have := isElemAbelian_comm hBel hb₂ hc0
    have e : b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ = 1 := by
      rw [this]; group
    rw [e]; exact V₁.one_mem
  ·
    have hCU : conjSub (g : G)⁻¹ V₁ ≤ conjClosure Vp H := by
      rw [← hBU]; exact hBUU
    have hpair := relIndex_eq_of_commutator_le (X := conjSub (g : G)⁻¹ W)
      (Y := conjClosure Vp H) hUab hcardV₁' hBU.le
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (isElemAbelian_comm hBel (hV₁'B ha) hb).symm)
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (isElemAbelian_comm hUab (hCU ha) hu).symm)
    have hcM : centralizerMod V₁ (conjClosure Vp H) (conjSub (g : G)⁻¹ W) =
        conjClosure Vp H ⊓ Subgroup.centralizer (conjSub (g : G)⁻¹ W : Set G) := by
      ext x
      constructor
      · rintro ⟨hxU, hxN, hxc⟩
        refine ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
        have h1 := hxc b hb
        have h2 : x * b * x⁻¹ * b⁻¹ ∈ conjSub (g : G)⁻¹ V₁ := by
          have := Subgroup.commutator_mem_commutator hxU hb
          rwa [Subgroup.commutator_comm, hBU] at this
        have h3 : x * b * x⁻¹ * b⁻¹ ∈ conjSub (g : G)⁻¹ V₁ ⊓ V₁ := ⟨h2, h1⟩
        rw [hV₁'inf, Subgroup.mem_bot] at h3
        calc b * x = (x * b * x⁻¹ * b⁻¹)⁻¹ * (x * b) := by group
          _ = x * b := by rw [h3]; group
      · rintro ⟨hxU, hxc⟩
        refine ⟨hxU, h.H_normalizes_V₁ (hUH hxU), fun b hb => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp hxc b hb
        have e : x * b * x⁻¹ * b⁻¹ = 1 := by rw [← this]; group
        rw [e]; exact V₁.one_mem
    have hQC : conjSub (g : G)⁻¹ W ⊓ pCoreOf 2 H =
        conjSub (g : G)⁻¹ W ⊓ Subgroup.centralizer (conjClosure Vp H : Set G) := by
      ext b
      constructor
      · rintro ⟨hb, hbQ⟩
        refine ⟨hb, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
        have hbQ' := (h.toHypF91.pCoreOf_eq_centralizerMod ▸ hbQ : b ∈ centralizerMod V₁ H
          (conjClosure Vp H))
        have h1 := hbQ'.2.2 u hu
        have h2 : b * u * b⁻¹ * u⁻¹ ∈ conjSub (g : G)⁻¹ V₁ := by
          have := Subgroup.commutator_mem_commutator hb hu
          rwa [hBU] at this
        have h3 : b * u * b⁻¹ * u⁻¹ ∈ conjSub (g : G)⁻¹ V₁ ⊓ V₁ := ⟨h2, h1⟩
        rw [hV₁'inf, Subgroup.mem_bot] at h3
        calc u * b = (b * u * b⁻¹ * u⁻¹)⁻¹ * (b * u) := by group
          _ = b * u := by rw [h3]; group
      · rintro ⟨hb, hbc⟩
        refine ⟨hb, ?_⟩
        rw [h.toHypF91.pCoreOf_eq_centralizerMod]
        refine ⟨hBH hb, h.H_normalizes_V₁ (hBH hb), fun u hu => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp hbc u hu
        have e : b * u * b⁻¹ * u⁻¹ = 1 := by rw [← this]; group
        rw [e]; exact V₁.one_mem
    rw [hcM, hQC, ← hpair]
    exact Nat.le_self_pow (by norm_num) _

theorem mIdx_pos_of_lt (h : HypF98 T V L V₁ Vp H)
    (hlt : F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G)) :
    0 < mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) := by
  have hp : IsPGroup 2 (F8.Uγ Vp H (g : G)) := isPGroup_of_isElemAbelian h.isElemAbelian_Uγ
  have h1 := relIndex_eq_two_pow_mIdx (Y := F8.Dγ Vp V₁ H (g : G)) hp
  have h2 : (F8.Dγ Vp V₁ H (g : G)).relIndex (F8.Uγ Vp H (g : G)) ≠ 1 := fun e =>
    absurd (Subgroup.relIndex_eq_one.mp e) (not_le_of_gt hlt)
  rcases Nat.eq_zero_or_pos (mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G))) with h0 | h0
  · exact absurd (by rw [h1, h0]; rfl) h2
  · exact h0

theorem exists_setup_of_lt (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hlt : F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G)) :
    ∃ (δ δ' : F8.Geom T L H) (k : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H δ δ' k ∧
      0 < mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) ∧
      mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) ≤
        mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) := by
  by_cases hc : mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ≤
      mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G))
  · exact ⟨γ, γ', g, s, h.mIdx_pos_of_lt hlt, hc⟩
  · obtain ⟨δ, δ', k, y, sk, -, -, eU, eB, eDH, eDγ⟩ :=
      h.exists_symmetric_setup s (h.not_Vγ_le_ballStab_of_lt s hlt)
    have m1 : mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) =
        mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) := by
      rw [eU, eDγ, F9.mIdx_conjSub]
    have m2 : mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) =
        mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) := by
      rw [eDH, ← eB, F9.mIdx_conjSub]
    refine ⟨δ, δ', k, sk, ?_, ?_⟩
    · rw [m1]; omega
    · rw [m2, m1]; omega

theorem F916_4 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hlt : F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G)) :
    ∃ (δ δ' : F8.Geom T L H) (k : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H δ δ' k ∧
      0 < mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) ∧
      mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) ≤
        mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) ∧
      autOn (tildeOf V₁ (F8.Uγ Vp H (k : G))) (tildeOf V₁ (conjClosure Vp H)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure Vp H))
          (commGroupOfElemAbelian h.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) := by
  obtain ⟨δ, δ', k, sk, hpos, hle⟩ := h.exists_setup_of_lt s hlt
  exact ⟨δ, δ', k, sk, hpos, hle, (h.F916_2 sk hpos hle).1⟩

theorem F916_3_aux (h : HypF98 T V L V₁ Vp H) :
    ∃ B : Subgroup G, B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧ QCrit V₁ Vp H B := by
  obtain ⟨γ, γ', g, s⟩ := h.exists_F8Setup
  have hUV : conjClosure Vp H ≤ conjClosure V H := conjClosure_mono h.Vp_le_V le_rfl
  by_cases hD : F8.Uγ Vp H (g : G) = F8.Dγ Vp V₁ H (g : G)
  · rcases h.F916_1 s hD with ⟨-, -, -, hT⟩ | ⟨-, -, -, -, hT⟩
    · obtain ⟨hBL, hq⟩ := h.exists_qcrit_of_transvection s h.F911_3
        (h.V₁_le_Vp.trans (le_conjClosure Vp H)) hUV hT
      exact ⟨_, hBL, hq⟩
    · obtain ⟨hBL, hq⟩ := h.exists_qcrit_of_transvection s h.elemAbelian h.V₁_le_V
        (le_conjClosure V H) hT
      exact ⟨_, hBL, hq⟩
  · have hlt : F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G) :=
      lt_of_le_of_ne (centralizerMod_le_left _ _ _) (Ne.symm hD)
    obtain ⟨δ, δ', k, sk, hpos, hle⟩ := h.exists_setup_of_lt s hlt
    have hq := (h.F916_2_aux sk hpos hle).1
    have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
    obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
      exists_nbrs_of_geodesic h.amalgamHypV.gen sk.critical.geodesic (by omega : 2 ≤ _)
    have hV2 := (h.F913_2 sk).2 γ₂ hγ₂nb hd
    obtain ⟨c, hc, hcγ⟩ := stab_transitive_on_nbrs hγ₂nb
      (show F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) from (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H)).symm)
    have hcH : (c : G) ∈ H := by rwa [stab_γ₁ h.amalgamHypV.le₂] at hc
    have hc1 : c • F8.γ₁ T L H = F8.γ₁ T L H := smul_eq_of_mem_stab hc
    refine ⟨conjSub (c : G) (F8.Uγ Vp H (k : G)), ?_, h.toHypF91.qcrit_conj hq hcH⟩
    have h1 := conjSub_mono (c : G) (h.Uγ_le_Vγ.trans hV2)
    rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hc1, hcγ,
      inf_comm, h.F913_1] at h1
    exact h1

theorem F916_3 (h : HypF98 T V L V₁ Vp H) :
    qInt (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) h.toHypF91.isElemAbelian_tilde ≤ 2 ∧
      ∃ B : Subgroup G, B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧
        autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
          @Qset ↥(tildeOf V₁ (conjClosure Vp H))
            (commGroupOfElemAbelian h.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) := by
  obtain ⟨B, hBL, hq⟩ := h.F916_3_aux
  have hmem := h.toHypF91.mem_Qset_of_qcrit hq
  exact ⟨h.toHypF91.qInt_tilde_le_two_of_mem hmem, B, hBL, hmem⟩

end HypF98

end Fin