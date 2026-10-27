module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.MS93.ASC134
public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Quasithin.Vol2.Ch4Sec3C135H1
public import CFSG.Quasithin.Vol2.Ch4Sec3C136One

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open CFSG.Quasithin.H13.Ch4.C135 (slNat dualHom coe_slNat coe_dualHom moduleAct_false_eq
  moduleAct_true_eq dualHom_dualHom)

variable {G : Type} [Group G]

section Layers

@[expose] def burnsideC135_layerSub (F : Type) [Field F] (k j : ℕ) :
    Subgroup (Multiplicative (Fin k → Fin 3 → F)) where
  carrier := {x | ∀ i : Fin k, j ≤ (i : ℕ) → Multiplicative.toAdd x i = 0}
  mul_mem' := by
    intro x y hx hy i hi
    simp only [Set.mem_setOf_eq] at hx hy
    rw [toAdd_mul, Pi.add_apply, hx i hi, hy i hi, add_zero]
  one_mem' := by
    intro i _
    rfl
  inv_mem' := by
    intro x hx i hi
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [toAdd_inv, Pi.neg_apply, hx i hi, neg_zero]

@[expose] def burnsideC135_layer {V : Subgroup G} {F : Type} [Field F] {k : ℕ}
    (β : ↥V →* Multiplicative (Fin k → Fin 3 → F)) (j : ℕ) : Subgroup G :=
  ((burnsideC135_layerSub F k j).comap β).map V.subtype

variable {V : Subgroup G} {F : Type} [Field F] {k : ℕ}
  {β : ↥V →* Multiplicative (Fin k → Fin 3 → F)}

theorem burnsideC135_mem_layer {j : ℕ} {g : G} :
    g ∈ burnsideC135_layer β j ↔ ∃ h : g ∈ V, ∀ i : Fin k, j ≤ (i : ℕ) →
      Multiplicative.toAdd (β ⟨g, h⟩) i = 0 := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨h, hv⟩
    exact ⟨⟨g, h⟩, hv, rfl⟩

theorem burnsideC135_layer_le (j : ℕ) : burnsideC135_layer β j ≤ V := fun _ hg =>
  (burnsideC135_mem_layer.mp hg).1

theorem burnsideC135_layer_zero {Z : Subgroup G} (hZV : Z ≤ V) (hker : β.ker = Z.subgroupOf V) :
    burnsideC135_layer β 0 = Z := by
  ext g
  rw [burnsideC135_mem_layer]
  constructor
  · rintro ⟨h, hv⟩
    have h1 : (⟨g, h⟩ : ↥V) ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      exact hv i (Nat.zero_le _)
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro hg
    refine ⟨hZV hg, fun i _ => ?_⟩
    have h1 : (⟨g, hZV hg⟩ : ↥V) ∈ β.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hg
    rw [MonoidHom.mem_ker] at h1
    rw [h1]
    rfl

theorem burnsideC135_layer_top : burnsideC135_layer β k = V := by
  refine le_antisymm (burnsideC135_layer_le k) fun g hg => ?_
  rw [burnsideC135_mem_layer]
  exact ⟨hg, fun i hi => absurd i.2 (not_lt.mpr hi)⟩

theorem burnsideC135_layer_mono {j j' : ℕ} (hjj : j ≤ j') :
    burnsideC135_layer β j ≤ burnsideC135_layer β j' := by
  intro g hg
  obtain ⟨h, hv⟩ := burnsideC135_mem_layer.mp hg
  exact burnsideC135_mem_layer.mpr ⟨h, fun i hi => hv i (hjj.trans hi)⟩

variable {L U : Subgroup G} {ρ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}

theorem burnsideC135_isNormalIn_layer (hVU : V ≤ U) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hβeq : ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((ρ a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i))
    (j : ℕ) : IsNormalIn L U (burnsideC135_layer β j) := by
  refine ⟨(burnsideC135_layer_le j).trans hVU, fun a ha g hg => ?_⟩
  obtain ⟨h, hv⟩ := burnsideC135_mem_layer.mp hg
  have hmem : a * g * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV ha) g).mp h
  refine burnsideC135_mem_layer.mpr ⟨hmem, fun i hi => ?_⟩
  rw [hβeq ⟨a, ha⟩ ⟨g, h⟩ ⟨_, hmem⟩ rfl i, hv i hi, Matrix.mulVec_zero]

theorem burnsideC135_isChiefStep_layer (hVU : V ≤ U) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hρ : Function.Surjective ρ) (hβ : Function.Surjective β)
    (hβeq : ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((ρ a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i))
    {j : ℕ} (hj : j < k) :
    IsChiefStep L U (burnsideC135_layer β j) (burnsideC135_layer β (j + 1)) ∧
      ¬ IsCentralStep L (burnsideC135_layer β j) (burnsideC135_layer β (j + 1)) := by
  classical
  set J : Fin k := ⟨j, hj⟩ with hJ
  set e₀ : Fin 3 → F := Pi.single 0 1 with he₀
  have he₀ne : e₀ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he₀] at this
  obtain ⟨x, hx⟩ := hβ (Multiplicative.ofAdd (Pi.single J e₀ : Fin k → Fin 3 → F))
  have hxc : ∀ i : Fin k, Multiplicative.toAdd (β x) i = (Pi.single J e₀ : Fin k → Fin 3 → F) i := by
    intro i
    rw [hx]
    rfl
  have hxj1 : (x : G) ∈ burnsideC135_layer β (j + 1) := by
    refine burnsideC135_mem_layer.mpr ⟨x.2, fun i hi => ?_⟩
    rw [hxc]
    have hne : i ≠ J := by
      intro h
      rw [h] at hi
      simp [hJ] at hi
    exact Pi.single_eq_of_ne hne _
  have hxj : (x : G) ∉ burnsideC135_layer β j := by
    intro h
    obtain ⟨h', hv⟩ := burnsideC135_mem_layer.mp h
    have := hv J le_rfl
    rw [show (⟨(x : G), h'⟩ : ↥V) = x from rfl, hxc, Pi.single_eq_same] at this
    exact he₀ne this
  refine ⟨⟨burnsideC135_isNormalIn_layer hVU hLV hβeq (j + 1),
    burnsideC135_isNormalIn_layer hVU hLV hβeq j,
    lt_of_le_of_ne (burnsideC135_layer_mono (Nat.le_succ j)) fun h => hxj (h ▸ hxj1), ?_⟩, ?_⟩
  · intro K hK hjK hKj
    let X : AddSubgroup (Fin 3 → F) :=
      { carrier := {y | ∃ g : ↥V, (g : G) ∈ K ∧ Multiplicative.toAdd (β g) J = y}
        add_mem' := by
          rintro _ _ ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩
          exact ⟨g₁ * g₂, K.mul_mem hg₁ hg₂, by rw [map_mul, toAdd_mul, Pi.add_apply]⟩
        zero_mem' := ⟨1, K.one_mem, by rw [map_one]; rfl⟩
        neg_mem' := by
          rintro _ ⟨g, hg, rfl⟩
          exact ⟨g⁻¹, K.inv_mem hg, by rw [map_inv, toAdd_inv, Pi.neg_apply]⟩ }
    have hXinv : ∀ (i i' : Fin 3) (hii : i ≠ i') (b : F) (y : Fin 3 → F), y ∈ X →
        (Matrix.SpecialLinearGroup.transvection hii b : Matrix (Fin 3) (Fin 3) F).mulVec y ∈ X := by
      rintro i i' hii b _ ⟨g, hg, rfl⟩
      obtain ⟨a, ha⟩ := hρ (Matrix.SpecialLinearGroup.transvection hii b)
      have hmem : (a : G) * g * (a : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV a.2) g).mp g.2
      refine ⟨⟨_, hmem⟩, hK.2 a a.2 g hg, ?_⟩
      rw [hβeq a g ⟨_, hmem⟩ rfl J, ha]
    by_cases hX : ∃ y ∈ X, y ≠ 0
    · obtain ⟨y, hyX, hy0⟩ := hX
      have htop := CFSG.Quasithin.H13.Ch4.eq_top_of_transvection_invariant X hXinv hyX hy0
      right
      refine le_antisymm hKj fun g hg => ?_
      obtain ⟨h, hv⟩ := burnsideC135_mem_layer.mp hg
      have hyX' : Multiplicative.toAdd (β ⟨g, h⟩) J ∈ X := by
        rw [htop]
        exact AddSubgroup.mem_top _
      obtain ⟨g', hg'K, hg'⟩ := hyX'
      have hg'1 := burnsideC135_mem_layer.mp (hKj hg'K)
      have hdiff : g * (g' : G)⁻¹ ∈ burnsideC135_layer β j := by
        refine burnsideC135_mem_layer.mpr ⟨V.mul_mem h (V.inv_mem g'.2), fun i hi => ?_⟩
        have e : (⟨g * (g' : G)⁻¹, V.mul_mem h (V.inv_mem g'.2)⟩ : ↥V) = ⟨g, h⟩ * g'⁻¹ := rfl
        rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
        rcases eq_or_lt_of_le hi with hij | hij
        · have hiJ : i = J := Fin.ext hij.symm
          rw [hiJ, hg']
          abel
        · obtain ⟨h'', hv''⟩ := hg'1
          rw [hv i hij, show g' = ⟨(g' : G), h''⟩ from rfl, hv'' i hij, neg_zero, add_zero]
      have := K.mul_mem (hjK hdiff) hg'K
      rwa [inv_mul_cancel_right] at this
    · push Not at hX
      left
      refine le_antisymm (fun g hg => ?_) hjK
      obtain ⟨h, hv⟩ := burnsideC135_mem_layer.mp (hKj hg)
      refine burnsideC135_mem_layer.mpr ⟨h, fun i hi => ?_⟩
      rcases eq_or_lt_of_le hi with hij | hij
      · have hiJ : i = J := Fin.ext hij.symm
        rw [hiJ]
        exact hX _ ⟨⟨g, h⟩, hg, rfl⟩
      · exact hv i hij
  ·
    intro hcent
    have h01 : (1 : Fin 3) ≠ 0 := by decide
    obtain ⟨a, ha⟩ := hρ (Matrix.SpecialLinearGroup.transvection h01 (1 : F))
    have hc := hcent a a.2 x hxj1
    obtain ⟨h, hv⟩ := burnsideC135_mem_layer.mp hc
    have hmem : (a : G) * x * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV a.2) x).mp x.2
    have e : (⟨(a : G) * x * (a : G)⁻¹ * (x : G)⁻¹, h⟩ : ↥V) = ⟨_, hmem⟩ * x⁻¹ := rfl
    have h1 := hv J le_rfl
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply,
      hβeq a x ⟨_, hmem⟩ rfl J, ha, hxc, Pi.single_eq_same,
      CFSG.Quasithin.H13.Ch4.transvection_mulVec] at h1
    have h2 := congrFun h1 1
    simp [he₀] at h2

theorem burnsideC135_isChiefSeriesBetween_of_coords {Z : Subgroup G} (hVU : V ≤ U)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V)
    (hρ : Function.Surjective ρ) (hβ : Function.Surjective β) (hker : β.ker = Z.subgroupOf V)
    (hβeq : ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((ρ a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i)) :
    F112W.IsChiefSeriesBetween L U Z V k := by
  have key : ∀ j, j ≤ k → F112W.IsChiefSeriesBetween L U Z (burnsideC135_layer β j) j := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [burnsideC135_layer_zero hZV hker]
      exact .refl
    | succ j ih =>
      intro hj
      obtain ⟨hstep, hnc⟩ := burnsideC135_isChiefStep_layer hVU hLV hρ hβ hβeq (j := j) hj
      exact .noncentral hstep hnc (ih (Nat.le_of_succ_le hj))
  have := key k le_rfl
  rwa [burnsideC135_layer_top] at this

end Layers

section Sums

variable {L U V Z : Subgroup G} {F : Type} [Field F]

theorem burnsideC135_dualHom_surjective : Function.Surjective (dualHom (F := F)) :=
  fun γ => ⟨dualHom γ, dualHom_dualHom γ⟩

theorem burnsideC135_slNat_surjective {K : Type*} [Group K] {α : K →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) : Function.Surjective (slNat α) := by
  intro γ
  obtain ⟨g, hg⟩ := hα (specialLinearGroupEquivStatedSL 3 F γ)
  refine ⟨g, ?_⟩
  simp only [slNat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hg, MulEquiv.symm_apply_apply]

theorem burnsideC135_isChiefSeriesBetween_of_sum {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) {dual : Bool} {k : ℕ}
    (hN : IsSumOfNaturalModulesVia L V Z α dual k) (hVU : V ≤ U) :
    F112W.IsChiefSeriesBetween L U Z V k := by
  obtain ⟨hLV, hZV, β, hβ, hker, hβeq⟩ := hN
  cases dual with
  | false =>
    refine burnsideC135_isChiefSeriesBetween_of_coords (ρ := slNat α) hVU hLV hZV
      (burnsideC135_slNat_surjective hα) hβ hker ?_
    intro a u v huv i
    rw [hβeq a u v huv i, moduleAct_false_eq]
  | true =>
    refine burnsideC135_isChiefSeriesBetween_of_coords (ρ := dualHom.comp (slNat α)) hVU hLV hZV
      (burnsideC135_dualHom_surjective.comp (burnsideC135_slNat_surjective hα)) hβ hker ?_
    intro a u v huv i
    rw [hβeq a u v huv i, moduleAct_true_eq]
    rfl

end Sums

section Cases

variable [Finite G]

@[expose] def burnsideC135_caseCount : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 6
  | _ => 1

variable {X R L : Subgroup G}

theorem burnsideC135_isNormalIn_c134Q (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) :
    IsNormalIn L (pCoreOf 2 L) (c134Q X L) :=
  F112W.isNormalIn_of_le_normalizer (MS93.commutator_le_pCoreOf hLX hXL)
    (hLX.trans (CFSG.Quasithin.H13.Ch4.le_normalizer_c134Q hXL))

theorem burnsideC135_isChiefSeriesFrom_pCoreOf (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L) {m : ℕ}
    (h : IsChiefSeriesFrom L (pCoreOf 2 L) (c134Q X L) m) :
    IsChiefSeriesFrom L (pCoreOf 2 L) (pCoreOf 2 L) m := by
  have hQU : c134Q X L ≤ pCoreOf 2 L := MS93.commutator_le_pCoreOf hLX hXL
  have h0 : F112W.IsChiefSeriesBetween L (pCoreOf 2 L) (c134Q X L) (pCoreOf 2 L) 0 := by
    refine (F112W.isChiefSeriesBetween_zero_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 L) le_rfl
      (burnsideC135_isNormalIn_c134Q hLX hXL)
      (F112W.isNormalIn_of_le_normalizer le_rfl
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)) hQU).mpr ?_
    calc ⁅pCoreOf 2 L, oTwoUpper L⁆ ≤ ⁅pCoreOf 2 L, L⁆ :=
          Subgroup.commutator_mono le_rfl (oTwoUpper_le L)
      _ = c134Q X L := (MS93.commutator_eq_blockU hLX hXL hperf).symm
  have := h0.append h
  rwa [zero_add] at this

theorem burnsideC135_chief_case4 (hLX : L ≤ X) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    {U : Subgroup G} (hQU' : c134Q X L ≤ U) (hUL : U ≤ L) (hUO : U ≤ pCoreOf 2 L)
    (hi : MS93.IsC134Case4Corr X R L) :
    IsChiefSeriesFrom L U (c134Q X L) 6 := by
  have hLQ : L ≤ Subgroup.normalizer (c134Q X L : Set G) :=
    hLX.trans (CFSG.Quasithin.H13.Ch4.le_normalizer_c134Q hXL)
  obtain ⟨⟨n, F, _, _, α, -, hα, -, hZeq, -, h1, h2, h3, h4⟩, -⟩ := hi
  set Q := c134Q X L with hQ
  have hQU : Q ≤ U := hQU'
  have hCQ : Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G) ≤ Q := h4.2.1
  have hΦ : frattiniIn Q ≤ Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G) := h3.2.1
  have hZΦ : centerOf Q ≤ frattiniIn Q := h2.2.1
  have hCZ : ⁅centerOf Q, L⁆ ≤ centerOf Q :=
    le_sup_right.trans (le_of_eq hZeq.symm)
  have hZU : centerOf Q ≤ U := hZΦ.trans (hΦ.trans (hCQ.trans hQU))
  have hLZ : L ≤ Subgroup.normalizer (centerOf Q : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgQ := Subgroup.mem_normalizer_iff.mp (hLQ hg)
    constructor
    · rintro ⟨hxQ, hxC⟩
      refine ⟨(hgQ x).mp hxQ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g ∈ Q := by
        have := (hgQ (g⁻¹ * y * g)).mp
        simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem hg)) y).mp hy
      have hc := Subgroup.mem_centralizer_iff.mp hxC _ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * y := by group
    · rintro ⟨hxQ, hxC⟩
      refine ⟨(hgQ x).mpr hxQ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : g * y * g⁻¹ ∈ Q := (hgQ y).mp hy
      have hc := Subgroup.mem_centralizer_iff.mp hxC _ hy'
      have : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
        calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * y * g⁻¹) := hc
          _ = g * (x * y) * g⁻¹ := by group
      simpa using this
  have e1 := F112W.isChiefSeriesFrom_of_between_bot
    (burnsideC135_isChiefSeriesBetween_of_sum hα.1 h1 (hCZ.trans hZU))
  have e0 : F112W.IsChiefSeriesBetween L U ⁅centerOf Q, L⁆ (centerOf Q) 0 := by
    refine (F112W.isChiefSeriesBetween_zero_iff hUL hUO
      (F112W.isNormalIn_of_le_normalizer (hCZ.trans hZU) h1.1)
      (F112W.isNormalIn_of_le_normalizer hZU hLZ) hCZ).mpr ?_
    exact Subgroup.commutator_mono le_rfl (oTwoUpper_le L)
  have e2 := (burnsideC135_isChiefSeriesBetween_of_sum hα.1 h2
    (hΦ.trans (hCQ.trans hQU))).append (e0.append e1)
  have e3 := (burnsideC135_isChiefSeriesBetween_of_sum hα.1 h3 (hCQ.trans hQU)).append e2
  exact (burnsideC135_isChiefSeriesBetween_of_sum hα.1 h4 hQU).append e3

theorem burnsideC135_chief_of_case (hLX : L ≤ X) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) {i : ℕ} (hi : MS93.IsC134CaseCorr i X R L) :
    IsChiefSeriesFrom L (pCoreOf 2 L) (pCoreOf 2 L) (burnsideC135_caseCount i) := by
  refine burnsideC135_isChiefSeriesFrom_pCoreOf hLX hXL hperf ?_
  have hQU : c134Q X L ≤ pCoreOf 2 L := MS93.commutator_le_pCoreOf hLX hXL
  have hLQ : L ≤ Subgroup.normalizer (c134Q X L : Set G) :=
    hLX.trans (CFSG.Quasithin.H13.Ch4.le_normalizer_c134Q hXL)
  match i, hi with
  | 1, hi =>
    obtain ⟨-, n, F, _, _, -, hnat⟩ := hi
    obtain ⟨α, hα, -, hN⟩ := (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hnat
    exact F112W.isChiefSeriesFrom_of_between_bot
      (burnsideC135_isChiefSeriesBetween_of_sum hα hN hQU)
  | 2, hi =>
    obtain ⟨⟨n, F, _, _, α, -, hα, hN⟩, -⟩ := hi
    exact F112W.isChiefSeriesFrom_of_between_bot
      (burnsideC135_isChiefSeriesBetween_of_sum hα.1 hN hQU)
  | 3, hi =>
    obtain ⟨⟨n, F, _, _, α, -, hα, h1, h2⟩, -⟩ := hi
    have hZQ : centerOf (c134Q X L) ≤ c134Q X L := h2.2.1
    have hZ := F112W.isChiefSeriesFrom_of_between_bot
      (burnsideC135_isChiefSeriesBetween_of_sum hα.1 h1 (hZQ.trans hQU))
    exact (burnsideC135_isChiefSeriesBetween_of_sum hα.1 h2 hQU).append hZ
  | 4, hi =>
    exact burnsideC135_chief_case4 hLX hXL hQU (CFSG.LieType.BorelTits.pCoreOf_le 2 L) le_rfl hi
  | 5, hi =>
    obtain ⟨⟨α, hα, -, hN⟩, -⟩ := hi
    have hCQ : c134CQ X L ≤ c134Q X L := hN.2.1
    have hCn : IsNormalIn L (pCoreOf 2 L) (c134CQ X L) := by
      refine ⟨hCQ.trans hQU, fun g hg x hx => ?_⟩
      have hxg : x * g = g * x := Subgroup.mem_centralizer_iff.mp hx.2 g hg |>.symm
      have : g * x * g⁻¹ = x := by
        calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hxg]
          _ = x := by group
      rw [this]
      exact hx
    have h0 : IsChiefSeriesFrom L (pCoreOf 2 L) (c134CQ X L) 0 := by
      refine (F112W.isChiefSeriesFrom_zero_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 L) le_rfl
        hCn).mpr ?_
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx g hg
      have hgL : g ∈ L := oTwoUpper_le L hg
      have hxg : x * g = g * x := (Subgroup.mem_centralizer_iff.mp hx.2 g hgL).symm
      rw [Subgroup.mem_bot, commutatorElement_def, hxg]
      group
    exact (burnsideC135_isChiefSeriesBetween_of_sum hα.1 hN hQU).append h0
  | 0, hi => exact hi.elim
  | (j + 6), hi => exact hi.elim

end Cases

section Weak

open scoped Pointwise

variable [Finite G]

@[expose] def burnsideC135_Case4W (G₀ R L : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      centerOf (c134Q G₀ L) = c134CQ G₀ L ⊔ ⁅centerOf (c134Q G₀ L), L⁆ ∧
      c134CQ G₀ L ⊓ ⁅centerOf (c134Q G₀ L), L⁆ = ⊥ ∧
      IsSumOfNaturalModulesVia L ⁅centerOf (c134Q G₀ L), L⁆ ⊥ α false 1) ∧
    C134NotCentralizerCore G₀ R ∧
    IsChiefSeriesFrom L (c134Q G₀ L) (c134Q G₀ L) 6

@[expose] def burnsideC135_C134W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, (i ≠ 4 ∧ MS93.IsC134CaseCorr i G₀ R L) ∨ (i = 4 ∧ burnsideC135_Case4W G₀ R L)

theorem burnsideC135_isChiefSeriesFrom_mono {L Q P N : Subgroup G} {m : ℕ} (hQP : Q ≤ P)
    (h : IsChiefSeriesFrom L Q N m) : IsChiefSeriesFrom L P N m := by
  have hstep : ∀ {L' N' : Subgroup G}, IsChiefStep L Q L' N' → IsChiefStep L P L' N' := by
    intro L' N' hs
    obtain ⟨hN, hL', hlt, hmax⟩ := hs
    exact ⟨⟨hN.1.trans hQP, hN.2⟩, ⟨hL'.1.trans hQP, hL'.2⟩, hlt,
      fun K hK hLK hKN => hmax K ⟨hKN.trans hN.1, hK.2⟩ hLK hKN⟩
  induction h with
  | bot => exact .bot
  | central hs hc _ ih => exact .central (hstep hs) hc ih
  | noncentral hs hc _ ih => exact .noncentral (hstep hs) hc ih

theorem burnsideC135_case4_weak {X R L : Subgroup G} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (h : MS93.IsC134Case4Corr X R L) :
    burnsideC135_Case4W X R L := by
  have hQ := burnsideC135_chief_case4 hLX hXL le_rfl
    ((MS93.commutator_le_pCoreOf hLX hXL).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
    (MS93.commutator_le_pCoreOf hLX hXL) h
  obtain ⟨⟨n, F, i₁, i₂, α, hF, hα, -, hZ, hD, h1, -, -, -⟩, hN⟩ := h
  exact ⟨⟨n, F, i₁, i₂, α, hF, hα, hZ, hD, h1⟩, hN, hQ⟩

theorem burnsideC135_c134W_of_corr (h : MS93.AS_C_1_34_corr) : burnsideC135_C134W := by
  intro G _ _ G₀ R L hMS hL hG hsl3
  obtain ⟨i, hi⟩ := h G G₀ R L hMS hL hG hsl3
  by_cases hi4 : i = 4
  · subst hi4
    have hLX : L ≤ G₀ := MS93.le_of_coe_eq_mul_left hG
    have hXL : G₀ ≤ Subgroup.normalizer (L : Set G) := by
      have h' := MS93.le_normalizer_oddGen G₀
      rwa [← MS93.isMSPair_eq_oddGen hMS hL hG] at h'
    exact ⟨4, Or.inr ⟨rfl, burnsideC135_case4_weak hLX hXL hi⟩⟩
  · exact ⟨i, Or.inl ⟨hi4, hi⟩⟩

theorem burnsideC135_chief_of_case4W {X R L : Subgroup G} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L)
    (h : burnsideC135_Case4W X R L) :
    IsChiefSeriesFrom L (pCoreOf 2 L) (pCoreOf 2 L) 6 :=
  burnsideC135_isChiefSeriesFrom_pCoreOf hLX hXL hperf
    (burnsideC135_isChiefSeriesFrom_mono (MS93.commutator_le_pCoreOf hLX hXL) h.2.2)

end Weak

end CFSG.ASVolI

end
