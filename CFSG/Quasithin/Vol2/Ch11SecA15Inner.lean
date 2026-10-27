module

public import CFSG.Quasithin.Vol2.Ch11SecA13Basic
public import CFSG.Quasithin.Vol2.Ch11SecA15Fix
public import CFSG.Quasithin.Vol2.Ch11SecA15Kill
public import CFSG.Quasithin.Vol2.Ch11SecA15Z1b
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_le {K : Subgroup G} {x : G} (h1 : ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (h2 : ∀ k ∈ K, x⁻¹ * k * x⁻¹⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h1 k, fun hk => ?_⟩
  have := h2 _ hk
  simpa [mul_assoc] using this

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem mem_pCoreOf_LT_of_conj (h : Hyp11 G T L I n) {c : G} (hcT : c ∈ T)
    (hc : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : c ∈ pCoreOf 2 (L ⊔ T) := by
  have hQN : ∀ t ∈ T, ∀ x ∈ pCoreOf 2 L, t * x * t⁻¹ ∈ pCoreOf 2 L := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (h.normal ht)) x).mp hx
  let D : Subgroup G :=
    { carrier := {t | t ∈ T ∧ ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 L}
      one_mem' := ⟨T.one_mem, fun l _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨T.mul_mem ha hb, fun l hl => ?_⟩
        have e : a * b * l * (a * b)⁻¹ * l⁻¹ =
            (a * (b * l * b⁻¹ * l⁻¹) * a⁻¹) * (a * l * a⁻¹ * l⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (hQN a ha _ (hb' l hl)) (ha' l hl)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨T.inv_mem ha, fun l hl => ?_⟩
        have e : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ = a⁻¹ * (a * l * a⁻¹ * l⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hQN _ (T.inv_mem ha) _ (Subgroup.inv_mem _ (ha' l hl)) }
  have hDT : D ≤ T := fun t ht => ht.1
  have hQT : pCoreOf 2 L ≤ T :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h)).trans inf_le_left
  have hle : D ⊔ pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((sup_le hDT hQT).trans le_sup_right) (sup_le ?_ ?_)
      ((h.fsu.sylow.1).to_le (sup_le hDT hQT))
    ·
      have hconj : ∀ l ∈ L, ∀ k ∈ D ⊔ pCoreOf 2 L, l * k * l⁻¹ ∈ D ⊔ pCoreOf 2 L := by
        intro l hl k hk
        rw [Subgroup.sup_eq_closure] at hk
        induction hk using Subgroup.closure_induction with
        | mem x hx =>
          rcases hx with hx | hx
          · have e : l * x * l⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ * x := by group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ (hx.2 l hl)))
              (Subgroup.mem_sup_left hx)
          · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
              (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) x).mp hx)
        | one => simp
        | mul a b _ _ ha hb =>
          have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
          rw [e]
          exact Subgroup.mul_mem _ ha hb
        | inv a _ ha =>
          have e : l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ := by group
          rw [e]
          exact Subgroup.inv_mem _ ha
      intro l hl
      exact mem_normalizer_of_conj_le (hconj l hl) (hconj l⁻¹ (L.inv_mem hl))
    ·
      intro t ht
      refine mem_normalizer_sup (mem_normalizer_of_conj_le ?_ ?_)
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (h.normal ht))
      · rintro d ⟨hdT, hd⟩
        refine ⟨T.mul_mem (T.mul_mem ht hdT) (T.inv_mem ht), fun l hl => ?_⟩
        have hl' : t⁻¹ * l * t ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (h.normal (T.inv_mem ht)) l).mp hl
          simpa using this
        have e : t * d * t⁻¹ * l * (t * d * t⁻¹)⁻¹ * l⁻¹ =
            t * (d * (t⁻¹ * l * t) * d⁻¹ * (t⁻¹ * l * t)⁻¹) * t⁻¹ := by group
        rw [e]
        exact hQN t ht _ (hd _ hl')
      · rintro d ⟨hdT, hd⟩
        refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hdT) (T.inv_mem (T.inv_mem ht)),
          fun l hl => ?_⟩
        have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (h.normal ht) l).mp hl
        have e : t⁻¹ * d * t⁻¹⁻¹ * l * (t⁻¹ * d * t⁻¹⁻¹)⁻¹ * l⁻¹ =
            t⁻¹ * (d * (t * l * t⁻¹) * d⁻¹ * (t * l * t⁻¹)⁻¹) * t⁻¹⁻¹ := by group
        rw [e]
        exact hQN _ (T.inv_mem ht) _ (hd _ hl')
  exact hle (Subgroup.mem_sup_left (show c ∈ D from ⟨hcT, hc⟩))

theorem conjV_ROf_props (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) {r : G}
    (hr : r ∈ ROf T L V₁) (hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G)) :
    (∃ k : ℕ, conjV (fsuV T I) r hrV ^ 2 ^ k = 1) ∧
    conjV (fsuV T I) r hrV ∈
      stabW ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) ∧
    (∀ x ∈ autOn L (fsuV T I),
      conjV (fsuV T I) r hrV * x * (conjV (fsuV T I) r hrV)⁻¹ ∈ autOn L (fsuV T I)) ∧
    (∀ x ∈ autOn (LOf L V₁) (fsuV T I), conjV (fsuV T I) r hrV * x *
      (conjV (fsuV T I) r hrV)⁻¹ ∈ autOn (LOf L V₁) (fsuV T I)) ∧
    (∀ x : ↥(autOn (LOf L V₁) (fsuV T I)), ∃ y : ↥(autOn (LOf L V₁) (fsuV T I)),
      y ∈ CFSG.pCore 2 ↥(autOn (LOf L V₁) (fsuV T I)) ∧
        conjV (fsuV T I) r hrV * (x : MulAut ↥(fsuV T I)) * (conjV (fsuV T I) r hrV)⁻¹ =
          (y : MulAut ↥(fsuV T I)) * x) := by
  have hrT : r ∈ T := ROf_le_T h hr
  have hrL : r ∈ Subgroup.normalizer (L : Set G) := h.normal hrT
  have hrL₁ : r ∈ Subgroup.normalizer (LOf L V₁ : Set G) := T_le_normalizer_L1 h hU hrT
  have hX : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    lOf_le_L.trans (L_le_normalizer_fsuV h)
  have hconj : ∀ {x : G} (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G)),
      conjV (fsuV T I) r hrV * conjV (fsuV T I) x hx * (conjV (fsuV T I) r hrV)⁻¹ =
        conjV (fsuV T I) (r * x * r⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrV hx)
          (Subgroup.inv_mem _ hrV)) := by
    intro x hx
    rw [← conjV_inv _ hrV, ← conjV_mul, ← conjV_mul]
  have hceq : ∀ {x y : G} (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G))
      (hy : y ∈ Subgroup.normalizer (fsuV T I : Set G)), x = y →
      conjV (fsuV T I) x hx = conjV (fsuV T I) y hy := by
    intro x y hx hy hxy
    subst hxy
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := isPGroup_ROf (T := T) (L := L) (V₁ := V₁) ⟨r, hr⟩
    refine ⟨k, ?_⟩
    have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    ext v
    have : ((conjV (fsuV T I) r hrV ^ 2 ^ k) v : G) = r ^ 2 ^ k * v * (r ^ 2 ^ k)⁻¹ := by
      clear hk hrk
      induction (2 ^ k) with
      | zero => simp
      | succ m ih => rw [pow_succ', MulAut.mul_apply, conjV_apply_coe, ih]; group
    rw [this, hrk]
    simp
  · rw [← inf_centralizer_subgroupOf, conjV_mem_stabW_iff inf_le_left hrV]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hrV, mem_normalizer_centralizer hrL⟩
  · intro x hx
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hx
    rw [hconj hlV]
    exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hrL l).mp hl) _
  · intro x hx
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hx
    rw [hconj hlV]
    exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hrL₁ l).mp hl) _
  · intro x
    obtain ⟨l, rfl⟩ := autOnHom'_surjective _ _ hX x
    have hk := commutator_lOf_ROf_mem h hU l.2 hr
    have hkL₁ : r * (l : G) * r⁻¹ * (l : G)⁻¹ ∈ LOf L V₁ :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ hk
    refine ⟨autOnHom' _ _ hX ⟨_, hkL₁⟩, conjV_mem_pCore_of_mem_pCoreOf hX hk, ?_⟩
    rw [autOnHom'_coe, autOnHom'_coe, hconj, ← conjV_mul]
    exact hceq _ _ (by group)

theorem radicalInner_of_kind (hFc : Facts15c) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    RadicalInner (autOn L (fsuV T I)) ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I))
      (V₁.subgroupOf (fsuV T I)) := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  rcases hk with hk | hk
  · obtain ⟨_, K, _, _, π, hK, hπ⟩ := sl3_realization hG2 h1102 h hk
    exact hFc.innerSL3 K n h.one_lt hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _
      (isFlagW_of_isVi h hU)
  · obtain ⟨_, K, _, _, π, hK, hπ⟩ := sp4_realization hG2 h1102 h hk
    exact hFc.innerSp4 K n h.one_lt hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _
      (isFlagW_of_isVi h hU)

theorem ROf_eq_sup (hFc : Facts15c) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    ROf T L V₁ = pCoreOf 2 (LOf L V₁) ⊔ pCoreOf 2 (L ⊔ T) := by
  refine le_antisymm (fun r hr => ?_) (sup_le (pCoreOf_lOf_le_ROf h hU) (pCoreOf_LT_le_ROf h))
  have hrT : r ∈ T := ROf_le_T h hr
  have hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G) := T_le_normalizer_fsuV T I hrT
  obtain ⟨p1, p2, p3, p4, p5⟩ := conjV_ROf_props h hU hr hrV
  have hRI := radicalInner_of_kind hFc hG2 h1102 h hU hk
  unfold RadicalInner at hRI
  rw [← autOn_lOf_eq h hU] at hRI
  obtain ⟨y, hy, hyeq⟩ := hRI _ p1 p2 p3 p4 p5
  have hX : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    lOf_le_L.trans (L_le_normalizer_fsuV h)
  obtain ⟨k, hk, rfl⟩ := exists_mem_pCoreOf_of_mem_pCore hX
    (isPGroup_lOf_inf_centralizer h1102 h) hy
  have hkR : (k : G) ∈ ROf T L V₁ := pCoreOf_lOf_le_ROf h hU hk
  have hkV : (k : G) ∈ Subgroup.normalizer (fsuV T I : Set G) := hX k.2
  rw [autOnHom'_coe] at hyeq
  have hc : (k : G)⁻¹ * r ∈ pCoreOf 2 (L ⊔ T) := by
    refine mem_pCoreOf_LT_of_conj h (T.mul_mem (T.inv_mem (ROf_le_T h hkR)) hrT) fun l hl => ?_
    have hlV : l ∈ Subgroup.normalizer (fsuV T I : Set G) := L_le_normalizer_fsuV h hl
    have hx : (k : G)⁻¹ * r * l * ((k : G)⁻¹ * r)⁻¹ * l⁻¹ ∈ L := by
      have h1 : r * l * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (h.normal hrT) l).mp hl
      have h2 : (k : G)⁻¹ * (r * l * r⁻¹) * (k : G) ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem (lOf_le_L k.2)) h1) (lOf_le_L k.2)
      have e : (k : G)⁻¹ * r * l * ((k : G)⁻¹ * r)⁻¹ * l⁻¹ =
          (k : G)⁻¹ * (r * l * r⁻¹) * (k : G) * l⁻¹ := by group
      rw [e]
      exact L.mul_mem h2 (L.inv_mem hl)
    rw [← centralizer_eq_pCoreOf h1102 h]
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hu : l⁻¹ * v * l ∈ fsuV T I := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) v).mp hv
      simpa using this
    have hw : (k : G) * (l⁻¹ * v * l) * (k : G)⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp hkV _).mp hu
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨_, hw⟩ : ↥(fsuV T I)) : G))
      (hyeq (conjV (fsuV T I) l hlV) (conjV_mem_autOn hl hlV))
    simp only [MulAut.mul_apply, ← conjV_inv, conjV_apply_coe] at h1
    set X := (k : G)⁻¹ * r * l * ((k : G)⁻¹ * r)⁻¹ * l⁻¹ with hX
    have key : X * v * X⁻¹ = v := by
      calc X * v * X⁻¹ = (k : G)⁻¹ * (r * (l * (r⁻¹ * ((k : G) * (l⁻¹ * v * l) * (k : G)⁻¹) *
            r⁻¹⁻¹) * l⁻¹) * r⁻¹) * k := by rw [hX]; group
        _ = (k : G)⁻¹ * ((k : G) * (l * ((k : G)⁻¹ * ((k : G) * (l⁻¹ * v * l) * (k : G)⁻¹) *
            (k : G)⁻¹⁻¹) * l⁻¹) * (k : G)⁻¹) * k := by rw [h1]
        _ = v := by group
    calc v * X = X * v * X⁻¹ * X := by rw [key]
      _ = X * v := by group
  have : r = (k : G) * ((k : G)⁻¹ * r) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hc)

theorem ROf_le_centralizer_V1' (hFc : Facts15c) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    ROf T L V₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
  rw [ROf_eq_sup hFc hG2 h1102 h hU hk]
  refine sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
    (lOf_one_le_centralizer hF11 h1102 h hU)) ?_
  refine (Subgroup.le_centralizer_iff.mp (fsuV_le_centralizer_pCoreOf_LT h)).trans ?_
  exact Subgroup.centralizer_le (IsVi.le_fsuV hU)

theorem lOf_inf_le_normalizer_ROf (hFc : Facts15c) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (ROf T L V₁ : Set G) := by
  rw [ROf_eq_sup hFc hG2 h1102 h hU hk]
  intro x hx
  exact mem_normalizer_sup (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (T_le_normalizer_lOf (T := L ⊓ Subgroup.normalizer (V₁ : Set G))
        (inf_le_left.trans Subgroup.le_normalizer) inf_le_right hx))
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      ((le_sup_left.trans Subgroup.le_normalizer) hx.1))

end CFSG.Quasithin.Vol2.Ch11.SecA
