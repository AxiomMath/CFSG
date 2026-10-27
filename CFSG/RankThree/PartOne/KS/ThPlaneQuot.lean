module

public import CFSG.RankThree.PartOne.KS.ThPlaneCoord
public import CFSG.RankThree.PartOne.KS.ThPlaneAlt

public section

namespace CFSG.RankThree.PartOne.ThPlane

open CFSG.Certificates.ExtraspecialNF
open scoped commutatorElement

structure ExtQuotData (G : Type) [Group G] (A : Type) [Group A] where
  z : G
  q : Fin 8 → G
  c : Fin 8 → Fin 8 → ZMod 2
  M : Subgroup G
  rel : Rel z q c
  inj : Function.Injective (Function.uncurry (nf z q))
  Q_le : Subgroup.closure (insert z (Set.range q)) ≤ M
  norm : ∀ m ∈ M, ∀ g ∈ Subgroup.closure (insert z (Set.range q)),
    m * g * m⁻¹ ∈ Subgroup.closure (insert z (Set.range q))
  zc : ∀ m ∈ M, m * z = z * m
  π : M →* A
  surj : Function.Surjective π
  ker : ∀ m : M, π m = 1 ↔ (m : G) ∈ Subgroup.closure (insert z (Set.range q))

namespace ExtQuotData

variable {G : Type} [Group G] {A : Type} [Group A] (D : ExtQuotData G A)

@[expose] def Q : Subgroup G := Subgroup.closure (insert D.z (Set.range D.q))

@[expose] noncomputable def act (m : G) : (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2) :=
  actv D.z D.q m

theorem act_mul {m m' : G} (hm : m ∈ D.M) (hm' : m' ∈ D.M) (v : Fin 8 → ZMod 2) :
    D.act (m * m') v = D.act m (D.act m' v) :=
  actv_mul D.rel D.inj (D.norm m hm) (D.zc m hm) (D.norm m' hm') v

theorem act_add {m : G} (hm : m ∈ D.M) (v w : Fin 8 → ZMod 2) :
    D.act m (v + w) = D.act m v + D.act m w :=
  actv_add D.rel D.inj (D.norm m hm) (D.zc m hm) v w

theorem act_one (v : Fin 8 → ZMod 2) : D.act 1 v = v := actv_one D.inj v

theorem act_of_mem {m : G} (hm : m ∈ D.Q) (v : Fin 8 → ZMod 2) : D.act m v = v :=
  actv_of_mem D.rel D.inj hm v

theorem act_zero {m : G} (hm : m ∈ D.M) : D.act m 0 = 0 := by
  have h := D.act_add hm 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem bil_act {m : G} (hm : m ∈ D.M) (v w : Fin 8 → ZMod 2) :
    bil D.c (D.act m v) (D.act m w) = bil D.c v w :=
  bil_actv D.rel D.inj (D.norm m hm) (D.zc m hm) v w

theorem coord_conj {m : G} (hm : m ∈ D.M) {g : G} (hg : g ∈ D.Q) :
    coord D.z D.q (m * g * m⁻¹) = D.act m (coord D.z D.q g) :=
  ThPlane.coord_conj D.rel D.inj (D.norm m hm) (D.zc m hm) hg

theorem act_inv_act {g : G} (hg : g ∈ D.M) (v : Fin 8 → ZMod 2) :
    D.act g⁻¹ (D.act g v) = v := by
  rw [← D.act_mul (D.M.inv_mem hg) hg, inv_mul_cancel, D.act_one]

theorem exists_conj_act {t w : G} (ht : t ∈ D.M) (hw : w ∈ D.M)
    (hconj : ∃ a : A, a * D.π ⟨t, ht⟩ * a⁻¹ = D.π ⟨w, hw⟩) :
    ∃ g ∈ D.M, ∀ v, D.act g (D.act t (D.act g⁻¹ v)) = D.act w v := by
  obtain ⟨a, ha⟩ := hconj
  obtain ⟨⟨g, hg⟩, hga⟩ := D.surj a
  refine ⟨g, hg, fun v => ?_⟩
  have hgt : g * t * g⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hg ht) (D.M.inv_mem hg)
  have h1 : D.π ⟨g * t * g⁻¹, hgt⟩ = D.π ⟨w, hw⟩ := by
    have : (⟨g * t * g⁻¹, hgt⟩ : D.M) = ⟨g, hg⟩ * ⟨t, ht⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hga, ha]
  have hn : w⁻¹ * (g * t * g⁻¹) ∈ D.Q := by
    have hmem : w⁻¹ * (g * t * g⁻¹) ∈ D.M := D.M.mul_mem (D.M.inv_mem hw) hgt
    refine (D.ker ⟨_, hmem⟩).1 ?_
    have : (⟨w⁻¹ * (g * t * g⁻¹), hmem⟩ : D.M) = ⟨w, hw⟩⁻¹ * ⟨g * t * g⁻¹, hgt⟩ := rfl
    rw [this, map_mul, map_inv, h1, inv_mul_cancel]
  have e : g * t * g⁻¹ = w * (w⁻¹ * (g * t * g⁻¹)) := by group
  have h2 : D.act (g * t * g⁻¹) v = D.act w v := by
    rw [e, D.act_mul hw (D.M.mul_mem (D.M.inv_mem hw) hgt), D.act_of_mem hn]
  rw [← h2, D.act_mul (D.M.mul_mem hg ht) (D.M.inv_mem hg), D.act_mul hg ht]

theorem fix_conj {t w : G} (ht : t ∈ D.M) (hw : w ∈ D.M)
    (hconj : ∃ a : A, a * D.π ⟨t, ht⟩ * a⁻¹ = D.π ⟨w, hw⟩) :
    ∃ g ∈ D.M, (∀ v, D.act t v = v → D.act w (D.act g v) = D.act g v) ∧
      (∀ v, D.act w v = v → D.act t (D.act g⁻¹ v) = D.act g⁻¹ v) := by
  obtain ⟨g, hg, hgt⟩ := D.exists_conj_act ht hw hconj
  refine ⟨g, hg, fun v hv => ?_, fun v hv => ?_⟩
  · have := hgt (D.act g v)
    rw [D.act_inv_act hg, hv] at this
    exact this.symm
  · have := hgt v
    rw [hv] at this
    have h2 := congrArg (D.act g⁻¹) this
    rw [D.act_inv_act hg] at h2
    exact h2

theorem centralizer_le_zpowers {t w : G} (ht : t ∈ D.M) (hw : w ∈ D.M)
    (hconj : ∃ a : A, a * D.π ⟨t, ht⟩ * a⁻¹ = D.π ⟨w, hw⟩)
    (hfix : ∀ v, D.act w v = v → v = 0) {g : G} (hg : g ∈ D.Q) (hc : t * g = g * t) :
    g ∈ Subgroup.zpowers D.z := by
  obtain ⟨k, hk, hk1, -⟩ := D.fix_conj ht hw hconj
  have hfixg : D.act t (coord D.z D.q g) = coord D.z D.q g := by
    have := D.coord_conj ht hg
    have e : t * g * t⁻¹ = g := by rw [hc]; group
    rw [e] at this
    exact this.symm
  have h0 : D.act k (coord D.z D.q g) = 0 := hfix _ (hk1 _ hfixg)
  have : coord D.z D.q g = 0 := by
    have h2 := congrArg (D.act k⁻¹) h0
    rw [D.act_inv_act hk, D.act_zero (D.M.inv_mem hk)] at h2
    exact h2
  exact (coord_eq_zero_iff D.rel D.inj hg).1 this

theorem isPGroup_Q : IsPGroup 2 D.Q :=
  IsPGroup.of_card (n := 9) (card_closure D.rel D.inj)

theorem z_ne_one : D.z ≠ 1 := ne_one_of_injective D.inj

theorem orderOf_z : orderOf D.z = 2 := orderOf_eq_two D.rel D.z_ne_one

theorem orderOf_proj {t : G} (ht : t ∈ D.M) {n : ℕ} (hn : n.Prime) (hn2 : n ≠ 2)
    (ho : orderOf t = n) : orderOf (D.π ⟨t, ht⟩) = n := by
  have hpow : (D.π ⟨t, ht⟩) ^ n = 1 := by
    rw [← map_pow]
    have : (⟨t, ht⟩ : D.M) ^ n = 1 := Subtype.ext (by simp [← ho])
    rw [this, map_one]
  have : Fact n.Prime := ⟨hn⟩
  refine orderOf_eq_prime hpow ?_
  intro h1
  have hQ : t ∈ D.Q := (D.ker ⟨t, ht⟩).1 h1
  obtain ⟨k, hk⟩ := D.isPGroup_Q ⟨t, hQ⟩
  have h2 : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : n ∣ 2 ^ k := ho ▸ orderOf_dvd_of_pow_eq_one h2
  exact hn2 ((Nat.prime_dvd_prime_iff_eq hn Nat.prime_two).1 (hn.dvd_of_dvd_pow h3))

theorem card_le_eight [Finite G] (D : ExtQuotData G (alternatingGroup (Fin 9))) {t w : G}
    (ht : t ∈ D.M) (hw : w ∈ D.M) (hπw : orderOf (D.π ⟨w, hw⟩) = 5) (hto : orderOf t = 5)
    (hfix : ∀ v, D.act w v = v → v = 0) {V : Subgroup G} (hVM : V ≤ D.M)
    (hVc : ∀ x ∈ V, x * t = t * x) (hV2 : IsPGroup 2 V) : Nat.card V ≤ 8 := by
  have hπt := D.orderOf_proj ht Nat.prime_five (by norm_num) hto
  have hconj : ∃ a : alternatingGroup (Fin 9), a * D.π ⟨t, ht⟩ * a⁻¹ = D.π ⟨w, hw⟩ :=
    exists_conj_alt Nat.prime_five le_rfl (by norm_num) _ _ hπt hπw
  let ψ : V →* alternatingGroup (Fin 9) := D.π.comp (Subgroup.inclusion hVM)
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hz2 : Nat.card (Subgroup.zpowers D.z) = 2 := by
      rw [Nat.card_zpowers, D.orderOf_z]
    rw [← hz2]
    refine Nat.card_le_card_of_injective (fun x : ψ.ker => (⟨((x : V) : G), ?_⟩ :
      Subgroup.zpowers D.z)) ?_
    · have hx1 : D.π (Subgroup.inclusion hVM (x : V)) = 1 := x.2
      have hxQ : ((x : V) : G) ∈ D.Q := (D.ker (Subgroup.inclusion hVM (x : V))).1 hx1
      exact D.centralizer_le_zpowers ht hw hconj hfix hxQ (hVc _ (x : V).2).symm
    · intro x y hxy
      have h1 : ((x : V) : G) = ((y : V) : G) :=
        congrArg (fun u : Subgroup.zpowers D.z => (u : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card ψ.range ∣ 4 := by
    have hpg : IsPGroup 2 ψ.range := hV2.of_surjective ψ.rangeRestrict
      (by intro y; obtain ⟨x, hx⟩ := y.2; exact ⟨x, Subtype.ext hx⟩)
    refine card_dvd_four_of_commute_five (D.π ⟨t, ht⟩) hπt ψ.range ?_ hpg
    rintro _ ⟨x, rfl⟩
    show D.π (Subgroup.inclusion hVM x) * D.π ⟨t, ht⟩ = D.π ⟨t, ht⟩ * D.π (Subgroup.inclusion hVM x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hVc _ x.2)
  have hr4 : Nat.card ψ.range ≤ 4 := Nat.le_of_dvd (by norm_num) hrange
  calc Nat.card V = Nat.card ψ.ker * Nat.card ψ.range := hcard.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hker hr4
    _ = 8 := by norm_num

theorem act_coord_of_commute {t : G} (ht : t ∈ D.M) {g : G} (hg : g ∈ D.Q) (hc : t * g = g * t) :
    D.act t (coord D.z D.q g) = coord D.z D.q g := by
  have := D.coord_conj ht hg
  have e : t * g * t⁻¹ = g := by rw [hc]; group
  rw [e] at this
  exact this.symm

theorem coord_one : coord D.z D.q (1 : G) = 0 := by
  have : (1 : G) = nf D.z D.q 0 0 := (nf_zero_zero D.z D.q).symm
  rw [this, coord_nf D.inj]

theorem card_le_four [Finite G] (D : ExtQuotData G (alternatingGroup (Fin 9))) {t w : G}
    (ht : t ∈ D.M) (hw : w ∈ D.M) (hπw : orderOf (D.π ⟨w, hw⟩) = 7) (hto : orderOf t = 7)
    (D0 : Set (Fin 8 → ZMod 2)) (hD0 : ∀ v, D.act w v = v → v ∈ D0)
    (hpair : ∀ e ∈ D0, ∀ e' ∈ D0, e ≠ 0 → e' ≠ 0 → e ≠ e' → bil D.c e e' = 1)
    {V : Subgroup G} (hVM : V ≤ D.M) (hVc : ∀ x ∈ V, x * t = t * x)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : IsPGroup 2 V) : Nat.card V ≤ 4 := by
  have hπt := D.orderOf_proj ht (by decide) (by norm_num) hto
  have hconj : ∃ a : alternatingGroup (Fin 9), a * D.π ⟨t, ht⟩ * a⁻¹ = D.π ⟨w, hw⟩ :=
    exists_conj_alt (by decide) (by norm_num) le_rfl _ _ hπt hπw
  have hVQ : ∀ x ∈ V, x ∈ D.Q := by
    let ψ : V →* alternatingGroup (Fin 9) := D.π.comp (Subgroup.inclusion hVM)
    have hpg : IsPGroup 2 ψ.range := hV2.of_surjective ψ.rangeRestrict
      (by intro y; obtain ⟨x, hx⟩ := y.2; exact ⟨x, Subtype.ext hx⟩)
    have hbot : ψ.range = ⊥ := by
      refine eq_bot_of_commute_seven (D.π ⟨t, ht⟩) hπt ψ.range ?_ hpg
      rintro _ ⟨x, rfl⟩
      show D.π (Subgroup.inclusion hVM x) * D.π ⟨t, ht⟩ =
        D.π ⟨t, ht⟩ * D.π (Subgroup.inclusion hVM x)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVc _ x.2)
    intro x hx
    have h1 : ψ ⟨x, hx⟩ = 1 := by
      have : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨⟨x, hx⟩, rfl⟩
      rw [hbot] at this
      exact this
    exact (D.ker (Subgroup.inclusion hVM ⟨x, hx⟩)).1 h1
  obtain ⟨g, hg, hk1, -⟩ := D.fix_conj ht hw hconj
  have hginj : ∀ u u' : Fin 8 → ZMod 2, D.act g u = D.act g u' → u = u' := by
    intro u u' h
    have := congrArg (D.act g⁻¹) h
    rwa [D.act_inv_act hg, D.act_inv_act hg] at this
  let a : V → (Fin 8 → ZMod 2) := fun x => D.act g (coord D.z D.q (x : G))
  have ha_mem : ∀ x : V, a x ∈ D0 := fun x =>
    hD0 _ (hk1 _ (D.act_coord_of_commute ht (hVQ _ x.2) (hVc _ x.2).symm))
  have ha_add : ∀ x y : V, a (x * y) = a x + a y := by
    intro x y
    show D.act g (coord D.z D.q ((x : G) * (y : G))) = _
    rw [coord_mul D.rel D.inj (hVQ _ x.2) (hVQ _ y.2), D.act_add hg]
  have ha_orth : ∀ x y : V, bil D.c (a x) (a y) = 0 := by
    intro x y
    show bil D.c (D.act g (coord D.z D.q (x : G))) (D.act g (coord D.z D.q (y : G))) = 0
    rw [D.bil_act hg]
    obtain ⟨s, v, hv⟩ := (mem_closure_iff D.rel).1 (hVQ _ x.2)
    obtain ⟨s', v', hv'⟩ := (mem_closure_iff D.rel).1 (hVQ _ y.2)
    have hz1 := D.z_ne_one
    have hsymm := D.rel.symm_of_ne_one hz1
    have hdiag := D.rel.diag_eq_zero hz1
    have hcomm := hVab _ x.2 _ y.2
    have hc1 : ⁅(x : G), (y : G)⁆ = 1 := by
      rw [commutatorElement_def, hcomm]; group
    rw [← hv, ← hv', commutator_eq_zpow D.rel hsymm hdiag] at hc1
    rw [← hv, ← hv', coord_nf D.inj, coord_nf D.inj]
    exact zpow_val_inj hz1 (hc1.trans (pow_zero D.z).symm |>.trans (by simp))
  have ha_pair : ∀ x y : V, a x = 0 ∨ a y = 0 ∨ a x = a y := by
    intro x y
    by_contra hcon
    push Not at hcon
    have h1 := hpair _ (ha_mem x) _ (ha_mem y) hcon.1 hcon.2.1 hcon.2.2
    rw [ha_orth] at h1
    exact zero_ne_one h1
  let ψ' : V →* Multiplicative (Fin 8 → ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (a x)
      map_one' := by
        show Multiplicative.ofAdd (D.act g (coord D.z D.q ((1 : V) : G))) = 1
        rw [Subgroup.coe_one, D.coord_one, D.act_zero hg]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (a (x * y)) =
          Multiplicative.ofAdd (a x) * Multiplicative.ofAdd (a y)
        rw [ha_add]
        rfl }
  have hcard := Subgroup.card_ker_mul_card_range ψ'
  have hz2 : Nat.card (Subgroup.zpowers D.z) = 2 := by
    rw [Nat.card_zpowers, D.orderOf_z]
  have hker : Nat.card ψ'.ker ≤ 2 := by
    refine le_trans ?_ hz2.le
    have hmem : ∀ x : ψ'.ker, ((x : V) : G) ∈ Subgroup.zpowers D.z := by
      intro x
      have hx0 : a (x : V) = 0 := by
        have h1 : ψ' (x : V) = 1 := x.2
        exact h1
      have : coord D.z D.q ((x : V) : G) = 0 := by
        apply hginj
        rw [D.act_zero hg]
        exact hx0
      exact (coord_eq_zero_iff D.rel D.inj (hVQ _ (x : V).2)).1 this
    refine Nat.card_le_card_of_injective (fun x : ψ'.ker => (⟨((x : V) : G), hmem x⟩ :
      Subgroup.zpowers D.z)) ?_
    intro x y hxy
    have h1 : ((x : V) : G) = ((y : V) : G) :=
      congrArg (fun u : Subgroup.zpowers D.z => (u : G)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card ψ'.range ≤ 2 := by
    have hcs : Nat.card ψ'.range = Set.ncard ((ψ'.range : Subgroup _) : Set (Multiplicative (Fin 8 → ZMod 2))) :=
      Nat.card_coe_set_eq _
    rw [hcs]
    by_cases hex : ∃ x : V, a x ≠ 0
    · obtain ⟨x0, hx0⟩ := hex
      have hsub : ((ψ'.range : Subgroup _) : Set (Multiplicative (Fin 8 → ZMod 2))) ⊆
          {1, Multiplicative.ofAdd (a x0)} := by
        rintro _ ⟨x, rfl⟩
        rcases ha_pair x x0 with h | h | h
        · left
          show Multiplicative.ofAdd (a x) = 1
          rw [h]; rfl
        · exact absurd h hx0
        · right
          show Multiplicative.ofAdd (a x) = Multiplicative.ofAdd (a x0)
          rw [h]
      calc Set.ncard ((ψ'.range : Subgroup _) : Set (Multiplicative (Fin 8 → ZMod 2)))
          ≤ Set.ncard ({1, Multiplicative.ofAdd (a x0)} : Set (Multiplicative (Fin 8 → ZMod 2))) :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
            refine (Set.ncard_insert_le _ _).trans ?_
            rw [Set.ncard_singleton]
    · push Not at hex
      have hsub : ((ψ'.range : Subgroup _) : Set (Multiplicative (Fin 8 → ZMod 2))) ⊆ {1} := by
        rintro _ ⟨x, rfl⟩
        show Multiplicative.ofAdd (a x) = 1
        rw [hex x]; rfl
      calc Set.ncard ((ψ'.range : Subgroup _) : Set (Multiplicative (Fin 8 → ZMod 2)))
          ≤ Set.ncard ({1} : Set (Multiplicative (Fin 8 → ZMod 2))) :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by rw [Set.ncard_singleton]; norm_num
  calc Nat.card V = Nat.card ψ'.ker * Nat.card ψ'.range := hcard.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange
    _ = 4 := by norm_num

theorem act_eq_mulVec {g : G} (hg : g ∈ D.M) (col : Fin 8 → Fin 8 → ZMod 2)
    (hcol : ∀ i, coord D.z D.q (g * D.q i * g⁻¹) = col i) (v : Fin 8 → ZMod 2) :
    D.act g v = (Matrix.of fun r k => col k r).mulVec v := by
  let A : (Fin 8 → ZMod 2) →+ (Fin 8 → ZMod 2) :=
    { toFun := D.act g
      map_zero' := D.act_zero hg
      map_add' := D.act_add hg }
  have hsingle : ∀ i, D.act g (Pi.single i 1) = col i := by
    intro i
    have : nf D.z D.q 0 (Pi.single i 1) = D.q i := nf_single D.z D.q i
    have h0 : D.act g (Pi.single i 1) =
        coord D.z D.q (g * nf D.z D.q 0 (Pi.single i 1) * g⁻¹) := rfl
    rw [h0, this, hcol]
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  have h1 : D.act g v = ∑ i, D.act g (Pi.single i (v i)) := by
    conv_lhs => rw [hv]
    exact map_sum A _ _
  have h2 : ∀ i, D.act g (Pi.single i (v i)) = v i • col i := by
    intro i
    rcases zmod_two_cases (v i) with h | h
    · rw [h]
      have : (Pi.single i (0 : ZMod 2) : Fin 8 → ZMod 2) = 0 := by simp
      rw [this, D.act_zero hg]
      simp
    · rw [h, hsingle]
      simp
  rw [h1]
  funext r
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, h2,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem act_mul_matrix {a b : G} (ha : a ∈ D.M) (hb : b ∈ D.M) {Ba Bb : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hA : ∀ v, D.act a v = Ba.mulVec v) (hB : ∀ v, D.act b v = Bb.mulVec v) (v : Fin 8 → ZMod 2) :
    D.act (a * b) v = (Ba * Bb).mulVec v := by
  rw [D.act_mul ha hb, hB, hA, Matrix.mulVec_mulVec]

theorem act_pow_matrix {a : G} (ha : a ∈ D.M) {Ba : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hA : ∀ v, D.act a v = Ba.mulVec v) (k : ℕ) :
    ∀ v : Fin 8 → ZMod 2, D.act (a ^ k) v = (Ba ^ k).mulVec v := by
  induction k with
  | zero => intro v; rw [pow_zero, pow_zero, D.act_one, Matrix.one_mulVec]
  | succ k ih =>
    intro v
    rw [pow_succ, pow_succ]
    exact D.act_mul_matrix (D.M.pow_mem ha k) ha ih hA v

end ExtQuotData

end CFSG.RankThree.PartOne.ThPlane
