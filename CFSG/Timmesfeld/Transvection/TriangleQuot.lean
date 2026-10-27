module

public import CFSG.Timmesfeld.Transvection.TriangleAb
public import CFSG.Timmesfeld.ARS.Sec8HypQuot

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.LeviQuot
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

@[expose] def triClass (A Y : Subgroup G) : Set (Subgroup G) :=
  {D | ∃ y ∈ Y, D = conjSub A y}

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t)
include S

theorem triClass_subset (Y : Subgroup G) : triClass A Y ⊆ Δ := by
  rintro _ ⟨y, -, rfl⟩
  exact S.cls.root.conjSub_mem S.tri.memA y

omit S in
theorem le_of_mem_triClass {A Y : Subgroup G} (hAY : A ≤ Y) {D : Subgroup G}
    (hD : D ∈ triClass A Y) : D ≤ Y := by
  obtain ⟨y, hy, rfl⟩ := hD
  exact conjSub_le hAY hy

omit S in
theorem conjSub_mem_triClass {A Y : Subgroup G} {D : Subgroup G} (hD : D ∈ triClass A Y)
    {g : G} (hg : g ∈ Y) : conjSub D g ∈ triClass A Y := by
  obtain ⟨y, hy, rfl⟩ := hD
  exact ⟨g * y, Y.mul_mem hg hy, (conjSub_mul A g y).symm⟩

variable (htY : t ∈ A ⊔ E ⊔ B)
include htY

theorem mem_triClass : A ∈ triClass A (A ⊔ E ⊔ B) ∧ E ∈ triClass A (A ⊔ E ⊔ B) ∧
    B ∈ triClass A (A ⊔ E ⊔ B) := by
  obtain ⟨w, hw, hwE⟩ := S.exists_conjSub_eq_E
  refine ⟨⟨1, Subgroup.one_mem _, by rw [conjSub_one]⟩, ⟨w, le_sup_left (b := B) hw, hwE.symm⟩,
    ⟨t, htY, S.conjA.symm⟩⟩

theorem exists_opposite_triClass {D : Subgroup G} (hD : D ∈ triClass A (A ⊔ E ⊔ B)) :
    ∃ D' ∈ triClass A (A ⊔ E ⊔ B), Opposite D D' := by
  obtain ⟨y, hy, rfl⟩ := hD
  exact ⟨conjSub E y, conjSub_mem_triClass (S.mem_triClass htY).2.1 hy,
    S.tri.oppA.symm.conj y⟩

theorem gen_triClass : gen (triClass A (A ⊔ E ⊔ B)) = A ⊔ E ⊔ B := by
  refine le_antisymm (gen_le fun D hD => le_of_mem_triClass (le_sup_left.trans le_sup_left) hD)
    ?_
  obtain ⟨hA, hE, hB⟩ := S.mem_triClass htY
  exact sup_le (sup_le (le_gen hA) (le_gen hE)) (le_gen hB)

theorem mem_center_of_commutatorElement_mem [Finite G] {x : ↥(A ⊔ E ⊔ B)}
    (hx : ∀ y : ↥(A ⊔ E ⊔ B), ⁅x, y⁆ ∈ Subgroup.center ↥(A ⊔ E ⊔ B)) :
    x ∈ Subgroup.center ↥(A ⊔ E ⊔ B) := by
  have hAY : A ≤ A ⊔ E ⊔ B := le_sup_left.trans le_sup_left
  have key : ∀ D ∈ triClass A (A ⊔ E ⊔ B), ∀ d ∈ D, Commute (x : G) d := by
    intro D hD d hd
    by_cases hd1 : d = 1
    · rw [hd1]
      exact Commute.one_right _
    have hDΔ := S.triClass_subset _ hD
    have hDY := le_of_mem_triClass hAY hD
    have hdd : d * d = 1 := S.cls.mul_self hDΔ hd
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
    obtain ⟨d', hd'_def⟩ : ∃ d', d' = (x : G) * d * (x : G)⁻¹ := ⟨_, rfl⟩
    have hD' : conjSub D x ∈ triClass A (A ⊔ E ⊔ B) := conjSub_mem_triClass hD x.2
    have hD'Δ := S.triClass_subset _ hD'
    have hd' : d' ∈ conjSub D x := hd'_def ▸ conj_mem_conjSub _ hd
    have hd'1 : d' ≠ 1 := fun h => hd1 (conj_eq_one_iff.1 (hd'_def ▸ h))
    have hd'd' : d' * d' = 1 := S.cls.mul_self hD'Δ hd'
    have hc : ∀ g ∈ A ⊔ E ⊔ B, Commute (d * d') g := by
      intro g hg
      have h1 := Subgroup.mem_center_iff.1 (hx ⟨d, hDY hd⟩) ⟨g, hg⟩
      have h2 : ((⁅x, (⟨d, hDY hd⟩ : ↥(A ⊔ E ⊔ B))⁆ : ↥(A ⊔ E ⊔ B)) : G) = d' * d := by
        rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hd'_def, hdinv]
      have h3 : Commute (d' * d) g := by
        have := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul] at this
        rw [h2] at this
        exact this.symm
      have h4 : d * d' = (d' * d)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd'd', hdinv]
      rw [h4]
      exact h3.inv_left
    obtain ⟨P, hP, hDP⟩ := S.exists_opposite_triClass htY hD
    have hPΔ := S.triClass_subset _ hP
    have hPY := le_of_mem_triClass hAY hP
    by_cases hDD' : conjSub D x = D
    ·
      have hcD : d * d' ∈ D := D.mul_mem hd (hDD' ▸ hd')
      have hc1 : d * d' = 1 := by
        by_contra hc1
        exact hDP.not_commute_of_mem hcD hc1 fun y hy => hc y (hPY hy)
      have : d' = d := by
        rw [← hdinv]
        exact eq_inv_of_mul_eq_one_right hc1
      show (x : G) * d = d * x
      calc (x : G) * d = d' * x := by rw [hd'_def]; group
        _ = d * x := by rw [this]
    · exfalso
      rcases S.cls.commuting_or_opposite hDΔ hD'Δ (Ne.symm hDD') with hcomm | hopp
      ·
        refine hDP.not_commute_of_mem hd hd1 fun y hy => ?_
        by_cases hy1 : y = 1
        · rw [hy1]
          exact Commute.one_right _
        exact (commute_of_commute_mul S.cls S.iso hPΔ hDΔ hD'Δ (Ne.symm hDD') hcomm hy hy1 hd
          hd1 hd' (hc y (hPY hy)).symm).symm
      ·
        have hodd := hopp.odd_orderOf_mul (S.cls.root.mul_self D hDΔ) hd hd1 hd' hd'1
        have hcc : d * d' * (d * d') = 1 := by
          have h1 := (hc d (hDY hd)).eq
          calc d * d' * (d * d') = d * (d' * d) * d' := by group
            _ = d * (d * d') * d' := by
                rw [show d' * d = d⁻¹ * (d * d') * d by group, ← h1]; group
            _ = 1 := by
                rw [show d * (d * d') * d' = (d * d) * (d' * d') by group, hdd, hd'd', one_mul]
        have hc1 : d * d' = 1 := by
          have hdvd : orderOf (d * d') ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hcc])
          have h1 : orderOf (d * d') = 1 := by
            rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
            · exact h
            · exact absurd hodd (by rw [h]; decide)
          exact orderOf_eq_one_iff.1 h1
        have : d' = d := by
          rw [← hdinv]
          exact eq_inv_of_mul_eq_one_right hc1
        exact hDD' (S.cls.eq_of_mem_of_mem S.iso hD'Δ hDΔ hd' (this ▸ hd) hd'1)
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hg : (g : G) ∈ gen (triClass A (A ⊔ E ⊔ B)) := by
    rw [S.gen_triClass htY]
    exact g.2
  have : Commute (x : G) g := by
    refine gen_induction (p := fun y => Commute (x : G) y) hg (fun D hD y hy => key D hD y hy)
      (Commute.one_right _) fun y z hy hz => hy.mul_right hz
  exact this.eq.symm

theorem center_quotient_eq_bot [Finite G] :
    Subgroup.center (↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun q hq => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine S.mem_center_of_commutatorElement_mem htY fun y => ?_
  rw [← QuotientGroup.eq_one_iff (N := Subgroup.center ↥(A ⊔ E ⊔ B))]
  have h := Subgroup.mem_center_iff.1 hq (QuotientGroup.mk' _ y)
  rw [commutatorElement_def]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
  rw [← h]
  group

section Quot

variable [Finite G]

theorem isRootClass_quotClass :
    IsRootClass (quotClass (A ⊔ E ⊔ B) (triClass A (A ⊔ E ⊔ B))) :=
  LeviQuot.isRootClass_quotClass S.cls.root S.iso (S.triClass_subset _)
    (fun _ hX => le_of_mem_triClass (le_sup_left.trans le_sup_left) hX)
      (fun _ hX => S.exists_opposite_triClass htY hX)
    (S.mem_triClass htY).1 (fun _ hX _ hg => conjSub_mem_triClass hX hg)
    (fun _ ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩)
    (fun X hX Y hY hs => absurd hs (S.cls.noSpecial X (S.triClass_subset _ hX) Y
      (S.triClass_subset _ hY)))
    (S.gen_triClass htY)

theorem isTransvectionClass_quotClass :
    IsTransvectionClass (quotClass (A ⊔ E ⊔ B) (triClass A (A ⊔ E ⊔ B))) := by
  refine ⟨S.isRootClass_quotClass htY, ?_⟩
  rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩ hs
  exact S.cls.noSpecial X (S.triClass_subset _ hX) Y (S.triClass_subset _ hY)
    (special_of_special_quotMap S.cls.root S.iso (S.triClass_subset _)
      (fun _ hX => le_of_mem_triClass (le_sup_left.trans le_sup_left) hX)
      (fun _ hX => S.exists_opposite_triClass htY hX)
      (S.isRootClass_quotClass htY) hX hY hs)

theorem noIsolated_quotClass' :
    NoIsolated (quotClass (A ⊔ E ⊔ B) (triClass A (A ⊔ E ⊔ B))) :=
  LeviQuot.noIsolated_quotClass S.cls.root S.iso (S.triClass_subset _)
    (fun _ hX => le_of_mem_triClass (le_sup_left.trans le_sup_left) hX)
      (fun _ hX => S.exists_opposite_triClass htY hX)

theorem injOn_quotMap' : Set.InjOn (quotMap (A ⊔ E ⊔ B)) (triClass A (A ⊔ E ⊔ B)) :=
  LeviQuot.injOn_quotMap S.cls.root S.iso (S.triClass_subset _)
    (fun _ hX => le_of_mem_triClass (le_sup_left.trans le_sup_left) hX)
      (fun _ hX => S.exists_opposite_triClass htY hX)

theorem quotSetting : TriangleSetting (quotClass (A ⊔ E ⊔ B) (triClass A (A ⊔ E ⊔ B)))
    (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E) (quotMap (A ⊔ E ⊔ B) B)
    (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) := by
  obtain ⟨hA, hE, hB⟩ := S.mem_triClass htY
  have hinj := S.injOn_quotMap' htY
  have hAY := le_of_mem_triClass (le_sup_left.trans le_sup_left) hA
  have hEY := le_of_mem_triClass (le_sup_left.trans le_sup_left) hE
  have hBY := le_of_mem_triClass (le_sup_left.trans le_sup_left) hB
  refine ⟨S.isTransvectionClass_quotClass htY, S.noIsolated_quotClass' htY,
    ⟨⟨A, hA, rfl⟩, ⟨E, hE, rfl⟩, ⟨B, hB, rfl⟩, fun h => S.tri.ne (hinj hA hB h),
      commuting_quotMap S.tri.comm,
      opposite_quotMap hEY hAY S.tri.oppA fun h => S.tri.oppA.ne (hinj hE hA h),
      opposite_quotMap hEY hBY S.tri.oppB fun h => S.tri.oppB.ne (hinj hE hB h)⟩,
    ?_, ?_, ?_⟩
  · rw [← map_mul]
    have : (⟨t, htY⟩ * ⟨t, htY⟩ : ↥(A ⊔ E ⊔ B)) = 1 := Subtype.ext S.sq
    rw [this, map_one]
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := exists_of_mem_quotMap hy
    exact Commute.map (show Commute (⟨t, htY⟩ : ↥(A ⊔ E ⊔ B)) y' from
      Subtype.ext (S.centE y' hy')) _
  · rw [← quotMap_conjSub A htY, S.conjA]

theorem exists_of_mem_graph_quot {f : ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)}
    (hf : f ∈ graph (quotMap (A ⊔ E ⊔ B) A)
      (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩)) :
    ∃ f' : ↥(A ⊔ E ⊔ B), (f' : G) ∈ graph A t ∧
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) f' = f := by
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff (S.quotSetting htY).commuting_conjSub).1 hf
  obtain ⟨a', ha', rfl⟩ := exists_of_mem_quotMap ha
  refine ⟨a' * (⟨t, htY⟩ * a' * (⟨t, htY⟩ : ↥(A ⊔ E ⊔ B))⁻¹), ?_, by simp⟩
  exact (mem_graph_iff S.commuting_conjSub).2 ⟨a', ha', rfl⟩

theorem quotFourTerm : FourTerm (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E)
    (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) := by
  intro e he f hf f' hf'
  obtain ⟨e₀, he₀, rfl⟩ := exists_of_mem_quotMap he
  obtain ⟨f₀, hf₀, rfl⟩ := S.exists_of_mem_graph_quot htY hf
  obtain ⟨f₀', hf₀', rfl⟩ := S.exists_of_mem_graph_quot htY hf'
  set z : G := (e₀ : G) * f₀ * e₀ * f₀ * f₀' * (e₀ * f₀ * e₀ * f₀) * f₀' with hz_def
  have hle : A ⊔ E ⊔ B ≤ Subgroup.centralizer {z} := by
    have h : ∀ {y}, y ∈ A ∨ y ∈ E ∨ y ∈ B → y ∈ Subgroup.centralizer {z} := fun hy =>
      Subgroup.mem_centralizer_singleton_iff.2
        (commute_commutator_mul S.cls S.iso S.tri S.sq S.centE S.conjA he₀ hf₀ hf₀' hy).eq.symm
    exact sup_le (sup_le (fun y hy => h (Or.inl hy)) (fun y hy => h (Or.inr (Or.inl hy))))
      fun y hy => h (Or.inr (Or.inr hy))
  have hxx : ((e₀ : G) * f₀ * e₀ * f₀) * (e₀ * f₀ * e₀ * f₀) = 1 :=
    commutator_mul_self S.cls S.iso S.tri S.centE S.conjA he₀ hf₀
  have hff : (f₀' : G) * f₀' = 1 := S.graph_mul_self hf₀'
  have hc : ⁅e₀ * f₀ * e₀ * f₀, f₀'⁆ ∈ Subgroup.center ↥(A ⊔ E ⊔ B) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 : ((⁅e₀ * f₀ * e₀ * f₀, f₀'⁆ : ↥(A ⊔ E ⊔ B)) : G) = z := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_eq_of_mul_eq_one_right hxx,
        inv_eq_of_mul_eq_one_right hff, hz_def]
    simp only [Subgroup.coe_mul]
    rw [h1]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
  rw [← map_mul, ← map_mul, ← map_mul, ← commutatorElement_eq_one_iff_commute,
    ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).2 hc

theorem eq_one_of_commute_quot {z : ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)}
    (hzA : ∀ y ∈ quotMap (A ⊔ E ⊔ B) A, Commute z y)
    (hzE : ∀ y ∈ quotMap (A ⊔ E ⊔ B) E, Commute z y)
    (hzB : ∀ y ∈ quotMap (A ⊔ E ⊔ B) B, Commute z y) : z = 1 := by
  set C := ((Subgroup.centralizer {z}).comap
    (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)))).map (A ⊔ E ⊔ B).subtype with hC
  have hmem : ∀ {X : Subgroup G}, X ≤ A ⊔ E ⊔ B →
      (∀ y ∈ quotMap (A ⊔ E ⊔ B) X, Commute z y) → X ≤ C := by
    intro X hX hz x hx
    refine ⟨⟨x, hX hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (hz _ (mk_mem_quotMap hx)).eq.symm
  have hle : A ⊔ E ⊔ B ≤ C := sup_le (sup_le (hmem (le_sup_left.trans le_sup_left) hzA)
    (hmem (le_sup_right.trans le_sup_left) hzE)) (hmem le_sup_right hzB)
  have hcen : z ∈ Subgroup.center (↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ g
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have : y' = y := Subtype.ext hyy'
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, this] at hy'
    exact hy'
  rw [S.center_quotient_eq_bot htY, Subgroup.mem_bot] at hcen
  exact hcen

omit htY [Finite G] in
theorem card_quotMap : Nat.card (quotMap (A ⊔ E ⊔ B) A) = Nat.card A := by
  have hAY : A ≤ A ⊔ E ⊔ B := le_sup_left.trans le_sup_left
  have hEY : E ≤ A ⊔ E ⊔ B := le_sup_right.trans le_sup_left
  have hinj : Set.InjOn (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)))
      (A.subgroupOf (A ⊔ E ⊔ B) : Set ↥(A ⊔ E ⊔ B)) := by
    intro a ha a' ha' h
    have h1 : a⁻¹ * a' ∈ Subgroup.center ↥(A ⊔ E ⊔ B) := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk'_apply] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel]
    have h2 : ((a⁻¹ * a' : ↥(A ⊔ E ⊔ B)) : G) ∈ A :=
      A.mul_mem (A.inv_mem (Subgroup.mem_subgroupOf.1 ha)) (Subgroup.mem_subgroupOf.1 ha')
    have h3 := eq_one_of_mem_center S.tri.oppA.symm hEY h2 h1
    rw [inv_mul_eq_one] at h3
    exact h3
  have : Nat.card (quotMap (A ⊔ E ⊔ B) A) = Nat.card (A.subgroupOf (A ⊔ E ⊔ B)) := by
    rw [quotMap, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hinj]
    rfl
  rw [this, card_subgroupOf_of_le hAY]

theorem exists_isNaturalModule_quot (hq : 4 ≤ Nat.card A) : ∃ n : ℕ, Nat.card A = 2 ^ n ∧
    ∃ φ : ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      ((quotMap (A ⊔ E ⊔ B) E).subgroupOf (quotMap (A ⊔ E ⊔ B) E ⊔
        quotMap (A ⊔ E ⊔ B) A)).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
      ((quotMap (A ⊔ E ⊔ B) A).subgroupOf (quotMap (A ⊔ E ⊔ B) E ⊔
        quotMap (A ⊔ E ⊔ B) A)).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) ∧
      ∃ θ : (Fin 2 → GaloisField 2 n) → ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B),
        IsNaturalModule φ θ ∧ Set.range θ = (corrN (quotMap (A ⊔ E ⊔ B) A)
          (quotMap (A ⊔ E ⊔ B) E) (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
            ⟨t, htY⟩) : Set (↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B))) := by
  have hq' : 4 ≤ Nat.card (quotMap (A ⊔ E ⊔ B) A) := by rw [S.card_quotMap]; exact hq
  obtain ⟨n, hn, φ, hφE, hφA, θ, hθ, hrange⟩ := (S.quotSetting htY).exists_isNaturalModule_corrN
    (S.quotFourTerm htY) hq' fun z hzA hzE hzB => S.eq_one_of_commute_quot htY
      (fun y hy => hzA y hy) (fun y hy => hzE y hy) (fun y hy => hzB y hy)
  exact ⟨n, S.card_quotMap.symm.trans hn, φ, hφE, hφA, θ, hθ, hrange⟩

end Quot

end TriangleSetting

end CFSG.Timmesfeld.Transvection
