module

public import CFSG.Timmesfeld.ARS.Sec5Centralizer

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Linear

theorem conjSet_inter (S T : Set (Subgroup G)) (g : G) :
    conjSet (S ∩ T) g = conjSet S g ∩ conjSet T g :=
  Set.image_inter fun _ _ h => RankOne.map_conj_inj.1 h

theorem conjSet_eq_self (hR : IsRootClass R) (g : G) : conjSet R g = R := by
  refine Set.Subset.antisymm ?_ fun B hB => ?_
  · rintro _ ⟨B, hB, rfl⟩
    exact hR.conjSub_mem hB g
  · rw [mem_conjSet]
    exact hR.conjSub_mem hB g⁻¹

theorem isTI_conjSet (hR : IsRootClass R) {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ) (g : G) :
    IsTI R (conjSet Δ g) := by
  obtain ⟨hΔR, ⟨A, hA, B, hB, hAB⟩, hne, hTI⟩ := hΔ
  refine ⟨?_, ⟨_, ⟨A, hA, rfl⟩, _, ⟨B, hB, rfl⟩, fun h => hAB (RankOne.map_conj_inj.1 h)⟩,
    fun h => hne ?_, fun h => ?_⟩
  · rintro _ ⟨E, hE, rfl⟩
    exact hR.conjSub_mem (hΔR hE) g
  · have := congrArg (fun S => conjSet S g⁻¹) h
    simpa only [conjSet_conjSet_inv, conjSet_eq_self hR] using this
  · have key : conjSet (conjSet Δ g) h = conjSet (conjSet Δ (g⁻¹ * h * g)) g := by
      rw [← conjSet_mul, ← conjSet_mul]
      congr 1
      group
    rw [key, ← conjSet_inter]
    rcases hTI (g⁻¹ * h * g) with h' | h'
    · left
      rw [h', conjSet, Set.image_empty]
    · right
      rw [h']

theorem conjSet_eq_of_mem [Finite G] {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ) {g : G} {B : Subgroup G}
    (hB : B ∈ Δ) (hBg : B ∈ conjSet Δ g) : conjSet Δ g = Δ := by
  have hfin : Δ.Finite := Set.toFinite Δ
  rcases hΔ.2.2.2 g with h | h
  · exact absurd (h ▸ (⟨hB, hBg⟩ : B ∈ Δ ∩ conjSet Δ g)) (Set.notMem_empty B)
  · have hsub : Δ ⊆ conjSet Δ g := fun x hx => (h.symm ▸ hx : x ∈ Δ ∩ conjSet Δ g).2
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (hfin.image _)).symm
    rw [conjSet, Set.ncard_image_of_injective _ fun _ _ h => RankOne.map_conj_inj.1 h]

@[expose] def IsPoint (Δ P : Set (Subgroup G)) : Prop := ∃ g : G, conjSet Δ g = P

section Points

variable {Δ : Set (Subgroup G)}

theorem isPoint_self (Δ : Set (Subgroup G)) : IsPoint Δ Δ := ⟨1, conjSet_one Δ⟩

theorem IsPoint.conj {P : Set (Subgroup G)} (hP : IsPoint Δ P) (g : G) :
    IsPoint Δ (conjSet P g) := by
  obtain ⟨h, rfl⟩ := hP
  exact ⟨g * h, conjSet_mul Δ g h⟩

theorem IsPoint.isTI (hR : IsRootClass R) (hΔ : IsTI R Δ) {P : Set (Subgroup G)}
    (hP : IsPoint Δ P) : IsTI R P := by
  obtain ⟨g, rfl⟩ := hP
  exact isTI_conjSet hR hΔ g

theorem IsPoint.isWeakTI (hR : IsRootClass R) (hΔ : IsTI R Δ) {P : Set (Subgroup G)}
    (hP : IsPoint Δ P) : IsWeakTI R P :=
  (hP.isTI hR hΔ).isWeakTI

theorem exists_isPoint_mem (hR : IsRootClass R) (hΔ : IsTI R Δ) {B : Subgroup G} (hB : B ∈ R) :
    ∃ P, IsPoint Δ P ∧ B ∈ P := by
  obtain ⟨A, hA, -⟩ := hΔ.2.1
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq (hΔ.1 hA) hB
  exact ⟨conjSet Δ g, ⟨g, rfl⟩, A, hA, rfl⟩

theorem IsPoint.eq_of_mem [Finite G] (hR : IsRootClass R) (hΔ : IsTI R Δ) {P Q : Set (Subgroup G)}
    (hP : IsPoint Δ P) (hQ : IsPoint Δ Q) {B : Subgroup G} (hBP : B ∈ P) (hBQ : B ∈ Q) :
    P = Q := by
  obtain ⟨g, rfl⟩ := hP
  obtain ⟨h, rfl⟩ := hQ
  have e : conjSet (conjSet Δ g) (h * g⁻¹) = conjSet Δ h := by
    rw [← conjSet_mul, inv_mul_cancel_right]
  rw [← e] at hBQ ⊢
  exact (conjSet_eq_of_mem (isTI_conjSet hR hΔ g) hBP hBQ).symm

end Points

theorem exists_ne_one_commute_of_le_normalizer [Finite G] {K H : Subgroup G}
    (hK : IsPGroup 2 K) (hH : IsPGroup 2 H) (hKH : K ≤ Subgroup.normalizer (H : Set G))
    (hne : H ≠ ⊥) : ∃ t ∈ H, t ≠ 1 ∧ ∀ k ∈ K, Commute k t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := K ⊔ H with hL
  have hLp : IsPGroup 2 L := hK.to_sup_of_normal_right' hH hKH
  have hHL : H ≤ L := le_sup_right
  have hnormL : ∀ x ∈ L, x ∈ Subgroup.normalizer (H : Set G) :=
    fun x hx => (sup_le hKH Subgroup.le_normalizer) hx
  have hnorm : (H.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hHL]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.1 (hnormL k hk) h).1 hh
  have hnil : Group.IsNilpotent L := hLp.isNilpotent
  have hne' : H.subgroupOf L ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hHL hx⟩ : L) ∈ H.subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne'))
  refine ⟨z.1, hz.1, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun k hk => ?_⟩
  have hc := Subgroup.mem_center_iff.1 hz.2 ⟨k, (le_sup_left : K ≤ L) hk⟩
  exact congrArg Subtype.val hc

theorem commutator_le_of_le_normalizer {X Y H : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (H : Set G)) (hY : Y ≤ H) : ⁅X, Y⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact H.mul_mem ((Subgroup.mem_normalizer_iff.1 (hX hx) y).1 (hY hy)) (H.inv_mem (hY hy))

theorem commutator_le_of_le_normalizer' {X Y H : Subgroup G} (hX : X ≤ H)
    (hY : Y ≤ Subgroup.normalizer (H : Set G)) : ⁅X, Y⁆ ≤ H := by
  rw [Subgroup.commutator_comm]
  exact commutator_le_of_le_normalizer hY hX

theorem commutatorElement_commutatorElement_mem {w b t : G} {T C : Subgroup G}
    (hw : w * w = 1) (hb : b * b = 1) (hT : ∀ s ∈ T, ∀ s' ∈ T, s * s' = s' * s)
    (hT2 : ∀ s ∈ T, s * s = 1) (hwT : w ∈ Subgroup.normalizer (T : Set G))
    (hbC : ∀ s ∈ T, ⁅b, s⁆ ∈ C) (hCT : C ≤ T)
    (hwC : ∀ c ∈ C, w * c = c * w) (hbC' : ∀ c ∈ C, b * c = c * b) (ht : t ∈ T) :
    ⁅⁅w, b⁆, t⁆ ∈ C := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hT2 t ht)
  have hσ : ∀ g : G, g * g = 1 → ∀ s s' : G, g * (s * s') * g = (g * s * g) * (g * s' * g) := by
    intro g hg s s'
    rw [show (g * s * g) * (g * s' * g) = g * s * (g * g) * s' * g by group, hg]
    group
  have hwT' : ∀ s ∈ T, w * s * w ∈ T := fun s hs => by
    have := (Subgroup.mem_normalizer_iff.1 hwT s).1 hs
    rwa [hwi] at this
  have hwc : ∀ c ∈ C, w * c * w = c := fun c hc => by rw [hwC c hc, mul_assoc, hw, mul_one]
  have hbc : ∀ c ∈ C, b * c * b = c := fun c hc => by rw [hbC' c hc, mul_assoc, hb, mul_one]
  obtain ⟨u, hu⟩ : ∃ u, u = b * t * b * t := ⟨_, rfl⟩
  have huC : u ∈ C := by
    have := hbC t ht
    rwa [commutatorElement_def, hbi, hti, ← hu] at this
  have huT : u ∈ T := hCT huC
  have e1 : b * t * b = u * t := by rw [hu, mul_assoc _ t t, hT2 t ht, mul_one]
  obtain ⟨v, hv⟩ : ∃ v, v = w * t * w * t := ⟨_, rfl⟩
  have hvT : v ∈ T := by rw [hv]; exact T.mul_mem (hwT' t ht) ht
  have e2 : w * t * w = v * t := by rw [hv, mul_assoc _ t t, hT2 t ht, mul_one]
  obtain ⟨u', hu'⟩ : ∃ u', u' = b * v * b * v := ⟨_, rfl⟩
  have hu'C : u' ∈ C := by
    have := hbC v hvT
    rwa [commutatorElement_def, hbi, inv_eq_of_mul_eq_one_right (hT2 v hvT), ← hu'] at this
  have hu'T : u' ∈ T := hCT hu'C
  have e3 : b * v * b = u' * v := by rw [hu', mul_assoc _ v v, hT2 v hvT, mul_one]
  have e4 : w * v * w = v := by
    have h1 : w * (w * t * w) * w = t := by
      rw [show w * (w * t * w) * w = (w * w) * t * (w * w) by group, hw]; group
    calc w * v * w = w * ((w * t * w) * t) * w := by rw [hv]
      _ = (w * (w * t * w) * w) * (w * t * w) := hσ w hw _ _
      _ = t * (v * t) := by rw [h1, e2]
      _ = v * t * t := by rw [← mul_assoc, hT t ht v hvT]
      _ = v := by rw [mul_assoc, hT2 t ht, mul_one]
  have hx : ⁅w, b⁆ * t * ⁅w, b⁆⁻¹ = w * (b * (w * (b * t * b) * w) * b) * w := by
    rw [commutatorElement_def, show (w * b * w⁻¹ * b⁻¹)⁻¹ = b * w * b⁻¹ * w⁻¹ by group, hwi, hbi]
    group
  have key : ⁅w, b⁆ * t * ⁅w, b⁆⁻¹ = u' * t := by
    have h2 : u * (u' * v * (u * t)) = u' * (v * t) := by
      calc u * (u' * v * (u * t)) = (u * (u' * v)) * u * t := by group
        _ = (u' * v) * u * u * t := by rw [hT u huT (u' * v) (T.mul_mem hu'T hvT)]
        _ = u' * (v * t) := by rw [mul_assoc (u' * v) u u, hT2 u huT, mul_one, mul_assoc]
    calc ⁅w, b⁆ * t * ⁅w, b⁆⁻¹ = w * (b * (w * (u * t) * w) * b) * w := by rw [hx, e1]
      _ = w * (b * (u * (v * t)) * b) * w := by rw [hσ w hw u t, hwc u huC, e2]
      _ = w * (u * (u' * v * (u * t))) * w := by
          rw [hσ b hb u (v * t), hσ b hb v t, hbc u huC, e3, e1]
      _ = w * (u' * (v * t)) * w := by rw [h2]
      _ = u' * (v * (v * t)) := by rw [hσ w hw u' (v * t), hσ w hw v t, hwc u' hu'C, e4, e2]
      _ = u' * t := by rw [← mul_assoc v v t, hT2 v hvT, one_mul]
  have : ⁅⁅w, b⁆, t⁆ = u' := by
    rw [commutatorElement_def ⁅w, b⁆ t, key, hti, mul_assoc, hT2 t ht, mul_one]
  rw [this]
  exact hu'C

theorem commuting_of_conjSub_eq [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {X C : Subgroup G} (hX : X ∈ R) (hC : C ∈ R) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1)
    (hxC : conjSub C x = C) : Commuting X C := by
  by_cases hXC : X = C
  · subst hXC
    exact hR.commuting_self hX
  rcases hR.rel X hX C hC hXC with h | h | h
  · exact h
  · exact absurd (h.eq_one_of_conjSub_eq hx hxC) hx1
  · exact absurd hxC (Sec3.conjSub_ne_of_special hR hiso hX hC h hx hx1)

theorem commuting_of_commute [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {X C : Subgroup G} (hX : X ∈ R) (hC : C ∈ R) {x t : G} (hx : x ∈ X) (hx1 : x ≠ 1)
    (ht : t ∈ C) (ht1 : t ≠ 1) (hxt : Commute x t) : Commuting X C := by
  refine commuting_of_conjSub_eq hR hiso hX hC hx hx1 ?_
  have hmem : t ∈ conjSub C x := by
    have := conj_mem_conjSub x ht
    rwa [hxt.eq, mul_inv_cancel_right] at this
  exact Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hC x) hC hmem ht ht1

theorem mul_self_of_mem_gen [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hnd : IsNondegenerate R) {P : Set (Subgroup G)} (hP : IsWeakTI R P) {s : G}
    (hs : s ∈ gen P) : s * s = 1 := by
  have hc := commuting_gen_of_isWeakTI_of hR hiso hnd hP
  refine (gen_induction (p := fun x => x ∈ gen P ∧ x * x = 1) hs
    (fun B hB y hy => ⟨le_gen hB hy, hR.mul_self B (hP.1 hB) y hy⟩) ⟨one_mem _, mul_one 1⟩
    ?_).2
  rintro y z ⟨hy, hyy⟩ ⟨hz, hzz⟩
  refine ⟨mul_mem hy hz, ?_⟩
  calc y * z * (y * z) = y * (z * y) * z := by group
    _ = y * (y * z) * z := by rw [(hc z hz y hy).eq]
    _ = 1 := by rw [← mul_assoc, hyy, one_mul, hzz]

section Dictionary

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ)
include hR hiso hnd hΩ hΔ

theorem gen_inf_gen_eq_bot {P Q : Set (Subgroup G)} (hP : IsPoint Δ P) (hQ : IsPoint Δ Q)
    (hPQ : P ≠ Q) : gen P ⊓ gen Q = ⊥ := by
  have hPw := hP.isWeakTI hR hΔ
  have hQw := hQ.isWeakTI hR hΔ
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  by_contra hx1
  obtain ⟨S, hS, -, hxS⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hPw subset_rfl hx.1 hx1
  obtain ⟨T, hT, -, hxT⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hQw subset_rfl hx.2 hx1
  have hST := Sec3.eq_of_mem_of_mem hR hiso (hPw.1 hS) (hQw.1 hT) hxS hxT hx1
  exact hPQ (IsPoint.eq_of_mem hR hΔ hP hQ hS (hST ▸ hT))

omit [Finite G] hiso hnd hΩ in
theorem gen_ne_bot {P : Set (Subgroup G)} (hP : IsPoint Δ P) : gen P ≠ ⊥ := by
  have hPw := hP.isWeakTI hR hΔ
  obtain ⟨A, hA, -⟩ := hPw.2.1
  intro h
  exact hR.ne_bot A (hPw.1 hA) (eq_bot_iff.2 ((le_gen hA).trans h.le))

theorem exists_commuting_of_mem_stabSet {P : Set (Subgroup G)} (hP : IsPoint Δ P)
    {X : Subgroup G} (hX : X ∈ R) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) (hxP : x ∈ stabSet P) :
    ∃ C ∈ P, Commuting X C := by
  have hPw := hP.isWeakTI hR hΔ
  have hK : IsPGroup 2 (Subgroup.zpowers x) :=
    (hR.isPGroup hX).to_le ((Subgroup.zpowers_le (H := X)).2 hx)
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((gen P : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).2 (Sec5.stabSet_le_normalizer_gen P hxP)
  obtain ⟨t, ht, ht1, hcomm⟩ := exists_ne_one_commute_of_le_normalizer hK
    (isPGroup_gen_of_isWeakTI hR hiso hnd hPw) hnorm (gen_ne_bot hR hΔ hP)
  obtain ⟨C, hC, -, htC⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hPw subset_rfl ht ht1
  exact ⟨C, hC, commuting_of_commute hR hiso hX (hPw.1 hC) hx hx1 htC ht1
    (hcomm x (Subgroup.mem_zpowers x))⟩

theorem exists_commuting_of_le_stabSet {P : Set (Subgroup G)} (hP : IsPoint Δ P)
    {X : Subgroup G} (hX : X ∈ R) (hXP : X ≤ stabSet P) : ∃ C ∈ P, Commuting X C := by
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
  exact exists_commuting_of_mem_stabSet hR hiso hnd hΩ hΔ hP hX hx hx1 (hXP hx)

theorem le_stabSet_of_mem_stabSet {P : Set (Subgroup G)} (hP : IsPoint Δ P) {X : Subgroup G}
    (hX : X ∈ R) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) (hxP : x ∈ stabSet P) : X ≤ stabSet P := by
  obtain ⟨C, hC, hXC⟩ := exists_commuting_of_mem_stabSet hR hiso hnd hΩ hΔ hP hX hx hx1 hxP
  exact Sec5.le_stabSet_of_commuting hR (hP.isWeakTI hR hΔ) hX hC hXC

theorem not_le_stabSet_of_opposite {P : Set (Subgroup G)} (hP : IsPoint Δ P) {X Y : Subgroup G}
    (hX : X ∈ R) (hY : Y ∈ P) (hXY : Opposite X Y) : ¬ X ≤ stabSet P := by
  have hPw := hP.isWeakTI hR hΔ
  intro h
  obtain ⟨C, hC, hXC⟩ := exists_commuting_of_le_stabSet hR hiso hnd hΩ hΔ hP hX h
  have hCY : Y ≠ C := by
    rintro rfl
    exact hXY.not_commuting (hR.ne_bot X hX) hXC
  exact not_commuting_of_opposite_of_mem_lambdaSet hR hX hXY
    (Sec5.mem_lambdaSet hR hiso hnd hΩ hPw hY hC hCY) hXC

theorem commuting_of_le_stabSet {P Q : Set (Subgroup G)} (hP : IsPoint Δ P) (hQ : IsPoint Δ Q)
    (hPQ : P ≠ Q) {X Y : Subgroup G} (hX : X ∈ P) (hY : Y ∈ Q) (hXQ : X ≤ stabSet Q)
    (hYP : Y ≤ stabSet P) : Commuting X Y := by
  have hPw := hP.isWeakTI hR hΔ
  have hQw := hQ.isWeakTI hR hΔ
  have hXR := hPw.1 hX
  have hYR := hQw.1 hY
  have hXY : X ≠ Y := by
    rintro rfl
    exact hPQ (IsPoint.eq_of_mem hR hΔ hP hQ hX hY)
  rcases hR.rel X hXR Y hYR hXY with h | h | h
  · exact h
  · exact absurd hXQ (not_le_stabSet_of_opposite hR hiso hnd hΩ hΔ hQ hXR hY h)
  · exfalso
    apply h.commutator_ne_bot hR
    rw [eq_bot_iff, ← gen_inf_gen_eq_bot hR hiso hnd hΩ hΔ hP hQ hPQ]
    exact le_inf (commutator_le_of_le_normalizer' (le_gen hX)
        (hYP.trans (Sec5.stabSet_le_normalizer_gen P)))
      (commutator_le_of_le_normalizer (hXQ.trans (Sec5.stabSet_le_normalizer_gen Q)) (le_gen hY))

theorem special_of_le_stabSet {Q : Set (Subgroup G)} (hQ : IsPoint Δ Q) {X Y : Subgroup G}
    (hX : X ∈ R) (hY : Y ∈ Q) (hXQ : X ≤ stabSet Q) (hXY : ¬ Commuting X Y) :
    Special R X Y ∧ ⁅X, Y⁆ ∈ Q := by
  have hQw := hQ.isWeakTI hR hΔ
  have hYR := hQw.1 hY
  have hne : X ≠ Y := by
    rintro rfl
    exact hXY (hR.commuting_self hX)
  have hs : Special R X Y := by
    rcases hR.rel X hX Y hYR hne with h | h | h
    · exact absurd h hXY
    · exact absurd hXQ (not_le_stabSet_of_opposite hR hiso hnd hΩ hΔ hQ hX hY h)
    · exact h
  exact ⟨hs, Sec5.mem_of_le_gen hR hiso hnd hΩ hQw subset_rfl hs.1
    (commutator_le_of_le_normalizer (hXQ.trans (Sec5.stabSet_le_normalizer_gen Q)) (le_gen hY))⟩

theorem le_stabSet_of_forall_not_opposite {P : Set (Subgroup G)} (hP : IsPoint Δ P)
    {B : Subgroup G} (hB : B ∈ R) (h : ∀ C ∈ P, ¬ Opposite B C) : B ≤ stabSet P := by
  have hPw := hP.isWeakTI hR hΔ
  intro b hb
  rw [mem_stabSet]
  have hP' : IsPoint Δ (conjSet P b) := hP.conj b
  have hP'w := hP'.isWeakTI hR hΔ
  have hcomm : ∀ A ∈ P, Commuting A (conjSub A b) := by
    intro A hA
    have hAR := hPw.1 hA
    by_cases hAB : A = B
    · rw [hAB, conjSub_of_mem hb]
      exact hR.commuting_self hB
    rcases hR.rel A hAR B hB hAB with hc | ho | hs
    · rw [conjSub_of_forall_commute fun a ha => (hc a ha b hb).symm]
      exact hR.commuting_self hAR
    · exact absurd ho.symm (h A hA)
    · exact commuting_conjSub_of_special hR hAR hs hb
  have h1 : gen P ≤ Subgroup.normalizer ((gen (conjSet P b) : Subgroup G) : Set G) :=
    (gen_le fun A hA => Sec5.le_stabSet_of_commuting hR hP'w (hPw.1 hA) ⟨A, hA, rfl⟩
      (hcomm A hA)).trans (Sec5.stabSet_le_normalizer_gen _)
  have h2 : gen (conjSet P b) ≤ Subgroup.normalizer ((gen P : Subgroup G) : Set G) := by
    refine (gen_le ?_).trans (Sec5.stabSet_le_normalizer_gen P)
    rintro _ ⟨A, hA, rfl⟩
    exact Sec5.le_stabSet_of_commuting hR hPw (hR.conjSub_mem (hPw.1 hA) b) hA (hcomm A hA).symm
  by_contra hne
  have hbot := gen_inf_gen_eq_bot hR hiso hnd hΩ hΔ hP' hP hne
  have hc : Commuting (gen (conjSet P b)) (gen P) := by
    rw [commuting_iff_commutator_eq_bot, eq_bot_iff, ← hbot]
    exact le_inf (commutator_le_of_le_normalizer' le_rfl h1)
      (commutator_le_of_le_normalizer h2 le_rfl)
  obtain ⟨A, hA, -⟩ := hPw.2.1
  have hA' : conjSub A b ∈ P := Sec5.mem_of_commuting_gen hR hiso hnd hΩ hPw
    (hR.conjSub_mem (hPw.1 hA) b) (hc.mono (le_gen ⟨A, hA, rfl⟩) le_rfl)
  exact hne (IsPoint.eq_of_mem hR hΔ hP' hP ⟨A, hA, rfl⟩ hA')

theorem commutator_mem_of_opposite {P Q : Set (Subgroup G)} (hP : IsPoint Δ P)
    (hQ : IsPoint Δ Q) {A B C : Subgroup G} (hA : A ∈ P) (hC : C ∈ P) (hB : B ∈ Q)
    (hAB : Opposite A B) (hBC : Special R B C) : ⁅B, C⁆ ∈ Q := by
  have hPw := hP.isWeakTI hR hΔ
  have hAR := hPw.1 hA
  have hCR := hPw.1 hC
  have hBR := (hQ.isWeakTI hR hΔ).1 hB
  have hAC : A ≠ C := by
    rintro rfl
    exact Special.not_opposite hR hBR hBC hAB.symm
  have hCl : C ∈ lambdaSet R A := Sec5.mem_lambdaSet hR hiso hnd hΩ hPw hA hC hAC
  have hBCR : ⁅B, C⁆ ∈ R := hBC.1
  have hnorm : ∀ x ∈ A ⊔ B, conjSub (C ⊔ ⁅B, C⁆) x = C ⊔ ⁅B, C⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hAR hBR hAB hCl ⟨hCR, hBC⟩ hx
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hAR
  obtain ⟨b, hb, -, hab⟩ := hAB.2.1 a ha ha1
  have hx : a⁻¹ * b ∈ A ⊔ B :=
    (A ⊔ B).mul_mem (Subgroup.mem_sup_left (A.inv_mem ha)) (Subgroup.mem_sup_right hb)
  have hAx : conjSub A (a⁻¹ * b) = B := by
    rw [conjSub_mul, hab, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hCxQ : conjSub C (a⁻¹ * b) ∈ Q := by
    have h1 : conjSub C (a⁻¹ * b) ∈ conjSet P (a⁻¹ * b) := ⟨C, hC, rfl⟩
    rwa [IsPoint.eq_of_mem hR hΔ (hP.conj _) hQ ⟨A, hA, hAx⟩ hB] at h1
  have hCxN : conjSub C (a⁻¹ * b) ≤ C ⊔ ⁅B, C⁆ := by
    rw [← hnorm _ hx]
    exact Subgroup.map_mono le_sup_left
  have hCxB : Commuting (conjSub C (a⁻¹ * b)) B := by
    have := ((Sec5.commuting_of_mem hR hiso hnd hPw hC hA).conjSub (a⁻¹ * b))
    rwa [hAx] at this
  have heq : conjSub C (a⁻¹ * b) = ⁅B, C⁆ := by
    by_contra hne
    have hsup := sup_eq_of_le_of_commuting hR hiso hCR hBCR (hR.conjSub_mem hCR _) hBCR
      hBC.2.2.symm hCxN le_sup_right hne
    apply hBC.not_commuting hR
    have hBN : Commuting B (conjSub C (a⁻¹ * b) ⊔ ⁅B, C⁆) :=
      Commuting.sup_right hCxB.symm hBC.2.1.symm
    rw [hsup] at hBN
    exact hBN.mono le_rfl le_sup_left
  rwa [heq] at hCxQ

theorem le_stabSet_or_le_stabSet_of_special {P Q : Set (Subgroup G)} (hP : IsPoint Δ P)
    (hQ : IsPoint Δ Q) {X Y : Subgroup G} (hX : X ∈ P) (hY : Y ∈ Q) (hXY : Special R X Y) :
    X ≤ stabSet Q ∨ Y ≤ stabSet P := by
  have hPw := hP.isWeakTI hR hΔ
  have hXR := hPw.1 hX
  have hYR := (hQ.isWeakTI hR hΔ).1 hY
  by_cases hex : ∃ A ∈ Q, Opposite X A
  · obtain ⟨A, hA, hXA⟩ := hex
    right
    have hmem : ⁅X, Y⁆ ∈ P := commutator_mem_of_opposite hR hiso hnd hΩ hΔ hQ hP hA hY hX
      hXA.symm hXY
    exact Sec5.le_stabSet_of_commuting hR hPw hYR hmem hXY.2.2.symm
  · left
    push Not at hex
    exact le_stabSet_of_forall_not_opposite hR hiso hnd hΩ hΔ hQ hXR fun A hA => hex A hA

theorem opposite_of_not_le_stabSet {P Q : Set (Subgroup G)} (hP : IsPoint Δ P)
    (hQ : IsPoint Δ Q) {X Y : Subgroup G} (hX : X ∈ P) (hY : Y ∈ Q) (hXQ : ¬ X ≤ stabSet Q)
    (hYP : ¬ Y ≤ stabSet P) : Opposite X Y := by
  have hQw := hQ.isWeakTI hR hΔ
  have hXR := (hP.isWeakTI hR hΔ).1 hX
  have hYR := hQw.1 hY
  have hXY : X ≠ Y := by
    rintro rfl
    exact hXQ (Sec5.le_stabSet_of_commuting hR hQw hYR hY (hR.commuting_self hYR))
  rcases hR.rel X hXR Y hYR hXY with h | h | h
  · exact absurd (Sec5.le_stabSet_of_commuting hR hQw hXR hY h) hXQ
  · exact h
  · rcases le_stabSet_or_le_stabSet_of_special hR hiso hnd hΩ hΔ hP hQ hX hY h with h' | h'
    · exact absurd h' hXQ
    · exact absurd h' hYP

theorem commutator_gen_eq {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C Y : Subgroup G}
    (hC : C ∈ P) (hY : Y ∈ lambdaSet R C) (hYP : Y ∉ P) : ⁅gen P, Y⁆ = C := by
  have hPw := hP.isWeakTI hR hΔ
  have hCR := hPw.1 hC
  have hYR : Y ∈ R := hY.1.1
  refine le_antisymm (Sec5.commutator_gen_le hR hiso hnd hΩ hPw hC hY) ?_
  obtain ⟨D, hD, hYD⟩ : ∃ D ∈ P, ¬ Commuting Y D := by
    by_contra! h
    exact hYP (Sec5.mem_of_commuting_gen hR hiso hnd hΩ hPw hYR
      (commuting_iff_le_centralizer.2 (gen_le fun D hD => commuting_iff_le_centralizer.1
        (h D hD))))
  have hYst : Y ≤ stabSet P := Sec5.le_stabSet_of_commuting hR hPw hYR hC hY.1.2.2.symm
  obtain ⟨hs, -⟩ := special_of_le_stabSet hR hiso hnd hΩ hΔ hP hYR hD hYst hYD
  have hle : ⁅D, Y⁆ ≤ C :=
    (Subgroup.commutator_mono (le_gen hD) le_rfl).trans
      (Sec5.commutator_gen_le hR hiso hnd hΩ hPw hC hY)
  rw [← QD.eq_of_le_of_mem hR hiso hs.symm.1 hCR hle]
  exact Subgroup.commutator_mono (le_gen hD) le_rfl

theorem exists_mem_lambdaSet_of_le_stabSet {P : Set (Subgroup G)} (hP : IsPoint Δ P)
    {B : Subgroup G} (hB : B ∈ R) (hBP : B ∉ P) (hBst : B ≤ stabSet P) :
    ∃ Z ∈ P, B ∈ lambdaSet R Z := by
  have hPw := hP.isWeakTI hR hΔ
  obtain ⟨D, hD, hBD⟩ : ∃ D ∈ P, ¬ Commuting B D := by
    by_contra! h
    exact hBP (Sec5.mem_of_commuting_gen hR hiso hnd hΩ hPw hB
      (commuting_iff_le_centralizer.2 (gen_le fun D hD => commuting_iff_le_centralizer.1
        (h D hD))))
  obtain ⟨hs, hmem⟩ := special_of_le_stabSet hR hiso hnd hΩ hΔ hP hB hD hBst hBD
  exact ⟨_, hmem, (mem_lambdaSet_commutator hR hiso hB (hPw.1 hD) hs).1⟩

theorem le_stabSet_of_mem_lambdaSet {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C B : Subgroup G}
    (hC : C ∈ P) (hB : B ∈ lambdaSet R C) (hBP : B ∉ P) {P' : Set (Subgroup G)}
    (hP' : IsPoint Δ P') (hCP' : C ≤ stabSet P') : B ≤ stabSet P' := by
  have hPw := hP.isWeakTI hR hΔ
  have hP'w := hP'.isWeakTI hR hΔ
  have hCR : C ∈ R := hPw.1 hC
  have hBR : B ∈ R := hB.1.1
  have hCB : Commuting C B := hB.1.2.2
  obtain ⟨Q, hQ, hBQ⟩ := exists_isPoint_mem hR hΔ hBR
  have hQw := hQ.isWeakTI hR hΔ
  by_cases hP'P : P' = P
  · subst hP'P
    exact Sec5.le_stabSet_of_commuting hR hPw hBR hC hCB.symm
  by_cases hP'Q : P' = Q
  · subst hP'Q
    exact Sec5.le_stabSet_of_commuting hR hQw hBR hBQ (hR.commuting_self hBR)
  obtain ⟨W, hW, hCW⟩ := exists_commuting_of_le_stabSet hR hiso hnd hΩ hΔ hP' hCR hCP'
  have hWR := hP'w.1 hW
  by_contra hBP'
  have hBW : ¬ Commuting B W := fun h => hBP' (Sec5.le_stabSet_of_commuting hR hP'w hBR hW h)
  have hne : B ≠ W := fun e => hBW (e ▸ hR.commuting_self hBR)
  have hQP : Q ≠ P := fun e => hBP (e ▸ hBQ)
  rcases hR.rel B hBR W hWR hne with h | h | h
  · exact hBW h
  · exact not_commuting_of_opposite_of_mem_lambdaSet hR hWR h.symm (mem_lambdaSet_comm hCR hB)
      hCW.symm
  rcases le_stabSet_or_le_stabSet_of_special hR hiso hnd hΩ hΔ hQ hP' hBQ hW h with h' | h'
  · exact hBP' h'
  obtain ⟨hs, hZQ⟩ := special_of_le_stabSet hR hiso hnd hΩ hΔ hQ hWR hBQ h' fun h'' => hBW h''.symm
  have hZR : ⁅W, B⁆ ∈ R := hs.1
  have hZB : ⁅W, B⁆ ≠ B := fun e =>
    hs.symm.ne_commutator hR (by rw [Subgroup.commutator_comm]; exact e.symm)
  have hWst : W ≤ stabSet P := Sec5.le_stabSet_of_commuting hR hPw hWR hC hCW.symm
  have hL1 : ⁅gen P, B⁆ = C := commutator_gen_eq hR hiso hnd hΩ hΔ hP hC hB hBP
  have key : ⁅⁅W, B⁆, gen P⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro z hz t ht
    obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hWR
    obtain ⟨b, hb, rfl⟩ := (bijOn_commutator hR hiso hWR hBR hs hw hw1).surjOn hz
    refine commutatorElement_commutatorElement_mem (T := gen P) (hR.mul_self W hWR w hw)
      (hR.mul_self B hBR b hb) (commuting_gen_of_isWeakTI_of hR hiso hnd hPw)
      (fun s hs => ?_) (Sec5.stabSet_le_normalizer_gen P (hWst hw)) (fun s hs => ?_)
      (le_gen hC) (fun c hc => (hCW c hc w hw).symm.eq) (fun c hc => (hCB c hc b hb).symm.eq) ht
    · exact mul_self_of_mem_gen hR hiso hnd hPw hs
    · rw [← hL1, ← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hs hb)
  have hZC : Commuting ⁅W, B⁆ C := by
    refine (commuting_iff_le_centralizer.2 ?_).symm
    exact QD.commutator_le_of_le (commuting_iff_le_centralizer.1 hCW)
      (commuting_iff_le_centralizer.1 hCB)
  have hZP : ⁅W, B⁆ ∉ P := fun h => hQP (IsPoint.eq_of_mem hR hΔ hQ hP hZQ h)
  have hZst : ⁅W, B⁆ ≤ stabSet P := Sec5.le_stabSet_of_commuting hR hPw hZR hC hZC
  obtain ⟨Y, hY, hZY⟩ := exists_mem_lambdaSet_of_le_stabSet hR hiso hnd hΩ hΔ hP hZR hZP hZst
  have hY' : ⁅gen P, ⁅W, B⁆⁆ = Y := commutator_gen_eq hR hiso hnd hΩ hΔ hP hY hZY hZP
  have hYC : Y = C := QD.eq_of_le_of_mem hR hiso (hPw.1 hY) hCR
    (by rw [← hY', Subgroup.commutator_comm]; exact key)
  rw [hYC] at hZY
  have hCQ : C ∉ Q := fun h => hQP (IsPoint.eq_of_mem hR hΔ hQ hP h hC)
  have e1 := commutator_gen_eq hR hiso hnd hΩ hΔ hQ hZQ (mem_lambdaSet_comm hCR hZY) hCQ
  have e2 := commutator_gen_eq hR hiso hnd hΩ hΔ hQ hBQ (mem_lambdaSet_comm hCR hB) hCQ
  exact hZB (e1.symm.trans e2)

theorem eq_of_forall_le_stabSet_iff {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C Z : Subgroup G}
    (hC : C ∈ P) (hZ : Z ∈ P)
    (h : ∀ P', IsPoint Δ P' → (C ≤ stabSet P' ↔ Z ≤ stabSet P')) : C = Z := by
  have hPw := hP.isWeakTI hR hΔ
  have key : ∀ {X Y : Subgroup G}, X ∈ P → Y ∈ P →
      (∀ P', IsPoint Δ P' → Y ≤ stabSet P' → X ≤ stabSet P') → omegaSet R X ⊆ omegaSet R Y := by
    intro X Y hX hY hXY E ⟨hER, hXE⟩
    refine ⟨hER, ?_⟩
    obtain ⟨Q, hQ, hEQ⟩ := exists_isPoint_mem hR hΔ hER
    exact opposite_of_not_le_stabSet hR hiso hnd hΩ hΔ hP hQ hY hEQ
      (fun hYQ => not_le_stabSet_of_opposite hR hiso hnd hΩ hΔ hQ (hPw.1 hX) hEQ hXE
        (hXY Q hQ hYQ))
      (not_le_stabSet_of_opposite hR hiso hnd hΩ hΔ hP hER hX hXE.symm)
  exact hΩ Z (hPw.1 hZ) C (hPw.1 hC) (Set.Subset.antisymm (key hC hZ fun P' hP' => (h P' hP').2)
    (key hZ hC fun P' hP' => (h P' hP').1))

end Dictionary

end Linear

end CFSG.Timmesfeld.ARS
