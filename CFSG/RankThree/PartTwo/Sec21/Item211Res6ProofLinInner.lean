module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofField
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofDInn

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open CFSG.Assembly (IsElemAbelian)
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section LinInner

variable {K : Type} [Field K]

instance innP_normal : (innP K).Normal :=
  ⟨fun _ hn g => conj_mem_range_conj' g hn⟩

theorem exists_central_involution_inf {M : Type*} [Group M] [Finite M] {T R : Subgroup M}
    (hT2 : IsPGroup 2 T) (hRT : R ≤ T) (hRn : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R) (hR : R ≠ ⊥) :
    ∃ x ∈ R, x ≠ 1 ∧ x ^ 2 = 1 ∧ ∀ t ∈ T, t * x = x * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT2.isNilpotent
  set R' := R.subgroupOf T with hR'
  have hR'n : R'.Normal := ⟨fun a ha b => by
    rw [hR', Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hRn b b.2 a ha⟩
  have hR'1 : R' ≠ ⊥ := by
    intro h
    apply hR
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRT hr⟩ : T) ∈ R' := by rw [hR', Subgroup.mem_subgroupOf]; exact hr
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hQ := Group.IsNilpotent.inf_center_ne_bot_of_normal hR'1
  obtain ⟨q, hqQ, hq1, hq2, -⟩ := exists_central_involution (T := R' ⊓ Subgroup.center T)
    (hT2.to_subgroup _) hQ
  refine ⟨(q : M), ?_, ?_, ?_, ?_⟩
  · have := (Subgroup.mem_inf.mp hqQ).1
    rwa [hR', Subgroup.mem_subgroupOf] at this
  · exact fun h => hq1 (Subtype.ext h)
  · simpa using congrArg Subtype.val hq2
  · intro t ht
    have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hqQ).2 ⟨t, ht⟩
    simpa using congrArg Subtype.val this

theorem outerCentConcl_of_inf_ne_bot [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    (hK3 : Nat.card K % 3 = 1) {D T : Subgroup (MulAut (projectiveSL 3 K))}
    (hDe : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) (hT2 : IsPGroup 2 T)
    (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut (projectiveSL 3 K))))
    (hnab : ¬ (∀ a ∈ innP K ⊓ Subgroup.centralizer
        ((T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) : Set (MulAut (projectiveSL 3 K))),
      ∀ b ∈ innP K ⊓ Subgroup.centralizer
        ((T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) : Set (MulAut (projectiveSL 3 K))),
      a * b = b * a))
    (hR : T ⊓ innP K ≠ ⊥) : OuterCentConcl (innP K) T := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hK2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp3
  have : Finite (MulAut (projectiveSL 3 K)) :=
    Finite.of_injective (fun σ : MulAut (projectiveSL 3 K) => (σ : projectiveSL 3 K → _))
      (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨x, hxR, hx1, hx2, hxc⟩ := exists_central_involution_inf hT2 inf_le_left
    (fun t ht r hr => ⟨T.mul_mem (T.mul_mem ht hr.1) (T.inv_mem ht),
      conj_mem_range_conj' t hr.2⟩) hR
  obtain ⟨hxT, ⟨y, rfl⟩⟩ := Subgroup.mem_inf.mp hxR
  have hy2 : y ^ 2 = 1 := conj_injective_three (by rw [map_pow, hx2, map_one])
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨X₀, hX₀2, hX₀⟩ : ∃ X₀ : SL(3, K), X₀ ^ 2 = 1 ∧ proj 3 K X₀ = y := by
    have hAe : IsElemAbelian 2 (Subgroup.zpowers y) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨m, rfl⟩⟩ := a
        obtain ⟨_, ⟨n, rfl⟩⟩ := b
        simp only [Subgroup.coe_mul]
        rw [← zpow_add, ← zpow_add, add_comm]
      · rintro _ ⟨m, rfl⟩
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy2, one_zpow]
    obtain ⟨X₀, hX₀, hX₀x⟩ := CFSG.Quasithin.E22S.exists_invLift hAe (Subgroup.mem_zpowers y)
    exact ⟨X₀, hX₀.2, hX₀x⟩
  have hX₀1 : X₀ ≠ 1 := fun h => hy1 (by rw [← hX₀, h, map_one])
  obtain ⟨g, hg⟩ := exists_frame_sZero hp2 hX₀2 hX₀1
  set a : MulAut (projectiveSL 3 K) := MulAut.conj (proj 3 K g) with ha
  set κ := (MulAut.conj a).toMonoidHom with hκ
  have hκapp : ∀ u, κ u = a * u * a⁻¹ := fun u => rfl
  have hκinj : Function.Injective κ := (MulAut.conj a).injective
  have hκI : ∀ u ∈ innP K, κ u ∈ innP K := fun u hu => conj_mem_range_conj' a hu
  have hκx : κ (MulAut.conj y) = xZero := by
    rw [hκapp, ha, mul_conj_mul_inv', MulAut.conj_apply, ← hX₀, ← map_inv, ← map_mul,
      ← map_mul, hg]
    rfl
  set T' := T.map κ with hT'
  refine outerCentConcl_of_conj a ?_
  have hT'2 : IsPGroup 2 T' := hT2.map κ
  have hX : xZero ∈ T' := ⟨_, hxT, hκx⟩
  have hXc : ∀ t ∈ T', t * xZero = xZero * t := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← hκx, ← map_mul, ← map_mul, hxc t ht]
  have hnab' : ¬ (∀ u ∈ innP K ⊓ Subgroup.centralizer
        ((T' ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) : Set (MulAut (projectiveSL 3 K))),
      ∀ v ∈ innP K ⊓ Subgroup.centralizer
        ((T' ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) : Set (MulAut (projectiveSL 3 K))),
      u * v = v * u) := by
    intro hall
    apply hnab
    have hmem : ∀ u ∈ innP K ⊓ Subgroup.centralizer
        ((T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) : Set (MulAut (projectiveSL 3 K))),
        κ u ∈ innP K ⊓ Subgroup.centralizer
          ((T' ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) :
            Set (MulAut (projectiveSL 3 K))) := by
      intro u hu
      obtain ⟨huI, huC⟩ := Subgroup.mem_inf.mp hu
      refine Subgroup.mem_inf.mpr ⟨hκI u huI, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨⟨t, ht, rfl⟩, hwI⟩ := Subgroup.mem_inf.mp hw
      have htI : t ∈ innP K := by
        have := conj_mem_range_conj' a⁻¹ hwI
        rwa [hκapp, show a⁻¹ * (a * t * a⁻¹) * a⁻¹⁻¹ = t by group] at this
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp huC t ⟨ht, htI⟩]
    intro u hu v hv
    apply hκinj
    rw [map_mul, map_mul]
    exact hall _ (hmem u hu) _ (hmem v hv)
  obtain ⟨d, hdD, hdI, hd1⟩ := exists_mem_inf_range_ne_one hK3 hDe hD9
  have hdC : κ d ∈ innP K ⊓ Subgroup.centralizer (T' : Set (MulAut (projectiveSL 3 K))) := by
    refine Subgroup.mem_inf.mpr ⟨hκI d hdI, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hTD ht) d hdD).symm]
  have hd1' : κ d ≠ 1 := fun h => hd1 (hκinj (by rw [h, map_one]))
  have hd3 : κ d ^ 3 = 1 := by rw [← map_pow, hDe.2 d hdD, map_one]
  by_cases hD : ∃ t ∈ T', ProjectivePlane.linearFieldPart K (le_refl 3) t = 1 ∧
      ∃ A : SL(2, K), t (iota A) ≠ iota A
  · obtain ⟨t, ht, hφ, hmove⟩ := hD
    exact outerCentConcl_of_dihedral hK2 hT'2 hX hXc hnab' hdC hd1' hd3 ht hφ hmove
  · push Not at hD
    exact outerCentConcl_of_field hp3 hX hXc hD

end LinInner

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
