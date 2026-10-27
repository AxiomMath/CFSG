module

public import CFSG.Milestones.ASVolI.C135.Coords
public import CFSG.Milestones.ASVolI.C135.Syl
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Cent

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (slNat slNat_surjective dualHom dualHom_dualHom coe_dualHom
  moduleAct_true_eq le_normalizer_centerOf)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Irred

variable {Q L W₁ W₂ : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
  {βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F)}
  {β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)} {β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)}

theorem burnsideC135_W₁_irred (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    {K : Subgroup G} (hUK : centerOf (Q) ≤ K) (hKW : K ≤ W₁)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) : K = centerOf (Q) ∨ K = W₁ := by
  classical
  let Y : AddSubgroup (Fin 3 → F) :=
    { carrier := {y | ∃ k : ↥W₁, (k : G) ∈ K ∧ Multiplicative.toAdd (β₁ k) = y}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, K.mul_mem ha hb, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, K.one_mem, by rw [map_one]; rfl⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, K.inv_mem ha, by rw [map_inv, toAdd_inv]⟩ }
  have hYinv : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F) (v : Fin 3 → F), v ∈ Y →
      (Matrix.SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ Y := by
    rintro i j hij b _ ⟨k, hk, rfl⟩
    obtain ⟨l, hl⟩ := hD.alpha_onto (dualHom (Matrix.SpecialLinearGroup.transvection hij b))
    have hmem : (l : G) * k * (l : G)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hD.norm₁ l.2) _).mp k.2
    refine ⟨⟨_, hmem⟩, hLK l l.2 k hk, ?_⟩
    rw [hD.dual₁_act l k ⟨_, hmem⟩ rfl, hl]
    rw [show (((dualHom (Matrix.SpecialLinearGroup.transvection hij b))⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose =
        ((dualHom (dualHom (Matrix.SpecialLinearGroup.transvection hij b)) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) from rfl,
      dualHom_dualHom]
  by_cases hY : ∃ y ∈ Y, y ≠ 0
  · obtain ⟨y, hyY, hy0⟩ := hY
    have htop := CFSG.Quasithin.H13.Ch4.eq_top_of_transvection_invariant Y hYinv hyY hy0
    right
    refine le_antisymm hKW fun w hw => ?_
    have h1 : Multiplicative.toAdd (β₁ ⟨w, hw⟩) ∈ Y := by rw [htop]; exact AddSubgroup.mem_top _
    obtain ⟨k, hk, hkw⟩ := h1
    have h2 : k⁻¹ * ⟨w, hw⟩ ∈ β₁.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : β₁ k = β₁ ⟨w, hw⟩ := Multiplicative.toAdd.injective hkw
      rw [this, inv_mul_cancel]
    rw [hD.dual₁_ker, Subgroup.mem_subgroupOf] at h2
    have h3 : (k : G)⁻¹ * w ∈ K := hUK (by simpa using h2)
    have e : w = (k : G) * ((k : G)⁻¹ * w) := by group
    rw [e]
    exact K.mul_mem hk h3
  · push Not at hY
    left
    refine le_antisymm (fun k hk => ?_) hUK
    have h1 := hY _ ⟨⟨k, hKW hk⟩, hk, rfl⟩
    have h2 : (⟨k, hKW hk⟩ : ↥W₁) ∈ β₁.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective h1
    rw [hD.dual₁_ker, Subgroup.mem_subgroupOf] at h2
    exact h2

theorem burnsideC135_W₁_invariant (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    {S₀ : Subgroup G} (hS₀L : S₀ ≤ Subgroup.normalizer (L : Set G))
    (hS₀U : S₀ ≤ Subgroup.normalizer (centerOf (Q) : Set G)) {q₀ : G} (hq₀W : q₀ ∈ W₁)
    (hq₀U : q₀ ∉ centerOf (Q))
    (hq₀S : ∀ s ∈ S₀, s * q₀ * s⁻¹ * q₀⁻¹ ∈ centerOf (Q)) :
    S₀ ≤ Subgroup.normalizer (W₁ : Set G) := by
  have key : ∀ s ∈ S₀, ∀ w ∈ W₁, s * w * s⁻¹ ∈ W₁ := by
    intro s hs
    let K : Subgroup G := W₁ ⊓ W₁.comap (MulAut.conj s).toMonoidHom
    have hmemK : ∀ w, w ∈ K ↔ w ∈ W₁ ∧ s * w * s⁻¹ ∈ W₁ := fun w => Iff.rfl
    have hUK : centerOf (Q) ≤ K := fun u hu =>
      (hmemK u).mpr ⟨hD.le₁ hu, hD.le₁ ((Subgroup.mem_normalizer_iff.mp (hS₀U hs) u).mp hu)⟩
    have hLK : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K := by
      intro l hl k hk
      obtain ⟨hk1, hk2⟩ := (hmemK k).mp hk
      refine (hmemK _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hD.norm₁ hl) k).mp hk1, ?_⟩
      have hsl : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hS₀L hs) l).mp hl
      have e : s * (l * k * l⁻¹) * s⁻¹ = (s * l * s⁻¹) * (s * k * s⁻¹) * (s * l * s⁻¹)⁻¹ := by
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hD.norm₁ hsl) _).mp hk2
    have hq₀K : q₀ ∈ K := by
      refine (hmemK q₀).mpr ⟨hq₀W, ?_⟩
      have e : s * q₀ * s⁻¹ = (s * q₀ * s⁻¹ * q₀⁻¹) * q₀ := by group
      rw [e]
      exact W₁.mul_mem (hD.le₁ (hq₀S s hs)) hq₀W
    rcases burnsideC135_W₁_irred hD hUK inf_le_left hLK with h | h
    · exact absurd (h ▸ hq₀K) hq₀U
    · intro w hw
      rw [← h] at hw
      exact ((hmemK w).mp hw).2
  exact burnsideC135_le_normalizer_of_conj key

end Irred

theorem burnsideC135_exists_fixed {S₀ Q U : Subgroup G} (hS₀ : IsPGroup 2 S₀) (hQS : Q ≤ S₀)
    (hS₀Q : S₀ ≤ Subgroup.normalizer (Q : Set G)) (hS₀U : S₀ ≤ Subgroup.normalizer (U : Set G))
    (hne : ¬ Q ≤ U) : ∃ q ∈ Q, q ∉ U ∧ ∀ s ∈ S₀, s * q * s⁻¹ * q⁻¹ ∈ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥S₀ := U.subgroupOf S₀ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hS₀U g.2) n).mp hn
  set π := QuotientGroup.mk' N with hπ
  have hp : IsPGroup 2 (↥S₀ ⧸ N) := (hS₀.of_equiv (MulEquiv.refl _)).to_quotient N
  have : Group.IsNilpotent (↥S₀ ⧸ N) := hp.isNilpotent
  set Qb : Subgroup (↥S₀ ⧸ N) := (Q.subgroupOf S₀).map π with hQb
  have hQn : (Q.subgroupOf S₀).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hS₀Q g.2) n).mp hn
  have : Qb.Normal := hQn.map π (QuotientGroup.mk'_surjective N)
  have hQb : Qb ≠ ⊥ := by
    intro h
    apply hne
    intro q hq
    have h1 : π ⟨q, hQS hq⟩ ∈ Qb := ⟨⟨q, hQS hq⟩, hq, rfl⟩
    rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hQb
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨hzQ, hzZ⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨q, hq0, hqz⟩ := hzQ
  have hq : (q : G) ∈ Q := hq0
  refine ⟨q, hq, fun hqU => ?_, fun s hs => ?_⟩
  · apply hz1'
    rw [← hqz, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    exact hqU
  · have h2 := Subgroup.mem_center_iff.mp hzZ (π ⟨s⁻¹, S₀.inv_mem hs⟩)
    rw [← hqz, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, hN, Subgroup.mem_subgroupOf] at h2
    have e : (((⟨s⁻¹, S₀.inv_mem hs⟩ * q)⁻¹ * (q * ⟨s⁻¹, S₀.inv_mem hs⟩) : ↥S₀) : G) =
        (q : G)⁻¹ * s * q * s⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [e] at h2
    have h3 := (Subgroup.mem_normalizer_iff.mp (hS₀U q.2) _).mp h2
    have e2 : (q : G) * ((q : G)⁻¹ * s * q * s⁻¹) * (q : G)⁻¹ = s * q * s⁻¹ * (q : G)⁻¹ := by
      group
    rw [e2] at h3
    exact h3

section Invariant

variable {X L S₀ Q : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_exists_invariant_dualSplit (hα : IsModO2Surj L α) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hS₀ : IsSylowTwoOf S₀ X)
    (hQS : Q ≤ S₀) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (h1 : IsSumOfNaturalModulesVia L (centerOf (Q)) ⊥ α false 1)
    (h2 : IsSumOfNaturalModulesVia L (Q) (centerOf (Q)) α true 2) :
    ∃ (β' : ↥(Q) →* Multiplicative (Fin 2 → Fin 3 → F))
      (βU : ↥(centerOf (Q)) →* Multiplicative (Fin 3 → F)),
      Function.Surjective β' ∧ β'.ker = (centerOf (Q)).subgroupOf (Q) ∧
      (∀ (a : ↥L) (u v : ↥(Q)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
        Multiplicative.toAdd (β' v) i =
          (moduleAct true (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β' u) i)) ∧
      burnsideC135_DSG Q L (burnsideC135_Wc β' 1) (burnsideC135_Wc β' 0)
        (slNat α) βU (burnsideC135_βc β' 1) (burnsideC135_βc β' 0) ∧
      S₀ ≤ Subgroup.normalizer (burnsideC135_Wc β' 1 : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLQ, hUQ, β, hβs, hβk, hβeq⟩ := h2
  have hS₀L : S₀ ≤ Subgroup.normalizer (L : Set G) := hS₀.1.trans hXL
  have hS₀Q : S₀ ≤ Subgroup.normalizer (Q : Set G) := hS₀.1.trans hXQ
  have hS₀U : S₀ ≤ Subgroup.normalizer (centerOf (Q) : Set G) :=
    le_normalizer_centerOf hS₀Q
  have hne : ¬ Q ≤ centerOf (Q) := by
    intro h
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd (fun _ => Pi.single 0 1))
    have h4 : q ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact h q.2
    rw [MonoidHom.mem_ker, hq] at h4
    have h5 := congrFun (congrFun (congrArg Multiplicative.toAdd h4) 0) 0
    simp at h5
  obtain ⟨q₀, hq₀Q, hq₀U, hq₀S⟩ := burnsideC135_exists_fixed hS₀.2.1 hQS hS₀Q hS₀U hne
  have hρ := slNat_surjective hα.1
  obtain ⟨hPg, hodd⟩ := burnsideC135_image_sylow hS₀ hLX hXL hρ
  obtain ⟨-, y₁, -, hdual⟩ := burnsideC135_sylow_fix (hPg.toSylow hodd)
  have hcoord : ∀ i : Fin 2, ∃ c : F, Multiplicative.toAdd (β ⟨q₀, hq₀Q⟩) i = c • y₁ := by
    intro i
    refine hdual _ fun t ht => ?_
    have ht' : t ∈ ((S₀ ⊓ L).subgroupOf L).map (slNat α) := (IsPGroup.mem_toSylow hPg hodd).mp ht
    obtain ⟨l, hl0, rfl⟩ := ht'
    have hl : (l : G) ∈ S₀ ⊓ L := hl0
    have hmem : (l : G) * q₀ * (l : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp hq₀Q
    have h3 := hβeq l ⟨q₀, hq₀Q⟩ ⟨_, hmem⟩ rfl i
    rw [moduleAct_true_eq] at h3
    have h4 : β ⟨_, hmem⟩ = β ⟨q₀, hq₀Q⟩ := by
      have h5 : (⟨q₀, hq₀Q⟩⁻¹ * ⟨_, hmem⟩ : ↥(Q)) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        have h6 := hq₀S l hl.1
        have h7 := (Subgroup.mem_normalizer_iff.mp (hS₀U (S₀.inv_mem (hQS hq₀Q))) _).mp h6
        have e : (((⟨q₀, hq₀Q⟩ : ↥(Q))⁻¹ * ⟨_, hmem⟩ : ↥(Q)) : G) =
            q₀⁻¹ * ((l : G) * q₀ * (l : G)⁻¹ * q₀⁻¹) * q₀⁻¹⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact h7
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h5
      exact h5.symm
    rw [h4] at h3
    exact h3.symm
  choose c hc using hcoord
  have hc0 : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hq₀U
    have h5 : (⟨q₀, hq₀Q⟩ : ↥(Q)) ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
      · rw [hc 0, h.1, zero_smul]; rfl
      · rw [hc 1, h.2, zero_smul]; rfl
    rw [hβk, Subgroup.mem_subgroupOf] at h5
    exact h5
  let M : Matrix (Fin 2) (Fin 2) F :=
    if c 0 ≠ 0 then !![1, 0; c 1, c 0] else !![0, 1; c 1, c 0]
  have hMdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    by_cases h : c 0 ≠ 0
    · simp only [M, if_pos h, Matrix.det_fin_two_of]
      simpa using h
    · simp only [M, if_neg h, Matrix.det_fin_two_of]
      push Not at h
      have h1' : c 1 ≠ 0 := hc0.resolve_left (by simpa using h)
      simpa [h] using h1'
  have hM1 : M 1 0 = c 1 ∧ M 1 1 = c 0 := by
    by_cases h : c 0 ≠ 0
    · simp only [M, if_pos h]; exact ⟨rfl, rfl⟩
    · simp only [M, if_neg h]; exact ⟨rfl, rfl⟩
  obtain ⟨hβ's, hβ'k, hβ'eq⟩ := burnsideC135_twist (α := α) hβs hβk hβeq
    (Matrix.nonsing_inv_mul M hMdet) (Matrix.mul_nonsing_inv M hMdet)
  set β' := (burnsideC135_mix M).comp β with hβ'
  obtain ⟨βU, hD⟩ := burnsideC135_dualSplit_of_coords hα h1 hLQ hUQ hβ's hβ'k hβ'eq
  refine ⟨β', βU, hβ's, hβ'k, hβ'eq, hD, ?_⟩
  have hq₀W : q₀ ∈ burnsideC135_Wc β' 1 := by
    refine burnsideC135_mem_Wc.mpr ⟨hq₀Q, ?_⟩
    rw [hβ', MonoidHom.comp_apply, burnsideC135_mix_apply, Fin.sum_univ_two, hc 0, hc 1, hM1.1,
      hM1.2, smul_smul, smul_smul, mul_comm (c 1) (c 0), ← add_smul]
    rw [show c 0 * c 1 + c 0 * c 1 = 0 from CharTwo.add_self_eq_zero _, zero_smul]
  exact burnsideC135_W₁_invariant hD hS₀L hS₀U hq₀W hq₀U hq₀S

end Invariant

end CFSG.ASVolI

end
