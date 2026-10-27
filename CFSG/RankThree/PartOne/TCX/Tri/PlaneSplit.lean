module

public import CFSG.RankThree.PartOne.TCX.Plane
public import CFSG.RankThree.PartOne.KF.ClsExcD4
public import CFSG.RankThree.PartOne.KGD.D4QTorus
public import CFSG.RankThree.PartOne.K1214.OmegaAlg

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KGD
open CFSG.Timmesfeld.ExceptionalOrders
open CFSG.RankThree.PartOne.TCX


section Torus

variable {K : Type} [Field K]

theorem entrywise_torusCoordHom (δ : K ≃+* K) (c : Fin TwistTag.D4.tag.rank → Kˣ) :
    Units.map (entrywiseHom δ.toRingHom) ((torusCoordHom TwistTag.D4.tag K c :
      torusGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
      ((torusCoordHom TwistTag.D4.tag K (fun i => Units.map δ.toRingHom.toMonoidHom (c i)) :
        torusGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
  rw [coe_torusCoordHom, coe_torusCoordHom, map_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  exact entrywise_torusElt δ i (c i)

end Torus

section Plane

theorem tri_plane_split {K : Type} [Field K] [Finite K] {p f₀ : ℕ} (hp : p.Prime)
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = (2 ^ (p * f₀)) ^ 3) {σ δ₀ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀)) (hδ₀ : ∀ c, δ₀ c = c ^ 2 ^ (3 * f₀))
    (hpq : p ∣ 2 ^ f₀ - 1) :
    ∃ R U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
        (∀ r ∈ R, fieldActor (t := TwistTag.D4) σ δ₀ r = r) ∧ U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
        (∀ u ∈ U, fieldActor (t := TwistTag.D4) σ δ₀ u ∈ U) ∧
        R ≤ Subgroup.normalizer (U : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpf : 1 ≤ 3 * (p * f₀) := Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
    (Nat.mul_pos hp.pos hf₀))
  have hK' : Nat.card K = 2 ^ (3 * (p * f₀)) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf hK'
  have h2f : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hmodeq : 2 ^ f₀ ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' h2f).2 hpq).symm
  have hmod : ∀ m : ℕ, 2 ^ (f₀ * m) % p = 1 := fun m => by
    have h1 := hmodeq.pow m
    rw [one_pow, ← pow_mul] at h1
    rw [h1]
    exact Nat.mod_eq_of_lt hp.one_lt
  have hpK : p ∣ Nat.card K - 1 := by
    have h1 : 2 ^ f₀ - 1 ∣ (2 ^ f₀) ^ (3 * p) - 1 ^ (3 * p) := Nat.sub_dvd_pow_sub_pow _ _ _
    rw [one_pow] at h1
    have h2 : (2 ^ (p * f₀)) ^ 3 = (2 ^ f₀) ^ (3 * p) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hK, h2]
    exact hpq.trans h1
  have hdvd : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hpK
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => hp.one_lt.ne' (hζo.symm.trans (by rw [h, orderOf_one]))
  have hpowmod : ∀ n : ℕ, n % p = 1 → ζ ^ n = ζ := fun n hn => by
    rw [← Nat.mod_add_div n p, hn, pow_add, pow_mul, hζp, one_pow, mul_one, pow_one]
  have hσζ : Units.map σ.toRingHom.toMonoidHom ζ = ζ := by
    apply Units.ext
    change σ (ζ : K) = ζ
    rw [hσ]
    have := hpowmod (2 ^ (p * f₀)) (by rw [mul_comm p f₀]; exact hmod p)
    exact congrArg Units.val this
  have hδζ : Units.map δ₀.toRingHom.toMonoidHom ζ = ζ := by
    apply Units.ext
    change δ₀ (ζ : K) = ζ
    rw [hδ₀]
    have := hpowmod (2 ^ (3 * f₀)) (by rw [mul_comm 3 f₀]; exact hmod 3)
    exact congrArg Units.val this
  have hσ1 : Units.map σ.toRingHom.toMonoidHom (1 : Kˣ) = 1 := map_one _
  have hδ1 : Units.map δ₀.toRingHom.toMonoidHom (1 : Kˣ) = 1 := map_one _
  have hpermi2 : ∀ i : Fin TwistTag.D4.tag.rank, TwistTag.D4.perm i = i2 ↔ i = i2 := fun i => by
    constructor
    · intro h
      apply TwistTag.D4.perm.injective
      rw [h, perm_i2]
    · rintro rfl
      exact perm_i2
  have hodd : Odd (Nat.card K - 1) := odd_card_sub_one_of_card_eq (n := p * f₀)
    (Nat.mul_pos hp.pos hf₀) hK
  have hfinj : Function.Injective ((torusGroup TwistTag.D4.tag K).subtype.comp
      (torusCoordHom TwistTag.D4.tag K)) := coordHom_injective_D4 hodd
  set c₁ : Fin TwistTag.D4.tag.rank → Kˣ := fun i => if i = i2 then 1 else ζ with hc₁
  set c₂ : Fin TwistTag.D4.tag.rank → Kˣ := fun i => if i = i2 then ζ else 1 with hc₂
  have hc₁mem : c₁ ∈ compatSubgroup (t := TwistTag.D4) σ.toRingHom := by
    rw [mem_compatSubgroup]
    intro i
    by_cases hi : i = i2
    · subst hi
      rw [perm_i2]
      simp [hc₁]
    · have : TwistTag.D4.perm i ≠ i2 := fun h => hi ((hpermi2 i).1 h)
      simpa [hc₁, hi, this] using hσζ.symm
  have hc₂mem : c₂ ∈ compatSubgroup (t := TwistTag.D4) σ.toRingHom := by
    rw [mem_compatSubgroup]
    intro i
    by_cases hi : i = i2
    · subst hi
      rw [perm_i2]
      simpa [hc₂] using hσζ.symm
    · have : TwistTag.D4.perm i ≠ i2 := fun h => hi ((hpermi2 i).1 h)
      simp [hc₂, hi, this]
  have hmemC : ∀ c ∈ compatSubgroup (t := TwistTag.D4) σ.toRingHom,
      ((torusCoordHom TwistTag.D4.tag K c : torusGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun c hc =>
    graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom
      (compatTorus_le_graphFixedRootTorus σ.toRingHom ⟨c, hc, rfl⟩)
  have hmemB : ∀ c ∈ compatSubgroup (t := TwistTag.D4) σ.toRingHom,
      ((torusCoordHom TwistTag.D4.tag K c : torusGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := fun c hc =>
    graphFixedRootTorus_le_graphFixedRootBorel
      (compatTorus_le_graphFixedRootTorus σ.toRingHom ⟨c, hc, rfl⟩)
  set u₁ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨_, hmemC c₁ hc₁mem⟩ with hu₁
  set u₂ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨_, hmemC c₂ hc₂mem⟩ with hu₂
  have hi02 : (i0 : Fin TwistTag.D4.tag.rank) ≠ i2 := by decide
  have hc₁p : c₁ ^ p = 1 := by
    funext i
    by_cases hi : i = i2 <;> simp [hc₁, hi, hζp]
  have hc₂p : c₂ ^ p = 1 := by
    funext i
    by_cases hi : i = i2 <;> simp [hc₂, hi, hζp]
  have hu₁p : u₁ ^ p = 1 := Subtype.ext (by
    have h : ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K))
        (c₁ ^ p) = 1 := by rw [hc₁p, map_one]
    rw [map_pow] at h
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h)
  have hu₂p : u₂ ^ p = 1 := Subtype.ext (by
    have h : ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K))
        (c₂ ^ p) = 1 := by rw [hc₂p, map_one]
    rw [map_pow] at h
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h)
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    have h1 : ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K)) c₁ =
        ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K)) 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := congrFun (hfinj h1) i0
    exact hζ1 (by simpa [hc₁, hi02] using h2)
  have hu₂1 : u₂ ≠ 1 := by
    intro h
    have h1 : ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K)) c₂ =
        ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K)) 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := congrFun (hfinj h1) i2
    exact hζ1 (by simpa [hc₂] using h2)
  have hu₁o : orderOf u₁ = p := orderOf_eq_prime hu₁p hu₁1
  have hu₂o : orderOf u₂ = p := orderOf_eq_prime hu₂p hu₂1
  have hcomm : Commute u₁ u₂ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact CFSG.RankThree.PartOne.KE.torusGroup_comm
      (torusCoordHom TwistTag.D4.tag K c₁).2 (torusCoordHom TwistTag.D4.tag K c₂).2)
  have hind : u₂ ∉ Subgroup.zpowers u₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K)) c₂ =
        ((torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K))
          (c₁ ^ k) := by
      rw [map_zpow]
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    have h2 := congrFun (hfinj h1) i2
    exact hζ1 (by simpa [hc₁, hc₂] using h2)
  have hfix : ∀ (c : Fin TwistTag.D4.tag.rank → Kˣ) (hc : c ∈ compatSubgroup (t := TwistTag.D4)
      σ.toRingHom), (∀ i, Units.map δ₀.toRingHom.toMonoidHom (c i) = c i) →
      fieldActor (t := TwistTag.D4) σ δ₀ ⟨_, hmemC c hc⟩ = ⟨_, hmemC c hc⟩ := by
    intro c hc hcδ
    refine Subtype.ext ?_
    rw [coe_fieldActor, entrywise_torusCoordHom]
    congr 2
    funext i
    exact hcδ i
  have hfu₁ : fieldActor (t := TwistTag.D4) σ δ₀ u₁ = u₁ :=
    hfix c₁ hc₁mem fun i => by
      by_cases hi : i = i2
      · simp [hc₁, hi]
      · simpa [hc₁, hi] using hδζ
  have hfu₂ : fieldActor (t := TwistTag.D4) σ δ₀ u₂ = u₂ :=
    hfix c₂ hc₂mem fun i => by
      by_cases hi : i = i2
      · simpa [hc₂, hi] using hδζ
      · simp [hc₂, hi]
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hδcomm : ∀ c, δ₀ (σ c) = σ (δ₀ c) := ringEquiv_comm_of_finite σ δ₀
  refine ⟨Subgroup.closure ({u₁, u₂} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
    (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine CFSG.RankThree.PartOne.K1214.isElementaryAbelian_closure (fun x hx y hy => ?_)
      (fun x hx => ?_)
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
      · exact hcomm.eq
      · exact hcomm.eq.symm
    · rcases hx with hx | hx <;> rw [hx]
      · rw [← hu₁o]; exact pow_orderOf_eq_one _
      · rw [← hu₂o]; exact pow_orderOf_eq_one _
  · exact card_closure_pair hp hcomm hu₁o hu₂o hind
  · intro r hr
    have hle : Subgroup.closure ({u₁, u₂} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
        (fieldActor (t := TwistTag.D4) σ δ₀).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [Subgroup.closure_le]
      rintro x (hx | hx) <;> rw [hx]
      · exact hfu₁
      · exact hfu₂
    exact hle hr
  · intro hU
    have hne : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≠ ⊥ := by
      intro hbot
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrad⟩ :=
        diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ
          (∅ : Set (Fin TwistTag.D4.foldedTag.rank))
      refine hrad (fun huniv => ?_) ?_
      · have : (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈
            (∅ : Set (Fin TwistTag.D4.foldedTag.rank)) := by rw [huniv]; trivial
        exact this
      · rw [eq_bot_iff]
        have h1 := graphFixedParabolicRadical_le_graphFixedPosUnipotent (t := TwistTag.D4)
          (K := K) (σ := σ.toRingHom) (∅ : Set (Fin TwistTag.D4.foldedTag.rank))
        rw [hbot] at h1
        exact h1
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have hyC : y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := hUC hy
    have : (⟨y, hyC⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := hy
    rw [hU, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  · exact isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom)
  · intro u hu
    have hX := map_graphFixedEntrywiseAut_subgroupOf (t := TwistTag.D4) (σ := σ.toRingHom) hδcomm
      hUC (map_units_map_entrywiseHom_graphFixedPosUnipotent hδcomm)
    rw [← hX]
    exact ⟨u, hu, rfl⟩
  · rw [Subgroup.closure_le]
    have hnormal : ∀ u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (u : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom →
        u ∈ Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
              Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := fun u hu => by
      have h1 : u ∈ (Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
          Set (ModGL TwistTag.D4.tag K))).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
        graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hu
      rwa [Subgroup.subgroupOf_normalizer_eq hUC] at h1
    rintro x (hx | hx) <;> rw [hx]
    · exact hnormal u₁ (hmemB c₁ hc₁mem)
    · exact hnormal u₂ (hmemB c₂ hc₂mem)

end Plane

end CFSG.RankThree.PartOne.TCX.Tri
