module

public import CFSG.Quasithin.Vol2.Ch11SecO1bJ
public import CFSG.Quasithin.Vol2.Ch11SecO1bM

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_map_subtype_iff {V : Subgroup G} {U : Subgroup ↥V} (v : ↥V) :
    (v : G) ∈ U.map V.subtype ↔ v ∈ U :=
  ⟨fun ⟨w, hw, he⟩ => (Subtype.ext he : w = v) ▸ hw, fun h => ⟨v, h, rfl⟩⟩

variable [Finite G]

theorem mQuot_le_of_relIndex_le {A B : Subgroup G} (hA : ∀ x ∈ A, x ^ 2 = 1) {n : ℕ}
    (h : B.relIndex A ≤ 2 ^ n) : E3.mQuot A B ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥A := fun v => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hA v v.2)⟩
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp hp
  have hdvd : B.relIndex A ∣ 2 ^ N := by
    rw [← hN]
    exact Subgroup.relIndex_dvd_card B A
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [E3.mQuot, hk, padicValNat.prime_pow]
  rw [hk] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

variable {T L I : Subgroup G} {n : ℕ}

theorem T_le_normalizer_flag (hS : SecD.NatSetting11 G T L I n) {i : ℕ}
    {U : Subgroup ↥(fsuV T I)}
    (hU : SecA.IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I)) ⊥ (2 ^ n) i U)
    (huniq : ∀ U', SecA.IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I)) ⊥ (2 ^ n) i U' →
      U' = U) :
    T ≤ Subgroup.normalizer ((U.map (fsuV T I).subtype : Subgroup G) : Set G) := by
  intro t ht
  have htL := hS.normal ht
  have htV := SecA.T_le_normalizer_fsuV T I ht
  have hmap := huniq _ (SecA.isFlagW_map hU (SecO1.mem_stabW_bot _)
    (fun h hh => G2Q8.conjV_mul_conjV_inv_mem htL htV hh) fun g hg => by
      obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hg
      rw [← SecA.conjV_inv (fsuV T I) htV, ← SecA.conjV_mul, ← SecA.conjV_mul]
      refine SecA.conjV_mem_autOn (Subgroup.mem_inf.mpr ⟨?_, ?_⟩) _
      · exact T.mul_mem (T.mul_mem (T.inv_mem ht) (Subgroup.mem_inf.mp hx).1) ht
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) x).mp
          (Subgroup.mem_inf.mp hx).2
        simpa using this)
  have hsub : (U.map (fsuV T I).subtype).subgroupOf (fsuV T I) = U :=
    Subgroup.comap_map_eq_self_of_injective (fsuV T I).subtype_injective U
  have hst : SecA.conjV (fsuV T I) t htV ∈
      SecA.stabW ((U.map (fsuV T I).subtype).subgroupOf (fsuV T I)) := by
    rw [hsub]
    exact SecA.mem_stabW_of_map_eq hmap
  exact (SecA.conjV_mem_stabW_iff (Subgroup.map_subtype_le U) htV).mp hst

variable [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K]

theorem exists_V1_sl3 {π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I))}
    {f : ↥(fsuV T I) → (Fin 3 → K)} {g : SpecialLinearGroup (Fin 3) K}
    (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I))) :
    ∃ V₁ : Subgroup G, V₁ ≤ fsuV T I ∧ T ≤ Subgroup.normalizer (V₁ : Set G) ∧
      ∀ v : ↥(fsuV T I),
        (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by
  obtain ⟨U₁, -, -, h₁, -, -, -, -, hu₁, -, -⟩ := SecO1.hasUniqueFlag hS
  refine ⟨U₁.map (fsuV T I).subtype, Subgroup.map_subtype_le U₁, T_le_normalizer_flag hS h₁ hu₁,
    fun v => ?_⟩
  rw [mem_map_subtype_iff]
  rw [← hK] at h₁
  rw [eq_U1_of_isFlagW (SecO1.sq_eq_one hS) hf hg h₁]
  exact mem_pre_line_iff hf g v

theorem exists_V1_sp4 {π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))}
    {f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)} {g : StatedSp 2 K}
    (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I))) :
    ∃ V₁ : Subgroup G, V₁ ≤ fsuV T I ∧ T ≤ Subgroup.normalizer (V₁ : Set G) ∧
      ∀ v : ↥(fsuV T I), (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • (mat 2 K g *ᵥ vec4 1 0 0 0) := by
  obtain ⟨U₁, -, -, h₁, -, -, -, -, hu₁, -, -⟩ := SecO1.hasUniqueFlag hS
  refine ⟨U₁.map (fsuV T I).subtype, Subgroup.map_subtype_le U₁, T_le_normalizer_flag hS h₁ hu₁,
    fun v => ?_⟩
  rw [mem_map_subtype_iff]
  rw [← hK] at h₁
  obtain ⟨S, hS', hc, hU⟩ := exists_eq_pre_of_isFlagW_sp (SecO1.sq_eq_one hS) hf hg h₁
  rw [hU, (eq_std_of_stable_sp hS').1 (by rw [hc, pow_one])]
  exact mem_gS1_iff g (f v)

end CFSG.Quasithin.Vol2.Ch11.SecO1b

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecO1b
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

theorem rankV2Fact_holds : RankV2Fact := by
  intro G _ _ T L I n V₂ hS hk hV₂ A hAT hA
  have := SecO1.isMulCommutative hS
  have hV₂V := SecA.IsVi.le_fsuV hV₂
  have hAV : A ≤ Subgroup.normalizer (fsuV T I : Set G) := fun a ha =>
    SecA.T_le_normalizer_fsuV T I (hAT ha)
  have hAV₂ : A ≤ Subgroup.normalizer (V₂ : Set G) := fun a ha =>
    SecA.IsVi.le_normalizer hV₂ (hAT ha)
  refine mQuot_le_of_relIndex_le hA.2 ?_
  rcases hk with hk | hk
  · obtain ⟨K, _, _, _, hK, π, f, hf, g, hg⟩ := exists_coord_sl3_syl hS hk
    obtain ⟨V₁, hV₁V, hTV₁, hV₁⟩ := exists_V1_sl3 hS hK hf hg
    have hx₀ : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => by simpa using congrFun h 0
    rw [← hK]
    exact rankV2_of_coords (SecO1.IsCoord.injective_of_bot hf) hf.surj (ind_sl3 g) hV₁V hV₂V
      hV₁ (fun v => by
        rw [← Subgroup.mem_subgroupOf, mem_V2_sl3 hS hK hf hg hV₂, mem_pre_plane_iff hf g v,
          plane_sl3])
      hA hAV (fun a ha => hTV₁ (hAT ha)) hAV₂ fun a ha => exists_semilinear_conjV hf
        (fun T' hT' => commutant_statedSL (by norm_num) T' hT') hx₀ (hS.normal (hAT ha)) (hAV ha)
  · obtain ⟨K, _, _, _, hK, π, f, -, hf, g, hg⟩ := exists_coord_sp4_syl hS hk
    obtain ⟨V₁, hV₁V, hTV₁, hV₁⟩ := exists_V1_sp4 hS hK hf hg
    have hx₀ : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
      (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
    rw [← hK]
    exact rankV2_of_coords (SecO1.IsCoord.injective_of_bot hf) hf.surj (ind_sp4 g) hV₁V hV₂V
      hV₁ (fun v => by
        rw [← Subgroup.mem_subgroupOf, mem_V2_sp4 hS hK hf hg hV₂]
        exact plane_sp4 g (f v))
      hA hAV (fun a ha => hTV₁ (hAT ha)) hAV₂ fun a ha => exists_semilinear_conjV hf
        (fun T' hT' => commutant_statedSp T' hT') hx₀ (hS.normal (hAT ha)) (hAV ha)

end CFSG.Quasithin.Vol2.Ch11.SecD
