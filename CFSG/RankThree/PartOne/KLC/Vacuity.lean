module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem mem_normalizer_of_mem_borelGroup {b : ModGL τ K} (hb : b ∈ borelGroup τ K)
    (hbC : b ∈ adjointGroup τ K) {PU : Subgroup (adjointGroup τ K)}
    (hPU : PU = (posUnipotent τ K).subgroupOf (adjointGroup τ K)) :
    (⟨b, hbC⟩ : adjointGroup τ K) ∈ Subgroup.normalizer (PU : Set (adjointGroup τ K)) := by
  have hb' : b ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
    have h1 : b ∈ adjointGroup τ K ⊓ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
      rw [(borel_self_normalizers τ K).1]
      exact hb
    exact (Subgroup.mem_inf.1 h1).2
  rw [Subgroup.mem_normalizer_iff]
  intro u
  rw [hPU, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.1 hb' (u : ModGL τ K)

theorem mem_normalizer_map_conj {G : Type*} [Group G] (H : Subgroup G) (c n : G)
    (hn : n ∈ Subgroup.normalizer (H : Set G)) :
    c * n * c⁻¹ ∈ Subgroup.normalizer ((H.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hn

theorem exists_conj_borel_le_normalizer (S : Sylow 2 (adjointGroup τ K)) :
    ∃ c : adjointGroup τ K, ∀ b : ModGL τ K, b ∈ borelGroup τ K → ∀ hbC : b ∈ adjointGroup τ K,
      c * ⟨b, hbC⟩ * c⁻¹ ∈ Subgroup.normalizer ((S : Subgroup (adjointGroup τ K)) :
        Set (adjointGroup τ K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL τ K) := finite_modGL
  have hC : Finite (adjointGroup τ K) := Subtype.finite
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨⟨PU, hPU⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ K 2 w₀ hw₀
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup τ K) PU S
  have hSmap : (S : Subgroup (adjointGroup τ K)) =
      (PU : Subgroup (adjointGroup τ K)).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]
    exact coe_smul_sylow_eq_map c PU
  refine ⟨c, fun b hb hbC => ?_⟩
  rw [hSmap]
  exact mem_normalizer_map_conj _ c _ (mem_normalizer_of_mem_borelGroup hb hbC hPU)

omit [Finite K] [CharP K 2] in
theorem exists_parabolic_of_conj_borel_le {P : Subgroup (adjointGroup τ K)} (hP : P ≠ ⊤)
    {c : adjointGroup τ K}
    (hc : ∀ b : ModGL τ K, b ∈ borelGroup τ K → ∀ hbC : b ∈ adjointGroup τ K,
      c * ⟨b, hbC⟩ * c⁻¹ ∈ P) :
    ∃ J : Set (Fin τ.rank), J ≠ Set.univ ∧ ∀ z : ModGL τ K,
      z ∈ parabolicSubgroup τ K J ↔ ∃ s : adjointGroup τ K, s ∈ P ∧
        (s : ModGL τ K) = (c : ModGL τ K) * z * (c : ModGL τ K)⁻¹ := by
  classical
  let A : Subgroup (ModGL τ K) :=
    (P.map (adjointGroup τ K).subtype).comap (MulAut.conj (c : ModGL τ K)).toMonoidHom
  have hmemA : ∀ z : ModGL τ K, z ∈ A ↔ ∃ s : adjointGroup τ K, s ∈ P ∧
      (s : ModGL τ K) = (c : ModGL τ K) * z * (c : ModGL τ K)⁻¹ := by
    intro z
    rw [Subgroup.mem_comap]
    constructor
    · rintro ⟨s, hs, hsz⟩
      exact ⟨s, hs, hsz⟩
    · rintro ⟨s, hs, hsz⟩
      exact ⟨s, hs, hsz⟩
  have hAC : A ≤ adjointGroup τ K := by
    intro z hz
    obtain ⟨s, -, hsz⟩ := (hmemA z).1 hz
    have hz' : z = (c : ModGL τ K)⁻¹ * (s : ModGL τ K) * c := by
      rw [hsz]
      group
    rw [hz']
    exact (adjointGroup τ K).mul_mem ((adjointGroup τ K).mul_mem
      ((adjointGroup τ K).inv_mem c.2) s.2) c.2
  have hBA : borelGroup τ K ≤ A := by
    intro b hb
    have hbC : b ∈ adjointGroup τ K :=
      ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1 hb
    exact (hmemA b).2 ⟨c * ⟨b, hbC⟩ * c⁻¹, hc b hb hbC,
      by simp only [Subgroup.coe_mul, InvMemClass.coe_inv]⟩
  have hAeq := eq_parabolicSubgroup_of_borelGroup_le hBA hAC
  refine ⟨{i | weylElt τ K i 1 ∈ A}, ?_, fun z => ?_⟩
  · intro huniv
    rw [huniv] at hAeq
    have hall := hAeq.trans (standard_parabolic_cells τ K).2.2.2.2.2.1
    apply hP
    rw [eq_top_iff]
    intro sX _
    have hz : (c : ModGL τ K)⁻¹ * (sX : ModGL τ K) * c ∈ A := by
      rw [hall]
      exact (adjointGroup τ K).mul_mem ((adjointGroup τ K).mul_mem
        ((adjointGroup τ K).inv_mem c.2) sX.2) c.2
    obtain ⟨s', hs', hs'eq⟩ := (hmemA _).1 hz
    have hss : s' = sX := by
      apply Subtype.ext
      rw [hs'eq]
      group
    exact hss ▸ hs'
  · rw [← hAeq]
    exact hmemA z

theorem exists_mem_parabolic_of_commute {x y : ModGL τ K} (hxC : x ∈ adjointGroup τ K)
    (hyC : y ∈ adjointGroup τ K) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) :
    ∃ (g : adjointGroup τ K) (J : Set (Fin τ.rank)), J ≠ Set.univ ∧
      (g : ModGL τ K)⁻¹ * x * g ∈ parabolicSubgroup τ K J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL τ K) := finite_modGL
  have hC : Finite (adjointGroup τ K) := Subtype.finite
  let yX : adjointGroup τ K := ⟨y, hyC⟩
  let xX : adjointGroup τ K := ⟨x, hxC⟩
  have hyX2 : yX ^ 2 = 1 := Subtype.ext hy2
  have hyX1 : yX ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hU : Subgroup.zpowers yX ≠ ⊥ := by
    intro h
    exact hyX1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers yX))
  have hU2 : IsPGroup 2 (Subgroup.zpowers yX) := by
    refine IsPGroup.iff_orderOf.2 fun g => ?_
    obtain ⟨k, hk⟩ := g.2
    have hg2 : (g : adjointGroup τ K) ^ 2 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyX2, one_zpow]
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext hg2)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨S, P, hP, hN, -, -, hS⟩ := holds_adjointGroup_tag τ K 2 (Subgroup.zpowers yX) hU hU2
  obtain ⟨c, hc⟩ := exists_conj_borel_le_normalizer (τ := τ) (K := K) S
  obtain ⟨J, hJ, hJP⟩ := exists_parabolic_of_conj_borel_le hP
    (fun b hb hbC => hS (hc b hb hbC))
  have hxy' : xX * yX = yX * xX := Subtype.ext hxy
  have hcomm : Commute xX yX := hxy'
  have hcent : xX ∈ Subgroup.centralizer ((Subgroup.zpowers yX : Subgroup (adjointGroup τ K)) :
      Set (adjointGroup τ K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨k, rfl⟩
    exact (hcomm.symm.zpow_left k).eq
  have hxN : xX ∈ Subgroup.normalizer ((Subgroup.zpowers yX : Subgroup (adjointGroup τ K)) :
      Set (adjointGroup τ K)) := Subgroup.centralizer_le_normalizer _ hcent
  refine ⟨c, J, hJ, (hJP _).2 ⟨xX, hN hxN, ?_⟩⟩
  change x = (c : ModGL τ K) * ((c : ModGL τ K)⁻¹ * x * c) * (c : ModGL τ K)⁻¹
  group

theorem no_commuting_of_not_dvd_parabolic {x y : ModGL τ K} {p : ℕ} (hxC : x ∈ adjointGroup τ K)
    (hyC : y ∈ adjointGroup τ K) (hx : orderOf x = p) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hxy : x * y = y * x)
    (hpar : ∀ J : Set (Fin τ.rank), J ≠ Set.univ → ¬ p ∣ Nat.card (parabolicSubgroup τ K J)) :
    False := by
  obtain ⟨g, J, hJ, hmem⟩ := exists_mem_parabolic_of_commute hxC hyC hy2 hy1 hxy
  have hord : orderOf ((g : ModGL τ K)⁻¹ * x * (g : ModGL τ K)) = p := by
    have : (g : ModGL τ K)⁻¹ * x * (g : ModGL τ K) = (MulAut.conj (g : ModGL τ K)⁻¹) x := by
      rw [MulAut.conj_apply, inv_inv]
    rw [this, MulEquiv.orderOf_eq, hx]
  refine hpar J hJ ?_
  have := orderOf_dvd_natCard
    (⟨(g : ModGL τ K)⁻¹ * x * (g : ModGL τ K), hmem⟩ : parabolicSubgroup τ K J)
  rwa [Subgroup.orderOf_mk, hord] at this

end CFSG.RankThree.PartOne.KLC
