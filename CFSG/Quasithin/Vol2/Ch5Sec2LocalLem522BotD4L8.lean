module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylow
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.GorensteinWalter
open scoped MatrixGroups Pointwise

theorem exists_cartan_psl2_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    ∃ d ∈ Subgroup.normalizer (psl2UpperUnipotentSubgroup K : Set (PSL2 K)), d ^ 7 = 1 ∧
      d ≠ 1 ∧ ∀ u ∈ psl2UpperUnipotentSubgroup K, u * d = d * u → u = 1 := by
  have hKu : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]
  have : Nontrivial Kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hKu]
    norm_num
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  have hω7 : ω ^ 7 = 1 := hKu ▸ pow_card_eq_one'
  have hω2 : (ω : K) ^ 2 ≠ 1 := by
    intro h
    have h2 : ω ^ 2 = 1 := Units.ext (by simpa using h)
    have h1 : orderOf ω ∣ Nat.gcd 2 7 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hω7)
    have h1' : orderOf ω = 1 := Nat.dvd_one.mp (by simpa using h1)
    exact hω (orderOf_eq_one_iff.mp h1')
  let τ : Kˣ →* SL(2, K) :=
    { toFun := fun a => ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show !![((a * b : Kˣ) : K), 0; 0, (((a * b)⁻¹ : Kˣ) : K)] =
          !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] * !![(b : K), 0; 0, ((b⁻¹ : Kˣ) : K)]
        rw [Matrix.mul_fin_two]
        simp [mul_comm] }
  set D := τ ω with hD
  have hD00 : (D : Matrix (Fin 2) (Fin 2) K) 0 0 = ω := rfl
  have hDB : D ∈ sl2Borel K := by
    rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
    rfl
  set d := psl2QuotientMap K D with hd
  set U := psl2UpperUnipotentSubgroup K with hU
  have hdN : d ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    rw [hU, psl2UpperUnipotent_normalizer_eq_borel, psl2Borel_eq_map]
    exact Subgroup.mem_map_of_mem _ hDB
  have hd7 : d ^ 7 = 1 := by
    rw [hd, ← map_pow, hD, ← map_pow, hω7, map_one, map_one]
  have hfix : ∀ u ∈ U, u * d = d * u → u = 1 := by
    intro u hu hud
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
    have hconj : d * psl2QuotientMap K (sl2UpperUnipotent x) * d⁻¹ =
        psl2QuotientMap K (sl2UpperUnipotent ((ω : K) ^ 2 * x)) := by
      rw [hd, ← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hDB x, hD00]
    have heq : psl2QuotientMap K (sl2UpperUnipotent ((ω : K) ^ 2 * x)) =
        psl2QuotientMap K (sl2UpperUnipotent x) := by
      rw [← hconj, ← hud]
      group
    have hcen : sl2UpperUnipotent ((ω : K) ^ 2 * x - x) ∈ Subgroup.center (SL(2, K)) := by
      have hq : psl2QuotientMap K (sl2UpperUnipotent ((ω : K) ^ 2 * x - x)) = 1 := by
        rw [sub_eq_add_neg, ← sl2UpperUnipotent_mul, map_mul, ← sl2UpperUnipotent_inv, map_inv,
          heq, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp hq
    have hscalar := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcen (0 : Fin 2)
    have h01 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
    have hx0 : ((ω : K) ^ 2 - 1) * x = 0 := by
      have : (0 : K) = (ω : K) ^ 2 * x - x := by simpa [sl2UpperUnipotent] using h01
      rw [sub_mul, one_mul, ← this]
    rcases mul_eq_zero.mp hx0 with h | h
    · exact absurd (sub_eq_zero.mp h) hω2
    · rw [h, sl2UpperUnipotent_zero, map_one]
  refine ⟨d, hdN, hd7, ?_, hfix⟩
  intro hd1
  have hUbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    exact hfix u hu (by rw [hd1, one_mul, mul_one])
  have hUcard := psl2UpperUnipotentSubgroup_card K
  rw [← hU, hUbot, Subgroup.card_bot, hK] at hUcard
  omega

theorem exists_cartan_of_isL2Quot_three {X : Type*} [Group X] [Finite X] (hX : IsL2Quot 3 X)
    {S : Subgroup X} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    ∃ c ∈ Subgroup.normalizer (S : Set X), c ^ 7 = 1 ∧ c ≠ 1 ∧
      ∀ s ∈ S, s * c = c * s → s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXcard : Nat.card X = 504 := by rw [hX.card (by norm_num)]; norm_num
  obtain ⟨e⟩ := hX
  set K := GaloisField 2 3
  have hK : Nat.card K = 8 := by rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  have hYcard : Nat.card (PSL2 K) = 504 := by rw [← Nat.card_congr e.toEquiv, hXcard]
  set U := psl2UpperUnipotentSubgroup K with hU
  have hUcard : Nat.card U = 8 := by rw [hU, psl2UpperUnipotentSubgroup_card, hK]
  set S' := S.map (e : X →* PSL2 K) with hS'
  have hsyl : ∀ P : Subgroup (PSL2 K), Nat.card P = 8 → IsPGroup 2 P ∧ ¬ 2 ∣ P.index := by
    intro P hP
    refine ⟨IsPGroup.of_card (n := 3) (by rw [hP]; norm_num), ?_⟩
    have h := Subgroup.card_mul_index P
    rw [hP, hYcard] at h
    have h63 : P.index = 63 := by omega
    rw [h63]
    norm_num
  obtain ⟨hU2, hUi⟩ := hsyl U hUcard
  have hS'2 : IsPGroup 2 S' := hS2.map _
  have hS'i : ¬ 2 ∣ S'.index := by rw [hS', Subgroup.index_map_equiv]; exact hSi
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 K) (hU2.toSylow hUi) (hS'2.toSylow hS'i)
  have hSU : ∀ y : PSL2 K, y ∈ S' ↔ h⁻¹ * y * h ∈ U := by
    intro y
    have h1 := congrArg (fun P : Sylow 2 (PSL2 K) => y ∈ (P : Subgroup (PSL2 K))) hh
    simp only [IsPGroup.toSylow_coe, Sylow.coe_subgroup_smul, eq_iff_iff] at h1
    rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply, inv_inv]
  set f : X ≃* PSL2 K := e.trans (MulAut.conj h⁻¹) with hf
  have hfx : ∀ x : X, f x = h⁻¹ * e x * h := fun x => by
    simp [hf]
  have hSf : ∀ x : X, x ∈ S ↔ f x ∈ U := by
    intro x
    rw [hfx, ← hSU, hS']
    exact (Subgroup.mem_map_iff_mem (f := (e : X →* PSL2 K)) e.injective).symm
  obtain ⟨d, hdN, hd7, hd1, hfix⟩ := exists_cartan_psl2_eight hK
  refine ⟨f.symm d, ?_, by rw [← map_pow, hd7, map_one], ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hSf, hSf, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp hdN (f x)
  · intro hc
    apply hd1
    have := congrArg f hc
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · intro s hs hsc
    have hfs := (hSf s).mp hs
    have h1 := congrArg f hsc
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    have h2 := hfix (f s) hfs h1
    rwa [map_eq_one_iff f f.injective] at h2

end CFSG.Quasithin.H13
