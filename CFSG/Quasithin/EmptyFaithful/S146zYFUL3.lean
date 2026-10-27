module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.EmptyFaithful.S146zYFULPlane
public import CFSG.Quasithin.EmptyFaithful.S146zYFULTorus
public import CFSG.Quasithin.Vol2.F134LieL3

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieL3
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped MatrixGroups

theorem two_pow_mod_five_of_not_dvd {n : ℕ} (hn : ¬ 4 ∣ n) :
    2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 ∨ 2 ^ n % 5 = 4 := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hr0 : r ≠ 0 := fun h => hn ⟨k, by omega⟩
  have h16 : 2 ^ (4 * k) % 5 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  rw [pow_add, Nat.mul_mod, h16]
  interval_cases r <;> simp_all

theorem noElemTwentyFive_of_not_dvd_four {X : Type} [Group X] {n : ℕ} (hn : ¬ 4 ∣ n)
    (h : StatedClassicalModel X .PSL 3 2 n) : NoElemTwentyFive X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK5 : Nat.card K % 5 = 2 ∨ Nat.card K % 5 = 3 ∨ Nat.card K % 5 = 4 := by
    rw [hK]
    exact two_pow_mod_five_of_not_dvd hn
  refine NoElemTwentyFive.of_mulEquiv e (noElemTwentyFive_of_isCyclic fun Q hQ => ?_)
  exact isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _)
    (fun S => CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_of_le_GL_three (by omega)
      (by omega) S.isPGroup') Q hQ

theorem false_of_e25Config {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK5 : Nat.card K % 5 = 1)
    (e₁ : ↥L ≃* projectiveSL 3 K) (hcfg : E25Config L P T) : False := by
  classical
  have hLn : L.Normal := hcfg.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := E25Config.isSylowTwoOf_inf hcfg
  set UL : Subgroup L := (T ⊓ L).subgroupOf L with hULdef
  have hUL2 : IsPGroup 2 UL := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hU1 : IsPGroup 2 (UL.map e₁.toMonoidHom) := hUL2.map _
  have hU1i : ¬ 2 ∣ (UL.map e₁.toMonoidHom).index := by
    rw [show UL.map e₁.toMonoidHom = UL.map (e₁ : ↥L →* projectiveSL 3 K) from rfl,
      Subgroup.index_map_equiv]
    exact hS.2.2
  obtain ⟨S₀, hS₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) S₀ (hU1.toSylow hU1i)
  have hmem : ∀ z, z ∈ UL.map e₁.toMonoidHom ↔ g⁻¹ * z * g ∈ projUnitriangular 3 K := by
    intro z
    have h1 : UL.map e₁.toMonoidHom = ((g • S₀ : Sylow 2 (projectiveSL 3 K)) :
        Subgroup (projectiveSL 3 K)) := by
      rw [hg]
      rfl
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, hS₀]
  set e : ↥L ≃* projectiveSL 3 K := e₁.trans (MulAut.conj g⁻¹) with hedef
  have he : ∀ y : L, e y = g⁻¹ * e₁ y * g := fun y => by
    rw [hedef, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hUe : UL.map e.toMonoidHom = projUnitriangular 3 K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e y ∈ _
      rw [he]
      exact (hmem _).mp ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, hye⟩ := (hmem (g * x * g⁻¹)).mpr (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x
        by group])
      refine ⟨y, hy, ?_⟩
      change e y = x
      rw [he]
      change e₁ y = g * x * g⁻¹ at hye
      rw [hye]
      group
  set P' : Subgroup (projectiveSL 3 K) := (P.subgroupOf L).map e.toMonoidHom with hP'def
  have hP'card : Nat.card P' = 25 := by
    rw [hP'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  have hP'exp : ∀ x ∈ P', x ^ 5 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy5 : y ^ 5 = 1 := Subtype.ext (by simpa using hcfg.exp y (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy5, map_one]
  have hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ P', ∃ y ∈ P', ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s := by
    intro u hu x hx
    rw [← hUe] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y, hy, s, hs, hys⟩ := E25Config.mul_inf hcfg u' (Subgroup.mem_subgroupOf.mp hu') x'
      (Subgroup.mem_subgroupOf.mp hx')
    refine ⟨e ⟨y, hcfg.le hy⟩, ⟨⟨y, hcfg.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩,
      e ⟨s, hs.2⟩, ?_, ?_⟩
    · rw [← hUe]
      exact ⟨⟨s, hs.2⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    · change e u' * e x' = e ⟨y, hcfg.le hy⟩ * e ⟨s, hs.2⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hys
  have hPB : ∀ g : SL(3, K), proj 3 K g ∈ P' → g ∈ upperTriangular 3 K :=
    fun g hg => mem_upperTriangular_of_le_twentyFive (by rw [hP'card]) hK5 hQU hg
  have hD1 := inf_ratioGroup_ne_bot_twentyFive hPB hP'card hP'exp
  have hD2 := not_le_ratioGroup_twentyFive hPB hP'card hP'exp
  set α : A → MulAut (projectiveSL 3 K) := fun t => (e.symm.trans (MulAut.conjNormal t)).trans e
    with hαdef
  have hα : ∀ t (y : L), α t (e y) = e (MulAut.conjNormal t y) := fun t y => by
    rw [hαdef]
    simp
  have hαU : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      (projUnitriangular 3 K).map (α t).toMonoidHom = projUnitriangular 3 K := by
    intro t ht
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hUe] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨MulAut.conjNormal t y, ?_, (hα t y).symm⟩
      have hy' := Subgroup.mem_subgroupOf.mp hy
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
      exact ⟨T.mul_mem (T.mul_mem ht.1 hy'.1) (T.inv_mem ht.1), hLn.conj_mem _ hy'.2 t⟩
    · rw [Subgroup.card_map_of_injective (α t).injective]
  have hαP : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ P', α t x ∈ P' := by
    rintro t ht _ ⟨y, hy, rfl⟩
    refine ⟨MulAut.conjNormal t y, ?_, (hα t y).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp ht.2 _).mp (Subgroup.mem_subgroupOf.mp hy)
  set Q : Subgroup (projectiveSL 3 K) := P' ⊓ ratioGroup K with hQdef
  have hαQ : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ Q, α t x ∈ Q :=
    fun t ht x hx => ⟨hαP t ht x hx.1, map_mem_ratioGroup (hαU t ht) hx.2⟩
  set QA : Subgroup A := (Q.map e.symm.toMonoidHom).map L.subtype with hQAdef
  have hQAP : QA ≤ P := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hq.1
    have hp' : e.symm (e p) = p := e.symm_apply_apply p
    change ((e.symm (e p) : L) : A) ∈ P
    rw [hp']
    exact Subgroup.mem_subgroupOf.mp hp
  have hfwd : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ z ∈ QA, t * z * t⁻¹ ∈ QA := by
    rintro t ht _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨_, ⟨α t q, hαQ t ht q hq, rfl⟩, ?_⟩
    have h1 : e.symm (α t q) = MulAut.conjNormal t (e.symm q) := by
      have h2 := hα t (e.symm q)
      rw [e.apply_symm_apply] at h2
      rw [h2, e.symm_apply_apply]
    change ((e.symm (α t q) : L) : A) = t * ((e.symm q : L) : A) * t⁻¹
    rw [h1, MulAut.conjNormal_apply]
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (QA : Set A) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd t ht z, fun hz => ?_⟩
    have h1 := hfwd t⁻¹ (inv_mem ht) _ hz
    rwa [show t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z by group] at h1
  rcases hcfg.irred QA hQAP hnorm with h | h
  · apply hD1
    rw [hQAdef, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h
    exact h
  · apply hD2
    have hP : P = (P.subgroupOf L).map L.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hcfg.le]
    rw [hQAdef, hP] at h
    have h2 := Subgroup.map_injective L.subtype_injective h
    have h3 : Q = P' := by
      rw [hP'def, ← h2, Subgroup.map_map]
      ext x
      simp
    intro x hx
    rw [← h3] at hx
    exact hx.2

theorem facts134Five_psl3Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n := by
  intro n
  by_cases h4 : 4 ∣ n
  · intro A _ _ L P T hL hcfg
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hL
    have := charP_two_of_card_eq_two_pow hK
    refine false_of_e25Config (K := K) ?_
      (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))) hcfg
    obtain ⟨k, rfl⟩ := h4
    rw [hK, pow_mul, Nat.pow_mod]
    norm_num
  · exact noE25Config_of_noElem fun X _ h => noElemTwentyFive_of_not_dvd_four h4 h

end CFSG.Quasithin.S146zY
