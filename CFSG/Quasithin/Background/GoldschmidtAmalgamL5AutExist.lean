module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Rel
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.F6.GoldAmN

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ G₁' G₂' : Subgroup D} {a b s ρ x y : D}

structure SubAmalgam (G₁ G₂ G₁' G₂' : Subgroup D) : Prop where
  amalgam : GoldHyp G₁ G₂
  le₁ : G₁' ≤ G₁
  le₂ : G₂' ≤ G₂
  idx₁ : G₁'.relIndex G₁ = 2
  idx₂ : G₂'.relIndex G₂ = 2
  vertex₁ : Vertex G₁' (G₁' ⊓ G₂')
  vertex₂ : Vertex G₂' (G₁' ⊓ G₂')

namespace SubAmalgam

variable (H : SubAmalgam G₁ G₂ G₁' G₂')

include H

omit [Finite D] in
theorem T'_le_T : G₁' ⊓ G₂' ≤ G₁ ⊓ G₂ :=
  le_inf (inf_le_left.trans H.le₁) (inf_le_right.trans H.le₂)

theorem relIndex_T : (G₁' ⊓ G₂').relIndex (G₁ ⊓ G₂) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (G₁' ⊓ G₂') G₁' G₁ inf_le_left H.le₁
  have h2 := Subgroup.relIndex_mul_relIndex (G₁' ⊓ G₂') (G₁ ⊓ G₂) G₁ H.T'_le_T inf_le_left
  rw [H.vertex₁.index_eq, H.idx₁] at h1
  rw [H.amalgam.vertex_left.index_eq] at h2
  omega

theorem not_T_le₁ : ¬ G₁ ⊓ G₂ ≤ G₁' := by
  intro hle
  have h1 := Subgroup.relIndex_mul_relIndex (G₁ ⊓ G₂) G₁' G₁ hle H.le₁
  rw [H.idx₁, H.amalgam.vertex_left.index_eq] at h1
  omega

theorem not_T_le₂ : ¬ G₁ ⊓ G₂ ≤ G₂' := by
  intro hle
  have h1 := Subgroup.relIndex_mul_relIndex (G₁ ⊓ G₂) G₂' G₂ hle H.le₂
  rw [H.idx₂, H.amalgam.vertex_right.index_eq] at h1
  omega

theorem T_inf₂ : (G₁ ⊓ G₂) ⊓ G₂' = G₁' ⊓ G₂' :=
  inf_eq_of_relIndex_two H.T'_le_T H.relIndex_T inf_le_right H.not_T_le₂

omit [Finite D] in
theorem normal₁ : G₁ ≤ Subgroup.normalizer (G₁' : Set D) :=
  le_normalizer_of_relIndex_two H.le₁ H.idx₁

omit [Finite D] in
theorem normal₂ : G₂ ≤ Subgroup.normalizer (G₂' : Set D) :=
  le_normalizer_of_relIndex_two H.le₂ H.idx₂

theorem normal_T' : G₁ ⊓ G₂ ≤ Subgroup.normalizer ((G₁' ⊓ G₂' : Subgroup D) : Set D) :=
  le_normalizer_of_relIndex_two H.T'_le_T H.relIndex_T

end SubAmalgam

structure AutHyp (G₁ G₂ G₁' G₂' : Subgroup D) (a b s ρ x y : D) : Prop
    extends SubAmalgam G₁ G₂ G₁' G₂' where
  hA : ARel a b s x
  hAρ : ARho a b s x ρ
  hB : MRelB a b s ρ y
  card : Nat.card ↥(Subgroup.closure ({a, b, s, ρ} : Set D)) = 64
  eT : Subgroup.closure ({a, b, s, ρ} : Set D) = G₁' ⊓ G₂'
  eG₁ : Subgroup.closure ({a, b, s, ρ, x} : Set D) = G₁'
  eG₂ : Subgroup.closure ({a, b, s, ρ, y} : Set D) = G₂'
  pCore₁ : pCoreOf 2 G₁' = Q1r.map (embR hA.toTRel hAρ.toRhoRel)
  pCore₂ : pCoreOf 2 G₂' = Q2r.map (embR hA.toTRel hAρ.toRhoRel)

namespace AutHyp

variable (H : AutHyp G₁ G₂ G₁' G₂' a b s ρ x y)

include H

abbrev emb : Tr →* D := embR H.hA.toTRel H.hAρ.toRhoRel

omit [Finite D] in
theorem emb_injective : Function.Injective H.emb :=
  embR_injective H.hA.toTRel H.hAρ.toRhoRel H.card

omit [Finite D] in
theorem range_emb : H.emb.range = G₁' ⊓ G₂' :=
  (embR_range H.hA.toTRel H.hAρ.toRhoRel).trans H.eT

omit [Finite D] in
theorem card_T' : Nat.card ↥(G₁' ⊓ G₂') = 64 := by rw [← H.eT]; exact H.card

theorem card_T : Nat.card ↥(G₁ ⊓ G₂) = 128 := by
  have := card_eq_of_relIndex_two H.T'_le_T H.relIndex_T
  rw [H.card_T'] at this
  omega

omit [Finite D] in
theorem x_mem : x ∈ G₁' := H.eG₁ ▸ Subgroup.subset_closure (by simp)

omit [Finite D] in
theorem y_mem : y ∈ G₂' := H.eG₂ ▸ Subgroup.subset_closure (by simp)

omit [Finite D] in
theorem card_pCore₁ : Nat.card ↥(pCoreOf 2 G₁') = 32 := by
  rw [H.pCore₁, ← card_Q1r]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective Q1r _ H.emb_injective).toEquiv).symm

theorem card_pCoreT₁ : Nat.card ↥(pCoreOf 2 G₁) = 64 := by
  have := card_eq_of_relIndex_two H.amalgam.pCoreOf_left_le H.amalgam.relIndex_pCoreOf_T_left
  rw [H.card_T] at this
  omega

end AutHyp

theorem pCoreOf_inf_eq_of_relIndex_two {G G' : Subgroup D} (hle : G' ≤ G) (hi : G'.relIndex G = 2) :
    pCoreOf 2 G ⊓ G' = pCoreOf 2 G' := by
  have hnormG : G ≤ Subgroup.normalizer (G' : Set D) := le_normalizer_of_relIndex_two hle hi
  have hnormE : G ≤ Subgroup.normalizer (pCoreOf 2 G' : Set D) :=
    hnormG.trans (normalizer_le_normalizer_pCoreOf 2 G')
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (IsPGroup.to_le (pCoreOf_isPGroup 2 G) inf_le_left)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G (hle hg)) u
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg : g ∈
      Subgroup.normalizer (G' : Set D)) u
    simp only [Subgroup.mem_inf] at h1 h2 ⊢
    exact and_congr h1 h2
  · exact le_inf (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 G').trans hle) hnormE (pCoreOf_isPGroup 2 G')) (pCoreOf_le 2 G')

theorem exists_fixed_conj_of_cube {x : D} (hx : x ^ 3 = 1) {S : Set D}
    (hS : ∀ g ∈ S, x * g * x⁻¹ ∈ S) (h3 : ¬ 3 ∣ S.ncard) : ∃ g ∈ S, x * g * x⁻¹ = g := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxxx : x * x * x = 1 := by rw [← pow_three']; exact hx
  let f : S → S := fun g => ⟨x * g * x⁻¹, hS g g.2⟩
  have hf3 : ∀ g : S, f (f (f g)) = g := by
    intro g
    apply Subtype.ext
    show x * (x * (x * (g : D) * x⁻¹) * x⁻¹) * x⁻¹ = g
    calc x * (x * (x * (g : D) * x⁻¹) * x⁻¹) * x⁻¹
        = (x * x * x) * (g : D) * (x * x * x)⁻¹ := by group
      _ = g := by rw [hxxx]; simp
  let σ : Equiv.Perm S := ⟨f, fun g => f (f g), hf3, hf3⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext g
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact congrArg Subtype.val (hf3 g)
  have : Fintype S := Fintype.ofFinite S
  have hα : ¬ 3 ∣ Fintype.card S := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact h3
  obtain ⟨g, hg⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hα hσ
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

namespace AutHyp

variable (H : AutHyp G₁ G₂ G₁' G₂' a b s ρ x y)

include H

theorem exists_tau₁ : ∃ τ₁ ∈ pCoreOf 2 G₁, τ₁ ∉ G₁' ∧ x * τ₁ * x⁻¹ = τ₁ := by
  have hxG₁' : x ∈ G₁' := H.x_mem
  have hxG₁ : x ∈ G₁ := H.le₁ hxG₁'
  set S : Set D := {g | g ∈ pCoreOf 2 G₁ ∧ g ∉ G₁'} with hS
  have hSconj : ∀ g ∈ S, x * g * x⁻¹ ∈ S := by
    rintro g ⟨hgP, hgG⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ hxG₁) g).mp hgP, ?_⟩
    intro hmem
    apply hgG
    have := G₁'.mul_mem (G₁'.mul_mem (G₁'.inv_mem hxG₁') hmem) hxG₁'
    simpa [mul_assoc] using this
  have hcardP : (↑(pCoreOf 2 G₁) : Set D).ncard = 64 := by
    rw [← Nat.card_coe_set_eq]; exact H.card_pCoreT₁
  have hinter : (↑(pCoreOf 2 G₁) ∩ ↑G₁' : Set D).ncard = 32 := by
    have : (↑(pCoreOf 2 G₁) ∩ ↑G₁' : Set D) = ↑(pCoreOf 2 G₁') := by
      rw [← pCoreOf_inf_eq_of_relIndex_two H.le₁ H.idx₁]; rfl
    rw [this, ← Nat.card_coe_set_eq]
    exact H.card_pCore₁
  have hcardS : S.ncard = 32 := by
    have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (↑(pCoreOf 2 G₁) : Set D) (↑G₁' : Set D)
    have e : (↑(pCoreOf 2 G₁) \ ↑G₁' : Set D) = S := by
      ext g; simp [hS]
    rw [e, hinter, hcardP] at h1
    omega
  obtain ⟨g, hgS, hgx⟩ := exists_fixed_conj_of_cube H.hA.hx hSconj (by rw [hcardS]; norm_num)
  exact ⟨g, hgS.1, hgS.2, hgx⟩

end AutHyp

end CFSG.Quasithin.F6.GoldAmL5
