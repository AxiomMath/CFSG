module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIGroup
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep1
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIBase
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red

public section

namespace CFSG.Quasithin.H13.C1294

section Step2

variable {K : Type} [Group K] [Finite K]

theorem ker_eq_of_perfect (P : Subgroup K) [P.Normal] (hP : IsPGroup 2 P)
    (hsimp : IsSimpleGroup (K ⧸ P)) (hcardQ : Nat.card (K ⧸ P) = 20160)
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (q : W → ZMod 2)
    (ρ : K →* (W ≃ₗ[ZMod 2] W))
    (hO : ρ.range ≤ orthogonalSubgroupOf q)
    (hcardO : Nat.card (orthogonalSubgroupOf q) = 40320)
    (hbig : 10080 ≤ Nat.card ρ.range)
    (hno2 : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ orthogonalSubgroupOf q →
      (∀ γ ∈ orthogonalSubgroupOf q, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → Nat.card N ≠ 2) :
    ρ.ker = P := by
  classical
  haveI : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  haveI : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hNP : ρ.ker ⊔ P ≠ ⊤ := by
    intro htop
    have hQ : IsPGroup 2 (K ⧸ ρ.ker) := by
      intro q'
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q'
      have hk : k ∈ ρ.ker ⊔ P := by rw [htop]; exact Subgroup.mem_top k
      obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup_of_normal_left.1 hk
      obtain ⟨j, hj⟩ := hP ⟨p, hp⟩
      refine ⟨j, ?_⟩
      have hpow : p ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have e : (QuotientGroup.mk k : K ⧸ ρ.ker) = QuotientGroup.mk p := by
        rw [← hnp, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
      rw [e, ← QuotientGroup.mk_pow, hpow, QuotientGroup.mk_one]
    have hperfQ : ⁅(⊤ : Subgroup (K ⧸ ρ.ker)), (⊤ : Subgroup (K ⧸ ρ.ker))⁆ = ⊤ := by
      have hsurj : Function.Surjective (QuotientGroup.mk' ρ.ker) := QuotientGroup.mk_surjective
      have h1 := Subgroup.map_commutator (QuotientGroup.mk' ρ.ker) (H₁ := (⊤ : Subgroup K))
        (H₂ := (⊤ : Subgroup K))
      rw [hperf, Subgroup.map_top_of_surjective _ hsurj] at h1
      exact h1.symm
    have hsub := subsingleton_of_perfect_isPGroup hQ hperfQ
    have hr : ρ.range = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨k, rfl⟩
      have : (QuotientGroup.mk k : K ⧸ ρ.ker) = 1 := Subsingleton.elim _ _
      have hk : k ∈ ρ.ker := (QuotientGroup.eq_one_iff k).1 this
      exact hk
    rw [hr, Subgroup.card_bot] at hbig
    norm_num at hbig
  have hNle : ρ.ker ≤ P := by
    haveI := hsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map (QuotientGroup.mk' P)) with h | h
    · intro n hn
      have hmem : QuotientGroup.mk' P n ∈ ρ.ker.map (QuotientGroup.mk' P) :=
        Subgroup.mem_map_of_mem _ hn
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    · exfalso
      apply hNP
      rw [eq_top_iff]
      intro k _
      have hk : QuotientGroup.mk' P k ∈ ρ.ker.map (QuotientGroup.mk' P) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.1 hk
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnk
      have hnp : n⁻¹ * k ∈ P := (QuotientGroup.eq).1 hnk
      exact Subgroup.mem_sup_of_normal_left.2 ⟨n, hn, n⁻¹ * k, hnp, by group⟩
  have hcard : Nat.card ρ.range = ρ.ker.relIndex P * 20160 := by
    have h1 : Nat.card ρ.range = ρ.ker.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv).symm
    rw [h1, ← Subgroup.relIndex_mul_index hNle]
    rw [show P.index = 20160 from hcardQ]
  have hr2 : ρ.ker.relIndex P ≤ 2 := by
    have h := Subgroup.card_le_of_le hO
    rw [hcardO, hcard] at h
    omega
  have hr0 : ρ.ker.relIndex P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcard
    rw [hcard] at hbig
    omega
  have hr1 : ρ.ker.relIndex P = 1 := by
    by_contra hne
    have h2 : ρ.ker.relIndex P = 2 := by omega
    have hrO : ρ.range = orthogonalSubgroupOf q := by
      apply Subgroup.eq_of_le_of_card_ge hO
      rw [hcardO, hcard, h2]
    have hcardN' : Nat.card (P.map ρ) = 2 := by
      have hr' : (ρ.comp P.subtype).range = P.map ρ := by
        rw [← MonoidHom.map_range, Subgroup.range_subtype]
      have hk : (ρ.comp P.subtype).ker = ρ.ker.subgroupOf P := by
        ext x
        simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hc := Nat.card_congr (QuotientGroup.quotientKerEquivRange (ρ.comp P.subtype)).toEquiv
      rw [← hr', ← hc, hk]
      exact h2
    have hsub : P.map ρ ≤ orthogonalSubgroupOf q := le_trans (Subgroup.map_le_range ρ P) hO
    have hnorm : ∀ γ ∈ orthogonalSubgroupOf q, ∀ n ∈ P.map ρ, γ * n * γ⁻¹ ∈ P.map ρ := by
      intro γ hγ n hn
      rw [← hrO] at hγ
      obtain ⟨k, rfl⟩ := hγ
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hn
      refine Subgroup.mem_map.2 ⟨k * p * k⁻¹, ?_, ?_⟩
      · exact Subgroup.Normal.conj_mem inferInstance p hp k
      · simp [map_mul, map_inv]
    exact hno2 (P.map ρ) hsub hnorm hcardN'
  exact le_antisymm hNle (Subgroup.relIndex_eq_one.1 hr1)

end Step2

section Step2Concrete

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem K₁_le_normalizer_u128 {K₁ V V₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G))) :
    K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
  fun k hk => le_normalizer_conjClosure V _ (K₁_le_normalizer hK hk)

theorem step2_main {K₁ V V₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (D : HatModelU (u128 V V₁))
    (h5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2)
    (F4 : FactF4) :
    ∃ q : D.V → ZMod 2, (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
      (D.img K₁).relIndex (orthogonalSubgroupOf q) = 2 ∧ Nat.card (D.img K₁) = 20160 ∧
      ∀ k : G, ∀ hk : k ∈ K₁,
        D.ρ ⟨k, K₁_le_normalizer_u128 (V := V) hK hk⟩ = 1 ↔ k ∈ pCoreOf 2 K₁ := by
  classical
  obtain ⟨hdim, q, hpolar, -, ⟨S, hS3, hSq⟩, hΓO, hidx⟩ := h5
  have hnd : ∀ v : D.V, (∀ w, D.B v w = 0) → v = 0 := fun v hv => L128A.HatU.B_nondegenerate D v hv
  obtain ⟨hcardO, hno2, -⟩ := F4 D.V q D.B hdim hpolar hnd ⟨S, hS3, hSq⟩
  have hK₁U := K₁_le_normalizer_u128 (V := V) hK
  set Γ := D.img (Subgroup.normalizer (V₁ : Set G)) with hΓdef
  set Kd := D.img K₁ with hKd
  set O := orthogonalSubgroupOf q with hOdef
  set ρK : ↥K₁ →* (D.V ≃ₗ[ZMod 2] D.V) := D.ρ.comp (Subgroup.inclusion hK₁U) with hρK
  have hrange : ρK.range = Kd := (L1294.img_eq_range D hK₁U).symm
  have hKΓ : Kd ≤ Γ := L1294.img_mono D (K₁_le_normalizer hK)
  have hΓO' : Γ ≤ O := hΓO
  have hKO : Kd ≤ O := le_trans hKΓ hΓO'
  have hO : ρK.range ≤ O := by rw [hrange]; exact hKO
  have hrelΓ : Γ.relIndex O * Nat.card Γ = 40320 := by
    have h := Subgroup.relIndex_mul_card (H := Γ) (K := O)
    rw [inf_eq_left.2 hΓO', hcardO] at h
    exact h
  have hΓcard : 20160 ≤ Nat.card Γ := by
    have hpos : 0 < Nat.card Γ := by
      rcases Nat.eq_zero_or_pos (Nat.card Γ) with h0 | h0
      · rw [h0, mul_zero] at hrelΓ; omega
      · exact h0
    nlinarith
  have hrelK : Kd.relIndex Γ * Nat.card Kd = Nat.card Γ := by
    have h := Subgroup.relIndex_mul_card (H := Kd) (K := Γ)
    rw [inf_eq_left.2 hKΓ] at h
    exact h
  have hle : Nat.card Γ ≤ 2 * Nat.card Kd := by
    rw [← hrelK]
    exact Nat.mul_le_mul_right _ himg
  have hbigKd : 10080 ≤ Nat.card Kd := by omega
  have hbig : 10080 ≤ Nat.card ρK.range := by
    rw [hrange]
    exact hbigKd
  have hker : ρK.ker = CFSG.pCore 2 ↥K₁ :=
    ker_eq_of_perfect (CFSG.pCore 2 ↥K₁) CFSG.pCore_isPGroup (isSimpleGroup_quot hK4)
      (index_pCore_eq hK4) (perfect_top_of_cComp hK) q ρK hO hcardO hbig hno2
  have hcardK : Nat.card Kd = 20160 := by
    rw [← hrange]
    have h1 : Nat.card ρK.range = ρK.ker.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρK).toEquiv).symm
    rw [h1, hker, index_pCore_eq hK4]
  refine ⟨q, hpolar, ?_, hcardK, ?_⟩
  · have h := Subgroup.relIndex_mul_card (H := Kd) (K := O)
    rw [inf_eq_left.2 hKO, hcardO, hcardK] at h
    exact Nat.eq_of_mul_eq_mul_right (show 0 < 20160 by norm_num) (h.trans (by norm_num))
  · intro k hk
    have hmem : (⟨k, hk⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ ↔ k ∈ pCoreOf 2 K₁ := by
      constructor
      · intro h
        exact Subgroup.mem_map.2 ⟨⟨k, hk⟩, h, rfl⟩
      · intro h
        obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.1 h
        have : x = ⟨k, hk⟩ := Subtype.ext hxk
        rw [← this]
        exact hx
    rw [← hmem, ← hker]
    exact MonoidHom.mem_ker.symm

end Step2Concrete

end CFSG.Quasithin.H13.C1294
