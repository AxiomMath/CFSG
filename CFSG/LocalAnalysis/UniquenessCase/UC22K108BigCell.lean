module

public import CFSG.GroupTheory.TitsSystem.Parabolic
import CFSG.Milestones.ASVolI.I2BNWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal]
  {S : Set (WeylGroup B N)}

theorem k108big_exists_eq_mul_of_mem_dc {w : WeylGroup B N} {y z : G} (hy : y ∈ dc B N w)
    (hz : z ∈ dc B N w) : ∃ b ∈ B, ∃ b' ∈ B, y = b * z * b' := by
  obtain ⟨n, hn, c, hc, c', hc', rfl⟩ := mem_dc_iff.1 hz
  obtain ⟨d, hd, d', hd', rfl⟩ := (mem_dc_of_lift hn).1 hy
  exact ⟨d * c⁻¹, B.mul_mem hd (B.inv_mem hc), c'⁻¹ * d', B.mul_mem (B.inv_mem hc') hd',
    by group⟩

theorem k108big_exists_image_dc_eq (h : IsBNPair B N S) (φ : G ≃* G)
    (hφ : ∀ x, φ x ∈ B ↔ x ∈ B) (w : WeylGroup B N) : ∃ v, φ '' dc B N w = dc B N v := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨v, hv⟩ := h.exists_mem_dc (φ n)
  refine ⟨v, Set.Subset.antisymm ?_ fun y hy => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_dc_mk_iff.1 hx
    rw [map_mul, map_mul]
    exact mul_mem_dc hv ((hφ b).2 hb) ((hφ b').2 hb')
  · obtain ⟨b, hb, b', hb', rfl⟩ := k108big_exists_eq_mul_of_mem_dc hy hv
    refine ⟨φ.symm b * n * φ.symm b', mem_dc_mk_iff.2 ⟨_, ?_, _, ?_, rfl⟩, ?_⟩
    · exact (hφ _).1 (by simpa using hb)
    · exact (hφ _).1 (by simpa using hb')
    · simp [map_mul]

theorem k108big_exists_image_dc_gen (h : IsBNPair B N S) (φ : G ≃* G)
    (hφ : ∀ x, φ x ∈ B ↔ x ∈ B) {s : WeylGroup B N} (hs : s ∈ S) :
    ∃ t ∈ S, φ '' dc B N s = dc B N t := by
  obtain ⟨v, hv⟩ := k108big_exists_image_dc_eq h φ hφ s
  refine ⟨v, ?_, hv⟩
  set P := (parabolic B N {s}).map φ.toMonoidHom with hP
  have hmemP : ∀ x, x ∈ P ↔ x ∈ B ∨ x ∈ dc B N v := by
    intro x
    rw [hP, Subgroup.mem_map_equiv,
      CFSG.ASVolI.burnsideI25b_mem_parabolic_single_iff h hs, ← hv]
    constructor
    · rintro (hB | hdc)
      · left
        simpa using (hφ (φ.symm x)).2 hB
      · right
        exact ⟨φ.symm x, hdc, by simp⟩
    · rintro (hB | ⟨y, hy, rfl⟩)
      · left
        exact (hφ _).1 (by simpa using hB)
      · right
        simpa using hy
  have hBP : B ≤ P := fun b hb => (hmemP b).2 (Or.inl hb)
  obtain ⟨J, hJ, hPJ⟩ := h.exists_parabolic hBP
  by_cases hJe : J = ∅
  · exfalso
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective s
    have h1 : φ n ∈ P := (hmemP _).2 (Or.inr (hv ▸ ⟨n, hn ▸ coe_mem_dc n, rfl⟩))
    rw [hPJ, hJe, parabolic_empty] at h1
    exact h.ne_one hs (hn ▸ mk_eq_one_iff.2 ((hφ _).1 h1))
  · obtain ⟨j, hj⟩ := Set.nonempty_iff_ne_empty.2 hJe
    obtain ⟨nj, hnj⟩ := QuotientGroup.mk_surjective j
    have hmem : (nj : G) ∈ P := by
      rw [hPJ]
      exact (h.mem_parabolic_iff_of_mem_dc hJ (hnj ▸ coe_mem_dc nj)).2
        (Subgroup.subset_closure hj)
    rcases (hmemP _).1 hmem with hB | hdc
    · exact absurd (hnj ▸ mk_eq_one_iff.2 hB) (h.ne_one (hJ hj))
    · exact h.eq_of_mem_dc (hnj ▸ coe_mem_dc nj) hdc ▸ hJ hj

theorem k108big_exists_image_dc_length_le (h : IsBNPair B N S) (φ : G ≃* G)
    (hφ : ∀ x, φ x ∈ B ↔ x ∈ B) (w : WeylGroup B N) :
    ∃ v, φ '' dc B N w = dc B N v ∧ wordLength S v ≤ wordLength S w := by
  suffices key : ∀ k, ∀ w : WeylGroup B N, wordLength S w = k →
      ∃ v, φ '' dc B N w = dc B N v ∧ wordLength S v ≤ k from key _ w rfl
  intro k
  induction k with
  | zero =>
    intro w hw
    obtain rfl : w = 1 :=
      (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure w)).1 hw
    refine ⟨1, ?_, by simp [wordLength_one]⟩
    rw [dc_one]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hφ y).2 hy
    · intro hx
      exact ⟨φ.symm x, (hφ _).1 (by simpa using hx), by simp⟩
  | succ k ih =>
    intro w hw
    have hw1 : w ≠ 1 := by
      rintro rfl
      rw [wordLength_one] at hw
      omega
    obtain ⟨s, hs, hsw⟩ :=
      exists_left_descent h.bnCore.mul_self_eq_one (h.mem_closure w) hw1
    have hww : s * (s * w) = w := by rw [← mul_assoc, h.mul_self_eq_one hs, one_mul]
    have hlt : wordLength S (s * w) < wordLength S (s * (s * w)) := by rw [hww]; omega
    have hprod : dc B N s * dc B N (s * w) = dc B N w := by
      rw [h.dc_mul_dc_of_lt hs hlt, hww]
    obtain ⟨t, ht, hst⟩ := k108big_exists_image_dc_gen h φ hφ hs
    obtain ⟨v', hv', hlv'⟩ := ih (s * w) (by omega)
    obtain ⟨v, hv⟩ := k108big_exists_image_dc_eq h φ hφ w
    refine ⟨v, hv, ?_⟩
    have himg : φ '' dc B N w = dc B N t * dc B N v' := by
      rw [← hprod, Set.image_mul, hst, hv']
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective v
    have hnv : (n : G) ∈ dc B N v := hn ▸ coe_mem_dc n
    have hnv' : (n : G) ∈ dc B N t * dc B N v' := by rw [← himg, hv]; exact hnv
    have hsub : dc B N t * dc B N v' ⊆ dc B N v' ∪ dc B N (t * v') := by
      rcases h.length_mul_eq_or ht v' with hl | hl
      · rw [h.dc_mul_dc_of_lt ht (by omega)]
        exact Set.subset_union_right
      · rw [h.dc_mul_dc_of_gt ht (by omega)]
    rcases hsub hnv' with h1 | h1
    · rw [h.eq_of_mem_dc hnv h1]
      omega
    · rw [h.eq_of_mem_dc hnv h1]
      have := h.length_mul_le ht v'
      omega

theorem k108big_image_dc_longest (h : IsBNPair B N S) (φ : G ≃* G)
    (hφ : ∀ x, φ x ∈ B ↔ x ∈ B) {w₀ : WeylGroup B N}
    (hmax : ∀ w, wordLength S w ≤ wordLength S w₀) : φ '' dc B N w₀ = dc B N w₀ := by
  obtain ⟨v, hv, -⟩ := k108big_exists_image_dc_length_le h φ hφ w₀
  have hφ' : ∀ x, φ.symm x ∈ B ↔ x ∈ B := fun x => by
    rw [← hφ (φ.symm x)]
    simp
  obtain ⟨u, hu, hlu⟩ := k108big_exists_image_dc_length_le h φ.symm hφ' v
  have huw : u = w₀ := by
    apply h.dc_injective
    rw [← hu, ← hv, Set.image_image]
    simp
  have hpre := CFSG.ASVolI.burnsideI25c_prefix_longest h (J := S) subset_rfl
    (h.mem_closure w₀) (fun w _ => hmax w) (h.mem_closure v)
  have hl : wordLength S v = wordLength S w₀ := by
    rw [huw] at hlu
    have := hmax v
    omega
  have h0 : wordLength S (v⁻¹ * w₀) = 0 := by omega
  rw [hv, inv_mul_eq_one.1
    ((wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure _)).1 h0)]

theorem k108big_cartan_le_normalizer_conj {U : Subgroup G}
    (hUB : B ≤ Subgroup.normalizer (U : Set G)) (n₀ : N) :
    B ⊓ N ≤ Subgroup.normalizer
      ((U.map (MulAut.conj (n₀ : G)).toMonoidHom : Subgroup G) : Set G) := by
  intro c hc
  have hconj : ∀ (K : Subgroup G) (a b : G), K.map (MulAut.conj (b * a)).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom := fun K a b => by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hH : (n₀ : G)⁻¹ * c * (n₀ : G) ∈ B ⊓ N := by
    simpa using CFSG.ASVolI.burnsideI25b_conj_mem_H hc (N.inv_mem n₀.2)
  have hc' : U.map (MulAut.conj ((n₀ : G)⁻¹ * c * (n₀ : G))).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hUB (Subgroup.mem_inf.1 hH).1)
  have key : (U.map (MulAut.conj (n₀ : G)).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      U.map (MulAut.conj (n₀ : G)).toMonoidHom := by
    rw [← hconj U (n₀ : G) c]
    have hcn : c * (n₀ : G) = (n₀ : G) * ((n₀ : G)⁻¹ * c * (n₀ : G)) := by group
    rw [hcn, hconj U _ (n₀ : G), hc']
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 key

theorem k108big_sup_conj_eq_top [IsSimpleGroup G] (h : IsBNPair B N S) {U : Subgroup G}
    (hU : U ≠ ⊥) (hUB : B ≤ Subgroup.normalizer (U : Set G)) (hBU : B ≤ U ⊔ (B ⊓ N))
    {w₀ : WeylGroup B N} (hmax : ∀ w, wordLength S w ≤ wordLength S w₀) {g : G}
    (hg : g ∈ dc B N w₀) : U ⊔ U.map (MulAut.conj g).toMonoidHom = ⊤ := by
  have hconj : ∀ (K : Subgroup G) (a b : G), K.map (MulAut.conj (b * a)).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom := fun K a b => by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  obtain ⟨n₀, hn₀, b, hb, b', hb', rfl⟩ := mem_dc_iff.1 hg
  have hfix : ∀ c ∈ B, U.map (MulAut.conj c).toMonoidHom = U := fun c hc =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hUB hc)
  set V := U.map (MulAut.conj (n₀ : G)).toMonoidHom with hV
  have hred : U ⊔ U.map (MulAut.conj (b * n₀ * b')).toMonoidHom =
      (U ⊔ V).map (MulAut.conj b).toMonoidHom := by
    rw [hconj U b' (b * (n₀ : G)), hfix b' hb', hconj U (n₀ : G) b, Subgroup.map_sup,
      hfix b hb]
  rw [hred]
  suffices hY : U ⊔ V = ⊤ by
    rw [hY]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj b).surjective
  have hHV := k108big_cartan_le_normalizer_conj hUB n₀
  have hHY : B ⊓ N ≤ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hUB (Subgroup.mem_inf.1 hc).1),
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hHV hc)]
  have hBP : B ≤ (U ⊔ V) ⊔ (B ⊓ N) := hBU.trans (sup_le_sup_right le_sup_left _)
  obtain ⟨J, hJ, hPJ⟩ := h.exists_parabolic hBP
  have hBnP : B.map (MulAut.conj (n₀ : G)).toMonoidHom ≤ (U ⊔ V) ⊔ (B ⊓ N) := by
    calc B.map (MulAut.conj (n₀ : G)).toMonoidHom
        ≤ (U ⊔ (B ⊓ N)).map (MulAut.conj (n₀ : G)).toMonoidHom := Subgroup.map_mono hBU
      _ = V ⊔ (B ⊓ N).map (MulAut.conj (n₀ : G)).toMonoidHom := Subgroup.map_sup _ _ _
      _ ≤ (U ⊔ V) ⊔ (B ⊓ N) := by
          refine sup_le_sup le_sup_right ?_
          rintro _ ⟨c, hc, rfl⟩
          exact CFSG.ASVolI.burnsideI25b_conj_mem_H hc n₀.2
  have hn₀J : (n₀ : G) ∈ parabolic B N J := by
    refine (h.mem_and_subset_of_conj_le (Set.empty_subset S) hJ fun x hx => ?_).1
    rw [parabolic_empty] at hx
    rw [← hPJ]
    exact hBnP ⟨x, hx, rfl⟩
  have hw₀J : w₀ ∈ Subgroup.closure J :=
    hn₀ ▸ (h.mem_parabolic_iff_of_mem_dc hJ (coe_mem_dc n₀)).1 hn₀J
  have hJS : J = S := by
    refine Set.Subset.antisymm hJ fun s hs => ?_
    by_contra hsJ
    have := CFSG.ASVolI.burnsideI25b_length_lt_mul_right h hJ hw₀J hs hsJ
    have := hmax (w₀ * s)
    omega
  have hP : (U ⊔ V) ⊔ (B ⊓ N) = ⊤ := by rw [hPJ, hJS, h.parabolic_univ]
  haveI : (U ⊔ V).Normal := Subgroup.normalizer_eq_top_iff.1
    (eq_top_iff.2 (hP.symm.le.trans (sup_le Subgroup.le_normalizer hHY)))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U ⊔ V) with hbot | htop
  · exact absurd (eq_bot_iff.2 (le_sup_left.trans hbot.le)) hU
  · exact htop

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
