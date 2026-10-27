module

public import CFSG.Walter.W67.Section5.P56Ree

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

theorem exists_mem_P₁_comm (hp : s.p = 3) {x : G} (hxE : x ∈ s.fr.E) (hox : orderOf x = 3) :
    ∃ u ∈ f5.P₁, u ≠ 1 ∧ x * u = u * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hox, pow_one])
  obtain ⟨u, hu, hu1, hux⟩ := Borel5.exists_fixed_ne_one hX3 (f5.isPGroup_P₁ hp) f5.P₁_ne_bot
    (Subgroup.zpowers_le.mpr (f5.E_le_normalizer_P₁ hxE))
  refine ⟨u, hu, hu1, ?_⟩
  have := hux x (Subgroup.mem_zpowers x)
  calc x * u = x * u * x⁻¹ * x := by group
    _ = u * x := by rw [this]

theorem tfacts_inf
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) {Q : Subgroup G}
    (hQ3 : IsPGroup 3 Q) (hP₁Q : f5.P₁ ≤ Q) (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G))
    (hJQ : s.J ∈ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3) (h9 : 9 ≤ s.f)
    (hQx : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q) :
    Sec56.TFacts (Q ⊓ Subgroup.centralizer ({x} : Set G)) (3 ^ (s.f / 3)) s.J := by
  have hfpf := f5.fpf_of_isPGroup h22 h26i hp hQ3 hBQ hEQ
  have hTL := f5.inf_centralizer_le_L h26i hJR hR hp hQ3 hP₁Q hBQ hfpf hJQ hxE hox h9
  obtain ⟨-, h3f, -⟩ := s.exists_ree h26i hJR hR hp hxE hox h9
  refine s.tfacts_of_nine h26i hJR hR hp hxE hox h9 hTL ?_
  rw [hQx, Hyp.q, hp, ← pow_mul, Nat.div_mul_cancel h3f]

theorem exists_pow_three_ne_one_nine
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) {Q : Subgroup G}
    (hQ3 : IsPGroup 3 Q) (hP₁Q : f5.P₁ ≤ Q) (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G))
    (hJQ : s.J ∈ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3) (h9 : 9 ≤ s.f)
    (hQx : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q) :
    ∃ y ∈ Q, y ^ 3 ≠ 1 := by
  obtain ⟨y, hyT, hy3⟩ :=
    (f5.tfacts_inf h22 h26i hJR hR hp hQ3 hP₁Q hBQ hEQ hJQ hxE hox h9 hQx).exists_pow_three_ne_one
  exact ⟨y, (Subgroup.mem_inf.mp hyT).1, hy3⟩

theorem false_of_center_nine
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) {Q : Subgroup G}
    (hQ3 : IsPGroup 3 Q) (hP₁Q : f5.P₁ ≤ Q) (hP₁C : f5.P₁ ≤ Subgroup.centralizer (Q : Set G))
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G))
    (hJQ : s.J ∈ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3) (h9 : 9 ≤ s.f)
    (hQx : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q) : False := by
  have hT := f5.tfacts_inf h22 h26i hJR hR hp hQ3 hP₁Q hBQ hEQ hJQ hxE hox h9 hQx
  have hJx : s.J ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (s.commute_J (s.fr.E_le_H hxE)).symm
  have hJT : s.J ∈ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    Sec54.mem_normalizer_inf hJQ (Subgroup.le_normalizer hJx)
  have hZ := hT.center_inf_J hJT
  obtain ⟨u, hu, hu1, hux⟩ := f5.exists_mem_P₁_comm hp hxE hox
  apply hu1
  have huT : u ∈ Q ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hP₁Q hu, Subgroup.mem_centralizer_singleton_iff.mpr hux.symm⟩
  have hmem : u ∈ (Q ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      Subgroup.centralizer ((Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({s.J} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨huT, Subgroup.mem_centralizer_iff.mpr
      fun t ht => Subgroup.mem_centralizer_iff.mp (hP₁C hu) t (Subgroup.mem_inf.mp ht).1⟩, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (s.commute_J (s.K_le_H (f5.P₁_le hu)))
  rwa [hZ, Subgroup.mem_bot] at hmem

end Frame5

end CFSG.Walter.W67
