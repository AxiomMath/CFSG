module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.S15223P4.C

theorem mem_of_orderOf_pow_three {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup (Q ⧸ CFSG.pCore 2 Q)] {N : Subgroup Q} [N.Normal] {y : Q} (hyN : y ∈ N)
    (hy3 : orderOf y = 3) {x : Q} {a : ℕ} (hx : orderOf x = 3 ^ a) : x ∈ N := by
  have hR2 : IsPGroup 2 (CFSG.pCore 2 Q) := CFSG.pCore_isPGroup
  have hmap : N.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) = ⊤ := by
    have hnorm : (N.map (QuotientGroup.mk' (CFSG.pCore 2 Q))).Normal :=
      Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore 2 Q)))
      with h | h
    · exfalso
      have hy : QuotientGroup.mk' (CFSG.pCore 2 Q) y ∈ N.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) :=
        Subgroup.mem_map_of_mem _ hyN
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
      obtain ⟨m, hm⟩ := hR2 ⟨y, hy⟩
      have hm' : y ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h3 : 3 ∣ 2 ^ m := hy3 ▸ orderOf_dvd_of_pow_eq_one hm'
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    · exact h
  have hxm : QuotientGroup.mk' (CFSG.pCore 2 Q) x ∈ N.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 hxm
  have hr : n⁻¹ * x ∈ CFSG.pCore 2 Q := QuotientGroup.eq.1 hnx
  obtain ⟨b, hb⟩ := hR2 ⟨n⁻¹ * x, hr⟩
  have hb' : (n⁻¹ * x) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hπn : (QuotientGroup.mk n : Q ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
  have hπx : (QuotientGroup.mk x : Q ⧸ N) = QuotientGroup.mk (n⁻¹ * x) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπn, inv_one, one_mul]
  have h1 : (QuotientGroup.mk x : Q ⧸ N) ^ 3 ^ a = 1 := by
    rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
    rfl
  have h2 : (QuotientGroup.mk x : Q ⧸ N) ^ 2 ^ b = 1 := by
    rw [hπx, ← QuotientGroup.mk_pow, hb']
    rfl
  have hg := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow a b (by norm_num)), pow_one] at hg
  exact (QuotientGroup.eq_one_iff x).1 hg

theorem isSimple_quot_of_isLnTwo_four {G : Type} [Group G] {K : Subgroup G}
    (h : IsLnTwo 4 (OTwoQuot K)) : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨e⟩ := h
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 4) (by norm_num)
      (Or.inl (by norm_num))).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).trans e).isSimpleGroup

end CFSG.Quasithin.S15223P4.C
