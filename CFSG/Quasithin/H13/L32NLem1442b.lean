module

public import CFSG.Quasithin.H13.L32NLem1442a
public import CFSG.Quasithin.H13.L32NLem14324b
public import CFSG.Quasithin.H13.L32NLem14324d
public import CFSG.Quasithin.H13.L32NLem14324n

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

variable {G : Type} [Group G] [Finite G]

theorem exists_e9_alt6 : ∃ c₁ c₂ : ↥(alternatingGroup (Fin 6)), c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧
    c₁ * c₂ = c₂ * c₁ ∧ c₁ ≠ 1 ∧ ∀ i : Fin 3, c₁ ^ (i : ℕ) ≠ c₂ :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, by decide⟩

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem false_of_concl1 (h1 : G112Concl1 (D.img (l32nH T V))) : False := by
  have := C.six_le
  rw [h1.1] at this
  omega

theorem false_of_concl2 (h2 : G112Concl2 (D.img (l32nH T V))) : False := by
  have := C.six_le
  rw [h2.1] at this
  omega

theorem false_of_concl3 (h3 : G112Concl3 (D.img (l32nH T V))) : False := by
  obtain ⟨k, hk⟩ := C.exists_card_X
  have h4 := L14324.card_le_four_of_concl3 C.X_le C.X_elem hk C.pCoreOf_eq_bot h3
  have hdvd := C.card_dvd_of_six h3.1 h4
  obtain ⟨-, P, -, -, hP, -⟩ := h3
  have h27 : 27 ∣ Nat.card ↥(D.img (l32nH T V)) := hP ▸ Subgroup.card_subgroup_dvd_card P
  exact absurd (h27.trans hdvd) (by decide)

theorem false_of_concl6U33
    (h6U : G11.SzG11S.G112Concl6U33S (D.img (l32nH T V))) : False := by
  obtain ⟨k, hk⟩ := C.exists_card_X
  have h8 := L14324.lt_of_concl6U33 C.X_le C.X_elem hk h6U.2
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 3 ≤ k by omega)
    omega
  have h4 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤ 4 := by
    rw [hk]
    exact (Nat.pow_le_pow_right (by norm_num) hk2).trans (by norm_num)
  have hdvd := C.card_dvd_of_six h6U.1.1 h4
  rw [h6U.1.2] at hdvd
  exact absurd hdvd (by decide)

theorem false_of_concl5 (h5 : G112Concl5 D.B (D.img (l32nH T V))) : False := by
  obtain ⟨M⟩ := S8Five.exists_model5 C.g111.alt C.g111.nondegenerate h5
  obtain ⟨P, hPA, hP9, hPc, hP3, hPfix⟩ := M.exists_E9 C.isSylow C.πa_ne C.fix_T
  exact C.no_E9 (hPA.trans M.A_le) hP9 hPc hP3 hPfix

theorem false_of_concl10
    (h10 : G112Concl10 (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    False := by
  classical
  set Γ := D.img (l32nH T V) with hΓ
  obtain ⟨-, -, ⟨φ⟩, h3, -⟩ := h10
  set E := genFittingLayer ↥Γ with hE
  set O := CFSG.pCore 3 ↥Γ with hO
  have hEn : E.Normal := CFSG.ComponentClassification.Layer.normal _
  have hOn : O.Normal := CFSG.pCore_normal
  have hdisj : Disjoint O E := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have hEs : IsSimpleGroup ↥E := φ.isSimpleGroup
    have hON : (O.subgroupOf E).Normal := hOn.subgroupOf E
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf E) with hb | ht
    · exact Subgroup.subgroupOf_eq_bot.mp hb
    · exfalso
      have hle := Subgroup.card_le_of_le (Subgroup.subgroupOf_eq_top.mp ht)
      rw [h3, Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at hle
      exact absurd hle (by decide)
  obtain ⟨c₁, c₂, hc₁, hc₂, hc, hc₁1, hcn⟩ := exists_e9_alt6
  have hOnt : Nontrivial ↥O := by
    rw [← Finite.one_lt_card_iff_nontrivial, h3]
    norm_num
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥O)
  set x : ↥Γ := ((φ.symm c₁ : ↥E) : ↥Γ) with hx
  set y : ↥Γ := ((φ.symm c₂ : ↥E) : ↥Γ) with hy
  have hxE : x ∈ E := (φ.symm c₁).2
  have hyE : y ∈ E := (φ.symm c₂).2
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← Subgroup.coe_pow, ← map_pow, hc₁, map_one, Subgroup.coe_one]
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← Subgroup.coe_pow, ← map_pow, hc₂, map_one, Subgroup.coe_one]
  have hz3 : (z : ↥Γ) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥O) (x := z)
    rw [h3] at h
    exact congrArg Subtype.val h
  have hxy : Commute x y := by
    change (x * y = y * x)
    rw [hx, hy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  have hxz : Commute x (z : ↥Γ) :=
    Subgroup.commute_of_normal_of_disjoint E O hEn hOn (disjoint_comm.mp hdisj) _ _ hxE z.2
  have hyz : Commute y (z : ↥Γ) :=
    Subgroup.commute_of_normal_of_disjoint E O hEn hOn (disjoint_comm.mp hdisj) _ _ hyE z.2
  have hx1 : x ≠ 1 := by
    intro h1
    apply hc₁1
    have h2 : (φ.symm c₁ : ↥E) = 1 := Subtype.ext h1
    simpa using congrArg φ h2
  have hyx : ∀ n : ℕ, x ^ n ≠ y := by
    intro n hn
    apply hcn ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩
    have h2 : (φ.symm c₁) ^ n = φ.symm c₂ := Subtype.ext (by rw [Subgroup.coe_pow]; exact hn)
    rw [← map_pow] at h2
    have h4 := φ.symm.injective h2
    rw [← h4]
    exact (pow_eq_pow_mod n hc₁).symm
  have hzxy : ∀ m n : ℕ, x ^ m * y ^ n ≠ (z : ↥Γ) := by
    intro m n hmn
    apply hz1
    have hmem : (z : ↥Γ) ∈ E := by
      rw [← hmn]
      exact E.mul_mem (E.pow_mem hxE m) (E.pow_mem hyE n)
    have hb : (z : ↥Γ) ∈ O ⊓ E := ⟨z.2, hmem⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hb
    exact Subtype.ext hb
  have h3le := S8Five.three_le_pRank_of_triple hx3 hy3 hz3 hxy hxz hyz hx1 hyx hzxy
  have h2le : CFSG.Assembly.pRank 3 (⊤ : Subgroup ↥Γ) ≤ 2 := C.pRank_img_le_two
  omega

end Ctx

end L1442

end CFSG.Quasithin.H13
