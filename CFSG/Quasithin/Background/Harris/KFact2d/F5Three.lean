module

public import CFSG.Quasithin.Background.Harris.KFact2d.ModelL3
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5P7

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E2P.Asc80
  CFSG.Quasithin.Background.Harris.OrdinaryProofs
open scoped MatrixGroups

theorem center_SL3_three_eq_bot : Subgroup.center SL(3, ZMod 3) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have h1 : r = 1 := by
      have : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1 := by decide
      exact this r (by simpa using hr)
    subst h1
    apply Subtype.ext
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

theorem card_PSL3_three : Nat.card (PSL3 3) = 5616 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e : PSL3 3 ≃* SL(3, ZMod 3) :=
    (QuotientGroup.quotientMulEquivOfEq center_SL3_three_eq_bot).trans QuotientGroup.quotientBot
  rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 3]
  norm_num [ZMod.card, Fin.prod_univ_three]

theorem card_leviC_three : Nat.card (leviC 3) = 48 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Subgroup.card_mul_index (leviC 3)
  rw [index_leviC (by norm_num : (3 : ℕ) ≠ 2), card_PSL3_three] at h
  norm_num at h
  omega

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_of_isSylowTwoOf' {K S : Subgroup X} (h : IsSylowTwoOf S K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = S.subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨IsPGroup.toSylow (h.2.1.comap_subtype) h.2.2, rfl⟩

theorem card_cenZ_three {K S : Subgroup X} (hK : IsPSL 3 3 1 ↥K) (hS : IsSylowTwoOf S K) :
    Nat.card ↥(cenZ K S) = 48 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, U₀, hU₀, hmap⟩ := exists_equiv_special (p := 3) (by norm_num) hK hS
  have hC : Subgroup.centralizer (E2P.zOf U₀ : Set (PSL3 3)) = leviC 3 :=
    centralizer_zOf_eq_leviC (by norm_num) hU₀.1 hU₀.2.1
  have hcen : (Subgroup.centralizer (E2P.zOf (S.subgroupOf K) : Set ↥K)).map e.toMonoidHom =
      Subgroup.centralizer (E2P.zOf U₀ : Set (PSL3 3)) := by
    rw [← hmap]
    ext w
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have hy' := (mem_zOf_map_iff e _ y).1 hy
      have := h _ hy'
      apply e.symm.injective
      simpa using this
    · intro h z hz
      have hz' : e z ∈ E2P.zOf ((S.subgroupOf K).map e.toMonoidHom) :=
        (mem_zOf_map_iff e _ (e z)).2 (by simpa using hz)
      have := h _ hz'
      apply e.injective
      simpa using this
  have hcenK : cenZ K S = (Subgroup.centralizer (E2P.zOf (S.subgroupOf K) : Set ↥K)).map K.subtype := by
    ext x
    rw [mem_cenZ_iff hS.1, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyc⟩
      exact ⟨y, hyc, hy⟩
    · rintro ⟨y, hyc, hy⟩
      exact ⟨y, hy, hyc⟩
  rw [hcenK, Subgroup.card_map_of_injective K.subtype_injective,
    ← Subgroup.card_map_of_injective (f := e.toMonoidHom) (show Function.Injective e.toMonoidHom from e.injective) (K := Subgroup.centralizer (E2P.zOf (S.subgroupOf K) : Set ↥K)),
    hcen, hC, card_leviC_three]

theorem card_sylow_three {K S : Subgroup X} (hK : IsPSL 3 3 1 ↥K) (hS : IsSylowTwoOf S K) :
    Nat.card ↥S = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := exists_equiv_psl3 hK
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf' hS
  have hKc : Nat.card ↥K = 5616 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_congr e.toEquiv]
    exact card_PSL3_three
  have h1 := Sylow.card_eq_multiplicity P
  rw [hKc] at h1
  have hv : (5616 : ℕ).factorization 2 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have : (5616 : ℕ) = 2 ^ 4 * 351 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [hv] at h1
  have h2 : Nat.card ↥(S.subgroupOf K) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  rw [← h2, ← hP]
  simpa using h1

theorem cenMax_three {K T : Subgroup X} (hK : IsPSL 3 3 1 ↥K) (hS : IsSylowTwoOf (T ⊓ K) K) :
    CenMax K T := by
  intro B hSB hBC
  have h16 := card_sylow_three hK hS
  have h48 := card_cenZ_three hK hS
  have hd1 : 16 ∣ Nat.card ↥B := h16 ▸ Subgroup.card_dvd_of_le hSB
  have hd2 : Nat.card ↥B ∣ 48 := h48 ▸ Subgroup.card_dvd_of_le hBC
  obtain ⟨a, ha⟩ := hd1
  have ha3 : a ∣ 3 := by
    rw [ha] at hd2
    have : 16 * a ∣ 16 * 3 := by simpa using hd2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have : a = 1 ∨ a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp ha3 with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases this with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hSB (by rw [h16, ha])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hBC (by rw [h48, ha])

theorem f5_three : StarStmtFor fun q => q = 3 := by
  intro X _ _ K T M V p hp hX hV hVT hTV hA
  subst hp
  obtain ⟨hX', -, -, hL, hM⟩ := hX
  have hK : IsPSL 3 3 1 ↥K := by
    rcases hL with ⟨h, -⟩ | ⟨-, h, -⟩
    · omega
    · exact h
  have := hX'.normal
  have hCen : CenMax K T := cenMax_three hK hX'.isSylow_inf
  have hTM : T ≤ M := by
    have hmem : M ∈ maxOver (⊤ : Subgroup X) T := by
      rw [hX'.minPar.uniqueMax]
      exact Set.mem_singleton M
    exact hmem.2
  exact V_le_pCoreOf_of_cenMax hX'.sup hTM hM hCen hVT hV hA

end CFSG.Quasithin.Background.Harris.KFact2d
