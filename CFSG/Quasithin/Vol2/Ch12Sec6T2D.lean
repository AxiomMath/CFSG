module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Syl
public import CFSG.Quasithin.Vol2.Ch12Sec6T2A6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N
open scoped IsMulCommutative

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def psiP (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ↥L →* Equiv.Perm (Fin 8) :=
  (alternatingGroup (Fin 8)).subtype.comp (S126L19a.psi F hH)

theorem actsAs_psiP (F : Frame126 T L V) (hH : Hyp126 G T L V) (l : ↥L) :
    ActsAs F l (psiP F hH l) :=
  S126L19a.actsAs_psi F hH l

theorem psiP_mem (F : Frame126 T L V) (hH : Hyp126 G T L V) (l : ↥L) :
    psiP F hH l ∈ alternatingGroup (Fin 8) :=
  (S126L19a.psi F hH l).2

theorem psiP_stab (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {l : ↥L} (hl : (l : G) ∈ Gv v) :
    (psiP F hH l 0 = 0 ∧ psiP F hH l 1 = 1) ∨ (psiP F hH l 0 = 1 ∧ psiP F hH l 1 = 0) :=
  (mem_Gv_iff h1222 F hH hv hβ (Subgroup.le_normalizer l.2) (hH.hyp.irrPlus.2.2.1 l.2)
    (actsAs_psiP F hH l)).1 hl

omit [Finite G] in
theorem Lv_le_L (L : Subgroup G) (v : G) : Lv L v ≤ L :=
  (perfectCore_le _).trans inf_le_left

omit [Finite G] in
theorem Lv_le_Gv (L : Subgroup G) (v : G) : Lv L v ≤ Gv v :=
  (perfectCore_le _).trans inf_le_right

theorem exists_Lv_of_A6s (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    ∀ a ∈ A6s, ∃ l : ↥L, (l : G) ∈ Lv L v ∧ psiP F hH l = a := by
  set f := psiP F hH with hf
  set K' : Subgroup ↥L := (L ⊓ Gv v).subgroupOf L with hK'
  have hA : A6s ≤ K'.map f := by
    intro a ha
    obtain ⟨h0, h1, hA8⟩ := mem_A6s.1 ha
    obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH ⟨a, hA8⟩
    have hfl : f l = a := by rw [hf, psiP, MonoidHom.comp_apply, hl]; rfl
    refine ⟨l, ?_, hfl⟩
    show (l : G) ∈ L ⊓ Gv v
    refine ⟨l.2, (mem_Gv_iff h1222 F hH hv hβ (Subgroup.le_normalizer l.2)
      (hH.hyp.irrPlus.2.2.1 l.2) (actsAs_psiP F hH l)).2 (Or.inl ?_)⟩
    rw [← hf, hfl]
    exact ⟨h0, h1⟩
  have hA' : A6s ≤ (perfectCore K').map f := by
    rw [map_perfectCore]
    exact le_perfectCore_of_perfect hA A6s_perfect
  have hLv : (perfectCore K').map L.subtype = Lv L v := by
    rw [map_perfectCore, hK', Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rfl
  intro a ha
  obtain ⟨y, hy, hya⟩ := hA' ha
  refine ⟨y, ?_, hya⟩
  rw [← hLv]
  exact ⟨y, hy, rfl⟩

theorem psi_pCore_eq_one (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {y : ↥L}
    (hy : (y : G) ∈ pCoreOf 2 (Lv L v)) : psiP F hH y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := psiP F hH with hf
  have hOL : pCoreOf 2 (Lv L v) ≤ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Lv_le_L L v)
  set N : Subgroup (Equiv.Perm (Fin 8)) := ((pCoreOf 2 (Lv L v)).subgroupOf L).map f with hN
  have hN2 : IsPGroup 2 N := by
    have h1 : IsPGroup 2 ((pCoreOf 2 (Lv L v)).subgroupOf L) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Lv L v)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hOL).symm
    exact h1.map f
  have hNst : ∀ n ∈ N, ((n 0 = 0 ∧ n 1 = 1) ∨ (n 0 = 1 ∧ n 1 = 0)) ∧
      n ∈ alternatingGroup (Fin 8) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzG : (z : G) ∈ Gv v :=
      Lv_le_Gv L v ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) hz)
    exact ⟨psiP_stab h1222 F hH hv hβ hzG, psiP_mem F hH z⟩
  have hNA : ∀ a ∈ A6s, ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha n hn
    obtain ⟨l, hl, rfl⟩ := exists_Lv_of_A6s h1222 F hH hv hβ a ha
    obtain ⟨z, hz, rfl⟩ := hn
    refine ⟨l * z * l⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hz' : (z : G) ∈ pCoreOf 2 (Lv L v) := hz
    show ((l : G) * z * (l : G)⁻¹) ∈ pCoreOf 2 (Lv L v)
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Lv L v) hl) z).1 hz'
  have hN0 : N ⊓ A6s = ⊥ := eq_bot_of_normal inf_le_right
    (fun a ha n hn => ⟨hNA a ha n hn.1, A6s.mul_mem (A6s.mul_mem ha hn.2) (A6s.inv_mem ha)⟩)
    (hN2.to_inf_left)
  have hconjA : ∀ n : Equiv.Perm (Fin 8), ((n 0 = 0 ∧ n 1 = 1) ∨ (n 0 = 1 ∧ n 1 = 0)) →
      n ∈ alternatingGroup (Fin 8) → ∀ a ∈ A6s, n * a * n⁻¹ ∈ A6s := by
    intro n hn hnA a ha
    obtain ⟨h0, h1, haA⟩ := mem_A6s.1 ha
    have hi0 : n⁻¹ 0 = 0 ∨ n⁻¹ 0 = 1 := by
      rcases hn with ⟨e0, e1⟩ | ⟨e0, e1⟩
      · exact Or.inl (by rw [Equiv.Perm.inv_eq_iff_eq, e0])
      · exact Or.inr (by rw [Equiv.Perm.inv_eq_iff_eq, e1])
    have hi1 : n⁻¹ 1 = 0 ∨ n⁻¹ 1 = 1 := by
      rcases hn with ⟨e0, e1⟩ | ⟨e0, e1⟩
      · exact Or.inr (by rw [Equiv.Perm.inv_eq_iff_eq, e1])
      · exact Or.inl (by rw [Equiv.Perm.inv_eq_iff_eq, e0])
    refine mem_A6s.2 ⟨?_, ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply]
      rcases hi0 with e | e
      · rw [e, h0]
        exact (Equiv.Perm.inv_eq_iff_eq.1 e).symm
      · rw [e, h1]
        exact (Equiv.Perm.inv_eq_iff_eq.1 e).symm
    · simp only [Equiv.Perm.mul_apply]
      rcases hi1 with e | e
      · rw [e, h0]
        exact (Equiv.Perm.inv_eq_iff_eq.1 e).symm
      · rw [e, h1]
        exact (Equiv.Perm.inv_eq_iff_eq.1 e).symm
    · exact (alternatingGroup (Fin 8)).mul_mem ((alternatingGroup (Fin 8)).mul_mem hnA haA)
        ((alternatingGroup (Fin 8)).inv_mem hnA)
  have hNbot : ∀ n ∈ N, n = 1 := by
    intro n hn
    obtain ⟨hst, hnA⟩ := hNst n hn
    have hcomm : ∀ a ∈ A6s, n * a = a * n := by
      intro a ha
      have h1 : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ A6s := by
        refine ⟨?_, A6s.mul_mem (hconjA n hst hnA a ha) (A6s.inv_mem ha)⟩
        have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
        rw [e]
        exact N.mul_mem hn (hNA a ha _ (N.inv_mem hn))
      rw [hN0, Subgroup.mem_bot] at h1
      calc n * a = n * a * n⁻¹ * a⁻¹ * (a * n) := by group
        _ = a * n := by rw [h1, one_mul]
    rcases eq_of_comm hcomm with h | h
    · exact h
    · exfalso
      rw [h, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hnA
      exact absurd hnA (by decide)
  exact hNbot _ ⟨y, hy, rfl⟩

theorem perm_of_mem_D (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {d : G}
    (hd : d ∈ centralizerSection ((L ⊔ T) ⊓ Gv v) (Lv L v) (pCoreOf 2 (Lv L v)))
    {τ : Equiv.Perm (Fin 8)} (hτ : ActsAs F d τ) : τ = 1 ∨ τ = Equiv.swap 0 1 := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hdH : d ∈ (L ⊔ T) ⊓ Gv v := hd.1
  refine eq_of_comm fun a ha => ?_
  obtain ⟨l, hl, hla⟩ := exists_Lv_of_A6s h1222 F hH hv hβ a ha
  have hc := hd.2.2.2 l hl
  have hcL : (l : G) * d * (l : G)⁻¹ * d⁻¹ ∈ L := by
    have h1 : d * (l : G)⁻¹ * d⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hLTL hdH.1) _).1 (L.inv_mem l.2)
    have e : (l : G) * d * (l : G)⁻¹ * d⁻¹ = l * (d * (l : G)⁻¹ * d⁻¹) := by group
    rw [e]
    exact L.mul_mem l.2 h1
  have hact1 := (actsAs_psiP F hH l).commutator hτ (hLV l.2) (hLTV hdH.1)
  have hact2 := actsAs_psiP F hH ⟨_, hcL⟩
  have hone := psi_pCore_eq_one h1222 F hH hv hβ (y := ⟨_, hcL⟩) hc
  rw [hone] at hact2
  have e := hact1.unique hact2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (hLV l.2) (hLTV hdH.1)) (Subgroup.inv_mem _ (hLV l.2))) (Subgroup.inv_mem _ (hLTV hdH.1)))
  rw [hla] at e
  calc τ * a = (a * τ * a⁻¹ * τ⁻¹)⁻¹ * (a * τ) := by group
    _ = a * τ := by rw [e, inv_one, one_mul]

theorem isPGroup_D (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    IsPGroup 2 ↥(centralizerSection ((L ⊔ T) ⊓ Gv v) (Lv L v) (pCoreOf 2 (Lv L v))) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  rintro ⟨d, hd⟩
  have hdH : d ∈ (L ⊔ T) ⊓ Gv v := hd.1
  obtain ⟨τ, hτ⟩ := exists_actsAs F hH (hLTL hdH.1) (hLTV hdH.1)
  have hτ2 : τ * τ = 1 := by
    rcases perm_of_mem_D h1222 F hH hv hβ hd hτ with h | h
    · rw [h, one_mul]
    · rw [h, Equiv.swap_mul_self]
  have hd2 : ActsAs F (d * d) 1 := by
    have := hτ.mul hτ (hLTV hdH.1)
    rwa [hτ2] at this
  have hd2C : d * d ∈ Subgroup.centralizer (V : Set G) :=
    mem_centralizer_of_actsAs_one F hVL hLV (Subgroup.mul_mem _ (hLTL hdH.1) (hLTL hdH.1))
      (Subgroup.mul_mem _ (hLTV hdH.1) (hLTV hdH.1)) hd2
  obtain ⟨m, hm⟩ := isPGroup_CLT_V h1222 hH ⟨d * d, (L ⊔ T).mul_mem hdH.1 hdH.1, hd2C⟩
  refine ⟨m + 1, Subtype.ext ?_⟩
  have hm' : (d * d) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_succ', pow_mul, sq, hm']

end S126T2

end CFSG.Quasithin.H13
