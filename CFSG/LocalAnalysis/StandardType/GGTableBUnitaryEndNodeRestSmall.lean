module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestMult
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestTorus

public section

namespace CFSG.StandardType

namespace TableBUR

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  TableBUE
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)

theorem ggEndNodeAdm_of_pow_eq_one {p r : ℕ} {R : Type} [Group R] {I I' : Set (MulAut R)}
    (h : GGEndNodeAdm p r R I') (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ I') : GGEndNodeAdm p r R I := by
  intro L' _ _ ψ hψ hker hL A hA hAI hr h3 hadm
  refine h L' ψ hψ hker hL A hA (fun a ha => ?_) hr h3 hadm
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨φ, hI φ hφ ?_, hφa⟩
  have hk : ∀ k : ℕ, ∀ l : L', (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [hk p l, hA.2 a ha, MulAut.one_apply, MulAut.one_apply]

section Small

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem diagVec_le_torusThree (h : UnitaryFieldData 2 1 K) {d : ℕ}
    {A : Subgroup ↥(unitarySU 2 1 K d)} (hA : IsElemAbelian 3 A) :
    diagVec A ≤ torusThree K d := by
  intro σ hσ
  obtain ⟨hpow, hprod⟩ := diagVec_props h hA hσ
  refine ⟨hpow, Units.ext ?_⟩
  rw [Units.coe_prod, Units.val_one]
  exact hprod

theorem isEndNode_smv (h : UnitaryFieldData 2 1 K) (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : Kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {A : Subgroup ↥(unitarySU 2 1 K 5)} (hA : IsElemAbelian 3 A)
    (hdiag : ∀ x ∈ A, ∃ σ : Fin 5 → Kˣ, (x : GL (Fin 5) K) = diagHom 5 σ)
    {x : ↥(unitarySU 2 1 K 5)} (hxA : x ∈ A) {m : Fin 5}
    (hxσ : (x : GL (Fin 5) K) = diagHom 5 (smv ω m)) :
    TableBOrth.IsEndNode (A.map (LargeEvenProjMk (unitarySU 2 1 K 5)))
      (LargeEvenProjMk (unitarySU 2 1 K 5) x) := by
  classical
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  set π := LargeEvenProjMk (unitarySU 2 1 K 5) with hπ
  obtain ⟨-, hωinv, -, -, -⟩ := omega_facts hω3 hω1
  have hsm_self : smv ω m m = ω⁻¹ := by simp [smv]
  set S : Finset (Fin 5) := {m}ᶜ with hSdef
  have hSnode : IsNodeOn (smv ω m) S := by
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [hSdef, Finset.mem_compl, Finset.mem_singleton] at hi hj
      rw [smv_apply_ne ω hi, smv_apply_ne ω hj]
    · rw [hSdef, Finset.mem_compl, Finset.mem_singleton, not_not] at hi
      subst hi
      rw [smv_apply_ne ω hj, hsm_self]
      exact hωinv
  have hScard : S.card = 4 := by
    rw [hSdef, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hnp : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h Nat.prime_three (by norm_num) hz hzp
  have hker := ker_projMk_le_center (n := 1) (d := 5) (K := K)
  have hx1 : x ≠ 1 := by
    rintro rfl
    obtain ⟨j, hj⟩ : ∃ j : Fin 5, j ≠ m := ⟨m + 1, by simp⟩
    have h1 : diagHom 5 (smv ω m) = 1 := by rw [← hxσ]; rfl
    have h2 := congrFun (diagHom_injective 5 (h1.trans (map_one _).symm)) j
    rw [smv_apply_ne ω hj, Pi.one_apply] at h2
    exact hω1 h2
  refine isEndNode_map_of_cover π hker (fun y' hy' hy1' => hnp y' hy1' (hA.2 y' hy')) hxA hx1
    (isQuasisimple_blockSU S h hK (by omega) (by rw [hScard]; decide))
    (blockSU_le_centralizer hSnode.1 hxσ)
    (fun g hg g' hg' => commutator_mem_blockSU hSnode hxσ hg hg')
    (centralizer_map_eq_of_noTorsion π (QuotientGroup.mk'_surjective _) hker hnp (hA.2 x hxA))
    fun y' hy' => ?_
  obtain ⟨σ', hσ'⟩ := hdiag y' hy'
  rw [commute_blockSU_iff h hσ']
  obtain ⟨hpow, hprod⟩ := diagVec_props h hA (mem_diagVec_of hy' hσ')
  constructor
  · intro hc
    obtain ⟨j₀, hj₀⟩ : ∃ j : Fin 5, j ≠ m := ⟨m + 1, by simp⟩
    have hj₀S : j₀ ∈ S := by rw [hSdef, Finset.mem_compl, Finset.mem_singleton]; exact hj₀
    set c := σ' j₀ with hc0
    have hcS : ∀ j, j ≠ m → σ' j = c := fun j hj =>
      hc j (by rw [hSdef, Finset.mem_compl, Finset.mem_singleton]; exact hj) j₀ hj₀S
    obtain ⟨k, hk⟩ := mem_powers_omega hK4 hω1 c
    have hc3 : c ^ 3 = 1 := hpow j₀
    have hm : σ' m = c⁻¹ := by
      have hp : ∏ j, σ' j = 1 := Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hprod)
      rw [← Finset.mul_prod_erase Finset.univ σ' (Finset.mem_univ m)] at hp
      have hrest : ∏ j ∈ Finset.univ.erase m, σ' j = c ^ 4 := by
        rw [Finset.prod_congr rfl fun j hj => hcS j (Finset.ne_of_mem_erase hj),
          Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
      rw [hrest] at hp
      have hc4 : c ^ 4 = c := by rw [pow_succ, hc3, one_mul]
      rw [hc4] at hp
      exact eq_inv_of_mul_eq_one_left hp
    have hσk : σ' = smv ω m ^ k := by
      funext j
      rw [Pi.pow_apply]
      by_cases hj : j = m
      · subst hj
        rw [hsm_self, inv_pow, hk, hm]
      · rw [smv_apply_ne ω hj, hk, hcS j hj]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, zpow_natCast, hxσ, hσ', hσk, map_pow]
  · intro hmem i hi j hj
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hσm : σ' = smv ω m ^ k := by
      apply diagHom_injective 5
      rw [← hσ', map_zpow, ← hxσ, Subgroup.coe_zpow]
    rw [hσm, Pi.pow_apply, Pi.pow_apply, hSnode.1 i hi j hj]

theorem triv_out (hK4 : Nat.card K = 4) {ω : Kˣ} (hω1 : ω ≠ 1) {d : ℕ} {a b c : Fin d}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {φ : K ≃+* K} (hφ : φ ≠ 1) (j : Fin d) :
    φ (triv ω a b c j : K) ≠ (triv ω a b c a : K) := by
  rw [triv_apply_left ω hab hac]
  have hj : triv ω a b c j = 1 ∨ triv ω a b c j = ω := by
    simp only [triv, Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hja : j = a
    · subst hja
      simp [hab, hac]
    by_cases hjb : j = b
    · subst hjb
      simp [hja, hbc]
    by_cases hjc : j = c
    · subst hjc
      simp [hja, hjb]
    · simp [hja, hjb, hjc]
  rcases hj with hj | hj
  · rw [hj, Units.val_one, map_one]
    exact fun he => hω1 (Units.ext he.symm)
  · rw [hj]
    exact apply_omega_ne hK4 hω1 hφ

theorem ggEndNodeEltAdm_four_five (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    GGEndNodeEltAdm 3 (d - 2) (LargeEvenProj (unitarySU 2 1 K d)) := by
  classical
  intro Ab hAb hr h3 hadm
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have h := TableBU.unitaryFieldData_of_card hK (le_refl 1)
  set π := LargeEvenProjMk (unitarySU 2 1 K d) with hπ
  have hd3 : ¬ 3 ∣ d := by rcases hd with rfl | rfl <;> norm_num
  have hd4 : 4 ≤ d := by omega
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hnp : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h Nat.prime_three hd3 hz hzp
  obtain ⟨A, hmap, -, hA, hcardA⟩ :=
    exists_lift_of_noTorsion π (QuotientGroup.mk'_surjective _) Nat.prime_three hnp hAb
  obtain ⟨P, hP, hdiag⟩ := exists_conj_diag h Nat.prime_three hpq hA
  set c := conjSU h P hP with hc
  set A' := A.map (c : ↥(unitarySU 2 1 K d) →* ↥(unitarySU 2 1 K d)) with hA'
  have hA'ab : IsElemAbelian 3 A' := by
    have := isElemAbelian_range (H := A) (p := 3)
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
      (fun a => Subtype.ext (by simpa using hA.2 a a.2))
      ((c : ↥(unitarySU 2 1 K d) →* ↥(unitarySU 2 1 K d)).comp A.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hdiag' : ∀ x ∈ A', ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiag x hx
  have hcard' : Nat.card A' = Nat.card Ab := by
    rw [hA', ← hcardA]
    exact (Nat.card_congr (A.equivMapOfInjective _ c.injective).toEquiv).symm
  set cR := conjProj h P hP with hcR
  have hmap' : A'.map π = Ab.map (cR : LargeEvenProj (unitarySU 2 1 K d) →*
      LargeEvenProj (unitarySU 2 1 K d)) := by
    rw [← hmap, hA', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨U, hU1, hU2, hAU⟩ := hadm
  set U' := U.map (MulAut.congr cR).toMonoidHom with hU'
  have hU'1 : U' ≠ ⊥ := fun hbot =>
    hU1 ((Subgroup.map_eq_bot_iff_of_injective U (MulAut.congr cR).injective).mp hbot)
  have hU'2 : IsPGroup 2 U' := hU2.map _
  have hAU' : (A'.map π).map MulAut.conj ≤
      Subgroup.normalizer (U' : Set (MulAut (LargeEvenProj (unitarySU 2 1 K d)))) := by
    rw [hmap']
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have e : MulAut.conj (cR b) = (MulAut.congr cR).toMonoidHom (MulAut.conj b) :=
      (congr_conj cR b).symm
    change MulAut.conj (cR b) ∈ _
    rw [e]
    exact Subgroup.le_normalizer_map _ ⟨MulAut.conj b, hAU ⟨b, hb, rfl⟩, rfl⟩
  set W := diagVec A' with hW
  have hWT : W ≤ torusThree K d := diagVec_le_torusThree h hA'ab
  have hWcard : 27 ≤ Nat.card W := by
    rw [hW, card_diagVec hdiag', hcard']
    exact h3
  obtain ⟨ω, hω3, hω1⟩ := exists_omega hK4
  obtain ⟨-, hωinv, -, -, -⟩ := omega_facts hω3 hω1
  have hbot : (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 1 K d) = ⊥ :=
    suScalars_eq_bot_four hK hd3
  have hq : ¬(d = 3 ∧ 2 ^ 1 = 2) := fun h' => by omega
  have hnot : (∀ i j : Fin d, i ≠ j → ∃ σ ∈ W, σ i ≠ σ j) →
      (∃ a b c : Fin d, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ triv ω a b c ∈ W) → False := by
    intro hdist ⟨a, b, c', hab, hbc, hac, htri⟩
    refine not_exists_twoSubgroup_of_diag h hK (by omega) hq hbot (A := A') (fun i j hij => ?_)
      (fun φ hφ => ?_) hU'1 hU'2 hAU'
    · obtain ⟨σ, hσ, hne⟩ := hdist i j hij
      obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp hσ
      exact ⟨x, hx, σ, hxσ, hne⟩
    · obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp htri
      exact ⟨x, hx, triv ω a b c', hxσ, a, triv_out hK4 hω1 hab hbc hac hφ⟩
  rcases hd with rfl | rfl
  ·
    exfalso
    have hWeq : W = torusThree K 4 := by
      apply Subgroup.eq_of_le_of_card_ge hWT
      have : Nat.card (torusThree K 4) ≤ 3 ^ 3 :=
        card_torusThree_le (by rw [hK4]) 3
      omega
    refine hnot (fun i j hij => ⟨epsv ω i j, hWeq ▸ epsv_mem ω hω3 i j, ?_⟩)
      ⟨0, 1, 2, by decide, by decide, by decide, hWeq ▸ triv_mem ω hω3 0 1 2⟩
    rw [epsv_apply_left ω hij, epsv_apply_right ω hij]
    exact hωinv
  ·
    by_cases hsm : ∃ m, smv ω m ∈ W
    · obtain ⟨m, hm⟩ := hsm
      obtain ⟨x, hxA, hxσ⟩ := mem_diagVec.mp hm
      have ht := isEndNode_smv h hK hω3 hω1 hA'ab hdiag' hxA hxσ
      rw [hmap'] at ht
      have ht' := ht.map cR.symm
      rw [Subgroup.map_map] at ht'
      have hid : cR.symm.toMonoidHom.comp
          (cR : LargeEvenProj (unitarySU 2 1 K 5) →* LargeEvenProj (unitarySU 2 1 K 5)) =
            MonoidHom.id _ := by
        ext y
        simp
      rw [hid, Subgroup.map_id] at ht'
      obtain ⟨h1, h2, h3', h4⟩ := ht'
      exact ⟨_, h1, h2, h3', h4⟩
    · exfalso
      push Not at hsm
      obtain ⟨hdist, htri⟩ := five_dist_triple hK4 hω3 hω1 hWT hWcard hsm
      exact hnot hdist htri

theorem ggEndNodeAdm_four_five
    (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    GGEndNodeAdm 3 (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
        (LargeEvenGUSet (Fin d) K (2 ^ 1))) := by
  have h := TableBU.unitaryFieldData_of_card hK (le_refl 1)
  have hd3 : ¬ 3 ∣ d := by rcases hd with rfl | rfl <;> norm_num
  have hd' : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  refine ggEndNodeAdm_of_pow_eq_one (I' := Set.range MulAut.conj) ?_
    fun φ hφ hφp => mem_range_conj_of_pow_eq_one h hK hd' hdq Nat.prime_three (by norm_num) hd3
      hφ hφp
  exact ggEndNodeAdm_of_eltAdm subset_rfl (center_proj_eq_bot hK hd' hdq)
    (fun L' _ _ ψ hψ hker hperf => not_three_dvd_card_ker hK hd L' ψ hψ hker hperf)
    (ggEndNodeEltAdm_four_five hK hd)

end Small

end TableBUR

open TableBUR CFSG.Assembly in
theorem ggEndNodeAdmUnitarySmallInput_holds :
    GGEndNodeAdmUnitarySmallInput := by
  intro p lab hp hlab hl hn hrank
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpq⟩ := hl
  dsimp only at htag hpq hn hrank ⊢
  subst hn
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq)
  subst hp3
  have hr : ggUnitaryTorusRank 3 (l + 1) = l + 1 - 2 := by
    have : ¬ 3 ∣ l + 1 := by rcases hrank with rfl | rfl <;> norm_num
    simp only [ggUnitaryTorusRank, this, ↓reduceIte]
  rw [hr]
  rcases htag with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
    exact ⟨K, i1, i2, hK, hq', ggEndNodeAdm_four_five hK (by omega)⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
    exact ⟨K, i1, i2, hK, hq', ggEndNodeAdm_four_five hK (Or.inl rfl)⟩

end CFSG.StandardType
