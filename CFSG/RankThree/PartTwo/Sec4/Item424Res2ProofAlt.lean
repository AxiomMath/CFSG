module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA6
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA7
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA8
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA9
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensusAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item424Res2

open Equiv Equiv.Perm Item434AltPerm

theorem normalizerMonoidHom_pow_four {Y : Type*} [Group Y] {F : Subgroup Y} {r : Y}
    (hr : r ∈ Subgroup.normalizer (F : Set Y)) (h4 : r ^ 4 = 1) {x : Y} (hx : x ∈ F)
    (h2 : r ^ 2 * x * (r ^ 2)⁻¹ ≠ x) :
    F.normalizerMonoidHom ⟨r, hr⟩ ∈ autIn (⊤ : Subgroup Y) F ∧
      F.normalizerMonoidHom ⟨r, hr⟩ ^ 4 = 1 ∧ F.normalizerMonoidHom ⟨r, hr⟩ ^ 2 ≠ 1 := by
  refine ⟨mem_autIn_iff.mpr ⟨r, hr, Subgroup.mem_top r, rfl⟩, ?_, ?_⟩
  · rw [← map_pow]
    have : (⟨r, hr⟩ : Subgroup.normalizer (F : Set Y)) ^ 4 = 1 := Subtype.ext h4
    rw [this, map_one]
  · intro h
    apply h2
    have h1 := congrArg (fun σ : MulAut F => ((σ ⟨x, hx⟩ : F) : Y)) h
    simp only [MulAut.one_apply] at h1
    rw [← map_pow, Sec4.normalizerMonoidHom_apply_coe] at h1
    exact h1

@[expose] def rSix : Perm (Fin 6) := swap 0 3 * swap 1 4 * swap 2 5 * swap 4 5

@[expose] def rEight : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 2 5 * swap 4 5

theorem rSix_facts : sign rSix = 1 ∧ rSix ^ 4 = 1 ∧
    (∀ v : Fin 2 → ZMod 3, ∃ w : Fin 2 → ZMod 3, rSix * vecPerm2 6 v * rSix⁻¹ = vecPerm2 6 w) ∧
    rSix ^ 2 * c1 6 * (rSix ^ 2)⁻¹ ≠ c1 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem rEight_facts : sign rEight = 1 ∧ rEight ^ 4 = 1 ∧
    (∀ v : Fin 2 → ZMod 3, ∃ w : Fin 2 → ZMod 3,
      rEight * vecPerm2 8 v * rEight⁻¹ = vecPerm2 8 w) ∧
    rEight ^ 2 * c1 8 * (rEight ^ 2)⁻¹ ≠ c1 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem exists_pow_four_F06 :
    ∃ σ ∈ autIn (⊤ : Subgroup (alternatingGroup (Fin 6))) F06, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨hrA, hr4, hrN, hr2⟩ := rSix_facts
  have hr : (⟨rSix, mem_alternatingGroup.mpr hrA⟩ : alternatingGroup (Fin 6)) ∈
      Subgroup.normalizer (F06 : Set (alternatingGroup (Fin 6))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨v, hv⟩ := mem_F06.mp hx
    obtain ⟨w, hw⟩ := hrN v
    refine mem_F06.mpr ⟨w, ?_⟩
    rw [← hw, hv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hc1F : c1 6 ∈ F0 6 := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hc1 : (⟨c1 6, F0_six_le_alternatingGroup hc1F⟩ : alternatingGroup (Fin 6)) ∈ F06 :=
    Subgroup.mem_comap.mpr hc1F
  obtain ⟨hm, h4, h2⟩ := normalizerMonoidHom_pow_four hr (Subtype.ext hr4) hc1
    (fun h => hr2 (by simpa using congrArg Subtype.val h))
  exact ⟨_, hm, h4, h2⟩

theorem exists_pow_four_F08 :
    ∃ σ ∈ autIn (⊤ : Subgroup (alternatingGroup (Fin 8))) Res423Two.F08,
      σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨hrA, hr4, hrN, hr2⟩ := rEight_facts
  have hmem : ∀ x : alternatingGroup (Fin 8), x ∈ Res423Two.F08 ↔
      ∃ w, vecPerm2 8 w = (x : Perm (Fin 8)) := fun x => by
    rw [Res423Two.F08, Subgroup.mem_subgroupOf, F0_eq_range f0Facts_eight]
    exact ⟨fun ⟨v, hv⟩ => ⟨_, hv⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩
  have hr : (⟨rEight, mem_alternatingGroup.mpr hrA⟩ : alternatingGroup (Fin 8)) ∈
      Subgroup.normalizer (Res423Two.F08 : Set (alternatingGroup (Fin 8))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨v, hv⟩ := (hmem x).mp hx
    obtain ⟨w, hw⟩ := hrN v
    refine (hmem _).mpr ⟨w, ?_⟩
    rw [← hw, hv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hc1F : c1 8 ∈ F0 8 := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hc1 : (⟨c1 8, Res423Two.F0_eight_le hc1F⟩ : alternatingGroup (Fin 8)) ∈
      Res423Two.F08 :=
    Subgroup.mem_subgroupOf.mpr hc1F
  obtain ⟨hm, h4, h2⟩ := normalizerMonoidHom_pow_four hr (Subtype.ext hr4) hc1
    (fun h => hr2 (by simpa using congrArg Subtype.val h))
  exact ⟨_, hm, h4, h2⟩

theorem exists_pow_four_alt6 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6))
    {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨ρ, hρ, h4, h2⟩ := exists_pow_four_F06
  exact exists_pow_four_of_conj e Res423Two.factorization_card_alt6 card_F06 hρ h4 h2 hD9

theorem exists_pow_four_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7))
    {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 :=
  exists_pow_four_of_conj e Res423Two.factorization_card_alt7 Res423Two.card_eNine7
    Res423Two.rho7_mem Res423Two.rho7_pow_four Res423Two.rho7_sq_ne_one hD9

theorem exists_pow_four_alt8 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 8))
    {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨ρ, hρ, h4, h2⟩ := exists_pow_four_F08
  exact exists_pow_four_of_conj e Res423Two.factorization_card_alt8 Res423Two.card_F08 hρ h4 h2
    hD9

theorem isSolvable_centralizer_alt9 {X : Type} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 9)) {D : Subgroup X}
    (hD : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D)
    (hD9 : Nat.card D = 9) {c : X} (hcD : c ∈ D) (hc1 : c ≠ 1) :
    Group.IsSolvable (Subgroup.centralizer ({c} : Set X)) := by
  set D₁ := D.map e.toMonoidHom with hD₁
  have hD₁e : CFSG.Assembly.IsElemAbelian 3 D₁ := Res423Two.isElemAbelian_map' _ hD.prop
  have hD₁9 : Nat.card D₁ = 9 := by rw [hD₁, Subgroup.card_map_of_injective e.injective, hD9]
  have hmax : ∀ E : Subgroup (alternatingGroup (Fin 9)), CFSG.Assembly.IsElemAbelian 3 E →
      D₁ ≤ E → E ≤ D₁ := by
    intro E hE hDE
    have hEe : CFSG.Assembly.IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      Res423Two.isElemAbelian_map' _ hE
    have hDE' : D ≤ E.map e.symm.toMonoidHom := by
      intro x hx
      exact ⟨e x, hDE ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    have h1 := hD.2 hEe hDE'
    intro y hy
    exact ⟨e.symm y, h1 ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩
  obtain ⟨g, hgW, hgA⟩ := Res423Two.exists_conj_le_W hD₁9 hmax
  set D₂ := (D₁.map (alternatingGroup (Fin 9)).subtype).map (MulAut.conj g⁻¹).toMonoidHom
    with hD₂
  have hD₂e : CFSG.Assembly.IsElemAbelian 3 D₂ :=
    Res423Two.isElemAbelian_map' _ (Res423Two.isElemAbelian_map' _ hD₁e)
  have hDc : ∀ a ∈ D₂, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD₂e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set c₂ : Perm (Fin 9) := MulAut.conj g⁻¹ ((e c : alternatingGroup (Fin 9)) : Perm (Fin 9))
    with hc₂
  have hc₂D : c₂ ∈ D₂ := ⟨_, ⟨e c, ⟨c, hcD, rfl⟩, rfl⟩, rfl⟩
  have hc₂1 : c₂ ≠ 1 := by
    intro h
    apply hc1
    have h1 : ((e c : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 1 :=
      (MulAut.conj g⁻¹).injective (h.trans (map_one _).symm)
    have h2 : e c = 1 := Subtype.ext h1
    exact e.injective (h2.trans (map_one e).symm)
  have hc₂3 : c₂ ^ 3 = 1 := hD₂e.2 c₂ hc₂D
  have hfpf : ∀ p, c₂ p ≠ p := Res423Two.fpf_of_le_W_of_not_le_A0 hgW hgA hDc hc₂D hc₂1
  have hcard := Res423Two.card_centralizer_fpf_nine hc₂3 hc₂1 hfpf
  have hsol : Group.IsSolvable (Subgroup.centralizer ({c₂} : Set (Perm (Fin 9)))) :=
    isSolvable_of_card_eq_two_mul_pow_three (k := 4) (by rw [hcard]; norm_num)
  let φ₀ : X →* Perm (Fin 9) :=
    ((MulAut.conj g⁻¹).toMonoidHom.comp (alternatingGroup (Fin 9)).subtype).comp e.toMonoidHom
  have hφ₀ : Function.Injective φ₀ := (MulAut.conj g⁻¹).injective.comp
    ((alternatingGroup (Fin 9)).subtype_injective.comp e.injective)
  have hmemC : ∀ x : Subgroup.centralizer ({c} : Set X),
      φ₀ x ∈ Subgroup.centralizer ({c₂} : Set (Perm (Fin 9))) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (x : X) * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
    have : φ₀ x * φ₀ c = φ₀ c * φ₀ x := by rw [← map_mul, ← map_mul, hx]
    exact this
  let φ : Subgroup.centralizer ({c} : Set X) →* Subgroup.centralizer ({c₂} : Set (Perm (Fin 9))) :=
    (φ₀.comp (Subgroup.centralizer ({c} : Set X)).subtype).codRestrict _ hmemC
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (hφ₀ (congrArg Subtype.val hab))
  exact Group.isSolvable_of_isSolvable_injective hφ

theorem census424_of_alt {X : Type} [Group X] [Finite X] {n : ℕ} (hn : n ≤ 9)
    (e : X ≃* alternatingGroup (Fin n)) : Census424 X := by
  by_cases h5 : n ≤ 5
  · exact census424_of_not_nine_dvd (Res423Alt.not_nine_dvd_card_alternating h5 e)
  intro D c d K h
  have hc1 : c ≠ 1 := h.c_ne_one
  exfalso
  interval_cases n
  · exact false_of_pow_four h (exists_pow_four_alt6 e h.card_eq)
  · exact false_of_pow_four h (exists_pow_four_alt7 e h.card_eq)
  · exact false_of_pow_four h (exists_pow_four_alt8 e h.card_eq)
  · exact not_isSolvable_centralizer h
      (isSolvable_centralizer_alt9 e h.maximal h.card_eq h.c_mem hc1)

end Item424Res2

open Item424Res2

theorem k424Inner46Four : K424Inner46Four := by
  rintro X _ _ hX hq hZ -
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | hX | hX
  · exact census424_of_alt hn e
  · exact (Res423Alt.false_of_isExtOf_three hq hZ hX).elim
  · exact (Res423Alt.false_of_isExtOf_three hq hZ hX).elim

end CFSG.RankThree.PartTwo.Sec4
