module

public import CFSG.Quasithin.Background.DicksonPerfectPSL2
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.LieType.CentralExt.SL2Lift

public section

namespace CFSG.Quasithin.Dickson

open CFSG.Quasithin.A1c CFSG.LieType.CentralExt
open scoped MatrixGroups commutatorElement

theorem nonempty_mulEquiv_alt_five_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 60) : Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hG, show (60 : ℕ) = 5 * 12 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnot_normal : ¬ (P : Subgroup G).Normal := fun hN => by
    rcases hN.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP
      omega
    · rw [h, Subgroup.card_top, hG] at hP
      omega
  have hcard : Nat.card (Sylow 5 G) = 6 := by
    have hmod := card_sylow_modEq_one 5 G
    have hdvd : Nat.card (Sylow 5 G) ∣ 12 := by
      have h := P.card_dvd_index
      rwa [(P : Subgroup G).index_eq_card, show Nat.card (G ⧸ (P : Subgroup G)) = 12 by
        have := (P : Subgroup G).card_mul_index
        rw [hP, hG, (P : Subgroup G).index_eq_card] at this
        omega] at h
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card (Sylow 5 G) ≠ 1 := fun h1 => by
      have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnot_normal (Sylow.normal_of_subsingleton P)
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 G) <;> simp_all
  have hfaithful : FaithfulSMul G (Sylow 5 G) := by
    let φ := MulAction.toPermHom G (Sylow 5 G)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · refine ⟨fun {g h} hgh => ?_⟩
      have : φ g = φ h := Equiv.ext hgh
      exact (MonoidHom.ker_eq_bot_iff φ).mp hk this
    · refine absurd ?_ hnot_normal
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp
        (congrArg (fun σ : Equiv.Perm (Sylow 5 G) => σ P) hg)
  exact CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    (Ω := Sylow 5 G) inferInstance hcard hG

theorem card_psl2_five :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = 60 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hF : Nat.card (ZMod 5) = 5 ^ 1 := by rw [Nat.card_zmod, pow_one]
  rw [CFSG.GorensteinWalter.psl2_card_formula (ZMod 5) ⟨5, 1, by norm_num, by decide, le_rfl, hF⟩,
    Nat.card_zmod]
  norm_num

theorem nonempty_psl2_five_equiv_alt :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) ≃*
      alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  exact nonempty_mulEquiv_alt_five_of_simple card_psl2_five

section Quotient

variable {p : ℕ} [hp : Fact p.Prime]

@[expose] def pslMap (p : ℕ) [Fact p.Prime] :
    SL(2, ZMod p) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
  QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p)))

theorem ker_pslMap : (pslMap p).ker = Subgroup.center (SL(2, ZMod p)) :=
  QuotientGroup.ker_mk' _

theorem pslMap_surjective : Function.Surjective (pslMap p) := QuotientGroup.mk'_surjective _

theorem mem_ker_pslMap {g : SL(2, ZMod p)} : g ∈ (pslMap p).ker ↔ g = 1 ∨ g = sl2NegOne p := by
  rw [ker_pslMap]
  constructor
  · exact eq_one_or_eq_sl2NegOne_of_mem_center
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact sl2NegOne_mem_center

theorem sl2_eq_one_or_negOne_of_mul_self (hp2 : p ≠ 2) {g : SL(2, ZMod p)} (hg : g * g = 1) :
    g = 1 ∨ g = sl2NegOne p := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
      ((ZMod.natCast_eq_zero_iff 2 p).1 h'))
  have hM : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) * g = 1 := by
    simpa using congrArg Subtype.val hg
  rcases matrix_eq_one_or_neg_one_of_sq_eq_one h2 hM g.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · right
    apply Subtype.ext
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2NegOne]

theorem map_pslMap_perfect {K : Subgroup (SL(2, ZMod p))} (hK : ⁅K, K⁆ = K) :
    ⁅K.map (pslMap p), K.map (pslMap p)⁆ = K.map (pslMap p) := by
  rw [← Subgroup.map_commutator, hK]

theorem map_pslMap_ne_bot {K : Subgroup (SL(2, ZMod p))} (hK : ⁅K, K⁆ = K) (hne : K ≠ ⊥) :
    K.map (pslMap p) ≠ ⊥ := by
  intro h
  apply hne
  have hle : K ≤ (pslMap p).ker := by
    intro x hx
    have : pslMap p x ∈ K.map (pslMap p) := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hperf : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hK
  have hc : ∀ a ∈ K, a ∈ Subgroup.center (SL(2, ZMod p)) := fun a ha =>
    ker_pslMap (p := p) ▸ hle ha
  have : IsMulCommutative K := ⟨⟨fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hc a a.2) b).symm⟩⟩
  have : Subsingleton K := inferInstance
  exact Subgroup.eq_bot_of_subsingleton K

theorem eq_top_of_map_pslMap_eq_top (hp5 : 5 ≤ p) {K : Subgroup (SL(2, ZMod p))}
    (h : K.map (pslMap p) = ⊤) : K = ⊤ := by
  have hperf := sl2_isPerfect hp5
  have hdec : ∀ x : SL(2, ZMod p), ∃ k ∈ K, ∃ z ∈ Subgroup.center (SL(2, ZMod p)), x = k * z := by
    intro x
    have hx : pslMap p x ∈ K.map (pslMap p) := by rw [h]; trivial
    obtain ⟨k, hk, hkx⟩ := hx
    refine ⟨k, hk, k⁻¹ * x, ?_, by group⟩
    rw [← ker_pslMap, MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
  have hcomm : commutator (SL(2, ZMod p)) ≤ K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := hdec x
    obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := hdec y
    rw [commutatorElement_mul_center hz₁ hz₂, commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  rw [eq_top_iff]
  rwa [hperf.commutator_eq_top] at hcomm

theorem negOne_mem_of_equiv_alt_five (hp2 : p ≠ 2) {K : Subgroup (SL(2, ZMod p))}
    (e : K.map (pslMap p) ≃* alternatingGroup (Fin 5)) : sl2NegOne p ∈ K := by
  obtain ⟨a, ha1, ha2⟩ : ∃ a : alternatingGroup (Fin 5), a ≠ 1 ∧ a * a = 1 := by decide +kernel
  obtain ⟨x, hxK, hx⟩ := (e.symm a).2
  have hxne : pslMap p x ≠ 1 := by
    intro h1
    apply ha1
    apply e.symm.injective
    apply Subtype.ext
    rw [← hx]
    simpa using h1
  have hsq : pslMap p (x * x) = 1 := by
    rw [map_mul, hx]
    have : e.symm a * e.symm a = 1 := by rw [← map_mul, ha2, map_one]
    simpa using congrArg Subtype.val this
  rcases mem_ker_pslMap.1 (MonoidHom.mem_ker.2 hsq) with h1 | h2
  · rcases sl2_eq_one_or_negOne_of_mul_self hp2 h1 with rfl | rfl
    · exact (hxne (map_one _)).elim
    · exact (hxne (mem_ker_pslMap.2 (Or.inr rfl))).elim
  · rw [← h2]
    exact K.mul_mem hxK hxK

end Quotient

section Main

variable {p : ℕ} [hp : Fact p.Prime]

@[expose] noncomputable def pslMapOn (K : Subgroup (SL(2, ZMod p))) : K →* K.map (pslMap p) :=
  (pslMap p).subgroupMap K

theorem pslMapOn_surjective (K : Subgroup (SL(2, ZMod p))) :
    Function.Surjective (pslMapOn K) := (pslMap p).subgroupMap_surjective K

theorem mem_ker_pslMapOn {K : Subgroup (SL(2, ZMod p))} (x : K) :
    x ∈ (pslMapOn K).ker ↔ (x : SL(2, ZMod p)) = 1 ∨ (x : SL(2, ZMod p)) = sl2NegOne p := by
  rw [← mem_ker_pslMap, MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    simpa [pslMapOn] using congrArg Subtype.val h
  · intro h
    exact Subtype.ext (by simpa [pslMapOn] using h)

theorem ker_pslMapOn_le_center (K : Subgroup (SL(2, ZMod p))) :
    (pslMapOn K).ker ≤ Subgroup.center K := by
  intro x hx
  have hxc : (x : SL(2, ZMod p)) ∈ Subgroup.center (SL(2, ZMod p)) := by
    rw [← ker_pslMap, mem_ker_pslMap]
    exact (mem_ker_pslMapOn x).1 hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 hxc y)

theorem isPGroup_two_ker_pslMapOn (K : Subgroup (SL(2, ZMod p))) :
    IsPGroup 2 (pslMapOn K).ker := by
  intro x
  refine ⟨1, ?_⟩
  have hx := (mem_ker_pslMapOn x.1).1 x.2
  apply Subtype.ext
  apply Subtype.ext
  rcases hx with h | h
  · simp [h]
  · simp [pow_two, h, sl2NegOne_mul_self]

theorem card_ker_pslMapOn (hp2 : p ≠ 2) {K : Subgroup (SL(2, ZMod p))} (hneg : sl2NegOne p ∈ K) :
    Nat.card (pslMapOn K).ker = 2 := by
  refine (Nat.card_eq_two_iff' (1 : (pslMapOn K).ker)).2
    ⟨⟨⟨sl2NegOne p, hneg⟩, ?_⟩, ?_, ?_⟩
  · exact (mem_ker_pslMapOn _).2 (Or.inr rfl)
  · intro h
    have := congrArg (fun y : (pslMapOn K).ker => ((y : K) : SL(2, ZMod p))) h
    exact sl2NegOne_ne_one hp2 this
  · intro y hy
    rcases (mem_ker_pslMapOn y.1).1 y.2 with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hy
    · exact Subtype.ext (Subtype.ext h)

theorem card_sl2_five : Nat.card (SL(2, ZMod 5)) = 120 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem nonempty_equiv_sl2_five_of_equiv_alt_five (hp2 : p ≠ 2) {K : Subgroup (SL(2, ZMod p))}
    (hK : ⁅K, K⁆ = K) (e : K.map (pslMap p) ≃* alternatingGroup (Fin 5)) :
    Nonempty (K ≃* SL(2, ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨eP⟩ := nonempty_psl2_five_equiv_alt
  have hneg : sl2NegOne p ∈ K := negOne_mem_of_equiv_alt_five hp2 e
  have hcen := ker_pslMapOn_le_center K
  have h2 := isPGroup_two_ker_pslMapOn K
  let ε : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) ≃* K.map (pslMap p) :=
    eP.trans e.symm
  let α : SL(2, ZMod 5) →* K.map (pslMap p) := ε.toMonoidHom.comp (pslMap 5)
  have hα : Function.Surjective α := ε.surjective.comp pslMap_surjective
  have hk : ringChar (ZMod 5) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  obtain ⟨β, hβ⟩ := exists_lift hk (pslMapOn_surjective K) hcen h2 α
  have hdec : ∀ x : K, ∃ s : SL(2, ZMod 5), ∃ z ∈ (pslMapOn K).ker, x = β s * z := by
    intro x
    obtain ⟨s, hs⟩ := hα (pslMapOn K x)
    refine ⟨s, (β s)⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : pslMapOn K (β s) = α s := DFunLike.congr_fun hβ s
    rw [this, hs, inv_mul_cancel]
  have hβsurj : Function.Surjective β := by
    have hcomm : commutator K ≤ β.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s₁, z₁, hz₁, rfl⟩ := hdec x
      obtain ⟨s₂, z₂, hz₂, rfl⟩ := hdec y
      rw [commutatorElement_mul_center (hcen hz₁) (hcen hz₂), commutatorElement_def]
      exact β.range.mul_mem (β.range.mul_mem (β.range.mul_mem ⟨s₁, rfl⟩ ⟨s₂, rfl⟩)
        (β.range.inv_mem ⟨s₁, rfl⟩)) (β.range.inv_mem ⟨s₂, rfl⟩)
    have hperfK : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hK
    rw [hperfK.commutator_eq_top] at hcomm
    intro x
    exact hcomm (Subgroup.mem_top x)
  have hcardKbar : Nat.card (K.map (pslMap p)) = 60 := by
    rw [Nat.card_congr e.toEquiv, card_alt_five]
  have hcardK : Nat.card K = 120 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pslMapOn K).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (pslMapOn_surjective K)).toEquiv,
      hcardKbar, card_ker_pslMapOn hp2 hneg]
  have hbij : Function.Bijective β :=
    hβsurj.bijective_of_nat_card_le (by rw [card_sl2_five, hcardK])
  exact ⟨(MulEquiv.ofBijective β hbij).symm⟩

theorem eq_or_eq_top_of_equiv_alt_five
    (hp2 : p ≠ 2) {K : Subgroup (SL(2, ZMod p))}
    (e : K.map (pslMap p) ≃* alternatingGroup (Fin 5)) {K' : Subgroup (SL(2, ZMod p))}
    (hKK' : K ≤ K') : K' = K ∨ K' = ⊤ := by
  have hneg : sl2NegOne p ∈ K := negOne_mem_of_equiv_alt_five hp2 e
  have hker_le : ∀ H : Subgroup (SL(2, ZMod p)), sl2NegOne p ∈ H → (pslMap p).ker ≤ H := by
    intro H hH g hg
    rcases mem_ker_pslMap.1 hg with rfl | rfl
    · exact H.one_mem
    · exact hH
  have hcomap : ∀ H : Subgroup (SL(2, ZMod p)), sl2NegOne p ∈ H →
      (H.map (pslMap p)).comap (pslMap p) = H := fun H hH =>
    Subgroup.comap_map_eq_self (hker_le H hH)
  rcases overgroup_alternating_five_psl2_prime hp2 (Subgroup.map_mono hKK') ⟨e⟩ with h | h
  · right
    rw [← hcomap K' (hKK' hneg), h]
    exact Subgroup.comap_top _
  · left
    have hcardK : Nat.card (K.map (pslMap p)) = 60 := by
      rw [Nat.card_congr e.toEquiv, card_alt_five]
    have heq : K.map (pslMap p) = K'.map (pslMap p) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hKK') (by rw [h, hcardK])
    rw [← hcomap K' (hKK' hneg), ← heq, hcomap K hneg]

theorem perfect_subgroup_sl2_prime
    (hp5 : 5 ≤ p) {K : Subgroup (SL(2, ZMod p))} (hK : ⁅K, K⁆ = K)
    (hne : K ≠ ⊥) :
    K = ⊤ ∨ (Nonempty (K ≃* SL(2, ZMod 5)) ∧ p ^ 2 % 5 = 1 ∧ p ≠ 5 ∧ sl2NegOne p ∈ K ∧
      ∀ K' : Subgroup (SL(2, ZMod p)), K ≤ K' → K' = K ∨ K' = ⊤) := by
  have hp2 : p ≠ 2 := by omega
  rcases perfect_subgroup_psl2_prime hp2 (K.map (pslMap p)) (map_pslMap_perfect hK)
    (map_pslMap_ne_bot hK hne) with h | ⟨⟨e⟩, h5⟩
  · exact Or.inl (eq_top_of_map_pslMap_eq_top hp5 h)
  · by_cases htop : K = ⊤
    · exact Or.inl htop
    · right
      have hp5' : p ≠ 5 := by
        rintro rfl
        apply htop
        apply eq_top_of_map_pslMap_eq_top hp5
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_congr e.toEquiv, card_alt_five, card_psl2_five]
      refine ⟨nonempty_equiv_sl2_five_of_equiv_alt_five hp2 hK e, ?_, hp5',
        negOne_mem_of_equiv_alt_five hp2 e, fun K' h => eq_or_eq_top_of_equiv_alt_five hp2 e h⟩
      rcases h5 with h5 | h5
      · exact absurd h5 hp5'
      · have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
        omega

end Main

end CFSG.Quasithin.Dickson
