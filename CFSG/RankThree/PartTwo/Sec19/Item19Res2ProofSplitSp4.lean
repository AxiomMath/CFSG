module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofFlag
public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
public import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher SymplecticTorusWeyl

section Sp4

variable {K : Type} [Field K]

theorem center_sl2_eq_bot [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * hK2
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hsq)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

theorem card_le_three_of_elemAbelian_sl2 [Finite K] [CharP K 2]
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  obtain ⟨⟨f, hf0⟩, -, hf⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card, PNat.mk_coe] at hf
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  by_cases h7 : 7 ≤ Nat.card K
  · let π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    have hπ : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_sl2_eq_bot]
    set E' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := E.map π with hE'
    have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective hπ
    have hE'p : ∀ c ∈ E', c ^ 3 = 1 := by
      rintro _ ⟨c, hc, rfl⟩
      rw [← map_pow, hE.2 c hc, map_one]
    have hpg : IsPGroup 3 ↥E' := fun g => ⟨1, Subtype.ext (by simpa using hE'p g g.2)⟩
    obtain ⟨R, hR⟩ := hpg.exists_le_sylow
    have hcop : Nat.Coprime 3 (Nat.card K) := by
      rw [hf]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hcyc : IsCyclic R :=
      CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K (p := 2) (f := f) hf h7
        3 (by norm_num) hcop R
    have hEcyc : IsCyclic ↥E' := by
      have : IsCyclic ↥(E'.subgroupOf
          (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) :=
        Subgroup.isCyclic _
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hR).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hR).surjective
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E')
    have h1 : orderOf g ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa using hE'p g g.2
    rw [hg, hcard] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  · have hf3 : f < 3 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 ∨
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hf]
      interval_cases f <;> norm_num
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
    have hdvd : Nat.card E ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Subgroup.card_subgroup_dvd_card E
    rw [hk] at hdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra h
      have h9 : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
      have h9' := h9.trans hdvd
      rcases hSL with h6 | h60
      · rw [h6] at h9'
        norm_num at h9'
      · rw [h60] at h9'
        norm_num at h9'
    interval_cases k <;> norm_num

theorem lam_eq_one_iff' (i : Fin 2) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    lam i g = 1 ↔ g = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
  have h1 : (((lam i g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [h]; rfl
  rw [coe_lam] at h1
  obtain ⟨h00, h01, h10, h11⟩ := pairMat_apply_pair
    (Sum.inl_ne_inr : (Sum.inl i : Fin 2 ⊕ Fin 2) ≠ Sum.inr i) (g : Matrix (Fin 2) (Fin 2) K)
  rw [h1] at h00 h01 h10 h11
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp_all

variable (K) in
noncomputable def slPair :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K :=
  (lam (0 : Fin 2)).noncommCoprod (lam (1 : Fin 2)) fun g g' =>
    commute_lam_lam (by decide) g g'

theorem slPair_apply (g g' : Matrix.SpecialLinearGroup (Fin 2) K) :
    slPair K (g, g') = lam (0 : Fin 2) g * lam (1 : Fin 2) g' := by
  simp [slPair, MonoidHom.noncommCoprod_apply]

theorem slPair_injective : Function.Injective (slPair K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨g, g'⟩ hker
  have h : lam (0 : Fin 2) g * lam (1 : Fin 2) g' = 1 := by
    rw [← slPair_apply]; exact hker
  have hM : (((lam (0 : Fin 2) g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((lam (1 : Fin 2) g' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    have := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
    simpa using this
  have hdisj : Disjoint ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} : Set (Fin 2 ⊕ Fin 2))
      {Sum.inl (1 : Fin 2), Sum.inr (1 : Fin 2)} := by
    rw [Set.disjoint_left]
    rintro x (rfl | rfl) <;> simp
  have hg : g = 1 := by
    rw [← lam_eq_one_iff' (0 : Fin 2)]
    apply Subtype.ext
    apply Units.ext
    ext x y
    by_cases hx : x ∈ ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} : Set (Fin 2 ⊕ Fin 2))
    · have := (isSupp_lam (0 : Fin 2) g).mul_apply_of_mem (isSupp_lam (1 : Fin 2) g') hdisj hx y
      rw [hM] at this
      exact this.symm
    · exact (isSupp_lam (0 : Fin 2) g) x y (Or.inl hx)
  subst hg
  rw [map_one, one_mul] at h
  have hg' : g' = 1 := (lam_eq_one_iff' (1 : Fin 2) g').1 h
  subst hg'
  rfl

theorem not_three_dvd_index_slPair [Finite K] [CharP K 2] : ¬ 3 ∣ (slPair K).range.index := by
  have := Fintype.ofFinite K
  obtain ⟨⟨f, hf0⟩, -, hf⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card, PNat.mk_coe] at hf
  set q := Nat.card K with hqdef
  have hq2 : 2 ≤ q := by
    rw [hf]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf0
  have hrange : Nat.card (slPair K).range = (q * (q ^ 2 - 1)) ^ 2 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective slPair_injective,
      Subgroup.card_top, Nat.card_prod, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    ring
  have hSp := card_statedSp (K := K) 2
  have hprod : ∏ j ∈ Finset.Icc 1 2, (q ^ (2 * j) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  rw [hprod] at hSp
  have hidx := (slPair K).range.card_mul_index
  rw [hrange, hSp] at hidx
  set m := q ^ 2 - 1 with hm
  have hq4 : q ^ 2 = m + 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hm0 : 0 < m := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hq41 : q ^ 4 - 1 = m * (m + 2) := by
    have h4 : q ^ 4 = (m + 1) ^ 2 := by rw [← hq4]; ring
    rw [h4]
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  have hidx' : (slPair K).range.index = q ^ 2 * (m + 2) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < (q * m) ^ 2 by positivity)
    rw [hidx, hq41]
    ring
  rw [hidx']
  have hq3 : q ^ 2 % 3 = 1 := by
    rw [hf, ← pow_mul, mul_comm, pow_mul]
    norm_num [Nat.pow_mod]
  intro h3
  have hmod : q ^ 2 * (m + 2) % 3 = 2 := by
    rw [Nat.mul_mod, hq3, show (m + 2) % 3 = 2 by omega]
  omega

theorem exists_sylow_le_range_slPair [Finite K] [CharP K 2] :
    ∃ S : Sylow 3 (StatedSp 2 K), (S : Subgroup (StatedSp 2 K)) ≤ (slPair K).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := (slPair K).range with hH
  obtain ⟨S0⟩ : Nonempty (Sylow 3 H) := inferInstance
  set S1 : Subgroup (StatedSp 2 K) := (S0 : Subgroup H).map H.subtype with hS1def
  have hS1 : IsPGroup 3 S1 := S0.isPGroup'.map H.subtype
  have hidx : ¬ 3 ∣ S1.index := by
    rw [hS1def, Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact S0.not_dvd_index h
    · exact not_three_dvd_index_slPair h
  refine ⟨hS1.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem exists_conj_map_le_sylow' {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ c : G, E.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : x ∈ ((g • P : Sylow p G) : Subgroup G) := by rw [hg]; exact hEQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hsx
  have : (MulAut.conj g⁻¹).toMonoidHom x = s := by
    rw [← hsx]; simp; group
  rw [this]; exact hs

theorem card_le_nine_of_elemAbelian_sp4 [Finite K] [CharP K 2] {E : Subgroup (StatedSp 2 K)}
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := exists_sylow_le_range_slPair (K := K)
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow' S hEp
  set φ := slPair K with hφ
  set E₂ := E.map (MulAut.conj c).toMonoidHom with hE₂
  have hE₂card : Nat.card E₂ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hE₂H : E₂ ≤ φ.range := hc.trans hS
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE₂comm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hEcomm a ha b hb]
  have hE₂exp : ∀ x ∈ E₂, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 a ha, map_one]
  set Ê := E₂.comap φ with hÊ
  have hÊmap : Ê.map φ = E₂ := Subgroup.map_comap_eq_self hE₂H
  have hÊcard : Nat.card Ê = Nat.card E := by
    rw [← hE₂card, ← hÊmap, Subgroup.card_map_of_injective slPair_injective]
  have hÊcomm : ∀ a ∈ Ê, ∀ b ∈ Ê, a * b = b * a := by
    intro a ha b hb
    apply slPair_injective
    rw [map_mul, map_mul]
    exact hE₂comm _ ha _ hb
  have hÊexp : ∀ a ∈ Ê, a ^ 3 = 1 := by
    intro a ha
    apply slPair_injective
    rw [map_pow, map_one]
    exact hE₂exp _ ha
  have h1 : Nat.card (Ê.map (MonoidHom.fst _ _)) ≤ 3 := by
    refine card_le_three_of_elemAbelian_sl2 ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb]
      simp only [MonoidHom.coe_fst]
      rw [← Prod.fst_mul, ← Prod.fst_mul, hÊcomm x hx y hy]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hÊexp a ha, map_one]
  have h2 : Nat.card (Ê.map (MonoidHom.snd _ _)) ≤ 3 := by
    refine card_le_three_of_elemAbelian_sl2 ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb]
      simp only [MonoidHom.coe_snd]
      rw [← Prod.snd_mul, ← Prod.snd_mul, hÊcomm x hx y hy]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hÊexp a ha, map_one]
  have hle : Ê ≤ (Ê.map (MonoidHom.fst _ _)).prod (Ê.map (MonoidHom.snd _ _)) := by
    intro a ha
    exact ⟨⟨a, ha, rfl⟩, ⟨a, ha, rfl⟩⟩
  have h3 : Nat.card Ê ≤
      Nat.card ((Ê.map (MonoidHom.fst _ _)).prod (Ê.map (MonoidHom.snd _ _))) :=
    Subgroup.card_le_of_le hle
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod] at h3
  rw [← hÊcard]
  nlinarith

theorem conj_comp_proj_injective [CharP K 2] :
    Function.Injective ((MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))).comp (proj 2 K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcen : g ∈ Subgroup.center (StatedSp 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 : proj 2 K g * proj 2 K h * (proj 2 K g)⁻¹ = proj 2 K h := by
      have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ (proj 2 K h)) hg
      simpa [MulAut.conj_apply] using this
    apply KFacts.proj_injective_of_charTwo
    rw [map_mul, map_mul]
    calc proj 2 K h * proj 2 K g = proj 2 K g * proj 2 K h * (proj 2 K g)⁻¹ * proj 2 K g := by
          rw [h1]
      _ = proj 2 K g * proj 2 K h := by group
  rw [CFSG.LieType.Universal.Symplectic.center_eq] at hcen
  have h2 : g ∈ spScalars 2 K := hcen
  rw [KFacts.spScalars_eq_bot, Subgroup.mem_bot] at h2
  exact h2

theorem map_pairRootMat_one (σ : K ≃+* K) (a b : Fin 2 ⊕ Fin 2) :
    (pairRootMat K a b 1).map σ = pairRootMat K a b 1 := by
  have hs : ∀ x : Fin 2 ⊕ Fin 2, σ (lineSign K x) = lineSign K x := by
    rintro (x | x) <;> simp [lineSign]
  ext x y
  simp only [Matrix.map_apply, pairRootMat, rootNil]
  split_ifs
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp [hs]

theorem fieldSp_pairRootElt_one (σ : K ≃+* K) {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b) :
    fieldSp 2 K σ (pairRootElt hab 1) = pairRootElt hab 1 := by
  apply statedSp_ext
  rw [coe_fieldSp, coe_pairRootElt, map_pairRootMat_one]

theorem mulVec_inl_inr_self (i : Fin 2) (v : Fin 2 ⊕ Fin 2 → K) :
    pairRootMat K (Sum.inl i) (Sum.inr i) 1 *ᵥ v =
      v + v (Sum.inr i) • Pi.single (Sum.inl i) 1 := by
  rw [pairRootMat_inl_inr_self, add_mulVec, one_mulVec, one_smul, single_mulVec_eq, one_mul]

theorem mulVec_inr_inl_self (i : Fin 2) (v : Fin 2 ⊕ Fin 2 → K) :
    pairRootMat K (Sum.inr i) (Sum.inl i) 1 *ᵥ v =
      v + v (Sum.inl i) • Pi.single (Sum.inr i) 1 := by
  rw [pairRootMat_inr_inl_self, add_mulVec, one_mulVec, one_smul, single_mulVec_eq, one_mul]

theorem mulVec_inl_inr_zero_one (v : Fin 2 ⊕ Fin 2 → K) :
    pairRootMat K (Sum.inl 0) (Sum.inr 1) 1 *ᵥ v =
      v + (v (Sum.inr 1) • Pi.single (Sum.inl 0) 1 + v (Sum.inr 0) • Pi.single (Sum.inl 1) 1) := by
  rw [pairRootMat_inl_inr (by decide), add_mulVec, one_mulVec, one_smul, add_mulVec,
    single_mulVec_eq, single_mulVec_eq, one_mul, one_mul]

theorem eq_bot_or_eq_top_of_pairRoot {W : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hA : ∀ i : Fin 2, ∀ v ∈ W, pairRootMat K (Sum.inl i) (Sum.inr i) 1 *ᵥ v ∈ W)
    (hB : ∀ i : Fin 2, ∀ v ∈ W, pairRootMat K (Sum.inr i) (Sum.inl i) 1 *ᵥ v ∈ W)
    (hC : ∀ v ∈ W, pairRootMat K (Sum.inl 0) (Sum.inr 1) 1 *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hA' : ∀ i : Fin 2, ∀ v ∈ W,
      v (Sum.inr i) • (Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro i v hv
    have h := W.sub_mem (hA i v hv) hv
    rwa [mulVec_inl_inr_self, add_sub_cancel_left] at h
  have hB' : ∀ i : Fin 2, ∀ v ∈ W,
      v (Sum.inl i) • (Pi.single (Sum.inr i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro i v hv
    have h := W.sub_mem (hB i v hv) hv
    rwa [mulVec_inr_inl_self, add_sub_cancel_left] at h
  have hC' : ∀ v ∈ W, v (Sum.inr 1) • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) +
      v (Sum.inr 0) • (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro v hv
    have h := W.sub_mem (hC v hv) hv
    rwa [mulVec_inl_inr_zero_one, add_sub_cancel_left] at h
  have hef : ∀ i : Fin 2, (Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W →
      (Pi.single (Sum.inr i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro i h
    simpa using hB' i _ h
  have hfe : ∀ i : Fin 2, (Pi.single (Sum.inr i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W →
      (Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro i h
    simpa using hA' i _ h
  have hswap0 : (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W →
      (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro h
    simpa using hC' _ h
  have hswap1 : (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W →
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro h
    simpa using hC' _ h
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hv0
  simp only [Pi.zero_apply] at hx
  have he : ∃ i : Fin 2, (Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    rcases x with i | i
    · exact ⟨i, hfe i ((Submodule.smul_mem_iff W hx).mp (hB' i v hv))⟩
    · exact ⟨i, (Submodule.smul_mem_iff W hx).mp (hA' i v hv)⟩
  obtain ⟨i, hi⟩ := he
  have h0 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W ∧
      (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    fin_cases i
    · exact ⟨hi, hswap0 (hef 0 hi)⟩
    · exact ⟨hswap1 (hef 1 hi), hi⟩
  have hall : ∀ y : Fin 2 ⊕ Fin 2, (Pi.single y 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    rintro (j | j) <;> fin_cases j
    · exact h0.1
    · exact h0.2
    · exact hef 0 h0.1
    · exact hef 1 h0.2
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine W.sum_mem fun y _ => ?_
  have hy : (Pi.single y (w y) : Fin 2 ⊕ Fin 2 → K) =
      w y • (Pi.single y 1 : Fin 2 ⊕ Fin 2 → K) := by
    ext z
    by_cases hz : z = y
    · subst hz
      simp
    · simp [hz]
  rw [hy]
  exact W.smul_mem _ (hall y)

theorem exists_stabilizer_of_parabolic_sp [Finite K] [CharP K 2]
    {Q : Subgroup (StatedProj (StatedSp 2 K))} (hQ : IsProperParabolic Q) :
    ∃ W : Submodule K (Fin 2 ⊕ Fin 2 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : StatedSp 2 K, proj 2 K g ∈ Q → ∀ v ∈ W,
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQtop, T, hT⟩ := hQ
  obtain ⟨-, -, hsyl, -⟩ := sylow_normalizers (r := 2) (K := K) 2 (by norm_num)
  have hmem : Subgroup.normalizer ((T : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) ∈
      LinearFlag.sylowNormalizers (StatedProj (StatedSp 2 K)) 2 := ⟨T, rfl⟩
  rw [hsyl] at hmem
  obtain ⟨F, hF, hFeq⟩ := hmem
  obtain ⟨g, hg⟩ := exists_map_flag_eq hF
  have hB : (projBorel 2 K).map (MulAut.conj (proj 2 K g)).toMonoidHom ≤ Q := by
    rw [← projIsoFlagStabilizer_eq_map_conj hg, ← hFeq]
    exact hT
  set A : Subgroup (StatedSp 2 K) :=
    (Q.comap (proj 2 K)).map (MulAut.conj g⁻¹).toMonoidHom with hA
  have hBA : borelSubgroup 2 K ≤ A := by
    intro b hb
    refine ⟨g * b * g⁻¹, ?_, ?_⟩
    · change proj 2 K (g * b * g⁻¹) ∈ Q
      apply hB
      refine ⟨proj 2 K b, ⟨b, hb, rfl⟩, ?_⟩
      simp [MulAut.conj_apply]
    · simp
      group
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  obtain ⟨i, hi⟩ : (borelCuts K A).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hne
    apply hQtop
    rw [hne] at hAeq
    rw [eq_top_iff]
    intro z _
    obtain ⟨x, rfl⟩ := proj_surjective (r := 2) (K := K) z
    have hx : g⁻¹ * x * g ∈ A := by
      rw [hAeq, mem_flagStabilizer]
      intro i hi
      exact absurd hi (Set.notMem_empty i)
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g⁻¹ * y * g = g⁻¹ * x * g := by simpa [MulAut.conj_apply] using hyx
    have : y = x := mul_left_cancel (mul_right_cancel hyx')
    exact this ▸ hy
  obtain ⟨hi1, hi2⟩ := borelCuts_le A i hi
  have hdim : Module.finrank K ((flag 2 K i).map (spAct g)) = i := by
    rw [finrank_map_spAct, finrank_flag (by omega)]
  refine ⟨(flag 2 K i).map (spAct g), ?_, ?_, ?_⟩
  · intro h
    rw [h, finrank_bot] at hdim
    omega
  · intro h
    rw [h, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
    simp at hdim
    omega
  · intro x hx v hv
    have hxA : g⁻¹ * x * g ∈ A := ⟨x, hx, by simp⟩
    rw [hAeq] at hxA
    have hstab := mem_flagStabilizer.mp hxA i hi
    have hx' : x ∈ stabilizer 2 K ((flag 2 K i).map (spAct g)) := by
      rw [stabilizer_map_spAct]
      refine ⟨g⁻¹ * x * g, hstab, ?_⟩
      simp [MulAut.conj_apply]
      group
    rw [mem_stabilizer] at hx'
    rw [← hx']
    exact ⟨v, hv, rfl⟩

theorem not_forall_fieldAut_fixed_mem [Finite K] [CharP K 2] (σ : K ≃+* K)
    {Q : Subgroup (StatedProj (StatedSp 2 K))} (hQ : IsProperParabolic Q) :
    ¬ ∀ z, fieldAut 2 K σ z = z → z ∈ Q := by
  intro hall
  obtain ⟨W, hW0, hWtop, hW⟩ := exists_stabilizer_of_parabolic_sp hQ
  have hmem : ∀ {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b), ∀ v ∈ W, pairRootMat K a b 1 *ᵥ v ∈ W := by
    intro a b hab v hv
    have hfix : fieldAut 2 K σ (proj 2 K (pairRootElt hab 1)) = proj 2 K (pairRootElt hab 1) := by
      rw [fieldAut_proj, fieldSp_pairRootElt_one]
    have := hW (pairRootElt hab 1) (hall _ hfix) v hv
    rwa [coe_pairRootElt] at this
  rcases eq_bot_or_eq_top_of_pairRoot (fun i => hmem Sum.inl_ne_inr)
    (fun i => hmem Sum.inr_ne_inl) (hmem Sum.inl_ne_inr) with h | h
  · exact hW0 h
  · exact hWtop h

theorem ks1919SplitAut_sp4 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (ψ : Y ≃* CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 n)) (E : Subgroup (MulAut Y))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (F : Subgroup (MulAut Y))
    (hFE : F ≤ E) (hFinn : F ≤ (MulAut.conj : Y →* MulAut Y).range) (hF9 : Nat.card F = 9)
    (c : MulAut Y) (hcE : c ∈ E) (hcF : c ∉ F) (P : Subgroup Y) (hP : IsProperParabolic P) :
    ¬ ∀ y : Y, c y = y → y ∈ P := by
  intro hfixP
  set K := GaloisField 2 n with hK
  set Ψ : Y ≃* StatedProj (StatedSp 2 K) :=
    ψ.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSp 2 K)).symm
    with hΨ
  set Γ : MulAut Y ≃* MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr Ψ with hΓ
  set α := Γ c with hα
  have hc3 : c ^ 3 = 1 := hE.2 c hcE
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hc3, map_one]
  by_cases hlin : α ∈ (conjAut 2 K).range
  · set I := (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))).range with hI
    have hαI : α ∈ I := by
      obtain ⟨A, hA⟩ := hlin
      rw [← hA]
      exact KFacts.conjAut_mem_inner_of_charTwo A
    set E₁ := E.map Γ.toMonoidHom with hE₁
    set F₁ := F.map Γ.toMonoidHom with hF₁
    set E' := E₁ ⊓ I with hE'
    have hF₁I : F₁ ≤ I := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, rfl⟩ := hFinn hx
      change Γ (MulAut.conj y) ∈ I
      rw [hΓ, KFacts.congr_mulAutConj]
      exact ⟨Ψ y, rfl⟩
    have hF₁E' : F₁ ≤ E' := le_inf (Subgroup.map_mono hFE) hF₁I
    have hαE' : α ∈ E' := ⟨⟨c, hcE, rfl⟩, hαI⟩
    have hαF₁ : α ∉ F₁ := by
      rintro ⟨x, hx, hxc⟩
      exact hcF (Γ.injective hxc ▸ hx)
    have hcardF₁ : Nat.card F₁ = 9 := by
      rw [hF₁, Subgroup.card_map_of_injective Γ.injective, hF9]
    have hcardE₁ : Nat.card E₁ = 27 := by
      rw [hE₁, Subgroup.card_map_of_injective Γ.injective, hE27]
    have hdvd1 : Nat.card E' ∣ 27 := hcardE₁ ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : 9 ∣ Nat.card E' := hcardF₁ ▸ Subgroup.card_dvd_of_le hF₁E'
    have hne9 : Nat.card E' ≠ 9 := by
      intro h9
      have : F₁ = E' := Subgroup.eq_of_le_of_card_ge hF₁E' (by rw [h9, hcardF₁])
      exact hαF₁ (this ▸ hαE')
    have h27 : Nat.card E' = 27 := by
      obtain ⟨k, hk⟩ := hdvd2
      have hk27 : 9 * k ≤ 27 := hk ▸ Nat.le_of_dvd (by norm_num) hdvd1
      rw [hk] at hdvd1 hne9 ⊢
      have hk3 : k ≤ 3 := by omega
      interval_cases k <;> first | rfl | omega
    have hcommE₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hexpE₁ : ∀ x ∈ E₁, x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
    set ι := (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))).comp (proj 2 K) with hι
    have hιinj : Function.Injective ι := conj_comp_proj_injective
    have hE'ι : E' ≤ ι.range := by
      intro x hx
      obtain ⟨z, hz⟩ := hx.2
      obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := K) z
      exact ⟨g, hz⟩
    set E₃ := E'.comap ι with hE₃
    have hcard₃ : Nat.card E₃ = 27 := by
      rw [← h27, ← Subgroup.map_comap_eq_self hE'ι, Subgroup.card_map_of_injective hιinj]
    have hE₃ab : CFSG.Open.IsElemAbelian 3 E₃ := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hιinj ?_)⟩⟩, fun a ha => hιinj ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hcommE₁ _ a.2.1 _ b.2.1
      · rw [map_pow, map_one]
        exact hexpE₁ _ ha.1
    have := card_le_nine_of_elemAbelian_sp4 hE₃ab
    omega
  · obtain ⟨σ, -, H, hαH⟩ := KFacts.sp4_even_order_three_field_descent α hα3 hlin
    set β := conjAut 2 K H with hβ
    set Q := (P.map Ψ.toMonoidHom).map ((β⁻¹ : MulAut (StatedProj (StatedSp 2 K))) :
      StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 K)).toMonoidHom with hQ
    have hQpar : IsProperParabolic Q :=
      isProperParabolic_map_equiv _ (isProperParabolic_map_equiv Ψ hP)
    apply not_forall_fieldAut_fixed_mem σ hQpar
    intro z hz
    have hfixα : α (β z) = β z := by
      rw [hαH]
      change β (fieldAut 2 K σ (β⁻¹ (β z))) = β z
      rw [MulAut.inv_apply_self, hz]
    have hcfix : c (Ψ.symm (β z)) = Ψ.symm (β z) := by
      have h1 : Ψ (c (Ψ.symm (β z))) = β z := hfixα
      have h2 := congrArg Ψ.symm h1
      rwa [MulEquiv.symm_apply_apply] at h2
    refine ⟨β z, ⟨Ψ.symm (β z), hfixP _ hcfix, by simp⟩, ?_⟩
    change β⁻¹ (β z) = z
    rw [MulAut.inv_apply_self]

end Sp4

end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof
