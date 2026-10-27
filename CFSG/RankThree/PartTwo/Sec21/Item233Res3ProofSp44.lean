module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofGen
public import CFSG.RankThree.PartTwo.KFacts.KS222Sp4
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSp44

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor spRev exists_conj_into_d8Tor_sp
  diagU_dvec4_mem_spRev d8Vec_four card_center_mulEquiv)
open U4Lines (torusD torusD_apply coe_torusD line_cases weyl₁ weyl₂ conj_weyl₁ conj_weyl₂)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther (hyperCent)

namespace Item233Res3Proof

variable {G : Type} [Group G]

abbrev Fq4 : Type := GaloisField 2 2

abbrev SP44 : Type := ↥(spRev Fq4)

theorem card_mu3_F4 : Nat.card (rootsOfUnity 3 Fq4) = 3 :=
  CFSG.LinearGroups.card_rootsOfUnity_of_dvd (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num)

@[expose] noncomputable def sD (v : D8Mod 3 Fq4) : SP44 :=
  ⟨torusD v, by rw [torusD_apply, d8Vec_four]; exact diagU_dvec4_mem_spRev _ _⟩

noncomputable abbrev TS : Subgroup SP44 := (d8Tor 3 Fq4 4).subgroupOf (spRev Fq4)

theorem sD_mem (v : D8Mod 3 Fq4) : sD v ∈ TS := ⟨v, rfl⟩

theorem exists_sD {t : SP44} (ht : t ∈ TS) : ∃ v, t = sD v := by
  obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
  exact ⟨v, Subtype.ext hv.symm⟩

theorem sD_pow_three (v : D8Mod 3 Fq4) : sD v ^ 3 = 1 := by
  have h1 : v.1 ^ 3 = 1 := Subtype.ext ((mem_rootsOfUnity 3 _).mp v.1.2)
  have h2 : v.2 ^ 3 = 1 := Subtype.ext ((mem_rootsOfUnity 3 _).mp v.2.2)
  have h : v ^ 3 = 1 := Prod.ext h1 h2
  apply Subtype.ext
  change torusD v ^ 3 = 1
  rw [← map_pow, h, map_one]

theorem sD_injective {v v' : D8Mod 3 Fq4} (h : sD v = sD v') : v = v' := by
  have h' := congrArg (fun x : SP44 => ((x : GL (Fin 4) Fq4) : Matrix (Fin 4) (Fin 4) Fq4)) h
  simp only [sD, coe_torusD] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp at h0 h1
  exact Prod.ext (Subtype.ext (Units.ext h0)) (Subtype.ext (Units.ext h1))

theorem card_TS_le : Nat.card TS ≤ 9 := by
  have hsurj : Function.Surjective (fun v : D8Mod 3 Fq4 => (⟨sD v, sD_mem v⟩ : TS)) := by
    rintro ⟨t, ht⟩
    obtain ⟨v, rfl⟩ := exists_sD ht
    exact ⟨v, rfl⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod, card_mu3_F4] at h

@[expose] noncomputable def ws1 : SP44 :=
  ⟨weyl₁, CFSG.RankThree.PartOne.SP4C.hP_spRev _ (by decide)⟩

@[expose] noncomputable def ws2 : SP44 :=
  ⟨weyl₂, CFSG.RankThree.PartOne.SP4C.hP_spRev _ (by decide)⟩

theorem ws1_conj (v : D8Mod 3 Fq4) : ws1 * sD v * ws1⁻¹ = sD (v.2, v.1) :=
  Subtype.ext (conj_weyl₁ v)

theorem ws2_conj (v : D8Mod 3 Fq4) : ws2 * sD v * ws2⁻¹ = sD (v.1, v.2⁻¹) :=
  Subtype.ext (conj_weyl₂ v)

theorem ws1_mul_self : ws1 * ws1 = 1 := by
  apply Subtype.ext
  change weyl₁ * weyl₁ = (1 : GL (Fin 4) Fq4)
  rw [weyl₁, ← map_mul, show (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) *
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 1 by decide, map_one]

theorem ws2_mul_self : ws2 * ws2 = 1 := by
  apply Subtype.ext
  change weyl₂ * weyl₂ = (1 : GL (Fin 4) Fq4)
  rw [weyl₂, ← map_mul, show (Equiv.swap (1 : Fin 4) 2) * (Equiv.swap (1 : Fin 4) 2) = 1 by
    decide, map_one]

theorem exists_model_Sp44 [Finite G] {A Z : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G))
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3)
    (eZ : Z ≃* projSp 2 Fq4) :
    Subgroup.center Z = ⊥ ∧ Nat.card (A ⊓ Z : Subgroup G) = 9 ∧
      ∃ e : Z ≃* SP44, (∀ t ∈ TS, ((e.symm t : Z) : G) ∈ A) ∧
        ∀ f (hf : f ∈ A ⊓ Z), e ⟨f, (Subgroup.mem_inf.mp hf).2⟩ ∈ TS := by
  have hAe : IsElemAbelian 3 A := hA.prop
  set e₁ := eZ.trans Sec4.Item434SmallTwoOther.sp44Equiv
  have hZc : Subgroup.center Z = ⊥ := by
    have h := card_center_mulEquiv e₁
    rw [Sec4.Item434SmallTwoOther.center_sp44, Subgroup.card_bot] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have hCI : Sec4.CubeInner Z := by
    have hS : Sec4.CubeInner (StatedSp 2 Fq4) := fun τ h3 =>
      Sec4.Item434SmallTwoOther.mem_range_conj_of_pow_three_sp44 τ h3
    exact hS.of_mulEquiv e₁
  have h27 : ¬ 27 ∣ Nat.card Z := by
    rw [Nat.card_congr e₁.toEquiv, Sec4.Item434SmallTwoOther.card_sp44]
    norm_num
  have hF9 := card_inf_eq_nine hA hA27 hAN hZc hCI hC3 h27
  refine ⟨hZc, hF9, ?_⟩
  let e₂ : projSp 2 Fq4 ≃* SP44 :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 Fq4)).symm.trans
      ((CFSG.RankThree.PartOne.KFU.spEquivProj (K := Fq4) (by norm_num)).symm.trans
        (CFSG.RankThree.PartOne.KFU.spRevEquiv Fq4))
  set e₀ : Z ≃* SP44 := eZ.trans e₂
  set X : Subgroup SP44 := ((A ⊓ Z).subgroupOf Z).map e₀.toMonoidHom with hX
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    have : y ^ 3 = 1 := Subtype.ext (by
      simpa using hAe.2 _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1)
    rw [this, map_one]
  have hX9 : Nat.card X = 9 := by
    rw [hX, Subgroup.card_map_of_injective e₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ Z ≤ Z)).toEquiv, hF9]
  have hdvd : 3 ∣ Nat.card Fq4 - 1 := by rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_sp Nat.prime_three (by norm_num) hdvd X hX3
  have hXT : X.map (MulAut.conj g).toMonoidHom = TS := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hX9]
      exact card_TS_le
  set e : Z ≃* SP44 := e₀.trans (MulAut.conj g)
  refine ⟨e, ?_, ?_⟩
  · intro t ht
    rw [← hXT] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : e.symm ((MulAut.conj g).toMonoidHom (e₀.toMonoidHom y)) = y := by
      change e.symm (e y) = y
      exact e.symm_apply_apply y
    rw [h1]
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1
  · intro f hf
    rw [← hXT]
    exact ⟨e₀ ⟨f, (Subgroup.mem_inf.mp hf).2⟩, ⟨⟨f, (Subgroup.mem_inf.mp hf).2⟩,
      Subgroup.mem_subgroupOf.mpr hf, rfl⟩, rfl⟩

theorem ws121_conj (v : D8Mod 3 Fq4) :
    (ws1 * ws2 * ws1) * sD v * (ws1 * ws2 * ws1)⁻¹ = sD (v.1⁻¹, v.2) := by
  have e : (ws1 * ws2 * ws1) * sD v * (ws1 * ws2 * ws1)⁻¹ =
      ws1 * (ws2 * (ws1 * sD v * ws1⁻¹) * ws2⁻¹) * ws1⁻¹ := by group
  rw [e, ws1_conj, ws2_conj, ws1_conj]

theorem ws212_conj (v : D8Mod 3 Fq4) :
    (ws2 * ws1 * ws2) * sD v * (ws2 * ws1 * ws2)⁻¹ = sD (v.2⁻¹, v.1⁻¹) := by
  have e : (ws2 * ws1 * ws2) * sD v * (ws2 * ws1 * ws2)⁻¹ =
      ws2 * (ws1 * (ws2 * sD v * ws2⁻¹) * ws1⁻¹) * ws2⁻¹ := by group
  rw [e, ws2_conj, ws1_conj, ws2_conj]

theorem mul_self_of_aba {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1) :
    (a * b * a) * (a * b * a) = 1 := by
  calc (a * b * a) * (a * b * a) = a * b * (a * a) * b * a := by group
    _ = 1 := by rw [ha, mul_one, mul_assoc a b b, hb, mul_one, ha]

theorem exists_reflection_line_Sp44 [Finite G] {A Z : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 3 ^ 3) (hZc : Subgroup.center Z = ⊥)
    (hF9 : Nat.card (A ⊓ Z : Subgroup G) = 9)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3) (e : Z ≃* SP44)
    (hT1 : ∀ t ∈ TS, ((e.symm t : Z) : G) ∈ A)
    (hT2 : ∀ f (hf : f ∈ A ⊓ Z), e ⟨f, (Subgroup.mem_inf.mp hf).2⟩ ∈ TS)
    {R : Subgroup G} (hRF : R ≤ A ⊓ Z) (hR3 : Nat.card R = 3) :
    ∃ ρ ∈ starOf A Z, IsReflectionOn ρ ∧ R ≤ fixedInG A ρ ∧
      Z ⊓ Subgroup.centralizer (fixedInG A ρ : Set G) =
        Z ⊓ Subgroup.centralizer (R : Set G) := by
  set θ : SP44 →* G := Z.subtype.comp e.symm.toMonoidHom with hθ
  have hθZ : ∀ x, θ x ∈ Z := fun x => (e.symm x).2
  have hθinj : ∀ x y : SP44, x ^ 3 = 1 → y ^ 3 = 1 → θ x = θ y → x = y := fun x y _ _ h =>
    e.symm.injective (Subtype.ext h)
  have hF : ∀ f ∈ A ⊓ Z, ∃ t ∈ TS, f = θ t := by
    intro f hf
    refine ⟨e ⟨f, (Subgroup.mem_inf.mp hf).2⟩, hT2 f hf, ?_⟩
    change f = ((e.symm (e ⟨f, _⟩) : Z) : G)
    rw [MulEquiv.symm_apply_apply]
  have hT3 : ∀ t ∈ TS, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨v, rfl⟩ := exists_sD ht
    exact sD_pow_three v
  have hRZ : R ≤ Z := hRF.trans inf_le_right
  set R' : Subgroup SP44 := (R.subgroupOf Z).map e.toMonoidHom with hR'
  have hR'T : R' ≤ TS := by
    rintro _ ⟨r, hr, rfl⟩
    exact hT2 r (hRF (Subgroup.mem_subgroupOf.mp hr))
  have hR'3 : Nat.card (R'.map (spRev Fq4).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (spRev Fq4).subtype_injective, hR',
      Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRZ).toEquiv, hR3]
  have hR'd : R'.map (spRev Fq4).subtype ≤ d8Tor 3 Fq4 4 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hR'T hx
  have hRθ : ∀ v : D8Mod 3 Fq4, R'.map (spRev Fq4).subtype = Subgroup.zpowers (torusD v) →
      R = Subgroup.zpowers (θ (sD v)) := by
    intro v hv
    have h1 : R' = Subgroup.zpowers (sD v) := by
      apply Subgroup.map_injective (spRev Fq4).subtype_injective
      rw [hv, MonoidHom.map_zpowers]
      rfl
    have h2 : R.subgroupOf Z = R'.map e.symm.toMonoidHom := by
      rw [hR', Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Z := by
        ext x
        simp
      rw [this, Subgroup.map_id]
    calc R = (R.subgroupOf Z).map Z.subtype := (Subgroup.map_subgroupOf_eq_of_le hRZ).symm
      _ = (R'.map e.symm.toMonoidHom).map Z.subtype := by rw [h2]
      _ = R'.map θ := by rw [Subgroup.map_map]
      _ = Subgroup.zpowers (θ (sD v)) := by rw [h1, MonoidHom.map_zpowers]
  have key : ∀ (w : SP44) (v v₁ : D8Mod 3 Fq4), w * w = 1 →
      (∀ t ∈ TS, w * t * w⁻¹ ∈ TS) → w * sD v * w⁻¹ = sD v → w * sD v₁ * w⁻¹ ≠ sD v₁ →
      v ≠ 1 → R = Subgroup.zpowers (θ (sD v)) →
      ∃ ρ ∈ starOf A Z, IsReflectionOn ρ ∧ R ≤ fixedInG A ρ ∧
        Z ⊓ Subgroup.centralizer (fixedInG A ρ : Set G) =
          Z ⊓ Subgroup.centralizer (R : Set G) := by
    intro w v v₁ hw2 hwT hv hv₁ hv1 hR
    have hx01 : sD v ≠ 1 := by
      intro h
      apply hv1
      apply sD_injective
      rw [h]
      exact Subtype.ext (by simp [sD])
    obtain ⟨ρ, hρZ, hρ, hle, hcent⟩ := exists_reflection_of_model hAe hA27 hZc hF9 hC3 θ hθZ hT3
      hT1 hF hθinj hw2 hwT (sD_mem v) (sD_mem v₁) hv hv₁ hx01
    exact ⟨ρ, hρZ, hρ, hR ▸ hle, by rw [hcent, hR]⟩
  have hTconj : ∀ (f : D8Mod 3 Fq4 → D8Mod 3 Fq4) (w : SP44),
      (∀ u, w * sD u * w⁻¹ = sD (f u)) → ∀ t ∈ TS, w * t * w⁻¹ ∈ TS := by
    intro f w hw t ht
    obtain ⟨u, rfl⟩ := exists_sD ht
    rw [hw]
    exact sD_mem _
  have : Nontrivial (rootsOfUnity 3 Fq4) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_mu3_F4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 Fq4)
  have hωinv : ω⁻¹ ≠ 1 := fun h => hω (inv_eq_one.mp h)
  have hωω : ω ≠ ω⁻¹ := by
    intro h
    apply hω
    have h3 : ω ^ 3 = 1 := by
      have := pow_card_eq_one' (G := rootsOfUnity 3 Fq4) (x := ω)
      rwa [card_mu3_F4] at this
    have h2 : ω * ω = 1 := by
      calc ω * ω = ω * ω⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω * ω)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have hne : ∀ {a b c d : rootsOfUnity 3 Fq4}, (a ≠ c ∨ b ≠ d) → sD (a, b) ≠ sD (c, d) := by
    intro a b c d h he
    have := sD_injective he
    rcases h with h | h
    · exact h (congrArg Prod.fst this)
    · exact h (congrArg Prod.snd this)
  rcases line_cases card_mu3_F4 hω hR'd hR'3 with h | h | h | h
  ·
    refine key ws2 (ω, 1) (1, ω) ws2_mul_self (hTconj _ ws2 ws2_conj) ?_ ?_
      (fun h1 => hω (congrArg Prod.fst h1)) (hRθ _ h)
    · rw [ws2_conj]
      simp
    · rw [ws2_conj]
      exact hne (Or.inr (show ω⁻¹ ≠ ω from hωω.symm))
  ·
    refine key (ws1 * ws2 * ws1) (1, ω) (ω, 1) (mul_self_of_aba ws1_mul_self ws2_mul_self)
      (hTconj _ _ ws121_conj) ?_ ?_ (fun h1 => hω (congrArg Prod.snd h1)) (hRθ _ h)
    · rw [ws121_conj]
      simp
    · rw [ws121_conj]
      exact hne (Or.inl (show ω⁻¹ ≠ ω from hωω.symm))
  ·
    refine key ws1 (ω, ω) (ω, 1) ws1_mul_self (hTconj _ ws1 ws1_conj) ?_ ?_
      (fun h1 => hω (congrArg Prod.fst h1)) (hRθ _ h)
    · rw [ws1_conj]
    · rw [ws1_conj]
      exact hne (Or.inl (Ne.symm hω))
  ·
    refine key (ws2 * ws1 * ws2) (ω, ω⁻¹) (ω, 1) (mul_self_of_aba ws2_mul_self ws1_mul_self)
      (hTconj _ _ ws212_conj) ?_ ?_ (fun h1 => hω (congrArg Prod.fst h1)) (hRθ _ h)
    · rw [ws212_conj]
      simp
    · rw [ws212_conj]
      exact hne (Or.inl (by simpa using hω.symm))

theorem kOf_eq_perfectResidual_of_mulEquiv [Finite G] {A L : Subgroup G} (hA : A ∈ partTwoF G)
    {c : G} (hcA : c ∈ A) (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A}
    (hφL : φ ∈ starOf A L) (hφ2 : orderOf φ = 2) {m : ℕ} (hm : 2 ≤ m)
    (e : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) ≃*
      projSL 2 (GaloisField 2 m)) :
    kOf A φ = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) := by
  have := isSimpleGroup_projSL_two hm
  have hK := Item222Proof.kZero_eq_perfectResidual hA hcA hLc hφL hφ2 e.isSimpleGroup
    (exists_not_commute_of_mulEquiv_projSL e) (three_dvd_card_of_mulEquiv_projSL e)
  have hU : ¬ StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
    rw [hK]
    exact Item222Proof.not_statedClassicalModel_U34_of_mulEquiv (by omega) e
  rw [kOf_eq_kZero hU, hK]

theorem map_commOf_le_of_mem_starOf {A Z : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G)) {ρ : MulAut A} (hρZ : ρ ∈ starOf A Z) :
    (commOf ρ).map A.subtype ≤ Z := by
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  obtain ⟨⟨w, hwN⟩, hwZ, hρw⟩ := hρZ
  have hwZ' : w ∈ Z := Subgroup.mem_subgroupOf.mp hwZ
  have hρapp : ∀ a : A, ((ρ a : A) : G) = w * a * w⁻¹ := fun a => by rw [← hρw]; rfl
  rintro _ ⟨u, hu, rfl⟩
  have hmem : u ∈ (commHom hAc ρ).range := (range_commHom hAc ρ).symm ▸ hu
  obtain ⟨a, rfl⟩ := hmem
  change ((a⁻¹ * ρ a : A) : G) ∈ Z
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hρapp]
  have haN : (a : G)⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ (hAN a.2)
  have h1 : (a : G)⁻¹ * w * ((a : G)⁻¹)⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp haN w).mp hwZ'
  have e : (a : G)⁻¹ * (w * a * w⁻¹) = ((a : G)⁻¹ * w * ((a : G)⁻¹)⁻¹) * w⁻¹ := by group
  rw [e]
  exact Z.mul_mem h1 (Z.inv_mem hwZ')

theorem mem_sup_of_mem_centralizer_line [Finite G] (h222 : Item222) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {Z : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (Z : Set G))
    (hAZ : (A ⊓ Z) ⊔ (A ⊓ Subgroup.centralizer (Z : Set G)) = A)
    (hF9 : Nat.card (A ⊓ Z : Subgroup G) = 9) {ρ : MulAut A} (hρD : ρ ∈ dStar A)
    (hρZ : ρ ∈ starOf A Z) {R : Subgroup G} (hRF : R ≤ A ⊓ Z) (hR3 : Nat.card R = 3)
    (hRρ : R ≤ fixedInG A ρ)
    (hKρ : kOf A ρ = inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer (R : Set G)))
    (hK60 : Nat.card (kOf A ρ) = 60) {x : G}
    (hx : x ∈ Z ⊓ Subgroup.centralizer (R : Set G)) :
    x ∈ (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔ kOf A ρ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hρ : IsReflectionOn ρ := hρD.1
  have hρ2 := apply_apply_of_orderOf_eq_two hρ.1
  set X := Z ⊓ Subgroup.centralizer (R : Set G) with hXdef
  set N' : Subgroup X := perfectResidual X with hN'def
  have hKN : kOf A ρ = N'.map X.subtype := hKρ
  set P : Subgroup G := (commOf ρ).map A.subtype with hPdef
  have hPK : P ≤ kOf A ρ := map_commOf_le_kOf h222 hpair hK hρD
  have hPX : P ≤ X := hPK.trans (hKN ▸ Subgroup.map_subtype_le _)
  have hPZ : P ≤ Z := map_commOf_le_of_mem_starOf hAe hAN hρZ
  have hP3 : Nat.card P = 3 := by
    rw [hPdef, Subgroup.card_map_of_injective A.subtype_injective]
    exact hρ.2
  have hPA : P ≤ A := Subgroup.map_subtype_le _
  have hPR : P ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyP, hyR⟩
    obtain ⟨u, hu, rfl⟩ := hyP
    have hinv : ρ u = u⁻¹ := inv_of_mem_commOf hAc hρ2 hu
    obtain ⟨v, hv, hvu⟩ := hRρ hyR
    have hvu' : v = u := Subtype.ext hvu
    rw [hvu'] at hv
    have hfix : ρ u = u := (mem_fixedSubgroupOf ρ u).mp hv
    have hu2 : u * u = 1 := by
      calc u * u = u * ρ u := by rw [hfix]
        _ = 1 := by rw [hinv, mul_inv_cancel]
    have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 u u.2)
    have hu1 : u = 1 := by
      calc u = u ^ 3 * (u * u)⁻¹ := by group
        _ = 1 := by rw [hu3, hu2, inv_one, one_mul]
    rw [Subgroup.mem_bot, hu1]
    rfl
  have hRPF : R ⊔ P = A ⊓ Z := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hRF (le_inf hPA hPZ))
    have hlt : R < R ⊔ P := by
      refine lt_of_le_of_ne le_sup_left fun h => ?_
      have hPR' : P ≤ R := h ▸ le_sup_right
      have : P = ⊥ := by rw [← hPR]; exact (inf_eq_left.mpr hPR').symm
      rw [this, Subgroup.card_bot] at hP3
      omega
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card (R ⊔ P : Subgroup G) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hF9]
      exact Subgroup.card_dvd_of_le (sup_le hRF (le_inf hPA hPZ))
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rw [hR3, hkeq] at h1
    rw [hF9, hkeq]
    interval_cases k
    · norm_num at h1
    · norm_num at h1
    · norm_num
  have hN'card : Nat.card N' = 60 := by
    rw [← hK60, hKN, Subgroup.card_map_of_injective X.subtype_injective]
  set P' : Subgroup X := P.subgroupOf X with hP'def
  have hP'N : P' ≤ N' := by
    intro y hy
    have hyK : (y : G) ∈ kOf A ρ := hPK (Subgroup.mem_subgroupOf.mp hy)
    rw [hKN] at hyK
    obtain ⟨y', hy', hyy'⟩ := hyK
    rwa [← Subtype.ext hyy']
  have hP'card : Nat.card P' = 3 := by
    rw [hP'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hP3]
  have hfac : (Nat.card N').factorization 3 = 1 := by
    rw [hN'card, show (60 : ℕ) = 3 ^ 1 * 20 by norm_num]
    exact Sec4.Item434AltPerm.factorization_three_pow_mul 1 (by norm_num)
  let PS : Sylow 3 N' := Sylow.ofCard (P'.subgroupOf N') (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'N).toEquiv, hP'card, hfac, pow_one])
  have hPSmap : (PS : Subgroup N').map N'.subtype = P' := by
    change (P'.subgroupOf N').map N'.subtype = P'
    exact Subgroup.map_subgroupOf_eq_of_le hP'N
  have hFrat := Sylow.normalizer_sup_eq_top PS
  rw [hPSmap] at hFrat
  have hxX : (⟨x, hx⟩ : X) ∈ ((Subgroup.normalizer (P' : Set X) ⊔ N' : Subgroup X) : Set X) := by
    rw [hFrat]
    exact Subgroup.mem_top _
  rw [Subgroup.mul_normal] at hxX
  obtain ⟨y, hy, n, hn, hyn⟩ := hxX
  have hxyn : x = (y : G) * (n : G) := by
    have h1 : y * n = ⟨x, hx⟩ := hyn
    rw [← Subgroup.coe_mul, h1]
  rw [hxyn]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨(y.2 : (y : G) ∈ X).1, ?_⟩)
    (Subgroup.mem_sup_right (hKN ▸ ⟨n, hn, rfl⟩))
  have hyZ : (y : G) ∈ Z := (y.2 : (y : G) ∈ X).1
  have hyR : (y : G) ∈ Subgroup.centralizer (R : Set G) := (y.2 : (y : G) ∈ X).2
  have hyP : ∀ p ∈ P, (y : G) * p * (y : G)⁻¹ ∈ P := by
    intro p hp
    have hpX : p ∈ X := hPX hp
    have h1 := (Subgroup.mem_normalizer_iff.mp hy ⟨p, hpX⟩).mp
      (show (⟨p, hpX⟩ : X) ∈ (P' : Set X) from Subgroup.mem_subgroupOf.mpr hp)
    exact Subgroup.mem_subgroupOf.mp h1
  have hyF : ∀ f ∈ A ⊓ Z, (y : G) * f * (y : G)⁻¹ ∈ A ⊓ Z := by
    intro f hf
    have hRN : R ≤ Subgroup.normalizer (P : Set G) := fun r hr =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun p hp =>
        congrArg Subtype.val (hAc ⟨p, hPA hp⟩ ⟨r, (hRF hr).1⟩))
    have hfRP : f ∈ ((R ⊔ P : Subgroup G) : Set G) := by rw [hRPF]; exact hf
    rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left P R hRN] at hfRP
    obtain ⟨p, hp, r, hr, rfl⟩ := hfRP
    have hyr : (y : G) * r * (y : G)⁻¹ = r := by
      rw [← Subgroup.mem_centralizer_iff.mp hyR r hr, mul_inv_cancel_right]
    have e : (y : G) * (p * r) * (y : G)⁻¹ =
        ((y : G) * p * (y : G)⁻¹) * ((y : G) * r * (y : G)⁻¹) := by group
    rw [e, hyr, ← hRPF]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hyP p hp)) (Subgroup.mem_sup_left hr)
  apply mem_normalizer_of_forall_conj_mem
  intro a ha
  obtain ⟨f, hf, c', hc', rfl⟩ := exists_mul_of_inf_sup_eq hAZ a ha
  have hyc : (y : G) * c' * (y : G)⁻¹ = c' := by
    rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc').2 _ hyZ, mul_inv_cancel_right]
  have e : (y : G) * (f * c') * (y : G)⁻¹ =
      ((y : G) * f * (y : G)⁻¹) * ((y : G) * c' * (y : G)⁻¹) := by group
  rw [e, hyc]
  exact A.mul_mem (Subgroup.mem_inf.mp (hyF f hf)).1 (Subgroup.mem_inf.mp hc').1

theorem closure_hyperCent_eq_top_Sp44 {Z : Type*} [Group Z] [Finite Z] (eZ : Z ≃* projSp 2 Fq4)
    {F : Subgroup Z} (hF9 : Nat.card F = 9) : Subgroup.closure (hyperCent F) = ⊤ := by
  set ψ : StatedSp 2 Fq4 ≃* Z := (eZ.trans Sec4.Item434SmallTwoOther.sp44Equiv).symm
  set D0 := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torus 2 Fq4
  have h0 : Subgroup.closure (hyperCent D0) = ⊤ :=
    Sec4.Item434SmallTwoOther.closure_hyperCent_torus_gf4
  have h1 : Subgroup.closure (hyperCent (D0.map ψ.toMonoidHom)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : ψ.symm y ∈ Subgroup.closure (hyperCent D0) := by
      rw [h0]
      exact Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem ψ.toMonoidHom hy
    rw [MonoidHom.map_closure] at h2
    have h3 : ψ.toMonoidHom (ψ.symm y) = y := ψ.apply_symm_apply y
    rw [h3] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨x, ⟨R, hRP, hR3, hRx⟩, rfl⟩
    refine ⟨R.map ψ.toMonoidHom, Subgroup.map_mono hRP, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective ψ.injective, Subgroup.card_map_of_injective ψ.injective,
        hR3]
    · rintro _ ⟨r, hr, rfl⟩
      change ψ r * ψ x = ψ x * ψ r
      rw [← map_mul, ← map_mul, hRx r hr]
  have hD0 : Nat.card (D0.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective,
      Sec4.Item434SmallTwoOther.card_torus_gf4]
    norm_num
  have hZ3 : (Nat.card Z).factorization 3 = 2 := by
    rw [Nat.card_congr (eZ.trans Sec4.Item434SmallTwoOther.sp44Equiv).toEquiv]
    exact Sec4.Item434SmallTwoOther.factorization_card_sp44
  obtain ⟨g, hg⟩ := Sec4.Item434SmallTwoOther.exists_map_conj_of_sylow
    (P₀ := D0.map ψ.toMonoidHom) (P := F) (by rw [hD0, hZ3]; norm_num) (by rw [hF9, hD0])
  rw [hg]
  exact Sec4.Item434SmallTwoOther.closure_hyperCent_map_conj h1 g

end Item233Res3Proof

open Item233Res3Proof

theorem item233ZRootGenSp44_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) : Item233ZRootGenSp44 := by
  intro G _ _ A E U c L hpair hconc hA27 φ hφ Z hZ hKZ h3 hR eK hZsp
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  have hK := hKW G A E U c L hpair
  obtain ⟨z, hzA, hz1, hZz⟩ := mem_thetaComponentFamily_iff.mp hZ.1
  have hAN : A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hzA hz1
      Z hZz
  have hC3 := Item221ResProof.card_inf_centralizer_eq_three h66 hpair.standing hpair.mem_S hZ
  obtain ⟨eZ⟩ := hZsp
  obtain ⟨hZc, hF9, e, hT1, hT2⟩ := exists_model_Sp44 hAmax hA27 hAN hC3 eZ
  have hAZ := inf_sup_inf_centralizer_eq hA27 hZc hF9 hC3
  set F' : Subgroup Z := (A ⊓ Z).subgroupOf Z with hF'
  have hF'9 : Nat.card F' = 9 := by
    rw [hF', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ Z ≤ Z)).toEquiv,
      hF9]
  have hgen := closure_hyperCent_eq_top_Sp44 eZ hF'9
  set RHS := (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔
    ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ with hRHS
  have hstep : ∀ x ∈ hyperCent F', (x : G) ∈ RHS := by
    rintro x ⟨R0, hR0F, hR03, hR0x⟩
    set R : Subgroup G := R0.map Z.subtype with hRdef
    have hRF : R ≤ A ⊓ Z := by
      rintro _ ⟨r, hr, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hR0F hr)
    have hR3 : Nat.card R = 3 := by
      rw [hRdef, Subgroup.card_map_of_injective Z.subtype_injective]
      omega
    have hxR : (x : G) ∈ Z ⊓ Subgroup.centralizer (R : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      exact congrArg Subtype.val (hR0x r hr)
    obtain ⟨ρ, hρZ, hρ, hRρ, hcent⟩ := exists_reflection_line_Sp44 hAe hA27 hZc hF9 hC3 e hT1
      hT2 hRF hR3
    have hρD : ρ ∈ dStar A := hR ρ hρZ hρ
    obtain ⟨eR⟩ := ks222Sp4 G Z R 2 (by norm_num) even_two ⟨eZ⟩ (hRF.trans inf_le_right) hR3
    have hcent' : inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer (fixedInG A ρ : Set G)) =
        inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer (R : Set G)) := by
      rw [hcent]
    have hKρ := kOf_eq_perfectResidual_of_mulEquiv hAF hzA hZz hρZ hρ.1 (le_refl 2)
      ((MulEquiv.subgroupCongr hcent').trans eR)
    rw [hcent'] at hKρ
    have hK60 : Nat.card (kOf A ρ) = 60 := by
      rw [hKρ, Nat.card_congr eR.toEquiv, card_projSL_two 2 (by norm_num)]
      norm_num
    have hmem := mem_sup_of_mem_centralizer_line h222 hpair hK hAN hAZ hF9 hρD hρZ hRF hR3 hRρ
      hKρ hK60 hxR
    have hle : (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔ kOf A ρ ≤ RHS :=
      sup_le_sup_left (le_iSup_of_le ρ (le_iSup_of_le hρD
        (le_iSup (fun _ : ρ ∈ starOf A Z => kOf A ρ) hρZ))) _
    exact hle hmem
  intro w hw
  have hw' : (⟨w, hw⟩ : Z) ∈ Subgroup.closure (hyperCent F') := by
    rw [hgen]
    exact Subgroup.mem_top _
  have hle : Subgroup.closure (hyperCent F') ≤ RHS.comap Z.subtype :=
    (Subgroup.closure_le _).mpr fun x hx => hstep x hx
  exact hle hw'

end CFSG.RankThree.PartTwo.Sec21
