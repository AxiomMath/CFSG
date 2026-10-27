module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank Matrix Polynomial CFSG.RankThree.PartOne CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

namespace SevSpNs

variable {F : Type} [Field F] {n e s r p : ℕ}
  {A₀ : GL (Fin n ⊕ Fin n) F} {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
  {C : Matrix (Fin e) (Fin e) F}

theorem pow_mulVec_eq_of_mulVec_eq {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    {v : Fin n ⊕ Fin n → F} (hv : M *ᵥ v = v) (i : ℕ) : (M ^ i) *ᵥ v = v := by
  induction i with
  | zero => rw [pow_zero, one_mulVec]
  | succ i ih => rw [pow_succ, ← mulVec_mulVec, hv, ih]

theorem fix_of_supp [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) (hCp : C ^ p = 1)
    (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {W U : StatedSp n F}
    {k k' : Fin s → ℕ} (hW : RootPlaneSp.SpBlockMat A₀ ε C W k)
    (hU : RootPlaneSp.SpBlockMat A₀ ε C U k') (hsupp : ∀ i, p ∣ k i → p ∣ k' i)
    {v : Fin n ⊕ Fin n → F} (hv : spEnd W v = v) : spEnd U v = v := by
  have h1 : SLNS.nsCore (r := r) C (SpNonsplitComp.truncExp p k k') = 1 := by
    rw [NoOffPSLRest.nsCore_congr hCp (k' := 0) fun i => ?_, SLNS.nsCore_zero]
    unfold SpNonsplitComp.truncExp
    split_ifs with hi
    · rw [Pi.zero_apply, Nat.zero_mod]
      exact Nat.mod_eq_zero_of_dvd (hsupp i hi)
    · rfl
  have h2 := SpNonsplitComp.nsCore_truncExp (r := r) hp hp2 hCp hcunit k k'
  rw [h1] at h2
  set E := ∑ i ∈ Finset.range p, SLNS.nsCore (r := r) C k ^ i with hE
  have h3 : SLNS.nsCore (r := r) C k' * E = E := by
    have h4 : SLNS.nsCore (r := r) C k' * E + 1 - E - 1 = 0 := by rw [← h2, sub_self]
    rw [show SLNS.nsCore (r := r) C k' * E + 1 - E - 1 = SLNS.nsCore (r := r) C k' * E - E by
      abel] at h4
    exact sub_eq_zero.mp h4
  have h6 : mat n F U * SpNonsplitComp.frameRing A₀ ε E = SpNonsplitComp.frameRing A₀ ε E := by
    rw [SpNonsplitComp.mat_eq_of_spBlockMat hU, ← map_mul, h3]
  have hE' : SpNonsplitComp.frameRing A₀ ε E = ∑ i ∈ Finset.range p, mat n F W ^ i := by
    rw [hE, map_sum]
    simp only [map_pow, ← SpNonsplitComp.mat_eq_of_spBlockMat hW]
  have hv' : mat n F W *ᵥ v = v := hv
  have hEv : SpNonsplitComp.frameRing A₀ ε E *ᵥ v = v := by
    rw [hE', Matrix.sum_mulVec]
    simp only [pow_mulVec_eq_of_mulVec_eq hv', Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul F, SpNonsplitComp.natCast_eq_one hp hp2, one_smul]
  change mat n F U *ᵥ v = v
  calc mat n F U *ᵥ v = mat n F U *ᵥ (SpNonsplitComp.frameRing A₀ ε E *ᵥ v) := by rw [hEv]
    _ = SpNonsplitComp.frameRing A₀ ε E *ᵥ v := by rw [mulVec_mulVec, h6]
    _ = v := hEv

omit [Field F] in
theorem mem_spSupported_of_fix {K : Type} [Field K] {x w g : StatedSp n K} {O : Set K[X]}
    (hw : w ∈ spSupported x O) (hgx : g * x = x * g)
    (hfix : ∀ v, spEnd w v = v → spEnd g v = v) : g ∈ spSupported x O :=
  mem_spSupported.mpr ⟨hgx, fun k hk hkO v hv => hfix v ((mem_spSupported.mp hw).2 k hk hkO v hv)⟩

theorem exists_mem_inf_centralizer {H : Type*} [Group H] [Finite H] {q : ℕ} (hq : q.Prime)
    {N A : Subgroup H} (hA : IsPGroup q A) (hN : ∀ a ∈ A, ∀ l ∈ N, a * l * a⁻¹ ∈ N)
    (hqN : q ∣ Nat.card N) :
    ∃ w ∈ N, w ≠ 1 ∧ w ^ q = 1 ∧ ∀ a ∈ A, a * w = w * a := by
  have : Fact q.Prime := ⟨hq⟩
  let act : MulAction A N :=
    { smul := fun a l => ⟨(a : H) * l * (a : H)⁻¹, hN a a.2 l l.2⟩
      one_smul := fun l => Subtype.ext (show (1 : H) * l * (1 : H)⁻¹ = l by simp)
      mul_smul := fun a b l => Subtype.ext (show ((a : H) * b) * l * ((a : H) * b)⁻¹ =
        a * (b * l * (b : H)⁻¹) * (a : H)⁻¹ by group) }
  have hmod := hA.card_modEq_card_fixedPoints N
  set M : Subgroup H := N ⊓ Subgroup.centralizer (A : Set H) with hM
  have hfix : ∀ l : N, l ∈ MulAction.fixedPoints A N ↔ (l : H) ∈ M := by
    intro l
    constructor
    · intro hl
      refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 : (a : H) * l * a⁻¹ = l := congrArg Subtype.val (hl ⟨a, ha⟩)
      exact mul_inv_eq_iff_eq_mul.mp h1
    · intro hl a
      apply Subtype.ext
      change (a : H) * l * (a : H)⁻¹ = l
      rw [Subgroup.mem_centralizer_iff.mp hl.2 a a.2, mul_inv_cancel_right]
  have heq : MulAction.fixedPoints A N ≃ M :=
    { toFun := fun l => ⟨l.1.1, (hfix l.1).mp l.2⟩
      invFun := fun m => ⟨⟨m.1, m.2.1⟩, (hfix ⟨m.1, m.2.1⟩).mpr m.2⟩
      left_inv := fun l => rfl
      right_inv := fun m => rfl }
  have hdvd : q ∣ Nat.card M := by
    rw [← Nat.card_congr heq]
    apply Nat.dvd_of_mod_eq_zero
    rw [← hmod]
    exact Nat.mod_eq_zero_of_dvd hqN
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := M) q hdvd
  refine ⟨w, w.2.1, fun h1 => ?_, ?_, fun a ha => ?_⟩
  · have : w = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hw
    exact hq.one_lt.ne hw
  · have h1 : w ^ q = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    exact congrArg Subtype.val h1
  · exact Subgroup.mem_centralizer_iff.mp w.2.2 a ha

@[expose] def permCoords (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (σ : Equiv.Perm (Fin s)) :
    Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r :=
  ε.trans (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin e)) σ.symm) (Equiv.refl (Fin r)))

omit [Field F] in
theorem nsCore_submatrix_perm [Field F] (C : Matrix (Fin e) (Fin e) F) (k : Fin s → ℕ)
    (σ : Equiv.Perm (Fin s)) :
    (SLNS.nsCore (r := r) C (k ∘ σ)).submatrix
        (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin e)) σ.symm) (Equiv.refl (Fin r)))
        (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin e)) σ.symm) (Equiv.refl (Fin r))) =
      SLNS.nsCore C k := by
  ext (⟨a, i⟩ | u) (⟨b, j⟩ | v) <;>
    simp [SLNS.nsCore, Matrix.blockDiagonal_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem spBlockMat_perm {X : StatedSp n F} {k : Fin s → ℕ} (σ : Equiv.Perm (Fin s)) :
    RootPlaneSp.SpBlockMat A₀ ε C X k ↔
      RootPlaneSp.SpBlockMat A₀ (permCoords ε σ) C X (k ∘ σ) := by
  have h : (SLNS.nsCore (r := r) C (k ∘ σ)).submatrix (permCoords ε σ) (permCoords ε σ) =
      (SLNS.nsCore C k).submatrix ε ε := by
    rw [← nsCore_submatrix_perm C k σ, Matrix.submatrix_submatrix]
    rfl
  unfold RootPlaneSp.SpBlockMat
  rw [h]

theorem exists_perm_zero_one {s : ℕ} (hs : 2 ≤ s) {j j' : Fin s} (hjj : j ≠ j') :
    ∃ σ : Equiv.Perm (Fin s), σ ⟨0, by omega⟩ = j ∧ σ ⟨1, by omega⟩ = j' := by
  set i₀ : Fin s := ⟨0, by omega⟩
  set i₁ : Fin s := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by simpa [i₀, i₁] using congrArg Fin.val h
  set a := Equiv.swap i₀ j j' with ha
  have ha0 : a ≠ i₀ := by
    intro h
    have h1 : Equiv.swap i₀ j a = Equiv.swap i₀ j i₀ := by rw [h]
    rw [ha, Equiv.swap_apply_self, Equiv.swap_apply_left] at h1
    exact hjj h1.symm
  refine ⟨(Equiv.swap i₁ a).trans (Equiv.swap i₀ j), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm ha0),
      Equiv.swap_apply_left]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left, ha, Equiv.swap_apply_self]

theorem direct_of_two_supp [Finite F] [CharP F 2] {G : Type} [Group G] (hp : p.Prime)
    (hp2 : p ≠ 2) (hns : ¬ p ∣ Nat.card F - 1) (he : 2 ≤ e) (hs : 4 ≤ s) (hCp : C ^ p = 1)
    (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1))
    (hreal : ∀ k : Fin s → ℕ, ∃ X : StatedSp n F, RootPlaneSp.SpBlockMat A₀ ε C X k)
    {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ) {Bs : Subgroup G}
    (hframe : ∀ b ∈ Bs, ∃ k, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k)
    {z : StatedSp n F} {k : Fin s → ℕ} (hz : RootPlaneSp.SpBlockMat A₀ ε C z k) (hz1 : z ≠ 1)
    {j j' : Fin s} (hjj : j ≠ j') (hk : ∀ i, i ≠ j → i ≠ j' → p ∣ k i) :
    ∃ L₂ : Subgroup G, CFSG.Assembly.IsComponentOf L₂ (ψ.range ⊓ Subgroup.centralizer {ψ z}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_zero_one (by omega : 2 ≤ s) hjj
  set k₀ : Fin s → ℕ := fun i => if i = j ∨ i = j' then k i else 0 with hk₀
  have hz₀ : RootPlaneSp.SpBlockMat A₀ ε C z k₀ := by
    unfold RootPlaneSp.SpBlockMat at hz ⊢
    rw [hz, NoOffPSLRest.nsCore_congr hCp (k := k) (k' := k₀) fun i => ?_]
    by_cases hi : i = j ∨ i = j'
    · simp [hk₀, hi]
    · push Not at hi
      simp only [hk₀, hi.1, hi.2, or_self, ite_false, Nat.zero_mod]
      exact Nat.mod_eq_zero_of_dvd (hk i hi.1 hi.2)
  have hz' := (spBlockMat_perm σ).mp hz₀
  have havoid : ∀ i : Fin s, 2 ≤ (i : ℕ) → σ i ≠ j ∧ σ i ≠ j' := by
    intro i hi
    constructor
    · intro h
      have := σ.injective (h.trans hσ0.symm)
      have h2 := congrArg Fin.val this
      simp at h2
      omega
    · intro h
      have := σ.injective (h.trans hσ1.symm)
      have h2 := congrArg Fin.val this
      simp at h2
      omega
  have hplane : RootPlaneSp.PlaneSupp (k₀ ∘ σ) := by
    intro i hi
    obtain ⟨h1, h2⟩ := havoid i hi
    simp [hk₀, h1, h2]
  have hreal' : ∀ k' : Fin s → ℕ, ∃ X : StatedSp n F,
      RootPlaneSp.SpBlockMat A₀ (permCoords ε σ) C X k' := by
    intro k'
    obtain ⟨X, hX⟩ := hreal (k' ∘ σ.symm)
    refine ⟨X, ?_⟩
    have h1 := (spBlockMat_perm σ).mp hX
    have h2 : (k' ∘ σ.symm) ∘ σ = k' := by
      funext i
      simp
    rwa [h2] at h1
  obtain ⟨L, hL, hLc⟩ := ggSpNonsplitCompInput_holds F n e s r p hp hp2 hns he hs C
    (permCoords ε σ) A₀ hCp hcunit hreal' z (k₀ ∘ σ) hplane hz' hz1
  have hmapC : (Subgroup.centralizer ({z} : Set (StatedSp n F))).map ψ =
      ψ.range ⊓ Subgroup.centralizer {ψ z} := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hψ (by rw [map_mul, map_mul]; exact hy), rfl⟩
  refine ⟨L.map ψ, ?_, ?_⟩
  · have h1 := isComponentOf_map_of_injective ψ hψ hL
    rwa [hmapC] at h1
  have hcongr : ∀ {b : G} {k k' : Fin s → ℕ}, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k →
      (∀ i, k i % p = k' i % p) → NoOffPSLRest.SpFrameRep ψ A₀ ε C b k' := by
    rintro b k k' ⟨X, hX1, hX2⟩ hkk
    exact ⟨X, hX1, by rw [hX2, NoOffPSLRest.nsCore_congr hCp hkk]⟩
  have hsupp : ∀ b ∈ Bs ⊓ Subgroup.centralizer ((L.map ψ : Subgroup G) : Set G),
      ∀ i, i ≠ j → i ≠ j' → p ∣ NoOffPSLRest.spExp ψ A₀ ε C b i := by
    intro b hb i hij hij'
    obtain ⟨Y, hY1, hY2⟩ := NoOffPSLRest.spExp_spec (hframe b hb.1)
    have hYc : Y ∈ Subgroup.centralizer (L : Set (StatedSp n F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      apply hψ
      have := (Subgroup.mem_centralizer_iff.mp hb.2) (ψ l) ⟨l, hl, rfl⟩
      rw [map_mul, map_mul, ← hY1]
      exact this
    have h1 := hLc Y _ ((spBlockMat_perm σ).mp hY2) hYc (σ.symm i) (by
      by_contra hlt
      push Not at hlt
      interval_cases hv : ((σ.symm i : Fin s) : ℕ)
      · apply hij
        rw [← hσ0, show (⟨0, by omega⟩ : Fin s) = σ.symm i from Fin.ext hv.symm,
          Equiv.apply_symm_apply]
      · apply hij'
        rw [← hσ1, show (⟨1, by omega⟩ : Fin s) = σ.symm i from Fin.ext hv.symm,
          Equiv.apply_symm_apply])
    simpa using h1
  have hinj : Function.Injective (fun b : (Bs ⊓ Subgroup.centralizer
      ((L.map ψ : Subgroup G) : Set G) : Subgroup G) =>
      (((NoOffPSLRest.spExp ψ A₀ ε C b j : ℕ) : ZMod p),
        ((NoOffPSLRest.spExp ψ A₀ ε C b j' : ℕ) : ZMod p))) := by
    intro b b' hbb
    have hb := NoOffPSLRest.spExp_spec (hframe b b.2.1)
    have hb' := NoOffPSLRest.spExp_spec (hframe b' b'.2.1)
    simp only [Prod.mk.injEq] at hbb
    have hmod : ∀ i, NoOffPSLRest.spExp ψ A₀ ε C b' i % p =
        NoOffPSLRest.spExp ψ A₀ ε C b i % p := by
      intro i
      by_cases hij : i = j
      · subst hij
        exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp hbb.1).symm
      · by_cases hij' : i = j'
        · subst hij'
          exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp hbb.2).symm
        · rw [Nat.mod_eq_zero_of_dvd (hsupp b' b'.2 i hij hij'),
            Nat.mod_eq_zero_of_dvd (hsupp b b.2 i hij hij')]
    exact Subtype.ext (hb.eq (hcongr hb' hmod))
  have : NeZero p := ⟨hp.ne_zero⟩
  calc Nat.card (Bs ⊓ Subgroup.centralizer ((L.map ψ : Subgroup G) : Set G) : Subgroup G)
      ≤ Nat.card (ZMod p × ZMod p) := Nat.card_le_card_of_injective _ hinj
    _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_zmod, sq]

end SevSpNs

end CFSG.StandardType
