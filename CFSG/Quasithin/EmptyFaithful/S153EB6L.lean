module

public import CFSG.Quasithin.Background.G64Transvec
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.Quasithin.EmptyFaithful.S153EB6H
public import CFSG.Quasithin.EmptyFaithful.S153EB6J

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL

theorem exists_gl_of_inv {K : Type} [Field K] {n : ℕ} (f g : (Fin n → K) →ₗ[K] (Fin n → K))
    (h1 : ∀ v, f (g v) = v) (h2 : ∀ v, g (f v) = v) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin n) K,
      (∀ v, ((γ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v = f v) ∧
      ∀ v, (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K).mulVec v = g v := by
  have hMM' : LinearMap.toMatrix' f * LinearMap.toMatrix' g = 1 := by
    rw [← LinearMap.toMatrix'_comp, show f ∘ₗ g = LinearMap.id from LinearMap.ext h1,
      LinearMap.toMatrix'_id]
  have hM'M : LinearMap.toMatrix' g * LinearMap.toMatrix' f = 1 := by
    rw [← LinearMap.toMatrix'_comp, show g ∘ₗ f = LinearMap.id from LinearMap.ext h2,
      LinearMap.toMatrix'_id]
  refine ⟨Units.mk _ _ hMM' hM'M, fun v => LinearMap.toMatrix'_mulVec f v, fun v => ?_⟩
  exact LinearMap.toMatrix'_mulVec g v

section Transv

variable {K : Type} [Field K] {n : ℕ}

@[expose] def tauK (i₀ i₁ : Fin n) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun v := fun l => v l + if l = i₀ then v i₁ else 0
  map_add' v w := by
    funext l
    by_cases h : l = i₀
    · simp only [h, ite_true, Pi.add_apply]
      ring
    · simp [h]
  map_smul' r v := by
    funext l
    by_cases h : l = i₀
    · simp only [h, ite_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [h]

theorem tauK_apply (i₀ i₁ : Fin n) (v : Fin n → K) (l : Fin n) :
    tauK i₀ i₁ v l = v l + if l = i₀ then v i₁ else 0 := rfl

theorem tauK_apply_of_ne {i₀ i₁ l : Fin n} (h : l ≠ i₀) (v : Fin n → K) :
    tauK i₀ i₁ v l = v l := by
  simp [tauK_apply, h]

theorem tauK_tauK (h2 : (2 : K) = 0) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) (v : Fin n → K) :
    tauK i₀ i₁ (tauK i₀ i₁ v) = v := by
  funext l
  by_cases h : l = i₀
  · subst h
    simp [tauK_apply, hne.symm]
    linear_combination (v i₁) * h2
  · simp [tauK_apply, h]

theorem tauK_ne {i₀ i₁ : Fin n} :
    tauK i₀ i₁ (Pi.single i₁ (1 : K)) ≠ Pi.single i₁ 1 := by
  intro h
  have := congrFun h i₀
  simp [tauK_apply] at this

theorem cblock_apply_of_ne' {j k l : Fin n} (hj : l ≠ j) (hk : l ≠ k) (v : Fin n → K) :
    cblock j k v l = v l := by
  simp [cblock, hj, hk]

theorem tauK_cblock {i₀ i₁ j k : Fin n} (hjk : j ≠ k) (hj0 : j ≠ i₀) (hj1 : j ≠ i₁)
    (hk0 : k ≠ i₀) (hk1 : k ≠ i₁) (v : Fin n → K) :
    cblock j k (tauK i₀ i₁ v) = tauK i₀ i₁ (cblock j k v) := by
  funext l
  by_cases h1 : l = j
  · subst h1
    have e1 : cblock l k (tauK i₀ i₁ v) l = tauK i₀ i₁ v k := by simp [cblock]
    have e2 : cblock l k v l = v k := by simp [cblock]
    rw [e1, tauK_apply_of_ne hk0, tauK_apply_of_ne hj0, e2]
  by_cases h2 : l = k
  · subst h2
    have e1 : cblock j l (tauK i₀ i₁ v) l = tauK i₀ i₁ v j + tauK i₀ i₁ v l := by
      simp [cblock, h1]
    have e2 : cblock j l v l = v j + v l := by simp [cblock, h1]
    rw [e1, tauK_apply_of_ne hj0, tauK_apply_of_ne hk0, tauK_apply_of_ne hk0, e2]
  · rw [cblock_apply_of_ne' h1 h2, tauK_apply, tauK_apply, cblock_apply_of_ne' h1 h2,
      cblock_apply_of_ne' hj1.symm hk1.symm]

end Transv

section GLLevel

variable {n : ℕ}

theorem gl_ext {A B : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)}
    (h : ∀ v : Fin n → ZMod 2,
      (A : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v = (B : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v) :
    A = B :=
  Units.ext (Matrix.ext_of_mulVec_single fun _ => h _)

theorem gl_mulVec_mul (A B : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    ((A * B : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v =
      (A : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec ((B : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem gl_mulVec_one (v : Fin n → ZMod 2) :
    ((1 : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v = v := by
  rw [Units.val_one, Matrix.one_mulVec]

theorem exists_comm3_gl (hn : 4 ≤ n) {x : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)}
    (hx : G64.IsTransvecGL x) :
    ∃ c : Matrix.GeneralLinearGroup (Fin n) (ZMod 2), orderOf c = 3 ∧ c * x = x * c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : ZMod 2) = 0 := by decide
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let j : Fin n := ⟨2, by omega⟩
  let k : Fin n := ⟨3, by omega⟩
  have hjk : j ≠ k := by simp [j, k, Fin.ext_iff]
  have hj0 : j ≠ i₀ := by simp [j, i₀, Fin.ext_iff]
  have hj1 : j ≠ i₁ := by simp [j, i₁, Fin.ext_iff]
  have hk0 : k ≠ i₀ := by simp [k, i₀, Fin.ext_iff]
  have hk1 : k ≠ i₁ := by simp [k, i₁, Fin.ext_iff]
  have hi01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  obtain ⟨γc, hγc, -⟩ := exists_gl_of_inv (cblock j k : (Fin n → ZMod 2) →ₗ[ZMod 2] _)
    (cblock j k ∘ₗ cblock j k) (fun v => cblock_cube h2 hjk v)
    (fun v => cblock_cube h2 hjk v)
  obtain ⟨γt, hγt, -⟩ := exists_gl_of_inv (tauK i₀ i₁ : (Fin n → ZMod 2) →ₗ[ZMod 2] _)
    (tauK i₀ i₁) (fun v => tauK_tauK h2 hi01 v) (fun v => tauK_tauK h2 hi01 v)
  have hT : G64.IsTransvecGL γt := by
    refine ⟨fun h1 => ?_, Pi.single i₀ 1, fun v => ?_⟩
    · have h3 := hγt (Pi.single i₁ 1)
      rw [h1, gl_mulVec_one] at h3
      exact tauK_ne h3.symm
    · rw [hγt]
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (v i₁) with h | h
      · left
        funext l
        by_cases hl : l = i₀ <;> simp [tauK_apply, hl, h]
      · right
        funext l
        by_cases hl : l = i₀
        · simp [tauK_apply, hl, h]
          ring
        · simp [tauK_apply, hl]
  obtain ⟨g, hg⟩ := G64.exists_conj_of_isTransvecGL hx hT
  have hcomm : γc * γt = γt * γc := by
    apply gl_ext
    intro v
    rw [gl_mulVec_mul, gl_mulVec_mul, hγc, hγt, hγt, hγc]
    exact tauK_cblock hjk hj0 hj1 hk0 hk1 v
  have hc3 : γc ^ 3 = 1 := by
    apply gl_ext
    intro v
    rw [pow_succ, pow_two, gl_mulVec_mul, gl_mulVec_mul, hγc, hγc, hγc, gl_mulVec_one]
    exact cblock_cube h2 hjk v
  have hc1 : γc ≠ 1 := by
    intro h1
    have h3 := hγc (Pi.single j 1)
    rw [h1, gl_mulVec_one] at h3
    exact cblock_ne hjk h3.symm
  refine ⟨g⁻¹ * γc * g, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · have : (g⁻¹ * γc * g) ^ 3 = g⁻¹ * γc ^ 3 * g := by rw [pow_three, pow_three]; group
      rw [this, hc3]
      group
    · intro h1
      apply hc1
      have : γc = g * (g⁻¹ * γc * g) * g⁻¹ := by group
      rw [this, h1]
      group
  · have hx' : x = g⁻¹ * γt * g := by rw [← hg]; group
    calc g⁻¹ * γc * g * x = g⁻¹ * (γc * γt) * g := by rw [hx']; group
      _ = g⁻¹ * (γt * γc) * g := by rw [hcomm]
      _ = x * (g⁻¹ * γc * g) := by rw [hx']; group

end GLLevel

section Transfer

variable {V : Type} [CommGroup V]

@[expose] noncomputable def autGLe {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2)) :
    MulAut V ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  (MulAut.congr e).trans (S153E58.mulAutPiEquivGL n)

theorem autGLe_mulVec {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2)) (φ : MulAut V)
    (v : Fin n → ZMod 2) :
    ((autGLe e φ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v =
      Multiplicative.toAdd (e (φ (e.symm (Multiplicative.ofAdd v)))) := by
  have h1 := S153E58.mulAutPiEquivGL_symm_apply n (autGLe e φ) (Multiplicative.ofAdd v)
  have h2 : (S153E58.mulAutPiEquivGL n).symm (autGLe e φ) = MulAut.congr e φ :=
    MulEquiv.symm_apply_apply _ _
  rw [h2] at h1
  have h3 : (MulAut.congr e φ) (Multiplicative.ofAdd v) =
      e (φ (e.symm (Multiplicative.ofAdd v))) := by simp [MulAut.congr_apply]
  rw [h3] at h1
  have := congrArg Multiplicative.toAdd h1
  simpa using this.symm

theorem isTransvecGL_autGLe {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2)) {a : MulAut V}
    (ha1 : a ≠ 1) (hc : Nat.card ↥(commV (Subgroup.zpowers a)) = 2) :
    G64.IsTransvecGL (autGLe e a) := by
  obtain ⟨p, hp⟩ : ∃ p : V, ∀ w ∈ commV (Subgroup.zpowers a), w = 1 ∨ w = p := by
    obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : ↥(commV (Subgroup.zpowers a)))).1 hc
    refine ⟨(y : V), fun w hw => ?_⟩
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val (hyu ⟨w, hw⟩ (fun h' => hw1 (congrArg Subtype.val h'))))
  refine ⟨fun h1 => ha1 ?_, Multiplicative.toAdd (e p), fun v => ?_⟩
  · exact (autGLe e).injective (by rw [h1, map_one])
  · set u := e.symm (Multiplicative.ofAdd v) with hu
    have hmem : a u * u⁻¹ ∈ commV (Subgroup.zpowers a) :=
      Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, u, rfl⟩
    have he : e u = Multiplicative.ofAdd v := e.apply_symm_apply _
    have key : Multiplicative.toAdd (e (a u)) - v = Multiplicative.toAdd (e (a u * u⁻¹)) := by
      rw [map_mul, map_inv, he, toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg]
      rfl
    rw [autGLe_mulVec, key]
    rcases hp _ hmem with h | h
    · left
      rw [h, map_one]
      rfl
    · right
      rw [h]

theorem exists_comm3_of_transvection [Finite V] (hexp : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card V = 2 ^ n) {a : MulAut V} (ha1 : a ≠ 1)
    (hc : Nat.card ↥(commV (Subgroup.zpowers a)) = 2) :
    ∃ g : MulAut V, orderOf g = 3 ∧ g * a = a * g := by
  obtain ⟨e⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one hexp hcard
  obtain ⟨c, hc3, hcc⟩ := exists_comm3_gl hn (isTransvecGL_autGLe e ha1 hc)
  refine ⟨(autGLe e).symm c, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hc3
  · apply (autGLe e).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hcc

theorem isSimple_mulAut [Finite V] (hexp : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card V = 2 ^ n) : IsSimpleGroup (MulAut V) := by
  obtain ⟨e⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one hexp hcard
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := Bridge.isSimple_sl_zmod2 n hn
  let ι : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
      ⟨Matrix.SpecialLinearGroup.toGL_injective, MonoidHom.range_eq_top.1 G64.range_toGL⟩
  exact ((autGLe e).trans ι.symm).isSimpleGroup

end Transfer

section BinaryFacts

variable {V : Type} [CommGroup V]

theorem modelFacts_of_binary [Finite V] {G Kb : Subgroup (MulAut V)} {a : MulAut V}
    (hI : Induced V G Kb a) {n : ℕ} (hn : 3 ≤ n) (hmt : BinaryNaturalSL G ⊤ ⊥ n 1) :
    ModelFacts V G Kb a := by
  have hG : G = ⊤ := G64.BinaryNaturalSL.eq_top hmt
  have hcard : Nat.card V = 2 ^ n := G64.BinaryNaturalSL.card_eq hmt
  have := isSimple_mulAut hI.exp hn hcard
  have hKb : Kb = ⊤ := by
    have : Kb.Normal := ⟨fun k hk g => hI.norm g (hG ▸ Subgroup.mem_top g) k hk⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Kb with h | h
    · exact absurd h hI.ne
    · exact h
  refine ⟨fun p => exists_three_fix_of_mt hI.mt hI.big p, ?_, ?_⟩
  · intro M hM hnorm hne
    rw [hKb] at hM hnorm ⊢
    have : M.Normal := ⟨fun m hm g => hnorm g (Subgroup.mem_top g) m hm⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · exact absurd h hne
    · exact h
  · by_cases h3 : n = 3
    · left
      refine ⟨hG, ?_, by rw [hKb, hG]⟩
      rw [hcard, h3]
      norm_num
    · right
      obtain ⟨g, hg3, hgc⟩ := exists_comm3_of_transvection hI.exp (by omega) hcard hI.a1 hI.card
      exact ⟨g, hG ▸ Subgroup.mem_top g, hg3, hgc⟩

end BinaryFacts

end S153EB6

end CFSG.Quasithin
