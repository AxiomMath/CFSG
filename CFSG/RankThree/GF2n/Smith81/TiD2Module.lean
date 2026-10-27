module

public import CFSG.RankThree.GF2n.Smith81.TiOmega4Plus
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.RankThree.GF2n.Smith81.TiLemmaF
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic
public import CFSG.RankThree.GF2n.Smith81.Sec115Dim

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem _root_.CFSG.RankThree.GF2n.Stroth80.Ctx.Lgen_le_H0 (hc : Ctx M Q Z B) :
    Lgen M (LB M Q B) ≤ H0 M Z := by
  unfold Lgen
  refine iSup₂_le fun m hm y hy => ?_
  rw [mem_conjSubgroup] at hy
  have hyM : y ∈ M := by
    have h1 : m * (m⁻¹ * y * m) * m⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hm (hc.LB_le_M hy)) (M.inv_mem hm)
    rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at h1
  refine ⟨hyM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hz' : m⁻¹ * z * m ∈ Z := by
    have := cqt_conj_mem_Z hc.hyp (M.inv_mem hm) hz
    simpa using this
  have h1 := hc.LB_centralizes_Z hy (m⁻¹ * z * m) hz'
  have h2 : (m⁻¹ * y * m) * (m⁻¹ * z * m) = (m⁻¹ * z * m) * (m⁻¹ * y * m) := by
    have : (m⁻¹ * y * m) * (m⁻¹ * z * m) * (m⁻¹ * y * m)⁻¹ = m⁻¹ * z * m := h1
    calc (m⁻¹ * y * m) * (m⁻¹ * z * m) = (m⁻¹ * y * m) * (m⁻¹ * z * m) * (m⁻¹ * y * m)⁻¹ *
          (m⁻¹ * y * m) := by group
      _ = (m⁻¹ * z * m) * (m⁻¹ * y * m) := by rw [this]
  calc z * y = m * ((m⁻¹ * z * m) * (m⁻¹ * y * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * y * m) * (m⁻¹ * z * m)) * m⁻¹ := by rw [h2]
    _ = y * z := by group

theorem _root_.CFSG.RankThree.GF2n.Stroth80.Ctx.Q_le_Lgen (hc : Ctx M Q Z B) :
    Q ≤ Lgen M (LB M Q B) :=
  le_sup_left.trans (le_Lgen_self M (LB M Q B))

theorem _root_.CFSG.RankThree.GF2n.Stroth80.Ctx.Lgen_le_M (hc : Ctx M Q Z B) :
    Lgen M (LB M Q B) ≤ M :=
  Lgen_le hc.LB_le_M

theorem _root_.CFSG.RankThree.GF2n.Stroth80.Ctx.mem_Lgen_conj (hc : Ctx M Q Z B) {m s : G}
    (hm : m ∈ M) (hs : s ∈ Lgen M (LB M Q B)) : m * s * m⁻¹ ∈ Lgen M (LB M Q B) := by
  have h1 : m * s * m⁻¹ ∈ conjSubgroup m (Lgen M (LB M Q B)) := by
    rw [mem_conjSubgroup, show m⁻¹ * (m * s * m⁻¹) * m = s by group]
    exact hs
  exact conjSubgroup_Lgen_le hm h1

theorem exists_det_equiv {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (hK2 : (2 : K) = 0) (B : LinearMap.BilinForm K E) (Qf : E → K)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f)
    (hyp : ∃ S₁ S₂ : Submodule K E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, Qf x = 0) ∧
      ∀ x ∈ S₂, Qf x = 0)
    (hdim : Module.finrank K E = 4) : ∃ Θ : E ≃ₗ[K] Mat2 K, ∀ e, (Θ e).det = Qf e := by
  obtain ⟨S₁, S₂, hc, hQ₁, hQ₂⟩ := hyp
  have hsym : ∀ x y, B x y = B y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    linear_combination h - (B y x) * hK2
  have hB₁ : ∀ x ∈ S₁, ∀ y ∈ S₁, B x y = 0 := fun x hx y hy => by
    have h := hQadd x y
    rw [hQ₁ _ (S₁.add_mem hx hy), hQ₁ x hx, hQ₁ y hy] at h
    linear_combination -h
  have hB₂ : ∀ x ∈ S₂, ∀ y ∈ S₂, B x y = 0 := fun x hx y hy => by
    have h := hQadd x y
    rw [hQ₂ _ (S₂.add_mem hx hy), hQ₂ x hx, hQ₂ y hy] at h
    linear_combination -h
  have hd1 := Sec115Dim.two_mul_finrank_le_of_iso B hK2 halt hnd S₁ hB₁
  have hd2 := Sec115Dim.two_mul_finrank_le_of_iso B hK2 halt hnd S₂ hB₂
  have hsum : Module.finrank K S₁ + Module.finrank K S₂ = 4 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have h1 : Module.finrank K S₁ = 2 := by omega
  have h2 : Module.finrank K S₂ = 2 := by omega
  let b : Module.Basis (Fin 2) K S₁ := Module.finBasisOfFinrankEq K S₁ h1
  let Φ : S₂ →ₗ[K] (Fin 2 → K) := LinearMap.pi (fun i => (B (b i : E)).domRestrict S₂)
  have hΦ : ∀ (f : S₂) i, Φ f i = B (b i : E) (f : E) := fun f i => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : ∀ i, B (b i : E) (f : E) = 0 := fun i => by rw [← hΦ, hf]; rfl
    have hS₁ : ∀ x ∈ S₁, B x (f : E) = 0 := by
      intro x hx
      have hx' := b.sum_repr ⟨x, hx⟩
      have : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : E) := by
        have h := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at h
        simp only [Submodule.coe_smul] at h
        exact h.symm
      rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply, h0, smul_zero]
    have hall : ∀ y : E, B (f : E) y = 0 := by
      intro y
      obtain ⟨u, hu, v, hv, rfl⟩ :=
        Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : y ∈ S₁ ⊔ S₂)
      rw [map_add, hsym (f : E) u, hS₁ u hu, zero_add]
      exact hB₂ _ f.2 _ hv
    exact Subtype.ext (hnd _ hall)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h2]; simp)).mp hinj
  obtain ⟨f₀, hf₀⟩ := hsurj (Pi.single 0 1)
  obtain ⟨f₁, hf₁⟩ := hsurj (Pi.single 1 1)
  have h00 : B (b 0 : E) (f₀ : E) = 1 := by simpa [hΦ] using congrFun hf₀ 0
  have h10 : B (b 1 : E) (f₀ : E) = 0 := by simpa [hΦ] using congrFun hf₀ 1
  have h01 : B (b 0 : E) (f₁ : E) = 0 := by simpa [hΦ] using congrFun hf₁ 0
  have h11 : B (b 1 : E) (f₁ : E) = 1 := by simpa [hΦ] using congrFun hf₁ 1
  have hb0b1 : ∀ i j, B (b i : E) (b j : E) = 0 := fun i j => hB₁ _ (b i).2 _ (b j).2
  have hff : ∀ u v : S₂, B (u : E) (v : E) = 0 := fun u v => hB₂ _ u.2 _ v.2
  let θinv : Mat2 K →ₗ[K] E :=
    { toFun := fun X => X 0 0 • (b 0 : E) + X 0 1 • (b 1 : E) + X 1 1 • (f₀ : E) +
        X 1 0 • (f₁ : E)
      map_add' := fun X Y => by
        simp only [Matrix.add_apply, add_smul]
        abel
      map_smul' := fun c X => by
        simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add] }
  have hθ : ∀ X, θinv X = X 0 0 • (b 0 : E) + X 0 1 • (b 1 : E) + X 1 1 • (f₀ : E) +
      X 1 0 • (f₁ : E) := fun X => rfl
  have hθQ : ∀ X, Qf (θinv X) = X.det := by
    intro X
    have hu : X 0 0 • (b 0 : E) + X 0 1 • (b 1 : E) ∈ S₁ :=
      S₁.add_mem (S₁.smul_mem _ (b 0).2) (S₁.smul_mem _ (b 1).2)
    have hv : X 1 1 • (f₀ : E) + X 1 0 • (f₁ : E) ∈ S₂ :=
      S₂.add_mem (S₂.smul_mem _ f₀.2) (S₂.smul_mem _ f₁.2)
    have e1 : θinv X = (X 0 0 • (b 0 : E) + X 0 1 • (b 1 : E)) +
        (X 1 1 • (f₀ : E) + X 1 0 • (f₁ : E)) := by rw [hθ]; abel
    rw [e1, hQadd, hQ₁ _ hu, hQ₂ _ hv, zero_add, zero_add]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h00,
      h01, h10, h11]
    rw [Matrix.det_fin_two]
    linear_combination (X 0 1 * X 1 0) * hK2
  have hθinj : Function.Injective θinv := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    have hX' : θinv X = 0 := hX
    have c00 : X 0 0 = 0 := by
      have := congrArg (fun v => B v (f₀ : E)) hX'
      simp only [hθ, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h00, h10, halt, hff f₀ f₁, hff f₁ f₀, map_zero, LinearMap.zero_apply] at this
      linear_combination this
    have c01 : X 0 1 = 0 := by
      have := congrArg (fun v => B v (f₁ : E)) hX'
      simp only [hθ, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h01, h11, halt, hff f₀ f₁, hff f₁ f₀, map_zero, LinearMap.zero_apply] at this
      linear_combination this
    have c11 : X 1 1 = 0 := by
      have := congrArg (fun v => B (b 0 : E) v) hX'
      simp only [hθ, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h00, h01, hb0b1, map_zero] at this
      linear_combination this
    have c10 : X 1 0 = 0 := by
      have := congrArg (fun v => B (b 1 : E) v) hX'
      simp only [hθ, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h10, h11, hb0b1, map_zero] at this
      linear_combination this
    rw [Matrix.eta_fin_two X, c00, c01, c10, c11]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdimM : Module.finrank K (Mat2 K) = 4 := by
    rw [Module.finrank_matrix]
    simp
  have hsurj' : Function.Surjective θinv :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hdim, hdimM])).mp hθinj
  let e : Mat2 K ≃ₗ[K] E := LinearEquiv.ofBijective θinv ⟨hθinj, hsurj'⟩
  refine ⟨e.symm, fun x => ?_⟩
  obtain ⟨X, rfl⟩ := e.surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact (hθQ X).symm

theorem exists_psi {S : Subgroup G} {K : Type} [Field K] [Finite K] {n : ℕ}
    (hS : QuotSat S Q (IsSLModel 2 n)) (hK : Nat.card K = n) :
    ∃ ψ : ↥S →* SL(2, K), Function.Surjective ψ ∧ ∀ m : ↥S, ψ m = 1 ↔ (m : G) ∈ Q := by
  obtain ⟨hN, K', hfld, hfin, hcard, ⟨e⟩⟩ := hS
  haveI := hN
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  have hKK : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hcard]
  let ι : K' ≃+* K := FiniteField.ringEquivOfCardEq hKK
  let Φ : ↥S ⧸ Q.subgroupOf S ≃* SL(2, K') :=
    e.trans (specialLinearGroupEquivStatedSL 2 K').symm
  refine ⟨((D2.slCongr ι).toMonoidHom).comp
    (Φ.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf S))), ?_, ?_⟩
  · exact (D2.slCongr ι).surjective.comp (Φ.surjective.comp (QuotientGroup.mk'_surjective _))
  · intro m
    show (D2.slCongr ι) (Φ (QuotientGroup.mk m)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]

@[expose] def conjLinHom {K E F : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F]
    [Module K F] (Θ : E ≃ₗ[K] F) : (E ≃ₗ[K] E) →* (F ≃ₗ[K] F) where
  toFun T := Θ.symm.trans (T.trans Θ)
  map_one' := LinearEquiv.ext fun x => by simp
  map_mul' S T := LinearEquiv.ext fun x => by simp

theorem conjLinHom_apply {K E F : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F]
    [Module K F] (Θ : E ≃ₗ[K] F) (T : E ≃ₗ[K] E) (x : F) : conjLinHom Θ T x = Θ (T (Θ.symm x)) :=
  rfl

theorem exists_pair_homs {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    (δ : ↥(D2.detIsom K) →* Multiplicative (ZMod 2))
    (hδ : ∀ T : ↥(D2.detIsom K), δ T = 1 ↔ (T : Mat2 K ≃ₗ[K] Mat2 K) ∈ D2.pairGroup K)
    {S : Type*} [Group S] {E : Type*} [AddCommGroup E] [Module K E] (Θ : E ≃ₗ[K] Mat2 K)
    (φ : S →* (E ≃ₗ[K] E)) (hiso : ∀ m e, (Θ (φ m e)).det = (Θ e).det)
    (ψ : S →* SL(2, K)) (hψs : Function.Surjective ψ) (hker : ∀ m, ψ m = 1 → φ m = 1) :
    ∃ p₁ p₂ : S →* SL(2, K), ∀ m e,
      Θ (φ m e) = (p₁ m : Mat2 K) * Θ e * (p₂ m : Mat2 K)ᵀ := by
  classical
  let fΘ : S →* ↥(D2.detIsom K) :=
    ((conjLinHom Θ).comp φ).codRestrict (D2.detIsom K) (fun m X => by
      show (Θ (φ m (Θ.symm X))).det = X.det
      rw [hiso, LinearEquiv.apply_symm_apply])
  let f : S →* Multiplicative (ZMod 2) := δ.comp fΘ
  have hf1 : ∀ m, φ m = 1 → f m = 1 := fun m h => by
    show δ (fΘ m) = 1
    have : fΘ m = 1 := by
      apply Subtype.ext
      show conjLinHom Θ (φ m) = 1
      rw [h, map_one]
    rw [this, map_one]
  have hcomm : commutator S ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hmap : (commutator S).map ψ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hψs,
      ← commutator_def, D2.sl2_commutator_eq_top h4]
  have hf : ∀ m, f m = 1 := fun m => by
    have h1 : ψ m ∈ (commutator S).map ψ := by rw [hmap]; trivial
    obtain ⟨c, hc, hcm⟩ := Subgroup.mem_map.mp h1
    have h2 : ψ (c⁻¹ * m) = 1 := by rw [map_mul, map_inv, hcm, inv_mul_cancel]
    have h3 : f (c⁻¹ * m) = 1 := hf1 _ (hker _ h2)
    have h4' : f c = 1 := MonoidHom.mem_ker.mp (hcomm hc)
    have : f m = f c * f (c⁻¹ * m) := by rw [← map_mul, mul_inv_cancel_left]
    rw [this, h3, h4', mul_one]
  have hpair : ∀ m, ∃ g h : SL(2, K), ∀ e, Θ (φ m e) =
      (g : Mat2 K) * Θ e * (h : Mat2 K)ᵀ := by
    intro m
    have h1 : δ (fΘ m) = 1 := hf m
    obtain ⟨g, h, hgh⟩ := (hδ _).mp h1
    refine ⟨g, h, fun e => ?_⟩
    have := hgh (Θ e)
    rwa [show (fΘ m : Mat2 K ≃ₗ[K] Mat2 K) (Θ e) = Θ (φ m e) by
      show conjLinHom Θ (φ m) (Θ e) = _
      rw [conjLinHom_apply, LinearEquiv.symm_apply_apply]] at this
  choose p₁ p₂ hp using hpair
  have hmul : ∀ a b, p₁ (a * b) = p₁ a * p₁ b ∧ p₂ (a * b) = p₂ a * p₂ b := by
    intro a b
    apply D2.pair_unique
    intro X
    obtain ⟨e, rfl⟩ := Θ.surjective X
    have h1 := hp (a * b) e
    have h2 : Θ (φ (a * b) e) = (p₁ a : Mat2 K) * (p₁ b : Mat2 K) * Θ e *
        ((p₂ a : Mat2 K) * (p₂ b : Mat2 K))ᵀ := by
      rw [map_mul, LinearEquiv.mul_apply, hp a, hp b]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [h1] at h2
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      using h2
  exact ⟨MonoidHom.mk' p₁ fun a b => (hmul a b).1, MonoidHom.mk' p₂ fun a b => (hmul a b).2,
    hp⟩

theorem autSL2 (K : Type) [Field K] [Finite K] [CharP K 2] (_ : 4 ≤ Nat.card K)
    (α : MulAut SL(2, K)) :
    ∃ (g : SL(2, K)) (σ : K ≃+* K), ∀ A : SL(2, K), α A = g * D2.slMap σ A * g⁻¹ := by
  obtain ⟨M, σ, h⟩ := CFSG.RankThree.PartOne.KCRootAxis.exists_conj_mul_slFieldAut α
  refine ⟨M, σ, fun A => ?_⟩
  rw [h]
  rfl

theorem kernel_dichotomy {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {S : Type*} [Group S] (ψ : S →* SL(2, K)) (hψs : Function.Surjective ψ)
    (p : S →* SL(2, K)) (hp : ∀ m, ψ m = 1 → p m = 1) :
    (∀ m, p m = 1) ∨ (∀ m, p m = 1 → ψ m = 1) := by
  haveI : (p.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψs
  rcases D2.sl2_normal_eq_bot_or_top h4 (p.ker.map ψ) with h | h
  · right
    intro m hm
    have h1 : ψ m ∈ p.ker.map ψ := Subgroup.mem_map_of_mem ψ (MonoidHom.mem_ker.mpr hm)
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  · left
    intro m
    have h1 : ψ m ∈ p.ker.map ψ := by rw [h]; trivial
    obtain ⟨n, hn, hnm⟩ := Subgroup.mem_map.mp h1
    have h2 : ψ (n⁻¹ * m) = 1 := by rw [map_mul, map_inv, hnm, inv_mul_cancel]
    have h3 : p (n⁻¹ * m) = 1 := hp _ h2
    have h4' : p n = 1 := MonoidHom.mem_ker.mp hn
    have : p m = p n * p (n⁻¹ * m) := by rw [← map_mul, mul_inv_cancel_left]
    rw [this, h3, h4', mul_one]

theorem twist_of_pair {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {S : Type*} [Group S] {E : Type*} [AddCommGroup E] [Module K E]
    (Θ : E ≃ₗ[K] Mat2 K) (φ : S →* (E ≃ₗ[K] E)) (ψ : S →* SL(2, K))
    (hψs : Function.Surjective ψ) (p₁ p₂ : S →* SL(2, K))
    (hp : ∀ m e, Θ (φ m e) = (p₁ m : Mat2 K) * Θ e * (p₂ m : Mat2 K)ᵀ)
    (h₁ : ∀ m, ψ m = 1 ↔ p₁ m = 1) (h₂ : ∀ m, ψ m = 1 ↔ p₂ m = 1) :
    ∃ (Θ' : E ≃ₗ[K] Mat2 K) (σ : K ≃+* K) (p : S →* SL(2, K)),
      (∀ e, (Θ' e).det = (Θ e).det) ∧ Function.Surjective p ∧ (∀ m, p m = 1 ↔ ψ m = 1) ∧
      ∀ m e, Θ' (φ m e) = D2.twEquiv σ (p m) (Θ' e) := by
  classical
  let β₁ : SL(2, K) →* SL(2, K) :=
    MonoidHom.liftOfRightInverse ψ (Function.surjInv hψs) (Function.rightInverse_surjInv hψs)
      ⟨p₁, fun m hm => (h₁ m).mp (MonoidHom.mem_ker.mp hm)⟩
  let β₂ : SL(2, K) →* SL(2, K) :=
    MonoidHom.liftOfRightInverse ψ (Function.surjInv hψs) (Function.rightInverse_surjInv hψs)
      ⟨p₂, fun m hm => (h₂ m).mp (MonoidHom.mem_ker.mp hm)⟩
  have hβ₁ : ∀ m, β₁ (ψ m) = p₁ m := fun m =>
    MonoidHom.liftOfRightInverse_comp_apply ψ (Function.surjInv hψs)
      (Function.rightInverse_surjInv hψs) ⟨p₁, fun m hm => (h₁ m).mp (MonoidHom.mem_ker.mp hm)⟩ m
  have hβ₂ : ∀ m, β₂ (ψ m) = p₂ m := fun m =>
    MonoidHom.liftOfRightInverse_comp_apply ψ (Function.surjInv hψs)
      (Function.rightInverse_surjInv hψs) ⟨p₂, fun m hm => (h₂ m).mp (MonoidHom.mem_ker.mp hm)⟩ m
  haveI : Finite SL(2, K) := Finite.of_injective (fun g : SL(2, K) => (g : Mat2 K))
    Subtype.val_injective
  have hinj : ∀ (β : SL(2, K) →* SL(2, K)) (p : S →* SL(2, K)), (∀ m, β (ψ m) = p m) →
      (∀ m, ψ m = 1 ↔ p m = 1) → Function.Injective β := by
    intro β p hβ hker
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨m, rfl⟩ := hψs g
    rw [hβ] at hg
    exact (hker m).mpr hg
  have hbij : ∀ (β : SL(2, K) →* SL(2, K)) (p : S →* SL(2, K)), (∀ m, β (ψ m) = p m) →
      (∀ m, ψ m = 1 ↔ p m = 1) → Function.Bijective β := fun β p hβ hker =>
    ⟨hinj β p hβ hker, Finite.injective_iff_surjective.mp (hinj β p hβ hker)⟩
  let e₁ : SL(2, K) ≃* SL(2, K) := MulEquiv.ofBijective β₁ (hbij β₁ p₁ hβ₁ h₁)
  let e₂ : SL(2, K) ≃* SL(2, K) := MulEquiv.ofBijective β₂ (hbij β₂ p₂ hβ₂ h₂)
  obtain ⟨c, σ, hcσ⟩ := autSL2 K h4 (e₁.symm.trans e₂)
  have hp₂ : ∀ m, p₂ m = c * D2.slMap σ (p₁ m) * c⁻¹ := by
    intro m
    have := hcσ (p₁ m)
    rw [← hβ₁, ← hβ₂] at *
    have e : (e₁.symm.trans e₂) (β₁ (ψ m)) = β₂ (ψ m) := by
      show e₂ (e₁.symm (e₁ (ψ m))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    rw [e] at this
    rw [this]
  refine ⟨Θ.trans (D2.pairEquiv 1 c⁻¹), σ, p₁, fun e => ?_, ?_, fun m => (h₁ m).symm, ?_⟩
  · show (D2.pairEquiv 1 c⁻¹ (Θ e)).det = _
    exact D2.det_pairEquiv _ _ _
  · intro g
    obtain ⟨m, hm⟩ := (hbij β₁ p₁ hβ₁ h₁).2 g
    obtain ⟨n, rfl⟩ := hψs m
    exact ⟨n, by rw [← hβ₁, hm]⟩
  · intro m e
    show D2.pairEquiv 1 c⁻¹ (Θ (φ m e)) = D2.twEquiv σ (p₁ m) (D2.pairEquiv 1 c⁻¹ (Θ e))
    rw [hp m e, D2.twEquiv_apply]
    simp only [D2.pairEquiv_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
      Matrix.transpose_mul, hp₂ m, Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hcc : ((c : Mat2 K))ᵀ * (((c⁻¹ : SL(2, K)) : Mat2 K))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, D2.sl_inv_mul, Matrix.transpose_one]
    rw [hcc, Matrix.mul_one]

theorem range_sub_one_of_leftMul {K : Type} [Field K] [CharP K 2] {E : Type*} [AddCommGroup E]
    [Module K E] (Θ : E ≃ₗ[K] Mat2 K) (T : E ≃ₗ[K] E) {g : SL(2, K)} (hg1 : g ≠ 1)
    (hg2 : g * g = 1) (hT : ∀ e, Θ (T e) = (g : Mat2 K) * Θ e) :
    Module.finrank K (LinearMap.range ((T : E →ₗ[K] E) - 1)) = 2 ∧
      ∀ v ∈ LinearMap.range ((T : E →ₗ[K] E) - 1), (Θ v).det = 0 := by
  have hmap : (LinearMap.range ((T : E →ₗ[K] E) - 1)).map (Θ : E →ₗ[K] Mat2 K) =
      LinearMap.range (D2.pairLin ((g : Mat2 K) - 1) 1) := by
    ext Y
    constructor
    · rintro ⟨v, ⟨e, rfl⟩, rfl⟩
      refine ⟨Θ e, ?_⟩
      simp [D2.pairLin_apply, hT, Matrix.sub_mul]
    · rintro ⟨X, rfl⟩
      obtain ⟨e, rfl⟩ := Θ.surjective X
      exact ⟨T e - e, ⟨e, by simp⟩, by simp [D2.pairLin_apply, hT, Matrix.sub_mul]⟩
  obtain ⟨h1, h2⟩ := D2.range_leftMul hg1 hg2
  refine ⟨?_, ?_⟩
  · rw [← LinearEquiv.finrank_map_eq Θ (LinearMap.range ((T : E →ₗ[K] E) - 1)), hmap]
    exact h1
  · intro v hv
    apply h2
    rw [← hmap]
    exact Submodule.mem_map_of_mem hv

section D2G

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem no_trivial_second_factor (hc : Ctx M Q Z B) (hw : Width Q Z 2)
    (hno : NoA2 Q Z (LB M Q B)) (hD : GlobalModelData M Q Z γ M₀)
    (φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    (Θ : M₀.E ≃ₗ[K] Mat2 K) (hΘ : ∀ e, (Θ e).det = M₀.Qf e)
    (p₁ p₂ : ↥(Lgen M (LB M Q B)) →* SL(2, K))
    (hp : ∀ m e, Θ (φS m e) = (p₁ m : Mat2 K) * Θ e * (p₂ m : Mat2 K)ᵀ)
    (hp₂ : ∀ m, p₂ m = 1) (hp₁ : ∀ m : ↥(Lgen M (LB M Q B)), p₁ m = 1 → (m : G) ∈ Q)
    (hQ1 : ∀ m : ↥(Lgen M (LB M Q B)), (m : G) ∈ Q → p₁ m = 1) : False := by
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hcard : Nat.card K = Nat.card Z := hD.card
  have hK : 1 < Nat.card K := by omega
  obtain ⟨a, haL, haQ⟩ : ∃ a ∈ LB M Q B, a ∉ Q := by
    by_contra hcon
    push Not at hcon
    have hle : LB M Q B ≤ Q := fun a ha => hcon a ha
    have h1 := hc.card_LB_ge hw (by norm_num)
    have h2 : Nat.card (LB M Q B) ≤ Nat.card Q := Subgroup.card_le_of_le hle
    have h3 : 0 < Nat.card Q := Nat.card_pos
    have h4 : Nat.card Z ^ (2 - 1) = Nat.card Z := by norm_num
    rw [h4] at h1
    nlinarith
  have haM : a ∈ M := hc.LB_le_M haL
  have haS : a ∈ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B) haL
  set a' : ↥(Lgen M (LB M Q B)) := ⟨a, haS⟩ with ha'def
  have ha2Q : a ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB haL
  have hg1 : p₁ a' ≠ 1 := fun h => haQ (hp₁ a' h)
  have hg2 : p₁ a' * p₁ a' = 1 := by
    rw [← map_mul]
    apply hQ1
    show a * a ∈ Q
    rw [← sq]
    exact ha2Q
  have hT : ∀ e, Θ (φS a' e) = ((p₁ a' : SL(2, K)) : Mat2 K) * Θ e := by
    intro e
    rw [hp a' e, hp₂ a']
    simp
  obtain ⟨hfin, hsing⟩ := range_sub_one_of_leftMul Θ (φS a') hg1 hg2 hT
  have hA2 : IsA2 Q Z a := by
    refine (isA2_iff M₀ hD.reg hcard hK (a := a) (φS a')
      (fun x hx => conj_mem_Q hc.hyp haM hx)
      (fun x hx => by
        have := conj_mem_Q hc.hyp (M.inv_mem haM) hx
        simpa using this)
      (fun x hx => hφπ a' x hx)).mpr ⟨haQ, ha2Q, hfin, fun v hv => ?_⟩
    rw [← hΘ]
    exact hsing v hv
  exact hno a haL hA2

structure D2Data {S : Subgroup G} (Q Z : Subgroup G) (M₀ : Tim79.QuadModel Q Z K γ)
    (φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)) where
  Θ : M₀.E ≃ₗ[K] Mat2 K
  σ : K ≃+* K
  p : ↥S →* SL(2, K)
  det_eq : ∀ e, (Θ e).det = M₀.Qf e
  surj : Function.Surjective p
  ker_iff : ∀ m : ↥S, p m = 1 ↔ (m : G) ∈ Q
  act : ∀ (m : ↥S) e, Θ (φS m e) = D2.twEquiv σ (p m) (Θ e)

theorem exists_d2Data
    (hc : Ctx M Q Z B) (hw : Width Q Z 2) (hno : NoA2 Q Z (LB M Q B))
    (hcase : QuotSat (Lgen M (LB M Q B)) Q (IsSLModel 2 (Nat.card Z)))
    (hD : GlobalModelData M Q Z γ M₀)
    (φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    (hφker : ∀ m : ↥(Lgen M (LB M Q B)), φS m = 1 ↔ (m : G) ∈ Q)
    (hφQ : ∀ m e, M₀.Qf (φS m e) = M₀.Qf e)
    (Θ₀ : M₀.E ≃ₗ[K] Mat2 K) (hΘ₀ : ∀ e, (Θ₀ e).det = M₀.Qf e) :
    Nonempty (D2Data Q Z M₀ φS) := by
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hK4 : 4 ≤ Nat.card K := by rw [hD.card]; exact hq4
  obtain ⟨ψ, hψs, hψk⟩ := exists_psi hcase hD.card
  obtain ⟨δ, hδ⟩ := D2.exists_dicksonHom K
  have hiso : ∀ m e, (Θ₀ (φS m e)).det = (Θ₀ e).det := fun m e => by
    rw [hΘ₀, hΘ₀, hφQ]
  obtain ⟨p₁, p₂, hp⟩ := exists_pair_homs hK4 δ hδ Θ₀ φS hiso ψ hψs
    (fun m hm => (hφker m).mpr ((hψk m).mp hm))
  have hQ1 : ∀ m : ↥(Lgen M (LB M Q B)), (m : G) ∈ Q → p₁ m = 1 ∧ p₂ m = 1 := by
    intro m hm
    have h1 : φS m = 1 := (hφker m).mpr hm
    apply D2.pair_unique (g := p₁ m) (g' := 1) (h := p₂ m) (h' := 1)
    intro X
    obtain ⟨e, rfl⟩ := Θ₀.surjective X
    rw [← hp m e, h1]
    simp
  have hker₁ : ∀ m, ψ m = 1 → p₁ m = 1 := fun m hm => (hQ1 m ((hψk m).mp hm)).1
  have hker₂ : ∀ m, ψ m = 1 → p₂ m = 1 := fun m hm => (hQ1 m ((hψk m).mp hm)).2
  have hfin : ∀ (m : ↥(Lgen M (LB M Q B))) , ψ m = 1 ↔ (m : G) ∈ Q := hψk
  have hswap : ∀ (p₁' p₂' : ↥(Lgen M (LB M Q B)) →* SL(2, K))
      (Θ' : M₀.E ≃ₗ[K] Mat2 K), (∀ e, (Θ' e).det = M₀.Qf e) →
      (∀ m e, Θ' (φS m e) = (p₁' m : Mat2 K) * Θ' e * (p₂' m : Mat2 K)ᵀ) →
      (∀ m, p₂' m = 1) → (∀ m : ↥(Lgen M (LB M Q B)), (m : G) ∈ Q → p₁' m = 1) →
      (∀ m : ↥(Lgen M (LB M Q B)), p₁' m = 1 → (m : G) ∈ Q) → False := fun p₁' p₂' Θ' hΘ' hp' hp₂'
        hQ' hk' =>
    no_trivial_second_factor hc hw hno hD φS hφπ Θ' hΘ' p₁' p₂' hp' hp₂' hk' hQ'
  rcases kernel_dichotomy hK4 ψ hψs p₁ hker₁ with h1 | h1 <;>
    rcases kernel_dichotomy hK4 ψ hψs p₂ hker₂ with h2 | h2
  ·
    exfalso
    have hall : ∀ m : ↥(Lgen M (LB M Q B)), ψ m = 1 := by
      intro m
      rw [hψk m, ← hφker m]
      refine LinearEquiv.ext fun e => ?_
      apply Θ₀.injective
      rw [hp m e, h1 m, h2 m]
      simp
    obtain ⟨m, hm⟩ := hψs (D2.uSL 1)
    have := hall m
    rw [hm] at this
    have h3 := congrArg (fun A : SL(2, K) => (A : Mat2 K) 0 1) this
    simp at h3
  ·
    exfalso
    refine hswap p₂ p₁ (Θ₀.trans (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) K K)) ?_ ?_ h1
      (fun m hm => (hQ1 m hm).2) (fun m hm => h2 m hm |> (hψk m).mp)
    · intro e
      show ((Θ₀ e)ᵀ).det = _
      rw [Matrix.det_transpose, hΘ₀]
    · intro m e
      show (Θ₀ (φS m e))ᵀ = _
      rw [hp m e]
      show ((p₁ m : Mat2 K) * Θ₀ e * (p₂ m : Mat2 K)ᵀ)ᵀ =
        (p₂ m : Mat2 K) * (Θ₀ e)ᵀ * (p₁ m : Mat2 K)ᵀ
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  ·
    exfalso
    exact hswap p₁ p₂ Θ₀ hΘ₀ hp h2 (fun m hm => (hQ1 m hm).1) (fun m hm => h1 m hm |> (hψk m).mp)
  ·
    obtain ⟨Θ', σ, p, hdet, hps, hpk, hact⟩ := twist_of_pair hK4 Θ₀ φS ψ hψs p₁ p₂ hp
      (fun m => ⟨hker₁ m, h1 m⟩) (fun m => ⟨hker₂ m, h2 m⟩)
    refine ⟨⟨Θ', σ, p, fun e => by rw [hdet, hΘ₀], hps, fun m => ?_, hact⟩⟩
    rw [hpk, hψk]

variable {S : Subgroup G} {φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)}

theorem D2Data.lemmaS (D : D2Data Q Z M₀ φS) {t : ↥S} (htQ : (t : G) ∉ Q)
    (ht2 : (t : G) ^ 2 ∈ Q) :
    ∃ c : Fin 2 → K, c ≠ 0 ∧ ∀ e, φS t e = e → M₀.Qf e = 0 →
      ∃ μ : K, e = μ • D.Θ.symm (D2.tw D.σ c) := by
  have hp1 : D.p t ≠ 1 := fun h => htQ ((D.ker_iff t).mp h)
  have hp2 : D.p t * D.p t = 1 := by
    rw [← map_mul]
    refine (D.ker_iff _).mpr ?_
    show (t : G) * (t : G) ∈ Q
    rwa [← sq]
  obtain ⟨c, hc0, -, hX⟩ := D2.lemmaS D.σ hp1 hp2
  refine ⟨c, hc0, fun e he hq => ?_⟩
  have h1 : D2.twEquiv D.σ (D.p t) (D.Θ e) = D.Θ e := by rw [← D.act, he]
  have h2 : (D.Θ e).det = 0 := by rw [D.det_eq, hq]
  obtain ⟨μ, hμ⟩ := hX _ h1 h2
  refine ⟨μ, D.Θ.injective ?_⟩
  rw [hμ, map_smul, LinearEquiv.apply_symm_apply]

theorem D2Data.B_eq_polar (D : D2Data Q Z M₀ φS) (e f : M₀.E) :
    M₀.B e f = D2.polar (D.Θ e) (D.Θ f) := by
  have h1 := M₀.Qf_add e f
  have h2 := D2.det_add (D.Θ e) (D.Θ f)
  rw [← map_add, D.det_eq, D.det_eq, D.det_eq] at h2
  linear_combination h2 - h1

theorem D2Data.B_tw_ne_zero (D : D2Data Q Z M₀ φS) {c c' : Fin 2 → K}
    (h : c 0 * c' 1 - c 1 * c' 0 ≠ 0) :
    M₀.B (D.Θ.symm (D2.tw D.σ c)) (D.Θ.symm (D2.tw D.σ c')) ≠ 0 := by
  rw [D.B_eq_polar, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact D2.polar_tw_ne_zero D.σ h

theorem D2Data.card_le_of_pGroup (D : D2Data Q Z M₀ φS) {P : Subgroup G} (hPS : P ≤ S)
    (hP2 : IsPGroup 2 P) (hPQ : P ⊓ Q = ⊥) : Nat.card P ≤ Nat.card K := by
  let f : ↥P →* SL(2, K) := D.p.comp (Subgroup.inclusion hPS)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ((Subgroup.inclusion hPS x : ↥S) : G) ∈ Q := (D.ker_iff _).mp hx
    have h2 : (x : G) ∈ P ⊓ Q := ⟨x.2, h1⟩
    rw [hPQ, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have h3 : Nat.card P = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [h3]
  exact D2.card_le_of_isPGroup_sl2 (hP2.of_surjective f.rangeRestrict f.rangeRestrict_surjective)

theorem D2Data.card_le_two_mul (D : D2Data Q Z M₀ φS)
    (δ : ↥(D2.detIsom K) →* Multiplicative (ZMod 2))
    (hδ : ∀ T : ↥(D2.detIsom K), δ T = 1 ↔ (T : Mat2 K ≃ₗ[K] Mat2 K) ∈ D2.pairGroup K)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) (hS : S ≤ H0 M Z)
    (hφS : ∀ m : ↥S, φS m = φ ⟨m, hS m.2⟩)
    (hφker : ∀ m : ↥(H0 M Z), φ m = 1 → (m : G) ∈ Q) (hQS : Q ≤ S)
    (hφQ : ∀ (m : ↥(H0 M Z)) e, M₀.Qf (φ m e) = M₀.Qf e)
    (hnorm : ∀ m ∈ H0 M Z, ∀ s ∈ S, m * s * m⁻¹ ∈ S)
    {P : Subgroup G} (hP : P ≤ H0 M Z) : Nat.card P ≤ 2 * Nat.card ↥(P ⊓ S) := by
  classical
  let fΘ : ↥(H0 M Z) →* ↥(D2.detIsom K) :=
    ((conjLinHom D.Θ).comp φ).codRestrict (D2.detIsom K) (fun m X => by
      show (D.Θ (φ m (D.Θ.symm X))).det = X.det
      rw [D.det_eq, hφQ, ← D.det_eq, LinearEquiv.apply_symm_apply])
  let f : ↥(H0 M Z) →* Multiplicative (ZMod 2) := δ.comp fΘ
  have hmemS : ∀ m : ↥(H0 M Z), f m = 1 → (m : G) ∈ S := by
    intro m hm
    obtain ⟨g, h, hgh⟩ := (hδ _).mp hm
    have hpe : ∀ Y : Mat2 K, D2.pairEquiv g h Y = D.Θ (φ m (D.Θ.symm Y)) := by
      intro Y
      rw [D2.pairEquiv_apply, ← hgh Y]
      rfl
    have hN : ∀ s : SL(2, K), ∃ s' : SL(2, K), ∀ X : Mat2 K,
        D2.pairEquiv g h (D2.twEquiv D.σ s X) = D2.twEquiv D.σ s' (D2.pairEquiv g h X) := by
      intro s
      obtain ⟨m₁, rfl⟩ := D.surj s
      let m₂ : ↥S := ⟨(m : G) * (m₁ : G) * (m : G)⁻¹, hnorm m m.2 m₁ m₁.2⟩
      refine ⟨D.p m₂, fun X => ?_⟩
      obtain ⟨e, rfl⟩ := D.Θ.surjective X
      have hcomm : (⟨m₂.1, hS m₂.2⟩ : ↥(H0 M Z)) * m = m * ⟨m₁.1, hS m₁.2⟩ :=
        Subtype.ext (by show (m : G) * (m₁ : G) * (m : G)⁻¹ * (m : G) = (m : G) * (m₁ : G); group)
      have h1 : φ m (φS m₁ e) = φS m₂ (φ m e) := by
        rw [hφS m₁, hφS m₂]
        have := LinearEquiv.congr_fun (congrArg φ hcomm) e
        rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
        exact this.symm
      rw [← D.act m₁ e, hpe, hpe, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
        ← D.act m₂, h1]
    have hh : h = D2.slMap D.σ g := D2.normalizer_pair D.σ hN
    obtain ⟨s₀, hs₀⟩ := D.surj g
    have hφm : φ m = φ ⟨s₀.1, hS s₀.2⟩ := by
      refine LinearEquiv.ext fun e => D.Θ.injective ?_
      have h1 := hpe (D.Θ e)
      rw [LinearEquiv.symm_apply_apply, hh] at h1
      rw [← h1, ← hφS, D.act, hs₀]
      rfl
    have hQm : φ (m * ⟨s₀.1, hS s₀.2⟩⁻¹) = 1 := by rw [map_mul, map_inv, hφm, mul_inv_cancel]
    have hQmem := hφker _ hQm
    have : (m : G) = (m : G) * (s₀ : G)⁻¹ * (s₀ : G) := by group
    rw [this]
    exact S.mul_mem (hQS hQmem) s₀.2
  let g' : ↥P →* Multiplicative (ZMod 2) := f.comp (Subgroup.inclusion hP)
  have h1 : Nat.card g'.ker * g'.ker.index = Nat.card P := Subgroup.card_mul_index g'.ker
  have h2 : g'.ker.index = Nat.card g'.range := Subgroup.index_ker g'
  have h3 : Nat.card g'.range ≤ 2 := by
    refine (Subgroup.card_le_card_group g'.range).trans ?_
    rw [Nat.card_congr Multiplicative.toAdd]
    simp [Nat.card_zmod]
  have h4 : Nat.card g'.ker ≤ Nat.card ↥(P ⊓ S) := by
    refine Nat.card_le_card_of_injective
      (fun x : g'.ker => (⟨(x : ↥P).1, (x : ↥P).2, hmemS _ (MonoidHom.mem_ker.mp x.2)⟩ :
        ↥(P ⊓ S))) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card P = Nat.card g'.ker * g'.ker.index := h1.symm
    _ = Nat.card g'.ker * Nat.card g'.range := by rw [h2]
    _ ≤ Nat.card ↥(P ⊓ S) * 2 := Nat.mul_le_mul h4 h3
    _ = 2 * Nat.card ↥(P ⊓ S) := by ring

theorem D2Data.exists_ctx_line (D : D2Data Q Z M₀ φS) (hc : Ctx M Q Z B) (hSM : S ≤ M)
    (hφπ : ∀ (m : ↥S) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    {c₁ : Fin 2 → K} (hc₁ : c₁ ≠ 0)
    (hB : ∀ v, v ∈ M₀.img B ↔ ∃ μ : K, v = μ • D.Θ.symm (D2.tw D.σ c₁))
    {c : Fin 2 → K} (hc0 : c ≠ 0) :
    ∃ A : Subgroup G, Ctx M Q Z A ∧
      ∀ v, v ∈ M₀.img A ↔ ∃ μ : K, v = μ • D.Θ.symm (D2.tw D.σ c) := by
  obtain ⟨g, hg⟩ := D2.exists_sl_mulVec_eq hc₁ hc0
  obtain ⟨m, hm⟩ := D.surj g
  have hmM : (m : G) ∈ M := hSM m.2
  have hkey : ∀ μ : K, φS m (μ • D.Θ.symm (D2.tw D.σ c₁)) = μ • D.Θ.symm (D2.tw D.σ c) := by
    intro μ
    apply D.Θ.injective
    rw [D.act]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    rw [hm, D2.twEquiv_tw, hg]
  refine ⟨conjSubgroup m B, hc.conj_of_mem hmM, fun v => ?_⟩
  constructor
  · rintro ⟨x, hxA, hxQ, rfl⟩
    have hy : (m : G)⁻¹ * x * (m : G) ∈ B := mem_conjSubgroup.mp hxA
    have hyQ : (m : G)⁻¹ * x * (m : G) ∈ Q := hc.le hy
    have hπ := hφπ m _ hyQ
    rw [show (m : G) * ((m : G)⁻¹ * x * (m : G)) * (m : G)⁻¹ = x by group] at hπ
    obtain ⟨μ, hμ⟩ := (hB _).mp (M₀.pi_mem_img hy hyQ)
    exact ⟨μ, by rw [hπ, hμ, hkey]⟩
  · rintro ⟨μ, rfl⟩
    obtain ⟨y, hyB, hyQ, hyπ⟩ := (hB (μ • D.Θ.symm (D2.tw D.σ c₁))).mpr ⟨μ, rfl⟩
    refine ⟨(m : G) * y * (m : G)⁻¹, ?_, conj_mem_Q hc.hyp hmM hyQ, ?_⟩
    · rw [mem_conjSubgroup, show (m : G)⁻¹ * ((m : G) * y * (m : G)⁻¹) * (m : G) = y by group]
      exact hyB
    · rw [hφπ m y hyQ, hyπ, hkey]

end D2G

end CFSG.RankThree.GF2n.Smith81
