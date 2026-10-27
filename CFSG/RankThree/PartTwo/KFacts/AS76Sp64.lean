module

public import CFSG.RankThree.PartTwo.KFacts.AS76Tools
public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeSp64
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpDescent

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec21.AS76.Sp64

open CFSG.RankThree.PartTwo.Sec21.AS76

open Module Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

section RTrans

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def rtv (F : ReflForm K V) (N : Module.End K V) (u : V) : Module.End K V where
  toFun v := F.β (N u) v • u + F.β u v • N u
  map_add' v w := by rw [F.add_right, F.add_right, add_smul, add_smul]; abel
  map_smul' c v := by
    rw [F.smul_right, F.smul_right, smul_add, smul_smul, smul_smul, RingHom.id_apply]

theorem rtv_apply (F : ReflForm K V) (N : Module.End K V) (u v : V) :
    rtv F N u v = F.β (N u) v • u + F.β u v • N u := rfl

variable (F : ReflForm K V) (N : Module.End K V)

theorem rtv_mul_self (hs : ∀ a b, F.β a b = F.β b a) (halt : ∀ a, F.β a a = 0) {u : V}
    (hu : F.β u (N u) = 0) : rtv F N u * rtv F N u = 0 := by
  have hNuu : F.β (N u) u = 0 := by rw [hs, hu]
  ext v
  simp only [Module.End.mul_apply, rtv_apply, F.add_right, F.smul_right, hNuu, halt, hu,
    mul_zero, add_zero, zero_smul, LinearMap.zero_apply]

theorem rtv_mul_rtv_mul_rtv (hs : ∀ a b, F.β a b = F.β b a)
    (hadj : ∀ a b, F.β (N a) b = F.β a (N b)) (hNN : ∀ a, N (N a) = 0) {u u' : V}
    (h1 : F.β u (N u') = 1) (h0 : F.β u u' = 0) :
    rtv F N u * rtv F N u' * rtv F N u = rtv F N u := by
  have hNuu' : F.β (N u) u' = 1 := by rw [hadj, h1]
  have hu'Nu : F.β u' (N u) = 1 := by rw [hs, hNuu']
  have hNu'u : F.β (N u') u = 1 := by rw [hadj, hu'Nu]
  have hu'u : F.β u' u = 0 := by rw [hs, h0]
  have hNuNu' : F.β (N u) (N u') = 0 := by rw [hadj, hNN, F.β_zero_right]
  have hNu'Nu : F.β (N u') (N u) = 0 := by rw [hadj, hNN, F.β_zero_right]
  ext v
  simp only [Module.End.mul_apply, rtv_apply, F.add_right, F.smul_right, hNuu', hu'Nu, hNu'u,
    hu'u, hNuNu', hNu'Nu, h1, h0, mul_one, mul_zero, add_zero, zero_add]

theorem rtv_commute (hadj : ∀ a b, F.β (N a) b = F.β a (N b)) (hNN : ∀ a, N (N a) = 0)
    (u : V) : rtv F N u * N = N * rtv F N u := by
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply, rtv_apply, rtv_apply]
  have e1 : F.β (N u) (N v) = 0 := by rw [hadj, hNN, F.β_zero_right]
  rw [e1, ← hadj, zero_smul, zero_add, map_add, map_smul, map_smul, hNN, smul_zero, add_zero]

theorem rtv_isometry [CharP K 2] (hσ : ∀ c, F.σ c = c) (hs : ∀ a b, F.β a b = F.β b a)
    (halt : ∀ a, F.β a a = 0) {u : V} (hu : F.β u (N u) = 0) (v w : V) :
    F.β ((1 + rtv F N u) v) ((1 + rtv F N u) w) = F.β v w := by
  have hNuu : F.β (N u) u = 0 := by rw [hs, hu]
  simp only [LinearMap.add_apply, Module.End.one_apply, rtv_apply, F.add_left, F.add_right,
    F.smul_left, F.smul_right, hσ, halt, hu, hNuu, mul_zero, add_zero]
  rw [hs v u, hs v (N u)]
  linear_combination (F.β (N u) w * F.β u v + F.β (N u) v * F.β u w) *
    CharTwo.two_eq_zero (R := K)

theorem rtv_ne_zero (hadj : ∀ a b, F.β (N a) b = F.β a (N b)) {u u' : V}
    (h1 : F.β u (N u') = 1) (h0 : F.β u u' = 0) : rtv F N u ≠ 0 := by
  intro h
  have h2 := congrArg (fun T : Module.End K V => T u') h
  simp only [rtv_apply, hadj, h1, h0, one_smul, zero_smul, add_zero, LinearMap.zero_apply] at h2
  rw [h2, F.β_zero_left] at h1
  exact zero_ne_one h1

theorem exists_isometric_matrixUnits [Finite K] [CharP K 2] [FiniteDimensional K V] {r : ℕ}
    (hr : 3 ≤ r) (hV : finrank K V = 2 * r) (hσ : ∀ c, F.σ c = c)
    (hs : ∀ a b, F.β a b = F.β b a) (halt : ∀ a, F.β a a = 0)
    (hadj : ∀ a b, F.β (N a) b = F.β a (N b)) (hN : N * N = 0) :
    ∃ X X' : Module.End K V, X * X = 0 ∧ X' * X' = 0 ∧ X * X' * X = X ∧ X' * X * X' = X' ∧
      X * N = N * X ∧ X' * N = N * X' ∧ X ≠ 0 ∧
      (∀ v w, F.β ((1 + X) v) ((1 + X) w) = F.β v w) ∧
      (∀ v w, F.β ((1 + X') v) ((1 + X') w) = F.β v w) := by
  have hNN : ∀ a, N (N a) = 0 := fun a => by
    rw [← Module.End.mul_apply, hN, LinearMap.zero_apply]
  by_cases hA : ∃ e ∈ LinearMap.ker N, ∃ e₀ ∈ LinearMap.ker N, F.β e e₀ ≠ 0
  · obtain ⟨e, he, e₀, he₀, hee₀⟩ := hA
    set e' := (F.β e e₀)⁻¹ • e₀ with he'
    have hee' : F.β e e' = 1 := by rw [he', F.smul_right, inv_mul_cancel₀ hee₀]
    have he'e : F.β e' e = 1 := by rw [hs, hee']
    have hNe : N e = 0 := LinearMap.mem_ker.mp he
    have hNe' : N e' = 0 := by rw [he', map_smul, LinearMap.mem_ker.mp he₀, smul_zero]
    have hc : ∀ x : V, N x = 0 → tv F x * N = N * tv F x := fun x hx =>
      tv_commute F N hx fun v => by rw [← hadj, hx, F.β_zero_left]
    refine ⟨tv F e, tv F e', tv_mul_self F (halt e), tv_mul_self F (halt e'),
      tv_mul_tv_mul_tv F (by rw [hee', he'e, one_mul]),
      tv_mul_tv_mul_tv F (by rw [hee', he'e, one_mul]), hc e hNe, hc e' hNe', tv_ne_zero F hee',
      tv_isometry F hσ hs (halt e), tv_isometry F hσ hs (halt e')⟩
  · push Not at hA
    have hW : LinearMap.ker N ≤ F.perp (LinearMap.ker N) := fun v hv w hw => hA w hw v hv
    have h1 := F.finrank_perp (LinearMap.ker N)
    have h2 := Submodule.finrank_mono hW
    obtain ⟨H, hHmem, hHdim⟩ := exists_ker_sqrt (fun v => F.β v (N v))
      (fun a b => by
        rw [map_add, F.add_left, F.add_right, F.add_right, hs b (N a), hadj]
        linear_combination F.β a (N b) * CharTwo.two_eq_zero (R := K))
      (fun c v => by rw [map_smul, F.smul_left, F.smul_right, hσ]; ring)
    have h3 : finrank K H ≤ finrank K (H.map N) + finrank K (LinearMap.ker N) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (N.domRestrict H)
      rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
      have hk : finrank K ((LinearMap.ker N).comap H.subtype) ≤ finrank K (LinearMap.ker N) := by
        rw [← Submodule.finrank_map_subtype_eq H ((LinearMap.ker N).comap H.subtype)]
        exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
      omega
    obtain ⟨u, hu, u'₀, hu'₀, huu'₀⟩ := exists_eq_one F N H hHdim (by omega)
    have huN : F.β u (N u) = 0 := (hHmem u).mp hu
    have hu'₀N : F.β u'₀ (N u'₀) = 0 := (hHmem u'₀).mp hu'₀
    set u' := u'₀ + F.β u u'₀ • N u'₀ with hu'
    have hNu' : N u' = N u'₀ := by rw [hu', map_add, map_smul, hNN, smul_zero, add_zero]
    have h1' : F.β u (N u') = 1 := by rw [hNu', huu'₀]
    have h0 : F.β u u' = 0 := by
      rw [hu', F.add_right, F.smul_right, huu'₀, mul_one]
      linear_combination F.β u u'₀ * CharTwo.two_eq_zero (R := K)
    have hu'N : F.β u' (N u') = 0 := by
      rw [hNu', hu', F.add_left, F.smul_left, hu'₀N, halt, mul_zero, add_zero]
    have h1'' : F.β u' (N u) = 1 := by rw [← hadj, hs, h1']
    have h0' : F.β u' u = 0 := by rw [hs, h0]
    exact ⟨rtv F N u, rtv F N u', rtv_mul_self F N hs halt huN, rtv_mul_self F N hs halt hu'N,
      rtv_mul_rtv_mul_rtv F N hs hadj hNN h1' h0, rtv_mul_rtv_mul_rtv F N hs hadj hNN h1'' h0',
      rtv_commute F N hadj hNN u, rtv_commute F N hadj hNN u', rtv_ne_zero F N hadj h1' h0,
      rtv_isometry F N hσ hs halt huN, rtv_isometry F N hσ hs halt hu'N⟩

end RTrans

theorem spForm_comm {K : Type} [Field K] [CharP K 2] {r : ℕ} (u v : Fin r ⊕ Fin r → K) :
    (spForm r K).β u v = (spForm r K).β v u := by
  have h := spForm_self r K (u + v)
  rw [(spForm r K).add_left, (spForm r K).add_right, (spForm r K).add_right, spForm_self,
    spForm_self, zero_add, add_zero] at h
  linear_combination h - (spForm r K).β v u * CharTwo.two_eq_zero (R := K)

theorem invCentThree_Sp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r) :
    InvCentThree (StatedSp r K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro t ht
  set F := spForm r K with hF
  obtain ⟨T, hT⟩ : ∃ T, T = natRep (StatedSp r K) t := ⟨_, rfl⟩
  have hTT : T * T = 1 := by rw [hT, ← map_mul, ht, map_one]
  have hTTa : ∀ a, T (T a) = a := fun a => by
    rw [← Module.End.mul_apply, hTT, Module.End.one_apply]
  have hiso : ∀ a b, F.β (T a) (T b) = F.β a b := fun a b => by
    rw [hT]; exact isIsometric_natRep_statedSp r K t a b
  obtain ⟨N, hN⟩ : ∃ N : Module.End K (Fin r ⊕ Fin r → K), N = T - 1 := ⟨_, rfl⟩
  have h2 : (2 : Module.End K (Fin r ⊕ Fin r → K)) = 0 := end_two_eq_zero
  have hx : ∀ x : Module.End K (Fin r ⊕ Fin r → K), x + x = 0 := fun x => by
    rw [← two_mul, h2, zero_mul]
  have hNN : N * N = 0 := by
    rw [hN, sub_mul, mul_sub, mul_sub, hTT, mul_one, one_mul, one_mul]
    calc (1 : Module.End K (Fin r ⊕ Fin r → K)) - T - (T - 1) = (1 + 1) - (T + T) := by abel
      _ = 0 := by rw [hx, hx, sub_zero]
  have hadj : ∀ a b, F.β (N a) b = F.β a (N b) := by
    intro a b
    rw [hN, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      F.β_sub_left, F.β_sub_right]
    congr 1
    conv_lhs => rw [← hTTa b]
    rw [hiso]
  have hV : finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; ring
  obtain ⟨X, X', hX, hX', h1, h1', hc, hc', hX0, hiX, hiX'⟩ :=
    exists_isometric_matrixUnits F N hr hV (fun c => rfl) spForm_comm (spForm_self r K) hadj hNN
  obtain ⟨Y, hY⟩ : ∃ Y : Module.End K (Fin r ⊕ Fin r → K), Y = (1 + X) * (1 + X') := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry r K Y fun v w => by
    rw [hY, Module.End.mul_apply, Module.End.mul_apply, hiX, hiX']
  have hgY : natRep (StatedSp r K) g = Y := LinearMap.ext hg
  refine ⟨g, orderOf_eq_prime ?_ ?_, ?_⟩
  · apply natRep_injective (StatedSp r K)
    rw [map_pow, hgY, map_one, hY, cube_eq_one h2 hX hX' h1 h1']
  · intro h
    apply ne_one h2 hX h1 hX0
    rw [← hY, ← hgY, h, map_one]
  · apply natRep_injective (StatedSp r K)
    have hT1 : T = 1 + N := by rw [hN]; abel
    rw [map_mul, map_mul, hgY, ← hT, hT1, mul_add, add_mul, mul_one, one_mul, hY,
      commute_prod hc hc']

@[expose] def c3 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

theorem c3_pow_three : c3 ^ 3 = 1 := by decide

theorem c3_inv_zero : c3⁻¹ 0 = 2 := by decide

theorem permMatrix_map {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] (π : Equiv.Perm ι)
    {f : K → K} (h0 : f 0 = 0) (h1 : f 1 = 1) : (π.permMatrix K).map f = π.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp [h0, h1]

section Levi

variable (K : Type) [Field K]

@[expose] def q6 : StatedSp 3 K := leviSp (TauCeti.permutationGL c3)

variable {K}

theorem coe_q6 : (((q6 K : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      fromBlocks (c3⁻¹.permMatrix K) 0 0 (c3.permMatrix K)ᵀ := by
  rw [q6, coe_leviSp, ← map_inv, TauCeti.permutationGL_coe, TauCeti.permutationGL_coe, inv_inv]

theorem q6_pow_three : q6 K ^ 3 = 1 := by
  rw [q6, ← map_pow, ← map_pow, c3_pow_three, map_one, map_one]

theorem q6_ne_one : q6 K ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : StatedSp 3 K => ((g : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl 0) (Sum.inl 0)) h
  simp only [coe_q6, fromBlocks_apply₁₁, Subgroup.coe_one, Units.val_one, one_apply_eq] at h1
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, c3_inv_zero] at h1

theorem fieldSp_q6 (φ : K ≃+* K) : fieldSp 3 K φ (q6 K) = q6 K := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSp, coe_q6, fromBlocks_map, permMatrix_map _ (map_zero φ) (map_one φ),
    transpose_map, permMatrix_map _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)]

theorem fieldAut_proj_q6 (φ : K ≃+* K) : fieldAut 3 K φ (proj 3 K (q6 K)) = proj 3 K (q6 K) := by
  rw [fieldAut_proj, fieldSp_q6]

end Levi

open CFSG.RankThree.PartTwo.KFacts.KS21.Sp64 (F4 PS)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem proj_injective_F4 : Function.Injective (proj 3 F4) :=
  UnitaryHigher.proj_bijective_of_charTwo.1

theorem invCentThree_PS : InvCentThree PS :=
  (invCentThree_Sp (K := F4) (le_refl 3)).of_mulEquiv
    (MulEquiv.ofBijective (proj 3 F4) UnitaryHigher.proj_bijective_of_charTwo)

theorem orderOf_proj_q6 : orderOf (proj 3 F4 (q6 F4)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_injective _ proj_injective_F4]
  exact orderOf_eq_prime q6_pow_three q6_ne_one

theorem invFixThree_PS : InvFixThree PS := by
  intro α hα
  have hα2 : α ^ 2 = 1 := by
    have h := pow_orderOf_eq_one α
    rwa [hα] at h
  have hK : Nat.card F4 = 2 ^ 2 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KS21.Sp64.card_F4]; norm_num
  have hαE : α ∈ spSemilinearAutGroup 3 F4 := by
    rw [(automorphism_generation (r := 3) (K := F4) (by norm_num)).1]
    exact Subgroup.mem_top α
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut hαE
  by_cases hφ : φ = 1
  · subst hφ
    rw [map_one, mul_one, spInner_eq_conj] at hgφ
    subst hgφ
    exact conj_fix CFSG.RankThree.PartTwo.KFacts.KS21.Sp64.center_PS invCentThree_PS _ hα
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, h, hh⟩ :=
      even_symplectic_quadratic_involution_descent (by norm_num) (by norm_num) hK
        (by rw [← sq]; exact hα2) g φ (by rw [hgφ, spInner_apply]) hφ
    exact ⟨conjAut 3 F4 ⟨h, statedSp_le_gsp h.2⟩ (proj 3 F4 (q6 F4)),
      by rw [MulEquiv.orderOf_eq]; exact orderOf_proj_q6, fix_of_conj hh (fieldAut_proj_q6 φ)⟩

theorem invFixThree_projSp : InvFixThree (CFSG.Assembly.RankThreeEven.projSp 3 F4) :=
  invFixThree_PS.of_mulEquiv
    (CFSG.RankThree.PartTwo.KFacts.KS21.Sp64.equivSp.trans
      CFSG.RankThree.PartTwo.KFacts.KS21.Sp64.psEquivSp.symm)

end CFSG.RankThree.PartTwo.Sec21.AS76.Sp64
