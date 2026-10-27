module

public import CFSG.Quasithin.Vol2.Ch11SecEK1E
public import CFSG.Quasithin.Vol2.Ch11SecEFacts5
public import CFSG.Quasithin.Vol2.Ch11SecAKA8
public import CFSG.Quasithin.Vol2.Ch11SecAKA2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.KGNat.KA
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkQ blkQ_apply blkIdx sigma2 spMat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer flag)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (mem_pCoreOf_Q0_iff pCoreOf_Q0_eq gammaW_pre_eq)

namespace EK1

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_pCore_eq_root (hK4 : ∃ s : Finset K, s.card = 4)
    {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)} {σ : K →+* K}
    (hσ : ∀ (c : K) (x : Fin 2 ⊕ Fin 2 → K), T (c • x) = σ c • T x)
    (hL : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x)
    (hinj : Function.Injective T) (hline : T (vec4 1 0 0 0) ∈ spLine K)
    (hlevi : ∀ M ∈ perfectCore (Q2 K 0), ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ v,
      T (mat 2 K M *ᵥ v) = mat 2 K N *ᵥ (mat 2 K M *ᵥ T v))
    {m : ℕ} (hroot : ∀ x : K, x ^ m = 1 → x = 1) (hk : ∀ v, (⇑T)^[m] v = v) :
    ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ v, mat 2 K N *ᵥ v = T v := by
  obtain ⟨hσ1, ha2, ha3, hb2, hb1, hab, ha1⟩ := shape_of_levi hK4 hσ hL hinj hline hlevi
  have hlin : ∀ (c : K) x, T (c • x) = c • T x := fun c x => by rw [hσ, hσ1]
  obtain ⟨l1, l2, l3⟩ := hline
  obtain ⟨lam, hlam⟩ : ∃ l, T (vec4 1 0 0 0) (.inl 0) = l := ⟨_, rfl⟩
  obtain ⟨a₁, ha₁⟩ : ∃ a, T (vec4 0 1 0 0) (.inl 1) = a := ⟨_, rfl⟩
  rw [ha₁] at hab ha1
  have he0 : T (vec4 1 0 0 0) = lam • vec4 1 0 0 0 :=
    vec4_eq (by rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one, hlam])
      (by rw [Pi.smul_apply, vec4_apply_inl1, smul_eq_mul, mul_zero, l1])
      (by rw [Pi.smul_apply, vec4_apply_inr0, smul_eq_mul, mul_zero, l2])
      (by rw [Pi.smul_apply, vec4_apply_inr1, smul_eq_mul, mul_zero, l3])
  have hplane : ∀ v : Fin 2 ⊕ Fin 2 → K, v (.inr 0) = 0 → v (.inr 1) = 0 →
      (T v) (.inl 1) = a₁ * v (.inl 1) ∧ (T v) (.inr 0) = 0 ∧ (T v) (.inr 1) = 0 := by
    intro v h2 h3
    have hTv : T v = v (.inl 0) • (lam • vec4 1 0 0 0) + v (.inl 1) • T (vec4 0 1 0 0) := by
      conv_lhs => rw [eq_plane v h2 h3]
      rw [map_add, hlin, hlin, he0]
    rw [hTv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1, ha2, ha3, ha₁]
    exact ⟨by ring, by ring, by ring⟩
  have hit0 : ∀ m : ℕ, (⇑T)^[m] (vec4 1 0 0 0) = lam ^ m • vec4 1 0 0 0 := by
    intro m
    induction m with
    | zero => rw [Function.iterate_zero, id, pow_zero, one_smul]
    | succ m ih => rw [Function.iterate_succ_apply', ih, hlin, he0, smul_smul, pow_succ]
  have hit1 : ∀ m : ℕ, ((⇑T)^[m] (vec4 0 1 0 0)) (.inl 1) = a₁ ^ m ∧
      ((⇑T)^[m] (vec4 0 1 0 0)) (.inr 0) = 0 ∧ ((⇑T)^[m] (vec4 0 1 0 0)) (.inr 1) = 0 := by
    intro m
    induction m with
    | zero => exact ⟨by rw [pow_zero]; rfl, rfl, rfl⟩
    | succ m ih =>
      obtain ⟨h1, h2, h3⟩ := hplane _ ih.2.1 ih.2.2
      rw [Function.iterate_succ_apply', h1, ih.1, pow_succ, mul_comm]
      exact ⟨rfl, h2, h3⟩
  have hlam1 : lam = 1 := by
    have h := congrFun ((hit0 m).symm.trans (hk _)) (.inl 0)
    rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one] at h
    exact hroot _ h
  have ha11 : a₁ = 1 := by
    have h := (hit1 m).1
    rw [hk] at h
    exact hroot _ (h.symm.trans rfl)
  let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := T, map_add' := map_add T, map_smul' := fun c v => hlin c v }
  have hTL : ∀ v, TL v = T v := fun v => rfl
  obtain ⟨c, hc⟩ := exists_similitude TL fun γ => by
    obtain ⟨γ', hγ'⟩ := hL γ
    exact ⟨γ', fun x => hγ' x⟩
  have hc1 : c = 1 := by
    have h := hc (vec4 0 1 0 0) (vec4 0 0 0 1)
    rw [toBilin'_spJ_apply, toBilin'_spJ_apply] at h
    simp only [Fin.sum_univ_two, hTL, vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1, hb2, ha2, ha3, hab, ha₁, ha11] at h
    linear_combination -h
  have hbij : Function.Bijective TL :=
    ⟨show Function.Injective T from hinj, Finite.surjective_of_injective (f := TL) hinj⟩
  obtain ⟨N, hN⟩ := exists_statedSp_of_isometry hbij fun x y => by rw [hc, hc1, one_mul]
  have hNQ : N ∈ Q2 K 0 := by
    show N ∈ stabilizer 2 K (flag 2 K 1)
    rw [flag_one_eq]
    refine mem_stabilizer_iff'.mpr fun y => ?_
    rw [hN, hTL]
    constructor
    · intro hy
      have hy' : y = y (.inl 0) • vec4 1 0 0 0 :=
        vec4_eq (by simp [vec4]) (by simp [vec4, hy.1]) (by simp [vec4, hy.2.1])
          (by simp [vec4, hy.2.2])
      rw [hy', hlin, he0, hlam1, one_smul]
      exact (spLine K).smul_mem _ vec4_e0_mem_spLine
    · intro hy
      have hy' : T y = T ((T y) (.inl 0) • vec4 1 0 0 0) := by
        rw [hlin, he0, hlam1, one_smul]
        exact vec4_eq (by simp [vec4]) (by simp [vec4, hy.1]) (by simp [vec4, hy.2.1])
          (by simp [vec4, hy.2.2])
      rw [hinj hy']
      exact (spLine K).smul_mem _ vec4_e0_mem_spLine
  have hχ : spMat N (.inl 0) (.inl 0) = 1 := by
    rw [spMat_eq_mulVec, single_inl0, hN, hTL, hlam, hlam1]
  have e11 : spMat N (.inl 1) (.inl 1) = 1 := by
    rw [spMat_eq_mulVec, single_inl1, hN, hTL, ha₁, ha11]
  have e13 : spMat N (.inl 1) (.inr 1) = 0 := by
    rw [spMat_eq_mulVec, single_inr1, hN, hTL, hb1]
  have e31 : spMat N (.inr 1) (.inl 1) = 0 := by
    rw [spMat_eq_mulVec, single_inl1, hN, hTL, ha3]
  have e33 : spMat N (.inr 1) (.inr 1) = 1 := by
    rw [spMat_eq_mulVec, single_inr1, hN, hTL, hab, ha11]
  have hB : blkQ 0 ⟨N, hNQ⟩ = 1 := by
    rw [blkQ_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkIdx, sigma2, e11, e13, e31, e33]
  refine ⟨N, ?_, hN⟩
  rw [← pCoreOf_Q0_eq hK4]
  exact (mem_pCoreOf_Q0_iff hK4).mpr ⟨hNQ, hχ, hB⟩

variable {W : Type*} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem exists_core_root (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) {U : Subgroup W}
    (hU : U = hf.pre (gmapSp g (spLine K)).toAddSubgroup) (hfix : Ch11.SecA.RadicalFixes H Z U)
    (hpt : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z)
    {m : ℕ} (hroot : ∀ x : K, x ^ m = 1 → x = 1) {τ : MulAut W} (hk : τ ^ m = 1)
    (hτZ : τ ∈ Ch11.SecA.stabW Z)
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H)
    (hτc : ∀ x : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
      ∃ y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
        y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) ∧
          τ * (x : MulAut W) * τ⁻¹ = (y : MulAut W) * x) :
    ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ w, f (τ w) = f (psiSp π g N w) := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hτZ' : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (Ch11.SecA.mem_stabW.mp hτZ z).mp hz
  have hτZ'' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz =>
    (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW Z).inv_mem hτZ) z).mp hz
  have hτR : ∀ r ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U)),
      τ * r * τ⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hτc x
    have hx' : x ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) := by
      exact hx
    show τ * (x : MulAut W) * τ⁻¹ ∈ _
    rw [hxy]
    exact (mem_pCoreOf_iff' _ (y * x)).mpr (mul_mem hy hx')
  have hτU := mem_stabW_of_conj hfix hpt hτZ hτR
  subst hU
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 τ hτZ'
    hτZ'' (inv_conj_mem_of_conj_mem hτH)
  obtain ⟨T, hTf, hσ⟩ : ∃ T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K),
      (∀ w, T (f w) = f (τ w)) ∧ ∀ (c : K) x, T (c • x) = σ c • T x :=
    ⟨hf.autMap τ hτZ', hf.autMap_apply _ _, hσ⟩
  have hTinj : Function.Injective T := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := hf.surj x
    obtain ⟨b, rfl⟩ := hf.surj y
    rw [hTf, hTf, hf.eq_iff] at hxy
    rw [hf.eq_iff]
    have := hτZ'' _ hxy
    rwa [← map_inv, ← map_mul, MulAut.inv_apply_self] at this
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x := by
    intro γ
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(StatedSp 2 K), π γ' = ⟨_, hτH _ (π γ).2⟩ :=
      hf.onto ⟨_, hτH _ (π γ).2⟩
    refine ⟨γ', fun x => ?_⟩
    obtain ⟨w, rfl⟩ := hf.surj x
    have e : τ (((π γ : ↥H) : MulAut W) w) = ((π γ' : ↥H) : MulAut W) (τ w) := by
      rw [hγ']
      simp [MulAut.mul_apply]
    rw [← hf.act4, hTf, hTf, e, hf.act4]
  have hσ' : ∀ (c : K) x, gconjMap g T (c • x) = σ c • gconjMap g T x := fun c x => by
    rw [gconjMap_apply, gconjMap_apply, Matrix.mulVec_smul, hσ, Matrix.mulVec_smul]
  have hL' : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      gconjMap g T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ gconjMap g T x := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hnorm (g * γ * g⁻¹)
    refine ⟨g⁻¹ * γ' * g, fun x => ?_⟩
    have e : mat 2 K g *ᵥ (mat 2 K γ *ᵥ x) = mat 2 K (g * γ * g⁻¹) *ᵥ (mat 2 K g *ᵥ x) := by
      rw [gconj_mulVec_sp, mat_inv_mulVec]
    rw [gconjMap_apply, gconjMap_apply, e, hγ', map_mul, map_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, mat_mulVec_inv]
  have hinj' : Function.Injective (gconjMap g T) := fun x y h => by
    rw [gconjMap_apply, gconjMap_apply] at h
    have h1 := congrArg (fun v => mat 2 K g *ᵥ v) h
    simp only [mat_mulVec_inv] at h1
    have h3 := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) (hTinj h1)
    simpa only [mat_inv_mulVec] using h3
  have hline' : gconjMap g T (vec4 1 0 0 0) ∈ spLine K := by
    obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
    have hu₀U : u₀ ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup :=
      hf.mem_pre.mpr (mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩)
    have h2 : f (τ u₀) ∈ gmapSp g (spLine K) := (Ch11.SecA.mem_stabW.mp hτU u₀).mp hu₀U
    rw [← hTf, hu₀, mem_gmapSp] at h2
    exact h2
  have hlevi' : ∀ M ∈ perfectCore (Q2 K 0), ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ v,
      gconjMap g T (mat 2 K M *ᵥ v) = mat 2 K N *ᵥ (mat 2 K M *ᵥ gconjMap g T v) := by
    intro M hM
    have hψM : psiSp π g M ∈
        perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) := by
      rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) =
        Ch11.SecS.gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup) from rfl,
        gammaW_pre_eq hf g 0 _ flag_one_eq]
      exact ⟨M, hM, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hτc ⟨_, hψM⟩
    have hyR := (mem_pCoreOf_iff' _ y).mpr hy
    rw [pCoreOf_gamma_eq hf g] at hyR
    obtain ⟨N, hN, hNy⟩ := hyR
    refine ⟨N, hN, fun v => ?_⟩
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ v)
    have e : τ (psiSp π g M w) = psiSp π g N (psiSp π g M (τ w)) := by
      have := congrArg (fun x : MulAut W => x (τ w)) hxy
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
      rw [this, ← hNy]
    have e2 := congrArg f e
    rw [← hTf, psiSp_apply, hf.act4, psiSp_apply, hf.act4, hf.act4, ← hTf, hw] at e2
    have e3 := congrArg (fun z => mat 2 K g⁻¹ *ᵥ z) e2
    simp only [gconj_mulVec_sp, mat_inv_mulVec] at e3
    rw [gconjMap_apply, gconjMap_apply]
    exact e3
  have hk' : ∀ v, (⇑(gconjMap g T))^[m] v = v := by
    intro v
    rw [gconjMap_iterate]
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ v)
    rw [← hw, iterate_of_intertwine hTf, hk, MulAut.one_apply, hw, mat_inv_mulVec]
  obtain ⟨N₀, hN₀, hN₀T⟩ := exists_pCore_eq_root hK4 hσ' hL' hinj' hline' hlevi' hroot hk'
  refine ⟨N₀, hN₀, fun w => ?_⟩
  rw [← hTf, psiSp_apply, hf.act4, gconj_mulVec_sp, hN₀T, gconjMap_apply, mat_mulVec_inv,
    mat_mulVec_inv]

omit [Finite K] [CharP K 2] in
theorem exists_pow_of_mem_pCoreOf {G : Type*} [Group G] {X : Subgroup G} {x : G}
    (hx : x ∈ pCoreOf 2 X) : ∃ a : ℕ, x ^ 2 ^ a = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ CFSG.pCore 2 ↥X := (mem_pCoreOf_iff' X y).mp ⟨y, hy, rfl⟩
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨y, hy'⟩
  refine ⟨a, ?_⟩
  have h1 := congrArg (fun z : ↥(CFSG.pCore 2 ↥X) => ((z : ↥X) : G)) ha
  simpa using h1

end EK1

open EK1 in
theorem factCentLeviSp4_holds : FactCentLeviSp4 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU β hβH _ hc ⟨m, hmo, hmc, hβm⟩
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hroot : ∀ x : K, x ^ m = 1 → x = 1 := fun x hx =>
    eq_one_of_pow_coprime hK hmo.pos.ne' hmc hx
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hpt := KGNat.factPointSp4_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hfix := KGNat.factRadicalFixedSp4_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hτc : ∀ x : ↥(perfectCore (H ⊓ SecA.stabW U)),
      ∃ y : ↥(perfectCore (H ⊓ SecA.stabW U)),
        y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ SecA.stabW U)) ∧
          β * (x : MulAut W) * β⁻¹ = (y : MulAut W) * x := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hc x x.2)
    refine ⟨y, by exact hy, ?_⟩
    have hyx' : (y : MulAut W) = β * x * β⁻¹ * (x : MulAut W)⁻¹ := hyx
    rw [hyx', inv_mul_cancel_right]
  obtain ⟨f, hf, g, -, hUeq⟩ := KA.exists_point_coords hn hK hW hπ hP hU
  obtain ⟨N, hN, hact⟩ := exists_core_root hK4 hf g hUeq hfix hpt hroot hβm (mem_stabW_bot β)
    hβH hτc
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hseq : β = psiSp π g N := MulEquiv.ext fun w => hinj _ _ (hact w)
  obtain ⟨a, ha⟩ := exists_pow_of_mem_pCoreOf hN
  refine eq_one_of_odd_of_two_pow hmo hβm (a := a) ?_
  rw [hseq, ← map_pow, ha, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecE
