module

public import CFSG.Quasithin.Vol2.KGNatSp4Torus
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4
public import CFSG.Quasithin.Vol2.KGNatSL3PointFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

namespace C11P9A

variable {K : Type} [Field K]

theorem lSp_dGL_mem_normalizer_Usp (t : Kˣ × Kˣ) :
    lSp K (dGL t) ∈ Subgroup.normalizer (Usp K : Set (StatedSp 2 K)) := by
  have key : ∀ s : Kˣ × Kˣ, ∀ u ∈ Usp K, lSp K (dGL s) * u * (lSp K (dGL s))⁻¹ ∈ Usp K := by
    rintro s _ ⟨x, y, z, r, rfl⟩
    rw [show lSp K (dGL s) * (qSp x y z * nSp r) * (lSp K (dGL s))⁻¹ =
        (lSp K (dGL s) * qSp x y z * (lSp K (dGL s))⁻¹) *
          (lSp K (dGL s) * nSp r * (lSp K (dGL s))⁻¹) by group,
      lSp_dGL_conj_qSp, lSp_dGL_conj_nSp]
    exact (Usp K).mul_mem (qSp_mem_Usp _ _ _) (nSp_mem_Usp _)
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key t u, fun h => ?_⟩
  have h1 := key t⁻¹ _ h
  rwa [map_inv, map_inv, inv_inv,
    show (lSp K (dGL t))⁻¹ * (lSp K (dGL t) * u * (lSp K (dGL t))⁻¹) * lSp K (dGL t) = u by
      group] at h1

theorem mat_lSp_dGL_e0 (a : Kˣ) :
    mat 2 K (lSp K (dGL (a, 1))) *ᵥ vec4 1 0 0 0 = (a : K) • vec4 1 0 0 0 := by
  rw [mat_lSp, coe_dGL]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [vec4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, Matrix.diagonal_apply]

section Point

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem act_diag_sp (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    (c : Kˣ) {w : W} (hw : f w ∈ gmapSp g (spLine K)) :
    f (((π (g * lSp K (dGL (c, 1)) * g⁻¹) : ↥H) : MulAut W) w) = (c : K) • f w := by
  obtain ⟨t, ht⟩ := mem_gmapSp_spLine_iff.mp hw
  rw [hf.act4, ht, Matrix.mulVec_smul, map_mul, map_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, mat_inv_mulVec, mat_lSp_dGL_e0, Matrix.mulVec_smul, smul_comm]

theorem mem_normalizer_diag_sp {P : Subgroup (MulAut W)} {g : StatedSp 2 K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W))
    (c : Kˣ) :
    ((π (g * lSp K (dGL (c, 1)) * g⁻¹) : ↥H) : MulAut W) ∈
      Subgroup.normalizer (P : Set (MulAut W)) := by
  have hTN := lSp_dGL_mem_normalizer_Usp (K := K) (c, 1)
  set d := lSp K (dGL (c, 1)) with hd
  have e1 : ∀ X Y : StatedSp 2 K, ((π X : ↥H) : MulAut W) * ((π Y : ↥H) : MulAut W) *
      ((π X : ↥H) : MulAut W)⁻¹ = ((π (X * Y * X⁻¹) : ↥H) : MulAut W) := fun X Y => by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨u, hu, rfl⟩ := (hg y).mp hy
    refine (hg _).mpr ⟨d * u * d⁻¹, (Subgroup.mem_normalizer_iff.mp hTN u).mp hu, ?_⟩
    rw [e1]
    congr 2
    group
  · intro hy
    obtain ⟨u, hu, hu'⟩ := (hg _).mp hy
    refine (hg y).mpr ⟨d⁻¹ * u * d, ?_, ?_⟩
    · refine (Subgroup.mem_normalizer_iff.mp hTN _).mpr ?_
      rwa [show d * (d⁻¹ * u * d) * d⁻¹ = u by group]
    · have e2 : ((π (g * d * g⁻¹) : ↥H) : MulAut W)⁻¹ *
          ((π (g * u * g⁻¹) : ↥H) : MulAut W) * ((π (g * d * g⁻¹) : ↥H) : MulAut W) =
          ((π (g * (d⁻¹ * u * d) * g⁻¹) : ↥H) : MulAut W) := by
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have h1 : y = ((π (g * d * g⁻¹) : ↥H) : MulAut W)⁻¹ *
          (((π (g * d * g⁻¹) : ↥H) : MulAut W) * y * ((π (g * d * g⁻¹) : ↥H) : MulAut W)⁻¹) *
          ((π (g * d * g⁻¹) : ↥H) : MulAut W) := by group
      rw [h1, hu', e2]

end Point

end C11P9A

open C11P9A in
theorem factNatPointSp4_holds : FactNatPointSp4 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U₁ hU₁ D hD
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  have hU' : Ch11.SecA.IsFlagW H P ⊥ (Nat.card K) 1 U₁ := by rw [hK]; exact hU₁
  obtain ⟨S, hS, hcS, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU'
  rw [(eq_std_of_stable_sp hS).1 (by rw [hcS, pow_one])]
  set U₁ := hf.pre (gmapSp g (spLine K)).toAddSubgroup with hU₁
  have hPU : ∀ w, (∀ p ∈ P, p w = w) ↔ w ∈ U₁ := by
    intro w
    constructor
    · intro h
      exact (fixedW_iff_sp hf hg w).mp fun s hs => by
        rw [h s hs, mul_inv_cancel]
        exact Subgroup.one_mem _
    · intro hw p hp
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((fixedW_iff_sp hf hg w).mpr hw p hp))
  refine ⟨fun w hw1 hwP => ⟨(hPU w).mp hwP, fun h hh hhw => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := mem_gmapSp_spLine_iff.mp ((hPU w).mp hwP)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw1 (Subgroup.mem_bot.mp ((hf.ker w).mp hc))
    obtain ⟨M, hM⟩ : ∃ M : ↥(StatedSp 2 K), π M = ⟨h, hh⟩ := hf.onto ⟨h, hh⟩
    have hhM : h = ((π M : ↥H) : MulAut W) := by rw [hM]
    have hMg : mat 2 K M *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = mat 2 K g *ᵥ vec4 1 0 0 0 := by
      have h1 := congrArg f hhw
      rw [hhM, hf.act4, hc, Matrix.mulVec_smul] at h1
      exact smul_right_injective _ hc0 h1
    have hMg' : mat 2 K M⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = mat 2 K g *ᵥ vec4 1 0 0 0 := by
      conv_lhs => rw [← hMg]
      rw [mat_inv_mulVec]
    rw [hhM, hf.pi_mem_stabW_iff_sp (hf.le_pre _), hf.img_pre]
    intro y
    change y ∈ gmapSp g _ ↔ _ ∈ gmapSp g _
    rw [mem_gmapSp_spLine_iff, mem_gmapSp_spLine_iff]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, by rw [Matrix.mulVec_smul, hMg]⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      rw [← mat_inv_mulVec M y, hs, Matrix.mulVec_smul, hMg']
  · set B := H ⊓ Subgroup.normalizer (P : Set (MulAut W)) with hB
    have hBU : ∀ b ∈ B, ∀ w ∈ U₁, b w ∈ U₁ := by
      intro b hb w hw
      rw [← hPU] at hw ⊢
      intro p hp
      have hp' : b⁻¹ * p * b⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb.2) p).mp hp
      have h1 := hw _ hp'
      rw [MulAut.mul_apply, MulAut.mul_apply, inv_inv] at h1
      calc p (b w) = b (b⁻¹ (p (b w))) := (MulAut.apply_inv_self W b _).symm
        _ = b w := by rw [h1]
    have hscal : ∀ b ∈ B, ∃ c : K, ∀ u ∈ U₁, f (b u) = c • f u := by
      intro b hb
      obtain ⟨M, hM⟩ : ∃ M : ↥(StatedSp 2 K), π M = ⟨b, hb.1⟩ := hf.onto ⟨b, hb.1⟩
      have hbM : b = ((π M : ↥H) : MulAut W) := by rw [hM]
      obtain ⟨c, hc⟩ := exists_scalar_of_stab_sp hf (g := g) (γ := M) fun w hw => by
        rw [← hbM]
        exact hBU b hb w hw
      exact ⟨c, fun u hu => by rw [hbM]; exact hc u hu⟩
    let K₀ : Subgroup (MulAut W) :=
      { carrier := {b | b ∈ B ∧ ∀ u ∈ U₁, b u = u}
        mul_mem' := fun {x y} hx hy => ⟨B.mul_mem hx.1 hy.1, fun u hu => by
          rw [MulAut.mul_apply, hy.2 u hu, hx.2 u hu]⟩
        one_mem' := ⟨B.one_mem, fun u _ => rfl⟩
        inv_mem' := fun {x} hx => ⟨B.inv_mem hx.1, fun u hu => by
          conv_lhs => rw [← hx.2 u hu]
          exact MulAut.inv_apply_self W x u⟩ }
    have hK₀B : K₀ ≤ B := fun x hx => hx.1
    have hK₀n : (K₀.subgroupOf B).Normal := by
      refine ⟨fun x hx b => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨B.mul_mem (B.mul_mem b.2 hx.1) (B.inv_mem b.2), fun u hu => ?_⟩
      have hbu : (b : MulAut W)⁻¹ u ∈ U₁ := hBU _ (B.inv_mem b.2) u hu
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply,
        MulAut.mul_apply, hx.2 _ hbu, MulAut.apply_inv_self]
    by_contra hcon
    push Not at hcon
    have hDK : D ≤ K₀ := by
      intro d hd
      obtain ⟨u, hu, hu1, hdu⟩ := hcon d hd
      have hdB : d ∈ B := hD.1 hd
      obtain ⟨c, hc⟩ := hscal d hdB
      have hfu : f u ≠ 0 := fun h0 => hu1 (Subgroup.mem_bot.mp ((hf.ker u).mp h0))
      have hc1 : c = 1 := by
        have h1 := hc u hu
        rw [hdu] at h1
        have h2 : (c - 1) • f u = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hfu)
      exact ⟨hdB, fun v hv => hinj _ _ (by rw [hc v hv, hc1, one_smul])⟩
    obtain ⟨k, hk⟩ := hD.2.2
    have hdiv : K₀.relIndex B ∣ 2 ^ k := by
      rw [← hk, ← Subgroup.relIndex_mul_relIndex D K₀ B hDK hK₀B]
      exact Dvd.intro_left _ rfl
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
    have ha1 : (a : K) ≠ 1 := by
      obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K) (by
        have := four_le_card hn hK
        omega)
      intro h
      have ha1' : a = 1 := Units.ext h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha (Units.mk0 c hc0))
      rw [ha1', _root_.one_zpow] at hk
      exact hc1 (congrArg Units.val hk).symm
    set t := ((π (g * lSp K (dGL (a, 1)) * g⁻¹) : ↥H) : MulAut W) with ht
    have htB : t ∈ B := ⟨(π _).2, mem_normalizer_diag_sp hg a⟩
    have htf : ∀ u ∈ U₁, f (t u) = (a : K) • f u := fun u hu => act_diag_sp hf g a hu
    have htk : ∀ m : ℕ, ∀ u ∈ U₁, f ((t ^ m) u) = ((a : K) ^ m) • f u := by
      intro m
      induction m with
      | zero => intro u hu; rw [pow_zero, MulAut.one_apply, pow_zero, one_smul]
      | succ m ih =>
        intro u hu
        rw [pow_succ', MulAut.mul_apply, htf _ (hBU _ (B.pow_mem htB m) u hu), ih u hu,
          smul_smul, pow_succ']
    have hpow : ((⟨t, htB⟩ : ↥B) ^ 2 ^ j) ∈ K₀.subgroupOf B := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      have h1 := pow_card_eq_one' (x := (QuotientGroup.mk ⟨t, htB⟩ : ↥B ⧸ K₀.subgroupOf B))
      rwa [← Subgroup.index, ← Subgroup.relIndex, hj] at h1
    obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
    have hu₀U : u₀ ∈ U₁ := mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
    have h2 := (Subgroup.mem_subgroupOf.mp hpow).2 u₀ hu₀U
    rw [Subgroup.coe_pow] at h2
    have h3 := htk (2 ^ j) u₀ hu₀U
    rw [h2, hu₀] at h3
    have h4 : ((a : K) ^ 2 ^ j - 1) • (mat 2 K g *ᵥ vec4 1 0 0 0) = 0 := by
      rw [sub_smul, ← h3, one_smul, sub_self]
    have h5 : (a : K) ^ 2 ^ j = 1 :=
      sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right (v0_ne_zero g))
    exact ha1 (eq_one_of_pow_two_pow h5)

end CFSG.Quasithin.Vol2.Ch11.SecS
