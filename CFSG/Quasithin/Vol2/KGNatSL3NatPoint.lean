module

public import CFSG.Quasithin.Vol2.Ch11SecSFacts4
public import CFSG.Quasithin.Vol2.KGNatSL3Line
public import CFSG.Quasithin.Vol2.KGNatSL3PointT

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem tSL_mem_normalizer_Usl {K : Type} [Field K] (t : Kˣ × Kˣ) :
    tSL t ∈ Subgroup.normalizer (Usl K : Set (SpecialLinearGroup (Fin 3) K)) := by
  have key : ∀ s : Kˣ × Kˣ, ∀ u ∈ Usl K, tSL s * u * (tSL s)⁻¹ ∈ Usl K := by
    intro s u hu
    obtain ⟨a, b, c, rfl⟩ := mem_Usl.mp hu
    rw [tSL_conj_uSL]
    exact uSL_mem_Usl _ _ _
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key t u, fun h => ?_⟩
  have h1 := key t⁻¹ _ h
  rwa [map_inv, inv_inv, show (tSL t)⁻¹ * (tSL t * u * (tSL t)⁻¹) * tSL t = u by group] at h1

theorem factNatPointSL3_holds : Ch11.SecS.FactNatPointSL3 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U₁ hU₁ D hD
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hZ' : ∀ h ∈ H, ∀ z ∈ (⊥ : Subgroup W), h z = z := fun h _ z hz => by
    rw [Subgroup.mem_bot.mp hz, map_one]
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  have hU' : Ch11.SecA.IsFlagW H P ⊥ (Nat.card K) 1 U₁ := by rw [hK]; exact hU₁
  have hUeq := eq_U1_of_isFlagW hW hf hg hU'
  subst hUeq
  have hPU : ∀ w, (∀ p ∈ P, p w = w) ↔ w ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
    intro w
    constructor
    · intro h
      have h1 := (fixedW_iff hf hg w).mp fun s hs => by
        rw [h s hs, mul_inv_cancel]
        exact Subgroup.one_mem _
      rw [← stdLine_eq_flagSpace]
      exact h1
    · intro hw p hp
      obtain ⟨u, ⟨a, b, c, rfl⟩, rfl⟩ := (hg p).mp hp
      exact fix_HU1 hSL hf hZ' g _ ((mem_perfectCore_HU1_iff hSL hf g _).mpr
        ⟨uSL a b c, uMat_mulVec_e0 a b c, rfl⟩) w hw
  refine ⟨fun w hw1 hwP => ⟨(hPU w).mp hwP, fun h hh hhw => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := (mem_pre_line_iff hf g w).mp ((hPU w).mp hwP)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw1 (Subgroup.mem_bot.mp ((hf.ker w).mp hc))
    obtain ⟨M, hM⟩ := (rho3_bijective hf).2 ⟨h, hh⟩
    have hhM : h = ((rho3 π M : ↥H) : MulAut W) := by rw [hM]
    have hMg : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) =
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] := by
      have h1 := congrArg f hhw
      rw [hhM, hf.act3, hc, Matrix.mulVec_smul] at h1
      exact smul_right_injective _ hc0 h1
    have hMg' : ((M⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) =
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] := by
      conv_lhs => rw [← hMg]
      rw [ginv_g_mulVec]
    rw [hhM, hf.rho3_mem_stabW_iff (hf.le_pre _), hf.img_pre]
    intro y
    change y ∈ gmap g _ ↔ _ ∈ gmap g _
    rw [← stdLine_eq_flagSpace, mem_gmap_stdLine_iff, mem_gmap_stdLine_iff]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, by rw [Matrix.mulVec_smul, hMg]⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      rw [← ginv_g_mulVec M y, hs, Matrix.mulVec_smul, hMg']
  · set U₁ := hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup with hU₁
    set B := H ⊓ Subgroup.normalizer (P : Set (MulAut W)) with hB
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
      obtain ⟨M, hM⟩ := (rho3_bijective hf).2 ⟨b, hb.1⟩
      have hbM : b = ((rho3 π M : ↥H) : MulAut W) := by rw [hM]
      obtain ⟨c, hc⟩ := exists_scalar_of_stab hf (g := g) (A := M) fun w hw => by
        rw [← hbM, stdLine_eq_flagSpace]
        rw [stdLine_eq_flagSpace] at hw
        exact hBU b hb w hw
      exact ⟨c, fun u hu => by rw [hbM]; exact hc u (by rw [stdLine_eq_flagSpace]; exact hu)⟩
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
    set t := ((rho3 π (g * tSL (a, 1) * g⁻¹) : ↥H) : MulAut W) with ht
    have e1 : ∀ X Y : SpecialLinearGroup (Fin 3) K, ((rho3 π X : ↥H) : MulAut W) *
        ((rho3 π Y : ↥H) : MulAut W) * ((rho3 π X : ↥H) : MulAut W)⁻¹ =
        ((rho3 π (X * Y * X⁻¹) : ↥H) : MulAut W) := fun X Y => by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have e2 : ∀ X Y : SpecialLinearGroup (Fin 3) K, ((rho3 π X : ↥H) : MulAut W)⁻¹ *
        ((rho3 π Y : ↥H) : MulAut W) * ((rho3 π X : ↥H) : MulAut W) =
        ((rho3 π (X⁻¹ * Y * X) : ↥H) : MulAut W) := fun X Y => by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have htN : t ∈ Subgroup.normalizer (P : Set (MulAut W)) := by
      have hTN := tSL_mem_normalizer_Usl (a, 1)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨u, hu, rfl⟩ := (hg y).mp hy
        refine (hg _).mpr ⟨tSL (a, 1) * u * (tSL (a, 1))⁻¹,
          (Subgroup.mem_normalizer_iff.mp hTN u).mp hu, ?_⟩
        rw [ht, e1]
        congr 2
        group
      · intro hy
        obtain ⟨u, hu, hu'⟩ := (hg _).mp hy
        refine (hg y).mpr ⟨(tSL (a, 1))⁻¹ * u * tSL (a, 1), ?_, ?_⟩
        · refine (Subgroup.mem_normalizer_iff.mp hTN _).mpr ?_
          rwa [show tSL (a, 1) * ((tSL (a, 1))⁻¹ * u * tSL (a, 1)) * (tSL (a, 1))⁻¹ = u by group]
        · have h1 : y = t⁻¹ * (t * y * t⁻¹) * t := by group
          rw [h1, hu', ht, e2]
          congr 2
          group
    have htB : t ∈ B := ⟨(rho3 π _).2, htN⟩
    have htf : ∀ u ∈ U₁, f (t u) = (a : K) • f u := fun u hu =>
      act_diag hf g a (by rw [stdLine_eq_flagSpace]; exact hu)
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
    obtain ⟨u₀, hu₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
    have hu₀U : u₀ ∈ U₁ := (mem_pre_line_iff hf g u₀).mpr ⟨1, by rw [hu₀, one_smul]⟩
    have h2 := (Subgroup.mem_subgroupOf.mp hpow).2 u₀ hu₀U
    rw [Subgroup.coe_pow] at h2
    have h3 := htk (2 ^ j) u₀ hu₀U
    rw [h2, hu₀] at h3
    have h4 : ((a : K) ^ 2 ^ j - 1) • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) = 0 := by
      rw [sub_smul, ← h3, one_smul, sub_self]
    have h5 : (a : K) ^ 2 ^ j = 1 :=
      sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right (g_e0_ne_zero g))
    exact ha1 (eq_one_of_pow_two_pow h5)

end CFSG.Quasithin.Vol2.KGNat
