module

public import CFSG.Quasithin.Vol2.Ch11SecAKA3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.Quasithin.Vol2.KGNat (IsCoord linModelNat gmapSp spLine vec4)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (lSp dGL)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (torus_mem_stabW act_diag_sp)

namespace BK1

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem injective_of_bot (hf : IsCoord (linModelNat (StatedSp 2 K)) H ⊥ π f) {a b : W}
    (h : f a = f b) : a = b :=
  mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))

theorem exists_scalar_of_mem (hf : IsCoord (linModelNat (StatedSp 2 K)) H ⊥ π f)
    (g : StatedSp 2 K) {s : MulAut W}
    (hs : s ∈ H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) :
    ∃ c : K, c ≠ 0 ∧ ∀ w, f w ∈ gmapSp g (spLine K) → f (s w) = c • f w := by
  obtain ⟨M, hM⟩ : ∃ M, π M = ⟨s, hs.1⟩ := hf.onto ⟨s, hs.1⟩
  have hsM : s = ((π M : ↥H) : MulAut W) := by rw [hM]
  obtain ⟨c, hc⟩ := KGNat.exists_scalar_of_stab_sp hf (g := g) (γ := M) fun w hw => by
    rw [← hsM]
    exact (Ch11.SecA.mem_stabW.mp hs.2 w).mp hw
  refine ⟨c, ?_, fun w hw => by rw [hsM]; exact hc w hw⟩
  rintro rfl
  obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
  have hu₀U : f u₀ ∈ gmapSp g (spLine K) :=
    KGNat.mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
  have h1 := hc u₀ hu₀U
  rw [zero_smul, hf.act4, hu₀] at h1
  apply KGNat.v0_ne_zero g
  have h2 := congrArg (fun v => mat 2 K M⁻¹ *ᵥ v) h1
  simpa only [KGNat.mat_inv_mulVec, Matrix.mulVec_zero] using h2

theorem exists_coord_ne (hf : IsCoord (linModelNat (StatedSp 2 K)) H ⊥ π f) {g : StatedSp 2 K}
    {u : W} (hu : f u ∈ gmapSp g (spLine K)) (hu1 : u ≠ 1) :
    ∃ t : K, t ≠ 0 ∧ f u = t • (mat 2 K g *ᵥ vec4 1 0 0 0) := by
  obtain ⟨t, ht⟩ := KGNat.mem_gmapSp_spLine_iff.mp hu
  refine ⟨t, fun h0 => hu1 (injective_of_bot hf ?_), ht⟩
  rw [ht, h0, zero_smul, hf.map_one]

end BK1

theorem factPointSp4_holds : FactPointSp4 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU
  obtain ⟨f, hf, g, -, rfl⟩ := KGNat.KA.exists_point_coords hn hK hW hπ hP hU
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hpow : ∀ c : K, c ≠ 0 → ∃ k : ℕ, (a : K) ^ k = c := by
    intro c hc
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (ha (Units.mk0 c hc)) :
      Units.mk0 c hc ∈ Submonoid.powers a)
    exact ⟨k, by rw [← Units.val_pow_eq_pow_val, show a ^ k = Units.mk0 c hc from hk,
      Units.val_mk0]⟩
  have hmem : ∀ c : Kˣ, ((π (g * lSp K (dGL (c, 1)) * g⁻¹) : ↥H) : MulAut W) ∈
      H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup) :=
    fun c => ⟨(π _).2, torus_mem_stabW hf g c⟩
  refine ⟨⟨_, hmem a, fun s hs => ?_⟩, fun u hu w hw hu1 hw1 => ?_,
    fun s hs u hu hu1 hsu w hw => ?_⟩
  · obtain ⟨c, hc0, hc⟩ := BK1.exists_scalar_of_mem hf g hs
    obtain ⟨k, hk⟩ := hpow c hc0
    refine ⟨k, fun u hu => BK1.injective_of_bot hf ?_⟩
    rw [zpow_natCast, KGNat.KA.torus_pow, hc u hu, act_diag_sp hf g (a ^ k) hu,
      Units.val_pow_eq_pow_val, hk]
  · obtain ⟨s, hs0, hs⟩ := BK1.exists_coord_ne hf hu hu1
    obtain ⟨t, ht0, ht⟩ := BK1.exists_coord_ne hf hw hw1
    refine ⟨_, hmem (Units.mk0 (t / s) (div_ne_zero ht0 hs0)), BK1.injective_of_bot hf ?_⟩
    rw [act_diag_sp hf g _ hu, Units.val_mk0, hs, ht, smul_smul, div_mul_cancel₀ _ hs0]
  · obtain ⟨c, -, hc⟩ := BK1.exists_scalar_of_mem hf g hs
    have hfu0 : f u ≠ 0 := fun h0 => hu1 (BK1.injective_of_bot hf (by rw [h0, hf.map_one]))
    have hc1 : c = 1 := by
      have h1 := hc u hu
      rw [hsu] at h1
      have h2 : (c - 1) • f u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hfu0)
    exact BK1.injective_of_bot hf (by rw [hc w hw, hc1, one_smul])

theorem factPointTSp4_holds : FactPointTSp4 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU S hS2 hSH hSU _
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨f, hf, g, -, rfl⟩ := KGNat.KA.exists_point_coords hn hK hW hπ hP hU
  exact KGNat.actsCyclicallyOn_point hf (fun T hT => KGNat.commutant_statedSp T hT)
    (KGNat.v0_ne_zero g) (fun w => KGNat.mem_gmapSp_spLine_iff) hS2 hSH hSU

end CFSG.Quasithin.Vol2.Ch11.SecB
