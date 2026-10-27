module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4K
public import CFSG.Quasithin.Vol2.KGNatSL3NatFixed

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.ClassicalInvolution.ModelFacts.OddCover C11P9A
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Quasithin.Vol2.KGNat (charP_two_of_card four_le_card exists_isCoord linModelNat
  exists_sylow_eq_conj_Usp exists_eq_pre_of_isFlagW_sp eq_std_of_stable_sp flag_one_eq spLine
  spPlane gmapSp vec4 mem_gmapSp_spLine_iff v0_ne_zero fixedW_iff_sp le_of_isSylowTwoOf
  exists_ne_zero_ne_one)

theorem factNatFixedSp4_holds : FactNatFixedSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₂ hU₂ R hR2 hPR hRN
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hK4 := exists_finset_card_four (four_le_card hn hK)
  have hZ' : ∀ h ∈ H, ∀ z ∈ Z, h z = z := fun h hh z hz => hZ z hz h hh
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [← hK] at hU₂
  obtain ⟨S₂, hS₂, hc₂, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU₂
  obtain rfl := (eq_std_of_stable_sp hS₂).2.1 hc₂
  set U₁ := hf.pre (gmapSp g (spLine K)).toAddSubgroup with hU₁
  have hfixΓ := fix_gammaW_one hf hZ' g
  have hPΓ : ∀ p ∈ P, p ∈ gammaW H U₁ := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := (hg p).mp hp
    rw [hU₁, gammaW_pre_eq hf g 0 _ flag_one_eq]
    exact ⟨u, usp_le_perfectCore hK4 hu, rfl⟩
  have hPU : ∀ w, (∀ p ∈ P, p w = w) ↔ w ∈ U₁ := by
    intro w
    constructor
    · intro h
      exact (fixedW_iff_sp hf hg w).mp fun s hs => by rw [h s hs, mul_inv_cancel]; exact Z.one_mem
    · intro hw p hp
      exact hfixΓ p (hPΓ p hp) w hw
  have hRH : R ⊓ H ≤ P := le_of_isSylowTwoOf hP (hR2.to_inf_left) (le_inf hPR hP.1) inf_le_right
  have hRP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P := fun r hr x hx =>
    hRH ⟨R.mul_mem (R.mul_mem hr (hPR hx)) (R.inv_mem hr),
      (Subgroup.mem_normalizer_iff.mp (hRN hr) x).mp (hP.1 hx)⟩
  have hRU : ∀ r ∈ R, ∀ w ∈ U₁, r w ∈ U₁ := by
    intro r hr w hw
    rw [← hPU] at hw ⊢
    intro p hp
    have h1 := hw _ (hRP r⁻¹ (R.inv_mem hr) p hp)
    rw [MulAut.mul_apply, MulAut.mul_apply, inv_inv] at h1
    calc p (r w) = r (r⁻¹ (p (r w))) := (MulAut.apply_inv_self W r _).symm
      _ = r w := by rw [h1]
  have hRU' : ∀ r ∈ R, ∀ w, r w ∈ U₁ ↔ w ∈ U₁ := fun r hr w =>
    ⟨fun h => by
      have := hRU r⁻¹ (R.inv_mem hr) _ h
      rwa [MulAut.inv_apply_self] at this, hRU r hr w⟩
  set Y := Ch11.SecA.commS (H ⊓ Ch11.SecA.stabW U₁) U₁ with hYdef
  have hYU : Y ≤ U₁ := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨h, hh, u, hu, rfl⟩
    exact U₁.mul_mem ((Ch11.SecA.mem_stabW.mp hh.2 u).mp hu) (U₁.inv_mem hu))
  have hRY : ∀ r ∈ R, ∀ y ∈ Y, r y ∈ Y := by
    intro r hr
    have hle : Y ≤ Y.comap (r : W →* W) := (Subgroup.closure_le _).mpr (by
      rintro _ ⟨h, hh, u, hu, rfl⟩
      have hrh : r * h * r⁻¹ ∈ H ⊓ Ch11.SecA.stabW U₁ := by
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hRN hr) h).mp hh.1,
          Ch11.SecA.mem_stabW.mpr fun w => ?_⟩
        rw [MulAut.mul_apply, MulAut.mul_apply, hRU' r hr, ← Ch11.SecA.mem_stabW.mp hh.2,
          hRU' r⁻¹ (R.inv_mem hr)]
      show r (h u * u⁻¹) ∈ Y
      have heq : r (h u * u⁻¹) = (r * h * r⁻¹) (r u) * (r u)⁻¹ := by
        rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      rw [heq]
      exact Subgroup.subset_closure ⟨_, hrh, r u, hRU r hr u hu, rfl⟩)
    exact fun y hy => hle hy
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
  have htH : t ∈ H := (π _).2
  have htS : t ∈ Ch11.SecA.stabW U₁ := torus_mem_stabW hf g a
  have htf : ∀ u ∈ U₁, f (t u) = (a : K) • f u := fun u hu => act_diag_sp hf g a hu
  have htk : ∀ k : ℕ, ∀ u ∈ U₁, (t ^ k) u ∈ U₁ := by
    intro k
    induction k with
    | zero => intro u hu; rw [pow_zero, MulAut.one_apply]; exact hu
    | succ k ih =>
      intro u hu
      rw [pow_succ', MulAut.mul_apply]
      exact (Ch11.SecA.mem_stabW.mp htS _).mp (ih u hu)
  obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
  have hu₀U : u₀ ∈ U₁ := hf.mem_pre.mpr (mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩)
  have hA : ∀ h ∈ H ⊓ Ch11.SecA.stabW U₁, ∃ k : ℕ, ∀ u ∈ U₁, h u = (t ^ k) u :=
    fun h hh => act_eq_pow_of_mem_stab hK4 hf hZ' g ha hh
  have hB : ∀ k : ℕ, ∀ u ∈ U₁, ∃ v ∈ U₁, (t ^ k) u * u⁻¹ = t v * v⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro u hu
      exact ⟨1, U₁.one_mem, by rw [pow_zero, MulAut.one_apply, mul_inv_cancel, map_one,
        mul_inv_cancel]⟩
    | succ k ih =>
      intro u hu
      obtain ⟨v, hv, hveq⟩ := ih u hu
      refine ⟨(t ^ k) u * v, U₁.mul_mem (htk k u hu) hv, ?_⟩
      rw [pow_succ', MulAut.mul_apply, map_mul]
      calc t ((t ^ k) u) * u⁻¹ = t ((t ^ k) u) * ((t ^ k) u)⁻¹ * ((t ^ k) u * u⁻¹) := by group
        _ = t ((t ^ k) u) * ((t ^ k) u)⁻¹ * (t v * v⁻¹) := by rw [hveq]
        _ = t ((t ^ k) u) * t v * ((t ^ k) u * v)⁻¹ := by rw [mul_inv]; ac_rfl
  let Yt : Subgroup W :=
    { carrier := {y | ∃ v ∈ U₁, t v * v⁻¹ = y}
      mul_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
        exact ⟨v * v', U₁.mul_mem hv hv', by rw [map_mul, mul_inv]; ac_rfl⟩
      one_mem' := ⟨1, U₁.one_mem, by rw [map_one, mul_inv_cancel]⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, U₁.inv_mem hv, by rw [map_inv, inv_inv, mul_inv, inv_inv]⟩ }
  have hYYt : Y ≤ Yt := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨h, hh, u, hu, rfl⟩
    obtain ⟨k, hk⟩ := hA h hh
    obtain ⟨v, hv, hveq⟩ := hB k u hu
    exact ⟨v, hv, by rw [hk u hu]; exact hveq.symm⟩)
  have hYtZ : ∀ y ∈ Yt, y ∈ Z → y = 1 := by
    rintro _ ⟨v, hv, rfl⟩ hz
    have h1 : f (t v) = f v := (hf.eq_iff _ _).mpr hz
    rw [htf v hv] at h1
    have h2 : f v = 0 := by
      have h3 : ((a : K) - 1) • f v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha1)
    rw [hZ' t htH v ((hf.ker v).mp h2), mul_inv_cancel]
  have hy0 : t u₀ * u₀⁻¹ ∈ Y := Subgroup.subset_closure ⟨t, ⟨htH, htS⟩, u₀, hu₀U, rfl⟩
  have hy0ne : t u₀ * u₀⁻¹ ≠ 1 := by
    intro h
    have h1 : f (t u₀) = f u₀ := by rw [mul_inv_eq_one.mp h]
    rw [htf u₀ hu₀U, hu₀] at h1
    have h3 : ((a : K) - 1) • (mat 2 K g *ᵥ vec4 1 0 0 0) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    exact v0_ne_zero g ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha1))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥R ↥Y :=
    { smul := fun r y => ⟨(r : MulAut W) y, hRY r r.2 y y.2⟩
      one_smul := fun y => Subtype.ext rfl
      mul_smul := fun r s y => Subtype.ext rfl }
  have hY2 : IsPGroup 2 ↥Y := fun y => ⟨1, Subtype.ext (by rw [pow_one]; exact hW y)⟩
  have hYcard : 2 ∣ Nat.card ↥Y := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hY2
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      have := Finite.card_le_one_iff_subsingleton.mp hm.le
      exact hy0ne (congrArg Subtype.val (Subsingleton.elim (⟨_, hy0⟩ : ↥Y) 1))
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨b, hb, hb1⟩ := hR2.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥Y hYcard
    (a := (1 : ↥Y)) fun r => Subtype.ext (show (r : MulAut W) 1 = 1 from map_one _)
  refine ⟨b, fun r hr => congrArg Subtype.val (hb ⟨r, hr⟩), ?_⟩
  have hbZ : (b : W) ∉ Z := fun hz => hb1 (Subtype.ext (hYtZ _ (hYYt b.2) hz).symm)
  have hbU₁ : (b : W) ∈ U₁ := hYU b.2
  exact exists_move_gammaW_two hK4 hf g (hf.mem_pre.mp hbU₁) hbZ

end CFSG.Quasithin.Vol2.Ch11.SecS
