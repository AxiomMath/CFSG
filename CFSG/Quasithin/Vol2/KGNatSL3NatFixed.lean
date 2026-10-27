module

public import CFSG.Quasithin.Vol2.KGNatSL3Line
public import CFSG.Quasithin.Vol2.KGNatSL3PointT
public import CFSG.Quasithin.Vol2.Ch11SecSZL2
public import CFSG.Quasithin.Vol2.Ch11SecAFactsLine

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem le_of_isSylowTwoOf {G : Type*} [Group G] [Finite G] {P H Q : Subgroup G}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) (hQ : IsPGroup 2 Q) (hPQ : P ≤ Q)
    (hQH : Q ≤ H) : Q ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hidx⟩ := hP
  have h1 : P.relIndex Q * Q.relIndex H = P.relIndex H :=
    Subgroup.relIndex_mul_relIndex P Q H hPQ hQH
  obtain ⟨k, hk⟩ := hQ.index (P.subgroupOf Q)
  have hk0 : k = 0 := by
    by_contra hk0
    apply hidx
    change 2 ∣ P.relIndex H
    rw [← h1]
    exact Dvd.dvd.mul_right (by rw [Subgroup.relIndex, hk]; exact dvd_pow_self 2 hk0) _
  rw [hk0, pow_zero] at hk
  exact Subgroup.relIndex_eq_one.mp hk

section Point

variable {K : Type} [Field K] [Finite K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem mem_perfectCore_HU1_of_fix (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {x : MulAut W} (hx : x ∈ H)
    (hfix : ∀ u ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup, f (x u) = f u) :
    x ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) := by
  obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨x, hx⟩
  have hxA : x = ((rho3 π A : ↥H) : MulAut W) := by rw [hA]
  obtain ⟨u₀, hu₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  have hu₀U := (mem_pre_line_iff hf g u₀).mpr ⟨1, by rw [hu₀, one_smul]⟩
  have h1 := hfix u₀ hu₀U
  rw [hxA, hf.act3, hu₀] at h1
  refine (mem_perfectCore_HU1_iff hSL hf g x).mpr ⟨g⁻¹ * A * g, ?_, ?_⟩
  · rw [← mulVec_gconj, h1, ginv_g_mulVec]
  · rw [hxA, show g * (g⁻¹ * A * g) * g⁻¹ = A by group]

end Point

theorem factNatFixedSL3_holds : Ch11.SecS.FactNatFixedSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₂ hU₂ R hR2 hPR hRN
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  have hZ' : ∀ h ∈ H, ∀ z ∈ Z, h z = z := fun h hh z hz => hZ z hz h hh
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  have hU' : Ch11.SecA.IsFlagW H P Z (Nat.card K) 2 U₂ := by rw [hK]; exact hU₂
  have hUeq := eq_U2_of_isFlagW hW hf hg hU'
  subst hUeq
  set U₁ := hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup with hU₁
  have hPU : ∀ w, (∀ p ∈ P, p w = w) ↔ w ∈ U₁ := by
    intro w
    constructor
    · intro h
      have h1 := (fixedW_iff hf hg w).mp fun s hs => by rw [h s hs, mul_inv_cancel]; exact Z.one_mem
      rw [hU₁, ← stdLine_eq_flagSpace]
      exact h1
    · intro hw p hp
      obtain ⟨u, ⟨a, b, c, rfl⟩, rfl⟩ := (hg p).mp hp
      exact fix_HU1 hSL hf hZ' g _ ((mem_perfectCore_HU1_iff hSL hf g _).mpr
        ⟨uSL a b c, uMat_mulVec_e0 a b c, rfl⟩) w hw
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
  set t := ((rho3 π (g * tSL (a, 1) * g⁻¹) : ↥H) : MulAut W) with ht
  have htH : t ∈ H := (rho3 π _).2
  have htS : t ∈ Ch11.SecA.stabW U₁ := by
    have := mem_stab_diag hf g a
    rwa [stdLine_eq_flagSpace] at this
  have htf : ∀ u ∈ U₁, f (t u) = (a : K) • f u := fun u hu =>
    act_diag hf g a (by rw [stdLine_eq_flagSpace]; exact hu)
  have htk : ∀ k : ℕ, ∀ u ∈ U₁, (t ^ k) u ∈ U₁ ∧ f ((t ^ k) u) = ((a : K) ^ k) • f u := by
    intro k
    induction k with
    | zero => intro u hu; rw [pow_zero, MulAut.one_apply, pow_zero, one_smul]; exact ⟨hu, rfl⟩
    | succ k ih =>
      intro u hu
      obtain ⟨h1, h2⟩ := ih u hu
      rw [pow_succ', MulAut.mul_apply]
      refine ⟨(Ch11.SecA.mem_stabW.mp htS _).mp h1, ?_⟩
      rw [htf _ h1, h2, smul_smul, pow_succ']
  obtain ⟨u₀, hu₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  have hu₀U : u₀ ∈ U₁ := (mem_pre_line_iff hf g u₀).mpr ⟨1, by rw [hu₀, one_smul]⟩
  have hA : ∀ h ∈ H ⊓ Ch11.SecA.stabW U₁, ∃ k : ℕ, ∀ u ∈ U₁, h u = (t ^ k) u := by
    intro h hh
    obtain ⟨M, hM⟩ := (rho3_bijective hf).2 ⟨h, hh.1⟩
    have hhM : h = ((rho3 π M : ↥H) : MulAut W) := by rw [hM]
    obtain ⟨c, hc⟩ := exists_scalar_of_stab hf (g := g) (A := M) fun w hw => by
      rw [← hhM, stdLine_eq_flagSpace]
      rw [stdLine_eq_flagSpace] at hw
      exact (Ch11.SecA.mem_stabW.mp hh.2 w).mp hw
    have hcU : ∀ u ∈ U₁, f (h u) = c • f u := fun u hu => by
      rw [hhM]
      exact hc u (by rw [stdLine_eq_flagSpace]; exact hu)
    have hc0 : c ≠ 0 := by
      intro hc0
      have h1 := hcU u₀ hu₀U
      rw [hc0, zero_smul, hf.ker] at h1
      have h2 : u₀ ∈ Z := by
        have := hZ' h⁻¹ (H.inv_mem hh.1) _ h1
        rw [MulAut.inv_apply_self] at this
        rw [this]
        exact h1
      rw [← hf.ker, hu₀] at h2
      exact g_e0_ne_zero g h2
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (a : K) ^ k = c := by
      obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (ha (Units.mk0 c hc0)) :
        Units.mk0 c hc0 ∈ Submonoid.powers a)
      exact ⟨k, by
        rw [← Units.val_pow_eq_pow_val, show a ^ k = Units.mk0 c hc0 from hk, Units.val_mk0]⟩
    refine ⟨k, fun u hu => ?_⟩
    have htkH : (t ^ k)⁻¹ ∈ H := H.inv_mem (H.pow_mem htH k)
    obtain ⟨C, hC⟩ := (rho3_bijective hf).2 ⟨(t ^ k)⁻¹, htkH⟩
    have hCf : ∀ v, f ((t ^ k)⁻¹ v) = (C : Matrix (Fin 3) (Fin 3) K) *ᵥ f v := fun v => by
      have := hf.act3 C v
      rwa [hC] at this
    have hfix : ∀ v ∈ U₁, f (((t ^ k)⁻¹ * h) v) = f v := by
      intro v hv
      rw [MulAut.mul_apply, hCf, hcU v hv, ← hk, ← (htk k v hv).2, ← hCf, MulAut.inv_apply_self]
    have hxu := fix_HU1 hSL hf hZ' g _
      (mem_perfectCore_HU1_of_fix hSL hf g (H.mul_mem htkH hh.1) hfix) u hu
    rw [MulAut.mul_apply] at hxu
    calc h u = (t ^ k) ((t ^ k)⁻¹ (h u)) := (MulAut.apply_inv_self W _ _).symm
      _ = (t ^ k) u := by rw [hxu]
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
      refine ⟨(t ^ k) u * v, U₁.mul_mem (htk k u hu).1 hv, ?_⟩
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
    have h3 : ((a : K) - 1) • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    exact g_e0_ne_zero g ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha1))
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
  have hbU₂ : (b : W) ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup := by
    obtain ⟨c, hc⟩ := (mem_pre_line_iff hf g _).mp hbU₁
    refine (mem_pre_plane_iff hf g _).mpr ?_
    rw [hc, Matrix.mulVec_smul, ginv_g_mulVec]
    simp
  by_contra hcon
  push Not at hcon
  exact hbZ ((fixed_plane_iff hSL hf hZ' g hbU₂).mp hcon)

end CFSG.Quasithin.Vol2.KGNat
