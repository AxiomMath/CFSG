module

public import CFSG.Quasithin.Vol2.Ch11G2Q8LeviG2
public import CFSG.Quasithin.Vol2.Ch11G2Q8NatPoint
public import CFSG.Quasithin.Vol2.KGNatSL3NatFixed

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {K : Type} [Field K] [CharP K 2]

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem mem_perfectCore_HU1_of_fix [Finite K] (h4 : 4 ≤ Nat.card K)
    (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g : ↥(cayleyGroup K))
    {x : MulAut W} (hx : x ∈ H)
    (hfix : ∀ u ∈ hf.pre (gmapG g (stdF K 1)).toAddSubgroup, f (x u) = f u) :
    x ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) := by
  obtain ⟨M, hM⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨x, hx⟩
  have hxM : x = ((rhoG hc0 hc1 π M : ↥H) : MulAut W) := by rw [hM]
  obtain ⟨u₀, hu₀⟩ := hf.surj (g2Act g (eu 0 1))
  have hu₀U : u₀ ∈ hf.pre (gmapG g (stdF K 1)).toAddSubgroup :=
    mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
  have h1 := hfix u₀ hu₀U
  rw [hxM, IsCoord.actG hf hc0 hc1, hu₀] at h1
  have hS : g⁻¹ * M * g ∈ stabV0 K := by
    rw [mem_stabV0, g2Act_mul_apply, g2Act_mul_apply, h1, g2Act_inv_apply]
  rw [← map_stabQ_eq hf hc0 hc1 g, perfectCore_map _ (psiG_injective hf hc0 hc1 g),
    perfectCore_stabQ_one h4]
  refine ⟨g⁻¹ * M * g, hS, ?_⟩
  rw [psiG_apply, show g * (g⁻¹ * M * g) * g⁻¹ = M by group, hxM]

theorem fix_perfectCore_HU2 [Finite K] (h4 : 4 ≤ Nat.card K)
    (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g : ↥(cayleyGroup K))
    {u : W} (hu : u ∈ hf.pre (gmapG g (stdF K 2)).toAddSubgroup)
    (hfix : ∀ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 2)).toAddSubgroup)),
      s u = u) : u ∈ Z := by
  obtain ⟨c, hc0', hc1'⟩ := exists_ne_zero_ne_one (by omega : 2 < Nat.card K)
  have hle : sl2E1 K ≤ perfectCore (stabQ (stdF K 2)) :=
    le_perfectCore_of_perfect sl2E1_le_stabQ (sl2E1_perfect hc0' hc1')
  have hmem : ∀ k ∈ sl2E1 K, psiG hc0 hc1 π g k ∈
      perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 2)).toAddSubgroup)) := by
    intro k hk
    rw [← map_stabQ_eq hf hc0 hc1 g, perfectCore_map _ (psiG_injective hf hc0 hc1 g)]
    exact ⟨k, hle hk, rfl⟩
  have key : ∀ k ∈ sl2E1 K, g2Act k (g2Act g⁻¹ (f u)) = g2Act g⁻¹ (f u) := by
    intro k hk
    have h1 := congrArg f (hfix _ (hmem k hk))
    rw [psiG_apply, IsCoord.actG hf hc0 hc1] at h1
    have h2 := congrArg (g2Act g⁻¹) h1
    rw [conj_g2Act] at h2
    exact h2
  have hu' : g2Act g⁻¹ (f u) ∈ stdF K 2 := mem_gmapG.mp hu
  obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp hu'
  set v := g2Act g⁻¹ (f u) with hv
  have hx := key _ (Subgroup.subset_closure ⟨1, Or.inl rfl⟩)
  have hy := key _ (Subgroup.subset_closure ⟨1, Or.inr rfl⟩)
  rw [q6_eta v, b1, b2, b3, b4, g2Act_x1q] at hx
  rw [q6_eta v, b1, b2, b3, b4, g2Act_y1q] at hy
  obtain ⟨-, -, -, -, -, ex⟩ := q6_inj hx
  obtain ⟨ey, -, -, -, -, -⟩ := q6_inj hy
  have ha : v (.inl 0) = 0 := by linear_combination ex
  have hf' : v (.inr 2) = 0 := by linear_combination ey
  have hv0 : v = 0 := by
    rw [q6_eta v, b1, b2, b3, b4, ha, hf', q6_zero]
  have h0 : f u = 0 := by
    rw [← g2Act_apply_inv g (f u), ← hv, hv0, map_zero]
  exact (hf.ker u).mp h0

end Real

theorem factNatFixedG2_holds : Ch11.SecS.FactNatFixedG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₂ hU₂ R hR2 hPR hRN
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have h4 := four_le_card hn hK
  have hZ' : ∀ h ∈ H, ∀ z ∈ Z, h z = z := fun h hh z hz => hZ z hz h hh
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU' : Ch11.SecA.IsFlagW H P Z (Nat.card K) 2 U₂ := by rw [hK]; exact hU₂
  obtain ⟨S₂, hS₂, hc₂, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU'
  rw [eq_stdF_of_card hS₂ hc₂]
  set U₁ := hf.pre (gmapG g (stdF K 1)).toAddSubgroup with hU₁
  have hU₁f : Ch11.SecA.IsFlagW H P Z (2 ^ n) 1 U₁ := by
    rw [← hK]
    exact isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 1) (card_stdF (by norm_num))
  have hfix1 : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U₁), ∀ u ∈ U₁, h u = u :=
    fix_of_perfect (perfectCore_perfect _) (fun h hh z hz => hZ' h (perfectCore_le _ hh).1 z hz)
      (factPointG2A_holds K n hn hK W hW H Z π hπ P hP U₁ hU₁f)
  have hPL := factSylowLeviG2_holds K n hn hK W hW H Z π hπ P hP U₁ hU₁f
  have hPU : ∀ w, (∀ p ∈ P, p w = w) ↔ w ∈ U₁ := by
    intro w
    constructor
    · intro h
      change f w ∈ gmapG g (stdF K 1)
      rw [mem_gmapG]
      refine fixed_U0 fun u hu => ?_
      have h1 := congrArg f (h _ ((hg _).mpr ⟨u, hu, rfl⟩))
      rw [IsCoord.actG hf hc0 hc1] at h1
      have h2 := congrArg (g2Act g⁻¹) h1
      rw [conj_g2Act] at h2
      exact h2
    · intro hw p hp
      exact hfix1 p (hPL hp) w hw
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
    intro h
    have ha1' : a = 1 := Units.ext h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha (Units.mk0 c₀ hc0))
    rw [ha1', _root_.one_zpow] at hk
    exact hc1 (congrArg Units.val hk).symm
  set t := ((rhoG hc0 hc1 π (g * tG a * g⁻¹) : ↥H) : MulAut W) with ht
  have htH : t ∈ H := (rhoG hc0 hc1 π _).2
  have htS : t ∈ Ch11.SecA.stabW U₁ := mem_stab_diagG hf hc0 hc1 g a
  have htf : ∀ u ∈ U₁, f (t u) = (a : K) • f u := fun u hu => act_diagG hf hc0 hc1 g a hu
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
  obtain ⟨u₀, hu₀⟩ := hf.surj (g2Act g (eu 0 1))
  have hu₀U : u₀ ∈ U₁ := mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
  have hA : ∀ h ∈ H ⊓ Ch11.SecA.stabW U₁, ∃ k : ℕ, ∀ u ∈ U₁, h u = (t ^ k) u := by
    intro h hh
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_stabG hf hc0 hc1 g hh
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a ^ k = c := by
      obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (ha c) : c ∈ Submonoid.powers a)
      exact ⟨k, hk⟩
    refine ⟨k, fun u hu => ?_⟩
    have htkH : (t ^ k)⁻¹ ∈ H := H.inv_mem (H.pow_mem htH k)
    obtain ⟨C, hC⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨(t ^ k)⁻¹, htkH⟩
    have hCf : ∀ v, f ((t ^ k)⁻¹ v) = g2Act C (f v) := fun v => by
      have h1 := IsCoord.actG hf hc0 hc1 C v
      rwa [hC] at h1
    have hfix : ∀ v ∈ U₁, f (((t ^ k)⁻¹ * h) v) = f v := by
      intro v hv
      rw [MulAut.mul_apply, hCf, hc v hv, ← hk, Units.val_pow_eq_pow_val, ← (htk k v hv).2,
        ← hCf, MulAut.inv_apply_self]
    have hxu := hfix1 _ (mem_perfectCore_HU1_of_fix h4 hf hc0 hc1 g (H.mul_mem htkH hh.1)
      hfix) u hu
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
    have h3 : ((a : K) - 1) • g2Act g (eu 0 (1 : K)) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    exact g2Act_eu_ne_zero g ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha1))
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
  have hbU₂ : (b : W) ∈ hf.pre (gmapG g (stdF K 2)).toAddSubgroup := by
    change f b ∈ gmapG g (stdF K 2)
    exact Submodule.map_mono (stdF_mono (by norm_num : 1 ≤ 2)) hbU₁
  by_contra hcon
  push Not at hcon
  exact hbZ (fix_perfectCore_HU2 h4 hf hc0 hc1 g hbU₂ hcon)

end CFSG.Quasithin.Vol2.Ch11.G2Q8
