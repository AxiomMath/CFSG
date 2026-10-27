module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowProduct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

private theorem mem_zpow_prime_pow_of_mem_zpowers {G : Type*} [Group G] {a : G} {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) (ha : orderOf a = p ^ k) {b : G}
    (hb : b ∈ Subgroup.zpowers a) (hb1 : b ≠ 1) :
    a ^ (p ^ (k - 1)) ∈ Subgroup.zpowers b := by
  have hpow_ne : a ^ (p ^ (k - 1)) ≠ 1 := by
    intro h
    have hd : orderOf a ∣ p ^ (k - 1) := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact h
    rw [ha] at hd
    have hpos : 0 < p ^ (k - 1) := pow_pos hp.pos _
    have hle := Nat.le_of_dvd hpos hd
    have hlt : p ^ (k - 1) < p ^ k := by
      apply Nat.pow_lt_pow_right hp.one_lt
      omega
    omega
  have horder : orderOf (a ^ (p ^ (k - 1))) = p := by
    have hdvd : orderOf (a ^ (p ^ (k - 1))) ∣ p := by
      rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul,
        show p ^ (k - 1) * p = p ^ k by rw [← pow_succ, Nat.sub_add_cancel hk],
        ← ha, pow_orderOf_eq_one]
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hpow_ne
    · exact h
  have hbord : p ∣ orderOf b := by
    have hdvd : orderOf b ∣ p ^ k := by
      rw [← ha]; exact orderOf_dvd_of_mem_zpowers hb
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact hb1 (orderOf_eq_one_iff.mp hm)
    have h1 : p ^ 1 ∣ p ^ m := pow_dvd_pow p (by omega)
    rw [hm]; simpa using h1
  let Z : Subgroup G := Subgroup.zpowers a
  haveI : IsCyclic Z := Subgroup.isCyclic_zpowers a
  have haZ : a ^ (p ^ (k - 1)) ∈ Z := Subgroup.npow_mem_zpowers a _
  let A : Subgroup Z := Subgroup.zpowers (⟨a ^ (p ^ (k - 1)), haZ⟩ : Z)
  let B : Subgroup Z := Subgroup.zpowers (⟨b, hb⟩ : Z)
  have hAcard : Nat.card A = p := by
    change Nat.card (Subgroup.zpowers (⟨a ^ (p ^ (k - 1)), haZ⟩ : Z)) = p
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact horder
  have hBcard : Nat.card B = orderOf b := by
    change Nat.card (Subgroup.zpowers (⟨b, hb⟩ : Z)) = orderOf b
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hAcard]; exact hp.ne_zero)
  have hle : A ≤ B := by
    rw [IsCyclic.subgroup_le_iff_card_dvd (H := A) (K := B), hAcard, hBcard]
    exact hbord
  have hmemZ : (⟨a ^ (p ^ (k - 1)), haZ⟩ : Z) ∈ B := hle (Subgroup.mem_zpowers _)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmemZ
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨n, ?_⟩
  have hcoe := congrArg (fun z : Z => (z : G)) hn
  simpa using hcoe

theorem orderOf_two_dvd_finrank_of_pow_prime_pow {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] {ℓ k : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hk : 1 ≤ k)
    {y : LGL 2 W} (hy : y ^ (ℓ ^ k) = 1) (M : Submodule (ZMod 2) W)
    (hyM : ∀ x ∈ M, y x ∈ M) (hfix : ∀ x ∈ M, (y ^ (ℓ ^ (k - 1))) x = x → x = 0) :
    orderOf (2 : ZMod (ℓ ^ k)) ∣ Module.finrank (ZMod 2) ↥M := by
  classical
  haveI : Finite ↥M := inferInstance
  by_cases hM : M = ⊥
  · rw [hM, finrank_bot]
    exact dvd_zero _
  · have hpowmem : ∀ n : ℕ, ∀ x ∈ M, (y ^ n) x ∈ M := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
        intro x hx
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hyM _ (ih x hx)
    have hmap : M.map (y : W →ₗ[ZMod 2] W) = M := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hyM x hx
      · intro x hx
        refine ⟨(y ^ (ℓ ^ k - 1)) x, hpowmem _ x hx, ?_⟩
        have h1 : (y * y ^ (ℓ ^ k - 1)) x = x := by
          rw [← pow_succ', Nat.sub_add_cancel (one_le_pow₀ hℓ.one_le), hy]
          rfl
        rwa [LinearEquiv.mul_apply] at h1
    let e : ↥M ≃ₗ[ZMod 2] ↥M := LinearEquiv.ofSubmodules y M M hmap
    have he : ∀ w : ↥M, ((e w : ↥M) : W) = y (w : W) := fun w => rfl
    have hpowe : ∀ n : ℕ, ∀ w : ↥M, (((e ^ n) w : ↥M) : W) = (y ^ n) (w : W) := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, he, ih]
    have hep : e ^ (ℓ ^ k) = 1 := by
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [hpowe (ℓ ^ k) w, hy]
      rfl
    have hfixe : ∀ w : ↥M, (e ^ (ℓ ^ (k - 1))) w = w → w = 0 := by
      intro w hw
      apply Subtype.ext
      refine hfix (w : W) w.2 ?_
      have h1 := congrArg Subtype.val hw
      rw [hpowe (ℓ ^ (k - 1)) w] at h1
      exact h1
    obtain ⟨x0, hx0⟩ : ∃ x : ↥M, x ≠ 0 := by
      obtain ⟨x, hxM, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
      exact ⟨⟨x, hxM⟩, fun h => hxne (congrArg Subtype.val h)⟩
    haveI : Nonempty ↥M := ⟨x0⟩
    have hord : orderOf e = ℓ ^ k := by
      have hdvd : orderOf e ∣ ℓ ^ k := orderOf_dvd_of_pow_eq_one hep
      have hnotdvd : ¬ orderOf e ∣ ℓ ^ (k - 1) := by
        intro hd
        have h1 : e ^ (ℓ ^ (k - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
        exact hx0 (hfixe x0 (by rw [h1]; rfl))
      obtain ⟨j, hjk_le, hj⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
      have hjk : j = k := by
        by_contra hne
        have hjle : j ≤ k - 1 := by omega
        exact hnotdvd (by rw [hj]; exact pow_dvd_pow ℓ hjle)
      rw [hj, hjk]
    let G : Subgroup (LGL 2 ↥M) := Subgroup.zpowers e
    have hGcard : Nat.card G = ℓ ^ k := by
      change Nat.card (Subgroup.zpowers e) = ℓ ^ k
      rw [Nat.card_zpowers]
      exact hord
    have hfree_aux : ∀ g ∈ G, g ≠ 1 → ∀ x : ↥M, x ≠ 0 → g x ≠ x := by
      intro g hg hg1 x hxne hgx
      have hmem : e ^ (ℓ ^ (k - 1)) ∈ Subgroup.zpowers g :=
        mem_zpow_prime_pow_of_mem_zpowers hℓ hk hord hg hg1
      have hfix_x : (e ^ (ℓ ^ (k - 1))) x = x := by
        have hstab : g ∈ MulAction.stabilizer (LGL 2 ↥M) x := by
          rw [MulAction.mem_stabilizer_iff]
          simpa [LinearEquiv.smul_def] using hgx
        simpa [LinearEquiv.smul_def] using Subgroup.zpowers_le.mpr hstab hmem
      exact hxne (hfixe x hfix_x)
    let Ω := {x : ↥M // x ≠ 0}
    letI : MulAction G Ω :=
      { smul := fun g x => ⟨g.1 x.1, by
          intro h
          apply x.2
          have h2 := congrArg (fun z => g.1.symm z) h
          simpa using h2⟩
        one_smul := fun x => by
          apply Subtype.ext
          change ((1 : G) : LGL 2 ↥M) x.1 = x.1
          simp
        mul_smul := fun g h x => by
          apply Subtype.ext
          change ((g * h : G) : LGL 2 ↥M) x.1 =
            (g : LGL 2 ↥M) ((h : LGL 2 ↥M) x.1)
          rw [Subgroup.coe_mul, LinearEquiv.mul_apply] }
    have hfree : ∀ (g : G) (ω : Ω), g • ω = ω → g = 1 := by
      intro g ω hgω
      apply Subtype.ext
      by_contra hg1
      have hx : g.1 ω.1 = ω.1 := congrArg Subtype.val hgω
      exact hfree_aux g.1 g.2 hg1 ω.1 ω.2 hx
    have hdvd : ℓ ^ k ∣ Nat.card Ω := by
      refine CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.dvd_card_of_orbit_dvd
        (K := G) (Ω := Ω) (d := ℓ ^ k) ?_
      intro ω
      haveI : Fintype G := Fintype.ofFinite G
      haveI : Fintype (MulAction.orbit G ω) := Fintype.ofFinite _
      haveI : Fintype (MulAction.stabilizer G ω) := Fintype.ofFinite _
      have hcardstab : Fintype.card (MulAction.stabilizer G ω) = 1 := by
        rw [Fintype.card_eq_one_iff]
        exact ⟨1, fun g => Subtype.ext
          (hfree g.1 ω (MulAction.mem_stabilizer_iff.mp g.2))⟩
      have horbit : Nat.card (MulAction.orbit G ω) = ℓ ^ k := by
        have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G ω
        rw [hcardstab, mul_one] at h1
        rw [Nat.card_eq_fintype_card, h1, ← Nat.card_eq_fintype_card, hGcard]
      rw [horbit]
    have hΩcard : Nat.card Ω = Nat.card ↥M - 1 := by
      haveI : Fintype ↥M := Fintype.ofFinite ↥M
      have h := Fintype.card_subtype_compl (α := ↥M) (fun x : ↥M => x = 0)
      rw [Fintype.card_subtype_eq (0 : ↥M)] at h
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
      simpa [Ω] using h
    haveI : Module.Finite (ZMod 2) ↥M := Module.Finite.of_finite
    have hmod : Nat.card ↥M ≡ 1 [MOD ℓ ^ k] := by
      have hdvdM : ℓ ^ k ∣ Nat.card ↥M - 1 := by
        rw [← hΩcard]; exact hdvd
      have hle1 : 1 ≤ Nat.card ↥M := Nat.card_pos
      exact ((Nat.modEq_iff_dvd' hle1).mpr hdvdM).symm
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥M), Nat.card_zmod] at hmod
    exact orderOf_dvd_of_pow_eq_one (by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
      simpa using this)

end CFSG.LocalAnalysis.WeakClosure81

end
