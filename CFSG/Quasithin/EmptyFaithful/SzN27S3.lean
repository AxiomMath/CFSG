module

public import CFSG.Quasithin.EmptyFaithful.SzN27Cfg
public import CFSG.Quasithin.EmptyFaithful.SBdK36Gen

public section

namespace CFSG.Quasithin.SzN27

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open Equiv

section OutCyclic

@[expose] def OutCyclic (X : Type) [Group X] : Prop :=
  Function.Injective (MulAut.conj : X →* MulAut X) ∧ IsCyclic (Outer X)

theorem OutCyclic.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : OutCyclic Y) :
    OutCyclic X := by
  refine ⟨fun g g' hgg => ?_, ?_⟩
  · have h1 : MulAut.conj (e g) = MulAut.conj (e g') := by
      rw [← OuterAutomorphisms.congr_conj e g, ← OuterAutomorphisms.congr_conj e g', hgg]
    exact e.injective (h.1 h1)
  · have := h.2
    exact isCyclic_of_surjective (OuterAutomorphisms.equivalence e).symm.toMonoidHom
      (OuterAutomorphisms.equivalence e).symm.surjective

end OutCyclic

section Gamma

abbrev Gam : Type := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

@[expose] noncomputable def signHom : Gam →* ℤˣ × ℤˣ :=
  (Equiv.Perm.sign.comp (MonoidHom.fst _ _)).prod (Equiv.Perm.sign.comp (MonoidHom.snd _ _))

theorem signHom_apply (g : Gam) : signHom g = (Equiv.Perm.sign g.1, Equiv.Perm.sign g.2) := rfl

theorem Gam.pow_three_iff (g : Gam) : g ^ 3 = 1 ↔ signHom g = 1 := by
  have h1 : ∀ a : Perm (Fin 3), a ^ 3 = 1 ↔ Equiv.Perm.sign a = 1 := by decide
  rw [signHom_apply, Prod.ext_iff, Prod.ext_iff]
  simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one, h1]

theorem Gam.mul_pow_three {a b : Gam} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) : (a * b) ^ 3 = 1 := by
  rw [Gam.pow_three_iff] at *
  rw [map_mul, ha, hb, mul_one]

theorem Gam.pow_three_of_centralizes {x : Gam} (h : ∀ e : Gam, e ^ 3 = 1 → x * e = e * x) :
    x ^ 3 = 1 := by
  have h1 : ∀ a : Perm (Fin 3), a * finRotate 3 = finRotate 3 * a → Equiv.Perm.sign a = 1 := by
    decide
  have hc : (finRotate 3 : Perm (Fin 3)) ^ 3 = 1 := by decide
  have e1 := h (finRotate 3, 1) (by
    rw [Prod.ext_iff]
    simp [hc])
  have e2 := h (1, finRotate 3) (by
    rw [Prod.ext_iff]
    simp [hc])
  rw [Gam.pow_three_iff, signHom_apply, Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · exact h1 _ (by simpa [Prod.ext_iff] using e1)
  · exact h1 _ (by simpa [Prod.ext_iff] using e2)

theorem signHom_surjective : Function.Surjective signHom := by
  rintro ⟨a, b⟩
  have h1 : ∀ u : ℤˣ, ∃ σ : Perm (Fin 3), Equiv.Perm.sign σ = u := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨swap 0 1, Equiv.Perm.sign_swap (by decide)⟩
  obtain ⟨σ, hσ⟩ := h1 a
  obtain ⟨τ, hτ⟩ := h1 b
  exact ⟨(σ, τ), by rw [signHom_apply]; simp [hσ, hτ]⟩

theorem not_isCyclic_units_prod : ¬ IsCyclic (ℤˣ × ℤˣ) := by
  intro h
  obtain ⟨g, hg⟩ := h.exists_generator
  have hsq : ∀ x : ℤˣ × ℤˣ, x ^ 2 = 1 := by
    rintro ⟨a, b⟩
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
      decide
  have h1 : ∀ x : ℤˣ × ℤˣ, x = 1 ∨ x = g := by
    intro x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    have : g ^ k = g ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
      have : (g ^ (2 : ℤ)) = 1 := by simpa using hsq g
      rw [this, one_zpow, mul_one]
    rw [this]
    have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h2 | h2 <;> rw [h2]
    · left; simp
    · right; simp
  have e1 := h1 (-1, 1)
  have e2 := h1 (1, -1)
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exact absurd e1 (by decide)
  · exact absurd e1 (by decide)
  · exact absurd e2 (by decide)
  · exact absurd (e1.trans e2.symm) (by decide)

end Gamma

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup {Y S : Subgroup G} (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    {x : G} (hx : x ∈ Y ⊔ S) : ∃ y ∈ Y, ∃ s ∈ S, x = y * s := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · exact ⟨a, ha, 1, S.one_mem, by simp⟩
    · exact ⟨1, Y.one_mem, a, ha, by simp⟩
  | one => exact ⟨1, Y.one_mem, 1, S.one_mem, by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨y₁, hy₁, s₁, hs₁, rfl⟩ := iha
    obtain ⟨y₂, hy₂, s₂, hs₂, rfl⟩ := ihb
    refine ⟨y₁ * (s₁ * y₂ * s₁⁻¹), Y.mul_mem hy₁
      ((Subgroup.mem_normalizer_iff.mp (hSY hs₁) y₂).mp hy₂), s₁ * s₂, S.mul_mem hs₁ hs₂, ?_⟩
    group
  | inv a _ iha =>
    obtain ⟨y, hy, s, hs, rfl⟩ := iha
    refine ⟨s⁻¹ * y⁻¹ * s, ?_, s⁻¹, S.inv_mem hs, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem hs)) y⁻¹).mp (Y.inv_mem hy)
    simpa using this

omit [Finite G] in
theorem isPGroup_zpowers_two {X : Type} [Group X] {g : X} {k : ℕ} (h : g ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem false_of_s3s3 {L Yp S : Subgroup G} (hZ : centerOf L = CFSG.Open.pCoreOf 2 L)
    (hS2 : IsPGroup 2 ↥S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hSY : S ≤ Subgroup.normalizer (Yp : Set G)) (hYL : Yp ≤ L)
    (hQsyl : IsSylowTwoOf (S ⊓ L) L) (hY3 : ∀ y ∈ Yp, y ^ 3 ∈ pCoreOf 2 Yp)
    (φ : ↥(Yp ⊔ S) →* Gam) (hφ : Function.Surjective φ)
    (hφk : φ.ker = (oTwoPhi (Yp ⊔ S)).subgroupOf (Yp ⊔ S))
    (hT : ((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
      (Yp.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hX : OutCyclic (↥L ⧸ Subgroup.center ↥L)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.2
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hYS : Yp ≤ Yp ⊔ S := le_sup_left
  have hSYS : S ≤ Yp ⊔ S := le_sup_right
  have hSN₂ : Yp ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
    refine sup_le ?_ ?_
    · exact hYL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    · exact hSL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hSN₃ : Yp ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 Yp : Set G) := by
    refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Yp) ?_
    exact hSY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Yp)
  have hker₁ : ∀ x : G, ∀ hx : x ∈ Yp ⊔ S, x ∈ pCoreOf 2 L → φ ⟨x, hx⟩ = 1 := by
    intro x hx hxO
    have hle : pCoreOf 2 L ⊓ (Yp ⊔ S) ≤ pCoreOf 2 (Yp ⊔ S) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left)
      intro h hh
      refine Subgroup.mem_normalizer_iff.mpr fun a => ?_
      constructor
      · rintro ⟨ha1, ha2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hSN₂ hh) a).mp ha1,
          (Yp ⊔ S).mul_mem ((Yp ⊔ S).mul_mem hh ha2) ((Yp ⊔ S).inv_mem hh)⟩
      · rintro ⟨ha1, ha2⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hSN₂ hh) a).mpr ha1, ?_⟩
        have := (Yp ⊔ S).mul_mem ((Yp ⊔ S).mul_mem ((Yp ⊔ S).inv_mem hh) ha2) hh
        simpa [mul_assoc] using this
    have h1 := SBd.pCoreOf_le_oTwoPhi (Yp ⊔ S) (hle ⟨hxO, hx⟩)
    have : (⟨x, hx⟩ : ↥(Yp ⊔ S)) ∈ φ.ker := by
      rw [hφk]
      exact Subgroup.mem_subgroupOf.mpr h1
    exact this
  have hker₂ : ∀ x : G, ∀ hx : x ∈ Yp ⊔ S, x ∈ pCoreOf 2 Yp → φ ⟨x, hx⟩ = 1 := by
    intro x hx hxO
    have hle : pCoreOf 2 Yp ≤ pCoreOf 2 (Yp ⊔ S) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Yp).trans hYS) hSN₃
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Yp)
    have h1 := SBd.pCoreOf_le_oTwoPhi (Yp ⊔ S) (hle hxO)
    have : (⟨x, hx⟩ : ↥(Yp ⊔ S)) ∈ φ.ker := by
      rw [hφk]
      exact Subgroup.mem_subgroupOf.mpr h1
    exact this
  have hYE : ∀ y : G, ∀ hy : y ∈ Yp, (φ ⟨y, hYS hy⟩) ^ 3 = 1 := by
    intro y hy
    rw [← map_pow]
    have : (⟨y, hYS hy⟩ : ↥(Yp ⊔ S)) ^ 3 = ⟨y ^ 3, (Yp ⊔ S).pow_mem (hYS hy) 3⟩ := rfl
    rw [this]
    exact hker₂ _ _ (hY3 y hy)
  have hS2' : ∀ s : ↥S, ∃ k : ℕ, (φ ⟨(s : G), hSYS s.2⟩) ^ 2 ^ k = 1 := by
    intro s
    obtain ⟨k, hk⟩ := hS2 s
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨(s : G), hSYS s.2⟩ : ↥(Yp ⊔ S)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
  have hone : ∀ (x : Gam) (k : ℕ), x ^ 3 = 1 → x ^ 2 ^ k = 1 → x = 1 := by
    intro x k h3 h2
    have h := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    have hg : (2 ^ k).gcd 3 = 1 := by
      have : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      exact this
    rwa [hg, pow_one] at h
  have hF1 : ∀ e : Gam, e ^ 3 = 1 → ∃ (y : G) (hy : y ∈ Yp), φ ⟨y, hYS hy⟩ = e := by
    intro e he
    obtain ⟨x, rfl⟩ := hφ e
    obtain ⟨y, hy, s, hs, hxs⟩ := exists_mul_of_mem_sup hSY x.2
    have hx : x = ⟨y, hYS hy⟩ * ⟨s, hSYS hs⟩ := Subtype.ext hxs
    refine ⟨y, hy, ?_⟩
    obtain ⟨k, hk⟩ := hS2' ⟨s, hs⟩
    have h3 : (φ ⟨s, hSYS hs⟩) ^ 3 = 1 := by
      have h1 : φ ⟨s, hSYS hs⟩ = (φ ⟨y, hYS hy⟩)⁻¹ * φ x := by
        rw [hx, map_mul]
        group
      rw [h1]
      refine Gam.mul_pow_three ?_ he
      rw [inv_pow, hYE y hy, inv_one]
    have h1 : φ ⟨s, hSYS hs⟩ = 1 := hone _ k h3 hk
    rw [hx, map_mul, h1, mul_one]
  let θ : ↥S →* ℤˣ × ℤˣ := signHom.comp (φ.comp (Subgroup.inclusion hSYS))
  have hθs : Function.Surjective θ := by
    intro p
    obtain ⟨γ, hγ⟩ := signHom_surjective p
    obtain ⟨x, rfl⟩ := hφ γ
    obtain ⟨y, hy, s, hs, hxs⟩ := exists_mul_of_mem_sup hSY x.2
    have hx : x = ⟨y, hYS hy⟩ * ⟨s, hSYS hs⟩ := Subtype.ext hxs
    refine ⟨⟨s, hs⟩, ?_⟩
    have h1 : signHom (φ ⟨y, hYS hy⟩) = 1 := (Gam.pow_three_iff _).mp (hYE y hy)
    rw [← hγ, hx, map_mul, map_mul, h1, one_mul]
    rfl
  obtain ⟨Tsyl, hTeq, -, -⟩ := exists_quotSylow hZ hQsyl
  set T' : Subgroup (↥L ⧸ Z) := ((S ⊓ L).subgroupOf L).map π with hT'def
  have hTsyl : IsSylowTwoOf T' ⊤ := by
    rw [← hTeq]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  let ρ : ↥S →* MulAut (↥L ⧸ Z) :=
    (PerfectAutomorphisms.centerQuotientHom ↥L).comp
      ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hSL))
  have hρ : ∀ (s : ↥S) (l : ↥L),
      ρ s (π l) = π (Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSL s) l) := fun s l =>
    PerfectAutomorphisms.onCenterQuotient_apply_mk _ l
  have hρcoe : ∀ (s : ↥S) (l : ↥L),
      ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSL s) l : ↥L) : G) =
        (s : G) * l * (s : G)⁻¹ := fun s l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hSL s) l
  let ψ : ↥S →* Outer (↥L ⧸ Z) := (QuotientGroup.mk' (inner (↥L ⧸ Z))).comp ρ
  have key : ∀ s : ↥S, ψ s = 1 → φ (Subgroup.inclusion hSYS s) = 1 := by
    intro s hs
    have hin : ρ s ∈ inner (↥L ⧸ Z) := (QuotientGroup.eq_one_iff _).mp hs
    obtain ⟨g, hg⟩ := hin
    obtain ⟨k, hk⟩ := hS2 s
    have hg2 : g ^ 2 ^ k = 1 := by
      apply hX.1
      rw [map_pow, hg, ← map_pow, hk, map_one, map_one]
    have hρT : ∀ x ∈ T', ρ s x ∈ T' := by
      rintro _ ⟨q, hq, rfl⟩
      have hq' : (q : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.mp hq
      rw [hρ]
      refine ⟨Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSL s) q,
        Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      rw [hρcoe]
      exact ⟨S.mul_mem (S.mul_mem s.2 hq'.1) (S.inv_mem s.2),
        (Subgroup.mem_normalizer_iff.mp (hSL s.2) q).mp hq'.2⟩
    have hgN : g ∈ Subgroup.normalizer (T' : Set (↥L ⧸ Z)) := by
      refine mem_normalizer_of_conj_le fun u hu => ?_
      have := hρT u hu
      rw [← hg] at this
      simpa [MulAut.conj_apply] using this
    have hgT : g ∈ T' := by
      have h2g : IsPGroup 2 (Subgroup.zpowers g) := isPGroup_zpowers_two hg2
      have hP : IsPGroup 2 ↥(T' ⊔ Subgroup.zpowers g) :=
        IsPGroup.to_sup_of_normal_left' (K1.isSylowTwoOf_top_iff.mp hTsyl).1 h2g
          (Subgroup.zpowers_le.mpr hgN)
      have heq := IsSylowTwoOf.eq_of_le hTsyl (le_sup_left : T' ≤ T' ⊔ Subgroup.zpowers g)
        le_top hP
      have hmem : g ∈ T' ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
      rwa [heq] at hmem
    obtain ⟨l, hl, hlg⟩ := hT hgT
    have hlY : (l : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hl
    have hwmem : (l : G)⁻¹ * (s : G) ∈ Yp ⊔ S :=
      (Yp ⊔ S).mul_mem ((Yp ⊔ S).inv_mem (hYS hlY)) (hSYS s.2)
    set w : ↥(Yp ⊔ S) := ⟨(l : G)⁻¹ * (s : G), hwmem⟩ with hwdef
    have hwc : ∀ e : Gam, e ^ 3 = 1 → φ w * e = e * φ w := by
      intro e he
      obtain ⟨y, hy, rfl⟩ := hF1 e he
      have hsy : (s : G) * y * (s : G)⁻¹ ∈ Yp :=
        (Subgroup.mem_normalizer_iff.mp (hSY s.2) y).mp hy
      have hπζ : π ((l⁻¹ : ↥L) * (⟨(s : G) * y * (s : G)⁻¹, hYL hsy⟩ : ↥L) * l *
          (⟨y, hYL hy⟩ : ↥L)⁻¹) = 1 := by
        have h0 := hρ s ⟨y, hYL hy⟩
        rw [← hg, MulAut.conj_apply] at h0
        have h1 : π (⟨(s : G) * y * (s : G)⁻¹, hYL hsy⟩ : ↥L) = g * π ⟨y, hYL hy⟩ * g⁻¹ := by
          rw [h0]
          congr 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, hlg]
        group
      have hζL : ((l : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * l * y⁻¹) ∈ pCoreOf 2 L := by
        rw [← hZ]
        have hzc : ((l⁻¹ : ↥L) * (⟨(s : G) * y * (s : G)⁻¹, hYL hsy⟩ : ↥L) * l *
            (⟨y, hYL hy⟩ : ↥L)⁻¹) ∈ Z := by
          rw [← hker]
          exact hπζ
        exact SBc2.mem_centerOf_iff_center.mpr hzc
      have hζmem : (l : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * l * y⁻¹ ∈ Yp ⊔ S :=
        hYS (Yp.mul_mem (Yp.mul_mem (Yp.mul_mem (Yp.inv_mem hlY) hsy) hlY) (Yp.inv_mem hy))
      have hζφ := hker₁ _ hζmem hζL
      have hcomm : w * (⟨y, hYS hy⟩ : ↥(Yp ⊔ S)) =
          ⟨(l : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * l * y⁻¹, hζmem⟩ * ⟨y, hYS hy⟩ * w := by
        apply Subtype.ext
        simp only [hwdef, Subgroup.coe_mul]
        group
      rw [← map_mul, ← map_mul, hcomm]
      simp only [map_mul, hζφ, one_mul]
    have hw3 : (φ w) ^ 3 = 1 := Gam.pow_three_of_centralizes hwc
    have hl3 : (φ ⟨(l : G), hYS hlY⟩) ^ 3 = 1 := hYE l hlY
    have hs_eq : (⟨(s : G), hSYS s.2⟩ : ↥(Yp ⊔ S)) = ⟨(l : G), hYS hlY⟩ * w := by
      apply Subtype.ext
      simp [hwdef]
    obtain ⟨k', hk'⟩ := hS2' s
    have hs3 : (φ ⟨(s : G), hSYS s.2⟩) ^ 3 = 1 := by
      rw [hs_eq, map_mul]
      exact Gam.mul_pow_three hl3 hw3
    exact hone _ k' hs3 hk'
  have hcyc : IsCyclic (↥S ⧸ ψ.ker) := by
    have : IsCyclic ↥ψ.range := Subgroup.isCyclic _
    exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange ψ).symm.surjective
  have hθk : ψ.ker ≤ θ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    show signHom (φ (Subgroup.inclusion hSYS s)) = 1
    rw [key s hs, map_one]
  let θ' : (↥S ⧸ ψ.ker) →* ℤˣ × ℤˣ := QuotientGroup.lift ψ.ker θ hθk
  have hθ's : Function.Surjective θ' := by
    intro p
    obtain ⟨s, hs⟩ := hθs p
    exact ⟨QuotientGroup.mk s, by simpa [θ'] using hs⟩
  exact not_isCyclic_units_prod (isCyclic_of_surjective θ' hθ's)

end Main

end CFSG.Quasithin.SzN27
