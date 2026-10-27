module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoR
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenExtra

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {t : MulAut W} {P : Subgroup (MulAut W)}

private theorem w16g_le_stabSub_of_stableUnder {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder X U) : X ≤ stabSub U := by
  intro x hx
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : x⁻¹ (x u) ∈ U := h x⁻¹ (X.inv_mem hx) (x u) hu
    simpa using h1
  · intro hu
    exact h x hx u hu

private theorem w16g_commute_of_mem_sup {A B : Subgroup (MulAut W)}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hcent : Subgroup.centralizer (A : Set (MulAut W)) ⊓
      Subgroup.centralizer (B : Set (MulAut W)) ≤
      Subgroup.centralizer (A ⊔ B : Subgroup (MulAut W)) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with hyA | hyB
    · exact hx.1 y hyA
    · exact hx.2 y hyB
  have hAcent : A ≤ Subgroup.centralizer (A ⊔ B : Subgroup (MulAut W)) := by
    intro a ha
    apply hcent
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]; intro y hy; exact (hA a ha y hy).symm
    · rw [Subgroup.mem_centralizer_iff]; intro y hy; exact (hAB a ha y hy).symm
  have hBcent : B ≤ Subgroup.centralizer (A ⊔ B : Subgroup (MulAut W)) := by
    intro b hb
    apply hcent
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]; intro y hy; exact hAB y hy b hb
    · rw [Subgroup.mem_centralizer_iff]; intro y hy; exact (hB b hb y hy).symm
  haveI : IsMulCommutative ↥(A ⊔ B) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp (sup_le hAcent hBcent)
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(A ⊔ B)) ⟨y, hy⟩)

private theorem w16g_isPOnePlusTwo_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsPOnePlusTwo p X) : IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  haveI : CFSG.IsExtraspecial p X := hX
  refine ⟨isExtraspecial_of_mulEquiv e.symm, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hc
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hp x, map_one]

private theorem w16g_subgroupOf_commutator {M : Type} [Group M] {H₁ H₂ K : Subgroup M}
    (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) :
    ⁅H₁.subgroupOf K, H₂.subgroupOf K⁆ = (⁅H₁, H₂⁆).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le h₁ h₂)]

private theorem w16g_map_inclusion_subgroupOf {W : Type} [CommGroup W]
    {G K : Subgroup (MulAut W)} (hGK : G ≤ K) {P : Subgroup (MulAut W)} (hPG : P ≤ G) :
    (P.subgroupOf G).map (Subgroup.inclusion hGK) = P.subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    exact ⟨⟨(x : MulAut W), hPG (Subgroup.mem_subgroupOf.mp hx)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), Subtype.ext rfl⟩

private theorem w16g_map_commSub_le {W : Type} [CommGroup W]
    {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    (x : G) :
    (commSub ⊤ (Subgroup.zpowers (σ x))).map V₀.subtype ≤
      commSub V₀ (Subgroup.zpowers (x : MulAut W)) := by
  rw [commSub, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro c ⟨d, hd, rfl⟩
  obtain ⟨y, hy, v, _, hdxy⟩ := hd
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  change (d : W) ∈ {c | ∃ z ∈ Subgroup.zpowers (x : MulAut W), ∃ w ∈ V₀, z w * w⁻¹ = c}
  refine ⟨(x : MulAut W) ^ n, Subgroup.zpow_mem_zpowers _ _, (v : W), v.2, ?_⟩
  have hleft : ((x : MulAut W) ^ n) (v : W) = (((σ x) ^ n) v : W) := by
    rw [← map_zpow, hσ, Subgroup.coe_zpow]
  rw [← hdxy, ← hn, Subgroup.coe_mul, Subgroup.coe_inv, hleft]

private theorem w16g_commSub_sup_left {V : Type} [CommGroup V]
    (A B : Subgroup V) (X : Subgroup (MulAut V)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have hsplit : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _
    rw [hsplit]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
      (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w16g_zpow_apply_eq_self {W : Type*} [CommGroup W] {a : MulAut W} {u : W}
    (h : a u = u) (m : ℤ) : (a ^ m) u = u := by
  have h1 : a ∈ MulAction.stabilizer (MulAut W) u := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have h2 := (MulAction.stabilizer (MulAut W) u).zpow_mem h1 m
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2

private theorem w16g_commutator_centSub_le {W : Type*} [CommGroup W] {U : Subgroup W}
    {X : Subgroup (MulAut W)} (hX : X ≤ stabSub U) : ⁅X, centSub U⁆ ≤ centSub U := by
  rw [Subgroup.commutator_le]
  intro x hx y hy u hu
  rw [commutatorElement_def]
  have hyu : y⁻¹ u = u := by
    have h1 : y⁻¹ (y u) = u := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rwa [mem_centSub.mp hy u hu] at h1
  have hxu : x⁻¹ u ∈ U := (mem_stabSub.mp (hX (X.inv_mem hx)) u).mpr hu
  have hyx : y (x⁻¹ u) = x⁻¹ u := mem_centSub.mp hy (x⁻¹ u) hxu
  change x (y (x⁻¹ (y⁻¹ u))) = u
  rw [hyu, hyx]
  exact x.apply_symm_apply u

private theorem w16g_eq_bot_of_isPGroup_of_commutator_eq_self {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] {P : Subgroup A} (hP : IsPGroup p ↥P) (hperf : ⁅P, P⁆ = P) :
    P = ⊥ := by
  by_contra hne
  have hnil : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hP
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (S := P)).mp hnil
  have hle : ∀ n, P ≤ P.lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        calc P = ⁅P, P⁆ := hperf.symm
          _ ≤ ⁅P.lowerCentralSeries n, P⁆ := Subgroup.commutator_mono ih le_rfl
  have hmem := hle c
  rw [hc] at hmem
  exact hne (le_bot_iff.mp hmem)

private theorem w16g_P_fixes_of_t_fixes {W : Type*} [CommGroup W] {t : MulAut W}
    {P : Subgroup (MulAut W)} (htP : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) {U : Subgroup W}
    (hPU : ∀ x ∈ P, ∀ u ∈ U, x u ∈ U) (htU : ∀ u ∈ U, t u = u) :
    ∀ x ∈ P, ∀ u ∈ U, x u = u := by
  have hX : P ≤ stabSub U := by
    intro x hx
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h1 : x⁻¹ (x u) ∈ U := hPU x⁻¹ (P.inv_mem hx) (x u) hu
      simpa using h1
    · intro hu
      exact hPU x hx u hu
  have hle : ⁅P, Subgroup.zpowers t⁆ ≤ P ⊓ centSub U := by
    refine le_inf (le_of_eq hc) ?_
    calc ⁅P, Subgroup.zpowers t⁆ ≤ ⁅P, centSub U⁆ :=
          Subgroup.commutator_mono_right (Subgroup.zpowers_le.mpr (mem_centSub.mpr htU))
      _ ≤ centSub U := w16g_commutator_centSub_le hX
  intro x hx u hu
  have hxK : x ∈ ⁅P, Subgroup.zpowers t⁆ := by rw [hc]; exact hx
  exact mem_centSub.mp (hle hxK).2 u hu

private theorem w16g_mem_sup_of_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hnorm : K ≤ Subgroup.normalizer H) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
        refine ⟨h1 * (k1 * h2 * k1⁻¹), H.mul_mem hh1 ?_, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hnorm hk1) h2).mp hh2
        · group
      inv_mem' := by
        rintro x ⟨h, hh, k, hk, rfl⟩
        refine ⟨k⁻¹ * h⁻¹ * k, ?_, k⁻¹, K.inv_mem hk, ?_⟩
        · simpa using
            (Subgroup.mem_normalizer_iff.mp (hnorm (K.inv_mem hk)) h⁻¹).mp (H.inv_mem hh)
        · group }
  have hle : H ⊔ K ≤ S :=
    sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
      (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
  exact hle hx

private theorem w16g_le_normalizer_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) : K ≤ Subgroup.normalizer H := by
  have hcent : K ≤ Subgroup.centralizer (H : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy
  exact hcent.trans (Subgroup.centralizer_le_normalizer (H : Set G))

private theorem w16g_zpowers_le_normalizer {G : Type*} [Group G] {P : Subgroup G} {t : G}
    (ht : t * t = 1) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) :
    Subgroup.zpowers t ≤ Subgroup.normalizer P := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hn x
  · intro hx
    have hh := hn (t * x * t⁻¹) hx
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
    have hxx : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [htinv]
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by simp only [mul_assoc]
        _ = x := by rw [ht, one_mul, mul_one]
    rwa [hxx] at hh

private theorem w16g_card_sup_of_inf_eq_bot {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hnorm : K ≤ Subgroup.normalizer H) (h : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : H × K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ heq
      have hEq : p1 * p2 = q1 * q2 := Subtype.ext_iff.mp heq
      have h1 : q1⁻¹ * p1 = q2 * p2⁻¹ := by
        have h3 : q1⁻¹ * (p1 * p2) = q2 := by
          rw [hEq, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [← h3]
        symm
        rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
      have hmemH : q1⁻¹ * p1 ∈ H := H.mul_mem (H.inv_mem hq1) hp1
      have hmemK : q2 * p2⁻¹ ∈ K := K.mul_mem hq2 (K.inv_mem hp2)
      have hmem : q1⁻¹ * p1 ∈ (⊥ : Subgroup G) := by
        rw [← h]
        exact ⟨hmemH, h1 ▸ hmemK⟩
      rw [Subgroup.mem_bot] at hmem
      have hp1' : p1 = q1 := by
        apply mul_left_cancel (a := q1⁻¹)
        rw [hmem, inv_mul_cancel]
      have hq2' : q2 = p2 := by
        have hz : q2 * p2⁻¹ = 1 := by rw [← h1]; exact hmem
        calc q2 = q2 * (p2⁻¹ * p2) := by rw [inv_mul_cancel, mul_one]
          _ = (q2 * p2⁻¹) * p2 := (mul_assoc q2 p2⁻¹ p2).symm
          _ = p2 := by rw [hz, one_mul]
      exact Prod.ext (Subtype.ext hp1') (Subtype.ext hq2').symm
    · intro x
      have hxsup : (x : G) ∈ H ⊔ K := x.2
      obtain ⟨h1, hh1, k1, hk1, hkx⟩ := w16g_mem_sup_of_normalizer hnorm hxsup
      exact ⟨(⟨h1, hh1⟩, ⟨k1, hk1⟩), Subtype.ext hkx⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

private theorem w16g_zpowers_eq_one_or_self {A : Type*} [Group A] {t : A} (ht : t * t = 1)
    {b : A} (hb : b ∈ Subgroup.zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, pow_two]
    exact ht
  have hmod := zpow_eq_zpow_emod k h2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hmod, h, zpow_zero]
  · right; rw [hmod, h, zpow_one]

private theorem w16g_restrict_setup {A : Subgroup W}
    (hA : StableUnder (P ⊔ Subgroup.zpowers t) A) (h : Cfg132 t P) :
    ∃ t' : MulAut ↥A,
      (∀ u : ↥A, (t' u : W) = t (u : W)) ∧ t' ^ 2 = 1 ∧
      ⁅autSub P A, Subgroup.zpowers t'⁆ = autSub P A ∧
      IsPGroup 3 ↥(autSub P A) ∧
      (∀ x ∈ autSub P A, t' * x * t'⁻¹ ∈ autSub P A) ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ rk ↥(commSub A (Subgroup.zpowers t)) ∧
      (t' = 1 ↔ ∀ u ∈ A, t u = u) := by
  classical
  let G : Subgroup (MulAut W) := P ⊔ Subgroup.zpowers t
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hPG : P ≤ G := le_sup_left
  have hGA : G ≤ stabSub A := w16g_le_stabSub_of_stableUnder hA
  have hPA : P ≤ stabSub A := hPG.trans hGA
  let σ : G →* MulAut ↥A := (resHom A).comp (Subgroup.inclusion hGA)
  have hσ : ∀ (x : G) (u : ↥A), ((σ x) u : W) = (x : MulAut W) (u : W) := by
    intro x u
    change (((resHom A) (Subgroup.inclusion hGA x)) u : W) = (x : MulAut W) (u : W)
    rw [resHom_apply]
    rfl
  have hmapσ : (P.subgroupOf G).map σ = autSub P A := by
    rw [show σ = (resHom A).comp (Subgroup.inclusion hGA) from rfl,
      ← Subgroup.map_map (K := P.subgroupOf G) (g := resHom A)
        (f := Subgroup.inclusion hGA)]
    rw [w16g_map_inclusion_subgroupOf hGA hPG]
    rfl
  let t' : MulAut ↥A := σ ⟨t, htG⟩
  have ht'coe : ∀ u : ↥A, (t' u : W) = t (u : W) := fun u => hσ ⟨t, htG⟩ u
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h1
    exact h1
  have ht'sq : t' ^ 2 = 1 := by
    change σ ⟨t, htG⟩ ^ 2 = 1
    rw [← map_pow]
    have h2 : (⟨t, htG⟩ : G) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, Subgroup.coe_one, pow_two] using htt
    rw [h2, map_one]
  have hzp : ((Subgroup.zpowers t).subgroupOf G).map σ = Subgroup.zpowers t' := by
    have h1 : (Subgroup.zpowers t).subgroupOf G = Subgroup.zpowers (⟨t, htG⟩ : G) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rw [h1, MonoidHom.map_zpowers]
  have hcA' : ⁅autSub P A, Subgroup.zpowers t'⁆ = autSub P A := by
    have hcommG : ⁅P.subgroupOf G, (Subgroup.zpowers t).subgroupOf G⁆ = P.subgroupOf G := by
      rw [w16g_subgroupOf_commutator hPG (Subgroup.zpowers_le.mpr htG), h.hc]
    have hmap := Subgroup.map_commutator (P.subgroupOf G)
      ((Subgroup.zpowers t).subgroupOf G) σ
    rw [hcommG, hmapσ, hzp] at hmap
    exact hmap.symm
  have hgrpA : IsPGroup 3 ↥(autSub P A) := by
    rw [autSub]
    exact (h.hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm).map (resHom A)
  have ht'norm : ∀ x ∈ autSub P A, t' * x * t'⁻¹ ∈ autSub P A := by
    intro x hx
    rw [← hmapσ] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨t, htG⟩ * q * ⟨t, htG⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change t * (q : MulAut W) * t⁻¹ ∈ P
      exact h.hn _ (Subgroup.mem_subgroupOf.mp hq)
    · rw [map_mul, map_mul, map_inv]
  have hle_rk : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤
      rk ↥(commSub A (Subgroup.zpowers t)) := by
    have hmap := w16g_map_commSub_le σ hσ ⟨t, htG⟩
    calc rk ↥(commSub ⊤ (Subgroup.zpowers t'))
        = rk ↥((commSub ⊤ (Subgroup.zpowers t')).map A.subtype) := by
            unfold rk
            rw [Subgroup.card_map_of_injective (K := commSub ⊤ (Subgroup.zpowers t'))
              (f := A.subtype) A.subtype_injective]
      _ ≤ rk ↥(commSub A (Subgroup.zpowers t)) := rk_mono hmap
  have ht'iff : t' = 1 ↔ ∀ u ∈ A, t u = u := by
    constructor
    · intro h1 u hu
      have h2 := congrArg (fun φ : MulAut ↥A => ((φ ⟨u, hu⟩ : ↥A) : W)) h1
      rw [ht'coe ⟨u, hu⟩] at h2
      simpa using h2
    · intro hfix
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      rw [ht'coe u]
      exact hfix (u : W) u.2
  exact ⟨t', ht'coe, ht'sq, hcA', hgrpA, ht'norm, hle_rk, ht'iff⟩

private theorem w16g_inf_centSub_ne_bot {A : Subgroup W}
    (hA : StableUnder (P ⊔ Subgroup.zpowers t) A) (hA1 : A ≠ ⊤)
    (h : Cfg132 t P) (hmin : MinFaith132 t P) : P ⊓ centSub A ≠ ⊥ := by
  classical
  obtain ⟨t', ht'coe, -, hcA', hgrpA, -, -, -⟩ := w16g_restrict_setup hA h
  have hPA : P ≤ stabSub A := le_sup_left.trans (w16g_le_stabSub_of_stableUnder hA)
  intro hbot
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h1
    exact h1
  have hnotfaith : ¬ (∀ y ∈ P ⊔ Subgroup.zpowers t, (∀ u ∈ A, y u = u) → y = 1) := by
    intro hf
    exact hA1 (hmin A hA hf)
  push Not at hnotfaith
  obtain ⟨y, hyG, hyfix, hyne⟩ := hnotfaith
  by_cases hyP : y ∈ P
  · have hmem : y ∈ P ⊓ centSub A := ⟨hyP, mem_centSub.mpr hyfix⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hyne hmem
  · obtain ⟨p, hp, q, hq, hy_eq⟩ :=
        w16g_mem_sup_of_normalizer (w16g_zpowers_le_normalizer htt h.hn) hyG
    have hq_t : q = t := by
      rcases w16g_zpowers_eq_one_or_self htt hq with h1 | h1
      · exfalso; apply hyP
        show y ∈ P
        rw [← hy_eq, h1, mul_one]
        exact hp
      · exact h1
    have ht'inv : t' = (resHom A ⟨p, hPA hp⟩)⁻¹ := by
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      have hp' : (p : MulAut W) (t' u : W) = (u : W) := by
        have h1 := hyfix (u : W) u.2
        rw [← hy_eq, hq_t, MulAut.mul_apply, ← ht'coe u] at h1
        exact h1
      calc (t' u : W) = (p : MulAut W).symm ((p : MulAut W) (t' u : W)) := by
            rw [MulEquiv.symm_apply_apply]
        _ = (p : MulAut W).symm (u : W) := by rw [hp']
        _ = (((resHom A ⟨p, hPA hp⟩)⁻¹) u : W) := by rw [MulAut.inv_apply]; rfl
    have ht'mem : t' ∈ autSub P A := by
      rw [ht'inv]
      exact (autSub P A).inv_mem (mem_autSub.mpr ⟨⟨p, hPA hp⟩, hp, rfl⟩)
    have hperf : ⁅autSub P A, autSub P A⁆ = autSub P A := by
      apply le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl)
      calc autSub P A = ⁅autSub P A, Subgroup.zpowers t'⁆ := hcA'.symm
        _ ≤ ⁅autSub P A, autSub P A⁆ :=
            Subgroup.commutator_mono_right (Subgroup.zpowers_le.mpr ht'mem)
    have hbot' : autSub P A = ⊥ := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact w16g_eq_bot_of_isPGroup_of_commutator_eq_self hgrpA hperf
    have hPle : P ≤ centSub A := by
      intro x hx
      rw [mem_centSub]
      intro u hu
      have hmem : resHom A ⟨x, hPA hx⟩ ∈ autSub P A := mem_autSub.mpr ⟨⟨x, hPA hx⟩, hx, rfl⟩
      rw [hbot'] at hmem
      have h1 : resHom A ⟨x, hPA hx⟩ = 1 := Subgroup.mem_bot.mp hmem
      have h2 := congrArg (fun φ : MulAut ↥A => ((φ ⟨u, hu⟩ : ↥A) : W)) h1
      simpa [resHom_apply] using h2
    have hle : P ≤ P ⊓ centSub A := le_inf le_rfl hPle
    rw [hbot] at hle
    exact h.hne (le_bot_iff.mp hle)

private theorem w16g_card_autSub_eq_three (h131 : W4Lem13_1) {A : Subgroup W}
    (hA : StableUnder (P ⊔ Subgroup.zpowers t) A) (h : Cfg132 t P)
    (hrkA : rk ↥(commSub A (Subgroup.zpowers t)) = 1)
    (hP'ne : autSub P A ≠ ⊥) : Nat.card (autSub P A) = 3 := by
  classical
  obtain ⟨t', ht'coe, ht'sq, hcA', hgrpA, ht'norm, hle_rk, ht'iff⟩ := w16g_restrict_setup hA h
  have hWA : ∀ u : ↥A, u ^ 2 = 1 := by
    intro u
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using h.hW (u : W)
  have ht'ne : t' ≠ 1 := by
    intro h1
    have hfixA : ∀ u ∈ A, t u = u := ht'iff.mp h1
    have hbot : commSub A (Subgroup.zpowers t) = ⊥ :=
      commSub_eq_bot_iff.mpr (fun u hu z hz => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact w16g_zpow_apply_eq_self (hfixA u hu) n)
    rw [hbot, rk_bot] at hrkA
    omega
  have ht'2 : orderOf t' = 2 := orderOf_eq_prime ht'sq ht'ne
  have hle1 : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 1 := hle_rk.trans (le_of_eq hrkA)
  have hne0 : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≠ 0 := by
    intro h0
    have hbot : commSub ⊤ (Subgroup.zpowers t') = ⊥ := (rk_eq_zero_iff hWA).mp h0
    apply ht'ne
    apply MulEquiv.ext
    intro u
    have hu : u ∈ fixV (Subgroup.zpowers t') := commSub_eq_bot_iff.mp hbot (Subgroup.mem_top u)
    simpa using mem_fixV_zpowers_iff.mp hu
  have hrk' : rk ↥(commSub ⊤ (Subgroup.zpowers t')) = 1 := by omega
  exact (h131 ↥A hWA t' ht'2 (by omega) 3 (autSub P A) Nat.prime_three hgrpA hP'ne
    ht'norm hcA').2 (Or.inr ⟨mem_stabSub.mpr (fun _ => Iff.rfl), hrk'⟩)

private theorem w16g_commutator_sup_zpowers {A B : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hA : ∀ x ∈ A, t * x * t⁻¹ ∈ A) (hB : ∀ x ∈ B, t * x * t⁻¹ ∈ B)
    (htt : t * t = 1) :
    ⁅A ⊔ B, Subgroup.zpowers t⁆ = ⁅A, Subgroup.zpowers t⁆ ⊔ ⁅B, Subgroup.zpowers t⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      w16g_mem_sup_of_normalizer (w16g_le_normalizer_of_commute hcomm) hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hAt : ⁅a, t⁆ ∈ A := by
      have hh := hA a⁻¹ (A.inv_mem ha)
      rw [show ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) by
        rw [commutatorElement_def]; simp only [mul_assoc]]
      exact A.mul_mem ha hh
    have hBt : ⁅b, t⁆ ∈ B := by
      have hh := hB b⁻¹ (B.inv_mem hb)
      rw [show ⁅b, t⁆ = b * (t * b⁻¹ * t⁻¹) by
        rw [commutatorElement_def]; simp only [mul_assoc]]
      exact B.mul_mem hb hh
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact htt
    have hmod := zpow_eq_zpow_emod n h2
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · rw [hmod, hn, zpow_zero]
      simp [commutatorElement_def]
    · rw [hmod, hn, zpow_one]
      have key : ⁅a * b, t⁆ = ⁅a, t⁆ * ⁅b, t⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
        have h1 : a * ⁅b, t⁆ * a⁻¹ = ⁅b, t⁆ := by
          rw [hcomm a ha ⁅b, t⁆ hBt, mul_assoc, mul_inv_cancel, mul_one]
        rw [h1]
        exact (hcomm ⁅a, t⁆ hAt ⁅b, t⁆ hBt).symm
      rw [key]
      exact Subgroup.mul_mem_sup
        (Subgroup.subset_closure ⟨a, ha, t, Subgroup.mem_zpowers t, rfl⟩)
        (Subgroup.subset_closure ⟨b, hb, t, Subgroup.mem_zpowers t, rfl⟩)
  · exact sup_le (Subgroup.commutator_mono_left le_sup_left)
      (Subgroup.commutator_mono_left le_sup_right)

private theorem w16g_decomp_aux (h131 : W4Lem13_1) (h : Cfg132 t P) (hmin : MinFaith132 t P)
    {A B : Subgroup W} (hA : StableUnder (P ⊔ Subgroup.zpowers t) A)
    (hB : StableUnder (P ⊔ Subgroup.zpowers t) B)
    (hd : A ⊓ B = ⊥) (hs : A ⊔ B = ⊤) (hA1 : A ≠ ⊤) (hB1 : B ≠ ⊤)
    (hrkA : rk ↥(commSub A (Subgroup.zpowers t)) = 1) :
    ∃ P₁ P₂ : Subgroup (MulAut W), P₁ ≤ P ∧ P₂ ≤ P ∧
      (∀ x ∈ P, x ∈ P₁ ↔ ∀ u ∈ A, x u = u) ∧ (∀ x ∈ P, x ∈ P₂ ↔ ∀ u ∈ B, x u = u) ∧
      Nat.card P₂ = 3 ∧ P₁ ⊓ P₂ = ⊥ ∧ P₁ ⊔ P₂ = P ∧ (∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) ∧
      (∀ x ∈ P₁, t * x * t⁻¹ ∈ P₁) ∧ (∀ x ∈ P₂, t * x * t⁻¹ ∈ P₂) ∧
      ⁅P₁, Subgroup.zpowers t⁆ = P₁ := by
  classical
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h1
    exact h1
  have hPA : P ≤ stabSub A := le_sup_left.trans (w16g_le_stabSub_of_stableUnder hA)
  have hPB : P ≤ stabSub B := le_sup_left.trans (w16g_le_stabSub_of_stableUnder hB)
  have hGA : P ⊔ Subgroup.zpowers t ≤ stabSub A := w16g_le_stabSub_of_stableUnder hA
  have hGB : P ⊔ Subgroup.zpowers t ≤ stabSub B := w16g_le_stabSub_of_stableUnder hB
  let P₁ : Subgroup (MulAut W) := P ⊓ centSub A
  let P₂ : Subgroup (MulAut W) := P ⊓ centSub B
  have hP₁le : P₁ ≤ P := inf_le_left
  have hP₂le : P₂ ≤ P := inf_le_left
  have hP₁iff : ∀ x ∈ P, x ∈ P₁ ↔ ∀ u ∈ A, x u = u := by
    intro x hx
    dsimp only [P₁]
    rw [Subgroup.mem_inf, mem_centSub]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have hP₂iff : ∀ x ∈ P, x ∈ P₂ ↔ ∀ u ∈ B, x u = u := by
    intro x hx
    dsimp only [P₂]
    rw [Subgroup.mem_inf, mem_centSub]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have hinf : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxA : ∀ u ∈ A, x u = u := (hP₁iff x hx.1.1).mp hx.1
    have hxB : ∀ u ∈ B, x u = u := (hP₂iff x hx.2.1).mp hx.2
    rw [Subgroup.mem_bot]
    apply MulEquiv.ext
    intro w
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (by rw [hs]; exact Subgroup.mem_top w)
    rw [← hab, map_mul, hxA a ha, hxB b hb, MulAut.one_apply]
  have hP₁ne : P₁ ≠ ⊥ := w16g_inf_centSub_ne_bot hA hA1 h hmin
  have hP₂ne : P₂ ≠ ⊥ := w16g_inf_centSub_ne_bot hB hB1 h hmin
  have hP'ne : autSub P A ≠ ⊥ := by
    intro hbot
    have hPle : P ≤ centSub A := by
      intro x hx
      rw [mem_centSub]
      intro u hu
      have hmem : resHom A ⟨x, hPA hx⟩ ∈ autSub P A := mem_autSub.mpr ⟨⟨x, hPA hx⟩, hx, rfl⟩
      rw [hbot] at hmem
      have h1 : resHom A ⟨x, hPA hx⟩ = 1 := Subgroup.mem_bot.mp hmem
      have h2 := congrArg (fun φ : MulAut ↥A => ((φ ⟨u, hu⟩ : ↥A) : W)) h1
      simpa [resHom_apply] using h2
    have hle : P ≤ P₁ := le_inf le_rfl hPle
    have hle2 : P₂ ≤ P₁ ⊓ P₂ := le_inf (hP₂le.trans hle) le_rfl
    rw [hinf] at hle2
    exact hP₂ne (le_bot_iff.mp hle2)
  have hcardAutA : Nat.card (autSub P A) = 3 := w16g_card_autSub_eq_three h131 hA h hrkA hP'ne
  have hPcard : Nat.card P = 3 * Nat.card P₁ := by
    have h1 := card_autSub_mul hPA
    rw [hcardAutA] at h1
    exact h1.symm
  have hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x := by
    intro x hx y hy
    apply MulEquiv.ext
    intro w
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (by rw [hs]; exact Subgroup.mem_top w)
    rw [← hab]
    have hxA : ∀ u ∈ A, x u = u := (hP₁iff x (hP₁le hx)).mp hx
    have hyB : ∀ u ∈ B, y u = u := (hP₂iff y (hP₂le hy)).mp hy
    have hyA : y a ∈ A := (mem_stabSub.mp (hPA (hP₂le hy)) a).mpr ha
    have hxB : x b ∈ B := (mem_stabSub.mp (hPB (hP₁le hx)) b).mpr hb
    calc (x * y) (a * b) = x (y (a * b)) := by rw [MulAut.mul_apply]
      _ = x (y a * y b) := by rw [map_mul]
      _ = x (y a) * x (y b) := by rw [map_mul]
      _ = (y a) * (x b) := by rw [hxA (y a) hyA, hyB b hb]
      _ = (y * x) (a * b) := by
            rw [MulAut.mul_apply, map_mul, map_mul, hxA a ha, hyB (x b) hxB]
  have hcard_sup : Nat.card ↥(P₁ ⊔ P₂) = Nat.card P₁ * Nat.card P₂ :=
    w16g_card_sup_of_inf_eq_bot (w16g_le_normalizer_of_commute hcomm) hinf
  have hP₂le3 : Nat.card P₂ ≤ 3 := by
    have hle_card : Nat.card ↥(P₁ ⊔ P₂) ≤ Nat.card P :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (sup_le hP₁le hP₂le))
    have h1 : Nat.card P₁ * Nat.card P₂ ≤ Nat.card P₁ * 3 := by
      rw [← hcard_sup, mul_comm (Nat.card P₁) 3, ← hPcard]
      exact hle_card
    exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP₂grp : IsPGroup 3 ↥P₂ := h.hP.to_le hP₂le
  have hP₂ge3 : 3 ≤ Nat.card P₂ := by
    have hdvd : 3 ∣ Nat.card P₂ := by
      rcases hP₂grp.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hP₂ne
      · exact h1
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hcardP₂ : Nat.card P₂ = 3 := le_antisymm hP₂le3 hP₂ge3
  have hsup : P₁ ⊔ P₂ = P := by
    have hle : P₁ ⊔ P₂ ≤ P := sup_le hP₁le hP₂le
    have hcard_eq : Nat.card ↥(P₁ ⊔ P₂) = Nat.card P := by
      rw [hcard_sup, hcardP₂, hPcard]
      ring
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq.symm)
  have hn₁ : ∀ x ∈ P₁, t * x * t⁻¹ ∈ P₁ := by
    intro x hx
    have hxP : x ∈ P := hP₁le hx
    have hxA : ∀ u ∈ A, x u = u := (hP₁iff x hxP).mp hx
    refine (hP₁iff (t * x * t⁻¹) (h.hn x hxP)).mpr ?_
    intro u hu
    have htA : t ∈ stabSub A := hGA (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have htu : t⁻¹ u ∈ A := (mem_stabSub.mp ((stabSub A).inv_mem htA) u).mpr hu
    calc (t * x * t⁻¹) u = t (x (t⁻¹ u)) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = t (t⁻¹ u) := by rw [hxA (t⁻¹ u) htu]
      _ = u := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hn₂ : ∀ x ∈ P₂, t * x * t⁻¹ ∈ P₂ := by
    intro x hx
    have hxP : x ∈ P := hP₂le hx
    have hxB : ∀ u ∈ B, x u = u := (hP₂iff x hxP).mp hx
    refine (hP₂iff (t * x * t⁻¹) (h.hn x hxP)).mpr ?_
    intro u hu
    have htB : t ∈ stabSub B := hGB (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have htu : t⁻¹ u ∈ B := (mem_stabSub.mp ((stabSub B).inv_mem htB) u).mpr hu
    calc (t * x * t⁻¹) u = t (x (t⁻¹ u)) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = t (t⁻¹ u) := by rw [hxB (t⁻¹ u) htu]
      _ = u := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have le_commA : ⁅P₁, Subgroup.zpowers t⁆ ≤ P₁ := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mp
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hn₁ x
    · intro hx
      have hh := hn₁ (t * x * t⁻¹) hx
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
      have hxx : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [htinv]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by
              simp only [mul_assoc]
          _ = x := by rw [htt, one_mul, mul_one]
      rwa [hxx] at hh
  have le_commB : ⁅P₂, Subgroup.zpowers t⁆ ≤ P₂ := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mp
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hn₂ x
    · intro hx
      have hh := hn₂ (t * x * t⁻¹) hx
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
      have hxx : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [htinv]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by
              simp only [mul_assoc]
          _ = x := by rw [htt, one_mul, mul_one]
      rwa [hxx] at hh
  have hsup_comm : ⁅P₁ ⊔ P₂, Subgroup.zpowers t⁆ =
      ⁅P₁, Subgroup.zpowers t⁆ ⊔ ⁅P₂, Subgroup.zpowers t⁆ :=
    w16g_commutator_sup_zpowers hcomm hn₁ hn₂ htt
  have hP_div : P = ⁅P₁, Subgroup.zpowers t⁆ ⊔ ⁅P₂, Subgroup.zpowers t⁆ := by
    rw [← h.hc, ← hsup, hsup_comm]
  have hc₁ : ⁅P₁, Subgroup.zpowers t⁆ = P₁ := by
    apply le_antisymm le_commA
    intro z hz
    have hzP : z ∈ P := hP₁le hz
    rw [hP_div] at hzP
    have hcommAB : ∀ x ∈ ⁅P₁, Subgroup.zpowers t⁆, ∀ y ∈ ⁅P₂, Subgroup.zpowers t⁆,
        x * y = y * x := fun x hx y hy => hcomm x (le_commA hx) y (le_commB hy)
    obtain ⟨u, hu, v, hv, huv⟩ :=
      w16g_mem_sup_of_normalizer (w16g_le_normalizer_of_commute hcommAB) hzP
    have hvP₁ : v ∈ P₁ := by
      have hvv : v = u⁻¹ * z := by rw [← huv, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hvv]
      exact P₁.mul_mem (P₁.inv_mem (le_commA hu)) hz
    have hvbot : v ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hinf]
      exact ⟨hvP₁, le_commB hv⟩
    rw [Subgroup.mem_bot] at hvbot
    rw [← huv, hvbot, mul_one]
    exact hu
  exact ⟨P₁, P₂, hP₁le, hP₂le, hP₁iff, hP₂iff, hcardP₂, hinf, hsup, hcomm, hn₁, hn₂, hc₁⟩

theorem w16h_decomp_split (h131 : W4Lem13_1) (h : Cfg132 t P) (hmin : MinFaith132 t P)
    (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {U U' : Subgroup W}
    (hU : StableUnder (P ⊔ Subgroup.zpowers t) U) (hU' : StableUnder (P ⊔ Subgroup.zpowers t) U')
    (hd : U ⊓ U' = ⊥) (hs : U ⊔ U' = ⊤) (hU1 : U ≠ ⊤) (hU2 : U' ≠ ⊤) :
    ∃ A B : Subgroup W, ((A = U ∧ B = U') ∨ (A = U' ∧ B = U)) ∧
      rk ↥(commSub A (Subgroup.zpowers t)) = 1 ∧
      ∃ P₁ P₂ : Subgroup (MulAut W), P₁ ≤ P ∧ P₂ ≤ P ∧
        (∀ x ∈ P, x ∈ P₁ ↔ ∀ u ∈ A, x u = u) ∧ (∀ x ∈ P, x ∈ P₂ ↔ ∀ u ∈ B, x u = u) ∧
        Nat.card P₂ = 3 ∧ P₁ ⊓ P₂ = ⊥ ∧ P₁ ⊔ P₂ = P ∧ (∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) ∧
        (∀ x ∈ P₁, t * x * t⁻¹ ∈ P₁) ∧ (∀ x ∈ P₂, t * x * t⁻¹ ∈ P₂) ∧
        ⁅P₁, Subgroup.zpowers t⁆ = P₁ := by
  classical
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h1
    exact h1
  have hPU : ∀ x ∈ P, ∀ u ∈ U, x u ∈ U := fun x hx u hu =>
    (mem_stabSub.mp ((w16g_le_stabSub_of_stableUnder hU) (Subgroup.mem_sup_left hx)) u).mpr hu
  have hPU' : ∀ x ∈ P, ∀ u ∈ U', x u ∈ U' := fun x hx u hu =>
    (mem_stabSub.mp ((w16g_le_stabSub_of_stableUnder hU') (Subgroup.mem_sup_left hx)) u).mpr hu
  have htU_false : ¬ ∀ u ∈ U, t u = u := by
    intro htUfix
    have hPfix := w16g_P_fixes_of_t_fixes h.hn h.hc hPU htUfix
    have hqU : ∀ q ∈ Subgroup.zpowers t, ∀ u ∈ U, q u = u := by
      intro q hq u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      exact w16g_zpow_apply_eq_self (htUfix u hu) n
    have hfaith : ∀ y ∈ P ⊔ Subgroup.zpowers t, (∀ u ∈ U', y u = u) → y = 1 := by
      intro y hy hfix
      obtain ⟨x, hx, q, hq, hyxq⟩ :=
        w16g_mem_sup_of_normalizer (w16g_zpowers_le_normalizer htt h.hn) hy
      subst hyxq
      apply MulEquiv.ext
      intro w
      obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup.mp (by rw [hs]; exact Subgroup.mem_top w)
      rw [← huv]
      have hfixv : x (q v) = v := by
        have h1 := hfix v hv
        rwa [MulAut.mul_apply] at h1
      calc (x * q) (u * v) = x (q (u * v)) := by rw [MulAut.mul_apply]
        _ = x (q u * q v) := by rw [map_mul]
        _ = x (q u) * x (q v) := by rw [map_mul]
        _ = x u * x (q v) := by rw [hqU q hq u hu]
        _ = u * v := by rw [hPfix x hx u hu, hfixv]
    exact hU2 (hmin U' hU' hfaith)
  have htU'_false : ¬ ∀ u ∈ U', t u = u := by
    intro htU'fix
    have hPfix := w16g_P_fixes_of_t_fixes h.hn h.hc hPU' htU'fix
    have hqU' : ∀ q ∈ Subgroup.zpowers t, ∀ u ∈ U', q u = u := by
      intro q hq u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      exact w16g_zpow_apply_eq_self (htU'fix u hu) n
    have hfaith : ∀ y ∈ P ⊔ Subgroup.zpowers t, (∀ u ∈ U, y u = u) → y = 1 := by
      intro y hy hfix
      obtain ⟨x, hx, q, hq, hyxq⟩ :=
        w16g_mem_sup_of_normalizer (w16g_zpowers_le_normalizer htt h.hn) hy
      subst hyxq
      apply MulEquiv.ext
      intro w
      obtain ⟨u, hu, v, hv, huv⟩ :=
        Subgroup.mem_sup.mp (by rw [← sup_comm, hs]; exact Subgroup.mem_top w)
      rw [← huv]
      have hfixv : x (q v) = v := by
        have h1 := hfix v hv
        rwa [MulAut.mul_apply] at h1
      calc (x * q) (u * v) = x (q (u * v)) := by rw [MulAut.mul_apply]
        _ = x (q u * q v) := by rw [map_mul]
        _ = x (q u) * x (q v) := by rw [map_mul]
        _ = x u * x (q v) := by rw [hqU' q hq u hu]
        _ = u * x (q v) := by rw [hPfix x hx u hu]
        _ = u * v := by rw [hfixv]
    exact hU1 (hmin U hU hfaith)
  have hrkUne : rk ↥(commSub U (Subgroup.zpowers t)) ≠ 0 := by
    intro h0
    apply htU_false
    intro u hu
    have hle : U ≤ fixV (Subgroup.zpowers t) :=
      commSub_eq_bot_iff.mp ((rk_eq_zero_iff h.hW).mp h0)
    exact mem_fixV_zpowers_iff.mp (hle hu)
  have hrkU'ne : rk ↥(commSub U' (Subgroup.zpowers t)) ≠ 0 := by
    intro h0
    apply htU'_false
    intro u hu
    have hle : U' ≤ fixV (Subgroup.zpowers t) :=
      commSub_eq_bot_iff.mp ((rk_eq_zero_iff h.hW).mp h0)
    exact mem_fixV_zpowers_iff.mp (hle hu)
  have hU_le : commSub U (Subgroup.zpowers t) ≤ U :=
    commSub_le_of_invariant (fun x hx w hw =>
      (mem_stabSub.mp (Subgroup.zpowers_le.mpr
        ((w16g_le_stabSub_of_stableUnder hU) (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
        hx) w).mpr hw)
  have hU'_le : commSub U' (Subgroup.zpowers t) ≤ U' :=
    commSub_le_of_invariant (fun x hx w hw =>
      (mem_stabSub.mp (Subgroup.zpowers_le.mpr
        ((w16g_le_stabSub_of_stableUnder hU') (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
        hx) w).mpr hw)
  have hdecomp : rk ↥(commSub U (Subgroup.zpowers t)) +
      rk ↥(commSub U' (Subgroup.zpowers t)) = rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    have hsup' : commSub ⊤ (Subgroup.zpowers t) =
        commSub U (Subgroup.zpowers t) ⊔ commSub U' (Subgroup.zpowers t) := by
      rw [← hs, w16g_commSub_sup_left]
    have hinf' : commSub U (Subgroup.zpowers t) ⊓ commSub U' (Subgroup.zpowers t) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_inf] at hu
      rw [← hd, Subgroup.mem_inf]
      exact ⟨hU_le hu.1, hU'_le hu.2⟩
    rw [hsup']
    have h1 := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers t))
      (commSub U' (Subgroup.zpowers t))
    rw [hinf', rk_bot, add_zero] at h1
    exact h1.symm
  have hchoice : rk ↥(commSub U (Subgroup.zpowers t)) = 1 ∨
      rk ↥(commSub U' (Subgroup.zpowers t)) = 1 := by
    have h1 : 1 ≤ rk ↥(commSub U (Subgroup.zpowers t)) := Nat.one_le_iff_ne_zero.mpr hrkUne
    have h2 : 1 ≤ rk ↥(commSub U' (Subgroup.zpowers t)) := Nat.one_le_iff_ne_zero.mpr hrkU'ne
    have h3 : rk ↥(commSub U (Subgroup.zpowers t)) +
        rk ↥(commSub U' (Subgroup.zpowers t)) ≤ 3 := by
      rw [hdecomp]; exact h.hrk
    omega
  rcases hchoice with h1 | h1
  · exact ⟨U, U', Or.inl ⟨rfl, rfl⟩, h1,
      w16g_decomp_aux h131 h hmin hU hU' hd hs hU1 hU2 h1⟩
  · refine ⟨U', U, Or.inr ⟨rfl, rfl⟩, h1, ?_⟩
    have hd' : U' ⊓ U = ⊥ := by rw [inf_comm]; exact hd
    have hs' : U' ⊔ U = ⊤ := by rw [sup_comm]; exact hs
    exact w16g_decomp_aux h131 h hmin hU' hU hd' hs' hU2 hU1 h1

theorem w16h_decomp_factor (hIH : W4Lem13_2ShapeLe (Nat.card P - 1)) (h131 : W4Lem13_1)
    (h : Cfg132 t P) {A B : Subgroup W}
    (hA : StableUnder (P ⊔ Subgroup.zpowers t) A) (hB : StableUnder (P ⊔ Subgroup.zpowers t) B)
    (hd : A ⊓ B = ⊥) (hs : A ⊔ B = ⊤) (hrkA : rk ↥(commSub A (Subgroup.zpowers t)) = 1)
    {P₁ P₂ : Subgroup (MulAut W)} (hP₁ : P₁ ≤ P) (hP₂ : P₂ ≤ P)
    (hP₁A : ∀ x ∈ P, x ∈ P₁ ↔ ∀ u ∈ A, x u = u) (hP₂B : ∀ x ∈ P, x ∈ P₂ ↔ ∀ u ∈ B, x u = u)
    (hcard : Nat.card P₂ = 3) (hinf : P₁ ⊓ P₂ = ⊥) (hsup : P₁ ⊔ P₂ = P)
    (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) (hn₁ : ∀ x ∈ P₁, t * x * t⁻¹ ∈ P₁)
    (hn₂ : ∀ x ∈ P₂, t * x * t⁻¹ ∈ P₂) (hc₁ : ⁅P₁, Subgroup.zpowers t⁆ = P₁)
    (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    IsPOnePlusTwo 3 ↥P₁ ∧ rk ↥(commSub B (Subgroup.zpowers t)) = 2 := by
  classical
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h1
    exact h1
  have hGB : (P ⊔ Subgroup.zpowers t) ≤ stabSub B :=
    w16g_le_stabSub_of_stableUnder hB
  have hGA : (P ⊔ Subgroup.zpowers t) ≤ stabSub A :=
    w16g_le_stabSub_of_stableUnder hA
  have htA : t ∈ stabSub A := hGA (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have htB : t ∈ stabSub B := hGB (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hP₁A' : P₁ ≤ stabSub A := (hP₁.trans le_sup_left).trans hGA
  have hP₁B' : P₁ ≤ stabSub B := (hP₁.trans le_sup_left).trans hGB
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP₂cyc : IsCyclic ↥P₂ := isCyclic_of_prime_card hcard
  haveI : IsCyclic ↥P₂ := hP₂cyc
  haveI : IsMulCommutative ↥P₂ := IsCyclic.isMulCommutative
  have hP₂abel : ∀ x ∈ P₂, ∀ y ∈ P₂, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥P₂) ⟨y, hy⟩)
  have hP₁nab : ¬ ∀ x ∈ P₁, ∀ y ∈ P₁, x * y = y * x := by
    intro hc₁
    apply hnab
    have hall := w16g_commute_of_mem_sup hcomm hc₁ hP₂abel
    intro x hx y hy
    rw [← hsup] at hx hy
    exact hall x hx y hy
  have hP₁ne : P₁ ≠ ⊥ := by
    intro hbot
    apply hnab
    intro x hx y hy
    have hxP : x ∈ P₂ := by
      have hx' : x ∈ P₁ ⊔ P₂ := by rw [hsup]; exact hx
      rwa [hbot, bot_sup_eq] at hx'
    have hyP : y ∈ P₂ := by
      have hy' : y ∈ P₁ ⊔ P₂ := by rw [hsup]; exact hy
      rwa [hbot, bot_sup_eq] at hy'
    exact congrArg Subtype.val (mul_comm' (⟨x, hxP⟩ : ↥P₂) ⟨y, hyP⟩)
  have hPcentB : P ⊓ centSub B = P₂ := by
    ext x
    rw [Subgroup.mem_inf, mem_centSub]
    constructor
    · rintro ⟨hxP, hxfix⟩
      exact (hP₂B x hxP).mpr hxfix
    · intro hx
      exact ⟨hP₂ hx, (hP₂B x (hP₂ hx)).mp hx⟩
  have hinfP₁B : P₁ ⊓ centSub B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxP₂ : x ∈ P₂ := by
      rw [← hPcentB, Subgroup.mem_inf]
      exact ⟨hP₁ hx.1, hx.2⟩
    have hmem : x ∈ P₁ ⊓ P₂ := ⟨hx.1, hxP₂⟩
    rw [hinf] at hmem
    exact hmem
  have hcardAut : Nat.card (autSub P₁ B) = Nat.card P₁ := by
    have h1 := card_autSub_mul hP₁B'
    rw [hinfP₁B, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hP'ne : autSub P₁ B ≠ ⊥ := by
    intro hbot
    apply hP₁ne
    have h1 : Nat.card P₁ = 1 := by rw [← hcardAut, hbot, Subgroup.card_bot]
    exact (Subgroup.card_eq_one).mp h1
  have hA_le : commSub A (Subgroup.zpowers t) ≤ A :=
    commSub_le_of_invariant (fun x hx w hw =>
      (mem_stabSub.mp (Subgroup.zpowers_le.mpr htA hx) w).mpr hw)
  have hB_le : commSub B (Subgroup.zpowers t) ≤ B :=
    commSub_le_of_invariant (fun x hx w hw =>
      (mem_stabSub.mp (Subgroup.zpowers_le.mpr htB hx) w).mpr hw)
  have hdecomp : rk ↥(commSub ⊤ (Subgroup.zpowers t)) =
      rk ↥(commSub A (Subgroup.zpowers t)) + rk ↥(commSub B (Subgroup.zpowers t)) := by
    have hsup' : commSub ⊤ (Subgroup.zpowers t) =
        commSub A (Subgroup.zpowers t) ⊔ commSub B (Subgroup.zpowers t) := by
      rw [← hs, w16g_commSub_sup_left]
    have hinf' : commSub A (Subgroup.zpowers t) ⊓ commSub B (Subgroup.zpowers t) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_inf] at hu
      rw [← hd, Subgroup.mem_inf]
      exact ⟨hA_le hu.1, hB_le hu.2⟩
    rw [hsup']
    have h1 := rk_sup_add_rk_inf (commSub A (Subgroup.zpowers t))
      (commSub B (Subgroup.zpowers t))
    rw [hinf', rk_bot, add_zero] at h1
    exact h1
  have hrkB_le2 : rk ↥(commSub B (Subgroup.zpowers t)) ≤ 2 := by
    have h1 := h.hrk
    rw [hdecomp, hrkA] at h1
    omega
  let G₁ : Subgroup (MulAut W) := P₁ ⊔ Subgroup.zpowers t
  have htG₁ : t ∈ G₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hP₁G₁ : P₁ ≤ G₁ := le_sup_left
  have hG₁B : G₁ ≤ stabSub B := by
    dsimp only [G₁]
    exact sup_le hP₁B' (Subgroup.zpowers_le.mpr htB)
  let σ : G₁ →* MulAut ↥B := (resHom B).comp (Subgroup.inclusion hG₁B)
  have hσ : ∀ (x : G₁) (u : ↥B), ((σ x) u : W) = (x : MulAut W) (u : W) := by
    intro x u
    change (((resHom B) (Subgroup.inclusion hG₁B x)) u : W) = (x : MulAut W) (u : W)
    rw [resHom_apply]
    rfl
  have hmapσ : (P₁.subgroupOf G₁).map σ = autSub P₁ B := by
    rw [show σ = (resHom B).comp (Subgroup.inclusion hG₁B) from rfl,
      ← Subgroup.map_map (K := P₁.subgroupOf G₁) (g := resHom B)
        (f := Subgroup.inclusion hG₁B)]
    rw [w16g_map_inclusion_subgroupOf hG₁B hP₁G₁]
    rfl
  let ρ : P₁ →* MulAut ↥B := σ.comp (Subgroup.inclusion hP₁G₁)
  have hρrange : ρ.range = autSub P₁ B := by
    rw [show ρ = σ.comp (Subgroup.inclusion hP₁G₁) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range hP₁G₁, hmapσ]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hcent : (x : MulAut W) ∈ centSub B := by
        rw [mem_centSub]
        intro u hu
        have h1 := congrArg (fun φ : MulAut ↥B => (φ ⟨u, hu⟩ : W)) hx
        have h2 : ((ρ x) ⟨u, hu⟩ : W) = (x : MulAut W) (u : W) := by
          change (((σ ⟨(x : MulAut W), hP₁G₁ x.2⟩) ⟨u, hu⟩) : W) = (x : MulAut W) (u : W)
          rw [hσ]
        rw [h2] at h1
        simpa using h1
      have hmem : (x : MulAut W) ∈ P₁ ⊓ centSub B := ⟨x.2, hcent⟩
      rw [hinfP₁B, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro hx
      rw [hx, map_one]
  let e : ↥P₁ ≃* ↥(autSub P₁ B) :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  have hP'grp : IsPGroup 3 ↥(autSub P₁ B) := (h.hP.to_le hP₁).of_equiv e
  let t' : MulAut ↥B := σ ⟨t, htG₁⟩
  have ht'sq : t' ^ 2 = 1 := by
    change σ ⟨t, htG₁⟩ ^ 2 = 1
    rw [← map_pow]
    have h2 : (⟨t, htG₁⟩ : G₁) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, Subgroup.coe_one, pow_two] using htt
    rw [h2, map_one]
  have hzp : ((Subgroup.zpowers t).subgroupOf G₁).map σ = Subgroup.zpowers t' := by
    have h1 : (Subgroup.zpowers t).subgroupOf G₁ = Subgroup.zpowers (⟨t, htG₁⟩ : G₁) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rw [h1, MonoidHom.map_zpowers]
  have hc' : ⁅autSub P₁ B, Subgroup.zpowers t'⁆ = autSub P₁ B := by
    have hcommG : ⁅P₁.subgroupOf G₁, (Subgroup.zpowers t).subgroupOf G₁⁆ =
        P₁.subgroupOf G₁ := by
      rw [w16g_subgroupOf_commutator hP₁G₁ (Subgroup.zpowers_le.mpr htG₁), hc₁]
    have hmap := Subgroup.map_commutator (P₁.subgroupOf G₁)
      ((Subgroup.zpowers t).subgroupOf G₁) σ
    rw [hcommG, hmapσ, hzp] at hmap
    exact hmap.symm
  have ht'norm : ∀ x ∈ autSub P₁ B, t' * x * t'⁻¹ ∈ autSub P₁ B := by
    intro x hx
    rw [← hmapσ] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨t, htG₁⟩ * q * ⟨t, htG₁⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change t * (q : MulAut W) * t⁻¹ ∈ P₁
      exact hn₁ _ (Subgroup.mem_subgroupOf.mp hq)
    · rw [map_mul, map_mul, map_inv]
  have ht'ne : t' ≠ 1 := by
    intro h1
    apply hP'ne
    have hzpbot : Subgroup.zpowers t' = ⊥ := by rw [h1, Subgroup.zpowers_one_eq_bot]
    calc autSub P₁ B = ⁅autSub P₁ B, Subgroup.zpowers t'⁆ := hc'.symm
      _ = ⁅autSub P₁ B, (⊥ : Subgroup (MulAut ↥B))⁆ := by rw [hzpbot]
      _ = ⊥ := Subgroup.commutator_bot_right _
  have ht'2 : orderOf t' = 2 := orderOf_eq_prime ht'sq ht'ne
  have hle_rk : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤
      rk ↥(commSub B (Subgroup.zpowers t)) := by
    have hmap := w16g_map_commSub_le σ hσ ⟨t, htG₁⟩
    calc rk ↥(commSub ⊤ (Subgroup.zpowers t'))
        = rk ↥((commSub ⊤ (Subgroup.zpowers t')).map B.subtype) := by
            unfold rk
            rw [Subgroup.card_map_of_injective (K := commSub ⊤ (Subgroup.zpowers t'))
              (f := B.subtype) B.subtype_injective]
      _ ≤ rk ↥(commSub B (Subgroup.zpowers t)) := rk_mono hmap
  have ht'rk : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 3 :=
    (hle_rk.trans hrkB_le2).trans (by norm_num)
  have hcardle : Nat.card ↥(autSub P₁ B) ≤ Nat.card P - 1 := by
    rw [hcardAut]
    have hssub : (P₁ : Set (MulAut W)) ⊂ (P : Set (MulAut W)) := by
      rw [ssubset_iff_subset_ne]
      refine ⟨hP₁, ?_⟩
      intro heq
      have hPP : P₁ = P := by
        ext x
        exact Set.ext_iff.mp heq x
      have hP₂le : P₂ ≤ P₁ := by
        intro x hx
        have hxP : x ∈ P := hP₂ hx
        rwa [← hPP] at hxP
      have hle : P₂ ≤ ⊥ := by
        rw [← hinf]
        exact le_inf hP₂le le_rfl
      have hbot : P₂ = ⊥ := le_bot_iff.mp hle
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    have hlt : Nat.card ↥P₁ < Nat.card ↥P := Set.Finite.card_lt_card (Set.toFinite _) hssub
    omega
  have hW'2 : ∀ w : ↥B, w ^ 2 = 1 := by
    intro w
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using h.hW (w : W)
  have hconc := hIH ↥B hW'2 t' ht'2 ht'rk 3 (autSub P₁ B) Nat.prime_three hP'grp hP'ne
    ht'norm hc' hcardle
  have hP'nab' : ¬ ∀ x ∈ autSub P₁ B, ∀ y ∈ autSub P₁ B, x * y = y * x := by
    intro hab
    apply hP₁nab
    intro x hx y hy
    have h1 : (e ⟨x, hx⟩ : MulAut ↥B) * (e ⟨y, hy⟩ : MulAut ↥B) =
        (e ⟨y, hy⟩ : MulAut ↥B) * (e ⟨x, hx⟩ : MulAut ↥B) :=
      hab (e ⟨x, hx⟩ : MulAut ↥B) (e ⟨x, hx⟩).2 (e ⟨y, hy⟩ : MulAut ↥B) (e ⟨y, hy⟩).2
    have h2 : e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [map_mul, map_mul]
      exact h1
    exact congrArg (fun z : ↥P₁ => (z : MulAut W)) (e.injective h2)
  have hP'1 : IsPOnePlusTwo 3 ↥(autSub P₁ B) := by
    rcases hconc with ⟨hcyc, _⟩ | ⟨k, _, hE⟩ | hP1 | ⟨hZ, hrk3⟩
    · haveI : IsCyclic ↥(autSub P₁ B) := hcyc
      haveI : IsMulCommutative ↥(autSub P₁ B) := IsCyclic.isMulCommutative
      exact absurd (by
        intro x hx y hy
        exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(autSub P₁ B)) ⟨y, hy⟩)) hP'nab'
    · obtain ⟨φ⟩ := hE
      exact absurd (by
        intro x hx y hy
        have h1 : φ ⟨x, hx⟩ * φ ⟨y, hy⟩ = φ ⟨y, hy⟩ * φ ⟨x, hx⟩ := mul_comm _ _
        have h2 : φ (⟨x, hx⟩ * ⟨y, hy⟩) = φ (⟨y, hy⟩ * ⟨x, hx⟩) := by
          rw [map_mul, map_mul]
          exact h1
        exact congrArg Subtype.val (φ.injective h2)) hP'nab'
    · exact hP1
    · exact absurd hrk3 (by
        have h2 : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 2 := hle_rk.trans hrkB_le2
        omega)
  have hP1_ext : IsPOnePlusTwo 3 ↥P₁ := w16g_isPOnePlusTwo_of_mulEquiv e.symm hP'1
  have hne_bot : commSub B (Subgroup.zpowers t) ≠ ⊥ := by
    intro hbot
    apply ht'ne
    have hfix : B ≤ fixV (Subgroup.zpowers t) := commSub_eq_bot_iff.mp hbot
    ext u
    have h1 : ((t' u : ↥B) : W) = t (u : W) := hσ ⟨t, htG₁⟩ u
    have h2 : t (u : W) = (u : W) := mem_fixV_zpowers_iff.mp (hfix u.2)
    simpa using Subtype.ext (h1.trans h2)
  have hrkB2 : rk ↥(commSub B (Subgroup.zpowers t)) = 2 := by
    refine le_antisymm hrkB_le2 ?_
    by_contra hlt
    push Not at hlt
    have hge1 : 1 ≤ rk ↥(commSub B (Subgroup.zpowers t)) := by
      by_contra h0
      push Not at h0
      have hz : rk ↥(commSub B (Subgroup.zpowers t)) = 0 := by omega
      exact hne_bot ((rk_eq_zero_iff h.hW).mp hz)
    have hrk1 : rk ↥(commSub B (Subgroup.zpowers t)) = 1 := by omega
    have hrk1' : rk ↥(commSub ⊤ (Subgroup.zpowers t')) = 1 := by
      have hge : 1 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t')) := by
        by_contra h0
        push Not at h0
        have hz : rk ↥(commSub ⊤ (Subgroup.zpowers t')) = 0 := by omega
        have hbot : commSub ⊤ (Subgroup.zpowers t') = ⊥ := (rk_eq_zero_iff hW'2).mp hz
        apply ht'ne
        have hfix : fixV (Subgroup.zpowers t') = ⊤ :=
          eq_top_iff.mpr (commSub_eq_bot_iff.mp hbot)
        ext u
        have hu : u ∈ fixV (Subgroup.zpowers t') := by rw [hfix]; exact Subgroup.mem_top u
        simpa using mem_fixV_zpowers_iff.mp hu
      have hle : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 1 :=
        hle_rk.trans (le_of_eq hrk1)
      omega
    have htrans : InducesTransvection t' ⊤ := by
      refine ⟨?_, hrk1'⟩
      rw [mem_stabSub]
      intro u
      simp
    have h131' := (h131 ↥B hW'2 t' ht'2 ht'rk 3 (autSub P₁ B) Nat.prime_three hP'grp hP'ne
      ht'norm hc').2 (Or.inr htrans)
    have hcard27 : Nat.card ↥(autSub P₁ B) = 27 := by rw [hP'1.2.1]; norm_num
    omega
  exact ⟨hP1_ext, hrkB2⟩

private noncomputable def w16g_prodEquivOfCommute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    H × K ≃* ↥(H ⊔ K) := by
  let φ : H × K →* ↥(H ⊔ K) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        let a1 : G := p.1
        let b1 : G := q.1
        let a2 : G := p.2
        let b2 : G := q.2
        have hc : b1 * a2 = a2 * b1 := hcomm q.1 q.1.2 p.2 p.2.2
        change a1 * b1 * (a2 * b2) = (a1 * a2) * (b1 * b2)
        calc a1 * b1 * (a2 * b2)
            = a1 * (b1 * (a2 * b2)) := mul_assoc a1 b1 (a2 * b2)
          _ = a1 * ((b1 * a2) * b2) := by rw [mul_assoc b1 a2 b2]
          _ = a1 * ((a2 * b1) * b2) := by rw [hc]
          _ = a1 * (a2 * (b1 * b2)) := by rw [mul_assoc a2 b1 b2]
          _ = (a1 * a2) * (b1 * b2) := (mul_assoc a1 a2 (b1 * b2)).symm }
  exact MulEquiv.ofBijective φ (by
    constructor
    · rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ heq
      have hEq : p1 * p2 = q1 * q2 := Subtype.ext_iff.mp heq
      have h1 : q1⁻¹ * p1 = q2 * p2⁻¹ := by
        have h3 : q1⁻¹ * (p1 * p2) = q2 := by
          rw [hEq, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [← h3]
        symm
        rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
      have hmemH : q1⁻¹ * p1 ∈ H := H.mul_mem (H.inv_mem hq1) hp1
      have hmemK : q2 * p2⁻¹ ∈ K := K.mul_mem hq2 (K.inv_mem hp2)
      have hmem : q1⁻¹ * p1 ∈ (⊥ : Subgroup G) := by
        rw [← hinf]
        exact ⟨hmemH, h1 ▸ hmemK⟩
      rw [Subgroup.mem_bot] at hmem
      have hp1' : p1 = q1 := by
        apply mul_left_cancel (a := q1⁻¹)
        rw [hmem, inv_mul_cancel]
      have hq2' : q2 = p2 := by
        have hz : q2 * p2⁻¹ = 1 := by rw [← h1]; exact hmem
        calc q2 = q2 * (p2⁻¹ * p2) := by rw [inv_mul_cancel, mul_one]
          _ = (q2 * p2⁻¹) * p2 := (mul_assoc q2 p2⁻¹ p2).symm
          _ = p2 := by rw [hz, one_mul]
      exact Prod.ext (Subtype.ext hp1') (Subtype.ext hq2').symm
    · intro x
      have hxsup : (x : G) ∈ H ⊔ K := x.2
      obtain ⟨h, hh, k, hk, hkx⟩ :=
        w16g_mem_sup_of_normalizer (w16g_le_normalizer_of_commute hcomm) hxsup
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hkx⟩)

private theorem w16g_commSub_le_of_act_le {A : Subgroup W} {Q X : Subgroup (MulAut W)}
    (h : ∀ q ∈ Q, ∃ x ∈ X, ∀ u ∈ A, q u = x u) : commSub A Q ≤ commSub A X := by
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨q, hq, u, hu, hqcu⟩
  obtain ⟨x, hx, hact⟩ := h q hq
  rw [← hqcu]
  exact Subgroup.subset_closure ⟨x, hx, u, hu, by rw [hact u hu]⟩

private theorem w16g_exists_act_eq_right {B : Subgroup W} {P₁ P₂ : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x)
    (hP₂B : ∀ x ∈ P₂, ∀ u ∈ B, x u = u)
    (hP₁B : ∀ x ∈ P₁, ∀ u ∈ B, x u ∈ B)
    {q : MulAut W} (hq : q ∈ P₁ ⊔ P₂) :
    ∃ a ∈ P₁, ∀ u ∈ B, q u = a u := by
  obtain ⟨a, ha, b, hb, hqab⟩ :=
    w16g_mem_sup_of_normalizer (w16g_le_normalizer_of_commute hcomm) hq
  refine ⟨a, ha, fun u hu => ?_⟩
  rw [← hqab, MulAut.mul_apply, hP₂B b hb u hu]

private theorem w16g_map_commSub_autSub {W : Type} [CommGroup W]
    {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    {X : Subgroup (MulAut W)} (hXG : X ≤ G) :
    (commSub ⊤ ((X.subgroupOf G).map σ)).map V₀.subtype = commSub V₀ X := by
  apply le_antisymm
  · rw [commSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro c ⟨d, hd, rfl⟩
    obtain ⟨y, hy, w, -, hdyw⟩ := hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxX : (x : MulAut W) ∈ X := Subgroup.mem_subgroupOf.mp hx
    rw [commSub]
    apply Subgroup.subset_closure
    refine ⟨(x : MulAut W), hxX, (w : W), w.2, ?_⟩
    have h1 : (((σ x) w * w⁻¹ : ↥V₀) : W) = (d : W) := by rw [hdyw]
    change (x : MulAut W) (w : W) * (w : W)⁻¹ = (d : W)
    rw [← h1, Subgroup.coe_mul, Subgroup.coe_inv]
    exact congrArg (fun z : W => z * (w : W)⁻¹) (hσ x w).symm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    rw [commSub, MonoidHom.map_closure]
    apply Subgroup.subset_closure
    refine ⟨σ ⟨x, hXG hx⟩ ⟨w, hw⟩ * ⟨w, hw⟩⁻¹, ?_, ?_⟩
    · exact ⟨σ ⟨x, hXG hx⟩, Subgroup.mem_map.mpr
        ⟨⟨x, hXG hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, ⟨w, hw⟩, Subgroup.mem_top _, rfl⟩
    · change (((σ ⟨x, hXG hx⟩) ⟨w, hw⟩ : ↥V₀) : W) * (w : W)⁻¹ =
        (x : MulAut W) (w : W) * (w : W)⁻¹
      exact congrArg (fun z : W => z * (w : W)⁻¹) (hσ ⟨x, hXG hx⟩ ⟨w, hw⟩)

private theorem w16g_restrict_rk_six (hMin : W4Lem13_2MinLe 27) (h131 : W4Lem13_1)
    (h : Cfg132 t P) {B : Subgroup W}
    (hB : StableUnder (P ⊔ Subgroup.zpowers t) B)
    {P₁ : Subgroup (MulAut W)} (hP₁ : P₁ ≤ P)
    (hn₁ : ∀ x ∈ P₁, t * x * t⁻¹ ∈ P₁) (hc₁ : ⁅P₁, Subgroup.zpowers t⁆ = P₁)
    (hext : IsPOnePlusTwo 3 ↥P₁) (hinfP₁B : P₁ ⊓ centSub B = ⊥)
    (hrkB2 : rk ↥(commSub B (Subgroup.zpowers t)) = 2) :
    rk ↥(commSub B P₁) = 6 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGB : (P ⊔ Subgroup.zpowers t) ≤ stabSub B := w16g_le_stabSub_of_stableUnder hB
  have htB : t ∈ stabSub B := hGB (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hP₁B' : P₁ ≤ stabSub B := (hP₁.trans le_sup_left).trans hGB
  let G₁ : Subgroup (MulAut W) := P₁ ⊔ Subgroup.zpowers t
  have htG₁ : t ∈ G₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hP₁G₁ : P₁ ≤ G₁ := le_sup_left
  have hG₁B : G₁ ≤ stabSub B := by
    dsimp only [G₁]
    exact sup_le hP₁B' (Subgroup.zpowers_le.mpr htB)
  let σ : G₁ →* MulAut ↥B := (resHom B).comp (Subgroup.inclusion hG₁B)
  have hσ : ∀ (x : G₁) (u : ↥B), ((σ x) u : W) = (x : MulAut W) (u : W) := by
    intro x u
    change (((resHom B) (Subgroup.inclusion hG₁B x)) u : W) = (x : MulAut W) (u : W)
    rw [resHom_apply]
    rfl
  have hmapσ : (P₁.subgroupOf G₁).map σ = autSub P₁ B := by
    rw [show σ = (resHom B).comp (Subgroup.inclusion hG₁B) from rfl,
      ← Subgroup.map_map (K := P₁.subgroupOf G₁) (g := resHom B)
        (f := Subgroup.inclusion hG₁B)]
    rw [w16g_map_inclusion_subgroupOf hG₁B hP₁G₁]
    rfl
  let ρ : P₁ →* MulAut ↥B := σ.comp (Subgroup.inclusion hP₁G₁)
  have hρrange : ρ.range = autSub P₁ B := by
    rw [show ρ = σ.comp (Subgroup.inclusion hP₁G₁) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range hP₁G₁, hmapσ]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hcent : (x : MulAut W) ∈ centSub B := by
        rw [mem_centSub]
        intro u hu
        have h1 := congrArg (fun φ : MulAut ↥B => (φ ⟨u, hu⟩ : W)) hx
        have h2 : ((ρ x) ⟨u, hu⟩ : W) = (x : MulAut W) (u : W) := by
          change (((σ ⟨(x : MulAut W), hP₁G₁ x.2⟩) ⟨u, hu⟩) : W) = (x : MulAut W) (u : W)
          rw [hσ]
        rw [h2] at h1
        simpa using h1
      have hmem : (x : MulAut W) ∈ P₁ ⊓ centSub B := ⟨x.2, hcent⟩
      rw [hinfP₁B, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro hx
      rw [hx, map_one]
  let e : ↥P₁ ≃* ↥(autSub P₁ B) :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  have hP'grp : IsPGroup 3 ↥(autSub P₁ B) := (h.hP.to_le hP₁).of_equiv e
  have hP'ne : autSub P₁ B ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P₁ = 1 := by
      rw [Nat.card_congr e.toEquiv, hbot, Subgroup.card_bot]
    rw [hext.2.1] at h1
    norm_num at h1
  have hP'ext : IsPOnePlusTwo 3 ↥(autSub P₁ B) := w16g_isPOnePlusTwo_of_mulEquiv e hext
  let t' : MulAut ↥B := σ ⟨t, htG₁⟩
  have ht'sq : t' ^ 2 = 1 := by
    change σ ⟨t, htG₁⟩ ^ 2 = 1
    rw [← map_pow]
    have h2 : (⟨t, htG₁⟩ : G₁) ^ 2 = 1 := by
      apply Subtype.ext
      have htt : t * t = 1 := by
        have h1 := pow_orderOf_eq_one t
        rw [h.ht, pow_two] at h1
        exact h1
      simpa [Subgroup.coe_pow, Subgroup.coe_one, pow_two] using htt
    rw [h2, map_one]
  have hzp : ((Subgroup.zpowers t).subgroupOf G₁).map σ = Subgroup.zpowers t' := by
    have h1 : (Subgroup.zpowers t).subgroupOf G₁ = Subgroup.zpowers (⟨t, htG₁⟩ : G₁) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rw [h1, MonoidHom.map_zpowers]
  have hc' : ⁅autSub P₁ B, Subgroup.zpowers t'⁆ = autSub P₁ B := by
    have hcommG : ⁅P₁.subgroupOf G₁, (Subgroup.zpowers t).subgroupOf G₁⁆ = P₁.subgroupOf G₁ := by
      rw [w16g_subgroupOf_commutator hP₁G₁ (Subgroup.zpowers_le.mpr htG₁), hc₁]
    have hmap := Subgroup.map_commutator (P₁.subgroupOf G₁)
      ((Subgroup.zpowers t).subgroupOf G₁) σ
    rw [hcommG, hmapσ, hzp] at hmap
    exact hmap.symm
  have ht'norm : ∀ x ∈ autSub P₁ B, t' * x * t'⁻¹ ∈ autSub P₁ B := by
    intro x hx
    rw [← hmapσ] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨t, htG₁⟩ * q * ⟨t, htG₁⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change t * (q : MulAut W) * t⁻¹ ∈ P₁
      exact hn₁ _ (Subgroup.mem_subgroupOf.mp hq)
    · rw [map_mul, map_mul, map_inv]
  have ht'ne : t' ≠ 1 := by
    intro h1
    apply hP'ne
    have hzpbot : Subgroup.zpowers t' = ⊥ := by rw [h1, Subgroup.zpowers_one_eq_bot]
    calc autSub P₁ B = ⁅autSub P₁ B, Subgroup.zpowers t'⁆ := hc'.symm
      _ = ⁅autSub P₁ B, (⊥ : Subgroup (MulAut ↥B))⁆ := by rw [hzpbot]
      _ = ⊥ := Subgroup.commutator_bot_right _
  have ht'2 : orderOf t' = 2 := orderOf_eq_prime ht'sq ht'ne
  have hle_rk : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤
      rk ↥(commSub B (Subgroup.zpowers t)) := by
    have hmap := w16g_map_commSub_le σ hσ ⟨t, htG₁⟩
    calc rk ↥(commSub ⊤ (Subgroup.zpowers t'))
        = rk ↥((commSub ⊤ (Subgroup.zpowers t')).map B.subtype) := by
            unfold rk
            rw [Subgroup.card_map_of_injective (K := commSub ⊤ (Subgroup.zpowers t'))
              (f := B.subtype) B.subtype_injective]
      _ ≤ rk ↥(commSub B (Subgroup.zpowers t)) := rk_mono hmap
  have hW'2 : ∀ w : ↥B, w ^ 2 = 1 := by
    intro w
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using h.hW (w : W)
  have hcfg : Cfg132 t' (autSub P₁ B) :=
    { hW := hW'2
      ht := ht'2
      hrk := by
        have h1 : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 2 := hle_rk.trans (le_of_eq hrkB2)
        omega
      hP := hP'grp
      hne := hP'ne
      hn := ht'norm
      hc := hc' }
  have hsix : rk ↥(commSub ⊤ (autSub P₁ B)) = 6 :=
    (w16h_rk_six_or_eight hMin h131 hcfg hP'ext).2 (hle_rk.trans (le_of_eq hrkB2))
  have hmap_comm : (commSub ⊤ (autSub P₁ B)).map B.subtype = commSub B P₁ := by
    rw [← hmapσ]
    exact w16g_map_commSub_autSub σ hσ hP₁G₁
  rw [← hmap_comm]
  unfold rk
  rw [Subgroup.card_map_of_injective B.subtype_injective]
  exact hsix

theorem w16h_decomp (hIH : W4Lem13_2ShapeLe (Nat.card P - 1))
    (hMin : 27 < Nat.card P → W4Lem13_2MinLe 27) (h131 : W4Lem13_1) (h : Cfg132 t P)
    (hmin : MinFaith132 t P)
    (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {U U' : Subgroup W}
    (hU : StableUnder (P ⊔ Subgroup.zpowers t) U) (hU' : StableUnder (P ⊔ Subgroup.zpowers t) U')
    (hd : U ⊓ U' = ⊥) (hs : U ⊔ U' = ⊤) (hU1 : U ≠ ⊤) (hU2 : U' ≠ ⊤) :
    IsZ3TimesPOnePlusTwo ↥P ∧ rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 ∧
      ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub ⊤ Q) = 6 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, B, hAB, hrkA, P₁, P₂, hP₁, hP₂, hP₁A, hP₂B, hcardP₂, hinfP₁P₂, hsupP₁P₂,
    hcomm, hn₁, hn₂, hc₁⟩ :=
    w16h_decomp_split h131 h hmin hnab hU hU' hd hs hU1 hU2
  have hA : StableUnder (P ⊔ Subgroup.zpowers t) A := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hB : StableUnder (P ⊔ Subgroup.zpowers t) B := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hdAB : A ⊓ B = ⊥ := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hd
    · rw [inf_comm]; exact hd
  have hsAB : A ⊔ B = ⊤ := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hs
    · rw [sup_comm]; exact hs
  obtain ⟨hP1ext, hrkB2⟩ :=
    w16h_decomp_factor hIH h131 h hA hB hdAB hsAB hrkA hP₁ hP₂ hP₁A hP₂B hcardP₂ hinfP₁P₂
      hsupP₁P₂ hcomm hn₁ hn₂ hc₁ hnab
  have hcardP₁ : Nat.card ↥P₁ = 27 := by rw [hP1ext.2.1]; norm_num
  have hP₁ne : P₁ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P₁ = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcardP₁] at h1
    norm_num at h1
  have hcardP : Nat.card P = 81 := by
    have hcard := w16g_card_sup_of_inf_eq_bot (w16g_le_normalizer_of_commute hcomm) hinfP₁P₂
    rw [hsupP₁P₂, hcardP₁, hcardP₂] at hcard
    norm_num at hcard
    exact hcard
  have hMin' : W4Lem13_2MinLe 27 := hMin (by rw [hcardP]; norm_num)
  have hrkt : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
    have htA : t ∈ stabSub A :=
      w16g_le_stabSub_of_stableUnder hA (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have htB : t ∈ stabSub B :=
      w16g_le_stabSub_of_stableUnder hB (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hA_le : commSub A (Subgroup.zpowers t) ≤ A :=
      commSub_le_of_invariant (fun x hx w hw =>
        (mem_stabSub.mp (Subgroup.zpowers_le.mpr htA hx) w).mpr hw)
    have hB_le : commSub B (Subgroup.zpowers t) ≤ B :=
      commSub_le_of_invariant (fun x hx w hw =>
        (mem_stabSub.mp (Subgroup.zpowers_le.mpr htB hx) w).mpr hw)
    have hsup' : commSub ⊤ (Subgroup.zpowers t) =
        commSub A (Subgroup.zpowers t) ⊔ commSub B (Subgroup.zpowers t) := by
      rw [← hsAB, w16g_commSub_sup_left]
    have hinf' : commSub A (Subgroup.zpowers t) ⊓ commSub B (Subgroup.zpowers t) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_inf] at hu
      rw [← hdAB, Subgroup.mem_inf]
      exact ⟨hA_le hu.1, hB_le hu.2⟩
    rw [hsup']
    have h1 := rk_sup_add_rk_inf (commSub A (Subgroup.zpowers t))
      (commSub B (Subgroup.zpowers t))
    rw [hinf', rk_bot, add_zero] at h1
    rw [h1, hrkA, hrkB2]
  have hZ3 : IsZ3TimesPOnePlusTwo ↥P := by
    have hP2equiv : ↥P₂ ≃* Multiplicative (ZMod 3) := by
      apply mulEquivOfPrimeCardEq (p := 3)
      · exact hcardP₂
      · exact Nat.card_zmod 3
    refine ⟨↥P₁, inferInstance, hP1ext, ⟨?_⟩⟩
    exact ((w16g_prodEquivOfCommute hcomm hinfP₁P₂).trans
      (MulEquiv.subgroupCongr hsupP₁P₂)).symm.trans
      (MulEquiv.prodComm.trans (MulEquiv.prodCongr hP2equiv (MulEquiv.refl ↥P₁)))
  have hPcentB : P ⊓ centSub B = P₂ := by
    ext x
    rw [Subgroup.mem_inf, mem_centSub]
    exact ⟨fun h => (hP₂B x h.1).mpr h.2, fun h => ⟨hP₂ h, (hP₂B x (hP₂ h)).mp h⟩⟩
  have hinfP₁B : P₁ ⊓ centSub B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxP₂ : x ∈ P₂ := by
      rw [← hPcentB, Subgroup.mem_inf]
      exact ⟨hP₁ hx.1, hx.2⟩
    have hmem : x ∈ P₁ ⊓ P₂ := ⟨hx.1, hxP₂⟩
    rwa [hinfP₁P₂] at hmem
  have hrkBP1 : rk ↥(commSub B P₁) = 6 :=
    w16g_restrict_rk_six hMin' h131 h hB hP₁ hn₁ hc₁ hP1ext hinfP₁B hrkB2
  have hcommAP₁_bot : commSub A P₁ = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro a ha
    rw [mem_fixV]
    intro x hx
    exact (hP₁A x (hP₁ hx)).mp hx a ha
  have hrkWP1 : rk ↥(commSub ⊤ P₁) = 6 := by
    have hsup' : commSub ⊤ P₁ = commSub A P₁ ⊔ commSub B P₁ := by
      rw [← hsAB, w16g_commSub_sup_left]
    rw [hsup', hcommAP₁_bot, bot_sup_eq]
    exact hrkBP1
  refine ⟨hZ3, hrkt, P₁, ⟨hP₁, hP1ext, hrkWP1⟩, ?_⟩
  rintro Q ⟨hQle, hQext, hQrk⟩
  have hcardQ : Nat.card ↥Q = 27 := by rw [hQext.2.1]; norm_num
  have hP₂abel : ∀ x ∈ P₂, ∀ y ∈ P₂, x * y = y * x := by
    haveI : IsCyclic ↥P₂ := isCyclic_of_prime_card hcardP₂
    haveI : IsMulCommutative ↥P₂ := IsCyclic.isMulCommutative
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥P₂) ⟨y, hy⟩)
  have hQnab : ¬ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro hab
    have hcenter : Subgroup.center ↥Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hab y.1 y.2 x.1 x.2)
    haveI : Subsingleton (↥Q ⧸ Subgroup.center ↥Q) :=
      (QuotientGroup.subsingleton_iff (N := Subgroup.center ↥Q)).2 hcenter
    haveI : CFSG.IsExtraspecial 3 ↥Q := hQext.1
    haveI := CFSG.IsExtraspecial.quotient_nontrivial 3 ↥Q
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥Q ⧸ Subgroup.center ↥Q)
    exact hxy (Subsingleton.elim x y)
  have hQinf : Q ⊓ P₂ = ⊥ := by
    by_contra hne
    have hle : P₂ ≤ Q := by
      have hdvd : Nat.card ↥(Q ⊓ P₂) ∣ Nat.card P₂ := Subgroup.card_dvd_of_le inf_le_right
      rw [hcardP₂] at hdvd
      have hne1 : Nat.card ↥(Q ⊓ P₂) ≠ 1 := by
        intro h1
        exact hne (Subgroup.card_eq_one.mp h1)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · have heq : Q ⊓ P₂ = P₂ :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcardP₂])
        exact heq ▸ inf_le_left
    have hQeq : Q = (Q ⊓ P₁) ⊔ P₂ := by
      apply le_antisymm
      · intro q hq
        have hq' : q ∈ P₁ ⊔ P₂ := by rw [hsupP₁P₂]; exact hQle hq
        obtain ⟨a, ha, b, hb, hqab⟩ :=
          w16g_mem_sup_of_normalizer (w16g_le_normalizer_of_commute hcomm) hq'
        have hbQ : b ∈ Q := hle hb
        have haQ : a ∈ Q := by
          have h1 : a = q * b⁻¹ := by rw [← hqab]; group
          rw [h1]
          exact Q.mul_mem hq (Q.inv_mem hbQ)
        rw [← hqab]
        exact Subgroup.mul_mem_sup ⟨haQ, ha⟩ hb
      · exact sup_le inf_le_left hle
    have hcommQP₁ : ∀ x ∈ Q ⊓ P₁, ∀ y ∈ P₂, x * y = y * x :=
      fun x hx y hy => hcomm x hx.2 y hy
    have hQP₁abel : ∀ x ∈ Q ⊓ P₁, ∀ y ∈ Q ⊓ P₁, x * y = y * x := by
      have hcard_QP₁ : Nat.card ↥(Q ⊓ P₁) = 9 := by
        have hinf' : (Q ⊓ P₁) ⊓ P₂ = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [Subgroup.mem_inf] at hx
          have h1 : x ∈ P₁ ⊓ P₂ := ⟨hx.1.2, hx.2⟩
          rwa [hinfP₁P₂] at h1
        have hnorm : P₂ ≤ Subgroup.normalizer ((Q ⊓ P₁ : Subgroup (MulAut W)) :
            Set (MulAut W)) := by
          have hcent : P₂ ≤ Subgroup.centralizer ((Q ⊓ P₁ : Subgroup (MulAut W)) :
              Set (MulAut W)) := by
            intro y hy
            rw [Subgroup.mem_centralizer_iff]
            intro x hx
            exact hcomm x hx.2 y hy
          exact hcent.trans (Subgroup.centralizer_le_normalizer _)
        have h := w16g_card_sup_of_inf_eq_bot hnorm hinf'
        rw [← hQeq, hcardQ, hcardP₂] at h
        omega
      haveI : IsMulCommutative ↥(Q ⊓ P₁) :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard_QP₁]; norm_num)
      intro x hx y hy
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(Q ⊓ P₁)) ⟨y, hy⟩)
    have hab := w16g_commute_of_mem_sup hcommQP₁ hQP₁abel hP₂abel
    apply hQnab
    intro x hx y hy
    rw [hQeq] at hx hy
    exact hab x hx y hy
  have hP₂centQ : P₂ ≤ Subgroup.centralizer (Q : Set (MulAut W)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ P₁ ⊔ P₂ := by rw [hsupP₁P₂]; exact hQle hq
    obtain ⟨a, ha, b, hb, hqab⟩ :=
      w16g_mem_sup_of_normalizer (w16g_le_normalizer_of_commute hcomm) hq'
    rw [← hqab]
    calc (a * b) * y = a * (b * y) := by rw [mul_assoc]
      _ = a * (y * b) := by rw [hP₂abel b hb y hy]
      _ = (a * y) * b := by rw [mul_assoc]
      _ = (y * a) * b := by rw [hcomm a ha y hy]
      _ = y * (a * b) := by rw [mul_assoc]
  have hnormQ : P₂ ≤ Subgroup.normalizer (Q : Set (MulAut W)) :=
    hP₂centQ.trans (Subgroup.centralizer_le_normalizer (Q : Set (MulAut W)))
  have hQsup : Q ⊔ P₂ = P := by
    have hcard_sup := w16g_card_sup_of_inf_eq_bot hnormQ hQinf
    have hle : Q ⊔ P₂ ≤ P := sup_le hQle hP₂
    have hcard_eq : Nat.card ↥(Q ⊔ P₂) = Nat.card P := by
      rw [hcard_sup, hcardQ, hcardP₂, hcardP]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq.symm)
  have hP₂fixB : ∀ x ∈ P₂, ∀ u ∈ B, x u = u :=
    fun x hx u hu => (hP₂B x (hP₂ hx)).mp hx u hu
  have hP₁stabB : ∀ x ∈ P₁, ∀ u ∈ B, x u ∈ B := fun x hx u hu =>
    (mem_stabSub.mp (w16g_le_stabSub_of_stableUnder hB (Subgroup.mem_sup_left (hP₁ hx))) u).mpr hu
  have hcommBQ_le : commSub B Q ≤ commSub B P₁ := by
    apply w16g_commSub_le_of_act_le
    intro q hq
    exact w16g_exists_act_eq_right hcomm hP₂fixB hP₁stabB (by rw [hsupP₁P₂]; exact hQle hq)
  have hcommBP₁_le : commSub B P₁ ≤ commSub B Q := by
    apply w16g_commSub_le_of_act_le
    intro x hx
    have hx' : x ∈ Q ⊔ P₂ := by rw [hQsup]; exact hP₁ hx
    obtain ⟨q, hq, b, hb, hxqb⟩ := w16g_mem_sup_of_normalizer hnormQ hx'
    exact ⟨q, hq, fun u hu => by rw [← hxqb, MulAut.mul_apply, hP₂fixB b hb u hu]⟩
  have hBQ_eq : commSub B Q = commSub B P₁ := le_antisymm hcommBQ_le hcommBP₁_le
  have hAQ : commSub A Q ≤ A := commSub_le_of_invariant (fun x hx w hw =>
    (mem_stabSub.mp (w16g_le_stabSub_of_stableUnder hA
      (Subgroup.mem_sup_left (hQle hx))) w).mpr hw)
  have hBQ : commSub B Q ≤ B := commSub_le_of_invariant (fun x hx w hw =>
    (mem_stabSub.mp (w16g_le_stabSub_of_stableUnder hB
      (Subgroup.mem_sup_left (hQle hx))) w).mpr hw)
  have hQ_decomp : commSub ⊤ Q = commSub A Q ⊔ commSub B Q := by
    rw [← hsAB, w16g_commSub_sup_left]
  have hQinf_AB : commSub A Q ⊓ commSub B Q = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_inf] at hu
    rw [← hdAB, Subgroup.mem_inf]
    exact ⟨hAQ hu.1, hBQ hu.2⟩
  have hrkQadd : rk ↥(commSub ⊤ Q) = rk ↥(commSub A Q) + rk ↥(commSub B Q) := by
    rw [hQ_decomp]
    have h1 := rk_sup_add_rk_inf (commSub A Q) (commSub B Q)
    rw [hQinf_AB, rk_bot, add_zero] at h1
    exact h1
  have hrkBQ : rk ↥(commSub B Q) = 6 := by rw [hBQ_eq]; exact hrkBP1
  have hrkAQ : rk ↥(commSub A Q) = 0 := by
    have h1 := hQrk
    rw [hrkQadd, hrkBQ] at h1
    omega
  have hQcentA : Q ≤ centSub A := by
    have hbot : commSub A Q = ⊥ := (rk_eq_zero_iff h.hW).mp hrkAQ
    have hfix : A ≤ fixV Q := commSub_eq_bot_iff.mp hbot
    intro x hx
    rw [mem_centSub]
    intro u hu
    exact mem_fixV.mp (hfix hu) x hx
  have hQleP₁ : Q ≤ P₁ := by
    have hle : Q ≤ P ⊓ centSub A := le_inf hQle hQcentA
    have hPcentA : P ⊓ centSub A = P₁ := by
      ext x
      rw [Subgroup.mem_inf, mem_centSub]
      exact ⟨fun h => (hP₁A x h.1).mpr h.2, fun h => ⟨hP₁ h, (hP₁A x (hP₁ h)).mp h⟩⟩
    rwa [hPcentA] at hle
  exact Subgroup.eq_of_le_of_card_ge hQleP₁ (by rw [hcardP₁, hcardQ])

end CFSG.LocalAnalysis.WeakClosure81
