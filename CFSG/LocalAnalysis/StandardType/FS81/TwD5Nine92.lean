module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Cent
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Norm
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Weak

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

private theorem zpowers_pow_three_eq_one {G : Type} [Group G] {b : G}
    (hb : orderOf b = 3) :
    ∀ y ∈ Subgroup.zpowers b, y ^ 3 = 1 := fun y hy =>
  orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hy).trans (by rw [hb]))

private theorem primeCore_inf_sup_zpowers_eq_bot {G : Type} [Group G] [Finite G]
    {b₀ b₂ : G} (hb0 : orderOf b₀ = 3) (hb2 : orderOf b₂ = 3)
    (hcomm : b₀ * b₂ = b₂ * b₀) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b₂} : Set G)) ⊓
      (Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂) = ⊥ := by
  have h0 : IsElemAbelian 3 (Subgroup.zpowers b₀) :=
    isElemAbelian_zpowers (by rw [← hb0]; exact pow_orderOf_eq_one b₀)
  have h2 : IsElemAbelian 3 (Subgroup.zpowers b₂) :=
    isElemAbelian_zpowers (by rw [← hb2]; exact pow_orderOf_eq_one b₂)
  have hc : ∀ a ∈ Subgroup.zpowers b₀, ∀ b ∈ Subgroup.zpowers b₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (show Commute b₀ b₂ from hcomm) i).zpow_right j |>.eq
  have hdisj : Disjoint (Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂)
      (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b₂} : Set G))) :=
    disjoint_of_forall_pow_three_eq_one_of_coprime
      (IsElemAbelian.sup_of_commute h0 h2 hc).2
      (CFSG.HardMathSupport.Timmesfeld.Balance.coprime_card_gLAPPrimeCoreOf' Nat.prime_three _)
  rw [inf_comm]
  exact hdisj.eq_bot

private theorem conj_mem_primeCore_sup_zpowers_sup_zpowers {G : Type} [Group G]
    [Finite G] {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E)
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    (hfus : Fus42 B b₀)
    (hnorm : ∀ g ∈ Subgroup.centralizer ({B.b 2} : Set G), ∀ x ∈ nineJ K (B.b 2),
      g * x * g⁻¹ ∈ nineJ K (B.b 2) ⊔
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    {g : G} (hg : g ∈ Subgroup.centralizer ({B.b 2} : Set G)) :
    g * b₀ * g⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) ⊔
      Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) := by
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let O : Subgroup G := GLAPPrimeCoreOf 3 H
  let J : Subgroup G := nineJ K (B.b 2)
  have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.2.1
  have hb0b2 : b₀ * B.b 2 = B.b 2 * b₀ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hKC hb2K)).symm
  have hb0H : b₀ ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hb0b2
  have hxH : g * b₀ * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hb0H) (H.inv_mem hg)
  have hJleK : J ≤ K := (Subgroup.commutator_le_self _).trans inf_le_left
  have hJle : J ≤ H := (Subgroup.commutator_le_self _).trans inf_le_right
  have hxJ : ∀ x ∈ J, (g * b₀ * g⁻¹) * x * (g * b₀ * g⁻¹)⁻¹ * x⁻¹ ∈ O := by
    intro x hx
    have hu : g⁻¹ * x * g ∈ J ⊔ O := by
      simpa using hnorm g⁻¹ (H.inv_mem hg) x hx
    have hqJ : ∀ y ∈ J, b₀ * y * b₀⁻¹ * y⁻¹ ∈ O := by
      intro y hy
      have hyb : Commute b₀ y :=
        (Subgroup.mem_centralizer_singleton_iff.mp ((hJleK.trans hKC) hy)).symm
      have h1 : b₀ * y * b₀⁻¹ * y⁻¹ = 1 := by
        simpa [commutatorElement_def] using hyb.commutator_eq
      rw [h1]
      exact one_mem _
    have hmem : b₀ * (g⁻¹ * x * g) * b₀⁻¹ * (g⁻¹ * x * g)⁻¹ ∈ O :=
      commutator_mem_gLAPPrimeCoreOf_of_mem_sup hJle hb0H hqJ hu
    have heq : (g * b₀ * g⁻¹) * x * (g * b₀ * g⁻¹)⁻¹ * x⁻¹ =
        g * (b₀ * (g⁻¹ * x * g) * b₀⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (gLAPPrimeCoreOf_normal 3 H) hg) _).mp hmem
  exact mem_sup_of_commutator_mem_primeCore hstd hB hrec hfus hnorm hxH hxJ

private theorem exists_mul_eq_of_mem_primeCore_sup_zpowers_sup_zpowers {G : Type} [Group G]
    {O H P0 P2 : Subgroup G} (hOH : O ≤ H) (hP0H : P0 ≤ H) (hP2H : P2 ≤ H)
    (hOnormal : (O.subgroupOf H).Normal)
    (hcomm : ∀ a ∈ P0, ∀ b ∈ P2, Commute a b) {x : G} (hxH : x ∈ H)
    (hx : x ∈ O ⊔ P0 ⊔ P2) :
    ∃ o ∈ O, ∃ a ∈ P0, ∃ b ∈ P2, x = o * a * b := by
  have hx' : x ∈ O ⊔ (P0 ⊔ P2) := by rwa [← sup_assoc]
  have hxsub : (⟨x, hxH⟩ : ↥H) ∈ (O.subgroupOf H) ⊔ ((P0 ⊔ P2).subgroupOf H) := by
    rw [← Subgroup.subgroupOf_sup hOH (sup_le hP0H hP2H)]
    exact hx'
  obtain ⟨o, ho, y, hy, hoy⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := O.subgroupOf H)
      (t := (P0 ⊔ P2).subgroupOf H) (hs := hOnormal)).mp hxsub
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (CFSG.mem_sup_of_commute hcomm).mp (Subgroup.mem_subgroupOf.mp hy)
  have hoxy : (o : G) * (y : G) = x := congrArg Subtype.val hoy
  exact ⟨o, Subgroup.mem_subgroupOf.mp ho, a, ha, b, hb, by
    rw [← hoxy, ← hab]; group⟩

private theorem mem_primeCore_sup_zpowers_of_conj_eq_inv {G : Type} [Group G]
    {b₀ b₂ t o a b x : G} {O H : Subgroup G}
    (hOnormH : H ≤ Subgroup.normalizer (O : Set G))
    (haH : a ∈ H) (hoH : o ∈ H) (hoO : o ∈ O) (hbH : b ∈ H)
    (hcomm2 : ∀ y ∈ H, b₂ * y = y * b₂) (ha : a ∈ Subgroup.zpowers b₀)
    (hb : b ∈ Subgroup.zpowers b₂) (hb2ord : orderOf b₂ = 3)
    (ht0 : t * b₀ * t⁻¹ = b₀⁻¹) (ht2 : t * b₂ = b₂ * t)
    (hOtO : t * o * t⁻¹ ∈ O) (hx : x = o * a * b)
    (htx : t * x * t⁻¹ = x⁻¹)
    (hOInfP : O ⊓ (Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂) = ⊥) :
    x ∈ O ⊔ Subgroup.zpowers b₀ := by
  have hb_central : ∀ y ∈ H, Commute b y := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Commute.zpow_left (hcomm2 y hy) j
  have hb_inv_a : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := ((hb_central a haH).inv_left.inv_right).eq
  have hb_inv_o : b⁻¹ * o⁻¹ = o⁻¹ * b⁻¹ := ((hb_central o hoH).inv_left.inv_right).eq
  have ha_conj : t * a * t⁻¹ = a⁻¹ := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow, ht0, inv_zpow]
  have hb_conj : t * b * t⁻¹ = b := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← conj_zpow, show t * b₂ * t⁻¹ = b₂ by rw [ht2]; group]
  have hconj_x : t * x * t⁻¹ = (t * o * t⁻¹) * a⁻¹ * b := by
    calc t * x * t⁻¹ = (t * o * t⁻¹) * (t * a * t⁻¹) * (t * b * t⁻¹) := by
          rw [hx]; group
      _ = (t * o * t⁻¹) * a⁻¹ * b := by rw [ha_conj, hb_conj]
  have hEq : (t * o * t⁻¹) * a⁻¹ * b = a⁻¹ * o⁻¹ * b⁻¹ := by
    rw [← hconj_x, htx, hx]
    simp [mul_inv_rev, hb_inv_a, hb_inv_o, mul_assoc]
  have hb2O : b * b ∈ O := by
    have hb_eq : b * b = a * (t * o * t⁻¹)⁻¹ * a⁻¹ * o⁻¹ := by
      calc b * b = a * (t * o * t⁻¹)⁻¹ * ((t * o * t⁻¹) * a⁻¹ * b * b) := by group
        _ = a * (t * o * t⁻¹)⁻¹ * (a⁻¹ * o⁻¹) := by rw [hEq]; group
        _ = a * (t * o * t⁻¹)⁻¹ * a⁻¹ * o⁻¹ := by group
    have hcO : a * (t * o * t⁻¹)⁻¹ * a⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOnormH haH) _).mp (O.inv_mem hOtO)
    rw [hb_eq]
    exact O.mul_mem hcO (O.inv_mem hoO)
  have hb3 : b ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hb).trans (by rw [hb2ord]))
  have hbbP : b * b ∈ Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂ :=
    Subgroup.mem_sup_right (by simpa [pow_two] using Subgroup.pow_mem (Subgroup.zpowers b₂) hb 2)
  have hbb1 : b * b = 1 := by
    simpa [hOInfP] using (Subgroup.mem_inf.mpr ⟨hb2O, hbbP⟩ :
      b * b ∈ O ⊓ (Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂))
  have hb1 : b = 1 := by
    calc b = b ^ 3 * (b * b)⁻¹ := by group
      _ = 1 := by rw [hb3, hbb1]; group
  have hmem : o * a ∈ O ⊔ Subgroup.zpowers b₀ := Subgroup.mul_mem_sup hoO ha
  rw [hx, hb1, mul_one]
  exact hmem

private theorem mem_primeCore_sup_zpowers_of_mem_centralizer {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hnorm : ∀ g ∈ Subgroup.centralizer ({B.b 2} : Set G), ∀ x ∈ nineJ K (B.b 2),
      g * x * g⁻¹ ∈ nineJ K (B.b 2) ⊔
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    {t g : G} (ht0 : t * b₀ * t⁻¹ = b₀⁻¹)
    (ht2 : ∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t)
    (hg : g ∈ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({B.b 2} : Set G)) :
    g * b₀ * g⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) ⊔
      Subgroup.zpowers b₀ := by
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let O : Subgroup G := GLAPPrimeCoreOf 3 H
  let P0 : Subgroup G := Subgroup.zpowers b₀
  let P2 : Subgroup G := Subgroup.zpowers (B.b 2)
  have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
  have hb0ord : orderOf b₀ = 3 := hstd.2.1.1
  have hb2ord : orderOf (B.b 2) = 3 := B.ord 2
  have hb0b2 : b₀ * B.b 2 = B.b 2 * b₀ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hstd.2.1.2.1 hb2K)).symm
  have hgH : g ∈ H := hg.2
  have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg.1
  have hb0H : b₀ ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hb0b2
  have hb2H : B.b 2 ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htH : t ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr (ht2 2 (by norm_num))
  have hOleH : O ≤ H := Subgroup.map_subtype_le _
  have hP0leH : P0 ≤ H := Subgroup.zpowers_le.mpr hb0H
  have hP2leH : P2 ≤ H := Subgroup.zpowers_le.mpr hb2H
  have hOnormal : (O.subgroupOf H).Normal := gLAPPrimeCoreOf_normal 3 H
  have hOnormH : H ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (gLAPPrimeCoreOf_normal 3 H)
  have hxA : g * b₀ * g⁻¹ ∈ O ⊔ P0 ⊔ P2 :=
    conj_mem_primeCore_sup_zpowers_sup_zpowers hstd hB hrec hfus hnorm hgH
  have hxH : g * b₀ * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hgH hb0H) (H.inv_mem hgH)
  have hcommP : ∀ a ∈ P0, ∀ b ∈ P2, Commute a b := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (show Commute b₀ (B.b 2) from hb0b2) i).zpow_right j
  obtain ⟨o, hoO, a, haP0, b, hbP2, hx_decomp⟩ :=
    exists_mul_eq_of_mem_primeCore_sup_zpowers_sup_zpowers hOleH hP0leH hP2leH
      hOnormal hcommP hxH hxA
  have hoH : o ∈ H := hOleH hoO
  have haH : a ∈ H := hP0leH haP0
  have hbH : b ∈ H := hP2leH hbP2
  have hcomm2 : ∀ y ∈ H, B.b 2 * y = y * B.b 2 := fun y hy =>
    Subgroup.mem_centralizer_iff.mp hy (B.b 2) (by simp)
  have hOtO : t * o * t⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hOnormH htH) o).mp hoO
  have hOInfP : O ⊓ (P0 ⊔ P2) = ⊥ :=
    primeCore_inf_sup_zpowers_eq_bot hb0ord hb2ord hb0b2
  have htx : t * (g * b₀ * g⁻¹) * t⁻¹ = (g * b₀ * g⁻¹)⁻¹ := by
    have htg : t * g = g * t := hgt.symm
    have htg_inv : g⁻¹ * t⁻¹ = t⁻¹ * g⁻¹ := by
      simpa [mul_inv_rev] using congrArg Inv.inv hgt.symm
    calc t * (g * b₀ * g⁻¹) * t⁻¹ = (t * g) * b₀ * (g⁻¹ * t⁻¹) := by group
      _ = (g * t) * b₀ * (t⁻¹ * g⁻¹) := by rw [htg, htg_inv]
      _ = g * (t * b₀ * t⁻¹) * g⁻¹ := by group
      _ = g * b₀⁻¹ * g⁻¹ := by rw [ht0]
      _ = (g * b₀ * g⁻¹)⁻¹ := by group
  exact mem_primeCore_sup_zpowers_of_conj_eq_inv hOnormH haH hoH hoO hbH hcomm2
    haP0 hbP2 hb2ord ht0 (ht2 2 (by norm_num)) hOtO hx_decomp htx hOInfP

private theorem exists_mul_self_or_mul_t_of_conj_mem_zpowers {G : Type} [Group G]
    {b₀ t g : G} {H : Subgroup G} (hb0ord : orderOf b₀ = 3)
    (ht0 : t * b₀ * t⁻¹ = b₀⁻¹) {o : G} (hoH : o ∈ H) (hgH : g ∈ H)
    (htH : t ∈ H) (hoxo : o * (g * b₀ * g⁻¹) * o⁻¹ ∈ Subgroup.zpowers b₀) :
    ∃ m : G, m ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ H ∧
      (m = o * g ∨ m = o * g * t) := by
  let n : G := o * g
  have hnH : n ∈ H := H.mul_mem hoH hgH
  have hn_conj : n * b₀ * n⁻¹ ∈ Subgroup.zpowers b₀ := by
    have h : n * b₀ * n⁻¹ = o * (g * b₀ * g⁻¹) * o⁻¹ := by dsimp only [n]; group
    rwa [h]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn_conj
  have hkmod : b₀ ^ (k % 3) = b₀ ^ k := by simpa [hb0ord] using zpow_mod_orderOf b₀ k
  have hb0pow3 : b₀ ^ 3 = 1 := by rw [← hb0ord]; exact pow_orderOf_eq_one b₀
  have hb0_sq : b₀ ^ 2 = b₀⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, show 2 + 1 = 3 by norm_num, hb0pow3]
  have hn_case : n * b₀ * n⁻¹ = b₀ ∨ n * b₀ * n⁻¹ = b₀⁻¹ := by
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      have h1 : n * b₀ * n⁻¹ = 1 := by rw [← hk, ← hkmod, h0, zpow_zero]
      have hord : orderOf (n * b₀ * n⁻¹) = 3 := by
        rw [show n * b₀ * n⁻¹ = MulAut.conj n b₀ by rw [MulAut.conj_apply],
          MulEquiv.orderOf_eq, hb0ord]
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    · left
      rw [← hk, ← hkmod, h1, zpow_one]
    · right
      rw [← hk, ← hkmod, h2, show b₀ ^ (2 : ℤ) = b₀⁻¹ by simpa using hb0_sq]
  by_cases h : n * b₀ * n⁻¹ = b₀
  · have hn_comm : n * b₀ = b₀ * n := by
      calc n * b₀ = (n * b₀ * n⁻¹) * n := by group
        _ = b₀ * n := by rw [h]
    refine ⟨n, Subgroup.mem_inf.mpr ⟨?_, hnH⟩, Or.inl rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hn_comm
  · have hb : n * b₀ * n⁻¹ = b₀⁻¹ := hn_case.resolve_left h
    have hconj : (n * t) * b₀ * (n * t)⁻¹ = b₀ := by
      calc (n * t) * b₀ * (n * t)⁻¹ = n * (t * b₀ * t⁻¹) * n⁻¹ := by group
        _ = n * b₀⁻¹ * n⁻¹ := by rw [ht0]
        _ = (n * b₀ * n⁻¹)⁻¹ := by group
        _ = b₀ := by rw [hb]; exact inv_inv b₀
    have hnt_comm : (n * t) * b₀ = b₀ * (n * t) := by
      calc (n * t) * b₀ = ((n * t) * b₀ * (n * t)⁻¹) * (n * t) := by group
        _ = b₀ * (n * t) := by rw [hconj]
    refine ⟨n * t, Subgroup.mem_inf.mpr ⟨?_, H.mul_mem hnH htH⟩, Or.inr rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hnt_comm

private theorem mem_sup_of_exists_mul_self_or_mul_t {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hnorm : ∀ g ∈ Subgroup.centralizer ({B.b 2} : Set G), ∀ x ∈ nineJ K (B.b 2),
      g * x * g⁻¹ ∈ nineJ K (B.b 2) ⊔
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    {t g m o : G}
    (hoO : o ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    (htPt : t⁻¹ ∈ Subgroup.zpowers t)
    (hmrel : m = o * g ∨ m = o * g * t)
    (hm : m ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer ({B.b 2} : Set G)) :
    g ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) ⊔
      Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) ⊔
        nineJ K (B.b 2) ⊔ Subgroup.zpowers t := by
  let O : Subgroup G := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G))
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let P0 : Subgroup G := Subgroup.zpowers b₀
  let P2 : Subgroup G := Subgroup.zpowers (B.b 2)
  let J : Subgroup G := nineJ K (B.b 2)
  obtain ⟨d, hdD, k, hk, hmk⟩ :=
    exists_mul_eq_of_mem_centralizer_inf_centralizer hstd hB hrec hm
  have hkP : k ∈ P2 ⊔ J := by
    rw [← inf_centralizer_eq_zpowers_sup_nineJ hstd hB hrec]
    exact hk
  have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
  have hdH : d ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hdD.2 (B.b 2) hb2K).symm
  have hdJ : ∀ x ∈ J, d * x * d⁻¹ * x⁻¹ ∈ O := by
    intro x hx
    have hcomm : d * x = x * d :=
      (Subgroup.mem_centralizer_iff.mp hdD.2 x
        ((Subgroup.commutator_le_self _).trans inf_le_left hx)).symm
    have h1 : d * x * d⁻¹ * x⁻¹ = 1 := by rw [hcomm]; group
    rw [h1]
    exact one_mem _
  have hdA : d ∈ O ⊔ P0 ⊔ P2 :=
    mem_sup_of_commutator_mem_primeCore hstd hB hrec hfus hnorm hdH hdJ
  have hOleA : O ≤ O ⊔ P0 ⊔ P2 := le_trans le_sup_left le_sup_left
  have hoInvR : o⁻¹ ∈ O ⊔ P0 ⊔ P2 ⊔ J ⊔ Subgroup.zpowers t :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (hOleA (O.inv_mem hoO)))
  have hdR : d ∈ O ⊔ P0 ⊔ P2 ⊔ J ⊔ Subgroup.zpowers t :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hdA)
  have hPJleR : P2 ⊔ J ≤ O ⊔ P0 ⊔ P2 ⊔ J ⊔ Subgroup.zpowers t := by
    dsimp only [P2, J]
    exact le_sup_of_le_left (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
  have hkR : k ∈ O ⊔ P0 ⊔ P2 ⊔ J ⊔ Subgroup.zpowers t := hPJleR hkP
  rcases hmrel with hmg | hmgt
  · have hg : g = o⁻¹ * d * k := by
      calc g = o⁻¹ * m := by rw [hmg]; group
        _ = o⁻¹ * (d * k) := by rw [hmk]
        _ = o⁻¹ * d * k := by group
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hoInvR hdR) hkR
  · have htPtR : t⁻¹ ∈ O ⊔ P0 ⊔ P2 ⊔ J ⊔ Subgroup.zpowers t :=
      Subgroup.mem_sup_right htPt
    have hg : g = o⁻¹ * d * k * t⁻¹ := by
      calc g = o⁻¹ * m * t⁻¹ := by rw [hmgt]; group
        _ = o⁻¹ * (d * k) * t⁻¹ := by rw [hmk]
        _ = o⁻¹ * d * k * t⁻¹ := by group
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hoInvR hdR) hkR) htPtR

theorem t5Nine92_of_norm (hN : T5Nine92Norm) : T5Nine92 := by
  intro G _ _ b₀ K E hstd hKP hchar B hB hrec hfus hodd t ht ht0 ht1 ht2 g hg
  classical
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let O : Subgroup G := GLAPPrimeCoreOf 3 H
  let P0 : Subgroup G := Subgroup.zpowers b₀
  let Pt : Subgroup G := Subgroup.zpowers t
  let x : G := g * b₀ * g⁻¹
  have hgH : g ∈ H := hg.2
  have htH : t ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr (ht2 2 (by norm_num))
  have hnorm : ∀ y ∈ Subgroup.centralizer ({B.b 2} : Set G), ∀ z ∈ nineJ K (B.b 2),
      y * z * y⁻¹ ∈ nineJ K (B.b 2) ⊔
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) :=
    hN G b₀ K E hstd hKP hchar B hB hrec hfus hodd
  have ht0' : t * b₀ * t⁻¹ = b₀⁻¹ := by simpa [hB.2.1] using ht0
  have hxA : x ∈ O ⊔ P0 :=
    mem_primeCore_sup_zpowers_of_mem_centralizer hstd hB hrec hfus hnorm ht0' ht2 hg
  have hxE : x ∈ P0 ⊔ O := by simpa [sup_comm] using hxA
  have hxord : orderOf x = 3 := by
    rw [show x = MulAut.conj g b₀ by rw [MulAut.conj_apply], MulEquiv.orderOf_eq,
      hstd.2.1.1]
  have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
  have hb0b2 : b₀ * B.b 2 = B.b 2 * b₀ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hstd.2.1.2.1 hb2K)).symm
  have hb0H : b₀ ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hb0b2
  have hEpg : IsPGroup 3 P0 := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hstd.2.1.1, pow_one]
  have hnormal : P0 ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.zpowers_le.mpr hb0H).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (gLAPPrimeCoreOf_normal 3 H))
  obtain ⟨o, hoO, hoxo⟩ := exists_mem_conj_of_mem_sup_of_coprime
    (zpowers_pow_three_eq_one hstd.2.1.1) hEpg
    (CFSG.HardMathSupport.Timmesfeld.Balance.coprime_card_gLAPPrimeCoreOf' Nat.prime_three H)
    hnormal hxE hxord
  have hoH : o ∈ H := (Subgroup.map_subtype_le _) hoO
  obtain ⟨m, hm, hmrel⟩ :=
    exists_mul_self_or_mul_t_of_conj_mem_zpowers hstd.2.1.1 ht0' hoH hgH htH hoxo
  exact mem_sup_of_exists_mul_self_or_mul_t hstd hB hrec hfus hnorm hoO
    (Pt.inv_mem (Subgroup.mem_zpowers t)) hmrel hm

end CFSG.StandardType.FrameRoute.FS81

end
