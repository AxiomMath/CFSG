module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Module
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.QSylow

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open scoped Pointwise
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private theorem mem_sup_iff_of_le_normalizer' {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) {g : G} :
    g ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, g = x * y := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H K hK, Set.mem_mul]
  exact ⟨fun ⟨x, hx, y, hy, hxy⟩ => ⟨x, hx, y, hy, hxy.symm⟩,
    fun ⟨x, hx, y, hy, hxy⟩ => ⟨x, hx, y, hy, hxy.symm⟩⟩

private theorem card_sup_of_le_normalizer' {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) (hi : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      have h1 : ((x : G) * y) = x' * y' := congrArg Subtype.val hxy
      have h2 : (x' : G)⁻¹ * x = y' * (y : G)⁻¹ := by
        calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
          _ = (x' : G)⁻¹ * (x' * y') * (y : G)⁻¹ := by rw [h1]
          _ = y' * (y : G)⁻¹ := by group
      have hmem : (x' : G)⁻¹ * x ∈ H ⊓ K :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem x'.2) x.2,
          h2 ▸ mul_mem y'.2 (inv_mem y.2)⟩
      rw [hi, Subgroup.mem_bot] at hmem
      have hx : (x : G) = x' := by
        rw [← mul_inv_cancel_left (x' : G) x, hmem, mul_one]
      have hy : (y : G) = y' := by
        rw [hx] at h1
        exact mul_left_cancel h1
      simp only [Prod.mk.injEq]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
    · rintro ⟨g, hg⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer' hK).1 hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

private theorem three_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (hH : IsPGroup 3 H) (hK : IsPGroup 3 K) (hne : H ≠ K) :
    3 * Nat.card H ≤ Nat.card K := by
  obtain ⟨a, ha⟩ := hH.exists_card_eq
  obtain ⟨b, hb⟩ := hK.exists_card_eq
  have hle : 3 ^ a ≤ 3 ^ b := by
    simpa only [ha, hb] using Subgroup.card_le_of_le hHK
  have hab : a ≤ b := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hneab : a ≠ b := by
    intro heq
    exact hne (Subgroup.eq_of_le_of_card_ge hHK (by rw [ha, hb, heq]))
  have hlt : a + 1 ≤ b := by omega
  calc 3 * Nat.card H = 3 * 3 ^ a := by rw [ha]
    _ = 3 ^ (a + 1) := by rw [pow_succ']
    _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hlt
    _ = Nat.card K := hb.symm

private theorem centralizer_inf_zpowers_b {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    {B₂ R : Subgroup G} (hB₂ : B2Package b z B₂) (hRB : R ≤ B₂)
    (hR9 : Nat.card R = 9) (hR1 : GGFF.zs z 0 ∈ R)
    (hRc : ∀ r ∈ R, b * r * b⁻¹ * r⁻¹ ∈ Subgroup.zpowers (GGFF.zs z 0))
    (hRn : ∃ r ∈ R, b * r * b⁻¹ * r⁻¹ ≠ 1) :
    R ⊓ Subgroup.centralizer ({b} : Set G) = Subgroup.zpowers (GGFF.zs z 0) := by
  let b₁ : G := GGFF.zs z 0
  have hb₁3 : b₁ ^ 3 = 1 := by
    dsimp only [b₁]
    exact h.settingCore.zs_pow 0
  have hb₁ne : b₁ ≠ 1 := by
    intro h1
    exact h.model.z_ne_one 0 (Subtype.ext (by simpa [b₁, GGFF.zs] using h1))
  have hb₁ord : orderOf b₁ = 3 := orderOf_eq_prime hb₁3 hb₁ne
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB₂.abel.1.is_comm.comm ⟨x, hRB hx⟩ ⟨y, hRB hy⟩)
  have hb₁cenb : b₁ ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (h.settingCore.comm_of_mem (GGFF.SettingCore.zs_mem z 0)).symm
  let φ : ↥R →* ↥(Subgroup.zpowers b₁) :=
    { toFun := fun r => ⟨b * (r : G) * b⁻¹ * (r : G)⁻¹, hRc r r.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change b * ((x : G) * (y : G)) * b⁻¹ * ((x : G) * (y : G))⁻¹ =
          (b * (x : G) * b⁻¹ * (x : G)⁻¹) * (b * (y : G) * b⁻¹ * (y : G)⁻¹)
        let c : G := b * (y : G) * b⁻¹ * (y : G)⁻¹
        have hcR : c ∈ R := by
          dsimp only [c]
          exact (Subgroup.zpowers_le.mpr hR1) (hRc y y.2)
        have hxc : (x : G) * c = c * (x : G) := hRcomm x x.2 c hcR
        have hby : b * (y : G) * b⁻¹ = c * (y : G) := by
          dsimp only [c]
          group
        have hyb : (y : G) * b⁻¹ * (y : G)⁻¹ = b⁻¹ * c := by
          calc (y : G) * b⁻¹ * (y : G)⁻¹
              = b⁻¹ * (b * (y : G) * b⁻¹) * (y : G)⁻¹ := by group
            _ = b⁻¹ * (c * (y : G)) * (y : G)⁻¹ := by rw [hby]
            _ = b⁻¹ * c := by group
        have hcx : c * (x : G)⁻¹ = (x : G)⁻¹ * c :=
          (show Commute c (x : G) from hxc.symm).inv_right.eq
        calc b * ((x : G) * (y : G)) * b⁻¹ * ((x : G) * (y : G))⁻¹
            = b * (x : G) * ((y : G) * b⁻¹ * (y : G)⁻¹) * (x : G)⁻¹ := by group
          _ = b * (x : G) * (b⁻¹ * c) * (x : G)⁻¹ := by rw [hyb]
          _ = b * (x : G) * b⁻¹ * c * (x : G)⁻¹ := by group
          _ = b * (x : G) * b⁻¹ * (c * (x : G)⁻¹) := by group
          _ = b * (x : G) * b⁻¹ * ((x : G)⁻¹ * c) := by rw [hcx]
          _ = (b * (x : G) * b⁻¹ * (x : G)⁻¹) * c := by group }
  have hrange_ne : φ.range ≠ ⊥ := by
    intro hbot
    obtain ⟨r, hr, hrne⟩ := hRn
    have hmem : φ ⟨r, hr⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot] at hmem
    have h1 : φ ⟨r, hr⟩ = 1 := Subgroup.mem_bot.mp hmem
    exact hrne (congrArg Subtype.val h1)
  have hcodcard : Nat.card ↥(Subgroup.zpowers b₁) = 3 := by
    rw [Nat.card_zpowers, hb₁ord]
  have hrange_top : φ.range = ⊤ := by
    rcases (φ.range).eq_bot_or_eq_top_of_prime_card
      (hp := ⟨by rw [hcodcard]; norm_num⟩) with hbot | htop
    · exact absurd hbot hrange_ne
    · exact htop
  have hrange_card : Nat.card φ.range = 3 := by
    rw [hrange_top, Subgroup.card_top, hcodcard]
  have hkercard : Nat.card φ.ker = 3 := by
    have hprod := Subgroup.card_ker_mul_card_range φ
    rw [hrange_card, hR9] at hprod
    omega
  have hzp_le_kermap : Subgroup.zpowers b₁ ≤ φ.ker.map R.subtype := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_map]
    refine ⟨⟨b₁, hR1⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change b * b₁ * b⁻¹ * b₁⁻¹ = 1
    have hcomm : b * b₁ = b₁ * b := (Subgroup.mem_centralizer_iff.mp hb₁cenb) b rfl
    have hb₁b : b₁ * b⁻¹ = b⁻¹ * b₁ := (show Commute b b₁ from hcomm).inv_left.eq.symm
    calc b * b₁ * b⁻¹ * b₁⁻¹ = b * (b₁ * b⁻¹) * b₁⁻¹ := by group
      _ = b * (b⁻¹ * b₁) * b₁⁻¹ := by rw [hb₁b]
      _ = 1 := by group
  have hkermap_eq : φ.ker.map R.subtype = Subgroup.zpowers b₁ := by
    have h := Subgroup.eq_of_le_of_card_ge hzp_le_kermap (by
      rw [Subgroup.card_map_of_injective R.subtype_injective, hkercard,
        Nat.card_zpowers, hb₁ord])
    exact h.symm
  have hset : R ⊓ Subgroup.centralizer ({b} : Set G) = φ.ker.map R.subtype := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxR, hxC⟩
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hxR⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change b * x * b⁻¹ * x⁻¹ = 1
      have hcomm : b * x = x * b := (Subgroup.mem_centralizer_iff.mp hxC) b rfl
      rw [hcomm]
      group
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [MonoidHom.mem_ker] at hy
      have hyval : b * (y : G) * b⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val hy
      have hbxx : b * (y : G) = (y : G) * b := by
        have h2 := mul_inv_eq_one.mp hyval
        calc b * (y : G) = b * (y : G) * b⁻¹ * b := by group
          _ = (y : G) * b := by rw [h2]
      rw [← hyx]
      exact Subgroup.mem_inf.mpr ⟨y.2, by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hbxx⟩
  exact hset.trans hkermap_eq

private theorem exists_nontrivial_fixed_point {G : Type} [Group G] [Finite G]
    {R P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (R : Set G))
    (hP : IsPGroup 3 P) (hR9 : Nat.card R = 9) :
    ∃ r ∈ R, r ≠ 1 ∧ ∀ p ∈ P, p * r = r * p :=
  letI : MulAction ↥P ↥R :=
    { smul := fun p r => ⟨(p : G) * (r : G) * (p : G)⁻¹, by
        exact (Subgroup.mem_normalizer_iff.mp (hPN p.2) (r : G)).mp r.2⟩
      one_smul := fun r => by
        apply Subtype.ext
        change (1 : G) * (r : G) * (1 : G)⁻¹ = (r : G)
        simp
      mul_smul := fun p q r => by
        apply Subtype.ext
        change ((p : G) * (q : G)) * (r : G) * ((p : G) * (q : G))⁻¹ =
          (p : G) * ((q : G) * (r : G) * (q : G)⁻¹) * (p : G)⁻¹
        group }
  by
    have hdiv : 3 ∣ Nat.card ↥R := by rw [hR9]; norm_num
    have hone : (⟨1, R.one_mem⟩ : ↥R) ∈ MulAction.fixedPoints ↥P ↥R := by
      rw [MulAction.mem_fixedPoints]
      intro p
      apply Subtype.ext
      change (p : G) * 1 * (p : G)⁻¹ = 1
      group
    obtain ⟨r₁, hr₁fix, hne1⟩ :=
      hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (hp := ⟨by norm_num⟩) (α := ↥R) hdiv hone
    have hr₁fix' : ∀ p : ↥P, p • r₁ = r₁ :=
      (MulAction.mem_fixedPoints).mp hr₁fix
    have hr₁R : (r₁ : G) ∈ R := r₁.2
    have hr₁ne : (r₁ : G) ≠ 1 := by
      intro h1
      exact hne1 (Subtype.ext (by simpa using h1.symm))
    have hr₁comm : ∀ p ∈ P, p * (r₁ : G) = (r₁ : G) * p := by
      intro p hp
      have hval := congrArg Subtype.val (hr₁fix' ⟨p, hp⟩)
      change (p : G) * (r₁ : G) * (p : G)⁻¹ = (r₁ : G) at hval
      calc p * (r₁ : G) = p * (r₁ : G) * (p : G)⁻¹ * p := by group
        _ = (r₁ : G) * p := by rw [hval]
    exact ⟨(r₁ : G), hr₁R, hr₁ne, hr₁comm⟩

theorem aStar_max_of_R {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ A : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c) (hS : SylowData b B₂ A c)
    (hT : ∀ P : Sylow 3 G, ¬ ((P : Subgroup G) ≤ Subgroup.centralizer ({GGFF.zs z 0} : Set G)))
    {R : Subgroup G} (hRB : R ≤ B₂) (hR9 : Nat.card R = 9) (hR1 : GGFF.zs z 0 ∈ R)
    (hRc : ∀ r ∈ R, b * r * b⁻¹ * r⁻¹ ∈ Subgroup.zpowers (GGFF.zs z 0))
    (hRn : ∃ r ∈ R, b * r * b⁻¹ * r⁻¹ ≠ 1) :
    ∀ P : Subgroup G, P ≤ Subgroup.centralizer (R : Set G) → IsPGroup 3 P → A ≤ P → P = A := by
  classical
  let b₁ : G := GGFF.zs z 0
  let Q : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers c
  let S : Subgroup G := A ⊔ Q
  let Ab : Subgroup G := A ⊔ Subgroup.zpowers b
  let N : Subgroup G := Subgroup.normalizer (R : Set G)
  have hb₁3 : b₁ ^ 3 = 1 := by
    dsimp only [b₁]
    exact h.settingCore.zs_pow 0
  have hb₁ne : b₁ ≠ 1 := by
    intro h1
    exact h.model.z_ne_one 0 (Subtype.ext (by simpa [b₁, GGFF.zs] using h1))
  have hb₁ord : orderOf b₁ = 3 := orderOf_eq_prime hb₁3 hb₁ne
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB₂.abel.1.is_comm.comm ⟨x, hRB hx⟩ ⟨y, hRB hy⟩)
  have hbN : b ∈ N := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro r hr
    have hrφ : b * r * b⁻¹ * r⁻¹ ∈ R :=
      (Subgroup.zpowers_le.mpr hR1) (hRc r hr)
    have hEq : b * r * b⁻¹ = (b * r * b⁻¹ * r⁻¹) * r := by group
    rw [hEq]
    exact R.mul_mem hrφ hr
  have hAN : A ≤ N := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer (R : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hA.le_cen ha)) r (hRB hr)
  have hbNormA : Subgroup.zpowers b ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype ?_
    intro x hx
    exact hA.nor b (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)) x hx
  have hbP : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.hypA.ord]; norm_num)
  have hAbP : IsPGroup 3 Ab := by
    dsimp only [Ab]
    exact hA.isP.to_sup_of_normal_left' hbP hbNormA
  have hAbN : Ab ≤ N := by
    dsimp only [Ab]
    exact sup_le hAN (Subgroup.zpowers_le.mpr hbN)
  have hc_nor_bOne : c ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    rw [show (bOne z : Subgroup G) =
        Subgroup.closure ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G) from
      CFSG.StandardType.GGFF.SettingCore.tor_eq_closure z]
    refine CFSG.StandardType.GGFF.mem_nor_of_closure
      (S := ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G)) ?_
    rintro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · rw [hτc.cyc₀]; exact Subgroup.subset_closure (by simp)
    · rw [hτc.cyc₁]; exact Subgroup.subset_closure (by simp)
    · rw [hτc.cyc₂]; exact Subgroup.subset_closure (by simp)
  have hcD : c ∈ dGrp b z := Subgroup.mem_sup_right ⟨hτc.c_mem, hc_nor_bOne⟩
  have hcNormA : c ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro x hx
    exact hA.nor c hcD x hx
  have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) := by
    dsimp only [Q]
    exact sup_le hbNormA (Subgroup.zpowers_le.mpr hcNormA)
  have hbc : Commute b c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hτc.c_mem)).symm
  have hcomm_bc : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hbc i j).eq
  have hz01 : GGFF.zs z 0 ≠ GGFF.zs z 1 := by
    intro hz
    have hv : vecElt (GGFF.zs z)
        (Pi.single (0 : Fin 3) (1 : ZMod 3) + Pi.single (1 : Fin 3) (2 : ZMod 3)) = 1 := by
      rw [GGFF.vecElt_add h.settingCore.zs_pow h.settingCore.zs_comm]
      rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single,
        CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single]
      have hval1 : ((2 : ZMod 3).val) = 2 := rfl
      have hval0 : ((1 : ZMod 3).val) = 1 := rfl
      rw [hval0, hval1, pow_one, hz]
      calc GGFF.zs z 1 * GGFF.zs z 1 ^ 2 = GGFF.zs z 1 ^ (1 + 2) := by
            rw [pow_add, pow_one]
        _ = GGFF.zs z 1 ^ 3 := by norm_num
        _ = 1 := h.settingCore.zs_pow 1
    have hzero := h.settingCore.inj' _ hv
    have hcoord := congrFun hzero 0
    simp at hcoord
  have hcne : c ≠ 1 := by
    intro hc1
    apply hz01
    have h := hτc.cyc₀
    rw [hc1] at h
    simpa using h
  have hcord : orderOf c = 3 := orderOf_eq_prime hτc.c_cube hcne
  have hInt_bc : (Subgroup.zpowers b ⊓ Subgroup.zpowers c : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases Subgroup.mem_inf.mp hx with ⟨hxb, hxc⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxb
    have hxL : b ^ j ∈ L := (Subgroup.zpowers_le.mpr hτc.c_mem) hxc
    rw [h.settingCore.zpow_eq_one_of_mem hxL]
    exact Subgroup.mem_bot.mpr rfl
  have hQcard : Nat.card Q = 9 := by
    have hprod := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
      (C := Subgroup.zpowers b) (D := Subgroup.zpowers c) hcomm_bc
    dsimp only [Q]
    rw [hInt_bc, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, h.hypA.ord, hcord] at hprod
    omega
  have hAQ : A ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    rcases Subgroup.mem_inf.mp hq with ⟨hqA, hqQ⟩
    by_contra hqne
    have hB₂leCen : B₂ ≤ Subgroup.centralizer ({q} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hA.comm x (hA.B₂_le hx) q hqA
    have hK : B₂ ⊓ Subgroup.centralizer ({q} : Set G) = B₂ := inf_eq_left.mpr hB₂leCen
    have hcard := card_centralizer_le h hB₂ hτc (by simpa [Q] using hqQ) hqne
    rw [hK, hB₂.card] at hcard
    norm_num at hcard
  have hScard : Nat.card S = Nat.card A * 9 := by
    dsimp only [S]
    rw [card_sup_of_le_normalizer' hQnormA hAQ, hQcard]
  have hAbinf : A ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).2
    have hxAQ : x ∈ A ⊓ Q := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hxQ⟩
    rw [hAQ] at hxAQ
    exact hxAQ
  have hAbcard : Nat.card Ab = Nat.card A * 3 := by
    dsimp only [Ab]
    rw [card_sup_of_le_normalizer' hbNormA hAbinf, Nat.card_zpowers, h.hypA.ord]
  have hS_eq_three_Ab : Nat.card S = 3 * Nat.card Ab := by
    rw [hScard, hAbcard]; ring
  have hSylowCard : ∀ T : Sylow 3 G, Nat.card T = Nat.card S := by
    intro T
    obtain ⟨U, hSU⟩ := hS.isP.exists_le_sylow
    have hUS : (U : Subgroup G) = S := hS.max U U.isPGroup' hSU
    calc Nat.card T = Nat.card U := by
          rw [Sylow.card_eq_multiplicity T, Sylow.card_eq_multiplicity U]
      _ = Nat.card S := by rw [hUS]
  have hMaxAb : ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → Ab ≤ P → P = Ab := by
    intro P hPN hP hAb_le_P
    obtain ⟨r₁, hr₁R, hr₁ne, hr₁comm⟩ :=
      exists_nontrivial_fixed_point hPN hP hR9
    have hbAb : b ∈ Ab := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    have hb_r₁ : b * (r₁ : G) = (r₁ : G) * b := hr₁comm b (hAb_le_P hbAb)
    have hr₁_cenb : (r₁ : G) ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb_r₁
    have hCRb := centralizer_inf_zpowers_b h hB₂ hRB hR9 hR1 hRc hRn
    have hr₁_b₁ : (r₁ : G) ∈ Subgroup.zpowers b₁ := by
      have hmem : (r₁ : G) ∈ R ⊓ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hr₁R, hr₁_cenb⟩
      rw [hCRb] at hmem
      simpa [b₁] using hmem
    have hb₁_zr : b₁ ∈ Subgroup.zpowers (r₁ : G) := by
      rcases GGFF.eq_or_eq_inv_of_mem_zpowers hb₁ord hr₁_b₁ hr₁ne with he | he
      · rw [← he]
        exact Subgroup.mem_zpowers (r₁ : G)
      · have hb₁eq : b₁ = (r₁ : G)⁻¹ := by rw [he]; simp
        rw [hb₁eq]
        exact Subgroup.inv_mem (Subgroup.zpowers (r₁ : G)) (Subgroup.mem_zpowers (r₁ : G))
    have hPcen : P ≤ Subgroup.centralizer ({b₁} : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb₁_zr
      rw [← hk]
      exact (Commute.zpow_right (show Commute p (r₁ : G) from hr₁comm p hp) k).eq.symm
    by_cases hPAb : P = Ab
    · exact hPAb
    · exfalso
      have hcard_ge : Nat.card S ≤ Nat.card P := by
        rw [hS_eq_three_Ab]
        exact three_mul_card_le_of_lt hAb_le_P hAbP hP (fun heq => hPAb heq.symm)
      obtain ⟨U, hPU⟩ := hP.exists_le_sylow
      have hcardU : Nat.card U = Nat.card S := hSylowCard U
      have hcardP : Nat.card P = Nat.card S := by
        apply le_antisymm
        · calc Nat.card P ≤ Nat.card U := Subgroup.card_le_of_le hPU
            _ = Nat.card S := hcardU
        · exact hcard_ge
      have hUP : (U : Subgroup G) = P :=
        (Subgroup.eq_of_le_of_card_ge hPU (by rw [hcardP, hcardU])).symm
      exact hT U (by
        rw [hUP]
        exact hPcen)
  intro P₀ hP₀cen hP₀p hAP₀
  have hP₀N : P₀ ≤ N := hP₀cen.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  let AbN : Subgroup ↥N := Ab.subgroupOf N
  have hAbNp : IsPGroup 3 AbN := hAbP.comap_subtype
  have hAbNmax : ∀ Q : Subgroup ↥N, IsPGroup 3 Q → AbN ≤ Q → Q = AbN := by
    intro Q hQ hle
    have hQ'p : IsPGroup 3 (Q.map N.subtype) := hQ.map N.subtype
    have hQ'N : Q.map N.subtype ≤ N := Subgroup.map_subtype_le Q
    have hAbQ' : Ab ≤ Q.map N.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hAbN]
      exact Subgroup.map_mono hle
    have hQ'eq : Q.map N.subtype = Ab := hMaxAb _ hQ'N hQ'p hAbQ'
    exact Subgroup.map_injective N.subtype_injective (by
      rwa [Subgroup.map_subgroupOf_eq_of_le hAbN])
  let S₀ : Sylow 3 ↥N :=
    { toSubgroup := AbN
      isPGroup' := hAbNp
      is_maximal' := fun {Q} hQ hle => hAbNmax Q hQ hle }
  let P₀N : Subgroup ↥N := P₀.subgroupOf N
  have hP₀Np : IsPGroup 3 P₀N := hP₀p.comap_subtype
  obtain ⟨T, hP₀N_T⟩ := hP₀Np.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥N S₀ T
  have hT_eq : (T : Subgroup ↥N) =
      (MulAut.conj (g : G) • Ab).subgroupOf N := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.conj_smul_subgroupOf hAbN g
  have hP₀_le_conj : P₀ ≤ MulAut.conj (g : G) • Ab := by
    intro p hp
    have hpN : p ∈ N := hP₀N hp
    have hpP₀N : (⟨p, hpN⟩ : ↥N) ∈ P₀N := Subgroup.mem_subgroupOf.mpr hp
    have hpT : (⟨p, hpN⟩ : ↥N) ∈ (T : Subgroup ↥N) := hP₀N_T hpP₀N
    rw [hT_eq, Subgroup.mem_subgroupOf] at hpT
    exact hpT
  have hconjCenR : ∀ (h : G), h ∈ N → ∀ {x : G},
      x ∈ Subgroup.centralizer (R : Set G) → h * x * h⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    intro h hh x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hhr' : h⁻¹ * r * h ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hh) r).mp hr
      simpa using this
    have hcomm : (h⁻¹ * r * h) * x = x * (h⁻¹ * r * h) :=
      (Subgroup.mem_centralizer_iff.mp hx) (h⁻¹ * r * h) hhr'
    calc r * (h * x * h⁻¹) = h * ((h⁻¹ * r * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * r * h)) * h⁻¹ := by rw [hcomm]
      _ = (h * x * h⁻¹) * r := by group
  let K : Subgroup G := Ab ⊓ Subgroup.centralizer (R : Set G)
  have hAbCen : K = A := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxAb, hxC⟩
      by_contra hxA
      have hA_inter : A ≤ K := by
        intro y hy
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hy,
          (Subgroup.mem_centralizer_iff.mpr fun r hr =>
            (Subgroup.mem_centralizer_iff.mp (hA.le_cen hy) r (hRB hr)))⟩
      have hne : A ≠ K := fun heq => hxA (heq ▸ hx)
      have hge : 3 * Nat.card A ≤ Nat.card K :=
        three_mul_card_le_of_lt hA_inter hA.isP (hAbP.to_le inf_le_left) hne
      have hcard_eq : Nat.card K = Nat.card Ab := by
        apply le_antisymm (Subgroup.card_le_of_le inf_le_left)
        calc Nat.card Ab = Nat.card A * 3 := hAbcard
          _ = 3 * Nat.card A := Nat.mul_comm _ _
          _ ≤ Nat.card K := hge
      have hEq : K = Ab :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard_eq])
      have hbInter : b ∈ K := by
        rw [hEq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
      have hbC : b ∈ Subgroup.centralizer (R : Set G) := (Subgroup.mem_inf.mp hbInter).2
      obtain ⟨r, hr, hrne⟩ := hRn
      have hcomm : b * r = r * b := ((Subgroup.mem_centralizer_iff.mp hbC) r hr).symm
      exact hrne (by rw [hcomm]; group)
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hx,
        (Subgroup.mem_centralizer_iff.mpr fun r hr =>
          (Subgroup.mem_centralizer_iff.mp (hA.le_cen hx) r (hRB hr)))⟩
  have hAbCen' : Ab ⊓ Subgroup.centralizer (R : Set G) = A := hAbCen
  have hconjA_le : MulAut.conj ((g : G)⁻¹) • A ≤ A := by
    intro x hx
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have hx_eq : x = (g : G)⁻¹ * a * (g : G) := by
      rw [← hax]
      simp [MulAut.smul_def]
    have hxAb : x ∈ Ab := by
      rw [hx_eq]
      have hmem : a ∈ MulAut.conj (g : G) • Ab := hP₀_le_conj (hAP₀ ha)
      have hmem' : (MulAut.conj (g : G))⁻¹ • a ∈ Ab :=
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hmem
      simpa [MulAut.smul_def, MulAut.conj_apply] using hmem'
    have hxC : x ∈ Subgroup.centralizer (R : Set G) := by
      rw [hx_eq]
      simpa using hconjCenR (g : G)⁻¹ (N.inv_mem g.2) (hP₀cen (hAP₀ ha))
    have hxInter : x ∈ Ab ⊓ Subgroup.centralizer (R : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxAb, hxC⟩
    rwa [hAbCen'] at hxInter
  have hcard_conjA : Nat.card ↥(MulAut.conj ((g : G)⁻¹) • A) = Nat.card A := by
    rw [Subgroup.pointwise_smul_def]
    exact Subgroup.card_map_of_injective (MulAut.conj ((g : G)⁻¹)).injective
  have hconjA : MulAut.conj ((g : G)⁻¹) • A = A :=
    Subgroup.eq_of_le_of_card_ge hconjA_le (by rw [hcard_conjA])
  have hconjA' : MulAut.conj (g : G) • A = A := by
    have h := congrArg (fun H : Subgroup G => MulAut.conj (g : G) • H) hconjA
    simpa [← mul_smul] using h.symm
  have hP₀_le_A : P₀ ≤ A := by
    intro p hp
    have hp_ab : (g : G)⁻¹ * p * (g : G) ∈ Ab := by
      have hmem : p ∈ MulAut.conj (g : G) • Ab := hP₀_le_conj hp
      have hmem' : (MulAut.conj (g : G))⁻¹ • p ∈ Ab :=
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hmem
      simpa [MulAut.smul_def, MulAut.conj_apply] using hmem'
    have hp_c : (g : G)⁻¹ * p * (g : G) ∈ Subgroup.centralizer (R : Set G) := by
      simpa using hconjCenR (g : G)⁻¹ (N.inv_mem g.2) (hP₀cen hp)
    have hp_A : (g : G)⁻¹ * p * (g : G) ∈ A := by
      have h := Subgroup.mem_inf.mpr ⟨hp_ab, hp_c⟩
      rwa [hAbCen'] at h
    have hp_conjA : p ∈ MulAut.conj (g : G) • A := by
      have h := Subgroup.smul_mem_pointwise_smul ((g : G)⁻¹ * p * (g : G))
        (MulAut.conj (g : G)) A hp_A
      have hval : (MulAut.conj (g : G)) • ((g : G)⁻¹ * p * (g : G)) = p := by
        rw [MulAut.smul_def, MulAut.conj_apply]
        group
      simpa [hval] using h
    rwa [hconjA'] at hp_conjA
  exact (Subgroup.eq_of_le_of_card_ge hAP₀ (Subgroup.card_le_of_le hP₀_le_A)).symm

end CFSG.StandardType.FF81.PropOne

end
