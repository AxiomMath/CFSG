module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KX
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KA
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXS1
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXS4
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXS3B

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open

theorem eq_one_of_central_simple {K : Type} [Group K] (hK : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) {k : K} (hk : ∀ g : K, g * k = k * g) : k = 1 := by
  rcases hK.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · have hkZ : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr hk
    rw [h] at hkZ
    exact Subgroup.mem_bot.mp hkZ
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center K := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem centralizer_ne_top_of_simple {G : Type} [Group G] (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  apply hx
  apply eq_one_of_central_simple hsimp hnab
  intro g
  have hg : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [htop]
    exact Subgroup.mem_top g
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

theorem mem_normalizer_subgroupOf {G : Type} [Group G] {C KX : Subgroup G} (hKX : KX ≤ C)
    {g : G} (hg : g ∈ C) (hN : g ∈ Subgroup.normalizer (KX : Set G)) :
    (⟨g, hg⟩ : C) ∈ Subgroup.normalizer ((KX.subgroupOf C : Subgroup C) : Set C) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_normalizer_iff] at hN
  have hh := hN (h : G)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hh

theorem isKGroupCat_of_sub {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {C : Subgroup G} (hC : C ≠ ⊤)
    {X : Type} [Group X] [Finite X] (f : X →* C) (hf : Function.Injective f) :
    CFSG.SectionRank.IsKGroupCat X := by
  have hinj : Function.Injective (C.subtype.comp f) := C.subtype_injective.comp hf
  have hH : (C.subtype.comp f).range ≠ ⊤ := by
    intro htop
    apply hC
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ (C.subtype.comp f).range := by
      rw [htop]
      exact Subgroup.mem_top g
    obtain ⟨y, hy⟩ := hg
    rw [← hy]
    exact (f y).2
  have hY := isKGroupCat_of_proper hK hH
  exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv hY (MonoidHom.ofInjective hinj)

theorem isQuasithin_of_sub {G : Type} [Group G] [Finite G] (hG : CFSG.Open.evenRank G ≤ 2)
    {C : Subgroup G} {X : Type} [Group X] [Finite X] (f : X →* C) (hf : Function.Injective f) :
    CFSG.Quasithin.IsQuasithin X :=
  isQuasithin_of_injective hG (C.subtype.comp f) (C.subtype_injective.comp hf)

theorem pRank_centralizer_sub {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hG : CFSG.Open.evenRank G ≤ 2) {w : C} (hw2 : (w : G) * (w : G) = 1) (hw1 : (w : G) ≠ 1) :
    CFSG.Open.pRank 3 (Subgroup.centralizer ({w} : Set C)) ≤ 2 := by
  have h2 := pRank_le_two_centralizer hG hw2 hw1 Nat.prime_three (by norm_num)
  have hsub : (Subgroup.centralizer ({w} : Set C)).map C.subtype ≤
      Subgroup.centralizer ({(w : G)} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using hc)
  have hle := pRank_le_map 3 (by norm_num) C.subtype C.subtype_injective
    (Subgroup.centralizer ({w} : Set C))
  have hmono := pRank_mono 3 (by norm_num) hsub
  exact hle.trans (hmono.trans h2)

end CFSG.Quasithin.H13.Ch4.J4KX

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.A4
open CFSG.Quasithin.H13.Ch4.J4KX

theorem j4KXNormal6_of
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (h425 : Thm4_2_5)
    (hBM : InspBM22Cover)
    (h36N : CFSG.QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h38N : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) :
    J4KXNormal6 := by
  intro G _ _ T M L Mm I H K hy hIH c h6 r hr hr1 hr2 hrI x hxLH hx3 hq hcard hM22
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK, -, hG⟩ := hy.qtke
  have hsimp : IsSimpleGroup G := hy.simple
  have hnab : ∃ a b : G, a * b ≠ b * a := hy.nonabelian
  have hJ4 : IsSporadic .J4 ↥K := by
    obtain ⟨h, -⟩ := h6
    exact h
  have hKsimple : IsSimpleGroup ↥K := NoJ4.isSimpleGroup_of_isSporadic hJ4
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx3
    norm_num at hx3
  set KX := perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)) with hKX
  have hKXK : KX ≤ K := (perfectCore_le _).trans inf_le_left
  have hKXC : KX ≤ Subgroup.centralizer ({x} : Set G) := (perfectCore_le _).trans inf_le_right
  set CG : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCG
  have hCGne : CG ≠ ⊤ := centralizer_ne_top_of_simple hsimp hnab hx1
  have hLI : perfectCore (L ⊓ H) ≤ I := NoJ4.LH_le hy hIH c
  have hxI : x ∈ I := hLI hxLH
  have hxr : x * r = r * x := Subgroup.mem_centralizer_singleton_iff.mp (hrI hxI)
  have hrK : r ∈ Subgroup.centralizer (K : Set G) := hr.2
  have hNr : Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    NoJ4.centralizer_le_normalizer h36 h37 h38 h39 h48 h425 hy hIH c h6 hrK hr1 hr2 hrI
  have hN : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({r} : Set G) ≤
      Subgroup.normalizer (KX : Set G) :=
    NoJ4.inf_centralizer_le_normalizer hNr
  have hKXr : KX ≤ Subgroup.centralizer ({r} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hrK k (hKXK hk))
  have hcommr : ∀ k ∈ KX, r * k = k * r := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKXr hk)).symm
  have hrCG : r ∈ CG := Subgroup.mem_centralizer_singleton_iff.mpr hxr.symm
  have h2Z : 2 ∣ Nat.card ↥(Subgroup.center ↥KX) := by
    rw [hcard]
    norm_num
  obtain ⟨z, hzKX, hzc, hzz2, hz1⟩ :
      ∃ z : G, z ∈ KX ∧ (∀ k ∈ KX, z * k = k * z) ∧ z * z = 1 ∧ z ≠ 1 := by
    obtain ⟨zz, hzz⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
    refine ⟨(zz.1 : G), zz.1.2, ?_, ?_, ?_⟩
    · intro k hk
      have hw := Subgroup.mem_center_iff.mp zz.2 ⟨k, hk⟩
      have hw' := congrArg Subtype.val hw
      simp only [Subgroup.coe_mul] at hw'
      exact hw'.symm
    · have h2 : zz * zz = 1 := by
        rw [← pow_two, ← hzz]
        exact pow_orderOf_eq_one zz
      have h3 := congrArg (fun w : ↥(Subgroup.center ↥KX) => (w : G)) h2
      simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h3
    · intro h
      have h0 : zz = 1 := Subtype.ext (Subtype.ext h)
      rw [h0, orderOf_one] at hzz
      norm_num at hzz
  have hzC : z ∈ CG := hKXC hzKX
  have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hrz' : r * z = z * r := hcommr z hzKX
  have hrz : r ≠ z := by
    intro h
    have hrK' : r ∈ K := by
      rw [h]
      exact hKXK hzKX
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_quasisimple hq
    have hKnab : ∃ a b : ↥K, a * b ≠ b * a :=
      ⟨⟨a.1, hKXK a.2⟩, ⟨b.1, hKXK b.2⟩,
        fun h' => hab (Subtype.ext (show (a.1 : G) * b.1 = b.1 * a.1 from congrArg Subtype.val h'))⟩
    have hcen : ∀ g : ↥K, g * ⟨r, hrK'⟩ = ⟨r, hrK'⟩ * g := by
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.mp hrK g.1 g.2
    exact hr1 (congrArg Subtype.val (eq_one_of_central_simple hKsimple hKnab hcen))
  have hS1z : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (KX : Set G) :=
    step1_normalizer hG hK hBM hsimp hnab hq hcard hM22 h36N h38N hx3 hKXC hKXr hr1 hr2
      (Subgroup.mem_centralizer_singleton_iff.mpr hxr) hN hz1 hzz2
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hzc k hk).symm) hzC
      (Subgroup.mem_centralizer_singleton_iff.mpr hrz')
  have hrz_ne : r * z ≠ 1 := by
    intro h
    apply hrz
    calc r = r * z * z := by rw [mul_assoc, hzz2, mul_one]
      _ = z := by rw [h, one_mul]
  have hrzrz : (r * z) * (r * z) = 1 := by
    calc (r * z) * (r * z) = r * (z * r) * z := by group
      _ = r * (r * z) * z := by rw [← hrz']
      _ = z * z := by rw [← mul_assoc, hr2, one_mul]
      _ = 1 := hzz2
  have hKXrz : KX ≤ Subgroup.centralizer ({r * z} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc k * (r * z) = (k * r) * z := by group
        _ = (r * k) * z := by rw [← hcommr k hk]
        _ = r * (k * z) := by group
        _ = r * (z * k) := by rw [← hzc k hk]
        _ = (r * z) * k := by group)
  have hzxrz : (r * z) ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (r * z) * x = r * (z * x) := by group
        _ = r * (x * z) := by rw [hzx]
        _ = (r * x) * z := by group
        _ = (x * r) * z := by rw [← hxr]
        _ = x * (r * z) := by group)
  have hrrz : r ∈ Subgroup.centralizer ({r * z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc r * (r * z) = r * (z * r) := by rw [← hrz']
        _ = (r * z) * r := by group)
  have hS1rz : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({r * z} : Set G) ≤
      Subgroup.normalizer (KX : Set G) :=
    step1_normalizer hG hK hBM hsimp hnab hq hcard hM22 h36N h38N hx3 hKXC hKXr hr1 hr2
      (Subgroup.mem_centralizer_singleton_iff.mpr hxr) hN hrz_ne hrzrz hKXrz hzxrz hrrz
  obtain ⟨rΓ, hrΓ⟩ : ∃ rΓ : CG, (rΓ : G) = r := ⟨⟨r, hrCG⟩, rfl⟩
  obtain ⟨zΓ, hzΓ⟩ : ∃ zΓ : CG, (zΓ : G) = z := ⟨⟨z, hzC⟩, rfl⟩
  have hr1Γ : rΓ ≠ 1 := by
    intro h
    apply hr1
    rw [← hrΓ, h]
    rfl
  have hz1Γ : zΓ ≠ 1 := by
    intro h
    apply hz1
    rw [← hzΓ, h]
    rfl
  have hrzΓ : rΓ ≠ zΓ := by
    intro h
    apply hrz
    rw [← hrΓ, ← hzΓ, h]
  have h1Γ : rΓ * rΓ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one, hrΓ]
    exact hr2
  have h2Γ : zΓ * zΓ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one, hzΓ]
    exact hzz2
  have h3Γ : zΓ * rΓ = rΓ * zΓ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hrΓ, hzΓ]
    exact hrz'.symm
  have hNrΓ : Subgroup.centralizer ({rΓ} : Set CG) ≤
      Subgroup.normalizer ((KX.subgroupOf CG : Subgroup CG) : Set CG) := by
    intro g hg
    have hgr : (g : G) * r = r * (g : G) := by
      have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
      simpa [hrΓ] using h
    have hgC : (g : G) ∈ Subgroup.centralizer ({r} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgr
    exact J4KX.mem_normalizer_subgroupOf hKXC g.2 (hN (Subgroup.mem_inf.mpr ⟨g.2, hgC⟩))
  have hNzΓ : Subgroup.centralizer ({zΓ} : Set CG) ≤
      Subgroup.normalizer ((KX.subgroupOf CG : Subgroup CG) : Set CG) := by
    intro g hg
    have hgz : (g : G) * z = z * (g : G) := by
      have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
      simpa [hzΓ] using h
    have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgz
    exact J4KX.mem_normalizer_subgroupOf hKXC g.2 (hS1z (Subgroup.mem_inf.mpr ⟨g.2, hgC⟩))
  have hNrzΓ : Subgroup.centralizer ({rΓ * zΓ} : Set CG) ≤
      Subgroup.normalizer ((KX.subgroupOf CG : Subgroup CG) : Set CG) := by
    intro g hg
    have hgrz : (g : G) * (r * z) = (r * z) * (g : G) := by
      have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
      simpa [hrΓ, hzΓ] using h
    have hgC : (g : G) ∈ Subgroup.centralizer ({r * z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgrz
    exact J4KX.mem_normalizer_subgroupOf hKXC g.2 (hS1rz (Subgroup.mem_inf.mpr ⟨g.2, hgC⟩))
  have hON : CFSG.oddCore CG ≤ Subgroup.normalizer ((KX.subgroupOf CG : Subgroup CG) : Set CG) :=
    odd_core_le_normalizer h1Γ h2Γ h3Γ hr1Γ hz1Γ hrzΓ hNrΓ hNzΓ hNrzΓ
  have hKΓq : CFSG.IsQuasisimple ↥(KX.subgroupOf CG) := isQuasisimple_subgroupOf hKXC hq
  have hKΓz : Nat.card ↥(Subgroup.center ↥(KX.subgroupOf CG)) = 6 :=
    (card_center_subgroupOf hKXC).trans hcard
  have hevΓ : 2 ∣ Nat.card ↥(KX.subgroupOf CG) := by
    have h6 := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥(KX.subgroupOf CG))
    rw [hKΓz] at h6
    exact (by norm_num : 2 ∣ 6).trans h6
  have hOcen : ∀ o ∈ CFSG.oddCore CG, ∀ k ∈ KX.subgroupOf CG, o * k = k * o :=
    odd_core_centralizes hKΓq
      (fun hodd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hevΓ)) hON
  have hzKXΓ : zΓ ∈ KX.subgroupOf CG := Subgroup.mem_subgroupOf.mpr (by rw [hzΓ]; exact hzKX)
  have hzcΓ : ∀ k ∈ KX.subgroupOf CG, zΓ * k = k * zΓ := by
    intro k hk
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hzΓ]
    exact hzc _ (Subgroup.mem_subgroupOf.mp hk)
  have hrKΓ : ∀ k ∈ KX.subgroupOf CG, rΓ * k = k * rΓ := by
    intro k hk
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hrΓ]
    exact hcommr _ (Subgroup.mem_subgroupOf.mp hk)
  have hpzΓ : CFSG.Open.pRank 3 (Subgroup.centralizer ({zΓ} : Set CG)) ≤ 2 := by
    apply pRank_centralizer_sub hG
    · rw [hzΓ]
      exact hzz2
    · rw [hzΓ]
      exact hz1
  have hQTΓ : ∀ (X : Type) [Group X] [Finite X] (f : X →* CG), Function.Injective f →
      CFSG.Quasithin.IsQuasithin X := fun X _ _ f hf => isQuasithin_of_sub hG f hf
  have hKGΓ : ∀ (X : Type) [Group X] [Finite X] (f : X →* CG), Function.Injective f →
      CFSG.SectionRank.IsKGroupCat X := fun X _ _ f hf => isKGroupCat_of_sub hK hCGne f hf
  obtain ⟨E0, hE0, hE0c⟩ := exists_e9_of_isSporadic_M22 hM22
  obtain ⟨E0Γ, hE0Γ, hE0Γc⟩ := exists_e0_subgroupOf hKXC E0 hE0 hE0c
  have hM22Γ := isSporadic_M22_subgroupOf hKXC hM22
  have hK0 : CFSG.Open.IsComponentOf (KX.subgroupOf CG) ⊤ :=
    step3_component hKΓq hKΓz E0Γ hE0Γ hE0Γc hM22Γ h1Γ hr1Γ hrKΓ hNrΓ hOcen hzKXΓ hzcΓ hpzΓ hBM
      hQTΓ hKGΓ
  have hgΓall := step4_normalizer hKΓq hKΓz E0Γ hE0Γ hE0Γc hK0 hzKXΓ hzcΓ hpzΓ
  intro g hg
  have hgΓ : (⟨g, hg⟩ : CG) ∈ Subgroup.normalizer ((KX.subgroupOf CG : Subgroup CG) : Set CG) :=
    hgΓall _
  have hmapEq : KX.map (MulAut.conj g).toMonoidHom = KX := by
    ext y
    constructor
    · intro hy'
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy'
      have h1 := (Subgroup.mem_normalizer_iff.mp hgΓ) ⟨k, hKXC hk⟩
      have h2 := h1.mp (Subgroup.mem_subgroupOf.mpr hk)
      have h3 := Subgroup.mem_subgroupOf.mp h2
      simpa [MulAut.conj_apply] using h3
    · intro hy'
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hgΓ)) ⟨y, hKXC hy'⟩
      have h2 := h1.mp (Subgroup.mem_subgroupOf.mpr hy')
      have h3 := Subgroup.mem_subgroupOf.mp h2
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * y * g⁻¹⁻¹, ?_, ?_⟩
      · simpa using h3
      · show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
        rw [inv_inv]
        group
  exact normalizer_of_map_eq hmapEq

end CFSG.Quasithin.H13.Ch4

end
