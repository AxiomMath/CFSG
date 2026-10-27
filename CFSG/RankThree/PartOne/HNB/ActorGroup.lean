module

public import CFSG.RankThree.PartOne.HNB.Native
public import CFSG.RankThree.PartOne.HNB.Tools
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.GroupTheory.SteinbergBMSectionTenSetup
public import CFSG.RankThree.GroupTheory.ThetaComponents

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree
open scoped Pointwise
open CFSG.Blueprint.NativeSporadic (Carrier)

structure ActorGroup (G : Type) [Group G] (A L : Subgroup G) where
  c : G
  N : NativeIn G L
  y : G
  hcA : c ∈ A
  hc1 : c ≠ 1
  hc5 : orderOf c = 5
  hcL : L ≤ Subgroup.centralizer ({c} : Set G)
  hLθ : L ∈ thetaComponentsAt 5 c
  hcLinf : Subgroup.zpowers c ⊓ L = ⊥
  hyY : y ∈ N.Y
  hy5 : orderOf y = 5

namespace ActorGroup

variable {G : Type} [Group G] {A L : Subgroup G} (d : ActorGroup G A L)

abbrev x : G := d.N.x
abbrev t : G := d.N.t
abbrev K : Subgroup G := d.N.K
abbrev Y : Subgroup G := d.N.Y

@[expose] def B : Subgroup G := Subgroup.zpowers d.c ⊔ Subgroup.zpowers d.x

@[expose] def A0 : Subgroup G := d.B ⊔ Subgroup.zpowers d.y

theorem y_mem_K : d.y ∈ d.K := d.N.hYK d.hyY

theorem x_mem_L : d.x ∈ L := d.N.hxL

theorem K_le_L : d.K ≤ L := d.N.hKL

theorem y_mem_L : d.y ∈ L := d.K_le_L d.y_mem_K

theorem commute_c_of_mem_L {g : G} (hg : g ∈ L) : g * d.c = d.c * g :=
  Subgroup.mem_centralizer_singleton_iff.mp (d.hcL hg)

theorem commute_x_of_mem_K {g : G} (hg : g ∈ d.K) : g * d.x = d.x * g :=
  Subgroup.mem_centralizer_singleton_iff.mp (d.N.hKx hg)

theorem c_mul_x : d.c * d.x = d.x * d.c := (d.commute_c_of_mem_L d.x_mem_L).symm

theorem c_mul_y : d.c * d.y = d.y * d.c := (d.commute_c_of_mem_L d.y_mem_L).symm

theorem x_mul_y : d.x * d.y = d.y * d.x := (d.commute_x_of_mem_K d.y_mem_K).symm

theorem B_le_centralizer_zpowers_y : d.B ≤ Subgroup.centralizer (Subgroup.zpowers d.y : Set G) :=
  sup_le (zpowers_le_centralizer_zpowers d.c_mul_y)
    (zpowers_le_centralizer_zpowers d.x_mul_y)

theorem zpowers_c_le_centralizer_zpowers_x :
    Subgroup.zpowers d.c ≤ Subgroup.centralizer (Subgroup.zpowers d.x : Set G) :=
  zpowers_le_centralizer_zpowers d.c_mul_x

theorem zpowers_inf_L_eq_bot_iff_mem {u : G} (hu : u ∈ Subgroup.zpowers d.c) (huL : u ∈ L) :
    u = 1 := by
  have := d.hcLinf
  exact Subgroup.mem_bot.mp (this ▸ Subgroup.mem_inf.mpr ⟨hu, huL⟩)

theorem zpowers_c_inf_zpowers_x : Subgroup.zpowers d.c ⊓ Subgroup.zpowers d.x = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  obtain ⟨hc, hx⟩ := Subgroup.mem_inf.mp hu
  refine d.zpowers_inf_L_eq_bot_iff_mem hc ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact zpow_mem d.x_mem_L n

theorem B_inf_zpowers_y : d.B ⊓ Subgroup.zpowers d.y = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  obtain ⟨hB, hy⟩ := Subgroup.mem_inf.mp hu
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers d.c)
    (Subgroup.zpowers d.x)
    ((d.zpowers_c_le_centralizer_zpowers_x).trans (Subgroup.centralizer_le_normalizer _))
  have hu' : u ∈ ((Subgroup.zpowers d.c : Subgroup G) : Set G) * (Subgroup.zpowers d.x : Set G) := by
    rw [← hset]
    exact hB
  obtain ⟨a, ha, b, hb, hab⟩ := hu'
  change a * b = u at hab
  have huK : u ∈ d.K := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact zpow_mem d.y_mem_K n
  have huL : u ∈ L := d.K_le_L huK
  have hbL : b ∈ L := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact zpow_mem d.x_mem_L n
  have ha1 : a = 1 := by
    apply d.zpowers_inf_L_eq_bot_iff_mem ha
    have : a = u * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact L.mul_mem huL (L.inv_mem hbL)
  rw [ha1, one_mul] at hab
  have hub : u ∈ Subgroup.zpowers d.x ⊓ d.K := Subgroup.mem_inf.mpr ⟨hab ▸ hb, huK⟩
  rw [d.N.hxK] at hub
  exact Subgroup.mem_bot.mp hub

theorem isElementaryAbelian_zpowers_c : IsElementaryAbelian 5 (Subgroup.zpowers d.c) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← d.hc5]; exact pow_orderOf_eq_one d.c)

theorem isElementaryAbelian_zpowers_x : IsElementaryAbelian 5 (Subgroup.zpowers d.x) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← d.N.hx5]; exact pow_orderOf_eq_one d.x)

theorem isElementaryAbelian_zpowers_y : IsElementaryAbelian 5 (Subgroup.zpowers d.y) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← d.hy5]; exact pow_orderOf_eq_one d.y)

theorem isElementaryAbelian_B : IsElementaryAbelian 5 d.B :=
  SteinbergBM.isElementaryAbelian_sup_of_le_centralizer d.isElementaryAbelian_zpowers_c
    d.isElementaryAbelian_zpowers_x d.zpowers_c_le_centralizer_zpowers_x

theorem isElementaryAbelian_A0 : IsElementaryAbelian 5 d.A0 :=
  SteinbergBM.isElementaryAbelian_sup_of_le_centralizer d.isElementaryAbelian_B
    d.isElementaryAbelian_zpowers_y d.B_le_centralizer_zpowers_y

theorem card_B : Nat.card d.B = 25 := by
  rw [B, SteinbergBM.card_sup_of_le_centralizer_of_inf_eq_bot d.zpowers_c_le_centralizer_zpowers_x
    d.zpowers_c_inf_zpowers_x, Nat.card_zpowers, Nat.card_zpowers, d.hc5, d.N.hx5]

theorem card_A0 : Nat.card d.A0 = 5 ^ 3 := by
  rw [A0, SteinbergBM.card_sup_of_le_centralizer_of_inf_eq_bot d.B_le_centralizer_zpowers_y
    d.B_inf_zpowers_y, d.card_B, Nat.card_zpowers, d.hy5]
  norm_num

theorem B_le_A0 : d.B ≤ d.A0 := le_sup_left

theorem c_mem_B : d.c ∈ d.B := Subgroup.mem_sup_left (Subgroup.mem_zpowers d.c)

theorem c_mem_A0 : d.c ∈ d.A0 := d.B_le_A0 d.c_mem_B

theorem K_le_centralizer_B : d.K ≤ Subgroup.centralizer (d.B : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact d.commute_c_of_mem_L (d.K_le_L hk)
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact d.commute_x_of_mem_K hk

theorem A0_le_centralizer_t : d.A0 ≤ Subgroup.centralizer ({d.t} : Set G) := by
  have htK : d.t ∈ d.K := d.N.hYK d.N.htY
  have hc : d.c ∈ Subgroup.centralizer ({d.t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.commute_c_of_mem_L (d.K_le_L htK)).symm
  have hx : d.x ∈ Subgroup.centralizer ({d.t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.commute_x_of_mem_K htK).symm
  have hy : d.y ∈ Subgroup.centralizer ({d.t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.N.htc d.y d.hyY)
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr hc) (Subgroup.zpowers_le.mpr hx))
    (Subgroup.zpowers_le.mpr hy)

theorem Y_le_centralizer_t : d.Y ≤ Subgroup.centralizer ({d.t} : Set G) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (d.N.htc y hy)

theorem centralizer_K_inf_A0_le_B {a : G} (ha : a ∈ d.A0) (hK : ∀ k ∈ d.K, a * k = k * a) :
    a ∈ d.B := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right d.B (Subgroup.zpowers d.y)
    (d.B_le_centralizer_zpowers_y.trans (Subgroup.centralizer_le_normalizer _))
  have ha' : a ∈ (d.B : Set G) * (Subgroup.zpowers d.y : Set G) := by
    rw [← hset]
    exact ha
  obtain ⟨b, hb, u, hu, hbu⟩ := ha'
  change b * u = a at hbu
  subst hbu
  have huK : u ∈ d.K := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact zpow_mem d.y_mem_K n
  have hbK : ∀ k ∈ d.K, b * k = k * b := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (d.K_le_centralizer_B hk) b hb)
  have hu1 : u = 1 := by
    have hcen : (⟨u, huK⟩ : d.K) ∈ Subgroup.center d.K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      show (k : G) * u = u * (k : G)
      have h1 := hK k k.2
      have h2 := hbK k k.2
      calc (k : G) * u = b⁻¹ * (b * k) * u := by group
        _ = b⁻¹ * (k * b) * u := by rw [h2]
        _ = b⁻¹ * (k * (b * u)) := by group
        _ = b⁻¹ * ((b * u) * k) := by rw [h1]
        _ = (b⁻¹ * b) * (u * k) := by group
        _ = u * k := by group
    have := d.N.hKsimple
    rw [SteinbergBM.center_eq_bot_of_isSimpleGroup d.N.hKnonab] at hcen
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcen)
  rw [hu1, mul_one]
  exact hb

theorem sectionTen_A0 [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    SteinbergBM.SectionTenSetup G 5 d.A0 := by
  obtain ⟨hs, hn, hKP, hCP, he, hq, -, -, -, hpref⟩ := h
  refine ⟨hs, hn, hKP, hCP, he, hq, d.isElementaryAbelian_A0, d.card_A0, ⟨Subgroup.zpowers d.t, ?_,
    ?_, ?_⟩, hpref⟩
  · intro hbot
    have : d.N.t = 1 := by
      have := Subgroup.mem_zpowers d.N.t
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have h2 := d.N.ht2
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.N.ht2]; norm_num)
  · intro a ha
    exact mem_normalizer_zpowers_of_commute
      (Subgroup.mem_centralizer_singleton_iff.mp (d.A0_le_centralizer_t ha))

end ActorGroup

theorem exists_orderOf_five_sl2 :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), orderOf g = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hall : ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), g ^ 5 = 1 ∧ g ≠ 1 := by decide
  obtain ⟨g, h1, h2⟩ := hall
  exact ⟨g, orderOf_eq_prime h1 h2⟩

theorem exists_actorGroup_of_nativeData {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G 5 A) (hL : L ∈ thetaComponentFamily 5 A) {M : Type}
    [Group M] (hs : IsSimpleGroup M) (hn : ∃ a b : M, a * b ≠ b * a) (hN : NativeData M)
    (e : M ≃* L) : Nonempty (ActorGroup G A L) := by
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hL
  obtain ⟨N⟩ := nativeIn_of_nativeData hN e
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hAe : IsElementaryAbelian 5 A := h.2.2.2.2.2.2.1
  have hc5 : orderOf c = 5 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := A) c hcA) hc1
  have hcL : L ≤ Subgroup.centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hLc).1
  have hLs : IsSimpleGroup L := e.isSimpleGroup_congr.mp hs
  have hLn : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨e a, e b, fun hh => hab (e.injective (by rw [map_mul, map_mul, hh]))⟩
  have hcLinf : Subgroup.zpowers c ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    obtain ⟨huc, huL⟩ := Subgroup.mem_inf.mp hu
    have hcen : (⟨u, huL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      show (l : G) * u = u * (l : G)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp huc
      have hlc : (l : G) * c = c * l :=
        Subgroup.mem_centralizer_singleton_iff.mp (hcL l.2)
      exact ((Commute.zpow_right (show Commute (l : G) c from hlc) n)).eq.symm ▸ rfl
    rw [SteinbergBM.center_eq_bot_of_isSimpleGroup hLn] at hcen
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcen)
  obtain ⟨σ⟩ := N.hYsl
  obtain ⟨g, hg⟩ := exists_orderOf_five_sl2
  refine ⟨⟨c, N, ((σ.symm g : N.Y) : G), hcA, hc1, hc5, hcL, hLc, hcLinf, (σ.symm g).2, ?_⟩⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq σ.symm g]
  exact hg

theorem exists_actorGroup {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G 5 A) (hL : L ∈ thetaComponentFamily 5 A)
    (hN : HNNativeFive) (e : Carrier .HN ≃* L) : Nonempty (ActorGroup G A L) :=
  exists_actorGroup_of_nativeData h hL hN.1 hN.2.1 hN.2.2 e

end CFSG.RankThree.PartOne.HNB
