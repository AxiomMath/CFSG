module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem rootE8_isSimpleGroup_of_marking {X : Type*} [Group X]
    {P : LargeEvenMarkProp X} (h : LargeEvenMarking X P) (hZ : Subgroup.center X = ⊥) :
    IsSimpleGroup X := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hθ⟩ := largeEvenRawDatum_exists hraw
  have : IsSimpleGroup R := hs
  have hq : IsSimpleGroup (X ⧸ Subgroup.center X) := θ.isSimpleGroup
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem rootE8_mem_zpowers_of_mem_centralizer {G : Type} [Group G] [Finite G] {r : Row}
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (r.n + 1)} {Y : Subgroup G}
    (h : RootSetting r b₀ K E B Y) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Y)
    (hxK : x ∈ Subgroup.centralizer (K : Set G)) : x ∈ Subgroup.zpowers b₀ := by
  classical
  set A : Subgroup G := Subgroup.zpowers b₀ with hA
  set C : Subgroup G := Subgroup.centralizer ({b₀} : Set G) with hC
  set D : Subgroup G := C ⊓ Y with hD
  have hCD : D ≤ C := by rw [hD]; exact inf_le_left
  have hKD : K ≤ D := by rw [hD, hC, h.cap]; exact le_sup_right
  have hAD : A ≤ D := by rw [hD, hC, hA, h.cap]; exact le_sup_left
  have hDcap : D = A ⊔ K := by rw [hD, hC, hA]; exact h.cap
  have hKnorm : (K.subgroupOf C).Normal := h.std.2.1.1.2.2.1
  have hKconj : ∀ a b : G, a ∈ K → b ∈ C → b * a * b⁻¹ ∈ K :=
    (Subgroup.normal_subgroupOf_iff h.std.2.1.1.2.1).mp hKnorm
  have hKDnorm : (K.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff hKD).mpr fun a b ha hb => hKconj a b ha (hCD hb)
  have : (K.subgroupOf D).Normal := hKDnorm
  have hDsup : K.subgroupOf D ⊔ A.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKD hAD, sup_comm, hDcap, Subgroup.subgroupOf_self]
  have hxsup : (⟨x, hx⟩ : ↥D) ∈ K.subgroupOf D ⊔ A.subgroupOf D := by
    rw [hDsup]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, a, ha, hka⟩ := Subgroup.mem_sup_of_normal_left.mp hxsup
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hkaG : (k : G) * (a : G) = x := congrArg Subtype.val hka
  have hb₀CK : b₀ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k' hk' =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.std.2.1.1.2.1 hk')
  have hACK : A ≤ Subgroup.centralizer (K : Set G) := by
    rw [hA]
    exact Subgroup.zpowers_le.mpr hb₀CK
  have haC : (a : G) ∈ Subgroup.centralizer (K : Set G) := hACK haA
  have hkC : (k : G) ∈ Subgroup.centralizer (K : Set G) := by
    have hkeq : (k : G) = x * (a : G)⁻¹ := by rw [← hkaG]; group
    rw [hkeq]
    exact Subgroup.mul_mem _ hxK (Subgroup.inv_mem _ haC)
  have hk_center : (⟨(k : G), hkK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkC (k' : G) k'.2)
  have hk_one : (k : G) = 1 := by
    have h1 : (⟨(k : G), hkK⟩ : ↥K) = 1 :=
      Subgroup.mem_bot.mp (h.std.2.1.1.2.2.2.1 ▸ hk_center)
    exact congrArg Subtype.val h1
  rw [← hkaG, hk_one, one_mul]
  simpa [hA] using haA

theorem RootSetting.centralizer_inf_eq_bot {G : Type} [Group G] [Finite G] {r : Row} {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (r.n + 1)} {Y : Subgroup G} (h : RootSetting r b₀ K E B Y) :
    Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hzCY, hzY⟩ := Subgroup.mem_inf.mp hz
  have hb₀Y : b₀ ∈ Y := by
    have h1 : b₀ ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Y := by
      rw [h.cap]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
    exact (Subgroup.mem_inf.mp h1).2
  have hKY : K ≤ Y := by
    intro k hk
    have h1 : k ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Y := by
      rw [h.cap]
      exact Subgroup.mem_sup_right hk
    exact (Subgroup.mem_inf.mp h1).2
  have hzC : z ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzCY b₀ hb₀Y).symm
  have hzK : z ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le hKY hzCY
  have hzA : z ∈ Subgroup.zpowers b₀ :=
    rootE8_mem_zpowers_of_mem_centralizer h ⟨hzC, hzY⟩ hzK
  by_cases hz1 : z = 1
  · exact hz1
  · exfalso
    have hb₀ord : orderOf b₀ = 3 := h.std.2.1.1.1
    have hzord3 : orderOf z ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hzA
      rwa [hb₀ord] at this
    have hzord : orderOf z = 3 :=
      orderOf_eq_prime ((orderOf_dvd_iff_pow_eq_one).mp hzord3) hz1
    have hzeq : Subgroup.zpowers z = Subgroup.zpowers b₀ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzA) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hb₀ord]
    have hb₀z : b₀ ∈ Subgroup.zpowers z := by
      rw [hzeq]
      exact Subgroup.mem_zpowers b₀
    have hb₀cent : ∀ y ∈ Y, b₀ * y = y * b₀ := by
      intro y hy
      have hzy : Commute z y := (Subgroup.mem_centralizer_iff.mp hzCY y hy).symm
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb₀z
      rw [← hn]
      exact (Commute.zpow_left hzy n).eq
    have hYC : Y ≤ Subgroup.centralizer ({b₀} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hb₀cent y hy).symm
    have hYeq : Y = Subgroup.zpowers b₀ ⊔ K := by
      rw [← h.cap]
      exact (inf_eq_right.mpr hYC).symm
    have hAY : Subgroup.zpowers b₀ ≤ Y := Subgroup.zpowers_le.mpr hb₀Y
    have hKYnorm : (K.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff hKY).mpr fun a b ha hb =>
        (Subgroup.normal_subgroupOf_iff h.std.2.1.1.2.1).mp h.std.2.1.1.2.2.1 a b ha (hYC hb)
    have : (K.subgroupOf Y).Normal := hKYnorm
    have hYsup : K.subgroupOf Y ⊔ (Subgroup.zpowers b₀).subgroupOf Y = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKY hAY, sup_comm, ← hYeq, Subgroup.subgroupOf_self]
    have hcomm_le : commutator ↥Y ≤ K.subgroupOf Y :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hYsup inferInstance
    have hmap : ⁅Y, Y⁆ ≤ K := by
      calc ⁅Y, Y⁆ = (commutator ↥Y).map Y.subtype := (Subgroup.map_subtype_commutator Y).symm
        _ ≤ (K.subgroupOf Y).map Y.subtype := Subgroup.map_mono (f := Y.subtype) hcomm_le
        _ = K := Subgroup.map_subgroupOf_eq_of_le hKY
    have hcommY : ⁅Y, Y⁆ = Y := by
      rw [← Subgroup.map_subtype_commutator Y, h.isEm.1, Subgroup.map_top,
        Subgroup.range_subtype]
    have hb₀K : b₀ ∈ K := hmap (hcommY.symm ▸ hb₀Y)
    have hb₀center : (⟨b₀, hb₀K⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h.std.2.1.1.2.1 k.2))
    have hb₀one : b₀ = 1 := by
      have h1 : (⟨b₀, hb₀K⟩ : ↥K) = 1 :=
        Subgroup.mem_bot.mp (h.std.2.1.1.2.2.2.1 ▸ hb₀center)
      exact congrArg Subtype.val h1
    rw [hb₀one, orderOf_one] at hb₀ord
    norm_num at hb₀ord

theorem RootSetting.eq_bot_of_isPGroup_two {G : Type} [Group G] [Finite G] {r : Row} {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (r.n + 1)} {Y : Subgroup G} (h : RootSetting r b₀ K E B Y)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ Subgroup.centralizer ({b₀} : Set G) ⊓ Y)
    (hN : Subgroup.centralizer ({b₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G)) : P = ⊥ := by
  classical
  have hKsimple : IsSimpleGroup ↥K :=
    rootE8_isSimpleGroup_of_marking h.std.2.1.1.2.2.2.2.1 h.std.2.1.1.2.2.2.1
  have hKY : K ≤ Y := by
    intro k hk
    have h1 : k ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Y := by
      rw [h.cap]
      exact Subgroup.mem_sup_right hk
    exact (Subgroup.mem_inf.mp h1).2
  have hKCY : K ≤ Subgroup.centralizer ({b₀} : Set G) ⊓ Y :=
    le_inf h.std.2.1.1.2.1 hKY
  have hKNP : K ≤ Subgroup.normalizer (P : Set G) := fun k hk => hN (hKCY hk)
  have hPNK : P ≤ Subgroup.normalizer (K : Set G) := by
    have hCNK : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.std.2.1.1.2.1).mp h.std.2.1.1.2.2.1
    exact (hPC.trans inf_le_left).trans hCNK
  have hPKnormal : ((P ⊓ K).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro p k hp hk
    refine ⟨?_, K.mul_mem (K.mul_mem hk hp.2) (K.inv_mem hk)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKNP hk) p).mp hp.1
  have : ((P ⊓ K).subgroupOf K).Normal := hPKnormal
  have hPKbot : P ⊓ K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P ⊓ K).subgroupOf K) with hbot | htop
    · have hd : Disjoint (P ⊓ K) K := Subgroup.subgroupOf_eq_bot.mp hbot
      have hh := hd.eq_bot
      rwa [inf_of_le_left inf_le_right] at hh
    · exfalso
      have hKleP : K ≤ P := fun x hx => ((Subgroup.subgroupOf_eq_top.mp htop) hx).1
      have : IsPGroup 2 ↥K := hP.to_le hKleP
      have : Nontrivial (Subgroup.center ↥K) :=
        IsPGroup.center_nontrivial (p := 2) (G := ↥K) (hP.to_le hKleP)
      have hsub : Subsingleton (Subgroup.center ↥K) := by
        rw [h.std.2.1.1.2.2.2.1]
        infer_instance
      exact (not_subsingleton_iff_nontrivial.mpr inferInstance) hsub
  have hPKcomm : ⁅P, K⁆ = ⊥ := by
    have h1 : ⁅P, K⁆ ≤ K := (Subgroup.le_normalizer_iff_commutator_le_right).mp hPNK
    have h2 : ⁅P, K⁆ ≤ P := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hKNP
    exact le_bot_iff.mp (hPKbot ▸ le_inf h2 h1)
  have hPCK : P ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPKcomm
  have hPA : P ≤ Subgroup.zpowers b₀ := fun x hx =>
    rootE8_mem_zpowers_of_mem_centralizer h (hPC hx) (hPCK hx)
  have hcard_dvd : Nat.card ↥P ∣ 3 := by
    have hb₀ord : orderOf b₀ = 3 := h.std.2.1.1.1
    have hh := Subgroup.card_dvd_of_le hPA
    rwa [Nat.card_zpowers, hb₀ord] at hh
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥P)).mp hP
  have h2n : 2 ^ n = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2))
      (by rwa [← hn]) (dvd_refl _)
  exact Subgroup.card_eq_one.mp (by rw [hn, h2n])

end CFSG.StandardType.FrameRoute.FS81
