module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.ClassicalInvolution.Models.Transfer.Basic
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.Quasithin.Recognition.HSTypeModels

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

private theorem fs81SixLift_notMem_of_order_three {G : Type} [Group G] {N : Subgroup G}
    (hN2 : IsPGroup 2 N) {x : G} (hx : orderOf x = 3) : x ∉ N := by
  intro hxN
  have hne : (⟨x, hxN⟩ : ↥N) ≠ 1 := by
    intro h
    have h1 : orderOf x = 1 := by
      calc orderOf x = orderOf (⟨x, hxN⟩ : ↥N) :=
        Subgroup.orderOf_coe (⟨x, hxN⟩ : ↥N)
        _ = 1 := by rw [h, orderOf_one]
    rw [hx] at h1
    norm_num at h1
  have h2 : 2 ∣ orderOf (⟨x, hxN⟩ : ↥N) := hN2.dvd_orderOf hne
  rw [← Subgroup.orderOf_coe (⟨x, hxN⟩ : ↥N), hx] at h2
  norm_num at h2

private theorem fs81SixLift_orderOf_mk_of_order_three {G : Type} [Group G] [Finite G]
    {C N : Subgroup G} [hN' : (N.subgroupOf C).Normal]
    (hN2 : IsPGroup 2 N) {x : G} (hxC : x ∈ C) (hx : orderOf x = 3) :
    orderOf (QuotientGroup.mk' (N.subgroupOf C) ⟨x, hxC⟩) = 3 := by
  have hcoe : orderOf x = orderOf (⟨x, hxC⟩ : ↥C) :=
    Subgroup.orderOf_coe (⟨x, hxC⟩ : ↥C)
  have hdvd0 := orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf C)) (⟨x, hxC⟩ : ↥C)
  have hdvd : orderOf (QuotientGroup.mk' (N.subgroupOf C) ⟨x, hxC⟩) ∣ 3 := by
    rw [← hcoe, hx] at hdvd0
    exact hdvd0
  have hne : orderOf (QuotientGroup.mk' (N.subgroupOf C) ⟨x, hxC⟩) ≠ 1 := by
    intro h1
    have hcls : QuotientGroup.mk' (N.subgroupOf C) ⟨x, hxC⟩ = 1 :=
      orderOf_eq_one_iff.mp h1
    have hxN : x ∈ N :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hcls)
    exact fs81SixLift_notMem_of_order_three hN2 hx hxN
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · exact absurd h hne
  · exact h

private theorem fs81SixLift_notMem_of_inverts {G : Type} [Group G] [Finite G]
    {C N : Subgroup G} (hCN : C ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N)
    {b k : G} (hbC : b ∈ C) (hkC : k ∈ C) (hb : orderOf b = 3)
    (hkb : k * b * k⁻¹ = b⁻¹) (hkN : k ∈ N) : False := by
  have hb2N : b ^ (-2 : ℤ) ∈ N := by
    have h1 : b * k⁻¹ * b⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hCN hbC) k⁻¹).mp (N.inv_mem hkN)
    have h2 : k * (b * k⁻¹ * b⁻¹) ∈ N := N.mul_mem hkN h1
    have hcomm : ⁅k, b⁆ = b ^ (-2 : ℤ) := by
      rw [show ⁅k, b⁆ = k * b * k⁻¹ * b⁻¹ from rfl, hkb]
      group
    rw [← hcomm]
    change k * b * k⁻¹ * b⁻¹ ∈ N
    simpa [mul_assoc] using h2
  have hord : orderOf (b ^ (-2 : ℤ)) = 3 := by
    have hz : b ^ (-2 : ℤ) = (b ^ 2)⁻¹ := by simp [zpow_neg]
    rw [hz, orderOf_inv, orderOf_pow, hb]
    norm_num
  exact fs81SixLift_notMem_of_order_three hN2 hord hb2N

private theorem fs81SixLift_orderOf_mk_invol {G : Type} [Group G] [Finite G]
    {C M N : Subgroup G} [hN' : (N.subgroupOf C).Normal]
    (hMC : M ≤ C) (hCN : C ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N)
    {b k : G} (hbM : b ∈ M) (hkM : k ∈ M) (hb : orderOf b = 3)
    (hk : orderOf k = 2) (hkb : k * b * k⁻¹ = b⁻¹) :
    orderOf (QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩) = 2 := by
  have hcoe : orderOf k = orderOf (⟨k, hMC hkM⟩ : ↥C) :=
    Subgroup.orderOf_coe (⟨k, hMC hkM⟩ : ↥C)
  have hdvd0 := orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf C)) (⟨k, hMC hkM⟩ : ↥C)
  have hdvd : orderOf (QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩) ∣ 2 := by
    rw [← hcoe, hk] at hdvd0
    exact hdvd0
  have hne : orderOf (QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩) ≠ 1 := by
    intro h1
    have hcls : QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩ = 1 :=
      orderOf_eq_one_iff.mp h1
    have hkN : k ∈ N :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hcls)
    exact fs81SixLift_notMem_of_inverts hCN hN2 (hMC hbM) (hMC hkM) hb hkb hkN
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
  · exact absurd h hne
  · exact h

private theorem fs81SixLift_commutator_mem {G : Type} [Group G] {C N : Subgroup G}
    [hN' : (N.subgroupOf C).Normal] {x y : ↥C}
    (h : QuotientGroup.mk' (N.subgroupOf C) x * QuotientGroup.mk' (N.subgroupOf C) y =
      QuotientGroup.mk' (N.subgroupOf C) y * QuotientGroup.mk' (N.subgroupOf C) x) :
    (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ N := by
  have h1 : QuotientGroup.mk' (N.subgroupOf C) (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

private theorem fs81SixLift_mem_sup_of_commutator {G : Type} [Group G] [Finite G]
    {M N C T : Subgroup G} (hNM : N ≤ M) (hMC : M ≤ C)
    (hCN : C ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N)
    {t m : G} (htC : t ∈ C) (hmM : m ∈ M) (ht : orderOf t = 3)
    (hct : ∀ x ∈ M, x * t = t * x → x ∈ T) (hNT : N ≤ T)
    (hcomm : m * t * m⁻¹ * t⁻¹ ∈ N) : m ∈ T := by
  obtain ⟨n, hcard⟩ := hN2.exists_card_eq
  have hcop : Nat.Coprime (orderOf t) (Nat.card N) := by
    rw [ht, hcard]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hNt : ∀ x ∈ N, t * x * t⁻¹ ∈ N := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hCN htC) x).mp hx
  have hg : m⁻¹ * (t * m * t⁻¹) ∈ N := by
    have h1 : t * m * t⁻¹ * m⁻¹ ∈ N := by
      simpa [mul_inv_rev, mul_assoc] using N.inv_mem hcomm
    have h2 : m⁻¹ * (t * m * t⁻¹ * m⁻¹) * m ∈ N := by
      simpa [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (hCN (C.inv_mem (hMC hmM))) _).mp h1
    simpa [mul_assoc] using h2
  obtain ⟨n, hn, hfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime N hNt hg hcop
  have hcomm' : t * (m * n) = (m * n) * t := by
    calc t * (m * n) = t * (m * n) * t⁻¹ * t := by group
      _ = (m * n) * t := by rw [hfix]
  have hmn : m * n ∈ T :=
    hct (m * n) (M.mul_mem hmM (hNM hn)) hcomm'.symm
  have hm : m = (m * n) * n⁻¹ := by group
  rw [hm]
  exact T.mul_mem hmn (hNT (N.inv_mem hn))

private theorem fs81SixLift_mem_map_sup {G : Type} [Group G] {C N K : Subgroup G}
    [hN' : (N.subgroupOf C).Normal] (hNC : N ≤ C) (hKC : K ≤ C) {m : G} (hmC : m ∈ C)
    (hm : m ∈ N ⊔ K) :
    QuotientGroup.mk' (N.subgroupOf C) ⟨m, hmC⟩ ∈
      (K.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)) := by
  have hx : (⟨m, hmC⟩ : ↥C) ∈ (N.subgroupOf C) ⊔ K.subgroupOf C := by
    have h1 : (⟨m, hmC⟩ : ↥C) ∈ (N ⊔ K).subgroupOf C := Subgroup.mem_subgroupOf.mpr hm
    rwa [Subgroup.subgroupOf_sup hNC hKC] at h1
  have hx' : (⟨m, hmC⟩ : ↥C) ∈
      (↑(N.subgroupOf C ⊔ K.subgroupOf C) : Set ↥C) := hx
  rw [Subgroup.normal_mul, Set.mem_mul] at hx'
  obtain ⟨y, hy, z, hz, hxz⟩ := hx'
  rw [← hxz, map_mul]
  have h1 : QuotientGroup.mk' (N.subgroupOf C) y = 1 :=
    (QuotientGroup.eq_one_iff y).mpr hy
  have h2 : QuotientGroup.mk' (N.subgroupOf C) z ∈
      (K.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)) :=
    Subgroup.mem_map_of_mem _ hz
  rw [h1, one_mul]
  exact h2

private theorem fs81SixLift_zpowers_subgroupOf {G : Type} [Group G] {C : Subgroup G} {t : G}
    (htC : t ∈ C) :
    (Subgroup.zpowers t).subgroupOf C = Subgroup.zpowers (⟨t, htC⟩ : ↥C) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    Subgroup.mem_closure_singleton, Subgroup.mem_closure_singleton]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

private theorem fs81SixLift_closure_subgroupOf {G : Type} [Group G] {C : Subgroup G} {b k : G}
    (hbC : b ∈ C) (hkC : k ∈ C) :
    (Subgroup.closure ({b, k} : Set G)).subgroupOf C =
      Subgroup.closure ({⟨b, hbC⟩, ⟨k, hkC⟩} : Set ↥C) := by
  have hle : Subgroup.closure ({b, k} : Set G) ≤ C :=
    (Subgroup.closure_le C).mpr (by rintro x (rfl | rfl) <;> assumption)
  apply Subgroup.map_injective (f := C.subtype) (Subgroup.subtype_injective C)
  rw [Subgroup.map_subgroupOf_eq_of_le hle, MonoidHom.map_closure]
  simp

private theorem fs81SixLift_normalizer {G : Type} [Group G] {C M N P : Subgroup G}
    [hN' : (N.subgroupOf C).Normal]
    (hPM : P ≤ Subgroup.normalizer (M : Set G)) :
    (P.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)) ≤
      Subgroup.normalizer (((M.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)) :
        Set (↥C ⧸ (N.subgroupOf C)))) := by
  have h1 : P.subgroupOf C ≤ Subgroup.normalizer (M.subgroupOf C : Set ↥C) := by
    rw [← Subgroup.comap_subtype P C, ← Subgroup.comap_subtype M C]
    exact (Subgroup.comap_mono hPM).trans (Subgroup.le_normalizer_comap C.subtype)
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

private theorem fs81SixLift_Phat_equiv {G : Type} [Group G] {C N P : Subgroup G}
    [hN' : (N.subgroupOf C).Normal] (hPC : P ≤ C) (hPN : P ⊓ N = ⊥)
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nonempty (↥((P.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hψ : ∀ x ∈ P.subgroupOf C, x ∈ (QuotientGroup.mk' (N.subgroupOf C)).ker → x = 1 := by
    intro x hx hxker
    have hx1 : QuotientGroup.mk' (N.subgroupOf C) x = 1 := MonoidHom.mem_ker.mp hxker
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    have hxN : (x : G) ∈ N :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x).mp hx1)
    have h : (x : G) ∈ P ⊓ N := ⟨hxP, hxN⟩
    rw [hPN] at h
    exact Subtype.ext (Subgroup.mem_bot.mp h)
  obtain ⟨e⟩ := hP
  have heP := CFSG.ClassicalInvolution.Models.Transfer.mulEquivMap
    (θ := QuotientGroup.mk' (N.subgroupOf C)) (L := P.subgroupOf C) hψ
  exact ⟨heP.symm.trans ((Subgroup.subgroupOfEquivOfLe hPC).trans e)⟩

private theorem fs81SixLift_P_inf_N {G : Type} [Group G]
    {C N P : Subgroup G} (hPC : P ≤ C) (hCN : C ≤ Subgroup.normalizer (N : Set G))
    (hN2 : IsPGroup 2 N) {b₁ : G} (hb₁P : b₁ ∈ P) (hb₁ : orderOf b₁ = 3)
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    P ⊓ N = ⊥ := by
  classical
  haveI hPsimp : IsSimpleGroup ↥P := by
    obtain ⟨e⟩ := hP
    exact (MulEquiv.isSimpleGroup_congr e).mpr
      CFSG.Quasithin.HSType.isSimpleGroup_SL_three_two
  have hPnN : P ≤ Subgroup.normalizer (P ⊓ N : Set G) := by
    have h1 : P ≤ Subgroup.normalizer (N : Set G) := hPC.trans hCN
    have h2 : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
    have h3 : P ≤ Subgroup.normalizer (N : Set G) ⊓ Subgroup.normalizer (P : Set G) :=
      le_inf h1 h2
    have h4 := h3.trans (Subgroup.inf_normalizer_le_normalizer_inf (H := N) (K := P))
    simpa [inf_comm] using h4
  haveI hPNnormal : ((P ⊓ N).subgroupOf P).Normal := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer_inf (H := N) (K := P)).mpr
      (by simpa [inf_comm] using hPnN)
    simpa [Subgroup.inf_subgroupOf_right] using h
  rcases Subgroup.Normal.eq_bot_or_eq_top ((P ⊓ N).subgroupOf P) with hbot | htop
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥P) ∈ (P ⊓ N).subgroupOf P :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [hbot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hx'))
  · exfalso
    have hPNle : P ≤ N := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥P) ∈ (P ⊓ N).subgroupOf P := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hx').2
    exact fs81SixLift_notMem_of_order_three hN2 hb₁ (hPNle hb₁P)

private theorem fs81SixLift_centralizer_zpowers {G : Type} [Group G] [Finite G]
    {C M N : Subgroup G} [hN' : (N.subgroupOf C).Normal]
    (hNM : N ≤ M) (hMC : M ≤ C) (hCN : C ≤ Subgroup.normalizer (N : Set G))
    (hN2 : IsPGroup 2 N) {b : G} (hbM : b ∈ M) (hb : orderOf b = 3)
    (hcb : ∀ m ∈ M, m * b = b * m → m ∈ N ⊔ Subgroup.zpowers b) :
    ∀ x ∈ (M.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)),
      x * QuotientGroup.mk' (N.subgroupOf C) ⟨b, hMC hbM⟩ =
        QuotientGroup.mk' (N.subgroupOf C) ⟨b, hMC hbM⟩ * x →
      x ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf C) ⟨b, hMC hbM⟩) := by
  intro x hx hcomm
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
  have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
  have hmC : (m : G) ∈ C := hMC hmM
  have hbC : b ∈ C := hMC hbM
  have hcommN : (m : G) * b * (m : G)⁻¹ * b⁻¹ ∈ N :=
    fs81SixLift_commutator_mem (x := m) (y := (⟨b, hbC⟩ : ↥C)) hcomm
  have hsup : (m : G) ∈ N ⊔ Subgroup.zpowers b :=
    fs81SixLift_mem_sup_of_commutator (T := N ⊔ Subgroup.zpowers b) hNM hMC hCN hN2
      hbC hmM hb hcb le_sup_left hcommN
  have hK : Subgroup.zpowers b ≤ C := Subgroup.zpowers_le.mpr hbC
  have h1 := fs81SixLift_mem_map_sup (K := Subgroup.zpowers b) (hNM.trans hMC) hK hmC hsup
  rwa [fs81SixLift_zpowers_subgroupOf hbC, MonoidHom.map_zpowers] at h1

private theorem fs81SixLift_centralizer_closure {G : Type} [Group G] [Finite G]
    {C M N P : Subgroup G} [hN' : (N.subgroupOf C).Normal]
    (hNM : N ≤ M) (hMC : M ≤ C) (hCN : C ≤ Subgroup.normalizer (N : Set G))
    (hN2 : IsPGroup 2 N) (hPC : P ≤ C) {b k b₁ : G} (hbM : b ∈ M) (hkM : k ∈ M)
    (hb₁P : b₁ ∈ P) (hb₁ : orderOf b₁ = 3)
    (hcb₁ : ∀ m ∈ M, m * b₁ = b₁ * m → m ∈ N ⊔ Subgroup.closure ({b, k} : Set G)) :
    ∀ x ∈ (M.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)),
      x * QuotientGroup.mk' (N.subgroupOf C) ⟨b₁, hPC hb₁P⟩ =
        QuotientGroup.mk' (N.subgroupOf C) ⟨b₁, hPC hb₁P⟩ * x →
      x ∈ Subgroup.closure ({QuotientGroup.mk' (N.subgroupOf C) ⟨b, hMC hbM⟩,
        QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩} : Set (↥C ⧸ (N.subgroupOf C))) := by
  intro x hx hcomm
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
  have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
  have hmC : (m : G) ∈ C := hMC hmM
  have hbC : b ∈ C := hMC hbM
  have hkC : k ∈ C := hMC hkM
  have hb₁C : b₁ ∈ C := hPC hb₁P
  have hcommN : (m : G) * b₁ * (m : G)⁻¹ * b₁⁻¹ ∈ N :=
    fs81SixLift_commutator_mem (x := m) (y := (⟨b₁, hb₁C⟩ : ↥C)) hcomm
  have hsup : (m : G) ∈ N ⊔ Subgroup.closure ({b, k} : Set G) :=
    fs81SixLift_mem_sup_of_commutator (T := N ⊔ Subgroup.closure ({b, k} : Set G))
      hNM hMC hCN hN2 hb₁C hmM hb₁ hcb₁ le_sup_left hcommN
  have hK : Subgroup.closure ({b, k} : Set G) ≤ C :=
    (Subgroup.closure_le C).mpr (by rintro x (rfl | rfl) <;> assumption)
  have h1 := fs81SixLift_mem_map_sup (K := Subgroup.closure ({b, k} : Set G))
    (hNM.trans hMC) hK hmC hsup
  rw [fs81SixLift_closure_subgroupOf hbC hkC, MonoidHom.map_closure] at h1
  simpa using h1

private theorem fs81SixLift_conj_mk {G : Type} [Group G] {C N : Subgroup G}
    [hN' : (N.subgroupOf C).Normal] {b k : G} (hbC : b ∈ C) (hkC : k ∈ C)
    (hkb : k * b * k⁻¹ = b⁻¹) :
    QuotientGroup.mk' (N.subgroupOf C) (⟨k, hkC⟩ : ↥C) *
        QuotientGroup.mk' (N.subgroupOf C) (⟨b, hbC⟩ : ↥C) *
        (QuotientGroup.mk' (N.subgroupOf C) (⟨k, hkC⟩ : ↥C))⁻¹ =
      (QuotientGroup.mk' (N.subgroupOf C) (⟨b, hbC⟩ : ↥C))⁻¹ := by
  have hC : (⟨k, hkC⟩ : ↥C) * ⟨b, hbC⟩ * (⟨k, hkC⟩ : ↥C)⁻¹ = (⟨b, hbC⟩ : ↥C)⁻¹ := by
    apply Subtype.ext
    simpa using hkb
  simpa only [map_mul, map_inv] using
    congrArg (QuotientGroup.mk' (N.subgroupOf C)) hC

private theorem fs81SixLift_Mhat_le {G : Type} [Group G] [Finite G]
    {C M N P : Subgroup G} {b k b₁ : G} [hN' : (N.subgroupOf C).Normal]
    (h : FS81SixLemma)
    (hNM : N ≤ M) (hMC : M ≤ C) (hCN : C ≤ Subgroup.normalizer (N : Set G))
    (hN2 : IsPGroup 2 N) (hPC : P ≤ C) (hPM : P ≤ Subgroup.normalizer (M : Set G))
    (hbM : b ∈ M) (hkM : k ∈ M) (hb : orderOf b = 3) (hk : orderOf k = 2)
    (hkb : k * b * k⁻¹ = b⁻¹)
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hb₁P : b₁ ∈ P) (hb₁ : orderOf b₁ = 3)
    (hPk : ∀ p ∈ P, p * k = k * p)
    (hcb : ∀ m ∈ M, m * b = b * m → m ∈ N ⊔ Subgroup.zpowers b)
    (hcb₁ : ∀ m ∈ M, m * b₁ = b₁ * m → m ∈ N ⊔ Subgroup.closure ({b, k} : Set G)) :
    (M.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)) ≤
      Subgroup.closure ({QuotientGroup.mk' (N.subgroupOf C) ⟨b, hMC hbM⟩,
        QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩} :
          Set (↥C ⧸ (N.subgroupOf C))) := by
  let π : ↥C →* ↥C ⧸ (N.subgroupOf C) := QuotientGroup.mk' (N.subgroupOf C)
  let Mhat : Subgroup (↥C ⧸ (N.subgroupOf C)) := (M.subgroupOf C).map π
  let Phat : Subgroup (↥C ⧸ (N.subgroupOf C)) := (P.subgroupOf C).map π
  have hPN : P ⊓ N = ⊥ := fs81SixLift_P_inf_N hPC hCN hN2 hb₁P hb₁ hP
  have hbhatM : π ⟨b, hMC hbM⟩ ∈ Mhat :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbM)
  have hkhatM : π ⟨k, hMC hkM⟩ ∈ Mhat :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hkM)
  have hb1hatP : π ⟨b₁, hPC hb₁P⟩ ∈ Phat :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb₁P)
  have hbhat : orderOf (π ⟨b, hMC hbM⟩) = 3 :=
    fs81SixLift_orderOf_mk_of_order_three hN2 (hMC hbM) hb
  have hkhat : orderOf (π ⟨k, hMC hkM⟩) = 2 :=
    fs81SixLift_orderOf_mk_invol hMC hCN hN2 hbM hkM hb hk hkb
  have hb1hat : orderOf (π ⟨b₁, hPC hb₁P⟩) = 3 :=
    fs81SixLift_orderOf_mk_of_order_three hN2 (hPC hb₁P) hb₁
  have hconj : π ⟨k, hMC hkM⟩ * π ⟨b, hMC hbM⟩ * (π ⟨k, hMC hkM⟩)⁻¹ =
      (π ⟨b, hMC hbM⟩)⁻¹ := fs81SixLift_conj_mk (hMC hbM) (hMC hkM) hkb
  have hnorm : Phat ≤ Subgroup.normalizer (Mhat : Set _) := fs81SixLift_normalizer hPM
  have hPhat : Nonempty (↥Phat ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    fs81SixLift_Phat_equiv hPC hPN hP
  have hcent : ∀ p ∈ Phat, p * π ⟨k, hMC hkM⟩ = π ⟨k, hMC hkM⟩ * p := by
    rintro p ⟨q, hq, rfl⟩
    have hqk : (q : G) * k = k * (q : G) := hPk _ (Subgroup.mem_subgroupOf.mp hq)
    have hqk' : (q : ↥C) * ⟨k, hMC hkM⟩ = ⟨k, hMC hkM⟩ * q := by
      apply Subtype.ext
      simpa using hqk
    rw [← map_mul, ← map_mul, hqk']
  exact h (↥C ⧸ (N.subgroupOf C)) Mhat Phat (π ⟨b, hMC hbM⟩) (π ⟨k, hMC hkM⟩)
    (π ⟨b₁, hPC hb₁P⟩) hbhatM hkhatM hbhat hkhat hconj hnorm hPhat hb1hatP hb1hat hcent
    (fs81SixLift_centralizer_zpowers hNM hMC hCN hN2 hbM hb hcb)
    (fs81SixLift_centralizer_closure hNM hMC hCN hN2 hPC hbM hkM hb₁P hb₁ hcb₁)

theorem fs81SixLift_of_sixLemma (h : FS81SixLemma) : FS81SixLift := by
  classical
  intro G _ _ C M N P b k b₁ hNM hMC hCN hN2 hPC hPM hbM hkM hb hk hkb hP hb₁P hb₁ hPk
    hcb hcb₁
  have hNC : N ≤ C := hNM.trans hMC
  haveI hN' : (N.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mpr hCN
  have hMhat := fs81SixLift_Mhat_le h hNM hMC hCN hN2 hPC hPM hbM hkM hb hk hkb hP hb₁P hb₁
    hPk hcb hcb₁
  intro m hm
  let x : ↥C := ⟨m, hMC hm⟩
  have hxM : x ∈ M.subgroupOf C := Subgroup.mem_subgroupOf.mpr hm
  have hxMhat : QuotientGroup.mk' (N.subgroupOf C) x ∈
      (M.subgroupOf C).map (QuotientGroup.mk' (N.subgroupOf C)) :=
    Subgroup.mem_map_of_mem _ hxM
  have hxclos : QuotientGroup.mk' (N.subgroupOf C) x ∈
      Subgroup.closure ({QuotientGroup.mk' (N.subgroupOf C) ⟨b, hMC hbM⟩,
        QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩} :
          Set (↥C ⧸ (N.subgroupOf C))) := hMhat hxMhat
  have hmapclos : (Subgroup.closure ({⟨b, hMC hbM⟩, ⟨k, hMC hkM⟩} : Set ↥C)).map
      (QuotientGroup.mk' (N.subgroupOf C)) =
        Subgroup.closure ({QuotientGroup.mk' (N.subgroupOf C) ⟨b, hMC hbM⟩,
          QuotientGroup.mk' (N.subgroupOf C) ⟨k, hMC hkM⟩} :
            Set (↥C ⧸ (N.subgroupOf C))) := by
    rw [MonoidHom.map_closure]
    simp
  have hxK : QuotientGroup.mk' (N.subgroupOf C) x ∈
      (Subgroup.closure ({⟨b, hMC hbM⟩, ⟨k, hMC hkM⟩} : Set ↥C)).map
        (QuotientGroup.mk' (N.subgroupOf C)) := by
    rwa [hmapclos]
  have hxsup : x ∈ (N.subgroupOf C) ⊔
      Subgroup.closure ({⟨b, hMC hbM⟩, ⟨k, hMC hkM⟩} : Set ↥C) := by
    have h1 : x ∈ Subgroup.comap (QuotientGroup.mk' (N.subgroupOf C))
        ((Subgroup.closure ({⟨b, hMC hbM⟩, ⟨k, hMC hkM⟩} : Set ↥C)).map
          (QuotientGroup.mk' (N.subgroupOf C))) := Subgroup.mem_comap.mpr hxK
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at h1
  have hxsup' : x ∈ (↑(N.subgroupOf C ⊔
      Subgroup.closure ({⟨b, hMC hbM⟩, ⟨k, hMC hkM⟩} : Set ↥C)) : Set ↥C) := hxsup
  rw [Subgroup.normal_mul, Set.mem_mul] at hxsup'
  obtain ⟨y, hy, z, hz, hxz⟩ := hxsup'
  have hyN : (y : G) ∈ N := Subgroup.mem_subgroupOf.mp hy
  have hzclos : (z : G) ∈ Subgroup.closure ({b, k} : Set G) := by
    have h := Subgroup.mem_map_of_mem C.subtype hz
    simpa [MonoidHom.map_closure] using h
  have hmul : m = (y : G) * (z : G) := by
    have h := congrArg Subtype.val hxz
    simpa [x] using h.symm
  rw [hmul]
  exact Subgroup.mul_mem_sup hyN hzclos

end CFSG.StandardType.FrameRoute.FS81
