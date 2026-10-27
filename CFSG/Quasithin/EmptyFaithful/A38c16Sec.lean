module

public import CFSG.Quasithin.EmptyFaithful.A38c16Defs
public import CFSG.Quasithin.EmptyFaithful.A38c16Nat

public section

namespace CFSG.Quasithin.A38c16

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Abstract

variable {G : Type} [Group G] {W : Type} [CommGroup W]

structure SecData (Hc Uc Zc : Subgroup G) (φ : ↥Uc →* W) (ρ : ↥Hc →* MulAut W) : Prop where
  norm : ∀ x ∈ Hc, ∀ u ∈ Uc, x * u * x⁻¹ ∈ Uc
  Z_le : Zc ≤ Uc
  surj : Function.Surjective φ
  ker : ∀ u : ↥Uc, φ u = 1 ↔ (u : G) ∈ Zc
  act : ∀ (x : ↥Hc) (u : ↥Uc), ρ x (φ u) = φ ⟨(x : G) * u * (x : G)⁻¹, norm x x.2 u u.2⟩

@[expose] def secOf (Uc : Subgroup G) (φ : ↥Uc →* W) (J : Subgroup G) : Subgroup W :=
  (J.subgroupOf Uc).map φ

@[expose] def preOf (Uc : Subgroup G) (φ : ↥Uc →* W) (N : Subgroup W) : Subgroup G :=
  (N.comap φ).map Uc.subtype

variable {Hc Uc Zc : Subgroup G} {φ : ↥Uc →* W} {ρ : ↥Hc →* MulAut W}

theorem mem_secOf {J : Subgroup G} {w : W} :
    w ∈ secOf Uc φ J ↔ ∃ u : ↥Uc, (u : G) ∈ J ∧ φ u = w := by
  simp only [secOf, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_preOf {N : Subgroup W} {u : G} :
    u ∈ preOf Uc φ N ↔ ∃ hu : u ∈ Uc, φ ⟨u, hu⟩ ∈ N := by
  simp only [preOf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, h, rfl⟩

theorem secOf_preOf (hsurj : Function.Surjective φ) (N : Subgroup W) :
    secOf Uc φ (preOf Uc φ N) = N := by
  unfold secOf preOf
  rw [CFSG.Quasithin.map_subtype_subgroupOf', Subgroup.map_comap_eq_self_of_surjective hsurj]

theorem secOf_le_iff {A : Subgroup G} (hA : A ≤ Uc) {N : Subgroup W} :
    secOf Uc φ A ≤ N ↔ A ≤ preOf Uc φ N := by
  constructor
  · intro h u hu
    exact mem_preOf.2 ⟨hA hu, h (mem_secOf.2 ⟨⟨u, hA hu⟩, hu, rfl⟩)⟩
  · intro h w hw
    obtain ⟨u, hu, rfl⟩ := mem_secOf.1 hw
    obtain ⟨hu', h2⟩ := mem_preOf.1 (h hu)
    exact h2

theorem mem_secOf_iff (hd : SecData Hc Uc Zc φ ρ) {J : Subgroup G} (hZJ : Zc ≤ J) {u : ↥Uc} :
    φ u ∈ secOf Uc φ J ↔ (u : G) ∈ J := by
  rw [mem_secOf]
  constructor
  · rintro ⟨u', hu', he⟩
    have h1 : φ (u'⁻¹ * u) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h2 : ((u'⁻¹ * u : ↥Uc) : G) ∈ Zc := (hd.ker _).1 h1
    have : (u : G) = (u' : G) * ((u'⁻¹ * u : ↥Uc) : G) := by simp
    rw [this]
    exact J.mul_mem hu' (hZJ h2)
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem secOf_Z (hd : SecData Hc Uc Zc φ ρ) : secOf Uc φ Zc = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := mem_secOf.1 hw
  rw [Subgroup.mem_bot]
  exact (hd.ker u).2 hu

theorem Z_le_preOf (hd : SecData Hc Uc Zc φ ρ) (N : Subgroup W) : Zc ≤ preOf Uc φ N := by
  intro z hz
  refine mem_preOf.2 ⟨hd.Z_le hz, ?_⟩
  rw [(hd.ker ⟨z, hd.Z_le hz⟩).2 hz]
  exact N.one_mem

theorem isKSub_secOf (hd : SecData Hc Uc Zc φ ρ) {K J : Subgroup G}
    (hKJ : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J) :
    IsKSub ((K.subgroupOf Hc).map ρ) (secOf Uc φ J) := by
  rintro _ ⟨x, hx, rfl⟩ v hv
  obtain ⟨u, huJ, rfl⟩ := mem_secOf.1 hv
  rw [hd.act]
  exact mem_secOf.2 ⟨_, hKJ x (Subgroup.mem_subgroupOf.1 hx) u huJ, rfl⟩

theorem card_secOf (hd : SecData Hc Uc Zc φ ρ) {J : Subgroup G} (hZJ : Zc ≤ J) (hJU : J ≤ Uc) :
    Nat.card (secOf Uc φ J) = Zc.relIndex J := by
  have hker : φ.ker = Zc.subgroupOf Uc := by
    ext u
    rw [MonoidHom.mem_ker, hd.ker, Subgroup.mem_subgroupOf]
  have hZ'J' : Zc.subgroupOf Uc ≤ J.subgroupOf Uc := fun x hx => hZJ hx
  have h1 := Subgroup.relIndex_map_map φ (Zc.subgroupOf Uc) (J.subgroupOf Uc)
  rw [hker, sup_idem, sup_eq_left.2 hZ'J', Subgroup.relIndex_subgroupOf hJU] at h1
  have h2 : (Zc.subgroupOf Uc).map φ = ⊥ := by
    have := secOf_Z hd
    exact this
  rw [h2] at h1
  rw [← h1]
  exact (Subgroup.relIndex_bot_left _).symm

theorem isSimple8_secOf [Finite G] (hd : SecData Hc Uc Zc φ ρ) {K J : Subgroup G}
    (hKH : K ≤ Hc) (hUp : IsPGroup 2 Uc) (hZJ : Zc ≤ J) (hJU : J ≤ Uc) (hm : mIdx J Zc = 3)
    (hirr : IsIrredOnSection K J Zc) :
    IsSimple8 ((K.subgroupOf Hc).map ρ) (secOf Uc φ J) := by
  obtain ⟨hlt, hKJn, hKZn, hmin⟩ := hirr
  have hKJ : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := fun k hk j hj =>
    (Subgroup.mem_normalizer_iff.1 (hKJn hk) j).1 hj
  refine ⟨isKSub_secOf hd hKJ, ?_, ?_⟩
  · rw [card_secOf hd hZJ hJU, HypF98.relIndex_eq_two_pow_mIdx (hUp.to_le hJU), hm]
    norm_num
  · intro N hNJ hNK
    have hZN : Zc ≤ preOf Uc φ N := Z_le_preOf hd N
    have hN'J : preOf Uc φ N ≤ J := by
      intro u hu
      obtain ⟨hu', hφ⟩ := mem_preOf.1 hu
      exact (mem_secOf_iff hd hZJ).1 (hNJ hφ)
    have hKN : K ≤ Subgroup.normalizer (preOf Uc φ N : Set G) := by
      refine le_normalizer_of_forall_conj fun k hk u hu => ?_
      obtain ⟨hu', hφ⟩ := mem_preOf.1 hu
      have hk' : k ∈ Hc := hKH hk
      refine mem_preOf.2 ⟨hd.norm k hk' u hu', ?_⟩
      have := hd.act ⟨k, hk'⟩ ⟨u, hu'⟩
      rw [← this]
      exact hNK _ ⟨⟨k, hk'⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩ _ hφ
    rcases hmin _ hZN hN'J hKN with h | h
    · left
      rw [← secOf_preOf hd.surj N, h, secOf_Z hd]
    · right
      rw [← secOf_preOf hd.surj N, h]

theorem commSub_le_secOf_commutator (hd : SecData Hc Uc Zc φ ρ) {K : Subgroup G} :
    commSub ⊤ ((K.subgroupOf Hc).map ρ) ≤ secOf Uc φ ⁅Uc, K⁆ := by
  unfold commSub
  rw [Subgroup.closure_le]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, w, -, rfl⟩
  obtain ⟨u, rfl⟩ := hd.surj w
  have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.1 hx
  have hxu : (x : G) * u * (x : G)⁻¹ ∈ Uc := hd.norm x x.2 u u.2
  have hmem : (x : G) * u * (x : G)⁻¹ * (u : G)⁻¹ ∈ ⁅Uc, K⁆ := by
    have h1 : ⁅(u : G), (x : G)⁆ ∈ ⁅Uc, K⁆ := Subgroup.commutator_mem_commutator u.2 hxK
    have h2 := (⁅Uc, K⁆).inv_mem h1
    rwa [commutatorElement_inv, commutatorElement_def] at h2
  rw [SetLike.mem_coe, hd.act]
  have hUm : (x : G) * u * (x : G)⁻¹ * (u : G)⁻¹ ∈ Uc := Uc.mul_mem hxu (Uc.inv_mem u.2)
  refine mem_secOf.2 ⟨⟨_, hUm⟩, hmem, ?_⟩
  have e : (⟨(x : G) * u * (x : G)⁻¹ * (u : G)⁻¹, hUm⟩ : ↥Uc) =
      ⟨(x : G) * u * (x : G)⁻¹, hxu⟩ * u⁻¹ := rfl
  rw [e, map_mul, map_inv]

theorem commutator_le_preOf (hd : SecData Hc Uc Zc φ ρ) {K : Subgroup G} (hKH : K ≤ Hc) :
    ⁅Uc, K⁆ ≤ preOf Uc φ (commSub ⊤ ((K.subgroupOf Hc).map ρ)) := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have hk' : k ∈ Hc := hKH hk
  have hku : k * u⁻¹ * k⁻¹ ∈ Uc := hd.norm k hk' u⁻¹ (Uc.inv_mem hu)
  have hcom : ⁅u, k⁆ ∈ Uc := by
    rw [commutatorElement_def]
    have : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [this]
    exact Uc.mul_mem hu hku
  refine mem_preOf.2 ⟨hcom, ?_⟩
  have hgen : ρ ⟨k, hk'⟩ (φ ⟨u, hu⟩) * (φ ⟨u, hu⟩)⁻¹ ∈ commSub ⊤ ((K.subgroupOf Hc).map ρ) :=
    Subgroup.subset_closure ⟨_, ⟨⟨k, hk'⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩, φ ⟨u, hu⟩,
      Subgroup.mem_top _, rfl⟩
  have hinv := (commSub ⊤ ((K.subgroupOf Hc).map ρ)).inv_mem hgen
  have h2 : ρ ⟨k, hk'⟩ (φ (⟨u, hu⟩ : ↥Uc)⁻¹) = φ ⟨k * u⁻¹ * k⁻¹, hku⟩ :=
    hd.act ⟨k, hk'⟩ ⟨u, hu⟩⁻¹
  have e : (⟨⁅u, k⁆, hcom⟩ : ↥Uc) = ⟨u, hu⟩ * ⟨k * u⁻¹ * k⁻¹, hku⟩ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul]
    group
  have h3 : φ ⟨⁅u, k⁆, hcom⟩ = (ρ ⟨k, hk'⟩ (φ ⟨u, hu⟩) * (φ ⟨u, hu⟩)⁻¹)⁻¹ := by
    rw [e, map_mul, ← h2, map_inv, map_inv, mul_inv_rev, inv_inv]
  rw [h3]
  exact hinv

theorem commSub_le_iSup_simple8 [Finite G] (hd : SecData Hc Uc Zc φ ρ) {K : Subgroup G}
    (hKH : K ≤ Hc) (hUp : IsPGroup 2 Uc)
    (hsum : ⁅Uc, K⁆ ⊔ Zc ≤ ⨆ (J : Subgroup G) (_ : Zc ≤ J ∧ J ≤ Uc ∧ mIdx J Zc = 3 ∧
      IsIrredOnSection K J Zc), J) :
    commSub ⊤ ((K.subgroupOf Hc).map ρ) ≤
      ⨆ (M : Subgroup W) (_ : IsSimple8 ((K.subgroupOf Hc).map ρ) M), M := by
  refine (commSub_le_secOf_commutator hd).trans ?_
  have hcU : ⁅Uc, K⁆ ≤ Uc := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have hku : k * u⁻¹ * k⁻¹ ∈ Uc := hd.norm k (hKH hk) u⁻¹ (Uc.inv_mem hu)
    rw [commutatorElement_def]
    have : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [this]
    exact Uc.mul_mem hu hku
  rw [secOf_le_iff hcU]
  refine (le_sup_left.trans hsum).trans ?_
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨hZJ, hJU, hm, hirr⟩ := hJ
  rw [← secOf_le_iff hJU]
  exact le_iSup₂ (f := fun (M : Subgroup W) (_ : IsSimple8 ((K.subgroupOf Hc).map ρ) M) => M)
    (secOf Uc φ J) (isSimple8_secOf hd hKH hUp hZJ hJU hm hirr)

theorem inf_le_of_commSub_inf_eq_bot (hd : SecData Hc Uc Zc φ ρ) {K Kp : Subgroup G}
    (hKH : K ≤ Hc) (hKpH : Kp ≤ Hc)
    (h : commSub ⊤ ((K.subgroupOf Hc).map ρ) ⊓ commSub ⊤ ((Kp.subgroupOf Hc).map ρ) = ⊥) :
    (⁅Uc, K⁆ ⊔ Zc) ⊓ (⁅Uc, Kp⁆ ⊔ Zc) ≤ Zc := by
  intro x hx
  have h1 : x ∈ preOf Uc φ (commSub ⊤ ((K.subgroupOf Hc).map ρ)) :=
    (sup_le (commutator_le_preOf hd hKH) (Z_le_preOf hd _)) hx.1
  have h2 : x ∈ preOf Uc φ (commSub ⊤ ((Kp.subgroupOf Hc).map ρ)) :=
    (sup_le (commutator_le_preOf hd hKpH) (Z_le_preOf hd _)) hx.2
  obtain ⟨hxU, h1'⟩ := mem_preOf.1 h1
  obtain ⟨hxU2, h2'⟩ := mem_preOf.1 h2
  have h3 : φ ⟨x, hxU⟩ ∈ commSub ⊤ ((K.subgroupOf Hc).map ρ) ⊓
      commSub ⊤ ((Kp.subgroupOf Hc).map ρ) := ⟨h1', h2'⟩
  rw [h, Subgroup.mem_bot] at h3
  exact (hd.ker ⟨x, hxU⟩).1 h3

theorem star_norm {K : Subgroup G} (hn : ∀ x ∈ Hc, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (x : ↥Hc) :
    ∀ k ∈ (K.subgroupOf Hc).map ρ, ρ x * k * (ρ x)⁻¹ ∈ (K.subgroupOf Hc).map ρ := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨x * k * x⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp [map_mul, map_inv]⟩
  exact hn x x.2 k (Subgroup.mem_subgroupOf.1 hk)

theorem star_comm {Q K Kp : Subgroup G} (hker : ∀ x : ↥Hc, ρ x = 1 ↔ (x : G) ∈ Q)
    (hcomm : ∀ k ∈ K, ∀ y ∈ Kp, k⁻¹ * y⁻¹ * k * y ∈ Q) :
    ∀ k ∈ (K.subgroupOf Hc).map ρ, ∀ y ∈ (Kp.subgroupOf Hc).map ρ, k * y = y * k := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨y, hy, rfl⟩
  have h1 : ρ (k⁻¹ * y⁻¹ * k * y) = 1 :=
    (hker _).2 (hcomm k (Subgroup.mem_subgroupOf.1 hk) y (Subgroup.mem_subgroupOf.1 hy))
  simp only [map_mul, map_inv] at h1
  calc ρ k * ρ y = (ρ y * ρ k) * ((ρ k)⁻¹ * (ρ y)⁻¹ * ρ k * ρ y) := by group
    _ = ρ y * ρ k := by rw [h1, mul_one]

end Abstract

end CFSG.Quasithin.A38c16
