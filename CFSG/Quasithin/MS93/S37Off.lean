module

public import CFSG.Quasithin.MS93.S37Gal
public import CFSG.Quasithin.MS93.S36Frat
public import CFSG.Quasithin.MS93.S37T1

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section TImage

variable {T : Subgroup G}

omit [Finite G] in
theorem mem_tImage {θ : MulAut ↥T} {K : Subgroup G} {x : G} :
    x ∈ tImage θ K ↔ ∃ (y : G) (hy : y ∈ T), y ∈ K ∧ ((θ ⟨y, hy⟩ : ↥T) : G) = x := by
  constructor
  · rintro ⟨_, ⟨⟨y, hyT⟩, hyK, rfl⟩, rfl⟩
    exact ⟨y, hyT, hyK, rfl⟩
  · rintro ⟨y, hyT, hyK, rfl⟩
    exact ⟨θ ⟨y, hyT⟩, ⟨⟨y, hyT⟩, hyK, rfl⟩, rfl⟩

omit [Finite G] in
theorem tImage_inf_centralizer (θ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage θ (T ⊓ Subgroup.centralizer (K : Set G)) =
      T ⊓ Subgroup.centralizer (tImage θ K : Set G) := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hyT, ⟨-, hyC⟩, rfl⟩ := mem_tImage.1 hx
    refine ⟨(θ ⟨y, hyT⟩).2, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨w, hwT, hwK, rfl⟩ := mem_tImage.1 hz
    have hc := Subgroup.mem_centralizer_iff.1 hyC w hwK
    have e : (⟨w, hwT⟩ : ↥T) * ⟨y, hyT⟩ = ⟨y, hyT⟩ * ⟨w, hwT⟩ := Subtype.ext hc
    have := congrArg (fun t => ((θ t : ↥T) : G)) e
    simpa only [map_mul, Subgroup.coe_mul] using this
  · rintro ⟨hxT, hxC⟩
    refine mem_tImage.2 ⟨((θ⁻¹ ⟨x, hxT⟩ : ↥T) : G), (θ⁻¹ ⟨x, hxT⟩).2, ⟨(θ⁻¹ ⟨x, hxT⟩).2,
      Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩, ?_⟩
    · have hwT := hK hw
      have hθw : ((θ ⟨w, hwT⟩ : ↥T) : G) ∈ tImage θ K := mem_tImage.2 ⟨w, hwT, hw, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.1 hxC _ hθw
      have e : θ ⟨w, hwT⟩ * ⟨x, hxT⟩ = ⟨x, hxT⟩ * θ ⟨w, hwT⟩ := Subtype.ext hc
      have := congrArg (fun t => ((θ⁻¹ t : ↥T) : G)) e
      simp only [map_mul, Subgroup.coe_mul] at this
      have h1 : θ⁻¹ (θ ⟨w, hwT⟩) = ⟨w, hwT⟩ := by simp
      rw [h1] at this
      exact this
    · show ((θ (θ⁻¹ ⟨x, hxT⟩) : ↥T) : G) = x
      simp

omit [Finite G] in
theorem tImage_mono' (θ : MulAut ↥T) {K K' : Subgroup G} (h : K ≤ K') :
    tImage θ K ≤ tImage θ K' :=
  Subgroup.map_mono (Subgroup.map_mono fun _ hx => h hx)

omit [Finite G] in
theorem tImage_inv_tImage' (θ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage θ⁻¹ (tImage θ K) = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hyT, hy, rfl⟩ := mem_tImage.1 hx
    obtain ⟨z, hzT, hz, hzy⟩ := mem_tImage.1 hy
    have : (⟨y, hyT⟩ : ↥T) = θ ⟨z, hzT⟩ := Subtype.ext hzy.symm
    rw [this]
    simpa using hz
  · intro hx
    refine mem_tImage.2 ⟨((θ ⟨x, hK hx⟩ : ↥T) : G), (θ ⟨x, hK hx⟩).2,
      mem_tImage.2 ⟨x, hK hx, hx, rfl⟩, ?_⟩
    simp

omit [Finite G] in
theorem tImage_tImage_inv' (θ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage θ (tImage θ⁻¹ K) = K := by
  have := tImage_inv_tImage' θ⁻¹ hK
  rwa [inv_inv] at this

omit [Finite G] in
theorem tImage_inf' (θ : MulAut ↥T) (K K' : Subgroup G) :
    tImage θ (K ⊓ K') = tImage θ K ⊓ tImage θ K' := by
  ext x
  simp only [Subgroup.mem_inf, mem_tImage]
  constructor
  · rintro ⟨y, hyT, ⟨hyK, hyK'⟩, rfl⟩
    exact ⟨⟨y, hyT, hyK, rfl⟩, ⟨y, hyT, hyK', rfl⟩⟩
  · rintro ⟨⟨y, hyT, hyK, rfl⟩, ⟨z, hzT, hzK', hz⟩⟩
    have hyz : (⟨z, hzT⟩ : ↥T) = ⟨y, hyT⟩ := θ.injective (Subtype.ext hz)
    have : z = y := congrArg Subtype.val hyz
    subst this
    exact ⟨z, hyT, ⟨hyK, hzK'⟩, rfl⟩

omit [Finite G] in
theorem card_tImage (θ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    Nat.card (tImage θ K) = Nat.card K := by
  rw [tImage, Subgroup.card_map_of_injective T.subtype_injective,
    Subgroup.card_map_of_injective θ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem relIndex_tImage (θ : MulAut ↥T) {K K' : Subgroup G} (hK : K ≤ T) (hK' : K' ≤ T) :
    (tImage θ K).relIndex (tImage θ K') = K.relIndex K' := by
  have h1 := Subgroup.relIndex_mul_card (tImage θ K) (tImage θ K')
  have h2 := Subgroup.relIndex_mul_card K K'
  rw [← tImage_inf', card_tImage θ hK', card_tImage θ (inf_le_left.trans hK)] at h1
  have hpos : 0 < Nat.card ↥(K ⊓ K') := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

omit [Finite G] in
theorem tImage_of_characteristic (θ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T)
    (hc : (K.subgroupOf T).Characteristic) : tImage θ K = K := by
  rw [tImage, Subgroup.characteristic_iff_map_eq.mp hc θ, Subgroup.map_subgroupOf_eq_of_le hK]

end TImage

abbrev Ut (M T L : Subgroup G) {S : Subgroup G} (θ : MulAut ↥S) : Subgroup G :=
  tImage θ (Uq M T L)

abbrev Qt (M : Subgroup G) {S : Subgroup G} (θ : MulAut ↥S) : Subgroup G := tImage θ (pCoreOf 2 M)

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem co_comm {x : G} (hx : x ∈ M) {u : G} (hu : u ∈ Uq M T L) (hc : ⁅x, u⁆ ∈ Uq M T L) :
    C.N.co ⟨⁅x, u⁆, hc⟩ = C.act hx (C.N.co ⟨u, hu⟩) - C.N.co ⟨u, hu⟩ := by
  have hxu : x * u * x⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (C.hMU hx) u).1 hu
  have e : (⟨⁅x, u⁆, hc⟩ : ↥(Uq M T L)) = ⟨x * u * x⁻¹, hxu⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ :=
    Subtype.ext (commutatorElement_def x u)
  rw [e, C.N.co_mul, C.N.co_inv, C.N.act_co C.hMU C.hMA hx (u := ⟨u, hu⟩)
    (v := ⟨x * u * x⁻¹, hxu⟩) rfl]
  abel

section Sub

variable {S : Subgroup G}

theorem Uq_le_S (hQS : pCoreOf 2 M ≤ S) : Uq M T L ≤ S :=
  (C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)).trans hQS

theorem inf_centralizer_Uq (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) :
    S ⊓ Subgroup.centralizer (Uq M T L : Set G) = pCoreOf 2 M := by
  refine le_antisymm ?_ (le_inf hQS ?_)
  · rintro t ⟨htS, htC⟩
    refine C.h.mem_pCoreOf_of_comm_Uq (hST htS) fun u hu => ?_
    have : ⁅u, t⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 htC u hu
    rw [this]
    exact one_mem _
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (comm_of_mem_Uq C.h hu hx).symm

theorem Qt_eq (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S) :
    Qt M θ = S ⊓ Subgroup.centralizer (Ut M T L θ : Set G) := by
  rw [Qt, ← C.inf_centralizer_Uq hQS hST, tImage_inf_centralizer θ (C.Uq_le_S hQS)]

theorem le_Qt_iff (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S) :
    Uq M T L ≤ Qt M θ ↔ Ut M T L θ ≤ pCoreOf 2 M := by
  rw [C.Qt_eq hQS hST, ← C.inf_centralizer_Uq hQS hST]
  constructor
  · intro hle u' hu'
    refine ⟨tImage_le θ _ hu', Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (hle hu).2 u' hu').symm
  · intro hle u hu
    refine ⟨C.Uq_le_S hQS hu, Subgroup.mem_centralizer_iff.2 fun u' hu' => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (hle hu').2 u hu).symm

theorem Ut_le_M (hST : S ≤ T) (θ : MulAut ↥S) : Ut M T L θ ≤ M :=
  (tImage_le θ _).trans (hST.trans C.h.le)

theorem conj_mem_Ut (hST : S ≤ T) (θ : MulAut ↥S) {t x : G} (ht : t ∈ S)
    (hx : x ∈ Ut M T L θ) : t * x * t⁻¹ ∈ Ut M T L θ := by
  obtain ⟨y, hyS, hyU, rfl⟩ := mem_tImage.1 hx
  have hs : ((θ.symm ⟨t, ht⟩ : ↥S) : G) * y * ((θ.symm ⟨t, ht⟩ : ↥S) : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (C.hMU (C.h.le (hST (θ.symm ⟨t, ht⟩).2))) y).1 hyU
  refine mem_tImage.2 ⟨_, S.mul_mem (S.mul_mem (θ.symm ⟨t, ht⟩).2 hyS)
    (S.inv_mem (θ.symm ⟨t, ht⟩).2), hs, ?_⟩
  have e : (⟨((θ.symm ⟨t, ht⟩ : ↥S) : G) * y * ((θ.symm ⟨t, ht⟩ : ↥S) : G)⁻¹, S.mul_mem
      (S.mul_mem (θ.symm ⟨t, ht⟩).2 hyS) (S.inv_mem (θ.symm ⟨t, ht⟩).2)⟩ : ↥S) =
      θ.symm ⟨t, ht⟩ * ⟨y, hyS⟩ * (θ.symm ⟨t, ht⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem Ut_comm (θ : MulAut ↥S) {x y : G} (hx : x ∈ Ut M T L θ) (hy : y ∈ Ut M T L θ) :
    x * y = y * x := by
  obtain ⟨a, haS, haU, rfl⟩ := mem_tImage.1 hx
  obtain ⟨b, hbS, hbU, rfl⟩ := mem_tImage.1 hy
  have e : (⟨a, haS⟩ : ↥S) * ⟨b, hbS⟩ = ⟨b, hbS⟩ * ⟨a, haS⟩ :=
    Subtype.ext (Sp4L.uq_comm C.h haU hbU)
  have := congrArg (fun t => ((θ t : ↥S) : G)) e
  simpa only [map_mul, Subgroup.coe_mul] using this

theorem Ut_sq (θ : MulAut ↥S) {x : G} (hx : x ∈ Ut M T L θ) : x ^ 2 = 1 := by
  obtain ⟨a, haS, haU, rfl⟩ := mem_tImage.1 hx
  have e : (⟨a, haS⟩ : ↥S) ^ 2 = 1 := Subtype.ext (by simpa using Sp4L.uq_sq C.h haU)
  have := congrArg (fun t => ((θ t : ↥S) : G)) e
  simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one] using this

theorem comm_mem_inf (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S) {x u : G}
    (hx : x ∈ Ut M T L θ) (hu : u ∈ Uq M T L) : ⁅x, u⁆ ∈ Uq M T L ⊓ Ut M T L θ := by
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact (Uq M T L).mul_mem
      ((Subgroup.mem_normalizer_iff.1 (C.hMU (C.Ut_le_M hST θ hx)) u).1 hu)
      ((Uq M T L).inv_mem hu)
  · have e : ⁅x, u⁆ = x * (u * x⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Ut M T L θ).mul_mem hx
      (C.conj_mem_Ut hST θ (C.Uq_le_S hQS hu) ((Ut M T L θ).inv_mem hx))

theorem act_quad (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S) {x y : G}
    (hx : x ∈ Ut M T L θ) (hy : y ∈ Ut M T L θ) (v : V4 F) :
    C.act (C.Ut_le_M hST θ hy) (C.act (C.Ut_le_M hST θ hx) v - v) =
      C.act (C.Ut_le_M hST θ hx) v - v := by
  obtain ⟨u, rfl⟩ := C.N.co_surj v
  have hw := C.comm_mem_inf hQS hST θ hx u.2
  rw [← C.co_comm (C.Ut_le_M hST θ hx) u.2 hw.1]
  refine C.N.act_co C.hMU C.hMA _ ?_
  show ⁅x, (u : G)⁆ = y * ⁅x, (u : G)⁆ * y⁻¹
  rw [C.Ut_comm θ hy hw.2, mul_inv_cancel_right]

theorem act_eq_of_linear (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S) {x y : G}
    (hx : x ∈ Ut M T L θ) (hy : y ∈ Ut M T L θ)
    (hxnl : C.sig (C.Ut_le_M hST θ hx) ≠ RingHom.id F)
    (hylin : ∀ (c : F) (v : V4 F),
      C.act (C.Ut_le_M hST θ hy) (c • v) = c • C.act (C.Ut_le_M hST θ hy) v) (v : V4 F) :
    C.act (C.Ut_le_M hST θ hy) v = v := by
  obtain ⟨c, hc⟩ : ∃ c : F, C.sig (C.Ut_le_M hST θ hx) c ≠ c := by
    by_contra hall
    push Not at hall
    exact hxnl (RingHom.ext hall)
  set w := C.act (C.Ut_le_M hST θ hy) v - v with hw
  have h1 : C.act (C.Ut_le_M hST θ hx) (c • w) = c • w := by
    have := C.act_quad hQS hST θ hy hx (c • v)
    rw [hylin, ← smul_sub] at this
    exact this
  have h2 : C.act (C.Ut_le_M hST θ hx) w = w := C.act_quad hQS hST θ hy hx v
  rw [C.sig_spec, h2] at h1
  have h3 : (C.sig (C.Ut_le_M hST θ hx) c - c) • w = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) hc
  · exact sub_eq_zero.1 h

end Sub

theorem omegaOneCenterOf_le_Qt (θ : MulAut ↥T) : omegaOneCenterOf T ≤ Qt M θ := by
  rw [← tImage_of_characteristic θ (PU.omegaOneCenterOf_le T)
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T)]
  exact tImage_mono' θ ((omegaOneCenterOf_le_Z0q M T C.h.le).trans C.h.Z0q_le_pCoreOf)

theorem Z0q_le_Qt_iff (θ : MulAut ↥T) : Z0q M T ≤ Qt M θ ↔ Uq M T L ≤ Qt M θ := by
  rw [C.h.Z0q_eq_sup]
  exact ⟨fun h => le_sup_right.trans h, fun h => sup_le (C.omegaOneCenterOf_le_Qt θ) h⟩

theorem mem_pCore_of_act_eq {t : G} (ht : t ∈ T) (h1 : ∀ v, C.act (C.h.le ht) v = v) :
    t ∈ pCoreOf 2 M := by
  refine C.h.mem_pCoreOf_of_comm_Uq ht fun u hu => ?_
  have hu' : u⁻¹ ∈ Uq M T L := inv_mem hu
  have htu : t * u⁻¹ * t⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (C.hMU (C.h.le ht)) _).1 hu'
  have hco := C.N.act_co C.hMU C.hMA (C.h.le ht) (u := ⟨u⁻¹, hu'⟩) (v := ⟨_, htu⟩) rfl
  rw [h1] at hco
  have hA := (C.N.co_eq_co_iff _ _).1 hco
  have e : ⁅u, t⁆ = (u⁻¹)⁻¹ * (t * u⁻¹ * t⁻¹) := by
    rw [commutatorElement_def, inv_inv]
    group
  rw [e]
  exact hA.2

theorem card_Uq : Nat.card ↥(Uq M T L) =
    Nat.card (V4 F) * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
  have h := Subgroup.card_ker_mul_card_of_surjective C.N.β_surj
  have hker : C.N.β.ker = (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    ext u
    rw [MonoidHom.mem_ker, C.N.β_ker, Subgroup.mem_subgroupOf]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  rw [← h, mul_comm]
  rfl

theorem card_mul_card_le {x : G} (hx : x ∈ M) :
    Nat.card (V4 F) * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      Nat.card ↥(Uq M T L) * Nat.card ↥(KGNat.fixAdd (C.act hx)) := by
  set A := Uq M T L ⊓ Subgroup.centralizer (L : Set G) with hA
  set W : Subgroup ↥(Uq M T L) :=
    (Uq M T L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (Uq M T L) with hW
  let f : ↥W →* Multiplicative (V4 F) := C.N.β.comp W.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hWc : Nat.card ↥W = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hker : Nat.card f.ker ≤ Nat.card ↥A := by
    refine Nat.card_le_card_of_injective (fun w => (⟨((w : ↥W) : ↥(Uq M T L)), ?_⟩ : ↥A)) ?_
    · have := (C.N.β_ker _).1 (w.2 : f (w : ↥W) = 1)
      exact ⟨((w : ↥W) : ↥(Uq M T L)).2, this.2⟩
    · intro w w' h
      ext
      simpa using congrArg Subtype.val h
  have hrange : Nat.card f.range ≤ Nat.card ↥(KGNat.fixAdd (C.act hx)) := by
    refine Nat.card_le_card_of_injective (fun r => (⟨Multiplicative.toAdd (r : _), ?_⟩ :
      ↥(KGNat.fixAdd (C.act hx)))) ?_
    · obtain ⟨w, hw⟩ := r.2
      rw [← hw]
      show C.act hx (C.N.co ((w : ↥W) : ↥(Uq M T L))) = C.N.co ((w : ↥W) : ↥(Uq M T L))
      refine C.N.act_co C.hMU C.hMA hx ?_
      have hc := (Subgroup.mem_subgroupOf.1 w.2).2
      have := Subgroup.mem_centralizer_iff.1 hc x rfl
      rw [this, mul_inv_cancel_right]
    · intro r r' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Multiplicative.toAdd.injective h')
  rw [← hWc, ← h1, C.card_Uq]
  calc Nat.card (V4 F) * (Nat.card f.ker * Nat.card f.range)
      ≤ Nat.card (V4 F) * (Nat.card ↥A * Nat.card ↥(KGNat.fixAdd (C.act hx))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hker hrange)
    _ = Nat.card (V4 F) * Nat.card ↥A * Nat.card ↥(KGNat.fixAdd (C.act hx)) := by ring

theorem card_V4 : Nat.card (V4 F) = (2 ^ C.k) ^ 4 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := F), C.hF]
  simp

theorem card_V4_le_relIndex_mul {x : G} (hx : x ∈ M) :
    Nat.card (V4 F) ≤ (Subgroup.centralizer ({x} : Set G)).relIndex (Uq M T L) *
      Nat.card ↥(KGNat.fixAdd (C.act hx)) := by
  have h1 := C.card_mul_card_le hx
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({x} : Set G)) (Uq M T L)
  rw [inf_comm] at h2
  have hpos : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({x} : Set G)) := Nat.card_pos
  rw [← h2] at h1
  have : Nat.card (V4 F) * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      ((Subgroup.centralizer ({x} : Set G)).relIndex (Uq M T L) *
        Nat.card ↥(KGNat.fixAdd (C.act hx))) *
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({x} : Set G)) := by
    calc _ ≤ _ := h1
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

theorem sq_le_relIndex_of_nonlinear {x : G} (hx : x ∈ M) (hnl : C.sig hx ≠ RingHom.id F) :
    (2 ^ C.k) ^ 2 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex (Uq M T L) := by
  have h1 := C.card_V4_le_relIndex_mul hx
  have hne : ∃ c : F, C.sig hx c ≠ c := by
    by_contra hall
    push Not at hall
    exact hnl (RingHom.ext hall)
  have h2 := card_fixAdd_sq_le (C.sig_spec hx) hne
  rw [C.card_V4] at h1 h2
  set q := 2 ^ C.k with hq
  set R := (Subgroup.centralizer ({x} : Set G)).relIndex (Uq M T L)
  set f := Nat.card ↥(KGNat.fixAdd (C.act hx))
  have hf : f ≤ q ^ 2 := by
    by_contra hlt
    push Not at hlt
    have h3 : (q ^ 2) ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
    have e : (q ^ 2) ^ 2 = q ^ 4 := by ring
    rw [e] at h3
    omega
  by_contra hR
  push Not at hR
  have hq0 : 0 < q ^ 2 := by positivity
  have h4 : R * f < q ^ 4 := by
    calc R * f ≤ R * q ^ 2 := Nat.mul_le_mul_left _ hf
      _ < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_right hR hq0
      _ = q ^ 4 := by ring
  omega

theorem le_relIndex_of_linear {x : G} (hx : x ∈ M)
    (hlin : ∀ (c : F) (v : V4 F), C.act hx (c • v) = c • C.act hx v)
    (hne : ∃ v : V4 F, C.act hx v ≠ v) :
    2 ^ C.k ≤ (Subgroup.centralizer ({x} : Set G)).relIndex (Uq M T L) := by
  have h1 := C.card_V4_le_relIndex_mul hx
  rw [C.card_V4] at h1
  let W : Submodule F (V4 F) :=
    { carrier := {v | C.act hx v = v}
      add_mem' := fun {a b} ha hb => by
        show C.act hx (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := map_zero _
      smul_mem' := fun c v hv => by
        show C.act hx (c • v) = c • v
        rw [hlin, hv] }
  have hW : Nat.card ↥(KGNat.fixAdd (C.act hx)) = Nat.card ↥W := rfl
  have hWtop : W ≠ ⊤ := by
    obtain ⟨v, hv⟩ := hne
    intro h
    exact hv (show v ∈ W by rw [h]; trivial)
  have hrank : Module.finrank F ↥W < 4 := by
    have := Submodule.finrank_lt hWtop
    simpa using this
  have hcardW : Nat.card ↥W ≤ (2 ^ C.k) ^ 3 := by
    have : Fintype ↥W := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := ↥W), C.hF]
    exact Nat.pow_le_pow_right (by positivity) (by omega)
  rw [hW] at h1
  set q := 2 ^ C.k
  set R := (Subgroup.centralizer ({x} : Set G)).relIndex (Uq M T L)
  by_contra hR
  push Not at hR
  have hq0 : 0 < q ^ 3 := by positivity
  have h4 : R * Nat.card ↥W < q ^ 4 := by
    calc R * Nat.card ↥W ≤ R * q ^ 3 := Nat.mul_le_mul_left _ hcardW
      _ < q * q ^ 3 := Nat.mul_lt_mul_of_pos_right hR hq0
      _ = q ^ 4 := by ring
  omega

theorem sig_congr {x y : G} (h : x = y) (hx : x ∈ M) (hy : y ∈ M) : C.sig hx = C.sig hy := by
  subst h
  rfl

section Lin

variable {S : Subgroup G}

omit [Field F] [Fintype F] C in
theorem relIndex_pos' (H K : Subgroup G) : 0 < H.relIndex K := by
  have h := Subgroup.relIndex_mul_card H K
  by_contra h0
  push Not at h0
  rw [Nat.le_zero.1 h0, zero_mul] at h
  exact (Nat.card_pos (α := ↥K)).ne' h.symm

theorem relIndex_centralizer_le (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S) {x : G}
    (hx : x ∈ Ut M T L θ) :
    (Subgroup.centralizer ({x} : Set G)).relIndex (Uq M T L) ≤ (Qt M θ).relIndex (Uq M T L) := by
  have hle : Qt M θ ⊓ Uq M T L ≤ Subgroup.centralizer ({x} : Set G) ⊓ Uq M T L := by
    rw [C.Qt_eq hQS hST]
    rintro y ⟨⟨-, hyC⟩, hyU⟩
    refine ⟨Subgroup.mem_centralizer_iff.2 fun z hz => ?_, hyU⟩
    rw [Set.mem_singleton_iff.1 hz]
    exact Subgroup.mem_centralizer_iff.1 hyC x hx
  rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer ({x} : Set G)) (Uq M T L),
    ← Subgroup.inf_relIndex_right (Qt M θ) (Uq M T L)]
  exact Nat.le_of_dvd (relIndex_pos' _ _) (Subgroup.relIndex_dvd_of_le_left _ hle)

theorem relIndex_Qt_eq (hQS : pCoreOf 2 M ≤ S) (θ : MulAut ↥S) :
    (Qt M θ).relIndex (Uq M T L) = (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) := by
  rw [← relIndex_tImage θ⁻¹ (tImage_le θ _) (C.Uq_le_S hQS), tImage_inv_tImage' θ hQS]

theorem sig_of_mem_pCore {x : G} (hx : x ∈ pCoreOf 2 M) :
    C.sig (pCoreOf_le' M hx) = RingHom.id F :=
  (C.linear_iff _).1 fun c v => by rw [C.act_of_mem_pCore hx, C.act_of_mem_pCore hx]

theorem relIndex_le_of_nonlinear (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S)
    {x₀ : G} (hx₀ : x₀ ∈ Ut M T L θ) (hnl : C.sig (C.Ut_le_M hST θ hx₀) ≠ RingHom.id F) :
    (pCoreOf 2 M).relIndex (Ut M T L θ) ≤ C.k := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  refine le_trans ?_ (card_ringHom_le C.hF)
  set H := Ut M T L θ
  let f : ↥H → (F →+* F) := fun y => C.sig (C.Ut_le_M hST θ y.2)
  have hfQ : ∀ y y' : ↥H, (y⁻¹ * y' : ↥H) ∈ (pCoreOf 2 M).subgroupOf H → f y = f y' := by
    intro y y' h
    have hyM := C.Ut_le_M hST θ y.2
    have hy'M := C.Ut_le_M hST θ y'.2
    have hq : ((y⁻¹ * y' : ↥H) : G) ∈ pCoreOf 2 M := Subgroup.mem_subgroupOf.1 h
    have e2 : (y' : G) = (y : G) * ((y⁻¹ * y' : ↥H) : G) := by simp
    show C.sig hyM = C.sig hy'M
    rw [C.sig_congr e2 hy'M (M.mul_mem hyM (pCoreOf_le' M hq)),
      C.sig_mul hyM (pCoreOf_le' M hq), C.sig_of_mem_pCore hq, RingHom.comp_id]
  have hinj : ∀ y y' : ↥H, f y = f y' → (y⁻¹ * y' : ↥H) ∈ (pCoreOf 2 M).subgroupOf H := by
    intro y y' h
    have hyM := C.Ut_le_M hST θ y.2
    have hy'M := C.Ut_le_M hST θ y'.2
    have hyy : (y : G) * y' ∈ H := H.mul_mem y.2 y'.2
    have hy2 : (y : G) * y = 1 := by rw [← pow_two]; exact C.Ut_sq θ y.2
    have hsig : C.sig (C.Ut_le_M hST θ hyy) = RingHom.id F := by
      rw [C.sig_congr rfl _ (M.mul_mem hyM hy'M), C.sig_mul hyM hy'M]
      have h' : C.sig hy'M = C.sig hyM := h.symm
      rw [h', ← C.sig_mul hyM hyM, C.sig_congr hy2 _ M.one_mem]
      exact (C.linear_iff _).1 fun c v => by
        rw [show C.act M.one_mem = C.N.act C.hMU C.hMA M.one_mem from rfl, C.N.act_one]
        rfl
    have hact := C.act_eq_of_linear hQS hST θ hx₀ hyy hnl ((C.linear_iff _).2 hsig)
    have hQ : (y : G) * y' ∈ pCoreOf 2 M := C.mem_pCore_of_act_eq (hST (tImage_le θ _ hyy)) hact
    rw [Subgroup.mem_subgroupOf]
    have : (y : G)⁻¹ = y := by rw [inv_eq_iff_mul_eq_one]; exact hy2
    simpa [this] using hQ
  let g : ↥H ⧸ (pCoreOf 2 M).subgroupOf H → (F →+* F) :=
    Quotient.lift f fun a b hab => hfQ a b (QuotientGroup.leftRel_apply.1 hab)
  have hg : Function.Injective g := by
    intro qa qb hab
    induction qa using QuotientGroup.induction_on
    induction qb using QuotientGroup.induction_on
    exact QuotientGroup.eq.2 (hinj _ _ hab)
  have : Finite (F →+* F) := Finite.of_injective (fun σ : F →+* F => (σ : F → F))
    DFunLike.coe_injective
  exact Nat.card_le_card_of_injective g hg

theorem act_linear_of_mem_T1 {x : G} (hx : x ∈ T1 M T L) (hxM : x ∈ M) (c : F) (v : V4 F) :
    C.act hxM (c • v) = c • C.act hxM v := by
  rw [show C.act hxM = C.act (C.sup_le_M (T1_le_sup hx)) from rfl,
    C.rho_spec ⟨x, T1_le_sup hx⟩, C.rho_spec ⟨x, T1_le_sup hx⟩, Matrix.mulVec_smul]

theorem sig_ne_of_not_mem_T1 {x : G} (hxT : x ∈ T) (hx : x ∉ T1 M T L) (hxM : x ∈ M) :
    C.sig hxM ≠ RingHom.id F := fun h =>
  hx ⟨hxT, C.mem_sup_of_linear hxT ((C.linear_iff hxM).2 h)⟩

theorem Ut_le_T1 (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S)
    (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hle : (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) ≤ (pCoreOf 2 M).relIndex (Ut M T L θ)) :
    Ut M T L θ ≤ T1 M T L ∧ Ut M T L θ⁻¹ ≤ T1 M T L := by
  have hk := C.k.lt_two_pow_self
  have hq2 : 2 ^ C.k ≤ (2 ^ C.k) ^ 2 := Nat.le_self_pow two_ne_zero _
  have h1 : Ut M T L θ ≤ T1 M T L := by
    intro x hx
    by_contra hxT1
    have hnl := C.sig_ne_of_not_mem_T1 (hST (tImage_le θ _ hx)) hxT1 (C.Ut_le_M hST θ hx)
    have h2 := C.relIndex_le_of_nonlinear hQS hST θ hx hnl
    have h3 := C.sq_le_relIndex_of_nonlinear (C.Ut_le_M hST θ hx) hnl
    have h4 := C.relIndex_centralizer_le hQS hST θ hx
    rw [C.relIndex_Qt_eq hQS θ] at h4
    omega
  refine ⟨h1, fun y hy => ?_⟩
  by_contra hyT1
  have hnl := C.sig_ne_of_not_mem_T1 (hST (tImage_le θ⁻¹ _ hy)) hyT1 (C.Ut_le_M hST θ⁻¹ hy)
  have h2 := C.relIndex_le_of_nonlinear hQS hST θ⁻¹ hy hnl
  have hnot : ¬ Ut M T L θ ≤ pCoreOf 2 M := fun h => hcrit ((C.le_Qt_iff hQS hST θ).2 h)
  obtain ⟨x, hx, hxQ⟩ := Set.not_subset.1 hnot
  have hlin := C.act_linear_of_mem_T1 (h1 hx) (C.Ut_le_M hST θ hx)
  have hne : ∃ v, C.act (C.Ut_le_M hST θ hx) v ≠ v := by
    by_contra hall
    push Not at hall
    exact hxQ (C.mem_pCore_of_act_eq (hST (tImage_le θ _ hx)) hall)
  have h3 := C.le_relIndex_of_linear (C.Ut_le_M hST θ hx) hlin hne
  have h4 := C.relIndex_centralizer_le hQS hST θ hx
  rw [C.relIndex_Qt_eq hQS θ] at h4
  omega

end Lin

end Cfg

end CFSG.Quasithin.MS93.S37
