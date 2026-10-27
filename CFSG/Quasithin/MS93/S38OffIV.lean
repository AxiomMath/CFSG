module

public import CFSG.Quasithin.MS93.S38PU
public import CFSG.Quasithin.MS93.S38GL32
public import CFSG.Quasithin.MS93.ML3Sec
public import CFSG.Quasithin.MS93.SkTypes

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace OffIV

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.QuasithinUnique.Setup.Family GL32F

variable {G : Type} [Group G]

section Rho

variable {M : Subgroup G} (α : ↥M →* ↥(StatedSL 3 (ZMod 2)))

@[expose] def rhoHom : ↥M →* GL32 := (StatedSL 3 (ZMod 2)).subtype.comp α

open Classical in
@[expose] noncomputable def rhoG (t : G) : GL32 :=
  if ht : t ∈ M then rhoHom α ⟨t, ht⟩ else 1

variable {α}

theorem rhoG_of_mem {t : G} (ht : t ∈ M) : rhoG α t = rhoHom α ⟨t, ht⟩ := dite_eq_left ht

theorem rhoG_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    rhoG α (x * y) = rhoG α x * rhoG α y := by
  rw [rhoG_of_mem (M.mul_mem hx hy), rhoG_of_mem hx, rhoG_of_mem hy, ← map_mul]
  rfl

theorem rhoG_inv {x : G} (hx : x ∈ M) : rhoG α x⁻¹ = (rhoG α x)⁻¹ := by
  rw [rhoG_of_mem (M.inv_mem hx), rhoG_of_mem hx, ← map_inv]
  rfl

theorem rhoG_pow {x : G} (hx : x ∈ M) (n : ℕ) : rhoG α (x ^ n) = rhoG α x ^ n := by
  rw [rhoG_of_mem (M.pow_mem hx n), rhoG_of_mem hx, ← map_pow]
  rfl

theorem rhoG_one : rhoG α 1 = 1 := by
  rw [rhoG_of_mem M.one_mem, ← map_one (rhoHom α)]
  rfl

theorem rhoG_sq_eq_one {F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 2 F) {x : G}
    (hx : x ∈ F) : rhoG α x ^ 2 = 1 := by
  rw [← rhoG_pow (hFM hx), hF.2 x hx, rhoG_one]

theorem rhoG_comm {F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 2 F) {x y : G}
    (hx : x ∈ F) (hy : y ∈ F) : rhoG α x * rhoG α y = rhoG α y * rhoG α x := by
  rw [← rhoG_mul (hFM hx) (hFM hy), ← rhoG_mul (hFM hy) (hFM hx),
    show x * y = y * x from congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)]

theorem isPGroup_map_rhoHom {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T) :
    IsPGroup 2 ((T.subgroupOf M).map (rhoHom α)) :=
  (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).map (rhoHom α)

theorem rhoG_mem_map {T : Subgroup G} (hTM : T ≤ M) {t : G} (ht : t ∈ T) :
    rhoG α t ∈ (T.subgroupOf M).map (rhoHom α) :=
  ⟨⟨t, hTM ht⟩, ht, (rhoG_of_mem (hTM ht)).symm⟩

theorem exists_of_mem_map {T : Subgroup G} {b : GL32}
    (hb : b ∈ (T.subgroupOf M).map (rhoHom α)) : ∃ t ∈ T, rhoG α t = b := by
  obtain ⟨⟨t, htM⟩, ht, rfl⟩ := hb
  exact ⟨t, ht, rhoG_of_mem htM⟩

end Rho

section Coord

variable {M V K : Subgroup G} {α : ↥M →* ↥(StatedSL 3 (ZMod 2))} (N : NatSec M V K α false)

theorem coord_conj_rhoG {m : G} (hm : m ∈ M) {v : G} (hv : v ∈ V) :
    N.coord (m * v * m⁻¹) = ((rhoG α m : GL32) : Mat3) *ᵥ N.coord v := by
  have := N.coord_conj ⟨m, hm⟩ hv
  rw [natAct_false, coe_toSL3] at this
  rw [rhoG_of_mem hm]
  exact this

theorem coord_commutator {m : G} (hm : m ∈ M) {u : G} (hu : u ∈ V) :
    N.coord ⁅u, m⁆ = (((rhoG α m : GL32) : Mat3) - 1) *ᵥ N.coord u := by
  have hu' : m * u⁻¹ * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (N.norm hm) _).mp (V.inv_mem hu)
  have e : ⁅u, m⁆ = u * (m * u⁻¹ * m⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, N.coord_mul hu hu', coord_conj_rhoG N hm (V.inv_mem hu), N.coord_inv hu,
    Matrix.mulVec_neg, Matrix.sub_mulVec, Matrix.one_mulVec, CharTwo.neg_eq, sub_eq_add_neg,
    CharTwo.neg_eq, add_comm]

end Coord

section Ker

variable [Finite G] {M T L : Subgroup G} {α : ↥M →* ↥(StatedSL 3 (ZMod 2))}

omit [Finite G] in
theorem commute_of_mem_pCoreOf {q x : G} (hq : q ∈ pCoreOf 2 M) (hx : x ∈ Xq M) :
    q * x = x * q :=
  Subgroup.mem_centralizer_iff.mp ((PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) hx).2) q hq

theorem rhoG_eq_one_of_mem_pCoreOf (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1) {q : G}
    (hq : q ∈ pCoreOf 2 M) : rhoG α q = 1 := by
  rw [rhoG_of_mem (pCoreOf_le' M hq), rhoHom, MonoidHom.comp_apply,
    eq_one_of_isSumOfNaturalModulesVia hnat fun v hv => by
      rw [commute_of_mem_pCoreOf hq (h.Uq_le_Xq hv), mul_inv_cancel_right]]
  rfl

theorem mem_pCoreOf_of_rhoG_eq_one (h : PUHyp M T L)
    (N : NatSec M (Uq M T L) (Uq M T L ⊓ Zq M L) α false) {t : G} (htT : t ∈ T)
    (h1 : rhoG α t = 1) : t ∈ pCoreOf 2 M := by
  refine h.mem_pCoreOf_of_comm_Uq htT fun u hu => ?_
  have hc : ⁅u, t⁆ ∈ Uq M T L := by
    have e : ⁅u, t⁆ = u * (t * u⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (Uq M T L).mul_mem hu
      ((Subgroup.mem_normalizer_iff.mp (N.norm (h.le htT)) _).mp ((Uq M T L).inv_mem hu))
  have h0 : N.coord ⁅u, t⁆ = 0 := by
    rw [coord_commutator N (h.le htT) hu, h1, Units.val_one, sub_self, Matrix.zero_mulVec]
  exact ((N.coord_eq_zero_iff hc).mp h0).2.2

theorem rhoG_eq_one_iff (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1) {t : G}
    (htT : t ∈ T) : rhoG α t = 1 ↔ t ∈ pCoreOf 2 M :=
  ⟨mem_pCoreOf_of_rhoG_eq_one h (NatSec.ofIsSum hnat) htT,
    rhoG_eq_one_of_mem_pCoreOf h hnat⟩

theorem mem_sup_of_rhoG_eq (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    {F : Subgroup G} (hFT : F ≤ T) {x y : G} (hx : x ∈ T) (hy : y ∈ F)
    (he : rhoG α x = rhoG α y) : x ∈ F ⊔ pCoreOf 2 M := by
  have hyT := hFT hy
  have hq : y⁻¹ * x ∈ pCoreOf 2 M := by
    refine (rhoG_eq_one_iff h hnat (T.mul_mem (T.inv_mem hyT) hx)).mp ?_
    rw [rhoG_mul (M.inv_mem (h.le hyT)) (h.le hx), rhoG_inv (h.le hyT), he, inv_mul_cancel]
  have e : x = y * (y⁻¹ * x) := by group
  rw [e]
  exact (F ⊔ pCoreOf 2 M).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)

end Ker

section Sizes

@[expose] def pairSub (c : Fin 3 → ZMod 2) : AddSubgroup (Fin 3 → ZMod 2) where
  carrier := {y | y = 0 ∨ y = c}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (add_zero 0)
    · exact Or.inr (zero_add _)
    · exact Or.inr (add_zero _)
    · exact Or.inl (CharTwo.add_self_eq_zero _)
  neg_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl neg_zero
    · exact Or.inr (CharTwo.neg_eq _)

theorem mem_pairSub {c y : Fin 3 → ZMod 2} : y ∈ pairSub c ↔ y = 0 ∨ y = c := Iff.rfl

variable {M V K : Subgroup G} {α : ↥M →* ↥(StatedSL 3 (ZMod 2))} {dual : Bool}

theorem relIndex_eq_eight (N : NatSec M V K α dual) : K.relIndex V = 8 := by
  have hk : N.β.ker = K.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, N.ker v, Subgroup.mem_subgroupOf]
  rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr N.surj,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  rfl

theorem relIndex_pre_pairSub (N : NatSec M V K α dual) {c : Fin 3 → ZMod 2} (hc0 : c ≠ 0) :
    K.relIndex (N.pre (pairSub c)) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  obtain ⟨u₀, hu₀, hcu₀⟩ := N.exists_coord_eq c
  refine ⟨u₀, N.mem_pre.mpr ⟨hu₀, by rw [hcu₀]; exact Or.inr rfl⟩, fun b hb => ?_⟩
  obtain ⟨hbV, hb⟩ := N.mem_pre.mp hb
  rw [← N.coord_eq_zero_iff (V.mul_mem hbV hu₀), ← N.coord_eq_zero_iff hbV, N.coord_mul hbV hu₀,
    hcu₀]
  rcases mem_pairSub.mp hb with hb | hb <;> rw [hb]
  · simp [hc0]
  · rw [CharTwo.add_self_eq_zero]
    simp [hc0]

theorem le_pre_pairSub (N : NatSec M V K α dual) (c : Fin 3 → ZMod 2) :
    K ≤ N.pre (pairSub c) := fun _ hx =>
  N.mem_pre.mpr ⟨N.le hx, Or.inl ((N.coord_eq_zero_iff (N.le hx)).mpr hx)⟩

theorem card_pre_pairSub (N : NatSec M V K α dual) {c : Fin 3 → ZMod 2} (hc0 : c ≠ 0) :
    Nat.card ↥(N.pre (pairSub c)) = 2 * Nat.card ↥K := by
  have := Subgroup.relIndex_mul_card K (N.pre (pairSub c))
  rw [relIndex_pre_pairSub N hc0, inf_eq_left.mpr (le_pre_pairSub N c)] at this
  exact this.symm

end Sizes

section Invol

@[expose] def commMap {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t : G}
    (ht : t ∈ Subgroup.normalizer (A : Set G)) : ↥A →* ↥A where
  toFun a := ⟨⁅(a : G), t⁆, by
    have e : ⁅(a : G), t⁆ = a * (t * (a : G)⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem a.2 ((Subgroup.mem_normalizer_iff.mp ht _).mp (A.inv_mem a.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    have hta : t * (a : G)⁻¹ * t⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp ht _).mp (A.inv_mem a.2)
    have htb : t * (b : G)⁻¹ * t⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp ht _).mp (A.inv_mem b.2)
    have h1 := hA _ hta _ (A.mul_mem b.2 htb)
    show ⁅(a : G) * b, t⁆ = ⁅(a : G), t⁆ * ⁅(b : G), t⁆
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc (a : G) * b * t * ((a : G) * b)⁻¹ * t⁻¹ =
        a * ((b * (t * (b : G)⁻¹ * t⁻¹)) * (t * (a : G)⁻¹ * t⁻¹)) := by group
      _ = a * ((t * (a : G)⁻¹ * t⁻¹) * (b * (t * (b : G)⁻¹ * t⁻¹))) := by rw [h1]
      _ = a * t * (a : G)⁻¹ * t⁻¹ * (b * t * (b : G)⁻¹ * t⁻¹) := by group)

theorem coe_commMap {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t : G}
    (ht : t ∈ Subgroup.normalizer (A : Set G)) (a : ↥A) :
    ((commMap hA ht a : ↥A) : G) = ⁅(a : G), t⁆ :=
  rfl

variable [Finite G] {M T L : Subgroup G} {α : ↥M →* ↥(StatedSL 3 (ZMod 2))}

theorem uq_inf_centralizer_eq (h : PUHyp M T L)
    (N : NatSec M (Uq M T L) (Uq M T L ⊓ Zq M L) α false)
    (hcard : Nat.card ↥(Zq M L ⊓ Uq M T L) = 2)
    (hcomm : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S,
      (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) → Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆)
    {f : G} (hfT : f ∈ T) (hf2 : f ^ 2 = 1) {c : Fin 3 → ZMod 2} (hc0 : c ≠ 0)
    (hc : ∀ v, (((rhoG α f : GL32) : Mat3) - 1) *ᵥ v = 0 ∨
      (((rhoG α f : GL32) : Mat3) - 1) *ᵥ v = c)
    (hcv : ∃ v, (((rhoG α f : GL32) : Mat3) - 1) *ᵥ v = c) :
    Uq M T L ⊓ Subgroup.centralizer {f} = N.pre (pairSub c) ∧
      (Subgroup.centralizer ({f} : Set G)).relIndex (Uq M T L) = 4 := by
  have hfM : f ∈ M := h.le hfT
  have hUab : ∀ a ∈ Uq M T L, ∀ b ∈ Uq M T L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isElemAbelian_Uq.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUsq : ∀ a ∈ Uq M T L, a⁻¹ = a := fun a ha =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h.isElemAbelian_Uq.2 a ha)
  have hfN : f ∈ Subgroup.normalizer (Uq M T L : Set G) := N.norm hfM
  set κ := commMap hUab hfN with hκ
  have hκmem : ∀ u ∈ Uq M T L, ⁅u, f⁆ ∈ κ.range.map (Uq M T L).subtype := fun u hu =>
    ⟨κ ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
  obtain ⟨S, hTS, hS⟩ := exists_isSylowTwoOf_of_le h.le h.isPGroup
  have hnt : ∃ u ∈ Uq M T L, f * u * f⁻¹ ≠ u := by
    obtain ⟨v, hv⟩ := hcv
    obtain ⟨u, hu, hcu⟩ := N.exists_coord_eq v
    refine ⟨u, hu, fun he => hc0 ?_⟩
    have := coord_conj_rhoG N hfM hu
    rw [he, hcu] at this
    rw [← hv, Matrix.sub_mulVec, Matrix.one_mulVec, ← this, sub_self]
  have hUZ : Uq M T L ⊓ Zq M L ≤ κ.range.map (Uq M T L).subtype := by
    refine (hcomm S hS f (hTS hfT) hnt).trans ?_
    rw [Subgroup.commutator_le]
    intro u hu s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hk2 := zpow_eq_zpow_emod' k hf2
    rw [hk2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [Nat.cast_ofNat, hk, zpow_zero, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [Nat.cast_ofNat, hk, zpow_one]
      exact hκmem u hu
  have hR : κ.range.map (Uq M T L).subtype = N.pre (pairSub c) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine N.mem_pre.mpr ⟨(κ u).2, ?_⟩
      show N.coord ⁅(u : G), f⁆ ∈ pairSub c
      rw [coord_commutator N hfM u.2]
      exact hc _
    · intro x hx
      obtain ⟨hxU, hx⟩ := N.mem_pre.mp hx
      rcases mem_pairSub.mp hx with hx | hx
      · exact hUZ ((N.coord_eq_zero_iff hxU).mp hx)
      · obtain ⟨v, hv⟩ := hcv
        obtain ⟨u, hu, hcu⟩ := N.exists_coord_eq v
        have hyU : ⁅u, f⁆ ∈ Uq M T L := (κ ⟨u, hu⟩).2
        have hy : N.coord ⁅u, f⁆ = N.coord x := by
          rw [coord_commutator N hfM hu, hcu, hv, hx]
        have hz := hUZ (N.inv_mul_mem_of_coord_eq hyU hxU hy)
        have e : x = ⁅u, f⁆ * (⁅u, f⁆⁻¹ * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ (hκmem u hu) hz
  have hcardpre : Nat.card ↥(N.pre (pairSub c)) = 4 := by
    rw [card_pre_pairSub N hc0, inf_comm, hcard]
  have hker : κ.ker = (Subgroup.centralizer ({f} : Set G)).subgroupOf (Uq M T L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      ← commutatorElement_eq_one_iff_mul_comm, ← coe_commMap hUab hfN u, ← hκ]
    exact ⟨fun hh => by rw [hh]; rfl, fun hh => Subtype.ext hh⟩
  have hrel : (Subgroup.centralizer ({f} : Set G)).relIndex (Uq M T L) = 4 := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker,
      ← Subgroup.card_map_of_injective (Uq M T L).subtype_injective, hR, hcardpre]
  have hsub : N.pre (pairSub c) ≤ Uq M T L ⊓ Subgroup.centralizer {f} := by
    rw [← hR]
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(κ u).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show ⁅(u : G), f⁆ * f = f * ⁅(u : G), f⁆
    have key : f * ⁅(u : G), f⁆ * f⁻¹ = ⁅(u : G), f⁆⁻¹ := by
      calc f * ⁅(u : G), f⁆ * f⁻¹ = f * u * f⁻¹ * f ^ 2 * (u : G)⁻¹ * (f ^ 2)⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = ⁅(u : G), f⁆⁻¹ := by
            rw [hf2, commutatorElement_def]
            group
    have hxU : ⁅(u : G), f⁆ ∈ Uq M T L := (κ u).2
    rw [hUsq _ hxU] at key
    calc ⁅(u : G), f⁆ * f = f * ⁅(u : G), f⁆ * f⁻¹ * f := by rw [key]
      _ = f * ⁅(u : G), f⁆ := by group
  have hcardU : Nat.card ↥(Uq M T L) = 16 := by
    have := Subgroup.relIndex_mul_card (Uq M T L ⊓ Zq M L) (Uq M T L)
    rw [relIndex_eq_eight N, inf_eq_left.mpr inf_le_left, inf_comm, hcard] at this
    exact this.symm
  have hcardC : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({f} : Set G)) = 4 := by
    have := Subgroup.relIndex_mul_card (Subgroup.centralizer ({f} : Set G)) (Uq M T L)
    rw [hrel, hcardU, inf_comm] at this
    omega
  refine ⟨(Subgroup.eq_of_le_of_card_ge hsub ?_).symm, hrel⟩
  rw [hcardC, hcardpre]

end Invol

section Off

@[expose] def HasCentre (b : GL32) (c : Fin 3 → ZMod 2) : Prop :=
  (∀ v, ((b : Mat3) - 1) *ᵥ v = 0 ∨ ((b : Mat3) - 1) *ᵥ v = c) ∧ ∃ v, ((b : Mat3) - 1) *ᵥ v = c

theorem HasCentre.img {b₁ b₂ : GL32} {c : Fin 3 → ZMod 2} (h₁ : HasCentre b₁ c)
    (h₂ : HasCentre b₂ c) : ∀ v, ∃ w, ((b₁ : Mat3) - 1) *ᵥ v = ((b₂ : Mat3) - 1) *ᵥ w := by
  intro v
  rcases h₁.1 v with h0 | hc
  · exact ⟨0, by rw [h0, Matrix.mulVec_zero]⟩
  · obtain ⟨w, hw⟩ := h₂.2
    exact ⟨w, by rw [hc, hw]⟩

variable [Finite G] {M T L : Subgroup G} {α : ↥M →* ↥(StatedSL 3 (ZMod 2))}

theorem exists_of_isXOff (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    (hcard : Nat.card ↥(Zq M L ⊓ Uq M T L) = 2)
    (hcomm : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S,
      (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) → Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆)
    {F : Subgroup G} (hF : IsXOff M T F) :
    ∃ f₁ ∈ F, ∃ f₂ ∈ F, ∃ c : Fin 3 → ZMod 2, rhoG α f₁ ≠ 1 ∧ rhoG α f₂ ≠ 1 ∧
      rhoG α f₁ ≠ rhoG α f₂ ∧ HasCentre (rhoG α f₁) c ∧ HasCentre (rhoG α f₂) c ∧
      (∀ x ∈ F, rhoG α x = 1 ∨ rhoG α x = rhoG α f₁ ∨ rhoG α x = rhoG α f₂ ∨
        rhoG α x = rhoG α f₁ * rhoG α f₂) ∧
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F ∧
      (pCoreOf 2 M).relIndex F = 4 := by
  obtain ⟨hFT, hFea, hFQ, hoff⟩ := hF
  have hFM : F ≤ M := hFT.trans h.le
  set N := NatSec.ofIsSum hnat
  have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K => Subgroup.index_ne_zero_of_finite
  let ρF : ↥F →* GL32 := (rhoHom α).comp (Subgroup.inclusion hFM)
  have hρF : ∀ x : ↥F, ρF x = rhoG α x := fun x => (rhoG_of_mem (hFM x.2)).symm
  have hidx : (pCoreOf 2 M).relIndex F = Nat.card ρF.range := by
    rw [Subgroup.relIndex, ← Subgroup.index_ker]
    congr 1
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hρF, rhoG_eq_one_iff h hnat (hFT x.2)]
  obtain ⟨f₁, hf₁F, hf₁Q⟩ := Set.not_subset.mp fun hs => hFQ hs
  have hb₁ : rhoG α f₁ ≠ 1 := fun he => hf₁Q ((rhoG_eq_one_iff h hnat (hFT hf₁F)).mp he)
  have hs₁ := rhoG_sq_eq_one (α := α) hFM hFea hf₁F
  obtain ⟨c₁, hc₁0, hc₁, hcv₁⟩ := transv hs₁ hb₁
  obtain ⟨hC₁, hr₁⟩ :=
    uq_inf_centralizer_eq h N hcard hcomm (hFT hf₁F) (hFea.2 f₁ hf₁F) hc₁0 hc₁ hcv₁
  have hU4 : 4 ≤ (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) := by
    rw [← hr₁]
    exact Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf₁F)) (hne _ _)
  have hX : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) ≤
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) :=
    Subgroup.relIndex_le_of_le_right h.Uq_le_Xq (hne _ _)
  rw [hidx] at hoff
  obtain ⟨f₂, hf₂F, hb₂, hb₂₁⟩ : ∃ f ∈ F, rhoG α f ≠ 1 ∧ rhoG α f ≠ rhoG α f₁ := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hle : ρF.range ≤ Subgroup.zpowers (rhoG α f₁) := by
      rintro _ ⟨x, rfl⟩
      rw [hρF]
      by_cases hx1 : rhoG α x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · rw [hall x x.2 hx1]
        exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hs₁ hb₁] at this
    omega
  have hs₂ := rhoG_sq_eq_one (α := α) hFM hFea hf₂F
  obtain ⟨c₂, hc₂0, hc₂, hcv₂⟩ := transv hs₂ hb₂
  obtain ⟨hC₂, -⟩ :=
    uq_inf_centralizer_eq h N hcard hcomm (hFT hf₂F) (hFea.2 f₂ hf₂F) hc₂0 hc₂ hcv₂
  have hP := isPGroup_map_rhoHom (α := α) h.le h.isPGroup
  have hfour : ∀ x ∈ F, rhoG α x = 1 ∨ rhoG α x = rhoG α f₁ ∨ rhoG α x = rhoG α f₂ ∨
      rhoG α x = rhoG α f₁ * rhoG α f₂ := fun x hx =>
    mem_of_comm_four hP (rhoG_mem_map h.le (hFT hf₁F)) (rhoG_mem_map h.le (hFT hf₂F))
      (rhoG_mem_map h.le (hFT hx)) hs₁ hs₂ hb₁ hb₂ (Ne.symm hb₂₁)
      (rhoG_comm hFM hFea hf₁F hf₂F) (rhoG_comm hFM hFea hx hf₁F) (rhoG_comm hFM hFea hx hf₂F)
  have hle4 : Nat.card ρF.range ≤ 4 := by
    have hsub : (ρF.range : Set GL32) ⊆
        {1, rhoG α f₁, rhoG α f₂, rhoG α f₁ * rhoG α f₂} := by
      rintro _ ⟨x, rfl⟩
      rw [hρF]
      rcases hfour x x.2 with e | e | e | e <;> rw [e] <;> simp
    calc Nat.card ρF.range = Nat.card ↥(ρF.range : Set GL32) := rfl
      _ ≤ Nat.card ↥({1, rhoG α f₁, rhoG α f₂, rhoG α f₁ * rhoG α f₂} : Set GL32) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 4 := by
          rw [Nat.card_coe_set_eq]
          refine (Set.ncard_insert_le _ _).trans ?_
          refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
          refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
          rw [Set.ncard_singleton]
  have hc12 : c₂ = c₁ := by
    by_contra hne12
    have hleZ : Subgroup.centralizer (F : Set G) ⊓ Uq M T L ≤ Uq M T L ⊓ Zq M L := by
      intro u hu
      obtain ⟨huC, huU⟩ := Subgroup.mem_inf.mp hu
      have hpre : ∀ {f c}, f ∈ F → Uq M T L ⊓ Subgroup.centralizer {f} = N.pre (pairSub c) →
          N.coord u = 0 ∨ N.coord u = c := fun {f c} hf hCf => by
        have : u ∈ N.pre (pairSub c) := by
          rw [← hCf]
          exact Subgroup.mem_inf.mpr
            ⟨huU, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf) huC⟩
        exact (N.mem_pre.mp this).2
      refine (N.coord_eq_zero_iff huU).mp ?_
      rcases hpre hf₁F hC₁ with h1 | h1
      · exact h1
      · rcases hpre hf₂F hC₂ with h2 | h2
        · exact h2
        · exact absurd (h2.symm.trans h1) hne12
    have h8 : 8 ≤ (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) := by
      rw [← Subgroup.inf_relIndex_right, ← relIndex_eq_eight N]
      exact Subgroup.relIndex_le_of_le_left hleZ (hne _ _)
    omega
  subst hc12
  refine ⟨f₁, hf₁F, f₂, hf₂F, c₂, hb₁, hb₂, Ne.symm hb₂₁, ⟨hc₁, hcv₁⟩, ⟨hc₂, hcv₂⟩, hfour, ?_, ?_⟩
  · rw [hidx]
    omega
  · rw [hidx]
    omega

theorem le_sup_of_isXOff (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    (hcard : Nat.card ↥(Zq M L ⊓ Uq M T L) = 2)
    (hcomm : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S,
      (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) → Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆)
    {F₁ F₂ : Subgroup G} (hF₁ : IsXOff M T F₁) (hF₂ : IsXOff M T F₂) :
    F₂ ≤ F₁ ⊔ pCoreOf 2 M := by
  obtain ⟨f₁, hf₁, f₂, hf₂, c, hb₁, hb₂, hb₁₂, hc₁, hc₂, -, -, -⟩ :=
    exists_of_isXOff h hnat hcard hcomm hF₁
  obtain ⟨g₁, hg₁, g₂, hg₂, c', hb₁', hb₂', hb₁₂', hc₁', hc₂', hfour', -, -⟩ :=
    exists_of_isXOff h hnat hcard hcomm hF₂
  have hM₁ : F₁ ≤ M := hF₁.1.trans h.le
  have hM₂ : F₂ ≤ M := hF₂.1.trans h.le
  have hP := isPGroup_map_rhoHom (α := α) h.le h.isPGroup
  have hm : ∀ {x : G} {F : Subgroup G}, IsXOff M T F → x ∈ F →
      rhoG α x ∈ (T.subgroupOf M).map (rhoHom α) := fun hF hx => rhoG_mem_map h.le (hF.1 hx)
  set E := (F₁.subgroupOf M).map (rhoHom α)
  have hE : ∀ x ∈ F₁, rhoG α x ∈ E := fun x hx => rhoG_mem_map hM₁ hx
  have hgE : ∀ {g g' : G}, g ∈ F₂ → g' ∈ F₂ → rhoG α g ≠ 1 → rhoG α g' ≠ 1 →
      rhoG α g ≠ rhoG α g' → HasCentre (rhoG α g) c' → HasCentre (rhoG α g') c' →
      rhoG α g ∈ E := fun {g g'} hg hg' hn hn' hgg' hcg hcg' => by
    rcases eq_of_center_four hP (hm hF₁ hf₁) (hm hF₁ hf₂) (hm hF₂ hg) (hm hF₂ hg')
        (rhoG_sq_eq_one hM₁ hF₁.2.1 hf₁) (rhoG_sq_eq_one hM₁ hF₁.2.1 hf₂)
        (rhoG_sq_eq_one hM₂ hF₂.2.1 hg) (rhoG_sq_eq_one hM₂ hF₂.2.1 hg') hb₁ hb₂ hn hn' hb₁₂
        (rhoG_comm hM₁ hF₁.2.1 hf₁ hf₂) (hc₁.img hc₂) hgg' (rhoG_comm hM₂ hF₂.2.1 hg hg')
        (hcg.img hcg') with e | e | e
    · rw [e]
      exact hE _ hf₁
    · rw [e]
      exact hE _ hf₂
    · rw [e]
      exact E.mul_mem (hE _ hf₁) (hE _ hf₂)
  have hg₁E := hgE hg₁ hg₂ hb₁' hb₂' hb₁₂' hc₁' hc₂'
  have hg₂E := hgE hg₂ hg₁ hb₂' hb₁' (Ne.symm hb₁₂') hc₂' hc₁'
  intro x hx
  have hxE : rhoG α x ∈ E := by
    rcases hfour' x hx with e | e | e | e <;> rw [e]
    · exact E.one_mem
    · exact hg₁E
    · exact hg₂E
    · exact E.mul_mem hg₁E hg₂E
  obtain ⟨y, hy, hxy⟩ := exists_of_mem_map hxE
  exact mem_sup_of_rhoG_eq h hnat hF₁.1 (hF₂.1 hx) hy hxy.symm

theorem mem_sup_of_mem_centralizer (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    (hcard : Nat.card ↥(Zq M L ⊓ Uq M T L) = 2)
    (hcomm : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S,
      (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) → Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆)
    {F : Subgroup G} (hF : IsXOff M T F) {y : G} (hyT : y ∈ T)
    (hyC : y ∈ Subgroup.centralizer (F : Set G)) : y ∈ F ⊔ pCoreOf 2 M := by
  obtain ⟨f₁, hf₁, f₂, hf₂, c, hb₁, hb₂, hb₁₂, -, -, -, -, -⟩ :=
    exists_of_isXOff h hnat hcard hcomm hF
  have hFM : F ≤ M := hF.1.trans h.le
  have hP := isPGroup_map_rhoHom (α := α) h.le h.isPGroup
  have hy : ∀ {f : G}, f ∈ F → rhoG α y * rhoG α f = rhoG α f * rhoG α y := fun {f} hf => by
    rw [← rhoG_mul (h.le hyT) (hFM hf), ← rhoG_mul (hFM hf) (h.le hyT),
      Subgroup.mem_centralizer_iff.mp hyC f hf]
  rcases mem_of_comm_four hP (rhoG_mem_map h.le (hF.1 hf₁)) (rhoG_mem_map h.le (hF.1 hf₂))
      (rhoG_mem_map h.le hyT) (rhoG_sq_eq_one hFM hF.2.1 hf₁) (rhoG_sq_eq_one hFM hF.2.1 hf₂)
      hb₁ hb₂ hb₁₂ (rhoG_comm hFM hF.2.1 hf₁ hf₂) (hy hf₁) (hy hf₂) with e | e | e | e
  · exact mem_sup_of_rhoG_eq h hnat hF.1 hyT F.one_mem (e.trans rhoG_one.symm)
  · exact mem_sup_of_rhoG_eq h hnat hF.1 hyT hf₁ e
  · exact mem_sup_of_rhoG_eq h hnat hF.1 hyT hf₂ e
  · exact mem_sup_of_rhoG_eq h hnat hF.1 hyT (F.mul_mem hf₁ hf₂)
      (e.trans (rhoG_mul (hFM hf₁) (hFM hf₂)).symm)

end Off

end OffIV

open OffIV in
theorem PUHyp.xOffData_of_isSL3TwoU {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L)
    (hX : IsSL3TwoU M T L) : XOffData M T := by
  obtain ⟨-, hcard, ⟨α, -, hnat⟩, -, hcomm⟩ := hX
  refine XOffData.of_cent h h.centralizer_Z0q (fun F₁ F₂ h₁ h₂ => ?_) (fun F hF => ?_)
    (fun F hF y hy hyC => mem_sup_of_mem_centralizer h hnat hcard hcomm hF hy hyC)
  · exact le_antisymm (sup_le (le_sup_of_isXOff h hnat hcard hcomm h₂ h₁) le_sup_right)
      (sup_le (le_sup_of_isXOff h hnat hcard hcomm h₁ h₂) le_sup_right)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, heq, -⟩ := exists_of_isXOff h hnat hcard hcomm hF
    exact heq

open OffIV in
theorem PUHyp.xOffCent_of_isSL3TwoU {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) (hX : IsSL3TwoU M T L) :
    (∀ F : Subgroup G, IsXOff M T F → T ⊓ Subgroup.centralizer (F : Set G) ≤ F ⊔ pCoreOf 2 M) ∧
      ∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F = 4 := by
  obtain ⟨-, hcard, ⟨α, -, hnat⟩, -, hcomm⟩ := hX
  refine ⟨fun F hF y hy => mem_sup_of_mem_centralizer h hnat hcard hcomm hF hy.1 hy.2,
    fun F hF => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h4⟩ := exists_of_isXOff h hnat hcard hcomm hF
  exact h4

end CFSG.Quasithin.MS93
