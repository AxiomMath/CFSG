module

public import CFSG.Quasithin.MS93.S36Crit
public import CFSG.Quasithin.MS93.S32Basic
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.Quasithin.MS93.ML3Sec
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

namespace S36

section Card

theorem card_eq_card_inf_ker_mul_card_map {H : Type*} [Group H] (f : G →* H) (K : Subgroup G) :
    Nat.card ↥K = Nat.card ↥(K ⊓ f.ker) * Nat.card ↥(K.map f) := by
  have h1 := Subgroup.card_mul_index (f.comp K.subtype).ker
  rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype] at h1
  rw [← h1]
  congr 1
  have : (f.comp K.subtype).ker = (f.ker).subgroupOf K := (MonoidHom.comap_ker f K.subtype).symm
  rw [this, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm]

end Card

section Comm

variable {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t : G}
  (ht : t ∈ Subgroup.normalizer (A : Set G))

@[expose] def commHomOn : ↥A →* ↥A where
  toFun a := ⟨t * a * t⁻¹ * (a : G)⁻¹,
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp ht a).mp a.2) (A.inv_mem a.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have hta : t * (a : G) * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp ht a).mp a.2
    have htb : t * (b : G) * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp ht b).mp b.2
    have h1 := hA _ (A.inv_mem a.2) _ (A.mul_mem htb (A.inv_mem b.2))
    calc t * ((a : G) * b) * t⁻¹ * ((b : G)⁻¹ * (a : G)⁻¹) =
        (t * a * t⁻¹) * ((t * b * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (t * a * t⁻¹) * ((a : G)⁻¹ * (t * b * t⁻¹ * (b : G)⁻¹)) := by rw [h1]
      _ = t * a * t⁻¹ * (a : G)⁻¹ * (t * b * t⁻¹ * (b : G)⁻¹) := by group)

theorem commHomOn_apply (a : ↥A) :
    ((commHomOn hA ht a : ↥A) : G) = t * a * t⁻¹ * (a : G)⁻¹ := rfl

theorem mem_ker_commHomOn (a : ↥A) : a ∈ (commHomOn hA ht).ker ↔ t * a = a * t := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff, commHomOn_apply, OneMemClass.coe_one,
    mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

@[expose] def commImg : Subgroup G := (commHomOn hA ht).range.map A.subtype

theorem mem_commImg {x : G} : x ∈ commImg hA ht ↔ ∃ a ∈ A, t * a * t⁻¹ * a⁻¹ = x := by
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨commHomOn hA ht ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩

theorem commImg_le : commImg hA ht ≤ A := Subgroup.map_subtype_le _

theorem card_commImg_mul :
    Nat.card ↥(commImg hA ht) * Nat.card ↥(A ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥A := by
  have h1 := Subgroup.card_mul_index (commHomOn hA ht).ker
  rw [Subgroup.index_ker] at h1
  have e2 : ((commHomOn hA ht).ker).map A.subtype = A ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr
        ((mem_ker_commHomOn hA ht a).mp ha).symm⟩
    · rintro ⟨hxA, hxC⟩
      refine ⟨⟨x, hxA⟩, (mem_ker_commHomOn hA ht _).mpr ?_, rfl⟩
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
  rw [commImg, Subgroup.card_map_of_injective A.subtype_injective, ← e2,
    Subgroup.card_map_of_injective A.subtype_injective, mul_comm]
  exact h1

theorem commImg_le_centralizer (hA2 : ∀ a ∈ A, a ^ 2 = 1) (ht2 : t ^ 2 = 1) :
    commImg hA ht ≤ A ⊓ Subgroup.centralizer ({t} : Set G) := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨commImg_le hA ht hx, ?_⟩
  obtain ⟨a, ha, rfl⟩ := (mem_commImg hA ht).mp hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA2 a ha)
  have hb : t * a * t ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp ht a).mp ha
    rwa [htinv] at this
  have hab := hA _ hb _ ha
  rw [htinv, hainv]
  calc t * a * t * a * t = a * (t * a * t) * t := by rw [hab]
    _ = a * t * a * (t * t) := by group
    _ = t * t * (a * t * a) := by rw [htt, one_mul, mul_one]
    _ = t * (t * a * t * a) := by group

theorem commutator_zpowers_le_commImg (ht2 : t ^ 2 = 1) :
    ⁅A, Subgroup.zpowers t⁆ ≤ commImg hA ht := by
  rw [Subgroup.commutator_le]
  intro a ha g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [zpow_eq_zpow_emod' k ht2, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [hk, zpow_zero, commutatorElement_one_right]
    exact (commImg hA ht).one_mem
  · rw [hk, zpow_one]
    refine (mem_commImg hA ht).mpr ⟨a⁻¹, A.inv_mem ha, ?_⟩
    have hb : t * a⁻¹ * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp ht _).mp (A.inv_mem ha)
    rw [commutatorElement_def, inv_inv, hA _ hb _ ha]
    group

end Comm

section Sixteen

variable [Finite G]

theorem relIndex_ne_zero' (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h0
  have := Subgroup.relIndex_mul_card H K
  rw [h0, zero_mul] at this
  exact Nat.card_pos.ne this

theorem four_le_card_of_lt {U A W : Subgroup G} (hU16 : Nat.card ↥U = 16) (hA2 : Nat.card ↥A = 2)
    (hAW : A ≤ W) (hWA : ¬ W ≤ A) (hWU : W ≤ U) : 4 ≤ Nat.card ↥W := by
  have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hAW fun e => hWA (le_of_eq e.symm))
  rw [hA2] at hlt
  have hdvd : Nat.card ↥W ∣ 16 := hU16 ▸ Subgroup.card_dvd_of_le hWU
  obtain ⟨c, hc⟩ := hdvd
  rcases (by omega : Nat.card ↥W = 3 ∨ 4 ≤ Nat.card ↥W) with h3 | h4
  · rw [h3] at hc
    omega
  · exact h4

theorem le_of_card_mul_eq_sixteen {I C W A₀ : Subgroup G} (hIC : I ≤ C)
    (hcard : Nat.card ↥I * Nat.card ↥C = 16) (hWC : W ≤ C) (hW : 4 ≤ Nat.card ↥W)
    (hA₀ : Nat.card ↥A₀ = 2) (hA₀W : A₀ ≤ W) (hIA : I ≠ ⊥ → A₀ ≤ I) : I ≤ W := by
  by_cases hI : I = ⊥
  · rw [hI]
    exact bot_le
  have hAI := hIA hI
  have h1 : Nat.card ↥I ≤ Nat.card ↥C := Subgroup.card_le_of_le hIC
  have h2 : 2 ≤ Nat.card ↥I := hA₀ ▸ Subgroup.card_le_of_le hAI
  have h4 : Nat.card ↥I ≤ 4 := by
    by_contra hc
    have h6 : 5 * 5 ≤ Nat.card ↥I * Nat.card ↥C := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨c, hc⟩ : Nat.card ↥I ∣ 16 := ⟨_, hcard.symm⟩
  rcases (by omega : Nat.card ↥I = 2 ∨ Nat.card ↥I = 3 ∨ Nat.card ↥I = 4) with h5 | h5 | h5
  · have : A₀ = I := Subgroup.eq_of_le_of_card_ge hAI (by rw [h5, hA₀])
    rw [← this]
    exact hA₀W
  · rw [h5] at hc
    omega
  · have hC : Nat.card ↥C = 4 := by
      rw [h5] at hcard
      omega
    have : W = C := Subgroup.eq_of_le_of_card_ge hWC (by rw [hC]; exact hW)
    rw [this]
    exact hIC

end Sixteen

section TImageCard

variable {T : Subgroup G}

theorem mem_tImage {ψ : MulAut ↥T} {K : Subgroup G} {x : G} :
    x ∈ tImage ψ K ↔ ∃ k : ↥T, (k : G) ∈ K ∧ ((ψ k : ↥T) : G) = x := by
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨ψ k, ⟨k, hk, rfl⟩, rfl⟩

theorem card_tImage (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    Nat.card ↥(tImage ψ K) = Nat.card ↥K := by
  rw [tImage, Subgroup.card_map_of_injective T.subtype_injective,
    Subgroup.card_map_of_injective ψ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem sq_eq_one_of_mem_tImage {ψ : MulAut ↥T} {K : Subgroup G} (hK : ∀ k ∈ K, k ^ 2 = 1)
    {x : G} (hx : x ∈ tImage ψ K) : x ^ 2 = 1 := by
  obtain ⟨k, hk, rfl⟩ := mem_tImage.mp hx
  have : k ^ 2 = 1 := Subtype.ext (by simpa using hK _ hk)
  calc ((ψ k : ↥T) : G) ^ 2 = ((ψ (k ^ 2) : ↥T) : G) := by rw [map_pow]; rfl
    _ = 1 := by rw [this, map_one]; rfl

theorem commute_of_mem_tImage {ψ : MulAut ↥T} {K K' : Subgroup G}
    (hKK : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) {x y : G} (hx : x ∈ tImage ψ K)
    (hy : y ∈ tImage ψ K') : x * y = y * x := by
  obtain ⟨k, hk, rfl⟩ := mem_tImage.mp hx
  obtain ⟨k', hk', rfl⟩ := mem_tImage.mp hy
  have : k * k' = k' * k := Subtype.ext (hKK _ hk _ hk')
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, this]

end TImageCard

section NatSecFacts

variable {F : Type} [Field F] {L V K : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)}

theorem alpha_eq_one_of_conj (N : NatSec L V K α false) {l : ↥L}
    (hl : ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ K) : α l = 1 := by
  have key : ∀ y : Fin 3 → F, (natAct false (toSL3 α l)).mulVec y = y := by
    intro y
    obtain ⟨v, hv, rfl⟩ := N.exists_coord_eq y
    have hlv := N.conj_mem l hv
    have hc := (N.coord_eq_zero_iff (V.mul_mem hlv (V.inv_mem hv))).mpr (hl v hv)
    rw [N.coord_mul hlv (V.inv_mem hv), N.coord_inv hv, add_neg_eq_zero, N.coord_conj l hv] at hc
    exact hc
  have hmat : ((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [natAct_false, Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
  have h1 : toSL3 α l = 1 := Subtype.ext hmat
  have e : α l = specialLinearGroupEquivStatedSL 3 F (toSL3 α l) := by simp [toSL3]
  rw [e, h1, map_one]

theorem natSec_card_eq [Finite F] (N : NatSec L V K α false) :
    Nat.card ↥V = Nat.card ↥K * Nat.card F ^ 3 := by
  have h1 := Subgroup.card_mul_index N.β.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr N.surj, Subgroup.card_top] at h1
  have hker : N.β.ker = K.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, N.ker v, Subgroup.mem_subgroupOf]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe N.le).toEquiv] at h1
  rw [← h1, show Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (Fin 3 → F) from rfl,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

end NatSecFacts

section CaseIV

variable [Finite G] {M T L : Subgroup G}

theorem isPerfect_statedSL3_two : Group.IsPerfect ↥(StatedSL 3 (ZMod 2)) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) (ZMod 2)

variable (h : PUHyp M T L) {α : ↥M →* ↥(StatedSL 3 (ZMod 2))} (hαs : Function.Surjective α)
  (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
include h hnat

omit [Finite G] h hnat in
theorem natAct_toSL3_eq_one {m : ↥M} (hm : α m = 1) :
    natAct false (toSL3 α m) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [natAct_false]
  have : toSL3 α m = 1 := by simp [toSL3, hm]
  rw [this]
  rfl

theorem exists_alpha_ne_one : ∃ l : ↥L, α (Subgroup.inclusion h.L_le l) ≠ 1 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  set N := NatSec.ofIsSum hnat with hN
  have hUL : ⁅Uq M T L, L⁆ ≤ Uq M T L ⊓ Zq M L := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hui : u⁻¹ ∈ Uq M T L := (Uq M T L).inv_mem hu
    have hc := N.coord_conj (Subgroup.inclusion h.L_le ⟨l, hl⟩) hui
    rw [natAct_toSL3_eq_one (hall ⟨l, hl⟩), Matrix.one_mulVec] at hc
    have hmem : l * u⁻¹ * l⁻¹ ∈ Uq M T L := N.conj_mem (Subgroup.inclusion h.L_le ⟨l, hl⟩) hui
    have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [e, ← N.coord_eq_zero_iff ((Uq M T L).mul_mem hu hmem), N.coord_mul hu hmem]
    simp only [Subgroup.coe_inclusion] at hc
    rw [hc, N.coord_inv hu, add_neg_cancel]
  rw [h.Uq_comm] at hUL
  obtain ⟨u, hu, hcu⟩ := N.exists_coord_eq (Pi.single 0 1)
  have h0 := (N.coord_eq_zero_iff hu).mpr (hUL hu)
  rw [hcu] at h0
  have := congrFun h0 0
  simp at this

@[expose] def kerG (α : ↥M →* ↥(StatedSL 3 (ZMod 2))) : Subgroup G := α.ker.map M.subtype

omit [Finite G] h hnat in
theorem mem_kerG {t : G} : t ∈ kerG α ↔ ∃ ht : t ∈ M, α ⟨t, ht⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨ht, hα⟩
    exact ⟨⟨t, ht⟩, hα, rfl⟩

omit [Finite G] h hnat in
theorem le_normalizer_kerG : M ≤ Subgroup.normalizer (kerG α : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_kerG, mem_kerG]
  constructor
  · rintro ⟨hx, hαx⟩
    refine ⟨M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm), ?_⟩
    have : (⟨m * x * m⁻¹, M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm)⟩ : ↥M) =
        ⟨m, hm⟩ * ⟨x, hx⟩ * (⟨m, hm⟩ : ↥M)⁻¹ := rfl
    rw [this, map_mul, map_mul, hαx, mul_one, map_inv, mul_inv_cancel]
  · rintro ⟨hx', hαx⟩
    have hx : x ∈ M := by
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) hx') hm
      simpa [mul_assoc] using this
    refine ⟨hx, ?_⟩
    have e : (⟨x, hx⟩ : ↥M) = (⟨m, hm⟩ : ↥M)⁻¹ * ⟨m * x * m⁻¹, hx'⟩ * ⟨m, hm⟩ :=
      Subtype.ext (by simp [mul_assoc])
    rw [e, map_mul, map_mul, hαx, mul_one, map_inv, inv_mul_cancel]

theorem mem_pCoreOf_of_alpha_eq_one {t : G} (ht : t ∈ M) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1)
    (hα1 : α ⟨t, ht⟩ = 1) : t ∈ pCoreOf 2 M := by
  obtain ⟨l, hl⟩ := exists_alpha_ne_one h hnat
  refine h.mem_pCoreOf_of_rel (le_normalizer_kerG (α := α)) (fun hLD => hl ?_) ht ht2
    fun l' hl' => ?_
  · obtain ⟨_, h1⟩ := mem_kerG.mp (hLD l.2)
    exact h1
  · rw [mem_kerG]
    refine ⟨M.mul_mem (M.mul_mem (M.mul_mem ht (h.L_le hl')) (M.inv_mem ht))
      (M.inv_mem (h.L_le hl')), ?_⟩
    have e : (⟨⁅t, l'⁆, M.mul_mem (M.mul_mem (M.mul_mem ht (h.L_le hl')) (M.inv_mem ht))
        (M.inv_mem (h.L_le hl'))⟩ : ↥M) = ⁅(⟨t, ht⟩ : ↥M), ⟨l', h.L_le hl'⟩⁆ := rfl
    rw [e, map_commutatorElement, hα1, commutatorElement_one_left]

omit [Finite G] h hnat in
theorem commute_of_mem_pCoreOf_Xq {q x : G} (hq : q ∈ pCoreOf 2 M) (hx : x ∈ Xq M) :
    q * x = x * q :=
  Subgroup.mem_centralizer_iff.mp ((PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) hx).2) q hq

theorem alpha_eq_one_of_mem_pCoreOf {q : G} (hq : q ∈ pCoreOf 2 M) :
    α ⟨q, pCoreOf_le' M hq⟩ = 1 :=
  eq_one_of_isSumOfNaturalModulesVia hnat fun v hv => by
    rw [commute_of_mem_pCoreOf_Xq hq (h.Uq_le_Xq hv), mul_inv_cancel_right]

omit hnat in
include hαs in
theorem map_L_eq_top : (L.subgroupOf M).map α = ⊤ := by
  have : Group.IsPerfect ↥(StatedSL 3 (ZMod 2)) := isPerfect_statedSL3_two
  have hn : ((L.subgroupOf M).map α).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer).map α hαs
  refine eq_top_of_perfect_of_pow_mem _ fun x => ?_
  obtain ⟨m, rfl⟩ := hαs x
  obtain ⟨e, he⟩ := h.exists_pow_mem_L m.2
  exact ⟨e, m ^ 2 ^ e, by simpa [Subgroup.mem_subgroupOf] using he, map_pow α m _⟩

include hαs in
theorem commute_of_mem_T_Zq {t z : G} (ht : t ∈ T) (hz : z ∈ Zq M L) : t * z = z * t := by
  have htM : t ∈ M := h.le ht
  obtain ⟨⟨l, hlM⟩, hlL, hl⟩ : ∃ l' ∈ L.subgroupOf M, α l' = α ⟨t, htM⟩ := by
    have : α ⟨t, htM⟩ ∈ (L.subgroupOf M).map α := by
      rw [map_L_eq_top h hαs]
      exact Subgroup.mem_top _
    obtain ⟨l', hl', he⟩ := this
    exact ⟨l', hl', he⟩
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.mp hlL
  set k : G := l⁻¹ * t with hk
  have hkM : k ∈ M := M.mul_mem (M.inv_mem (h.L_le hlL')) htM
  have hαk : α ⟨k, hkM⟩ = 1 := by
    have e : (⟨k, hkM⟩ : ↥M) = (⟨l, h.L_le hlL'⟩ : ↥M)⁻¹ * ⟨t, htM⟩ := rfl
    rw [e, map_mul, map_inv, ← hl, inv_mul_cancel]
  have hZn : M ≤ Subgroup.normalizer (Zq M L : Set G) := le_normalizer_Zq h.le_normalizer
  have hZL : ∀ z ∈ Zq M L, l * z = z * l := fun z hz =>
    Subgroup.mem_centralizer_iff.mp hz.2 l hlL'
  have hconj : ∀ z ∈ Zq M L, t * z * t⁻¹ = k * z * k⁻¹ := by
    intro z hz
    have hkz : k * z * k⁻¹ ∈ Zq M L := (Subgroup.mem_normalizer_iff.mp (hZn hkM) z).mp hz
    have e : t = l * k := by rw [hk]; group
    rw [e]
    calc l * k * z * (l * k)⁻¹ = l * (k * z * k⁻¹) * l⁻¹ := by group
      _ = k * z * k⁻¹ * l * l⁻¹ := by rw [hZL _ hkz]
      _ = k * z * k⁻¹ := by group
  have hpow : ∀ n : ℕ, ∀ z ∈ Zq M L, t ^ n * z * (t ^ n)⁻¹ = k ^ n * z * (k ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z _; simp
    | succ n ih =>
      intro z hz
      have hkz : k * z * k⁻¹ ∈ Zq M L := (Subgroup.mem_normalizer_iff.mp (hZn hkM) z).mp hz
      calc t ^ (n + 1) * z * (t ^ (n + 1))⁻¹ = t ^ n * (t * z * t⁻¹) * (t ^ n)⁻¹ := by
            rw [pow_succ]; group
        _ = t ^ n * (k * z * k⁻¹) * (t ^ n)⁻¹ := by rw [hconj z hz]
        _ = k ^ n * (k * z * k⁻¹) * (k ^ n)⁻¹ := ih _ hkz
        _ = k ^ (n + 1) * z * (k ^ (n + 1))⁻¹ := by rw [pow_succ]; group
  obtain ⟨f, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  have hk2 : (k ^ m) ^ 2 ^ f = 1 := by
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hkmM : k ^ m ∈ M := M.pow_mem hkM m
  have hkmQ : k ^ m ∈ pCoreOf 2 M := by
    refine mem_pCoreOf_of_alpha_eq_one h hnat hkmM ⟨f, hk2⟩ ?_
    have e : (⟨k ^ m, hkmM⟩ : ↥M) = (⟨k, hkM⟩ : ↥M) ^ m := rfl
    rw [e, map_pow, hαk, one_pow]
  have htm : t ^ m * z * (t ^ m)⁻¹ = z := by
    rw [hpow m z hz, commute_of_mem_pCoreOf_Xq hkmQ hz.1, mul_inv_cancel_right]
  have htmC : t ^ m ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t ^ m * z = t ^ m * z * (t ^ m)⁻¹ * t ^ m := by group
      _ = z * t ^ m := by rw [htm]
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht⟩
  have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hcop : m.gcd (orderOf t) = 1 := by
    have h1 : orderOf t ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one he'
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hm))
  have htz : t ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.zpowers_le.mpr htmC) (mem_zpowers_pow_iff.mpr hcop)
  exact Subgroup.mem_centralizer_singleton_iff.mp htz

omit [Finite G] h hnat in
theorem card_eq_card_inf_kerG_mul {K : Subgroup G} (hK : K ≤ M) :
    Nat.card ↥K = Nat.card ↥(K ⊓ kerG α) * Nat.card ↥((K.subgroupOf M).map α) := by
  have h1 := card_eq_card_inf_ker_mul_card_map α (K.subgroupOf M)
  have e1 : K.subgroupOf M ⊓ α.ker = (K ⊓ kerG α).subgroupOf M := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_kerG]
    exact ⟨fun hx => ⟨hx.1, x.2, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
  rw [e1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hK)).toEquiv] at h1
  exact h1

theorem pCoreOf_le_kerG : pCoreOf 2 M ≤ kerG α := fun _ hq =>
  mem_kerG.mpr ⟨pCoreOf_le' M hq, alpha_eq_one_of_mem_pCoreOf h hnat hq⟩

theorem inf_kerG_le {K : Subgroup G} (hK2 : IsPGroup 2 K) : K ⊓ kerG α ≤ pCoreOf 2 M := by
  rintro x ⟨hxK, hxk⟩
  obtain ⟨hxM, hαx⟩ := mem_kerG.mp hxk
  obtain ⟨e, he⟩ := hK2 ⟨x, hxK⟩
  exact mem_pCoreOf_of_alpha_eq_one h hnat hxM ⟨e, by simpa using congrArg Subtype.val he⟩ hαx

theorem card_eq_card_pCoreOf_mul {K : Subgroup G} (hKM : K ≤ M) (hK2 : IsPGroup 2 K)
    (hQK : pCoreOf 2 M ≤ K) :
    Nat.card ↥K = Nat.card ↥(pCoreOf 2 M) * Nat.card ↥((K.subgroupOf M).map α) := by
  rw [card_eq_card_inf_kerG_mul (α := α) hKM,
    le_antisymm (inf_kerG_le h hnat hK2) (le_inf hQK (pCoreOf_le_kerG h hnat))]

theorem card_eq_card_inf_pCoreOf_mul {K : Subgroup G} (hKT : K ≤ T) :
    Nat.card ↥K = Nat.card ↥(K ⊓ pCoreOf 2 M) * Nat.card ↥((K.subgroupOf M).map α) := by
  have e : K ⊓ kerG α = K ⊓ pCoreOf 2 M :=
    le_antisymm (le_inf inf_le_left (inf_kerG_le h hnat (h.isPGroup.to_le hKT)))
      (inf_le_inf_left _ (pCoreOf_le_kerG h hnat))
  rw [card_eq_card_inf_kerG_mul (α := α) (hKT.trans h.le), e]

omit [Finite G] h hnat in
theorem card_statedSL3_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

omit [Finite G] h hnat in
theorem card_dvd_eight_of_isPGroup {P : Subgroup ↥(StatedSL 3 (ZMod 2))} (hP : IsPGroup 2 P) :
    Nat.card ↥P ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hdvd : Nat.card ↥P ∣ 168 := card_statedSL3_two ▸ Subgroup.card_subgroup_dvd_card P
  rw [hn] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ n) 21 := Nat.Coprime.pow_left n (by norm_num)
  exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)

omit [Finite G] h hnat in
theorem card_map_dvd_eight {K : Subgroup G} (hKM : K ≤ M) (hK2 : IsPGroup 2 K) :
    Nat.card ↥((K.subgroupOf M).map α) ∣ 8 :=
  card_dvd_eight_of_isPGroup ((hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKM).symm).map α)

omit hnat in
theorem uq_comm : ∀ a ∈ Uq M T L, ∀ b ∈ Uq M T L, a * b = b * a := fun _ ha _ hb =>
  commute_of_mem_pCoreOf_Xq (Xq_le_pCoreOf M (h.Uq_le_Xq ha)) (h.Uq_le_Xq hb)

theorem not_commImg_le {t : G} (htM : t ∈ M) (hαt : α ⟨t, htM⟩ ≠ 1) :
    ¬ commImg (uq_comm h) (le_normalizer_Uq h.le_normalizer htM) ≤ Uq M T L ⊓ Zq M L := by
  intro hle
  exact hαt (alpha_eq_one_of_conj (NatSec.ofIsSum hnat) fun v hv =>
    hle ((mem_commImg _ _).mpr ⟨v, hv, rfl⟩))

omit hnat in
theorem exists_ne_of_commImg_ne_bot {t : G} (htM : t ∈ M)
    (hI : commImg (uq_comm h) (le_normalizer_Uq h.le_normalizer htM) ≠ ⊥) :
    ∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  apply hI
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_commImg _ _).mp hx
  rw [hall a ha, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem card_inf_centralizer_le_four (hA₀2 : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2)
    (hU16 : Nat.card ↥(Uq M T L) = 16)
    (hinv : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S, (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) →
      Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆)
    {S : Subgroup G} (hS : IsSylowTwoOf S M) {t : G} (htS : t ∈ S) (ht2 : t ^ 2 = 1)
    (hαt : α ⟨t, hS.1 htS⟩ ≠ 1) :
    Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({t} : Set G)) ≤ 4 := by
  set I := commImg (uq_comm h) (le_normalizer_Uq h.le_normalizer (hS.1 htS)) with hIdef
  have hnle := not_commImg_le h hnat (hS.1 htS) hαt
  have hne : I ≠ ⊥ := by
    intro hb
    apply hnle
    show I ≤ _
    rw [hb]
    exact bot_le
  have hA₀I : Uq M T L ⊓ Zq M L ≤ I :=
    (hinv S hS t htS (exists_ne_of_commImg_ne_bot h (hS.1 htS) hne)).trans
      (commutator_zpowers_le_commImg _ _ ht2)
  have h4 : 4 ≤ Nat.card ↥I := four_le_card_of_lt hU16 hA₀2 hA₀I hnle (commImg_le _ _)
  have hm := card_commImg_mul (uq_comm h) (le_normalizer_Uq h.le_normalizer (hS.1 htS))
  rw [← hIdef, hU16] at hm
  by_contra hc
  have : 4 * 5 ≤ Nat.card ↥I * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.mul_le_mul h4 (by omega)
  omega

theorem four_le_card_map_tImage_inv (hA₀2 : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2)
    (hU16 : Nat.card ↥(Uq M T L) = 16)
    (hinv : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S, (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) →
      Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆)
    {S : Subgroup G} (hS : IsSylowTwoOf S M) (hTS : T ≤ S) {ψ : MulAut ↥T} {z' : G}
    (hz'Z : z' ∈ tImage ψ (Z0q M T)) (hz'Q : z' ∉ pCoreOf 2 M) :
    4 ≤ Nat.card ↥(((tImage ψ⁻¹ (Z0q M T)).subgroupOf M).map α) := by
  have hz'T : z' ∈ T := tImage_le ψ _ hz'Z
  have hz'2 : z' ^ 2 = 1 := sq_eq_one_of_mem_tImage h.isElemAbelian_Z0q.2 hz'Z
  have hαz' : α ⟨z', hS.1 (hTS hz'T)⟩ ≠ 1 := fun h1 =>
    hz'Q (mem_pCoreOf_of_alpha_eq_one h hnat _ ⟨1, by simpa using hz'2⟩ h1)
  have hC4 := card_inf_centralizer_le_four h hnat hA₀2 hU16 hinv hS (hTS hz'T) hz'2 hαz'
  set C := Subgroup.centralizer ({z'} : Set G) with hCdef
  have hrU : 4 ≤ C.relIndex (Uq M T L) := by
    have := Subgroup.relIndex_mul_card C (Uq M T L)
    rw [inf_comm, hU16] at this
    by_contra hlt
    have : C.relIndex (Uq M T L) * Nat.card ↥(Uq M T L ⊓ C) ≤ 3 * 4 :=
      Nat.mul_le_mul (by omega) hC4
    omega
  have hrZ : C.relIndex (Uq M T L) ≤ C.relIndex (Z0q M T) :=
    Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) (relIndex_ne_zero' _ _)
  have hψQC : tImage ψ (pCoreOf 2 M) ≤ C := by
    intro y hy
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_mem_tImage (fun q hq x hx => commute_of_mem_pCoreOf_Xq hq hx) hy
      (tImage_mono ψ h.Z0q_le_Xq hz'Z)
  have hrQ : C.relIndex (Z0q M T) ≤ (tImage ψ (pCoreOf 2 M)).relIndex (Z0q M T) :=
    Subgroup.relIndex_le_of_le_left hψQC (relIndex_ne_zero' _ _)
  have hcardZ := Subgroup.relIndex_mul_card (tImage ψ (pCoreOf 2 M)) (Z0q M T)
  set B := tImage ψ⁻¹ (Z0q M T) with hBdef
  have hBT : B ≤ T := tImage_le _ _
  have hBcard : Nat.card ↥B = Nat.card ↥(Z0q M T) := card_tImage ψ⁻¹ (Z0q_le_T h)
  have hBQ : Nat.card ↥(B ⊓ pCoreOf 2 M) ≤
      Nat.card ↥(tImage ψ (pCoreOf 2 M) ⊓ Z0q M T) := by
    rw [← card_tImage ψ (inf_le_left.trans hBT)]
    refine Subgroup.card_le_of_le (le_inf (tImage_mono ψ inf_le_right) ?_)
    exact (tImage_mono ψ inf_le_left).trans (tImage_tImage_inv ψ (Z0q_le_T h)).le
  have hcB := card_eq_card_inf_pCoreOf_mul h hnat hBT (α := α)
  have hpos : 0 < Nat.card ↥(B ⊓ pCoreOf 2 M) := Nat.card_pos
  by_contra hlt
  have h1 : Nat.card ↥(B ⊓ pCoreOf 2 M) * Nat.card ↥((B.subgroupOf M).map α) ≤
      Nat.card ↥(B ⊓ pCoreOf 2 M) * 3 := Nat.mul_le_mul_left _ (by omega)
  have h2 : 4 * Nat.card ↥(tImage ψ (pCoreOf 2 M) ⊓ Z0q M T) ≤
      (tImage ψ (pCoreOf 2 M)).relIndex (Z0q M T) *
        Nat.card ↥(tImage ψ (pCoreOf 2 M) ⊓ Z0q M T) :=
    Nat.mul_le_mul_right _ (hrU.trans (hrZ.trans hrQ))
  omega

include hαs in
theorem not_Uq_inf_centralizer_le (hXZU : Xq M = Zq M L ⊔ Uq M T L) :
    ¬ Uq M T L ⊓ Subgroup.centralizer (T : Set G) ≤ Zq M L := by
  intro hle
  have hZT : Zq M L ≤ Subgroup.centralizer (T : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => commute_of_mem_T_Zq h hαs hnat ht hz
  have heq : omegaOneCenterOf T = Zq M L := by
    rw [h.omegaOneCenterOf_eq]
    refine le_antisymm ?_ (le_inf inf_le_left hZT)
    rintro x ⟨hxX, hxC⟩
    have hZU : Zq M L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
      Zq_le.trans (le_normalizer_Uq h.le_normalizer)
    have hx' : x ∈ ((Zq M L ⊔ Uq M T L : Subgroup G) : Set G) := by
      rw [← hXZU]
      exact hxX
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZU] at hx'
    obtain ⟨z, hz, u, hu, rfl⟩ := hx'
    have hzC := hZT hz
    have huC : u ∈ Subgroup.centralizer (T : Set G) := by
      have e : u = z⁻¹ * (z * u) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzC) hxC
    exact Subgroup.mul_mem _ hz (hle ⟨hu, huC⟩)
  refine h.noChar _ (PU.omegaOneCenterOf_le T) (PU.omegaOneCenterOf_ne_bot h.isPGroup h.ne_bot)
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T) ?_
  rw [heq]
  exact le_normalizer_Zq h.le_normalizer

theorem card_map_T_ne_eight
    (hSyl : ∀ S : Subgroup G, IsSylowTwoOf S M →
      Uq M T L ⊓ Subgroup.centralizer (S : Set G) = Uq M T L ⊓ Subgroup.centralizer (M : Set G))
    (hK7 : ¬ Uq M T L ⊓ Subgroup.centralizer (T : Set G) ≤ Zq M L) {S : Subgroup G}
    (hS : IsSylowTwoOf S M) (hTS : T ≤ S) : Nat.card ↥((T.subgroupOf M).map α) ≠ 8 := by
  intro h8
  have hTS' : (T.subgroupOf M).map α ≤ (S.subgroupOf M).map α :=
    Subgroup.map_mono (Subgroup.comap_mono hTS)
  have hS8 : Nat.card ↥((S.subgroupOf M).map α) = 8 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) (card_map_dvd_eight hS.1 hS.2.1))
      (h8 ▸ Subgroup.card_le_of_le hTS')
  have hcS := card_eq_card_pCoreOf_mul h hnat hS.1 hS.2.1 (h.pCore_le.trans hTS)
  have hcT := card_eq_card_pCoreOf_mul h hnat h.le h.isPGroup h.pCore_le
  have hTeq : T = S := Subgroup.eq_of_le_of_card_ge hTS (by rw [hcS, hcT, hS8, h8])
  subst hTeq
  apply hK7
  rw [hSyl T hS]
  intro x hx
  have : x ∈ Uq M T L ⊓ Zq M L := by
    rw [h.Uq_inf_Zq]
    exact ⟨hx.1, Subgroup.centralizer_le h.L_le hx.2⟩
  exact this.2

omit hnat in
theorem commImg_le_W (hA₀2 : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2)
    (hU16 : Nat.card ↥(Uq M T L) = 16)
    (hinv : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S, (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) →
      Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆)
    {S : Subgroup G} (hS : IsSylowTwoOf S M) (hTS : T ≤ S)
    (hW4 : 4 ≤ Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (T : Set G) ⊔ Uq M T L ⊓ Zq M L))
    (hA₀C : Uq M T L ⊓ Zq M L ≤ Subgroup.centralizer (M : Set G)) {b : G} (hbT : b ∈ T)
    (hb2 : b ^ 2 = 1) :
    commImg (uq_comm h) (le_normalizer_Uq h.le_normalizer (h.le hbT)) ≤
      Uq M T L ⊓ Subgroup.centralizer (T : Set G) ⊔ Uq M T L ⊓ Zq M L := by
  refine le_of_card_mul_eq_sixteen (C := Uq M T L ⊓ Subgroup.centralizer ({b} : Set G))
    (A₀ := Uq M T L ⊓ Zq M L) (commImg_le_centralizer _ _ h.isElemAbelian_Uq.2 hb2) ?_ ?_ hW4
    hA₀2 le_sup_right ?_
  · rw [card_commImg_mul, hU16]
  · exact sup_le (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbT)))
      (le_inf inf_le_left (hA₀C.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (h.le hbT)))))
  · intro hI
    exact (hinv S hS b (hTS hbT) (exists_ne_of_commImg_ne_bot h (h.le hbT) hI)).trans
      (commutator_zpowers_le_commImg _ _ hb2)

include hαs in
theorem relIndex_eq_of_sl3Two (hb : critDist (puAmalgam h.le) = 2)
    (hXZU : Xq M = Zq M L ⊔ Uq M T L) (hA₀2 : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2)
    (hSyl : ∀ S : Subgroup G, IsSylowTwoOf S M →
      Uq M T L ⊓ Subgroup.centralizer (S : Set G) = Uq M T L ⊓ Subgroup.centralizer (M : Set G))
    (hinv : ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S, (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) →
      Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆) :
    (pCoreOf 2 M).relIndex T = 4 ∧
      (Uq M T L ⊓ Zq M L).relIndex (⁅Uq M T L, T⁆ ⊔ Uq M T L ⊓ Zq M L) = 2 := by
  have hU16 : Nat.card ↥(Uq M T L) = 16 := by
    rw [natSec_card_eq (NatSec.ofIsSum hnat), hA₀2, Nat.card_zmod]
    norm_num
  obtain ⟨S, hS, hTS⟩ :=
    CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge h.le h.isPGroup
  have hK7 := not_Uq_inf_centralizer_le h hαs hnat hXZU
  have hA₀C : Uq M T L ⊓ Zq M L ≤ Subgroup.centralizer (M : Set G) :=
    le_centralizer_of_card_eq_two (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_Zq h.le_normalizer)) hA₀2
  obtain ⟨ψ, hψ⟩ := exists_critical_inr h hb
  obtain ⟨z', hz'Z, hz'Q⟩ := IsConcreteLE.not_le_iff_exists.mp ((not_le_tImage_iff h hb ψ).mp hψ)
  have hz'T : z' ∈ T := tImage_le ψ _ hz'Z
  have hz'2 : z' ^ 2 = 1 := sq_eq_one_of_mem_tImage h.isElemAbelian_Z0q.2 hz'Z
  have hαz' : α ⟨z', h.le hz'T⟩ ≠ 1 := fun h1 =>
    hz'Q (mem_pCoreOf_of_alpha_eq_one h hnat _ ⟨1, by simpa using hz'2⟩ h1)
  set B := tImage ψ⁻¹ (Z0q M T) with hBdef
  have hB4 := four_le_card_map_tImage_inv h hnat hA₀2 hU16 hinv hS hTS hz'Z hz'Q
  have hBT : (B.subgroupOf M).map α ≤ (T.subgroupOf M).map α :=
    Subgroup.map_mono (Subgroup.comap_mono (tImage_le _ _))
  have hT4 : Nat.card ↥((T.subgroupOf M).map α) = 4 := by
    set n := Nat.card ↥((T.subgroupOf M).map α) with hn
    have h1 : 4 ≤ n := hB4.trans (Subgroup.card_le_of_le hBT)
    have h2 : n ≠ 8 := card_map_T_ne_eight h hnat hSyl hK7 hS hTS
    obtain ⟨c, hc⟩ : n ∣ 8 := card_map_dvd_eight (α := α) h.le h.isPGroup
    have h3 : n ≤ 8 := Nat.le_of_dvd (by norm_num) ⟨c, hc⟩
    interval_cases n <;> omega
  have hBeq : (B.subgroupOf M).map α = (T.subgroupOf M).map α :=
    Subgroup.eq_of_le_of_card_ge hBT (by rw [hT4]; exact hB4)
  refine ⟨?_, ?_⟩
  · have hcT := card_eq_card_pCoreOf_mul h hnat h.le h.isPGroup h.pCore_le (α := α)
    have := Subgroup.relIndex_mul_card (pCoreOf 2 M) T
    rw [inf_eq_left.mpr h.pCore_le, hcT, hT4] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (this.trans (mul_comm _ _))
  · set A₀ := Uq M T L ⊓ Zq M L with hA₀
    set W := Uq M T L ⊓ Subgroup.centralizer (T : Set G) ⊔ A₀ with hW
    have hWU : W ≤ Uq M T L := sup_le inf_le_left inf_le_left
    have hW4 : 4 ≤ Nat.card ↥W := four_le_card_of_lt hU16 hA₀2 le_sup_right
      (fun hle => hK7 ((le_sup_left.trans hle).trans inf_le_right)) hWU
    have hUT : ⁅Uq M T L, T⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro u hu t ht
      have htM := h.le ht
      obtain ⟨⟨b, hbM⟩, hbB, hbt⟩ : ∃ b' ∈ B.subgroupOf M, α b' = α ⟨t, htM⟩ := by
        have : α ⟨t, htM⟩ ∈ (T.subgroupOf M).map α := ⟨⟨t, htM⟩, ht, rfl⟩
        rw [← hBeq] at this
        obtain ⟨b', hb', he⟩ := this
        exact ⟨b', hb', he⟩
      have hbB' : b ∈ B := hbB
      have hbT : b ∈ T := tImage_le _ _ hbB'
      have hb2 : b ^ 2 = 1 := sq_eq_one_of_mem_tImage h.isElemAbelian_Z0q.2 hbB'
      have hq : b⁻¹ * t ∈ pCoreOf 2 M := by
        refine inf_kerG_le h hnat h.isPGroup ⟨T.mul_mem (T.inv_mem hbT) ht,
          mem_kerG.mpr ⟨M.mul_mem (M.inv_mem hbM) htM, ?_⟩⟩
        have e : (⟨b⁻¹ * t, M.mul_mem (M.inv_mem hbM) htM⟩ : ↥M) =
            (⟨b, hbM⟩ : ↥M)⁻¹ * ⟨t, htM⟩ := rfl
        rw [e, map_mul, map_inv, hbt, inv_mul_cancel]
      have hqu : (b⁻¹ * t) * u⁻¹ * (b⁻¹ * t)⁻¹ = u⁻¹ := by
        rw [commute_of_mem_pCoreOf_Xq hq (h.Uq_le_Xq ((Uq M T L).inv_mem hu)),
          mul_inv_cancel_right]
      have hut : ⁅u, t⁆ = ⁅u, b⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc u * t * u⁻¹ * t⁻¹ = u * b * ((b⁻¹ * t) * u⁻¹ * (b⁻¹ * t)⁻¹) * b⁻¹ := by group
          _ = u * b * u⁻¹ * b⁻¹ := by rw [hqu]
      rw [hut]
      exact commImg_le_W h hA₀2 hU16 hinv hS hTS hW4 hA₀C hbT hb2
        (commutator_zpowers_le_commImg _ _ hb2
          (Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers b)))
    have hR : ⁅Uq M T L, T⁆ ⊔ A₀ ≤ W := sup_le hUT le_sup_right
    have hWz : W ≤ Uq M T L ⊓ Subgroup.centralizer ({z'} : Set G) :=
      sup_le (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz'T)))
        (le_inf inf_le_left (hA₀C.trans
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (h.le hz'T)))))
    have hCz := card_inf_centralizer_le_four h hnat hA₀2 hU16 hinv hS (hTS hz'T) hz'2 hαz'
    have hIz : commImg (uq_comm h) (le_normalizer_Uq h.le_normalizer (h.le hz'T)) ≤
        ⁅Uq M T L, T⁆ := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := (mem_commImg _ _).mp hx
      have h2 := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hz'T)
      rwa [commutatorElement_inv, commutatorElement_def] at h2
    have hRlow : 4 ≤ Nat.card ↥(⁅Uq M T L, T⁆ ⊔ A₀) :=
      four_le_card_of_lt hU16 hA₀2 le_sup_right
        (fun hle => not_commImg_le h hnat (h.le hz'T) hαz' (hIz.trans (le_sup_left.trans hle)))
        (hR.trans hWU)
    have hRcard : Nat.card ↥(⁅Uq M T L, T⁆ ⊔ A₀) = 4 :=
      le_antisymm ((Subgroup.card_le_of_le hR).trans ((Subgroup.card_le_of_le hWz).trans hCz))
        hRlow
    have := Subgroup.relIndex_mul_card A₀ (⁅Uq M T L, T⁆ ⊔ A₀)
    rw [inf_eq_left.mpr le_sup_right, hRcard, hA₀2] at this
    omega

end CaseIV

section Final

variable [Finite G] {M T L : Subgroup G}

theorem isSL3TwoNonsplit_of (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2)
    (h4 : IsSL3TwoU M T L) : IsSL3TwoNonsplit M T L := by
  obtain ⟨hXZU, hZU2, ⟨α, hαs, hnat⟩, hSyl, hinv⟩ := h4
  have hA₀2 : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2 := by
    rw [inf_comm]
    exact hZU2
  have hUD : Uq M T L ⊓ Dq M L = Uq M T L ⊓ Zq M L := by rw [h.Uq_inf_Dq, h.Uq_inf_Zq]
  obtain ⟨hTQ, hUT⟩ := relIndex_eq_of_sl3Two h hαs hnat hb hXZU hA₀2 hSyl hinv
  refine ⟨⟨α, hαs, ?_⟩, ?_, hTQ, ?_, hXZU, hSyl⟩
  · rw [hUD]
    exact hnat
  · rw [hUD]
    exact hA₀2
  · rw [hUD]
    exact hUT

end Final

end S36

end CFSG.Quasithin.MS93
