module

public import CFSG.Quasithin.MS93.S38OffIV
public import CFSG.Quasithin.MS93.S38A6
public import CFSG.Quasithin.MS93.S6Bridge

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace OffVI

open A6F Equiv

variable {G : Type} [Group G]

section Crd

variable {U : Subgroup G} (β : ↥U →* Multiplicative (AltHeart 6))

open Classical in
@[expose] noncomputable def crd (u : G) : Fin 4 → ZMod 2 :=
  if hu : u ∈ U then S6B.heartChi (Multiplicative.toAdd (β ⟨u, hu⟩)) else 0

variable {β}

theorem crd_of_mem {u : G} (hu : u ∈ U) :
    crd β u = S6B.heartChi (Multiplicative.toAdd (β ⟨u, hu⟩)) :=
  dite_eq_left hu

theorem crd_mul {u v : G} (hu : u ∈ U) (hv : v ∈ U) : crd β (u * v) = crd β u + crd β v := by
  rw [crd_of_mem (U.mul_mem hu hv), crd_of_mem hu, crd_of_mem hv, ← map_add]
  congr 1
  exact congrArg Multiplicative.toAdd (map_mul β ⟨u, hu⟩ ⟨v, hv⟩)

theorem crd_one : crd β 1 = 0 := by
  rw [crd_of_mem U.one_mem]
  have : β ⟨1, U.one_mem⟩ = 1 := map_one β
  rw [this, toAdd_one, map_zero]

theorem crd_inv {u : G} (hu : u ∈ U) : crd β u⁻¹ = -crd β u := by
  have := crd_mul (β := β) hu (U.inv_mem hu)
  rw [mul_inv_cancel, crd_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem crd_eq_zero_iff {Z : Subgroup G} (hk : β.ker = Z.subgroupOf U) {u : G} (hu : u ∈ U) :
    crd β u = 0 ↔ u ∈ Z := by
  rw [crd_of_mem hu, ← map_zero S6B.heartChi]
  constructor
  · intro h0
    have h1 := S6B.heartChi_bijective.1 h0
    have h2 : β ⟨u, hu⟩ = 1 := by
      rw [← ofAdd_toAdd (β ⟨u, hu⟩), h1, ofAdd_zero]
    have h3 : (⟨u, hu⟩ : ↥U) ∈ β.ker := h2
    rw [hk, Subgroup.mem_subgroupOf] at h3
    exact h3
  · intro hz
    have h3 : (⟨u, hu⟩ : ↥U) ∈ β.ker := by
      rw [hk, Subgroup.mem_subgroupOf]
      exact hz
    rw [MonoidHom.mem_ker] at h3
    rw [h3, toAdd_one]

theorem exists_crd_eq (hs : Function.Surjective β) (w : Fin 4 → ZMod 2) :
    ∃ u ∈ U, crd β u = w := by
  obtain ⟨y, hy⟩ := S6B.heartChi_bijective.2 w
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd y)
  refine ⟨u, u.2, ?_⟩
  rw [crd_of_mem u.2, Subtype.coe_eta, hu, toAdd_ofAdd, hy]

theorem crd_conj {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 6)}
    (hU : L ≤ Subgroup.normalizer (U : Set G))
    (he : ∀ (a : ↥L) (u v : ↥U), (v : G) = a * u * a⁻¹ →
      ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 6 (α a : Perm (Fin 6)) x) : AltHeart 6) =
          Multiplicative.toAdd (β v))
    (a : ↥L) {u : G} (hu : u ∈ U) :
    crd β ((a : G) * u * (a : G)⁻¹) = actChi (α a : Perm (Fin 6)) (crd β u) := by
  have hv : (a : G) * u * (a : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hU a.2) u).mp hu
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨u, hu⟩))
  have h1 := he a ⟨u, hu⟩ ⟨_, hv⟩ rfl x hx
  rw [crd_of_mem hv, crd_of_mem hu, ← h1, ← hx, S6B.heartChi_mk, S6B.heartChi_mk]
  exact chi_perm _ (S6B.sum_eq_zero_of_mem x.2)

end Crd

structure A6Data (M T L : Subgroup G) where
  α₀ : ↥L →* alternatingGroup (Fin 6)
  β₀ : ↥(Uq M T L) →* Multiplicative (AltHeart 6)
  surj : Function.Surjective β₀
  ker : β₀.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L)
  equiv : ∀ (a : ↥L) (u v : ↥(Uq M T L)), (v : G) = a * u * a⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β₀ u) →
      (QuotientAddGroup.mk (permWeight 6 (α₀ a : Perm (Fin 6)) x) : AltHeart 6) =
        Multiplicative.toAdd (β₀ v)
  act : ∀ m ∈ M, ∃ l ∈ L, ∀ u ∈ Uq M T L,
    (m * u * m⁻¹)⁻¹ * (l * u * l⁻¹) ∈ Uq M T L ⊓ Zq M L

variable {M T L : Subgroup G}

section Nonempty

variable [Finite G]

theorem PUHyp.nonempty_a6Data (h : PUHyp M T L)
    (hX : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) (h2 : ¬ IsSp4U M T L) :
    Nonempty (A6Data M T L) := by
  rcases hX with ⟨-, N₀, hA⟩ | ⟨hk, -⟩
  swap
  · omega
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hMZ : M ≤ Subgroup.normalizer ((Uq M T L ⊓ Zq M L : Subgroup G) : Set G) :=
    le_normalizer_inf hMU (le_normalizer_Zq h.le_normalizer)
  obtain ⟨α, hαnat, hcase⟩ :=
    sp4Two_of_altNaturalSection h.L_le h.le_normalizer hMU hMZ inf_le_left hA
  rcases hcase with hsurj | hall
  · refine absurd (Or.inr ⟨α, hsurj, ?_⟩) h2
    rw [← h.Uq_inf_Zq]
    exact hαnat
  obtain ⟨-, α₀, -, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hA
  refine ⟨⟨α₀, β₀, hβ₀s, hβ₀k, hβ₀e, fun m hm => ?_⟩⟩
  obtain ⟨l, hl⟩ := hall ⟨m, hm⟩
  refine ⟨l, l.2, fun u hu => ?_⟩
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hαnat
  have hmu : m * u * m⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.mp (hMU hm) u).mp hu
  have hlu : (l : G) * u * (l : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.mp (hMU (h.L_le l.2)) u).mp hu
  have h1 := hβe ⟨m, hm⟩ ⟨u, hu⟩ ⟨_, hmu⟩ rfl 0
  have h2' := hβe ⟨l, h.L_le l.2⟩ ⟨u, hu⟩ ⟨_, hlu⟩ rfl 0
  rw [hl] at h1
  have heq : β ⟨_, hmu⟩ = β ⟨_, hlu⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    exact h1.trans h2'.symm
  have hk : (⟨_, hmu⟩ : ↥(Uq M T L))⁻¹ * ⟨_, hlu⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq]
    exact inv_mul_cancel _
  rw [hβk, Subgroup.mem_subgroupOf] at hk
  exact hk

end Nonempty

section HomOf

variable {M : Subgroup G} {H : Type} [Group H] (r : ↥M →* H)

open Classical in
@[expose] noncomputable def homOf (t : G) : H := if ht : t ∈ M then r ⟨t, ht⟩ else 1

variable {r}

theorem homOf_of_mem {t : G} (ht : t ∈ M) : homOf r t = r ⟨t, ht⟩ := dite_eq_left ht

theorem homOf_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    homOf r (x * y) = homOf r x * homOf r y := by
  rw [homOf_of_mem (M.mul_mem hx hy), homOf_of_mem hx, homOf_of_mem hy, ← map_mul]
  rfl

theorem homOf_inv {x : G} (hx : x ∈ M) : homOf r x⁻¹ = (homOf r x)⁻¹ := by
  rw [homOf_of_mem (M.inv_mem hx), homOf_of_mem hx, ← map_inv]
  rfl

theorem homOf_one : homOf r 1 = 1 := by
  rw [homOf_of_mem M.one_mem, ← map_one r]
  rfl

theorem homOf_pow {x : G} (hx : x ∈ M) (n : ℕ) : homOf r (x ^ n) = homOf r x ^ n := by
  rw [homOf_of_mem (M.pow_mem hx n), homOf_of_mem hx, ← map_pow]
  rfl

theorem homOf_mem_map {T : Subgroup G} (hTM : T ≤ M) {t : G} (ht : t ∈ T) :
    homOf r t ∈ (T.subgroupOf M).map r :=
  ⟨⟨t, hTM ht⟩, ht, (homOf_of_mem (hTM ht)).symm⟩

theorem exists_of_mem_map' {T : Subgroup G} {b : H} (hb : b ∈ (T.subgroupOf M).map r) :
    ∃ t ∈ T, homOf r t = b := by
  obtain ⟨⟨t, htM⟩, ht, rfl⟩ := hb
  exact ⟨t, ht, homOf_of_mem htM⟩

theorem isPGroup_map' {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T) :
    IsPGroup 2 ((T.subgroupOf M).map r) :=
  (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).map r

theorem homOf_sq {F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 2 F) {x : G} (hx : x ∈ F) :
    homOf r x * homOf r x = 1 := by
  rw [← homOf_mul (hFM hx) (hFM hx), ← pow_two, hF.2 x hx, homOf_one]

theorem homOf_comm {F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 2 F) {x y : G}
    (hx : x ∈ F) (hy : y ∈ F) : homOf r x * homOf r y = homOf r y * homOf r x := by
  rw [← homOf_mul (hFM hx) (hFM hy), ← homOf_mul (hFM hy) (hFM hx),
    show x * y = y * x from congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)]

end HomOf

section Psi

variable [Finite G] (D : A6Data M T L)

@[expose] noncomputable def lOf (m : ↥M) : ↥L :=
  ⟨Classical.choose (D.act m m.2), (Classical.choose_spec (D.act m m.2)).1⟩

omit [Finite G] in
theorem lOf_spec (m : ↥M) {u : G} (hu : u ∈ Uq M T L) :
    ((m : G) * u * (m : G)⁻¹)⁻¹ * ((lOf D m : G) * u * (lOf D m : G)⁻¹) ∈ Uq M T L ⊓ Zq M L :=
  (Classical.choose_spec (D.act m m.2)).2 u hu

@[expose] noncomputable def psiFun (m : ↥M) : Perm (Fin 6) := (D.α₀ (lOf D m) : Perm (Fin 6))

variable {D}

theorem psiFun_spec (h : PUHyp M T L) (m : ↥M) {u : G} (hu : u ∈ Uq M T L) :
    crd D.β₀ ((m : G) * u * (m : G)⁻¹) = actChi (psiFun D m) (crd D.β₀ u) := by
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hmu : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.mp (hMU m.2) u).mp hu
  have hlu : (lOf D m : G) * u * (lOf D m : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.mp (hMU (h.L_le (lOf D m).2)) u).mp hu
  have h0 := (crd_eq_zero_iff D.ker ((Uq M T L).mul_mem ((Uq M T L).inv_mem hmu) hlu)).mpr
    (lOf_spec D m hu)
  rw [crd_mul ((Uq M T L).inv_mem hmu) hlu, crd_inv hmu] at h0
  rw [neg_add_eq_zero.mp h0]
  exact crd_conj (h.L_le.trans hMU) D.equiv (lOf D m) hu

omit [Finite G] in
theorem eq_of_crd {σ τ : Perm (Fin 6)}
    (hst : ∀ u ∈ Uq M T L, actChi σ (crd D.β₀ u) = actChi τ (crd D.β₀ u)) : σ = τ :=
  eq_of_actChi fun w => by
    obtain ⟨u, hu, rfl⟩ := exists_crd_eq D.surj w
    exact hst u hu

variable (D)

@[expose] noncomputable def psi (h : PUHyp M T L) : ↥M →* Perm (Fin 6) :=
  MonoidHom.mk' (psiFun D) fun a b => eq_of_crd (D := D) fun u hu => by
    have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
    have hbu : (b : G) * u * (b : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.mp (hMU b.2) u).mp hu
    rw [← psiFun_spec h (a * b) hu, actChi_mul, ← psiFun_spec h b hu, ← psiFun_spec h a hbu]
    congr 1
    simp only [Subgroup.coe_mul]
    group

variable {D}

theorem psi_spec (h : PUHyp M T L) {m : G} (hm : m ∈ M) {u : G} (hu : u ∈ Uq M T L) :
    crd D.β₀ (m * u * m⁻¹) = actChi (homOf (psi D h) m) (crd D.β₀ u) := by
  rw [homOf_of_mem hm]
  exact psiFun_spec h ⟨m, hm⟩ hu

theorem sign_psi (h : PUHyp M T L) {m : G} (hm : m ∈ M) : Perm.sign (homOf (psi D h) m) = 1 := by
  rw [homOf_of_mem hm]
  exact Perm.mem_alternatingGroup.mp (D.α₀ (lOf D ⟨m, hm⟩)).2

theorem psi_eq_one_iff (h : PUHyp M T L) {t : G} (htT : t ∈ T) :
    homOf (psi D h) t = 1 ↔ t ∈ pCoreOf 2 M := by
  have htM := h.le htT
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  constructor
  · intro h1
    refine h.mem_pCoreOf_of_comm_Uq htT fun u hu => ?_
    have htu : t * u * t⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.mp (hMU htM) u).mp hu
    have hc : ⁅u, t⁆ ∈ Uq M T L ⊓ Zq M L := by
      have e : ⁅u, t⁆ = u * (t * u * t⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e, ← crd_eq_zero_iff D.ker ((Uq M T L).mul_mem hu ((Uq M T L).inv_mem htu)),
        crd_mul hu ((Uq M T L).inv_mem htu), crd_inv htu, psi_spec h htM hu, h1, actChi_one]
      exact add_neg_cancel _
    exact hc.2.2
  · intro hq
    refine eq_of_crd (D := D) fun u hu => ?_
    rw [← psi_spec h htM hu, actChi_one, OffIV.commute_of_mem_pCoreOf hq (h.Uq_le_Xq hu),
      mul_inv_cancel_right]

end Psi

section Fix

theorem phi_zero : B5FinSp.phi 0 = 0 := by decide

theorem actChi_zero (σ : Perm (Fin 6)) : actChi σ 0 = 0 := by
  show B5FinSp.chi (fun i => B5FinSp.phi 0 (σ⁻¹ i)) = 0
  rw [phi_zero]
  exact B5FinSp.chi_const 0

theorem mul_self_eq_one (a : Multiplicative (Fin 4 → ZMod 2)) : a * a = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  exact CharTwo.add_self_eq_zero (Multiplicative.toAdd a i)

@[expose] def fixSub (σ : Perm (Fin 6)) : Subgroup (Multiplicative (Fin 4 → ZMod 2)) where
  carrier := {w | actChi σ (Multiplicative.toAdd w) = Multiplicative.toAdd w}
  mul_mem' {a b} ha hb := by
    show actChi σ (Multiplicative.toAdd a + Multiplicative.toAdd b) =
      Multiplicative.toAdd a + Multiplicative.toAdd b
    rw [actChi_add, ha, hb]
  one_mem' := actChi_zero σ
  inv_mem' {a} ha := by
    show actChi σ (Multiplicative.toAdd a⁻¹) = Multiplicative.toAdd a⁻¹
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq_one a)]
    exact ha

theorem mem_fixSub {σ : Perm (Fin 6)} {w : Multiplicative (Fin 4 → ZMod 2)} :
    w ∈ fixSub σ ↔ actChi σ (Multiplicative.toAdd w) = Multiplicative.toAdd w :=
  Iff.rfl

theorem card_fixSub (σ : Perm (Fin 6)) :
    Nat.card (fixSub σ) = (Finset.univ.filter fun w => actChi σ w = w).card := by
  have e : Nat.card (fixSub σ) = Nat.card {w : Fin 4 → ZMod 2 // actChi σ w = w} :=
    Nat.card_congr ⟨fun w => ⟨Multiplicative.toAdd w.1, w.2⟩,
      fun w => ⟨Multiplicative.ofAdd w.1, w.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_fixSub_inf (σ τ : Perm (Fin 6)) :
    Nat.card ↥(fixSub σ ⊓ fixSub τ) =
      (Finset.univ.filter fun w => actChi σ w = w ∧ actChi τ w = w).card := by
  have e : Nat.card ↥(fixSub σ ⊓ fixSub τ) =
      Nat.card {w : Fin 4 → ZMod 2 // actChi σ w = w ∧ actChi τ w = w} :=
    Nat.card_congr ⟨fun w => ⟨Multiplicative.toAdd w.1, w.2⟩,
      fun w => ⟨Multiplicative.ofAdd w.1, w.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_mul_index_fix (K : Subgroup (Multiplicative (Fin 4 → ZMod 2))) :
    Nat.card K * K.index = 16 := by
  rw [Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  rfl

variable {U : Subgroup G} {β : ↥U →* Multiplicative (AltHeart 6)}

@[expose] noncomputable def gam (β : ↥U →* Multiplicative (AltHeart 6)) :
    ↥U →* Multiplicative (Fin 4 → ZMod 2) where
  toFun u := Multiplicative.ofAdd (crd β u)
  map_one' := by
    show Multiplicative.ofAdd (crd β (1 : G)) = 1
    rw [crd_one, ofAdd_zero]
  map_mul' u v := by
    show Multiplicative.ofAdd (crd β ((u : G) * v)) = Multiplicative.ofAdd (crd β u) *
      Multiplicative.ofAdd (crd β v)
    rw [crd_mul u.2 v.2, ofAdd_add]

theorem gam_surjective (hs : Function.Surjective β) : Function.Surjective (gam β) := by
  intro w
  obtain ⟨u, hu, hw⟩ := exists_crd_eq hs (Multiplicative.toAdd w)
  exact ⟨⟨u, hu⟩, by show Multiplicative.ofAdd (crd β u) = w; rw [hw, ofAdd_toAdd]⟩

@[expose] noncomputable def preU (β : ↥U →* Multiplicative (AltHeart 6))
    (K : Subgroup (Multiplicative (Fin 4 → ZMod 2))) : Subgroup G :=
  (K.comap (gam β)).map U.subtype

theorem mem_preU {K : Subgroup (Multiplicative (Fin 4 → ZMod 2))} {u : G} :
    u ∈ preU β K ↔ u ∈ U ∧ Multiplicative.ofAdd (crd β u) ∈ K := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hu, hK⟩
    exact ⟨⟨u, hu⟩, hK, rfl⟩

theorem relIndex_preU (hs : Function.Surjective β)
    (K : Subgroup (Multiplicative (Fin 4 → ZMod 2))) :
    (preU β K).relIndex U * Nat.card K = 16 := by
  have e : (preU β K).subgroupOf U = K.comap (gam β) :=
    Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective K (gam_surjective hs), mul_comm]
  exact card_mul_index_fix K

end Fix

section Off

variable [Finite G]

theorem exists_of_isXOff (h : PUHyp M T L) (D : A6Data M T L) {F : Subgroup G}
    (hF : IsXOff M T F) :
    ∃ f₁ ∈ F, ∃ f₂ ∈ F, homOf (psi D h) f₁ ≠ 1 ∧ homOf (psi D h) f₂ ≠ 1 ∧
      homOf (psi D h) f₁ ≠ homOf (psi D h) f₂ ∧
      (∀ w, actChi (homOf (psi D h) f₁) w = w ↔ actChi (homOf (psi D h) f₂) w = w) ∧
      (∀ x ∈ F, homOf (psi D h) x = 1 ∨ homOf (psi D h) x = homOf (psi D h) f₁ ∨
        homOf (psi D h) x = homOf (psi D h) f₂ ∨
        homOf (psi D h) x = homOf (psi D h) f₁ * homOf (psi D h) f₂) ∧
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F ∧
      (pCoreOf 2 M).relIndex F = 4 := by
  obtain ⟨hFT, hFea, hFQ, hoff⟩ := hF
  have hFM : F ≤ M := hFT.trans h.le
  set r := psi D h with hr
  have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K => Subgroup.index_ne_zero_of_finite
  have hP := isPGroup_map' (r := r) h.le h.isPGroup
  have hPA : ∀ x ∈ (T.subgroupOf M).map r, Perm.sign x = 1 := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := exists_of_mem_map' hx
    exact sign_psi h (h.le ht)
  have hm : ∀ {x : G}, x ∈ F → homOf r x ∈ (T.subgroupOf M).map r := fun hx =>
    homOf_mem_map h.le (hFT hx)
  let ρF : ↥F →* Perm (Fin 6) := r.comp (Subgroup.inclusion hFM)
  have hρF : ∀ x : ↥F, ρF x = homOf r x := fun x => (homOf_of_mem (r := r) (hFM x.2)).symm
  have hidx : (pCoreOf 2 M).relIndex F = Nat.card ρF.range := by
    rw [Subgroup.relIndex, ← Subgroup.index_ker]
    congr 1
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hρF, psi_eq_one_iff h (hFT x.2)]
  obtain ⟨f₁, hf₁F, hf₁Q⟩ := Set.not_subset.mp fun hs => hFQ hs
  have hn₁ : homOf r f₁ ≠ 1 := fun he => hf₁Q ((psi_eq_one_iff h (hFT hf₁F)).mp he)
  have hs₁ := homOf_sq (r := r) hFM hFea hf₁F
  set C := Subgroup.centralizer (F : Set G) ⊓ Uq M T L with hC
  have hCK : ∀ f ∈ F, C ≤ preU D.β₀ (fixSub (homOf r f)) := by
    intro f hf u hu
    obtain ⟨huC, huU⟩ := Subgroup.mem_inf.mp hu
    refine mem_preU.mpr ⟨huU, ?_⟩
    have hfu : f * u * f⁻¹ = u := by
      rw [Subgroup.mem_centralizer_iff.mp huC f hf, mul_inv_cancel_right]
    have := psi_spec (D := D) h (hFM hf) huU
    rw [hfu] at this
    exact this.symm
  have hUF : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) ≤
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) :=
    Subgroup.relIndex_le_of_le_right h.Uq_le_Xq (hne _ _)
  have hCU : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) = C.relIndex (Uq M T L) :=
    (Subgroup.inf_relIndex_right _ _).symm
  have h4 : 4 ≤ (Subgroup.centralizer (F : Set G)).relIndex (Xq M) := by
    have h1 := relIndex_preU D.surj (fixSub (homOf r f₁))
    rw [card_fixSub, card_fix_of_mem hP hPA (hm hf₁F) hs₁ hn₁] at h1
    have h2 := Subgroup.relIndex_le_of_le_left (hCK f₁ hf₁F) (hne C (Uq M T L))
    omega
  rw [hidx] at hoff
  obtain ⟨f₂, hf₂F, hn₂, hn₂₁⟩ : ∃ f ∈ F, homOf r f ≠ 1 ∧ homOf r f ≠ homOf r f₁ := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hle : ρF.range ≤ Subgroup.zpowers (homOf r f₁) := by
      rintro _ ⟨x, rfl⟩
      rw [hρF]
      by_cases hx1 : homOf r x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · rw [hall x x.2 hx1]
        exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hs₁) hn₁] at this
    omega
  have hs₂ := homOf_sq (r := r) hFM hFea hf₂F
  have hfour : ∀ x ∈ F, homOf r x = 1 ∨ homOf r x = homOf r f₁ ∨ homOf r x = homOf r f₂ ∨
      homOf r x = homOf r f₁ * homOf r f₂ := fun x hx =>
    mem_of_comm_four hP hPA (hm hf₁F) (hm hf₂F) (hm hx) hs₁ hs₂ hn₁ hn₂ (Ne.symm hn₂₁)
      (homOf_comm hFM hFea hf₁F hf₂F) (homOf_comm hFM hFea hx hf₁F) (homOf_comm hFM hFea hx hf₂F)
  have hle4 : Nat.card ρF.range ≤ 4 := by
    have hsub : (ρF.range : Set (Perm (Fin 6))) ⊆
        {1, homOf r f₁, homOf r f₂, homOf r f₁ * homOf r f₂} := by
      rintro _ ⟨x, rfl⟩
      rw [hρF]
      rcases hfour x x.2 with e | e | e | e <;> rw [e] <;> simp
    calc Nat.card ρF.range = Nat.card ↥(ρF.range : Set (Perm (Fin 6))) := rfl
      _ ≤ Nat.card ↥({1, homOf r f₁, homOf r f₂, homOf r f₁ * homOf r f₂} :
          Set (Perm (Fin 6))) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 4 := by
          rw [Nat.card_coe_set_eq]
          refine (Set.ncard_insert_le _ _).trans ?_
          refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
          refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
          rw [Set.ncard_singleton]
  have hfix : ∀ w, actChi (homOf r f₁) w = w ↔ actChi (homOf r f₂) w = w := by
    by_contra hw
    push Not at hw
    have hcard := card_fix_two_of_mem hP hPA (hm hf₁F) (hm hf₂F) hs₁ hs₂ hn₁ hn₂
      (homOf_comm hFM hFea hf₁F hf₂F) (by
        obtain ⟨w, hw⟩ := hw
        exact ⟨w, fun h' => by
          rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h2 (h'.mp h1)
          · exact h1 (h'.mpr h2)⟩)
    have h1 := relIndex_preU D.surj (fixSub (homOf r f₁) ⊓ fixSub (homOf r f₂))
    rw [card_fixSub_inf] at h1
    have hCK2 : C ≤ preU D.β₀ (fixSub (homOf r f₁) ⊓ fixSub (homOf r f₂)) := fun u hu =>
      mem_preU.mpr ⟨(mem_preU.mp (hCK f₁ hf₁F hu)).1, Subgroup.mem_inf.mpr
        ⟨(mem_preU.mp (hCK f₁ hf₁F hu)).2, (mem_preU.mp (hCK f₂ hf₂F hu)).2⟩⟩
    have h2 := Subgroup.relIndex_le_of_le_left hCK2 (hne C (Uq M T L))
    have hpos : 0 < (Finset.univ.filter fun w =>
        actChi (homOf r f₁) w = w ∧ actChi (homOf r f₂) w = w).card :=
      Finset.card_pos.mpr ⟨0, by simp [actChi_zero]⟩
    have h8 : 8 ≤ (preU D.β₀ (fixSub (homOf r f₁) ⊓ fixSub (homOf r f₂))).relIndex
        (Uq M T L) := by
      by_contra hlt
      push Not at hlt
      have : (preU D.β₀ (fixSub (homOf r f₁) ⊓ fixSub (homOf r f₂))).relIndex (Uq M T L) *
          (Finset.univ.filter fun w =>
            actChi (homOf r f₁) w = w ∧ actChi (homOf r f₂) w = w).card ≤ 7 * 2 :=
        Nat.mul_le_mul (by omega) hcard
      omega
    omega
  refine ⟨f₁, hf₁F, f₂, hf₂F, hn₁, hn₂, Ne.symm hn₂₁, hfix, hfour, ?_, ?_⟩
  · rw [hidx]
    omega
  · rw [hidx]
    omega

theorem mem_sup_of_homOf_eq (h : PUHyp M T L) (D : A6Data M T L) {F : Subgroup G} (hFT : F ≤ T)
    {x y : G} (hx : x ∈ T) (hy : y ∈ F) (he : homOf (psi D h) x = homOf (psi D h) y) :
    x ∈ F ⊔ pCoreOf 2 M := by
  have hyT := hFT hy
  have hq : y⁻¹ * x ∈ pCoreOf 2 M := by
    refine (psi_eq_one_iff (D := D) h (T.mul_mem (T.inv_mem hyT) hx)).mp ?_
    rw [homOf_mul (M.inv_mem (h.le hyT)) (h.le hx), homOf_inv (h.le hyT), he, inv_mul_cancel]
  have e : x = y * (y⁻¹ * x) := by group
  rw [e]
  exact (F ⊔ pCoreOf 2 M).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)

theorem le_sup_of_isXOff (h : PUHyp M T L) (D : A6Data M T L) {F₁ F₂ : Subgroup G}
    (hF₁ : IsXOff M T F₁) (hF₂ : IsXOff M T F₂) : F₂ ≤ F₁ ⊔ pCoreOf 2 M := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hn₁, hn₂, hn₁₂, hfix, -, -, -⟩ := exists_of_isXOff h D hF₁
  obtain ⟨g₁, hg₁, g₂, hg₂, hn₁', hn₂', hn₁₂', hfix', hfour', -, -⟩ := exists_of_isXOff h D hF₂
  set r := psi D h with hr
  have hM₁ : F₁ ≤ M := hF₁.1.trans h.le
  have hM₂ : F₂ ≤ M := hF₂.1.trans h.le
  have hP := isPGroup_map' (r := r) h.le h.isPGroup
  have hPA : ∀ x ∈ (T.subgroupOf M).map r, Perm.sign x = 1 := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := exists_of_mem_map' hx
    exact sign_psi h (h.le ht)
  have hm : ∀ {x : G} {F : Subgroup G}, IsXOff M T F → x ∈ F →
      homOf r x ∈ (T.subgroupOf M).map r := fun hF hx => homOf_mem_map h.le (hF.1 hx)
  set E := (F₁.subgroupOf M).map r
  have hE : ∀ x ∈ F₁, homOf r x ∈ E := fun x hx => homOf_mem_map hM₁ hx
  have hgE : ∀ {g g' : G}, g ∈ F₂ → g' ∈ F₂ → homOf r g ≠ 1 → homOf r g' ≠ 1 →
      homOf r g ≠ homOf r g' →
      (∀ w, actChi (homOf r g) w = w ↔ actChi (homOf r g') w = w) →
      homOf r g ∈ E := fun {g g'} hg hg' hn hn' hgg' hgf => by
    rcases eq_of_fix_four hP hPA (hm hF₁ hf₁) (hm hF₁ hf₂) (hm hF₂ hg) (hm hF₂ hg')
        (homOf_sq hM₁ hF₁.2.1 hf₁) (homOf_sq hM₁ hF₁.2.1 hf₂) (homOf_sq hM₂ hF₂.2.1 hg)
        (homOf_sq hM₂ hF₂.2.1 hg') hn₁ hn₂ hn hn' hn₁₂ (homOf_comm hM₁ hF₁.2.1 hf₁ hf₂) hfix
        hgg' (homOf_comm hM₂ hF₂.2.1 hg hg') hgf with e | e | e
    · rw [e]
      exact hE _ hf₁
    · rw [e]
      exact hE _ hf₂
    · rw [e]
      exact E.mul_mem (hE _ hf₁) (hE _ hf₂)
  have hg₁E := hgE hg₁ hg₂ hn₁' hn₂' hn₁₂' hfix'
  have hg₂E := hgE hg₂ hg₁ hn₂' hn₁' (Ne.symm hn₁₂') fun w => (hfix' w).symm
  intro x hx
  have hxE : homOf r x ∈ E := by
    rcases hfour' x hx with e | e | e | e <;> rw [e]
    · exact E.one_mem
    · exact hg₁E
    · exact hg₂E
    · exact E.mul_mem hg₁E hg₂E
  obtain ⟨y, hy, hxy⟩ := exists_of_mem_map' hxE
  exact mem_sup_of_homOf_eq h D hF₁.1 (hF₂.1 hx) hy hxy.symm

theorem mem_sup_of_mem_centralizer (h : PUHyp M T L) (D : A6Data M T L) {F : Subgroup G}
    (hF : IsXOff M T F) {y : G} (hyT : y ∈ T) (hyC : y ∈ Subgroup.centralizer (F : Set G)) :
    y ∈ F ⊔ pCoreOf 2 M := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hn₁, hn₂, hn₁₂, -, -, -, -⟩ := exists_of_isXOff h D hF
  set r := psi D h with hr
  have hFM : F ≤ M := hF.1.trans h.le
  have hP := isPGroup_map' (r := r) h.le h.isPGroup
  have hPA : ∀ x ∈ (T.subgroupOf M).map r, Perm.sign x = 1 := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := exists_of_mem_map' hx
    exact sign_psi h (h.le ht)
  have hy : ∀ {f : G}, f ∈ F → homOf r y * homOf r f = homOf r f * homOf r y := fun {f} hf => by
    rw [← homOf_mul (h.le hyT) (hFM hf), ← homOf_mul (hFM hf) (h.le hyT),
      Subgroup.mem_centralizer_iff.mp hyC f hf]
  rcases mem_of_comm_four hP hPA (homOf_mem_map h.le (hF.1 hf₁)) (homOf_mem_map h.le (hF.1 hf₂))
      (homOf_mem_map h.le hyT) (homOf_sq hFM hF.2.1 hf₁) (homOf_sq hFM hF.2.1 hf₂) hn₁ hn₂ hn₁₂
      (homOf_comm hFM hF.2.1 hf₁ hf₂) (hy hf₁) (hy hf₂) with e | e | e | e
  · exact mem_sup_of_homOf_eq h D hF.1 hyT F.one_mem (e.trans homOf_one.symm)
  · exact mem_sup_of_homOf_eq h D hF.1 hyT hf₁ e
  · exact mem_sup_of_homOf_eq h D hF.1 hyT hf₂ e
  · exact mem_sup_of_homOf_eq h D hF.1 hyT (F.mul_mem hf₁ hf₂)
      (e.trans (homOf_mul (hFM hf₁) (hFM hf₂)).symm)

end Off

end OffVI

open OffVI in
theorem PUHyp.xOffData_of_isAltSix {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} (h : PUHyp M T L)
    (hX : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) (h2 : ¬ IsSp4U M T L) :
    XOffData M T := by
  obtain ⟨D⟩ := PUHyp.nonempty_a6Data h hX h2
  refine XOffData.of_cent h h.centralizer_Z0q (fun F₁ F₂ h₁ h₂ => ?_) (fun F hF => ?_)
    (fun F hF y hy hyC => mem_sup_of_mem_centralizer h D hF hy hyC)
  · exact le_antisymm (sup_le (le_sup_of_isXOff h D h₂ h₁) le_sup_right)
      (sup_le (le_sup_of_isXOff h D h₁ h₂) le_sup_right)
  · obtain ⟨-, -, -, -, -, -, -, -, -, heq, -⟩ := exists_of_isXOff h D hF
    exact heq

open OffVI in
theorem PUHyp.xOffCent_of_isAltSix {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} (h : PUHyp M T L)
    (hX : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) (h2 : ¬ IsSp4U M T L) :
    (∀ F : Subgroup G, IsXOff M T F → T ⊓ Subgroup.centralizer (F : Set G) ≤ F ⊔ pCoreOf 2 M) ∧
      ∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F = 4 := by
  obtain ⟨D⟩ := PUHyp.nonempty_a6Data h hX h2
  refine ⟨fun F hF y hy => mem_sup_of_mem_centralizer h D hF hy.1 hy.2, fun F hF => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h4⟩ := exists_of_isXOff h D hF
  exact h4

end CFSG.Quasithin.MS93
