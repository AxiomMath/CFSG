module

public import CFSG.Quasithin.Background.F918V3QB2
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Background.F918Z1Quot
public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.F918V3QB1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

section QuotApi

variable {Y : Type} [CommGroup Y]

@[expose] noncomputable def d3q_quotHomOn (Z : Subgroup Y) {H : Subgroup (MulAut Y)}
    (hH : H ≤ stabSub Z) : ↥H →* MulAut (Y ⧸ Z) :=
  (quotHom Z).comp (Subgroup.inclusion hH)

theorem d3q_autQuot_eq_map {K H : Subgroup (MulAut Y)} {Z : Subgroup Y} (hKH : K ≤ H)
    (hH : H ≤ stabSub Z) : autQuot K Z = (K.subgroupOf H).map (d3q_quotHomOn Z hH) :=
  CFSG.Quasithin.v3qb_autQuot_eq_map hKH hH

theorem d3q_mem_stabSub_map {Z U : Subgroup Y} {g : MulAut Y} (hgZ : g ∈ stabSub Z)
    (hgU : g ∈ stabSub U) :
    quotHom Z ⟨g, hgZ⟩ ∈ stabSub (U.map (QuotientGroup.mk' Z)) :=
  CFSG.Quasithin.v3qb_mem_stabSub_map hgZ hgU

@[expose] noncomputable def d3q_resQuot (Z U : Subgroup Y) :
    ↥(stabSub Z ⊓ stabSub U) →* MulAut ↥(U.map (QuotientGroup.mk' Z)) :=
  (resHom (U.map (QuotientGroup.mk' Z))).comp
    (((quotHom Z).comp (Subgroup.inclusion inf_le_left)).codRestrict
      (stabSub (U.map (QuotientGroup.mk' Z))) (fun g => d3q_mem_stabSub_map g.2.1 g.2.2))

theorem d3q_resQuot_eq_one_iff {Z U : Subgroup Y} (g : ↥(stabSub Z ⊓ stabSub U)) :
    d3q_resQuot Z U g = 1 ↔ ∀ u ∈ U, (g : MulAut Y) u * u⁻¹ ∈ Z :=
  CFSG.Quasithin.v3qb_resQuot_eq_one_iff g

end QuotApi

section AbstractKq

variable {P Q H : Type} [CommGroup P] [CommGroup Q] [Group H] [Finite P] [Finite Q] [Finite H]

theorem d3q_kq_range_le (μ : P →* Q) (hμ : Function.Surjective μ) (Θ₀ : H →* MulAut P)
    (Θ : H →* MulAut Q) (hint : ∀ (h : H) (p : P), μ (Θ₀ h p) = Θ h (μ p))
    (hker : Θ.ker ≤ Θ₀.ker) (k : ℕ) : kq Θ.range k ≤ kq Θ₀.range k := by
  by_cases htop : kq Θ₀.range k = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hr]
  obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp (le_of_eq hr.symm)
  have hker' : Θ₀.ker ≤ Θ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh ⊢
    refine MulEquiv.ext fun q => ?_
    obtain ⟨p, rfl⟩ := hμ q
    rw [← hint, hh]
    rfl
  have hker_eq : Θ.ker = Θ₀.ker := le_antisymm hker hker'
  have hΘeq : ∀ x y : H, Θ₀ x = Θ₀ y → Θ x = Θ y := by
    intro x y hxy
    have h1 : x⁻¹ * y ∈ Θ₀.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := hker' h1
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
    exact inv_mul_eq_one.mp h2
  set Ã : Subgroup H := A.comap Θ₀ with hÃ
  set B : Subgroup (MulAut Q) := Ã.map Θ with hB
  have hAÃ : Ã.map Θ₀ = A := by
    rw [hÃ, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hA.1
  have hBne : B ≠ ⊥ := by
    intro hB0
    apply hA.2.1
    rw [← hAÃ]
    rw [hB, Subgroup.map_eq_bot_iff] at hB0
    exact (Subgroup.map_eq_bot_iff _).mpr (hB0.trans hker)
  have hBel : IsElemAbelian2 B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      apply hΘeq
      rw [map_mul, map_mul]
      exact hA.2.2.1 _ (Subgroup.mem_comap.mp hx) _ (Subgroup.mem_comap.mp hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, ← map_one Θ]
      apply hΘeq
      rw [map_pow, map_one]
      exact hA.2.2.2 _ (Subgroup.mem_comap.mp hx)
  have hcomm : ∀ n : ℕ, commIter ⊤ B n ≤ (commIter ⊤ A n).map μ := by
    intro n
    induction n with
    | zero =>
      show (⊤ : Subgroup Q) ≤ (⊤ : Subgroup P).map μ
      rw [Subgroup.map_top_of_surjective μ hμ]
    | succ n ih =>
      show commSub (commIter ⊤ B n) B ≤ (commSub (commIter ⊤ A n) A).map μ
      refine (commSub_mono ih le_rfl).trans ?_
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨Θ₀ x p * p⁻¹, Subgroup.subset_closure
        ⟨Θ₀ x, Subgroup.mem_comap.mp hx, p, hp, rfl⟩, ?_⟩
      rw [map_mul, map_inv, hint]
  have hBk : commSeries B k = ⊥ := by
    have h1 := hcomm k
    rw [show commIter ⊤ A k = commSeries A k from rfl, hAk, Subgroup.map_bot] at h1
    exact le_bot_iff.mp h1
  have hcard : Nat.card B = Nat.card A := by
    have h1 := B1More.card_map_mul_card_inf_ker Ã Θ
    have h2 := B1More.card_map_mul_card_inf_ker Ã Θ₀
    rw [hAÃ] at h2
    rw [hker_eq] at h1
    have hpos : 0 < Nat.card ↥(Ã ⊓ Θ₀.ker) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hfix : (fixV A).map μ ≤ fixV B := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← hint]
    exact congrArg μ (hv _ (Subgroup.mem_comap.mp hx))
  have hidx : rkIdx (fixV B) ≤ rkIdx (fixV A) := by
    refine le_trans (b := rkIdx ((fixV A).map μ)) ?_ ?_
    · exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite
        (Subgroup.index_dvd_of_le hfix)
    · exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite
        (Subgroup.index_map_dvd _ hμ)
  refine kq_le_iff.mpr ⟨B, ⟨Subgroup.map_le_range _ _, hBne, hBel⟩, hBk, ?_⟩
  refine le_trans ?_ hAr
  unfold rAV
  have hrk : rk ↥B = rk ↥A := by
    unfold rk
    rw [hcard]
  rw [hrk]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hidx) (Nat.cast_nonneg _)

end AbstractKq

section Faithful

theorem d3q_eq_of_central {L : Type*} [Group L] [hperf : Group.IsPerfect L] (α : L →* L)
    (hα : ∀ l, α l * l⁻¹ ∈ Subgroup.center L) : ∀ l, α l = l := by
  let c : L →* L := MonoidHom.mk' (fun l => α l * l⁻¹) (by
    intro a b
    have hb := Subgroup.mem_center_iff.mp (hα b) a⁻¹
    calc α (a * b) * (a * b)⁻¹ = α a * ((α b * b⁻¹) * a⁻¹) := by rw [map_mul]; group
      _ = α a * (a⁻¹ * (α b * b⁻¹)) := by rw [← hb]
      _ = (α a * a⁻¹) * (α b * b⁻¹) := by group)
  have hc : ∀ l, c l = α l * l⁻¹ := fun l => rfl
  have hker : (⊤ : Subgroup L) ≤ c.ker := by
    rw [← hperf.commutator_eq_top]
    show ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ ≤ c.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hc, hc]
    exact Subgroup.mem_center_iff.mp (hα b) (α a * a⁻¹)
  intro l
  have := hker (Subgroup.mem_top l)
  rw [MonoidHom.mem_ker, hc, mul_inv_eq_one] at this
  exact this

variable {Y : Type} [CommGroup Y]

theorem d3q_faithful {Z U : Subgroup Y} {Λ H : Subgroup (MulAut Y)} (hq : CFSG.IsQuasisimple ↥Λ)
    (hZ : Z ≤ fixV Λ) (hΛH : Λ ≤ H) (hHN : H ≤ Subgroup.normalizer (Λ : Set (MulAut Y)))
    (hHZ : H ≤ stabSub Z) (hHU : H ≤ stabSub U) (hcomm : commSub U Λ = U) (hnt : ¬ U ≤ Z)
    {k : MulAut Y} (hk : k ∈ H) (hkU : ∀ u ∈ U, k u * u⁻¹ ∈ Z) : ∀ u ∈ U, k u = u := by
  set ρ : ↥H →* MulAut ↥(U.map (QuotientGroup.mk' Z)) :=
    (d3q_resQuot Z U).comp (Subgroup.inclusion (le_inf hHZ hHU)) with hρ
  have hρ1 : ∀ x : ↥H, ρ x = 1 ↔ ∀ u ∈ U, (x : MulAut Y) u * u⁻¹ ∈ Z :=
    fun x => d3q_resQuot_eq_one_iff _
  set ρΛ : ↥Λ →* MulAut ↥(U.map (QuotientGroup.mk' Z)) := ρ.comp (Subgroup.inclusion hΛH)
    with hρΛ
  have hK : ρΛ.ker ≤ Subgroup.center ↥Λ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker ρΛ) with h | h
    · exfalso
      apply hnt
      have hall : ∀ l ∈ Λ, ∀ u ∈ U, l u * u⁻¹ ∈ Z := by
        intro l hl u hu
        have hmem : (⟨l, hl⟩ : ↥Λ) ∈ ρΛ.ker := by rw [h]; trivial
        exact (hρ1 _).mp hmem u hu
      calc U = commSub U Λ := hcomm.symm
        _ ≤ Z := by
          rw [commSub, Subgroup.closure_le]
          rintro _ ⟨l, hl, w, hw, rfl⟩
          exact hall l hl w hw
    · exact h
  let α : ↥Λ →* ↥Λ := MonoidHom.mk'
    (fun l => ⟨k * l * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hHN hk) l).mp l.2⟩) (by
      intro a b
      apply Subtype.ext
      show k * (↑a * ↑b) * k⁻¹ = k * ↑a * k⁻¹ * (k * ↑b * k⁻¹)
      group)
  have hρk : ρ ⟨k, hk⟩ = 1 := (hρ1 _).mpr hkU
  have hαρ : ∀ l : ↥Λ, ρΛ (α l) = ρΛ l := by
    intro l
    have h1 : Subgroup.inclusion hΛH (α l) =
        ⟨k, hk⟩ * Subgroup.inclusion hΛH l * ⟨k, hk⟩⁻¹ := Subtype.ext rfl
    show ρ (Subgroup.inclusion hΛH (α l)) = ρ (Subgroup.inclusion hΛH l)
    rw [h1, map_mul, map_mul, hρk, one_mul, map_inv, hρk, inv_one, mul_one]
  have hα : ∀ l, α l * l⁻¹ ∈ Subgroup.center ↥Λ := fun l => hK (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαρ, mul_inv_cancel])
  have : Group.IsPerfect ↥Λ := hq.1
  have hα1 := d3q_eq_of_central α hα
  have hcomm_k : ∀ l ∈ Λ, k * l = l * k := by
    intro l hl
    have h := congrArg Subtype.val (hα1 ⟨l, hl⟩)
    exact mul_inv_eq_iff_eq_mul.mp h
  have key : commSub U Λ ≤ MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    have hz : k w * w⁻¹ ∈ Z := hkU w hw
    have e1 : k (l w) = l (k w) := by
      have := congrArg (fun m : MulAut Y => m w) (hcomm_k l hl)
      simpa [MulAut.mul_apply] using this
    have e2 : l (k w * w⁻¹) = k w * w⁻¹ := hZ hz l hl
    show k (l w * w⁻¹) = l w * w⁻¹
    rw [map_mul, map_inv, e1]
    rw [map_mul, map_inv] at e2
    calc l (k w) * (k w)⁻¹ = (l (k w) * (l w)⁻¹) * (l w * w⁻¹) * (w * (k w)⁻¹) := by
          simp [mul_comm, mul_left_comm, mul_assoc]
      _ = l w * w⁻¹ := by
          rw [e2]
          simp [mul_comm, mul_left_comm, mul_assoc]
  intro u hu
  rw [← hcomm] at hu
  exact key hu

theorem d3q_autQuot_sup {A B : Subgroup (MulAut Y)} {Z : Subgroup Y} (hA : A ≤ stabSub Z)
    (hB : B ≤ stabSub Z) : autQuot (A ⊔ B) Z = autQuot A Z ⊔ autQuot B Z :=
  CFSG.Quasithin.v3qb_autQuot_sup hA hB

theorem d3q_autSub_autQuot {Z U : Subgroup Y} {H : Subgroup (MulAut Y)} (hHZ : H ≤ stabSub Z)
    (hHU : H ≤ stabSub U) :
    autSub (autQuot H Z) (U.map (QuotientGroup.mk' Z)) =
      ((d3q_resQuot Z U).comp (Subgroup.inclusion (le_inf hHZ hHU))).range :=
  CFSG.Quasithin.v3qb_autSub_autQuot hHZ hHU

theorem d3q_kq_autSub_autQuot_le [Finite Y] {Z U : Subgroup Y} {Λ H : Subgroup (MulAut Y)}
    (hq : CFSG.IsQuasisimple ↥Λ) (hZ : Z ≤ fixV Λ) (hΛH : Λ ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Λ : Set (MulAut Y))) (hHZ : H ≤ stabSub Z)
    (hHU : H ≤ stabSub U) (hcomm : commSub U Λ = U) (hnt : ¬ U ≤ Z) (k : ℕ) :
    kq (autSub (autQuot H Z) (U.map (QuotientGroup.mk' Z))) k ≤ kq (autSub H U) k := by
  rw [d3q_autSub_autQuot hHZ hHU, autSub_eq_range_resHomOn hHU]
  refine d3q_kq_range_le ((QuotientGroup.mk' Z).subgroupMap U)
    ((QuotientGroup.mk' Z).subgroupMap_surjective U) (resHomOn U hHU)
    ((d3q_resQuot Z U).comp (Subgroup.inclusion (le_inf hHZ hHU))) (fun h p => rfl) ?_ k
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have hx1 : ∀ u ∈ U, (x : MulAut Y) u * u⁻¹ ∈ Z :=
    (d3q_resQuot_eq_one_iff (Subgroup.inclusion (le_inf hHZ hHU) x)).mp hx
  have := d3q_faithful hq hZ hΛH hHN hHZ hHU hcomm hnt x.2 hx1
  refine MulEquiv.ext fun u => Subtype.ext ?_
  exact this u u.2

theorem d3q_irrPlus_map {Z V : Subgroup Y} {Λ : Subgroup (MulAut Y)} (hZ : Z ≤ fixV Λ)
    (hΛZ : Λ ≤ stabSub Z) (hV : V ∈ IrrPlus Λ (⊤ : Subgroup Y)) :
    V.map (QuotientGroup.mk' Z) ∈ IrrPlus (autQuot Λ Z) (⊤ : Subgroup (Y ⧸ Z)) :=
  CFSG.Quasithin.v3qb_irrPlus_map hZ hΛZ hV

end Faithful

section GeneralPrelim

variable {Y : Type} [CommGroup Y]

theorem d3q_fixed_of_comm_le {Z : Subgroup Y} {Λ : Subgroup (MulAut Y)} [Group.IsPerfect ↥Λ]
    (hZ : Z ≤ fixV Λ) {v : Y} (hv : ∀ l ∈ Λ, l v * v⁻¹ ∈ Z) : v ∈ fixV Λ :=
  CFSG.Quasithin.v3qb_fixed_of_comm_le hZ hv

theorem d3q_orbSup_map {Z V : Subgroup Y} {S : Subgroup (MulAut Y)} (hSZ : S ≤ stabSub Z) :
    orbSup (autQuot S Z) (V.map (QuotientGroup.mk' Z)) =
      (orbSup S V).map (QuotientGroup.mk' Z) :=
  CFSG.Quasithin.v3qb_orbSup_map hSZ

theorem d3q_invariant_orbSup {V : Subgroup Y} {Λ S : Subgroup (MulAut Y)}
    (hSN : S ≤ Subgroup.normalizer (Λ : Set (MulAut Y))) (hV : ∀ x ∈ Λ, ∀ w ∈ V, x w ∈ V) :
    ∀ x ∈ Λ, ∀ w ∈ orbSup S V, x w ∈ orbSup S V :=
  CFSG.Quasithin.v3qb_invariant_orbSup hSN hV

theorem d3q_commSub_orbSup {V : Subgroup Y} {Λ S : Subgroup (MulAut Y)}
    (hSN : S ≤ Subgroup.normalizer (Λ : Set (MulAut Y))) (hV : ∀ x ∈ Λ, ∀ w ∈ V, x w ∈ V)
    (hcomm : commSub V Λ = V) : commSub (orbSup S V) Λ = orbSup S V := by
  refine le_antisymm (commSub_le_of_invariant (d3q_invariant_orbSup hSN hV)) ?_
  refine orbSup_le fun s hs => ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v ∈ commSub V Λ := by rw [hcomm]; exact hv
  refine Subgroup.closure_induction (p := fun u _ => s u ∈ commSub (orbSup S V) Λ) ?_ ?_ ?_ ?_ hv'
  · rintro _ ⟨l, hl, w, hw, rfl⟩
    have e : s (l w * w⁻¹) = (s * l * s⁻¹) (s w) * (s w)⁻¹ := by simp [MulAut.mul_apply]
    show s (l w * w⁻¹) ∈ _
    rw [e]
    exact Subgroup.subset_closure ⟨s * l * s⁻¹, (Subgroup.mem_normalizer_iff.mp (hSN hs) l).mp hl,
      s w, map_le_orbSup hs ⟨w, hw, rfl⟩, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact inv_mem ha

end GeneralPrelim

section IsoTransfer

variable {A₁ A₂ : Type*} [Group A₁] [Group A₂] {Q₁ Q₂ : Type*} [CommGroup Q₁] [CommGroup Q₂]
  [MulDistribMulAction A₁ Q₁] [MulDistribMulAction A₂ Q₂]

theorem d3q_iso_of_iso_map (θ : Q₁ →* Q₂) (hθ : ∀ a₁ : A₁, ∃ a₂ : A₂, ∀ x, θ (a₁ • x) = a₂ • θ x)
    {S L₁ L₂ : Subgroup Q₁} (hS : XMod.IsInv A₁ S) (hinj : ∀ x ∈ S, θ x = 1 → x = 1)
    (h₁ : L₁ ≤ S) (h₂ : L₂ ≤ S) (h : XMod.Iso A₂ (L₁.map θ) (L₂.map θ)) :
    XMod.Iso A₁ L₁ L₂ := by
  have hinj' : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := hinj _ (S.mul_mem hx (S.inv_mem hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨e₁, he₁⟩ := exists_equivMap_of_injOn θ hinj' h₁
  obtain ⟨e₂, he₂⟩ := exists_equivMap_of_injOn θ hinj' h₂
  refine ⟨e₁.trans (φ.trans e₂.symm), fun a l l' hll' => ?_⟩
  obtain ⟨a₂, ha₂⟩ := hθ a
  have h1 : a₂ • ((e₁ l : ↥(L₁.map θ)) : Q₂) = ((e₁ l' : ↥(L₁.map θ)) : Q₂) := by
    rw [he₁, he₁, ← ha₂, hll']
  have h2 := hφ a₂ (e₁ l) (e₁ l') h1
  have hx : θ (((e₂.symm (φ (e₁ l)) : ↥L₂)) : Q₁) = ((φ (e₁ l) : ↥(L₂.map θ)) : Q₂) := by
    rw [← he₂, MulEquiv.apply_symm_apply]
  have hy : θ (((e₂.symm (φ (e₁ l')) : ↥L₂)) : Q₁) = ((φ (e₁ l') : ↥(L₂.map θ)) : Q₂) := by
    rw [← he₂, MulEquiv.apply_symm_apply]
  show a • (((e₂.symm (φ (e₁ l)) : ↥L₂)) : Q₁) = ((e₂.symm (φ (e₁ l')) : ↥L₂) : Q₁)
  apply hinj' _ (hS a _ (h₂ (e₂.symm (φ (e₁ l))).2)) _ (h₂ (e₂.symm (φ (e₁ l'))).2)
  rw [ha₂, hx, hy, h2]

end IsoTransfer

section TildeQuot

variable {Y : Type} [CommGroup Y]

theorem d3q_modFix_map_le {Z W : Subgroup Y} {Λ : Subgroup (MulAut Y)} :
    modFix Λ W ≤
      (modFix (autQuot Λ Z) (W.map (QuotientGroup.mk' Z))).comap (QuotientGroup.mk' Z) := by
  intro c hc
  rw [Subgroup.mem_comap]
  refine ⟨⟨c, hc.1, rfl⟩, fun a => ?_⟩
  obtain ⟨g, hg, hga⟩ := mem_autQuot.mp a.2
  show (a : MulAut (Y ⧸ Z)) (QuotientGroup.mk' Z c) = QuotientGroup.mk' Z c
  rw [← hga]
  show QuotientGroup.mk' Z ((g : MulAut Y) c) = QuotientGroup.mk' Z c
  rw [show (g : MulAut Y) c = c from hc.2 ⟨(g : MulAut Y), hg⟩]

@[expose] noncomputable def d3q_tildeMap (Z W : Subgroup Y) {Λ : Subgroup (MulAut Y)} :
    (Y ⧸ modFix Λ W) →* ((Y ⧸ Z) ⧸ modFix (autQuot Λ Z) (W.map (QuotientGroup.mk' Z))) :=
  QuotientGroup.map _ _ (QuotientGroup.mk' Z) d3q_modFix_map_le

theorem d3q_tildeMap_mk (Z W : Subgroup Y) {Λ : Subgroup (MulAut Y)} (y : Y) :
    d3q_tildeMap (Λ := Λ) Z W (QuotientGroup.mk y) =
      QuotientGroup.mk (QuotientGroup.mk' Z y) := rfl

theorem d3q_tildeMap_smul (Z W : Subgroup Y) {Λ : Subgroup (MulAut Y)} (hΛZ : Λ ≤ stabSub Z)
    (a : ↥Λ) : ∃ a' : ↥(autQuot Λ Z), ∀ x : Y ⧸ modFix Λ W,
      d3q_tildeMap Z W (a • x) = a' • d3q_tildeMap Z W x := by
  refine ⟨⟨quotHom Z ⟨a, hΛZ a.2⟩, mem_autQuot.mpr ⟨_, a.2, rfl⟩⟩, fun x => ?_⟩
  induction x using QuotientGroup.induction_on with
  | H y => rfl

theorem d3q_tilde_map (Z W : Subgroup Y) {Λ : Subgroup (MulAut Y)} (J : Subgroup Y) :
    (tilde Λ W J).map (d3q_tildeMap Z W) =
      tilde (autQuot Λ Z) (W.map (QuotientGroup.mk' Z)) (J.map (QuotientGroup.mk' Z)) := by
  unfold tilde
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem d3q_tildeMap_inj {Z W : Subgroup Y} {Λ : Subgroup (MulAut Y)} [Group.IsPerfect ↥Λ]
    (hZ : Z ≤ fixV Λ) (hΛZ : Λ ≤ stabSub Z) :
    ∀ x ∈ tilde Λ W W, d3q_tildeMap Z W x = 1 → x = 1 := by
  intro x hx h
  obtain ⟨w, hw, rfl⟩ := mem_tilde_iff.1 hx
  rw [d3q_tildeMap_mk, QuotientGroup.eq_one_iff] at h
  have hv : ∀ l ∈ Λ, l w * w⁻¹ ∈ Z := by
    intro l hl
    have h2 := h.2 ⟨quotHom Z ⟨l, hΛZ hl⟩, mem_autQuot.mpr ⟨_, hl, rfl⟩⟩
    exact (mk_eq_mk_iff _ _).mp h2
  have hfix := d3q_fixed_of_comm_le hZ hv
  rw [QuotientGroup.eq_one_iff]
  exact ⟨hw, fun a => hfix a a.2⟩

end TildeQuot

section Transport

variable {Y : Type} [CommGroup Y]

theorem d3q_autQuot_le_normalizer {Z : Subgroup Y} {K H : Subgroup (MulAut Y)}
    (hKH : K ≤ H) (hH : H ≤ stabSub Z) (hHN : H ≤ Subgroup.normalizer (K : Set (MulAut Y))) :
    autQuot H Z ≤ Subgroup.normalizer (autQuot K Z : Set (MulAut (Y ⧸ Z))) := by
  rw [d3q_autQuot_eq_map le_rfl hH, d3q_autQuot_eq_map hKH hH]
  exact map_le_normalizer_map_of_le_normalizer (d3q_quotHomOn Z hH) hKH hHN

theorem d3q_irrPlusOn_map {Z V : Subgroup Y} {Λ S : Subgroup (MulAut Y)}
    [Group.IsPerfect ↥Λ] (hZ : Z ≤ fixV Λ) (hΛZ : Λ ≤ stabSub Z) (hSZ : S ≤ stabSub Z)
    (hSN : S ≤ Subgroup.normalizer (Λ : Set (MulAut Y))) (hV : V ∈ IrrPlusOn Λ (orbSup S V) S) :
    V.map (QuotientGroup.mk' Z) ∈ IrrPlusOn (autQuot Λ Z)
      (orbSup (autQuot S Z) (V.map (QuotientGroup.mk' Z))) (autQuot S Z) := by
  have hVΛ : ∀ x ∈ Λ, ∀ w ∈ V, x w ∈ V := (isInv_iff Λ V).mp hV.1.2.1
  have hVSΛ := d3q_invariant_orbSup hSN hVΛ
  have hWS : ∀ t ∈ S, ∀ w ∈ orbSup S V, t • w ∈ orbSup S V := fun t ht w hw =>
    mem_orbSup_of_mem_map ht hw
  have hsrc := (forall_smul_eq_iff_mem_irrPlusOn hSN hWS hV.1).mpr hV
  rw [d3q_orbSup_map hSZ]
  have hIrr : V.map (QuotientGroup.mk' Z) ∈
      IrrPlus (autQuot Λ Z) ((orbSup S V).map (QuotientGroup.mk' Z)) :=
    ⟨Subgroup.map_mono (le_orbSup S V), (d3q_irrPlus_map hZ hΛZ ⟨le_top, hV.1.2⟩).2⟩
  have hSΛ : autQuot S Z ≤ Subgroup.normalizer (autQuot Λ Z : Set (MulAut (Y ⧸ Z))) := by
    refine (autQuot_mono (le_sup_right : S ≤ Λ ⊔ S) Z).trans ?_
    refine d3q_autQuot_le_normalizer (le_sup_left : Λ ≤ Λ ⊔ S) (sup_le hΛZ hSZ)
      (sup_le Subgroup.le_normalizer hSN)
  have hWhat : ∀ t ∈ autQuot S Z, ∀ w ∈ (orbSup S V).map (QuotientGroup.mk' Z),
      t • w ∈ (orbSup S V).map (QuotientGroup.mk' Z) := by
    intro t ht w hw
    obtain ⟨s, hsS, rfl⟩ := mem_autQuot.mp ht
    obtain ⟨u, hu, rfl⟩ := hw
    exact ⟨(s : MulAut Y) u, mem_orbSup_of_mem_map hsS hu, rfl⟩
  refine (forall_smul_eq_iff_mem_irrPlusOn hSΛ hWhat hIrr).mp ?_
  rintro t ⟨ht, hiso⟩
  obtain ⟨s, hsS, rfl⟩ := mem_autQuot.mp ht
  have e : (quotHom Z s : MulAut (Y ⧸ Z)) • V.map (QuotientGroup.mk' Z) =
      ((s : MulAut Y) • V).map (QuotientGroup.mk' Z) := by
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨(s : MulAut Y) v, Subgroup.smul_mem_pointwise_smul v _ V hv, rfl⟩
    · rintro ⟨_, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ V).mp hw
      exact ⟨QuotientGroup.mk' Z v, ⟨v, hv, rfl⟩, rfl⟩
  have hsV : (s : MulAut Y) • V ≤ orbSup S V := by
    rw [orbSup_eq_biSup_smul]
    exact le_biSup_smul S V hsS
  have hinv : XMod.IsInv ↥Λ (tilde Λ (orbSup S V) (orbSup S V)) :=
    isInv_tilde (fun a w hw => hVSΛ a a.2 w hw)
  have hiso' : XMod.Iso ↥(autQuot Λ Z)
      ((tilde Λ (orbSup S V) ((s : MulAut Y) • V)).map (d3q_tildeMap Z (orbSup S V)))
      ((tilde Λ (orbSup S V) V).map (d3q_tildeMap Z (orbSup S V))) := by
    rw [d3q_tilde_map, d3q_tilde_map, ← e]
    exact hiso
  have hiso'' := d3q_iso_of_iso_map (d3q_tildeMap Z (orbSup S V))
    (fun a => d3q_tildeMap_smul Z (orbSup S V) hΛZ a) hinv
    (d3q_tildeMap_inj hZ hΛZ) (tilde_mono hsV) (tilde_mono (le_orbSup S V)) hiso'
  have := hsrc _ ⟨hsS, hiso''⟩
  rw [e, this]

theorem d3q_pCoreOf_autQuot_eq_bot [Finite Y] {Z : Subgroup Y} {Λ : Subgroup (MulAut Y)}
    (hq : CFSG.IsQuasisimple ↥Λ) (hΛZ : Λ ≤ stabSub Z) (hne : autQuot Λ Z ≠ ⊥)
    (hO2 : pCoreOf 2 Λ = ⊥) : pCoreOf 2 (autQuot Λ Z) = ⊥ := by
  have hker : (D37Lift.toQuot Z Λ hΛZ).ker ≤ Subgroup.center ↥Λ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (MonoidHom.normal_ker (D37Lift.toQuot Z Λ hΛZ)) with h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      rintro _ hφ
      obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
      have : (⟨(g : MulAut Y), hg⟩ : ↥Λ) ∈ (D37Lift.toQuot Z Λ hΛZ).ker := by rw [h]; trivial
      rw [MonoidHom.mem_ker] at this
      have h1 := congrArg Subtype.val this
      rw [Subgroup.mem_bot]
      exact h1
    · exact h
  have hX : CFSG.Open.pCore 2 ↥Λ = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Λ.subtype_injective).mp hO2
  have h := pCore_eq_bot_of_surjective_of_ker_le_center (D37Lift.toQuot Z Λ hΛZ)
    (D37Lift.toQuot_surjective Z Λ hΛZ) hker hX
  unfold pCoreOf
  rw [h, Subgroup.map_bot]

end Transport

section Quot

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V Z : Subgroup Y}

theorem d3Std_quot_gen (hstd : D3Std Γ Λ S Λ V) (hZ : Z ≤ fixV Λ) (hZΓ : Γ ≤ stabSub Z) :
    D3Std (autQuot Γ Z) (autQuot Λ Z) (autQuot S Z) (autQuot Λ Z)
      (V.map (QuotientGroup.mk' Z)) := by
  have hD := hstd.hyp
  have hSΓ : S ≤ Γ := hD.sylow.1
  have hΛΓ : Λ ≤ Γ := le_of_mem_cComp hD.comp
  have hΛS : Λ ⊔ S ≤ Γ := sup_le hΛΓ hSΓ
  have hΛZ : Λ ≤ stabSub Z := hΛΓ.trans hZΓ
  have hSZ : S ≤ stabSub Z := hSΓ.trans hZΓ
  have hSN : S ≤ Subgroup.normalizer (Λ : Set (MulAut Y)) := hSΓ.trans hD.Mp_normal
  have hirrV := mem_irrPlus_top_iff.mp hD.irr
  have : Group.IsPerfect ↥Λ := hD.quasi.1
  have hVnt : ¬ V ≤ Z := by
    intro h
    exact absurd (inf_eq_left.mpr (h.trans hZ)) (ne_of_lt hirrV.2.2.1)
  have hVSΛ : Λ ≤ stabSub (orbSup S V) :=
    B1.le_stabSub_of_invariant (d3q_invariant_orbSup hSN hirrV.1)
  have hVSS : S ≤ stabSub (orbSup S V) := le_stabSub_orbSup S V
  have hVScomm : commSub (orbSup S V) Λ = orbSup S V := d3q_commSub_orbSup hSN hirrV.1 hirrV.2.1
  have hVSnt : ¬ orbSup S V ≤ Z := fun h => hVnt ((le_orbSup S V).trans h)
  set φ := d3q_quotHomOn Z hZΓ with hφ
  have eΓ : autQuot Γ Z = (Γ.subgroupOf Γ).map φ := d3q_autQuot_eq_map le_rfl hZΓ
  have eΛ : autQuot Λ Z = (Λ.subgroupOf Γ).map φ := d3q_autQuot_eq_map hΛΓ hZΓ
  have eS : autQuot S Z = (S.subgroupOf Γ).map φ := d3q_autQuot_eq_map hSΓ hZΓ
  have hLne : autQuot Λ Z ≠ ⊥ := by
    intro hbot
    apply hVnt
    calc V = commSub V Λ := hirrV.2.1.symm
      _ ≤ Z := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨l, hl, w, -, rfl⟩
        have h1 : quotHom Z ⟨l, hΛZ hl⟩ ∈ autQuot Λ Z := mem_autQuot.mpr ⟨_, hl, rfl⟩
        rw [hbot, Subgroup.mem_bot] at h1
        have h2 := congrArg (fun m : MulAut (Y ⧸ Z) => m (QuotientGroup.mk w)) h1
        simp only [quotHom_mk, MulAut.one_apply] at h2
        exact (mk_eq_mk_iff _ _).mp h2
  have hexp : ∀ w : Y ⧸ Z, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hD.exp v]; rfl
  have hqsqtk : IsQuotientOfSQTKTC ↥(autQuot Γ Z) := by
    rw [eΓ, map_subgroupOf_self_eq_range]
    exact isQuotientOfSQTK_range_aux φ hD.qsqtk
  have hsylow : IsSylowTwoOf (autQuot S Z) (autQuot Γ Z) := by
    rw [eS, eΓ]
    exact isSylowTwoOf_map_subgroupOf φ hD.sylow
  have hcomp : autQuot Λ Z ∈ cComp (autQuot Γ Z) := by
    rw [eΛ, eΓ]
    exact map_subgroupOf_mem_cComp φ hD.comp (by rw [← eΛ]; exact hLne)
  have hquasi : CFSG.IsQuasisimple ↥(autQuot Λ Z) := by
    rw [eΛ]
    exact isQuasisimple_map_subgroupOf_of_ne_bot hΛΓ hD.quasi φ (by rw [← eΛ]; exact hLne)
  have hMpeq : autQuot Λ Z = conjClosure (autQuot Λ Z) (autQuot S Z) := by
    have h := map_subgroupOf_conjClosure φ hΛΓ hSΓ
    rw [← hD.Mp_eq] at h
    rw [eΛ, eS]
    exact h
  have hMnorm : autQuot Γ Z ≤ Subgroup.normalizer (autQuot Λ Z : Set (MulAut (Y ⧸ Z))) :=
    d3q_autQuot_le_normalizer hΛΓ hZΓ hD.Mp_normal
  have hirr : V.map (QuotientGroup.mk' Z) ∈ IrrPlus (autQuot Λ Z) (⊤ : Subgroup (Y ⧸ Z)) :=
    d3q_irrPlus_map hZ hΛZ hD.irr
  have hgen : (⨆ m ∈ autQuot Γ Z, (V.map (QuotientGroup.mk' Z)).map m.toMonoidHom) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : y ∈ (⨆ m ∈ Γ, V.map m.toMonoidHom) := by rw [hD.gen]; trivial
    have hle : (⨆ m ∈ Γ, V.map m.toMonoidHom).map (QuotientGroup.mk' Z) ≤
        ⨆ m ∈ autQuot Γ Z, (V.map (QuotientGroup.mk' Z)).map m.toMonoidHom := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun m => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hm => ?_
      refine le_iSup₂_of_le (quotHom Z ⟨m, hZΓ hm⟩) (mem_autQuot.mpr ⟨_, hm, rfl⟩) ?_
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk' Z v, ⟨v, hv, rfl⟩, rfl⟩
    exact hle ⟨y, hy, rfl⟩
  have hirrT := d3q_irrPlusOn_map hZ hΛZ hSZ hSN hstd.irrT
  have hSylX : IsSylowTwoOf (autQuot S Z) (autQuot Λ Z ⊔ autQuot S Z) :=
    F7.isSylowTwoOf_mono_right hsylow le_sup_right
      (sup_le (autQuot_mono hΛΓ Z) (autQuot_mono hSΓ Z))
  have hSΛ : autQuot S Z ≤ Subgroup.normalizer (autQuot Λ Z : Set (MulAut (Y ⧸ Z))) :=
    (autQuot_mono hSΓ Z).trans hMnorm
  have hO2 : pCoreOf 2 (autQuot Λ Z) = ⊥ :=
    d3q_pCoreOf_autQuot_eq_bot hD.quasi hΛZ hLne (D31.pCoreOf_Mp_eq_bot hD)
  have ho2 := o2inv_of_irrPlusOn hSΛ hSylX hO2 hirrT
  have hqhat : qhatOf (autSub (autQuot Λ Z ⊔ autQuot S Z)
      (orbSup (autQuot S Z) (V.map (QuotientGroup.mk' Z)))) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [d3q_orbSup_map hSZ, ← d3q_autQuot_sup hΛZ hSZ]
    exact (d3q_kq_autSub_autQuot_le hD.quasi hZ (le_sup_left : Λ ≤ Λ ⊔ S)
      (hΛS.trans hD.Mp_normal) (hΛS.trans hZΓ) (sup_le hVSΛ hVSS) hVScomm hVSnt 3).trans
      hstd.qhat
  exact ⟨⟨hexp, hqsqtk, hsylow, hcomp, hquasi, hMpeq, hMnorm, hirr, ho2, hgen⟩, hqhat, hirrT⟩

theorem d3Std_quot (hstd : D3Std Γ Λ S Λ V) (hVS : V = orbSup S V) (hZ : Z ≤ fixV Λ)
    (hZΓ : Γ ≤ stabSub Z) :
    D3Std (autQuot Γ Z) (autQuot Λ Z) (autQuot S Z) (autQuot Λ Z) (V.map (QuotientGroup.mk' Z)) :=
  have _ := hVS
  d3Std_quot_gen hstd hZ hZΓ

end Quot

end CFSG.Quasithin
