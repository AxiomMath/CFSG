module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Pairs
public import CFSG.SignalizerFunctorTheorem.Quadratic.Independence

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

section Generic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

def decTrivQuot (W : Submodule (ZMod p) V) : Subgroup (LGL p V) where
  carrier := {g | ∀ v, g v - v ∈ W}
  one_mem' := fun v => by simp
  mul_mem' := fun {a b} ha hb v => by
    have h := W.add_mem (ha (b v)) (hb v)
    have e : a (b v) - b v + (b v - v) = (a * b) v - v := by
      change a (b v) - b v + (b v - v) = a (b v) - v
      abel
    rw [e] at h
    exact h
  inv_mem' := fun {a} ha v => by
    have h := W.neg_mem (ha (a⁻¹ v))
    have e : -(a (a⁻¹ v) - a⁻¹ v) = a⁻¹ v - v := by
      change -(a (a.symm v) - a.symm v) = a.symm v - v
      rw [LinearEquiv.apply_symm_apply]
      abel
    rw [e] at h
    exact h

theorem dec_le_trivQuot_iff (A : Subgroup (LGL p V)) (W : Submodule (ZMod p) V) :
    A ≤ decTrivQuot W ↔ commSub A ≤ W := by
  rw [commSub_le_iff]
  exact ⟨fun h a ha v => h ha v, fun h a ha v => h a ha v⟩

theorem dec_commSub_sup (A B : Subgroup (LGL p V)) :
    commSub (A ⊔ B) = commSub A ⊔ commSub B := by
  apply le_antisymm
  · rw [← dec_le_trivQuot_iff]
    exact sup_le ((dec_le_trivQuot_iff _ _).mpr le_sup_left)
      ((dec_le_trivQuot_iff _ _).mpr le_sup_right)
  · exact sup_le (commSub_mono _ _ le_sup_left) (commSub_mono _ _ le_sup_right)

theorem dec_le_kerOn_top_iff {A : Subgroup (LGL p V)} {W : Submodule (ZMod p) V} :
    A ≤ kerOn ⊤ W ↔ ∀ a ∈ A, ∀ w ∈ W, a w = w :=
  ⟨fun h _ ha w hw => (h ha).2 w hw, fun h a ha => ⟨trivial, h a ha⟩⟩

theorem dec_comm_of_split {U W : Submodule (ZMod p) V} (h : IsCompl U W) {e g : LGL p V}
    (heU : ∀ u ∈ U, e u ∈ U) (heW : ∀ w ∈ W, e w = w) (hgU : ∀ u ∈ U, g u = u)
    (hgW : ∀ w ∈ W, g w ∈ W) : e * g = g * e := by
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ U ⊔ W := by rw [h.sup_eq_top]; trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  change e (g (u + w)) = g (e (u + w))
  simp only [map_add]
  rw [hgU u hu, heW w hw, heW _ (hgW w hw), hgU _ (heU u hu)]

end Generic

section Group

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem dec_mem_normalizer_commutator {S T : Subgroup G} {g : G}
    (hS : g ∈ Subgroup.normalizer (S : Set G)) (hT : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer ((⁅S, T⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), g ∈ Subgroup.normalizer (T : Set G) →
      ∀ x ∈ ⁅S, T⁆, g * x * g⁻¹ ∈ ⁅S, T⁆ := by
    intro g hgS hgT
    have hle : ⁅S, T⁆ ≤ (⁅S, T⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro s hs t ht
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj g).toMonoidHom ⁅s, t⁆ = ⁅g * s * g⁻¹, g * t * g⁻¹⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hgS s).mp hs)
        ((Subgroup.mem_normalizer_iff.mp hgT t).mp ht)
    intro x hx
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hS hT x, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer _).inv_mem hS) ((Subgroup.normalizer _).inv_mem hT) _ hx
  simpa [mul_assoc] using this

theorem dec_le_normalizer_of_commute {S T : Subgroup G}
    (h : ∀ t ∈ T, ∀ s ∈ S, t * s = s * t) : T ≤ Subgroup.normalizer (S : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : t * x * t⁻¹ = x := by rw [h t ht x hx]; group
    rwa [this]
  · intro hx
    have h1 := h t⁻¹ (T.inv_mem ht) _ hx
    have h3 : x * t⁻¹ = t * x * t⁻¹ * t⁻¹ := by
      have e : t⁻¹ * (t * x * t⁻¹) = x * t⁻¹ := by group
      rw [← e]
      exact h1
    rw [mul_right_cancel h3]
    exact hx

end Group

section Card

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem dec_eq_of_le_of_card_le {U U' : Submodule (ZMod p) V} (h : U ≤ U')
    (hc : Nat.card U' ≤ Nat.card U) : U = U' := by
  have h1 := card_eq_pow_finrank U
  have h2 := card_eq_pow_finrank U'
  have h3 : Module.finrank (ZMod p) U' ≤ Module.finrank (ZMod p) U := by
    rw [h1, h2] at hc
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hc
  exact Submodule.eq_of_le_of_finrank_le h h3

omit [Finite V] in
theorem dec_card_mul_of_isCompl {U W : Submodule (ZMod p) V} (h : IsCompl U W) :
    Nat.card U * Nat.card W = Nat.card V := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Submodule.prodEquivOfIsCompl U W h).toEquiv

theorem dec_exists_basis {U : Submodule (ZMod p) V} (h : Nat.card U = p ^ 2) :
    ∃ b : Fin 2 → V, LinearIndependent (ZMod p) b ∧
      Submodule.span (ZMod p) (Set.range b) = U := by
  have hfr : Module.finrank (ZMod p) U = 2 := by
    have := card_eq_pow_finrank U
    rw [h] at this
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le this).symm
  let bs := Module.finBasisOfFinrankEq (ZMod p) U hfr
  refine ⟨fun i => (bs i : V), ?_, ?_⟩
  · exact (bs.linearIndependent).map' U.subtype (Submodule.ker_subtype U)
  · have e : Set.range (fun i => (bs i : V)) = U.subtype '' Set.range bs := by
      ext x
      simp [Set.mem_range]
    rw [e, ← Submodule.map_span, bs.span_eq, Submodule.map_top, Submodule.range_subtype]

omit [Finite V] in
theorem dec_ne_bot_of_card {U : Submodule (ZMod p) V} (h : Nat.card U = p ^ 2) : U ≠ ⊥ := by
  rintro rfl
  have h1 : Nat.card (⊥ : Submodule (ZMod p) V) = 1 := Nat.card_unique
  rw [h1] at h
  have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
  omega

theorem dec_block_le {E E' : Subgroup (LGL p V)} (hE : IsBlock p E)
    (hE' : IsBlock p E') (hpl : commSub E = commSub E') {W : Submodule (ZMod p) V}
    (hW : IsCompl (commSub E) W) (hEW : ∀ g ∈ E, ∀ w ∈ W, g w = w)
    (hE'W : ∀ g ∈ E', ∀ w ∈ W, g w = w) : E ≤ E' := by
  obtain ⟨b, hb, hspan⟩ := dec_exists_basis hE.card_comm
  obtain ⟨Φ, hΦ⟩ := hE.exists_mulEquiv b hb hspan
  obtain ⟨Φ', hΦ'⟩ := hE'.exists_mulEquiv b hb (hspan.trans hpl)
  intro g hg
  set g' : E' := Φ'.symm (Φ ⟨g, hg⟩) with hg'
  have h1 := hΦ ⟨g, hg⟩
  have h2 := hΦ' g'
  rw [hg', MulEquiv.apply_symm_apply] at h2
  have hagree : ∀ u ∈ commSub E, g u = (g' : LGL p V) u := by
    intro u hu
    rw [← hspan] at hu
    refine LinearMap.eqOn_span (s := Set.range b) (f := (g : V →ₗ[ZMod p] V))
      (g := ((g' : LGL p V) : V →ₗ[ZMod p] V)) ?_ hu
    rintro _ ⟨j, rfl⟩
    exact (h1 j).trans (h2 j).symm
  have : g = (g' : LGL p V) := by
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ commSub E ⊔ W := by rw [hW.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, map_add, hagree u hu, hEW g hg w hw, hE'W _ g'.2 w hw]
  rw [this]
  exact g'.2

theorem dec_block_eq {E E' : Subgroup (LGL p V)} (hE : IsBlock p E)
    (hE' : IsBlock p E') (hpl : commSub E = commSub E') {W : Submodule (ZMod p) V}
    (hW : IsCompl (commSub E) W) (hEW : ∀ g ∈ E, ∀ w ∈ W, g w = w)
    (hE'W : ∀ g ∈ E', ∀ w ∈ W, g w = w) : E = E' :=
  le_antisymm (dec_block_le hE hE' hpl hW hEW hE'W)
    (dec_block_le hE' hE hpl.symm (hpl ▸ hW) hE'W hEW)

end Card

section Small

variable {p : ℕ}

theorem dec_rp_prime : (rp p).Prime := by
  unfold rp
  split_ifs <;> norm_num

theorem dec_rp_ne (hp : p = 2 ∨ p = 3) : rp p ≠ p := by
  unfold rp
  rcases hp with h | h <;> simp [h]

theorem dec_two_lt (hp : p = 2 ∨ p = 3) : 2 < p ^ 2 - 1 := by
  rcases hp with h | h <;> rw [h] <;> norm_num

end Small

section Facts

open scoped commutatorElement

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fact p.Prime] [Finite V]
  {H : Subgroup (LGL p V)} {A B : Subgroup (LGL p V)}

theorem dec_comm_le_Qp (hAH : A ≤ H) : ⁅Qp p H, A⁆ ≤ Qp p H := by
  rw [Subgroup.commutator_le]
  intro q hq a ha
  have h1 : a * q⁻¹ * a⁻¹ ∈ Qp p H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_Qp hAH ha) q⁻¹).mp ((Qp p H).inv_mem hq)
  have e : ⁅q, a⁆ = q * (a * q⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (Qp p H).mul_mem hq h1

theorem dec_A_le_normalizer_comm (hAH : A ≤ H) :
    A ≤ Subgroup.normalizer ((⁅Qp p H, A⁆ : Subgroup (LGL p V)) : Set (LGL p V)) :=
  fun _ ha => dec_mem_normalizer_commutator (le_normalizer_Qp hAH ha) (Subgroup.le_normalizer ha)

omit [Fact p.Prime] [Finite V] in
theorem dec_Qp_le_normalizer_comm :
    Qp p H ≤ Subgroup.normalizer ((⁅Qp p H, A⁆ : Subgroup (LGL p V)) : Set (LGL p V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => commutator_normal g hg x hx, fun hx => ?_⟩
  have := commutator_normal g⁻¹ ((Qp p H).inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem dec_two_three (hH : Hyp H) (hA : IsAVMin H A) : p = 2 ∨ p = 3 :=
  (isPGroup_commutator hH hA).1

theorem dec_coprime_K (hH : Hyp H) (hA : IsAVMin H A) :
    Nat.Coprime p (Nat.card (⁅Qp p H, A⁆ : Subgroup (LGL p V))) := by
  obtain ⟨hp, hK⟩ := isPGroup_commutator hH hA
  have : Fact (rp p).Prime := ⟨dec_rp_prime⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  rw [hn]
  exact Nat.Coprime.pow_right n
    ((Nat.coprime_primes (Fact.out : p.Prime) (dec_rp_prime)).mpr (dec_rp_ne hp).symm)

theorem dec_exists_x (hH : Hyp H) (hA : IsAVMin H A) :
    ∃ x, x ∈ Qp p H ∧ x ∉ Subgroup.centralizer (A : Set (LGL p V)) := by
  by_contra hcon
  apply commutator_ne_bot hH hA
  rw [commutator_eq_iSup hA]
  simp only [iSup_eq_bot]
  intro x hx
  exact absurd ⟨x, hx.1, hx.2⟩ hcon

theorem dec_plane_eq (hH : Hyp H) (hA : IsAVMin H A) {x y : LGL p V} (hxQ : x ∈ Qp p H)
    (hx : x ∉ Subgroup.centralizer (A : Set (LGL p V))) (hyQ : y ∈ Qp p H)
    (hy : y ∉ Subgroup.centralizer (A : Set (LGL p V))) :
    commSub (A ⊔ cj x A) = commSub (A ⊔ cj y A) := by
  by_contra hne
  have hp := dec_two_three hH hA
  have hpx := pair_card_comm hH hA hxQ hx
  have hpy := pair_card_comm hH hA hyQ hy
  have hx' := pair_commSub_Qx hH hA hxQ hx
  have hy' := pair_commSub_Qx hH hA hyQ hy
  have h3 : ¬ commSub ((A ⊔ cj x A) ⊓ Qp p H) ≤ commSub ((A ⊔ cj y A) ⊓ Qp p H) := by
    rw [hx', hy']
    intro hle
    exact hne (dec_eq_of_le_of_card_le hle (by rw [hpx, hpy]))
  have h3' : ¬ commSub ((A ⊔ cj y A) ⊓ Qp p H) ≤ commSub ((A ⊔ cj x A) ⊓ Qp p H) := by
    rw [hx', hy']
    intro hle
    exact hne (dec_eq_of_le_of_card_le hle (by rw [hpx, hpy])).symm
  have hQ : IsPGroup (rp p) ↥(((A ⊔ cj x A) ⊓ Qp p H) ⊔ ((A ⊔ cj y A) ⊓ Qp p H)) :=
    (isPGroup_commutator hH hA).2.to_le
      (sup_le (pair_Qx_le hA hxQ) (pair_Qx_le hA hyQ))
  have hirr : ∀ {z : LGL p V}, z ∈ Qp p H → z ∉ Subgroup.centralizer (A : Set (LGL p V)) →
      ∀ U ≤ commSub ((A ⊔ cj z A) ⊓ Qp p H),
        (∀ g ∈ (A ⊔ cj z A) ⊓ Qp p H, ∀ u ∈ U, g u ∈ U) →
        U = ⊥ ∨ U = commSub ((A ⊔ cj z A) ⊓ Qp p H) := by
    intro z hzQ hz U hU hinv
    rw [pair_commSub_Qx hH hA hzQ hz] at hU ⊢
    exact pair_irred hH hA hzQ hz U hU hinv
  obtain ⟨_, hinf⟩ := indep_pair (dec_rp_prime) (dec_rp_ne hp) hQ (hirr hxQ hx) (hirr hyQ hy)
    h3 h3' (by rw [pair_Qx_card hH hA hxQ hx]; exact dec_two_lt hp)
    (by rw [pair_Qx_card hH hA hyQ hy]; exact dec_two_lt hp)
  have hle : commSub A ≤
      commSub ((A ⊔ cj x A) ⊓ Qp p H) ⊓ commSub ((A ⊔ cj y A) ⊓ Qp p H) := by
    refine le_inf ?_ ?_
    · rw [hx']
      exact commSub_le_pair
    · rw [hy']
      exact commSub_le_pair
  rw [hinf] at hle
  exact hA.2.1 (le_bot_iff.mp hle)

theorem dec_commSub_K (hH : Hyp H) (hA : IsAVMin H A) {x : LGL p V} (hxQ : x ∈ Qp p H)
    (hx : x ∉ Subgroup.centralizer (A : Set (LGL p V))) :
    commSub ⁅Qp p H, A⁆ = commSub (A ⊔ cj x A) := by
  apply le_antisymm
  · rw [← dec_le_trivQuot_iff, commutator_eq_iSup hA]
    refine iSup₂_le fun y hy => (dec_le_trivQuot_iff _ _).mpr ?_
    rw [pair_commSub_Qx hH hA hy.1 hy.2]
    exact (dec_plane_eq hH hA hy.1 hy.2 hxQ hx).le
  · rw [← pair_commSub_Qx hH hA hxQ hx]
    exact commSub_mono _ _ (pair_Qx_le hA hxQ)

theorem dec_card_plane (hH : Hyp H) (hA : IsAVMin H A) :
    Nat.card (commSub ⁅Qp p H, A⁆) = p ^ 2 := by
  obtain ⟨x, hxQ, hx⟩ := dec_exists_x hH hA
  rw [dec_commSub_K hH hA hxQ hx]
  exact pair_card_comm hH hA hxQ hx

theorem dec_irr (hH : Hyp H) (hA : IsAVMin H A) {U : Submodule (ZMod p) V}
    (hU : U ≤ commSub ⁅Qp p H, A⁆) (hinv : ∀ g ∈ ⁅Qp p H, A⁆, ∀ u ∈ U, g u ∈ U) :
    U = ⊥ ∨ U = commSub ⁅Qp p H, A⁆ := by
  obtain ⟨x, hxQ, hx⟩ := dec_exists_x hH hA
  rw [dec_commSub_K hH hA hxQ hx] at hU ⊢
  exact pair_irred hH hA hxQ hx U hU fun g hg u hu => hinv g (pair_Qx_le hA hxQ hg) u hu

theorem dec_isCompl_K (hH : Hyp H) (hA : IsAVMin H A) :
    IsCompl (commSub ⁅Qp p H, A⁆) (fixSub ⁅Qp p H, A⁆) :=
  (isCompl_fixSub_commSub (dec_coprime_K hH hA)).symm

theorem dec_commSub_le (hH : Hyp H) (hA : IsAVMin H A) : commSub A ≤ commSub ⁅Qp p H, A⁆ := by
  obtain ⟨x, hxQ, hx⟩ := dec_exists_x hH hA
  rw [dec_commSub_K hH hA hxQ hx]
  exact commSub_le_pair

theorem dec_A_fix (hH : Hyp H) (hA : IsAVMin H A) {a : LGL p V} (ha : a ∈ A) {w : V}
    (hw : w ∈ fixSub ⁅Qp p H, A⁆) : a w = w := by
  have hn : a ∈ Subgroup.normalizer ((⁅Qp p H, A⁆ : Subgroup (LGL p V)) : Set (LGL p V)) :=
    dec_A_le_normalizer_comm hA.1.1 ha
  have h1 : a w ∈ fixSub ⁅Qp p H, A⁆ := map_mem_fixSub_of_mem_normalizer _ hn hw
  have h2 : a w - w ∈ commSub ⁅Qp p H, A⁆ := dec_commSub_le hH hA (sub_mem_commSub A ha w)
  have h3 : a w - w ∈ fixSub ⁅Qp p H, A⁆ := Submodule.sub_mem _ h1 hw
  have := (Submodule.disjoint_def.mp (dec_isCompl_K hH hA).disjoint) _ h2 h3
  exact sub_eq_zero.mp this

theorem dec_KA_fix (hH : Hyp H) (hA : IsAVMin H A) :
    ∀ g ∈ ⁅Qp p H, A⁆ ⊔ A, ∀ w ∈ fixSub ⁅Qp p H, A⁆, g w = w := by
  rw [← dec_le_kerOn_top_iff]
  exact sup_le (dec_le_kerOn_top_iff.mpr fun g hg w hw => hw g hg)
    (dec_le_kerOn_top_iff.mpr fun a ha w hw => dec_A_fix hH hA ha hw)

theorem dec_pair_le (hA : IsAVMin H A) {x : LGL p V} (hxQ : x ∈ Qp p H) :
    A ⊔ cj x A ≤ ⁅Qp p H, A⁆ ⊔ A := by
  refine le_trans (le_of_eq (pair_decomp hA hxQ).1) ?_
  exact sup_le le_sup_right (le_trans (pair_Qx_le hA hxQ) le_sup_left)

theorem dec_pair_eq (hH : Hyp H) (hA : IsAVMin H A) {x y : LGL p V} (hxQ : x ∈ Qp p H)
    (hx : x ∉ Subgroup.centralizer (A : Set (LGL p V))) (hyQ : y ∈ Qp p H)
    (hy : y ∉ Subgroup.centralizer (A : Set (LGL p V))) : A ⊔ cj y A = A ⊔ cj x A := by
  refine dec_block_eq (pair_isBlock hH hA hyQ hy).2
    (pair_isBlock hH hA hxQ hx).2 (dec_plane_eq hH hA hyQ hy hxQ hx)
    (W := fixSub ⁅Qp p H, A⁆) ?_ ?_ ?_
  · rw [← dec_commSub_K hH hA hyQ hy]
    exact dec_isCompl_K hH hA
  · exact fun g hg w hw => dec_KA_fix hH hA g (dec_pair_le hA hyQ hg) w hw
  · exact fun g hg w hw => dec_KA_fix hH hA g (dec_pair_le hA hxQ hg) w hw

theorem dec_KA_eq (hH : Hyp H) (hA : IsAVMin H A) {x : LGL p V} (hxQ : x ∈ Qp p H)
    (hx : x ∉ Subgroup.centralizer (A : Set (LGL p V))) :
    ⁅Qp p H, A⁆ ⊔ A = A ⊔ cj x A := by
  apply le_antisymm
  · refine sup_le ?_ le_sup_left
    rw [commutator_eq_iSup hA]
    refine iSup₂_le fun y hy => ?_
    exact le_trans inf_le_left (le_of_eq (dec_pair_eq hH hA hxQ hx hy.1 hy.2))
  · exact dec_pair_le hA hxQ

theorem dec_isBlock_KA (hH : Hyp H) (hA : IsAVMin H A) : IsBlock p (⁅Qp p H, A⁆ ⊔ A) := by
  obtain ⟨x, hxQ, hx⟩ := dec_exists_x hH hA
  rw [dec_KA_eq hH hA hxQ hx]
  exact (pair_isBlock hH hA hxQ hx).2

theorem dec_commSub_KA (hH : Hyp H) (hA : IsAVMin H A) :
    commSub (⁅Qp p H, A⁆ ⊔ A) = commSub ⁅Qp p H, A⁆ := by
  rw [dec_commSub_sup]
  exact sup_eq_left.mpr (dec_commSub_le hH hA)

theorem dec_fixSub_KA (hH : Hyp H) (hA : IsAVMin H A) :
    fixSub (⁅Qp p H, A⁆ ⊔ A) = fixSub ⁅Qp p H, A⁆ := by
  apply le_antisymm
  · exact fixSub_anti _ _ le_sup_left
  · intro w hw g hg
    exact dec_KA_fix hH hA g hg w hw

end Facts

section Analysis

open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {H : Subgroup (LGL p V)} {A B : Subgroup (LGL p V)}

theorem dec_dichotomy (hH : Hyp H) (hA : IsAVMin H A) (hB : IsAVMin H B) :
    commSub ⁅Qp p H, B⁆ ≤ commSub ⁅Qp p H, A⁆ ∨ commSub ⁅Qp p H, B⁆ ≤ fixSub ⁅Qp p H, A⁆ := by
  have hKB : ⁅Qp p H, B⁆ ≤ Qp p H := dec_comm_le_Qp hB.1.1
  have hnorm : ∀ g ∈ (⁅Qp p H, B⁆ : Subgroup (LGL p V)),
      g ∈ Subgroup.normalizer ((⁅Qp p H, A⁆ : Subgroup (LGL p V)) : Set (LGL p V)) :=
    fun g hg => dec_Qp_le_normalizer_comm (hKB hg)
  have hVA : ∀ g ∈ (⁅Qp p H, B⁆ : Subgroup (LGL p V)), ∀ v ∈ commSub ⁅Qp p H, A⁆,
      g v ∈ commSub ⁅Qp p H, A⁆ :=
    fun g hg v hv => map_mem_commSub_of_mem_normalizer _ (hnorm g hg) hv
  have hWA : ∀ g ∈ (⁅Qp p H, B⁆ : Subgroup (LGL p V)), ∀ v ∈ fixSub ⁅Qp p H, A⁆,
      g v ∈ fixSub ⁅Qp p H, A⁆ :=
    fun g hg v hv => map_mem_fixSub_of_mem_normalizer _ (hnorm g hg) hv
  have hVB : ∀ g ∈ (⁅Qp p H, B⁆ : Subgroup (LGL p V)), ∀ v ∈ commSub ⁅Qp p H, B⁆,
      g v ∈ commSub ⁅Qp p H, B⁆ :=
    fun g hg v hv => map_mem_commSub _ hg hv
  have h1 := dec_irr hH hB (U := commSub ⁅Qp p H, B⁆ ⊓ commSub ⁅Qp p H, A⁆) inf_le_left
    (fun g hg u hu => ⟨hVB g hg u hu.1, hVA g hg u hu.2⟩)
  have h2 := dec_irr hH hB (U := commSub ⁅Qp p H, B⁆ ⊓ fixSub ⁅Qp p H, A⁆) inf_le_left
    (fun g hg u hu => ⟨hVB g hg u hu.1, hWA g hg u hu.2⟩)
  have hsum : commSub ⁅Qp p H, B⁆ ≤
      (commSub ⁅Qp p H, B⁆ ⊓ commSub ⁅Qp p H, A⁆) ⊔ (commSub ⁅Qp p H, B⁆ ⊓ fixSub ⁅Qp p H, A⁆) := by
    rw [commSub_le_iff]
    intro g hg v
    have hv : v ∈ commSub ⁅Qp p H, A⁆ ⊔ fixSub ⁅Qp p H, A⁆ := by
      rw [(dec_isCompl_K hH hA).sup_eq_top]
      trivial
    obtain ⟨vA, hvA, vW, hvW, rfl⟩ := Submodule.mem_sup.mp hv
    have e : g (vA + vW) - (vA + vW) = (g vA - vA) + (g vW - vW) := by
      rw [map_add]
      abel
    rw [e]
    refine Submodule.add_mem_sup ?_ ?_
    · exact ⟨sub_mem_commSub _ hg vA, Submodule.sub_mem _ (hVA g hg vA hvA) hvA⟩
    · exact ⟨sub_mem_commSub _ hg vW, Submodule.sub_mem _ (hWA g hg vW hvW) hvW⟩
  have hne : commSub ⁅Qp p H, B⁆ ≠ ⊥ := dec_ne_bot_of_card (dec_card_plane hH hB)
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exfalso
      apply hne
      rw [h1, h2, sup_bot_eq] at hsum
      exact le_bot_iff.mp hsum
    · exact Or.inr (inf_eq_left.mp h2)
  · exact Or.inl (inf_eq_left.mp h1)

theorem dec_cases (hH : Hyp H) (hA : IsAVMin H A) (hB : IsAVMin H B) :
    B ≤ ⁅Qp p H, A⁆ ⊔ A ∨
      ((∀ b ∈ B, ∀ v ∈ commSub ⁅Qp p H, A⁆, b v = v) ∧
        ∀ b ∈ B, ∀ e ∈ ⁅Qp p H, A⁆ ⊔ A, b * e = e * b) := by
  have hcardA := dec_card_plane hH hA
  have hcardB := dec_card_plane hH hB
  have hKB : ⁅Qp p H, B⁆ ≤ Qp p H := dec_comm_le_Qp hB.1.1
  rcases dec_dichotomy hH hA hB with h | h
  · left
    have hVeq : commSub ⁅Qp p H, B⁆ = commSub ⁅Qp p H, A⁆ :=
      dec_eq_of_le_of_card_le h (by rw [hcardA, hcardB])
    have hKBnorm : ∀ g ∈ (⁅Qp p H, B⁆ : Subgroup (LGL p V)),
        g ∈ Subgroup.normalizer ((⁅Qp p H, A⁆ : Subgroup (LGL p V)) : Set (LGL p V)) :=
      fun g hg => dec_Qp_le_normalizer_comm (hKB hg)
    have hKBtriv : ∀ g ∈ (⁅Qp p H, B⁆ : Subgroup (LGL p V)), ∀ w ∈ fixSub ⁅Qp p H, A⁆,
        g w = w := by
      intro g hg w hw
      have h1 : g w ∈ fixSub ⁅Qp p H, A⁆ :=
        map_mem_fixSub_of_mem_normalizer _ (hKBnorm g hg) hw
      have h2 : g w - w ∈ commSub ⁅Qp p H, A⁆ := hVeq ▸ sub_mem_commSub _ hg w
      have h3 : g w - w ∈ fixSub ⁅Qp p H, A⁆ := Submodule.sub_mem _ h1 hw
      exact sub_eq_zero.mp
        ((Submodule.disjoint_def.mp (dec_isCompl_K hH hA).disjoint) _ h2 h3)
    have hWle : fixSub ⁅Qp p H, A⁆ ≤ fixSub ⁅Qp p H, B⁆ := fun w hw g hg => hKBtriv g hg w hw
    have hWeq : fixSub ⁅Qp p H, A⁆ = fixSub ⁅Qp p H, B⁆ := by
      apply dec_eq_of_le_of_card_le hWle
      have h1 := dec_card_mul_of_isCompl (dec_isCompl_K hH hA)
      have h2 := dec_card_mul_of_isCompl (dec_isCompl_K hH hB)
      rw [hVeq] at h2
      have hpos : 0 < Nat.card (commSub ⁅Qp p H, A⁆) := Nat.card_pos
      exact le_of_eq (Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm))
    have hEB : ⁅Qp p H, B⁆ ⊔ B = ⁅Qp p H, A⁆ ⊔ A := by
      refine dec_block_eq (dec_isBlock_KA hH hB) (dec_isBlock_KA hH hA)
        (W := fixSub ⁅Qp p H, A⁆) ?_ ?_ ?_ ?_
      · rw [dec_commSub_KA hH hB, dec_commSub_KA hH hA, hVeq]
      · rw [dec_commSub_KA hH hB, hVeq]
        exact dec_isCompl_K hH hA
      · intro g hg w hw
        rw [hWeq] at hw
        exact dec_KA_fix hH hB g hg w hw
      · intro g hg w hw
        exact dec_KA_fix hH hA g hg w hw
    rw [← hEB]
    exact le_sup_right
  · right
    have hVAWB : commSub ⁅Qp p H, A⁆ ≤ fixSub ⁅Qp p H, B⁆ := by
      rcases dec_dichotomy hH hB hA with h' | h'
      · exfalso
        have hVeq : commSub ⁅Qp p H, A⁆ = commSub ⁅Qp p H, B⁆ :=
          dec_eq_of_le_of_card_le h' (by rw [hcardA, hcardB])
        have hle : commSub ⁅Qp p H, A⁆ ≤ fixSub ⁅Qp p H, A⁆ := hVeq ▸ h
        have hbot : commSub ⁅Qp p H, A⁆ = ⊥ :=
          (dec_isCompl_K hH hA).disjoint.eq_bot_of_le hle
        exact dec_ne_bot_of_card hcardA hbot
      · exact h'
    have hBVA : ∀ b ∈ B, ∀ v ∈ commSub ⁅Qp p H, A⁆, b v = v :=
      fun b hb v hv => dec_A_fix hH hB hb (hVAWB hv)
    refine ⟨hBVA, ?_⟩
    intro b hb e he
    refine (dec_comm_of_split (dec_isCompl_K hH hA) ?_ ?_ (hBVA b hb) ?_).symm
    · intro u hu
      rw [← dec_commSub_KA hH hA] at hu ⊢
      exact map_mem_commSub _ he hu
    · intro w hw
      exact dec_KA_fix hH hA e he w hw
    · intro w hw
      have h1 : b w - w ∈ fixSub ⁅Qp p H, A⁆ :=
        h (dec_commSub_le hH hB (sub_mem_commSub B hb w))
      have := Submodule.add_mem _ h1 hw
      simpa using this

end Analysis

section Blk

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem dec_mem_blk {H A : Subgroup (LGL p V)} {h : LGL p V} (hh : h ∈ H) {a : LGL p V}
    (ha : a ∈ A) : h * a * h⁻¹ ∈ blk H A :=
  Subgroup.mem_iSup_of_mem h
    (Subgroup.mem_iSup_of_mem hh (Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩))

theorem dec_le_blk {H A : Subgroup (LGL p V)} : A ≤ blk H A := by
  intro a ha
  have := dec_mem_blk H.one_mem ha
  simpa using this

theorem dec_blk_le_of_normalizes {H A N : Subgroup (LGL p V)}
    (hN : ∀ h ∈ H, h ∈ Subgroup.normalizer (N : Set (LGL p V))) (hAN : A ≤ N) :
    blk H A ≤ N := by
  refine iSup₂_le fun h hh => ?_
  rintro _ ⟨a, ha, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (hN h hh) a).mp (hAN ha)
  simpa [MulAut.conj_apply] using this

theorem dec_blk_le_of_le {H A : Subgroup (LGL p V)} (hAH : A ≤ H) : blk H A ≤ H :=
  dec_blk_le_of_normalizes (fun _ hh => Subgroup.le_normalizer hh) hAH

theorem dec_cj_blk_le {H A : Subgroup (LGL p V)} {g : LGL p V} (hg : g ∈ H) :
    cj g (blk H A) ≤ blk H A := by
  refine Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun h hh => ?_)
  rintro _ ⟨a, ha, rfl⟩
  have := dec_mem_blk (H.mul_mem hg hh) ha
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem dec_mem_normalizer_blk {H A : Subgroup (LGL p V)} {g : LGL p V} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer ((blk H A : Subgroup (LGL p V)) : Set (LGL p V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ cj g (blk H A) :=
      Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    exact dec_cj_blk_le hg this
  · intro hx
    have : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ cj g⁻¹ (blk H A) :=
      Subgroup.mem_map.mpr ⟨_, hx, by simp⟩
    have h2 := dec_cj_blk_le (H.inv_mem hg) this
    simpa [mul_assoc] using h2

theorem dec_blk_le {H A : Subgroup (LGL p V)} (hA : IsAVMin H A) : blk H A ≤ H :=
  dec_blk_le_of_le hA.1.1

theorem dec_normal (H A : Subgroup (LGL p V)) :
    ((kerOn H (commSub (blk H A))).subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine ⟨H.mul_mem (H.mul_mem g.2 n.2) (H.inv_mem g.2), fun w hw => ?_⟩
  have h1 : ((g⁻¹ : H) : LGL p V) w ∈ commSub (blk H A) :=
    map_mem_commSub_of_mem_normalizer _ (dec_mem_normalizer_blk (g⁻¹).2) hw
  change (g : LGL p V) ((n : LGL p V) (((g⁻¹ : H) : LGL p V) w)) = w
  rw [hn.2 _ h1]
  exact apply_inv_apply' (g : LGL p V) w

end Blk

section Main

open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {H : Subgroup (LGL p V)} {A : Subgroup (LGL p V)}

theorem dec_normalizes (hH : Hyp H)
    (hGen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H) (hA : IsAVMin H A) :
    H ≤ Subgroup.normalizer ((⁅Qp p H, A⁆ ⊔ A : Subgroup (LGL p V)) : Set (LGL p V)) := by
  refine le_trans (le_of_eq hGen.symm) (iSup₂_le fun B hB => ?_)
  rcases dec_cases hH hA hB with h | ⟨_, hcomm⟩
  · exact h.trans Subgroup.le_normalizer
  · exact dec_le_normalizer_of_commute hcomm

end Main

open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {H : Subgroup (LGL p V)}

section

variable (hH : Hyp H) (hGen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H)
  {A : Subgroup (LGL p V)} (hA : IsAVMin H A)

include hH hGen hA

theorem dec_blk_eq : blk H A = ⁅Qp p H, A⁆ ⊔ A := by
  apply le_antisymm
  · exact dec_blk_le_of_normalizes (fun h hh => dec_normalizes hH hGen hA hh) le_sup_right
  · refine sup_le ?_ dec_le_blk
    rw [Subgroup.commutator_le]
    intro q hq a ha
    rw [commutatorElement_def]
    exact (blk H A).mul_mem (dec_mem_blk (Qp_le H hq) ha) ((blk H A).inv_mem (dec_le_blk ha))

theorem dec_isBlock : (p = 2 ∨ p = 3) ∧ IsBlock p (blk H A) := by
  rw [dec_blk_eq hH hGen hA]
  exact ⟨dec_two_three hH hA, dec_isBlock_KA hH hA⟩

theorem dec_isCompl : IsCompl (commSub (blk H A)) (fixSub (blk H A)) := by
  rw [dec_blk_eq hH hGen hA, dec_commSub_KA hH hA, dec_fixSub_KA hH hA]
  exact dec_isCompl_K hH hA

theorem dec_avmin {B : Subgroup (LGL p V)} (hB : IsAVMin H B) :
    B ≤ blk H A ∨ B ≤ kerOn H (commSub (blk H A)) := by
  rw [dec_blk_eq hH hGen hA, dec_commSub_KA hH hA]
  rcases dec_cases hH hA hB with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr fun b hb => ⟨hB.1.1 hb, fun v hv => h b hb v hv⟩

theorem dec_sup : blk H A ⊔ kerOn H (commSub (blk H A)) = H := by
  apply le_antisymm
  · exact sup_le (dec_blk_le hA) fun g hg => hg.1
  · refine le_trans (le_of_eq hGen.symm) (iSup₂_le fun B hB => ?_)
    rcases dec_avmin hH hGen hA hB with h | h
    · exact h.trans le_sup_left
    · exact h.trans le_sup_right

theorem dec_inf : blk H A ⊓ kerOn H (commSub (blk H A)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact (dec_isBlock hH hGen hA).2.faithful g hg.1 hg.2.2

theorem dec_commute : ∀ e ∈ blk H A, ∀ f ∈ kerOn H (commSub (blk H A)), e * f = f * e := by
  intro e he f hf
  refine dec_comm_of_split (dec_isCompl hH hGen hA) (fun u hu => map_mem_commSub _ he hu)
    (fun w hw => hw e he) (fun u hu => hf.2 u hu) fun w hw => ?_
  exact map_mem_fixSub_of_mem_normalizer _ (dec_mem_normalizer_blk hf.1) hw

theorem dec_commSub_ker : commSub (kerOn H (commSub (blk H A))) ≤ fixSub (blk H A) := by
  rw [commSub_le_iff]
  intro f hf v
  have hv : v ∈ commSub (blk H A) ⊔ fixSub (blk H A) := by
    rw [(dec_isCompl hH hGen hA).sup_eq_top]
    trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  have h1 : f w ∈ fixSub (blk H A) :=
    map_mem_fixSub_of_mem_normalizer _ (dec_mem_normalizer_blk hf.1) hw
  have e : f (u + w) - (u + w) = f w - w := by
    rw [map_add, hf.2 u hu]
    abel
  rw [e]
  exact Submodule.sub_mem _ h1 hw

theorem dec_blk_of_le {B : Subgroup (LGL p V)} (hB : IsAVMin H B) (hBA : B ≤ blk H A) :
    blk H B = blk H A := by
  have hle : blk H B ≤ blk H A :=
    dec_blk_le_of_normalizes (fun _ hh => dec_mem_normalizer_blk hh) hBA
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [(dec_isBlock hH hGen hA).2.card, (dec_isBlock hH hGen hB).2.card]

end

end CFSG.SignalizerFunctorTheorem.Quadratic
