module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434L34
public import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Alt

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

section Perfect

variable {G M : Type*} [Group G] [Group M]

theorem commutatorElement_mul_left_of_mem_center {a z : G} (hz : z ∈ Subgroup.center G) (b : G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b = b * z := (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_right_of_mem_center (a : G) {b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a⁻¹ = a⁻¹ * z := (Subgroup.mem_center_iff.mp hz a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hza]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_top_of_range_le_map [Group.IsPerfect G] (φ : G →* M)
    (hker : φ.ker ≤ Subgroup.center G) {R : Subgroup G} (hR : φ.range ≤ R.map φ) : R = ⊤ := by
  have key : ∀ g : G, ∃ r ∈ R, ∃ z ∈ Subgroup.center G, g = r * z := by
    intro g
    obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp (hR (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
    refine ⟨r, hr, r⁻¹ * g, hker ?_, (mul_inv_cancel_left r g).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrg, inv_mul_cancel]
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G), commutator_def,
    Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨r₁, hr₁, z₁, hz₁, rfl⟩ := key g₁
  obtain ⟨r₂, hr₂, z₂, hz₂, rfl⟩ := key g₂
  rw [commutatorElement_mul_left_of_mem_center hz₁,
    commutatorElement_mul_right_of_mem_center r₁ hz₂, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)

end Perfect

section Lift

variable {G H : Type*} [Group G] [Group H]

theorem card_eq_card_inf_ker_mul_card_map (f : G →* H) (X : Subgroup G) :
    Nat.card X = Nat.card (X ⊓ f.ker : Subgroup G) * Nat.card (X.map f) := by
  set f' : X →* H := f.comp X.subtype with hf'
  have hrange : f'.range = X.map f := by
    rw [hf', MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f'.ker = f.ker.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf', MonoidHom.comp_apply,
      Subgroup.coe_subtype, MonoidHom.mem_ker]
  have hcard : Nat.card f'.ker = Nat.card (X ⊓ f.ker : Subgroup G) := by
    rw [hker, ← Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← Subgroup.card_mul_index f'.ker, Subgroup.index_ker, hrange, hcard]

theorem card_inf_comap (f : G →* H) {A : Subgroup G} {P : Subgroup H} (hP : P ≤ A.map f) :
    Nat.card (A ⊓ P.comap f : Subgroup G) = Nat.card (A ⊓ f.ker : Subgroup G) * Nat.card P := by
  rw [card_eq_card_inf_ker_mul_card_map f (A ⊓ P.comap f)]
  have h1 : A ⊓ P.comap f ⊓ f.ker = A ⊓ f.ker := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    intro x hx
    obtain ⟨hxA, hxk⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxA, ?_⟩, hxk⟩
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hxk]
    exact P.one_mem
  have h2 : (A ⊓ P.comap f).map f = P := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := hP hp
      exact ⟨a, ⟨ha, hp⟩, rfl⟩
  rw [h1, h2]

theorem exists_coprime_lift (f : G →* H) {L : Subgroup G} (hZ : IsPGroup 3 (L ⊓ f.ker : Subgroup G))
    {x : G} (hx : x ∈ L) (hσ : Nat.Coprime (orderOf (f x)) 3) :
    ∃ y ∈ L, f y = f x ∧ Nat.Coprime (orderOf y) 3 := by
  set m := orderOf (f x) with hm
  have hxm : x ^ m ∈ L ⊓ f.ker :=
    Subgroup.mem_inf.mpr ⟨pow_mem hx m, by rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]⟩
  obtain ⟨k, hk⟩ := hZ ⟨x ^ m, hxm⟩
  have hk' : (x ^ m) ^ (3 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) (orderOf (f x)) :=
    Nat.Coprime.pow_left k (Nat.coprime_comm.mp hσ)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨x ^ (3 ^ k * u), pow_mem hx _, by rw [map_pow, pow_mul, hu], ?_⟩
  have hy : (x ^ (3 ^ k * u)) ^ m = 1 := by
    rw [← pow_mul, show 3 ^ k * u * m = m * 3 ^ k * u by ring, pow_mul, pow_mul, hk', one_pow]
  exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hy) hσ

theorem eq_of_coprime_lift (f : G →* H) {L : Subgroup G} (hZ : IsPGroup 3 (L ⊓ f.ker : Subgroup G))
    (hcen : ∀ z ∈ L ⊓ f.ker, ∀ l ∈ L, z * l = l * z) {y y' : G} (hy : y ∈ L) (hy' : y' ∈ L)
    (hf : f y = f y') (h3 : Nat.Coprime (orderOf y) 3) (h3' : Nat.Coprime (orderOf y') 3) :
    y = y' := by
  set z := y⁻¹ * y' with hzdef
  have hz : z ∈ L ⊓ f.ker :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hy) hy',
      by rw [MonoidHom.mem_ker, map_mul, map_inv, hf, inv_mul_cancel]⟩
  have hyz : y' = y * z := by rw [hzdef, mul_inv_cancel_left]
  have hcomm : Commute y z := (hcen z hz y hy).symm
  set N := orderOf y * orderOf y' with hN
  have hzN : z ^ N = 1 := by
    have h1 : y' ^ N = 1 := by
      rw [hN, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [hyz, hcomm.mul_pow, hN, pow_mul, pow_orderOf_eq_one, one_pow, one_mul] at h1
    rw [hN]
    exact h1
  obtain ⟨k, hk⟩ := hZ ⟨z, hz⟩
  have hk' : z ^ (3 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) N :=
    Nat.Coprime.pow_left k (Nat.coprime_comm.mp (Nat.Coprime.mul_left h3 h3'))
  have hd : orderOf z ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hzN)
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [hyz, hz1, mul_one]

end Lift

section QuotConj

variable {G : Type} [Group G] {X : Type*} [Group X]

@[expose] noncomputable def quotConj (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    G →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp ((KFacts.centerDescend (layer G)).comp (layerConj G))

theorem quotConj_apply_mk (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (g : G) (x : layer G) :
    quotConj e g (e (x : layer G ⧸ Subgroup.center (layer G))) =
      e ((layerConj G g x : layer G) : layer G ⧸ Subgroup.center (layer G)) := by
  simp [quotConj, MulAut.congr_apply, KFacts.centerDescend_mk]

theorem quotConj_eq_one_iff (hL : IsQuasisimple (layer G))
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {g : G} :
    quotConj e g = 1 ↔ g ∈ Subgroup.centralizer (layer G : Set G) := by
  rw [← layerConj_eq_one_iff]
  constructor
  · intro hg
    apply Item434L34.eq_one_of_centerDescend_eq_one hL
    have h1 : MulAut.congr e (KFacts.centerDescend (layer G) (layerConj G g)) = 1 := hg
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  · intro hg
    change MulAut.congr e (KFacts.centerDescend (layer G) (layerConj G g)) = 1
    rw [hg, map_one, map_one]

theorem layerConj_of_mem {l : G} (hl : l ∈ layer G) :
    layerConj G l = MulAut.conj (⟨l, hl⟩ : layer G) := by
  ext x
  rw [layerConj_apply_coe]
  rfl

theorem quotConj_of_mem (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {l : G}
    (hl : l ∈ layer G) :
    quotConj e l =
      MulAut.conj (e ((⟨l, hl⟩ : layer G) : layer G ⧸ Subgroup.center (layer G))) := by
  change MulAut.congr e (KFacts.centerDescend (layer G) (layerConj G l)) = _
  rw [layerConj_of_mem hl, KFacts.centerDescend_conj, KFacts.congr_mulAutConj]

end QuotConj

section AltPerm

variable {n : ℕ}

@[expose] noncomputable def permEquiv (hn : n = 5 ∨ 7 ≤ n) :
    Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective (CFSG.Quasithin.SteinbergCB.conjPerm n)
    ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by omega),
      CFSG.Quasithin.SteinbergCB.conjPerm_surjective hn⟩

theorem permEquiv_apply (hn : n = 5 ∨ 7 ≤ n) (σ : Perm (Fin n)) :
    permEquiv hn σ = CFSG.Quasithin.SteinbergCB.conjPerm n σ :=
  rfl

theorem conjPerm_coe (τ : alternatingGroup (Fin n)) :
    CFSG.Quasithin.SteinbergCB.conjPerm n (τ : Perm (Fin n)) = MulAut.conj τ := by
  ext g
  rw [CFSG.Quasithin.SteinbergCB.conjPerm_apply, MulAut.conj_apply]
  rfl

theorem permEquiv_symm_conj (hn : n = 5 ∨ 7 ≤ n) (τ : alternatingGroup (Fin n)) :
    (permEquiv hn).symm (MulAut.conj τ) = (τ : Perm (Fin n)) := by
  rw [MulEquiv.symm_apply_eq, permEquiv_apply, conjPerm_coe]

variable {G : Type} [Group G]

@[expose] noncomputable def altPerm (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) : G →* Perm (Fin n) :=
  (permEquiv hn).symm.toMonoidHom.comp (quotConj e)

theorem altPerm_of_mem (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) {l : G}
    (hl : l ∈ layer G) :
    altPerm hn e l =
      (e ((⟨l, hl⟩ : layer G) : layer G ⧸ Subgroup.center (layer G)) : Perm (Fin n)) := by
  change (permEquiv hn).symm (quotConj e l) = _
  rw [quotConj_of_mem e hl, permEquiv_symm_conj]

theorem altPerm_eq_one_iff (hL : IsQuasisimple (layer G)) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) {g : G} :
    altPerm hn e g = 1 ↔ g ∈ Subgroup.centralizer (layer G : Set G) := by
  rw [← quotConj_eq_one_iff hL e]
  change (permEquiv hn).symm (quotConj e g) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]

theorem ker_altPerm (hL : IsQuasisimple (layer G)) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) :
    (altPerm hn e).ker = Subgroup.centralizer (layer G : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, altPerm_eq_one_iff hL]

theorem map_layer_altPerm (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) :
    (layer G).map (altPerm hn e) = alternatingGroup (Fin n) := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    rw [altPerm_of_mem hn e hl]
    exact SetLike.coe_mem _
  · intro σ hσ
    obtain ⟨y, hy⟩ := e.surjective ⟨σ, hσ⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨x, x.2, ?_⟩
    rw [altPerm_of_mem hn e x.2]
    exact congrArg Subtype.val hy

theorem layer_inf_ker_altPerm (hL : IsQuasisimple (layer G)) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) :
    layer G ⊓ (altPerm hn e).ker = (Subgroup.center (layer G)).map (layer G).subtype := by
  rw [ker_altPerm hL, CFSG.GroupTheory.inf_centralizer_eq_map_center]

end AltPerm

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {n : ℕ}

theorem isPGroup_layer_inf_ker (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) :
    IsPGroup 3 (layer G ⊓ (altPerm hn e).ker : Subgroup G) := by
  rw [layer_inf_ker_altPerm h.isQuasisimple]
  exact h.isPGroup_center_layer.map _

theorem layer_inf_ker_central (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) :
    ∀ z ∈ layer G ⊓ (altPerm hn e).ker, ∀ l ∈ layer G, z * l = l * z := by
  intro z hz l hl
  rw [ker_altPerm h.isQuasisimple] at hz
  exact (Subgroup.mem_centralizer_iff.mp hz.2 l hl).symm

theorem center_layer_eq_bot_of_eight_le (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    Subgroup.center (layer G) = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  set η : layer G →* alternatingGroup (Fin (m + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (layer G))) with hη
  have hsurj : Function.Surjective η :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center (layer G) := by
    ext x
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card η.ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hsurj
    (by rw [hker]) hodd
  rw [hker] at h1
  exact Subgroup.card_eq_one.mp h1

theorem inf_centralizer_layer_eq_bot_of_le (h : Ctx434Core G A M Q)
    (hZ : Subgroup.center (layer G) = ⊥) {D : Subgroup G} (hDL : D ≤ layer G)
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27) :
    A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have hZL : ¬ A ⊓ Subgroup.centralizer (layer G : Set G) ≤
      (Subgroup.center (layer G)).map (layer G).subtype := by
    rw [hZ, Subgroup.map_bot, le_bot_iff]
    exact hne
  have hrank := (h.rank3II_4_39 hne hZL).1
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨hzA, hzC⟩ := Subgroup.mem_inf.mp z.2
  have hz3 : (z : G) ^ 3 = 1 := h.isE27.1.2 z hzA
  have hLC : layer G ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center, hZ, Subgroup.map_bot]
  have hzD : (z : G) ∉ D := by
    intro hzD
    have hmem : (z : G) ∈ layer G ⊓ Subgroup.centralizer (layer G : Set G) :=
      Subgroup.mem_inf.mpr ⟨hDL hzD, hzC⟩
    rw [hLC, Subgroup.mem_bot] at hmem
    exact hz1 (Subtype.ext hmem)
  obtain ⟨hFe, hFcard⟩ := Sec5.isElemAbelian_sup_zpowers hD hzD hz3
    fun d hd => Subgroup.mem_centralizer_iff.mp hzC d (hDL hd)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨_, le_top, hFe, by rw [hFcard, hD27]; norm_num⟩
  omega

theorem layer_le_of_gens (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n))
    {S : Set (Perm (Fin n))} (hS : alternatingGroup (Fin n) ≤ Subgroup.closure S)
    (hgen : ∀ σ ∈ S, σ ∈ alternatingGroup (Fin n) ∧ Nat.Coprime (orderOf σ) 3 ∧
      ∃ B : Subgroup G, B ≤ A ∧ 9 ≤ Nat.card B ∧
        ∀ b ∈ B, altPerm hn e b * σ = σ * altPerm hn e b) :
    layer G ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  set β := altPerm hn e with hβ
  have hZ := isPGroup_layer_inf_ker h hn e
  have hcen := layer_inf_ker_central h hn e
  have hlift : ∀ σ ∈ S, ∃ y ∈ layer G, y ∈ M ∧ β y = σ := by
    intro σ hσ
    obtain ⟨hσA, hσ3, B, hBA, hB9, hBσ⟩ := hgen σ hσ
    rw [← map_layer_altPerm hn e] at hσA
    obtain ⟨x, hxL, hxσ⟩ := hσA
    obtain ⟨y, hyL, hyx, hy3⟩ := exists_coprime_lift β hZ hxL (by rw [hxσ]; exact hσ3)
    rw [hxσ] at hyx
    refine ⟨y, hyL, ?_, hyx⟩
    have hyB : y ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hconj : b * y * b⁻¹ = y := by
        have : (layer G).Characteristic := layer_characteristic
        have : (layer G).Normal := inferInstance
        refine eq_of_coprime_lift β hZ hcen (this.conj_mem y hyL b) hyL ?_ ?_ hy3
        · rw [map_mul, map_mul, map_inv, hyx, hBσ b hb, mul_inv_cancel_right]
        · have ho := orderOf_injective (MulAut.conj b).toMonoidHom (MulAut.conj b).injective y
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ho
          rw [ho]
          exact hy3
      calc b * y = b * y * b⁻¹ * b := by group
        _ = y * b := by rw [hconj]
    have hBe : CFSG.Assembly.IsElemAbelian 3 B := Source.isElemAbelian_of_le h.isE27.1 hBA
    obtain ⟨k, hk⟩ := (h.isE27.isPGroup.to_le hBA).exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := B) (n := 2)
      (by rw [hk]; exact pow_dvd_pow 3 hk2)
    have hKe : CFSG.Assembly.IsElemAbelian 3 (K.map B.subtype) :=
      Source.isElemAbelian_of_le hBe (Subgroup.map_subtype_le K)
    have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
      le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
        ⟨_, Subgroup.map_subtype_le K, hKe,
          by rw [Subgroup.card_map_of_injective B.subtype_injective, hK]⟩
    exact ((Subgroup.centralizer_le_normalizer _).trans
      ((normalizer_le_gamma hBA hB2).trans h.gamma_le)) hyB
  set φ : layer G →* Perm (Fin n) := β.comp (layer G).subtype with hφ
  set R : Subgroup (layer G) := M.comap (layer G).subtype with hR
  have hker : φ.ker ≤ Subgroup.center (layer G) := by
    intro x hx
    have hmem : (x : G) ∈ layer G ⊓ β.ker := ⟨x.2, hx⟩
    rw [layer_inf_ker_altPerm h.isQuasisimple] at hmem
    obtain ⟨z, hz, hzx⟩ := hmem
    rw [show x = z from Subtype.ext hzx.symm]
    exact hz
  have hrange : φ.range = (alternatingGroup (Fin n)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, map_layer_altPerm]
  have hRmap : alternatingGroup (Fin n) ≤ R.map φ := by
    refine hS.trans ((Subgroup.closure_le _).mpr fun σ hσ => ?_)
    obtain ⟨y, hyL, hyM, hyσ⟩ := hlift σ hσ
    exact ⟨⟨y, hyL⟩, hyM, hyσ⟩
  have htop := eq_top_of_range_le_map φ hker (hrange.symm ▸ hRmap)
  intro x hx
  have hmem : (⟨x, hx⟩ : layer G) ∈ R := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434Alt
