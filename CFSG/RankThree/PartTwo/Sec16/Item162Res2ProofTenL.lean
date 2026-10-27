module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofAxis
public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofSeven
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofPerm
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofAct

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 Equiv
  Equiv.Perm
open CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec17.Proof171Gen
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)
open scoped commutatorElement

theorem le_eSeven_of_perfect {H : Subgroup (Perm (Fin 10))}
    (hH : H ≤ Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10))
    (hHp : ⁅H, H⁆ = H) : H ≤ (alternatingGroup (Fin 7)).map embedSeven := by
  have hc : ∀ σ : Perm (Fin 7), Commute (embedSeven σ) dThree := embedSeven_commute
  rw [← hHp, Subgroup.commutator_le]
  intro u hu v hv
  obtain ⟨i, σ, hσ, rfl⟩ := exists_eq_of_commute_dThree_of_mem
    (Subgroup.mem_centralizer_singleton_iff.mp (hH hu).1) (hH hu).2
  obtain ⟨j, τ, hτ, rfl⟩ := exists_eq_of_commute_dThree_of_mem
    (Subgroup.mem_centralizer_singleton_iff.mp (hH hv).1) (hH hv).2
  rw [commutatorElement_mul_of_commute ((hc σ).pow_right _).symm ((hc τ).pow_right _).symm
    ((hc σ).pow_right _).symm ((hc τ).pow_right _).symm (Commute.pow_pow_self dThree _ _),
    ← map_commutatorElement]
  refine ⟨⁅σ, τ⁆, ?_, rfl⟩
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)

theorem exists_conj_eq_dThree {x : Perm (Fin 10)} (hx : x.IsThreeCycle) :
    ∃ h : Perm (Fin 10), h * x * h⁻¹ = dThree :=
  isConj_iff.mp (isConj_iff_cycleType_eq.mpr (hx.trans isThreeCycle_dThree.symm))

theorem card_le_of_perfect_of_isThreeCycle {x : Perm (Fin 10)} (hx : x.IsThreeCycle)
    {H : Subgroup (Perm (Fin 10))}
    (hH : H ≤ Subgroup.centralizer ({x} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10))
    (hHp : ⁅H, H⁆ = H) : Nat.card H ≤ 2520 := by
  obtain ⟨h, hh⟩ := exists_conj_eq_dThree hx
  have hconj : H.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hH hy).1
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · change h * y * h⁻¹ * dThree = dThree * (h * y * h⁻¹)
      rw [← hh]
      calc h * y * h⁻¹ * (h * x * h⁻¹) = h * (y * x) * h⁻¹ := by group
        _ = h * (x * y) * h⁻¹ := by rw [hyx]
        _ = h * x * h⁻¹ * (h * y * h⁻¹) := by group
    · exact (Subgroup.Normal.conj_mem inferInstance y (hH hy).2 h)
  have hle := le_eSeven_of_perfect hconj (by rw [← Subgroup.map_commutator, hHp])
  have h1 := Subgroup.card_le_of_le hle
  rwa [card_map_embedSeven, Subgroup.card_map_of_injective (MulAut.conj h).injective] at h1

theorem axisElt_support_card : ∀ e : Fin 6, (axisElt e).support.card = 3 := by
  decide +kernel

noncomputable def eSevenEquiv :
    ↥((alternatingGroup (Fin 7)).map embedSeven) ≃* alternatingGroup (Fin 7) :=
  ((alternatingGroup (Fin 7)).equivMapOfInjective embedSeven embedSeven_injective).symm

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_comm_image {X Y : Subgroup G} (hXY : X ≤ Y) {Q : Type*} [Group Q]
    (f : ↥Y →* Q) (hker : IsPGroup 2 f.ker)
    (hcomm : ∀ x : ↥X, ∀ x' : ↥X, f (Subgroup.inclusion hXY x) * f (Subgroup.inclusion hXY x') =
      f (Subgroup.inclusion hXY x') * f (Subgroup.inclusion hXY x)) :
    Group.IsSolvable ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥X →* Q := f.comp (Subgroup.inclusion hXY) with hφ
  have hc : ∀ a b : ↥φ.range, a * b = b * a := by
    rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
    exact Subtype.ext (hcomm x y)
  have hsolR : Group.IsSolvable ↥φ.range := Group.isSolvable_of_comm hc
  have hker2 : IsPGroup 2 ↥φ.ker := by
    rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := hker ⟨Subgroup.inclusion hXY k, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥f.ker => ((z : ↥Y) : G)) hn
    simpa using this
  have hnil : Group.IsNilpotent ↥φ.ker := hker2.isNilpotent
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem theta_le_pCoreOf_of_ten {Y L : Subgroup G} {c : G} (hLY : L ≤ Y) (hcY : c ∈ Y)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hLp : Group.IsPerfect ↥L) (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) :
    ∀ t : ↥L, t ∈ aschbacherSolvableCore 3 ↥L → (t : G) ∈ CFSG.Open.pCoreOf 2 Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := projTen Y φ with hπ
  set f : ↥L →* Perm (Fin 10) := π.comp (Subgroup.inclusion hLY) with hf
  have hker2 : IsPGroup 2 f.ker := by
    intro k
    have hk : Subgroup.inclusion hLY (k : ↥L) ∈ CFSG.pCore 2 ↥Y :=
      (projTen_eq_one_iff Y φ _).mp (MonoidHom.mem_ker.mp k.2)
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨_, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : CFSG.pCore 2 ↥Y => ((y : ↥Y) : G)) hn
    simpa using this
  have hkerθ : f.ker ≤ θ := by
    have := hker2.isNilpotent
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.2.1
      f.ker inferInstance inferInstance (Sec17.Proof171.not_three_dvd_of_isPGroup_two hker2)
  have hcardθ : Nat.card ↥L = 2520 * Nat.card θ := by
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h2
    exact h2
  have h1 := Subgroup.card_ker_mul_card_range f
  have hθpos : 0 < Nat.card θ := Nat.card_pos
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  have h3 : Nat.card f.ker ≤ Nat.card θ := Subgroup.card_le_of_le hkerθ
  have hge : 2520 ≤ Nat.card f.range := by
    by_contra hlt
    have := Nat.mul_lt_mul_of_lt_of_le (not_le.mp hlt) h3 hθpos
    rw [mul_comm (Nat.card f.range), h1, hcardθ, mul_comm] at this
    exact lt_irrefl _ this
  set c' : ↥Y := ⟨c, hcY⟩ with hc'
  set x := π c' with hx
  have hLx : f.range ≤ Subgroup.centralizer ({x} : Set (Perm (Fin 10))) ⊓
      alternatingGroup (Fin 10) := by
    rintro _ ⟨l, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, projTen_mem_alternatingGroup Y φ _⟩
    have hlc : (l : G) * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)
    have he : Subgroup.inclusion hLY l * c' = c' * Subgroup.inclusion hLY l := Subtype.ext hlc
    change π (Subgroup.inclusion hLY l) * π c' = π c' * π (Subgroup.inclusion hLY l)
    rw [← map_mul, ← map_mul, he]
  have hperf : ⁅f.range, f.range⁆ = f.range := by
    have : Group.IsPerfect ↥f.range :=
      Group.IsPerfect.ofSurjective (f := f.rangeRestrict) (MonoidHom.rangeRestrict_surjective f)
    exact Subgroup.isPerfect_iff.mp this
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by simp [hc', hc3])
    rw [this, map_one]
  have hx1 : x ≠ 1 := by
    intro h0
    have hcO := mem_pCoreOf_of_projTen_eq_one h0
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) ⟨c, hcO⟩
    have h2 : c ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact hc1 (Step163Alt.eq_one_of_two_three h2 (by rw [pow_one]; exact hc3))
  have hx3c : x.IsThreeCycle := isThreeCycle_of_card_centralizer hx3 hx1
    (hge.trans (Subgroup.card_le_of_le (hLx.trans inf_le_left)))
  have hle := card_le_of_perfect_of_isThreeCycle hx3c hLx hperf
  have hkereq : f.ker = θ := by
    refine Subgroup.eq_of_le_of_card_ge hkerθ ?_
    have h4 : Nat.card f.range = 2520 := le_antisymm hle hge
    rw [h4, hcardθ, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).ge
  intro t ht
  rw [← hkereq] at ht
  exact mem_pCoreOf_of_projTen_eq_one ht

theorem le_normalizer_of_ten {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hΩ3 : (omegaA A).ncard = 3)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (hY : Y ∈ scriptY0Star A (lB A)) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
    (hm : MeetsY4 A (lB A) L Y)
    (hθ : ∀ t : ↥L, t ∈ aschbacherSolvableCore 3 ↥L →
      (t : G) ∈ Subgroup.normalizer (Y : Set G)) :
    L ≤ Subgroup.normalizer (Y : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hAY : A ≤ Y := Step163Alt.le_of_alternating_ten (Res162.partTwoE_maximal h)
    hD.isElemAbelian hY.prop.1.1.2 hY.prop.2.2 φ
  have hcA : c ∈ A := hD.mem_A
  have hcY : c ∈ Y := hAY hcA
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := hD.le_centralizer
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  obtain ⟨hinjA, g, hgA, hgsurj, hlift⟩ := exists_conj_lift hD.isElemAbelian hD.card_eq hAY φ
  set π := projTen Y φ with hπ
  have hker2 := projTen_ker_isPGroup Y φ
  set c' : ↥Y := ⟨c, hcY⟩ with hc'
  obtain ⟨e, he⟩ := exists_axisElt_of_mem_omegaA hAY φ hΩ3 hinjA hgA hlift hD.zpowers_mem_omegaA
  have hx3c : (π c').IsThreeCycle := by
    have h1 : (axisElt e).IsThreeCycle := card_support_eq_three_iff.mp (axisElt_support_card e)
    rw [← he, IsThreeCycle, cycleType_conj] at h1
    exact h1
  obtain ⟨k₀, hk₀⟩ := exists_conj_eq_dThree hx3c
  set π' : ↥Y →* Perm (Fin 10) := (MulAut.conj k₀).toMonoidHom.comp π with hπ'
  have hπ'apply : ∀ y, π' y = k₀ * π y * k₀⁻¹ := fun y => rfl
  have hπ'c : π' c' = dThree := hk₀
  have hπ'one : ∀ y, π' y = 1 → (y : G) ∈ CFSG.Open.pCoreOf 2 Y := by
    intro y hy
    rw [hπ'apply, conj_eq_one_iff] at hy
    exact mem_pCoreOf_of_projTen_eq_one hy
  have hker2' : IsPGroup 2 π'.ker := by
    have hk : π'.ker = π.ker := by
      ext z
      simp only [MonoidHom.mem_ker, hπ'apply, conj_eq_one_iff]
    rw [hk]
    exact hker2
  have hπ'alt : ∀ y, π' y ∈ alternatingGroup (Fin 10) := fun y => by
    rw [hπ'apply]
    exact (alternatingGroup.normal (α := Fin 10)).conj_mem _ (projTen_mem_alternatingGroup Y φ y) k₀
  have hπ'surj : ∀ σ ∈ alternatingGroup (Fin 10), ∃ y, π' y = σ := by
    intro σ hσ
    have hσ' : k₀⁻¹ * σ * k₀ ∈ alternatingGroup (Fin 10) := by
      have := (alternatingGroup.normal (α := Fin 10)).conj_mem σ hσ k₀⁻¹
      rwa [inv_inv] at this
    obtain ⟨y, hy⟩ := mem_range_projTen Y φ hσ'
    refine ⟨y, ?_⟩
    rw [hπ'apply, show π y = k₀⁻¹ * σ * k₀ from hy]
    group
  set Yh := ((Subgroup.centralizer ({dThree} : Set (Perm (Fin 10)))).comap π').map Y.subtype
    with hYh
  have hYhY : Yh ≤ Y := Subgroup.map_subtype_le _
  have hmemYh : ∀ y : ↥Y, π' y * dThree = dThree * π' y → (y : G) ∈ Yh := fun y hy =>
    ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hy, rfl⟩
  have hYhmem : ∀ y ∈ Yh, ∃ hy : y ∈ Y, π' ⟨y, hy⟩ * dThree = dThree * π' ⟨y, hy⟩ := by
    rintro _ ⟨⟨y, hy⟩, h1, rfl⟩
    exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.mp h1⟩
  have hcpow : ∀ n : ℤ, π' ⟨c ^ n, Y.zpow_mem hcY n⟩ = dThree ^ n := by
    intro n
    rw [← hπ'c, ← map_zpow]
    rfl
  have hconjc : ∀ n : ℤ, ∀ y : ↥Y, π' y * dThree = dThree * π' y →
      ∃ hm : c ^ n * (y : G) * (c ^ n)⁻¹ ∈ Y, π' ⟨c ^ n * (y : G) * (c ^ n)⁻¹, hm⟩ = π' y := by
    intro n y hy
    have hm : c ^ n * (y : G) * (c ^ n)⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.zpow_mem hcY n) y.2) (Y.inv_mem (Y.zpow_mem hcY n))
    refine ⟨hm, ?_⟩
    have he1 : (⟨c ^ n * (y : G) * (c ^ n)⁻¹, hm⟩ : ↥Y) =
        ⟨c ^ n, Y.zpow_mem hcY n⟩ * y * (⟨c ^ n, Y.zpow_mem hcY n⟩ : ↥Y)⁻¹ := Subtype.ext rfl
    rw [he1, map_mul, map_mul, map_inv, hcpow, ((Commute.zpow_left hy.symm n)).eq,
      mul_inv_cancel_right]
  have hcYh : Subgroup.zpowers c ≤ Subgroup.normalizer (Yh : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun y hyYh => ?_
    obtain ⟨hy, hyc⟩ := hYhmem y hyYh
    obtain ⟨hm, hm'⟩ := hconjc 1 ⟨y, hy⟩ hyc
    have h1 := hmemYh ⟨_, hm⟩ (by rw [hm']; exact hyc)
    simpa using h1
  have hc3g : IsPGroup 3 (Subgroup.zpowers c) := Sec17.Proof171.isPGroup_zpowers_of_pow_three hc3
  set fh : ↥Yh →* Perm (Fin 10) := π'.comp (Subgroup.inclusion hYhY) with hfh
  have hfhker : ¬ 3 ∣ Nat.card fh.ker := by
    have hp : IsPGroup 2 fh.ker := by
      rintro ⟨k, hk⟩
      obtain ⟨n, hn⟩ := hker2' ⟨Subgroup.inclusion hYhY k, hk⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun z : ↥π'.ker => ((z : ↥Y) : G)) hn
      simpa using this
    exact Sec17.Proof171.not_three_dvd_of_isPGroup_two hp
  have hliftc : ∀ y : ↥Yh, ∃ k : ↥Yh, (k : G) ∈ Subgroup.centralizer
      ((Subgroup.zpowers c : Subgroup G) : Set G) ∧ fh k = fh y := by
    intro y
    refine exists_centralizer_with_same_image_of_trivial_quotient_action 3 Nat.prime_three
      (Subgroup.zpowers c) Yh hc3g hcYh fh hfhker (fun member element => ?_) y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp member.2
    obtain ⟨hel, helc⟩ := hYhmem _ element.2
    obtain ⟨hm, hm'⟩ := hconjc n ⟨element, hel⟩ helc
    change π' ⟨(member : G) * element * (member : G)⁻¹, _⟩ = π' ⟨element, hel⟩
    have he1 : (⟨(member : G) * element * (member : G)⁻¹,
        hYhY (Subgroup.le_normalizer_iff.mp hcYh member member.property element
          element.property)⟩ : ↥Y) = ⟨c ^ n * (element : G) * (c ^ n)⁻¹, hm⟩ :=
      Subtype.ext (by simp only; rw [hn])
    rw [he1, hm']
  have hNL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_zpowers_le_normalizer_L h (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA)
  have hcNL : ∀ k : G, k ∈ Subgroup.centralizer
      ((Subgroup.zpowers c : Subgroup G) : Set G) → k ∈ Subgroup.normalizer (L : Set G) := by
    intro k hk
    apply hNL
    apply centralizer_singleton_le_normalizer_zpowers c
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hk c (Subgroup.mem_zpowers c)).symm
  set Dd := L ⊓ Y with hDd
  set N := (Dd.subgroupOf Y).map π' with hN
  have hNmem : ∀ d (hd : d ∈ Dd), π' ⟨d, (Subgroup.mem_inf.mp hd).2⟩ ∈ N := fun d hd =>
    ⟨⟨d, (Subgroup.mem_inf.mp hd).2⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  have hNc : ∀ u ∈ N, u * dThree = dThree * u ∧ u ∈ alternatingGroup (Fin 10) := by
    rintro _ ⟨⟨d, hdY⟩, hd, rfl⟩
    have hdD : d ∈ Dd := Subgroup.mem_subgroupOf.mp hd
    refine ⟨?_, hπ'alt _⟩
    have hdc : d * c = c * d :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (Subgroup.mem_inf.mp hdD).1)
    have he1 : (⟨d, hdY⟩ : ↥Y) * c' = c' * ⟨d, hdY⟩ := Subtype.ext hdc
    rw [← hπ'c, ← map_mul, ← map_mul, he1]
  set E7 := (alternatingGroup (Fin 7)).map embedSeven with hE7
  have hE7c : ∀ σ ∈ E7, σ * dThree = dThree * σ ∧ σ ∈ alternatingGroup (Fin 10) := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨embedSeven_commute τ, ?_⟩
    rw [Perm.mem_alternatingGroup, sign_embedSeven]
    exact hτ
  have hE7N : ∀ σ ∈ E7, ∀ u ∈ N, σ * u * σ⁻¹ ∈ N := by
    intro σ hσ u hu
    obtain ⟨hσc, hσA⟩ := hE7c σ hσ
    obtain ⟨y, hy⟩ := hπ'surj σ hσA
    have hyYh : (y : G) ∈ Yh := hmemYh y (by rw [hy]; exact hσc)
    obtain ⟨k, hkc, hk⟩ := hliftc ⟨y, hyYh⟩
    obtain ⟨⟨d, hdY⟩, hd, rfl⟩ := hu
    have hdD : d ∈ Dd := Subgroup.mem_subgroupOf.mp hd
    have hkY : (k : G) ∈ Y := hYhY k.2
    have hkdk : (k : G) * d * (k : G)⁻¹ ∈ Dd := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hcNL _ hkc) d).mp (Subgroup.mem_inf.mp hdD).1
      · exact Y.mul_mem (Y.mul_mem hkY hdY) (Y.inv_mem hkY)
    have hσk : π' ⟨k, hkY⟩ = σ := by
      have : fh k = π' ⟨k, hkY⟩ := rfl
      rw [← this, hk, ← hy]
      rfl
    refine ⟨⟨_, (Subgroup.mem_inf.mp hkdk).2⟩, Subgroup.mem_subgroupOf.mpr hkdk, ?_⟩
    have he1 : (⟨(k : G) * d * (k : G)⁻¹, (Subgroup.mem_inf.mp hkdk).2⟩ : ↥Y) =
        ⟨k, hkY⟩ * ⟨d, hdY⟩ * (⟨k, hkY⟩ : ↥Y)⁻¹ := Subtype.ext rfl
    rw [he1, map_mul, map_mul, map_inv, hσk]
  obtain ⟨X, hX, hXLY⟩ := hm
  have hE7leN : E7 ≤ N := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup ↥E7 := eSevenEquiv.isSimpleGroup
    have hnorm : (N.subgroupOf E7).Normal := by
      refine ⟨fun n hn σ => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hE7N σ σ.2 n hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf E7) with hbot | htop
    · exfalso
      apply Proof162.not_isSolvable_of_mem_scriptY4 hX
      have hXY : X ≤ Y := hXLY.trans inf_le_right
      refine isSolvable_of_comm_image hXY π' hker2' fun x x' => ?_
      have hxN := hNmem _ (hXLY x.2)
      have hx'N := hNmem _ (hXLY x'.2)
      obtain ⟨hxc, hxA⟩ := hNc _ hxN
      obtain ⟨hx'c, hx'A⟩ := hNc _ hx'N
      obtain ⟨i, σ, hσ, hiσ⟩ := exists_eq_of_commute_dThree_of_mem hxc hxA
      obtain ⟨j, τ, hτ, hjτ⟩ := exists_eq_of_commute_dThree_of_mem hx'c hx'A
      have hcomm : ⁅π' (Subgroup.inclusion hXY x), π' (Subgroup.inclusion hXY x')⁆ ∈ N := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hxN hx'N) (inv_mem hxN)) (inv_mem hx'N)
      have hcE7 : ⁅π' (Subgroup.inclusion hXY x), π' (Subgroup.inclusion hXY x')⁆ ∈ E7 := by
        have hc : ∀ σ : Perm (Fin 7), Commute (embedSeven σ) dThree := embedSeven_commute
        change ⁅π' ⟨x, _⟩, π' ⟨x', _⟩⁆ ∈ E7
        rw [hiσ, hjτ, commutatorElement_mul_of_commute ((hc σ).pow_right _).symm
          ((hc τ).pow_right _).symm ((hc σ).pow_right _).symm ((hc τ).pow_right _).symm
          (Commute.pow_pow_self dThree _ _), ← map_commutatorElement]
        refine ⟨⁅σ, τ⁆, ?_, rfl⟩
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)
      have h1 : (⟨_, hcE7⟩ : ↥E7) ∈ N.subgroupOf E7 := Subgroup.mem_subgroupOf.mpr hcomm
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 := congrArg Subtype.val h1
      simp only [OneMemClass.coe_one] at h2
      rw [commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
    · intro σ hσ
      have h1 : (⟨σ, hσ⟩ : ↥E7) ∈ N.subgroupOf E7 := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
  set D0 := Dd ⊓ (E7.comap π').map Y.subtype with hD0
  have hD0Y : D0 ≤ Y := inf_le_left.trans inf_le_right
  have hD0L : D0 ≤ L := inf_le_left.trans inf_le_left
  have hD0E : ∀ d : ↥D0, π' (Subgroup.inclusion hD0Y d) ∈ E7 := by
    rintro ⟨d, hd⟩
    obtain ⟨-, ⟨⟨d', hd'Y⟩, hd'E, hdd'⟩⟩ := Subgroup.mem_inf.mp hd
    have : (Subgroup.inclusion hD0Y ⟨d, hd⟩ : ↥Y) = ⟨d', hd'Y⟩ := Subtype.ext hdd'.symm
    rw [this]
    exact hd'E
  set f₁ : ↥D0 →* ↥E7 := (π'.comp (Subgroup.inclusion hD0Y)).codRestrict E7 hD0E with hf₁
  set f₂ : ↥D0 →* ↥L ⧸ θ := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hD0L) with hf₂
  have hf₁s : Function.Surjective f₁ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨⟨d, hdY⟩, hd, hdσ⟩ := hE7leN hσ
    have hdD : d ∈ Dd := Subgroup.mem_subgroupOf.mp hd
    have hdD0 : d ∈ D0 := Subgroup.mem_inf.mpr ⟨hdD, ⟨⟨d, hdY⟩, by
      change π' ⟨d, hdY⟩ ∈ E7
      rw [hdσ]
      exact hσ, rfl⟩⟩
    refine ⟨⟨d, hdD0⟩, Subtype.ext ?_⟩
    exact hdσ
  have hker : f₂.ker ≤ f₁.ker := by
    have hk : f₂.ker = θ.comap (Subgroup.inclusion hD0L) := by
      rw [hf₂, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hθsol : Group.IsSolvable θ :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
    have hsolK : Group.IsSolvable f₂.ker := by
      rw [hk]
      exact Group.isSolvable_of_isSolvable_injective
        ((Subgroup.inclusion hD0L).subgroupComap_injective θ (Subgroup.inclusion_injective hD0L))
    have hn : (f₂.ker.map f₁).Normal := (inferInstance : f₂.ker.Normal).map f₁ hf₁s
    have hsol : Group.IsSolvable (f₂.ker.map f₁) :=
      Group.isSolvable_of_surjective (f := f₁.subgroupMap f₂.ker)
        (f₁.subgroupMap_surjective f₂.ker)
    have hbot' := eq_bot_of_normal_of_isSolvable_a7 eSevenEquiv (f₂.ker.map f₁) hsol
    intro x hx
    have h1 : f₁ x ∈ f₂.ker.map f₁ := Subgroup.mem_map_of_mem f₁ hx
    rw [hbot', Subgroup.mem_bot] at h1
    exact h1
  have hf₂s : Function.Surjective f₂ := surjective_of_ker_le f₁ hf₁s f₂ hker
    (by rw [Nat.card_congr φL.toEquiv, Nat.card_congr eSevenEquiv.toEquiv])
  intro l hl
  obtain ⟨d, hd⟩ := hf₂s (QuotientGroup.mk' θ ⟨l, hl⟩)
  have hdl : (Subgroup.inclusion hD0L d)⁻¹ * ⟨l, hl⟩ ∈ θ := by
    rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply]
    exact hd
  have h1 := hθ _ hdl
  have h2 : (d : G)⁻¹ * l ∈ Subgroup.normalizer (Y : Set G) := by simpa using h1
  have he1 : l = (d : G) * ((d : G)⁻¹ * l) := by group
  rw [he1]
  exact mul_mem (Subgroup.le_normalizer (hD0Y d.2)) h2

theorem img_facts_of_ten {Y L : Subgroup G} {d : G} (hLY : L ≤ Y) (hdY : d ∈ Y)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hLd : L ≤ Subgroup.centralizer ({d} : Set G))
    (hLp : Group.IsPerfect ↥L) (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) :
    2520 ≤ Nat.card (imgTen Y φ L) ∧ ⁅imgTen Y φ L, imgTen Y φ L⁆ = imgTen Y φ L ∧
      imgTen Y φ L ≤ Subgroup.centralizer ({projTen Y φ ⟨d, hdY⟩} : Set (Perm (Fin 10))) ⊓
        alternatingGroup (Fin 10) ∧ (projTen Y φ ⟨d, hdY⟩).IsThreeCycle := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := projTen Y φ with hπ
  set f : ↥L →* Perm (Fin 10) := π.comp (Subgroup.inclusion hLY) with hf
  have himg : imgTen Y φ L = f.range := by
    ext z
    rw [mem_imgTen, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLY l, l.2, rfl⟩
  have hker2 : IsPGroup 2 f.ker := by
    intro k
    have hk : Subgroup.inclusion hLY (k : ↥L) ∈ CFSG.pCore 2 ↥Y :=
      (projTen_eq_one_iff Y φ _).mp (MonoidHom.mem_ker.mp k.2)
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨_, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : CFSG.pCore 2 ↥Y => ((y : ↥Y) : G)) hn
    simpa using this
  have hkerθ : f.ker ≤ θ := by
    have := hker2.isNilpotent
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.2.1
      f.ker inferInstance inferInstance (Sec17.Proof171.not_three_dvd_of_isPGroup_two hker2)
  have hcardθ : Nat.card ↥L = 2520 * Nat.card θ := by
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h2
    exact h2
  have h1 := Subgroup.card_ker_mul_card_range f
  have hθpos : 0 < Nat.card θ := Nat.card_pos
  have h3 : Nat.card f.ker ≤ Nat.card θ := Subgroup.card_le_of_le hkerθ
  have hge : 2520 ≤ Nat.card f.range := by
    by_contra hlt
    have := Nat.mul_lt_mul_of_lt_of_le (not_le.mp hlt) h3 hθpos
    rw [mul_comm (Nat.card f.range), h1, hcardθ, mul_comm] at this
    exact lt_irrefl _ this
  set d' : ↥Y := ⟨d, hdY⟩ with hd'
  have hLx : f.range ≤ Subgroup.centralizer ({π d'} : Set (Perm (Fin 10))) ⊓
      alternatingGroup (Fin 10) := by
    rintro _ ⟨l, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, projTen_mem_alternatingGroup Y φ _⟩
    have hlc : (l : G) * d = d * l := Subgroup.mem_centralizer_singleton_iff.mp (hLd l.2)
    have he : Subgroup.inclusion hLY l * d' = d' * Subgroup.inclusion hLY l := Subtype.ext hlc
    change π (Subgroup.inclusion hLY l) * π d' = π d' * π (Subgroup.inclusion hLY l)
    rw [← map_mul, ← map_mul, he]
  have hperf : ⁅f.range, f.range⁆ = f.range := by
    have : Group.IsPerfect ↥f.range :=
      Group.IsPerfect.ofSurjective (f := f.rangeRestrict) (MonoidHom.rangeRestrict_surjective f)
    exact Subgroup.isPerfect_iff.mp this
  have hx3 : π d' ^ 3 = 1 := by
    rw [← map_pow]
    have : d' ^ 3 = 1 := Subtype.ext (by simp [hd', hd3])
    rw [this, map_one]
  have hx1 : π d' ≠ 1 := by
    intro h0
    have hcO := mem_pCoreOf_of_projTen_eq_one h0
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) ⟨d, hcO⟩
    have h2 : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact hd1 (Step163Alt.eq_one_of_two_three h2 (by rw [pow_one]; exact hd3))
  rw [himg]
  exact ⟨hge, hperf, hLx, isThreeCycle_of_card_centralizer hx3 hx1
    (hge.trans (Subgroup.card_le_of_le (hLx.trans inf_le_left)))⟩

theorem le_sup_of_ten {A : Subgroup G} {c c' : G} {L L' Y : Subgroup G} (h : Sec15R G A c L)
    (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (hne : Subgroup.zpowers c' ≠ Subgroup.zpowers c)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (φL' : ↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))
    (hY : Y ∈ scriptY0Star A (lB A)) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
    (hLY : L ≤ Y) (hL'Y : L' ≤ Y) : Y ≤ (L ⊔ L') ⊔ CFSG.Open.pCoreOf 2 Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hAY : A ≤ Y := Step163Alt.le_of_alternating_ten (Res162.partTwoE_maximal h)
    hD.isElemAbelian hY.prop.1.1.2 hY.prop.2.2 φ
  have hcA : c ∈ A := hD.mem_A
  have hc'A : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc').1
  have hcY : c ∈ Y := hAY hcA
  have hc'Y : c' ∈ Y := hAY hc'A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hc'3 : c' ^ 3 = 1 := hD.isElemAbelian.2 c' hc'A
  have hc'1 : c' ≠ 1 := by
    intro h1
    have h3 := (zpowers_mem_omegaA_iff.mp hc').2.1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  obtain ⟨hinjA, g, hgA, hgsurj, -⟩ := exists_conj_lift hD.isElemAbelian hD.card_eq hAY φ
  set π := projTen Y φ with hπ
  obtain ⟨hL7, hLperf, hLc, hc3c⟩ := img_facts_of_ten hLY hcY hc3 hD.ne_one hD.le_centralizer
    (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) φL φ
  obtain ⟨hL'7, hL'perf, hL'c, hc'3c⟩ := img_facts_of_ten hL'Y hc'Y hc'3 hc'1
    (le_centralizer_of_mem_thetaComponentsAt hL'.1)
    (Sec6.isPerfect_of_mem_thetaComponentsAt hL'.1) φL' φ
  set c₁ : ↥Y := ⟨c, hcY⟩ with hc₁
  set c₂ : ↥Y := ⟨c', hc'Y⟩ with hc₂
  have haxis : ∀ x : Perm (Fin 10), x ∈ eTwentySeven → x.IsThreeCycle → ∃ e : Fin 6,
      x = axisElt e := by
    rintro _ ⟨i, j, k, rfl⟩ hx
    exact axisElt_of_support_card i j k hx.card_support
  obtain ⟨ea, hea⟩ := haxis _ (hgA c₁ hcA) (by
    rw [IsThreeCycle, cycleType_conj]
    exact hc3c)
  obtain ⟨eb, heb⟩ := haxis _ (hgA c₂ hc'A) (by
    rw [IsThreeCycle, cycleType_conj]
    exact hc'3c)
  have hab : ea.val / 2 ≠ eb.val / 2 := by
    intro hab
    apply hne
    rcases axisElt_same_axis ea eb hab with h1 | h1
    · rw [← hea, ← heb] at h1
      have h2 : π c₂ = π c₁ := by
        have := congrArg (fun z => g⁻¹ * z * g) h1
        simpa [mul_assoc] using this
      have h3 : c₂ * c₁⁻¹ = 1 := hinjA _ (mul_mem hc'A (inv_mem hcA))
        (by rw [map_mul, map_inv, h2, mul_inv_cancel])
      have h4 : c' = c := congrArg Subtype.val (mul_inv_eq_one.mp h3)
      rw [h4]
    · rw [← hea, ← heb] at h1
      have h2 : π c₂ = (π c₁)⁻¹ := by
        have := congrArg (fun z => g⁻¹ * z * g) h1
        simpa [mul_assoc] using this
      have h3 : c₂ * c₁ = 1 := hinjA _ (mul_mem hc'A hcA)
        (by rw [map_mul, h2, inv_mul_cancel])
      have h4 : c' = c⁻¹ := congrArg Subtype.val (eq_inv_of_mul_eq_one_left h3)
      rw [h4, Subgroup.zpowers_inv]
  have hclaim : ∀ (M : Subgroup G) (y : ↥Y),
      imgTen Y φ M ≤ Subgroup.centralizer ({π y} : Set (Perm (Fin 10))) ⊓
        alternatingGroup (Fin 10) → ⁅imgTen Y φ M, imgTen Y φ M⁆ = imgTen Y φ M →
      2520 ≤ Nat.card (imgTen Y φ M) → (π y).IsThreeCycle →
      ∀ R : Subgroup (Perm (Fin 10)),
        R ≤ Subgroup.centralizer ({g * π y * g⁻¹} : Set (Perm (Fin 10))) ⊓
          alternatingGroup (Fin 10) → ¬ 3 ∣ Nat.card R →
        R ≤ (imgTen Y φ M).map (MulAut.conj g).toMonoidHom := by
    intro M y hMc hMp hM7 hy3 R hR hR3
    refine le_of_le_centralizer_of_isThreeCycle (x := g * π y * g⁻¹)
      (by rw [IsThreeCycle, cycleType_conj]; exact hy3) ?_
      (commutator_map_conj_self hMp g)
      (by rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]) hR hR3
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hMc hz
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have hzc : z * π y = π y * z := Subgroup.mem_centralizer_singleton_iff.mp hz'.1
      change g * z * g⁻¹ * (g * π y * g⁻¹) = g * π y * g⁻¹ * (g * z * g⁻¹)
      calc g * z * g⁻¹ * (g * π y * g⁻¹) = g * (z * π y) * g⁻¹ := by group
        _ = g * (π y * z) * g⁻¹ := by rw [hzc]
        _ = g * π y * g⁻¹ * (g * z * g⁻¹) := by group
    · exact Subgroup.Normal.conj_mem inferInstance z hz'.2 g
  have hΔ : Y = delta A (lB A) Y := hY.prop.1.2.2.1
  refine hΔ.le.trans (sSup_le fun Q hQ => ?_)
  obtain ⟨hQQ, hQY⟩ := hQ
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQQ.1.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
  set R := (imgTen Y φ Q).map (MulAut.conj g).toMonoidHom with hR
  have hR3 : ¬ 3 ∣ Nat.card R := by
    rw [hR, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact fun h3 => hQ3 (h3.trans (card_imgTen_dvd Y φ hQY))
  have hER : eTwentySeven ≤ Subgroup.normalizer (R : Set (Perm (Fin 10))) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := hgsurj x hx
    obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hr
    have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have haqa : (a : G) * q * (a : G)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hAQ ha) q).mp hqQ
    refine ⟨π (a * q * a⁻¹), Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haqa), ?_⟩
    simp only [hπ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hRK : ∃ K : Subgroup (Perm (Fin 10)), (K = kOne ∨ K = kTwo ∨ K = kThree) ∧ R ≤ K := by
    rcases le_kOne_or_le_kTwo_or_le_kThree hR3 hER with h1 | h1 | h1
    · exact ⟨kOne, Or.inl rfl, h1⟩
    · exact ⟨kTwo, Or.inr (Or.inl rfl), h1⟩
    · exact ⟨kThree, Or.inr (Or.inr rfl), h1⟩
  obtain ⟨K, hK, hRK⟩ := hRK
  rcases le_centralizer_axisElt_or hab hK with hKa | hKb
  · rw [← hea] at hKa
    have h1 := hclaim L c₁ hLc hLperf hL7 hc3c R (hRK.trans hKa) hR3
    rw [hR, Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective] at h1
    exact (le_sup_of_imgTen_le Y φ hQY h1).trans (sup_le_sup_right le_sup_left _)
  · rw [← heb] at hKb
    have h1 := hclaim L' c₂ hL'c hL'perf hL'7 hc'3c R (hRK.trans hKb) hR3
    rw [hR, Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective] at h1
    exact (le_sup_of_imgTen_le Y φ hQY h1).trans (sup_le_sup_right le_sup_right _)

end CFSG.RankThree.PartTwo.Sec16.Res162b
