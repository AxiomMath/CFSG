module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec19.Step1919O2
import CFSG.RankThree.PartTwo.Sec3.ThreeGroupCentralizer
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS12MovesM22
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open scoped Pointwise

namespace Step1910O2Proof

theorem mul_comm_of_commutator_eq_one {X : Type*} [Group X] {a b : X}
    (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a :=
  commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h)

variable {G : Type} [Group G] [Finite G]

theorem card_le_card_center_thetaQuot {L S : Subgroup G} (hS3 : IsPGroup 3 S) (hSL : S ≤ L)
    (hSC : S ≤ Sec4.thetaQuotCentralizer L) :
    Nat.card S ≤ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  set S' : Subgroup L := S.subgroupOf L with hS'
  have hS'card : Nat.card S' = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hS'3 : IsPGroup 3 S' := hS3.comap_subtype
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hmap : S'.map π ≤ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hsC : (s : G) ∈ Sec4.thetaQuotCentralizer L := hSC (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨t, ht, hte⟩ := (Sec6.mem_thetaQuotCentralizer_iff.mp hsC).2 _ (L.inv_mem l.2)
    have htl : t = l * s * l⁻¹ * s⁻¹ := by
      apply Subtype.ext
      rw [show (t : G) = L.subtype t from rfl, hte]
      simp [mul_assoc]
    have h1 : π (l * s * l⁻¹ * s⁻¹) = 1 := by
      rw [← htl, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ht
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_comm_of_commutator_eq_one h1
  have hinj : Set.InjOn π (S' : Set L) :=
    Sec12.injOn_mk_of_coprime _ three_not_dvd_card_aschbacherSolvableCore hS'3
  rw [← hS'card, ← Step198DProof.card_map_of_injOn π hinj]
  exact Subgroup.card_le_of_le hmap

theorem mul_comm_of_mem_sup {L E : Subgroup G} (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hE3 : IsPGroup 3 E) (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) {x : G} (hx : x ∈ L ⊔ E)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) {b : G}
    (hb : b ∈ E ⊓ Sec4.thetaQuotCentralizer L) : x * b = b * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx' : x ∈ ((L ⊔ E : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L E hEL] at hx'
  obtain ⟨l, hl, e₀, he₀, rfl⟩ := hx'
  have hlE : l ∈ Subgroup.normalizer (E : Set G) := by
    have := Subgroup.mul_mem _ hxE (Subgroup.inv_mem _ (Subgroup.le_normalizer he₀))
    simpa using this
  have hwE : l * b * l⁻¹ * b⁻¹ ∈ E :=
    E.mul_mem ((Subgroup.mem_normalizer_iff.mp hlE b).mp hb.1) (E.inv_mem hb.1)
  have hwθ : l * b * l⁻¹ * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have h := (Sec6.mem_thetaQuotCentralizer_iff.mp hb.2).2 _ (L.inv_mem hl)
    simpa [mul_assoc] using h
  have hdisj : Disjoint E (inSubgroup (aschbacherSolvableCore 3) L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (Sec6.theta_solvable_and_not_dvd L).2)
  have hlb : l * b = b * l :=
    mul_comm_of_commutator_eq_one ((Subgroup.disjoint_def.mp hdisj) hwE hwθ)
  calc l * e₀ * b = l * (e₀ * b) := mul_assoc _ _ _
    _ = l * (b * e₀) := by rw [hEab e₀ he₀ b hb.1]
    _ = l * b * e₀ := (mul_assoc _ _ _).symm
    _ = b * l * e₀ := by rw [hlb]
    _ = b * (l * e₀) := mul_assoc _ _ _

omit [Finite G] in
theorem conj_mul_inv_mem {E B : Subgroup G} {d x : G}
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hEexp : ∀ e ∈ E, e ^ 3 = 1)
    (hBE : B ≤ E) (hdE : d ∈ E) (hdB : d ∉ B)
    (hdec : ∀ e ∈ E, ∃ b ∈ B, ∃ k : ℤ, e = b * d ^ k)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) {a : ℕ} (hx3 : x ^ 3 ^ a = 1)
    (hxB : ∀ b ∈ B, x * b = b * x) (hxd : x * d * x⁻¹ ≠ d) :
    ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ B := by
  have hconjB : ∀ b ∈ B, x * b * x⁻¹ = b := fun b hb => by rw [hxB b hb, mul_inv_cancel_right]
  have hxdE : x * d * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxE d).mp hdE
  obtain ⟨b₀, hb₀, k, hk⟩ := hdec _ hxdE
  have hd3 : d ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hEexp d hdE
  rw [zpow_eq_zpow_emod k hd3] at hk
  have hb₀E := hBE hb₀
  have hβ : x * d * x⁻¹ * d⁻¹ ∈ B := by
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero, mul_one] at hk
      apply hdB
      have h : x * d * x⁻¹ = x * b₀ * x⁻¹ := by rw [hk, hconjB b₀ hb₀]
      rw [mul_left_cancel (mul_right_cancel h)]
      exact hb₀
    · rw [h1, zpow_one] at hk
      rw [hk, mul_inv_cancel_right]
      exact hb₀
    · exfalso
      rw [h2] at hk
      have hc : Commute b₀ (d ^ (2 : ℤ)) := Commute.zpow_right (hEab b₀ hb₀E d hdE) 2
      have hx2d : x ^ 2 * d * (x ^ 2)⁻¹ = d := by
        have e1 : x ^ 2 * d * (x ^ 2)⁻¹ = x * (x * d * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
        have e2 : x * (b₀ * d ^ (2 : ℤ)) * x⁻¹ =
            (x * b₀ * x⁻¹) * (x * d * x⁻¹) ^ (2 : ℤ) := by
          rw [conj_zpow]
          group
        rw [e1, hk, e2, hconjB b₀ hb₀, hk, hc.mul_zpow]
        have hb3 : b₀ ^ (3 : ℤ) = 1 := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
          exact hEexp b₀ hb₀E
        have e3 : b₀ * (b₀ ^ (2 : ℤ) * (d ^ (2 : ℤ)) ^ (2 : ℤ)) =
            b₀ ^ (3 : ℤ) * d ^ (3 : ℤ) * d := by group
        rw [e3, hb3, hd3, one_mul, one_mul]
      have hcomm2 : Commute (x ^ 2) d := by
        have h := congrArg (· * x ^ 2) hx2d
        simp only [inv_mul_cancel_right] at h
        exact h
      obtain ⟨m, hm⟩ : Odd (3 ^ a) := Odd.pow (by decide)
      have hx1 : x = ((x ^ 2) ^ m)⁻¹ := by
        have h : x ^ (2 * m + 1) = 1 := hm ▸ hx3
        rw [pow_succ, pow_mul] at h
        exact eq_inv_of_mul_eq_one_right h
      have hcx : Commute x d := by
        rw [hx1]
        exact (hcomm2.pow_left m).inv_left
      apply hxd
      rw [hcx.eq, mul_inv_cancel_right]
  intro e he
  obtain ⟨b, hb, k', rfl⟩ := hdec e he
  set β := x * d * x⁻¹ * d⁻¹ with hβdef
  have hxd' : x * d * x⁻¹ = β * d := by rw [hβdef]; group
  have hcβd : Commute β d := hEab β (hBE hβ) d hdE
  have h1 : x * (b * d ^ k') * x⁻¹ * (b * d ^ k')⁻¹ =
      (x * b * x⁻¹) * (x * d * x⁻¹) ^ k' * (d ^ k')⁻¹ * b⁻¹ := by
    rw [conj_zpow]
    group
  rw [h1, hconjB b hb, hxd', hcβd.mul_zpow]
  have h2 : b * (β ^ k' * d ^ k') * (d ^ k')⁻¹ * b⁻¹ = b * β ^ k' * b⁻¹ := by group
  rw [h2]
  exact B.mul_mem (B.mul_mem hb (B.zpow_mem hβ k')) (B.inv_mem hb)

theorem type_of_mem (h131 : Item131) (hspor : SporadicModels131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hcL : c ∈ L) :
    Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22 := by
  rcases (item131_seven_of_mem h131 hspor hD hcL).1 with hSL | ⟨-, hty⟩
  · left
    obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL
    set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
    have hΛn : Λ.Normal := lBar_normal hD
    have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
    have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
    have hq2 : 2 < p ^ f := by
      by_contra hq2
      have hp := D.piField.prime
      have hf := D.piField.one_le
      have h2 : p ^ f = 2 := by
        have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
        omega
      have := SLTwoData.isSolvable_of_two D h2
      have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
      have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
      exact Group.IsPerfect.not_isSolvable Λ inferInstance
    have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
    obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    exact isSLThreePi_of_mulEquiv
      (((MulEquiv.subgroupCongr hL₀).trans (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA)).trans
        η.symm) (Sec4.isSLThreePi_of_equiv D.piField D.modThree D.e)
  · exact hty

theorem exists_mem_sup_normalizer_moves {L E B : Subgroup G} {d : G}
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hE3 : IsPGroup 3 E)
    (hBE : B ≤ E) (hBC : B ≤ Sec4.thetaQuotCentralizer L) (hdE : d ∈ E)
    (hdec1 : ∀ e ∈ E, ∃ t ∈ E ⊓ L, ∃ b ∈ B, e = t * b)
    (hdec2 : ∀ e ∈ E, ∃ b ∈ B, ∃ k : ℤ, e = b * d ^ k)
    {xb : L ⧸ aschbacherSolvableCore 3 L}
    (hxN : xb ∈ Subgroup.normalizer ((((E ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :
        Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Set (L ⧸ aschbacherSolvableCore 3 L)))
    (hx3 : IsPGroup 3 (Subgroup.zpowers xb)) {t₀ : L} (ht₀ : t₀ ∈ (E ⊓ L).subgroupOf L)
    (hmove : xb * (t₀ : L ⧸ aschbacherSolvableCore 3 L) * xb⁻¹ ≠ t₀) :
    ∃ x ∈ L ⊔ E, x ∈ Subgroup.normalizer (E : Set G) ∧ IsPGroup 3 (Subgroup.zpowers x) ∧
      x * d * x⁻¹ ≠ d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLY : L ≤ L ⊔ E := le_sup_left
  have hEY : E ≤ L ⊔ E := le_sup_right
  have hθLY : inSubgroup (aschbacherSolvableCore 3) L ≤ L ⊔ E := (Sec6.theta_le L).trans hLY
  have hYN : L ⊔ E ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    (sup_le Subgroup.le_normalizer hEL).trans (Sec6.normalizer_le_normalizer_theta L)
  set N : Subgroup (L ⊔ E : Subgroup G) :=
    (inSubgroup (aschbacherSolvableCore 3) L).subgroupOf (L ⊔ E) with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hθLY).mpr hYN
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθLY).toEquiv]
    exact (Sec6.theta_solvable_and_not_dvd L).2
  set πY := QuotientGroup.mk' N with hπY
  set ψ : L →* (L ⊔ E : Subgroup G) ⧸ N := πY.comp (Subgroup.inclusion hLY) with hψ
  have hψker : ∀ l : L, ψ l = 1 ↔ l ∈ aschbacherSolvableCore 3 L := by
    intro l
    rw [hψ, MonoidHom.comp_apply, hπY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    constructor
    · rintro ⟨l', hl', hl'e⟩
      rwa [← Subtype.ext hl'e]
    · intro hl
      exact ⟨l, hl, rfl⟩
  have hθker : aschbacherSolvableCore 3 L ≤ ψ.ker := fun l hl => (hψker l).mpr hl
  set ψb := QuotientGroup.lift (aschbacherSolvableCore 3 L) ψ hθker with hψb
  have hψb_mk : ∀ (l : G) (hl : l ∈ L),
      ψb ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = πY ⟨l, hLY hl⟩ :=
    fun l hl => QuotientGroup.lift_mk _ hθker _
  have hψb_inj : Function.Injective ψb := by
    intro u v huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    rw [QuotientGroup.eq]
    apply (hψker _).mp
    rw [map_mul, map_inv, ← QuotientGroup.lift_mk _ hθker u, ← QuotientGroup.lift_mk _ hθker v,
      ← hψb, huv, inv_mul_cancel]
  set xY := ψb xb with hxY
  have hxY3 : IsPGroup 3 (Subgroup.zpowers xY) := by
    rw [hxY, ← MonoidHom.map_zpowers]
    exact hx3.map ψb
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk_surjective xb
  have hxYl₀ : xY = πY ⟨l₀, hLY l₀.2⟩ := by rw [hxY, ← hl₀, ← hψb_mk l₀ l₀.2]
  have hxYB : ∀ b (hb : b ∈ B), xY * πY ⟨b, hEY (hBE hb)⟩ * xY⁻¹ = πY ⟨b, hEY (hBE hb)⟩ := by
    intro b hb
    obtain ⟨t, ht, hte⟩ := (Sec6.mem_thetaQuotCentralizer_iff.mp (hBC hb)).2 _ (L.inv_mem l₀.2)
    have h1 : πY (⟨l₀, hLY l₀.2⟩ * ⟨b, hEY (hBE hb)⟩ * (⟨l₀, hLY l₀.2⟩ : (L ⊔ E : Subgroup G))⁻¹ *
        (⟨b, hEY (hBE hb)⟩ : (L ⊔ E : Subgroup G))⁻¹) = 1 := by
      rw [hπY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
      refine ⟨t, ht, ?_⟩
      rw [hte]
      simp [mul_assoc]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    rw [hxYl₀, mul_comm_of_commutator_eq_one h1, mul_inv_cancel_right]
  have hxYE : xY ∈ Subgroup.normalizer (((E.subgroupOf (L ⊔ E)).map (QuotientGroup.mk' N) :
      Subgroup ((L ⊔ E : Subgroup G) ⧸ N)) : Set ((L ⊔ E : Subgroup G) ⧸ N)) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨t, ht, b, hb, hyt⟩ := hdec1 _ (Subgroup.mem_subgroupOf.mp hy)
    have hyeq : y = ⟨t, hLY ht.2⟩ * ⟨b, hEY (hBE hb)⟩ := Subtype.ext hyt
    obtain ⟨t', ht', ht'e⟩ := (Subgroup.mem_normalizer_iff.mp hxN _).mp
      ⟨⟨t, ht.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have h4 : xY * πY ⟨t, hLY ht.2⟩ * xY⁻¹ = πY ⟨t', hLY t'.2⟩ := by
      rw [← hψb_mk t ht.2, ← hψb_mk t' t'.2, hxY, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact ht'e.symm
    have e1 : xY * QuotientGroup.mk' N y * xY⁻¹ = (xY * πY ⟨t, hLY ht.2⟩ * xY⁻¹) *
        (xY * πY ⟨b, hEY (hBE hb)⟩ * xY⁻¹) := by
      rw [hyeq, map_mul, hπY]
      group
    rw [e1, h4, hxYB b hb, ← map_mul]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr
      (E.mul_mem (Subgroup.mem_subgroupOf.mp ht').1 (hBE hb)), rfl⟩
  have hmoveY : xY * ((⟨d, hEY hdE⟩ : (L ⊔ E : Subgroup G)) : (L ⊔ E : Subgroup G) ⧸ N) * xY⁻¹ ≠
      ((⟨d, hEY hdE⟩ : (L ⊔ E : Subgroup G)) : (L ⊔ E : Subgroup G) ⧸ N) := by
    intro hfix
    have hfix' : xY * πY ⟨d, hEY hdE⟩ * xY⁻¹ = πY ⟨d, hEY hdE⟩ := hfix
    have hfixE : ∀ e (he : e ∈ E), xY * πY ⟨e, hEY he⟩ * xY⁻¹ = πY ⟨e, hEY he⟩ := by
      intro e he
      obtain ⟨b, hb, k, hek⟩ := hdec2 e he
      have hy : (⟨e, hEY he⟩ : (L ⊔ E : Subgroup G)) =
          ⟨b, hEY (hBE hb)⟩ * (⟨d, hEY hdE⟩ : (L ⊔ E : Subgroup G)) ^ k :=
        Subtype.ext (by simp [hek])
      have e1 : xY * πY (⟨b, hEY (hBE hb)⟩ * (⟨d, hEY hdE⟩ : (L ⊔ E : Subgroup G)) ^ k) * xY⁻¹ =
          (xY * πY ⟨b, hEY (hBE hb)⟩ * xY⁻¹) * (xY * πY ⟨d, hEY hdE⟩ * xY⁻¹) ^ k := by
        rw [conj_zpow, map_mul, map_zpow]
        group
      rw [hy, e1, hxYB b hb, hfix', map_mul, map_zpow]
    apply hmove
    apply hψb_inj
    have h1 := hfixE (t₀ : G) (Subgroup.mem_subgroupOf.mp ht₀).1
    rw [map_mul, map_mul, map_inv, ← hxY]
    exact h1
  have hEY3 : IsPGroup 3 (E.subgroupOf (L ⊔ E)) := hE3.comap_subtype
  obtain ⟨x, hxEY, hx3', hxd⟩ :=
    Sec12.exists_isPGroup_normalizer_moves N hN3 hEY3 hxY3 hxYE hmoveY
  refine ⟨x, x.2, ?_, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun e he => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hxEY ⟨e, hEY he⟩).mp
      (Subgroup.mem_subgroupOf.mpr he)
    exact Subgroup.mem_subgroupOf.mp h1
  · have h := hx3'.map (L ⊔ E).subtype
    rwa [MonoidHom.map_zpowers] at h
  · intro h
    apply hxd
    exact Subtype.ext (by simpa using h)

end Step1910O2Proof

theorem rank3II_19_10_O2_of_spor (h131 : Item131)
    (hspor : SporadicModels131) : Step1910O2 := by
  intro G _ _ A c L E M hctx d hdD hdc _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L :=
    ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT,
      hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE : IsE27 E := hctx.isE27
  have hA := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hE3 : IsPGroup 3 E := hE.isPGroup
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hELA : E ≤ L ⊔ A := hctx.le_sup.trans inf_le_left
  have hcE : c ∈ E :=
    mem_of_le_centralizer hst hctx.partTwoS_eq hEE (hA.1.2 c hcA)
      (hELA.trans (sup_le hLc (le_centralizer_of_mem hA.1.1 hcA)))
  have hcL : c ∈ L := hctx.mem_L
  have hEL : E ≤ Subgroup.normalizer (L : Set G) :=
    hELA.trans (sup_le Subgroup.le_normalizer hctx.mem_lA.2.1)
  set B := E ⊓ Sec4.thetaQuotCentralizer L with hBdef
  have hBE : B ≤ E := inf_le_left
  have hdE : d ∈ E := hdD.1
  have hdB : d ∉ B := by
    rintro ⟨-, hdC⟩
    apply hdc
    have hsec : d ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨hdD.2, fun l hl => ?_⟩
      have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hdC).2 l hl
      have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hl) _).mp h1
      have e : l * (l⁻¹ * (d * l * d⁻¹)) * l⁻¹ = d * l * d⁻¹ * l⁻¹ := by group
      rw [e] at h2
      exact h2
    rw [hctx.mem_lA.2.2.1] at hsec
    exact hsec
  have hd1 : d ≠ 1 := fun h => hdB (h ▸ B.one_mem)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hEexp d hdE) hd1
  have hType := Step1910O2Proof.type_of_mem h131 hspor hD hcL
  have hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hType with hSL | hA7 | hM22
    · exact Sec12.card_center_eq_three_of_isSLThreePi hSL
    · exact hA7.1
    · exact hM22.1
  have hdvd27 : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hS
  have hB9 : 9 ≤ Nat.card B :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun x hx => hEexp x hx.1)
      hctx.centralizer_noncyclic
  have hBcard : Nat.card B = 9 := by
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd27 B hBE)
    interval_cases k
    · rw [hk] at hB9; norm_num at hB9
    · rw [hk] at hB9; norm_num at hB9
    · rw [hk]; norm_num
    · exfalso
      have hBE' : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hk, hE.2]; norm_num)
      exact hdB (hBE' ▸ hdE)
  have hEL9 : 9 ≤ Nat.card (E ⊓ L : Subgroup G) :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun x hx => hEexp x hx.1) hctx.inf_noncyclic
  have hELcard : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd27 _ inf_le_left)
    interval_cases k
    · rw [hk] at hEL9; norm_num at hEL9
    · rw [hk] at hEL9; norm_num at hEL9
    · rw [hk]; norm_num
    · exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE.2]; norm_num)
      have hBL : B ≤ L := fun b hb => by
        have hb' : b ∈ E ⊓ L := by rw [hEL']; exact hb.1
        exact hb'.2
      have h := Step1910O2Proof.card_le_card_center_thetaQuot (hE3.to_le hBE) hBL inf_le_right
      rw [hZ3] at h
      omega
  have hTB : Nat.card ((E ⊓ L) ⊓ B : Subgroup G) ≤ 3 := by
    have h := Step1910O2Proof.card_le_card_center_thetaQuot (S := (E ⊓ L) ⊓ B)
      (hE3.to_le (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right)
    rwa [hZ3] at h
  have hTN : E ⊓ L ≤ Subgroup.normalizer (B : Set G) := fun t ht =>
    Subgroup.mem_normalizer_fintype fun b hb => by
      rw [hEab t ht.1 b (hBE hb), mul_inv_cancel_right]
      exact hb
  have hEsup1 : (E ⊓ L) ⊔ B = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hBE) ?_
    have h1 := Sec6.card_sup_mul_card_inf hTN
    rw [hELcard, hBcard] at h1
    have hpos : 0 < Nat.card ((E ⊓ L) ⊓ B : Subgroup G) := Nat.card_pos
    rw [hE.2]
    nlinarith
  have hdec1 : ∀ e ∈ E, ∃ t ∈ E ⊓ L, ∃ b ∈ B, e = t * b := by
    intro e he
    have he' : e ∈ (((E ⊓ L) ⊔ B : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, hEsup1]
      exact he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at he'
    obtain ⟨t, ht, b, hb, rfl⟩ := he'
    exact ⟨t, ht, b, hb, rfl⟩
  have hBN : B ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := fun b hb =>
    Sec12.mem_normalizer_zpowers_of_commute (hEab b (hBE hb) d hdE)
  have hinf : B ⊓ Subgroup.zpowers d = ⊥ := by
    have hdvd : Nat.card (B ⊓ Subgroup.zpowers d : Subgroup G) ∣ 3 := by
      rw [← hd3, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : B ⊓ Subgroup.zpowers d = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hd3])
      have hd' : d ∈ B ⊓ Subgroup.zpowers d := by
        rw [heq]
        exact Subgroup.mem_zpowers d
      exact hdB hd'.1
  have hEsup2 : B ⊔ Subgroup.zpowers d = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hBE (Subgroup.zpowers_le.mpr hdE)) ?_
    have h1 := Sec6.card_sup_mul_card_inf hBN
    rw [hinf, Subgroup.card_bot, mul_one, hBcard, Nat.card_zpowers, hd3] at h1
    rw [h1, hE.2]
  have hdec2 : ∀ e ∈ E, ∃ b ∈ B, ∃ k : ℤ, e = b * d ^ k := by
    intro e he
    have he' : e ∈ ((B ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, hEsup2]
      exact he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at he'
    obtain ⟨b, hb, z, hz, rfl⟩ := he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨b, hb, k, rfl⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ := three_not_dvd_card_aschbacherSolvableCore
  set π := QuotientGroup.mk' θ with hπ
  set T : Subgroup L := (E ⊓ L).subgroupOf L with hTdef
  have hT9 : Nat.card T = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans hELcard
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  set Tb : Subgroup (L ⧸ θ) := T.map π with hTbdef
  have hinjT := Sec12.injOn_mk_of_coprime θ hθ3 hT3
  have hTb9 : Nat.card Tb = 9 := by
    rw [hTbdef, Step198DProof.card_map_of_injOn π hinjT, hT9]
  have hTbe : CFSG.Assembly.IsElemAbelian 3 Tb :=
    Sec13.isElemAbelian_map (Step198DProof.isElemAbelian_subgroupOf
      (Late.isElemAbelian_of_le hE.1 inf_le_left) L) π
  set c' : L := ⟨c, hcL⟩ with hc'
  have hc'T : c' ∈ T := Subgroup.mem_subgroupOf.mpr ⟨hcE, hcL⟩
  have hc'Z : c' ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLc g.2))
  have hπcZ : π c' ∈ Subgroup.center (L ⧸ θ) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨c', hc'Z, rfl⟩
  have hc'3 : orderOf c' = 3 := by rw [← Subgroup.orderOf_coe]; exact hc3
  have hπc1 : π c' ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply hθ3
    have h' := orderOf_dvd_natCard (⟨c', h1⟩ : θ)
    rwa [Subgroup.orderOf_mk, hc'3] at h'
  have hZT : Subgroup.center (L ⧸ θ) ≤ Tb := by
    have hle : Subgroup.zpowers (π c') ≤ Subgroup.center (L ⧸ θ) :=
      Subgroup.zpowers_le.mpr hπcZ
    have hπc3 : orderOf (π c') = 3 := by
      refine orderOf_eq_prime ?_ hπc1
      have hc'p : c' ^ 3 = 1 := by rw [← hc'3]; exact pow_orderOf_eq_one c'
      rw [← map_pow, hc'p, map_one]
    have heq : Subgroup.zpowers (π c') = Subgroup.center (L ⧸ θ) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hZ3, Nat.card_zpowers, hπc3])
    rw [← heq]
    exact Subgroup.zpowers_le.mpr ⟨c', hc'T, rfl⟩
  have hType' : Sec4.IsSLThreePi (L ⧸ θ) ∨
      Sec4.IsTripleCover (L ⧸ θ) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ θ) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ θ) CFSG.Blueprint.NativeSporadic.M22 := by
    rcases hType with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨xb, hxN, hx3, tb, htb, hmove⟩ := KFacts.ks12NormalizerMoves _
    (Sec12.isQuasisimple_thetaQuot_of_mem hL) hType' Tb hTbe hTb9 hZT
  obtain ⟨t₀, ht₀, rfl⟩ := htb
  obtain ⟨x, hxY, hxE, hx3', hxd⟩ := Step1910O2Proof.exists_mem_sup_normalizer_moves hEL hE3
    hBE inf_le_right hdE hdec1 hdec2 hxN hx3 ht₀ hmove
  obtain ⟨a, ha⟩ : ∃ a : ℕ, x ^ 3 ^ a = 1 := by
    obtain ⟨a, ha⟩ := hx3' ⟨x, Subgroup.mem_zpowers x⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  have hxB : ∀ b ∈ B, x * b = b * x := fun b hb =>
    Step1910O2Proof.mul_comm_of_mem_sup hEL hE3 hEab hxY hxE hb
  have hxEB := Step1910O2Proof.conj_mul_inv_mem hEab hEexp hBE hdE hdB hdec2 hxE ha hxB hxd
  have hdx : d * x ≠ x * d := by
    intro h
    apply hxd
    rw [← h, mul_inv_cancel_right]
  set P := E ⊔ Subgroup.zpowers x with hPdef
  have hxNE : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set G) := Subgroup.zpowers_le.mpr hxE
  have hP3 : IsPGroup 3 P := by
    rw [hPdef, sup_comm]
    exact hx3'.to_sup_of_normal_right' hE3 hxNE
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  have hNEM : Subgroup.normalizer (E : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [hE.pRank_eq]; norm_num)).trans hctx.mem_scriptM.2
  have hPM : P ≤ M := sup_le hEM (hxNE.trans hNEM)
  have hBcen : ∀ b ∈ B, ∀ p ∈ P, b * p = p * b := by
    intro b hb p hp
    have hle : P ≤ Subgroup.centralizer ({b} : Set G) := by
      refine sup_le (le_centralizer_of_mem hE.1.1 (hBE hb)) (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxB b hb
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hp)).symm
  have hcomm : ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ B := by
    intro p hp
    have hp' : p ∈ ((E : Set G) * (Subgroup.zpowers x : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left E _ hxNE]
      exact hp
    obtain ⟨e, he, z, hz, rfl⟩ := hp'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 : x * (e * x ^ k) * x⁻¹ * (e * x ^ k)⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rw [h1]
    exact hxEB e he
  have hxZ2 : (⟨x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x)⟩ : P) ∈
      Subgroup.upperCentralSeries P 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
      Subgroup.upperCentralSeries_one]
    intro p
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hBcen _ (hcomm p p.2) q q.2).symm
  have hM2 : CFSG.Assembly.IsTwoLocal M := hctx.mem_scriptM.1.1
  have hfaith : ∀ y ∈ P, (∀ s ∈ CFSG.Open.pCoreOf 2 M, y * s = s * y) → y = 1 := by
    intro y hy hys
    have hyC : y ∈ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 M : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun s hs => (hys s hs).symm
    have hyO : y ∈ CFSG.Open.pCoreOf 2 M := hctx.charTwoType M hM2 ⟨hPM hy, hyC⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨y, hyO⟩
    obtain ⟨k, hk⟩ := hP3 ⟨y, hy⟩
    exact eq_one_of_pow_two_pow_of_pow_three_pow (by simpa using congrArg Subtype.val hj)
      (by simpa using congrArg Subtype.val hk)
  rcases Sec3.rank3II_3_19 hP3 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
      (hPM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hfaith
      (Subgroup.mem_sup_left hdE) hd3 with h | h
  · exact absurd (h x ⟨_, hxZ2, rfl⟩) hdx
  · exact h

theorem rank3II_19_10_O2_of
    (h131 : Item131) : Step1910O2 :=
  rank3II_19_10_O2_of_spor h131 Sec13.sporadicModels131

end CFSG.RankThree.PartTwo.Sec19
