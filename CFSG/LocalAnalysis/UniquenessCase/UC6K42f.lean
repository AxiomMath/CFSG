module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K42e
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem center_le_commutator_uc6 {x : G} {D Q : Subgroup G} (hD : D = Subgroup.zpowers x)
    (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) (z : ↥Q)
    (hz : x * (z : G) = (z : G) * x) : z ∈ commutator ↥Q := by
  have hx0 : x ∈ D := hD ▸ Subgroup.mem_zpowers x
  have hxN : x ∈ normalizer (Q : Set G) := hDQ hx0
  let α : MulAut ↥Q := Q.normalizerMonoidHom ⟨x, hxN⟩
  have hαe : ∀ e : ↥Q, ((α e : ↥Q) : G) = x * (e : G) * x⁻¹ := fun e => rfl
  let ab : ↥Q →* Abelianization ↥Q := Abelianization.of
  let g : ↥Q →* Abelianization ↥Q := (ab.comp α.toMonoidHom) * ab⁻¹
  let gb : Abelianization ↥Q →* Abelianization ↥Q := Abelianization.lift g
  have hgb : ∀ q : ↥Q, gb (ab q) = ab (α q) * (ab q)⁻¹ := fun q => by
    show Abelianization.lift g (Abelianization.of q) = _
    rw [Abelianization.lift_apply_of]
    rfl
  let Rg : Subgroup G := ((gb.range).comap ab).map Q.subtype
  have hRg : ∀ q : ↥Q, (q : G) ∈ Rg ↔ ab q ∈ gb.range := by
    intro q
    constructor
    · rintro ⟨q', hq', hqq⟩
      have : q' = q := Subtype.ext hqq
      rw [this] at hq'
      exact hq'
    · intro h
      exact ⟨q, h, rfl⟩
  have hnat : ∀ k : ℕ, ∀ y ∈ Q, ⁅x ^ k, y⁆ ∈ Rg := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      have hxk : x ^ k ∈ D := hD ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k
      have hyk : x ^ k * y * (x ^ k)⁻¹ ∈ Q := (mem_normalizer_iff.1 (hDQ hxk) y).1 hy
      have h1 : ⁅x ^ (k + 1), y⁆ = ⁅x, x ^ k * y * (x ^ k)⁻¹⁆ * ⁅x ^ k, y⁆ := by
        simp only [commutatorElement_def, pow_succ]
        group
      rw [h1]
      refine Rg.mul_mem ?_ (ih y hy)
      let w : ↥Q := ⟨_, hyk⟩
      have hw : ⁅x, x ^ k * y * (x ^ k)⁻¹⁆ = ((α w * w⁻¹ : ↥Q) : G) := rfl
      rw [hw, hRg, map_mul, map_inv, ← hgb]
      exact ⟨ab w, rfl⟩
  have hle : ⁅D, Q⁆ ≤ Rg := by
    rw [Subgroup.commutator_le]
    intro d hd y hy
    classical
    rw [hD, mem_zpowers_iff_mem_range_orderOf] at hd
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hd
    exact hnat k y hy
  have hq : ∀ q : ↥Q, ab q ∈ gb.range := fun q =>
    (hRg q).1 (hle (by rw [hcomm]; exact q.2))
  have hsurj : Function.Surjective gb := by
    intro a
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective a
    exact hq q
  have hinj : Function.Injective gb := Finite.injective_iff_surjective.2 hsurj
  have hαz : α z = z := Subtype.ext (by
    rw [hαe, hz]
    group)
  have h1 : gb (ab z) = gb 1 := by
    rw [hgb, hαz, map_one, mul_inv_cancel]
  have h2 : ab z = 1 := hinj h1
  rw [← Abelianization.ker_of]
  exact h2

theorem centralizer_le_center_uc6 {D Q : Subgroup G} (hcomm : ⁅D, Q⁆ = Q)
    (hcomm1 : commutator ↥Q ≤ center ↥Q)
    (hDZ : ∀ d ∈ D, ∀ z ∈ (center ↥Q).map Q.subtype, d * z = z * d)
    {c : G} (hcQ : c ∈ Q) (hcD : ∀ d ∈ D, d * c = c * d) :
    c ∈ (center ↥Q).map Q.subtype := by
  have hcen : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ (center ↥Q).map Q.subtype := by
    intro a ha b hb
    exact ⟨⁅(⟨a, ha⟩ : ↥Q), ⟨b, hb⟩⁆,
      hcomm1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)), rfl⟩
  have hgen : Q ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [← hcomm, Subgroup.commutator_le]
    intro d hd q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdq : d * q * d⁻¹ * q⁻¹ ∈ Q := by
      have := Subgroup.commutator_mem_commutator hd hq
      rw [hcomm] at this
      simpa [commutatorElement_def] using this
    have hz1 : ⁅c, q⁆ ∈ (center ↥Q).map Q.subtype := hcen c hcQ q hq
    have hdc : d * c * d⁻¹ = c := by rw [hcD d hd]; group
    obtain ⟨z, hz⟩ : ∃ z : G, z = c * q * c⁻¹ * q⁻¹ := ⟨_, rfl⟩
    have hzmem : z ∈ (center ↥Q).map Q.subtype := by rw [hz]; exact hz1
    have hcu : c * (d * q * d⁻¹) * c⁻¹ * (d * q * d⁻¹)⁻¹ = z := by
      calc c * (d * q * d⁻¹) * c⁻¹ * (d * q * d⁻¹)⁻¹
          = (d * c * d⁻¹) * (d * q * d⁻¹) * (d * c * d⁻¹)⁻¹ * (d * q * d⁻¹)⁻¹ := by rw [hdc]
        _ = d * (c * q * c⁻¹ * q⁻¹) * d⁻¹ := by group
        _ = z := by
          have h1 := hDZ d hd z hzmem
          rw [hz] at h1 ⊢
          rw [h1]
          group
    have hA : c * (d * q * d⁻¹) * c⁻¹ = z * (d * q * d⁻¹) := mul_inv_eq_iff_eq_mul.1 hcu
    have hB : c * q * c⁻¹ = z * q := by rw [hz]; group
    have hC : z * (d * q * d⁻¹ * q⁻¹) = (d * q * d⁻¹ * q⁻¹) * z :=
      ((mem_centerG_uc6.1 hzmem).2 _ hdq).symm
    have hconj : c * (d * q * d⁻¹ * q⁻¹) * c⁻¹ = d * q * d⁻¹ * q⁻¹ := by
      calc c * (d * q * d⁻¹ * q⁻¹) * c⁻¹
          = (c * (d * q * d⁻¹) * c⁻¹) * (c * q * c⁻¹)⁻¹ := by group
        _ = (z * (d * q * d⁻¹)) * (z * q)⁻¹ := by rw [hA, hB]
        _ = z * (d * q * d⁻¹ * q⁻¹) * z⁻¹ := by group
        _ = (d * q * d⁻¹ * q⁻¹) * z * z⁻¹ := by rw [hC]
        _ = d * q * d⁻¹ * q⁻¹ := by group
    exact (mul_inv_eq_iff_eq_mul.1 hconj).symm
  exact mem_centerG_uc6.2 ⟨hcQ, fun g hg => Subgroup.mem_centralizer_singleton_iff.1 (hgen hg)⟩

theorem zpowers_eq_of_ne_one_uc6 {r : ℕ} (hr : r.Prime) {D : Subgroup G} (hD : Nat.card D = r)
    {x : G} (hx : x ∈ D) (hx1 : x ≠ 1) : Subgroup.zpowers x = D := by
  have hdvd : orderOf x ∣ r := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥D)
    rwa [Subgroup.orderOf_mk, hD] at this
  have hord : orderOf x = r :=
    ((Nat.dvd_prime hr).1 hdvd).resolve_left (fun h => hx1 (orderOf_eq_one_iff.1 h))
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx) ?_
  rw [Nat.card_zpowers, hord, hD]

theorem isExtraspecial_uc6 {Q : Subgroup G} (hcard : Nat.card (center ↥Q) = 2)
    (hcomm1 : commutator ↥Q ≤ center ↥Q) (hsq : ∀ x : ↥Q, x ^ 2 ∈ center ↥Q)
    (hnab : ¬ IsMulCommutative ↥Q) : CFSG.IsExtraspecial 2 ↥Q where
  center_order_p := hcard
  quotient_elementary_abelian := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center ↥Q)).2 hcomm1
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hsq x
  quotient_nontrivial := by
    by_contra htriv
    have : Subsingleton (↥Q ⧸ center ↥Q) := not_nontrivial_iff_subsingleton.mp htriv
    have hcenter_top : center ↥Q = ⊤ :=
      QuotientGroup.subgroup_eq_top_of_subsingleton (center ↥Q) inferInstance
    apply hnab
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxcent : x ∈ center ↥Q := by simp [hcenter_top]
    exact (Subgroup.mem_center_iff.mp hxcent y).symm

theorem structure2_uc6 {r : ℕ} (hr : r.Prime) {D Q : Subgroup G} (hD : Nat.card D = r)
    (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) (hnab : ¬ IsMulCommutative ↥Q)
    (hcomm1 : commutator ↥Q ≤ center ↥Q) (hsq : ∀ x : ↥Q, x ^ 2 ∈ center ↥Q)
    (hDZ : ∀ d ∈ D, ∀ z ∈ (center ↥Q).map Q.subtype, d * z = z * d)
    (hcyc : IsCyclic ↥(center ↥Q)) :
    Nat.card (center ↥Q) = 2 ∧
      ∀ x ∈ D, x ≠ 1 → ∀ y ∈ Q, x * y = y * x → y ∈ (center ↥Q).map Q.subtype := by
  have hcsq : ∀ x y : ↥Q, ⁅x, y⁆ ^ 2 = 1 := by
    intro x y
    have h1 : ⁅x * x, y⁆ = ⁅x, y⁆ * ⁅x, y⁆ := by
      have hc : ⁅x, y⁆ ∈ center ↥Q := hcomm1 (by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
      calc ⁅x * x, y⁆ = x * ⁅x, y⁆ * x⁻¹ * ⁅x, y⁆ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅x, y⁆ * ⁅x, y⁆ := by
            rw [Subgroup.mem_center_iff.mp hc x, mul_inv_cancel_right]
    have h2 : ⁅x * x, y⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.2
      rw [← sq]
      exact (Subgroup.mem_center_iff.1 (hsq x) y).symm
    rw [h2] at h1
    rw [sq]
    exact h1.symm
  letI : CommGroup ↥(center ↥Q) := IsMulCommutative.instCommGroup
  let Ω : Subgroup ↥Q :=
    (powMonoidHom 2 : ↥(center ↥Q) →* ↥(center ↥Q)).ker.map (center ↥Q).subtype
  have hΩ : commutator ↥Q ≤ Ω := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hxy : ⁅x, y⁆ ∈ center ↥Q :=
      hcomm1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
    refine ⟨⟨⁅x, y⁆, hxy⟩, ?_, rfl⟩
    show (powMonoidHom 2 : ↥(center ↥Q) →* ↥(center ↥Q)) ⟨⁅x, y⁆, hxy⟩ = 1
    apply Subtype.ext
    simpa using hcsq x y
  haveI := hcyc
  haveI : IsCyclic ↥(commutator ↥Q) := Subgroup.isCyclic_of_le hcomm1
  have hcard1 : Nat.card ↥(commutator ↥Q) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro c
    obtain ⟨z, hz, hzc⟩ := hΩ c.2
    apply Subtype.ext
    have hz2 : (z : ↥Q) ^ 2 = 1 := by simpa using congrArg Subtype.val (MonoidHom.mem_ker.1 hz)
    show (c : ↥Q) ^ 2 = 1
    rw [← hzc]
    exact hz2
  obtain ⟨x, hxD, -⟩ := exists_generator_uc6 hr hD
  have hfit : center ↥Q ≤ commutator ↥Q := by
    intro z hz
    have hx : x ∈ D := hxD ▸ Subgroup.mem_zpowers x
    have hzg : (z : G) ∈ (center ↥Q).map Q.subtype := ⟨z, hz, rfl⟩
    exact center_le_commutator_uc6 hxD hDQ hcomm z (hDZ x hx _ hzg)
  have hcen_eq : center ↥Q = commutator ↥Q := le_antisymm hfit hcomm1
  have hcard : Nat.card (center ↥Q) = 2 := by
    rw [hcen_eq]
    have hne : Nat.card ↥(commutator ↥Q) ≠ 1 := by
      intro h1
      apply hnab
      refine ⟨⟨fun a b => ?_⟩⟩
      have hmem : ⁅a, b⁆ ∈ commutator ↥Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      have hbot : commutator ↥Q = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      rw [hbot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 hmem)
    exact ((Nat.dvd_prime Nat.prime_two).1 hcard1).resolve_left hne
  refine ⟨hcard, ?_⟩
  intro x' hx' hx1 y hy hxy
  have hDx : Subgroup.zpowers x' = D := zpowers_eq_of_ne_one_uc6 hr hD hx' hx1
  apply centralizer_le_center_uc6 hcomm hcomm1 hDZ hy
  intro d hd
  rw [← hDx] at hd
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
  exact (Commute.zpow_left (show Commute x' y from hxy) n).eq

end CFSG.LocalAnalysis.UniquenessCase.UC6
