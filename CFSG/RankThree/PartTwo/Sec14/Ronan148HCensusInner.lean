module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensus

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open scoped commutatorElement

structure InnerCfg {S : Type} [Group S] (B V : Subgroup S) : Prop where
  elem : CFSG.Assembly.IsElemAbelian 3 B
  card : Nat.card B = 9
  klein : IsKleinFour V
  norm : B ≤ Subgroup.normalizer (V : Set S)
  pt : ∃ b ∈ B, b ≠ 1 ∧ V ≤ Subgroup.centralizer ({b} : Set S)
  nc : ¬ B ≤ Subgroup.centralizer (V : Set S)
  inv : ∀ R : Subgroup S, R ∈ invariantPiSubgroups ⊤ B (piCompl 3) → R ≤ V

theorem not_innerCfg_of_not_dvd {S : Type} [Group S] [Finite S] (h : ¬ 9 ∣ Nat.card S)
    (B V : Subgroup S) : ¬ InnerCfg B V := fun hc =>
  h (hc.card ▸ Subgroup.card_subgroup_dvd_card B)

theorem not_innerCfg_of_noKlein {S : Type} [Group S]
    (h : ∀ b : S, orderOf b = 3 → ∀ W : Subgroup S, W ≤ Subgroup.centralizer ({b} : Set S) →
      ¬ IsKleinFour W)
    (B V : Subgroup S) : ¬ InnerCfg B V := by
  intro hc
  obtain ⟨b, hbB, hb1, hVb⟩ := hc.pt
  exact h b (orderOf_eq_prime (hc.elem.2 b hbB) hb1) V hVb hc.klein

theorem InnerCfg.map {S T : Type} [Group S] [Group T] (e : S ≃* T) {B V : Subgroup S}
    (hc : InnerCfg B V) : InnerCfg (B.map e.toMonoidHom) (V.map e.toMonoidHom) := by
  have hBe : ↥B ≃* ↥(B.map e.toMonoidHom) := B.equivMapOfInjective _ e.injective
  have hVe : ↥V ≃* ↥(V.map e.toMonoidHom) := V.equivMapOfInjective _ e.injective
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hux, ← hvy, ← map_mul, ← map_mul]
    congr 1
    have h := congrArg Subtype.val (hc.elem.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h
  · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hc.elem.2 u hu, map_one]
  · rw [← Nat.card_congr hBe.toEquiv, hc.card]
  · exact ⟨by rw [← Nat.card_congr hVe.toEquiv]; exact hc.klein.card_four,
      by rw [← Monoid.exponent_eq_of_mulEquiv hVe]; exact hc.klein.exponent_two⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro t
    obtain ⟨s, rfl⟩ := e.surjective t
    have h1 : ∀ x : S, e x ∈ V.map e.toMonoidHom ↔ x ∈ V := fun x => by
      rw [Subgroup.mem_map_equiv]; simp
    rw [show e.toMonoidHom b * e s * (e.toMonoidHom b)⁻¹ = e (b * s * b⁻¹) by
      simp [map_mul, map_inv], h1, h1]
    exact Subgroup.mem_normalizer_iff.mp (hc.norm hb) s
  · obtain ⟨b, hbB, hb1, hVb⟩ := hc.pt
    refine ⟨e b, ⟨b, hbB, rfl⟩, fun h => hb1 (e.injective (by rw [h, map_one])), ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e v * e b = e b * e v
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hVb hv)]
  · intro h
    apply hc.nc
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (h ⟨x, hx, rfl⟩) (e v) ⟨v, hv, rfl⟩
  · intro R hR
    have hR' : R.map e.symm.toMonoidHom ∈ invariantPiSubgroups ⊤ B (piCompl 3) := by
      refine ⟨le_top, fun q hq => hR.2.1 q ?_, ?_⟩
      · rwa [Subgroup.card_map_of_injective e.symm.injective] at hq
      · intro b hb
        rw [Subgroup.mem_normalizer_iff]
        intro s
        have h1 : ∀ x : S, x ∈ R.map e.symm.toMonoidHom ↔ e x ∈ R := fun x => by
          rw [Subgroup.mem_map_equiv]; simp
        rw [h1, h1, map_mul, map_mul, map_inv]
        exact Subgroup.mem_normalizer_iff.mp (hR.2.2 ⟨b, hb, rfl⟩) (e s)
    intro r hr
    have := hc.inv _ hR' (⟨r, hr, rfl⟩ : e.symm r ∈ R.map e.symm.toMonoidHom)
    exact ⟨e.symm r, this, by simp⟩

section Reduction

variable {X : Type} [Group X]

theorem mem_normalizer_centralizer {L : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (L : Set X)) :
    x ∈ Subgroup.normalizer ((Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc l hl
    have hm : x⁻¹ * l * x⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) l).mp hl
    have h1 := hc _ hm
    calc l * (x * c * x⁻¹) = x * ((x⁻¹ * l * x⁻¹⁻¹) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * l * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * l := by group
  · intro hc l hl
    have hm : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx l).mp hl
    have h1 := hc _ hm
    calc l * c = x⁻¹ * ((x * l * x⁻¹) * (x * c * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * c * x⁻¹) * (x * l * x⁻¹)) * x := by rw [h1]
      _ = c * l := by group

theorem le_normalizer_of_conj_mem' [Finite X] {Z R : Subgroup X}
    (h : ∀ z ∈ Z, ∀ r ∈ R, z * r * z⁻¹ ∈ R) : Z ≤ Subgroup.normalizer (R : Set X) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨r, hr, rfl⟩
    exact h z hz r hr
  · rw [Subgroup.card_map_of_injective (MulAut.conj z).injective]

theorem center_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

@[expose] noncomputable def conjAut {L : Subgroup X} {x : X} (hx : x ∈ Subgroup.normalizer (L : Set X)) :
    MulAut L :=
  ((MulAut.conj x).subgroupMap L).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hx))

@[simp]
theorem coe_conjAut_apply {L : Subgroup X} {x : X} (hx : x ∈ Subgroup.normalizer (L : Set X))
    (l : L) : ((conjAut hx l : L) : X) = x * l * x⁻¹ := rfl

theorem exists_inner_of_pow_three {L : Subgroup X} {S : Type} [Group S] (e : ↥L ≃* S)
    (hodd : ∀ α : MulAut S, Odd (orderOf α) → ∃ s : S, α = MulAut.conj s)
    {x : X} (hx : x ∈ Subgroup.normalizer (L : Set X)) (hx3 : x ^ 3 = 1) :
    ∃ k : L, ∀ l : L, x * (l : X) * x⁻¹ = (k : X) * l * (k : X)⁻¹ := by
  set α := conjAut hx with hαdef
  have hα3 : α ^ 3 = 1 := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
    simp only [hαdef, coe_conjAut_apply]
    calc x * (x * (x * (l : X) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * (l : X) * (x * x * x)⁻¹ := by
          group
      _ = x ^ 3 * (l : X) * (x ^ 3)⁻¹ := by rw [pow_three']
      _ = (l : X) := by rw [hx3]; group
  set β := MulAut.congr e α with hβdef
  have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα3, map_one]
  have hodd' : Odd (orderOf β) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hβ3) with h | h
    · rw [h]; exact odd_one
    · rw [h]; decide
  obtain ⟨s, hs⟩ := hodd β hodd'
  refine ⟨e.symm s, fun l => ?_⟩
  have h1 : β (e l) = s * e l * s⁻¹ := by rw [hs, MulAut.conj_apply]
  have h2 : β (e l) = e (α l) := by
    rw [hβdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have h3 : α l = e.symm s * l * (e.symm s)⁻¹ := by
    apply e.injective
    rw [← h2, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h4 := congrArg Subtype.val h3
  rw [hαdef, coe_conjAut_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h4
  exact h4

noncomputable def innerSub (L : Subgroup X) : Subgroup X where
  carrier := {x | x ∈ Subgroup.normalizer (L : Set X) ∧
    ∃ k : L, ∀ l : L, x * (l : X) * x⁻¹ = (k : X) * l * (k : X)⁻¹}
  mul_mem' := by
    rintro x y ⟨hxN, kx, hkx⟩ ⟨hyN, ky, hky⟩
    refine ⟨Subgroup.mul_mem _ hxN hyN, kx * ky, fun l => ?_⟩
    have h1 := hkx (ky * l * ky⁻¹)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc x * y * (l : X) * (x * y)⁻¹ = x * (y * l * y⁻¹) * x⁻¹ := by group
      _ = x * ((ky : X) * l * (ky : X)⁻¹) * x⁻¹ := by rw [hky l]
      _ = (kx : X) * ((ky : X) * l * (ky : X)⁻¹) * (kx : X)⁻¹ := h1
      _ = ((kx * ky : L) : X) * l * ((kx * ky : L) : X)⁻¹ := by
        simp only [Subgroup.coe_mul]; group
  one_mem' := ⟨Subgroup.one_mem _, 1, fun l => by simp⟩
  inv_mem' := by
    rintro x ⟨hxN, kx, hkx⟩
    refine ⟨Subgroup.inv_mem _ hxN, kx⁻¹, fun l => ?_⟩
    have hm : x⁻¹ * (l : X) * x⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) l).mp l.2
    have h1 := hkx ⟨_, hm⟩
    simp only [Subgroup.coe_mk] at h1
    have h2 : x * (x⁻¹ * (l : X) * x⁻¹⁻¹) * x⁻¹ = (l : X) := by group
    rw [h2] at h1
    simp only [Subgroup.coe_inv]
    calc x⁻¹ * (l : X) * x⁻¹⁻¹ = (kx : X)⁻¹ * ((kx : X) * (x⁻¹ * (l : X) * x⁻¹⁻¹) *
        (kx : X)⁻¹) * kx := by group
      _ = (kx : X)⁻¹ * (l : X) * kx := by rw [← h1]
      _ = (kx : X)⁻¹ * (l : X) * ((kx : X)⁻¹)⁻¹ := by group

theorem mem_innerSub {L : Subgroup X} {x : X} :
    x ∈ innerSub L ↔ x ∈ Subgroup.normalizer (L : Set X) ∧
      ∃ k : L, ∀ l : L, x * (l : X) * x⁻¹ = (k : X) * l * (k : X)⁻¹ :=
  Iff.rfl

theorem eq_of_conj_eq {L : Subgroup X} (hZ : Subgroup.center L = ⊥) {k k' : L}
    (h : ∀ l : L, (k : X) * l * (k : X)⁻¹ = (k' : X) * l * (k' : X)⁻¹) : k = k' := by
  have hc : k'⁻¹ * k ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 := h g
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : X) * ((k' : X)⁻¹ * k) = (k' : X)⁻¹ * ((k' : X) * g * (k' : X)⁻¹) * k := by group
      _ = (k' : X)⁻¹ * ((k : X) * g * (k : X)⁻¹) * k := by rw [h1]
      _ = (k' : X)⁻¹ * k * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  calc k = k' * (k'⁻¹ * k) := by group
    _ = k' := by rw [hc, mul_one]

noncomputable def innerElt {L : Subgroup X} (x : innerSub L) : L := Classical.choose x.2.2

theorem innerElt_spec {L : Subgroup X} (x : innerSub L) (l : L) :
    (x : X) * l * (x : X)⁻¹ = (innerElt x : X) * l * (innerElt x : X)⁻¹ :=
  Classical.choose_spec x.2.2 l

noncomputable def innerHom {L : Subgroup X} (hZ : Subgroup.center L = ⊥) : innerSub L →* L where
  toFun := innerElt
  map_one' := eq_of_conj_eq hZ fun l => by rw [← innerElt_spec]; simp
  map_mul' x y := eq_of_conj_eq hZ fun l => by
    rw [← innerElt_spec]
    set m : L := innerElt y * l * (innerElt y)⁻¹ with hm
    have h1 := innerElt_spec x m
    have h2 := innerElt_spec y l
    simp only [hm, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [← h2] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (x : X) * y * l * ((x : X) * y)⁻¹ = x * (y * l * (y : X)⁻¹) * (x : X)⁻¹ := by group
      _ = (innerElt x : X) * (y * l * (y : X)⁻¹) * (innerElt x : X)⁻¹ := h1
      _ = (innerElt x : X) * ((innerElt y : X) * l * (innerElt y : X)⁻¹) * (innerElt x : X)⁻¹ :=
        by rw [h2]
      _ = (innerElt x : X) * innerElt y * l * ((innerElt x : X) * innerElt y)⁻¹ := by group

theorem innerHom_spec {L : Subgroup X} (hZ : Subgroup.center L = ⊥) (x : innerSub L) (l : L) :
    (x : X) * l * (x : X)⁻¹ = (innerHom hZ x : X) * l * (innerHom hZ x : X)⁻¹ :=
  innerElt_spec x l

theorem innerHom_eq_one_iff {L : Subgroup X} (hZ : Subgroup.center L = ⊥) (x : innerSub L) :
    innerHom hZ x = 1 ↔ ∀ l ∈ L, (x : X) * l = l * x := by
  constructor
  · intro h l hl
    have := innerHom_spec hZ x ⟨l, hl⟩
    rw [h] at this
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at this
    calc (x : X) * l = (x : X) * l * (x : X)⁻¹ * x := by group
      _ = l * x := by rw [this]
  · intro h
    refine (eq_of_conj_eq hZ fun l => ?_).symm
    rw [← innerHom_spec]
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
    rw [h l l.2]
    group

theorem innerHom_of_mem {L : Subgroup X} (hZ : Subgroup.center L = ⊥) (x : innerSub L)
    (hxL : (x : X) ∈ L) : innerHom hZ x = ⟨x, hxL⟩ :=
  eq_of_conj_eq hZ fun l => by rw [← innerHom_spec]

end Reduction

section Row

set_option linter.unusedSectionVars false

theorem olRow_of_inner (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a)
    (hodd : ∀ α : MulAut S, Odd (orderOf α) → ∃ s : S, α = MulAut.conj s)
    (hno : ∀ B V : Subgroup S, ¬ InnerCfg B V) :
    OLRow (fun T _ => Nonempty (T ≃* S)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZS := center_eq_bot_of_simple hnab
  have hZL : Subgroup.center L = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, hZS, Subgroup.map_bot]
  have hCP : IsPGroup 3 (Subgroup.centralizer (P : Set X)) :=
    ThreeGroup.isPGroup_centralizer hcfg.perf hcfg.triple hcfg.e27
  have hPpg : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hcfg.e27.1.2 x x.2)⟩
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcfg.e27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZP : Subgroup.center X ≤ P := center_le_of_isE27 hcfg.perf hcfg.triple hcfg.e27
  set I := innerSub L with hIdef
  have hPI : P ≤ I := fun x hx =>
    ⟨hcfg.normL hx, exists_inner_of_pow_three e hodd (hcfg.normL hx) (hcfg.e27.1.2 x hx)⟩
  have hQ3 : ¬ 3 ∣ Nat.card Q := by rw [hcfg.klein.card_four]; norm_num
  have hQP : Q = ⁅Q, P⁆ := by
    have h := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three P Q hPpg hQ3 hcfg.normQ
    rw [inf_eq_bot_of_not_dvd hCP hQ3, sup_bot_eq] at h
    exact h
  have hQI : Q ≤ I := by
    rw [hQP, Subgroup.commutator_le]
    intro q hq p hp
    have hqN : q ∈ Subgroup.normalizer (L : Set X) := hcfg.QnormL hq
    obtain ⟨-, kp, hkp⟩ := hPI hp
    have hqpq : q * p * q⁻¹ ∈ I := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hqN (hcfg.normL hp)) (Subgroup.inv_mem _ hqN),
        ⟨q * kp * q⁻¹, (Subgroup.mem_normalizer_iff.mp hqN kp).mp kp.2⟩, fun l => ?_⟩
      have hm : q⁻¹ * (l : X) * q⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hqN) l).mp l.2
      have h1 := hkp ⟨_, hm⟩
      simp only [Subgroup.coe_mk] at h1 ⊢
      calc q * p * q⁻¹ * (l : X) * (q * p * q⁻¹)⁻¹ =
          q * (p * (q⁻¹ * (l : X) * q⁻¹⁻¹) * p⁻¹) * q⁻¹ := by group
        _ = q * ((kp : X) * (q⁻¹ * (l : X) * q⁻¹⁻¹) * (kp : X)⁻¹) * q⁻¹ := by rw [h1]
        _ = q * kp * q⁻¹ * (l : X) * (q * kp * q⁻¹)⁻¹ := by group
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hqpq (Subgroup.inv_mem _ (hPI hp))
  set φ := innerHom hZL with hφ
  set P' := P.subgroupOf I with hP'
  set Q' := Q.subgroupOf I with hQ'
  set B := P'.map φ with hB
  set V := Q'.map φ with hV
  have hker : ∀ x : I, φ x = 1 ↔ ∀ l ∈ L, (x : X) * l = l * x := innerHom_eq_one_iff hZL
  have hCQ : Q ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
    have hPn : P ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) :=
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hcfg.normQ hx,
        mem_normalizer_centralizer (hcfg.normL hx)⟩
    rcases eq_bot_or_eq_of_le_kleinFour hcfg.klein inf_le_left hPn hCP with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hcfg.Qnc
  have hQinj : Function.Injective (φ.comp Q'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : ((y : I) : X) ∈ Q ⊓ Subgroup.centralizer (L : Set X) := by
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      exact ((hker y).mp hy l hl).symm
    rw [hCQ, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hcfgI : InnerCfg B V := by
    refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hux, ← hvy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hPab _ hu _ hv)
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, show u ^ 3 = 1 from Subtype.ext (hcfg.e27.1.2 _ hu), map_one]
    ·
      set ψ := φ.comp P'.subtype with hψ
      have hrange : ψ.range = B := range_comp_subtype φ P'
      have hP'card : Nat.card P' = 27 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPI).toEquiv, hcfg.e27.2]
      have hkercard : Nat.card ψ.ker = 3 := by
        have hmap : ψ.ker.map (I.subtype.comp P'.subtype) = Subgroup.center X := by
          apply le_antisymm
          · rintro _ ⟨x, hx, rfl⟩
            exact hcfg.cent _ x.2 ((hker (x : I)).mp hx)
          · intro z hz
            exact ⟨⟨⟨z, hPI (hZP hz)⟩, hZP hz⟩, (MonoidHom.mem_ker).mpr
              ((hker _).mpr fun l _ => ((Subgroup.mem_center_iff.mp hz) l).symm), rfl⟩
        have hinj : Function.Injective (I.subtype.comp P'.subtype) := fun a b h =>
          P'.subtype_injective (I.subtype_injective h)
        rw [← Subgroup.card_map_of_injective hinj, hmap, hcfg.triple.1]
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hP'card,
        hkercard] at h
      omega
    ·
      have e' : ↥Q' ≃* ↥V := by
        rw [hV, ← range_comp_subtype φ Q']
        exact MonoidHom.ofInjective hQinj
      have eQ : ↥Q' ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQI
      exact ⟨by rw [← Nat.card_congr e'.toEquiv, Nat.card_congr eQ.toEquiv]; exact hcfg.klein.card_four,
        by rw [← Monoid.exponent_eq_of_mulEquiv e', Monoid.exponent_eq_of_mulEquiv eQ];
           exact hcfg.klein.exponent_two⟩
    ·
      refine le_normalizer_of_conj_mem' fun b hb v hv => ?_
      obtain ⟨x, hx, rfl⟩ := hb
      obtain ⟨y, hy, rfl⟩ := hv
      refine ⟨x * y * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show ((x : I) : X) * (y : X) * ((x : I) : X)⁻¹ ∈ Q
      exact (Subgroup.mem_normalizer_iff.mp (hcfg.normQ hx) _).mp hy
    ·
      obtain ⟨p₀, hp₀, hp₀z, hQp₀⟩ := hcfg.pt
      set x₀ : I := ⟨p₀, hPI hp₀⟩ with hx₀
      refine ⟨φ x₀, ⟨x₀, hp₀, rfl⟩, fun h => hp₀z (hcfg.cent p₀ hp₀ ((hker x₀).mp h)), ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hQp₀ hy)
    ·
      intro hBV
      have hPQ : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x := by
        intro x hx y hy
        set x' : I := ⟨x, hPI hx⟩
        set y' : I := ⟨y, hQI hy⟩
        have hc : φ x' * φ y' = φ y' * φ x' :=
          (Subgroup.mem_centralizer_iff.mp (hBV ⟨x', hx, rfl⟩) (φ y') ⟨y', hy, rfl⟩).symm
        have hq : x' * y' * x'⁻¹ * y'⁻¹ ∈ Q' := by
          show x * y * x⁻¹ * y⁻¹ ∈ Q
          exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hcfg.normQ hx) y).mp hy)
            (Subgroup.inv_mem _ hy)
        have h1 : (φ.comp Q'.subtype) ⟨_, hq⟩ = 1 := by
          simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
          rw [hc]; group
        have h2 := congrArg Subtype.val (congrArg Subtype.val (hQinj (h1.trans (map_one _).symm)))
        simp only [OneMemClass.coe_one, Subgroup.coe_mul, Subgroup.coe_inv] at h2
        calc x * y = x * y * x⁻¹ * y⁻¹ * y * x := by group
          _ = y * x := by rw [h2, one_mul]
      have hQC : Q ≤ Q ⊓ Subgroup.centralizer (P : Set X) := fun y hy =>
        ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => hPQ x hx y hy⟩
      rw [inf_eq_bot_of_not_dvd hCP hQ3, le_bot_iff] at hQC
      have := hcfg.klein.card_four
      rw [hQC, Subgroup.card_bot] at this
      omega
    ·
      intro R hR
      set RX := R.map L.subtype with hRX
      have hRX3 : ¬ 3 ∣ Nat.card RX := by
        rw [Subgroup.card_map_of_injective L.subtype_injective]
        exact not_dvd_of_isPiSubgroup hR.2.1
      have hPR : P ≤ Subgroup.normalizer (RX : Set X) := by
        refine le_normalizer_of_conj_mem' fun x hx r hr => ?_
        obtain ⟨r', hr', rfl⟩ := hr
        set x' : I := ⟨x, hPI hx⟩
        have h1 := innerHom_spec hZL x' r'
        have h2 : φ x' * r' * (φ x')⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hR.2.2 ⟨x', hx, rfl⟩) r').mp hr'
        refine ⟨_, h2, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        exact h1.symm
      have hRQ := hcfg.inv RX ((Subgroup.map_subtype_le R).trans le_sup_left)
        ⟨le_top, isPiSubgroup_of_not_dvd hRX3, hPR⟩
      intro r hr
      have hrQ : (r : X) ∈ Q := hRQ ⟨r, hr, rfl⟩
      refine ⟨⟨r, hQI hrQ⟩, hrQ, ?_⟩
      exact innerHom_of_mem hZL ⟨r, hQI hrQ⟩ r.2
  exact hno _ _ (hcfgI.map e)

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
