module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res9ProofQ
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofSp48
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open Item812Res3 (IsMaxPSub)

namespace Item812Res10

theorem pow_nine_zmod9 : ∀ z : Multiplicative (ZMod 9), z ^ 9 = 1 := by
  decide

theorem pow_nine_zmod9sq : ∀ z : Multiplicative (ZMod 9 × ZMod 9), z ^ 9 = 1 := by
  decide

theorem card_cube_zmod9 :
    Nat.card {z : Multiplicative (ZMod 9) // z ^ 3 = 1} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_cube_zmod9sq :
    Nat.card {z : Multiplicative (ZMod 9 × ZMod 9) // z ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_cube_congr {H M : Type*} [Group H] [Group M] (e : H ≃* M) :
    Nat.card {x : H // x ^ 3 = 1} = Nat.card {z : M // z ^ 3 = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change x ^ 3 = 1 ↔ e x ^ 3 = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff])

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_theta {Q X : Subgroup G} (hQ : IsPGroup 3 Q) {x : G} (hxQ : x ∈ Q)
    (hxθ : x ∈ inSubgroup (aschbacherSolvableCore 3) X) : x = 1 := by
  obtain ⟨-, -, h3, -⟩ := solvable_prime_complement_core_characterization
    (H := X) Nat.prime_three
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨y, hy, rfl⟩ := hxθ
  have h1 : orderOf ((y : X) : G) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h2 : orderOf ((y : X) : G) ∣ Nat.card (aschbacherSolvableCore 3 X) := by
    rw [Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard _ hy
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have h1' : orderOf ((y : X) : G) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact orderOf_eq_one_iff.mp h1'

theorem mem_theta_of_mem_thetaQuotCentralizer {X : Subgroup G}
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥) {x : G} (hxX : x ∈ X)
    (hx : x ∈ Sec4.thetaQuotCentralizer X) : x ∈ inSubgroup (aschbacherSolvableCore 3) X := by
  obtain ⟨-, hl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
  have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨x, hxX⟩ ∈
      Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) := by
    rw [Subgroup.mem_center_iff]
    intro w
    induction w using QuotientGroup.induction_on with
    | H l =>
      obtain ⟨t, ht, hte⟩ := hl l l.2
      have hte' : (t : G) = (l : G)⁻¹ * (x * l * x⁻¹) := hte
      have h1 : (⟨x, hxX⟩ : X) * l * (⟨x, hxX⟩ : X)⁻¹ = l * t := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hte']
        group
      have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) t = 1 :=
        (QuotientGroup.eq_one_iff t).mpr ht
      calc QuotientGroup.mk' (aschbacherSolvableCore 3 X) l *
            QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨x, hxX⟩ =
          QuotientGroup.mk' (aschbacherSolvableCore 3 X) (l * t) *
            QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨x, hxX⟩ := by
            rw [map_mul, h2, mul_one]
        _ = QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨x, hxX⟩ *
            QuotientGroup.mk' (aschbacherSolvableCore 3 X) l := by
            rw [← h1, ← map_mul, ← map_mul]
            congr 1
            group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  exact ⟨_, hcen, rfl⟩

theorem commute_of_mem {Q X : Subgroup G} (hQ : IsPGroup 3 Q) {u v : G}
    (hu : u ∈ Q ⊓ Sec4.thetaQuotCentralizer X) (hv : v ∈ Q ⊓ X) : u * v = v * u := by
  obtain ⟨-, hl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hu.2
  have hθ := hl v hv.2
  have hQ' : v⁻¹ * (u * v * u⁻¹) ∈ Q :=
    Q.mul_mem (Q.inv_mem hv.1) (Q.mul_mem (Q.mul_mem hu.1 hv.1) (Q.inv_mem hu.1))
  have h1 := eq_one_of_mem_theta hQ hQ' hθ
  have h2 : u * v * u⁻¹ = v := by
    calc u * v * u⁻¹ = v * (v⁻¹ * (u * v * u⁻¹)) := by group
      _ = v := by rw [h1, mul_one]
  calc u * v = u * v * u⁻¹ * u := by group
    _ = v * u := by rw [h2]

theorem inf_eq_bot {Q X : Subgroup G} (hQ : IsPGroup 3 Q)
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥) :
    (Q ⊓ Sec4.thetaQuotCentralizer X) ⊓ (Q ⊓ X) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨hxQ, hxC⟩, -, hxX⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_theta hQ hxQ (mem_theta_of_mem_thetaQuotCentralizer hZ hxX hxC)

theorem sup_le_normalizer (X : Subgroup G) :
    X ⊔ Sec4.thetaQuotCentralizer X ≤ Subgroup.normalizer (X : Set G) :=
  sup_le Subgroup.le_normalizer (Subgroup.map_subtype_le _)

theorem card_le_of_le_sup {R X : Subgroup G} (hRp : IsPGroup 3 R)
    (hRX : R ≤ X ⊔ Sec4.thetaQuotCentralizer X)
    (h5 : ¬ 3 ^ 5 ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X)) :
    Nat.card R ≤ Nat.card (R ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) * 81 := by
  classical
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := hRX.trans (sup_le_normalizer X)
  set ρ : R →* MulAut (X ⧸ aschbacherSolvableCore 3 X) :=
    (thetaQuotMulAut X).comp ((compAction X).comp (Subgroup.inclusion hRN)) with hρ
  have hker : Nat.card ρ.ker ≤ Nat.card (R ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun r : ρ.ker => (⟨(r : R), (r : R).2, ⟨⟨(r : R), hRN (r : R).2⟩, r.2, rfl⟩⟩ :
        (R ⊓ Sec4.thetaQuotCentralizer X : Subgroup G))) ?_
    intro r s hrs
    have hrs' := congrArg Subtype.val hrs
    simp only at hrs'
    exact Subtype.ext (Subtype.ext hrs')
  have hrange : ρ.range ≤ (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →*
      MulAut (X ⧸ aschbacherSolvableCore 3 X)).range := by
    rintro _ ⟨r, rfl⟩
    exact (Item812Res2.mem_sup_thetaQuotCentralizer_iff (hRN r.2)).mp (hRX r.2)
  have hdvd : Nat.card ρ.range ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
    refine (Subgroup.card_dvd_of_le hrange).trans ?_
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_card _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ρ.range := hRp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk4 : k ≤ 4 := by
    by_contra hk5
    push Not at hk5
    apply h5
    have : 3 ^ 5 ∣ 3 ^ k := Nat.pow_dvd_pow 3 hk5
    rw [← hk] at this
    exact this.trans hdvd
  have hrange81 : Nat.card ρ.range ≤ 81 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
      _ = 81 := by norm_num
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  exact Nat.mul_le_mul hker hrange81

end Item812Res10


@[expose] def Fin812Q2Card : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      Nat.card (Q ⊓ X : Subgroup G) = 81

@[expose] def Fin812Q2Iso : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      Nonempty (↥(Q ⊓ X) ≃* Multiplicative (ZMod 9 × ZMod 9))

@[expose] def Fin812Q1Cyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      Nonempty (↥(Q ⊓ Sec4.thetaQuotCentralizer X) ≃* Multiplicative (ZMod 9))

namespace Item812Res10

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X Y : Subgroup G}
    {n : ℕ} (h : Sec8Final G A c L a b X Y n) :
    Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥ := by
  set F := GaloisField 2 3 with hFdef
  have hK : Nat.card F = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  set e : X ⧸ aschbacherSolvableCore 3 X ≃* StatedProj (StatedSp 2 F) :=
    h.item89_X.some.trans (Sec4.projSpEquivStatedProj 2 F) with he
  have hZ : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := Item812Res2.center_statedProj_eq_bot
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hz'
  rw [Subgroup.mem_bot]
  exact hz'

theorem not_dvd_card {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X Y : Subgroup G}
    {n : ℕ} (h : Sec8Final G A c L a b X Y n) :
    ¬ 3 ^ 5 ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
  rw [Nat.card_congr h.item89_X.some.toEquiv, Item812Res2.card_projSp_two_three]
  norm_num

theorem sec8R_eq_sup {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X Y : Subgroup G}
    {n : ℕ} (h : Sec8Final G A c L a b X Y n) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQ2 : Nat.card (Q ⊓ X : Subgroup G) = 81)
    (hQ1 : Nat.card (Q ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 9) :
    sec8R Q X = (Q ⊓ Sec4.thetaQuotCentralizer X) ⊔ (Q ⊓ X) ∧
      Nat.card (sec8R Q X) = 729 := by
  have hZ := center_eq_bot h
  have hcomm : ∀ u ∈ Q ⊓ Sec4.thetaQuotCentralizer X, ∀ v ∈ Q ⊓ X, u * v = v * u :=
    fun u hu v hv => commute_of_mem hQ hu hv
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [inf_eq_bot hQ hZ, Subgroup.card_bot, mul_one, hQ1, hQ2] at hcard
  have hle : (Q ⊓ Sec4.thetaQuotCentralizer X) ⊔ (Q ⊓ X) ≤ sec8R Q X :=
    sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_right))
      (le_inf inf_le_left (inf_le_right.trans le_sup_left))
  have hR := card_le_of_le_sup (hQ.to_le inf_le_left) (inf_le_right : sec8R Q X ≤ _)
    (not_dvd_card h)
  have hR1 : (sec8R Q X ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≤
      Q ⊓ Sec4.thetaQuotCentralizer X := inf_le_inf_right _ inf_le_left
  have hR1c := Subgroup.card_le_of_le hR1
  rw [hQ1] at hR1c
  have hR729 : Nat.card (sec8R Q X) ≤ 729 := by
    calc Nat.card (sec8R Q X) ≤ _ := hR
      _ ≤ 9 * 81 := Nat.mul_le_mul_right _ hR1c
      _ = 729 := by norm_num
  have heq : (Q ⊓ Sec4.thetaQuotCentralizer X) ⊔ (Q ⊓ X) = sec8R Q X :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hR729)
  refine ⟨heq.symm, ?_⟩
  rw [← heq, hcard]

end Item812Res10

open Item812Res10

theorem fin812Q2Iso_of (hC : Fin812Q2Card) : Fin812Q2Iso := by
  have hK := kFSp48SylowThree_holds
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hQ2 := hC G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  set e := h.item89_X.some with he
  set φ : ↥(Q ⊓ X) →* ↥(projSp 2 (GaloisField 2 3)) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp
      (Subgroup.inclusion (inf_le_right : Q ⊓ X ≤ X))) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 X)
        (Subgroup.inclusion (inf_le_right : Q ⊓ X ≤ X) x) = 1 := by
      have := congrArg e.symm hx
      simpa [hφ] using this
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : ((x : G)) = 1 :=
      eq_one_of_mem_theta hQ.2.1 x.2.1 ⟨_, h1, rfl⟩
    exact Subtype.ext h2
  have hcard : Nat.card φ.range = 81 := by
    rw [← hQ2, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  obtain ⟨ψ⟩ := hK φ.range hcard
  exact ⟨(MonoidHom.ofInjective hinj).trans ψ⟩

theorem fin812Q2Iso_of_card (hC : Fin812Q2Card) : Fin812Q2Iso :=
  fin812Q2Iso_of hC

theorem fin812RStruct_of_q (hQ2 : Fin812Q2Iso) (hQ1 : Fin812Q1Cyclic) : Fin812RStruct := by
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  obtain ⟨e2⟩ := hQ2 G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  obtain ⟨e1⟩ := hQ1 G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hc2 : Nat.card (Q ⊓ X : Subgroup G) = 81 := by
    rw [Nat.card_congr e2.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hc1 : Nat.card (Q ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 9 := by
    rw [Nat.card_congr e1.toEquiv]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨hReq, hRcard⟩ := sec8R_eq_sup h hQ.2.1 hc2 hc1
  have hcomm : ∀ u ∈ Q ⊓ Sec4.thetaQuotCentralizer X, ∀ v ∈ Q ⊓ X, u * v = v * u :=
    fun u hu v hv => commute_of_mem hQ.2.1 hu hv
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hab1 : ∀ u ∈ Q ⊓ Sec4.thetaQuotCentralizer X, ∀ u' ∈ Q ⊓ Sec4.thetaQuotCentralizer X,
      u * u' = u' * u := by
    intro u hu u' hu'
    have := e1.injective (by rw [map_mul, map_mul, mul_comm] :
      e1 (⟨u, hu⟩ * ⟨u', hu'⟩) = e1 (⟨u', hu'⟩ * ⟨u, hu⟩))
    exact congrArg Subtype.val this
  have hab2 : ∀ v ∈ Q ⊓ X, ∀ v' ∈ Q ⊓ X, v * v' = v' * v := by
    intro v hv v' hv'
    have := e2.injective (by rw [map_mul, map_mul, mul_comm] :
      e2 (⟨v, hv⟩ * ⟨v', hv'⟩) = e2 (⟨v', hv'⟩ * ⟨v, hv⟩))
    exact congrArg Subtype.val this
  have hp1 : ∀ u ∈ Q ⊓ Sec4.thetaQuotCentralizer X, u ^ 9 = 1 := by
    intro u hu
    have := e1.injective (by rw [map_pow, pow_nine_zmod9, map_one] :
      e1 (⟨u, hu⟩ ^ 9) = e1 1)
    simpa using congrArg Subtype.val this
  have hp2 : ∀ v ∈ Q ⊓ X, v ^ 9 = 1 := by
    intro v hv
    have := e2.injective (by rw [map_pow, pow_nine_zmod9sq, map_one] :
      e2 (⟨v, hv⟩ ^ 9) = e2 1)
    simpa using congrArg Subtype.val this
  refine ⟨?_, by rw [hRcard]; norm_num, ?_⟩
  · intro x hx y hy
    rw [← SetLike.mem_coe, hReq, hset] at hx hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hy
    calc u * v * (u' * v') = (u * u') * (v * v') := by
          rw [mul_assoc, ← mul_assoc v, (hcomm u' hu' v hv).symm, mul_assoc, mul_assoc]
      _ = (u' * u) * (v' * v) := by rw [hab1 u hu u' hu', hab2 v hv v' hv']
      _ = u' * v' * (u * v) := by
          rw [mul_assoc, ← mul_assoc u, hcomm u hu v' hv', mul_assoc, mul_assoc]
  · intro x hx
    rw [← SetLike.mem_coe, hReq, hset] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    rw [(Commute.mul_pow (hcomm u hu v hv) 9), hp1 u hu, hp2 v hv, one_mul]

theorem fin812ROmega_of_q (hQ2 : Fin812Q2Iso) (hQ1 : Fin812Q1Cyclic) : Fin812ROmega := by
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ x hxR hx3
  classical
  obtain ⟨e2⟩ := hQ2 G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  obtain ⟨e1⟩ := hQ1 G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hc2 : Nat.card (Q ⊓ X : Subgroup G) = 81 := by
    rw [Nat.card_congr e2.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hc1 : Nat.card (Q ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 9 := by
    rw [Nat.card_congr e1.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hS := fin812RStruct_of_q hQ2 hQ1 G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  obtain ⟨hRc, -, -⟩ := hS
  obtain ⟨hReq, -⟩ := sec8R_eq_sup h hQ.2.1 hc2 hc1
  have hcomm : ∀ u ∈ Q ⊓ Sec4.thetaQuotCentralizer X, ∀ v ∈ Q ⊓ X, u * v = v * u :=
    fun u hu v hv => commute_of_mem hQ.2.1 hu hv
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hinf := inf_eq_bot hQ.2.1 (center_eq_bot h)
  have hAab := h.mem_partTwoF.1
  set Ω : Subgroup G :=
    { carrier := {y | y ∈ sec8R Q X ∧ y ^ 3 = 1}
      mul_mem' := by
        rintro y z ⟨hy, hy3⟩ ⟨hz, hz3⟩
        refine ⟨(sec8R Q X).mul_mem hy hz, ?_⟩
        rw [(Commute.mul_pow (hRc y hy z hz) 3), hy3, hz3, one_mul]
      one_mem' := ⟨(sec8R Q X).one_mem, one_pow 3⟩
      inv_mem' := by
        rintro y ⟨hy, hy3⟩
        exact ⟨(sec8R Q X).inv_mem hy, by rw [inv_pow, hy3, inv_one]⟩ } with hΩ
  have hAB : A ≤ Subgroup.centralizer (sec8B A X : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (hAab.1.is_comm.comm ⟨z, Item812Res4.b_le_a hz⟩ ⟨y, hy⟩)
  have hQA := hQ.2.2 _ (Item812Res4.isPGroup_sup hQ.2.1
    (Item812Res4.isPGroup_of_isElemAbelian hAab) (hAPa.trans hPaQ)) le_sup_left (sup_le hQ.1 hAB)
  have hAQ : A ≤ Q := hQA ▸ le_sup_right
  have hBΩ : sec8B A X ≤ Ω := fun y hy =>
    ⟨⟨hAQ (Item812Res4.b_le_a hy), hy.2⟩, hAab.2 y (Item812Res4.b_le_a hy)⟩
  have hS1 : Nat.card {u : ↥(Q ⊓ Sec4.thetaQuotCentralizer X) // u ^ 3 = 1} = 3 :=
    (card_cube_congr e1).trans card_cube_zmod9
  have hS2 : Nat.card {v : ↥(Q ⊓ X) // v ^ 3 = 1} = 9 :=
    (card_cube_congr e2).trans card_cube_zmod9sq
  have hmem : ∀ p : {u : ↥(Q ⊓ Sec4.thetaQuotCentralizer X) // u ^ 3 = 1} ×
      {v : ↥(Q ⊓ X) // v ^ 3 = 1}, ((p.1 : ↥(Q ⊓ Sec4.thetaQuotCentralizer X)) : G) *
        ((p.2 : ↥(Q ⊓ X)) : G) ∈ Ω := by
    rintro ⟨⟨u, hu3⟩, ⟨v, hv3⟩⟩
    refine ⟨?_, ?_⟩
    · rw [hReq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left u.2) (Subgroup.mem_sup_right v.2)
    · have hu3' : (u : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hu3
      have hv3' : (v : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hv3
      change ((u : G) * (v : G)) ^ 3 = 1
      rw [(Commute.mul_pow (hcomm u u.2 v v.2) 3), hu3', hv3', one_mul]
  have hsurj : Function.Surjective (fun p : {u : ↥(Q ⊓ Sec4.thetaQuotCentralizer X) //
      u ^ 3 = 1} × {v : ↥(Q ⊓ X) // v ^ 3 = 1} => (⟨_, hmem p⟩ : Ω)) := by
    rintro ⟨y, hyR, hy3⟩
    rw [← SetLike.mem_coe, hReq, hset] at hyR
    obtain ⟨u, hu, v, hv, rfl⟩ := hyR
    have h3 : u ^ 3 * v ^ 3 = 1 := by
      rw [← (Commute.mul_pow (hcomm u hu v hv) 3)]
      exact hy3
    have hu3 : u ^ 3 = 1 := by
      have hmem1 : u ^ 3 ∈ (Q ⊓ Sec4.thetaQuotCentralizer X) ⊓ (Q ⊓ X) := by
        refine ⟨Subgroup.pow_mem _ hu 3, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h3]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hv 3)
      rw [hinf] at hmem1
      exact hmem1
    have hv3 : v ^ 3 = 1 := by
      rw [hu3, one_mul] at h3
      exact h3
    exact ⟨(⟨⟨u, hu⟩, Subtype.ext (by simpa using hu3)⟩,
      ⟨⟨v, hv⟩, Subtype.ext (by simpa using hv3)⟩), rfl⟩
  have hΩcard : Nat.card Ω ≤ 27 := by
    calc Nat.card Ω ≤ Nat.card ({u : ↥(Q ⊓ Sec4.thetaQuotCentralizer X) // u ^ 3 = 1} ×
          {v : ↥(Q ⊓ X) // v ^ 3 = 1}) := Nat.card_le_card_of_surjective _ hsurj
      _ = 27 := by rw [Nat.card_prod, hS1, hS2]
  have hB27 := Item812Res8.card_sec8B h
  have hBeqΩ : sec8B A X = Ω := Subgroup.eq_of_le_of_card_ge hBΩ (by rw [hB27]; exact hΩcard)
  have hxΩ : x ∈ Ω := ⟨hxR, hx3⟩
  rw [← hBeqΩ] at hxΩ
  exact Item812Res4.b_le_a hxΩ

theorem fin812QR_of_res10 (h45 : Sec4.Item4_5) (h84 : Pair84A)
    (hC : Fin812Q2Card) (hQ1 : Fin812Q1Cyclic) : Fin812QR :=
  fin812QR_of_res9 h45 h84 (fin812RStruct_of_q (fin812Q2Iso_of_card hC) hQ1)
    (fin812ROmega_of_q (fin812Q2Iso_of_card hC) hQ1)

end CFSG.RankThree.PartTwo.Sec8
