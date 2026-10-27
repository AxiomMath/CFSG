module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofBar
public import CFSG.RankThree.PartTwo.Sec21.Commute33Odd
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement Pointwise

namespace Item211LieProof

variable {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}

section Theta

@[expose] def cenMod (L O P : Subgroup G) (hLO : L ≤ Subgroup.normalizer (O : Set G))
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) : Subgroup L where
  carrier := {l | ∀ p ∈ P, (l : G) * p * (l : G)⁻¹ * p⁻¹ ∈ O}
  one_mem' := by
    intro p _
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact O.one_mem
  mul_mem' := by
    intro l₁ l₂ h₁ h₂ p hp
    have e : ((l₁ * l₂ : L) : G) * p * ((l₁ * l₂ : L) : G)⁻¹ * p⁻¹ =
        (l₁ : G) * ((l₂ : G) * p * (l₂ : G)⁻¹ * p⁻¹) * (l₁ : G)⁻¹ *
          ((l₁ : G) * p * (l₁ : G)⁻¹ * p⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    refine O.mul_mem ?_ (h₁ p hp)
    exact (Subgroup.mem_normalizer_iff.mp (hLO l₁.2) _).mp (h₂ p hp)
  inv_mem' := by
    intro l h₁ p hp
    have hq : (l : G)⁻¹ * p * (l : G) ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hLP (L.inv_mem l.2)) p).mp hp
      rwa [inv_inv] at this
    have h1 := O.inv_mem (h₁ _ hq)
    have e : ((l⁻¹ : L) : G) * p * ((l⁻¹ : L) : G)⁻¹ * p⁻¹ =
        ((l : G) * ((l : G)⁻¹ * p * (l : G)) * (l : G)⁻¹ * ((l : G)⁻¹ * p * (l : G))⁻¹)⁻¹ := by
      simp only [InvMemClass.coe_inv]
      group
    rw [e]
    exact h1

omit [Finite G] in
theorem cenMod_normal {L O P : Subgroup G} (hLO : L ≤ Subgroup.normalizer (O : Set G))
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) : (cenMod L O P hLO hLP).Normal := by
  refine ⟨fun l hl g p hp => ?_⟩
  have hq : (g : G)⁻¹ * p * (g : G) ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (hLP (L.inv_mem g.2)) p).mp hp
    rwa [inv_inv] at this
  have h1 := hl _ hq
  have h2 := (Subgroup.mem_normalizer_iff.mp (hLO g.2) _).mp h1
  have e : ((g * l * g⁻¹ : L) : G) * p * ((g * l * g⁻¹ : L) : G)⁻¹ * p⁻¹ =
      (g : G) * ((l : G) * ((g : G)⁻¹ * p * (g : G)) * (l : G)⁻¹ *
        ((g : G)⁻¹ * p * (g : G))⁻¹) * (g : G)⁻¹ := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  rw [e]
  exact h2

noncomputable abbrev centerPreTheta (L : Subgroup G) : Subgroup L :=
  (Subgroup.center (lBar L)).comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))

omit [Finite G] in
theorem le_centerPreTheta (L : Subgroup G) [Finite L] :
    aschbacherSolvableCore 3 L ≤ centerPreTheta L := by
  intro t ht
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff t).mpr ht]
  exact Subgroup.one_mem _

theorem isSolvable_centerPreTheta (L : Subgroup G) : Group.IsSolvable (centerPreTheta L) := by
  have hT : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
  let g : centerPreTheta L →* Subgroup.center (lBar L) :=
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (centerPreTheta L).subtype).codRestrict
      _ fun x => x.2
  have hcomm : Group.IsSolvable (Subgroup.center (lBar L)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (le_centerPreTheta L)) g ?_
  intro x hx
  have hx' : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (x : L) = 1 := congrArg Subtype.val hx
  exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp hx'⟩, rfl⟩

theorem isSimpleGroup_quotient_centerPreTheta {L : Subgroup G} (hq : IsQuasisimple (lBar L)) :
    IsSimpleGroup (L ⧸ centerPreTheta L) := by
  have : IsSimpleGroup (lBar L ⧸ Subgroup.center (lBar L)) := hq.2.1
  have e : L ⧸ centerPreTheta L ≃* lBar L ⧸ Subgroup.center (lBar L) :=
    (QuotientGroup.quotientQuotientEquivQuotient (aschbacherSolvableCore 3 L) (centerPreTheta L)
      (le_centerPreTheta L)).symm.trans (QuotientGroup.quotientMulEquivOfEq
        (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _))
  exact e.isSimpleGroup

theorem commutator_mem_oddCore (hS : A ∈ partTwoS G) (h : PairFacts A E U c L) :
    ∀ l ∈ L, ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) L,
      l * t * l⁻¹ * t⁻¹ ∈ inSubgroup (pPrimeCore 2) (inSubgroup (aschbacherSolvableCore 3) L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθ
  set O := inSubgroup (pPrimeCore 2) θ with hO
  set P := Commute33Steps.oddTwoCore θ with hP
  have : (aschbacherSolvableCore 3 L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic L
  have hNθ : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (θ : Set G) :=
    SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L _
  have hNO : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    hNθ.trans (Commute33Steps.normalizer_le_normalizer_oddCore θ)
  have hNP : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    hNθ.trans (Commute33Steps.normalizer_le_normalizer_oddTwoCore θ)
  have hLO : L ≤ Subgroup.normalizer (O : Set G) := Subgroup.le_normalizer.trans hNO
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer.trans hNP
  have hθs : Group.IsSolvable θ := by
    rw [hθ, inSubgroup]
    have := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
    exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.equivMapOfInjective
      (aschbacherSolvableCore 3 L) L.subtype L.subtype_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  have hθ3 : ¬ 3 ∣ Nat.card θ := by
    rw [hθ, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore L
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using h.Ae.2 _ g.2)⟩
  obtain ⟨S, hSA⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow 3 2
    Nat.prime_three Nat.prime_two A θ hA3 (h.AL.trans hNθ)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
  set S' : Subgroup G := (S : Subgroup θ).map θ.subtype with hS'
  have hS'θ : S' ≤ θ := Subgroup.map_subtype_le _
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map θ.subtype
  have hAS : ⁅S', A⁆ = ⊥ :=
    Sec6.commutator_eq_bot_of_mem_partTwoS hS h.cA h.c1 le_rfl
      (hS'θ.trans (theta_le_theta_centralizer h.Lc)) hS'2 hSA
  have hsa : ∀ s ∈ S', ∀ a ∈ A, s * a = a * s := by
    intro s hs a ha
    have h1 : ⁅s, a⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← hAS]
      exact Subgroup.commutator_mem_commutator hs ha
    rwa [commutatorElement_eq_one_iff_mul_comm] at h1
  have hθO : θ ≤ Subgroup.normalizer (O : Set G) := fun x hx =>
    Commute33Steps.normalizer_le_normalizer_oddCore θ (Subgroup.le_normalizer hx)
  have hset : ((O ⊔ S' : Subgroup G) : Set G) = (O : Set G) * (S' : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left O S' (hS'θ.trans hθO)
  have hAP : ∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ O := by
    intro a ha p hp
    have hpOS : p ∈ ((O ⊔ S' : Subgroup G) : Set G) := Commute33Steps.oddTwoCore_le_sup S hp
    rw [hset] at hpOS
    obtain ⟨o, ho, s, hs, rfl⟩ := hpOS
    have hsz : s * a = a * s := hsa s hs a ha
    have e : a * (o * s) * a⁻¹ * (o * s)⁻¹ = (a * o * a⁻¹) * o⁻¹ := by
      calc a * (o * s) * a⁻¹ * (o * s)⁻¹ = a * o * (s * a⁻¹) * s⁻¹ * o⁻¹ := by group
        _ = a * o * (a⁻¹ * s) * s⁻¹ * o⁻¹ := by
            rw [show s * a⁻¹ = a⁻¹ * s from by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, hsz, ← mul_assoc, inv_mul_cancel,
                one_mul]]
        _ = (a * o * a⁻¹) * o⁻¹ := by group
    rw [e]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNO (h.AL ha)) o).mp ho) (O.inv_mem ho)
  set C := cenMod L O P hLO hLP with hC
  have hCn : C.Normal := cenMod_normal hLO hLP
  have hLA : ∀ (l : L) (a : G), a ∈ A →
      ∀ p ∈ P, ((l : G) * a * (l : G)⁻¹ * a⁻¹) * p * ((l : G) * a * (l : G)⁻¹ * a⁻¹)⁻¹ * p⁻¹
        ∈ O := by
    intro l a ha p hp
    have hl : (l : G) ∈ L := l.2
    have ho₁ : a⁻¹ * p * a⁻¹⁻¹ * p⁻¹ ∈ O := hAP a⁻¹ (A.inv_mem ha) p hp
    rw [inv_inv] at ho₁
    set o₁ := a⁻¹ * p * a * p⁻¹ with ho₁def
    have hq : (l : G)⁻¹ * p * (l : G) ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hLP (L.inv_mem hl)) p).mp hp
      rwa [inv_inv] at this
    set q := (l : G)⁻¹ * p * (l : G) with hqdef
    have ho₂ : (l : G)⁻¹ * o₁ * (l : G) ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hLO (L.inv_mem hl)) o₁).mp ho₁
      rwa [inv_inv] at this
    set o₂ := (l : G)⁻¹ * o₁ * (l : G) with ho₂def
    have ho₃ : a * o₂ * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hNO (h.AL ha)) o₂).mp ho₂
    have ho₄ : a * q * a⁻¹ * q⁻¹ ∈ O := hAP a ha q hq
    have ho₅ : (l : G) * ((a * o₂ * a⁻¹) * (a * q * a⁻¹ * q⁻¹)) * (l : G)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hLO hl) _).mp (O.mul_mem ho₃ ho₄)
    have e : ((l : G) * a * (l : G)⁻¹ * a⁻¹) * p * ((l : G) * a * (l : G)⁻¹ * a⁻¹)⁻¹ * p⁻¹ =
        (l : G) * ((a * o₂ * a⁻¹) * (a * q * a⁻¹ * q⁻¹)) * (l : G)⁻¹ := by
      rw [ho₂def, ho₁def, hqdef]
      group
    rw [e]
    exact ho₅
  have hLAC : ∀ (l : L) (a : G) (ha : a ∈ A),
      (⟨(l : G) * a * (l : G)⁻¹ * a⁻¹, by
        have h1 : a * (l : G)⁻¹ * a⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (h.AL ha) _).mp (L.inv_mem l.2)
        have e : (l : G) * a * (l : G)⁻¹ * a⁻¹ = (l : G) * (a * (l : G)⁻¹ * a⁻¹) := by group
        rw [e]
        exact L.mul_mem l.2 h1⟩ : L) ∈ C := fun l a ha p hp => hLA l a ha p hp
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt h.Lc
  have hTs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
  set K₀ := centerPreTheta L with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPreTheta L
  have : IsSimpleGroup (L ⧸ K₀) := isSimpleGroup_quotient_centerPreTheta h.q
  have : Group.IsPerfect (lBar L) := h.q.1
  have hCK : ¬ C ≤ K₀ := by
    intro hCK
    have hAK : A ≤ Sec4.thetaQuotCentralizer L := by
      intro a ha
      set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, h.AL ha⟩) with hσ
      have hid : σ = 1 := KFacts.eq_one_of_forall_mul_inv_mem_center fun z => by
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
        rw [hσ, Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        have hmem : l⁻¹ * L.normalizerMonoidHom ⟨a, h.AL ha⟩ l ∈ C := by
          have h1 := hLAC l⁻¹ a ha
          convert h1 using 1
          apply Subtype.ext
          simp [mul_assoc]
        exact hCK hmem
      refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨h.AL ha, fun l hl => ?_⟩
      have h2 := congrArg (fun φ : MulAut (lBar L) => φ ((⟨l, hl⟩ : L) : lBar L)) hid
      simp only [hσ, Sec4.thetaQuotMulAut_mk, MulAut.one_apply] at h2
      rw [eq_comm, QuotientGroup.eq] at h2
      exact ⟨_, h2, rfl⟩
    have hAc : A ≤ Subgroup.zpowers c := by
      rw [← h.CA]
      exact le_inf le_rfl hAK
    have h1 := Subgroup.card_le_of_le (h.EA.trans hAc)
    rw [Nat.card_zpowers, h.orderOf_c, h.E27] at h1
    omega
  have hCtop : C = ⊤ := Sec4.Census.eq_top_of_not_le hK₀s hCK
  have hLPO : ∀ l ∈ L, ∀ p ∈ P, l * p * l⁻¹ * p⁻¹ ∈ O := by
    intro l hl p hp
    have hmem : (⟨l, hl⟩ : L) ∈ C := hCtop ▸ Subgroup.mem_top _
    exact hmem p hp
  have hθP : θ ≤ P := by
    intro t ht
    refine Commute33Steps.mem_oddTwoCore_of_commutator_mem hθs ht fun y hy => ?_
    have htL : t ∈ L := Subgroup.map_subtype_le _ ht
    have h1 := hLPO t htL y hy
    rw [commutatorElement_def]
    exact h1
  intro l hl t ht
  exact hLPO l hl t (hθP ht)

end Theta

section Lift

omit [Finite G] in
theorem mem_normalizer_sup_of' [Finite G] {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : ∀ x ∈ H₁, g * x * g⁻¹ ∈ H₁ ⊔ H₂) (h₂ : ∀ x ∈ H₂, g * x * g⁻¹ ∈ H₁ ⊔ H₂) :
    g ∈ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  have hle : H₁ ⊔ H₂ ≤ (H₁ ⊔ H₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun x hx => h₁ x hx) (fun x hx => h₂ x hx)
  exact Subgroup.mem_normalizer_fintype fun x hx => hle hx

theorem normalizer_le_normalizer_theta (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) : Set G) := by
  have : (aschbacherSolvableCore 3 L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic L
  exact SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L _

theorem theta_le_thetaQuotCentralizer (L : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) L ≤ Sec4.thetaQuotCentralizer L := by
  intro t ht
  have htL : t ∈ L := Subgroup.map_subtype_le _ ht
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer htL, fun l hl => ?_⟩
  have h1 : l⁻¹ * t * l ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have := (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_theta L (Subgroup.le_normalizer (L.inv_mem hl))) t).mp ht
    rwa [inv_inv] at this
  have e : l⁻¹ * (t * l * t⁻¹) = (l⁻¹ * t * l) * t⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ht)

theorem barAct_eq_one_of_mem {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hK : g ∈ Sec4.thetaQuotCentralizer L) : barAct L ⟨g, hg⟩ = 1 := by
  obtain ⟨y, hy, hyg⟩ := hK
  have : y = ⟨g, hg⟩ := Subtype.ext hyg
  rw [← this]
  exact hy

theorem barAct_mk {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    barAct L ⟨g, hg⟩ (l : lBar L) =
      ((⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg l).mp l.2⟩ : L) : lBar L) :=
  rfl

theorem barAct_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    barAct L ⟨l, Subgroup.le_normalizer hl⟩ = MulAut.conj ((⟨l, hl⟩ : L) : lBar L) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H m =>
    simp only [barAct, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk, MulAut.conj_apply,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    congr 1

theorem mem_theta_of_mem_thetaQuotCentralizer {L : Subgroup G}
    (hZ : Subgroup.center (lBar L) = ⊥) {l : G} (hl : l ∈ L)
    (hK : l ∈ Sec4.thetaQuotCentralizer L) : l ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have h1 := barAct_eq_one_of_mem (Subgroup.le_normalizer hl) hK
  rw [barAct_of_mem hl] at h1
  have h2 : ((⟨l, hl⟩ : L) : lBar L) = 1 :=
    conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm)
  rw [QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem exists_pow_isPGroup_three {H M : Type*} [Group H] [Finite H] [Group M] (f : H →* M)
    (g : H) (hg : f g ^ 3 = 1) : ∃ k a : ℕ, (g ^ k) ^ (3 ^ a) = 1 ∧ f (g ^ k) = f g := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hcop : m.Coprime (orderOf (f g)) := by
    have h3 : orderOf (f g) ∣ 3 := orderOf_dvd_of_pow_eq_one hg
    exact Nat.Coprime.coprime_dvd_right h3
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
  obtain ⟨k', hk'⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨m * k', a, ?_, ?_⟩
  · rw [← pow_mul, show m * k' * 3 ^ a = (3 ^ a * m) * k' by ring, pow_mul, ← hn,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_mul, hk']

theorem exists_fixed_conj_of_coprime {P J N : Subgroup G} (hP : IsPGroup 3 P)
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) (hNJ : N ≤ J)
    (hJN : J ≤ Subgroup.normalizer (N : Set G)) (hPN : P ≤ Subgroup.normalizer (N : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) {j : G} (hj : j ∈ J)
    (hjP : ∀ g ∈ P, j⁻¹ * (g * j * g⁻¹) ∈ N) :
    ∃ w ∈ J, w * j⁻¹ ∈ N ∧ ∀ g ∈ P, g * w * g⁻¹ = w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : P →* MulAut J := (Sec4.compAction J).comp (Subgroup.inclusion hPJ) with hφ
  have hφa : ∀ (g : P) (y : J), ((φ g y : J) : G) = (g : G) * y * (g : G)⁻¹ := fun g y => rfl
  set N' := N.subgroupOf J with hN'
  have : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mpr hJN
  have hN'3 : ¬ 3 ∣ Nat.card N' := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNJ).toEquiv]
    exact hN3
  have hφN : ∀ g, ∀ n ∈ N', φ g n ∈ N' := by
    intro g n hn
    rw [Subgroup.mem_subgroupOf, hφa]
    exact (Subgroup.mem_normalizer_iff.mp (hPN g.2) _).mp (Subgroup.mem_subgroupOf.mp hn)
  have hy : ∀ g, ((φ g ⟨j, hj⟩ : J) : J ⧸ N') = ((⟨j, hj⟩ : J) : J ⧸ N') := by
    intro g
    rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hφa]
    exact hjP g g.2
  obtain ⟨w, hw, hfix⟩ := KFacts.exists_fixed_of_coprime (p := 3) hP φ N' hN'3 hφN ⟨j, hj⟩ hy
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hw
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hw
  refine ⟨w, w.2, ?_, fun g hg => ?_⟩
  · have h1 : (j⁻¹ * (w : G)) ∈ N := by
      have := N.inv_mem hw
      rwa [mul_inv_rev, inv_inv] at this
    have e : (w : G) * j⁻¹ = (w : G) * (j⁻¹ * (w : G)) * (w : G)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hJN w.2) _).mp h1
  · have := congrArg Subtype.val (hfix ⟨g, hg⟩)
    rw [hφa] at this
    exact this

theorem exists_lift_centralizer (hS : A ∈ partTwoS G) (h : PairFacts A E U c L)
    (hZodd : Odd (Nat.card (Subgroup.center (lBar L)))) {τ : MulAut (lBar L)}
    (hτL : τ ∈ barImage L L) (hτU : ∀ u ∈ barImage L U, τ * u = u * τ) (hτ3 : τ ^ 3 = 1) :
    τ ∈ barImage L (L ⊓ Subgroup.centralizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (L : Set G) with hNdef
  obtain ⟨x₀, hx₀N, hx₀L, hx₀τ⟩ := mem_barImage_iff.mp hτL
  set φ : U →* MulAut (lBar L) := (barAct L).comp (Subgroup.inclusion h.UN) with hφ
  have hφu : ∀ u : U, φ u = barAct L ⟨u, h.UN u.2⟩ := fun u => rfl
  set z₀ : lBar L := ((⟨x₀, hx₀L⟩ : L) : lBar L) with hz₀
  have hτz₀ : τ = MulAut.conj z₀ := by rw [← hx₀τ, ← barAct_of_mem hx₀L]
  have hZφ : ∀ g : U, ∀ n ∈ Subgroup.center (lBar L), φ g n ∈ Subgroup.center (lBar L) := by
    intro g n hn
    rw [Subgroup.mem_center_iff] at hn ⊢
    intro y
    obtain ⟨y', rfl⟩ := (φ g).surjective y
    rw [← map_mul, ← map_mul, hn y']
  have hconj : ∀ w z : lBar L, MulAut.conj w = MulAut.conj z →
      w⁻¹ * z ∈ Subgroup.center (lBar L) := by
    intro w z hwz
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun σ : MulAut (lBar L) => σ y) hwz
    simp only [MulAut.conj_apply] at h1
    calc y * (w⁻¹ * z) = w⁻¹ * (w * y * w⁻¹) * z := by group
      _ = w⁻¹ * (z * y * z⁻¹) * z := by rw [h1]
      _ = w⁻¹ * z * y := by group
  have hy : ∀ g : U, ((φ g z₀ : lBar L) : lBar L ⧸ Subgroup.center (lBar L)) =
      (z₀ : lBar L ⧸ Subgroup.center (lBar L)) := by
    intro g
    rw [QuotientGroup.eq]
    refine hconj _ _ ?_
    rw [← KFacts.mul_mulAutConj_mul_inv, ← hτz₀]
    have hc := hτU (φ g) (mem_barImage_iff.mpr ⟨g, h.UN g.2, g.2, rfl⟩)
    rw [← hc]
    group
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center (lBar L)) := fun h2 =>
    (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨z', hz'z₀, hz'fix⟩ := KFacts.exists_fixed_of_coprime (p := 2) h.U2 φ
    (Subgroup.center (lBar L)) hZ2 hZφ z₀ hy
  have hτz' : τ = MulAut.conj z' := by
    rw [QuotientGroup.eq] at hz'z₀
    have h1 : MulAut.conj z₀ = MulAut.conj z' * MulAut.conj (z'⁻¹ * z₀) := by
      rw [← map_mul, mul_inv_cancel_left]
    have h2 : MulAut.conj (z'⁻¹ * z₀) = 1 := by
      ext y
      rw [MulAut.conj_apply, MulAut.one_apply,
        (Subgroup.mem_center_iff.mp hz'z₀ y).symm, mul_inv_cancel_right]
    rw [hτz₀, h1, h2, mul_one]
  obtain ⟨⟨x₁, hx₁L⟩, hx₁⟩ := QuotientGroup.mk_surjective z'
  have hx₁τ : barAct L ⟨x₁, Subgroup.le_normalizer hx₁L⟩ = τ := by
    rw [barAct_of_mem hx₁L, hτz']
    exact congrArg MulAut.conj hx₁
  obtain ⟨k, a, hka, hkτ⟩ := exists_pow_isPGroup_three (barAct L)
    ⟨x₁, Subgroup.le_normalizer hx₁L⟩ (by rw [hx₁τ]; exact hτ3)
  set x : G := x₁ ^ k with hx
  have hxL : x ∈ L := L.pow_mem hx₁L k
  have hxN : x ∈ N := Subgroup.le_normalizer hxL
  have hxe : ((⟨x₁, Subgroup.le_normalizer hx₁L⟩ : N) ^ k) = ⟨x, hxN⟩ :=
    Subtype.ext (by simp [hx])
  rw [hxe] at hkτ hka
  rw [hx₁τ] at hkτ
  have hxa : x ^ (3 ^ a) = 1 := by
    have := congrArg Subtype.val hka
    simpa using this
  have hP3 : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := a) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hxa
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθ
  set O := inSubgroup (pPrimeCore 2) θ with hO
  have hL1 := commutator_mem_oddCore hS h
  have hNθ := normalizer_le_normalizer_theta L
  have hθN : θ ≤ Subgroup.normalizer (θ : Set G) := Subgroup.le_normalizer
  have hθO : θ ≤ Subgroup.normalizer (O : Set G) := fun t ht =>
    Commute33Steps.normalizer_le_normalizer_oddCore θ (hθN ht)
  have hNO : N ≤ Subgroup.normalizer (O : Set G) :=
    hNθ.trans (Commute33Steps.normalizer_le_normalizer_oddCore θ)
  have hOθ : O ≤ θ := Subgroup.map_subtype_le _
  have hθL : θ ≤ L := Subgroup.map_subtype_le _
  have hθ3 : ¬ 3 ∣ Nat.card θ := by
    rw [hθ, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore L
  have hO3 : ¬ 3 ∣ Nat.card O := fun h3 => hθ3 (h3.trans (Subgroup.card_dvd_of_le hOθ))
  have hPL : Subgroup.zpowers x ≤ L := Subgroup.zpowers_le.mpr hxL
  have hPθ : Subgroup.zpowers x ≤ Subgroup.normalizer (θ : Set G) :=
    fun g hg => hNθ (Subgroup.le_normalizer (hPL hg))
  have hPO : Subgroup.zpowers x ≤ Subgroup.normalizer (O : Set G) :=
    fun g hg => hNO (Subgroup.le_normalizer (hPL hg))
  have hUθ : U ≤ Subgroup.normalizer (θ : Set G) := h.UN.trans hNθ
  have hfixn : ∀ n : ℤ, ∀ u ∈ U, (x ^ n)⁻¹ * (u * x ^ n * u⁻¹) ∈ θ := by
    intro n u hu
    have hxnL : x ^ n ∈ L := L.zpow_mem hxL n
    have hbar : ((⟨x ^ n, hxnL⟩ : L) : lBar L) = z' ^ (k * n : ℤ) := by
      rw [← hx₁, ← QuotientGroup.mk_zpow]
      congr 1
      apply Subtype.ext
      simp [hx, zpow_mul]
    have h1 := hz'fix ⟨u, hu⟩
    have h2 : barAct L ⟨u, h.UN hu⟩ (((⟨x ^ n, hxnL⟩ : L) : lBar L)) =
        ((⟨x ^ n, hxnL⟩ : L) : lBar L) := by
      rw [hbar, map_zpow]
      rw [hφu] at h1
      rw [h1]
    rw [barAct_mk, eq_comm, QuotientGroup.eq] at h2
    exact ⟨_, h2, rfl⟩
  have hgu : ∀ g ∈ Subgroup.zpowers x, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ θ := by
    rintro g ⟨n, rfl⟩ u hu
    have h1 := hfixn (-n) u hu
    have e : (x ^ (-n))⁻¹ * (u * x ^ (-n) * u⁻¹) = x ^ n * u * (x ^ n)⁻¹ * u⁻¹ := by
      rw [zpow_neg, inv_inv]
      group
    rw [e] at h1
    exact h1
  have hA : ∀ u ∈ U, ∃ t ∈ θ, u * x * u⁻¹ = t * x * t⁻¹ := by
    intro u hu
    set J := θ ⊔ U with hJ
    have hJθ : J ≤ Subgroup.normalizer (θ : Set G) := sup_le hθN hUθ
    have hPJ : Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set G) := by
      intro g hg
      refine mem_normalizer_sup_of' (fun t ht => Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (hPθ hg) t).mp ht)) (fun v hv => ?_)
      have e : g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hgu g hg v hv)) (Subgroup.mem_sup_right hv)
    obtain ⟨w, -, hwu, hwx⟩ := exists_fixed_conj_of_coprime hP3 hPJ le_sup_left hJθ hPθ hθ3
      (Subgroup.mem_sup_right hu) fun g hg => by
        have h1 := hgu g hg u hu
        have h2 := (Subgroup.mem_normalizer_iff.mp (hUθ (U.inv_mem hu)) _).mp h1
        rw [inv_inv] at h2
        have e : u⁻¹ * (g * u * g⁻¹) = u⁻¹ * (g * u * g⁻¹ * u⁻¹) * u := by group
        rw [e]
        exact h2
    refine ⟨(w * u⁻¹)⁻¹, θ.inv_mem hwu, ?_⟩
    have hxw : x * w * x⁻¹ = w := hwx x (Subgroup.mem_zpowers x)
    have hwx' : w * x * w⁻¹ = x := by
      calc w * x * w⁻¹ = (x * w * x⁻¹) * x * w⁻¹ := by rw [hxw]
        _ = x := by group
    calc u * x * u⁻¹ = (w * u⁻¹)⁻¹ * (w * x * w⁻¹) * (w * u⁻¹) := by group
      _ = (w * u⁻¹)⁻¹ * x * ((w * u⁻¹)⁻¹)⁻¹ := by rw [hwx', inv_inv]
  have hB : ∀ t ∈ θ, ∃ o ∈ O, t * x * t⁻¹ = o * x * o⁻¹ := by
    intro t ht
    obtain ⟨s, -, hst, hsx⟩ := exists_fixed_conj_of_coprime hP3 hPθ hOθ hθO hPO hO3 ht
      fun g hg => by
        have h1 := hL1 g (hPL hg) t ht
        have h2 := (Subgroup.mem_normalizer_iff.mp (hθO (θ.inv_mem ht)) _).mp h1
        rw [inv_inv] at h2
        have e : t⁻¹ * (g * t * g⁻¹) = t⁻¹ * (g * t * g⁻¹ * t⁻¹) * t := by group
        rw [e]
        exact h2
    refine ⟨(s * t⁻¹)⁻¹, O.inv_mem hst, ?_⟩
    have hxs : x * s * x⁻¹ = s := hsx x (Subgroup.mem_zpowers x)
    have hsx' : s * x * s⁻¹ = x := by
      calc s * x * s⁻¹ = (x * s * x⁻¹) * x * s⁻¹ := by rw [hxs]
        _ = x := by group
    calc t * x * t⁻¹ = (s * t⁻¹)⁻¹ * (s * x * s⁻¹) * (s * t⁻¹) := by group
      _ = (s * t⁻¹)⁻¹ * x * ((s * t⁻¹)⁻¹)⁻¹ := by rw [hsx', inv_inv]
  have hC : ∀ u ∈ U, ∃ o ∈ O, u * x * u⁻¹ = o * x * o⁻¹ := by
    intro u hu
    obtain ⟨t, ht, e1⟩ := hA u hu
    obtain ⟨o, ho, e2⟩ := hB t ht
    exact ⟨o, ho, e1.trans e2⟩
  set O' := O.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom with hO'
  set Ω := MulAction.orbit O' x with hΩ
  have hmemΩ : ∀ y : G, y ∈ Ω ↔ ∃ o ∈ O, y = o * x * o⁻¹ := by
    intro y
    constructor
    · rintro ⟨⟨g, o, ho, rfl⟩, rfl⟩
      refine ⟨o, ho, ?_⟩
      show (ConjAct.toConjAct o : ConjAct G) • x = o * x * o⁻¹
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    · rintro ⟨o, ho, rfl⟩
      refine ⟨⟨ConjAct.toConjAct o, o, ho, rfl⟩, ?_⟩
      show (ConjAct.toConjAct o : ConjAct G) • x = o * x * o⁻¹
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  have hUΩ : ∀ u ∈ U, ∀ y ∈ Ω, u * y * u⁻¹ ∈ Ω := by
    intro u hu y hy
    obtain ⟨o, ho, rfl⟩ := (hmemΩ y).mp hy
    obtain ⟨o', ho', e⟩ := hC u hu
    have hou : u * o * u⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hNO (h.UN hu)) o).mp ho
    refine (hmemΩ _).mpr ⟨u * o * u⁻¹ * o', O.mul_mem hou ho', ?_⟩
    calc u * (o * x * o⁻¹) * u⁻¹ = (u * o * u⁻¹) * (u * x * u⁻¹) * (u * o * u⁻¹)⁻¹ := by group
      _ = (u * o * u⁻¹ * o') * x * (u * o * u⁻¹ * o')⁻¹ := by rw [e]; group
  have hΩodd : Odd (Nat.card Ω) := by
    have h1 : Nat.card Ω * Nat.card (MulAction.stabilizer O' x) = Nat.card O' := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup O' x)
    have h2 : Nat.card O' = Nat.card O :=
      Subgroup.card_map_of_injective (ConjAct.toConjAct : G ≃* ConjAct G).injective
    have hOodd : Odd (Nat.card O) := Commute33Steps.odd_card_inSubgroup_pPrimeCore θ
    rw [← h2, ← h1] at hOodd
    exact Nat.Odd.of_mul_left hOodd
  set U' := U.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom with hU'
  have hU'2 : IsPGroup 2 U' := h.U2.map _
  let S : SubMulAction U' G :=
    { carrier := Ω
      smul_mem' := by
        rintro ⟨g, u, hu, rfl⟩ y hy
        rw [Subgroup.smul_def, ConjAct.smul_def]
        exact hUΩ u hu y hy }
  have hScard : Nat.card S = Nat.card Ω := rfl
  have hmod := hU'2.card_modEq_card_fixedPoints S
  have hne : (MulAction.fixedPoints U' S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints U' S) = 0 := by
      rw [hemp]
      simp
    rw [h0, hScard] at hmod
    exact (Nat.not_even_iff_odd.mpr hΩodd) (Nat.even_iff.mpr hmod)
  obtain ⟨⟨y, hy⟩, hfix⟩ := hne
  obtain ⟨o, ho, rfl⟩ := (hmemΩ y).mp hy
  have hoθ : o ∈ θ := hOθ ho
  have hoL : o ∈ L := hθL hoθ
  have hyL : o * x * o⁻¹ ∈ L := L.mul_mem (L.mul_mem hoL hxL) (L.inv_mem hoL)
  have hyC : o * x * o⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := congrArg Subtype.val (hfix ⟨ConjAct.toConjAct u, u, hu, rfl⟩)
    change ConjAct.toConjAct u • (o * x * o⁻¹) = o * x * o⁻¹ at h1
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h1
    calc u * (o * x * o⁻¹) = u * (o * x * o⁻¹) * u⁻¹ * u := by group
      _ = o * x * o⁻¹ * u := by rw [h1]
  refine mem_barImage_iff.mpr ⟨o * x * o⁻¹, Subgroup.le_normalizer hyL, ⟨hyL, hyC⟩, ?_⟩
  have ho1 : barAct L ⟨o, Subgroup.le_normalizer hoL⟩ = 1 :=
    barAct_eq_one_of_mem _ (theta_le_thetaQuotCentralizer L hoθ)
  have e : (⟨o * x * o⁻¹, Subgroup.le_normalizer hyL⟩ : N) =
      ⟨o, Subgroup.le_normalizer hoL⟩ * ⟨x, hxN⟩ * (⟨o, Subgroup.le_normalizer hoL⟩ : N)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, ho1, one_mul, inv_one, mul_one, hkτ]

end Lift

theorem star (hS : A ∈ partTwoS G) (h : PairFacts A E U c L)
    (hZodd : Odd (Nat.card (Subgroup.center (lBar L)))) :
    ∃ R : Subgroup (MulAut (lBar L)), IsPGroup 2 R ∧ barImage L (lThreeV E U c) ≤ R ∧
      (∀ r ∈ R, ∀ u ∈ barImage L U, r * u = u * r) ∧
      barImage L E ≤ Subgroup.normalizer (R : Set (MulAut (lBar L))) ∧
      ∀ τ ∈ barImage L L, (∀ u ∈ barImage L U, τ * u = u * τ) → τ ^ 3 = 1 →
        τ ∈ Subgroup.normalizer (R : Set (MulAut (lBar L))) := by
  have hV := vFacts h
  set M := Subgroup.centralizer ((U : Set G) ∪ {c}) with hM
  set X0 := inSubgroup (CFSG.pCore 2) M with hX0
  have hX02 : IsPGroup 2 X0 := (CFSG.pCore_isPGroup).map M.subtype
  have hX0M : X0 ≤ M := Subgroup.map_subtype_le _
  have hNX0 : Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (X0 : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 M
  refine ⟨barImage L X0, isPGroup_barImage hX02,
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV.le_X0 (Subgroup.mem_subgroupOf.mp hx)), ?_, ?_, ?_⟩
  · refine barImage_commute fun x hx u hu => ?_
    have := Subgroup.mem_centralizer_iff.mp (hX0M hx) u (Or.inl hu)
    exact this.symm
  · refine barImage_E_le_normalizer fun e he x hx => ?_
    have heM : e ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.mem_normalizer_fintype fun y hy => hV.E_conj_C e he y hy
    exact (Subgroup.mem_normalizer_iff.mp (hNX0 heM) x).mp hx
  · intro τ hτL hτU hτ3
    obtain ⟨y, hyN, ⟨hyL, hyU⟩, rfl⟩ :=
      mem_barImage_iff.mp (exists_lift_centralizer hS h hZodd hτL hτU hτ3)
    have hyM : y ∈ M := by
      rw [hM, Subgroup.mem_centralizer_iff]
      rintro z (hz | hz)
      · exact Subgroup.mem_centralizer_iff.mp hyU z hz
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (h.L_le_centralizer hyL)).symm
    have hyX : ∀ x ∈ X0, y * x * y⁻¹ ∈ X0 := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hNX0 (Subgroup.le_normalizer hyM)) x).mp hx
    exact Subgroup.mem_normalizer_fintype (barImage_conj_mem hyN hyX)

omit [Finite G] in
theorem le_inSubgroup_pCore {M : Type*} [Group M] {p : ℕ} {K W : Subgroup M} (hWK : W ≤ K)
    (hW : IsPGroup p W) (hKW : K ≤ Subgroup.normalizer (W : Set M)) :
    W ≤ inSubgroup (CFSG.pCore p) K := by
  intro w hw
  refine ⟨⟨w, hWK hw⟩, ?_, rfl⟩
  have hn : (W.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWK).mpr hKW
  have hp : IsPGroup p (W.subgroupOf K) :=
    hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  exact (le_sSup (show W.subgroupOf K ∈ {N : Subgroup K | N.Normal ∧ IsPGroup p N} from
    ⟨hn, hp⟩) : W.subgroupOf K ≤ CFSG.pCore p K) (Subgroup.mem_subgroupOf.mpr hw)

theorem inSubgroup_pCore_le_of_normal {M : Type*} [Group M] [Finite M] {p : ℕ} {K H : Subgroup M}
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set M)) :
    inSubgroup (CFSG.pCore p) K ≤ inSubgroup (CFSG.pCore p) H :=
  le_inSubgroup_pCore ((Subgroup.map_subtype_le _).trans hKH) ((CFSG.pCore_isPGroup).map _)
    (hHK.trans (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore
      p K))

theorem starO2 (hS : A ∈ partTwoS G) (h : PairFacts A E U c L)
    (hZodd : Odd (Nat.card (Subgroup.center (lBar L))))
    (hBi : barImage L (E ⊓ Subgroup.centralizer (U : Set G)) ≤
      (MulAut.conj : lBar L →* MulAut (lBar L)).range)
    (hVi : barImage L (lThreeV E U c) ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range) :
    barImage L (lThreeV E U c) ≤ inSubgroup (CFSG.pCore 2)
      ((MulAut.conj : lBar L →* MulAut (lBar L)).range ⊓
        Subgroup.centralizer (barImage L U : Set (MulAut (lBar L)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Inn := (MulAut.conj : lBar L →* MulAut (lBar L)).range with hInn
  set H := Inn ⊓ Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))) with hH
  set B := E ⊓ Subgroup.centralizer (U : Set G) with hB
  set V := lThreeV E U c with hV
  set H₃ := Subgroup.closure {τ | τ ∈ H ∧ τ ^ 3 = 1} with hH₃
  obtain ⟨R, hR2, hVR, -, -, hRτ⟩ := star hS h hZodd
  have hInnL : Inn ≤ barImage L L := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    exact mem_barImage_iff.mpr ⟨l, Subgroup.le_normalizer l.2, l.2, barAct_of_mem l.2⟩
  have hH₃H : H₃ ≤ H := (Subgroup.closure_le _).mpr fun τ hτ => hτ.1
  have hHH₃ : H ≤ Subgroup.normalizer (H₃ : Set (MulAut (lBar L))) := by
    intro g hg
    have hle : H₃ ≤ H₃.comap (MulAut.conj g).toMonoidHom := by
      rw [hH₃, Subgroup.closure_le]
      rintro τ ⟨hτH, hτ3⟩
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hg hτH) (H.inv_mem hg), ?_⟩
      change (g * τ * g⁻¹) ^ 3 = 1
      rw [conj_pow, hτ3, mul_one, mul_inv_cancel]
    exact Subgroup.mem_normalizer_fintype fun x hx => hle hx
  have hH₃R : H₃ ≤ Subgroup.normalizer (R : Set (MulAut (lBar L))) := by
    rw [hH₃, Subgroup.closure_le]
    rintro τ ⟨hτH, hτ3⟩
    exact hRτ τ (hInnL (Subgroup.mem_inf.mp hτH).1) (fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hτH).2 u hu).symm) hτ3
  have hVH₃ : barImage L V ≤ H₃ := by
    rw [← barImage_V_comm_B h, Subgroup.commutator_le]
    intro v hv b hb
    have hb3 : b ^ 3 = 1 := (isElemAbelian_barImage_E h).2 b (barImage_B_le_E hb)
    have hbH : b ∈ H := Subgroup.mem_inf.mpr ⟨hBi hb, Subgroup.mem_centralizer_iff.mpr
      fun u hu => barImage_U_comm_B u hu b hb⟩
    have hvH : v ∈ H := Subgroup.mem_inf.mpr ⟨hVi hv, Subgroup.mem_centralizer_iff.mpr
      fun u hu => barImage_U_comm_V h u hu v hv⟩
    rw [commutatorElement_def]
    refine H₃.mul_mem (Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hvH hbH) (H.inv_mem hvH),
      ?_⟩) (H₃.inv_mem (Subgroup.subset_closure ⟨hbH, hb3⟩))
    rw [conj_pow, hb3, mul_one, mul_inv_cancel]
  have hW : R ⊓ H₃ ≤ inSubgroup (CFSG.pCore 2) H₃ := by
    refine le_inSubgroup_pCore inf_le_right (hR2.to_le inf_le_left) fun g hg =>
      Subgroup.mem_normalizer_fintype fun x hx => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hH₃R hg) x).mp (Subgroup.mem_inf.mp hx).1
    · exact H₃.mul_mem (H₃.mul_mem hg (Subgroup.mem_inf.mp hx).2) (H₃.inv_mem hg)
  exact fun v hv => inSubgroup_pCore_le_of_normal hH₃H hHH₃ (hW ⟨hVR hv, hVH₃ hv⟩)

end Item211LieProof

end CFSG.RankThree.PartTwo.Sec21
