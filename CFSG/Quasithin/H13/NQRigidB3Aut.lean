module

public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.SteinbergBTResidualAbelianIndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_map_congr
  center_map_equiv)
open scoped commutatorElement Pointwise

section Aut0

noncomputable abbrev aut0 (J : Type*) [Group J] : Subgroup (MulAut J) :=
  CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived J

instance aut0_normal (J : Type*) [Group J] : (aut0 J).Normal :=
  CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_normal J

theorem commutator_le_aut0 (J : Type*) [Group J] : commutator (MulAut J) ≤ aut0 J :=
  CFSG.ComponentClassification.OuterAutomorphisms.commutator_le_innAutDerived J

theorem mk_mem_commutator_of_mem_aut0 {J : Type*} [Group J] {θ : MulAut J} (hθ : θ ∈ aut0 J) :
    QuotientGroup.mk' (inner J) θ ∈ commutator (Outer J) := by
  have hle : aut0 J ≤ (commutator (Outer J)).comap (QuotientGroup.mk' (inner J)) := by
    refine sup_le (fun a ha => ?_) ?_
    · rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff a).mpr ha]
      exact one_mem _
    · rw [← map_le_iff_le_comap, commutator_def, commutator_def, map_commutator]
      exact commutator_mono le_top le_top
  exact hle hθ

theorem mem_aut0_congr {J J' : Type*} [Group J] [Group J'] (φ : J ≃* J') {θ : MulAut J}
    (hθ : θ ∈ aut0 J) : MulAut.congr φ θ ∈ aut0 J' :=
  (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr φ).2 hθ

theorem card_commutator_outer_congr {J J' : Type*} [Group J] [Group J'] (φ : J ≃* J') :
    Nat.card (commutator (Outer J')) = Nat.card (commutator (Outer J)) := by
  set ψ := CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ with hψ
  have h : (commutator (Outer J)).map ψ.toMonoidHom = commutator (Outer J') := by
    rw [commutator_def, commutator_def, map_commutator,
      map_top_of_surjective ψ.toMonoidHom ψ.surjective]
  rw [← h, card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]

theorem card_center_congr {J J' : Type*} [Group J] [Group J'] (φ : J ≃* J') :
    Nat.card (center J') = Nat.card (center J) := by
  rw [← center_map_equiv φ, card_map_of_injective (f := φ.toMonoidHom) φ.injective]

end Aut0

section Pre

variable {E : Type*} [Group E]

@[expose] noncomputable def aut0Pre (J : Subgroup E) : Subgroup E :=
  ((aut0 J).comap J.normalizerMonoidHom).map (normalizer (J : Set E)).subtype

theorem mem_aut0Pre {J : Subgroup E} {y : E} :
    y ∈ aut0Pre J ↔
      ∃ hy : y ∈ normalizer (J : Set E), J.normalizerMonoidHom ⟨y, hy⟩ ∈ aut0 J := by
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩
    exact ⟨hz, h⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

theorem aut0Pre_le (J : Subgroup E) : aut0Pre J ≤ normalizer (J : Set E) :=
  map_subtype_le _

theorem commutatorElement_mem_aut0Pre {J : Subgroup E} {y z : E}
    (hy : y ∈ normalizer (J : Set E)) (hz : z ∈ normalizer (J : Set E)) :
    ⁅y, z⁆ ∈ aut0Pre J := by
  refine mem_map.mpr ⟨⁅(⟨y, hy⟩ : normalizer (J : Set E)), ⟨z, hz⟩⁆, ?_, rfl⟩
  rw [mem_comap, map_commutatorElement]
  exact commutator_le_aut0 J (commutator_mem_commutator (mem_top _) (mem_top _))

theorem conj_mem_aut0Pre {J : Subgroup E} {g y : E} (hg : g ∈ normalizer (J : Set E))
    (hy : y ∈ aut0Pre J) : g * y * g⁻¹ ∈ aut0Pre J := by
  obtain ⟨hyN, hy0⟩ := mem_aut0Pre.mp hy
  refine mem_map.mpr ⟨⟨g, hg⟩ * ⟨y, hyN⟩ * ⟨g, hg⟩⁻¹, ?_, rfl⟩
  rw [mem_comap, map_mul, map_mul, map_inv]
  exact (aut0_normal J).conj_mem _ hy0 _

@[expose] noncomputable def conjEquivOfMap {J J' : Subgroup E} (g : E)
    (hJ' : J.map (MulAut.conj g).toMonoidHom = J') : J ≃* J' :=
  (J.equivMapOfInjective _ (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hJ')

theorem conjEquivOfMap_apply {J J' : Subgroup E} (g : E)
    (hJ' : J.map (MulAut.conj g).toMonoidHom = J') (w : J) :
    ((conjEquivOfMap g hJ' w : J') : E) = g * w * g⁻¹ :=
  rfl

theorem conj_mem_normalizer_of_map {J J' : Subgroup E} {g y : E}
    (hJ' : J.map (MulAut.conj g).toMonoidHom = J') (hy : y ∈ normalizer (J : Set E)) :
    g * y * g⁻¹ ∈ normalizer (J' : Set E) := by
  rw [← hJ', mem_normalizer_iff]
  intro h
  rw [mem_map_equiv, mem_map_equiv, MulAut.conj_symm_apply, MulAut.conj_symm_apply]
  have e : g⁻¹ * (g * y * g⁻¹ * h * (g * y * g⁻¹)⁻¹) * g = y * (g⁻¹ * h * g) * y⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.mp hy _

theorem normalizerMonoidHom_conj {J J' : Subgroup E} (g : E)
    (hJ' : J.map (MulAut.conj g).toMonoidHom = J') {y : E} (hy : y ∈ normalizer (J : Set E)) :
    J'.normalizerMonoidHom ⟨g * y * g⁻¹, conj_mem_normalizer_of_map hJ' hy⟩ =
      MulAut.congr (conjEquivOfMap g hJ') (J.normalizerMonoidHom ⟨y, hy⟩) := by
  ext z
  set w := (conjEquivOfMap g hJ').symm z with hw
  have hz : (z : E) = g * w * g⁻¹ := by
    rw [← conjEquivOfMap_apply g hJ', hw, MulEquiv.apply_symm_apply]
  have h1 : ((MulAut.congr (conjEquivOfMap g hJ') (J.normalizerMonoidHom ⟨y, hy⟩) z : J') : E) =
      g * (y * (w : E) * y⁻¹) * g⁻¹ :=
    rfl
  rw [h1]
  change g * y * g⁻¹ * (z : E) * (g * y * g⁻¹)⁻¹ = _
  rw [hz]
  group

theorem conj_mem_aut0Pre_of_map {J J' : Subgroup E} {g y : E}
    (hJ' : J.map (MulAut.conj g).toMonoidHom = J') (hy : y ∈ aut0Pre J) :
    g * y * g⁻¹ ∈ aut0Pre J' := by
  obtain ⟨hyN, hy0⟩ := mem_aut0Pre.mp hy
  refine mem_aut0Pre.mpr ⟨conj_mem_normalizer_of_map hJ' hyN, ?_⟩
  rw [normalizerMonoidHom_conj g hJ' hyN]
  exact mem_aut0_congr _ hy0

theorem inner_of_mem_aut0Pre [Finite E] {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hXcard : ∃ a b : ℕ, Nat.card X = 2 ^ a * p ^ b) {J : Subgroup E}
    (hOD : ¬ p ∣ Nat.card (commutator (Outer J))) (f : X →* normalizer (J : Set E))
    (hf : ∀ x, (f x : E) ∈ aut0Pre J) (x : X) : J.normalizerMonoidHom (f x) ∈ inner J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : X →* Outer J := (QuotientGroup.mk' (inner J)).comp (J.normalizerMonoidHom.comp f)
    with hψ
  have hψc : ψ.range ≤ commutator (Outer J) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨hyN, hy0⟩ := mem_aut0Pre.mp (hf x)
    exact mk_mem_commutator_of_mem_aut0 hy0
  have h2 : IsPGroup 2 ψ.range := by
    obtain ⟨a, b, hab⟩ := hXcard
    have h1 : Nat.card ψ.range ∣ 2 ^ a * p ^ b := by
      rw [← hab]
      exact card_range_dvd ψ
    have h3 : ¬ p ∣ Nat.card ψ.range := fun h => hOD (h.trans (card_dvd_of_le hψc))
    have h4 : Nat.Coprime (Nat.card ψ.range) (p ^ b) :=
      Nat.Coprime.pow_right b (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr h3))
    have h5 : Nat.card ψ.range ∣ 2 ^ a := h4.dvd_of_dvd_mul_right h1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h5
    exact IsPGroup.of_card hm
  have hker := SteinbergBT.ker_eq_top_of_isPGroup_two_range hX2 ψ h2
  have hx : x ∈ ψ.ker := hker ▸ mem_top x
  have hx' : QuotientGroup.mk' (inner J) (J.normalizerMonoidHom (f x)) = 1 := hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact hx'

end Pre

section Center

variable {E : Type*} [Group E] [Finite E]

omit [Finite E] in
theorem exists_mul_of_mem_sup {J₁ J₂ : Subgroup E} (hc : ⁅J₁, J₂⁆ = ⊥) {z : E}
    (hz : z ∈ J₁ ⊔ J₂) : ∃ j₁ ∈ J₁, ∃ j₂ ∈ J₂, j₁ * j₂ = z := by
  have hle : J₁ ≤ normalizer (J₂ : Set E) :=
    (commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le_normalizer _)
  have hz' : z ∈ ((J₁ ⊔ J₂ : Subgroup E) : Set E) := hz
  rw [coe_mul_of_left_le_normalizer_right J₁ J₂ hle] at hz'
  obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := hz'
  exact ⟨j₁, hj₁, j₂, hj₂, hj⟩

omit [Finite E] in
theorem not_dvd_orderOf_mul {p : ℕ} (hp : p.Prime) {a b : E} (hab : Commute a b)
    (ha : ¬ p ∣ orderOf a) (hb : ¬ p ∣ orderOf b) : ¬ p ∣ orderOf (a * b) := by
  intro h
  have h1 : (a * b) ^ (orderOf a * orderOf b) = 1 := by
    rw [hab.mul_pow, pow_mul, pow_orderOf_eq_one, one_pow, mul_comm, pow_mul, pow_orderOf_eq_one,
      one_pow, one_mul]
  have h2 := h.trans (orderOf_dvd_of_pow_eq_one h1)
  rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
  · exact ha h3
  · exact hb h3

theorem not_dvd_card_center_sup {p : ℕ} (hp : p.Prime) {J₁ J₂ : Subgroup E}
    (hc : ⁅J₁, J₂⁆ = ⊥) (hZ₁ : ¬ p ∣ Nat.card (center J₁)) (hZ₂ : ¬ p ∣ Nat.card (center J₂)) :
    ¬ p ∣ Nat.card (center (J₁ ⊔ J₂ : Subgroup E)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center (J₁ ⊔ J₂ : Subgroup E)) p hdvd
  have hzo : orderOf ((z : ↥(J₁ ⊔ J₂)) : E) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hcomm : ∀ x ∈ J₁, ∀ y ∈ J₂, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc) hx)) y hy |>.symm
  obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := exists_mul_of_mem_sup hc (z : ↥(J₁ ⊔ J₂)).2
  have hzc : ∀ y : ↥(J₁ ⊔ J₂), y * (z : ↥(J₁ ⊔ J₂)) = (z : ↥(J₁ ⊔ J₂)) * y :=
    fun y => (mem_center_iff.mp z.2 y)
  have hj₁Z : (⟨j₁, hj₁⟩ : J₁) ∈ center J₁ := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := congrArg Subtype.val (hzc ⟨y, mem_sup_left y.2⟩)
    simp only [coe_mul] at h1
    rw [← hj] at h1
    change (y : E) * j₁ = j₁ * y
    have h2 : (y : E) * (j₁ * j₂) = j₁ * j₂ * y := h1
    have h3 : j₂ * (y : E) = y * j₂ := (hcomm y y.2 j₂ hj₂).symm
    calc (y : E) * j₁ = (y : E) * (j₁ * j₂) * j₂⁻¹ := by group
      _ = j₁ * j₂ * y * j₂⁻¹ := by rw [h2]
      _ = j₁ * (j₂ * y) * j₂⁻¹ := by group
      _ = j₁ * y := by rw [h3]; group
  have hj₂Z : (⟨j₂, hj₂⟩ : J₂) ∈ center J₂ := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := congrArg Subtype.val (hzc ⟨y, mem_sup_right y.2⟩)
    simp only [coe_mul] at h1
    rw [← hj] at h1
    change (y : E) * j₂ = j₂ * y
    have h2 : (y : E) * (j₁ * j₂) = j₁ * j₂ * y := h1
    have h3 : j₁ * (y : E) = y * j₁ := hcomm j₁ hj₁ y y.2
    calc (y : E) * j₂ = j₁⁻¹ * (j₁ * y) * j₂ := by group
      _ = j₁⁻¹ * (y * j₁) * j₂ := by rw [h3]
      _ = j₁⁻¹ * ((y : E) * (j₁ * j₂)) := by group
      _ = j₁⁻¹ * (j₁ * j₂ * y) := by rw [h2]
      _ = j₂ * y := by group
  have ho₁ : ¬ p ∣ orderOf j₁ := by
    intro h
    apply hZ₁
    have h1 : orderOf (⟨⟨j₁, hj₁⟩, hj₁Z⟩ : center J₁) = orderOf j₁ := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact h.trans (h1 ▸ orderOf_dvd_natCard (⟨⟨j₁, hj₁⟩, hj₁Z⟩ : center J₁))
  have ho₂ : ¬ p ∣ orderOf j₂ := by
    intro h
    apply hZ₂
    have h1 : orderOf (⟨⟨j₂, hj₂⟩, hj₂Z⟩ : center J₂) = orderOf j₂ := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact h.trans (h1 ▸ orderOf_dvd_natCard (⟨⟨j₂, hj₂⟩, hj₂Z⟩ : center J₂))
  have h4 : orderOf (j₁ * j₂) = p := by rw [hj, hzo]
  exact not_dvd_orderOf_mul hp (hcomm j₁ hj₁ j₂ hj₂) ho₁ ho₂ (h4 ▸ dvd_refl p)

end Center

end CFSG.Quasithin.H13.NQRigid
