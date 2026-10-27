module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5R2Calc
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5R2Quot
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.Quasithin.H13.R2

open CFSG.Open
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem commute_of_mem_center {z : P} (hz : z ∈ Subgroup.center P) (g : P) : Commute z g :=
  (Subgroup.mem_center_iff.mp hz g).symm

@[expose] def omegaCenter (P : Type) [Group P] : Subgroup P where
  carrier := {z | z ∈ Subgroup.center P ∧ z ^ 3 = 1}
  mul_mem' := by
    rintro z w ⟨hz, hz3⟩ ⟨hw, hw3⟩
    exact ⟨Subgroup.mul_mem _ hz hw, by rw [(commute_of_mem_center hz w).mul_pow, hz3, hw3,
      one_mul]⟩
  one_mem' := ⟨Subgroup.one_mem _, one_pow 3⟩
  inv_mem' := by
    rintro z ⟨hz, hz3⟩
    exact ⟨Subgroup.inv_mem _ hz, by rw [inv_pow, hz3, inv_one]⟩

omit [Finite P] in
theorem omegaCenter_central {z : P} (hz : z ∈ omegaCenter P) (g : P) : z * g = g * z :=
  (commute_of_mem_center hz.1 g).eq

omit [Finite P] in
theorem omegaCenter_isElemAbelian : IsElemAbelian 3 (omegaCenter P) :=
  ⟨⟨⟨fun z w => Subtype.ext (omegaCenter_central z.2 w)⟩⟩, fun _ hz => hz.2⟩

omit [Finite P] in
theorem mem_center_of_mulAut (φ : MulAut P) {z : P} (hz : z ∈ Subgroup.center P) :
    φ z ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := Subgroup.mem_center_iff.mp hz (φ.symm g)
  have e := congrArg φ this
  simpa using e

omit [Finite P] in
theorem mem_omegaCenter_of_mulAut (φ : MulAut P) {z : P} (hz : z ∈ omegaCenter P) :
    φ z ∈ omegaCenter P :=
  ⟨mem_center_of_mulAut φ hz.1, by rw [← map_pow, hz.2, map_one]⟩

omit [Finite P] in
theorem isElemAbelian_sup_zpowers {E : Subgroup P} (hE : IsElemAbelian 3 E) {g : P}
    (hg : g ^ 3 = 1) (hgE : ∀ e ∈ E, g * e = e * g) :
    IsElemAbelian 3 (E ⊔ Subgroup.zpowers g) := by
  have hN : Subgroup.zpowers g ≤ Subgroup.normalizer (E : Set P) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun e => ⟨fun he => ?_, fun he => ?_⟩
    · have e1 : g * e * g⁻¹ = e := by rw [hgE e he, mul_inv_cancel_right]
      rw [e1]
      exact he
    · have h1 := hgE _ he
      have e1 : g * e * g⁻¹ = e := by
        calc g * e * g⁻¹ = g⁻¹ * (g * (g * e * g⁻¹)) := by group
          _ = g⁻¹ * ((g * e * g⁻¹) * g) := by rw [h1]
          _ = e := by group
      rw [e1] at he
      exact he
  have hmem : ∀ z ∈ E ⊔ Subgroup.zpowers g, ∃ e ∈ E, ∃ k : ℤ, z = e * g ^ k := by
    intro z hz
    have hz' : z ∈ ((E ⊔ Subgroup.zpowers g : Subgroup P) : Set P) := hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left E _ hN] at hz'
    obtain ⟨e, he, w, hw, rfl⟩ := Set.mem_mul.mp hz'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨e, he, k, rfl⟩
  have hcEg : ∀ e ∈ E, ∀ k : ℤ, Commute e (g ^ k) := fun e he k =>
    (Commute.zpow_left (hgE e he) k).symm
  have hcE : ∀ e ∈ E, ∀ e' ∈ E, Commute e e' := fun e he e' he' =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
  refine ⟨⟨⟨fun z w => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨e, he, k, hzk⟩ := hmem z z.2
    obtain ⟨e', he', l, hwl⟩ := hmem w w.2
    show (z : P) * w = w * z
    rw [hzk, hwl]
    exact (((hcE e he e' he').mul_right (hcEg e he l)).mul_left
      (((hcEg e' he' k).symm).mul_right (Commute.zpow_zpow_self g k l))).eq
  · obtain ⟨e, he, k, rfl⟩ := hmem z hz
    rw [(hcEg e he k).mul_pow, hE.2 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm k,
      zpow_mul, zpow_natCast, hg, one_zpow]

omit [Finite P] in
theorem lt_sup_zpowers {E : Subgroup P} {g : P} (hg : g ∉ E) : E < E ⊔ Subgroup.zpowers g := by
  refine lt_of_le_of_ne le_sup_left fun he => hg ?_
  have : g ∈ E ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  rwa [← he] at this

theorem mem_of_commute_of_card_nine {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    {E : Subgroup P} (hE : IsElemAbelian 3 E) (h9 : Nat.card E = 9) {g : P} (hg : g ^ 3 = 1)
    (hgE : ∀ e ∈ E, g * e = e * g) : g ∈ E := by
  by_contra hgE'
  have h1 := h.m3 _ (isElemAbelian_sup_zpowers hE hg hgE)
  have h2 := Subgroup.card_lt_of_lt (lt_sup_zpowers hgE')
  omega

theorem mem_omegaCenter_of_pow_three {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h9 : Nat.card (omegaCenter P) = 9) {g : P} (hg : g ^ 3 = 1) : g ∈ omegaCenter P :=
  mem_of_commute_of_card_nine h omegaCenter_isElemAbelian h9 hg
    fun _ hz => (omegaCenter_central hz g).symm

omit [Finite P] in
instance omegaCenter_normal : (omegaCenter P).Normal :=
  ⟨fun z hz g => by
    have : g * z * g⁻¹ = z := by rw [← omegaCenter_central hz g, mul_inv_cancel_right]
    rw [this]
    exact hz⟩

omit [Finite P] in
theorem omegaCenter_map (φ : MulAut P) :
    (omegaCenter P).map (φ : P →* P) = omegaCenter P := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr fun z hz =>
    mem_omegaCenter_of_mulAut φ hz) fun z hz => ⟨φ.symm z, mem_omegaCenter_of_mulAut φ.symm hz, ?_⟩
  simp

omit [Finite P] in
@[expose] noncomputable def qAut (φ : MulAut P) : MulAut (P ⧸ omegaCenter P) :=
  QuotientGroup.congr (omegaCenter P) (omegaCenter P) φ (omegaCenter_map φ)

omit [Finite P] in
theorem qAut_mk (φ : MulAut P) (g : P) :
    qAut φ (g : P ⧸ omegaCenter P) = ((φ g : P) : P ⧸ omegaCenter P) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem frattini_quot_eq {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    {Z : Subgroup P} [Z.Normal] :
    frattini (P ⧸ Z) = (frattini P).map (QuotientGroup.mk' Z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨h.p3⟩
  refine le_antisymm ?_ (Subgroup.map_le_iff_le_comap.mpr
    (frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective Z)))
  have hN : ((frattini P).map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  refine CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary (p := 3) _ ?_ ?_
  · intro q q'
    induction q using QuotientGroup.induction_on with
    | H q =>
    induction q' using QuotientGroup.induction_on with
    | H q' =>
    induction q using QuotientGroup.induction_on with
    | H g =>
    induction q' using QuotientGroup.induction_on with
    | H g' =>
    have hc : ⁅g, g'⁆ ∈ frattini P := CFSG.commutator_le_frattini_of_isPGroup (p := 3)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top g'))
    have h1 : QuotientGroup.mk' ((frattini P).map (QuotientGroup.mk' Z))
        (QuotientGroup.mk' Z ⁅g, g'⁆) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨_, hc, rfl⟩
    rw [map_commutatorElement, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · intro q
    induction q using QuotientGroup.induction_on with
    | H q =>
    induction q using QuotientGroup.induction_on with
    | H g =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨g ^ 3, CFSG.pth_power_mem_frattini_of_isPGroup g, rfl⟩

theorem quot_m3 {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h9 : Nat.card (omegaCenter P) = 9) (E : Subgroup (P ⧸ omegaCenter P))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  classical
  set Z := omegaCenter P with hZ
  set π := QuotientGroup.mk' Z with hπ
  set F := E.comap π with hF
  have hcomm : ∀ f ∈ F, ∀ f' ∈ F, ⁅f', f⁆ ∈ Z := by
    intro f hf f' hf'
    have e1 : π ⁅f', f⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hf'⟩ ⟨_, hf⟩)
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at e1
  have hcube : ∀ f ∈ F, f ^ 3 ∈ Z := by
    intro f hf
    have e1 : π (f ^ 3) = 1 := by rw [map_pow]; exact hE.2 _ hf
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at e1
  let θ : ↥F →* ↥Z :=
    { toFun := fun f => ⟨(f : P) ^ 3, hcube f f.2⟩
      map_one' := by simp
      map_mul' := fun f f' => Subtype.ext (by
        have hc := hcomm f f.2 f' f'.2
        show ((f : P) * f') ^ 3 = (f : P) ^ 3 * (f' : P) ^ 3
        exact mul_pow_three_of_central (omegaCenter_central hc) hc.2) }
  have hker : Nat.card θ.ker ≤ 9 := by
    rw [← h9]
    refine Nat.card_le_card_of_injective (fun f => (⟨(f : F), ?_⟩ : ↥Z)) fun f f' e => ?_
    · have hf : ((f : F) : P) ^ 3 = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp f.2)
        simpa [θ] using this
      exact mem_omegaCenter_of_pow_three h h9 hf
    · exact Subtype.ext (Subtype.ext (congrArg Subtype.val e :))
  have hrange : Nat.card θ.range ≤ 9 := by
    rw [← h9]
    exact Subgroup.card_le_card_group _
  have hFcard : Nat.card F ≤ 81 := by
    rw [← Subgroup.card_mul_index θ.ker, Subgroup.index_ker]
    calc Nat.card θ.ker * Nat.card θ.range ≤ 9 * 9 := Nat.mul_le_mul hker hrange
      _ = 81 := by norm_num
  let ψ : ↥F →* P ⧸ Z := π.comp F.subtype
  have hψr : ψ.range = E := by
    ext q
    constructor
    · rintro ⟨f, rfl⟩
      exact f.2
    · intro hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z q
      exact ⟨⟨g, hq⟩, rfl⟩
  have hψk : Nat.card ψ.ker = 9 := by
    rw [← h9]
    refine Nat.card_congr ⟨fun f => ⟨(f : F), ?_⟩, fun z => ⟨⟨z, ?_⟩, ?_⟩, ?_, ?_⟩
    · have := MonoidHom.mem_ker.mp f.2
      simpa [ψ, hπ, QuotientGroup.eq_one_iff] using this
    · show π z ∈ E
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr z.2]
      exact E.one_mem
    · rw [MonoidHom.mem_ker]
      show π z = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact z.2
    · intro f; rfl
    · intro z; rfl
  have hFE : Nat.card F = 9 * Nat.card E := by
    rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker, hψk, hψr]
  omega

theorem center_le_frattini {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (hnc : ∃ g k : P, g * k ≠ k * g) : Subgroup.center P ≤ frattini P := by
  rcases le_frattini_or_eq_top h (fun g hg => mem_center_of_mulAut a hg)
    (fun g hg => mem_center_of_mulAut s hg) with hle | htop
  · exact hle
  · obtain ⟨g, k, hgk⟩ := hnc
    have hk : k ∈ Subgroup.center P := by rw [htop]; exact Subgroup.mem_top k
    exact absurd (Subgroup.mem_center_iff.mp hk g) hgk

theorem hyp_quot {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h9 : Nat.card (omegaCenter P) = 9) (hZ : omegaCenter P ≤ frattini P) :
    Hyp (P ⧸ omegaCenter P) (x : P ⧸ omegaCenter P) (y : P ⧸ omegaCenter P) (qAut a)
      (qAut s) where
  p3 := h.p3.to_quotient _
  index := by
    rw [frattini_quot_eq h (Z := omegaCenter P), Subgroup.index_map_eq _
      (QuotientGroup.mk'_surjective (omegaCenter P))
      (by rw [QuotientGroup.ker_mk']; exact hZ), h.index]
  m3 := quot_m3 h h9
  gen := by
    have := congrArg (Subgroup.map (QuotientGroup.mk' (omegaCenter P))) h.gen
    rw [MonoidHom.map_closure, Set.image_pair,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
    exact this
  ax := by
    rw [frattini_quot_eq h (Z := omegaCenter P), qAut_mk, ← QuotientGroup.mk_mul]
    exact ⟨_, h.ax, rfl⟩
  ay := by
    rw [frattini_quot_eq h (Z := omegaCenter P), qAut_mk, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    exact ⟨_, h.ay, rfl⟩
  sx := by
    rw [frattini_quot_eq h (Z := omegaCenter P), qAut_mk, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    exact ⟨_, h.sx, rfl⟩
  sy := by
    rw [frattini_quot_eq h (Z := omegaCenter P), qAut_mk, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    exact ⟨_, h.sy, rfl⟩

end CFSG.Quasithin.H13.R2
