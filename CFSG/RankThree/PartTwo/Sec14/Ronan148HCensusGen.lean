module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusInner
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open scoped Pointwise

section ThreeX

theorem commutator_mem_center_of_isPGroup {X : Type} [Group X] [Finite X]
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {T : Subgroup X}
    (hTp : IsPGroup 3 T) :
    (∀ a ∈ T, a ^ 3 ∈ Subgroup.center X) ∧
      ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X := by
  obtain ⟨-, ⟨e⟩⟩ := hT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* CFSG.Blueprint.NativeSporadic.ON :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hker : ∀ x, π x = 1 → x ∈ Subgroup.center X := by
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := e.injective (by
      rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hE := isElemAbelian_of_isPGroup_ON (hTp.map π)
  refine ⟨fun a ha => hker _ ?_, fun a ha b hb => hker _ ?_⟩
  · rw [map_pow]
    exact hE.2 (π a) ⟨a, ha, rfl⟩
  · have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨π a, a, ha, rfl⟩ ⟨π b, b, hb, rfl⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    simp only [map_mul, map_inv]
    rw [h]
    group

theorem olRow_of_three_noncentral (S : Type) [Group S]
    (h : ∃ T : Subgroup S, IsPGroup 3 T ∧ ((∃ a ∈ T, a ^ 3 ∉ Subgroup.center S) ∨
      ∃ a ∈ T, ∃ b ∈ T, a * b * a⁻¹ * b⁻¹ ∉ Subgroup.center S)) :
    OLRow (fun T _ => Nonempty (T ≃* S)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  obtain ⟨T, hT, hab⟩ := h
  set f : S →* X := L.subtype.comp e.symm.toMonoidHom with hf
  have hinj : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hZ : ∀ s : S, f s ∈ Subgroup.center X → s ∈ Subgroup.center S := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hs) (f g)
  obtain ⟨h3, hc⟩ := commutator_mem_center_of_isPGroup hcfg.triple (hT.map f)
  rcases hab with ⟨a, ha, ha3⟩ | ⟨a, ha, b, hb, hab⟩
  · exact ha3 (hZ _ (by rw [map_pow]; exact h3 _ ⟨a, ha, rfl⟩))
  · exact hab (hZ _ (by
      simp only [map_mul, map_inv]
      exact hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩))

end ThreeX

section TwoRank

theorem olRow_of_E16_ext (S : Type) [Group S]
    (hE : ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16) :
    OLRow (fun T _ => Sec4.IsExtOf T S (Multiplicative (ZMod 3))) := by
  intro X _ _ P L Q hcfg ⟨K, hKn, ⟨eK⟩, ⟨eS⟩⟩
  obtain ⟨E, hE, hE16⟩ := hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  let ψ : ↥L →* S := eS.toMonoidHom.comp (QuotientGroup.mk' K)
  have hψs : Function.Surjective ψ := eS.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : ∀ l : L, ψ l = 1 → l ∈ K := by
    intro l hl
    have h1 : (QuotientGroup.mk' K) l = 1 := eS.injective (by rw [map_one]; exact hl)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have : Finite S := Finite.of_surjective ψ hψs
  let W := E.comap ψ
  have hWcard : Nat.card W = 48 := by
    have h1 := Subgroup.card_mul_index W
    have h2 := Subgroup.card_mul_index E
    have h3 : W.index = E.index := Subgroup.index_comap_of_surjective E hψs
    have h4 : Nat.card L = Nat.card S * 3 := by
      rw [← hK3, ← Nat.card_congr eS.toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [h4, ← h2, hE16, h3] at h1
    have hpos : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)
  obtain ⟨T2⟩ : Nonempty (Sylow 2 W) := inferInstance
  have hT2card : Nat.card T2 = 16 := by
    rw [Sylow.card_eq_multiplicity, hWcard]
    have : (48 : ℕ).factorization 2 = 4 := by
      rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this]
    norm_num
  let g : ↥(T2 : Subgroup W) →* S := ψ.comp (W.subtype.comp (T2 : Subgroup W).subtype)
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : ((x : W) : L) ∈ K := hker _ hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T2.isPGroup') x
    have h1 : orderOf ((x : W) : L) = 2 ^ n := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn]
    have h2 : orderOf ((x : W) : L) ∣ 3 := hK3 ▸ Subgroup.orderOf_dvd_natCard K hxK
    rw [h1] at h2
    have hn0 : n = 0 := by
      by_contra hn0
      have : 2 ∣ 3 := (dvd_pow_self 2 hn0).trans h2
      omega
    rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
    exact hn
  have hgE : ∀ t : ↥(T2 : Subgroup W), g t ∈ E := fun t => (t : W).2
  have hcommT : ∀ t t' : ↥(T2 : Subgroup W), t * t' = t' * t := by
    intro t t'
    apply hginj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨g t, hgE t⟩ ⟨g t', hgE t'⟩)
  have hsqT : ∀ t : ↥(T2 : Subgroup W), t ^ 2 = 1 := by
    intro t
    apply hginj
    rw [map_pow, map_one]
    exact hE.2 _ (hgE t)
  let f : ↥(T2 : Subgroup W) →* X := L.subtype.comp (W.subtype.comp (T2 : Subgroup W).subtype)
  have hfinj : Function.Injective f :=
    L.subtype_injective.comp (W.subtype_injective.comp (T2 : Subgroup W).subtype_injective)
  have hFE : CFSG.Assembly.IsElemAbelian 2 f.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨t, ht⟩ := a.2
      obtain ⟨t', ht'⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ht, ← ht', ← map_mul, ← map_mul, hcommT]
    · obtain ⟨t, rfl⟩ := ha
      rw [← map_pow, hsqT, map_one]
  have hFcard : Nat.card f.range = 16 := by
    rw [← hT2card]
    exact Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm
  have h8 := card_le_eight_of_isTripleCover hcfg.triple f.range hFE
  omega

end TwoRank

theorem OLRow.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : OLRow (fun T _ => Nonempty (T ≃* S'))) : OLRow (fun T _ => Nonempty (T ≃* S)) :=
  fun X _ _ P L Q hcfg ⟨f⟩ => h X P L Q hcfg ⟨f.trans e⟩

@[expose] def InnerThree (S : Type) [Group S] : Prop :=
  ∀ σ : MulAut S, σ ^ 3 = 1 → ∃ s : S, σ = MulAut.conj s

theorem InnerThree.of_mulEquiv {S T : Type} [Group S] [Group T] (e : T ≃* S)
    (h : InnerThree S) : InnerThree T := by
  intro σ hσ
  obtain ⟨s, hs⟩ := h (MulAut.congr e σ) (by rw [← map_pow, hσ, map_one])
  refine ⟨e.symm s, MulEquiv.ext fun t => ?_⟩
  have h1 := congrArg (fun φ : MulAut S => φ (e t)) hs
  have h2 : e (σ t) = s * e t * s⁻¹ := by
    rw [← MulAut.conj_apply, ← h1]
    simp [MulAut.congr_apply]
  apply e.injective
  rw [h2, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem innerThree_of_range {S : Type} [Group S]
    (h : ∀ σ : MulAut S, σ ^ 3 = 1 → σ ∈ (MulAut.conj : S →* MulAut S).range) : InnerThree S :=
  fun σ hσ => by
    obtain ⟨s, hs⟩ := h σ hσ
    exact ⟨s, hs.symm⟩

section Inner

variable {X : Type} [Group X]

theorem conjAut_mul {L : Subgroup X} {x y : X} (hx : x ∈ Subgroup.normalizer (L : Set X))
    (hy : y ∈ Subgroup.normalizer (L : Set X)) :
    conjAut (Subgroup.mul_mem _ hx hy) = conjAut hx * conjAut hy := by
  apply MulEquiv.ext
  intro l
  apply Subtype.ext
  rw [MulAut.mul_apply, coe_conjAut_apply, coe_conjAut_apply, coe_conjAut_apply]
  group

theorem coe_conjAut_pow_apply {L : Subgroup X} {x : X} (hx : x ∈ Subgroup.normalizer (L : Set X))
    (n : ℕ) (l : L) : (((conjAut hx ^ n) l : L) : X) = x ^ n * l * (x ^ n)⁻¹ := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, coe_conjAut_apply, pow_succ]
    group

theorem conjAut_pow {L : Subgroup X} {x : X} (hx : x ∈ Subgroup.normalizer (L : Set X))
    (n : ℕ) : conjAut (Subgroup.pow_mem _ hx n) = conjAut hx ^ n := by
  apply MulEquiv.ext
  intro l
  apply Subtype.ext
  rw [coe_conjAut_apply, coe_conjAut_pow_apply]

theorem conjAut_eq_one_iff {L : Subgroup X} {x : X} (hx : x ∈ Subgroup.normalizer (L : Set X)) :
    conjAut hx = 1 ↔ ∀ l ∈ L, x * l = l * x := by
  constructor
  · intro h l hl
    have h1 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : X)) h
    simp only [coe_conjAut_apply, MulAut.one_apply] at h1
    calc x * l = x * l * x⁻¹ * x := by group
      _ = l * x := by rw [h1]
  · intro h
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rw [coe_conjAut_apply, MulAut.one_apply, h l l.2]
    group

theorem mem_center_of_conj_eq_one {S : Type} [Group S] {k : S} (h : MulAut.conj k = 1) :
    k ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun φ : MulAut S => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * k = k * g * k⁻¹ * k := by rw [h1]
    _ = k * g := by group

theorem conj_eq_one_of_mem_center {S : Type} [Group S] {k : S} (h : k ∈ Subgroup.center S) :
    MulAut.conj k = 1 := by
  apply MulEquiv.ext
  intro g
  rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp h g).symm]
  group

theorem exists_inner_of_innerThree {L : Subgroup X} (h : InnerThree ↥L) {x : X}
    (hx : x ∈ Subgroup.normalizer (L : Set X)) (hx3 : x ^ 3 = 1) :
    ∃ k : L, conjAut hx = MulAut.conj k := by
  have hα3 : conjAut hx ^ 3 = 1 := by
    rw [← conjAut_pow hx 3]
    apply (conjAut_eq_one_iff _).mpr
    intro l _
    rw [hx3]
    group
  exact h _ hα3

theorem conjAut_eq_conj_innerElt' {L : Subgroup X} {x : X} (hx : x ∈ innerSub L) :
    conjAut (mem_innerSub.mp hx).1 = MulAut.conj (innerElt ⟨x, hx⟩) := by
  apply MulEquiv.ext
  intro l
  apply Subtype.ext
  rw [coe_conjAut_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact innerElt_spec ⟨x, hx⟩ l

end Inner

section Row

set_option linter.unusedSectionVars false

variable {X : Type} [Group X] [Finite X] {P L Q : Subgroup X}

theorem OLCfg.inf_centralizer_L (hcfg : OLCfg P L Q) :
    Q ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCP : IsPGroup 3 (Subgroup.centralizer (P : Set X)) :=
    ThreeGroup.isPGroup_centralizer hcfg.perf hcfg.triple hcfg.e27
  have hPn : P ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hcfg.normQ hx,
      mem_normalizer_centralizer (hcfg.normL hx)⟩
  rcases eq_bot_or_eq_of_le_kleinFour hcfg.klein inf_le_left hPn hCP with h | h
  · exact h
  · exact absurd (h ▸ inf_le_right) hcfg.Qnc

theorem OLCfg.le_innerSub (hcfg : OLCfg P L Q) (h : InnerThree ↥L) :
    P ≤ innerSub L ∧ Q ≤ innerSub L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCP : IsPGroup 3 (Subgroup.centralizer (P : Set X)) :=
    ThreeGroup.isPGroup_centralizer hcfg.perf hcfg.triple hcfg.e27
  have hPpg : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hcfg.e27.1.2 x x.2)⟩
  have hPI : P ≤ innerSub L := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_inner_of_innerThree h (hcfg.normL hx) (hcfg.e27.1.2 x hx)
    refine mem_innerSub.mpr ⟨hcfg.normL hx, k, fun l => ?_⟩
    have h1 := congrArg (fun φ : MulAut L => ((φ l : L) : X)) hk
    simp only [coe_conjAut_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1
  refine ⟨hPI, ?_⟩
  have hQ3 : ¬ 3 ∣ Nat.card Q := by rw [hcfg.klein.card_four]; norm_num
  have hQP : Q = ⁅Q, P⁆ := by
    have h := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three P Q hPpg hQ3 hcfg.normQ
    rw [inf_eq_bot_of_not_dvd hCP hQ3, sup_bot_eq] at h
    exact h
  rw [hQP, Subgroup.commutator_le]
  intro q hq p hp
  have hqN : q ∈ Subgroup.normalizer (L : Set X) := hcfg.QnormL hq
  obtain ⟨-, kp, hkp⟩ := mem_innerSub.mp (hPI hp)
  have hqpq : q * p * q⁻¹ ∈ innerSub L := by
    refine mem_innerSub.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hqN (hcfg.normL hp)) (Subgroup.inv_mem _ hqN),
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

theorem OLCfg.exists_pt_pair (hcfg : OLCfg P L Q) (h : InnerThree ↥L) :
    ∃ s t : L, s ^ 3 ∈ Subgroup.center L ∧ s ∉ Subgroup.center L ∧
      t ^ 2 ∈ Subgroup.center L ∧ t ∉ Subgroup.center L ∧
      s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center L := by
  obtain ⟨hPI, hQI⟩ := hcfg.le_innerSub h
  obtain ⟨p₀, hp₀, hp₀z, hQp₀⟩ := hcfg.pt
  obtain ⟨⟨q, hq⟩, hq1⟩ : ∃ q : Q, q ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Subsingleton Q := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have := hcfg.klein.card_four
    rw [Nat.card_unique] at this
    omega
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hq2 : q ^ 2 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨q, hq⟩ : Q)
    rw [hcfg.klein.exponent_two] at this
    exact congrArg Subtype.val this
  have hx₀ : p₀ ∈ innerSub L := hPI hp₀
  have hy₀ : q ∈ innerSub L := hQI hq
  refine ⟨innerElt ⟨p₀, hx₀⟩, innerElt ⟨q, hy₀⟩, ?_, ?_, ?_, ?_, ?_⟩
  · apply mem_center_of_conj_eq_one
    rw [map_pow, ← conjAut_eq_conj_innerElt' hx₀, ← conjAut_pow]
    exact (conjAut_eq_one_iff _).mpr fun l _ => by rw [hcfg.e27.1.2 p₀ hp₀]; group
  · intro hc
    apply hp₀z
    apply hcfg.cent p₀ hp₀
    rw [← conjAut_eq_one_iff (mem_innerSub.mp hx₀).1, conjAut_eq_conj_innerElt' hx₀]
    exact conj_eq_one_of_mem_center hc
  · apply mem_center_of_conj_eq_one
    rw [map_pow, ← conjAut_eq_conj_innerElt' hy₀, ← conjAut_pow]
    exact (conjAut_eq_one_iff _).mpr fun l _ => by rw [hq2]; group
  · intro hc
    apply hq1'
    have h1 := (conjAut_eq_one_iff (mem_innerSub.mp hy₀).1).mp (by
      rw [conjAut_eq_conj_innerElt' hy₀]; exact conj_eq_one_of_mem_center hc)
    have hqC : q ∈ Q ⊓ Subgroup.centralizer (L : Set X) :=
      ⟨hq, Subgroup.mem_centralizer_iff.mpr fun l hl => (h1 l hl).symm⟩
    rw [hcfg.inf_centralizer_L] at hqC
    exact hqC
  · apply mem_center_of_conj_eq_one
    have hcomm : p₀ * q = q * p₀ :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hQp₀ hq)).symm
    have hc : conjAut (mem_innerSub.mp hx₀).1 * conjAut (mem_innerSub.mp hy₀).1 = conjAut (mem_innerSub.mp hy₀).1 * conjAut (mem_innerSub.mp hx₀).1 := by
      apply MulEquiv.ext
      intro l
      apply Subtype.ext
      rw [MulAut.mul_apply, MulAut.mul_apply, coe_conjAut_apply, coe_conjAut_apply,
        coe_conjAut_apply, coe_conjAut_apply]
      calc p₀ * (q * (l : X) * q⁻¹) * p₀⁻¹ = (p₀ * q) * l * (p₀ * q)⁻¹ := by group
        _ = (q * p₀) * l * (q * p₀)⁻¹ := by rw [hcomm]
        _ = q * (p₀ * l * p₀⁻¹) * q⁻¹ := by group
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← conjAut_eq_conj_innerElt' hx₀,
      ← conjAut_eq_conj_innerElt' hy₀, hc]
    group

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
