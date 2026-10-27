module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic
import CFSG.RankThree.PartOne.K1214.OmegaAlg
import CFSG.Quasithin.Background.A1cRank
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
import CFSG.RankThree.PartTwo.Sec13.K135OutPCore

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem mul_conj_mul_inv (φ : MulAut S) (g : S) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

omit [Finite S] in
theorem mem_normalizer_range_conj (φ : MulAut S) :
    φ ∈ Subgroup.normalizer ((MulAut.conj : S →* MulAut S).range : Set (MulAut S)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨φ g, (mul_conj_mul_inv φ g).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨φ⁻¹ g, ?_⟩
    have h1 := mul_conj_mul_inv φ⁻¹ g
    rw [hg] at h1
    rw [← h1]
    group

omit [Finite S] in
theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} {α : MulAut S} (hα : α ^ p = 1) :
    IsPGroup p (Subgroup.zpowers α) := by
  intro y
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hn, pow_one, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hα, one_zpow]

omit [Finite S] in
theorem eq_of_isSylowOf_le {G : Type*} [Group G] {p : ℕ} {R H J : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R J) (hHJ : H ≤ J) (hH : IsPGroup p H) (hRH : R ≤ H) :
    H = R := by
  obtain ⟨Q, rfl⟩ := hR
  have hHp : IsPGroup p (H.subgroupOf J) := hH.comap_of_injective _ J.subtype_injective
  have hQH : (Q : Subgroup J) ≤ H.subgroupOf J := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hRH ⟨y, hy, rfl⟩)
  have hEq := Q.is_maximal' hHp hQH
  rw [← hEq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHJ]

theorem commute_of_sylowShape {p e : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
    {V : Subgroup (MulAut S)} (h : KF135Hyp S p P x u V)
    (hshape : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e S) (he : 2 ≤ e) {α : MulAut S}
    (hα : α ∈ P) {a : MulAut S} (ha : a ∈ P) (hainn : a ∈ (MulAut.conj : S →* MulAut S).range) :
    α * a * α⁻¹ = a := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut S) := finite_mulAut
  have hinj := conj_injective h
  have hp5 : 5 ≤ p := by
    have := h.seven_le
    omega
  set Inn : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hInn
  set A : Subgroup (MulAut S) := P ⊓ Inn with hA
  have hAinn : A ≤ Inn := inf_le_right
  have hAp : IsPGroup p A := h.pgroup.to_le inf_le_left
  have hAcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := by
    intro c hc d hd
    have hA'p : IsPGroup p (A.comap (MulAut.conj : S →* MulAut S)) :=
      hAp.comap_of_injective _ hinj
    obtain ⟨Q₀, hQ₀⟩ := hA'p.exists_le_sylow
    have hQ₀ab := isMulCommutative_of_sylowShape hshape Q₀
    obtain ⟨c', rfl⟩ := hAinn hc
    obtain ⟨d', rfl⟩ := hAinn hd
    have hcd := congrArg Subtype.val (hQ₀ab.is_comm.comm ⟨c', hQ₀ hc⟩ ⟨d', hQ₀ hd⟩)
    simp only [Subgroup.coe_mul] at hcd
    rw [← map_mul, ← map_mul, hcd]
  set J : Subgroup (MulAut S) := Inn ⊓ Subgroup.centralizer (A : Set (MulAut S)) with hJ
  have hAJ : A ≤ J := fun c hc =>
    ⟨hAinn hc, Subgroup.mem_centralizer_iff.mpr fun d hd => hAcomm d hd c hc⟩
  have hαA : α ∈ Subgroup.normalizer (A : Set (MulAut S)) :=
    Subgroup.mem_normalizer_iff.mpr fun y => by
      constructor
      · rintro ⟨hyP, hyI⟩
        exact ⟨P.mul_mem (P.mul_mem hα hyP) (P.inv_mem hα),
          (Subgroup.mem_normalizer_iff.mp (mem_normalizer_range_conj α) y).mp hyI⟩
      · rintro ⟨hyP, hyI⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (mem_normalizer_range_conj α) y).mpr hyI⟩
        have := P.mul_mem (P.mul_mem (P.inv_mem hα) hyP) hα
        simpa [mul_assoc] using this
  have hαJ : α ∈ Subgroup.normalizer (J : Set (MulAut S)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyI, hyC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (mem_normalizer_range_conj α) y).mp hyI,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro c hc
      have hc' : α⁻¹ * c * α ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hαA) c).mp hc
        simpa using this
      have := Subgroup.mem_centralizer_iff.mp hyC _ hc'
      calc c * (α * y * α⁻¹) = α * ((α⁻¹ * c * α) * y) * α⁻¹ := by group
        _ = α * (y * (α⁻¹ * c * α)) * α⁻¹ := by rw [this]
        _ = α * y * α⁻¹ * c := by group
    · rintro ⟨hyI, hyC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (mem_normalizer_range_conj α) y).mpr hyI,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro c hc
      have hc' : α * c * α⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hαA c).mp hc
      have := Subgroup.mem_centralizer_iff.mp hyC _ hc'
      calc c * y = α⁻¹ * ((α * c * α⁻¹) * (α * y * α⁻¹)) * α := by group
        _ = α⁻¹ * ((α * y * α⁻¹) * (α * c * α⁻¹)) * α := by rw [this]
        _ = y * c := by group
  have hαp : α ^ p = 1 := h.exponent α hα
  obtain ⟨R, hR, hER⟩ := CFSG.RankThree.PartOne.exists_invariant_sylowOf
    (Subgroup.zpowers_le.mpr hαJ) (isPGroup_zpowers_of_pow_eq_one hαp)
  have hRJ : R ≤ J := hR.le
  have hRp : IsPGroup p R := hR.isPGroup
  have hαR : α ∈ Subgroup.normalizer (R : Set (MulAut S)) := hER (Subgroup.mem_zpowers α)
  have hAR : A ≤ R := by
    have hAN : A ≤ Subgroup.normalizer (R : Set (MulAut S)) := fun c hc =>
      Subgroup.mem_normalizer_iff.mpr fun y => by
        have hyJ : ∀ y ∈ R, c * y * c⁻¹ = y := fun y hy => by
          have := Subgroup.mem_centralizer_iff.mp (hRJ hy).2 c hc
          rw [this, mul_inv_cancel_right]
        constructor
        · intro hy
          rw [hyJ y hy]
          exact hy
        · intro hy
          have h1 := hyJ _ hy
          have h2 : c * y * c⁻¹ = y := by
            calc c * y * c⁻¹ = c⁻¹ * (c * (c * y * c⁻¹) * c⁻¹) * c := by group
              _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [h1]
              _ = y := by group
          rw [h2] at hy
          exact hy
    have hsup : R ⊔ A = R :=
      eq_of_isSylowOf_le hR (sup_le hRJ hAJ) (hRp.to_sup_of_normal_left' hAp hAN) le_sup_left
    exact hsup ▸ le_sup_right
  have hR'p : IsPGroup p (R.comap (MulAut.conj : S →* MulAut S)) :=
    hRp.comap_of_injective _ hinj
  obtain ⟨QS, hQS⟩ := hR'p.exists_le_sylow
  have hQSab := isMulCommutative_of_sylowShape hshape QS
  have hRinn : R ≤ Inn := hRJ.trans inf_le_left
  have hRQ : (QS : Subgroup S).map (MulAut.conj : S →* MulAut S) = R := by
    refine eq_of_isSylowOf_le hR ?_ (QS.isPGroup'.map _) ?_
    · rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
      obtain ⟨c', rfl⟩ := hAinn hc
      have hc' : c' ∈ (QS : Subgroup S) := hQS (hAR hc)
      have := congrArg Subtype.val (hQSab.is_comm.comm ⟨c', hc'⟩ ⟨y, hy⟩)
      simp only [Subgroup.coe_mul] at this
      rw [← map_mul, ← map_mul, this]
    · intro r hr
      obtain ⟨r', rfl⟩ := hRinn hr
      exact ⟨r', hQS hr, rfl⟩
  obtain ⟨φ₀⟩ := hshape QS QS.isPGroup' QS.not_dvd_index
  have φ : ↥R ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))) :=
    ((MulEquiv.subgroupCongr hRQ).symm.trans
      ((QS : Subgroup S).equivMapOfInjective _ hinj).symm).trans φ₀
  have hact := (CFSG.RankThree.PartOne.K1214.act_subgroup hp5 (Or.inr rfl) (by omega) (Or.inr he)
    φ hαR hαp).2
  exact hact a (hAR ⟨ha, hainn⟩) (h.exponent a ha)

theorem false_of_fix_two_subgroup {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
    {V : Subgroup (MulAut S)} (h : KF135Hyp S p P x u V) {α : MulAut S} (hα : α ∈ P)
    (hαout : α ∉ (MulAut.conj : S →* MulAut S).range) {b : S} (hb1 : b ≠ 1)
    (hbP : MulAut.conj b ∈ P) (hcomm : α * MulAut.conj b = MulAut.conj b * α)
    {U : Subgroup S} (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hαU : ∀ y ∈ U, α y = y)
    (hbU : ∀ y ∈ U, b * y = y * b) : False := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut S) := finite_mulAut
  have hinj := conj_injective h
  set c : MulAut S := MulAut.conj b with hc
  have hc1 : c ≠ 1 := fun h1 => hb1 (hinj (h1.trans (map_one _).symm))
  have hco : orderOf c = p := orderOf_eq_prime (h.exponent c hbP) hc1
  have hαo : orderOf α = p :=
    orderOf_eq_prime (h.exponent α hα) fun h1 => hαout (h1 ▸ Subgroup.one_mem _)
  have hE0 : CFSG.Open.IsElemAbelian p (Subgroup.zpowers c) := by
    refine ⟨⟨⟨fun y z => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp y.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp z.2
      show (y : MulAut S) * z = z * y
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hco,
        pow_orderOf_eq_one, one_zpow]
  have hcommE : ∀ y ∈ Subgroup.zpowers c, Commute y α := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_left (hcomm.symm : Commute c α) i
  have hαE : α ∉ Subgroup.zpowers c := fun h' =>
    hαout ((Subgroup.zpowers_le (H := (MulAut.conj : S →* MulAut S).range)).mpr
      (MonoidHom.mem_range.mpr ⟨b, rfl⟩) h')
  obtain ⟨hF, hFc⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE0 hαo hcommE hαE
  have hFP : Subgroup.zpowers c ⊔ Subgroup.zpowers α ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr hbP) (Subgroup.zpowers_le.mpr hα)
  have hFcard : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers α) = p ^ 2 := by
    rw [hFc, Nat.card_zpowers, hco, sq]
  let St : Subgroup (MulAut S) :=
    { carrier := {φ | ∀ y, y ∈ U ↔ φ y ∈ U}
      mul_mem' := fun {φ ψ} hφ hψ y => (hψ y).trans (hφ (ψ y))
      one_mem' := fun y => by simp
      inv_mem' := fun {φ} hφ y => by
        have h1 := hφ (φ⁻¹ y)
        simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply] at h1 ⊢
        exact h1.symm }
  have hcSt : c ∈ St := by
    intro y
    constructor
    · intro hy
      show b * y * b⁻¹ ∈ U
      rw [hbU y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have hy' : b * y * b⁻¹ ∈ U := hy
      have h1 := hbU _ hy'
      have h2 : b⁻¹ * (b * y * b⁻¹) * b = b * y * b⁻¹ := by
        rw [mul_assoc, ← h1]
        group
      have : y = b * y * b⁻¹ := by
        calc y = b⁻¹ * (b * y * b⁻¹) * b := by group
          _ = b * y * b⁻¹ := h2
      rw [this]
      exact hy'
  have hαSt : α ∈ St := by
    intro y
    constructor
    · intro hy
      rw [hαU y hy]
      exact hy
    · intro hy
      have := hαU _ hy
      rw [α.injective this] at hy
      exact hy
  have hFSt : Subgroup.zpowers c ⊔ Subgroup.zpowers α ≤ St :=
    sup_le (Subgroup.zpowers_le.mpr hcSt) (Subgroup.zpowers_le.mpr hαSt)
  obtain ⟨φ, hφ, hne⟩ := h.h2b _ hFP hF hFcard U hU1 hU2
  apply hne
  have hφU := hFSt hφ
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hφU z).mp hz
  · intro hy
    refine ⟨φ⁻¹ y, (hφU (φ⁻¹ y)).mpr ?_, ?_⟩
    · simpa only [MulAut.inv_apply, MulEquiv.apply_symm_apply] using hy
    · show φ (φ⁻¹ y) = y
      simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply]

omit [Finite S] in
theorem exists_commute_involution_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    {p : ℕ} (hY : ∀ A : Subgroup Y, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ b ∈ A, b ≠ 1 ∧ ∃ w : Y, w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b)
    (A : Subgroup X) (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ b ∈ A, b ≠ 1 ∧ ∃ w : X, w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b := by
  obtain ⟨b', hb', hb'1, w', hw'1, hw'2, hbw'⟩ := hY (A.map φ.toMonoidHom)
    (hA.map φ.toMonoidHom) (by rw [Subgroup.card_map_of_injective φ.injective, hAc])
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
  refine ⟨b, hb, fun h1 => hb'1 (by rw [h1, map_one]), φ.symm w', fun h1 => hw'1 ?_, ?_, ?_⟩
  · rw [← φ.apply_symm_apply w', h1, map_one]
  · rw [← map_pow, hw'2, map_one]
  · apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hbw'

theorem false_of_E2 {T : Type} [Group T] {p e : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
    {V : Subgroup (MulAut S)} (h : KF135Hyp S p P x u V)
    (hout : CFSG.RankThree.PartOne.OutStructure.OutPChain p S)
    (hshape : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e S) (he : 2 ≤ e) (f : S ≃* T)
    (hdesc : ∀ φ₀ : MulAut T, CFSG.RankThree.PartOne.CTP.IsOuterOfOrder p φ₀ →
      ∃ ψ φ : MulAut T, ψ * φ₀ * ψ⁻¹ = φ ∧ ∃ (X : Type) (_ : Group X) (β : X →* T),
        Function.Injective β ∧ (∀ t, φ t = t → t ∈ β.range) ∧ (∀ y, φ (β y) = β y) ∧
        ∀ A : Subgroup X, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 2 →
          ∃ b ∈ A, b ≠ 1 ∧ ∃ w : X, w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b) :
    False := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective h
  have : Finite (MulAut S) := finite_mulAut
  have hr2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_sylowShape hp hshape
  have hab := isMulCommutative_of_sylowShape hshape
  obtain ⟨α, hα, hαout⟩ : ∃ α ∈ P, α ∉ (MulAut.conj : S →* MulAut S).range := by
    by_contra hall
    push Not at hall
    exact false_of_rankLE2_inner h (fun y hy => hall y hy) hr2 hab
  set A : Subgroup (MulAut S) := P ⊓ (MulAut.conj : S →* MulAut S).range with hA
  set A' : Subgroup S := A.comap (MulAut.conj : S →* MulAut S) with hA'
  have hA'c : Nat.card A' = Nat.card A := card_comap_conj hinj inf_le_right
  have hrel : A.relIndex P ≤ p :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.relIndex_le_of_outPChain hp hout P h.exponent
  have hPA : A.relIndex P * Nat.card A = Nat.card P := by
    have := Subgroup.relIndex_mul_card (H := A) (K := P)
    rwa [show A ⊓ P = A from inf_eq_left.mpr inf_le_left] at this
  have hA'el : CFSG.Open.IsElemAbelian p A' := by
    have hA'p : IsPGroup p A' := (h.pgroup.to_le inf_le_left).comap_of_injective _ hinj
    obtain ⟨Q₀, hQ₀⟩ := hA'p.exists_le_sylow
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hinj ?_⟩
    · have := congrArg Subtype.val ((hab Q₀).is_comm.comm ⟨a.1, hQ₀ a.2⟩ ⟨b.1, hQ₀ b.2⟩)
      simpa using this
    · simpa only [map_pow, map_one] using h.exponent _ hy.1
  have hAle : Nat.card A ≤ p ^ 2 := by
    rw [← hA'c]
    exact hr2 A' hA'el
  have hAc : Nat.card A' = p ^ 2 := by
    rw [hA'c]
    refine le_antisymm hAle ?_
    by_contra hlt
    rw [not_le] at hlt
    have h3 := h.card
    have : Nat.card P < p ^ 3 := by
      rw [← hPA]
      calc A.relIndex P * Nat.card A ≤ p * Nat.card A := Nat.mul_le_mul_right _ hrel
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hp.pos
        _ = p ^ 3 := by ring
    omega
  have hαA' : ∀ a ∈ A', α a = a := by
    intro a ha
    have h1 := commute_of_sylowShape h hshape he hα ha.1 ha.2
    rw [mul_conj_mul_inv] at h1
    exact hinj h1
  have hαT : CFSG.RankThree.PartOne.CTP.IsOuterOfOrder p (MulAut.congr f α) := by
    refine ⟨?_, fun g hg => hαout ⟨f.symm g, ?_⟩⟩
    · rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (h.exponent α hα) fun h1 => hαout (h1 ▸ Subgroup.one_mem _)
    · apply (MulAut.congr f).injective
      have h1 := CFSG.LieType.SeitzGeneration.mulAut_congr_conj f (f.symm g)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.trans hg.symm
  obtain ⟨ψ, φ, hψα, X, _, β, hβinj, hfixβ, hβfix, hsing⟩ := hdesc _ hαT
  have hconj : ∀ s : S, ψ (f (α s)) = φ (ψ (f s)) := by
    intro s
    rw [← hψα]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, MulAut.congr_apply,
      MulEquiv.trans_apply]
  set A₁ : Subgroup T := (A'.map f.toMonoidHom).map ψ.toMonoidHom with hA₁
  have hA₁fix : ∀ t ∈ A₁, φ t = t := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    change φ (ψ (f a)) = ψ (f a)
    rw [← hconj, hαA' a ha]
  set A₀ : Subgroup X := A₁.comap β with hA₀
  have hA₀map : A₀.map β = A₁ :=
    Subgroup.map_comap_eq_self fun t ht => hfixβ t (hA₁fix t ht)
  have hA₁c : Nat.card A₁ = p ^ 2 := by
    rw [hA₁, Subgroup.card_map_of_injective ψ.injective,
      Subgroup.card_map_of_injective f.injective, hAc]
  have hA₀c : Nat.card A₀ = p ^ 2 := by
    rw [← hA₁c, ← hA₀map, Subgroup.card_map_of_injective hβinj]
  have hA₁el : CFSG.Open.IsElemAbelian p A₁ := (hA'el.map f.toMonoidHom).map ψ.toMonoidHom
  have hA₀el : CFSG.Open.IsElemAbelian p A₀ := hA₁el.comap hβinj
  obtain ⟨b₀, hb₀A, hb₀1, w₀, hw₀1, hw₀sq, hbw₀⟩ := hsing A₀ hA₀el hA₀c
  obtain ⟨_, ⟨bS, hbS, rfl⟩, hbSeq⟩ := Subgroup.mem_comap.mp hb₀A
  have hbSeq' : ψ (f bS) = β b₀ := hbSeq
  obtain ⟨wS, hwSeq⟩ : ∃ wS : S, ψ (f wS) = β w₀ := ⟨f.symm (ψ.symm (β w₀)), by simp⟩
  have hbS1 : bS ≠ 1 := by
    rintro rfl
    apply hb₀1
    apply hβinj
    simpa using hbSeq'.symm
  have hwS1 : wS ≠ 1 := by
    rintro rfl
    apply hw₀1
    apply hβinj
    simpa using hwSeq.symm
  have hwSsq : wS ^ 2 = 1 := by
    apply f.injective
    apply ψ.injective
    calc ψ (f (wS ^ 2)) = β (w₀ ^ 2) := by simp only [map_pow, hwSeq]
      _ = ψ (f 1) := by simp only [hw₀sq, map_one]
  have hbwS : bS * wS = wS * bS := by
    apply f.injective
    apply ψ.injective
    calc ψ (f (bS * wS)) = β (b₀ * w₀) := by simp only [map_mul, hbSeq', hwSeq]
      _ = β (w₀ * b₀) := by rw [hbw₀]
      _ = ψ (f (wS * bS)) := by simp only [map_mul, hbSeq', hwSeq]
  have hαwS : α wS = wS := by
    apply f.injective
    apply ψ.injective
    rw [hconj, hwSeq, hβfix]
  have hcomm : α * MulAut.conj bS = MulAut.conj bS * α := by
    have h1 := commute_of_sylowShape h hshape he hα hbS.1 hbS.2
    calc α * MulAut.conj bS = α * MulAut.conj bS * α⁻¹ * α := by group
      _ = MulAut.conj bS * α := by rw [h1]
  refine false_of_fix_two_subgroup h hα hαout hbS1 hbS.1 hcomm (U := Subgroup.zpowers wS)
    (Subgroup.zpowers_ne_bot.mpr hwS1) ?_ ?_ ?_
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hwSsq hwS1
  · intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [map_zpow, hαwS]
  · intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hbwS : Commute bS wS) n).eq

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
