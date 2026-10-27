module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.MS93.S38G

open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

@[expose] def cRel (A N : Subgroup Γ) : Subgroup Γ where
  carrier := {g | g ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ a ∈ A, ⁅g, a⁆ ∈ N}
  one_mem' := ⟨Subgroup.one_mem _, fun a _ => by rw [commutatorElement_one_left]; exact N.one_mem⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨Subgroup.mul_mem _ hg hh, fun a ha => ?_⟩
    have e : ⁅g * h, a⁆ = (g * ⁅h, a⁆ * g⁻¹) * ⁅g, a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hg _).mp (hh' a ha)) (hg' a ha)
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨Subgroup.inv_mem _ hg, fun a ha => ?_⟩
    have e : ⁅g⁻¹, a⁆ = g⁻¹ * ⁅g, a⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp (N.inv_mem (hg' a ha))

theorem mem_cRel {A N : Subgroup Γ} {g : Γ} :
    g ∈ cRel A N ↔ g ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ a ∈ A, ⁅g, a⁆ ∈ N := Iff.rfl

@[expose] def cOf (g : Γ) (N : Subgroup Γ) : Subgroup Γ where
  carrier := {x | x ∈ Subgroup.normalizer (N : Set Γ) ∧ ⁅g, x⁆ ∈ N}
  one_mem' := ⟨Subgroup.one_mem _, by rw [commutatorElement_one_right]; exact N.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    have e : ⁅g, x * y⁆ = ⁅g, x⁆ * (x * ⁅g, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem hx' ((Subgroup.mem_normalizer_iff.mp hx _).mp hy')
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨Subgroup.inv_mem _ hx, ?_⟩
    have e : ⁅g, x⁻¹⁆ = x⁻¹ * ⁅g, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp (N.inv_mem hx')

@[expose] def botLayer (N H Q : Subgroup Γ) : Subgroup Γ where
  carrier := {h | h ∈ H ∧ h ∈ Q ∧ h ∈ Subgroup.normalizer (N : Set Γ) ∧ h ^ 2 ∈ N ∧
    ∀ q ∈ Q, ⁅h, q⁆ ∈ N}
  one_mem' := ⟨H.one_mem, Q.one_mem, Subgroup.one_mem _, by simp [N.one_mem], fun q _ => by
    rw [commutatorElement_one_left]; exact N.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haH, haQ, haN, ha2, ha⟩ ⟨hbH, hbQ, hbN, hb2, hb⟩
    refine ⟨H.mul_mem haH hbH, Q.mul_mem haQ hbQ, Subgroup.mul_mem _ haN hbN, ?_, fun q hq => ?_⟩
    · have e : (a * b) ^ 2 = ⁅a, b⁆ * (b * a ^ 2 * b⁻¹) * b ^ 2 := by
        simp only [commutatorElement_def, pow_two]
        group
      rw [e]
      exact N.mul_mem (N.mul_mem (ha b hbQ) ((Subgroup.mem_normalizer_iff.mp hbN _).mp ha2)) hb2
    · have e : ⁅a * b, q⁆ = (a * ⁅b, q⁆ * a⁻¹) * ⁅a, q⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb q hq)) (ha q hq)
  inv_mem' := by
    rintro a ⟨haH, haQ, haN, ha2, ha⟩
    refine ⟨H.inv_mem haH, Q.inv_mem haQ, Subgroup.inv_mem _ haN, ?_, fun q hq => ?_⟩
    · rw [inv_pow]
      exact N.inv_mem ha2
    · have e : ⁅a⁻¹, q⁆ = a⁻¹ * ⁅a, q⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp (N.inv_mem (ha q hq))

variable {N H Q : Subgroup Γ}

theorem botLayer_le : botLayer N H Q ≤ H := fun _ h => h.1

theorem le_botLayer (hNH : N ≤ H) (hHQ : H ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (N : Set Γ)) : N ≤ botLayer N H Q := by
  intro n hn
  refine ⟨hNH hn, hHQ (hNH hn), Subgroup.le_normalizer hn, N.pow_mem hn 2, fun q hq => ?_⟩
  have e : ⁅n, q⁆ = n * (q * n⁻¹ * q⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hQN hq) _).mp (N.inv_mem hn))

theorem le_normalizer_botLayer {P : Subgroup Γ} (hPN : P ≤ Subgroup.normalizer (N : Set Γ))
    (hPH : P ≤ Subgroup.normalizer (H : Set Γ)) (hPQ : P ≤ Subgroup.normalizer (Q : Set Γ)) :
    P ≤ Subgroup.normalizer (botLayer N H Q : Set Γ) := by
  have key : ∀ g ∈ P, ∀ h ∈ botLayer N H Q, g * h * g⁻¹ ∈ botLayer N H Q := by
    rintro g hg h ⟨hH, hQ, hN, h2, hq⟩
    have hgN := hPN hg
    have hgN' := hPN (P.inv_mem hg)
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hPH hg) h).mp hH,
      (Subgroup.mem_normalizer_iff.mp (hPQ hg) h).mp hQ, ?_, ?_, fun q hq' => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hN) (Subgroup.inv_mem _ hgN)
    · have e : (g * h * g⁻¹) ^ 2 = g * h ^ 2 * g⁻¹ := by
        simp only [pow_two]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hgN _).mp h2
    · have hq'' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hPQ (P.inv_mem hg)) q).mp hq'
      have e : ⁅g * h * g⁻¹, q⁆ = g * ⁅h, g⁻¹ * q * g⁻¹⁻¹⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hgN _).mp (hq _ hq'')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (P.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem commutator_mem_of_botLayer {a b : Γ} (ha : a ∈ botLayer N H Q)
    (hb : b ∈ botLayer N H Q) : ⁅a, b⁆ ∈ N :=
  ha.2.2.2.2 b hb.2.1

theorem exists_mem_botLayer [Finite ↥Q] (hQ : IsPGroup 2 ↥Q) (hNH : N ≤ H) (hHQ : H ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (N : Set Γ)) (hQH : Q ≤ Subgroup.normalizer (H : Set Γ))
    (hne : ¬ H ≤ N) : ∃ h ∈ botLayer N H Q, h ∉ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup ↥Q := N.subgroupOf Q
  have hN' : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (hNH.trans hHQ)).mpr hQN
  set H' : Subgroup ↥Q := H.subgroupOf Q
  have hH' : H'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHQ).mpr hQH
  set π := QuotientGroup.mk' N'
  set Hb : Subgroup (↥Q ⧸ N') := H'.map π
  have hHb : Hb.Normal := Subgroup.Normal.map hH' π (QuotientGroup.mk'_surjective N')
  have hp : IsPGroup 2 (↥Q ⧸ N') := hQ.to_quotient N'
  have : Group.IsNilpotent (↥Q ⧸ N') := hp.isNilpotent
  have hHb1 : Hb ≠ ⊥ := by
    intro hb
    apply hne
    intro h hh
    have h1 : π ⟨h, hHQ hh⟩ ∈ Hb := ⟨⟨h, hHQ hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hHb1
  set Z := Hb ⊓ Subgroup.center (↥Q ⧸ N')
  have : Fintype ↥Z := Fintype.ofFinite _
  have hZp : IsPGroup 2 ↥Z := hp.to_subgroup Z
  have hZnt : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZ
  obtain ⟨n, hn⟩ := hZp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hn
  have hdvd : 2 ∣ Fintype.card ↥Z := by
    rw [← Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 hdvd
  obtain ⟨⟨q, hq⟩, hqH, hqz⟩ := z.2.1
  have hzc := z.2.2
  have hqH' : q ∈ H := Subgroup.mem_subgroupOf.mp hqH
  refine ⟨q, ⟨hqH', hq, hQN hq, ?_, fun q' hq' => ?_⟩, fun hqN => ?_⟩
  · have h1 : π ⟨q, hq⟩ ^ 2 = 1 := by
      rw [hqz]
      have : (z : ↥Q ⧸ N') ^ orderOf z = 1 := by
        rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      rwa [hz] at this
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · have h1 : π ⁅(⟨q, hq⟩ : ↥Q), ⟨q', hq'⟩⁆ = 1 := by
      rw [map_commutatorElement, hqz, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hzc _).symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · have h1 : (z : ↥Q ⧸ N') = 1 := by
      rw [← hqz, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hqN
    have h2 : z = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem commutator_top_eq_top {L : Subgroup Γ} (h : ⁅L, L⁆ = L) :
    ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
  have e : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_commutator, e, h]

theorem range_eq_bot_of_perfect {P S : Type*} [Group P] [Group S] [Group.IsSolvable S]
    (f : P →* S)
    (hP : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤) : f.range = ⊥ := by
  by_contra hne
  have : Nontrivial ↥f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥f.range)
  apply hlt.ne
  have hs : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  rw [commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator, hP]

@[expose] def conjK {K L : Subgroup Γ} (hLK : L ≤ Subgroup.normalizer (K : Set Γ)) (l : ↥L) :
    ↥K ≃* ↥K where
  toFun k := ⟨(l : Γ) * k * (l : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLK l.2) k).mp k.2⟩
  invFun k := ⟨(l : Γ)⁻¹ * k * (l : Γ)⁻¹⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hLK (L.inv_mem l.2)) k).mp k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjK_apply_coe {K L : Subgroup Γ} (hLK : L ≤ Subgroup.normalizer (K : Set Γ)) (l : ↥L)
    (k : ↥K) : ((conjK hLK l k : ↥K) : Γ) = (l : Γ) * k * (l : Γ)⁻¹ := rfl

theorem map_conjK_subgroupOf {K E L : Subgroup Γ} (hLK : L ≤ Subgroup.normalizer (K : Set Γ))
    (hLE : L ≤ Subgroup.normalizer (E : Set Γ)) (l : ↥L) :
    (E.subgroupOf K).map (conjK hLK l).toMonoidHom = E.subgroupOf K := by
  ext k
  constructor
  · rintro ⟨k', hk', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk'
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hLE l.2) k').mp hk'
  · intro hk
    refine ⟨(conjK hLK l).symm k, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf] at hk
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hLE (L.inv_mem l.2)) k).mp hk

@[expose] noncomputable def quotAct {K E L : Subgroup Γ} [(E.subgroupOf K).Normal]
    (hLK : L ≤ Subgroup.normalizer (K : Set Γ)) (hLE : L ≤ Subgroup.normalizer (E : Set Γ)) :
    ↥L →* MulAut (↥K ⧸ E.subgroupOf K) :=
  { toFun := fun l => QuotientGroup.congr _ _ (conjK hLK l) (map_conjK_subgroupOf hLK hLE l)
    map_one' := by
      ext y
      induction y using QuotientGroup.induction_on with
      | H k =>
        apply congrArg (QuotientGroup.mk (s := E.subgroupOf K))
        exact Subtype.ext (by simp [conjK])
    map_mul' := fun a b => by
      ext y
      induction y using QuotientGroup.induction_on with
      | H k =>
        apply congrArg (QuotientGroup.mk (s := E.subgroupOf K))
        exact Subtype.ext (by simp [conjK, mul_assoc]) }

theorem commutator_le_of_relIndex_le_four {K E L : Subgroup Γ} (hEK : E ≤ K)
    (hKE : K ≤ Subgroup.normalizer (E : Set Γ)) (hLK : L ≤ Subgroup.normalizer (K : Set Γ))
    (hLE : L ≤ Subgroup.normalizer (E : Set Γ)) (hL : ⁅L, L⁆ = L) (h0 : E.relIndex K ≠ 0)
    (h4 : E.relIndex K ≤ 4) : ⁅K, L⁆ ≤ E := by
  have : (E.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mpr hKE
  have : (E.subgroupOf K).FiniteIndex := ⟨h0⟩
  have hfin : Finite (↥K ⧸ E.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  have hcard : Nat.card (↥K ⧸ E.subgroupOf K) ≤ 4 := by
    rw [← Subgroup.index, ← Subgroup.relIndex]
    exact h4
  have : Group.IsSolvable (Equiv.Perm (↥K ⧸ E.subgroupOf K)) := Equiv.Perm.isSolvable hcard
  set ψ := quotAct (K := K) (E := E) hLK hLE
  have hr := range_eq_bot_of_perfect (MonoidHom.comp (MulAut.toPerm _) ψ) (commutator_top_eq_top hL)
  rw [Subgroup.commutator_le]
  intro k hk l hl
  have h1 : MulAut.toPerm _ (ψ ⟨l, hl⟩) = 1 := by
    have : (MonoidHom.comp (MulAut.toPerm _) ψ) ⟨l, hl⟩ ∈
        (MonoidHom.comp (MulAut.toPerm _) ψ).range :=
      ⟨_, rfl⟩
    rw [hr, Subgroup.mem_bot] at this
    exact this
  have h2 : ψ ⟨l, hl⟩ (QuotientGroup.mk ⟨k⁻¹, K.inv_mem hk⟩) =
      QuotientGroup.mk ⟨k⁻¹, K.inv_mem hk⟩ := by
    have := congrArg (fun σ : Equiv.Perm (↥K ⧸ E.subgroupOf K) =>
      σ (QuotientGroup.mk ⟨k⁻¹, K.inv_mem hk⟩)) h1
    exact this
  change QuotientGroup.mk (conjK hLK ⟨l, hl⟩ ⟨k⁻¹, K.inv_mem hk⟩) = _ at h2
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply_coe] at h2
  have e : ⁅k, l⁆ = ((l * k⁻¹ * l⁻¹)⁻¹ * k⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact E.inv_mem h2

theorem two_step {N J H L : Subgroup Γ} (hNJ : N ≤ J) (hJN : J ≤ Subgroup.normalizer (N : Set Γ))
    (hab : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ N) (hHL : ⁅H, L⁆ ≤ J) (hJL : ⁅J, L⁆ ≤ N)
    (hL : ⁅L, L⁆ = L) : ⁅H, L⁆ ≤ N := by
  have : (N.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mpr hJN
  rw [Subgroup.commutator_le]
  intro h hh
  have hmem : ∀ l ∈ L, ⁅h, l⁆ ∈ J := fun l hl => hHL (Subgroup.commutator_mem_commutator hh hl)
  have hconj : ∀ l ∈ L, ∀ j ∈ J, ⁅l, j⁆ ∈ N := by
    intro l hl j hj
    rw [← commutatorElement_inv]
    exact N.inv_mem (hJL (Subgroup.commutator_mem_commutator hj hl))
  let θ : ↥L →* ↥J ⧸ N.subgroupOf J :=
    { toFun := fun l => QuotientGroup.mk ⟨⁅h, (l : Γ)⁆, hmem l l.2⟩
      map_one' := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simp [N.one_mem]
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hb := hmem b b.2
        have e : ((⟨⁅h, ((a * b : ↥L) : Γ)⁆, hmem _ (a * b).2⟩ : ↥J)⁻¹ *
            (⟨⁅h, (a : Γ)⁆, hmem a a.2⟩ * ⟨⁅h, (b : Γ)⁆, hb⟩) : ↥J) =
            ⁅(a : Γ), ⁅h, (b : Γ)⁆⁻¹⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        exact hconj a a.2 _ (J.inv_mem hb) }
  have hcomm : ∀ p q : ↥J ⧸ N.subgroupOf J, p * q = q * p := by
    intro p q
    induction p using QuotientGroup.induction_on with
    | H x =>
      induction q using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have e : (((x * y)⁻¹ * (y * x) : ↥J) : Γ) = ⁅(y : Γ)⁻¹, (x : Γ)⁻¹⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        exact hab _ (J.inv_mem y.2) _ (J.inv_mem x.2)
  have hker : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ θ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  intro l hl
  have h1 : (⟨l, hl⟩ : ↥L) ∈ θ.ker := by
    rw [commutator_top_eq_top hL] at hker
    exact hker (Subgroup.mem_top _)
  rw [MonoidHom.mem_ker] at h1
  change QuotientGroup.mk _ = 1 at h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem commutator_le_self_of {H L : Subgroup Γ} (hLH : L ≤ Subgroup.normalizer (H : Set Γ)) :
    ⁅H, L⁆ ≤ H :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 hLH

theorem le_normalizer_of_conj {S E : Subgroup Γ} (h : ∀ g ∈ S, ∀ e ∈ E, g * e * g⁻¹ ∈ E) :
    S ≤ Subgroup.normalizer (E : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨h g hg e, fun he => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ he
  simpa [mul_assoc] using this

variable {L A₁ A₂ : Subgroup Γ}

theorem commutator_botLayer_le [Finite ↥Q] (hNH : N ≤ H) (hHQ : H ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (hLH : L ≤ Subgroup.normalizer (H : Set Γ)) (hLQ : L ≤ Subgroup.normalizer (Q : Set Γ))
    (hA₁N : A₁ ≤ Subgroup.normalizer (N : Set Γ)) (hA₂N : A₂ ≤ Subgroup.normalizer (N : Set Γ))
    (hL : ⁅L, L⁆ = L) (hgen : L ≤ A₁ ⊔ A₂ ⊔ Q) (hc₁ : (cRel A₁ N).relIndex H ≤ 2)
    (hc₂ : (cRel A₂ N).relIndex H ≤ 2) : ⁅botLayer N H Q, L⁆ ≤ N := by
  set K := botLayer N H Q with hKdef
  have hKH : K ≤ H := botLayer_le
  have hNK : N ≤ K := le_botLayer hNH hHQ hQN
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective (hKH.trans hHQ))
  have hKN : K ≤ Subgroup.normalizer (N : Set Γ) := fun k hk => hk.2.2.1
  set E := cRel L N ⊓ K with hEdef
  have hEK : E ≤ K := inf_le_right
  have hNE : N ≤ E := by
    intro n hn
    refine ⟨⟨Subgroup.le_normalizer hn, fun l hl => ?_⟩, hNK hn⟩
    have e : ⁅n, l⁆ = n * (l * n⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hLN hl) _).mp (N.inv_mem hn))
  have hKE : K ≤ Subgroup.normalizer (E : Set Γ) := by
    refine le_normalizer_of_conj fun k hk e he => ?_
    have hc : ⁅e⁻¹, k⁆ ∈ N := commutator_mem_of_botLayer (K.inv_mem (hEK he)) hk
    have e1 : k * e * k⁻¹ = e * ⁅e⁻¹, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact E.mul_mem he (hNE hc)
  have hLK : L ≤ Subgroup.normalizer (K : Set Γ) := le_normalizer_botLayer hLN hLH hLQ
  have hLE : L ≤ Subgroup.normalizer (E : Set Γ) := by
    refine le_normalizer_of_conj fun l hl e he => ?_
    obtain ⟨⟨heN, he'⟩, heK⟩ := he
    refine ⟨⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLN hl) heN) (Subgroup.inv_mem _ (hLN hl)),
      fun l' hl' => ?_⟩, (Subgroup.mem_normalizer_iff.mp (hLK hl) e).mp heK⟩
    have e1 : ⁅l * e * l⁻¹, l'⁆ = l * ⁅e, l⁻¹ * l' * l⁻¹⁻¹⁆ * l⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    have hl'' : l⁻¹ * l' * l⁻¹⁻¹ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hl') (L.inv_mem
      (L.inv_mem hl))
    exact (Subgroup.mem_normalizer_iff.mp (hLN hl) _).mp (he' _ hl'')
  have hDE : cRel A₁ N ⊓ cRel A₂ N ⊓ K ≤ E := by
    rintro d ⟨⟨hd₁, hd₂⟩, hdK⟩
    refine ⟨⟨hd₁.1, fun l hl => ?_⟩, hdK⟩
    have hle : A₁ ⊔ A₂ ⊔ Q ≤ cOf d N := by
      refine sup_le (sup_le (fun a ha => ⟨hA₁N ha, hd₁.2 a ha⟩) (fun a ha => ⟨hA₂N ha, hd₂.2 a ha⟩))
        (fun q hq => ⟨hQN hq, hdK.2.2.2.2 q hq⟩)
    exact (hle (hgen hl)).2
  have h0 : ∀ X : Subgroup Γ, X.relIndex K ≠ 0 := fun X => by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h0H : ∀ X : Subgroup Γ, X.relIndex H ≠ 0 := fun X => by
    have : Finite ↥H := Finite.of_injective _ (Subgroup.inclusion_injective hHQ)
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h4 : E.relIndex K ≤ 4 := by
    have h1 : E.relIndex K ≤ (cRel A₁ N ⊓ cRel A₂ N ⊓ K).relIndex K :=
      Subgroup.relIndex_le_of_le_left hDE (h0 _)
    have h2 : (cRel A₁ N ⊓ cRel A₂ N ⊓ K).relIndex K = (cRel A₁ N ⊓ cRel A₂ N).relIndex K :=
      Subgroup.inf_relIndex_right _ _
    have h3 := Subgroup.relIndex_inf_le (H := cRel A₁ N) (K := cRel A₂ N) (L := K)
    have h5 : (cRel A₁ N).relIndex K ≤ 2 :=
      (Subgroup.relIndex_le_of_le_right hKH (h0H _)).trans hc₁
    have h6 : (cRel A₂ N).relIndex K ≤ 2 :=
      (Subgroup.relIndex_le_of_le_right hKH (h0H _)).trans hc₂
    calc E.relIndex K ≤ (cRel A₁ N).relIndex K * (cRel A₂ N).relIndex K := by
          rw [← h2] at h3; exact h1.trans h3
      _ ≤ 2 * 2 := Nat.mul_le_mul h5 h6
      _ = 4 := rfl
  have hKLE : ⁅K, L⁆ ≤ E := commutator_le_of_relIndex_le_four hEK hKE hLK hLE hL (h0 _) h4
  have hEL : ⁅E, L⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro e he l hl
    exact he.1.2 l hl
  exact two_step hNE (fun e he => hKN (hEK he))
    (fun a ha b hb => commutator_mem_of_botLayer (hEK ha) (hEK hb)) hKLE hEL hL

theorem commutator_le_of_codim [Finite ↥Q] (hQ : IsPGroup 2 ↥Q) (hHQ : H ≤ Q)
    (hQH : Q ≤ Subgroup.normalizer (H : Set Γ)) (hLH : L ≤ Subgroup.normalizer (H : Set Γ))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set Γ)) (hA₁H : A₁ ≤ Subgroup.normalizer (H : Set Γ))
    (hA₁Q : A₁ ≤ Subgroup.normalizer (Q : Set Γ)) (hA₂H : A₂ ≤ Subgroup.normalizer (H : Set Γ))
    (hA₂Q : A₂ ≤ Subgroup.normalizer (Q : Set Γ)) (hL : ⁅L, L⁆ = L) (hgen : L ≤ A₁ ⊔ A₂ ⊔ Q)
    (N : Subgroup Γ) (hNH : N ≤ H) (hQN : Q ≤ Subgroup.normalizer (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ)) (hA₁N : A₁ ≤ Subgroup.normalizer (N : Set Γ))
    (hA₂N : A₂ ≤ Subgroup.normalizer (N : Set Γ)) (hc₁ : (cRel A₁ N).relIndex H ≤ 2)
    (hc₂ : (cRel A₂ N).relIndex H ≤ 2) : ⁅H, L⁆ ≤ N := by
  have : Finite ↥H := Finite.of_injective _ (Subgroup.inclusion_injective hHQ)
  have h0H : ∀ X : Subgroup Γ, X.relIndex H ≠ 0 := fun X => by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  suffices key : ∀ n, ∀ N : Subgroup Γ, Nat.card ↥H - Nat.card ↥N = n → N ≤ H →
      Q ≤ Subgroup.normalizer (N : Set Γ) → L ≤ Subgroup.normalizer (N : Set Γ) →
      A₁ ≤ Subgroup.normalizer (N : Set Γ) → A₂ ≤ Subgroup.normalizer (N : Set Γ) →
      (cRel A₁ N).relIndex H ≤ 2 → (cRel A₂ N).relIndex H ≤ 2 → ⁅H, L⁆ ≤ N from
    key _ N rfl hNH hQN hLN hA₁N hA₂N hc₁ hc₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hNH hQN hLN hA₁N hA₂N hc₁ hc₂
  by_cases hHN : H ≤ N
  · exact (commutator_le_self_of hLH).trans hHN
  set K := botLayer N H Q with hKdef
  have hKH : K ≤ H := botLayer_le
  have hNK : N ≤ K := le_botLayer hNH hHQ hQN
  obtain ⟨k, hkK, hkN⟩ := exists_mem_botLayer hQ hNH hHQ hQN hQH hHN
  have hlt : Nat.card ↥N < Nat.card ↥K := by
    have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective (hKH.trans hHQ))
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hNK fun e => hkN (e ▸ hkK))
  have hKle : Nat.card ↥K ≤ Nat.card ↥H := Subgroup.card_le_of_le hKH
  have hQK : Q ≤ Subgroup.normalizer (K : Set Γ) :=
    le_normalizer_botLayer hQN hQH Subgroup.le_normalizer
  have hLK : L ≤ Subgroup.normalizer (K : Set Γ) := le_normalizer_botLayer hLN hLH hLQ
  have hA₁K : A₁ ≤ Subgroup.normalizer (K : Set Γ) := le_normalizer_botLayer hA₁N hA₁H hA₁Q
  have hA₂K : A₂ ≤ Subgroup.normalizer (K : Set Γ) := le_normalizer_botLayer hA₂N hA₂H hA₂Q
  have hcK : ∀ A : Subgroup Γ, (cRel A N).relIndex H ≤ 2 → (cRel A K).relIndex H ≤ 2 := by
    intro A hA
    have hle : cRel A N ⊓ H ≤ cRel A K := by
      rintro h ⟨⟨_, hh⟩, hhH⟩
      exact ⟨hQK (hHQ hhH), fun a ha => hNK (hh a ha)⟩
    have h1 := Subgroup.relIndex_le_of_le_left hle (h0H _)
    rw [Subgroup.inf_relIndex_right] at h1
    exact h1.trans hA
  have hHK : ⁅H, L⁆ ≤ K := ih (Nat.card ↥H - Nat.card ↥K) (by omega) K rfl hKH hQK hLK hA₁K hA₂K
    (hcK _ hc₁) (hcK _ hc₂)
  have hKL : ⁅K, L⁆ ≤ N := commutator_botLayer_le hNH hHQ hQN hLN hLH hLQ hA₁N hA₂N hL hgen hc₁ hc₂
  exact two_step hNK (fun x hx => hx.2.2.1) (fun a ha b hb => commutator_mem_of_botLayer ha hb)
    hHK hKL hL

end CFSG.Quasithin.MS93.S38G
