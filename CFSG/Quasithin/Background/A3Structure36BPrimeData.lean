
module


public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BPrimeBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Open
open scoped commutatorElement

variable {X : Type} [Group X]

theorem exists_primeData (h129 : A129One) (h : A36BHyp X) {q : ℕ} (hq : q.Prime)
    (hπ : IsPi X q) : Nonempty (PrimeData X q) := by
  have hfin : Finite X := h.finite
  have hperf : Group.IsPerfect X := isPerfect_of_hyp h
  have hfq : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := IsPi.ne_two h hπ
  have hp1 : 1 < q := hq.one_lt
  have hRp : IsPGroup q ↥(CFSG.pCore q X) := CFSG.pCore_isPGroup
  have hrank : CFSG.Open.pRank q (⊤ : Subgroup ↥(CFSG.pCore q X)) ≤ 2 :=
    (pRank_top_le_of_injective hp1 (CFSG.pCore q X).subtype
      (CFSG.pCore q X).subtype_injective).trans (h.rank q hq hq2)
  have hRne : CFSG.pCore q X ≠ ⊥ := by
    intro hb
    apply hπ
    rw [hb]
    exact bot_le
  have hRnt : Nontrivial ↥(CFSG.pCore q X) := (Subgroup.nontrivial_iff_ne_bot _).2 hRne
  obtain ⟨P, hsc, hfaith⟩ := exists_isSupercritical_faithful (p := q) hq2 hRp
  have hPchar : P.Characteristic := hsc.characteristic
  let α : X →* MulAut ↥(CFSG.pCore q X) := MulAut.conjNormal
  have hα : α ≠ 1 := by
    intro h1
    apply hπ
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun φ : MulAut ↥(CFSG.pCore q X) =>
      ((φ ⟨r, hr⟩ : ↥(CFSG.pCore q X)) : X)) (congrArg (fun f : X →* MulAut ↥(CFSG.pCore q X) =>
        f g) h1)
    simp only [α, MulAut.conjNormal_apply, MonoidHom.one_apply, MulAut.one_apply] at h2
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hker : IsPGroup q (frattiniAction P).ker := by
    refine isPGroup_of_coprime_eq_one fun a ha => ?_
    have ha' : (orderOf (a : MulAut ↥(CFSG.pCore q X))).Coprime q := by
      rwa [← Subgroup.orderOf_coe a] at ha
    exact Subtype.ext (hfaith a ha' ((mem_ker_frattiniAction_iff P a).1 a.2))
  obtain ⟨hcard, hρ1, hinv, hirr⟩ := action_frattini_quotient hq2 hRp hrank P hsc.pow_eq_one
    hker α hα ((frattiniAction P).comp α) rfl
  have hmemK : ∀ x : X, x ∈ ((frattiniAction P).comp α).ker ↔
      ∀ d ∈ P, d⁻¹ * MulAut.conjNormal x d ∈ frattiniIn P := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      mem_ker_frattiniAction_iff]
  have hPcardW : Nat.card (↥P ⧸ frattini ↥P) ≤ Nat.card ↥P :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have hiso : IsElemAbelianOfRank q 2 ↥P ∨ IsPOnePlusTwo q ↥P := by
    rcases hsc.iso_cases hq2 hRp hrank with hcyc | hE | hH
    · exfalso
      obtain ⟨e⟩ := hcyc
      have h1 : Nat.card ↥P = q := by
        rw [Nat.card_congr e.toEquiv]
        exact Nat.card_zmod q
      have h3 := hPcardW
      rw [hcard, h1] at h3
      nlinarith [hq.two_le]
    · exact Or.inl hE
    · exact Or.inr hH
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup X, P' = P.map (CFSG.pCore q X).subtype := ⟨_, rfl⟩
  have hP'le : P' ≤ CFSG.pCore q X := hP' ▸ Subgroup.map_subtype_le P
  have hP'normal : P'.Normal := by
    rw [hP']
    infer_instance
  have hP'p : IsPGroup q ↥P' := (CFSG.pCore_isPGroup (p := q) (G := X)).to_le hP'le
  have hP'exp : ∀ x ∈ P', x ^ q = 1 := by
    intro x hx
    rw [hP'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h3 := hsc.pow_eq_one y hy
    change (y : X) ^ q = 1
    rw [← Subgroup.coe_pow, h3]
    rfl
  have hclosure : Subgroup.closure {x : X | x ∈ P' ∧ x ^ q = 1} = P' := by
    have hset : {x : X | x ∈ P' ∧ x ^ q = 1} = (P' : Set X) := by
      ext x
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, hP'exp x hx⟩⟩
    rw [hset, Subgroup.closure_eq]
  have hclass : ClassLeTwo P' := by
    unfold ClassLeTwo
    rw [hP', ← Subgroup.map_commutator, ← Subgroup.map_commutator]
    have h3 := hsc.classLeTwo
    unfold ClassLeTwo at h3
    rw [h3, Subgroup.map_bot]
  have hPne : P ≠ ⊥ := hsc.ne_bot hRp
  have hP'rank : CFSG.Open.pRank q P' = 2 := by
    apply le_antisymm
    · exact (pRank_mono hp1 le_top).trans (h.rank q hq hq2)
    · by_contra hlt
      push Not at hlt
      have hPrk : CFSG.Open.pRank q P ≤ 1 := by
        have h3 := pRank_le_map hp1 (CFSG.pCore q X).subtype
          (CFSG.pCore q X).subtype_injective P
        rw [← hP'] at h3
        omega
      obtain ⟨z, hzP, hPz, hzord⟩ :=
        exists_eq_zpowers_of_pRank_le_one hRp hPne hsc.pow_eq_one hPrk
      have hcardP : Nat.card ↥P = q := by rw [hPz, Nat.card_zpowers, hzord]
      have h3 := hPcardW
      rw [hcard, hcardP] at h3
      nlinarith [hq.two_le]
  have hcomm : ⁅P', (⊤ : Subgroup X)⁆ ≠ ⊥ := by
    intro hb
    apply hρ1
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ ((frattiniAction P).comp α).ker := by
      rw [hmemK]
      intro d hd
      have hd' : ((d : ↥(CFSG.pCore q X)) : X) ∈ P' := by
        rw [hP']
        exact ⟨d, hd, rfl⟩
      have h3 : ⁅((d : ↥(CFSG.pCore q X)) : X), x⁆ ∈ ⁅P', (⊤ : Subgroup X)⁆ :=
        Subgroup.commutator_mem_commutator hd' (Subgroup.mem_top x)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
      have h4 : MulAut.conjNormal x d = d := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
        exact h3.symm
      rw [h4, inv_mul_cancel]
      exact Subgroup.one_mem _
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    rfl
  obtain ⟨C, hCn, hC, hsl⟩ := h129 q hq hq2 X P' ⊤ hP'normal hP'p hclosure hclass hP'rank
    h.perfect hcomm
  have hker' : ∀ x : X, x ∈ ((frattiniAction P).comp α).ker ↔
      ActsTriviallyOnFrattiniQuotient P' x := by
    intro x
    rw [hP']
    exact mem_ker_frattiniAction_conjNormal (CFSG.pCore q X) P x
  have hmap : C.map (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).toMonoidHom =
      ((frattiniAction P).comp α).ker := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (hker' _).2 ((hC c).1 hc)
    · intro hx
      exact ⟨⟨x, Subgroup.mem_top x⟩, (hC _).2 ((hker' x).1 hx), rfl⟩
  let e : ↥(⊤ : Subgroup X) ⧸ C ≃* X ⧸ ((frattiniAction P).comp α).ker :=
    QuotientGroup.congr C _ Subgroup.topEquiv hmap
  have hsl' : IsSL2 q (X ⧸ ((frattiniAction P).comp α).ker) ∨
      ((q % 5 = 1 ∨ q % 5 = 4) ∧ IsSL2 5 (X ⧸ ((frattiniAction P).comp α).ker)) := by
    rcases hsl with hs | ⟨h5, hs⟩
    · left
      obtain ⟨f⟩ := hs
      exact ⟨e.symm.trans f⟩
    · right
      obtain ⟨f⟩ := hs
      exact ⟨h5, ⟨e.symm.trans f⟩⟩
  have hne_top : ((frattiniAction P).comp α).ker ≠ ⊤ := by
    intro htop
    apply hρ1
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ ((frattiniAction P).comp α).ker := htop ▸ Subgroup.mem_top x
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    rfl
  refine ⟨⟨P, ((frattiniAction P).comp α).ker, inferInstance, hne_top, hsc, hfaith, hiso, hmemK,
    hsl', hcard, ?_, ?_⟩⟩
  · intro t htK ht2 d hd
    have hρt : ((frattiniAction P).comp α) t ≠ 1 := fun h1 => htK (MonoidHom.mem_ker.2 h1)
    have hρt2 : ((frattiniAction P).comp α) t * ((frattiniAction P).comp α) t = 1 := by
      have h3 : t ^ 2 ∈ ((frattiniAction P).comp α).ker := ht2
      rw [MonoidHom.mem_ker, map_pow, pow_two] at h3
      exact h3
    have hw := hinv t hρt2 hρt ((⟨d, hd⟩ : ↥P) : ↥P ⧸ frattini ↥P)
    change frattiniAction P (α t) ((⟨d, hd⟩ : ↥P) : ↥P ⧸ frattini ↥P) = _ at hw
    rw [frattiniAction_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq] at hw
    have hw' := inv_mem hw
    rw [mul_inv_rev, inv_inv, inv_inv] at hw'
    exact ⟨_, hw', rfl⟩
  · intro hΦ U hUP hUinv
    have hcardP : Nat.card ↥P = q ^ 2 := by
      have h3 : Nat.card (↥P ⧸ (⊥ : Subgroup ↥P)) = Nat.card ↥P := by
        rw [← Subgroup.index_eq_card, Subgroup.index_bot]
      rw [hΦ] at hcard
      rw [← h3]
      exact hcard
    have hUdvd : Nat.card U ∣ q ^ 2 := hcardP ▸ Subgroup.card_dvd_of_le hUP
    obtain ⟨k, hk, hUk⟩ := (Nat.dvd_prime_pow hq).1 hUdvd
    interval_cases k
    · left
      exact Subgroup.eq_bot_of_card_eq U (by simpa using hUk)
    · exfalso
      have hUq : Nat.card U = q := by simpa using hUk
      have hU₁card : Nat.card (U.subgroupOf P) = q :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv).trans hUq
      have hinj : Function.Injective (QuotientGroup.mk' (frattini ↥P)) := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hΦ]
      have hU₂card : Nat.card ((U.subgroupOf P).map (QuotientGroup.mk' (frattini ↥P))) = q :=
        (Subgroup.card_map_of_injective hinj).trans hU₁card
      obtain ⟨h', u, hu, hnot⟩ := hirr _ hU₂card
      obtain ⟨u₁, hu₁, rfl⟩ := hu
      apply hnot
      change frattiniAction P (α h') ((u₁ : ↥P) : ↥P ⧸ frattini ↥P) ∈ _
      rw [frattiniAction_mk]
      exact ⟨_, hUinv h' u₁ hu₁, rfl⟩
    · right
      exact Subgroup.eq_of_le_of_card_ge hUP (by rw [hcardP, hUk])

end CFSG.Quasithin.A36B
