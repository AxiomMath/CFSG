module

public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.Quasithin.Background.A1cA131

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

theorem eq_one_of_centralizes_of_faithful {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {P A : Subgroup G} (hPp : IsPGroup p P)
    (hfaith : ∀ a ∈ A, (∀ z ∈ P, a * z = z * a) → a = 1) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {y : G} (hy : y ∈ P) {a : G} (ha : a ∈ A) (hn : ∀ z ∈ P, a * z * a⁻¹ ∈ P)
    (hg : ∀ z ∈ P, (y * a) * z = z * (y * a)) : a = 1 := by
  apply hfaith a ha
  have h1 : ∀ z ∈ P, a * z * a⁻¹ = y⁻¹ * z * y := by
    intro z hz
    have := hg z hz
    calc a * z * a⁻¹ = y⁻¹ * (y * a * z) * a⁻¹ := by group
      _ = y⁻¹ * (z * (y * a)) * a⁻¹ := by rw [this]
      _ = y⁻¹ * z * y := by group
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
  have h2 : ∀ z ∈ P, (y * y) * z = z * (y * y) := by
    intro z hz
    have hw : a * z * a⁻¹ ∈ P := hn z hz
    have e1 : a * (a * z * a⁻¹) * a⁻¹ = z := by
      calc a * (a * z * a⁻¹) * a⁻¹ = (a * a) * z * (a * a)⁻¹ := by group
        _ = z := by rw [ha2]; simp
    have e2 : a * (a * z * a⁻¹) * a⁻¹ = y⁻¹ * (y⁻¹ * z * y) * y := by
      rw [h1 _ hw, h1 z hz]
    have : z = y⁻¹ * (y⁻¹ * z * y) * y := e1.symm.trans e2
    calc (y * y) * z = (y * y) * (y⁻¹ * (y⁻¹ * z * y) * y) := by rw [← this]
      _ = z * (y * y) := by group
  have hodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := hPp ⟨y, hy⟩
    have hk' : y ^ p ^ k = 1 := congrArg Subtype.val hk
    exact Odd.of_dvd_nat (((Fact.out : p.Prime).odd_of_ne_two hp).pow) (orderOf_dvd_of_pow_eq_one hk')
  obtain ⟨m, hm⟩ := hodd
  have hyy : y = (y * y) ^ (m + 1) := by
    have e : orderOf y + 1 = 2 * (m + 1) := by omega
    calc y = y ^ (orderOf y + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
      _ = y ^ (2 * (m + 1)) := by rw [e]
      _ = (y * y) ^ (m + 1) := by rw [pow_mul, sq]
  have h3 : ∀ z ∈ P, y * z = z * y := by
    intro z hz
    have : Commute (y * y) z := h2 z hz
    have hc : Commute ((y * y) ^ (m + 1)) z := this.pow_left (m + 1)
    rw [← hyy] at hc
    exact hc.eq
  intro z hz
  have h4 : y⁻¹ * z * y = z := by
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [h3 z hz]
      _ = z := by group
  have := h1 z hz
  rw [h4] at this
  exact mul_inv_eq_iff_eq_mul.mp this

omit [Finite V] in
theorem exists_sqt_cover_of_le {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hX : IsQuotientOfSQTKTC ↥X) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S),
      (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2) ∧
        ∃ φ : S →* ↥K, Function.Surjective φ := by
  obtain ⟨S, _, _, hSQT, -, φ, hφ⟩ := hX
  let K' : Subgroup ↥X := K.subgroupOf X
  refine ⟨↥(K'.comap φ), inferInstance, inferInstance, ?_, ?_⟩
  · intro p hp hp2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (K'.comap φ).subtype
      (K'.comap φ).subtype_injective).trans (hSQT p hp hp2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom.comp (φ.subgroupComap K'), ?_⟩
    exact (Subgroup.subgroupOfEquivOfLe hKX).surjective.comp
      (MonoidHom.subgroupComap_surjective φ K' hφ)

omit [Finite V] in
theorem normal_subgroupOf_sup {P A : Subgroup (MulAut V)}
    (hAn : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P) : (P.subgroupOf (P ⊔ A)).Normal := by
  have hnorm : P ⊔ A ≤ Subgroup.normalizer (P : Set (MulAut V)) := by
    refine sup_le Subgroup.le_normalizer fun a ha => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hAn a ha y, fun hy => ?_⟩
    have := hAn a⁻¹ (A.inv_mem ha) _ hy
    simpa [mul_assoc] using this
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := (Subgroup.mem_normalizer_iff.mp (hnorm g.2) n).mp hn
  simpa using this

omit [Finite V] in
theorem subgroupOf_le_pCore {P A : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime]
    (hPp : IsPGroup p P) (hAn : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P) :
    P.subgroupOf (P ⊔ A) ≤ CFSG.Open.pCore p ↥(P ⊔ A) := by
  have hpK : IsPGroup p ↥(P.subgroupOf (P ⊔ A)) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ _)).symm
  exact le_pCore p (normal_subgroupOf_sup hAn) hpK

theorem a131_of_faithful {X P A : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hPX : P ≤ X) (hPp : IsPGroup p P) (hA2 : IsElemAbelian2 A) (hAX : A ≤ X)
    (hAn : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P) (hX : IsQuotientOfSQTKTC ↥X)
    (hfaith : ∀ a ∈ A, (∀ y ∈ P, a * y = y * a) → a = 1) :
    A1c.A131Concl p ↥(P ⊔ A) := by
  have hKX : P ⊔ A ≤ X := sup_le hPX hAX
  obtain ⟨S, _, _, hS, φ, hφ⟩ := exists_sqt_cover_of_le hKX hX
  have hPK : P ≤ P ⊔ A := le_sup_left
  have hAK : A ≤ P ⊔ A := le_sup_right
  have hnormK : (P.subgroupOf (P ⊔ A)).Normal := normal_subgroupOf_sup hAn
  have hle : P.subgroupOf (P ⊔ A) ≤ CFSG.Open.pCore p ↥(P ⊔ A) := subgroupOf_le_pCore hPp hAn
  have hF : Subgroup.centralizer (CFSG.Open.pCore p ↥(P ⊔ A) : Set ↥(P ⊔ A)) ≤
      CFSG.Open.pCore p ↥(P ⊔ A) := by
    intro g hg
    have hsup : (P.subgroupOf (P ⊔ A)) ⊔ (A.subgroupOf (P ⊔ A)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPK hAK, Subgroup.subgroupOf_self]
    have hgtop : g ∈ (P.subgroupOf (P ⊔ A)) ⊔ (A.subgroupOf (P ⊔ A)) := by
      rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨n, hn, h, hh, hnh⟩ := Subgroup.mem_sup_of_normal_left.mp hgtop
    have hnP : (n : MulAut V) ∈ P := hn
    have hhA : (h : MulAut V) ∈ A := hh
    have hgc : ∀ z ∈ P, ((n : MulAut V) * (h : MulAut V)) * z =
        z * ((n : MulAut V) * (h : MulAut V)) := by
      intro z hz
      have hzK : z ∈ P ⊔ A := hPK hz
      have hzmem : (⟨z, hzK⟩ : ↥(P ⊔ A)) ∈ CFSG.Open.pCore p ↥(P ⊔ A) := hle hz
      have := Subgroup.mem_centralizer_iff.mp hg _ hzmem
      have h2 := congrArg (fun w : ↥(P ⊔ A) => (w : MulAut V)) this
      have h3 : ((g : ↥(P ⊔ A)) : MulAut V) = (n : MulAut V) * (h : MulAut V) := by
        rw [← hnh]; rfl
      simp only [Subgroup.coe_mul] at h2
      rw [h3] at h2
      exact h2.symm
    have hh1 : (h : MulAut V) = 1 := eq_one_of_centralizes_of_faithful hp hPp hfaith hA2.2 hnP
      hhA (hAn _ hhA) hgc
    have hh2 : h = 1 := Subtype.ext hh1
    rw [hh2, mul_one] at hnh
    rw [← hnh]
    exact hle hn
  exact A1c.A131Concl_of_surjective hp hF _ S φ hφ rfl (hS p (Fact.out) hp)

theorem isCyclic_inf_centralizer_of_faithful {X P A : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hPX : P ≤ X) (hPp : IsPGroup p P) (hA2 : IsElemAbelian2 A) (hAX : A ≤ X)
    (hAn : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P) (hX : IsQuotientOfSQTKTC ↥X)
    (hfaith : ∀ a ∈ A, (∀ y ∈ P, a * y = y * a) → a = 1) {a : MulAut V} (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    IsCyclic ↥(P ⊓ Subgroup.centralizer ({a} : Set (MulAut V))) := by
  have h131 := a131_of_faithful hp hPX hPp hA2 hAX hAn hX hfaith
  set K := P ⊔ A with hK
  have haK : a ∈ K := (le_sup_right : A ≤ K) haA
  have hPK : P ≤ K := le_sup_left
  let ā : ↥K := ⟨a, haK⟩
  have hā2 : ā ^ 2 = 1 := Subtype.ext (hA2.2 a haA)
  have hT2 : IsPGroup 2 (Subgroup.zpowers ā) := A1c.isPGroup_two_zpowers hā2
  have hT1 : Subgroup.zpowers ā ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    exact ha1 (congrArg Subtype.val h)
  have hcyc := h131.1 (Subgroup.zpowers ā) hT2 hT1
  have hsub : (P ⊓ Subgroup.centralizer ({a} : Set (MulAut V))).subgroupOf K ≤
      CFSG.Open.pCore p ↥K ⊓ Subgroup.centralizer ((Subgroup.zpowers ā : Subgroup ↥K) : Set ↥K) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    refine ⟨subgroupOf_le_pCore hPp hAn (by rw [Subgroup.mem_subgroupOf]; exact hz.1),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute ā z := by
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_singleton_iff.mp hz.2)).symm
    exact (hc.zpow_left k).eq
  have hc1 : IsCyclic ↥((P ⊓ Subgroup.centralizer ({a} : Set (MulAut V))).subgroupOf K) :=
    isCyclic_of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective hsub)
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPK)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPK)).surjective

@[expose] noncomputable def oddFitting (X : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ (p : ℕ) (_ : p.Prime) (_ : p ≠ 2), pCoreOf p X

@[expose] noncomputable def fittingRes23 (X : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ (p : ℕ) (_ : p.Prime) (_ : p ≠ 2) (_ : p ≠ 3), pCoreOf p X

structure D214Hyp (X A : Subgroup (MulAut V)) (r : ℚ) : Prop where
  qhat : qhatOf X = (r : WithTop ℚ)
  mem : A ∈ QhatStar X
  noncyclic : ¬ IsCyclic ↥A
  faithful : ∀ a ∈ A, (∀ y ∈ oddFitting X, a * y = y * a) → a = 1
  comm_eq_top : commV (oddFitting X) = ⊤
  sqtk : IsQuotientOfSQTKTC ↥X

theorem one_lt_rk_of_not_isCyclic {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) (hnc : ¬ IsCyclic ↥A) : 1 < rk A := by
  by_contra hle
  have hpos := hA.rk_pos hA1
  have hrk : rk A = 1 := by omega
  have hcard : Nat.card A = 2 := by
    rw [card_eq_two_pow_of_isPGroup hA.isPGroup, hrk, pow_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hnc (isCyclic_of_prime_card hcard)

theorem D2_14_1 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (h : D214Hyp X A r) : ∀ y ∈ fittingRes23 X, ∀ a ∈ A, a * y = y * a := by
  obtain ⟨r', hr', -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec h.mem
  have hrk : 1 < rk A := one_lt_rk_of_not_isCyclic hA2.isElemAbelian2 hA2.ne_bot h.noncyclic
  have hcen : ∀ a ∈ A, fittingRes23 X ≤ Subgroup.centralizer ({a} : Set (MulAut V)) := by
    intro a ha
    refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => iSup_le fun hp3 => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_contra hne
    have : Fact p.Prime := ⟨hp⟩
    have hD : ⁅pCoreOf p X, A⁆ ≠ ⊥ :=
      commutator_ne_bot_iff.mpr ⟨y, hy, a, ha, fun e => hne e.symm⟩
    exact hp3 ((D2_13 hV h.qhat h.mem hp2 rfl hD).2.2.2.2 hrk).1
  intro y hy a ha
  exact ((Subgroup.mem_centralizer_singleton_iff).mp (hcen a ha hy)).symm

theorem faithful_pCore_three (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (h : D214Hyp X A r) :
    ∀ a ∈ A, (∀ y ∈ pCoreOf 3 X, a * y = y * a) → a = 1 := by
  intro a ha hc
  apply h.faithful a ha
  have hcen : oddFitting X ≤ Subgroup.centralizer ({a} : Set (MulAut V)) := by
    refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases h3 : p = 3
    · subst h3
      exact (hc y hy).symm
    · have hy' : y ∈ fittingRes23 X := Subgroup.mem_iSup_of_mem p
        (Subgroup.mem_iSup_of_mem hp (Subgroup.mem_iSup_of_mem hp2
          (Subgroup.mem_iSup_of_mem h3 hy)))
      exact (D2_14_1 hV h y hy' a ha).symm
  intro y hy
  exact ((Subgroup.mem_centralizer_singleton_iff).mp (hcen hy)).symm

theorem D2_14_4 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (h : D214Hyp X A r) : rk A = 2 := by
  obtain ⟨r', hr', -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec h.mem
  have hrk : 1 < rk A := one_lt_rk_of_not_isCyclic hA2.isElemAbelian2 hA2.ne_bot h.noncyclic
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h131 := a131_of_faithful (X := X) (P := pCoreOf 3 X) (A := A) (p := 3) (by norm_num)
    (pCoreOf_le 3 X) (pCoreOf_isPGroup 3 X) hA2.isElemAbelian2 hA2.le
    (fun a ha y hy => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X (hA2.le ha)) y).mp hy)
    h.sqtk (faithful_pCore_three hV h)
  have hle := h131.2.1
  set K := pCoreOf 3 X ⊔ A with hK
  have hAK : A ≤ K := le_sup_right
  have hE : IsElemAbelian 2 (A.subgroupOf K) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hA2.isElemAbelian2.1 _ a.2 _ b.2
    · apply Subtype.ext
      exact hA2.isElemAbelian2.2 _ hx
  have hcard : Nat.card ↥(A.subgroupOf K) = 2 ^ rk A := by
    rw [← card_eq_two_pow_of_isPGroup hA2.isElemAbelian2.isPGroup]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have := le_pRank Nat.prime_two (X := ⊤) le_top hE hcard
  omega

end CFSG.Quasithin
