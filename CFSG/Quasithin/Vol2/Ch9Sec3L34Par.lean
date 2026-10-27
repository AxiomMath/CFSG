module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34KGT
public import CFSG.Quasithin.Vol2.Ch9Lem933
public import CFSG.Quasithin.Vol2.Ch9Sec3VU
public import CFSG.Quasithin.Background.C41PfKG
public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfB
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CoprimeProduct
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Vol2.Ch9Sec3Field
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KG1
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Max
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Out
public import CFSG.Quasithin.Vol2.Ch9Sec3Typ
public import CFSG.Quasithin.Vol2.Ch9Sec3Vtx

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace L34P

variable {K : Subgroup G}

omit [Finite G] in
theorem quotConjHom_apply (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    C41Pf.quotConjHom K g (k : O2Q K) =
      ((⟨(g : G) * k * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 k).mp k.2⟩ : ↥K) :
        O2Q K) := rfl

omit [Finite G] in
theorem map_quotConjHom_eq {P : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) :
    ((P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map
        (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom =
      (P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨(g : G) * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg k).mp k.2⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp hgP k).mp (Subgroup.mem_subgroupOf.mp hk))
  · rintro _ ⟨k, hk, rfl⟩
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp k.2
      simpa using this
    have hkP : g⁻¹ * k * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgP) k).mp
        (Subgroup.mem_subgroupOf.mp hk)
      simpa using this
    refine ⟨((⟨g⁻¹ * k * g, hk'⟩ : ↥K) : O2Q K), ⟨⟨g⁻¹ * k * g, hk'⟩,
      Subgroup.mem_subgroupOf.mpr hkP, rfl⟩, ?_⟩
    show C41Pf.quotConjHom K ⟨g, hg⟩ ((⟨g⁻¹ * k * g, hk'⟩ : ↥K) : O2Q K) = _
    rw [quotConjHom_apply]
    congr 1
    apply Subtype.ext
    show g * (g⁻¹ * k * g) * g⁻¹ = (k : G)
    group

theorem map_R_cases {X : Type} [Group X] [Finite X] {S₀ R₂ R₃ : Subgroup X} (hne : R₂ ≠ R₃)
    (hR₂ : R₂ ≤ S₀) (hR₃ : R₃ ≤ S₀) (hE₂ : IsElemAbelian 2 R₂) (hE₃ : IsElemAbelian 2 R₃)
    (h₂ : Nat.card R₂ = 16) (h₃ : Nat.card R₃ = 16)
    (hEA : ∀ E : Subgroup X, E ≤ S₀ → IsElemAbelian 2 E → E ≤ R₂ ∨ E ≤ R₃) {φ : MulAut X}
    (hφ : S₀.map φ.toMonoidHom = S₀) :
    (R₂.map φ.toMonoidHom = R₂ ∧ R₃.map φ.toMonoidHom = R₃) ∨
      (R₂.map φ.toMonoidHom = R₃ ∧ R₃.map φ.toMonoidHom = R₂) := by
  have key : ∀ R : Subgroup X, R ≤ S₀ → IsElemAbelian 2 R → Nat.card R = 16 →
      R.map φ.toMonoidHom = R₂ ∨ R.map φ.toMonoidHom = R₃ := by
    intro R hR hE hc
    have hle : R.map φ.toMonoidHom ≤ S₀ := hφ ▸ Subgroup.map_mono hR
    have hc' : Nat.card (R.map φ.toMonoidHom) = 16 := by
      rw [Subgroup.card_map_of_injective φ.injective, hc]
    rcases hEA _ hle (CFSG.SectionRank.isElemAbelian_map hE φ.toMonoidHom) with h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hc', h₂]))
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hc', h₃]))
  have hinj : ∀ A B : Subgroup X, A.map φ.toMonoidHom = B.map φ.toMonoidHom → A = B :=
    fun A B h => Subgroup.map_injective φ.injective h
  rcases key R₂ hR₂ hE₂ h₂ with h2 | h2 <;> rcases key R₃ hR₃ hE₃ h₃ with h3 | h3
  · exact absurd (hinj _ _ (h2.trans h3.symm)) hne
  · exact Or.inl ⟨h2, h3⟩
  · exact Or.inr ⟨h2, h3⟩
  · exact absurd (hinj _ _ (h2.trans h3.symm)) hne

end L34P

namespace L34P

theorem map_conj_eq {X : Type} [Group X] {R₂ R₃ : Subgroup X} {φ δ : MulAut X}
    (hφ : R₂.map φ⁻¹.toMonoidHom = R₂ ∨ R₂.map φ⁻¹.toMonoidHom = R₃)
    (hδ₂ : R₂.map δ.toMonoidHom = R₂) (hδ₃ : R₃.map δ.toMonoidHom = R₃) :
    R₂.map (φ * δ * φ⁻¹).toMonoidHom = R₂ := by
  have hm : ∀ (a b : MulAut X) (R : Subgroup X),
      R.map (a * b).toMonoidHom = (R.map b.toMonoidHom).map a.toMonoidHom := by
    intro a b R
    rw [Subgroup.map_map]
    rfl
  have hback : (R₂.map φ⁻¹.toMonoidHom).map φ.toMonoidHom = R₂ := by
    rw [← hm, mul_inv_cancel]
    exact Subgroup.map_id R₂
  rw [hm, hm]
  rcases hφ with h | h
  · rw [h, hδ₂]
    rw [h] at hback
    exact hback
  · rw [h, hδ₃]
    rw [h] at hback
    exact hback

theorem map_pow_three {X : Type} [Group X] (φ : MulAut X) (R : Subgroup X) :
    R.map (φ ^ 3).toMonoidHom =
      ((R.map φ.toMonoidHom).map φ.toMonoidHom).map φ.toMonoidHom := by
  rw [pow_succ, pow_succ, pow_one, Subgroup.map_map, Subgroup.map_map]
  rfl

end L34P

namespace L34P

theorem map_mul_eq {X : Type} [Group X] (a b : MulAut X) (R : Subgroup X) :
    R.map (a * b).toMonoidHom = (R.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_inv_eq {X : Type} [Group X] {a : MulAut X} {R : Subgroup X}
    (h : R.map a.toMonoidHom = R) : R.map a⁻¹.toMonoidHom = R := by
  have h1 : (R.map a.toMonoidHom).map a⁻¹.toMonoidHom = R := by
    rw [← map_mul_eq, inv_mul_cancel]
    exact Subgroup.map_id R
  rwa [h] at h1

theorem exists_two_ne_one {X : Type} [Group X] [Finite X] {R : Subgroup X}
    (hR2 : ∀ r ∈ R, r ^ 2 = 1) (hR : 2 < Nat.card R) :
    ∃ r ∈ R, ∃ s ∈ R, r ≠ 1 ∧ s ≠ 1 ∧ r ≠ s := by
  have hne : R ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hR
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hnle : ¬ R ≤ Subgroup.zpowers r := fun h => by
    have h1 := Subgroup.card_le_of_le h
    rw [Nat.card_zpowers] at h1
    have h2 := orderOf_le_of_pow_eq_one two_pos (hR2 r hr)
    omega
  obtain ⟨s, hs, hsn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  refine ⟨r, hr, s, hs, hr1', fun h => hsn (h ▸ one_mem _), fun h => hsn ?_⟩
  rw [← h]
  exact Subgroup.mem_zpowers r

theorem oTwoUpper_normalizer_eq {X : Type} [Group X] [Finite X] {R : Subgroup X}
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (π : ↥(Subgroup.normalizer (R : Set X)) →* S) (hπ : Function.Surjective π)
    (hker : π.ker = R.subgroupOf (Subgroup.normalizer (R : Set X)))
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hR2 : ∃ r ∈ R, ∃ s ∈ R, r ≠ 1 ∧ s ≠ 1 ∧ r ≠ s)
    (htr : ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (R : Set X), n * r * n⁻¹ = s) :
    oTwoUpper (Subgroup.normalizer (R : Set X)) = Subgroup.normalizer (R : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oTwoUpper (Subgroup.normalizer (R : Set X)) with hO
  have hON : O ≤ Subgroup.normalizer (R : Set X) := oTwoUpper_le _
  have hRN : R ≤ Subgroup.normalizer (R : Set X) := Subgroup.le_normalizer
  have hNO : Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (O : Set X) :=
    le_normalizer_oTwoUpper _
  have hsplit : ∀ n ∈ Subgroup.normalizer (R : Set X), ∃ o ∈ O, o⁻¹ * n ∈ R := by
    have hO'n : (O.subgroupOf (Subgroup.normalizer (R : Set X))).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hNO g.2) x).mp hx
    have := hO'n.map π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((O.subgroupOf (Subgroup.normalizer (R : Set X))).map π) with h | h
    · exfalso
      refine H13.not_isPGroup_of_isSimpleGroup hS (p := 2) fun y => ?_
      obtain ⟨n, rfl⟩ := hπ y
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper _ n.2
      have hmem : π (n ^ 2 ^ k) ∈ (O.subgroupOf (Subgroup.normalizer (R : Set X))).map π :=
        ⟨n ^ 2 ^ k, Subgroup.mem_subgroupOf.mpr (by simpa using hk), rfl⟩
      rw [h, Subgroup.mem_bot, map_pow] at hmem
      exact ⟨k, hmem⟩
    · intro n hn
      have hmem : π ⟨n, hn⟩ ∈ (O.subgroupOf (Subgroup.normalizer (R : Set X))).map π := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨o, ho, hoe⟩ := hmem
      refine ⟨o, Subgroup.mem_subgroupOf.mp ho, ?_⟩
      have hk : o⁻¹ * ⟨n, hn⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hoe, inv_mul_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at hk
      simpa using hk
  have hRO : R ≤ O := by
    by_contra hRO
    have h1 : ∀ r ∈ R, r ∈ O → r = 1 := by
      intro r hr hrO
      by_contra hr1
      refine hRO fun s hs => ?_
      by_cases hs1 : s = 1
      · rw [hs1]
        exact O.one_mem
      obtain ⟨n, hn, rfl⟩ := htr r hr s hs hr1 hs1
      exact (Subgroup.mem_normalizer_iff.mp (hNO hn) r).mp hrO
    have h2 : ∀ o ∈ O, ∀ r ∈ R, o * r * o⁻¹ = r := by
      intro o ho r hr
      have hc1 : o * r * o⁻¹ * r⁻¹ ∈ R :=
        R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hON ho) r).mp hr) (R.inv_mem hr)
      have hc2 : o * r * o⁻¹ * r⁻¹ ∈ O := by
        have h3 : r * o⁻¹ * r⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hNO (hRN hr)) _).mp (O.inv_mem ho)
        have e : o * r * o⁻¹ * r⁻¹ = o * (r * o⁻¹ * r⁻¹) := by group
        rw [e]
        exact O.mul_mem ho h3
      have h4 := h1 _ hc1 hc2
      calc o * r * o⁻¹ = o * r * o⁻¹ * r⁻¹ * r := by group
        _ = r := by rw [h4, one_mul]
    obtain ⟨r, hr, s, hs, hr1, hs1, hrs⟩ := hR2
    obtain ⟨n, hn, hnrs⟩ := htr r hr s hs hr1 hs1
    obtain ⟨o, ho, hor⟩ := hsplit n hn
    have hcomm := hRc _ hor r hr
    have key : n * r * n⁻¹ = r :=
      calc n * r * n⁻¹ = o * (o⁻¹ * n * r) * (o⁻¹ * n)⁻¹ * o⁻¹ := by group
        _ = o * (r * (o⁻¹ * n)) * (o⁻¹ * n)⁻¹ * o⁻¹ := by rw [hcomm]
        _ = o * r * o⁻¹ := by group
        _ = r := h2 o ho r hr
    exact hrs (key.symm.trans hnrs)
  refine le_antisymm hON fun n hn => ?_
  obtain ⟨o, ho, hor⟩ := hsplit n hn
  have e : n = o * (o⁻¹ * n) := by group
  rw [e]
  exact O.mul_mem ho (hRO hor)

theorem not_normalizer_le {X : Type} [Group X] [Finite X] {R S₀ : Subgroup X}
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (π : ↥(Subgroup.normalizer (R : Set X)) →* S) (hπ : Function.Surjective π)
    (hker : π.ker = R.subgroupOf (Subgroup.normalizer (R : Set X)))
    (hS₀R : S₀ ≤ Subgroup.normalizer (R : Set X)) (hS₀2 : IsPGroup 2 S₀) (hS₀R' : ¬ S₀ ≤ R) :
    ¬ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (S₀ : Set X) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (S₀.subgroupOf (Subgroup.normalizer (R : Set X))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hle g.2) x).mp hx
  have := hn.map π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((S₀.subgroupOf (Subgroup.normalizer (R : Set X))).map π) with h | h
  · refine hS₀R' fun x hx => ?_
    have h1 : π ⟨x, hS₀R hx⟩ ∈ (S₀.subgroupOf (Subgroup.normalizer (R : Set X))).map π :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hS₀R hx⟩ : ↥(Subgroup.normalizer (R : Set X))) ∈ π.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  · apply H13.not_isPGroup_of_isSimpleGroup hS (p := 2)
    have h2 : IsPGroup 2 ↥((S₀.subgroupOf (Subgroup.normalizer (R : Set X))).map π) :=
      (hS₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀R).symm).map π
    rw [h] at h2
    exact h2.of_equiv Subgroup.topEquiv

variable {K : Subgroup G}

@[expose] def preN (K : Subgroup G) (R : Subgroup (O2Q K)) : Subgroup G :=
  ((Subgroup.normalizer (R : Set (O2Q K))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map
    K.subtype

@[expose] def preR (K : Subgroup G) (R : Subgroup (O2Q K)) : Subgroup G :=
  (R.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype

omit [Finite G] in
theorem mem_preN {R : Subgroup (O2Q K)} {x : G} :
    x ∈ preN K R ↔ ∃ hx : x ∈ K,
      ((⟨x, hx⟩ : ↥K) : O2Q K) ∈ Subgroup.normalizer (R : Set (O2Q K)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem mem_preR {R : Subgroup (O2Q K)} {x : G} :
    x ∈ preR K R ↔ ∃ hx : x ∈ K, ((⟨x, hx⟩ : ↥K) : O2Q K) ∈ R := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem preN_le (R : Subgroup (O2Q K)) : preN K R ≤ K := fun _ hx => (mem_preN.mp hx).1

omit [Finite G] in
theorem preR_le_preN (R : Subgroup (O2Q K)) : preR K R ≤ preN K R := fun _ hx => by
  obtain ⟨h1, h2⟩ := mem_preR.mp hx
  exact mem_preN.mpr ⟨h1, Subgroup.le_normalizer h2⟩

omit [Finite G] in
theorem isPGroup_preR {R : Subgroup (O2Q K)} (hR2 : IsPGroup 2 R) : IsPGroup 2 ↥(preR K R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (hR2.comap_of_ker_isPGroup _ ?_).map K.subtype
  rw [QuotientGroup.ker_mk']
  exact CFSG.pCore_isPGroup

omit [Finite G] in
theorem quotConjHom_eq_conj {k : G} (hk : k ∈ K) (hkN : k ∈ Subgroup.normalizer (K : Set G)) :
    C41Pf.quotConjHom K ⟨k, hkN⟩ = MulAut.conj (((⟨k, hk⟩ : ↥K)) : O2Q K) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [quotConjHom_apply, MulAut.conj_apply]
  rfl

omit [Finite G] in
theorem mem_normalizer_map_comap {Q : Subgroup (O2Q K)} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hQ : Q.map (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom = Q) :
    g ∈ Subgroup.normalizer (((Q.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype :
      Subgroup G) : Set G) := by
  have key : ∀ (h : G) (hh : h ∈ Subgroup.normalizer (K : Set G)),
      Q.map (C41Pf.quotConjHom K ⟨h, hh⟩).toMonoidHom = Q →
      ∀ x ∈ ((Q.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype : Subgroup G),
        h * x * h⁻¹ ∈ ((Q.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype :
          Subgroup G) := by
    rintro h hh hQh _ ⟨k, hk, rfl⟩
    refine ⟨⟨h * k * h⁻¹, (Subgroup.mem_normalizer_iff.mp hh k).mp k.2⟩, ?_, rfl⟩
    have h1 : C41Pf.quotConjHom K ⟨h, hh⟩ (k : O2Q K) ∈ Q := by
      rw [← hQh]
      exact ⟨_, hk, rfl⟩
    rw [quotConjHom_apply] at h1
    exact h1
  refine B6.mem_normalizer_of_forall_mem (key g hg hQ) fun x hx => ?_
  have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  have hQ' : Q.map (C41Pf.quotConjHom K ⟨g⁻¹, hg'⟩).toMonoidHom = Q := by
    have e : C41Pf.quotConjHom K ⟨g⁻¹, hg'⟩ = (C41Pf.quotConjHom K ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    exact map_inv_eq hQ
  simpa using key g⁻¹ hg' hQ' x hx

theorem map_normalizer_eq {X : Type} [Group X] {a : MulAut X} {R : Subgroup X}
    (hR : R.map a.toMonoidHom = R) :
    (Subgroup.normalizer (R : Set X)).map a.toMonoidHom = Subgroup.normalizer (R : Set X) := by
  have hφ : ∀ (a : MulAut X) (A : Subgroup X), A.map a.toMonoidHom = A →
      (Subgroup.normalizer (A : Set X)).map a.toMonoidHom ≤ Subgroup.normalizer (A : Set X) := by
    rintro a A hA _ ⟨y, hy, rfl⟩
    have hy : A.map (MulAut.conj y).toMonoidHom = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
    have e : (MulAut.conj (a y)).toMonoidHom =
        a.toMonoidHom.comp ((MulAut.conj y).toMonoidHom.comp a⁻¹.toMonoidHom) := by
      ext z
      simp [MulAut.conj_apply]
    have h1 : A.map (MulAut.conj (a y)).toMonoidHom = A := by
      rw [e, ← Subgroup.map_map, ← Subgroup.map_map, map_inv_eq hA, hy, hA]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  refine le_antisymm (hφ a R hR) fun y hy => ?_
  refine ⟨a⁻¹ y, hφ a⁻¹ R (map_inv_eq hR) ⟨y, hy, rfl⟩, ?_⟩
  show a (a⁻¹ y) = y
  simp

omit [Finite G] in
theorem mem_normalizer_preN {R : Subgroup (O2Q K)} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hR : R.map (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom = R) :
    g ∈ Subgroup.normalizer ((preN K R : Subgroup G) : Set G) :=
  mem_normalizer_map_comap hg (map_normalizer_eq hR)

omit [Finite G] in
theorem mem_normalizer_oTwoUpper_preN {R : Subgroup (O2Q K)} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hR : R.map (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom = R) :
    g ∈ Subgroup.normalizer ((oTwoUpper (preN K R) : Subgroup G) : Set G) :=
  normalizer_le_normalizer_oTwoUpper _ (mem_normalizer_preN hg hR)

omit [Finite G] in
theorem mem_normalizer_preR {R : Subgroup (O2Q K)} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hR : R.map (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom = R) :
    g ∈ Subgroup.normalizer ((preR K R : Subgroup G) : Set G) :=
  mem_normalizer_map_comap hg hR

omit [Finite G] in
theorem mem_normalizer_preR_of_mem {R : Subgroup (O2Q K)} {x : G} (hx : x ∈ preN K R) :
    x ∈ Subgroup.normalizer ((preR K R : Subgroup G) : Set G) := by
  obtain ⟨hxK, hxN⟩ := mem_preN.mp hx
  refine mem_normalizer_preR (Subgroup.le_normalizer hxK) ?_
  rw [quotConjHom_eq_conj hxK]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN

omit [Finite G] in
theorem mem_preN_of_mem {R : Subgroup (O2Q K)} {k : G} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (K : Set G))
    (hR : R.map (C41Pf.quotConjHom K ⟨k, hkN⟩).toMonoidHom = R) : k ∈ preN K R := by
  refine mem_preN.mpr ⟨hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← quotConjHom_eq_conj hk hkN]
  exact hR

theorem exists_mem_oTwoUpper_preN {R : Subgroup (O2Q K)}
    (hO : oTwoUpper (Subgroup.normalizer (R : Set (O2Q K))) =
      Subgroup.normalizer (R : Set (O2Q K)))
    {y : O2Q K} (hy : y ∈ Subgroup.normalizer (R : Set (O2Q K))) :
    ∃ k ∈ oTwoUpper (preN K R), ∃ hk : k ∈ K, ((⟨k, hk⟩ : ↥K) : O2Q K) = y := by
  set P := (Subgroup.normalizer (R : Set (O2Q K))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hP : P.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
      Subgroup.normalizer (R : Set (O2Q K)) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have himg : (oTwoUpper P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
      Subgroup.normalizer (R : Set (O2Q K)) := by
    rw [← oTwoUpper_map, hP, hO]
  have hK' : oTwoUpper (preN K R) = (oTwoUpper P).map K.subtype := oTwoUpper_map K.subtype P
  rw [← himg] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  refine ⟨k, ?_, k.2, rfl⟩
  rw [hK']
  exact ⟨k, hk, rfl⟩

theorem exists_mul_of_mem_preN {R : Subgroup (O2Q K)}
    (hO : oTwoUpper (Subgroup.normalizer (R : Set (O2Q K))) =
      Subgroup.normalizer (R : Set (O2Q K)))
    {x : G} (hx : x ∈ preN K R) :
    ∃ k ∈ oTwoUpper (preN K R), ∃ o ∈ pCoreOf 2 K, x = k * o := by
  obtain ⟨hxK, hxN⟩ := mem_preN.mp hx
  obtain ⟨k, hk, hkK, hke⟩ := exists_mem_oTwoUpper_preN hO hxN
  refine ⟨k, hk, k⁻¹ * x, ?_, by group⟩
  have h1 : (⟨k⁻¹ * x, K.mul_mem (K.inv_mem hkK) hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff]
    have e : (⟨k⁻¹ * x, K.mul_mem (K.inv_mem hkK) hxK⟩ : ↥K) = (⟨k, hkK⟩ : ↥K)⁻¹ * ⟨x, hxK⟩ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hke, inv_mul_cancel]
  exact (L34.mem_pCoreOf_iff_pCore _).mpr h1

end L34P

namespace L34P

variable {K : Subgroup G}

theorem nonempty_alt5 {R : Subgroup (O2Q K)} (hR2 : IsPGroup 2 R)
    (hO : oTwoUpper (Subgroup.normalizer (R : Set (O2Q K))) =
      Subgroup.normalizer (R : Set (O2Q K)))
    (π : ↥(Subgroup.normalizer (R : Set (O2Q K))) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (hπ : Function.Surjective π)
    (hker : π.ker = R.subgroupOf (Subgroup.normalizer (R : Set (O2Q K)))) :
    Nonempty (↥(oTwoUpper (preN K R)) ⧸ CFSG.pCore 2 ↥(oTwoUpper (preN K R)) ≃*
      alternatingGroup (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK'K : oTwoUpper (preN K R) ≤ K := (oTwoUpper_le _).trans (preN_le R)
  have hmem : ∀ x : ↥(oTwoUpper (preN K R)),
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hK'K)) x ∈
        Subgroup.normalizer (R : Set (O2Q K)) := fun x =>
    (mem_preN.mp (oTwoUpper_le _ x.2)).2
  set θ := ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hK'K)).codRestrict _
    hmem with hθ
  have hθs : Function.Surjective θ := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, hkK, hke⟩ := exists_mem_oTwoUpper_preN hO hy
    exact ⟨⟨k, hk⟩, Subtype.ext hke⟩
  have hc4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hc4)
  set e := (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    (GaloisField 2 2)).trans e5 with he
  set g := e.toMonoidHom.comp (π.comp θ) with hg
  have hgs : Function.Surjective g := e.surjective.comp (hπ.comp hθs)
  have hker' : IsPGroup 2 ↥g.ker := by
    rintro ⟨y, hy⟩
    have h1 : π (θ y) = 1 := e.injective (by rw [map_one]; exact hy)
    have h2 : θ y ∈ π.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    have hyR : ((y : ↥(oTwoUpper (preN K R))) : G) ∈ preR K R := mem_preR.mpr ⟨hK'K y.2, h2⟩
    obtain ⟨k, hk⟩ := isPGroup_preR hR2 ⟨_, hyR⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨Vol2Native.A312L.modO2EquivOfHom Vol2Native.A312L.Seven.alt5_nonabelian g hgs hker'⟩

omit [Finite G] in
theorem commutator_mem_pCoreOf {R : Subgroup (O2Q K)} (hR2 : IsPGroup 2 R) {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxK' : x ∈ Subgroup.normalizer ((oTwoUpper (preN K R) : Subgroup G) : Set G))
    (hx : ∀ y ∈ Subgroup.normalizer (R : Set (O2Q K)),
      C41Pf.quotConjHom K ⟨x, hxK⟩ y * y⁻¹ ∈ R)
    {k : G} (hk : k ∈ oTwoUpper (preN K R)) :
    k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 (oTwoUpper (preN K R)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK'R : oTwoUpper (preN K R) ≤ Subgroup.normalizer ((preR K R : Subgroup G) : Set G) :=
    fun k hk => mem_normalizer_preR_of_mem (oTwoUpper_le _ hk)
  have hle : oTwoUpper (preN K R) ⊓ preR K R ≤ pCoreOf 2 (oTwoUpper (preN K R)) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk, hK'R hk⟩)
      ((isPGroup_preR hR2).to_le inf_le_right)
  obtain ⟨hkK, hkN⟩ := mem_preN.mp (oTwoUpper_le _ hk)
  have hxkK : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxK k).mp hkK
  have hcK' : x * k * x⁻¹ * k⁻¹ ∈ oTwoUpper (preN K R) :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hxK' k).mp hk) (inv_mem hk)
  have hcR : x * k * x⁻¹ * k⁻¹ ∈ preR K R := by
    refine mem_preR.mpr ⟨K.mul_mem hxkK (K.inv_mem hkK), ?_⟩
    have h1 := hx _ hkN
    rw [quotConjHom_apply] at h1
    exact h1
  have h := (pCoreOf 2 (oTwoUpper (preN K R))).inv_mem (hle ⟨hcK', hcR⟩)
  have e : (x * k * x⁻¹ * k⁻¹)⁻¹ = k * x * k⁻¹ * x⁻¹ := by group
  rwa [e] at h

theorem isSylowTwoOf_inf {R : Subgroup (O2Q K)} (hTKs : IsSylowTwoOf (T ⊓ K) K)
    (hTKP : T ⊓ K ≤ preN K R) :
    IsSylowTwoOf (T ⊓ oTwoUpper (preN K R)) (oTwoUpper (preN K R)) := by
  have h1 : IsSylowTwoOf (T ⊓ K) (preN K R) := Lin2.isSylowTwoOf_of_le_of_le hTKs hTKP (preN_le R)
  have h2 := A4.isSylowTwoOf_inf_normal h1 (oTwoUpper_le _) (le_normalizer_oTwoUpper _)
  have e : T ⊓ K ⊓ oTwoUpper (preN K R) = T ⊓ oTwoUpper (preN K R) := by
    rw [inf_assoc, inf_eq_right.mpr ((oTwoUpper_le _).trans (preN_le R))]
  rwa [e] at h2

theorem mem_lFamily {R : Subgroup (O2Q K)} {T₁ : Subgroup G}
    (hT₁ : T₁ ≤ Subgroup.normalizer ((oTwoUpper (preN K R) : Subgroup G) : Set G))
    (hA : Nonempty (↥(oTwoUpper (preN K R)) ⧸ CFSG.pCore 2 ↥(oTwoUpper (preN K R)) ≃*
      alternatingGroup (Fin 5))) : oTwoUpper (preN K R) ∈ lFamily T₁ := by
  obtain ⟨e⟩ := hA
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hq : CFSG.IsQuasisimple
      (↥(oTwoUpper (preN K R)) ⧸ CFSG.pCore 2 ↥(oTwoUpper (preN K R))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup
        Vol2Native.A312L.Seven.alt5_nonabelian)
  show oTwoUpper (preN K R) ∈ cComp (oTwoUpper (preN K R) ⊔ T₁)
  refine H13.mem_cComp_of_quasisimple_quotient (H13.oTwoUpper_eq_top_of_isPGroup _) hq ?_
  refine A4.subnormal_of_normal le_sup_left ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer hT₁

theorem inf_normalizer_le {R : Subgroup (O2Q K)}
    (hO : oTwoUpper (Subgroup.normalizer (R : Set (O2Q K))) =
      Subgroup.normalizer (R : Set (O2Q K)))
    (hTKP : T ⊓ K ≤ preN K R) (hOT : pCoreOf 2 K ≤ T) :
    oTwoUpper (preN K R) ⊓
        Subgroup.normalizer ((T ⊓ oTwoUpper (preN K R) : Subgroup G) : Set G) ≤
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have hK'K : oTwoUpper (preN K R) ≤ K := (oTwoUpper_le _).trans (preN_le R)
  have heq : T ⊓ K = (T ⊓ oTwoUpper (preN K R)) ⊔ pCoreOf 2 K := by
    refine le_antisymm (fun x hx => ?_)
      (sup_le (inf_le_inf_left T hK'K) (le_inf hOT (pCoreOf_le 2 K)))
    obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_preN hO (hTKP hx)
    have hkT : k ∈ T := by
      have e : k = (k * o) * o⁻¹ := by group
      rw [e]
      exact T.mul_mem hx.1 (T.inv_mem (hOT ho))
    exact mul_mem (Subgroup.mem_sup_left ⟨hkT, hk⟩) (Subgroup.mem_sup_right ho)
  intro x hx
  refine ⟨hK'K hx.1, ?_⟩
  rw [heq]
  exact le_normalizer_sup_of_le_of_le inf_le_right
    (inf_le_left.trans (hK'K.trans (Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_pCoreOf 2 K)))) hx

omit [Finite G] in
theorem normalizer_le_of_lift {R : Subgroup (O2Q K)}
    (hlift : ∀ y ∈ Subgroup.normalizer (R : Set (O2Q K)), ∃ k : G, ∃ hk : k ∈ K,
      k ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ∧
        ((⟨k, hk⟩ : ↥K) : O2Q K) = y) :
    Subgroup.normalizer (R : Set (O2Q K)) ≤ Subgroup.normalizer
      ((((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) : Subgroup (O2Q K)) :
        Set (O2Q K)) := by
  intro y hy
  obtain ⟨k, hkK, hkN, rfl⟩ := hlift y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    ← quotConjHom_eq_conj hkK (Subgroup.le_normalizer hkK)]
  exact map_quotConjHom_eq _ hkN

end L34P

structure L34.Vertex (T L I B D K' : Subgroup G) : Prop where
  centralizer_V1 : K' ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
    ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)
  T1_le : T ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K' : Set G)
  D_le : D ≤ Subgroup.normalizer (K' : Set G)
  sylow : IsSylowTwoOf (T ⊓ K') K'
  alt5 : Nonempty (↥K' ⧸ CFSG.pCore 2 ↥K' ≃* alternatingGroup (Fin 5))
  r0 : T ⊓ K' ≤ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G))
  borel : K' ⊓ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G) ≤
    fsuM T L ⊓ Subgroup.normalizer (L : Set G)
  borelL : L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤
    Subgroup.normalizer (K' : Set G)
  lfam : K' ∈ lFamily (T ⊓ Subgroup.normalizer (L : Set G))
  B_le : B ≤ K'
  not_le_M : ¬ K' ≤ fsuM T L
  inf_M : K' ⊓ fsuM T L ≤ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G)
  pCore_le : pCoreOf 2 K' ≤ T
  other : ∃ d' ∈ D ⊓ L, d' ≠ 1 ∧ ⁅K', Subgroup.zpowers d'⁆ ≤ pCoreOf 2 K'

namespace Setup

namespace IsCoord

open CFSG.Quasithin.H Matrix

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem borelOf_L_le_r0 (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G))) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤
      D ⊔ ((T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G))) := by
  rintro x ⟨hxL, hxN⟩
  have hxL0 : x ∈ fsuL0 T L := S.L_le_L0 hxL
  have hψxL : ψ ⟨x, hxL0⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
    ⟨⟨x, hxL0⟩, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩
  have hut : ∀ g : SpecialLinearGroup (Fin 2) K, g * u1 K * g⁻¹ ∈ uni K → g ∈ utT K := by
    intro g hg
    obtain ⟨c, hc'⟩ := mem_uni_iff.mp hg
    have h1 := FactsFrob.isUT_of_conj_u1 (G := Matrix.SpecialLinearGroup.toGL g) (c := c) (by
      rw [← map_inv]
      show (g : Matrix (Fin 2) (Fin 2) K) * (u1 K : Matrix (Fin 2) (Fin 2) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
      rw [← hc', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul])
    exact h1
  have hconjT : ∀ l ∈ T ⊓ L, ∀ hl : l ∈ fsuL0 T L,
      ψ ⟨x * l * x⁻¹, (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hxL0 hl)
        ((fsuL0 T L).inv_mem hxL0)⟩ ∈ (uni K).prod (uni K) := by
    intro l hl hlL
    have h1 : x * l * x⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
    exact (hc.mem_T_iff h37c h38c _).mp h1.1
  have hψ : ψ ⟨x, hxL0⟩ ∈ (utT K).prod (utT K) := by
    rcases hc.map_L h37c h38c with hL | hL
    · rw [hL] at hψxL
      have hx2 : (ψ ⟨x, hxL0⟩).2 = 1 := hψxL
      obtain ⟨l, hl, hlL, hψl⟩ := hc.exists_mem_inf_L h37c h38c
        (γ := (u1 K, 1)) ⟨u1_mem, (uni K).one_mem⟩ (by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
      have h2 := hconjT l hl hlL
      have e : (⟨x * l * x⁻¹, (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hxL0 hlL)
          ((fsuL0 T L).inv_mem hxL0)⟩ : ↥(fsuL0 T L)) = ⟨x, hxL0⟩ * ⟨l, hlL⟩ * ⟨x, hxL0⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hψl] at h2
      refine ⟨hut _ h2.1, ?_⟩
      rw [hx2]
      exact (utT K).one_mem
    · rw [hL] at hψxL
      have hx1 : (ψ ⟨x, hxL0⟩).1 = 1 := hψxL
      obtain ⟨l, hl, hlL, hψl⟩ := hc.exists_mem_inf_L h37c h38c
        (γ := (1, u1 K)) ⟨(uni K).one_mem, u1_mem⟩ (by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
      have h2 := hconjT l hl hlL
      have e : (⟨x * l * x⁻¹, (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hxL0 hlL)
          ((fsuL0 T L).inv_mem hxL0)⟩ : ↥(fsuL0 T L)) = ⟨x, hxL0⟩ * ⟨l, hlL⟩ * ⟨x, hxL0⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hψl] at h2
      refine ⟨?_, hut _ h2.2⟩
      rw [hx1]
      exact (utT K).one_mem
  rw [← hc.map_normalizer h37c h38c] at hψ
  obtain ⟨m, hm, hψm⟩ := hψ
  have hq := hc.mem_Q_of_psi_eq_one h37c h38c (⟨x, hxL0⟩ * m⁻¹) (by
    rw [map_mul, map_inv, hψm, mul_inv_cancel])
  have hmN : (m : G) ∈ fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
    Subgroup.mem_subgroupOf.mp hm
  have hN₀ : fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤
      D ⊔ ((T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G))) :=
    (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall S.isSylowTwoOf_T_inf_L0_normalizer hD).trans
      (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
  have e : x = ((⟨x, hxL0⟩ * m⁻¹ : ↥(fsuL0 T L)) : G) * m := by simp
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_right hq)) (hN₀ hmN)

end IsCoord

end Setup

namespace Setup

variable (S : Setup T L I n)
include S

theorem exists_vertex_l34 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (hTorus : FactL34Torus)
    (h2 : n = 2) {H K B D : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T)
    (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K))
    (hB : Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) (hBK : B ≤ K)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hKV : K ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    ∃ K' : Subgroup G, L34.Vertex T L I B D K' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  have hK4 : Fintype.card F = 4 := by rw [hc.card, h2]; norm_num
  set M := fsuM T L with hM
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQ
  set R₀ := (T ⊓ fsuL0 T L) ⊔ Q with hR₀
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTM : T ≤ M := Setup.T_le_fsuM
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hTHs : IsSylowTwoOf T H := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
  have hKL' : IsPSL 3 2 2 (O2Q K) := L34.isPSL_of_star hKH hJ hKL
  have hDL0 : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hBD' : B ≤ D := hBD ▸ inf_le_left
  have hL0N := hc.L0_le_normalizer_L h37 h38 h37c h38c
  have hDL : D ≤ Subgroup.normalizer (L : Set G) := hDL0.trans hL0N
  have hR₀L : R₀ ≤ Subgroup.normalizer (L : Set G) := hc.r0_le_normalizer_L h37 h38 h37c h38c
  have hR₀T : R₀ ≤ T := sup_le inf_le_left inf_le_left
  have hR₀T₁ : R₀ ≤ T₁ := le_inf hR₀T hR₀L
  have hTKR : T ⊓ K ≤ R₀ := hc.inf_le_r0 h37c h38c h2 hD hdiag hTK hDK hKV (hBD ▸ hBTK)
  have hTKT₁ : T ⊓ K ≤ T₁ := hTKR.trans hR₀T₁
  have hDR₀ : D ≤ Subgroup.normalizer (R₀ : Set G) := hD.1.trans S.N0_le_normalizer_r0
  have hRK : R₀ ⊓ K = T ⊓ K :=
    le_antisymm (inf_le_inf_right K hR₀T) (le_inf hTKR inf_le_right)
  have hDTK : D ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := fun d hd => by
    rw [← hRK]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hDR₀ hd, hDK hd⟩
  have hTTK : T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTK ht⟩
  have hDT : ∀ x ∈ D, x ∈ T → x = 1 := fun x hx hxT =>
    eq_one_of_odd_of_mem hfsu.sylow.1 hxT (hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hx))
  have hψinj : ∀ x (hx : x ∈ D), ψ ⟨x, hDL0 hx⟩ = 1 → x = 1 := fun x hx hψx =>
    hc.eq_one_of_odd h37c h38c ⟨x, hDL0 hx⟩
      (hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hx)) hψx
  have hBX : B ≤ K ⊓ (H ⊓ M) := le_inf hBK hB.1
  have hBh' : Lin2.IsHallTwoPrimeOf B (K ⊓ (H ⊓ M)) := by
    obtain ⟨-, hBodd, k, hk⟩ := hB
    refine ⟨hBX, hBodd, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex B (K ⊓ (H ⊓ M)) (H ⊓ M) hBX inf_le_right
    have h3 : B.relIndex (K ⊓ (H ⊓ M)) ∣ 2 ^ k := by
      rw [← hk, ← h1]
      exact dvd_mul_right _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    exact ⟨j, hj⟩
  have hTKs' : IsSylowTwoOf (T ⊓ K) (K ⊓ (H ⊓ M)) :=
    Lin2.isSylowTwoOf_of_le_of_le hTKs
      (le_inf inf_le_right (le_inf (inf_le_left.trans hTH) (inf_le_left.trans hTM))) inf_le_left
  have hKHM : B ⊔ (T ⊓ K) = K ⊓ (H ⊓ M) := sup_eq_of_isHall_isSylow hBh' hTKs'
  have hKM' : K ⊓ M ≤ B ⊔ (T ⊓ K) := by
    rw [hKHM]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hKH) inf_le_right)
  have hKe : 2 ∣ Nat.card (oTwoQuot ↥K) := by
    show 2 ∣ Nat.card (↥K ⧸ CFSG.Open.pCore 2 ↥K)
    rw [show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160 from
      Ch1Four.card_of_isPSL_three_four hKL']
    norm_num
  have hNK : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ B ⊔ (T ⊓ K) := by
    rw [hKHM]
    exact le_inf inf_le_left (S.inf_normalizer_le' hH hHK hKc hTK hKe)
  have hBTKN : B ⊔ (T ⊓ K) ≤ M ⊓ Subgroup.normalizer (L : Set G) :=
    sup_le (le_inf ((hBD'.trans hDL0).trans Setup.L0_le_fsuM) (hBD'.trans hDL))
      (le_inf (inf_le_left.trans hTM) (hTKT₁.trans inf_le_right))
  set HD := K ⊔ D ⊔ T with hHD
  have hV₁HD : V₁ ≤ pCoreOf 2 HD := by
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((inf_le_left.trans S.fsuV_le_T).trans le_sup_right) ?_ (S.isPGroup_fsuV.to_le inf_le_left)
    refine sup_le (sup_le (fun k hk => Subgroup.centralizer_le_normalizer _ (hKV hk)) ?_)
      S.T_le_normalizer_V1
    exact fun d hd => S.mem_normalizer_V1_of_mem_N0 (hD.1 hd)
  have hHDO : pCoreOf 2 HD ≠ ⊥ := fun h0 => hc.V1_ne_bot (le_bot_iff.mp (h0 ▸ hV₁HD))
  set S₀ : Subgroup (O2Q K) := ((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    with hS₀
  have hP2 : IsPGroup 2 ↥((T ⊓ K).subgroupOf K) :=
    hTKs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hS₀2 : IsPGroup 2 S₀ := hP2.map _
  have hS₀i : ¬ 2 ∣ S₀.index := fun h2' =>
    hTKs.2.2 (h2'.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hS₀syl : IsSylowTwoOf S₀ ⊤ := by
    refine ⟨le_top, hS₀2, ?_⟩
    show ¬ 2 ∣ S₀.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hS₀i
  have hS₀64 : Nat.card S₀ = 64 := L34.card_eq_of_isPSL hKL' hS₀2 hS₀i
  obtain ⟨R₂, R₃, hne, hR, hEA⟩ := L34Br.l34ParData_of (L34.lieModel_of_isPSL hKL') hS₀syl
  obtain ⟨hR₂S, hR₂N, hR₂E, hR₂c, hρ₂, -⟩ := hR R₂ (Or.inl rfl)
  obtain ⟨hR₃S, hR₃N, hR₃E, hR₃c, hρ₃, -⟩ := hR R₃ (Or.inr rfl)
  have hcases : ∀ φ : MulAut (O2Q K), S₀.map φ.toMonoidHom = S₀ →
      (R₂.map φ.toMonoidHom = R₂ ∧ R₃.map φ.toMonoidHom = R₃) ∨
        (R₂.map φ.toMonoidHom = R₃ ∧ R₃.map φ.toMonoidHom = R₂) := fun φ hφ =>
    L34P.map_R_cases hne hR₂S hR₃S hR₂E hR₃E hR₂c hR₃c hEA hφ
  have hαS : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)),
      g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
        S₀.map (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom = S₀ := fun g hg hgP =>
    L34P.map_quotConjHom_eq hg hgP
  have hfaith : ∀ d ∈ D, ∀ hd : d ∈ Subgroup.normalizer (K : Set G),
      C41Pf.quotConjHom K ⟨d, hd⟩ = 1 → d = 1 := by
    intro d hdD hd h1
    have hcc : ∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro k hk
      have h3 := congrArg (fun φ : MulAut (O2Q K) => φ ((⟨k, hk⟩ : ↥K) : O2Q K)) h1
      simp only [MulAut.one_apply] at h3
      rw [L34P.quotConjHom_apply, QuotientGroup.eq_iff_div_mem, ← L34.mem_pCoreOf_iff_pCore,
        div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h3
      exact h3
    have hodd : Odd (orderOf d) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hdD)
    by_cases hdK : d ∈ K
    · exact eq_one_of_odd_of_mem (pCoreOf_isPGroup 2 K)
        (L34.mem_pCoreOf_of_centralizes hKL' hdK hcc) hodd
    · exfalso
      have hd3 : d ^ 3 = 1 := hc.pow_three_eq_one h37c h38c h2 hD hdiag hdD
      have hr := L34.three_le_pRank_of_centralizes hKL' hd (by rw [hd3]; exact one_mem _) hdK
        hcc
      have hle : K ⊔ Subgroup.zpowers d ≤ HD :=
        sup_le (le_sup_left.trans le_sup_left)
          (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_right hdD)))
      have h4 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle
      have h5 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hfsu.qtke hHDO Nat.prime_three
        (by norm_num)
      omega
  have hD9 : Nat.card D = 9 := by
    have hinj : Function.Injective (ψ.comp (D.subgroupOf (fsuL0 T L)).subtype) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨⟨x, hxL⟩, hx⟩ h1
      have hxD : x ∈ D := Subgroup.mem_subgroupOf.mp hx
      have h3 := hψinj x hxD h1
      exact Subtype.ext (Subtype.ext h3)
    have hrange : (ψ.comp (D.subgroupOf (fsuL0 T L)).subtype).range =
        (D.subgroupOf (fsuL0 T L)).map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    calc Nat.card D = Nat.card (D.subgroupOf (fsuL0 T L)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL0).toEquiv).symm
      _ = Nat.card (ψ.comp (D.subgroupOf (fsuL0 T L)).subtype).range :=
          Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      _ = 9 := by
          rw [hrange, hdiag, Nat.card_congr ((diagT F).prodEquiv (diagT F)).toEquiv,
            Nat.card_prod, card_diagT, hc.natCard, h2]
          norm_num
  set E : Subgroup (MulAut (O2Q K)) :=
    (D.subgroupOf (Subgroup.normalizer (K : Set G))).map (C41Pf.quotConjHom K) with hE
  have hE9 : Nat.card E = 9 := by
    have hinj : Function.Injective ((C41Pf.quotConjHom K).comp
        (D.subgroupOf (Subgroup.normalizer (K : Set G))).subtype) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨⟨x, hxN⟩, hx⟩ h1
      exact Subtype.ext (Subtype.ext (hfaith x (Subgroup.mem_subgroupOf.mp hx) hxN h1))
    have hrange : ((C41Pf.quotConjHom K).comp
        (D.subgroupOf (Subgroup.normalizer (K : Set G))).subtype).range = E := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hD9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  have hES : ∀ x ∈ E, S₀.map (x : MulAut (O2Q K)).toMonoidHom = S₀ := by
    rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
    exact hαS d hdN (hDTK (Subgroup.mem_subgroupOf.mp hd))
  obtain ⟨hTa, hTb⟩ := hTorus (O2Q K) hKL' S₀ hS₀2 hS₀64 E hE9 hES

  have hαconj : ∀ (a b : G) (ha : a ∈ Subgroup.normalizer (K : Set G))
      (hb : b ∈ Subgroup.normalizer (K : Set G)),
      C41Pf.quotConjHom K ⟨a, ha⟩ * C41Pf.quotConjHom K ⟨b, hb⟩ *
          (C41Pf.quotConjHom K ⟨a, ha⟩)⁻¹ =
        C41Pf.quotConjHom K ⟨a * b * a⁻¹, mul_mem (mul_mem ha hb) (inv_mem ha)⟩ := by
    intro a b ha hb
    rw [← map_inv, ← map_mul, ← map_mul]
    try rfl
  have hDfix : ∀ d ∈ D, ∀ hd : d ∈ Subgroup.normalizer (K : Set G),
      R₂.map (C41Pf.quotConjHom K ⟨d, hd⟩).toMonoidHom = R₂ ∧
        R₃.map (C41Pf.quotConjHom K ⟨d, hd⟩).toMonoidHom = R₃ := by
    intro d hdD hd
    rcases hcases _ (hαS d hd (hDTK hdD)) with h | h
    · exact h
    · exfalso
      have hd3 : d ^ 3 = 1 := hc.pow_three_eq_one h37c h38c h2 hD hdiag hdD
      have h3 : (C41Pf.quotConjHom K ⟨d, hd⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨d, hd⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
          Subtype.ext (by simpa using hd3)
        rw [this, map_one]
      have h4 := L34P.map_pow_three (C41Pf.quotConjHom K ⟨d, hd⟩) R₂
      rw [h3, h.1, h.2, h.1] at h4
      exact hne ((Subgroup.map_id R₂).symm.trans h4)
  have hψeq : ∀ x ∈ D, ∀ y ∈ D, ∀ (hx : x ∈ fsuL0 T L) (hy : y ∈ fsuL0 T L),
      ψ ⟨x, hx⟩ = ψ ⟨y, hy⟩ → x = y := by
    intro x hx y hy hxL hyL h
    have hxy : x * y⁻¹ ∈ D := D.mul_mem hx (D.inv_mem hy)
    have h1 := hψinj (x * y⁻¹) hxy (by
      have e' : (⟨x * y⁻¹, hDL0 hxy⟩ : ↥(fsuL0 T L)) = ⟨x, hxL⟩ * ⟨y, hyL⟩⁻¹ := rfl
      rw [e', map_mul, map_inv, h, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  have hU3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hK4]
  have huni : ∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set G) →
      s ∈ Subgroup.normalizer (D : Set G) →
      (∀ d ∈ D, s * d * s⁻¹ = d) ∨ (∀ d ∈ D, s * d * s⁻¹ = d⁻¹) := by
    intro s hsT hsL hsD
    obtain ⟨A, B', τ, hA, hB', hform⟩ := hc.exists_form_ut hsT
    have hns : bar e ⟨s, S.hMN (Setup.T_le_fsuM hsT)⟩ =
        CFSG.Quasithin.H.Om4.lr A B' * CFSG.Quasithin.H.Om4.frM τ := by
      rcases hform with hf | hf
      · exact hf
      · exact absurd hsL (hc.not_mem_normalizer_L_of_swap h37c h38c (Setup.T_le_fsuM hsT) hf)
    have hconj : ∀ d ∈ D, ∃ a b : Fˣ, ∃ hdL : d ∈ fsuL0 T L,
        ψ ⟨d, hdL⟩ = (diagOf a, diagOf b) ∧ ∃ d' ∈ D, ∃ hd'L : d' ∈ fsuL0 T L,
          ψ ⟨d', hd'L⟩ =
            (diagOf (Units.map τ.toMonoidHom a), diagOf (Units.map τ.toMonoidHom b)) ∧
          s * d * s⁻¹ = d' := by
      intro d hd
      obtain ⟨a, b, hab⟩ := IsCoord.exists_diag_of_mem hdiag hd (hDL0 hd)
      obtain ⟨d', hd'D, hd'L, hψd', hmem⟩ :=
        hc.conj_diag_ns h37c h38c hdiag hsT hA hB' hns (hDL0 hd) hab
      have hsd : s * d * s⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hsD d).mp hd
      exact ⟨a, b, hDL0 hd, hab, d', hd'D, hd'L, hψd',
        mul_inv_eq_one.mp (hDT _ (D.mul_mem hsd (D.inv_mem hd'D)) hmem)⟩
    by_cases hτ : τ = 1
    · left
      intro d hd
      obtain ⟨a, b, hdL, hab, d', hd'D, hd'L, hψd', hsd⟩ := hconj d hd
      rw [hsd]
      refine hψeq d' hd'D d hd hd'L hdL ?_
      rw [hψd', hab, hτ]
      try rfl
    · right
      have hinv : ∀ a : Fˣ, Units.map τ.toMonoidHom a = a⁻¹ := by
        intro a
        have h3 : a ^ 3 = 1 := by
          rw [← hU3]
          exact pow_card_eq_one'
        apply Units.ext
        rw [Units.coe_map]
        show τ (a : F) = ((a⁻¹ : Fˣ) : F)
        rw [frob_of_ne_one hK4 hτ, ← Units.val_pow_eq_pow_val]
        congr 1
        rw [eq_inv_iff_mul_eq_one, ← pow_succ]
        exact h3
      intro d hd
      obtain ⟨a, b, hdL, hab, d', hd'D, hd'L, hψd', hsd⟩ := hconj d hd
      rw [hsd]
      refine hψeq d' hd'D d⁻¹ (D.inv_mem hd) hd'L ((fsuL0 T L).inv_mem hdL) ?_
      have e' : (⟨d⁻¹, (fsuL0 T L).inv_mem hdL⟩ : ↥(fsuL0 T L)) = ⟨d, hdL⟩⁻¹ := rfl
      rw [hψd', e', map_inv, hab, hinv, hinv, Prod.inv_mk, diagOf_inv, diagOf_inv]
  set P : Subgroup G := ((MulAction.stabilizer (MulAut (O2Q K)) R₂).comap
    (C41Pf.quotConjHom K)).map (Subgroup.normalizer (K : Set G)).subtype with hPdef
  have hmemP : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)),
      R₂.map (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom = R₂ → g ∈ P :=
    fun g hg h => ⟨⟨g, hg⟩, h, rfl⟩
  have hofP : ∀ g ∈ P, ∃ hg : g ∈ Subgroup.normalizer (K : Set G),
      R₂.map (C41Pf.quotConjHom K ⟨g, hg⟩).toMonoidHom = R₂ := by
    rintro _ ⟨⟨g, hg⟩, h, rfl⟩
    exact ⟨hg, h⟩
  have hTL0 := S.isSylowTwoOf_T_inf_L0_normalizer
  have hsolv : Group.IsSolvable ↥(T ⊓ fsuL0 T L) := by
    have := hTL0.2.1.isNilpotent
    infer_instance
  have hcop : (Nat.card D).Coprime (Nat.card ↥(T ⊓ fsuL0 T L)) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hTL0.2.1
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hD.2.1)
  have hdec := CFSG.LocalAnalysis.EvenBN.TwoF4.inf_centralizer_sup_commutator_eq
    (hD.1.trans inf_le_right) hsolv hcop
  have hTL0P : T ⊓ fsuL0 T L ≤ P := by
    rw [← hdec]
    refine sup_le ?_ ?_
    · rintro c ⟨hcTL, hcC⟩
      have hcT : c ∈ T := hcTL.1
      have hcN : c ∈ Subgroup.normalizer (K : Set G) := hTK hcT
      have hcD : ∀ d ∈ D, c * d * c⁻¹ = d := fun d hd => by
        have h1 := Subgroup.mem_centralizer_iff.mp hcC d hd
        calc c * d * c⁻¹ = d * c * c⁻¹ := by rw [h1]
          _ = d := by group
      have hcent : ∀ x ∈ E, C41Pf.quotConjHom K ⟨c, hcN⟩ * x *
          (C41Pf.quotConjHom K ⟨c, hcN⟩)⁻¹ = x := by
        rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
        rw [hαconj c d hcN hdN]
        congr 1
        exact Subtype.ext (hcD d (Subgroup.mem_subgroupOf.mp hd))
      exact hmemP c hcN (hTa _ (hαS c hcN (hTTK hcT)) (fun x hx => by rw [hcent x hx]; exact hx)
        (Or.inl hcent) R₂ hR₂S hR₂E hR₂c)
    · rw [Subgroup.commutator_le]
      intro y hy d hd
      have hyN : y ∈ Subgroup.normalizer (K : Set G) := hTK hy.1
      have hdN : d ∈ Subgroup.normalizer (K : Set G) := hDK hd
      have h1 : y * d * y⁻¹ ∈ P := by
        refine hmemP _ (mul_mem (mul_mem hyN hdN) (inv_mem hyN)) ?_
        rw [← hαconj y d hyN hdN]
        have hφ : R₂.map (C41Pf.quotConjHom K ⟨y, hyN⟩)⁻¹.toMonoidHom = R₂ ∨
            R₂.map (C41Pf.quotConjHom K ⟨y, hyN⟩)⁻¹.toMonoidHom = R₃ := by
          rw [← map_inv]
          rcases hcases _ (hαS y⁻¹ (inv_mem hyN) (hTTK (T.inv_mem hy.1))) with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1
        exact L34P.map_conj_eq hφ (hDfix d hd hdN).1 (hDfix d hd hdN).2
      have h2 : d⁻¹ ∈ P := P.inv_mem (hmemP d hdN (hDfix d hd hdN).1)
      rw [commutatorElement_def]
      exact P.mul_mem h1 h2
  have hT₁P : T₁ ≤ P := by
    intro t ht
    obtain ⟨m, hm, hmt⟩ := S.exists_mul_mem_normalizer_hall hD ht.1
    have hmT₁ : m ∈ T₁ := ⟨hm.1, hL0N hm.2⟩
    have hs : m * t ∈ T₁ := T₁.mul_mem hmT₁ ht
    have hsN : m * t ∈ Subgroup.normalizer (K : Set G) := hTK hs.1
    have hunif : (∀ x ∈ E, C41Pf.quotConjHom K ⟨m * t, hsN⟩ * x *
          (C41Pf.quotConjHom K ⟨m * t, hsN⟩)⁻¹ = x) ∨
        (∀ x ∈ E, C41Pf.quotConjHom K ⟨m * t, hsN⟩ * x *
          (C41Pf.quotConjHom K ⟨m * t, hsN⟩)⁻¹ = x⁻¹) := by
      rcases huni (m * t) hs.1 hs.2 hmt with h | h
      · left
        rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
        rw [hαconj _ d hsN hdN]
        congr 1
        exact Subtype.ext (h d (Subgroup.mem_subgroupOf.mp hd))
      · right
        rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
        rw [hαconj _ d hsN hdN, ← map_inv]
        congr 1
        exact Subtype.ext (h d (Subgroup.mem_subgroupOf.mp hd))
    have hsP : m * t ∈ P := by
      refine hmemP _ hsN (hTa _ (hαS _ hsN (hTTK hs.1)) (fun x hx => ?_) hunif R₂ hR₂S hR₂E
        hR₂c)
      rcases hunif with h | h
      · rw [h x hx]
        exact hx
      · rw [h x hx]
        exact E.inv_mem hx
    have e' : t = m⁻¹ * (m * t) := by group
    rw [e']
    exact P.mul_mem (P.inv_mem (hTL0P hm)) hsP
  have hT₁fix : ∀ t ∈ T₁, ∀ ht : t ∈ Subgroup.normalizer (K : Set G),
      R₂.map (C41Pf.quotConjHom K ⟨t, ht⟩).toMonoidHom = R₂ ∧
        R₃.map (C41Pf.quotConjHom K ⟨t, ht⟩).toMonoidHom = R₃ := by
    intro t ht htN
    obtain ⟨hg, h⟩ := hofP t (hT₁P ht)
    rcases hcases _ (hαS t htN (hTTK ht.1)) with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h'.1) hne

  have hc4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hc4)
  set eP := (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    (GaloisField 2 2)).trans e5 with heP
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    eP.isSimpleGroup
  have hPnab : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := Vol2Native.A312L.Seven.alt5_nonabelian
    refine ⟨eP.symm a, eP.symm b, fun h => hab ?_⟩
    have h1 := congrArg eP h
    simpa using h1
  have hrad : ∀ R : Subgroup (O2Q K), (R = R₂ ∨ R = R₃) →
      oTwoUpper (Subgroup.normalizer (R : Set (O2Q K))) =
        Subgroup.normalizer (R : Set (O2Q K)) := by
    intro R hR'
    obtain ⟨-, -, hRE, hRc, ⟨π, hπ, hker⟩, htr⟩ := hR R hR'
    refine L34P.oTwoUpper_normalizer_eq hPnab π hπ hker (fun a ha b hb => ?_)
      (L34P.exists_two_ne_one (fun r hr => hRE.2 r hr) (by rw [hRc]; norm_num)) htr
    exact congrArg Subtype.val (hRE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hTKpre : ∀ R : Subgroup (O2Q K), (R = R₂ ∨ R = R₃) → T ⊓ K ≤ L34P.preN K R := by
    intro R hR' x hx
    obtain ⟨-, hRN, -⟩ := hR R hR'
    exact L34P.mem_preN.mpr ⟨hx.2, hRN (Subgroup.le_normalizer
      ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)⟩
  have hmove : ∃ t ∈ T, ∃ ht : t ∈ Subgroup.normalizer (K : Set G),
      R₂.map (C41Pf.quotConjHom K ⟨t, ht⟩).toMonoidHom ≠ R₂ := by
    by_contra hall
    push Not at hall
    obtain ⟨π₂, hπ₂, hker₂⟩ := hρ₂
    have hTP₂ : T ≤ Subgroup.normalizer ((L34P.preN K R₂ : Subgroup G) : Set G) := fun t ht =>
      L34P.mem_normalizer_preN (hTK ht) (hall t ht (hTK ht))
    have hR₂2 : IsPGroup 2 R₂ := fun r => ⟨1, Subtype.ext (by simpa using hR₂E.2 r r.2)⟩
    have hYH : L34P.preN K R₂ ⊔ T ≤ H := sup_le ((L34P.preN_le R₂).trans hKH) hTH
    have hRY : L34P.preR K R₂ ≤ pCoreOf 2 (L34P.preN K R₂ ⊔ T) := by
      refine le_pCoreOf_of_le_normalizer 2 ((L34P.preR_le_preN R₂).trans le_sup_left) ?_
        (L34P.isPGroup_preR hR₂2)
      exact sup_le (fun x hx => L34P.mem_normalizer_preR_of_mem hx)
        (fun t ht => L34P.mem_normalizer_preR (hTK ht) (hall t ht (hTK ht)))
    have hYO : pCoreOf 2 (L34P.preN K R₂ ⊔ T) ≠ ⊥ := by
      intro h0
      obtain ⟨r, hr, -, -, hr1, -, -⟩ :=
        L34P.exists_two_ne_one (fun r hr => hR₂E.2 r hr) (by rw [hR₂c]; norm_num)
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) r
      have h1 := hRY (L34P.mem_preR.mpr ⟨k.2, hr⟩)
      rw [h0, Subgroup.mem_bot] at h1
      apply hr1
      have hk1 : k = 1 := Subtype.ext h1
      rw [hk1, map_one]
    have hYM : ¬ L34P.preN K R₂ ⊔ T ≤ M := by
      intro hYM
      have hP₂N : L34P.preN K R₂ ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
        fun x hx => (sup_le hBTK Subgroup.le_normalizer)
          (hKM' ⟨L34P.preN_le R₂ hx, hYM (Subgroup.mem_sup_left hx)⟩)
      refine L34P.not_normalizer_le hPnab π₂ hπ₂ hker₂ (Subgroup.le_normalizer.trans hR₂N) hS₀2
        (fun hle => ?_) (L34P.normalizer_le_of_lift fun y hy => ?_)
      · have h1 := Subgroup.card_le_of_le hle
        rw [hS₀64, hR₂c] at h1
        norm_num at h1
      · obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
        exact ⟨k, k.2, hP₂N (L34P.mem_preN.mpr ⟨k.2, hy⟩), rfl⟩
    have hYeq : L34P.preN K R₂ ⊔ T = H :=
      hH.2.2 (L34P.preN K R₂ ⊔ T) ⟨le_sup_right, hYO⟩ hYH hYM
    have hKP : K ≤ L34P.preN K R₂ := by
      intro k hk
      have hkY : k ∈ ((L34P.preN K R₂ ⊔ T : Subgroup G) : Set G) := by
        rw [SetLike.mem_coe, hYeq]
        exact hKH hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTP₂] at hkY
      obtain ⟨p, hp, t, ht, rfl⟩ := hkY
      have htK : t ∈ K := by
        have e' : t = p⁻¹ * (p * t) := by group
        rw [e']
        exact K.mul_mem (K.inv_mem (L34P.preN_le R₂ hp)) hk
      exact (L34P.preN K R₂).mul_mem hp (hTKpre R₂ (Or.inl rfl) ⟨ht, htK⟩)
    have hsimp : IsSimpleGroup (O2Q K) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hKL').2
    have hnorm : R₂.Normal := by
      refine ⟨fun r hr y => ?_⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
      obtain ⟨hk', h⟩ := L34P.mem_preN.mp (hKP k.2)
      exact (Subgroup.mem_normalizer_iff.mp h r).mp hr
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R₂ with h | h
    · rw [h, Subgroup.card_bot] at hR₂c
      norm_num at hR₂c
    · rw [h, Subgroup.card_top, Ch1Four.card_of_isPSL_three_four hKL'] at hR₂c
      norm_num at hR₂c
  obtain ⟨t₀, ht₀T, ht₀N, ht₀m⟩ := hmove
  obtain ⟨m, hm, hmt⟩ := S.exists_mul_mem_normalizer_hall hD ht₀T
  have htT : m * t₀ ∈ T := T.mul_mem hm.1 ht₀T
  have htN : m * t₀ ∈ Subgroup.normalizer (K : Set G) := hTK htT
  have hmT₁ : m ∈ T₁ := ⟨hm.1, hL0N hm.2⟩
  have hmN : m ∈ Subgroup.normalizer (K : Set G) := hTK hm.1
  have hswap₀ : R₂.map (C41Pf.quotConjHom K ⟨t₀, ht₀N⟩).toMonoidHom = R₃ := by
    rcases hcases _ (hαS t₀ ht₀N (hTTK ht₀T)) with h | h
    · exact absurd h.1 ht₀m
    · exact h.1
  have htm : R₂.map (C41Pf.quotConjHom K ⟨m * t₀, htN⟩).toMonoidHom = R₃ := by
    have e' : C41Pf.quotConjHom K ⟨m * t₀, htN⟩ =
        C41Pf.quotConjHom K ⟨m, hmN⟩ * C41Pf.quotConjHom K ⟨t₀, ht₀N⟩ := by
      rw [← map_mul]
      try rfl
    rw [e', L34P.map_mul_eq, hswap₀, (hT₁fix m hmT₁ hmN).2]
  have htm' : R₂.map (C41Pf.quotConjHom K ⟨m * t₀, htN⟩).toMonoidHom ≠ R₂ := by
    rw [htm]
    exact fun h => hne h.symm
  have htL : m * t₀ ∉ Subgroup.normalizer (L : Set G) := fun h =>
    htm' (hT₁fix _ ⟨htT, h⟩ htN).1
  obtain ⟨A, B', τ, hA, hB', hform⟩ := hc.exists_form_ut htT
  have hswap : bar e ⟨m * t₀, S.hMN (Setup.T_le_fsuM htT)⟩ =
      CFSG.Quasithin.H.Om4.lr A B' * CFSG.Quasithin.H.Om4.frM τ * CFSG.Quasithin.H.Om4.trM := by
    rcases hform with hf | hf
    · exact absurd (hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c (Setup.T_le_fsuM htT) hf) htL
    · exact hf
  have : Nontrivial Fˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Fˣ)
  have hdg1 : diagOf (1 : Fˣ) = 1 := by rw [← diagHom_apply, map_one]
  have hdgne : ∀ c : Fˣ, c ≠ 1 → diagOf c ≠ 1 := by
    intro c hc1 h
    have h3 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [coe_diagOf] at h3
    exact hc1 (Units.ext (by simpa using h3))
  have hτω : Units.map τ.toMonoidHom ω ≠ 1 := fun h1 => hω (by
    have h2 := congrArg Units.val h1
    rw [Units.coe_map, Units.val_one] at h2
    exact Units.ext (by simpa using τ.injective (h2.trans (map_one τ).symm)))
  have hd' : ∃ d' ∈ D, ∃ hd'L0 : d' ∈ fsuL0 T L, d' ∈ L ∧ d' ≠ 1 ∧
      ∃ d'' ∈ D, ∃ hd''L : d'' ∈ fsuL0 T L, (m * t₀) * d' * (m * t₀)⁻¹ = d'' ∧
        ∀ j : ℤ, ψ ⟨d'', hd''L⟩ ≠ ψ ⟨d', hd'L0⟩ ^ j := by
    have htd : ∀ d ∈ D, (m * t₀) * d * (m * t₀)⁻¹ ∈ D := fun d hd =>
      (Subgroup.mem_normalizer_iff.mp hmt d).mp hd
    rcases hc.map_L h37c h38c with hL | hL
    · obtain ⟨d', hd'D, hd'L0, hψd'⟩ := IsCoord.exists_mem_of_diag hdiag ω 1
      have hd'L : d' ∈ L := hc.mem_L_of_mem_D h37 h38 h37c h38c hD hd'D (by
        rw [hL]
        show (ψ ⟨d', _⟩).2 = 1
        rw [hψd']
        exact hdg1)
      obtain ⟨d'', hd''D, hd''L, hψd'', hmem⟩ :=
        hc.conj_diag_swap h37c h38c hdiag htT hA hB' hswap hd'L0 hψd'
      refine ⟨d', hd'D, hd'L0, hd'L, fun h1 => ?_, d'', hd''D, hd''L,
        mul_inv_eq_one.mp (hDT _ (D.mul_mem (htd d' hd'D) (D.inv_mem hd''D)) hmem),
        fun j hj => ?_⟩
      · have h0 : (⟨d', hd'L0⟩ : ↥(fsuL0 T L)) = 1 := Subtype.ext h1
        rw [h0, map_one] at hψd'
        exact hdgne ω hω (congrArg Prod.fst hψd').symm
      · rw [hψd'', hψd'] at hj
        have h2 := congrArg Prod.snd hj
        simp only [Prod.pow_snd, hdg1, one_zpow] at h2
        exact hdgne _ hτω h2
    · obtain ⟨d', hd'D, hd'L0, hψd'⟩ := IsCoord.exists_mem_of_diag hdiag 1 ω
      have hd'L : d' ∈ L := hc.mem_L_of_mem_D h37 h38 h37c h38c hD hd'D (by
        rw [hL]
        show (ψ ⟨d', _⟩).1 = 1
        rw [hψd']
        exact hdg1)
      obtain ⟨d'', hd''D, hd''L, hψd'', hmem⟩ :=
        hc.conj_diag_swap h37c h38c hdiag htT hA hB' hswap hd'L0 hψd'
      refine ⟨d', hd'D, hd'L0, hd'L, fun h1 => ?_, d'', hd''D, hd''L,
        mul_inv_eq_one.mp (hDT _ (D.mul_mem (htd d' hd'D) (D.inv_mem hd''D)) hmem),
        fun j hj => ?_⟩
      · have h0 : (⟨d', hd'L0⟩ : ↥(fsuL0 T L)) = 1 := Subtype.ext h1
        rw [h0, map_one] at hψd'
        exact hdgne ω hω (congrArg Prod.snd hψd').symm
      · rw [hψd'', hψd'] at hj
        have h2 := congrArg Prod.fst hj
        simp only [Prod.pow_fst, hdg1, one_zpow] at h2
        exact hdgne _ hτω h2
  obtain ⟨d', hd'D, hd'L0, hd'L, hd'1, d'', hd''D, hd''L, htd', hψne⟩ := hd'
  have hd'N : d' ∈ Subgroup.normalizer (K : Set G) := hDK hd'D
  set φd := C41Pf.quotConjHom K ⟨d', hd'N⟩ with hφd
  have hτE : Subgroup.zpowers φd ≤ E :=
    Subgroup.zpowers_le.mpr ⟨⟨d', hd'N⟩, Subgroup.mem_subgroupOf.mpr hd'D, rfl⟩
  have hφd3 : orderOf φd = 3 := by
    have hd3 : d' ^ 3 = 1 := hc.pow_three_eq_one h37c h38c h2 hD hdiag hd'D
    refine orderOf_eq_prime ?_ fun h1 => hd'1 (hfaith d' hd'D hd'N h1)
    rw [hφd, ← map_pow]
    have : (⟨d', hd'N⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hτ3 : Nat.card (Subgroup.zpowers φd) = 3 := by rw [Nat.card_zpowers, hφd3]
  have hαinj : ∀ x ∈ D, ∀ y ∈ D, ∀ (hx : x ∈ Subgroup.normalizer (K : Set G))
      (hy : y ∈ Subgroup.normalizer (K : Set G)),
      C41Pf.quotConjHom K ⟨x, hx⟩ = C41Pf.quotConjHom K ⟨y, hy⟩ → x = y := by
    intro x hxD y hyD hx hy h
    have hxy : x * y⁻¹ ∈ D := D.mul_mem hxD (D.inv_mem hyD)
    have h1 : C41Pf.quotConjHom K ⟨x * y⁻¹, hDK hxy⟩ = 1 := by
      have e' : (⟨x * y⁻¹, hDK hxy⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨x, hx⟩ * ⟨y, hy⟩⁻¹ := rfl
      rw [e', map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hfaith _ hxy _ h1)
  have hφj : ∀ j : ℤ, φd ^ j = C41Pf.quotConjHom K ⟨d' ^ j, hDK (D.zpow_mem hd'D j)⟩ := by
    intro j
    rw [hφd, ← map_zpow]
    exact congrArg _ (Subtype.ext (by simp))
  have hτmove : (Subgroup.zpowers φd).map
      (MulAut.conj (C41Pf.quotConjHom K ⟨m * t₀, htN⟩)).toMonoidHom ≠ Subgroup.zpowers φd := by
    intro heq
    have hmem : (MulAut.conj (C41Pf.quotConjHom K ⟨m * t₀, htN⟩)) φd ∈
        Subgroup.zpowers φd := by
      rw [← heq]
      exact ⟨φd, Subgroup.mem_zpowers φd, rfl⟩
    rw [MulAut.conj_apply, hφd, hαconj _ d' htN hd'N] at hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have htdD : (m * t₀) * d' * (m * t₀)⁻¹ ∈ D := by
      rw [htd']
      exact hd''D
    have hdj := hαinj _ htdD _ (D.zpow_mem hd'D j) _ _ (hj.symm.trans (hφj j))
    apply hψne j
    have e' : (⟨d'', hd''L⟩ : ↥(fsuL0 T L)) = ⟨d', hd'L0⟩ ^ j := by
      apply Subtype.ext
      show d'' = d' ^ j
      rw [← htd', hdj]
    rw [e', map_zpow]
  have hgE : ∀ x ∈ E, C41Pf.quotConjHom K ⟨m * t₀, htN⟩ * x *
      (C41Pf.quotConjHom K ⟨m * t₀, htN⟩)⁻¹ ∈ E := by
    rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
    rw [hαconj _ d htN hdN]
    exact ⟨⟨m * t₀ * d * (m * t₀)⁻¹, mul_mem (mul_mem htN hdN) (inv_mem htN)⟩,
      Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hmt d).mp (Subgroup.mem_subgroupOf.mp hd)), rfl⟩
  have hTb' := hTb _ (hαS _ htN (hTTK htT)) hgE R₂ hR₂S hR₂E hR₂c htm' _ hτE hτ3 hτmove
  rw [htm] at hTb'
  have hOT : pCoreOf 2 K ≤ T :=
    (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHKn.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)).trans
      (F7.isSylowTwoOf_pCoreOf_le hTHs)
  have hF : ∀ R : Subgroup (O2Q K), (R = R₂ ∨ R = R₃) →
      (∀ y ∈ Subgroup.normalizer (R : Set (O2Q K)), ∀ x ∈ Subgroup.zpowers φd,
        (x : MulAut (O2Q K)) y * y⁻¹ ∈ R) →
      ∃ K' : Subgroup G, L34.Vertex T L I B D K' := by
    intro R hR' hRτ
    obtain ⟨-, hRN, hRE, hRc, ⟨π, hπ, hker⟩, -⟩ := hR R hR'
    have hO := hrad R hR'
    have hR2 : IsPGroup 2 R := fun r => ⟨1, Subtype.ext (by simpa using hRE.2 r r.2)⟩
    have hTfix : ∀ t ∈ T₁, ∀ ht : t ∈ Subgroup.normalizer (K : Set G),
        R.map (C41Pf.quotConjHom K ⟨t, ht⟩).toMonoidHom = R := by
      rcases hR' with rfl | rfl
      · exact fun t ht htN => (hT₁fix t ht htN).1
      · exact fun t ht htN => (hT₁fix t ht htN).2
    have hDfix' : ∀ d ∈ D, ∀ hd : d ∈ Subgroup.normalizer (K : Set G),
        R.map (C41Pf.quotConjHom K ⟨d, hd⟩).toMonoidHom = R := by
      rcases hR' with rfl | rfl
      · exact fun d hd hdN => (hDfix d hd hdN).1
      · exact fun d hd hdN => (hDfix d hd hdN).2
    have hTKP := hTKpre R hR'
    have hK'K : oTwoUpper (L34P.preN K R) ≤ K := (oTwoUpper_le _).trans (L34P.preN_le R)
    have hT₁K' : T₁ ≤ Subgroup.normalizer ((oTwoUpper (L34P.preN K R) : Subgroup G) : Set G) :=
      fun t ht => L34P.mem_normalizer_oTwoUpper_preN (hTK ht.1) (hTfix t ht (hTK ht.1))
    have hDK' : D ≤ Subgroup.normalizer ((oTwoUpper (L34P.preN K R) : Subgroup G) : Set G) :=
      fun d hd => L34P.mem_normalizer_oTwoUpper_preN (hDK hd) (hDfix' d hd (hDK hd))
    have hA := L34P.nonempty_alt5 hR2 hO π hπ hker
    have hsyl := L34P.isSylowTwoOf_inf hTKs hTKP
    refine ⟨oTwoUpper (L34P.preN K R), ⟨hK'K.trans hKV, hT₁K', hDK', hsyl, hA,
      (inf_le_inf_left T hK'K).trans hTKR,
      (L34P.inf_normalizer_le hO hTKP hOT).trans (hNK.trans hBTKN),
      (hc.borelOf_L_le_r0 h37c h38c hD).trans (sup_le hDK' (hR₀T₁.trans hT₁K')),
      L34P.mem_lFamily hT₁K' hA, fun b hb => ?_, fun hK'M => ?_, fun x hx => ?_,
      (F7.isSylowTwoOf_pCoreOf_le hsyl).trans inf_le_left, ⟨d', ⟨hd'D, hd'L⟩, hd'1, ?_⟩⟩⟩
    ·
      have hbD : b ∈ D := hBD' hb
      exact mem_oTwoUpper_of_odd
        (L34P.mem_preN_of_mem (hBK hb) (hDK hbD) (hDfix' b hbD (hDK hbD)))
        (hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hbD))
    ·
      have hK'N : oTwoUpper (L34P.preN K R) ≤
          Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
        fun x hx => (sup_le hBTK Subgroup.le_normalizer) (hKM' ⟨hK'K hx, hK'M hx⟩)
      refine L34P.not_normalizer_le hPnab π hπ hker (Subgroup.le_normalizer.trans hRN) hS₀2
        (fun hle => ?_) (L34P.normalizer_le_of_lift fun y hy => ?_)
      · have h1 := Subgroup.card_le_of_le hle
        rw [hS₀64, hRc] at h1
        norm_num at h1
      · obtain ⟨k, hk, hkK, hke⟩ := L34P.exists_mem_oTwoUpper_preN hO hy
        exact ⟨k, hkK, hK'N hk, hke⟩
    ·
      have hx' := hKM' ⟨hK'K hx.1, hx.2⟩
      have h1 : x ∈ Subgroup.normalizer
          (((T ⊓ K) ⊓ oTwoUpper (L34P.preN K R) : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨(sup_le hBTK Subgroup.le_normalizer) hx',
          (sup_le (hBD'.trans hDK') (hTKT₁.trans hT₁K')) hx'⟩
      rwa [inf_assoc, inf_eq_right.mpr hK'K] at h1
    ·
      rw [Subgroup.commutator_le]
      intro k hk x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hxD : d' ^ j ∈ D := D.zpow_mem hd'D j
      rw [commutatorElement_def]
      refine L34P.commutator_mem_pCoreOf hR2 (hDK hxD) (hDK' hxD) (fun y hy => ?_) hk
      have h1 := hRτ y hy _ (Subgroup.zpow_mem_zpowers φd j)
      rw [hφj j] at h1
      exact h1
  rcases hTb' with h | h
  · exact hF R₂ (Or.inl rfl) h
  · exact hF R₃ (Or.inr rfl) h

end Setup

end CFSG.Quasithin.H13.Ch9
