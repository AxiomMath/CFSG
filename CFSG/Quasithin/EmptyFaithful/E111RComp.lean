module

public import CFSG.Quasithin.Vol2.Ch11SecBE111Core

public section

namespace CFSG.Quasithin.E2.E22N.E111R

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def IsComp (X S : Subgroup G) : Prop :=
  S ≤ X ∧ (S.subgroupOf X).Normal ∧ IsSimpleGroup ↥S ∧ ∃ a b : ↥S, a * b ≠ b * a

theorem conjSub_eq_of_mem_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : A1b.conjSub g H = H := by
  ext x
  rw [A1b.mem_conjSub_iff]
  have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x)
  simp only [inv_inv] at h
  exact h.symm

theorem mem_normalizer_of_conjSub_eq {g : G} {H : Subgroup G} (h : A1b.conjSub g H = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact A1b.mem_conjSub_of_mem hx
  · intro hx
    rw [← h, A1b.mem_conjSub_iff] at hx
    simpa [mul_assoc] using hx

theorem conjSub_iSup₂ {ι : Sort*} {κ : ι → Sort*} (g : G) (f : (i : ι) → κ i → Subgroup G) :
    A1b.conjSub g (⨆ (i) (j), f i j) = ⨆ (i) (j), A1b.conjSub g (f i j) := by
  unfold A1b.conjSub
  simp only [Subgroup.map_iSup]

theorem mem_normalizer_of_conjSub_le {g : G} {H : Subgroup G} (h1 : A1b.conjSub g H ≤ H)
    (h2 : A1b.conjSub g⁻¹ H ≤ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  refine mem_normalizer_of_conjSub_eq (le_antisymm h1 ?_)
  calc H = A1b.conjSub g (A1b.conjSub g⁻¹ H) := by
        rw [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one]
    _ ≤ A1b.conjSub g H := A1b.conjSub_mono g h2

theorem normal_of_conjSub_le {N : Subgroup G} (h : ∀ g : G, A1b.conjSub g N ≤ N) : N.Normal :=
  ⟨fun _ hn g => h g (A1b.mem_conjSub_of_mem hn)⟩

namespace IsComp

variable {X S S' : Subgroup G}

theorem le (hS : IsComp X S) : S ≤ X := hS.1

theorem simple (hS : IsComp X S) : IsSimpleGroup ↥S := hS.2.2.1

theorem nonabelian (hS : IsComp X S) : ∃ a b : ↥S, a * b ≠ b * a := hS.2.2.2

theorem le_normalizer (hS : IsComp X S) : X ≤ Subgroup.normalizer (S : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hS.1).mp hS.2.1

theorem ne_bot (hS : IsComp X S) : S ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := hS.nonabelian
  have ha : a = 1 := Subtype.ext (by simpa [h] using a.2)
  rw [ha, one_mul, mul_one] at hab
  exact hab rfl

theorem conj (hX : X.Normal) (hS : IsComp X S) (g : G) : IsComp X (A1b.conjSub g S) := by
  set e := Subgroup.equivMapOfInjective S (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [A1b.mem_conjSub_iff] at hx
    have := hX.conj_mem _ (hS.le hx) g
    simpa [mul_assoc] using this
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (fun x hx => by
      rw [A1b.mem_conjSub_iff] at hx
      have := hX.conj_mem _ (hS.le hx) g
      simpa [mul_assoc] using this)]
    intro x hx
    rw [← A1b.conjSub_normalizer, A1b.mem_conjSub_iff]
    exact hS.le_normalizer (by simpa using hX.conj_mem x hx g⁻¹)
  · have := hS.simple
    exact (MulEquiv.isSimpleGroup_congr e).mp this
  · obtain ⟨a, b, hab⟩ := hS.nonabelian
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h

theorem eq_or_commute (hS : IsComp X S) (hS' : IsComp X S') :
    S = S' ∨ ∀ x ∈ S, ∀ y ∈ S', x * y = y * x := by
  have := hS.simple
  have := hS'.simple
  have hnS : ∀ s ∈ S, s ∈ Subgroup.normalizer ((S ⊓ S' : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hS'.le_normalizer (hS.le hs)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hN : ((S ⊓ S').subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S ⊓ S').subgroupOf S) with h | h
  · right
    rw [Subgroup.subgroupOf_eq_bot] at h
    intro x hx y hy
    have hc1 : x * y * x⁻¹ * y⁻¹ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (hS.le_normalizer (hS'.le hy)) x⁻¹).mp
        (inv_mem hx)
      have h3 := S.mul_mem hx this
      simpa [mul_assoc] using h3
    have hc2 : x * y * x⁻¹ * y⁻¹ ∈ S' := by
      have := (Subgroup.mem_normalizer_iff.mp (hS'.le_normalizer (hS.le hx)) y).mp hy
      exact S'.mul_mem this (inv_mem hy)
    have h0 := (Subgroup.disjoint_def.mp h) ⟨hc1, hc2⟩ hc1
    have : x * y * x⁻¹ * y⁻¹ * y * x = y * x := by rw [h0, one_mul]
    simpa [mul_assoc] using this
  · left
    rw [Subgroup.subgroupOf_eq_top] at h
    have hSS' : S ≤ S' := h.trans inf_le_right
    have hn : (S.subgroupOf S').Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSS').mpr (hS'.le.trans hS.le_normalizer)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf S') with h' | h'
    · rw [Subgroup.subgroupOf_eq_bot] at h'
      exact absurd (le_bot_iff.mp fun x hx => (Subgroup.disjoint_def.mp h') hx (hSS' hx))
        hS.ne_bot
    · exact le_antisymm hSS' (Subgroup.subgroupOf_eq_top.mp h')

end IsComp

section Reduced

variable [Finite G] {X T : Subgroup G}

theorem exists_isComp (hR : E111Reduced G X T) : ∃ S, IsComp X S := by
  obtain ⟨hXn, hX1, hmin, hnab, -, -, -⟩ := hR
  obtain ⟨r, S, hr, hSX, hSs, hconj, hSn, e, -⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hXn hX1 hmin
  set i₀ : Fin r := ⟨0, hr⟩
  refine ⟨S i₀, hSX i₀, hSn i₀, hSs i₀, ?_⟩
  by_contra hab
  push Not at hab
  have hcomm : ∀ i, ∀ a b : ↥(S i), a * b = b * a := by
    intro i a b
    obtain ⟨g, hg⟩ := hconj i₀ i
    have ha : (a : G) ∈ CFSG.conjugate (S i₀) g := by rw [← hg]; exact a.2
    have hb : (b : G) ∈ CFSG.conjugate (S i₀) g := by rw [← hg]; exact b.2
    obtain ⟨a', ha', ha'e⟩ := ha
    obtain ⟨b', hb', hb'e⟩ := hb
    have h1 := congrArg (fun z : ↥(S i₀) => (MulAut.conj g⁻¹) (z : G)) (hab ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul, map_mul] at h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha'e, ← hb'e]
    exact h1
  obtain ⟨x, y, hxy⟩ := hnab
  apply hxy
  have hp : e.symm x * e.symm y = e.symm y * e.symm x := funext fun i => hcomm i _ _
  have := congrArg e hp
  simpa using this

theorem iSup_isComp_eq (hR : E111Reduced G X T) :
    ⨆ (S : Subgroup G) (_ : IsComp X S), S = X := by
  obtain ⟨S₀, hS₀⟩ := exists_isComp hR
  have hXn := hR.1
  have hNX : (⨆ (S : Subgroup G) (_ : IsComp X S), S) ≤ X := iSup₂_le fun S hS => hS.le
  have hNn : (⨆ (S : Subgroup G) (_ : IsComp X S), S).Normal := normal_of_conjSub_le fun g => by
    rw [conjSub_iSup₂]
    exact iSup₂_le fun S hS => le_iSup₂_of_le (A1b.conjSub g S) (hS.conj hXn g) le_rfl
  rcases hR.2.2.1 _ hNn hNX with h | h
  · exact absurd (le_bot_iff.mp ((le_iSup₂_of_le S₀ hS₀ le_rfl).trans h.le)) hS₀.ne_bot
  · exact h

omit [Finite G] in
theorem iSup_conj_eq (hR : E111Reduced G X T) {S : Subgroup G} (hS : IsComp X S) :
    ⨆ (t : G) (_ : t ∈ T), A1b.conjSub t S = X := by
  obtain ⟨hXn, -, hmin, -, -, -, hXT⟩ := hR
  set N := ⨆ (t : G) (_ : t ∈ T), A1b.conjSub t S with hN
  have hNX : N ≤ X := iSup₂_le fun t _ => (hS.conj hXn t).le
  have hTN : ∀ g ∈ T, A1b.conjSub g N ≤ N := fun g hg => by
    rw [hN, conjSub_iSup₂]
    refine iSup₂_le fun t ht => ?_
    rw [← A1b.conjSub_mul]
    exact le_iSup₂_of_le (g * t) (T.mul_mem hg ht) le_rfl
  have hXN : ∀ g ∈ X, A1b.conjSub g N ≤ N := fun g hg => by
    rw [hN, conjSub_iSup₂]
    refine iSup₂_le fun t ht => ?_
    rw [conjSub_eq_of_mem_normalizer ((hS.conj hXn t).le_normalizer hg)]
    exact le_iSup₂_of_le t ht le_rfl
  have hnorm : X ⊔ T ≤ Subgroup.normalizer (N : Set G) := sup_le
    (fun g hg => mem_normalizer_of_conjSub_le (hXN g hg) (hXN _ (inv_mem hg)))
    (fun g hg => mem_normalizer_of_conjSub_le (hTN g hg) (hTN _ (inv_mem hg)))
  rw [hXT, top_le_iff, Subgroup.normalizer_eq_top_iff] at hnorm
  rcases hmin N hnorm hNX with h | h
  · have hSN : S ≤ N := le_iSup₂_of_le 1 T.one_mem (by rw [A1b.conjSub_one])
    exact absurd (le_bot_iff.mp (hSN.trans h.le)) hS.ne_bot
  · exact h

theorem exists_isComp_not_le (hR : E111Reduced G X T) {A : Subgroup G} (hA : A ≠ ⊥) :
    ∃ S, IsComp X S ∧ ¬ A ≤ Subgroup.centralizer (S : Set G) := by
  by_contra h
  push Not at h
  apply hA
  have hC : X ≤ Subgroup.centralizer (A : Set G) := by
    rw [← iSup_isComp_eq hR]
    exact iSup₂_le fun S hS => Subgroup.le_centralizer_iff.mp (h S hS)
  have h2 := Subgroup.le_centralizer_iff.mp hC
  rw [hR.2.2.2.2.1] at h2
  exact le_bot_iff.mp h2

omit [Finite G] in
theorem pCoreOf_top_eq : pCoreOf 2 (⊤ : Subgroup G) = CFSG.Open.pCore 2 G := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := G)).symm,
    Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom =
      MonoidHom.id G := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

omit [Finite G] in
theorem pCoreOf_top_normal : (pCoreOf 2 (⊤ : Subgroup G)).Normal := by
  rw [pCoreOf_top_eq]
  exact CFSG.LieType.BorelTits.pCore_normal 2

theorem pCoreOf_two_eq_bot (hR : E111Reduced G X T) : pCoreOf 2 (⊤ : Subgroup G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_isComp hR
  have hXn := hR.1
  rw [pCoreOf_top_eq]
  set P := CFSG.Open.pCore 2 G
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hPX : P ⊓ X = ⊥ := by
    rcases hR.2.2.1 (P ⊓ X) inferInstance inf_le_right with h | h
    · exact h
    · exfalso
      have hS2 : IsPGroup 2 ↥S := hP2.to_le ((hS.le.trans h.ge).trans inf_le_left)
      have := hS.simple
      have := hS2.isNilpotent
      exact not_nonabelian_of_isSolvable inferInstance hS.nonabelian
  have hc : ⁅P, X⁆ = ⊥ := le_bot_iff.mp (hPX ▸ Subgroup.commutator_le_inf P X)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hR.2.2.2.2.1] at hc
  exact le_bot_iff.mp hc

omit [Finite G] in
theorem tauOf_le (h : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T A : Subgroup G) :
    E1.tauOf ⊤ T A ≤ T ⊓ Subgroup.centralizer (A : Set G) := by
  intro t ht
  rw [E1.mem_tauOf] at ht
  refine ⟨ht.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  have h1 := ht.2.2 a ha
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem isSylowIn_inf (hR : E111Reduced G X T) {S : Subgroup G} (hS : IsComp X S) :
    IsSylowIn 2 (T ⊓ S) S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXn := hR.1
  have hTX : IsSylowIn 2 (T ⊓ X) X := hR.2.2.2.2.2.1.inf_normal le_top inferInstance
  have hTS : IsSylowIn 2 (T ⊓ X ⊓ S) S := hTX.inf_normal hS.le hS.2.1
  rwa [inf_assoc, inf_eq_right.mpr hS.le] at hTS

theorem inf_ne_bot (hR : E111Reduced G X T) {S : Subgroup G} (hS : IsComp X S)
    (hinv : ∃ x ∈ S, x ≠ 1 ∧ x ^ 2 = 1) : T ⊓ S ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := (isSylowIn_inf hR hS).card_eq
  obtain ⟨x, hxS, hx1, hx2⟩ := hinv
  have ho : orderOf (⟨x, hxS⟩ : ↥S) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hx2)) (fun h => hx1 (congrArg Subtype.val h))
  have h2 : 2 ∣ Nat.card S := ho ▸ orderOf_dvd_natCard _
  have hv : 1 ≤ (Nat.card S).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization Nat.card_pos.ne').mp h2
  intro hbot
  rw [hbot, Subgroup.card_bot] at hc
  have : 2 ≤ 2 ^ (Nat.card S).factorization 2 :=
    le_self_pow₀ (by norm_num) (by omega)
  omega

end Reduced

theorem le_of_diag {H S T : Subgroup G} (hS : IsSimpleGroup ↥S) (hTS : T ⊓ S ≠ ⊥) (hTH : T ≤ H)
    (hdiag : ∀ x ∈ S, ∃ y ∈ H, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G)) : S ≤ H := by
  have hn : ((H ⊓ S).subgroupOf S).Normal := by
    refine ⟨fun k hk s => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨y, hyH, hc⟩ := hdiag s s.2
    have hcom := Subgroup.mem_centralizer_iff.mp hc (k : G) k.2
    have hks : (s : G) * k * (s : G)⁻¹ = y * k * y⁻¹ := by
      calc (s : G) * k * (s : G)⁻¹
          = s * (k * ((s : G)⁻¹ * y)) * ((s : G)⁻¹ * y)⁻¹ * (s : G)⁻¹ := by group
        _ = s * (((s : G)⁻¹ * y) * k) * ((s : G)⁻¹ * y)⁻¹ * (s : G)⁻¹ := by rw [hcom]
        _ = y * k * y⁻¹ := by group
    refine ⟨?_, (s * k * s⁻¹).2⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hks]
    exact H.mul_mem (H.mul_mem hyH hk.1) (H.inv_mem hyH)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((H ⊓ S).subgroupOf S) with h | h
  · exfalso
    apply hTS
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact le_bot_iff.mp fun x hx => (Subgroup.disjoint_def.mp h) ⟨hTH hx.1, hx.2⟩ hx.2
  · exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left

end CFSG.Quasithin.E2.E22N.E111R
