module

public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Ch1Sec3

theorem mem_sup_iff_of_le_normalizer {Q P : Subgroup G} (h : P ≤ Subgroup.normalizer (Q : Set G))
    {x : G} : x ∈ Q ⊔ P ↔ ∃ q ∈ Q, ∃ a ∈ P, x = q * a := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Q P h, Set.mem_mul]
  constructor
  · rintro ⟨q, hq, a, ha, rfl⟩
    exact ⟨q, hq, a, ha, rfl⟩
  · rintro ⟨q, hq, a, ha, rfl⟩
    exact ⟨q, hq, a, ha, rfl⟩

theorem inf_sup_eq_of_le_normalizer {P Q U : Subgroup G} (hUP : U ≤ P)
    (hU : U ≤ Subgroup.normalizer (Q : Set G)) (hPQ : P ⊓ Q = ⊥) : P ⊓ (Q ⊔ U) = U := by
  refine le_antisymm (fun x hx => ?_) (le_inf hUP le_sup_right)
  obtain ⟨q, hq, u, hu, rfl⟩ := (mem_sup_iff_of_le_normalizer hU).1 hx.2
  have hqP : q ∈ P := by
    have := P.mul_mem hx.1 (P.inv_mem (hUP hu))
    simpa using this
  have hq1 : q = 1 := by
    have : q ∈ P ⊓ Q := ⟨hqP, hq⟩
    rw [hPQ] at this
    exact this
  rw [hq1, one_mul]
  exact hu

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this

theorem mem_normalizer_of_map_conj_le {H : Subgroup G} {g : G}
    (h₁ : H.map (MulAut.conj g).toMonoidHom ≤ H) (h₂ : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h₁ ⟨x, hx, rfl⟩
  · intro hx
    have := h₂ ⟨g * x * g⁻¹, hx, rfl⟩
    simpa [mul_assoc] using this

theorem commutator_le_normalizer {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have e : ∀ {g : G}, g ∈ Subgroup.normalizer (H : Set G) → g ∈ Subgroup.normalizer (K : Set G) →
      ⁅H, K⁆.map (MulAut.conj g).toMonoidHom = ⁅H, K⁆ := fun hH hK => by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hK]
  exact mem_normalizer_of_map_conj_le (e hH hK).le
    (e (Subgroup.inv_mem _ hH) (Subgroup.inv_mem _ hK)).le

theorem commutator_le_left_of_le_normalizer {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  have : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hK hk) h⁻¹).mp (H.inv_mem hh)
  have e : ⁅h, k⁆ = h * (k * h⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact H.mul_mem hh this

theorem mem_normalizer_conjClosure {P Q : Subgroup G} {g : G}
    (hP : g ∈ Subgroup.normalizer (P : Set G)) (hQ : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure P Q : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (P : Set G) →
      g ∈ Subgroup.normalizer (Q : Set G) →
      (conjClosure P Q).map (MulAut.conj g).toMonoidHom ≤ conjClosure P Q := by
    intro g hP hQ
    rw [Subgroup.map_le_iff_le_comap]
    refine conjClosure_le fun h hh z hz => ?_
    have e : g * (h * z * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ := by
      group
    change (MulAut.conj g) (h * z * h⁻¹) ∈ conjClosure P Q
    rw [MulAut.conj_apply, e]
    exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hQ h).mp hh)
      ((Subgroup.mem_normalizer_iff.mp hP z).mp hz)
  exact mem_normalizer_of_map_conj_le (key hP hQ)
    (key (Subgroup.inv_mem _ hP) (Subgroup.inv_mem _ hQ))

section Frattini

variable [Finite G]

theorem frattiniIn_eq_commutator {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
    (hexp : ∀ x ∈ P, x ^ p = 1) : frattiniIn P = ⁅P, P⁆ := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  have h1 : frattini P = commutator P := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
    have hr : Set.range (fun x : P => x ^ p) = {1} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl⟩
        exact Subtype.ext (by simpa using hexp x x.2)
      · rintro rfl
        exact ⟨1, one_pow p⟩
    rw [hr, Set.union_singleton, Subgroup.closure_insert_one, Subgroup.closure_eq]
  unfold frattiniIn
  rw [h1, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem eq_of_sup_frattiniIn_eq {P U : Subgroup G} (hUP : U ≤ P) (h : U ⊔ frattiniIn P = P) :
    U = P := by
  have hinj : Function.Injective (Subgroup.map P.subtype : Subgroup P → Subgroup G) :=
    Subgroup.map_injective P.subtype_injective
  have h1 : U.subgroupOf P ⊔ frattini P = ⊤ := by
    apply hinj
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hUP, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact h
  have h2 := frattini_nongenerating h1
  have h3 := congrArg (Subgroup.map P.subtype) h2
  rwa [Subgroup.map_subgroupOf_eq_of_le hUP, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h3

theorem frattiniIn_ne_of_ne_bot {P : Subgroup G} (hP : P ≠ ⊥) : frattiniIn P ≠ P := by
  intro h
  apply hP
  exact (eq_of_sup_frattiniIn_eq bot_le (by rw [bot_sup_eq, h])).symm

end Frattini

section SylowConj

variable [Finite G] {p : ℕ} [hp : Fact p.Prime]

open scoped Pointwise in
theorem exists_conj_of_isSylowIn {S S' H : Subgroup G} (hS : IsSylowIn p S H)
    (hS' : IsSylowIn p S' H) : ∃ h ∈ H, ∀ x : G, x ∈ S' ↔ h⁻¹ * x * h ∈ S := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) hS.toSylow hS'.toSylow
  have hg' : MulAut.conj g • (hS.toSylow : Subgroup H) = (hS'.toSylow : Subgroup H) := by
    rw [← Sylow.coe_subgroup_smul (g := g), hg]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxH : x ∈ H := hS'.le hx
    have : (⟨x, hxH⟩ : H) ∈ (hS'.toSylow : Subgroup H) := hx
    rw [← hg', Subgroup.mem_smul_pointwise_iff_exists] at this
    obtain ⟨s, hs, hsx⟩ := this
    have : (g : G)⁻¹ * x * g = (s : G) := by
      have h2 : ((MulAut.conj g • s : H) : G) = x := congrArg Subtype.val hsx
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [← h2]; group
    rw [this]
    exact hs
  · intro hx
    have hxH : (g : G)⁻¹ * x * g ∈ H := hS.le hx
    have hxH' : x ∈ H := by
      have := H.mul_mem (H.mul_mem g.2 hxH) (H.inv_mem g.2)
      simpa [mul_assoc] using this
    have : (⟨x, hxH'⟩ : H) ∈ (hS'.toSylow : Subgroup H) := by
      rw [← hg', Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨⟨(g : G)⁻¹ * x * g, hxH⟩, hx, ?_⟩
      apply Subtype.ext
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact this

theorem isSylowIn_map_conj {P H : Subgroup G} (hP : IsSylowIn p P H) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    IsSylowIn p (P.map (MulAut.conj g).toMonoidHom) H := by
  refine isSylowIn_of_card_eq ?_ ?_
  · rw [← map_conj_eq_of_mem_normalizer hg]
    exact Subgroup.map_mono hP.le
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hP.card_eq

end SylowConj

theorem le_of_relIndex_eq_two_pow [Finite G] {X P W : Subgroup G} (hX : X = oTwoUpper X)
    (hPW : P ≤ W) (hWX : W ≤ X) (hXW : X ≤ Subgroup.normalizer (W : Set G)) {a : ℕ}
    (ha : P.relIndex X = 2 ^ a) : X ≤ W := by
  rw [hX]
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have : (W.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).2 hXW
  have h1 := Subgroup.pow_index_mem (W.subgroupOf X) ⟨x, hx⟩
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (ha ▸ Subgroup.relIndex_dvd_of_le_left X hPW)
  refine ⟨b, ?_⟩
  have h2 : (⟨x, hx⟩ : X) ^ (W.relIndex X) ∈ W.subgroupOf X := h1
  rw [hb, Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem commutator_sup_le {Q P : Subgroup G} (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q ⊔ P, Q ⊔ P⁆ ≤ Q ⊔ ⁅P, P⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨q, hq, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hPQ).1 hx
  obtain ⟨r, hr, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hPQ).1 hy
  have h1 : a * r * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hPQ ha) r).mp hr
  have h2 : b * q⁻¹ * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hPQ hb) q⁻¹).mp (Q.inv_mem hq)
  have e : ⁅q * a, r * b⁆ = q * (a * r * a⁻¹) * ⁅a, b⁆ * (b * q⁻¹ * b⁻¹) * r⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_left h1)) (Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator ha hb))) (Subgroup.mem_sup_left h2))
    (Subgroup.mem_sup_left (Q.inv_mem hr))

end Ch1Sec3

open Ch1Sec3

section Xi

variable [Finite G] {T X : Subgroup G}

omit [Finite G] in
theorem card_eq_card_pCoreOf_mul_relIndex (X : Subgroup G) :
    Nat.card X = Nat.card (pCoreOf 2 X) * (pCoreOf 2 X).relIndex X := by
  have h := Subgroup.relIndex_mul_card (pCoreOf 2 X) X
  rw [inf_eq_left.2 (pCoreOf_le 2 X)] at h
  rw [← h, mul_comm]

theorem IsXi.prime_spec (hX : IsXi T X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpX : p ∣ Nat.card X) :
    (∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) ∧
      ((pCoreOf 2 X).relIndex X = p ^ 2 ∨
        ((pCoreOf 2 X).relIndex X = p ^ 3 ∧ ¬ ⁅X, X⁆ ≤ pCoreOf 2 X)) ∧
      ∀ Y : Subgroup G, ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ Y → Y ≤ X →
        T ≤ Subgroup.normalizer (Y : Set G) → Y = ⁅X, X⁆ ⊔ pCoreOf 2 X ∨ Y = X := by
  obtain ⟨-, -, -, p₀, hp₀, hp₀2, hpow, hidx, hirr⟩ := hX
  suffices hpp : p = p₀ by subst hpp; exact ⟨hpow, hidx, hirr⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 X)
  obtain ⟨k, hk⟩ : ∃ k, (pCoreOf 2 X).relIndex X = p₀ ^ k := by
    rcases hidx with h | ⟨h, -⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  rw [card_eq_card_pCoreOf_mul_relIndex, ha, hk] at hpX
  rcases (Nat.Prime.dvd_mul hp).1 hpX with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp hp₀).1 (hp.dvd_of_dvd_pow h)

theorem IsXi.relIndex_eq (hX : IsXi T X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpX : p ∣ Nat.card X) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ 3 ∧ (pCoreOf 2 X).relIndex X = p ^ k := by
  rcases (hX.prime_spec hp hp2 hpX).2.1 with h | ⟨h, -⟩
  · exact ⟨2, le_rfl, by norm_num, h⟩
  · exact ⟨3, by norm_num, le_rfl, h⟩

section Sylow

variable {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}

theorem IsXi.card_sylow (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) : Nat.card P = (pCoreOf 2 X).relIndex X := by
  obtain ⟨k, -, -, hk⟩ := hX.relIndex_eq hp.out hp2 hpX
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 X)
  rw [hP.card_eq, card_eq_card_pCoreOf_mul_relIndex, ha, hk,
    Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hp.out.ne_zero),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_of_ne hp2, Finsupp.single_eq_same,
    zero_add]

theorem IsSylowIn.inf_pCoreOf_two_eq_bot (hp2 : p ≠ 2) (hP : IsSylowIn p P X) :
    P ⊓ pCoreOf 2 X = ⊥ :=
  (IsPGroup.disjoint_of_ne p 2 hp2 P (pCoreOf 2 X) hP.isPGroup (pCoreOf_isPGroup 2 X)).eq_bot

theorem IsXi.relIndex_sylow (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) : P.relIndex X = Nat.card (pCoreOf 2 X) := by
  have h := Subgroup.relIndex_mul_card P X
  rw [inf_eq_left.2 hP.le, hX.card_sylow hp2 hpX hP, card_eq_card_pCoreOf_mul_relIndex] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by
    obtain ⟨k, -, -, hk⟩ := hX.relIndex_eq hp.out hp2 hpX
    rw [hk]; exact pow_ne_zero _ hp.out.ne_zero)) h

theorem IsXi.pCoreOf_sup_eq (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) : pCoreOf 2 X ⊔ P = X := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le (pCoreOf_le 2 X) hP.le) ?_
  have hcop : (Nat.card (pCoreOf 2 X)).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne 2 p (Ne.symm hp2) _ _ (pCoreOf_isPGroup 2 X) hP.isPGroup
  have hdvd := hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
    (Subgroup.card_dvd_of_le (le_sup_right : P ≤ pCoreOf 2 X ⊔ P))
  rw [hX.card_sylow hp2 hpX hP, ← card_eq_card_pCoreOf_mul_relIndex] at hdvd
  exact Nat.le_of_dvd Nat.card_pos hdvd

theorem IsXi.pow_eq_one (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) {a : G} (ha : a ∈ P) : a ^ p = 1 := by
  have h1 : a ^ p ∈ P ⊓ pCoreOf 2 X :=
    ⟨P.pow_mem ha p, (hX.prime_spec hp.out hp2 hpX).1 a (hP.le ha)⟩
  rw [hP.inf_pCoreOf_two_eq_bot hp2] at h1
  exact h1

omit [Finite G] hp in
theorem IsSylowIn.le_normalizer_pCoreOf_two (hP : IsSylowIn p P X) :
    P ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
  hP.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

theorem IsXi.sylow_ne_bot (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) : P ≠ ⊥ := by
  intro h
  have h1 := hX.card_sylow hp2 hpX hP
  rw [h, Subgroup.card_bot] at h1
  obtain ⟨k, hk2, -, hk⟩ := hX.relIndex_eq hp.out hp2 hpX
  rw [hk] at h1
  have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.out.one_lt
  omega

theorem IsXi.sq_le_card_sylow (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) : p ^ 2 ≤ Nat.card P := by
  rw [hX.card_sylow hp2 hpX hP]
  obtain ⟨k, hk2, -, hk⟩ := hX.relIndex_eq hp.out hp2 hpX
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos hk2

theorem IsXi.commutator_le (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) : ⁅X, X⁆ ≤ pCoreOf 2 X ⊔ ⁅P, P⁆ := by
  conv_lhs => rw [← hX.pCoreOf_sup_eq hp2 hpX hP]
  exact commutator_sup_le hP.le_normalizer_pCoreOf_two

theorem IsXi.frattiniIn_eq (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) :
    frattiniIn P = ⁅P, P⁆ ∧ frattiniIn P = P ⊓ (⁅X, X⁆ ⊔ pCoreOf 2 X) := by
  have h1 : frattiniIn P = ⁅P, P⁆ :=
    frattiniIn_eq_commutator hP.isPGroup fun a ha => hX.pow_eq_one hp2 hpX hP ha
  refine ⟨h1, le_antisymm ?_ ?_⟩
  · rw [h1]
    exact le_inf (commutator_le_left_of_le_normalizer Subgroup.le_normalizer)
      (le_sup_of_le_left (Subgroup.commutator_mono hP.le hP.le))
  · have h2 : ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ pCoreOf 2 X ⊔ ⁅P, P⁆ :=
      sup_le (hX.commutator_le hp2 hpX hP) le_sup_left
    calc P ⊓ (⁅X, X⁆ ⊔ pCoreOf 2 X) ≤ P ⊓ (pCoreOf 2 X ⊔ ⁅P, P⁆) := inf_le_inf_left _ h2
      _ = ⁅P, P⁆ := inf_sup_eq_of_le_normalizer
          (commutator_le_left_of_le_normalizer Subgroup.le_normalizer)
          ((commutator_le_left_of_le_normalizer Subgroup.le_normalizer).trans
            hP.le_normalizer_pCoreOf_two)
          (hP.inf_pCoreOf_two_eq_bot hp2)
      _ = frattiniIn P := h1.symm

end Sylow

theorem IsXi.exists_prime_sup_eq (hX : IsXi T X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card X ∧
      (∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p) ∧
      ∀ P : Subgroup G, IsSylowIn p P X → pCoreOf 2 X ⊔ P = X := by
  obtain ⟨-, -, -, p, hp, hp2, -, hidx, -⟩ := id hX
  have hidx' : ∃ k, k ≠ 0 ∧ (pCoreOf 2 X).relIndex X = p ^ k := by
    rcases hidx with h | ⟨h, -⟩
    · exact ⟨2, two_ne_zero, h⟩
    · exact ⟨3, three_ne_zero, h⟩
  obtain ⟨k, hk0, hk⟩ := hidx'
  have hpX : p ∣ Nat.card X := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self p hk0) _
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hp2, hpX, fun q hq hqX => ?_, fun P hP => hX.pCoreOf_sup_eq hp2 hpX hP⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 X)
  rw [card_eq_card_pCoreOf_mul_relIndex, ha, hk] at hqX
  rcases (Nat.Prime.dvd_mul hq).1 hqX with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))

theorem IsXi.prime_dvd_card (hX : IsXi T X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpX : p ∣ Nat.card X) {q : ℕ} (hq : q.Prime) (hqX : q ∣ Nat.card X) : q = 2 ∨ q = p := by
  obtain ⟨p₀, hp₀, hp₀2, hp₀X, hdiv, -⟩ := hX.exists_prime_sup_eq
  have hpp : p = p₀ := (hdiv p hp hpX).resolve_left hp2
  subst hpp
  exact hdiv q hq hqX

section Two

variable {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}

theorem IsXi.eq_conjClosure (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) :
    X = conjClosure P X ∧ X = conjClosure P (pCoreOf 2 X) ∧
      pCoreOf 2 X = ⁅pCoreOf 2 X, P⁆ := by
  set Q := pCoreOf 2 X with hQ
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 X)
  have hidx : P.relIndex X = 2 ^ a := by rw [hX.relIndex_sylow hp2 hpX hP, ha]
  have hX1 : X = oTwoUpper X := hX.1
  have hsup : Q ⊔ P = X := hX.pCoreOf_sup_eq hp2 hpX hP
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hP.le_normalizer_pCoreOf_two
  have hQX : Q ≤ X := pCoreOf_le 2 X
  have hVX : conjClosure P X ≤ X :=
    conjClosure_le fun h hh z hz => X.mul_mem (X.mul_mem hh (hP.le hz)) (X.inv_mem hh)
  have h1 : X = conjClosure P X := le_antisymm
    (le_of_relIndex_eq_two_pow hX1 (le_conjClosure P X) hVX (le_normalizer_conjClosure P X) hidx)
    hVX
  have hWX : conjClosure P Q ≤ X :=
    conjClosure_le fun h hh z hz => X.mul_mem (X.mul_mem (hQX hh) (hP.le hz)) (X.inv_mem (hQX hh))
  have h2 : X = conjClosure P Q := by
    refine le_antisymm (le_of_relIndex_eq_two_pow hX1 (le_conjClosure P Q) hWX ?_ hidx) hWX
    rw [← hsup]
    refine sup_le (le_normalizer_conjClosure P Q) fun g hg => ?_
    exact mem_normalizer_conjClosure (Subgroup.le_normalizer hg) (hPQ hg)
  set C := ⁅Q, P⁆ with hC
  have hCQ : C ≤ Q := commutator_le_left_of_le_normalizer hPQ
  have hPC : P ≤ Subgroup.normalizer (C : Set G) := Subgroup.normalizer_commutator_ge_right Q P
  have hQC : Q ≤ Subgroup.normalizer (C : Set G) := Subgroup.normalizer_commutator_ge_left Q P
  have hW : X ≤ Subgroup.normalizer ((P ⊔ C : Subgroup G) : Set G) := by
    rw [← hsup]
    refine sup_le (fun q hq => ?_) fun b hb =>
      Subgroup.inf_normalizer_le_normalizer_sup P C ⟨Subgroup.le_normalizer hb, hPC hb⟩
    have key : ∀ {q : G}, q ∈ Q →
        (P ⊔ C).map (MulAut.conj q).toMonoidHom ≤ P ⊔ C := by
      intro q hq
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hQC hq)]
      refine sup_le ?_ le_sup_right
      rintro _ ⟨z, hz, rfl⟩
      have e : (MulAut.conj q).toMonoidHom z = ⁅q, z⁆ * z := by
        change q * z * q⁻¹ = _
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq hz))
        (Subgroup.mem_sup_left hz)
    exact mem_normalizer_of_map_conj_le (key hq) (key (Q.inv_mem hq))
  have hle : X ≤ P ⊔ C := le_of_relIndex_eq_two_pow hX1 le_sup_left
    (sup_le hP.le (hCQ.trans hQX)) hW hidx
  have h3 : Q = C := by
    refine le_antisymm (fun q hq => ?_) hCQ
    have hq' : q ∈ ((P ⊔ C : Subgroup G) : Set G) := hle (hQX hq)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P C hPC] at hq'
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp hq'
    have hbQ : b ∈ Q := by
      have := Q.mul_mem hq (Q.inv_mem (hCQ hc))
      simpa using this
    have hb1 : b ∈ P ⊓ Q := ⟨hb, hbQ⟩
    rw [hP.inf_pCoreOf_two_eq_bot hp2, Subgroup.mem_bot] at hb1
    rw [hb1, one_mul]
    exact hc
  exact ⟨h1, h2, h3⟩

end Two

section Three

variable {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}

theorem pCoreOf_le_of_quasithinIsSylowTwo (hT : quasithinIsSylowTwo T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) : pCoreOf 2 X ≤ T := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have h1 : IsPGroup 2 ((S : Subgroup G) ⊔ pCoreOf 2 X : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' S.isPGroup' (pCoreOf_isPGroup 2 X)
      (hTX.trans (normalizer_le_normalizer_pCoreOf 2 X))
  have h2 := S.is_maximal' h1 le_sup_left
  rw [← h2]
  exact le_sup_right

theorem IsXi.eq_pCoreOf_sup_normalizer (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    T = pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (P : Set G)) := by
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_le_of_quasithinIsSylowTwo hT hX.2.1
  refine le_antisymm (fun t ht => ?_) (sup_le hQT inf_le_left)
  obtain ⟨g, hgX, hg⟩ := exists_conj_of_isSylowIn hP (isSylowIn_map_conj hP (hX.2.1 ht))
  rw [← hX.pCoreOf_sup_eq hp2 hpX hP] at hgX
  obtain ⟨q, hq, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hP.le_normalizer_pCoreOf_two).1 hgX
  have hn : q⁻¹ * t ∈ T ⊓ Subgroup.normalizer (P : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem (hQT hq)) ht, Subgroup.mem_normalizer_iff.2 fun z => ?_⟩
    constructor
    · intro hz
      have h2 := (hg (t * z * t⁻¹)).1 ⟨z, hz, rfl⟩
      have e : q⁻¹ * t * z * (q⁻¹ * t)⁻¹ =
          a * ((q * a)⁻¹ * (t * z * t⁻¹) * (q * a)) * a⁻¹ := by group
      rw [e]
      exact P.mul_mem (P.mul_mem ha h2) (P.inv_mem ha)
    · intro hz
      have h1 : (q * a)⁻¹ * (t * z * t⁻¹) * (q * a) ∈ P := by
        have e : (q * a)⁻¹ * (t * z * t⁻¹) * (q * a) =
            a⁻¹ * (q⁻¹ * t * z * (q⁻¹ * t)⁻¹) * a := by group
        rw [e]
        exact P.mul_mem (P.mul_mem (P.inv_mem ha) hz) ha
      obtain ⟨w, hw, hwe⟩ := (hg (t * z * t⁻¹)).2 h1
      have hwz : w = z := by
        have hwe' : t * w * t⁻¹ = t * z * t⁻¹ := hwe
        simpa using hwe'
      rw [← hwz]
      exact hw
  have e : t = q * (q⁻¹ * t) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hq hn

theorem IsXi.irreducible (hT : quasithinIsSylowTwo T) (hX : IsXi T X) (hp2 : p ≠ 2)
    (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    frattiniIn P ≠ P ∧ ∀ U : Subgroup G, frattiniIn P ≤ U → U ≤ P →
      T ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U : Set G) →
      U = frattiniIn P ∨ U = P := by
  refine ⟨frattiniIn_ne_of_ne_bot (hX.sylow_ne_bot hp2 hpX hP), fun U hΦU hUP hNU => ?_⟩
  obtain ⟨hΦ1, hΦ2⟩ := hX.frattiniIn_eq hp2 hpX hP
  set Q := pCoreOf 2 X with hQ
  have hUQ : U ≤ Subgroup.normalizer (Q : Set G) := hUP.trans hP.le_normalizer_pCoreOf_two
  have hY1 : ⁅X, X⁆ ⊔ Q ≤ Q ⊔ U :=
    sup_le ((hX.commutator_le hp2 hpX hP).trans (sup_le_sup_left (hΦ1 ▸ hΦU) Q)) le_sup_left
  have hY2 : Q ⊔ U ≤ X := sup_le (pCoreOf_le 2 X) (hUP.trans hP.le)
  have hY3 : T ≤ Subgroup.normalizer ((Q ⊔ U : Subgroup G) : Set G) := by
    calc T = Q ⊔ (T ⊓ Subgroup.normalizer (P : Set G)) :=
          hX.eq_pCoreOf_sup_normalizer hT hp2 hpX hP
      _ ≤ _ := sup_le (fun q hq => Subgroup.le_normalizer (Subgroup.mem_sup_left hq))
          fun s hs => Subgroup.inf_normalizer_le_normalizer_sup Q U
            ⟨(hX.2.1.trans (normalizer_le_normalizer_pCoreOf 2 X)) hs.1, hNU hs⟩
  have hD : P ⊓ (Q ⊔ U) = U := inf_sup_eq_of_le_normalizer hUP hUQ (hP.inf_pCoreOf_two_eq_bot hp2)
  rcases (hX.prime_spec hp.out hp2 hpX).2.2 (Q ⊔ U) hY1 hY2 hY3 with h | h
  · left
    rw [← hD, h, hΦ2]
  · right
    rw [← hD, h, inf_eq_left.2 hP.le]

end Three

end Xi

namespace Ch1Sec3

theorem eq_commutator_frattiniIn_of_irreducible [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {P S : Subgroup G} (hPp : IsPGroup p P) (hexp : ∀ a ∈ P, a ^ p = 1)
    (hcard : p ^ 2 ≤ Nat.card P) (hS2 : IsPGroup 2 S)
    (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hirr : ∀ U : Subgroup G, frattiniIn P ≤ U → U ≤ P →
      S ≤ Subgroup.normalizer (U : Set G) → U = frattiniIn P ∨ U = P) :
    P = ⁅P, frattiniIn S⁆ := by
  set Φ := frattiniIn P with hΦdef
  have hΦ : Φ = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  have hΦP : Φ ≤ P := hΦ ▸ commutator_le_left_of_le_normalizer Subgroup.le_normalizer
  have hNΦ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Φ : Set G) :=
    normalizer_le_normalizer_map_of_characteristic (frattini P)
  have hconjP : ∀ g ∈ P, ∀ f ∈ Φ, g * f * g⁻¹ ∈ Φ := fun g hg f hf =>
    (Subgroup.mem_normalizer_iff.mp (hNΦ (Subgroup.le_normalizer hg)) f).mp hf
  have hconjS : ∀ g ∈ S, ∀ f ∈ Φ, g * f * g⁻¹ ∈ Φ := fun g hg f hf =>
    (Subgroup.mem_normalizer_iff.mp (hNΦ (hSP hg)) f).mp hf
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Φ := fun a ha b hb => by
    rw [hΦ]
    have := Subgroup.commutator_mem_commutator ha hb
    rwa [commutatorElement_def] at this
  set D := frattiniIn S with hDdef
  have hDS : D ≤ S := Subgroup.map_subtype_le _
  have hSD : S ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_map_of_characteristic (frattini S))
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := hDS.trans hSP
  have : Fact (IsPGroup 2 S) := ⟨hS2⟩
  have hsq : ∀ s ∈ S, s ^ 2 ∈ D := fun s hs =>
    ⟨⟨s, hs⟩ ^ 2, CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _, by simp⟩
  have hcomS : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ D := fun s hs t ht =>
    ⟨⁅(⟨s, hs⟩ : S), ⟨t, ht⟩⁆, CFSG.commutator_le_frattini_of_isPGroup (p := 2)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)),
      by simp [commutatorElement_def]⟩
  set W := ⁅P, D⁆ with hWdef
  have hWP : W ≤ P := commutator_le_left_of_le_normalizer hDP
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := fun s hs =>
    commutator_le_normalizer (hSP hs) (hSD hs)
  rcases hirr (W ⊔ Φ) le_sup_right (sup_le hWP hΦP)
    (fun s hs => Subgroup.inf_normalizer_le_normalizer_sup W Φ
      ⟨hSW hs, hNΦ (hSP hs)⟩) with h | h
  swap
  · exact (eq_of_sup_frattiniIn_eq hWP h).symm
  exfalso
  have hD : ∀ a ∈ P, ∀ d ∈ D, d * a * d⁻¹ * a⁻¹ ∈ Φ := fun a ha d hd => by
    have h1 : ⁅a, d⁆ ∈ Φ := h ▸ Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hd)
    have e : d * a * d⁻¹ * a⁻¹ = ⁅a, d⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Φ.inv_mem h1
  let C : G → Subgroup G := fun s =>
    { carrier := {a | a ∈ P ∧ s * a * s⁻¹ * a⁻¹ ∈ Φ}
      one_mem' := ⟨P.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨P.mul_mem ha hb, ?_⟩
        have e : s * (a * b) * s⁻¹ * (a * b)⁻¹ =
            (s * a * s⁻¹ * a⁻¹) * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact Φ.mul_mem ha' (hconjP a ha _ hb')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨P.inv_mem ha, ?_⟩
        have e : s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hconjP a⁻¹ (P.inv_mem ha) _ (Φ.inv_mem ha') }
  have hCs : ∀ s ∈ S, C s = Φ ∨ C s = P := by
    intro s hs
    have hCΦ : Φ ≤ C s := fun f hf =>
      ⟨hΦP hf, Φ.mul_mem (hconjS s hs f hf) (Φ.inv_mem hf)⟩
    have key : ∀ t ∈ S, ∀ a ∈ C s, t * a * t⁻¹ ∈ C s := by
      rintro t ht a ⟨ha, ha'⟩
      have hsa : s * a * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hSP hs) a).mp ha
      have hb : t * (s * a * s⁻¹) * t⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hSP ht) _).mp hsa
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hSP ht) a).mp ha, ?_⟩
      have e : s * (t * a * t⁻¹) * s⁻¹ * (t * a * t⁻¹)⁻¹ =
          ((s * t * s⁻¹ * t⁻¹) * (t * (s * a * s⁻¹) * t⁻¹) * (s * t * s⁻¹ * t⁻¹)⁻¹ *
            (t * (s * a * s⁻¹) * t⁻¹)⁻¹) * (t * (s * a * s⁻¹ * a⁻¹) * t⁻¹) := by group
      rw [e]
      exact Φ.mul_mem (hD _ hb _ (hcomS s hs t ht)) (hconjS t ht _ ha')
    have hSC : S ≤ Subgroup.normalizer (C s : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key t ht x, fun hx => ?_⟩
      have := key t⁻¹ (S.inv_mem ht) _ hx
      simpa [mul_assoc] using this
    exact hirr (C s) hCΦ (fun a ha => ha.1) hSC
  have hinv : ∀ s ∈ S, C s = Φ → ∀ a ∈ P, a * (s * a * s⁻¹) ∈ Φ := by
    intro s hs hC a ha
    have hsa : s * a * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hSP hs) a).mp ha
    have he : s ^ 2 * a * (s ^ 2)⁻¹ * a⁻¹ ∈ Φ := hD a ha (s ^ 2) (hsq s hs)
    have hw : a * (s * a * s⁻¹) ∈ C s := by
      refine ⟨P.mul_mem ha hsa, ?_⟩
      have e : s * (a * (s * a * s⁻¹)) * s⁻¹ * (a * (s * a * s⁻¹))⁻¹ =
          ((s * a * s⁻¹) * (s ^ 2 * a * (s ^ 2)⁻¹ * a⁻¹) * (s * a * s⁻¹)⁻¹) *
            ((s * a * s⁻¹) * a * (s * a * s⁻¹)⁻¹ * a⁻¹) := by group
      rw [e]
      exact Φ.mul_mem (hconjP _ hsa _ he) (hcomm _ hsa a ha)
    rw [hC] at hw
    exact hw
  have hall : ∀ U : Subgroup G, Φ ≤ U → U ≤ P → S ≤ Subgroup.normalizer (U : Set G) := by
    intro U hΦU hUP
    have key : ∀ s ∈ S, ∀ a ∈ U, s * a * s⁻¹ ∈ U := by
      intro s hs a ha
      rcases hCs s hs with hC | hC
      · have h1 := hinv s hs hC a (hUP ha)
        have e : s * a * s⁻¹ = a⁻¹ * (a * (s * a * s⁻¹)) := by group
        rw [e]
        exact U.mul_mem (U.inv_mem ha) (hΦU h1)
      · have h1 : a ∈ C s := hC ▸ hUP ha
        have e : s * a * s⁻¹ = (s * a * s⁻¹ * a⁻¹) * a := by group
        rw [e]
        exact U.mul_mem (hΦU h1.2) ha
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key s hs x, fun hx => ?_⟩
    have := key s⁻¹ (S.inv_mem hs) _ hx
    simpa [mul_assoc] using this
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  obtain ⟨a, ha, haΦ⟩ :=
    IsConcreteLE.exists_of_lt (lt_of_le_of_ne hΦP (frattiniIn_ne_of_ne_bot hPne))
  have hU : Subgroup.zpowers a ⊔ Φ ≤ P := sup_le (Subgroup.zpowers_le.2 ha) hΦP
  rcases hirr _ le_sup_right hU (hall _ le_sup_right hU) with h' | h'
  · exact haΦ (h' ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  · have hza := eq_of_sup_frattiniIn_eq (Subgroup.zpowers_le.2 ha) h'
    have hc : Nat.card P = orderOf a := by rw [← hza, Nat.card_zpowers]
    have ho : orderOf a ≤ p := Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one (hexp a ha))
    have : p < p ^ 2 := by
      have := hp.out.two_le
      nlinarith
    omega

end Ch1Sec3

section Four

variable [Finite G] {T X : Subgroup G} {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}

theorem IsXi.eq_commutator_frattiniIn (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    P = ⁅P, frattiniIn (T ⊓ Subgroup.normalizer (P : Set G))⁆ :=
  eq_commutator_frattiniIn_of_irreducible hP.isPGroup (fun _ ha => hX.pow_eq_one hp2 hpX hP ha)
    (hX.sq_le_card_sylow hp2 hpX hP) (hT.1.to_le inf_le_left) inf_le_right
    (hX.irreducible hT hp2 hpX hP).2

theorem IsXi.eq_commutator_normalizer (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    P = ⁅P, T ⊓ Subgroup.normalizer (P : Set G)⁆ := by
  refine le_antisymm ?_ (commutator_le_left_of_le_normalizer inf_le_right)
  conv_lhs => rw [hX.eq_commutator_frattiniIn hT hp2 hpX hP]
  exact Subgroup.commutator_mono le_rfl (Subgroup.map_subtype_le _)

end Four

theorem Ch1Sec3.oTwoUpper_sup_eq_of_isPGroup {B X : Subgroup G} (hB : IsPGroup 2 B)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hX : X = oTwoUpper X) :
    oTwoUpper (B ⊔ X) = X := by
  refine (eq_oTwoUpper_of_pow_mem le_sup_right (fun x hx => ?_) hX).symm
  have hx' : x ∈ ((X ⊔ B : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X B hBX] at hx'
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hB ⟨b, hb⟩
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hBX hb) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

theorem IsXi.eq_oTwoUpper_sup [Finite G] {T X H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hX : IsXi T X) (hH : InH (X ⊔ T) H) : X = oTwoUpper (pCoreOf 2 H ⊔ X) := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hB : pCoreOf 2 H ≤ (S : Subgroup G) := pCoreOf_two_le_sylow H S (le_sup_right.trans hH.1)
  exact (oTwoUpper_sup_eq_of_isPGroup (pCoreOf_isPGroup 2 H) (hB.trans hX.2.1) hX.1).symm

end CFSG.Quasithin
