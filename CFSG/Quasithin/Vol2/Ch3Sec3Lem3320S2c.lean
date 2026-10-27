module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S2b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_triple {Q : Type*} [Group Q] {a b c : Q} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (i j l i' j' l' : ℕ) :
    a ^ i * b ^ j * c ^ l * (a ^ i' * b ^ j' * c ^ l') =
      a ^ (i + i') * b ^ (j + j') * c ^ (l + l') := by
  have h1 : Commute (c ^ l) (a ^ i') := (hac.pow_pow i' l).symm
  have h2 : Commute (b ^ j) (a ^ i') := (hab.pow_pow i' j).symm
  have h3 : Commute (c ^ l) (b ^ j') := (hbc.pow_pow j' l).symm
  rw [pow_add, pow_add, pow_add]
  simp only [mul_assoc]
  rw [h1.left_comm, h2.left_comm, h3.left_comm]

omit [Finite G] in
theorem card_eq_of_three {Q : Type*} [Group Q] {Y : Subgroup Q} [Finite Y] {a b c t₁ t₂ : Q}
    (ha : a ∈ Y) (hb : b ∈ Y) (hc : c ∈ Y) (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hc1 : c ≠ 1) (h1a : t₁ * a * t₁⁻¹ = a) (h1b : t₁ * b * t₁⁻¹ = b⁻¹)
    (h1c : t₁ * c * t₁⁻¹ = c⁻¹) (h2a : t₂ * a * t₂⁻¹ = a⁻¹) (h2b : t₂ * b * t₂⁻¹ = b)
    (h2c : t₂ * c * t₂⁻¹ = c⁻¹) (hspan : ∀ y ∈ Y, ∃ i j l : ℕ, y = a ^ i * b ^ j * c ^ l) :
    Nat.card Y = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hinv : ∀ {e : Q}, e ^ 3 = 1 → e⁻¹ = e ^ 2 := fun he => by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', he]
  have hconj : ∀ (t : Q) (i j l : ℕ), t * (a ^ i * b ^ j * c ^ l) * t⁻¹ =
      (t * a * t⁻¹) ^ i * (t * b * t⁻¹) ^ j * (t * c * t⁻¹) ^ l := by
    intro t i j l
    rw [conj_pow, conj_pow, conj_pow]
    group
  have h3 : ∀ {e : Q} (n : ℕ), e ^ 3 = 1 → e ^ (n + 2 * n) = 1 := fun n he => by
    rw [show n + 2 * n = 3 * n by ring, pow_mul, he, one_pow]
  have h3' : ∀ {e : Q} (n : ℕ), e ^ 3 = 1 → e ^ (2 * n + n) = 1 := fun n he => by
    rw [show 2 * n + n = 3 * n by ring, pow_mul, he, one_pow]
  have key : ∀ i j l i' j' l' : ℕ, a ^ i * b ^ j * c ^ l = a ^ i' * b ^ j' * c ^ l' →
      a ^ (i + i) = a ^ (i' + i') ∧ b ^ (j + j) = b ^ (j' + j') := by
    intro i j l i' j' l' E
    have E1 := congrArg (fun q => t₁ * q * t₁⁻¹) E
    have E2 := congrArg (fun q => t₂ * q * t₂⁻¹) E
    simp only [hconj, h1a, h1b, h1c, h2a, h2b, h2c, hinv hb3, hinv hc3, hinv ha3,
      ← pow_mul] at E1 E2
    constructor
    · have E3 := congrArg₂ (· * ·) E E1
      rw [mul_triple hab hac hbc, mul_triple hab hac hbc, h3 _ hb3, h3 _ hc3, h3 _ hb3,
        h3 _ hc3, mul_one, mul_one, mul_one, mul_one] at E3
      exact E3
    · have E3 := congrArg₂ (· * ·) E E2
      rw [mul_triple hab hac hbc, mul_triple hab hac hbc, h3 _ ha3, h3 _ hc3, h3 _ ha3,
        h3 _ hc3, one_mul, mul_one, one_mul, mul_one] at E3
      exact E3
  let f : Fin 3 × Fin 3 × Fin 3 → Y := fun v =>
    ⟨a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ),
      Y.mul_mem (Y.mul_mem (Y.pow_mem ha _) (Y.pow_mem hb _)) (Y.pow_mem hc _)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j, l⟩ ⟨i', j', l'⟩ hfe
    have E : a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (l : ℕ) =
        a ^ (i' : ℕ) * b ^ (j' : ℕ) * c ^ (l' : ℕ) := congrArg Subtype.val hfe
    obtain ⟨ea, eb⟩ := key _ _ _ _ _ _ E
    rw [pow_inj_mod, hoa] at ea
    rw [pow_inj_mod, hob] at eb
    have hi : i = i' := Fin.ext (by omega)
    have hj : j = j' := Fin.ext (by omega)
    subst hi
    subst hj
    have ec : c ^ (l : ℕ) = c ^ (l' : ℕ) := mul_left_cancel E
    rw [pow_inj_mod, hoc] at ec
    have hl : l = l' := Fin.ext (by omega)
    rw [hl]
  have hs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨i, j, l, rfl⟩ := hspan y hy
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨l % 3, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩
    show a ^ (i % 3) * b ^ (j % 3) * c ^ (l % 3) = a ^ i * b ^ j * c ^ l
    rw [← pow_eq_pow_mod i ha3, ← pow_eq_pow_mod j hb3, ← pow_eq_pow_mod l hc3]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)]
  simp

omit [Finite G] in
theorem commute_of_three {Q : Type*} [Group Q] {q a : Q} {j m : ℕ} (ha3 : a ^ 3 = 1)
    (hq : q * a * q⁻¹ = a ^ j) (hj : j % 3 ≠ 0) (hqm : q ^ 3 ^ m = 1) : q * a = a * q := by
  have h2 : q * q * a * (q * q)⁻¹ = a := conj_sq_of_pow ha3 hj hq
  have hc : Commute (q * q) a := by
    show q * q * a = a * (q * q)
    calc q * q * a = q * q * a * (q * q)⁻¹ * (q * q) := by group
      _ = a * (q * q) := by rw [h2]
  obtain ⟨k, hk⟩ := (show Odd 3 by decide).pow (n := m)
  have hqr : q = (q * q) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = 3 ^ m + 1 by omega, pow_succ, hqm, one_mul]
  rw [hqr]
  exact (hc.pow_left (k + 1)).eq

omit [Finite G] in
theorem exists_mem_not_mem_two {A B C : Subgroup G} (hAB : ¬ A ≤ B) (hAC : ¬ A ≤ C) :
    ∃ a ∈ A, a ∉ B ∧ a ∉ C := by
  obtain ⟨a, haA, haB⟩ := Set.not_subset.mp hAB
  obtain ⟨b, hbA, hbC⟩ := Set.not_subset.mp hAC
  by_cases haC : a ∈ C
  · by_cases hbB : b ∈ B
    · refine ⟨a * b, A.mul_mem haA hbA, fun h => haB ?_, fun h => hbC ?_⟩
      · have := B.mul_mem h (B.inv_mem hbB)
        rwa [mul_inv_cancel_right] at this
      · have := C.mul_mem (C.inv_mem haC) h
        rwa [inv_mul_cancel_left] at this
    · exact ⟨b, hbA, hbB, hbC⟩
  · exact ⟨a, haA, haB, haC⟩

theorem perm3_invert : ∀ σ κ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ ≠ 1 →
    Equiv.Perm.sign κ = 1 → σ * κ * σ⁻¹ * κ = 1 := by
  decide

omit [Finite G] in
theorem three_le_card {Q : Type*} [Group Q] [Finite Q] {a b : Q} (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : a ≠ b) : 3 ≤ Nat.card Q := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card]
  have h : ({1, a, b} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hb⟩
  rw [← h]
  exact Finset.card_le_univ _

omit [Finite G] in
theorem comm_mem_of_inv {N : Subgroup G} {t₁ t₂ e : G}
    (h1 : t₁ ∈ Subgroup.normalizer (N : Set G)) (he : e ∈ Subgroup.normalizer (N : Set G))
    (ha : t₂ * e * t₂⁻¹ * e ∈ N) (hb : t₁ * e * t₁⁻¹ * e ∈ N) : ⁅t₁ * t₂, e⁆ ∈ N := by
  have e1 : ⁅t₁ * t₂, e⁆ =
      (t₁ * (t₂ * e * t₂⁻¹ * e) * t₁⁻¹) * (e * (t₁ * e * t₁⁻¹ * e)⁻¹ * e⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp h1 _).mp ha)
    ((Subgroup.mem_normalizer_iff.mp he _).mp (N.inv_mem hb))

omit [Finite G] in
theorem mk_conj_eq_of_comm {B N : Subgroup G} [(N.subgroupOf B).Normal] {t y : G} (ht : t ∈ B)
    (hy : y ∈ B) (hc : ⁅t, y⁆ ∈ N) :
    QuotientGroup.mk' (N.subgroupOf B) ⟨t, ht⟩ * QuotientGroup.mk' (N.subgroupOf B) ⟨y, hy⟩ *
      (QuotientGroup.mk' (N.subgroupOf B) ⟨t, ht⟩)⁻¹ =
        QuotientGroup.mk' (N.subgroupOf B) ⟨y, hy⟩ := by
  rw [(mk_comm_iff ht hy).mpr hc, mul_inv_cancel_right]

omit [Finite G] in
theorem mk_conj_eq_inv {B N : Subgroup G} [(N.subgroupOf B).Normal] {t y : G} (ht : t ∈ B)
    (hy : y ∈ B) (hc : t * y * t⁻¹ * y ∈ N) :
    QuotientGroup.mk' (N.subgroupOf B) ⟨t, ht⟩ * QuotientGroup.mk' (N.subgroupOf B) ⟨y, hy⟩ *
      (QuotientGroup.mk' (N.subgroupOf B) ⟨t, ht⟩)⁻¹ =
        (QuotientGroup.mk' (N.subgroupOf B) ⟨y, hy⟩)⁻¹ := by
  have hm : t * y * t⁻¹ * y ∈ B := B.mul_mem (B.mul_mem (B.mul_mem ht hy) (B.inv_mem ht)) hy
  have h1 := (mk_eq_one_iff hm).mpr hc
  have e : (⟨t * y * t⁻¹ * y, hm⟩ : ↥B) = ⟨t, ht⟩ * ⟨y, hy⟩ * (⟨t, ht⟩)⁻¹ * ⟨y, hy⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv] at h1
  exact eq_inv_of_mul_eq_one_left h1

omit [Finite G] in
theorem mk_pow_eq {B N : Subgroup G} [(N.subgroupOf B).Normal] {u v : G} (hu : u ∈ B)
    (hv : v ∈ B) {n : ℕ} (h : v * (u ^ n)⁻¹ ∈ N) :
    QuotientGroup.mk' (N.subgroupOf B) ⟨v, hv⟩ =
      QuotientGroup.mk' (N.subgroupOf B) ⟨u, hu⟩ ^ n := by
  rw [← mul_inv_eq_one, ← map_pow, ← map_inv, ← map_mul]
  exact (mk_eq_one_iff (B.mul_mem hv (B.inv_mem (B.pow_mem hu n)))).mpr h

omit [Finite G] in
theorem mk_pow_three {B N : Subgroup G} [(N.subgroupOf B).Normal] {y : G} (hy : y ∈ B)
    (h : y ^ 3 ∈ N) : QuotientGroup.mk' (N.subgroupOf B) ⟨y, hy⟩ ^ 3 = 1 := by
  rw [← map_pow]
  exact (mk_eq_one_iff (B.pow_mem hy 3)).mpr h

structure IsGenX (X T : Subgroup G) (x : G) : Prop where
  mem : x ∈ X
  cube : x ^ 3 = 1
  not_mem : x ∉ pCoreOf 2 (X ⊔ T)
  gen : ∀ x' ∈ X, ∃ j : ℕ, x' * (x ^ j)⁻¹ ∈ pCoreOf 2 (X ⊔ T)

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem exists_isGenX : ∃ x : G, IsGenX X T x := by
  obtain ⟨x, h1, h2, h3, h4⟩ := H.exists_x
  exact ⟨x, ⟨h1, h2, h3, h4⟩⟩

theorem conj_mem_inf {x : G} (hx : x ∈ X) {t : G} (ht : t ∈ T) :
    (t ∈ pCoreOf 2 (X ⊔ T) → ⁅t, x⁆ ∈ X ⊓ pCoreOf 2 (X ⊔ T)) ∧
    (t ∉ pCoreOf 2 (X ⊔ T) → t * x * t⁻¹ * x ∈ X ⊓ pCoreOf 2 (X ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxXT : x ∈ X ⊔ T := Subgroup.mem_sup_left hx
  have htXT : t ∈ X ⊔ T := Subgroup.mem_sup_right ht
  have htX : t * x * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (H.hTX ht) x).mp hx
  have hRn : X ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  constructor
  · intro htR
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact X.mul_mem htX (X.inv_mem hx)
    · have h1 : x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 (X ⊔ T) :=
        (Subgroup.mem_normalizer_iff.mp (hRn hxXT) t⁻¹).mp ((pCoreOf 2 (X ⊔ T)).inv_mem htR)
      have e : ⁅t, x⁆ = t * (x * t⁻¹ * x⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (pCoreOf 2 (X ⊔ T)).mul_mem htR h1
  · intro htR
    refine ⟨X.mul_mem htX hx, ?_⟩
    obtain ⟨e⟩ := H.hS3
    set ψ : ↥(X ⊔ T) →* Equiv.Perm (Fin 3) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T))) with hψ
    have hψk : ∀ y : ↥(X ⊔ T), ψ y = 1 → (y : G) ∈ pCoreOf 2 (X ⊔ T) := by
      intro y hy
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T)) y = 1 :=
        (map_eq_one_iff e.toMonoidHom e.injective).mp hy
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact (Lem3328.mem_pCore_iff _).mp h2
    have hσ : Equiv.Perm.sign (ψ ⟨t, htXT⟩) ≠ 1 := by
      intro hs
      have h3 : ψ ⟨t, htXT⟩ ^ 3 = 1 := One3323.pow_three_of_sign _ hs
      obtain ⟨k, hk⟩ := H.h.sylow.1 ⟨t, ht⟩
      have hk' : ψ ⟨t, htXT⟩ ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have : (⟨t, htXT⟩ : ↥(X ⊔ T)) ^ 2 ^ k = 1 := Subtype.ext (by
          have := congrArg Subtype.val hk
          simpa using this)
        rw [this, map_one]
      have h1 := pow_gcd_eq_one.mpr ⟨h3, hk'⟩
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at h1
      exact htR (hψk _ h1)
    have hx1 := sign_eq_one le_sup_left H.hXX ψ x hx
    have hmem : t * x * t⁻¹ * x ∈ X ⊔ T :=
      (X ⊔ T).mul_mem ((X ⊔ T).mul_mem ((X ⊔ T).mul_mem htXT hxXT) ((X ⊔ T).inv_mem htXT)) hxXT
    apply hψk ⟨t * x * t⁻¹ * x, hmem⟩
    have e1 : (⟨t * x * t⁻¹ * x, hmem⟩ : ↥(X ⊔ T)) =
        ⟨t, htXT⟩ * ⟨x, hxXT⟩ * (⟨t, htXT⟩)⁻¹ * ⟨x, hxXT⟩ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv]
    exact perm3_invert _ _ hσ hx1

theorem act_line (hB : IsB₀ X T D B₀) (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀)
    {x : G} (hx : x ∈ X) {g : G} (hg : g ∈ D) {t : G} (ht : t ∈ T) :
    (g⁻¹ * t * g ∈ pCoreOf 2 (X ⊔ T) → ⁅t, g * x * g⁻¹⁆ ∈ B₀) ∧
      (g⁻¹ * t * g ∉ pCoreOf 2 (X ⊔ T) →
        t * (g * x * g⁻¹) * t⁻¹ * (g * x * g⁻¹) ∈ B₀) := by
  have hXR := (H.cube_mem hB habel).2
  have hgB : g ∈ X ⊔ T ⊔ D := Subgroup.mem_sup_right hg
  have ht' : g⁻¹ * t * g ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (H.h.DN (D.inv_mem hg)) t).mp ht
    simpa using this
  obtain ⟨h1, h2⟩ := H.conj_mem_inf hx ht'
  have hconj : ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ := fun hb =>
    (Subgroup.mem_normalizer_iff.mp (hB.nor hgB) _).mp hb
  constructor
  · intro hR
    have := hconj (hXR (h1 hR))
    convert this using 1
    simp only [commutatorElement_def]
    group
  · intro hR
    have := hconj (hXR (h2 hR))
    convert this using 1
    group

theorem exists_lines : ∃ g ∈ D, ∃ h ∈ D, ∃ t₁ ∈ T, ∃ t₂ ∈ T,
    t₁ ∈ pCoreOf 2 (X ⊔ T) ∧ g⁻¹ * t₁ * g ∉ pCoreOf 2 (X ⊔ T) ∧
      h⁻¹ * t₁ * h ∉ pCoreOf 2 (X ⊔ T) ∧ t₂ ∉ pCoreOf 2 (X ⊔ T) ∧
        g⁻¹ * t₂ * g ∈ pCoreOf 2 (X ⊔ T) ∧ h⁻¹ * t₂ * h ∉ pCoreOf 2 (X ⊔ T) := by
  set R := pCoreOf 2 (X ⊔ T) with hR
  obtain ⟨K, hK⟩ : ∃ K : G → Subgroup G, ∀ g, K g = R.map (MulAut.conj g).toMonoidHom :=
    ⟨_, fun _ => rfl⟩
  have hmemK : ∀ g t : G, t ∈ K g ↔ g⁻¹ * t * g ∈ R := by
    intro g t
    rw [hK, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hK1 : K 1 = R := by
    ext t
    rw [hmemK]
    simp
  have hKmul : ∀ g h : G, K (g * h) = (K h).map (MulAut.conj g).toMonoidHom := by
    intro g h
    ext t
    rw [hmemK, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hmemK]
    constructor <;> intro ht <;> convert ht using 1 <;> group
  have hcard : ∀ g : G, Nat.card (K g) = Nat.card R := fun g => by
    rw [hK]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle : ∀ g h : G, K g ≤ K h → K g = K h := fun g h hgh =>
    Subgroup.eq_of_le_of_card_ge hgh (by rw [hcard, hcard])
  have hRle : ∀ g : G, R ≤ K g → R = K g := fun g hle' => by
    have := hle 1 g (by rwa [hK1])
    rwa [hK1] at this
  have hleR : ∀ g : G, K g ≤ R → K g = R := fun g hle' => by
    have := hle g 1 (by rwa [hK1])
    rwa [hK1] at this
  have hTn : ∀ {g : G}, g ∈ D → ∀ {t : G}, g⁻¹ * t * g ∈ T → t ∈ T := fun hg t ht => by
    have := (Subgroup.mem_normalizer_iff.mp (H.h.DN hg) _).mp ht
    simpa [mul_assoc] using this
  obtain ⟨g, hg, hgR⟩ : ∃ g ∈ D, K g ≠ R := by
    by_contra hcon
    push Not at hcon
    apply H.hD
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have h1 : t ∈ K g⁻¹ := by rw [hcon g⁻¹ (D.inv_mem hg)]; exact ht
      rw [hmemK, inv_inv] at h1
      exact h1
    · intro ht
      have h1 : g * t * g⁻¹ ∈ K g := by rw [hcon g hg]; exact ht
      rw [hmemK] at h1
      simpa [mul_assoc] using h1
  obtain ⟨h, hh, hhR, hhg⟩ : ∃ h ∈ D, K h ≠ R ∧ K h ≠ K g := by
    by_contra hcon
    push Not at hcon
    have hg2 : K (g * g) = R := by
      by_contra h2
      have h3 := hcon _ (D.mul_mem hg hg) h2
      apply hgR
      have h4 : (K g).map (MulAut.conj g).toMonoidHom = R.map (MulAut.conj g).toMonoidHom := by
        rw [← hKmul, h3, hK]
      exact Subgroup.map_injective (MulAut.conj g).injective h4
    have hpow : ∀ n : ℕ, K (g ^ (2 * n)) = R ∧ K (g ^ (2 * n + 1)) = K g := by
      intro n
      induction n with
      | zero => exact ⟨by simpa using hK1, by simp⟩
      | succ n ih =>
        have h1 : K (g ^ (2 * (n + 1))) = R := by
          rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ', hKmul, ih.2, ← hKmul, hg2]
        refine ⟨h1, ?_⟩
        rw [pow_succ', hKmul, h1, ← hK1, ← hKmul, mul_one]
    have hodd : Odd (orderOf g) :=
      Odd.of_dvd_nat H.h.Dodd (Subgroup.orderOf_dvd_natCard D hg)
    obtain ⟨n, hn⟩ := hodd
    have := (hpow n).2
    rw [← hn, pow_orderOf_eq_one, hK1] at this
    exact hgR this.symm
  have hgR' : ¬ R ≤ K g := fun h' => hgR (hRle g h').symm
  have hhR' : ¬ R ≤ K h := fun h' => hhR (hRle h h').symm
  have hgR'' : ¬ K g ≤ R := fun h' => hgR (hleR g h')
  have hgh : ¬ K g ≤ K h := fun h' => hhg (hle g h h').symm
  obtain ⟨t₁, ht₁R, ht₁g, ht₁h⟩ := exists_mem_not_mem_two hgR' hhR'
  obtain ⟨t₂, ht₂g, ht₂R, ht₂h⟩ := exists_mem_not_mem_two hgR'' hgh
  rw [hmemK] at ht₁g ht₁h ht₂g ht₂h
  exact ⟨g, hg, h, hh, t₁, H.R_le_T ht₁R, t₂, hTn hg (H.R_le_T ht₂g), ht₁R, ht₁g, ht₁h, ht₂R,
    ht₂g, ht₂h⟩

theorem conj_mem_pow (hB : IsB₀ X T D B₀) (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀)
    {x : G} (hx : IsGenX X T x) {d : G} (hd : d ∈ D) {x' : G} (hx' : x' ∈ X) :
    ∃ j : ℕ, (d * x' * d⁻¹) * ((d * x * d⁻¹) ^ j)⁻¹ ∈ B₀ := by
  have hXR := (H.cube_mem hB habel).2
  obtain ⟨j, hj⟩ := hx.gen x' hx'
  have h1 : x' * (x ^ j)⁻¹ ∈ B₀ :=
    hXR ⟨X.mul_mem hx' (X.inv_mem (X.pow_mem hx.mem j)), hj⟩
  refine ⟨j, ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (hB.nor (Subgroup.mem_sup_right hd)) _).mp h1
  convert this using 1
  rw [conj_pow]
  group

theorem mem_B₀_of_three (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) {k : G} (hk : k ∈ T ⊔ D)
    (hkT : ∀ s ∈ T, ⁅k, s⁆ ∈ B₀) {m : ℕ} (hkm : k ^ 3 ^ m ∈ B₀) : k ∈ B₀ := by
  set Y := conjClosure X D with hY
  obtain ⟨x, hx⟩ := H.exists_isGenX
  have hxB : x ∉ B₀ := fun h' => hx.not_mem (hB.inf ⟨Subgroup.mem_sup_left hx.mem, h'⟩)
  obtain ⟨-, hT₀, hlt⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  obtain ⟨r, hrR, hrB⟩ := Set.not_subset.mp (H.not_R_le_B₀ hT₀ hlt)
  have hN : (B₀.subgroupOf (X ⊔ T ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  set π := QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) with hπ
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hkB : k ∈ X ⊔ T ⊔ D := (sup_le hTB le_sup_right : T ⊔ D ≤ X ⊔ T ⊔ D) hk
  have hconjB₀ : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ :=
    fun hg b hb => (Subgroup.mem_normalizer_iff.mp (hB.nor hg) b).mp hb
  have hπk : π ⟨k, hkB⟩ ^ 3 ^ m = 1 := by
    rw [← map_pow]
    exact (mk_eq_one_iff ((X ⊔ T ⊔ D).pow_mem hkB _)).mpr hkm
  have hline : ∀ g ∈ D, ⁅k, g * x * g⁻¹⁆ ∈ B₀ := by
    intro g hg
    have hgB : g ∈ X ⊔ T ⊔ D := Subgroup.mem_sup_right hg
    have hy : g * x * g⁻¹ ∈ Y := mem_conjClosure hg hx.mem
    have hyB : g * x * g⁻¹ ∈ X ⊔ T ⊔ D := Y_le_B hy
    have hs : g * r * g⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (H.h.DN hg) r).mp (H.R_le_T hrR)
    have hsB : g * r * g⁻¹ ∉ B₀ := fun h' => hrB (by
      have := hconjB₀ ((X ⊔ T ⊔ D).inv_mem hgB) h'
      simpa [mul_assoc] using this)
    have hsy : ⁅g * r * g⁻¹, g * x * g⁻¹⁆ ∈ B₀ :=
      (H.act_line hB habel hx.mem hg hs).1 (by simpa [mul_assoc] using hrR)
    have hky : k * (g * x * g⁻¹) * k⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (H.hBY hkB) _).mp hy
    have hsB' : g * r * g⁻¹ ∈ X ⊔ T ⊔ D := hTB hs
    have hc1 : Commute (π ⟨g * r * g⁻¹, hsB'⟩) (π ⟨k, hkB⟩) :=
      (mk_comm_iff hsB' hkB).mpr (by
        have := hkT _ hs
        have e : ⁅g * r * g⁻¹, k⁆ = ⁅k, g * r * g⁻¹⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact B₀.inv_mem this)
    have hc2 : Commute (π ⟨g * r * g⁻¹, hsB'⟩) (π ⟨g * x * g⁻¹, hyB⟩) :=
      (mk_comm_iff hsB' hyB).mpr hsy
    have hsky : ⁅g * r * g⁻¹, k * (g * x * g⁻¹) * k⁻¹⁆ ∈ B₀ := by
      refine (mk_comm_iff hsB' (Y_le_B hky)).mp ?_
      have e : π ⟨k * (g * x * g⁻¹) * k⁻¹, Y_le_B hky⟩ =
          π ⟨k, hkB⟩ * π ⟨g * x * g⁻¹, hyB⟩ * (π ⟨k, hkB⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact ((hc1.mul_right hc2).mul_right hc1.inv_right).eq
    have hyB₀ : g * x * g⁻¹ ∉ B₀ := fun h' => hxB (by
      have := hconjB₀ ((X ⊔ T ⊔ D).inv_mem hgB) h'
      simpa [mul_assoc] using this)
    obtain ⟨j, hj⟩ := H.exists_pow_of_comm hA hB habel hs hsB hy hky hyB₀ hsy hsky
    have hq : π ⟨k, hkB⟩ * π ⟨g * x * g⁻¹, hyB⟩ * (π ⟨k, hkB⟩)⁻¹ =
        π ⟨g * x * g⁻¹, hyB⟩ ^ j := by
      have h1 := (mk_eq_one_iff ((X ⊔ T ⊔ D).mul_mem (Y_le_B hky)
        ((X ⊔ T ⊔ D).inv_mem ((X ⊔ T ⊔ D).pow_mem hyB j)))).mpr hj
      rw [← mul_inv_eq_one, ← map_pow, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    have hy3 : π ⟨g * x * g⁻¹, hyB⟩ ^ 3 = 1 := by
      rw [← map_pow]
      refine (mk_eq_one_iff ((X ⊔ T ⊔ D).pow_mem hyB 3)).mpr ?_
      rw [conj_pow, hx.cube, mul_one, mul_inv_cancel]
      exact B₀.one_mem
    have hj0 : j % 3 ≠ 0 := by
      intro hj0
      apply hyB₀
      have h1 : π ⟨g * x * g⁻¹, hyB⟩ ^ j = 1 := by
        rw [pow_eq_pow_mod j hy3, hj0, pow_zero]
      rw [← hq] at h1
      have h2 : π ⟨g * x * g⁻¹, hyB⟩ = 1 := by
        have := congrArg (fun q => (π ⟨k, hkB⟩)⁻¹ * q * π ⟨k, hkB⟩) h1
        simpa [mul_assoc] using this
      exact (mk_eq_one_iff hyB).mp h2
    exact (mk_comm_iff hkB hyB).mp (commute_of_three hy3 hq hj0 hπk)
  refine H.mem_of_centralizes_TD hB hk fun y hy => ?_
  have hYC : Y ≤ ((Subgroup.centralizer {π ⟨k, hkB⟩}).comap π).map (X ⊔ T ⊔ D).subtype := by
    refine conjClosure_le fun d hd x' hx' => ?_
    have hdx : d * x' * d⁻¹ ∈ X ⊔ T ⊔ D := Y_le_B (mem_conjClosure hd hx')
    have hdxB : d * x * d⁻¹ ∈ X ⊔ T ⊔ D := Y_le_B (mem_conjClosure hd hx.mem)
    refine ⟨⟨_, hdx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨j, hj⟩ := H.conj_mem_pow hB habel hx hd hx'
    have e : π ⟨d * x' * d⁻¹, hdx⟩ = π ⟨d * x * d⁻¹, hdxB⟩ ^ j := by
      rw [← mul_inv_eq_one, ← map_pow, ← map_inv, ← map_mul]
      exact (mk_eq_one_iff ((X ⊔ T ⊔ D).mul_mem hdx
        ((X ⊔ T ⊔ D).inv_mem ((X ⊔ T ⊔ D).pow_mem hdxB j)))).mpr hj
    have hc : Commute (π ⟨k, hkB⟩) (π ⟨d * x * d⁻¹, hdxB⟩) :=
      (mk_comm_iff hkB hdxB).mpr (hline d hd)
    rw [e]
    exact ((hc.pow_right j).eq).symm
  obtain ⟨⟨y', hy'B⟩, hy', rfl⟩ := hYC hy
  rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hy'
  exact (mk_comm_iff hkB hy'B).mp hy'.symm

theorem pCore_le_map (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    CFSG.pCore 3 (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) ≤
      ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
        (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hTDB : T ⊔ D ≤ X ⊔ T ⊔ D := sup_le hTB le_sup_right
  have hYP := H.map_le_pCore hB habel
  intro q hq
  obtain ⟨⟨c, hc⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨y, hy, k, hk, rfl⟩ := H.mem_Y_TD hc
  have hkB : k ∈ X ⊔ T ⊔ D := hTDB hk
  have hyB : y ∈ X ⊔ T ⊔ D := Y_le_B hy
  have hymem : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨y, hyB⟩ ∈
      ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
        (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))) :=
    Subgroup.mem_map.mpr ⟨⟨y, hyB⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have e : (⟨y * k, hc⟩ : ↥(X ⊔ T ⊔ D)) = ⟨y, hyB⟩ * ⟨k, hkB⟩ := rfl
  have hkP : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨k, hkB⟩ ∈
      CFSG.pCore 3 (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) := by
    have h1 := (CFSG.pCore 3 _).mul_mem ((CFSG.pCore 3 _).inv_mem (hYP hymem)) hq
    rwa [e, map_mul, inv_mul_cancel_left] at h1
  have hkT : ∀ s ∈ T, ⁅k, s⁆ ∈ B₀ := by
    intro s hs
    have hsB := hTB hs
    have hks : ⁅k, s⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp
        (sup_le Subgroup.le_normalizer H.h.DN hk) s).mp hs) (T.inv_mem hs)
    have hksB : ⁅k, s⁆ ∈ X ⊔ T ⊔ D := hTB hks
    have h1 : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨⁅k, s⁆, hksB⟩ ∈
        CFSG.pCore 3 (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) := by
      have e2 : (⟨⁅k, s⁆, hksB⟩ : ↥(X ⊔ T ⊔ D)) =
          ⟨k, hkB⟩ * (⟨s, hsB⟩ * (⟨k, hkB⟩)⁻¹ * (⟨s, hsB⟩)⁻¹) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact (CFSG.pCore 3 _).mul_mem hkP (CFSG.pCore_normal.conj_mem _
        ((CFSG.pCore 3 _).inv_mem hkP) _)
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup ⟨_, h1⟩
    obtain ⟨b, hb⟩ := H.h.sylow.1 ⟨_, hks⟩
    have ha' : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨⁅k, s⁆, hksB⟩ ^ 3 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hb' : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨⁅k, s⁆, hksB⟩ ^ 2 ^ b = 1 := by
      rw [← map_pow]
      have : (⟨⁅k, s⁆, hksB⟩ : ↥(X ⊔ T ⊔ D)) ^ 2 ^ b = 1 := Subtype.ext (by
        have := congrArg Subtype.val hb
        simpa using this)
      rw [this, map_one]
    have h2 := pow_gcd_eq_one.mpr ⟨ha', hb'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow a b (by norm_num)), pow_one] at h2
    exact (mk_eq_one_iff hksB).mp h2
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup ⟨_, hkP⟩
  have hka : k ^ 3 ^ a ∈ B₀ := by
    have h1 : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨k, hkB⟩ ^ 3 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    rw [← map_pow] at h1
    exact (mk_eq_one_iff ((X ⊔ T ⊔ D).pow_mem hkB _)).mp h1
  have hk1 : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨k, hkB⟩ = 1 :=
    (mk_eq_one_iff hkB).mpr (H.mem_B₀_of_three hA hB habel hk hkT hka)
  rw [e, map_mul, hk1, mul_one]
  exact hymem

theorem isElementaryAbelian_map (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    CFSG.IsElementaryAbelian 3 ↥(((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
      (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)))) := by
  have hY3 := (H.cube_mem hB habel).1
  refine { is_comm := ⟨fun p q => ?_⟩, exponent_dvd_p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun p => ?_ }
  · obtain ⟨p, hp⟩ := p
    obtain ⟨q, hq⟩ := q
    obtain ⟨⟨y, hyB⟩, hy, rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨⟨z, hzB⟩, hz, rfl⟩ := Subgroup.mem_map.mp hq
    exact Subtype.ext ((mk_comm_iff hyB hzB).mpr (habel (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp hy) (Subgroup.mem_subgroupOf.mp hz))))
  · obtain ⟨p, hp⟩ := p
    obtain ⟨⟨y, hyB⟩, hy, rfl⟩ := Subgroup.mem_map.mp hp
    exact Subtype.ext (mk_pow_three hyB (hY3 y (Subgroup.mem_subgroupOf.mp hy)))

theorem lines_span (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) {x : G} (hx : IsGenX X T x)
    {g h t₁ t₂ : G} (hg : g ∈ D) (hh : h ∈ D) (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (h1R : t₁ ∈ pCoreOf 2 (X ⊔ T)) (h1g : g⁻¹ * t₁ * g ∉ pCoreOf 2 (X ⊔ T))
    (h1h : h⁻¹ * t₁ * h ∉ pCoreOf 2 (X ⊔ T)) (h2R : t₂ ∉ pCoreOf 2 (X ⊔ T))
    (h2g : g⁻¹ * t₂ * g ∈ pCoreOf 2 (X ⊔ T)) (h2h : h⁻¹ * t₂ * h ∉ pCoreOf 2 (X ⊔ T))
    {d : G} (hd : d ∈ D) :
    ∃ n : ℕ, d * x * d⁻¹ * (x ^ n)⁻¹ ∈ B₀ ∨ d * x * d⁻¹ * ((g * x * g⁻¹) ^ n)⁻¹ ∈ B₀ ∨
      d * x * d⁻¹ * ((h * x * h⁻¹) ^ n)⁻¹ ∈ B₀ := by
  have hTR : ∀ {t : G}, t ∈ T → t ∈ B₀ → t ∈ pCoreOf 2 (X ⊔ T) := fun ht htB =>
    hB.inf ⟨Subgroup.mem_sup_right ht, htB⟩
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hxB : x ∉ B₀ := fun h' => hx.not_mem (hB.inf ⟨Subgroup.mem_sup_left hx.mem, h'⟩)
  have hconjB₀ : ∀ {e : G}, e ∈ D → ∀ {b : G}, b ∈ B₀ → e * b * e⁻¹ ∈ B₀ := fun he b hb =>
    (Subgroup.mem_normalizer_iff.mp (hB.nor (Subgroup.mem_sup_right he)) b).mp hb
  have hlY : ∀ {e : G}, e ∈ D → e * x * e⁻¹ ∈ conjClosure X D := fun he =>
    mem_conjClosure he hx.mem
  have hlB : ∀ {e : G}, e ∈ D → e * x * e⁻¹ ∉ B₀ := fun he h' => hxB (by
    have := hconjB₀ (D.inv_mem he) h'
    simpa [mul_assoc] using this)
  have hxY : x ∈ conjClosure X D := le_conjClosure X D hx.mem
  have hone : ∀ {t : G}, (1 : G)⁻¹ * t * 1 = t := fun {t} => by group
  have hx1 : (1 : G) * x * (1 : G)⁻¹ = x := by group
  have ht₁B : t₁ ∉ B₀ := fun h' => h1g (hTR (by
    have := (Subgroup.mem_normalizer_iff.mp (H.h.DN (D.inv_mem hg)) t₁).mp ht₁
    simpa using this) (by
    have := hconjB₀ (D.inv_mem hg) h'
    simpa using this))
  have ht₂B : t₂ ∉ B₀ := fun h' => h2R (hTR ht₂ h')
  have ht₁₂ : t₁ * t₂ ∈ T := T.mul_mem ht₁ ht₂
  have ht₁₂B : t₁ * t₂ ∉ B₀ := fun h' => h2R (by
    have h1 := hTR ht₁₂ h'
    have := (pCoreOf 2 (X ⊔ T)).mul_mem ((pCoreOf 2 (X ⊔ T)).inv_mem h1R) h1
    simpa using this)
  have a1 : ⁅t₁, x⁆ ∈ B₀ := by
    have := (H.act_line hB habel hx.mem D.one_mem ht₁).1 (by rw [hone]; exact h1R)
    rwa [hx1] at this
  by_cases hd1 : d⁻¹ * t₁ * d ∈ pCoreOf 2 (X ⊔ T)
  · obtain ⟨n, hn⟩ := H.exists_pow_of_comm hA hB habel ht₁ ht₁B hxY (hlY hd) hxB a1
      ((H.act_line hB habel hx.mem hd ht₁).1 hd1)
    exact ⟨n, Or.inl hn⟩
  by_cases hd2 : d⁻¹ * t₂ * d ∈ pCoreOf 2 (X ⊔ T)
  · obtain ⟨n, hn⟩ := H.exists_pow_of_comm hA hB habel ht₂ ht₂B (hlY hg) (hlY hd) (hlB hg)
      ((H.act_line hB habel hx.mem hg ht₂).1 h2g) ((H.act_line hB habel hx.mem hd ht₂).1 hd2)
    exact ⟨n, Or.inr (Or.inl hn)⟩
  have hfix : ∀ {e : G}, e ∈ D → e⁻¹ * t₁ * e ∉ pCoreOf 2 (X ⊔ T) →
      e⁻¹ * t₂ * e ∉ pCoreOf 2 (X ⊔ T) → ⁅t₁ * t₂, e * x * e⁻¹⁆ ∈ B₀ := fun he h1 h2 =>
    comm_mem_of_inv (hB.nor (hTB ht₁)) (hB.nor (Y_le_B (hlY he)))
      ((H.act_line hB habel hx.mem he ht₂).2 h2) ((H.act_line hB habel hx.mem he ht₁).2 h1)
  obtain ⟨n, hn⟩ := H.exists_pow_of_comm hA hB habel ht₁₂ ht₁₂B (hlY hh) (hlY hd) (hlB hh)
    (hfix hh h1h h2h) (hfix hd hd1 hd2)
  exact ⟨n, Or.inr (Or.inr hn)⟩

theorem card_map (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    {x : G} (hx : IsGenX X T x) {g h t₁ t₂ : G} (hg : g ∈ D) (hh : h ∈ D) (ht₁ : t₁ ∈ T)
    (ht₂ : t₂ ∈ T) (h1R : t₁ ∈ pCoreOf 2 (X ⊔ T)) (h1g : g⁻¹ * t₁ * g ∉ pCoreOf 2 (X ⊔ T))
    (h1h : h⁻¹ * t₁ * h ∉ pCoreOf 2 (X ⊔ T)) (h2R : t₂ ∉ pCoreOf 2 (X ⊔ T))
    (h2g : g⁻¹ * t₂ * g ∈ pCoreOf 2 (X ⊔ T)) (h2h : h⁻¹ * t₂ * h ∉ pCoreOf 2 (X ⊔ T)) :
    Nat.card ↥(((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
      (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)))) = 27 := by
  have hY3 := (H.cube_mem hB habel).1
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hxB : x ∉ B₀ := fun h' => hx.not_mem (hB.inf ⟨Subgroup.mem_sup_left hx.mem, h'⟩)
  have hlY : ∀ {e : G}, e ∈ D → e * x * e⁻¹ ∈ conjClosure X D := fun he =>
    mem_conjClosure he hx.mem
  have hlB : ∀ {e : G}, e ∈ D → e * x * e⁻¹ ∉ B₀ := fun he h' => hxB (by
    have := (Subgroup.mem_normalizer_iff.mp (hB.nor (Subgroup.mem_sup_right (D.inv_mem he)))
      _).mp h'
    simpa [mul_assoc] using this)
  have hxY : x ∈ conjClosure X D := le_conjClosure X D hx.mem
  have hone : ∀ {t : G}, (1 : G)⁻¹ * t * 1 = t := fun {t} => by group
  have hx1 : (1 : G) * x * (1 : G)⁻¹ = x := by group
  have a1 : ⁅t₁, x⁆ ∈ B₀ := by
    have := (H.act_line hB habel hx.mem D.one_mem ht₁).1 (by rw [hone]; exact h1R)
    rwa [hx1] at this
  have a2 : t₂ * x * t₂⁻¹ * x ∈ B₀ := by
    have := (H.act_line hB habel hx.mem D.one_mem ht₂).2 (by rw [hone]; exact h2R)
    rwa [hx1] at this
  have r1a := mk_conj_eq_of_comm (hTB ht₁) (Y_le_B hxY) a1
  have r1b := mk_conj_eq_inv (hTB ht₁) (Y_le_B (hlY hg))
    ((H.act_line hB habel hx.mem hg ht₁).2 h1g)
  have r1c := mk_conj_eq_inv (hTB ht₁) (Y_le_B (hlY hh))
    ((H.act_line hB habel hx.mem hh ht₁).2 h1h)
  have r2a := mk_conj_eq_inv (hTB ht₂) (Y_le_B hxY) a2
  have r2b := mk_conj_eq_of_comm (hTB ht₂) (Y_le_B (hlY hg))
    ((H.act_line hB habel hx.mem hg ht₂).1 h2g)
  have r2c := mk_conj_eq_inv (hTB ht₂) (Y_le_B (hlY hh))
    ((H.act_line hB habel hx.mem hh ht₂).2 h2h)
  have hcomm : ∀ {y z : G} (hy : y ∈ conjClosure X D) (hz : z ∈ conjClosure X D),
      Commute (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨y, Y_le_B hy⟩)
        (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨z, Y_le_B hz⟩) := fun hy hz =>
    (mk_comm_iff _ _).mpr (habel (Subgroup.commutator_mem_commutator hy hz))
  have hcube : ∀ {y : G} (hy : y ∈ conjClosure X D),
      QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨y, Y_le_B hy⟩ ^ 3 = 1 :=
    fun {y} hy => mk_pow_three (Y_le_B hy) (hY3 y hy)
  have hne : ∀ {y : G} (hy : y ∈ X ⊔ T ⊔ D), y ∉ B₀ →
      QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨y, hy⟩ ≠ 1 := fun hy hyB h' =>
    hyB ((mk_eq_one_iff hy).mp h')
  set a := QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨x, Y_le_B hxY⟩ with ha
  set b := QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨g * x * g⁻¹, Y_le_B (hlY hg)⟩ with hb
  set c := QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨h * x * h⁻¹, Y_le_B (hlY hh)⟩ with hc
  have hab : Commute a b := hcomm hxY (hlY hg)
  have hac : Commute a c := hcomm hxY (hlY hh)
  have hbc : Commute b c := hcomm (hlY hg) (hlY hh)
  have ha3 : a ^ 3 = 1 := hcube hxY
  have hb3 : b ^ 3 = 1 := hcube (hlY hg)
  have hc3 : c ^ 3 = 1 := hcube (hlY hh)
  let SM : Subgroup (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) :=
    { carrier := {q | ∃ i j l : ℕ, q = a ^ i * b ^ j * c ^ l}
      mul_mem' := by
        rintro _ _ ⟨i, j, l, rfl⟩ ⟨i', j', l', rfl⟩
        exact ⟨i + i', j + j', l + l', mul_triple hab hac hbc i j l i' j' l'⟩
      one_mem' := ⟨0, 0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, l, rfl⟩
        refine ⟨2 * i, 2 * j, 2 * l, (eq_inv_of_mul_eq_one_left ?_).symm⟩
        rw [mul_triple hab hac hbc, show 2 * i + i = 3 * i by ring,
          show 2 * j + j = 3 * j by ring, show 2 * l + l = 3 * l by ring, pow_mul, pow_mul,
          pow_mul, ha3, hb3, hc3, one_pow, one_pow, one_pow, mul_one, mul_one] }
  have hYSM : conjClosure X D ≤
      (SM.comap (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)))).map (X ⊔ T ⊔ D).subtype := by
    refine conjClosure_le fun d hd x' hx' => ?_
    have hdx : d * x' * d⁻¹ ∈ X ⊔ T ⊔ D := Y_le_B (mem_conjClosure hd hx')
    refine ⟨⟨_, hdx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    obtain ⟨j, hj⟩ := H.conj_mem_pow hB habel hx hd hx'
    rw [mk_pow_eq (Y_le_B (hlY hd)) hdx hj]
    obtain ⟨n, hn⟩ := H.lines_span hA hB habel hx hg hh ht₁ ht₂ h1R h1g h1h h2R h2g h2h hd
    rcases hn with hn | hn | hn
    · rw [mk_pow_eq (Y_le_B hxY) (Y_le_B (hlY hd)) hn, ← pow_mul]
      exact ⟨n * j, 0, 0, by simp [ha]⟩
    · rw [mk_pow_eq (Y_le_B (hlY hg)) (Y_le_B (hlY hd)) hn, ← pow_mul]
      exact ⟨0, n * j, 0, by simp [hb]⟩
    · rw [mk_pow_eq (Y_le_B (hlY hh)) (Y_le_B (hlY hd)) hn, ← pow_mul]
      exact ⟨0, 0, n * j, by simp [hc]⟩
  have hspan : ∀ q ∈ ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
      (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))), ∃ i j l : ℕ, q = a ^ i * b ^ j * c ^ l := by
    intro q hq
    obtain ⟨⟨y, hyB⟩, hy, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨⟨y', hy'B⟩, hy', e⟩ := hYSM (Subgroup.mem_subgroupOf.mp hy)
    have : (⟨y', hy'B⟩ : ↥(X ⊔ T ⊔ D)) = ⟨y, hyB⟩ := Subtype.ext e
    rw [← this]
    exact hy'
  have hmem : ∀ {y : G} (hy : y ∈ conjClosure X D),
      QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨y, Y_le_B hy⟩ ∈
        ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
          (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))) := fun hy =>
    Subgroup.mem_map.mpr ⟨⟨_, Y_le_B hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  exact card_eq_of_three (hmem hxY) (hmem (hlY hg)) (hmem (hlY hh)) hab hac hbc ha3 hb3 hc3
    (hne (Y_le_B hxY) hxB) (hne (Y_le_B (hlY hg)) (hlB hg)) (hne (Y_le_B (hlY hh)) (hlB hh))
    r1a r1b r1c r2a r2b r2c hspan

theorem one_lt_pRank_two (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    {t₁ t₂ : G} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T) (ht₁B : t₁ ∉ B₀) (ht₂B : t₂ ∉ B₀)
    (ht₁₂ : t₁ * t₂⁻¹ ∉ B₀) :
    1 < CFSG.pRank 2 (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsq, hcommT⟩ := H.sq_comm_mem hB habel
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  set Th := (T.subgroupOf (X ⊔ T ⊔ D)).map (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)))
    with hTh
  have hTEA : CFSG.IsElementaryAbelian 2 ↥Th := by
    refine { is_comm := ⟨fun p q => ?_⟩, exponent_dvd_p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun p => ?_ }
    · obtain ⟨p, hp⟩ := p
      obtain ⟨q, hq⟩ := q
      obtain ⟨⟨s, hsB⟩, hs, rfl⟩ := Subgroup.mem_map.mp hp
      obtain ⟨⟨s', hs'B⟩, hs', rfl⟩ := Subgroup.mem_map.mp hq
      exact Subtype.ext ((mk_comm_iff hsB hs'B).mpr (hcommT s (Subgroup.mem_subgroupOf.mp hs)
        s' (Subgroup.mem_subgroupOf.mp hs')))
    · obtain ⟨p, hp⟩ := p
      obtain ⟨⟨s, hsB⟩, hs, rfl⟩ := Subgroup.mem_map.mp hp
      refine Subtype.ext ?_
      show QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨s, hsB⟩ ^ 2 = 1
      rw [pow_two, ← map_mul]
      exact (mk_eq_one_iff ((X ⊔ T ⊔ D).mul_mem hsB hsB)).mpr
        (hsq s (Subgroup.mem_subgroupOf.mp hs))
  have hmem : ∀ {t : G} (ht : t ∈ T),
      QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨t, hTB ht⟩ ∈ Th := fun ht =>
    Subgroup.mem_map.mpr ⟨⟨_, hTB ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥Th).exists_card_eq
  have h3 : 3 ≤ Nat.card ↥Th := by
    refine three_le_card (a := ⟨_, hmem ht₁⟩) (b := ⟨_, hmem ht₂⟩) (fun h' => ht₁B ?_)
      (fun h' => ht₂B ?_) (fun h' => ht₁₂ ?_)
    · exact (mk_eq_one_iff (hTB ht₁)).mp (congrArg Subtype.val h')
    · exact (mk_eq_one_iff (hTB ht₂)).mp (congrArg Subtype.val h')
    · have h1 := congrArg Subtype.val h'
      refine (mk_eq_one_iff ((X ⊔ T ⊔ D).mul_mem (hTB ht₁)
        ((X ⊔ T ⊔ D).inv_mem (hTB ht₂)))).mp ?_
      have e : (⟨t₁ * t₂⁻¹, (X ⊔ T ⊔ D).mul_mem (hTB ht₁) ((X ⊔ T ⊔ D).inv_mem (hTB ht₂))⟩ :
          ↥(X ⊔ T ⊔ D)) = ⟨t₁, hTB ht₁⟩ * (⟨t₂, hTB ht₂⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv, mul_inv_eq_one]
      exact h1
  have hn2 : 2 ≤ n := by
    have h3' : 3 ≤ 2 ^ n := hn ▸ h3
    rcases n with _ | _ | n
    · norm_num at h3'
    · norm_num at h3'
    · omega
  have := le_pRank_of_elemAb (by norm_num : 1 < 2) hTEA hn
  omega

theorem not_abel (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) :
    ¬ ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀ := by
  intro habel
  have hN : (B₀.subgroupOf (X ⊔ T ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  have hTR : ∀ {t : G}, t ∈ T → t ∈ B₀ → t ∈ pCoreOf 2 (X ⊔ T) := fun ht htB =>
    hB.inf ⟨Subgroup.mem_sup_right ht, htB⟩
  obtain ⟨-, -, hA3⟩ := hA _ 3 Nat.prime_three (by norm_num) H.pRank_three_le
    (B₀.subgroupOf (X ⊔ T ⊔ D)) (H.fStar_eq hB habel)
  have hP := le_antisymm (H.pCore_le_map hA hB habel) (H.map_le_pCore hB habel)
  obtain ⟨x, hx⟩ := H.exists_isGenX
  obtain ⟨g, hg, h, hh, t₁, ht₁, t₂, ht₂, h1R, h1g, h1h, h2R, h2g, h2h⟩ := H.exists_lines
  have hcard := H.card_map hA hB habel hx hg hh ht₁ ht₂ h1R h1g h1h h2R h2g h2h
  have ht₁B : t₁ ∉ B₀ := fun h' => h1g (hTR (by
    have := (Subgroup.mem_normalizer_iff.mp (H.h.DN (D.inv_mem hg)) t₁).mp ht₁
    simpa using this) (by
    have := (Subgroup.mem_normalizer_iff.mp (hB.nor (Subgroup.mem_sup_right (D.inv_mem hg)))
      t₁).mp h'
    simpa using this))
  have ht₂B : t₂ ∉ B₀ := fun h' => h2R (hTR ht₂ h')
  have ht₁₂ : t₁ * t₂⁻¹ ∉ B₀ := fun h' => h2R (by
    have h1 := hTR (T.mul_mem ht₁ (T.inv_mem ht₂)) h'
    have := (pCoreOf 2 (X ⊔ T)).mul_mem ((pCoreOf 2 (X ⊔ T)).inv_mem h1) h1R
    simpa using this)
  have hm2 := H.one_lt_pRank_two hB habel ht₁ ht₂ ht₁B ht₂B ht₁₂
  obtain ⟨K, hKn, hK1, hK2⟩ := hA3 (by rw [hP]; exact H.isElementaryAbelian_map hB habel)
    (by rw [hP]; exact hcard.trans (by norm_num)) hm2
  rw [hP] at hK2
  obtain ⟨q, hqK, hq1⟩ := IsConcreteLE.exists_of_lt hK1
  set K' : Subgroup G :=
    (K.comap (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)))).map (X ⊔ T ⊔ D).subtype with hK'
  have hK'B : K' ≤ X ⊔ T ⊔ D := Subgroup.map_subtype_le _
  have hB₀K' : B₀ ≤ K' := fun b hb => ⟨⟨b, hB.le hb⟩, by
    rw [SetLike.mem_coe, Subgroup.mem_comap, (mk_eq_one_iff (hB.le hb)).mpr hb]
    exact K.one_mem, rfl⟩
  have hlt : B₀ < K' := by
    refine lt_of_le_of_ne hB₀K' fun heq => hq1 ?_
    obtain ⟨⟨c', hc'⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hcK : c' ∈ K' := ⟨⟨c', hc'⟩, hqK, rfl⟩
    rw [← heq] at hcK
    exact (Subgroup.mem_bot).mpr ((mk_eq_one_iff hc').mpr hcK)
  have hK'n : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K' : Set G) := by
    refine Main3324.le_normalizer_of_conj fun g' hg' k hk => ?_
    obtain ⟨k', hk', rfl⟩ := hk
    refine ⟨⟨g', hg'⟩ * k' * (⟨g', hg'⟩)⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hKn.conj_mem _ hk' _
  have hYK := (H.X_le_of_normal hK'n (hB.max _ hlt hK'B hK'n)).2
  have hŶK : ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
      (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))) ≤ K := by
    intro q' hq'
    obtain ⟨⟨y, hyB⟩, hy, rfl⟩ := Subgroup.mem_map.mp hq'
    obtain ⟨k', hk', hk'e⟩ := hYK (Subgroup.mem_subgroupOf.mp hy)
    have : k' = ⟨y, hyB⟩ := Subtype.ext hk'e
    rw [← this]
    exact hk'
  exact hK2.not_ge hŶK

theorem le_commutator_sup (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) :
    conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀ :=
  (H.commutator_le_or hB).resolve_left (H.not_abel hA hB)

end Hyp3320

end S3320

end CFSG.Quasithin.H13
