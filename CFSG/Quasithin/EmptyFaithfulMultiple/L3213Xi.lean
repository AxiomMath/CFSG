module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L3213

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem pCoreOf_le_sectionCentralizer (X : Subgroup G) :
    pCoreOf 2 X ≤ sectionCentralizer X (pCoreOf 2 X) := by
  intro c hc
  have hcX : c ∈ X := pCoreOf_le 2 X hc
  refine ⟨Subgroup.le_normalizer hcX, le_normalizer_pCoreOf 2 X hcX, fun x hx => ?_⟩
  have h1 : x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 X :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X hx) c⁻¹).mp
      ((pCoreOf 2 X).inv_mem hc)
  have e : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 X).mul_mem hc h1

theorem conj_mem_sectionCentralizer {X K : Subgroup G} {n g : G}
    (hnX : n ∈ Subgroup.normalizer (X : Set G)) (hnK : n ∈ Subgroup.normalizer (K : Set G))
    (hg : g ∈ sectionCentralizer X K) : n * g * n⁻¹ ∈ sectionCentralizer X K := by
  obtain ⟨hgX, hgK, hgc⟩ := hg
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hnX hgX) (Subgroup.inv_mem _ hnX),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hnK hgK) (Subgroup.inv_mem _ hnK), fun x hx => ?_⟩
  have hy : n⁻¹ * x * n ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnX) x).mp hx
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp hnK _).mp (hgc _ hy)
  have e : n * g * n⁻¹ * x * (n * g * n⁻¹)⁻¹ * x⁻¹ =
      n * (g * (n⁻¹ * x * n) * g⁻¹ * (n⁻¹ * x * n)⁻¹) * n⁻¹ := by group
  rw [e]
  exact h1

theorem le_of_le_sup_commutator {N X : Subgroup G} (hn : X ≤ Subgroup.normalizer (N : Set G))
    (hsolv : Group.IsSolvable X) (h : X ≤ N ⊔ ⁅X, X⁆) : X ≤ N := by
  let D : ℕ → Subgroup G := fun k => (derivedSeries X k).map X.subtype
  have hD0 : D 0 = X := by
    simp only [D, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDs : ∀ k, D (k + 1) = ⁅D k, D k⁆ := fun k => by
    simp only [D, derivedSeries_succ, Subgroup.map_commutator]
  have hDX : ∀ k, D k ≤ X := fun k => Subgroup.map_subtype_le _
  have key : ∀ k, X ≤ N ⊔ D k := by
    intro k
    induction k with
    | zero => rw [hD0]; exact le_sup_right
    | succ k ih =>
      calc X ≤ N ⊔ ⁅X, X⁆ := h
        _ ≤ N ⊔ ⁅N ⊔ D k, N ⊔ D k⁆ := sup_le_sup_left (Subgroup.commutator_mono ih ih) _
        _ ≤ N ⊔ (N ⊔ ⁅D k, D k⁆) :=
          sup_le_sup_left (commutator_sup_le ((hDX k).trans hn)) _
        _ = N ⊔ D (k + 1) := by rw [hDs, ← sup_assoc, sup_idem]
  obtain ⟨n, hn'⟩ := (Group.isSolvable_def X).mp hsolv
  have h1 := key n
  have h2 : D n = ⊥ := by simp only [D, hn', Subgroup.map_bot]
  rwa [h2, sup_bot_eq] at h1

section Finite

variable [Finite G] {T X : Subgroup G}

theorem xi_commutator_mem_of_mem_frattini (hX : IsXi T X) {a b : G} (ha : a ∈ X)
    (hb : b ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X) : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 X := by
  obtain ⟨p, hp, hp2, hpX, -, -⟩ := hX.exists_prime_sup_eq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge p (bot_le : (⊥ : Subgroup G) ≤ X) IsPGroup.of_bot
  set Q := pCoreOf 2 X with hQ
  have hXP : Q ⊔ P = X := hX.pCoreOf_sup_eq hp2 hpX hP
  have hcomm : ⁅X, X⁆ ≤ Q ⊔ ⁅P, P⁆ := hX.commutator_le hp2 hpX hP
  have hPdvd : Nat.card P ∣ p ^ 3 := by
    obtain ⟨k, -, hk3, hk⟩ := hX.relIndex_eq hp hp2 hpX
    rw [hX.card_sylow hp2 hpX hP, hk]
    exact pow_dvd_pow p hk3
  have hPc := commutator_le_centralizer_of_card_dvd hPdvd
  have hQn : X ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 X
  have hconj : ∀ y ∈ X, ∀ c ∈ Q, y * c * y⁻¹ ∈ Q := fun y hy c hc =>
    (Subgroup.mem_normalizer_iff.mp (hQn hy) c).mp hc
  let Z₂ : Subgroup G :=
    { carrier := {b | b ∈ X ∧ ∀ a ∈ X, a * b * a⁻¹ * b⁻¹ ∈ Q}
      one_mem' := ⟨X.one_mem, fun a _ => by simp [Q.one_mem]⟩
      mul_mem' := by
        rintro b₁ b₂ ⟨hb₁, hb₁'⟩ ⟨hb₂, hb₂'⟩
        refine ⟨X.mul_mem hb₁ hb₂, fun a ha => ?_⟩
        have e : a * (b₁ * b₂) * a⁻¹ * (b₁ * b₂)⁻¹ =
            (a * b₁ * a⁻¹ * b₁⁻¹) * (b₁ * (a * b₂ * a⁻¹ * b₂⁻¹) * b₁⁻¹) := by group
        rw [e]
        exact Q.mul_mem (hb₁' a ha) (hconj b₁ hb₁ _ (hb₂' a ha))
      inv_mem' := by
        rintro b ⟨hb, hb'⟩
        refine ⟨X.inv_mem hb, fun a ha => ?_⟩
        have e : a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = b⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * b⁻¹⁻¹ := by group
        rw [e]
        exact hconj b⁻¹ (X.inv_mem hb) _ (Q.inv_mem (hb' a ha)) }
  have hQZ : Q ≤ Z₂ := fun c hc => ⟨pCoreOf_le 2 X hc, fun a ha =>
    Q.mul_mem (hconj a ha c hc) (Q.inv_mem hc)⟩
  have hPZ : ⁅P, P⁆ ≤ Z₂ := by
    intro c hc
    have hcP : c ∈ P := commutator_le_self P hc
    refine ⟨hP.le hcP, fun a ha => ?_⟩
    rw [← hXP] at ha
    obtain ⟨q, hq, s, hs, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (hP.le.trans hQn)).1 ha
    have hsc : s * c = c * s := Subgroup.mem_centralizer_iff.mp (hPc hc) s hs
    have hc' : c * q⁻¹ * c⁻¹ ∈ Q := hconj c (hP.le hcP) _ (Q.inv_mem hq)
    have e : q * s * c * (q * s)⁻¹ * c⁻¹ = q * (c * q⁻¹ * c⁻¹) := by
      calc q * s * c * (q * s)⁻¹ * c⁻¹ = q * (s * c) * s⁻¹ * q⁻¹ * c⁻¹ := by group
        _ = q * (c * s) * s⁻¹ * q⁻¹ * c⁻¹ := by rw [hsc]
        _ = q * (c * q⁻¹ * c⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq hc'
  have hb' : b ∈ Z₂ := sup_le (hcomm.trans (sup_le hQZ hPZ)) hQZ hb
  exact hb'.2 a ha

theorem xi_commutator_mem_pCoreOf_of_coprime (hX : IsXi T X) {p n : ℕ}
    (hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) (hnp : Nat.Coprime n p) {g : G} (hgn : g ^ n = 1)
    (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (h : ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X) :
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 X :=
  commutator_mem_of_frattini_coprime hnp hgn (pCoreOf_le 2 X) (le_normalizer_pCoreOf 2 X)
    (normalizer_le_normalizer_pCoreOf 2 X hgX) hpow
    (fun _ hd _ hb => xi_commutator_mem_of_mem_frattini hX hd hb) h

theorem xi_inf_sectionCentralizer_le (hT : quasithinIsSylowTwo T) (hX : IsXi T X) :
    T ⊓ sectionCentralizer X (pCoreOf 2 X) ≤ pCoreOf 2 (X ⊔ T) := by
  set T₀ := T ⊓ sectionCentralizer X (pCoreOf 2 X) with hT₀
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_le_of_quasithinIsSylowTwo hT hX.2.1
  have hQT₀ : pCoreOf 2 X ≤ T₀ := le_inf hQT (pCoreOf_le_sectionCentralizer X)
  have hXN : X ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have hsc := hs.2.2.2
    have h1 : s * x⁻¹ * s⁻¹ * x⁻¹⁻¹ ∈ pCoreOf 2 X := hsc x⁻¹ (X.inv_mem hx)
    have h2 : x * (s * x⁻¹ * s⁻¹ * x⁻¹⁻¹) * x⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X hx) _).mp h1
    have e : x * s * x⁻¹ = (x * (s * x⁻¹ * s⁻¹ * x⁻¹⁻¹) * x⁻¹) * s := by group
    rw [e]
    exact T₀.mul_mem (hQT₀ h2) hs
  have hTN : T ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro t ht
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    exact ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht), conj_mem_sectionCentralizer (hX.2.1 ht)
      (normalizer_le_normalizer_pCoreOf 2 X (hX.2.1 ht)) hs.2⟩
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) (sup_le hXN hTN)
    (hT.1.to_le inf_le_left)

theorem xi_mem_pCoreOf_sup (hT : quasithinIsSylowTwo T) (hX : IsXi T X) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) {t : G} (ht : t ∈ T)
    (h : ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X) : t ∈ pCoreOf 2 (X ⊔ T) := by
  obtain ⟨k, hk⟩ := hT.1 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hc := xi_commutator_mem_pCoreOf_of_coprime hX hpow hcop hk' (hX.2.1 ht) h
  exact xi_inf_sectionCentralizer_le hT hX
    ⟨ht, hX.2.1 ht, normalizer_le_normalizer_pCoreOf 2 X (hX.2.1 ht), hc⟩

end Finite

end CFSG.Quasithin.EmptyFaithfulMultiple.L3213
