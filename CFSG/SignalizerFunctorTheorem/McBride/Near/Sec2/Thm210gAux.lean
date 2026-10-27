module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.McBride.Thompson.SolvableFPF
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux2

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210g

variable {Γ : Type*} [Group Γ]

theorem sup_eq_of_mem_hyperplanes [Finite Γ] {p : ℕ} (hp : p.Prime) {A B E : Subgroup Γ}
    (hB : B ∈ Coprime.hyperplanes p A) (hEA : E ≤ A) (hEB : ¬ E ≤ B) : B ⊔ E = A := by
  obtain ⟨hBA, hcard⟩ := hB
  have hsup : B ⊔ E ≤ A := sup_le hBA hEA
  have hBpos : 0 < Nat.card B := Nat.card_pos
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ E)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hsup
  have h1 : Nat.card B * p = Nat.card B * (m * k) := by
    rw [mul_comm, ← hcard, hk, hm, mul_assoc]
  have h2 : p = m * k := Nat.eq_of_mul_eq_mul_left hBpos h1
  rcases (Nat.dvd_prime hp).1 (Dvd.intro k h2.symm) with hm1 | hmp
  · exfalso
    apply hEB
    have : B = B ⊔ E :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, hm1, mul_one])
    exact this ▸ le_sup_right
  · have hk1 : k = 1 := by
      have : p * k = p * 1 := by rw [mul_one]; nth_rw 2 [h2]; rw [hmp]
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    exact Subgroup.eq_of_le_of_card_ge hsup (by rw [hk, hk1, mul_one])

theorem exists_hyperplane_not_le [Finite Γ] {p : ℕ} (hp : p.Prime) {A Y T : Subgroup Γ}
    (hA : IsElemAbelian p A) (hpA : p ≤ Nat.card A) (hAY : A ≤ Subgroup.normalizer (Y : Set Γ))
    (hY : Nat.Coprime p (Nat.card Y)) (hYT : ¬ Y ≤ T) :
    ∃ B ∈ Coprime.hyperplanes p A, ¬ (Y ⊓ Subgroup.centralizer (B : Set Γ) ≤ T) := by
  by_contra hcon
  push Not at hcon
  apply hYT
  rw [← iSup_centralizer_hyperplanes hp hA hpA hAY hY]
  exact iSup₂_le hcon

theorem inf_centralizer_ne_bot_of_hyperplane [Finite Γ] {p : ℕ} (hp : p.Prime) {A B Z : Subgroup Γ}
    (hA : IsElemAbelian p A) (hB : B ∈ Coprime.hyperplanes p A)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set Γ)) (hZB : Z ≤ Subgroup.centralizer (B : Set Γ))
    (hnil : ¬ Group.IsNilpotent Z) : Z ⊓ Subgroup.centralizer (A : Set Γ) ≠ ⊥ := by
  intro hbot
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ B := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hBA, hcard⟩ := hB
    have hAB : A = B := le_antisymm hcon hBA
    have hpos : 0 < Nat.card B := Nat.card_pos
    rw [hAB] at hcard
    have : Nat.card B * p = Nat.card B * 1 := by rw [mul_one, mul_comm]; exact hcard.symm
    exact hp.ne_one (Nat.eq_of_mul_eq_mul_left hpos this)
  have ha1 : a ≠ 1 := fun h1 => haB (h1 ▸ one_mem B)
  have := Fact.mk hp
  have hord : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1
  have hAeq : B ⊔ Subgroup.zpowers a = A :=
    sup_eq_of_mem_hyperplanes hp hB (Subgroup.zpowers_le.2 haA)
      fun hle => haB (hle (Subgroup.mem_zpowers a))
  refine Thompson.fpf_nilpotent hp hord (hAZ haA) ?_ |> hnil
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzZ, hza⟩ := Subgroup.mem_inf.1 hz
  rw [Subgroup.mem_bot]
  have hzA : z ∈ Subgroup.centralizer (A : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hAeq] at hx
    have hle : B ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer {z} := by
      refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 (hZB hzZ) b hb
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hza).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have : z ∈ Z ⊓ Subgroup.centralizer (A : Set Γ) := Subgroup.mem_inf.2 ⟨hzZ, hzA⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

theorem mem_normalizer_proj {J L X : Subgroup Γ} (hJL : ∀ j ∈ J, ∀ l ∈ L, Commute j l) {q : Γ}
    (hqJ : q ∈ Subgroup.normalizer (J : Set Γ)) (hqL : q ∈ Subgroup.normalizer (L : Set Γ))
    (hqX : q ∈ Subgroup.normalizer (X : Set Γ)) :
    q ∈ Subgroup.normalizer (proj J L X : Set Γ) := by
  have key : ∀ q : Γ, q ∈ Subgroup.normalizer (J : Set Γ) → q ∈ Subgroup.normalizer (L : Set Γ) →
      q ∈ Subgroup.normalizer (X : Set Γ) → ∀ y ∈ proj J L X, q * y * q⁻¹ ∈ proj J L X := by
    intro q hqJ hqL hqX y hy
    obtain ⟨hyJ, l, hl, hyl⟩ := (mem_proj_iff hJL).1 hy
    refine (mem_proj_iff hJL).2 ⟨(Subgroup.mem_normalizer_iff.1 hqJ y).1 hyJ, q * l * q⁻¹,
      (Subgroup.mem_normalizer_iff.1 hqL l).1 hl, ?_⟩
    have : q * y * q⁻¹ * (q * l * q⁻¹) = q * (y * l) * q⁻¹ := by group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.1 hqX (y * l)).1 hyl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key q hqJ hqL hqX y, fun hy => ?_⟩
  have := key q⁻¹ (inv_mem hqJ) (inv_mem hqL) (inv_mem hqX) _ hy
  simpa [mul_assoc] using this

section DirectProduct

variable {S : Set (Subgroup Γ)} {L : Subgroup Γ}

theorem commute_sSup_sSup (hL : IsDirectProduct S L) {T₁ T₂ : Set (Subgroup Γ)} (h₁ : T₁ ⊆ S)
    (h₂ : T₂ ⊆ S) (hd : Disjoint T₁ T₂) : ∀ x ∈ sSup T₁, ∀ y ∈ sSup T₂, Commute x y := by
  have h : sSup T₁ ≤ Subgroup.centralizer ((sSup T₂ : Subgroup Γ) : Set Γ) := by
    refine sSup_le fun K hK => ?_
    rw [Subgroup.le_centralizer_iff]
    refine sSup_le fun K' hK' y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hne : K ≠ K' := fun heq => Set.disjoint_left.1 hd hK (heq ▸ hK')
    exact (hL.commute K (h₁ hK) K' (h₂ hK') hne x hx y hy).eq
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h hx) y hy).symm

theorem le_normalizer_sSup (hL : IsDirectProduct S L) {T : Set (Subgroup Γ)} (hT : T ⊆ S) :
    L ≤ Subgroup.normalizer ((sSup T : Subgroup Γ) : Set Γ) := by
  refine Thm210.le_normalizer_of_conj_mem fun c hc x hx => ?_
  have hle : sSup T ≤ (sSup T).comap (MulAut.conj c).toMonoidHom := by
    refine sSup_le fun K hK y hy => ?_
    have hcK : c ∈ Subgroup.normalizer (K : Set Γ) := hL.le_normalizer (hT hK) hc
    exact le_sSup hK ((Subgroup.mem_normalizer_iff.1 hcK y).1 hy)
  simpa using hle hx

variable [Finite Γ]

theorem projIn_iSup_le (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S) {ι : Sort*}
    (Y : ι → Subgroup Γ) (hY : ∀ i, Y i ≤ L) {K : Subgroup Γ}
    (h : ∀ i, projIn S J (Y i) ≤ K) : projIn S J (⨆ i, Y i) ≤ K := by
  set M : Subgroup Γ := ((K.subgroupOf J).comap (hL.coord hJ)).map L.subtype with hM
  have hYM : ∀ i, Y i ≤ M := by
    intro i y hy
    refine ⟨⟨y, hY i hy⟩, ?_, rfl⟩
    exact h i ((hL.mem_projIn_iff hJ).2 ⟨⟨y, hY i hy⟩, hy, rfl⟩)
  intro x hx
  obtain ⟨y, hyX, rfl⟩ := (hL.mem_projIn_iff hJ).1 hx
  obtain ⟨y', hy', hyy⟩ := iSup_le hYM hyX
  have : y' = y := Subtype.ext hyy
  rw [this] at hy'
  exact hy'

end DirectProduct

theorem eq_bot_or_eq_of_le_normalizer {J P : Subgroup Γ} (hs : IsSimpleGroup ↥J) (hPJ : P ≤ J)
    (hN : J ≤ Subgroup.normalizer (P : Set Γ)) : P = ⊥ ∨ P = J := by
  have hnorm : (P.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPJ).2 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf J) with h | h
  · left
    rw [← Subgroup.map_subgroupOf_eq_of_le hPJ, h, Subgroup.map_bot]
  · right
    refine le_antisymm hPJ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥J) ∈ P.subgroupOf J := by rw [h]; trivial
    exact this

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210g
