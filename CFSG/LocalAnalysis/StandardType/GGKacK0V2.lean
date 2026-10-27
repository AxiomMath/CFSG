module

public import CFSG.LocalAnalysis.StandardType.GGKacK0
public import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKacCompBij (D : GGKacDatum) (L' : Type) [Group L'] (e : MulAut L') : Prop :=
  ∃ f : {J : Subgroup L' // IsComponentOf J (ggFixSub e)} ≃
      {i : Fin D.orbits.length // D.orbits[i].qs = true},
    ∀ J, GGHasLabel D.orbits[(f J).1].lab (↥J.1 ⧸ Subgroup.center ↥J.1)

@[expose] def GGKacSigmaClause {R : Type} [Group R] (p : ℕ) (I : Set (MulAut R)) (D : GGKacDatum)
    (L' : Type) [Group L'] (ψ : L' →* R) (e : MulAut L') : Prop :=
  ∀ o ∈ D.orbits, o.qs = false → ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
    (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      ∃ t : L', t ^ p = 1 ∧ (∀ a ∈ A, a t = t) ∧
        (∀ J : Subgroup L', IsComponentOf J (ggFixSub e) → ∀ j ∈ J, t * j = j * t) ∧
        (MulAut.conj t : MulAut L') ∉ Subgroup.zpowers e

@[expose] def GGK0MainB (Gen : LargeEvenLabel → ℕ → Prop)
    (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → Gen lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, Valid lab p D ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
              CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → p ∣ Nat.card J) ∧
            (2 ≤ D.rZ → ∃ E : Subgroup L', IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
              E ≤ ggFixSub e ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
              ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z) ∧
            GGKacCompBij D L' e

@[expose] def GGK0MainBS (Gen : LargeEvenLabel → ℕ → Prop)
    (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → Gen lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, Valid lab p D ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
              CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → p ∣ Nat.card J) ∧
            (2 ≤ D.rZ → ∃ E : Subgroup L', IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
              E ≤ ggFixSub e ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
              ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z) ∧
            GGKacCompBij D L' e ∧ GGKacSigmaClause p I D L' ψ e

theorem GGK0MainBS.toB {Gen : LargeEvenLabel → ℕ → Prop}
    {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop} (h : GGK0MainBS Gen Valid) :
    GGK0MainB Gen Valid := by
  intro p lab hlab hgen Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hgen Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he, -⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, hd, he⟩

theorem GGK0MainB.toMain {Gen : LargeEvenLabel → ℕ → Prop}
    {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop} (h : GGK0MainB Gen Valid) :
    GGK0Main Gen Valid := by
  intro p lab hlab hgen Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hgen Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, -⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, hd⟩

@[expose] def GGKacExcPair (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) ∧
    (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4)

theorem GGKacGeneric.toExcPair {lab : LargeEvenLabel} {p : ℕ} (h : GGKacGeneric lab p) :
    GGKacExcPair lab p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

@[expose] def GGK0ExcB : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, GGKacValid lab p D ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
              CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → p ∣ Nat.card J) ∧
            (GGKacGeneric lab p → 2 ≤ D.rZ → ∃ E : Subgroup L', IsElemAbelian p E ∧
              Nat.card E = p ^ D.rZ ∧ E ≤ ggFixSub e ∧
              (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
              ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z) ∧
            GGKacCompBij D L' e

theorem GGK0ExcB.toMainB (h : GGK0ExcB) : GGK0MainB GGKacGeneric GGKacValid := by
  intro p lab hlab hgen Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hgen.toExcPair Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, hd hgen, he⟩

theorem ggK0MainBS_of_B_exc (h : GGK0MainB GGKacGeneric GGKacValid) :
    GGK0MainBS GGKacGeneric GGKacValid := by
  intro p lab hlab hgen Q hQ
  have hn : 2 ≤ lab.n := by
    by_contra hlt
    have h1 : lab.n = 1 := by have := hlab.1; omega
    obtain ⟨hp, -, hd, htag, hF4, hE6, hE78⟩ := hgen
    rw [h1] at hd
    norm_num at hd
    have hp3 : p = 3 := by
      rcases hd with h1 | h3
      · exact absurd h1 hp.one_lt.ne'
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    rcases htag with h | h | h | h | h
    · exact hE6 ⟨Or.inl h, Or.inl rfl⟩
    · exact hE6 ⟨Or.inr h, Or.inl rfl⟩
    · exact hE78 ⟨Or.inl h, Or.inl rfl⟩
    · exact hE78 ⟨Or.inr h, Or.inl rfl⟩
    · exact hF4 ⟨h, rfl⟩
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hgen Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he⟩ := hP L' ψ hψ hker hcomm e hep hind
  refine ⟨D, hV, ha, hb, hc, hd, he, ?_⟩
  intro o ho hqs
  obtain ⟨T, tw, -, hT⟩ := hV
  have hq := ggKacTable_qs_of_two_le T tw p hn D hT o ho
  rw [hq] at hqs
  exact absurd hqs (by decide)

theorem ggKacValid_qs_false {lab : LargeEvenLabel} {p : ℕ} (hn : 1 ≤ lab.n) (hp : p.Prime)
    (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) {D : GGKacDatum} (hD : GGKacValid lab p D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) (hqs : o.qs = false) :
    o.lab = ⟨.A, 1, 1⟩ ∨ o.lab = ⟨.twA, 2, 1⟩ := by
  obtain ⟨T, tw, -, hT⟩ := hD
  by_cases hn2 : 2 ≤ lab.n
  · have hq := ggKacTable_qs_of_two_le T tw p hn2 D hT o ho
    rw [hq] at hqs
    exact absurd hqs (by decide)
  · have h1 : lab.n = 1 := by omega
    rw [h1] at hd hT
    norm_num at hd
    have hp3 : p = 3 := by
      rcases hd with h1 | h3
      · exact absurd h1 hp.one_lt.ne'
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    have key : ∀ (T : GGKacType) (tw : Bool), ∀ D ∈ ggKacTable T tw 3 1, ∀ o ∈ D.orbits,
        o.qs = false → (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 1) ∨
          (o.lab.tag = .twA ∧ o.lab.rank = 2 ∧ o.lab.n = 1) := by
      intro T tw
      cases T <;> cases tw <;> decide +kernel
    have hk := key T tw D hT o ho hqs
    rcases o with ⟨⟨t, r, n⟩, q⟩
    simp only at hk ⊢
    rcases hk with ⟨ht, hr, hn⟩ | ⟨ht, hr, hn⟩
    · left; subst ht hr hn; rfl
    · right; subst ht hr hn; rfl

end CFSG.StandardType

end
