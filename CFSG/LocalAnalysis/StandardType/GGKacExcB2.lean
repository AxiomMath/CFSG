module

public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGKacA12Sigma

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKacA12Comp (D : GGKacDatum) (L' : Type) [Group L'] (e : MulAut L') : Prop :=
  ∀ i : Fin D.orbits.length, D.orbits[i].lab = ⟨.A, 1, 1⟩ → D.orbits[i].qs = false →
    ∃ S : Subgroup L', S ≤ ggFixSub e ∧
      (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
        ∀ s ∈ S, ∀ j ∈ J, s * j = j * s) ∧
      (∀ φ : MulAut L', φ * e = e * φ → Subgroup.map (φ : L' →* L') S = S) ∧
      Nat.card ↥(commutator ↥S) = 3 ∧ ¬ commutator ↥S ≤ Subgroup.center ↥S

@[expose] def GGK0ExcB2 : Prop :=
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
            GGKacCompBij D L' e ∧ GGKacA12Comp D L' e

theorem GGK0ExcB2.toExcB (h : GGK0ExcB2) : GGK0ExcB := by
  intro p lab hlab hpair Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hpair Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he, -⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, hd, he⟩

theorem ggKacValid_qs_false_p3 {lab : LargeEvenLabel} {p : ℕ} (hn : 1 ≤ lab.n) (hp : p.Prime)
    (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) {D : GGKacDatum} (hD : GGKacValid lab p D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) (hqs : o.qs = false) : lab.n = 1 ∧ p = 3 := by
  obtain ⟨T, tw, -, hT⟩ := hD
  by_cases hn2 : 2 ≤ lab.n
  · have hq := ggKacTable_qs_of_two_le T tw p hn2 D hT o ho
    rw [hq] at hqs
    exact absurd hqs (by decide)
  · have h1 : lab.n = 1 := by omega
    refine ⟨h1, ?_⟩
    rw [h1] at hd
    norm_num at hd
    rcases hd with h1 | h3
    · exact absurd h1 hp.one_lt.ne'
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3

@[expose] def GGKacSigmaClauseOn {R : Type} [Group R] (P : GGKacOrbit → Prop) (p : ℕ)
    (I : Set (MulAut R)) (D : GGKacDatum) (L' : Type) [Group L'] (ψ : L' →* R)
    (e : MulAut L') : Prop :=
  ∀ o ∈ D.orbits, P o → ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
    (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      ∃ t : L', t ^ p = 1 ∧ (∀ a ∈ A, a t = t) ∧
        (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
          ∀ j ∈ J, t * j = j * t) ∧
        (MulAut.conj t : MulAut L') ∉ Subgroup.zpowers e

@[expose] def GGK0ExcBS : Prop :=
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
            GGKacCompBij D L' e ∧
            GGKacSigmaClauseOn (fun o => o.lab = ⟨.A, 1, 1⟩ ∧ o.qs = false) p I D L' ψ e

theorem ggK0ExcBS_of_B2 (h : GGK0ExcB2) : GGK0ExcBS := by
  intro p lab hlab hpair Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hpair Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he, hA12⟩ := hP L' ψ hψ hker hcomm e hep hind
  refine ⟨D, hV, ha, hb, hc, hd, he, ?_⟩
  rintro o ho ⟨hlabo, hqso⟩ A heA hAel -
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
  obtain ⟨S, hSfix, hcomp, hinv, hcard, hnc⟩ := hA12 ⟨i, hi⟩ hlabo hqso
  obtain ⟨hp, -, hdv, -⟩ := hpair
  obtain ⟨-, hp3⟩ := ggKacValid_qs_false_p3 hlab.1 hp hdv hV ho hqso
  exact ggKacA12_sigma hp3 e S hSfix hcomp hinv hcard hnc A heA hAel

end CFSG.StandardType

end
