module

public import CFSG.Quasithin.Background.FFC2Core
public import CFSG.Quasithin.Background.FFC2Sp4
public import CFSG.Quasithin.Background.FFC2Sym
public import CFSG.Quasithin.Background.FFC2G2
public import CFSG.Quasithin.Background.B5B42
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

theorem b4hyp_data {G L : Subgroup (MulAut V)} (h : B4Hyp G L) :
    L ≤ G ∧ (∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) ∧
      (∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L) ∧ CFSG.IsQuasisimple ↥L := by
  obtain ⟨-, hL, hq, -⟩ := h
  subst hL
  refine ⟨quasithinGenFitting_le G, fun g hg l hl => ?_, fun g hg hcomm => ?_, hq⟩
  · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_quasithinGenFitting G hg) l).1 hl
  · apply centralizer_quasithinGenFitting_le G
    exact ⟨hg, Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm l hl).symm⟩

omit [Finite V] in
theorem ffJ_data (G : Subgroup (MulAut V)) :
    ffJ G ≤ G ∧ ∀ g ∈ G, ∀ h ∈ ffJ G, g * h * g⁻¹ ∈ ffJ G :=
  ⟨B6.ffJ_le G, fun _ hg _ hh => (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ G hg) _).1 hh⟩

theorem charTwo_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])

theorem ffJ_ne_of_case5 {G L A : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L)
    (h5 : B42Case5 G A) : ffJ G ≠ L := by
  intro hJL
  obtain ⟨⟨n, hn, π, hπ, -⟩, -⟩ := h5
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have : Group.IsPerfect ↥L := hq.1
  have : Nontrivial ↥L := nontrivial_of_isQuasisimple hq
  let e : ↥(ffJ G) ≃* ↥L := MulEquiv.subgroupCongr hJL
  exact not_surjective_perm_of_perfect hn5 ⟨e.toMonoidHom.comp π, e.surjective.comp hπ.1⟩

theorem ident_perm {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hJL : ffJ G ≠ L) {n : ℕ}
    (hn : n = 5 ∨ n = 7) (e : ↥(ffJ G) ≃* Equiv.Perm (Fin n)) :
    L = ⁅ffJ G, ffJ G⁆ ∧ G = ffJ G := by
  obtain ⟨hLG, hLn, hself, hq⟩ := b4hyp_data hHyp
  obtain ⟨hHG, hHn⟩ := ffJ_data G
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨hs, hnab⟩ := commutator_simple_of_perm hn5 e
  exact ident_aux hHG hLG hHn hLn hself hq hJL hnab hs
    (card_mulAut_commutator_perm_le (by omega) e)

theorem ident_g2
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hJL : ffJ G ≠ L) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2) (e : ↥(ffJ G) ≃* ↥(quasithinG2 K)) :
    L = ⁅ffJ G, ffJ G⁆ ∧ G = ffJ G := by
  obtain ⟨hLG, hLn, hself, hq⟩ := b4hyp_data hHyp
  obtain ⟨hHG, hHn⟩ := ffJ_data G
  obtain ⟨hs, hnab, haut⟩ := commutator_data_g2 hK e
  exact ident_aux hHG hLG hHn hLn hself hq hJL hnab hs haut

theorem ident_sp4 {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L)
    (h : BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1) :
    Nonempty (↥(ffJ G) ≃* Equiv.Perm (Fin 6)) ∧ L = ⁅ffJ G, ffJ G⁆ ∧ G = ffJ G := by
  obtain ⟨hLG, hLn, hself, hq⟩ := b4hyp_data hHyp
  obtain ⟨hHG, hHn⟩ := ffJ_data G
  obtain ⟨K, hKf, hKfin, hKc, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv h
  have hK : Nat.card K = 2 := by simpa using hKc
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let c : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hF
  let e6 : ↥(ffJ G) ≃* Equiv.Perm (Fin 6) := (e.symm.trans (B5FinSp.theta c).symm)
  obtain ⟨hs, hnab⟩ := commutator_simple_of_perm (by norm_num : 5 ≤ 6) e6
  refine ⟨⟨e6⟩, eq_commutator_of_normal_simple hHG hLG hHn hLn hself hq hnab hs, ?_⟩
  exact le_antisymm (le_of_binaryNaturalSp4_one hHn h) hHG

theorem asB42Ident_of_b42
    (h42 : AsB42) : AsB42Ident := by
  intro V _ _ hV G L hHyp A hA hcase
  obtain ⟨hLG, hLn, hself, hq⟩ := b4hyp_data hHyp
  have hJL : ffJ G ≠ L := by
    rcases hcase with h5 | hne
    · exact ffJ_ne_of_case5 hq h5
    · exact hne
  refine ⟨hJL, ?_⟩
  have finish : (L = ⁅ffJ G, ffJ G⁆ ∧ G = ffJ G) →
      ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (↥(ffJ G) ≃* Equiv.Perm (Fin n))) ∨
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
          Nonempty (↥(ffJ G) ≃* ↥(quasithinG2 K))) →
      G = ffJ G ∧ L = ⁅G, G⁆ ∧
        ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (↥G ≃* Equiv.Perm (Fin n))) ∨
          ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
            Nonempty (↥G ≃* ↥(quasithinG2 K))) := by
    rintro ⟨hL, hGH⟩ hs
    refine ⟨hGH, ?_, ?_⟩
    · calc L = ⁅ffJ G, ffJ G⁆ := hL
        _ = ⁅G, G⁆ := by rw [← hGH]
    · let eGH : ↥G ≃* ↥(ffJ G) := MulEquiv.subgroupCongr hGH
      rcases hs with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨K, hK, hf, hc, ⟨e⟩⟩
      · exact Or.inl ⟨n, h5, h8, ⟨eGH.trans e⟩⟩
      · exact Or.inr ⟨K, hK, hf, hc, ⟨eGH.trans e⟩⟩
  rcases h42 V hV G L hHyp A hA with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact absurd c1.1 hJL
  · exact absurd c2.1 hJL
  · obtain ⟨⟨n, hn, h1⟩, -⟩ := c3
    have hn1 : n = 1 := by
      have hge : 1 ≤ n := B5.one_le_of_binaryNaturalSp4 hn
      by_contra hne
      exact hJL (h1 (by omega))
    subst hn1
    obtain ⟨⟨e6⟩, hL, hGH⟩ := ident_sp4 hHyp hn
    exact finish ⟨hL, hGH⟩ (Or.inl ⟨6, by norm_num, by norm_num, ⟨e6⟩⟩)
  · obtain ⟨⟨n, hn, -, h1⟩, -⟩ := c4
    have hn1 : n = 1 := by
      have hge : 1 ≤ n := B5.one_le_of_g2Natural hn
      by_contra hne
      exact hJL (h1 (by omega))
    subst hn1
    obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := hn
    have hK : Nat.card K = 2 := by simpa using hKc
    have := charTwo_of_card_two hK
    have hinj := injective_of_zornQ_realizes hπ
    let e : ↥(quasithinG2 K) ≃* ↥(ffJ G) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    obtain ⟨hL, hGH⟩ := ident_g2 hHyp hJL hK e.symm
    exact finish ⟨hL, hGH⟩ (Or.inr ⟨K, hKf, hKfin, hK, ⟨e.symm⟩⟩)
  · obtain ⟨⟨n, hn, π, hπ, -⟩, -⟩ := c5
    have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    have hinj := injective_of_symDn_realizes hn5 hπ
    let e : Equiv.Perm (Fin n) ≃* ↥(ffJ G) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    obtain ⟨hL, hGH⟩ := ident_perm hHyp hJL hn e.symm
    exact finish ⟨hL, hGH⟩
      (Or.inl ⟨n, hn5, by rcases hn with rfl | rfl <;> norm_num, ⟨e.symm⟩⟩)
  · exact absurd c6.1 hJL
  · exact absurd c7.2.1 hJL
  · exact absurd c8.1 hJL
  · exact absurd c9.1 hJL
  · obtain ⟨-, h10 | h10⟩ := c10
    · exact absurd h10.2.1 hJL
    · obtain ⟨hGH, ⟨e⟩, -⟩ := h10
      let e' : ↥(ffJ G) ≃* Equiv.Perm (Fin 8) := (MulEquiv.subgroupCongr hGH).symm.trans e
      obtain ⟨hs, hnab⟩ := commutator_simple_of_perm (by norm_num : 5 ≤ 8) e'
      obtain ⟨hHG, hHn⟩ := ffJ_data G
      have hL := eq_commutator_of_normal_simple hHG hLG hHn hLn hself hq hnab hs
      exact finish ⟨hL, hGH⟩ (Or.inl ⟨8, by norm_num, le_rfl, ⟨e'⟩⟩)
  · exact absurd c11.2.1 hJL

end FFC

end CFSG.Quasithin
