module

public import CFSG.RankThree.PartOne.N143.SecRankHard
public import CFSG.RankThree.PartOne.SRC.LiftP
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
public import CFSG.RankThree.PartOne.N143.SectionCover

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup CFSG CFSG.Assembly TauCeti
open CFSG.RankThree.PartOne.N143

@[expose] def RankFourCover (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (φ : Y →* S), Function.Surjective φ → IsPGroup p φ.ker →
    ∃ (T E : Subgroup Y) (k : ℕ), T ≠ ⊥ ∧ IsPGroup 2 T ∧ IsElementaryAbelian p E ∧ 4 ≤ k ∧
      Nat.card E = p ^ k ∧ E ≤ normalizer (T : Set Y)

theorem map_mem_normalizer_map {A B : Type*} [Group A] [Group B] (g : A →* B)
    {T : Subgroup A} {a : A} (ha : a ∈ normalizer (T : Set A)) :
    g a ∈ normalizer ((T.map g : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨a * t * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha t).mp ht, by simp⟩
  · rintro ⟨t', ht', h⟩
    have ha' : a⁻¹ ∈ normalizer (T : Set A) := (normalizer (T : Set A)).inv_mem ha
    refine ⟨a⁻¹ * t' * a⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp ha' t').mp ht', ?_⟩
    simp only [map_mul, map_inv, h]
    group

theorem noLowTwoRankSectionFor_of_rankFourCover_finite {P : CFSGIndex → Prop}
    (h : ∀ i, P i → Finite i.Group → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ RankFourCover p i.Group) :
    NoLowTwoRankSectionFor P := by
  intro L _ _ hKL he H M _ _ hM π hπ _ ⟨i, hi, ⟨e⟩⟩
  have hfin : Finite i.Group := Finite.of_equiv (M ⧸ center M) e.toEquiv
  obtain ⟨p, hp, hp2, hcov⟩ := h i hi hfin
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, -, hKmin⟩ := Finite.exists_le_minimal (p := fun K : Subgroup H => K.map π = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective π hπ])
  set πK : K →* M := π.comp K.subtype with hπK
  have hπKs : Function.Surjective πK := by
    intro x
    have hx : x ∈ K.map π := by
      rw [hKmin.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin : ∀ Y : Subgroup K, Y ≠ ⊤ → Y.map πK ≠ ⊤ := by
    intro Y hY hYmap
    apply hY
    have h1 : (Y.map K.subtype).map π = ⊤ := by
      rw [Subgroup.map_map]
      exact hYmap
    have h2 := hKmin.le_of_le h1 (Subgroup.map_subtype_le Y)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  obtain ⟨-, hCn, -, hCsyl, -, -, -, -, -⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover
      (CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hM) πK hπKs hmin
  set C : Subgroup K := (center M).comap πK with hC
  have : C.Normal := hCn
  set R : Subgroup K := CFSG.pPrimeCore p K ⊓ C with hR
  have hRn : R.Normal := inferInstance
  have hRC : R ≤ C := inf_le_right
  have hRcop : Nat.Coprime (Nat.card R) p :=
    ((CFSG.pPrimeCore_coprime_card (p := p) (G := K)).symm).coprime_dvd_left
      (Subgroup.card_dvd_of_le inf_le_left)
  have hRker : R ≤ ((QuotientGroup.mk' (center M)).comp πK).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hRC hx
  set φ0 : K ⧸ R →* M ⧸ center M :=
    QuotientGroup.lift R ((QuotientGroup.mk' (center M)).comp πK) hRker with hφ0
  have hφ0s : Function.Surjective φ0 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center M) q
    obtain ⟨k, rfl⟩ := hπKs x
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hφ0ker : φ0.ker = C.map (QuotientGroup.mk' R) := by
    rw [hφ0, QuotientGroup.ker_lift, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  set φ : K ⧸ R →* i.Group := e.toMonoidHom.comp φ0 with hφ
  have hφs : Function.Surjective φ := e.surjective.comp hφ0s
  have hφker : φ.ker = φ0.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφ, MonoidHom.comp_apply]
    exact map_eq_one_iff e.toMonoidHom e.injective
  have hindex : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ (R.subgroupOf C).index := by
    intro q hq hqp
    have : Fact q.Prime := ⟨hq⟩
    obtain Q : Sylow q C := default
    have hQn := hCsyl q Q
    set Q' : Subgroup K := (Q : Subgroup C).map C.subtype with hQ'
    have hQ'card : Nat.Coprime p (Nat.card Q') := by
      obtain ⟨k, hk⟩ := (Q.isPGroup'.map C.subtype).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
    have hQ'le : Q' ≤ CFSG.pPrimeCore p K := by
      unfold CFSG.pPrimeCore
      exact le_sSup ⟨hQn, hQ'card⟩
    have hQR : (Q : Subgroup C) ≤ R.subgroupOf C := by
      intro x hx
      rw [mem_subgroupOf]
      exact ⟨hQ'le ⟨x, hx, rfl⟩, x.2⟩
    exact fun hdvd => Q.not_dvd_index
      (hdvd.trans (Subgroup.index_dvd_of_le hQR))
  have hkerp : IsPGroup p φ.ker := by
    rw [hφker, hφ0ker]
    have hn0 : (R.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdvd => by
      by_contra hne
      exact hindex d hd hne hdvd)
    refine IsPGroup.of_card (n := (R.subgroupOf C).index.primeFactorsList.length) ?_
    rw [CFSG.natCard_map_mk'_eq, ← Subgroup.index_eq_card]
    exact hpow
  obtain ⟨TB, EB, k, hT, hT2, hE, hk, hEcard, hnorm⟩ := hcov (K ⧸ R) φ hφs hkerp
  obtain ⟨T₀, E₀, hT₀, hT₀2, hE₀, hE₀card, hE₀norm⟩ :=
    exists_lift_through_pPrime_kernel hp hp2 R hRcop hT hT2 hE hnorm
  rw [hEcard] at hE₀card
  set g : K →* L := H.subtype.comp K.subtype with hg
  have hginj : Function.Injective g := H.subtype_injective.comp K.subtype_injective
  have hU : T₀.map g ≠ ⊥ := fun hb =>
    hT₀ ((Subgroup.map_eq_bot_iff_of_injective _ hginj).mp hb)
  have hU2 : IsPGroup 2 (T₀.map g) := hT₀2.map g
  have hrk := CFSG.RankThree.PartOne.PlaneAux.le_evenRank_of_hom_normalizes hp hp2
    (A := E₀) (fun a b => (IsMulCommutative.is_comm (M := E₀)).comm a b)
    (fun a => by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E₀) a
      exact this)
    hE₀card (g.comp E₀.subtype) (hginj.comp E₀.subtype_injective) hU hU2
    (fun a => map_mem_normalizer_map g (hE₀norm a.2))
  omega

theorem noLowTwoRankSectionFor_of_rankFourCover {P : CFSGIndex → Prop}
    (h : ∀ i, P i → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ RankFourCover p i.Group) :
    NoLowTwoRankSectionFor P :=
  noLowTwoRankSectionFor_of_rankFourCover_finite fun i hi _ => h i hi

end CFSG.RankThree.PartOne.SRC
