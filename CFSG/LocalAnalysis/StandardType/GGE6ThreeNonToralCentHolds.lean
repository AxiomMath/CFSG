module

public import CFSG.LocalAnalysis.StandardType.GGL45E67Toral
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralEmbed
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralClauses
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.StandardType.ExcFramesHalf
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.TableBExc.E6Three

private def centPowSet {M : Type*} [Group M] (G₀ E : Subgroup M) : Set M :=
  {d : M | (∀ m : ℕ, ∃ c' ∈ G₀,
    (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ d ^ 3 = 1}

private theorem commute_map_conj_iff {M : Type*} [Group M] {E : Subgroup M} {g x : M} :
    (∀ e ∈ E, x * e = e * x) ↔
      ∀ e' ∈ E.map (MulAut.conj g).toMonoidHom,
        MulAut.conj g x * e' = e' * MulAut.conj g x := by
  constructor
  · intro hx e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 he'
    change (MulAut.conj g) x * (MulAut.conj g) e =
      (MulAut.conj g) e * (MulAut.conj g) x
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g) (hx e he)
  · intro hx e he
    have h := hx (MulAut.conj g e) (Subgroup.mem_map.2 ⟨e, he, rfl⟩)
    exact (MulAut.conj g).injective (by simpa only [map_mul] using h)

private theorem conj_comm_clause {M : Type*} [Group M] (G₀ E : Subgroup M) {g : M}
    (hg : g ∈ G₀)
    (hcomm : ∀ x ∈ G₀, ∀ y ∈ G₀,
      (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, x * e' = e' * x) →
      (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, y * e' = e' * y) →
      x * y = y * x) :
    ∀ x ∈ G₀, ∀ y ∈ G₀,
      (∀ e ∈ E, x * e = e * x) → (∀ e ∈ E, y * e = e * y) → x * y = y * x := by
  intro x hx y hy hxE hyE
  have hxE' : ∀ e' ∈ E.map (MulAut.conj g).toMonoidHom,
      MulAut.conj g x * e' = e' * MulAut.conj g x :=
    (commute_map_conj_iff (E := E) (g := g) (x := x)).1 hxE
  have hyE' : ∀ e' ∈ E.map (MulAut.conj g).toMonoidHom,
      MulAut.conj g y * e' = e' * MulAut.conj g y :=
    (commute_map_conj_iff (E := E) (g := g) (x := y)).1 hyE
  have hxG : MulAut.conj g x ∈ G₀ := by
    simpa only [MulAut.conj_apply] using mul_mem (mul_mem hg hx) (inv_mem hg)
  have hyG : MulAut.conj g y ∈ G₀ := by
    simpa only [MulAut.conj_apply] using mul_mem (mul_mem hg hy) (inv_mem hg)
  have h := hcomm (MulAut.conj g x) hxG (MulAut.conj g y) hyG hxE' hyE'
  exact (MulAut.conj g).injective (by simpa only [map_mul] using h)

private theorem conj_pow_clause {M : Type*} [Group M] (G₀ E : Subgroup M) {g : M}
    (hg : g ∈ G₀) {d' : M}
    (hd'pow : ∀ m : ℕ, ∃ c' ∈ G₀,
      (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, c' * e' = e' * c') ∧
        d' = c' ^ 3 ^ m) :
    ∀ m : ℕ, ∃ c' ∈ G₀,
      (∀ e ∈ E, c' * e = e * c') ∧ g⁻¹ * d' * g = c' ^ 3 ^ m := by
  intro m
  obtain ⟨c', hc'G, hc'E', hd'm⟩ := hd'pow m
  have hc''G : g⁻¹ * c' * g ∈ G₀ := by
    simpa only [MulAut.conj_apply] using mul_mem (mul_mem (inv_mem hg) hc'G) hg
  refine ⟨g⁻¹ * c' * g, hc''G, ?_, ?_⟩
  · intro e₀ he₀
    have h := hc'E' (MulAut.conj g e₀) (Subgroup.mem_map.2 ⟨e₀, he₀, rfl⟩)
    calc g⁻¹ * c' * g * e₀
        = g⁻¹ * (c' * (g * e₀ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * e₀ * g⁻¹) * c') * g := by
          rw [show c' * (g * e₀ * g⁻¹) = (g * e₀ * g⁻¹) * c' from h]
      _ = e₀ * (g⁻¹ * c' * g) := by group
  · calc g⁻¹ * d' * g = MulAut.conj g⁻¹ d' := by
          rw [MulAut.conj_apply]
          group
      _ = MulAut.conj g⁻¹ (c' ^ 3 ^ m) := by rw [hd'm]
      _ = (MulAut.conj g⁻¹ c') ^ 3 ^ m := map_pow _ _ _
      _ = (g⁻¹ * c' * g) ^ 3 ^ m := by
          rw [MulAut.conj_apply]
          group

private theorem conj_dec_clause {M : Type*} [Group M] (G₀ E : Subgroup M) {g : M}
    (hg : g ∈ G₀)
    (hdec : ∀ c ∈ G₀,
      (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, c * e' = e' * c) →
      ∃ e' ∈ E.map (MulAut.conj g).toMonoidHom, ∃ d : M,
        (∀ m : ℕ, ∃ c' ∈ G₀,
          (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, c' * e' = e' * c') ∧
            d = c' ^ 3 ^ m) ∧
        c = e' * d) :
    ∀ c ∈ G₀, (∀ e ∈ E, c * e = e * c) →
      ∃ e ∈ E, ∃ d : M,
        (∀ m : ℕ, ∃ c' ∈ G₀, (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧
        c = e * d := by
  intro c hc hcE
  have hcE' : ∀ e' ∈ E.map (MulAut.conj g).toMonoidHom,
      MulAut.conj g c * e' = e' * MulAut.conj g c :=
    (commute_map_conj_iff (E := E) (g := g) (x := c)).1 hcE
  have hcG : MulAut.conj g c ∈ G₀ := by
    simpa only [MulAut.conj_apply] using mul_mem (mul_mem hg hc) (inv_mem hg)
  obtain ⟨e', he', d', hd'pow, hcd'⟩ := hdec (MulAut.conj g c) hcG hcE'
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 he'
  refine ⟨e, he, g⁻¹ * d' * g, conj_pow_clause G₀ E hg hd'pow, ?_⟩
  apply (MulAut.conj g).injective
  rw [hcd', map_mul]
  congr 1
  rw [MulAut.conj_apply]
  group

private theorem conj_card_clause {M : Type*} [Group M] (G₀ E : Subgroup M) {g : M}
    (hg : g ∈ G₀)
    (h9 : (centPowSet G₀ (E.map (MulAut.conj g).toMonoidHom)).encard ≤ 9) :
    (centPowSet G₀ E).encard ≤ 9 := by
  have hsub : MulAut.conj g '' centPowSet G₀ E ⊆
      centPowSet G₀ (E.map (MulAut.conj g).toMonoidHom) := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hdpow, hd3⟩ := hd
    refine ⟨?_, ?_⟩
    · intro m
      obtain ⟨c', hc'G, hc'E, hdm⟩ := hdpow m
      have hc'G' : MulAut.conj g c' ∈ G₀ := by
        simpa only [MulAut.conj_apply] using mul_mem (mul_mem hg hc'G) (inv_mem hg)
      exact ⟨MulAut.conj g c', hc'G', (commute_map_conj_iff (E := E) (g := g)
        (x := c')).1 hc'E, by rw [hdm, map_pow]⟩
    · rw [← map_pow, hd3, map_one]
  calc (centPowSet G₀ E).encard
      = (MulAut.conj g '' centPowSet G₀ E).encard := by
          rw [Function.Injective.encard_image (MulAut.conj g).injective]
      _ ≤ (centPowSet G₀ (E.map (MulAut.conj g).toMonoidHom)).encard :=
          Set.encard_le_encard hsub
      _ ≤ 9 := h9

private theorem clauses_of_conj {M : Type*} [Group M] (G₀ E : Subgroup M) {g : M}
    (hg : g ∈ G₀)
    (hcomm : ∀ x ∈ G₀, ∀ y ∈ G₀,
      (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, x * e' = e' * x) →
      (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, y * e' = e' * y) →
      x * y = y * x)
    (hdec : ∀ c ∈ G₀,
      (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, c * e' = e' * c) →
      ∃ e' ∈ E.map (MulAut.conj g).toMonoidHom, ∃ d : M,
        (∀ m : ℕ, ∃ c' ∈ G₀,
          (∀ e' ∈ E.map (MulAut.conj g).toMonoidHom, c' * e' = e' * c') ∧
            d = c' ^ 3 ^ m) ∧
        c = e' * d)
    (h9 : (centPowSet G₀ (E.map (MulAut.conj g).toMonoidHom)).encard ≤ 9) :
    (∀ x ∈ G₀, ∀ y ∈ G₀,
      (∀ e ∈ E, x * e = e * x) → (∀ e ∈ E, y * e = e * y) → x * y = y * x) ∧
    (∀ c ∈ G₀, (∀ e ∈ E, c * e = e * c) →
      ∃ e ∈ E, ∃ d : M,
        (∀ m : ℕ, ∃ c' ∈ G₀, (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧
        c = e * d) ∧
    (centPowSet G₀ E).encard ≤ 9 :=
  ⟨conj_comm_clause G₀ E hg hcomm, conj_dec_clause G₀ E hg hdec,
    conj_card_clause G₀ E hg h9⟩

private theorem not_toral_map_conj
    {L : Type} [Field L] (E : Subgroup (ModGL .E6 L)) {g : ModGL .E6 L}
    (hg : g ∈ adjointGroup .E6 L)
    (hnt : ¬ IsToralSubgroup .E6 L E) :
    ¬ E.map (MulAut.conj g).toMonoidHom ≤ torusGroup .E6 L := by
  intro hle
  apply hnt
  refine ⟨g⁻¹, (adjointGroup .E6 L).inv_mem hg, ?_⟩
  intro x hx
  simpa [MulAut.conj_apply] using hle (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)

private theorem algebraicClosure_facts {K : Type} [Field K] [Finite K] [CharP K 2] :
    CharP (AlgebraicClosure K) 2 ∧
      ringChar (AlgebraicClosure K) ≠ 3 ∧
      (letI := ZMod.algebra (AlgebraicClosure K) 2
       Algebra.IsAlgebraic (ZMod 2) (AlgebraicClosure K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  refine ⟨hchar, ?_, ?_⟩
  · rw [ringChar.eq (AlgebraicClosure K) 2]
    norm_num
  · exact isAlgebraic_zmod_algebraicClosure_of_finite K 2

theorem ggL45E6NonToralThreeCent_holds :
    GGL45E6NonToralThreeCent := by
  intro K₀ hfield hfin hchar Ebar hEadj hEea hnt hcard
  letI := hfield
  letI := hfin
  letI := hchar
  let L := AlgebraicClosure K₀
  obtain ⟨hcharL, hL, halg⟩ := algebraicClosure_facts (K := K₀)
  haveI := hcharL
  have hEfin : (Ebar : Set (ModGL .E6 L)).Finite := by
    haveI : Finite Ebar := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    exact Set.toFinite _
  obtain ⟨g, hgG, hEM, hreg⟩ :=
    E6NonToralThree.exists_conj_regular (L := L) (ℓ := 2) (by norm_num)
      halg hEadj hEfin hEea
  let E' : Subgroup (ModGL .E6 L) := Ebar.map (MulAut.conj g).toMonoidHom
  have hE'ea : IsElemAbelian 3 E' := hEea.map (MulAut.conj g).toMonoidHom
  have hE'card : Nat.card E' = 3 ^ 4 := by
    change Nat.card (Ebar.map (MulAut.conj g).toMonoidHom) = 3 ^ 4
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hET := not_toral_map_conj Ebar hgG hnt
  have hclauses := E6NonToralThree.centralizer_clauses (E := E') hL hEM hE'ea hE'card hET
    (fun e he => (hreg e he).1) (fun e he i => (hreg e he).2 i)
  exact clauses_of_conj (adjointGroup .E6 L) Ebar (g := g) hgG
    hclauses.1 hclauses.2.1 hclauses.2.2

end CFSG.StandardType
