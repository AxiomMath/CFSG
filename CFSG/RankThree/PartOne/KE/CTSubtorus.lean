module

public import CFSG.RankThree.PartOne.KE.CTLang

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

@[expose] def subtorusImage {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]
    (ι : C →* ModGL τ L) (g0 : ModGL τ L) (Z : Subgroup (ModGL τ L)) : Subgroup C :=
  (Z.map (MulAut.conj g0).toMonoidHom).comap ι

theorem mem_subtorusImage_iff {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]
    (ι : C →* ModGL τ L) (g0 : ModGL τ L) (Z : Subgroup (ModGL τ L)) (y : C) :
    y ∈ subtorusImage ι g0 Z ↔ g0⁻¹ * ι y * g0 ∈ Z := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have h : g0 * x * g0⁻¹ = ι y := hxy
    have : g0⁻¹ * ι y * g0 = x := by rw [← h]; group
    rw [this]
    exact hx
  · intro h
    refine ⟨_, h, ?_⟩
    change g0 * (g0⁻¹ * ι y * g0) * g0⁻¹ = ι y
    group

theorem sylow_conjugacy_of_subtorus {τ : Tag} (d : ℕ) {C : Type} [Group C] [Finite C]
    {L : Type} [Field L] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (Φ : ModGL τ L →* ModGL τ L) (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Φ g0 = g0 * n) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {N : ℕ} (hN : N ≠ 0)
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ι.range.relIndex X ∣ d ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range)
    (Z : Subgroup (ModGL τ L)) (hZ : Z ≤ twistedTorusOf n Φ) (hcyc : IsCyclic Z)
    (hcard : Nat.card Z = N)
    (hord : p ^ (Nat.card C).factorization p = p ^ N.factorization p) :
    IsCyclic (subtorusImage ι g0 Z) ∧ Nat.card (subtorusImage ι g0 Z) ∣ N ∧
      N / Nat.card (subtorusImage ι g0 Z) ∣ d ∧
      (∃ S : Sylow p C, (S : Subgroup C) ≤ subtorusImage ι g0 Z) ∧
      (∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q) ∧
      (∀ x : C, orderOf x = p → ∃ g : C, g * x * g⁻¹ ∈ subtorusImage ι g0 Z) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hZfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  let cg : ModGL τ L →* ModGL τ L := (MulAut.conj g0).toMonoidHom
  have hcg : Function.Injective cg := (MulAut.conj g0).injective
  have hcg_apply : ∀ x, cg x = g0 * x * g0⁻¹ := fun x => rfl
  have hZC : Z ≤ adjointGroup τ L := hZ.trans (twistedTorusOf_le_adjointGroup n Φ)
  set X : Subgroup (ModGL τ L) := Z.map cg with hX
  have hXfin : Finite X :=
    Finite.of_surjective (cg.subgroupMap Z) (cg.subgroupMap_surjective Z)
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (hZC hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 (hZ hx)).2
    rw [hcg_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ x * (g0 * n)⁻¹ = g0 * (n * Φ x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have := hXfin
  obtain ⟨hidx, hpg⟩ := hrat X hXC hXF
  have hXcard : Nat.card X = N := by
    rw [hX, Subgroup.card_map_of_injective hcg, hcard]
  set T : Subgroup C := subtorusImage ι g0 Z with hT
  have hTX : T = X.comap ι := rfl
  have hTmap : T.map ι = ι.range ⊓ X := by rw [hTX]; exact Subgroup.map_comap_eq ι X
  have hTcard : Nat.card T = Nat.card (ι.range ⊓ X : Subgroup (ModGL τ L)) := by
    rw [← hTmap, Subgroup.card_map_of_injective hι]
  have hmul : ι.range.relIndex X * Nat.card T = N := by
    rw [hTcard, Subgroup.relIndex_mul_card, hXcard]
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hTdvd : Nat.card T ∣ N := Dvd.intro_left _ hmul
  have hTdiv : N / Nat.card T ∣ d := by
    rw [← hmul, Nat.mul_div_cancel _ hTpos]
    exact hidx
  have hψ : ∀ y : T, g0⁻¹ * ι (y : C) * g0 ∈ Z := fun y => (mem_subtorusImage_iff ι g0 Z y).1 y.2
  have hcycT : IsCyclic T := by
    have := hcyc
    let ψ : T →* Z := ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp T.subtype)).codRestrict _
      (fun y => by simpa using hψ y)
    refine isCyclic_of_injective ψ fun a b hab => ?_
    have h1 : g0⁻¹ * ι (a : C) * g0⁻¹⁻¹ = g0⁻¹ * ι (b : C) * g0⁻¹⁻¹ := congrArg Subtype.val hab
    have h2 := (MulAut.conj g0⁻¹).injective h1
    exact Subtype.ext (hι h2)
  have hSylow : ∃ S : Sylow p C, (S : Subgroup C) ≤ T := by
    obtain ⟨P0⟩ : Nonempty (Sylow p Z) := inferInstance
    set P1 : Subgroup (ModGL τ L) := ((P0 : Subgroup Z).map Z.subtype).map cg with hP1
    have hP1X : P1 ≤ X := Subgroup.map_mono (Subgroup.map_subtype_le _)
    have hP1p : IsPGroup p P1 := (P0.isPGroup'.map _).map cg
    have hP1range : P1 ≤ ι.range := hpg p hp hp3 P1 hP1X hP1p
    set P : Subgroup C := P1.comap ι with hP
    have hPmap : P.map ι = P1 := by
      rw [hP, Subgroup.map_comap_eq, inf_eq_right.2 hP1range]
    have hPcard : Nat.card P = p ^ (Nat.card C).factorization p := by
      have h1 : Nat.card P = Nat.card P1 := by
        rw [← hPmap, Subgroup.card_map_of_injective hι]
      have h2 : Nat.card P1 = Nat.card (P0 : Subgroup Z) := by
        rw [hP1, Subgroup.card_map_of_injective hcg,
          Subgroup.card_map_of_injective Z.subtype_injective]
      rw [h1, h2, Sylow.card_eq_multiplicity P0, hcard, hord]
    refine ⟨Sylow.ofCard P hPcard, ?_⟩
    rw [Sylow.coe_ofCard]
    exact Subgroup.comap_mono hP1X
  obtain ⟨S, hST⟩ := hSylow
  have hconj : ∀ Q : Subgroup C, IsPGroup p Q → ∃ g : C, ∀ q ∈ Q, g * q * g⁻¹ ∈ T := by
    intro Q hQ
    obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S' S
    refine ⟨g, fun q hq => hST ?_⟩
    have h1 := Subgroup.smul_mem_pointwise_smul q (MulAut.conj g) (S' : Subgroup _) (hS' hq)
    have h2 : (MulAut.conj g • (S' : Subgroup C)) = ((g • S' : Sylow p C) : Subgroup C) := rfl
    rw [h2, hg] at h1
    exact h1
  have hpcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q := by
    intro Q hQ
    obtain ⟨g, hg⟩ := hconj Q hQ
    have := hcycT
    let φ : Q →* T := ((MulAut.conj g).toMonoidHom.comp Q.subtype).codRestrict T
      fun q => hg q q.2
    refine isCyclic_of_injective φ fun a b hab => ?_
    have h1 : g * (a : C) * g⁻¹ = g * (b : C) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext ((MulAut.conj g).injective h1)
  have hord_conj : ∀ x : C, orderOf x = p → ∃ g : C, g * x * g⁻¹ ∈ T := by
    intro x hx
    have hQ : IsPGroup p (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx, pow_one]
    obtain ⟨g, hg⟩ := hconj _ hQ
    exact ⟨g, hg x (Subgroup.mem_zpowers x)⟩
  exact ⟨hcycT, hTdvd, hTdiv, ⟨S, hST⟩, hpcyc, hord_conj⟩

end CFSG.RankThree.PartOne.KE
