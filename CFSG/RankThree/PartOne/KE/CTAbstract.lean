module

public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.PartOne.KE.CTStatement

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

theorem cyclic_sylow_of_twisted_torus {τ : Tag} (d : ℕ) {C : Type} [Group C] [Finite C]
    {L : Type} [Field L] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (Φ : ModGL τ L →* ModGL τ L)
    (hιΦ : ∀ y, Φ (ι y) = ι y) (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Φ g0 = g0 * n) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {N : ℕ} (hN : N ≠ 0)
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ι.range.relIndex X ∣ d ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range)
    (hcentL : ∀ x ∈ torusGroup τ L, orderOf x = p →
      (∀ a : Fin τ.rank → Lˣ, x = rootDiagUnit τ a →
        ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1) →
      ∀ y ∈ adjointGroup τ L, y * x = x * y → y ∈ torusGroup τ L)
    (hcyc : IsCyclic (twistedTorusOf n Φ)) (hcard : Nat.card (twistedTorusOf n Φ) = N)
    (hreg : ∀ x ∈ twistedTorusOf n Φ, orderOf x = p → ∀ a : Fin τ.rank → Lˣ,
      x = rootDiagUnit τ a → ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1)
    (hord : p ^ (Nat.card C).factorization p = p ^ N.factorization p) :
    CyclicSylowConclusion' C p N d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hT0fin : Finite (twistedTorusOf n Φ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  let cg : ModGL τ L →* ModGL τ L := (MulAut.conj g0).toMonoidHom
  have hcg : Function.Injective cg := (MulAut.conj g0).injective
  have hcg_apply : ∀ x, cg x = g0 * x * g0⁻¹ := fun x => rfl
  have hT0C := twistedTorusOf_le_adjointGroup n Φ
  set X : Subgroup (ModGL τ L) := (twistedTorusOf n Φ).map cg with hX
  have hXfin : Finite X :=
    Finite.of_surjective (cg.subgroupMap (twistedTorusOf n Φ))
      (cg.subgroupMap_surjective (twistedTorusOf n Φ))
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (hT0C hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 hx).2
    rw [hcg_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ x * (g0 * n)⁻¹ = g0 * (n * Φ x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have := hXfin
  obtain ⟨hidx, hpg⟩ := hrat X hXC hXF
  have hXcard : Nat.card X = N := by
    rw [hX, Subgroup.card_map_of_injective hcg, hcard]
  set T : Subgroup C := X.comap ι with hT
  have hTmap : T.map ι = ι.range ⊓ X := Subgroup.map_comap_eq ι X
  have hTcard : Nat.card T = Nat.card (ι.range ⊓ X : Subgroup (ModGL τ L)) := by
    rw [← hTmap, Subgroup.card_map_of_injective hι]
  have hmul : ι.range.relIndex X * Nat.card T = N := by
    rw [hTcard, Subgroup.relIndex_mul_card, hXcard]
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hTdvd : Nat.card T ∣ N := Dvd.intro_left _ hmul
  have hTdiv : N / Nat.card T ∣ d := by
    rw [← hmul, Nat.mul_div_cancel _ hTpos]
    exact hidx
  have hψ : ∀ y : T, g0⁻¹ * ι (y : C) * g0⁻¹⁻¹ ∈ twistedTorusOf n Φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (show ι (y : C) ∈ X from y.2)
    rw [← hxy, hcg_apply]
    have : g0⁻¹ * (g0 * x * g0⁻¹) * g0⁻¹⁻¹ = x := by group
    rw [this]
    exact hx
  have hcycT : IsCyclic T := by
    have := hcyc
    let ψ : T →* twistedTorusOf n Φ :=
      ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp T.subtype)).codRestrict _ hψ
    refine isCyclic_of_injective ψ fun a b hab => ?_
    have h1 : g0⁻¹ * ι (a : C) * g0⁻¹⁻¹ =
        g0⁻¹ * ι (b : C) * g0⁻¹⁻¹ := congrArg Subtype.val hab
    have h2 := (MulAut.conj g0⁻¹).injective h1
    exact Subtype.ext (hι h2)
  have hSylow : ∃ S : Sylow p C, (S : Subgroup C) ≤ T := by
    obtain ⟨P0⟩ : Nonempty (Sylow p (twistedTorusOf n Φ)) := inferInstance
    set P1 : Subgroup (ModGL τ L) :=
      ((P0 : Subgroup (twistedTorusOf n Φ)).map (twistedTorusOf n Φ).subtype).map cg with hP1
    have hP1X : P1 ≤ X :=
      Subgroup.map_mono (Subgroup.map_subtype_le _)
    have hP1p : IsPGroup p P1 := (P0.isPGroup'.map _).map cg
    have hP1range : P1 ≤ ι.range :=
      hpg p hp hp3 P1 hP1X hP1p
    set P : Subgroup C := P1.comap ι with hP
    have hPmap : P.map ι = P1 := by
      rw [hP, Subgroup.map_comap_eq, inf_eq_right.2 hP1range]
    have hPcard : Nat.card P = p ^ (Nat.card C).factorization p := by
      have h1 : Nat.card P = Nat.card P1 := by
        rw [← hPmap, Subgroup.card_map_of_injective hι]
      have h2 : Nat.card P1 = Nat.card (P0 : Subgroup (twistedTorusOf n Φ)) := by
        rw [hP1, Subgroup.card_map_of_injective hcg,
          Subgroup.card_map_of_injective (twistedTorusOf n Φ).subtype_injective]
      rw [h1, h2, Sylow.card_eq_multiplicity P0, hcard, hord]
    refine ⟨Sylow.ofCard P hPcard, ?_⟩
    rw [Sylow.coe_ofCard]
    exact Subgroup.comap_mono hP1X
  obtain ⟨S, hST⟩ := hSylow
  have hconj : ∀ Q : Subgroup C, IsPGroup p Q →
      ∃ g : C, ∀ q ∈ Q, g * q * g⁻¹ ∈ T := by
    intro Q hQ
    obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S' S
    refine ⟨g, fun q hq => hST ?_⟩
    have h1 := Subgroup.smul_mem_pointwise_smul q (MulAut.conj g) (S' : Subgroup _) (hS' hq)
    have h2 : (MulAut.conj g • (S' : Subgroup C)) =
        ((g • S' : Sylow p C) : Subgroup C) := rfl
    rw [h2, hg] at h1
    exact h1
  have hpcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q := by
    intro Q hQ
    obtain ⟨g, hg⟩ := hconj Q hQ
    have := hcycT
    let φ : Q →* T := ((MulAut.conj g).toMonoidHom.comp Q.subtype).codRestrict T
      fun q => hg q q.2
    refine isCyclic_of_injective φ fun a b hab => ?_
    have h1 : g * (a : C) * g⁻¹ = g * (b : C) * g⁻¹ :=
      congrArg Subtype.val hab
    have h2 := (MulAut.conj g).injective h1
    exact Subtype.ext h2
  have hord_conj : ∀ x : C, orderOf x = p →
      ∃ g : C, g * x * g⁻¹ ∈ T := by
    intro x hx
    have hQ : IsPGroup p (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx, pow_one]
    obtain ⟨g, hg⟩ := hconj _ hQ
    exact ⟨g, hg x (Subgroup.mem_zpowers x)⟩
  have hcentral : ∀ z ∈ T, orderOf z = p → Subgroup.centralizer {z} = T := by
    intro z hzT hzp
    ext y
    constructor
    · intro hy
      have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 hy
      obtain ⟨x', hx', hxz⟩ := (show ι z ∈ X from hzT)
      have hx'p : orderOf x' = p := by
        rw [← orderOf_injective cg hcg x', hxz, orderOf_injective ι hι z, hzp]
      have hx'T : x' ∈ torusGroup τ L := (mem_twistedTorusOf.1 hx').1
      have hy'C : g0⁻¹ * ι y * g0 ∈ adjointGroup τ L :=
        mul_mem (mul_mem (inv_mem hg0C) (hιC y)) hg0C
      have hcomm : (g0⁻¹ * ι y * g0) * x' = x' * (g0⁻¹ * ι y * g0) := by
        have h1 : ι z * ι y = ι y * ι z := by rw [← map_mul, ← map_mul, hyz]
        have h2 : g0 * x' = ι z * g0 := by
          rw [← hxz, hcg_apply]
          group
        have h3 : x' * g0⁻¹ = g0⁻¹ * ι z := by
          rw [← hxz, hcg_apply]
          group
        calc g0⁻¹ * ι y * g0 * x' = g0⁻¹ * ι y * (ι z * g0) := by rw [mul_assoc _ g0, h2]
          _ = g0⁻¹ * (ι y * ι z) * g0 := by group
          _ = g0⁻¹ * (ι z * ι y) * g0 := by rw [h1]
          _ = (g0⁻¹ * ι z) * ι y * g0 := by group
          _ = x' * g0⁻¹ * ι y * g0 := by rw [h3]
          _ = x' * (g0⁻¹ * ι y * g0) := by group
      have hy'T := hcentL x' hx'T hx'p (hreg x' hx' hx'p) _ hy'C hcomm
      have hy'fix : n * Φ (g0⁻¹ * ι y * g0) * n⁻¹ =
          g0⁻¹ * ι y * g0 := by
        rw [map_mul, map_mul, map_inv, hg0, hιΦ y]
        group
      have hy'0 : g0⁻¹ * ι y * g0 ∈ twistedTorusOf n Φ := mem_twistedTorusOf.2 ⟨hy'T, hy'fix⟩
      show ι y ∈ X
      refine ⟨_, hy'0, ?_⟩
      rw [hcg_apply]
      group
    · intro hy
      have hcommT : ∀ a b : T, a * b = b * a := by
        intro a b
        have := hcycT
        exact (IsCyclic.commGroup : CommGroup T).mul_comm a b
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hcommT ⟨y, hy⟩ ⟨z, hzT⟩
      exact congrArg Subtype.val this
  refine ⟨T, hcycT, hTdvd, hTdiv, ⟨S, hST⟩, hpcyc, hord_conj, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := hord_conj x hx
  refine ⟨g, hg, hcentral _ hg ?_⟩
  exact (MulEquiv.orderOf_eq (MulAut.conj g) x).trans hx

end CFSG.RankThree.PartOne.KE
