module

public import CFSG.RankThree.PartOne.KE.SigmaMain

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial Pointwise

theorem solvable_normal_le_of_embedding_family {D G ι : Type*} [Group D] [Group G]
    (ψ : D →* G) (hψ : Function.Injective ψ) (P : ι → Subgroup G) (Z : Subgroup G)
    (hPψ : ∀ i, P i ≤ ψ.range) (hP : ∀ i, CFSG.IsQuasisimple (P i))
    (hnorm : ∀ i, ∀ d : D, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i)
    (hcent : ∀ d : D, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z)
    (V : Subgroup D) [hVn : V.Normal] [hV : Group.IsSolvable V] : V ≤ Z.comap ψ := fun v hv =>
  hcent v fun i u hu =>
    commutes_of_quasisimple_embedding ψ hψ (P i) (hPψ i) (hP i) (hnorm i) V v hv u hu

theorem sylow_conjugacy_of_subtorus_gen {τ : Tag} (d : ℕ) {C : Type} [Group C] [Finite C]
    {L : Type} [Field L] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (Φ : ModGL τ L →* ModGL τ L) (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Φ g0 = g0 * n) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {N : ℕ} (hN : N ≠ 0)
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ι.range.relIndex X ∣ d ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range)
    (Z : Subgroup (ModGL τ L)) (hZ : Z ≤ twistedTorusOf n Φ)
    (hcard : Nat.card Z = N)
    (hord : p ^ (Nat.card C).factorization p = p ^ N.factorization p) :
    Nat.card (subtorusImage ι g0 Z) ∣ N ∧ N / Nat.card (subtorusImage ι g0 Z) ∣ d ∧
      (∃ S : Sylow p C, (S : Subgroup C) ≤ subtorusImage ι g0 Z) ∧
      (∀ Q : Subgroup C, IsPGroup p Q → ∃ g : C, ∀ q ∈ Q, g * q * g⁻¹ ∈ subtorusImage ι g0 Z) := by
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
  exact ⟨hTdvd, hTdiv, ⟨S, hST⟩, hconj⟩

theorem sigma_embedding_data {τ : Tag} {C : Type} [Group C] {L : Type} [Field L] {ι' : Type}
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hιC : ∀ y, ι y ∈ adjointGroup τ L)
    (Φ : ModGL τ L →* ModGL τ L) (hιΦ : ∀ y, Φ (ι y) = ι y) (n g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime) (hordW : ¬ p ∣ Nat.card (WeylGroup τ))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (P : ι' → Subgroup (ModGL τ L)) (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan τ L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints n Φ) (hPadj : ∀ i, P i ≤ adjointGroup τ L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S)
    {x : C} (hx : orderOf x = p) (c : C)
    (hc : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g0⁻¹ * ι (c * x * c⁻¹) * g0 →
      rootCharKernel a ⊆ S) :
    ∃ ψ : Subgroup.centralizer ({x} : Set C) →* ModGL τ L, Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup τ L ⊔ rootSpan τ L S) ∧
      (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup τ L) ∧
      (∀ i, P i ≤ ψ.range) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
        ∀ v ∈ V, ψ v ∈ subtorusSigma n Φ S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Z := subtorusSigma n Φ S with hZdef
  set Q := rootSpan τ L S with hQdef
  set H := torusGroup τ L with hHdef
  set D := Subgroup.centralizer ({x} : Set C) with hD
  let ψ : D →* ModGL τ L :=
    ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp (MulAut.conj c).toMonoidHom)).comp D.subtype
  have hψ : ∀ y : D, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0 := fun y => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    have h1 := mul_right_cancel (mul_left_cancel hab)
    have h2 := hι h1
    have h3 : (a : C) = b := by
      have := congrArg (fun z => c⁻¹ * z * c) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hψmem : ∀ y : D, ψ y ∈ adjointGroup τ L := fun y => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg0C) (hιC _)) hg0C
  have hψfix : ∀ y : D, n * Φ (ψ y) * n⁻¹ = ψ y := fun y => by
    rw [hψ, map_mul, map_mul, map_inv, hg0, hιΦ]
    group
  have hxD : x ∈ D := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xD : D := ⟨x, hxD⟩ with hxDdef
  set h : ModGL τ L := ψ xD with hh
  have hhZ : h ∈ Z := by
    have := (mem_subtorusImage_iff ι g0 Z (c * x * c⁻¹)).1 hc
    rw [hh, hψ]
    exact this
  have hψx : h = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hψ xD
  have hordh : orderOf h = p := by
    rw [hh, orderOf_injective ψ hψinj xD, ← Subgroup.orderOf_coe]
    exact hx
  have hHh : h ∈ H := (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf n Φ S hhZ)).1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hHh
  have hord' : orderOf (rootDiagUnit τ a) = p := by rw [← ha]; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hord'
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hord'
  have hker := hkerZ a (ha.symm.trans hψx)
  have hcommh : ∀ y : D, ψ y * rootDiagUnit τ a = rootDiagUnit τ a * ψ y := fun y => by
    rw [← ha, hh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hHQ : ∀ y : D, ψ y ∈ H ⊔ Q := fun y => by
    have := mem_torus_mul_rootSpan_of_commute hp hordW hap ha1 hS hSn hker (hψmem y) (hcommh y)
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootSpan hS)] at this
  set Rs := twistedFixedPoints n Φ with hRs
  have hPψ : ∀ i, P i ≤ ψ.range := by
    intro i u hu
    have huR : n * Φ u * n⁻¹ = u := hPR i hu
    set P' : Subgroup (ModGL τ L) := (P i).map (MulAut.conj g0).toMonoidHom with hP'
    have hP'adj : P' ≤ adjointGroup τ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact mul_mem (mul_mem hg0C (hPadj i hv)) (inv_mem hg0C)
    have hP'fix : ∀ w ∈ P', Φ w = w := by
      rintro _ ⟨v, hv, rfl⟩
      have hvR : n * Φ v * n⁻¹ = v := hPR i hv
      change Φ (g0 * v * g0⁻¹) = g0 * v * g0⁻¹
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * n * Φ v * (g0 * n)⁻¹ = g0 * (n * Φ v * n⁻¹) * g0⁻¹ := by group
        _ = g0 * v * g0⁻¹ := by rw [hvR]
    have hPperf : ⁅P i, P i⁆ = P i := Subgroup.isPerfect_iff.1 (hPq i).1
    have hP'perf : ⁅P', P'⁆ = P' := by
      rw [hP', ← Subgroup.map_commutator, hPperf]
    have hmem : g0 * u * g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hu
    have hPfini : Finite (P i) := hPfin i
    have hP'fin : Finite P' := Finite.of_surjective
      ((MulAut.conj g0).toMonoidHom.subgroupMap (P i))
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective (P i))
    obtain ⟨y', hy'⟩ := hperf P' hP'fin hP'adj hP'fix hP'perf hmem
    have hιx' : ι (c * x * c⁻¹) = g0 * h * g0⁻¹ := by
      rw [hψx]
      group
    have huh : u * h = h * u := Subgroup.mem_centralizer_iff.1 hhZ.2 u (hPQ i hu)
    have hcomm' : y' * (c * x * c⁻¹) = (c * x * c⁻¹) * y' := by
      apply hι
      rw [map_mul ι y' (c * x * c⁻¹), map_mul ι (c * x * c⁻¹) y', hy', hιx']
      calc g0 * u * g0⁻¹ * (g0 * h * g0⁻¹) = g0 * (u * h) * g0⁻¹ := by group
        _ = g0 * (h * u) * g0⁻¹ := by rw [huh]
        _ = g0 * h * g0⁻¹ * (g0 * u * g0⁻¹) := by group
    have hyD : c⁻¹ * y' * c ∈ D := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc c⁻¹ * y' * c * x = c⁻¹ * (y' * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y') * c := by rw [hcomm']
        _ = x * (c⁻¹ * y' * c) := by group
    refine ⟨⟨c⁻¹ * y' * c, hyD⟩, ?_⟩
    rw [hψ]
    change g0⁻¹ * ι (c * (c⁻¹ * y' * c) * c⁻¹) * g0 = u
    rw [show c * (c⁻¹ * y' * c) * c⁻¹ = y' by group, hy']
    group
  have hnorm : ∀ i, ∀ d : D, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i := fun i d u hu =>
    hPnorm i (ψ d) (hHQ d) (hψfix d) u hu
  have hcent : ∀ d : D, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z := fun d hd =>
    hPcent (ψ d) (hHQ d) (hψfix d) hd
  refine ⟨ψ, hψinj, hψ, hHQ, hψfix, hψmem, hPψ, fun V hVn hVs v hv => ?_⟩
  have hle := solvable_normal_le_of_embedding_family ψ hψinj P Z hPψ hPq hnorm hcent V
  exact hle hv

end CFSG.RankThree.PartOne.KE
