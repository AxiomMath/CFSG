module

public import CFSG.RankThree.PartOne.SLBN.Global5
public import CFSG.RankThree.PartOne.SLBN.Bridge
public import CFSG.RankThree.PartOne.SLBN.Pairs
public import CFSG.RankThree.PartOne.SLBN.LocalFive
public import CFSG.RankThree.PartOne.SLBN.SmallAction

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup CFSG CFSG.OrderReductions.FrattiniAutomorphisms

theorem hasPair_of_minimal_cover {S X : Type} [Group S] [Finite S] [IsSimpleGroup S] [Group X]
    [Finite X]
    (hclosed : ∀ (Y : Type) [Group Y] [Finite Y] (φ : Y →* S), Function.Surjective φ →
      IsPGroup 3 φ.ker → φ.ker ≤ Subgroup.center Y →
        (∀ M : Subgroup Y, M.map φ = ⊤ → M = ⊤) → φ.ker = ⊥)
    (P : Subgroup S) (hP : Nat.card P = 25)
    (hLL : ∀ (Q : Type) [Group Q] [Finite Q] (ρ : Q →* X), Function.Surjective ρ →
      IsPGroup 3 ρ.ker → (∀ E : Subgroup Q, IsElementaryAbelian 3 E → Nat.card E ≤ 27) →
        IsCyclic ρ.ker)
    {n : ℕ} (b : Fin n → S) (ι : Fin n → X →* S) (hb2 : ∀ i, orderOf (b i) = 2)
    (hιker : ∀ i A, ι i A = 1 → A ^ 2 = 1) (hιc : ∀ i g, ι i g * b i = b i * ι i g)
    (hV : ∀ (V : Type) [CommGroup V] [Finite V], (∀ x : V, x ^ 3 = 1) → ∀ ρ : S →* MulAut V,
      (∀ i, Nat.card {v : V | ρ (b i) v = v} ≤ 3) → Nat.card V ≤ 3 ^ 7)
    (hpair : HasPair 3 S)
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] (φ : Y →* S)
    (hφ : Function.Surjective φ) (hker : IsPGroup 3 φ.ker)
    (hmin : ∀ M : Subgroup Y, M.map φ = ⊤ → M = ⊤) : HasPair 3 Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  have hlift : ∀ i, ∃ b' : Y, orderOf b' = 2 ∧ φ b' = b i := fun i =>
    CFSG.RankThree.PartOne.SRC.exists_involution_lift φ Nat.prime_three (by norm_num) hker
      (hb2 i) (hφ (b i))
  choose b' hb'2 hb'φ using hlift
  have hb'sq : ∀ i, b' i ^ 2 = 1 := fun i => by
    have := pow_orderOf_eq_one (b' i)
    rwa [hb'2 i] at this
  have hcyc : ∀ i, IsCyclic ↥(φ.ker ⊓ Subgroup.centralizer ({b' i} : Set Y)) := by
    intro i
    refine isCyclic_ker_inf_centralizer φ hφ hker (ι i) (hιker i) (t := b i)
      (fun g => hιc i g) (hb'2 i) (hb'φ i) ?_ hLL
    intro E hE hEel
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
    have hk4 : 4 ≤ k := by
      by_contra h
      push Not at h
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hno (hasPair_of_centralizer (hb'2 i) hEel hk4 hk hE)
  let K : Subgroup Y := φ.ker
  have hK1 : ∀ y ∈ K, frattiniConj K y = 1 := fun y hy => frattiniConj_eq_one_of_mem K hker hy
  let ρb : S →* MulAut (↥K ⧸ frattini ↥K) :=
    (QuotientGroup.lift K (frattiniConj K) (fun y hy => hK1 y hy)).comp
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
  have hρb : ∀ y : Y, ρb (φ y) = frattiniConj K y := by
    intro y
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ y) = (y : Y ⧸ K) :=
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm_apply_eq.mpr rfl
    have h2 : ρb (φ y) = QuotientGroup.lift K (frattiniConj K) (fun y hy => hK1 y hy)
        ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ y)) := rfl
    rw [h2, h1]
    rfl
  have hel := isElementaryAbelian_frattini_quotient K hker
  have hcomm : ∀ x y : ↥K ⧸ frattini ↥K, x * y = y * x := hel.toIsMulCommutative.is_comm.comm
  have hpow : ∀ x : ↥K ⧸ frattini ↥K, x ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 _)
  let _ : CommGroup (↥K ⧸ frattini ↥K) :=
    { (inferInstance : Group (↥K ⧸ frattini ↥K)) with mul_comm := hcomm }
  have hcardQ : Nat.card (↥K ⧸ frattini ↥K) ≤ 3 ^ 7 := by
    refine hV (↥K ⧸ frattini ↥K) hpow ρb fun i => ?_
    have := card_fixed_le_three K hker (hb'sq i) (hcyc i)
    have e : {v : ↥K ⧸ frattini ↥K | ρb (b i) v = v} =
        {q : ↥K ⧸ frattini ↥K | frattiniConj K (b' i) q = q} := by
      ext q
      simp only [Set.mem_ofPred_eq]
      rw [← hb'φ i, hρb]
    rw [e]
    exact this
  have hρ1 : ρb = 1 :=
    mulAut_hom_eq_one_of_small hcomm hpow hcardQ P hP ρb
  have hψ1 : ∀ y : Y, frattiniConj K y = 1 := fun y => by
    rw [← hρb, hρ1]; rfl
  have hcen : K ≤ Subgroup.center Y := by
    have hPker : IsPGroup 3 (quotientAutomorphism (frattini ↥K)).ker :=
      (CFSG.GroupTheory.frattini_automorphism_kernel hker).2
    have hα : (MulAut.conjNormal : Y →* MulAut ↥K) = 1 :=
      eq_one_of_perfect_of_range_isPGroup _ _ hPker (fun y => by
        rw [MonoidHom.mem_ker]
        exact hψ1 y)
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun a : MulAut ↥K => ((a ⟨k, hk⟩ : ↥K) : Y)) (congrArg (fun f => f y) hα)
    simp only [MulAut.conjNormal_apply] at h
    calc y * k = (y * k * y⁻¹) * y := by group
      _ = k * y := by rw [show y * k * y⁻¹ = k from h]
  have hbot : K = ⊥ := hclosed Y φ hφ hker hcen hmin
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hbot
  let e : Y ≃* S := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  exact hno (hpair.map e.symm.toMonoidHom e.symm.injective)

theorem rankFourCover_nine_core {S X : Type} [Group S] [Finite S] [IsSimpleGroup S] [Group X]
    [Finite X] (hperf : Group.IsPerfect S)
    (hclosed : ∀ (Y : Type) [Group Y] [Finite Y] (φ : Y →* S), Function.Surjective φ →
      IsPGroup 3 φ.ker → φ.ker ≤ Subgroup.center Y →
        (∀ M : Subgroup Y, M.map φ = ⊤ → M = ⊤) → φ.ker = ⊥)
    (P : Subgroup S) (hP : Nat.card P = 25)
    (hLL : ∀ (Q : Type) [Group Q] [Finite Q] (ρ : Q →* X), Function.Surjective ρ →
      IsPGroup 3 ρ.ker → (∀ E : Subgroup Q, IsElementaryAbelian 3 E → Nat.card E ≤ 27) →
        IsCyclic ρ.ker)
    {n : ℕ} (b : Fin n → S) (ι : Fin n → X →* S) (hb2 : ∀ i, orderOf (b i) = 2)
    (hιker : ∀ i A, ι i A = 1 → A ^ 2 = 1) (hιc : ∀ i g, ι i g * b i = b i * ι i g)
    (hV : ∀ (V : Type) [CommGroup V] [Finite V], (∀ x : V, x ^ 3 = 1) → ∀ ρ : S →* MulAut V,
      (∀ i, Nat.card {v : V | ρ (b i) v = v} ≤ 3) → Nat.card V ≤ 3 ^ 7)
    (hpair : HasPair 3 S) : CFSG.RankThree.PartOne.SRC.RankFourCover 3 S := by
  classical
  intro Y _ _ φ hφ hker
  obtain ⟨Y₀, -, hY₀min⟩ := Finite.exists_le_minimal
    (p := fun M : Subgroup Y => M.map φ = ⊤) (a := ⊤) (by rw [Subgroup.map_top_of_surjective φ hφ])
  set φ₀ : Y₀ →* S := φ.comp Y₀.subtype with hφ₀
  have hφ₀s : Function.Surjective φ₀ := by
    intro x
    have hx : x ∈ Y₀.map φ := by
      rw [hY₀min.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin₀ : ∀ M : Subgroup Y₀, M.map φ₀ = ⊤ → M = ⊤ := by
    intro M hM
    have h1 : (M.map Y₀.subtype).map φ = ⊤ := by
      rw [Subgroup.map_map]
      exact hM
    have h2 := hY₀min.le_of_le h1 (Subgroup.map_subtype_le M)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  have hker₀ : IsPGroup 3 φ₀.ker := by
    intro x
    have hx1 : φ ((x : Y₀) : Y) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : Y₀) : Y), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : φ.ker => (z : Y)) hk))⟩
  have hperf₀ : Group.IsPerfect Y₀ := by
    rw [Group.isPerfect_def]
    apply hmin₀
    have h1 := hperf.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hφ₀s]
    rwa [_root_.commutator_def] at h1
  have := hperf₀
  exact (hasPair_of_minimal_cover hclosed P hP hLL b ι hb2 hιker hιc hV hpair φ₀ hφ₀s hker₀
    hmin₀).map Y₀.subtype Y₀.subtype_injective

end CFSG.RankThree.PartOne.SLBN
