module

public import CFSG.Sporadic.Recognition.CoverRecipeSq

public section

namespace CFSG.Sporadic.Recognition.CoverRecipe

open CFSG.CosetTable CFSG.LieType.Multipliers Subgroup
open scoped commutatorElement

variable {m : ℕ}

@[expose] def cubeWords (R : List (List (Fin m × Bool))) : List (List (Fin m × Bool)) :=
  R.map fun r => r ++ r ++ r

@[expose] def powWords (ord : Fin m → ℕ) : List (List (Fin m × Bool)) :=
  (List.finRange m).filterMap fun i =>
    if ord i = 0 then none else some (List.replicate (ord i) (i, true))

@[expose] def cover₃Words (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool))
    (ord : Fin m → ℕ) : List (List (Fin m × Bool)) :=
  (coverWords R w ++ cubeWords R ++ powWords ord).mergeSort fun a b => decide (a.length ≤ b.length)

theorem mem_cover₃Words {R : List (List (Fin m × Bool))} {w : Fin m → List (Fin m × Bool)}
    {ord : Fin m → ℕ} {x : List (Fin m × Bool)} :
    x ∈ cover₃Words R w ord ↔ x ∈ coverWords R w ∨ x ∈ cubeWords R ∨ x ∈ powWords ord := by
  unfold cover₃Words
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_append, List.mem_append, or_assoc]

theorem mk_replicate (i : Fin m) (d : ℕ) :
    FreeGroup.mk (List.replicate d (i, true)) = FreeGroup.of i ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [List.replicate_succ, pow_succ', ← ih]
    rfl

theorem lift_cover₃_eq_one {X : Type*} [Group X] {g : Fin m → X} {R : List (List (Fin m × Bool))}
    {cw : Fin m → List (Fin m × Bool)} {ord : Fin m → ℕ}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i)
    (hpow : ∀ i, ord i ≠ 0 → g i ^ ord i = 1) :
    ∀ w ∈ cover₃Words R cw ord, FreeGroup.lift g (FreeGroup.mk w) = 1 := by
  intro w hwm
  rw [mem_cover₃Words] at hwm
  simp only [coverWords, cubeWords, powWords, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and, List.mem_filterMap] at hwm
  rcases hwm with (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩) | ⟨r, hr, rfl⟩ | ⟨i, hi⟩
  · rw [mk_commWord, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
      map_commutatorElement, FreeGroup.lift_apply_of, hR r hr]
    simp [commutatorElement_def]
  · rw [show FreeGroup.mk ((i, false) :: cw i) = (FreeGroup.of i)⁻¹ * FreeGroup.mk (cw i) from rfl,
      map_mul, map_inv, FreeGroup.lift_apply_of, hw i, inv_mul_cancel]
  · have e : FreeGroup.mk (r ++ r ++ r) = FreeGroup.mk r ^ 3 := by
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, pow_three']
    rw [e, map_pow, hR r hr, one_pow]
  · by_cases h0 : ord i = 0
    · simp [h0] at hi
    · rw [ite_eq_right h0, Option.some.injEq] at hi
      rw [← hi, mk_replicate, map_pow, FreeGroup.lift_apply_of, hpow i h0]

theorem card_le_card_cover₃ {X : Type*} [Group X] {g : Fin m → X}
    (hgen : Subgroup.closure (Set.range g) = ⊤) {R : List (List (Fin m × Bool))}
    {cw : Fin m → List (Fin m × Bool)} {ord : Fin m → ℕ}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i)
    (hpow : ∀ i, ord i ≠ 0 → g i ^ ord i = 1) [Finite (PG m (cover₃Words R cw ord))] :
    Nat.card X ≤ Nat.card (PG m (cover₃Words R cw ord)) := by
  let π : PG m (cover₃Words R cw ord) →* X := PresentedGroup.toGroup (f := g) fun r hr => by
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hr
    exact lift_cover₃_eq_one hR hw hpow w hwm
  have hsurj : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of,
      MonoidHom.map_closure, ← Set.range_comp]
    have : (π ∘ PresentedGroup.of) = g := funext fun i => PresentedGroup.toGroup.of _
    rw [this]
    exact hgen
  have : Finite X := Finite.of_surjective π hsurj
  exact Nat.card_le_card_of_surjective π hsurj

def cubeSubgroup {M : Type*} [Group M] (C : Subgroup M) (hC : C ≤ center M) : Subgroup M where
  carrier := {x | ∃ z ∈ C, x = z ^ 3}
  mul_mem' := fun {x y} hx hy => by
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨z * w, mul_mem hz hw, ?_⟩
    exact (Commute.mul_pow (Subgroup.mem_center_iff.mp (hC hw) z) 3).symm
  one_mem' := ⟨1, one_mem _, (one_pow 3).symm⟩
  inv_mem' := fun {x} hx => by
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z⁻¹, inv_mem hz, (inv_pow z 3).symm⟩

theorem mem_cubeSubgroup {M : Type*} [Group M] {C : Subgroup M} {hC : C ≤ center M} {x : M} :
    x ∈ cubeSubgroup C hC ↔ ∃ z ∈ C, x = z ^ 3 := by
  unfold cubeSubgroup
  exact Iff.rfl

theorem eq_bot_of_cubes {M : Type*} [Group M] [Finite M] {C : Subgroup M} (hC : IsPGroup 3 C)
    (hcube : ∀ z ∈ C, ∃ b ∈ C, b ^ 3 = z) : C = ⊥ := by
  let f : C → C := fun b => ⟨b.1 ^ 3, C.pow_mem b.2 3⟩
  have hsurj : Function.Surjective f := fun z => by
    obtain ⟨b, hb, hbz⟩ := hcube z.1 z.2
    exact ⟨⟨b, hb⟩, Subtype.ext hbz⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
  by_contra hne
  have hcard : Nat.card C ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  have h3 : 3 ∣ Nat.card C := by
    rcases n with _ | n
    · exact absurd hn hcard
    · rw [hn]; exact dvd_pow_self 3 (Nat.succ_ne_zero n)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hxx : f x = f 1 := Subtype.ext (by simpa [f] using congrArg Subtype.val hx3)
  have := hinj hxx
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem exists_canonical_lift {M X : Type*} [Group M] [Finite M] [Group X] (π : M →* X)
    (hker : π.ker ≤ center M) (hp : IsPGroup 3 π.ker) (hπ : Function.Surjective π) {y : X}
    {d : ℕ} (hy : y ^ d = 1) (hd : d.Coprime 3) : ∃ e : M, π e = y ∧ e ^ d = 1 := by
  obtain ⟨a, rfl⟩ := hπ y
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hcop : (Nat.card π.ker).Coprime d := by
    rw [hn]; exact Nat.Coprime.pow_left n hd.symm
  have hmem : a ^ d ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]; exact hy
  obtain ⟨x, hx⟩ := (powCoprime hcop).surjective (⟨a ^ d, hmem⟩ : π.ker)⁻¹
  have hxd : x.1 ^ d = (a ^ d)⁻¹ := by
    have := congrArg Subtype.val hx
    simpa using this
  have hcomm : Commute a x.1 := Subgroup.mem_center_iff.mp (hker x.2) a
  refine ⟨a * x.1, ?_, ?_⟩
  · rw [map_mul, (MonoidHom.mem_ker.mp x.2), mul_one]
  · rw [hcomm.mul_pow, hxd, mul_inv_cancel]

theorem ker_eq_bot_of_cover₃ {X : Type} [Group X] {g : Fin m → X}
    (hgen : Subgroup.closure (Set.range g) = ⊤) {R : List (List (Fin m × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1) {cw : Fin m → List (Fin m × Bool)}
    {ord : Fin m → ℕ}
    (hA : ∀ i, ord i = 0 → FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)) ∧
      FreeGroup.lift g (FreeGroup.mk (cw i)) = g i)
    (hB : ∀ i, ord i ≠ 0 → cw i = [(i, true)] ∧ g i ^ ord i = 1 ∧ (ord i).Coprime 3)
    (hfin : Finite (PG m (cover₃Words R cw ord)))
    (hcard : Nat.card (PG m (cover₃Words R cw ord)) ≤ Nat.card X) {M : Type} [Group M]
    [Finite M] (π : M →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ center M)
    (hp : IsPGroup 3 π.ker) (hder : π.ker ≤ commutator M) : π.ker = ⊥ := by
  classical
  have hXfin : Finite X := Finite.of_surjective _ hπ
  have hcomp : ∀ b : Fin m → M, π.comp (FreeGroup.lift b) = FreeGroup.lift (fun i => π (b i)) :=
    fun b => FreeGroup.ext_hom _ _ fun i => by simp
  choose a ha using fun i => hπ (g i)
  have hex : ∀ i, ∃ e : M, π e = g i ∧ (ord i = 0 → e = FreeGroup.lift a (FreeGroup.mk (cw i))) ∧
      (ord i ≠ 0 → e ^ ord i = 1) := by
    intro i
    by_cases hi : ord i = 0
    · refine ⟨FreeGroup.lift a (FreeGroup.mk (cw i)), ?_, fun _ => rfl, fun h => absurd hi h⟩
      rw [← MonoidHom.comp_apply, hcomp, show (fun j => π (a j)) = g from funext ha]
      exact (hA i hi).2
    · obtain ⟨hcw, hgo, hcop⟩ := hB i hi
      obtain ⟨e, he1, he2⟩ := exists_canonical_lift π hker hp hπ hgo hcop
      exact ⟨e, he1, fun h => absurd h hi, fun _ => he2⟩
  choose ee hπee hee0 hee1 using hex
  have hqee : (fun i => π (ee i)) = g := funext hπee
  have hfix : ∀ i, FreeGroup.lift ee (FreeGroup.mk (cw i)) = ee i := by
    intro i
    by_cases hi : ord i = 0
    · rw [hee0 i hi]
      exact eq_of_mem_commutator_of_central π hker (FreeGroup.lift ee) (FreeGroup.lift a)
        (by rw [hcomp, hcomp, hqee, show (fun j => π (a j)) = g from funext ha]) (hA i hi).1
    · rw [(hB i hi).1, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
        FreeGroup.lift_apply_of]
  have hrc : ∀ r ∈ R, FreeGroup.lift ee (FreeGroup.mk r) ∈ π.ker := fun r hr => by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp, hqee]
    exact hR r hr
  set N : Subgroup M := cubeSubgroup π.ker hker with hNdef
  have hNle : N ≤ π.ker := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_cubeSubgroup.1 hx
    exact pow_mem hz 3
  have hNn : N.Normal := Subgroup.normal_of_le_center (hNle.trans hker)
  set M₀ : Subgroup M := Subgroup.closure (Set.range ee) with hM₀
  have hmap : M₀.map π = ⊤ := by
    rw [hM₀, MonoidHom.map_closure, ← Set.range_comp]
    have : (π ∘ ee) = g := hqee
    rw [this]
    exact hgen
  have hsplit : ∀ x : M, ∃ y ∈ M₀, ∃ z ∈ π.ker, x = y * z := fun x => by
    have : π x ∈ M₀.map π := by rw [hmap]; trivial
    obtain ⟨y, hy, hyx⟩ := this
    refine ⟨y, hy, y⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have hcom : commutator M ≤ M₀ := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨x1, hx1, z1, hz1, rfl⟩ := hsplit x
    obtain ⟨y1, hy1, z2, hz2, rfl⟩ := hsplit y
    rw [commutator_mul_center (hker hz1) (hker hz2), commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx1 hy1) (inv_mem hx1)) (inv_mem hy1)
  have hKM₀ : π.ker ≤ M₀ := hder.trans hcom
  let ē : Fin m → M ⧸ N := fun i => (ee i : M ⧸ N)
  have hlift : FreeGroup.lift ē = (QuotientGroup.mk' N).comp (FreeGroup.lift ee) :=
    FreeGroup.ext_hom _ _ fun i => by simp [ē]
  have hrel : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ (cover₃Words R cw ord).map FreeGroup.mk},
      FreeGroup.lift ē r = 1 := by
    intro r hr
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hr
    rw [hlift, MonoidHom.comp_apply]
    rw [mem_cover₃Words] at hwm
    simp only [coverWords, cubeWords, powWords, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and, List.mem_filterMap] at hwm
    rcases hwm with (⟨i, r', hr', rfl⟩ | ⟨i, rfl⟩) | ⟨r', hr', rfl⟩ | ⟨i, hi⟩
    · rw [mk_commWord, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
        map_commutatorElement, FreeGroup.lift_apply_of]
      have hc := mem_center_iff.mp (hker (hrc r' hr')) (ee i)
      rw [commutatorElement_eq_one_iff_mul_comm.2 hc, map_one]
    · rw [show FreeGroup.mk ((i, false) :: cw i) = (FreeGroup.of i)⁻¹ * FreeGroup.mk (cw i) from
        rfl, map_mul, map_inv, FreeGroup.lift_apply_of, hfix i, inv_mul_cancel, map_one]
    · have e : FreeGroup.mk (r' ++ r' ++ r') = FreeGroup.mk r' ^ 3 := by
        rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, pow_three']
      rw [e, map_pow]
      exact (QuotientGroup.eq_one_iff _).2 (mem_cubeSubgroup.2 ⟨_, hrc r' hr', rfl⟩)
    · by_cases h0 : ord i = 0
      · simp [h0] at hi
      · rw [ite_eq_right h0, Option.some.injEq] at hi
        rw [← hi, mk_replicate, map_pow, FreeGroup.lift_apply_of, hee1 i h0, map_one]
  let ψ : PG m (cover₃Words R cw ord) →* M ⧸ N := PresentedGroup.toGroup (f := ē) hrel
  have hψ : ∀ y ∈ M₀, (y : M ⧸ N) ∈ ψ.range := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hrel⟩
    | one => exact ⟨1, by simp⟩
    | mul x y _ _ hx hy => exact mul_mem hx hy
    | inv x _ hx => exact inv_mem hx
  have hNker : N ≤ π.ker := hNle
  let qb : M ⧸ N →* X := QuotientGroup.lift N π hNker
  have hqb : ∀ x : M, qb (x : M ⧸ N) = π x := fun x => rfl
  have hsurj : Function.Surjective (qb.comp ψ) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨PresentedGroup.of i, ?_⟩
    rw [MonoidHom.comp_apply, PresentedGroup.toGroup.of hrel]
    exact (hqb (ee i)).trans (hπee i)
  have hbij : Function.Bijective (qb.comp ψ) := hsurj.bijective_of_nat_card_le hcard
  have hKN : ∀ z ∈ π.ker, z ∈ N := fun z hz => by
    obtain ⟨p, hp1⟩ := hψ z (hKM₀ hz)
    have h1 : (qb.comp ψ) p = (qb.comp ψ) 1 := by
      rw [MonoidHom.comp_apply, hp1, map_one]
      exact (hqb z).trans (MonoidHom.mem_ker.mp hz)
    have h2 : p = 1 := hbij.1 h1
    rw [h2, map_one] at hp1
    exact (QuotientGroup.eq_one_iff z).1 hp1.symm
  refine eq_bot_of_cubes hp fun z hz => ?_
  obtain ⟨b, hb, hbz⟩ := hKN z hz
  exact ⟨b, hb, hbz.symm⟩

end CFSG.Sporadic.Recognition.CoverRecipe
