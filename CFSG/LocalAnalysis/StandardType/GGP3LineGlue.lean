module

public import CFSG.LocalAnalysis.StandardType.GGReflNormLine
public import CFSG.LocalAnalysis.StandardType.GGP3LineNormalizer
public import CFSG.LocalAnalysis.StandardType.GGP3Witness
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGLineTest {Λ : Type} [Fintype Λ] [DecidableEq Λ] (X : Matrix (Option Λ) (Option Λ) ℤ)
    (p : ℕ) : Prop :=
  ∃ (ψ : List (Option Λ)) (k : Option Λ) (ρ : Option Λ → ℤ), ρ ∈ ggLCoroots X ∧
    ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod p) = 0 ∧
    ∀ v ∈ ggLCoroots X, ∀ r : (ZMod p)ˣ,
      (fun i => (ρ i : ZMod p) -
          ((∑ i', ggSWordR X ψ (Pi.single k 1) i' * ∑ j, X i' j * ρ j : ℤ) : ZMod p) *
            (ggSWord X ψ (Pi.single k 1) i : ZMod p)) ≠ fun i => (r : ZMod p) * (v i : ZMod p)

private theorem p3lg_gen_refl {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    {X : Matrix (Option Λ) (Option Λ) ℤ} {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V} {ι : Additive ↥Bs ≃+ V}
    (hD : GGExtDatum ι X φ' h' α') (hp2 : p ≠ 2) (o : Option Λ) :
    GGIsReflection p (φ' o) := by
  have hfx : α' o (h' o) = 2 := by
    rw [hD.pair o o, hD.diag o]
    norm_num
  exact ggIsReflection_of_eq_reflection hp2 ι hfx
    (ggLin_eq_reflection ι hfx (hD.lin o))

private theorem p3lg_prod_inv_eq_reverse_prod {M : Type} [Group M] (l : List M)
    (h : ∀ x ∈ l, x⁻¹ = x) : l.prod⁻¹ = l.reverse.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, mul_inv_rev, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem p3lg_exists_word {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ} {Λ : Type}
    {φ' : Option Λ → MulAut ↥Bs} (hgen : ∀ i : Λ, GGIsReflection p (φ' (some i)))
    {w : MulAut ↥Bs} (hw : w ∈ Subgroup.closure (Set.range fun i : Λ => φ' (some i))) :
    ∃ ψ : List Λ, w = (ψ.map fun i => φ' (some i)).prod := by
  let K : Subgroup (MulAut ↥Bs) :=
    { carrier := {w | ∃ ψ : List Λ, w = (ψ.map fun i => φ' (some i)).prod}
      one_mem' := ⟨[], by simp⟩
      mul_mem' := by
        rintro x y ⟨ψ₁, rfl⟩ ⟨ψ₂, rfl⟩
        exact ⟨ψ₁ ++ ψ₂, by rw [List.map_append, List.prod_append]⟩
      inv_mem' := by
        rintro x ⟨ψ, rfl⟩
        have hself : ∀ z ∈ ψ.map (fun i => φ' (some i)), z⁻¹ = z := by
          intro z hz
          rw [List.mem_map] at hz
          obtain ⟨i, -, rfl⟩ := hz
          exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using (hgen i).1)
        refine ⟨ψ.reverse, ?_⟩
        rw [List.map_reverse, ← p3lg_prod_inv_eq_reverse_prod (ψ.map fun i => φ' (some i)) hself] }
  have hle : Subgroup.closure (Set.range fun i : Λ => φ' (some i)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨[i], by simp⟩
  exact hle hw

private theorem p3lg_coeff_unique {V : Type} [AddCommGroup V] {p : ℕ} [Module (ZMod p) V]
    {Λ : Type} [Fintype Λ] {h' : Option Λ → V} (hind : LinearIndependent (ZMod p) h')
    {a b : Option Λ → ZMod p} (h : ∑ j, a j • h' j = ∑ j, b j • h' j) : a = b := by
  funext j
  have h0 : ∑ i, (a - b) i • h' i = 0 := by
    simp only [Pi.sub_apply, sub_smul]
    rw [Finset.sum_sub_distrib, h, sub_self]
  have h1 := (Fintype.linearIndependent_iff.mp hind (a - b)) h0 j
  have h2 : a j - b j = 0 := by simpa [Pi.sub_apply] using h1
  exact sub_eq_zero.mp h2

private theorem p3lg_vec_mem_orbit {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ} {φ' : Option Λ → MulAut ↥Bs}
    {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') {ρ : Option Λ → ℤ} (hρ : ρ ∈ ggLCoroots X) :
    ∃ u₀ ∈ Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ' (some i))), ∃ i₀ : Λ,
      ∑ i, ((ρ i : ℤ) : ZMod p) • h' i = u₀ (h' (some i₀)) := by
  obtain ⟨ψρ, i₀, rfl⟩ := hρ
  refine ⟨ggLin (p := p) ι ((ψρ.map fun j => φ' (some j)).prod), ?_, i₀, ?_⟩
  · rw [map_list_prod]
    refine Subgroup.list_prod_mem _ (fun z hz => ?_)
    rw [List.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [List.mem_map] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · have hm : (ψρ.map fun j => φ' (some j)).prod = ((ψρ.map some).map φ').prod := by
      rw [List.map_map, Function.comp_def]
    rw [hm]
    exact ((ggExtDatum_word hD (ψρ.map some) (some i₀)).1).symm

private theorem p3lg_orbit_mem_coroots {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (hp2 : p ≠ 2)
    {u : V ≃ₗ[ZMod p] V}
    (hu : u ∈ Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ' (some i))))
    (m : Λ) :
    ∃ v ∈ ggLCoroots X, u (h' (some m)) = ∑ i, ((v i : ℤ) : ZMod p) • h' i := by
  have hgen : ∀ i : Λ, GGIsReflection p (φ' (some i)) :=
    fun i => p3lg_gen_refl hD hp2 (some i)
  have hmap : (Subgroup.closure (Set.range fun i : Λ => φ' (some i))).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ' (some i))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hu' : u ∈ (Subgroup.closure (Set.range fun i : Λ => φ' (some i))).map
      (ggLin (p := p) ι) := by
    rw [hmap]
    exact hu
  obtain ⟨w, hw, hwmap⟩ := Subgroup.mem_map.mp hu'
  obtain ⟨ψu, hψu⟩ := p3lg_exists_word (p := p) hgen hw
  refine ⟨ggSWord X (ψu.map some) (Pi.single (some m) 1), ⟨ψu, m, rfl⟩, ?_⟩
  rw [← hwmap, hψu]
  have hm : (ψu.map fun j => φ' (some j)).prod = ((ψu.map some).map φ').prod := by
    rw [List.map_map, Function.comp_def]
  rw [hm]
  exact (ggExtDatum_word hD (ψu.map some) (some m)).1

private theorem p3lg_action_coords {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α')
    (ψ : List (Option Λ)) (k : Option Λ) (ρ : Option Λ → ℤ) :
    ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹)
        (∑ i, ((ρ i : ℤ) : ZMod p) • h' i) =
      ∑ i, ((ρ i : ZMod p) -
        ((∑ i', ggSWordR X ψ (Pi.single k 1) i' * ∑ j, X i' j * ρ j : ℤ) : ZMod p) *
          (ggSWord X ψ (Pi.single k 1) i : ZMod p)) • h' i := by
  have hA : (∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) *
      α' i (∑ j, ((ρ j : ℤ) : ZMod p) • h' j)) =
      ((∑ i', ggSWordR X ψ (Pi.single k 1) i' * ∑ j, X i' j * ρ j : ℤ) : ZMod p) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hαi : α' i (∑ j, ((ρ j : ℤ) : ZMod p) • h' j) =
        ∑ j, ((ρ j : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, hD.pair i j]
    have hinner : (∑ j, ((ρ j : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) =
        ((∑ j, X i j * ρ j : ℤ) : ZMod p) := by
      rw [Int.cast_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Int.cast_mul]
      ring
    rw [hαi, Int.cast_mul, hinner]
  rw [(ggExtDatum_word hD ψ k).2.2 (∑ i, ((ρ i : ℤ) : ZMod p) • h' i), hA,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul, sub_smul]

private theorem p3lg_sRefl_neg {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (j : N) (m : N → ℤ) : ggSRefl X j (-m) = -(ggSRefl X j m) := by
  funext i
  have hsum : (∑ k, X j k * -(m k)) = -(∑ k, X j k * m k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [ggSRefl, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  ring

private theorem p3lg_word_append {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (l₁ l₂ : List N) (m : N → ℤ) :
    ggSWord X (l₁ ++ l₂) m = ggSWord X l₁ (ggSWord X l₂ m) := by
  induction l₁ with
  | nil => rfl
  | cons j l ih =>
    show ggSRefl X j (ggSWord X (l ++ l₂) m) = ggSRefl X j (ggSWord X l (ggSWord X l₂ m))
    rw [ih]

private theorem p3lg_word_neg {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (l : List N) (m : N → ℤ) : ggSWord X l (-m) = -(ggSWord X l m) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    show ggSRefl X j (ggSWord X l (-m)) = -(ggSRefl X j (ggSWord X l m))
    rw [ih, p3lg_sRefl_neg]

private theorem p3lg_sRefl_single {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (X : Matrix (Option Λ) (Option Λ) ℤ) {i : Λ} (hX : X (some i) (some i) = 2) :
    ggSRefl X (some i) (Pi.single (some i) 1) = -(Pi.single (some i) 1) := by
  funext o
  have hsum : (∑ k : Option Λ,
      X (some i) k * (Pi.single (some i) (1 : ℤ) : Option Λ → ℤ) k) = 2 := by
    rw [Fintype.sum_eq_single (some i)]
    · rw [Pi.single_eq_same, mul_one, hX]
    · intro k hk
      have h : (Pi.single (some i) (1 : ℤ) : Option Λ → ℤ) k = 0 := by
        rw [Pi.single_apply]
        exact if_neg hk
      rw [h, mul_zero]
  simp only [ggSRefl, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  ring

private theorem p3lg_neg_mem_coroots {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {X : Matrix (Option Λ) (Option Λ) ℤ} (hX : ∀ j : Λ, X (some j) (some j) = 2)
    {v : Option Λ → ℤ} (hv : v ∈ ggLCoroots X) : -v ∈ ggLCoroots X := by
  obtain ⟨ψ, i, rfl⟩ := hv
  refine ⟨ψ ++ [i], i, ?_⟩
  rw [List.map_append, List.map_cons, List.map_nil, p3lg_word_append,
    show ggSWord X [some i] (Pi.single (some i) 1) = -(Pi.single (some i) 1) from
      p3lg_sRefl_single X (hX i),
    p3lg_word_neg]

theorem ggFork_false_of_lineTest (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M fun i j => X (some i) (some j))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)))
    (hT : GGLineTest X p) : False := by
  obtain ⟨ψ, k, ρ, hρ, ha, htest⟩ := hT
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  have hFT : TauCeti.IsFiniteType (fun i j => X (some i) (some j)) :=
    isFiniteType_of_ggIsWeylMatrixFixed hM hC
  have hind : LinearIndependent (ZMod p) (fun i : Λ => h' (some i)) :=
    hD.indep.comp some (Option.some_injective _)
  have hRC : GGReflClosed (fun i : Λ => ggLin (p := p) ι (φ' (some i))) :=
    ggReflClosed_of_indep (p := p) hp hFT hC (fun i => h' (some i)) (fun i => α' (some i))
      (fun i j => hD.pair (some i) (some j)) hind
      (fun i => ggLin (p := p) ι (φ' (some i))) (fun i v => hD.lin (some i) v)
  have hs : ∀ i v, ggLin (p := p) ι (φ' (some i)) v = v - α' (some i) v • h' (some i) :=
    fun i v => hD.lin (some i) v
  have hα : ∀ i, α' (some i) (h' (some i)) = 2 := by
    intro i
    rw [hD.pair (some i) (some i), hD.diag (some i)]
    norm_num
  have h0 : ∀ i, h' (some i) ≠ 0 := fun i => hD.indep.ne_zero (some i)
  have hTn : ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) ∈
      Subgroup.normalizer (Subgroup.closure (Set.range fun i : Λ =>
        ggLin (p := p) ι (φ' (some i))) : Set (V ≃ₗ[ZMod p] V)) :=
    ggExtDatum_lin_mem_normalizer ha₀ hcfg hD hAL ψ k ha
  obtain ⟨u₀, hu₀, i₀, hρu₀⟩ := p3lg_vec_mem_orbit (p := p) hD hρ
  obtain ⟨u, hu, m, r, hr, hTh⟩ :=
    ggNormalizer_orbit_mem hp (fun i : Λ => ggLin (p := p) ι (φ' (some i)))
      (fun i => h' (some i)) (fun i => α' (some i)) hs hα h0 hRC hTn hu₀ i₀
  obtain ⟨v, hv, huv⟩ := p3lg_orbit_mem_coroots (p := p) hD hp hu m
  have hact := p3lg_action_coords (p := p) hD ψ k ρ
  have hmain : ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹)
      (∑ i, ((ρ i : ℤ) : ZMod p) • h' i) =
      ∑ i, (r * ((v i : ℤ) : ZMod p)) • h' i := by
    rw [hρu₀, hTh, huv, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul]
  have hcoeff : (fun i => ((ρ i : ℤ) : ZMod p) -
        ((∑ i', ggSWordR X ψ (Pi.single k 1) i' * ∑ j, X i' j * ρ j : ℤ) : ZMod p) *
          ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p)) =
      fun i => r * ((v i : ℤ) : ZMod p) := by
    apply p3lg_coeff_unique (p := p) hD.indep
    rw [← hact, hmain]
  exact htest v hv (Units.mk0 r hr) (by
    funext i
    have h1 := congrFun hcoeff i
    rw [Units.val_mk0]
    exact h1)

theorem ggLineTest_three_of_invTest3 {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {X : Matrix (Option Λ) (Option Λ) ℤ} (hX : ∀ j : Λ, X (some j) (some j) = 2)
    (h : GGInvTest3 X) : GGLineTest X 3 := by
  have h3 : ∀ r : (ZMod 3)ˣ, (r : ZMod 3) = 1 ∨ (r : ZMod 3) = -1 := by decide
  obtain ⟨ψ, k, ρ, hρ, ha, htest⟩ := h
  refine ⟨ψ, k, ρ, hρ, ha, ?_⟩
  intro v hv r
  rcases h3 r with hr | hr
  · intro hcon
    exact htest v hv (by
      funext i
      have h1 := congrFun hcon i
      rw [h1, hr, one_mul])
  · intro hcon
    exact htest (-v) (p3lg_neg_mem_coroots hX hv) (by
      funext i
      have h1 := congrFun hcon i
      rw [h1, hr, Pi.neg_apply]
      push_cast
      ring)

theorem ggFork_false_of_invTest_three (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M fun i j => X (some i) (some j))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)))
    (hT : GGInvTest3 X) : False := by
  subst hp3
  exact ggFork_false_of_lineTest ha₀ (by norm_num) hcfg hD hM hC hAL
    (ggLineTest_three_of_invTest3 (fun j => hD.diag (some j)) hT)

end CFSG.StandardType
