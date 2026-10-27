module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNsFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNsComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmInv
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsFrame
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

namespace WitOmNs

open Module QuadraticMap TableBOrth CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions

section Diag

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {L : Type} [Field L]
  [Algebra K L] {s : ℕ} {κ : Type} {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V}

theorem diag_eq_of_res {p : ℕ} {ζ : L} (hζp : ζ ^ p = 1) {x x' : V →ₗ[K] V} {k k' : Fin s → ℕ}
    (hx : ∀ d w, x (Φ (d, w)) = Φ (fun l => ζ ^ k l * d l, w))
    (hx' : ∀ d w, x' (Φ (d, w)) = Φ (fun l => ζ ^ k' l * d l, w))
    (hres : ∀ l, k l % p = k' l % p) : x = x' := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [hx, hx']
  congr 2
  funext l
  rw [pow_eq_pow_mod (k l) hζp, pow_eq_pow_mod (k' l) hζp, hres l]

theorem dvd_of_fix_blk {p : ℕ} {ζ : L} (hζo : IsPrimitiveRoot ζ p) {x : V →ₗ[K] V}
    {k : Fin s → ℕ} (hx : ∀ d w, x (Φ (d, w)) = Φ (fun l => ζ ^ k l * d l, w)) {l : Fin s}
    (hfix : x (blk Φ l 1) = blk Φ l 1) : p ∣ k l := by
  rw [diag_blk hx, mul_one, blk, blk] at hfix
  have h1 := congrFun (congrArg Prod.fst (Φ.injective hfix)) l
  simp only [Pi.single_eq_same] at h1
  exact hζo.dvd_of_pow_eq_one _ h1

theorem card_le_pow_of_supp {p : ℕ} (hp : p.Prime) {ζ : L} (hζp : ζ ^ p = 1) {X : Type*}
    [Finite X] {F : X → V →ₗ[K] V} (hF : Function.Injective F) {kf : X → Fin s → ℕ}
    (hkf : ∀ x d w, F x (Φ (d, w)) = Φ (fun l => ζ ^ kf x l * d l, w)) (T : Finset (Fin s))
    (h₀ : ∀ x l, l ∉ T → p ∣ kf x l) : Nat.card X ≤ p ^ T.card := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hinj : Function.Injective (fun x : X => fun l : T => ((kf x l : ℕ) : ZMod p)) := by
    intro x x' h
    refine hF (diag_eq_of_res hζp (hkf x) (hkf x') fun l => ?_)
    by_cases hl : l ∈ T
    · exact (ZMod.natCast_eq_natCast_iff' _ _ p).mp (congrFun h ⟨l, hl⟩)
    · rw [Nat.mod_eq_zero_of_dvd (h₀ x l hl), Nat.mod_eq_zero_of_dvd (h₀ x' l hl)]
  calc Nat.card X ≤ Nat.card (T → ZMod p) := Nat.card_le_card_of_injective _ hinj
    _ = p ^ T.card := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe]

end Diag

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [CharP K 2] in
theorem exists_coords_root {g : Polynomial K} [Fact (Irreducible g)]
    (hdeg : (CoordSL.rootPB g).dim = 2) (a : AdjoinRoot g) :
    ∃ y w : K, a = y • 1 + w • AdjoinRoot.root g := by
  set b₀ := (CoordSL.rootPB g).basis.reindex (finCongr hdeg) with hb₀
  have hb : ∀ k : Fin 2, b₀ k = AdjoinRoot.root g ^ (k : ℕ) := fun k => by
    rw [hb₀, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    simp only [CoordSL.rootPB, AdjoinRoot.powerBasis_gen]
    rfl
  refine ⟨b₀.repr a 0, b₀.repr a 1, ?_⟩
  conv_lhs => rw [← b₀.sum_repr a]
  rw [Fin.sum_univ_two, hb, hb]
  simp

theorem exists_frame_of_comm (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K + 1) {A : Subgroup (V ≃ₗ[K] V)}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hAO : ∀ a ∈ A, a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ (g : Polynomial K) (_ : Fact (Irreducible g)) (s : ℕ) (κ : Type) (_ : Fintype κ)
      (Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] V) (β : LinearMap.BilinForm K (AdjoinRoot g))
      (kf : (V →ₗ[K] V) → Fin s → ℕ),
      IsPrimitiveRoot (AdjoinRoot.root g) p ∧ (CoordSL.rootPB g).dim = 2 ∧ β.IsAlt ∧
      (∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
        ∑ i, β (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w'))) ∧
      ∀ a ∈ A, ∀ d w, (a : V →ₗ[K] V) (Φ (d, w)) =
        Φ (fun l => AdjoinRoot.root g ^ kf (a : V →ₗ[K] V) l * d l, w) := by
  classical
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  have hpK' : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (Polynomial.cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      Polynomial.degree_eq_natDegree (Polynomial.cyclotomic_ne_zero p _),
      Polynomial.natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ :=
    WfDvdMonoid.exists_irreducible_factor hne (Polynomial.cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hζo : IsPrimitiveRoot (AdjoinRoot.root g) p := NSFrame.root_isPrimitiveRoot hp hpK' hgd
  have hdeg := SpNS.rootPB_dim_eq_two hp hp2 hpK' hgd hpK
  set S : Set (Module.End K V) := {x | ∃ a ∈ A, (a : V →ₗ[K] V) = x} with hS
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine LinearMap.ext fun v => ?_
    show a (b v) = b (a v)
    rw [← LinearEquiv.mul_apply, hAc a ha b hb, LinearEquiv.mul_apply]
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    refine LinearMap.ext fun v => ?_
    rw [Module.End.pow_apply, Module.End.one_apply, LinearEquiv.coe_coe,
      ← LinearEquiv.coe_pow, hAp a ha, LinearEquiv.coe_one, id_eq]
  have hSB : ∀ x ∈ S, ∀ u w, polarBilin Q (x u) (x w) = polarBilin Q u w := by
    rintro _ ⟨a, ha, rfl⟩ u w
    simp only [polarBilin_apply_apply, LinearEquiv.coe_coe]
    exact polar_map_of_mem (hAO a ha) u w
  obtain ⟨s, κ, hκ, Φ, β, hβalt, hact, hdecB⟩ := SpNS.exists_nframe hp hp2 hpK' hgd hdeg
    (SpNS.aeval_root_pow_pred hp hpK' hgd hpK) (B := polarBilin Q)
    (fun x => by rw [polarBilin_apply_apply]; exact polar_self_eq_zero Q x) hQ S hSc hSp hSB
  choose! kf hkf using hact
  exact ⟨g, inferInstance, s, κ, hκ, Φ, β, kf, hζo, hdeg, hβalt, hdecB,
    fun a ha => hkf _ ⟨a, ha, rfl⟩⟩

theorem exists_twoPlane_conj (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (h8 : 8 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (V ≃ₗ[K] V)}
    (hAO : ∀ a ∈ A, a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hAmax : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A)
    {g : Polynomial K} [Fact (Irreducible g)] {s : ℕ} {κ : Type}
    {Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K (AdjoinRoot g)}
    {kf : (V →ₗ[K] V) → Fin s → ℕ} (hζo : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hdeg : (CoordSL.rootPB g).dim = 2) (hβalt : β.IsAlt)
    (hdecB : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hkA : ∀ a ∈ A, ∀ d w, (a : V →ₗ[K] V) (Φ (d, w)) =
      Φ (fun l => AdjoinRoot.root g ^ kf (a : V →ₗ[K] V) l * d l, w))
    {i j : Fin s} (hij : i ≠ j) (hi : ∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) i)
    (hj : ∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) j) {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) (ht1 : t ≠ 1) :
    ∃ d ∈ A, d ≠ 1 ∧ d ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ d ^ p = 1 ∧
      finrank K (LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id)) + 4 = finrank K V ∧
      (∀ l, l ≠ i → l ≠ j → ∀ a, d (blk Φ l a) = blk Φ l a) ∧
      ∃ g' ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
        g' * d * g'⁻¹ * t = t * (g' * d * g'⁻¹) := by
  classical
  obtain ⟨ai, hai, hki⟩ := hi
  obtain ⟨aj, haj, hkj⟩ := hj
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  set ζ := AdjoinRoot.root g with hζdef
  have hζp : ζ ^ p = 1 := hζo.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζo.ne_one hp.one_lt
  have hζ0 : ζ ≠ 0 := hζo.ne_zero hp.ne_zero
  have hspan : ∀ a : AdjoinRoot g, ∃ y w : K, a = y • 1 + w • ζ := exists_coords_root hdeg
  have hL2 : finrank K (AdjoinRoot g) = 2 := by rw [(CoordSL.rootPB g).finrank, hdeg]
  have hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w')) := fun d d' w w' => by
    simpa only [polarBilin_apply_apply] using hdecB d d' w w'
  have hQi := quad_blk_mul_eq (Φ := Φ) hp hζp (x := (ai : V →ₗ[K] V))
    (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hAO ai hai) v) (hkA ai hai) hki
  have hQj := quad_blk_mul_eq (Φ := Φ) hp hζp (x := (aj : V →ₗ[K] V))
    (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hAO aj haj) v) (hkA aj haj) hkj
  have hβnd : ∀ u, (∀ v, β u v = 0) → u = 0 := WitSpNs.frame_block_nondegenerate hQ hdecB i
  set d := twoPlane Φ hζ0 i j with hd
  have hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (quad_twoPlane hζ0 hdec hij hQi hQj)
  have hdp : d ^ p = 1 := twoPlane_pow_eq_one hζ0 hζp
  have hd1 : d ≠ 1 := twoPlane_ne_one hζ0 hζ1
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hdΩ : d ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    hodd d hdO (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hdp))
  have hdA : d ∈ A := hAmax d hdΩ hdp fun a ha => LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact (twoPlane_commute hζ0 (hkA a ha) v).symm
  have hdfix : ∀ l, l ≠ i → l ≠ j → ∀ a, d (blk Φ l a) = blk Φ l a := fun l hli hlj a =>
    twoPlane_fix hζ0 (Pi.single_eq_of_ne (Ne.symm hli) _) (Pi.single_eq_of_ne (Ne.symm hlj) _) 0
  obtain ⟨e, f, y, w, hef, hd0', hd1', hd2', hd3', hdW, hfixef⟩ :=
    exists_hyp_twoPlane hζ0 hdec hij hζ1 hβalt hβnd hspan hQi hQj
  have hdim : finrank K (LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id)) + 4 = finrank K V := by
    set π : V →ₗ[K] AdjoinRoot g × AdjoinRoot g :=
      ((LinearMap.proj i).comp ((LinearMap.fst K _ _).comp Φ.symm.toLinearMap)).prod
        ((LinearMap.proj j).comp ((LinearMap.fst K _ _).comp Φ.symm.toLinearMap)) with hπ
    have hle : LinearMap.ker π ≤ LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id) := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hvi : (Φ.symm v).1 i = 0 := congrArg Prod.fst hv
      have hvj : (Φ.symm v).1 j = 0 := congrArg Prod.snd hv
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]
      have h1 := twoPlane_fix (Φ := Φ) hζ0 hvi hvj (Φ.symm v).2
      rwa [Prod.mk.eta, LinearEquiv.apply_symm_apply] at h1
    have hrk := LinearMap.finrank_range_add_finrank_ker π
    have hr : finrank K (LinearMap.range π) ≤ 4 := by
      have := Submodule.finrank_le (LinearMap.range π)
      rwa [Module.finrank_prod, hL2] at this
    have hmono := Submodule.finrank_mono hle
    set ι : AdjoinRoot g × AdjoinRoot g →ₗ[K] V :=
      { toFun := fun z => two Φ i j z.1 z.2
        map_add' := fun z z' => by
          simp only [Prod.fst_add, Prod.snd_add, two, blk_add]
          abel
        map_smul' := fun c z => by
          simp only [Prod.smul_fst, Prod.smul_snd, two, blk_smul, RingHom.id_apply,
            smul_add] } with hι
    have hιinj : Function.Injective ι := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨x, x'⟩ hz
      rw [LinearMap.mem_ker] at hz
      change two Φ i j x x' = 0 at hz
      have h0 : Φ.symm (two Φ i j x x') = 0 := by rw [hz, map_zero]
      simp only [two, blk, map_add, LinearEquiv.symm_apply_apply] at h0
      have hx := congrFun (congrArg Prod.fst h0) i
      have hx' := congrFun (congrArg Prod.fst h0) j
      simp [hij, hij.symm] at hx hx'
      exact Prod.ext hx hx'
    have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    have hrange : LinearMap.range ι ≤ LinearMap.range ((d : V →ₗ[K] V) - LinearMap.id) := by
      rintro _ ⟨⟨x, x'⟩, rfl⟩
      refine ⟨two Φ i j ((ζ - 1)⁻¹ * x) ((ζ - 1)⁻¹ * x'), ?_⟩
      have hsub : ∀ b : AdjoinRoot g, ζ * ((ζ - 1)⁻¹ * b) - (ζ - 1)⁻¹ * b = b := fun b => by
        rw [← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ hζ1', one_mul]
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, twoPlane_two hζ0 hij]
      change _ = two Φ i j x x'
      conv_rhs => rw [← hsub x, ← hsub x']
      rw [two, two, two, blk_sub, blk_sub]
      abel
    have hrk2 := LinearMap.finrank_range_add_finrank_ker ((d : V →ₗ[K] V) - LinearMap.id)
    have hι4 : finrank K (LinearMap.range ι) = 4 := by
      rw [LinearMap.finrank_range_of_inj hιinj, Module.finrank_prod, hL2]
    have hmono2 := Submodule.finrank_mono hrange
    omega
  have h1 : 1 ≤ finrank K (LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id)) := by omega
  obtain ⟨w₀, hw₀d, hw₀Q⟩ := exists_fix_quad_ne_zero hQ hdO hp hp2 hdp h1
  obtain ⟨e', f', hef', hte, htf⟩ := WitOm.exists_hypFamily_stable hQ htO htt ht1 h8
  obtain ⟨g', hg', hge⟩ := WitOm.exists_orthDerived_apply_eq hQ hT hef hef' hw₀Q
    (fun k => (hfixef w₀ hw₀d k).1) (fun k => (hfixef w₀ hw₀d k).2)
  have hgO : g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ hg'
  set M : V ≃ₗ[K] V := g'⁻¹ * t * g' with hM
  have hMO : M ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (mul_mem (inv_mem hgO) htO) hgO
  have hMM' : M * M = 1 := by
    calc M * M = g'⁻¹ * (t * t) * g' := by rw [hM]; group
      _ = 1 := by rw [htt]; group
  have hMM : ∀ v, M (M v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hMM']
    rfl
  have hginv : ∀ k, g'⁻¹ (e' k) = e k ∧ g'⁻¹ (f' k) = f k := fun k => by
    constructor
    · rw [← (hge k).1, ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    · rw [← (hge k).2, ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
  have hspanE : ∀ x ∈ Submodule.span K (Set.range e'),
      g'⁻¹ x ∈ Submodule.span K (Set.range e) := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    rw [map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smul, (hginv k).1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hspanF : ∀ x ∈ Submodule.span K (Set.range f'),
      g'⁻¹ x ∈ Submodule.span K (Set.range f) := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    rw [map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smul, (hginv k).2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hcomm := commute_of_hypStable hef (M := (M : V →ₗ[K] V)) (d := (d : V →ₗ[K] V))
    (fun u v => polar_map_of_mem hMO u v) hMM
    (fun k => by
      show g'⁻¹ (t (g' (e k))) ∈ _
      rw [(hge k).1]
      exact hspanE _ (hte k))
    (fun k => by
      show g'⁻¹ (t (g' (f k))) ∈ _
      rw [(hge k).2]
      exact hspanF _ (htf k))
    hd0' hd1' hd2' hd3' hdW
  have hMd : M * d = d * M := LinearEquiv.ext fun v => hcomm v
  have htM : t = g' * M * g'⁻¹ := by rw [hM]; group
  refine ⟨d, hdA, hd1, hdO, hdp, hdim, hdfix, g', hg', ?_⟩
  rw [htM]
  calc g' * d * g'⁻¹ * (g' * M * g'⁻¹) = g' * (d * M) * g'⁻¹ := by group
    _ = g' * (M * d) * g'⁻¹ := by rw [hMd]
    _ = g' * M * g'⁻¹ * (g' * d * g'⁻¹) := by group

theorem exists_witness_lin (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (h10 : 10 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K + 1) {A : Subgroup (V ≃ₗ[K] V)}
    (hAΩ : A ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hAmax : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A)
    (hAcard : p ^ 2 ≤ Nat.card A) {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) (ht1 : t ≠ 1) :
    ∃ d ∈ A, d ≠ 1 ∧ ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g * d * g⁻¹ * t = t * (g * d * g⁻¹) ∧
      ∃ Lp : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple Lp ∧
        Lp ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
        (∀ x ∈ Lp, x * d = d * x) ∧
        (∀ c ∈ TauCeti.QuadraticMap.orthogonalGroup Q, c * d = d * c → ∀ x ∈ Lp,
          c * x * c⁻¹ ∈ Lp) ∧
        Nat.card {z : A // ∀ x ∈ Lp, (z : V ≃ₗ[K] V) * x = x * z} ≤ p ^ 2 := by
  classical
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  have hAO : ∀ a ∈ A, a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun a ha =>
    Subgroup.commutator_le_self _ (hAΩ ha)
  obtain ⟨g, hfact, s, κ, hκ, Φ, β, kf, hζo, hdeg, hβalt, hdecB, hkA⟩ :=
    exists_frame_of_comm hQ hp hpK hAc hAp hAO
  set ζ := AdjoinRoot.root g with hζdef
  have hζp : ζ ^ p = 1 := hζo.pow_eq_one
  have hFA : Function.Injective (fun a : A => ((a : V ≃ₗ[K] V) : V →ₗ[K] V)) :=
    fun a a' h => Subtype.ext (LinearEquiv.toLinearMap_injective h)
  have hkA' : ∀ (a : A) d w, ((a : V ≃ₗ[K] V) : V →ₗ[K] V) (Φ (d, w)) =
      Φ (fun l => ζ ^ kf ((a : V ≃ₗ[K] V) : V →ₗ[K] V) l * d l, w) := fun a => hkA a a.2
  have := LayerCores.finite_linearEquiv (K := K) (V := V)
  obtain ⟨i, j, hij, hi, hj⟩ : ∃ i j : Fin s, i ≠ j ∧
      (∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) i) ∧ (∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) j) := by
    by_contra hno
    push Not at hno
    have hpp : p < p ^ 2 := by
      have := hp.two_le
      nlinarith
    by_cases hex : ∃ i₀, ∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) i₀
    · obtain ⟨i₀, hi₀⟩ := hex
      have h1 := card_le_pow_of_supp hp hζp hFA hkA' {i₀} (fun a l hl => by
        rw [Finset.mem_singleton] at hl
        exact hno i₀ l (Ne.symm hl) hi₀ a a.2)
      rw [Finset.card_singleton, pow_one] at h1
      omega
    · push Not at hex
      have h1 := card_le_pow_of_supp hp hζp hFA hkA' ∅ (fun a l _ => hex l a a.2)
      rw [Finset.card_empty, pow_zero] at h1
      have := hp.two_le
      nlinarith
  obtain ⟨d, hdA, hd1, hdO, hdp, hdim, hdfix, g', hg', hcommt⟩ :=
    exists_twoPlane_conj hQ hT (by omega) hp hp2 hAO hAmax hζo hdeg hβalt hdecB hkA hij hi hj
      htO htt ht1
  obtain ⟨Lp, hLq, hLΩ, hLd, hLn, hLz⟩ := exists_fixComponent hQ hdO hp hp2 hdp (by omega)
  have hcount : Nat.card {z : A // ∀ x ∈ Lp, (z : V ≃ₗ[K] V) * x = x * z} ≤ p ^ 2 := by
    have hsub : Function.Injective (fun z : {z : A // ∀ x ∈ Lp, (z : V ≃ₗ[K] V) * x = x * z} =>
        (((z : A) : V ≃ₗ[K] V) : V →ₗ[K] V)) :=
      fun z z' h => Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective h))
    have h1 := card_le_pow_of_supp hp hζp hsub (fun z => hkA' (z : A)) {i, j} (by
      rintro ⟨⟨z, hz⟩, hzL⟩ l hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact dvd_of_fix_blk hζo (hkA z hz) (hLz z (hAO z hz) (hAc z hz d hdA) hzL _
        (hdfix l hl.1 hl.2 1)))
    rwa [Finset.card_pair hij] at h1
  exact ⟨d, hdA, hd1, g', hg', hcommt, Lp, hLq, hLΩ, hLd, hLn, hcount⟩

end Main

end WitOmNs

end CFSG.StandardType
