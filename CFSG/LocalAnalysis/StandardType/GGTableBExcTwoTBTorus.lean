module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBSec
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.RankThree.CentralCover.SteinbergBNReflectionNormalizers

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open TableBExcTwo

namespace TableBExcTwoTB

section Two

variable {K : Type} [Field K]

theorem two_eq_zero_of_card_two (hK : Nat.card K = 2) : (2 : K) = 0 := by
  rcases eq_zero_or_eq_one_of_card_eq_two hK (2 : K) with h | h
  · exact h
  · exfalso
    have h1 : (1 : K) + 1 = 1 := by rw [one_add_one_eq_two, h]
    have h0 : (1 : K) = 0 := by linear_combination h1
    exact one_ne_zero h0

theorem mat_eq_of_pow_three (hK : Nat.card K = 2) (M : Matrix (Fin 2) (Fin 2) K)
    (hdet : M.det = 1) (h3 : M * M * M = 1) (h1 : M ≠ 1) :
    M = !![0, 1; 1, 1] ∨ M = !![1, 1; 1, 0] := by
  have h2 := two_eq_zero_of_card_two hK
  have key := eq_zero_or_eq_one_of_card_eq_two hK
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.eta_fin_two M] at h3 h1 ⊢
  rcases key (M 0 0) with a | a <;> rcases key (M 0 1) with b | b <;>
    rcases key (M 1 0) with c | c <;> rcases key (M 1 1) with d | d <;>
    simp only [a, b, c, d] at hdet h3 h1 ⊢ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2,
      TableBF4Two.neg_one_eq_one_of_two h2, Matrix.one_fin_two] at hdet h3 h1 ⊢

theorem sl2_eq_of_pow_three (hK : Nat.card K = 2) (A : SL2 K) (h3 : A ^ 3 = 1) (h1 : A ≠ 1) :
    A = uSL 1 * vSL 1 ∨ A = (uSL 1 * vSL 1)⁻¹ := by
  have h2 := two_eq_zero_of_card_two hK
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have h3M : (A : Matrix (Fin 2) (Fin 2) K) * A * A = 1 := by
    have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K)) h3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
    rw [pow_three, ← mul_assoc] at this
    exact this
  have h1M : (A : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
    h1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one]))
  have hS3 : (uSL 1 * vSL 1 : SL2 K) ^ 3 = 1 := TableBF4Two.S0_pow_three h2
  rcases mat_eq_of_pow_three hK _ hdet h3M h1M with h | h
  · left
    apply Subtype.ext
    rw [h, TableBF4Two.coe_S0 h2]
  · right
    have hinv : (uSL 1 * vSL 1 : SL2 K)⁻¹ = (uSL 1 * vSL 1) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', show (2 : ℕ) + 1 = 3 from rfl, hS3]
    rw [hinv]
    apply Subtype.ext
    rw [h, TableBF4Two.coe_S0_sq h2]

end Two

theorem zmod3_mul_self_of_ne_zero : ∀ k : ZMod 3, k ≠ 0 → k * k = 1 := by decide

theorem zmod3_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

theorem zmod3_two_mul_eq_zero : ∀ z : ZMod 3, 2 * z = 0 → z = 0 := by decide

theorem zmod3_val_one : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = 1 := rfl

theorem zmod3_val_two : (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 3))).val = 2 := rfl

section Torus

variable {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def tGen (F : OrthFrame τ d) (i : Fin (d + 1)) : adjointGroup τ K :=
  rho K F i (uSL 1 * vSL 1)

theorem tGen_pow_three (F : OrthFrame τ d) (i : Fin (d + 1)) : tGen K F i ^ 3 = 1 := by
  rw [tGen, ← map_pow, TableBF4Two.S0_pow_three CharTwo.two_eq_zero, map_one]

theorem tGen_ne_one (F : OrthFrame τ d) (i : Fin (d + 1)) : tGen K F i ≠ 1 := fun h =>
  TableBF4Two.S0_ne_one (K := K) CharTwo.two_eq_zero
    (rho_injective F i (h.trans (map_one _).symm))

variable (K) in
@[expose] noncomputable def tC (F : OrthFrame τ d) (i : Fin (d + 1)) :
    Multiplicative (ZMod 3) →* adjointGroup τ K :=
  TableBSymp.zmodPowHom (tGen_pow_three (K := K) F i)

theorem tC_apply (F : OrthFrame τ d) (i : Fin (d + 1)) (a : Multiplicative (ZMod 3)) :
    tC K F i a = tGen K F i ^ (Multiplicative.toAdd a).val := by
  rw [tC, TableBSymp.zmodPowHom_apply]

theorem tC_apply_rho (F : OrthFrame τ d) (i : Fin (d + 1)) (a : Multiplicative (ZMod 3)) :
    tC K F i a = rho K F i ((uSL 1 * vSL 1) ^ (Multiplicative.toAdd a).val) := by
  rw [tC_apply, tGen, map_pow]

theorem tC_one (F : OrthFrame τ d) (i : Fin (d + 1)) :
    tC K F i (Multiplicative.ofAdd 1) = tGen K F i := by
  rw [tC_apply, zmod3_val_one, pow_one]

theorem tC_injective (F : OrthFrame τ d) (i : Fin (d + 1)) : Function.Injective (tC K F i) := by
  have := Fact.mk Nat.prime_three
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [tC_apply] at ha
  have hd := orderOf_dvd_of_pow_eq_one ha
  rw [orderOf_eq_prime (tGen_pow_three (K := K) F i) (tGen_ne_one (K := K) F i)] at hd
  have hlt := ZMod.val_lt (Multiplicative.toAdd a)
  have h0 : (Multiplicative.toAdd a).val = 0 := by omega
  rw [ZMod.val_eq_zero] at h0
  rw [← ofAdd_toAdd a, h0, ofAdd_zero]

theorem tC_commute (F : OrthFrame τ d) :
    Pairwise fun i j : Fin (d + 1) => ∀ a b, Commute (tC K F i a) (tC K F j b) := by
  intro i j hij a b
  rw [tC_apply_rho, tC_apply_rho]
  exact commute_rho F hij _ _

variable (K) in
@[expose] noncomputable def tD (F : OrthFrame τ d) :
    (Fin (d + 1) → Multiplicative (ZMod 3)) →* adjointGroup τ K :=
  MonoidHom.noncommPiCoprod (tC K F) (tC_commute F)

theorem tC_iSupIndep (F : OrthFrame τ d) : iSupIndep fun i => (tC K F i).range := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  obtain ⟨a, rfl⟩ := hx
  have hle : (⨆ (j) (_ : j ≠ i), (tC K F j).range) ≤
      Subgroup.centralizer {rho K F i (uSL 1)} := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, tC_apply_rho]
    exact (commute_rho F hj _ _).eq
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hx')
  rw [tC_apply_rho, ← map_mul, ← map_mul] at hc
  have hc' := rho_injective F _ hc
  by_contra hne
  have hval : (Multiplicative.toAdd a).val ≠ 0 := by
    intro h0
    apply hne
    rw [tC_apply_rho, h0, pow_zero, map_one]
  exact TableBF4Two.S0_pow_mul_uSL_ne CharTwo.two_eq_zero (ZMod.val_lt _) hval hc'

theorem tD_injective (F : OrthFrame τ d) : Function.Injective (tD K F) :=
  MonoidHom.injective_noncommPiCoprod_of_iSupIndep (tC K F) (tC_iSupIndep F) (tC_injective F)

variable (K) in
@[expose] noncomputable def tE (F : OrthFrame τ d) :
    Multiplicative (Fin (d + 1) → ZMod 3) →* adjointGroup τ K :=
  (tD K F).comp (MulEquiv.piMultiplicative fun _ : Fin (d + 1) => ZMod 3).toMonoidHom

theorem tE_apply (F : OrthFrame τ d) (v : Fin (d + 1) → ZMod 3) :
    tE K F (Multiplicative.ofAdd v) = tD K F fun j => Multiplicative.ofAdd (v j) :=
  rfl

theorem tE_injective (F : OrthFrame τ d) : Function.Injective (tE K F) := fun _ _ h =>
  (MulEquiv.piMultiplicative fun _ : Fin (d + 1) => ZMod 3).injective (tD_injective (K := K) F h)

theorem tE_range (F : OrthFrame τ d) : (tE K F).range = (tD K F).range := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨f, rfl⟩
    refine ⟨(MulEquiv.piMultiplicative fun _ : Fin (d + 1) => ZMod 3).symm f, ?_⟩
    rw [tE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem tE_single (F : OrthFrame τ d) (i : Fin (d + 1)) (c : ZMod 3) :
    tE K F (Multiplicative.ofAdd (Pi.single i c)) = tC K F i (Multiplicative.ofAdd c) := by
  rw [tE_apply, tD]
  have h : (fun j => Multiplicative.ofAdd ((Pi.single i c : Fin (d + 1) → ZMod 3) j)) =
      Pi.mulSingle i (Multiplicative.ofAdd c) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [h, MonoidHom.noncommPiCoprod_mulSingle]

variable (K) in
@[expose] noncomputable def nGen (F : OrthFrame τ d) (i : Fin (d + 1)) : adjointGroup τ K :=
  rho K F i WSL

theorem nGen_conj_tC (F : OrthFrame τ d) (i j : Fin (d + 1)) (a : Multiplicative (ZMod 3)) :
    nGen K F i * tC K F j a * (nGen K F i)⁻¹ = tC K F j (if j = i then a⁻¹ else a) := by
  split_ifs with hji
  · subst hji
    rw [show tC K F j a⁻¹ = (tC K F j a)⁻¹ from map_inv _ a, tC_apply_rho, nGen, ← map_inv,
      ← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [← conj_pow, TableBF4Two.W_S0_W CharTwo.two_eq_zero, inv_pow]
  · rw [tC_apply_rho, nGen, (commute_rho F (Ne.symm hji) WSL _).eq, mul_inv_cancel_right]

theorem nGen_conj_tD (F : OrthFrame τ d) (i : Fin (d + 1))
    (f : Fin (d + 1) → Multiplicative (ZMod 3)) :
    nGen K F i * tD K F f * (nGen K F i)⁻¹ = tD K F (reflHom i f) := by
  have h : (MulAut.conj (nGen K F i)).toMonoidHom.comp (tD K F) =
      (tD K F).comp (reflHom i) := MonoidHom.pi_ext fun j a => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, tD,
      MonoidHom.noncommPiCoprod_mulSingle, reflHom_mulSingle]
    exact nGen_conj_tC F i j a
  have h1 := congrArg (fun φ => φ f) h
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1

theorem nGen_conj_tE (F : OrthFrame τ d) (i : Fin (d + 1)) (v : Fin (d + 1) → ZMod 3) :
    nGen K F i * tE K F (Multiplicative.ofAdd v) * (nGen K F i)⁻¹ =
      tE K F (Multiplicative.ofAdd (v - reflCoeff i v • Pi.single i 1)) := by
  rw [tE_apply, tE_apply, nGen_conj_tD, reflHom_ofAdd]

theorem smul_single_one (i : Fin (d + 1)) (c : ZMod 3) :
    c • (Pi.single i 1 : Fin (d + 1) → ZMod 3) = Pi.single i c := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

theorem piTorus_tE (F : OrthFrame τ d) : TableBF4.piTorus (tE K F) = tD K F := by
  refine MonoidHom.ext fun f => ?_
  rw [TableBF4.piTorus_apply, tE_apply]
  congr 1

theorem tD_section (F : OrthFrame τ d) {L' : Type} [Group L'] {ψ : L' →* adjointGroup τ K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') :
    ∃ σ : (Fin (d + 1) → Multiplicative (ZMod 3)) →* L', ψ.comp σ = tD K F := by
  have hcomm : ∀ x ∈ (TableBF4.piTorus (tE K F)).range.comap ψ,
      ∀ y ∈ (TableBF4.piTorus (tE K F)).range.comap ψ, x * y = y * x := by
    rw [TableBF4.range_piTorus]
    exact CFSG.RankThree.CentralCover.reflection_comap_comm hψ hker Nat.prime_three
      (by norm_num) (tE K F) reflCoeff reflCoeff_single (nGen K F) (nGen_conj_tE F)
  have hinv : ∀ i : Fin (d + 1), ∃ w : adjointGroup τ K,
      w * TableBSymp.torusBasis (TableBF4.piTorus (tE K F)) i * w⁻¹ =
        (TableBSymp.torusBasis (TableBF4.piTorus (tE K F)) i)⁻¹ := by
    intro i
    refine ⟨nGen K F i, ?_⟩
    rw [TableBF4.torusBasis_piTorus, nGen_conj_tE, reflCoeff_single, ← map_inv, ← ofAdd_neg]
    congr 2
    rw [two_smul]
    abel
  obtain ⟨σ, hσ⟩ := TableBF4.exists_torus_section_of_comm hψ hker (by decide : Odd 3)
    (TableBF4.piTorus (tE K F)) hcomm hinv
  exact ⟨σ, by rw [hσ, piTorus_tE]⟩

end Torus

section Weyl

noncomputable def nW (τ : Tag) (K : Type) [Field K] (w : List (Fin τ.rank)) : ModGL τ K :=
  (w.map fun i => weylElt τ K i 1).prod

theorem nW_cons (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (w : List (Fin τ.rank)) :
    nW τ K (i :: w) = (weylElt τ K i 1 : ModGL τ K) * nW τ K w := by
  simp [nW, List.map_cons, List.prod_cons]

theorem nW_mem (τ : Tag) (K : Type) [Field K] (w : List (Fin τ.rank)) :
    nW τ K w ∈ adjointGroup τ K := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih => rw [nW_cons]; exact mul_mem (weylElt_mem_adjointGroup i 1) ih

noncomputable def nWA (τ : Tag) (K : Type) [Field K] (w : List (Fin τ.rank)) :
    adjointGroup τ K :=
  ⟨nW τ K w, nW_mem τ K w⟩

@[expose] def wAct (τ : Tag) (w : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  w.foldr (fun i u => reflect τ i u) v

theorem wAct_cons (τ : Tag) (i : Fin τ.rank) (w : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    wAct τ (i :: w) v = reflect τ i (wAct τ w v) := rfl

theorem reflect_neg (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i (-v) = -reflect τ i v := by
  simp only [reflect, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_smul]
  abel

theorem wAct_neg (τ : Tag) (w : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    wAct τ w (-v) = -wAct τ w v := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wAct_cons, wAct_cons, ih, reflect_neg]

theorem isRoot_wAct {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (w : List (Fin τ.rank)) :
    IsRoot τ (wAct τ w α) := by
  induction w with
  | nil => exact hα
  | cons i w ih => exact IsRoot.reflect i ih

theorem map_conj_nW_rootSubgroup (τ : Tag) (K : Type) [Field K] (w : List (Fin τ.rank))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ K α).map (MulAut.conj (nW τ K w)).toMonoidHom =
      rootSubgroup τ K (wAct τ w α) := by
  induction w with
  | nil =>
    have h1 : (MulAut.conj (nW τ K [])).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun x => by simp [nW]
    rw [h1, Subgroup.map_id]
    rfl
  | cons i w ih =>
    rw [nW_cons, map_conj_mul, ih, wAct_cons,
      map_conj_weylElt_rootSubgroup K i (isRoot_wAct hα w)]

theorem rootSL2_range_neg (τ : Tag) (K : Type) [Field K] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : (rootSL2 τ K (-α)).range = (rootSL2 τ K α).range := by
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (CFSG.LieType.Chevalley.IsRoot.neg hα),
    CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hα, neg_neg, sup_comm]

theorem map_conj_nW_rootSL2_range (τ : Tag) (K : Type) [Field K] (w : List (Fin τ.rank))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSL2 τ K α).range.map (MulAut.conj (nW τ K w)).toMonoidHom =
      (rootSL2 τ K (wAct τ w α)).range := by
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hα,
    CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (isRoot_wAct hα w), Subgroup.map_sup,
    map_conj_nW_rootSubgroup τ K w hα,
    map_conj_nW_rootSubgroup τ K w (CFSG.LieType.Chevalley.IsRoot.neg hα), wAct_neg]

theorem rootSL2_eq_of_order_three (τ : Tag) (K : Type) [Field K] (hK : Nat.card K = 2)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {x : ModGL τ K}
    (hx : x ∈ (rootSL2 τ K α).range) (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    x = rootSL2 τ K α (uSL 1 * vSL 1) ∨ x = rootSL2 τ K α (uSL 1 * vSL 1)⁻¹ := by
  obtain ⟨A, rfl⟩ := hx
  have hA3 : A ^ 3 = 1 := by
    apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field α
    rw [map_pow, h3, map_one]
  have hA1 : A ≠ 1 := fun h => h1 (by rw [h, map_one])
  rcases sl2_eq_of_pow_three hK A hA3 hA1 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end Weyl

section Frame

variable {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]

@[expose] def PermutesFrame (F : OrthFrame τ d) (w : List (Fin τ.rank))
    (π : Fin (d + 1) → Fin (d + 1)) : Prop :=
  ∀ a, wAct τ w (F.root a) = F.root (π a) ∨ wAct τ w (F.root a) = -F.root (π a)

theorem S0_inv_eq_sq (h2 : (2 : K) = 0) : (uSL 1 * vSL 1 : SL2 K)⁻¹ = (uSL 1 * vSL 1) ^ 2 := by
  have hS3 : (uSL 1 * vSL 1 : SL2 K) ^ 3 = 1 := TableBF4Two.S0_pow_three h2
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', show (2 : ℕ) + 1 = 3 from rfl, hS3]

theorem conj_nWA_tGen (hK : Nat.card K = 2) (F : OrthFrame τ d) {w : List (Fin τ.rank)}
    {π : Fin (d + 1) → Fin (d + 1)} (hπ : PermutesFrame F w π) (a : Fin (d + 1)) :
    ∃ k : ZMod 3, k ≠ 0 ∧
      nWA τ K w * tGen K F a * (nWA τ K w)⁻¹ = tC K F (π a) (Multiplicative.ofAdd k) := by
  set g := nWA τ K w with hg
  set x : adjointGroup τ K := g * tGen K F a * g⁻¹ with hx
  have hcoe : (x : ModGL τ K) = nW τ K w * (tGen K F a : ModGL τ K) * (nW τ K w)⁻¹ := by
    rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hmem1 : (tGen K F a : ModGL τ K) ∈ (rootSL2 τ K (F.root a)).range :=
    ⟨uSL 1 * vSL 1, rfl⟩
  have hmem2 : nW τ K w * (tGen K F a : ModGL τ K) * (nW τ K w)⁻¹ ∈
      (rootSL2 τ K (wAct τ w (F.root a))).range := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj (nW τ K w)).toMonoidHom hmem1
    rw [map_conj_nW_rootSL2_range τ K w (F.isRoot a)] at h
    exact h
  have hkey : (rootSL2 τ K (wAct τ w (F.root a))).range =
      (rootSL2 τ K (F.root (π a))).range := by
    rcases hπ a with h | h
    · rw [h]
    · rw [h]
      exact rootSL2_range_neg τ K (F.isRoot (π a))
  have hmem : (x : ModGL τ K) ∈ (rootSL2 τ K (F.root (π a))).range := by
    rw [hcoe, ← hkey]
    exact hmem2
  have hx3 : x ^ 3 = 1 := by
    rw [hx, conj_pow, tGen_pow_three, mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := by
    intro h
    apply tGen_ne_one (K := K) F a
    rw [hx] at h
    calc tGen K F a = g⁻¹ * (g * tGen K F a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have h3 : (x : ModGL τ K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  have hx1' : (x : ModGL τ K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rcases rootSL2_eq_of_order_three τ K hK (F.isRoot (π a)) hmem h3 hx1' with h | h
  · refine ⟨1, one_ne_zero, ?_⟩
    apply Subtype.ext
    rw [h, tC_one]
    rfl
  · refine ⟨2, by decide, ?_⟩
    apply Subtype.ext
    rw [h, S0_inv_eq_sq (two_eq_zero_of_card_two hK), map_pow, tC_apply, zmod3_val_two,
      Subgroup.coe_pow]
    rfl

theorem conj_nWA_tC (hK : Nat.card K = 2) (F : OrthFrame τ d) {w : List (Fin τ.rank)}
    {π : Fin (d + 1) → Fin (d + 1)} (hπ : PermutesFrame F w π) (a : Fin (d + 1)) :
    ∃ k : ZMod 3, k ≠ 0 ∧ ∀ x : Multiplicative (ZMod 3),
      nWA τ K w * tC K F a x * (nWA τ K w)⁻¹ =
        tC K F (π a) (Multiplicative.ofAdd (Multiplicative.toAdd x * k)) := by
  obtain ⟨k, hk0, hk⟩ := conj_nWA_tGen hK F hπ a
  refine ⟨k, hk0, fun x => ?_⟩
  rw [tC_apply, ← conj_pow, hk, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

variable (K) in
def frameWeyl (F : OrthFrame τ d) (w₁ w₂ : List (Fin τ.rank)) : Set (adjointGroup τ K) :=
  {x | (∃ i, x = nGen K F i) ∨ x = nWA τ K w₁ ∨ x = nWA τ K w₂}

theorem tC_mem_tE (F : OrthFrame τ d) (a : Fin (d + 1)) (x : Multiplicative (ZMod 3)) :
    tC K F a x ∈ (tE K F).range :=
  ⟨Multiplicative.ofAdd (Pi.single a (Multiplicative.toAdd x)), by
    rw [tE_single, ofAdd_toAdd]⟩

theorem map_conj_tE_le (F : OrthFrame τ d) (g : adjointGroup τ K) (π : Fin (d + 1) → Fin (d + 1))
    (h : ∀ (a : Fin (d + 1)) (x : Multiplicative (ZMod 3)), ∃ y, g * tC K F a x * g⁻¹ =
      tC K F (π a) y) :
    (tE K F).range.map (MulAut.conj g).toMonoidHom ≤ (tE K F).range := by
  rw [tE_range, tD, MonoidHom.noncommPiCoprod_range, Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rintro _ ⟨z, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := h a x
  show g * tC K F a x * g⁻¹ ∈ _
  rw [hy]
  exact (le_iSup (fun i => (tC K F i).range) (π a)) ⟨y, rfl⟩

theorem tGen_mem_of_tC_mem (F : OrthFrame τ d) {a : Fin (d + 1)}
    {E' : Subgroup (adjointGroup τ K)} {k : ZMod 3} (hk : k ≠ 0)
    (h : tC K F a (Multiplicative.ofAdd k) ∈ E') : tGen K F a ∈ E' := by
  have h1 : tC K F a (Multiplicative.ofAdd k) ^ k.val = tGen K F a := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val,
      zmod3_mul_self_of_ne_zero k hk]
    exact tC_one F a
  rw [← h1]
  exact E'.pow_mem h _

theorem irreducible_frame (hK : Nat.card K = 2) (F : OrthFrame τ d) {w₁ w₂ : List (Fin τ.rank)}
    {π₁ π₂ : Fin (d + 1) → Fin (d + 1)} (h₁ : PermutesFrame F w₁ π₁)
    (h₂ : PermutesFrame F w₂ π₂)
    (htrans : ∀ S : Finset (Fin (d + 1)), S.Nonempty → (∀ a ∈ S, π₁ a ∈ S) →
      (∀ a ∈ S, π₂ a ∈ S) → S = Finset.univ)
    (E' : Subgroup (adjointGroup τ K)) (hle : E' ≤ (tE K F).range)
    (hinv : ∀ x ∈ frameWeyl K F w₁ w₂, ∀ e ∈ E', x * e * x⁻¹ ∈ E') :
    E' = ⊥ ∨ E' = (tE K F).range := by
  classical
  by_cases hbot : E' = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E', x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  obtain ⟨v, rfl⟩ : ∃ v : Fin (d + 1) → ZMod 3, tE K F (Multiplicative.ofAdd v) = x := by
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hle hxE)
    exact ⟨Multiplicative.toAdd g, by rw [ofAdd_toAdd, hg]⟩
  have hi : ∃ i, v i ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hx1
    have hv0 : v = 0 := funext hne
    rw [hv0, ofAdd_zero, map_one]
  obtain ⟨i, hi⟩ := hi
  have hc := hinv (nGen K F i) (Or.inl ⟨i, rfl⟩) _ hxE
  rw [nGen_conj_tE] at hc
  have hy : tE K F (Multiplicative.ofAdd v) *
      (tE K F (Multiplicative.ofAdd (v - reflCoeff i v • Pi.single i 1)))⁻¹ =
      tC K F i (Multiplicative.ofAdd (reflCoeff i v)) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, ← tE_single]
    congr 2
    rw [smul_single_one]
    abel
  have hc' : tC K F i (Multiplicative.ofAdd (reflCoeff i v)) ∈ E' := by
    rw [← hy]
    exact E'.mul_mem hxE (E'.inv_mem hc)
  have hcne : reflCoeff i v ≠ 0 := by
    rw [reflCoeff_apply]
    exact mul_ne_zero zmod3_two_ne_zero hi
  have hS1 : tGen K F i ∈ E' := tGen_mem_of_tC_mem F hcne hc'
  have hcl₁ : ∀ a, tGen K F a ∈ E' → tGen K F (π₁ a) ∈ E' := by
    intro a ha
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tGen hK F h₁ a
    have hm := hinv (nWA τ K w₁) (Or.inr (Or.inl rfl)) _ ha
    rw [hk] at hm
    exact tGen_mem_of_tC_mem F hk0 hm
  have hcl₂ : ∀ a, tGen K F a ∈ E' → tGen K F (π₂ a) ∈ E' := by
    intro a ha
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tGen hK F h₂ a
    have hm := hinv (nWA τ K w₂) (Or.inr (Or.inr rfl)) _ ha
    rw [hk] at hm
    exact tGen_mem_of_tC_mem F hk0 hm
  have hS : Finset.univ.filter (fun a => tGen K F a ∈ E') = Finset.univ := by
    apply htrans
    · exact ⟨i, by simp [hS1]⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact hcl₁ a ha
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact hcl₂ a ha
  have hall : ∀ a, tGen K F a ∈ E' := by
    intro a
    have : a ∈ Finset.univ.filter (fun a => tGen K F a ∈ E') := by
      rw [hS]
      exact Finset.mem_univ a
    exact (Finset.mem_filter.mp this).2
  refine le_antisymm hle ?_
  rw [tE_range, tD, MonoidHom.noncommPiCoprod_range]
  refine iSup_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  rw [tC_apply]
  exact E'.pow_mem (hall a) _

theorem schur_frame (hK : Nat.card K = 2) (F : OrthFrame τ d) {w₁ w₂ : List (Fin τ.rank)}
    {π₁ π₂ : Fin (d + 1) → Fin (d + 1)} (h₁ : PermutesFrame F w₁ π₁)
    (h₂ : PermutesFrame F w₂ π₂)
    (htrans : ∀ S : Finset (Fin (d + 1)), S.Nonempty → (∀ a ∈ S, π₁ a ∈ S) →
      (∀ a ∈ S, π₂ a ∈ S) → S = Finset.univ)
    (G : adjointGroup τ K → adjointGroup τ K)
    (hGE : ∀ e ∈ (tE K F).range, G e ∈ (tE K F).range)
    (hGmul : ∀ e ∈ (tE K F).range, ∀ e' ∈ (tE K F).range, G (e * e') = G e * G e')
    (hGW : ∀ x ∈ frameWeyl K F w₁ w₂, ∀ e ∈ (tE K F).range, G (x * e * x⁻¹) = x * G e * x⁻¹) :
    ∃ c : ℕ, ∀ e ∈ (tE K F).range, G e = e ^ c := by
  have hsurj : ∀ v : Fin (d + 1) → ZMod 3, ∃ u : Fin (d + 1) → ZMod 3,
      tE K F (Multiplicative.ofAdd u) = G (tE K F (Multiplicative.ofAdd v)) := by
    intro v
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hGE _ ⟨Multiplicative.ofAdd v, rfl⟩)
    exact ⟨Multiplicative.toAdd g, by rw [ofAdd_toAdd, hg]⟩
  choose fE hfE using hsurj
  have hadd : ∀ v w, fE (v + w) = fE v + fE w := by
    intro v w
    apply Multiplicative.ofAdd.injective
    apply tE_injective (K := K) F
    rw [hfE, ofAdd_add v w, map_mul,
      hGmul (tE K F (Multiplicative.ofAdd v)) ⟨_, rfl⟩ (tE K F (Multiplicative.ofAdd w)) ⟨_, rfl⟩,
      ← hfE v, ← hfE w, ofAdd_add (fE v) (fE w), map_mul]
  let fA : (Fin (d + 1) → ZMod 3) →+ (Fin (d + 1) → ZMod 3) := AddMonoidHom.mk' fE hadd
  set c : Fin (d + 1) → ZMod 3 := fun a => fE (Pi.single a 1) a with hc_def
  have hoff : ∀ a j, j ≠ a → fE (Pi.single a 1) j = 0 := by
    intro a j hja
    have hc0 : reflCoeff j (Pi.single a 1) = 0 := by
      rw [reflCoeff_apply, Pi.single_eq_of_ne hja, mul_zero]
    have hfix : nGen K F j * tE K F (Multiplicative.ofAdd (Pi.single a 1)) * (nGen K F j)⁻¹ =
        tE K F (Multiplicative.ofAdd (Pi.single a 1)) := by
      rw [nGen_conj_tE, hc0]
      simp
    have hG := hGW (nGen K F j) (Or.inl ⟨j, rfl⟩) (tE K F (Multiplicative.ofAdd (Pi.single a 1)))
      ⟨_, rfl⟩
    rw [hfix, ← hfE (Pi.single a 1), nGen_conj_tE] at hG
    have hinj := Multiplicative.ofAdd.injective (tE_injective F hG)
    have hj := congrFun hinj j
    simp only [Pi.sub_apply, Pi.smul_apply, reflCoeff_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at hj
    apply zmod3_two_mul_eq_zero
    linear_combination hj
  have hdiag : ∀ a, fE (Pi.single a 1) = Pi.single a (c a) := by
    intro a
    funext j
    by_cases hj : j = a
    · subst hj
      simp [hc_def]
    · rw [hoff a j hj, Pi.single_eq_of_ne hj]
  have hsc : ∀ a (y : ZMod 3), fE (Pi.single a y) = Pi.single a (c a * y) := by
    intro a y
    have hsmul : y • (Pi.single a 1 : Fin (d + 1) → ZMod 3) = y.val • Pi.single a 1 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    have hy2 : fE (Pi.single a y) = y.val • fE (Pi.single a 1) := by
      rw [← smul_single_one a y, hsmul]
      exact map_nsmul fA _ _
    rw [hy2, hdiag a]
    funext j
    by_cases hj : j = a
    · subst hj
      simp [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
    · simp [Pi.single_eq_of_ne hj]
  have hfull : ∀ v : Fin (d + 1) → ZMod 3, fE v = fun j => c j * v j := by
    intro v
    have hsum : fE v = ∑ j, fE (Pi.single j (v j)) := by
      have hv : v = ∑ j, Pi.single j (v j) := (Finset.univ_sum_single v).symm
      calc fE v = fA v := rfl
        _ = fA (∑ j, Pi.single j (v j)) := by rw [← hv]
        _ = ∑ j, fA (Pi.single j (v j)) := map_sum fA _ _
        _ = ∑ j, fE (Pi.single j (v j)) := rfl
    funext k
    rw [hsum, Finset.sum_apply]
    simp only [hsc]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      simp [Pi.single_eq_of_ne (Ne.symm hjk)]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hG_tC : ∀ (b : Fin (d + 1)) (y : ZMod 3),
      G (tC K F b (Multiplicative.ofAdd y)) = tC K F b (Multiplicative.ofAdd (c b * y)) := by
    intro b y
    rw [← tE_single, ← hfE, hsc, tE_single]
  have hperm₁ : ∀ a, c (π₁ a) = c a := by
    intro a
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tC hK F h₁ a
    have hm := hGW (nWA τ K w₁) (Or.inr (Or.inl rfl)) (tC K F a (Multiplicative.ofAdd 1))
      (tC_mem_tE F a _)
    rw [hk (Multiplicative.ofAdd 1), hG_tC, hG_tC, hk (Multiplicative.ofAdd (c a * 1))] at hm
    have h := Multiplicative.ofAdd.injective (tC_injective F (π₁ a) hm)
    simp only [toAdd_ofAdd, mul_one, one_mul] at h
    exact mul_right_cancel₀ hk0 h
  have hperm₂ : ∀ a, c (π₂ a) = c a := by
    intro a
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tC hK F h₂ a
    have hm := hGW (nWA τ K w₂) (Or.inr (Or.inr rfl)) (tC K F a (Multiplicative.ofAdd 1))
      (tC_mem_tE F a _)
    rw [hk (Multiplicative.ofAdd 1), hG_tC, hG_tC, hk (Multiplicative.ofAdd (c a * 1))] at hm
    have h := Multiplicative.ofAdd.injective (tC_injective F (π₂ a) hm)
    simp only [toAdd_ofAdd, mul_one, one_mul] at h
    exact mul_right_cancel₀ hk0 h
  have hconst : ∀ a, c a = c 0 := by
    intro a
    have hS : Finset.univ.filter (fun b => c b = c 0) = Finset.univ := by
      apply htrans
      · exact ⟨0, by simp⟩
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        rw [hperm₁ b, hb]
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        rw [hperm₂ b, hb]
    have : a ∈ Finset.univ.filter (fun b => c b = c 0) := by
      rw [hS]
      exact Finset.mem_univ a
    exact (Finset.mem_filter.mp this).2
  refine ⟨(c 0).val, ?_⟩
  have hv : ∀ v : Fin (d + 1) → ZMod 3,
      G (tE K F (Multiplicative.ofAdd v)) = tE K F (Multiplicative.ofAdd v) ^ (c 0).val := by
    intro v
    have e1 : (fun j => c j * v j) = (c 0).val • v := by
      funext j
      rw [hconst j, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [← hfE v, hfull v, e1, ← map_pow, ← ofAdd_nsmul]
  rintro _ ⟨g, rfl⟩
  have := hv (Multiplicative.toAdd g)
  rw [ofAdd_toAdd] at this
  exact this

theorem secEltAt_frame (hK : Nat.card K = 2) (F : OrthFrame τ d) {w₁ w₂ : List (Fin τ.rank)}
    {π₁ π₂ : Fin (d + 1) → Fin (d + 1)} (h₁ : PermutesFrame F w₁ π₁)
    (h₂ : PermutesFrame F w₂ π₂)
    (htrans : ∀ S : Finset (Fin (d + 1)), S.Nonempty → (∀ a ∈ S, π₁ a ∈ S) →
      (∀ a ∈ S, π₂ a ∈ S) → S = Finset.univ) :
    E6TwoTB.SecEltAt 3 (tE K F).range := by
  refine ⟨d + 1, TableBF4.piTorus (tE K F), frameWeyl K F w₁ w₂,
    TableBF4.range_piTorus _, ?_, ?_, ?_, ?_, ?_⟩
  · intro L' _ ψ hψ hker
    obtain ⟨σ, hσ⟩ := tD_section F hψ hker
    exact ⟨σ, by rw [hσ, piTorus_tE]⟩
  · rintro x (⟨i, rfl⟩ | rfl | rfl) e he
    · have hm := map_conj_tE_le (K := K) F (nGen K F i) id
        (fun a y => ⟨_, nGen_conj_tC F i a y⟩)
      exact hm ⟨e, he, rfl⟩
    · have hm := map_conj_tE_le (K := K) F (nWA τ K w₁) π₁ (fun a y => by
        obtain ⟨k, -, hk⟩ := conj_nWA_tC hK F h₁ a
        exact ⟨_, hk y⟩)
      exact hm ⟨e, he, rfl⟩
    · have hm := map_conj_tE_le (K := K) F (nWA τ K w₂) π₂ (fun a y => by
        obtain ⟨k, -, hk⟩ := conj_nWA_tC hK F h₂ a
        exact ⟨_, hk y⟩)
      exact hm ⟨e, he, rfl⟩
  · intro E' hle hinv
    exact irreducible_frame hK F h₁ h₂ htrans E' hle hinv
  · refine ⟨nGen K F 0, Or.inl ⟨0, rfl⟩, tGen K F 0,
      ⟨Multiplicative.ofAdd (Pi.single 0 1), by rw [tE_single, tC_one]⟩, ?_⟩
    intro h
    rw [← tC_one F 0, nGen_conj_tC, if_pos rfl] at h
    have h2 := tC_injective F 0 h
    exact absurd h2 (by decide)
  · intro G hGE hGmul hGW
    exact schur_frame hK F h₁ h₂ htrans G hGE hGmul hGW

end Frame

end TableBExcTwoTB

end CFSG.StandardType

end
