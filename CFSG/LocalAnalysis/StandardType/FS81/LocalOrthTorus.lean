module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Multiplicative CFSG.Open CFSG.Assembly CFSG.StandardType.SpCoord CFSG.StandardType.NbrOrth

variable {G : Type} [Group G] {L : Type} [Group L]

private noncomputable def torusHom {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    (τ : (Fin n → Multiplicative (ZMod 3)) →* L) :
    (Fin n → Multiplicative (ZMod 3)) →* G :=
  (Subgroup.subtype K).comp (φ.symm.toMonoidHom.comp τ)

private theorem torusHom_apply {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    (τ : (Fin n → Multiplicative (ZMod 3)) →* L) (f : Fin n → Multiplicative (ZMod 3)) :
    torusHom φ τ f = (φ.symm (τ f) : G) := rfl

private noncomputable def torusCoord {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    (τ : (Fin n → Multiplicative (ZMod 3)) →* L) : Fin n → G :=
  fun i => (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)

private noncomputable def torusB {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    (τ : (Fin n → Multiplicative (ZMod 3)) →* L) : Fin (n + 1) → G :=
  Fin.cons b₀ (torusCoord φ τ)

private theorem commute_of_mem_centralizer {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) {x : G} (hx : x ∈ K) :
    Commute b₀ x := by
  have h := hKC hx
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h.symm

private theorem commute_torusHom {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    (τ : (Fin n → Multiplicative (ZMod 3)) →* L)
    (a b : Fin n → Multiplicative (ZMod 3)) :
    Commute (torusHom φ τ a) (torusHom φ τ b) := by
  rw [torusHom_apply, torusHom_apply]
  have h : (φ.symm (τ a)) * (φ.symm (τ b)) = (φ.symm (τ b)) * (φ.symm (τ a)) := by
    calc (φ.symm (τ a)) * (φ.symm (τ b)) = φ.symm (τ a * τ b) := (map_mul _ _ _).symm
      _ = φ.symm (τ (a * b)) := congrArg φ.symm (map_mul τ a b).symm
      _ = φ.symm (τ (b * a)) := congrArg (fun x => φ.symm (τ x)) (mul_comm a b)
      _ = φ.symm (τ b * τ a) := congrArg φ.symm (map_mul τ b a)
      _ = (φ.symm (τ b)) * (φ.symm (τ a)) := map_mul _ _ _
  have hG : (↑(φ.symm (τ a)) : G) * ↑(φ.symm (τ b)) =
      ↑(φ.symm (τ b)) * ↑(φ.symm (τ a)) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, h]
  exact hG

theorem torusBasis_comm {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) :
    ∀ i j, Commute
      (Fin.cons (α := fun _ => G) b₀ (fun i =>
        (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)) i)
      (Fin.cons (α := fun _ => G) b₀ (fun i =>
        (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)) j) := by
  intro i j
  change Commute (torusB (b₀ := b₀) φ τ i) (torusB (b₀ := b₀) φ τ j)
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact Commute.refl _
    | succ j =>
      rw [show torusB (b₀ := b₀) φ τ 0 = b₀ from rfl,
        show torusB (b₀ := b₀) φ τ j.succ = (φ.symm (τ (Pi.mulSingle j (ofAdd 1))) : G) from rfl]
      exact commute_of_mem_centralizer hKC (φ.symm (τ (Pi.mulSingle j (ofAdd 1)))).2
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [show torusB (b₀ := b₀) φ τ 0 = b₀ from rfl,
        show torusB (b₀ := b₀) φ τ i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G) from rfl]
      exact (commute_of_mem_centralizer hKC (φ.symm (τ (Pi.mulSingle i (ofAdd 1)))).2).symm
    | succ j =>
      rw [show torusB (b₀ := b₀) φ τ i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G) from rfl,
        show torusB (b₀ := b₀) φ τ j.succ = (φ.symm (τ (Pi.mulSingle j (ofAdd 1))) : G) from rfl]
      exact commute_torusHom φ τ _ _

private theorem torusHom_injective {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ) :
    Function.Injective (torusHom φ τ) := by
  intro a b h
  have h' : (φ.symm (τ a) : ↥K) = φ.symm (τ b) := by
    apply Subtype.ext
    simpa only [torusHom_apply] using h
  exact hτ (φ.symm.injective h')

private theorem orderOf_torusHom {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ) (i : Fin n) :
    orderOf (torusHom φ τ (Pi.mulSingle i (ofAdd 1))) = 3 := by
  rw [orderOf_injective (torusHom φ τ) (torusHom_injective φ hτ)]
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [mulSingle_ofAdd_pow, ZMod.natCast_self, zero_mul, ofAdd_zero, Pi.mulSingle_one]
  · intro h
    have h' := congrFun h i
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h'
    have h'' : (1 : ZMod 3) = 0 := by simpa using congrArg Multiplicative.toAdd h'
    exact one_ne_zero h''

theorem torusBasis_ord {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ)
    (hb₀ : orderOf b₀ = 3) (i : Fin (n + 1)) :
    orderOf (Fin.cons (α := fun _ => G) b₀ (fun i =>
      (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)) i) = 3 := by
  change orderOf (torusB (b₀ := b₀) φ τ i) = 3
  cases i using Fin.cases with
  | zero => rw [show torusB (b₀ := b₀) φ τ 0 = b₀ from rfl]; exact hb₀
  | succ i =>
    rw [show torusB (b₀ := b₀) φ τ i.succ =
      (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G) from rfl]
    exact orderOf_torusHom φ hτ i

private theorem prod_torusBasis_eq {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    (τ : (Fin n → Multiplicative (ZMod 3)) →* L) (e : Coords (n + 1)) :
    (List.ofFn fun i => (torusB (b₀ := b₀) φ τ i) ^ (e i).val).prod =
      b₀ ^ (e 0).val * torusHom φ τ (fun i => ofAdd (e i.succ)) := by
  rw [List.ofFn_succ, List.prod_cons,
    show torusB (b₀ := b₀) φ τ 0 = b₀ from rfl]
  congr 1
  have hf : (fun i : Fin n => ofAdd (e i.succ)) =
      (List.ofFn fun i : Fin n =>
        (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3)) ^ (e i.succ).val).prod := by
    rw [Fin.prod_ofFn, ← Finset.univ_prod_mulSingle (fun i : Fin n => ofAdd (e i.succ))]
    exact Finset.prod_congr rfl fun i _ => mulSingle_ofAdd_eq_pow i (e i.succ)
  rw [hf, map_list_prod, ← List.ofFn_comp']
  apply congrArg List.prod
  rw [List.ofFn_inj]
  funext i
  simp only [torusB, Fin.cons_succ, Function.comp_apply, map_pow, torusHom_apply, torusCoord]

private theorem torus_pow_and_hom_eq_one {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    {m : ℕ} {f : Fin n → Multiplicative (ZMod 3)}
    (h : b₀ ^ m * torusHom φ τ f = 1) :
    b₀ ^ m = 1 ∧ torusHom φ τ f = 1 := by
  have hmul : b₀ ^ m = (torusHom φ τ f)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hmem : b₀ ^ m ∈ Subgroup.zpowers b₀ ⊓ K := by
    refine ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _, ?_⟩
    rw [hmul]
    exact K.inv_mem (by rw [torusHom_apply]; exact (φ.symm (τ f)).2)
  rw [disjoint_iff.mp hdisj] at hmem
  have hb : b₀ ^ m = 1 := Subgroup.mem_bot.mp hmem
  refine ⟨hb, ?_⟩
  rw [hb, one_mul] at h
  exact h

theorem torusBasis_indep {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ)
    (hb₀ : orderOf b₀ = 3) (hdisj : Disjoint (Subgroup.zpowers b₀) K) (e : Coords (n + 1)) :
    (List.ofFn fun i => (Fin.cons (α := fun _ => G) b₀ (fun i =>
      (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)) i) ^ (e i).val).prod = 1 → e = 0 := by
  change (List.ofFn fun i => (torusB (b₀ := b₀) φ τ i) ^ (e i).val).prod = 1 → e = 0
  intro hprod
  set f : Fin n → Multiplicative (ZMod 3) := fun i => ofAdd (e i.succ) with hf
  rw [prod_torusBasis_eq φ τ e] at hprod
  obtain ⟨hb, hσ⟩ := torus_pow_and_hom_eq_one φ hdisj hprod
  have he0 : e 0 = 0 := by
    have hdvd : 3 ∣ (e 0).val := by
      have h := orderOf_dvd_iff_pow_eq_one.mpr hb
      rwa [hb₀] at h
    have hval : (e 0).val = 0 := by
      have hlt := ZMod.val_lt (e 0)
      omega
    exact (ZMod.val_eq_zero (e 0)).mp hval
  have hsucc : ∀ i : Fin n, e i.succ = 0 := by
    have hσ' : (φ.symm (τ f) : ↥K) = 1 := by
      apply Subtype.ext
      rw [← torusHom_apply φ τ f]
      exact hσ
    have hτf : τ f = 1 := by
      have h := congrArg (fun x : ↥K => φ x) hσ'
      simpa using h
    have hf1 : f = 1 := hτ (by simpa using hτf)
    intro i
    have h := congrFun hf1 i
    rw [hf] at h
    have h'' := congrArg Multiplicative.toAdd h
    simpa using h''
  funext k
  cases k using Fin.cases with
  | zero => exact he0
  | succ i => exact hsucc i

private theorem closure_range_gen_eq {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} {E : Subgroup G}
    (hEK : ∀ x : ↥K, (x : G) ∈ E ↔ φ x ∈ τ.range) :
    Subgroup.closure (Set.range fun i =>
      (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)) = E ⊓ K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hEK (φ.symm (τ (Pi.mulSingle i (ofAdd 1))))).mpr
      ⟨Pi.mulSingle i (ofAdd 1), by rw [MulEquiv.apply_symm_apply]⟩,
      (φ.symm (τ (Pi.mulSingle i (ofAdd 1)))).2⟩
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyE, hyK⟩ := hy
    obtain ⟨z, hz⟩ := (hEK ⟨y, hyK⟩).mp hyE
    have hyz : y = torusHom φ τ z := by
      rw [torusHom_apply, hz, MulEquiv.symm_apply_apply]
    have hzdec : z = (List.ofFn fun i : Fin n =>
        (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3)) ^
          (toAdd (z i)).val).prod := by
      rw [Fin.prod_ofFn]
      calc z = ∏ i, Pi.mulSingle i (z i) := (Finset.univ_prod_mulSingle z).symm
        _ = ∏ i, (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3)) ^
              (toAdd (z i)).val := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [← ofAdd_toAdd (z i)]
            exact mulSingle_ofAdd_eq_pow i (toAdd (z i))
    rw [hyz, hzdec, map_list_prod, ← List.ofFn_comp']
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [map_pow, torusHom_apply]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

@[expose] noncomputable def torusBasis {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ)
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K) : Basis3 G (n + 1) where
  b := Fin.cons (α := fun _ => G) b₀ fun i => (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)
  comm := torusBasis_comm φ hKC
  ord := torusBasis_ord φ hτ hb₀
  indep := torusBasis_indep φ hτ hb₀ hdisj

section

variable {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
  {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ)
  (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
  (hdisj : Disjoint (Subgroup.zpowers b₀) K)

theorem torusBasis_b_zero : (torusBasis φ hτ hb₀ hKC hdisj).b 0 = b₀ := rfl

theorem torusBasis_b_succ (i : Fin n) :
    (torusBasis φ hτ hb₀ hKC hdisj).b i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G) := rfl

theorem torusBasis_adapted {E : Subgroup G} (hEK : ∀ x : ↥K, (x : G) ∈ E ↔ φ x ∈ τ.range)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E) :
    Adapted (torusBasis φ hτ hb₀ hKC hdisj) b₀ K E := by
  have hgen : Subgroup.closure (Set.range fun i =>
      (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)) = E ⊓ K := closure_range_gen_eq φ hEK
  refine ⟨?_, torusBasis_b_zero φ hτ hb₀ hKC hdisj, ?_⟩
  · rw [Basis3.span]
    change Subgroup.closure (Set.range (Fin.cons (α := fun _ => G) b₀ (fun i =>
      (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)))) = E
    rw [Fin.range_cons, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure b₀, hgen]
    exact hsup
  · intro i hi
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hi
    rw [← hj, torusBasis_b_succ]
    exact (φ.symm (τ (Pi.mulSingle j (ofAdd 1)))).2

private theorem realized_list_prod {n : ℕ} (B : Basis3 G (n + 1)) {H : Subgroup G}
    {l : List (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))}
    (h : ∀ A ∈ l, A ∈ B.realized H) : l.prod ∈ B.realized H := by
  induction l with
  | nil => simpa using realized_one B H
  | cons A l ih =>
    rw [List.prod_cons]
    exact realized_mul B (h A (by simp)) (ih fun A hA => h A (by simp [hA]))

private theorem spMat_one_one {k : ℕ} :
    spMat (1 : Equiv.Perm (Fin k)) (1 : Fin k → ZMod 3) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [spMat, Matrix.one_apply, h]

private theorem spMat_one_mul {k : ℕ} (s t : Fin k → ZMod 3) :
    spMat (1 : Equiv.Perm (Fin k)) s * spMat (1 : Equiv.Perm (Fin k)) t =
      spMat (1 : Equiv.Perm (Fin k)) (s * t) := by
  rw [spMat_mul]
  rfl

private theorem spMat_one_list_prod {k : ℕ} (l : List (Fin k → ZMod 3)) :
    spMat (1 : Equiv.Perm (Fin k)) l.prod =
      (l.map (spMat (1 : Equiv.Perm (Fin k)))).prod := by
  induction l with
  | nil => simpa using spMat_one_one (k := k)
  | cons s l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, spMat_one_mul]

private theorem spMat_eq_perm_mul_diag {k : ℕ} (σ : Equiv.Perm (Fin k))
    (s : Fin k → ZMod 3) :
    spMat σ s = spMat σ (fun _ => (1 : ZMod 3)) * spMat (1 : Equiv.Perm (Fin k)) s := by
  rw [spMat_mul]
  ext i j
  simp [spMat]

private theorem perm_tail {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ 0 = 0) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, σ i.succ = (π i).succ := by
  refine ⟨(Equiv.Perm.decomposeFin σ).2, fun i => ?_⟩
  have hσ' : σ = Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin σ) :=
    (Equiv.symm_apply_apply Equiv.Perm.decomposeFin σ).symm
  have hz : (Equiv.Perm.decomposeFin σ).1 = 0 := by
    have h := Equiv.Perm.decomposeFin_symm_apply_zero (n := n)
      (p := (Equiv.Perm.decomposeFin σ).1) (e := (Equiv.Perm.decomposeFin σ).2)
    rw [← hσ'] at h
    exact h.symm.trans hσ
  rw [hσ', Equiv.Perm.decomposeFin_symm_apply_succ, hz]
  simp

private theorem conj_of_commute {x g : G} (h : Commute x g) : g * x * g⁻¹ = x := by
  rw [← h.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem conj_torusCoord {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (w : L)
    (x : Fin n → Multiplicative (ZMod 3)) :
    ((φ.symm w : ↥K) : G) * (φ.symm (τ x) : G) * (((φ.symm w : ↥K) : G))⁻¹ =
      (φ.symm (w * τ x * w⁻¹) : G) := by
  have hK : (φ.symm w) * (φ.symm (τ x)) * (φ.symm w)⁻¹ = φ.symm (w * τ x * w⁻¹) := by
    apply φ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hG := congrArg (Subgroup.subtype K) hK
  rw [map_mul, map_mul, map_inv] at hG
  exact hG

private theorem torusCoord_pow {n : ℕ} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L}
    (x : Fin n → Multiplicative (ZMod 3)) (t : ℕ) :
    (φ.symm (τ x) : G) ^ t = (φ.symm (τ (x ^ t)) : G) := by
  rw [← Subgroup.coe_pow, ← map_pow, ← map_pow]

private theorem permMat_mem_realized {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ)
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∃ w : L, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f))
    {σ : Equiv.Perm (Fin (n + 1))} (hσ0 : σ 0 = 0) :
    spMat σ (fun _ => (1 : ZMod 3)) ∈ (torusBasis φ hτ hb₀ hKC hdisj).realized K := by
  obtain ⟨π, hπ⟩ := perm_tail hσ0
  obtain ⟨w, hw⟩ := hperm π
  refine ⟨((φ.symm w : ↥K) : G), (φ.symm w).2, ?_⟩
  rw [Basis3.acts_spMat_iff]
  intro j
  cases j using Fin.cases with
  | zero =>
    rw [show (σ) 0 = 0 from hσ0, torusBasis_b_zero,
      show ((fun _ => (1 : ZMod 3)) (0 : Fin (n + 1))).val = 1 from rfl, pow_one]
    exact conj_of_commute (commute_of_mem_centralizer hKC (φ.symm w).2)
  | succ i =>
    rw [torusBasis_b_succ, conj_torusCoord, hw, permAut_mulSingle, ← torusBasis_b_succ,
      show ((fun _ => (1 : ZMod 3)) i.succ).val = 1 from rfl, pow_one, hπ i]

private def sgnVec {n : ℕ} (i : Fin n) : Fin n → ZMod 3 := fun k => if k = i then -1 else 1

private def dinvTail {n : ℕ} (i j : Fin n) : Fin n → ZMod 3 := sgnVec i * sgnVec j

private theorem dinvTail_self_left {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    dinvTail i j i = -1 := by
  simp only [dinvTail, sgnVec, Pi.mul_apply, if_pos rfl, if_neg hij]
  decide

private theorem dinvTail_self_right {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    dinvTail i j j = -1 := by
  simp only [dinvTail, sgnVec, Pi.mul_apply, if_neg (Ne.symm hij), if_pos rfl]
  decide

private theorem dinvTail_of_ne {n : ℕ} {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    dinvTail i j k = 1 := by
  simp only [dinvTail, sgnVec, Pi.mul_apply, if_neg hki, if_neg hkj]
  decide

private theorem sgnVec_mul_self {n : ℕ} (i : Fin n) : sgnVec i * sgnVec i = 1 := by
  funext k
  by_cases h : k = i
  · simp only [sgnVec, Pi.mul_apply, if_pos h, Pi.one_apply]
    decide
  · simp only [sgnVec, Pi.mul_apply, if_neg h, Pi.one_apply]
    decide

private theorem dinvTail_mul_self {n : ℕ} (i j : Fin n) :
    dinvTail i j * dinvTail i j = 1 := by
  rw [dinvTail]
  calc sgnVec i * sgnVec j * (sgnVec i * sgnVec j)
      = (sgnVec i * sgnVec i) * (sgnVec j * sgnVec j) := by ac_rfl
    _ = 1 := by rw [sgnVec_mul_self, sgnVec_mul_self, one_mul]

private theorem even_card_negSet {n : ℕ} {t : Fin n → ZMod 3}
    (ht : ∀ i, t i = 1 ∨ t i = -1) (hprod : ∏ i, t i = 1) :
    Even (Finset.univ.filter fun i => t i = -1).card := by
  classical
  set T : Finset (Fin n) := Finset.univ.filter fun i => t i = -1 with hTdef
  have hT : ∀ i, t i = -1 ↔ i ∈ T := by intro i; simp [hTdef]
  have hprodt : (∏ i, t i) = ∏ i ∈ T, (-1 : ZMod 3) := by
    calc ∏ i, t i = ∏ i, (if t i = -1 then t i else 1) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases h : t i = -1
          · rw [if_pos h]
          · rcases ht i with h1 | h1
            · rw [if_neg h, h1]
            · exact absurd h1 h
      _ = ∏ i ∈ Finset.univ.filter (fun i => t i = -1), t i :=
          (Finset.prod_filter (s := Finset.univ) (p := fun i => t i = -1) (f := t)).symm
      _ = ∏ i ∈ T, (-1 : ZMod 3) := by
          rw [show Finset.univ.filter (fun i => t i = -1) = T from rfl]
          exact Finset.prod_congr rfl fun i hi => (hT i).mpr hi
  rw [hprodt, Finset.prod_const] at hprod
  have h2 : 2 ∣ T.card := by
    have ho : orderOf (-1 : ZMod 3) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
      exact orderOf_eq_prime (by decide) (by decide)
    rw [← ho]
    exact orderOf_dvd_iff_pow_eq_one.mpr hprod
  rw [Nat.even_iff]
  exact Nat.dvd_iff_mod_eq_zero.mp h2

private theorem negSet_mul_dinvTail {n : ℕ} {T : Finset (Fin n)} {t : Fin n → ZMod 3}
    (hT : ∀ i, t i = -1 ↔ i ∈ T) {i j : Fin n} (hi : i ∈ T) (hj : j ∈ T.erase i) :
    ∀ k, (t * dinvTail i j) k = -1 ↔ k ∈ (T.erase i).erase j := by
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjT : j ∈ T := (Finset.mem_erase.mp hj).2
  have hij : i ≠ j := Ne.symm hji
  have hTi : t i = -1 := (hT i).mpr hi
  have htj : t j = -1 := (hT j).mpr hjT
  intro k
  rw [Pi.mul_apply]
  by_cases hki : k = i
  · rw [show t k * dinvTail i j k = 1 by rw [hki, hTi, dinvTail_self_left hij]; decide, hki]
    constructor
    · intro h
      exact absurd h (by decide)
    · intro h
      rw [Finset.mem_erase, Finset.mem_erase] at h
      exact absurd rfl h.2.1
  · by_cases hkj : k = j
    · rw [show t k * dinvTail i j k = 1 by rw [hkj, htj, dinvTail_self_right hij]; decide, hkj]
      constructor
      · intro h
        exact absurd h (by decide)
      · intro h
        rw [Finset.mem_erase, Finset.mem_erase] at h
        exact absurd rfl h.1
    · rw [dinvTail_of_ne hki hkj, mul_one, hT k]
      constructor
      · intro hk
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨hkj, hki, hk⟩
      · intro h
        rw [Finset.mem_erase, Finset.mem_erase] at h
        exact h.2.2

private theorem isSign_mul_dinvTail {n : ℕ} {t : Fin n → ZMod 3}
    (ht : ∀ i, t i = 1 ∨ t i = -1) {i j : Fin n} (hij : i ≠ j) :
    ∀ k, (t * dinvTail i j) k = 1 ∨ (t * dinvTail i j) k = -1 := by
  intro k
  rw [Pi.mul_apply]
  have h1 : t k = 1 ∨ t k = -1 := ht k
  have h2 : dinvTail i j k = 1 ∨ dinvTail i j k = -1 := by
    by_cases hki : k = i
    · exact Or.inr (by rw [hki]; exact dinvTail_self_left hij)
    · by_cases hkj : k = j
      · exact Or.inr (by rw [hkj]; exact dinvTail_self_right hij)
      · exact Or.inl (dinvTail_of_ne hki hkj)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [h1, h2]; left; decide
  · rw [h1, h2]; right; decide
  · rw [h1, h2]; right; decide
  · rw [h1, h2]; left; decide

private theorem card_erase_two {n : ℕ} {T : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ T) (hj : j ∈ T.erase i) :
    ((T.erase i).erase j).card = T.card - 2 := by
  rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]
  omega

private theorem ssubset_erase_two {n : ℕ} {T : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ T) (hj : j ∈ T.erase i) : (T.erase i).erase j ⊂ T := by
  have hsub : (T.erase i).erase j ⊆ T := by
    intro x hx
    simp only [Finset.mem_erase] at hx
    exact hx.2.2
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨i, hi, by simp⟩

private theorem exists_dinvTail_prod_empty {n : ℕ} {T : Finset (Fin n)} (hT0 : T = ∅)
    {t : Fin n → ZMod 3} (hT : ∀ i, t i = -1 ↔ i ∈ T)
    (ht : ∀ i, t i = 1 ∨ t i = -1) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, p.1 ≠ p.2) ∧
      t = (l.map fun p => dinvTail p.1 p.2).prod := by
  have ht1 : t = 1 := by
    funext k
    rcases ht k with h | h
    · exact h
    · exfalso
      have hk : k ∈ T := (hT k).mp h
      rw [hT0] at hk
      exact Finset.notMem_empty k hk
  exact ⟨[], by simp, by rw [ht1]; simp⟩

private theorem exists_dinvTail_prod_nonempty {n : ℕ} {T : Finset (Fin n)}
    (ih : ∀ T' : Finset (Fin n), T' ⊂ T → ∀ (t : Fin n → ZMod 3),
      (∀ i, t i = -1 ↔ i ∈ T') → (∀ i, t i = 1 ∨ t i = -1) →
      Even T'.card → ∃ l : List (Fin n × Fin n), (∀ p ∈ l, p.1 ≠ p.2) ∧
        t = (l.map fun p => dinvTail p.1 p.2).prod)
    (hT0 : T ≠ ∅) {t : Fin n → ZMod 3} (hT : ∀ i, t i = -1 ↔ i ∈ T)
    (ht : ∀ i, t i = 1 ∨ t i = -1) (heven : Even T.card) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, p.1 ≠ p.2) ∧
      t = (l.map fun p => dinvTail p.1 p.2).prod := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT0
  obtain ⟨m, hm⟩ := heven
  obtain ⟨j, hj⟩ : (T.erase i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [Finset.erase_eq_empty_iff] at h
    rcases h with h | h
    · exact hT0 h
    · rw [h, Finset.card_singleton] at hm
      omega
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
  have hT2sub : (T.erase i).erase j ⊂ T := ssubset_erase_two hi hj
  have hcard : ((T.erase i).erase j).card = T.card - 2 := card_erase_two hi hj
  have heven2 : Even ((T.erase i).erase j).card := by
    rw [hcard]
    exact ⟨m - 1, by omega⟩
  let t' : Fin n → ZMod 3 := t * dinvTail i j
  have ht' : ∀ k, t' k = 1 ∨ t' k = -1 := by
    intro k
    dsimp only [t']
    exact isSign_mul_dinvTail ht hij k
  have hT2 : ∀ k, t' k = -1 ↔ k ∈ (T.erase i).erase j := by
    intro k
    dsimp only [t']
    exact negSet_mul_dinvTail hT hi hj k
  obtain ⟨l, hl, hlt⟩ := ih ((T.erase i).erase j) hT2sub t' hT2 ht' heven2
  have hdecomp : t = dinvTail i j * t' := by
    dsimp only [t']
    calc t = t * 1 := (mul_one t).symm
      _ = t * (dinvTail i j * dinvTail i j) := by rw [dinvTail_mul_self]
      _ = dinvTail i j * (t * dinvTail i j) := by ac_rfl
  refine ⟨(i, j) :: l, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hij
    · exact hl p hp
  · rw [List.map_cons, List.prod_cons, ← hlt]
    exact hdecomp

private theorem exists_dinvTail_prod_aux {n : ℕ} (T : Finset (Fin n)) :
    ∀ (t : Fin n → ZMod 3), (∀ i, t i = -1 ↔ i ∈ T) →
      (∀ i, t i = 1 ∨ t i = -1) → Even T.card →
      ∃ l : List (Fin n × Fin n), (∀ p ∈ l, p.1 ≠ p.2) ∧
        t = (l.map fun p => dinvTail p.1 p.2).prod := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
    intro t hT ht heven
    by_cases hT0 : T = ∅
    · exact exists_dinvTail_prod_empty hT0 hT ht
    · exact exists_dinvTail_prod_nonempty ih hT0 hT ht heven

private theorem exists_dinvTail_prod {n : ℕ} {t : Fin n → ZMod 3}
    (ht : ∀ i, t i = 1 ∨ t i = -1) (hprod : ∏ i, t i = 1) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, p.1 ≠ p.2) ∧
      t = (l.map fun p => dinvTail p.1 p.2).prod := by
  let T : Finset (Fin n) := Finset.univ.filter fun i => t i = -1
  exact exists_dinvTail_prod_aux T t (by intro i; simp [T]) ht (even_card_negSet ht hprod)

private theorem fin_cons_one_mul {n : ℕ} (a b : Fin n → ZMod 3) :
    Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (a * b) =
      (Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) a) *
        (Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) b) := by
  ext k
  cases k using Fin.cases <;> simp

private theorem fin_cons_one_list_prod {n : ℕ} (l : List (Fin n → ZMod 3)) :
    Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) l.prod =
      (l.map fun x => Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) x).prod := by
  induction l with
  | nil =>
    ext k
    cases k using Fin.cases <;> simp
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, fin_cons_one_mul]

private theorem exists_dinvSign_prod {n : ℕ} {s : Fin (n + 1) → ZMod 3}
    (hs : IsSign s) (hs0 : s 0 = 1) (hprod : ∏ i : Fin n, s i.succ = 1) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, p.1 ≠ p.2) ∧
      s = (l.map fun p => Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3)
        (dinvTail p.1 p.2)).prod := by
  let t : Fin n → ZMod 3 := fun i => s i.succ
  obtain ⟨l, hl, hlt⟩ := exists_dinvTail_prod (t := t) (fun i => hs i.succ) hprod
  have hscons : s = Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) t := by
    rw [← Fin.cons_self_tail s, hs0]
    rfl
  refine ⟨l, hl, ?_⟩
  have hmap : (l.map fun p => Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3)
      (dinvTail p.1 p.2)) =
      ((l.map fun p => dinvTail p.1 p.2).map fun x =>
        Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) x) := by
    rw [List.map_map]
    rfl
  rw [hmap, ← fin_cons_one_list_prod, ← hlt, ← hscons]

private theorem dinv_comm {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (f : Fin n → Multiplicative (ZMod 3)) : dinv i j f = dinv j i f := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [dinv, hij, Ne.symm hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [dinv, hij, Ne.symm hij]
    · simp [dinv, hki, hkj]

private theorem dinv_mulSingle_one {n : ℕ} {i j m : Fin n} (hij : i ≠ j) :
    dinv i j (Pi.mulSingle m (ofAdd (1 : ZMod 3))) =
      (Pi.mulSingle m (ofAdd 1) : Fin n → Multiplicative (ZMod 3)) ^ (dinvTail i j m).val := by
  by_cases hmi : m = i
  · subst hmi
    rw [dinv_mulSingle_self hij, dinvTail_self_left hij]
    have hval : (-1 : ZMod 3).val = 2 := by decide
    rw [hval, mulSingle_ofAdd_pow, ← Pi.mulSingle_inv]
    exact congrArg (Pi.mulSingle m)
      (by decide : (ofAdd (1 : ZMod 3))⁻¹ = ofAdd ((2 : ZMod 3) * 1))
  · by_cases hmj : m = j
    · subst hmj
      rw [dinv_comm hij, dinv_mulSingle_self (Ne.symm hij), dinvTail_self_right hij]
      have hval : (-1 : ZMod 3).val = 2 := by decide
      rw [hval, mulSingle_ofAdd_pow, ← Pi.mulSingle_inv]
      exact congrArg (Pi.mulSingle m)
        (by decide : (ofAdd (1 : ZMod 3))⁻¹ = ofAdd ((2 : ZMod 3) * 1))
    · rw [dinv_mulSingle_of_ne hmi hmj, dinvTail_of_ne hmi hmj,
        show (1 : ZMod 3).val = 1 from rfl, pow_one]

private theorem dinvMat_mem_realized {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ)
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    (hdinv : ∀ i j : Fin n, i ≠ j → ∃ w : L, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f))
    {i j : Fin n} (hij : i ≠ j) :
    spMat (1 : Equiv.Perm (Fin (n + 1)))
      (Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (dinvTail i j)) ∈
      (torusBasis φ hτ hb₀ hKC hdisj).realized K := by
  obtain ⟨w, hw⟩ := hdinv i j hij
  refine ⟨((φ.symm w : ↥K) : G), (φ.symm w).2, ?_⟩
  rw [Basis3.acts_spMat_iff]
  intro k
  cases k using Fin.cases with
  | zero =>
    rw [show (1 : Equiv.Perm (Fin (n + 1))) 0 = 0 from rfl, torusBasis_b_zero,
      show (Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (dinvTail i j)) 0 = 1 from rfl,
      show (1 : ZMod 3).val = 1 from rfl, pow_one]
    exact conj_of_commute (commute_of_mem_centralizer hKC (φ.symm w).2)
  | succ m =>
    rw [show (1 : Equiv.Perm (Fin (n + 1))) m.succ = m.succ from rfl, torusBasis_b_succ,
      conj_torusCoord, hw,
      show (Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (dinvTail i j)) m.succ =
        dinvTail i j m from rfl,
      torusCoord_pow, dinv_mulSingle_one hij]

private theorem mem_evenFix0_iff {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} :
    A ∈ evenFix0 n ↔ ∃ σ s, IsSign s ∧
      (σ 0 = 0 ∧ s 0 = 1 ∧ (∏ i : Fin n, s i.succ) = 1) ∧ A = spMat σ s :=
  Iff.rfl

theorem torusBasis_heven
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∃ w : L, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f))
    (hdinv : ∀ i j : Fin n, i ≠ j → ∃ w : L, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) :
    evenFix0 n ⊆ (torusBasis φ hτ hb₀ hKC hdisj).realized K := by
  intro A hA
  rw [mem_evenFix0_iff] at hA
  obtain ⟨σ, s, hs, ⟨hσ0, hs0, hprod⟩, rfl⟩ := hA
  have hperm_mem : spMat σ (fun _ => (1 : ZMod 3)) ∈
      (torusBasis φ hτ hb₀ hKC hdisj).realized K :=
    permMat_mem_realized φ hτ hb₀ hKC hdisj hperm hσ0
  obtain ⟨l, hl, hsl⟩ := exists_dinvSign_prod hs hs0 hprod
  have hdiag_mem : spMat (1 : Equiv.Perm (Fin (n + 1))) s ∈
      (torusBasis φ hτ hb₀ hKC hdisj).realized K := by
    rw [hsl, spMat_one_list_prod]
    refine realized_list_prod (torusBasis φ hτ hb₀ hKC hdisj) fun X hX => ?_
    rw [List.mem_map] at hX
    obtain ⟨a, ha, rfl⟩ := hX
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact dinvMat_mem_realized φ hτ hb₀ hKC hdisj hdinv (hl p hp)
  rw [spMat_eq_perm_mul_diag]
  exact realized_mul (torusBasis φ hτ hb₀ hKC hdisj) hperm_mem hdiag_mem

end

end CFSG.StandardType.FrameRoute.FS81

end
