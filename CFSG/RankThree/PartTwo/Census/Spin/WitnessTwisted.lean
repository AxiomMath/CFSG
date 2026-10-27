module

public import CFSG.RankThree.PartTwo.Census.Spin.Witness

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

section TorusSet

variable {K : Type*} [Field K] {s : ℕ} [NeZero s] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] (ζ : Kˣ) (hζ : orderOf ζ = s) (S : κ → Finset ι)

@[expose] noncomputable def torusSetHom : (κ → Multiplicative (ZMod s)) →* (ι → Kˣ) :=
  ∏ b, ∏ i ∈ S b, (MonoidHom.mulSingle (fun _ : ι => Kˣ) i).comp
    ((zpowHom ζ hζ).comp (Pi.evalMonoidHom (fun _ : κ => Multiplicative (ZMod s)) b))

omit [Fintype ι] [DecidableEq κ] in
theorem torusSetHom_apply (e : κ → Multiplicative (ZMod s)) :
    torusSetHom ζ hζ S e = ∏ b, ∏ i ∈ S b, Pi.mulSingle i (zpowHom ζ hζ (e b)) := by
  simp [torusSetHom]

omit [Fintype ι] [DecidableEq κ] in
theorem torusSetHom_mem {L : Subfield K} (hζL : (ζ : K) ∈ L) (e : κ → Multiplicative (ZMod s))
    (k : ι) : ((torusSetHom ζ hζ S e k : Kˣ) : K) ∈ L := by
  rw [torusSetHom_apply, Finset.prod_apply, Units.coe_prod]
  refine L.prod_mem fun b _ => ?_
  rw [Finset.prod_apply, Units.coe_prod]
  refine L.prod_mem fun i _ => ?_
  by_cases hk : k = i
  · subst hk
    rw [Pi.mulSingle_eq_same]
    exact zpowHom_mem ζ hζ hζL _
  · rw [Pi.mulSingle_eq_of_ne hk, Units.val_one]
    exact L.one_mem

omit [Fintype ι] [DecidableEq κ] in
theorem torusSetHom_perm (π : Equiv.Perm ι) (hS : ∀ b i, π i ∈ S b ↔ i ∈ S b)
    (e : κ → Multiplicative (ZMod s)) (k : ι) :
    torusSetHom ζ hζ S e (π k) = torusSetHom ζ hζ S e k := by
  rw [torusSetHom_apply, Finset.prod_apply, Finset.prod_apply]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Finset.prod_apply, Finset.prod_apply]
  by_cases hk : k ∈ S b
  · have hk' : π k ∈ S b := (hS b k).mpr hk
    rw [Finset.prod_eq_single (π k) (fun i _ hi => Pi.mulSingle_eq_of_ne (Ne.symm hi) _)
      (fun h => absurd hk' h), Finset.prod_eq_single k
      (fun i _ hi => Pi.mulSingle_eq_of_ne (Ne.symm hi) _) (fun h => absurd hk h),
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · have h1 : ∀ i ∈ S b, Pi.mulSingle (M := fun _ : ι => Kˣ) i (zpowHom ζ hζ (e b)) (π k) = 1 :=
      fun i hi => Pi.mulSingle_eq_of_ne (fun h => hk ((hS b k).mp (by rw [h]; exact hi))) _
    have h2 : ∀ i ∈ S b, Pi.mulSingle (M := fun _ : ι => Kˣ) i (zpowHom ζ hζ (e b)) k = 1 :=
      fun i hi =>
      Pi.mulSingle_eq_of_ne (fun h => hk (by rw [h]; exact hi)) _
    rw [Finset.prod_eq_one h1, Finset.prod_eq_one h2]

omit [DecidableEq κ] in
theorem torusSetHom_char (CM : Matrix ι ι ℤ) (e : κ → Multiplicative (ZMod s)) (j : ι) :
    ∏ k, (torusSetHom ζ hζ S e k) ^ CM k j =
      zpowHom ζ hζ (∏ b, ∏ i ∈ S b, e b ^ CM i j) := by
  simp only [map_prod, map_zpow, torusSetHom_apply, Finset.prod_apply]
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_eq_single i (fun k _ hk => by rw [Pi.mulSingle_eq_of_ne hk, one_zpow])
    (fun h => absurd (Finset.mem_univ _) h), Pi.mulSingle_eq_same]

theorem eq_one_of_torusSetHom_char (hs : s.Prime) (CM : Matrix ι ι ℤ) (rw : κ → ι)
    (hdet : (Matrix.of fun a b => ((∑ i ∈ S b, CM i (rw a) : ℤ) : ZMod s)).det ≠ 0)
    (e : κ → Multiplicative (ZMod s))
    (he : ∀ a, ∏ k, (torusSetHom ζ hζ S e k) ^ CM k (rw a) = 1) : e = 1 := by
  have hfact : Fact s.Prime := ⟨hs⟩
  set v : κ → ZMod s := fun b => Multiplicative.toAdd (e b)
  have hv : Matrix.mulVec (Matrix.of fun a b => ((∑ i ∈ S b, CM i (rw a) : ℤ) : ZMod s)) v =
      0 := by
    funext a
    have h1 := he a
    rw [torusSetHom_char, zpowHom_eq_one_iff] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [toAdd_prod, toAdd_one, toAdd_zpow] at h2
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul, zsmul_eq_mul, Int.cast_sum]
  have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  funext b
  have h3 := congrFun hv0 b
  exact Multiplicative.toAdd.injective (by simpa [v] using h3)

end TorusSet

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (R : RootData K N ι)

theorem torus_witness_of {H : Subgroup R.G} (L : Subfield K) (h2 : (2 : K) = 0)
    {s : ℕ} [NeZero s] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (τ : (κ → Multiplicative (ZMod s)) →* (ι → Kˣ))
    (hτD : ∀ e, R.torus (τ e) ∈ ⁅H, H⁆) (hτL : ∀ e j, ((τ e j : Kˣ) : K) ∈ L)
    (i₀ : ι) (hxD : ∀ u ∈ L, R.x i₀ u ∈ ⁅H, H⁆)
    (hnc : ∃ c ∈ ⁅H, H⁆, R.x i₀ 1 * c ≠ c * R.x i₀ 1)
    {κ' : Type*} (g : κ' → R.G) (hgD : ∀ a, g a ∈ ⁅H, H⁆)
    (hdet : ∀ e, (∀ a, Commute (R.torus (τ e)) (g a)) → e = 1) :
    ∃ E P : Subgroup R.G, IsWitness H s (Fintype.card κ) E P := by
  set θ := R.torus.comp τ
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    refine (Subgroup.mem_bot).mpr (hdet e fun a => ?_)
    change Commute (θ e) _
    rw [he]
    exact Commute.one_left _
  set P : Subgroup R.G := (L.toAddSubgroup.toSubgroup).map (R.root (.inl i₀))
  have hxP : ∀ u ∈ L, R.x i₀ u ∈ P := fun u hu => ⟨Multiplicative.ofAdd u, hu, rfl⟩
  refine ⟨θ.range, P, ⟨⟨⟨fun a b => ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, hnc.elim fun c hc =>
    ⟨R.x i₀ 1, hxP 1 L.one_mem, c, hc.1, hc.2⟩, ?_⟩⟩
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    change (a : R.G) * (b : R.G) = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ s = 1 := by
      funext b
      change Multiplicative.ofAdd (s • Multiplicative.toAdd (e b)) = Multiplicative.ofAdd 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_fun,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  · rintro _ ⟨e, rfl⟩
    exact hτD e
  · rintro _ ⟨u, hu, rfl⟩
    exact hxD _ hu
  · rintro ⟨_, u, hu, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change R.root (.inl i₀) u ^ 2 = 1
    rw [← map_pow]
    have : u ^ 2 = 1 := by
      change Multiplicative.ofAdd (2 • Multiplicative.toAdd u) = Multiplicative.ofAdd 0
      rw [nsmul_eq_mul, Nat.cast_ofNat, h2, zero_mul]
    rw [this, map_one]
  · rintro _ ⟨e, rfl⟩ hc
    rw [hdet e fun a => hc _ (hgD a), map_one]
  · rintro _ ⟨e, rfl⟩ _ ⟨u, hu, rfl⟩
    change R.torus (τ e) * R.x i₀ (Multiplicative.toAdd u) * (R.torus (τ e))⁻¹ ∈ P
    replace hu : Multiplicative.toAdd u ∈ L := hu
    rw [RootData.torus_conj_x]
    refine hxP _ (L.mul_mem ?_ hu)
    rw [Units.coe_prod]
    exact L.prod_mem fun k _ => by
      rw [Units.val_zpow_eq_zpow_val]
      exact L.zpow_mem (hτL e k) _

section Twisted

variable (σ : K →+* K) (π : Equiv.Perm ι) (F : R.G →* R.G)

structure IsTwistedFrobenius : Prop where
  map_x : ∀ i u, F (R.x i u) = R.x (π i) (σ u)
  map_y : ∀ i u, F (R.y i u) = R.y (π i) (σ u)
  map_torus : ∀ s, F (R.torus s) = R.torus fun j => Units.map (σ : K →* K) (s (π j))

@[expose] def pairX (a b : ι) (u : K) : R.G := R.x a u * R.x b (σ u)

@[expose] def pairY (a b : ι) (u : K) : R.G := R.y a u * R.y b (σ u)

variable {R σ π F}

theorem pairX_add {a b : ι} (hab : R.CM a b = 0) (u v : K) :
    R.pairX σ a b (u + v) = R.pairX σ a b u * R.pairX σ a b v := by
  simp only [pairX, map_add, x_add, mul_assoc]
  rw [← mul_assoc (R.x a v), (R.commute_x_x hab v (σ u)).eq, mul_assoc]

theorem pairY_add {a b : ι} (hab : R.CM a b = 0) (u v : K) :
    R.pairY σ a b (u + v) = R.pairY σ a b u * R.pairY σ a b v := by
  simp only [pairY, map_add, y_add, mul_assoc]
  rw [← mul_assoc (R.y a v), (R.commute_y_y hab v (σ u)).eq, mul_assoc]

theorem pairX_inv {a b : ι} (hab : R.CM a b = 0) (u : K) :
    (R.pairX σ a b u)⁻¹ = R.pairX σ a b (-u) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pairX_add hab, neg_add_cancel]
  simp [pairX, x_zero]

theorem pairY_inv {a b : ι} (hab : R.CM a b = 0) (u : K) :
    (R.pairY σ a b u)⁻¹ = R.pairY σ a b (-u) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pairY_add hab, neg_add_cancel]
  simp [pairY, y_zero]

variable (hF : R.IsTwistedFrobenius σ π F)
include hF

theorem x_mem_fixed_tw {i : ι} (hi : π i = i) {u : K} (hu : σ u = u) :
    R.x i u ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, hF.map_x, hi, hu]

theorem y_mem_fixed_tw {i : ι} (hi : π i = i) {u : K} (hu : σ u = u) :
    R.y i u ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, hF.map_y, hi, hu]

theorem torus_mem_fixed_tw {s : ι → Kˣ} (hs : ∀ j, σ (s (π j) : K) = s j) :
    R.torus s ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, hF.map_torus]
  congr 1
  funext j
  exact Units.ext (hs j)

theorem h_mem_fixed_tw {i : ι} (hi : π i = i) {c : Kˣ} (hc : σ c = c) :
    R.h i c ∈ fixedSubgroup F := by
  refine torus_mem_fixed_tw hF fun j => ?_
  by_cases hj : j = i
  · subst hj
    rw [hi, Pi.mulSingle_eq_same, hc]
  · have hj' : π j ≠ i := fun h => hj (π.injective (h.trans hi.symm))
    rw [Pi.mulSingle_eq_of_ne hj', Pi.mulSingle_eq_of_ne hj, Units.val_one, map_one]

theorem pairX_mem_fixed {a b : ι} (hab : π a = b) (hba : π b = a) (hcm : R.CM a b = 0)
    {u : K} (hu : σ (σ u) = u) : R.pairX σ a b u ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, pairX, map_mul, hF.map_x, hF.map_x, hab, hba, hu]
  exact (R.commute_x_x hcm u (σ u)).symm.eq

theorem pairY_mem_fixed {a b : ι} (hab : π a = b) (hba : π b = a) (hcm : R.CM a b = 0)
    {u : K} (hu : σ (σ u) = u) : R.pairY σ a b u ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, pairY, map_mul, hF.map_y, hF.map_y, hab, hba, hu]
  exact (R.commute_y_y hcm u (σ u)).symm.eq

omit hF in
theorem fixed_zpow {μ : Kˣ} (hμ : σ μ = μ) (k : ℤ) : σ ((μ ^ k : Kˣ) : K) = ((μ ^ k : Kˣ) : K) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hμ]

theorem x_mem_commutator_tw {i j : ι} (hi : π i = i) (hj : π j = j) {μ : Kˣ} (hμ : σ μ = μ)
    (hμc : μ ^ R.CM j i ≠ 1) {u : K} (hu : σ u = u) :
    R.x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  set c : K := ((μ ^ R.CM j i : Kˣ) : K)
  have hc1 : c - 1 ≠ 0 := fun h => hμc (Units.ext (sub_eq_zero.mp h))
  have hw : σ (u / (c - 1)) = u / (c - 1) := by
    rw [map_div₀, map_sub, fixed_zpow hμ, hu, map_one]
  have hc : R.x i u = ⁅R.h j μ, R.x i (u / (c - 1))⁆ := by
    rw [commutatorElement_def, h_conj_x, x_inv, ← x_add]
    congr 1
    field_simp
    ring
  rw [hc]
  exact Subgroup.commutator_mem_commutator (h_mem_fixed_tw hF hj hμ) (x_mem_fixed_tw hF hi hw)

theorem y_mem_commutator_tw {i j : ι} (hi : π i = i) (hj : π j = j) {μ : Kˣ} (hμ : σ μ = μ)
    (hμc : μ ^ R.CM j i ≠ 1) {u : K} (hu : σ u = u) :
    R.y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  set c : K := (((μ ^ R.CM j i)⁻¹ : Kˣ) : K) with hcdef
  have hc1 : c - 1 ≠ 0 := fun h => hμc (inv_eq_one.mp (Units.ext (sub_eq_zero.mp h)))
  have hσc : σ c = c := by
    rw [hcdef, ← zpow_neg]
    exact fixed_zpow hμ _
  have hw : σ (u / (c - 1)) = u / (c - 1) := by
    rw [map_div₀, map_sub, hσc, hu, map_one]
  have hc : R.y i u = ⁅R.h j μ, R.y i (u / (c - 1))⁆ := by
    rw [commutatorElement_def, h_conj_y, y_inv, ← y_add]
    congr 1
    field_simp
    ring
  rw [hc]
  exact Subgroup.commutator_mem_commutator (h_mem_fixed_tw hF hj hμ) (y_mem_fixed_tw hF hi hw)

omit hF in
theorem h_conj_pairX {a b j : ι} {k : ℤ} (hja : R.CM j a = k) (hjb : R.CM j b = k) {μ : Kˣ}
    (hμ : σ μ = μ) (w : K) :
    R.h j μ * R.pairX σ a b w * (R.h j μ)⁻¹ = R.pairX σ a b (((μ ^ k : Kˣ) : K) * w) := by
  have e1 : R.h j μ * R.pairX σ a b w * (R.h j μ)⁻¹ =
      (R.h j μ * R.x a w * (R.h j μ)⁻¹) * (R.h j μ * R.x b (σ w) * (R.h j μ)⁻¹) := by
    simp only [pairX]
    group
  rw [e1, h_conj_x, h_conj_x, hja, hjb, pairX, map_mul, fixed_zpow hμ]

omit hF in
theorem h_conj_pairY {a b j : ι} {k : ℤ} (hja : R.CM j a = k) (hjb : R.CM j b = k) {μ : Kˣ}
    (hμ : σ μ = μ) (w : K) :
    R.h j μ * R.pairY σ a b w * (R.h j μ)⁻¹ =
      R.pairY σ a b ((((μ ^ k)⁻¹ : Kˣ) : K) * w) := by
  have e1 : R.h j μ * R.pairY σ a b w * (R.h j μ)⁻¹ =
      (R.h j μ * R.y a w * (R.h j μ)⁻¹) * (R.h j μ * R.y b (σ w) * (R.h j μ)⁻¹) := by
    simp only [pairY]
    group
  rw [e1, h_conj_y, h_conj_y, hja, hjb, pairY, map_mul, ← zpow_neg, fixed_zpow hμ, zpow_neg]

theorem pairX_mem_commutator {a b j : ι} (hab : π a = b) (hba : π b = a) (hcm : R.CM a b = 0)
    (hj : π j = j) {k : ℤ} (hja : R.CM j a = k) (hjb : R.CM j b = k) {μ : Kˣ} (hμ : σ μ = μ)
    (hμk : μ ^ k ≠ 1) {u : K} (hu : σ (σ u) = u) :
    R.pairX σ a b u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  set c : K := ((μ ^ k : Kˣ) : K)
  have hc1 : c - 1 ≠ 0 := fun h => hμk (Units.ext (sub_eq_zero.mp h))
  have hσc : σ c = c := fixed_zpow hμ k
  have hw : σ (σ (u / (c - 1))) = u / (c - 1) := by
    simp only [map_div₀, map_sub, hσc, hu, map_one]
  have hc : R.pairX σ a b u = ⁅R.h j μ, R.pairX σ a b (u / (c - 1))⁆ := by
    rw [commutatorElement_def, h_conj_pairX hja hjb hμ, pairX_inv hcm, ← pairX_add hcm]
    congr 1
    field_simp
    ring
  rw [hc]
  exact Subgroup.commutator_mem_commutator (h_mem_fixed_tw hF hj hμ)
    (pairX_mem_fixed hF hab hba hcm hw)

theorem pairY_mem_commutator {a b j : ι} (hab : π a = b) (hba : π b = a) (hcm : R.CM a b = 0)
    (hj : π j = j) {k : ℤ} (hja : R.CM j a = k) (hjb : R.CM j b = k) {μ : Kˣ} (hμ : σ μ = μ)
    (hμk : μ ^ k ≠ 1) {u : K} (hu : σ (σ u) = u) :
    R.pairY σ a b u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  set c : K := (((μ ^ k)⁻¹ : Kˣ) : K) with hcdef
  have hc1 : c - 1 ≠ 0 := fun h => hμk (inv_eq_one.mp (Units.ext (sub_eq_zero.mp h)))
  have hσc : σ c = c := by
    rw [hcdef, ← zpow_neg]
    exact fixed_zpow hμ (-k)
  have hw : σ (σ (u / (c - 1))) = u / (c - 1) := by
    simp only [map_div₀, map_sub, hσc, hu, map_one]
  have hc : R.pairY σ a b u = ⁅R.h j μ, R.pairY σ a b (u / (c - 1))⁆ := by
    rw [commutatorElement_def, h_conj_pairY hja hjb hμ, pairY_inv hcm, ← pairY_add hcm]
    congr 1
    field_simp
    ring
  rw [hc]
  exact Subgroup.commutator_mem_commutator (h_mem_fixed_tw hF hj hμ)
    (pairY_mem_fixed hF hab hba hcm hw)

omit hF in
theorem h_mem_of_xy {D : Subgroup R.G} {i : ι} (hx : ∀ u, σ u = u → R.x i u ∈ D)
    (hy : ∀ u, σ u = u → R.y i u ∈ D) {c : Kˣ} (hc : σ c = c) : R.h i c ∈ D := by
  have hc' : σ (-((c⁻¹ : Kˣ) : K)) = -((c⁻¹ : Kˣ) : K) := by
    rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀, hc]
  rw [h_eq]
  refine D.mul_mem (D.mul_mem (D.mul_mem (hx _ hc) (hy _ hc')) (hx _ hc)) (D.inv_mem ?_)
  exact D.mul_mem (D.mul_mem (hx 1 (map_one σ)) (hy (-1) (by simp))) (hx 1 (map_one σ))

omit hF in
theorem h_mul_h_mem_of_pair {D : Subgroup R.G} {a b : ι} (hne : a ≠ b) (hcm : R.CM a b = 0)
    (hX : ∀ u, σ (σ u) = u → R.pairX σ a b u ∈ D) (hY : ∀ u, σ (σ u) = u → R.pairY σ a b u ∈ D)
    {c : Kˣ} (hc : σ c = c) : R.h a c * R.h b c ∈ D := by
  have hc' : σ (-((c⁻¹ : Kˣ) : K)) = -((c⁻¹ : Kˣ) : K) := by
    rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀, hc]
  have cxx : ∀ u v, Commute (R.x a u) (R.x b v) := R.commute_x_x hcm
  have cxy : ∀ u v, Commute (R.x a u) (R.y b v) := R.commute_x_y hne
  have cyx : ∀ u v, Commute (R.y a u) (R.x b v) := fun u v =>
    (R.commute_x_y (Ne.symm hne) v u).symm
  have cyy : ∀ u v, Commute (R.y a u) (R.y b v) := R.commute_y_y hcm
  have cw : ∀ u1 u2 u3 v1 v2 v3, Commute (R.x a u1 * R.y a u2 * R.x a u3)
      (R.x b v1 * R.y b v2 * R.x b v3) := fun u1 u2 u3 v1 v2 v3 => by
    refine ((Commute.mul_left (Commute.mul_left ?_ ?_) ?_))
    · exact ((cxx _ _).mul_right (cxy _ _)).mul_right (cxx _ _)
    · exact ((cyx _ _).mul_right (cyy _ _)).mul_right (cyx _ _)
    · exact ((cxx _ _).mul_right (cxy _ _)).mul_right (cxx _ _)
  have hgen : ∀ u1 u2 u3 v1 v2 v3, R.x a u1 * R.x b v1 * (R.y a u2 * R.y b v2) *
      (R.x a u3 * R.x b v3) = R.x a u1 * R.y a u2 * R.x a u3 *
        (R.x b v1 * R.y b v2 * R.x b v3) := fun u1 u2 u3 v1 v2 v3 => by
    simp only [mul_assoc]
    rw [← mul_assoc (R.x b v1) (R.y a u2), ← (cyx u2 v1).eq, mul_assoc (R.y a u2),
      ← mul_assoc (R.y b v2) (R.x a u3), ← (cxy u3 v2).eq, mul_assoc (R.x a u3),
      ← mul_assoc (R.x b v1) (R.x a u3), ← (cxx u3 v1).eq, mul_assoc (R.x a u3)]
  have key : R.h a c * R.h b c = R.pairX σ a b c * R.pairY σ a b (-((c⁻¹ : Kˣ) : K)) *
      R.pairX σ a b c * (R.pairX σ a b 1 * R.pairY σ a b (-1) * R.pairX σ a b 1)⁻¹ := by
    simp only [pairX, pairY, hc, hc', map_one, map_neg]
    rw [hgen, hgen, R.h_eq a c, R.h_eq b c, weyl, weyl, mul_inv_rev]
    set α := R.x a c * R.y a (-((c⁻¹ : Kˣ) : K)) * R.x a c
    set β := R.x b c * R.y b (-((c⁻¹ : Kˣ) : K)) * R.x b c
    set α1 := R.x a 1 * R.y a (-1) * R.x a 1
    set β1 := R.x b 1 * R.y b (-1) * R.x b 1
    have h3 : Commute α1⁻¹ (β * β1⁻¹) := ((cw _ _ _ _ _ _).inv_left).mul_right
      ((cw _ _ _ _ _ _).inv_left.inv_right)
    calc α * α1⁻¹ * (β * β1⁻¹) = α * (α1⁻¹ * (β * β1⁻¹)) := by group
      _ = α * ((β * β1⁻¹) * α1⁻¹) := by rw [h3.eq]
      _ = α * β * (β1⁻¹ * α1⁻¹) := by group
  rw [key]
  have h1 : σ (σ (1 : K)) = 1 := by simp
  have hm1 : σ (σ (-1 : K)) = -1 := by simp
  have hcc : σ (σ (c : K)) = c := by rw [hc, hc]
  have hcc' : σ (σ (-((c⁻¹ : Kˣ) : K))) = -((c⁻¹ : Kˣ) : K) := by rw [hc', hc']
  exact D.mul_mem (D.mul_mem (D.mul_mem (hX _ hcc) (hY _ hcc')) (hX _ hcc))
    (D.inv_mem (D.mul_mem (D.mul_mem (hX _ h1) (hY _ hm1)) (hX _ h1)))

end Twisted

structure IsDisjointPair (a b : ι) : Prop where
  EE : R.E a * R.E b = 0
  EE' : R.E b * R.E a = 0
  EF : R.E a * R.F b = 0
  FE : R.F b * R.E a = 0
  EF' : R.E b * R.F a = 0
  FE' : R.F a * R.E b = 0
  FF : R.F a * R.F b = 0
  FF' : R.F b * R.F a = 0

variable {R} {σ : K →+* K}

theorem mat_x_mul_x {a b : ι} (hp : R.IsDisjointPair a b) (u v : K) :
    R.mat (R.x a u * R.x b v) = 1 + u • R.E a + v • R.E b := by
  rw [mat_mul, mat_x, mat_x, SqZeroPair.φ_upper, SqZeroPair.φ_upper]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hp.EE,
    smul_zero, add_zero]

theorem mat_y_mul_y {a b : ι} (hp : R.IsDisjointPair a b) (u v : K) :
    R.mat (R.y a u * R.y b v) = 1 + u • R.F a + v • R.F b := by
  rw [mat_mul, mat_y, mat_y, SqZeroPair.φ_lower, SqZeroPair.φ_lower]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hp.FF,
    smul_zero, add_zero]

theorem E_mul_F_ne_zero (a : ι) : R.E a * R.F a ≠ 0 := fun h =>
  R.E_ne_zero a (by rw [← (R.sqZero a).efe, h, zero_mul])

theorem eq_zero_of_commute_pairX_pairY {a b : ι} (hp : R.IsDisjointPair a b) {u : K}
    (h : Commute (R.pairX σ a b u) (R.pairY σ a b 1)) : u = 0 := by
  have h' : R.x a u * R.x b (σ u) * (R.y a 1 * R.y b 1) =
      R.y a 1 * R.y b 1 * (R.x a u * R.x b (σ u)) := by
    have := h.eq
    simp only [pairX, pairY, map_one] at this
    exact this
  have hm : R.mat (R.x a u * R.x b (σ u)) * R.mat (R.y a 1 * R.y b 1) =
      R.mat (R.y a 1 * R.y b 1) * R.mat (R.x a u * R.x b (σ u)) := by
    rw [← mat_mul, ← mat_mul, h']
  rw [mat_x_mul_x hp, mat_y_mul_y hp, one_smul, one_smul] at hm
  have h1 : u • (R.E a * R.F a - R.F a * R.E a) + σ u • (R.E b * R.F b - R.F b * R.E b) = 0 := by
    have e : (1 + u • R.E a + σ u • R.E b) * (1 + R.F a + R.F b) -
        (1 + R.F a + R.F b) * (1 + u • R.E a + σ u • R.E b) =
        u • (R.E a * R.F a - R.F a * R.E a) + σ u • (R.E b * R.F b - R.F b * R.E b) +
          u • (R.E a * R.F b - R.F b * R.E a) + σ u • (R.E b * R.F a - R.F a * R.E b) := by
      simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
        smul_add]
      abel
    rw [hm, sub_self, hp.EF, hp.FE, hp.EF', hp.FE', sub_self] at e
    simp only [smul_zero, add_zero] at e
    exact e.symm
  have h2 : R.E a * R.F a * (u • (R.E a * R.F a - R.F a * R.E a) +
      σ u • (R.E b * R.F b - R.F b * R.E b)) = u • (R.E a * R.F a) := by
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_sub, mul_sub]
    have e1 : R.E a * R.F a * (R.E a * R.F a) = R.E a * R.F a := by
      rw [← mul_assoc, (R.sqZero a).efe]
    have e2 : R.E a * R.F a * (R.F a * R.E a) = 0 := by
      rw [mul_assoc, ← mul_assoc (R.F a) (R.F a), (R.sqZero a).ff, zero_mul, mul_zero]
    have e3 : R.E a * R.F a * (R.E b * R.F b) = 0 := by
      rw [mul_assoc, ← mul_assoc (R.F a) (R.E b), hp.FE', zero_mul, mul_zero]
    have e4 : R.E a * R.F a * (R.F b * R.E b) = 0 := by
      rw [mul_assoc, ← mul_assoc (R.F a) (R.F b), hp.FF, zero_mul, mul_zero]
    rw [e1, e2, e3, e4, sub_zero, sub_self, smul_zero, add_zero]
  rw [h1, mul_zero] at h2
  rcases smul_eq_zero.mp h2.symm with hu | hAC
  · exact hu
  · exact absurd hAC (E_mul_F_ne_zero a)

theorem char_eq_one_of_commute_pairX {a b : ι} (hp : R.IsDisjointPair a b) {t : ι → Kˣ}
    (h : Commute (R.torus t) (R.pairX σ a b 1)) : (∏ k, t k ^ R.CM k a) = 1 := by
  have h1 : R.torus t * R.pairX σ a b 1 * (R.torus t)⁻¹ = R.pairX σ a b 1 := by
    rw [h.eq, mul_inv_cancel_right]
  have e : R.torus t * R.pairX σ a b 1 * (R.torus t)⁻¹ =
      (R.torus t * R.x a 1 * (R.torus t)⁻¹) * (R.torus t * R.x b (σ 1) * (R.torus t)⁻¹) := by
    simp only [pairX]
    group
  rw [e, torus_conj_x, torus_conj_x, pairX] at h1
  have hm := congrArg R.mat h1
  rw [mat_x_mul_x hp, mat_x_mul_x hp] at hm
  have h3 := congrArg (· * R.F a) hm
  simp only [add_mul, one_mul, mul_one, smul_mul_assoc, hp.EF', smul_zero, add_zero,
    one_smul] at h3
  have h4 : (((∏ k, t k ^ R.CM k a : Kˣ) : K) - 1) • (R.E a * R.F a) = 0 := by
    rw [sub_smul, one_smul, add_left_cancel h3, sub_self]
  rcases smul_eq_zero.mp h4 with h5 | h5
  · exact Units.ext (sub_eq_zero.mp h5)
  · exact absurd h5 (E_mul_F_ne_zero a)

end RootData

end CFSG.RankThree.PartTwo.Census.Spin
