module

public import CFSG.Milestones.ASVolI.B4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Quasithin.EmptyFaithful.SzN2Quot
public import CFSG.Quasithin.Vol2.Ch11SecB414MF
public import CFSG.Quasithin.Vol2.Ch11SecB414MS
public import CFSG.Quasithin.Vol2.Ch11SecB414N
public import CFSG.Quasithin.Vol2.Ch11SecB414PA
public import CFSG.Quasithin.Vol2.Ch11SecB414PC
public import CFSG.Quasithin.Vol2.Ch11SecB414PD

public section

namespace CFSG.ASVolI

open CFSG.Open

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

@[expose] def burnsideB4h_pr : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

section Generic

variable {K : Type} [Field K]

@[expose] def burnsideB4h_pl (u v : Fin 4 → K) : Fin 6 → K := fun s =>
  u (burnsideB4h_pr s).1 * v (burnsideB4h_pr s).2 - u (burnsideB4h_pr s).2 * v (burnsideB4h_pr s).1

@[expose] noncomputable def burnsideB4h_coords (x : wedgeSpace K) : Fin 6 → K :=
  fun s => plk (burnsideB4h_pr s).1 (burnsideB4h_pr s).2 x

theorem burnsideB4h_coords_wedge (u v : Fin 4 → K) :
    burnsideB4h_coords (wedge u v) = burnsideB4h_pl u v := by
  ext s
  simp [burnsideB4h_coords, plk_wedge, burnsideB4h_pl]

theorem burnsideB4h_coords_injective :
    Function.Injective (burnsideB4h_coords : wedgeSpace K → Fin 6 → K) := by
  intro x y h
  have h' : ∀ s, plk (burnsideB4h_pr s).1 (burnsideB4h_pr s).2 x =
      plk (burnsideB4h_pr s).1 (burnsideB4h_pr s).2 y := fun s => congrFun h s
  exact ext_plk (h' 0) (h' 1) (h' 2) (h' 3) (h' 4) (h' 5)

theorem burnsideB4h_coords_zero : burnsideB4h_coords (0 : wedgeSpace K) = 0 := by
  ext s
  simp [burnsideB4h_coords]

@[expose] def burnsideB4h_cm (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun r s =>
    M (burnsideB4h_pr r).1 (burnsideB4h_pr s).1 * M (burnsideB4h_pr r).2 (burnsideB4h_pr s).2 -
      M (burnsideB4h_pr r).1 (burnsideB4h_pr s).2 * M (burnsideB4h_pr r).2 (burnsideB4h_pr s).1

theorem burnsideB4h_pl_mulVec (M : Matrix (Fin 4) (Fin 4) K) (u v : Fin 4 → K) :
    burnsideB4h_pl (M.mulVec u) (M.mulVec v) = (burnsideB4h_cm M).mulVec (burnsideB4h_pl u v) := by
  ext r
  fin_cases r <;>
    simp [burnsideB4h_pl, burnsideB4h_cm, burnsideB4h_pr, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem burnsideB4h_coords_wedgeAct (M : Matrix (Fin 4) (Fin 4) K) (x : wedgeSpace K) :
    burnsideB4h_coords (wedgeAct M x) = (burnsideB4h_cm M).mulVec (burnsideB4h_coords x) := by
  ext r
  have key : plk (burnsideB4h_pr r).1 (burnsideB4h_pr r).2 ∘ₗ wedgeAct M =
      ∑ s, burnsideB4h_cm M r s • plk (burnsideB4h_pr s).1 (burnsideB4h_pr s).2 :=
    linearMap_ext_wedge fun v w => by
      have h := congrFun (burnsideB4h_pl_mulVec M v w) r
      simp only [LinearMap.comp_apply, wedgeAct_wedge, LinearMap.sum_apply, LinearMap.smul_apply,
        plk_wedge, smul_eq_mul]
      simpa [burnsideB4h_pl, Matrix.mulVec, dotProduct] using h
  have := LinearMap.congr_fun key x
  simpa [burnsideB4h_coords, Matrix.mulVec, dotProduct] using this

end Generic

@[expose] def burnsideB4h_Q (w : Fin 6 → ZMod 2) : ZMod 2 := w 0 * w 5 + w 1 * w 4 + w 2 * w 3

@[expose] def burnsideB4h_Om : Finset (Fin 6 → ZMod 2) :=
  Finset.univ.filter fun w => w ≠ 0 ∧ burnsideB4h_Q w = 0

theorem burnsideB4h_Om_card : burnsideB4h_Om.card = 35 := by
  unfold burnsideB4h_Om burnsideB4h_Q
  decide +kernel

theorem burnsideB4h_pl_Q : ∀ u v : Fin 4 → ZMod 2, burnsideB4h_pl u v ≠ 0 →
    burnsideB4h_Q (burnsideB4h_pl u v) = 0 := by
  unfold burnsideB4h_Q burnsideB4h_pl burnsideB4h_pr
  decide +kernel

theorem burnsideB4h_Om_exists : ∀ w : Fin 6 → ZMod 2, w ≠ 0 → burnsideB4h_Q w = 0 →
    ∃ u v : Fin 4 → ZMod 2, burnsideB4h_pl u v = w := by
  unfold burnsideB4h_Q burnsideB4h_pl burnsideB4h_pr
  decide +kernel

@[expose] def burnsideB4h_utriM (a : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, a 0, a 1, a 2; 0, 1, a 3, a 4; 0, 0, 1, a 5; 0, 0, 0, 1]

@[expose] def burnsideB4h_utriInv (a : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![a 0, a 1 + a 0 * a 3, a 2 + a 0 * a 4 + a 1 * a 5 + a 0 * a 3 * a 5, a 3,
    a 4 + a 3 * a 5, a 5]

@[expose] def burnsideB4h_utriMul (a b : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![a 0 + b 0, a 1 + a 0 * b 3 + b 1, a 2 + a 0 * b 4 + a 1 * b 5 + b 2, a 3 + b 3,
    a 4 + a 3 * b 5 + b 4, a 5 + b 5]

theorem burnsideB4h_utriM_mul : ∀ a b : Fin 6 → ZMod 2,
    burnsideB4h_utriM a * burnsideB4h_utriM b = burnsideB4h_utriM (burnsideB4h_utriMul a b) := by
  unfold burnsideB4h_utriM burnsideB4h_utriMul
  decide +kernel

theorem burnsideB4h_utriM_inv : ∀ a : Fin 6 → ZMod 2,
    burnsideB4h_utriM a * burnsideB4h_utriM (burnsideB4h_utriInv a) = 1 ∧
    burnsideB4h_utriM (burnsideB4h_utriInv a) * burnsideB4h_utriM a = 1 := by
  unfold burnsideB4h_utriM burnsideB4h_utriInv
  decide +kernel

theorem burnsideB4h_fix_coords : ∀ w : Fin 6 → ZMod 2,
    (∀ s : Fin 6, (burnsideB4h_cm (burnsideB4h_utriM (Pi.single s 1))).mulVec w = w) →
    w = 0 ∨ w = Pi.single 0 1 := by
  unfold burnsideB4h_cm burnsideB4h_utriM burnsideB4h_pr
  decide +kernel

@[expose] def burnsideB4h_lead (w : Fin 6 → ZMod 2) : Fin 6 :=
  if w 5 ≠ 0 then 5 else if w 4 ≠ 0 then 4 else if w 3 ≠ 0 then 3 else
    if w 2 ≠ 0 then 2 else if w 1 ≠ 0 then 1 else 0

@[expose] def burnsideB4h_sz : Fin 6 → ℕ := ![1, 2, 4, 4, 8, 16]

theorem burnsideB4h_cell_card : ∀ c : Fin 6,
    (burnsideB4h_Om.filter fun w => burnsideB4h_lead w = c).card = burnsideB4h_sz c := by
  unfold burnsideB4h_Om burnsideB4h_Q burnsideB4h_lead burnsideB4h_sz
  decide +kernel

theorem burnsideB4h_cell_orbit : ∀ w ∈ burnsideB4h_Om, ∀ w' ∈ burnsideB4h_Om,
    burnsideB4h_lead w' = burnsideB4h_lead w →
    ∃ a : Fin 6 → ZMod 2, (burnsideB4h_cm (burnsideB4h_utriM a)).mulVec w = w' := by
  unfold burnsideB4h_Om burnsideB4h_Q burnsideB4h_lead burnsideB4h_cm burnsideB4h_utriM
    burnsideB4h_pr
  decide +kernel

theorem burnsideB4h_C2_perm : ∀ a : Fin 6 → ZMod 2,
    ((burnsideB4h_cm (burnsideB4h_utriM a)).mulVec (Pi.single 1 1) = Pi.single 1 1 ∨
        (burnsideB4h_cm (burnsideB4h_utriM a)).mulVec (Pi.single 1 1) =
          Pi.single 1 1 + Pi.single 0 1) ∧
    ((burnsideB4h_cm (burnsideB4h_utriM a)).mulVec (Pi.single 1 1 + Pi.single 0 1) = Pi.single 1 1 ∨
        (burnsideB4h_cm (burnsideB4h_utriM a)).mulVec (Pi.single 1 1 + Pi.single 0 1) =
          Pi.single 1 1 + Pi.single 0 1) := by
  unfold burnsideB4h_cm burnsideB4h_utriM burnsideB4h_pr
  decide +kernel

end

section

@[expose] def burnsideB4h_utriG (a : Fin 6 → ZMod 2) : GL (Fin 4) (ZMod 2) where
  val := burnsideB4h_utriM a
  inv := burnsideB4h_utriM (burnsideB4h_utriInv a)
  val_inv := (burnsideB4h_utriM_inv a).1
  inv_val := (burnsideB4h_utriM_inv a).2

theorem burnsideB4h_utriG_mul (a b : Fin 6 → ZMod 2) :
    burnsideB4h_utriG a * burnsideB4h_utriG b = burnsideB4h_utriG (burnsideB4h_utriMul a b) :=
  Units.ext (burnsideB4h_utriM_mul a b)

theorem burnsideB4h_utriG_inv (a : Fin 6 → ZMod 2) :
    (burnsideB4h_utriG a)⁻¹ = burnsideB4h_utriG (burnsideB4h_utriInv a) := Units.ext rfl

theorem burnsideB4h_utriM_zero : burnsideB4h_utriM 0 = 1 := by
  unfold burnsideB4h_utriM
  decide +kernel

theorem burnsideB4h_utriG_injective : Function.Injective burnsideB4h_utriG := by
  intro a b h
  have h' : burnsideB4h_utriM a = burnsideB4h_utriM b := congrArg Units.val h
  have e : ∀ i j, burnsideB4h_utriM a i j = burnsideB4h_utriM b i j := fun i j => by rw [h']
  ext s
  fin_cases s
  · simpa [burnsideB4h_utriM] using e 0 1
  · simpa [burnsideB4h_utriM] using e 0 2
  · simpa [burnsideB4h_utriM] using e 0 3
  · simpa [burnsideB4h_utriM] using e 1 2
  · simpa [burnsideB4h_utriM] using e 1 3
  · simpa [burnsideB4h_utriM] using e 2 3

@[expose] def burnsideB4h_U : Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := Set.range burnsideB4h_utriG
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (burnsideB4h_utriG_mul a b).symm⟩
  one_mem' := ⟨0, Units.ext burnsideB4h_utriM_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (burnsideB4h_utriG_inv a).symm⟩

theorem burnsideB4h_utriG_mem (a : Fin 6 → ZMod 2) : burnsideB4h_utriG a ∈ burnsideB4h_U :=
  ⟨a, rfl⟩

theorem burnsideB4h_U_card : Nat.card burnsideB4h_U = 64 := by
  have e : (Fin 6 → ZMod 2) ≃ burnsideB4h_U :=
    Equiv.ofBijective (fun a => ⟨burnsideB4h_utriG a, burnsideB4h_utriG_mem a⟩)
      ⟨fun a b h => burnsideB4h_utriG_injective (congrArg Subtype.val h),
        fun ⟨g, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩
  rw [← Nat.card_congr e]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]

theorem burnsideB4h_GL_card : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_four, ZMod.card]

theorem burnsideB4h_U_index : burnsideB4h_U.index = 315 := by
  have h := Subgroup.card_mul_index burnsideB4h_U
  rw [burnsideB4h_U_card, burnsideB4h_GL_card] at h
  omega

theorem burnsideB4h_exists_conj_U {T₀ : Subgroup (GL (Fin 4) (ZMod 2))} (hp : IsPGroup 2 T₀)
    (hidx : ¬ 2 ∣ T₀.index) :
    ∃ c : GL (Fin 4) (ZMod 2), ∀ g, g ∈ T₀ ↔ ∃ u ∈ burnsideB4h_U, c * u * c⁻¹ = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 burnsideB4h_U := IsPGroup.of_card (n := 6) (by
    rw [burnsideB4h_U_card]; norm_num)
  have hUi : ¬ 2 ∣ burnsideB4h_U.index := by
    rw [burnsideB4h_U_index]; norm_num
  let P : Sylow 2 (GL (Fin 4) (ZMod 2)) := hp.toSylow hidx
  let Q : Sylow 2 (GL (Fin 4) (ZMod 2)) := hUp.toSylow hUi
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (GL (Fin 4) (ZMod 2)) Q P
  refine ⟨c, fun g => ?_⟩
  have h1 : g ∈ (P : Subgroup _) ↔ g ∈ ((c • Q : Sylow 2 _) : Subgroup _) := by rw [hc]
  have h2 : g ∈ ((c • Q : Sylow 2 _) : Subgroup _) ↔ ∃ u ∈ (Q : Subgroup _), MulAut.conj c u = g := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.smul_def]
  have hP : (P : Subgroup _) = T₀ := rfl
  have hQ : (Q : Subgroup _) = burnsideB4h_U := rfl
  rw [← hP, h1, h2, hQ]
  simp [MulAut.conj_apply]

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

section TwoElt

variable {K : Type} [Field K]

theorem burnsideB4h_neg_one_eq (hK : ∀ s : K, s = 0 ∨ s = 1) : (-1 : K) = 1 := by
  rcases hK (-1) with h | h
  · exact absurd (neg_eq_zero.1 h) one_ne_zero
  · exact h

theorem burnsideB4h_neg_self (hK : ∀ s : K, s = 0 ∨ s = 1) (b : Fin 4 → K) : -b = b := by
  funext i
  rcases hK (b i) with h | h <;> simp [h, burnsideB4h_neg_one_eq hK]

theorem burnsideB4h_eq_of_add_eq_zero (hK : ∀ s : K, s = 0 ∨ s = 1) {a b : Fin 4 → K}
    (h : a + b = 0) : a = b := by
  have := eq_neg_of_add_eq_zero_left h
  rw [this, burnsideB4h_neg_self hK]

theorem burnsideB4h_indep_pair (hK : ∀ s : K, s = 0 ∨ s = 1) {a b : Fin 4 → K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a ≠ b) : LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff' ha]
  intro s
  rcases hK s with h | h
  · subst h
    simpa using hb.symm
  · subst h
    simpa using hab

@[expose] def burnsideB4h_Indep3 (a b c : Fin 4 → K) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b ≠ c

theorem burnsideB4h_indep3 (hK : ∀ s : K, s = 0 ∨ s = 1) {a b c : Fin 4 → K}
    (h : burnsideB4h_Indep3 a b c) : LinearIndependent K ![a, b, c] := by
  obtain ⟨ha, hb, hc, hab, hac, hbc, habc⟩ := h
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hg
  have key : ∀ x y z : K, x • a + y • b + z • c = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z hxyz
    rcases hK x with rfl | rfl <;> rcases hK y with rfl | rfl <;> rcases hK z with rfl | rfl <;>
      simp at hxyz ⊢
    · exact hc hxyz
    · exact hb hxyz
    · exact hbc (burnsideB4h_eq_of_add_eq_zero hK hxyz)
    · exact ha hxyz
    · exact hac (burnsideB4h_eq_of_add_eq_zero hK hxyz)
    · exact hab (burnsideB4h_eq_of_add_eq_zero hK hxyz)
    · apply habc
      exact burnsideB4h_eq_of_add_eq_zero hK hxyz
  obtain ⟨h0, h1, h2⟩ := key _ _ _ hg
  fin_cases i <;> assumption

theorem burnsideB4h_extend_triple {a b c : Fin 4 → K} (h : LinearIndependent K ![a, b, c]) :
    ∃ d, LinearIndependent K ![a, b, c, d] := by
  obtain ⟨d, hd⟩ := exists_linearIndependent_snoc_of_lt_finrank (v := ![a, b, c]) h (by simp)
  refine ⟨d, ?_⟩
  convert hd using 1
  funext i
  fin_cases i <;> rfl

theorem burnsideB4h_extend_pair {a b : Fin 4 → K} (h : LinearIndependent K ![a, b]) :
    ∃ c, ∃ d, LinearIndependent K ![a, b, c, d] := by
  obtain ⟨c, hc⟩ := exists_linearIndependent_snoc_of_lt_finrank (v := ![a, b]) h (by simp)
  have hc' : LinearIndependent K ![a, b, c] := by
    convert hc using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨d, hd⟩ := burnsideB4h_extend_triple hc'
  exact ⟨c, d, hd⟩

theorem burnsideB4h_exists_gl4 {a b c d : Fin 4 → K} (h : LinearIndependent K ![a, b, c, d]) :
    ∃ g : GL (Fin 4) K, g.1 *ᵥ stdVec 0 = a ∧ g.1 *ᵥ stdVec 1 = b ∧
      g.1 *ᵥ stdVec 2 = c ∧ g.1 *ᵥ stdVec 3 = d := by
  let A : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => ![a, b, c, d] j i
  have hcol : A.col = ![a, b, c, d] := by
    funext j i
    rfl
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact h
  refine ⟨hA.unit, ?_, ?_, ?_, ?_⟩ <;>
    (funext i; simp [A, mulVec_stdVec, IsUnit.unit_spec])

theorem burnsideB4h_exists_gl_pair (hK : ∀ s : K, s = 0 ∨ s = 1) {a b : Fin 4 → K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ g : GL (Fin 4) K, g.1 *ᵥ stdVec 0 = a ∧ g.1 *ᵥ stdVec 1 = b := by
  obtain ⟨c, d, h⟩ := burnsideB4h_extend_pair (burnsideB4h_indep_pair hK ha hb hab)
  obtain ⟨g, h0, h1, -, -⟩ := burnsideB4h_exists_gl4 h
  exact ⟨g, h0, h1⟩

theorem burnsideB4h_exists_gl_triple (hK : ∀ s : K, s = 0 ∨ s = 1) {a b c : Fin 4 → K}
    (h : burnsideB4h_Indep3 a b c) :
    ∃ g : GL (Fin 4) K, g.1 *ᵥ stdVec 0 = a ∧ g.1 *ᵥ stdVec 1 = b ∧ g.1 *ᵥ stdVec 2 = c := by
  obtain ⟨d, hd⟩ := burnsideB4h_extend_triple (burnsideB4h_indep3 hK h)
  obtain ⟨g, h0, h1, h2, -⟩ := burnsideB4h_exists_gl4 hd
  exact ⟨g, h0, h1, h2⟩

end TwoElt

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_pl_ne_zero_iff : ∀ u v : Fin 4 → ZMod 2,
    (u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v) ↔ burnsideB4h_pl u v ≠ 0 := by
  unfold burnsideB4h_pl burnsideB4h_pr
  decide +kernel

theorem burnsideB4h_ZMod2 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide

theorem burnsideB4h_wedgeAct_one {K : Type} [Field K] :
    wedgeAct (1 : Matrix (Fin 4) (Fin 4) K) = LinearMap.id := by
  unfold wedgeAct
  rw [Matrix.toLin'_one, exteriorPower.map_id]

theorem burnsideB4h_wedgeAct_mul {K : Type} [Field K] (M N : Matrix (Fin 4) (Fin 4) K) :
    wedgeAct (M * N) = (wedgeAct M).comp (wedgeAct N) := by
  unfold wedgeAct
  rw [Matrix.toLin'_mul, exteriorPower.map_comp]

@[expose, instance_reducible] noncomputable def burnsideB4h_wact :
    MulAction (GL (Fin 4) (ZMod 2)) (wedgeSpace (ZMod 2)) where
  smul g w := wedgeAct g.1 w
  one_smul w := by
    show wedgeAct (1 : GL (Fin 4) (ZMod 2)).1 w = w
    rw [Units.val_one, burnsideB4h_wedgeAct_one]
    rfl
  mul_smul g h w := by
    show wedgeAct (g * h).1 w = wedgeAct g.1 (wedgeAct h.1 w)
    rw [Units.val_mul, burnsideB4h_wedgeAct_mul]
    rfl

@[expose] noncomputable def burnsideB4h_wx0 : wedgeSpace (ZMod 2) :=
  wedge (stdVec 0) (stdVec 1)

@[expose] def burnsideB4h_Orb : Set (wedgeSpace (ZMod 2)) :=
  {w | ∃ g : GL (Fin 4) (ZMod 2), wedgeAct g.1 burnsideB4h_wx0 = w}

theorem burnsideB4h_mulVec_ne_zero {K : Type} [Field K] (g : GL (Fin 4) K) {v : Fin 4 → K}
    (hv : v ≠ 0) : g.1.mulVec v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (g⁻¹).1.mulVec h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec, Matrix.mulVec_zero] at this

theorem burnsideB4h_mulVec_inj {K : Type} [Field K] (g : GL (Fin 4) K) {u v : Fin 4 → K}
    (h : g.1.mulVec u = g.1.mulVec v) : u = v := by
  have := congrArg (g⁻¹).1.mulVec h
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at this

theorem burnsideB4h_stdVec_ne_zero {K : Type} [Field K] (i : Fin 4) : (stdVec i : Fin 4 → K) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [stdVec] at this

theorem burnsideB4h_stdVec_ne {K : Type} [Field K] {i j : Fin 4} (hij : i ≠ j) :
    (stdVec i : Fin 4 → K) ≠ stdVec j := by
  intro h
  have := congrFun h i
  simp [stdVec, Pi.single_apply, hij] at this

theorem burnsideB4h_Orb_iff (w : wedgeSpace (ZMod 2)) :
    w ∈ burnsideB4h_Orb ↔
      ∃ a b : Fin 4 → ZMod 2, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ wedge a b = w := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g.1.mulVec (stdVec 0), g.1.mulVec (stdVec 1),
      burnsideB4h_mulVec_ne_zero g (burnsideB4h_stdVec_ne_zero 0),
      burnsideB4h_mulVec_ne_zero g (burnsideB4h_stdVec_ne_zero 1), ?_, ?_⟩
    · intro h
      exact burnsideB4h_stdVec_ne (by decide : (0 : Fin 4) ≠ 1) (burnsideB4h_mulVec_inj g h)
    · exact (wedgeAct_wedge _ _ _).symm
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain ⟨g, h0, h1⟩ := burnsideB4h_exists_gl_pair burnsideB4h_ZMod2 ha hb hab
    exact ⟨g, by rw [burnsideB4h_wx0, wedgeAct_wedge, h0, h1]⟩

theorem burnsideB4h_coords_Orb_mem {w : wedgeSpace (ZMod 2)} (hw : w ∈ burnsideB4h_Orb) :
    burnsideB4h_coords w ∈ burnsideB4h_Om := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := (burnsideB4h_Orb_iff w).1 hw
  rw [burnsideB4h_coords_wedge]
  have hne := (burnsideB4h_pl_ne_zero_iff a b).1 ⟨ha, hb, hab⟩
  simp only [burnsideB4h_Om, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hne, burnsideB4h_pl_Q a b hne⟩

theorem burnsideB4h_Om_coords_Orb {ω : Fin 6 → ZMod 2} (hω : ω ∈ burnsideB4h_Om) :
    ∃ w ∈ burnsideB4h_Orb, burnsideB4h_coords w = ω := by
  simp only [burnsideB4h_Om, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  obtain ⟨u, v, huv⟩ := burnsideB4h_Om_exists ω hω.1 hω.2
  have hne : burnsideB4h_pl u v ≠ 0 := by rw [huv]; exact hω.1
  obtain ⟨hu, hv, huv'⟩ := (burnsideB4h_pl_ne_zero_iff u v).2 hne
  exact ⟨wedge u v, (burnsideB4h_Orb_iff _).2 ⟨u, v, hu, hv, huv', rfl⟩,
    by rw [burnsideB4h_coords_wedge, huv]⟩

theorem burnsideB4h_Orb_card : Nat.card burnsideB4h_Orb = 35 := by
  have e : burnsideB4h_Orb ≃ (burnsideB4h_Om : Set (Fin 6 → ZMod 2)) :=
    Equiv.ofBijective
      (fun w => ⟨burnsideB4h_coords w.1, by
        simpa using burnsideB4h_coords_Orb_mem w.2⟩)
      ⟨fun w w' h => Subtype.ext (burnsideB4h_coords_injective (congrArg Subtype.val h)),
        fun ⟨ω, hω⟩ => by
          obtain ⟨w, hw, hwω⟩ := burnsideB4h_Om_coords_Orb (by simpa using hω)
          exact ⟨⟨w, hw⟩, Subtype.ext hwω⟩⟩
  rw [Nat.card_congr e]
  simp [burnsideB4h_Om_card]

theorem burnsideB4h_card_orbit_mul_stab {G X : Type*} [Group G] [MulAction G X] (b : X) :
    Nat.card (MulAction.orbit G b) * Nat.card (MulAction.stabilizer G b) = Nat.card G := by
  rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G b)]

section StabSection

attribute [local instance] burnsideB4h_wact

theorem burnsideB4h_stab_card :
    Nat.card (MulAction.stabilizer (GL (Fin 4) (ZMod 2)) burnsideB4h_wx0) = 576 := by
  have h := burnsideB4h_card_orbit_mul_stab (G := GL (Fin 4) (ZMod 2)) burnsideB4h_wx0
  have horb : Nat.card (MulAction.orbit (GL (Fin 4) (ZMod 2)) burnsideB4h_wx0) = 35 := by
    rw [← burnsideB4h_Orb_card]
    rfl
  rw [horb, burnsideB4h_GL_card] at h
  omega

end StabSection

theorem burnsideB4h_exists_wedge_lift {K : Type} [Field K] {N : Type} [AddCommGroup N] [Module K N]
    (B : (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] N) (hB : ∀ x, B x x = 0) :
    ∃ θ : wedgeSpace K →ₗ[K] N, ∀ u v, θ (wedge u v) = B u v := by
  let A : (Fin 4 → K) [⋀^Fin 2]→ₗ[K] N :=
    { toFun := fun f => B (f 0) (f 1)
      map_update_add' := by
        intro _ f i x y
        fin_cases i <;> simp [Function.update]
      map_update_smul' := by
        intro _ f i c x
        fin_cases i <;> simp [Function.update]
      map_eq_zero_of_eq' := by
        intro f i j hij hne
        have h01 : f 0 = f 1 := by
          fin_cases i <;> fin_cases j <;> simp at hne hij ⊢ <;> first | exact hij | exact hij.symm
        show B (f 0) (f 1) = 0
        rw [← h01]
        exact hB _ }
  refine ⟨exteriorPower.alternatingMapLinearEquiv A, fun u v => ?_⟩
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti A ![u, v]

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_wedgeAct_mul_apply (g h : GL (Fin 4) (ZMod 2)) (w : wedgeSpace (ZMod 2)) :
    wedgeAct (g * h).1 w = wedgeAct g.1 (wedgeAct h.1 w) := by
  rw [Units.val_mul, burnsideB4h_wedgeAct_mul]
  rfl

theorem burnsideB4h_wedgeAct_one_apply (w : wedgeSpace (ZMod 2)) :
    wedgeAct (1 : GL (Fin 4) (ZMod 2)).1 w = w := by
  rw [Units.val_one, burnsideB4h_wedgeAct_one]
  rfl

theorem burnsideB4h_wedgeAct_inv_apply (g : GL (Fin 4) (ZMod 2)) (w : wedgeSpace (ZMod 2)) :
    wedgeAct g⁻¹.1 (wedgeAct g.1 w) = w := by
  rw [← burnsideB4h_wedgeAct_mul_apply, inv_mul_cancel, burnsideB4h_wedgeAct_one_apply]

theorem burnsideB4h_wedgeAct_injective (g : GL (Fin 4) (ZMod 2)) :
    Function.Injective (wedgeAct g.1 : wedgeSpace (ZMod 2) → wedgeSpace (ZMod 2)) := by
  intro w w' h
  have := congrArg (wedgeAct g⁻¹.1) h
  rwa [burnsideB4h_wedgeAct_inv_apply, burnsideB4h_wedgeAct_inv_apply] at this

section PhiSection

variable {V : Type} [CommGroup V] (ρ : GL (Fin 4) (ZMod 2) →* MulAut V) (v : V)

open Classical in
@[expose] noncomputable def burnsideB4h_phi (w : wedgeSpace (ZMod 2)) : V :=
  if h : ∃ s : GL (Fin 4) (ZMod 2), wedgeAct s.1 burnsideB4h_wx0 = w then
    ρ (Classical.choose h) v else 1

variable {ρ v}

theorem burnsideB4h_phi_apply (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
    wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0) (s : GL (Fin 4) (ZMod 2)) :
    burnsideB4h_phi ρ v (wedgeAct s.1 burnsideB4h_wx0) = ρ s v := by
  have h : ∃ s' : GL (Fin 4) (ZMod 2), wedgeAct s'.1 burnsideB4h_wx0 = wedgeAct s.1 burnsideB4h_wx0 :=
    ⟨s, rfl⟩
  unfold burnsideB4h_phi
  rw [dif_pos h]
  have hspec := Classical.choose_spec h
  set s' := Classical.choose h
  have h1 : wedgeAct (s⁻¹ * s').1 burnsideB4h_wx0 = burnsideB4h_wx0 := by
    rw [burnsideB4h_wedgeAct_mul_apply, hspec, burnsideB4h_wedgeAct_inv_apply]
  have h2 := (hstab (s⁻¹ * s')).2 h1
  rw [map_mul, MulAut.mul_apply] at h2
  calc ρ s' v = ρ s (ρ s⁻¹ (ρ s' v)) := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
    _ = ρ s v := by rw [h2]

theorem burnsideB4h_phi_off {w : wedgeSpace (ZMod 2)} (hw : w ∉ burnsideB4h_Orb) :
    burnsideB4h_phi ρ v w = 1 := by
  unfold burnsideB4h_phi
  rw [dif_neg]
  exact hw

theorem burnsideB4h_phi_equiv (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
    wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0) (g : GL (Fin 4) (ZMod 2))
    (w : wedgeSpace (ZMod 2)) :
    burnsideB4h_phi ρ v (wedgeAct g.1 w) = ρ g (burnsideB4h_phi ρ v w) := by
  by_cases hw : w ∈ burnsideB4h_Orb
  · obtain ⟨s, rfl⟩ := hw
    rw [← burnsideB4h_wedgeAct_mul_apply, burnsideB4h_phi_apply hstab,
      burnsideB4h_phi_apply hstab, map_mul, MulAut.mul_apply]
  · have hw' : wedgeAct g.1 w ∉ burnsideB4h_Orb := by
      rintro ⟨s, hs⟩
      apply hw
      refine ⟨g⁻¹ * s, ?_⟩
      rw [burnsideB4h_wedgeAct_mul_apply, hs, burnsideB4h_wedgeAct_inv_apply]
    rw [burnsideB4h_phi_off hw, burnsideB4h_phi_off hw', map_one]

theorem burnsideB4h_phi_inj (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
    wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0) {w w' : wedgeSpace (ZMod 2)}
    (hw : w ∈ burnsideB4h_Orb) (hw' : w' ∈ burnsideB4h_Orb)
    (h : burnsideB4h_phi ρ v w = burnsideB4h_phi ρ v w') : w = w' := by
  obtain ⟨s, rfl⟩ := hw
  obtain ⟨t, rfl⟩ := hw'
  rw [burnsideB4h_phi_apply hstab, burnsideB4h_phi_apply hstab] at h
  have h1 : ρ (s⁻¹ * t) v = v := by
    rw [map_mul, MulAut.mul_apply, ← h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have h2 := (hstab (s⁻¹ * t)).1 h1
  rw [burnsideB4h_wedgeAct_mul_apply] at h2
  have := congrArg (wedgeAct s.1) h2
  rw [← burnsideB4h_wedgeAct_mul_apply, mul_inv_cancel, burnsideB4h_wedgeAct_one_apply] at this
  exact this.symm

end PhiSection

end

section

theorem burnsideB4h_lead_single0 : burnsideB4h_lead (Pi.single 0 1 : Fin 6 → ZMod 2) = 0 := by
  unfold burnsideB4h_lead
  decide +kernel

theorem burnsideB4h_lead_single1 : burnsideB4h_lead (Pi.single 1 1 : Fin 6 → ZMod 2) = 1 := by
  unfold burnsideB4h_lead
  decide +kernel

theorem burnsideB4h_lead_e2c :
    burnsideB4h_lead (Pi.single 1 1 + Pi.single 0 1 : Fin 6 → ZMod 2) = 1 := by
  unfold burnsideB4h_lead
  decide +kernel

theorem burnsideB4h_single1_Om : (Pi.single 1 1 : Fin 6 → ZMod 2) ∈ burnsideB4h_Om := by
  unfold burnsideB4h_Om burnsideB4h_Q
  decide +kernel

theorem burnsideB4h_e2c_Om :
    (Pi.single 1 1 + Pi.single 0 1 : Fin 6 → ZMod 2) ∈ burnsideB4h_Om := by
  unfold burnsideB4h_Om burnsideB4h_Q
  decide +kernel

theorem burnsideB4h_cells (S : Finset (Fin 6 → ZMod 2)) (hS : S ⊆ burnsideB4h_Om)
    (h0 : (Pi.single 0 1 : Fin 6 → ZMod 2) ∈ S)
    (hinv : ∀ w ∈ S, ∀ a : Fin 6 → ZMod 2,
      (burnsideB4h_cm (burnsideB4h_utriM a)).mulVec w ∈ S)
    (hcard : S.card = 7) :
    ∀ w ∈ burnsideB4h_Om, burnsideB4h_lead w = 1 → w ∈ S := by
  classical
  have hfull : ∀ c : Fin 6, (∃ w ∈ S, burnsideB4h_lead w = c) → ∀ w' ∈ burnsideB4h_Om,
      burnsideB4h_lead w' = c → w' ∈ S := by
    rintro c ⟨w, hwS, hwc⟩ w' hw' hw'c
    obtain ⟨a, ha⟩ := burnsideB4h_cell_orbit w (hS hwS) w' hw' (by rw [hw'c, hwc])
    rw [← ha]
    exact hinv w hwS a
  have hm : ∀ c : Fin 6, (S.filter fun w => burnsideB4h_lead w = c).card = 0 ∨
      (S.filter fun w => burnsideB4h_lead w = c).card = burnsideB4h_sz c := by
    intro c
    by_cases h : ∃ w ∈ S, burnsideB4h_lead w = c
    · right
      rw [← burnsideB4h_cell_card c]
      congr 1
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hwS, hwc⟩
        exact ⟨hS hwS, hwc⟩
      · rintro ⟨hwO, hwc⟩
        exact ⟨hfull c h w hwO hwc, hwc⟩
    · left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw hwc
      exact h ⟨w, hw, hwc⟩
  have hsum : S.card = ∑ c : Fin 6, (S.filter fun w => burnsideB4h_lead w = c).card :=
    Finset.card_eq_sum_card_fiberwise (fun w _ => Finset.mem_univ _)
  have hm0 : (S.filter fun w => burnsideB4h_lead w = 0).card ≠ 0 := by
    rw [Finset.card_ne_zero]
    exact ⟨_, Finset.mem_filter.2 ⟨h0, burnsideB4h_lead_single0⟩⟩
  have hex : ∃ w ∈ S, burnsideB4h_lead w = 1 := by
    by_contra hno
    have hz : (S.filter fun w => burnsideB4h_lead w = 1).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw hwc
      exact hno ⟨w, hw, hwc⟩
    rw [Fin.sum_univ_six, hz] at hsum
    have e0 := hm 0
    have e2 := hm 2
    have e3 := hm 3
    have e4 := hm 4
    have e5 := hm 5
    have s0 : burnsideB4h_sz 0 = 1 := rfl
    have s2 : burnsideB4h_sz 2 = 4 := rfl
    have s3 : burnsideB4h_sz 3 = 4 := rfl
    have s4 : burnsideB4h_sz 4 = 8 := rfl
    have s5 : burnsideB4h_sz 5 = 16 := rfl
    omega
  exact hfull 1 hex

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_pl_e01 :
    burnsideB4h_pl (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1) = Pi.single 0 1 := by
  unfold burnsideB4h_pl burnsideB4h_pr stdVec
  decide +kernel

theorem burnsideB4h_pl_e02 :
    burnsideB4h_pl (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2) = Pi.single 1 1 := by
  unfold burnsideB4h_pl burnsideB4h_pr stdVec
  decide +kernel

theorem burnsideB4h_pl_e012 :
    burnsideB4h_pl (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2) =
      Pi.single 1 1 + Pi.single 0 1 := by
  unfold burnsideB4h_pl burnsideB4h_pr stdVec
  decide +kernel

theorem burnsideB4h_coords_x0 : burnsideB4h_coords burnsideB4h_wx0 = Pi.single 0 1 := by
  rw [burnsideB4h_wx0, burnsideB4h_coords_wedge, burnsideB4h_pl_e01]

section OrbitCount

attribute [local instance] burnsideB4h_wact

theorem burnsideB4h_O_card_ge {H₀ : Subgroup (GL (Fin 4) (ZMod 2))} (hH₀card : Nat.card H₀ = 1344) :
    7 ≤ Set.ncard {ω : wedgeSpace (ZMod 2) | ∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω} := by
  have h := burnsideB4h_card_orbit_mul_stab (G := ↥H₀) (X := wedgeSpace (ZMod 2)) burnsideB4h_wx0
  rw [hH₀card] at h
  have horb : Nat.card (MulAction.orbit ↥H₀ burnsideB4h_wx0) =
      Set.ncard {ω : wedgeSpace (ZMod 2) | ∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω} := by
    rw [← Nat.card_coe_set_eq]
    congr 2
    ext ω
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hdvd : Nat.card (MulAction.stabilizer ↥H₀ burnsideB4h_wx0) ∣ 576 := by
    rw [← burnsideB4h_stab_card]
    have hle : (MulAction.stabilizer ↥H₀ burnsideB4h_wx0).map H₀.subtype ≤
        MulAction.stabilizer (GL (Fin 4) (ZMod 2)) burnsideB4h_wx0 := by
      rintro _ ⟨h, hh, rfl⟩
      exact hh
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective H₀.subtype_injective] at this
  have hdvd' : Nat.card (MulAction.stabilizer ↥H₀ burnsideB4h_wx0) ∣ 1344 :=
    ⟨Nat.card (MulAction.orbit ↥H₀ burnsideB4h_wx0), by rw [← h]; ring⟩
  have hg : Nat.card (MulAction.stabilizer ↥H₀ burnsideB4h_wx0) ∣ 192 := by
    have := Nat.dvd_gcd hdvd' hdvd
    simpa using this
  have hle : Nat.card (MulAction.stabilizer ↥H₀ burnsideB4h_wx0) ≤ 192 :=
    Nat.le_of_dvd (by norm_num) hg
  rw [← horb]
  by_contra hlt
  push_neg at hlt
  have : Nat.card (MulAction.orbit ↥H₀ burnsideB4h_wx0) *
      Nat.card (MulAction.stabilizer ↥H₀ burnsideB4h_wx0) ≤ 6 * 192 := by
    apply Nat.mul_le_mul (by omega) hle
  omega

end OrbitCount

theorem burnsideB4h_phi_x0 {V : Type} [CommGroup V] {ρ : GL (Fin 4) (ZMod 2) →* MulAut V} {v : V}
    (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
      wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0) :
    burnsideB4h_phi ρ v burnsideB4h_wx0 = v := by
  have h := burnsideB4h_phi_apply hstab 1
  rw [burnsideB4h_wedgeAct_one_apply, map_one] at h
  exact h

theorem burnsideB4h_coords_mem_Om_of_Orb {ω : wedgeSpace (ZMod 2)} (h : ω ∈ burnsideB4h_Orb) :
    burnsideB4h_coords ω ≠ 0 := by
  have := burnsideB4h_coords_Orb_mem h
  simp only [burnsideB4h_Om, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this.1

theorem burnsideB4h_C2_mem {V : Type} [CommGroup V] [Finite V]
    {ρ : GL (Fin 4) (ZMod 2) →* MulAut V} {v : V} (hv1 : v ≠ 1)
    (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
      wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0)
    {H₀ : Subgroup (GL (Fin 4) (ZMod 2))} (hH₀card : Nat.card H₀ = 1344)
    (hUH : burnsideB4h_U ≤ H₀)
    (hY : Nat.card ↥(Subgroup.closure {y : V | ∃ h ∈ H₀, ρ h v = y}) = 8) :
    (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2) ∈
        {ω : wedgeSpace (ZMod 2) | ∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω}) ∧
      (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2) ∈
        {ω : wedgeSpace (ZMod 2) | ∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω}) ∧
      (∀ y ∈ Subgroup.closure {y : V | ∃ h ∈ H₀, ρ h v = y}, y ≠ 1 →
        ∃ ω ∈ {ω : wedgeSpace (ZMod 2) | ∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω},
          burnsideB4h_phi ρ v ω = y) := by
  classical
  set O : Set (wedgeSpace (ZMod 2)) := {ω | ∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω} with hO
  set orbH : Set V := {y | ∃ h ∈ H₀, ρ h v = y} with horbH
  set Y := Subgroup.closure orbH with hYdef
  have hOorb : ∀ ω ∈ O, ω ∈ burnsideB4h_Orb := fun ω ⟨h, _, e⟩ => ⟨h, e⟩
  have horbH_eq : orbH = burnsideB4h_phi ρ v '' O := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨wedgeAct h.1 burnsideB4h_wx0, ⟨h, hh, rfl⟩, burnsideB4h_phi_apply hstab h⟩
    · rintro ⟨ω, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨h, hh, (burnsideB4h_phi_apply hstab h).symm⟩
  have hinjO : Set.InjOn (burnsideB4h_phi ρ v) O := fun ω hω ω' hω' h =>
    burnsideB4h_phi_inj hstab (hOorb ω hω) (hOorb ω' hω') h
  have hncard : orbH.ncard = O.ncard := by
    rw [horbH_eq]
    exact hinjO.ncard_image
  have hO7le : 7 ≤ O.ncard := burnsideB4h_O_card_ge hH₀card
  have hsub : orbH ⊆ (Y : Set V) := Subgroup.subset_closure
  have h1 : (1 : V) ∉ orbH := by
    rintro ⟨h, _, h1⟩
    apply hv1
    exact (ρ h).injective (h1.trans (map_one (ρ h)).symm)
  have hins : insert (1 : V) orbH ⊆ (Y : Set V) := Set.insert_subset Y.one_mem hsub
  have hYcard : (Y : Set V).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hY
  have hcard_ins : (insert (1 : V) orbH).ncard = orbH.ncard + 1 :=
    Set.ncard_insert_of_notMem h1 (Set.toFinite _)
  have hle : (insert (1 : V) orbH).ncard ≤ 8 := (Set.ncard_le_ncard hins).trans hYcard.le
  have hO7 : O.ncard = 7 := by omega
  have hYeq : insert (1 : V) orbH = (Y : Set V) :=
    Set.eq_of_subset_of_ncard_le hins (by omega)
  have hYsub : ∀ y ∈ Y, y ≠ 1 → y ∈ orbH := by
    intro y hy hy1
    have : y ∈ insert (1 : V) orbH := by rw [hYeq]; exact hy
    rcases this with rfl | h
    · exact absurd rfl hy1
    · exact h
  have hOcoords : ∀ ω ∈ O, burnsideB4h_coords ω ∈ burnsideB4h_Om := fun ω hω =>
    burnsideB4h_coords_Orb_mem (hOorb ω hω)
  let S : Finset (Fin 6 → ZMod 2) := (Set.toFinite (burnsideB4h_coords '' O)).toFinset
  have hSmem : ∀ c, c ∈ S ↔ ∃ ω ∈ O, burnsideB4h_coords ω = c := by
    intro c
    simp [S]
  have hScard : S.card = 7 := by
    have : (burnsideB4h_coords '' O).ncard = S.card :=
      Set.ncard_eq_toFinset_card _ (Set.toFinite _)
    rw [← this, Set.ncard_image_of_injective O burnsideB4h_coords_injective, hO7]
  have hSOm : S ⊆ burnsideB4h_Om := by
    intro c hc
    obtain ⟨ω, hω, rfl⟩ := (hSmem c).1 hc
    exact hOcoords ω hω
  have hx0O : burnsideB4h_wx0 ∈ O := ⟨1, H₀.one_mem, by rw [burnsideB4h_wedgeAct_one_apply]⟩
  have h0S : (Pi.single 0 1 : Fin 6 → ZMod 2) ∈ S :=
    (hSmem _).2 ⟨burnsideB4h_wx0, hx0O, burnsideB4h_coords_x0⟩
  have hinv : ∀ c ∈ S, ∀ a : Fin 6 → ZMod 2,
      (burnsideB4h_cm (burnsideB4h_utriM a)).mulVec c ∈ S := by
    intro c hc a
    obtain ⟨ω, ⟨h, hh, rfl⟩, rfl⟩ := (hSmem c).1 hc
    refine (hSmem _).2 ⟨wedgeAct (burnsideB4h_utriG a).1 (wedgeAct h.1 burnsideB4h_wx0), ?_, ?_⟩
    · refine ⟨burnsideB4h_utriG a * h, H₀.mul_mem (hUH (burnsideB4h_utriG_mem a)) hh, ?_⟩
      rw [burnsideB4h_wedgeAct_mul_apply]
    · rw [burnsideB4h_coords_wedgeAct]
      rfl
  have hcells := burnsideB4h_cells S hSOm h0S hinv hScard
  have hC1 : wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2) ∈ O := by
    obtain ⟨ω, hω, hc⟩ := (hSmem _).1 (hcells _ burnsideB4h_single1_Om burnsideB4h_lead_single1)
    have : ω = wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2) := by
      apply burnsideB4h_coords_injective
      rw [hc, burnsideB4h_coords_wedge, burnsideB4h_pl_e02]
    rw [← this]
    exact hω
  have hC2 : wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2) ∈ O := by
    obtain ⟨ω, hω, hc⟩ := (hSmem _).1 (hcells _ burnsideB4h_e2c_Om burnsideB4h_lead_e2c)
    have : ω = wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2) := by
      apply burnsideB4h_coords_injective
      rw [hc, burnsideB4h_coords_wedge, burnsideB4h_pl_e012]
    rw [← this]
    exact hω
  refine ⟨hC1, hC2, ?_⟩
  intro y hy hy1
  have := hYsub y hy hy1
  rw [horbH_eq] at this
  obtain ⟨ω, hω, hωy⟩ := this
  exact ⟨ω, hω, hωy⟩

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_single_ne : (Pi.single 1 1 : Fin 6 → ZMod 2) ≠
    Pi.single 1 1 + Pi.single 0 1 := by
  decide +kernel

theorem burnsideB4h_R0 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {ρ : GL (Fin 4) (ZMod 2) →* MulAut V} {v : V} (hv1 : v ≠ 1)
    (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
      wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0)
    {H₀ : Subgroup (GL (Fin 4) (ZMod 2))} (hH₀card : Nat.card H₀ = 1344)
    (hUH : burnsideB4h_U ≤ H₀)
    (hY : Nat.card ↥(Subgroup.closure {y : V | ∃ h ∈ H₀, ρ h v = y}) = 8) :
    burnsideB4h_phi ρ v (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2)) *
      burnsideB4h_phi ρ v (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2)) = v := by
  classical
  obtain ⟨hC1, hC2, hYsub⟩ := burnsideB4h_C2_mem hv1 hstab hH₀card hUH hY
  have hOorb : ∀ ω : wedgeSpace (ZMod 2),
      (∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω) → ω ∈ burnsideB4h_Orb :=
    fun ω ⟨h, _, e⟩ => ⟨h, e⟩
  set ω₁ : wedgeSpace (ZMod 2) := wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2) with hω₁def
  set ω₂ : wedgeSpace (ZMod 2) := wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2)
    with hω₂def
  have hω₁ : ω₁ ∈ burnsideB4h_Orb := hOorb _ hC1
  have hω₂ : ω₂ ∈ burnsideB4h_Orb := hOorb _ hC2
  have hc₁ : burnsideB4h_coords ω₁ = Pi.single 1 1 := by
    rw [hω₁def, burnsideB4h_coords_wedge, burnsideB4h_pl_e02]
  have hc₂ : burnsideB4h_coords ω₂ = Pi.single 1 1 + Pi.single 0 1 := by
    rw [hω₂def, burnsideB4h_coords_wedge, burnsideB4h_pl_e012]
  have hne : ω₁ ≠ ω₂ := by
    intro h
    have := congrArg burnsideB4h_coords h
    rw [hc₁, hc₂] at this
    exact burnsideB4h_single_ne this
  have hφY : ∀ ω : wedgeSpace (ZMod 2), (∃ h ∈ H₀, wedgeAct h.1 burnsideB4h_wx0 = ω) →
      burnsideB4h_phi ρ v ω ∈ Subgroup.closure {y : V | ∃ h ∈ H₀, ρ h v = y} := by
    rintro _ ⟨h, hh, rfl⟩
    rw [burnsideB4h_phi_apply hstab h]
    exact Subgroup.subset_closure ⟨h, hh, rfl⟩
  have ha := hφY _ hC1
  have hb := hφY _ hC2
  have hsq : ∀ y : V, y * y = 1 := fun y => by
    have := hV y
    rwa [pow_two] at this
  have hab1 : burnsideB4h_phi ρ v ω₁ * burnsideB4h_phi ρ v ω₂ ≠ 1 := by
    intro h
    have h1 : burnsideB4h_phi ρ v ω₂ = (burnsideB4h_phi ρ v ω₁)⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : (burnsideB4h_phi ρ v ω₁)⁻¹ = burnsideB4h_phi ρ v ω₁ :=
      inv_eq_of_mul_eq_one_right (hsq _)
    exact hne (burnsideB4h_phi_inj hstab hω₁ hω₂ (h1.trans h2).symm)
  obtain ⟨ω, hωO, hωφ⟩ := hYsub _ (Subgroup.mul_mem _ ha hb) hab1
  have hperm : ∀ u ∈ burnsideB4h_U, ρ u (burnsideB4h_phi ρ v ω₁ * burnsideB4h_phi ρ v ω₂) =
      burnsideB4h_phi ρ v ω₁ * burnsideB4h_phi ρ v ω₂ := by
    intro u hu
    obtain ⟨c, rfl⟩ := hu
    have hu₁ : wedgeAct (burnsideB4h_utriG c).1 ω₁ = ω₁ ∨
        wedgeAct (burnsideB4h_utriG c).1 ω₁ = ω₂ := by
      rcases (burnsideB4h_C2_perm c).1 with h | h
      · left
        apply burnsideB4h_coords_injective
        rw [burnsideB4h_coords_wedgeAct, hc₁]
        exact h
      · right
        apply burnsideB4h_coords_injective
        rw [burnsideB4h_coords_wedgeAct, hc₁, hc₂]
        exact h
    have hu₂ : wedgeAct (burnsideB4h_utriG c).1 ω₂ = ω₁ ∨
        wedgeAct (burnsideB4h_utriG c).1 ω₂ = ω₂ := by
      rcases (burnsideB4h_C2_perm c).2 with h | h
      · left
        apply burnsideB4h_coords_injective
        rw [burnsideB4h_coords_wedgeAct, hc₂, hc₁]
        exact h
      · right
        apply burnsideB4h_coords_injective
        rw [burnsideB4h_coords_wedgeAct, hc₂]
        exact h
    have hinj := burnsideB4h_wedgeAct_injective (burnsideB4h_utriG c)
    rw [map_mul, ← burnsideB4h_phi_equiv hstab, ← burnsideB4h_phi_equiv hstab]
    rcases hu₁ with h1 | h1 <;> rcases hu₂ with h2 | h2
    · exact absurd (hinj (h1.trans h2.symm)) hne
    · rw [h1, h2]
    · rw [h1, h2, mul_comm]
    · exact absurd (hinj (h1.trans h2.symm)) hne
  have hfix : ∀ u ∈ burnsideB4h_U, wedgeAct u.1 ω = ω := by
    intro u hu
    have h1 : burnsideB4h_phi ρ v (wedgeAct u.1 ω) = burnsideB4h_phi ρ v ω := by
      rw [burnsideB4h_phi_equiv hstab, hωφ]
      exact hperm u hu
    have hωOrb := hOorb ω hωO
    have hωOrb' : wedgeAct u.1 ω ∈ burnsideB4h_Orb := by
      obtain ⟨s, rfl⟩ := hωOrb
      exact ⟨u * s, by rw [burnsideB4h_wedgeAct_mul_apply]⟩
    exact burnsideB4h_phi_inj hstab hωOrb' hωOrb h1
  have hcfix : ∀ s : Fin 6,
      (burnsideB4h_cm (burnsideB4h_utriM (Pi.single s 1))).mulVec (burnsideB4h_coords ω) =
        burnsideB4h_coords ω := by
    intro s
    have h := hfix (burnsideB4h_utriG (Pi.single s 1)) (burnsideB4h_utriG_mem _)
    rw [← burnsideB4h_coords_wedgeAct]
    exact congrArg burnsideB4h_coords h
  rcases burnsideB4h_fix_coords _ hcfix with h0 | h0
  · exact absurd h0 (burnsideB4h_coords_mem_Om_of_Orb (hOorb ω hωO))
  · have : ω = burnsideB4h_wx0 :=
      burnsideB4h_coords_injective (by rw [h0, burnsideB4h_coords_x0])
    rw [← hωφ, this, burnsideB4h_phi_x0 hstab]

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_wedge_zero_right (a : Fin 4 → ZMod 2) : wedge a (0 : Fin 4 → ZMod 2) = 0 := by
  have := wedge_smul_right (0 : ZMod 2) a a
  simpa using this

theorem burnsideB4h_wedge_zero_left (a : Fin 4 → ZMod 2) : wedge (0 : Fin 4 → ZMod 2) a = 0 := by
  have := wedge_smul_left (0 : ZMod 2) a a
  simpa using this

theorem burnsideB4h_add_self (b : Fin 4 → ZMod 2) : b + b = 0 := by
  funext i
  have : ∀ x : ZMod 2, x + x = 0 := by decide
  exact this _

theorem burnsideB4h_neg_wedge (x : wedgeSpace (ZMod 2)) : -x = x := by
  have h2 : (2 : ZMod 2) • x = 0 := by
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_smul]
  have h : x + x = 0 := by rwa [two_smul] at h2
  exact neg_eq_of_add_eq_zero_right h

theorem burnsideB4h_wedge_comm (a b : Fin 4 → ZMod 2) : wedge a b = wedge b a := by
  rw [wedge_swap a b, burnsideB4h_neg_wedge]

theorem burnsideB4h_indep3_perm : ∀ a b c : Fin 4 → ZMod 2, burnsideB4h_Indep3 a b c →
    burnsideB4h_Indep3 a (b + c) b := by
  unfold burnsideB4h_Indep3
  decide +kernel

theorem burnsideB4h_notIndep3 {a b c : Fin 4 → ZMod 2} (h : ¬ burnsideB4h_Indep3 a b c) :
    a = 0 ∨ b = 0 ∨ c = 0 ∨ a = b ∨ a = c ∨ b = c ∨ a + b = c := by
  unfold burnsideB4h_Indep3 at h
  by_contra hcon
  push_neg at hcon
  exact h hcon

theorem burnsideB4h_phi_zero {V : Type} [CommGroup V] {ρ : GL (Fin 4) (ZMod 2) →* MulAut V}
    {v : V} : burnsideB4h_phi ρ v 0 = 1 := by
  apply burnsideB4h_phi_off
  rintro ⟨s, hs⟩
  have h1 : burnsideB4h_coords (wedgeAct s.1 burnsideB4h_wx0) ≠ 0 :=
    burnsideB4h_coords_mem_Om_of_Orb ⟨s, rfl⟩
  rw [hs, burnsideB4h_coords_zero] at h1
  exact h1 rfl

theorem burnsideB4h_Phi_add {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {ρ : GL (Fin 4) (ZMod 2) →* MulAut V} {v : V}
    (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
      wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0)
    (R0 : burnsideB4h_phi ρ v (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2)) *
      burnsideB4h_phi ρ v (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2)) = v)
    (a b c : Fin 4 → ZMod 2) :
    burnsideB4h_phi ρ v (wedge a b) * burnsideB4h_phi ρ v (wedge a c) =
      burnsideB4h_phi ρ v (wedge a (b + c)) := by
  have hφ0 : burnsideB4h_phi ρ v 0 = 1 := burnsideB4h_phi_zero
  have hsq : ∀ y : V, y * y = 1 := fun y => by
    have := hV y
    rwa [pow_two] at this
  by_cases hI : burnsideB4h_Indep3 a b c
  · obtain ⟨g, hg0, hg1, hg2⟩ :=
      burnsideB4h_exists_gl_triple burnsideB4h_ZMod2 (burnsideB4h_indep3_perm a b c hI)
    have hc : g.1.mulVec (stdVec 1 + stdVec 2) = c := by
      rw [Matrix.mulVec_add, hg1, hg2, add_comm b c, add_assoc, burnsideB4h_add_self, add_zero]
    have e1 : wedge a b = wedgeAct g.1 (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 2)) := by
      rw [wedgeAct_wedge, hg0, hg2]
    have e2 : wedge a c =
        wedgeAct g.1 (wedge (stdVec 0 : Fin 4 → ZMod 2) (stdVec 1 + stdVec 2)) := by
      rw [wedgeAct_wedge, hg0, hc]
    have e3 : wedge a (b + c) = wedgeAct g.1 burnsideB4h_wx0 := by
      rw [burnsideB4h_wx0, wedgeAct_wedge, hg0, hg1]
    rw [e1, e2, e3, burnsideB4h_phi_equiv hstab, burnsideB4h_phi_equiv hstab,
      burnsideB4h_phi_equiv hstab, ← map_mul, R0, burnsideB4h_phi_x0 hstab]
  · rcases burnsideB4h_notIndep3 hI with h | h | h | h | h | h | h
    · rw [h, burnsideB4h_wedge_zero_left, burnsideB4h_wedge_zero_left,
        burnsideB4h_wedge_zero_left, hφ0, mul_one]
    · rw [h, burnsideB4h_wedge_zero_right, hφ0, one_mul, zero_add]
    · rw [h, burnsideB4h_wedge_zero_right, hφ0, mul_one, add_zero]
    · rw [← h, wedge_self, hφ0, one_mul, wedge_add_right, wedge_self, zero_add]
    · rw [← h, wedge_self, hφ0, mul_one, wedge_add_right, wedge_self, add_zero]
    · rw [← h, burnsideB4h_add_self, burnsideB4h_wedge_zero_right, hφ0]
      exact hsq _
    · rw [← h]
      have e : b + (a + b) = a := by
        calc b + (a + b) = a + (b + b) := by abel
          _ = a := by rw [burnsideB4h_add_self, add_zero]
      rw [e, wedge_add_right, wedge_self, zero_add, hφ0]
      exact hsq _

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_two_smul {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) :
    ∀ x : Additive V, (2 : ℕ) • x = 0 := by
  intro x
  rw [← ofMul_toMul x, ← ofMul_pow, hV]
  rfl

theorem burnsideB4h_core {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : GL (Fin 4) (ZMod 2) →* MulAut V) (v : V) (hv1 : v ≠ 1)
    (hgen : Subgroup.closure {y : V | ∃ s : GL (Fin 4) (ZMod 2), ρ s v = y} = ⊤)
    (hstab : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔
      wedgeAct s.1 burnsideB4h_wx0 = burnsideB4h_wx0)
    (H₀ : Subgroup (GL (Fin 4) (ZMod 2))) (hH₀card : Nat.card H₀ = 1344)
    (hUH : burnsideB4h_U ≤ H₀)
    (hY : Nat.card ↥(Subgroup.closure {y : V | ∃ h ∈ H₀, ρ h v = y}) = 8) :
    ∃ β : V ≃* Multiplicative (wedgeSpace (ZMod 2)), ∀ (g : GL (Fin 4) (ZMod 2)) (u : V),
      β (ρ g u) = Multiplicative.ofAdd (wedgeAct g.1 (Multiplicative.toAdd (β u))) := by
  classical
  have R0 := burnsideB4h_R0 hV hv1 hstab hH₀card hUH hY
  have hadd := burnsideB4h_Phi_add hV hstab R0
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (burnsideB4h_two_smul hV)
  have hsymm : ∀ a b : Fin 4 → ZMod 2,
      burnsideB4h_phi ρ v (wedge a b) = burnsideB4h_phi ρ v (wedge b a) := fun a b => by
    rw [burnsideB4h_wedge_comm]
  have hφ0 : burnsideB4h_phi ρ v 0 = 1 := burnsideB4h_phi_zero
  let B : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive V :=
    LinearMap.mk₂ (ZMod 2) (fun a b => Additive.ofMul (burnsideB4h_phi ρ v (wedge a b)))
      (fun a a' b => by
        show Additive.ofMul (burnsideB4h_phi ρ v (wedge (a + a') b)) =
          Additive.ofMul (burnsideB4h_phi ρ v (wedge a b)) +
            Additive.ofMul (burnsideB4h_phi ρ v (wedge a' b))
        rw [hsymm (a + a') b, hsymm a b, hsymm a' b, ← hadd b a a']
        exact ofMul_mul _ _)
      (fun c a b => by
        rcases burnsideB4h_ZMod2 c with rfl | rfl
        · simp [burnsideB4h_wedge_zero_left, hφ0]
        · simp)
      (fun a b b' => by
        show Additive.ofMul (burnsideB4h_phi ρ v (wedge a (b + b'))) =
          Additive.ofMul (burnsideB4h_phi ρ v (wedge a b)) +
            Additive.ofMul (burnsideB4h_phi ρ v (wedge a b'))
        rw [← hadd a b b']
        exact ofMul_mul _ _)
      (fun c a b => by
        rcases burnsideB4h_ZMod2 c with rfl | rfl
        · simp [burnsideB4h_wedge_zero_right, hφ0]
        · simp)
  have hB : ∀ x, B x x = 0 := fun x => by
    show Additive.ofMul (burnsideB4h_phi ρ v (wedge x x)) = 0
    rw [wedge_self, hφ0]
    rfl
  obtain ⟨θ, hθ⟩ := burnsideB4h_exists_wedge_lift B hB
  have hθ' : ∀ a b : Fin 4 → ZMod 2,
      θ (wedge a b) = Additive.ofMul (burnsideB4h_phi ρ v (wedge a b)) := fun a b => by
    rw [hθ]
    rfl
  have hρA : ∀ (g : GL (Fin 4) (ZMod 2)) (x : Additive V),
      (AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (ρ g).toMonoidHom)) x =
        Additive.ofMul (ρ g (Additive.toMul x)) := fun g x => rfl
  have hequiv : ∀ (g : GL (Fin 4) (ZMod 2)) (w : wedgeSpace (ZMod 2)),
      θ (wedgeAct g.1 w) = Additive.ofMul (ρ g (Additive.toMul (θ w))) := by
    intro g
    have key : θ ∘ₗ wedgeAct g.1 =
        (AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (ρ g).toMonoidHom)) ∘ₗ θ :=
      linearMap_ext_wedge fun a b => by
        simp only [LinearMap.comp_apply, wedgeAct_wedge, hθ', hρA, toMul_ofMul]
        rw [← wedgeAct_wedge, burnsideB4h_phi_equiv hstab]
    intro w
    have := LinearMap.congr_fun key w
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hρA] at this
    exact this
  have hrange : ∀ s : GL (Fin 4) (ZMod 2), Additive.ofMul (ρ s v) ∈ LinearMap.range θ := by
    intro s
    refine ⟨wedgeAct s.1 burnsideB4h_wx0, ?_⟩
    rw [burnsideB4h_wx0, wedgeAct_wedge, hθ']
    rw [← wedgeAct_wedge, ← burnsideB4h_wx0, burnsideB4h_phi_apply hstab s]
  have hsurj : Function.Surjective θ := by
    intro y
    have hy : Additive.toMul y ∈
        Subgroup.closure {y : V | ∃ s : GL (Fin 4) (ZMod 2), ρ s v = y} := by
      rw [hgen]
      trivial
    have h : ∀ z ∈ Subgroup.closure {y : V | ∃ s : GL (Fin 4) (ZMod 2), ρ s v = y},
        Additive.ofMul z ∈ LinearMap.range θ := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        exact hrange s
      | one => exact ⟨0, by simp⟩
      | mul x y _ _ hx hy =>
        rw [ofMul_mul]
        exact Submodule.add_mem _ hx hy
      | inv x _ hx =>
        rw [ofMul_inv]
        exact Submodule.neg_mem _ hx
    obtain ⟨w, hw⟩ := h _ hy
    exact ⟨w, by rw [hw]; exact ofMul_toMul y⟩
  have hinjOn : Set.InjOn (burnsideB4h_phi ρ v) burnsideB4h_Orb := fun w hw w' hw' h =>
    burnsideB4h_phi_inj hstab hw hw' h
  set orbV : Set V := {y | ∃ s : GL (Fin 4) (ZMod 2), ρ s v = y} with horbV
  have horbV_eq : orbV = burnsideB4h_phi ρ v '' burnsideB4h_Orb := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨wedgeAct s.1 burnsideB4h_wx0, ⟨s, rfl⟩, burnsideB4h_phi_apply hstab s⟩
    · rintro ⟨w, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (burnsideB4h_phi_apply hstab s).symm⟩
  have hcardV : orbV.ncard = 35 := by
    rw [horbV_eq, hinjOn.ncard_image, ← Nat.card_coe_set_eq]
    exact burnsideB4h_Orb_card
  have h1 : (1 : V) ∉ orbV := by
    rintro ⟨s, hs⟩
    exact hv1 ((ρ s).injective (hs.trans (map_one (ρ s)).symm))
  have hVge : 36 ≤ Nat.card V := by
    have h := Set.ncard_le_ncard (Set.subset_univ (insert (1 : V) orbV)) (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem h1 (Set.toFinite _), hcardV, Set.ncard_univ] at h
    exact h
  have hpg : IsPGroup 2 V := fun x => ⟨1, by simpa using hV x⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hk6 : 6 ≤ k := by
    by_contra hlt
    push_neg at hlt
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hV64 : 64 ≤ Nat.card V := by
    rw [hk]
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk6
  have hW64 : Nat.card (wedgeSpace (ZMod 2)) ≤ 64 := by
    have := Nat.card_le_card_of_injective _ (burnsideB4h_coords_injective (K := ZMod 2))
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using this
  haveI : Finite (wedgeSpace (ZMod 2)) := Finite.of_injective _ (burnsideB4h_coords_injective (K := ZMod 2))
  have hAdd : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
  have hbij : Function.Bijective θ :=
    hsurj.bijective_of_nat_card_le (by rw [hAdd]; omega)
  let e : wedgeSpace (ZMod 2) ≃+ Additive V := AddEquiv.ofBijective θ.toAddMonoidHom hbij
  have he : ∀ w, e w = θ w := fun w => rfl
  refine ⟨{ toFun := fun u => Multiplicative.ofAdd (e.symm (Additive.ofMul u))
            invFun := fun m => Additive.toMul (e (Multiplicative.toAdd m))
            left_inv := fun u => by simp
            right_inv := fun m => by simp
            map_mul' := fun u u' => by
              show Multiplicative.ofAdd (e.symm (Additive.ofMul (u * u'))) =
                Multiplicative.ofAdd (e.symm (Additive.ofMul u)) *
                  Multiplicative.ofAdd (e.symm (Additive.ofMul u'))
              rw [ofMul_mul, map_add]
              rfl }, ?_⟩
  intro g u
  show Multiplicative.ofAdd (e.symm (Additive.ofMul (ρ g u))) =
    Multiplicative.ofAdd (wedgeAct g.1 (e.symm (Additive.ofMul u)))
  refine congrArg Multiplicative.ofAdd ?_
  apply e.injective
  rw [AddEquiv.apply_symm_apply, he, hequiv, ← he, AddEquiv.apply_symm_apply]
  rfl

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_x_eq (x : wedgeSpace (ZMod 2)) (hx0 : x ≠ 0)
    (hfix : ∀ u ∈ burnsideB4h_U, wedgeAct u.1 x = x) : x = burnsideB4h_wx0 := by
  have hc : ∀ s : Fin 6, (burnsideB4h_cm (burnsideB4h_utriM (Pi.single s 1))).mulVec
      (burnsideB4h_coords x) = burnsideB4h_coords x := by
    intro s
    rw [← burnsideB4h_coords_wedgeAct]
    exact congrArg burnsideB4h_coords
      (hfix (burnsideB4h_utriG (Pi.single s 1)) (burnsideB4h_utriG_mem _))
  rcases burnsideB4h_fix_coords _ hc with h | h
  · exact absurd (burnsideB4h_coords_injective (h.trans burnsideB4h_coords_zero.symm)) hx0
  · exact burnsideB4h_coords_injective (h.trans burnsideB4h_coords_x0.symm)

theorem burnsideB4h_card_of_rk {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (Y : Subgroup V) (h : CFSG.Quasithin.rk ↥Y = 3) : Nat.card ↥Y = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥Y := fun y => ⟨1, Subtype.ext (by simpa using hV y)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  unfold CFSG.Quasithin.rk at h
  rw [hn, padicValNat.prime_pow] at h
  rw [hn, h]
  norm_num

theorem burnsideB4h_layer1 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (G H T : Subgroup (MulAut V)) (ρ : GL (Fin 4) (ZMod 2) →* MulAut V)
    (hρ : Function.Injective ρ) (hrange : ρ.range = G) (v : V) (hv1 : v ≠ 1)
    (hgen : Subgroup.closure (CFSG.Quasithin.orbitOf G v) = ⊤)
    (x : wedgeSpace (ZMod 2)) (hx0 : x ≠ 0)
    (hstab : ∀ g : MulAut V, g ∈ G ⊓ MulAction.stabilizer (MulAut V) v ↔
      ∃ s : GL (Fin 4) (ZMod 2), wedgeAct s.1 x = x ∧ ρ s = g)
    (hHG : H ≤ G) (hH : Nat.card H = 1344)
    (hTU : ∀ u ∈ burnsideB4h_U, ρ u ∈ T) (hTstab : T ≤ MulAction.stabilizer (MulAut V) v)
    (hTH : T ≤ H)
    (hrk : CFSG.Quasithin.rk ↥(Subgroup.closure (CFSG.Quasithin.orbitOf H v)) = 3) :
    ∃ β : V ≃* Multiplicative (wedgeSpace (ZMod 2)), ∀ (g : GL (Fin 4) (ZMod 2)) (u : V),
      β (ρ g u) = Multiplicative.ofAdd (wedgeAct g.1 (Multiplicative.toAdd (β u))) := by
  classical
  have hmem : ∀ s : GL (Fin 4) (ZMod 2), ρ s ∈ G := fun s => by
    rw [← hrange]
    exact ⟨s, rfl⟩
  have hstab' : ∀ s : GL (Fin 4) (ZMod 2), ρ s v = v ↔ wedgeAct s.1 x = x := by
    intro s
    have h := hstab (ρ s)
    have e : ρ s ∈ G ⊓ MulAction.stabilizer (MulAut V) v ↔ ρ s v = v := by
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨fun h => h.2, fun h => ⟨hmem s, h⟩⟩
    rw [← e, h]
    constructor
    · rintro ⟨t, ht, hts⟩
      rw [← hρ hts]
      exact ht
    · intro hs
      exact ⟨s, hs, rfl⟩
  have hxU : ∀ u ∈ burnsideB4h_U, wedgeAct u.1 x = x := by
    intro u hu
    apply (hstab' u).1
    have := hTstab (hTU u hu)
    rwa [MulAction.mem_stabilizer_iff] at this
  have hx : x = burnsideB4h_wx0 := burnsideB4h_x_eq x hx0 hxU
  subst hx
  have hH₀card : Nat.card (H.comap ρ) = 1344 := by
    have h1 : (H.comap ρ).map ρ = H := by
      rw [Subgroup.map_comap_eq, hrange]
      exact inf_eq_right.2 hHG
    have h2 : Nat.card ((H.comap ρ).map ρ) = Nat.card (H.comap ρ) :=
      Subgroup.card_map_of_injective hρ
    rw [h1, hH] at h2
    exact h2.symm
  have hUH : burnsideB4h_U ≤ H.comap ρ := fun u hu => hTH (hTU u hu)
  have hgen' : Subgroup.closure {y : V | ∃ s : GL (Fin 4) (ZMod 2), ρ s v = y} = ⊤ := by
    have hset : {y : V | ∃ s : GL (Fin 4) (ZMod 2), ρ s v = y} =
        CFSG.Quasithin.orbitOf G v := by
      ext y
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨ρ s, hmem s, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        rw [← hrange] at hg
        obtain ⟨s, rfl⟩ := hg
        exact ⟨s, rfl⟩
    rw [hset]
    exact hgen
  have hY : Nat.card ↥(Subgroup.closure {y : V | ∃ h ∈ H.comap ρ, ρ h v = y}) = 8 := by
    have hset : {y : V | ∃ h ∈ H.comap ρ, ρ h v = y} = CFSG.Quasithin.orbitOf H v := by
      ext y
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨ρ h, hh, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        have hgG : g ∈ ρ.range := by
          rw [hrange]
          exact hHG hg
        obtain ⟨s, rfl⟩ := hgG
        exact ⟨s, hg, rfl⟩
    rw [hset]
    exact burnsideB4h_card_of_rk hV _ hrk
  exact burnsideB4h_core hV ρ v hv1 hgen' hstab' (H.comap ρ) hH₀card hUH hY

end

section

open CFSG.Open
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem burnsideB4h_StatedSL : StatedSL 4 (ZMod 2) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  apply Subgroup.subset_closure
  show (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1
  have hu : IsUnit (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  rcases burnsideB4h_ZMod2 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).det with h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · exact h

theorem burnsideB4h_card_SL3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem as_B_4_13 : B_4_13 := by
  intro V _ _ hV G π v H T hv1 hgen _hpar hx hHpar hE hT hTstab hTH hrk
  obtain ⟨x, hx1, hxstab⟩ := hx
  have hSL := burnsideB4h_StatedSL
  let e0 : ChB.orthModel6.Gam ≃* GL (Fin 4) (ZMod 2) :=
    (MulEquiv.subgroupCongr hSL).trans Subgroup.topEquiv
  have hact : ∀ (s : ChB.orthModel6.Gam) (y : ChB.orthModel6.Amb), ChB.orthModel6.act s y =
      Multiplicative.ofAdd (wedgeAct (e0 s).1 (Multiplicative.toAdd y)) := fun s y => rfl
  let π1 : GL (Fin 4) (ZMod 2) ≃* ↥G := e0.symm.trans π
  let ρ₀ : GL (Fin 4) (ZMod 2) →* MulAut V := G.subtype.comp π1.toMonoidHom
  have hρ₀inj : Function.Injective ρ₀ := Subtype.coe_injective.comp π1.injective
  have hρ₀range : ρ₀.range = G := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      exact (π1 s).2
    · intro hg
      exact ⟨π1.symm ⟨g, hg⟩, by simp [ρ₀]⟩
  have hπ : ∀ s : ChB.orthModel6.Gam, ((π s : ↥G) : MulAut V) = ρ₀ (e0 s) := by
    intro s
    simp [ρ₀, π1]
  have hT₀p : IsPGroup 2 (T.comap ρ₀) := hT.2.1.comap_of_injective ρ₀ hρ₀inj
  have hT₀idx : ¬ 2 ∣ (T.comap ρ₀).index := by
    rw [Subgroup.index_comap, hρ₀range]
    exact hT.2.2
  obtain ⟨c, hc⟩ := burnsideB4h_exists_conj_U hT₀p hT₀idx
  letI : MulAction (GL (Fin 4) (ZMod 2)) (wedgeSpace (ZMod 2)) := burnsideB4h_wact
  let ρ' : GL (Fin 4) (ZMod 2) →* MulAut V := ρ₀.comp (MulAut.conj c).toMonoidHom
  have hρ'apply : ∀ s, ρ' s = ρ₀ (c * s * c⁻¹) := fun s => rfl
  have hρ'inj : Function.Injective ρ' := hρ₀inj.comp (MulAut.conj c).injective
  have hρ'range : ρ'.range = G := by
    rw [← hρ₀range]
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨c * s * c⁻¹, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨c⁻¹ * t * c, ?_⟩
      have : c * (c⁻¹ * t * c) * c⁻¹ = t := by group
      rw [hρ'apply, this]
  have hρ₀' : ∀ g : GL (Fin 4) (ZMod 2), ρ₀ g = ρ' (c⁻¹ * g * c) := fun g => by
    have : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
    rw [hρ'apply, this]
  set xa : wedgeSpace (ZMod 2) := Multiplicative.toAdd x with hxa
  have hxa0 : xa ≠ 0 := by
    intro h
    apply hx1
    have h1 : x = Multiplicative.ofAdd xa := rfl
    rw [h1, h]
    rfl
  have hstab0 : ∀ g : MulAut V, g ∈ G ⊓ MulAction.stabilizer (MulAut V) v ↔
      ∃ t : GL (Fin 4) (ZMod 2), t • xa = xa ∧ ρ₀ t = g := by
    intro g
    rw [hxstab g]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨e0 s, ?_, (hπ s).symm⟩
      have h2 := congrArg Multiplicative.toAdd ((hact s x).symm.trans hs)
      exact h2
    · rintro ⟨t, ht, rfl⟩
      refine ⟨e0.symm t, ?_, ?_⟩
      · rw [hact, MulEquiv.apply_symm_apply]
        have h3 : wedgeAct t.1 xa = xa := ht
        rw [h3]
        rfl
      · rw [hπ, MulEquiv.apply_symm_apply]
  have hstab' : ∀ g : MulAut V, g ∈ G ⊓ MulAction.stabilizer (MulAut V) v ↔
      ∃ s : GL (Fin 4) (ZMod 2), s • (c⁻¹ • xa) = c⁻¹ • xa ∧ ρ' s = g := by
    intro g
    rw [hstab0 g]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨c⁻¹ * t * c, ?_, (hρ₀' t).symm⟩
      calc (c⁻¹ * t * c) • (c⁻¹ • xa) = (c⁻¹ * t * c * c⁻¹) • xa := (mul_smul _ _ _).symm
        _ = (c⁻¹ * t) • xa := by rw [mul_assoc (c⁻¹ * t) c c⁻¹, mul_inv_cancel, mul_one]
        _ = c⁻¹ • (t • xa) := mul_smul _ _ _
        _ = c⁻¹ • xa := by rw [ht]
    · rintro ⟨s, hs, rfl⟩
      refine ⟨c * s * c⁻¹, ?_, (hρ'apply s).symm⟩
      calc (c * s * c⁻¹) • xa = c • (s • (c⁻¹ • xa)) := by rw [mul_smul, mul_smul]
        _ = c • (c⁻¹ • xa) := by rw [hs]
        _ = xa := smul_inv_smul c xa
  have hxc0 : c⁻¹ • xa ≠ 0 := by
    intro h
    apply hxa0
    exact burnsideB4h_wedgeAct_injective c⁻¹ (h.trans (map_zero (wedgeAct c⁻¹.1)).symm)
  have hTU : ∀ u ∈ burnsideB4h_U, ρ' u ∈ T := by
    intro u hu
    have : c * u * c⁻¹ ∈ T.comap ρ₀ := (hc _).2 ⟨u, hu, rfl⟩
    exact this
  obtain ⟨E, hEn, hEab, hE8, ⟨φE⟩⟩ := hE
  have hH1344 : Nat.card H = 1344 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E
    rw [Nat.card_congr φE.toEquiv, hE8, burnsideB4h_card_SL3] at h1
    omega
  obtain ⟨β', hβ'⟩ := burnsideB4h_layer1 hV G H T ρ' hρ'inj hρ'range v hv1 hgen (c⁻¹ • xa) hxc0
    hstab' hHpar.1 hH1344 hTU (fun t ht => (hTstab ht).2) hTH hrk
  let cE : wedgeSpace (ZMod 2) ≃+ wedgeSpace (ZMod 2) :=
    { toFun := fun w => c • w
      invFun := fun w => c⁻¹ • w
      left_inv := fun w => inv_smul_smul c w
      right_inv := fun w => smul_inv_smul c w
      map_add' := fun a b => map_add (wedgeAct c.1) a b }
  let β : V ≃* Multiplicative (wedgeSpace (ZMod 2)) := β'.trans (AddEquiv.toMultiplicative cE)
  refine ⟨β, fun s u => ?_⟩
  rw [hact, hπ]
  show Multiplicative.ofAdd (c • Multiplicative.toAdd (β' ((ρ₀ (e0 s)) u))) =
    Multiplicative.ofAdd ((e0 s) • (c • Multiplicative.toAdd (β' u)))
  rw [hρ₀' (e0 s), hβ', toAdd_ofAdd]
  show Multiplicative.ofAdd (c • ((c⁻¹ * e0 s * c) • Multiplicative.toAdd (β' u))) = _
  rw [← mul_smul, ← mul_smul]
  have : c * (c⁻¹ * e0 s * c) = e0 s * c := by group
  rw [this]

end

section

section Transport
open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) {R : Type} [Group R] (α : ↥G ≃* R)

@[expose] def burnsideB4h_img (A : Subgroup (MulAut V)) : Subgroup R :=
  (A.subgroupOf G).map α.toMonoidHom

variable {G α}

theorem burnsideB4h_mem_img {A : Subgroup (MulAut V)} {y : R} :
    y ∈ burnsideB4h_img G α A ↔ ∃ g : ↥G, (g : MulAut V) ∈ A ∧ α g = y := by
  unfold burnsideB4h_img
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem burnsideB4h_img_mono {A B : Subgroup (MulAut V)} (h : A ≤ B) :
    burnsideB4h_img G α A ≤ burnsideB4h_img G α B := fun y hy => by
  obtain ⟨g, hg, rfl⟩ := burnsideB4h_mem_img.1 hy
  exact burnsideB4h_mem_img.2 ⟨g, h hg, rfl⟩

theorem burnsideB4h_img_centralizer (A : Subgroup (MulAut V)) {B : Subgroup (MulAut V)}
    (hB : B ≤ G) :
    burnsideB4h_img G α (A ⊓ Subgroup.centralizer (B : Set (MulAut V))) =
      burnsideB4h_img G α A ⊓ Subgroup.centralizer (burnsideB4h_img G α B : Set R) := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, rfl⟩ := burnsideB4h_mem_img.1 hy
    refine ⟨burnsideB4h_mem_img.2 ⟨g, hg.1, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro z hz
    obtain ⟨b, hb, rfl⟩ := burnsideB4h_mem_img.1 hz
    have hc : (b : MulAut V) * (g : MulAut V) = (g : MulAut V) * (b : MulAut V) :=
      (Subgroup.mem_centralizer_iff.1 hg.2) _ hb
    have : b * g = g * b := Subtype.ext hc
    rw [← map_mul, ← map_mul, this]
  · rintro ⟨h1, h2⟩
    obtain ⟨g, hg, rfl⟩ := burnsideB4h_mem_img.1 h1
    refine burnsideB4h_mem_img.2 ⟨g, ⟨hg, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
    intro z hz
    have hzG : z ∈ G := hB hz
    have hmem : α ⟨z, hzG⟩ ∈ burnsideB4h_img G α B := burnsideB4h_mem_img.2 ⟨⟨z, hzG⟩, hz, rfl⟩
    have hc := (Subgroup.mem_centralizer_iff.1 h2) _ hmem
    have : (⟨z, hzG⟩ : ↥G) * g = g * ⟨z, hzG⟩ := α.injective (by rw [map_mul, map_mul, hc])
    exact congrArg Subtype.val this

theorem burnsideB4h_card_img {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    Nat.card (burnsideB4h_img G α A) = Nat.card A := by
  unfold burnsideB4h_img
  rw [Subgroup.card_map_of_injective α.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem burnsideB4h_le_of_isMaxParabolic2 {P : Subgroup (MulAut V)} (hP : IsMaxParabolic2 G P) :
    P ≤ G :=
  hP.1.1

variable [Finite V] [Finite R]

theorem burnsideB4h_img_perfectCore {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    burnsideB4h_img G α (perfectCore A) = perfectCore (burnsideB4h_img G α A) := by
  have h1 : (perfectCore (A.subgroupOf G)).map G.subtype = perfectCore A := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hA]
  have h2 : (perfectCore A).subgroupOf G = perfectCore (A.subgroupOf G) := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  unfold burnsideB4h_img
  rw [h2, map_perfectCore]

theorem burnsideB4h_img_pCoreOf {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    burnsideB4h_img G α (pCoreOf 2 A) = pCoreOf 2 (burnsideB4h_img G α A) := by
  have h1 : pCoreOf 2 ((A.subgroupOf G).map G.subtype) =
      (pCoreOf 2 (A.subgroupOf G)).map G.subtype :=
    CFSG.Quasithin.H13.Ch4.B414.M.pCoreOf_map_inj G.subtype G.subtype_injective _
  rw [Subgroup.map_subgroupOf_eq_of_le hA] at h1
  have h2 : (pCoreOf 2 A).subgroupOf G = pCoreOf 2 (A.subgroupOf G) := by
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  unfold burnsideB4h_img
  rw [h2]
  exact (CFSG.Quasithin.H13.Ch4.B414.M.pCoreOf_map_inj α.toMonoidHom α.injective _).symm

theorem burnsideB4h_img_maxParabolic {P : Subgroup (MulAut V)} (hP : IsMaxParabolic2 G P) :
    IsMaxParabolic2 (⊤ : Subgroup R) (burnsideB4h_img G α P) :=
  CFSG.QuasithinUnique.Vol2Native.A312L.isMaxParabolic2_top_map_equiv α
    (CFSG.Quasithin.SzN2.isMaxParabolic2_top_of_map hP)

end Transport

end

section

section Unique
open CFSG.ASVolI.ChB

variable {F : Type} [Field F]

theorem burnsideB4h_unq_charP [Fintype F] (hF : Fintype.card F = 4) : CharP F 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (k := 2) (by norm_num) (by rw [Nat.card_eq_fintype_card, hF]; norm_num)

theorem burnsideB4h_unq_two_eq_zero [Fintype F] (hF : Fintype.card F = 4) : (2 : F) = 0 := by
  have := burnsideB4h_unq_charP hF
  exact CharTwo.two_eq_zero

theorem burnsideB4h_unq_pow_three [Fintype F] (hF : Fintype.card F = 4) (ν : Fˣ) : ν ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Fˣ) (x := ν)
  rw [Nat.card_units, Nat.card_eq_fintype_card, hF] at h
  simpa using h

theorem burnsideB4h_unq_exists_ne_one [Fintype F] (hF : Fintype.card F = 4) : ∃ ν : Fˣ, ν ≠ 1 := by
  by_contra h
  push Not at h
  have hs : Subsingleton Fˣ := ⟨fun a b => (h a).trans (h b).symm⟩
  have h1 := (Finite.card_le_one_iff_subsingleton (α := Fˣ)).2 hs
  rw [Nat.card_units, Nat.card_eq_fintype_card, hF] at h1
  omega

@[expose] def burnsideB4h_unq_diag (a b c : Fˣ) : GL (Fin 3) F where
  val := Matrix.diagonal ![(a : F), b, c]
  inv := Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp

theorem burnsideB4h_unq_twAdj_diag (k : ℕ) (a b c : Fˣ) (M : Matrix (Fin 3) (Fin 3) F)
    (i j : Fin 3) :
    twAdjMat k (burnsideB4h_unq_diag a b c) M i j =
      ((a : F) * b * c) ^ k * (![(a : F), b, c] i * M i j *
        ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)] j) := by
  unfold twAdjMat
  have hdet : ((burnsideB4h_unq_diag a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      (a : F) * b * c := by
    show (Matrix.diagonal ![(a : F), b, c]).det = _
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  rw [hdet]
  show ((a : F) * b * c) ^ k * ((Matrix.diagonal ![(a : F), b, c] * M *
    Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)]) i j) = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem burnsideB4h_unq_twAdj_tv (k : ℕ) (i j : Fin 3) (h : i ≠ j) (c : F)
    (M : Matrix (Fin 3) (Fin 3) F) :
    twAdjMat k (Matrix.GeneralLinearGroup.transvection i j h c) M =
      Matrix.transvection i j c * M * Matrix.transvection i j (-c) := by
  unfold twAdjMat
  have hdet : ((Matrix.GeneralLinearGroup.transvection i j h c : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    exact Matrix.det_transvection_of_ne i j h c
  rw [hdet, one_pow, one_smul]
  rfl

theorem burnsideB4h_unq_tv02 (N : Matrix (Fin 3) (Fin 3) F)
    (h : Matrix.transvection 0 2 (1 : F) * N * Matrix.transvection 0 2 (-1 : F) = N) :
    N 2 0 = 0 ∧ N 2 1 = 0 ∧ N 1 0 = 0 ∧ N 2 2 = N 0 0 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply,
    Matrix.single_apply] at e00 e01 e02 e12
  exact ⟨e00, e01, e12, by linear_combination e02 + e00⟩

theorem burnsideB4h_unq_tv21 (N : Matrix (Fin 3) (Fin 3) F)
    (h : Matrix.transvection 2 1 (1 : F) * N * Matrix.transvection 2 1 (-1 : F) = N) :
    N 0 2 = 0 ∧ N 1 2 = 0 ∧ N 1 0 = 0 ∧ N 1 1 = N 2 2 := by
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply,
    Matrix.single_apply] at e01 e11 e20 e21
  exact ⟨e01, e11, e20, by linear_combination e21 + e11⟩

theorem burnsideB4h_unq_fix (h2 : (2 : F) = 0) (N : Matrix (Fin 3) (Fin 3) F)
    (htr : N.trace = 0)
    (h1 : Matrix.transvection 0 2 (1 : F) * N * Matrix.transvection 0 2 (-1 : F) = N)
    (h1' : Matrix.transvection 2 1 (1 : F) * N * Matrix.transvection 2 1 (-1 : F) = N) :
    N = Matrix.single 0 1 (N 0 1) := by
  obtain ⟨a1, a2, a3, a4⟩ := burnsideB4h_unq_tv02 N h1
  obtain ⟨b1, b2, b3, b4⟩ := burnsideB4h_unq_tv21 N h1'
  have h00 : N 0 0 = 0 := by
    rw [Matrix.trace_fin_three] at htr
    linear_combination htr - b4 - 2 * a4 - N 0 0 * h2
  have h22 : N 2 2 = 0 := a4.trans h00
  have h11 : N 1 1 = 0 := b4.trans h22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, *]

theorem burnsideB4h_unq_single_mem (c : F) :
    Matrix.single (0 : Fin 3) (1 : Fin 3) c ∈ sl3Sub F := by
  simp [sl3Sub, Matrix.trace_fin_three, Matrix.single_apply]

theorem burnsideB4h_unq_diag_E (k : ℕ) (t : Fˣ) (c : F) :
    twAdjMat k (burnsideB4h_unq_diag t 1 t⁻¹) (Matrix.single 0 1 c) =
      Matrix.single 0 1 ((t : F) * c) := by
  ext i j
  rw [burnsideB4h_unq_twAdj_diag]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem burnsideB4h_unq_diag_E' (k : ℕ) (ν : Fˣ) (c : F) :
    twAdjMat k (burnsideB4h_unq_diag ν 1 1) (Matrix.single 0 1 c) =
      Matrix.single 0 1 ((ν : F) ^ (k + 1) * c) := by
  ext i j
  rw [burnsideB4h_unq_twAdj_diag]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, pow_succ] <;> ring

theorem burnsideB4h_unq_tv_E (k : ℕ) (c : F) :
    twAdjMat k (Matrix.GeneralLinearGroup.transvection 0 2 (by decide) 1) (Matrix.single 0 1 c) =
      Matrix.single 0 1 c := by
  rw [burnsideB4h_unq_twAdj_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply,
      Matrix.single_apply]

theorem burnsideB4h_unq_tv_E' (k : ℕ) (c : F) :
    twAdjMat k (Matrix.GeneralLinearGroup.transvection 2 1 (by decide) 1) (Matrix.single 0 1 c) =
      Matrix.single 0 1 c := by
  rw [burnsideB4h_unq_twAdj_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply,
      Matrix.single_apply]

theorem burnsideB4h_unq_core [Fintype F] (hF : Fintype.card F = 4) {k k' : ℕ} (hk : k < 3)
    (hk' : k' < 3) (Θ : ↥(sl3Sub F) ≃+ ↥(sl3Sub F))
    (hint : ∀ (g : GL (Fin 3) F) (M N : ↥(sl3Sub F)),
      (N : Matrix (Fin 3) (Fin 3) F) = twAdjMat k g M →
        (Θ N : Matrix (Fin 3) (Fin 3) F) = twAdjMat k' g (Θ M : Matrix (Fin 3) (Fin 3) F)) :
    k = k' := by
  have h2 := burnsideB4h_unq_two_eq_zero hF
  let E : F → ↥(sl3Sub F) := fun c => ⟨Matrix.single 0 1 c, burnsideB4h_unq_single_mem c⟩
  have hE : ∀ c, ((E c : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.single 0 1 c :=
    fun c => rfl
  have hN1 := hint (Matrix.GeneralLinearGroup.transvection 0 2 (by decide) 1) (E 1) (E 1)
    (by rw [hE, burnsideB4h_unq_tv_E])
  have hN2 := hint (Matrix.GeneralLinearGroup.transvection 2 1 (by decide) 1) (E 1) (E 1)
    (by rw [hE, burnsideB4h_unq_tv_E'])
  rw [burnsideB4h_unq_twAdj_tv] at hN1 hN2
  have htr : (Θ (E 1) : Matrix (Fin 3) (Fin 3) F).trace = 0 := (Θ (E 1)).2
  have hfix := burnsideB4h_unq_fix h2 _ htr hN1.symm hN2.symm
  set c : F := (Θ (E 1) : Matrix (Fin 3) (Fin 3) F) 0 1 with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : Θ (E 1) = 0 := by
      apply Subtype.ext
      rw [hfix, h0]
      simp
    have : E 1 = 0 := by
      have := Θ.injective (hz.trans (map_zero Θ).symm)
      exact this
    have h01 := congrArg (fun M : ↥(sl3Sub F) => (M : Matrix (Fin 3) (Fin 3) F) 0 1) this
    simp [hE, Matrix.single_apply] at h01
  have hstep2 : ∀ t : Fˣ, (Θ (E (t : F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.single 0 1 ((t : F) * c) := by
    intro t
    have := hint (burnsideB4h_unq_diag t 1 t⁻¹) (E 1) (E (t : F))
      (by rw [hE, hE, burnsideB4h_unq_diag_E, mul_one])
    rw [this, hfix, burnsideB4h_unq_diag_E]
  obtain ⟨ν, hν⟩ := burnsideB4h_unq_exists_ne_one hF
  have h3 := burnsideB4h_unq_pow_three hF ν
  have hst3 := hint (burnsideB4h_unq_diag ν 1 1) (E 1) (E (((ν ^ (k + 1) : Fˣ)) : F))
    (by rw [hE, hE, burnsideB4h_unq_diag_E', mul_one, Units.val_pow_eq_pow_val])
  rw [hstep2, hfix, burnsideB4h_unq_diag_E'] at hst3
  have hentry := congrFun (congrFun hst3 0) 1
  simp only [Matrix.single_apply, if_true, Units.val_pow_eq_pow_val] at hentry
  have hpow : (ν : F) ^ (k + 1) = (ν : F) ^ (k' + 1) := mul_right_cancel₀ hc0 hentry
  have hpowU : ν ^ (k + 1) = ν ^ (k' + 1) := Units.ext (by simpa using hpow)
  have hord : orderOf ν = 3 := orderOf_eq_prime h3 hν
  have hmod := (pow_eq_pow_iff_modEq).1 hpowU
  rw [hord] at hmod
  unfold Nat.ModEq at hmod
  omega

theorem burnsideB4h_unq_twist_unique {V : Type} [CommGroup V] [Fintype F]
    (hF : Fintype.card F = 4) (G : Subgroup (MulAut V)) (α : ↥G →* PGL3 F)
    (hα : Function.Surjective α) {k k' : ℕ} (hk : k < 3) (hk' : k' < 3)
    {β β' : V ≃* Multiplicative ↥(sl3Sub F)} (h : TwAdjointIntertwines G α k β)
    (h' : TwAdjointIntertwines G α k' β') : k = k' := by
  let Θ : ↥(sl3Sub F) ≃+ ↥(sl3Sub F) := AddEquiv.toMultiplicative.symm (β.symm.trans β')
  refine burnsideB4h_unq_core hF hk hk' Θ ?_
  intro g M N hN
  obtain ⟨γ, hγ⟩ := hα (QuotientGroup.mk g)
  set v : V := β.symm (Multiplicative.ofAdd M) with hv
  have hβv : β v = Multiplicative.ofAdd M := by rw [hv]; exact β.apply_symm_apply _
  have h1 := h γ v g hγ.symm
  rw [hβv, toAdd_ofAdd] at h1
  have h2 : Multiplicative.toAdd (β ((γ : MulAut V) v)) = N := Subtype.ext (by rw [h1, hN])
  have h3 : (γ : MulAut V) v = β.symm (Multiplicative.ofAdd N) := by
    apply β.injective
    rw [β.apply_symm_apply, ← h2, ofAdd_toAdd]
  have h4 := h' γ v g hγ.symm
  have hΘN : Θ N = Multiplicative.toAdd (β' ((γ : MulAut V) v)) := by
    rw [h3]; rfl
  have hΘM : Θ M = Multiplicative.toAdd (β' v) := rfl
  rw [hΘN, hΘM]
  exact h4

end Unique

end

section

section TrInv

variable {F : Type} [Field F]

@[expose] def burnsideB4h_trInv2 (A : GL (Fin 2) F) : GL (Fin 2) F where
  val := Matrix.transpose ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  inv := Matrix.transpose (A : Matrix (Fin 2) (Fin 2) F)
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem burnsideB4h_coe_trInv2 (A : GL (Fin 2) F) :
    ((burnsideB4h_trInv2 A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.transpose ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem burnsideB4h_trInv2_mul (A B : GL (Fin 2) F) :
    burnsideB4h_trInv2 (A * B) = burnsideB4h_trInv2 A * burnsideB4h_trInv2 B := by
  apply Units.ext
  rw [Units.val_mul, burnsideB4h_coe_trInv2, burnsideB4h_coe_trInv2, burnsideB4h_coe_trInv2,
    _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem burnsideB4h_trInv2_trInv2 (A : GL (Fin 2) F) :
    burnsideB4h_trInv2 (burnsideB4h_trInv2 A) = A := by
  apply Units.ext
  rw [burnsideB4h_coe_trInv2]
  have h : (((burnsideB4h_trInv2 A)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.transpose (A : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [h, Matrix.transpose_transpose]

theorem burnsideB4h_det_trInv2 (A : GL (Fin 2) F) :
    ((burnsideB4h_trInv2 A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ((A : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
  rw [burnsideB4h_coe_trInv2, Matrix.det_transpose]
  have h1 : (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det *
      (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  exact eq_inv_of_mul_eq_one_left h1

theorem burnsideB4h_trInv2_mem {A : GL (Fin 2) F} (hA : A ∈ StatedSL 2 F) :
    burnsideB4h_trInv2 A ∈ StatedSL 2 F := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at hA ⊢
  rw [burnsideB4h_det_trInv2, hA, inv_one]

@[expose] noncomputable def burnsideB4h_trInv : ↥(StatedSL 2 F) ≃* ↥(StatedSL 2 F) where
  toFun B := ⟨burnsideB4h_trInv2 (B : GL (Fin 2) F), burnsideB4h_trInv2_mem B.2⟩
  invFun B := ⟨burnsideB4h_trInv2 (B : GL (Fin 2) F), burnsideB4h_trInv2_mem B.2⟩
  left_inv B := Subtype.ext (burnsideB4h_trInv2_trInv2 _)
  right_inv B := Subtype.ext (burnsideB4h_trInv2_trInv2 _)
  map_mul' A B := Subtype.ext (burnsideB4h_trInv2_mul _ _)

end TrInv

end

section

section Found
open CFSG.ASVolI.ChB

variable {F : Type} [Field F]

@[expose] noncomputable def burnsideB4h_act (k : ℕ) (y : Matrix.ProjGenLinGroup (Fin 3) F)
    (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  twAdjMat k (Matrix.ProjGenLinGroup.mk_surjective y).choose M

theorem burnsideB4h_twAdjMat_mul (k : ℕ) (g h : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    twAdjMat k (g * h) M = twAdjMat k g (twAdjMat k h M) :=
  CFSG.Quasithin.H13.Ch4.B414.M.twAdj_mul k g h M

theorem burnsideB4h_twAdjMat_one (k : ℕ) (M : Matrix (Fin 3) (Fin 3) F) :
    twAdjMat k 1 M = M :=
  CFSG.Quasithin.H13.Ch4.B414.M.twAdj_one k M

theorem burnsideB4h_twAdjMat_scalar [Fintype F] (hF : Fintype.card F = 4) (k : ℕ) (u : Fˣ)
    (M : Matrix (Fin 3) (Fin 3) F) :
    twAdjMat k (Matrix.GeneralLinearGroup.scalar (Fin 3) u) M = M := by
  have h3 := burnsideB4h_unq_pow_three hF u
  have hscal : ∀ w : Fˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 3) w : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (w : F) • (1 : Matrix (Fin 3) (Fin 3) F) := fun w => by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h1 := hscal u
  have h2 : (((Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = ((u⁻¹ : Fˣ) : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← map_inv, hscal]
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar]
    simp [h3]
  unfold twAdjMat
  rw [hdet, h2, h1]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem burnsideB4h_twAdjMat_mul_center [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    (g z : GL (Fin 3) F) (hz : z ∈ Subgroup.center (GL (Fin 3) F))
    (M : Matrix (Fin 3) (Fin 3) F) : twAdjMat k (g * z) M = twAdjMat k g M := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, rfl⟩ := hz
  rw [burnsideB4h_twAdjMat_mul, burnsideB4h_twAdjMat_scalar hF]

theorem burnsideB4h_act_mk [Fintype F] (hF : Fintype.card F = 4) (k : ℕ) (g : GL (Fin 3) F)
    (M : Matrix (Fin 3) (Fin 3) F) :
    burnsideB4h_act k (Matrix.ProjGenLinGroup.mk g) M = twAdjMat k g M := by
  unfold burnsideB4h_act
  have hspec := (Matrix.ProjGenLinGroup.mk_surjective
    (Matrix.ProjGenLinGroup.mk g : Matrix.ProjGenLinGroup (Fin 3) F)).choose_spec
  obtain ⟨z, hz, hzz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff'.1 hspec.symm
  rw [← hzz, burnsideB4h_twAdjMat_mul_center hF k g z hz M]

theorem burnsideB4h_act_mul [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    (y z : Matrix.ProjGenLinGroup (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    burnsideB4h_act k (y * z) M = burnsideB4h_act k y (burnsideB4h_act k z M) := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  obtain ⟨h, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective z
  rw [← map_mul, burnsideB4h_act_mk hF, burnsideB4h_act_mk hF, burnsideB4h_act_mk hF,
    burnsideB4h_twAdjMat_mul]

theorem burnsideB4h_act_one [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    (M : Matrix (Fin 3) (Fin 3) F) : burnsideB4h_act k 1 M = M := by
  have : (1 : Matrix.ProjGenLinGroup (Fin 3) F) = Matrix.ProjGenLinGroup.mk 1 := rfl
  rw [this, burnsideB4h_act_mk hF, burnsideB4h_twAdjMat_one]

theorem burnsideB4h_act_add [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    (y : Matrix.ProjGenLinGroup (Fin 3) F) (M N : Matrix (Fin 3) (Fin 3) F) :
    burnsideB4h_act k y (M + N) = burnsideB4h_act k y M + burnsideB4h_act k y N := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  rw [burnsideB4h_act_mk hF, burnsideB4h_act_mk hF, burnsideB4h_act_mk hF]
  exact CFSG.Quasithin.H13.Ch4.B414.M.twAdj_add k g M N

theorem burnsideB4h_act_smul [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    (y : Matrix.ProjGenLinGroup (Fin 3) F) (t : F) (M : Matrix (Fin 3) (Fin 3) F) :
    burnsideB4h_act k y (t • M) = t • burnsideB4h_act k y M := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  rw [burnsideB4h_act_mk hF, burnsideB4h_act_mk hF]
  exact CFSG.Quasithin.H13.Ch4.B414.M.twAdj_smul k g t M

@[expose] def burnsideB4h_fixM [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    (Y : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)) :
    Submodule F (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | M.trace = 0 ∧ ∀ y ∈ Y, burnsideB4h_act k y M = M}
  add_mem' := by
    rintro M N ⟨hM1, hM2⟩ ⟨hN1, hN2⟩
    refine ⟨by rw [Matrix.trace_add, hM1, hN1, add_zero], fun y hy => ?_⟩
    rw [burnsideB4h_act_add hF, hM2 y hy, hN2 y hy]
  zero_mem' := by
    refine ⟨Matrix.trace_zero _ _, fun y hy => ?_⟩
    simpa using burnsideB4h_act_smul hF k y 0 0
  smul_mem' := by
    rintro c M ⟨hM1, hM2⟩
    refine ⟨by rw [Matrix.trace_smul, hM1, smul_zero], fun y hy => ?_⟩
    rw [burnsideB4h_act_smul hF, hM2 y hy]

theorem burnsideB4h_mem_fixM [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    (Y : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)) (M : Matrix (Fin 3) (Fin 3) F) :
    M ∈ burnsideB4h_fixM hF k Y ↔ M.trace = 0 ∧ ∀ y ∈ Y, burnsideB4h_act k y M = M := Iff.rfl

@[expose] def burnsideB4h_blkMat (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

theorem burnsideB4h_blkMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    burnsideB4h_blkMat (A * B) = burnsideB4h_blkMat A * burnsideB4h_blkMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_blkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem burnsideB4h_blkMat_one : burnsideB4h_blkMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideB4h_blkMat]

theorem burnsideB4h_det_blkMat (B : Matrix (Fin 2) (Fin 2) F) :
    (burnsideB4h_blkMat B).det = B.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [burnsideB4h_blkMat]

@[expose] def burnsideB4h_blkGL (B : GL (Fin 2) F) : GL (Fin 3) F where
  val := burnsideB4h_blkMat (B : Matrix (Fin 2) (Fin 2) F)
  inv := burnsideB4h_blkMat ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  val_inv := by rw [← burnsideB4h_blkMat_mul, Units.mul_inv, burnsideB4h_blkMat_one]
  inv_val := by rw [← burnsideB4h_blkMat_mul, Units.inv_mul, burnsideB4h_blkMat_one]

@[expose] def burnsideB4h_blkHom : GL (Fin 2) F →* GL (Fin 3) F where
  toFun := burnsideB4h_blkGL
  map_one' := Units.ext burnsideB4h_blkMat_one
  map_mul' A B := Units.ext (by
    show burnsideB4h_blkMat ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
    rw [Units.val_mul, burnsideB4h_blkMat_mul]
    rfl)

@[expose] noncomputable def burnsideB4h_embSL :
    ↥(StatedSL 2 F) →* Matrix.ProjGenLinGroup (Fin 3) F :=
  Matrix.ProjGenLinGroup.mk.comp (burnsideB4h_blkHom.comp (StatedSL 2 F).subtype)

theorem burnsideB4h_embSL_apply (B : ↥(StatedSL 2 F)) :
    burnsideB4h_embSL B = Matrix.ProjGenLinGroup.mk (burnsideB4h_blkGL (B : GL (Fin 2) F)) := rfl

theorem burnsideB4h_det_of_mem (B : ↥(StatedSL 2 F)) :
    ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL B.2

theorem burnsideB4h_act_embSL [Fintype F] (hF : Fintype.card F = 4) (k : ℕ) (B : ↥(StatedSL 2 F))
    (M : Matrix (Fin 3) (Fin 3) F) :
    burnsideB4h_act k (burnsideB4h_embSL B) M =
      burnsideB4h_blkMat ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * M *
        burnsideB4h_blkMat (((B : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rw [burnsideB4h_embSL_apply, burnsideB4h_act_mk hF]
  unfold twAdjMat
  have hdet : ((burnsideB4h_blkGL (B : GL (Fin 2) F) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    show (burnsideB4h_blkMat ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det = 1
    rw [burnsideB4h_det_blkMat, burnsideB4h_det_of_mem]
  rw [hdet, one_pow, one_smul]
  rfl

theorem burnsideB4h_embSL_eq_one {B : ↥(StatedSL 2 F)} (h : burnsideB4h_embSL B = 1) : B = 1 := by
  rw [burnsideB4h_embSL_apply, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have hm := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hu
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e11 := congrFun (congrFun hm 1) 1
  have e12 := congrFun (congrFun hm 1) 2
  have e21 := congrFun (congrFun hm 2) 1
  have e22 := congrFun (congrFun hm 2) 2
  simp [Matrix.scalar_apply, burnsideB4h_blkGL, burnsideB4h_blkMat] at e00 e11 e12 e21 e22
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e11, e12, e21, e22] <;> aesop

theorem burnsideB4h_embSL_injective : Function.Injective (burnsideB4h_embSL (F := F)) := by
  rw [injective_iff_map_eq_one]
  exact fun B h => burnsideB4h_embSL_eq_one h

end Found

section C0
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]

@[expose] noncomputable def burnsideB4h_x0 (ν : Fˣ) : Matrix.ProjGenLinGroup (Fin 3) F :=
  Matrix.ProjGenLinGroup.mk (dgHom ν)

@[expose] noncomputable def burnsideB4h_C0 (ν : Fˣ) :
    Subgroup (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Ptheta F 0 ⊓ Subgroup.centralizer
    (Subgroup.zpowers (burnsideB4h_x0 ν : Matrix.ProjGenLinGroup (Fin 3) F) :
      Set (Matrix.ProjGenLinGroup (Fin 3) F))

theorem burnsideB4h_mem_C0_iff [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    (y : Matrix.ProjGenLinGroup (Fin 3) F) :
    y ∈ burnsideB4h_C0 ν ↔ ∃ B : ↥(StatedSL 2 F), burnsideB4h_embSL B = y := by
  have h3 : ∀ u : Fˣ, u ^ 3 = 1 := burnsideB4h_unq_pow_three hF
  constructor
  · rintro ⟨hy1, hy2⟩
    obtain ⟨A, h10, h20, rfl⟩ := exists_rep_of_mem_Ptheta hy1
    have hcomm := (Subgroup.mem_centralizer_iff.1 hy2) (burnsideB4h_x0 ν)
      (Subgroup.mem_zpowers _)
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1
      (show Matrix.ProjGenLinGroup.mk (dgHom ν * Matrix.SpecialLinearGroup.toGL A) =
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A * dgHom ν) by
        rw [map_mul, map_mul]; exact hcomm)
    have hm := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hu
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_dgHom,
      Matrix.GeneralLinearGroup.coe_scalar] at hm
    have e00 := congrFun (congrFun hm 0) 0
    have e01 := congrFun (congrFun hm 0) 1
    have e02 := congrFun (congrFun hm 0) 2
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.mul_apply,
      Fin.sum_univ_three, h10, h20] at e00 e01 e02
    have hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := A.prop
    rw [det_of_par h10 h20] at hdet
    have hA0 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
    have hν0 : (ν : F) ≠ 0 := ν.ne_zero
    have hν1 : (ν : F) ≠ 1 := fun h => hν (Units.ext h)
    have hu1 : (u : F) = 1 := by
      have : ((u : F) - 1) * ((ν : F) * (A : Matrix (Fin 3) (Fin 3) F) 0 0) = 0 := by
        linear_combination e00
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero hν0 hA0))
    rw [hu1, mul_one] at e01 e02
    have h01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
      have : ((ν : F) - 1) * (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν1)
    have h02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by
      have : ((ν : F) - 1) * (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by linear_combination e02
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν1)
    set a : F := (A : Matrix (Fin 3) (Fin 3) F) 0 0 with ha_def
    have hA0' : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := hA0
    have ha3 : a ^ 3 = 1 := by
      have := congrArg Units.val (h3 (Units.mk0 a hA0))
      simpa using this
    set D : F := (A : Matrix (Fin 3) (Fin 3) F) 1 1 * (A : Matrix (Fin 3) (Fin 3) F) 2 2 -
      (A : Matrix (Fin 3) (Fin 3) F) 1 2 * (A : Matrix (Fin 3) (Fin 3) F) 2 1 with hD_def
    have hD : D = a⁻¹ := eq_inv_of_mul_eq_one_right hdet
    let B₁ : Matrix (Fin 2) (Fin 2) F :=
      !![a⁻¹ * (A : Matrix (Fin 3) (Fin 3) F) 1 1, a⁻¹ * (A : Matrix (Fin 3) (Fin 3) F) 1 2;
        a⁻¹ * (A : Matrix (Fin 3) (Fin 3) F) 2 1, a⁻¹ * (A : Matrix (Fin 3) (Fin 3) F) 2 2]
    have hdetB : B₁.det = 1 := by
      have e : B₁.det = a⁻¹ ^ 2 * D := by
        simp only [B₁, Matrix.det_fin_two, hD_def]
        simp
        ring
      rw [e, hD, ← pow_succ, inv_pow, show (2 : ℕ) + 1 = 3 from rfl, ha3, inv_one]
    let B₁SL : Matrix.SpecialLinearGroup (Fin 2) F := ⟨B₁, hdetB⟩
    have hmem : Matrix.SpecialLinearGroup.toGL B₁SL ∈ StatedSL 2 F := by
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
      simpa using hdetB
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [burnsideB4h_embSL_apply]
    refine Matrix.ProjGenLinGroup.mk_eq_mk_iff.2 ⟨Units.mk0 a hA0, ?_⟩
    apply Units.ext
    show burnsideB4h_blkMat B₁ * Matrix.scalar (Fin 3) a = (A : Matrix (Fin 3) (Fin 3) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideB4h_blkMat, B₁, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three,
        h01, h02, h10, h20, hA0, ha_def] <;> field_simp [hA0']
  · rintro ⟨B, rfl⟩
    let A : Matrix.SpecialLinearGroup (Fin 3) F :=
      ⟨burnsideB4h_blkMat ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
        rw [burnsideB4h_det_blkMat, burnsideB4h_det_of_mem]⟩
    have hAGL : Matrix.SpecialLinearGroup.toGL A = burnsideB4h_blkGL (B : GL (Fin 2) F) :=
      Units.ext rfl
    have hblk : IsBlock (A : Matrix (Fin 3) (Fin 3) F) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [A, burnsideB4h_blkMat]
    have hmem := mk_mem_Ptheta_zero (A := A) (by simp [A, burnsideB4h_blkMat])
      (by simp [A, burnsideB4h_blkMat])
    rw [hAGL] at hmem
    refine ⟨hmem, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hc : burnsideB4h_x0 ν * burnsideB4h_embSL B = burnsideB4h_embSL B * burnsideB4h_x0 ν := by
      rw [burnsideB4h_embSL_apply, burnsideB4h_x0, ← map_mul, ← map_mul, ← hAGL,
        ← block_comm_dg hblk ν]
    exact (Commute.zpow_left (show Commute (burnsideB4h_x0 ν) (burnsideB4h_embSL B) from hc) n).eq

theorem burnsideB4h_act_fix_zpowers [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    {x : Matrix.ProjGenLinGroup (Fin 3) F} {M : Matrix (Fin 3) (Fin 3) F}
    (h : burnsideB4h_act k x M = M) {y : Matrix.ProjGenLinGroup (Fin 3) F}
    (hy : y ∈ Subgroup.zpowers x) : burnsideB4h_act k y M = M := by
  let S : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F) :=
    { carrier := {y | burnsideB4h_act k y M = M}
      one_mem' := burnsideB4h_act_one hF k M
      mul_mem' := fun {a b} ha hb => by
        show burnsideB4h_act k (a * b) M = M
        rw [burnsideB4h_act_mul hF, show burnsideB4h_act k b M = M from hb,
          show burnsideB4h_act k a M = M from ha]
      inv_mem' := fun {a} ha => by
        show burnsideB4h_act k a⁻¹ M = M
        conv_lhs => rw [← show burnsideB4h_act k a M = M from ha]
        rw [← burnsideB4h_act_mul hF, inv_mul_cancel, burnsideB4h_act_one hF] }
  exact (Subgroup.zpowers_le.2 (show x ∈ S from h)) hy

theorem burnsideB4h_mem_fixM_iff [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    (k : ℕ) (M : Matrix (Fin 3) (Fin 3) F) :
    M ∈ burnsideB4h_fixM hF k (Subgroup.zpowers (burnsideB4h_x0 ν)) ↔
      M.trace = 0 ∧ ∀ i j, facE k i j % 3 ≠ 0 → M i j = 0 := by
  rw [burnsideB4h_mem_fixM]
  have hx : ∀ N : Matrix (Fin 3) (Fin 3) F,
      burnsideB4h_act k (burnsideB4h_x0 ν) N = N ↔ ∀ i j, facE k i j % 3 ≠ 0 → N i j = 0 := by
    intro N
    rw [burnsideB4h_x0, burnsideB4h_act_mk hF]
    exact fixed_iff (by rw [Nat.card_eq_fintype_card, hF]) hν k N
  constructor
  · rintro ⟨ht, hfix⟩
    exact ⟨ht, (hx M).1 (hfix _ (Subgroup.mem_zpowers _))⟩
  · rintro ⟨ht, hs⟩
    exact ⟨ht, fun y hy => burnsideB4h_act_fix_zpowers hF k ((hx M).2 hs) hy⟩

theorem burnsideB4h_exists_lift {K : Type} [Group K] (a : K →* Matrix.ProjGenLinGroup (Fin 3) F)
    (h : ∀ y, ∃ B : ↥(StatedSL 2 F), burnsideB4h_embSL B = a y) :
    ∃ π : K →* ↥(StatedSL 2 F), ∀ y, burnsideB4h_embSL (π y) = a y := by
  have hr : ∀ y, a y ∈ (burnsideB4h_embSL (F := F)).range := fun y => by
    obtain ⟨B, hB⟩ := h y
    exact ⟨B, hB⟩
  let e : ↥(StatedSL 2 F) ≃* ↥(burnsideB4h_embSL (F := F)).range :=
    MonoidHom.ofInjective burnsideB4h_embSL_injective
  refine ⟨e.symm.toMonoidHom.comp (a.codRestrict (burnsideB4h_embSL (F := F)).range hr),
    fun y => ?_⟩
  have := e.apply_symm_apply (a.codRestrict (burnsideB4h_embSL (F := F)).range hr y)
  exact congrArg Subtype.val this

theorem burnsideB4h_lift_surj [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    {K : Type} [Group K] (a : K →* Matrix.ProjGenLinGroup (Fin 3) F)
    (ha1 : ∀ y, a y ∈ burnsideB4h_C0 ν) (ha2 : ∀ c ∈ burnsideB4h_C0 ν, ∃ y, a y = c) :
    ∃ π : K →* ↥(StatedSL 2 F), (∀ y, burnsideB4h_embSL (π y) = a y) ∧
      Function.Surjective π := by
  obtain ⟨π, hπ⟩ := burnsideB4h_exists_lift a fun y => (burnsideB4h_mem_C0_iff hF hν _).1 (ha1 y)
  refine ⟨π, hπ, fun B => ?_⟩
  obtain ⟨y, hy⟩ := ha2 _ ((burnsideB4h_mem_C0_iff hF hν _).2 ⟨B, rfl⟩)
  exact ⟨y, burnsideB4h_embSL_injective (by rw [hπ, hy])⟩

end C0

section Cases
open scoped TensorProduct

variable {F : Type} [Field F]

@[expose] def burnsideB4h_TensorCase (k : ℕ) {K : Type}
    [Group K] (a : K →* Matrix.ProjGenLinGroup (Fin 3) F)
    (W : Submodule F (Matrix (Fin 3) (Fin 3) F)) : Prop :=
  ∃ π₁ π₂ : K →* ↥(StatedSL 2 F), Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    ∃ Φ : ((Fin 2 → F) ⊗[F] (Fin 2 → F)) →ₗ[F] Matrix (Fin 3) (Fin 3) F,
      Function.Injective Φ ∧ LinearMap.range Φ = W ∧
      (∀ (y : K) (m : (Fin 2 → F) ⊗[F] (Fin 2 → F)),
        Φ (CFSG.ASVolI.ChB.tensActOf π₁ π₂ y m) = burnsideB4h_act k (a y) (Φ m)) ∧
      CFSG.ASVolI.ChB.TensorUniserialTrivEnds π₁ π₂

@[expose] def burnsideB4h_NatCase (k : ℕ) {K : Type}
    [Group K] (a : K →* Matrix.ProjGenLinGroup (Fin 3) F)
    (W : Submodule F (Matrix (Fin 3) (Fin 3) F)) : Prop :=
  ∃ π : K →* ↥(StatedSL 2 F), Function.Surjective π ∧
    ∃ Φ : (Fin 2 → F) →ₗ[F] Matrix (Fin 3) (Fin 3) F,
      Function.Injective Φ ∧ LinearMap.range Φ = W ∧
      ∀ (y : K) (v : Fin 2 → F),
        Φ (((π y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v) =
          burnsideB4h_act k (a y) (Φ v)

@[expose] def burnsideB4h_MStmt (k : ℕ) {K : Type}
    [Group K] (a : K →* Matrix.ProjGenLinGroup (Fin 3) F)
    (W : Submodule F (Matrix (Fin 3) (Fin 3) F)) : Prop :=
  (k = 0 → burnsideB4h_TensorCase k a W) ∧ (k ≠ 0 → burnsideB4h_NatCase k a W)

end Cases

end

section

section NatBase
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]

@[expose] def burnsideB4h_colL : (Fin 2 → F) →ₗ[F] Matrix (Fin 3) (Fin 3) F where
  toFun v := !![0, 0, 0; v 0, 0, 0; v 1, 0, 0]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

@[expose] def burnsideB4h_rowL : (Fin 2 → F) →ₗ[F] Matrix (Fin 3) (Fin 3) F where
  toFun v := !![0, v 0, v 1; 0, 0, 0; 0, 0, 0]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem burnsideB4h_colL_injective : Function.Injective (burnsideB4h_colL (F := F)) := by
  intro v w h
  have h1 := congrFun (congrFun h 1) 0
  have h2 := congrFun (congrFun h 2) 0
  simp [burnsideB4h_colL] at h1 h2
  ext i
  fin_cases i <;> simp [h1, h2]

theorem burnsideB4h_rowL_injective : Function.Injective (burnsideB4h_rowL (F := F)) := by
  intro v w h
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 0) 2
  simp [burnsideB4h_rowL] at h1 h2
  ext i
  fin_cases i <;> simp [h1, h2]

theorem burnsideB4h_blk_col (B C : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    burnsideB4h_blkMat B * burnsideB4h_colL v * burnsideB4h_blkMat C =
      burnsideB4h_colL (B.mulVec v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_blkMat, burnsideB4h_colL, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem burnsideB4h_blk_row (B C : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    burnsideB4h_blkMat B * burnsideB4h_rowL v * burnsideB4h_blkMat C =
      burnsideB4h_rowL ((Matrix.transpose C).mulVec v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_blkMat, burnsideB4h_rowL, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem burnsideB4h_fixM_one [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    (M : Matrix (Fin 3) (Fin 3) F) :
    M ∈ burnsideB4h_fixM hF 1 (Subgroup.zpowers (burnsideB4h_x0 ν)) ↔
      ∃ v : Fin 2 → F, burnsideB4h_colL v = M := by
  rw [burnsideB4h_mem_fixM_iff hF hν]
  constructor
  · rintro ⟨-, hs⟩
    refine ⟨![M 1 0, M 2 0], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideB4h_colL, hs 0 0 (by decide), hs 0 1 (by decide), hs 0 2 (by decide),
        hs 1 1 (by decide), hs 1 2 (by decide), hs 2 1 (by decide), hs 2 2 (by decide)]
  · rintro ⟨v, rfl⟩
    refine ⟨by simp [burnsideB4h_colL, Matrix.trace_fin_three], fun i j h => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [burnsideB4h_colL, facE]

theorem burnsideB4h_fixM_two [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    (M : Matrix (Fin 3) (Fin 3) F) :
    M ∈ burnsideB4h_fixM hF 2 (Subgroup.zpowers (burnsideB4h_x0 ν)) ↔
      ∃ v : Fin 2 → F, burnsideB4h_rowL v = M := by
  rw [burnsideB4h_mem_fixM_iff hF hν]
  constructor
  · rintro ⟨-, hs⟩
    refine ⟨![M 0 1, M 0 2], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideB4h_rowL, hs 0 0 (by decide), hs 1 0 (by decide), hs 1 1 (by decide),
        hs 1 2 (by decide), hs 2 0 (by decide), hs 2 1 (by decide), hs 2 2 (by decide)]
  · rintro ⟨v, rfl⟩
    refine ⟨by simp [burnsideB4h_rowL, Matrix.trace_fin_three], fun i j h => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [burnsideB4h_rowL, facE]

theorem burnsideB4h_natCase_base [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    {k : ℕ} (hk : k < 3) (hk0 : k ≠ 0) {K : Type} [Group K]
    (a : K →* Matrix.ProjGenLinGroup (Fin 3) F) (ha1 : ∀ y, a y ∈ burnsideB4h_C0 ν)
    (ha2 : ∀ c ∈ burnsideB4h_C0 ν, ∃ y, a y = c) :
    burnsideB4h_NatCase k a (burnsideB4h_fixM hF k (Subgroup.zpowers (burnsideB4h_x0 ν))) := by
  obtain ⟨π, hπ, hπs⟩ := burnsideB4h_lift_surj hF hν a ha1 ha2
  have h12 : k = 1 ∨ k = 2 := by omega
  rcases h12 with rfl | rfl
  · refine ⟨π, hπs, burnsideB4h_colL, burnsideB4h_colL_injective, ?_, ?_⟩
    · ext M
      rw [LinearMap.mem_range, burnsideB4h_fixM_one hF hν]
    · intro y v
      rw [← hπ y, burnsideB4h_act_embSL hF, burnsideB4h_blk_col]
  · refine ⟨(burnsideB4h_trInv (F := F)).toMonoidHom.comp π,
      (burnsideB4h_trInv (F := F)).surjective.comp hπs, burnsideB4h_rowL,
      burnsideB4h_rowL_injective, ?_, ?_⟩
    · ext M
      rw [LinearMap.mem_range, burnsideB4h_fixM_two hF hν]
    · intro y v
      rw [← hπ y, burnsideB4h_act_embSL hF, burnsideB4h_blk_row]
      rfl

end NatBase

end

section

section Psi
open scoped TensorProduct

variable {F : Type} [Field F]

@[expose] def burnsideB4h_vmvBil :
    (Fin 2 → F) →ₗ[F] (Fin 2 → F) →ₗ[F] Matrix (Fin 2) (Fin 2) F :=
  LinearMap.mk₂ F (fun x y => Matrix.vecMulVec x y)
    (fun x₁ x₂ y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
    (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
    (fun x y₁ y₂ => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
    (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])

@[expose] def burnsideB4h_PsiL : ((Fin 2 → F) ⊗[F] (Fin 2 → F)) →ₗ[F] Matrix (Fin 2) (Fin 2) F :=
  TensorProduct.lift burnsideB4h_vmvBil

theorem burnsideB4h_PsiL_tmul (x y : Fin 2 → F) :
    burnsideB4h_PsiL (x ⊗ₜ[F] y) = Matrix.vecMulVec x y := by
  simp [burnsideB4h_PsiL, burnsideB4h_vmvBil]

@[expose] def burnsideB4h_LamL : Matrix (Fin 2) (Fin 2) F →ₗ[F] ((Fin 2 → F) ⊗[F] (Fin 2 → F)) where
  toFun N := ∑ i, ∑ j, N i j • ((Pi.single i (1 : F) : Fin 2 → F) ⊗ₜ[F]
    (Pi.single j (1 : F) : Fin 2 → F))
  map_add' N N' := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c N := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

theorem burnsideB4h_PsiL_LamL (N : Matrix (Fin 2) (Fin 2) F) :
    burnsideB4h_PsiL (burnsideB4h_LamL N) = N := by
  simp only [burnsideB4h_LamL, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    burnsideB4h_PsiL_tmul]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.vecMulVec_apply, Pi.single_apply, Finset.sum_apply]

theorem burnsideB4h_PsiL_surjective : Function.Surjective (burnsideB4h_PsiL (F := F)) :=
  fun N => ⟨burnsideB4h_LamL N, burnsideB4h_PsiL_LamL N⟩

theorem burnsideB4h_PsiL_injective : Function.Injective (burnsideB4h_PsiL (F := F)) := by
  have h : Module.finrank F ((Fin 2 → F) ⊗[F] (Fin 2 → F)) =
      Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    rw [Module.finrank_tensorProduct, Module.finrank_matrix]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).2
    burnsideB4h_PsiL_surjective

@[expose] noncomputable def burnsideB4h_Psi :
    ((Fin 2 → F) ⊗[F] (Fin 2 → F)) ≃ₗ[F] Matrix (Fin 2) (Fin 2) F :=
  LinearEquiv.ofBijective burnsideB4h_PsiL ⟨burnsideB4h_PsiL_injective,
    burnsideB4h_PsiL_surjective⟩

theorem burnsideB4h_Psi_apply (m : (Fin 2 → F) ⊗[F] (Fin 2 → F)) :
    burnsideB4h_Psi m = burnsideB4h_PsiL m := rfl

theorem burnsideB4h_Psi_map (A A' : Matrix (Fin 2) (Fin 2) F) (m : (Fin 2 → F) ⊗[F] (Fin 2 → F)) :
    burnsideB4h_Psi (CFSG.ASVolI.ChB.tensAct A (Matrix.transpose A') m) =
      A * burnsideB4h_Psi m * A' := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [burnsideB4h_Psi_apply, CFSG.ASVolI.ChB.tensAct, TensorProduct.map_tmul,
      Matrix.toLin'_apply, burnsideB4h_PsiL_tmul]
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]
  | add m₁ m₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, h₁, h₂, Matrix.mul_add, Matrix.add_mul]

end Psi

section Classify

variable {F : Type} [Field F]

@[expose] def burnsideB4h_ConjInv (S : Submodule F (Matrix (Fin 2) (Fin 2) F)) : Prop :=
  ∀ A A' : Matrix (Fin 2) (Fin 2) F, A * A' = 1 → A' * A = 1 → A.det = 1 →
    ∀ N ∈ S, A * N * A' ∈ S

@[expose] def burnsideB4h_sl2 : Submodule F (Matrix (Fin 2) (Fin 2) F) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F)

@[expose] def burnsideB4h_oneSpan : Submodule F (Matrix (Fin 2) (Fin 2) F) :=
  Submodule.span F {1}

@[expose] def burnsideB4h_Ut (t : F) : Matrix (Fin 2) (Fin 2) F := !![1, t; 0, 1]

@[expose] def burnsideB4h_Lt (t : F) : Matrix (Fin 2) (Fin 2) F := !![1, 0; t, 1]

theorem burnsideB4h_Ut_inv (t : F) :
    burnsideB4h_Ut t * burnsideB4h_Ut (-t) = 1 ∧ burnsideB4h_Ut (-t) * burnsideB4h_Ut t = 1 ∧
      (burnsideB4h_Ut t).det = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideB4h_Ut, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideB4h_Ut, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [burnsideB4h_Ut, Matrix.det_fin_two]

theorem burnsideB4h_Lt_inv (t : F) :
    burnsideB4h_Lt t * burnsideB4h_Lt (-t) = 1 ∧ burnsideB4h_Lt (-t) * burnsideB4h_Lt t = 1 ∧
      (burnsideB4h_Lt t).det = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideB4h_Lt, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideB4h_Lt, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [burnsideB4h_Lt, Matrix.det_fin_two]

theorem burnsideB4h_W_inv :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = 1 ∧
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = 1 ∧
        (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.det_fin_two]

theorem burnsideB4h_uni_exists_omega [Fintype F] (hF : Fintype.card F = 4) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ν, hν⟩ := burnsideB4h_unq_exists_ne_one hF
  have h3 := burnsideB4h_unq_pow_three hF ν
  refine ⟨(ν : F), ?_⟩
  have h3' : (ν : F) ^ 3 = 1 := by simpa using congrArg Units.val h3
  have hν1 : (ν : F) ≠ 1 := fun h => hν (Units.ext h)
  have : ((ν : F) - 1) * ((ν : F) ^ 2 + ν + 1) = 0 := by linear_combination h3'
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν1)

section KeyLemmas

variable {S : Submodule F (Matrix (Fin 2) (Fin 2) F)} (hS : burnsideB4h_ConjInv S)
  (h2 : (2 : F) = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
include hS

theorem burnsideB4h_uni_Ut_mem (t : F) {N : Matrix (Fin 2) (Fin 2) F} (hN : N ∈ S) :
    burnsideB4h_Ut t * N * burnsideB4h_Ut (-t) ∈ S :=
  hS _ _ (burnsideB4h_Ut_inv t).1 (burnsideB4h_Ut_inv t).2.1 (burnsideB4h_Ut_inv t).2.2 N hN

theorem burnsideB4h_uni_Lt_mem (t : F) {N : Matrix (Fin 2) (Fin 2) F} (hN : N ∈ S) :
    burnsideB4h_Lt t * N * burnsideB4h_Lt (-t) ∈ S :=
  hS _ _ (burnsideB4h_Lt_inv t).1 (burnsideB4h_Lt_inv t).2.1 (burnsideB4h_Lt_inv t).2.2 N hN

theorem burnsideB4h_uni_W_mem {N : Matrix (Fin 2) (Fin 2) F} (hN : N ∈ S) :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * N * !![0, -1; 1, 0] ∈ S :=
  hS _ _ burnsideB4h_W_inv.1 burnsideB4h_W_inv.2.1 burnsideB4h_W_inv.2.2 N hN

include h2 hω

theorem burnsideB4h_uni_key1 {N : Matrix (Fin 2) (Fin 2) F} (hN : N ∈ S) :
    N 1 0 • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
  have hN' := hN
  rw [Matrix.eta_fin_two N] at hN'
  have hD1 := sub_mem (burnsideB4h_uni_Ut_mem hS 1 hN') hN'
  have hDω := sub_mem (burnsideB4h_uni_Ut_mem hS ω hN') hN'
  have := add_mem (S.smul_mem ω hD1) hDω
  convert this using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_Ut, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination (-(ω * N 1 0)) * h2
    | linear_combination (N 1 0) * hω + (ω * N 0 0 - ω * N 1 1) * h2
    | linear_combination (ω * N 1 0) * h2

theorem burnsideB4h_uni_key2 {N : Matrix (Fin 2) (Fin 2) F} (hN : N ∈ S) :
    N 0 1 • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
  have hN' := hN
  rw [Matrix.eta_fin_two N] at hN'
  have hD1 := sub_mem (burnsideB4h_uni_Lt_mem hS 1 hN') hN'
  have hDω := sub_mem (burnsideB4h_uni_Lt_mem hS ω hN') hN'
  have := add_mem (S.smul_mem ω hD1) hDω
  convert this using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_Lt, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination (-(ω * N 0 1)) * h2
    | linear_combination (N 0 1) * hω + (ω * N 1 1 - ω * N 0 0) * h2
    | linear_combination (ω * N 0 1) * h2

theorem burnsideB4h_uni_key3 {N : Matrix (Fin 2) (Fin 2) F} (hN : N ∈ S) (hr : N 1 0 = 0) :
    (N 1 1 - N 0 0) • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
  have hN' := hN
  rw [Matrix.eta_fin_two N] at hN'
  have hD1 := sub_mem (burnsideB4h_uni_Ut_mem hS 1 hN') hN'
  convert hD1 using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_Ut, Matrix.mul_apply, Fin.sum_univ_two, hr] <;> ring_nf

theorem burnsideB4h_uni_E12_or_E21 {N : Matrix (Fin 2) (Fin 2) F} (hN : N ∈ S)
    (hns : ¬(N 0 1 = 0 ∧ N 1 0 = 0 ∧ N 0 0 = N 1 1)) :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S ∨
      (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
  by_cases hr : N 1 0 = 0
  · by_cases hq : N 0 1 = 0
    · left
      have hps : N 1 1 - N 0 0 ≠ 0 := by
        intro h
        exact hns ⟨hq, hr, (sub_eq_zero.mp h).symm⟩
      have := S.smul_mem (N 1 1 - N 0 0)⁻¹ (burnsideB4h_uni_key3 hS h2 hω hN hr)
      rwa [smul_smul, inv_mul_cancel₀ hps, one_smul] at this
    · right
      have := S.smul_mem (N 0 1)⁻¹ (burnsideB4h_uni_key2 hS h2 hω hN)
      rwa [smul_smul, inv_mul_cancel₀ hq, one_smul] at this
  · left
    have := S.smul_mem (N 1 0)⁻¹ (burnsideB4h_uni_key1 hS h2 hω hN)
    rwa [smul_smul, inv_mul_cancel₀ hr, one_smul] at this

theorem burnsideB4h_uni_E21_of_E12
    (h : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S) :
    (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
  have hW := burnsideB4h_uni_W_mem hS h
  have e : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 0, 0] * !![0, -1; 1, 0] =
      (-1 : F) • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at hW
  have := S.smul_mem (-1 : F) hW
  rwa [smul_smul, neg_mul, one_mul, neg_neg, one_smul] at this

theorem burnsideB4h_uni_E12_of_E21
    (h : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S) :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
  have hW := burnsideB4h_uni_W_mem hS h
  have e : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 0; 1, 0] * !![0, -1; 1, 0] =
      (-1 : F) • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at hW
  have := S.smul_mem (-1 : F) hW
  rwa [smul_smul, neg_mul, one_mul, neg_neg, one_smul] at this

theorem burnsideB4h_uni_one_mem (hE12 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S)
    (hE21 : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S) :
    (1 : Matrix (Fin 2) (Fin 2) F) ∈ S := by
  have h1 := burnsideB4h_uni_Lt_mem hS 1 hE12
  have := add_mem (sub_mem h1 hE12) hE21
  convert this using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_Lt, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h2

theorem burnsideB4h_uni_sl2_le (hE12 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S)
    (hE21 : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S)
    (hI : (1 : Matrix (Fin 2) (Fin 2) F) ∈ S) : burnsideB4h_sl2 ≤ S := by
  intro M hM
  have hM' : M 0 0 + M 1 1 = 0 := by
    simpa [burnsideB4h_sl2, Matrix.trace_fin_two] using hM
  have e : M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) + M 0 1 • (!![0, 1; 0, 0] :
      Matrix (Fin 2) (Fin 2) F) + M 1 0 • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination hM' - M 0 0 * h2
  rw [e]
  exact add_mem (add_mem (S.smul_mem _ hI) (S.smul_mem _ hE12)) (S.smul_mem _ hE21)

end KeyLemmas

theorem burnsideB4h_uni_classify [Fintype F] (hF : Fintype.card F = 4)
    {S : Submodule F (Matrix (Fin 2) (Fin 2) F)} (hS : burnsideB4h_ConjInv S) :
    S = ⊥ ∨ S = burnsideB4h_oneSpan ∨ S = burnsideB4h_sl2 ∨ S = ⊤ := by
  have h2 := burnsideB4h_unq_two_eq_zero hF
  obtain ⟨ω, hω⟩ := burnsideB4h_uni_exists_omega hF
  by_cases hsc : ∀ N ∈ S, N 0 1 = 0 ∧ N 1 0 = 0 ∧ N 0 0 = N 1 1
  · have hscal : ∀ N ∈ S, N = N 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
      intro N hN
      obtain ⟨h1, h2', h3⟩ := hsc N hN
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2', h3]
    by_cases hbot : ∀ N ∈ S, N = 0
    · left
      exact eq_bot_iff.2 fun N hN => by simp [hbot N hN]
    · right; left
      push Not at hbot
      obtain ⟨N, hN, hN0⟩ := hbot
      have hc0 : N 0 0 ≠ 0 := fun h => by
        have h' := hscal N hN
        rw [h, zero_smul] at h'
        exact hN0 h'
      have h1 : (1 : Matrix (Fin 2) (Fin 2) F) ∈ S := by
        have h := S.smul_mem (N 0 0)⁻¹ hN
        obtain ⟨hq, hr, hps⟩ := hsc N hN
        have e : (N 0 0)⁻¹ • N = (1 : Matrix (Fin 2) (Fin 2) F) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [hq, hr, ← hps, hc0]
        rwa [e] at h
      apply le_antisymm
      · intro M hM
        rw [hscal M hM]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · rw [burnsideB4h_oneSpan, Submodule.span_le]
        simpa using h1
  · push Not at hsc
    obtain ⟨N, hN, hns⟩ := hsc
    have hns' : ¬(N 0 1 = 0 ∧ N 1 0 = 0 ∧ N 0 0 = N 1 1) := fun h =>
      hns h.1 h.2.1 h.2.2
    have hE : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S ∧
        (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
      rcases burnsideB4h_uni_E12_or_E21 hS h2 hω hN hns' with h | h
      · exact ⟨h, burnsideB4h_uni_E21_of_E12 hS h2 hω h⟩
      · exact ⟨burnsideB4h_uni_E12_of_E21 hS h2 hω h, h⟩
    have hI := burnsideB4h_uni_one_mem hS h2 hω hE.1 hE.2
    have hsl := burnsideB4h_uni_sl2_le hS h2 hω hE.1 hE.2 hI
    by_cases htr : ∀ N ∈ S, N 0 0 + N 1 1 = 0
    · right; right; left
      refine le_antisymm (fun M hM => ?_) hsl
      have := htr M hM
      simpa [burnsideB4h_sl2, Matrix.trace_fin_two] using this
    · right; right; right
      push Not at htr
      obtain ⟨N', hN', ht⟩ := htr
      have hE11 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
        have hsub : N' - (N' 0 1 • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) +
            N' 1 0 • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) +
            N' 1 1 • (1 : Matrix (Fin 2) (Fin 2) F)) ∈ S :=
          sub_mem hN' (add_mem (add_mem (S.smul_mem _ hE.1) (S.smul_mem _ hE.2))
            (S.smul_mem _ hI))
        have hne : N' 0 0 - N' 1 1 ≠ 0 := by
          intro h
          apply ht
          linear_combination h + N' 1 1 * h2
        have := S.smul_mem (N' 0 0 - N' 1 1)⁻¹ hsub
        convert this using 1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hne]
      have hE22 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) ∈ S := by
        have := sub_mem hI hE11
        convert this using 1
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [eq_top_iff]
      intro M _
      have e : M = M 0 0 • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) +
          M 0 1 • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) +
          M 1 0 • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) F) +
          M 1 1 • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [e]
      exact add_mem (add_mem (add_mem (S.smul_mem _ hE11) (S.smul_mem _ hE.1))
        (S.smul_mem _ hE.2)) (S.smul_mem _ hE22)

end Classify

section Assembly
open scoped TensorProduct

variable {F : Type} [Field F]

theorem burnsideB4h_oneSpan_le_sl2 (h2 : (2 : F) = 0) :
    (burnsideB4h_oneSpan : Submodule F (Matrix (Fin 2) (Fin 2) F)) ≤ burnsideB4h_sl2 := by
  rw [burnsideB4h_oneSpan, Submodule.span_le]
  intro M hM
  rw [Set.mem_singleton_iff] at hM
  subst hM
  show (Matrix.traceLinearMap (Fin 2) F F) 1 = 0
  rw [Matrix.traceLinearMap_apply, Matrix.trace_one]
  simpa using h2

theorem burnsideB4h_uni_tensorUniserial [Fintype F] (hF : Fintype.card F = 4) {K : Type}
    [Group K] (π₁ : K →* ↥(StatedSL 2 F)) (h₁ : Function.Surjective π₁) :
    CFSG.ASVolI.ChB.TensorUniserialTrivEnds π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) := by
  have h2 := burnsideB4h_unq_two_eq_zero hF
  have hconj : ∀ (k : K) (m : (Fin 2 → F) ⊗[F] (Fin 2 → F)),
      burnsideB4h_Psi (CFSG.ASVolI.ChB.tensActOf π₁
        ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m) =
        ((π₁ k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * burnsideB4h_Psi m *
          (((π₁ k : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro k m
    exact burnsideB4h_Psi_map _ _ m
  have hinv : ∀ A : Submodule F ((Fin 2 → F) ⊗[F] (Fin 2 → F)),
      (∀ k : K, ∀ m ∈ A, CFSG.ASVolI.ChB.tensActOf π₁
        ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m ∈ A) →
      burnsideB4h_ConjInv (A.map (burnsideB4h_Psi (F := F)).toLinearMap) := by
    intro A hA A₀ A₀' e1 e2 hdet N hN
    obtain ⟨m, hm, rfl⟩ := hN
    let g : GL (Fin 2) F := ⟨A₀, A₀', e1, e2⟩
    have hg : g ∈ StatedSL 2 F := by
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
      exact hdet
    obtain ⟨k, hk⟩ := h₁ ⟨g, hg⟩
    refine ⟨_, hA k m hm, ?_⟩
    rw [LinearEquiv.coe_coe, hconj, hk]
    rfl
  set Ψ := (burnsideB4h_Psi (F := F)) with hΨ
  set A₀ : Submodule F ((Fin 2 → F) ⊗[F] (Fin 2 → F)) :=
    (burnsideB4h_oneSpan (F := F)).comap Ψ.toLinearMap with hA₀
  set A₁ : Submodule F ((Fin 2 → F) ⊗[F] (Fin 2 → F)) :=
    (burnsideB4h_sl2 (F := F)).comap Ψ.toLinearMap with hA₁
  have h01 : A₀ ≤ A₁ := Submodule.comap_mono (burnsideB4h_oneSpan_le_sl2 h2)
  have hclass : ∀ A : Submodule F ((Fin 2 → F) ⊗[F] (Fin 2 → F)),
      (∀ k : K, ∀ m ∈ A, CFSG.ASVolI.ChB.tensActOf π₁
        ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m ∈ A) →
      A = ⊥ ∨ A = A₀ ∨ A = A₁ ∨ A = ⊤ := by
    intro A hA
    have hc := burnsideB4h_uni_classify hF (hinv A hA)
    have hA' : A = (A.map Ψ.toLinearMap).comap Ψ.toLinearMap :=
      (Submodule.comap_map_eq_of_injective Ψ.injective A).symm
    rcases hc with h | h | h | h
    · left
      rw [hA', h, Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.2 Ψ.injective
    · right; left
      rw [hA', h]
    · right; right; left
      rw [hA', h]
    · right; right; right
      rw [hA', h, Submodule.comap_top]
  have hcent : ∀ (k : K), ∀ m ∈ A₀, CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m = m := by
    intro k m hm
    apply Ψ.injective
    rw [hconj]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    have hc' : Ψ m = c • (1 : Matrix (Fin 2) (Fin 2) F) := hc.symm
    rw [hc', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]
  have htr : ∀ (k : K) (m : (Fin 2 → F) ⊗[F] (Fin 2 → F)),
      (Ψ (CFSG.ASVolI.ChB.tensActOf π₁
        ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m)).trace = (Ψ m).trace := by
    intro k m
    rw [hconj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨?_, ⟨A₀, ?_, ?_, hcent, ?_⟩, ⟨A₁, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro A B hA hB
    rcases hclass A hA with rfl | rfl | rfl | rfl <;> rcases hclass B hB with rfl | rfl | rfl | rfl <;>
      first
      | exact Or.inl bot_le | exact Or.inr bot_le | exact Or.inl le_top | exact Or.inr le_top
      | exact Or.inl le_rfl | exact Or.inl h01 | exact Or.inr h01
  ·
    intro k m hm
    rw [hcent k m hm]
    exact hm
  ·
    intro h
    have h1 : Ψ.symm 1 ∈ A₀ := by
      show Ψ.toLinearMap (Ψ.symm 1) ∈ burnsideB4h_oneSpan
      simpa [burnsideB4h_oneSpan] using Submodule.subset_span (Set.mem_singleton _)
    rw [h] at h1
    have h0 : Ψ.symm 1 = 0 := h1
    have := congrArg Ψ h0
    simp at this
  ·
    intro A hA hne
    rcases hclass A hA with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact le_rfl
    · exact h01
    · exact le_top
  ·
    intro k m hm
    show Ψ.toLinearMap (CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m) ∈ burnsideB4h_sl2
    have hm' : (Ψ m).trace = 0 := by
      have : Ψ.toLinearMap m ∈ burnsideB4h_sl2 := hm
      simpa [burnsideB4h_sl2] using this
    simp only [burnsideB4h_sl2, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
    rw [show Ψ.toLinearMap (CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m) = Ψ (CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m) from rfl, htr, hm']
  ·
    intro h
    have : Ψ.symm (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ A₁ := by rw [h]; trivial
    have h' : Ψ.toLinearMap (Ψ.symm (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F)) ∈
        burnsideB4h_sl2 := this
    simp [burnsideB4h_sl2, Matrix.trace_fin_two] at h'
  ·
    intro k m
    show Ψ.toLinearMap (CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m - m) ∈ burnsideB4h_sl2
    simp only [burnsideB4h_sl2, LinearMap.mem_ker, Matrix.traceLinearMap_apply, map_sub,
      Matrix.trace_sub]
    rw [show Ψ.toLinearMap (CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m) = Ψ (CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m) from rfl, htr]
    simp
  ·
    intro A hA hne
    rcases hclass A hA with rfl | rfl | rfl | rfl
    · exact bot_le
    · exact h01
    · exact le_rfl
    · exact absurd rfl hne

end Assembly

end

section

section TensorBase
open scoped TensorProduct
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]

@[expose] def burnsideB4h_XiL : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 3) (Fin 3) F where
  toFun N := !![-N.trace, 0, 0; 0, N 0 0, N 0 1; 0, N 1 0, N 1 1]
  map_add' N N' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.trace_add] <;> ring
  map_smul' c N := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.trace_smul]

theorem burnsideB4h_XiL_injective : Function.Injective (burnsideB4h_XiL (F := F)) := by
  intro N N' h
  have e11 := congrFun (congrFun h 1) 1
  have e12 := congrFun (congrFun h 1) 2
  have e21 := congrFun (congrFun h 2) 1
  have e22 := congrFun (congrFun h 2) 2
  simp [burnsideB4h_XiL] at e11 e12 e21 e22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, e12, e21, e22]

theorem burnsideB4h_blk_XiL (B C N : Matrix (Fin 2) (Fin 2) F) (hCB : C * B = 1) :
    burnsideB4h_blkMat B * burnsideB4h_XiL N * burnsideB4h_blkMat C =
      burnsideB4h_XiL (B * N * C) := by
  have htr : (B * N * C).trace = N.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hCB, Matrix.one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB4h_blkMat, burnsideB4h_XiL, Matrix.mul_apply, Fin.sum_univ_three, htr]

theorem burnsideB4h_fixM_zero [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    (M : Matrix (Fin 3) (Fin 3) F) :
    M ∈ burnsideB4h_fixM hF 0 (Subgroup.zpowers (burnsideB4h_x0 ν)) ↔
      ∃ N : Matrix (Fin 2) (Fin 2) F, burnsideB4h_XiL N = M := by
  rw [burnsideB4h_mem_fixM_iff hF hν]
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨!![M 1 1, M 1 2; M 2 1, M 2 2], ?_⟩
    have h01 := hs 0 1 (by decide)
    have h02 := hs 0 2 (by decide)
    have h10 := hs 1 0 (by decide)
    have h20 := hs 2 0 (by decide)
    rw [Matrix.trace_fin_three] at ht
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideB4h_XiL, h01, h02, h10, h20, Matrix.trace_fin_two] <;> linear_combination -ht
  · rintro ⟨N, rfl⟩
    refine ⟨by simp [burnsideB4h_XiL, Matrix.trace_fin_three, Matrix.trace_fin_two], fun i j h => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [burnsideB4h_XiL, facE]

theorem burnsideB4h_Psi_tensActOf {K : Type} [Group K] (π₁ : K →* ↥(StatedSL 2 F)) (k : K)
    (m : (Fin 2 → F) ⊗[F] (Fin 2 → F)) :
    burnsideB4h_Psi (CFSG.ASVolI.ChB.tensActOf π₁
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π₁) k m) =
      ((π₁ k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * burnsideB4h_Psi m *
        (((π₁ k : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  burnsideB4h_Psi_map _ _ m

theorem burnsideB4h_tensorCase_base [Fintype F] (hF : Fintype.card F = 4) {ν : Fˣ} (hν : ν ≠ 1)
    {K : Type} [Group K] (a : K →* Matrix.ProjGenLinGroup (Fin 3) F)
    (ha1 : ∀ y, a y ∈ burnsideB4h_C0 ν) (ha2 : ∀ c ∈ burnsideB4h_C0 ν, ∃ y, a y = c) :
    burnsideB4h_TensorCase 0 a
      (burnsideB4h_fixM hF 0 (Subgroup.zpowers (burnsideB4h_x0 ν))) := by
  obtain ⟨π, hπ, hπs⟩ := burnsideB4h_lift_surj hF hν a ha1 ha2
  refine ⟨π, (burnsideB4h_trInv (F := F)).toMonoidHom.comp π, hπs,
    (burnsideB4h_trInv (F := F)).surjective.comp hπs,
    burnsideB4h_XiL.comp (burnsideB4h_Psi (F := F)).toLinearMap, ?_, ?_, ?_,
    burnsideB4h_uni_tensorUniserial hF π hπs⟩
  · exact burnsideB4h_XiL_injective.comp (burnsideB4h_Psi (F := F)).injective
  · ext M
    rw [LinearMap.mem_range, burnsideB4h_fixM_zero hF hν]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨burnsideB4h_Psi m, rfl⟩
    · rintro ⟨N, rfl⟩
      exact ⟨(burnsideB4h_Psi (F := F)).symm N, by simp⟩
  · intro y m
    rw [← hπ y, burnsideB4h_act_embSL hF]
    show burnsideB4h_XiL (burnsideB4h_Psi (CFSG.ASVolI.ChB.tensActOf π
      ((burnsideB4h_trInv (F := F)).toMonoidHom.comp π) y m)) = _
    have hΦm : (burnsideB4h_XiL.comp (burnsideB4h_Psi (F := F)).toLinearMap) m =
        burnsideB4h_XiL (burnsideB4h_Psi m) := rfl
    rw [hΦm, burnsideB4h_Psi_tensActOf]
    exact (burnsideB4h_blk_XiL ((π y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      (((π y : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) (burnsideB4h_Psi m)
      (Units.inv_mul _)).symm

end TensorBase

end

section

section Transport
open scoped TensorProduct
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]

@[expose] noncomputable def burnsideB4h_cjL (c : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F ≃ₗ[F] Matrix (Fin 3) (Fin 3) F where
  toFun := cj c
  map_add' := cj_add c
  map_smul' t M := by
    simp only [cj, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  invFun := cj c⁻¹
  left_inv := cj_inv_cj c
  right_inv := cj_cj_inv c

@[expose] noncomputable def burnsideB4h_grL :
    Matrix (Fin 3) (Fin 3) F ≃ₗ[F] Matrix (Fin 3) (Fin 3) F where
  toFun := gr
  map_add' := gr_add
  map_smul' t M := gr_smul t M
  invFun := gr
  left_inv := gr_gr
  right_inv := gr_gr

theorem burnsideB4h_act_conj [Fintype F] (hF : Fintype.card F = 4) (k : ℕ) (c : GL (Fin 3) F)
    (y : Matrix.ProjGenLinGroup (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    burnsideB4h_cjL c (burnsideB4h_act k y M) =
      burnsideB4h_act k (Matrix.ProjGenLinGroup.mk c * y * (Matrix.ProjGenLinGroup.mk c)⁻¹)
        (burnsideB4h_cjL c M) := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  rw [← map_inv, ← map_mul, ← map_mul, burnsideB4h_act_mk hF, burnsideB4h_act_mk hF]
  have := cj_twAdj (k := k) c (c * g * c⁻¹) M
  rw [show c⁻¹ * (c * g * c⁻¹) * c = g by group] at this
  exact this

theorem burnsideB4h_act_graph [Fintype F] (hF : Fintype.card F = 4) {k : ℕ} (hk : k < 3)
    (y : Matrix.ProjGenLinGroup (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    burnsideB4h_grL (burnsideB4h_act k y M) =
      burnsideB4h_act ((3 - k) % 3) (graphAut F y) (burnsideB4h_grL M) := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  rw [graphAut_mk, burnsideB4h_act_mk hF, burnsideB4h_act_mk hF]
  have hd : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  show gr (CFSG.Quasithin.H13.Ch4.twAdj k g M) =
    CFSG.Quasithin.H13.Ch4.twAdj ((3 - k) % 3) (thetaGL g) (gr M)
  have hF' : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have := gr_conj (thetaGL g) M
  rw [thetaGL_thetaGL] at this
  have hdk : ((g : Matrix (Fin 3) (Fin 3) F).det) ^ k =
      ((g : Matrix (Fin 3) (Fin 3) F).det)⁻¹ ^ ((3 - k) % 3) := by
    calc ((g : Matrix (Fin 3) (Fin 3) F).det) ^ k
        = (((g : Matrix (Fin 3) (Fin 3) F).det)⁻¹ ^ k)⁻¹ := by rw [inv_pow, inv_inv]
      _ = (((g : Matrix (Fin 3) (Fin 3) F).det) ^ ((3 - k) % 3))⁻¹ := by
        rw [inv_pow_eq hF' hd hk]
      _ = ((g : Matrix (Fin 3) (Fin 3) F).det)⁻¹ ^ ((3 - k) % 3) := by rw [inv_pow]
  rw [CFSG.Quasithin.H13.Ch4.twAdj, CFSG.Quasithin.H13.Ch4.twAdj, gr_smul, this, det_thetaGL, hdk]

@[expose] def burnsideB4h_Intw (k k' : ℕ) (φ : Matrix.ProjGenLinGroup (Fin 3) F ≃*
    Matrix.ProjGenLinGroup (Fin 3) F) (Λ : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] Matrix (Fin 3) (Fin 3) F) :
    Prop :=
  (∀ M, (Λ M).trace = M.trace) ∧ ∀ y M, Λ (burnsideB4h_act k y M) = burnsideB4h_act k' (φ y) (Λ M)

theorem burnsideB4h_Intw_trans {k k' k'' : ℕ} {φ ψ : Matrix.ProjGenLinGroup (Fin 3) F ≃*
    Matrix.ProjGenLinGroup (Fin 3) F} {Λ Λ' : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] Matrix (Fin 3) (Fin 3) F}
    (h : burnsideB4h_Intw k k' φ Λ) (h' : burnsideB4h_Intw k' k'' ψ Λ') :
    burnsideB4h_Intw k k'' (φ.trans ψ) (Λ.trans Λ') :=
  ⟨fun M => by
    show (Λ' (Λ M)).trace = M.trace
    rw [h'.1, h.1], fun y M => by
    show Λ' (Λ (burnsideB4h_act k y M)) = burnsideB4h_act k'' (ψ (φ y)) (Λ' (Λ M))
    rw [h.2, h'.2]⟩

theorem burnsideB4h_Intw_cj [Fintype F] (hF : Fintype.card F = 4) (k : ℕ) (c : GL (Fin 3) F) :
    burnsideB4h_Intw k k (MulAut.conj (Matrix.ProjGenLinGroup.mk c)) (burnsideB4h_cjL c) :=
  ⟨fun M => trace_cj c M, fun y M => by
    rw [burnsideB4h_act_conj hF]
    rfl⟩

theorem burnsideB4h_Intw_graph [Fintype F] (hF : Fintype.card F = 4) {k : ℕ} (hk : k < 3) :
    burnsideB4h_Intw k ((3 - k) % 3) (graphAut F) burnsideB4h_grL :=
  ⟨fun M => trace_gr M, fun y M => burnsideB4h_act_graph hF hk y M⟩

theorem burnsideB4h_MStmt_pullback {k k' : ℕ} (hkk' : k = 0 ↔ k' = 0)
    {φ : Matrix.ProjGenLinGroup (Fin 3) F ≃* Matrix.ProjGenLinGroup (Fin 3) F}
    {Λ : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] Matrix (Fin 3) (Fin 3) F}
    (hΛ : burnsideB4h_Intw k k' φ Λ) {K : Type} [Group K]
    (a : K →* Matrix.ProjGenLinGroup (Fin 3) F) {W' : Submodule F (Matrix (Fin 3) (Fin 3) F)}
    (h : burnsideB4h_MStmt k' (φ.toMonoidHom.comp a) W') :
    burnsideB4h_MStmt k a (W'.comap Λ.toLinearMap) := by
  have hsymm : ∀ (y : Matrix.ProjGenLinGroup (Fin 3) F) (N : Matrix (Fin 3) (Fin 3) F),
      Λ.symm (burnsideB4h_act k' (φ y) N) = burnsideB4h_act k y (Λ.symm N) := by
    intro y N
    apply Λ.injective
    rw [LinearEquiv.apply_symm_apply, hΛ.2, LinearEquiv.apply_symm_apply]
  have hrange : ∀ {E : Type} [AddCommGroup E] [Module F E] (Φ' : E →ₗ[F] Matrix (Fin 3) (Fin 3) F),
      LinearMap.range Φ' = W' →
        LinearMap.range (Λ.symm.toLinearMap.comp Φ') = W'.comap Λ.toLinearMap := by
    intro E _ _ Φ' hr
    ext M
    rw [LinearMap.mem_range, Submodule.mem_comap]
    constructor
    · rintro ⟨m, hm⟩
      have hm' : Λ.symm (Φ' m) = M := hm
      have : Λ.toLinearMap M = Φ' m := by
        rw [← hm']
        exact Λ.apply_symm_apply _
      rw [this, ← hr]
      exact ⟨m, rfl⟩
    · intro hM
      rw [← hr] at hM
      obtain ⟨m, hm⟩ := hM
      exact ⟨m, by
        show Λ.symm (Φ' m) = M
        rw [hm]
        exact Λ.symm_apply_apply M⟩
  refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
  · obtain ⟨π₁, π₂, h1, h2, Φ', hinj, hr, hequiv, hU⟩ := h.1 (hkk'.1 hk0)
    refine ⟨π₁, π₂, h1, h2, Λ.symm.toLinearMap.comp Φ', Λ.symm.injective.comp hinj, hrange _ hr,
      ?_, hU⟩
    intro y m
    show Λ.symm (Φ' (CFSG.ASVolI.ChB.tensActOf π₁ π₂ y m)) =
      burnsideB4h_act k (a y) (Λ.symm (Φ' m))
    rw [hequiv y m]
    exact hsymm (a y) (Φ' m)
  · obtain ⟨π, h1, Φ', hinj, hr, hequiv⟩ := h.2 (fun h0 => hk0 (hkk'.2 h0))
    refine ⟨π, h1, Λ.symm.toLinearMap.comp Φ', Λ.symm.injective.comp hinj, hrange _ hr, ?_⟩
    intro y v
    show Λ.symm (Φ' (((π y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v)) =
      burnsideB4h_act k (a y) (Λ.symm (Φ' v))
    rw [hequiv y v]
    exact hsymm (a y) (Φ' v)

theorem burnsideB4h_fixM_comap [Fintype F] (hF : Fintype.card F = 4) {k k' : ℕ}
    {φ : Matrix.ProjGenLinGroup (Fin 3) F ≃* Matrix.ProjGenLinGroup (Fin 3) F}
    {Λ : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] Matrix (Fin 3) (Fin 3) F}
    (hΛ : burnsideB4h_Intw k k' φ Λ) (Y : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)) :
    burnsideB4h_fixM hF k Y = (burnsideB4h_fixM hF k' (Y.map φ.toMonoidHom)).comap Λ.toLinearMap := by
  ext M
  rw [Submodule.mem_comap, burnsideB4h_mem_fixM, burnsideB4h_mem_fixM]
  show _ ↔ (Λ M).trace = 0 ∧ _
  rw [hΛ.1]
  constructor
  · rintro ⟨ht, hy⟩
    refine ⟨ht, ?_⟩
    rintro _ ⟨y, hyY, rfl⟩
    show burnsideB4h_act k' (φ y) (Λ M) = Λ M
    rw [← hΛ.2, hy y hyY]
  · rintro ⟨ht, hy⟩
    refine ⟨ht, fun y hyY => ?_⟩
    apply Λ.injective
    rw [hΛ.2]
    exact hy _ ⟨y, hyY, rfl⟩

theorem burnsideB4h_comm_map {H : Type} [Group H] (ψ : H ≃* H) {Y L : Subgroup H}
    (h : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∀ y ∈ Y.map ψ.toMonoidHom, ∀ l ∈ L.map ψ.toMonoidHom,
      y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (L.map ψ.toMonoidHom) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨l, hl, rfl⟩
  rw [pCoreOf_map_inj ψ.toMonoidHom ψ.injective]
  exact ⟨y * l * y⁻¹ * l⁻¹, h y hy l hl, by simp⟩

theorem burnsideB4h_map_trans {H : Type} [Group H] (ψ₁ ψ₂ : H ≃* H) (L : Subgroup H) :
    L.map (ψ₁.trans ψ₂).toMonoidHom = (L.map ψ₁.toMonoidHom).map ψ₂.toMonoidHom := by
  rw [show (ψ₁.trans ψ₂).toMonoidHom = ψ₂.toMonoidHom.comp ψ₁.toMonoidHom from
    MonoidHom.ext fun _ => rfl]
  exact (Subgroup.map_map _ _ _).symm

theorem burnsideB4h_card_map_equiv {H : Type} [Group H] (ψ : H ≃* H) (L : Subgroup H) :
    Nat.card (L.map ψ.toMonoidHom) = Nat.card L :=
  Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective

theorem burnsideB4h_normalForm [Fintype F] (hF : Fintype.card F = 4)
    {P'' : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)} (hP : CFSG.Quasithin.IsMaxParabolic2 ⊤ P'')
    {Y : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)} (hY3 : Nat.card Y = 3)
    (hYc : ∀ y ∈ Y, ∀ l ∈ CFSG.Quasithin.perfectCore P'',
      y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (CFSG.Quasithin.perfectCore P'')) :
    ∃ (φ : Matrix.ProjGenLinGroup (Fin 3) F ≃* Matrix.ProjGenLinGroup (Fin 3) F) (ν : Fˣ),
      ν ≠ 1 ∧ (CFSG.Quasithin.perfectCore P'').map φ.toMonoidHom = Ptheta F 0 ∧
      Y.map φ.toMonoidHom = Subgroup.zpowers (burnsideB4h_x0 ν) ∧
      ∀ k : ℕ, k < 3 → ∃ (k' : ℕ) (Λ : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] Matrix (Fin 3) (Fin 3) F),
        k' < 3 ∧ (k = 0 ↔ k' = 0) ∧ burnsideB4h_Intw k k' φ Λ := by
  have hF' : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  haveI : Finite F := Finite.of_fintype F
  haveI : CharP F 2 := burnsideB4h_unq_charP hF
  obtain ⟨c, j, hc⟩ := exists_conj_perfectCore hF' hP
  obtain ⟨c₀, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective c
  have hcomm1 := burnsideB4h_comm_map (MulAut.conj (Matrix.ProjGenLinGroup.mk c₀)) hYc
  rw [hc] at hcomm1
  have hcard1 : Nat.card (Y.map (MulAut.conj (Matrix.ProjGenLinGroup.mk c₀)).toMonoidHom) = 3 := by
    rw [burnsideB4h_card_map_equiv, hY3]
  match j, hc, hcomm1 with
  | 0, hc, hcomm1 =>
    obtain ⟨g, ν, hν, hPg, hYg⟩ := exists_conj_normal hF' hcard1 hcomm1
    refine ⟨(MulAut.conj (Matrix.ProjGenLinGroup.mk c₀)).trans
      (MulAut.conj (Matrix.ProjGenLinGroup.mk g)), ν, hν, ?_, ?_, fun k hk => ?_⟩
    · rw [burnsideB4h_map_trans, hc, hPg]
    · rw [burnsideB4h_map_trans, hYg]
      rfl
    · exact ⟨k, (burnsideB4h_cjL c₀).trans (burnsideB4h_cjL g), hk, Iff.rfl,
        burnsideB4h_Intw_trans (burnsideB4h_Intw_cj hF k c₀) (burnsideB4h_Intw_cj hF k g)⟩
  | 1, hc, hcomm1 =>
    have hcomm2 := burnsideB4h_comm_map (graphAut F) hcomm1
    rw [map_graphAut_Ptheta_one] at hcomm2
    have hcard2 : Nat.card ((Y.map (MulAut.conj (Matrix.ProjGenLinGroup.mk c₀)).toMonoidHom).map
        (graphAut F).toMonoidHom) = 3 := by
      rw [burnsideB4h_card_map_equiv, hcard1]
    obtain ⟨g, ν, hν, hPg, hYg⟩ := exists_conj_normal hF' hcard2 hcomm2
    refine ⟨((MulAut.conj (Matrix.ProjGenLinGroup.mk c₀)).trans (graphAut F)).trans
      (MulAut.conj (Matrix.ProjGenLinGroup.mk g)), ν, hν, ?_, ?_, fun k hk => ?_⟩
    · rw [burnsideB4h_map_trans, burnsideB4h_map_trans, hc, map_graphAut_Ptheta_one, hPg]
    · rw [burnsideB4h_map_trans, burnsideB4h_map_trans, hYg]
      rfl
    · refine ⟨(3 - k) % 3, ((burnsideB4h_cjL c₀).trans burnsideB4h_grL).trans (burnsideB4h_cjL g),
        Nat.mod_lt _ (by norm_num), ?_, ?_⟩
      · constructor <;> intro h <;> omega
      · exact burnsideB4h_Intw_trans (burnsideB4h_Intw_trans (burnsideB4h_Intw_cj hF k c₀)
          (burnsideB4h_Intw_graph hF hk)) (burnsideB4h_Intw_cj hF ((3 - k) % 3) g)

theorem burnsideB4h_mem_centralizer_map {H : Type} [Group H] (φ : H ≃* H) (Y : Subgroup H) (c : H) :
    φ c ∈ Subgroup.centralizer ((Y.map φ.toMonoidHom : Subgroup H) : Set H) ↔
      c ∈ Subgroup.centralizer (Y : Set H) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    have := h (φ z) ⟨z, hz, rfl⟩
    apply φ.injective
    rw [map_mul, map_mul]
    exact this
  · rintro h _ ⟨z, hz, rfl⟩
    show φ z * φ c = φ c * φ z
    rw [← map_mul, ← map_mul, h z hz]

theorem burnsideB4h_model [Fintype F] (hF : Fintype.card F = 4)
    {P'' : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)} (hP : CFSG.Quasithin.IsMaxParabolic2 ⊤ P'')
    {Y : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)} (hY3 : Nat.card Y = 3)
    (hYc : ∀ y ∈ Y, ∀ l ∈ CFSG.Quasithin.perfectCore P'',
      y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (CFSG.Quasithin.perfectCore P''))
    {K : Type} [Group K] (a : K →* Matrix.ProjGenLinGroup (Fin 3) F)
    (ha1 : ∀ y, a y ∈ CFSG.Quasithin.perfectCore P'' ⊓ Subgroup.centralizer (Y : Set _))
    (ha2 : ∀ c ∈ CFSG.Quasithin.perfectCore P'' ⊓ Subgroup.centralizer (Y : Set _),
      ∃ y, a y = c) (k : ℕ) (hk : k < 3) :
    burnsideB4h_MStmt k a (burnsideB4h_fixM hF k Y) := by
  obtain ⟨φ, ν, hν, hL, hY, hΛ⟩ := burnsideB4h_normalForm hF hP hY3 hYc
  obtain ⟨k', Λ, hk', hkk', hI⟩ := hΛ k hk
  have hcent : ∀ c, φ c ∈ Subgroup.centralizer
      ((Subgroup.zpowers (burnsideB4h_x0 ν) : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)) :
        Set (Matrix.ProjGenLinGroup (Fin 3) F)) ↔ c ∈ Subgroup.centralizer (Y : Set _) := by
    intro c
    rw [← hY]
    exact burnsideB4h_mem_centralizer_map φ Y c
  have ha1' : ∀ y, (φ.toMonoidHom.comp a) y ∈ burnsideB4h_C0 ν := fun y => by
    refine ⟨?_, (hcent _).2 (ha1 y).2⟩
    rw [← hL]
    exact ⟨a y, (ha1 y).1, rfl⟩
  have ha2' : ∀ c ∈ burnsideB4h_C0 ν, ∃ y, (φ.toMonoidHom.comp a) y = c := by
    rintro c ⟨hc1, hc2⟩
    rw [← hL] at hc1
    obtain ⟨l, hl, rfl⟩ := hc1
    obtain ⟨y, hy⟩ := ha2 l ⟨hl, (hcent l).1 hc2⟩
    exact ⟨y, by simp [hy]⟩
  have hbase : burnsideB4h_MStmt k' (φ.toMonoidHom.comp a)
      (burnsideB4h_fixM hF k' (Subgroup.zpowers (burnsideB4h_x0 ν))) :=
    ⟨fun h0 => by
      subst h0
      exact burnsideB4h_tensorCase_base hF hν _ ha1' ha2',
     fun h0 => burnsideB4h_natCase_base hF hν hk' h0 _ ha1' ha2'⟩
  have hpull := burnsideB4h_MStmt_pullback hkk' hI a hbase
  rwa [burnsideB4h_fixM_comap hF hI Y, hY]

end Transport

end

section

section VLevel
open scoped TensorProduct
open CFSG.Quasithin CFSG.ASVolI.ChB

variable {V : Type} [CommGroup V] {F : Type} [Field F]

theorem burnsideB4h_mem_sl3_iff {M : Matrix (Fin 3) (Fin 3) F} : M ∈ sl3Sub F ↔ M.trace = 0 := by
  simp [sl3Sub]

theorem burnsideB4h_exists_toV [Fintype F] (hF : Fintype.card F = 4) (X : Subgroup (MulAut V))
    (Y : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)) (k : ℕ)
    (β : V ≃* Multiplicative ↥(sl3Sub F))
    (hfix : ∀ v : V, v ∈ fixV X ↔
      ((Multiplicative.toAdd (β v) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) ∈
        burnsideB4h_fixM hF k Y)
    {E : Type} [AddCommGroup E] [Module F E] (Φ : E →ₗ[F] Matrix (Fin 3) (Fin 3) F)
    (hinj : Function.Injective Φ) (hrange : LinearMap.range Φ = burnsideB4h_fixM hF k Y) :
    ∃ Ψ : Multiplicative E ≃* ↥(fixV X), ∀ m : E,
      ((Multiplicative.toAdd (β ((Ψ (Multiplicative.ofAdd m) : ↥(fixV X)) : V)) :
        ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) = Φ m := by
  have hmem : ∀ m : E, Φ m ∈ burnsideB4h_fixM hF k Y := fun m => hrange ▸ ⟨m, rfl⟩
  have hsl : ∀ m : E, Φ m ∈ sl3Sub F := fun m =>
    burnsideB4h_mem_sl3_iff.2 ((burnsideB4h_mem_fixM hF k Y _).1 (hmem m)).1
  let g : E → V := fun m => β.symm (Multiplicative.ofAdd (⟨Φ m, hsl m⟩ : ↥(sl3Sub F)))
  have hβg : ∀ m, β (g m) = Multiplicative.ofAdd (⟨Φ m, hsl m⟩ : ↥(sl3Sub F)) := fun m =>
    β.apply_symm_apply _
  have hgfix : ∀ m, g m ∈ fixV X := fun m => (hfix _).2 (by
    rw [hβg]
    exact hmem m)
  let f : Multiplicative E →* ↥(fixV X) :=
    { toFun := fun m => ⟨g (Multiplicative.toAdd m), hgfix _⟩
      map_one' := by
        apply Subtype.ext
        show g 0 = 1
        apply β.injective
        rw [hβg, map_one]
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp
      map_mul' := fun m m' => by
        apply Subtype.ext
        show g (Multiplicative.toAdd m + Multiplicative.toAdd m') =
          g (Multiplicative.toAdd m) * g (Multiplicative.toAdd m')
        apply β.injective
        rw [map_mul, hβg, hβg, hβg]
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp }
  have hf_inj : Function.Injective f := by
    intro m m' h
    have h1 : g (Multiplicative.toAdd m) = g (Multiplicative.toAdd m') := congrArg Subtype.val h
    have h2 := congrArg β h1
    rw [hβg, hβg] at h2
    have h3 := congrArg (fun x => ((Multiplicative.toAdd x : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F)) h2
    exact Multiplicative.toAdd.injective (hinj h3)
  have hf_surj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    have hv' := (hfix v).1 hv
    rw [← hrange] at hv'
    obtain ⟨m, hm⟩ := hv'
    refine ⟨Multiplicative.ofAdd m, ?_⟩
    apply Subtype.ext
    show g m = v
    apply β.injective
    rw [hβg]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simpa using hm
  refine ⟨MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩, fun m => ?_⟩
  show ((Multiplicative.toAdd (β (g m)) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) = Φ m
  rw [hβg]
  rfl

theorem burnsideB4h_structure [Finite V] [Fintype F] (hF : Fintype.card F = 4)
    (G : Subgroup (MulAut V)) (α : ↥G ≃* PGL3 F) {P : Subgroup (MulAut V)}
    (hP : IsMaxParabolic2 G P) {X : Subgroup (MulAut V)} (hXP : X ≤ P) (hX3 : Nat.card X = 3)
    (hXc : ∀ x ∈ X, ∀ l ∈ perfectCore P, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (perfectCore P))
    {k : ℕ} (hk : k < 3) {β : V ≃* Multiplicative ↥(sl3Sub F)}
    (hβ : TwAdjointIntertwines G α.toMonoidHom k β) :
    (k = 0 → IsTensorOfNaturalsUniserialVia β
      (perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) (fixV X)) ∧
    (k ≠ 0 → IsNaturalSL2ViaAdjoint β
      (perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) (fixV X)) := by
  let α' : ↥G ≃* Matrix.ProjGenLinGroup (Fin 3) F := α
  have hPG : P ≤ G := burnsideB4h_le_of_isMaxParabolic2 hP
  have hXG : X ≤ G := hXP.trans hPG
  have hKG : perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V)) ≤ G :=
    inf_le_left.trans ((perfectCore_le P).trans hPG)
  have hP''max : IsMaxParabolic2 ⊤ (burnsideB4h_img G α' P) := burnsideB4h_img_maxParabolic hP
  have hL'' : burnsideB4h_img G α' (perfectCore P) = perfectCore (burnsideB4h_img G α' P) :=
    burnsideB4h_img_perfectCore hPG
  have hY3 : Nat.card (burnsideB4h_img G α' X) = 3 := by
    rw [burnsideB4h_card_img hXG, hX3]
  have hYc : ∀ y ∈ burnsideB4h_img G α' X, ∀ l ∈ perfectCore (burnsideB4h_img G α' P),
      y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (perfectCore (burnsideB4h_img G α' P)) := by
    intro y hy l hl
    rw [← hL''] at hl
    obtain ⟨g, hgX, rfl⟩ := burnsideB4h_mem_img.1 hy
    obtain ⟨g₂, hg₂, rfl⟩ := burnsideB4h_mem_img.1 hl
    rw [← hL'', ← burnsideB4h_img_pCoreOf ((perfectCore_le P).trans hPG)]
    refine burnsideB4h_mem_img.2 ⟨g * g₂ * g⁻¹ * g₂⁻¹, ?_, by simp⟩
    exact hXc _ hgX _ hg₂
  let a : ↥(perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) →*
      Matrix.ProjGenLinGroup (Fin 3) F := α'.toMonoidHom.comp (Subgroup.inclusion hKG)
  have hC : burnsideB4h_img G α' (perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) =
      perfectCore (burnsideB4h_img G α' P) ⊓
        Subgroup.centralizer ((burnsideB4h_img G α' X : Subgroup _) : Set _) := by
    rw [burnsideB4h_img_centralizer _ hXG, hL'']
  have ha1 : ∀ y, a y ∈ perfectCore (burnsideB4h_img G α' P) ⊓
      Subgroup.centralizer ((burnsideB4h_img G α' X : Subgroup _) : Set _) := fun y => by
    rw [← hC]
    exact burnsideB4h_mem_img.2 ⟨Subgroup.inclusion hKG y, y.2, rfl⟩
  have ha2 : ∀ c ∈ perfectCore (burnsideB4h_img G α' P) ⊓
      Subgroup.centralizer ((burnsideB4h_img G α' X : Subgroup _) : Set _), ∃ y, a y = c := by
    intro c hc
    rw [← hC] at hc
    obtain ⟨g, hg, rfl⟩ := burnsideB4h_mem_img.1 hc
    exact ⟨⟨g, hg⟩, rfl⟩
  have hmodel := burnsideB4h_model hF hP''max hY3 hYc a ha1 ha2 k hk
  have hact : ∀ (g : ↥G) (v : V),
      ((Multiplicative.toAdd (β ((g : MulAut V) v)) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) =
        burnsideB4h_act k (α' g)
          ((Multiplicative.toAdd (β v) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) := by
    intro g v
    exact hβ g v (Matrix.ProjGenLinGroup.mk_surjective (α' g)).choose
      (Matrix.ProjGenLinGroup.mk_surjective (α' g)).choose_spec
  have hfix : ∀ v : V, v ∈ fixV X ↔
      ((Multiplicative.toAdd (β v) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) ∈
        burnsideB4h_fixM hF k (burnsideB4h_img G α' X) := by
    intro v
    rw [burnsideB4h_mem_fixM]
    have htr : ((Multiplicative.toAdd (β v) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F).trace = 0 :=
      burnsideB4h_mem_sl3_iff.1 (Multiplicative.toAdd (β v)).2
    constructor
    · intro hv
      refine ⟨htr, ?_⟩
      intro y hy
      obtain ⟨g, hgX, rfl⟩ := burnsideB4h_mem_img.1 hy
      rw [← hact g v]
      have h1 : (g : MulAut V) v = v := hv _ hgX
      rw [h1]
    · rintro ⟨-, hy⟩ x hx
      have hxG := hXG hx
      have h1 := hact ⟨x, hxG⟩ v
      rw [hy _ (burnsideB4h_mem_img.2 ⟨⟨x, hxG⟩, hx, rfl⟩)] at h1
      apply β.injective
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact h1
  refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
  · obtain ⟨π₁, π₂, h1, h2, Φ, hinj, hrange, hequiv, hU⟩ := hmodel.1 hk0
    obtain ⟨Ψ, hΨ⟩ := burnsideB4h_exists_toV hF X (burnsideB4h_img G α' X) k β hfix Φ hinj hrange
    refine ⟨π₁, π₂, h1, h2, Ψ, ?_, ?_, hU⟩
    · intro y m
      apply β.injective
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      have h3 := hact ⟨y, hKG y.2⟩ ((Ψ (Multiplicative.ofAdd m) : ↥(fixV X)) : V)
      rw [hΨ] at h3
      rw [hΨ, hequiv y m]
      exact h3.symm
    · intro c m
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      simp only [toAdd_ofAdd, Submodule.coe_smul, hΨ, map_smul]
  · obtain ⟨π, h1, Φ, hinj, hrange, hequiv⟩ := hmodel.2 hk0
    obtain ⟨Ψ, hΨ⟩ := burnsideB4h_exists_toV hF X (burnsideB4h_img G α' X) k β hfix Φ hinj hrange
    refine ⟨π, h1, Ψ, ?_, ?_⟩
    · intro y v
      apply β.injective
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      have h3 := hact ⟨y, hKG y.2⟩ ((Ψ (Multiplicative.ofAdd v) : ↥(fixV X)) : V)
      rw [hΨ] at h3
      have hnat : natAct (StatedSL 2 F) (π y) (Multiplicative.ofAdd v) =
          Multiplicative.ofAdd (((π y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v) := rfl
      rw [hnat, hΨ]
      exact (hequiv y v).trans h3.symm
    · intro c m
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      simp only [toAdd_ofAdd, Submodule.coe_smul, hΨ, map_smul]

end VLevel

end

section

section NatBridge
open CFSG.Quasithin

theorem burnsideB4h_cls_nat_unpack {Q : Type} [CommGroup Q] (H : Subgroup (MulAut Q))
    (hnat : BinaryNaturalSL H ⊤ ⊥ 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ (π : ↥(StatedSL 2 K) →* ↥H) (T : Q ≃* Multiplicative (Fin 2 → K)),
        Function.Surjective π ∧
        ∀ (γ : ↥(StatedSL 2 K)) (q : Q),
          T (((π γ : ↥H) : MulAut Q) q) = Multiplicative.ofAdd
            (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
              (Multiplicative.toAdd (T q))) := by
  obtain ⟨K, hKf, hKfin, hcard, π, hsurj, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  refine ⟨K, hKf, hKfin, by rw [hcard]; norm_num, π, ?_⟩
  let D := FFModel.nat (StatedSL 2 K)
  let ev : (↥D.sec ⧸ D.ker.subgroupOf D.sec) →* Multiplicative (Fin 2 → K) :=
    QuotientGroup.lift (D.ker.subgroupOf D.sec) D.sec.subtype (by
      intro x hx
      have h1 : (x : D.Amb) ∈ D.ker := hx
      have h2 : D.ker = ⊥ := rfl
      rw [h2, Subgroup.mem_bot] at h1
      exact h1)
  have hev : ∀ m : ↥D.sec, ev (QuotientGroup.mk m) = (m : D.Amb) :=
    fun m => rfl
  let T0 : ↥(⊤ : Subgroup Q) →* Multiplicative (Fin 2 → K) := ev.comp β
  have hT0eq : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥(⊤ : Subgroup Q)),
      T0 ⟨((π γ : ↥H) : MulAut Q) (u : Q), Subgroup.mem_top _⟩ =
        Multiplicative.ofAdd (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
          (Multiplicative.toAdd (T0 u))) := by
    intro γ u
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h := hβe γ u m (Subgroup.mem_top _) (Subgroup.mem_top _) hm.symm
    have hT0u : T0 u = (m : D.Amb) := by
      show ev (β u) = _
      rw [← hm]
      rfl
    show ev (β ⟨((π γ : ↥H) : MulAut Q) (u : Q), Subgroup.mem_top _⟩) = _
    rw [h, hT0u]
    rfl
  have hT0inj : Function.Injective T0 := by
    rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 : (m : D.Amb) = 1 := by
      have : T0 u = (m : D.Amb) := by
        show ev (β u) = _
        rw [← hm]
        rfl
      rw [← this]
      exact hu
    have h2 : m = 1 := Subtype.ext h1
    have h3 : β u = 1 := by rw [← hm, h2]; rfl
    have h4 := (hβk u).1 h3
    exact Subtype.ext (Subgroup.mem_bot.1 h4)
  have hT0surj : Function.Surjective T0 := by
    intro x
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (⟨x, Subgroup.mem_top _⟩ : ↥D.sec))
    exact ⟨u, by
      show ev (β u) = x
      rw [hu]
      rfl⟩
  refine ⟨(Subgroup.topEquiv (G := Q)).symm.trans (MulEquiv.ofBijective T0 ⟨hT0inj, hT0surj⟩),
    hsurj, fun γ q => ?_⟩
  exact hT0eq γ ⟨q, Subgroup.mem_top _⟩

@[expose] def burnsideB4h_cls_nat_mapSL {R S : Type} [Field R] [Field S] (f : R →+* S) :
    ↥(StatedSL 2 R) →* ↥(StatedSL 2 S) :=
  ((Matrix.GeneralLinearGroup.map f).comp (StatedSL 2 R).subtype).codRestrict (StatedSL 2 S)
    (fun γ => by
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
      have h1 : ((γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = 1 :=
        CFSG.Open.StatedAPI.det_of_mem_statedSL γ.2
      show (f.mapMatrix ((γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)).det = 1
      rw [← RingHom.map_det, h1, map_one])

theorem burnsideB4h_cls_nat_coe_mapSL {R S : Type} [Field R] [Field S] (f : R →+* S)
    (γ : ↥(StatedSL 2 R)) :
    (((burnsideB4h_cls_nat_mapSL f γ : ↥(StatedSL 2 S)) : GL (Fin 2) S) :
      Matrix (Fin 2) (Fin 2) S) = ((γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map f := rfl

theorem burnsideB4h_cls_nat_field {Q : Type} [CommGroup Q] (H : Subgroup (MulAut Q)) {K F : Type}
    [Field K] [Field F] (e : K ≃+* F) (π : ↥(StatedSL 2 K) →* ↥H)
    (T : Q ≃* Multiplicative (Fin 2 → K)) (hπ : Function.Surjective π)
    (hT : ∀ (γ : ↥(StatedSL 2 K)) (q : Q),
      T (((π γ : ↥H) : MulAut Q) q) = Multiplicative.ofAdd
        (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (T q)))) :
    ∃ (π' : ↥(StatedSL 2 F) →* ↥H) (T' : Q ≃* Multiplicative (Fin 2 → F)),
      Function.Surjective π' ∧
      ∀ (γ : ↥(StatedSL 2 F)) (q : Q),
        T' (((π' γ : ↥H) : MulAut Q) q) = Multiplicative.ofAdd
          (((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (T' q))) := by
  have hmm : ∀ γ : ↥(StatedSL 2 F),
      (((burnsideB4h_cls_nat_mapSL (e.symm : F →+* K) γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).map (e : K →+* F) =
        ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro γ
    ext i j
    simp [burnsideB4h_cls_nat_coe_mapSL]
  have hsurj : Function.Surjective (burnsideB4h_cls_nat_mapSL (e.symm : F →+* K)) := by
    intro γ
    refine ⟨burnsideB4h_cls_nat_mapSL (e : K →+* F) γ, ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [burnsideB4h_cls_nat_coe_mapSL]
  let mapVec : Multiplicative (Fin 2 → K) ≃* Multiplicative (Fin 2 → F) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ : Fin 2 => e.toAddEquiv)
  refine ⟨π.comp (burnsideB4h_cls_nat_mapSL (e.symm : F →+* K)), T.trans mapVec,
    hπ.comp hsurj, fun γ q => ?_⟩
  show mapVec (T (((π (burnsideB4h_cls_nat_mapSL (e.symm : F →+* K) γ) : ↥H) : MulAut Q) q)) = _
  rw [hT]
  apply Multiplicative.toAdd.injective
  funext i
  show e _ = _
  have h := RingHom.map_mulVec (e : K →+* F)
    (((burnsideB4h_cls_nat_mapSL (e.symm : F →+* K) γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) (Multiplicative.toAdd (T q)) i
  rw [hmm] at h
  exact h

section Induced

variable {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) (C₁ C₂ : Subgroup V)
  (hC₁ : ∀ h ∈ H, ∀ c ∈ C₁, h c ∈ C₁) (hC₂ : ∀ h ∈ H, ∀ c ∈ C₂, h c ∈ C₂)
include hC₂

@[expose] def burnsideB4h_cls_nat_resC (h : ↥H) : ↥C₂ ≃* ↥C₂ where
  toFun u := ⟨(h : MulAut V) u, hC₂ h h.2 u u.2⟩
  invFun u := ⟨((h⁻¹ : ↥H) : MulAut V) u, hC₂ _ (h⁻¹).2 u u.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)
  map_mul' u u' := Subtype.ext (map_mul _ _ _)

omit hC₂
include hC₁ hC₂

@[expose] def burnsideB4h_cls_nat_indQ (h : ↥H) :
    (↥C₂ ⧸ C₁.subgroupOf C₂) ≃* (↥C₂ ⧸ C₁.subgroupOf C₂) :=
  QuotientGroup.congr (C₁.subgroupOf C₂) (C₁.subgroupOf C₂)
    (burnsideB4h_cls_nat_resC H C₂ hC₂ h) (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hC₁ h h.2 y hy
      · intro hx
        refine ⟨(burnsideB4h_cls_nat_resC H C₂ hC₂ h).symm x, ?_, by simp⟩
        exact hC₁ _ (h⁻¹).2 x hx)

theorem burnsideB4h_cls_nat_indQ_mk (h : ↥H) (u : ↥C₂) :
    burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ h (QuotientGroup.mk u) =
      QuotientGroup.mk ⟨(h : MulAut V) u, hC₂ h h.2 u u.2⟩ :=
  QuotientGroup.congr_mk _ _ _ _ u

@[expose] def burnsideB4h_cls_nat_psi : ↥H →* MulAut (↥C₂ ⧸ C₁.subgroupOf C₂) where
  toFun h := burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ h
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H u => exact burnsideB4h_cls_nat_indQ_mk H C₁ C₂ hC₁ hC₂ 1 u
  map_mul' h h' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      show burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ (h * h') (QuotientGroup.mk u) =
        burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ h
          (burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ h' (QuotientGroup.mk u))
      rw [burnsideB4h_cls_nat_indQ_mk, burnsideB4h_cls_nat_indQ_mk, burnsideB4h_cls_nat_indQ_mk]
      rfl

theorem burnsideB4h_cls_nat_induced :
    ∃ ψ : ↥H →* ↥(CFSG.ASVolI.ChB.autSec H C₂ C₁), Function.Surjective ψ ∧
      ∀ (h : ↥H) (u v : ↥C₂), (v : V) = (h : MulAut V) (u : V) →
        ((ψ h : ↥(CFSG.ASVolI.ChB.autSec H C₂ C₁)) : MulAut (↥C₂ ⧸ C₁.subgroupOf C₂))
          (QuotientGroup.mk u) = QuotientGroup.mk v := by
  have hmem : ∀ h : ↥H, burnsideB4h_cls_nat_psi H C₁ C₂ hC₁ hC₂ h ∈
      CFSG.ASVolI.ChB.autSec H C₂ C₁ := by
    intro h
    refine ⟨(h : MulAut V), h.2, ?_, ?_, ?_⟩
    · exact CFSG.Quasithin.mem_stabSub_of_invariant (hC₂ h h.2)
        (hC₂ ((h : MulAut V)⁻¹) (H.inv_mem h.2))
    · exact CFSG.Quasithin.mem_stabSub_of_invariant (hC₁ h h.2)
        (hC₁ ((h : MulAut V)⁻¹) (H.inv_mem h.2))
    · intro w w' hw
      have hw' : w' = ⟨(h : MulAut V) w, hC₂ h h.2 w w.2⟩ := Subtype.ext hw
      show burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ h (QuotientGroup.mk w) = QuotientGroup.mk w'
      rw [burnsideB4h_cls_nat_indQ_mk, hw']
  refine ⟨(burnsideB4h_cls_nat_psi H C₁ C₂ hC₁ hC₂).codRestrict
    (CFSG.ASVolI.ChB.autSec H C₂ C₁) hmem, ?_, ?_⟩
  · rintro ⟨φ, g, hgH, -, -, hgφ⟩
    refine ⟨⟨g, hgH⟩, Subtype.ext (MulEquiv.ext fun x => ?_)⟩
    induction x using QuotientGroup.induction_on with
    | H u =>
      show burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ ⟨g, hgH⟩ (QuotientGroup.mk u) = φ _
      rw [burnsideB4h_cls_nat_indQ_mk]
      exact (hgφ u ⟨g u, hC₂ g hgH u u.2⟩ rfl).symm
  · intro h u v hv
    show burnsideB4h_cls_nat_indQ H C₁ C₂ hC₁ hC₂ h (QuotientGroup.mk u) = QuotientGroup.mk v
    rw [burnsideB4h_cls_nat_indQ_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext hv.symm)

end Induced

theorem burnsideB4h_cls_nat_bridge {V : Type} [CommGroup V] {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) (H : Subgroup (MulAut V)) (C₁ C₂ : Subgroup V) (h12 : C₁ ≤ C₂)
    (hC₁ : ∀ h ∈ H, ∀ c ∈ C₁, h c ∈ C₁) (hC₂ : ∀ h ∈ H, ∀ c ∈ C₂, h c ∈ C₂)
    (hnat : BinaryNaturalSL (CFSG.ASVolI.ChB.autSec H C₂ C₁) ⊤ ⊥ 2 2) :
    ∃ (α : ↥H →* ↥(StatedSL 2 F)) (β : ↥C₂ →* Multiplicative (Fin 2 → F)),
      Function.Surjective α ∧ Function.Surjective β ∧ β.ker = C₁.subgroupOf C₂ ∧
      ∀ (h : ↥H) (u v : ↥C₂), (v : V) = (h : MulAut V) (u : V) →
        Multiplicative.toAdd (β v) =
          ((α h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
            (Multiplicative.toAdd (β u)) := by
  obtain ⟨K, hKf, hKfin, hcard, π, T, hπ, hT⟩ := burnsideB4h_cls_nat_unpack _ hnat
  letI := hKf
  haveI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hcard, hF]
  obtain ⟨π', T', hπ', hT'⟩ := burnsideB4h_cls_nat_field _ (FiniteField.ringEquivOfCardEq hKF) π T
    hπ hT
  have hπ'inj : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hmv : ∀ v : Fin 2 → F,
        ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v = v := by
      intro v
      obtain ⟨q, hq⟩ := T'.surjective (Multiplicative.ofAdd v)
      have h1 := hT' γ q
      simp only [hγ, OneMemClass.coe_one, MulAut.one_apply] at h1
      rw [hq, toAdd_ofAdd] at h1
      exact (Multiplicative.ofAdd.injective h1).symm
    have hmat : ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      simp [Matrix.toLin'_apply, hmv]
    exact Subtype.ext (Units.ext hmat)
  let πE : ↥(StatedSL 2 F) ≃* ↥(CFSG.ASVolI.ChB.autSec H C₂ C₁) :=
    MulEquiv.ofBijective π' ⟨hπ'inj, hπ'⟩
  obtain ⟨ψ, hψs, hψ⟩ := burnsideB4h_cls_nat_induced H C₁ C₂ hC₁ hC₂
  refine ⟨πE.symm.toMonoidHom.comp ψ,
    T'.toMonoidHom.comp (QuotientGroup.mk' (C₁.subgroupOf C₂)), ?_, ?_, ?_, ?_⟩
  · exact πE.symm.surjective.comp hψs
  · exact T'.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    rw [MonoidHom.mem_ker]
    show T' (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff _ T'.injective, QuotientGroup.eq_one_iff]
  · intro h u v hv
    have h1 := hψ h u v hv
    have hπα : π' (πE.symm (ψ h)) = ψ h := πE.apply_symm_apply (ψ h)
    show Multiplicative.toAdd (T' (QuotientGroup.mk v)) = _
    rw [← h1]
    have h2 := hT' (πE.symm (ψ h)) (QuotientGroup.mk u)
    rw [hπα] at h2
    rw [h2]
    rfl

end NatBridge

end

section

section Semi

open SemidirectProduct

variable {V : Type} [CommGroup V] (G : Subgroup (MulAut V))

abbrev burnsideB4h_Amb : Type := V ⋊[G.subtype] ↥G

@[expose] def burnsideB4h_V0 : Subgroup (burnsideB4h_Amb G) :=
  (inl : V →* burnsideB4h_Amb G).range

@[expose] def burnsideB4h_Gam : Subgroup (burnsideB4h_Amb G) :=
  (inr : ↥G →* burnsideB4h_Amb G).range

@[expose] def burnsideB4h_lift (A : Subgroup (MulAut V)) : Subgroup (burnsideB4h_Amb G) :=
  (A.subgroupOf G).map (inr : ↥G →* burnsideB4h_Amb G)

variable {G}

theorem burnsideB4h_inr_mul_inl (g : ↥G) (v : V) :
    (inr g : burnsideB4h_Amb G) * inl v * (inr g)⁻¹ = inl ((g : MulAut V) v) := by
  rw [← map_inv]
  exact (inl_aut (φ := G.subtype) g v).symm

theorem burnsideB4h_eq_inl {x : burnsideB4h_Amb G} (hx : x ∈ burnsideB4h_V0 G) :
    x = inl x.left := by
  obtain ⟨v, rfl⟩ := hx
  rfl

theorem burnsideB4h_right_of_V0 {x : burnsideB4h_Amb G} (hx : x ∈ burnsideB4h_V0 G) :
    x.right = 1 := by
  obtain ⟨v, rfl⟩ := hx
  rfl

theorem burnsideB4h_inl_mem (v : V) : (inl v : burnsideB4h_Amb G) ∈ burnsideB4h_V0 G := ⟨v, rfl⟩

theorem burnsideB4h_inr_mem (g : ↥G) : (inr g : burnsideB4h_Amb G) ∈ burnsideB4h_Gam G := ⟨g, rfl⟩

theorem burnsideB4h_mem_lift {A : Subgroup (MulAut V)} {x : burnsideB4h_Amb G} :
    x ∈ burnsideB4h_lift G A ↔ ∃ g : ↥G, (g : MulAut V) ∈ A ∧ inr g = x := by
  unfold burnsideB4h_lift
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem burnsideB4h_lift_le_Gam (A : Subgroup (MulAut V)) :
    burnsideB4h_lift G A ≤ burnsideB4h_Gam G := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := burnsideB4h_mem_lift.1 hx
  exact burnsideB4h_inr_mem g

theorem burnsideB4h_rightHom_mem {A : Subgroup (MulAut V)} {x : burnsideB4h_Amb G}
    (hx : x ∈ burnsideB4h_lift G A) :
    (((rightHom : burnsideB4h_Amb G →* ↥G) x : ↥G) : MulAut V) ∈ A := by
  obtain ⟨g, hg, rfl⟩ := burnsideB4h_mem_lift.1 hx
  rwa [rightHom_inr]

instance burnsideB4h_V0_normal : (burnsideB4h_V0 G).Normal := by
  unfold burnsideB4h_V0
  rw [range_inl_eq_ker_rightHom]
  exact MonoidHom.normal_ker _

instance burnsideB4h_finite_Amb [Finite V] [Finite ↥G] : Finite (burnsideB4h_Amb G) :=
  Finite.of_equiv (V × ↥G) (SemidirectProduct.equivProd (N := V) (G := ↥G) (φ := G.subtype)).symm

variable {R : Type} [Group R]

@[expose] def burnsideB4h_alpha0 (α : ↥G ≃* R) : ↥(burnsideB4h_Gam G) →* R :=
  α.toMonoidHom.comp ((rightHom : burnsideB4h_Amb G →* ↥G).comp (burnsideB4h_Gam G).subtype)

theorem burnsideB4h_alpha0_apply (α : ↥G ≃* R) (x : ↥(burnsideB4h_Gam G)) :
    burnsideB4h_alpha0 α x = α (rightHom (x : burnsideB4h_Amb G)) := rfl

theorem burnsideB4h_map_lift (α : ↥G ≃* R) (A : Subgroup (MulAut V)) :
    ((burnsideB4h_lift G A).subgroupOf (burnsideB4h_Gam G)).map (burnsideB4h_alpha0 α) =
      burnsideB4h_img G α A := by
  ext y
  rw [burnsideB4h_mem_img]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, hg, hgx⟩ := burnsideB4h_mem_lift.1 hx
    refine ⟨g, hg, ?_⟩
    have hgx' : (x : burnsideB4h_Amb G) = inr g := hgx.symm
    rw [burnsideB4h_alpha0_apply, hgx', rightHom_inr]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨inr g, burnsideB4h_inr_mem g⟩, ?_, ?_⟩
    · exact burnsideB4h_mem_lift.2 ⟨g, hg, rfl⟩
    · rw [burnsideB4h_alpha0_apply]
      show α (rightHom (inr g : burnsideB4h_Amb G)) = α g
      rw [rightHom_inr]

end Semi

end

section

section HypNat

open SemidirectProduct CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}

theorem burnsideB4h_comap_inv {A : Subgroup (MulAut V)} {C : Subgroup (burnsideB4h_Amb G)}
    (hN : burnsideB4h_lift G A ≤ Subgroup.normalizer (C : Set (burnsideB4h_Amb G)))
    {l : MulAut V} (hl : l ∈ A) (hlG : l ∈ G) {c : V} (hc : (inl c : burnsideB4h_Amb G) ∈ C) :
    (inl (l c) : burnsideB4h_Amb G) ∈ C := by
  have hg : (inr ⟨l, hlG⟩ : burnsideB4h_Amb G) ∈ burnsideB4h_lift G A :=
    burnsideB4h_mem_lift.2 ⟨⟨l, hlG⟩, hl, rfl⟩
  have h := (Subgroup.mem_normalizer_iff.1 (hN hg) (inl c)).1 hc
  rw [burnsideB4h_inr_mul_inl] at h
  exact h

@[expose] def burnsideB4h_restr (A : Subgroup (MulAut V)) :
    ↥(burnsideB4h_lift G A) →* ↥A where
  toFun x := ⟨((rightHom (x : burnsideB4h_Amb G) : ↥G) : MulAut V), burnsideB4h_rightHom_mem x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

theorem burnsideB4h_restr_surjective {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    Function.Surjective (burnsideB4h_restr (G := G) A) := by
  intro p
  refine ⟨⟨inr ⟨(p : MulAut V), hA p.2⟩, burnsideB4h_mem_lift.2 ⟨⟨(p : MulAut V), hA p.2⟩, p.2, rfl⟩⟩,
    ?_⟩
  apply Subtype.ext
  show ((rightHom (inr ⟨(p : MulAut V), hA p.2⟩ : burnsideB4h_Amb G) : ↥G) : MulAut V) = _
  rw [rightHom_inr]

@[expose] def burnsideB4h_leftHom (C : Subgroup (burnsideB4h_Amb G)) (hC : C ≤ burnsideB4h_V0 G) :
    ↥C →* ↥(C.comap (inl : V →* burnsideB4h_Amb G)) where
  toFun x := ⟨(x : burnsideB4h_Amb G).left, by
    show (inl (x : burnsideB4h_Amb G).left : burnsideB4h_Amb G) ∈ C
    rw [← burnsideB4h_eq_inl (hC x.2)]
    exact x.2⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    show ((x : burnsideB4h_Amb G) * (y : burnsideB4h_Amb G)).left = _
    rw [SemidirectProduct.mul_left, burnsideB4h_right_of_V0 (hC x.2)]
    rfl

theorem burnsideB4h_leftHom_surjective (C : Subgroup (burnsideB4h_Amb G))
    (hC : C ≤ burnsideB4h_V0 G) : Function.Surjective (burnsideB4h_leftHom C hC) := by
  intro d
  refine ⟨⟨inl (d : V), d.2⟩, ?_⟩
  apply Subtype.ext
  rfl

variable {F : Type} [Field F] [Fintype F]

theorem burnsideB4h_hyp_natural (hF : Fintype.card F = 4) {P : Subgroup (MulAut V)}
    (hPG : perfectCore P ≤ G)
    (hstar : ∀ C₁ C₂ : Subgroup V, C₁ < C₂ →
        (∀ l ∈ perfectCore P, ∀ c ∈ C₁, l c ∈ C₁) → (∀ l ∈ perfectCore P, ∀ c ∈ C₂, l c ∈ C₂) →
        (∀ J : Subgroup V, (∀ l ∈ perfectCore P, ∀ c ∈ J, l c ∈ J) → C₁ ≤ J → J ≤ C₂ →
          J = C₁ ∨ J = C₂) →
        (∃ l ∈ perfectCore P, ∃ c ∈ C₂, l c * c⁻¹ ∉ C₁) →
          BinaryNaturalSL (ChB.autSec (perfectCore P) C₂ C₁) ⊤ ⊥ 2 2)
    (C₁ C₂ : Subgroup (burnsideB4h_Amb G)) (hC₂V : C₂ ≤ burnsideB4h_V0 G) (hlt : C₁ < C₂)
    (hN₁ : burnsideB4h_lift G (perfectCore P) ≤ Subgroup.normalizer (C₁ : Set (burnsideB4h_Amb G)))
    (hN₂ : burnsideB4h_lift G (perfectCore P) ≤ Subgroup.normalizer (C₂ : Set (burnsideB4h_Amb G)))
    (hmin : ∀ J : Subgroup (burnsideB4h_Amb G), C₁ ≤ J → J ≤ C₂ →
      burnsideB4h_lift G (perfectCore P) ≤ Subgroup.normalizer (J : Set (burnsideB4h_Amb G)) →
        J = C₁ ∨ J = C₂)
    (hnon : ∃ l ∈ burnsideB4h_lift G (perfectCore P), ∃ c ∈ C₂, l * c * l⁻¹ * c⁻¹ ∉ C₁) :
    ∃ N' : Subgroup ↥(burnsideB4h_lift G (perfectCore P)),
      CFSG.Quasithin.IsNaturalSection (burnsideB4h_lift G (perfectCore P)) C₂ C₁ N'
        (StatedSL 2 F) := by
  classical
  have hC₁V : C₁ ≤ burnsideB4h_V0 G := hlt.le.trans hC₂V
  have hC₂inl : ∀ x ∈ C₂, ∃ v : V, (inl v : burnsideB4h_Amb G) = x ∧
      (inl v : burnsideB4h_Amb G) ∈ C₂ := by
    intro x hx
    obtain ⟨v, rfl⟩ := hC₂V hx
    exact ⟨v, rfl, hx⟩
  have hC₁inl : ∀ x ∈ C₁, ∃ v : V, (inl v : burnsideB4h_Amb G) = x ∧
      (inl v : burnsideB4h_Amb G) ∈ C₁ := by
    intro x hx
    obtain ⟨v, rfl⟩ := hC₁V hx
    exact ⟨v, rfl, hx⟩
  have hinv₁ : ∀ l ∈ perfectCore P, ∀ c ∈ C₁.comap (inl : V →* burnsideB4h_Amb G), l c ∈
      C₁.comap (inl : V →* burnsideB4h_Amb G) := fun l hl c hc =>
    burnsideB4h_comap_inv hN₁ hl (hPG hl) hc
  have hinv₂ : ∀ l ∈ perfectCore P, ∀ c ∈ C₂.comap (inl : V →* burnsideB4h_Amb G), l c ∈
      C₂.comap (inl : V →* burnsideB4h_Amb G) := fun l hl c hc =>
    burnsideB4h_comap_inv hN₂ hl (hPG hl) hc
  have hD12 : C₁.comap (inl : V →* burnsideB4h_Amb G) ≤ C₂.comap (inl : V →* burnsideB4h_Amb G) :=
    Subgroup.comap_mono hlt.le
  have hDlt : C₁.comap (inl : V →* burnsideB4h_Amb G) < C₂.comap (inl : V →* burnsideB4h_Amb G) := by
    refine lt_of_le_of_ne hD12 fun h => hlt.ne (le_antisymm hlt.le fun x hx => ?_)
    obtain ⟨v, rfl, hv⟩ := hC₂inl x hx
    have hv' : v ∈ C₁.comap (inl : V →* burnsideB4h_Amb G) := h ▸ hv
    exact hv'
  have hDmin : ∀ J : Subgroup V, (∀ l ∈ perfectCore P, ∀ c ∈ J, l c ∈ J) →
      C₁.comap (inl : V →* burnsideB4h_Amb G) ≤ J → J ≤ C₂.comap (inl : V →* burnsideB4h_Amb G) →
        J = C₁.comap (inl : V →* burnsideB4h_Amb G) ∨ J = C₂.comap (inl : V →* burnsideB4h_Amb G) := by
    intro J hJ h1J hJ2
    have hle1 : C₁ ≤ J.map (inl : V →* burnsideB4h_Amb G) := by
      intro x hx
      obtain ⟨v, rfl, hv⟩ := hC₁inl x hx
      exact ⟨v, h1J hv, rfl⟩
    have hle2 : J.map (inl : V →* burnsideB4h_Amb G) ≤ C₂ := by
      rintro x ⟨v, hv, rfl⟩
      exact hJ2 hv
    have hnorm : burnsideB4h_lift G (perfectCore P) ≤
        Subgroup.normalizer ((J.map (inl : V →* burnsideB4h_Amb G) : Subgroup _) :
          Set (burnsideB4h_Amb G)) := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := burnsideB4h_mem_lift.1 hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨c, hc, rfl⟩
        rw [burnsideB4h_inr_mul_inl]
        exact ⟨_, hJ _ hg c hc, rfl⟩
      · rintro ⟨c, hc, hcc⟩
        have hh : h = (inl (((g⁻¹ : ↥G) : MulAut V) c) : burnsideB4h_Amb G) := by
          have e1 := burnsideB4h_inr_mul_inl (g⁻¹) c
          rw [map_inv, inv_inv] at e1
          rw [← e1]
          have e2 : (inl c : burnsideB4h_Amb G) = inr g * h * (inr g)⁻¹ := hcc
          rw [e2]
          group
        rw [hh]
        exact ⟨_, hJ _ (inv_mem hg) c hc, rfl⟩
    have hcomap : ∀ K : Subgroup V, (K.map (inl : V →* burnsideB4h_Amb G)).comap
        (inl : V →* burnsideB4h_Amb G) = K := fun K =>
      Subgroup.comap_map_eq_self_of_injective inl_injective K
    rcases hmin _ hle1 hle2 hnorm with h | h
    · left
      rw [← hcomap J, h]
    · right
      rw [← hcomap J, h]
  have hDnon : ∃ l ∈ perfectCore P, ∃ c ∈ C₂.comap (inl : V →* burnsideB4h_Amb G),
      l c * c⁻¹ ∉ C₁.comap (inl : V →* burnsideB4h_Amb G) := by
    obtain ⟨l, hl, c, hc, hn⟩ := hnon
    obtain ⟨g, hg, rfl⟩ := burnsideB4h_mem_lift.1 hl
    obtain ⟨v, rfl, hv⟩ := hC₂inl c hc
    refine ⟨(g : MulAut V), hg, v, hv, fun hmem => hn ?_⟩
    rw [burnsideB4h_inr_mul_inl, ← map_inv, ← map_mul]
    exact hmem
  obtain ⟨α', β', hα's, hβ's, hker, hequiv⟩ :=
    burnsideB4h_cls_nat_bridge hF (perfectCore P) _ _ hD12 hinv₁ hinv₂
      (hstar _ _ hDlt hinv₁ hinv₂ hDmin hDnon)
  let ψ := burnsideB4h_leftHom C₂ hC₂V
  have hψs := burnsideB4h_leftHom_surjective C₂ hC₂V
  let ρ := burnsideB4h_restr (G := G) (perfectCore P)
  have hρs := burnsideB4h_restr_surjective hPG
  refine ⟨(α'.comp ρ).ker, hN₂, α'.comp ρ, hα's.comp hρs, rfl, β'.comp ψ, hβ's.comp hψs, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    show (inl (x : burnsideB4h_Amb G).left : burnsideB4h_Amb G) ∈ C₁ ↔ _
    rw [← burnsideB4h_eq_inl (hC₂V x.2)]
  · intro a u v huv
    obtain ⟨g, hg, hga⟩ := burnsideB4h_mem_lift.1 a.2
    obtain ⟨u₀, hu₀⟩ := hC₂V u.2
    obtain ⟨v₀, hv₀⟩ := hC₂V v.2
    have hl : (v : burnsideB4h_Amb G).left = v₀ := by rw [← hv₀]; rfl
    have hl' : (u : burnsideB4h_Amb G).left = u₀ := by rw [← hu₀]; rfl
    have hra : ((ρ a : ↥(perfectCore P)) : MulAut V) = (g : MulAut V) := by
      show ((rightHom (a : burnsideB4h_Amb G) : ↥G) : MulAut V) = _
      rw [← hga, rightHom_inr]
    have key : (v : burnsideB4h_Amb G).left =
        ((ρ a : ↥(perfectCore P)) : MulAut V) (u : burnsideB4h_Amb G).left := by
      rw [hra, hl, hl']
      apply inl_injective (φ := G.subtype)
      have hainv : ((a⁻¹ : ↥(burnsideB4h_lift G (perfectCore P))) : burnsideB4h_Amb G) =
          (a : burnsideB4h_Amb G)⁻¹ := rfl
      rw [hv₀, huv, hainv, ← hga, ← hu₀]
      exact burnsideB4h_inr_mul_inl g u₀
    exact hequiv (ρ a) (ψ u) (ψ v) key

end HypNat

end

section

section ClsBeta

open Subgroup CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.B414
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {Γ V Z L X : Subgroup G} {F : Type} [Field F]
  [Fintype F] {α : ↥Γ →* GL (Fin 3) F ⧸ center (GL (Fin 3) F)}
  {P : Subgroup (GL (Fin 3) F ⧸ center (GL (Fin 3) F))}

theorem burnsideB4h_cls_exists_beta (hyp : Hyp Γ V Z L X F α P) :
    ∃ k : ℕ, k < 3 ∧ ∃ β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F),
      (∀ v, Multiplicative.toAdd (β v) ∈ sl3 F) ∧
      (∀ M ∈ sl3 F, ∃ v, Multiplicative.toAdd (β v) = M) ∧ β.ker = Z.subgroupOf V ∧
      ∀ (γ : ↥Γ) (u v : ↥V), (v : G) = γ * u * γ⁻¹ → ∀ g : GL (Fin 3) F,
        (QuotientGroup.mk g : GL (Fin 3) F ⧸ center (GL (Fin 3) F)) = α γ →
        Multiplicative.toAdd (β v) = twAdj k g (Multiplicative.toAdd (β u)) := by
  have : Fact (IsElem V Z) := ⟨hyp.isElem⟩
  have := hyp.charP
  obtain ⟨Φ₀, hinj, hΦ₀⟩ := hyp.exists_adj_embedding
  obtain ⟨k, hk, Φ, hΦ⟩ := exists_twAdj_equiv hyp.card
    (glRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker)
    (glRep_isIrreducible hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hyp.lt
      hyp.irred) Φ₀ hinj hΦ₀
  refine ⟨k, hk, ?_⟩
  let β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F) :=
    { toFun := fun v => Multiplicative.ofAdd (Xm (Φ.symm (secπ V Z v)))
      map_one' := by
        rw [secπ_one, map_zero, ← XmL_apply, map_zero]
        rfl
      map_mul' := fun v w => by
        rw [secπ_mul, map_add, ← XmL_apply, map_add]
        rfl }
  have hβ : ∀ v, Multiplicative.toAdd (β v) = Xm (Φ.symm (secπ V Z v)) := fun _ => rfl
  refine ⟨β, fun v => ?_, fun M hM => ?_, ?_, fun γ u v huv g hg => ?_⟩
  · rw [hβ]
    exact trace_Xm F _
  · obtain ⟨v, hv⟩ := secπ_surjective V Z (Φ (co M))
    refine ⟨v, ?_⟩
    rw [hβ, hv, AddEquiv.symm_apply_apply]
    exact Xm_co F hM
  · ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← secπ_eq_zero_iff]
    constructor
    · intro h
      have h1 : Xm (Φ.symm (secπ V Z v)) = 0 := congrArg Multiplicative.toAdd h
      have h2 : Φ.symm (secπ V Z v) = 0 := by
        rw [← co_Xm (Φ.symm (secπ V Z v)), h1]
        funext i
        fin_cases i <;> rfl
      rw [← Φ.apply_symm_apply (secπ V Z v), h2, map_zero]
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hβ, h, map_zero, ← XmL_apply, map_zero]
      rfl
  · have hvu : v = conjV V γ (hyp.le_normalizer_V γ.2) u := Subtype.ext huv
    have h1 : secπ V Z v = Φ (((g : Matrix (Fin 3) (Fin 3) F).det) ^ k •
        adG g (Φ.symm (secπ V Z u))) := by
      rw [← hΦ, Φ.apply_symm_apply,
        glRep_eq hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hg, secRep_secπ, hvu]
    rw [hβ, hβ, h1, AddEquiv.symm_apply_apply, ← XmL_apply, map_smul, XmL_apply, adG,
      adjAd_apply, Xm_co F (by rw [trace_conj_eq F _ _ _ (by rw [← Units.val_mul,
        inv_mul_cancel, Units.val_one]), trace_Xm])]
    rfl

end ClsBeta

end

section

section HypBuild

open SemidirectProduct CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {F : Type} [Field F] [Fintype F]

theorem burnsideB4h_V0_ne_bot [Nontrivial V] : (⊥ : Subgroup (burnsideB4h_Amb G)) < burnsideB4h_V0 G := by
  refine lt_of_le_of_ne bot_le fun h => ?_
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have h1 : (inl v : burnsideB4h_Amb G) ∈ (⊥ : Subgroup (burnsideB4h_Amb G)) :=
    h ▸ burnsideB4h_inl_mem v
  rw [Subgroup.mem_bot] at h1
  exact hv (inl_injective (h1.trans (map_one (inl : V →* burnsideB4h_Amb G)).symm))

theorem burnsideB4h_hyp [Finite V] (hexp : ∀ v : V, v ^ 2 = 1) (hF : Fintype.card F = 4)
    (α : ↥G ≃* PGL3 F) (hnt : Nontrivial V)
    (hirr : ∀ W : Subgroup V, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {P : Subgroup (MulAut V)} (hP : IsMaxParabolic2 G P)
    {X : Subgroup (MulAut V)} (hXP : X ≤ P) (hX3 : Nat.card X = 3)
    (hXc : ∀ x ∈ X, ∀ l ∈ perfectCore P, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (perfectCore P))
    (hstar : ∀ C₁ C₂ : Subgroup V, C₁ < C₂ →
        (∀ l ∈ perfectCore P, ∀ c ∈ C₁, l c ∈ C₁) → (∀ l ∈ perfectCore P, ∀ c ∈ C₂, l c ∈ C₂) →
        (∀ J : Subgroup V, (∀ l ∈ perfectCore P, ∀ c ∈ J, l c ∈ J) → C₁ ≤ J → J ≤ C₂ →
          J = C₁ ∨ J = C₂) →
        (∃ l ∈ perfectCore P, ∃ c ∈ C₂, l c * c⁻¹ ∉ C₁) →
          BinaryNaturalSL (ChB.autSec (perfectCore P) C₂ C₁) ⊤ ⊥ 2 2) :
    CFSG.Quasithin.H13.Ch4.B414.Hyp (burnsideB4h_Gam G) (burnsideB4h_V0 G) ⊥
      (burnsideB4h_lift G (perfectCore P)) (burnsideB4h_lift G X) F (burnsideB4h_alpha0 α)
      (burnsideB4h_img G α P) := by
  classical
  have hPG : P ≤ G := burnsideB4h_le_of_isMaxParabolic2 hP
  have hHG : perfectCore P ≤ G := (perfectCore_le P).trans hPG
  haveI : Finite ↥G := Finite.of_equiv (PGL3 F) α.symm
  refine
    { card := hF
      le_normalizer_V := ?_
      le_normalizer_Z := ?_
      lt := burnsideB4h_V0_ne_bot
      sq_mem := ?_
      comm_mem := ?_
      irred := ?_
      le_L := burnsideB4h_lift_le_Gam _
      le_X := burnsideB4h_lift_le_Gam _
      surj := ?_
      ker_iff := ?_
      maxParabolic := burnsideB4h_img_maxParabolic hP
      map_L := ?_
      map_X_le := ?_
      card_X := ?_
      comm_X := ?_
      natural := ?_ }
  · intro x _
    rw [Subgroup.normalizer_eq_top_iff.2 (burnsideB4h_V0_normal (G := G))]
    exact Subgroup.mem_top x
  · intro x _
    rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup (burnsideB4h_Amb G)).Normal)]
    exact Subgroup.mem_top x
  · rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_bot, ← map_pow, hexp, map_one]
  · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [Subgroup.mem_bot, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    have : v * w * v⁻¹ * w⁻¹ = 1 := by
      rw [mul_comm v w, mul_inv_cancel_right, mul_inv_cancel]
    rw [this, map_one]
  · intro J _ hJV hJN
    set W : Subgroup V := J.comap (inl : V →* burnsideB4h_Amb G) with hW
    have hWinv : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W := by
      intro g hg w hw
      have h := (Subgroup.mem_normalizer_iff.1 (hJN (burnsideB4h_inr_mem ⟨g, hg⟩)) (inl w)).1 hw
      rw [burnsideB4h_inr_mul_inl] at h
      exact h
    rcases hirr W hWinv with h | h
    · left
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      obtain ⟨v, rfl⟩ := hJV hx
      have hv : v ∈ W := hx
      rw [h, Subgroup.mem_bot] at hv
      rw [hv, map_one]
    · right
      refine le_antisymm hJV ?_
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ W := by rw [h]; exact Subgroup.mem_top v
      exact hv
  · intro y
    obtain ⟨g, rfl⟩ := α.surjective y
    exact ⟨⟨inr g, burnsideB4h_inr_mem g⟩, by
      rw [burnsideB4h_alpha0_apply]
      show α (rightHom (inr g : burnsideB4h_Amb G)) = α g
      rw [rightHom_inr]⟩
  · intro γ
    obtain ⟨g, hg⟩ := γ.2
    have hγ : (γ : burnsideB4h_Amb G) = inr g := hg.symm
    have hα : burnsideB4h_alpha0 α γ = α g := by
      rw [burnsideB4h_alpha0_apply, hγ, rightHom_inr]
    rw [hα, map_eq_one_iff α α.injective, hγ]
    constructor
    · rintro rfl v _
      rw [Subgroup.mem_bot]
      simp
    · intro h
      refine Subtype.ext (MulEquiv.ext fun x => ?_)
      have h1 := h (inl x) (burnsideB4h_inl_mem x)
      rw [Subgroup.mem_bot, burnsideB4h_inr_mul_inl, ← map_inv, ← map_mul] at h1
      have h2 : (g : MulAut V) x * x⁻¹ = 1 := inl_injective (h1.trans (map_one _).symm)
      exact mul_inv_eq_one.1 h2
  · rw [burnsideB4h_map_lift, burnsideB4h_img_perfectCore hPG]
  · rw [burnsideB4h_map_lift]
    exact burnsideB4h_img_mono hXP
  · rw [burnsideB4h_map_lift, burnsideB4h_card_img (hXP.trans hPG)]
    exact hX3
  · intro x hx l hl
    rw [burnsideB4h_map_lift] at hx hl ⊢
    obtain ⟨a, ha, rfl⟩ := burnsideB4h_mem_img.1 hx
    obtain ⟨b, hb, rfl⟩ := burnsideB4h_mem_img.1 hl
    rw [← burnsideB4h_img_pCoreOf hHG]
    refine burnsideB4h_mem_img.2 ⟨a * b * a⁻¹ * b⁻¹, hXc _ ha _ hb, ?_⟩
    simp
  · intro C₁ C₂ _ hlt hC₂V hN₁ hN₂ hmin hnon
    exact burnsideB4h_hyp_natural hF hHG hstar C₁ C₂ hC₂V hlt hN₁ hN₂ hmin hnon

end HypBuild

end

section

section Cls

open SemidirectProduct CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB

theorem burnsideB4h_cls_class {V : Type} [CommGroup V] [Finite V] (hexp : ∀ v : V, v ^ 2 = 1)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (G : Subgroup (MulAut V)) (α : ↥G ≃* PGL3 F) (hnt : Nontrivial V)
    (hirr : ∀ W : Subgroup V, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup (MulAut V)) (hP : IsMaxParabolic2 G P)
    (X : Subgroup (MulAut V)) (hXP : X ≤ P) (hX3 : Nat.card X = 3)
    (hXc : ∀ x ∈ X, ∀ l ∈ perfectCore P, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (perfectCore P))
    (hstar : ∀ C₁ C₂ : Subgroup V, C₁ < C₂ →
        (∀ l ∈ perfectCore P, ∀ c ∈ C₁, l c ∈ C₁) → (∀ l ∈ perfectCore P, ∀ c ∈ C₂, l c ∈ C₂) →
        (∀ J : Subgroup V, (∀ l ∈ perfectCore P, ∀ c ∈ J, l c ∈ J) → C₁ ≤ J → J ≤ C₂ →
          J = C₁ ∨ J = C₂) →
        (∃ l ∈ perfectCore P, ∃ c ∈ C₂, l c * c⁻¹ ∉ C₁) →
          BinaryNaturalSL (ChB.autSec (perfectCore P) C₂ C₁) ⊤ ⊥ 2 2) :
    ∃ k : ℕ, k < 3 ∧ ∃ β : V ≃* Multiplicative ↥(sl3Sub F),
      TwAdjointIntertwines G α.toMonoidHom k β := by
  classical
  haveI : Finite ↥G := Finite.of_equiv (PGL3 F) α.symm
  have hyp := burnsideB4h_hyp hexp hF α hnt hirr hP hXP hX3 hXc hstar
  obtain ⟨k, hk, β₀, hsl, hsurj, hker, hβ₀⟩ := burnsideB4h_cls_exists_beta hyp
  refine ⟨k, hk, ?_⟩
  have hsl3 : ∀ M : Matrix (Fin 3) (Fin 3) F,
      M ∈ CFSG.Quasithin.H13.Ch4.sl3 F ↔ M ∈ sl3Sub F := fun M => Iff.rfl
  let β₂ : V →* Multiplicative (Matrix (Fin 3) (Fin 3) F) :=
    β₀.comp (inl : V →* burnsideB4h_Amb G).rangeRestrict
  have hβ₂ : ∀ v, β₂ v = β₀ ⟨inl v, burnsideB4h_inl_mem v⟩ := fun v => rfl
  let β₁ : V →* Multiplicative ↥(sl3Sub F) :=
    { toFun := fun v => Multiplicative.ofAdd
        (⟨Multiplicative.toAdd (β₂ v), (hsl3 _).1 (hsl _)⟩ : ↥(sl3Sub F))
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show Multiplicative.toAdd (β₂ 1) = 0
        rw [map_one]
        rfl
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show Multiplicative.toAdd (β₂ (v * w)) =
          Multiplicative.toAdd (β₂ v) + Multiplicative.toAdd (β₂ w)
        rw [map_mul]
        rfl }
  have hβ₀inj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  have hβ₁inj : Function.Injective β₁ := by
    intro v w h
    have h1 : Multiplicative.toAdd (β₂ v) = Multiplicative.toAdd (β₂ w) :=
      congrArg (fun m => ((Multiplicative.toAdd m : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F)) h
    have h3 := hβ₀inj (Multiplicative.toAdd.injective h1)
    exact inl_injective (congrArg Subtype.val h3)
  have hβ₁surj : Function.Surjective β₁ := by
    intro m
    obtain ⟨x, hx⟩ := hsurj ((Multiplicative.toAdd m : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F)
      ((hsl3 _).2 (Multiplicative.toAdd m).2)
    obtain ⟨v, hv⟩ := x.2
    refine ⟨v, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    show Multiplicative.toAdd (β₂ v) = _
    have hvx : (⟨inl v, burnsideB4h_inl_mem v⟩ : ↥(burnsideB4h_V0 G)) = x := Subtype.ext hv
    rw [hβ₂, hvx]
    exact hx
  refine ⟨MulEquiv.ofBijective β₁ ⟨hβ₁inj, hβ₁surj⟩, ?_⟩
  intro element vector representative hrep
  have h := hβ₀ ⟨inr element, burnsideB4h_inr_mem element⟩
    ⟨inl vector, burnsideB4h_inl_mem vector⟩
    ⟨inl ((element : MulAut V) vector), burnsideB4h_inl_mem _⟩
    (burnsideB4h_inr_mul_inl element vector).symm representative (by
      rw [burnsideB4h_alpha0_apply]
      show _ = α (rightHom (inr element : burnsideB4h_Amb G))
      rw [rightHom_inr]
      exact hrep)
  exact h

end Cls

end

section

section
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB

theorem as_B_4_14 : B_4_14 := by
  intro V _ _ hexp F _ _ hF G α hnt hirr P hP X hXP hX3 hXc hstar
  obtain ⟨k, hk, β, hβ⟩ :=
    burnsideB4h_cls_class hexp hF G α hnt hirr P hP X hXP hX3 hXc hstar
  obtain ⟨hT, hN⟩ := burnsideB4h_structure hF G α hP hXP hX3 hXc hk hβ
  refine ⟨k, hk, β, hβ, hT, hN, ?_⟩
  intro k' hk' β' hβ'
  exact burnsideB4h_unq_twist_unique hF G α.toMonoidHom α.surjective hk' hk hβ' hβ

end

end

end CFSG.ASVolI
