module

public import CFSG.Quasithin.EmptyFaithful.R3c14Cfg
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin.R3c14

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBGraphForm CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin

abbrev SLn (n : ℕ) : Type := Matrix.SpecialLinearGroup (Fin n) (ZMod 2)

noncomputable abbrev dlt (n : ℕ) : MulAut (SLn n) := slGraphAut n (ZMod 2)

theorem dlt_apply {n : ℕ} (g : SLn n) : dlt n g = (g⁻¹).transpose := rfl

theorem scalars_bot (n : ℕ) : scalars n (ZMod 2) = ⊥ := by
  rw [scalars_eq_center]
  exact CFSG.QuasithinUnique.Setup.Family.center_specialLinear_eq_bot_of_card_two n (ZMod 2)
    (by rw [Nat.card_zmod])

theorem proj_inj_two (n : ℕ) : Function.Injective (proj n (ZMod 2)) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  rw [ker_proj, scalars_bot]

@[expose] noncomputable def projEquivTwo (n : ℕ) : SLn n ≃* projectiveSL n (ZMod 2) :=
  { Equiv.ofBijective (proj n (ZMod 2)) ⟨proj_inj_two n, proj_surjective n (ZMod 2)⟩ with
    map_mul' := map_mul _ }

theorem projEquivTwo_apply {n : ℕ} (g : SLn n) : projEquivTwo n g = proj n (ZMod 2) g := rfl

theorem field_trivial_two (σ : ZMod 2 ≃+* ZMod 2) : σ = 1 := by
  ext x
  fin_cases x
  · exact map_zero σ
  · exact map_one σ

theorem aut_form_sl {n : ℕ} (hn : 3 ≤ n) (α : MulAut (SLn n)) :
    ∃ (a : SLn n) (ε : ℕ), ε ≤ 1 ∧ α = MulAut.conj a * dlt n ^ ε := by
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := ZMod 2) (n := n) hn
  obtain ⟨A, σ, ε, hε, hβ⟩ := hgen ((MulAut.congr (projEquivTwo n)) α)
  have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
    have hu : IsUnit (A : Matrix (Fin n) (Fin n) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    obtain ⟨u, hu⟩ := hu
    have hu1 : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
    rw [← hu, hu1 u]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : SLn n, (a : Matrix (Fin n) (Fin n) (ZMod 2)) = A := ⟨⟨A, hdet⟩, rfl⟩
  have hA : Matrix.SpecialLinearGroup.toGL a = A := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact ha
  have hσ : σ = 1 := field_trivial_two σ
  refine ⟨a, ε, hε, ?_⟩
  have hδ : ∀ g : SLn n, projEquivTwo n (dlt n g) = dualAut n (ZMod 2) (projEquivTwo n g) := by
    intro g
    rw [projEquivTwo_apply, projEquivTwo_apply, dualAut_proj]
    rfl
  have hc : ∀ g : SLn n, (MulAut.congr (projEquivTwo n) α) (projEquivTwo n g) =
      projEquivTwo n (α g) := by
    intro g
    simp [MulAut.congr_apply]
  have hβ' : (MulAut.congr (projEquivTwo n)) α =
      MulAut.conj (projEquivTwo n a) * dualAut n (ZMod 2) ^ ε := by
    rw [hβ, hσ, map_one, mul_one, ← hA, conjAut_toGL, projEquivTwo_apply]
  apply MulEquiv.ext
  intro g
  apply (projEquivTwo n).injective
  rw [← hc g, hβ']
  interval_cases ε
  · simp [MulAut.conj_apply, map_mul, map_inv]
  · simp only [pow_one, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [← hδ]


section Mat

variable {n : ℕ}

@[expose] def trv (i j : Fin n) (h : i ≠ j) : SLn n :=
  ⟨Matrix.transvection i j (1 : ZMod 2), Matrix.det_transvection_of_ne i j h 1⟩

theorem coe_trv (i j : Fin n) (h : i ≠ j) :
    ((trv i j h : SLn n) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + Matrix.single i j 1 := rfl


theorem trv_mem {i j : Fin n} (hij : i < j) : trv i j hij.ne ∈ unitriangular n (ZMod 2) := by
  rw [mem_unitriangular]
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · simp only [coe_trv, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hkl : k ≠ l := hlk.ne'
    have : ¬ (i = k ∧ j = l) := fun ⟨h1, h2⟩ => by
      subst h1; subst h2; exact absurd hij (not_lt.mpr hlk.le)
    simp [hkl, this]
  · simp only [coe_trv, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have : ¬ (i = k ∧ j = k) := fun ⟨h1, h2⟩ => hij.ne (h1.trans h2.symm)
    simp [this]

theorem comm_single_aux {G : Matrix (Fin n) (Fin n) (ZMod 2)} {a b : Fin n}
    (h : G * Matrix.single a b 1 = Matrix.single a b 1 * G) :
    (∀ k, k ≠ a → G k a = 0) ∧ (∀ l, l ≠ b → G b l = 0) ∧ G a a = G b b := by
  refine ⟨fun k hk => ?_, fun l hl => ?_, ?_⟩
  · have := congrFun (congrFun h k) b
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hk] at this
    simpa using this
  · have := congrFun (congrFun h a) l
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, Matrix.single_mul_apply_same] at this
    simpa using this.symm
  · have := congrFun (congrFun h a) b
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at this
    simpa using this

@[expose] def z0 (hn : 3 ≤ n) : SLn n :=
  trv (⟨0, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this; omega)

theorem coe_z0 (hn : 3 ≤ n) : ((z0 hn : SLn n) : Matrix (Fin n) (Fin n) (ZMod 2)) =
    1 + Matrix.single (⟨0, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ 1 := rfl

theorem eq_one_or_z0 (hn : 3 ≤ n) {g : SLn n}
    (hg : ∀ (a : ℕ) (ha : a + 1 < n),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * Matrix.single (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩ 1 =
        Matrix.single (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩ 1 * (g : Matrix (Fin n) (Fin n) (ZMod 2))) :
    g = 1 ∨ g = z0 hn := by
  set G : Matrix (Fin n) (Fin n) (ZMod 2) := (g : Matrix (Fin n) (Fin n) (ZMod 2)) with hG
  have hrow := fun (a : ℕ) (ha : a + 1 < n) => comm_single_aux (hg a ha)
  have hdiag : ∀ (m : ℕ) (hm : m < n), G ⟨m, hm⟩ ⟨m, hm⟩ = G ⟨0, by omega⟩ ⟨0, by omega⟩ := by
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      rw [← ih (by omega)]
      exact ((hrow m hm).2.2).symm
  have hoff : ∀ k l : Fin n, k ≠ l → G k l = 0 ∨ (k.val = 0 ∧ l.val = n - 1) := by
    intro k l hkl
    by_cases hl : l.val + 1 < n
    · left
      have := (hrow l.val hl).1 k (by
        intro h
        exact hkl (by rw [h]))
      simpa using this
    · by_cases hk : 1 ≤ k.val
      · left
        have hk1 : k.val - 1 + 1 < n := by omega
        have := (hrow (k.val - 1) hk1).2.1 l (by
          intro h
          apply hkl
          have : k.val = l.val := by
            have := congrArg Fin.val h
            simp at this
            omega
          exact Fin.ext this)
        simpa [Nat.sub_add_cancel hk] using this
      · right
        constructor
        · omega
        · have := l.2
          omega
  have hd1 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
    by_contra hne
    have hd0 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
      generalize G ⟨0, by omega⟩ ⟨0, by omega⟩ = d at hne ⊢
      revert d
      decide
    have : G.det = 0 := by
      refine Matrix.det_eq_zero_of_row_eq_zero (⟨1, by omega⟩ : Fin n) fun l => ?_
      by_cases hl : l = (⟨1, by omega⟩ : Fin n)
      · rw [hl]
        have := hdiag 1 (by omega)
        rw [this, hd0]
      · rcases hoff ⟨1, by omega⟩ l (fun h => hl h.symm) with h | ⟨h, -⟩
        · exact h
        · simp at h
    have h1 : G.det = 1 := g.2
    rw [h1] at this
    exact one_ne_zero this
  have hdk : ∀ k : Fin n, G k k = 1 := fun k => by
    have := hdiag k.val k.2
    simpa [hd1] using this
  set c : ZMod 2 := G ⟨0, by omega⟩ ⟨n - 1, by omega⟩ with hc
  have hne0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hentry : ∀ k l : Fin n, G k l = (if k = l then 1 else 0) +
      (if ((⟨0, by omega⟩ : Fin n) = k ∧ (⟨n - 1, by omega⟩ : Fin n) = l) then c else 0) := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      have h0 : ¬ ((⟨0, by omega⟩ : Fin n) = k ∧ (⟨n - 1, by omega⟩ : Fin n) = k) := by
        rintro ⟨h1, h2⟩
        exact hne0 (h1.trans h2.symm)
      simp [hdk k, h0]
    · by_cases hcond : (⟨0, by omega⟩ : Fin n) = k ∧ (⟨n - 1, by omega⟩ : Fin n) = l
      · obtain ⟨e1, e2⟩ := hcond
        rw [← e1, ← e2]
        simp [hc, hne0]
      · rcases hoff k l hkl with h | ⟨h1, h2⟩
        · simp [hkl, hcond, h]
        · exact absurd ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩ hcond
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h0 | h1
  · left
    refine Subtype.ext (Matrix.ext fun k l => ?_)
    show G k l = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) k l
    rw [hentry k l, h0]
    simp [Matrix.one_apply]
  · right
    refine Subtype.ext (Matrix.ext fun k l => ?_)
    show G k l = ((1 + Matrix.single (⟨0, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ 1 :
      Matrix (Fin n) (Fin n) (ZMod 2))) k l
    rw [hentry k l, h1]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]


theorem comm_single_of_comm {g : SLn n} {i j : Fin n} {hij : i ≠ j}
    (h : g * trv i j hij = trv i j hij * g) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) * Matrix.single i j 1 =
      Matrix.single i j 1 * (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have h1 := congrArg (fun x : SLn n => (x : Matrix (Fin n) (Fin n) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_trv, mul_add, add_mul, mul_one, one_mul] at h1
  exact add_left_cancel h1

theorem z0_ne_one (hn : 3 ≤ n) : z0 hn ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SLn n => (x : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨0, by omega⟩ ⟨n - 1, by omega⟩) h
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [coe_z0, Matrix.add_apply, hne] at h1

theorem trv_inv {i j : Fin n} (hij : i ≠ j) : (trv i j hij)⁻¹ = trv i j hij := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  have h := Matrix.transvection_mul_transvection_same i j hij (1 : ZMod 2) 1
  have h2 : (1 + 1 : ZMod 2) = 0 := by decide
  rw [h2, Matrix.transvection_zero] at h
  exact h

theorem outer_aux {g : SLn n} {i j : Fin n} (hij : i ≠ j)
    (h : (MulAut.conj g * dlt n) (trv i j hij) = trv i j hij) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) * Matrix.single j i 1 =
      Matrix.single i j 1 * (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have h1 : g * dlt n (trv i j hij) = trv i j hij * g := by
    rw [MulAut.mul_apply, MulAut.conj_apply] at h
    calc g * dlt n (trv i j hij) = (g * dlt n (trv i j hij) * g⁻¹) * g := by group
      _ = trv i j hij * g := by rw [h]
  have h2 := congrArg (fun x : SLn n => (x : Matrix (Fin n) (Fin n) (ZMod 2))) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul, dlt_apply, trv_inv,
    Matrix.SpecialLinearGroup.coe_transpose, coe_trv] at h2
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single] at h2
  simp only [mul_add, add_mul, mul_one, one_mul] at h2
  exact add_left_cancel h2

theorem no_outer (hn : 3 ≤ n) {g : SLn n}
    (h : ∀ t ∈ unitriangular n (ZMod 2), (MulAut.conj g * dlt n) t = t) : False := by
  have hlt1 : (⟨n - 2, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ := by
    simp [Fin.lt_def]
    omega
  have hlt2 : (⟨0, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ := by
    simp [Fin.lt_def]
    omega
  have e1 := outer_aux hlt1.ne (h _ (trv_mem hlt1))
  have e2 := outer_aux hlt2.ne (h _ (trv_mem hlt2))
  have hcol : ∀ k : Fin n, (g : Matrix (Fin n) (Fin n) (ZMod 2)) k ⟨n - 1, by omega⟩ = 0 := by
    intro k
    by_cases hk2 : k = ⟨n - 2, by omega⟩
    · have hk0 : k ≠ ⟨0, by omega⟩ := by
        rw [hk2]
        intro h'
        have := congrArg Fin.val h'
        simp at this
        omega
      have := congrFun (congrFun e2 k) ⟨0, by omega⟩
      rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hk0] at this
      simpa using this
    · have := congrFun (congrFun e1 k) ⟨n - 2, by omega⟩
      rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hk2] at this
      simpa using this
  have h0 := Matrix.det_eq_zero_of_column_eq_zero (⟨n - 1, by omega⟩ : Fin n) hcol
  have h1 : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := g.2
  rw [h1] at h0
  exact one_ne_zero h0


theorem isSylow_U (n : ℕ) (hn : 1 ≤ n) : IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) hn
  refine K1.isSylowTwoOf_top_iff.mpr ⟨?_, ?_⟩
  · rw [← hP]
    exact P.isPGroup'
  · rw [← hP]
    exact P.not_dvd_index

theorem z0_mem_V (hn : 3 ≤ n) {V : Subgroup (SLn n)} (hVU : V ≤ unitriangular n (ZMod 2))
    (hV4 : Nat.card V = 4)
    (hUV : unitriangular n (ZMod 2) ≤ Subgroup.normalizer (V : Set (SLn n))) : z0 hn ∈ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 ↥(unitriangular n (ZMod 2)) := (isSylow_U n (by omega)).2.1
  have hnil : Group.IsNilpotent ↥(unitriangular n (ZMod 2)) := hU2.isNilpotent
  have hVn : (V.subgroupOf (unitriangular n (ZMod 2))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mpr hUV
  have hV1 : V.subgroupOf (unitriangular n (ZMod 2)) ≠ ⊥ := by
    intro hb
    have h1 : Nat.card (V.subgroupOf (unitriangular n (ZMod 2))) = 1 := by
      rw [hb]
      exact Subgroup.card_bot
    have h2 : Nat.card (V.subgroupOf (unitriangular n (ZMod 2))) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv
    omega
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hV1
  obtain ⟨⟨⟨x, hxU⟩, hxmem⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  have hxV : x ∈ V := Subgroup.mem_subgroupOf.mp hxmem.1
  have hxc : ∀ t ∈ unitriangular n (ZMod 2), t * x = x * t := fun t ht => by
    have := Subgroup.mem_center_iff.mp hxmem.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hx : x = 1 ∨ x = z0 hn := by
    refine eq_one_or_z0 hn fun a ha => ?_
    have hlt : (⟨a, by omega⟩ : Fin n) < ⟨a + 1, ha⟩ := by
      simp [Fin.lt_def]
    exact comm_single_of_comm (hij := hlt.ne) ((hxc _ (trv_mem hlt)).symm)
  rcases hx with h1 | h1
  · exact absurd (Subtype.ext (Subtype.ext h1)) hx1
  · rw [← h1]
    exact hxV

theorem not_elData_sl (hn : 3 ≤ n) {V H : Subgroup (SLn n)} {ζ : MulAut (SLn n)}
    (h : ElData (unitriangular n (ZMod 2)) V H ζ) : False := by
  obtain ⟨g, ε, hε, hζ⟩ := aut_form_sl hn ζ
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hζ
    have hfixT : ∀ t ∈ unitriangular n (ZMod 2), g * t * g⁻¹ = t := fun t ht => by
      have := h.fixT t ht
      rw [hζ, MulAut.conj_apply] at this
      exact this
    have hgc : ∀ (a : ℕ) (ha : a + 1 < n),
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) * Matrix.single (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩ 1 =
          Matrix.single (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩ 1 *
            (g : Matrix (Fin n) (Fin n) (ZMod 2)) := fun a ha => by
      have hlt : (⟨a, by omega⟩ : Fin n) < ⟨a + 1, ha⟩ := by
        simp [Fin.lt_def]
      refine comm_single_of_comm (hij := hlt.ne) ?_
      have := hfixT _ (trv_mem hlt)
      calc g * trv _ _ hlt.ne = (g * trv _ _ hlt.ne * g⁻¹) * g := by group
        _ = trv _ _ hlt.ne * g := by rw [this]
    rcases eq_one_or_z0 hn hgc with h1 | h1
    · apply h.ne
      rw [hζ, h1]
      ext x
      simp
    · have hz0V : z0 hn ∈ V := z0_mem_V hn h.VT h.V4 h.TV
      have hz0 : z0 hn = 1 := h.fix (z0 hn) hz0V fun k hk => by
        have := h.fixH k hk
        rw [hζ, h1, MulAut.conj_apply] at this
        calc k * z0 hn = (z0 hn * k * (z0 hn)⁻¹) * z0 hn := by rw [this]
          _ = z0 hn * k := by group
      exact z0_ne_one hn hz0
  ·
    rw [pow_one] at hζ
    exact no_outer hn fun t ht => by
      have := h.fixT t ht
      rwa [hζ] at this

theorem not_elConfig_sl (hn : 3 ≤ n) : ¬ ElConfig (SLn n) := by
  intro hc
  obtain ⟨V, H, ζ, hd⟩ := ElConfig.of_sylow (isSylow_U n (by omega)) hc
  exact not_elData_sl hn hd

end Mat

theorem not_elConfig_of_psl {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel X .PSL n 2 1) : ¬ ElConfig X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  let ψ : X ≃* SLn n :=
    φ.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two n K hK2)
  exact fun hc => not_elConfig_sl hn (ElConfig.map ψ hc)

end CFSG.Quasithin.R3c14
