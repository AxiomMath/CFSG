module

public import CFSG.Quasithin.H13.AS91Sec6Inter
public import CFSG.Quasithin.H13.AS91Sec6Base
public import CFSG.Quasithin.H13.AS91Sec6M24
public import CFSG.Quasithin.H13.AS91Sec6Kzero
public import CFSG.GroupTheory.TIFusion
public import CFSG.Quasithin.H13.AS91ResHolds

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace ResM24T

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (r : ResM24T c)

theorem todd_conj (m : ↥c.G1) {e : G} (he : e ∈ c.E) :
    r.todd ⟨(m : G) * e * (m : G)⁻¹, c.conj_mem_E m he⟩ =
      rho11 AutPerm le_rfl ⟨r.φ m, r.toResM24.φ_mem m⟩ (r.todd ⟨e, he⟩) :=
  r.todd_equiv m ⟨e, he⟩

@[expose] noncomputable def tE : G := (r.todd.symm (M24G.setClass {0, 1}) : ↥c.E)

theorem tE_mem : r.tE ∈ c.E := (r.todd.symm _).2

theorem todd_tE : r.todd ⟨r.tE, r.tE_mem⟩ = M24G.setClass {0, 1} :=
  r.todd.apply_symm_apply _

theorem isDuadClass_todd_tE : M24G.IsDuadClass (r.todd ⟨r.tE, r.tE_mem⟩) :=
  ⟨{0, 1}, by decide, r.todd_tE.symm⟩

theorem tE_ne_one : r.tE ≠ 1 := by
  intro h
  have h1 : (⟨r.tE, r.tE_mem⟩ : ↥c.E) = 1 := Subtype.ext h
  have h2 := r.todd_tE
  rw [h1, map_one] at h2
  exact M24G.setClass_ne_one_of_card_two (by decide) h2.symm

theorem isSextClass_todd_iff {e : G} (he : e ∈ c.E) :
    M24G.IsSextClass (r.todd ⟨e, he⟩) ↔ ∃ m ∈ c.G1, m * z * m⁻¹ = e := by
  constructor
  · rintro ⟨U, hU, hUe⟩
    obtain ⟨a, ha, haU⟩ := M24G.sextet_transitive r.isSextet_U₀
    obtain ⟨b, hb, hbU⟩ := M24G.sextet_transitive hU
    have hσ : b⁻¹ * a ∈ M24g := M24g.mul_mem (M24g.inv_mem hb) ha
    obtain ⟨m, hm⟩ := r.toResM24.exists_φ_eq hσ
    have hσU : (b⁻¹ * a) • r.U₀ = U := by rw [mul_smul, haU, ← hbU, inv_smul_smul]
    refine ⟨m, m.2, ?_⟩
    have h : r.todd ⟨(m : G) * z * (m : G)⁻¹, c.conj_mem_E m c.z_mem_E⟩ = r.todd ⟨e, he⟩ := by
      rw [todd_conj r m c.z_mem_E, r.todd_z,
        ← M24G.sextClass_smul (r.toResM24.φ_mem m) r.isSextet_U₀, ← hUe]
      congr 1
      rw [show r.φ m = b⁻¹ * a from hm]
      exact hσU
    exact congrArg Subtype.val (r.todd.injective h)
  · rintro ⟨m, hm, rfl⟩
    refine ⟨r.φ ⟨m, hm⟩ • r.U₀,
      (M24G.isSextet_smul_iff (r.toResM24.φ_mem _)).2 r.isSextet_U₀, ?_⟩
    rw [M24G.sextClass_smul (r.toResM24.φ_mem _) r.isSextet_U₀, ← r.todd_z,
      ← todd_conj r ⟨m, hm⟩ c.z_mem_E]

theorem isDuadClass_todd_iff {e : G} (he : e ∈ c.E) :
    M24G.IsDuadClass (r.todd ⟨e, he⟩) ↔ ∃ m ∈ c.G1, m * r.tE * m⁻¹ = e := by
  constructor
  · rintro ⟨D, hD, hDe⟩
    obtain ⟨σ, hσ, hσD⟩ := M24G.duad_transitive (D := {0, 1}) (by decide) hD
    obtain ⟨m, hm⟩ := r.toResM24.exists_φ_eq hσ
    refine ⟨m, m.2, ?_⟩
    have h : r.todd ⟨(m : G) * r.tE * (m : G)⁻¹, c.conj_mem_E m r.tE_mem⟩ =
        r.todd ⟨e, he⟩ := by
      rw [todd_conj r m r.tE_mem, r.todd_tE,
        ← M24G.setClass_smul (r.toResM24.φ_mem m) (by decide), ← hDe]
      congr 1
      rw [show r.φ m = σ from hm]
      exact hσD
    exact congrArg Subtype.val (r.todd.injective h)
  · rintro ⟨m, hm, rfl⟩
    refine ⟨r.φ ⟨m, hm⟩ • ({0, 1} : Finset (Fin 24)), ?_, ?_⟩
    · rw [Finset.card_smul_finset]
      decide
    · rw [M24G.setClass_smul (r.toResM24.φ_mem _) (by decide), ← r.todd_tE,
        ← todd_conj r ⟨m, hm⟩ r.tE_mem]

theorem exists_conj_z_or_tE {e : G} (he : e ∈ c.E)
    (he1 : e ≠ 1) : (∃ m ∈ c.G1, m * z * m⁻¹ = e) ∨ ∃ m ∈ c.G1, m * r.tE * m⁻¹ = e := by
  have hw : r.todd ⟨e, he⟩ ≠ 1 := by
    intro h
    apply he1
    have h' : (⟨e, he⟩ : ↥c.E) = 1 := r.todd.injective (h.trans (map_one r.todd).symm)
    exact congrArg Subtype.val h'
  rcases M24G.isDuadClass_or_isSextClass hw with hd | hs
  · exact Or.inr ((r.isDuadClass_todd_iff he).1 hd)
  · exact Or.inl ((r.isSextClass_todd_iff he).1 hs)

theorem not_isConj_tE_z : ¬ IsConj r.tE z := by
  intro h
  obtain ⟨m, hm, hmz⟩ := c.exists_G1_conj_of_isConj_z r.tE_mem h
  have h1 := (r.isSextClass_todd_iff r.tE_mem).2 ⟨m, hm, hmz⟩
  exact M24G.not_isSextClass_of_isDuadClass r.isDuadClass_todd_tE h1

theorem tE_mem_map_conj {g : G} (hg : g ∈ centralizer ({r.tE} : Set G)) :
    r.tE ∈ c.E.map (MulAut.conj g).toMonoidHom := by
  refine ⟨r.tE, r.tE_mem, ?_⟩
  have hgt : g * r.tE = r.tE * g := (Subgroup.mem_centralizer_singleton_iff.mp hg)
  show g * r.tE * g⁻¹ = r.tE
  rw [hgt, mul_inv_cancel_right]

theorem not_isConj_z_of_mem_inter (hI : Sec7Inputs) (hJ : HypJ4 G z) (hmax : Stmt5_Max13)
    (h2c : Stmt5_2c) (hN : NormalTwoSextet)
    {g : G} (hg : g ∈ centralizer ({r.tE} : Set G))
    (hgM : g ∉ c.G1) {e : G} (he : e ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom) :
    ¬ IsConj e z := by
  intro hez
  have hne : c.E.map (MulAut.conj g).toMonoidHom ≠ c.E := fun h =>
    hgM (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have ht : r.tE ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_inf.mpr ⟨r.tE_mem, r.tE_mem_map_conj hg⟩
  rcases c.inter_map_conj_of_isConj_z r hI hJ hmax h2c hN hne he hez ht with h1 | ⟨m, -, hmt⟩
  · exact r.tE_ne_one h1
  · exact r.not_isConj_tE_z (isConj_iff.mpr ⟨m, hmt⟩).symm

theorem card_inter_le_four (hI : Sec7Inputs) (hJ : HypJ4 G z) (hmax : Stmt5_Max13)
    (h2c : Stmt5_2c) (hN : NormalTwoSextet)
    {g : G}
    (hg : g ∈ centralizer ({r.tE} : Set G)) (hgM : g ∉ c.G1) :
    Nat.card ↥(c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom) ≤ 4 := by
  set I : Subgroup G := c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom with hIdef
  set V : Subgroup W11 := (I.subgroupOf c.E).map r.todd.toMonoidHom with hV
  have hVd : ∀ v ∈ V, v ≠ 1 → M24G.IsDuadClass v := by
    intro v hv hv1
    obtain ⟨⟨e, heE⟩, he, rfl⟩ := Subgroup.mem_map.mp hv
    have he' : e ∈ I := Subgroup.mem_subgroupOf.mp he
    have hv1' : r.todd ⟨e, heE⟩ ≠ 1 := hv1
    rcases M24G.isDuadClass_or_isSextClass hv1' with hd | hs
    · exact hd
    · exfalso
      obtain ⟨m, -, hmz⟩ := (r.isSextClass_todd_iff heE).1 hs
      exact r.not_isConj_z_of_mem_inter hI hJ hmax h2c hN hg hgM he'
        (isConj_iff.mpr ⟨m, hmz⟩).symm
  have h4 := M24G.card_le_four_of_forall_isDuadClass V hVd
  have hinj : Function.Injective r.todd.toMonoidHom := r.todd.injective
  rw [hV, Subgroup.card_map_of_injective hinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : I ≤ c.E)).toEquiv] at h4
  exact h4

theorem zpow_eq_one_or_self {W : Type*} [Group W] {a : W} (ha : a * a = 1) (m : ℤ) :
    a ^ m = 1 ∨ a ^ m = a := by
  by_cases ha1 : a = 1
  · left
    rw [ha1, one_zpow]
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hmod : a ^ (m % 2) = a ^ m := by
    rw [show (2 : ℤ) = ((orderOf a : ℕ) : ℤ) by rw [hord]; rfl, zpow_mod_orderOf]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [← hmod, h, zpow_zero]
  · right
    rw [← hmod, h, zpow_one]

theorem mem_closure_pair_of_sq {W : Type*} [CommGroup W] {a b w : W} (ha : a * a = 1)
    (hb : b * b = 1) :
    w ∈ Subgroup.closure ({a, b} : Set W) ↔ w = 1 ∨ w = a ∨ w = b ∨ w = a * b := by
  rw [Subgroup.mem_closure_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    rcases zpow_eq_one_or_self ha m with h1 | h1 <;>
      rcases zpow_eq_one_or_self hb n with h2 | h2 <;>
      simp [h1, h2]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem card_closure_pair_of_sq {W : Type*} [CommGroup W] [DecidableEq W] {a b : W}
    (ha : a * a = 1) (hb : b * b = 1) (h1 : a ≠ 1) (h2 : b ≠ 1) (h3 : a * b ≠ 1) (h4 : a ≠ b)
    (h5 : a ≠ a * b) (h6 : b ≠ a * b) :
    Nat.card (Subgroup.closure ({a, b} : Set W)) = 4 := by
  have hset : ((Subgroup.closure ({a, b} : Set W) : Subgroup W) : Set W) =
      ((({1, a, b, a * b} : Finset W)) : Set W) := by
    ext w
    rw [SetLike.mem_coe, mem_closure_pair_of_sq ha hb]
    simp
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem (by simp [h1.symm, h2.symm, h3.symm]),
    Finset.card_insert_of_notMem (by simp [h4, h5]),
    Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]

@[expose] noncomputable def triadSp (k : Fin 24) : Subgroup W11 :=
  Subgroup.closure {M24G.setClass {0, 1}, M24G.setClass {0, k}}

theorem mem_triadSp {k : Fin 24} {w : W11} : w ∈ triadSp k ↔
    w = 1 ∨ w = M24G.setClass {0, 1} ∨ w = M24G.setClass {0, k} ∨
      w = M24G.setClass {0, 1} * M24G.setClass {0, k} :=
  mem_closure_pair_of_sq (M24G.W11_mul_self _) (M24G.W11_mul_self _)

theorem setClass01_mul (k : Fin 24) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    M24G.setClass {0, 1} * M24G.setClass {0, k} = M24G.setClass {1, k} := by
  rw [M24G.duad_setClass_mul]
  congr 1
  ext i
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rcases h1 with rfl | rfl
      · exact absurd (Or.inl rfl) h2
      · exact Or.inl rfl
    · rcases h1 with rfl | rfl
      · exact absurd (Or.inl rfl) h2
      · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inr rfl, by
        rintro (h | h)
        · exact absurd h (by decide)
        · exact hk1 h.symm⟩
    · exact Or.inr ⟨Or.inr rfl, by
        rintro (h | h)
        · exact hk0 h
        · exact hk1 h⟩

theorem setClass_ne_of_ne {D D' : Finset (Fin 24)} (hD : D.card = 2) (hD' : D'.card = 2)
    (hne : D ≠ D') : M24G.setClass D ≠ M24G.setClass D' :=
  fun h => hne (M24G.setClass_injOn_duads hD hD' h)

theorem card_triadSp {k : Fin 24} (hk0 : k ≠ 0) (hk1 : k ≠ 1) : Nat.card (triadSp k) = 4 := by
  classical
  have h01 : ({0, 1} : Finset (Fin 24)).card = 2 := Finset.card_pair (by decide)
  have h0k : ({0, k} : Finset (Fin 24)).card = 2 := Finset.card_pair hk0.symm
  have h1k : ({1, k} : Finset (Fin 24)).card = 2 := Finset.card_pair hk1.symm
  have hab := setClass01_mul k hk0 hk1
  have hne1 : ({0, 1} : Finset (Fin 24)) ≠ {0, k} := by
    intro h
    have : (1 : Fin 24) ∈ ({0, k} : Finset (Fin 24)) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact absurd h' (by decide)
    · exact hk1 h'.symm
  have hne2 : ({0, 1} : Finset (Fin 24)) ≠ {1, k} := by
    intro h
    have : (0 : Fin 24) ∈ ({1, k} : Finset (Fin 24)) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact absurd h' (by decide)
    · exact hk0 h'.symm
  have hne3 : ({0, k} : Finset (Fin 24)) ≠ {1, k} := by
    intro h
    have : (0 : Fin 24) ∈ ({1, k} : Finset (Fin 24)) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact absurd h' (by decide)
    · exact hk0 h'.symm
  have h3 : M24G.setClass {0, 1} * M24G.setClass {0, k} ≠ 1 := by
    rw [hab]
    exact M24G.setClass_ne_one_of_card_two h1k
  have h5 : M24G.setClass {0, 1} ≠ M24G.setClass {0, 1} * M24G.setClass {0, k} := by
    rw [hab]
    exact setClass_ne_of_ne h01 h1k hne2
  have h6 : M24G.setClass {0, k} ≠ M24G.setClass {0, 1} * M24G.setClass {0, k} := by
    rw [hab]
    exact setClass_ne_of_ne h0k h1k hne3
  exact card_closure_pair_of_sq (M24G.W11_mul_self _) (M24G.W11_mul_self _)
    (M24G.setClass_ne_one_of_card_two h01) (M24G.setClass_ne_one_of_card_two h0k) h3
    (setClass_ne_of_ne h01 h0k hne1) h5 h6

@[expose] noncomputable def UE (k : Fin 24) : Subgroup G :=
  ((triadSp k).comap r.todd.toMonoidHom).map c.E.subtype

theorem mem_UE {k : Fin 24} {x : G} : x ∈ r.UE k ↔ ∃ hx : x ∈ c.E, r.todd ⟨x, hx⟩ ∈ triadSp k := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem UE_le_E (k : Fin 24) : r.UE k ≤ c.E := by
  intro x hx
  obtain ⟨hxE, -⟩ := (r.mem_UE).mp hx
  exact hxE

theorem card_UE {k : Fin 24} (hk0 : k ≠ 0) (hk1 : k ≠ 1) : Nat.card (r.UE k) = 4 := by
  have hinj : Function.Injective c.E.subtype := c.E.subtype_injective
  rw [UE, Subgroup.card_map_of_injective hinj]
  have hsurj : Function.Surjective r.todd.toMonoidHom := r.todd.surjective
  rw [← card_triadSp hk0 hk1]
  exact Nat.card_congr ((Subgroup.comap r.todd.toMonoidHom (triadSp k)).equivMapOfInjective
    r.todd.toMonoidHom r.todd.injective |>.toEquiv.trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective hsurj _)).toEquiv)

@[expose] noncomputable def elemOf (w : W11) : G := (r.todd.symm w : ↥c.E)

theorem elemOf_mem (w : W11) : r.elemOf w ∈ c.E := (r.todd.symm w).2

theorem todd_elemOf (w : W11) : r.todd ⟨r.elemOf w, r.elemOf_mem w⟩ = w :=
  r.todd.apply_symm_apply w

theorem eq_of_todd_eq {a b : G} (ha : a ∈ c.E) (hb : b ∈ c.E)
    (h : r.todd ⟨a, ha⟩ = r.todd ⟨b, hb⟩) : a = b :=
  congrArg Subtype.val (r.todd.injective h)

theorem conj_eq_iff (h : ↥c.G1) {e : G} (he : e ∈ c.E) :
    (h : G) * e * (h : G)⁻¹ = e ↔
      rho11 AutPerm le_rfl ⟨r.φ h, r.toResM24.φ_mem h⟩ (r.todd ⟨e, he⟩) = r.todd ⟨e, he⟩ := by
  rw [← todd_conj r h he]
  constructor
  · intro h1
    exact congrArg r.todd (Subtype.ext h1)
  · intro h1
    exact r.eq_of_todd_eq _ he h1

theorem perm_smul_pair (σ : S24) (a b : Fin 24) : σ • ({a, b} : Finset (Fin 24)) = {σ a, σ b} := by
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton]
  rfl

theorem rho_setClass_eq_iff {σ : S24} (hσ : σ ∈ M24g) {D : Finset (Fin 24)} (hD : D.card = 2) :
    rho11 AutPerm le_rfl ⟨σ, hσ⟩ (M24G.setClass D) = M24G.setClass D ↔ σ • D = D := by
  rw [← M24G.setClass_smul hσ (by rw [hD]; decide)]
  constructor
  · intro h
    exact M24G.setClass_injOn_duads (by rw [Finset.card_smul_finset, hD]) hD h
  · intro h
    rw [h]

theorem fix_two_of_smul {σ : S24} (h01 : σ • ({0, 1} : Finset (Fin 24)) = {0, 1})
    (h02 : σ • ({0, 2} : Finset (Fin 24)) = {0, 2} ∨ σ • ({0, 2} : Finset (Fin 24)) = {1, 2}) :
    σ 2 = 2 ∧ ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) := by
  rw [perm_smul_pair] at h01 h02
  have h0 : σ 0 ∈ ({0, 1} : Finset (Fin 24)) := h01 ▸ by simp
  have h1 : σ 1 ∈ ({0, 1} : Finset (Fin 24)) := h01 ▸ by simp
  have h2 : σ 2 ∈ ({0, 2} : Finset (Fin 24)) ∨ σ 2 ∈ ({1, 2} : Finset (Fin 24)) := by
    rcases h02 with h | h
    · exact Or.inl (h ▸ by simp)
    · exact Or.inr (h ▸ by simp)
  have hne01 : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
  have hne02 : σ 0 ≠ σ 2 := fun h => absurd (σ.injective h) (by decide)
  have hne12 : σ 1 ≠ σ 2 := fun h => absurd (σ.injective h) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 h2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with (h2 | h2) | (h2 | h2)
  all_goals first
    | exact absurd (h0.trans h1.symm) hne01
    | exact absurd (h0.trans h2.symm) hne02
    | exact absurd (h1.trans h2.symm) hne12
    | exact ⟨h2, Or.inl ⟨h0, h1⟩⟩
    | exact ⟨h2, Or.inr ⟨h0, h1⟩⟩

theorem E_sq {e : G} (he : e ∈ c.E) : e * e = 1 := by
  have := c.E_elem.2 e he
  simpa [pow_two] using this

theorem E_comm {a b : G} (ha : a ∈ c.E) (hb : b ∈ c.E) : a * b = b * a :=
  congrArg Subtype.val (c.E_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem phi_smul01 (h : ↥c.G1) (hC : (h : G) ∈ centralizer ({r.tE} : Set G)) :
    r.φ h • ({0, 1} : Finset (Fin 24)) = {0, 1} := by
  have h1 : (h : G) * r.tE * (h : G)⁻¹ = r.tE := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hC, mul_inv_cancel_right]
  rw [r.conj_eq_iff h r.tE_mem, r.todd_tE] at h1
  exact (rho_setClass_eq_iff (r.toResM24.φ_mem h) (by decide)).mp h1

theorem smul01_of_mem_stabS1 {σ : S24} (hσ : σ ∈ M24G.stabS1) :
    σ • ({0, 1} : Finset (Fin 24)) = {0, 1} := by
  obtain ⟨-, -, h | h⟩ := M24G.mem_stabS1.mp hσ
  · rw [perm_smul_pair, h.1, h.2]
  · rw [perm_smul_pair, h.1, h.2, Finset.pair_comm]

theorem smul02_of_mem_stabS1 {σ : S24} (hσ : σ ∈ M24G.stabS1) :
    σ • ({0, 2} : Finset (Fin 24)) = {0, 2} ∨ σ • ({0, 2} : Finset (Fin 24)) = {1, 2} := by
  obtain ⟨-, h2, h | h⟩ := M24G.mem_stabS1.mp hσ
  · left
    rw [perm_smul_pair, h.1, h2]
  · right
    rw [perm_smul_pair, h.1, h2]

theorem rho_mem_triadSp_of_stabS1 {σ : S24} (hσS : σ ∈ M24G.stabS1) (hσ : σ ∈ M24g) {w : W11}
    (hw : w ∈ triadSp 2) : rho11 AutPerm le_rfl ⟨σ, hσ⟩ w ∈ triadSp 2 := by
  have hle : triadSp 2 ≤ (triadSp 2).comap (rho11 AutPerm le_rfl ⟨σ, hσ⟩).toMonoidHom := by
    conv_lhs => rw [triadSp]
    rw [Subgroup.closure_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rcases hv with rfl | rfl
    · rw [(rho_setClass_eq_iff hσ (by decide)).mpr (smul01_of_mem_stabS1 hσS), mem_triadSp]
      exact Or.inr (Or.inl rfl)
    · rw [← M24G.setClass_smul hσ (by decide), mem_triadSp]
      rcases smul02_of_mem_stabS1 hσS with h | h
      · rw [h]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [h, ← setClass01_mul 2 (by decide) (by decide)]
        exact Or.inr (Or.inr (Or.inr rfl))
  have h := hle hw
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at h

theorem conj_mem_UE_of_stabS1 (y : ↥c.G1) (hy : r.φ y ∈ M24G.stabS1) {v : G}
    (hv : v ∈ r.UE 2) : (y : G) * v * (y : G)⁻¹ ∈ r.UE 2 := by
  obtain ⟨hvE, hvT⟩ := (r.mem_UE).mp hv
  refine (r.mem_UE).mpr ⟨c.conj_mem_E y hvE, ?_⟩
  rw [todd_conj r y hvE]
  exact rho_mem_triadSp_of_stabS1 hy (r.toResM24.φ_mem y) hvT

theorem mem_normalizer_UE_of_stabS1 (y : ↥c.G1) (hy : r.φ y ∈ M24G.stabS1) :
    (y : G) ∈ normalizer (r.UE 2 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => r.conj_mem_UE_of_stabS1 y hy hv, fun hv => ?_⟩
  have hy' : r.φ y⁻¹ ∈ M24G.stabS1 := by rw [map_inv]; exact M24G.stabS1.inv_mem hy
  have := r.conj_mem_UE_of_stabS1 y⁻¹ hy' hv
  simpa [mul_assoc] using this

theorem phi_mem_stabS1 (b : ↥c.G1) (hbC : (b : G) ∈ centralizer ({r.tE} : Set G))
    (hbN : (b : G) ∈ normalizer (r.UE 2 : Set G)) : r.φ b ∈ M24G.stabS1 := by
  have h01 := r.phi_smul01 b hbC
  have hu : r.elemOf (M24G.setClass {0, 2}) ∈ r.UE 2 :=
    (r.mem_UE).mpr ⟨r.elemOf_mem _, by
      rw [r.todd_elemOf, mem_triadSp]
      exact Or.inr (Or.inr (Or.inl rfl))⟩
  have hbu := (Subgroup.mem_normalizer_iff.mp hbN _).mp hu
  obtain ⟨hbuE, hbuT⟩ := (r.mem_UE).mp hbu
  rw [todd_conj r b (r.elemOf_mem _), r.todd_elemOf,
    ← M24G.setClass_smul (r.toResM24.φ_mem b) (by decide), mem_triadSp] at hbuT
  have hcard : (r.φ b • ({0, 2} : Finset (Fin 24))).card = 2 := by
    rw [Finset.card_smul_finset]; decide
  have h02 : r.φ b • ({0, 2} : Finset (Fin 24)) = {0, 2} ∨
      r.φ b • ({0, 2} : Finset (Fin 24)) = {1, 2} := by
    rcases hbuT with h | h | h | h
    · exact absurd h (M24G.setClass_ne_one_of_card_two hcard)
    · have h' := M24G.setClass_injOn_duads hcard (by decide) h
      rw [← h01] at h'
      exact absurd (smul_left_cancel _ h') (by decide)
    · exact Or.inl (M24G.setClass_injOn_duads hcard (by decide) h)
    · rw [setClass01_mul 2 (by decide) (by decide)] at h
      exact Or.inr (M24G.setClass_injOn_duads hcard (by decide) h)
  obtain ⟨h2, h01'⟩ := fix_two_of_smul h01 h02
  exact M24G.mem_stabS1.mpr ⟨r.toResM24.φ_mem b, h2, h01'⟩

theorem not_mem_triadSp_of_isSextClass {w : W11} (hw : M24G.IsSextClass w) : w ∉ triadSp 2 := by
  intro h
  obtain ⟨U, hU, rfl⟩ := hw
  rw [mem_triadSp] at h
  rcases h with h | h | h | h
  · exact M24G.sextClass_ne_one hU h
  · exact M24G.not_isSextClass_of_isDuadClass ⟨{0, 1}, by decide, h.symm⟩ ⟨U, hU, rfl⟩
  · exact M24G.not_isSextClass_of_isDuadClass ⟨{0, 2}, by decide, h.symm⟩ ⟨U, hU, rfl⟩
  · rw [setClass01_mul 2 (by decide) (by decide)] at h
    exact M24G.not_isSextClass_of_isDuadClass ⟨{1, 2}, by decide, h.symm⟩ ⟨U, hU, rfl⟩

theorem setClass03_not_mem_triadSp : M24G.setClass {0, 3} ∉ triadSp 2 := by
  intro h
  rw [mem_triadSp] at h
  rcases h with h | h | h | h
  · exact M24G.setClass_ne_one_of_card_two (by decide) h
  · exact absurd (M24G.setClass_injOn_duads (by decide) (by decide) h) (by decide)
  · exact absurd (M24G.setClass_injOn_duads (by decide) (by decide) h) (by decide)
  · rw [setClass01_mul 2 (by decide) (by decide)] at h
    exact absurd (M24G.setClass_injOn_duads (by decide) (by decide) h) (by decide)

theorem card_le_of_phi_mem (S : Subgroup S24)
    (hS : ∀ B : Subgroup S24, B ≤ S → (∀ b ∈ B, b * b = 1) → Nat.card B ≤ 16) (B : Subgroup G)
    (hB : ∀ b ∈ B, ∃ hb : b ∈ c.G1, r.φ ⟨b, hb⟩ ∈ S) (hBG1 : B ≤ c.G1)
    (hB2 : ∀ b ∈ B, b * b = 1) : Nat.card B ≤ Nat.card ↥(B ⊓ c.E) * 2 ^ 4 := by
  have hst : (B.subgroupOf c.G1).map r.φ ≤ S := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨hbG1, h⟩ := hB b (Subgroup.mem_subgroupOf.mp hb)
    exact h
  have hsq : ∀ σ ∈ (B.subgroupOf c.G1).map r.φ, σ * σ = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hB2 _ (Subgroup.mem_subgroupOf.mp hb))
    rw [this, map_one]
  have h16 := hS _ hst hsq
  have hcard := c.card_map_mul_card_inf r B hBG1
  calc Nat.card B = Nat.card ↥((B.subgroupOf c.G1).map r.φ) * Nat.card ↥(B ⊓ c.E) :=
        hcard.symm
    _ ≤ 16 * Nat.card ↥(B ⊓ c.E) := Nat.mul_le_mul_right _ h16
    _ = Nat.card ↥(B ⊓ c.E) * 2 ^ 4 := by ring

theorem centralizer_inf_normalizer_UE_le (hI : Sec7Inputs) (hJ : HypJ4 G z)
    (hmax : Stmt5_Max13) (h2c : Stmt5_2c) (hN : NormalTwoSextet) :
    centralizer ({r.tE} : Set G) ⊓ normalizer (r.UE 2 : Set G) ≤ c.G1 := by
  classical
  have hE2 : ∀ e ∈ c.E, e * e = 1 := fun e he => E_sq he
  have hEc : ∀ a ∈ c.E, ∀ b ∈ c.E, a * b = b * a := fun a ha b hb => E_comm ha hb
  set X : Subgroup G := centralizer ({r.tE} : Set G) ⊓ normalizer (r.UE 2 : Set G) with hX
  have hUE := r.UE_le_E 2
  have hEX : c.E ≤ X := by
    intro e he
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hEc e he _ r.tE_mem
    · rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        have : e * n * e⁻¹ = n := by rw [hEc e he n (hUE hn), mul_inv_cancel_right]
        rw [this]
        exact hn
      · intro hn
        have hnE : n ∈ c.E := by
          have h' : n = e⁻¹ * (e * n * e⁻¹) * e := by group
          rw [h']
          exact c.E.mul_mem (c.E.mul_mem (c.E.inv_mem he) (hUE hn)) he
        have : e * n * e⁻¹ = n := by rw [hEc e he n hnE, mul_inv_cancel_right]
        rw [← this]
        exact hn
  have hNX : ∀ g ∈ X, ∀ n ∈ r.UE 2, g * n * g⁻¹ ∈ r.UE 2 := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hg).2 n).mp hn
  have hTI : ∀ g ∈ X, ∀ e ∈ c.E, e ∉ r.UE 2 → g * e * g⁻¹ ∈ c.E →
      g ∈ normalizer (c.E : Set G) := by
    intro g hg e he heN hge
    by_contra hgM
    have hgC := (Subgroup.mem_inf.mp hg).1
    have hgN := (Subgroup.mem_inf.mp hg).2
    have h4 := r.card_inter_le_four hI hJ hmax h2c hN hgC hgM
    have hUle : r.UE 2 ≤ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom := by
      intro u hu
      refine Subgroup.mem_inf.mpr ⟨hUE hu, ?_⟩
      have hu' : g⁻¹ * u * g ∈ r.UE 2 := (Subgroup.mem_normalizer_iff''.mp hgN u).mp hu
      exact ⟨g⁻¹ * u * g, hUE hu', by simp [MulAut.conj_apply, mul_assoc]⟩
    have hgeIn : g * e * g⁻¹ ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_inf.mpr ⟨hge, ⟨e, he, rfl⟩⟩
    have hgeN : g * e * g⁻¹ ∉ r.UE 2 := fun h =>
      heN ((Subgroup.mem_normalizer_iff.mp hgN e).mpr h)
    have hlt : r.UE 2 < c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom :=
      lt_of_le_of_ne hUle (fun h => hgeN (by rw [h]; exact hgeIn))
    have hc := Subgroup.card_lt_of_lt hlt
    rw [r.card_UE (by decide) (by decide)] at hc
    omega
  have hxE := r.elemOf_mem M24G.x1120
  have hfE := r.elemOf_mem (M24G.setClass {0, 3})
  have hxN : r.elemOf M24G.x1120 ∉ r.UE 2 := by
    intro h
    obtain ⟨hx, hmem⟩ := (r.mem_UE).mp h
    rw [r.todd_elemOf] at hmem
    exact not_mem_triadSp_of_isSextClass M24G.isSextClass_x1120 hmem
  have hfN : r.elemOf (M24G.setClass {0, 3}) ∉ r.UE 2 := by
    intro h
    obtain ⟨hf, hmem⟩ := (r.mem_UE).mp h
    rw [r.todd_elemOf] at hmem
    exact setClass03_not_mem_triadSp hmem
  have hrank : ∀ e ∈ c.E, ∀ B : Subgroup G, B ≤ X ⊓ normalizer (c.E : Set G) →
      (∀ b ∈ B, e⁻¹ * (b * e * b⁻¹) ∈ r.UE 2) → (∀ b ∈ B, b * b = 1) →
      Nat.card B ≤ Nat.card ↥(B ⊓ c.E) * 2 ^ 4 := by
    intro e _ B hB _ hB2
    have hBG1 : B ≤ c.G1 := fun b hb => (Subgroup.mem_inf.mp (hB hb)).2
    refine r.card_le_of_phi_mem M24G.stabS1 M24G.card_le_sixteen_stabS1 B
      (fun b hb => ⟨hBG1 hb, ?_⟩) hBG1 hB2
    have hbX := (Subgroup.mem_inf.mp (hB hb)).1
    exact r.phi_mem_stabS1 ⟨b, hBG1 hb⟩ (Subgroup.mem_inf.mp hbX).1 (Subgroup.mem_inf.mp hbX).2
  have hk : (Nat.card ↥(r.UE 2) * 2 ^ 4) ^ 2 < Nat.card c.E * Nat.card ↥(r.UE 2) := by
    rw [r.card_UE (by decide) (by decide), c.card_E]
    norm_num
  have hfusx := CFSG.GroupTheory.TIFusion.fusion_of_rank X c.E (r.UE 2) hEX hUE hNX hE2 hEc
    hTI hxE hxN 4 (hrank _ hxE) hk
  have hfusf := CFSG.GroupTheory.TIFusion.fusion_of_rank X c.E (r.UE 2) hEX hUE hNX hE2 hEc
    hTI hfE hfN 4 (hrank _ hfE) hk
  have hsat : ∀ n ∈ r.UE 2, ∃ y ∈ X ⊓ normalizer (c.E : Set G),
      y * r.elemOf M24G.x1120 * y⁻¹ = r.elemOf M24G.x1120 * n := by
    intro n hn
    obtain ⟨hnE, hnT⟩ := (r.mem_UE).mp hn
    by_cases hn1 : n = 1
    · exact ⟨1, Subgroup.one_mem _, by rw [hn1]; group⟩
    have hu : r.todd ⟨n, hnE⟩ ∈ ({M24G.setClass {0, 1}, M24G.setClass {0, 2},
        M24G.setClass {0, 1} * M24G.setClass {0, 2}} : Set W11) := by
      rcases mem_triadSp.mp hnT with h | h | h | h
      · exfalso
        apply hn1
        exact r.eq_of_todd_eq hnE (Subgroup.one_mem _) (h.trans (map_one r.todd).symm)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨σ, hσS, hσ, hσx⟩ := M24G.x1120_sat _ hu
    obtain ⟨y, hy⟩ := r.toResM24.exists_φ_eq hσ
    have hyS : r.φ y ∈ M24G.stabS1 := by rw [show r.φ y = σ from hy]; exact hσS
    refine ⟨y, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, r.mem_normalizer_UE_of_stabS1 y hyS⟩,
      y.2⟩, ?_⟩
    · have h01 := smul01_of_mem_stabS1 hyS
      have := (rho_setClass_eq_iff (r.toResM24.φ_mem y) (by decide)).mpr h01
      rw [← r.todd_tE, ← r.conj_eq_iff y r.tE_mem] at this
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * r.tE = (y : G) * r.tE * (y : G)⁻¹ * y := by group
        _ = r.tE * y := by rw [this]
    · apply r.eq_of_todd_eq (c.conj_mem_E y hxE) (c.E.mul_mem hxE hnE)
      rw [todd_conj r y hxE, r.todd_elemOf]
      have hmul : r.todd ⟨r.elemOf M24G.x1120 * n, c.E.mul_mem hxE hnE⟩ =
          r.todd ⟨r.elemOf M24G.x1120, hxE⟩ * r.todd ⟨n, hnE⟩ := by
        rw [← map_mul]
        rfl
      rw [hmul, r.todd_elemOf]
      have hσ' : (⟨r.φ y, r.toResM24.φ_mem y⟩ : ↥AutPerm) = ⟨σ, hσ⟩ := Subtype.ext hy
      rw [hσ']
      exact hσx
  have hdist : ∀ y ∈ X ⊓ normalizer (c.E : Set G),
      y * r.elemOf M24G.x1120 * y⁻¹ ≠ r.elemOf (M24G.setClass {0, 3}) := by
    intro y hy heq
    have hyG1 : y ∈ c.G1 := (Subgroup.mem_inf.mp hy).2
    have h1 := todd_conj r ⟨y, hyG1⟩ hxE
    rw [r.todd_elemOf] at h1
    obtain ⟨U, hU, hUx⟩ := M24G.isSextClass_x1120
    have hs : M24G.IsSextClass (r.todd ⟨y * r.elemOf M24G.x1120 * y⁻¹,
        c.conj_mem_E ⟨y, hyG1⟩ hxE⟩) := by
      rw [h1, ← hUx, ← M24G.sextClass_smul (r.toResM24.φ_mem _) hU]
      exact ⟨_, (M24G.isSextet_smul_iff (r.toResM24.φ_mem _)).2 hU, rfl⟩
    have heq' : r.todd ⟨y * r.elemOf M24G.x1120 * y⁻¹, c.conj_mem_E ⟨y, hyG1⟩ hxE⟩ =
        M24G.setClass {0, 3} := by
      rw [← r.todd_elemOf (M24G.setClass {0, 3})]
      exact congrArg r.todd (Subtype.ext heq)
    rw [heq'] at hs
    exact M24G.not_isSextClass_of_isDuadClass ⟨{0, 3}, by decide, rfl⟩ hs
  exact CFSG.GroupTheory.TIFusion.le_normalizer_of_ti X c.E (r.UE 2) hEX hUE hNX hE2 hEc hTI
    hxE hxN hfE hfN hfusx hfusf hsat hdist

theorem rho_mem_triadSp_of {σ : S24} (hσ : σ ∈ M24g)
    (h01 : σ • ({0, 1} : Finset (Fin 24)) = {0, 1}) {k₁ k₂ : Fin 24} (hk₁0 : k₁ ≠ 0)
    (hk₂0 : k₂ ≠ 0) (hk₂1 : k₂ ≠ 1) (hk : σ k₁ = k₂) {w : W11} (hw : w ∈ triadSp k₁) :
    rho11 AutPerm le_rfl ⟨σ, hσ⟩ w ∈ triadSp k₂ := by
  have h0 : σ 0 = 0 ∨ σ 0 = 1 := by
    rw [perm_smul_pair] at h01
    have : σ 0 ∈ ({0, 1} : Finset (Fin 24)) := h01 ▸ by simp
    simpa using this
  have hle : triadSp k₁ ≤ (triadSp k₂).comap (rho11 AutPerm le_rfl ⟨σ, hσ⟩).toMonoidHom := by
    conv_lhs => rw [triadSp]
    rw [Subgroup.closure_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rcases hv with rfl | rfl
    · rw [(rho_setClass_eq_iff hσ (by decide)).mpr h01, mem_triadSp]
      exact Or.inr (Or.inl rfl)
    · have hev : Even ({0, k₁} : Finset (Fin 24)).card := by
        rw [Finset.card_pair hk₁0.symm]
        decide
      rw [← M24G.setClass_smul hσ hev, perm_smul_pair, hk, mem_triadSp]
      rcases h0 with h0 | h0
      · rw [h0]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [h0, ← setClass01_mul k₂ hk₂0 hk₂1]
        exact Or.inr (Or.inr (Or.inr rfl))
  have h := hle hw
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at h

theorem conj_mem_UE_iff (m : ↥c.G1) (h01 : r.φ m • ({0, 1} : Finset (Fin 24)) = {0, 1})
    {k : Fin 24} (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hm2 : r.φ m 2 = k) (u : G) :
    u ∈ r.UE 2 ↔ (m : G) * u * (m : G)⁻¹ ∈ r.UE k := by
  constructor
  · intro hu
    obtain ⟨huE, huT⟩ := (r.mem_UE).mp hu
    refine (r.mem_UE).mpr ⟨c.conj_mem_E m huE, ?_⟩
    rw [todd_conj r m huE]
    exact rho_mem_triadSp_of (r.toResM24.φ_mem m) h01 (by decide) hk0 hk1 hm2 huT
  · intro hu
    obtain ⟨huE', huT⟩ := (r.mem_UE).mp hu
    have huE : u ∈ c.E := by
      have h' : u = (m : G)⁻¹ * ((m : G) * u * (m : G)⁻¹) * m := by group
      rw [h']
      have := c.conj_mem_E m⁻¹ huE'
      simpa using this
    refine (r.mem_UE).mpr ⟨huE, ?_⟩
    have hmi01 : r.φ m⁻¹ • ({0, 1} : Finset (Fin 24)) = {0, 1} := by
      rw [map_inv]
      conv_lhs => rw [← h01]
      rw [inv_smul_smul]
    have hmi2 : r.φ m⁻¹ k = 2 := by
      rw [map_inv, ← hm2]
      exact (r.φ m).symm_apply_apply 2
    have h := rho_mem_triadSp_of (r.toResM24.φ_mem m⁻¹) hmi01 hk0 (by decide) (by decide) hmi2 huT
    rw [← todd_conj r m⁻¹ huE'] at h
    have heq : (⟨((m⁻¹ : ↥c.G1) : G) * ((m : G) * u * (m : G)⁻¹) * ((m⁻¹ : ↥c.G1) : G)⁻¹,
        c.conj_mem_E m⁻¹ huE'⟩ : ↥c.E) = ⟨u, huE⟩ := by
      apply Subtype.ext
      simp only [InvMemClass.coe_inv]
      group
    rw [heq] at h
    exact h

theorem mem_centralizer_tE_of (m : ↥c.G1) (h01 : r.φ m • ({0, 1} : Finset (Fin 24)) = {0, 1}) :
    (m : G) ∈ centralizer ({r.tE} : Set G) := by
  have := (rho_setClass_eq_iff (r.toResM24.φ_mem m) (by decide)).mpr h01
  rw [← r.todd_tE, ← r.conj_eq_iff m r.tE_mem] at this
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (m : G) * r.tE = (m : G) * r.tE * (m : G)⁻¹ * m := by group
    _ = r.tE * m := by rw [this]

theorem centralizer_inf_normalizer_UE_le_of (hI : Sec7Inputs) (hJ : HypJ4 G z)
    (hmax : Stmt5_Max13) (h2c : Stmt5_2c) (hN : NormalTwoSextet)
    {k : Fin 24} (hk0 : k ≠ 0)
    (hk1 : k ≠ 1) :
    centralizer ({r.tE} : Set G) ⊓ normalizer (r.UE k : Set G) ≤ c.G1 := by
  obtain ⟨σ, hσ, h01, h2⟩ := M24G.exists_stab01_smul k hk0 hk1
  obtain ⟨m, hm⟩ := r.toResM24.exists_φ_eq hσ
  have hm01 : r.φ m • ({0, 1} : Finset (Fin 24)) = {0, 1} := by rw [show r.φ m = σ from hm]; exact h01
  have hm2 : r.φ m 2 = k := by rw [show r.φ m = σ from hm]; exact h2
  have hmC := r.mem_centralizer_tE_of m hm01
  intro y hy
  obtain ⟨hyC, hyN⟩ := Subgroup.mem_inf.mp hy
  set y' : G := (m : G)⁻¹ * y * m with hy'
  have hy'C : y' ∈ centralizer ({r.tE} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmC) hyC) hmC
  have hy'N : y' ∈ normalizer (r.UE 2 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [r.conj_mem_UE_iff m hm01 hk0 hk1 hm2 u,
      r.conj_mem_UE_iff m hm01 hk0 hk1 hm2 (y' * u * y'⁻¹),
      Subgroup.mem_normalizer_iff.mp hyN ((m : G) * u * (m : G)⁻¹)]
    have heq : (m : G) * (y' * u * y'⁻¹) * (m : G)⁻¹ = y * ((m : G) * u * (m : G)⁻¹) * y⁻¹ := by
      rw [hy']
      group
    rw [heq]
  have hy'M := r.centralizer_inf_normalizer_UE_le hI hJ hmax h2c hN
    (Subgroup.mem_inf.mpr ⟨hy'C, hy'N⟩)
  have : y = (m : G) * y' * (m : G)⁻¹ := by rw [hy']; group
  rw [this]
  exact c.G1.mul_mem (c.G1.mul_mem m.2 hy'M) (c.G1.inv_mem m.2)

theorem mem_zpowers_tE {n : G} : n ∈ zpowers r.tE ↔ n = 1 ∨ n = r.tE := by
  constructor
  · intro hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact zpow_eq_one_or_self (E_sq r.tE_mem) k
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem card_zpowers_tE : Nat.card (zpowers r.tE) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact E_sq r.tE_mem) r.tE_ne_one

theorem elemOf_ne_one {w : W11} (hw : w ≠ 1) : r.elemOf w ≠ 1 := by
  intro h
  apply hw
  rw [← r.todd_elemOf w]
  have h1 : (⟨r.elemOf w, r.elemOf_mem w⟩ : ↥c.E) = 1 := Subtype.ext h
  rw [h1, map_one]

theorem elemOf_ne_tE {w : W11} (hw : w ≠ M24G.setClass {0, 1}) : r.elemOf w ≠ r.tE := by
  intro h
  apply hw
  rw [← r.todd_elemOf w, ← r.todd_tE]
  exact congrArg r.todd (Subtype.ext h)

theorem rho_todd_of_mem_zpowers (b : ↥c.G1) {e : G} (he : e ∈ c.E)
    (h : e⁻¹ * ((b : G) * e * (b : G)⁻¹) ∈ zpowers r.tE) :
    rho11 AutPerm le_rfl ⟨r.φ b, r.toResM24.φ_mem b⟩ (r.todd ⟨e, he⟩) = r.todd ⟨e, he⟩ ∨
      rho11 AutPerm le_rfl ⟨r.φ b, r.toResM24.φ_mem b⟩ (r.todd ⟨e, he⟩) =
        r.todd ⟨e, he⟩ * M24G.setClass {0, 1} := by
  rw [← todd_conj r b he]
  rcases (r.mem_zpowers_tE).mp h with h1 | h1
  · exact Or.inl (congrArg r.todd (Subtype.ext (inv_mul_eq_one.mp h1).symm))
  · right
    have hy : (b : G) * e * (b : G)⁻¹ = e * r.tE := by rw [← h1, mul_inv_cancel_left]
    rw [← r.todd_tE, ← map_mul]
    exact congrArg r.todd (Subtype.ext hy)

theorem exists_duad_eq {D : Finset (Fin 24)} (hD : D.card = 2)
    (h : (({0, 1} : Finset (Fin 24)) ∩ D).card = 1) :
    ∃ k : Fin 24, k ≠ 0 ∧ k ≠ 1 ∧ (D = {0, k} ∨ D = {1, k}) := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hD
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hmem : ∀ b : Fin 24, (b = 0 ∨ b = 1) → (b = x ∨ b = y) → b = a := by
    intro b hb1 hb2
    have : b ∈ ({0, 1} : Finset (Fin 24)) ∩ {x, y} := by
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hb1, hb2⟩
    rw [ha] at this
    exact Finset.mem_singleton.mp this
  have haI : a ∈ ({0, 1} : Finset (Fin 24)) ∩ {x, y} := by
    rw [ha]
    exact Finset.mem_singleton_self a
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at haI
  obtain ⟨ha01, hax | hay⟩ := haI
  · have hy0 : y ≠ 0 := fun hy => hxy ((hmem y (Or.inl hy) (Or.inr rfl)).trans hax).symm
    have hy1 : y ≠ 1 := fun hy => hxy ((hmem y (Or.inr hy) (Or.inr rfl)).trans hax).symm
    rw [← hax]
    rcases ha01 with rfl | rfl
    · exact ⟨y, hy0, hy1, Or.inl rfl⟩
    · exact ⟨y, hy0, hy1, Or.inr rfl⟩
  · have hx0 : x ≠ 0 := fun hx => hxy ((hmem x (Or.inl hx) (Or.inl rfl)).trans hay)
    have hx1 : x ≠ 1 := fun hx => hxy ((hmem x (Or.inr hx) (Or.inl rfl)).trans hay)
    rw [← hay]
    rcases ha01 with rfl | rfl
    · exact ⟨x, hx0, hx1, Or.inl (Finset.pair_comm _ _)⟩
    · exact ⟨x, hx0, hx1, Or.inr (Finset.pair_comm _ _)⟩

theorem map_conj_comm {g a b : G} (ha : a ∈ c.E.map (MulAut.conj g).toMonoidHom)
    (hb : b ∈ c.E.map (MulAut.conj g).toMonoidHom) : a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
    _ = g * (b' * a') * g⁻¹ := by rw [E_comm ha' hb']
    _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group

theorem isDuadClass_of_mem_inter (hI : Sec7Inputs) (hJ : HypJ4 G z) (hmax : Stmt5_Max13)
    (h2c : Stmt5_2c) (hN : NormalTwoSextet)
    {g : G}
    (hg : g ∈ centralizer ({r.tE} : Set G)) (hgM : g ∉ c.G1) {e : G}
    (he : e ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom) (he1 : e ≠ 1) :
    M24G.IsDuadClass (r.todd ⟨e, (Subgroup.mem_inf.mp he).1⟩) := by
  have hw : r.todd ⟨e, (Subgroup.mem_inf.mp he).1⟩ ≠ 1 := by
    intro h
    exact he1 (r.eq_of_todd_eq _ (Subgroup.one_mem _) (h.trans (map_one r.todd).symm))
  rcases M24G.isDuadClass_or_isSextClass hw with hd | hs
  · exact hd
  · exfalso
    obtain ⟨m, -, hmz⟩ := (r.isSextClass_todd_iff _).1 hs
    exact r.not_isConj_z_of_mem_inter hI hJ hmax h2c hN hg hgM he (isConj_iff.mpr ⟨m, hmz⟩).symm

theorem exists_UE_le_map_conj (hI : Sec7Inputs) (hJ : HypJ4 G z) (hmax : Stmt5_Max13)
    (h2c : Stmt5_2c) (hN : NormalTwoSextet)
    {g : G}
    (hg : g ∈ centralizer ({r.tE} : Set G)) (hgM : g ∉ c.G1) {v : G}
    (hv : v ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom) (hv1 : v ≠ 1) (hvt : v ≠ r.tE) :
    ∃ k : Fin 24, k ≠ 0 ∧ k ≠ 1 ∧ r.UE k ≤ c.E.map (MulAut.conj g).toMonoidHom := by
  have hvE : v ∈ c.E := (Subgroup.mem_inf.mp hv).1
  have htI : r.tE ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_inf.mpr ⟨r.tE_mem, r.tE_mem_map_conj hg⟩
  have htvI : r.tE * v ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom := Subgroup.mul_mem _ htI hv
  have htvE : r.tE * v ∈ c.E := (Subgroup.mem_inf.mp htvI).1
  have htv1 : r.tE * v ≠ 1 := by
    intro h
    apply hvt
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (E_sq r.tE_mem)]
  obtain ⟨D, hD, hDv⟩ := r.isDuadClass_of_mem_inter hI hJ hmax h2c hN hg hgM hv hv1
  have hdtv := r.isDuadClass_of_mem_inter hI hJ hmax h2c hN hg hgM htvI htv1
  have htvc : r.todd ⟨r.tE * v, htvE⟩ = M24G.setClass {0, 1} * M24G.setClass D := by
    rw [← r.todd_tE, hDv, ← map_mul]
    rfl
  rw [htvc] at hdtv
  have hne : ({0, 1} : Finset (Fin 24)) ≠ D := by
    rintro rfl
    exact hvt (r.eq_of_todd_eq hvE r.tE_mem (by rw [← hDv, r.todd_tE]))
  have h1 := M24G.card_inter_of_isDuadClass_mul (by decide) hD hne hdtv
  obtain ⟨k, hk0, hk1, hDk⟩ := exists_duad_eq hD h1
  refine ⟨k, hk0, hk1, ?_⟩
  have h0k : ∃ w ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom, ∃ hw : w ∈ c.E,
      r.todd ⟨w, hw⟩ = M24G.setClass {0, k} := by
    rcases hDk with rfl | rfl
    · exact ⟨v, hv, hvE, hDv.symm⟩
    · refine ⟨r.tE * v, htvI, htvE, ?_⟩
      rw [htvc, ← setClass01_mul k hk0 hk1, ← mul_assoc, M24G.W11_mul_self, one_mul]
  obtain ⟨w, hwI, hwE, hwc⟩ := h0k
  have hmemV : ∀ {x : G} (hx : x ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom),
      r.todd ⟨x, (Subgroup.mem_inf.mp hx).1⟩ ∈
        ((c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom).subgroupOf c.E).map r.todd.toMonoidHom :=
    fun hx => ⟨⟨_, (Subgroup.mem_inf.mp hx).1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hTV : triadSp k ≤
      ((c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom).subgroupOf c.E).map r.todd.toMonoidHom := by
    rw [triadSp, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [← r.todd_tE]
      exact hmemV htI
    · rw [← hwc]
      exact hmemV hwI
  intro u hu
  obtain ⟨huE, huT⟩ := (r.mem_UE).mp hu
  obtain ⟨⟨x, hxE⟩, hx, hxu⟩ := Subgroup.mem_map.mp (hTV huT)
  rw [← r.eq_of_todd_eq hxE huE hxu]
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2

theorem centralizer_tE_le (hI : Sec7Inputs) (hJ : HypJ4 G z)
    (hmax : Stmt5_Max13) (h2c : Stmt5_2c) (hN : NormalTwoSextet) :
    centralizer ({r.tE} : Set G) ≤ c.G1 := by
  classical
  have hE2 : ∀ e ∈ c.E, e * e = 1 := fun e he => E_sq he
  have hEc : ∀ a ∈ c.E, ∀ b ∈ c.E, a * b = b * a := fun a ha b hb => E_comm ha hb
  have hNE : zpowers r.tE ≤ c.E := Subgroup.zpowers_le.mpr r.tE_mem
  have hEX : c.E ≤ centralizer ({r.tE} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEc e he _ r.tE_mem)
  have hNX : ∀ g ∈ centralizer ({r.tE} : Set G), ∀ n ∈ zpowers r.tE,
      g * n * g⁻¹ ∈ zpowers r.tE := by
    intro g hg n hn
    rcases (r.mem_zpowers_tE).mp hn with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers _
  have hTI : ∀ g ∈ centralizer ({r.tE} : Set G), ∀ e ∈ c.E, e ∉ zpowers r.tE →
      g * e * g⁻¹ ∈ c.E → g ∈ normalizer (c.E : Set G) := by
    intro g hg e he heN hge
    by_contra hgM
    have hv : g * e * g⁻¹ ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_inf.mpr ⟨hge, ⟨e, he, rfl⟩⟩
    have hv1 : g * e * g⁻¹ ≠ 1 := by
      intro h
      apply heN
      rw [show e = g⁻¹ * (g * e * g⁻¹) * g by group, h, mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    have hvt : g * e * g⁻¹ ≠ r.tE := by
      intro h
      apply heN
      have hgt : g⁻¹ * r.tE * g = r.tE := by
        rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hg, inv_mul_cancel_left]
      rw [show e = g⁻¹ * (g * e * g⁻¹) * g by group, h, hgt]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk0, hk1, hUk⟩ := r.exists_UE_le_map_conj hI hJ hmax h2c hN hg hgM hv hv1 hvt
    apply hgM
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (c.map_conj_E_eq_of_le_G1 fun w hw => ?_)
    have htw : r.tE ∈ c.E.map (MulAut.conj g).toMonoidHom := r.tE_mem_map_conj hg
    refine r.centralizer_inf_normalizer_UE_le_of hI hJ hmax h2c hN hk0 hk1
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (map_conj_comm hw htw), ?_⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [map_conj_comm hw (hUk hu), mul_inv_cancel_right]
      exact hu
    · intro hu
      have hu' : u ∈ c.E.map (MulAut.conj g).toMonoidHom := by
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) (hUk hu)) hw
        rwa [show w⁻¹ * (w * u * w⁻¹) * w = u by group] at this
      rwa [map_conj_comm hw hu', mul_inv_cancel_right] at hu
  have hx := r.elemOf_mem (M24G.setClass {0, 2})
  have hf := r.elemOf_mem M24G.f770
  have hxN : r.elemOf (M24G.setClass {0, 2}) ∉ zpowers r.tE := by
    rw [r.mem_zpowers_tE, not_or]
    exact ⟨r.elemOf_ne_one (M24G.setClass_ne_one_of_card_two (by decide)),
      r.elemOf_ne_tE fun h =>
        absurd (M24G.setClass_injOn_duads (by decide) (by decide) h) (by decide)⟩
  have hfN : r.elemOf M24G.f770 ∉ zpowers r.tE := by
    obtain ⟨U, hU, hUf⟩ := M24G.isSextClass_f770
    have hf1 : M24G.f770 ≠ 1 := by
      rw [← hUf]
      exact M24G.sextClass_ne_one hU
    rw [r.mem_zpowers_tE, not_or]
    refine ⟨r.elemOf_ne_one hf1, r.elemOf_ne_tE fun h => ?_⟩
    exact M24G.not_isSextClass_of_isDuadClass ⟨{0, 1}, by decide, h.symm⟩ M24G.isSextClass_f770
  have hrank : ∀ S : Subgroup S24,
      (∀ B : Subgroup S24, B ≤ S → (∀ b ∈ B, b * b = 1) → Nat.card B ≤ 16) → ∀ e ∈ c.E,
      (∀ b : ↥c.G1, (b : G) ∈ centralizer ({r.tE} : Set G) →
        e⁻¹ * ((b : G) * e * (b : G)⁻¹) ∈ zpowers r.tE → r.φ b ∈ S) →
      ∀ B : Subgroup G, B ≤ centralizer ({r.tE} : Set G) ⊓ normalizer (c.E : Set G) →
      (∀ b ∈ B, e⁻¹ * (b * e * b⁻¹) ∈ zpowers r.tE) → (∀ b ∈ B, b * b = 1) →
      Nat.card B ≤ Nat.card ↥(B ⊓ c.E) * 2 ^ 4 := by
    intro S hS e _ hSe B hB hBe hB2
    have hBG1 : B ≤ c.G1 := fun b hb => (Subgroup.mem_inf.mp (hB hb)).2
    exact r.card_le_of_phi_mem S hS B (fun b hb => ⟨hBG1 hb,
      hSe ⟨b, hBG1 hb⟩ (Subgroup.mem_inf.mp (hB hb)).1 (hBe b hb)⟩) hBG1 hB2
  have hSx : ∀ b : ↥c.G1, (b : G) ∈ centralizer ({r.tE} : Set G) →
      (r.elemOf (M24G.setClass {0, 2}))⁻¹ *
        ((b : G) * r.elemOf (M24G.setClass {0, 2}) * (b : G)⁻¹) ∈ zpowers r.tE →
      r.φ b ∈ M24G.stabS1 := by
    intro b hbC hb
    have h01 := r.phi_smul01 b hbC
    have hcard : (r.φ b • ({0, 2} : Finset (Fin 24))).card = 2 := by
      rw [Finset.card_smul_finset]
      decide
    have h02 : r.φ b • ({0, 2} : Finset (Fin 24)) = {0, 2} ∨
        r.φ b • ({0, 2} : Finset (Fin 24)) = {1, 2} := by
      rcases r.rho_todd_of_mem_zpowers b hx hb with h | h
      · rw [r.todd_elemOf, ← M24G.setClass_smul (r.toResM24.φ_mem b) (by decide)] at h
        exact Or.inl (M24G.setClass_injOn_duads hcard (by decide) h)
      · rw [r.todd_elemOf, ← M24G.setClass_smul (r.toResM24.φ_mem b) (by decide),
          mul_comm (M24G.setClass {0, 2}), setClass01_mul 2 (by decide) (by decide)] at h
        exact Or.inr (M24G.setClass_injOn_duads hcard (by decide) h)
    obtain ⟨h2, h01'⟩ := fix_two_of_smul h01 h02
    exact M24G.mem_stabS1.mpr ⟨r.toResM24.φ_mem b, h2, h01'⟩
  have hSf : ∀ b : ↥c.G1, (b : G) ∈ centralizer ({r.tE} : Set G) →
      (r.elemOf M24G.f770)⁻¹ * ((b : G) * r.elemOf M24G.f770 * (b : G)⁻¹) ∈ zpowers r.tE →
      r.φ b ∈ M24G.stabS2 := by
    intro b hbC hb
    have h := r.rho_todd_of_mem_zpowers b hf hb
    rw [r.todd_elemOf] at h
    exact M24G.mem_stabS2.mpr ⟨r.toResM24.φ_mem b, r.phi_smul01 b hbC, h⟩
  have hk : (Nat.card ↥(zpowers r.tE) * 2 ^ 4) ^ 2 <
      Nat.card c.E * Nat.card ↥(zpowers r.tE) := by
    rw [r.card_zpowers_tE, c.card_E]
    norm_num
  have hfusx := CFSG.GroupTheory.TIFusion.fusion_of_rank (centralizer ({r.tE} : Set G)) c.E
    (zpowers r.tE) hEX hNE hNX hE2 hEc hTI hx hxN 4
    (hrank M24G.stabS1 M24G.card_le_sixteen_stabS1 _ hx hSx) hk
  have hfusf := CFSG.GroupTheory.TIFusion.fusion_of_rank (centralizer ({r.tE} : Set G)) c.E
    (zpowers r.tE) hEX hNE hNX hE2 hEc hTI hf hfN 4
    (hrank M24G.stabS2 M24G.card_le_sixteen_stabS2 _ hf hSf) hk
  have hsat : ∀ n ∈ zpowers r.tE, ∃ y ∈ centralizer ({r.tE} : Set G) ⊓ normalizer (c.E : Set G),
      y * r.elemOf (M24G.setClass {0, 2}) * y⁻¹ = r.elemOf (M24G.setClass {0, 2}) * n := by
    intro n hn
    rcases (r.mem_zpowers_tE).mp hn with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, by group⟩
    obtain ⟨σ, hσS, hσ0⟩ := M24G.exists_swap01
    obtain ⟨hσ, hσ2, -⟩ := M24G.mem_stabS1.mp hσS
    obtain ⟨y, hy⟩ := r.toResM24.exists_φ_eq hσ
    have hyS : r.φ y ∈ M24G.stabS1 := by rw [show r.φ y = σ from hy]; exact hσS
    refine ⟨y, Subgroup.mem_inf.mpr ⟨r.mem_centralizer_tE_of y (smul01_of_mem_stabS1 hyS), y.2⟩,
      ?_⟩
    apply r.eq_of_todd_eq (c.conj_mem_E y hx) (c.E.mul_mem hx r.tE_mem)
    have hmul : r.todd ⟨r.elemOf (M24G.setClass {0, 2}) * r.tE, c.E.mul_mem hx r.tE_mem⟩ =
        r.todd ⟨r.elemOf (M24G.setClass {0, 2}), hx⟩ * r.todd ⟨r.tE, r.tE_mem⟩ := by
      rw [← map_mul]
      rfl
    rw [hmul, todd_conj r y hx, r.todd_elemOf, r.todd_tE,
      ← M24G.setClass_smul (r.toResM24.φ_mem y) (by decide), perm_smul_pair,
      show r.φ y = σ from hy, hσ0, hσ2, mul_comm (M24G.setClass {0, 2}),
      setClass01_mul 2 (by decide) (by decide)]
  have hdist : ∀ y ∈ centralizer ({r.tE} : Set G) ⊓ normalizer (c.E : Set G),
      y * r.elemOf (M24G.setClass {0, 2}) * y⁻¹ ≠ r.elemOf M24G.f770 := by
    intro y hy heq
    have hyG1 : y ∈ c.G1 := (Subgroup.mem_inf.mp hy).2
    have h1 := todd_conj r ⟨y, hyG1⟩ hx
    rw [r.todd_elemOf, ← M24G.setClass_smul (r.toResM24.φ_mem _) (by decide)] at h1
    have heq' : r.todd ⟨y * r.elemOf (M24G.setClass {0, 2}) * y⁻¹, c.conj_mem_E ⟨y, hyG1⟩ hx⟩ =
        M24G.f770 := by
      rw [← r.todd_elemOf M24G.f770]
      exact congrArg r.todd (Subtype.ext heq)
    rw [heq'] at h1
    have hcard : (r.φ ⟨y, hyG1⟩ • ({0, 2} : Finset (Fin 24))).card = 2 := by
      rw [Finset.card_smul_finset]
      decide
    exact M24G.not_isSextClass_of_isDuadClass ⟨_, hcard, h1.symm⟩ M24G.isSextClass_f770
  exact CFSG.GroupTheory.TIFusion.le_normalizer_of_ti _ c.E _ hEX hNE hNX hE2 hEc hTI hx hxN hf
    hfN hfusx hfusf hsat hdist

end ResM24T

theorem stmt6_3_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c))
    (hI : Sec7Inputs) (hmax : Stmt5_Max13) (h2c : Stmt5_2c) (hN : NormalTwoSextet) :
    Stmt6_3 := by
  intro G _ _ z hJ c
  obtain ⟨r⟩ := hres G z hJ c
  have hC := r.centralizer_tE_le hI hJ hmax h2c hN
  refine ⟨r.tE, r.tE_mem, r.tE_ne_one, ?_, fun e he he1 => r.exists_conj_z_or_tE he he1, ?_,
    le_antisymm (le_inf hC le_rfl) inf_le_right⟩
  · rintro ⟨m, -, hm⟩
    exact r.not_isConj_tE_z (isConj_iff.mpr ⟨m, hm⟩).symm
  · intro g hg
    obtain ⟨t', ht'E, ht'⟩ := Subgroup.mem_map.mp hg
    have ht'' : g * t' * g⁻¹ = r.tE := ht'
    have ht'1 : t' ≠ 1 := by
      rintro rfl
      apply r.tE_ne_one
      rw [← ht'', mul_one, mul_inv_cancel]
    rcases r.exists_conj_z_or_tE ht'E ht'1 with ⟨m, -, hmz⟩ | ⟨m, hm, hmt⟩
    · exfalso
      apply r.not_isConj_tE_z
      refine (isConj_iff.mpr ⟨g * m, ?_⟩).symm
      rw [← ht'', ← hmz]
      group
    · have hgm : g * m ∈ centralizer ({r.tE} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : g * m * r.tE * (g * m)⁻¹ = r.tE := by
          calc g * m * r.tE * (g * m)⁻¹ = g * (m * r.tE * m⁻¹) * g⁻¹ := by group
            _ = r.tE := by rw [hmt, ht'']
        calc g * m * r.tE = g * m * r.tE * (g * m)⁻¹ * (g * m) := by group
          _ = r.tE * (g * m) := by rw [h1]
      have hgG1 : g ∈ c.G1 := by
        have := c.G1.mul_mem (hC hgm) (c.G1.inv_mem hm)
        rwa [mul_inv_cancel_right] at this
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgG1

theorem stmt6_3_holds :
    Stmt6_3 :=
  stmt6_3_of resM24T_holds sec7Inputs_holds_uncond stmt5_max13_holds stmt5_2c_holds
    fun hU N hNM hN2 hNU hnorm => M24G.normal_two_subgroup_of_sextet hU N hNM hN2 hNU hnorm

end CFSG.Quasithin.H13.AS91
