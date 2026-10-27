module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3FrameSDecomp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3Torus
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G}

private theorem frame_conj_V_eq {c : Ctx2311 D Ch} (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup c.V (x i : G) = c.V := by
  refine conjSubgroup_eq_iff_mem_normalizer.mpr ?_
  exact Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L (Subgroup.mem_sup_left (x i).2)

private theorem frame_Ki_le_L {c : Ctx2311 D Ch} (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup c.K (x i) ≤ c.L := by
  rintro y ⟨k, hk, rfl⟩
  exact c.L.mul_mem (c.L.mul_mem (c.L.inv_mem (x i).2) (c.K_le_L hk))
    (c.L.inv_mem (c.L.inv_mem (x i).2))

private theorem frame_E_le_L {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (i : Fin 3) : frameE x i ≤ c.L :=
  (SL3Facts.frame_E_le_K F x i).trans (frame_Ki_le_L x i)

private def sectionTrivial {G : Type*} [Group G] (A V : Subgroup G) : Subgroup G where
  carrier := {g : G | g ∈ Subgroup.normalizer (V : Set G) ∧
    ∀ x ∈ A, g * x * g⁻¹ * x⁻¹ ∈ V}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, fun x _ => ?_⟩
    simpa using V.one_mem
  mul_mem' := by
    rintro g h ⟨hgV, hg⟩ ⟨hhV, hh⟩
    refine ⟨Subgroup.mul_mem _ hgV hhV, fun x hx => ?_⟩
    have hsplit : (g * h) * x * (g * h)⁻¹ * x⁻¹ =
        (g * (h * x * h⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    rw [hsplit]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hgV _).mp (hh x hx)) (hg x hx)
  inv_mem' := by
    rintro g ⟨hgV, hg⟩
    refine ⟨Subgroup.inv_mem _ hgV, fun x hx => ?_⟩
    simp only [inv_inv]
    have h : g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g ∈ V := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) _).mp (V.inv_mem (hg x hx))
    have heq : g⁻¹ * x * g * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g := by group
    rw [heq]
    exact h

private theorem mem_sectionTrivial {A V : Subgroup G} {g : G} :
    g ∈ sectionTrivial A V ↔ g ∈ Subgroup.normalizer (V : Set G) ∧
      ∀ x ∈ A, g * x * g⁻¹ * x⁻¹ ∈ V :=
  Iff.rfl

private theorem commutator_mem_iff_mul_left {G : Type*} [Group G] {A V : Subgroup G} {p k x : G}
    (hpV : p ∈ Subgroup.normalizer (V : Set G))
    (hp : ∀ y ∈ A, p * y * p⁻¹ * y⁻¹ ∈ V) (hx : x ∈ A) :
    (p * k) * x * (p * k)⁻¹ * x⁻¹ ∈ V ↔ k * x * k⁻¹ * x⁻¹ ∈ V := by
  have hsplit : (p * k) * x * (p * k)⁻¹ * x⁻¹ =
      (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * (p * x * p⁻¹ * x⁻¹) := by group
  rw [hsplit]
  constructor
  · intro h
    have h1 : p * (k * x * k⁻¹ * x⁻¹) * p⁻¹ ∈ V := by
      have := V.mul_mem h (V.inv_mem (hp x hx))
      simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp hpV (k * x * k⁻¹ * x⁻¹)).mpr h1
  · intro h
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hpV (k * x * k⁻¹ * x⁻¹)).mp h) (hp x hx)

private theorem commutator_mem_iff_mul_right {G : Type*} [Group G] {A V : Subgroup G} {p k x : G}
    (hp : ∀ y ∈ A, p * y * p⁻¹ * y⁻¹ ∈ V) (hkV : k ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ A) :
    (k * p) * x * (k * p)⁻¹ * x⁻¹ ∈ V ↔ k * x * k⁻¹ * x⁻¹ ∈ V := by
  have hsplit : (k * p) * x * (k * p)⁻¹ * x⁻¹ =
      (k * (p * x * p⁻¹ * x⁻¹) * k⁻¹) * (k * x * k⁻¹ * x⁻¹) := by group
  rw [hsplit]
  constructor
  · intro h
    have hu : k * (p * x * p⁻¹ * x⁻¹) * k⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hkV _).mp (hp x hx)
    have := V.mul_mem (V.inv_mem hu) h
    simpa [mul_assoc] using this
  · intro h
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hkV _).mp (hp x hx)) h

private theorem frameInter_le_pCoreOf {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    {i j : Fin 3} (hij : i ≠ j) : frameE x i ⊓ frameE x j ≤ frameS c := by
  intro t ht
  have htL : t ∈ c.L := frame_E_le_L F x i ht.1
  have hmem : c.phiL F.hV ⟨t, htL⟩ ∈
      (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ⊓
        (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom := by
    refine ⟨?_, ?_⟩
    · rw [← SL3Facts.frame_map_E_eq F x i]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht.1)
    · rw [← SL3Facts.frame_map_E_eq F x j]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht.2)
  rw [hx.2.2.1 i j hij] at hmem
  have hφ : c.phiL F.hV ⟨t, htL⟩ = 1 := by simpa using hmem
  have hker : (⟨t, htL⟩ : ↥c.L) ∈ CFSG.pCore 2 ↥c.L := by
    rw [← F.hker]
    exact MonoidHom.mem_ker.mpr hφ
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := c.L) ⟨t, htL⟩).mpr hker

private theorem frame_inf_pCoreOf_le {c : Ctx2311 D Ch} (x : Fin 3 → ↥c.L) (i : Fin 3) :
    conjSubgroup c.K (x i) ⊓ frameS c ≤ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ g ∈ conjSubgroup c.K (x i),
      ∀ y ∈ conjSubgroup c.K (x i) ⊓ frameS c,
        g * y * g⁻¹ ∈ conjSubgroup c.K (x i) ⊓ frameS c := by
    rintro g hg y ⟨hyK, hyS⟩
    have hgL : g ∈ c.L := frame_Ki_le_L x i hg
    have hgy : g * y * g⁻¹ ∈ conjSubgroup c.K (x i) :=
      (conjSubgroup c.K (x i)).mul_mem
        ((conjSubgroup c.K (x i)).mul_mem hg hyK) (Subgroup.inv_mem _ hg)
    exact ⟨hgy,
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L hgL) y).mp hyS⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => hnorm g hg y hy, fun hy => by
      have h2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      have := hnorm g⁻¹ ((conjSubgroup c.K (x i)).inv_mem hg) (g * y * g⁻¹) hy
      simpa [h2] using this⟩
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le inf_le_right

private theorem frame_sup_trivial {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i j : Fin 3) :
    ∀ z ∈ frameE x i ⊔ frameE x j, ∀ t ∈ frameE x i ⊓ frameE x j,
      z * t * z⁻¹ * t⁻¹ ∈ c.V := by
  have hZV : ∀ p : Fin 3, conjSubgroup D.Z (x p) ≤ c.V := fun p =>
    (SL3Facts.frame_Z_le_V x p).trans (le_of_eq (frame_conj_V_eq x p))
  have hsupL : frameE x i ⊔ frameE x j ≤ c.L :=
    sup_le (frame_E_le_L F x i) (frame_E_le_L F x j)
  have hnormV : ∀ z ∈ frameE x i ⊔ frameE x j, z ∈ Subgroup.normalizer (c.V : Set G) :=
    fun z hz => Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L
      (Subgroup.mem_sup_left (hsupL hz))
  have hEi : frameE x i ≤ sectionTrivial (frameE x i ⊓ frameE x j) c.V := by
    intro z hz
    refine mem_sectionTrivial.mpr ⟨hnormV z (Subgroup.mem_sup_left hz), fun t ht => ?_⟩
    exact hZV i (SL3Facts.frame_commutator_le F x i
      (Subgroup.commutator_mem_commutator hz ht.1))
  have hEj : frameE x j ≤ sectionTrivial (frameE x i ⊓ frameE x j) c.V := by
    intro z hz
    refine mem_sectionTrivial.mpr ⟨hnormV z (Subgroup.mem_sup_right hz), fun t ht => ?_⟩
    exact hZV j (SL3Facts.frame_commutator_le F x j
      (Subgroup.commutator_mem_commutator hz ht.2))
  intro z hz t ht
  exact (mem_sectionTrivial.mp (sup_le hEi hEj hz)).2 t ht

private theorem frame_lift_y {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (i j : Fin 3) {y : ↥(c.H F.hV)}
    (hy : y ∈ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ⊔
        (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom) :
    ∃ yhat : ↥c.L, c.phiL F.hV yhat = y ∧ (yhat : G) ∈ frameE x i ⊔ frameE x j := by
  have hmap : (CFSG.Open.pCoreOf 2 (frameKStar F)).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ⊔
      (CFSG.Open.pCoreOf 2 (frameKStar F)).map
        (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom =
      ((frameE x i ⊔ frameE x j).subgroupOf c.L).map (c.phiL F.hV) := by
    rw [← SL3Facts.frame_map_E_eq F x i, ← SL3Facts.frame_map_E_eq F x j,
      ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup (frame_E_le_L F x i) (frame_E_le_L F x j)]
  obtain ⟨yhat, hyhat, hφ⟩ := Subgroup.mem_map.mp (hmap ▸ hy)
  exact ⟨yhat, hφ, Subgroup.mem_subgroupOf.mp hyhat⟩

private theorem frame_lift_kappa {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (i : Fin 3) {κ : ↥(c.H F.hV)}
    (hκ : κ ∈ (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom) :
    ∃ khat : ↥c.L, c.phiL F.hV khat = κ ∧ (khat : G) ∈ conjSubgroup c.K (x i) := by
  obtain ⟨k, hk, hkκ⟩ := Subgroup.mem_map.mp hκ
  obtain ⟨k0, hk0, hk0φ⟩ := Subgroup.mem_map.mp hk
  have hmemL : (x i : G)⁻¹ * (k0 : G) * (x i : G) ∈ c.L :=
    c.L.mul_mem (c.L.mul_mem (c.L.inv_mem (x i).2) k0.2) (x i).2
  refine ⟨⟨(x i : G)⁻¹ * (k0 : G) * (x i : G), hmemL⟩, ?_, ?_⟩
  · have h1 : c.phiL F.hV ⟨(x i : G)⁻¹ * (k0 : G) * (x i : G), hmemL⟩ =
        (MulAut.conj (c.phiL F.hV (x i))⁻¹) (c.phiL F.hV k0) := by
      rw [show (⟨(x i : G)⁻¹ * (k0 : G) * (x i : G), hmemL⟩ : ↥c.L) =
          (x i)⁻¹ * k0 * x i from Subtype.ext rfl, map_mul, map_mul, map_inv,
        MulAut.conj_apply]
      group
    rw [h1, hk0φ]
    exact hkκ
  · rw [mem_conjSubgroup_iff]
    have heq : (x i : G) * ((x i : G)⁻¹ * (k0 : G) * (x i : G)) * (x i : G)⁻¹ =
        (k0 : G) := by group
    rw [heq]
    exact Subgroup.mem_subgroupOf.mp hk0

private theorem frame_kappa_pow {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (i : Fin 3) {κ : ↥(c.H F.hV)} {khat : ↥c.L} (hφ : c.phiL F.hV khat = κ) {r : ℕ}
    (hκr : κ ^ r = 1) (hkK : (khat : G) ∈ conjSubgroup c.K (x i)) :
    (khat : G) ^ r ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i)) := by
  have hmem : (khat ^ r : ↥c.L) ∈ (c.phiL F.hV).ker := by
    rw [MonoidHom.mem_ker, map_pow, hφ, hκr]
  rw [F.hker] at hmem
  have hS : ((khat ^ r : ↥c.L) : G) ∈ frameS c :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := c.L) (khat ^ r)).mpr hmem
  refine frame_inf_pCoreOf_le x i ⟨?_, hS⟩
  simpa using (conjSubgroup c.K (x i)).pow_mem hkK r

private theorem frame_kappa_notMem_pCoreOf {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (x : Fin 3 → ↥c.L) (i : Fin 3) {κ : ↥(c.H F.hV)} {khat : ↥c.L}
    (hφ : c.phiL F.hV khat = κ)
    (hκU : κ ∉ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom) :
    (khat : G) ∉ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i)) := by
  intro hmem
  have hKiO2 : CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i)) =
      (CFSG.Open.pCoreOf 2 c.K).map (MulAut.conj (x i : G)⁻¹).toMonoidHom := by
    rw [conjSubgroup, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  rw [hKiO2] at hmem
  obtain ⟨k, hk, hkκ⟩ := Subgroup.mem_map.mp hmem
  have hk0 : k = (x i : G) * (khat : G) * (x i : G)⁻¹ := by
    have h1 : (x i : G)⁻¹ * k * (x i : G) = (khat : G) := by
      simpa [MulAut.conj_apply] using hkκ
    rw [← h1]
    group
  have hkK : k ∈ c.K := CFSG.LieType.BorelTits.pCoreOf_le 2 c.K hk
  have hkL : k ∈ c.L := c.K_le_L hkK
  have hκ0 : c.phiL F.hV ⟨k, hkL⟩ ∈ CFSG.Open.pCoreOf 2 (frameKStar F) :=
    phiL_mem_pCoreOf (c := c) (hV := F.hV) (x := ⟨k, hkL⟩) hk
  have hκeq : (MulAut.conj (c.phiL F.hV (x i))⁻¹)
      (c.phiL F.hV ⟨k, hkL⟩) = κ := by
    have h1 : (⟨k, hkL⟩ : ↥c.L) = x i * khat * (x i)⁻¹ := Subtype.ext hk0
    have h2 : c.phiL F.hV ⟨k, hkL⟩ =
        c.phiL F.hV (x i) * κ * (c.phiL F.hV (x i))⁻¹ := by
      simp only [h1, map_mul, map_inv, hφ]
    rw [h2, MulAut.conj_apply]
    group
  exact hκU (Subgroup.mem_map.mpr ⟨_, hκ0, hκeq⟩)

private theorem frame_kappa_fpf {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (i : Fin 3) {k : G} (hKi : k ∈ conjSubgroup c.K (x i))
    (hO : k ∉ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i)))
    {r : ℕ} (hr : Odd r) (hpow : k ^ r ∈ CFSG.Open.pCoreOf 2 (conjSubgroup c.K (x i)))
    (hM : k ∈ conjSubgroup D.M (x i))
    (hNE : k ∈ Subgroup.normalizer (frameE x i : Set G))
    (hV : k ∈ Subgroup.normalizer (c.V : Set G)) :
    ∀ t ∈ frameE x i, k * t * k⁻¹ * t⁻¹ ∈ c.V → t ∈ c.V := by
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by rw [F.normalizer_Z_eq]
  have hZi : k ∈ Subgroup.normalizer (conjSubgroup D.Z (x i) : Set G) := by
    have hNZ : conjSubgroup (Subgroup.normalizer (D.Z : Set G)) (x i) =
        Subgroup.normalizer (conjSubgroup D.Z (x i) : Set G) := by
      change (Subgroup.normalizer (D.Z : Set G)).map
          (MulAut.conj (x i : G)⁻¹).toMonoidHom =
        Subgroup.normalizer (D.Z.map (MulAut.conj (x i : G)⁻¹).toMonoidHom : Set G)
      exact Subgroup.map_normalizer_eq_of_bijective _
        (MulAut.conj (x i : G)⁻¹).bijective
    rw [← hNZ]
    exact mem_conjSubgroup_iff.mpr (hMZ (mem_conjSubgroup_iff.mp hM))
  have hZV : conjSubgroup D.Z (x i) ≤ c.V :=
    (SL3Facts.frame_Z_le_V x i).trans (le_of_eq (frame_conj_V_eq x i))
  have hVE : c.V ≤ frameE x i := by
    rw [← frame_conj_V_eq x i]
    exact SL3Facts.frame_V_le_E x i
  have hfree : ∀ t ∈ frameE x i, k * t * k⁻¹ * t⁻¹ ∈ conjSubgroup D.Z (x i) →
      t ∈ conjSubgroup D.Z (x i) := fun t ht h =>
    SL3Facts.frame_mem_Z_of_commutator_mem F x i hKi hO hr hpow ht h
  refine CFSG.mem_of_conj_mem_of_section (SL3Facts.frame_commutator_le F x i) hZV hVE
    le_rfl ?_ hfree
  intro X hX
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl | rfl
  exacts [hNE, hZi, hV, hNE]

private theorem frame_pair_reduce {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    {d : G} {i j : Fin 3}
    {yhat khat s : ↥c.L}
    (hyE : (yhat : G) ∈ frameE x i ⊔ frameE x j)
    (hkV : (khat : G) ∈ Subgroup.normalizer (c.V : Set G))
    (hd_eq : d = (yhat : G) * (khat : G) * (s : G))
    (hsP : ∀ t ∈ frameE x i ⊓ frameE x j, (s : G) * t * (s : G)⁻¹ * t⁻¹ ∈ c.V)
    (hfpf : ∀ t ∈ frameE x i, (khat : G) * t * (khat : G)⁻¹ * t⁻¹ ∈ c.V → t ∈ c.V)
    {t : G} (ht : t ∈ frameE x i ⊓ frameE x j) (hcomm : d * t * d⁻¹ * t⁻¹ ∈ c.V) :
    t ∈ c.V := by
  have h1 : ((yhat : G) * ((khat : G) * (s : G))) * t *
      ((yhat : G) * ((khat : G) * (s : G)))⁻¹ * t⁻¹ ∈ c.V := by
    simpa only [hd_eq, mul_assoc] using hcomm
  have hsupL : frameE x i ⊔ frameE x j ≤ c.L :=
    sup_le (frame_E_le_L F x i) (frame_E_le_L F x j)
  have hyV : (yhat : G) ∈ Subgroup.normalizer (c.V : Set G) :=
    Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L (Subgroup.mem_sup_left (hsupL hyE))
  have h2 : ((khat : G) * (s : G)) * t * ((khat : G) * (s : G))⁻¹ * t⁻¹ ∈ c.V :=
    (commutator_mem_iff_mul_left (A := frameE x i ⊓ frameE x j) (V := c.V)
      (p := (yhat : G)) (k := (khat : G) * (s : G)) (x := t) hyV
      (frame_sup_trivial F x i j (yhat : G) hyE) ht).mp h1
  have h3 : (khat : G) * t * (khat : G)⁻¹ * t⁻¹ ∈ c.V :=
    (commutator_mem_iff_mul_right (A := frameE x i ⊓ frameE x j) (V := c.V)
      (p := (s : G)) (k := (khat : G)) (x := t) hsP hkV ht).mp h2
  exact hfpf t ht.1 h3

private theorem frame_pair_fpf {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    {d : G} (hdL : d ∈ c.L) {i j : Fin 3} (hij : i ≠ j)
    {y κ : ↥(c.H F.hV)}
    (hy : y ∈ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ⊔
        (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom)
    (hκK : κ ∈ (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom)
    (hκU : κ ∉ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom)
    (hκodd : ∃ r : ℕ, Odd r ∧ κ ^ r = 1)
    (hφd : c.phiL F.hV ⟨d, hdL⟩ = y * κ)
    (hScomm : ⁅frameS c, frameS c⁆ ≤ c.V)
    (hNE : ∀ (l : ↥c.L), c.phiL F.hV l ∈ (frameKStar F).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom →
      (l : G) ∈ conjSubgroup D.M (x i) ∧
        (l : G) ∈ Subgroup.normalizer (frameE x i : Set G)) :
    ∀ t ∈ frameE x i ⊓ frameE x j, d * t * d⁻¹ * t⁻¹ ∈ c.V → t ∈ c.V := by
  obtain ⟨yhat, hφyhat, hyE⟩ := frame_lift_y F x i j hy
  obtain ⟨khat, hφkhat, hkK⟩ := frame_lift_kappa F x i hκK
  obtain ⟨r, hr, hκr⟩ := hκodd
  have hκK' : c.phiL F.hV khat ∈ (frameKStar F).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom := by
    rwa [hφkhat]
  have hkM := hNE khat hκK'
  have hpow := frame_kappa_pow F x i hφkhat hκr hkK
  have hkO := frame_kappa_notMem_pCoreOf F x i hφkhat hκU
  have hkV : (khat : G) ∈ Subgroup.normalizer (c.V : Set G) :=
    Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L (Subgroup.mem_sup_left khat.2)
  have hfpf := frame_kappa_fpf F x i hkK hkO hr hpow hkM.1 hkM.2 hkV
  let s : ↥c.L := (yhat * khat)⁻¹ * ⟨d, hdL⟩
  have hφs : c.phiL F.hV s = 1 := by
    have h1 : c.phiL F.hV s =
        (c.phiL F.hV yhat * c.phiL F.hV khat)⁻¹ * c.phiL F.hV ⟨d, hdL⟩ := by
      simp only [s, map_mul, map_inv]
    rw [h1, hφyhat, hφkhat, hφd]
    group
  have hsS : (s : G) ∈ frameS c := by
    have hmem : s ∈ CFSG.pCore 2 ↥c.L := by
      rw [← F.hker]
      exact MonoidHom.mem_ker.mpr hφs
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := c.L) s).mpr hmem
  have hd_eq : d = (yhat : G) * (khat : G) * (s : G) := by
    have h1 : (⟨d, hdL⟩ : ↥c.L) = (yhat * khat) * s := by
      simp only [s]
      group
    simpa using congrArg Subtype.val h1
  have hsP : ∀ t ∈ frameE x i ⊓ frameE x j, (s : G) * t * (s : G)⁻¹ * t⁻¹ ∈ c.V := by
    intro t ht
    exact hScomm (Subgroup.commutator_mem_commutator hsS (frameInter_le_pCoreOf F x hx hij ht))
  intro t ht hcomm
  exact frame_pair_reduce F x hyE hkV hd_eq hsP hfpf ht hcomm

private theorem frame_fpf_all {c : Ctx2311 D Ch} (F : c.SL3Facts) (x : Fin 3 → ↥c.L)
    (hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)))
    (hScomm : ⁅frameS c, frameS c⁆ ≤ c.V)
    {d : G} (hdL : d ∈ c.L)
    (hdNE : ∀ i : Fin 3, d ∈ Subgroup.normalizer (frameE x i : Set G))
    (hdec : ∀ (i j : Fin 3), i ≠ j → ∃ y κ : ↥(c.H F.hV),
      y ∈ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ⊔
        (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom ∧
      κ ∈ (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ∧
      κ ∉ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ∧
      (∃ r : ℕ, Odd r ∧ κ ^ r = 1) ∧
      c.phiL F.hV ⟨d, hdL⟩ = y * κ)
    (hNE : ∀ (i : Fin 3) (l : ↥c.L), c.phiL F.hV l ∈ (frameKStar F).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom →
      (l : G) ∈ conjSubgroup D.M (x i) ∧
        (l : G) ∈ Subgroup.normalizer (frameE x i : Set G)) :
    ∀ t ∈ frameS c, d * t * d⁻¹ * t⁻¹ ∈ c.V → t ∈ c.V := by
  have hSsup := (F.pCoreOf_eq_sup_inter x hx).1
  have hmemV : c.V ≤ frameE x 0 ⊓ frameE x 1 := by
    refine le_inf ?_ ?_
    · rw [← frame_conj_V_eq x 0]
      exact SL3Facts.frame_V_le_E x 0
    · rw [← frame_conj_V_eq x 1]
      exact SL3Facts.frame_V_le_E x 1
  have hVB : c.V ≤ frameS c := by
    change c.V ≤ CFSG.Open.pCoreOf 2 c.L
    rw [hSsup]
    exact le_sup_of_le_left (le_sup_of_le_left hmemV)
  let T : Fin 3 → Subgroup G :=
    ![frameE x 0 ⊓ frameE x 1, frameE x 0 ⊓ frameE x 2, frameE x 1 ⊓ frameE x 2]
  have hB : frameS c = ⨆ A ∈ Set.range T, A := by
    rw [iSup_range]
    refine hSsup.trans ?_
    simp [T, CFSG.Quasithin.iSup_fin_three]
  have hdV : d ∈ Subgroup.normalizer (c.V : Set G) :=
    Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L (Subgroup.mem_sup_left hdL)
  have hdS : ∀ A ∈ Set.range T, d ∈ Subgroup.normalizer (A : Set G) := by
    rintro A ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hdNE 0, hdNE 1⟩
    · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hdNE 0, hdNE 2⟩
    · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hdNE 1, hdNE 2⟩
  have hfree : ∀ A ∈ Set.range T, ∀ t ∈ A, d * t * d⁻¹ * t⁻¹ ∈ c.V → t ∈ c.V := by
    rintro A ⟨i, rfl⟩
    fin_cases i
    · obtain ⟨y, κ, hy, hκK, hκU, hκodd, hφd⟩ := hdec 0 1 (by decide)
      exact frame_pair_fpf F x hx hdL (by decide) hy hκK hκU hκodd hφd hScomm (hNE 0)
    · obtain ⟨y, κ, hy, hκK, hκU, hκodd, hφd⟩ := hdec 0 2 (by decide)
      exact frame_pair_fpf F x hx hdL (by decide) hy hκK hκU hκodd hφd hScomm (hNE 0)
    · obtain ⟨y, κ, hy, hκK, hκU, hκodd, hφd⟩ := hdec 1 2 (by decide)
      exact frame_pair_fpf F x hx hdL (by decide) hy hκK hκU hκodd hφd hScomm (hNE 1)
  exact CFSG.mem_of_conj_mem_of_iSup hB hScomm hVB hdV hdS hfree

private theorem frame_adapted {c : Ctx2311 D Ch} (F : c.SL3Facts) {d : G} (hdL : d ∈ c.L)
    (hdodd : Odd (orderOf d)) (hd3 : d ^ 3 ≠ 1)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    ∃ a : Fin 3 → ↥(c.H F.hV), IsSL3Frame (frameKStar F) a ∧
      (∀ i, c.phiL F.hV ⟨d, hdL⟩ ∈ (MulAction.stabilizer ↥(c.H F.hV)
        ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) : Set (c.toCtx23L.W F.hV))).map
          (MulAut.conj (a i)⁻¹).toMonoidHom) ∧
      (∀ (i j : Fin 3), i ≠ j → ∃ y κ : ↥(c.H F.hV),
        y ∈ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
            (MulAut.conj (a i)⁻¹).toMonoidHom ⊔
          (CFSG.Open.pCoreOf 2 (frameKStar F)).map (MulAut.conj (a j)⁻¹).toMonoidHom ∧
        κ ∈ (frameKStar F).map (MulAut.conj (a i)⁻¹).toMonoidHom ∧
        c.phiL F.hV ⟨d, hdL⟩ = y * κ ∧
        κ ∉ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
          (MulAut.conj (a i)⁻¹).toMonoidHom ∧
        ∃ r : ℕ, Odd r ∧ κ ^ r = 1) ∧
      Hinf (MulAction.stabilizer ↥(c.H F.hV)
        ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
          Set (c.toCtx23L.W F.hV))) = frameKStar F := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom _ (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom _ (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom _ ((c.H F.hV).subtype.comp
      (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom _ ((c.H F.hV).subtype.comp
      (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  have hnat : IsNaturalClassicalModule (c.H F.hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F.hSL, F.hnat⟩))))
  have hKstar : Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :
        Subgroup (c.toCtx23L.W F.hV)) : Set (c.toCtx23L.W F.hV))) = frameKStar F :=
    c.toCtx23L.Hinf_stabilizer_sylowStar_eq_map_Hinf F.hV kTab23a_holds F.h4 F.h1930 hnat
  have hℓ : fixedPointSubgroup ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) = c.toCtx23L.Ztil F.hV :=
    c.toCtx23L.fixedPointSubgroup_sylowStar_eq_Ztil F.hV kTab23a_holds hnat F.h4 F.h1930
  rw [hℓ] at hKstar
  obtain ⟨hgodd, hg3⟩ := phiL_odd_cube c hdL hdodd hd3 F.hker
  have hcomm : ∀ k ∈ Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :
        Subgroup (c.toCtx23L.W F.hV)) : Set (c.toCtx23L.W F.hV))),
      c.phiL F.hV ⟨d, hdL⟩ * k * (c.phiL F.hV ⟨d, hdL⟩)⁻¹ * k⁻¹ ∈
        CFSG.Open.pCoreOf 2 (Hinf (MulAction.stabilizer ↥(c.H F.hV)
          ((fixedPointSubgroup ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :
            Subgroup (c.toCtx23L.W F.hV)) : Set (c.toCtx23L.W F.hV)))) := by
    intro k hk
    rw [hℓ, hKstar] at hk ⊢
    exact phiL_commutator_mem_pCoreOf c hdL hdK k hk
  obtain ⟨a, hframe, hPa, hdecomp⟩ :=
    kSL3FrameTorus_holds (c.toCtx23L.W F.hV) (c.H F.hV) (CFSG.Open.pRank 2 D.Z)
      F.hSL F.hnat F.h3 (c.sylowStar F.hV) (c.phiL F.hV ⟨d, hdL⟩) hgodd hg3 hcomm
  rw [hℓ] at hframe hdecomp hPa; rw [hKstar] at hframe hdecomp
  refine ⟨a, hframe, hPa, fun i j hij => ?_, hKstar⟩
  obtain ⟨y, hy, κ, hκ, hg, hκU, r, hr, hκr⟩ := hdecomp i j hij
  exact ⟨y, κ, hy, hκ.1, hg, hκU, r, hr, hκr⟩

private theorem frame_lift_data {c : Ctx2311 D Ch} (F : c.SL3Facts) {d : G} (hdL : d ∈ c.L)
    {a : Fin 3 → ↥(c.H F.hV)} (hframe : IsSL3Frame (frameKStar F) a)
    (hdecomp : ∀ (i j : Fin 3), i ≠ j → ∃ y κ : ↥(c.H F.hV),
      y ∈ (CFSG.Open.pCoreOf 2 (frameKStar F)).map (MulAut.conj (a i)⁻¹).toMonoidHom ⊔
        (CFSG.Open.pCoreOf 2 (frameKStar F)).map (MulAut.conj (a j)⁻¹).toMonoidHom ∧
      κ ∈ (frameKStar F).map (MulAut.conj (a i)⁻¹).toMonoidHom ∧
      c.phiL F.hV ⟨d, hdL⟩ = y * κ ∧
      κ ∉ (CFSG.Open.pCoreOf 2 (frameKStar F)).map (MulAut.conj (a i)⁻¹).toMonoidHom ∧
      ∃ r : ℕ, Odd r ∧ κ ^ r = 1) :
    ∃ x : Fin 3 → ↥c.L, IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)) ∧
      (∀ i, c.phiL F.hV (x i) = a i) ∧
      (∀ (i j : Fin 3), i ≠ j → ∃ y κ : ↥(c.H F.hV),
        y ∈ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
            (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ⊔
          (CFSG.Open.pCoreOf 2 (frameKStar F)).map
            (MulAut.conj (c.phiL F.hV (x j))⁻¹).toMonoidHom ∧
        κ ∈ (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ∧
        κ ∉ (CFSG.Open.pCoreOf 2 (frameKStar F)).map
            (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ∧
        (∃ r : ℕ, Odd r ∧ κ ^ r = 1) ∧
        c.phiL F.hV ⟨d, hdL⟩ = y * κ) := by
  classical
  have ha0 : a 0 = 1 := hframe.1
  choose xx hxx using fun i => c.phiL_surjective F.hV (a i)
  let x : Fin 3 → ↥c.L := fun i => if i = 0 then 1 else xx i
  have hxφ : ∀ i, c.phiL F.hV (x i) = a i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa [x, ha0]
    · simp only [x, if_neg hi, hxx]
  have hx : IsSL3Frame (frameKStar F) (fun i => c.phiL F.hV (x i)) := by
    rw [show (fun i => c.phiL F.hV (x i)) = a from funext hxφ]
    exact hframe
  refine ⟨x, hx, hxφ, fun i j hij => ?_⟩
  obtain ⟨y, κ, hy, hκK, hg, hκU, hκodd⟩ := hdecomp i j hij
  refine ⟨y, κ, ?_, ?_, ?_, hκodd, hg⟩
  · rw [hxφ i, hxφ j]
    exact hy
  · rw [hxφ i]
    exact hκK
  · rw [hxφ i]
    exact hκU

private theorem frame_point_stab {c : Ctx2311 D Ch} (F : c.SL3Facts) {d : G} (hdL : d ∈ c.L)
    {a : Fin 3 → ↥(c.H F.hV)} {x : Fin 3 → ↥c.L} (hxφ : ∀ i, c.phiL F.hV (x i) = a i)
    (hPa : ∀ i, c.phiL F.hV ⟨d, hdL⟩ ∈ (MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) : Set (c.toCtx23L.W F.hV))).map
        (MulAut.conj (a i)⁻¹).toMonoidHom)
    (hKstar : Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))) = frameKStar F) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    (∀ i : Fin 3, d ∈ Subgroup.normalizer (frameE x i : Set G)) ∧
      (∀ (i : Fin 3) (l : ↥c.L), c.phiL F.hV l ∈ (frameKStar F).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom →
        (l : G) ∈ conjSubgroup D.M (x i) ∧
          (l : G) ∈ Subgroup.normalizer (frameE x i : Set G)) := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom _ (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom _ (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  have hPa' : ∀ i, c.phiL F.hV ⟨d, hdL⟩ ∈ (MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) : Set (c.toCtx23L.W F.hV))).map
        (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom := by
    intro i
    rw [hxφ i]
    exact hPa i
  have hNE : ∀ (i : Fin 3) (l : ↥c.L), c.phiL F.hV l ∈ (frameKStar F).map
      (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom →
      (l : G) ∈ conjSubgroup D.M (x i) ∧
        (l : G) ∈ Subgroup.normalizer (frameE x i : Set G) := by
    intro i l hl
    refine SL3Facts.frame_comap_stabilizer_le F x i ?_
    have hle : (frameKStar F).map (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom ≤
        (MulAction.stabilizer ↥(c.H F.hV)
          ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) : Set (c.toCtx23L.W F.hV))).map
          (MulAut.conj (c.phiL F.hV (x i))⁻¹).toMonoidHom := by
      rw [← hKstar]
      exact Subgroup.map_mono (uc22p21c_Hinf_le _)
    exact hle hl
  exact ⟨fun i => (SL3Facts.frame_comap_stabilizer_le F x i
    (l := ⟨d, hdL⟩) (hPa' i)).2, hNE⟩

private theorem frame_fpf {c : Ctx2311 D Ch} (F : c.SL3Facts) {d : G} (hdL : d ∈ c.L)
    (hdodd : Odd (orderOf d)) (hd3 : d ^ 3 ≠ 1)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    ∀ t ∈ frameS c, d * t * d⁻¹ * t⁻¹ ∈ c.V → t ∈ c.V := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom _ (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom _ (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom _ ((c.H F.hV).subtype.comp
      (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom _ ((c.H F.hV).subtype.comp
      (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  obtain ⟨a, hframe, hPa, hdecomp, hKstar⟩ := frame_adapted F hdL hdodd hd3 hdK
  obtain ⟨x, hx, hxφ, hdec⟩ := frame_lift_data F hdL hframe hdecomp
  obtain ⟨hdNE, hNE⟩ := frame_point_stab F hdL hxφ hPa hKstar
  exact frame_fpf_all F x hx (F.pCoreOf_eq_sup_inter x hx).2.1 hdL hdNE hdec hNE

theorem SL3Facts.pCoreOf_inf_centralizer_eq_bot {c : Ctx2311 D Ch} (F : c.SL3Facts) {d : G}
    (hdL : d ∈ c.L) (hdodd : Odd (orderOf d)) (hd3 : d ^ 3 ≠ 1)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    CFSG.Open.pCoreOf 2 c.L ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  have hjoin := frame_fpf F hdL hdodd hd3 hdK
  have hVfix := (c.fixed_of_centralizes_Kbar F.h1930 F.h4 F.h12 F.hN8 kSL3PointTorus_holds
    F.h3 F.hSL F.hnat F.hker hdL hdodd hd3 hdK).1
  refine le_antisymm ?_ bot_le
  intro t ht
  rw [Subgroup.mem_bot]
  have hdt : d * t * d⁻¹ * t⁻¹ = 1 := by
    have h := (Subgroup.mem_centralizer_iff.mp ht.2) d (Set.mem_singleton d)
    rw [h]
    group
  have htV : t ∈ c.V := hjoin t ht.1 (by rw [hdt]; exact c.V.one_mem)
  have hmem : t ∈ c.V ⊓ Subgroup.centralizer ({d} : Set G) := ⟨htV, ht.2⟩
  rw [hVfix] at hmem
  simpa using hmem

end Ctx2311

theorem s23_17_elt_of_frame (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts)
    (h207 : S20_7 D) (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hline : S23_5_line D Ch) (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch)
    (hN3 : S23_9_NotLarge D Ch) (h12 : S23_12 D Ch) (h14 : S23_14 D Ch) : S23_17_elt D Ch := by
  intro h1930 c d hdL hdodd hd3 hdK
  have F : c.SL3Facts := c.sl3Facts_of h1930 hE h207 h2 h3 h4 hline hN1 hN2 hN3 h12 h14
  obtain ⟨h3m, hV, hSL, hnatSL, hker⟩ :=
    c.sl3Line_of h1930 hE h207 h2 h3 h4 hline kNshape_holds KOrdNat.kOrdNatural_holds
      kSchurL2_holds kSchurSL3_holds hN1 hN2 hN3
  have hN8 : ⁅c.V, c.K⁆ = c.V :=
    c.commutator_V_K_eq_of_sl3 h4 h1930 hV h3m hSL hnatSL kSL3Span_holds
  obtain ⟨-, hESle⟩ :=
    c.fixed_of_centralizes_Kbar h1930 h4 h12 hN8 kSL3PointTorus_holds h3m hSL hnatSL hker
      hdL hdodd hd3 hdK
  have hSC : CFSG.Open.pCoreOf 2 c.L ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ :=
    F.pCoreOf_inf_centralizer_eq_bot hdL hdodd hd3 hdK
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxbot : x ∈ CFSG.Open.pCoreOf 2 c.L ⊓ Subgroup.centralizer ({d} : Set G) :=
    ⟨hESle hx, hx.2⟩
  rw [hSC] at hxbot
  simpa using hxbot

end CFSG.LocalAnalysis.UniquenessCase.UC22
