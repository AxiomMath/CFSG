module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteCard

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.Open
  CFSG.Assembly

theorem eq_inv_of_mem_zpowers {V : Type*} [CommGroup V] {z : V} (hz3 : z ^ 3 = 1) {w : V}
    (hw : w ∈ Subgroup.zpowers z) (hw1 : w ≠ 1) (hwz : w ≠ z) : w = z⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [zpow_eq_zpow_emod' k hz3] at hw1 hwz ⊢
  have : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases this with h | h | h
  · rw [h, zpow_zero] at hw1; exact absurd rfl hw1
  · rw [h, zpow_one] at hwz; exact absurd rfl hwz
  · rw [h, eq_inv_iff_mul_eq_one, zpow_two, ← pow_three']
    exact hz3

theorem map_mem_zpowers {V : Type*} [CommGroup V] {z : V} {φ : MulAut V}
    (hφ : φ z ∈ Subgroup.zpowers z) {t : V} (ht : t ∈ Subgroup.zpowers z) :
    φ t ∈ Subgroup.zpowers z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  rw [map_zpow]
  exact Subgroup.zpow_mem _ hφ k

theorem fix_of_mem_zpowers {V : Type*} [CommGroup V] {z : V} {u : MulAut V} (hu : u z = z)
    {t : V} (ht : t ∈ Subgroup.zpowers z) : u t = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  rw [map_zpow, hu]

theorem inv_of_mem_zpowers {V : Type*} [CommGroup V] {z : V} {φ : MulAut V} (hφ : φ z = z⁻¹)
    {t : V} (ht : t ∈ Subgroup.zpowers z) : φ t = t⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  rw [map_zpow, hφ, inv_zpow]

theorem apply_eq_of_conj {V : Type*} [CommGroup V] {z : V} {ψ φ φ' : MulAut V}
    (h : ψ * φ = φ' * ψ) (hψ : ψ⁻¹ z ∈ Subgroup.zpowers z) (hφ : φ z ∈ Subgroup.zpowers z) :
    φ' z = φ z := by
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hψ
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hφ
  have h1 : φ' z = ψ (φ (ψ⁻¹ z)) := by
    have h2 := congrArg (fun f : MulAut V => f (ψ⁻¹ z)) h
    simp only [MulAut.mul_apply, MulAut.apply_inv_self] at h2
    exact h2.symm
  rw [h1, ← ha, map_zpow, ← hc, ← zpow_mul, mul_comm, zpow_mul, map_zpow, ha,
    MulAut.apply_inv_self]

theorem mul_inv_mem_zpowers_of_refl {V : Type*} [CommGroup V] [Finite V] {z : V} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) {φ : MulAut V} (hφc : Nat.card {b : V // φ b = b} * 3 = Nat.card V)
    (hφz : φ z = z⁻¹) (b : V) : φ b * b⁻¹ ∈ Subgroup.zpowers z := by
  let d : V →* V :=
    { toFun := fun b => φ b * b⁻¹
      map_one' := by simp
      map_mul' := fun a c => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : Nat.card d.ker = Nat.card {b : V // φ b = b} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => by
      rw [MonoidHom.mem_ker]
      exact mul_inv_eq_one)
  have hrange : Nat.card d.range = 3 := by
    have h1 := d.ker.card_mul_index
    rw [Subgroup.index_ker, hker] at h1
    haveI : Nonempty {b : V // φ b = b} := ⟨⟨1, map_one φ⟩⟩
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hφc.symm)
  have hzinv : z⁻¹ = z * z := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hz3)
  have hzr : z ∈ d.range := ⟨z, by
    show φ z * z⁻¹ = z
    rw [hφz, hzinv, ← mul_assoc, ← pow_three', hz3, one_mul]⟩
  have hle : Subgroup.zpowers z ≤ d.range := (Subgroup.zpowers_le).mpr hzr
  have hcz : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    haveI := Fact.mk Nat.prime_three
    exact orderOf_eq_prime hz3 hz1
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hcz])
  rw [heq]
  exact ⟨b, rfl⟩

theorem unip_of_refl {V : Type*} [CommGroup V] [Finite V] {z : V} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) {φ φ' : MulAut V}
    (hφc : Nat.card {b : V // φ b = b} * 3 = Nat.card V) (hφz : φ z = z⁻¹)
    (hφ'c : Nat.card {b : V // φ' b = b} * 3 = Nat.card V) (hφ'z : φ' z = z⁻¹) :
    (φ * φ') z = z ∧ ∀ b, (φ * φ') b * b⁻¹ ∈ Subgroup.zpowers z := by
  refine ⟨by rw [MulAut.mul_apply, hφ'z, map_inv, hφz, inv_inv], fun b => ?_⟩
  have htm := mul_inv_mem_zpowers_of_refl hz3 hz1 hφ'c hφ'z b
  have hb' : φ' b = φ' b * b⁻¹ * b := (inv_mul_cancel_right _ _).symm
  rw [MulAut.mul_apply, hb', map_mul, inv_of_mem_zpowers hφz htm, mul_assoc]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htm) (mul_inv_mem_zpowers_of_refl hz3 hz1 hφc hφz b)

theorem commute_of_unip {V : Type*} [CommGroup V] {z : V} {u u' : MulAut V}
    (hu : u z = z ∧ ∀ b, u b * b⁻¹ ∈ Subgroup.zpowers z)
    (hu' : u' z = z ∧ ∀ b, u' b * b⁻¹ ∈ Subgroup.zpowers z) : u * u' = u' * u := by
  ext b
  simp only [MulAut.mul_apply]
  obtain ⟨s, hs, hsb⟩ : ∃ s ∈ Subgroup.zpowers z, u b = s * b :=
    ⟨_, hu.2 b, (inv_mul_cancel_right _ _).symm⟩
  obtain ⟨s', hs', hs'b⟩ : ∃ s ∈ Subgroup.zpowers z, u' b = s * b :=
    ⟨_, hu'.2 b, (inv_mul_cancel_right _ _).symm⟩
  rw [hs'b, map_mul, fix_of_mem_zpowers hu.1 hs', hsb, map_mul, fix_of_mem_zpowers hu'.1 hs, hs'b]
  exact mul_left_comm _ _ _

theorem ggFrameA4_of_weylOfType {ι : Type} {M : CoxeterMatrix ι}
    (hconj : ∃ i₀ : ι, ∀ i, ∃ w : M.Group, w * M.simple i₀ = M.simple i * w)
    (hnc : ∃ i j k l : ι, M.simple i * M.simple j * (M.simple k * M.simple l) ≠
      M.simple k * M.simple l * (M.simple i * M.simple j))
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} (hBsE : IsElemAbelian 3 Bs)
    {A₀ : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A₀)
    (he : ∀ i : ι, GGIsReflection 3 ((e (M.simple i) : ↥A₀) : MulAut ↥Bs))
    (hA₀ : A₀ ≤ ggAutomizer ⊤ Bs) (hfix : ∀ b : ↥Bs, (∀ φ ∈ A₀, φ b = b) → b = 1)
    {z : G} (hzBs : z ∈ Bs) (hz1 : z ≠ 1) :
    ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧
      g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  letI : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with mul_comm := fun a b => hBsE.1.is_comm.comm a b }
  let z' : ↥Bs := ⟨z, hzBs⟩
  have hz'3 : z' ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hBsE.2 z hzBs)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  let S : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | φ z' ∈ Subgroup.zpowers z' ∧ φ⁻¹ z' ∈ Subgroup.zpowers z'}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · rw [MulAut.mul_apply]; exact map_mem_zpowers ha hb
        · rw [mul_inv_rev, MulAut.mul_apply]; exact map_mem_zpowers hb' ha'
      one_mem' := ⟨Subgroup.mem_zpowers z', Subgroup.mem_zpowers z'⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by rw [inv_inv]; exact ha⟩ }
  have key : ∀ h : G, ∀ ψ : MulAut ↥Bs, (∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = h * b * h⁻¹) →
      ψ z' ∈ Subgroup.zpowers z' := by
    intro h ψ hψ
    have e1 : ((ψ z' : ↥Bs) : G) = h * z * h⁻¹ := hψ z'
    have hmem : h * z * h⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      rw [Set.mem_singleton_iff.mp hw, ← e1]
      exact congrArg Subtype.val (mul_comm z' (ψ z'))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcon h hmem)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow, e1]; exact hk)⟩
  have hgen : ∀ H : Subgroup G, ggInduced H Bs ⊆ S := by
    rintro H φ ⟨g, -, -, hφ⟩
    refine ⟨key g φ hφ, key g⁻¹ φ⁻¹ fun b => ?_⟩
    have h1 := hφ (φ⁻¹ b)
    rw [MulAut.apply_inv_self] at h1
    rw [inv_inv, h1]
    group
  have hAleS : A₀ ≤ S := hA₀.trans ((Subgroup.closure_le _).mpr (hgen ⊤))
  have hAS : ∀ w : M.Group, ((e w : ↥A₀) : MulAut ↥Bs) ∈ S :=
    fun w => hAleS (e w).2
  obtain ⟨i₀, hi₀⟩ := hconj
  have hsame : ∀ i, ((e (M.simple i) : ↥A₀) : MulAut ↥Bs) z' =
      ((e (M.simple i₀) : ↥A₀) : MulAut ↥Bs) z' := by
    intro i
    obtain ⟨w, hw⟩ := hi₀ i
    have h := congrArg (fun v => ((e v : ↥A₀) : MulAut ↥Bs)) hw
    simp only [map_mul, Subgroup.coe_mul] at h
    exact apply_eq_of_conj h (hAS w).2 (hAS _).1
  by_cases h0 : ((e (M.simple i₀) : ↥A₀) : MulAut ↥Bs) z' = z'
  ·
    have hfixall : ∀ ψ ∈ A₀, ψ z' = z' := by
      intro ψ hψ
      obtain ⟨w, rfl⟩ : ∃ w, ((e w : ↥A₀) : MulAut ↥Bs) = ψ :=
        ⟨e.symm ⟨ψ, hψ⟩, by simp⟩
      let T : Subgroup M.Group :=
        (MulAction.stabilizer (MulAut ↥Bs) z').comap
          (A₀.subtype.comp e.toMonoidHom)
      have hT : (⊤ : Subgroup M.Group) ≤ T := by
        rw [← M.toCoxeterSystem.subgroup_closure_range_simple, Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
        exact (hsame i).trans h0
      exact hT (Subgroup.mem_top w)
    exact hz'1 (hfix z' hfixall)
  ·
    have hφ1 : ((e (M.simple i₀) : ↥A₀) : MulAut ↥Bs) z' ≠ 1 :=
      fun h => hz'1 ((map_eq_one_iff _ (MulEquiv.injective _)).mp h)
    have hinvz : ∀ i, ((e (M.simple i) : ↥A₀) : MulAut ↥Bs) z' =
        z'⁻¹ := fun i => (hsame i).trans (eq_inv_of_mem_zpowers hz'3 (hAS _).1 hφ1 h0)
    obtain ⟨i, j, k, l, hne⟩ := hnc
    have hu := unip_of_refl hz'3 hz'1 (he i).2 (hinvz i) (he j).2 (hinvz j)
    have hu' := unip_of_refl hz'3 hz'1 (he k).2 (hinvz k) (he l).2 (hinvz l)
    have hcomm := commute_of_unip hu hu'
    apply hne
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact hcomm

theorem ggFrameA4Input_of {ι : Type} {M : CoxeterMatrix ι} (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput)
    (hconj : ∃ i₀ : ι, ∀ i, ∃ w : M.Group, w * M.simple i₀ = M.simple i * w)
    (hnc : ∃ i j k l : ι, M.simple i * M.simple j * (M.simple k * M.simple l) ≠
      M.simple k * M.simple l * (M.simple i * M.simple j)) : GGFrameA4Input M := by
  intro G _ _ B Bs x L D J hR hW hAt _ z hzB hz1
  obtain ⟨y, K, hN, e, he⟩ := hAt
  exact ggFrameA4_of_weylOfType hconj hnc hR.1.2.1.2.1 e he
    (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
    (eq_one_of_fix_join hTBF hWI hR hW hN) (hR.1.2.1.1 hzB) hz1

theorem coxeterE7_eq : CoxeterMatrix.E₇ = coxeterMatrix (isFiniteType_cartan .E7) :=
  (coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E7)
    (M := CoxeterMatrix.E₇) (isFiniteType_cartan .E7) (by
      have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E7 = CartanMatrix.E 7 := cartanE_eq 7
      exact hc.symm ▸ ggIntCartan_E₇)).symm

theorem coxeterE8_eq : CoxeterMatrix.E₈ = coxeterMatrix (isFiniteType_cartan .E8) :=
  (coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
    (M := CoxeterMatrix.E₈) (isFiniteType_cartan .E8) (by
      have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8
      exact hc.symm ▸ ggIntCartan_E₈)).symm

def iE7 (n : Fin 7) : Fin Tag.E7.rank := n

def iE8 (n : Fin 8) : Fin Tag.E8.rank := n

def cwE7Raw : Fin 7 → List (Fin 7) :=
  ![[], [3, 1, 2, 3, 0, 2], [0, 2], [2, 3, 0, 2], [3, 4, 2, 3, 0, 2], [4, 5, 3, 4, 2, 3, 0, 2],
    [5, 6, 4, 5, 3, 4, 2, 3, 0, 2]]

def cwE7 : Fin Tag.E7.rank → List (Fin Tag.E7.rank) := cwE7Raw

def cwE8Raw : Fin 8 → List (Fin 8) :=
  ![[], [3, 1, 2, 3, 0, 2], [0, 2], [2, 3, 0, 2], [3, 4, 2, 3, 0, 2], [4, 5, 3, 4, 2, 3, 0, 2],
    [5, 6, 4, 5, 3, 4, 2, 3, 0, 2], [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2]]

def cwE8 : Fin Tag.E8.rank → List (Fin Tag.E8.rank) := cwE8Raw

theorem cwE7_act : ∀ i k : Fin Tag.E7.rank,
    TableBExc.wordAct .E7 (cwE7 i) (reflect .E7 (iE7 0) (Pi.single k 1)) =
      reflect .E7 i (TableBExc.wordAct .E7 (cwE7 i) (Pi.single k 1)) := by
  decide +kernel

theorem cwE8_act : ∀ i k : Fin Tag.E8.rank,
    TableBExc.wordAct .E8 (cwE8 i) (reflect .E8 (iE8 0) (Pi.single k 1)) =
      reflect .E8 i (TableBExc.wordAct .E8 (cwE8 i) (Pi.single k 1)) := by
  decide +kernel

theorem ncE7_act : ∃ k : Fin Tag.E7.rank,
    reflect .E7 (iE7 0) (reflect .E7 (iE7 2) (reflect .E7 (iE7 2) (reflect .E7 (iE7 3)
      (Pi.single k 1)))) ≠
    reflect .E7 (iE7 2) (reflect .E7 (iE7 3) (reflect .E7 (iE7 0) (reflect .E7 (iE7 2)
      (Pi.single k 1)))) := by
  decide +kernel

theorem ncE8_act : ∃ k : Fin Tag.E8.rank,
    reflect .E8 (iE8 0) (reflect .E8 (iE8 2) (reflect .E8 (iE8 2) (reflect .E8 (iE8 3)
      (Pi.single k 1)))) ≠
    reflect .E8 (iE8 2) (reflect .E8 (iE8 3) (reflect .E8 (iE8 0) (reflect .E8 (iE8 2)
      (Pi.single k 1)))) := by
  decide +kernel

theorem conj_simple_E7 : ∃ i₀ : Fin Tag.E7.rank, ∀ i, ∃ w : WeylGroup .E7,
    w * simple .E7 i₀ = simple .E7 i * w :=
  ⟨iE7 0, fun i => ⟨wordW .E7 (cwE7 i), ext_single fun k => by
    simp only [mul_smul, wordW_smul, simple_smul]
    exact cwE7_act i k⟩⟩

theorem conj_simple_E8 : ∃ i₀ : Fin Tag.E8.rank, ∀ i, ∃ w : WeylGroup .E8,
    w * simple .E8 i₀ = simple .E8 i * w :=
  ⟨iE8 0, fun i => ⟨wordW .E8 (cwE8 i), ext_single fun k => by
    simp only [mul_smul, wordW_smul, simple_smul]
    exact cwE8_act i k⟩⟩

theorem noncomm_E7 : ∃ i j k l : Fin Tag.E7.rank,
    simple .E7 i * simple .E7 j * (simple .E7 k * simple .E7 l) ≠
      simple .E7 k * simple .E7 l * (simple .E7 i * simple .E7 j) := by
  refine ⟨iE7 0, iE7 2, iE7 2, iE7 3, fun h => ?_⟩
  obtain ⟨k, hk⟩ := ncE7_act
  apply hk
  have h2 := congrArg (· • (Pi.single k 1 : Fin Tag.E7.rank → ℤ)) h
  simp only [mul_smul, simple_smul] at h2
  exact h2

theorem noncomm_E8 : ∃ i j k l : Fin Tag.E8.rank,
    simple .E8 i * simple .E8 j * (simple .E8 k * simple .E8 l) ≠
      simple .E8 k * simple .E8 l * (simple .E8 i * simple .E8 j) := by
  refine ⟨iE8 0, iE8 2, iE8 2, iE8 3, fun h => ?_⟩
  obtain ⟨k, hk⟩ := ncE8_act
  apply hk
  have h2 := congrArg (· • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) h
  simp only [mul_smul, simple_smul] at h2
  exact h2

theorem ggFrameA4Input_E7 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGFrameA4Input CoxeterMatrix.E₇ := by
  rw [coxeterE7_eq]
  exact ggFrameA4Input_of hTBF hWI conj_simple_E7 noncomm_E7

theorem ggFrameA4Input_E8 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGFrameA4Input CoxeterMatrix.E₈ := by
  rw [coxeterE8_eq]
  exact ggFrameA4Input_of hTBF hWI conj_simple_E8 noncomm_E8

end CFSG.StandardType.FrameRoute

end
