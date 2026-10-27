module

public import CFSG.Quasithin.EmptyFaithful.S151TBBridge
public import CFSG.Quasithin.EmptyFaithful.S151TBA7Comb
public import CFSG.Quasithin.EmptyFaithful.S151TBA7Aut

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem mem_autOn_iff {X V : Subgroup G} {φ : MulAut ↥V} :
    φ ∈ autOn X V ↔
      ∃ n : ↥(Subgroup.normalizer (V : Set G)), (n : G) ∈ X ∧ conjAct V n = φ := by
  unfold autOn
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem conjAct_mem_autOn {X V : Subgroup G} (n : ↥(Subgroup.normalizer (V : Set G)))
    (hn : (n : G) ∈ X) : conjAct V n ∈ autOn X V :=
  mem_autOn_iff.2 ⟨n, hn, rfl⟩

theorem autOn_mono {X Y V : Subgroup G} (h : X ≤ Y) : autOn X V ≤ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_mono h

theorem conjAct_commute_iff (V : Subgroup G) (n m : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V n * conjAct V m = conjAct V m * conjAct V n ↔
      (n : G) * (m : G) * (n : G)⁻¹ * (m : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have h := conjAct_eq_one_iff V (n * m * n⁻¹ * m⁻¹)
  have h1 : conjAct V (n * m * n⁻¹ * m⁻¹) = ⁅conjAct V n, conjAct V m⁆ := by
    simp [commutatorElement_def]
  rw [h1, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem conj_mem_autOn {X R V : Subgroup G} (hXR : X ≤ Subgroup.normalizer (R : Set G))
    {x a : MulAut ↥V} (hx : x ∈ autOn X V) (ha : a ∈ autOn R V) : x * a * x⁻¹ ∈ autOn R V := by
  obtain ⟨g₁, hg₁, rfl⟩ := mem_autOn_iff.1 hx
  obtain ⟨g₂, hg₂, rfl⟩ := mem_autOn_iff.1 ha
  refine mem_autOn_iff.2 ⟨g₁ * g₂ * g₁⁻¹, ?_, by simp [map_mul, map_inv]⟩
  show (g₁ : G) * g₂ * (g₁ : G)⁻¹ ∈ R
  exact (Subgroup.mem_normalizer_iff.mp (hXR hg₁) g₂).mp hg₂

section Config

variable [Finite G] {K R V M : Subgroup G}

theorem mem_pCoreOf_of_centralizer
    (hC : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    (hcen : Subgroup.center (LStar K) = ⊥) {x : G} (hxK : x ∈ K)
    (hxV : x ∈ Subgroup.centralizer (V : Set G)) : x ∈ pCoreOf 2 K := by
  have h := mk_mem_center_of_centralizer hC (x := ⟨x, hxK⟩) hxV
  rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h
  exact ⟨⟨x, hxK⟩, h, rfl⟩

omit [Finite G] in
theorem mem_pCoreOf_iff_of_ker_eq {Q : Type*} [Group Q] {α : ↥K →* Q}
    (hk : α.ker = CFSG.pCore 2 ↥K) {x : G} (hx : x ∈ K) :
    x ∈ pCoreOf 2 K ↔ α ⟨x, hx⟩ = 1 := by
  rw [← MonoidHom.mem_ker, hk]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mul_inv_comm_iff {H : Type*} [Group H] (a τ : H) :
    a * (τ * a⁻¹ * τ⁻¹) = 1 ↔ a * τ = τ * a := by
  have h : a * (τ * a⁻¹ * τ⁻¹) = ⁅a, τ⁆ := by
    simp only [commutatorElement_def, mul_assoc]
  rw [h]
  exact commutatorElement_eq_one_iff_mul_comm

theorem weight_two_of_case_b {K R V M : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ∧
      (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
      IsTwoReducedIn (K ⊔ R) V)
    (hcen : Subgroup.center (LStar K) = ⊥) (hO2M : pCoreOf 2 K ≤ M)
    {α α' : ↥K →* alternatingGroup (Fin 7)} (hα : IsAltBlockTypeWith K 7 α)
    (hα' : IsAltBlockTypeWith K 7 α') {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hRact : autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩)) {p q : Fin 7} (hpq : p ≠ q)
    (hconj : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α' ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        Equiv.swap p q * (α' ⟨k, hk⟩ : Equiv.Perm (Fin 7)) * (Equiv.swap p q)⁻¹)
    (hMK : autOn (M ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V))) :
    ∃ v : ↥(evenWeight 7), HasWeightTwo (v : Fin 7 → ZMod 2) ∧
      ∀ x : ↥K, (x : G) ∈ M ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v := by
  obtain ⟨hP, hC, hred⟩ := h1
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hker : ((alternatingGroup (Fin 7)).subtype.comp α').ker = α.ker := by
    ext y
    have h1 : y ∈ ((alternatingGroup (Fin 7)).subtype.comp α').ker ↔ y ∈ α'.ker := by
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        rw [h]
        rfl
    rw [h1, hα'.2.1, ← hα.2.1]
  obtain ⟨g, hg⟩ := exists_conj_of_ker_eq α hα.1 ((alternatingGroup (Fin 7)).subtype.comp α') hker
  have hg' : ∀ y : ↥K, ((α' y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      g * (α y : Equiv.Perm (Fin 7)) * g⁻¹ := fun y => hg y
  have hij : g⁻¹ p ≠ g⁻¹ q := fun h => hpq (g⁻¹.injective h)
  have hτ : Equiv.swap (g⁻¹ p) (g⁻¹ q) = g⁻¹ * Equiv.swap p q * g := by
    rw [Equiv.swap_apply_apply]
    simp
  set τ : Equiv.Perm (Fin 7) := Equiv.swap (g⁻¹ p) (g⁻¹ q) with hτdef
  have hτα : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        τ * (α ⟨k, hk⟩ : Equiv.Perm (Fin 7)) * τ⁻¹ := by
    intro k hk hk'
    have h := hconj k hk hk'
    rw [hg', hg'] at h
    rw [hτ]
    calc ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
        = g⁻¹ * (g * (α ⟨t * k * t⁻¹, hk'⟩ : Equiv.Perm (Fin 7)) * g⁻¹) * g := by group
      _ = g⁻¹ * (Equiv.swap p q * (g * (α ⟨k, hk⟩ : Equiv.Perm (Fin 7)) * g⁻¹) *
            (Equiv.swap p q)⁻¹) * g := by rw [h]
      _ = (g⁻¹ * Equiv.swap p q * g) * (α ⟨k, hk⟩ : Equiv.Perm (Fin 7)) *
            (g⁻¹ * Equiv.swap p q * g)⁻¹ := by group
  have htK : ∀ k : G, k ∈ K → t * k * t⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 (hRK htR) k).1 hk
  have hcommute : ∀ x : ↥K, conjAct V ⟨(x : G), hKV x.2⟩ * conjAct V ⟨t, htV⟩ =
      conjAct V ⟨t, htV⟩ * conjAct V ⟨(x : G), hKV x.2⟩ ↔
      (α x : Equiv.Perm (Fin 7)) * τ = τ * (α x : Equiv.Perm (Fin 7)) := by
    intro x
    rw [conjAct_commute_iff]
    have hk' : t * (x : G)⁻¹ * t⁻¹ ∈ K := htK _ (K.inv_mem x.2)
    have hdK : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ K := by
      have h3 := K.mul_mem x.2 hk'
      simpa [mul_assoc] using h3
    have hcentre : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ Subgroup.centralizer (V : Set G) ↔
        (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ pCoreOf 2 K :=
      ⟨mem_pCoreOf_of_centralizer hC hcen hdK, fun h => pCore_le_centralizer hRK hP h⟩
    have hdc := mem_pCoreOf_iff_of_ker_eq hα.2.1 hdK
    have hmul : (⟨(x : G) * t * (x : G)⁻¹ * t⁻¹, hdK⟩ : ↥K) =
        x * ⟨t * (x : G)⁻¹ * t⁻¹, hk'⟩ := Subtype.ext (by simp [mul_assoc])
    have hinv : (⟨(x : G)⁻¹, K.inv_mem x.2⟩ : ↥K) = x⁻¹ := rfl
    have hval : ((α ⟨(x : G) * t * (x : G)⁻¹ * t⁻¹, hdK⟩ : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) = (α x : Equiv.Perm (Fin 7)) *
          (τ * (α x : Equiv.Perm (Fin 7))⁻¹ * τ⁻¹) := by
      rw [hmul, map_mul]
      have h5 := hτα (x : G)⁻¹ (K.inv_mem x.2) hk'
      rw [hinv, map_inv] at h5
      rw [Subgroup.coe_mul, h5]
      rfl
    rw [hcentre, hdc, ← mul_inv_comm_iff, ← hval]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hM : ∀ x : ↥K, (x : G) ∈ M ↔
      conjAct V ⟨(x : G), hKV x.2⟩ ∈ autOn (M ⊓ K) V := by
    intro x
    constructor
    · intro hx
      exact conjAct_mem_autOn _ ⟨hx, x.2⟩
    · intro hx
      obtain ⟨n, hn, hnx⟩ := mem_autOn_iff.1 hx
      have hn' : (n : G) ∈ M ⊓ K := hn
      have h1' : conjAct V (n⁻¹ * ⟨(x : G), hKV x.2⟩) = 1 := by
        rw [map_mul, map_inv, hnx]
        simp
      have h2 := (conjAct_eq_one_iff V _).1 h1'
      have h3 : (n : G)⁻¹ * (x : G) ∈ pCoreOf 2 K :=
        mem_pCoreOf_of_centralizer hC hcen (K.mul_mem (K.inv_mem hn'.2) x.2) (by simpa using h2)
      have h4 : (n : G)⁻¹ * (x : G) ∈ M := hO2M h3
      have h5 : (x : G) = (n : G) * ((n : G)⁻¹ * (x : G)) := by group
      rw [h5]
      exact M.mul_mem hn'.1 h4
  have hMt : ∀ x : ↥K, conjAct V ⟨(x : G), hKV x.2⟩ ∈ autOn (M ⊓ K) V ↔
      conjAct V ⟨(x : G), hKV x.2⟩ * conjAct V ⟨t, htV⟩ =
        conjAct V ⟨t, htV⟩ * conjAct V ⟨(x : G), hKV x.2⟩ := by
    intro x
    rw [hMK, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, h⟩
      have htb : conjAct V ⟨t, htV⟩ ∈ autOn R V := conjAct_mem_autOn _ htR
      exact (h _ htb).symm
    · intro h
      refine ⟨conjAct_mem_autOn _ x.2, fun a ha => ?_⟩
      rw [SetLike.mem_coe, hRact] at ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact (Commute.zpow_left (show Commute (conjAct V ⟨t, htV⟩)
        (conjAct V ⟨(x : G), hKV x.2⟩) from h.symm) n).eq
  refine ⟨pairVecΔ (g⁻¹ p) (g⁻¹ q) hij, hasWeightTwo_pairVec _ _ hij, fun x => ?_⟩
  rw [hM, hMt, hcommute]
  exact (permWeight_pairVec_iff _ _ _ hij).symm

theorem dihedral_four_central_unique :
    ∀ w : DihedralGroup 4, (∀ g : DihedralGroup 4, g * w = w * g) → w ≠ 1 →
      w = DihedralGroup.r 2 := by
  decide

omit [Finite G] in
theorem false_of_case_iii {K R V M : Subgroup G} (hMR : M ≤ Subgroup.normalizer (R : Set G))
    (hD : Nonempty (↥(autOn R V) ≃* DihedralGroup 4))
    (e : ↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 7)) {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {4, 3})
    (hMap : ((autOn (M ⊓ K) V).subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) : False := by
  obtain ⟨ψ⟩ := hD
  have hRA : autOn R V ≤ autOn (K ⊔ R) V := autOn_mono le_sup_right
  set z₁ : ↥(autOn R V) := ψ.symm (DihedralGroup.r 2) with hz₁
  have hψz₁ : ψ z₁ = DihedralGroup.r 2 := ψ.apply_symm_apply _
  have hz₁c : ∀ a : ↥(autOn R V), a * z₁ = z₁ * a := by
    intro a
    apply ψ.injective
    rw [map_mul, map_mul, hψz₁]
    have : ∀ g : DihedralGroup 4, g * DihedralGroup.r 2 = DihedralGroup.r 2 * g := by decide
    exact this _
  have hz₁ne : z₁ ≠ 1 := by
    intro h
    have h' := congrArg ψ h
    rw [hψz₁, map_one] at h'
    revert h'
    decide
  have hz₁sq : z₁ * z₁ = 1 := by
    apply ψ.injective
    rw [map_mul, hψz₁, map_one]
    decide
  let z : Equiv.Perm (Fin 7) := e ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩
  have hz1 : z ≠ 1 := by
    intro h
    apply hz₁ne
    have h' := e.injective (h.trans (map_one e).symm)
    have h'' : (z₁ : MulAut ↥V) = 1 := congrArg Subtype.val h'
    exact Subtype.ext h''
  have hz2 : z * z = 1 := by
    have hsq' : (z₁ : MulAut ↥V) * (z₁ : MulAut ↥V) = 1 := congrArg Subtype.val hz₁sq
    have : (⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ * ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ :
        ↥(autOn (K ⊔ R) V)) = 1 := Subtype.ext hsq'
    show e _ * e _ = 1
    rw [← map_mul, this, map_one]
  refine false_of_involution_commuting_stab hP hz1 hz2 ?_
  intro x hxA hxS
  have hx : x ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7) :=
    ⟨(mem_stabilizer_iff_stabilizes x P).2 hxS, hxA⟩
  rw [← hMap] at hx
  obtain ⟨μ, hμ, rfl⟩ := Subgroup.mem_map.1 hx
  have hμ' : (μ : MulAut ↥V) ∈ autOn (M ⊓ K) V := Subgroup.mem_subgroupOf.1 hμ
  have hXR : M ⊓ K ≤ Subgroup.normalizer (R : Set G) := inf_le_left.trans hMR
  have hw : (μ : MulAut ↥V) * (z₁ : MulAut ↥V) * (μ : MulAut ↥V)⁻¹ ∈ autOn R V :=
    conj_mem_autOn hXR hμ' z₁.2
  let w : ↥(autOn R V) := ⟨_, hw⟩
  have hwc : ∀ a : ↥(autOn R V), a * w = w * a := by
    intro a
    have ha' : (μ : MulAut ↥V)⁻¹ * (a : MulAut ↥V) * ((μ : MulAut ↥V)⁻¹)⁻¹ ∈ autOn R V :=
      conj_mem_autOn hXR (inv_mem hμ') a.2
    have hcomm := congrArg Subtype.val (hz₁c ⟨_, ha'⟩)
    apply Subtype.ext
    show (a : MulAut ↥V) * ((μ : MulAut ↥V) * (z₁ : MulAut ↥V) * (μ : MulAut ↥V)⁻¹) =
      ((μ : MulAut ↥V) * (z₁ : MulAut ↥V) * (μ : MulAut ↥V)⁻¹) * (a : MulAut ↥V)
    have hcomm' : (μ : MulAut ↥V)⁻¹ * (a : MulAut ↥V) * (μ : MulAut ↥V) * (z₁ : MulAut ↥V) =
        (z₁ : MulAut ↥V) * ((μ : MulAut ↥V)⁻¹ * (a : MulAut ↥V) * (μ : MulAut ↥V)) := by
      simpa using hcomm
    calc (a : MulAut ↥V) * ((μ : MulAut ↥V) * (z₁ : MulAut ↥V) * (μ : MulAut ↥V)⁻¹)
        = (μ : MulAut ↥V) * ((μ : MulAut ↥V)⁻¹ * (a : MulAut ↥V) * (μ : MulAut ↥V) *
            (z₁ : MulAut ↥V)) * (μ : MulAut ↥V)⁻¹ := by group
      _ = (μ : MulAut ↥V) * ((z₁ : MulAut ↥V) * ((μ : MulAut ↥V)⁻¹ * (a : MulAut ↥V) *
            (μ : MulAut ↥V))) * (μ : MulAut ↥V)⁻¹ := by rw [hcomm']
      _ = ((μ : MulAut ↥V) * (z₁ : MulAut ↥V) * (μ : MulAut ↥V)⁻¹) * (a : MulAut ↥V) := by group
  have hwne : w ≠ 1 := by
    intro h
    apply hz₁ne
    have h' : (μ : MulAut ↥V) * (z₁ : MulAut ↥V) * (μ : MulAut ↥V)⁻¹ = 1 := congrArg Subtype.val h
    apply Subtype.ext
    have h'' : (z₁ : MulAut ↥V) = (μ : MulAut ↥V)⁻¹ * 1 * (μ : MulAut ↥V) := by
      rw [← h']
      group
    simpa using h''
  have hψw : ψ w = DihedralGroup.r 2 := by
    refine dihedral_four_central_unique (ψ w) (fun g => ?_)
      (fun h => hwne (ψ.injective (by simpa using h)))
    have := hwc (ψ.symm g)
    have h2 := congrArg ψ this
    rw [map_mul, map_mul, ψ.apply_symm_apply] at h2
    exact h2
  have hweq : w = z₁ := ψ.injective (hψw.trans hψz₁.symm)
  have hμz : (μ : MulAut ↥V) * (z₁ : MulAut ↥V) = (z₁ : MulAut ↥V) * (μ : MulAut ↥V) := by
    have h' : (μ : MulAut ↥V) * (z₁ : MulAut ↥V) * (μ : MulAut ↥V)⁻¹ = (z₁ : MulAut ↥V) :=
      congrArg Subtype.val hweq
    rw [mul_inv_eq_iff_eq_mul] at h'
    exact h'
  show e μ * z = z * e μ
  show e μ * e ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ = e ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ * e μ
  rw [← map_mul, ← map_mul]
  exact congrArg e (Subtype.ext hμz)

theorem stabilizes_conj {σ : Equiv.Perm (Fin 7)} (π : Equiv.Perm (Fin 7))
    {P : Finset (Finset (Fin 7))} (h : StabilizesPartition σ P) :
    StabilizesPartition (π * σ * π⁻¹) (P.image (Finset.image π)) := by
  unfold StabilizesPartition at h ⊢
  rw [Finset.image_image]
  have hcomp : (Finset.image (π * σ * π⁻¹)) ∘ (Finset.image π) =
      (Finset.image π) ∘ (Finset.image σ) := by
    funext B
    simp only [Function.comp_apply, Finset.image_image]
    congr 1
    funext b
    simp
  rw [hcomp, ← Finset.image_image, h]

theorem isPartitionOfType_image {n : ℕ} {P : Finset (Finset (Fin n))} {sizes : Multiset ℕ}
    (hP : IsPartitionOfType P sizes) (π : Equiv.Perm (Fin n)) :
    IsPartitionOfType (P.image (Finset.image π)) sizes := by
  obtain ⟨hne, hdisj, hcov, hcard⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    exact (hne B₀ hB₀).image π
  · intro B hB B' hB' hne'
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨B₀', hB₀', rfl⟩ := Finset.mem_image.mp hB'
    have hne₀ : B₀ ≠ B₀' := fun h => hne' (by rw [h])
    exact (Finset.disjoint_image π.injective).mpr (hdisj B₀ hB₀ B₀' hB₀' hne₀)
  · have : (P.image (Finset.image π)).biUnion id = Finset.image π (P.biUnion id) := by
      rw [Finset.image_biUnion, Finset.biUnion_image]
      rfl
    rw [this, hcov]
    exact Finset.image_univ_of_surjective π.surjective
  · have hinj : Function.Injective (Finset.image π) := Finset.image_injective π.injective
    rw [Finset.image_val_of_injOn hinj.injOn, Multiset.map_map, ← hcard]
    apply Multiset.map_congr rfl
    intro B _
    exact Finset.card_image_of_injective _ π.injective

theorem exists_majority (w : Fin 7 → ZMod 2) :
    ∃ X : Finset (Fin 7), 4 ≤ X.card ∧ ((∀ i ∈ X, w i = 1) ∨ (∀ i ∈ X, w i = 0)) := by
  by_cases h : 4 ≤ (Finset.univ.filter fun i => w i = 1).card
  · exact ⟨_, h, Or.inl (fun i hi => (Finset.mem_filter.1 hi).2)⟩
  · refine ⟨Finset.univ.filter fun i => w i = 0, ?_,
      Or.inr (fun i hi => (Finset.mem_filter.1 hi).2)⟩
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
      (fun i => w i = 1)
    have hfilt : (Finset.univ.filter fun i => ¬ w i = 1) = Finset.univ.filter fun i => w i = 0 := by
      apply Finset.filter_congr
      intro i _
      generalize w i = a
      revert a
      decide
    rw [hfilt] at hsum
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega

theorem threeCycle_inv_a {a b c : Fin 7} : (threeCycle a b c)⁻¹ a = c := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (threeCycle_c a b c).symm

theorem threeCycle_inv_b {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) :
    (threeCycle a b c)⁻¹ b = a := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (threeCycle_a hab hac).symm

theorem threeCycle_inv_c {a b c : Fin 7} (hbc : b ≠ c) (hac : a ≠ c) :
    (threeCycle a b c)⁻¹ c = b := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (threeCycle_b hbc hac).symm

theorem permWeight_threeCycle_fix (w : ↥(evenWeight 7)) {X : Finset (Fin 7)}
    (hX : (∀ i ∈ X, (w : Fin 7 → ZMod 2) i = 1) ∨ (∀ i ∈ X, (w : Fin 7 → ZMod 2) i = 0))
    {a b c : Fin 7} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : permWeight 7 (threeCycle a b c) w = w := by
  have hconst : ∀ i ∈ X, ∀ j ∈ X, (w : Fin 7 → ZMod 2) i = (w : Fin 7 → ZMod 2) j := by
    intro i hi j hj
    rcases hX with h | h
    · rw [h i hi, h j hj]
    · rw [h i hi, h j hj]
  apply Subtype.ext
  funext i
  show (w : Fin 7 → ZMod 2) ((threeCycle a b c)⁻¹ i) = (w : Fin 7 → ZMod 2) i
  by_cases hia : i = a
  · rw [hia, threeCycle_inv_a]
    exact hconst c hc a ha
  · by_cases hib : i = b
    · rw [hib, threeCycle_inv_b hab hac]
      exact hconst a ha b hb
    · by_cases hic : i = c
      · rw [hic, threeCycle_inv_c hbc hac]
        exact hconst b hb c hc
      · rw [Equiv.Perm.inv_eq_iff_eq.2 (threeCycle_other hia hib hic).symm]

theorem false_of_case_iv {K R V M : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ∧
      (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
      IsTwoReducedIn (K ⊔ R) V)
    (hcen : Subgroup.center (LStar K) = ⊥)
    {α : ↥K →* alternatingGroup (Fin 7)} (hα : IsAltBlockTypeWith K 7 α)
    (e : ↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 7)) {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {2, 2, 2, 1})
    (hMap : ((autOn (M ⊓ K) V).subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7))
    (v : ↥(evenWeight 7))
    (hStab : ∀ x : ↥K, permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v → (x : G) ∈ M) : False := by
  obtain ⟨hP1, hC, hred⟩ := h1
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hφ0 : ∀ x : ↥K, ((conjAct V).comp (Subgroup.inclusion hKV)) x ∈ autOn (K ⊔ R) V :=
    fun x => conjAct_mem_autOn _ ((le_sup_left : K ≤ K ⊔ R) x.2)
  let φ1 : ↥K →* ↥(autOn (K ⊔ R) V) :=
    ((conjAct V).comp (Subgroup.inclusion hKV)).codRestrict (autOn (K ⊔ R) V) hφ0
  let φ : ↥K →* Equiv.Perm (Fin 7) := e.toMonoidHom.comp φ1
  have hkerφ : φ.ker = α.ker := by
    ext x
    have hx1 : φ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
      show e (φ1 x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
      have h := conjAct_eq_one_iff V (Subgroup.inclusion hKV x)
      exact ⟨fun h' => h.1 (congrArg Subtype.val h'), fun h' => Subtype.ext (h.2 h')⟩
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hx1]
    have hc : (x : G) ∈ Subgroup.centralizer (V : Set G) ↔ (x : G) ∈ pCoreOf 2 K :=
      ⟨mem_pCoreOf_of_centralizer hC hcen x.2, fun h => pCore_le_centralizer hRK hP1 h⟩
    rw [hc]
    exact mem_pCoreOf_iff_of_ker_eq hα.2.1 x.2
  obtain ⟨g, hg⟩ := exists_conj_of_ker_eq α hα.1 φ hkerφ
  obtain ⟨X, hX4, hXc⟩ := exists_majority (v : Fin 7 → ZMod 2)
  have hP' : IsPartitionOfType (P.image (Finset.image (g⁻¹ : Equiv.Perm (Fin 7)))) {2, 2, 2, 1} :=
    isPartitionOfType_image hP g⁻¹
  refine false_of_threeCycles_stab hP' (by omega : 3 ≤ X.card) ?_
  intro a b c ha hb hc hab hbc hac
  obtain ⟨x, hx⟩ := hα.1 ⟨threeCycle a b c, threeCycle_mem_alternating hab hbc⟩
  have hxc : (α x : Equiv.Perm (Fin 7)) = threeCycle a b c := congrArg Subtype.val hx
  have hfix : permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v := by
    rw [hxc]
    exact permWeight_threeCycle_fix v hXc ha hb hc hab hbc hac
  have hxM : (x : G) ∈ M := hStab x hfix
  have hstab : φ x ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7) := by
    rw [← hMap]
    exact ⟨φ1 x, Subgroup.mem_subgroupOf.2 (conjAct_mem_autOn _ ⟨hxM, x.2⟩), rfl⟩
  have hstab' : StabilizesPartition (φ x) P := (mem_stabilizer_iff_stabilizes _ _).1 hstab.1
  have h2 := stabilizes_conj g⁻¹ hstab'
  rw [hg x, hxc] at h2
  have h3 : g⁻¹ * (g * threeCycle a b c * g⁻¹) * g⁻¹⁻¹ = threeCycle a b c := by group
  rw [h3] at h2
  exact h2

end Config

end CFSG.Quasithin.S151TB
