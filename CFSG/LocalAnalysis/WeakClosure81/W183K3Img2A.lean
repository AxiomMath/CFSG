module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
public import CFSG.LocalAnalysis.WeakClosure81.W19ModE
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement
open W183K3

variable {G : Type} [Group G] [Finite G]

theorem w183K3Img2_hasQuotShape_of_mulEquiv {K L L' : Subgroup G} (e : ↥L ≃* ↥L')
    (hK : ∀ l : ↥L, (l : G) ∈ K ↔ (e l : G) ∈ K) {P : ∀ (X : Type) [Group X], Prop}
    (hQ : HasQuotShape L K P) : HasQuotShape L' K P := by
  obtain ⟨X, hX, φ, hφs, hφk, hPX⟩ := hQ
  refine ⟨X, hX, φ.comp e.symm.toMonoidHom, hφs.comp e.symm.surjective, ?_, hPX⟩
  intro k
  change φ (e.symm k) = 1 ↔ (k : G) ∈ K
  rw [hφk (e.symm k)]
  have h := hK (e.symm k)
  rwa [show e (e.symm k) = k from e.apply_symm_apply k] at h

theorem w183K3Img2_isComponentModN_map {K H L : Subgroup G} (e : G ≃* G)
    (hK : K.map e.toMonoidHom = K) (hH : H.map e.toMonoidHom = H)
    (h : IsComponentModN K H L) : IsComponentModN K H (L.map e.toMonoidHom) := by
  have hfe : Function.Injective e.toMonoidHom := fun a _b hab => e.injective (by simpa using hab)
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : e.symm k ∈ K := by
      rw [← hK] at hk
      obtain ⟨k', hk'K, hk'eq⟩ := Subgroup.mem_map.1 hk
      have hkk : k' = e.symm k := by
        rw [← hk'eq]
        change k' = e.symm (e k')
        rw [e.symm_apply_apply]
      rwa [hkk] at hk'K
    exact Subgroup.mem_map.2 ⟨e.symm k, h.2.1 hk', by simp⟩
  · rintro x ⟨l, hl, rfl⟩
    rw [← hH]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.2.2.1 hl)
  · have hsub := h.2.2.2.1.map e.toMonoidHom
    rwa [hH] at hsub
  · refine w183K3Img2_hasQuotShape_of_mulEquiv
      (Subgroup.equivMapOfInjective L e.toMonoidHom hfe) ?_ h.2.2.2.2
    intro l
    constructor
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hl
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK] at hl
      obtain ⟨k, hkK, hkeq⟩ := Subgroup.mem_map.1 hl
      have hkl : k = l := e.injective hkeq
      rwa [hkl] at hkK

theorem w183K3Img2_quot_of_shape {J E : Subgroup G} (M : ModDataE J E) {K A : Subgroup G}
    {Z : Subgroup (LGL 2 M.W)} (hAJ : A ≤ J) (hKA : K ≤ A)
    (hρker : ∀ j : ↥J, M.ρ j = 1 → (j : G) ∈ K)
    (hZ : ∀ j : ↥J, (M.ρ j : LGL 2 M.W) ∈ Z ↔ (j : G) ∈ K)
    {X : Type} [Group X] (φ : ↥A →* X) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥A, φ k = 1 ↔ (k : G) ∈ K) :
    ∃ θ : ↥(M.img A) →* X, Function.Surjective θ ∧
      ∀ r : ↥(M.img A), θ r = 1 ↔ (r : LGL 2 M.W) ∈ Z := by
  let ψ : ↥A →* LGL 2 M.W := M.ρ.comp (Subgroup.inclusion hAJ)
  have hψ : ∀ k : ↥A, ψ k = M.ρ (Subgroup.inclusion hAJ k) := fun _ => rfl
  let ψ' : ↥A →* ↥(M.img A) := ψ.codRestrict (M.img A) fun k => by
    rw [hψ k]
    exact M.mem_img.2 ⟨Subgroup.inclusion hAJ k, k.2, rfl⟩
  have hψ'coe : ∀ k : ↥A, (ψ' k : LGL 2 M.W) = ψ k := fun _ => rfl
  have hψ's : Function.Surjective ψ' := by
    intro y
    obtain ⟨j, hj, hjρ⟩ := M.mem_img.1 y.2
    refine ⟨⟨(j : G), hj⟩, Subtype.ext ?_⟩
    show (ψ' ⟨(j : G), hj⟩ : LGL 2 M.W) = (y : LGL 2 M.W)
    rw [hψ'coe, hψ]
    have hinc : Subgroup.inclusion hAJ ⟨(j : G), hj⟩ = j := Subtype.ext rfl
    rw [hinc, hjρ]
  have hle : ψ'.ker ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have h2 : M.ρ (Subgroup.inclusion hAJ k) = 1 := by
      rw [← hψ k, ← hψ'coe k]
      exact congrArg Subtype.val hk
    exact (hφk k).2 (hρker (Subgroup.inclusion hAJ k) h2)
  let θ : ↥(M.img A) →* X := MonoidHom.liftOfSurjective ψ' hψ's ⟨φ, hle⟩
  have hθ : ∀ l : ↥A, θ (ψ' l) = φ l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply ψ' _ _ ⟨φ, hle⟩ l
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨l, hl⟩ := hφs y
    exact ⟨ψ' l, by rw [hθ l, hl]⟩
  refine ⟨θ, hθs, ?_⟩
  intro r
  obtain ⟨l, hl⟩ := hψ's r
  have hθl : θ r = φ l := by rw [← hl, hθ l]
  rw [hθl, hφk l, ← hl]
  have hρj : (ψ' l : LGL 2 M.W) = M.ρ (Subgroup.inclusion hAJ l) := by
    rw [hψ'coe l, hψ l]
  rw [hρj]
  exact (hZ (Subgroup.inclusion hAJ l)).symm

theorem w183K3Img2_mem_sup_of_comm {W : Type} [Group W] {S C : Subgroup W}
    (hc : ∀ s ∈ S, ∀ c ∈ C, s * c = c * s) {x : W} :
    x ∈ S ⊔ C ↔ ∃ y ∈ S, ∃ z ∈ C, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, C.one_mem, by simp⟩
      · exact ⟨1, S.one_mem, y, hy, by simp⟩
    · exact ⟨1, S.one_mem, 1, C.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, S.mul_mem hy₁ hy₂, z₁ * z₂, C.mul_mem hz₁ hz₂, ?_⟩
      have h := hc y₂ hy₂ z₁ hz₁
      calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by simp only [mul_assoc]
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [h]
        _ = y₁ * z₁ * (y₂ * z₂) := by simp only [mul_assoc]
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, S.inv_mem hy, z⁻¹, C.inv_mem hz, ?_⟩
      calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by rw [mul_inv_rev]
        _ = (y * z)⁻¹ := by rw [← hc y hy z hz]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

theorem w183K3Img2_quasi_of_quot {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {A Z' : Subgroup (LGL 2 W)} {X : Type} [Group X]
    (hZA : Z' ≤ A) (hZc : ∀ z ∈ Z', ∀ a ∈ A, z * a = a * z)
    (θ : ↥A →* X) (hθs : Function.Surjective θ)
    (hθk : ∀ a : ↥A, θ a = 1 ↔ (a : LGL 2 W) ∈ Z')
    (hXs : IsSimpleGroup X) (hXnab : ∃ a b : X, a * b ≠ b * a) :
    A = ⁅A, A⁆ ⊔ Z' ∧ CFSG.Open.IsQuasisimple ↥⁅A, A⁆ ∧
      quasiCentre ⁅A, A⁆ = ⁅A, A⁆ ⊓ Z' := by
  classical
  haveI hXperf : Group.IsPerfect X :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun hc => by
      obtain ⟨a, b, hab⟩ := hXnab
      exact hab (hc.is_comm.comm a b)
  set A' : Subgroup (LGL 2 W) := ⁅A, A⁆ with hA'def
  have hA'A : A' ≤ A := Subgroup.commutator_le_self A
  haveI hZn : (Z'.subgroupOf A).Normal :=
    Subgroup.normal_of_le_center fun z hz => by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hZc (z : LGL 2 W) (Subgroup.mem_subgroupOf.mp hz)
        (w : LGL 2 W) w.2).symm
  have hkerθ : θ.ker = Z'.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hθk a
  let q : ↥A →* ↥A ⧸ Z'.subgroupOf A := QuotientGroup.mk' _
  have hkerq : q.ker = Z'.subgroupOf A := QuotientGroup.ker_mk' _
  let e : (↥A ⧸ Z'.subgroupOf A) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hkerθ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs)
  haveI hperfQ : Group.IsPerfect (↥A ⧸ Z'.subgroupOf A) :=
    Group.IsPerfect.ofSurjective
      (f := (e.symm : X →* (↥A ⧸ Z'.subgroupOf A))) e.symm.surjective
  have hmapq : ((⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆).map q) = ⊤ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact Subgroup.commutator_eq_self
  have hA'sub : A'.subgroupOf A = ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ := by
    apply Subgroup.map_injective A.subtype_injective
    show (A'.subgroupOf A).map A.subtype =
      (⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆).map A.subtype
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.commutator_le_self A),
      Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hAsup : A = A' ⊔ Z' := by
    have hsupA : (A'.subgroupOf A) ⊔ (Z'.subgroupOf A) = ⊤ := by
      have h := congrArg (Subgroup.comap q) hmapq
      rw [Subgroup.comap_map_eq, Subgroup.comap_top, hkerq] at h
      rwa [← hA'sub] at h
    have h := congrArg (Subgroup.map A.subtype) hsupA
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hA'A,
      Subgroup.map_subgroupOf_eq_of_le hZA, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  have hperf : ⁅A', A'⁆ = A' :=
    commutator_perfect_of_central (F := A) (Z := Z') hZc (le_of_eq hAsup)
  have hZ₁A' : A' ⊓ Z' ≤ A' := inf_le_left
  have hZ₁c : ∀ z ∈ A' ⊓ Z', ∀ a ∈ A', z * a = a * z := fun z hz a ha =>
    hZc z hz.2 a (hA'A ha)
  haveI hZ₁n : ((A' ⊓ Z').subgroupOf A').Normal :=
    Subgroup.normal_of_le_center fun z hz => by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hZ₁c (z : LGL 2 W) (Subgroup.mem_subgroupOf.mp hz)
        (w : LGL 2 W) w.2).symm
  let θ' : ↥A' →* X := θ.comp (Subgroup.inclusion hA'A)
  have hθ'k : ∀ a : ↥A', θ' a = 1 ↔ (a : LGL 2 W) ∈ A' ⊓ Z' := by
    intro a
    have h1 : θ' a = 1 ↔ (a : LGL 2 W) ∈ Z' := hθk (Subgroup.inclusion hA'A a)
    rw [h1]
    exact ⟨fun hz => ⟨a.2, hz⟩, fun h => h.2⟩
  have hθ's : Function.Surjective θ' := by
    intro x
    obtain ⟨a, ha⟩ := hθs x
    have hmem : (a : LGL 2 W) ∈ A' ⊔ Z' := (le_of_eq hAsup) a.2
    obtain ⟨a', ha', z, hz, haz⟩ :=
      (w183K3Img2_mem_sup_of_comm (fun s hs c hc => (hZc c hc s (hA'A hs)).symm)).mp hmem
    have ha'A : a' ∈ A := hA'A ha'
    have hzA : z ∈ A := hZA hz
    have hae : (⟨a, a.2⟩ : ↥A) = ⟨a', ha'A⟩ * ⟨z, hzA⟩ :=
      Subtype.ext (by show (a : LGL 2 W) = a' * z; exact haz.symm)
    refine ⟨⟨a', ha'⟩, ?_⟩
    have h1 : θ' ⟨a', ha'⟩ = θ ⟨a', ha'A⟩ := rfl
    rw [h1]
    have h2 : θ ⟨a, a.2⟩ = θ ⟨a', ha'A⟩ := by
      have h3 := congrArg θ hae
      rwa [map_mul, (hθk ⟨z, hzA⟩).2 hz, mul_one] at h3
    rw [← h2]
    exact ha
  have hkerθ' : θ'.ker = (A' ⊓ Z').subgroupOf A' := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hθ'k a
  have hsimple : IsSimpleGroup (↥A' ⧸ (A' ⊓ Z').subgroupOf A') := by
    let e' : (↥A' ⧸ (A' ⊓ Z').subgroupOf A') ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hkerθ'.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ' hθ's)
    exact (MulEquiv.isSimpleGroup_congr e').mpr hXs
  have hquasi := isQuasisimple_of_central_simple_quot (F := A') (Z := A' ⊓ Z')
    hperf hZ₁A' hZ₁c hsimple
  refine ⟨?_, ?_, ?_⟩
  · exact hAsup
  · exact hquasi.1
  · exact hquasi.2

private theorem w183K3Img2_le_normalizer_of_comm {W : Type} [Group W] {A B : Subgroup W}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.normalizer (A : Set W) := by
  refine Subgroup.le_normalizer_iff.mpr fun b hb a ha => ?_
  have h1 : b * a * b⁻¹ = a := by rw [← h a ha b hb]; group
  rwa [h1]

theorem w183K3Img2_map_subgroupOf_eq_bot_or_le {W : Type} [Group W] {A B Z : Subgroup W}
    {X : Type} [Group X] (hBA : B ≤ A) (hZB : Z ≤ B)
    (θ : ↥A →* X) (hθs : Function.Surjective θ)
    (hθk : ∀ a : ↥A, θ a = 1 ↔ (a : W) ∈ Z)
    (hXs : IsSimpleGroup X) (hBn : (B.subgroupOf A).Normal) :
    (B.subgroupOf A).map θ = ⊥ ∨ A ≤ B := by
  haveI := hBn
  haveI : ((B.subgroupOf A).map θ).Normal := hBn.map θ hθs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((B.subgroupOf A).map θ) with hbot | htop
  · exact Or.inl hbot
  · right
    intro a ha
    have hmem : θ (⟨a, ha⟩ : ↥A) ∈ (B.subgroupOf A).map θ := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hmem
    have hbval : (b : W) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hker : θ (⟨a, ha⟩ * b⁻¹) = 1 := by rw [map_mul, map_inv, hbeq]; group
    have hmemZ : ((⟨a, ha⟩ * b⁻¹ : ↥A) : W) ∈ Z := (hθk _).1 hker
    have ha' : a = ((⟨a, ha⟩ * b⁻¹ : ↥A) : W) * (b : W) := by
      change a = a * (b : W)⁻¹ * (b : W); group
    rw [ha']
    exact B.mul_mem (hZB hmemZ) hbval

noncomputable def w183K3Img2_center_quot_iso {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {A Z' : Subgroup (LGL 2 W)} {X : Type} [Group X]
    (hZc : ∀ z ∈ Z', ∀ a ∈ A, z * a = a * z) (hZA : Z' ≤ A)
    (hA : A = ⁅A, A⁆ ⊔ Z') (hC : quasiCentre ⁅A, A⁆ = ⁅A, A⁆ ⊓ Z')
    (θ : ↥A →* X) (hθs : Function.Surjective θ)
    (hθk : ∀ a : ↥A, θ a = 1 ↔ (a : LGL 2 W) ∈ Z') :
    X ≃* (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) := by
  classical
  set A' : Subgroup (LGL 2 W) := ⁅A, A⁆ with hA'def
  have hA'A : A' ≤ A := Subgroup.commutator_le_self A
  haveI hZ₁n : ((A' ⊓ Z').subgroupOf A').Normal :=
    Subgroup.normal_of_le_center fun z hz => by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hZc (z : LGL 2 W) (Subgroup.mem_subgroupOf.mp hz).2
        (w : LGL 2 W) (hA'A w.2)).symm
  haveI hZn : (Z'.subgroupOf A).Normal :=
    Subgroup.normal_of_le_center fun z hz => by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hZc (z : LGL 2 W) (Subgroup.mem_subgroupOf.mp hz)
        (w : LGL 2 W) w.2).symm
  let θ' : ↥A' →* X := θ.comp (Subgroup.inclusion hA'A)
  have hθ's : Function.Surjective θ' := by
    intro x
    obtain ⟨a, ha⟩ := hθs x
    have hmem : (a : LGL 2 W) ∈ A' ⊔ Z' := (le_of_eq hA) a.2
    obtain ⟨a', ha', z, hz, haz⟩ :=
      (w183K3Img2_mem_sup_of_comm (fun s hs c hc => (hZc c hc s (hA'A hs)).symm)).mp hmem
    have ha'A : a' ∈ A := hA'A ha'
    have hzA : z ∈ A := hZA hz
    have hae : (⟨a, a.2⟩ : ↥A) = ⟨a', ha'A⟩ * ⟨z, hzA⟩ :=
      Subtype.ext (by show (a : LGL 2 W) = a' * z; exact haz.symm)
    refine ⟨⟨a', ha'⟩, ?_⟩
    have h1 : θ' ⟨a', ha'⟩ = θ ⟨a', ha'A⟩ := rfl
    rw [h1]
    have h2 : θ ⟨a, a.2⟩ = θ ⟨a', ha'A⟩ := by
      have h3 := congrArg θ hae
      rwa [map_mul, (hθk ⟨z, hzA⟩).2 hz, mul_one] at h3
    rw [← h2]
    exact ha
  have hθ'k : ∀ a : ↥A', θ' a = 1 ↔ (a : LGL 2 W) ∈ A' ⊓ Z' := by
    intro a
    have h1 : θ' a = 1 ↔ (a : LGL 2 W) ∈ Z' := hθk (Subgroup.inclusion hA'A a)
    rw [h1]
    exact ⟨fun hz => ⟨a.2, hz⟩, fun h => h.2⟩
  have hkerθ' : θ'.ker = (A' ⊓ Z').subgroupOf A' := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hθ'k a
  have hcenter : (A' ⊓ Z').subgroupOf A' = Subgroup.center ↥A' := by
    apply Subgroup.map_injective A'.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    exact hC.symm
  exact (QuotientGroup.quotientKerEquivOfSurjective θ' hθ's).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkerθ').trans
      (QuotientGroup.quotientMulEquivOfEq hcenter))

theorem w183K3Img2_commutator_sup_sup_le {W : Type} [Group W] {A B Z : Subgroup W}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAZ : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a)
    (hBZ : ∀ b ∈ B, ∀ z ∈ Z, b * z = z * b)
    (hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) :
    ⁅A ⊔ B ⊔ Z, A ⊔ B ⊔ Z⁆ ≤ A ⊔ B := by
  let T : Subgroup W := A ⊔ B ⊔ Z
  have hAT : A ≤ T := le_trans le_sup_left le_sup_left
  have hBT : B ≤ T := le_trans le_sup_right le_sup_left
  have hZT : Z ≤ T := le_sup_right
  have hT_A : T ≤ Subgroup.normalizer (A : Set W) := by
    rw [show T = A ⊔ B ⊔ Z from rfl]
    exact sup_le (sup_le Subgroup.le_normalizer
      (w183K3Img2_le_normalizer_of_comm hAB))
      (w183K3Img2_le_normalizer_of_comm hAZ)
  have hT_B : T ≤ Subgroup.normalizer (B : Set W) := by
    rw [show T = A ⊔ B ⊔ Z from rfl]
    exact sup_le (sup_le
      (w183K3Img2_le_normalizer_of_comm fun b hb a ha => (hAB a ha b hb).symm)
      Subgroup.le_normalizer)
      (w183K3Img2_le_normalizer_of_comm hBZ)
  have hT_Z : T ≤ Subgroup.normalizer (Z : Set W) := by
    rw [show T = A ⊔ B ⊔ Z from rfl]
    exact sup_le (sup_le
      (w183K3Img2_le_normalizer_of_comm fun z hz a ha => (hAZ a ha z hz).symm)
      (w183K3Img2_le_normalizer_of_comm fun z hz b hb => (hBZ b hb z hz).symm))
      Subgroup.le_normalizer
  haveI hAn : (A.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAT).mpr hT_A
  haveI hBn : (B.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBT).mpr hT_B
  haveI hZn : (Z.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZT).mpr hT_Z
  haveI hABn : ((A.subgroupOf T) ⊔ (B.subgroupOf T)).Normal := inferInstance
  have hTcentZ : T ≤ Subgroup.centralizer (Z : Set W) := by
    rw [show T = A ⊔ B ⊔ Z from rfl]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hAZ a ha z hz).symm
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hBZ b hb z hz).symm
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro z' hz'
      exact (hZZ z hz z' hz').symm
  have hZ'cent : Z.subgroupOf T ≤ Subgroup.center ↥T := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hTcentZ t.2) (z : W)
      (Subgroup.mem_subgroupOf.mp hz)).symm
  have hATZ : (A.subgroupOf T) ⊔ (B.subgroupOf T) ⊔ (Z.subgroupOf T) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAT hBT, ← Subgroup.subgroupOf_sup (sup_le hAT hBT) hZT,
      show A ⊔ B ⊔ Z = T from rfl, Subgroup.subgroupOf_self]
  have hZtop : ⁅Z.subgroupOf T, (⊤ : Subgroup ↥T)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hZ'cent.trans (Subgroup.center_le_centralizer _))
  have hABZ : ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T), Z.subgroupOf T⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hZ'cent.trans (Subgroup.center_le_centralizer _))
  have hmain : ⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆ ≤
      (A.subgroupOf T) ⊔ (B.subgroupOf T) := by
    calc ⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆
        = ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T) ⊔ (Z.subgroupOf T), ⊤⁆ := by rw [hATZ]
      _ = ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T), ⊤⁆ ⊔ ⁅Z.subgroupOf T, ⊤⁆ :=
          Subgroup.commutator_sup_right _ _ ⊤
      _ = ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T), ⊤⁆ := by rw [hZtop, sup_bot_eq]
      _ = ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T),
            (A.subgroupOf T) ⊔ (B.subgroupOf T) ⊔ (Z.subgroupOf T)⁆ := by rw [hATZ]
      _ = ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T), (A.subgroupOf T) ⊔ (B.subgroupOf T)⁆ ⊔
            ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T), Z.subgroupOf T⁆ :=
          Subgroup.commutator_sup_left _ _ _
      _ = ⁅(A.subgroupOf T) ⊔ (B.subgroupOf T), (A.subgroupOf T) ⊔ (B.subgroupOf T)⁆ := by
          rw [hABZ, sup_bot_eq]
      _ ≤ (A.subgroupOf T) ⊔ (B.subgroupOf T) :=
          Subgroup.commutator_le_right _ (A.subgroupOf T ⊔ B.subgroupOf T)
  have hmap : ⁅T, T⁆ ≤ A ⊔ B := by
    have h := Subgroup.map_mono (f := T.subtype) hmain
    rw [Subgroup.map_commutator, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hAT, Subgroup.map_subgroupOf_eq_of_le hBT,
      Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  simpa only [T] using hmap

end CFSG.LocalAnalysis.WeakClosure81

end
