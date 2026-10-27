module

public import CFSG.Quasithin.EmptyFaithful.T1521SL2ENorm
public import CFSG.Quasithin.EmptyFaithful.T1521SJ

public section

namespace CFSG.Quasithin.L21521E

open CFSG.PSL2Table CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Quasithin.L21521 CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

theorem exists_equiv_unipotent {G : Type} [Group G] [Finite G] {L P : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : IsPSL 2 2 n ↥L) (hP : IsSylowTwoOf P L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : ↥L ≃* PSL(2, K)), Nat.card K = 2 ^ n ∧
      ∀ x : ↥L, (x : G) ∈ P ↔ φ x ∈ unipotent K := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  let φ0 : ↥L ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 PSL(2, K) := (A4.toSylow hP).mapSurjective (f := φ0.toMonoidHom) φ0.surjective
  have hQ : (Q : Subgroup PSL(2, K)) = (P.subgroupOf L).map φ0.toMonoidHom := rfl
  let U₀ : Sylow 2 PSL(2, K) := Sylow.ofCard (unipotent K) (by
    rw [card_unipotent', hK, factorization_card_psl2 (by omega) hK])
  have hU₀ : (U₀ : Subgroup PSL(2, K)) = unipotent K := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, K) U₀ Q
  have hmem : ∀ x, x ∈ (Q : Subgroup PSL(2, K)) ↔ g⁻¹ * x * g ∈ unipotent K := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * (g * y * g⁻¹) * g ∈ _
      simpa [mul_assoc] using hy
    · intro h
      refine ⟨g⁻¹ * x * g, h, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  refine ⟨K, hKf, hKfin, φ0.trans (MulAut.conj g⁻¹), hK, fun x => ?_⟩
  have h1 : (x : G) ∈ P ↔ φ0 x ∈ (Q : Subgroup PSL(2, K)) := by
    rw [hQ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  rw [h1, hmem]
  change _ ↔ g⁻¹ * φ0 x * g⁻¹⁻¹ ∈ unipotent K
  rw [inv_inv]

section Coord

variable {G : Type} [Group G] {K : Type} [Field K] {L V : Subgroup G}

theorem coord_mem (φ : ↥L ≃* PSL(2, K)) (hφ : ∀ x : ↥L, (x : G) ∈ V ↔ φ x ∈ unipotent K) (x : K) :
    ((φ.symm (mk (unip x)) : ↥L) : G) ∈ V :=
  (hφ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact mk_unip_mem_unipotent x)

theorem coord_surj (φ : ↥L ≃* PSL(2, K)) (hφ : ∀ x : ↥L, (x : G) ∈ V ↔ φ x ∈ unipotent K)
    (hVL : V ≤ L) {y : G} (hy : y ∈ V) : ∃ x : K, ((φ.symm (mk (unip x)) : ↥L) : G) = y := by
  have h := (hφ ⟨y, hVL hy⟩).mp hy
  obtain ⟨x, hx⟩ := (mem_unipotent_iff_exists _).mp h
  refine ⟨x, ?_⟩
  rw [← hx, MulEquiv.symm_apply_apply]

theorem coord_injective (φ : ↥L ≃* PSL(2, K)) :
    Function.Injective (fun x : K => ((φ.symm (mk (unip x)) : ↥L) : G)) := by
  intro x y h
  have h1 : φ.symm (mk (unip x)) = φ.symm (mk (unip y)) := Subtype.ext h
  exact (mk_unip_eq_mk_unip_iff' x y).mp (φ.symm.injective h1)

theorem exists_twist_conj [Finite K] [CharP K 2] (φ : ↥L ≃* PSL(2, K))
    (hφ : ∀ x : ↥L, (x : G) ∈ V ↔ φ x ∈ unipotent K) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (haV : ∀ y ∈ V, a * y * a⁻¹ ∈ V) :
    ∃ (t : K) (σ : K ≃+* K), t ≠ 0 ∧ ∀ x : K,
      a * ((φ.symm (mk (unip x)) : ↥L) : G) * a⁻¹ =
        ((φ.symm (mk (unip (t * σ x))) : ↥L) : G) := by
  let α : MulAut ↥L := conjAct L ⟨a, ha⟩
  let β : MulAut PSL(2, K) := MulAut.congr φ α
  have hβz : ∀ z : PSL(2, K), β z = φ (α (φ.symm z)) := fun z => rfl
  have hα : ∀ y : ↥L, ((α y : ↥L) : G) = a * (y : G) * a⁻¹ := fun y => rfl
  have hβU : ∀ z ∈ unipotent K, β z ∈ unipotent K := by
    intro z hz
    have hz' : ((φ.symm z : ↥L) : G) ∈ V :=
      (hφ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact hz)
    have h1 : ((α (φ.symm z) : ↥L) : G) ∈ V := by
      rw [hα]
      exact haV _ hz'
    rw [hβz]
    exact (hφ _).mp h1
  obtain ⟨t, σ, ht, hts⟩ := exists_twist_of_unipotent_stable β hβU
  refine ⟨t, σ, ht, fun x => ?_⟩
  have h1 : φ.symm (β (mk (unip x))) = α (φ.symm (mk (unip x))) := by
    rw [hβz, MulEquiv.symm_apply_apply]
  rw [← hα, ← h1, hts]

end Coord

theorem centralizer_le_innerPart {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    {S L : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G)) (φ : ↥L ≃* PSL(2, K))
    (hφ : ∀ x : ↥L, (x : G) ∈ S ⊓ L ↔ φ x ∈ unipotent K) :
    S ⊓ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) ≤ innerPart1521 S L := by
  rintro s ⟨hsS, hsC⟩
  let α : MulAut ↥L := conjAct L ⟨s, hSN hsS⟩
  let β : MulAut PSL(2, K) := MulAut.congr φ α
  have hβz : ∀ z : PSL(2, K), β z = φ (α (φ.symm z)) := fun z => rfl
  have hα : ∀ y : ↥L, ((α y : ↥L) : G) = s * (y : G) * s⁻¹ := fun y => rfl
  have hfix : ∀ z ∈ unipotent K, β z = z := by
    intro z hz
    have hz' : ((φ.symm z : ↥L) : G) ∈ S ⊓ L :=
      (hφ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact hz)
    have hcomm := Subgroup.mem_centralizer_iff.mp hsC _ hz'
    have h1 : α (φ.symm z) = φ.symm z := by
      apply Subtype.ext
      rw [hα, mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    rw [hβz, h1, MulEquiv.apply_symm_apply]
  obtain ⟨u, hu, hβu⟩ := exists_eq_conj_of_forall_unipotent' β hfix
  let l : ↥L := φ.symm u
  have hlV : (l : G) ∈ S ⊓ L :=
    (hφ l).mpr (by rw [show φ l = u from MulEquiv.apply_symm_apply _ _]; exact hu)
  have hconj : ∀ y : ↥L, ((α y : ↥L) : G) = (l : G) * y * (l : G)⁻¹ := by
    intro y
    have h1 : α y = φ.symm (β (φ y)) := by
      rw [hβz, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rw [h1, hβu, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rfl
  have hcent : (l : G)⁻¹ * s ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hconj ⟨y, hy⟩
    rw [hα] at h1
    calc y * ((l : G)⁻¹ * s) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * s := by group
      _ = (l : G)⁻¹ * (s * y * s⁻¹) * s := by rw [← h1]
      _ = (l : G)⁻¹ * s * y := by group
  have hS : (l : G)⁻¹ * s ∈ S := S.mul_mem (S.inv_mem hlV.1) hsS
  have hs : s = (l : G) * ((l : G)⁻¹ * s) := by group
  rw [hs]
  exact Subgroup.mul_mem_sup hlV ⟨hS, hcent⟩

section CoordCard

variable {G : Type} [Group G] {K : Type} [Field K] {L V : Subgroup G}

theorem card_eq_of_coord (φ : ↥L ≃* PSL(2, K))
    (hφ : ∀ x : ↥L, (x : G) ∈ V ↔ φ x ∈ unipotent K) (hVL : V ≤ L) :
    Nat.card V = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : K => (⟨((φ.symm (mk (unip x)) : ↥L) : G), coord_mem φ hφ x⟩ : V)) ⟨?_, ?_⟩)).symm
  · intro x y h
    have h' : ((φ.symm (mk (unip x)) : ↥L) : G) = ((φ.symm (mk (unip y)) : ↥L) : G) :=
      congrArg (fun z : V => (z : G)) h
    exact coord_injective φ h'
  · intro y
    obtain ⟨x, hx⟩ := coord_surj φ hφ hVL y.2
    exact ⟨x, Subtype.ext hx⟩

theorem isElemAbelian_of_equiv_unipotent [CharP K 2] (φ : ↥L ≃* PSL(2, K))
    (hφ : ∀ x : ↥L, (x : G) ∈ V ↔ φ x ∈ unipotent K) (hVL : V ≤ L) : IsElemAbelian 2 V := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have ha := (hφ ⟨a.1, hVL a.2⟩).mp a.2
    have hb := (hφ ⟨b.1, hVL b.2⟩).mp b.2
    have h := unipotent_mul_comm ha hb
    rw [← map_mul, ← map_mul] at h
    have h1 := φ.injective h
    have h3 : (a.1 : G) * b.1 = b.1 * a.1 := congrArg (fun z : ↥L => (z : G)) h1
    exact Subtype.ext h3
  · have hx' := (hφ ⟨x, hVL hx⟩).mp hx
    obtain ⟨s, hs⟩ := (mem_unipotent_iff_exists _).mp hx'
    have h1 : φ ((⟨x, hVL hx⟩ : ↥L) ^ 2) = φ 1 := by
      rw [map_pow, hs, sq, ← map_mul, ← unip_add, show s + s = 0 by linear_combination s * h2,
        unip_zero, map_one, map_one]
    have h3 := φ.injective h1
    have h4 := congrArg (fun z : ↥L => (z : G)) h3
    simpa using h4

theorem eq_one_of_central_unipotent [Finite K] (h2 : (2 : K) = 0) (h4 : 4 ≤ Nat.card K)
    {z : PSL(2, K)} (hz : z ∈ unipotent K) (hc : ∀ y : PSL(2, K), y * z = z * y) : z = 1 := by
  obtain ⟨s, rfl⟩ := (mem_unipotent_iff_exists z).mp hz
  obtain ⟨a, ha⟩ := exists_unit_sq_ne_one h2 h4
  have h1 : mk (diag a) * mk (unip s) * (mk (diag a))⁻¹ = mk (unip s) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hc (mk (diag a))
  rw [mk_conj, diag_conj_unip, mk_unip_eq_mk_unip_iff'] at h1
  have h3 : ((a : K) ^ 2 - 1) * s = 0 := by linear_combination h1
  have hne : (a : K) ^ 2 - 1 ≠ 0 := fun h => ha (sub_eq_zero.mp h)
  have hs : s = 0 := (mul_eq_zero.mp h3).resolve_left hne
  rw [hs, unip_zero, map_one]

end CoordCard

end CFSG.Quasithin.L21521E
