module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp

import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWKer
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWLift
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWU3
import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoModel
public import CFSG.Quasithin.Background.HSU3Borel
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

private theorem isSylowTwoOf_sup_s
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) : IsSylowTwoOf S (L1 ⊔ S) := by
  have hF := hI.hF
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hI.hSB (Or.inr (Or.inl h1))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
    le_antisymm (sup_le le_sup_left (hS1.le.trans (sup_le (inf_le_right.trans le_sup_left)
      le_sup_right))) (sup_le le_sup_left (hQ1S.trans le_sup_right))
  rw [hsup1]
  exact isSylowTwoOf_sup_pCoreOf hF.1 hS1

private theorem chiefHom_ker_le_q1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {U L N : Subgroup G} (hUH : U ≤ L1 ⊔ S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k) :
    ∀ g : ↥(L1 ⊔ S), Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) g = 1 → (g : G) ∈ Q1 L1 L2 S := by
  intro g hg
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hmem := (Ch3z.chiefHom_eq_one_iff hHL hHN hNL g).mp hg
  exact Str86AbHyp.mem_q1_of_chiefFactor_natural hI hUH hstep hE hnat g.2 hmem.2.2

private theorem isPGroup_ker_chiefHom
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {U L N : Subgroup G} (hUH : U ≤ L1 ⊔ S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k) :
    IsPGroup 2 (Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1)).ker := by
  let f := Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
    (D14.le_normalizer_of_isNormalIn hstep.1)
  let φ : f.ker →* ↥(Q1 L1 L2 S) :=
    ((L1 ⊔ S).subtype.comp f.ker.subtype).codRestrict _ fun x =>
      chiefHom_ker_le_q1 hI hUH hstep hE hnat x.1 x.2
  refine (pCoreOf_isPGroup 2 (P1 L1 L2 S)).of_injective φ ?_
  intro a b hab
  have h : ((φ a : ↥(Q1 L1 L2 S)) : G) = ((φ b : ↥(Q1 L1 L2 S)) : G) :=
    congrArg (fun x : ↥(Q1 L1 L2 S) => (x : G)) hab
  exact Subtype.ext (Subtype.ext h)

private theorem exists_su3Anti_model_equiv {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {k : ℕ} (hk : 2 ≤ k) (h : BinaryNaturalSU3 H ⊤ ⊥ k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = (2 ^ k) ^ 2 ∧
      ∃ (Φ : V ≃* Multiplicative (Fin 3 → K)) (e : H ≃* ↥(su3Anti K k)),
        ∀ (x : H) (v : V),
          Φ ((x : MulAut V) v) =
            Multiplicative.ofAdd ((((e x : ↥(su3Anti K k)) : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ v).toAdd) := by
  classical
  obtain ⟨K, hKf, hKfin, hKchar, hKcard, Φ, ρ, hρsurj, hΦ⟩ :=
    binaryNaturalSU3_su3Anti_model (V := V) hk h
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    ext v
    have h1 := hΦ x v
    rw [hx] at h1
    have h2 : Φ ((x : MulAut V) v) = Φ v := by simpa using h1
    simpa using Φ.injective h2
  let e : H ≃* ↥(su3Anti K k) := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  refine ⟨K, hKf, hKfin, hKchar, hKcard, Φ, e, ?_⟩
  intro x v
  rw [show e x = ρ x from rfl]
  exact hΦ x v

private theorem mem_map_iff_of_ker_le {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) {S Q : Subgroup X} (hker : f.ker ≤ Q) (hQ : Q ≤ S) (x : X) :
    f x ∈ S.map f ↔ x ∈ S := by
  constructor
  · intro hx
    obtain ⟨s, hs, hfs⟩ := Subgroup.mem_map.mp hx
    have hx' : x * s⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfs, mul_inv_cancel]
    have hxS : x * s⁻¹ ∈ S := hQ (hker hx')
    have h1 : x = (x * s⁻¹) * s := by group
    rw [h1]
    exact S.mul_mem hxS hs
  · intro hx
    exact Subgroup.mem_map_of_mem f hx

private theorem mem_normalizer_map_iff_of_preimage {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) {S : Subgroup X} (hpre : ∀ x : X, f x ∈ S.map f ↔ x ∈ S) (g : X) :
    g ∈ Subgroup.normalizer (S : Set X) ↔
      f g ∈ Subgroup.normalizer (S.map f : Set Y) := by
  constructor
  · intro hg
    have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set X) :=
      (Subgroup.normalizer (S : Set X)).inv_mem hg
    rw [Subgroup.mem_normalizer_iff] at hg hginv ⊢
    intro t
    constructor
    · intro ht
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
      have h := Subgroup.mem_map_of_mem f ((hg s).mp hs)
      simpa only [map_mul, map_inv, inv_inv] using h
    · intro ht
      obtain ⟨s, hs, hfs⟩ := Subgroup.mem_map.mp ht
      have h := Subgroup.mem_map_of_mem f ((hginv s).mp hs)
      have h' : (f g)⁻¹ * f s * f g ∈ S.map f := by
        simpa only [map_mul, map_inv, inv_inv] using h
      rw [hfs] at h'
      convert h' using 2 <;> group
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro s
    constructor
    · intro hs
      have h := (hg (f s)).mp (Subgroup.mem_map_of_mem f hs)
      have h2 : f (g * s * g⁻¹) ∈ S.map f := by
        simpa only [map_mul, map_inv, inv_inv] using h
      exact (hpre (g * s * g⁻¹)).mp h2
    · intro hs
      have h : f (g * s * g⁻¹) ∈ S.map f := Subgroup.mem_map_of_mem f hs
      have h2 : f g * f s * (f g)⁻¹ ∈ S.map f := by
        simpa only [map_mul, map_inv, inv_inv] using h
      exact (hpre s).mp ((hg (f s)).mpr h2)

private theorem mem_normalizer_subgroupOf_iff {X : Type*} [Group X] {S H : Subgroup X}
    (hS : S ≤ H) {g : X} (hgH : g ∈ H) :
    (⟨g, hgH⟩ : ↥H) ∈ Subgroup.normalizer (S.subgroupOf H : Set ↥H) ↔
      g ∈ Subgroup.normalizer (S : Set X) := by
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro x
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mp ((hg ⟨x, hS hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx))
    · intro hx
      have hxH : x ∈ H := by
        have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [← h1]
        exact H.mul_mem (H.mul_mem (H.inv_mem hgH) (hS hx)) hgH
      exact (hg ⟨x, hxH⟩).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hx))
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro u
    constructor
    · intro hu
      exact Subgroup.mem_subgroupOf.mpr ((hg (u : X)).mp (Subgroup.mem_subgroupOf.mp hu))
    · intro hu
      exact Subgroup.mem_subgroupOf.mpr ((hg (u : X)).mpr (Subgroup.mem_subgroupOf.mp hu))

private theorem mem_normalizer_conj_map {X : Type*} [Group X] {P Q : Subgroup X} {c x : X}
    (hP : P = Q.map (MulAut.conj c).toMonoidHom)
    (hx : x ∈ Subgroup.normalizer (Q : Set X)) :
    c * x * c⁻¹ ∈ Subgroup.normalizer (P : Set X) := by
  have hmap := Subgroup.map_equiv_normalizer_eq Q (MulAut.conj c)
  rw [hP, ← hmap]
  simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hx

private theorem not_mem_normalizer_conj_map {X : Type*} [Group X] {P Q : Subgroup X} {c y : X}
    (hP : P = Q.map (MulAut.conj c).toMonoidHom)
    (hy : y ∉ Subgroup.normalizer (Q : Set X)) :
    c * y * c⁻¹ ∉ Subgroup.normalizer (P : Set X) := by
  intro hcy
  apply hy
  have hmap := Subgroup.map_equiv_normalizer_eq Q (MulAut.conj c)
  rw [hP, ← hmap] at hcy
  have hcy' : (MulAut.conj c) y ∈
      (Subgroup.normalizer (Q : Set X)).map (MulAut.conj c).toMonoidHom := by
    simpa [MulAut.conj_apply] using hcy
  exact (Subgroup.mem_map_iff_mem (MulAut.conj c).injective).mp hcy'

private theorem eq_one_of_model_fixed {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    {V : Type} [Group V] [Finite V] {A : Subgroup (MulAut V)}
    (Φ : V ≃* Multiplicative (Fin 3 → K)) (e : A ≃* ↥(su3Anti K k))
    (hΦ : ∀ (x : A) (v : V), Φ ((x : MulAut V) v) =
      Multiplicative.ofAdd ((((e x : ↥(su3Anti K k)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ v).toAdd))
    {g : A} {w : ↥(su3Anti K k)} (hw : e g = w)
    (hfp : ∀ v : Fin 3 → K,
      (((w : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v →
        v = 0)
    (v : V) (hv : (g : MulAut V) v = v) : v = 1 := by
  have h1 : Φ ((g : MulAut V) v) = Φ v := by rw [hv]
  have h2 := hΦ g v
  rw [h1, hw] at h2
  have h3 : (((w : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (Φ v).toAdd = (Φ v).toAdd := by
    have := congrArg Multiplicative.toAdd h2
    simpa using this.symm
  have h4 : (Φ v).toAdd = 0 := hfp _ h3
  have h5 : Φ v = 1 := by
    calc Φ v = Multiplicative.ofAdd (Φ v).toAdd := rfl
      _ = Multiplicative.ofAdd 0 := by rw [h4]
      _ = 1 := rfl
  exact Φ.injective (by simpa using h5)

private theorem mem_L_of_chiefHom_fixed {H U L N : Subgroup G}
    (hstep : IsChiefStep H U L N) (hUH : U ≤ H) {g : G} (hg : g ∈ H)
    (hfix : ∀ v : ↥(Ch3z.chiefMod L N),
      ((Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1)) ⟨g, hg⟩ : MulAut _) v = v → v = 1) :
    ∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ L → x ∈ L := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  intro x hxN hxL
  have hfix' : ((Ch3z.chiefHom hHL hHN) ⟨g, hg⟩ : MulAut _)
      (Ch3z.chiefIota hNL ⟨x, hxN⟩) = Ch3z.chiefIota hNL ⟨x, hxN⟩ := by
    simpa [Ch3z.chiefHom] using
      (Ch3z.chiefPsi_fix hHL hHN hNL hxN ⟨g, hg⟩ hxL)
  exact (Ch3z.chiefIota_eq_one_iff hNL ⟨x, hxN⟩).mp (hfix _ hfix')

private theorem fixedPointFree_on_chiefMod {H U L N : Subgroup G}
    (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (Φ : ↥(Ch3z.chiefMod L N) ≃* Multiplicative (Fin 3 → K))
    (e : ↥(Ch3z.chiefAut H L N) ≃* ↥(su3Anti K k))
    (hΦ : ∀ (x : ↥(Ch3z.chiefAut H L N)) (v : ↥(Ch3z.chiefMod L N)),
      Φ ((x : MulAut _) v) =
        Multiplicative.ofAdd ((((e x : ↥(su3Anti K k)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ v).toAdd))
    {g : G} (hg : g ∈ H) {w : ↥(su3Anti K k)}
    (hw : e (Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) ⟨g, hg⟩) = w)
    (hfp : ∀ v : Fin 3 → K,
      (((w : ↥(su3Anti K k)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0) :
    ∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ L → x ∈ L := by
  have hfix : ∀ v : ↥(Ch3z.chiefMod L N),
      ((Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1)) ⟨g, hg⟩ :
          MulAut ↥(Ch3z.chiefMod L N)) v = v → v = 1 := by
    intro v hv
    exact eq_one_of_model_fixed (V := ↥(Ch3z.chiefMod L N))
      Φ e hΦ hw hfp v hv
  exact mem_L_of_chiefHom_fixed hstep hUH hg hfix

private theorem fixedPointFree_conj {K : Type} [Field K] {n : ℕ} (c w : GL (Fin n) K)
    (h : ∀ v : Fin n → K,
      (((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v → v = 0)) :
    ∀ v : Fin n → K,
      (((c * w * c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v → v = 0) := by
  intro v hv
  have hmat : (((c * w * c⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      ((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    simp only [Units.val_mul]
  rw [hmat] at hv
  have hv1 : ((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) = v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
    exact hv
  have hv2 : ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    have h1 := congrArg (fun z =>
      (((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z)) hv1
    rw [Matrix.mulVec_mulVec] at h1
    have hcc : (((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hcc, Matrix.one_mulVec] at h1
    exact h1
  have hv3 : (((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0 := h _ hv2
  rw [hv3, Matrix.mulVec_zero, Matrix.mulVec_zero] at hv1
  simpa using hv1.symm

private theorem one_le_k_of_natCard_eq_sq {K : Type} [Field K] [Finite K] {k : ℕ}
    (hK : Nat.card K = (2 ^ k) ^ 2) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    have h2 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    simp only [pow_zero, one_pow, one_mul] at hK
    omega
  · exact hk

private theorem exists_sylow_conj_standard {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : ℕ} (hK : Nat.card K = (2 ^ k) ^ 2)
    {P : Subgroup ↥(su3Anti K k)} (hP : IsSylowIn 2 P ⊤) :
    ∃ c : ↥(su3Anti K k), P =
      ((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)).map
        (MulAut.conj c).toMonoidHom := by
  have hk1 : 1 ≤ k := one_le_k_of_natCard_eq_sq hK
  have huj : IsSylowIn 2 (CFSG.Quasithin.H.SU3.ujSub k K) (su3Anti K k) :=
    isSylowIn_su3Anti_ujSub (K := K) (k := k) hk1 hK
  have htop : (⊤ : Subgroup ↥(su3Anti K k)).map (su3Anti K k).subtype = su3Anti K k := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hujB : IsSylowIn 2
      ((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)) ⊤ := by
    have hrew : IsSylowIn 2
        (((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)).map
          (su3Anti K k).subtype) (((⊤ : Subgroup ↥(su3Anti K k))).map
            (su3Anti K k).subtype) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr huj.1, htop]
      exact huj
    exact (CFSG.Quasithin.E1.isSylowIn_map_of_injective
      (f := (su3Anti K k).subtype) (su3Anti K k).subtype_injective).mp hrew
  obtain ⟨c, -, hc⟩ := Ch1Sec3.exists_conj_of_isSylowIn hujB hP
  refine ⟨c, ?_⟩
  ext x
  rw [Subgroup.mem_map_equiv]
  simpa [MulAut.conj_symm_apply] using hc x

private theorem exists_standard_torus_data {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : ℕ} (hK : Nat.card K = (2 ^ k) ^ 2) {n d : ℕ} (hn : Odd n)
    (hnq : n ∣ 2 ^ k + 1) (hd : ¬ n ∣ d) :
    ∃ w y : ↥(su3Anti K k),
      w ∈ Subgroup.normalizer
        (((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)) :
          Set ↥(su3Anti K k)) ∧
      w ^ n = 1 ∧
      (∀ v : Fin 3 → K,
        (((w ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0) ∧
      Odd (orderOf y) ∧ Commute y w ∧
      y ∉ Subgroup.normalizer
        (((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)) :
          Set ↥(su3Anti K k)) := by
  classical
  have hk1 : 1 ≤ k := one_le_k_of_natCard_eq_sq hK
  have huj : IsSylowIn 2 (CFSG.Quasithin.H.SU3.ujSub k K) (su3Anti K k) :=
    isSylowIn_su3Anti_ujSub (K := K) (k := k) hk1 hK
  obtain ⟨w, y, hwL, hwN, hwn, hwfp, hyL, hy3, hyw, hyN⟩ :=
    exists_su3Anti_torus_and_block (K := K) (k := k) hK (n := n) (d := d) hn hnq hd
  let wB : ↥(su3Anti K k) := ⟨w, hwL⟩
  let yB : ↥(su3Anti K k) := ⟨y, hyL⟩
  have hwNB : wB ∈ Subgroup.normalizer
      ((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k) :
        Set ↥(su3Anti K k)) :=
    (mem_normalizer_subgroupOf_iff (X := GL (Fin 3) K)
      (S := CFSG.Quasithin.H.SU3.ujSub k K) (H := su3Anti K k) huj.1 wB.2).mpr
      (by simpa [wB] using hwN)
  have hyNB : yB ∉ Subgroup.normalizer
      ((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k) :
        Set ↥(su3Anti K k)) := by
    intro hy
    exact hyN (by
      simpa [yB] using (mem_normalizer_subgroupOf_iff (X := GL (Fin 3) K)
        (S := CFSG.Quasithin.H.SU3.ujSub k K) (H := su3Anti K k) huj.1 yB.2).mp hy)
  have hwnB : wB ^ n = 1 := by
    apply Subtype.ext
    simpa [wB] using hwn
  have hy3B : yB ^ 3 = 1 := by
    apply Subtype.ext
    simpa [yB] using hy3
  have hyodd : Odd (orderOf yB) :=
    Odd.of_dvd_nat (by norm_num : Odd 3) (orderOf_dvd_of_pow_eq_one hy3B)
  have hywB : Commute yB wB := Subtype.ext hyw
  have hwfpB : ∀ v : Fin 3 → K,
      (((wB ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0 := by
    intro v hv
    have h : w ^ d = ((wB ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) := by
      rw [Subgroup.coe_pow]
    exact hwfp v (by rwa [← h] at hv)
  exact ⟨wB, yB, hwNB, hwnB, hwfpB, hyodd, hywB, hyNB⟩

private theorem conj_fixedPointFree {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    {c w : ↥(su3Anti K k)} {d : ℕ}
    (hwfp : ∀ v : Fin 3 → K,
      (((w ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0) :
    ∀ v : Fin 3 → K,
      ((((c * w * c⁻¹) ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0 := by
  intro v hv
  have hcoe : (((c * w * c⁻¹) ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) =
      (c : GL (Fin 3) K) * w ^ d * (c : GL (Fin 3) K)⁻¹ := by
    rw [Subgroup.coe_pow]
    have h1 : (((c * w * c⁻¹) : ↥(su3Anti K k)) : GL (Fin 3) K) =
        (c : GL (Fin 3) K) * w * (c : GL (Fin 3) K)⁻¹ := rfl
    rw [h1, conj_pow]
  have hmat : ((((c * w * c⁻¹) ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((w ^ d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((((c : GL (Fin 3) K))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hcoe]
    simp only [Units.val_mul]
  exact fixedPointFree_conj (c : GL (Fin 3) K) (w ^ d) hwfp v (by rwa [hmat] at hv)

private theorem conj_torus_data {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    {c w y : ↥(su3Anti K k)} {n d : ℕ} (hwn : w ^ n = 1)
    (hwfp : ∀ v : Fin 3 → K,
      (((w ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0)
    (hyodd : Odd (orderOf y)) (hyw : Commute y w)
    (hwN : w ∈ Subgroup.normalizer
      (((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)) :
        Set ↥(su3Anti K k)))
    (hyNot : y ∉ Subgroup.normalizer
      (((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)) :
        Set ↥(su3Anti K k))) :
    ∃ w' y' : ↥(su3Anti K k),
      w' ∈ Subgroup.normalizer
        ((((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)).map
          (MulAut.conj c).toMonoidHom) : Set ↥(su3Anti K k)) ∧
      w' ^ n = 1 ∧
      (∀ v : Fin 3 → K,
        (((w' ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0) ∧
      Odd (orderOf y') ∧ Commute y' w' ∧
      y' ∉ Subgroup.normalizer
        ((((CFSG.Quasithin.H.SU3.ujSub k K).subgroupOf (su3Anti K k)).map
          (MulAut.conj c).toMonoidHom) : Set ↥(su3Anti K k)) := by
  let w' : ↥(su3Anti K k) := c * w * c⁻¹
  let y' : ↥(su3Anti K k) := c * y * c⁻¹
  have hwnB : w' ^ n = 1 := by
    rw [show w' = MulAut.conj c w by simp [w', MulAut.conj_apply], ← map_pow, hwn, map_one]
  have hy'odd : Odd (orderOf y') := by
    have h : orderOf y' = orderOf y := by
      rw [show y' = MulAut.conj c y by simp [y', MulAut.conj_apply], MulEquiv.orderOf_eq]
    rwa [h]
  have hyw' : Commute y' w' := by
    rw [show y' = MulAut.conj c y by simp [y', MulAut.conj_apply],
      show w' = MulAut.conj c w by simp [w', MulAut.conj_apply]]
    exact hyw.map (MulAut.conj c)
  have hw'fp : ∀ v : Fin 3 → K,
      (((w' ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0 := by
    simpa [w'] using conj_fixedPointFree (c := c) (w := w) (d := d) hwfp
  exact ⟨w', y', mem_normalizer_conj_map rfl hwN, hwnB, hw'fp, hy'odd, hyw',
    not_mem_normalizer_conj_map rfl hyNot⟩

private theorem exists_torus_and_block_of_isSylow {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : ℕ} (hK : Nat.card K = (2 ^ k) ^ 2) {n d : ℕ} (hn : Odd n)
    (hnq : n ∣ 2 ^ k + 1) (hd : ¬ n ∣ d)
    {P : Subgroup ↥(su3Anti K k)} (hP : IsSylowIn 2 P ⊤) :
    ∃ w y : ↥(su3Anti K k),
      w ∈ Subgroup.normalizer (P : Set ↥(su3Anti K k)) ∧
      w ^ n = 1 ∧
      (∀ v : Fin 3 → K,
        (((w ^ d : ↥(su3Anti K k)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0) ∧
      Odd (orderOf y) ∧ Commute y w ∧
      y ∉ Subgroup.normalizer (P : Set ↥(su3Anti K k)) := by
  obtain ⟨c, hPmap⟩ := exists_sylow_conj_standard hK hP
  obtain ⟨w, y, hwN, hwn, hwfp, hyodd, hyw, hyNot⟩ :=
    exists_standard_torus_data hK hn hnq hd
  obtain ⟨w', y', hw'N, hw'n, hw'fp, hy'odd, hyw', hy'not⟩ :=
    conj_torus_data hwn hwfp hyodd hyw hwN hyNot
  refine ⟨w', y', ?_, hw'n, hw'fp, hy'odd, hyw', ?_⟩
  · rwa [hPmap]
  · rwa [hPmap]

private theorem mem_map_chiefHom_iff
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {U L N : Subgroup G} (hUH : U ≤ L1 ⊔ S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k) :
    ∀ x : ↥(L1 ⊔ S),
      Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) x ∈
          (S.subgroupOf (L1 ⊔ S)).map
            (Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
              (D14.le_normalizer_of_isNormalIn hstep.1)) ↔
        x ∈ S.subgroupOf (L1 ⊔ S) := by
  let f := Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
    (D14.le_normalizer_of_isNormalIn hstep.1)
  have hker : f.ker ≤ (Q1 L1 L2 S).subgroupOf (L1 ⊔ S) := by
    intro g hg
    exact Subgroup.mem_subgroupOf.mpr
      (chiefHom_ker_le_q1 hI hUH hstep hE hnat g (by simpa [f] using hg))
  have hQ : (Q1 L1 L2 S).subgroupOf (L1 ⊔ S) ≤ S.subgroupOf (L1 ⊔ S) := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hI.hF.toW)
        (Subgroup.mem_subgroupOf.mp hy))
  intro x
  simpa [f] using mem_map_iff_of_ker_le f hker hQ x

private theorem exists_model_and_sylow
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {L N : Subgroup G}
    (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G))
    (hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = (2 ^ k) ^ 2 ∧
      ∃ (Φ : ↥(Ch3z.chiefMod L N) ≃* Multiplicative (Fin 3 → K))
        (eρ : ↥(Ch3z.chiefAut (L1 ⊔ S) L N) ≃* ↥(su3Anti K k))
        (T : Subgroup ↥(Ch3z.chiefAut (L1 ⊔ S) L N)),
        (∀ (x : ↥(Ch3z.chiefAut (L1 ⊔ S) L N)) (v : ↥(Ch3z.chiefMod L N)),
          Φ ((x : MulAut _) v) =
            Multiplicative.ofAdd ((((eρ x : ↥(su3Anti K k)) : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) *ᵥ (Φ v).toAdd)) ∧
        T = (S.subgroupOf (L1 ⊔ S)).map (Ch3z.chiefHom hHL hHN) ∧
        IsSylowIn 2 (T.map eρ.toMonoidHom) ⊤ := by
  classical
  letI : CommGroup ↥(Ch3z.chiefMod L N) := commGroupOfElemAbelian hE
  obtain ⟨K, hKf, hKfin, hKchar, hKcard, Φ, eρ, hΦ⟩ :=
    exists_su3Anti_model_equiv (V := ↥(Ch3z.chiefMod L N)) hI.hk hnat
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  let H : Subgroup G := L1 ⊔ S
  let f : ↥H →* ↥(Ch3z.chiefAut H L N) := Ch3z.chiefHom hHL hHN
  have hSylH : IsSylowTwoOf S H := isSylowTwoOf_sup_s hI
  have hSylIn : IsSylowIn 2 (S.subgroupOf H) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hSylH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSylH.1).symm
    · rw [Subgroup.relIndex_top_right]
      exact hSylH.2.2
  let T : Subgroup ↥(Ch3z.chiefAut H L N) := (S.subgroupOf H).map f
  have hTe : IsSylowIn 2 (T.map eρ.toMonoidHom) ⊤ := by
    have h := (CFSG.Quasithin.E1.isSylowIn_two_map_top
      (CFSG.Quasithin.Ch3z.chiefHom_surjective hHL hHN) hSylIn)
    have h' := (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv eρ).mpr (by simpa [T, f] using h)
    simpa using h'
  exact ⟨K, hKf, hKfin, hKchar, hKcard, Φ, eρ, T, hΦ, rfl, hTe⟩

private theorem exists_lift_pair {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) (hK : IsPGroup 2 f.ker)
    {p a d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {W Yv : Y}
    (hW : W ^ p ^ a = 1) (hYodd : Odd (orderOf Yv)) (hcomm : Commute Yv W) :
    ∃ ω h : X, f ω = W ∧ ω ^ p ^ a = 1 ∧ f h = Yv ∧ Odd (orderOf h) ∧
      Commute h (ω ^ d) := by
  obtain ⟨ω, hωf, hωpow⟩ := exists_lift_pow_primePow_eq_one f hf hK hp hp2 hW
  obtain ⟨h, hhf, hhodd, hhcomm⟩ :=
    exists_lift_odd_commute f hf hK hp hp2 (w := ω) hωpow (y := Yv) hYodd (by rwa [hωf])
  exact ⟨ω, h, hωf, hωpow, hhf, hhodd, hhcomm.pow_right d⟩

private theorem exists_lift_of_torus_data {X A B : Type*} [Group X] [Group A] [Group B]
    [Finite X] (f : X →* A) (hf : Function.Surjective f) (hK : IsPGroup 2 f.ker)
    (e : A ≃* B) {T : Subgroup A} {w y : B} {p a d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hwn : w ^ p ^ a = 1) (hyodd : Odd (orderOf y)) (hyw : Commute y w)
    (hwN : w ∈ Subgroup.normalizer (T.map e.toMonoidHom : Set B))
    (hyNot : y ∉ Subgroup.normalizer (T.map e.toMonoidHom : Set B)) :
    ∃ ω h : X, f ω = e.symm w ∧ ω ^ p ^ a = 1 ∧ f h = e.symm y ∧
      Odd (orderOf h) ∧ Commute h (ω ^ d) ∧
      e.symm w ∈ Subgroup.normalizer (T : Set A) ∧
      e.symm y ∉ Subgroup.normalizer (T : Set A) := by
  classical
  have hWAnorm : e.symm w ∈ Subgroup.normalizer (T : Set A) := by
    rw [← Subgroup.map_equiv_normalizer_eq T e] at hwN
    exact (Subgroup.mem_map_equiv (f := e) (K := Subgroup.normalizer (T : Set A))).mp hwN
  have hYAnot : e.symm y ∉ Subgroup.normalizer (T : Set A) := by
    intro hYA
    apply hyNot
    rw [← Subgroup.map_equiv_normalizer_eq T e]
    exact (Subgroup.mem_map_equiv (f := e) (K := Subgroup.normalizer (T : Set A))).mpr hYA
  have hWApow : (e.symm w) ^ p ^ a = 1 := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, hwn, map_one]
  have hYAcomm : Commute (e.symm y) (e.symm w) := hyw.map e.symm
  have hyoddA : Odd (orderOf (e.symm y)) := by
    have h : orderOf (e.symm y) = orderOf y := MulEquiv.orderOf_eq e.symm y
    rwa [h]
  obtain ⟨ω, h, hωf, hωpow, hhf, hhodd, hhcomm⟩ :=
    exists_lift_pair f hf hK hp hp2 hWApow hyoddA hYAcomm
  exact ⟨ω, h, hωf, hωpow, hhf, hhodd, hhcomm, hWAnorm, hYAnot⟩

private theorem not_mem_bigB_of_map_not_normalizer {L1 L2 S H : Subgroup G}
    {A : Type*} [Group A] (f : ↥H →* A) {h : G}
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hSH : S ≤ H) (hH : h ∈ H)
    (hpre : ∀ x : ↥H, f x ∈ (S.subgroupOf H).map f ↔ x ∈ S.subgroupOf H)
    (hnot : f ⟨h, hH⟩ ∉
      Subgroup.normalizer ((S.subgroupOf H).map f : Set A)) :
    h ∉ bigB L1 L2 S := by
  intro hhB
  have hhN : h ∈ Subgroup.normalizer (S : Set G) := hSB hhB
  have hhNH : (⟨h, hH⟩ : ↥H) ∈ Subgroup.normalizer (S.subgroupOf H : Set ↥H) :=
    (mem_normalizer_subgroupOf_iff hSH hH).mpr hhN
  exact hnot ((mem_normalizer_map_iff_of_preimage f hpre ⟨h, hH⟩).mp hhNH)

private theorem mem_bigB_of_lift
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {U L N : Subgroup G} (hUH : U ≤ L1 ⊔ S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {T : Subgroup ↥(Ch3z.chiefAut (L1 ⊔ S) L N)}
    (hTmap : T = (S.subgroupOf (L1 ⊔ S)).map
      (Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1)))
    {eρ : ↥(Ch3z.chiefAut (L1 ⊔ S) L N) ≃* ↥(su3Anti K k)} {w : ↥(su3Anti K k)}
    {ωH : ↥(L1 ⊔ S)}
    (hWAnorm : eρ.symm w ∈ Subgroup.normalizer (T : Set ↥(Ch3z.chiefAut (L1 ⊔ S) L N)))
    (hωf : Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) ωH = eρ.symm w) :
    (ωH : G) ∈ bigB L1 L2 S := by
  let H : Subgroup G := L1 ⊔ S
  let f : ↥H →* ↥(Ch3z.chiefAut H L N) := Ch3z.chiefHom
    (D14.le_normalizer_of_isNormalIn hstep.2.1)
    (D14.le_normalizer_of_isNormalIn hstep.1)
  have hpreT : ∀ x : ↥H, f x ∈ T ↔ x ∈ S.subgroupOf H := by
    intro x
    have h := mem_map_chiefHom_iff hI hUH hstep hE hnat x
    rw [← hTmap] at h
    simpa [f, H] using h
  have hpre : ∀ x : ↥H, f x ∈ (S.subgroupOf H).map f ↔ x ∈ S.subgroupOf H := by
    intro x
    have h := hpreT x
    rwa [hTmap] at h
  have hωNH : ωH ∈ Subgroup.normalizer (S.subgroupOf H : Set ↥H) := by
    refine (mem_normalizer_map_iff_of_preimage f hpre ωH).mpr ?_
    rw [← hTmap, hωf]
    exact hWAnorm
  have hωN : (ωH : G) ∈ Subgroup.normalizer (S : Set G) :=
    (mem_normalizer_subgroupOf_iff (le_sup_right : S ≤ H) ωH.2).mp hωNH
  have hHP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  exact str86_p1_inf_normalizer_le_bigB hI.hF.toW hI.hSB
    (Subgroup.mem_inf.mpr ⟨hHP1 ωH.2, hωN⟩)

theorem Str86AbHyp.exists_lemmaW_elements
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {U L N : Subgroup G} (hUH : U ≤ L1 ⊔ S)
    (hstep : IsChiefStep (L1 ⊔ S) U L N) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hnat : @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k)
    {p a d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpa : p ^ a ∣ 2 ^ k + 1) (hd : ¬ p ^ a ∣ d) :
    ∃ ω h : G, ω ∈ L1 ⊔ S ∧ ω ∈ bigB L1 L2 S ∧ ω ^ p ^ a = 1 ∧
      (∀ x ∈ N, ω ^ d * x * (ω ^ d)⁻¹ * x⁻¹ ∈ L → x ∈ L) ∧
      h ∈ L1 ⊔ S ∧ Odd (orderOf h) ∧ Commute h (ω ^ d) ∧ h ∉ bigB L1 L2 S := by
  classical
  let H : Subgroup G := L1 ⊔ S
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  let f : ↥H →* ↥(Ch3z.chiefAut H L N) := Ch3z.chiefHom hHL hHN
  have hf : Function.Surjective f := Ch3z.chiefHom_surjective hHL hHN
  have hKf : IsPGroup 2 f.ker := by
    simpa [f] using isPGroup_ker_chiefHom hI hUH hstep hE hnat
  letI : CommGroup ↥(Ch3z.chiefMod L N) := commGroupOfElemAbelian hE
  obtain ⟨K, hKfld, hKfin, hKchar, hKcard, Φ, eρ, T, hΦ, hTmap, hTe⟩ :=
    exists_model_and_sylow hI hHL hHN hE hnat
  letI : Field K := hKfld
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨w, y, hwN, hwn, hwfp, hyodd, hyw, hyNot⟩ :=
    exists_torus_and_block_of_isSylow (K := K) (k := k) hKcard
      ((hp.odd_of_ne_two hp2).pow) hpa hd hTe
  obtain ⟨ωH, hH, hωf, hωpow, hhf, hhodd, hhcomm, hWAnorm, hYAnot⟩ :=
    exists_lift_of_torus_data f hf hKf eρ hp hp2 hwn hyodd hyw hwN hyNot
  have hωB : (ωH : G) ∈ bigB L1 L2 S :=
    mem_bigB_of_lift hI hUH hstep hE hnat hTmap hWAnorm hωf
  have hpre : ∀ x : ↥H, f x ∈ (S.subgroupOf H).map f ↔ x ∈ S.subgroupOf H := by
    intro x
    simpa [f, H] using mem_map_chiefHom_iff hI hUH hstep hE hnat x
  have hfeq : eρ (f (ωH ^ d)) = w ^ d := by
    calc eρ (f (ωH ^ d)) = eρ ((f ωH) ^ d) := by rw [map_pow]
      _ = (eρ (f ωH)) ^ d := by rw [map_pow]
      _ = (eρ (eρ.symm w)) ^ d := by rw [hωf]
      _ = w ^ d := by rw [MulEquiv.apply_symm_apply]
  have hfree := fixedPointFree_on_chiefMod hstep hUH Φ eρ hΦ (ωH ^ d).2 hfeq hwfp
  have hhnotB : (hH : G) ∉ bigB L1 L2 S := by
    have hnot : f hH ∉ Subgroup.normalizer ((S.subgroupOf H).map f : Set _) := by
      rw [hhf, ← hTmap]
      exact hYAnot
    exact not_mem_bigB_of_map_not_normalizer f hI.hSB (le_sup_right : S ≤ H) hH.2 hpre hnot
  have hhcommd : Commute (hH : G) ((ωH : G) ^ d) := by
    have h2 : Commute (hH : G) (((ωH ^ d : ↥H) : G)) := hhcomm.map H.subtype
    simpa using h2
  refine ⟨(ωH : G), (hH : G), ωH.2, hωB, ?_, ?_, hH.2, ?_, hhcommd, hhnotB⟩
  · simpa using congrArg Subtype.val hωpow
  · intro x hxN hxL
    exact hfree x hxN (by simpa using hxL)
  · simpa using hhodd

end CFSG.Quasithin.Stroth

end
