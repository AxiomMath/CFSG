module

public import CFSG.Quasithin.MS93.S46R468FF
public import CFSG.Quasithin.MS93.S46SL2Sec

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin.MS93.S46
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type*} [Group G] {K V Z : Subgroup G}

theorem natural_comm_of_ff [Finite K] [Finite V] {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (θ : ↥K →* SL(2, F)) (hθ : Function.Surjective θ)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hZV : Z ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z) (hV2 : ∀ v ∈ V, v * v ∈ Z)
    (hker : ∀ k : ↥K, θ k = 1 → ∀ v ∈ V, ⁅(k : G), v⁆ ∈ Z)
    {X : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup 2 ((X.subgroupOf K).map θ))
    (hXc : Nat.card ((X.subgroupOf K).map θ) = Nat.card F)
    (hXV : Z.relIndex (⁅V, X⁆ ⊔ Z) ≤ Fintype.card F) :
    (∀ k ∈ K, Odd (orderOf k) → ∀ v ∈ V, ⁅k, v⁆ ∈ Z) ∨
    ∃ (N : Subgroup G) (β : ↥N →* Multiplicative (Fin 2 → F)),
      Z ≤ N ∧ N ≤ V ∧ Function.Surjective β ∧ (∀ x : ↥N, β x = 1 ↔ (x : G) ∈ Z) ∧
      (∀ k ∈ K, Odd (orderOf k) → ∀ v ∈ V, ⁅k, v⁆ ∈ N) ∧
      ∀ (k : ↥K) (u v : ↥N), (v : G) = k * u * k⁻¹ →
        Multiplicative.toAdd (β v) =
          (θ k : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β u) := by
  classical
  have hN : (Z.subgroupOf V).Normal := subgroupOf_normal_of_comm hZV hVc
  let _ : CommGroup (V ⧸ Z.subgroupOf V) :=
    { (QuotientGroup.Quotient.group (Z.subgroupOf V)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h := hVc _ (V.inv_mem b.2) _ (V.inv_mem a.2)
            have he : (((a * b)⁻¹ * (b * a) : ↥V) : G) = ⁅((b : G))⁻¹, ((a : G))⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
              group
            rw [he]
            exact h }
  have hmk : ∀ q : Additive (V ⧸ Z.subgroupOf V), ∃ v : ↥V,
      q = Additive.ofMul (v : V ⧸ Z.subgroupOf V) := fun q => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨v, by rw [hv]; rfl⟩
  have h2 : ∀ q : Additive (V ⧸ Z.subgroupOf V), 2 • q = 0 := by
    intro q
    obtain ⟨v, rfl⟩ := hmk q
    rw [← ofMul_pow, ← ofMul_one, ← QuotientGroup.mk_pow]
    congr 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
    exact hV2 _ v.2
  let _ : Module (ZMod 2) (Additive (V ⧸ Z.subgroupOf V)) := AddCommGroup.zmodModule h2
  have : Finite (Additive (V ⧸ Z.subgroupOf V)) :=
    Finite.of_surjective (fun v : ↥V => Additive.ofMul (v : V ⧸ Z.subgroupOf V)) fun q => by
      obtain ⟨v, rfl⟩ := hmk q
      exact ⟨v, rfl⟩
  let cj : ↥K → (↥V →* ↥V) := fun k =>
    { toFun := fun v => ⟨(k : G) * v * (k : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hKV k.2) v).mp v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcj : ∀ (k : ↥K) (v : ↥V), ((cj k v : ↥V) : G) = (k : G) * v * (k : G)⁻¹ :=
    fun k v => rfl
  let cq : ↥K → (V ⧸ Z.subgroupOf V →* V ⧸ Z.subgroupOf V) := fun k =>
    QuotientGroup.map (Z.subgroupOf V) (Z.subgroupOf V) (cj k) (fun z hz => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hcj]
      exact (Subgroup.mem_normalizer_iff.mp (hKZ k.2) z).mp (Subgroup.mem_subgroupOf.mp hz))
  have hcq : ∀ (k : ↥K) (v : ↥V), cq k (v : V ⧸ Z.subgroupOf V) =
      ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) := fun k v => rfl
  let act : ↥K →* (Additive (V ⧸ Z.subgroupOf V) →ₗ[ZMod 2] Additive (V ⧸ Z.subgroupOf V)) :=
    { toFun := fun k => (MonoidHom.toAdditive (cq k)).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq 1 (v : V ⧸ Z.subgroupOf V)) = Additive.ofMul _
        rw [hcq]
        congr 2
        exact Subtype.ext (by rw [hcj]; simp)
      map_mul' := fun k k' => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq (k * k') (v : V ⧸ Z.subgroupOf V)) =
          Additive.ofMul (cq k (cq k' (v : V ⧸ Z.subgroupOf V)))
        rw [hcq, hcq, hcq]
        congr 2
        exact Subtype.ext (by rw [hcj, hcj, hcj]; simp [mul_assoc]) }
  have hact : ∀ (k : ↥K) (v : ↥V), act k (Additive.ofMul (v : V ⧸ Z.subgroupOf V)) =
      Additive.ofMul ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) := fun k v => rfl
  have hZconj : ∀ w ∈ V, ∀ z ∈ Z, w * z * w⁻¹ ∈ Z := by
    intro w hw z hz
    have e : w * z * w⁻¹ = ⁅w, z⁆ * z := by rw [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (hVc w hw z (hZV hz)) hz
  have hfix : ∀ (k : ↥K) (v : ↥V), act k (Additive.ofMul (v : V ⧸ Z.subgroupOf V)) =
      Additive.ofMul (v : V ⧸ Z.subgroupOf V) ↔ ⁅(k : G), (v : G)⁆ ∈ Z := by
    intro k v
    rw [hact]
    have key : Additive.ofMul ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) =
        Additive.ofMul (v : V ⧸ Z.subgroupOf V) ↔
        ((k : G) * v * (k : G)⁻¹)⁻¹ * v ∈ Z := by
      rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv, hcj]
    rw [key]
    constructor
    · intro h
      have e : ⁅(k : G), (v : G)⁆ = (v : G) * (((k : G) * v * (k : G)⁻¹)⁻¹ * v)⁻¹ * (v : G)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact hZconj _ v.2 _ (Z.inv_mem h)
    · intro h
      have e : ((k : G) * v * (k : G)⁻¹)⁻¹ * v =
          (v : G)⁻¹ * ⁅(k : G), (v : G)⁆⁻¹ * (v : G)⁻¹⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact hZconj _ (V.inv_mem v.2) _ (Z.inv_mem h)
  have hkerle : θ.ker ≤ act.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := hmk q
    rw [Module.End.one_apply]
    exact (hfix k v).mpr (hker k hk v v.2)
  let e := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let ρ : Representation (ZMod 2) SL(2, F) (Additive (V ⧸ Z.subgroupOf V)) :=
    (QuotientGroup.lift θ.ker act hkerle).comp e.symm.toMonoidHom
  have hρ : ∀ k, ρ (θ k) = act k := by
    intro k
    have he : e.symm (θ k) = (k : ↥K ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift θ.ker act hkerle (e.symm (θ k)) = act k
    rw [he, QuotientGroup.lift_mk]
  have hoddK : ∀ k : ↥K, Odd (orderOf (k : G)) → Odd (orderOf (θ k)) := fun k hk =>
    Odd.of_dvd_nat (by rwa [Subgroup.orderOf_coe] at hk) (orderOf_map_dvd θ k)
  let π : ↥V → Additive (V ⧸ Z.subgroupOf V) := fun v => Additive.ofMul (v : V ⧸ Z.subgroupOf V)
  have hπmul : ∀ a b : ↥V, π (a * b) = π a + π b := fun a b => by
    simp only [π, QuotientGroup.mk_mul, ofMul_mul]
  have hπinv : ∀ a : ↥V, π a⁻¹ = -π a := fun a => by
    simp only [π, QuotientGroup.mk_inv, ofMul_inv]
  have hπ0 : ∀ a : ↥V, π a = 0 ↔ (a : G) ∈ Z := fun a => by
    simp only [π, ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπact : ∀ (k : ↥K) (v : ↥V), π (cj k v) = ρ (θ k) (π v) := fun k v => by
    rw [hρ, hact]
  set Xθ := (X.subgroupOf K).map θ with hXθ
  have hHV : ⁅V, X⁆ ⊔ Z ≤ V := by
    refine sup_le (Subgroup.commutator_le.mpr fun v hv x hx => ?_) hZV
    have e : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hKV (hXK hx)) _).mp (V.inv_mem hv))
  set I := ((⁅V, X⁆ ⊔ Z).subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V)) with hIdef
  have hIcard : Nat.card I = Z.relIndex (⁅V, X⁆ ⊔ Z) := by
    have h1 := Subgroup.relIndex_ker ((⁅V, X⁆ ⊔ Z).subgroupOf V)
      (QuotientGroup.mk' (Z.subgroupOf V))
    rw [QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hHV] at h1
    exact h1.symm
  have hsub : ∀ m ∈ sl2Comm ρ (Xθ : Set SL(2, F)), Additive.toMul m ∈ I := by
    intro m hm
    have hle : sl2Comm ρ (Xθ : Set SL(2, F)) ≤
        AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup I) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, ⟨x, hx, rfl⟩, q, rfl⟩
      obtain ⟨v, rfl⟩ := hmk q
      rw [SetLike.mem_coe, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, hρ,
        hact, toMul_sub, toMul_ofMul, toMul_ofMul]
      refine ⟨cj x v * v⁻¹, ?_, ?_⟩
      · have e : ((cj x v * v⁻¹ : ↥V) : G) = ⁅(v : G), (x : G)⁆⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hcj, commutatorElement_inv,
            commutatorElement_def]
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, e]
        exact Subgroup.mem_sup_left (Subgroup.inv_mem _
          (Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_subgroupOf.mp hx)))
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, div_eq_mul_inv]
    have h1 := hle hm
    rwa [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup] at h1
  have hoff : Nat.card (sl2Comm ρ (Xθ : Set SL(2, F))) ≤ Nat.card F := by
    calc Nat.card (sl2Comm ρ (Xθ : Set SL(2, F))) ≤ Nat.card I :=
          Nat.card_le_card_of_injective (fun m => ⟨Additive.toMul (m : _), hsub m m.2⟩)
            fun a b h => Subtype.ext (Additive.toMul.injective
              (congrArg (fun y : ↥I => (y : V ⧸ Z.subgroupOf V)) h))
      _ = Z.relIndex (⁅V, X⁆ ⊔ Z) := hIcard
      _ ≤ Nat.card F := by rw [Nat.card_eq_fintype_card]; exact hXV
  rcases natural_of_sl2Comm ρ hF Xθ hX hXc hoff with hall | ⟨γ, hγi, hγeq, hγr⟩
  · left
    intro k hk hodd v hv
    have h1 := hall (θ ⟨k, hk⟩) (hoddK ⟨k, hk⟩ hodd) (π ⟨v, hv⟩)
    rw [hρ] at h1
    exact (hfix ⟨k, hk⟩ ⟨v, hv⟩).mp h1
  right
  let N : Subgroup G :=
    { carrier := {g | ∃ v : ↥V, (v : G) = g ∧ π v ∈ sl2OddComm ρ}
      mul_mem' := by
        rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
        exact ⟨a * b, rfl, by rw [hπmul]; exact add_mem ha hb⟩
      one_mem' := ⟨1, rfl, by rw [(hπ0 1).mpr Z.one_mem]; exact zero_mem _⟩
      inv_mem' := by
        rintro _ ⟨a, rfl, ha⟩
        exact ⟨a⁻¹, rfl, by rw [hπinv]; exact neg_mem ha⟩ }
  have hmemN : ∀ g, g ∈ N ↔ ∃ v : ↥V, (v : G) = g ∧ π v ∈ sl2OddComm ρ := fun g => Iff.rfl
  let uN : ↥N → (Fin 2 → F) := fun x =>
    Classical.choose ((hγr _).mp (Classical.choose_spec ((hmemN x).mp x.2)).2)
  have huN : ∀ (x : ↥N) (v : ↥V), (v : G) = x → γ (uN x) = π v := by
    intro x v hv
    have h1 := Classical.choose_spec ((hγr _).mp (Classical.choose_spec ((hmemN x).mp x.2)).2)
    have h2 : Classical.choose ((hmemN x).mp x.2) = v :=
      Subtype.ext ((Classical.choose_spec ((hmemN x).mp x.2)).1.trans hv.symm)
    exact h1.trans (congrArg π h2)
  let β : ↥N →* Multiplicative (Fin 2 → F) :=
    { toFun := fun x => Multiplicative.ofAdd (uN x)
      map_one' := by
        change Multiplicative.ofAdd (uN 1) = 1
        rw [ofAdd_eq_one]
        apply hγi
        rw [huN 1 1 rfl, map_zero]
        exact (hπ0 1).mpr Z.one_mem
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (uN (x * y)) =
          Multiplicative.ofAdd (uN x) * Multiplicative.ofAdd (uN y)
        rw [← ofAdd_add]
        congr 1
        obtain ⟨a, ha, -⟩ := (hmemN x).mp x.2
        obtain ⟨b, hb, -⟩ := (hmemN y).mp y.2
        apply hγi
        rw [map_add, huN x a ha, huN y b hb, huN (x * y) (a * b) (by simp [ha, hb]), hπmul] }
  have hβ : ∀ x, β x = Multiplicative.ofAdd (uN x) := fun x => rfl
  refine ⟨N, β, fun z hz => ?_, ?_, fun y => ?_, fun x => ?_, fun k hk hodd v hv => ?_,
    fun k x y hxy => ?_⟩
  · exact ⟨⟨z, hZV hz⟩, rfl, by rw [(hπ0 ⟨z, hZV hz⟩).mpr hz]; exact zero_mem _⟩
  · rintro _ ⟨v, rfl, -⟩
    exact v.2
  · obtain ⟨v, hv⟩ := hmk (γ (Multiplicative.toAdd y))
    have hvW : π v ∈ sl2OddComm ρ := (hγr _).mpr ⟨_, hv⟩
    refine ⟨⟨v, v, rfl, hvW⟩, ?_⟩
    rw [hβ, ← ofAdd_toAdd y]
    congr 1
    apply hγi
    rw [huN _ v rfl]
    exact hv.symm
  · obtain ⟨a, ha, -⟩ := (hmemN x).mp x.2
    rw [hβ, ofAdd_eq_one, ← ha, ← hπ0, ← huN x a ha]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      exact hγi (h.trans (map_zero γ).symm)
  · refine ⟨cj ⟨k, hk⟩ ⟨v, hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hcj, commutatorElement_def]
    · rw [hπmul, hπinv, hπact, ← sub_eq_add_neg]
      exact sub_mem_sl2OddComm ρ (hoddK ⟨k, hk⟩ hodd) _
  · obtain ⟨a, ha, -⟩ := (hmemN x).mp x.2
    rw [hβ, hβ, toAdd_ofAdd, toAdd_ofAdd]
    apply hγi
    rw [hγeq, huN x a ha, huN y (cj k a) (by rw [hcj, ha, hxy, Subgroup.coe_inv]), hπact]

end CFSG.Quasithin.MS93.S46R
