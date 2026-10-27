module

public import CFSG.Monster.GMS.Leech.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement Matrix

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

def image (D : Subgroup G) : Subgroup Co1 :=
  (D.subgroupOf (Subgroup.centralizer ({z} : Set G))).map L.φ

theorem mem_image {D : Subgroup G} {x : Co1} :
    x ∈ L.image D ↔ ∃ c : Subgroup.centralizer ({z} : Set G), (c : G) ∈ D ∧ L.φ c = x := by
  unfold image
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

include L

theorem card_eq_card_image_mul (D : Subgroup G) (hD : D ≤ Subgroup.centralizer ({z} : Set G)) :
    Nat.card D = Nat.card (L.image D) * Nat.card ↥(leechQ z ⊓ D) := by
  let K : Subgroup (Subgroup.centralizer ({z} : Set G)) :=
    D.subgroupOf (Subgroup.centralizer ({z} : Set G))
  let f : K →* Co1 := L.φ.comp K.subtype
  have h1 : Nat.card D = Nat.card K :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv).symm
  have h2 : Nat.card K = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h3 : f.range = L.image D := by
    ext x
    rw [MonoidHom.mem_range, L.mem_image]
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have h4 : Nat.card f.ker = Nat.card ↥(leechQ z ⊓ D) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨((k.1 : Subgroup.centralizer ({z} : Set G)) : G),
          (L.φ_ker _).1 (MonoidHom.mem_ker.1 k.2), k.1.2⟩
        invFun := fun g => ⟨⟨⟨g.1, L.mem_centralizer g.2.1⟩, g.2.2⟩,
          MonoidHom.mem_ker.2 ((L.φ_ker _).2 g.2.1)⟩
        left_inv := fun k => rfl
        right_inv := fun g => rfl }
  rw [h1, h2, h3, h4]

theorem card_inf_iInf_centralizer_Q
    {ι : Type} [Fintype ι] (s : ι → G) (hs : ∀ i, s i ∈ leechQ z)
    (hind : LinearIndependent (ZMod 2) fun i => L.vec (s i)) :
    Nat.card ↥(leechQ z ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G)) =
      2 ^ (25 - Fintype.card ι) := by
  classical
  let M : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
    { toFun := fun w i => CFSG.Sporadic.Co1.Module.bil₀ w (L.vec (s i))
      map_add' := fun u u' => by
        funext i
        exact Leech.bil₀_add_left _ _ _
      map_smul' := fun c w => by
        funext i
        simp [CFSG.Sporadic.Co1.Module.bil₀, smul_dotProduct] }
  have hsurj : Function.Surjective M := fun ε => by
    obtain ⟨w, hw⟩ := Leech.exists_bil₀_eq hind ε
    exact ⟨w, funext hw⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker M
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fin_fun] at hrk
  have hfk : Module.finrank (ZMod 2) (LinearMap.ker M) = 24 - Fintype.card ι := by omega
  have hcardker : Nat.card (LinearMap.ker M) = 2 ^ (24 - Fintype.card ι) := by
    rw [← hfk]
    exact (FiniteField.pow_finrank_eq_natCard 2 _).symm
  have hset : {g : G | g ∈ leechQ z ∧ L.vec g ∈ (LinearMap.ker M : Set (Fin 24 → ZMod 2))} =
      ((leechQ z ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G) : Subgroup G) : Set G) := by
    ext g
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hg, hgM⟩
      refine ⟨hg, fun i => ?_⟩
      have h := congrFun (LinearMap.mem_ker.1 hgM) i
      exact commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff hg (hs i)).2 h)
    · rintro ⟨hg, h⟩
      refine ⟨hg, LinearMap.mem_ker.2 (funext fun i => ?_)⟩
      exact (L.comm_eq_one_iff hg (hs i)).1 (commutatorElement_eq_one_iff_mul_comm.2 (h i))
  have h1 := L.ncard_preimage (LinearMap.ker M : Set (Fin 24 → ZMod 2))
  rw [hset] at h1
  have h2 : Nat.card ↥(leechQ z ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G)) =
      ((leechQ z ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G) : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have h3 : Nat.card (LinearMap.ker M) = (LinearMap.ker M : Set (Fin 24 → ZMod 2)).ncard :=
    Nat.card_coe_set_eq _
  rw [h2, h1, ← h3, hcardker, ← pow_succ']
  congr 1
  omega

theorem image_inf_iInf_centralizer
    {ι : Type} [Fintype ι] (s : ι → G) (hs : ∀ i, s i ∈ leechQ z)
    (hind : LinearIndependent (ZMod 2) fun i => L.vec (s i)) :
    L.image (Subgroup.centralizer ({z} : Set G) ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G)) =
      ⨅ i, co1Stab (L.vec (s i)) := by
  ext x
  rw [L.mem_image, Subgroup.mem_iInf]
  constructor
  · rintro ⟨c, hcD, rfl⟩ i
    have hc : (c : G) * s i = s i * c :=
      Subgroup.mem_centralizer_singleton_iff.1 ((Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hcD).2) i)
    have h1 := L.vec_conj c (s i) (hs i)
    have h2 : (c : G) * s i * (c : G)⁻¹ = s i := by
      rw [hc]
      group
    rw [h2] at h1
    exact h1.symm
  · intro hx
    obtain ⟨c, rfl⟩ := L.φ_surj x
    obtain ⟨p, hp, hpa⟩ := L.exists_conj_eq (a := fun i => (c : G) * s i * (c : G)⁻¹) (b := s)
      (fun i => L.conj_mem c (hs i)) hs
      (fun i => by rw [L.vec_conj c (s i) (hs i)]; exact hx i) hind
    refine ⟨⟨p, L.mem_centralizer hp⟩ * c, Subgroup.mem_inf.2 ⟨(⟨p, L.mem_centralizer hp⟩ * c).2,
      Subgroup.mem_iInf.2 fun i => Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · have h := hpa i
      calc p * c * s i = (p * ((c : G) * s i * (c : G)⁻¹) * p⁻¹) * (p * c) := by group
        _ = s i * (p * c) := by rw [h]
    · rw [map_mul, (L.φ_ker _).2 hp, one_mul]

theorem card_inf_iInf_centralizer
    {ι : Type} [Fintype ι] (s : ι → G) (hs : ∀ i, s i ∈ leechQ z)
    (hind : LinearIndependent (ZMod 2) fun i => L.vec (s i)) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G)) =
      2 ^ (25 - Fintype.card ι) * Nat.card ↥(⨅ i, co1Stab (L.vec (s i))) := by
  have hD : Subgroup.centralizer ({z} : Set G) ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G) ≤
      Subgroup.centralizer ({z} : Set G) := inf_le_left
  have hQD : leechQ z ⊓ (Subgroup.centralizer ({z} : Set G) ⊓
      ⨅ i, Subgroup.centralizer ({s i} : Set G)) =
      leechQ z ⊓ ⨅ i, Subgroup.centralizer ({s i} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hg, -, h⟩
      exact ⟨hg, h⟩
    · rintro ⟨hg, h⟩
      exact ⟨hg, L.mem_centralizer hg, h⟩
  rw [L.card_eq_card_image_mul _ hD, L.image_inf_iInf_centralizer s hs hind, hQD,
    L.card_inf_iInf_centralizer_Q s hs hind, mul_comm]

end LeechSystem

end CFSG.Monster.GMS
