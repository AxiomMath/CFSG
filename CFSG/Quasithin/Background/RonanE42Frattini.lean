module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_sup_of_normal {K X T : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hXK : X ≤ K) (hn : K ≤ Subgroup.normalizer ((X ⊔ T : Subgroup G) : Set G)) :
    K ≤ Subgroup.normalizer (T : Set G) ⊔ X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : T.relIndex K ∣ T.relIndex ⊤ :=
    ⟨_, (Subgroup.relIndex_mul_relIndex T K ⊤ hTK le_top).symm⟩
  have hTK2 : IsSylowIn 2 T K :=
    ⟨hTK, hT.isPGroup, fun h => hT.not_dvd_relIndex (h.trans hdiv)⟩
  have hMK : X ⊔ T ≤ K := sup_le hXK hTK
  have hN : ((X ⊔ T).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMK).mpr hn
  haveI : Finite (Sylow 2 K) :=
    Finite.of_injective (fun P : Sylow 2 K => (P : Set K)) SetLike.coe_injective
  obtain ⟨P, hPT⟩ : ∃ P : Sylow 2 K, (P : Subgroup K) = T.subgroupOf K :=
    ⟨hTK2.toSylow, IsSylowIn.coe_toSylow hTK2⟩
  have hPmem : ∀ x : K, x ∈ (P : Subgroup K) ↔ (x : G) ∈ T := fun x => by
    rw [hPT, Subgroup.mem_subgroupOf]
  have hPle : (P : Subgroup K) ≤ (X ⊔ T).subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ((hPmem x).mp hx))
  have htop := Sylow.normalizer_sup_eq_top' (N := (X ⊔ T).subgroupOf K) P hPle
  have hXT : X ⊔ T ≤ Subgroup.normalizer (T : Set G) ⊔ X :=
    sup_le le_sup_right fun t ht => Subgroup.mem_sup_left (Subgroup.le_normalizer ht)
  intro k hk
  have hmem : (⟨k, hk⟩ : K) ∈ ((Subgroup.normalizer (P : Set K) ⊔ (X ⊔ T).subgroupOf K :
      Subgroup K) : Set K) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mul_normal] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
  have haT : (a : G) ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      let h' : ↥K := ⟨h, hTK hh⟩
      exact (hPmem _).mp ((Subgroup.mem_normalizer_iff.mp ha h').mp ((hPmem h').mpr hh))
    · intro hh
      have hhK : h ∈ K := by
        have e : h = (a : G)⁻¹ * ((a : G) * h * (a : G)⁻¹) * (a : G) := by group
        rw [e]
        exact K.mul_mem (K.mul_mem (K.inv_mem a.2) (hTK hh)) a.2
      let h' : ↥K := ⟨h, hhK⟩
      exact (hPmem h').mp ((Subgroup.mem_normalizer_iff.mp ha h').mpr ((hPmem _).mpr hh))
  have hbN : (b : G) ∈ X ⊔ T := Subgroup.mem_subgroupOf.mp hb
  have hkab : (a : G) * (b : G) = k := by
    have := congrArg Subtype.val hab
    simpa using this
  rw [← hkab]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haT) (hXT hbN)

end CFSG.Quasithin.RonanE42
