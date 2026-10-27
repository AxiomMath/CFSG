module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaB

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace X1512

variable {G : Type} [Group G]

structure NatMod (n : ℕ) (K L X : Subgroup G) [(L.subgroupOf X).Normal]
    (Ψ : ↥K →* Equiv.Perm (Fin n)) (β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X) : Prop where
  surj : Function.Surjective β
  inj : Function.Injective β
  equiv : ∀ (k : ↥K) (u : ↥(G6.coreMod n)) (x : ↥X), β u = QuotientGroup.mk x →
    ∃ hkx : (k : G) * (x : G) * (k : G)⁻¹ ∈ X,
      β (G6.coreAct n (Ψ k) u) = QuotientGroup.mk ⟨(k : G) * (x : G) * (k : G)⁻¹, hkx⟩

theorem natMod_of_naturalSn {n : ℕ} (hn : n = 3 ∨ n = 5) {F L X : Subgroup G}
    [(L.subgroupOf X).Normal] (h : NaturalSn n F L X) :
    ∃ (Ψ : ↥F →* Equiv.Perm (Fin n)) (β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X),
      Function.Surjective Ψ ∧ Ψ.ker = (cSecIn F L X).subgroupOf F ∧ NatMod n F L X Ψ β := by
  obtain ⟨θ, β, hθs, hθk, hβs, hβk, hequiv⟩ := h
  refine ⟨θ, β, hθs, hθk, hβs, ?_, hequiv⟩
  rw [← MonoidHom.ker_eq_bot_iff, hβk, natKer_eq_bot hn]

variable {n : ℕ} {K L X A : Subgroup G} [(L.subgroupOf X).Normal]
  {Ψ : ↥K →* Equiv.Perm (Fin n)} {β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X}

theorem relIndex_fixSecIn_eq (hM : NatMod n K L X Ψ β) (hLX : L ≤ X) (hAK : A ≤ K) :
    (fixSecIn A L X).relIndex X = (fixΔ n ((A.subgroupOf K).map Ψ)).index := by
  have hcomap : (fixSecIn A L X).subgroupOf X =
      ((fixΔ n ((A.subgroupOf K).map Ψ)).map β).comap (QuotientGroup.mk' (L.subgroupOf X)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_map, mem_fixSecIn hLX]
    constructor
    · rintro ⟨-, hx⟩
      obtain ⟨u, hu⟩ := hM.surj (QuotientGroup.mk x)
      refine ⟨u, ?_, hu⟩
      rintro σ ⟨a', ha', rfl⟩
      obtain ⟨hax, h⟩ := hM.equiv a' u x hu
      apply hM.inj
      rw [h, hu]
      exact ((mk_eq_iff hLX).mpr (hx a' (Subgroup.mem_subgroupOf.mp ha'))).symm
    · rintro ⟨u, hu, hux⟩
      refine ⟨x.2, fun a ha => ?_⟩
      have haK : a ∈ K := hAK ha
      have hux' : β u = QuotientGroup.mk x := hux
      obtain ⟨hax, h⟩ := hM.equiv ⟨a, haK⟩ u x hux'
      have hfix := hu (Ψ ⟨a, haK⟩) ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [hfix, hux'] at h
      exact (mk_eq_iff hLX).mp h
  unfold Subgroup.relIndex
  rw [hcomap]
  refine (Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)).trans ?_
  exact Subgroup.index_map_of_bijective ⟨hM.inj, hM.surj⟩ _

end X1512

end CFSG.Quasithin
