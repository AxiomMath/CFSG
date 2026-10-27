module

public import CFSG.Quasithin.Vol2.Ch3zStep

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6

namespace Ch3z

section Natural

theorem allOnes_sq (n : ℕ) : allOnes n * allOnes n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, allOnes, toAdd_ofAdd, Pi.add_apply, toAdd_one, Pi.zero_apply]
  decide

theorem allOnes_not_mem_core {n : ℕ} (hn : Odd n) : allOnes n ∉ coreMod n := by
  intro h
  rw [mem_coreMod] at h
  simp only [allOnes, toAdd_ofAdd] at h
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  obtain ⟨k, rfl⟩ := hn
  have h1 : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [h1] at h
  exact one_ne_zero h

@[expose] def allOnesSub (n : ℕ) : Subgroup (PermMod n) where
  carrier := {x | x = 1 ∨ x = allOnes n}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (allOnes_sq n)
  inv_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right (allOnes_sq n))

theorem natKer_eq_bot {n : ℕ} (hn : Odd n) : natKer n = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu' : (u : PermMod n) ∈ Subgroup.zpowers (allOnes n) := hu
  have hle : Subgroup.zpowers (allOnes n) ≤ allOnesSub n :=
    Subgroup.zpowers_le.mpr (Or.inr rfl)
  rcases hle hu' with h1 | h1
  · exact Subtype.ext h1
  · exfalso
    have h2 : allOnes n ∈ coreMod n := by
      rw [← h1]
      exact u.2
    exact allOnes_not_mem_core hn h2

end Natural

section Quot

variable {G : Type} [Group G] {L N : Subgroup G}

@[expose] noncomputable def chiefLift [(L.subgroupOf N).Normal] (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    ↥N ⧸ L.subgroupOf N →* ↥(chiefMod L N) :=
  QuotientGroup.lift (L.subgroupOf N) (chiefIota hNL)
    (fun x hx => MonoidHom.mem_ker.mpr ((chiefIota_eq_one_iff hNL x).2 (Subgroup.mem_subgroupOf.mp hx)))

theorem chiefLift_bijective [(L.subgroupOf N).Normal] (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    Function.Bijective (chiefLift hNL) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      have h1 : chiefIota hNL x = 1 := MonoidHom.mem_ker.mp hq
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff x).2
        (Subgroup.mem_subgroupOf.mpr ((chiefIota_eq_one_iff hNL x).1 h1))
  · intro y
    obtain ⟨x, rfl⟩ := chiefIota_surjective hNL y
    exact ⟨QuotientGroup.mk x, rfl⟩

@[expose] noncomputable def chiefQuotEquiv [(L.subgroupOf N).Normal]
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) : ↥N ⧸ L.subgroupOf N ≃* ↥(chiefMod L N) :=
  MulEquiv.ofBijective (chiefLift hNL) (chiefLift_bijective hNL)

theorem chiefQuotEquiv_mk [(L.subgroupOf N).Normal] (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (x : ↥N) : chiefQuotEquiv hNL (QuotientGroup.mk x) = chiefIota hNL x := rfl

end Quot

section One

variable {G : Type} [Group G] [Finite G] {H L N U : Subgroup G}

theorem translate_one (hstep : IsChiefStep H U L N) (hUH : U ≤ H) [(L.subgroupOf N).Normal]
    {m : ℕ} (hm : Odd m) (θ : ↥(chiefAut H L N) ≃* Equiv.Perm (Fin m))
    (β : ↥(coreMod m) →* ↥(chiefMod L N))
    (hβeq : ∀ (x : ↥(chiefAut H L N)) (u : ↥(coreMod m)),
      β (coreAct m (θ x) u) = (x : MulAut ↥(chiefMod L N)) (β u))
    (hβr : β.range = ⊤) (hβk : β.ker = ⊥)
    (hJ : ((thompsonJ H).subgroupOf H).map
      (θ.toMonoidHom.comp (chiefHom (Setting.hHL hstep) (Setting.hHN hstep))) = ⊤) :
    QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin m)) (Equiv.Perm (Fin m)) ∧
      NaturalSn m H L N := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNH : N ≤ H := hstep.1.1.trans hUH
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hNH.trans hHL
  have hCeq : cSecIn H L N = centralizerMod L H N := cSecIn_eq_centralizerMod le_rfl hstep.2.1
  set φ : ↥H →* Equiv.Perm (Fin m) := θ.toMonoidHom.comp (chiefHom hHL hHN) with hφ
  have hφsurj : Function.Surjective φ := θ.surjective.comp (chiefHom_surjective hHL hHN)
  have hφker : φ.ker = (cSecIn H L N).subgroupOf H := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hCeq]
    constructor
    · intro hg
      have hg' : θ (chiefHom hHL hHN g) = 1 := hg
      have h1 : chiefHom hHL hHN g = 1 := θ.injective (by rw [map_one]; exact hg')
      exact (chiefHom_eq_one_iff hHL hHN hNL g).1 h1
    · intro hg
      have h1 := (chiefHom_eq_one_iff hHL hHN hNL g).2 hg
      show θ (chiefHom hHL hHN g) = 1
      rw [h1, map_one]
  refine ⟨⟨φ, hφsurj, hφker, ⟨(MulEquiv.subgroupCongr hJ).trans Subgroup.topEquiv⟩⟩, ?_⟩
  refine ⟨φ, (chiefQuotEquiv hNL).symm.toMonoidHom.comp β, hφsurj, hφker, ?_, ?_, ?_⟩
  · exact (chiefQuotEquiv hNL).symm.surjective.comp (MonoidHom.range_eq_top.mp hβr)
  · have h1 : ((chiefQuotEquiv hNL).symm.toMonoidHom.comp β).ker = β.ker := by
      ext u
      simp [MonoidHom.mem_ker]
    rw [h1, hβk, natKer_eq_bot hm]
  · intro f u x hux
    have hβu : β u = chiefIota hNL x := by
      have h1 := congrArg (chiefQuotEquiv hNL) hux
      rw [chiefQuotEquiv_mk] at h1
      simpa using h1
    have hfx : (f : G) * x * (f : G)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN f.2) x).mp x.2
    refine ⟨hfx, ?_⟩
    show (chiefQuotEquiv hNL).symm (β (coreAct m (θ (chiefHom hHL hHN f)) u)) =
      QuotientGroup.mk ⟨(f : G) * x * (f : G)⁻¹, hfx⟩
    rw [hβeq]
    have e1 : ((chiefHom hHL hHN f : ↥(chiefAut H L N)) : MulAut ↥(chiefMod L N)) =
        chiefPsi hHL hHN f := rfl
    rw [e1, hβu, chiefPsi_iota hHL hHN hNL f x hfx]
    apply (chiefQuotEquiv hNL).injective
    rw [MulEquiv.apply_symm_apply, chiefQuotEquiv_mk]

end One

end Ch3z

end CFSG.Quasithin
