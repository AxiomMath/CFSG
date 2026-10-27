module

public import CFSG.Sporadic.Co2Smith.GlNJKCompl
public import CFSG.Sporadic.Co2Smith.GlNJG2

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith CFSG.Certificates
open Subgroup

theorem LK_le_normalizer :
    LK ≤ normalizer (Jc : Set K) :=
  LK_le_N

theorem normalizer_Jc_eq :
    normalizer (Jc : Set K) = Jc ⊔ LK := by
  refine le_antisymm ?_ (sup_le Subgroup.le_normalizer LK_le_normalizer)
  intro g hg
  obtain ⟨x, hxLK, hxpi⟩ := exists_LK_piK (σ := piK ⟨g, hg⟩) (piK_mem_njAut ⟨g, hg⟩)
  have hker : piK (x⁻¹ * ⟨g, hg⟩) = 1 := by
    rw [map_mul, map_inv, hxpi, inv_mul_cancel]
  have hmem : (x : K)⁻¹ * g ∈ Jc := by
    simpa using mem_Jc_of_piK_eq_one hker
  have hg' : g = (x : K) * ((x : K)⁻¹ * g) := by group
  rw [hg']
  exact Subgroup.mul_mem (Jc ⊔ LK) (Subgroup.mem_sup_right hxLK)
    (Subgroup.mem_sup_left hmem)

private theorem exists_njAut_apply_zero
    (k : Fin 77) :
    ∃ σ ∈ njAut, σ 0 = k := by
  refine ⟨piK ⟨wordK CFSG.Sporadic.Co2Smith.Native.glNJConj[(k : ℕ)]!, wordK_mem ?_⟩,
    piK_mem_njAut _, ?_⟩
  · intro i hi
    exact qK_mem_N ((glNJOm_spec.2.2.2.2.2.2.1 k k.2).1 i hi)
  · apply omK_injective
    rw [piK_spec, omK_zero, omK_conj_z0]

private theorem card_stabilizer_njAut (b : Fin 77) :
    Nat.card ↥(MulAction.stabilizer njAut b) =
      Nat.card ↥(njAut ⊓ MulAction.stabilizer (Equiv.Perm (Fin 77)) b) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun σ => ⟨σ.1.1, ⟨σ.1.2, σ.2⟩⟩
      invFun := fun τ => ⟨⟨τ.1, τ.2.1⟩, τ.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_njAut :
    Nat.card njAut = 887040 := by
  have htrans : ∀ k : Fin 77, ∃ σ ∈ njAut, σ 0 = k := exists_njAut_apply_zero
  have horbit : MulAction.orbit njAut (0 : Fin 77) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro k
    obtain ⟨σ, hσ, hσk⟩ := htrans k
    exact MulAction.mem_orbit_iff.2 ⟨⟨σ, hσ⟩, hσk⟩
  have horbitcard : Nat.card ↑(MulAction.orbit njAut (0 : Fin 77)) = 77 := by
    rw [horbit, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hstab : Nat.card (MulAction.stabilizer njAut (0 : Fin 77)) = 11520 := by
    rw [card_stabilizer_njAut,
      show njAut ⊓ MulAction.stabilizer (Equiv.Perm (Fin 77)) (0 : Fin 77) = njAut0 from rfl,
      ← PQ_eq_njAut0, card_PQ]
  have hOS := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAction.stabilizer njAut (0 : Fin 77))
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer njAut (0 : Fin 77))] at hOS
  calc Nat.card njAut = 77 * 11520 := by rw [hOS, horbitcard, hstab]
    _ = 887040 := by norm_num

theorem card_normalizer_Jc :
    Nat.card (normalizer (Jc : Set K)) = 908328960 := by
  have hker : piK.ker = Jc.subgroupOf (normalizer (Jc : Set K)) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨mem_Jc_of_piK_eq_one, piK_Jc⟩
  have hrange : piK.range = njAut := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact piK_mem_njAut g
    intro σ hσ
    obtain ⟨x, -, hx⟩ := exists_LK_piK hσ
    exact ⟨x, hx⟩
  have hkercard : Nat.card piK.ker = 1024 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer : Jc ≤ normalizer (Jc : Set K))).toEquiv, card_Jc]
  have hrangcard : Nat.card piK.range = 887040 := by
    rw [hrange, card_njAut]
  have hOS := Subgroup.card_eq_card_quotient_mul_card_subgroup piK.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange piK).toEquiv] at hOS
  calc Nat.card (normalizer (Jc : Set K)) = 887040 * 1024 := by rw [hOS, hkercard, hrangcard]
    _ = 908328960 := by norm_num

theorem closure_range_omK :
    Subgroup.closure (Set.range omK) = Jc := by
  refine le_antisymm ?_ Jc_le_closure_omK
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact omK_mem_Jc k

theorem closure_preimage_omK :
    Subgroup.closure (Subgroup.subtype Jc ⁻¹' Set.range omK) = ⊤ := by
  have hmap : (Subgroup.closure (Subgroup.subtype Jc ⁻¹' Set.range omK)).map
      (Subgroup.subtype Jc) = Jc := by
    rw [MonoidHom.map_closure]
    have hset : (Subgroup.subtype Jc) '' (Subgroup.subtype Jc ⁻¹' Set.range omK) =
        Set.range omK := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · rintro ⟨k, rfl⟩
        exact ⟨⟨omK k, omK_mem_Jc k⟩, ⟨k, rfl⟩, rfl⟩
    rw [hset, closure_range_omK]
  refine le_antisymm le_top ?_
  intro a _
  have ha : (a : K) ∈ (Subgroup.closure (Subgroup.subtype Jc ⁻¹' Set.range omK)).map
      (Subgroup.subtype Jc) := by
    rw [hmap]
    exact a.2
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 ha
  have hba' : b = a := Subtype.ext hba
  simpa [hba'] using hb

theorem cnt_omK_mulAut (α : MulAut Jc)
    (σ : Equiv.Perm (Fin 77))
    (hσ : ∀ k, ((α ⟨omK k, omK_mem_Jc k⟩ : Jc) : K) = omK (σ k)) (x : Jc) :
    cnt omK ((α x : Jc) : K) = cnt omK (x : K) := by
  have hsymm : ∀ k, α ⟨omK (σ.symm k), omK_mem_Jc (σ.symm k)⟩ =
      ⟨omK k, omK_mem_Jc k⟩ := by
    intro k
    apply Subtype.ext
    rw [hσ (σ.symm k), Equiv.apply_symm_apply]
  have hsymm' : ∀ k, α.symm ⟨omK k, omK_mem_Jc k⟩ =
      ⟨omK (σ.symm k), omK_mem_Jc (σ.symm k)⟩ := by
    intro k
    have h := congrArg (fun w => α.symm w) (hsymm k)
    simpa using h.symm
  unfold cnt
  refine Nat.card_congr (Equiv.subtypeEquiv σ.symm fun k => ?_)
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨σ.symm j, ?_⟩
    have hjJ : (⟨omK j, omK_mem_Jc j⟩ : Jc) =
        (⟨omK k, omK_mem_Jc k⟩ : Jc) * α x := Subtype.ext hj
    have h' := congrArg (fun w : Jc => α.symm w) hjJ
    simp only [map_mul, MulEquiv.symm_apply_apply] at h'
    have h'' := congrArg Subtype.val h'
    simp only [Subgroup.coe_mul] at h''
    rw [congrArg Subtype.val (hsymm' j), congrArg Subtype.val (hsymm' k)] at h''
    exact h''
  · rintro ⟨j, hj⟩
    refine ⟨σ j, ?_⟩
    have hjJ : (⟨omK j, omK_mem_Jc j⟩ : Jc) =
        (⟨omK (σ.symm k), omK_mem_Jc (σ.symm k)⟩ : Jc) * x := Subtype.ext hj
    have h' := congrArg (fun w : Jc => α w) hjJ
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    have h'' := congrArg Subtype.val h'
    simp only [Subgroup.coe_mul] at h''
    rw [hσ j, congrArg Subtype.val (hsymm k)] at h''
    exact h''

theorem adj_omK_mulAut (α : MulAut Jc)
    (σ : Equiv.Perm (Fin 77))
    (hσ : ∀ k, ((α ⟨omK k, omK_mem_Jc k⟩ : Jc) : K) = omK (σ k)) (a b : Fin 77) :
    adj omK (σ a) (σ b) ↔ adj omK a b := by
  unfold adj
  have hmul : omK (σ a) * omK (σ b) =
      ((α ((⟨omK a, omK_mem_Jc a⟩ : Jc) * ⟨omK b, omK_mem_Jc b⟩) : Jc) : K) := by
    rw [map_mul, Subgroup.coe_mul, hσ a, hσ b]
  rw [hmul, cnt_omK_mulAut α σ hσ, Function.Injective.ne_iff (EquivLike.injective σ)]
  simp [Subgroup.coe_mul]

theorem nbrInv_of_mulAut
    (α : MulAut Jc) (σ : Equiv.Perm (Fin 77))
    (hσ : ∀ k, ((α ⟨omK k, omK_mem_Jc k⟩ : Jc) : K) = omK (σ k)) :
    NbrInv CFSG.Sporadic.Co2Smith.Native.glNJNbr σ := by
  intro x y
  rw [mem_glNJNbr_iff, mem_glNJNbr_iff]
  exact (adj_omK_mulAut α σ hσ x y).symm

private theorem exists_perm_of_maps
    (α : MulAut Jc)
    (hα : ∀ k : Fin 77, ∃ k' : Fin 77, ((α ⟨omK k, omK_mem_Jc k⟩ : Jc) : K) = omK k') :
    ∃ σ : Equiv.Perm (Fin 77),
      ∀ k, ((α ⟨omK k, omK_mem_Jc k⟩ : Jc) : K) = omK (σ k) := by
  choose f hf using hα
  have hfinj : Function.Injective f := by
    intro a b hab
    have h : ((α ⟨omK a, omK_mem_Jc a⟩ : Jc) : K) =
        ((α ⟨omK b, omK_mem_Jc b⟩ : Jc) : K) := by rw [hf a, hf b, hab]
    have hJ := EquivLike.injective α (Subtype.ext h)
    exact omK_injective (congrArg Subtype.val hJ)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj), fun k => ?_⟩
  exact hf k

theorem exists_LK_conj_eq_omK
    (k : Fin 77) :
    ∃ ℓ ∈ LK, ℓ * z0 * ℓ⁻¹ = omK k := by
  refine ⟨wordK CFSG.Sporadic.Co2Smith.Native.glNJConj[(k : ℕ)]!, wordK_mem ?_,
    omK_conj_z0 k⟩
  intro i hi
  exact subset_closure ⟨⟨i, (glNJOm_spec.2.2.2.2.2.2.1 k k.2).1 i hi⟩, rfl⟩

private def conjAgree (α : MulAut Jc) (ℓ : K) :
    Subgroup Jc where
  carrier := {a | ((α a : Jc) : K) = ℓ * (a : K) * ℓ⁻¹}
  one_mem' := by
    show ((α 1 : Jc) : K) = ℓ * ((1 : Jc) : K) * ℓ⁻¹
    simp
  mul_mem' := fun {a b} ha hb => by
    show ((α (a * b) : Jc) : K) = ℓ * ((a * b : Jc) : K) * ℓ⁻¹
    rw [map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]
    group
  inv_mem' := fun {a} ha => by
    show ((α a⁻¹ : Jc) : K) = ℓ * ((a⁻¹ : Jc) : K) * ℓ⁻¹
    rw [map_inv, Subgroup.coe_inv, Subgroup.coe_inv, ha]
    group

private theorem conjAgree_eq_top
    (α : MulAut Jc) (ℓ : K)
    (hℓ : ∀ k, ((α ⟨omK k, omK_mem_Jc k⟩ : Jc) : K) = ℓ * omK k * ℓ⁻¹) :
    conjAgree α ℓ = ⊤ := by
  refine le_antisymm le_top ?_
  have hsub : Subgroup.closure (Subgroup.subtype Jc ⁻¹' Set.range omK) ≤ conjAgree α ℓ := by
    rw [Subgroup.closure_le]
    rintro a ⟨k, hk⟩
    rw [show a = (⟨omK k, omK_mem_Jc k⟩ : Jc) from Subtype.ext hk.symm]
    exact hℓ k
  intro a _
  refine hsub ?_
  rw [closure_preimage_omK]
  trivial

theorem exists_LK_of_preserves
    (α : MulAut Jc)
    (hα : ∀ k : Fin 77, ∃ k' : Fin 77, ((α ⟨omK k, omK_mem_Jc k⟩ : Jc) : K) = omK k') :
    ∃ ℓ ∈ LK, ∀ a : Jc, ((α a : Jc) : K) = ℓ * a * ℓ⁻¹ := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_maps α hα
  have hσnj : σ ∈ njAut := (mem_njAut).2 (nbrInv_of_mulAut α σ hσ)
  obtain ⟨x, hxLK, hxpi⟩ := exists_LK_piK hσnj
  refine ⟨(x : K), hxLK, fun a => ?_⟩
  have htop : conjAgree α (x : K) = ⊤ :=
    conjAgree_eq_top α (x : K) fun k => by rw [hσ k, ← hxpi, piK_spec]
  have ha : a ∈ conjAgree α (x : K) := by
    rw [htop]
    exact Subgroup.mem_top a
  exact ha

end CFSG.Sporadic.Co2Jc
