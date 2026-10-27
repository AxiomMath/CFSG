module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux6

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

public theorem isReflection_omPlusRefl (y : OmPlusIdx 4) :
    (omPlusRefl 3 y) ^ 2 = 1 ∧
      Nat.card {f : Fin 4 → Multiplicative (ZMod 3) // omPlusRefl 3 y f = f} * 3 =
        Nat.card (Fin 4 → Multiplicative (ZMod 3)) := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := y
  cases s
  · rw [omPlusRefl_false]
    exact ⟨permAut_swap_sq i j,
      card_fix_permAut_swap (p := 3) (k := 4) (by norm_num) (by norm_num) hij.ne⟩
  · rw [omPlusRefl_true]
    exact ⟨OrthExcEven.sgnTransp_sq hij.ne,
      OrthExcEven.card_fix_sgnTransp (p := 3) (k := 4) (by norm_num) (by norm_num) hij.ne⟩

public theorem NLqMap_mem_normalizer (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (l : ↥(NL L Bs)) :
    NLqMap Bs L θ l ∈
      Subgroup.normalizer (Ebar Bs L θ : Set (OrthRest.RPlus K 4)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Ebar Bs L θ).map (MulAut.conj (NLqMap Bs L θ l)) ≤ Ebar Bs L θ := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨e, he, rfl⟩ := (mem_Ebar θ).mp hz
    have h1 : MulAut.conj (NLqMap Bs L θ l) (qMap (K := K) θ e) =
        qMap (K := K) θ (NLtoL L Bs l * e * (NLtoL L Bs l)⁻¹) := by
      rw [MulAut.conj_apply, NLqMap_apply, map_mul, map_mul, map_inv]
    change (MulAut.conj (NLqMap Bs L θ l)) (qMap (K := K) θ e) ∈ Ebar Bs L θ
    rw [h1]
    refine (mem_Ebar θ).mpr ⟨NLtoL L Bs l * e * (NLtoL L Bs l)⁻¹, mem_EL.mpr ?_, rfl⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hN : ∀ h : G, h ∈ Bs ↔ (l : G) * h * (l : G)⁻¹ ∈ Bs :=
        Subgroup.mem_normalizer_iff.mp l.2.2
      exact (hN _).mp (Subgroup.mem_inf.mp (mem_EL.mp he)).1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ l.2.1 (Subgroup.mem_inf.mp (mem_EL.mp he)).2)
        (Subgroup.inv_mem _ l.2.1)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (NLqMap Bs L θ l)).injective]

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]


private theorem isSignedPerm_of_mem_range_conjC
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4}
    {Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ)}
    {ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))}
    (hΘE : ∀ e, Θ (ΘE e) = qE Bs L θ e)
    (hsigned : ∀ g : OrthRest.RPlus K 4,
      g ∈ Subgroup.normalizer (Ebar Bs L θ : Set (OrthRest.RPlus K 4)) →
        ∀ w : MulAut (Fin 4 → Multiplicative (ZMod 3)),
          (∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ =
            (Θ (w f) : OrthRest.RPlus K 4)) → IsSignedPerm ⇑w)
    {u : MulAut (Fin 4 → Multiplicative (ZMod 3))}
    (hu : u ∈ (conjC Bs L θ ΘE).range) : IsSignedPerm ⇑u := by
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hu
  refine hsigned (NLqMap Bs L θ l) (NLqMap_mem_normalizer Bs L θ l) u (fun f => ?_)
  rw [← hl]
  exact conjC_relation Bs L θ Θ ΘE hΘE l f

private theorem permAut_swap_mem_of_forall_omPlusRefl_mem
    {M : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3)))}
    (hM : ∀ y : OmPlusIdx 4, omPlusRefl 3 y ∈ M)
    {a b : Fin 4} (hab : a ≠ b) : permAut (Equiv.swap a b) ∈ M := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 : omPlusRefl 3 (⟨(a, b), h⟩, false) ∈ M := hM _
    rwa [omPlusRefl_false] at h1
  · have h1 : omPlusRefl 3 (⟨(b, a), h⟩, false) ∈ M := hM _
    rw [omPlusRefl_false, Equiv.swap_comm] at h1
    exact h1

private theorem sgnAut_mul_mem_of_forall_omPlusRefl_mem
    {M : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3)))}
    (hM : ∀ y : OmPlusIdx 4, omPlusRefl 3 y ∈ M)
    {i j : Fin 4} (hij : i ≠ j) : sgnAut i * sgnAut j ∈ M := by
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 : omPlusRefl 3 (⟨(i, j), h⟩, true) ∈ M := hM _
    have h2 : omPlusRefl 3 (⟨(i, j), h⟩, false) ∈ M := hM _
    rw [omPlusRefl_true] at h1
    rw [omPlusRefl_false] at h2
    have h3 : (sgnAut i * sgnAut j * permAut (Equiv.swap i j)) *
        (permAut (Equiv.swap i j))⁻¹ ∈ M := M.mul_mem h1 (M.inv_mem h2)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h3
  · have h1 : omPlusRefl 3 (⟨(j, i), h⟩, true) ∈ M := hM _
    have h2 : omPlusRefl 3 (⟨(j, i), h⟩, false) ∈ M := hM _
    rw [omPlusRefl_true] at h1
    rw [omPlusRefl_false] at h2
    have h3 : (sgnAut j * sgnAut i * permAut (Equiv.swap j i)) *
        (permAut (Equiv.swap j i))⁻¹ ∈ M := M.mul_mem h1 (M.inv_mem h2)
    rw [mul_assoc, mul_inv_cancel, mul_one, sgnAut_mul_comm j i] at h3
    exact h3

private theorem sgnAut_not_mem_range_conjC
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4}
    {Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ)}
    {ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))}
    (hΘE : ∀ e, Θ (ΘE e) = qE Bs L θ e)
    (hnosgn : ∀ (a : Fin 4) (g : OrthRest.RPlus K 4),
      (∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ =
        (Θ (sgnAut a f) : OrthRest.RPlus K 4)) → False)
    (a : Fin 4) : sgnAut a ∉ (conjC Bs L θ ΘE).range := by
  intro hmem
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hmem
  exact hnosgn a (NLqMap Bs L θ l) (fun f => by
    rw [← hl]
    exact conjC_relation Bs L θ Θ ΘE hΘE l f)

private theorem card_eq_192_of_isSignedPerm_even
    {M : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3)))}
    (hM : ∀ u ∈ M, IsSignedPerm ⇑u)
    (hD : ∀ i j : Fin 4, i ≠ j → sgnAut i * sgnAut j ∈ M)
    (hT : ∀ a b : Fin 4, a ≠ b → permAut (Equiv.swap a b) ∈ M)
    (hmiss : ∃ i : Fin 4, sgnAut i ∉ M) : Nat.card ↥M = 192 := by
  have h := SignedPermCount.card_eq_of_isSignedPerm_even (p := 3) (k := 4)
    (by norm_num) (by norm_num) hM hD hT hmiss
  norm_num at h
  exact h

private theorem closure_omPlusRefl_eq_of_card_eq_192
    {M : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3)))}
    (hM : ∀ y : OmPlusIdx 4, omPlusRefl 3 y ∈ M)
    (hM_signed : ∀ u ∈ M, IsSignedPerm ⇑u)
    (hM_card : Nat.card ↥M = 192) :
    Subgroup.closure (Set.range fun y : OmPlusIdx 4 => omPlusRefl 3 y) = M := by
  set H' : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3))) :=
    Subgroup.closure (Set.range fun y : OmPlusIdx 4 => omPlusRefl 3 y) with hH'def
  have hmem' : ∀ y : OmPlusIdx 4, omPlusRefl 3 y ∈ H' := fun y =>
    Subgroup.subset_closure ⟨y, rfl⟩
  have hgen_t : ∀ a b : Fin 4, a ≠ b → permAut (Equiv.swap a b) ∈ H' :=
    fun a b hab => permAut_swap_mem_of_forall_omPlusRefl_mem hmem' hab
  have hgen_d : ∀ i j : Fin 4, i ≠ j → sgnAut i * sgnAut j ∈ H' :=
    fun i j hij => sgnAut_mul_mem_of_forall_omPlusRefl_mem hmem' hij
  have hH'le : H' ≤ M :=
    (Subgroup.closure_le _).mpr (by rintro - ⟨y, rfl⟩; exact hM y)
  have hH'_signed : ∀ u ∈ H', IsSignedPerm ⇑u := fun u hu => hM_signed u (hH'le hu)
  have hH'_card : Nat.card ↥H' = 192 := by
    have hdvd : 192 ∣ Nat.card ↥H' := by
      have h := SignedPermCount.dvd_card_of_isSignedPerm_even (p := 3) (k := 4)
        (by norm_num) (by norm_num) hH'_signed hgen_d hgen_t
      norm_num at h ⊢
      exact h
    have hle : Nat.card ↥H' ≤ 192 := (Subgroup.card_le_of_le hH'le).trans_eq hM_card
    exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have hH'_eq : H' = M :=
    Subgroup.eq_of_le_of_card_ge hH'le (by rw [hH'_card, hM_card])
  exact hH'def.symm.trans hH'_eq

omit [Finite K] in
private theorem ker_conjBs_eq_ker_conjC
    {Bs L : Subgroup G} {x : G} {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4}
    {ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hxBs : x ∈ Bs) (hxord : orderOf x = 3)
    (hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    (conjBs L Bs).ker = (conjC Bs L θ ΘE).ker := by
  have h1 : (conjBs L Bs).ker = (conjE L Bs).ker :=
    (ker_conjE_eq_ker_conjBs hBs hcard hcardE hxBs hxord hExbot hLx).symm
  rw [h1,
    show conjC Bs L θ ΘE = (MulAut.congr ΘE).toMonoidHom.comp (conjE L Bs) from rfl,
    MonoidHom.ker_comp_of_injective _ _ (MulAut.congr ΘE).injective]

omit [Finite K] in
private theorem card_eq_192_of_maps_same_kernel
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4}
    {ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))}
    {P : Subgroup ↥(NL L Bs)} {K : Subgroup (MulAut ↥Bs)}
    {H : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3)))}
    (hPmapB : P.map (conjBs L Bs) = K)
    (hPmapC : P.map (conjC Bs L θ ΘE) = H)
    (hker : (conjBs L Bs).ker = (conjC Bs L θ ΘE).ker)
    (hcardH : Nat.card ↥H = 192) : Nat.card ↥K = 192 := by
  have h1 := Subgroup.card_ker_mul_card_range ((conjBs L Bs).comp P.subtype)
  have h2 := Subgroup.card_ker_mul_card_range ((conjC Bs L θ ΘE).comp P.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmapB] at h1
  rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmapC] at h2
  have hker' : ((conjBs L Bs).comp P.subtype).ker =
      ((conjC Bs L θ ΘE).comp P.subtype).ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
      ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker]
  rw [hker'] at h1
  have hpos : 0 < Nat.card ↥(((conjC Bs L θ ΘE).comp P.subtype).ker) := Nat.card_pos
  have heq : Nat.card ↥(((conjC Bs L θ ΘE).comp P.subtype).ker) * Nat.card ↥K =
      Nat.card ↥(((conjC Bs L θ ΘE).comp P.subtype).ker) * Nat.card ↥H :=
    h1.trans h2.symm
  rw [Nat.eq_of_mul_eq_mul_left hpos heq, hcardH]

private theorem exists_lift_mem_NL_conjC_eq_omPlusRefl
    {Bs L : Subgroup G} {x : G} {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4}
    {Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ)}
    {ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs))
    (hxBs : x ∈ Bs) (hxord : orderOf x = 3)
    (hΘE : ∀ e, Θ (ΘE e) = qE Bs L θ e)
    {y : OmPlusIdx 4}
    (hlift : ∃ g ∈ Subgroup.normalizer (Ebar Bs L θ : Set (OrthRest.RPlus K 4)),
      ∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ =
        (Θ (omPlusRefl 3 y f) : OrthRest.RPlus K 4)) :
    ∃ l : ↥(NL L Bs), (conjC Bs L θ ΘE) l = omPlusRefl 3 y ∧
      GGIsReflection 3 (conjBs L Bs l) := by
  obtain ⟨g, hgN, hgrel⟩ := hlift
  obtain ⟨l, hl, hlNL⟩ :=
    exists_lift_mem_NL hZ2 hBs hcard hcardE hx1 hLx hBL θ hgN
  have hconjC : (conjC Bs L θ ΘE) ⟨l, hlNL⟩ = omPlusRefl 3 y := by
    refine MulEquiv.ext fun f => Θ.injective (Subtype.ext ?_)
    rw [← conjC_relation Bs L θ Θ ΘE hΘE ⟨l, hlNL⟩ f]
    have h1 : NLqMap Bs L θ ⟨l, hlNL⟩ = g := by
      rw [NLqMap_apply]
      exact hl
    rw [h1]
    exact hgrel f
  refine ⟨⟨l, hlNL⟩, hconjC, ?_⟩
  have hconjE : conjE L Bs ⟨l, hlNL⟩ = (MulAut.congr ΘE).symm (omPlusRefl 3 y) := by
    apply (MulAut.congr ΘE).injective
    rw [show (MulAut.congr ΘE) ((conjE L Bs) ⟨l, hlNL⟩) =
      conjC Bs L θ ΘE ⟨l, hlNL⟩ from rfl, hconjC, MulEquiv.apply_symm_apply]
  have hreflE : (conjE L Bs ⟨l, hlNL⟩) ^ 2 = 1 ∧
      Nat.card {e : ↥(Bs ⊓ L) // conjE L Bs ⟨l, hlNL⟩ e = e} * 3 =
        Nat.card ↥(Bs ⊓ L) := by
    constructor
    · rw [hconjE, show ((MulAut.congr ΘE).symm (omPlusRefl 3 y)) ^ 2 =
          (MulAut.congr ΘE).symm ((omPlusRefl 3 y) ^ 2) from (map_pow _ _ 2).symm,
        (isReflection_omPlusRefl y).1, map_one]
    · rw [← card_fixedPoints_congr ΘE (conjE L Bs ⟨l, hlNL⟩), hconjE,
        MulEquiv.apply_symm_apply, (isReflection_omPlusRefl y).2,
        ← Nat.card_congr ΘE.toEquiv]
  exact isReflection_conjE hcompl hxBs hxord hcard hcardE hLx ⟨l, hlNL⟩ hreflE.1 hreflE.2

omit [Finite K] in
private theorem card_ggAutomizer_eq_192_of_card_range_conjC
    {Bs L : Subgroup G} {x : G} {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4}
    {ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hxBs : x ∈ Bs) (hxord : orderOf x = 3)
    (hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hH : Nat.card ↥(conjC Bs L θ ΘE).range = 192) :
    Nat.card (ggAutomizer L Bs) = 192 := by
  rw [card_ggAutomizer_eq_card_range_conjE hBs hcard hcardE hxBs hxord hExbot hLx]
  have hmap : (conjC Bs L θ ΘE).range =
      ((conjE L Bs).range).map (MulAut.congr ΘE).toMonoidHom :=
    MonoidHom.range_comp (MulAut.congr ΘE).toMonoidHom (conjE L Bs)
  have hcardmap : Nat.card ↥((conjE L Bs).range) =
      Nat.card ↥(((conjE L Bs).range).map (MulAut.congr ΘE).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.congr ΘE).injective).symm
  rw [hcardmap, ← hmap, hH]

private theorem ggAutomizer_eq_closure_reflections
    {Bs L : Subgroup G} {x : G} {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4}
    {Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ)}
    {ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs))
    (hxBs : x ∈ Bs) (hxord : orderOf x = 3)
    (hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥)
    (hΘE : ∀ e, Θ (ΘE e) = qE Bs L θ e)
    (hlifts : ∀ y : OmPlusIdx 4,
      ∃ g ∈ Subgroup.normalizer (Ebar Bs L θ : Set (OrthRest.RPlus K 4)),
        ∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ =
          (Θ (omPlusRefl 3 y f) : OrthRest.RPlus K 4))
    (hH_gen : Subgroup.closure (Set.range fun y : OmPlusIdx 4 => omPlusRefl 3 y) =
      (conjC Bs L θ ΘE).range)
    (hcardH : Nat.card ↥(conjC Bs L θ ΘE).range = 192)
    (hcardA : Nat.card (ggAutomizer L Bs) = 192) :
    ggAutomizer L Bs =
      Subgroup.closure {r | r ∈ ggAutomizer L Bs ∧ GGIsReflection 3 r} := by
  have hAeq : ggAutomizer L Bs = (conjBs L Bs).range := ggAutomizer_eq_range_conjBs L Bs
  set S : Set (MulAut ↥Bs) := {r | r ∈ ggAutomizer L Bs ∧ GGIsReflection 3 r} with hSdef
  set K : Subgroup (MulAut ↥Bs) := Subgroup.closure S with hKdef
  have hKleA : K ≤ ggAutomizer L Bs :=
    (Subgroup.closure_le _).mpr (fun r hr => hr.1)
  set P : Subgroup ↥(NL L Bs) := K.comap (conjBs L Bs) with hPdef
  have hPmapB : P.map (conjBs L Bs) = K := by
    refine le_antisymm ?_ ?_
    · rintro - ⟨l, hl, rfl⟩
      exact hl
    · intro k hk
      have hkA : k ∈ (conjBs L Bs).range := by rw [← hAeq]; exact hKleA hk
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hkA
      exact ⟨l, hk, rfl⟩
  have hPmapC : P.map (conjC Bs L θ ΘE) = (conjC Bs L θ ΘE).range := by
    refine le_antisymm ?_ ?_
    · rintro - ⟨l, -, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨l, rfl⟩
    · rw [← hH_gen]
      refine (Subgroup.closure_le _).mpr ?_
      rintro - ⟨y, rfl⟩
      obtain ⟨l, hconjC, hrefl⟩ :=
        exists_lift_mem_NL_conjC_eq_omPlusRefl hZ2 hBs hcard hcardE hx1 hLx hBL
          hcompl hxBs hxord hΘE (hlifts y)
      have hmemK : conjBs L Bs l ∈ K :=
        Subgroup.subset_closure
          ⟨by rw [hAeq]; exact MonoidHom.mem_range.mpr ⟨l, rfl⟩, hrefl⟩
      exact ⟨l, hmemK, hconjC⟩
  have hcardK : Nat.card ↥K = 192 :=
    card_eq_192_of_maps_same_kernel hPmapB hPmapC
      (ker_conjBs_eq_ker_conjC hBs hcard hcardE hxBs hxord hExbot hLx) hcardH
  have hKA : K = ggAutomizer L Bs := by
    refine Subgroup.eq_of_le_of_card_ge hKleA ?_
    rw [hcardK, hcardA]
  exact hKA.symm

theorem card_ggAutomizer_eq_of_omegaPlus (hK : Nat.card K = 2) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    Nat.card (ggAutomizer L Bs) = 192 ∧
      ggAutomizer L Bs =
        Subgroup.closure {r | r ∈ ggAutomizer L Bs ∧ GGIsReflection 3 r} := by
  classical
  obtain ⟨hxBs, hxL, hxord, hEbot, hExbot⟩ := bstar_basic hZ2 hBs hx1 hBL
  have hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs) :=
    bstar_isComplement hBs hcard hcardE hxBs hxord hExbot
  obtain ⟨Θ, hsigned, hnosgn, hlifts⟩ :=
    exists_frameSignedDataRPlus hK hZ2 hBs hcard hcardE hx1 hLx hBL hstar θ
  set ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3)) := ΘE Bs L θ Θ hEbot with hΘEdef
  have hΘE : ∀ e, Θ (ΘE e) = qE Bs L θ e := fun e => ΘE_apply Bs L θ Θ hEbot e
  set H : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3))) :=
    (conjC Bs L θ ΘE).range with hHdef
  have hH_signed : ∀ u ∈ H, IsSignedPerm ⇑u := by
    intro u hu
    exact isSignedPerm_of_mem_range_conjC hΘE hsigned (hHdef ▸ hu)
  have homPlus_mem : ∀ y : OmPlusIdx 4, omPlusRefl 3 y ∈ H := by
    intro y
    obtain ⟨l, hconjC, -⟩ :=
      exists_lift_mem_NL_conjC_eq_omPlusRefl hZ2 hBs hcard hcardE hx1 hLx hBL
        hcompl hxBs hxord hΘE (hlifts y)
    exact hHdef.symm ▸ MonoidHom.mem_range.mpr ⟨l, hconjC⟩
  have HT : ∀ a b : Fin 4, a ≠ b → permAut (Equiv.swap a b) ∈ H :=
    fun a b hab => permAut_swap_mem_of_forall_omPlusRefl_mem homPlus_mem hab
  have HD : ∀ i j : Fin 4, i ≠ j → sgnAut i * sgnAut j ∈ H :=
    fun i j hij => sgnAut_mul_mem_of_forall_omPlusRefl_mem homPlus_mem hij
  have hH_card : Nat.card H = 192 :=
    card_eq_192_of_isSignedPerm_even hH_signed HD HT
      ⟨0, by rw [hHdef]; exact sgnAut_not_mem_range_conjC hΘE hnosgn 0⟩
  have hH_gen : Subgroup.closure (Set.range fun y : OmPlusIdx 4 => omPlusRefl 3 y) =
      H :=
    closure_omPlusRefl_eq_of_card_eq_192 homPlus_mem hH_signed hH_card
  have hcardA : Nat.card (ggAutomizer L Bs) = 192 :=
    card_ggAutomizer_eq_192_of_card_range_conjC hBs hcard hcardE hxBs hxord hExbot hLx
      (hHdef ▸ hH_card)
  refine ⟨hcardA, ?_⟩
  exact ggAutomizer_eq_closure_reflections hZ2 hBs hcard hcardE hx1 hLx hBL hcompl
    hxBs hxord hExbot hΘE hlifts (hHdef ▸ hH_gen) (hHdef ▸ hH_card) hcardA

end CFSG.StandardType.E6QTwo

end
