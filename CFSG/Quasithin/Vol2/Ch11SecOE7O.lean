module

public import CFSG.Quasithin.Vol2.Ch11SecOE7G
public import CFSG.Quasithin.Background.A3Structure320
public import CFSG.Quasithin.Vol2.Ch11SecOE7A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)

section Transport

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem solvRad_map_of_injective (ψ : X →* Y) (hψ : Function.Injective ψ) (R : Subgroup X) :
    solvRad (R.map ψ) = (solvRad R).map ψ := by
  refine le_antisymm ?_ (A320.map_solvRad_le ψ R)
  have hle : solvRad (R.map ψ) ≤ ψ.range := (solvRad_le _).trans (Subgroup.map_le_range ψ R)
  rw [← Subgroup.map_comap_eq_self hle]
  refine Subgroup.map_mono (le_solvRad ?_ ?_ ?_)
  · intro x hx
    obtain ⟨r, hr, hrx⟩ := solvRad_le _ hx
    rwa [← hψ hrx]
  · refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hx ⊢
    push_cast
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_solvRad (Subgroup.le_normalizer ⟨g, g.2, rfl⟩) hx
  · have : Group.IsSolvable ↥(solvRad (R.map ψ)) := solvRad_isSolvable _
    exact Group.isSolvable_of_isSolvable_injective
      (f := (ψ.comp (Subgroup.subtype _)).codRestrict (solvRad (R.map ψ)) fun x => x.2)
      fun a b hab => Subtype.ext (hψ (congrArg Subtype.val hab))

theorem relIndex_solvRad_map_of_injective (ψ : X →* Y) (hψ : Function.Injective ψ)
    (V R : Subgroup X) :
    (V.map ψ ⊓ solvRad (R.map ψ)).relIndex (V.map ψ) = (V ⊓ solvRad R).relIndex V := by
  rw [solvRad_map_of_injective ψ hψ, ← Subgroup.map_inf _ _ _ hψ,
    Subgroup.relIndex_map_map_of_injective _ _ hψ]

omit [Finite X] [Finite Y] in
theorem isSolvable_map_iff (ψ : X →* Y) (hψ : Function.Injective ψ) (R : Subgroup X) :
    Group.IsSolvable ↥(R.map ψ) ↔ Group.IsSolvable ↥R := by
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (R.equivMapOfInjective ψ hψ).toMonoidHom) (MulEquiv.injective _)
  · intro h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (R.equivMapOfInjective ψ hψ).symm.toMonoidHom) (MulEquiv.injective _)

end Transport

@[expose] def OvergroupProp {P : Type*} [Group P] (q : ℕ) (W : Subgroup P) : Prop :=
  ∀ R : Subgroup P, W ≤ R → R ≤ Subgroup.normalizer (W : Set P) ∨
    (¬ Group.IsSolvable ↥R ∧ q ≤ (W ⊓ solvRad R).relIndex W)

theorem OvergroupProp.map {P : Type*} [Group P] [Finite P] {q : ℕ} {W : Subgroup P}
    (h : OvergroupProp q W) (α : P ≃* P) : OvergroupProp q (W.map α.toMonoidHom) := by
  have hback : ∀ X : Subgroup P, (X.map α.symm.toMonoidHom).map α.toMonoidHom = X := fun X => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id X
    ext x
    simp
  have hback' : ∀ X : Subgroup P, (X.map α.toMonoidHom).map α.symm.toMonoidHom = X := fun X => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id X
    ext x
    simp
  intro R hWR
  set R' := R.map α.symm.toMonoidHom with hR'
  have hWR' : W ≤ R' := by
    have := Subgroup.map_mono (f := α.symm.toMonoidHom) hWR
    rwa [hback'] at this
  have hRR : R = R'.map α.toMonoidHom := (hback R).symm
  rcases h R' hWR' with hN | ⟨hs, hc⟩
  · left
    rw [hRR, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hN
  · right
    refine ⟨fun hs' => hs ?_, ?_⟩
    · rw [hRR] at hs'
      exact (isSolvable_map_iff α.toMonoidHom α.injective R').mp hs'
    · rw [hRR, relIndex_solvRad_map_of_injective α.toMonoidHom α.injective]
      exact hc

section Lower

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_mem_normalizer {P : Type*} [Group P] (ψ : P →* G) {W : Subgroup P} {y : P}
    (hy : y ∈ Subgroup.normalizer (W : Set P)) :
    ψ y ∈ Subgroup.normalizer ((W.map ψ : Subgroup G) : Set G) := by
  rw [← A1b.conjSub_eq_iff_mem_normalizer, ← SecE3.map_conjSub,
    A1b.conjSub_eq_iff_mem_normalizer.mpr hy]

theorem not_isE_of_overgroupProp {P : Type*} [Group P] [Finite P] {L T : Subgroup G}
    [hLn : L.Normal] (hT : IsSylowIn 2 T ⊤) (ψ : P →* G) (hψ : Function.Injective ψ)
    (hψL : ψ.range = L) {n : ℕ} (hn : 1 ≤ n) {W : Subgroup P} (hWp : OvergroupProp (2 ^ n) W)
    (hAT : W.map ψ ≤ T) (hA : IsElemAbelian 2 (W.map ψ)) (K : Subgroup G) :
    ¬ IsE (n - 1) ⊤ T (W.map ψ) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨-, hτ, -, hE⟩
  set A := W.map ψ with hAdef
  have hAK : A ≤ K := (le_sup_left.trans (le_tauOf hT hAT hA)).trans (hτ.trans inf_le_right)
  have hAL : A ≤ L := hψL ▸ Subgroup.map_le_range ψ W
  set R := K ⊓ L with hRdef
  have hAR : A ≤ R := le_inf hAK hAL
  set R' := R.comap ψ with hR'def
  have hRR : R'.map ψ = R := Subgroup.map_comap_eq_self (hψL ▸ inf_le_right)
  have hWR : W ≤ R' := fun w hw => hAR ⟨w, hw, rfl⟩
  have hKR : K ≤ Subgroup.normalizer (R : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxK, hxL⟩
      exact ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), hLn.conj_mem x hxL k⟩
    · rintro ⟨hxK, hxL⟩
      refine ⟨?_, ?_⟩
      · have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
        simpa [mul_assoc] using this
      · have := hLn.conj_mem _ hxL k⁻¹
        simpa [mul_assoc] using this
  rcases hWp R' hWR with hN | ⟨hs, hc⟩
  ·
    have hRN : R ≤ Subgroup.normalizer (A : Set G) := by
      rw [← hRR]
      rintro _ ⟨y, hy, rfl⟩
      exact map_mem_normalizer ψ (hN hy)
    have hA2 := isPGroup_of_isElemAbelian hA
    have h1 : A ≤ pCoreOf 2 R := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAR hRN hA2
    have h2 : pCoreOf 2 R ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 R).trans inf_le_left)
        (hKR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 R))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R)
    have hAO : A.subgroupOf K ≤ CFSG.Open.pCore 2 ↥K := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := h2 (h1 (Subgroup.mem_subgroupOf.mp hx))
      rwa [show y = x from Subtype.ext hyx] at hy
    have hb2 : barO2 ↥K (A.subgroupOf K) = ⊥ := by
      rw [barO2, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hAO
    have hbR : barRad ↥K (A.subgroupOf K) = ⊥ := by
      rw [barRad, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hAO.trans E3.pCore_two_le_solvableRadical
    rcases hE with ⟨⟨-, -, -, -, -, -, hcard⟩, -⟩ | ⟨hE2, -⟩
    · rw [hb2, Subgroup.card_bot] at hcard
      exact absurd hcard (by norm_num)
    · exact RootLift.not_eTwo_of_barRad_eq_bot hbR hE2
  ·
    have hRs : ¬ Group.IsSolvable ↥R := fun hR =>
      hs ((isSolvable_map_iff ψ hψ R').mp (hRR ▸ hR))
    have hKs : ¬ Group.IsSolvable ↥K := fun hK => hRs
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left))
    rcases hE with ⟨hE1, -⟩ | ⟨-, hcard⟩
    · exact hKs (RootLift.isSolvable_of_eOne hE1)
    · set O : Subgroup G := (CFSG.solvableRadical ↥K).map K.subtype with hOdef
      have hOs : Group.IsSolvable ↥O := by
        have : Group.IsSolvable ↥(CFSG.solvableRadical ↥K) := A3.solvableRadical_isSolvable
        exact (isSolvable_map_iff K.subtype K.subtype_injective _).mpr this
      have hON : O.comap ψ ⊓ R' ≤ solvRad R' := by
        refine le_solvRad inf_le_right ⟨fun x hx g => ?_⟩ ?_
        · rw [Subgroup.mem_subgroupOf] at hx ⊢
          obtain ⟨hxO, hxR⟩ := hx
          refine ⟨?_, R'.mul_mem (R'.mul_mem g.2 hxR) (R'.inv_mem g.2)⟩
          obtain ⟨s, hs, hsx⟩ := hxO
          have hgK : ψ g ∈ K := (g.2 : ψ (g : P) ∈ R).1
          refine ⟨⟨ψ g, hgK⟩ * s * ⟨ψ g, hgK⟩⁻¹,
            (inferInstance : (CFSG.solvableRadical ↥K).Normal).conj_mem _ hs _, ?_⟩
          have hsx' : (s : G) = ψ x := hsx
          simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hsx', map_mul, map_mul, map_inv]
        · have h1 : (O.comap ψ ⊓ R').map ψ ≤ O := fun y ⟨x, hx, hxy⟩ => hxy ▸ hx.1
          have h2 : Group.IsSolvable ↥((O.comap ψ ⊓ R').map ψ) :=
            Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)
          exact (isSolvable_map_iff ψ hψ _).mp h2
      have hWle : O.comap ψ ⊓ W ≤ W ⊓ solvRad R' := fun x hx =>
        ⟨hx.2, hON ⟨hx.1, hWR hx.2⟩⟩
      have h3 := Subgroup.relIndex_le_of_le_left (L := W) hWle Subgroup.index_ne_zero_of_finite
      rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap] at h3
      have h4 : Nat.card ↥(barRad ↥K (A.subgroupOf K)) = O.relIndex A := by
        rw [barRad, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hOdef,
          ← Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK]
      have h5 : 2 ^ n ≤ 2 ^ (n - 1) := by
        calc 2 ^ n ≤ (W ⊓ solvRad R').relIndex W := hc
          _ ≤ O.relIndex (W.map ψ) := h3
          _ = Nat.card ↥(barRad ↥K (A.subgroupOf K)) := h4.symm
          _ ≤ 2 ^ (n - 1) := hcard
      have h6 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega

omit [Finite G] in
theorem conjSub_map_psi {P : Type*} [Group P] {L : Subgroup G} [L.Normal] (e : ↥L ≃* P)
    (x : G) (W : Subgroup P) :
    A1b.conjSub x (W.map (L.subtype.comp e.symm.toMonoidHom)) =
      (W.map ((e.symm.trans (MulAut.conjNormal x)).trans e).toMonoidHom).map
        (L.subtype.comp e.symm.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.conjNormal_apply]
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.conjNormal_apply]

theorem le_nParam_of_overgroupProp {L T : Subgroup G} (h : AlmostSimple L)
    (hT : IsSylowIn 2 T ⊤) {P : Type*} [Group P] [Finite P] (e : ↥L ≃* P) {n : ℕ} (hn : 2 ≤ n)
    {W : Subgroup P} (hW : IsElemAbelian 2 W) (hW1 : W ≠ ⊥) (hWp : OvergroupProp (2 ^ n) W) :
    (n : ℕ∞) ≤ nParam (⊤ : Subgroup G) := by
  have hLn := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : P →* G := L.subtype.comp e.symm.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := L.subtype_injective.comp e.symm.injective
  have hψL : ψ.range = L := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set A₀ := W.map ψ with hA₀
  have hA₀e : IsElemAbelian 2 A₀ := isElemAbelian_map' ψ hW
  obtain ⟨g₀, hg₀⟩ := exists_conjSub_le_of_isSylowIn hT (isPGroup_of_isElemAbelian hA₀e)
  set A := A1b.conjSub g₀ A₀ with hAdef
  have hAe : IsElemAbelian 2 A := SecU1.isElemAbelian_conjSub hA₀e g₀
  have hA1 : A ≠ ⊥ := by
    intro h0
    apply hW1
    have h1 : A₀ = ⊥ := by
      have := congrArg (A1b.conjSub g₀⁻¹) h0
      rwa [hAdef, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one, A1b.conjSub,
        Subgroup.map_bot] at this
    rwa [hA₀, Subgroup.map_eq_bot_iff_of_injective _ hψ] at h1
  refine le_nParam_of_forall_not_isE hn hT (fun N hN h2 => eq_bot_of_normal_of_isPGroup h hN h2)
    hg₀ hAe hA1 fun g hgT K hK => ?_
  have hc := conjSub_map_psi e (g * g₀) W
  rw [A1b.conjSub_mul] at hc
  rw [hAdef, hc] at hgT hK
  exact not_isE_of_overgroupProp hT ψ hψ hψL (by omega) (hWp.map _) hgT
    (isElemAbelian_map' ψ (isElemAbelian_map' _ hW)) K hK

end Lower

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
