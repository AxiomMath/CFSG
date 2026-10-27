module

public import CFSG.Quasithin.Background.B2FactorizationBaumannVar
public import CFSG.Quasithin.H13.GoldschmidtC137Iso
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftXEmbed

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.Lift

variable {G : Type} [Group G]

@[expose] noncomputable def starPreIn {V : Subgroup G} (hV : IsElemAbelian 2 V) (M : Subgroup G)
    (Y : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  M ⊓ (Y.comap (convI hV)).map (normalizer (V : Set G)).subtype

theorem mem_starPreIn {V : Subgroup G} {hV : IsElemAbelian 2 V} {M : Subgroup G}
    {Y : Subgroup (MulAut (IntMod V hV))} {g : G} :
    g ∈ starPreIn hV M Y ↔ g ∈ M ∧ ∃ hg : g ∈ normalizer (V : Set G), convI hV ⟨g, hg⟩ ∈ Y := by
  unfold starPreIn
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨hM, ⟨h, hh, rfl⟩⟩
    exact ⟨hM, h.2, hh⟩
  · rintro ⟨hM, hg, hY⟩
    exact ⟨hM, ⟨g, hg⟩, hY, rfl⟩

section Transport

variable [Finite G] {X V : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_subgroupOf (hV : IsElemAbelian 2 V) :
    IsElemAbelian 2 (V.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hV X

omit [Finite G] in
theorem isPGroup_subgroupOf {K : Subgroup G} (hKX : K ≤ X) (hK : IsPGroup 2 K) :
    IsPGroup 2 (K.subgroupOf X) :=
  hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKX).symm

omit [Finite G] in
theorem pCoreOf_subgroupOf_eq {K : Subgroup G} (hKX : K ≤ X) :
    pCoreOf 2 (K.subgroupOf X) = (pCoreOf 2 K).subgroupOf X := by
  have h := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 X (K.subgroupOf X)
  rw [Subgroup.map_subgroupOf_eq_of_le hKX] at h
  rw [← h]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm

omit [Finite G] in
theorem inf_subgroupOf_eq (A B : Subgroup G) :
    (A ⊓ B).subgroupOf X = A.subgroupOf X ⊓ B.subgroupOf X :=
  Subgroup.comap_inf _ _ _

omit [Finite G] in
theorem centralizer_subgroupOf_eq (hVX : V ≤ X) :
    Subgroup.centralizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (Subgroup.centralizer (V : Set G)).subgroupOf X := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have := h ⟨v, hVX hv⟩ (Subgroup.mem_subgroupOf.2 hv)
    exact congrArg Subtype.val this
  · intro h v hv
    exact Subtype.ext (h (v : G) (Subgroup.mem_subgroupOf.1 hv))

omit [Finite G] in
theorem thompsonJ_subgroupOf_eq {R : Subgroup G} (hRX : R ≤ X) :
    thompsonJ (R.subgroupOf X) = (thompsonJ R).subgroupOf X := by
  have h1 : (thompsonJ (R.subgroupOf X)).map X.subtype = thompsonJ R := by
    rw [← thompsonJ_map_of_injective' X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hRX]
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm

omit [Finite G] in
theorem baum_subgroupOf_eq {R : Subgroup G} (hRX : R ≤ X) :
    baum (R.subgroupOf X) = (baum R).subgroupOf X := by
  have h1 : (baum (R.subgroupOf X)).map X.subtype = baum R := by
    rw [← baum_map_of_injective X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hRX]
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm

omit [Finite G] in
theorem isSylowTwoOf_subgroupOf_iff {K H : Subgroup G} (hKH : K ≤ H) (hHX : H ≤ X) :
    IsSylowTwoOf (K.subgroupOf X) (H.subgroupOf X) ↔ IsSylowTwoOf K H := by
  have hKX : K ≤ X := hKH.trans hHX
  have hidx : (K.subgroupOf X).relIndex (H.subgroupOf X) = K.relIndex H := by
    have := Subgroup.relIndex_map_map_of_injective (f := X.subtype) (K.subgroupOf X)
      (H.subgroupOf X) X.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKX, Subgroup.map_subgroupOf_eq_of_le hHX] at this
    exact this.symm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hKH, ?_, ?_⟩
    · exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe hKX)
    · intro h
      apply h3
      show 2 ∣ (K.subgroupOf X).relIndex (H.subgroupOf X)
      rw [hidx]
      exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun x hx => h1 hx, isPGroup_subgroupOf hKX h2, ?_⟩
    intro h
    apply h3
    show 2 ∣ K.relIndex H
    rw [← hidx]
    exact h

omit [Finite G] in
theorem isElemAbelian_map_subtype {E : Subgroup ↥X} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map X.subtype) := CFSG.Open.IsElemAbelian.map hE _

theorem pRank_subgroupOf_eq {K : Subgroup G} (hKX : K ≤ X) :
    CFSG.Open.pRank 2 (K.subgroupOf X) = CFSG.Open.pRank 2 K := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hEK, hE, hk⟩
    refine ⟨E.map X.subtype, ?_, isElemAbelian_map_subtype hE, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hEK hy
    · rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact hk
  · rintro ⟨E, hEK, hE, hk⟩
    have hEX : E ≤ X := hEK.trans hKX
    refine ⟨E.subgroupOf X, fun x hx => hEK hx, isElemAbelian_subgroupOf hE, ?_⟩
    rw [← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv

@[expose] def ivEquiv (hV : IsElemAbelian 2 V) (hVX : V ≤ X) :
    IntMod V hV ≃* IntMod (V.subgroupOf X) (isElemAbelian_subgroupOf hV) :=
  vEquiv hVX

omit [Finite G] in
theorem autI_subgroupOf_eq (hV : IsElemAbelian 2 V) (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G)) {K : Subgroup G} (hKX : K ≤ X) :
    autI (isElemAbelian_subgroupOf hV) (K.subgroupOf X) =
      (autI hV K).map (theta (ivEquiv hV hVX)).toMonoidHom :=
  autOn_subgroupOf hVX hXN hKX

omit [Finite G] in
theorem theta_symm_starHom (hV : IsElemAbelian 2 V) (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G)) (x : ↥X) :
    (theta (ivEquiv hV hVX)).symm (B2F.starHom (isElemAbelian_subgroupOf hV)
      (B2F.mem_normalizer_of_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer hVX).2 hXN))
      x) = convI hV ⟨(x : G), hXN x.2⟩ := by
  apply MulEquiv.ext
  intro v
  apply IntMod.val_injective
  rw [theta_symm_apply, convI_apply_val]
  show ((((convI (isElemAbelian_subgroupOf hV)) ⟨(x : ↥X), _⟩) ((ivEquiv hV hVX) v)).val : ↥X) =
    (x : G) * v.val * (x : G)⁻¹
  rw [convI_apply_val]
  rfl

omit [Finite G] in
theorem starPre_eq (hV : IsElemAbelian 2 V) (hVX : V ≤ X) (hXN : X ≤ normalizer (V : Set G))
    (M : Subgroup G) (Y : Subgroup (MulAut (IntMod V hV))) :
    B2F.starPre (isElemAbelian_subgroupOf hV)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVX).2 hXN) (M.subgroupOf X)
      (Y.map (theta (ivEquiv hV hVX)).toMonoidHom) = (starPreIn hV M Y).subgroupOf X := by
  ext x
  rw [B2F.mem_starPre, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_starPreIn]
  constructor
  · rintro ⟨hM, hY⟩
    refine ⟨hM, hXN x.2, ?_⟩
    rw [mem_map_theta, theta_symm_starHom hV hVX hXN] at hY
    exact hY
  · rintro ⟨hM, hg, hY⟩
    refine ⟨hM, ?_⟩
    rw [mem_map_theta, theta_symm_starHom hV hVX hXN]
    exact hY

end Transport

end CFSG.Quasithin.H13.U3.GC137
