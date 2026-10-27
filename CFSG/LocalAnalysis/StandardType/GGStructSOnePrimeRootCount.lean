module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRoot
public import CFSG.LieType.ChevTwo.LayeredCount

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo CFSG.ComponentClassification

section General

variable {X : Type} [Group X]

@[expose] def GGInvolCentTypedBy (G₀ : Subgroup X) (r : X) (o : List ℕ) : Prop :=
  CFSG.LieType.ChevTwo.IsChevTwoLayeredBy (GGInvolCentBar G₀ r) o

end General

section Centralizer

variable {C : Type} [Group C]

@[expose] def GGRootCentQLTypedBy (z : C) (o : List ℕ) : Prop :=
  ∃ Q L : Subgroup C, IsPGroup 2 Q ∧ Q ⊔ L = Subgroup.centralizer ({z} : Set C) ∧
    L ≤ Subgroup.normalizer (Q : Set C) ∧ CFSG.LieType.ChevTwo.IsChevTwoLayeredBy ↥L o

theorem GGRootCentQLTypedBy.map {C' : Type} [Group C'] {z : C} {o : List ℕ}
    (h : GGRootCentQLTypedBy z o) (α : C ≃* C') : GGRootCentQLTypedBy (α z) o := by
  obtain ⟨Q, L, hQ2, hQL, hLQ, hL⟩ := h
  refine ⟨Q.map α.toMonoidHom, L.map α.toMonoidHom, hQ2.map _, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hQL, RootCentExc.centralizer_map_mulEquiv]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hLQ
  · exact IsChevTwoLayeredBy.of_mulEquiv
      (L.equivMapOfInjective α.toMonoidHom α.injective).symm hL

end Centralizer

section Counts

@[expose] def ggSpLayerOrd (m q : ℕ) : ℕ := if m = 2 ∧ q = 2 then 360 else CFSG.Open.ordBC m q

@[expose] def ggRootFactorOrders : CFSG.Open.StatedLieTag → ℕ → ℕ → List (List ℕ)
  | .PSL, n, f => [[CFSG.Open.ordA (n - 3) (2 ^ f)]]
  | .PSU, n, f => [[CFSG.Open.ordTwistedA (n - 3) (2 ^ f)]]
  | .PSp, n, f => [[ggSpLayerOrd (n - 1) (2 ^ f)],
      if n = 2 then [CFSG.Open.ordA 1 (2 ^ f)]
      else [CFSG.Open.ordA 1 (2 ^ f), ggSpLayerOrd (n - 2) (2 ^ f)]]
  | .POmegaPlus, n, f => [if n = 4 then
        [CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordA 1 (2 ^ f)]
      else [CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordD (n - 2) (2 ^ f)]]
  | .POmegaMinus, n, f => [[CFSG.Open.ordA 1 (2 ^ f), CFSG.Open.ordTwistedD (n - 2) (2 ^ f)]]
  | .F4, _, f => [[CFSG.Open.ordBC 3 (2 ^ f)]]
  | .E6, _, f => [[CFSG.Open.ordA 5 (2 ^ f)]]
  | .E7, _, f => [[CFSG.Open.ordD 6 (2 ^ f)]]
  | .E8, _, f => [[CFSG.Open.ordE7 (2 ^ f)]]
  | .twistedE6, _, f => [[CFSG.Open.ordTwistedA 5 (2 ^ f)]]
  | _, _, _ => []

end Counts

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem ggInvolCentTypedBy_map_iff_of_injective (φ : X →* X') (hφ : Function.Injective φ)
    (G₀ : Subgroup X) (r : X) (o : List ℕ) :
    GGInvolCentTypedBy (G₀.map φ) (φ r) o ↔ GGInvolCentTypedBy G₀ r o := by
  let A : Subgroup X := Subgroup.centralizer ({r} : Set X) ⊓ G₀
  have hB : Subgroup.centralizer ({φ r} : Set X') ⊓ G₀.map φ = A.map φ := by
    have hle : G₀.map φ ≤ φ.range := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, rfl⟩
    rw [inf_comm, ← inf_eq_left.mpr hle, inf_assoc,
      ggRCQL_range_inf_centralizer hφ r, Subgroup.map_inf _ _ φ hφ]
    simp [A, inf_comm]
  let e : ↥A ≃* ↥(A.map φ) := Subgroup.equivMapOfInjective A φ hφ
  have hpc : (CFSG.Open.pCore 2 ↥A).map e.toMonoidHom =
      CFSG.Open.pCore 2 ↥(A.map φ) := CFSG.pCore_map_iso 2 e
  have hq : IsChevTwoLayeredBy (↥A ⧸ CFSG.Open.pCore 2 ↥A) o ↔
      IsChevTwoLayeredBy (↥(A.map φ) ⧸ CFSG.Open.pCore 2 ↥(A.map φ)) o :=
    IsChevTwoLayeredBy.mulEquiv_iff (QuotientGroup.congr (CFSG.Open.pCore 2 ↥A)
      (CFSG.Open.pCore 2 ↥(A.map φ)) e hpc)
  have hq' : IsChevTwoLayeredBy
      (↥(Subgroup.centralizer ({φ r} : Set X') ⊓ G₀.map φ) ⧸
        CFSG.Open.pCore 2 ↥(Subgroup.centralizer ({φ r} : Set X') ⊓ G₀.map φ)) o ↔
      IsChevTwoLayeredBy (↥A ⧸ CFSG.Open.pCore 2 ↥A) o := by
    rw [hB]
    exact hq.symm
  simpa [GGInvolCentTypedBy, GGInvolCentBar, A] using hq'

theorem ggInvolCentTypedBy_conj_iff {G₀ : Subgroup X} {r g : X} (o : List ℕ)
    (hg : g ∈ Subgroup.normalizer (G₀ : Set X)) :
    GGInvolCentTypedBy G₀ (g * r * g⁻¹) o ↔ GGInvolCentTypedBy G₀ r o := by
  have h := ggInvolCentTypedBy_map_iff_of_injective (G₀ := G₀) (r := r)
    (φ := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective o
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom G₀ = G₀ := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.1 hg)
  rw [hmap] at h
  simpa [MulAut.conj_apply] using h

private theorem ggInvolCentTypedBy_congr_aux {G₀ G₁ : Subgroup X} {r r' : X} {o : List ℕ}
    (hG : G₀ = G₁)
    (h : Subgroup.centralizer ({r} : Set X) ⊓ G₁ =
      Subgroup.centralizer ({r'} : Set X) ⊓ G₁) :
    GGInvolCentTypedBy G₀ r o ↔ GGInvolCentTypedBy G₁ r' o := by
  let A : Subgroup X := Subgroup.centralizer ({r} : Set X) ⊓ G₀
  let B : Subgroup X := Subgroup.centralizer ({r'} : Set X) ⊓ G₁
  have hAB : A = B := by
    dsimp only [A, B]
    rw [hG, h]
  let e : ↥A ≃* ↥B := MulEquiv.subgroupCongr hAB
  have hpc : (CFSG.Open.pCore 2 ↥A).map e.toMonoidHom = CFSG.Open.pCore 2 ↥B :=
    CFSG.pCore_map_iso 2 e
  have hq : IsChevTwoLayeredBy (↥A ⧸ CFSG.Open.pCore 2 ↥A) o ↔
      IsChevTwoLayeredBy (↥B ⧸ CFSG.Open.pCore 2 ↥B) o :=
    IsChevTwoLayeredBy.mulEquiv_iff
      (QuotientGroup.congr (CFSG.Open.pCore 2 ↥A) (CFSG.Open.pCore 2 ↥B) e hpc)
  simpa [GGInvolCentTypedBy, GGInvolCentBar, A, B] using hq

theorem ggInvolCentTypedBy_congr {G₀ : Subgroup X} {r r' : X} {o : List ℕ}
    (h : Subgroup.centralizer ({r} : Set X) ⊓ G₀ =
      Subgroup.centralizer ({r'} : Set X) ⊓ G₀) :
    GGInvolCentTypedBy G₀ r o ↔ GGInvolCentTypedBy G₀ r' o :=
  ggInvolCentTypedBy_congr_aux rfl h

private theorem ggInvolCentTypedBy_subgroup_congr {G₀ G₁ : Subgroup X} {r : X} {o : List ℕ}
    (h : G₀ = G₁) : GGInvolCentTypedBy G₀ r o ↔ GGInvolCentTypedBy G₁ r o :=
  ggInvolCentTypedBy_congr_aux h rfl

theorem ggInvolCentTypedBy_range_of_top {U X : Type} [Group U] [Group X]
    {ψ : U →* X} (hψ : Function.Injective ψ) {y : U} {o : List ℕ}
    (h : GGInvolCentTypedBy (⊤ : Subgroup U) y o) : GGInvolCentTypedBy ψ.range (ψ y) o :=
  (ggInvolCentTypedBy_subgroup_congr (Subgroup.map_top ψ)).mp
    ((ggInvolCentTypedBy_map_iff_of_injective ψ hψ (⊤ : Subgroup U) y o).2 h)

end Transport

section Reductions

variable {X : Type} [Group X] [Finite X]

private theorem pCore_subgroupOf_eq_of_normal {W : Type} [Group W] {N V : Subgroup W}
    (hNV : N ≤ V) (hNVn : (N.subgroupOf V).Normal) :
    CFSG.Open.pCore 2 ↥(N.subgroupOf V) =
      (CFSG.Open.pCore 2 ↥V).subgroupOf (N.subgroupOf V) := by
  apply le_antisymm
  · haveI := hNVn
    haveI hchar : (CFSG.Open.pCore 2 ↥(N.subgroupOf V)).Characteristic :=
      CFSG.pCore_characteristic
    have hmapn : ((CFSG.Open.pCore 2 ↥(N.subgroupOf V)).map (N.subgroupOf V).subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hmaple : (CFSG.Open.pCore 2 ↥(N.subgroupOf V)).map (N.subgroupOf V).subtype ≤
        CFSG.Open.pCore 2 ↥V := by
      unfold CFSG.Open.pCore
      exact le_sSup ⟨hmapn, (CFSG.pCore_isPGroup (G := ↥(N.subgroupOf V))).map _⟩
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hmaple (Subgroup.mem_map_of_mem _ hx))
  · intro x hx
    unfold CFSG.Open.pCore
    refine le_sSup (show (CFSG.Open.pCore 2 ↥V).subgroupOf (N.subgroupOf V) ∈
      {K : Subgroup ↥(N.subgroupOf V) | K.Normal ∧ IsPGroup 2 K} from ⟨?_, ?_⟩) hx
    · exact (CFSG.pCore_normal (p := 2) (G := ↥V)).subgroupOf (N.subgroupOf V)
    · let ψ : ↥((CFSG.Open.pCore 2 ↥V).subgroupOf (N.subgroupOf V)) →*
          ↥(CFSG.Open.pCore 2 ↥V) :=
        { toFun := fun x => ⟨(x.1 : ↥V), x.2⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl }
      exact IsPGroup.of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥V)) ψ
        (fun a b h => Subtype.ext (Subtype.ext
          (congrArg (fun z : ↥(CFSG.Open.pCore 2 ↥V) => (z : ↥V)) h)))

private theorem isChevTwoLayeredBy_quotient_pCore_of_isPGroup {G : Type} [Group G] [Finite G]
    {N Q : Subgroup G} (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q)
    (hQnorm : N ≤ Subgroup.normalizer (Q : Set G)) [hQn : (Q.subgroupOf N).Normal]
    {o : List ℕ} (hNQ : IsChevTwoLayeredBy (↥N ⧸ Q.subgroupOf N) o) :
    IsChevTwoLayeredBy (↥N ⧸ CFSG.Open.pCore 2 ↥N) o := by
  have hQp : IsPGroup 2 ↥(Q.subgroupOf N) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  have hQle : Q.subgroupOf N ≤ CFSG.Open.pCore 2 ↥N := by
    unfold CFSG.Open.pCore
    exact le_sSup ⟨hQn, hQp⟩
  let T : Subgroup (↥N ⧸ Q.subgroupOf N) :=
    (CFSG.Open.pCore 2 ↥N).map (QuotientGroup.mk' (Q.subgroupOf N))
  have hTn : T.Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥N)).map _ (QuotientGroup.mk'_surjective _)
  haveI := hTn
  have hTp : IsPGroup 2 ↥T :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥N)).map _
  have hTsolv : Group.IsSolvable ↥T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥T := hTp.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hquot : IsChevTwoLayeredBy ((↥N ⧸ Q.subgroupOf N) ⧸ T) o :=
    hNQ.quotient T hTsolv
  have e : ((↥N ⧸ Q.subgroupOf N) ⧸ T) ≃*
      (↥N ⧸ CFSG.Open.pCore 2 ↥N) :=
    QuotientGroup.quotientQuotientEquivQuotient (Q.subgroupOf N)
      (CFSG.Open.pCore 2 ↥N) hQle
  exact hquot.of_mulEquiv e.symm

theorem ggInvolCentTypedBy_of_normal {G₀ : Subgroup X} {r : X} {N Q : Subgroup X}
    (hNV : N ≤ Subgroup.centralizer ({r} : Set X) ⊓ G₀)
    (hNnormal : (N.subgroupOf (Subgroup.centralizer ({r} : Set X) ⊓ G₀)).Normal)
    (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q)
    (hQnorm : N ≤ Subgroup.normalizer (Q : Set X)) [hQn : (Q.subgroupOf N).Normal]
    {o : List ℕ} (hNQ : IsChevTwoLayeredBy (↥N ⧸ Q.subgroupOf N) o)
    (hVNsolv : Group.IsSolvable
      (↥(Subgroup.centralizer ({r} : Set X) ⊓ G₀) ⧸
        N.subgroupOf (Subgroup.centralizer ({r} : Set X) ⊓ G₀))) :
    GGInvolCentTypedBy G₀ r o := by
  let V : Subgroup X := Subgroup.centralizer ({r} : Set X) ⊓ G₀
  let O : Subgroup ↥V := CFSG.Open.pCore 2 ↥V
  let Nv : Subgroup ↥V := N.subgroupOf V
  let Qv : Subgroup ↥V := Q.subgroupOf V
  have hQV : Q ≤ V := hQN.trans hNV
  have hQvNv : Qv ≤ Nv := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hQN (Subgroup.mem_subgroupOf.mp hx))
  have hQvNv_normal : (Qv.subgroupOf Nv).Normal := by
    have h := hQn.comap (Subgroup.subgroupOfEquivOfLe hNV).toMonoidHom
    convert h using 1
    ext x
    rfl
  have hQvnorm : Nv ≤ Subgroup.normalizer (Qv : Set ↥V) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQvNv).1 hQvNv_normal
  have hQ2v : IsPGroup 2 Qv :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQV).symm
  have hNQv : IsChevTwoLayeredBy (↥Nv ⧸ Qv.subgroupOf Nv) o := by
    let e : ↥Nv ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNV
    have he : Subgroup.map e.toMonoidHom (Qv.subgroupOf Nv) = Q.subgroupOf N := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        refine ⟨⟨⟨x.1, hNV x.2⟩, x.2⟩, ?_, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hx
    let ebar : (↥Nv ⧸ Qv.subgroupOf Nv) ≃* (↥N ⧸ Q.subgroupOf N) :=
      QuotientGroup.congr (Qv.subgroupOf Nv) (Q.subgroupOf N) e he
    exact hNQ.of_mulEquiv ebar
  have hNvQv : IsChevTwoLayeredBy (↥Nv ⧸ CFSG.Open.pCore 2 ↥Nv) o :=
    isChevTwoLayeredBy_quotient_pCore_of_isPGroup hQvNv hQ2v hQvnorm hNQv
  have hpCoreEq : CFSG.Open.pCore 2 ↥Nv = O.subgroupOf Nv :=
    pCore_subgroupOf_eq_of_normal hNV hNnormal
  have hNvO : IsChevTwoLayeredBy (↥Nv ⧸ O.subgroupOf Nv) o :=
    hNvQv.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpCoreEq).symm
  let π : ↥V →* ↥V ⧸ O := QuotientGroup.mk' O
  let f : ↥Nv →* ↥V ⧸ O := π.comp Nv.subtype
  have hMdef : f.range = Nv.map π := by
    rw [show f = π.comp Nv.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hMn : f.range.Normal := by
    rw [hMdef]
    exact hNnormal.map π (QuotientGroup.mk'_surjective O)
  have hMlayer : IsChevTwoLayeredBy ↥f.range o := by
    have hfker : f.ker = O.subgroupOf Nv := by
      ext x
      constructor
      · intro hx
        exact (QuotientGroup.eq_one_iff (x : ↥V)).mp (by
          change QuotientGroup.mk' O (x : ↥V) = 1
          exact MonoidHom.mem_ker.mp hx)
      · intro hx
        change QuotientGroup.mk' O (x : ↥V) = 1
        exact (QuotientGroup.eq_one_iff (x : ↥V)).mpr (Subgroup.mem_subgroupOf.mp hx)
    have e : (↥Nv ⧸ O.subgroupOf Nv) ≃* ↥f.range :=
      (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
        (QuotientGroup.quotientKerEquivRange f)
    exact hNvO.of_mulEquiv e.symm
  have hMn' : f.range = (Nv ⊔ O).map π := by
    rw [hMdef, Subgroup.map_sup]
    have hO : O.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hO, sup_bot_eq]
  have hsolv : Group.IsSolvable (↥V ⧸ (Nv ⊔ O)) := by
    have hmap : Function.Surjective (QuotientGroup.map Nv (Nv ⊔ O) (MonoidHom.id ↥V)
        (by simpa using (show Nv ≤ Nv ⊔ O from fun x hx => Subgroup.mem_sup_left hx))) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Nv ⊔ O) y
      refine ⟨QuotientGroup.mk' Nv x, ?_⟩
      rw [QuotientGroup.map_mk']
      rfl
    haveI : Group.IsSolvable (↥V ⧸ Nv) := hVNsolv
    exact Group.isSolvable_of_surjective hmap
  haveI hNvNormal : Nv.Normal := hNnormal
  haveI hONormal : O.Normal := CFSG.pCore_normal
  have hquot : Group.IsSolvable ((↥V ⧸ O) ⧸ f.range) := by
    have hker : Nv ⊔ O ≤ Subgroup.comap (QuotientGroup.mk' O) f.range := by
      intro x hx
      obtain ⟨n, hn, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      have hn' : QuotientGroup.mk' O n ∈ f.range := by
        rw [hMdef]
        exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hn
      have ho' : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).2 ho
      change QuotientGroup.mk' O (n * o) ∈ f.range
      rw [map_mul, ho', mul_one]
      exact hn'
    let φ : (↥V ⧸ (Nv ⊔ O)) →* ((↥V ⧸ O) ⧸ f.range) :=
      QuotientGroup.map (Nv ⊔ O) f.range (QuotientGroup.mk' O) hker
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective f.range y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O z
      refine ⟨QuotientGroup.mk' (Nv ⊔ O) x, ?_⟩
      exact QuotientGroup.map_mk' (Nv ⊔ O) f.range (QuotientGroup.mk' O) hker x
    haveI : Group.IsSolvable (↥V ⧸ (Nv ⊔ O)) := hsolv
    exact Group.isSolvable_of_surjective hφ
  haveI := hMn
  exact IsChevTwoLayeredBy.of_normal_of_solvable_quotient f.range hMlayer hquot

theorem ggInvolCentTypedBy_of_sup_eq {G₀ : Subgroup X} {r : X} {Q L : Subgroup X}
    {o : List ℕ} (hQ2 : IsPGroup 2 Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set X))
    (hQL : Q ⊔ L = Subgroup.centralizer ({r} : Set X) ⊓ G₀)
    (hL : IsChevTwoLayeredBy ↥L o) : GGInvolCentTypedBy G₀ r o := by
  let V : Subgroup X := Subgroup.centralizer ({r} : Set X) ⊓ G₀
  have hQV : Q ≤ V := by
    change Q ≤ Subgroup.centralizer ({r} : Set X) ⊓ G₀
    rw [← hQL]
    exact le_sup_left
  have hLV : L ≤ V := by
    change L ≤ Subgroup.centralizer ({r} : Set X) ⊓ G₀
    rw [← hQL]
    exact le_sup_right
  have hVnormal : (V.subgroupOf V).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hQnorm : V ≤ Subgroup.normalizer (Q : Set X) := by
    change Subgroup.centralizer ({r} : Set X) ⊓ G₀ ≤ Subgroup.normalizer (Q : Set X)
    rw [← hQL]
    exact sup_le Subgroup.le_normalizer hLQ
  haveI : (Q.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQV).2 hQnorm
  have hVQ : IsChevTwoLayeredBy (↥V ⧸ Q.subgroupOf V) o := by
    have hsup : L.subgroupOf V ⊔ Q.subgroupOf V = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLV hQV, sup_comm, hQL]
      change V.subgroupOf V = ⊤
      rw [Subgroup.subgroupOf_self]
    have hL' : IsChevTwoLayeredBy ↥(L.subgroupOf V) o :=
      hL.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLV)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 ↥(Q.subgroupOf V) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQV).symm
    have hQsolv : Group.IsSolvable ↥(Q.subgroupOf V) := by
      haveI : Group.IsNilpotent ↥(Q.subgroupOf V) := hQp.isNilpotent
      exact IsNilpotent.to_isSolvable
    exact hL'.quotient_of_sup_eq_top hQsolv hsup
  have hVVsolv : Group.IsSolvable (↥V ⧸ V.subgroupOf V) :=
    Group.isSolvable_of_comm fun a b => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf V) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf V) b
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_eq_mk']
      refine ⟨(x * y)⁻¹ * (y * x), ?_, by group⟩
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
  exact @ggInvolCentTypedBy_of_normal X _ _ G₀ r V Q le_rfl hVnormal hQV hQ2 hQnorm
    (inferInstance : (Q.subgroupOf V).Normal) o hVQ hVVsolv

theorem ggInvolCentTypedBy_of_oTwoPrime_eq_sup {G₀ : Subgroup X} {r : X} {Q L : Subgroup X}
    {o : List ℕ} (hQ2 : IsPGroup 2 Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set X))
    (hX : ggRCSX G₀ r = Q ⊔ L) (hL : IsChevTwoLayeredBy ↥L o) :
    GGInvolCentTypedBy G₀ r o := by
  let V : Subgroup X := Subgroup.centralizer ({r} : Set X) ⊓ G₀
  let N : Subgroup X := ggRCSX G₀ r
  have hYV : G₀ ⊓ Subgroup.centralizer ({r} : Set X) = V := by
    simp [V, inf_comm]
  have hNle : N ≤ V := by
    rw [show N = ggOTwoPrime (G₀ ⊓ Subgroup.centralizer ({r} : Set X)) from rfl, hYV]
    exact ggOTwoPrime_le _
  have hNnormal : (N.subgroupOf V).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNle]
    intro v hv
    have hvY : v ∈ G₀ ⊓ Subgroup.centralizer ({r} : Set X) := by
      rw [hYV]
      exact hv
    exact ggMem_normalizer_oTwoPrime (Subgroup.le_normalizer hvY)
  have hQN : Q ≤ N := by
    change Q ≤ ggRCSX G₀ r
    rw [hX]
    exact le_sup_left
  have hLN : L ≤ N := by
    change L ≤ ggRCSX G₀ r
    rw [hX]
    exact le_sup_right
  have hQnorm : N ≤ Subgroup.normalizer (Q : Set X) := by
    change ggRCSX G₀ r ≤ Subgroup.normalizer (Q : Set X)
    rw [hX]
    exact sup_le Subgroup.le_normalizer hLQ
  haveI hQn : (Q.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 hQnorm
  have hNQ : IsChevTwoLayeredBy (↥N ⧸ Q.subgroupOf N) o := by
    have hsup : L.subgroupOf N ⊔ Q.subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLN hQN, sup_comm, ← hX]
      change N.subgroupOf N = ⊤
      rw [Subgroup.subgroupOf_self]
    have hL' : IsChevTwoLayeredBy ↥(L.subgroupOf N) o :=
      hL.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 ↥(Q.subgroupOf N) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
    have hQsolv : Group.IsSolvable ↥(Q.subgroupOf N) := by
      haveI : Group.IsNilpotent ↥(Q.subgroupOf N) := hQp.isNilpotent
      exact IsNilpotent.to_isSolvable
    exact hL'.quotient_of_sup_eq_top hQsolv hsup
  have hgen_le : ggOTwoPrime V ≤ N := by
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro y ⟨hyV, k, hk⟩
    rw [show N = ggOTwoPrime (G₀ ⊓ Subgroup.centralizer ({r} : Set X)) from rfl]
    exact Subgroup.subset_closure ⟨by rw [hYV]; exact hyV, k, hk⟩
  have hodd_order : ∀ x : ↥V ⧸ N.subgroupOf V, Odd (orderOf x) := by
    intro x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf V) x
    obtain ⟨k, m, hm, horder⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos v).ne'
    have hvm : (v ^ m : X) ∈ ggOTwoPrime V := by
      refine Subgroup.subset_closure ⟨V.pow_mem v.2 m, k, ?_⟩
      rw [← pow_mul, mul_comm m (2 ^ k), ← horder, ← Subgroup.orderOf_coe v,
        pow_orderOf_eq_one]
    have hx : (QuotientGroup.mk' (N.subgroupOf V) v) ^ m = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hgen_le hvm)
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hx)
  have hodd : Odd (Nat.card (↥V ⧸ N.subgroupOf V)) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (Even.two_dvd heven)
    have hxodd := hodd_order x
    rw [hx] at hxodd
    exact (by norm_num : ¬ Odd 2) hxodd
  have hVNsolv : Group.IsSolvable (↥V ⧸ N.subgroupOf V) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact ggInvolCentTypedBy_of_normal hNle hNnormal hQN hQ2 hQnorm hNQ hVNsolv

theorem ggInvolCentTypedBy_of_model {U C : Type} [Group U] [Group C]
    {ψ : U →* X} {π : U →* C} (hπ : Function.Surjective π) (hker : π.ker = ψ.ker)
    {w : U} {o : List ℕ} (hw : GGRootCentQLTypedBy (π w) o) :
    GGInvolCentTypedBy ψ.range (ψ w) o := by
  set Θ := AutSt.modelEquiv ψ π hπ hker with hΘ
  let Θ' : C →* X := ψ.range.subtype.comp Θ.toMonoidHom
  have hΘ' : Θ' (π w) = ψ w := AutSt.modelEquiv_apply ψ π hπ hker w
  have hinj : Function.Injective Θ' := Subtype.val_injective.comp Θ.injective
  have hrange : Θ'.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact (Θ c).2
    · intro hx
      exact ⟨Θ.symm ⟨x, hx⟩, by simp [Θ']⟩
  obtain ⟨Q, L, hQ2, hQL, hLQ, hL⟩ := hw
  have hC := ggRCQL_range_inf_centralizer hinj (π w)
  rw [hrange, hΘ'] at hC
  refine ggInvolCentTypedBy_of_sup_eq (hQ2.map Θ') ?_ ?_
    (IsChevTwoLayeredBy.of_mulEquiv (L.equivMapOfInjective Θ' hinj).symm hL)
  · exact ggRCST_map_le_normalizer Θ' hLQ
  · rw [inf_comm, hC, ← hQL, Subgroup.map_sup]

end Reductions

section Tags

@[expose] def GGRootInvolCountTag (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X),
    CFSG.Open.StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set X) = ⊥ →
    ∀ r : X, GGRootInvolution (ggU t n f).D t ψ r →
      ∃ o ∈ ggRootFactorOrders t n f, GGInvolCentTypedBy ψ.range r o

@[expose] def GGRootInvolModelCountTag (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X),
    CFSG.Open.StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set X) = ⊥ →
    ∀ r : X, GGRootInvolution (ggU t n f).D t ψ r →
      ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C) (w : (ggU t n f).K),
        Function.Surjective π ∧ π.ker = ψ.ker ∧ ψ w = r ∧
          ∃ o ∈ ggRootFactorOrders t n f, GGRootCentQLTypedBy (π w) o

theorem ggRootInvolCountTag_of_placeholder (t : CFSG.Open.StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootInvolCountTag t := by
  intro X _ _ n f ψ _ hrk _ _ r _
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggRootInvolCountTag_POmegaOdd : GGRootInvolCountTag .POmegaOdd := by
  intro X _ _ n f ψ hadm
  exact absurd rfl hadm.2.2.2

theorem ggRootInvolCountTag_of_modelCount {t : CFSG.Open.StatedLieTag}
    (h : GGRootInvolModelCountTag t) : GGRootInvolCountTag t := by
  intro X _ _ n f ψ hadm hrk hker hC r hroot
  obtain ⟨C, _, π, w, hπ, hker', hw, o, ho, htyped⟩ :=
    h X n f ψ hadm hrk hker hC r hroot
  rw [← hw]
  exact ⟨o, ho, ggInvolCentTypedBy_of_model hπ hker' htyped⟩

end Tags

end CFSG.StandardType
