module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootBasic
public import CFSG.LieType.ChevTwo.LayeredOps
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem ggInvolCentTyped_map_iff_of_injective (φ : X →* X') (hφ : Function.Injective φ)
    (G₀ : Subgroup X) (r : X) :
    GGInvolCentTyped (G₀.map φ) (φ r) ↔ GGInvolCentTyped G₀ r := by
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
  have hq : IsChevTwoLayered (↥A ⧸ CFSG.Open.pCore 2 ↥A) ↔
      IsChevTwoLayered (↥(A.map φ) ⧸ CFSG.Open.pCore 2 ↥(A.map φ)) :=
    IsChevTwoLayered.mulEquiv_iff (QuotientGroup.congr (CFSG.Open.pCore 2 ↥A)
      (CFSG.Open.pCore 2 ↥(A.map φ)) e hpc)
  have hq' : IsChevTwoLayered
      (↥(Subgroup.centralizer ({φ r} : Set X') ⊓ G₀.map φ) ⧸
        CFSG.Open.pCore 2 ↥(Subgroup.centralizer ({φ r} : Set X') ⊓ G₀.map φ)) ↔
      IsChevTwoLayered (↥A ⧸ CFSG.Open.pCore 2 ↥A) := by
    rw [hB]
    exact hq.symm
  simpa [GGInvolCentTyped, GGInvolCentBar, A] using hq'

theorem ggInvolCentTyped_top_iff (G₀ : Subgroup X) {r : X} (hr : r ∈ G₀) :
    GGInvolCentTyped (⊤ : Subgroup ↥G₀) ⟨r, hr⟩ ↔ GGInvolCentTyped G₀ r := by
  have h := ggInvolCentTyped_map_iff_of_injective (X := ↥G₀) (X' := X)
    (φ := G₀.subtype) G₀.subtype_injective (⊤ : Subgroup ↥G₀) ⟨r, hr⟩
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  simpa using h.symm

theorem ggInvolCentTyped_conj_iff {G₀ : Subgroup X} {r g : X}
    (hg : g ∈ Subgroup.normalizer (G₀ : Set X)) :
    GGInvolCentTyped G₀ (g * r * g⁻¹) ↔ GGInvolCentTyped G₀ r := by
  have h := ggInvolCentTyped_map_iff_of_injective (G₀ := G₀) (r := r)
    (φ := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom G₀ = G₀ := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.1 hg)
  rw [hmap] at h
  simpa [MulAut.conj_apply] using h

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

private theorem isChevTwoLayered_quotient_pCore_of_isPGroup {G : Type} [Group G] [Finite G]
    {N Q : Subgroup G} (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q)
    (hQnorm : N ≤ Subgroup.normalizer (Q : Set G)) [hQn : (Q.subgroupOf N).Normal]
    (hNQ : IsChevTwoLayered (↥N ⧸ Q.subgroupOf N)) :
    IsChevTwoLayered (↥N ⧸ CFSG.Open.pCore 2 ↥N) := by
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
  have hquot : IsChevTwoLayered ((↥N ⧸ Q.subgroupOf N) ⧸ T) :=
    hNQ.quotient T hTsolv
  have e : ((↥N ⧸ Q.subgroupOf N) ⧸ T) ≃*
      (↥N ⧸ CFSG.Open.pCore 2 ↥N) :=
    QuotientGroup.quotientQuotientEquivQuotient (Q.subgroupOf N)
      (CFSG.Open.pCore 2 ↥N) hQle
  exact hquot.of_mulEquiv e.symm

theorem ggInvolCentTyped_of_normal {G₀ : Subgroup X} {r : X} {N Q : Subgroup X}
    (hNV : N ≤ Subgroup.centralizer ({r} : Set X) ⊓ G₀)
    (hNnormal : (N.subgroupOf (Subgroup.centralizer ({r} : Set X) ⊓ G₀)).Normal)
    (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q)
    (hQnorm : N ≤ Subgroup.normalizer (Q : Set X)) [hQn : (Q.subgroupOf N).Normal]
    (hNQ : IsChevTwoLayered (↥N ⧸ Q.subgroupOf N))
    (hVNsolv : Group.IsSolvable
      (↥(Subgroup.centralizer ({r} : Set X) ⊓ G₀) ⧸
        N.subgroupOf (Subgroup.centralizer ({r} : Set X) ⊓ G₀))) :
    GGInvolCentTyped G₀ r := by
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
  have hNQv : IsChevTwoLayered (↥Nv ⧸ Qv.subgroupOf Nv) := by
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
  have hNvQv : IsChevTwoLayered (↥Nv ⧸ CFSG.Open.pCore 2 ↥Nv) :=
    isChevTwoLayered_quotient_pCore_of_isPGroup hQvNv hQ2v hQvnorm hNQv
  have hpCoreEq : CFSG.Open.pCore 2 ↥Nv = O.subgroupOf Nv :=
    pCore_subgroupOf_eq_of_normal hNV hNnormal
  have hNvO : IsChevTwoLayered (↥Nv ⧸ O.subgroupOf Nv) :=
    hNvQv.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpCoreEq).symm
  let π : ↥V →* ↥V ⧸ O := QuotientGroup.mk' O
  let f : ↥Nv →* ↥V ⧸ O := π.comp Nv.subtype
  have hMdef : f.range = Nv.map π := by
    rw [show f = π.comp Nv.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hMn : f.range.Normal := by
    rw [hMdef]
    exact hNnormal.map π (QuotientGroup.mk'_surjective O)
  have hMlayer : IsChevTwoLayered ↥f.range := by
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
  exact IsChevTwoLayered.of_normal_of_solvable_quotient f.range hMlayer hquot

theorem ggInvolCentTyped_of_sup_eq {G₀ : Subgroup X} {r : X} {Q L : Subgroup X}
    (hQ2 : IsPGroup 2 Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set X))
    (hQL : Q ⊔ L = Subgroup.centralizer ({r} : Set X) ⊓ G₀)
    (hL : IsChevTwoLayered ↥L) : GGInvolCentTyped G₀ r := by
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
  have hVQ : IsChevTwoLayered (↥V ⧸ Q.subgroupOf V) := by
    have hsup : L.subgroupOf V ⊔ Q.subgroupOf V = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLV hQV, sup_comm, hQL]
      change V.subgroupOf V = ⊤
      rw [Subgroup.subgroupOf_self]
    have hL' : IsChevTwoLayered ↥(L.subgroupOf V) :=
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
  exact @ggInvolCentTyped_of_normal X _ _ G₀ r V Q le_rfl hVnormal hQV hQ2 hQnorm
    (inferInstance : (Q.subgroupOf V).Normal) hVQ hVVsolv

theorem ggInvolCentTyped_of_oTwoPrime_eq_sup {G₀ : Subgroup X} {r : X} {Q L : Subgroup X}
    (hQ2 : IsPGroup 2 Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set X))
    (hX : ggRCSX G₀ r = Q ⊔ L) (hL : IsChevTwoLayered ↥L) :
    GGInvolCentTyped G₀ r := by
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
  have hNQ : IsChevTwoLayered (↥N ⧸ Q.subgroupOf N) := by
    have hsup : L.subgroupOf N ⊔ Q.subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLN hQN, sup_comm, ← hX]
      change N.subgroupOf N = ⊤
      rw [Subgroup.subgroupOf_self]
    have hL' : IsChevTwoLayered ↥(L.subgroupOf N) :=
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
  exact ggInvolCentTyped_of_normal hNle hNnormal hQN hQ2 hQnorm hNQ hVNsolv

theorem ggInvolCentTyped_of_model {U C : Type} [Group U] [Group C]
    {ψ : U →* X} {π : U →* C} (hπ : Function.Surjective π) (hker : π.ker = ψ.ker)
    {w : U} (hw : GGRootCentQLTyped (π w)) :
    GGInvolCentTyped ψ.range (ψ w) := by
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
  refine ggInvolCentTyped_of_sup_eq (hQ2.map Θ') ?_ ?_
    (IsChevTwoLayered.of_mulEquiv (L.equivMapOfInjective Θ' hinj).symm hL)
  · exact ggRCST_map_le_normalizer Θ' hLQ
  · rw [inf_comm, hC, ← hQL, Subgroup.map_sup]

end Reductions

section Tags

theorem ggRootInvolCentTypedTag_of_placeholder (t : CFSG.Open.StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootInvolCentTypedTag t := by
  intro X _ _ n f ψ _ hrk _ _ r _
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggRootInvolCentTypedTag_POmegaOdd : GGRootInvolCentTypedTag .POmegaOdd := by
  intro X _ _ n f ψ hadm
  exact absurd rfl hadm.2.2.2

theorem ggRootInvolCentTypedTag_of_modelTyped {t : CFSG.Open.StatedLieTag}
    (h : GGRootInvolModelTypedTag t) : GGRootInvolCentTypedTag t := by
  intro X _ _ n f ψ hadm hrk hker hC r hroot
  obtain ⟨C, _, π, w, hπ, hker', hw, htyped⟩ := h X n f ψ hadm hrk hker hC r hroot
  have hψw : ψ w = r := hw
  rw [← hψw]
  exact ggInvolCentTyped_of_model hπ hker' htyped

theorem ggRootInvolCentTypedInput_of_tags
    (h : ∀ t, GGRootInvolCentTypedTag t) : GGRootInvolCentTypedInput := by
  intro X _ _ G₀ r hG₀ hnc hroot
  obtain ⟨t, n, f, ψ, hrange, hadm, hrk, hker, hroot'⟩ := hroot
  let ψ' : (ggU t n f).K →* ↥G₀ :=
    ψ.codRestrict G₀ (fun x => hrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hrange' : ψ'.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    have hy : (y : X) ∈ ψ.range := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hker' : ψ'.ker ≤ Subgroup.center (ggU t n f).K := by
    rw [MonoidHom.ker_codRestrict]
    exact hker
  have hcenter : Subgroup.centralizer (ψ'.range : Set ↥G₀) = ⊥ := by
    rw [hrange']
    change Subgroup.centralizer (Set.univ : Set ↥G₀) = ⊥
    rw [Subgroup.centralizer_univ,
      CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm
        hG₀ hnc]
  have hrG₀ : r ∈ G₀ := by
    obtain ⟨-, γ, hγ, u, hu⟩ := hroot'
    have hsub : ggRootSub (ggU t n f).D ψ γ u ≤ ψ.range := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, rfl⟩
    rw [← hrange]
    exact hsub hu
  have hroot'' : GGRootInvolution (ggU t n f).D t ψ' ⟨r, hrG₀⟩ := by
    obtain ⟨hr2, γ, hγ, u, hu⟩ := hroot'
    refine ⟨?_, γ, hγ, u, ?_⟩
    · simpa using hr2
    · have hmap : (ggRootSub (ggU t n f).D ψ' γ u).map G₀.subtype =
          ggRootSub (ggU t n f).D ψ γ u := by
        simp only [ggRootSub, Subgroup.map_map]
        congr 1
      have hmemX : G₀.subtype ⟨r, hrG₀⟩ ∈
          (ggRootSub (ggU t n f).D ψ' γ u).map G₀.subtype := by
        rw [hmap]
        exact hu
      exact (Subgroup.mem_map_iff_mem G₀.subtype_injective).mp hmemX
  have htag := h t (↥G₀) n f ψ' hadm hrk hker' hcenter ⟨r, hrG₀⟩ hroot''
  rw [hrange'] at htag
  exact (ggInvolCentTyped_top_iff G₀ hrG₀).1 htag

theorem ggRootInvolCentTypedInput_of_tagInputs (hPSL : GGRootInvolCentTypedTag .PSL)
    (hPSU : GGRootInvolCentTypedTag .PSU) (hPSp : GGRootInvolCentTypedTag .PSp)
    (hPlus : GGRootInvolCentTypedTag .POmegaPlus)
    (hMinus : GGRootInvolCentTypedTag .POmegaMinus) (hF4 : GGRootInvolCentTypedTag .F4)
    (hE6 : GGRootInvolCentTypedTag .E6) (hE7 : GGRootInvolCentTypedTag .E7)
    (hE8 : GGRootInvolCentTypedTag .E8) (hTwE6 : GGRootInvolCentTypedTag .twistedE6) :
    GGRootInvolCentTypedInput := by
  refine ggRootInvolCentTypedInput_of_tags fun t => ?_
  cases t with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggRootInvolCentTypedTag_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | G2 => exact ggRootInvolCentTypedTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggRootInvolCentTypedTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggRootInvolCentTypedTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggRootInvolCentTypedTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggRootInvolCentTypedTag_of_placeholder _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggRootInvolCentTypedTag_of_placeholder _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end Tags

private theorem exists_noncomm_of_le_of_quotient_noncomm {X : Type} [Group X]
    {G₀ S : Subgroup X} (hSG : S ≤ G₀) {N : Subgroup ↥S} [N.Normal]
    (hnc : ∃ a b : ↥S ⧸ N, a * b ≠ b * a) :
    ∃ a b : ↥G₀, a * b ≠ b * a := by
  by_contra h
  push Not at h
  obtain ⟨a, b, hab⟩ := hnc
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have haG : (a' : X) ∈ G₀ := hSG a'.2
  have hbG : (b' : X) ∈ G₀ := hSG b'.2
  have h' := h ⟨(a' : X), haG⟩ ⟨(b' : X), hbG⟩
  have hS : a' * b' = b' * a' := by
    refine Subtype.ext ?_
    exact congrArg (fun z : ↥G₀ => (z : X)) h'
  exact hab (by simpa [map_mul] using congrArg (QuotientGroup.mk' N) hS)

section General

theorem isChevSimple_two_of_rootInvolution
    (hL : CFSG.LocalAnalysis.GLTheoremA.I142T.LayerFixTyped)
    (hV : GGRootInvolCentTypedInput) {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {G₀ : Subgroup X} {r e : X} (hG₀ : IsSimpleGroup ↥G₀)
    (he : e ∈ Subgroup.normalizer (G₀ : Set X)) (hep : orderOf e = p) (hcomm : Commute r e)
    (hroot : GGIsRootInvolution G₀ r) (S : Subgroup X)
    (hSY : S ≤ Subgroup.centralizer ({r, e} : Set X) ⊓ G₀)
    (hsub : CFSG.Assembly.IsSubnormal S (Subgroup.centralizer ({r, e} : Set X) ⊓ G₀))
    (hperf : commutator ↥S = ⊤) (N : Subgroup ↥S) [N.Normal]
    (hsimp : IsSimpleGroup (↥S ⧸ N))
    (hnc : ∃ a b : ↥S ⧸ N, a * b ≠ b * a) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (↥S ⧸ N) := by
  have hncG : ∃ a b : ↥G₀, a * b ≠ b * a :=
    exists_noncomm_of_le_of_quotient_noncomm (hSY.trans inf_le_right) hnc
  have hVinst : GGInvolCentTyped G₀ r := hV X G₀ r hG₀ hncG hroot
  exact isChevSimple_of_ggInvolCentTyped hL hp hp2 he hep hcomm hVinst S hSY hsub hperf N
    hsimp hnc

end General

section Marking


theorem largeEvenMarking_of_isChevSimple {G : Type} [Group G] [Finite G]
    (hperf : commutator G = ⊤) (hsimp : IsSimpleGroup G)
    (hnc : ∃ a b : G, a * b ≠ b * a)
    (hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 G) :
    LargeEvenMarking G (fun _ _ _ _ _ _ => True) := by
  have hcenter : Subgroup.center G = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm
      hsimp hnc
  let e : (G ⧸ Subgroup.center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have hsimpZ : IsSimpleGroup (G ⧸ Subgroup.center G) := e.isSimpleGroup
  have hcoreZ : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (G ⧸ Subgroup.center G) :=
    CFSG.LieType.ChevTwo.isChevSimple_of_mulEquiv e hchev
  exact CFSG.StandardType.ChevTwo.ys08_holds_legacy G ⟨hperf, hsimpZ⟩ hcoreZ

theorem ggStructSOnePrimeRoot_of_ggRootInvolCentTyped
    (hL : CFSG.LocalAnalysis.GLTheoremA.I142T.LayerFixTyped)
    (hV : GGRootInvolCentTypedInput) : GGStructSOnePrimeRoot := by
  intro X _ _ p G₀ r e hp hp2 hG₀ he _hM hrG₀ hr2 hep hcomm hroot S hSY hsub hperf N
    instN _hO2 hsimp hnc
  have hncG : ∃ a b : ↥G₀, a * b ≠ b * a :=
    exists_noncomm_of_le_of_quotient_noncomm (hSY.trans inf_le_right) hnc
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (↥S ⧸ N) :=
    isChevSimple_two_of_rootInvolution hL hV hp hp2 hG₀ he hep hcomm hroot S hSY hsub
      hperf N hsimp hnc
  haveI : Group.IsPerfect ↥S := Group.isPerfect_def.mpr hperf
  haveI : Group.IsPerfect (↥S ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hperfN : commutator (↥S ⧸ N) = ⊤ := Group.isPerfect_def.mp inferInstance
  exact largeEvenMarking_of_isChevSimple hperfN hsimp hnc hchev

theorem ggStructSOnePrimeRoot_of_tagInputs
    (hL : CFSG.LocalAnalysis.GLTheoremA.I142T.LayerFixTyped)
    (hPSL : GGRootInvolCentTypedTag .PSL) (hPSU : GGRootInvolCentTypedTag .PSU)
    (hPSp : GGRootInvolCentTypedTag .PSp) (hPlus : GGRootInvolCentTypedTag .POmegaPlus)
    (hMinus : GGRootInvolCentTypedTag .POmegaMinus) (hF4 : GGRootInvolCentTypedTag .F4)
    (hE6 : GGRootInvolCentTypedTag .E6) (hE7 : GGRootInvolCentTypedTag .E7)
    (hE8 : GGRootInvolCentTypedTag .E8) (hTwE6 : GGRootInvolCentTypedTag .twistedE6) :
    GGStructSOnePrimeRoot :=
  ggStructSOnePrimeRoot_of_ggRootInvolCentTyped hL
    (ggRootInvolCentTypedInput_of_tagInputs hPSL hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6)

end Marking

end CFSG.StandardType
