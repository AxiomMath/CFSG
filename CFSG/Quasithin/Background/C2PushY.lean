module

public import CFSG.Quasithin.Background.C2PushLift
public import CFSG.Quasithin.Background.A3Structure312Embed
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin.C2Push

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowTwoOf_ge_of_isPGroup {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup G, IsSylowTwoOf S H ∧ P ≤ S := by
  have hPH' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hPH'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥H).map H.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩, ?_⟩
  · have : ((Q : Subgroup ↥H).map H.subtype).subgroupOf H = (Q : Subgroup ↥H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
    exact Q.not_dvd_index
  · intro x hx
    have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.mpr hx)
    exact ⟨⟨x, hPH hx⟩, hx', rfl⟩

omit [Finite G] in
theorem le_normalizer_sup_of_forall {ι : Type*} [DecidableEq ι] {A : Subgroup G} (L : ι → Subgroup G)
    (h : ∀ i, A ≤ Subgroup.normalizer (L i : Set G)) (s : Finset ι) :
    A ≤ Subgroup.normalizer ((s.sup L : Subgroup G) : Set G) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp [Subgroup.mem_bot]
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h a hx, ih hx⟩

theorem inf_sup_le_sup_inf_of_sylow {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (L : ι → Subgroup G) (hsyl : ∀ i, IsSylowTwoOf (T ⊓ L i) (L i))
    (hnorm : ∀ i j, L i ≤ Subgroup.normalizer (L j : Set G)) :
    T ⊓ Finset.univ.sup L ≤ Finset.univ.sup (fun i => T ⊓ L i) := by
  have key : ∀ s : Finset ι, T ⊓ s.sup L ≤ s.sup (fun i => T ⊓ L i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sup_insert]
      have hN : L a ≤ Subgroup.normalizer ((s.sup L : Subgroup G) : Set G) :=
        le_normalizer_sup_of_forall L (fun j => hnorm a j) s
      intro x hx
      have hx' := A312.inf_sup_le_of_sylow (hsyl a) hT2 hN hx
      have hnorm' : (T ⊓ L a) ≤ Subgroup.normalizer ((s.sup L : Subgroup G) : Set G) :=
        inf_le_right.trans hN
      have hx'' : x ∈ ((T ⊓ L a : Subgroup G) : Set G) * ((s.sup L : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm']
        exact hx'
      obtain ⟨t, ht, n, hn, rfl⟩ := hx''
      have hnT : n ∈ T ⊓ s.sup L := by
        refine ⟨?_, hn⟩
        have : n = t⁻¹ * (t * n) := by group
        rw [this]
        exact T.mul_mem (T.inv_mem ht.1) hx.1
      exact Subgroup.mul_mem_sup ht (ih hnT)
  simpa using key Finset.univ

theorem isSylowTwoOf_of_forall_inf_isSylow {ι : Type*} [Fintype ι] [DecidableEq ι] {R Y : Subgroup G}
    (hR2 : IsPGroup 2 R) (L : ι → Subgroup G) (hY : Finset.univ.sup L ⊔ R = Y)
    (hRn : R ≤ Subgroup.normalizer ((Finset.univ.sup L : Subgroup G) : Set G))
    (hsub : ∀ i, IsSubnormal (L i) Y) (hsyl : ∀ i, IsSylowTwoOf (R ⊓ L i) (L i))
    (hnorm : ∀ i j, L i ≤ Subgroup.normalizer (L j : Set G)) : IsSylowTwoOf R Y := by
  have hRY : R ≤ Y := hY ▸ le_sup_right
  obtain ⟨T, hTY, hRT⟩ := exists_isSylowTwoOf_ge_of_isPGroup hRY hR2
  have hT2 := hTY.2.1
  have hTL' : ∀ i, IsSylowTwoOf (T ⊓ L i) (L i) := fun i =>
    isSylowTwoOf_inf_of_isSubnormal (hsub i) hTY
  have hTL : ∀ i, T ⊓ L i ≤ R := by
    intro i
    have h2 := ((A4.isSylowTwoOf_iff_maximal).mp (hsyl i)).2.2 (T ⊓ L i) inf_le_right
      hT2.to_inf_left (inf_le_inf_right _ hRT)
    exact h2.trans inf_le_left
  have hTY0 : T ⊓ Finset.univ.sup L ≤ R :=
    (inf_sup_le_sup_inf_of_sylow hT2 L hTL' hnorm).trans (Finset.sup_le fun i _ => hTL i)
  have hTR : T ≤ R := by
    intro t ht
    have htY : t ∈ (↑(Finset.univ.sup L ⊔ R) : Set G) := hY ▸ hTY.1 ht
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hRn] at htY
    obtain ⟨y, hy, r, hr, hyr⟩ := htY
    have hyT : y ∈ T := by
      have : y = t * r⁻¹ := by rw [← hyr]; group
      rw [this]
      exact T.mul_mem ht (T.inv_mem (hRT hr))
    have : t = y * r := hyr.symm
    rw [this]
    exact R.mul_mem (hTY0 ⟨hyT, hy⟩) hr
  have hRTeq : T = R := le_antisymm hTR hRT
  rw [← hRTeq]
  exact hTY

theorem isSylowTwoOf_map_conj {S A : Subgroup G} (h : IsSylowTwoOf S A) (g : G) :
    IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom) (A.map (MulAut.conj g).toMonoidHom) := by
  rw [A4.isSylowTwoOf_iff_maximal] at h ⊢
  obtain ⟨hSA, hS2, hmax⟩ := h
  set e : G ≃* G := MulAut.conj g with he
  refine ⟨Subgroup.map_mono hSA, hS2.map _, fun P hPA hP2 hSP => ?_⟩
  have hP1 : P.comap e.toMonoidHom ≤ A := by
    have := Subgroup.comap_mono (f := e.toMonoidHom) hPA
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at this
  have hP3 : IsPGroup 2 (P.comap e.toMonoidHom) := hP2.comap_of_injective _ e.injective
  have hP4 : S ≤ P.comap e.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hSP
  have := Subgroup.map_mono (f := e.toMonoidHom) (hmax _ hP1 hP3 hP4)
  rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at this

omit [Finite G] in
theorem conjClosure_eq_sup (L R : Subgroup G) [Fintype ↥R] :
    conjClosure L R = Finset.univ.sup (fun r : ↥R => conjByElt (r : G) L) := by
  refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (Finset.sup_le fun r _ => ?_)
  · have : h * z * h⁻¹ ∈ conjByElt h L := Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩
    exact (Finset.le_sup (f := fun r : ↥R => conjByElt (r : G) L) (Finset.mem_univ ⟨h, hh⟩)) this
  · exact conjByElt_le_conjClosure r.2

theorem charTwo_of_pCoreOf_le {M Y : Subgroup G} (hM : CharTwo M) (hOY : pCoreOf 2 M ≤ Y)
    (hYM : Y ≤ M) : CharTwo Y := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hM hYM hOY

omit [Finite G] in
theorem imageOTwoQuot_conjByElt {M X : Subgroup G} {m : G} (hm : m ∈ M) (hXM : X ≤ M) :
    imageOTwoQuot M (conjByElt m X) =
      (imageOTwoQuot M X).map (MulAut.conj (QuotientGroup.mk ⟨m, hm⟩ : OTwoQuot M)).toMonoidHom := by
  ext u
  constructor
  · intro hu
    obtain ⟨y, hy, hyX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyX
    have hxy' : m * x * m⁻¹ = y := by simpa [MulAut.conj_apply] using hxy
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk ⟨x, hXM hx⟩,
      mem_imageOTwoQuot_iff.mpr ⟨x, hXM hx, hx, rfl⟩, ?_⟩
    subst hxy'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨x, hx, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    refine mem_imageOTwoQuot_iff.mpr ⟨m * x * m⁻¹,
      M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm),
      Subgroup.mem_map.mpr ⟨x, hxX, by simp [MulAut.conj_apply]⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl

theorem conjByElt_le_normalizer_conjByElt {M L : Subgroup G} (hL : L ∈ cComp M)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) :
    conjByElt m L ≤ Subgroup.normalizer (conjByElt m' L : Set G) := by
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hK := isComponent_imageOTwoQuot hL hLq
  have hKm : CFSG.IsComponent (imageOTwoQuot M (conjByElt m L)) := by
    rw [imageOTwoQuot_conjByElt hm hLM]
    exact CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hKm' : CFSG.IsComponent (imageOTwoQuot M (conjByElt m' L)) := by
    rw [imageOTwoQuot_conjByElt hm' hLM]
    exact CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hc : imageOTwoQuot M (conjByElt m L) ≤
      Subgroup.normalizer (imageOTwoQuot M (conjByElt m' L) : Set (OTwoQuot M)) := by
    rcases CFSG.LocalCores.distinct_components_commute hKm hKm' with h | h
    · rw [h]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
        (Subgroup.centralizer_le_normalizer _)
  have hmLM : conjByElt m L ≤ M := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using M.mul_mem (M.mul_mem hm (hLM hl)) (M.inv_mem hm)
  exact le_normalizer_of_imageOTwoQuot_le_normalizer hmLM
    (C2Nine.conjByElt_mem_cComp hL (Subgroup.le_normalizer hm')) hc

omit [Finite G] in
theorem conjClosure_sup_le {M R L : Subgroup G} (hRM : R ≤ M) (hLM : L ≤ M) :
    conjClosure L R ⊔ R ≤ M :=
  sup_le (conjClosure_le fun _ hh _ hz => M.mul_mem (M.mul_mem (hRM hh) (hLM hz))
    (M.inv_mem (hRM hh))) hRM

theorem isSylowTwoOf_inf_conjByElt {R L : Subgroup G} {r : G} (hr : r ∈ R)
    (hsyl : IsSylowTwoOf (R ⊓ L) L) : IsSylowTwoOf (R ⊓ conjByElt r L) (conjByElt r L) := by
  have h1 := isSylowTwoOf_map_conj hsyl r
  have h2 : (R ⊓ L).map (MulAut.conj r).toMonoidHom = R ⊓ conjByElt r L := by
    rw [inf_comm R L, map_conj_inf_of_mem hr, inf_comm]
    rfl
  rw [h2] at h1
  exact h1

theorem isSylowTwoOf_conjClosure_sup {M R L : Subgroup G} (hR : IsTwoRadicalIn M R)
    (hL : L ∈ cComp M) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsyl : IsSylowTwoOf (R ⊓ L) L) : IsSylowTwoOf R (conjClosure L R ⊔ R) := by
  classical
  have : Fintype ↥R := Fintype.ofFinite _
  have hRM : R ≤ M := hR.1
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hYM : conjClosure L R ⊔ R ≤ M := conjClosure_sup_le hRM hLM
  have hcc : conjClosure L R = Finset.univ.sup (fun r : ↥R => conjByElt (r : G) L) :=
    conjClosure_eq_sup L R
  refine isSylowTwoOf_of_forall_inf_isSylow (ι := ↥R) hR.isPGroup
    (fun r : ↥R => conjByElt (r : G) L) (by rw [hcc]) ?_ ?_ ?_ ?_
  · rw [← hcc]
    exact le_normalizer_conjClosure L R
  · intro r
    have hrc : conjByElt (r : G) L ∈ cComp M :=
      C2Nine.conjByElt_mem_cComp hL (Subgroup.le_normalizer (hRM r.2))
    have hle : conjByElt (r : G) L ≤ conjClosure L R ⊔ R :=
      (conjByElt_le_conjClosure r.2).trans le_sup_left
    exact A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hrc) hle hYM
  · intro r
    exact isSylowTwoOf_inf_conjByElt r.2 hsyl
  · intro r r'
    exact conjByElt_le_normalizer_conjByElt hL hLq (hRM r.2) (hRM r'.2)

end CFSG.Quasithin.C2Push
