module

public import CFSG.Quasithin.EmptyFaithful.S151S8C2C
public import CFSG.Quasithin.EmptyFaithful.SBd8Map

public section

namespace CFSG.Quasithin.S151S8C2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

section Inj

variable {X G : Type} [Group X] [Group G] [Finite X] [Finite G] (ι : X →* G)

omit [Finite X] [Finite G] in
theorem isPGroup_ker_of_injective (hι : Function.Injective ι) : IsPGroup 2 ↥ι.ker := by
  intro x
  refine ⟨0, ?_⟩
  have h : (x : X) = 1 := hι (by rw [MonoidHom.mem_ker.mp x.2, map_one])
  exact Subtype.ext (by simp [h])

theorem numC126_map_of_injective (hι : Function.Injective ι) {A : Subgroup X} (h : NumC126 A) :
    NumC126 (A.map ι) := by
  have hK := isPGroup_ker_of_injective ι hι
  have hQ : twoResidual (A.map ι) = (twoResidual A).map ι := (map_twoResidual ι A).symm
  have hP : pCoreOf 2 (twoResidual (A.map ι)) = (pCoreOf 2 (twoResidual A)).map ι := by
    rw [hQ, map_pCoreOf_eq ι hK (twoResidual A)]
  refine ⟨fun x hx => ?_, fun x hx hx3 => ?_⟩
  · rw [hQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, hk⟩ := h.1 y hy
    exact ⟨k, by rw [hP, ← map_pow]; exact Subgroup.mem_map_of_mem ι hk⟩
  · rw [hQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy3 : orderOf y = 3 := by rwa [orderOf_injective ι hι] at hx3
    have h4 := h.2 y hy hy3
    rw [hP, ← MonoidHom.map_zpowers, ← Subgroup.map_commutator,
      Subgroup.card_map_of_injective hι]
    exact h4

omit [Finite X] [Finite G] in
theorem isMinParabolicOf_map_of_injective (hι : Function.Injective ι) {A : Subgroup X}
    (h : IsMinParabolicOf A A) : IsMinParabolicOf (A.map ι) (A.map ι) := by
  rw [isMinParabolicOf_self_iff] at h ⊢
  let e : ↥A ≃* ↥(A.map ι) := A.equivMapOfInjective ι hι
  have := (SBd8.isMinParabolicOf_map_equiv_iff e (H := ⊤) (P := ⊤)).mpr h
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at this

omit [Finite X] [Finite G] in
theorem isPerfect_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Group.IsPerfect A) : Group.IsPerfect B := by
  refine ⟨?_⟩
  have key : (commutator A).map (e : A →* B) = commutator B := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← key, h.commutator_eq_top, Subgroup.map_top_of_surjective _ e.surjective]

end Inj

theorem input15122ThreeDLocN_of_simple (hS : Input15122ThreeDLocS) : Input15122ThreeDLocN := by
  intro G _ _ L S hsix hq hZ hS2 hSN hSyl hnc
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hSN' : S ≤ N := hSN
  let ι : ↥N →* G := N.subtype
  have hι : Function.Injective ι := N.subtype_injective
  have hKι : IsPGroup 2 ↥ι.ker := isPGroup_ker_of_injective ι hι
  set L₁ : Subgroup ↥N := L.subgroupOf N with hL₁
  set S₁ : Subgroup ↥N := S.subgroupOf N with hS₁
  have hL₁n : L₁.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr le_rfl
  have eL : ↥L₁ ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLN
  have hcore : (CFSG.pCore 2 ↥L₁).map eL.toMonoidHom = CFSG.pCore 2 ↥L := by
    have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL
    exact h
  let eq : (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.congr _ _ eL hcore
  have hsix₁ : SporadicSix (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := zb_sporadicSix_congr eq.symm hsix
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hpc : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := zb_pCore_le_center hq
  have hperf₁ : Group.IsPerfect ↥L₁ := isPerfect_of_equiv eL.symm hperf
  have hpc₁ : CFSG.pCore 2 ↥L₁ ≤ Subgroup.center ↥L₁ := by
    intro x hx
    have h1 : eL x ∈ CFSG.pCore 2 ↥L := by
      rw [← hcore]
      exact Subgroup.mem_map_of_mem _ hx
    have h2 := hpc h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro g
    apply eL.injective
    rw [map_mul, map_mul]
    exact h2 (eL g)
  have hS₁2 : IsPGroup 2 ↥S₁ := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSN').symm
  have hinfL : S₁ ⊓ L₁ = (S ⊓ L).subgroupOf N := Subgroup.ext fun x => Iff.rfl
  have e1 : (S₁ ⊓ L₁).map ι = S ⊓ L := by
    rw [hinfL]
    exact Subgroup.map_subgroupOf_eq_of_le (inf_le_right.trans hLN)
  have e2 : L₁.map ι = L := Subgroup.map_subgroupOf_eq_of_le hLN
  have e3 : S₁.map ι = S := Subgroup.map_subgroupOf_eq_of_le hSN'
  have hSyl₁ : IsSylowTwoOf (S₁ ⊓ L₁) L₁ :=
    (SBd3T.isSylowTwoOf_map_iff ι hι (S₁ ⊓ L₁) L₁).mp (by rw [e1, e2]; exact hSyl)
  have hnc₁ : ¬ L₁ ≤ Subgroup.centralizer (centerOf (S₁ ⊓ L₁) : Set ↥N) := by
    intro hLC
    apply hnc
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzN : z ∈ N := hLN ((inf_le_right : S ⊓ L ≤ L) hz.1)
    have hlN : l ∈ N := hLN hl
    have hz₁ : (⟨z, hzN⟩ : ↥N) ∈ centerOf (S₁ ⊓ L₁) := by
      refine ⟨⟨hz.1.1, hz.1.2⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (h : G) ⟨hh.1, hh.2⟩)
    have := Subgroup.mem_centralizer_iff.mp (hLC (show (⟨l, hlN⟩ : ↥N) ∈ L₁ from hl)) _ hz₁
    exact congrArg Subtype.val this
  obtain ⟨P₁, hPL, hSP, hSNP, hPz, hchar, hmin, hnum, hoP⟩ :=
    locN_of_simple_normal hS hL₁n hsix₁ hperf₁ hpc₁ hS₁2 hSyl₁ hnc₁
  refine ⟨P₁.map ι, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hPL hp
  · intro g hg
    have hgN : g ∈ N := hSN' hg.1
    have : (⟨g, hgN⟩ : ↥N) ∈ S₁ ⊓ L₁ := ⟨hg.1, hg.2⟩
    exact ⟨⟨g, hgN⟩, hSP this, rfl⟩
  · intro s hs
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    obtain ⟨p₁, hp₁, rfl⟩ := hp
    have h1 : (⟨s, hSN' hs⟩ : ↥N) ∈ Subgroup.normalizer (P₁ : Set ↥N) := hSNP (show (⟨s, hSN' hs⟩ : ↥N) ∈ S₁ from hs)
    exact ⟨_, (Subgroup.mem_normalizer_iff.mp h1 p₁).mp hp₁, rfl⟩
  · intro hPC
    obtain ⟨p₁, hp₁, hp₁z⟩ : ∃ p₁ ∈ P₁, p₁ ∉ Subgroup.centralizer (centerOf (S₁ ⊓ L₁) : Set ↥N) := by
      by_contra hcon
      exact hPz fun x hx => by
        by_contra hx'
        exact hcon ⟨x, hx, hx'⟩
    apply hp₁z
    refine Subgroup.mem_centralizer_iff.mpr fun z₁ hz₁ => ?_
    have hzSL : (z₁ : G) ∈ centerOf (S ⊓ L) := by
      refine ⟨⟨hz₁.1.1, hz₁.1.2⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have hhN : h ∈ N := hSN' hh.1
      have := Subgroup.mem_centralizer_iff.mp hz₁.2 ⟨h, hhN⟩ (show (⟨h, hhN⟩ : ↥N) ∈ S₁ ⊓ L₁ from ⟨hh.1, hh.2⟩)
      exact congrArg Subtype.val this
    have := Subgroup.mem_centralizer_iff.mp (hPC ⟨p₁, hp₁, rfl⟩) _ hzSL
    exact Subtype.ext this
  · exact charTwo_map_subtype (charTwo_iff_internal.mp hchar)
  · rw [← e3, ← Subgroup.map_sup]
    exact isMinParabolicOf_map_of_injective ι hι hmin
  · rw [← e3, ← Subgroup.map_sup]
    exact numC126_map_of_injective ι hι hnum
  · have hO := map_oPrimeResidualOf ι hKι P₁
    rw [← e1, ← hO, ← Subgroup.map_sup, hoP]

end CFSG.Quasithin.S151S8C2

namespace CFSG.Quasithin

theorem input15122ThreeDLoc_of_simple (hS : Input15122ThreeDLocS) : Input15122ThreeDLoc :=
  input15122ThreeDLoc_of_num (S151S8C2.input15122ThreeDLocN_of_simple hS)

end CFSG.Quasithin
