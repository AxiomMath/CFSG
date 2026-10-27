module

public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem
public import CFSG.Adapters.LieModelSimple
public import CFSG.RankThree.GF2n.Tim79aSec23NoSq

public section

namespace CFSG.OddTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped Pointwise

theorem noSqE1_of_centralizer_twoCore_le {G : Type} [Group G] {D : Set G}
    (hP : Pair G D)
    (hC : ∀ d ∈ D,
      (CFSG.pCore 2 (Subgroup.centralizer ({d} : Set G))).map
        (Subgroup.centralizer ({d} : Set G)).subtype ≤ Subgroup.zpowers d) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  intro d hd
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  let K : Subgroup G := CFSG.RankThree.GF2n.Tim79a.cenGen D d
  have hKC : K ≤ C := by
    change CFSG.RankThree.GF2n.Tim79a.cenGen D d ≤ C
    rw [CFSG.RankThree.GF2n.Tim79a.cenGen, Subgroup.closure_le]
    intro x hx
    exact hx.2
  have hconj : ∀ x ∈ D ∩ (C : Set G), ∀ c ∈ C, c * x * c⁻¹ ∈ D ∩ (C : Set G) := by
    intro x hx c hc
    obtain ⟨hxD, hxC⟩ := hx
    refine ⟨CFSG.Fischer.Pair.conj_mem hP hxD c, ?_⟩
    change c * x * c⁻¹ ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxC' : x ∈ Subgroup.centralizer ({d} : Set G) := hxC
    have hc' : c ∈ Subgroup.centralizer ({d} : Set G) := hc
    have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hxC'
    have hcd : c * d = d * c := Subgroup.mem_centralizer_singleton_iff.mp hc'
    have hc'd : c⁻¹ * d = d * c⁻¹ := by
      calc c⁻¹ * d = c⁻¹ * d * (c * c⁻¹) := by group
        _ = c⁻¹ * (d * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * d) * c⁻¹ := by rw [← hcd]
        _ = d * c⁻¹ := by group
    calc c * x * c⁻¹ * d = c * x * (c⁻¹ * d) := by group
      _ = c * x * (d * c⁻¹) := by rw [hc'd]
      _ = c * (x * d) * c⁻¹ := by group
      _ = c * (d * x) * c⁻¹ := by rw [hxd]
      _ = (c * d) * x * c⁻¹ := by group
      _ = (d * c) * x * c⁻¹ := by rw [hcd]
      _ = d * (c * x * c⁻¹) := by group
  have hconj_mem : ∀ x ∈ K, ∀ c ∈ C, c * x * c⁻¹ ∈ K := by
    intro x hx c hc
    change x ∈ CFSG.RankThree.GF2n.Tim79a.cenGen D d at hx
    change c * x * c⁻¹ ∈ CFSG.RankThree.GF2n.Tim79a.cenGen D d
    rw [CFSG.RankThree.GF2n.Tim79a.cenGen] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (hconj y hy c hc)
    | one => simpa using (Subgroup.one_mem (Subgroup.closure (D ∩ (C : Set G))))
    | mul a b ha hb iha ihb =>
        rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group]
        exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
        rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ iha
  have hKnormal : (K.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKC]
    intro h k hh hk
    exact hconj_mem h hh k hk
  let KC : Subgroup C := K.subgroupOf C
  haveI hKCnormal : KC.Normal := hKnormal
  let e : KC ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  have hpc : (CFSG.pCore 2 KC).map e.toMonoidHom = CFSG.pCore 2 K :=
    CFSG.pCore_map_iso 2 e
  let PC : Subgroup C := (CFSG.pCore 2 KC).map KC.subtype
  have hPCnormal : PC.Normal := ConjAct.normal_of_characteristic_of_normal
  have hPCp : IsPGroup 2 PC := CFSG.pCore_isPGroup.map KC.subtype
  have hPCle : PC ≤ CFSG.pCore 2 C :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hPCnormal hPCp
  have hcomp : C.subtype.comp KC.subtype = K.subtype.comp e.toMonoidHom := by
    ext z
    rfl
  have hmap : CFSG.inSubgroup (CFSG.pCore 2) K = PC.map C.subtype := by
    change (CFSG.pCore 2 K).map K.subtype = ((CFSG.pCore 2 KC).map KC.subtype).map C.subtype
    rw [← hpc, Subgroup.map_map, Subgroup.map_map, hcomp]
  change CFSG.inSubgroup (CFSG.pCore 2) K ≤ Subgroup.zpowers d ⊔ Subgroup.center G
  rw [hmap]
  exact (Subgroup.map_mono (f := C.subtype) hPCle).trans ((hC d hd).trans le_sup_left)

theorem noSqE1_of_fi22
    {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    (h : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi22)) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  haveI : Finite G := hP.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine noSqE1_of_centralizer_twoCore_le hP ?_
  intro d hd
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  have hrec := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition
    (G := G) D hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hZ hS d hd
  dsimp only at hrec
  obtain ⟨-, -, -, h22, -, -⟩ := hrec
  obtain ⟨hcomm, hcenter, -, hlie⟩ := h22 h
  have hcommC : commutator C = ⊤ := hcomm
  have hcenterC : (Subgroup.center C).map C.subtype = Subgroup.zpowers d := hcenter
  have hlieC : CFSG.Blueprint.LieModel (C ⧸ Subgroup.center C) .PSU 6 2 1 := hlie
  haveI : Group.IsPerfect C := Group.isPerfect_def.mpr hcommC
  haveI : Group.IsPerfect (C ⧸ Subgroup.center C) := inferInstance
  haveI : IsSimpleGroup (C ⧸ Subgroup.center C) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
      (by simp [CFSG.Blueprint.classicalTags]) hlieC
  have hlecenter : CFSG.pCore 2 C ≤ Subgroup.center C := by
    let π : C →* C ⧸ Subgroup.center C := QuotientGroup.mk' (Subgroup.center C)
    have hN : ((CFSG.pCore 2 C).map π).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal π (QuotientGroup.mk'_surjective _)
    have hP2 : IsPGroup 2 ((CFSG.pCore 2 C).map π) := CFSG.pCore_isPGroup.map π
    haveI : ((CFSG.pCore 2 C).map π).Normal := hN
    have hbot : (CFSG.pCore 2 C).map π = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 C).map π) with h | h
      · exact h
      · exfalso
        have htop : IsPGroup 2 (⊤ : Subgroup (C ⧸ Subgroup.center C)) := h ▸ hP2
        have hQ2 : IsPGroup 2 (C ⧸ Subgroup.center C) := htop.of_equiv Subgroup.topEquiv
        haveI : Group.IsNilpotent (C ⧸ Subgroup.center C) := hQ2.isNilpotent
        haveI : Group.IsSolvable (C ⧸ Subgroup.center C) := inferInstance
        exact (Group.IsPerfect.not_isSolvable (C ⧸ Subgroup.center C)) inferInstance
    have hker := (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 C) (f := π)).mp hbot
    simpa [π, QuotientGroup.ker_mk'] using hker
  have hle : (CFSG.pCore 2 C).map C.subtype ≤ Subgroup.zpowers d := by
    calc (CFSG.pCore 2 C).map C.subtype
        ≤ (Subgroup.center C).map C.subtype := Subgroup.map_mono hlecenter
      _ = Subgroup.zpowers d := hcenterC
  exact hle

theorem noSqE1_of_fi23
    {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    (h : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi23)) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  haveI : Finite G := hP.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine noSqE1_of_centralizer_twoCore_le hP ?_
  intro d hd
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  have hrec := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition
    (G := G) D hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hZ hS d hd
  dsimp only at hrec
  obtain ⟨-, -, -, -, h23, -⟩ := hrec
  obtain ⟨hcomm, hcenter, -, hQ⟩ := h23 h
  have hcommC : commutator C = ⊤ := hcomm
  have hcenterC : (Subgroup.center C).map C.subtype = Subgroup.zpowers d := hcenter
  haveI : Group.IsPerfect C := Group.isPerfect_def.mpr hcommC
  haveI : Group.IsPerfect (C ⧸ Subgroup.center C) := inferInstance
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Fi22 :=
    CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  obtain ⟨eQ⟩ := hQ
  haveI : IsSimpleGroup (C ⧸ Subgroup.center C) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 eQ
  have hlecenter : CFSG.pCore 2 C ≤ Subgroup.center C := by
    let π : C →* C ⧸ Subgroup.center C := QuotientGroup.mk' (Subgroup.center C)
    have hN : ((CFSG.pCore 2 C).map π).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal π (QuotientGroup.mk'_surjective _)
    have hP2 : IsPGroup 2 ((CFSG.pCore 2 C).map π) := CFSG.pCore_isPGroup.map π
    haveI : ((CFSG.pCore 2 C).map π).Normal := hN
    have hbot : (CFSG.pCore 2 C).map π = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 C).map π) with h | h
      · exact h
      · exfalso
        have htop : IsPGroup 2 (⊤ : Subgroup (C ⧸ Subgroup.center C)) := h ▸ hP2
        have hQ2 : IsPGroup 2 (C ⧸ Subgroup.center C) := htop.of_equiv Subgroup.topEquiv
        haveI : Group.IsNilpotent (C ⧸ Subgroup.center C) := hQ2.isNilpotent
        haveI : Group.IsSolvable (C ⧸ Subgroup.center C) := inferInstance
        exact (Group.IsPerfect.not_isSolvable (C ⧸ Subgroup.center C)) inferInstance
    have hker := (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 C) (f := π)).mp hbot
    simpa [π, QuotientGroup.ker_mk'] using hker
  have hle : (CFSG.pCore 2 C).map C.subtype ≤ Subgroup.zpowers d := by
    calc (CFSG.pCore 2 C).map C.subtype
        ≤ (Subgroup.center C).map C.subtype := Subgroup.map_mono hlecenter
      _ = Subgroup.zpowers d := hcenterC
  exact hle

theorem noSqE1_of_fi24
    {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    (h : Nonempty (G ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime)) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  haveI : Finite G := hP.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine noSqE1_of_centralizer_twoCore_le hP ?_
  intro d hd
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  let H : Subgroup G := Subgroup.zpowers d
  have hrec := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition
    (G := G) D hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hZ hS d hd
  dsimp only at hrec
  obtain ⟨-, -, -, -, -, h24⟩ := hrec
  obtain ⟨K, ⟨eK⟩, hCeq, hdisj, hcen⟩ := h24 h
  have hCeq' : C = H ⊔ K := hCeq
  have hdisj' : H ⊓ K = ⊥ := hdisj
  have hcen' : H ≤ Subgroup.centralizer (K : Set G) := hcen
  have hHCle : H ≤ C := by
    rw [hCeq']
    exact le_sup_left
  have hKC : K ≤ C := by
    rw [hCeq']
    exact le_sup_right
  have hHcentral : H ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer H) (Subgroup.le_centralizer_iff.mp hcen')
  let HC : Subgroup C := H.subgroupOf C
  let KC : Subgroup C := K.subgroupOf C
  have hHCle_center : HC ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro c
    have hxH : (x : G) ∈ H := hx
    have hcHK : (c : G) ∈ H ⊔ K := by
      rw [← hCeq']
      exact c.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hHcentral hxH) (c : G) hcHK)
  haveI : HC.Normal := Subgroup.normal_of_le_center hHCle_center
  have hsup : KC ⊔ HC = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := K) (A' := H) (B := C) hKC hHCle
    rw [sup_comm K H, ← hCeq', Subgroup.subgroupOf_self] at h
    exact h.symm
  have hinf : KC ⊓ HC = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxK : (x : G) ∈ K := hx.1
    have hxH : (x : G) ∈ H := hx.2
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj']
      exact ⟨hxH, hxK⟩
    simpa using hxbot
  have hdisjKC : Disjoint KC HC := by
    rw [disjoint_iff, hinf]
  have hmult : (KC : Set C) * (HC : Set C) = (Set.univ : Set C) := by
    have h := (Subgroup.mul_normal KC HC).symm
    rw [hsup] at h
    simpa using h
  have hcomp : KC.IsComplement' HC :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjKC hmult
  have eQ : C ⧸ HC ≃* CFSG.Blueprint.NativeSporadic.Fi23 :=
    (hcomp.QuotientMulEquiv).trans ((Subgroup.subgroupOfEquivOfLe hKC).trans eK)
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Fi23 :=
    CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  haveI : IsSimpleGroup (C ⧸ HC) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 eQ
  have hleHC : CFSG.pCore 2 C ≤ HC := by
    let π : C →* C ⧸ HC := QuotientGroup.mk' HC
    have hN : ((CFSG.pCore 2 C).map π).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal π (QuotientGroup.mk'_surjective _)
    have hP2 : IsPGroup 2 ((CFSG.pCore 2 C).map π) := CFSG.pCore_isPGroup.map π
    haveI : ((CFSG.pCore 2 C).map π).Normal := hN
    have hbot : (CFSG.pCore 2 C).map π = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 C).map π) with h | h
      · exact h
      · exfalso
        have htop : IsPGroup 2 (⊤ : Subgroup (C ⧸ HC)) := h ▸ hP2
        have hQ2 : IsPGroup 2 (C ⧸ HC) := htop.of_equiv Subgroup.topEquiv
        have hcardQ : Nat.card (C ⧸ HC) = 2 := hQ2.isSimpleGroup_iff_card_eq.mp inferInstance
        have hcardFi : Nat.card CFSG.Blueprint.NativeSporadic.Fi23 = 2 := by
          rw [← Nat.card_congr eQ.toEquiv]
          exact hcardQ
        rw [CFSG.Sporadic.Fi23.card_Fi23] at hcardFi
        norm_num at hcardFi
    have hker := (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 C) (f := π)).mp hbot
    simpa [π, QuotientGroup.ker_mk'] using hker
  have hle : (CFSG.pCore 2 C).map C.subtype ≤ Subgroup.zpowers d := by
    have hmap : (CFSG.pCore 2 C).map C.subtype ≤ H := by
      have h := Subgroup.map_mono (f := C.subtype) hleHC
      rwa [Subgroup.map_subgroupOf_eq_of_le hHCle] at h
    simpa [H] using hmap
  exact hle

end CFSG.OddTranspositions
