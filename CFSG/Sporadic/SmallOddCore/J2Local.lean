module

public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J2CentralizerD
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem not_le_of_isPGroup {M : Type*} [Group M] [Finite M] {B K : Subgroup M}
    (hB : CFSG.Assembly.IsQuasisimple B) {p : ℕ} [Fact p.Prime] (hK : IsPGroup p K)
    (hBK : B ≤ K) : False := by
  rw [ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hB
  have hperf : Group.IsPerfect B := hB.1
  have hBp : IsPGroup p B := hK.to_le hBK
  have : Group.IsNilpotent B := hBp.isNilpotent
  have hnt : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := hB.2.2
    exact hab (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable B inferInstance

theorem isPGroup_two_of_card {M : Type*} [Group M] {K : Subgroup M} {k : ℕ}
    (hK : Nat.card K = 2 ^ k) : IsPGroup 2 K :=
  IsPGroup.of_card hK

theorem isComponentOf_le_or_commute {M : Type*} [Group M] [Finite M] {B H N : Subgroup M}
    (hB : CFSG.Assembly.IsComponentOf B H) (hNH : N ≤ H) (hN : H ≤ normalizer (N : Set M)) :
    B ≤ N ∨ ⁅B, N⁆ = ⊥ := by
  have hBH := hB.1
  have hc := (isComponentOf_iff_isComponent_subgroupOf hBH).1 hB
  have hNn : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).2 hN
  rcases CFSG.LocalCores.component_normal_subgroup hc hNn with h | h
  · left
    intro x hx
    have := h (mem_subgroupOf.mpr hx : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H)
    exact mem_subgroupOf.mp this
  · right
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := (commutator_eq_bot_iff_le_centralizer.mp h)
      (mem_subgroupOf.mpr hx : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H)
    rw [mem_centralizer_iff] at h1
    have := h1 ⟨y, hNH hy⟩ (mem_subgroupOf.mpr hy)
    exact congrArg Subtype.val this

theorem j2DReps_mem :
    ∀ r ∈ j2DReps, tp 315 r ∈ genOf 315 j2DGens := by
  have hn : 315 < 2 ^ 32 := by norm_num
  have h := j2_DOK
  simp only [j2DOK, Bool.and_eq_true, List.all_eq_true] at h
  have hRp := h.1.1.1.1.2
  intro r hr
  have hr' := hr
  simp only [j2DReps, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;>
    exact tp_wordTbl_mem hn j2_DGens_perm (by decide) (hRp _ hr)

theorem j2_D_facts :
    Nat.card (genOf 315 j2DGens) = 60 ∧ genOf 315 j2DGens ≤ genOf 315 j2C1Gens ∧
      genOf 315 j2C1Gens ≤ normalizer (genOf 315 j2DGens : Set (Equiv.Perm (Fin 315))) ∧
      IsSimpleGroup ↥(genOf 315 j2DGens) ∧
      Nat.card ↥(genOf 315 j2C1Gens ⊓
        centralizer (genOf 315 j2DGens : Set (Equiv.Perm (Fin 315)))) = 4 := by
  have hn : 315 < 2 ^ 32 := by norm_num
  have h := j2_DOK
  simp only [j2DOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hDenum, hC1enum⟩, hC1p⟩, hDp⟩, hRp⟩, hnorm⟩, hcov⟩, hreps⟩, hcent⟩ := h
  rw [List.all_eq_true] at hC1p hDp hRp
  obtain ⟨hDcard, hDrep, hDcov, -⟩ := enumOK_spec hn hDp hDenum
  have hC1inv : ∀ c ∈ j2C1Gens, invOK 315 c (invT 315 c) = true := by
    simp only [enumOK, Bool.and_eq_true, List.all_eq_true] at hC1enum
    exact hC1enum.1.1.1.1
  have hDC1 : genOf 315 j2DGens ≤ genOf 315 j2C1Gens := by
    rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ j2DGens := by simpa using hg
    simp only [j2DGens, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl
    · exact tp_wordTbl_mem hn j2_C1Gens_perm (by decide) (hDp _ (by simp [j2DGens]))
    · exact tp_wordTbl_mem hn j2_C1Gens_perm (by decide) (hDp _ (by simp [j2DGens]))
  have hnorm' := normOK_spec hn hDp hDenum (fun c hc => ⟨hC1p c hc, hC1inv c hc⟩) hnorm
  set D := genOf 315 j2DGens
  have hDgK : ∀ l < j2DGens.toArray.size, Rep 315 j2DGens.toArray[l]! (tp 315 j2DGens.toArray[l]!) ∧
      Rep 315 (j2DGens.toArray.map (invT 315))[l]! (tp 315 j2DGens.toArray[l]!)⁻¹ ∧
      tp 315 j2DGens.toArray[l]! ∈ D := by
    intro l hl
    have hmem : j2DGens.toArray[l]! ∈ j2DGens := by simpa using getElem!_mem_array hl
    have hrep := rep_tp (hDp _ hmem)
    refine ⟨hrep, ?_, tp_mem_genOf hmem⟩
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos _ l hl]
    have hinv : invOK 315 j2DGens.toArray[l]! (invT 315 j2DGens.toArray[l]!) = true := by
      simp only [enumOK, Bool.and_eq_true, List.all_eq_true] at hDenum
      exact hDenum.1.1.1.1 _ hmem
    exact rep_invT hrep hinv
  have hsimple : IsSimpleGroup ↥D := by
    refine isSimpleGroup_of_cover (D := D) ?_ (j2DReps.map (tp 315)) ?_ ?_
    · intro h
      rw [h, Subgroup.card_bot] at hDcard
      exact absurd hDcard (by norm_num)
    · intro x hx
      obtain ⟨k, hk, hkrep⟩ := hDcov x hx
      rw [Array.all_eq_true] at hcov
      have h1 := hcov k hk
      rw [← getElem!_pos _ k hk, Bool.or_eq_true, List.any_eq_true] at h1
      rcases h1 with h1 | ⟨r, hr, hm⟩
      · exact Or.inl ((tblEq_idT_iff hn hkrep).1 h1)
      · right
        have hrrep := rep_tp (hRp r hr)
        have hspec := conjTreeOK_spec D hDgK hrrep (by
          rw [List.all_eq_true] at hreps
          have := hreps r hr
          rw [Bool.and_eq_true] at this
          exact this.1)
        have hqrep : ∀ j < (conjClosureH 315 j2DGens.toArray
            (j2DGens.toArray.map (invT 315)) r 100).1.size,
            Rep 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).1[j]!
              (tablePerm 315 (conjClosureH 315 j2DGens.toArray
                (j2DGens.toArray.map (invT 315)) r 100).1[j]!) := by
          intro j hj
          obtain ⟨c, -, hc⟩ := hspec j hj
          rw [tablePerm_eq hc]
          exact hc
        obtain ⟨j, hj, hxj⟩ := memT_spec hqrep hkrep hm
        obtain ⟨c, hc, hcrep⟩ := hspec j hj
        rw [tablePerm_eq hcrep] at hxj
        exact ⟨tp 315 r, List.mem_map.mpr ⟨r, hr, rfl⟩, c, hc, hxj⟩
    · intro r' hr'
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      rw [List.all_eq_true] at hreps
      have hrr := hreps r hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hrr
      obtain ⟨htree, ⟨hNtree, hNdist⟩, hNsize⟩ := hrr
      have hrrep := rep_tp (hRp r hr)
      have hspec := conjTreeOK_spec D hDgK hrrep htree
      set O := (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).1
      set K := closure ((fun j => tablePerm 315 O[j]!) '' {j | j < O.size})
      have hOrep : ∀ j < O.size, Rep 315 O[j]! (tablePerm 315 O[j]!) ∧
          tablePerm 315 O[j]! ∈ K := by
        intro j hj
        obtain ⟨c, -, hc⟩ := hspec j hj
        rw [tablePerm_eq hc]
        exact ⟨hc, by rw [← tablePerm_eq hc]; exact subset_closure ⟨j, hj, rfl⟩⟩
      have hN := mulTreeOK_spec hn K (gg := fun j => tablePerm 315 O[j]!) hOrep hNtree
      have hNrep : ∀ k < (mulClosureH 315 O 100).1.size,
          Rep 315 (mulClosureH 315 O 100).1[k]! (tablePerm 315 (mulClosureH 315 O 100).1[k]!) := by
        intro k hk
        obtain ⟨c, -, hc⟩ := hN k hk
        rw [tablePerm_eq hc]
        exact hc
      have hNnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hNrep) hNdist
      have hKcard : 60 ≤ Nat.card K := by
        have := length_le_card_of_nodup hNnodup (K := K) fun x hx => by
          obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hNrep hx
          obtain ⟨c, hc, hcrep⟩ := hN k hk
          rw [tablePerm_eq hcrep]
          exact hc
        rwa [List.length_map, Array.length_toList, hNsize] at this
      have hKD : K ≤ D := by
        rw [closure_le]
        rintro _ ⟨j, hj, rfl⟩
        obtain ⟨c, hc, hcrep⟩ := hspec j hj
        show tablePerm 315 O[j]! ∈ D
        rw [tablePerm_eq hcrep]
        exact D.mul_mem (D.mul_mem hc (j2DReps_mem r hr)) (D.inv_mem hc)
      have hKeq : K = D := Subgroup.eq_of_le_of_card_ge hKD (by rw [hDcard]; exact hKcard)
      calc D = K := hKeq.symm
        _ ≤ closure (conjClass D (tp 315 r)) := by
          rw [closure_le]
          rintro _ ⟨j, hj, rfl⟩
          obtain ⟨c, hc, hcrep⟩ := hspec j hj
          show tablePerm 315 O[j]! ∈ _
          rw [tablePerm_eq hcrep]
          exact subset_closure ⟨c, hc, rfl⟩
  refine ⟨hDcard, hDC1, hnorm', hsimple, ?_⟩
  rw [centCount_spec hn hC1p hC1enum hDp]
  exact hcent

theorem j2_Q_facts :
    Nat.card (genOf 315 j2QGens) = 32 ∧ genOf 315 j2QGens ≤ genOf 315 j2C2Gens ∧
      genOf 315 j2C2Gens ≤ normalizer (genOf 315 j2QGens : Set (Equiv.Perm (Fin 315))) ∧
      Nat.card ↥(genOf 315 j2C2Gens ⊓
        centralizer (genOf 315 j2QGens : Set (Equiv.Perm (Fin 315)))) = 2 := by
  have hn : 315 < 2 ^ 32 := by norm_num
  have h := j2_QOK
  simp only [j2QOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hQenum, hC2enum⟩, hC2p⟩, hQp⟩, hnorm⟩, hcent⟩ := h
  rw [List.all_eq_true] at hC2p hQp
  obtain ⟨hQcard, -, -, -⟩ := enumOK_spec hn hQp hQenum
  have hC2inv : ∀ c ∈ j2C2Gens, invOK 315 c (invT 315 c) = true := by
    simp only [enumOK, Bool.and_eq_true, List.all_eq_true] at hC2enum
    exact hC2enum.1.1.1.1
  have hQC2 : genOf 315 j2QGens ≤ genOf 315 j2C2Gens := by
    rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ j2QGens := by simpa using hg
    simp only [j2QGens, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl | rfl <;>
      exact tp_wordTbl_mem hn hC2p (by decide) (hQp _ (by simp [j2QGens]))
  refine ⟨hQcard, hQC2, normOK_spec hn hQp hQenum (fun c hc => ⟨hC2p c hc, hC2inv c hc⟩) hnorm, ?_⟩
  rw [centCount_spec hn hC2p hC2enum hQp]
  exact hcent

theorem map_centralizer_eq_inf {T M : Type*} [Group T] [Group M] {f : T →* M}
    (hf : Function.Injective f) (S : Set T) :
    (centralizer S).map f = f.range ⊓ centralizer (f '' S) := by
  ext y
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hx s hs]
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, fun s hs => hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hx _ ⟨s, hs, rfl⟩

theorem map_conj_inf_centralizer {M : Type*} [Group M] (H : Subgroup M) {g : M} (hg : g ∈ H)
    (S : Set M) :
    (H ⊓ centralizer S).map (MulAut.conj g).toMonoidHom =
      H ⊓ centralizer ((MulAut.conj g).toMonoidHom '' S) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    map_centralizer_eq_inf (MulAut.conj g).injective]
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    · intro x hx
      refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [hH, MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective, top_inf_eq]

theorem j2P_le_j2R : j2P ≤ j2R := le_sup_left

theorem j2P_local_components
    {τ : Equiv.Perm (Fin 315)} (hτP : τ ∈ j2P) (hτ : orderOf τ = 2)
    {B : Subgroup (Equiv.Perm (Fin 315))}
    (hB : CFSG.Assembly.IsComponentOf B (j2P ⊓ centralizer ({τ} : Set _))) :
    Nat.card ↥(j2P ⊓ centralizer (B : Set (Equiv.Perm (Fin 315)))) = 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ (j2P_le_j2R hτP) hτ
  set f := (MulAut.conj g⁻¹).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hBr : CFSG.Assembly.IsComponentOf (B.map f)
      (j2P ⊓ centralizer ({tp 315 r.rep} : Set _)) := by
    have h := (isComponentOf_map_iff hfinj).2 hB
    rwa [map_conj_inf_centralizer j2P (j2P.inv_mem hg), Set.image_singleton,
      show f (g * tp 315 r.rep * g⁻¹) = tp 315 r.rep by simp only [f]; simp; group] at h
  have hcardB : Nat.card ↥(j2P ⊓ centralizer (B : Set (Equiv.Perm (Fin 315)))) =
      Nat.card ↥(j2P ⊓ centralizer ((B.map f : Subgroup _) : Set (Equiv.Perm (Fin 315)))) := by
    rw [Subgroup.coe_map, ← map_conj_inf_centralizer j2P (j2P.inv_mem hg),
      Subgroup.card_map_of_injective hfinj]
  rw [hcardB]
  set B' := B.map f
  have htrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hτP) hg
    rwa [show g⁻¹ * (g * tp 315 r.rep * g⁻¹) * g = tp 315 r.rep by group] at this
  have hBq := hBr.2.2
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  ·
    have := (hrows _ List.mem_cons_self).2.2.1
    exact absurd htrP (this.1 rfl)
  ·
    obtain ⟨hDcard, hDC1, hC1D, hDsimple, hC1cent⟩ := j2_D_facts
    have hC1 : genOf 315 j2C1Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set _) := by
      have h := (hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)).2.2.2.1
      dsimp only [j2C] at h
      rw [genOf, j2C1Gens]
      exact h
    dsimp only at hBr
    rw [← hC1] at hBr
    rcases isComponentOf_le_or_commute hBr hDC1 hC1D with hle | hcomm
    ·
      have hBD : B' = genOf 315 j2DGens := by
        set D := genOf 315 j2DGens
        have hBDc := isComponentOf_of_le hBr hle hDC1
        have hc := (isComponentOf_iff_isComponent_subgroupOf hle).1 hBDc
        have hn : 315 < 2 ^ 32 := by norm_num
        have hm1 : wordTbl 315 j2C1Gens [3, 2] ∈ j2DGens := by simp [j2DGens]
        have hm2 : wordTbl 315 j2C1Gens [2, 4, 2, 4] ∈ j2DGens := by simp [j2DGens]
        have hnab : ∃ a b : ↥D, a * b ≠ b * a := by
          refine ⟨⟨_, tp_mem_genOf hm1⟩, ⟨_, tp_mem_genOf hm2⟩, fun h => ?_⟩
          have h' := congrArg Subtype.val h
          have := (commTT_iff (rep_tp (j2_DGens_perm _ hm1)) (rep_tp (j2_DGens_perm _ hm2))).2 h'
          rw [j2_D_noncomm] at this
          exact Bool.noConfusion this
        have : IsSimpleGroup ↥D := hDsimple
        obtain ⟨hDq, hDZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
        rcases quasisimple_subnormal_subgroups hDq hc.2 with htop | hcen
        · apply le_antisymm hle
          intro x hx
          have : (⟨x, hx⟩ : ↥D) ∈ B'.subgroupOf D := by rw [htop]; trivial
          exact mem_subgroupOf.mp this
        · exfalso
          rw [hDZ] at hcen
          have hbot : B'.subgroupOf D = ⊥ := le_bot_iff.mp hcen
          have hB'bot : B' = ⊥ := by
            rw [eq_bot_iff]
            intro x hx
            have : (⟨x, hle hx⟩ : ↥D) ∈ B'.subgroupOf D := mem_subgroupOf.mpr hx
            rw [hbot, mem_bot] at this
            exact congrArg Subtype.val this
          have hq := hBq
          rw [ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq
          obtain ⟨a, b, hab⟩ := hq.2.2
          apply hab
          have : Subsingleton ↥B' := by
            rw [hB'bot]
            infer_instance
          have : Subsingleton (↥B' ⧸ center ↥B') := inferInstance
          exact Subsingleton.elim _ _
      rw [hBD]
      exact j2_card_centralizer_D
    · exfalso
      have hle : B' ≤ genOf 315 j2C1Gens ⊓
          centralizer (genOf 315 j2DGens : Set (Equiv.Perm (Fin 315))) := by
        intro x hx
        refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
        rw [mem_centralizer_iff]
        intro y hy
        have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
        rw [mem_centralizer_iff] at this
        exact this y hy
      exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 2) (by rw [hC1cent]; norm_num)) hle
  ·
    exfalso
    obtain ⟨hQcard, hQC2, hC2Q, hC2cent⟩ := j2_Q_facts
    have hC2 : genOf 315 j2C2Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
      have h := (hrows _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))).2.2.2.1
      dsimp only [j2C] at h
      rw [genOf, j2C2Gens]
      exact h
    dsimp only at hBr
    rw [← hC2] at hBr
    rcases isComponentOf_le_or_commute hBr hQC2 hC2Q with hle | hcomm
    · exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 5) (by rw [hQcard]; norm_num)) hle
    · have hle : B' ≤ genOf 315 j2C2Gens ⊓
          centralizer (genOf 315 j2QGens : Set (Equiv.Perm (Fin 315))) := by
        intro x hx
        refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
        rw [mem_centralizer_iff]
        intro y hy
        have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
        rw [mem_centralizer_iff] at this
        exact this y hy
      exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 1) (by rw [hC2cent]; norm_num)) hle

theorem cti_j2_involution_local_components_ambient_centralizer_order_twelve
    {T : Type*}
    [Group T] [Finite T] (hT : Nonempty (T ≃* NativeSporadic.J2)) {t : T} (ht : orderOf t = 2)
    {B : Subgroup T} (hB : CFSG.Assembly.IsComponentOf B (centralizer ({t} : Set T))) :
    Nat.card ↥(centralizer (B : Set T)) = 12 := by
  obtain ⟨e⟩ := hT
  set ι : T →* Equiv.Perm (Fin 315) := j2P.subtype.comp (e.trans j2PermEquiv).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (e.trans j2PermEquiv).injective
  have hrange : ι.range = j2P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (e.trans j2PermEquiv).surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hτP : ι t ∈ j2P := hrange ▸ ⟨t, rfl⟩
  have hτ : orderOf (ι t) = 2 := by rw [orderOf_injective ι hι, ht]
  have hB' : CFSG.Assembly.IsComponentOf (B.map ι)
      (j2P ⊓ centralizer ({ι t} : Set (Equiv.Perm (Fin 315)))) := by
    have := (isComponentOf_map_iff hι).2 hB
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  have h12 := j2P_local_components hτP hτ hB'
  rw [← Subgroup.card_map_of_injective hι, map_centralizer_eq_inf hι, hrange]
  rwa [Subgroup.coe_map] at h12

end CFSG.Sporadic.SmallOddCore
