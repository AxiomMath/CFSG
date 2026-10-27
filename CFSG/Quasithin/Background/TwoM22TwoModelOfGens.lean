module

public import CFSG.Quasithin.Background.TwoM22TwoOuter
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Quasithin.Background.B19Basic
public import CFSG.Sporadic.Recognition.CoverBootstrap

public section

namespace CFSG.GroupTheory

open Subgroup

theorem closure_range_subtype_eq_top {G : Type*} [Group G] {ι : Type*} (g : ι → G) :
    Subgroup.closure (Set.range (fun i => (⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩ :
      ↥(Subgroup.closure (Set.range g))))) = ⊤ := by
  apply Subgroup.map_injective
    (f := (Subgroup.closure (Set.range g)).subtype) Subtype.val_injective
  rw [MonoidHom.map_closure]
  have himg : (Subgroup.closure (Set.range g)).subtype ''
      Set.range (fun i => (⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩ :
        ↥(Subgroup.closure (Set.range g)))) = Set.range g := by
    rw [← Set.range_comp]
    rfl
  rw [himg]
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨m, -, rfl⟩
    exact m.2

end CFSG.GroupTheory

namespace CFSG.Quasithin.TwoM22

open Subgroup CFSG.Blueprint CFSG.LieType.Multipliers
open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22

theorem lift_m22CommWord_of_cover {W : Type*} [Group W] (g : Fin 2 → W)
    (hrel : ∀ r ∈ m22Cover, FreeGroup.lift g (FreeGroup.mk r) = 1) (i : Fin 2) :
    FreeGroup.lift g (FreeGroup.mk (m22CommWord i)) = g i := by
  have h1 : FreeGroup.lift g (FreeGroup.mk ((i, false) :: m22CommWord i)) = 1 :=
    hrel _ (List.mem_append_right _
      (List.mem_map_of_mem (List.mem_finRange i)))
  rw [show FreeGroup.mk ((i, false) :: m22CommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (m22CommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem isPerfect_closure_of_m22_cover {W : Type*} [Group W] (g : Fin 2 → W)
    (hrel : ∀ r ∈ m22Cover, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    Group.IsPerfect ↥(Subgroup.closure (Set.range g)) := by
  rw [Group.isPerfect_def]
  exact CFSG.Sporadic.Recognition.CoverBootstrap.commutator_eq_top_of_commutator_words g
    (fun i => FreeGroup.mk (m22CommWord i))
    (fun i => by simpa [m22CommWord] using mk_commWords_mem_commutator (m22Comm i))
    (lift_m22CommWord_of_cover g hrel)

theorem lift_m22B11 {W : Type*} [Group W] (g : Fin 2 → W) :
    FreeGroup.lift g (FreeGroup.mk m22B11) = g 1 ^ 11 := by
  have hword : m22B11 = List.replicate 11 ((1, true) : Fin 2 × Bool) := by
    simp [m22B11, m22Word, CFSG.Sporadic.Recognition.CoverRecipe.abLetter]
  rw [hword, CFSG.Sporadic.Recognition.CoverTransfer.mk_replicate, map_pow,
    FreeGroup.lift_apply_of]

theorem exists_surjective_quotient_le_center
    {W : Type*} [Group W] (g : Fin 2 → W) (p : W →* Equiv.Perm (Fin 22))
    (hp : ∀ i, p (g i) = ((m22Gen i : CFSG.Blueprint.NativeSporadic.M22) :
      Equiv.Perm (Fin 22)))
    {hζM : g 1 ^ 11 ∈ Subgroup.closure (Set.range g)}
    (hrel : ∀ r ∈ m22Cover, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    ∃ q : ↥(Subgroup.closure (Set.range g)) →* ↥CFSG.Blueprint.NativeSporadic.M22,
      Function.Surjective q ∧ q.ker ≤ Subgroup.center ↥(Subgroup.closure (Set.range g)) ∧
        q ⟨g 1 ^ 11, hζM⟩ = 1 := by
  classical
  let M : Subgroup W := Subgroup.closure (Set.range g)
  let g' : Fin 2 → ↥M := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hspan : Subgroup.closure (Set.range g') = ⊤ :=
    CFSG.GroupTheory.closure_range_subtype_eq_top (G := W) g
  have hle : M ≤ (CFSG.Blueprint.NativeSporadic.M22).comap p := by
    rw [show M = Subgroup.closure (Set.range g) from rfl, Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    change p (g i) ∈ CFSG.Blueprint.NativeSporadic.M22
    rw [hp i]
    exact (m22Gen i).2
  let q : ↥M →* ↥CFSG.Blueprint.NativeSporadic.M22 :=
    (p.comp M.subtype).codRestrict _ (fun m => hle m.2)
  have hq_gen (i : Fin 2) : q (g' i) = m22Gen i := Subtype.ext (hp i)
  have hq : Function.Surjective q := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    rw [← closure_m22Gen (m22TabCheck_eq_true), Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨g' i, hq_gen i⟩
  have hsub_comp : M.subtype.comp (FreeGroup.lift g') = FreeGroup.lift g :=
    FreeGroup.ext_hom _ _ (fun i => rfl)
  have hrel' : ∀ r ∈ coverRelators (wordSet m22Rels) m22CommW, FreeGroup.lift g' r = 1 := by
    intro r hr
    have hr' : r ∈ wordSet m22Cover := by
      rw [← coverRelators_wordSet m22Rels m22CommWord]
      exact hr
    simp only [wordSet, Set.mem_ofPred_eq, List.mem_map] at hr'
    obtain ⟨w, hw, rfl⟩ := hr'
    apply Subtype.ext
    have h := congrArg (fun φ : FreeGroup (Fin 2) →* W => φ (FreeGroup.mk w)) hsub_comp
    simp only [MonoidHom.comp_apply] at h
    change M.subtype ((FreeGroup.lift g') (FreeGroup.mk w)) = M.subtype 1
    rw [h, hrel w hw, map_one]
  let f : M22Cover →* ↥M := PresentedGroup.toGroup hrel'
  have hf_gen (i : Fin 2) : f (PresentedGroup.of i) = g' i :=
    PresentedGroup.toGroup.of hrel'
  have hcomp : q.comp f = m22Pi := by
    apply PresentedGroup.ext
    intro i
    rw [MonoidHom.comp_apply, hf_gen]
    exact (hq_gen i).trans (CFSG.LieType.Multipliers.coverMap_of
      (CFSG.Quasithin.HM22.isPresentation_m22)
      (lift_m22CommWord (m22TabCheck_eq_true)) i).symm
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hspan, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hf_gen i⟩
  have hfker_le : f.ker ≤ m22Pi.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h := congrArg (fun φ : M22Cover →* ↥CFSG.Blueprint.NativeSporadic.M22 => φ x) hcomp
    simp only [MonoidHom.comp_apply] at h
    rw [← h, hx, map_one]
  have hker_map : q.ker = m22Pi.ker.map f := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      obtain ⟨a, ha⟩ := hf x
      refine ⟨a, ?_, ha⟩
      change m22Pi a = 1
      have h := congrArg (fun φ : M22Cover →* ↥CFSG.Blueprint.NativeSporadic.M22 => φ a) hcomp
      simp only [MonoidHom.comp_apply] at h
      rw [← h, ha]
      exact hx
    · rintro ⟨a, ha, rfl⟩
      rw [MonoidHom.mem_ker]
      have h := congrArg (fun φ : M22Cover →* ↥CFSG.Blueprint.NativeSporadic.M22 => φ a) hcomp
      simp only [MonoidHom.comp_apply] at h
      rw [h]
      exact ha
  have hker_le_center : q.ker ≤ Subgroup.center ↥M := by
    rw [hker_map]
    intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    have hacent : a ∈ Subgroup.center M22Cover :=
      (CFSG.LieType.Multipliers.coverMap_ker_le_center
        (CFSG.Quasithin.HM22.isPresentation_m22)
        (lift_m22CommWord (m22TabCheck_eq_true))) ha
    exact Subgroup.map_center_le_center hf (Subgroup.mem_map_of_mem f hacent)
  have hqζ : q ⟨g 1 ^ 11, hζM⟩ = 1 := by
    apply Subtype.ext
    change p (g 1 ^ 11) = 1
    rw [map_pow, hp 1]
    have h := (CFSG.Quasithin.HM22.isPresentation_m22).lift_eq_one
      (r := FreeGroup.mk m22B11) (List.mem_map_of_mem m22B11_mem)
    rw [lift_m22B11 m22Gen] at h
    simpa using congrArg Subtype.val h
  exact ⟨q, hq, hker_le_center, hqζ⟩

theorem coverRelators_lift_subtype {W : Type*} [Group W] (g : Fin 2 → W)
    (g' : Fin 2 → ↥(Subgroup.closure (Set.range g)))
    (hg' : ∀ i, (g' i : W) = g i)
    (hrel : ∀ r ∈ m22Cover, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    ∀ r ∈ coverRelators (wordSet m22Rels) m22CommW, FreeGroup.lift g' r = 1 := by
  have hsub_comp : (Subgroup.closure (Set.range g)).subtype.comp (FreeGroup.lift g') =
      FreeGroup.lift g := FreeGroup.ext_hom _ _ (fun i => by
        simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
        exact hg' i)
  intro r hr
  have hr' : r ∈ wordSet m22Cover := by
    rw [← coverRelators_wordSet m22Rels m22CommWord]
    exact hr
  simp only [wordSet, Set.mem_ofPred_eq, List.mem_map] at hr'
  obtain ⟨w, hw, rfl⟩ := hr'
  apply Subtype.ext
  have h := congrArg (fun φ : FreeGroup (Fin 2) →* W => φ (FreeGroup.mk w)) hsub_comp
  simp only [MonoidHom.comp_apply] at h
  change (Subgroup.closure (Set.range g)).subtype ((FreeGroup.lift g') (FreeGroup.mk w)) =
    (Subgroup.closure (Set.range g)).subtype 1
  rw [h, hrel w hw, map_one]

theorem zeta_mem_center_of_m22_cover {W : Type*} [Group W] (g : Fin 2 → W)
    (hrel : ∀ r ∈ m22Cover, FreeGroup.lift g (FreeGroup.mk r) = 1)
    {hζM : g 1 ^ 11 ∈ Subgroup.closure (Set.range g)} :
    (⟨g 1 ^ 11, hζM⟩ : ↥(Subgroup.closure (Set.range g))) ∈
      Subgroup.center ↥(Subgroup.closure (Set.range g)) := by
  classical
  let M : Subgroup W := Subgroup.closure (Set.range g)
  let g' : Fin 2 → ↥M := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hspan : Subgroup.closure (Set.range g') = ⊤ :=
    CFSG.GroupTheory.closure_range_subtype_eq_top (G := W) g
  have hrel' : ∀ r ∈ coverRelators (wordSet m22Rels) m22CommW, FreeGroup.lift g' r = 1 :=
    coverRelators_lift_subtype g g' (fun i => rfl) hrel
  let θ : ↥M := FreeGroup.lift g' (FreeGroup.mk m22B11)
  have hθ_eq : θ = ⟨g 1 ^ 11, hζM⟩ := by
    apply Subtype.ext
    have hsub_comp : M.subtype.comp (FreeGroup.lift g') = FreeGroup.lift g :=
      FreeGroup.ext_hom _ _ (fun i => rfl)
    have h := congrArg (fun φ : FreeGroup (Fin 2) →* W => φ (FreeGroup.mk m22B11)) hsub_comp
    simp only [MonoidHom.comp_apply] at h
    change M.subtype ((FreeGroup.lift g') (FreeGroup.mk m22B11)) = g 1 ^ 11
    rw [h, lift_m22B11 g]
  have hcomm_gen : ∀ i, g' i * θ = θ * g' i := by
    intro i
    have hc := (lift_coverRelators_eq_one_iff.mp hrel').1 i (FreeGroup.mk m22B11)
      (List.mem_map_of_mem m22B11_mem)
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  have hθ_center : θ ∈ Subgroup.center ↥M := by
    have hgen : (↑(Subgroup.closure (Set.range g')) : Set ↥M) = Set.univ := by rw [hspan]; rfl
    rw [← Subgroup.centralizer_univ, ← hgen, Subgroup.centralizer_closure]
    rintro _ ⟨i, rfl⟩
    exact hcomm_gen i
  rwa [hθ_eq] at hθ_center

theorem card_center_eq_two_of_m22_cover {W : Type*} [Group W] (g : Fin 2 → W)
    (hrel : ∀ r ∈ m22Cover, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hcent : ∀ x : W, (∀ m ∈ Subgroup.closure (Set.range g), x * m = m * x) →
      x = 1 ∨ x = g 1 ^ 11)
    (hζ : g 1 ^ 11 ≠ 1) (hζ2 : g 1 ^ 22 = 1) :
    Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range g))) = 2 := by
  classical
  let M : Subgroup W := Subgroup.closure (Set.range g)
  have hζM : g 1 ^ 11 ∈ M := M.pow_mem (Subgroup.subset_closure ⟨(1 : Fin 2), rfl⟩) 11
  let ζM : ↥M := ⟨g 1 ^ 11, hζM⟩
  have hζ_center : ζM ∈ Subgroup.center ↥M :=
    zeta_mem_center_of_m22_cover g hrel (hζM := hζM)
  have hsubset : Subgroup.center ↥M ≤ Subgroup.zpowers ζM := by
    intro z hz
    have hcomm : ∀ m ∈ M, (z : W) * m = m * (z : W) := by
      intro m hm
      exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨m, hm⟩)).symm
    rcases hcent z.val hcomm with h1 | h1
    · rw [Subgroup.mem_zpowers_iff]
      exact ⟨0, Subtype.ext (by simpa using h1.symm)⟩
    · rw [Subgroup.mem_zpowers_iff]
      refine ⟨1, ?_⟩
      rw [zpow_one]
      exact Subtype.ext h1.symm
  have hsuperset : Subgroup.zpowers ζM ≤ Subgroup.center ↥M :=
    Subgroup.zpowers_le.mpr hζ_center
  have hcenter : Subgroup.center ↥M = Subgroup.zpowers ζM :=
    le_antisymm hsubset hsuperset
  have hζM_ne_one : ζM ≠ 1 := by
    intro h
    exact hζ (by simpa [ζM] using congrArg Subtype.val h)
  have hζM_sq : ζM * ζM = 1 := by
    apply Subtype.ext
    change (g 1 ^ 11) * (g 1 ^ 11) = 1
    rw [← pow_add]
    norm_num
    exact hζ2
  have horder : orderOf ζM = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hζM_sq) hζM_ne_one
  rw [hcenter, Nat.card_zpowers, horder]

end CFSG.Quasithin.TwoM22

namespace CFSG.Quasithin.TwoM22

open Subgroup CFSG.Blueprint CFSG.LieType.Multipliers
open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22

theorem isTwoM22TwoModel_of_gens
    {W : Type} [Group W] [Finite W] (g : Fin 2 → W) (T : W) (p : W →* Equiv.Perm (Fin 22))
    (hp : ∀ i, p (g i) = ((CFSG.Sporadic.Recognition.M22Multiplier.m22Gen i :
      CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)))
    (hrel : ∀ r ∈ CFSG.Sporadic.Recognition.M22Multiplier.m22Cover,
      FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hζ : g 1 ^ 11 ≠ 1) (hζ2 : g 1 ^ 22 = 1) (hTT : T * T = 1)
    (hTconj : ∀ i, T * g i * T⁻¹ ∈ Subgroup.closure (Set.range g))
    (hTM : T ∉ Subgroup.closure (Set.range g))
    (hcent : ∀ x : W, (∀ m ∈ Subgroup.closure (Set.range g), x * m = m * x) →
      x = 1 ∨ x = g 1 ^ 11)
    (S : Subgroup W) (hS : S ≤ Subgroup.closure (Set.range g) ⊔ Subgroup.zpowers T)
    (hScard : Nat.card S = 2 ^ 9)
    (hSsq : ∀ y ∈ S, y ∉ Subgroup.closure (Set.range g) → y * y ≠ g 1 ^ 11) :
    IsTwoM22TwoModel (Subgroup.closure (Set.range g)) T := by
  classical
  have hζM : g 1 ^ 11 ∈ Subgroup.closure (Set.range g) :=
    Subgroup.pow_mem (Subgroup.closure (Set.range g))
      (Subgroup.subset_closure ⟨(1 : Fin 2), rfl⟩) 11
  obtain ⟨q, hq, hker_le_center, hqζ⟩ :=
    exists_surjective_quotient_le_center g p hp (hζM := hζM) hrel
  have hperf : Group.IsPerfect ↥(Subgroup.closure (Set.range g)) :=
    isPerfect_closure_of_m22_cover g hrel
  have hcard_center : Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range g))) = 2 :=
    card_center_eq_two_of_m22_cover g hrel hcent hζ hζ2
  have hcenter_le_ker : Subgroup.center ↥(Subgroup.closure (Set.range g)) ≤ q.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hcomm : ∀ m ∈ Subgroup.closure (Set.range g),
        (z : W) * m = m * (z : W) := by
      intro m hm
      exact (congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hz) ⟨m, hm⟩)).symm
    rcases hcent z.val hcomm with h1 | h1
    · rw [show z = 1 from Subtype.ext h1]
      exact map_one q
    · rw [show z = (⟨g 1 ^ 11, hζM⟩ : ↥(Subgroup.closure (Set.range g))) from Subtype.ext h1]
      exact hqζ
  have hker : q.ker = Subgroup.center ↥(Subgroup.closure (Set.range g)) :=
    le_antisymm hker_le_center hcenter_le_ker
  have hcardM : Nat.card ↥(Subgroup.closure (Set.range g)) = 2 * 443520 :=
    card_eq_two_mul_card_M22_of_central_extension q hq hker hcard_center
  have hconjM : ∀ m ∈ Subgroup.closure (Set.range g),
      T * m * T⁻¹ ∈ Subgroup.closure (Set.range g) := by
    intro m hm
    refine Subgroup.closure_induction
      (p := fun x _ => T * x * T⁻¹ ∈ Subgroup.closure (Set.range g)) ?_ ?_ ?_ ?_ hm
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hTconj i
    · simpa using (Subgroup.one_mem (Subgroup.closure (Set.range g)))
    · intro x y _ _ ihx ihy
      have h : T * (x * y) * T⁻¹ = (T * x * T⁻¹) * (T * y * T⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x _ ih
      have h : T * x⁻¹ * T⁻¹ = (T * x * T⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ih
  refine ⟨hperf, ?_, hcard_center, hTT, hTM, hconjM, ?_, ?_⟩
  · exact ⟨q, hq, hker⟩
  · intro x hx
    rcases hcent x hx with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.pow_mem (Subgroup.closure (Set.range g))
        (Subgroup.subset_closure ⟨(1 : Fin 2), rfl⟩) 11
  · intro m hm hycent
    set y : W := m * T with hydef
    have hyM : y ∉ Subgroup.closure (Set.range g) := by
      intro hy
      apply hTM
      have h : T = m⁻¹ * y := by rw [hydef]; group
      rw [h]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hy
    have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hTT
    have hy2M : y * y ∈ Subgroup.closure (Set.range g) := by
      have h : y * y = m * (T * m * T⁻¹) := by
        rw [hydef]
        calc (m * T) * (m * T) = m * (T * m * T⁻¹) * (T * T) := by group
          _ = m * (T * m * T⁻¹) := by rw [hTT, mul_one]
      rw [h]
      exact Subgroup.mul_mem _ hm (hconjM m hm)
    by_contra hne
    have hy2_eq : y * y = g 1 ^ 11 :=
      (hcent (y * y) hycent).resolve_left hne
    let N : Subgroup W := Subgroup.closure (Set.range g) ⊔ Subgroup.zpowers T
    have hTN : T ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers T)
    have hMN : Subgroup.closure (Set.range g) ≤ N := le_sup_left
    have hyN : y ∈ N := by
      rw [hydef]
      exact N.mul_mem (hMN hm) hTN
    have hTnorm : T ∈ Subgroup.normalizer
        ((Subgroup.closure (Set.range g) : Subgroup W) : Set W) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hconjM x
      · intro hx
        have h2 : T * (T * x * T⁻¹) * T⁻¹ = x := by
          rw [hTinv]
          calc T * (T * x * T) * T = (T * T) * x * (T * T) := by group
            _ = x := by rw [hTT]; group
        have hx' := hconjM (T * x * T⁻¹) hx
        rwa [h2] at hx'
    have hNnorm : N ≤ Subgroup.normalizer
        ((Subgroup.closure (Set.range g) : Subgroup W) : Set W) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hz) (Subgroup.inv_mem _ hx)
        · intro hz
          have h := Subgroup.mul_mem _
            (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hz) hx
          rwa [show x⁻¹ * (x * z * x⁻¹) * x = z by group] at h
      · exact Subgroup.zpowers_le.mpr hTnorm
    have hidx : ((Subgroup.closure (Set.range g)).subgroupOf N).index = 2 := by
      refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨T, hTN⟩, ?_, ?_⟩
      · change T ∉ Subgroup.closure (Set.range g)
        exact hTM
      · intro b
        by_cases hb : b ∈ (Subgroup.closure (Set.range g)).subgroupOf N
        · exact Or.inr hb
        · left
          have hbW : (b : W) ∉ Subgroup.closure (Set.range g) := by
            intro h
            exact hb h
          have hbN : (b : W) ∈ Subgroup.closure (Set.range g) ⊔ Subgroup.zpowers T := b.2
          rcases CFSG.Quasithin.B19.mem_or_mul_mem_of_mem_sup hTT hconjM hbN with
            hmem | hmem
          · exact absurd hmem hbW
          · show ((b * (⟨T, hTN⟩ : ↥N) : ↥N) : W) ∈ Subgroup.closure (Set.range g)
            simpa using hmem
    have hcardN : Nat.card ↥N = 2 * Nat.card ↥(Subgroup.closure (Set.range g)) := by
      have h := Subgroup.card_mul_index ((Subgroup.closure (Set.range g)).subgroupOf N)
      rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv] at h
      rw [← h, mul_comm]
    have hcardN2 : Nat.card ↥N = 2 ^ 9 * 3465 := by
      rw [hcardN, hcardM]
      norm_num
    have hfact : (Nat.card ↥N).factorization 2 = 9 := by
      rw [hcardN2, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3465)]
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S N :=
      CFSG.ABGLocalTools.isSylowOf_of_card hS (by rw [hfact, hScard])
    have hy4 : y ^ 4 = 1 := by
      have h4 : y ^ 4 = (y * y) * (y * y) := by
        rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
      rw [h4, hy2_eq]
      rw [← pow_add]
      norm_num
      exact hζ2
    have hdvd : orderOf y ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hy4
    have hdvd' : orderOf y ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hdvd'
    let X : Subgroup W := Subgroup.zpowers y
    have hXN : X ≤ N := Subgroup.zpowers_le.mpr hyN
    have hX : IsPGroup 2 X :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk2])
    obtain ⟨S₂, hS₂⟩ := (hX.comap_subtype (K := N)).exists_le_sylow
    let P' : Subgroup W := (S₂ : Subgroup ↥N).map N.subtype
    have hP'syl : CFSG.ABGLocalTools.IsSylowOf 2 P' N := ⟨S₂, rfl⟩
    have hXP' : X ≤ P' := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨(⟨x, hXN hx⟩ : ↥N), hS₂ hx, rfl⟩
    obtain ⟨k, hkN, hkconj⟩ := hSyl.exists_mem_conj hP'syl
    have hyP' : y ∈ P' := hXP' (Subgroup.mem_zpowers y)
    have hkyS : k⁻¹ * y * k ∈ S := (hkconj y).mp hyP'
    have hkNorm : k ∈ Subgroup.normalizer
        ((Subgroup.closure (Set.range g) : Subgroup W) : Set W) := hNnorm hkN
    have hkinvNorm : k⁻¹ ∈ Subgroup.normalizer
        ((Subgroup.closure (Set.range g) : Subgroup W) : Set W) :=
      (Subgroup.normalizer _).inv_mem hkNorm
    have hzNotM : k⁻¹ * y * k ∉ Subgroup.closure (Set.range g) := by
      intro hz
      exact hyM ((Subgroup.mem_normalizer_iff.mp hkinvNorm y).mpr (by simpa using hz))
    have hζ_center : (⟨g 1 ^ 11, hζM⟩ : ↥(Subgroup.closure (Set.range g))) ∈
        Subgroup.center ↥(Subgroup.closure (Set.range g)) :=
      zeta_mem_center_of_m22_cover g hrel (hζM := hζM)
    have hζ_comm : ∀ x ∈ Subgroup.closure (Set.range g),
        (g 1 ^ 11) * x = x * (g 1 ^ 11) := by
      intro x hx
      exact (congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hζ_center) ⟨x, hx⟩)).symm
    have hkζ : k⁻¹ * (g 1 ^ 11) * k = g 1 ^ 11 := by
      have hcentral : ∀ x ∈ Subgroup.closure (Set.range g),
          (k⁻¹ * (g 1 ^ 11) * k) * x = x * (k⁻¹ * (g 1 ^ 11) * k) := by
        intro x hx
        have hkx : k * x * k⁻¹ ∈ Subgroup.closure (Set.range g) :=
          (Subgroup.mem_normalizer_iff.mp hkNorm x).mp hx
        calc (k⁻¹ * (g 1 ^ 11) * k) * x
            = k⁻¹ * ((g 1 ^ 11) * (k * x * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * x * k⁻¹) * (g 1 ^ 11)) * k := by rw [hζ_comm _ hkx]
          _ = x * (k⁻¹ * (g 1 ^ 11) * k) := by group
      rcases hcent (k⁻¹ * (g 1 ^ 11) * k) hcentral with h1 | h1
      · exfalso
        apply hζ
        calc g 1 ^ 11 = k * (k⁻¹ * (g 1 ^ 11) * k) * k⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · exact h1
    have hzsq : (k⁻¹ * y * k) * (k⁻¹ * y * k) = g 1 ^ 11 := by
      calc (k⁻¹ * y * k) * (k⁻¹ * y * k) = k⁻¹ * (y * y) * k := by group
        _ = k⁻¹ * (g 1 ^ 11) * k := by rw [hy2_eq]
        _ = g 1 ^ 11 := hkζ
    exact hSsq (k⁻¹ * y * k) hkyS hzNotM hzsq

end CFSG.Quasithin.TwoM22
