module

public import CFSG.Quasithin.H13.NQSetupCcomponent
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwoModule
public import CFSG.GroupTheory.LocalCores.Components

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup Matrix

theorem pow_prime_eq_one_of_mulVec_eq_self {p : ℕ} [Fact p.Prime] {g : GL (Fin 2) (ZMod p)}
    (hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1) {v : Fin 2 → ZMod p} (hv : v ≠ 0)
    (hgv : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = v) : g ^ p = 1 := by
  obtain ⟨Q, hQ⟩ := CFSG.SectionRank.Ccomm.exists_GL_mulVec_single_eq hv
  set g' := Q⁻¹ * g * Q with hg'
  have he : (g' : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [hg', Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hQ, hgv, ← hQ,
      mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have h00 : (g' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := by
    simpa [mulVec_single_one] using congrFun he 0
  have h10 : (g' : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
    simpa [mulVec_single_one] using congrFun he 1
  have hdet' : (g' : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    rw [hg', Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  have h11 : (g' : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
    have h := hdet'
    rw [det_fin_two, h00, h10] at h
    simpa using h
  set c := (g' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 with hc
  have hform : (g' : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, c; 0, 1] := by
    rw [eta_fin_two (g' : Matrix (Fin 2) (Fin 2) (ZMod p)), h00, h10, h11]
  have hpow : ∀ n : ℕ, ((g' ^ n : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![1, (n : ZMod p) * c; 0, 1] := by
    intro n
    induction n with
    | zero => simp [one_fin_two]
    | succ n ih =>
      rw [pow_succ, Units.val_mul, ih, hform, mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [add_mul, add_comm]
  have hg'p : g' ^ p = 1 := by
    apply Units.ext
    rw [hpow, ZMod.natCast_self, zero_mul, Units.val_one, one_fin_two]
  have hg : g = MulAut.conj Q g' := by
    rw [MulAut.conj_apply, hg']
    group
  rw [hg, ← map_pow, hg'p, map_one]

theorem ccomponent_GL2_radical
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type*} [Group L]
    [Finite L] (hL : CFSG.IsCComponent (⊤ : Subgroup L)) (ρ : L →* GL (Fin 2) (ZMod p))
    (hρ : ρ ≠ 1) :
    (∀ l : L, l ∈ CFSG.solvableRadical L ↔ ρ l = 1 ∨ ρ l = -1) ∧ (∃ l : L, ρ l = -1) ∧
      (∀ l : L, ((ρ l : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1) ∧
      (∀ l : L, ρ l ^ 2 = 1 → ρ l = 1 ∨ ρ l = -1) ∧
      ∀ l : L, (∀ l' : L, ρ l * ρ l' = ρ l' * ρ l) → ρ l = 1 ∨ ρ l = -1 := by
  classical
  have : Group.IsPerfect L := ⟨by rw [commutator_def]; exact hL.2.1⟩
  set J := ρ.range with hJ
  have : Group.IsPerfect J := Group.IsPerfect.range ρ
  have hJne : J ≠ ⊥ := by
    intro hbot
    apply hρ
    ext l
    have : ρ l ∈ J := ⟨l, rfl⟩
    rw [hbot, mem_bot] at this
    rw [this]
    rfl
  obtain ⟨-, hcen, hJq, -⟩ := CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition hp2 J hJne
  have hneg := CFSG.SectionRank.Ccomm.neg_one_mem_of_perfect hp2 J hJne
  have hdet : ∀ l : L, ((ρ l : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 :=
    fun l => CFSG.SectionRank.Ccomm.det_eq_one_of_perfect J ⟨l, rfl⟩
  have hJqF : CFSG.IsQuasisimple J := by
    refine ⟨inferInstance, hJq.2, ?_⟩
    have : IsSimpleGroup (J ⧸ center J) := hJq.2
    have : Nontrivial (J ⧸ center J) := IsSimpleGroup.toNontrivial
    by_contra hab
    push Not at hab
    have hcomm : commutator (J ⧸ center J) = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [mem_centralizer_iff]
      intro b _
      exact hab b a
    have : Group.IsPerfect (J ⧸ center J) := inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hcomm
    exact top_ne_bot hcomm
  have : (CFSG.solvableRadical L).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hRsolv : Group.IsSolvable (CFSG.solvableRadical L) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  set R := CFSG.solvableRadical L with hR
  have hker : ρ.ker ≤ R := by
    refine le_solvableRadical_of_normal_ne_top hL fun htop => hρ ?_
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ ρ.ker := by rw [htop]; exact mem_top x
    simpa using hx
  have hRbar : R.map ρ.rangeRestrict ≤ center J := by
    have hn : (R.map ρ.rangeRestrict).Normal :=
      Normal.map inferInstance _ ρ.rangeRestrict_surjective
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJqF hn with h | h
    · exfalso
      have : Group.IsSolvable (R.map ρ.rangeRestrict) :=
        Group.isSolvable_of_surjective (ρ.rangeRestrict.subgroupMap_surjective R)
      have hJs : Group.IsSolvable J := by
        rw [h] at this
        exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup J).subtype)
          fun x => ⟨⟨x, mem_top x⟩, rfl⟩
      have : Nontrivial J := (nontrivial_iff_ne_bot J).2 hJne
      exact Group.IsPerfect.not_isSolvable J hJs
    · exact h
  have hC : (center J).comap ρ.rangeRestrict ≤ R := by
    set C := (center J).comap ρ.rangeRestrict with hCdef
    have hCn : C.Normal := Normal.comap inferInstance _
    have hNC : ρ.ker ≤ C := fun x hx => by
      rw [hCdef, mem_comap]
      have : ρ.rangeRestrict x = 1 := Subtype.ext (by simpa using hx)
      rw [this]
      exact one_mem _
    have hNs : Group.IsSolvable ρ.ker := by
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hker)
    have hCs : Group.IsSolvable C := by
      let g : C →* center J := (ρ.rangeRestrict.comp C.subtype).codRestrict (center J) fun x => x.2
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNC) g fun x hx => ?_
      have hx1 : ρ x = 1 := by
        rw [MonoidHom.mem_ker] at hx
        have h1 : ((g x : center J) : J) = 1 := by rw [hx]; rfl
        have h2 : ((g x : center J) : J) = ρ.rangeRestrict x := rfl
        rw [h2] at h1
        exact congrArg Subtype.val h1
      exact ⟨⟨x, hx1⟩, rfl⟩
    exact (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).2.2.1 C hCn hCs
  refine ⟨fun l => ⟨fun hl => ?_, fun hl => ?_⟩, ?_, hdet, fun l hl => ?_, fun l hl => ?_⟩
  · have h1 : ρ.rangeRestrict l ∈ center J := hRbar ⟨l, hl, rfl⟩
    exact (hcen _).1 h1
  · exact hC ((hcen _).2 hl)
  · obtain ⟨l, hl⟩ := hneg
    exact ⟨l, hl⟩
  · have := CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one
      (CFSG.SectionRank.Ccomm.two_ne_zero_zmod hp2) (hdet l)
      (show ((ρ l : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        ((ρ l : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 by
          rw [← Units.val_mul, ← sq, hl, Units.val_one])
    rcases this with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  · refine (hcen ⟨ρ l, l, rfl⟩).1 (mem_center_iff.2 fun y => ?_)
    obtain ⟨l', hl'⟩ := y.2
    apply Subtype.ext
    change (y : GL (Fin 2) (ZMod p)) * ρ l = ρ l * y
    rw [← hl']
    exact (hl l').symm

@[expose] noncomputable def glEquivMatrix {p : ℕ} [Fact p.Prime] {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W]
    (b : Module.Basis (Fin 2) (ZMod p) W) : (W ≃ₗ[ZMod p] W) ≃* GL (Fin 2) (ZMod p) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) W).symm.trans
    (CFSG.SectionRank.Ccomm.glEquivOfBasis b)

theorem glEquivMatrix_val {p : ℕ} [Fact p.Prime] {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W]
    (b : Module.Basis (Fin 2) (ZMod p) W) (g : W ≃ₗ[ZMod p] W) :
    ((glEquivMatrix b g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      LinearMap.toMatrix b b (g : W →ₗ[ZMod p] W) :=
  rfl

theorem glEquivMatrix_eq_neg_one_iff {p : ℕ} [Fact p.Prime] {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W]
    (b : Module.Basis (Fin 2) (ZMod p) W) (g : W ≃ₗ[ZMod p] W) :
    glEquivMatrix b g = -1 ↔ g = LinearEquiv.neg (ZMod p) := by
  have hneg : glEquivMatrix b (LinearEquiv.neg (ZMod p)) = -1 := by
    apply Units.ext
    rw [glEquivMatrix_val, Units.val_neg, Units.val_one]
    have : ((LinearEquiv.neg (ZMod p) : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W) = -LinearMap.id := by
      ext w
      simp
    rw [this, map_neg, LinearMap.toMatrix_id]
  rw [← hneg]
  exact (glEquivMatrix b).injective.eq_iff

theorem ccomponent_plane_radical
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type*} [Group L]
    [Finite L] (hL : CFSG.IsCComponent (⊤ : Subgroup L)) {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W] (hW : Module.finrank (ZMod p) W = 2) (α : L →* (W ≃ₗ[ZMod p] W))
    (hα : α ≠ 1) :
    (∀ l : L, l ∈ CFSG.solvableRadical L ↔ α l = 1 ∨ α l = LinearEquiv.neg (ZMod p)) ∧
      (∃ l : L, α l = LinearEquiv.neg (ZMod p)) ∧
      (∀ l : L, α l ^ 2 = 1 → α l = 1 ∨ α l = LinearEquiv.neg (ZMod p)) ∧
      ∀ l : L, (∀ l' : L, α l * α l' = α l' * α l) →
        α l = 1 ∨ α l = LinearEquiv.neg (ZMod p) := by
  have : Module.Finite (ZMod p) W := Module.finite_of_finrank_eq_succ hW
  set b := Module.finBasisOfFinrankEq (ZMod p) W hW
  set Ψ := glEquivMatrix b
  set ρ : L →* GL (Fin 2) (ZMod p) := Ψ.toMonoidHom.comp α with hρ
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply hα
    refine MonoidHom.ext fun l => Ψ.injective ?_
    have := DFunLike.congr_fun h l
    simpa [hρ] using this
  have h1 : ∀ l, ρ l = 1 ↔ α l = 1 := fun l => by
    simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact Ψ.map_eq_one_iff
  have hn : ∀ l, ρ l = -1 ↔ α l = LinearEquiv.neg (ZMod p) := fun l =>
    glEquivMatrix_eq_neg_one_iff b (α l)
  obtain ⟨hR, ⟨l₀, hl₀⟩, -, hinv, hcen⟩ := ccomponent_GL2_radical hp2 hL ρ hρ1
  refine ⟨fun l => by rw [hR, h1, hn], ⟨l₀, (hn l₀).1 hl₀⟩, fun l hl => ?_, fun l hl => ?_⟩
  · have : ρ l ^ 2 = 1 := by
      simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_pow, hl, map_one]
    rcases hinv l this with h | h
    · exact Or.inl ((h1 l).1 h)
    · exact Or.inr ((hn l).1 h)
  · have : ∀ l', ρ l * ρ l' = ρ l' * ρ l := fun l' => by
      simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul, hl l']
    rcases hcen l this with h | h
    · exact Or.inl ((h1 l).1 h)
    · exact Or.inr ((hn l).1 h)

theorem card_eq_card_ker_mul_card_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {H : Subgroup G} (hH : f.ker ≤ H) : Nat.card H = Nat.card f.ker * Nat.card (H.map f) := by
  have h1 := Subgroup.card_ker_mul_card_range (f.comp H.subtype)
  have hker : (f.comp H.subtype).ker = f.ker.subgroupOf H := by
    ext x
    simp [mem_subgroupOf]
  have hrange : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv] at h1
  exact h1.symm

theorem neg_mul_eq_mul_neg {k W : Type*} [CommRing k] [AddCommGroup W] [Module k W]
    (g : W ≃ₗ[k] W) : LinearEquiv.neg k * g = g * LinearEquiv.neg k :=
  LinearEquiv.ext fun w => by simp

theorem prime_plane_radical_preimages_of_two_valuation_one_have_cyclic_four_Sylow_images
    {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) {L : Type*} [Group L] [Finite L]
    [(CFSG.solvableRadical L).Normal] (hL : CFSG.IsCComponent (⊤ : Subgroup L)) {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] (hW : Module.finrank (ZMod p) W = 2)
    (α : L →* (W ≃ₗ[ZMod p] W)) (hα : α ≠ 1) :
    (center α.range).comap α.rangeRestrict = CFSG.solvableRadical L ∧
      (CFSG.solvableRadical L).map α.rangeRestrict = center α.range ∧
      ((center α.range).map α.range.subtype : Set (W ≃ₗ[ZMod p] W)) =
        {1, LinearEquiv.neg (ZMod p)} ∧
      ∀ H : Subgroup L, CFSG.solvableRadical L ≤ H → ∀ m : ℕ, Odd m →
        Nat.card (H.map (QuotientGroup.mk' (CFSG.solvableRadical L))) = 2 * m →
        ∀ S : Sylow 2 H, IsCyclic ((S : Subgroup H).map (α.comp H.subtype)) ∧
          Nat.card ((S : Subgroup H).map (α.comp H.subtype)) = 4 := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hR, ⟨l₀, hl₀⟩, hinv, hcen⟩ := ccomponent_plane_radical hp2 hL hW α hα
  set R := CFSG.solvableRadical L with hRdef
  have hcenJ : ∀ l : L, α.rangeRestrict l ∈ center α.range ↔ l ∈ R := by
    intro l
    rw [hR, mem_center_iff]
    constructor
    · intro h
      refine hcen l fun l' => ?_
      have := congrArg Subtype.val (h (α.rangeRestrict l'))
      exact this.symm
    · rintro (h | h) y
      · apply Subtype.ext
        change (y : W ≃ₗ[ZMod p] W) * α l = α l * y
        rw [h, one_mul, mul_one]
      · apply Subtype.ext
        change (y : W ≃ₗ[ZMod p] W) * α l = α l * y
        rw [h]
        exact (neg_mul_eq_mul_neg _).symm
  have h1 : (center α.range).comap α.rangeRestrict = R := by
    ext l
    rw [mem_comap]
    exact hcenJ l
  have h2 : R.map α.rangeRestrict = center α.range := by
    ext z
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (hcenJ l).2 hl
    · intro hz
      obtain ⟨l, rfl⟩ := α.rangeRestrict_surjective z
      exact ⟨l, (hcenJ l).1 hz, rfl⟩
  have h3 : ((center α.range).map α.range.subtype : Set (W ≃ₗ[ZMod p] W)) =
      {1, LinearEquiv.neg (ZMod p)} := by
    ext g
    simp only [coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨l, rfl⟩ := α.rangeRestrict_surjective z
      exact (hR l).1 ((hcenJ l).1 hz)
    · rintro (rfl | rfl)
      · exact ⟨1, one_mem _, rfl⟩
      · refine ⟨α.rangeRestrict l₀, (hcenJ l₀).2 ((hR l₀).2 (Or.inr hl₀)), ?_⟩
        exact hl₀
  refine ⟨h1, h2, h3, fun H hRH m hm hcard S => ?_⟩
  have : Module.Finite (ZMod p) W := Module.finite_of_finrank_eq_succ hW
  have : Nontrivial W := Module.nontrivial_of_finrank_eq_succ hW
  have : Finite W := Module.finite_of_finite (ZMod p)
  have : Finite (W ≃ₗ[ZMod p] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod p] W => (e : W → W)) DFunLike.coe_injective
  have hne : (1 : W ≃ₗ[ZMod p] W) ≠ LinearEquiv.neg (ZMod p) := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h' := LinearEquiv.congr_fun h w
    simp only [LinearEquiv.coe_one, id_eq, LinearEquiv.coe_neg, Pi.neg_apply] at h'
    have h2w : (2 : ZMod p) • w = 0 := by rw [two_smul]; nth_rewrite 1 [h']; exact neg_add_cancel w
    rcases smul_eq_zero.1 h2w with h0 | h0
    · exact CFSG.SectionRank.Ccomm.two_ne_zero_zmod hp2 h0
    · exact hw h0
  have hRker : α.ker ≤ R := fun l hl => (hR l).2 (Or.inl hl)
  have hRmap : (R.map α : Set (W ≃ₗ[ZMod p] W)) = {1, LinearEquiv.neg (ZMod p)} := by
    ext g
    simp only [coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (hR l).1 hl
    · rintro (rfl | rfl)
      · exact ⟨1, one_mem _, map_one α⟩
      · exact ⟨l₀, (hR l₀).2 (Or.inr hl₀), hl₀⟩
  have hRcard : Nat.card (R.map α) = 2 := by
    rw [← SetLike.coe_sort_coe, hRmap, Nat.card_coe_set_eq, Set.ncard_pair hne]
  have hHR : Nat.card H = Nat.card R * (2 * m) := by
    have := card_eq_card_ker_mul_card_map (QuotientGroup.mk' R) (H := H)
      (by rw [QuotientGroup.ker_mk']; exact hRH)
    rw [QuotientGroup.ker_mk', hcard] at this
    exact this
  have hRk : Nat.card R = Nat.card α.ker * 2 := by
    rw [card_eq_card_ker_mul_card_map α hRker, hRcard]
  have hHk : Nat.card H = Nat.card α.ker * Nat.card (H.map α) :=
    card_eq_card_ker_mul_card_map α (hRker.trans hRH)
  have hkpos : 0 < Nat.card α.ker := Nat.card_pos
  have hHmap : Nat.card (H.map α) = 4 * m := by
    have : Nat.card α.ker * Nat.card (H.map α) = Nat.card α.ker * (4 * m) := by
      rw [← hHk, hHR, hRk]
      ring
    exact Nat.eq_of_mul_eq_mul_left hkpos this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := α.subgroupMap H with hf
  set S' : Sylow 2 (H.map α) := S.mapSurjective (α.subgroupMap_surjective H) with hS'
  have : Finite (H.map α) := Finite.of_surjective _ (α.subgroupMap_surjective H)
  have hS'card : Nat.card S' = 4 := by
    rw [Sylow.card_eq_multiplicity, hHmap]
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.2 ⟨0, rfl⟩) hm
    have hfac : Nat.factorization (4 * m) 2 = 2 := by
      rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hm)),
        show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self Nat.prime_two]
      norm_num
    rw [hfac]
    norm_num
  have hSS' : Nat.card ((S : Subgroup H).map (α.comp H.subtype)) = Nat.card S' := by
    rw [hS', Sylow.coe_mapSurjective]
    have e : (S : Subgroup H).map (α.comp H.subtype) =
        ((S : Subgroup H).map f).map (H.map α).subtype := by
      rw [Subgroup.map_map]
      rfl
    rw [e, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have h4 : Nat.card ((S : Subgroup H).map (α.comp H.subtype)) = 4 := hSS'.trans hS'card
  refine ⟨?_, h4⟩
  by_contra hcyc
  have hle : (S : Subgroup H).map (α.comp H.subtype) ≤ zpowers (LinearEquiv.neg (ZMod p)) := by
    rintro _ ⟨s, hs, rfl⟩
    have hord : orderOf (⟨(α.comp H.subtype) s, s, hs, rfl⟩ :
        (S : Subgroup H).map (α.comp H.subtype)) ∣ 2 := by
      have hdvd := orderOf_dvd_natCard (⟨(α.comp H.subtype) s, s, hs, rfl⟩ :
        (S : Subgroup H).map (α.comp H.subtype))
      rw [h4] at hdvd
      have hne4 : orderOf (⟨(α.comp H.subtype) s, s, hs, rfl⟩ :
          (S : Subgroup H).map (α.comp H.subtype)) ≠ 4 := fun h =>
        hcyc (isCyclic_of_orderOf_eq_card _ (h.trans h4.symm))
      have : orderOf (⟨(α.comp H.subtype) s, s, hs, rfl⟩ :
          (S : Subgroup H).map (α.comp H.subtype)) ∈ Nat.divisors 4 :=
        Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · rw [h]; exact one_dvd 2
      · rw [h]
      · exact absurd h hne4
    have hsq : α s ^ 2 = 1 := by
      have := orderOf_dvd_iff_pow_eq_one.1 hord
      have := congrArg Subtype.val this
      simpa using this
    rcases hinv s hsq with h | h
    · rw [MonoidHom.comp_apply, Subgroup.coe_subtype, h]
      exact one_mem _
    · rw [MonoidHom.comp_apply, Subgroup.coe_subtype, h]
      exact mem_zpowers _
  have hzc : Nat.card (zpowers (LinearEquiv.neg (ZMod p) : W ≃ₗ[ZMod p] W)) ≤ 2 := by
    rw [Nat.card_zpowers]
    have : (LinearEquiv.neg (ZMod p) : W ≃ₗ[ZMod p] W) ^ 2 = 1 :=
      LinearEquiv.ext fun w => by simp [sq]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)
  have := Subgroup.card_le_of_le hle
  omega

theorem nq_noncyclic_coprime_projective_irreducibility
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {L : Type*} [Group L] [Finite L] [(CFSG.solvableRadical L).Normal]
    (hL : CFSG.IsCComponent (⊤ : Subgroup L)) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hV : Module.finrank (ZMod p) V = 2) (α : L →* (V ≃ₗ[ZMod p] V)) (hα : α ≠ 1)
    (H : Subgroup L)
    (hB : ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ H.map (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧ ¬ IsCyclic B ∧
        Nat.Coprime (Nat.card B) p)
    (U : Submodule (ZMod p) V) (hU : ∀ h ∈ H, ∀ u ∈ U, α h u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Module.Finite (ZMod p) V := Module.finite_of_finrank_eq_succ hV
  set R := CFSG.solvableRadical L with hRdef
  set b := Module.finBasisOfFinrankEq (ZMod p) V hV
  set Ψ := glEquivMatrix b
  set ρ : L →* GL (Fin 2) (ZMod p) := Ψ.toMonoidHom.comp α with hρ
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply hα
    refine MonoidHom.ext fun l => Ψ.injective ?_
    have := DFunLike.congr_fun h l
    simpa [hρ] using this
  obtain ⟨hR, -, hdet, -, -⟩ := ccomponent_GL2_radical hp2 hL ρ hρ1
  by_contra hUne
  push Not at hUne
  obtain ⟨hU0, hUT⟩ := hUne
  have hU1 : Module.finrank (ZMod p) U = 1 := by
    have h1 := Submodule.finrank_lt hUT
    have h2 : 0 < Module.finrank (ZMod p) U :=
      Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hU0)
    omega
  obtain ⟨u₀, hu₀, hspan⟩ := finrank_eq_one_iff'.1 hU1
  have hu : (u₀ : V) ≠ 0 := fun h => hu₀ (Subtype.ext h)
  have heig : ∀ h ∈ H, ∃ c : ZMod p, α h u₀ = c • (u₀ : V) := by
    intro h hh
    obtain ⟨c, hc⟩ := hspan ⟨α h u₀, hU h hh u₀ u₀.2⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := ZMod p) (s := Set.univ)
    (v := fun _ : Unit => (u₀ : V)) (linearIndepOn_univ_iff.2 (linearIndependent_unique_iff.2 hu))
  have hf1 : f u₀ = 1 := hf () (Set.mem_univ _)
  have hlam : ∀ h ∈ H, α h u₀ = f (α h u₀) • (u₀ : V) := by
    intro h hh
    obtain ⟨c, hc⟩ := heig h hh
    rw [hc, map_smul, hf1, smul_eq_mul, mul_one]
  let lamH : H →* ZMod p :=
    { toFun := fun h => f (α h u₀)
      map_one' := by simp [hf1]
      map_mul' := fun h h' => by
        change f (α ((h : L) * h') u₀) = f (α h u₀) * f (α h' u₀)
        have e := hlam h' h'.2
        calc f (α ((h : L) * h') u₀) = f (α h (α h' u₀)) := by
              rw [map_mul, LinearEquiv.mul_apply]
          _ = f (α h (f (α h' u₀) • (u₀ : V))) := by rw [← e]
          _ = f (α h u₀) * f (α h' u₀) := by rw [map_smul, map_smul, smul_eq_mul, mul_comm] }
  have hlamH : ∀ h : H, α h u₀ = lamH h • (u₀ : V) := fun h => hlam h h.2
  let χ : H →* ZMod p := lamH * lamH
  set π := QuotientGroup.mk' R with hπ
  have hkerχ : (π.subgroupMap H).ker ≤ χ.ker := by
    intro h hh
    have hhR : (h : L) ∈ R := by
      have := congrArg Subtype.val ((MonoidHom.mem_ker).1 hh)
      simpa [hπ] using this
    rw [MonoidHom.mem_ker]
    change lamH h * lamH h = 1
    rcases (hR h).1 hhR with h1 | h1
    · have : α h = 1 := by
        apply Ψ.injective
        simpa [hρ] using h1
      have : lamH h = 1 := by
        change f (α h u₀) = 1
        rw [this]
        exact hf1
      rw [this, mul_one]
    · have : α h = LinearEquiv.neg (ZMod p) := (glEquivMatrix_eq_neg_one_iff b (α h)).1 h1
      have : lamH h = -1 := by
        change f (α h u₀) = -1
        rw [this, LinearEquiv.coe_neg, Pi.neg_apply, map_neg]
        simp only [id_eq]
        rw [hf1]
      rw [this, neg_one_mul, neg_neg]
  set e := QuotientGroup.quotientKerEquivOfSurjective (π.subgroupMap H)
    (π.subgroupMap_surjective H) with he
  set χH : H.map π →* ZMod p :=
    (QuotientGroup.lift _ χ hkerχ).comp e.symm.toMonoidHom with hχH
  have hχH : ∀ h : H, χH (π.subgroupMap H h) = χ h := by
    intro h
    have : e.symm (π.subgroupMap H h) = (h : H ⧸ (π.subgroupMap H).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hχH, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]
  have hexp : ∀ h : H, χ h = 1 → (π.subgroupMap H h) ^ p = 1 := by
    intro h hχ
    have hsq : lamH h * lamH h = 1 := hχ
    have hv : ⇑(b.repr u₀) ≠ 0 := by
      intro h0
      apply hu
      have h' : b.repr (u₀ : V) = 0 := Finsupp.ext fun i => congrFun h0 i
      simpa using h'
    have hmat : ∀ c : ZMod p, α h u₀ = c • (u₀ : V) →
        ((ρ h : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ ⇑(b.repr u₀) =
          c • ⇑(b.repr u₀) := by
      intro c hc
      rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, glEquivMatrix_val,
        LinearMap.toMatrix_mulVec_repr]
      change ⇑(b.repr (α h u₀)) = c • ⇑(b.repr u₀)
      rw [hc, map_smul]
      rfl
    have hpR : ((h : L) ^ p) ∈ R := by
      rcases mul_self_eq_one_iff.1 hsq with h1 | h1
      · have hfix := hmat 1 (by rw [hlamH h, h1])
        rw [one_smul] at hfix
        have := pow_prime_eq_one_of_mulVec_eq_self (hdet h) hv hfix
        refine (hR _).2 (Or.inl ?_)
        rw [map_pow]
        exact this
      · have hfix := hmat (-1) (by rw [hlamH h, h1])
        have hdet' :
            (((-ρ h : GL (Fin 2) (ZMod p))) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
          rw [Units.val_neg, det_neg, hdet h]
          simp
        have hfix' : (((-ρ h : GL (Fin 2) (ZMod p))) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
            ⇑(b.repr u₀) = ⇑(b.repr u₀) := by
          rw [Units.val_neg, neg_mulVec, hfix, neg_one_smul, neg_neg]
        have h2 := pow_prime_eq_one_of_mulVec_eq_self hdet' hv hfix'
        have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
        rw [hodd.neg_pow] at h2
        refine (hR _).2 (Or.inr ?_)
        rw [map_pow]
        rw [neg_eq_iff_eq_neg] at h2
        rw [h2]
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, MonoidHom.subgroupMap_apply_coe, OneMemClass.coe_one]
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hpR
  obtain ⟨B, hBH, hBcyc, hBp⟩ := hB
  apply hBcyc
  set B' := B.subgroupOf (H.map π) with hB'
  set ψ : B' →* ZMod p := χH.comp B'.subtype with hψ
  have hψker : ∀ x : B', ψ x = 1 → x = 1 := by
    intro x hx
    obtain ⟨h, hh⟩ := π.subgroupMap_surjective H (x : H.map π)
    have hx' : χ h = 1 := by rw [← hχH, hh]; exact hx
    have hxp : x ^ p = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← hh]
      exact hexp h hx'
    have hcardB' : Nat.card B' = Nat.card B := Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv
    have hord : orderOf x ∣ Nat.gcd (Nat.card B') p :=
      Nat.dvd_gcd (orderOf_dvd_natCard x) (orderOf_dvd_of_pow_eq_one hxp)
    rw [hcardB', hBp, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hy : ψ y * ψ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h1 : ψ (x * y⁻¹) = 1 := by rw [map_mul, hxy, hy]
    exact mul_inv_eq_one.1 (hψker _ h1)
  have : Finite (H.map π) := Finite.of_surjective _ (π.subgroupMap_surjective H)
  have hB'cyc : IsCyclic B' := isCyclic_of_injective_ringHom ψ hψinj
  exact isCyclic_of_surjective (subgroupOfEquivOfLe hBH).toMonoidHom
    (subgroupOfEquivOfLe hBH).surjective

end CFSG.Quasithin.H13.NQSetup
