module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Ker

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

structure s16e_d3_Cfg (A : Subgroup (MulAut W)) (r m : ℕ) (Δ : Fin (r + 1) → Subgroup W)
    (σ : ↥A →* Equiv.Perm (Fin (r + 1))) : Prop where
  inj : Function.Injective Δ
  rk_eq : ∀ i, rk ↥(Δ i) = m
  indep : iSupIndep Δ
  sup_eq : (⨆ i, Δ i) = ⊤
  map_eq : ∀ (g : ↥A) (i : Fin (r + 1)), (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i)
  surj : Function.Surjective σ

structure s16e_d3_Ctx (A L : Subgroup (MulAut W)) (r : ℕ) (Δ : Fin (r + 1) → Subgroup W)
    (σ : ↥A →* Equiv.Perm (Fin (r + 1))) : Prop where
  cfg : s16e_d3_Cfg A r 3 Δ σ
  sq_eq_one : ∀ w : W, w ^ 2 = 1
  elem : IsElemAbelianOfRank 7 r ↥L
  le : L ≤ A
  normal : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L
  two_le : 2 ≤ r
  le_five : r ≤ 5

@[expose] def s16e_d3_ker (A : Subgroup (MulAut W)) {r : ℕ} (Δ : Fin (r + 1) → Subgroup W) :
    Subgroup (MulAut W) :=
  A ⊓ ⨅ i, stabSub (Δ i)

private noncomputable def s16e_d3_permFun {A : Subgroup (MulAut W)} {ι : Type}
    {Y : ι → Subgroup W}
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥A) (i : ι) : ι :=
  Classical.choose (hperm (g : MulAut W) g.2 i)

private theorem s16e_d3_permFun_spec {A : Subgroup (MulAut W)} {ι : Type}
    {Y : ι → Subgroup W}
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥A) (i : ι) :
    (Y i).map (g : MulAut W).toMonoidHom = Y (s16e_d3_permFun hperm g i) :=
  Classical.choose_spec (hperm (g : MulAut W) g.2 i)

private theorem s16e_d3_permFun_injective {A : Subgroup (MulAut W)} {ι : Type}
    {Y : ι → Subgroup W} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥A) :
    Function.Injective (s16e_d3_permFun hperm g) := by
  intro i j hij
  apply hinj
  have hi := s16e_d3_permFun_spec hperm g i
  have hj := s16e_d3_permFun_spec hperm g j
  rw [hij] at hi
  exact Subgroup.map_injective (g : MulAut W).injective (hi.trans hj.symm)

private noncomputable def s16e_d3_perm {A : Subgroup (MulAut W)} {ι : Type} [Fintype ι]
    {Y : ι → Subgroup W} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥A) : Equiv.Perm ι :=
  Equiv.ofBijective (s16e_d3_permFun hperm g)
    ⟨s16e_d3_permFun_injective hinj hperm g,
      (Finite.injective_iff_surjective).1 (s16e_d3_permFun_injective hinj hperm g)⟩

private theorem s16e_d3_perm_spec {A : Subgroup (MulAut W)} {ι : Type} [Fintype ι]
    {Y : ι → Subgroup W} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥A) (i : ι) :
    (Y i).map (g : MulAut W).toMonoidHom = Y (s16e_d3_perm hinj hperm g i) :=
  s16e_d3_permFun_spec hperm g i

private theorem s16e_d3_perm_mul {A : Subgroup (MulAut W)} {ι : Type} [Fintype ι]
    {Y : ι → Subgroup W} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g h : ↥A) :
    s16e_d3_perm hinj hperm (g * h) =
      s16e_d3_perm hinj hperm g * s16e_d3_perm hinj hperm h := by
  ext i
  apply hinj
  rw [← s16e_d3_perm_spec hinj hperm (g * h) i, Equiv.Perm.mul_apply,
    ← s16e_d3_perm_spec hinj hperm g (s16e_d3_perm hinj hperm h i),
    ← s16e_d3_perm_spec hinj hperm h i]
  rw [Subgroup.map_map]
  rfl

private noncomputable def s16e_d3_rho {A : Subgroup (MulAut W)} {ι : Type} [Fintype ι]
    {Y : ι → Subgroup W} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) : ↥A →* Equiv.Perm ι :=
  MonoidHom.mk' (s16e_d3_perm hinj hperm) (s16e_d3_perm_mul hinj hperm)

private theorem s16e_d3_rho_spec {A : Subgroup (MulAut W)} {ι : Type} [Fintype ι]
    {Y : ι → Subgroup W} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥A) (i : ι) :
    (Y i).map (g : MulAut W).toMonoidHom = Y (s16e_d3_rho hinj hperm g i) :=
  s16e_d3_perm_spec hinj hperm g i

private theorem s16e_d3_rho_surjective {A : Subgroup (MulAut W)} {ι : Type} [Fintype ι]
    {Y : ι → Subgroup W} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    (hsurj : ∀ π : Equiv.Perm ι, ∃ g ∈ A, ∀ i, (Y i).map g.toMonoidHom = Y (π i)) :
    Function.Surjective (s16e_d3_rho hinj hperm) := by
  intro π
  obtain ⟨g, hg, hgπ⟩ := hsurj π
  refine ⟨⟨g, hg⟩, ?_⟩
  ext i
  apply hinj
  exact (s16e_d3_rho_spec hinj hperm ⟨g, hg⟩ i).symm.trans (hgπ i)

private lemma s16e_d3_stab_of_map_eq {U : Subgroup W} {φ : MulAut W}
    (h : U.map φ.toMonoidHom = U) : φ ∈ stabSub U := by
  intro u
  constructor
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := φ.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [h] at hu'
    exact hu'

private lemma s16e_d3_map_eq_of_mem_stab {U : Subgroup W} {φ : MulAut W}
    (h : φ ∈ stabSub U) : U.map φ.toMonoidHom = U := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact (mem_stabSub.mp h u).2 hu
  · intro u hu
    refine Subgroup.mem_map.2 ⟨φ.symm u, ?_, by simp⟩
    exact (mem_stabSub.mp h (φ.symm u)).mp (by simpa using hu)

theorem s16e_d3_cfg_of_symSumOfConj [Finite W] {A : Subgroup (MulAut W)} {r m : ℕ}
    (h : SymSumOfConj A (⊤ : Subgroup W) r m) :
    ∃ (Δ : Fin (r + 1) → Subgroup W) (σ : ↥A →* Equiv.Perm (Fin (r + 1))),
      s16e_d3_Cfg A r m Δ σ := by
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data h
  letI : Fintype ι := hι
  let e : ι ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcard
  let Δ : Fin (r + 1) → Subgroup W := fun i => Y (e.symm i)
  let ρ : ↥A →* Equiv.Perm ι := s16e_d3_rho hinj hperm
  let σ : ↥A →* Equiv.Perm (Fin (r + 1)) :=
    (e.permCongrHom : Equiv.Perm ι ≃* Equiv.Perm (Fin (r + 1))).toMonoidHom.comp ρ
  refine ⟨Δ, σ, hinj.comp e.symm.injective, fun i => hrk (e.symm i),
    hind.comp e.symm.injective, ?_, ?_, ?_⟩
  · show (⨆ i, Y (e.symm i)) = ⊤
    rw [Equiv.iSup_comp]
    exact hsup
  · intro g i
    show (Y (e.symm i)).map (g : MulAut W).toMonoidHom = Y (e.symm (σ g i))
    rw [s16e_d3_rho_spec hinj hperm g (e.symm i)]
    congr 1
    simp [σ, ρ, Equiv.permCongr_apply]
  · intro π
    obtain ⟨g, hg⟩ :=
      s16e_d3_rho_surjective hinj hperm hsurj (e.permCongrHom.symm π)
    refine ⟨g, ?_⟩
    show e.permCongrHom (ρ g) = π
    rw [hg]
    exact e.permCongrHom.apply_symm_apply π

theorem s16e_d3_mem_ker_iff [Finite W] {A : Subgroup (MulAut W)} {r m : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}
    (h : s16e_d3_Cfg A r m Δ σ) {g : MulAut W} :
    g ∈ s16e_d3_ker A Δ ↔ ∃ hg : g ∈ A, σ ⟨g, hg⟩ = 1 := by
  constructor
  · intro hg
    rw [s16e_d3_ker, Subgroup.mem_inf, Subgroup.mem_iInf] at hg
    obtain ⟨hgA, hgstab⟩ := hg
    refine ⟨hgA, Equiv.ext fun i => ?_⟩
    have hmap : (Δ i).map (⟨g, hgA⟩ : ↥A).1.toMonoidHom = Δ i :=
      s16e_d3_map_eq_of_mem_stab (hgstab i)
    have h2 := h.map_eq ⟨g, hgA⟩ i
    rw [hmap] at h2
    exact h.inj h2.symm
  · rintro ⟨hgA, hσ⟩
    rw [s16e_d3_ker, Subgroup.mem_inf, Subgroup.mem_iInf]
    refine ⟨hgA, fun i => ?_⟩
    apply s16e_d3_stab_of_map_eq
    rw [h.map_eq ⟨g, hgA⟩ i, hσ]
    rfl

theorem s16e_d3_card_eq_mul_factorial [Finite W] {A : Subgroup (MulAut W)} {r m : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}
    (h : s16e_d3_Cfg A r m Δ σ) :
    Nat.card ↥A = Nat.card ↥(s16e_d3_ker A Δ) * Nat.factorial (r + 1) := by
  have hle : s16e_d3_ker A Δ ≤ A := inf_le_left
  have hker : (s16e_d3_ker A Δ).subgroupOf A = σ.ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, s16e_d3_mem_ker_iff h]
    constructor
    · rintro ⟨hgA, hσ⟩
      have hg : (⟨(g : MulAut W), hgA⟩ : ↥A) = g := Subtype.ext rfl
      rwa [hg] at hσ
    · intro hσ
      refine ⟨g.2, ?_⟩
      have hg : (⟨(g : MulAut W), g.2⟩ : ↥A) = g := Subtype.ext rfl
      rwa [hg]
  have hcardKer : Nat.card ↥(s16e_d3_ker A Δ) = Nat.card σ.ker := by
    rw [← hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
  have hquot : Nat.card (↥A ⧸ σ.ker) = Nat.factorial (r + 1) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ h.surj).toEquiv,
      Nat.card_perm, Nat.card_fin]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker, hquot, hcardKer]
  exact mul_comm _ _

theorem s16e_d3_eq_one_of_forall_fixes {A : Subgroup (MulAut W)} {r m : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}
    (h : s16e_d3_Cfg A r m Δ σ) {g : MulAut W} (hg : ∀ i, ∀ x ∈ Δ i, g x = x) : g = 1 := by
  apply MulEquiv.ext
  intro x
  show g x = x
  let U : Subgroup W :=
    { carrier := {y | g y = y}
      one_mem' := map_one g
      mul_mem' := fun {a b} ha hb => by
        show g (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show g a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hU : ∀ i, Δ i ≤ U := fun i y hy => hg i y hy
  exact (iSup_le hU) (by rw [h.sup_eq]; exact Subgroup.mem_top x)

theorem s16e_d3_exists_map_eq [Finite W] {A : Subgroup (MulAut W)} {r m : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}
    (h : s16e_d3_Cfg A r m Δ σ) (i j : Fin (r + 1)) :
    ∃ g ∈ A, (Δ i).map g.toMonoidHom = Δ j := by
  obtain ⟨g, hg⟩ := h.surj (Equiv.swap i j)
  refine ⟨(g : MulAut W), g.2, ?_⟩
  rw [h.map_eq g i, hg, Equiv.swap_apply_left]

theorem s16e_d3_card_block [Finite W] {A L : Subgroup (MulAut W)} {r : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}
    (h : s16e_d3_Ctx A L r Δ σ) (i : Fin (r + 1)) : Nat.card ↥(Δ i) = 8 := by
  rw [card_eq_two_pow h.sq_eq_one (Δ i), h.cfg.rk_eq i]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
