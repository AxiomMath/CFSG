module

public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.Background.G2SL3
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

namespace LRed5

section Twist

variable {V : Type} [CommGroup V]

theorem exists_equiv_of_section {U Z : Subgroup V} {Q : Type*} [Group Q] {f : ↥U →* Q}
    (hfs : Function.Surjective f) (hfk : ∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z) {s : MulAut V}
    (hU : ∀ u ∈ U, s u ∈ U) (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z)
    (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) :
    ∃ Θ : Q ≃* Q, ∀ u : ↥U, Θ (f u) = f ⟨s u, hU u u.2⟩ := by
  classical
  let sU : ↥U →* ↥U :=
    { toFun := fun u => ⟨s u, hU u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hsU : ∀ u : ↥U, ((sU u : ↥U) : V) = s u := fun u => rfl
  have hwd : ∀ u u' : ↥U, f u = f u' → f (sU u) = f (sU u') := by
    intro u u' h
    have h1 : f (u'⁻¹ * u) = 1 := by
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel _
    have h2 : ((u'⁻¹ * u : ↥U) : V) ∈ Z := (hfk _).1 h1
    have h3 : s ((u'⁻¹ * u : ↥U) : V) ∈ Z := hZ _ h2
    have h4 : f ((sU u')⁻¹ * sU u) = 1 := by
      rw [hfk]
      have : (((sU u')⁻¹ * sU u : ↥U) : V) = s (((u'⁻¹ * u : ↥U)) : V) := by
        simp [hsU, map_mul, map_inv]
      rw [this]
      exact h3
    rw [map_mul, map_inv] at h4
    exact (inv_mul_eq_one.1 h4).symm
  let Φ₀ : Q → Q := fun m => f (sU (Function.surjInv hfs m))
  have hΦ₀ : ∀ u : ↥U, Φ₀ (f u) = f (sU u) := fun u =>
    hwd _ _ (Function.surjInv_eq hfs (f u))
  let Φ : Q →* Q :=
    { toFun := Φ₀
      map_one' := by
        have := hΦ₀ 1
        rw [map_one] at this
        rw [this]
        have h1 : sU 1 = 1 := map_one sU
        rw [h1, map_one]
      map_mul' := by
        intro m m'
        obtain ⟨u, rfl⟩ := hfs m
        obtain ⟨u', rfl⟩ := hfs m'
        rw [← map_mul, hΦ₀, hΦ₀, hΦ₀, map_mul, map_mul] }
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    obtain ⟨u, rfl⟩ := hfs m
    have h1 : f (sU u) = 1 := by
      have : Φ (f u) = 1 := hm
      exact (hΦ₀ u).symm.trans this
    have h2 : ((sU u : ↥U) : V) ∈ Z := (hfk _).1 h1
    have h3 : (u : V) ∈ Z := by
      have := hZ' _ h2
      simpa [hsU] using this
    exact (hfk u).2 h3
  have hΦsurj : Function.Surjective Φ := by
    intro m'
    obtain ⟨w, rfl⟩ := hfs m'
    refine ⟨f ⟨s⁻¹ (w : V), hU' w w.2⟩, ?_⟩
    have : sU ⟨s⁻¹ (w : V), hU' w w.2⟩ = w := Subtype.ext (by simp [hsU])
    show Φ₀ (f _) = _
    rw [hΦ₀, this]
  exact ⟨MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩, fun u => hΦ₀ u⟩

theorem inner_of_equiv {n : ℕ} {L : Subgroup (MulAut V)} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hπs : Function.Surjective π) {s : MulAut V} (hL : ∀ l ∈ L, s * l * s⁻¹ ∈ L)
    (Φe : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2))
    (hrel : ∀ (γ γ' : ↥(StatedSL n (ZMod 2))),
      ((π γ' : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ →
      ∀ m : Multiplicative (Fin n → ZMod 2),
        Φe (natAct (StatedSL n (ZMod 2)) γ m) = natAct (StatedSL n (ZMod 2)) γ' (Φe m)) :
    ∃ l ∈ L, ∀ x ∈ L, s * x * s⁻¹ = l * x * l⁻¹ := by
  classical
  obtain ⟨g, hg⟩ := FLc.exists_mat_of_mulEquiv (n := n) Φe
  let g' : ↥(StatedSL n (ZMod 2)) := specialLinearGroupEquivStatedSL n (ZMod 2) g
  have hg' : ((g' : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = FLc.mat g :=
    specialLinearGroupEquivStatedSL_coe n (ZMod 2) g
  have hconj : ∀ γ : ↥(StatedSL n (ZMod 2)),
      s * ((π γ : ↥L) : MulAut V) * s⁻¹ = ((π (g' * γ * g'⁻¹) : ↥L) : MulAut V) := by
    intro γ
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(StatedSL n (ZMod 2)),
        π γ' = ⟨s * ((π γ : ↥L) : MulAut V) * s⁻¹, hL _ (π γ).2⟩ := hπs _
    have hγ'' : ((π γ' : ↥L) : MulAut V) = s * ((π γ : ↥L) : MulAut V) * s⁻¹ :=
      congrArg Subtype.val hγ'
    have hmat : FLc.mat g * ((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((γ' : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) * FLc.mat g := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 := congrArg (fun m => Multiplicative.toAdd m)
        (hrel γ γ' hγ'' (Multiplicative.ofAdd (Pi.single j 1)))
      have h2 := hg (((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single j 1)
      have h3 := hg (Pi.single j 1)
      simp only [natAct, toAdd_ofAdd] at h1
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [← h2, h1, h3]
    have hγeq : γ' = g' * γ * g'⁻¹ := by
      refine eq_mul_inv_of_mul_eq ?_
      apply Subtype.ext
      apply Units.ext
      show ((γ' : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          ((g' : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((g' : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          ((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
      rw [hg']
      exact hmat.symm
    rw [← hγeq]
    exact hγ''.symm
  refine ⟨((π g' : ↥L) : MulAut V), (π g').2, fun y hy => ?_⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL n (ZMod 2)), π γ = ⟨y, hy⟩ := hπs _
  have hyγ : y = ((π γ : ↥L) : MulAut V) := (congrArg Subtype.val hγ).symm
  rw [hyγ, hconj γ]
  simp [map_mul, map_inv]

theorem inner_of_natural_section {n : ℕ} {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hπ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia L U Z π) {s : MulAut V}
    (hU : ∀ u ∈ U, s u ∈ U) (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z)
    (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) (hL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) :
    ∃ l ∈ L, ∀ x ∈ L, s * x * s⁻¹ = l * x * l⁻¹ := by
  classical
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  obtain ⟨Φe, hΦe⟩ := exists_equiv_of_section hfs hfk hU hU' hZ hZ'
  refine inner_of_equiv hπ.1 hL Φe fun γ γ' hγ m => ?_
  obtain ⟨u, rfl⟩ := hfs m
  have hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hπ.2.2.2.1 (π γ) u u.2
  have hsu : ((π γ' : ↥L) : MulAut V) (s (u : V)) ∈ U :=
    hπ.2.2.2.1 (π γ') (s (u : V)) (hU u u.2)
  rw [← hfe γ u hu, hΦe, hΦe, ← hfe γ' ⟨s u, hU u u.2⟩ hsu]
  congr 1
  apply Subtype.ext
  show s (((π γ : ↥L) : MulAut V) (u : V)) = ((π γ' : ↥L) : MulAut V) (s (u : V))
  rw [hγ]
  simp [MulAut.mul_apply]

end Twist

section Sum

variable {V : Type} [CommGroup V]

abbrev M3 : Type := Multiplicative (Fin 3 → ZMod 2)

theorem natAct_irreducible_three (X : Subgroup M3)
    (hX : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (x : M3), x ∈ X → natAct (StatedSL 3 (ZMod 2)) γ x ∈ X) :
    X = ⊥ ∨ X = ⊤ := by
  refine SL3Model.natAct3_irreducible X fun A x hx => ?_
  have := hX (specialLinearGroupEquivStatedSL 3 (ZMod 2) A) x hx
  have h : SL3Model.natAct3 A x = natAct (StatedSL 3 (ZMod 2))
      (specialLinearGroupEquivStatedSL 3 (ZMod 2) A) x := by
    apply Multiplicative.toAdd.injective
    simp only [SL3Model.natAct3_apply, natAct, toAdd_ofAdd]
    rw [specialLinearGroupEquivStatedSL_coe]
    rfl
  rwa [h]


theorem inner_of_two_natural {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : DirectSumOfCopies L U Z (FFModel.nat (StatedSL 3 (ZMod 2))) 2) {s : MulAut V}
    (hU : ∀ u ∈ U, s u ∈ U) (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z)
    (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) (hL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) :
    ∃ l ∈ L, ∀ x ∈ L, s * x * s⁻¹ = l * x * l⁻¹ := by
  classical
  obtain ⟨I, π, hZI, hind, hsup, hreal⟩ := h
  have hIU : ∀ i, I i ≤ U := fun i => hsup ▸ (le_iSup I i).trans le_sup_right
  have hZU : Z ≤ U := hsup ▸ le_sup_left
  have hfin : ∀ i, ∃ f : ↥(I i) →* M3, Function.Surjective f ∧ (∀ u : ↥(I i), f u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥(I i)) (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ I i),
        f ⟨_, hu⟩ = natAct (StatedSL 3 (ZMod 2)) γ (f u) := fun i => FFC.exists_natMap (hreal i)
  choose f hfs hfk hfe using hfin
  have hsup2 : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 :=
    le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
      (sup_le (le_iSup I 0) (le_iSup I 1))
  have hrest0 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
    have : j = 1 := by revert j; decide
    rw [this]
  have hrest1 : (⨆ (j : Fin 2) (_ : j ≠ 1), I j) = I 0 := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le (0 : Fin 2) (by decide) le_rfl)
    have : j = 0 := by revert j; decide
    rw [this]
  have hsplit : ∀ a b : V, a ∈ I 0 → b ∈ I 1 → a * b ∈ Z → a ∈ Z ∧ b ∈ Z := by
    intro a b ha hb hab
    constructor
    · have h1 : a ∈ I 0 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) := by
        refine ⟨ha, ?_⟩
        rw [hrest0, ← mul_inv_cancel_right a b]
        exact (Z ⊔ I 1).mul_mem (Subgroup.mem_sup_left hab) ((Z ⊔ I 1).inv_mem (Subgroup.mem_sup_right hb))
      rwa [hind 0] at h1
    · have h1 : b ∈ I 1 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 1), I j) := by
        refine ⟨hb, ?_⟩
        rw [hrest1, ← inv_mul_cancel_left a b]
        exact (Z ⊔ I 0).mul_mem ((Z ⊔ I 0).inv_mem (Subgroup.mem_sup_right ha)) (Subgroup.mem_sup_left hab)
      rwa [hind 1] at h1
  let mP : (↥(I 0) × ↥(I 1) × ↥Z) →* ↥U :=
    { toFun := fun p => ⟨(p.1 : V) * (p.2.1 : V) * (p.2.2 : V),
        mul_mem (mul_mem (hIU 0 p.1.2) (hIU 1 p.2.1.2)) (hZU p.2.2.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        ac_rfl) }
  have hmP : ∀ p, ((mP p : ↥U) : V) = (p.1 : V) * (p.2.1 : V) * (p.2.2 : V) := fun p => rfl
  have hmPs : Function.Surjective mP := by
    rintro ⟨u, hu⟩
    rw [← hsup, hsup2] at hu
    obtain ⟨z, hz, w, hw, rfl⟩ := Subgroup.mem_sup.1 hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨z, hz⟩), Subtype.ext (by rw [hmP]; ac_rfl)⟩
  let F₀ : (↥(I 0) × ↥(I 1) × ↥Z) →* M3 × M3 :=
    ((f 0).comp (MonoidHom.fst _ _)).prod ((f 1).comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)))
  have hF₀ : ∀ p, F₀ p = (f 0 p.1, f 1 p.2.1) := fun p => rfl
  have hker : mP.ker ≤ F₀.ker := by
    intro p hp
    have hp1 : (p.1 : V) * (p.2.1 : V) * (p.2.2 : V) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hp)
    have hab : (p.1 : V) * (p.2.1 : V) ∈ Z := by
      rw [eq_inv_of_mul_eq_one_left hp1]
      exact Z.inv_mem p.2.2.2
    obtain ⟨ha, hb⟩ := hsplit _ _ p.1.2 p.2.1.2 hab
    rw [MonoidHom.mem_ker, hF₀]
    exact Prod.ext ((hfk 0 p.1).2 ha) ((hfk 1 p.2.1).2 hb)
  let F : ↥U →* M3 × M3 := mP.liftOfSurjective hmPs ⟨F₀, hker⟩
  have hF : ∀ p, F (mP p) = F₀ p := fun p =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨F₀, hker⟩ p
  have hFs : Function.Surjective F := by
    rintro ⟨m₀, m₁⟩
    obtain ⟨a, rfl⟩ := hfs 0 m₀
    obtain ⟨b, rfl⟩ := hfs 1 m₁
    exact ⟨mP (a, b, 1), by rw [hF, hF₀]⟩
  have hFk : ∀ u : ↥U, F u = 1 ↔ (u : V) ∈ Z := by
    intro u
    obtain ⟨p, rfl⟩ := hmPs u
    rw [hF, hF₀, hmP]
    constructor
    · intro h1
      have h2 : f 0 p.1 = 1 := congrArg Prod.fst h1
      have h3 : f 1 p.2.1 = 1 := congrArg Prod.snd h1
      exact mul_mem (mul_mem ((hfk 0 p.1).1 h2) ((hfk 1 p.2.1).1 h3)) p.2.2.2
    · intro h1
      have hab : (p.1 : V) * (p.2.1 : V) ∈ Z := by
        have := mul_mem h1 (Z.inv_mem p.2.2.2)
        rwa [mul_inv_cancel_right] at this
      obtain ⟨ha, hb⟩ := hsplit _ _ p.1.2 p.2.1.2 hab
      exact Prod.ext ((hfk 0 p.1).2 ha) ((hfk 1 p.2.1).2 hb)
  have hFe : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥U),
      ∃ hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U,
        F ⟨_, hu⟩ = (natAct (StatedSL 3 (ZMod 2)) γ (F u).1, natAct (StatedSL 3 (ZMod 2)) γ (F u).2) := by
    intro γ u
    obtain ⟨p, rfl⟩ := hmPs u
    have hpa : ((π γ : ↥L) : MulAut V) (p.1 : V) ∈ I 0 := (hreal 0).2.2.2.1 (π γ) _ p.1.2
    have hpb : ((π γ : ↥L) : MulAut V) (p.2.1 : V) ∈ I 1 := (hreal 1).2.2.2.1 (π γ) _ p.2.1.2
    have hpz : ((π γ : ↥L) : MulAut V) (p.2.2 : V) ∈ Z := (hreal 0).2.2.2.2.1 (π γ) _ p.2.2.2
    have hq : ((π γ : ↥L) : MulAut V) ((mP p : ↥U) : V) =
        (((π γ : ↥L) : MulAut V) (p.1 : V)) * (((π γ : ↥L) : MulAut V) (p.2.1 : V)) *
          (((π γ : ↥L) : MulAut V) (p.2.2 : V)) := by
      rw [hmP, map_mul, map_mul]
    have hu : ((π γ : ↥L) : MulAut V) ((mP p : ↥U) : V) ∈ U := by
      rw [hq]
      exact mul_mem (mul_mem (hIU 0 hpa) (hIU 1 hpb)) (hZU hpz)
    refine ⟨hu, ?_⟩
    have : (⟨_, hu⟩ : ↥U) = mP (⟨_, hpa⟩, ⟨_, hpb⟩, ⟨_, hpz⟩) :=
      Subtype.ext (by show ((π γ : ↥L) : MulAut V) ((mP p : ↥U) : V) = _; rw [hq, hmP])
    rw [this, hF, hF, hF₀, hF₀]
    simp only
    rw [hfe 0 γ p.1 hpa, hfe 1 γ p.2.1 hpb]
  have hinvU : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : V), u ∈ U → ((π γ : ↥L) : MulAut V) u ∈ U :=
    fun γ u hu => (hFe γ ⟨u, hu⟩).1
  obtain ⟨Θ, hΘ⟩ := exists_equiv_of_section hFs hFk hU hU' hZ hZ'
  have hπs : Function.Surjective π := (hreal 0).1
  have hΘrel : ∀ (γ γ' : ↥(StatedSL 3 (ZMod 2))),
      ((π γ' : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ → ∀ q : M3 × M3,
        Θ (natAct (StatedSL 3 (ZMod 2)) γ q.1, natAct (StatedSL 3 (ZMod 2)) γ q.2) =
          (natAct (StatedSL 3 (ZMod 2)) γ' (Θ q).1, natAct (StatedSL 3 (ZMod 2)) γ' (Θ q).2) := by
    intro γ γ' hγ q
    obtain ⟨u, rfl⟩ := hFs q
    obtain ⟨hu, hFu⟩ := hFe γ u
    have hsu : ((π γ' : ↥L) : MulAut V) (s (u : V)) ∈ U := hinvU γ' _ (hU u u.2)
    obtain ⟨hu', hFu'⟩ := hFe γ' ⟨s u, hU u u.2⟩
    have e1 : Θ (natAct (StatedSL 3 (ZMod 2)) γ (F u).1, natAct (StatedSL 3 (ZMod 2)) γ (F u).2) =
        F ⟨s (((π γ : ↥L) : MulAut V) (u : V)), hU _ hu⟩ := by
      rw [← hFu]
      exact hΘ ⟨_, hu⟩
    have e2 : (⟨s (((π γ : ↥L) : MulAut V) (u : V)), hU _ hu⟩ : ↥U) =
        ⟨((π γ' : ↥L) : MulAut V) (s (u : V)), hu'⟩ := by
      apply Subtype.ext
      show s (((π γ : ↥L) : MulAut V) (u : V)) = ((π γ' : ↥L) : MulAut V) (s (u : V))
      rw [hγ]
      simp [MulAut.mul_apply]
    have e3 : F ⟨s (u : V), hU u u.2⟩ = Θ (F u) := (hΘ u).symm
    rw [e1, e2, hFu', e3]
  have key : ∀ Ψ : M3 →* M3,
      (∀ (γ γ' : ↥(StatedSL 3 (ZMod 2))), ((π γ' : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ →
        ∀ m : M3, Ψ (natAct (StatedSL 3 (ZMod 2)) γ m) = natAct (StatedSL 3 (ZMod 2)) γ' (Ψ m)) →
      (∃ x, Ψ x ≠ 1) → ∃ l ∈ L, ∀ x ∈ L, s * x * s⁻¹ = l * x * l⁻¹ := by
    intro Ψ hΨ ⟨x₀, hx₀⟩
    have hex : ∀ γ : ↥(StatedSL 3 (ZMod 2)), ∃ γ' : ↥(StatedSL 3 (ZMod 2)),
        ((π γ' : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ := by
      intro γ
      obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(StatedSL 3 (ZMod 2)),
          π γ' = ⟨s * ((π γ : ↥L) : MulAut V) * s⁻¹, hL _ (π γ).2⟩ := hπs _
      exact ⟨γ', congrArg Subtype.val hγ'⟩
    have hker : Ψ.ker = ⊥ := by
      rcases natAct_irreducible_three Ψ.ker (fun γ x hx => by
          obtain ⟨γ', hγ'⟩ := hex γ
          rw [MonoidHom.mem_ker] at hx ⊢
          rw [hΨ γ γ' hγ', hx]
          simp [natAct]) with h | h
      · exact h
      · exact absurd (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x₀)) hx₀
    have hinj : Function.Injective Ψ := (MonoidHom.ker_eq_bot_iff Ψ).1 hker
    have hsurj : Function.Surjective Ψ := Finite.surjective_of_injective hinj
    exact inner_of_equiv hπs hL (MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩) fun γ γ' hγ m => hΨ γ γ' hγ m
  let Ψ₁ : M3 →* M3 := (MonoidHom.fst M3 M3).comp (Θ.toMonoidHom.comp (MonoidHom.inl M3 M3))
  let Ψ₂ : M3 →* M3 := (MonoidHom.snd M3 M3).comp (Θ.toMonoidHom.comp (MonoidHom.inl M3 M3))
  have hΨ₁ : ∀ (γ γ' : ↥(StatedSL 3 (ZMod 2))), ((π γ' : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ →
      ∀ m : M3, Ψ₁ (natAct (StatedSL 3 (ZMod 2)) γ m) = natAct (StatedSL 3 (ZMod 2)) γ' (Ψ₁ m) := by
    intro γ γ' hγ m
    have := hΘrel γ γ' hγ (m, 1)
    simp only [FFC.natAct_one_right] at this
    exact congrArg Prod.fst this
  have hΨ₂ : ∀ (γ γ' : ↥(StatedSL 3 (ZMod 2))), ((π γ' : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ →
      ∀ m : M3, Ψ₂ (natAct (StatedSL 3 (ZMod 2)) γ m) = natAct (StatedSL 3 (ZMod 2)) γ' (Ψ₂ m) := by
    intro γ γ' hγ m
    have := hΘrel γ γ' hγ (m, 1)
    simp only [FFC.natAct_one_right] at this
    exact congrArg Prod.snd this
  let x₀ : M3 := Multiplicative.ofAdd (Pi.single 0 1)
  have hx₀ : x₀ ≠ 1 := by
    intro h
    have := congrFun (congrArg Multiplicative.toAdd h) 0
    simp [x₀] at this
  have hne : Θ (x₀, 1) ≠ 1 := by
    intro h
    have h1 : (x₀, (1 : M3)) = 1 := Θ.injective (h.trans (map_one Θ).symm)
    exact hx₀ (congrArg Prod.fst h1)
  by_cases h1 : Ψ₁ x₀ = 1
  · refine key Ψ₂ hΨ₂ ⟨x₀, fun h2 => hne ?_⟩
    exact Prod.ext h1 h2
  · exact key Ψ₁ hΨ₁ ⟨x₀, h1⟩

end Sum

end LRed5

end CFSG.Quasithin
