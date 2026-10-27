module

public import CFSG.Quasithin.EmptyFaithful.A38c16Mod
public import CFSG.Quasithin.EmptyFaithful.A38c16BlocksClass
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.Quasithin.A38c16.Blocks

open scoped MatrixGroups

section Assembly

variable {W : Type} [CommGroup W] {Γ K Kp : Subgroup (MulAut W)}

@[expose] def piOf (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) : AddSubgroup (ZMod 2 × ZMod 2) where
  carrier := Set.range (classMap hΓ θ θp)
  zero_mem' := ⟨1, classMap_one hAut hΓ θ θp⟩
  add_mem' := by
    rintro _ _ ⟨γ, rfl⟩ ⟨γ', rfl⟩
    exact ⟨γ * γ', classMap_mul hAut hΓ θ θp γ γ'⟩
  neg_mem' := by
    rintro _ ⟨γ, rfl⟩
    exact ⟨γ, (neg_eq_of_add_eq_zero_right (classMap_add_self _)).symm⟩

theorem classMap_ne_zero_of_outer (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp)
    (θ : ↥K ≃* SL(3, ZMod 2)) (θp : ↥Kp ≃* SL(3, ZMod 2)) {s : MulAut W} (hs : s ∈ Γ)
    (hso : IsOuterOn K s) : classMap hΓ θ θp ⟨s, hs⟩ ≠ 0 := by
  intro h
  have h1 : outerClass (liftAut θ (conjK hΓ ⟨s, hs⟩)) = 0 := by
    have := congrArg Prod.fst h
    simpa [classMap] using this
  obtain ⟨k₀, hk₀⟩ := exists_inner_of_outerClass_zero hAut θ _ h1
  apply hso
  exact ⟨k₀, k₀.2, fun x hx => congrArg Subtype.val (hk₀ ⟨x, hx⟩)⟩

theorem piOf_ne_bot (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {s : MulAut W} (hs : s ∈ Γ) (hso : IsOuterOn K s) :
    piOf hAut hΓ θ θp ≠ ⊥ := by
  intro h
  have : classMap hΓ θ θp ⟨s, hs⟩ ∈ piOf hAut hΓ θ θp := ⟨_, rfl⟩
  rw [h, AddSubgroup.mem_bot] at this
  exact classMap_ne_zero_of_outer hAut hΓ θ θp hs hso this

@[expose] noncomputable def clsA (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) (a : ↥A) :
    ZMod 2 × ZMod 2 :=
  classMap hΓ θ θp ⟨a, hAΓ a.2⟩

theorem clsA_mul (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) (a b : ↥A) :
    clsA hΓ θ θp hAΓ (a * b) = clsA hΓ θ θp hAΓ a + clsA hΓ θ θp hAΓ b :=
  classMap_mul hAut hΓ θ θp ⟨a, hAΓ a.2⟩ ⟨b, hAΓ b.2⟩

theorem clsA_mem (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) (a : ↥A) :
    clsA hΓ θ θp hAΓ a ∈ piOf hAut hΓ θ θp := ⟨_, rfl⟩

@[expose] noncomputable def homA (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) :
    ↥A →* Multiplicative (ZMod 2 × ZMod 2) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (clsA hΓ θ θp hAΓ a))
    (fun a b => by rw [clsA_mul hAut hΓ θ θp hAΓ, ofAdd_add])

@[expose] noncomputable def qOf (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) :
    AddSubgroup (ZMod 2 × ZMod 2) where
  carrier := Set.range (clsA hΓ θ θp hAΓ)
  zero_mem' := ⟨1, by
    have h := clsA_mul hAut hΓ θ θp hAΓ 1 1
    rw [mul_one] at h
    simpa using h.symm⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, clsA_mul hAut hΓ θ θp hAΓ a b⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (neg_eq_of_add_eq_zero_right (classMap_add_self _)).symm⟩

theorem qOf_le_piOf (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) :
    qOf hAut hΓ θ θp hAΓ ≤ piOf hAut hΓ θ θp := by
  rintro _ ⟨a, rfl⟩
  exact clsA_mem hAut hΓ θ θp hAΓ a

@[expose] noncomputable def a0Of (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) :
    Subgroup (MulAut W) :=
  (homA hAut hΓ θ θp hAΓ).ker.map A.subtype

theorem card_A_eq (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) :
    Nat.card ↥A = Nat.card ↥(a0Of hAut hΓ θ θp hAΓ) * Nat.card ↥(qOf hAut hΓ θ θp hAΓ) := by
  have h1 := Subgroup.card_mul_index (homA hAut hΓ θ θp hAΓ).ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card ↥(a0Of hAut hΓ θ θp hAΓ) = Nat.card ↥(homA hAut hΓ θ θp hAΓ).ker :=
    Subgroup.card_map_of_injective A.subtype_injective
  have h3 : Nat.card ↥(qOf hAut hΓ θ θp hAΓ) = Nat.card ↥(homA hAut hΓ θ θp hAΓ).range := by
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd ?_)
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, Multiplicative.ofAdd.injective ha⟩
  rw [h2, h3, h1]

@[expose] def psi (hΓ : Case3Setting Γ K Kp) : ↥K × ↥Kp →* MulAut W :=
  (K.subtype).noncommCoprod (Kp.subtype) (fun k y => hΓ.comm k k.2 y y.2)

theorem psi_injective (hΓ : Case3Setting Γ K Kp) : Function.Injective (psi hΓ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have h1 : (g.1 : MulAut W) * (g.2 : MulAut W) = 1 := hg
  have h2 : (g.1 : MulAut W) = ((g.2 : MulAut W))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hmemKp : (g.1 : MulAut W) ∈ Kp := h2 ▸ Kp.inv_mem g.2.2
  have h3 : (g.1 : MulAut W) = 1 :=
    hΓ.cent _ (hΓ.K_le g.1.2) (fun k hk => (hΓ.comm k hk _ hmemKp).symm)
      (fun y hy => hΓ.comm _ g.1.2 y hy)
  have h4 : (g.2 : MulAut W) = 1 := by rw [h3, one_mul] at h1; exact h1
  rw [Subgroup.mem_bot]
  exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)

theorem exists_psi_of_mem_a0 (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp)
    (θ : ↥K ≃* SL(3, ZMod 2)) (θp : ↥Kp ≃* SL(3, ZMod 2)) {A : Subgroup (MulAut W)}
    (hAΓ : A ≤ Γ) {a : MulAut W} (ha : a ∈ a0Of hAut hΓ θ θp hAΓ) :
    ∃ g : ↥K × ↥Kp, psi hΓ g = a ∧ a ∈ A := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  have hx0 : clsA hΓ θ θp hAΓ x = 0 := by
    have h1 : Multiplicative.ofAdd (clsA hΓ θ θp hAΓ x) = 1 := hx
    exact ofAdd_eq_one.mp h1
  obtain ⟨k, y, hky⟩ := exists_mul_of_classMap_eq_zero hAut hΓ θ θp (γ := ⟨x, hAΓ x.2⟩) hx0
  exact ⟨(k, y), hky.symm, x.2⟩

theorem card_M3 : Nat.card M3 = 512 := by
  rw [Nat.card_eq_fintype_card]
  show Fintype.card (Fin 3 → Fin 3 → ZMod 2) = 512
  simp

theorem fixSetT_bot (t : ZMod 2 × ZMod 2) : fixSetT t ⊥ = Set.univ := by
  refine Set.eq_univ_of_forall fun X => ?_
  show ∀ g ∈ (⊥ : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2))), tensorActT t g X = X
  intro g hg
  rw [Subgroup.mem_bot.mp hg]
  exact tensorActT_one t X

theorem blkFixCard_bot (M : Subgroup W) : blkFixCard K Kp M ⊥ = Nat.card ↥M := by
  unfold blkFixCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩)
  intro g hg
  rw [Subgroup.mem_bot.mp hg]
  simp

theorem card_blk (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {S : Subgroup W} {t : ZMod 2 × ZMod 2}
    (hcount : ∀ F : Subgroup (↥K × ↥Kp), blkFixCard K Kp S F =
      Nat.card (fixSetT t (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)))
    (γ : ↥Γ) : Nat.card ↥(blk S (γ : MulAut W)) = 512 := by
  have h := blk_count hAut hΓ θ θp hcount γ ⊥
  rw [blkFixCard_bot, Subgroup.map_bot, fixSetT_bot, Nat.card_univ, card_M3] at h
  exact h

theorem blkFam_indep (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {S : Subgroup W} (hS1 : S ≠ ⊥) (hSK : IsKSub K S)
    (hSKp : IsKSub Kp S)
    (hSmin : ∀ N : Subgroup W, N ≤ S → IsKSub K N → IsKSub Kp N → N = ⊥ ∨ N = S)
    {t : ZMod 2 × ZMod 2}
    (hcount : ∀ F : Subgroup (↥K × ↥Kp), blkFixCard K Kp S F =
      Nat.card (fixSetT t (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)))
    (σ : ↥(piOf hAut hΓ θ θp) → ↥Γ) (hσ : ∀ π, classMap hΓ θ θp (σ π) = π) :
    iSupIndep (fun π : ↥(piOf hAut hΓ θ θp) => blk S (σ π : MulAut W)) := by
  refine iSupIndep_of_sep (K := K) (Kp := Kp) _ (fun π => blk_ne_bot _ hS1)
    (fun π => (inv2_blk (norm2_of_mem hΓ (σ π)) ⟨hSK, hSKp⟩).1)
    (fun π => (inv2_blk (norm2_of_mem hΓ (σ π)) ⟨hSK, hSKp⟩).2)
    (fun π => blk_min (norm2_of_mem hΓ (σ π)) hSmin) ?_
  intro π π' hne
  have hne' : t + (π : ZMod 2 × ZMod 2) ≠ t + (π' : ZMod 2 × ZMod 2) := fun h =>
    hne (Subtype.ext (add_left_cancel h))
  obtain ⟨E, hE⟩ := hAut.distinguish _ _ hne'
  refine ⟨E.comap (MulEquiv.prodCongr θ θp).toMonoidHom, ?_⟩
  have hmap : (E.comap (MulEquiv.prodCongr θ θp).toMonoidHom).map
      (MulEquiv.prodCongr θ θp).toMonoidHom = E :=
    Subgroup.map_comap_eq_self_of_surjective (MulEquiv.prodCongr θ θp).surjective _
  show blkFixCard K Kp (blk S (σ π : MulAut W)) _ ≠ blkFixCard K Kp (blk S (σ π' : MulAut W)) _
  rw [blk_count hAut hΓ θ θp hcount (σ π), blk_count hAut hΓ θ θp hcount (σ π'), hmap, hσ, hσ]
  exact hE

theorem a0Of_le {hAut : SL3OutFacts} {hΓ : Case3Setting Γ K Kp} {θ : ↥K ≃* SL(3, ZMod 2)}
    {θp : ↥Kp ≃* SL(3, ZMod 2)} {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) :
    a0Of hAut hΓ θ θp hAΓ ≤ A := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

end Assembly

theorem _root_.CFSG.Quasithin.A38c16.no_offender_of_counting {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    (hAut : SL3OutFacts) (hcheck : Case3Check)
    {Γ K Kp : Subgroup (MulAut W)} (hΓ : Case3Setting Γ K Kp)
    (θ : ↥K ≃* SL(3, ZMod 2)) (θp : ↥Kp ≃* SL(3, ZMod 2))
    {s : MulAut W} (hs : s ∈ Γ) (hso : IsOuterOn K s)
    {S : Subgroup W} (hS1 : S ≠ ⊥) (hSK : IsKSub K S) (hSKp : IsKSub Kp S)
    (hSmin : ∀ N : Subgroup W, N ≤ S → IsKSub K N → IsKSub Kp N → N = ⊥ ∨ N = S)
    {t : ZMod 2 × ZMod 2}
    (hcount : ∀ F : Subgroup (↥K × ↥Kp),
      Nat.card {w : W // w ∈ S ∧ ∀ g ∈ F, ((g.1 : MulAut W) * (g.2 : MulAut W)) w = w} =
        Nat.card (fixSetT t (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)))
    {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    Nat.card A ^ 2 * Nat.card (fixV A) < Nat.card W := by
  classical
  have _hW := hW
  have hcount' : ∀ F : Subgroup (↥K × ↥Kp), blkFixCard K Kp S F =
      Nat.card (fixSetT t (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)) := hcount
  have hPi0 : piOf hAut hΓ θ θp ≠ ⊥ := piOf_ne_bot hAut hΓ θ θp hs hso
  have hQPi : qOf hAut hΓ θ θp hAΓ ≤ piOf hAut hΓ θ θp := qOf_le_piOf hAut hΓ θ θp hAΓ
  have hex : ∀ π : ↥(piOf hAut hΓ θ θp), ∃ γ : ↥Γ, classMap hΓ θ θp γ = π := fun π => π.2
  choose σ hσ using hex
  have hind := blkFam_indep hAut hΓ θ θp hS1 hSK hSKp hSmin hcount' σ hσ
  have : Fintype ↥(piOf hAut hΓ θ θp) := Fintype.ofFinite _
  let B : ↥(piOf hAut hΓ θ θp) → Subgroup W := fun π => blk S (σ π : MulAut W)
  have hX : Nat.card ↥(⨆ i, B i) = 512 ^ Nat.card ↥(piOf hAut hΓ θ θp) := by
    rw [card_iSup_of_iSupIndep B hind]
    have : ∀ i, Nat.card ↥(B i) = 512 := fun i => card_blk hAut hΓ θ θp hcount' (σ i)
    simp only [this, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  obtain ⟨R, hRPi, hRuniq⟩ := exists_transversal (piOf hAut hΓ θ θp) (qOf hAut hΓ θ θp hAΓ)
  let R' : Finset ↥(piOf hAut hΓ θ θp) := R.subtype (· ∈ piOf hAut hΓ θ θp)
  let d : ↥A → ↥(piOf hAut hΓ θ θp) := fun a =>
    ⟨clsA hΓ θ θp hAΓ a, clsA_mem hAut hΓ θ θp hAΓ a⟩
  let F : Subgroup (↥K × ↥Kp) := (a0Of hAut hΓ θ θp hAΓ).comap (psi hΓ)
  let E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)) := F.map (MulEquiv.prodCongr θ θp).toMonoidHom
  have hB : ∀ (a : ↥A) (i : ↥(piOf hAut hΓ θ θp)), ∀ v ∈ B i, (a : MulAut W) v ∈ B (i + d a) := by
    intro a i v hv
    have hv' : (σ i : MulAut W)⁻¹ v ∈ S := hv
    have hcls : classMap hΓ θ θp (σ (i + d a)) = classMap hΓ θ θp (⟨a, hAΓ a.2⟩ * σ i) := by
      rw [hσ, classMap_mul hAut hΓ θ θp, hσ]
      show (i : ZMod 2 × ZMod 2) + clsA hΓ θ θp hAΓ a = clsA hΓ θ θp hAΓ a + i
      exact add_comm _ _
    have heq := blk_eq_of_classMap_eq hAut hΓ θ θp hSK hSKp hcls
    show (a : MulAut W) v ∈ blk S (σ (i + d a) : MulAut W)
    rw [heq]
    show ((⟨a, hAΓ a.2⟩ * σ i : ↥Γ) : MulAut W)⁻¹ ((a : MulAut W) v) ∈ S
    have : ((⟨a, hAΓ a.2⟩ * σ i : ↥Γ) : MulAut W)⁻¹ ((a : MulAut W) v) =
        (σ i : MulAut W)⁻¹ v := by
      simp [mul_inv_rev, MulAut.mul_apply]
    rw [this]
    exact hv'
  have hA₀' : ∀ a ∈ a0Of hAut hΓ θ θp hAΓ, ∃ h : a ∈ A, d ⟨a, h⟩ = 0 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨x.2, ?_⟩
    apply Subtype.ext
    have h1 : Multiplicative.ofAdd (clsA hΓ θ θp hAΓ x) = 1 := hx
    exact ofAdd_eq_one.mp h1
  have hR : ∀ p : ↥(piOf hAut hΓ θ θp), ∃ r ∈ R', ∃ a : ↥A, p = r + d a := by
    intro p
    obtain ⟨r, ⟨hrR, hq⟩, -⟩ := hRuniq p p.2
    obtain ⟨a, ha⟩ := hq
    refine ⟨⟨r, hRPi r hrR⟩, Finset.mem_subtype.mpr hrR, a, ?_⟩
    apply Subtype.ext
    show (p : ZMod 2 × ZMod 2) = r + clsA hΓ θ θp hAΓ a
    rw [ha]
    abel
  have horb := orbit_card_le B hind A (a0Of hAut hΓ θ θp hAΓ) d hB hA₀' R' hR
  have hterm : ∀ r : ↥(piOf hAut hΓ θ θp),
      Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ a0Of hAut hΓ θ θp hAΓ, h w = w} =
        Nat.card (fixSetT (t + (r : ZMod 2 × ZMod 2)) E) := by
    intro r
    have h1 : Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ a0Of hAut hΓ θ θp hAΓ, h w = w} =
        blkFixCard K Kp (B r) F := by
      unfold blkFixCard
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => and_congr_right fun _ =>
        ⟨fun hfix g hg => hfix (psi hΓ g) hg, fun hfix h hh => ?_⟩)
      obtain ⟨g, hg, -⟩ := exists_psi_of_mem_a0 hAut hΓ θ θp hAΓ hh
      rw [← hg]
      exact hfix g (by rw [Subgroup.mem_comap, hg]; exact hh)
    rw [h1, blk_count hAut hΓ θ θp hcount' (σ r) F, hσ]
  have hprod : ∏ r ∈ R', Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ a0Of hAut hΓ θ θp hAΓ, h w = w} =
      ∏ r ∈ R, Nat.card (fixSetT (t + r) E) := by
    calc ∏ r ∈ R', Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ a0Of hAut hΓ θ θp hAΓ, h w = w}
        = ∏ r ∈ R', Nat.card (fixSetT (t + (r : ZMod 2 × ZMod 2)) E) :=
          Finset.prod_congr rfl (fun r _ => hterm r)
      _ = ∏ r ∈ R, Nat.card (fixSetT (t + r) E) :=
          Finset.prod_subtype_of_mem (fun r => Nat.card (fixSetT (t + r) E)) hRPi
  rw [hprod] at horb
  have hE1 : ∀ g ∈ E, g * g = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    have hfA₀ : psi hΓ f ∈ a0Of hAut hΓ θ θp hAΓ := hf
    have h1 : f * f = 1 := by
      apply psi_injective hΓ
      rw [map_mul, map_one, ← sq]
      exact hAe.2 _ (a0Of_le hAΓ hfA₀)
    rw [← map_mul, h1, map_one]
  have hE2 : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    have hfA₀ : psi hΓ f ∈ a0Of hAut hΓ θ θp hAΓ := hf
    have hfA₀' : psi hΓ f' ∈ a0Of hAut hΓ θ θp hAΓ := hf'
    have h1 : f * f' = f' * f := by
      apply psi_injective hΓ
      rw [map_mul, map_mul]
      exact hAe.1 _ (a0Of_le hAΓ hfA₀) _ (a0Of_le hAΓ hfA₀')
    rw [← map_mul, ← map_mul, h1]
  have hA0F : Nat.card ↥(a0Of hAut hΓ θ θp hAΓ) ≤ Nat.card ↥F := by
    refine Nat.card_le_card_of_surjective
      (fun g : ↥F => (⟨psi hΓ g, g.2⟩ : ↥(a0Of hAut hΓ θ θp hAΓ))) ?_
    rintro ⟨a, ha⟩
    obtain ⟨g, hg, -⟩ := exists_psi_of_mem_a0 hAut hΓ θ θp hAΓ ha
    exact ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact ha⟩, Subtype.ext hg⟩
  have hFE : Nat.card ↥E = Nat.card ↥F :=
    Subgroup.card_map_of_injective (MulEquiv.prodCongr θ θp).injective
  have hAle : Nat.card ↥A ≤ Nat.card ↥E * Nat.card ↥(qOf hAut hΓ θ θp hAΓ) := by
    rw [card_A_eq hAut hΓ θ θp hAΓ]
    exact Nat.mul_le_mul_right _ (hFE ▸ hA0F)
  have hEQ : E ≠ ⊥ ∨ qOf hAut hΓ θ θp hAΓ ≠ ⊥ := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨hE0, hQ0⟩ := hcon
    have h1 : Nat.card ↥E = 1 := by rw [hE0]; exact Subgroup.card_bot
    have h2 : Nat.card ↥(qOf hAut hΓ θ θp hAΓ) = 1 := by rw [hQ0]; exact AddSubgroup.card_bot
    have : Nat.card ↥A ≤ 1 := by
      calc Nat.card ↥A ≤ Nat.card ↥E * Nat.card ↥(qOf hAut hΓ θ θp hAΓ) := hAle
        _ = 1 := by rw [h1, h2]
    exact hA1 (Subgroup.eq_bot_of_card_le A this)
  have hchk := hcheck t (piOf hAut hΓ θ θp) (qOf hAut hΓ θ θp hAΓ) R hPi0 hQPi hRPi hRuniq E hE1 hE2
    hEQ
  have h1 : Nat.card ↥A ^ 2 * Nat.card ↥((⨆ i, B i) ⊓ fixV A) < Nat.card ↥(⨆ i, B i) := by
    calc Nat.card ↥A ^ 2 * Nat.card ↥((⨆ i, B i) ⊓ fixV A)
        ≤ (Nat.card ↥E * Nat.card ↥(qOf hAut hΓ θ θp hAΓ)) ^ 2 *
            ∏ r ∈ R, Nat.card (fixSetT (t + r) E) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hAle 2) horb
      _ < 512 ^ Nat.card ↥(piOf hAut hΓ θ θp) := hchk
      _ = Nat.card ↥(⨆ i, B i) := hX.symm
  have h2 := card_mul_le_card_mul_inf (⨆ i, B i) (fixV A)
  rw [inf_comm] at h2
  have hcpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  have hXpos : 0 < Nat.card ↥((⨆ i, B i) ⊓ fixV A) := Nat.card_pos
  have h3 : Nat.card ↥A ^ 2 * Nat.card ↥(fixV A) * Nat.card ↥((⨆ i, B i) ⊓ fixV A) <
      Nat.card W * Nat.card ↥((⨆ i, B i) ⊓ fixV A) := by
    calc Nat.card ↥A ^ 2 * Nat.card ↥(fixV A) * Nat.card ↥((⨆ i, B i) ⊓ fixV A)
        = (Nat.card ↥A ^ 2 * Nat.card ↥((⨆ i, B i) ⊓ fixV A)) * Nat.card ↥(fixV A) := by ring
      _ < Nat.card ↥(⨆ i, B i) * Nat.card ↥(fixV A) := Nat.mul_lt_mul_of_pos_right h1 hcpos
      _ ≤ Nat.card W * Nat.card ↥((⨆ i, B i) ⊓ fixV A) := h2
  exact Nat.lt_of_mul_lt_mul_right h3

end CFSG.Quasithin.A38c16.Blocks
