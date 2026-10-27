module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Two
public import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableBF4Two

section Descent

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem center_le_ker_of_surjective (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) : Subgroup.center L' ≤ ψ.ker := by
  intro z hz
  have hz' : ψ z ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
  rw [hZ, Subgroup.mem_bot] at hz'
  exact hz'

theorem map_mem_ker_of_mem (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (α : MulAut L') {z : L'} (hz : z ∈ ψ.ker) :
    α z ∈ ψ.ker := by
  apply center_le_ker_of_surjective hψ hZ
  have hzc := hker hz
  rw [Subgroup.mem_center_iff] at hzc ⊢
  intro g
  obtain ⟨g', rfl⟩ := α.surjective g
  rw [← map_mul, ← map_mul, hzc g']

@[expose] noncomputable def descendFun (hψ : Function.Surjective ψ) (α : MulAut L') (r : R) : R :=
  ψ (α (Function.surjInv hψ r))

theorem descendFun_apply (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (α : MulAut L') (l : L') :
    descendFun hψ α (ψ l) = ψ (α l) := by
  set l₀ := Function.surjInv hψ (ψ l) with hl₀
  have h1 : ψ l₀ = ψ l := Function.surjInv_eq hψ _
  have hz : l⁻¹ * l₀ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have h2 := map_mem_ker_of_mem hψ hZ hker α hz
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

variable (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
  (hker : ψ.ker ≤ Subgroup.center L')

@[expose] noncomputable def descend (α : MulAut L') : MulAut R where
  toFun := descendFun hψ α
  invFun := descendFun hψ α⁻¹
  left_inv r := by
    obtain ⟨l, rfl⟩ := hψ r
    rw [descendFun_apply hψ hZ hker, descendFun_apply hψ hZ hker, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
  right_inv r := by
    obtain ⟨l, rfl⟩ := hψ r
    rw [descendFun_apply hψ hZ hker, descendFun_apply hψ hZ hker, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  map_mul' r s := by
    obtain ⟨l, rfl⟩ := hψ r
    obtain ⟨m, rfl⟩ := hψ s
    rw [← map_mul, descendFun_apply hψ hZ hker, descendFun_apply hψ hZ hker,
      descendFun_apply hψ hZ hker, map_mul, map_mul]

theorem descend_apply (α : MulAut L') (l : L') : descend hψ hZ hker α (ψ l) = ψ (α l) :=
  descendFun_apply hψ hZ hker α l

@[expose] noncomputable def descendHom : MulAut L' →* MulAut R where
  toFun := descend hψ hZ hker
  map_one' := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [descend_apply, MulAut.one_apply, MulAut.one_apply]
  map_mul' α β := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [MulAut.mul_apply, descend_apply, descend_apply, descend_apply, MulAut.mul_apply]

theorem descendHom_apply (α : MulAut L') (l : L') :
    descendHom hψ hZ hker α (ψ l) = ψ (α l) :=
  descendFun_apply hψ hZ hker α l

theorem descendHom_conj (t : L') :
    descendHom hψ hZ hker (MulAut.conj t) = MulAut.conj (ψ t) := by
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [descendHom_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem mem_range_conj_of_descendHom (hperf : commutator L' = ⊤) {α : MulAut L'}
    (h : descendHom hψ hZ hker α ∈ (MulAut.conj : R →* MulAut R).range) :
    α ∈ (MulAut.conj : L' →* MulAut L').range := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨t, rfl⟩ := hψ r
  refine ⟨t, ?_⟩
  ext l
  have h1 : ∀ m, ψ (α m) = ψ t * ψ m * (ψ t)⁻¹ := fun m => by
    rw [← descendHom_apply hψ hZ hker, ← hr, MulAut.conj_apply]
  rw [MulAut.conj_apply, TableBSymp.eq_conj_of_induces hker hperf α t h1 l]

end Descent


section Lift

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem exists_innerHom (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hZ : Subgroup.center R = ⊥) {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∃ χ : A →* R, Function.Injective χ ∧
      ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ := by
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    obtain ⟨t, rfl⟩ := hI hφI
    exact ⟨t, fun l => (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => TableBSymp.eq_conj_of_induces hker hperf (a : MulAut L') t'
      (fun l => by rw [hχ, ht'])
  refine ⟨χ, ?_, hinner⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
  apply Subtype.ext
  ext l
  rw [h1 l]
  simp

theorem exists_endNode_of_image (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (χ : A →* R) (hχinj : Function.Injective χ)
    (hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹)
    {t : R} (htA : t ∈ χ.range) (ht1 : t ≠ 1)
    (hcomp : IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set R)))
      (Subgroup.centralizer ({t} : Set R)))
    (hcent : ∀ s ∈ χ.range, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)),
      s * j = j * s) ↔ s ∈ Subgroup.zpowers t)) :
    ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  obtain ⟨a₀, rfl⟩ := htA
  obtain ⟨t', ht'⟩ := hψ (χ a₀)
  have ha₀ := hinner a₀ t' ht'
  have hfix : ggFix (a₀ : MulAut L') = Subgroup.centralizer ({t'} : Set L') := by
    ext l
    rw [mem_ggFix, ha₀, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      calc l * t' = t' * l * t'⁻¹ * t' := by rw [hl]
        _ = t' * l := by group
    · intro hl
      rw [← hl]
      group
  rw [← ht'] at hcomp hcent
  obtain ⟨hlayer, hcompL⟩ := TableBSymp.layer_centralizer_lift hψ hker hcomp
  refine ⟨a₀, a₀.2, fun h1 => ht1 ?_, ?_, fun a' ha' => ?_⟩
  · have : a₀ = 1 := Subtype.ext h1
    rw [this, map_one]
  · rw [hfix]
    exact hcompL
  · obtain ⟨s', hs'⟩ := hψ (χ ⟨a', ha'⟩)
    have hinn' := hinner ⟨a', ha'⟩ s' hs'
    set Kb := LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R)) with hKb
    have hKbq : CFSG.IsQuasisimple Kb := (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
    have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
    have hmapK := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hKbperf
    have hcent' := hcent (χ ⟨a', ha'⟩) ⟨⟨a', ha'⟩, rfl⟩
    rw [hfix, hlayer]
    constructor
    · intro hj
      have h1 : ∀ j ∈ Kb, χ ⟨a', ha'⟩ * j = j * χ ⟨a', ha'⟩ := by
        intro j hj'
        rw [← hmapK] at hj'
        obtain ⟨k, hk, rfl⟩ := hj'
        have e := hj k hk
        rw [hinn'] at e
        rw [← hs', ← map_mul, ← map_mul]
        congr 1
        calc s' * k = s' * k * s'⁻¹ * s' := by group
          _ = k * s' := by rw [e]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcent'.mp h1)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h2 : a₀ ^ n = ⟨a', ha'⟩ := hχinj (by rw [map_zpow, ← ht', hn])
      exact congrArg Subtype.val h2
    · intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h2 : a₀ ^ n = ⟨a', ha'⟩ := Subtype.ext hn
      have h3 : χ ⟨a', ha'⟩ ∈ Subgroup.zpowers (ψ t') :=
        Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [ht', ← map_zpow, h2]⟩
      have h4 := hcent'.mpr h3
      intro j hj
      rw [hinn']
      have hcomm := TableBSymp.commute_of_mem_commutator (x := s')
        (Y := Kb.comap ψ) (fun y hy => hker (by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs', h4 (ψ y) hy]
          group)) hj
      rw [hcomm]
      group

end Lift

@[expose] def GGF4TwoLocalEndNodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ A : Subgroup (TableBF4.RecipeGroup K), IsElemAbelian 3 A → 3 ^ 3 ≤ Nat.card A →
      (∃ V : Subgroup (TableBF4.RecipeGroup K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        A ≤ Subgroup.normalizer (V : Set (TableBF4.RecipeGroup K))) →
      ∃ t ∈ A, t ≠ 1 ∧
        IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set (TableBF4.RecipeGroup K))))
          (Subgroup.centralizer ({t} : Set (TableBF4.RecipeGroup K))) ∧
        ∀ s ∈ A, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer
            ({t} : Set (TableBF4.RecipeGroup K))), s * j = j * s) ↔ s ∈ Subgroup.zpowers t)

@[expose] def GGF4TwoOuterRankInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ τ : MulAut (TableBF4.RecipeGroup K),
      τ ∉ (MulAut.conj : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K)).range →
      τ ^ 2 = 1 → ∀ A : Subgroup (TableBF4.RecipeGroup K), IsElemAbelian 3 A →
        (∀ a ∈ A, MulAut.conj a * τ = τ * MulAut.conj a) → Nat.card A < 3 ^ 3

theorem sq_eq_one_of_card_le_two {H : Type*} [Group H] [Finite H] (hc : Nat.card H ≤ 2) (x : H) :
    x ^ 2 = 1 := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hd : orderOf x ∣ 2 := by
    have h1 := orderOf_dvd_natCard x
    rcases (show Nat.card H = 1 ∨ Nat.card H = 2 by omega) with h | h <;> rw [h] at h1
    · exact h1.trans (one_dvd 2)
    · exact h1
  exact orderOf_dvd_iff_pow_eq_one.mp hd

theorem sq_eq_one_zmod_two (x : Multiplicative (ZMod (2 * 1))) : x ^ 2 = 1 := by
  have h : ∀ y : ZMod (2 * 1), 2 • y = 0 := by decide
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul, h, ofAdd_zero]

section F4Two

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem center_eq_ker_card_le_two (hK : Nat.card K = 2) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* TableBF4.RecipeGroup K} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Subgroup.center L' = ψ.ker ∧ Nat.card ψ.ker ≤ 2 := by
  refine ⟨le_antisymm (center_le_ker_of_surjective hψ (TableBF4.center_recipeGroup_eq_bot K))
    hker, ?_⟩
  have hP : Group.IsPerfect L' := ⟨hperf⟩
  set η := (TableBF4.recipeEquiv K).toMonoidHom.comp ψ with hη
  have hηker : η.ker = ψ.ker := by
    ext l
    simp [hη, MonoidHom.mem_ker]
  have h := CFSG.LieType.Steinberg.CentralExt.F4Two.f4_two_card_ker_le_two hK η
    ((TableBF4.recipeEquiv K).surjective.comp hψ) (hηker ▸ hker)
  rwa [hηker] at h

theorem exists_theta_recipe (hK : Nat.card K = 2) :
    ∃ Θ : MulAut (TableBF4.RecipeGroup K) →* Multiplicative (ZMod (2 * 1)),
      Θ.ker = (MulAut.conj : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K)).range := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ₀, -, -, hker₀⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK]; norm_num)
  obtain ⟨Θ₁, hker₁⟩ : ∃ Θ : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * 1)),
      Θ.ker = (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    ⟨Θ₀, hker₀⟩
  set e := TableBF4.recipeEquiv K
  refine ⟨Θ₁.comp (MulAut.congr e).toMonoidHom, ?_⟩
  ext φ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker₁]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e.symm g, ?_⟩
    ext x
    have h1 := congrArg (fun χ : MulAut (adjointGroup .F4 K) => χ (e x)) hg
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [MulAut.conj_apply]
    apply e.injective
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    exact ⟨e g, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e g).symm⟩

end F4Two

theorem exists_twoLocal_of_inner_meet {L' R : Type} [Group L'] [Group R] [Finite L'] {ψ : L' →* R}
    (hcenter : Subgroup.center L' = ψ.ker) (hkercard : Nat.card ψ.ker ≤ 2)
    {A : Subgroup (MulAut L')} {χ : A →* R}
    (hlift : ∀ a : A, ∃ t' : L', ψ t' = χ a ∧ (a : MulAut L') = MulAut.conj t')
    {U : Subgroup (MulAut L')} (hU2 : IsPGroup 2 U)
    (hAU : A ≤ Subgroup.normalizer (U : Set (MulAut L')))
    (hUI : ¬ U ⊓ (MulAut.conj : L' →* MulAut L').range = ⊥) :
    ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ χ.range ≤ Subgroup.normalizer (V : Set R) := by
  set Vt := (U ⊓ (MulAut.conj : L' →* MulAut L').range).comap
    (MulAut.conj : L' →* MulAut L') with hVt
  have hsqker : ∀ z ∈ ψ.ker, z ^ 2 = 1 := fun z hz =>
    congrArg Subtype.val (sq_eq_one_of_card_le_two hkercard ⟨z, hz⟩)
  have hVt2 : IsPGroup 2 Vt := by
    rintro ⟨v, hv⟩
    obtain ⟨k, hk⟩ := hU2 ⟨MulAut.conj v, (Subgroup.mem_inf.mp hv).1⟩
    have hk' : MulAut.conj (v ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hz : v ^ 2 ^ k ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut L' => φ g) hk'
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * v ^ 2 ^ k = v ^ 2 ^ k * g * (v ^ 2 ^ k)⁻¹ * v ^ 2 ^ k := by rw [h1]
        _ = v ^ 2 ^ k * g := by group
    rw [hcenter] at hz
    refine ⟨k + 1, Subtype.ext ?_⟩
    show v ^ 2 ^ (k + 1) = 1
    rw [pow_succ, pow_mul]
    exact hsqker _ hz
  have hstab : ∀ a : A, ∀ h ∈ Vt.map ψ, χ a * h * (χ a)⁻¹ ∈ Vt.map ψ := by
    intro a h hh
    obtain ⟨v, hv, rfl⟩ := hh
    obtain ⟨t', ht', hat⟩ := hlift a
    refine ⟨t' * v * t'⁻¹, ?_, by rw [map_mul, map_mul, map_inv, ht']⟩
    have e : MulAut.conj (t' * v * t'⁻¹) =
        (a : MulAut L') * MulAut.conj v * (a : MulAut L')⁻¹ := by
      rw [hat, map_mul, map_mul, map_inv]
    show MulAut.conj (t' * v * t'⁻¹) ∈ U ⊓ (MulAut.conj : L' →* MulAut L').range
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨_, rfl⟩⟩
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hAU a.2) _).mp (Subgroup.mem_inf.mp hv).1
  refine ⟨Vt.map ψ, ?_, hVt2.map ψ, ?_⟩
  · obtain ⟨⟨φ, hφ⟩, hφ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUI
    obtain ⟨v, rfl⟩ := (Subgroup.mem_inf.mp hφ).2
    have hvV : v ∈ Vt := hφ
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨ψ v, v, hvV, rfl⟩, fun h => hφ1 ?_⟩
    have hψv : ψ v = 1 := congrArg Subtype.val h
    have hvc : v ∈ Subgroup.center L' := by
      rw [hcenter]
      exact hψv
    apply Subtype.ext
    ext l
    rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.mp hvc l]
    simp
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hstab a h, fun hh => ?_⟩
    have h1 := hstab a⁻¹ _ hh
    have e : (χ a)⁻¹ * (χ a * h * (χ a)⁻¹) * ((χ a)⁻¹)⁻¹ = h := by group
    rwa [map_inv, e] at h1

section Outer

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_lt_of_outer_meet (hK : Nat.card K = 2) (hE2 : GGF4TwoOuterRankInput) {L' : Type}
    [Group L']
    {ψ : L' →* TableBF4.RecipeGroup K} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center (TableBF4.RecipeGroup K) = ⊥) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} {χ : A →* TableBF4.RecipeGroup K}
    (hlift : ∀ a : A, ∃ t' : L', ψ t' = χ a ∧ (a : MulAut L') = MulAut.conj t')
    {U : Subgroup (MulAut L')} (hU : U ≠ ⊥) (hAU : A ≤ Subgroup.normalizer (U : Set (MulAut L')))
    (hUI : U ⊓ (MulAut.conj : L' →* MulAut L').range = ⊥) (hAbA : IsElemAbelian 3 χ.range) :
    Nat.card χ.range < 3 ^ 3 := by
  obtain ⟨Θ, hΘ⟩ := exists_theta_recipe hK
  set Φ := descendHom hψ hZ hker with hΦ
  have hΘ1 : ∀ φ : MulAut (TableBF4.RecipeGroup K),
      Θ φ = 1 ↔ φ ∈ (MulAut.conj : TableBF4.RecipeGroup K →* _).range := fun φ => by
    rw [← MonoidHom.mem_ker, hΘ]
  have hU'I : ∀ u ∈ U, Θ (Φ u) = 1 → u = 1 := by
    intro u hu h
    have h2 : u ∈ U ⊓ (MulAut.conj : L' →* MulAut L').range :=
      Subgroup.mem_inf.mpr ⟨hu, mem_range_conj_of_descendHom hψ hZ hker hperf ((hΘ1 _).mp h)⟩
    rw [hUI] at h2
    exact Subgroup.mem_bot.mp h2
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hτΘ : Θ (Φ u) ≠ 1 := fun h => hu1' (hU'I u hu h)
  have hτnot : Φ u ∉ (MulAut.conj : TableBF4.RecipeGroup K →* _).range := fun h =>
    hτΘ ((hΘ1 _).mpr h)
  have hτ2 : Φ u ^ 2 = 1 := by
    have h1 : u ^ 2 = 1 := hU'I (u ^ 2) (U.pow_mem hu 2) (by
      rw [map_pow, map_pow]
      exact sq_eq_one_zmod_two _)
    rw [← map_pow, h1, map_one]
  have hcomm : ∀ a ∈ χ.range, MulAut.conj a * Φ u = Φ u * MulAut.conj a := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨t', ht', hat⟩ := hlift a
    have hΦa : Φ (a : MulAut L') = MulAut.conj (χ a) := by
      rw [hat, hΦ, descendHom_conj, ht']
    have hw : (a : MulAut L') * u * (a : MulAut L')⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAU a.2) u).mp hu) (U.inv_mem hu)
    have hc : Θ (Φ (a : MulAut L')) = 1 := by
      rw [hΦa, hΘ1]
      exact ⟨_, rfl⟩
    have hΘw : Θ (Φ ((a : MulAut L') * u * (a : MulAut L')⁻¹ * u⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hc, one_mul, inv_one, mul_one, mul_inv_cancel]
    have h2 := congrArg Φ (hU'I _ hw hΘw)
    simp only [map_mul, map_inv, map_one, hΦa] at h2
    calc MulAut.conj (χ a) * Φ u
        = (MulAut.conj (χ a) * Φ u * (MulAut.conj (χ a))⁻¹ * (Φ u)⁻¹) * Φ u *
          MulAut.conj (χ a) := by group
      _ = Φ u * MulAut.conj (χ a) := by rw [h2, one_mul]
  exact hE2 K hK (Φ u) hτnot hτ2 χ.range hAbA hcomm

end Outer

section Main


theorem ggF4TwoEndNodeAdmInput_of_inputs (hE1 : GGF4TwoLocalEndNodeInput)
    (hE2 : GGF4TwoOuterRankInput) : GGF4TwoEndNodeAdmInput := by
  intro K _ _ _ hK2 L' _ _ ψ hψ hker hperf A hA hAI _ h3 hadm
  have hZ := TableBF4.center_recipeGroup_eq_bot K
  have hI := TableBF4.idImage_subset_inn K
  obtain ⟨hcenter, hkercard⟩ := center_eq_ker_card_le_two hK2 hψ hker hperf
  obtain ⟨χ, hχinj, hinner⟩ := exists_innerHom hψ hker hperf hZ hI hAI
  have hAbA : IsElemAbelian 3 χ.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card χ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hlift : ∀ a : A, ∃ t' : L', ψ t' = χ a ∧ (a : MulAut L') = MulAut.conj t' := by
    intro a
    obtain ⟨t', ht'⟩ := hψ (χ a)
    exact ⟨t', ht', MulEquiv.ext fun l => by rw [MulAut.conj_apply]; exact hinner a t' ht' l⟩
  have hloc : ∃ V : Subgroup (TableBF4.RecipeGroup K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      χ.range ≤ Subgroup.normalizer (V : Set (TableBF4.RecipeGroup K)) := by
    rcases hadm with ⟨U, hU, hU2, hAU⟩ | ⟨⟨a, ha, hna⟩, -⟩ | ⟨h3Z, -⟩
    · by_cases hUI : U ⊓ (MulAut.conj : L' →* MulAut L').range = ⊥
      · exfalso
        exact absurd (hcardAb ▸ h3) (not_le.mpr (card_lt_of_outer_meet hK2 hE2 hψ hZ hker hperf
          hlift hU hAU hUI hAbA))
      · exact exists_twoLocal_of_inner_meet hcenter hkercard hlift hU2 hAU hUI
    · exfalso
      obtain ⟨t', -, hat⟩ := hlift ⟨a, ha⟩
      exact hna ⟨t', hat.symm⟩
    · exfalso
      rw [hcenter] at h3Z
      have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
      have := Nat.le_of_dvd hpos h3Z
      omega
  obtain ⟨t, htA, ht1, hcomp, hcent⟩ := hE1 K hK2 χ.range hAbA (hcardAb ▸ h3) hloc
  exact exists_endNode_of_image hψ hker χ hχinj hinner htA ht1 hcomp hcent

end Main

end TableBF4Two

open TableBF4Two


theorem ggStdSubPreInputOn_F4Two_of_inputs (hE1 : GGF4TwoLocalEndNodeInput)
    (hE2 : GGF4TwoOuterRankInput) : GGStdSubPreInputOn GGTableBF4TwoLabel :=
  ggStdSubPreInputOn_F4Two (ggF4TwoEndNodeAdmInput_of_inputs hE1 hE2)

theorem ggStdSubPreInputOn_F4_all_of_inputs (hE1 : GGF4TwoLocalEndNodeInput)
    (hE2 : GGF4TwoOuterRankInput) : GGStdSubPreInputOn GGTableBF4AllLabel :=
  ggStdSubPreInputOn_F4_all (ggF4TwoEndNodeAdmInput_of_inputs hE1 hE2)

end CFSG.StandardType
