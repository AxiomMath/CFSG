module

public import CFSG.Quasithin.Background.E3Basic
import CFSG.Quasithin.Background.B1Coprime
import CFSG.Quasithin.Background.RonanE42Small
import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin

theorem exists_le_not_mem_cover {G : Type*} [Group G] [Finite G] {A A₁ : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1) (hA₁ : A₁ ≤ A)
    {a₀ : G} (ha₀₁ : a₀ ∉ A₁) :
    ∃ B : Subgroup G, A₁ ≤ B ∧ B ≤ A ∧ a₀ ∉ B ∧ ∀ b ∈ A, b ∈ B ∨ a₀ * b ∈ B := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {B | A₁ ≤ B ∧ B ≤ A ∧ a₀ ∉ B}
  obtain ⟨B, ⟨hB₁, hBA, hB₀⟩, hmax⟩ :=
    S.exists_max_image (fun B => Nat.card B) (Set.toFinite S) ⟨A₁, le_rfl, hA₁, ha₀₁⟩
  refine ⟨B, hB₁, hBA, hB₀, fun b hb => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hbB, hab⟩ := hcon
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  let B' : Subgroup G :=
    { carrier := {x | x ∈ A ∧ (x ∈ B ∨ x * b ∈ B)}
      one_mem' := ⟨A.one_mem, Or.inl B.one_mem⟩
      mul_mem' := by
        rintro x y ⟨hx, hxB⟩ ⟨hy, hyB⟩
        refine ⟨A.mul_mem hx hy, ?_⟩
        have hyb : y * b = b * y := hcomm y hy b hb
        rcases hxB with hxB | hxB <;> rcases hyB with hyB | hyB
        · exact Or.inl (B.mul_mem hxB hyB)
        · right
          rw [mul_assoc]
          exact B.mul_mem hxB hyB
        · right
          have h1 : x * y * b = x * b * y := by rw [mul_assoc, hyb, ← mul_assoc]
          rw [h1]
          exact B.mul_mem hxB hyB
        · left
          have h1 : x * b * (y * b) = x * y := by
            rw [hyb, mul_assoc, ← mul_assoc b b y, hsq b hb, one_mul]
          rw [← h1]
          exact B.mul_mem hxB hyB
      inv_mem' := by
        rintro x ⟨hx, hxB⟩
        show x⁻¹ ∈ A ∧ (x⁻¹ ∈ B ∨ x⁻¹ * b ∈ B)
        rw [hinv x hx]
        exact ⟨hx, hxB⟩ }
  have hBB' : B ≤ B' := fun x hx => ⟨hBA hx, Or.inl hx⟩
  have hbB' : b ∈ B' := ⟨hb, Or.inr (by rw [hsq b hb]; exact B.one_mem)⟩
  have ha₀B' : a₀ ∉ B' := by
    rintro ⟨-, h1 | h1⟩
    · exact hB₀ h1
    · exact hab h1
  have hB'S : B' ∈ S := ⟨hB₁.trans hBB', fun x hx => hx.1, ha₀B'⟩
  have hEq : B = B' := Subgroup.eq_of_le_of_card_ge hBB' (hmax B' hB'S)
  exact hbB (by rw [hEq]; exact hbB')

theorem eq_one_of_prod_eq_one_of_sSupIndep {G : Type*} [CommGroup G] {T : Set (Subgroup G)}
    (hT : sSupIndep T) (f : G → Subgroup G) (O : Finset G) (hfT : ∀ y ∈ O, f y ∈ T)
    (hmem : ∀ y ∈ O, y ∈ f y) (hinj : Set.InjOn f O) (hprod : ∏ y ∈ O, y = 1) :
    ∀ y ∈ O, y = 1 := by
  classical
  induction O using Finset.induction_on with
  | empty => simp
  | insert y₀ O hy₀ ih =>
    rw [Finset.prod_insert hy₀] at hprod
    have hO : ∀ y ∈ O, f y ≠ f y₀ := fun y hy h =>
      (ne_of_mem_of_not_mem hy hy₀)
        (hinj (Finset.mem_insert_of_mem hy) (Finset.mem_insert_self _ _) h)
    have hsup : ∏ y ∈ O, y ∈ sSup (T \ {f y₀}) :=
      Subgroup.prod_mem _ fun y hy => Subgroup.mem_sSup_of_mem
        (show f y ∈ T \ {f y₀} from ⟨hfT y (Finset.mem_insert_of_mem hy), hO y hy⟩)
        (hmem y (Finset.mem_insert_of_mem hy))
    have hy₀1 : y₀ = 1 := by
      have h1 : y₀ = (∏ y ∈ O, y)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      have h2 : (∏ y ∈ O, y)⁻¹ ∈ sSup (T \ {f y₀}) := Subgroup.inv_mem _ hsup
      rw [← h1] at h2
      exact Subgroup.disjoint_def.mp (hT (hfT y₀ (Finset.mem_insert_self _ _)))
        (hmem y₀ (Finset.mem_insert_self _ _)) h2
    rw [hy₀1, one_mul] at hprod
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hy₀1
    · exact ih (fun y hy => hfT y (Finset.mem_insert_of_mem hy))
        (fun y hy => hmem y (Finset.mem_insert_of_mem hy))
        (hinj.mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))) hprod y hy

variable {V : Type} [CommGroup V]

theorem autSub_mem_aSet {k : ℕ} {X A : Subgroup (MulAut V)} (hA : A ∈ E3.aSet k X)
    {U : Subgroup V} (hAU : A ≤ stabSub U) (hne : autSub A U ≠ ⊥) :
    autSub A U ∈ E3.aSet k (autSub X U) := by
  obtain ⟨hAX, -, hAe, hAfix⟩ := hA
  refine ⟨autSub_mono hAX U, hne, ⟨fun x hx y hy => ?_, fun x hx => ?_⟩, fun B hB hm => ?_⟩
  · obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hx
    obtain ⟨g', hg'A, rfl⟩ := mem_autSub.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAe.1 _ hgA _ hg'A)
  · obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hx
    rw [← map_pow]
    have h1 : g ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 _ hgA)
    rw [h1, map_one]
  ·
    let r : ↥A →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hAU)
    have hr : ∀ a : ↥A, r a ∈ autSub A U := fun a =>
      mem_autSub.mpr ⟨Subgroup.inclusion hAU a, a.2, rfl⟩
    let f : ↥A →* ↥(autSub A U) := r.codRestrict _ hr
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hx
      exact ⟨⟨g, hgA⟩, rfl⟩
    let K : Subgroup ↥A := (B.subgroupOf (autSub A U)).comap f
    let B' : Subgroup (MulAut V) := K.map A.subtype
    have hB'A : B' ≤ A := Subgroup.map_subtype_le K
    have hsub : B'.subgroupOf A = K :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective K
    have hrel : B'.relIndex A = B.relIndex (autSub A U) := by
      rw [Subgroup.relIndex, hsub, Subgroup.index_comap_of_surjective _ hf]
      rfl
    have hm' : E3.mQuot A B' < k := by
      unfold E3.mQuot at hm ⊢
      rw [hrel]
      exact hm
    have hfix := hAfix B' hB'A hm'
    have hmemB' : ∀ g : MulAut V, g ∈ B' ↔ ∃ hg : g ∈ A, r ⟨g, hg⟩ ∈ B := by
      intro g
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, ha⟩
      · rintro ⟨hg, hgB⟩
        exact ⟨⟨g, hg⟩, hgB, rfl⟩
    have h1 : ∀ u : ↥U, u ∈ fixV B ↔ (u : V) ∈ fixV B' := by
      intro u
      constructor
      · intro hu
        refine mem_fixV.2 fun g hg => ?_
        obtain ⟨hgA, hgB⟩ := (hmemB' g).1 hg
        exact congrArg Subtype.val (mem_fixV.1 hu _ hgB)
      · intro hu
        refine mem_fixV.2 fun b hb => ?_
        obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp (hB hb)
        have hgB' : (g : MulAut V) ∈ B' := (hmemB' g).2 ⟨hgA, hb⟩
        exact Subtype.ext (mem_fixV.1 hu _ hgB')
    have h2 : ∀ u : ↥U, u ∈ fixV (autSub A U) ↔ (u : V) ∈ fixV A := by
      intro u
      rw [mem_fixV_autSub, mem_fixV]
      exact ⟨fun h g hg => h g hg (hAU hg), fun h g hg _ => h g hg⟩
    ext u
    rw [h1, h2, hfix]

theorem le_stabSub_of_mem_aSet [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {j : ℕ} (hj : 2 ≤ j)
    {X A : Subgroup (MulAut V)} (hA : A ∈ E3.aSet j X) {U : Subgroup V}
    (hind : sSupIndep {Y : Subgroup V | ∃ a ∈ A, Y = U.map a.toMonoidHom}) :
    A ≤ stabSub U := by
  classical
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨-, -, hAe, hAfix⟩ := hA
  have hmemT : ∀ a ∈ A, U.map a.toMonoidHom ∈ {Y : Subgroup V | ∃ a ∈ A, Y = U.map a.toMonoidHom} :=
    fun a ha => ⟨a, ha, rfl⟩
  by_contra hcon
  obtain ⟨a₀, ha₀A, ha₀U⟩ := SetLike.not_le_iff_exists.mp hcon
  let A₁ : Subgroup (MulAut V) := A ⊓ stabSub U
  have hA₁A : A₁ ≤ A := inf_le_left
  have ha₀A₁ : a₀ ∉ A₁ := fun h => ha₀U h.2
  have hU : U ≠ ⊥ := by
    rintro rfl
    exact ha₀U fun u => by rw [Subgroup.mem_bot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  have hA₁p : IsPGroup 2 A₁ := (E3.isPGroup_of_isElemAbelian2 hAe).to_le hA₁A
  obtain ⟨w, hwU, hw1, hwfix⟩ :=
    B1.exists_fixed_ne_one hV hA₁p (fun b hb m hm => (hb.2 m).2 hm) hU
  have hUT : U = U.map (1 : MulAut V).toMonoidHom :=
    (StabLat.mem_stabSub_iff_map.mp (stabSub U).one_mem).symm
  have hstab : ∀ c ∈ A, c w = w → c ∈ A₁ := by
    intro c hc hcw
    refine ⟨hc, ?_⟩
    by_contra hcU
    have hne : U.map c.toMonoidHom ≠ U := fun h => hcU (StabLat.mem_stabSub_iff_map.mpr h)
    have hdisj : Disjoint (U.map c.toMonoidHom) U :=
      hind.pairwiseDisjoint (hmemT c hc) ⟨1, A.one_mem, hUT⟩ hne
    exact hw1 (Subgroup.disjoint_def.mp hdisj ⟨w, hwU, hcw⟩ hwU)
  have hmapeq : ∀ c ∈ A, ∀ c' ∈ A, U.map c.toMonoidHom = U.map c'.toMonoidHom →
      c⁻¹ * c' ∈ A₁ := by
    intro c hc c' hc' h
    refine ⟨A.mul_mem (A.inv_mem hc) hc', fun u => ?_⟩
    have h1 : c' u ∈ U.map c.toMonoidHom ↔ c' u ∈ U.map c'.toMonoidHom := by rw [h]
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h1
    rw [MulAut.mul_apply, MulAut.inv_apply]
    exact h1
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hAe.2 a ha
  obtain ⟨B, hA₁B, hBA, ha₀B, hcov⟩ := exists_le_not_mem_cover hAe.1 hsq hA₁A ha₀A₁
  have hrel : B.relIndex A = 2 := by
    rw [Subgroup.relIndex_eq_two_iff']
    refine ⟨a₀, ha₀A, fun b hb => ?_⟩
    by_cases hbB : b ∈ B
    · exact Or.inr ⟨hbB, fun h => ha₀B (by simpa using B.mul_mem h (B.inv_mem hbB))⟩
    · exact Or.inl ⟨(hcov b hb).resolve_left hbB, hbB⟩
  have hmB : E3.mQuot A B < j := by
    unfold E3.mQuot
    rw [hrel, padicValNat.self (by norm_num)]
    omega
  have hfixB := hAfix B hBA hmB
  have : Fintype ↥B := Fintype.ofFinite _
  let OB : Finset V := Finset.univ.image fun b : ↥B => (b : MulAut V) w
  have hmemOB : ∀ y, y ∈ OB ↔ ∃ b ∈ B, b w = y := by
    intro y
    simp only [OB, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, b.2, hb⟩, fun ⟨b, hb, h⟩ => ⟨⟨b, hb⟩, h⟩⟩
  have himage : ∀ b ∈ B, OB.image b = OB := by
    intro b hb
    ext y
    rw [Finset.mem_image, hmemOB]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b', hb', rfl⟩ := (hmemOB x).1 hx
      exact ⟨b * b', B.mul_mem hb hb', rfl⟩
    · rintro ⟨b', hb', rfl⟩
      refine ⟨b⁻¹ (b' w), (hmemOB _).2 ⟨b⁻¹ * b', B.mul_mem (B.inv_mem hb) hb', rfl⟩, ?_⟩
      show b (b⁻¹ (b' w)) = b' w
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hprod_map : ∀ c : MulAut V, c (∏ x ∈ OB, x) = ∏ y ∈ OB.image c, y := by
    intro c
    rw [map_prod, Finset.prod_image fun x _ y _ h => c.injective h]
  have hvB : (∏ x ∈ OB, x) ∈ fixV B :=
    mem_fixV.2 fun b hb => by rw [hprod_map, himage b hb]
  have hva₀ : a₀ (∏ x ∈ OB, x) = ∏ x ∈ OB, x :=
    mem_fixV.1 (hfixB ▸ hvB) a₀ ha₀A
  have hdisjO : Disjoint OB (OB.image a₀) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy'
    obtain ⟨b', hb', rfl⟩ := (hmemOB x).1 hx
    obtain ⟨b, hb, hbw⟩ := (hmemOB _).1 hy
    have hcw : ((a₀ * b')⁻¹ * b) w = w := by
      rw [MulAut.mul_apply, hbw, MulAut.inv_apply, MulEquiv.symm_apply_eq]
      rfl
    have hc := hA₁B (hstab _ (A.mul_mem (A.inv_mem (A.mul_mem ha₀A (hBA hb'))) (hBA hb)) hcw)
    apply ha₀B
    have h1 : a₀ = b * ((a₀ * b')⁻¹ * b)⁻¹ * b'⁻¹ := by group
    rw [h1]
    exact B.mul_mem (B.mul_mem hb (B.inv_mem hc)) (B.inv_mem hb')
  let O : Finset V := OB ∪ OB.image a₀
  have hprodO : ∏ y ∈ O, y = 1 := by
    rw [Finset.prod_union hdisjO, ← hprod_map, hva₀, ← sq, hV]
  have hOorb : ∀ y ∈ O, ∃ c ∈ A, c w = y := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨b, hb, rfl⟩ := (hmemOB y).1 hy
      exact ⟨b, hBA hb, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨b, hb, rfl⟩ := (hmemOB x).1 hx
      exact ⟨a₀ * b, A.mul_mem ha₀A (hBA hb), rfl⟩
  let cOf : V → MulAut V := fun y => Classical.epsilon fun c : MulAut V => c ∈ A ∧ c w = y
  have hcOf : ∀ y ∈ O, cOf y ∈ A ∧ cOf y w = y := fun y hy =>
    Classical.epsilon_spec (p := fun c : MulAut V => c ∈ A ∧ c w = y)
      (let ⟨c, hc, hcy⟩ := hOorb y hy; ⟨c, hc, hcy⟩)
  have hall := eq_one_of_prod_eq_one_of_sSupIndep hind (fun y => U.map (cOf y).toMonoidHom) O
    (fun y hy => hmemT _ (hcOf y hy).1)
    (fun y hy => ⟨w, hwU, (hcOf y hy).2⟩)
    (fun y hy y' hy' h => by
      have hc := hwfix _ (hmapeq _ (hcOf y hy).1 _ (hcOf y' hy').1 h)
      rw [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_eq] at hc
      rw [← (hcOf y hy).2, ← (hcOf y' hy').2, hc])
    hprodO
  have hwO : w ∈ O := Finset.mem_union_left _ ((hmemOB w).2 ⟨1, B.one_mem, rfl⟩)
  exact hw1 (hall w hwO)

theorem aParam_le_of_permutes [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {ι : Type*}
    {Wf : ι → Subgroup V} (hind : iSupIndep Wf) (htop : ⨆ i, Wf i = ⊤)
    {X : Subgroup (MulAut V)} (hperm : ∀ x ∈ X, ∀ i, ∃ i', (Wf i).map x.toMonoidHom = Wf i')
    {N : ℕ} (hN : 1 ≤ N) (hle : ∀ i, E3.aParam (autSub X (Wf i)) ≤ N) :
    E3.aParam X ≤ N := by
  apply RonanE42.aParam_le_of_aSet_empty
  intro A hA
  have hstab : ∀ i, A ≤ stabSub (Wf i) := fun i =>
    le_stabSub_of_mem_aSet hV (by omega) hA (hind.sSupIndep_range.mono (by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨i', hi'⟩ := hperm a (hA.1 ha) i
      exact ⟨i', hi'.symm⟩))
  obtain ⟨i, hi⟩ : ∃ i, autSub A (Wf i) ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hA.2.1
    have hle : ∀ i, Wf i ≤ fixV A := by
      intro i v hv
      refine mem_fixV.2 fun a ha => ?_
      have h1 : resHom (Wf i) ⟨a, hstab i ha⟩ ∈ autSub A (Wf i) :=
        mem_autSub.mpr ⟨⟨a, hstab i ha⟩, ha, rfl⟩
      rw [h i, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val (DFunLike.congr_fun h1 ⟨v, hv⟩)
    have htopA : fixV A = ⊤ := top_le_iff.mp (htop ▸ iSup_le hle)
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    ext v
    exact mem_fixV.1 (htopA ▸ Subgroup.mem_top v) a ha
  have h1 := E3.le_aParam_of_mem_aSet (by omega) (autSub_mem_aSet hA (hstab i) hi)
  have h2 := hle i
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
