module

public import CFSG.OddTranspositions.PartThree.Statements
import CFSG.Timmesfeld.Bridge.OddTranspBasic
import CFSG.OddTranspositions.PartThree.Nine.Wreath
import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.OddTranspositions.SixSixWreathClass
import CFSG.OddTranspositions.WreathBaseMinimal
import CFSG.OddTranspositions.WidthSylow
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.PartFour.Fourteen.ModelWreath
import CFSG.Walter.PSL2Facts.Even
import CFSG.LocalAnalysis.EvenSporadicStandard.SolvableRadical
import CFSG.Timmesfeld.Bridge.Asc72WreathConn
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki Equiv SemidirectProduct
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem exists_swap_class
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) (Φ : G ≃* L2Wreath f n) :
    ∃ f' n' : ℕ, 2 ≤ f' ∧ 2 ≤ n' ∧ ∃ a b : Fin n', a ≠ b ∧ ∃ Ψ : G ≃* L2Wreath f' n',
      Ψ hC.d = inr (swap a b) ∧
        ∀ x, x ∈ D ↔ IsConj (inr (swap a b) : L2Wreath f' n') (Ψ x) := by
  have hbase : Asc72.IsMinimalNormal (l2WreathBase f n) := by
    simpa [l2WreathBase] using base_isMinimalNormal f n hf hn
  obtain ⟨f', n', hf', a, b, hab, Ψ, hΨu, hΨD⟩ :=
    Nine.exists_wreath_normalized hC hrad (IsMinimalNormal.comap_mulEquiv Φ hbase)
      (not_isSimpleGroup_comap_mulEquiv Φ (l2WreathBase_not_isSimpleGroup hf hn))
  have hn' : 2 ≤ n' := by
    have := a.isLt
    have := b.isLt
    have := Fin.val_ne_of_ne hab
    omega
  exact ⟨f', n', hf', hn', a, b, hab, Ψ, hΨu, hΨD⟩

private theorem eq_inl_of_mem_l2WreathBase {f n : ℕ} {w : L2Wreath f n}
    (hw : w ∈ l2WreathBase f n) : w = SemidirectProduct.inl w.left := by
  obtain ⟨x, hx⟩ := hw
  rw [← hx, SemidirectProduct.left_inl]

private theorem not_isSolvable_psl2Model {f : ℕ} (hf : 2 ≤ f) :
    ¬ Group.IsSolvable (PSL2Model f) := by
  have hB : IsBenderGroup (PSL2Model f) := .isPSL2 f hf (MulEquiv.refl _)
  have : IsSimpleGroup (PSL2Model f) := IsBenderGroup.isSimpleGroup hB
  obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
  exact fun hs => hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hs a b)

private theorem not_isSolvable_l2WreathBase {f n : ℕ} (hf : 2 ≤ f) (hn : 1 ≤ n) :
    ¬ Group.IsSolvable (l2WreathBase f n) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let π : l2WreathBase f n →* PSL2Model f :=
    { toFun := fun b => (b : L2Wreath f n).left i₀
      map_one' := rfl
      map_mul' := fun a b => by
        show (↑(a * b) : L2Wreath f n).left i₀ =
          (a : L2Wreath f n).left i₀ * (b : L2Wreath f n).left i₀
        rw [Subgroup.coe_mul, eq_inl_of_mem_l2WreathBase a.2,
          eq_inl_of_mem_l2WreathBase b.2, ← map_mul, SemidirectProduct.left_inl]
        rfl }
  have hsurj : Function.Surjective π := by
    intro y
    refine ⟨⟨SemidirectProduct.inl (Pi.mulSingle (M := fun _ : Fin n => PSL2Model f) i₀ y),
      ?_⟩, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    show (SemidirectProduct.inl (Pi.mulSingle i₀ y) : L2Wreath f n).left i₀ = y
    rw [SemidirectProduct.left_inl, Pi.mulSingle_eq_same]
  intro hs
  have := hs
  exact not_isSolvable_psl2Model hf (Group.isSolvable_of_surjective (f := π) hsurj)

private theorem solvableRadical_l2Wreath_eq_bot {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) :
    CFSG.solvableRadical (L2Wreath f n) = ⊥ := by
  have hR : Group.IsSolvable (CFSG.solvableRadical (L2Wreath f n)) :=
    OddTransp.isSolvable_solvableRadical
  have hBn : (l2WreathBase f n).Normal := (base_isMinimalNormal f n hf hn).1
  have hNB : CFSG.solvableRadical (L2Wreath f n) ⊓ l2WreathBase f n = ⊥ := by
    have : (CFSG.solvableRadical (L2Wreath f n) ⊓ l2WreathBase f n).Normal := inferInstance
    rcases (base_isMinimalNormal f n hf hn).2.2
        (CFSG.solvableRadical (L2Wreath f n) ⊓ l2WreathBase f n) inferInstance inf_le_right with
      h | h
    · exact h
    · exfalso
      have hle : l2WreathBase f n ≤ CFSG.solvableRadical (L2Wreath f n) :=
        h.ge.trans inf_le_left
      have : Group.IsSolvable (l2WreathBase f n) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      have hn1 : 1 ≤ n := by omega
      exact not_isSolvable_l2WreathBase hf hn1 inferInstance
  have hcomm : ⁅CFSG.solvableRadical (L2Wreath f n), l2WreathBase f n⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_of_disjoint (disjoint_iff.mpr hNB)
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rw [centralizer_l2WreathBase (f := f) (n := n) hf] at hle
  exact le_bot_iff.mp hle

omit [Finite G] in
private theorem left_eq_of_commute_swap {f : ℕ} (hC : HypothesisC D) (Ψ : G ≃* L2Wreath f 2)
    (hΨu : Ψ hC.d = inr (swap (0 : Fin 2) 1)) {g : G} (hg : Commute g hC.d) (p : Fin 2) :
    (Ψ g).left p = (Ψ g).left 0 := by
  have h1 : Commute (Ψ g) (inr (swap (0 : Fin 2) 1)) := by
    rw [← hΨu]
    exact hg.map Ψ
  have h2 := congrArg (fun w : L2Wreath f 2 => w.left 1) h1.eq
  simp only [mul_left, left_inr, map_one, one_mul, mul_one, right_inr,
    WreathConn.permAct_apply, swap_inv, swap_apply_right] at h2
  fin_cases p
  · rfl
  · exact h2

private noncomputable def rhoTwo {f : ℕ} (hC : HypothesisC D) (Ψ : G ≃* L2Wreath f 2)
    (hΨu : Ψ hC.d = inr (swap (0 : Fin 2) 1)) :
    Subgroup.centralizer ({hC.d} : Set G) →* PSL2Model f :=
  { toFun := fun g => (Ψ (g : G)).left 0
    map_one' := by simp
    map_mul' := fun g h => by
      show (Ψ ((g : G) * h)).left 0 = (Ψ g).left 0 * (Ψ h).left 0
      rw [map_mul, mul_left, Pi.mul_apply, WreathConn.permAct_apply,
        left_eq_of_commute_swap hC Ψ hΨu
          (Subgroup.mem_centralizer_singleton_iff.mp h.2)] }

omit [Finite G] in
private theorem rhoTwo_ker {f : ℕ} (hC : HypothesisC D) (Ψ : G ≃* L2Wreath f 2)
    (hΨu : Ψ hC.d = inr (swap (0 : Fin 2) 1)) {g : G}
    (hg : g ∈ Subgroup.centralizer ({hC.d} : Set G)) (h : (Ψ g).left 0 = 1) :
    g = 1 ∨ g = hC.d := by
  have hgc : Commute g hC.d := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hleft : (Ψ g).left = 1 :=
    funext fun p => (left_eq_of_commute_swap hC Ψ hΨu hgc p).trans h
  have hperm : ∀ σ : Perm (Fin 2), σ = 1 ∨ σ = swap (0 : Fin 2) 1 := by decide
  rcases hperm (Ψ g).right with hr | hr
  · left
    apply Ψ.injective
    rw [map_one]
    exact SemidirectProduct.ext hleft hr
  · right
    apply Ψ.injective
    rw [hΨu]
    exact SemidirectProduct.ext hleft hr

private theorem card_le_two_of_subset {A : Type*} [Group A] [Finite A] {K : Subgroup A} {d : A}
    (h : ∀ x ∈ K, x = 1 ∨ x = d) : Nat.card K ≤ 2 := by
  classical
  by_cases hdK : d ∈ K
  · have h' : ∀ x : K, x = 1 ∨ x = ⟨d, hdK⟩ := by
      intro x
      rcases h x x.2 with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    let f : K → Fin 2 := fun x => if x = 1 then 0 else 1
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : x = 1
      · have hfx : f x = 0 := by simp [f, hx]
        have hfy : f y = 0 := by rw [← hxy, hfx]
        by_cases hy : y = 1
        · rw [hx, hy]
        · have h1 : f y = 1 := by simp [f, hy]
          rw [hfy] at h1
          exact absurd h1 (by decide)
      · have hfx : f x = 1 := by simp [f, hx]
        have hfy : f y = 1 := by rw [← hxy, hfx]
        by_cases hy : y = 1
        · have h1 : f y = 0 := by simp [f, hy]
          rw [hfy] at h1
          exact absurd h1 (by decide)
        · rcases h' x with h1 | h1 <;> rcases h' y with h2 | h2
          · rw [h1, h2]
          · exact absurd h1 hx
          · exact absurd h2 hy
          · rw [h1, h2]
    calc Nat.card K ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  · have hbot : K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases h x hx with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · exact absurd hx (h1 ▸ hdK)
    rw [hbot, Subgroup.card_bot]
    omega

private theorem solvableRadical_psl2Model_eq_bot {f : ℕ} (hf : 2 ≤ f) :
    CFSG.solvableRadical (PSL2Model f) = ⊥ := by
  have hB : IsBenderGroup (PSL2Model f) := .isPSL2 f hf (MulEquiv.refl _)
  have : IsSimpleGroup (PSL2Model f) := IsBenderGroup.isSimpleGroup hB
  obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
  exact CFSG.solvableRadical_eq_bot_of_isSimpleGroup _ ⟨a, b, hab⟩

private theorem solvableRadical_le_center_of_wreath_two (hC : HypothesisC D) {f : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model f)
    (hradL : CFSG.solvableRadical (PSL2Model f) = ⊥) :
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) := by
  let Z := Subgroup.center (Halpha D hC.alpha)
  let q : Halpha D hC.alpha →* (Halpha D hC.alpha ⧸ Z) := QuotientGroup.mk' Z
  let ρ' : Halpha D hC.alpha →* PSL2Model f := e.toMonoidHom.comp q
  have hnormal : ((CFSG.solvableRadical (Halpha D hC.alpha)).map ρ').Normal :=
    Subgroup.Normal.map inferInstance ρ' (e.surjective.comp (QuotientGroup.mk'_surjective Z))
  have : Group.IsSolvable (CFSG.solvableRadical (Halpha D hC.alpha)) :=
    OddTransp.isSolvable_solvableRadical
  have hsol : Group.IsSolvable ((CFSG.solvableRadical (Halpha D hC.alpha)).map ρ') :=
    Group.isSolvable_of_surjective (ρ'.subgroupMap_surjective _)
  have hle : (CFSG.solvableRadical (Halpha D hC.alpha)).map ρ' ≤ ⊥ := by
    rw [← hradL]
    exact OddTransp.le_solvableRadical hnormal hsol
  intro x hx
  have hx1 : e (q x) = 1 := by
    have hmem := hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa [ρ', MonoidHom.comp_apply] using hmem
  exact (QuotientGroup.eq_one_iff x).mp (e.injective (hx1.trans (map_one e).symm))

private theorem card_Halpha_le_of_wreath_two (hC : HypothesisC D) {f : ℕ}
    (Ψ : G ≃* L2Wreath f 2) (hΨu : Ψ hC.d = inr (swap (0 : Fin 2) 1)) :
    Nat.card (Halpha D hC.alpha) ≤ 2 * Nat.card (PSL2Model f) := by
  have hHC : Halpha D hC.alpha ≤ Subgroup.centralizer ({hC.d} : Set G) :=
    Halpha_le_centralizer_d hC
  have hdC : hC.d ∈ Subgroup.centralizer ({hC.d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl hC.d)
  have hkerC : Nat.card (rhoTwo hC Ψ hΨu).ker ≤ 2 := by
    refine card_le_two_of_subset (d := (⟨hC.d, hdC⟩ :
      Subgroup.centralizer ({hC.d} : Set G))) ?_
    intro x hx
    have hx1 : (Ψ ((x : Subgroup.centralizer ({hC.d} : Set G)) : G)).left 0 = 1 := hx
    rcases rhoTwo_ker hC Ψ hΨu x.2 hx1 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  let ρH : Halpha D hC.alpha →* PSL2Model f :=
    (rhoTwo hC Ψ hΨu).comp (Subgroup.inclusion hHC)
  have hkerH : Nat.card ρH.ker ≤ 2 := by
    have hinj : Function.Injective fun x : ρH.ker =>
        (⟨(Subgroup.inclusion hHC) (x : Halpha D hC.alpha), x.2⟩ :
          (rhoTwo hC Ψ hΨu).ker) := by
      intro x y hxy
      exact Subtype.ext ((Subgroup.inclusion_injective hHC) (congrArg Subtype.val hxy))
    have hle : Nat.card ρH.ker ≤ Nat.card (rhoTwo hC Ψ hΨu).ker :=
      Nat.card_le_card_of_injective _ hinj
    exact hle.trans hkerC
  have hHcard : Nat.card (Halpha D hC.alpha) ≤ 2 * Nat.card (PSL2Model f) := by
    have hquot : Nat.card (Halpha D hC.alpha ⧸ ρH.ker) ≤ Nat.card (PSL2Model f) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρH).toEquiv]
      exact Nat.card_le_card_of_injective (fun x : ρH.range => (x : PSL2Model f))
        fun a b hab => Subtype.ext hab
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ρH.ker
    rw [hcard]
    calc Nat.card (Halpha D hC.alpha ⧸ ρH.ker) * Nat.card ρH.ker
        ≤ Nat.card (PSL2Model f) * 2 := Nat.mul_le_mul hquot hkerH
      _ = 2 * Nat.card (PSL2Model f) := Nat.mul_comm _ _
  exact hHcard

private theorem isPGroup_of_wreath_two (hC : HypothesisC D) {f : ℕ} (hf : 2 ≤ f)
    (Ψ : G ≃* L2Wreath f 2) (hΨu : Ψ hC.d = inr (swap (0 : Fin 2) 1))
    (hΨD : ∀ x, x ∈ D ↔ IsConj (inr (swap (0 : Fin 2) 1) : L2Wreath f 2) (Ψ x)) :
    IsPGroup 2 (CFSG.solvableRadical (Halpha D hC.alpha)) := by
  obtain ⟨e⟩ := Nine.nonempty_quotientCenter_mulEquiv_of_wreath_two hC hf Ψ hΨu hΨD
  have hOle := solvableRadical_le_center_of_wreath_two hC e (solvableRadical_psl2Model_eq_bot hf)
  have hZle := CFSG.OddTranspositions.center_le_solvableRadical (Halpha D hC.alpha)
  have hHcard := card_Halpha_le_of_wreath_two hC Ψ hΨu
  have hZH : Nat.card (Halpha D hC.alpha) =
      Nat.card (Subgroup.center (Halpha D hC.alpha)) * Nat.card (PSL2Model f) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (Halpha D hC.alpha)), Nat.card_congr e.toEquiv, Nat.mul_comm]
  have hZcard : Nat.card (Subgroup.center (Halpha D hC.alpha)) ≤ 2 := by
    have hpos : 0 < Nat.card (PSL2Model f) := Nat.card_pos
    have h1 : Nat.card (Subgroup.center (Halpha D hC.alpha)) * Nat.card (PSL2Model f) ≤
        2 * Nat.card (PSL2Model f) := by
      rw [← hZH]
      exact hHcard
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hOZ : CFSG.solvableRadical (Halpha D hC.alpha) =
      Subgroup.center (Halpha D hC.alpha) := le_antisymm hOle hZle
  rw [hOZ]
  have hpos : 0 < Nat.card (Subgroup.center (Halpha D hC.alpha)) := Nat.card_pos
  rcases (by omega : Nat.card (Subgroup.center (Halpha D hC.alpha)) = 1 ∨
    Nat.card (Subgroup.center (Halpha D hC.alpha)) = 2) with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [h1]; norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [h1]; norm_num)

private theorem isPGroup_of_wreath_five_le (hC : HypothesisC D) {f n : ℕ} (hf : 2 ≤ f)
    (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) (Ψ : G ≃* L2Wreath f n)
    (hΨD : ∀ x, x ∈ D ↔ IsConj (inr (swap a b) : L2Wreath f n) (Ψ x)) :
    IsPGroup 2 (CFSG.solvableRadical (Halpha D hC.alpha)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  have hD : ∀ u, u ∈ D ↔ Ψ u ∈ WreathEndgame.swapSet f (k + 2) := fun u => by
    rw [hΨD u]
    exact ⟨WreathEndgame.mem_swapSet_of_isConj hab, WreathEndgame.isConj_of_mem_swapSet hab⟩
  obtain ⟨eH⟩ := WreathEndgame.halpha_equiv (f := f) (k := k) hC hf hk Ψ hD
  have hradL : CFSG.solvableRadical (L2Wreath f k) = ⊥ :=
    solvableRadical_l2Wreath_eq_bot (n := k) hf (by omega)
  have hnormal : ((CFSG.solvableRadical (Halpha D hC.alpha)).map eH.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance eH.toMonoidHom eH.surjective
  have : Group.IsSolvable (CFSG.solvableRadical (Halpha D hC.alpha)) :=
    OddTransp.isSolvable_solvableRadical
  have hsol : Group.IsSolvable ((CFSG.solvableRadical (Halpha D hC.alpha)).map eH.toMonoidHom) :=
    Group.isSolvable_of_surjective (eH.toMonoidHom.subgroupMap_surjective _)
  have hle : (CFSG.solvableRadical (Halpha D hC.alpha)).map eH.toMonoidHom ≤ ⊥ := by
    rw [← hradL]
    exact OddTransp.le_solvableRadical hnormal hsol
  have hbot : CFSG.solvableRadical (Halpha D hC.alpha) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : eH x = 1 := by
      have hmem := hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      simpa using hmem
    rw [Subgroup.mem_bot]
    exact eH.injective (by rw [h1, map_one])
  rw [hbot]
  exact IsPGroup.of_bot

private theorem isPGroup_of_wreath_one (hC : HypothesisC D) {f : ℕ}
    (Φ : G ≃* L2Wreath f 1) :
    IsPGroup 2 (CFSG.solvableRadical (Halpha D hC.alpha)) := by
  obtain ⟨e⟩ := CFSG.OddTranspositions.PartFour.nonempty_mulEquiv_psl2Model_of_l2Wreath_one Φ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htd : orderOf (e hC.d) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hC.setup.oddT.1 hC.d hC.hd
  have hcent : IsPGroup 2 (Subgroup.centralizer ({e hC.d} : Set (PSL2Model f))) :=
    CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo htd
  have hHC : Halpha D hC.alpha ≤ Subgroup.centralizer ({hC.d} : Set G) :=
    Halpha_le_centralizer_d hC
  have hsub : (Halpha D hC.alpha).map e.toMonoidHom ≤
      Subgroup.centralizer ({e hC.d} : Set (PSL2Model f)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxc : Commute x hC.d := Subgroup.mem_centralizer_singleton_iff.mp (hHC hx)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hxc.map e).eq
  have hH2 : IsPGroup 2 (Halpha D hC.alpha) := by
    have h2 : IsPGroup 2 ((Halpha D hC.alpha).map e.toMonoidHom) := hcent.to_le hsub
    exact h2.of_equiv
      (Subgroup.equivMapOfInjective (Halpha D hC.alpha) e.toMonoidHom e.injective).symm
  exact hH2.to_subgroup (CFSG.solvableRadical (Halpha D hC.alpha))

omit [Finite G] in
private theorem false_of_wreath_zero (hC : HypothesisC D) {f : ℕ}
    (Φ : G ≃* L2Wreath f 0) : False := by
  have hodd : orderOf hC.d = 2 := hC.setup.oddT.1 hC.d hC.hd
  have h1 : hC.d = 1 := CFSG.OddTranspositions.PartFour.eq_one_of_mulEquiv_l2Wreath_zero Φ hC.d
  rw [h1, orderOf_one] at hodd
  omega

theorem isPGroup_solvableRadical_Halpha_of_mulEquiv_l2Wreath
    {G : Type} [Group G] [Finite G] {D : Set G}
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {f n : ℕ} (hf : 2 ≤ f) (Φ : G ≃* L2Wreath f n) :
    IsPGroup 2 (CFSG.solvableRadical (Halpha D hC.alpha)) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · exact (false_of_wreath_zero hC (hn0 ▸ Φ)).elim
  rcases (by omega : n = 1 ∨ 2 ≤ n) with hn1 | hn2
  · exact isPGroup_of_wreath_one hC (hn1 ▸ Φ)
  obtain ⟨f', n', hf', hn', a, b, hab, Ψ, hΨu, hΨD⟩ := exists_swap_class hC hrad hf hn2 Φ
  rcases (by omega : n' = 2 ∨ n' = 3 ∨ n' = 4 ∨ 5 ≤ n') with h2 | h3 | h4 | h5
  · subst h2
    have hs : swap a b = swap (0 : Fin 2) 1 := by
      have hall : ∀ x y : Fin 2, x ≠ y → swap x y = swap (0 : Fin 2) 1 := by decide
      exact hall a b hab
    rw [hs] at hΨu hΨD
    exact isPGroup_of_wreath_two hC hf' Ψ hΨu hΨD
  · exact absurd (Nine.disconnected_of_wreath_le_four (by omega) (by omega) hab Ψ hΨD) hC.conn
  · exact absurd (Nine.disconnected_of_wreath_le_four (by omega) (by omega) hab Ψ hΨD) hC.conn
  · exact isPGroup_of_wreath_five_le hC hf' h5 hab Ψ hΨD

end CFSG.OddTranspositions.PartThree.ElevenThree
