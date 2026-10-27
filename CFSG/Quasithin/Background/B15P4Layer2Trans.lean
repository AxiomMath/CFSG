module

public import CFSG.Quasithin.Background.B15P4Layer2Section
public import CFSG.Quasithin.Background.B15P4LayerQuad
public import CFSG.Quasithin.Background.B15P4Comp
public import CFSG.Quasithin.Background.B15P4Layer2Weight
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.Quasithin.B15P4

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Open
open scoped Multiplicative

universe v

section Orbit

variable {k : Type*} [Field k] {U : Type v} [AddCommGroup U] [Module k U]

theorem exists_orbit_family' [Finite U] {G A L : Subgroup (U ≃ₗ[k] U)}
    (hAG : A ≤ Subgroup.normalizer (G : Set (U ≃ₗ[k] U))) (hL : IsComponentIn L G)
    {a₀ : U ≃ₗ[k] U} (ha₀ : a₀ ∈ A) (hmove : conjSub a₀ L ≠ L) :
    ∃ (s : ℕ) (Lfam : Fin s → Subgroup (U ≃ₗ[k] U)), 2 ≤ s ∧ Function.Injective Lfam ∧
      (∀ i, IsComponentIn (Lfam i) G) ∧
      (∀ a ∈ A, ∀ i, ∃ j, conjSub a (Lfam i) = Lfam j) ∧
      (∀ i j, ∃ a ∈ A, conjSub a (Lfam i) = Lfam j) ∧
      (∀ i, ∃ a ∈ A, Lfam i = conjSub a L) ∧ (∀ a ∈ A, ∃ i, Lfam i = conjSub a L) := by
  classical
  have : Finite (U ≃ₗ[k] U) := finite_linearEquiv
  let O : Set (Subgroup (U ≃ₗ[k] U)) := {X | ∃ a ∈ A, X = conjSub a L}
  have hOfin : Finite ↥O := inferInstance
  obtain ⟨s, e₀⟩ : ∃ s, Nonempty (↥O ≃ Fin s) := ⟨Nat.card ↥O, ⟨Finite.equivFin ↥O⟩⟩
  let e := e₀.some
  let Lfam : Fin s → Subgroup (U ≃ₗ[k] U) := fun i => (e.symm i).1
  have hmem : ∀ i, ∃ b ∈ A, Lfam i = conjSub b L := fun i => (e.symm i).2
  have hconjO : ∀ a ∈ A, ∀ i, conjSub a (Lfam i) ∈ O := by
    intro a ha i
    obtain ⟨b, hb, hbi⟩ := hmem i
    exact ⟨a * b, A.mul_mem ha hb, by rw [hbi, conjSub_mul]⟩
  have hLO : L ∈ O := ⟨1, A.one_mem, (conjSub_one L).symm⟩
  have hLO' : conjSub a₀ L ∈ O := ⟨a₀, ha₀, rfl⟩
  have hs : 2 ≤ s := by
    have hnt : Nontrivial ↥O := ⟨⟨⟨L, hLO⟩, ⟨conjSub a₀ L, hLO'⟩, fun h => hmove.symm
      (congrArg Subtype.val h)⟩⟩
    have h1 : 1 < Nat.card ↥O := Finite.one_lt_card_iff_nontrivial.2 hnt
    have h2 : Nat.card ↥O = s := by
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  refine ⟨s, Lfam, hs, fun i j h => e.symm.injective (Subtype.ext h), fun i => ?_, ?_, ?_, hmem,
    fun a ha => ⟨e ⟨conjSub a L, a, ha, rfl⟩, ?_⟩⟩
  · obtain ⟨b, hb, hbi⟩ := hmem i
    rw [hbi]
    exact isComponentIn_conjSub hL (hAG hb)
  · intro a ha i
    refine ⟨e ⟨_, hconjO a ha i⟩, ?_⟩
    show conjSub a (Lfam i) = (e.symm (e ⟨_, hconjO a ha i⟩)).1
    rw [Equiv.symm_apply_apply]
  · intro i j
    obtain ⟨b, hb, hbi⟩ := hmem i
    obtain ⟨c, hc, hcj⟩ := hmem j
    refine ⟨c * b⁻¹, A.mul_mem hc (A.inv_mem hb), ?_⟩
    rw [hbi, hcj, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]
  · show (e.symm (e ⟨conjSub a L, a, ha, rfl⟩)).1 = conjSub a L
    rw [Equiv.symm_apply_apply]

end Orbit

section Dict

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

theorem binPsi_apply_toAdd (x : MulAut V) (v : V) :
    binPsi θ x (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ (x v)) := by
  rw [binPsi_apply]
  simp

theorem commGL_map_eq_top {X : Subgroup (MulAut V)} (h : commV X = ⊤) :
    commGL (X.map (binPsi θ).toMonoidHom) ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hv : θ.symm (Multiplicative.ofAdd w) ∈ commV X := h ▸ Subgroup.mem_top _
  have key : ∀ v ∈ commV X,
      Multiplicative.toAdd (θ v) ∈ commGL (X.map (binPsi θ).toMonoidHom) ⊤ := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨x, hx, v', rfl⟩ := hy
      refine Submodule.subset_span ⟨binPsi θ x, ⟨x, hx, rfl⟩, Multiplicative.toAdd (θ v'),
        Submodule.mem_top, ?_⟩
      show Multiplicative.toAdd (θ (x v' * v'⁻¹)) =
        binPsi θ x (Multiplicative.toAdd (θ v')) - Multiplicative.toAdd (θ v')
      rw [binPsi_apply_toAdd, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul, toAdd_mul]
      exact Submodule.add_mem _ hx hy
    | inv x _ hx =>
      rw [map_inv, toAdd_inv]
      exact Submodule.neg_mem _ hx
  have := key _ hv
  simpa using this

theorem isIrrQuot_map_top {X : Subgroup (MulAut V)}
    (h : (⊤ : Subgroup V) ∈ IrrPlus X (⊤ : Subgroup V)) :
    IsIrrQuot (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (X.map (binPsi θ).toMonoidHom) ⊤ := by
  obtain ⟨-, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 h
  refine ⟨?_, ?_⟩
  · intro hle
    apply hlt.ne
    rw [top_inf_eq]
    rw [eq_top_iff]
    intro v _ x hx
    have h1 := hle (Submodule.mem_top (x := Multiplicative.toAdd (θ v)))
    have := (mem_fixGL_map θ X v).1 h1
    exact this x hx
  · intro U hUinv hfix _
    let J : Subgroup V :=
      { carrier := {v | Multiplicative.toAdd (θ v) ∈ U}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          show Multiplicative.toAdd (θ (a * b)) ∈ U
          rw [map_mul, toAdd_mul]
          exact U.add_mem ha hb
        inv_mem' := fun {a} ha => by
          show Multiplicative.toAdd (θ a⁻¹) ∈ U
          rw [map_inv, toAdd_inv]
          exact U.neg_mem ha }
    have hJinv : ∀ x ∈ X, ∀ w ∈ J, x w ∈ J := by
      intro x hx w hw
      show Multiplicative.toAdd (θ (x w)) ∈ U
      rw [← binPsi_apply_toAdd]
      exact hUinv (binPsi θ x) ⟨x, hx, rfl⟩ _ hw
    have hJfix : (⊤ : Subgroup V) ⊓ fixV X ≤ J := by
      intro v hv
      have := (mem_fixGL_map θ X v).2 hv.2
      rw [top_inf_eq] at hfix
      exact hfix this
    have hmemJ : ∀ w : W, w ∈ U ↔ θ.symm (Multiplicative.ofAdd w) ∈ J := by
      intro w
      show w ∈ U ↔ Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U
      simp
    have hfixiff : ∀ w : W, w ∈ fixGL (X.map (binPsi θ).toMonoidHom) ↔
        θ.symm (Multiplicative.ofAdd w) ∈ fixV X := by
      intro w
      have := mem_fixGL_map θ X (θ.symm (Multiplicative.ofAdd w))
      simpa using this
    rcases hirr J hJinv hJfix le_top with hJ | hJ
    · left
      ext w
      rw [Submodule.mem_inf, hmemJ, hJ, Subgroup.mem_inf]
      show _ ↔ w ∈ (⊤ : Submodule (ZMod 2) W) ∧ w ∈ fixGL (X.map (binPsi θ).toMonoidHom)
      rw [hfixiff]
      simp
    · right
      rw [eq_top_iff]
      intro w _
      rw [hmemJ, hJ]
      exact Subgroup.mem_top _

theorem conjSub_eq_conjAut (a : MulAut V) (K : Subgroup (MulAut V)) :
    conjSub a K = B1.conjAut a K :=
  (conjAut_eq_map a K).symm

theorem map_conjSub (a : MulAut V) (K : Subgroup (MulAut V)) :
    (conjSub a K).map (binPsi θ).toMonoidHom =
      conjSub (binPsi θ a) (K.map (binPsi θ).toMonoidHom) :=
  map_map_conj (binPsi θ) K a

end Dict

section Main

theorem false_of_top_irr {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G A K : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) (hK : IsComponentOf K G)
    {a₀ : MulAut V} (ha₀ : a₀ ∈ A) (hn : a₀ ∉ Subgroup.normalizer (K : Set (MulAut V)))
    (hcomm : commV (Kspan A K) = ⊤)
    (hirr : (⊤ : Subgroup V) ∈ IrrPlus (Kspan A K) (⊤ : Subgroup V)) (hB : A2sub A ≠ ⊥) :
    False := by
  classical
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (V := V) fun v => by
    rw [← pow_two]
    exact hV v
  have hinj := (binPsi θ).injective
  have hinjM : Function.Injective (binPsi θ).toMonoidHom := hinj
  have hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.2.2.1.1
  have hA2 : IsFFStarOffender G (A2sub A) := isFFStarOffender_A2sub hA hB
  have hnorm : A2sub A ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    normalizes_of_isQuadratic hV hA2 (isQuadratic_A2sub hc) hK
  have hel : CFSG.IsElementaryAbelian 2 ↥(A.map (binPsi θ).toMonoidHom) :=
    (isElemAbelian2_iff_map θ A).1 hA.2.2.1
  have hAG' : A.map (binPsi θ).toMonoidHom ≤
      Subgroup.normalizer ((G.map (binPsi θ).toMonoidHom : Subgroup (W ≃ₗ[ZMod 2] W)) :
        Set (W ≃ₗ[ZMod 2] W)) :=
    (Subgroup.map_mono hA.1).trans Subgroup.le_normalizer
  have hK' : IsComponentIn (K.map (binPsi θ).toMonoidHom) (G.map (binPsi θ).toMonoidHom) :=
    (isComponentIn_map_iff (binPsi θ)).2 ((isComp_iff K G).1 hK)
  have hmove : conjSub (binPsi θ a₀) (K.map (binPsi θ).toMonoidHom) ≠
      K.map (binPsi θ).toMonoidHom := by
    intro h
    apply hn
    have h2 : conjSub a₀ K = K := by
      apply Subgroup.map_injective hinjM
      rw [map_conjSub θ a₀ K]
      exact h
    exact mem_normalizer_iff_conjAut.2 (by rw [conjAut_eq_map]; exact h2)
  obtain ⟨s, L, hs, hinjL, hcompL, hperm, htrans, hLK, hKL⟩ :=
    exists_orbit_family' hAG' hK' (a₀ := binPsi θ a₀) ⟨a₀, ha₀, rfl⟩ hmove
  have hq : ∀ i, CFSG.IsQuasisimple ↥(L i) := fun i => isQuasisimple_of_isComponentIn (hcompL i)
  have hcommL : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥ := fun i j hij =>
    commutator_eq_bot_of_isComponentIn_ne (hcompL i) (hcompL j) (fun h => hij (hinjL h))
  have hH : ⨆ i, L i = (Kspan A K).map (binPsi θ).toMonoidHom := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      obtain ⟨a', ⟨a, ha, rfl⟩, hLi⟩ := hLK i
      have hLi' : L i = (conjSub a K).map (binPsi θ).toMonoidHom :=
        hLi.trans (map_conjSub θ a K).symm
      rw [hLi', conjSub_eq_conjAut]
      exact Subgroup.map_mono (conjAut_le_Kspan ha)
    · rw [Subgroup.map_le_iff_le_comap]
      refine Kspan_le_iff.2 fun a ha x hx => ?_
      obtain ⟨i, hi⟩ := hKL ((binPsi θ).toMonoidHom a) ⟨a, ha, rfl⟩
      have hi' : L i = (conjSub a K).map (binPsi θ).toMonoidHom :=
        hi.trans (map_conjSub θ a K).symm
      have hx' : x ∈ conjSub a K := by
        rw [conjSub_eq_conjAut]
        exact hx
      have : (binPsi θ) x ∈ L i := by
        rw [hi']
        exact ⟨x, hx', rfl⟩
      exact le_iSup L i this
  have hcommV : commGL (⨆ i, L i) ⊤ = ⊤ := by
    rw [hH]
    exact commGL_map_eq_top θ hcomm
  have hirrW : IsIrrQuot (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (⨆ i, L i) ⊤ := by
    rw [hH]
    exact isIrrQuot_map_top θ hirr
  have hBA : (A2sub A).map (binPsi θ).toMonoidHom ≤ A.map (binPsi θ).toMonoidHom :=
    Subgroup.map_mono (A2sub_le A)
  have hB0 : (A2sub A).map (binPsi θ).toMonoidHom ≠ ⊥ := fun h =>
    hB ((Subgroup.map_eq_bot_iff_of_injective (A2sub A) hinj).1 h)
  have hBfix : ∀ b ∈ (A2sub A).map (binPsi θ).toMonoidHom, ∀ i, conjSub b (L i) = L i := by
    intro b hb i
    obtain ⟨b₁, hb₁, rfl⟩ := hb
    obtain ⟨a', ⟨a, ha, rfl⟩, hLi⟩ := hLK i
    have hb₁K : conjSub b₁ K = K := conjSub_eq_self (hnorm hb₁)
    have hψb : conjSub (binPsi θ b₁) (K.map (binPsi θ).toMonoidHom) =
        K.map (binPsi θ).toMonoidHom := by
      rw [← map_conjSub θ b₁ K, hb₁K]
    have hab : binPsi θ b₁ * binPsi θ a = binPsi θ a * binPsi θ b₁ := by
      rw [← map_mul, ← map_mul, hc b₁ (A2sub_le A hb₁) a ha]
    show conjSub (binPsi θ b₁) (L i) = L i
    rw [hLi]
    show conjSub (binPsi θ b₁) (conjSub (binPsi θ a) (K.map (binPsi θ).toMonoidHom)) = _
    rw [← conjSub_mul, hab, conjSub_mul, hψb]
    rfl
  have hBq : ∀ a ∈ A.map (binPsi θ).toMonoidHom, ∀ b ∈ (A2sub A).map (binPsi θ).toMonoidHom,
      ∀ w, b (a w - w) = a w - w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
    obtain ⟨v, rfl⟩ : ∃ v, w = Multiplicative.toAdd (θ v) :=
      ⟨θ.symm (Multiplicative.ofAdd w), by simp⟩
    have h1 : binPsi θ a (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v) =
        Multiplicative.toAdd (θ (a v * v⁻¹)) := by
      rw [binPsi_apply_toAdd, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    show binPsi θ b (binPsi θ a (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v)) =
      binPsi θ a (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v)
    rw [h1, binPsi_apply_toAdd, A2sub_fix_comm hc hb ha v]
  have hmaxB : ∀ D : Subgroup (W ≃ₗ[ZMod 2] W), D ≤ (A2sub A).map (binPsi θ).toMonoidHom →
      weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) D ≤
        weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((A2sub A).map (binPsi θ).toMonoidHom) := by
    intro D hD
    obtain ⟨D₀, hD₀, rfl⟩ := exists_le_map_eq θ hD
    rw [weight_map θ D₀, weight_map θ (A2sub A)]
    have h1 := wt_le_of_isFFStarOffender hA (hD₀.trans (A2sub_le A))
    have h2 := wt_A2sub hA
    exact h1.trans h2.symm.le
  have := hel
  exact false_of_irreducible_diag hs L hinjL hq hcommL (A.map (binPsi θ).toMonoidHom) hperm
    htrans hcommV hirrW ((A2sub A).map (binPsi θ).toMonoidHom) hBA hB0 hBfix hBq hmaxB

end Main

end CFSG.Quasithin.B15P4
