module

public import CFSG.Milestones.ASVolI.G4
public import CFSG.Blueprint.SourceBinaryGolayCode
import CFSG.Quasithin.Background.RonanG72Sporadic
import CFSG.Quasithin.Background.RonanG73Spor
import CFSG.Quasithin.Background.RonanG73Odd
import CFSG.Quasithin.Background.RonanG73Alt7

public section

namespace CFSG.ASVolI.ChG

@[expose] def IsHyperplaneOf {A : Type*} [Group A] (p : ℕ) (P H : Subgroup A) : Prop :=
  H ≤ P ∧ H.relIndex P = p

@[expose] noncomputable def orbitLen {A : Type*} [Group A] (N H : Subgroup A) : ℕ :=
  Set.ncard {K : Subgroup A | ∃ g ∈ N, K = H.map (MulAut.conj g).toMonoidHom}

@[expose] def IsHeisenberg (p : ℕ) {A : Type*} [Group A] (P : Subgroup A) : Prop :=
  Nat.card P = p ^ 3 ∧ Monoid.exponent P = p ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a

@[expose] def IsLieTypeOddChar (X : Type) [Group X] : Prop :=
  ∃ (t : CFSG.Open.StatedLieTag) (n p f : ℕ), p ≠ 2 ∧
    (CFSG.Open.StatedClassicalModel X t n p f ∨ CFSG.Blueprint.ChevalleyExceptionalModel X t p f ∨
      CFSG.Blueprint.ReeTitsModel X t p f)

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11

abbrev GolayAmbient := Fin 24 → ZMod 2

@[expose] def golayConstantLine : Submodule (ZMod 2) GolayAmbient :=
  Submodule.span (ZMod 2) {fun _ : Fin 24 => (1 : ZMod 2)}

@[expose] def golayPairLine (first second : Fin 24) : Submodule (ZMod 2) GolayAmbient :=
  Submodule.span (ZMod 2) {fun coordinate : Fin 24 =>
    (if coordinate = first then 1 else 0) + (if coordinate = second then 1 else 0)}

@[expose] def golayPairKernel (first second : Fin 24) : Submodule (ZMod 2) GolayAmbient where
  carrier := {word | word first = word second}
  zero_mem' := rfl
  add_mem' := by
    intro left right left_mem right_mem
    change left first = left second at left_mem
    change right first = right second at right_mem
    change left first + right first = left second + right second
    rw [left_mem, right_mem]
  smul_mem' := by
    intro scalar word word_mem
    change word first = word second at word_mem
    change scalar • word first = scalar • word second
    rw [word_mem]

@[expose] def IsGolaySectionModule {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) {Model : Type} [Group Model]
    (small : Bool) (numerator denominator : Submodule (ZMod 2) GolayAmbient) : Prop :=
  ∃ (marking : ↥H ≃* Model) (action : Model →* Equiv.Perm (Fin 24)),
    Function.Injective action ∧
    (∀ permutation : Equiv.Perm (Fin 24),
      (∃ model : Model, action model = permutation) ↔
        (∀ word : GolayAmbient,
          word ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
            permAct permutation word ∈ CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
        (small = true → permutation 0 = 0 ∧ permutation 1 = 1)) ∧
    denominator ≤ numerator ∧
    (∀ (element : ↥H) (word : ↥numerator),
      permAct (action (marking element)) (word : GolayAmbient) ∈ numerator) ∧
    ∃ quotientMap : ↥numerator →ₗ[ZMod 2] V,
      Function.Surjective quotientMap ∧
      (∀ word : ↥numerator, quotientMap word = 0 ↔ (word : GolayAmbient) ∈ denominator) ∧
      ∀ (element : ↥H) (word image : ↥numerator),
        (image : GolayAmbient) = permAct (action (marking element)) (word : GolayAmbient) →
          quotientMap image = (element : GLV V) (quotientMap word)

@[expose] def IsMathieu24CodeOrCocode {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) : Prop :=
  IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M24) H false
      CFSG.Blueprint.EvenSource.sourceGolayCode golayConstantLine ∨
    IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M24) H false
      (permCore 24) CFSG.Blueprint.EvenSource.sourceGolayCode

@[expose] def IsMathieu22CodeOrCocode {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) : Prop :=
  IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M22) H true
      (CFSG.Blueprint.EvenSource.sourceGolayCode ⊓ golayPairKernel 0 1) golayConstantLine ∨
    IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M22) H true
      (permCore 24) (CFSG.Blueprint.EvenSource.sourceGolayCode ⊔ golayPairLine 0 1)

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

@[expose] def G_7_1 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G : Subgroup (GLV V)) (d : ℕ),
    Module.finrank (ZMod 2) V = d →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (GLV V), P ≤ G → IsPGroup p P →
      (Nat.card P = p → orderOf (2 : ZMod p) ≤ d) ∧
      (IsHeisenberg p P → p * orderOf (2 : ZMod p) ≤ d) ∧
      (IsElemAbelian p P → ∀ n : ℕ,
        IsLeast {k | ∃ H, IsHyperplaneOf p P H ∧ k = orbitLen (G ⊓ Subgroup.normalizer (P : Set (GLV V))) H} n →
        n * orderOf (2 : ZMod p) ≤ d ∧
          (d = n * orderOf (2 : ZMod p) → ∀ H, IsHyperplaneOf p P H →
            (∃ v : V, v ≠ 0 ∧ ∀ h ∈ H, h v = v) →
            Nat.card ↥(fixedSpace H) = 2 ^ orderOf (2 : ZMod p)))

section G71Aux

open scoped Classical

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private lemma g71_odd_nsmul {n : ℕ} (hn : Odd n) (v : V) : n • v = v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2) n v, (ZMod.natCast_eq_one_iff_odd).mpr hn, one_smul]

private instance g71_finite_glv : Finite (GLV V) :=
  Finite.of_injective (fun e : GLV V => (e : V → V))
    fun _ _ h => LinearEquiv.ext fun x => congrFun h x

private noncomputable instance g71_fintype_glv : Fintype (GLV V) := Fintype.ofFinite _

private instance g71_finite_subgroup : Finite (Subgroup (GLV V)) :=
  Finite.of_injective (fun H : Subgroup (GLV V) => (H : Set (GLV V))) SetLike.coe_injective

private instance g71_finite_submodule : Finite (Submodule (ZMod 2) V) :=
  Finite.of_injective (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective

private noncomputable def g71Sum (H : Subgroup (GLV V)) : V →ₗ[ZMod 2] V :=
  ∑ h : H, (h : GLV V).toLinearMap

private noncomputable def g71X (A K : Subgroup (GLV V)) : Submodule (ZMod 2) V :=
  fixedSpace K ⊓ LinearMap.ker (g71Sum A)

private lemma g71Sum_apply (H : Subgroup (GLV V)) (v : V) :
    g71Sum H v = ∑ h : H, (h : GLV V) v := by
  simp [g71Sum, LinearMap.sum_apply]

private lemma g71Sum_left (H : Subgroup (GLV V)) {k : GLV V} (hk : k ∈ H) (v : V) :
    k (g71Sum H v) = g71Sum H v := by
  rw [g71Sum_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨k, hk⟩ : H)) _ _ fun h => rfl

private lemma g71Sum_right (H : Subgroup (GLV V)) {k : GLV V} (hk : k ∈ H) (v : V) :
    g71Sum H (k v) = g71Sum H v := by
  rw [g71Sum_apply H (k v), g71Sum_apply H v]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨k, hk⟩ : H)) _ _ fun h => rfl

private lemma g71Sum_fixed {H : Subgroup (GLV V)} {v : V} (hv : ∀ h ∈ H, h v = v) :
    g71Sum H v = Nat.card H • v := by
  have h' : ∀ h : H, (h : GLV V) v = v := fun h => hv _ h.2
  rw [g71Sum_apply]
  simp only [h', Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

private lemma g71Sum_fixed_odd {H : Subgroup (GLV V)} (hH : Odd (Nat.card H)) {v : V}
    (hv : ∀ h ∈ H, h v = v) : g71Sum H v = v := by
  rw [g71Sum_fixed hv, g71_odd_nsmul hH]

private lemma g71Sum_sum_sub {A K : Subgroup (GLV V)} (hKA : K ≤ A) (hK : Odd (Nat.card K))
    (x : V) : g71Sum A (g71Sum K x) = g71Sum A x := by
  calc g71Sum A (g71Sum K x) = ∑ h : K, g71Sum A ((h : GLV V) x) := by
        rw [g71Sum_apply K x, map_sum]
    _ = ∑ _h : K, g71Sum A x := Finset.sum_congr rfl fun h _ => g71Sum_right A (hKA h.2) x
    _ = Nat.card K • g71Sum A x := by
        simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    _ = g71Sum A x := g71_odd_nsmul hK _

private lemma g71_sum_eq_of_sup {A K L : Subgroup (GLV V)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ≤ A) (hLA : L ≤ A) (hsup : K ⊔ L = A)
    (hodd : Odd (Nat.card A)) {v : V} (hv : ∀ l ∈ L, l v = v) :
    g71Sum K v = g71Sum A v := by
  have hKodd : Odd (Nat.card K) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hKA)
  have hwK : ∀ k ∈ K, k (g71Sum K v) = g71Sum K v := fun k hk => g71Sum_left K hk v
  have hwL : ∀ l ∈ L, l (g71Sum K v) = g71Sum K v := by
    intro l hl
    calc l (g71Sum K v) = ∑ h : K, l ((h : GLV V) v) := by rw [g71Sum_apply, map_sum]
      _ = ∑ h : K, (h : GLV V) v := by
        refine Finset.sum_congr rfl fun h _ => ?_
        have hc : l * (h : GLV V) = (h : GLV V) * l := hA l (hLA hl) _ (hKA h.2)
        calc l ((h : GLV V) v) = ((l * (h : GLV V) : GLV V)) v := rfl
          _ = (((h : GLV V) * l : GLV V)) v := by rw [hc]
          _ = (h : GLV V) v := by
            rw [show ((h : GLV V) * l : GLV V) v = (h : GLV V) (l v) from rfl, hv l hl]
      _ = g71Sum K v := (g71Sum_apply K v).symm
  have hwA : ∀ a ∈ A, a (g71Sum K v) = g71Sum K v := by
    have hle : A ≤ MulAction.stabilizer (GLV V) (g71Sum K v) := by
      rw [← hsup]
      refine sup_le (fun k hk => ?_) (fun l hl => ?_)
      · exact MulAction.mem_stabilizer_iff.mpr (hwK k hk)
      · exact MulAction.mem_stabilizer_iff.mpr (hwL l hl)
    exact fun a ha => MulAction.mem_stabilizer_iff.mp (hle ha)
  have h1 : g71Sum A (g71Sum K v) = g71Sum K v := g71Sum_fixed_odd hodd hwA
  rw [g71Sum_sum_sub hKA hKodd v] at h1
  exact h1.symm

private lemma mem_g71X {A K : Subgroup (GLV V)} {x : V} :
    x ∈ g71X A K ↔ (∀ k ∈ K, k x = x) ∧ g71Sum A x = 0 := by
  unfold g71X
  rw [Submodule.mem_inf, LinearMap.mem_ker]
  exact Iff.rfl

private lemma g71_maxsub {p : ℕ} (hp : p.Prime) {A K M : Subgroup (GLV V)}
    (hK : K.relIndex A = p) (hKM : K ≤ M) (hMA : M ≤ A) (hne : M ≠ K) : M = A := by
  have h1 := Subgroup.relIndex_mul_relIndex K M A hKM hMA
  have hne1 : K.relIndex M ≠ 1 := fun h => hne (le_antisymm (Subgroup.relIndex_eq_one.mp h) hKM)
  have hdvd : K.relIndex M ∣ p := ⟨M.relIndex A, by rw [← hK, ← h1]⟩
  have hKMp : K.relIndex M = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  rw [hKMp, hK] at h1
  have h2 : M.relIndex A = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact h1)
  exact le_antisymm hMA (Subgroup.relIndex_eq_one.mp h2)

private lemma g71_hyp_eq {p : ℕ} (hp : p.Prime) {A K L : Subgroup (GLV V)}
    (hK : K.relIndex A = p) (hL : L.relIndex A = p) (hKA : K ≤ A) (hLK : L ≤ K) : L = K := by
  have h1 := Subgroup.relIndex_mul_relIndex L K A hLK hKA
  rw [hK, hL] at h1
  have h2 : L.relIndex K = 1 := Nat.eq_of_mul_eq_mul_right hp.pos (by rw [one_mul]; exact h1)
  exact le_antisymm hLK (Subgroup.relIndex_eq_one.mp h2)

private lemma g71_hyp_sup {p : ℕ} (hp : p.Prime) {A K K' : Subgroup (GLV V)}
    (hK' : K'.relIndex A = p) (hK : K.relIndex A = p) (hK'A : K' ≤ A) (hKA : K ≤ A)
    (hne : K ≠ K') : K' ⊔ K = A := by
  refine g71_maxsub hp hK' le_sup_left (sup_le hK'A hKA) fun h => hne ?_
  have hKK' : K ≤ K' := by
    have hm : K ≤ K' ⊔ K := le_sup_right
    rwa [h] at hm
  exact g71_hyp_eq hp hK' hK hK'A hKK'

private lemma g71_ind {p : ℕ} (hp : p.Prime) {A : Subgroup (GLV V)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAodd : Odd (Nat.card A)) :
    ∀ T : Finset (Subgroup (GLV V)), (∀ K ∈ T, K ≤ A ∧ K.relIndex A = p) →
      Module.finrank (ZMod 2) (fixedSpace A) + ∑ K ∈ T, Module.finrank (ZMod 2) (g71X A K) =
        Module.finrank (ZMod 2) ((fixedSpace A ⊔ T.sup (g71X A) : Submodule (ZMod 2) V)) := by
  intro T
  refine Finset.induction_on T
    (fun _ => by rw [Finset.sum_empty, Finset.sup_empty, sup_bot_eq, add_zero]) ?_
  intro K' T hK'T ih hT
  have hK'A : K' ≤ A ∧ K'.relIndex A = p := hT K' (Finset.mem_insert_self _ _)
  have ih' := ih fun K hK => hT K (Finset.mem_insert_of_mem hK)
  have hK'odd : Odd (Nat.card K') := hAodd.of_dvd_nat (Subgroup.card_dvd_of_le hK'A.1)
  have hN : fixedSpace A ⊔ T.sup (g71X A) ≤ LinearMap.ker (g71Sum K' - g71Sum A) := by
    refine sup_le (fun c hc => ?_) (Finset.sup_le fun K hK => ?_)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      have hcA : ∀ a ∈ A, a c = c := fun a ha => hc a ha
      rw [g71Sum_fixed_odd hK'odd (fun h hh => hcA h (hK'A.1 hh)), g71Sum_fixed_odd hAodd hcA]
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      have hKA := hT K (Finset.mem_insert_of_mem hK)
      have hne : K ≠ K' := fun h => hK'T (h ▸ hK)
      have hsup := g71_hyp_sup hp hK'A.2 hKA.2 hK'A.1 hKA.1 hne
      have hx' := mem_g71X.mp hx
      exact g71_sum_eq_of_sup hA hK'A.1 hKA.1 hsup hAodd hx'.1
  have hinf : g71X A K' ⊓ (fixedSpace A ⊔ T.sup (g71X A)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyX, hyY⟩ := Submodule.mem_inf.mp hy
    have hy1 := hN hyY
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hy1
    have hyX' := mem_g71X.mp hyX
    rw [g71Sum_fixed_odd hK'odd hyX'.1, hyX'.2] at hy1
    exact (Submodule.mem_bot _).mpr hy1
  rw [Finset.sum_insert hK'T, Finset.sup_insert]
  have hcomm : fixedSpace A ⊔ (g71X A K' ⊔ T.sup (g71X A)) =
      g71X A K' ⊔ (fixedSpace A ⊔ T.sup (g71X A)) := sup_left_comm _ _ _
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (g71X A K') (fixedSpace A ⊔ T.sup (g71X A))
  rw [hinf, finrank_bot, add_zero] at hfin
  rw [hcomm, hfin, ← ih']
  omega

private lemma g71_ind_le {p : ℕ} (hp : p.Prime) {A : Subgroup (GLV V)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAodd : Odd (Nat.card A))
    (T : Finset (Subgroup (GLV V))) (hT : ∀ K ∈ T, K ≤ A ∧ K.relIndex A = p) :
    Module.finrank (ZMod 2) (fixedSpace A) + ∑ K ∈ T, Module.finrank (ZMod 2) (g71X A K) ≤
      Module.finrank (ZMod 2) V := by
  rw [g71_ind hp hA hAodd T hT]
  exact Submodule.finrank_le _

private lemma g71_orbit_dvd {p : ℕ} (hp : p.Prime) (W : Type) [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (c : W ≃ₗ[ZMod 2] W) (hc : c ^ p = 1)
    (hfix : ∀ w, c w = w → w = 0) :
    orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) W := by
  haveI := Fact.mk hp
  have hP : IsPGroup p (Subgroup.zpowers c) := by
    rintro ⟨x, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change ((fun n : ℤ => c ^ n) k) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  have hcong := hP.card_modEq_card_fixedPoints (α := W)
  have hfixset : MulAction.fixedPoints (Subgroup.zpowers c) W = ({0} : Set W) := by
    ext w
    constructor
    · intro hw
      exact Set.mem_singleton_iff.mpr (hfix w (hw ⟨c, Subgroup.mem_zpowers c⟩))
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact MulAction.mem_fixedPoints.mpr fun m => map_zero (m : W ≃ₗ[ZMod 2] W)
  rw [hfixset, Nat.card_coe_set_eq, Set.ncard_singleton,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod] at hcong
  have hpow : (2 : ZMod p) ^ Module.finrank (ZMod 2) W = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcong
    push_cast at h
    exact h
  exact orderOf_dvd_of_pow_eq_one hpow

private lemma g71_ord_le {p : ℕ} (hp : p.Prime) {A K : Subgroup (GLV V)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAexp : ∀ a ∈ A, a ^ p = 1)
    (hAodd : Odd (Nat.card A)) (hKA : K ≤ A) (hK : K.relIndex A = p) (hX : g71X A K ≠ ⊥) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (g71X A K) := by
  haveI := Fact.mk hp
  obtain ⟨g, hgA, hgK⟩ : ∃ g ∈ A, g ∉ K := by
    by_contra hcon
    push Not at hcon
    have hKA' : K = A := le_antisymm hKA fun g hg => hcon g hg
    rw [hKA', Subgroup.relIndex_self] at hK
    have := hp.one_lt
    omega
  have hMA : K ⊔ Subgroup.zpowers g = A := by
    refine g71_maxsub hp hK le_sup_left (sup_le hKA (Subgroup.zpowers_le.mpr hgA))
      fun h => hgK ?_
    have hm : g ∈ K ⊔ Subgroup.zpowers g :=
      (le_sup_right : Subgroup.zpowers g ≤ K ⊔ Subgroup.zpowers g) (Subgroup.mem_zpowers g)
    rwa [h] at hm
  have hcommg : ∀ k ∈ K, k * g = g * k := fun k hk => hA k (hKA hk) g hgA
  have hginvA : g⁻¹ ∈ A := A.inv_mem hgA
  have hinv : ∀ w ∈ g71X A K, g w ∈ g71X A K := by
    intro w hw
    obtain ⟨h1, h2⟩ := mem_g71X.mp hw
    refine mem_g71X.mpr ⟨fun k hk => ?_, ?_⟩
    · calc k (g w) = (k * g) w := rfl
        _ = (g * k) w := by rw [hcommg k hk]
        _ = g (k w) := rfl
        _ = g w := by rw [h1 k hk]
    · rw [g71Sum_right A hgA w, h2]
  have hinv' : ∀ w ∈ g71X A K, g⁻¹ w ∈ g71X A K := by
    intro w hw
    obtain ⟨h1, h2⟩ := mem_g71X.mp hw
    refine mem_g71X.mpr ⟨fun k hk => ?_, ?_⟩
    · have hc : k * g⁻¹ = g⁻¹ * k := hA k (hKA hk) g⁻¹ hginvA
      calc k (g⁻¹ w) = (k * g⁻¹) w := rfl
        _ = (g⁻¹ * k) w := by rw [hc]
        _ = g⁻¹ (k w) := rfl
        _ = g⁻¹ w := by rw [h1 k hk]
    · rw [g71Sum_right A hginvA w, h2]
  have hmap : (g71X A K).map ((g : GLV V) : V →ₗ[ZMod 2] V) = g71X A K := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hinv w hw
    · intro w hw
      exact ⟨g⁻¹ w, hinv' w hw, by simp⟩
  let e : g71X A K ≃ₗ[ZMod 2] g71X A K := LinearEquiv.ofSubmodules (g : GLV V) _ _ hmap
  have he : ∀ w : g71X A K, ((e w : g71X A K) : V) = g w := fun w => rfl
  have hpowe : ∀ n : ℕ, ∀ w : g71X A K, (((e ^ n) w : g71X A K) : V) = (g ^ n) (w : V) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, he, ih]
  have hep : e ^ p = 1 := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hpowe p w, hAexp g hgA]
    rfl
  have hfixe : ∀ w : g71X A K, e w = w → w = 0 := by
    intro w hw
    have hgw : g (w : V) = (w : V) := by
      have := congrArg Subtype.val hw
      rw [he] at this
      exact this
    have hwK : ∀ k ∈ K, k (w : V) = w := (mem_g71X.mp w.2).1
    have hAfix : ∀ a ∈ A, a (w : V) = w := by
      have hle : K ⊔ Subgroup.zpowers g ≤ MulAction.stabilizer (GLV V) (w : V) := by
        refine sup_le (fun k hk => MulAction.mem_stabilizer_iff.mpr (hwK k hk)) ?_
        exact Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hgw)
      rw [hMA] at hle
      exact fun a ha => MulAction.mem_stabilizer_iff.mp (hle ha)
    have hsumw : g71Sum A (w : V) = w := g71Sum_fixed_odd hAodd hAfix
    have hsum0 : g71Sum A (w : V) = 0 := (mem_g71X.mp w.2).2
    apply Subtype.ext
    calc (w : V) = g71Sum A (w : V) := hsumw.symm
      _ = 0 := hsum0
      _ = ((0 : g71X A K) : V) := rfl
  have hdvd := g71_orbit_dvd hp (g71X A K) e hep hfixe
  have hpos : 0 < Module.finrank (ZMod 2) (g71X A K) := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) (g71X A K)) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hX
    · exact h
  exact Nat.le_of_dvd hpos hdvd

private lemma g71_sum_conj {A : Subgroup (GLV V)} {g : GLV V}
    (hgN : g ∈ Subgroup.normalizer (A : Set (GLV V))) (x : V) :
    g (g71Sum A x) = g71Sum A (g x) := by
  have hg : ∀ h : GLV V, h ∈ A ↔ g * h * g⁻¹ ∈ A := fun h =>
    Subgroup.mem_set_normalizer_iff.mp hgN h
  have hmem : ∀ a : A, g * (a : GLV V) * g⁻¹ ∈ A := fun a => (hg _).mp a.2
  have hbij : Function.Bijective (fun a : A => (⟨g * (a : GLV V) * g⁻¹, hmem a⟩ : A)) := by
    constructor
    · intro a b h
      apply Subtype.ext
      exact (MulAut.conj g).injective (congrArg Subtype.val h)
    · intro b
      have hb : g⁻¹ * (b : GLV V) * g ∈ A := (hg _).mpr (by simpa [mul_assoc] using b.2)
      exact ⟨⟨g⁻¹ * (b : GLV V) * g, hb⟩, Subtype.ext (by simp [mul_assoc])⟩
  rw [g71Sum_apply A x, g71Sum_apply A (g x), map_sum]
  refine Fintype.sum_bijective _ hbij _ _ fun a => ?_
  show g ((a : GLV V) x) = (g * (a : GLV V) * g⁻¹) (g x)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp

private lemma g71_map_conj_self {A : Subgroup (GLV V)} {g : GLV V}
    (hgN : g ∈ Subgroup.normalizer (A : Set (GLV V))) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  have hg : ∀ h : GLV V, h ∈ A ↔ g * h * g⁻¹ ∈ A := fun h =>
    Subgroup.mem_set_normalizer_iff.mp hgN h
  have hginvN : g⁻¹ ∈ Subgroup.normalizer (A : Set (GLV V)) := Subgroup.inv_mem _ hgN
  have hg' : ∀ h : GLV V, h ∈ A ↔ g⁻¹ * h * g⁻¹⁻¹ ∈ A := fun h =>
    Subgroup.mem_set_normalizer_iff.mp hginvN h
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact (hg a).mp ha
  · intro a ha
    refine ⟨g⁻¹ * a * g⁻¹⁻¹, (hg' a).mp ha, ?_⟩
    show g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a
    group

private lemma g71_conj_hyp {p : ℕ} {A K : Subgroup (GLV V)} {g : GLV V}
    (hgN : g ∈ Subgroup.normalizer (A : Set (GLV V))) (hKA : K ≤ A) (hK : K.relIndex A = p) :
    K.map (MulAut.conj g).toMonoidHom ≤ A ∧
      (K.map (MulAut.conj g).toMonoidHom).relIndex A = p := by
  have hAc := g71_map_conj_self hgN
  refine ⟨?_, ?_⟩
  · calc K.map (MulAut.conj g).toMonoidHom ≤ A.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hKA
      _ = A := hAc
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) K A
      (MulAut.conj g).injective
    rw [hAc, hK] at h
    exact h

private lemma g71_inv_apply (g : GLV V) (y : V) : g⁻¹ (g y) = y :=
  LinearEquiv.symm_apply_apply g y

private lemma g71X_conj {A K : Subgroup (GLV V)} {g : GLV V}
    (hgN : g ∈ Subgroup.normalizer (A : Set (GLV V))) :
    g71X A (K.map (MulAut.conj g).toMonoidHom) = (g71X A K).map (g : V →ₗ[ZMod 2] V) := by
  ext x
  constructor
  · intro hx
    obtain ⟨h1, h2⟩ := mem_g71X.mp hx
    refine ⟨g⁻¹ x, mem_g71X.mpr ⟨fun k hk => ?_, ?_⟩, ?_⟩
    · have hmem : MulAut.conj g k ∈ K.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hk
      have e1 : g (k (g⁻¹ x)) = x := h1 _ hmem
      calc k (g⁻¹ x) = g⁻¹ (g (k (g⁻¹ x))) := (LinearEquiv.symm_apply_apply _ _).symm
        _ = g⁻¹ x := by rw [e1]
    · have := g71_sum_conj (g := g⁻¹) (Subgroup.inv_mem _ hgN) x
      rw [← this, h2, map_zero]
    · exact LinearEquiv.apply_symm_apply _ _
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := mem_g71X.mp hy
    refine mem_g71X.mpr ⟨fun k' hk' => ?_, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hk'
      show (g * k * g⁻¹) (g y) = g y
      rw [show (g * k * g⁻¹) (g y) = g (k (g⁻¹ (g y))) from rfl, g71_inv_apply,
        h1 k hk]
    · show g71Sum A (g y) = 0
      rw [← g71_sum_conj hgN y, h2, map_zero]

private lemma g71_X_ne_bot {A K : Subgroup (GLV V)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ≤ A) (hAodd : Odd (Nat.card A))
    {w : V} (hw : ∀ k ∈ K, k w = w) (hwA : ∃ a ∈ A, a w ≠ w) : g71X A K ≠ ⊥ := by
  intro hbot
  obtain ⟨a, haA, haw⟩ := hwA
  have hQfix : ∀ b ∈ A, b (g71Sum A w) = g71Sum A w := fun b hb => g71Sum_left A hb w
  have hQQ : g71Sum A (g71Sum A w) = g71Sum A w := g71Sum_fixed_odd hAodd hQfix
  have huX : w - g71Sum A w ∈ g71X A K := by
    refine mem_g71X.mpr ⟨fun k hk => ?_, ?_⟩
    · rw [map_sub, hw k hk, g71Sum_left A (hKA hk) w]
    · rw [map_sub, hQQ, sub_self]
  rw [hbot, Submodule.mem_bot] at huX
  have hwfix : w = g71Sum A w := sub_eq_zero.mp huX
  apply haw
  rw [hwfix]
  exact g71Sum_left A haA w

private lemma g71X_eq_fixed {A K : Subgroup (GLV V)} (h : fixedSpace A = ⊥) :
    g71X A K = fixedSpace K := by
  unfold g71X
  apply le_antisymm inf_le_left
  intro x hx
  refine Submodule.mem_inf.mpr ⟨hx, ?_⟩
  have hQ : g71Sum A x ∈ fixedSpace A := fun k hk => g71Sum_left A hk x
  rw [h, Submodule.mem_bot] at hQ
  exact LinearMap.mem_ker.mpr hQ

private lemma g71_avg {A : Subgroup (GLV V)} (hodd : Odd (Nat.card A))
    (W : Submodule (ZMod 2) V) (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) :
    ∃ W' : Submodule (ZMod 2) V, (∀ a ∈ A, ∀ w ∈ W', a w ∈ W') ∧ IsCompl W W' := by
  obtain ⟨C, hC⟩ := W.exists_isCompl
  have hC' : IsCompl (LinearMap.range W.subtype) C := by
    rw [Submodule.range_subtype]; exact hC
  let pr : V →ₗ[ZMod 2] W := LinearMap.linearProjOfIsCompl C W.subtype Subtype.val_injective hC'
  let pj : V →ₗ[ZMod 2] V := W.subtype ∘ₗ pr
  have hpjW : ∀ w ∈ W, pj w = w := by
    intro w hw
    have h1 := LinearMap.linearProjOfIsCompl_apply_left C W.subtype Subtype.val_injective hC'
      ⟨w, hw⟩
    have h2 : pr w = ⟨w, hw⟩ := h1
    show W.subtype (pr w) = w
    rw [h2]
    rfl
  have hpjmem : ∀ v, pj v ∈ W := fun v => (pr v).2
  let Pav : V →ₗ[ZMod 2] V := ∑ a : A,
    ((a : GLV V).toLinearMap ∘ₗ pj ∘ₗ ((a : GLV V)⁻¹).toLinearMap)
  have hPav : ∀ v, Pav v = ∑ a : A, (a : GLV V) (pj ((a : GLV V)⁻¹ v)) := by
    intro v
    simp [Pav, LinearMap.sum_apply]
  have hPavW : ∀ w ∈ W, Pav w = w := by
    intro w hw
    rw [hPav]
    calc ∑ a : A, (a : GLV V) (pj ((a : GLV V)⁻¹ w)) = ∑ a : A, (a : GLV V) ((a : GLV V)⁻¹ w) :=
          Finset.sum_congr rfl fun a _ => by
            rw [hpjW _ (hW _ (A.inv_mem a.2) w hw)]
      _ = ∑ _a : A, w := Finset.sum_congr rfl fun a _ => by simp
      _ = Nat.card A • w := by simp only [Finset.sum_const, Finset.card_univ,
            Nat.card_eq_fintype_card]
      _ = w := g71_odd_nsmul hodd w
  have hPavmem : ∀ v, Pav v ∈ W := by
    intro v
    rw [hPav]
    exact Submodule.sum_mem _ fun a _ => hW _ a.2 _ (hpjmem _)
  have hPavequiv : ∀ b ∈ A, ∀ v, Pav (b v) = b (Pav v) := by
    intro b hb v
    rw [hPav, hPav, map_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft (⟨b, hb⟩ : A)) _ _ fun a => ?_).symm
    simp [mul_inv_rev, LinearEquiv.mul_apply, g71_inv_apply]
  refine ⟨LinearMap.ker Pav, fun a ha w hw => ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hw ⊢
    rw [hPavequiv a ha, hw, map_zero]
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hxW hxK
      rw [LinearMap.mem_ker] at hxK
      rw [← hPavW x hxW, hxK]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      rw [Submodule.mem_sup]
      refine ⟨Pav v, hPavmem v, v - Pav v, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hPavW (Pav v) (hPavmem v), sub_self]

private lemma g71_simple_card {p : ℕ} (hp : p.Prime) {M G : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] [Nontrivial M] [Group G] [Finite G]
    (ψ : G →* (M ≃ₗ[ZMod 2] M))
    (hcomm : ∀ g h : G, ψ g * ψ h = ψ h * ψ g) (hexp : ∀ g : G, g ^ p = 1)
    (hsimple : ∀ N : Submodule (ZMod 2) M, (∀ g : G, ∀ x ∈ N, ψ g x ∈ N) → N = ⊥ ∨ N = ⊤) :
    Nat.card ψ.range ≤ p := by
  let E : (M ≃ₗ[ZMod 2] M) → Module.End (ZMod 2) M := fun e => (e : M →ₗ[ZMod 2] M)
  have hEmul : ∀ e f : M ≃ₗ[ZMod 2] M, E (e * f) = E e * E f := fun e f => by
    apply LinearMap.ext
    intro x
    rfl
  have hE1 : E 1 = 1 := by
    apply LinearMap.ext
    intro x
    rfl
  let S : Set (Module.End (ZMod 2) M) := {r | ∃ g : G, r = E (ψ g)}
  have hScomm : S.Pairwise Commute := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ _
    show E (ψ g) * E (ψ h) = E (ψ h) * E (ψ g)
    rw [← hEmul, ← hEmul, hcomm g h]
  letI : CommRing (Subring.closure S) := Subring.closureCommRingOfComm hScomm
  have hRS : ∀ r ∈ S, ∀ a : Subring.closure S,
      (a : Module.End (ZMod 2) M) * r = r * (a : Module.End (ZMod 2) M) := by
    intro r hr a
    have hc := mul_comm a (⟨r, Subring.subset_closure hr⟩ : Subring.closure S)
    have := congrArg Subtype.val hc
    simpa using this
  have hnzd : NoZeroDivisors (Subring.closure S) := by
    constructor
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    have hab' : (a : Module.End (ZMod 2) M) * (b : Module.End (ZMod 2) M) = 0 := by
      have := congrArg Subtype.val hab
      simpa using this
    have hker : ∀ g : G, ∀ x ∈ LinearMap.ker (a : Module.End (ZMod 2) M),
        ψ g x ∈ LinearMap.ker (a : Module.End (ZMod 2) M) := by
      intro g x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hc := hRS (E (ψ g)) ⟨g, rfl⟩ a
      have := congrArg (fun r : Module.End (ZMod 2) M => r x) hc
      simp only [Module.End.mul_apply] at this
      rw [hx, map_zero] at this
      exact this
    rcases hsimple _ hker with hbot | htop
    · apply Subtype.ext
      apply LinearMap.ext
      intro x
      have hbx : (b : Module.End (ZMod 2) M) x ∈ LinearMap.ker (a : Module.End (ZMod 2) M) := by
        rw [LinearMap.mem_ker]
        have := congrArg (fun r : Module.End (ZMod 2) M => r x) hab'
        simpa [Module.End.mul_apply] using this
      rw [hbot, Submodule.mem_bot] at hbx
      simpa using hbx
    · exfalso
      apply ha
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      have hx : x ∈ LinearMap.ker (a : Module.End (ZMod 2) M) := by
        rw [htop]
        exact Submodule.mem_top
      rw [LinearMap.mem_ker] at hx
      simpa using hx
  haveI : NoZeroDivisors (Subring.closure S) := hnzd
  haveI : IsDomain (Subring.closure S) := NoZeroDivisors.to_isDomain _
  let f : Polynomial (Subring.closure S) := Polynomial.X ^ p - Polynomial.C 1
  have hf0 : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hp.pos 1
  have hfdeg : f.natDegree = p := Polynomial.natDegree_X_pow_sub_C
  let rts : Finset (Subring.closure S) := f.roots.toFinset
  have hrts : ∀ r : Subring.closure S, r ^ p = 1 → r ∈ rts := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0]
    simp [f, hr]
  have hcardrts : rts.card ≤ p := by
    calc rts.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = p := hfdeg
  have hmemS : ∀ x ∈ ψ.range, E (x : M ≃ₗ[ZMod 2] M) ∈ Subring.closure S := by
    intro x hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
    exact Subring.subset_closure ⟨g, rfl⟩
  have hEpow : ∀ g : G, ∀ n : ℕ, E (ψ g) ^ n = E (ψ g ^ n) := by
    intro g n
    induction n with
    | zero => rw [pow_zero, pow_zero, hE1]
    | succ n ih => rw [pow_succ, pow_succ, ih, hEmul]
  have hpowE : ∀ x ∈ ψ.range, E (x : M ≃ₗ[ZMod 2] M) ^ p = 1 := by
    intro x hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
    have hgp : ψ g ^ p = 1 := by rw [← map_pow, hexp g, map_one]
    rw [hEpow, hgp, hE1]
  let F : ψ.range → rts := fun x =>
    ⟨⟨E (x.1 : M ≃ₗ[ZMod 2] M), hmemS x.1 x.2⟩, hrts _ (Subtype.ext (by
      simpa using hpowE x.1 x.2))⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : E (x.1 : M ≃ₗ[ZMod 2] M) = E (y.1 : M ≃ₗ[ZMod 2] M) := by
      have := congrArg (fun r : rts => (r.1 : Module.End (ZMod 2) M)) hxy
      exact this
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    exact congrArg (fun f : Module.End (ZMod 2) M => f m) h1
  have hle : Nat.card ψ.range ≤ Nat.card rts := Nat.card_le_card_of_injective F hFinj
  have hrtsc : Nat.card rts = rts.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  omega

private lemma g71_exists_hyp {p : ℕ} (hp : p.Prime) {A : Subgroup (GLV V)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAexp : ∀ a ∈ A, a ^ p = 1)
    (hAodd : Odd (Nat.card A)) (hAp : IsPGroup p A) {z : GLV V} (hzA : z ∈ A) (hz1 : z ≠ 1) :
    ∃ K : Subgroup (GLV V), K ≤ A ∧ K.relIndex A = p ∧ z ∉ K ∧ g71X A K ≠ ⊥ := by
  haveI := Fact.mk hp
  obtain ⟨u0, hu0⟩ : ∃ u : V, z u ≠ u := by
    by_contra h
    push Not at h
    exact hz1 (LinearEquiv.ext fun u => h u)
  haveI : WellFoundedLT (Submodule (ZMod 2) V) := Finite.to_wellFoundedLT
  let 𝒰 : Set (Submodule (ZMod 2) V) :=
    {U | (∀ a ∈ A, ∀ u ∈ U, a u ∈ U) ∧ ∃ u ∈ U, z u ≠ u}
  have hne : 𝒰.Nonempty := ⟨⊤, fun a _ u _ => Submodule.mem_top, u0, Submodule.mem_top, hu0⟩
  obtain ⟨U, ⟨hUinv, u1, hu1U, hu1⟩, hmin⟩ := WellFounded.has_min wellFounded_lt 𝒰 hne
  have hsimp : ∀ W : Submodule (ZMod 2) V, W ≤ U → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      W = ⊥ ∨ W = U := by
    intro W hWU hWinv
    by_contra hcon
    push Not at hcon
    obtain ⟨hW0, hWU'⟩ := hcon
    obtain ⟨W'', hW''inv, hcompl⟩ := g71_avg hAodd W hWinv
    have hUeq : W ⊔ (W'' ⊓ U) = U := by
      rw [← sup_inf_assoc_of_le W'' hWU, hcompl.sup_eq_top, top_inf_eq]
    have hdisj : Disjoint W (W'' ⊓ U) := hcompl.disjoint.mono_right inf_le_left
    have hU''inv : ∀ a ∈ A, ∀ u ∈ W'' ⊓ U, a u ∈ W'' ⊓ U := fun a ha u hu =>
      ⟨hW''inv a ha u hu.1, hUinv a ha u hu.2⟩
    by_cases hzW : ∃ w ∈ W, z w ≠ w
    · exact hmin W ⟨hWinv, hzW⟩ (lt_of_le_of_ne hWU hWU')
    · by_cases hzU : ∃ u ∈ W'' ⊓ U, z u ≠ u
      · have hlt : W'' ⊓ U < U := by
          refine lt_of_le_of_ne inf_le_right fun h => ?_
          have h0 := hdisj.eq_bot
          rw [h, inf_eq_left.mpr hWU] at h0
          exact hW0 h0
        exact hmin (W'' ⊓ U) ⟨hU''inv, hzU⟩ hlt
      · push Not at hzW hzU
        apply hu1
        rw [← hUeq] at hu1U
        obtain ⟨w, hw, u'', hu'', hsum⟩ := Submodule.mem_sup.mp hu1U
        rw [← hsum, map_add, hzW w hw, hzU u'' hu'']
  have hres : ∀ a ∈ A, U.map ((a : GLV V) : V →ₗ[ZMod 2] V) = U := by
    intro a ha
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hUinv a ha u hu
    · intro u hu
      exact ⟨(a : GLV V)⁻¹ u, hUinv _ (A.inv_mem ha) u hu, by simp⟩
  let ψ : A →* (U ≃ₗ[ZMod 2] U) :=
    { toFun := fun a => LinearEquiv.ofSubmodules (a : GLV V) U U (hres a a.2)
      map_one' := by
        apply LinearEquiv.ext
        intro u
        apply Subtype.ext
        rfl
      map_mul' := by
        intro a b
        apply LinearEquiv.ext
        intro u
        apply Subtype.ext
        rfl }
  have hcommψ : ∀ g h : A, ψ g * ψ h = ψ h * ψ g := by
    intro g h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA _ g.2 _ h.2)
  have hexpψ : ∀ g : A, g ^ p = 1 := fun g => Subtype.ext (by simpa using hAexp _ g.2)
  have hu1pos : u1 ≠ 0 := by
    intro h
    apply hu1
    rw [h, map_zero]
  haveI : Nontrivial U := ⟨⟨⟨u1, hu1U⟩, 0, fun h => hu1pos (congrArg Subtype.val h)⟩⟩
  have hsimpleψ : ∀ N : Submodule (ZMod 2) U, (∀ g : A, ∀ x ∈ N, ψ g x ∈ N) →
      N = ⊥ ∨ N = ⊤ := by
    intro N hN
    have hW : N.map U.subtype ≤ U := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hWinv : ∀ a ∈ A, ∀ w ∈ N.map U.subtype, a w ∈ N.map U.subtype := by
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨ψ ⟨a, ha⟩ x, hN ⟨a, ha⟩ x hx, rfl⟩
    rcases hsimp _ hW hWinv with h | h
    · left
      apply Submodule.map_injective_of_injective U.injective_subtype
      rw [Submodule.map_bot]
      exact h
    · right
      apply Submodule.map_injective_of_injective U.injective_subtype
      rw [h, Submodule.map_subtype_top]
  have hcard := g71_simple_card hp ψ hcommψ hexpψ hsimpleψ
  let K : Subgroup (GLV V) := ψ.ker.map A.subtype
  have hKA : K ≤ A := Subgroup.map_subtype_le ψ.ker
  have hKmem : ∀ k ∈ K, ∀ u ∈ U, k u = u := by
    intro k hk u hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hk
    have h1 : ψ a = 1 := MonoidHom.mem_ker.mp ha
    have h2 : ((ψ a) ⟨u, hu⟩ : V) = u := by rw [h1]; rfl
    exact h2
  have hzK : z ∉ K := fun hz => hu1 (hKmem z hz u1 hu1U)
  have htopA : (⊤ : Subgroup A).map A.subtype = A := by
    ext x
    simp
  have hKidx : K.relIndex A = ψ.ker.index := by
    have h := Subgroup.relIndex_map_map_of_injective (f := A.subtype) ψ.ker ⊤
      Subtype.val_injective
    rw [htopA, Subgroup.relIndex_top_right] at h
    exact h
  have hidx_le : K.relIndex A ≤ p := by
    rw [hKidx, Subgroup.index_ker]
    exact hcard
  have hidx_ne1 : K.relIndex A ≠ 1 := by
    intro h1
    have hAK := Subgroup.relIndex_eq_one.mp h1
    exact hzK (hAK hzA)
  have hidx_pp : K.relIndex A = p := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hAp
    have hdvd : K.relIndex A ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.relIndex_dvd_card K A
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exact absurd (by simpa using hkeq) hidx_ne1
      · simpa using hkeq
    · exfalso
      have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
      have h4 : K.relIndex A ≤ p := hidx_le
      rw [hkeq] at h4
      linarith
  refine ⟨K, hKA, hidx_pp, hzK, ?_⟩
  exact g71_X_ne_bot hA hKA hAodd (w := u1) (fun k hk => hKmem k hk u1 hu1U) ⟨z, hzA, hu1⟩

private lemma g71_zpowers_inter {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {a b w : G}
    (ha : orderOf a = p) (hb : orderOf b = p) (hab : a ∉ Subgroup.zpowers b)
    (hwa : w ∈ Subgroup.zpowers a) (hwb : w ∈ Subgroup.zpowers b) : w = 1 := by
  by_contra hw
  have hwo : orderOf w = p := by
    have hdvd : orderOf w ∣ p := ha ▸ orderOf_dvd_of_mem_zpowers hwa
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw
    · exact h
  have e1 : Subgroup.zpowers w = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwa)
      (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, ha]))
  have e2 : Subgroup.zpowers w = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwb)
      (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hb]))
  have h := Subgroup.mem_zpowers a
  rw [← e1, e2] at h
  exact hab h

private lemma g71_center_comm {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 3) (hnc : ∃ a b : G, a * b ≠ b * a) (x y : G) :
    y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center G := by
  haveI := Fact.mk hp
  have hZne : Subgroup.center G ≠ ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have hb : b ∈ Subgroup.center G := by
      rw [h]
      exact Subgroup.mem_top b
    exact (Subgroup.mem_center_iff.mp hb) a
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hG (by norm_num)
  have hkle : k ≤ 3 := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.center G)
    rw [hk, hG] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h
  have hk3 : k ≠ 3 := by
    intro h3
    apply hZne
    apply Subgroup.eq_top_of_card_eq
    rw [hk, hG, h3]
  have hidx := Subgroup.card_mul_index (Subgroup.center G)
  rw [hk, hG] at hidx
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2 : k = 2 := by omega
    subst hk2
    have hind : (Subgroup.center G).index = p := by
      have h2 : p ^ 2 * (Subgroup.center G).index = p ^ 2 * p := by
        rw [hidx]
        ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h2
    haveI : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hind
    have hcomm := isMulCommutative_of_isCyclic_quotient_center_self (G := G)
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (hcomm.is_comm.comm a b)
  have hind : (Subgroup.center G).index = p ^ 2 := by
    rw [hk1, pow_one] at hidx
    have h2 : p * (Subgroup.center G).index = p * p ^ 2 := by
      rw [hidx]
      ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h2
  haveI : IsMulCommutative (G ⧸ Subgroup.center G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hind
  have key : ∀ a b : G, (a * b)⁻¹ * (b * a) ∈ Subgroup.center G := by
    intro a b
    have h := IsMulCommutative.is_comm.comm (a : G ⧸ Subgroup.center G)
      (b : G ⧸ Subgroup.center G)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h
    exact QuotientGroup.eq.mp h
  have h := key x⁻¹ y⁻¹
  simpa [mul_inv_rev, mul_assoc] using h

private def g71HeiSub {x z : GLV V} (hxz : Commute x z) : Subgroup (GLV V) where
  carrier := {g | ∃ i c : ℤ, g = x ^ i * z ^ c}
  mul_mem' := by
    rintro _ _ ⟨i, c, rfl⟩ ⟨j, d, rfl⟩
    refine ⟨i + j, c + d, ?_⟩
    calc x ^ i * z ^ c * (x ^ j * z ^ d) = x ^ i * (z ^ c * x ^ j) * z ^ d := by
          simp only [mul_assoc]
      _ = x ^ i * (x ^ j * z ^ c) * z ^ d := by rw [(hxz.zpow_zpow j c).symm.eq]
      _ = x ^ (i + j) * z ^ (c + d) := by
          rw [zpow_add, zpow_add]
          simp only [mul_assoc]
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, c, rfl⟩
    refine ⟨-i, -c, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact ((hxz.zpow_zpow (-i) (-c)).eq).symm

private lemma g71Hei_comm {x z : GLV V} (hxz : Commute x z) {a b : GLV V}
    (ha : a ∈ g71HeiSub hxz) (hb : b ∈ g71HeiSub hxz) : a * b = b * a := by
  obtain ⟨i, c, rfl⟩ := ha
  obtain ⟨j, d, rfl⟩ := hb
  have h1 : Commute (x ^ i) (x ^ j) := (Commute.refl x).zpow_zpow i j
  have h2 : Commute (x ^ i) (z ^ d) := hxz.zpow_zpow i d
  have h3 : Commute (z ^ c) (x ^ j) := (hxz.zpow_zpow j c).symm
  have h4 : Commute (z ^ c) (z ^ d) := (Commute.refl z).zpow_zpow c d
  exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq

private lemma g71Hei_pow {x z : GLV V} {p : ℕ} (hxz : Commute x z) (hxp : x ^ p = 1)
    (hzp : z ^ p = 1) {a : GLV V} (ha : a ∈ g71HeiSub hxz) : a ^ p = 1 := by
  have hzpow : ∀ (g : GLV V), g ^ p = 1 → ∀ n : ℤ, (g ^ n) ^ p = 1 := by
    intro g hg n
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  obtain ⟨i, c, rfl⟩ := ha
  rw [(hxz.zpow_zpow i c).mul_pow, hzpow x hxp i, hzpow z hzp c, one_mul]

private lemma g71_conj_formula {x y z : GLV V} (hxz : Commute x z) (hyx : y * x * y⁻¹ = z * x)
    (hyz : Commute y z) (i c : ℤ) : y * (x ^ i * z ^ c) * y⁻¹ = z ^ i * (x ^ i * z ^ c) := by
  have hzx : Commute z x := hxz.symm
  have e1 : y * (x ^ i * z ^ c) * y⁻¹ = (y * x ^ i * y⁻¹) * (y * z ^ c * y⁻¹) := by group
  have hyzc : y * z ^ c * y⁻¹ = z ^ c := by
    rw [(hyz.zpow_right c).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [e1, hyzc, ← conj_zpow, hyx, hzx.mul_zpow i, mul_assoc]

private lemma g71_X_conj_ne {A K : Subgroup (GLV V)} {g : GLV V}
    (hgN : g ∈ Subgroup.normalizer (A : Set (GLV V))) (h : g71X A K ≠ ⊥) :
    g71X A (K.map (MulAut.conj g).toMonoidHom) ≠ ⊥ := by
  rw [g71X_conj hgN]
  intro hb
  apply h
  have hfr := LinearEquiv.finrank_map_eq (g : GLV V) (g71X A K)
  rw [hb, finrank_bot] at hfr
  exact Submodule.finrank_eq_zero.mp hfr.symm

private lemma g71_orbit_inj {G : Type*} [Group G] [Finite G] {p : ℕ} [hpf : Fact p.Prime]
    {z k : G}
    (hz : orderOf z = p) (hk : orderOf k = p) (hkz : k ∉ Subgroup.zpowers z) (hzk : Commute z k)
    {e : ℤ} (he : ¬ (p : ℤ) ∣ e) {j₁ j₂ : ℕ} (hj₁ : j₁ < p) (hj₂ : j₂ < p)
    (h : Subgroup.zpowers (z ^ (e * j₁) * k) = Subgroup.zpowers (z ^ (e * j₂) * k)) :
    j₁ = j₂ := by
  have hmem : z ^ (e * j₁) * k ∈ Subgroup.zpowers (z ^ (e * j₂) * k) := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc : Commute (z ^ (e * j₂)) k := hzk.zpow_left _
  have hpow : (z ^ (e * j₂) * k) ^ m = z ^ (e * j₂ * m) * k ^ m := by
    rw [hc.mul_zpow, ← zpow_mul]
  rw [hpow] at hm
  have hkm : k ^ m = k ^ (m - 1) * k := by
    rw [← zpow_add_one]
    congr 1
    ring
  rw [hkm] at hm
  have h1 : z ^ (e * j₂ * m) * k ^ (m - 1) = z ^ (e * j₁) := by
    apply mul_right_cancel (b := k)
    rw [mul_assoc, hm]
  have h2 : z ^ (e * j₁ - e * j₂ * m) = (z ^ (e * j₂ * m))⁻¹ * z ^ (e * j₁) := by
    rw [← zpow_neg, ← zpow_add]
    congr 1
    ring
  have hu : z ^ (e * j₁ - e * j₂ * m) = k ^ (m - 1) := by
    rw [h2, ← h1, inv_mul_cancel_left]
  have hv1 : k ^ (m - 1) ∈ Subgroup.zpowers k := zpow_mem (Subgroup.mem_zpowers k) _
  have hv2 : k ^ (m - 1) ∈ Subgroup.zpowers z := by
    rw [← hu]
    exact zpow_mem (Subgroup.mem_zpowers z) _
  have hone : k ^ (m - 1) = 1 := g71_zpowers_inter hk hz hkz hv1 hv2
  have hpm : (p : ℤ) ∣ (m - 1) := by
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr hone
    rw [hk] at h3
    exact_mod_cast h3
  have hpu : (p : ℤ) ∣ (e * j₁ - e * j₂ * m) := by
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr (hu.trans hone)
    rw [hz] at h3
    exact_mod_cast h3
  have hdiv : (p : ℤ) ∣ e * ((j₁ : ℤ) - j₂) := by
    have h3 : e * ((j₁ : ℤ) - j₂) = (e * j₁ - e * j₂ * m) + e * j₂ * (m - 1) := by ring
    rw [h3]
    exact dvd_add hpu (dvd_mul_of_dvd_right hpm _)
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpf.out
  have hdiv2 : (p : ℤ) ∣ ((j₁ : ℤ) - j₂) := by
    rcases hprime.dvd_or_dvd hdiv with h4 | h4
    · exact absurd h4 he
    · exact h4
  have hlt : |(j₁ : ℤ) - j₂| < p := by
    rw [abs_lt]
    constructor <;> omega
  have h0 := Int.eq_zero_of_abs_lt_dvd hdiv2 hlt
  omega

private lemma g71_heis {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {P : Subgroup (GLV V)}
    (hPP : IsPGroup p P) (hcardP : Nat.card P = p ^ 3) (hexpP : ∀ g ∈ P, g ^ p = 1)
    {a b : GLV V} (ha : a ∈ P) (hb : b ∈ P) (hab : a * b ≠ b * a) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  haveI := Fact.mk hp
  obtain ⟨y, x, hy, hx, hyx⟩ : ∃ y x : GLV V, y ∈ P ∧ x ∈ P ∧ y * x ≠ x * y :=
    ⟨a, b, ha, hb, hab⟩
  have hnc : ∃ u v : P, u * v ≠ v * u :=
    ⟨⟨y, hy⟩, ⟨x, hx⟩, fun h => hyx (congrArg Subtype.val h)⟩
  obtain ⟨z, hzdef⟩ : ∃ z : GLV V, z = y * x * y⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hzP : z ∈ P := by
    rw [hzdef]
    exact P.mul_mem (P.mul_mem (P.mul_mem hy hx) (P.inv_mem hy)) (P.inv_mem hx)
  have hzcen : ∀ g ∈ P, g * z = z * g := by
    intro g hg
    have hmem := g71_center_comm hp hcardP hnc ⟨x, hx⟩ ⟨y, hy⟩
    have hz' : (⟨z, hzP⟩ : P) = ⟨y, hy⟩ * ⟨x, hx⟩ * ⟨y, hy⟩⁻¹ * ⟨x, hx⟩⁻¹ :=
      Subtype.ext hzdef
    rw [← hz'] at hmem
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hmem) ⟨g, hg⟩)
  have hz1 : z ≠ 1 := by
    intro h
    apply hyx
    calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
      _ = x * y := by rw [← hzdef, h, one_mul]
  have hxz : Commute x z := hzcen x hx
  have hyz : Commute y z := hzcen y hy
  have hzx : Commute z x := hxz.symm
  have hxp : x ^ p = 1 := hexpP x hx
  have hzp : z ^ p = 1 := hexpP z hzP
  have hyxz : y * x * y⁻¹ = z * x := by
    rw [hzdef]
    group
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hAc : ∀ a ∈ g71HeiSub hxz, ∀ b ∈ g71HeiSub hxz, a * b = b * a :=
    fun a ha b hb => g71Hei_comm hxz ha hb
  have hAexp : ∀ a ∈ g71HeiSub hxz, a ^ p = 1 := fun a ha => g71Hei_pow hxz hxp hzp ha
  have hAle : g71HeiSub hxz ≤ P := by
    intro g hg
    obtain ⟨i, c, rfl⟩ := hg
    exact P.mul_mem (P.zpow_mem hx i) (P.zpow_mem hzP c)
  have hxA : x ∈ g71HeiSub hxz := ⟨1, 0, by simp⟩
  have hzA : z ∈ g71HeiSub hxz := ⟨0, 1, by simp⟩
  have hxz_ne : x ∉ Subgroup.zpowers z := by
    intro hx'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx'
    have hyzm : y * z ^ m * y⁻¹ = z ^ m := by
      rw [(hyz.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : y * x * y⁻¹ = x := by
      rw [← hm, hyzm]
    have h2 : z * x = x := by rw [← hyxz, h1]
    apply hz1
    exact mul_right_cancel (b := x) (by rw [one_mul, h2])
  have hzA' : Subgroup.zpowers z ≤ g71HeiSub hxz := Subgroup.zpowers_le.mpr hzA
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have hAcard : Nat.card (g71HeiSub hxz) = p ^ 2 := by
    have hdvd : Nat.card (g71HeiSub hxz) ∣ p ^ 3 := by
      rw [← hcardP]
      exact Subgroup.card_dvd_of_le hAle
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hcardzA : Nat.card (Subgroup.zpowers z) ≤ Nat.card (g71HeiSub hxz) :=
      Subgroup.card_le_of_le hzA'
    have hp2 := hp.two_le
    interval_cases j
    · rw [pow_zero] at hjeq
      omega
    · exfalso
      have hAz : Subgroup.zpowers z = g71HeiSub hxz :=
        Subgroup.eq_of_le_of_card_ge hzA' (le_of_eq (by rw [hzcard, hjeq, pow_one]))
      exact hxz_ne (hAz ▸ hxA)
    · simpa using hjeq
    · exfalso
      have hAP : g71HeiSub hxz = P :=
        Subgroup.eq_of_le_of_card_ge hAle (le_of_eq (by rw [hcardP, hjeq]))
      apply hyx
      exact hAc y (hAP ▸ hy) x (hAP ▸ hx)
  have hAp : IsPGroup p (g71HeiSub hxz) := IsPGroup.of_card hAcard
  have hAodd : Odd (Nat.card (g71HeiSub hxz)) := by
    rw [hAcard]
    exact hpodd.pow
  obtain ⟨K0, hK0A, hK0i, hzK0, hX0⟩ :=
    g71_exists_hyp hp hAc hAexp hAodd hAp hzA hz1
  have hK0card : Nat.card K0 = p := by
    have h := Subgroup.relIndex_mul_card (H := K0) (K := g71HeiSub hxz)
    rw [hK0i, inf_eq_left.mpr hK0A, hAcard] at h
    have h2 : p * Nat.card K0 = p * p := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h2
  have hK0ne : K0 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hK0card
    have := hp.one_lt
    omega
  obtain ⟨k', hk'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK0ne
  have hkord : orderOf (k' : GLV V) = p := by
    have hdvd : orderOf k' ∣ Nat.card K0 := orderOf_dvd_natCard k'
    rw [hK0card] at hdvd
    rw [Subgroup.orderOf_coe]
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hk'
    · exact h
  have hK0eq : Subgroup.zpowers (k' : GLV V) = K0 :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr k'.2)
      (le_of_eq (by rw [Nat.card_zpowers, hkord, hK0card]))
  obtain ⟨i, c, hkic⟩ : ∃ i c : ℤ, (k' : GLV V) = x ^ i * z ^ c := hK0A k'.2
  have hkz : (k' : GLV V) ∉ Subgroup.zpowers z := by
    intro hkz
    apply hzK0
    rw [← hK0eq]
    have heq : Subgroup.zpowers (k' : GLV V) = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkz)
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hkord, hzord]))
    rw [heq]
    exact Subgroup.mem_zpowers z
  have hpi : ¬ ((p : ℤ) ∣ i) := by
    rintro ⟨m, rfl⟩
    apply hkz
    rw [hkic]
    have hx1 : x ^ ((p : ℤ) * m) = 1 := by
      rw [zpow_mul, zpow_natCast, hxp, one_zpow]
    rw [hx1, one_mul]
    exact zpow_mem (Subgroup.mem_zpowers z) c
  have hyzpow : ∀ n : ℤ, y * z ^ n * y⁻¹ = z ^ n := fun n => by
    rw [(hyz.zpow_right n).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hyk : ∀ i' c' : ℤ, y * (x ^ i' * z ^ c') * y⁻¹ = z ^ i' * (x ^ i' * z ^ c') :=
    fun i' c' => g71_conj_formula hxz hyxz hyz i' c'
  have hyjk : ∀ (j : ℕ) (i' c' : ℤ), y ^ j * (x ^ i' * z ^ c') * (y ^ j)⁻¹ =
      z ^ (i' * j) * (x ^ i' * z ^ c') := by
    intro j
    induction j with
    | zero => intro i' c'; simp
    | succ j ih =>
      intro i' c'
      have e1 : y ^ (j + 1) * (x ^ i' * z ^ c') * (y ^ (j + 1))⁻¹ =
          y * (y ^ j * (x ^ i' * z ^ c') * (y ^ j)⁻¹) * y⁻¹ := by
        rw [pow_succ']
        group
      have e2 : y * (z ^ (i' * j) * (x ^ i' * z ^ c')) * y⁻¹ =
          (y * z ^ (i' * j) * y⁻¹) * (y * (x ^ i' * z ^ c') * y⁻¹) := by
        group
      rw [e1, ih, e2, hyzpow, hyk, show i' * ((j + 1 : ℕ) : ℤ) = i' * j + i' by push_cast; ring,
        zpow_add]
      simp only [mul_assoc]
  have hKf : ∀ j : ℕ, K0.map (MulAut.conj (y ^ j)).toMonoidHom =
      Subgroup.zpowers (z ^ (i * (j : ℤ)) * (k' : GLV V)) := by
    intro j
    have hc : (MulAut.conj (y ^ j)).toMonoidHom (k' : GLV V) =
        z ^ (i * (j : ℤ)) * (k' : GLV V) := by
      show y ^ j * (k' : GLV V) * (y ^ j)⁻¹ = _
      rw [hkic]
      exact hyjk j i c
    have hmap : K0.map (MulAut.conj (y ^ j)).toMonoidHom =
        (Subgroup.zpowers (k' : GLV V)).map (MulAut.conj (y ^ j)).toMonoidHom := by
      rw [hK0eq]
    rw [hmap, MonoidHom.map_zpowers, hc]
  have hzk : Commute z (k' : GLV V) := hAc z hzA _ (hK0A k'.2)
  have hinjOn : Set.InjOn (fun j : ℕ => K0.map (MulAut.conj (y ^ j)).toMonoidHom)
      (Finset.range p : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ h
    simp only [Finset.coe_range, Set.mem_Iio] at hj₁ hj₂
    simp only at h
    rw [hKf, hKf] at h
    exact g71_orbit_inj hzord hkord hkz hzk hpi hj₁ hj₂ h
  have hyA : (g71HeiSub hxz).map (MulAut.conj y).toMonoidHom ≤ g71HeiSub hxz := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i', c', rfl⟩ := hg
    show y * (x ^ i' * z ^ c') * y⁻¹ ∈ g71HeiSub hxz
    rw [hyk i' c']
    refine ⟨i', i' + c', ?_⟩
    rw [← mul_assoc, (hzx.zpow_zpow i' i').eq, mul_assoc, ← zpow_add]
  have hAeq : (g71HeiSub hxz).map (MulAut.conj y).toMonoidHom = g71HeiSub hxz := by
    apply Subgroup.eq_of_le_of_card_ge hyA
    exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj y).injective).symm
  have hyN : y ∈ Subgroup.normalizer (g71HeiSub hxz : Set (GLV V)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hmem : (MulAut.conj y).toMonoidHom h ∈
          (g71HeiSub hxz).map (MulAut.conj y).toMonoidHom := Subgroup.mem_map_of_mem _ hh
      rw [hAeq] at hmem
      exact hmem
    · intro hh
      rw [← hAeq] at hh
      obtain ⟨g, hg, hgh⟩ := Subgroup.mem_map.mp hh
      have hgh' : g = h :=
        (MulAut.conj y).injective (show (MulAut.conj y) g = (MulAut.conj y) h from hgh)
      rw [← hgh']
      exact hg
  have hTmem : ∀ K ∈ (Finset.range p).image
      (fun j : ℕ => K0.map (MulAut.conj (y ^ j)).toMonoidHom),
      K ≤ g71HeiSub hxz ∧ K.relIndex (g71HeiSub hxz) = p ∧ g71X (g71HeiSub hxz) K ≠ ⊥ := by
    intro K hK
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
    have hgN : y ^ j ∈ Subgroup.normalizer (g71HeiSub hxz : Set (GLV V)) :=
      Subgroup.pow_mem _ hyN j
    obtain ⟨h1, h2⟩ := g71_conj_hyp hgN hK0A hK0i
    exact ⟨h1, h2, g71_X_conj_ne hgN hX0⟩
  have hTcard : ((Finset.range p).image
      (fun j : ℕ => K0.map (MulAut.conj (y ^ j)).toMonoidHom)).card = p := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]
  set T := (Finset.range p).image (fun j : ℕ => K0.map (MulAut.conj (y ^ j)).toMonoidHom)
    with hTdef
  have hind := g71_ind_le hp hAc hAodd T (fun K hK => ⟨(hTmem K hK).1, (hTmem K hK).2.1⟩)
  have hterm : ∀ K ∈ T, orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (g71X (g71HeiSub hxz) K) :=
    fun K hK => g71_ord_le hp hAc hAexp hAodd (hTmem K hK).1 (hTmem K hK).2.1 (hTmem K hK).2.2
  have hsum := Finset.card_nsmul_le_sum T _ _ hterm
  rw [smul_eq_mul, hTcard] at hsum
  exact le_trans hsum (le_trans (Nat.le_add_left _ _) hind)

end G71Aux

theorem as_G_7_1 : G_7_1 := by
  intro V _ _ hfin G d hd p hp hp2 P hPG hPP
  haveI := Fact.mk hp
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hPP
    rw [hk]
    exact hpodd.pow
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hcard
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcard
      have := hp.one_lt
      omega
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPbot
    have hxord : orderOf x = p := by
      rcases (Nat.dvd_prime hp).mp (hcard ▸ orderOf_dvd_natCard x) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx
      · exact h1
    have hxp : (x : GLV V) ^ p = 1 := by
      rw [← hxord, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have hg1 : (x : GLV V) ≠ 1 := fun h => hx (Subtype.ext h)
    have hAc : ∀ a ∈ Subgroup.zpowers (x : GLV V), ∀ b ∈ Subgroup.zpowers (x : GLV V),
        a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self (x : GLV V) i j).eq
    have hAexp : ∀ a ∈ Subgroup.zpowers (x : GLV V), a ^ p = 1 := by
      intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    have hAcard : Nat.card (Subgroup.zpowers (x : GLV V)) = p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
    have hAodd : Odd (Nat.card (Subgroup.zpowers (x : GLV V))) := by
      rw [hAcard]
      exact hpodd
    have hrel : (⊥ : Subgroup (GLV V)).relIndex (Subgroup.zpowers (x : GLV V)) = p := by
      rw [Subgroup.relIndex_bot_left, hAcard]
    have hXne : g71X (Subgroup.zpowers (x : GLV V)) ⊥ ≠ ⊥ := by
      obtain ⟨v, hv⟩ : ∃ v : V, (x : GLV V) v ≠ v := by
        by_contra h
        push Not at h
        exact hg1 (LinearEquiv.ext h)
      refine g71_X_ne_bot hAc bot_le hAodd (w := v) (fun k hk => ?_)
        ⟨(x : GLV V), Subgroup.mem_zpowers _, hv⟩
      rw [Subgroup.mem_bot.mp hk]
      rfl
    have hord := g71_ord_le hp hAc hAexp hAodd bot_le hrel hXne
    calc orderOf (2 : ZMod p)
        ≤ Module.finrank (ZMod 2) (g71X (Subgroup.zpowers (x : GLV V)) ⊥) := hord
      _ ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le _
      _ = d := hd
  ·
    intro hH
    unfold IsHeisenberg at hH
    obtain ⟨hcardP, hexp0, a, ha, b, hb, hab⟩ := hH
    have hexpP : ∀ g ∈ P, g ^ p = 1 := by
      intro g hg
      have h1 : orderOf (⟨g, hg⟩ : P) ∣ Monoid.exponent P := Monoid.order_dvd_exponent _
      rw [hexp0] at h1
      have h2 : (⟨g, hg⟩ : P) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      simpa using congrArg Subtype.val h2
    rw [← hd]
    exact g71_heis hp hpodd hPP hcardP hexpP ha hb hab
  ·
    intro hE n hn
    obtain ⟨hEc, hEexp⟩ := hE
    have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hEc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    obtain ⟨H0, hH0, hn0⟩ := hn.1
    have hmin : ∀ H : Subgroup (GLV V), IsHyperplaneOf p P H →
        n ≤ orbitLen (G ⊓ Subgroup.normalizer (P : Set (GLV V))) H :=
      fun H hH => hn.2 ⟨H, hH, rfl⟩
    have hPne : P ≠ ⊥ := by
      intro hbot
      have h1 : H0.relIndex P = 1 := Subgroup.relIndex_eq_one.mpr (by rw [hbot]; exact bot_le)
      have h2 := hH0.2
      rw [h1] at h2
      have := hp.one_lt
      omega
    obtain ⟨z, hzP, hz1⟩ : ∃ z : GLV V, z ∈ P ∧ z ≠ 1 := by
      obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
      exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
    obtain ⟨K1, hK1P, hK1i, hz1K1, hX1⟩ :=
      g71_exists_hyp hp hcomm hEexp hPodd hPP hzP hz1
    obtain ⟨S, hSdef⟩ : ∃ S : Set (Subgroup (GLV V)),
        S = {K | IsHyperplaneOf p P K ∧ g71X P K ≠ ⊥} := ⟨_, rfl⟩
    have hSmem : ∀ K, K ∈ S ↔ IsHyperplaneOf p P K ∧ g71X P K ≠ ⊥ := by
      intro K
      rw [hSdef]
      rfl
    have hSfin : S.Finite := Set.toFinite S
    have hSorb : ∀ K ∈ S, ∀ g ∈ G ⊓ Subgroup.normalizer (P : Set (GLV V)),
        K.map (MulAut.conj g).toMonoidHom ∈ S := by
      intro K hK g hg
      obtain ⟨⟨hKP, hKi⟩, hX⟩ := (hSmem K).mp hK
      have hgN : g ∈ Subgroup.normalizer (P : Set (GLV V)) := (Subgroup.mem_inf.mp hg).2
      obtain ⟨h1, h2⟩ := g71_conj_hyp hgN hKP hKi
      refine (hSmem _).mpr ⟨⟨h1, h2⟩, ?_⟩
      rw [g71X_conj hgN]
      intro hbot
      apply hX
      have hfr := LinearEquiv.finrank_map_eq (g : GLV V) (g71X P K)
      rw [hbot, finrank_bot] at hfr
      exact Submodule.finrank_eq_zero.mp hfr.symm
    have hcard_le : ∀ K ∈ S, orbitLen (G ⊓ Subgroup.normalizer (P : Set (GLV V))) K ≤ S.ncard := by
      intro K hK
      unfold orbitLen
      apply Set.ncard_le_ncard _ hSfin
      rintro _ ⟨g, hg, rfl⟩
      exact hSorb K hK g hg
    have hK1S : K1 ∈ S := (hSmem K1).mpr ⟨⟨hK1P, hK1i⟩, hX1⟩
    have hnS : n ≤ S.ncard := (hmin K1 ⟨hK1P, hK1i⟩).trans (hcard_le K1 hK1S)
    have hT : ∀ K ∈ hSfin.toFinset, K ≤ P ∧ K.relIndex P = p := fun K hK => by
      obtain ⟨⟨h1, h2⟩, _⟩ := (hSmem K).mp ((Set.Finite.mem_toFinset hSfin).mp hK)
      exact ⟨h1, h2⟩
    have hind := g71_ind_le hp hcomm hPodd hSfin.toFinset hT
    have hterm : ∀ K ∈ hSfin.toFinset,
        orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (g71X P K) := by
      intro K hK
      obtain ⟨⟨h1, h2⟩, h3⟩ := (hSmem K).mp ((Set.Finite.mem_toFinset hSfin).mp hK)
      exact g71_ord_le hp hcomm hEexp hPodd h1 h2 h3
    have hcardT : S.ncard = hSfin.toFinset.card := Set.ncard_eq_toFinset_card S hSfin
    have hsum_lb : hSfin.toFinset.card * orderOf (2 : ZMod p) ≤
        ∑ K ∈ hSfin.toFinset, Module.finrank (ZMod 2) (g71X P K) := by
      have := Finset.card_nsmul_le_sum _ _ _ hterm
      simpa [smul_eq_mul] using this
    have hnord : n * orderOf (2 : ZMod p) ≤ hSfin.toFinset.card * orderOf (2 : ZMod p) :=
      Nat.mul_le_mul_right _ (by rw [← hcardT]; exact hnS)
    have hsumle : ∑ K ∈ hSfin.toFinset, Module.finrank (ZMod 2) (g71X P K) ≤
        Module.finrank (ZMod 2) V := le_trans (Nat.le_add_left _ _) hind
    refine ⟨?_, fun hdn H hH hv => ?_⟩
    · rw [← hd]
      exact hnord.trans (hsum_lb.trans hsumle)
    have hdV : Module.finrank (ZMod 2) V = n * orderOf (2 : ZMod p) := hd.trans hdn
    have hfix0 : Module.finrank (ZMod 2) (fixedSpace P) = 0 := by
      have h1 : Module.finrank (ZMod 2) (fixedSpace P) + ∑ K ∈ hSfin.toFinset,
          Module.finrank (ZMod 2) (g71X P K) ≤ ∑ K ∈ hSfin.toFinset,
          Module.finrank (ZMod 2) (g71X P K) := by
        calc _ ≤ Module.finrank (ZMod 2) V := hind
          _ = n * orderOf (2 : ZMod p) := hdV
          _ ≤ hSfin.toFinset.card * orderOf (2 : ZMod p) := hnord
          _ ≤ _ := hsum_lb
      omega
    have hfixbot : fixedSpace P = ⊥ := Submodule.finrank_eq_zero.mp hfix0
    have hsumeq : ∑ _K ∈ hSfin.toFinset, orderOf (2 : ZMod p) =
        ∑ K ∈ hSfin.toFinset, Module.finrank (ZMod 2) (g71X P K) := by
      rw [Finset.sum_const, smul_eq_mul]
      exact le_antisymm hsum_lb (hsumle.trans (hdV.le.trans hnord))
    have hterm_eq : ∀ K ∈ hSfin.toFinset,
        orderOf (2 : ZMod p) = Module.finrank (ZMod 2) (g71X P K) :=
      fun K hK => (Finset.sum_eq_sum_iff_of_le hterm).mp hsumeq K hK
    obtain ⟨v, hv0, hvH⟩ := hv
    have hXH : g71X P H = fixedSpace H := g71X_eq_fixed hfixbot
    have hXHne : g71X P H ≠ ⊥ := by
      rw [hXH]
      intro hb
      have hvmem : v ∈ fixedSpace H := hvH
      rw [hb, Submodule.mem_bot] at hvmem
      exact hv0 hvmem
    have hHT : H ∈ hSfin.toFinset :=
      (Set.Finite.mem_toFinset hSfin).mpr ((hSmem H).mpr ⟨hH, hXHne⟩)
    have hfeq := hterm_eq H hHT
    rw [hXH] at hfeq
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace H), Nat.card_zmod, ← hfeq]

@[expose] def G_7_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G : Subgroup (GLV V)) (d : ℕ),
    Module.finrank (ZMod 2) V = d →
    CFSG.IsQuasisimple ↥(fStarOf G) → CFSG.SectionRank.IsSQTKCat ↥(fStarOf G) →
    IsIrr (fStarOf G) ⊤ →
      ((∃ s : TauCeti.SporadicName, IsSporadic s (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G))) →
        10 ≤ d) ∧
      (∀ p e : ℕ, p.Prime → p ≠ 2 → 9 < p ^ e → IsPSL 2 p e ↥(fStarOf G) →
        6 < d ∧ (p ^ e ≠ 17 → 8 < d)) ∧
      (∀ (ε : Bool) (p : ℕ), p.Prime → p ≠ 2 →
        (IsPSLEps3 ε p 1 ↥(fStarOf G) ∨ IsSLEps3 ε p ↥(fStarOf G)) → d ≤ 8 →
          IsPSU 3 3 1 ↥(fStarOf G) ∧ d = 6) ∧
      (IsSporadic TauCeti.SporadicName.J4 ↥(fStarOf G) → 110 ≤ d) ∧
      (IsSporadic TauCeti.SporadicName.J2 ↥(fStarOf G) → 12 ≤ d) ∧
      ((IsSporadic TauCeti.SporadicName.HS ↥(fStarOf G) ∨
          IsSporadic TauCeti.SporadicName.He ↥(fStarOf G) ∨
          IsSporadic TauCeti.SporadicName.Ru ↥(fStarOf G)) → 20 ≤ d)

section G72

theorem as_G_7_2
    : G_7_2 := by
  intro V _ _ _ G d hd hq hS hirr
  subst hd
  exact ⟨fun h => RonanG72.ten_le_of_sporadic hq hS.1 hirr h,
    fun p e hp hp2 h9 hL => RonanG72.psl2_bound hp hp2 h9 hL,
    fun ε p hp hp2 hL hd => RonanG72.sl3_eps_bound hirr ε hp hp2 hL hd,
    RonanG72.j4_le, RonanG72.j2_le, RonanG72.hs_he_ru_le⟩

end G72

@[expose] def G_7_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G : Subgroup (GLV V)) [Finite ↥G] (d : ℕ),
    Module.finrank (ZMod 2) V = d →
    CFSG.IsQuasisimple ↥(fStarOf G) → CFSG.SectionRank.IsSQTKCat ↥(fStarOf G) →
    IsIrr (fStarOf G) ⊤ → d ≤ 2 * (CFSG.Open.twoRank ↥G + 1) →
      (IsLieTypeOddChar (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G)) →
        ((IsPSL 2 2 2 ↥(fStarOf G) ∨ IsPSL 3 2 1 ↥(fStarOf G) ∨
            Nonempty (↥(fStarOf G) ≃* ↥⁅StatedSp 2 (ZMod 2), StatedSp 2 (ZMod 2)⁆) ∨
            IsHat ↥(fStarOf G) ↥(alternatingGroup (Fin 6))) ∨
          (IsPSU 3 3 1 ↥(fStarOf G) ∧ d = 6))) ∧
      ((∃ s : TauCeti.SporadicName, IsSporadic s (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G))) →
        ((Nonempty (↥G ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M12) ∧
            IsPermCoreModule (fStarOf G) CFSG.Blueprint.NativeSporadic.M12) ∨
          (Nonempty (↥(fStarOf G) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧ d = 10 ∧
            IsMathieu22CodeOrCocode (fStarOf G)) ∨
          (Nonempty (↥(fStarOf G) ≃* ↥CFSG.Blueprint.NativeSporadic.M24) ∧ d = 11 ∧
            IsMathieu24CodeOrCocode (fStarOf G)) ∨
          (∃ N : Subgroup ↥G, N.Normal ∧ N.index = 2 ∧
            IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22 ∧ d = 12))) ∧
      (IsAlt 7 (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G)) →
        IsAlt 7 ↥(fStarOf G) ∧ (d = 4 ∨ d = 6))

section G73

theorem as_G_7_3
    : G_7_3 := by
  intro V _ _ _ G _ d hd hq hS hirr hbound
  subst hd
  obtain ⟨hLG, hnorm, hcent⟩ := RonanG73.fstar_facts G (fStarOf G) rfl
  obtain ⟨Γ, A, hΓG, hHyp⟩ := RonanG73.exists_g93Hyp hLG hnorm hq hS hirr hbound
  refine ⟨fun hodd => ?_, fun hs => ?_, fun hX => ?_⟩
  · exact RonanG73.clause1 hHyp hq hS hodd
  · exact RonanG73.clause2 hHyp hΓG hLG hnorm hcent hq hS.1 hs
  · exact RonanG73.clause3 hHyp hX

end G73

end CFSG.ASVolI
