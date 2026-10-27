module

public import CFSG.LocalAnalysis.StandardType.GGQ2SubStab
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
import CFSG.LocalAnalysis.StandardType.GGCartanATypeArith
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import CFSG.LocalAnalysis.StandardType.GGTBTorDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggQ2TN_heart [Module.Finite (ZMod 3) V] {m : ℕ} (hdim : Module.finrank (ZMod 3) V = m)
    (c : Fin m → V) (α : Fin m → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A m i j : ZMod 3))
    (x : V) (hxH : x ∉ Submodule.span (ZMod 3) (Set.range c)) (hxfix : ∀ i, α i x = 0) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) = m - 1 ∧
      Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) {x} = ⊤ ∧
      (∀ z ∈ Submodule.span (ZMod 3) (Set.range c), (∀ i, α i z = 0) → z = 0) ∧
      ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x} := by
  classical
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c)
  let f : (Fin m → ZMod 3) →ₗ[ZMod 3] V := Fintype.linearCombination (ZMod 3) c
  have hrange : LinearMap.range f = H := by
    simp [f, H]
  have hrow : ∀ b : Fin m → ZMod 3, (∀ j, α j (f b) = 0) →
      ∀ j, ∑ k, (CartanMatrix.A m j k : ZMod 3) * b k = 0 := by
    intro b hb j
    have hh : α j (∑ k, b k • c k) = 0 := hb j
    simp only [map_sum, map_smul, hpair, smul_eq_mul] at hh
    calc ∑ k, (CartanMatrix.A m j k : ZMod 3) * b k
        = ∑ k, b k * (CartanMatrix.A m j k : ZMod 3) := by
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = 0 := hh
  have hrow0 : ∀ b : Fin m → ZMod 3, f b = 0 →
      ∀ j, ∑ k, (CartanMatrix.A m j k : ZMod 3) * b k = 0 :=
    fun b hb => hrow b fun j => by rw [hb, map_zero]
  have hker_le : Module.finrank (ZMod 3) (LinearMap.ker f) ≤ 1 := by
    by_cases hbot : LinearMap.ker f = ⊥
    · rw [hbot, finrank_bot]
      omega
    · obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hbot
      refine finrank_le_one (R := ZMod 3) ⟨v, hv_mem⟩ ?_
      rintro ⟨w, hw_mem⟩
      have hvA : ∀ j, ∑ k, (CartanMatrix.A m j k : ZMod 3) * v k = 0 :=
        hrow0 v (LinearMap.mem_ker.mp hv_mem)
      have hwA : ∀ j, ∑ k, (CartanMatrix.A m j k : ZMod 3) * w k = 0 :=
        hrow0 w (LinearMap.mem_ker.mp hw_mem)
      obtain ⟨l, hl⟩ := ggCartanA_ker_le_one (p := 3) (N := m) v w hvA hwA hv_ne
      exact ⟨l, Subtype.ext hl.symm⟩
  have hrn : Module.finrank (ZMod 3) H + Module.finrank (ZMod 3) (LinearMap.ker f) = m := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange] at this
    simpa using this
  have hH_ge : m - 1 ≤ Module.finrank (ZMod 3) H := by omega
  have hH_lt : Module.finrank (ZMod 3) H < m := by
    have hne : H ≠ ⊤ := by
      intro htop
      exact hxH ((Submodule.eq_top_iff'.mp htop) x)
    have hlt := Submodule.finrank_lt (K := ZMod 3) (V := V) (s := H) hne
    rwa [hdim] at hlt
  by_cases hm0 : m = 0
  · subst hm0
    exact absurd hH_lt (by omega)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hH_eq : Module.finrank (ZMod 3) H = m - 1 := by omega
  have hsup : H ⊔ Submodule.span (ZMod 3) {x} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hxH, hH_eq, hdim]
    omega
  have hkerfin : Module.finrank (ZMod 3) (LinearMap.ker f) = 1 := by omega
  have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hkerfin
    omega
  obtain ⟨b, hb_mem, hb_ne⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hker_ne_bot
  have hbA : ∀ j, ∑ k, (CartanMatrix.A m j k : ZMod 3) * b k = 0 :=
    hrow0 b (LinearMap.mem_ker.mp hb_mem)
  have hkerH : ∀ z ∈ H, (∀ i, α i z = 0) → z = 0 := by
    intro z hz hzα
    rw [← hrange] at hz
    obtain ⟨a, rfl⟩ := hz
    have haA : ∀ j, ∑ k, (CartanMatrix.A m j k : ZMod 3) * a k = 0 := hrow a hzα
    by_cases ha0 : a = 0
    · rw [ha0, map_zero]
    · obtain ⟨l, hl⟩ := ggCartanA_ker_le_one (p := 3) (N := m) b a hbA haA hb_ne
      rw [hl, map_smul, LinearMap.mem_ker.mp hb_mem, smul_zero]
  have hfixspan : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x} := by
    intro z hzα
    have hzmem : z ∈ H ⊔ Submodule.span (ZMod 3) {x} := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨h, hh, y, hy, hhy⟩ := Submodule.mem_sup.mp hzmem
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨t, rfl⟩ := hy
    have hαh : ∀ i, α i h = 0 := by
      intro i
      have hz := hzα i
      rw [← hhy] at hz
      simpa [map_add, map_smul, hxfix i] using hz
    have hh0 : h = 0 := hkerH h hh hαh
    rw [← hhy, hh0, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x))
  exact ⟨hH_eq, hsup, hkerH, hfixspan⟩

theorem ggQ2TN_conn {m : ℕ} (c : Fin m → V) (α : Fin m → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A m i j : ZMod 3)) :
    ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j := by
  classical
  have hsymm : ∀ a b : Fin m, CartanMatrix.A m a b = CartanMatrix.A m b a := by
    intro a b
    have h := congrFun (congrFun (CartanMatrix.A_isSymm m) a) b
    simpa using h.symm
  have hrel : ∀ a b : Fin m,
      ((α a (c b) ≠ 0) ∧ (α b (c a) ≠ 0)) ↔ ggCartanAMod m 3 a b ≠ 0 := by
    intro a b
    have hba : (CartanMatrix.A m b a : ZMod 3) = (CartanMatrix.A m a b : ZMod 3) := by
      rw [hsymm b a]
    rw [hpair a b, hpair b a, hba]
    constructor
    · rintro ⟨h, -⟩
      simpa [ggCartanAMod] using h
    · intro h
      exact ⟨by simpa [ggCartanAMod] using h, by simpa [ggCartanAMod] using h⟩
  intro i j
  have hmono := Relation.ReflTransGen.mono
    (r := fun a b : Fin m => ggCartanAMod m 3 a b ≠ 0)
    (p := fun a b : Fin m => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0)
    (fun a b hab => (hrel a b).mpr hab)
  exact hmono i j (ggCartanAMod_conn m 3 i j)

theorem ggQ2TN_card_le [Module.Finite (ZMod 3) V] {m : ℕ} (hdim : Module.finrank (ZMod 3) V = m)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (c : Fin m → V) (s : Fin m → (V ≃ₗ[ZMod 3] V)) (x : V)
    (hsup : Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) {x} = ⊤)
    (hcardW : Nat.card (Subgroup.closure (Set.range s)) = (m + 1).factorial)
    (hStab : ∀ g ∈ A, g x = x → ∃ w ∈ Subgroup.closure (Set.range s), ∃ ε : ZMod 3,
      ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), g h = ε • w h) :
    Nat.card A ≤ 3 ^ m * (3 * (m + 1).factorial) := by
  classical
  have hVfin : Finite V := Module.finite_of_finite (R := ZMod 3)
  have hVVfin : Finite (V → V) := @Pi.finite V (fun _ => V) hVfin (fun _ => hVfin)
  have hEfin : Finite (V ≃ₗ[ZMod 3] V) :=
    @Finite.of_injective (V ≃ₗ[ZMod 3] V) (V → V) hVVfin
      (fun e => (e : V → V)) (fun e1 e2 h => LinearEquiv.ext (congrFun h))
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c)
  let W : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range s)
  have hWcard : Nat.card W = (m + 1).factorial := hcardW
  have hOS : Nat.card A =
      Nat.card (MulAction.orbit A x) * Nat.card (MulAction.stabilizer A x) := by
    rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A x), Nat.card_prod]
  have horbit : Nat.card (MulAction.orbit A x) ≤ Nat.card V :=
    @Nat.card_le_card_of_injective (MulAction.orbit A x) V hVfin
      (fun y : MulAction.orbit A x => (y : V)) fun a b h => Subtype.ext h
  have hVcard : Nat.card V = 3 ^ m := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), hdim, Nat.card_zmod]
  let F : ZMod 3 × W → (H → V) := fun p h => p.1 • ((p.2 : W) : V ≃ₗ[ZMod 3] V) h
  let ρ : MulAction.stabilizer A x → (H → V) :=
    fun g h => ((g : A) : V ≃ₗ[ZMod 3] V) h
  have hρinj : Function.Injective ρ := by
    intro g1 g2 hρ
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ H ⊔ Submodule.span (ZMod 3) {x} := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨h, hh, y, hy, hhy⟩ := Submodule.mem_sup.mp hv
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨t, rfl⟩ := hy
    have hg1x : ((g1 : A) : V ≃ₗ[ZMod 3] V) x = x := by
      simpa only [Subgroup.smul_def, LinearEquiv.smul_def] using
        (MulAction.mem_stabilizer_iff.mp g1.2)
    have hg2x : ((g2 : A) : V ≃ₗ[ZMod 3] V) x = x := by
      simpa only [Subgroup.smul_def, LinearEquiv.smul_def] using
        (MulAction.mem_stabilizer_iff.mp g2.2)
    have hh_eq : ((g1 : A) : V ≃ₗ[ZMod 3] V) h = ((g2 : A) : V ≃ₗ[ZMod 3] V) h := by
      have := congrFun hρ ⟨h, hh⟩
      simpa [ρ] using this
    calc ((g1 : A) : V ≃ₗ[ZMod 3] V) v
        = ((g1 : A) : V ≃ₗ[ZMod 3] V) (h + t • x) := by rw [← hhy]
      _ = ((g1 : A) : V ≃ₗ[ZMod 3] V) h + t • ((g1 : A) : V ≃ₗ[ZMod 3] V) x := by
          rw [map_add, map_smul]
      _ = ((g2 : A) : V ≃ₗ[ZMod 3] V) h + t • ((g2 : A) : V ≃ₗ[ZMod 3] V) x := by
          rw [hh_eq, hg1x, hg2x]
      _ = ((g2 : A) : V ≃ₗ[ZMod 3] V) (h + t • x) := by rw [map_add, map_smul]
      _ = ((g2 : A) : V ≃ₗ[ZMod 3] V) v := by rw [hhy]
  have hrangeρ : ∀ g : MulAction.stabilizer A x, ρ g ∈ Set.range F := by
    intro g
    have hgx : ((g : A) : V ≃ₗ[ZMod 3] V) x = x := by
      simpa only [Subgroup.smul_def, LinearEquiv.smul_def] using
        (MulAction.mem_stabilizer_iff.mp g.2)
    obtain ⟨w, hw, ε, hε⟩ := hStab ((g : A) : V ≃ₗ[ZMod 3] V) (g : A).2 hgx
    refine ⟨(ε, ⟨w, hw⟩), ?_⟩
    funext h
    simpa [F, ρ] using (hε h h.2).symm
  let ρ' : MulAction.stabilizer A x → Set.range F := fun g => ⟨ρ g, hrangeρ g⟩
  have hρ'inj : Function.Injective ρ' := by
    intro g1 g2 h
    apply hρinj
    exact congrArg Subtype.val h
  have hHfin : Finite H := @Subtype.finite V hVfin (fun x => x ∈ H)
  have hHV : Finite (H → V) := @Pi.finite H (fun _ => V) hHfin (fun _ => hVfin)
  have hRF : Finite (Set.range F) :=
    @Subtype.finite (H → V) hHV (fun y => y ∈ Set.range F)
  have hWfin : Finite W :=
    @Subtype.finite (V ≃ₗ[ZMod 3] V) hEfin (fun w => w ∈ W)
  have hFW : Fintype W := @Fintype.ofFinite W hWfin
  have hFZW : Fintype (ZMod 3 × W) :=
    @instFintypeProd (ZMod 3) W (Fintype.ofFinite (ZMod 3)) hFW
  have hZW : Finite (ZMod 3 × W) := @Finite.of_fintype (ZMod 3 × W) hFZW
  have hstab_card : Nat.card (MulAction.stabilizer A x) ≤ Nat.card (ZMod 3 × W) := by
    calc Nat.card (MulAction.stabilizer A x)
        ≤ Nat.card (Set.range F) :=
          @Nat.card_le_card_of_injective (MulAction.stabilizer A x) (Set.range F) hRF ρ' hρ'inj
      _ ≤ Nat.card (ZMod 3 × W) := by
          refine @Nat.card_le_card_of_surjective (ZMod 3 × W) (Set.range F) hZW
            (fun p : ZMod 3 × W => ⟨F p, Set.mem_range_self p⟩) ?_
          intro y
          obtain ⟨p, hp⟩ := y.2
          exact ⟨p, Subtype.ext hp⟩
  have hprod : Nat.card (ZMod 3 × W) = 3 * (m + 1).factorial := by
    rw [Nat.card_prod, Nat.card_zmod, hWcard]
  calc Nat.card A
      = Nat.card (MulAction.orbit A x) * Nat.card (MulAction.stabilizer A x) := hOS
    _ ≤ 3 ^ m * (3 * (m + 1).factorial) :=
        Nat.mul_le_mul (horbit.trans_eq hVcard) (hstab_card.trans_eq hprod)

end CFSG.StandardType

end
