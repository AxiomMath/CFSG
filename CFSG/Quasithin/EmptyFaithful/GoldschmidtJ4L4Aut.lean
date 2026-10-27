module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Alt8
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.J4L4

local notation "A₈" => alternatingGroup (Fin 8)

theorem card_mulAut_le {V : Type*} [Group V] [Finite V] (a b c : V)
    (h : Subgroup.closure ({a, b, c} : Set V) = ⊤) : Nat.card (MulAut V) ≤ Nat.card V ^ 3 := by
  have hinj : Function.Injective (fun φ : MulAut V => (φ a, φ b, φ c)) := by
    intro φ ψ hφψ
    simp only [Prod.mk.injEq] at hφψ
    obtain ⟨h1, h2, h3⟩ := hφψ
    have : φ.toMonoidHom = ψ.toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_dense h ?_
      rintro x (rfl | rfl | rfl)
      · exact h1
      · exact h2
      · exact h3
    exact MulEquiv.ext fun x => DFunLike.congr_fun this x
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_prod] at this
  calc Nat.card (MulAut V) ≤ Nat.card V * (Nat.card V * Nat.card V) := this
    _ = Nat.card V ^ 3 := by ring

theorem finite_mulAut {V : Type*} [Group V] [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun φ : MulAut V => (φ : V → V)) fun _ _ h => MulEquiv.ext fun x =>
    congrFun h x

theorem surjective_comp_inclusion_centralizer {G : Type*} [Group G] [Finite G]
    {V B : Subgroup G} (hV : Nat.card (MulAut V) < 20160)
    (hB : B ≤ Subgroup.normalizer (V : Set G)) (f : ↥B →* A₈) (hf : Function.Surjective f) :
    Function.Surjective (f.comp (Subgroup.inclusion
      (inf_le_left : B ⊓ Subgroup.centralizer (V : Set G) ≤ B))) := by
  have hsimple : IsSimpleGroup A₈ := alternatingGroup.isSimpleGroup (by simp)
  have : Finite (MulAut V) := finite_mulAut
  let ρ : ↥B →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hB)
  have hkerρ : ∀ x : ↥B, x ∈ ρ.ker ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro x
    have h := Subgroup.ext_iff.1 (Subgroup.normalizerMonoidHom_ker (H := V))
      (Subgroup.inclusion hB x)
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  have hn : (ρ.ker.map f).Normal := (MonoidHom.normal_ker ρ).map f hf
  have hne : ρ.ker.map f ≠ ⊥ := by
    intro h
    have hle : ρ.ker ≤ f.ker := fun x hx => by
      have : f x ∈ ρ.ker.map f := Subgroup.mem_map_of_mem f hx
      rw [h, Subgroup.mem_bot] at this
      exact this
    have h1 : f.ker.index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hle
    have h2 : f.ker.index = 20160 := by
      have e1 := Subgroup.card_mul_index f.ker
      have e2 := Subgroup.card_ker_mul_card_of_surjective hf
      rw [card_alt8] at e2
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (e1.trans e2.symm)
    have h3 : ρ.ker.index ≤ Nat.card (MulAut V) := by
      rw [Subgroup.index_ker]
      exact Subgroup.card_le_card_group _
    have h4 : 20160 ≤ ρ.ker.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (h2 ▸ h1)
    omega
  have htop : ρ.ker.map f = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal _).resolve_left hne
  intro y
  have hy : y ∈ ρ.ker.map f := htop ▸ Subgroup.mem_top y
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨(x : G), x.2, (hkerρ x).1 hx⟩, rfl⟩

end CFSG.Quasithin.J4L4
