module

import CFSG.LocalAnalysis.StandardType.GGOrthKStructEquivAux

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructInduces
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_induces_ext {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {σ τ : MulAut ↥Bs} {h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))}
    (hσ : InducesSigned K ψ Φ σ h) (hτ : InducesSigned K ψ Φ τ h) : σ = τ := by
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  obtain ⟨a, c, hc, hbc⟩ := okEq_mem_bs_decomp hψ hprod b.2
  have hmem : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs := by
    rw [hbc]; exact b.2
  have hb_eq : b = ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hmem⟩ :=
    Subtype.ext hbc.symm
  calc ((σ b : ↥Bs) : G)
      = ((σ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hmem⟩ : ↥Bs) : G) := by
        rw [hb_eq]
    _ = ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) * c := hσ a c hmem hc.2
    _ = ((τ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hmem⟩ : ↥Bs) : G) :=
        (hτ a c hmem hc.2).symm
    _ = ((τ b : ↥Bs) : G) := by rw [hb_eq]

theorem ggOrthKStruct_equiv {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n))
    (hup : ∀ σ ∈ ggAutomizer K Bs, ∃ h ∈ spSignedGroup ((n + 1) / 2) 3, InducesSigned K ψ Φ σ h)
    (hlow : ∀ h ∈ spSignedGroup ((n + 1) / 2) 3, ∃ σ ∈ ggAutomizer K Bs, InducesSigned K ψ Φ σ h) :
    ∃ E : ↥(ggAutomizer K Bs) ≃* ↥(spSignedGroup ((n + 1) / 2) 3),
      ∀ σ : ↥(ggAutomizer K Bs),
        InducesSigned K ψ Φ (σ : MulAut ↥Bs) ((E σ : ↥(spSignedGroup ((n + 1) / 2) 3)) : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))) := by
  classical
  let f : ↥(ggAutomizer K Bs) →* ↥(spSignedGroup ((n + 1) / 2) 3) :=
    { toFun := fun σ =>
        ⟨Classical.choose (hup σ σ.2), (Classical.choose_spec (hup σ σ.2)).1⟩
      map_one' := by
        apply Subtype.ext
        exact ggOrthKStruct_induces_unique hψ (Classical.choose_spec (hup 1 (1 : ↥(ggAutomizer K Bs)).2)).2
          (ggOrthKStruct_induces_one K ψ Φ)
      map_mul' := by
        intro σ τ
        apply Subtype.ext
        exact ggOrthKStruct_induces_unique hψ (Classical.choose_spec (hup (σ * τ) (σ * τ).2)).2
          (ggOrthKStruct_induces_mul (Classical.choose_spec (hup σ σ.2)).2
            (Classical.choose_spec (hup τ τ.2)).2) }
  have hf_inj : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    apply ggOrthKStruct_induces_ext hψ hprod (Classical.choose_spec (hup σ σ.2)).2
    have hv : Classical.choose (hup σ σ.2) = Classical.choose (hup τ τ.2) :=
      congrArg Subtype.val h
    rw [hv]
    exact (Classical.choose_spec (hup τ τ.2)).2
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨σ, hσmem, hσind⟩ := hlow y y.2
    refine ⟨⟨σ, hσmem⟩, ?_⟩
    apply Subtype.ext
    exact ggOrthKStruct_induces_unique hψ
      (Classical.choose_spec (hup σ hσmem)).2 hσind
  refine ⟨MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩, fun σ => ?_⟩
  exact (Classical.choose_spec (hup σ σ.2)).2

theorem ggOrthKStruct_card_fix {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {σ : MulAut ↥Bs} {h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))}
    (hσ : InducesSigned K ψ Φ σ h) :
    Nat.card {b : ↥Bs // σ b = b} =
      Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
  classical
  let toFun : ({a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} ×
      ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) → {b : ↥Bs // σ b = b} :=
    fun x =>
      let a := x.1.1
      let c := x.2
      have hmem : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (c : G) ∈ Bs :=
        Bs.mul_mem (hψ.torus_le (Subgroup.mem_map_of_mem ψ (Φ a).2)) c.2.1
      have hfix : σ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (c : G), hmem⟩ =
          ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (c : G), hmem⟩ := by
        apply Subtype.ext
        rw [hσ a (c : G) hmem c.2.2, x.1.2]
      ⟨⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (c : G), hmem⟩, hfix⟩
  have hinj : Function.Injective toFun := by
    rintro ⟨⟨a, ha⟩, c⟩ ⟨⟨a', ha'⟩, c'⟩ hh
    have hval : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (c : G) =
        ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * (c' : G) := by
      simpa only [toFun] using congrArg Subtype.val (congrArg Subtype.val hh)
    obtain ⟨haa, hcc⟩ := okEq_decomp_unique hψ c.2 c'.2 hval
    exact Prod.ext (Subtype.ext haa) (Subtype.ext hcc)
  have hsurj : Function.Surjective toFun := by
    rintro ⟨b, hb⟩
    obtain ⟨a, c, hc, hbc⟩ := okEq_mem_bs_decomp hψ hprod b.2
    have hmem : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs := by
      rw [hbc]; exact b.2
    have hb_eq : b = ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hmem⟩ :=
      Subtype.ext hbc.symm
    have hfix : h a = a := by
      have h1 : (σ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hmem⟩ : G) =
          ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c := by
        have h2 := congrArg Subtype.val hb
        rw [hb_eq] at h2
        simpa using h2
      rw [hσ a c hmem hc.2] at h1
      exact okEq_psi_Phi_injective hψ (mul_right_cancel h1)
    refine ⟨(⟨a, hfix⟩, ⟨c, hc⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c = (b : G)
    exact hbc
  calc Nat.card {b : ↥Bs // σ b = b}
      = Nat.card ({a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} ×
          ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) :=
        (Nat.card_congr (Equiv.ofBijective toFun ⟨hinj, hsurj⟩)).symm
    _ = Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_prod _ _

theorem ggOrthKStruct_isRefl_iff {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {σ : MulAut ↥Bs} {h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))}
    (hσ : InducesSigned K ψ Φ σ h) :
    GGIsReflection 3 σ ↔
      (h * h = 1 ∧ Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} * 3 = 3 ^ ((n + 1) / 2)) := by
  have hpow : σ ^ 2 = 1 ↔ h * h = 1 := by
    constructor
    · intro h2
      have hmul : InducesSigned K ψ Φ (σ * σ) (h * h) := ggOrthKStruct_induces_mul hσ hσ
      have h1 : InducesSigned K ψ Φ (1 : MulAut ↥Bs) 1 := ggOrthKStruct_induces_one K ψ Φ
      have h2' : σ * σ = 1 := by rwa [pow_two] at h2
      rw [h2'] at hmul
      exact ggOrthKStruct_induces_unique hψ hmul h1
    · intro hh
      have hmul : InducesSigned K ψ Φ (σ * σ) (h * h) := ggOrthKStruct_induces_mul hσ hσ
      have h1 : InducesSigned K ψ Φ (1 : MulAut ↥Bs) 1 := ggOrthKStruct_induces_one K ψ Φ
      rw [hh] at hmul
      have h2' : σ * σ = 1 := ggOrthKStruct_induces_ext hψ hprod hmul h1
      rwa [pow_two]
  have hcardσ := ggOrthKStruct_card_fix hψ hprod hσ
  have hcard1 := ggOrthKStruct_card_fix hψ hprod (ggOrthKStruct_induces_one K ψ Φ)
  have hcardBs : Nat.card {b : ↥Bs // (1 : MulAut ↥Bs) b = b} = Nat.card ↥Bs :=
    Nat.card_eq_of_bijective Subtype.val
      ⟨fun x y hxy => Subtype.ext hxy, fun y => ⟨⟨y, by simp⟩, rfl⟩⟩
  have hcardV : Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) //
      (1 : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))) a = a} =
      Nat.card (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) :=
    Nat.card_eq_of_bijective Subtype.val
      ⟨fun x y hxy => Subtype.ext hxy, fun y => ⟨⟨y, by simp⟩, rfl⟩⟩
  have hBs : Nat.card ↥Bs = Nat.card (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← hcardBs, hcard1, hcardV]
  have hV : Nat.card (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) = 3 ^ ((n + 1) / 2) :=
    okEq_card_coords ((n + 1) / 2)
  haveI : Nonempty ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    ⟨⟨1, Subgroup.one_mem _⟩⟩
  have hmpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  have hcardiff : Nat.card {b : ↥Bs // σ b = b} * 3 = Nat.card ↥Bs ↔
      Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} * 3 =
        3 ^ ((n + 1) / 2) := by
    rw [hcardσ, hBs, hV]
    constructor
    · intro hh
      have hh' : Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} * 3 *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) =
          3 ^ ((n + 1) / 2) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
        calc Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} * 3 *
              Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G))
            = Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} *
              Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) * 3 := by ring
          _ = 3 ^ ((n + 1) / 2) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := hh
      exact Nat.eq_of_mul_eq_mul_right hmpos hh'
    · intro hh
      calc Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) * 3
          = Nat.card {a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) // h a = a} * 3 *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by ring
        _ = 3 ^ ((n + 1) / 2) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by rw [hh]
  rw [GGIsReflection]
  exact and_congr hpow hcardiff

end CFSG.StandardType

end
