module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2b
import CFSG.Quasithin.Background.GoldschmidtE23SymFin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem eq_one_of_secNatS5 {H : Subgroup G} {U : Submodule (ZMod 2) V}
    (hS5 : SecNatS5 ρ H U ⊥) {h : G} (hh : h ∈ H) (hU : ∀ u ∈ U, ρ h u = u) : h = 1 := by
  obtain ⟨-, -, -, φ, ψ, -, -, -, hsurj, hE⟩ := hS5
  have h1 : φ ⟨h, hh⟩ = 1 := by
    refine CFSG.Quasithin.GE23.eq_one_of_fixed_all _ fun y hy i => ?_
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    have h2 : ψ (ρ h x) i = ψ x ((φ ⟨h, hh⟩).symm i) := congrFun (hE ⟨h, hh⟩ x hx) i
    rw [hU x hx] at h2
    exact h2.symm
  have h3 : (⟨h, hh⟩ : ↥H) = 1 := φ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h3

theorem not_apply_eq_of_secNatS5 {L : Subgroup G} {a : G} (haL : a ∉ L)
    (hS5 : SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥) {l : G} (hl : l ∈ L) :
    ¬ ∀ u ∈ commOn ρ L ⊤, ρ a u = ρ l u := by
  intro h
  have h1 : l⁻¹ * a = 1 := eq_one_of_secNatS5 hS5
    (mul_mem (inv_mem (Subgroup.mem_sup_left hl))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
    fun u hu => by rw [glRep_mul_apply, h u hu, glRep_inv_apply]
  rw [inv_mul_eq_one] at h1
  exact haL (h1 ▸ hl)

theorem apply_eq_self_of_commute_of_secNatS5 {L : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (haL : a ∉ L)
    (hS5 : SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥) {c : G}
    (hc : ∀ l ∈ L, c * l = l * c) : ∀ u ∈ commOn ρ L ⊤, ρ c u = u := by
  obtain ⟨-, -, -, φ, ψ, -, hK, hsum, hsurj, hE⟩ := hS5
  have hnorm : ∀ m ∈ L, a * m * a⁻¹ ∈ L := fun m hm =>
    (Subgroup.mem_normalizer_iff.1 haN m).1 hm
  have hmap := map_subgroupOf_eq_alternatingGroup ha2 hnorm haL φ
  have hA5 : ∀ τ ∈ alternatingGroup (Fin 5), ∃ l ∈ L, ∀ x ∈ commOn ρ L ⊤,
      ρ l x ∈ commOn ρ L ⊤ ∧ ψ (ρ l x) = fun i => ψ x (τ.symm i) := by
    intro τ hτ
    rw [← hmap, Subgroup.mem_map_equiv] at hτ
    have hτL : ((φ.symm τ : ↥(L ⊔ Subgroup.zpowers a)) : G) ∈ L := Subgroup.mem_subgroupOf.1 hτ
    refine ⟨(φ.symm τ : G), hτL, fun x hx =>
      ⟨commOn_top_mapsTo (Subgroup.le_normalizer hτL) hx, ?_⟩⟩
    rw [hE (φ.symm τ) x hx, MulEquiv.apply_symm_apply]
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun l hl => (hc l hl).symm)
  exact apply_eq_self_of_commute_of_perm ψ (fun x hx h0 => (Submodule.mem_bot _).1 (hK x hx h0))
    hsum hsurj hA5 (fun u hu => commOn_top_mapsTo hcN hu) hc

theorem secNatS5_of_forall_exists_eq_apply [Finite G] {H H' : Subgroup G}
    {U : Submodule (ZMod 2) V} (hS5 : SecNatS5 ρ H U ⊥)
    (hfaith : ∀ h ∈ H', (∀ u ∈ U, ρ h u = u) → h = 1)
    (hact : ∀ h ∈ H', ∃ h₀ ∈ H, ∀ u ∈ U, ρ h u = ρ h₀ u)
    (hcard : Nat.card ↥H ≤ Nat.card ↥H') : SecNatS5 ρ H' U ⊥ := by
  have hdet : ∀ y z : ↥H, (∀ u ∈ U, ρ y u = ρ z u) → y = z := fun y z hyz => by
    have h1 := eq_one_of_secNatS5 hS5 (mul_mem (inv_mem y.2) z.2) fun u hu => by
      rw [glRep_mul_apply, ← hyz u hu, glRep_inv_apply]
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  obtain ⟨hinv, -, -, φ, ψ, hB, hK, hsum, hsurj, hE⟩ := hS5
  have hex : ∀ x : ↥H', ∃ y : ↥H, ∀ u ∈ U, ρ x u = ρ y u := fun x => by
    obtain ⟨h₀, hh₀, he⟩ := hact x x.2
    exact ⟨⟨h₀, hh₀⟩, he⟩
  choose g hg using hex
  let F : ↥H' →* ↥H :=
    { toFun := g
      map_one' := hdet _ _ fun u hu => by rw [← hg 1 u hu]; simp
      map_mul' := fun x y => hdet _ _ fun u hu => by
        calc ρ (g (x * y) : G) u = ρ ((x * y : ↥H') : G) u := (hg (x * y) u hu).symm
          _ = ρ (x : G) (ρ (y : G) u) := by rw [Subgroup.coe_mul, glRep_mul_apply]
          _ = ρ (x : G) (ρ (g y : G) u) := by rw [hg y u hu]
          _ = ρ (g x : G) (ρ (g y : G) u) := hg x _ (hinv _ (g y).2 u hu)
          _ = ρ ((g x * g y : ↥H) : G) u := by rw [Subgroup.coe_mul, glRep_mul_apply] }
  have hinj : Function.Injective F := fun x y hxy => by
    have hxy' : g x = g y := hxy
    have h1 : (x : G)⁻¹ * y = 1 := hfaith _ (mul_mem (inv_mem x.2) y.2) fun u hu => by
      rw [glRep_mul_apply, hg y u hu, ← hxy', ← hg x u hu, glRep_inv_apply]
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  let e : ↥H' ≃* ↥H := MulEquiv.ofBijective F (hinj.bijective_of_nat_card_le hcard)
  refine ⟨fun h hh u hu => ?_, fun h _ u hu => ?_, bot_le, e.trans φ, ψ, hB, hK, hsum, hsurj,
    fun h x hx => ?_⟩
  · have h1 : ρ h u = ρ (g ⟨h, hh⟩ : G) u := hg ⟨h, hh⟩ u hu
    rw [h1]
    exact hinv _ (g ⟨h, hh⟩).2 u hu
  · rw [(Submodule.mem_bot _).1 hu, map_zero]
    exact zero_mem _
  · rw [hg h x hx, hE (g h) x hx]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
