module

public import CFSG.RankThree.PartOne.Q1327C.BL4Matrix

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.PartOne

variable {G : Type} [Group G]

abbrev cent (X Fix : Subgroup G) : Subgroup G :=
  X ⊓ Subgroup.centralizer (Fix : Set G)

abbrev centIncl (X Fix : Subgroup G) : ↥(cent X Fix) →* ↥X :=
  Subgroup.inclusion inf_le_left

section

variable {k : Type} [Field k] {X Fix : Subgroup G}

abbrev plane (ρ : ↥X →* SL4 k) (Fix : Subgroup G) : Subgroup (SL4 k) :=
  (Fix.subgroupOf X).map ρ

theorem rho_mem_centralizer (ρ : ↥X →* SL4 k) (c : ↥(cent X Fix)) :
    ρ (centIncl X Fix c) ∈
      Subgroup.centralizer ((plane ρ Fix : Subgroup (SL4 k)) : Set (SL4 k)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.1 c.2.2 (y : G) (Subgroup.mem_subgroupOf.1 hy)

theorem mem_cent_of_rho_mem {p : ℕ} (hp : p.Prime) (hZ : NoZ p X) {ρ : ↥X →* SL4 k}
    (hker : ρ.ker = Subgroup.center ↥X) (hFixX : Fix ≤ X) (hFixexp : ∀ a ∈ Fix, a ^ p = 1)
    {x : ↥X}
    (hx : ρ x ∈ Subgroup.centralizer ((plane ρ Fix : Subgroup (SL4 k)) : Set (SL4 k))) :
    (x : G) ∈ cent X Fix := by
  refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haX : a ∈ X := hFixX ha
  have ha' : (⟨a, haX⟩ : ↥X) ∈ Fix.subgroupOf X := ha
  have hcomm := Subgroup.mem_centralizer_iff.1 hx (ρ ⟨a, haX⟩) (Subgroup.mem_map_of_mem ρ ha')
  have hap : (⟨a, haX⟩ : ↥X) ^ p = 1 := Subtype.ext (hFixexp a ha)
  have hc : x * ⟨a, haX⟩ * x⁻¹ * ⟨a, haX⟩⁻¹ ∈ Subgroup.center ↥X := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have h1 := commutator_eq_one_of_central hp hZ hap hc
  have h2 : x * ⟨a, haX⟩ = ⟨a, haX⟩ * x := by
    calc x * ⟨a, haX⟩ = (x * ⟨a, haX⟩ * x⁻¹ * ⟨a, haX⟩⁻¹) * (⟨a, haX⟩ * x) := by group
      _ = ⟨a, haX⟩ * x := by rw [h1, one_mul]
  exact (congrArg Subtype.val h2).symm

@[expose] noncomputable def rhoC (ρ : ↥X →* SL4 k) (Fix : Subgroup G) :
    ↥(cent X Fix) →*
      ↥(Subgroup.centralizer ((plane ρ Fix : Subgroup (SL4 k)) : Set (SL4 k))) :=
  (ρ.comp (centIncl X Fix)).codRestrict _ (rho_mem_centralizer ρ)

theorem rhoC_surjective {p : ℕ} (hp : p.Prime) (hZ : NoZ p X) {ρ : ↥X →* SL4 k}
    (hsurj : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center ↥X) (hFixX : Fix ≤ X)
    (hFixexp : ∀ a ∈ Fix, a ^ p = 1) : Function.Surjective (rhoC ρ Fix) := by
  intro z
  obtain ⟨x, hx⟩ := hsurj z.1
  have hxC : (x : G) ∈ cent X Fix :=
    mem_cent_of_rho_mem hp hZ hker hFixX hFixexp (hx ▸ z.2)
  exact ⟨⟨x, hxC⟩, Subtype.ext hx⟩

theorem subgroupOf_map_eq (ρ : ↥X →* SL4 k) (K : Subgroup ↥(cent X Fix)) :
    (K.map (ρ.comp (centIncl X Fix))).subgroupOf
        (Subgroup.centralizer ((plane ρ Fix : Subgroup (SL4 k)) : Set (SL4 k))) =
      K.map (rhoC ρ Fix) := by
  ext z
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, hcz⟩
    exact ⟨c, hc, Subtype.ext hcz⟩
  · rintro ⟨c, hc, hcz⟩
    exact ⟨c, hc, congrArg Subtype.val hcz⟩

theorem injective_of_simple {H M : Type} [Group H] [Group M] (hH : IsSimpleGroup H) (f : H →* M)
    (hf : ¬ ∀ h, f h = 1) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact h
  · exact absurd (fun x => MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x)) hf

end

variable {k : Type} [Field k]

theorem l4_cell_card [Finite G] [Finite k] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X F Fix : Subgroup G} (hZ : NoZ p X) (hrk : p ∣ Nat.card kˣ)
    (hsimple2 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k)) (ρ : ↥X →* SL4 k)
    (hsurj : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center ↥X) (hFX : F ≤ X)
    (hFexp : ∀ a ∈ F, a ^ p = 1) (hFixF : Fix ≤ F) (hFixcard : Nat.card Fix = p ^ 2)
    (hdiag : ∀ x : ↥X, (x : G) ∈ F → ∃ D : Fin 4 → k,
      (ρ x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧ ∀ i, D i ^ p = 1)
    {Kc : Subgroup G} (hKperf : Group.IsPerfect ↥(Kc.subgroupOf (cent X Fix)))
    (hKsimple : IsSimpleGroup ↥(Kc.subgroupOf (cent X Fix)))
    (hKsub : (Kc.subgroupOf (cent X Fix)).IsSubnormal) :
    Nat.card ↥(Kc.subgroupOf (cent X Fix)) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
  classical
  have hFixX : Fix ≤ X := hFixF.trans hFX
  have hFixexp : ∀ a ∈ Fix, a ^ p = 1 := fun a ha => hFexp a (hFixF ha)
  have hFixp : IsPGroup p Fix := IsPGroup.of_card (n := 2) hFixcard
  set Kc' : Subgroup ↥(cent X Fix) := Kc.subgroupOf (cent X Fix) with hKc'
  set g : ↥(cent X Fix) →* SL4 k := ρ.comp (centIncl X Fix) with hg
  have : Group.IsPerfect ↥Kc' := hKperf
  have : Nontrivial ↥Kc' := hKsimple.toNontrivial
  have hkc : ¬ p ∣ Nat.card ρ.ker := by
    rw [hker]
    exact hZ
  have hdis : Disjoint (Fix.subgroupOf X) ρ.ker :=
    N143.disjoint_ker_of_isPGroup ρ hp (isPGroup_subgroupOf hFixX hFixp) hkc
  have hPcard : Nat.card (plane ρ Fix) = p ^ 2 := by
    rw [N143.card_map_of_disjoint_ker ρ hdis, ← hFixcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFixX).toEquiv
  have hPd : ∀ x ∈ plane ρ Fix, ∃ D : Fin 4 → k,
      (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧ ∀ i, D i ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdiag y (hFixF (Subgroup.mem_subgroupOf.1 hy))
  have hKmc : Kc'.map g ≤
      Subgroup.centralizer ((plane ρ Fix : Subgroup (SL4 k)) : Set (SL4 k)) := by
    rintro _ ⟨c, -, rfl⟩
    exact rho_mem_centralizer ρ c
  have hKmperf : Group.IsPerfect ↥(Kc'.map g) := Group.IsPerfect.map g
  have hKne : Kc'.map g ≠ ⊥ := by
    intro hbot
    have hcent : ∀ c ∈ Kc', centIncl X Fix c ∈ Subgroup.center ↥X := by
      intro c hc
      rw [← hker, MonoidHom.mem_ker]
      have : g c ∈ Kc'.map g := Subgroup.mem_map_of_mem g hc
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hcomm : ∀ a b : ↥Kc', a * b = b * a := by
      intro a b
      have h3 : ((a : ↥(cent X Fix)) : G) * ((b : ↥(cent X Fix)) : G) =
          ((b : ↥(cent X Fix)) : G) * ((a : ↥(cent X Fix)) : G) :=
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 (hcent a a.2) (centIncl X Fix b))).symm
      apply Subtype.ext
      apply Subtype.ext
      exact h3
    have : IsMulCommutative ↥Kc' := ⟨⟨hcomm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative ↥Kc' inferInstance
  have hKsub' : ((Kc'.map g).subgroupOf
      (Subgroup.centralizer ((plane ρ Fix : Subgroup (SL4 k)) : Set (SL4 k)))).IsSubnormal := by
    rw [hg, subgroupOf_map_eq]
    exact Subgroup.IsSubnormal.map (rhoC_surjective hp hZ hsurj hker hFixX hFixexp) hKsub
  have hcard := sl4_component_card hp hp5 hrk hPd hPcard hKmc hKmperf hKne hKsub' hsimple2
  rw [← hcard]
  have hinj : Function.Injective (g.comp Kc'.subtype) := by
    refine injective_of_simple hKsimple _ ?_
    intro hall
    apply hKne
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨c, hc, rfl⟩
    exact hall ⟨c, hc⟩
  have hdisK : Disjoint Kc' g.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    have h1 : (g.comp Kc'.subtype) ⟨x, hx⟩ = (g.comp Kc'.subtype) 1 := by
      rw [map_one]
      exact hxk
    exact congrArg Subtype.val (hinj h1)
  rw [N143.card_map_of_disjoint_ker g hdisK]

end CFSG.RankThree.PartOne.Q1327C
