module

public import CFSG.RankThree.GF2n.Tim81.Sec6.S65Local
import CFSG.CGT.Timmesfeld75.Sec7OneDihedral

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld
open CFSG.Timmesfeld.Bridge

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}
variable {U B : Subgroup G} {α β : G}

@[expose] def badSet (V : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ A ∈ omegaSet V, ∃ C ∈ omegaSet V, ∃ a ∈ A, ∃ c ∈ C, BadPair a c ∧ X = A ⊔ C}

structure MinBad (V U B : Subgroup G) (α β : G) : Prop where
  memB : B ∈ omegaSet V
  eq_sup : U = V ⊔ B
  memα : α ∈ V
  memβ : β ∈ B
  bad : BadPair α β
  min : ∀ X ∈ badSet V, Nat.card U ≤ Nat.card X

@[expose] def EU (V U : Subgroup G) : Set G :=
  {x | x ∈ Tim78.classD V ∧ ∃ A ∈ omegaSet V, A ≤ U ∧ x ∈ A}

abbrev UBar (U : Subgroup G) : Type := ↥U ⧸ Subgroup.center ↥U

@[expose] def EBar (V U : Subgroup G) : Set (UBar U) :=
  {x | ∃ u : ↥U, (u : G) ∈ EU V U ∧ (u : UBar U) = x}

structure Twin (M V U : Subgroup G) (α : G) (H : Subgroup G) (h₀ y₀ z₀ : G) : Prop where
  mem_ZU : z₀ ∈ ZU U
  sq : z₀ * z₀ = 1
  not_mem : z₀ ∉ V
  shape : Sec45Shape M V H h₀
  mem_H : y₀ ∈ H
  ne : conjSubgroup y₀ V ≠ V
  le : conjSubgroup y₀ V ≤ U
  sigma : conjSubgroup y₀ V ∈ sigmaSet M V
  mem : α * z₀ ∈ conjSubgroup y₀ V

theorem exists_minBad {d e : G} (hd : d ∈ Tim78.classD V) (he : e ∈ Tim78.classD V)
    (hb : BadPair d e) : ∃ U B α β, MinBad V U B α β := by
  classical
  obtain ⟨D, hD, hdD⟩ := exists_omegaSet_of_mem_classD hd
  obtain ⟨C, hC, heC⟩ := exists_omegaSet_of_mem_classD he
  have hbad : D ⊔ C ∈ badSet V :=
    ⟨D, hD, C, hC, d, hdD, e, heC, hb, rfl⟩
  have hex : ∃ n : ℕ, ∃ X ∈ badSet V, Nat.card X = n :=
    ⟨Nat.card ↥(D ⊔ C), D ⊔ C, hbad, rfl⟩
  obtain ⟨X, hX, hXcard⟩ := Nat.find_spec hex
  obtain ⟨A, hA, C', hC', a, haA, c, hcC, hbade, rfl⟩ := hX
  obtain ⟨g, -, rfl⟩ := Tim79a.mem_omegaOf.mp hA
  let α : G := g⁻¹ * a * g
  let β : G := g⁻¹ * c * g
  let B : Subgroup G := conjSubgroup g⁻¹ C'
  let U : Subgroup G := V ⊔ B
  have hα : α ∈ V := mem_conjSubgroup.mp haA
  have hβ : β ∈ B := by
    change β ∈ conjSubgroup g⁻¹ C'
    rw [mem_conjSubgroup]
    rwa [show (g⁻¹)⁻¹ * (g⁻¹ * c * g) * g⁻¹ = c by group]
  have hB : B ∈ omegaSet V := by
    obtain ⟨k, -, hk⟩ := Tim79a.mem_omegaOf.mp hC'
    refine Tim79a.mem_omegaOf.mpr ⟨g⁻¹ * k, Subgroup.mem_top _, ?_⟩
    show conjSubgroup g⁻¹ C' = conjSubgroup (g⁻¹ * k) V
    rw [hk, ← conjSubgroup_mul]
  have hbad' : BadPair α β := by
    have hsem : SemiconjBy g⁻¹ (a * c) (α * β) := by
      show g⁻¹ * (a * c) = (α * β) * g⁻¹
      simp only [α, β]
      group
    have hord : orderOf (α * β) = orderOf (a * c) := hsem.orderOf_eq.symm
    simpa [BadPair, hord] using hbade
  have hU : U = conjSubgroup g⁻¹ (conjSubgroup g V ⊔ C') := by
    show V ⊔ conjSubgroup g⁻¹ C' = conjSubgroup g⁻¹ (conjSubgroup g V ⊔ C')
    rw [CGT.Timmesfeld75.conjSubgroup_sup_eq_sup,
      CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hcard : Nat.card U = Nat.card ↥(conjSubgroup g V ⊔ C') := by
    rw [hU, card_conjSubgroup]
  refine ⟨U, B, α, β, hB, rfl, hα, hβ, hbad', ?_⟩
  intro Y hY
  rw [hcard, hXcard]
  exact Nat.find_min' hex ⟨Y, hY, rfl⟩

theorem mem_center_iff_mem_ZU {U : Subgroup G} {x : ↥U} :
    x ∈ Subgroup.center ↥U ↔ (x : G) ∈ ZU U := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨x.2, fun y hy => congrArg Subtype.val (h ⟨y, hy⟩)⟩
  · rintro ⟨-, hx⟩ y
    exact Subtype.ext (hx y y.2)

theorem MinBad.le (hm : MinBad V U B α β) :
    V ≤ U ∧ B ≤ U ∧ α ∈ U ∧ β ∈ U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm.eq_sup]; exact le_sup_left
  · rw [hm.eq_sup]; exact le_sup_right
  · rw [hm.eq_sup]; exact Subgroup.mem_sup_left hm.memα
  · rw [hm.eq_sup]; exact Subgroup.mem_sup_right hm.memβ

theorem mem_omegaSet_self (V : Subgroup G) : V ∈ omegaSet V :=
  Tim79a.mem_omegaOf.mpr ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩

theorem MinBad.alpha_ne_one (hS : Sec6Hyp M V) (hm : MinBad V U B α β) : α ≠ 1 := by
  intro h
  refine hm.bad (Or.inl ?_)
  have hβ2 : β * β = 1 := hS.sec5.toRootHyp.mul_self_of_mem hm.memB hm.memβ
  rw [h, one_mul]
  exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hβ2)

theorem MinBad.beta_ne_one (hS : Sec6Hyp M V) (hm : MinBad V U B α β) : β ≠ 1 := by
  intro h
  refine hm.bad (Or.inl ?_)
  have hα2 : α * α = 1 :=
    hS.sec5.toRootHyp.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  rw [h, mul_one]
  exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hα2)

theorem MinBad.closure_EU (hm : MinBad V U B α β) : Subgroup.closure (EU V U) = U := by
  have hV : V ∈ omegaSet V := mem_omegaSet_self V
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro x ⟨-, A, -, hAU, hxA⟩
    exact hAU hxA
  · rw [hm.eq_sup]
    refine sup_le ?_ ?_
    · intro v hv
      by_cases hv1 : v = 1
      · simpa [hv1] using Subgroup.one_mem (Subgroup.closure (EU V U))
      · exact Subgroup.subset_closure ⟨mem_classD_of_mem hV hv hv1, V, hV, le_sup_left, hv⟩
    · intro b hb
      by_cases hb1 : b = 1
      · simpa [hb1] using Subgroup.one_mem (Subgroup.closure (EU V U))
      · exact Subgroup.subset_closure
          ⟨mem_classD_of_mem hm.memB hb hb1, B, hm.memB, le_sup_right, hb⟩

theorem MinBad.sup_eq (hm : MinBad V U B α β) {A C : Subgroup G} (hA : A ∈ omegaSet V)
    (hC : C ∈ omegaSet V) (hAU : A ≤ U) (hCU : C ≤ U) {a c : G} (ha : a ∈ A) (hc : c ∈ C)
    (hb : BadPair a c) : A ⊔ C = U := by
  have hmem : A ⊔ C ∈ badSet V := ⟨A, hA, C, hC, a, ha, c, hc, hb, rfl⟩
  have hle : A ⊔ C ≤ U := sup_le hAU hCU
  exact Subgroup.eq_of_le_of_card_ge hle (hm.min (A ⊔ C) hmem)

theorem MinBad.pow_mem_ZU (hS : Sec6Hyp M V) (hm : MinBad V U B α β)
    {x y : G} (hx : x ∈ EU V U) (hy : y ∈ EU V U) (hb : BadPair x y) {r : ℕ} (hr : Odd r)
    (ho : orderOf (x * y) = 2 * r) : (x * y) ^ r ∈ ZU U := by
  obtain ⟨hxD, A, hA, hAU, hxA⟩ := hx
  obtain ⟨hyD, C, hC, hCU, hyC⟩ := hy
  have hsup : A ⊔ C = U := hm.sup_eq hA hC hAU hCU hxA hyC hb
  have hroot := hS.sec5.toRootHyp
  have hcommA := hroot.commute_pow_of_orderOf hxD hyD hr ho hA (Or.inl hxA)
  have hcommC := hroot.commute_pow_of_orderOf hxD hyD hr ho hC (Or.inr hyC)
  set t : G := (x * y) ^ r with ht
  have hxy : x * y ∈ A ⊔ C :=
    Subgroup.mul_mem (A ⊔ C) (Subgroup.mem_sup_left hxA) (Subgroup.mem_sup_right hyC)
  have htU : t ∈ U := by
    rw [← hsup]
    exact Subgroup.pow_mem (A ⊔ C) hxy r
  have hAc : A ≤ Subgroup.centralizer ({t} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact (hcommA z hz).eq.symm
  have hCc : C ≤ Subgroup.centralizer ({t} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact (hcommC z hz).eq.symm
  have hUc : U ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [← hsup]
    exact sup_le hAc hCc
  refine ⟨htU, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro z hz
  have h := Subgroup.mem_centralizer_iff.mp (hUc hz) t (Set.mem_singleton t)
  exact h.symm

theorem MinBad.not_mem_classD (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β)
    {x : G} (hx : x ∈ ZU U) : x ∉ Tim78.classD V := by
  intro hxD
  have hroot := hS.sec5.toRootHyp
  have hx1 : x ≠ 1 := classD_ne_one hxD
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hβ1 : β ≠ 1 := hm.beta_ne_one hS
  obtain ⟨A, hA, hxA⟩ := exists_omegaSet_of_mem_classD hxD
  have hxα : Commute x α :=
    (Subgroup.mem_centralizer_iff.mp hx.2 α hm.le.2.2.1).symm
  have hxβ : Commute x β :=
    (Subgroup.mem_centralizer_iff.mp hx.2 β hm.le.2.2.2).symm
  have hAV : ∀ z ∈ A, ∀ y ∈ V, Commute z y :=
    hroot.commute_of_commute_mem hA (mem_omegaSet_self V) hxA hm.memα hx1 hα1 hxα
  have hAB : ∀ z ∈ A, ∀ y ∈ B, Commute z y :=
    hroot.commute_of_commute_mem hA hm.memB hxA hm.memβ hx1 hβ1 hxβ
  exact hS.not_bad_of_common h64 (mem_omegaSet_self V) hm.memB hA hAV hAB hm.memα hm.memβ
    hm.bad

theorem MinBad.inf_ZU (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β) :
    V ⊓ ZU U = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  by_contra hv1
  exact hm.not_mem_classD hS h64 hv.2
    (mem_classD_of_mem (mem_omegaSet_self V) hv.1 hv1)

private theorem MinBad.z0_data (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {r : ℕ} (hr : Odd r) (ho : orderOf (α * β) = 2 * r) :
    ((α * β) ^ r ∈ ZU U) ∧ ((α * β) ^ r * (α * β) ^ r = 1) ∧ (α * β) ^ r ∉ V := by
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hβ1 : β ≠ 1 := hm.beta_ne_one hS
  have hαEU : α ∈ EU V U :=
    ⟨mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1, V, mem_omegaSet_self V,
      hm.le.1, hm.memα⟩
  have hβEU : β ∈ EU V U :=
    ⟨mem_classD_of_mem hm.memB hm.memβ hβ1, B, hm.memB, hm.le.2.1, hm.memβ⟩
  have hzZU : (α * β) ^ r ∈ ZU U := hm.pow_mem_ZU hS hαEU hβEU hm.bad hr ho
  refine ⟨hzZU, ?_, ?_⟩
  · have h2r : (α * β) ^ (2 * r) = 1 := by
      rw [← ho]
      exact pow_orderOf_eq_one (α * β)
    have h : (α * β) ^ (r + r) = 1 := by
      rw [show r + r = 2 * r by omega]
      exact h2r
    simpa only [pow_add] using h
  · intro hzV
    have hz1 : (α * β) ^ r ≠ 1 := by
      intro h
      have hdvd : orderOf (α * β) ∣ r := orderOf_dvd_iff_pow_eq_one.mpr h
      have hle : orderOf (α * β) ≤ r := Nat.le_of_dvd hr.pos hdvd
      rw [ho] at hle
      have hrpos : 0 < r := hr.pos
      omega
    have hmem : (α * β) ^ r ∈ V ⊓ ZU U := ⟨hzV, hzZU⟩
    rw [hm.inf_ZU hS h64] at hmem
    exact hz1 (Subgroup.mem_bot.mp hmem)

private theorem MinBad.twin_point (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) :
    ∃ z₀ u : G, ∃ A' : Subgroup G, z₀ ∈ ZU U ∧ z₀ * z₀ = 1 ∧ z₀ ∉ V ∧ u ∈ U ∧
      A' ∈ omegaSet V ∧ A' ≤ U ∧ α * z₀ ∈ A' ∧ ∀ x ∈ V, ∀ y ∈ A', Commute x y := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hβ1 : β ≠ 1 := hm.beta_ne_one hS
  have hα2 : α * α = 1 := hroot.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  have hβ2 : β * β = 1 := hroot.mul_self_of_mem hm.memB hm.memβ
  have hαD : α ∈ Tim78.classD V := mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1
  have hβD : β ∈ Tim78.classD V := mem_classD_of_mem hm.memB hm.memβ hβ1
  obtain ⟨r, hr, hr3, ho⟩ := hS.exists_odd_of_bad h64 hαD hβD hm.bad
  let z₀ : G := (α * β) ^ r
  have hz := hm.z0_data hS h64 hr ho
  have hzZU : z₀ ∈ ZU U := by simpa only [z₀] using hz.1
  have hz2 : z₀ * z₀ = 1 := by simpa only [z₀] using hz.2.1
  have hzV : z₀ ∉ V := by simpa only [z₀] using hz.2.2
  obtain ⟨j, rfl⟩ := hr
  let u : G := ((α * β) ^ j)⁻¹
  have hαU : α ∈ U := hm.le.2.2.1
  have hβU : β ∈ U := hm.le.2.2.2
  have huU : u ∈ U := by
    simpa [u] using U.inv_mem (Subgroup.pow_mem U (Subgroup.mul_mem U hαU hβU) j)
  let A' : Subgroup G := conjSubgroup u B
  have hA' : A' ∈ omegaSet V := by
    obtain ⟨k, -, hk⟩ := Tim79a.mem_omegaOf.mp hm.memB
    refine Tim79a.mem_omegaOf.mpr ⟨u * k, Subgroup.mem_top _, ?_⟩
    show conjSubgroup u B = conjSubgroup (u * k) V
    rw [hk, ← conjSubgroup_mul]
  have hxA' : u * β * u⁻¹ ∈ A' := by
    change u * β * u⁻¹ ∈ conjSubgroup u B
    refine mem_conjSubgroup.mpr ?_
    simpa only [show u⁻¹ * (u * β * u⁻¹) * u = β by group] using hm.memβ
  have hA1 : α * (u * β * u⁻¹) = z₀ := by
    simpa [u, z₀] using dihedral_mul_conj_inv_pow' hα2 hβ2 j
  have hαz : α * z₀ = u * β * u⁻¹ := by
    calc α * z₀ = α * (α * (u * β * u⁻¹)) := by rw [hA1]
      _ = u * β * u⁻¹ := by rw [← mul_assoc, hα2, one_mul]
  have hxmem : α * z₀ ∈ A' := hαz ▸ hxA'
  have hA'U : A' ≤ U := by
    intro x hx
    have hx' : u⁻¹ * x * u ∈ B := by
      simpa only [A'] using mem_conjSubgroup.mp hx
    rw [show x = u * (u⁻¹ * x * u) * u⁻¹ by group]
    exact U.mul_mem (U.mul_mem huU (hm.le.2.1 hx')) (U.inv_mem huU)
  have hx1 : α * z₀ ≠ 1 := by
    intro h
    apply hzV
    have hz : z₀ = α := by
      calc z₀ = α * (α * z₀) := by rw [← mul_assoc, hα2, one_mul]
        _ = α := by rw [h, mul_one]
    rw [hz]
    exact hm.memα
  have hαz0 : Commute α z₀ :=
    Subgroup.mem_centralizer_iff.mp hzZU.2 α hm.le.2.2.1
  have hcommV : ∀ x ∈ V, ∀ y ∈ A', Commute x y :=
    hroot.commute_of_commute_mem (mem_omegaSet_self V) hA' hm.memα hxmem hα1 hx1
      ((Commute.refl α).mul_right hαz0)
  exact ⟨z₀, u, A', hzZU, hz2, hzV, huU, hA', hA'U, hxmem, hcommV⟩

theorem MinBad.exists_twin (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β) :
    ∃ H h₀ y₀ z₀, Twin M V U α H h₀ y₀ z₀ := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hα2 : α * α = 1 := hroot.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  obtain ⟨z₀, u, A', hzZU, hz2, hzV, -, hA', hA'U, hxmem, hcommV⟩ :=
    hm.twin_point hS h64
  have hA'M : A' ≤ M := by
    have hCen : A' ≤ Subgroup.centralizer (V : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcommV v hv y hy).eq
    exact hCen.trans (by
      rw [← hroot.toHyp.normalizer_eq]
      exact Subgroup.centralizer_le_normalizer (V : Set G))
  have hA'V : A' ≠ V := by
    intro h
    apply hzV
    have hmemV : α * z₀ ∈ V := h ▸ hxmem
    have hV : α * (α * z₀) ∈ V := V.mul_mem hm.memα hmemV
    rwa [show α * (α * z₀) = z₀ by rw [← mul_assoc, hα2, one_mul]] at hV
  have hAsig : A' ∈ sigmaSet M V := by
    rcases h64 A' hA' hA'M with h | h
    · exact absurd h hA'V
    · exact h
  obtain ⟨g', hg'⟩ := hAsig
  have hsig' : conjSubgroup g' V ∈ sigmaSet M V := by
    rw [← hg'.1]
    exact ⟨g', hg'⟩
  have hSH : Sec45Shape M V (hOf M V g') g' := hS.sec5.shape hsig'
  obtain ⟨y, hyH, -, hVy, -⟩ :=
    hroot.exists_mem_conj_eq_of_eq_sup hSH.mem.2.1 hSH.hH
  have hne : conjSubgroup y V ≠ V := by
    intro h
    exact hA'V (hg'.1.trans (hVy.trans h))
  have hle : conjSubgroup y V ≤ U := by
    rw [← hVy, ← hg'.1]
    exact hA'U
  have hsigma : conjSubgroup y V ∈ sigmaSet M V := by
    rw [← hVy]
    exact hsig'
  have hmem : α * z₀ ∈ conjSubgroup y V := by
    rw [← hVy, ← hg'.1]
    exact hxmem
  exact ⟨hOf M V g', g', y, z₀, hzZU, hz2, hzV, hSH, hyH, hne, hle, hsigma, hmem⟩

end CFSG.RankThree.GF2n.Tim81
