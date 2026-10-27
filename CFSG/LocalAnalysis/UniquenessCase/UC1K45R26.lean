module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private theorem xof_le_pPrimeCore : Xof G ≤ CFSG.pPrimeCore 3 G := by
  have hK : Kof G ≤ CFSG.pPrimeCore 3 G := by
    haveI : (CFSG.pPrimeCore 3 G).Normal := CFSG.pPrimeCore_normal
    exact Subgroup.commutator_le_left (CFSG.pPrimeCore 3 G) ⊤
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact hK y.2

noncomputable def alt5Hom (c : Ctx45 p G D) : G →* alternatingGroup (Fin 5) :=
  (Classical.choice c.alt5).toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 G))

theorem alt5Hom_ker (c : Ctx45 p G D) :
    (alt5Hom c).ker = CFSG.pPrimeCore 3 G := by
  ext x
  simp only [alt5Hom, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem alt5Hom_surjective (c : Ctx45 p G D) : Function.Surjective (alt5Hom c) := by
  intro y
  obtain ⟨q, rfl⟩ := (Classical.choice c.alt5).surjective y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 G) q
  exact ⟨g, rfl⟩

theorem map_alt5Hom_eq_top (c : Ctx45 p G D) {S : Subgroup G}
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤) : S.map (alt5Hom c) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := alt5Hom_surjective c y
  have hg : g ∈ S ⊔ CFSG.pPrimeCore 3 G := by rw [hSup]; trivial
  obtain ⟨s, hs, h, hh, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := S) (t := CFSG.pPrimeCore 3 G)).mp hg
  have hfh : alt5Hom c h = 1 := MonoidHom.mem_ker.mp (by rw [alt5Hom_ker c]; exact hh)
  rw [map_mul, hfh, mul_one]
  exact Subgroup.mem_map_of_mem _ hs

theorem map_commutator_alt5Hom_eq_top (c : Ctx45 p G D) {S : Subgroup G}
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤) : (⁅S, S⁆).map (alt5Hom c) = ⊤ := by
  have hS := map_alt5Hom_eq_top c hSup
  calc (⁅S, S⁆).map (alt5Hom c)
      = ⁅S.map (alt5Hom c), S.map (alt5Hom c)⁆ := Subgroup.map_commutator S S (alt5Hom c)
    _ = commutator (alternatingGroup (Fin 5)) := by rw [hS]; rfl
    _ = ⊤ := commutator_alternatingGroup_eq_top (by simp)

theorem eq_commutator_mul_center (c : Ctx45 p G D) {S : Subgroup G}
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤)
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G) {s : G} (hs : s ∈ S) :
    ∃ a ∈ ⁅S, S⁆, ∃ z ∈ Subgroup.center G, a * z = s := by
  have hfs : alt5Hom c s ∈ (⁅S, S⁆).map (alt5Hom c) := by
    rw [map_commutator_alt5Hom_eq_top c hSup]; trivial
  obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.mp hfs
  refine ⟨a, ha, a⁻¹ * s, ?_, by group⟩
  rw [← hSH]
  refine Subgroup.mem_inf.mpr
    ⟨S.mul_mem (S.inv_mem (Subgroup.commutator_le_self S ha)) hs, ?_⟩
  rw [← alt5Hom_ker c, MonoidHom.mem_ker, map_mul, map_inv, hfa]
  simp

theorem commutator_commutator_eq_self (c : Ctx45 p G D) {S : Subgroup G}
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤)
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G) :
    ⁅⁅S, S⁆, ⁅S, S⁆⁆ = ⁅S, S⁆ := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  refine (Subgroup.commutator_le).mpr ?_
  intro s hs s' hs'
  obtain ⟨a, ha, z, hz, rfl⟩ := eq_commutator_mul_center c hSup hSH hs
  obtain ⟨a', ha', z', hz', rfl⟩ := eq_commutator_mul_center c hSup hSH hs'
  rw [CFSG.ComponentClassification.RankTwoAlt.commutatorElement_mul_central hz hz']
  exact Subgroup.commutator_mem_commutator ha ha'

theorem commutator_subtype_eq_top (c : Ctx45 p G D) {S : Subgroup G}
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤)
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G) :
    commutator ↥(⁅S, S⁆) = ⊤ := by
  have hself := commutator_commutator_eq_self c hSup hSH
  apply Subgroup.map_injective (f := (⁅S, S⁆).subtype) (⁅S, S⁆).subtype_injective
  rw [Subgroup.map_subtype_commutator, hself, Subgroup.map_top, Subgroup.range_subtype]

theorem mul_self_eq_one_of_mem_commutator_inf
    (c : Ctx45 p G D) {S : Subgroup G}
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤)
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G)
    {u : G} (hu : u ∈ ⁅S, S⁆ ⊓ CFSG.pPrimeCore 3 G) : u * u = 1 := by
  obtain ⟨huS, huH⟩ := Subgroup.mem_inf.mp hu
  let S' : Subgroup G := ⁅S, S⁆
  let π : ↥S' →* alternatingGroup (Fin 5) := (alt5Hom c).comp S'.subtype
  have hperf : commutator ↥S' = ⊤ := commutator_subtype_eq_top c hSup hSH
  have hπs : Function.Surjective π := by
    intro y
    have hy : y ∈ S'.map (alt5Hom c) := by
      change y ∈ (⁅S, S⁆).map (alt5Hom c)
      rw [map_commutator_alt5Hom_eq_top c hSup]
      trivial
    obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨a, ha⟩, hfa⟩
  have hπk : π.ker ≤ Subgroup.center ↥S' := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : G) * (x : G) = (x : G) * (y : G)
    have hxH : (x : G) ∈ CFSG.pPrimeCore 3 G := by
      rw [← alt5Hom_ker c, MonoidHom.mem_ker]
      have hx1 : π x = 1 := MonoidHom.mem_ker.mp hx
      simpa [π] using hx1
    have hxZ : (x : G) ∈ Subgroup.center G := by
      rw [← hSH]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.commutator_le_self S x.2, hxH⟩
    exact Subgroup.mem_center_iff.mp hxZ (y : G)
  have hker2 : Nat.card π.ker ∣ 2 :=
    CFSG.ComponentClassification.RankTwoAlt.card_ker_dvd_two_five hperf hπs hπk
  have hu_ker : (⟨u, huS⟩ : ↥S') ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    show alt5Hom c u = 1
    exact MonoidHom.mem_ker.mp (by rw [alt5Hom_ker c]; exact huH)
  have hdvd : orderOf (⟨u, huS⟩ : ↥S') ∣ 2 :=
    (Subgroup.orderOf_dvd_natCard π.ker hu_ker).trans hker2
  have h2 : (⟨u, huS⟩ : ↥S') ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have h2' : u ^ 2 = 1 := by
    have := congrArg Subtype.val h2
    simpa [Subgroup.coe_pow] using this
  simpa [pow_two] using h2'

theorem exists_involution_mem_zxof (c : Ctx45 p G D) :
    ∃ z : G, z ∈ ZXof G ∧ orderOf z = 2 := by
  have hXp : IsPGroup 2 ↥(Xof G) := xof_isPGroup
  have hTle : Tof G D ≤ Xof G := Subgroup.commutator_le_left (Xof G) D
  have hcardT : Nat.card ↥(Tof G D) = 8 := by
    obtain ⟨e⟩ := c.Q8
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hXnt : Nontrivial ↥(Xof G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < 8 := by norm_num
      _ = Nat.card ↥(Tof G D) := hcardT.symm
      _ ≤ Nat.card ↥(Xof G) := Subgroup.card_le_of_le hTle
  haveI : Nontrivial ↥(Xof G) := hXnt
  have hcenter : Nontrivial ↥(Subgroup.center ↥(Xof G)) := hXp.center_nontrivial
  haveI : Nontrivial ↥(Subgroup.center ↥(Xof G)) := hcenter
  have hcenter_p : IsPGroup 2 ↥(Subgroup.center ↥(Xof G)) :=
    hXp.to_subgroup (Subgroup.center ↥(Xof G))
  have h2dvd_center : 2 ∣ Nat.card ↥(Subgroup.center ↥(Xof G)) := by
    rcases hcenter_p.card_eq_or_dvd with h1 | h2
    · exfalso
      have := Finite.one_lt_card (α := ↥(Subgroup.center ↥(Xof G)))
      omega
    · exact h2
  have h2dvd_zx : 2 ∣ Nat.card ↥(ZXof G) := by
    change 2 ∣ Nat.card ↥((Subgroup.center ↥(Xof G)).map (Xof G).subtype)
    rw [Subgroup.card_map_of_injective (Xof G).subtype_injective]
    exact h2dvd_center
  obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ZXof G)) 2 h2dvd_zx
  refine ⟨(z : G), z.2, ?_⟩
  have horder : orderOf ((Subgroup.subtype (ZXof G)) z) = 2 := by
    rw [orderOf_injective _ (ZXof G).subtype_injective z, hz2]
  simpa using horder

theorem eq_one_or_eq_of_sq_eq_one (c : Ctx45 p G D) {z u : G}
    (hz : z ∈ ZXof G) (hz2 : orderOf z = 2)
    (hu : u ∈ Subgroup.center G) (hu2 : u * u = 1) : u = 1 ∨ u = z := by
  classical
  let Z := Subgroup.center G
  haveI : Fintype ↥Z := Fintype.ofFinite ↥Z
  haveI : IsCyclic ↥Z := c.center_cyclic
  have hzu : z ∈ Z := c.ZX_le hz
  have hzsq : (⟨z, hzu⟩ : ↥Z) ^ 2 = 1 := by
    apply Subtype.ext
    show z ^ 2 = 1
    rw [← hz2]
    exact pow_orderOf_eq_one z
  let s : Finset ↥Z := Finset.univ.filter fun a => a ^ 2 = 1
  have hcard : s.card ≤ 2 := by
    have := IsCyclic.card_pow_eq_one_le (α := ↥Z) (n := 2) (by norm_num)
    simpa [s] using this
  have hsub : ({1, ⟨z, hzu⟩} : Finset ↥Z) ⊆ s := by
    intro a ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp
    · exact hzsq
  have hz_ne_one : (⟨z, hzu⟩ : ↥Z) ≠ 1 := by
    intro h
    have hz1 : z = 1 := congrArg Subtype.val h
    rw [hz1] at hz2
    simp at hz2
  have hpair : ({1, ⟨z, hzu⟩} : Finset ↥Z).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]
    exact hz_ne_one.symm
  have hs_eq : ({1, ⟨z, hzu⟩} : Finset ↥Z) = s :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hpair]; exact hcard)
  have hu_mem : (⟨u, hu⟩ : ↥Z) ∈ s := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    show u ^ 2 = 1
    rw [pow_two]
    exact hu2
  rw [← hs_eq] at hu_mem
  rw [Finset.mem_insert, Finset.mem_singleton] at hu_mem
  rcases hu_mem with h | h
  · left; exact congrArg Subtype.val h
  · right; exact congrArg Subtype.val h

theorem commutator_sup_center_eq_self (c : Ctx45 p G D) {S : Subgroup G}
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G)
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤) :
    ⁅S, S⁆ ⊔ Subgroup.center G = S := by
  apply le_antisymm
  · exact sup_le (Subgroup.commutator_le_self S) (by rw [← hSH]; exact inf_le_left)
  · intro s hs
    obtain ⟨a, ha, z, hz, hza⟩ := eq_commutator_mul_center c hSup hSH hs
    rw [← hza]
    exact Subgroup.mul_mem_sup ha hz

theorem commutator_inf_le_xof (c : Ctx45 p G D) {S : Subgroup G}
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G)
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤) :
    ⁅S, S⁆ ⊓ CFSG.pPrimeCore 3 G ≤ Xof G := by
  intro u hu
  obtain ⟨huS, huH⟩ := Subgroup.mem_inf.mp hu
  by_cases hu1 : u = 1
  · rw [hu1]; exact (Xof G).one_mem
  · have huZ : u ∈ Subgroup.center G := by
      rw [← hSH]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.commutator_le_self S huS, huH⟩
    have hu2 : u * u = 1 :=
      mul_self_eq_one_of_mem_commutator_inf c hSup hSH (Subgroup.mem_inf.mpr ⟨huS, huH⟩)
    obtain ⟨z, hzX, hz2⟩ := exists_involution_mem_zxof c
    rcases eq_one_or_eq_of_sq_eq_one c hzX hz2 huZ hu2 with h | h
    · exact absurd h hu1
    · rw [h]
      exact Subgroup.map_subtype_le (Subgroup.center ↥(Xof G)) hzX

theorem exists_sup_commutator_xof_mul_center (c : Ctx45 p G D) {S : Subgroup G}
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G)
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G)
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤) (g : G) :
    ∃ m ∈ ⁅S, S⁆ ⊔ Xof G, ∃ z ∈ Subgroup.center G, m * z = g := by
  have hg : g ∈ S ⊔ CFSG.pPrimeCore 3 G := by rw [hSup]; trivial
  obtain ⟨s, hs, h, hh, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := S) (t := CFSG.pPrimeCore 3 G)).mp hg
  have hs' : s ∈ ⁅S, S⁆ ⊔ Subgroup.center G := by
    rw [commutator_sup_center_eq_self c hSH hSup]
    exact hs
  obtain ⟨a, ha, z, hz, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := ⁅S, S⁆) (t := Subgroup.center G)).mp hs'
  have hh' : h ∈ Xof G ⊔ Subgroup.center G := by rw [← hH]; exact hh
  obtain ⟨x, hx, z', hz', rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := Xof G) (t := Subgroup.center G)).mp hh'
  refine ⟨a * x, Subgroup.mul_mem_sup ha hx, z * z', (Subgroup.center G).mul_mem hz hz', ?_⟩
  calc (a * x) * (z * z') = a * (x * z) * z' := by group
    _ = a * (z * x) * z' := by rw [Subgroup.mem_center_iff.mp hz x]
    _ = (a * z) * (x * z') := by group

theorem sup_commutator_xof_eq_top (c : Ctx45 p G D) {S : Subgroup G}
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G)
    (hSH : S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G)
    (hSup : S ⊔ CFSG.pPrimeCore 3 G = ⊤) :
    ⁅S, S⁆ ⊔ Xof G = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← c.perfect]
  change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ ⁅S, S⁆ ⊔ Xof G
  rw [Subgroup.commutator_le]
  intro g _ g' _
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_sup_commutator_xof_mul_center c hH hSH hSup g
  obtain ⟨m', hm', z', hz', rfl⟩ := exists_sup_commutator_xof_mul_center c hH hSH hSup g'
  rw [CFSG.ComponentClassification.RankTwoAlt.commutatorElement_mul_central hz hz']
  exact Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator hm hm')

theorem r2_H_eq_X (c : Ctx45 p G D)
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G)
    (hS : ∃ S : Subgroup G, Subgroup.center G ≤ S ∧ S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G ∧
      S ⊔ CFSG.pPrimeCore 3 G = ⊤) : CFSG.pPrimeCore 3 G = Xof G := by
  obtain ⟨S, _hZS, hSH, hSup⟩ := hS
  refine le_antisymm ?_ xof_le_pPrimeCore
  intro h hh
  have htop : ⁅S, S⁆ ⊔ Xof G = ⊤ := sup_commutator_xof_eq_top c hH hSH hSup
  have hm : h ∈ ⁅S, S⁆ ⊔ Xof G := by rw [htop]; trivial
  obtain ⟨a, ha, x, hx, hax⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := ⁅S, S⁆) (t := Xof G)).mp hm
  have haH : a ∈ CFSG.pPrimeCore 3 G := by
    have ha_eq : a = h * x⁻¹ := by rw [← hax]; group
    rw [ha_eq]
    exact (CFSG.pPrimeCore 3 G).mul_mem hh
      ((CFSG.pPrimeCore 3 G).inv_mem (xof_le_pPrimeCore hx))
  have haX : a ∈ Xof G := commutator_inf_le_xof c hSH hSup ⟨ha, haH⟩
  rw [← hax]
  exact (Xof G).mul_mem haX hx

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
