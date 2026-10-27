module

public import CFSG.RankThree.PartOne.S12.Sec1322Reflect
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartOne.S12.Sec1322Fin

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

namespace Sec1322

open Sec1322Fin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d8_noncomm_order :
    ∀ a b : DihedralGroup 4, a * a = 1 → b * b = 1 → a * b ≠ b * a → orderOf (a * b) = 4 := by
  have key : ∀ a b : DihedralGroup 4, a * a = 1 → b * b = 1 → a * b ≠ b * a →
      (a * b) ^ 4 = 1 ∧ (a * b) ^ 1 ≠ 1 ∧ (a * b) ^ 2 ≠ 1 ∧ (a * b) ^ 3 ≠ 1 := by decide
  intro a b ha hb hab
  obtain ⟨h4, h1, h2, h3⟩ := key a b ha hb hab
  refine (orderOf_eq_iff (by norm_num)).2 ⟨h4, fun m hm hm0 => ?_⟩
  interval_cases m <;> assumption

theorem d8_not_comm : ∃ a b : DihedralGroup 4, a * b ≠ b * a := by decide

theorem z0_props : z0 * z0 = 1 ∧ z0 ≠ 1 ∧ ∀ γ : Gp, γ * z0 = z0 * γ := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem central_unique : ∀ g : Gp, g * g = 1 → g ≠ 1 → (∀ γ : Gp, γ * g = g * γ) → g = z0 := by
  decide

theorem exists_chain_of_iso {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hL : torusImage E L =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))))
    (eL : torusImage E L ≃* DihedralGroup 4) (eX : reflectionGroup p E ≃* Gp) :
    ∃ t₁ t₂ t₃ : MulAut E, Chain3 p E L t₁ t₂ t₃ := by
  classical
  have hp := h.prime
  have hcardE : Nat.card E = p ^ 3 := by
    rw [hEA]
    exact h.A_card
  let φ : Gp →* MulAut E := (reflectionGroup p E).subtype.comp eX.symm.toMonoidHom
  have hφ : ∀ g, φ g = ((eX.symm g : ↥(reflectionGroup p E)) : MulAut E) := fun _ => rfl
  have hφinj : Function.Injective φ := Subtype.val_injective.comp eX.symm.injective
  have hφX : ∀ g, φ g ∈ reflectionGroup p E := fun g => (eX.symm g).2
  have hφsurj : ∀ y ∈ reflectionGroup p E, ∃ g, φ g = y := fun y hy =>
    ⟨eX ⟨y, hy⟩, by simp [hφ]⟩
  set zM : MulAut E := φ z0 with hzM
  have hzX : zM ∈ reflectionGroup p E := hφX z0
  have hz2 : zM * zM = 1 := by rw [hzM, ← map_mul, (z0_props).1, map_one]
  have hz1 : zM ≠ 1 := fun h1 => (z0_props).2.1 (hφinj (h1.trans (map_one φ).symm))
  have hcen : ∀ y ∈ reflectionGroup p E, y * zM = zM * y := by
    intro y hy
    obtain ⟨g, rfl⟩ := hφsurj y hy
    rw [hzM, ← map_mul, ← map_mul, (z0_props).2.2 g]
  have huniq : ∀ y ∈ reflectionGroup p E, y * y = 1 → y ≠ 1 →
      (∀ x ∈ reflectionGroup p E, x * y = y * x) → y = zM := by
    intro y hy hy2 hy1 hyc
    obtain ⟨g, rfl⟩ := hφsurj y hy
    have hg : g = z0 :=
      central_unique g (hφinj (by rw [map_mul, hy2, map_one]))
        (fun hg => hy1 (by rw [hg, map_one]))
        (fun γ => hφinj (by rw [map_mul, map_mul]; exact hyc (φ γ) (hφX γ)))
    rw [hg]
  have hzinv : ∀ e : E, zM e = e⁻¹ := inverts_of_central h hF13 hzX hz2 hz1 hcen huniq
  let Rset : Set Gp := {g | IsAutReflection p E (φ g)}
  let Dset : Set Gp := {g | φ g ∈ reflectionSet p E}
  have hinvφ : ∀ g : Gp, φ g⁻¹ = (φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have hconj : ∀ g x : Gp, φ (g * x * g⁻¹) = φ g * φ x * (φ g)⁻¹ := fun g x => by
    rw [map_mul, map_mul, hinvφ g]
  have hRc : ∀ g x, x ∈ Rset → g * x * g⁻¹ ∈ Rset := by
    intro g x hx
    show IsAutReflection p E (φ (g * x * g⁻¹))
    rw [hconj]
    exact isAutReflection_conj (φ g) (φ x) hx
  have hDc : ∀ g x, x ∈ Dset → g * x * g⁻¹ ∈ Dset := by
    intro g x hx
    show φ (g * x * g⁻¹) ∈ reflectionSet p E
    rw [hconj]
    obtain ⟨w, hw, hlift⟩ := exists_lift (reflectionGroup_le E (hφX g))
    rw [← hlift]
    exact conj_mem_reflectionSet hp hx hw
  have hDR : Dset ⊆ Rset := fun x hx => hx.1
  have hRi : ∀ x ∈ Rset, x * x = 1 ∧ x ≠ 1 ∧ x ≠ z0 := by
    intro x hx
    have hord : orderOf (φ x) = 2 := hx.1
    have hsq : φ x * φ x = 1 := by
      have h5 := pow_orderOf_eq_one (φ x)
      rw [hord, pow_two] at h5
      exact h5
    refine ⟨hφinj (by rw [map_mul, hsq, map_one]), ?_, ?_⟩
    · rintro rfl
      rw [map_one, orderOf_one] at hord
      omega
    · rintro rfl
      exact not_isAutReflection_of_inverts h hcardE hzinv hx
  have hdich : ∀ x : Gp, x * x = 1 → x ≠ 1 → x ≠ z0 → (x ∈ Rset ↔ z0 * x ∉ Rset) := by
    intro x hx2 hx1 hxz
    have := reflection_dichotomy h hcardE hzinv (x := φ x)
      (by rw [← map_mul, hx2, map_one]) (fun h1 => hx1 (hφinj (h1.trans (map_one φ).symm)))
      (fun h1 => hxz (hφinj h1))
    show IsAutReflection p E (φ x) ↔ ¬ IsAutReflection p E (φ (z0 * x))
    rw [map_mul]
    exact this
  have hgen : Subgroup.closure Dset = ⊤ := by
    have h1 : Subgroup.closure (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹'
        reflectionSet p E) = ⊤ := Subgroup.closure_closure_coe_preimage
    have h2 : Dset = eX '' (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹' reflectionSet p E) := by
      ext g
      constructor
      · intro hg
        exact ⟨eX.symm g, hg, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        show φ (eX x) ∈ reflectionSet p E
        simpa [hφ] using hx
    have h3 := MonoidHom.map_closure eX.toMonoidHom
      (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹' reflectionSet p E)
    rw [h1, Subgroup.map_top_of_surjective _ eX.surjective] at h3
    rw [h2]
    exact h3.symm
  obtain ⟨hDeq, -, t1, ht1, t2, ht2, t3, ht3, hc13, ho12, ho23, hcl, hcls, hpairs⟩ :=
    chain_of_reflection_set hRc hDc hDR hRi hdich hgen
  set S : Set (MulAut E) := reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) with hS
  obtain ⟨s, hs, t, ht, hst⟩ : ∃ s ∈ S, ∃ t ∈ S, s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := d8_not_comm
    have hcomm : ∀ x ∈ torusImage E L, ∀ y ∈ torusImage E L, x * y = y * x := by
      intro x hx y hy
      rw [hL] at hx hy
      have hcomm' := Subgroup.isMulCommutative_closure (k := S) (fun a ha b hb _ => hcon a ha b hb)
      have := hcomm'.is_comm.comm (⟨x, hx⟩ : ↥(Subgroup.closure S)) ⟨y, hy⟩
      exact congrArg Subtype.val this
    apply hab
    have hu : eL.symm a * eL.symm b = eL.symm b * eL.symm a :=
      Subtype.ext (hcomm _ (eL.symm a).2 _ (eL.symm b).2)
    have := congrArg eL hu
    simpa using this
  have hsL : s ∈ torusImage E L := hs.2
  have htL : t ∈ torusImage E L := ht.2
  have hsX : s ∈ reflectionGroup p E := Subgroup.subset_closure hs.1
  have htX : t ∈ reflectionGroup p E := Subgroup.subset_closure ht.1
  have hs2 : s * s = 1 := by
    have h5 := pow_orderOf_eq_one s
    rw [hs.1.1.1, pow_two] at h5
    exact h5
  have ht2' : t * t = 1 := by
    have h5 := pow_orderOf_eq_one t
    rw [ht.1.1.1, pow_two] at h5
    exact h5
  have hord4 : orderOf (s * t) = 4 := by
    set u : ↥(torusImage E L) := ⟨s, hsL⟩
    set v : ↥(torusImage E L) := ⟨t, htL⟩
    have hu1 : u * u = 1 := Subtype.ext hs2
    have hv1 : v * v = 1 := Subtype.ext ht2'
    have hu2 : eL u * eL u = 1 := by rw [← map_mul, hu1, map_one]
    have hv2 : eL v * eL v = 1 := by rw [← map_mul, hv1, map_one]
    have hne : eL u * eL v ≠ eL v * eL u := by
      intro h1
      apply hst
      have h2 : u * v = v * u := eL.injective (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    have h4 := d8_noncomm_order _ _ hu2 hv2 hne
    rw [← map_mul, MulEquiv.orderOf_eq] at h4
    rw [← Subgroup.orderOf_coe] at h4
    exact h4
  set sG : Gp := eX ⟨s, hsX⟩ with hsG
  set tG : Gp := eX ⟨t, htX⟩ with htG
  have hφs : φ sG = s := by simp [hφ, hsG]
  have hφt : φ tG = t := by simp [hφ, htG]
  have hsD : sG ∈ Dset := by
    show φ sG ∈ reflectionSet p E
    rw [hφs]
    exact hs.1
  have htD : tG ∈ Dset := by
    show φ tG ∈ reflectionSet p E
    rw [hφt]
    exact ht.1
  have hord : orderOf (sG * tG) = 4 := by
    rw [← orderOf_injective φ hφinj, map_mul, hφs, hφt]
    exact hord4
  obtain ⟨x, hx⟩ := hpairs sG hsD tG htD hord
  refine ⟨φ t1, φ t2, φ t3, ?_⟩
  have hφD : ∀ g ∈ Dset, φ g ∈ reflectionSet p E := fun g hg => hg
  refine ⟨hφD _ ht1, hφD _ ht2, hφD _ ht3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hc13]
  · rw [← map_mul, orderOf_injective φ hφinj]
    exact ho12
  · rw [← map_mul, orderOf_injective φ hφinj]
    exact ho23
  · have hmap : Subgroup.closure ({φ t1, φ t2, φ t3} : Set (MulAut E)) =
        (Subgroup.closure ({t1, t2, t3} : Set Gp)).map φ := by
      rw [MonoidHom.map_closure]
      simp [Set.image_insert_eq]
    rw [hmap, hcl, ← MonoidHom.range_eq_map]
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact hφX g
    · intro hy
      exact hφsurj y hy
  · intro d hd
    have hdX : d ∈ reflectionGroup p E := Subgroup.subset_closure hd
    have hgD : eX ⟨d, hdX⟩ ∈ Dset := by
      show φ (eX ⟨d, hdX⟩) ∈ reflectionSet p E
      simpa [hφ] using hd
    have hφd : φ (eX ⟨d, hdX⟩) = d := by simp [hφ]
    rcases hcls _ hgD with ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      refine ⟨φ y, hφX y, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, hy, hφd]
    · right
      refine ⟨φ y, hφX y, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, hy, hφd]
  · obtain ⟨w, hw, hlift⟩ := exists_lift (reflectionGroup_le E (hφX x))
    refine ⟨w, hw, ?_⟩
    rw [hlift]
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · refine ⟨?_, ?_⟩
      · rw [← map_inv, ← map_mul, ← map_mul, hx1, hφs]
        exact hsL
      · rw [← map_inv, ← map_mul, ← map_mul, hx2, hφt]
        exact htL
    · refine ⟨?_, ?_⟩
      · rw [← map_inv, ← map_mul, ← map_mul, hx1, hφt]
        exact htL
      · rw [← map_inv, ← map_mul, ← map_mul, hx2, hφs]
        exact hsL

end Sec1322

theorem node1320Struct_of_node1322 (h123 : Node123) (h1322 : Node1322) (hU5 : KF1320U5) :
    Node1320Struct := by
  intro G _ _ p A c L E h hF hF13 hT hEA hnL3
  obtain ⟨⟨eX⟩, ⟨eL⟩⟩ := h1322 G p A c L E h hF hF13 hT hEA hnL3
  obtain ⟨hgenL, r, hr1, hr12, hmodel, hweyl, -, h9⟩ := h123 G p A c L E h
  have hchain := Sec1322.exists_chain_of_iso h hF13 hEA hgenL eL eX
  have hcardE : Nat.card E = p ^ 3 := by
    rw [hEA]
    exact h.A_card
  have hr8 : r ≤ 8 := by
    by_contra hlt
    have h4 := h9 (by omega)
    rw [hcardE] at h4
    have hp := h.prime
    have h5 := Nat.pow_right_injective hp.two_le h4
    omega
  have hcardL : Nat.card (torusImage E L) = 8 := by
    rw [Nat.card_congr eL.toEquiv, DihedralGroup.nat_card]
  refine ⟨?_, ⟨eX⟩, hchain⟩
  interval_cases r
  · exact absurd hmodel hnL3
  · obtain ⟨e⟩ := hweyl
    have h5 := Nat.card_congr e.toEquiv
    rw [hcardL, DihedralGroup.nat_card] at h5
    omega
  · obtain ⟨e⟩ := hweyl
    have h5 := Nat.card_congr e.toEquiv
    rw [hcardL, DihedralGroup.nat_card] at h5
    omega
  · obtain ⟨e⟩ := hweyl
    have h5 := Nat.card_congr e.toEquiv
    rw [hcardL, DihedralGroup.nat_card] at h5
    omega
  · exact Or.inl hmodel
  · exfalso
    obtain ⟨t₁, t₂, t₃, hc⟩ := hchain
    exact hU5 G p A c L E h hF hF13 hT hEA hmodel hnL3 ⟨eX⟩ t₁ t₂ t₃ hc
  · exact Or.inr (Or.inl hmodel)
  · exact Or.inr (Or.inr hmodel)

end CFSG.RankThree.PartOne
