module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_pair_eq_of_ncard_eq_two {α : Type*} {S : Set α} (hS : S.ncard = 2)
    {A B : α} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) : S = {A, B} := by
  obtain ⟨a, b, hab, hSab⟩ := Set.ncard_eq_two.mp hS
  have hAa : A = a ∨ A = b := by
    have h : A ∈ ({a, b} : Set α) := hSab ▸ hA
    simpa using h
  have hBa : B = a ∨ B = b := by
    have h : B ∈ ({a, b} : Set α) := hSab ▸ hB
    simpa using h
  rw [hSab]
  rcases hAa with hAa | hAb
  · have hBb : B = b := by
      rcases hBa with hBa | hBb
      · exact absurd (hAa.trans hBa.symm) hAB
      · exact hBb
    rw [hAa, hBb]
  · have hBa' : B = a := by
      rcases hBa with hBa | hBb
      · exact hBa
      · exact absurd (hAb.trans hBb.symm) hAB
    rw [hAb, hBa']
    exact Set.pair_comm a b

theorem c23_map_conj_eq_of_odd_order {H : Type*} [Group H] {S : Set (Subgroup H)}
    (hS : S.ncard = 2) {φ : H} {n : ℕ} (hn : Odd n) (hφ : φ ^ n = 1)
    (hSφ : ∀ X ∈ S, X.map (MulAut.conj φ).toMonoidHom ∈ S) {X : Subgroup H} (hX : X ∈ S) :
    X.map (MulAut.conj φ).toMonoidHom = X := by
  by_contra hne
  set Y : Subgroup H := X.map (MulAut.conj φ).toMonoidHom with hY
  have hYS : Y ∈ S := hSφ X hX
  have hXY : X ≠ Y := fun h => hne h.symm
  have hSeq : S = {X, Y} := c23_pair_eq_of_ncard_eq_two hS hX hYS hXY
  have hcomp : (MulAut.conj φ).toMonoidHom.comp (MulAut.conj φ).toMonoidHom =
      (MulAut.conj (φ * φ)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hYφS : Y.map (MulAut.conj φ).toMonoidHom ∈ S := hSφ Y hYS
  rw [hSeq, Set.mem_insert_iff, Set.mem_singleton_iff] at hYφS
  obtain ⟨k, hk⟩ := hn
  have hsq : (φ * φ) ^ (k + 1) = φ := by
    have h1 : (φ * φ) ^ (k + 1) = φ ^ (2 * (k + 1)) := by
      rw [← pow_two, ← pow_mul]
    rw [h1, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ,
      show φ ^ (2 * k + 1) = 1 by rw [← hk]; exact hφ, one_mul]
  rcases hYφS with hYX | hYY
  · have hmap : X.map (MulAut.conj (φ * φ)).toMonoidHom = X := by
      have h2 : Y.map (MulAut.conj φ).toMonoidHom =
          X.map ((MulAut.conj φ).toMonoidHom.comp (MulAut.conj φ).toMonoidHom) := by
        rw [hY, Subgroup.map_map]
      rw [hYX, hcomp] at h2
      exact h2.symm
    have hmem : φ * φ ∈ normalizer X :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap
    have hmemφ : φ ∈ normalizer X := by
      have hpow : (φ * φ) ^ (k + 1) ∈ normalizer X :=
        Subgroup.pow_mem (normalizer X) (x := φ * φ) hmem (k + 1)
      rwa [hsq] at hpow
    exact hne ((Subgroup.mem_normalizer_iff_map_conj_eq).1 hmemφ)
  · have hYXeq : Y = X := Subgroup.map_injective (MulEquiv.injective (MulAut.conj φ)) (by
        rw [hYY, hY])
    exact hXY hYXeq.symm

theorem c23_ncard_range_conjSubgroup_eq_two (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2) :
    (Set.range fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))).ncard = 2 := by
  rw [← s15_Core_s15_eq_ncard_range h]
  exact hs

theorem c23_exists_mem_not_nBar (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2) :
    ∃ x ∈ D.M, x ∉ nBar D.M V₀ V hV L := by
  by_contra hcon
  have hSsub : (Set.range fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))) ⊆
      {barSub V₀ V hV L} := by
    rintro X ⟨m, rfl⟩
    have hm : (m : G) ∈ nBar D.M V₀ V hV L := by
      by_contra hc
      exact hcon ⟨(m : G), m.2, hc⟩
    exact Set.mem_singleton_iff.mpr ((s15_Infra_mem_nBar_iff h.hyp125 hV m.2).1 hm)
  have hle : (Set.range fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))).ncard ≤ 1 := by
    have := Set.ncard_le_ncard hSsub (Set.finite_singleton (barSub V₀ V hV L))
    simpa using this
  have hs2 := c23_ncard_range_conjSubgroup_eq_two D h hV hs
  omega

theorem c23_barSub_conj_cases (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) {m : G} (hm : m ∈ D.M) :
    barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L ∨
      barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV (conjSubgroup L x) := by
  have hA : barSub V₀ V hV L ∈ Set.range (fun m : D.M =>
      barSub V₀ V hV (conjSubgroup L (m : G))) := ⟨1, by simp [conjSubgroup_one]⟩
  have hK : barSub V₀ V hV (conjSubgroup L x) ∈ Set.range (fun m : D.M =>
      barSub V₀ V hV (conjSubgroup L (m : G))) := ⟨⟨x, hx⟩, rfl⟩
  have hAK : barSub V₀ V hV L ≠ barSub V₀ V hV (conjSubgroup L x) := by
    intro hc
    exact hxn ((s15_Infra_mem_nBar_iff h.hyp125 hV hx).2 hc.symm)
  have hSeq := c23_pair_eq_of_ncard_eq_two (c23_ncard_range_conjSubgroup_eq_two D h hV hs)
    hA hK hAK
  have hmS : barSub V₀ V hV (conjSubgroup L m) ∈ Set.range (fun m : D.M =>
      barSub V₀ V hV (conjSubgroup L (m : G))) := ⟨⟨m, hm⟩, rfl⟩
  have := hSeq ▸ hmS
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this

theorem c23_barSub_le_normalizer_conjSubgroup (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2) {x : G}
    (hx : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsPGroup p E) :
    barSub V₀ V hV E ≤
      normalizer (barSub V₀ V hV (conjSubgroup L x) : Set (MulAut (Vtil V₀ V hV))) := by
  have hs2 := c23_ncard_range_conjSubgroup_eq_two D h hV hs
  intro φ hφE
  obtain ⟨g, hge, hgφ⟩ := (mem_barSub V₀ V hV E φ).1 hφE
  have hEMe : (g : G) ∈ D.M := hEM hge
  obtain ⟨k, hk⟩ := hE ⟨(g : G), hge⟩
  have hek : (g : G) ^ p ^ k = 1 := by
    have := congrArg (fun y : E => (y : G)) hk
    simpa using this
  have hgk : g ^ p ^ k = 1 := by
    ext
    simpa [Subgroup.coe_pow, hek]
  have hφk : φ ^ p ^ k = 1 := by
    rw [← hgφ, ← map_pow, hgk, map_one]
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hSφ : ∀ X ∈ Set.range (fun m : D.M =>
        barSub V₀ V hV (conjSubgroup L (m : G))),
      X.map (MulAut.conj φ).toMonoidHom ∈ Set.range (fun m : D.M =>
        barSub V₀ V hV (conjSubgroup L (m : G))) := by
    rintro X ⟨m, rfl⟩
    have hmm : (m : G) * (g : G)⁻¹ ∈ D.M := D.M.mul_mem m.2 (D.M.inv_mem hEMe)
    have hm' : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem g.2
    have hkey := s15_Infra_barSub_conjSubgroup V₀ V hV hm' (conjSubgroup L (m : G))
    rw [conjSubgroup_conjSubgroup] at hkey
    have hgt : actTil V₀ V hV ⟨(g : G)⁻¹, hm'⟩ = (actTil V₀ V hV g)⁻¹ := by
      rw [show (⟨(g : G)⁻¹, hm'⟩ : stabTil V₀ V) = g⁻¹ from Subtype.ext rfl, map_inv]
    have hφinv : (actTil V₀ V hV ⟨(g : G)⁻¹, hm'⟩)⁻¹ = φ := by
      rw [hgt, inv_inv, hgφ]
    rw [hφinv] at hkey
    exact ⟨⟨(m : G) * (g : G)⁻¹, hmm⟩, hkey⟩
  have hKS : barSub V₀ V hV (conjSubgroup L x) ∈ Set.range (fun m : D.M =>
      barSub V₀ V hV (conjSubgroup L (m : G))) := ⟨⟨x, hx⟩, rfl⟩
  have hKmap := c23_map_conj_eq_of_odd_order hs2 hodd hφk hSφ hKS
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 hKmap

theorem c23_card_barSub_conjSubgroup {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hx : x ∈ stabTil V₀ V) (L : Subgroup G) :
    Nat.card (barSub V₀ V hV (conjSubgroup L x)) = Nat.card (barSub V₀ V hV L) := by
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV hx L]
  exact Subgroup.card_map_of_injective
    (MulEquiv.injective (MulAut.conj (actTil V₀ V hV ⟨x, hx⟩)⁻¹))

theorem c23_barSub_conjSubgroup_le_Mbar (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {x : G} (hx : x ∈ D.M) :
    barSub V₀ V hV (conjSubgroup L x) ≤ Mbar D.M V₀ V hV := by
  apply barSub_mono
  intro g hg
  rw [mem_conjSubgroup_iff] at hg
  have hgM : x * g * x⁻¹ ∈ D.M := h.le hg
  have hgg : g = x⁻¹ * (x * g * x⁻¹) * x := by group
  rw [hgg]
  exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hx) hgM) hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
