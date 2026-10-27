module

public import CFSG.Quasithin.Background.SmithB42Disp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin
open scoped commutatorElement

private lemma m4outgen_commutator_mul_center {X : Type*} [Group X] {k₁ k₂ z₁ z₂ : X}
    (hz₁ : z₁ ∈ Subgroup.center X) (hz₂ : z₂ ∈ Subgroup.center X) :
    ⁅k₁ * z₁, k₂ * z₂⁆ = ⁅k₁, k₂⁆ := by
  have hz₁c : ∀ x, Commute z₁ x := fun x => (Subgroup.mem_center_iff.1 hz₁ x).symm
  have hz₂c : ∀ x, Commute x z₂ := fun x => Subgroup.mem_center_iff.1 hz₂ x
  calc ⁅k₁ * z₁, k₂ * z₂⁆
      = k₁ * ⁅z₁, k₂ * z₂⁆ * k₁⁻¹ * ⁅k₁, k₂ * z₂⁆ :=
        commutatorElement_mul_left_eq_conj_mul k₁ z₁ (k₂ * z₂)
    _ = k₁ * 1 * k₁⁻¹ * ⁅k₁, k₂ * z₂⁆ := by
        rw [(hz₁c (k₂ * z₂)).commutator_eq]
    _ = k₁ * 1 * k₁⁻¹ * (⁅k₁, k₂⁆ * k₂ * ⁅k₁, z₂⁆ * k₂⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj]
    _ = ⁅k₁, k₂⁆ := by
        rw [(hz₂c k₁).commutator_eq]
        group

private lemma m4outgen_eq_top_of_mul_center {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    {K : Subgroup X} (h : ∀ x : X, ∃ k ∈ K, ∃ z ∈ Subgroup.center X, x = k * z) :
    K = ⊤ := by
  rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := h a
  obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := h b
  rw [m4outgen_commutator_mul_center hz₁ hz₂]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)

private lemma m4outgen_exists_lift {Y S : Type*} [Group Y] [Group S] {L : Subgroup Y}
    {F : Y →* S} {P : Subgroup S} (hsurj : ∀ p ∈ P, ∃ l ∈ L, F l = p) :
    ∀ cs : List S, (∀ c ∈ cs, c ∈ P) →
      ∃ gs : List Y, (∀ g ∈ gs, g ∈ L) ∧ gs.map F = cs := by
  intro cs
  induction cs with
  | nil => exact fun _ => ⟨[], by simp, by simp⟩
  | cons c cs ih =>
      intro hcs
      obtain ⟨l, hlL, hFl⟩ := hsurj c (hcs c (by simp))
      obtain ⟨gs, hgsL, hgsF⟩ := ih (fun d hd => hcs d (by simp [hd]))
      refine ⟨l :: gs, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with hgc | hgs
        · rw [hgc]; exact hlL
        · exact hgsL g hgs
      · simp [hFl, hgsF]

private lemma m4outgen_image_gen_set {Y S : Type*} [Group Y] [Group S] (F : Y →* S)
    (t : Y) {gs : List Y} {cs : List S} (hgsF : gs.map F = cs) :
    F '' {v : Y | ∃ g ∈ gs, v = g * t * g⁻¹} =
      {v : S | ∃ c ∈ cs, v = c * F t * c⁻¹} := by
  ext v
  constructor
  · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨F g, by rw [← hgsF]; exact List.mem_map.2 ⟨g, hg, rfl⟩,
      by simp [map_mul, map_inv]⟩
  · rintro ⟨c, hc, rfl⟩
    rw [← hgsF] at hc
    obtain ⟨g, hg, hgc⟩ := List.mem_map.1 hc
    exact ⟨g * t * g⁻¹, ⟨g, hg, rfl⟩, by rw [← hgc]; simp [map_mul, map_inv]⟩

private lemma m4outgen_image_gen_set_aut {Y U : Type*} [Group Y] [CommGroup U]
    (ρ : Y →* MulAut U) (t : Y) (gs : List Y) :
    ρ '' {v : Y | ∃ g ∈ gs, v = g * t * g⁻¹} =
      {v : MulAut U | ∃ h ∈ gs.map ρ, v = h * ρ t * h⁻¹} := by
  ext v
  constructor
  · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨ρ g, List.mem_map.2 ⟨g, hg, rfl⟩, by simp [map_mul, map_inv]⟩
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨g, hg, hgh⟩ := List.mem_map.1 hh
    exact ⟨g * t * g⁻¹, ⟨g, hg, rfl⟩, by rw [← hgh]; simp [map_mul, map_inv]⟩

theorem outer_index_ge_of_generation {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ w : U, w * w = 1) {Y S : Type} [Group Y] [Group S] (L : Subgroup Y)
    (hperf : Group.IsPerfect ↥L) (F : Y →* S) (P : Subgroup S)
    (hFP : ∀ y ∈ L, F y ∈ P) (hsurj : ∀ p ∈ P, ∃ l ∈ L, F l = p)
    (hback : ∀ y : Y, F y ∈ P → y ∈ L)
    (hker : ∀ l : ↥L, F (l : Y) = 1 → l ∈ Subgroup.center ↥L)
    (ρ : Y →* MulAut U) {ζ : ↥L} (hζ : ζ ∈ Subgroup.center ↥L)
    (hfix : ∀ u : U, ρ (ζ : Y) u = u → u = 1) (h54 : 2 ^ 54 ≤ Nat.card U)
    {t : Y} (ht2 : t * t = 1) (cs : List S) (hlen : cs.length = 4) (hcs : ∀ c ∈ cs, c ∈ P)
    (hgen : P ≤ Subgroup.closure {x | ∃ c ∈ cs, x = c * F t * c⁻¹}) :
    2 ^ 4 ≤ (fixV (Subgroup.zpowers (ρ t))).index := by
  obtain ⟨gs, hgsL, hgsF⟩ := m4outgen_exists_lift hsurj cs hcs
  have hgs_len : gs.length = 4 := by
    have h1 : gs.length = cs.length := by simpa using congrArg List.length hgsF
    rw [h1, hlen]
  have hlen4 : (gs.map ρ).length = 4 := by rw [List.length_map, hgs_len]
  let N : Subgroup Y := Subgroup.closure {v : Y | ∃ g ∈ gs, v = g * t * g⁻¹}
  have hNmap : N.map F = Subgroup.closure {v : S | ∃ c ∈ cs, v = c * F t * c⁻¹} := by
    change (Subgroup.closure {v : Y | ∃ g ∈ gs, v = g * t * g⁻¹}).map F
      = Subgroup.closure {v : S | ∃ c ∈ cs, v = c * F t * c⁻¹}
    rw [MonoidHom.map_closure, m4outgen_image_gen_set F t hgsF]
  have hPN : P ≤ N.map F := by rw [hNmap]; exact hgen
  have hLleN : L ≤ N := by
    have htop : N.subgroupOf L = ⊤ := by
      refine m4outgen_eq_top_of_mul_center (X := ↥L) hperf ?_
      intro x
      have hxP : F (x : Y) ∈ P := hFP (x : Y) x.2
      have hxNF : F (x : Y) ∈ N.map F := hPN hxP
      rw [Subgroup.mem_map] at hxNF
      obtain ⟨n, hnN, hnF⟩ := hxNF
      have hnL : n ∈ L := hback n (by rw [hnF]; exact hxP)
      let k : ↥L := ⟨n, hnL⟩
      let z : ↥L := k⁻¹ * x
      have hz : z ∈ Subgroup.center ↥L := by
        refine hker z ?_
        change F (((k : ↥L) : Y)⁻¹ * (x : Y)) = 1
        rw [map_mul, map_inv]
        change (F n)⁻¹ * F (x : Y) = 1
        rw [hnF, inv_mul_cancel]
      refine ⟨k, Subgroup.mem_subgroupOf.mpr hnN, z, hz, ?_⟩
      change x = k * (k⁻¹ * x)
      group
    exact (Subgroup.subgroupOf_eq_top).1 htop
  let Nρ : Subgroup (MulAut U) :=
    Subgroup.closure {v : MulAut U | ∃ h ∈ gs.map ρ, v = h * ρ t * h⁻¹}
  have hNρ : Nρ = N.map ρ := by
    change Subgroup.closure {v : MulAut U | ∃ h ∈ gs.map ρ, v = h * ρ t * h⁻¹}
      = (Subgroup.closure {v : Y | ∃ g ∈ gs, v = g * t * g⁻¹}).map ρ
    rw [MonoidHom.map_closure, m4outgen_image_gen_set_aut ρ t gs]
  have hζN : (ζ : Y) ∈ N := hLleN ζ.2
  have hζNρ : ρ (ζ : Y) ∈ Nρ := by rw [hNρ]; exact ⟨(ζ : Y), hζN, rfl⟩
  have hzpow_le : Subgroup.zpowers (ρ (ζ : Y)) ≤ Nρ := Subgroup.zpowers_le.mpr hζNρ
  have hfixNρ : fixV Nρ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact hfix w (CFSG.Quasithin.mem_fixV_zpowers_iff_apply.1
      (fun x hx => hw x (hzpow_le hx)))
  have hcardle : Nat.card U ≤ (fixV (Subgroup.zpowers (ρ t))).index ^ 4 := by
    have h := CFSG.Quasithin.B42Disp.card_le_index_pow_of_fixV_closure_eq_bot
      (V := U) (ρ t) (gs.map ρ) (by change fixV Nρ = ⊥; exact hfixNρ)
    rwa [hlen4] at h
  by_contra hcon
  have hdlt : (fixV (Subgroup.zpowers (ρ t))).index < 2 ^ 4 := not_le.1 hcon
  have hlt : (fixV (Subgroup.zpowers (ρ t))).index ^ 4 < (2 ^ 4) ^ 4 :=
    Nat.pow_lt_pow_left hdlt (by norm_num)
  have heq : (2 ^ 4) ^ 4 = 2 ^ 16 := by rw [← pow_mul]
  rw [heq] at hlt
  have h16 : 2 ^ 16 < 2 ^ 54 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  exact absurd (hlt.trans h16) (not_lt.2 (h54.trans hcardle))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
