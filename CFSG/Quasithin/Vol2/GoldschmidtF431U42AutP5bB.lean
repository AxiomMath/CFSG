module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bA
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bE16G

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem Vg_isConj
    (c : AutCtx G M₁ M₂ z) (hconj0 : IsConj (c.iso.toG t0B) z) {u : Bh} (hu : (u : Ah) ∈ VA)
    (hu1 : u ≠ 1) : IsConj (c.iso.toG u) z := by
  have hu2 : (u : Ah) * (u : Ah) = 1 := VA_sq hu
  have hu1' : (u : Ah) ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨j, hj, g, hg, hgeq⟩ := inner_inv_type (VA_le_TAh hu) hu2 hu1'
  rcases hj with rfl | rfl
  · have e : repA 0 = xA := by simp [repA]
    rw [e] at hgeq
    have := c.iso.isConj_toG hg (v := xB) hgeq
    rwa [c.iso.toG_xB c.z2 c.z1 c.zc] at this
  · have e : repA 1 = t0A := by simp [repA]
    rw [e] at hgeq
    exact (c.iso.isConj_toG hg (v := t0B) hgeq).trans hconj0

theorem caseB
    (c : AutCtx G M₁ M₂ z) (h5 : U42AutFusionZ) (hconj0 : IsConj (c.iso.toG t0B) z) {y : G}
    (hy : ∀ a ∈ c.iso.imgG VA, y * a * y⁻¹ ∈ c.iso.imgG That) {a₀ : G}
    (ha₀ : a₀ ∈ c.iso.imgG VA) (hna : y * a₀ * y⁻¹ ∉ c.iso.imgG VA) : False := by
  set Vy : Subgroup G := (c.iso.imgG VA).map (MulAut.conj y).toMonoidHom with hVy
  have hVy_mem : ∀ g, g ∈ Vy ↔ ∃ u ∈ c.iso.imgG VA, y * u * y⁻¹ = g := by
    intro g
    rw [hVy, Subgroup.mem_map]
    rfl
  have hVyT : Vy ≤ c.iso.imgG That := by
    intro g hg
    obtain ⟨u, hu, rfl⟩ := (hVy_mem g).1 hg
    exact hy u hu
  set K : Subgroup Ah := (Vy.comap c.iso.toGHom).map Bh.subtype with hK
  have hK_mem : ∀ k : Ah, k ∈ K ↔ ∃ b : Bh, (b : Ah) = k ∧ c.iso.toG b ∈ Vy := by
    intro k
    rw [hK, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, rfl, hb⟩
    · rintro ⟨b, rfl, hb⟩
      exact ⟨b, hb, rfl⟩
  have hKB : K ≤ Bh := by
    intro k hk
    obtain ⟨b, rfl, -⟩ := (hK_mem k).1 hk
    exact b.2
  have hKT : K ≤ That := by
    intro k hk
    obtain ⟨b, rfl, hb⟩ := (hK_mem k).1 hk
    obtain ⟨b', hb', hbb⟩ := c.iso.mem_imgG.1 (hVyT hb)
    have : b' = b := c.iso.toG_injective hbb
    rwa [this] at hb'
  have himg : c.iso.imgG K = Vy := by
    ext g
    constructor
    · intro hg
      obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hg
      obtain ⟨b', hb', hbb⟩ := (hK_mem _).1 hb
      have : b' = b := Subtype.ext hb'
      rw [this] at hbb
      exact hbb
    · intro hg
      obtain ⟨b, -, rfl⟩ := c.iso.mem_imgG.1 (hVyT hg)
      exact c.iso.mem_imgG.2 ⟨b, (hK_mem _).2 ⟨b, rfl, hg⟩, rfl⟩
  have hcard : 16 ≤ Nat.card K := by
    have h1 := c.iso.card_imgG hKB
    have h2 : Nat.card Vy = Nat.card (c.iso.imgG VA) :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    have h3 := c.iso.card_imgG VA_le_Bh
    rw [himg, h2, h3] at h1
    rw [← h1]
    exact card_VA_ge
  have hbasic : ∀ b : Bh, c.iso.toG b ∈ Vy → ∃ u ∈ c.iso.imgG VA, y * u * y⁻¹ = c.iso.toG b :=
    fun b hb => (hVy_mem _).1 hb
  have hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', rfl, ha'⟩ := (hK_mem a).1 ha
    obtain ⟨b', rfl, hb'⟩ := (hK_mem b).1 hb
    obtain ⟨u, hu, hua⟩ := hbasic a' ha'
    obtain ⟨v, hv, hvb⟩ := hbasic b' hb'
    have : a' * b' = b' * a' := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, AutIso.toG_mul, ← hua, ← hvb]
      calc y * u * y⁻¹ * (y * v * y⁻¹) = y * (u * v) * y⁻¹ := by group
        _ = y * (v * u) * y⁻¹ := by rw [c.iso.Vg_comm hu hv]
        _ = y * v * y⁻¹ * (y * u * y⁻¹) := by group
    exact congrArg Subtype.val this
  have hsq : ∀ a ∈ K, a * a = 1 := by
    intro a ha
    obtain ⟨a', rfl, ha'⟩ := (hK_mem a).1 ha
    obtain ⟨u, hu, hua⟩ := hbasic a' ha'
    have : a' * a' = 1 := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, ← hua, c.iso.toG_one]
      calc y * u * y⁻¹ * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
        _ = 1 := by rw [c.iso.Vg_sq hu]; group
    exact congrArg Subtype.val this
  have hKV : ¬ K ≤ VA := by
    intro hle
    obtain ⟨b, hbT, hbb⟩ := c.iso.mem_imgG.1 (hy a₀ ha₀)
    have hbK : (b : Ah) ∈ K := (hK_mem _).2 ⟨b, rfl, (hVy_mem _).2 ⟨a₀, ha₀, hbb.symm⟩⟩
    exact hna (hbb ▸ c.iso.mem_imgG.2 ⟨b, hle hbK, rfl⟩)
  obtain ⟨r, hrK, hgood⟩ := e16_good hKT hcard hab hsq hKV
  obtain ⟨b, rfl, hbV⟩ := (hK_mem r).1 hrK
  obtain ⟨u, hu, hub⟩ := hbasic b hbV
  obtain ⟨û, hû, rfl⟩ := c.iso.mem_imgG.1 hu
  have hû1 : û ≠ 1 := by
    intro h
    rw [h, c.iso.toG_one] at hub
    have hb1 : c.iso.toG b = 1 := by rw [← hub]; group
    have : b = 1 := c.iso.toG_injective (hb1.trans c.iso.toG_one.symm)
    exact hgood.2.1 (by rw [this]; exact Yh.one_mem)
  have hconj : IsConj (c.iso.toG b) z :=
    (isConj_iff.2 ⟨y, hub⟩ : IsConj (c.iso.toG û) (c.iso.toG b)).symm.trans
      (Vg_isConj c hconj0 hû hû1)
  exact h5 G M₁ M₂ z c (c.iso.toG b) ⟨b, hgood, rfl⟩ hconj

end CFSG.Quasithin.H13.F431.U42Aut
