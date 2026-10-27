module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9Dih
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7S3F

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem exists_elt_Kl1 {l : PL} (hl : l ∈ Kl1L) : ∃ a : Ah, a ∈ Kl1h ∧ RepL l (a : P45) := by
  obtain ⟨a, -, hr⟩ := exists_elt_Alt1 (Kl1_check.2.2.2.2 l hl).2.1
  exact ⟨a, ⟨l, hl, hr⟩, hr⟩

theorem exists_elt_B1 {l : PL} (hl : l ∈ Bl1) :
    ∃ a : Ah, a ∈ B1h ∧ RepL l (a : P45) := by
  obtain ⟨a, -, hr⟩ := exists_That_of_mem_Thl (Bl_thl.1 l hl)
  exact ⟨a, ⟨l, hl, hr⟩, hr⟩

theorem KB_inter : ∀ l ∈ Kl1L, l ∈ Bl1 → l = idL ∨ l = dL := by decide +kernel

theorem Kl1_sq : ∀ l ∈ Kl1L, comp l l = idL := fun l hl => (Kl1_check.2.2.2.2 l hl).2.2

theorem Uh_prod :
    ∀ u ∈ Uh, ∃ k ∈ Kl1h, ∃ l ∈ B1h, u = k * l := by
  rintro u ⟨l, hl, hrep⟩
  obtain ⟨kL, hk, lL, hl', hkl⟩ := U_struct.1 l hl
  obtain ⟨κ, hκ, hκr⟩ := exists_elt_Kl1 hk
  obtain ⟨μ, hμ, hμr⟩ := exists_elt_B1 hl'
  refine ⟨κ, hκ, μ, hμ, ?_⟩
  have h1 : RepL l ((κ : P45) * (μ : P45)) := by
    rw [← hkl]
    exact repL_mul hκr hμr
  exact Subtype.ext (eq_of_repL hrep h1)

theorem mul_mem_Uh {k l : Ah} (hk : k ∈ Kl1h) (hl : l ∈ B1h) :
    k * l ∈ Uh := by
  obtain ⟨kL, hkL, hkr⟩ := hk
  obtain ⟨lL, hlL, hlr⟩ := hl
  exact ⟨comp kL lL, U_struct.2.1 kL hkL lL hlL, repL_mul hkr hlr⟩

theorem Kl1h_le_Bh : Kl1h ≤ Bh := Kl1h_le_That.trans That_le_Bh

theorem B1h_le_Bh : B1h ≤ Bh :=
  B1h_le_A2h.trans (A2h_le_That.trans That_le_Bh)

theorem Uh_le_Bh : Uh ≤ Bh := Uh_le_That.trans That_le_Bh

theorem Kl1h_sq {a : Ah} (ha : a ∈ Kl1h) : a * a = 1 := by
  obtain ⟨l, hl, hr⟩ := ha
  exact eq_of_repL_eq (repL_mul hr hr) (repL_one 45) (Kl1_sq l hl)

@[expose] noncomputable def dA : Ah :=
  Classical.choose (exists_elt_Kl1 (l := dL) (by decide +kernel))

theorem dA_mem_Kl1h : dA ∈ Kl1h :=
  (Classical.choose_spec (exists_elt_Kl1 (l := dL) (by decide +kernel))).1

theorem repL_dA : RepL dL (dA : P45) :=
  (Classical.choose_spec (exists_elt_Kl1 (l := dL) (by decide +kernel))).2

theorem dA_mem_B1h : dA ∈ B1h :=
  ⟨dL, U_struct.2.2.2.1, repL_dA⟩

theorem dA_sq : dA * dA = 1 := Kl1h_sq dA_mem_Kl1h

theorem dA_ne_one : dA ≠ 1 := by
  intro h
  have h1 : RepL idL (dA : P45) := by
    rw [h]
    exact repL_one 45
  exact U_struct.2.2.2.2.1 (repL_unique repL_dA h1)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

@[expose] noncomputable def dB : ↥Bh := ⟨dA, Kl1h_le_Bh dA_mem_Kl1h⟩

section R

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

@[expose] def V1G : Subgroup G := c.iso.imgG Kl1h

@[expose] def V2G : Subgroup G := c.iso.imgG B1h

@[expose] def UG : Subgroup G := c.iso.imgG Uh

@[expose] noncomputable def dG : G := c.iso.toG dB

theorem V1G_le_B1G : V1G c ≤ B1G c := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hg
  refine (mem_B1G_iff c).2 ⟨Subgroup.inclusion Bh_le_P1h b, Kl1h_le_Alt1h hb, ?_⟩
  exact c.iso.toG1_inclusion b

theorem mem_V1G_iff {g : G} : g ∈ V1G c ↔ g ∈ B1G c ∧ g ^ 2 = 1 := by
  constructor
  · intro hg
    refine ⟨V1G_le_B1G c hg, ?_⟩
    obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hg
    have hb2 : b * b = 1 := Subtype.ext (Kl1h_sq hb)
    rw [pow_two, ← AutIso.toG_mul, hb2, AutIso.toG_one]
  · rintro ⟨hg, hg2⟩
    obtain ⟨p, hp, rfl⟩ := (mem_B1G_iff c).1 hg
    have hp2 : p * p = 1 := by
      apply c.iso.toG1_injective
      rw [map_mul, map_one, ← pow_two]
      exact hg2
    have hp2' : (p : Ah) * (p : Ah) = 1 := by
      have := congrArg (fun x : ↥P1h => (x : Ah)) hp2
      simpa using this
    have hpl : (p : Ah) ∈ Kl1h := by
      obtain ⟨l, hl, hrep⟩ := hp
      have hll : comp l l = idL := by
        have h1 := repL_mul hrep hrep
        have h2 : ((p : Ah) : P45) * ((p : Ah) : P45) = 1 := by
          have := congrArg (fun x : Ah => (x : P45)) hp2'
          simpa using this
        rw [h2] at h1
        exact repL_unique h1 (repL_one 45)
      exact ⟨l, Alt1_invol l hl hll, hrep⟩
    refine c.iso.mem_imgG.2 ⟨⟨p, Kl1h_le_Bh hpl⟩, hpl, ?_⟩
    exact (c.iso.toG1_inclusion ⟨p, Kl1h_le_Bh hpl⟩).symm

theorem conj_V1G (h : F55Ctx c R) {n : G} (hn : n ∈ R) {g : G} (hg : g ∈ V1G c) :
    n * g * n⁻¹ ∈ V1G c := by
  rw [mem_V1G_iff] at hg ⊢
  refine ⟨?_, ?_⟩
  · rw [B1G_eq_oddCl] at hg ⊢
    exact oddCl_conj (fun x hx => conj_E1G c h hn hx) hg.1
  · calc (n * g * n⁻¹) ^ 2 = n * g ^ 2 * n⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hg.2]; group

theorem dG_ne_one : dG c ≠ 1 := by
  intro h
  have h1 : dB = 1 := c.iso.toG_injective (by rw [AutIso.toG_one]; exact h)
  exact dA_ne_one (congrArg (fun x : ↥Bh => (x : Ah)) h1)

theorem dG_mem_V1G : dG c ∈ V1G c := c.iso.mem_imgG.2 ⟨dB, dA_mem_Kl1h, rfl⟩

theorem dG_mem_V2G : dG c ∈ V2G c := c.iso.mem_imgG.2 ⟨dB, dA_mem_B1h, rfl⟩

theorem V1G_inf_V2G {g : G} (h1 : g ∈ V1G c) (h2 : g ∈ V2G c) : g = 1 ∨ g = dG c := by
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 h1
  obtain ⟨b', hb', hbb⟩ := c.iso.mem_imgG.1 h2
  have : b' = b := c.iso.toG_injective hbb
  subst this
  obtain ⟨l, hl, hr⟩ := hb
  obtain ⟨l', hl', hr'⟩ := hb'
  have hll : l = l' := repL_unique hr hr'
  rcases KB_inter l hl (hll ▸ hl') with h | h
  · left
    have hrl : RepL idL ((b' : Ah) : P45) := by
      rw [← h]
      exact hr
    have : b' = 1 := Subtype.ext (Subtype.ext (eq_of_repL hrl (repL_one 45)))
    rw [this, AutIso.toG_one]
  · right
    have hrl : RepL dL ((b' : Ah) : P45) := by
      rw [← h]
      exact hr
    have : b' = dB := Subtype.ext (Subtype.ext (eq_of_repL hrl repL_dA))
    rw [this]
    rfl

theorem R_le_normalizer_A2 (h : F55Ctx c R) :
    R ≤ Subgroup.normalizer (c.iso.imgG A2h : Set G) := by
  set F := c.iso.toG fhB with hF
  have hab := imgG_E16 c.iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha
  have hAR : c.iso.imgG A2h ≤ R := by
    intro a ha
    have haT : a ∈ c.iso.imgG That := imgG_mono' c.iso A2h_le_That ha
    have hFA : F ∈ c.iso.imgG A2h :=
      c.iso.mem_imgG.2 ⟨fhB, ⟨fhatL, A_cent_check.2.2.2.2.2.1, repL_fhat⟩, rfl⟩
    have haF : a ∈ cenOf F := by
      rw [cenOf, Subgroup.mem_centralizer_singleton_iff]
      exact (hab.1 F hFA a ha).symm
    exact h.hTR ⟨haT, haF⟩
  have hA16 : Nat.card ↥(c.iso.imgG A2h) = 16 := by
    rw [c.iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]
  exact le_normalizer_of_dihedral h.hD hAR hA16 hab.2

theorem conj_V2G (h : F55Ctx c R) {n : G} (hn : n ∈ R) {g : G} (hg : g ∈ V2G c) :
    n * g * n⁻¹ ∈ V2G c := by
  have hN := N2_le_normalizer_B1 c h.hZ h.hT₀G (R_le_normalizer_A2 c h hn)
  exact (Subgroup.mem_normalizer_iff.1 hN g).1 hg

theorem dG_central (h : F55Ctx c R) {n : G} (hn : n ∈ R) : n * dG c * n⁻¹ = dG c := by
  rcases V1G_inf_V2G c (conj_V1G c h hn (dG_mem_V1G c)) (conj_V2G c h hn (dG_mem_V2G c)) with
    h1 | h1
  · exfalso
    apply dG_ne_one c
    calc dG c = n⁻¹ * (n * dG c * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  · exact h1

theorem conj_UG (h : F55Ctx c R) {n : G} (hn : n ∈ R) {g : G} (hg : g ∈ UG c) :
    n * g * n⁻¹ ∈ UG c := by
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hg
  obtain ⟨k, hk, l, hl, hbkl⟩ := Uh_prod b hb
  have hkb : (k : Ah) ∈ Bh := Kl1h_le_Bh hk
  have hlb : (l : Ah) ∈ Bh := B1h_le_Bh hl
  have hbe : b = ⟨k, hkb⟩ * ⟨l, hlb⟩ := Subtype.ext hbkl
  have e : c.iso.toG b = c.iso.toG ⟨k, hkb⟩ * c.iso.toG ⟨l, hlb⟩ := by
    rw [hbe, AutIso.toG_mul]
  rw [e]
  have h1 := conj_V1G c h hn (c.iso.mem_imgG.2 ⟨⟨k, hkb⟩, hk, rfl⟩)
  have h2 := conj_V2G c h hn (c.iso.mem_imgG.2 ⟨⟨l, hlb⟩, hl, rfl⟩)
  obtain ⟨k', hk', hk'e⟩ := c.iso.mem_imgG.1 h1
  obtain ⟨l', hl', hl'e⟩ := c.iso.mem_imgG.1 h2
  have e2 : n * (c.iso.toG ⟨k, hkb⟩ * c.iso.toG ⟨l, hlb⟩) * n⁻¹ =
      (n * c.iso.toG ⟨k, hkb⟩ * n⁻¹) * (n * c.iso.toG ⟨l, hlb⟩ * n⁻¹) := by group
  rw [e2, ← hk'e, ← hl'e, ← AutIso.toG_mul]
  exact c.iso.mem_imgG.2 ⟨k' * l', mul_mem_Uh hk' hl', rfl⟩

end R

end CFSG.Quasithin.H13.F431.U42Aut
