module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Dec
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cnt

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

@[expose] noncomputable def aB : ↥Bh := ⟨aA, Kl1h_le_Bh aA_mem_Kl1h⟩

@[expose] noncomputable def b1P : ↥P1h := ⟨b1A, (Alt1h_le_C1 b1A_mem_Alt1h).1⟩

section C1

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

@[expose] noncomputable def aG : G := c.iso.toG aB

@[expose] noncomputable def b1G : G := c.iso.toG1 b1P

theorem aG_mem_V1G : aG c ∈ V1G c := c.iso.mem_imgG.2 ⟨aB, aA_mem_Kl1h, rfl⟩

theorem aG_ne_one : aG c ≠ 1 := by
  intro h
  have h1 : aB = 1 := c.iso.toG_injective (by rw [AutIso.toG_one]; exact h)
  have h2 : aA = 1 := congrArg (fun x : ↥Bh => (x : Ah)) h1
  have hrl : RepL a1L ((aA : Ah) : P45) := repL_aA
  rw [h2] at hrl
  exact a1_facts.1 (repL_unique hrl (repL_one 45))

theorem aG_ne_dG : aG c ≠ dG c := by
  intro h
  have h1 : aB = dB := c.iso.toG_injective h
  have h2 : aA = dA := congrArg (fun x : ↥Bh => (x : Ah)) h1
  have hrl : RepL a1L ((aA : Ah) : P45) := repL_aA
  rw [h2] at hrl
  exact a1_facts.2.1 (repL_unique hrl repL_dA)

theorem mem_V1G_four {g : G} (hg : g ∈ V1G c) :
    g = 1 ∨ g = dG c ∨ g = aG c ∨ g = aG c * dG c := by
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hg
  rcases mem_Kl1h_four hb with h | h | h | h
  · left
    have : b = 1 := Subtype.ext h
    rw [this, AutIso.toG_one]
  · right; left
    have : b = dB := Subtype.ext h
    rw [this]
    rfl
  · right; right; left
    have : b = aB := Subtype.ext h
    rw [this]
    rfl
  · right; right; right
    have : b = aB * dB := Subtype.ext h
    rw [this, AutIso.toG_mul]
    rfl

theorem b1G_mem_B1G : b1G c ∈ B1G c := (mem_B1G_iff c).2 ⟨b1P, b1A_mem_Alt1h, rfl⟩

theorem b1G_cube : b1G c ^ 3 = 1 := by
  have : b1P ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact b1A_cube)
  rw [b1G, ← map_pow, this, map_one]

theorem conj_B1G (h : F55Ctx c R) {n : G} (hn : n ∈ R) {g : G} (hg : g ∈ B1G c) :
    n * g * n⁻¹ ∈ B1G c := by
  rw [B1G_eq_oddCl] at hg ⊢
  exact oddCl_conj (fun x hx => conj_E1G c h hn hx) hg

@[expose] noncomputable def NV (c : AutCtx G M₁ M₂ z) (R : Subgroup G) : Subgroup G :=
  R ⊓ Subgroup.centralizer ({aG c} : Set G)

theorem card_NV (h : F55Ctx c R) : 32 ≤ Nat.card ↥(NV c R) := by
  classical
  have h1 := card_le_mul_of_conj_elt (H := R) (x := aG c)
    (S := {aG c, aG c * dG c}) (fun n hn => ?_)
  · have hS : ({aG c, aG c * dG c} : Finset G).card ≤ 2 := Finset.card_le_two
    have h64 : Nat.card ↥R = 64 := by rw [h.hR64]; norm_num
    have : 64 ≤ Nat.card ↥(NV c R) * 2 :=
      h64 ▸ h1.trans (Nat.mul_le_mul_left _ hS)
    omega
  · have hv := conj_V1G c h hn (aG_mem_V1G c)
    rcases mem_V1G_four c hv with h2 | h2 | h2 | h2
    · exfalso
      apply aG_ne_one c
      calc aG c = n⁻¹ * (n * aG c * n⁻¹) * n := by group
        _ = 1 := by rw [h2]; group
    · exfalso
      apply aG_ne_dG c
      have hd := dG_central c h hn
      calc aG c = n⁻¹ * (n * aG c * n⁻¹) * n := by group
        _ = n⁻¹ * dG c * n := by rw [h2]
        _ = dG c := by
          have : n * dG c = dG c * n := by
            calc n * dG c = (n * dG c * n⁻¹) * n := by group
              _ = dG c * n := by rw [hd]
          calc n⁻¹ * dG c * n = n⁻¹ * (dG c * n) := by group
            _ = n⁻¹ * (n * dG c) := by rw [this]
            _ = dG c := by group
    · simp [h2]
    · simp [h2]

theorem NV_comm_V1G (h : F55Ctx c R) {n : G} (hn : n ∈ NV c R) {g : G} (hg : g ∈ V1G c) :
    n * g = g * n := by
  have hnR : n ∈ R := hn.1
  have hna : n * aG c = aG c * n := Subgroup.mem_centralizer_singleton_iff.1 hn.2
  have hnd : n * dG c = dG c * n := by
    have hd := dG_central c h hnR
    calc n * dG c = (n * dG c * n⁻¹) * n := by group
      _ = dG c * n := by rw [hd]
  rcases mem_V1G_four c hg with rfl | rfl | rfl | rfl
  · simp
  · exact hnd
  · exact hna
  · calc n * (aG c * dG c) = (n * aG c) * dG c := by group
      _ = aG c * (n * dG c) := by rw [hna]; group
      _ = aG c * (dG c * n) := by rw [hnd]
      _ = (aG c * dG c) * n := by group

end C1

end CFSG.Quasithin.H13.F431.U42Aut
