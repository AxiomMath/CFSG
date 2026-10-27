module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R4

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section C1

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

@[expose] def C1G (c : AutCtx G M₁ M₂ z) (R : Subgroup G) : Subgroup G :=
  R ⊓ Subgroup.centralizer (B1G c : Set G)

theorem V1G_eq_toG1 {v : Ah} (hvB : v ∈ Bh) :
    c.iso.toG ⟨v, hvB⟩ = c.iso.toG1 ⟨v, Bh_le_P1h hvB⟩ :=
  (c.iso.toG1_inclusion ⟨v, hvB⟩).symm

theorem conj_b1G_cases (h : F55Ctx c R) {n : G} (hn : n ∈ NV c R) :
    ∃ w ∈ V1G c, n * b1G c * n⁻¹ = w * b1G c * w⁻¹ := by
  have hy : n * b1G c * n⁻¹ ∈ B1G c := conj_B1G c h hn.1 (b1G_mem_B1G c)
  obtain ⟨p, hp, hpy⟩ := (mem_B1G_iff c).1 hy
  have hrel : ∀ v ∈ Kl1h, (p : Ah) * v = (b1A * v * b1A⁻¹) * p := by
    intro v hv
    have hvB : v ∈ Bh := Kl1h_le_Bh hv
    have hv2 : b1A * v * b1A⁻¹ ∈ Kl1h := b1A_conj_Kl1h hv
    have hv2B : b1A * v * b1A⁻¹ ∈ Bh := Kl1h_le_Bh hv2
    set vP : ↥P1h := ⟨v, Bh_le_P1h hvB⟩ with hvP
    set uP : ↥P1h := b1P * vP * b1P⁻¹ with huP
    have huP' : (uP : Ah) = b1A * v * b1A⁻¹ := rfl
    have hw : c.iso.toG1 vP ∈ V1G c :=
      c.iso.mem_imgG.2 ⟨⟨v, hvB⟩, hv, V1G_eq_toG1 c hvB⟩
    have hu : c.iso.toG1 uP ∈ V1G c :=
      c.iso.mem_imgG.2 ⟨⟨b1A * v * b1A⁻¹, hv2B⟩, hv2, V1G_eq_toG1 c hv2B⟩
    have c1 := NV_comm_V1G c h hn hw
    have c2 := NV_comm_V1G c h hn hu
    have c1' : n⁻¹ * c.iso.toG1 vP = c.iso.toG1 vP * n⁻¹ := by
      calc n⁻¹ * c.iso.toG1 vP = n⁻¹ * (c.iso.toG1 vP * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * c.iso.toG1 vP) * n⁻¹ := by rw [c1]
        _ = c.iso.toG1 vP * n⁻¹ := by group
    have huy : c.iso.toG1 uP = b1G c * c.iso.toG1 vP * (b1G c)⁻¹ := by
      rw [huP, map_mul, map_mul, map_inv]
      rfl
    have key : c.iso.toG1 p * c.iso.toG1 vP = c.iso.toG1 uP * c.iso.toG1 p := by
      rw [hpy]
      calc n * b1G c * n⁻¹ * c.iso.toG1 vP
          = n * b1G c * (n⁻¹ * c.iso.toG1 vP) := by group
        _ = n * (b1G c * c.iso.toG1 vP) * n⁻¹ := by rw [c1']; group
        _ = n * (c.iso.toG1 uP * b1G c) * n⁻¹ := by rw [huy]; group
        _ = (n * c.iso.toG1 uP) * b1G c * n⁻¹ := by group
        _ = (c.iso.toG1 uP * n) * b1G c * n⁻¹ := by rw [c2]
        _ = c.iso.toG1 uP * (n * b1G c * n⁻¹) := by group
    have key' : p * vP = uP * p := c.iso.toG1_injective (by rw [map_mul, map_mul]; exact key)
    exact congrArg (fun x : ↥P1h => (x : Ah)) key'
  obtain ⟨ω, hω, hpω⟩ := Alt1_inner_elt hp hrel
  have hωB : ω ∈ Bh := Kl1h_le_Bh hω
  have hW : c.iso.toG ⟨ω, hωB⟩ ∈ V1G c := c.iso.mem_imgG.2 ⟨⟨ω, hωB⟩, hω, rfl⟩
  have hW2 : c.iso.toG ⟨ω, hωB⟩ ^ 2 = 1 := ((mem_V1G_iff c).1 hW).2
  have hWinv : (c.iso.toG ⟨ω, hωB⟩)⁻¹ = c.iso.toG ⟨ω, hωB⟩ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hW2]
  refine ⟨c.iso.toG ⟨ω, hωB⟩, hW, ?_⟩
  rw [← hpy, hWinv]
  have hp' : p = ⟨ω, Bh_le_P1h hωB⟩ * b1P * ⟨ω, Bh_le_P1h hωB⟩ := Subtype.ext hpω
  rw [hp', map_mul, map_mul, ← V1G_eq_toG1 c hωB]
  rfl

theorem card_CNb (h : F55Ctx c R) :
    8 ≤ Nat.card ↥(NV c R ⊓ Subgroup.centralizer ({b1G c} : Set G)) := by
  classical
  have h1 := card_le_mul_of_conj_elt (H := NV c R) (x := b1G c)
    (S := ([1, dG c, aG c, aG c * dG c].map fun w => w * b1G c * w⁻¹).toFinset) (fun n hn => ?_)
  · have hS : ([1, dG c, aG c, aG c * dG c].map
        fun w => w * b1G c * w⁻¹).toFinset.card ≤ 4 :=
      (List.toFinset_card_le _).trans (by simp)
    have h32 := card_NV c h
    have : 32 ≤ Nat.card ↥(NV c R ⊓ Subgroup.centralizer ({b1G c} : Set G)) * 4 :=
      h32.trans (h1.trans (Nat.mul_le_mul_left _ hS))
    omega
  · obtain ⟨w, hw, hwy⟩ := conj_b1G_cases c h hn
    rw [hwy, List.mem_toFinset, List.mem_map]
    refine ⟨w, ?_, rfl⟩
    rcases mem_V1G_four c hw with h2 | h2 | h2 | h2 <;> simp [h2]

theorem CNb_le_C1G (h : F55Ctx c R) :
    NV c R ⊓ Subgroup.centralizer ({b1G c} : Set G) ≤ C1G c R := by
  rintro n ⟨hn, hnb⟩
  refine ⟨hn.1, ?_⟩
  have hnb' : n * b1G c = b1G c * n := Subgroup.mem_centralizer_singleton_iff.1 hnb
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro g hg
  obtain ⟨p, hp, rfl⟩ := (mem_B1G_iff c).1 hg
  obtain ⟨κ, hκ, i, -, hκi⟩ := mem_Alt1h_dec hp
  have hκB : κ ∈ Bh := Kl1h_le_Bh hκ
  have hp' : p = ⟨κ, Bh_le_P1h hκB⟩ * b1P ^ i := Subtype.ext (by rw [hκi]; rfl)
  have hV : c.iso.toG1 p = c.iso.toG ⟨κ, hκB⟩ * b1G c ^ i := by
    rw [hp', map_mul, map_pow, ← V1G_eq_toG1 c hκB]
    rfl
  have hVm : c.iso.toG ⟨κ, hκB⟩ ∈ V1G c := c.iso.mem_imgG.2 ⟨⟨κ, hκB⟩, hκ, rfl⟩
  have c1 := NV_comm_V1G c h hn hVm
  have c2 : n * b1G c ^ i = b1G c ^ i * n := (Commute.pow_right (hnb' : Commute n (b1G c)) i).eq
  rw [hV]
  calc c.iso.toG ⟨κ, hκB⟩ * b1G c ^ i * n = c.iso.toG ⟨κ, hκB⟩ * (b1G c ^ i * n) := by group
    _ = c.iso.toG ⟨κ, hκB⟩ * (n * b1G c ^ i) := by rw [c2]
    _ = (c.iso.toG ⟨κ, hκB⟩ * n) * b1G c ^ i := by group
    _ = (n * c.iso.toG ⟨κ, hκB⟩) * b1G c ^ i := by rw [c1]
    _ = n * (c.iso.toG ⟨κ, hκB⟩ * b1G c ^ i) := by group

theorem card_C1G (h : F55Ctx c R) : 8 ≤ Nat.card ↥(C1G c R) :=
  (card_CNb c h).trans (Subgroup.card_le_of_le (CNb_le_C1G c h))

end C1

end CFSG.Quasithin.H13.F431.U42Aut
