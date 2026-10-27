module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Tra
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NOrbD

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem comm_of_span (c : AutCtx G M₁ M₂ z) {Kl : List PL} {h1 : idL ∈ Kl}
    {hmul : ∀ a ∈ Kl, ∀ b ∈ Kl, comp a b ∈ Kl} {Sl : List PL}
    (hsp : ∀ a ∈ Kl, ∃ p ∈ idL :: Sl, ∃ q ∈ idL :: Sl, comp p q = a) {n : G}
    (hn : ∀ r ∈ Sl, r ∈ Thl ∧ n * c.iso.toG (eltB r) = c.iso.toG (eltB r) * n) :
    ∀ a ∈ c.iso.imgG (listSub Kl h1 hmul), n * a = a * n := by
  have hid : eltB idL = 1 := by
    apply Subtype.ext
    rw [coe_eltB Thl_check.1]
    exact Subtype.ext (eq_of_repL (repL_eltOfL Thl_check.1) (repL_one 45))
  have hr : ∀ r ∈ idL :: Sl, r ∈ Thl ∧ n * c.iso.toG (eltB r) = c.iso.toG (eltB r) * n := by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · refine ⟨Thl_check.1, ?_⟩
      rw [hid, c.iso.toG_one]
      simp
    · exact hn r hr
  intro a ha
  obtain ⟨b, hbX, rfl⟩ := c.iso.mem_imgG.1 ha
  obtain ⟨l, hl, hrep⟩ := hbX
  obtain ⟨p, hp, q, hq, hpq⟩ := hsp l hl
  obtain ⟨hpT, hpc⟩ := hr p hp
  obtain ⟨hqT, hqc⟩ := hr q hq
  have hbpq : b = eltB p * eltB q := by
    apply Subtype.ext
    apply Subtype.ext
    apply eq_of_repL hrep
    rw [← hpq]
    have hrp : RepL p (eltB p : P45) := by
      rw [coe_eltB hpT]
      exact repL_eltOfL hpT
    have hrq : RepL q (eltB q : P45) := by
      rw [coe_eltB hqT]
      exact repL_eltOfL hqT
    exact repL_mul hrp hrq
  rw [hbpq, AutIso.toG_mul]
  have hc1 : Commute n (c.iso.toG (eltB p)) := hpc
  have hc2 : Commute n (c.iso.toG (eltB q)) := hqc
  exact (hc1.mul_right hc2).eq

theorem comm_of_comm_Om (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) {Kl : List PL} {h1 : idL ∈ Kl}
    {hmul : ∀ a ∈ Kl, ∀ b ∈ Kl, comp a b ∈ Kl} (hT : ∀ l ∈ Kl, l ∈ Thl)
    (hsp : ∀ a ∈ Kl, ∃ p ∈ idL :: Kl.filter (fun l => ZCl.contains l),
      ∃ q ∈ idL :: Kl.filter (fun l => ZCl.contains l), comp p q = a) {n : G}
    (hn : ∀ u ∈ Om (c.iso.imgG (listSub Kl h1 hmul)) z, n * u = u * n) :
    ∀ a ∈ c.iso.imgG (listSub Kl h1 hmul), n * a = a * n := by
  have hXT : listSub Kl h1 hmul ≤ That := listSub_le_That hT
  refine comm_of_span c hsp fun r hr => ?_
  obtain ⟨hrK, hrZ⟩ := List.mem_filter.1 hr
  have hrT := hT r hrK
  have hrep : RepL r (eltB r : P45) := by
    rw [coe_eltB hrT]
    exact repL_eltOfL hrT
  refine ⟨hrT, hn _ ⟨c.iso.mem_imgG.2 ⟨eltB r, ⟨r, hrK, hrep⟩, rfl⟩, ?_⟩⟩
  exact (hZ (hXT ⟨r, hrK, hrep⟩)).2 ⟨r, List.elem_iff.1 hrZ, hrep⟩

theorem z_mem_A1 (c : AutCtx G M₁ M₂ z) : z ∈ c.iso.imgG A1h := by
  have h : c.iso.toG xB ∈ c.iso.imgG A1h :=
    c.iso.mem_imgG.2 ⟨xB, ⟨xL, A_cent_check.2.2.1, repL_x⟩, rfl⟩
  rwa [c.iso.toG_xB c.z2 c.z1 c.zc] at h

theorem z_mem_A2 (c : AutCtx G M₁ M₂ z) : z ∈ c.iso.imgG A2h := by
  have h : c.iso.toG xB ∈ c.iso.imgG A2h :=
    c.iso.mem_imgG.2 ⟨xB, ⟨xL, A_cent_check.2.2.2.2.1, repL_x⟩, rfl⟩
  rwa [c.iso.toG_xB c.z2 c.z1 c.zc] at h

section Orders

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) (hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤)

include hZ hT₀G

theorem card_normalizer_A1 :
    Nat.card ↥(Subgroup.normalizer (c.iso.imgG A1h : Set G)) = 1920 := by
  have h := card_normalizer_eq (z_mem_A1 c) (claimT_A1 c hZ hT₀G)
  have hM : Subgroup.centralizer ({z} : Set G) = M₁ := c.cenOf_z
  rw [ncard_Om_A1 c hZ, hM, c.iso.card_normalizer_M1 (A1h_le_That.trans That_le_Bh),
    card_N1_A1] at h
  omega

theorem card_normalizer_A2 :
    Nat.card ↥(Subgroup.normalizer (c.iso.imgG A2h : Set G)) = 576 := by
  have h := card_normalizer_eq (z_mem_A2 c) (claimT_A2 c hZ hT₀G)
  have hM : Subgroup.centralizer ({z} : Set G) = M₁ := c.cenOf_z
  rw [ncard_Om_A2 c hZ, hM, c.iso.card_normalizer_M1 (A2h_le_That.trans That_le_Bh),
    card_N1_A2] at h
  omega

theorem normalizer_A1_equiv : Nonempty
    (↥(Subgroup.normalizer (c.iso.imgG A1h : Set G)) ⧸
      (c.iso.imgG A1h).subgroupOf (Subgroup.normalizer (c.iso.imgG A1h : Set G)) ≃*
        Equiv.Perm (Fin 5)) := by
  set A := c.iso.imgG A1h with hA
  have hab := imgG_E16 c.iso (K := A1h) (fun a ha b hb => A1h_comm ha hb) fun a ha => A1h_sq ha
  have hcent : Subgroup.centralizer (A : Set G) = A := by
    have := centralizer_aOf_M1 c
    rwa [aOf_M1] at this
  refine quot_equiv_perm (A := A) (m := 5) (Subgroup.le_normalizer) (Om A z) ?_ ?_ ?_ ?_ ?_
  · rintro n hn u ⟨hu, hc0⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hn u).1 hu, ?_⟩
    obtain ⟨c0, hc0⟩ := isConj_iff.1 hc0
    exact isConj_iff.2 ⟨c0 * (n : G)⁻¹, by rw [← hc0]; group⟩
  · intro a ha u hu
    exact hab.1 a ha u hu.1
  · intro n hn hnc
    have hcomm := comm_of_comm_Om c hZ (h1 := A1_check.1) (hmul := A1_check.2.1)
      A1_check.2.2.2.1 span_check.1 hnc
    rw [← hcent]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hcomm a ha).symm
  · exact (Nat.card_coe_set_eq (Om A z)).trans (ncard_Om_A1 c hZ)
  · rw [card_normalizer_A1 c hZ hT₀G, hA, c.iso.card_imgG (A1h_le_That.trans That_le_Bh),
      card_A1h]
    norm_num [Nat.factorial]

end Orders

end CFSG.Quasithin.H13.F431.U42Aut
