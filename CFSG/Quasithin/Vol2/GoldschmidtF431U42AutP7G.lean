module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7A

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (repL_x)

theorem listSub_le_That {F : List PL} {h1 : idL ∈ F} {hmul : ∀ a ∈ F, ∀ b ∈ F, comp a b ∈ F}
    (hT : ∀ a ∈ F, a ∈ Thl) : listSub F h1 hmul ≤ That := by
  rintro g ⟨a, ha, hrep⟩
  exact (mem_That_iff g).2 ⟨a, hT a ha, hrep⟩

theorem listSub_comm {F : List PL} {h1 : idL ∈ F} {hmul : ∀ a ∈ F, ∀ b ∈ F, comp a b ∈ F}
    (hab : ∀ a ∈ F, ∀ b ∈ F, comp a b = comp b a) {g h : Ah} (hg : g ∈ listSub F h1 hmul)
    (hh : h ∈ listSub F h1 hmul) : g * h = h * g := by
  obtain ⟨a, ha, hrepa⟩ := hg
  obtain ⟨b, hb, hrepb⟩ := hh
  exact Subtype.ext (eq_of_repL (l := comp a b) (repL_mul hrepa hrepb)
    (hab a ha b hb ▸ repL_mul hrepb hrepa))

theorem A_comm_check : (∀ a ∈ Al1, ∀ b ∈ Al1, comp a b = comp b a) ∧
    (∀ a ∈ Al2, ∀ b ∈ Al2, comp a b = comp b a) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem aOf_M1
    (iso : AutIso M₁ M₂) :
    aOf M₁ (iso.toG fhB) = iso.imgG (listSub Al1 A1_check.1 A1_check.2.1) := by
  have hA : pCoreOf 2 (P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) ≤ Bh := by
    rw [pCoreOf_D1]
    exact (listSub_le_That A1_check.2.2.2.1).trans That_le_Bh
  have := pCoreOf_cen_eq_imgG iso iso.phi1 Bh_le_P1h (fun b => iso.toG1_inclusion b) hA
  rw [pCoreOf_D1] at this
  exact this

theorem aOf_M2
    (iso : AutIso M₁ M₂) :
    aOf M₂ (iso.toG fhB) = iso.imgG (listSub Al2 A2_check.1 A2_check.2.1) := by
  have hA : pCoreOf 2 (P2h ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) ≤ Bh := by
    rw [pCoreOf_D2]
    exact (listSub_le_That A2_check.2.2.2.1).trans That_le_Bh
  have := pCoreOf_cen_eq_imgG iso iso.phi2 Bh_le_P2h (fun b => iso.toG2_inclusion b) hA
  rw [pCoreOf_D2] at this
  exact this

theorem card_aOf_M1
    (iso : AutIso M₁ M₂) : Nat.card ↥(aOf M₁ (iso.toG fhB)) = 16 := by
  rw [aOf_M1, iso.card_imgG ((listSub_le_That A1_check.2.2.2.1).trans That_le_Bh)]
  exact card_A1

theorem card_aOf_M2
    (iso : AutIso M₁ M₂) : Nat.card ↥(aOf M₂ (iso.toG fhB)) = 16 := by
  rw [aOf_M2, iso.card_imgG ((listSub_le_That A2_check.2.2.2.1).trans That_le_Bh)]
  exact card_A2

theorem centralizer_imgG_listSub
    (c : AutCtx G M₁ M₂ z) {F : List PL} {h1 : idL ∈ F} {hmul : ∀ a ∈ F, ∀ b ∈ F, comp a b ∈ F}
    (hFT : ∀ a ∈ F, a ∈ Thl) (hab : ∀ a ∈ F, ∀ b ∈ F, comp a b = comp b a) (hx : xL ∈ F)
    (hcent : ∀ g : Ah, (∀ a ∈ listSub F h1 hmul, g * a = a * g) → g ∈ listSub F h1 hmul) :
    Subgroup.centralizer ((c.iso.imgG (listSub F h1 hmul) : Subgroup G) : Set G) =
      c.iso.imgG (listSub F h1 hmul) := by
  set S := listSub F h1 hmul with hS
  have hSB : S ≤ Bh := (listSub_le_That hFT).trans That_le_Bh
  have hxmem : xA ∈ S := ⟨xL, hx, repL_x⟩
  apply le_antisymm
  · intro g hg
    have hxz : z ∈ c.iso.imgG S := by
      have : c.iso.toG xB ∈ c.iso.imgG S := c.iso.mem_imgG.2 ⟨xB, hxmem, rfl⟩
      rwa [c.iso.toG_xB c.z2 c.z1 c.zc] at this
    have hgz : g * z = z * g := ((Subgroup.mem_centralizer_iff.1 hg) z hxz).symm
    have hgM : g ∈ M₁ := c.cz (Subgroup.mem_centralizer_singleton_iff.2 hgz)
    set p : ↥P1h := c.iso.phi1.symm ⟨g, hgM⟩ with hp
    have hpg : c.iso.toG1 p = g := by
      show ((c.iso.phi1 (c.iso.phi1.symm ⟨g, hgM⟩) : ↥M₁) : G) = g
      rw [MulEquiv.apply_symm_apply]
    have hpc : ∀ a ∈ S, (p : Ah) * a = a * (p : Ah) := by
      intro a ha
      have hbA : c.iso.toG ⟨a, hSB ha⟩ ∈ c.iso.imgG S := c.iso.mem_imgG.2 ⟨⟨a, hSB ha⟩, ha, rfl⟩
      have h1 := (Subgroup.mem_centralizer_iff.1 hg) _ hbA
      have h2 : p * Subgroup.inclusion Bh_le_P1h ⟨a, hSB ha⟩ =
          Subgroup.inclusion Bh_le_P1h ⟨a, hSB ha⟩ * p := by
        apply c.iso.toG1_injective
        rw [map_mul, map_mul, hpg, c.iso.toG1_inclusion]
        exact h1.symm
      have h3 := congrArg (fun x : ↥P1h => (x : Ah)) h2
      simpa only [Subgroup.coe_mul, Subgroup.coe_inclusion] using h3
    have hpS : (p : Ah) ∈ S := hcent p hpc
    refine c.iso.mem_imgG.2 ⟨⟨p, hSB hpS⟩, hpS, ?_⟩
    rw [← hpg]
    exact (c.iso.toG1_inclusion ⟨p, hSB hpS⟩).symm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨a, ha, rfl⟩ := c.iso.mem_imgG.1 hg
    obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hh
    rw [← AutIso.toG_mul, ← AutIso.toG_mul]
    congr 1
    exact Subtype.ext (listSub_comm hab hb ha)

theorem centralizer_aOf_M1
    (c : AutCtx G M₁ M₂ z) :
    Subgroup.centralizer ((aOf M₁ (c.iso.toG fhB) : Subgroup G) : Set G) =
      aOf M₁ (c.iso.toG fhB) := by
  rw [aOf_M1]
  exact centralizer_imgG_listSub c A1_check.2.2.2.1 A_comm_check.1 A_cent_check.2.2.1
    (fun g hg => centralizer_A1 hg)

theorem centralizer_aOf_M2
    (c : AutCtx G M₁ M₂ z) :
    Subgroup.centralizer ((aOf M₂ (c.iso.toG fhB) : Subgroup G) : Set G) =
      aOf M₂ (c.iso.toG fhB) := by
  rw [aOf_M2]
  exact centralizer_imgG_listSub c A2_check.2.2.2.1 A_comm_check.2 A_cent_check.2.2.2.2.1
    (fun g hg => centralizer_A2 hg)

end CFSG.Quasithin.H13.F431.U42Aut
