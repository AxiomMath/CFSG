module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even16C

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace C16

variable {α α' δ ρ : Geo H M}

theorem Wn_le_centralizer_Wn (hs : Sit43 α) (hA : F53Amalgam H M S) (hb : 8 ≤ bMin H M)
    {l : Geo H M} (hl : dist l α = 2) :
    Wn l ≤ Subgroup.centralizer (Wn α : Set G) := by
  refine iSup₂_le fun k' hk' => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun k hk => ?_
  refine (hs.Zv_le_Qv_of_dist_lt_false (hs.vtype_of_dist_two hA hk) ?_).trans
    (Qv_le_centralizer_Zv hA k')
  have h1 := dist_triangle hA.amalgam.gen k α k'
  have h2 := dist_triangle hA.amalgam.gen α l k'
  rw [CosetGeom.dist_comm α l, hl] at h2
  rw [hk] at h1
  rw [CosetGeom.dist_comm k' l] at hk'
  omega

theorem Wn_le_Qv_of_dist_two (hs : Sit43 α) (hA : F53Amalgam H M S) (hb : 6 ≤ bMin H M)
    {l : Geo H M} (hl : dist l α = 2) : Wn l ≤ Qv α := by
  have hsl := hs.of_vtype_false (hs.vtype_of_dist_two hA hl)
  refine iSup₂_le fun k hk => hs.Zv_le_Qv_of_dist_lt_false (hsl.vtype_of_dist_two hA hk) ?_
  have h1 := dist_triangle hA.amalgam.gen k l α
  rw [hk, hl] at h1
  omega

theorem false_of_cfg (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 6 ≤ bMin H M) (h14 : ∀ {γ : Geo H M}, Sit43 γ → Claim14 γ)
    (h15 : ∀ {γ : Geo H M}, Sit43 γ → Claim15 γ) (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) :
    False := by
  have hWQ : ¬ Wn α ≤ Qv ρ := fun h => not_Wn_le_stab hA h26 hs he (by omega) (h14 hs) (h15 hs)
    hno hc (h.trans (Qv_le_stab_of_mem_nbrs hA hc.hδρ))
  obtain ⟨l, hl2, hlQ⟩ : ∃ l : Geo H M, dist l α = 2 ∧ ¬ Zv l ≤ Qv ρ := by
    by_contra hcon
    push Not at hcon
    exact hWQ (iSup₂_le fun l hl => hcon l hl)
  have hlv : vtype l = false := hs.vtype_of_dist_two hA hl2
  have hsl : Sit43 l := hs.of_vtype_false hlv
  have hlρ : dist l ρ = bMin H M := by
    have h1 := dist_triangle hA.amalgam.gen l α ρ
    rw [hl2, hc.dρ] at h1
    by_contra hne
    exact hlQ (hs.Zv_le_Qv_of_dist_lt_false hlv (by omega))
  obtain ⟨k3, hk3, hdk3⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := ρ)
    (d := bMin H M - 3) (by rw [hc.dρ]; omega)
  obtain ⟨k4, hk4, hdk4⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := k3)
    (d := bMin H M - 4) (by rw [hdk3]; omega)
  have hlk3 : dist l k3 = bMin H M - 1 := by
    have h1 := dist_triangle hA.amalgam.gen l α k3
    have h2 := dist_triangle hA.amalgam.gen l k3 ρ
    rw [dist_eq_one_iff_adj.mpr hk3.symm] at h2
    rw [hl2, hdk3] at h1
    omega
  have hlk4 : dist l k4 = bMin H M - 2 := by
    have h1 := dist_triangle hA.amalgam.gen l α k4
    have h2 := dist_triangle hA.amalgam.gen l k4 k3
    rw [dist_eq_one_iff_adj.mpr hk4.symm] at h2
    rw [hl2, hdk4] at h1
    omega
  have hcl : Cfg l ρ k3 k4 := ⟨⟨hlQ, hlρ⟩, hk3, hlk3, hk4, hlk4⟩
  have hnol : ¬ Claim17 l := fun h => hno (claim17_of_vtype_eq (hlv.trans hs.vα.symm) h)
  obtain ⟨w', hw', hw'ρ⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_Wn_inf_le_stab hA h26 hsl he (by omega) (h14 hsl) (h15 hsl) hnol hcl)
  have hWk4 : Wn l ≤ stab k4 := (h14 hsl hcl.crit hcl.hδ hcl.dδ hcl.hρ hcl.dρ).1
  have hk3v : vtype k3 = true := hcl.vδ hA hsl he
  have hk4v : vtype k4 = false := hcl.vρ hA hsl he
  have hw'Q : w' ∉ Qv k3 := fun h => hw'ρ (Qv_le_stab_of_mem_nbrs hA hcl.hα'δ h)
  have hk4ρ : k4 ≠ ρ := by
    intro h
    rw [h, hc.dρ] at hdk4
    omega
  have hS14 : ∀ {U : Subgroup G}, U ≤ Zv ρ → conjSub w' U = U → U ≤ Yv k3 := fun hU hUw =>
    hs.S14 hA h26 hk3v hk4 hcl.hα'δ hk4ρ (hWk4 hw'.1) hw'.2 hw'Q hU hUw
  have hY4 : Nat.card (Yv k3) = 4 := hs.card_Yv hA h26 hk3v
  obtain ⟨m, hm⟩ := he
  rcases (by omega : bMin H M = 6 ∨ 8 ≤ bMin H M) with h6 | h8
  ·
    have hU4 := four_le_card_Zv_inf hA h26 hs ⟨m, hm⟩ hb (h14 hs) (h15 hs) hno hc
    have hw'C : w' ∈ Subgroup.centralizer ((Zv α ⊓ Zv ρ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (fun _ hz => hz.1)
        (Qv_le_centralizer_Zv hA α (Wn_le_Qv_of_dist_two hs hA hb hl2 hw'.1))
    have hUY := hS14 inf_le_right (conjSub_eq_of_mem_centralizer hw'C)
    have hUeq : Zv α ⊓ Zv ρ = Yv k3 :=
      Subgroup.eq_of_le_of_card_ge hUY (by rw [hY4]; exact hU4)
    have hk4α : dist k4 α = 2 := by rw [CosetGeom.dist_comm, hdk4]; omega
    obtain ⟨β, hβ, hk4β⟩ := Sit43.exists_common_nbr_of_dist_two (α := α) hA hk4α
    have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
    have hαk4 : α ≠ k4 := by
      intro h
      rw [h, CosetGeom.dist_self] at hk4α
      omega
    have hYβ := hs.inf_Zv_eq_Yv hA h26 hβv (nbrs_symm hβ) hk4β hαk4
    have hle : Yv k3 ≤ Yv β := by
      rw [← hYβ]
      exact le_inf (hUeq ▸ inf_le_left) (Yv_le_Zv hk4)
    have hYeq : Yv k3 = Yv β :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hY4, hs.card_Yv hA h26 hβv])
    have hk3β := eq_of_Yv_eq hA h26 hs hk4v (nbrs_symm hk4) (nbrs_symm hk4β) hYeq
    have h1 : dist α β = 1 := dist_eq_one_iff_adj.mpr hβ
    rw [← hk3β, hdk3] at h1
    omega
  ·
    have hw'C : w' ∈ Subgroup.centralizer ((⁅Wn α ⊓ stab δ, Vn δ⁆ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (fun r hr => R0_le_Wn hA hs ⟨m, hm⟩ hc hr)
        (Wn_le_centralizer_Wn hs hA h8 hl2 hw'.1)
    have hRY := hS14 (R0_le_Zv hA h26 hs ⟨m, hm⟩ hb (h14 hs) (h15 hs) hno hc)
      (conjSub_eq_of_mem_centralizer hw'C)
    have h1 := Subgroup.card_le_of_le hRY
    have h2 := eight_le_card_R0 hA h26 hs ⟨m, hm⟩ (by omega) (h14 hs) (h15 hs) hno hc
    omega

end C16

theorem claim16 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (he : Even (bMin H M)) (hb : 6 ≤ bMin H M)
    (h14 : ∀ {γ : Geo H M}, Sit43 γ → Claim14 γ) (h15 : ∀ {γ : Geo H M}, Sit43 γ → Claim15 γ) :
    Claim17 α := by
  by_contra hno
  obtain ⟨α', hc⟩ := hs.exists_crit_partner hA
  obtain ⟨δ, ρ, hcfg⟩ := C16.exists_cfg hA (by omega) hc
  exact C16.false_of_cfg hA h26 hs he hb h14 h15 hno hcfg

end CFSG.Quasithin.F53.Stellmacher.S43.Even
