module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddSevenA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveSwapB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Seven

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}
variable {α' ν β l : Geo H M}

open Twelve

theorem isSwap_of_card (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 4 ≤ bMin H M) (d : Data α α' ν β l)
    (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G} (hu : u ∈ Zv l ⊓ Qv β)
    (huQ : u ∉ Qv α) (h2 : Nat.card ↥(⁅Vn β, Vn α'⁆ ⊓ Yv β) ≤ 2) :
    (D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩).IsSwap := by
  have huα : u ∈ stab α := d.Qv_beta_le hA hu.2
  have hβv : vtype β = true := Core.vtype_beta hs d.hβ
  have huQst : u ∈ Qst β := ⟨hu.2, d.Zv_le_centralizer_Yv hA hs ho hb hu.1⟩
  have hT : ∀ z ∈ Zv α, u * z * u⁻¹ * z⁻¹ ∈ ⁅Vn β, Vn α'⁆ ⊓ Yv β := by
    intro z hz
    have e : u * z * u⁻¹ * z⁻¹ = ⁅z, u⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    refine Subgroup.inv_mem _ ⟨Subgroup.commutator_mem_commutator (Sit43.Zv_le_Vn d.hβ hz)
      (Core.Zv_le_Vn d.hl hu.1), ?_⟩
    rw [← hs.comm_Zv_Qst hA h26 hβv (nbrs_symm d.hβ)]
    exact Subgroup.commutator_mem_commutator hz huQst
  have hn : u ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have hsec := secIdx_le_of_comm_mem (V := Zv α) (L := ⊥) (T := ⁅Vn β, Vn α'⁆ ⊓ Yv β)
    (A₀ := Zv α) (y := u) (fun a ha b hb => comm_of_elemAbelian (isElemAbelian_Zv hA α) ha hb)
    (stab_le_normalizer_Zv hA α huα) hn bot_le
    (inf_le_right.trans (Yv_le_Zv (nbrs_symm d.hβ))) le_rfl hT
  rw [Subgroup.relIndex_self, one_mul, Subgroup.relIndex_bot_left, secIdx_bot] at hsec
  have hne : (Zv α ⊓ Subgroup.centralizer ({u} : Set G)).relIndex (Zv α) ≠ 1 := by
    intro h1
    apply huQ
    rw [← hs.centralizer_Zv hA hs.vα]
    refine ⟨huα, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.relIndex_eq_one.mp h1 hz).2
  have hpos : 0 < (Zv α ⊓ Subgroup.centralizer ({u} : Set G)).relIndex (Zv α) :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h2' : (Zv α ⊓ Subgroup.centralizer ({u} : Set G)).relIndex (Zv α) = 2 := by omega
  exact (D.relIndex_centralizer_eq_two_iff ⟨u, huα⟩).mp h2'

theorem comm_mem_sup (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) (hWν : Wn α ≤ stab ν)
    {u : G} (hu : u ∈ Zv l ⊓ Qv β) {w : G} (hw : w ∈ Wn α ⊓ stab α') :
    u * w * u⁻¹ * w⁻¹ ∈ Hcomm α α' β l ⊔ Zv α := by
  have hW := isElemAbelian_Wn_of_five hA hs hb5
  have hZW : Zv α ≤ Wn α := hs.Zv_le_Wn hA h26
  have huα : u ∈ stab α := d.Qv_beta_le hA hu.2
  have hwν : w ∈ stab ν ⊓ stab α' := ⟨hWν hw.1, hw.2⟩
  rw [← Core.Zv_sup_Qv_crit hA hs ho d.crit d.hν d.dν, sup_comm] at hwν
  have hZn : Zv α ≤ Subgroup.normalizer (Qv α' : Set G) :=
    (Core.Zv_le_stab_crit hA hs d.crit).trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨q, hq, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZn).mp hwν
  have hqW : q ∈ Wn α := by
    have := (Wn α).mul_mem hw.1 ((Wn α).inv_mem (hZW hz))
    simpa using this
  have hnW := stab_le_normalizer_Wn α huα
  have hnZ := stab_le_normalizer_Zv hA α huα
  have huq : u * q * u⁻¹ ∈ Wn α := (Subgroup.mem_normalizer_iff.mp hnW q).mp hqW
  have huz : u * z * u⁻¹ ∈ Zv α := (Subgroup.mem_normalizer_iff.mp hnZ z).mp hz
  have hc1 : u * q * u⁻¹ * q⁻¹ ∈ Hcomm α α' β l := by
    have h1 : ⁅q, u⁆ ∈ Hcomm α α' β l :=
      Subgroup.commutator_mem_commutator (show q ∈ Wn α ⊓ Qv α' from ⟨hqW, hq⟩) hu
    have e : u * q * u⁻¹ * q⁻¹ = ⁅q, u⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hc2 : u * z * u⁻¹ * z⁻¹ ∈ Zv α := (Zv α).mul_mem huz ((Zv α).inv_mem hz)
  have hqz : z⁻¹ * q⁻¹ = q⁻¹ * z⁻¹ :=
    comm_of_elemAbelian hW ((Wn α).inv_mem (hZW hz)) ((Wn α).inv_mem hqW)
  have hcomm' : (u * z * u⁻¹) * q⁻¹ = q⁻¹ * (u * z * u⁻¹) :=
    comm_of_elemAbelian hW (hZW huz) ((Wn α).inv_mem hqW)
  have e : u * (q * z) * u⁻¹ * (q * z)⁻¹ =
      (u * q * u⁻¹ * q⁻¹) * (u * z * u⁻¹ * z⁻¹) := by
    calc u * (q * z) * u⁻¹ * (q * z)⁻¹ = (u * q * u⁻¹) * (u * z * u⁻¹) * (z⁻¹ * q⁻¹) := by
          group
      _ = (u * q * u⁻¹) * (u * z * u⁻¹) * (q⁻¹ * z⁻¹) := by rw [hqz]
      _ = (u * q * u⁻¹) * ((u * z * u⁻¹) * q⁻¹) * z⁻¹ := by group
      _ = (u * q * u⁻¹) * (q⁻¹ * (u * z * u⁻¹)) * z⁻¹ := by rw [hcomm']
      _ = _ := by group
  rw [e]
  exact Subgroup.mul_mem_sup hc1 hc2

theorem secIdx_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) (hWν : Wn α ≤ stab ν)
    {u : G} (hu : u ∈ Zv l ⊓ Qv β) :
    secIdx (Subgroup.zpowers u) (Zv α) (Wn α) ≤
      (Wn α ⊓ stab α').relIndex (Wn α) * Nat.card (Hcomm α α' β l) := by
  have hW := isElemAbelian_Wn_of_five hA hs hb5
  have hZW : Zv α ≤ Wn α := hs.Zv_le_Wn hA h26
  have huα : u ∈ stab α := d.Qv_beta_le hA hu.2
  have hHW := d.Hcomm_le_Wn hA
  have h1 := secIdx_le_of_comm_mem (V := Wn α) (L := Zv α) (T := Hcomm α α' β l ⊔ Zv α)
    (A₀ := Wn α ⊓ stab α') (fun a ha b hb => comm_of_elemAbelian hW ha hb)
    (stab_le_normalizer_Wn α huα) (stab_le_normalizer_Zv hA α huα) le_sup_right
    (sup_le hHW hZW) inf_le_left
    (fun w hw => comm_mem_sup hA h26 hs ho hb5 d hWν hu hw)
  refine h1.trans (Nat.mul_le_mul_left _ ?_)
  have hn : Hcomm α α' β l ≤ Subgroup.normalizer (Zv α : Set G) :=
    (hHW.trans ((Sit43.Wn_le_Qv hA hs (by omega)).trans (pCoreOf_le 2 _))).trans
      (stab_le_normalizer_Zv hA α)
  rw [Sit43.relIndex_sup_of_le_normalizer hn]
  have h2 := Subgroup.relIndex_mul_card (Zv α) (Hcomm α α' β l)
  have h3 : 0 < Nat.card (Zv α ⊓ Hcomm α α' β l : Subgroup G) := Nat.card_pos
  calc (Zv α).relIndex (Hcomm α α' β l) ≤
        (Zv α).relIndex (Hcomm α α' β l) * Nat.card (Zv α ⊓ Hcomm α α' β l : Subgroup G) :=
        Nat.le_mul_of_pos_right _ h3
    _ = _ := h2

theorem Hcomm_eq_bot (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l)) {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {v₀ : G}
    (hv₀ : v₀ ∈ Zv l) (hne : ⁅v₀, z₁⁆ ≠ 1) {u : G} (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α)
    (hcu : z₁ * u = u * z₁) {K : Subgroup G} (hK : Nat.card K ≤ 2)
    (hHK : Hcomm α α' β l ≤ K) (hvK : ⁅v₀, z₁⁆ ∈ K) : Hcomm α α' β l = ⊥ := by
  refine d.Hcomm_eq_bot_of_forall hA h26 hs ho hb5 D' hz₁ hsw' hu huQ fun a ha => ?_
  by_contra hau
  exact hau (d.comm_eq_one_of_eq hA h26 hs hb5 D' hz₁ hsw' hu.1 hcu ha hv₀
    (Twelve.eq_of_card_le_two hK (hHK (Subgroup.commutator_mem_commutator ha hu)) hvK hau hne))

theorem secIdx_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) (hWν : Wn α ≤ stab ν) {w₀ : G} (hw₀ : w₀ ∈ Wn α)
    (hw₀Q : w₀ ∉ Qv ν) (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G}
    (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α) :
    secIdx (Subgroup.zpowers u) (Zv α) (Wn α) ≤ 2 := by
  have hCR := inf_centralizer_eq_comm hA h26 hs ho hb5 d h6 hWν hw₀ hw₀Q
  have h8 := card_comm_le_eight hA h26 hs ho hb5 d h6 hWν hw₀ hw₀Q
  have hcβ : IsCritPair₃ β α' := Core.isCritPair₃_crit hA hs ho d.crit d.hβ (d.dist_beta hA)
  have h2α' := card_comm_inf_Yv_le_two hA h26 hs ho (by omega) hcβ h8
  have h2β : Nat.card ↥(⁅Vn β, Vn α'⁆ ⊓ Yv β) ≤ 2 := by
    have h := card_comm_inf_Yv_le_two hA h26 hs ho (by omega)
      (crit3_symm hA h26 hs ho (by omega) hcβ) (by rwa [Subgroup.commutator_comm])
    rwa [Subgroup.commutator_comm] at h
  have hsw := isSwap_of_card hA h26 hs ho (by omega) d D hu huQ h2β
  obtain ⟨z₁, hz₁, v₀, hv₀, hne⟩ := d.exists_z₁ hA h26 hs ho (by omega)
  obtain ⟨D'⟩ := (hs.of_vtype_false (d.vtypes hA hs ho).2.1).exists_dict5 hA (nbrs_symm d.hl)
  have hsw' := d.ψ_isSwap hA h26 hs ho (by omega) D hu huQ hsw D' hz₁ hv₀ hne
  have hcu : z₁ * u = u * z₁ := d.commute_of_swap hA h26 hs ho (by omega) D hu huQ hsw hz₁
  have key := secIdx_le hA h26 hs ho hb5 d hWν hu
  by_cases hB : Wn α ≤ stab α'
  · rw [inf_of_le_left hB, Subgroup.relIndex_self, one_mul] at key
    exact key.trans (d.card_Hcomm_le_two_of_swap hA h26 hs ho hb5 D' hz₁ hsw' hu huQ hcu)
  · have hHK : Hcomm α α' β l ≤ ⁅Vn β, Vn α'⁆ ⊓ Yv α' := by
      intro x hx
      have hxY := d.Hcomm_le_Yv hA h26 hs ho hb5 hx
      refine ⟨?_, hxY⟩
      rw [← hCR]
      refine ⟨Yv_le_Zv d.hν hxY, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact (comm_of_elemAbelian (isElemAbelian_Wn_of_five hA hs hb5) hw₀
        (d.Hcomm_le_Wn hA hx)).symm
    have hvK : ⁅v₀, z₁⁆ ∈ ⁅Vn β, Vn α'⁆ ⊓ Yv α' := by
      have h4d := (crit4d hA h26 hs ho (by omega) d.crit d.hν d.dν d.hβ d.dβ d.hl d.lν).2
        (Subgroup.commutator_mem_commutator hv₀ hz₁)
      exact ⟨Subgroup.commutator_mono inf_le_left le_rfl h4d.1, h4d.2⟩
    rw [Hcomm_eq_bot hA h26 hs ho hb5 d D' hz₁ hsw' hv₀ hne hu huQ hcu h2α' hHK hvK,
      Subgroup.card_bot, mul_one] at key
    have hle : Qv ν ⊓ Wn α ≤ Wn α ⊓ stab α' := fun x hx =>
      ⟨hx.2, Qv_le_stab_of_mem_nbrs hA (nbrs_symm d.hν) hx.1⟩
    calc secIdx (Subgroup.zpowers u) (Zv α) (Wn α) ≤ (Wn α ⊓ stab α').relIndex (Wn α) := key
      _ ≤ (Qv ν ⊓ Wn α).relIndex (Wn α) :=
          Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
      _ = (Qv ν).relIndex (Wn α) := Subgroup.inf_relIndex_right _ _
      _ ≤ 2 := relIndex_Qv_le_two hA h26 hs ho hb5 d h6 hWν

end Seven

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
