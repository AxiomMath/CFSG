module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveGeo
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddEleven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Twelve

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

@[expose] def Hcomm (α α' β l : Geo H M) : Subgroup G := ⁅Wn α ⊓ Qv α', Zv l ⊓ Qv β⁆

variable {α' ν β l : Geo H M}

omit [Finite G] in
theorem Yv_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Yv (g • δ) = conjSub (g : G) (Yv δ) := by
  apply le_antisymm
  · rw [le_conjSub_iff]
    refine le_iInf₂ fun l hl => ?_
    have hl' : g • l ∈ nbrs (g • δ) := (smul_adj g).mpr hl
    have h1 := conjSub_mono ((g : G)⁻¹) (Yv_le_Zv hl')
    rwa [Zv_smul, conjSub_conjSub_inv] at h1
  · refine le_iInf₂ fun l hl => ?_
    have hl' : g⁻¹ • l ∈ nbrs δ := by
      have : g⁻¹ • l ∈ nbrs (g⁻¹ • g • δ) := (smul_adj g⁻¹).mpr hl
      rwa [inv_smul_smul] at this
    have h1 := conjSub_mono (g : G) (Yv_le_Zv hl')
    rwa [← Zv_smul, smul_inv_smul] at h1

theorem Data.Hcomm_le_Wn (hA : F53Amalgam H M S) (d : Data α α' ν β l) :
    Hcomm α α' β l ≤ Wn α := by
  unfold Hcomm
  rw [Subgroup.commutator_le]
  intro a ha v hv
  have hvα : v ∈ stab α := d.Qv_beta_le hA hv.2
  have h1 : v * a⁻¹ * v⁻¹ ∈ Wn α :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α hvα) _).mp ((Wn α).inv_mem ha.1)
  have e : ⁅a, v⁆ = a * (v * a⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact (Wn α).mul_mem ha.1 h1

theorem Data.Hcomm_le_Zv (hA : F53Amalgam H M S) (d : Data α α' ν β l) :
    Hcomm α α' β l ≤ Zv l := by
  unfold Hcomm
  rw [Subgroup.commutator_le]
  intro a ha v hv
  have hal : a ∈ stab l := Qv_le_stab_of_mem_nbrs hA d.hl ha.2
  have h1 : a * v * a⁻¹ ∈ Zv l :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA l hal) v).mp hv.1
  have e : ⁅a, v⁆ = (a * v * a⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact (Zv l).mul_mem h1 ((Zv l).inv_mem hv.1)

theorem Data.Hcomm_le_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) :
    Hcomm α α' β l ≤ Yv α' := by
  have hW := isElemAbelian_Wn_of_five hA hs hb5
  obtain ⟨z, hz, hzQ⟩ := d.exists_z
  have hzW : z ∈ Wn α := hs.Zv_le_Wn hA h26 hz
  refine (le_inf (d.Hcomm_le_Wn hA) (d.Hcomm_le_Zv hA)).trans
    (d.le_Yv hA h26 hs ho inf_le_right hz hzQ fun x hx => ?_)
  exact comm_of_elemAbelian hW hzW hx.1

theorem Data.card_Hcomm_le_four (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) :
    Nat.card (Hcomm α α' β l) ≤ 4 :=
  (hs.card_Yv hA h26 (d.vtypes hA hs ho).1) ▸
    Subgroup.card_le_of_le (d.Hcomm_le_Yv hA h26 hs ho hb5)

theorem Data.comm_mem_sup (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ))
    (d : Data α α' ν β l) {κ θ : Geo H M} (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M)
    (hθ : θ ∈ nbrs κ) (hdθ : dist α θ + 3 = bMin H M) {u : G} (hu : u ∈ Zv l ⊓ Qv β)
    {w : G} (hw : w ∈ Wn α ⊓ stab α') : u * w * u⁻¹ * w⁻¹ ∈ Hcomm α α' β l ⊔ Zv α := by
  have hW := isElemAbelian_Wn_of_five hA hs hb5
  have hZW : Zv α ≤ Wn α := hs.Zv_le_Wn hA h26
  have huα : u ∈ stab α := d.Qv_beta_le hA hu.2
  have heq := Wn_inf_stab_eq hA h26 hs ho hb5 hL d.crit d.hν d.dν hκ hdκ hθ hdθ d.hβ d.dβ
  have hwν : w ∈ stab ν ⊓ stab α' := ⟨(heq ▸ hw).2, hw.2⟩
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

theorem Data.secIdx_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ))
    (d : Data α α' ν β l) {κ θ : Geo H M} (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M)
    (hθ : θ ∈ nbrs κ) (hdθ : dist α θ + 3 = bMin H M) {u : G} (hu : u ∈ Zv l ⊓ Qv β) :
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
    (fun w hw => d.comm_mem_sup hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hu hw)
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

theorem Data.exists_w₀ (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ))
    (d : Data α α' ν β l) {κ θ : Geo H M} (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M)
    (hθ : θ ∈ nbrs κ) (hdθ : dist α θ + 3 = bMin H M) (hB : ¬ Wn α ≤ stab α') :
    ∃ w₀ ∈ Wn α, w₀ ∉ stab ν := by
  by_contra hcon
  push Not at hcon
  apply hB
  intro w hw
  exact Wn_inf_stab_le_stab_nbr hA h26 hs ho hb5 hL d.crit d.hν d.dν hκ hdκ hθ hdθ d.hβ d.dβ
    ⟨hw, hcon w hw⟩

theorem le_Yv_kappa (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) {κ : Geo H M} (hκ : κ ∈ nbrs ν)
    (hdκ : dist α κ + 2 = bMin H M) {w₀ : G} (hw₀ : w₀ ∈ Wn α) (hw₀ν : w₀ ∉ stab ν)
    {U : Subgroup G} (hUν : U ≤ Zv ν) (hUW : U ≤ Wn α) : U ≤ Yv κ := by
  have hW := isElemAbelian_Wn_of_five hA hs hb5
  have hκv : vtype κ = true := by
    refine Core.vtype_of_odd hA hs ?_
    obtain ⟨k, hk⟩ := ho
    intro ⟨m, hm⟩
    omega
  have hw₀κ : w₀ ∈ stab κ := Wn_le_stab_of_dist hA hs (le_of_eq hdκ) hw₀
  have hmov : (⟨w₀, stab_le κ hw₀κ⟩ : ↥(H ⊔ M)) • ν ≠ ν := fun h =>
    hw₀ν (mem_stab_of_smul_eq h)
  exact hs.le_Yv_of_normalizes hA h26 hκv (nbrs_symm hκ) hUν hw₀κ hmov
    (conjSub_eq_of_commute fun x hx => comm_of_elemAbelian hW hw₀ (hUW hx))

theorem Data.Yv_ne (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) {κ : Geo H M} (hκ : κ ∈ nbrs ν)
    (hκα' : κ ≠ α') : Yv α' ≠ Yv κ := by
  intro heq
  obtain ⟨hα'v, -, hνv⟩ := d.vtypes hA hs ho
  have hα'ν : α' ∈ nbrs ν := nbrs_symm d.hν
  obtain ⟨g, hgν, hgκ⟩ := stab_transitive_on_nbrs hα'ν hκ
  have hYg : conjSub (g : G) (Yv α') = Yv α' := by
    rw [← Yv_smul, hgκ, ← heq]
  have hgN := mem_normalizer_of_conjSub_eq hYg
  have hsν : Sit43 ν := hs.of_vtype_false hνv
  have hNY := normalizer_Y (quot_stab_five hA hνv) (sylow_stab_inf_left hA hα'ν) hsν.orth
  rw [← hs.Yv_eq_comm_comm hA h26 hα'v d.hν] at hNY
  have hg' : (g : G) ∈ stab ν ⊓ stab α' := hNY ▸ ⟨hgν, hgN⟩
  exact hκα' (hgκ.symm.trans (smul_eq_of_mem_stab hg'.2))

theorem Data.card_Yv_inf_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) {κ : Geo H M} (hκ : κ ∈ nbrs ν)
    (hκα' : κ ≠ α') : Nat.card (Yv α' ⊓ Yv κ : Subgroup G) ≤ 2 := by
  have hκv : vtype κ = true := Sit43.vtype_true_of_adj (d.vtypes hA hs ho).2.2 hκ
  have h4 := hs.card_Yv hA h26 (d.vtypes hA hs ho).1
  have h4' := hs.card_Yv hA h26 hκv
  have hdvd : Nat.card (Yv α' ⊓ Yv κ : Subgroup G) ∣ 2 ^ 2 :=
    (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ h4 ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · rw [hk']; norm_num
  · rw [hk']; norm_num
  · exfalso
    rw [pow_two, show 2 * 2 = 4 by rfl] at hk'
    have e1 : Yv α' ⊓ Yv κ = Yv α' :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', h4])
    have e2 : Yv α' ⊓ Yv κ = Yv κ :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk', h4'])
    exact d.Yv_ne hA h26 hs ho hκ hκα' (e1.symm.trans e2)

omit [Finite G] in
theorem Data.kappa_ne (d : Data α α' ν β l) {κ : Geo H M} (hdκ : dist α κ + 2 = bMin H M) :
    κ ≠ α' := by
  intro h
  rw [h, d.crit.2] at hdκ
  omega

theorem Data.Hcomm_le_inf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ))
    (d : Data α α' ν β l) {κ θ : Geo H M} (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M)
    (hθ : θ ∈ nbrs κ) (hdθ : dist α θ + 3 = bMin H M) (hB : ¬ Wn α ≤ stab α') :
    Hcomm α α' β l ≤ Yv α' ⊓ Yv κ := by
  obtain ⟨w₀, hw₀, hw₀ν⟩ := d.exists_w₀ hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hB
  have hHY := d.Hcomm_le_Yv hA h26 hs ho hb5
  exact le_inf hHY (le_Yv_kappa hA h26 hs ho hb5 hκ hdκ hw₀ hw₀ν
    (hHY.trans (Yv_le_Zv d.hν)) (d.Hcomm_le_Wn hA))

theorem Data.comm_Zv_le_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) : ⁅Zv l, Zv α ⊓ Qv α'⁆ ≤ Wn α := by
  rw [Subgroup.commutator_le]
  intro v hv z hz
  have hvβ : v ∈ stab β := Core.Zv_le_stab_beta hA hs ho d.crit (d.dist_beta hA) d.hl hv
  have hzV : z ∈ Vn β := Sit43.Zv_le_Vn d.hβ hz.1
  have h1 : v * z * v⁻¹ ∈ Vn β :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hvβ) z).mp hzV
  have e : ⁅v, z⁆ = (v * z * v⁻¹) * z⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact hs.Vn_le_Wn hA h26 d.hβ ((Vn β).mul_mem h1 ((Vn β).inv_mem hzV))

theorem Data.comm_Zv_le_inf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ))
    (d : Data α α' ν β l) {κ θ : Geo H M} (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M)
    (hθ : θ ∈ nbrs κ) (hdθ : dist α θ + 3 = bMin H M) (hB : ¬ Wn α ≤ stab α') :
    ⁅Zv l, Zv α ⊓ Qv α'⁆ ≤ Yv α' ⊓ Yv κ := by
  obtain ⟨w₀, hw₀, hw₀ν⟩ := d.exists_w₀ hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hB
  have hY : ⁅Zv l, Zv α ⊓ Qv α'⁆ ≤ Yv α' :=
    (crit4d hA h26 hs ho (by omega) d.crit d.hν d.dν d.hβ d.dβ d.hl d.lν).2.trans inf_le_right
  exact le_inf hY (le_Yv_kappa hA h26 hs ho hb5 hκ hdκ hw₀ hw₀ν (hY.trans (Yv_le_Zv d.hν))
    (d.comm_Zv_le_Wn hA h26 hs ho))

theorem Data.card_Hcomm_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ))
    (d : Data α α' ν β l) {κ θ : Geo H M} (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M)
    (hθ : θ ∈ nbrs κ) (hdθ : dist α θ + 3 = bMin H M) (hB : ¬ Wn α ≤ stab α') :
    Nat.card (Hcomm α α' β l) ≤ 2 :=
  (Subgroup.card_le_of_le (d.Hcomm_le_inf hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hB)).trans
    (d.card_Yv_inf_le_two hA h26 hs ho hκ (d.kappa_ne hdκ))

end Twelve

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
