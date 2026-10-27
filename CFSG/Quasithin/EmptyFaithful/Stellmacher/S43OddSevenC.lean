module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddSevenA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddSevenFin
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

theorem false_of_le_normalizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {β γ : Geo H M} (hβ : β ∈ nbrs α) (hγ : γ ∈ nbrs β) (hγα : γ ≠ α)
    {X : Subgroup G} (hX : X ≤ stab β ⊓ stab γ) (hXQ : ¬ X ≤ Qv β)
    (hXN : X ≤ Subgroup.normalizer (Wn α : Set G)) : False := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hgen := F53.sup_edge_eq_stab hA hβv hγ (nbrs_symm hβ) hγα hX hXQ
  have hNβ : stab β ≤ Subgroup.normalizer (Wn α : Set G) := by
    rw [← hgen]
    exact sup_le hXN (inf_le_right.trans (stab_le_normalizer_Wn α))
  have hWQ : Wn α ≤ Qv α := hs.Wn_le_Qv hA hb
  have hU : Wn α ≤ stab α ⊓ stab β :=
    le_inf (hWQ.trans (pCoreOf_le 2 _)) (hWQ.trans (Qv_le_stab_of_mem_nbrs hA hβ))
  have hbot := eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj α β from hβ) hU
    (stab_le_normalizer_Wn α) hNβ
  exact Zv_ne_bot hA α (le_bot_iff.mp (hbot ▸ hs.Zv_le_Wn hA h26))

theorem comm_eq_of_inv_mul_mem (hA : F53Amalgam H M S) {l : Geo H M} {q z c : G}
    (hc : c ∈ Zv l) (hzq : z⁻¹ * q ∈ Qv l) : ⁅q, c⁆ = ⁅z, c⁆ := by
  have h1 : (z⁻¹ * q) * c = c * (z⁻¹ * q) :=
    (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA l hzq) c hc).symm
  calc ⁅q, c⁆ = z * ((z⁻¹ * q) * c) * (z⁻¹ * q)⁻¹ * z⁻¹ * c⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = z * (c * (z⁻¹ * q)) * (z⁻¹ * q)⁻¹ * z⁻¹ * c⁻¹ := by rw [h1]
    _ = ⁅z, c⁆ := by simp only [commutatorElement_def]; group

theorem comm_mul_eq (hA : F53Amalgam H M S) (hs : Sit43 α) (hb5 : 5 ≤ bMin H M) {q z c : G}
    (hq : q ∈ Wn α) (hzc : ⁅z, c⁆ ∈ Wn α) : ⁅q * z, c⁆ = ⁅z, c⁆ * ⁅q, c⁆ := by
  have hc1 : q * ⁅z, c⁆ = ⁅z, c⁆ * q :=
    Twelve.comm_of_elemAbelian (isElemAbelian_Wn_of_five hA hs hb5) hq hzc
  calc ⁅q * z, c⁆ = (q * ⁅z, c⁆) * q⁻¹ * ⁅q, c⁆ := by simp only [commutatorElement_def]; group
    _ = (⁅z, c⁆ * q) * q⁻¹ * ⁅q, c⁆ := by rw [hc1]
    _ = ⁅z, c⁆ * ⁅q, c⁆ := by group

variable {α' ν β l : Geo H M}

open Twelve

theorem exists_gamma (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hb : 4 ≤ bMin H M) (d : Data α α' ν β l) : ∃ γ ∈ nbrs β, γ ≠ α ∧ Vn α' ≤ Qv γ := by
  obtain ⟨γ, hγ, hdγ⟩ := Core.exists_nbr_dist hA (x := ν) (y := β) (n := bMin H M - 3)
    (by rw [CosetGeom.dist_comm]; have := d.dβ; omega)
  refine ⟨γ, hγ, fun h => ?_, ?_⟩
  · rw [h, CosetGeom.dist_comm] at hdγ
    have := d.dν
    omega
  · have h2 := Core.dist_le_of_mem_nbrs hA (x := γ) (y := ν) (z := α') (nbrs_symm d.hν)
    rw [CosetGeom.dist_comm γ ν] at h2
    exact Core.Vn_le_Qv_of_dist hA hs (d.vtypes hA hs ho).1
      (by rw [CosetGeom.dist_comm]; omega)

theorem exists_mul_of_le_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) (hWQ : Wn α ≤ Qv ν) {w : G} (hw : w ∈ Wn α) :
    ∃ q ∈ Wn α ⊓ Qv α', ∃ z ∈ Zv α, w = q * z := by
  have hwE : w ∈ Qv α' ⊔ Zv α := by
    rw [sup_comm, Core.Zv_sup_Qv_crit hA hs ho d.crit d.hν d.dν]
    exact ⟨pCoreOf_le 2 _ (hWQ hw), Qv_le_stab_of_mem_nbrs hA (nbrs_symm d.hν) (hWQ hw)⟩
  have hZn : Zv α ≤ Subgroup.normalizer (Qv α' : Set G) :=
    (Core.Zv_le_stab_crit hA hs d.crit).trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨q, hq, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZn).mp hwE
  refine ⟨q, ⟨?_, hq⟩, z, hz, rfl⟩
  have := (Wn α).mul_mem hw ((Wn α).inv_mem (hs.Zv_le_Wn hA h26 hz))
  simpa using this

theorem exists_not_inv_mul_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) (hWQ : Wn α ≤ Qv ν) :
    ∃ q ∈ Wn α ⊓ Qv α', ∀ z ∈ Zv α ⊓ Qv α', z⁻¹ * q ∉ Qv l := by
  by_contra hcon
  push Not at hcon
  have hRW := comm_le_Wn hA h26 hs ho d
  have hRV := comm_le_inf hA hs ho d
  have hα'v := (d.vtypes hA hs ho).1
  have hVeq : Zv ν ⊔ Zv l = Vn α' :=
    hs.Zv_sup_Zv_eq hA h26 (by omega) hα'v d.hν d.hl d.lν.symm h6
  have hVab := Sit43.isElemAbelian_Vn_of_three hA (by omega) α'
  have hcV : ∀ a ∈ Vn α', ∀ b ∈ Vn α', a * b = b * a := fun a ha b hb =>
    comm_of_elemAbelian hVab ha hb
  have hnl : Zv l ≤ Subgroup.normalizer (Zv ν : Set G) :=
    (Core.Zv_le_Vn d.hl).trans (le_normalizer_of_comm hcV (Core.Zv_le_Vn d.hν))
  have hwv : ∀ w ∈ Wn α, ∀ v ∈ Vn α', ⁅w, v⁆ ∈ ⁅Vn β, Vn α'⁆ := by
    intro w hw v hv
    obtain ⟨q, hq, z, hz, rfl⟩ := exists_mul_of_le_Qv hA h26 hs ho d hWQ hw
    have hv' : v ∈ Zv ν ⊔ Zv l := by rw [hVeq]; exact hv
    obtain ⟨cν, hcν, cl, hcl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnl).mp hv'
    obtain ⟨z', hz', hz'q⟩ := hcon q hq
    have hql : ⁅q, cl⁆ = ⁅z', cl⁆ := comm_eq_of_inv_mul_mem hA hcl hz'q
    have hR1 : ⁅z', cl⁆ ∈ ⁅Vn β, Vn α'⁆ :=
      Subgroup.commutator_mem_commutator (Sit43.Zv_le_Vn d.hβ hz'.1) (Core.Zv_le_Vn d.hl hcl)
    have hR2 : ⁅z, cν * cl⁆ ∈ ⁅Vn β, Vn α'⁆ :=
      Subgroup.commutator_mem_commutator (Sit43.Zv_le_Vn d.hβ hz) hv
    have h1 : q * cν = cν * q :=
      (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA ν (hWQ hq.1)) cν hcν).symm
    have h2 : cν * ⁅z', cl⁆ = ⁅z', cl⁆ * cν := hcV _ (Core.Zv_le_Vn d.hν hcν) _ (hRV hR1).2
    have hqν : q * cν * q⁻¹ = cν := by rw [h1]; group
    have hqv : ⁅q, cν * cl⁆ = ⁅z', cl⁆ := by
      calc ⁅q, cν * cl⁆ = (q * cν * q⁻¹) * ⁅q, cl⁆ * cν⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = cν * ⁅z', cl⁆ * cν⁻¹ := by rw [hql, hqν]
        _ = (⁅z', cl⁆ * cν) * cν⁻¹ := by rw [h2]
        _ = ⁅z', cl⁆ := by group
    rw [comm_mul_eq hA hs hb5 hq.1 (hRW hR2), hqv]
    exact Subgroup.mul_mem _ hR2 hR1
  obtain ⟨γ, hγ, hγα, hVγ⟩ := exists_gamma hA hs ho (by omega) d
  refine false_of_le_normalizer hA h26 hs (by omega) d.hβ hγ hγα (X := Vn α')
    (le_inf (Core.Vn_le_stab_beta hA hs ho d.crit (d.dist_beta hA))
      (hVγ.trans (pCoreOf_le 2 _)))
    (Core.not_Vn_le_Qv_crit hA h26 hs ho (by omega) d.crit d.hβ (d.dist_beta hA)) ?_
  refine Sit43.le_normalizer_of_conj_mem fun v hv w hw => ?_
  have e : v * w * v⁻¹ = ⁅w, v⁆⁻¹ * w := by simp only [commutatorElement_def]; group
  rw [e]
  exact (Wn α).mul_mem ((Wn α).inv_mem (hRW (hwv w hw v hv))) hw

theorem not_Wn_le_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6β : Nat.card (Vn β) = 2 ^ 6) (h6 : Nat.card (Vn α') = 2 ^ 6) : ¬ Wn α ≤ Qv ν := by
  intro hWQ
  obtain ⟨hα'v, hlv, -⟩ := d.vtypes hA hs ho
  have hRW := comm_le_Wn hA h26 hs ho d
  have hZW : Zv α ≤ Wn α := hs.Zv_le_Wn hA h26
  obtain ⟨qb, hqb, hqbZ⟩ := exists_not_inv_mul_mem hA h26 hs ho hb5 d h6 hWQ
  obtain ⟨za, hza, hzaQ⟩ : ∃ z ∈ Zv α ⊓ Qv α', z ∉ Qv l := by
    have h4d := (crit4d hA h26 hs ho (by omega) d.crit d.hν d.dν d.hβ d.dβ d.hl d.lν).1
    by_contra hcon
    push Not at hcon
    apply h4d
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv z hz
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA l (hcon z hz)) v hv)]
    exact Subgroup.one_mem _
  have hzaW : za ∈ Wn α ⊓ Qv α' := ⟨hZW hza.1, hza.2⟩
  obtain ⟨D'⟩ := (hs.of_vtype_false hlv).exists_dict5 hA (nbrs_symm d.hl)
  have hQl : Qv α' ≤ stab l := Qv_le_stab_of_mem_nbrs hA d.hl
  have hT : ∀ q (hq : q ∈ Wn α ⊓ Qv α'), D'.ψ ⟨q, hQl hq.2⟩ ∈ S5ThatF := by
    intro q hq
    rw [← mem_S5That_iff]
    refine (D'.mem_centralizer_Y_iff ⟨q, hQl hq.2⟩).mp ⟨d.Qv_le_edge hA hq.2, ?_⟩
    rw [← hs.Yv_eq_comm_comm hA h26 hα'v d.hl]
    exact (Sit43.Qv_le_centralizer_Yv hA d.hν (hWQ hq.1)).2
  have ha1 : D'.ψ ⟨za, hQl hza.2⟩ ≠ 1 := fun h => hzaQ ((D'.ker_iff _).mp h)
  have hb1 : D'.ψ ⟨qb, hQl hqb.2⟩ ≠ 1 := fun h =>
    hqbZ 1 (Subgroup.one_mem _) (by rw [inv_one, one_mul]; exact (D'.ker_iff _).mp h)
  have hba : D'.ψ ⟨qb, hQl hqb.2⟩ ≠ D'.ψ ⟨za, hQl hza.2⟩ := by
    intro h
    apply hqbZ za hza
    have h1 : D'.ψ ((⟨za, hQl hza.2⟩ : ↥(stab l))⁻¹ * ⟨qb, hQl hqb.2⟩) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    exact (D'.ker_iff _).mp h1
  obtain ⟨x, hx, hxsw, hxa⟩ : ∃ x, ∃ hx : x ∈ Wn α ⊓ Qv α',
      (D'.ψ ⟨x, hQl hx.2⟩).IsSwap ∧ D'.ψ ⟨x, hQl hx.2⟩ ≠ D'.ψ ⟨za, hQl hza.2⟩ := by
    rcases that_swap_or_swap _ (hT za hzaW) _ (hT qb hqb) ha1 hb1 hba with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨qb, hqb, (isSwap_iff _).mpr ⟨h1, h2, h3⟩, h4⟩
    · refine ⟨qb * za, ⟨(Wn α).mul_mem hqb.1 hzaW.1, (Qv α').mul_mem hqb.2 hza.2⟩, ?_⟩
      have e : D'.ψ ⟨qb * za, hQl ((Qv α').mul_mem hqb.2 hza.2)⟩ =
          D'.ψ ⟨qb, hQl hqb.2⟩ * D'.ψ ⟨za, hQl hza.2⟩ := by
        rw [← map_mul]
        rfl
      rw [e]
      exact ⟨(isSwap_iff _).mpr ⟨h1, h2, h3⟩, h4⟩
  have hξT := hT x hx
  have hξ1 : D'.ψ ⟨x, hQl hx.2⟩ ≠ 1 := ((isSwap_iff _).mp hxsw).1
  have hqc : ∀ q ∈ Wn α ⊓ Qv α', ∀ c ∈ Zv l ⊓ Subgroup.centralizer ({x} : Set G),
      ⁅q, c⁆ = 1 ∨ ⁅q, c⁆ = ⁅za, c⁆ := by
    intro q hq c hc
    obtain ⟨w, rfl⟩ : c ∈ D'.φ.range := D'.range_eq.ge hc.1
    have hcx : D'.φ w * x = x * D'.φ w := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hfix : orth.act (D'.ψ ⟨x, hQl hx.2⟩) w = w := by
      apply D'.inj
      rw [D'.act_eq, ← hcx]
      group
    have hcases := that_eq_of_ne _ (hT za hzaW) _ hξT _ (hT q hq) ha1 hξ1 hxa
    rcases that_act_comm _ (hT za hzaW) _ hξT _ (hT q hq) hcases w hfix with h | h
    · left
      rw [comm_φ_eq D' (hQl hq.2), h, map_one]
    · right
      rw [comm_φ_eq D' (hQl hq.2), h, ← comm_φ_eq D' (hQl hza.2)]
  have hwc : ∀ c ∈ Zv l ⊓ Subgroup.centralizer ({x} : Set G), ∀ w ∈ Wn α,
      ∃ z₁ ∈ Zv α, ∃ z₂ ∈ Zv α, ⁅w, c⁆ = ⁅z₁, c⁆ * ⁅z₂, c⁆ := by
    intro c hc w hw
    obtain ⟨q, hq, z, hz, rfl⟩ := exists_mul_of_le_Qv hA h26 hs ho d hWQ hw
    have hzc : ⁅z, c⁆ ∈ Wn α := hRW (Subgroup.commutator_mem_commutator
      (Sit43.Zv_le_Vn d.hβ hz) (Core.Zv_le_Vn d.hl hc.1))
    rw [comm_mul_eq hA hs hb5 hq.1 hzc]
    rcases hqc q hq c hc with h | h
    · exact ⟨z, hz, 1, (Zv α).one_mem, by rw [h, commutatorElement_one_left]⟩
    · exact ⟨z, hz, za, hza.1, by rw [h]⟩
  have hcR : ∀ c ∈ Zv l ⊓ Subgroup.centralizer ({x} : Set G), ∀ w ∈ Wn α,
      ⁅w, c⁆ ∈ ⁅Vn β, Vn α'⁆ := by
    intro c hc w hw
    obtain ⟨z₁, hz₁, z₂, hz₂, e⟩ := hwc c hc w hw
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.commutator_mem_commutator (Sit43.Zv_le_Vn d.hβ hz₁) (Core.Zv_le_Vn d.hl hc.1))
      (Subgroup.commutator_mem_commutator (Sit43.Zv_le_Vn d.hβ hz₂) (Core.Zv_le_Vn d.hl hc.1))
  obtain ⟨γ, hγ, hγα, hVγ⟩ := exists_gamma hA hs ho (by omega) d
  have hCQ : Zv l ⊓ Subgroup.centralizer ({x} : Set G) ≤ Qv β := by
    by_contra hCQ
    refine false_of_le_normalizer hA h26 hs (by omega) d.hβ hγ hγα ?_ hCQ ?_
    · intro c hc
      exact ⟨Core.Zv_le_stab_beta hA hs ho d.crit (d.dist_beta hA) d.hl hc.1,
        pCoreOf_le 2 _ (hVγ (Core.Zv_le_Vn d.hl hc.1))⟩
    · refine Sit43.le_normalizer_of_conj_mem fun c hc w hw => ?_
      have e : c * w * c⁻¹ = ⁅w, c⁆⁻¹ * w := by simp only [commutatorElement_def]; group
      rw [e]
      exact (Wn α).mul_mem ((Wn α).inv_mem (hRW (hcR c hc w hw))) hw
  have hC2 : (Zv l ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (Zv l) = 2 :=
    (D'.relIndex_centralizer_eq_two_iff ⟨x, hQl hx.2⟩).mpr hxsw
  have hmul := Subgroup.relIndex_mul_card (Zv l ⊓ Subgroup.centralizer ({x} : Set G)) (Zv l)
  rw [inf_of_le_left inf_le_left, hs.card_Zv_false hlv, hC2] at hmul
  obtain ⟨c, hc, hcQ⟩ : ∃ c ∈ Zv l ⊓ Subgroup.centralizer ({x} : Set G), c ∉ Qv α := by
    by_contra hcon
    push Not at hcon
    have hle : Zv l ⊓ Subgroup.centralizer ({x} : Set G) ≤ Yv α' := fun c hc =>
      d.Zv_inf_Qv_le_Yv hA h26 hs ho ⟨hc.1, hcon c hc⟩
    have h4 := Subgroup.card_le_of_le hle
    rw [hs.card_Yv hA h26 hα'v] at h4
    omega
  have hcα : c ∈ stab α := d.Qv_beta_le hA (hCQ hc)
  apply hcQ
  refine hs.faithful hA h26 (by omega) hs.vα d.hβ h6β hcα fun w hw => ?_
  obtain ⟨z₁, hz₁, z₂, hz₂, e⟩ := hwc c hc w hw
  have hZc : ∀ z ∈ Zv α, ⁅z, c⁆ ∈ Zv α := fun z hz => by
    have h1 : c * z⁻¹ * c⁻¹ ∈ Zv α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hcα) _).mp ((Zv α).inv_mem hz)
    have e' : ⁅z, c⁆ = z * (c * z⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
    rw [e']
    exact (Zv α).mul_mem hz h1
  rw [e]
  exact (Zv α).mul_mem (hZc z₁ hz₁) (hZc z₂ hz₂)

end Seven

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
