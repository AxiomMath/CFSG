module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20BF

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom Equiv
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_iota {X : Type} [Group X] {ψ Ψ : X →* Perm (Fin 5)}
    (hψ : Function.Surjective ψ) (hk : ψ.ker = Ψ.ker) :
    ∃ ι : Perm (Fin 5) →* Perm (Fin 5), Function.Injective ι ∧ ∀ x, ι (ψ x) = Ψ x := by
  refine ⟨ψ.liftOfSurjective hψ ⟨Ψ, hk.le⟩, ?_, fun x =>
    ψ.liftOfRightInverse_comp_apply _ _ ⟨Ψ, hk.le⟩ x⟩
  rw [injective_iff_map_eq_one]
  intro σ hσ
  obtain ⟨x, rfl⟩ := hψ σ
  have h1 : Ψ x = 1 := by
    rw [← ψ.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hψ) ⟨Ψ, hk.le⟩ x]
    exact hσ
  rw [← MonoidHom.mem_ker, hk]
  exact h1

theorem map_S5That_le {ι : Perm (Fin 5) →* Perm (Fin 5)} (hι : Function.Injective ι)
    (hD : ∀ σ ∈ S5Syl, ι σ ∈ S5Syl) {σ : Perm (Fin 5)} (hσ : σ ∈ S5That) : ι σ ∈ S5That := by
  have hle := exists_map_S5That hι hD
  have heq : S5That.map ι = S5That :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective hι])).symm
  rw [← heq]
  exact ⟨σ, hσ, rfl⟩

omit [Finite G] in
theorem exists_Mab_of_fix_four {α β : Geo H M} {Ψ : ↥(stab α) →* Perm (Fin 5)}
    (hΨs : Function.Surjective Ψ) (hPS : ((stab α ⊓ stab β).subgroupOf (stab α)).map Ψ = S5Syl)
    {σ : Perm (Fin 5)} (hσ : σ 4 = 4) : ∃ m : ↥(stab α), (m : G) ∈ Mab α β ∧ Ψ m = σ := by
  have hK : ((MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)).comap Ψ).map (stab α).subtype ≤
      Mab α β := by
    refine le_Mab (Subgroup.map_subtype_le _) (fun y hy => ?_) fun heq => ?_
    · refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      have h1 : Ψ ⟨y, hy.1⟩ ∈ S5Syl := by rw [← hPS]; exact ⟨⟨y, hy.1⟩, hy, rfl⟩
      exact S5Syl_le_stab_four h1
    · obtain ⟨z, hz⟩ := hΨs (swap 0 4)
      have hzK : (z : G) ∈ ((MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)).comap Ψ).map
          (stab α).subtype := by rw [heq]; exact z.2
      obtain ⟨w, hw, hwz⟩ := hzK
      have hwz' : w = z := Subtype.ext hwz
      subst hwz'
      have hw' : Ψ w ∈ MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5) := hw
      rw [MulAction.mem_stabilizer_iff, Perm.smul_def, hz] at hw'
      exact absurd hw' (by decide)
  obtain ⟨m, rfl⟩ := hΨs σ
  refine ⟨m, hK ⟨m, ?_, rfl⟩, rfl⟩
  show Ψ m ∈ MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)
  rw [MulAction.mem_stabilizer_iff, Perm.smul_def]
  exact hσ

theorem stab_le_normalizer_Estar (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) : stab α ≤ Subgroup.normalizer (Estar α : Set G) := by
  have hWZ : Wn α ≤ Subgroup.normalizer (Zv α : Set G) :=
    ((hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)).trans (stab_le_normalizer_Zv hA α)
  refine Sit43.le_normalizer_of_conj_mem fun x hx e he => ?_
  obtain ⟨heW, heZ⟩ := (mem_fixSecIn_iff hWZ).mp he
  refine (mem_fixSecIn_iff hWZ).mpr ⟨conj_mem_of_normalizes (stab_le_normalizer_Wn α) hx heW,
    fun a ha => ?_⟩
  have h1 := conj_mem_of_normalizes (stab_le_normalizer_Zv hA α) hx
    (heZ (x⁻¹ * a * x) ((stab α).mul_mem ((stab α).mul_mem ((stab α).inv_mem hx) ha) hx))
  have e : x * ((x⁻¹ * a * x) * e * (x⁻¹ * a * x)⁻¹ * e⁻¹) * x⁻¹ =
      a * (x * e * x⁻¹) * a⁻¹ * (x * e * x⁻¹)⁻¹ := by group
  rwa [e] at h1

theorem Wcomm_le_stab (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α) (hb : 3 ≤ bMin H M) :
    Wcomm α ≤ stab α := by
  rw [Wcomm, Subgroup.commutator_le]
  intro a ha g hg
  have haα : a ∈ stab α := ((hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)) ha
  rw [commutatorElement_def]
  exact (stab α).mul_mem ((stab α).mul_mem ((stab α).mul_mem haα hg) ((stab α).inv_mem haα))
    ((stab α).inv_mem hg)

theorem relIndex_W_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h20 : Out20bc α β) :
    (Subgroup.centralizer (Cst β : Set G)).relIndex (Wcomm α) ≤ 2 := by
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have hcs : cSecIn (stab α) (Zv α) (Wcomm α) = Qv α :=
    IsModelSec.cSecIn_eq_pCoreOf h.sec (quot_stab_five hA hs.vα)
  have hWZ : Wcomm α ≤ Subgroup.normalizer (Zv α : Set G) :=
    (Wcomm_le_stab hA hs hb).trans (stab_le_normalizer_Zv hA α)
  have hWnZ : Wn α ≤ Subgroup.normalizer (Zv α : Set G) :=
    ((hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)).trans (stab_le_normalizer_Zv hA α)
  obtain ⟨hn, θ, β₁, hθs, hθk, hsd⟩ := h.sec
  obtain ⟨Ψ, β₂, hΨs, hkΨ, hsd₂, hPS, -⟩ :=
    hsd.exists_normalized hθs hθk (sylow_stab_inf_left hA hβ)
  rw [hcs] at hkΨ
  obtain ⟨ι, hι, hιψ⟩ := exists_iota D.surj (D.ker_eq.trans hkΨ.symm)
  have hD8 : ∀ σ ∈ S5Syl, ι σ ∈ S5Syl := by
    intro σ hσ
    rw [← D.bar_S] at hσ
    obtain ⟨x, hx, rfl⟩ := hσ
    rw [hιψ, ← hPS]
    exact ⟨x, hx, rfl⟩
  have hQst : ∀ (k : G) (hk : k ∈ stab α), k ∈ Qst β → Ψ ⟨k, hk⟩ ∈ S5That := by
    intro k hk hkQ
    rw [← hιψ]
    refine map_S5That_le hι hD8 ?_
    rw [← D.mem_centralizer_Y_iff, ← hs.Yv_eq_comm_comm hA h26 hβv (nbrs_symm hβ)]
    exact ⟨⟨hk, pCoreOf_le 2 _ hkQ.1⟩, hkQ.2⟩
  obtain ⟨c, hcT, hspan⟩ := exists_gen
  obtain ⟨w₀, hw₀⟩ := QuotientGroup.mk_surjective (β₂ c)
  have hw₀F : (w₀ : G) ∈ fixSecIn (Qst β) (Zv α) (Wcomm α) := by
    rw [mem_fixSecIn_iff hWZ]
    refine ⟨w₀.2, fun k hk => ?_⟩
    have hkα : k ∈ stab α := Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ) hk.1
    obtain ⟨hkx, h1⟩ := hsd₂.equiv ⟨k, hkα⟩ c w₀ hw₀.symm
    rw [hcT _ ((mem_S5That_iff _).mp (hQst k hkα hk)), ← hw₀, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h1
    have h2 : (w₀ : G)⁻¹ * (k * w₀ * k⁻¹) ∈ Zv α := by simpa using h1
    have h3 := conj_mem_of_normalizes hWZ w₀.2 h2
    have e : (w₀ : G) * ((w₀ : G)⁻¹ * (k * w₀ * k⁻¹)) * (w₀ : G)⁻¹ =
        k * w₀ * k⁻¹ * (w₀ : G)⁻¹ := by group
    rwa [e] at h3
  rw [← h.proj] at hw₀F
  have hVα : Vn β ≤ stab α :=
    ((hs.Vn_le_Wn hA h26 hβ).trans (hs.Wn_le_Qv hA hb)).trans (pCoreOf_le 2 _)
  obtain ⟨v, hv, e, he, hve⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
    (hVα.trans (stab_le_normalizer_Estar hA hs hb))).mp hw₀F.1
  have hVC : Vn β ≤ Subgroup.centralizer (Cst β : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  have hZC : Zv α ≤ Subgroup.centralizer (Cst β : Set G) :=
    Subgroup.le_centralizer_iff.mp ((Cst_le_Qv hA hs hβ).trans (Qv_le_centralizer_Zv hA α))
  have := hn
  have hstep : ∀ σ : Perm (Fin 5), σ 4 = 4 →
      orth.act σ c * c⁻¹ ∈ (((Subgroup.centralizer (Cst β : Set G)).subgroupOf (Wcomm α)).map
        (QuotientGroup.mk' ((Zv α).subgroupOf (Wcomm α)))).comap β₂ := by
    intro σ hσ
    obtain ⟨m, hmM, hmσ⟩ := exists_Mab_of_fix_four hΨs hPS hσ
    obtain ⟨hmx, h1⟩ := hsd₂.equiv m c w₀ hw₀.symm
    rw [hmσ] at h1
    rw [Subgroup.mem_comap, map_mul, map_inv, h1, ← hw₀]
    refine ⟨⟨(m : G) * w₀ * (m : G)⁻¹, hmx⟩ * w₀⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      show (m : G) * w₀ * (m : G)⁻¹ * (w₀ : G)⁻¹ ∈ Subgroup.centralizer (Cst β : Set G)
      rw [hve]
      have hz : (m : G) * e * (m : G)⁻¹ * e⁻¹ ∈ Zv α := ((mem_fixSecIn_iff hWnZ).mp he).2 m m.2
      have hmv : (m : G) * v * (m : G)⁻¹ ∈ Subgroup.centralizer (Cst β : Set G) :=
        conj_mem_centralizer ((le_sup_left : Mab α β ≤ Xgrp α β).trans h20.C_normal hmM)
          (hVC hv)
      have e1 : (m : G) * (v * e) * (m : G)⁻¹ * (v * e)⁻¹ =
          ((m : G) * v * (m : G)⁻¹) * ((m : G) * e * (m : G)⁻¹ * e⁻¹) * v⁻¹ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmv (hZC hz)) (Subgroup.inv_mem _ (hVC hv))
    · rw [map_mul, map_inv]
      rfl
  set K' := (((Subgroup.centralizer (Cst β : Set G)).subgroupOf (Wcomm α)).map
    (QuotientGroup.mk' ((Zv α).subgroupOf (Wcomm α)))).comap β₂ with hK'
  have hcommK : commW orth S5Syl ⊤ ≤ K' := by
    intro w hw
    rw [mem_commW_iff orth mem_S5Syl_iff (Uf := Finset.univ) (fun u => by simp) w] at hw
    obtain ⟨a, b, d, rfl⟩ := hspan w hw
    have h01 := hstep (swap 0 1) (by decide)
    have h12 := hstep (swap 1 2) (by decide)
    have h23 := hstep (swap 2 3) (by decide)
    refine K'.mul_mem (K'.mul_mem ?_ ?_) ?_
    · cases a
      · exact K'.one_mem
      · exact h01
    · cases b
      · exact K'.one_mem
      · exact h12
    · cases d
      · exact K'.one_mem
      · exact h23
  have hidx2 : (commW orth S5Syl ⊤).index = 2 := by
    have h1 := Subgroup.card_mul_index (commW orth S5Syl ⊤)
    rw [card_commW_S5Syl, card_orth] at h1
    omega
  have hK'idx : K'.index ≤ 2 := by
    have h1 := Subgroup.index_dvd_of_le hcommK
    rw [hidx2] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  rw [hK', Subgroup.index_comap_of_surjective _ hsd₂.surj,
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)] at hK'idx
  · exact hK'idx
  · rw [QuotientGroup.ker_mk']
    intro x hx
    exact hZC hx

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B
