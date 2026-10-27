module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] {H M S : Subgroup G}

theorem Yv_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Yv (g • δ) = conjSub (g : G) (Yv δ) := by
  ext z
  rw [mem_conjSub]
  unfold Yv
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h l hl
    have hl' : g • l ∈ nbrs (g • δ) := (smul_adj g).mpr hl
    have h1 := h (g • l) hl'
    rw [Zv_smul, mem_conjSub] at h1
    exact h1
  · intro h l hl
    obtain ⟨l', rfl⟩ : ∃ l', l = g • l' := ⟨g⁻¹ • l, by simp⟩
    have hl' : l' ∈ nbrs δ := (smul_adj g).mp hl
    rw [Zv_smul, mem_conjSub]
    exact h l' hl'

theorem Mab_smul {α : Geo H M} (g : ↥(H ⊔ M)) (hg : (g : G) ∈ stab α) (δ : Geo H M) :
    Mab α (g • δ) = conjSub (g : G) (Mab α δ) := by
  have hα : conjSub (g : G) (stab α) = stab α := conjSub_eq_of_mem hg
  have hα' : conjSub (g : G)⁻¹ (stab α) = stab α := conjSub_eq_of_mem ((stab α).inv_mem hg)
  have hδ : stab (g • δ) = conjSub (g : G) (stab δ) := stab_smul g δ
  apply le_antisymm
  · refine iSup₂_le fun K hK => ?_
    obtain ⟨h1, h2, h3⟩ := hK
    have hK' : conjSub (g : G)⁻¹ K ≤ Mab α δ := by
      refine le_Mab ?_ ?_ ?_
      · rw [← hα']; exact conjSub_mono _ h1
      · have := conjSub_mono (g : G)⁻¹ h2
        rwa [conjSub_inf, hα', hδ, conjSub_conjSub_inv] at this
      · intro heq
        apply h3
        have := congrArg (conjSub (g : G)) heq
        rwa [conjSub_inv_conjSub, hα] at this
    have := conjSub_mono (g : G) hK'
    rwa [conjSub_inv_conjSub] at this
  · refine (conjSub_le_iff _).mpr (iSup₂_le fun K hK => ?_)
    obtain ⟨h1, h2, h3⟩ := hK
    have hK' : conjSub (g : G) K ≤ Mab α (g • δ) := by
      refine le_Mab ?_ ?_ ?_
      · rw [← hα]; exact conjSub_mono _ h1
      · have := conjSub_mono (g : G) h2
        rwa [conjSub_inf, hα, ← hδ] at this
      · intro heq
        apply h3
        have := congrArg (conjSub (g : G)⁻¹) heq
        rwa [conjSub_conjSub_inv, hα'] at this
    have := conjSub_mono (g : G)⁻¹ hK'
    rwa [conjSub_conjSub_inv] at this

omit [Group G] in
theorem commutator_le_left_of_le_normalizer {G : Type} [Group G] {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h hb) _).mp (A.inv_mem ha)
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact A.mul_mem ha h1

theorem conj_eq_of_mem_centralizer' {g : G} {K : Subgroup G}
    (h : g ∈ Subgroup.centralizer (K : Set G)) {y : G} (hy : y ∈ K) : g * y * g⁻¹ = y := by
  have := Subgroup.mem_centralizer_iff.mp h y hy
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

variable [Finite G]

theorem exists_geodesic (hA : F53Amalgam H M S) {α α' : Geo H M} (hd : dist α α' = 4) :
    ∃ β α₂ α₃ : Geo H M, β ∈ nbrs α ∧ α₂ ∈ nbrs β ∧ α₃ ∈ nbrs α₂ ∧ α' ∈ nbrs α₃ ∧
      dist α α₂ = 2 ∧ dist α α₃ = 3 ∧ dist β α' = 3 ∧ dist α₂ α' = 2 := by
  have hG := hA.amalgam.gen
  obtain ⟨α₃, h3, hd3⟩ := exists_adj_dist_eq hG (α := α) (δ := α') (d := 3) (by rw [hd])
  obtain ⟨α₂, h2, hd2⟩ := exists_adj_dist_eq hG (α := α) (δ := α₃) (d := 2) (by rw [hd3])
  obtain ⟨β, h1, hd1⟩ := exists_adj_dist_eq hG (α := α) (δ := α₂) (d := 1) (by rw [hd2])
  have hβ : β ∈ nbrs α := dist_eq_one_iff_adj.mp hd1
  have e1 : dist β α₂ = 1 := dist_eq_one_iff_adj.mpr h1.symm
  have e2 : dist α₂ α₃ = 1 := dist_eq_one_iff_adj.mpr h2.symm
  have e3 : dist α₃ α' = 1 := dist_eq_one_iff_adj.mpr h3.symm
  have t1 := CosetGeom.dist_triangle hG α β α'
  have t2 := CosetGeom.dist_triangle hG β α₂ α'
  have t3 := CosetGeom.dist_triangle hG α₂ α₃ α'
  have t4 := CosetGeom.dist_triangle hG α α₂ α'
  refine ⟨β, α₂, α₃, hβ, h1.symm, h2.symm, h3.symm, hd2, hd3, ?_, ?_⟩ <;> omega

theorem Zv_le_Qst (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α) (hb4 : bMin H M = 4)
    {β α₂ α' : Geo H M} (h2 : α₂ ∈ nbrs β) (hα' : vtype α' = false) (d1 : dist α' β = 3)
    (d2 : dist α' α₂ = 2) : Zv α' ≤ Qst β := by
  have hQβ : Zv α' ≤ Qv β := hs.Zv_le_Qv_of_dist_lt_false hα' (by omega)
  have hQ2 : Zv α' ≤ Qv α₂ := hs.Zv_le_Qv_of_dist_lt_false hα' (by omega)
  refine fun z hz => ⟨hQβ hz, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy2 : y ∈ Zv α₂ := Yv_le_Zv h2 hy
  exact Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α₂ (hQ2 hz)) y hy2

omit [Finite G] in
theorem inf_centralizer_eq_of_mul {Z : Subgroup G} {x z q : G} (hxz : x = z * q)
    (hq : q ∈ Subgroup.centralizer (Z : Set G)) :
    Z ⊓ Subgroup.centralizer ({x} : Set G) = Z ⊓ Subgroup.centralizer ({z} : Set G) := by
  ext w
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  refine and_congr_right fun hw => ?_
  have hqw : w * q = q * w := Subgroup.mem_centralizer_iff.mp hq w hw
  subst hxz
  constructor
  · intro h
    have h1 : z * w * q = w * z * q := by
      calc z * w * q = z * (w * q) := by group
        _ = z * (q * w) := by rw [hqw]
        _ = z * q * w := by group
        _ = w * (z * q) := h
        _ = w * z * q := by group
    exact mul_right_cancel h1
  · intro h
    calc z * q * w = z * (q * w) := by group
      _ = z * (w * q) := by rw [hqw]
      _ = z * w * q := by group
      _ = w * z * q := by rw [h]
      _ = w * (z * q) := by group

theorem exists_x (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    (he : Even (bMin H M)) (hb4 : bMin H M = 4) (h15 : Claim15 α) {α' β α₃ : Geo H M}
    (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α) (h' : α' ∈ nbrs α₃) (d3 : dist α α₃ = 3)
    (dβ : dist β α' = 3) :
    ∃ x ∈ Zv α', x ∉ Qv α ∧ (Zv α ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (Zv α) = 2 ∧
      ∀ h ∈ Wn α ⊓ stab α', h * x * h⁻¹ * x⁻¹ ∈ Zv α := by
  have hs' := hs.sit_crit hA he hc
  have hc' := hs.isCritPair₁_symm hA he hc
  have hα'v := hs.vtype_crit hA he hc
  have hν : α₃ ∈ nbrs α' := nbrs_symm h'
  have hdν : dist α α₃ < bMin H M := by omega
  have hdβ : dist α' β < bMin H M := by rw [CosetGeom.dist_comm]; omega
  have hidx := hs.relIndex_Zv_eq hA he hc
  rcases hs.relIndex_Zv_two_or_four hA h26 he hc hν hdν with ha | ha
  ·
    obtain ⟨x, hx, hxQ, hxH⟩ := h15 hc
    have ha' : (Zv α' ⊓ Qv α).relIndex (Zv α') = 2 := hidx ▸ ha
    obtain ⟨z, hz, hzQ, hzidx, -⟩ := hs'.exists_transposition_of_two hA h26 he hc' hβ hdβ ha'
    refine ⟨x, hx, hxQ, ?_, hxH⟩
    have hq : z⁻¹ * x ∈ Zv α' ⊓ Qv α :=
      inv_mul_mem_of_relIndex_two ha' hz hx (fun h => hzQ h.2) (fun h => hxQ h.2)
    rw [inf_centralizer_eq_of_mul (z := z) (q := z⁻¹ * x) (by group)
      (Qv_le_centralizer_Zv hA α hq.2)]
    exact hzidx
  ·
    have ha' : (Zv α' ⊓ Qv α).relIndex (Zv α') = 4 := hidx ▸ ha
    obtain ⟨D⟩ := hs.exists_dict hA hβ
    have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
    have hY := hs.Yv_eq_comm_comm hA h26 hβv (nbrs_symm hβ)
    have hsup := hs'.Zv_sup_Qv_eq_of_four hA h26 he hc' hβ hdβ ha'
    have hZα' : Zv α' ≤ stab α := hs.Zv_le_stab_crit' hA he hc
    obtain ⟨y, hy⟩ := D.surj (Equiv.swap 0 2)
    have hyC : (y : G) ∈ (stab α ⊓ stab β) ⊓ Subgroup.centralizer (Yv β : Set G) := by
      rw [hY]
      exact (D.mem_centralizer_Y_iff y).mpr (by rw [hy]; exact Subgroup.subset_closure (by simp))
    rw [← hsup, sup_comm] at hyC
    obtain ⟨q, hq, z, hz, hyqz⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (hZα'.trans (le_normalizer_pCoreOf 2 (stab α)))).mp hyC
    have hzα : z ∈ stab α := hZα' hz
    have hqα : q ∈ stab α := pCoreOf_le 2 _ hq
    have hψz : D.ψ ⟨z, hzα⟩ = Equiv.swap 0 2 := by
      have e : y = ⟨q, hqα⟩ * ⟨z, hzα⟩ := Subtype.ext hyqz
      rw [← hy, e, map_mul, (D.ker_iff ⟨q, hqα⟩).mpr hq, one_mul]
    refine ⟨z, hz, fun hzQ => ?_, ?_, ?_⟩
    · have := (D.ker_iff ⟨z, hzα⟩).mpr hzQ
      rw [hψz] at this
      exact absurd this (by decide)
    · rw [D.relIndex_centralizer_eq ⟨z, hzα⟩, hψz]
      exact idx_orth_swap (Or.inl rfl)
    ·
      intro h hh
      have hα₃v : vtype α₃ = true := Sit43.vtype_true_of_adj hα'v hν
      have hsup4 := hs.Zv_sup_Qv_eq_of_four hA h26 he hc hν hdν ha
      have hcomm4 := hs.comm_eq_Yv_of_four hA h26 he hc hν hdν ha
      have hYα : Yv α₃ ≤ Zv α := by
        rw [← hcomm4]
        exact commutator_le_left_of_le_normalizer (hZα'.trans (stab_le_normalizer_Zv hA α))
      have hhQ : h ∈ Qv α := hs.Wn_le_Qv hA (by omega) hh.1
      have hhC : h ∈ Subgroup.centralizer (Yv α₃ : Set G) := fun y hy =>
        Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α hhQ) y (hYα hy)
      have hY3 := hs.Yv_eq_comm_comm hA h26 hα₃v h'
      have hN := normalizer_Y (quot_stab_five hA hα'v) (sylow_stab_inf_left hA hν) hs'.orth
      rw [← hY3] at hN
      have hh3 : h ∈ stab α' ⊓ stab α₃ := by
        rw [← hN]
        exact ⟨hh.2, Subgroup.centralizer_le_normalizer _ hhC⟩
      have hhs : h ∈ (stab α' ⊓ stab α₃) ⊓ Subgroup.centralizer (Yv α₃ : Set G) := ⟨hh3, hhC⟩
      rw [← hsup4, sup_comm] at hhs
      have hZα : Zv α ≤ stab α' := hs.Zv_le_stab_crit hA hc
      obtain ⟨q', hq', z', hz', hhqz⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        (hZα.trans (le_normalizer_pCoreOf 2 (stab α')))).mp hhs
      have hzz : z' * z * z'⁻¹ ∈ Zv α' :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α' (hZα hz')) z).mp hz
      have hq'c := conj_eq_of_mem_centralizer' (Qv_le_centralizer_Zv hA α' hq') hzz
      have e : h * z * h⁻¹ * z⁻¹ = ⁅z', z⁆ := by
        rw [hhqz, commutatorElement_def]
        calc q' * z' * z * (q' * z')⁻¹ * z⁻¹ = (q' * (z' * z * z'⁻¹) * q'⁻¹) * z⁻¹ := by group
          _ = (z' * z * z'⁻¹) * z⁻¹ := by rw [hq'c]
          _ = z' * z * z'⁻¹ * z⁻¹ := by group
      rw [e]
      exact commutator_le_left_of_le_normalizer (hZα'.trans (stab_le_normalizer_Zv hA α))
        (Subgroup.commutator_mem_commutator hz' hz)

theorem exists_delta (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {β : Geo H M} (hβ : β ∈ nbrs α) {x : G} (hxα : x ∈ stab α)
    (hxQ : x ∈ Qst β)
    (hxT : (Zv α ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (Zv α) = 2) :
    ∃ δ ∈ nbrs α, Yv δ ⊓ Yv β = ⊥ ∧ x ∉ Mab α δ ∧
      stab α ⊓ stab δ ⊓ (stab α ⊓ stab β ⊓ Subgroup.centralizer (Yv β : Set G)) ≤ Qv α := by
  obtain ⟨D⟩ := hs.exists_dict hA hβ
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hY := hs.Yv_eq_comm_comm hA h26 hβv (nbrs_symm hβ)
  have hY0 : Yv β = (fixW orth S5That).map D.φ := by
    rw [hY, D.comm_comm_eq, commIter_two_eq_fixW_That]
  set τ := D.ψ ⟨x, hxα⟩ with hτ
  have hτT : τ ∈ S5That := by
    refine (D.mem_centralizer_Y_iff ⟨x, hxα⟩).mp ⟨⟨hxα, pCoreOf_le 2 _ hxQ.1⟩, ?_⟩
    rw [← hY]; exact hxQ.2
  have hτ2 : idx orth τ = 2 := by rw [hτ, ← D.relIndex_centralizer_eq]; exact hxT
  have hτs := swap_of_That_idx τ hτT hτ2
  obtain ⟨σ, hσ, hmove⟩ : ∃ σ : Equiv.Perm (Fin 5), (σ = sgA ∨ σ = sgB) ∧ (σ⁻¹ * τ * σ) 4 ≠ 4 := by
    rcases hτs with h | h
    · exact ⟨sgA, Or.inl rfl, by rw [h]; exact sgA_moves⟩
    · exact ⟨sgB, Or.inr rfl, by rw [h]; exact sgB_moves⟩
  obtain ⟨g, hg⟩ := D.surj σ
  set g' : ↥(H ⊔ M) := ⟨(g : G), stab_le α g.2⟩ with hg'
  have hg'α : (g' : G) ∈ stab α := g.2
  refine ⟨g' • β, smul_mem_nbrs_of_mem_stab g' hg'α hβ, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    rw [Yv_smul, mem_conjSub, hY0] at hz1
    rw [hY0] at hz2
    obtain ⟨y', hy', hy'e⟩ := hz1
    obtain ⟨y, hy, rfl⟩ := hz2
    have e1 : D.φ (orth.act σ y') = D.φ y := by
      rw [← hg, D.act_eq, hy'e]
      show (g : G) * ((g : G)⁻¹ * D.φ y * g) * (g : G)⁻¹ = D.φ y
      group
    have e2 := D.inj e1
    have h1 : y' = 1 := inf_Y_eq σ hσ y' hy' (e2 ▸ hy)
    rw [Subgroup.mem_bot, ← e2, h1, map_one, map_one]
  ·
    rw [Mab_smul g' hg'α β, mem_conjSub]
    intro hM
    have hgx : (g' : G)⁻¹ * x * g' ∈ stab α :=
      (stab α).mul_mem ((stab α).mul_mem ((stab α).inv_mem hg'α) hxα) hg'α
    have h1 := (Sit43.mem_Mab_iff D ⟨_, hgx⟩).mp hM
    have e : (⟨(g' : G)⁻¹ * x * g', hgx⟩ : ↥(stab α)) = g⁻¹ * ⟨x, hxα⟩ * g := rfl
    rw [e, map_mul, map_mul, map_inv, hg, ← hτ] at h1
    exact hmove h1
  ·
    intro k hk
    obtain ⟨hk1, hkC⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨hkα, hkδ⟩ := Subgroup.mem_inf.mp hk1
    rw [stab_smul, mem_conjSub] at hkδ
    have hgk : (g' : G)⁻¹ * k * g' ∈ stab α :=
      (stab α).mul_mem ((stab α).mul_mem ((stab α).inv_mem hg'α) hkα) hg'α
    have h1 : D.ψ ⟨_, hgk⟩ ∈ S5Syl := (D.mem_S_iff ⟨_, hgk⟩).mp ⟨hgk, hkδ⟩
    have e : (⟨(g' : G)⁻¹ * k * g', hgk⟩ : ↥(stab α)) = g⁻¹ * ⟨k, hkα⟩ * g := rfl
    rw [e, map_mul, map_mul, map_inv, hg] at h1
    have hkT : D.ψ ⟨k, hkα⟩ ∈ S5That := by
      refine (D.mem_centralizer_Y_iff ⟨k, hkα⟩).mp ⟨hkC.1, ?_⟩
      rw [← hY]; exact hkC.2
    have h2 := That_inf_conj σ hσ hkT h1
    exact (D.ker_iff ⟨k, hkα⟩).mp h2

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
