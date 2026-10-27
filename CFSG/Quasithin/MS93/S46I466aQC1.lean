module

public import CFSG.Quasithin.MS93.S46I466aQSec
public import CFSG.Quasithin.MS93.S46I466aQC2
public import CFSG.Quasithin.MS93.S4AFMain

public section

namespace CFSG.Quasithin.MS93.S46.QMix

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I466b
open scoped commutatorElement

section Grp

variable {𝔾 : Type*} [Group 𝔾]

theorem exists_omegaZ {Q P K : Subgroup 𝔾} (hPQ : P ≤ Q)
    (hQP : Q ≤ Subgroup.normalizer (P : Set 𝔾)) (hKP : K ≤ Subgroup.normalizer (P : Set 𝔾))
    (hKQ : K ≤ Subgroup.normalizer (Q : Set 𝔾)) :
    ∃ P' : Subgroup 𝔾, P ≤ P' ∧ P' ≤ Q ∧ (∀ q ∈ P', q ^ 2 ∈ P) ∧
      (∀ q ∈ P', ∀ r ∈ Q, ⁅q, r⁆ ∈ P) ∧
      (∀ q ∈ Q, q ^ 2 ∈ P → (∀ r ∈ Q, ⁅q, r⁆ ∈ P) → q ∈ P') ∧
      K ≤ Subgroup.normalizer (P' : Set 𝔾) := by
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set 𝔾), ∀ p ∈ P, g * p * g⁻¹ ∈ P :=
    fun g hg p hp => (Subgroup.mem_normalizer_iff.mp hg p).mp hp
  have hinv : ∀ q ∈ Q, (∀ r ∈ Q, ⁅q, r⁆ ∈ P) → ∀ r ∈ Q, ⁅q⁻¹, r⁆ ∈ P := by
    intro q hq hqc r hr
    have e : ⁅q⁻¹, r⁆ = q⁻¹ * ⁅q, r⁆⁻¹ * q⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hconj _ (hQP (Q.inv_mem hq)) _ (P.inv_mem (hqc r hr))
  let P' : Subgroup 𝔾 :=
    { carrier := {q | q ∈ Q ∧ q ^ 2 ∈ P ∧ ∀ r ∈ Q, ⁅q, r⁆ ∈ P}
      one_mem' := ⟨Q.one_mem, by simp, fun r _ => by simp⟩
      mul_mem' := by
        rintro q₁ q₂ ⟨hq₁, h₁2, h₁c⟩ ⟨hq₂, h₂2, h₂c⟩
        refine ⟨Q.mul_mem hq₁ hq₂, ?_, fun r hr => ?_⟩
        · have e : (q₁ * q₂) ^ 2 = q₁ ^ 2 * ⁅q₁⁻¹, q₂⁆ * q₂ ^ 2 := by
            simp only [commutatorElement_def, sq]; group
          rw [e]
          exact P.mul_mem (P.mul_mem h₁2 (hinv q₁ hq₁ h₁c q₂ hq₂)) h₂2
        · have e : ⁅q₁ * q₂, r⁆ = q₁ * ⁅q₂, r⁆ * q₁⁻¹ * ⁅q₁, r⁆ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact P.mul_mem (hconj _ (hQP hq₁) _ (h₂c r hr)) (h₁c r hr)
      inv_mem' := by
        rintro q ⟨hq, h2, hc⟩
        refine ⟨Q.inv_mem hq, ?_, hinv q hq hc⟩
        rw [inv_pow]
        exact P.inv_mem h2 }
  refine ⟨P', fun p hp => ⟨hPQ hp, ?_, fun r hr => ?_⟩, fun q hq => hq.1, fun q hq => hq.2.1,
    fun q hq => hq.2.2, fun q hq h2 hc => ⟨hq, h2, hc⟩, ?_⟩
  · rw [sq]
    exact P.mul_mem hp hp
  · have e : ⁅p, r⁆ = p * (r * p⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem hp (hconj _ (hQP hr) _ (P.inv_mem hp))
  · refine le_normalizer_of_map_conj_le fun k hk => ?_
    rintro _ ⟨q, ⟨hq, h2, hc⟩, rfl⟩
    have hkq : k * q * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ hk) q).mp hq
    refine ⟨hkq, ?_, fun r hr => ?_⟩
    · have e : (k * q * k⁻¹) ^ 2 = k * q ^ 2 * k⁻¹ := by simp only [sq]; group
      show (k * q * k⁻¹) ^ 2 ∈ P
      rw [e]
      exact hconj _ (hKP hk) _ h2
    · have hr' : k⁻¹ * r * k⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hKQ (K.inv_mem hk)) r).mp hr
      have e : ⁅k * q * k⁻¹, r⁆ = k * ⁅q, k⁻¹ * r * k⁻¹⁻¹⁆ * k⁻¹ := by
        simp only [commutatorElement_def]; group
      show ⁅k * q * k⁻¹, r⁆ ∈ P
      rw [e]
      exact hconj _ (hKP hk) _ (hc _ hr')

end Grp

section C1

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hb4 : critDist (puAmalgam h.le) = 4)
  (hS : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
    (Qv _ α).relIndex (Qv _ β) < Fintype.card F ^ 2)
  (hVQ : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x)
include h hφ hb4 hS hVQ

theorem commutator_qv_ltil_le_vv (h43 : S43) (hmin : PUMin M T L)
    {y y' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) y y') :
    ⁅Qv (puAmalgam h.le) y, Ltil h.le L y⁆ ≤ Vv _ y := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hy : IsMVtx _ y := hc.1
  set w := geo (puAmalgam h.le) y y' 2 with hwdef
  set s := geo (puAmalgam h.le) y y' 1 with hsdef
  have hw : IsMVtx _ w := isMVtx_geo_two' hb4 hc
  have hys : (puAmalgam h.le).treeGraph.Adj y s := adj_geo_one_of_isCritical _ hb0 hc
  have hsw : (puAmalgam h.le).treeGraph.Adj s w := adj_geo_crit hb4 hc (i := 1) (by norm_num)
  have hyw : (puAmalgam h.le).treeGraph.dist y w = 2 := dist_geo_crit hb4 hc (by norm_num)
  have hwy : (puAmalgam h.le).treeGraph.dist w y = 2 := by rw [tdist_comm]; exact hyw
  have hwy' : (puAmalgam h.le).treeGraph.dist w y' = 2 :=
    dist_geo_crit_right hb4 hc (i := 2) (by norm_num)
  have hc' := ms22_iii _ h20 hb0 hC hc
  obtain ⟨t, htZ, htQ⟩ := Set.not_subset.mp hc'.2.2
  have hZs : ZM (puAmalgam h.le) y' ≤ stab _ y := zm_le_stab_of_isCritical _ h20 hb0 hc
  have ht : t ∈ stab (puAmalgam h.le) y := hZs htZ
  have ht2 : t ^ 2 ∈ Qv (puAmalgam h.le) y := by
    rw [sq_eq_one_of_mem_zv h hfull (show t ∈ Zv (puAmalgam h.le) y' by
      rw [zv_of_isMVtx _ hc'.1]; exact htZ)]
    exact one_mem _
  have hQys : Qv (puAmalgam h.le) y ≤ stab _ y := qv_le_stab _ y
  have hQws : Qv (puAmalgam h.le) w ≤ stab _ y :=
    (qv_le_qv _ h20 hw hsw.symm).trans (qv_le_stab_of_adj _ hys.symm)
  have hVn := stab_le_normalizer_vv h y
  set K₀ := Qv (puAmalgam h.le) y ⊓ (Vv _ y ⊔ Qv _ w) with hK₀
  have hK₀t : ⁅K₀, ZM (puAmalgam h.le) y'⁆ ≤ Vv _ y := by
    refine (Subgroup.commutator_mono inf_le_right le_rfl).trans ?_
    refine commutator_sup_le_of Subgroup.le_normalizer (hQws.trans hVn) ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hVn)
    · have hZV : ZM (puAmalgam h.le) y' ≤ Vv _ w := by
        have := zv_le_vv_of_dist h (le_of_eq hwy')
        rwa [zv_of_isMVtx _ hc'.1] at this
      have hZw : ZM (puAmalgam h.le) w ≤ Vv _ y := by
        have := zv_le_vv_of_dist h (le_of_eq hyw)
        rwa [zv_of_isMVtx _ hw] at this
      calc ⁅Qv (puAmalgam h.le) w, ZM _ y'⁆ ≤ ⁅Qv (puAmalgam h.le) w, Vv _ w⁆ :=
            Subgroup.commutator_mono le_rfl hZV
        _ = ⁅Vv (puAmalgam h.le) w, Qv _ w⁆ := Subgroup.commutator_comm _ _
        _ ≤ ZM _ w := hVQ w hw
        _ ≤ Vv _ y := hZw
  have hK₀idx : K₀.relIndex (Qv (puAmalgam h.le) y) < Fintype.card F := by
    have hVyw : ¬ Vv (puAmalgam h.le) y ≤ Qv _ w := by
      have := h43 G M T L h hmin hb hfull y y' hc
      rwa [geo_rev_two hb4 hc] at this
    obtain ⟨ν, hcν, hgν⟩ : ∃ ν, IsCritical (puAmalgam h.le) w ν ∧ geo _ w ν 2 = y := by
      by_contra hno
      apply hVyw
      refine (vv_le_critGen_sup h20 hC hb4 hy hwy).trans (sup_le ?_ le_rfl)
      exact iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim
    obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hw
    have hZνs : ZM (puAmalgam h.le) ν ≤ stab _ w := zm_le_stab_of_isCritical _ h20 hb0 hcν
    obtain ⟨hE, -⟩ := card_natImage_zm_of_lt h hφ hC hcν
      (hS w _ hw (adj_geo_one_of_isCritical _ hb0 hcν)) hψ
    rw [card_natImage_eq_relIndex h hφ hw hψ hZνs] at hE
    have hZνV : ZM (puAmalgam h.le) ν ≤ Vv _ y := by
      have hd : (puAmalgam h.le).treeGraph.dist y ν = 2 := by
        rw [← hgν]
        exact dist_geo_crit_right hb4 hcν (by norm_num)
      have := zv_le_vv_of_dist h (le_of_eq hd)
      rwa [zv_of_isMVtx _ (ms22_iii _ h20 hb0 hC hcν).1] at this
    have hVs : Vv (puAmalgam h.le) y ⊔ Qv _ w ≤ Qv _ s :=
      sup_le ((vv_le_qv h hb hy).trans (qv_le_qv _ h20 hy hys)) (qv_le_qv _ h20 hw hsw.symm)
    have : Finite ↥(Qv (puAmalgam h.le) s) := finite_of_le_stab h hy (qv_le_stab_of_adj _ hys.symm)
    have : Finite ↥(Vv (puAmalgam h.le) y ⊔ Qv _ w) :=
      Finite.of_injective _ (Subgroup.inclusion_injective hVs)
    have htow := Subgroup.relIndex_mul_relIndex (Qv (puAmalgam h.le) w) (Vv _ y ⊔ Qv _ w)
      (Qv _ s) le_sup_right hVs
    have h1 : Fintype.card F ≤ (Qv (puAmalgam h.le) w).relIndex (Vv _ y ⊔ Qv _ w) := by
      rw [← hE]
      exact Subgroup.relIndex_le_of_le_right (hZνV.trans le_sup_left)
        relIndex_ne_zero_of_finite'
    have h2 := hS w s hw hsw.symm
    have h3 : (Vv (puAmalgam h.le) y ⊔ Qv _ w).relIndex (Qv _ s) < Fintype.card F := by
      by_contra hge
      push Not at hge
      have := Nat.mul_le_mul h1 hge
      rw [htow, ← sq] at this
      omega
    calc K₀.relIndex (Qv (puAmalgam h.le) y)
        = (Vv (puAmalgam h.le) y ⊔ Qv _ w).relIndex (Qv _ y) := Subgroup.inf_relIndex_left _ _
      _ ≤ (Vv (puAmalgam h.le) y ⊔ Qv _ w).relIndex (Qv _ s) :=
          Subgroup.relIndex_le_of_le_right (qv_le_qv _ h20 hy hys) relIndex_ne_zero_of_finite'
      _ < Fintype.card F := h3
  have hQp : IsPGroup 2 ↥(Qv (puAmalgam h.le) y) := isPGroup_qv_of_isMVtx h hy
  have : Finite ↥(Qv (puAmalgam h.le) y) := finite_of_le_stab h hy hQys
  have hLs := ltil_le_stab h y
  have hperf := ltil_perfect h hy
  suffices key : ∀ n : ℕ, ∀ P : Subgroup (puAmalgam h.le).Universal,
      P.relIndex (Qv (puAmalgam h.le) y) = n → Vv (puAmalgam h.le) y ≤ P →
        P ≤ Qv (puAmalgam h.le) y →
        stab (puAmalgam h.le) y ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal) →
        ⁅P, Ltil h.le L y⁆ ≤ Vv _ y → ⁅Qv (puAmalgam h.le) y, Ltil h.le L y⁆ ≤ Vv _ y by
    exact key _ _ rfl le_rfl (vv_le_qv h hb hy) hVn
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hVn))
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hVP hPQ hPn hPL
  by_cases hPeq : P = Qv (puAmalgam h.le) y
  · rw [← hPeq]
    exact hPL
  have hQPn : Qv (puAmalgam h.le) y ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal) :=
    hQys.trans hPn
  obtain ⟨P', hPP', hP'Q, hP'2, hP'c, hP'mem, hP'n⟩ :=
    exists_omegaZ (K := stab (puAmalgam h.le) y) hPQ hQPn hPn (stab_le_normalizer_qv _ y)
  have hne : P' ≠ P := by
    obtain ⟨q, hqQ, hqP, hq2, hqc⟩ := exists_mem_sq_mem_commutator_mem hQp hPQ hQPn hPeq
    intro he
    exact hqP (he ▸ hP'mem q hqQ hq2 hqc)
  have hP's : P' ≤ stab (puAmalgam h.le) y := hP'Q.trans hQys
  have : Finite ↥P' := finite_of_le_stab h hy hP's
  have hCt : ∀ c ∈ (P' ⊓ K₀) ⊔ P, ⁅c, t⁆ ∈ P := by
    have hle : ⁅(P' ⊓ K₀) ⊔ P, ZM (puAmalgam h.le) y'⁆ ≤ P :=
      commutator_sup_le_of ((inf_le_left.trans hP'Q).trans hQPn) Subgroup.le_normalizer
        ((Subgroup.commutator_mono inf_le_right le_rfl).trans (hK₀t.trans hVP))
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hPn))
    exact fun c hc => hle (Subgroup.commutator_mem_commutator hc htZ)
  have hidx : ((P' ⊓ K₀) ⊔ P).relIndex P' < Fintype.card F := by
    calc ((P' ⊓ K₀) ⊔ P).relIndex P' ≤ (P' ⊓ K₀).relIndex P' :=
          Subgroup.relIndex_le_of_le_left le_sup_left relIndex_ne_zero_of_finite'
      _ = K₀.relIndex P' := Subgroup.inf_relIndex_left _ _
      _ ≤ K₀.relIndex (Qv (puAmalgam h.le) y) :=
          Subgroup.relIndex_le_of_le_right hP'Q relIndex_ne_zero_of_finite'
      _ < Fintype.card F := hK₀idx
  have hsec := commutator_stab_le_of_section h hφ hy hP's hP'n hPn le_sup_right
    (sup_le inf_le_left hPP') hP'2
    (by rw [Subgroup.commutator_le]; intro a ha b hb; exact hP'c a ha b (hP'Q hb))
    (by rw [Subgroup.commutator_le]; intro a ha r hr; exact hP'c a ha r hr)
    ht htQ ht2 hCt hidx
  have hP'L : ⁅P', Ltil h.le L y⁆ ≤ Vv _ y :=
    commutator_le_of_perfect hperf ((Subgroup.commutator_mono le_rfl hLs).trans hsec) hPL
      (hLs.trans hVn) (hP's.trans hVn)
  have hlt : P'.relIndex (Qv (puAmalgam h.le) y) < n := by
    have htow := Subgroup.relIndex_mul_relIndex P P' (Qv (puAmalgam h.le) y) hPP' hP'Q
    have h1 : P.relIndex P' ≠ 1 := fun h1 =>
      hne (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hPP')
    have h0 : P.relIndex P' ≠ 0 := relIndex_ne_zero_of_finite'
    have h0' : P'.relIndex (Qv (puAmalgam h.le) y) ≠ 0 := relIndex_ne_zero_of_finite'
    have h2 : 2 ≤ P.relIndex P' := by omega
    rw [← hn, ← htow]
    calc P'.relIndex (Qv (puAmalgam h.le) y) < 2 * P'.relIndex (Qv _ y) := by omega
      _ ≤ P.relIndex P' * P'.relIndex (Qv _ y) := Nat.mul_le_mul_right _ h2
  exact ih _ hlt P' rfl (hVP.trans hPP') hP'Q hP'n hP'L

end C1

end CFSG.Quasithin.MS93.S46.QMix
