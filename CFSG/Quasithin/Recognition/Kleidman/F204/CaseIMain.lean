module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIBase
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

section Generic

omit [Finite G] in
private theorem mem_normalizer_of_conj_mem {K : Subgroup G} {g : G}
    (h1 : ∀ y ∈ K, g * y * g⁻¹ ∈ K) (h2 : ∀ y ∈ K, g⁻¹ * y * g⁻¹⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

omit [Finite G] in
private theorem mem_normalizer_of_commute {K : Subgroup G} {g : G}
    (h : ∀ y ∈ K, g * y = y * g) : g ∈ Subgroup.normalizer (K : Set G) := by
  refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
  · rw [h y hy, mul_inv_cancel_right]; exact hy
  · have e : g⁻¹ * y = y * g⁻¹ := by
      calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * y) * g⁻¹ := by rw [h y hy]
        _ = y * g⁻¹ := by group
    rw [e, inv_inv, inv_mul_cancel_right]; exact hy

omit [Finite G] in
private theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  mem_normalizer_of_conjSub_eq (by
    rw [conjSub_sup, F7.conjSub_eq_of_mem_normalizer hA, F7.conjSub_eq_of_mem_normalizer hB])

end Generic

variable {L1 L2 S D X : Subgroup G}

section T1

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
include F hT1

theorem caseI_step1 (hN : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → NatA x)
    {α β α' ε ε2 ε3 : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α')
    (hb : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S)) (hα : vtype α = true) (hα' : vtype α' = true)
    (hfα' : ZFaithful α') (hε : ε ∈ nbrs α') (hε2 : ε2 ∈ nbrs ε) (hε3 : ε3 ∈ nbrs ε2)
    (hdε : dist α ε + 1 = bMin (P1 L1 L2 S) (P2 L1 L2 S))
    (hdε2 : dist α ε2 + 2 = bMin (P1 L1 L2 S) (P2 L1 L2 S))
    (hdε3 : dist α ε3 + 3 = bMin (P1 L1 L2 S) (P2 L1 L2 S))
    {l : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hl : l ∈ nbrs α) (hlβ : l ≠ β) : Vn l ≤ Qv ε2 := by
  have hA := Amal.of_frame F
  have hgen := hA.amalgam.gen
  have hβα : β ∈ nbrs α := hc.adj
  have hαl : α ∈ nbrs l := (show (graph _ _ _).Adj α l from hl).symm
  have hεε2 : ε ∈ nbrs ε2 := (show (graph _ _ _).Adj ε ε2 from hε2).symm
  have hα'ε : α' ∈ nbrs ε := (show (graph _ _ _).Adj α' ε from hε).symm
  have hd1 : ∀ {u v : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, v ∈ nbrs u → dist u v = 1 :=
    fun h => dist_eq_one_iff_adj.mpr h
  have hvt : ∀ {u v : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, v ∈ nbrs u → vtype v = !vtype u := by
    intro u v h
    have := vtype_ne_of_adj (show (graph _ _ _).Adj u v from h)
    cases h1 : vtype u <;> cases h2 : vtype v <;> simp_all
  have hεf : vtype ε = false := by rw [hvt hε, hα']; rfl
  have hε2t : vtype ε2 = true := by rw [hvt hε2, hεf]; rfl
  have hlf : vtype l = false := by rw [hvt hl, hα]; rfl
  have hZαε : Zv α ≤ Qv ε := by
    apply Zv_le_Qv_of_dist_lt
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) α
    omega
  have hZα'β : Zv α' ≤ Qv β := by
    apply Zv_le_Qv_of_dist_lt
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) α'
    have := hc.dist_eq'
    rw [CosetGeom.dist_comm]
    omega
  have heq1 : Zv β = Zv ε := Zv_eq_Zv_of_not_le F hT1 hα hα' (hN α hα) (hN α' hα') hβα hε
    hZαε hZα'β hc.not_le
  refine iSup₂_le fun μ hμ => ?_
  by_contra hnot
  have hμt : vtype μ = true := by rw [hvt hμ, hlf]; rfl
  have hlμ : l ∈ nbrs μ := (show (graph _ _ _).Adj l μ from hμ).symm
  have hZμε3 : Zv μ ≤ Qv ε3 := by
    apply Zv_le_Qv_of_dist_lt
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) μ
    have t1 := dist_triangle hgen μ l ε3
    have t2 := dist_triangle hgen l α ε3
    have e1 := hd1 hlμ
    have e2 := hd1 hαl
    omega
  have hZε2l : Zv ε2 ≤ Qv l := by
    apply Zv_le_Qv_of_dist_lt
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) ε2
    have t1 := dist_triangle hgen ε2 α l
    have e2 := hd1 hl
    rw [CosetGeom.dist_comm ε2 α] at t1
    omega
  have heq2 : Zv l = Zv ε3 := Zv_eq_Zv_of_not_le F hT1 hμt hε2t (hN μ hμt) (hN ε2 hε2t) hlμ hε3
    hZμε3 hZε2l hnot
  have hsup := Zv_sup_Zv_eq F hT1 hα (hN α hα) hβα hl (Ne.symm hlβ)
  have hle1 : Zv ε ≤ Zv ε2 := by
    rw [Zv_eq_inf_centralizer F hT1 hε2t hεε2]; exact inf_le_left
  have hle3 : Zv ε3 ≤ Zv ε2 := by
    rw [Zv_eq_inf_centralizer F hT1 hε2t hε3]; exact inf_le_left
  have hle : Zv α ≤ Zv ε2 := by
    rw [← hsup, heq1, heq2]; exact sup_le hle1 hle3
  have hZα'ε2 : Zv α' ≤ Qv ε2 := by
    apply Zv_le_Qv_of_dist_lt
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) α'
    have t1 := dist_triangle hgen α' ε ε2
    have e1 := hd1 hε
    have e2 := hd1 hε2
    omega
  have hcen : Zv α ≤ Subgroup.centralizer (Zv α' : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv ε2 (hle ha)).2 z (hZα'ε2 hz)
  have hZαst : Zv α ≤ stab α' := hZαε.trans (hA.Qv_le_stab_of_mem_nbrs hα'ε)
  exact hc.not_le (hA.le_Qv_of_ZFaithful hfα' hZαst
    (F7.isPGroup_of_isElemAbelian (hA.isElemAbelian_Zv α)) hcen)

theorem caseI_false (hN : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → NatA x)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hI : ¬ Zv α' ≤ Qv α)
    (hidx : (Zv α ⊓ Qv α').relIndex (Zv α) = 4) (hb : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S)) :
    False := by
  have hA := Amal.of_frame F
  have hgen := hA.amalgam.gen
  obtain ⟨hbα', -, hfα'⟩ := hA.caseI (frame_dichotomy F) hc hI
  have hvt : ∀ {u v : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, v ∈ nbrs u → vtype v = !vtype u := by
    intro u v h
    have := vtype_ne_of_adj (show (graph _ _ _).Adj u v from h)
    cases h1 : vtype u <;> cases h2 : vtype v <;> simp_all
  have hα : vtype α = true := by
    cases h : vtype α
    · exact absurd ((hT1 α).mpr h) (hA.not_ZCentral_of_bAt hc.bAt_eq)
    · rfl
  have hα' : vtype α' = true := by
    cases h : vtype α'
    · exact absurd ((hT1 α').mpr h) (hA.not_ZCentral_of_bAt hbα')
    · rfl
  have hβα : β ∈ nbrs α := hc.adj
  have hd := hc.dist_eq
  obtain ⟨ε, hε, hdε⟩ := exists_adj_dist_eq hgen (α := α) (δ := α')
    (d := bMin (P1 L1 L2 S) (P2 L1 L2 S) - 1) (by omega)
  obtain ⟨ε2, hε2, hdε2⟩ := exists_adj_dist_eq hgen (α := α) (δ := ε)
    (d := bMin (P1 L1 L2 S) (P2 L1 L2 S) - 2) (by omega)
  obtain ⟨ε3, hε3, hdε3⟩ := exists_adj_dist_eq hgen (α := α) (δ := ε2)
    (d := bMin (P1 L1 L2 S) (P2 L1 L2 S) - 3) (by omega)
  have hεn : ε ∈ nbrs α' := hε
  have hε2n : ε2 ∈ nbrs ε := hε2
  have hε3n : ε3 ∈ nbrs ε2 := hε3
  have hεf : vtype ε = false := by rw [hvt hεn, hα']; rfl
  have hα'ε : α' ∈ nbrs ε := (show (graph _ _ _).Adj α' ε from hε).symm
  have hεε2 : ε ∈ nbrs ε2 := (show (graph _ _ _).Adj ε ε2 from hε2).symm
  have hcard := hA.card_nbrs α
  have : Finite ↥(nbrs α) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial ↥(nbrs α) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨⟨l, hl⟩, hne⟩ := exists_ne (⟨β, hβα⟩ : ↥(nbrs α))
  have hlβ : l ≠ β := fun h => hne (Subtype.ext h)
  have hlf : vtype l = false := by rw [hvt hl, hα]; rfl
  have hαl : α ∈ nbrs l := (show (graph _ _ _).Adj α l from hl).symm
  have hU1 := caseI_step1 F hT1 hN hc hb hα hα' hfα' hεn hε2n hε3n (by omega) (by omega)
    (by omega) hl hlβ
  have hU2 : IsElemAbelian 2 (Vn l) := hA.isElemAbelian_Vn hb l
  have hUε : Vn l ≤ stab ε := hU1.trans (hA.Qv_le_stab_of_mem_nbrs hεε2)
  have hidxε : (Vn l ⊓ Qv ε).relIndex (Vn l) ≤ 2 := relIndex_inf_Qv_le_two F hεf hUε hU2
  have hZαε : Zv α ≤ Qv ε := by
    apply Zv_le_Qv_of_dist_lt
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) α
    omega
  have hZn : Zv α ≤ Subgroup.normalizer (Qv α' : Set G) :=
    hZαε.trans ((hA.Qv_le_stab_of_mem_nbrs hα'ε).trans (le_normalizer_pCoreOf 2 (stab α')))
  have hQε : Qv ε ≤ Zv α ⊔ Qv α' := by
    have h1 := F1.relIndex_sup_eq_of_le_normalizer hZn
    have h0 : (Qv α').relIndex (Zv α) = 4 := by rw [← Subgroup.inf_relIndex_left]; exact hidx
    rw [h0] at h1
    have h2 := relIndex_Qv_sup_Qv F hα' hεn
    have hle : Zv α ⊔ Qv α' ≤ Qv ε ⊔ Qv α' := sup_le_sup_right hZαε _
    have hmul := Subgroup.relIndex_mul_relIndex (Qv α') (Zv α ⊔ Qv α') (Qv ε ⊔ Qv α')
      le_sup_right hle
    rw [h1, h2] at hmul
    have hk : (Zv α ⊔ Qv α').relIndex (Qv ε ⊔ Qv α') = 1 := by omega
    exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp hk)
  set M : Subgroup G := Zv α ⊔ (Vn l ⊓ Qv α') with hM
  have hZαU : Zv α ≤ Vn l := hA.Zv_le_Vn hαl
  have hMU : M ≤ Vn l := sup_le hZαU inf_le_left
  have hUQM : Vn l ⊓ Qv ε ≤ M := by
    intro u hu
    obtain ⟨huU, huε⟩ := Subgroup.mem_inf.mp hu
    have hu' : u ∈ Qv α' ⊔ Zv α := by rw [sup_comm]; exact hQε huε
    obtain ⟨a, ha, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZn).mp hu'
    have haU : a ∈ Vn l := by
      have := Subgroup.mul_mem _ huU (Subgroup.inv_mem _ (hZαU hz))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _ (le_sup_right (a := Zv α) (Subgroup.mem_inf.mpr ⟨haU, ha⟩))
      (le_sup_left (b := Vn l ⊓ Qv α') hz)
  have hMidx : M.relIndex (Vn l) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hUQM Subgroup.index_ne_zero_of_finite).trans hidxε
  have hZα'β : Zv α' ≤ Qv β := by
    apply Zv_le_Qv_of_dist_lt
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) α'
    have := hc.dist_eq'
    rw [CosetGeom.dist_comm]
    omega
  have hαβ : α ∈ nbrs β := (show (graph _ _ _).Adj α β from hc.adj).symm
  have hZα'α : Zv α' ≤ stab α := hZα'β.trans (hA.Qv_le_stab_of_mem_nbrs hαβ)
  have hnA : ∀ z ∈ Zv α', z ∈ Subgroup.normalizer (M : Set G) := by
    intro z hz
    refine mem_normalizer_sup (hA.stab_le_normalizer_Zv α (hZα'α hz))
      (mem_normalizer_of_commute fun y hy => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α' hz).2 y
      (Subgroup.mem_inf.mp hy).2).symm
  have hZlα : Zv l ≤ Zv α := by
    rw [Zv_eq_inf_centralizer F hT1 hα hl]; exact inf_le_left
  have hconjM : ∀ q ∈ Qv l, ∀ m ∈ M, q * m * q⁻¹ ∈ M := by
    intro q hq m hm
    have hc' := conj_mul_mem_Zv_of_mem_Vn F hT1 hN hb hlf hq (hMU hm)
    have e : q * m * q⁻¹ = m * (m⁻¹ * (q * m * q⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem _ hm (le_sup_left (b := Vn l ⊓ Qv α') (hZlα hc'))
  have hnB : ∀ q ∈ Qv l, q ∈ Subgroup.normalizer (M : Set G) := fun q hq =>
    mem_normalizer_of_conj_mem (hconjM q hq) (hconjM q⁻¹ (Subgroup.inv_mem _ hq))
  obtain ⟨z, hz, hzQ⟩ : ∃ z ∈ Zv α', z ∉ Qv α := by
    by_contra h; push Not at h; exact hI fun z hz => h z hz
  have hzα : z ∈ stab α := hZα'α hz
  have hzβ : z ∈ stab β := (hZα'β.trans (pCoreOf_le 2 _)) hz
  have hz2 : z ^ 2 ^ 1 = 1 := by rw [pow_one]; exact (hA.isElemAbelian_Zv α').2 z hz
  have hfaith := not_stab_le_centralizer_Zv F hT1 hα
  have hzl : z ∉ stab l := by
    intro hzl
    have h1 := inf_centralizer_two_eq F hT1 hα (hN α hα) hβα hfaith hzα hzβ hz2 hzQ
    have h2 := inf_centralizer_two_eq F hT1 hα (hN α hα) hl hfaith hzα hzl hz2 hzQ
    have hbot := Zv_inf_Zv_eq_bot F hT1 hα (hN α hα) hβα hl (Ne.symm hlβ)
    rw [← h1, ← h2, inf_idem] at hbot
    rw [h1] at hbot
    exact hA.Zv_ne_bot β hbot
  set zg : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨z, (mem_stab.mp hzα).1⟩ with hzg
  have hzgα : zg • α = α := smul_eq_of_mem_stab (g := zg) hzα
  have hzl' : zg • l ∈ nbrs α := by
    have := (smul_adj zg).mpr (show (graph _ _ _).Adj α l from hl)
    rwa [hzgα] at this
  have hzl'' : zg • l ≠ l := fun h => hzl (mem_stab_of_smul_eq (g := zg) h)
  have hMle : ∀ l' ∈ nbrs α, M ≤ Vn l' := by
    intro l' hl'
    by_cases hl'l : l' = l
    · rw [hl'l]; exact hMU
    obtain ⟨q, hqQ, hql⟩ := exists_Qv_smul_nbr F hα hl hzl' hl' hzl'' hl'l
    have hgl : (q * zg) • l = l' := by rw [mul_smul, hql]
    have hgn : ((q * zg : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.mul_mem _ (hnB _ hqQ) (hnA z hz)
    rw [← hgl, Vn_smul, ← F7.conjSub_eq_of_mem_normalizer hgn]
    exact conjSub_mono _ hMU
  set K : Subgroup G := ⨅ (l' : Geo (P1 L1 L2 S) (P2 L1 L2 S)) (_ : l' ∈ nbrs α), Vn l' with hK
  have hmemK : ∀ y, y ∈ K ↔ ∀ l' ∈ nbrs α, y ∈ Vn l' := by
    intro y; simp [hK, Subgroup.mem_iInf]
  have hMK : M ≤ K := fun y hy => (hmemK y).mpr fun l' hl' => hMle l' hl' hy
  have hKU : K ≤ Vn l := fun y hy => (hmemK y).mp hy l hl
  have hconjK : ∀ g ∈ stab α, ∀ y ∈ K, g * y * g⁻¹ ∈ K := by
    intro g hg y hy
    rw [hmemK] at hy ⊢
    intro l' hl'
    set gg : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨g, (mem_stab.mp hg).1⟩ with hgg
    have hggα : gg • α = α := smul_eq_of_mem_stab (g := gg) hg
    have hl'' : gg⁻¹ • l' ∈ nbrs α := by
      have := (smul_adj gg⁻¹).mpr (show (graph _ _ _).Adj α l' from hl')
      rwa [inv_smul_eq_iff.mpr hggα.symm] at this
    have hy' := hy _ hl''
    have e : Vn l' = conjSub g (Vn (gg⁻¹ • l')) := by
      show Vn l' = conjSub (gg : G) (Vn (gg⁻¹ • l'))
      rw [← Vn_smul, smul_inv_smul]
    rw [e, mem_conjSub, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy'
  have hnK : ∀ g ∈ stab α, g ∈ Subgroup.normalizer (K : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem (hconjK g hg) (hconjK g⁻¹ (Subgroup.inv_mem _ hg))
  have hKidx : K.relIndex (Vn l) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hMK Subgroup.index_ne_zero_of_finite).trans hMidx
  obtain ⟨ρ, hρα, hρ1, hρ3, hρl, -⟩ := exists_three_stab_two_nbrs F hα hl hβα hlβ
  have hUK : Vn l ≤ K := le_of_relIndex_le_two_of_norm hU2 (stab_le_normalizer_Vn l hρl)
    (hnK ρ hρα) (fun v hv => norm_three_Vn F hT1 hN hb hlf hρl hρ3 hρ1 hv) hKidx
  have hKeq : K = Vn l := le_antisymm hKU hUK
  have hUQ : Vn l ≤ Qv l := iSup₂_le fun μ hμ =>
    Zv_le_Qv_of_mem_nbrs F (show l ∈ nbrs μ from (show (graph _ _ _).Adj l μ from hμ).symm)
  have hUle : Vn l ≤ stab l ⊓ stab α :=
    le_inf (hUQ.trans (pCoreOf_le 2 _)) (hUQ.trans (hA.Qv_le_stab_of_mem_nbrs hαl))
  have hbot := hA.eq_bot_of_normalizes_both (show (graph _ _ _).Adj l α from hαl) hUle
    (stab_le_normalizer_Vn l) (fun g hg => hKeq ▸ hnK g hg)
  exact hA.Zv_ne_bot α (le_bot_iff.mp (hbot ▸ hZαU))

end T1

end CFSG.Quasithin.Kleidman.F204
