module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7K
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7C
public import CFSG.Quasithin.Recognition.Kleidman.F204.EqZ

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

private theorem vtype_of_mem_nbrs_L {H M : Subgroup G} {u v : Geo H M} (h : v ∈ nbrs u) :
    vtype v = !vtype u := by
  have := vtype_ne_of_adj (show (graph _ _ _).Adj u v from h)
  cases h1 : vtype u <;> cases h2 : vtype v <;> simp_all

omit [Finite G] in
private theorem comm_of_elem_L {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

theorem mem_Qv_of_fix_all (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {z : G} (hz : z ∈ stab δ) (hz2 : z * z = 1)
    (hfix : ∀ ν ∈ nbrs δ, z ∈ stab ν) : z ∈ Qv δ := by
  obtain ⟨E, hEs, hE3, hEQ, hball⟩ := ballStab_one_false F hδ
  have hzb : z ∈ ballStab 1 δ := by
    unfold ballStab
    refine Subgroup.mem_iInf.mpr fun ν => Subgroup.mem_iInf.mpr fun hν => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hν with h0 | h1
    · rw [← (dist_eq_zero_iff (Amal.of_frame F).amalgam.gen).mp h0]; exact hz
    · exact hfix ν (dist_eq_one_iff_adj.mp h1)
  rw [hball] at hzb
  have hEN : E ≤ Subgroup.normalizer (Qv δ : Set G) := hEs.trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨q, hq, e, he, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hEN).mp hzb
  have he3 : e ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥E) (x := ⟨e, he⟩)
    rw [hE3] at this
    simpa using congrArg Subtype.val this
  have heN : e ∈ Subgroup.normalizer (Qv δ : Set G) := hEN he
  have he2 : e * e ∈ Qv δ := by
    have h1 : e * q⁻¹ * e⁻¹ ∈ Qv δ :=
      (Subgroup.mem_normalizer_iff.mp heN _).mp ((Qv δ).inv_mem hq)
    have e' : e * e = (e * q⁻¹ * e⁻¹) * q⁻¹ * (q * e * (q * e)) := by group
    rw [e', hz2, mul_one]
    exact (Qv δ).mul_mem h1 ((Qv δ).inv_mem hq)
  have heQ : e ∈ Qv δ := by
    have : e = (e * e) * (e * e) * (e ^ 3)⁻¹ := by group
    rw [this, he3, inv_one, mul_one]
    exact (Qv δ).mul_mem he2 he2
  have he1 : e = 1 := by
    have : e ∈ E ⊓ Qv δ := Subgroup.mem_inf.mpr ⟨he, heQ⟩
    rw [hEQ, Subgroup.mem_bot] at this
    exact this
  rw [he1, mul_one]
  exact hq

omit [Finite G] in
theorem comm_conj_comm {q z : G} (hz : z * z = 1) (hq2 : (q * q) * z = z * (q * q))
    (hyz : (q * z * q⁻¹) * z = z * (q * z * q⁻¹)) :
    q * (q * z * q⁻¹ * z⁻¹) = (q * z * q⁻¹ * z⁻¹) * q := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h2 : q * z * q⁻¹ = q⁻¹ * z * q := by
    calc q * z * q⁻¹ = q⁻¹ * (q * q * z) * q⁻¹ := by group
      _ = q⁻¹ * (z * (q * q)) * q⁻¹ := by rw [hq2]
      _ = q⁻¹ * z * q := by group
  calc q * (q * z * q⁻¹ * z⁻¹) = q * (q * z * q⁻¹) * z⁻¹ := by group
    _ = q * (q⁻¹ * z * q) * z⁻¹ := by rw [h2]
    _ = z * (q * z⁻¹ * q⁻¹) * q := by group
    _ = z * (q * z * q⁻¹) * q := by rw [hzi]
    _ = (q * z * q⁻¹) * z * q := by rw [← hyz]
    _ = (q * z * q⁻¹ * z⁻¹) * q := by rw [hzi]

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem exists_mu_not_le : ∃ μ ∈ nbrs α', ¬ Zv μ ≤ Qv β := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  by_contra hcon
  push Not at hcon
  have hN := natA_of_W_le F hT1 hc hII hcon
  have hαβ : β ∈ nbrs α := hc.adj
  have hβα : α ∈ nbrs β := mem_nbrs_symm hαβ
  have hV2 := hA.isElemAbelian_Vn hb3 β
  have hN1 : ∀ q ∈ Qv β, ∀ v ∈ Vn β, q * v * q⁻¹ * v⁻¹ ∈ Zv β := by
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (Vn β : Set G) :=
      stab_le_normalizer_Vn β (pCoreOf_le 2 _ hq)
    have hVab : ∀ a ∈ Vn β, ∀ b ∈ Vn β, a * b = b * a := fun a ha b hb => comm_of_elem_L hV2 ha hb
    set σ := commMap hVab hqN with hσ
    set K : Subgroup G := (((Zv β).subgroupOf (Vn β)).comap σ).map (Vn β).subtype with hK
    have hmemK : ∀ v (hv : v ∈ Vn β), q * v * q⁻¹ * v⁻¹ ∈ Zv β → v ∈ K := by
      intro v hv h
      refine ⟨⟨v, hv⟩, ?_, rfl⟩
      show σ ⟨v, hv⟩ ∈ (Zv β).subgroupOf (Vn β)
      rw [Subgroup.mem_subgroupOf, commMap_apply]
      exact h
    have hKmem : ∀ v ∈ K, q * v * q⁻¹ * v⁻¹ ∈ Zv β := by
      rintro _ ⟨⟨v, hv⟩, hvK, rfl⟩
      have := Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hvK)
      rw [commMap_apply] at this
      exact this
    have hle : Vn β ≤ K := by
      refine iSup₂_le fun x hx z hz => ?_
      have hxβ : β ∈ nbrs x := mem_nbrs_symm hx
      have hxt : vtype x = true := by rw [vtype_of_mem_nbrs_L hx, hβ]; rfl
      have hzV : z ∈ Vn β := hA.Zv_le_Vn hx hz
      refine hmemK z hzV ?_
      have hqx : q ∈ stab x := hA.Qv_le_stab_of_mem_nbrs hx hq
      by_cases hqQ : q ∈ Qv x
      · have hcomm : q * z = z * q :=
          (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hz).2 q hqQ)
        rw [hcomm, show z * q * q⁻¹ * z⁻¹ = 1 by group]
        exact (Zv β).one_mem
      · obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (stab β)) ⟨q, hq⟩
        have hqn : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
        have hC := inf_centralizer_two_eq F hT1 hxt (hN x hxt) hxβ
          (not_stab_le_centralizer_Zv F hT1 hxt) hqx (pCoreOf_le 2 _ hq) hqn hqQ
        rw [← hC]
        have hZx2 := hA.isElemAbelian_Zv x
        have hqz : q * z * q⁻¹ ∈ Zv x :=
          (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv x hqx) z).mp hz
        refine Subgroup.mem_inf.mpr ⟨(Zv x).mul_mem hqz ((Zv x).inv_mem hz), ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hq2 : q * q ∈ Qv x := sq_mem_Qv_of_mem_nbrs F hxt hxβ hq
        have hc2 : (q * q) * z = z * (q * q) :=
          (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hz).2 _ hq2)
        have hz2 : z * z = 1 := by rw [← pow_two]; exact hZx2.2 z hz
        exact (comm_conj_comm hz2 hc2 (comm_of_elem_L hZx2 hqz hz)).symm
    exact fun v hv => hKmem v (hle hv)
  obtain ⟨μ, hμ, hA0μ⟩ := t1II_exists_nbr F hT1 hc hII
  have hμt : vtype μ = true := by rw [vtype_of_mem_nbrs_L hμ, hα']; rfl
  have hα'μ : α' ∈ nbrs μ := mem_nbrs_symm hμ
  obtain ⟨a, haA, haQ⟩ : ∃ a ∈ Zv α ⊓ Qv α', a ∉ Qv μ := by
    by_contra h; push Not at h; exact hA0μ fun a ha => h a ha
  have haZ : a ∈ Zv α := (Subgroup.mem_inf.mp haA).1
  have haα' : a ∈ Qv α' := (Subgroup.mem_inf.mp haA).2
  have haμ : a ∈ stab μ := hA.Qv_le_stab_of_mem_nbrs hμ haα'
  have haV : a ∈ Vn β := hA.Zv_le_Vn hβα haZ
  have ha2 : a * a = 1 := by rw [← pow_two]; exact (hA.isElemAbelian_Zv α).2 a haZ
  have hZμ2 := hA.isElemAbelian_Zv μ
  have hZab : ∀ x ∈ Zv μ, ∀ y ∈ Zv μ, x * y = y * x := fun x hx y hy => comm_of_elem_L hZμ2 hx hy
  have haN : a ∈ Subgroup.normalizer (Zv μ : Set G) := hA.stab_le_normalizer_Zv μ haμ
  set σ := commMap hZab haN with hσ
  have hCa := inf_centralizer_two_eq F hT1 hμt (hN μ hμt) hα'μ (not_stab_le_centralizer_Zv F hT1 hμt)
    haμ (pCoreOf_le 2 _ haα') (k := 1) (by rw [pow_one, pow_two]; exact ha2) haQ
  have hker : ∀ z : ↥(Zv μ), σ z = 1 ↔ (z : G) ∈ Zv α' := by
    intro z
    rw [← hCa, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [commMap_apply, Subgroup.coe_one] at h'
      refine ⟨z.2, ?_⟩
      have h3 : a * (z : G) * a⁻¹ = z := mul_inv_eq_one.mp h'
      calc (z : G) * a = (a * z * a⁻¹) * a := by rw [h3]
        _ = a * z := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [commMap_apply, Subgroup.coe_one, ← h]
      group
  have hrange : ∀ z : ↥(Zv μ), ((σ z : ↥(Zv μ)) : G) ∈ Zv α' := by
    intro z
    rw [← hCa, commMap_apply]
    refine Subgroup.mem_inf.mpr ⟨(Zv μ).mul_mem ((Subgroup.mem_normalizer_iff.mp haN z).mp z.2)
      ((Zv μ).inv_mem z.2), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc2 : (a * a) * (z : G) = z * (a * a) := by rw [ha2]; group
    have hz2 : (z : G) * z = 1 := by rw [← pow_two]; exact hZμ2.2 z z.2
    have hyz := hZab _ ((Subgroup.mem_normalizer_iff.mp haN z).mp z.2) _ z.2
    exact (comm_conj_comm hz2 hc2 hyz).symm
  have hcardμ : Nat.card (Zv μ) = 16 := (hN μ hμt).1
  have hcardα' : Nat.card (Zv α') = 4 := card_Zv_nbr F hT1 hμt (hN μ hμt) hα'μ
  have hcardβ : Nat.card (Zv β) = 4 := card_Zv_nbr F hT1 hα (hN α hα) hαβ
  have hkerσ : σ.ker = (Zv α').subgroupOf (Zv μ) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker z
  have hZα'μ : Zv α' ≤ Zv μ := by rw [Zv_eq_inf_centralizer F hT1 hμt hα'μ]; exact inf_le_left
  have hcardker : Nat.card σ.ker = 4 := by
    rw [hkerσ, natCard_subgroupOf' hZα'μ]
    exact hcardα'
  have hcr := Subgroup.card_ker_mul_card_range σ
  rw [hcardker, hcardμ] at hcr
  have hcardrange : Nat.card σ.range = 4 := by omega
  have hrangeeq : σ.range = (Zv α').subgroupOf (Zv μ) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨z, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hrange z)
    · rw [hcardrange, natCard_subgroupOf' hZα'μ, hcardα']
  have hα'β : Zv α' ≤ Zv β := by
    intro w hw
    have hw' : (⟨w, hZα'μ hw⟩ : ↥(Zv μ)) ∈ σ.range := by
      rw [hrangeeq]; exact Subgroup.mem_subgroupOf.mpr hw
    obtain ⟨z, hz⟩ := hw'
    have hzw : a * z * a⁻¹ * (z : G)⁻¹ = w := by
      have := congrArg Subtype.val hz
      rw [commMap_apply] at this
      exact this
    rw [← hzw]
    have hzQ : (z : G) ∈ Qv β := hcon μ hμ z.2
    have h1 := hN1 z hzQ a⁻¹ ((Vn β).inv_mem haV)
    have hzaz : (z : G) * a⁻¹ * (z : G)⁻¹ ∈ Vn β :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β (pCoreOf_le 2 _ hzQ)) _).mp
        ((Vn β).inv_mem haV)
    have hcomm := comm_of_elem_L hV2 haV hzaz
    have e : a * z * a⁻¹ * (z : G)⁻¹ = (z : G) * a⁻¹ * (z : G)⁻¹ * a⁻¹⁻¹ := by
      calc a * z * a⁻¹ * (z : G)⁻¹ = a * ((z : G) * a⁻¹ * (z : G)⁻¹) := by group
        _ = ((z : G) * a⁻¹ * (z : G)⁻¹) * a := hcomm
        _ = (z : G) * a⁻¹ * (z : G)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have hα'eqβ : Zv α' = Zv β :=
    Subgroup.eq_of_le_of_card_ge hα'β (by rw [hcardα', hcardβ])
  obtain ⟨z0, hz0, hz0Q⟩ := t1II_exists_z F hT1 hc hII
  have hz0V : z0 ∈ Vn β := hA.Zv_le_Vn hβα hz0
  have hz0α' : z0 ∈ stab α' := hVβ hz0V
  have hz02 : z0 * z0 = 1 := by rw [← pow_two]; exact (hA.isElemAbelian_Zv α).2 z0 hz0
  obtain ⟨ν, hν, hνz⟩ : ∃ ν ∈ nbrs α', z0 ∉ stab ν := by
    by_contra h
    push Not at h
    exact hz0Q (mem_Qv_of_fix_all F hα' hz0α' hz02 h)
  set zz : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨z0, (mem_stab.mp hz0α').1⟩ with hzz
  have hzzα' : zz • α' = α' := smul_eq_of_mem_stab (g := zz) hz0α'
  have hν' : zz • ν ∈ nbrs α' := by
    have := (smul_adj zz).mpr (show (graph _ _ _).Adj α' ν from hν)
    rwa [hzzα'] at this
  have hne : ν ≠ zz • ν := fun h => hνz (mem_stab_of_smul_eq (g := zz) h.symm)
  have hνt : vtype ν = true := by rw [vtype_of_mem_nbrs_L hν, hα']; rfl
  have hZν : Zv α' ≤ Zv ν := by
    rw [Zv_eq_inf_centralizer F hT1 hνt (mem_nbrs_symm hν)]; exact inf_le_left
  have hle : Zv (zz • ν) ≤ Zv ν := by
    rw [Zv_smul]
    intro x hx
    rw [mem_conjSub] at hx
    set t := z0⁻¹ * x * z0 with ht
    have htQ : t ∈ Qv β := hcon ν hν hx
    have h1 := hN1 t htQ z0 hz0V
    rw [← hα'eqβ] at h1
    have e : x = (t * z0 * t⁻¹ * z0⁻¹)⁻¹ * t := by rw [ht]; group
    rw [e]
    exact (Zv ν).mul_mem ((Zv ν).inv_mem (hZν h1)) hx
  have heq : Zv (zz • ν) = Zv ν :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Zv_smul]; unfold conjSub
      rw [Subgroup.card_map_of_injective (MulAut.conj (zz : G)).injective])
  exact Zv_ne_of_mem_nbrs_false F hα' hν hν' hne heq.symm

end CaseII

end CFSG.Quasithin.Kleidman.F204
