module

public import CFSG.Milestones.ASVolI.C135.NF

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4 (mem_pCoreOf_iff')
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot fixAll)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H

@[expose] noncomputable def projE (v : G) : Fin 3 → F :=
  haveI := Classical.propDecidable (v ∈ burnsideC135_Wc β 1 ⊔
    (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)))
  if hv : v ∈ burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) then
    burnsideC135_qc β (Classical.choose (show v ∈ (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) by
        rw [← H.coe_sup_WE]; exact hv)) 0
  else 0

theorem qc_eq_of_decompE {w e w' e' : G} (hw : w ∈ burnsideC135_Wc β 1)
    (he : e ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))
    (hw' : w' ∈ burnsideC135_Wc β 1)
    (he' : e' ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))
    (h : w * e = w' * e') : burnsideC135_qc β w 0 = burnsideC135_qc β w' 0 := by
  have e1 : w'⁻¹ * w = e' * e⁻¹ := by
    calc w'⁻¹ * w = w'⁻¹ * (w * e) * e⁻¹ := by group
      _ = w'⁻¹ * (w' * e') * e⁻¹ := by rw [h]
      _ = e' * e⁻¹ := by group
  have hmemW : w'⁻¹ * w ∈ burnsideC135_Wc β 1 :=
    (burnsideC135_Wc β 1).mul_mem ((burnsideC135_Wc β 1).inv_mem hw') hw
  have hmemE : w'⁻¹ * w ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) := by
    rw [e1]
    exact (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).mul_mem he'
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).inv_mem he)
  have hU : w'⁻¹ * w ∈ centerOf (c134Q X L) := H.inf_WE_le ⟨hmemW, hmemE⟩
  have hwQ := burnsideC135_Wc_le 1 hw
  have hw'Q := burnsideC135_Wc_le 1 hw'
  have h0 := (H.qc_eq_zero_iff ((c134Q X L).mul_mem ((c134Q X L).inv_mem hw'Q) hwQ)).mpr hU
  rw [burnsideC135_qc_mul ((c134Q X L).inv_mem hw'Q) hwQ, burnsideC135_qc_inv hw'Q] at h0
  have := congrFun h0 0
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
  linear_combination this

theorem projE_eq {v w e : G} (hw : w ∈ burnsideC135_Wc β 1)
    (he : e ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) (hv : v = w * e) :
    H.projE v = burnsideC135_qc β w 0 := by
  have hvS : v ∈ burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) :=
    hv ▸ Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right he)
  rw [projE, dif_pos hvS]
  have hspec := Classical.choose_spec (show v ∈ (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) by
        rw [← H.coe_sup_WE]; exact hvS)
  obtain ⟨hw₀, hrest⟩ := hspec
  obtain ⟨e₀, he₀, hve₀⟩ := hrest
  exact H.qc_eq_of_decompE hw₀ he₀ hw he (hve₀.trans hv)

theorem projE_mul {v v' : G}
    (hv : v ∈ burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)))
    (hv' : v' ∈ burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) :
    H.projE (v * v') = H.projE v + H.projE v' := by
  have hv1 : v ∈ (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) := by
    rw [← H.coe_sup_WE]; exact hv
  have hv1' : v' ∈ (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) := by
    rw [← H.coe_sup_WE]; exact hv'
  obtain ⟨w, hw, e, he, rfl⟩ := hv1
  obtain ⟨w', hw', e', he', rfl⟩ := hv1'
  have hew' : e * w' = w' * e := (Subgroup.mem_centralizer_iff.mp he.2 w'
    (burnsideC135_Wc_le 1 hw')).symm
  have e1 : w * e * (w' * e') = (w * w') * (e * e') := by
    calc w * e * (w' * e') = w * (e * w') * e' := by group
      _ = w * (w' * e) * e' := by rw [hew']
      _ = (w * w') * (e * e') := by group
  rw [H.projE_eq ((burnsideC135_Wc β 1).mul_mem hw hw')
    ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).mul_mem he he') e1,
    H.projE_eq hw he rfl, H.projE_eq hw' he' rfl,
    burnsideC135_qc_mul (burnsideC135_Wc_le 1 hw) (burnsideC135_Wc_le 1 hw'), Pi.add_apply]

theorem projE_eq_zero_iff {v : G}
    (hv : v ∈ burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) :
    H.projE v = 0 ↔ v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) := by
  have hv1 : v ∈ (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) := by
    rw [← H.coe_sup_WE]; exact hv
  obtain ⟨w, hw, e, he, rfl⟩ := hv1
  rw [H.projE_eq hw he rfl]
  have hwQ := burnsideC135_Wc_le 1 hw
  have hUE : centerOf (c134Q X L) ≤ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) :=
    fun u hu => ⟨H.Q_le hu.1, hu.2⟩
  constructor
  · intro h
    have hw1 := (H.mem_W₁_iff.mp hw).2
    have hwU : w ∈ centerOf (c134Q X L) := by
      refine (H.qc_eq_zero_iff hwQ).mp ?_
      funext i
      rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
      · exact h
      · exact hw1
    exact (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).mul_mem (hUE hwU) he
  · intro h
    have hwE : w ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) := by
      have e1 : w = (w * e) * e⁻¹ := by group
      rw [e1]
      exact (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).mul_mem h
        ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).inv_mem he)
    have hwU : w ∈ centerOf (c134Q X L) := H.inf_WE_le ⟨hw, hwE⟩
    have := (H.qc_eq_zero_iff hwQ).mpr hwU
    exact congrFun this 0

theorem projE_conj {A : Subgroup G} (hAX : A ≤ X) (a : ↥A) {v : G}
    (hv : v ∈ burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) :
    H.projE ((a : G) * v * (a : G)⁻¹) =
      H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU) a (H.projE v) := by
  have hv1 : v ∈ (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) := by
    rw [← H.coe_sup_WE]; exact hv
  obtain ⟨w, hw, e, he, rfl⟩ := hv1
  have haX : (a : G) ∈ X := hAX a.2
  have hmemW := (Subgroup.mem_normalizer_iff.mp (H.normW haX) w).mp hw
  have hmemE := (Subgroup.mem_normalizer_iff.mp (H.normE haX) e).mp he
  have e1 : (a : G) * (w * e) * (a : G)⁻¹ = ((a : G) * w * (a : G)⁻¹) * ((a : G) * e * (a : G)⁻¹) := by
    group
  rw [e1, H.projE_eq hmemW hmemE rfl, H.projE_eq hw he rfl,
    burnsideC135_qc_of_mem (burnsideC135_Wc_le 1 hmemW),
    burnsideC135_qc_of_mem (burnsideC135_Wc_le 1 hw)]
  have h := H.q1.rep_κ (hAX.trans H.normW) (hAX.trans H.normU) a ⟨w, hw⟩
  rw [H.q1_κ, H.q1_κ, burnsideC135_βc_apply, burnsideC135_βc_apply] at h
  exact h.symm

theorem rep_eq_of_triv {A : Subgroup G} (hAX : A ≤ X)
    (htriv : ∀ t ∈ pCoreOf 2 X, ∀ q ∈ c134Q X L, t * q * t⁻¹ * q⁻¹ ∈ centerOf (c134Q X L))
    (a : ↥A) (x : Fin 3 → F) :
    H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU) a x =
      H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW) a x := by
  obtain ⟨l, hl, t, ht, hlt⟩ := H.mem_mul (hAX a.2)
  have hconj : ∀ q ∈ c134Q X L, ∀ i : Fin 2,
      burnsideC135_qc β ((a : G) * q * (a : G)⁻¹) i =
        ((dualHom (slNat α ⟨l, hl⟩) : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ burnsideC135_qc β q i := by
    intro q hq i
    have htq : t * q * t⁻¹ ∈ c134Q X L :=
      (Subgroup.mem_normalizer_iff.mp (H.normQ (pCoreOf_le 2 X ht)) q).mp hq
    have h1 : burnsideC135_qc β (t * q * t⁻¹) = burnsideC135_qc β q := by
      have hU := htriv t ht q hq
      have h2 := (H.qc_eq_zero_iff ((c134Q X L).mul_mem htq ((c134Q X L).inv_mem hq))).mpr hU
      rw [burnsideC135_qc_mul htq ((c134Q X L).inv_mem hq), burnsideC135_qc_inv hq] at h2
      exact (add_neg_eq_zero.mp h2)
    rw [hlt, show l * t * q * (l * t)⁻¹ = l * (t * q * t⁻¹) * l⁻¹ by group,
      H.qc_conj hl htq i, h1]
  obtain ⟨w, hw⟩ := H.q1.surj x
  obtain ⟨q, hq⟩ := H.q2.surj x
  have hwQ := burnsideC135_Wc_le 1 w.2
  have h1 : H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU) a x =
      ((dualHom (slNat α ⟨l, hl⟩) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
    rw [← hw, H.q1.rep_κ, H.q1_κ, H.q1_κ, burnsideC135_βc_apply, burnsideC135_βc_apply]
    have hmem : (a : G) * w * (a : G)⁻¹ ∈ c134Q X L :=
      (Subgroup.mem_normalizer_iff.mp (H.normQ (hAX a.2)) _).mp hwQ
    have h2 := hconj w hwQ 0
    rw [burnsideC135_qc_of_mem hmem, burnsideC135_qc_of_mem hwQ] at h2
    simp only [toAdd_ofAdd]
    exact h2
  have h2 : H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW) a x =
      ((dualHom (slNat α ⟨l, hl⟩) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
    rw [← hq, H.q2.rep_κ, H.q2_κ, H.q2_κ]
    have hmem : (a : G) * q * (a : G)⁻¹ ∈ c134Q X L :=
      (Subgroup.mem_normalizer_iff.mp (H.normQ (hAX a.2)) _).mp q.2
    have h3 := hconj q q.2 1
    rw [burnsideC135_qc_of_mem hmem, burnsideC135_qc_of_mem q.2] at h3
    exact h3
  rw [h1, h2]

theorem inf_E_le_U {A : Subgroup G} (hAX : A ≤ X) (hA : IsElemAbelian 2 A)
    (hAT : ¬ A ≤ pCoreOf 2 X) :
    A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤ centerOf (c134Q X L) := by
  intro e he
  obtain ⟨a, haA, haT⟩ : ∃ a ∈ A, a ∉ pCoreOf 2 X := by
    by_contra h
    push Not at h
    exact hAT h
  obtain ⟨l, hl, t, ht, hlt⟩ := H.mem_mul (hAX haA)
  have hae : a * e = e * a := CFSG.Quasithin.H13.Ch4.C135.mul_comm_of_isElemAbelian hA haA he.1
  have hte : t⁻¹ * e = e * t⁻¹ := H.T_comm_E ((pCoreOf 2 X).inv_mem ht) he.2
  have hla : l = a * t⁻¹ := by rw [hlt]; group
  have hle : l * e = e * l := by
    rw [hla]
    calc a * t⁻¹ * e = a * (t⁻¹ * e) := by group
      _ = a * (e * t⁻¹) := by rw [hte]
      _ = (a * e) * t⁻¹ := by group
      _ = e * (a * t⁻¹) := by rw [hae]; group
  have hl1 : slNat α ⟨l, hl⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨l, hl⟩ : ↥L) ∈ (slNat α).ker := h1
    rw [burnsideC135_slNat_ker H.surj] at h2
    have h3 : l ∈ pCoreOf 2 L := (mem_pCoreOf_iff' ⟨l, hl⟩).mpr h2
    have h4 : l ∈ pCoreOf 2 X := MS93.pCoreOf_le_pCoreOf_of_le_normalizer H.le H.normL h3
    apply haT
    rw [hlt]
    exact (pCoreOf 2 X).mul_mem h4 ht
  have hl2 : slNat α ⟨l, hl⟩ * slNat α ⟨l, hl⟩ = 1 := by
    rw [← map_mul]
    have ha2 : a * a = 1 := by
      have := hA.2 a haA
      rwa [sq] at this
    have hll : l * l ∈ pCoreOf 2 X := by
      have htN : t⁻¹ ∈ pCoreOf 2 X := (pCoreOf 2 X).inv_mem ht
      have haN := le_normalizer_pCoreOf 2 X (hAX haA)
      have h1 : a * t⁻¹ * a⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp haN _).mp htN
      have e1 : l * l = (a * t⁻¹ * a⁻¹) * (a * a) * t⁻¹ := by rw [hla]; group
      rw [e1, ha2, mul_one]
      exact (pCoreOf 2 X).mul_mem h1 htN
    have h1 : l * l ∈ pCoreOf 2 L := MS93.inf_le_pCoreOf H.le ⟨hll, L.mul_mem hl hl⟩
    have h2 : (⟨l * l, L.mul_mem hl hl⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (mem_pCoreOf_iff' ⟨l * l, L.mul_mem hl hl⟩).mp h1
    rw [← burnsideC135_slNat_ker H.surj] at h2
    exact h2
  exact H.mem_U_of_commute he.2 hl hl1 hl2 hle

omit [Fintype F] [CharP F 2] H in
theorem _root_.CFSG.ASVolI.burnsideC135_card_fixAll_dvd [Finite F] {E : Type*} [Group E]
    (ρ : E →* Equiv.Perm (Fin 3 → F)) (hadd : ∀ x v w, ρ x (v + w) = ρ x v + ρ x w) :
    Nat.card (fixAll ρ) ∣ Nat.card (Fin 3 → F) := by
  have h0 : ∀ x, ρ x 0 = 0 := fun x => by
    have := hadd x 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∀ x, ρ x v = v}
      add_mem' := fun {v w} hv hw x => by rw [hadd, hv x, hw x]
      zero_mem' := fun x => h0 x
      neg_mem' := fun {v} hv x => by
        have h1 := hadd x v (-v)
        rw [add_neg_cancel, h0, hv x] at h1
        exact (neg_eq_of_add_eq_zero_right h1.symm).symm }
  have e : Nat.card (fixAll ρ) = Nat.card S := rfl
  rw [e]
  exact AddSubgroup.card_addSubgroup_dvd_card S

end burnsideC135_H1

end CFSG.ASVolI

end
