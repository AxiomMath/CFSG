module

public import CFSG.Milestones.ASVolI.C135.NE
public import CFSG.Milestones.ASVolI.C135.ND

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot fixAll)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G]

theorem burnsideC135_isElemAbelian_sup {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := by
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hAB a ha b hb, mul_inv_cancel_right]
      exact ha
    · intro h
      have hc := hAB _ h b⁻¹ (B.inv_mem hb)
      have e : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [← hc]
          _ = b * a * b⁻¹ := by group
      rw [e]
      exact h
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hBN
  have hmem : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    have hx' : x ∈ (A : Set G) * (B : Set G) := hset ▸ hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    CFSG.Quasithin.H13.Ch4.C135.mul_comm_of_isElemAbelian hA ha ha'
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    CFSG.Quasithin.H13.Ch4.C135.mul_comm_of_isElemAbelian hB hb hb'
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hxab⟩ := hmem x x.2
    obtain ⟨a', ha', b', hb', hyab⟩ := hmem y y.2
    show (x : G) * y = y * x
    rw [hxab, hyab]
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [hAc a ha a' ha', hBc b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    have h1 := hA.2 a ha
    have h2 := hB.2 b hb
    rw [sq] at h1 h2 ⊢
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hAB a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [h1, h2, one_mul]

variable [Finite G]

namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H

theorem qc_conj_one {t q : G} (ht : t ∈ pCoreOf 2 X) (hq : q ∈ c134Q X L) :
    burnsideC135_qc β (t * q * t⁻¹) 1 = burnsideC135_qc β q 1 := by
  obtain ⟨μ, hμ⟩ := H.shear ht
  have hmem : t * q * t⁻¹ ∈ c134Q X L :=
    (Subgroup.mem_normalizer_iff.mp (H.normQ (pCoreOf_le 2 X ht)) q).mp hq
  rw [burnsideC135_qc_of_mem hmem, burnsideC135_qc_of_mem hq]
  exact (hμ ⟨q, hq⟩ ⟨_, hmem⟩ rfl).2

theorem triv_of_shear {v : G} (hv : v ∈ pCoreOf 2 X)
    (h : ∀ (μ : F), (∀ (q q' : ↥(c134Q X L)), (q' : G) = v * q * v⁻¹ →
      Multiplicative.toAdd (β q') 0 =
          Multiplicative.toAdd (β q) 0 + μ • Multiplicative.toAdd (β q) 1 ∧
        Multiplicative.toAdd (β q') 1 = Multiplicative.toAdd (β q) 1) → μ = 0) :
    ∀ q ∈ c134Q X L, v * q * v⁻¹ * q⁻¹ ∈ centerOf (c134Q X L) := by
  obtain ⟨μ, hμ⟩ := H.shear hv
  have h0 := h μ hμ
  intro q hq
  have hmem : v * q * v⁻¹ ∈ c134Q X L :=
    (Subgroup.mem_normalizer_iff.mp (H.normQ (pCoreOf_le 2 X hv)) q).mp hq
  obtain ⟨e0, e1⟩ := hμ ⟨q, hq⟩ ⟨_, hmem⟩ rfl
  rw [h0, zero_smul, add_zero] at e0
  have h2 : (⟨q, hq⟩ : ↥(c134Q X L))⁻¹ * ⟨_, hmem⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Multiplicative.toAdd.injective
    funext i
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · exact e0.symm
    · exact e1.symm
  rw [H.βk, Subgroup.mem_subgroupOf] at h2
  have h3 : q⁻¹ * (v * q * v⁻¹) ∈ centerOf (c134Q X L) := h2
  have hqN : q ∈ Subgroup.normalizer (centerOf (c134Q X L) : Set G) :=
    le_normalizer_centerOf (fun x hx => Subgroup.le_normalizer hx) hq
  have e : v * q * v⁻¹ * q⁻¹ = q * (q⁻¹ * (v * q * v⁻¹)) * q⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hqN _).mp h3

theorem le_V_of_nontriv {v : G}
    (hv : v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))
    (hnt : ¬ ∀ q ∈ c134Q X L, v * q * v⁻¹ * q⁻¹ ∈ centerOf (c134Q X L))
    {t : G} (ht : t ∈ pCoreOf 2 X) (htv : t * v = v * t) :
    t ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) := by
  obtain ⟨μ, hμ⟩ := H.shear hv.1
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hnt
    refine H.triv_of_shear hv.1 fun μ' hμ' => ?_
    obtain ⟨q, hq0, hq1⟩ := H.exists_coords 0 (Pi.single 0 1)
    have hmem : v * q * v⁻¹ ∈ c134Q X L :=
      (Subgroup.mem_normalizer_iff.mp (H.normQ (pCoreOf_le 2 X hv.1)) _).mp q.2
    have a1 := (hμ q ⟨_, hmem⟩ rfl).1
    have a2 := (hμ' q ⟨_, hmem⟩ rfl).1
    rw [a1, hq1, h0] at a2
    have := congrFun a2 0
    simpa using this.symm
  exact H.le_V_of_shear hv hμ0 hμ ht htv

theorem coe_sup_WE : ((burnsideC135_Wc β 1 ⊔
    (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) : Subgroup G) : Set G) =
    (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _
    fun _ he => H.normW (pCoreOf_le 2 X he.1)

theorem triv_of_mem_sup {x : G} (hx : x ∈ burnsideC135_Wc β 1 ⊔
    (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) :
    ∀ q ∈ c134Q X L, x * q * x⁻¹ * q⁻¹ ∈ centerOf (c134Q X L) := by
  have hx' : x ∈ (burnsideC135_Wc β 1 : Set G) *
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) := by
    rw [← H.coe_sup_WE]
    exact hx
  obtain ⟨w, hw, e, he, rfl⟩ := hx'
  intro q hq
  have heq : q * e = e * q := Subgroup.mem_centralizer_iff.mp he.2 q hq
  have h1 : w * e * q * (w * e)⁻¹ * q⁻¹ = w * q * w⁻¹ * q⁻¹ := by
    calc w * e * q * (w * e)⁻¹ * q⁻¹ = w * (e * q) * e⁻¹ * w⁻¹ * q⁻¹ := by group
      _ = w * (q * e) * e⁻¹ * w⁻¹ * q⁻¹ := by rw [heq]
      _ = w * q * w⁻¹ * q⁻¹ := by group
  rw [h1]
  exact H.comm w (burnsideC135_Wc_le 1 hw) q hq

theorem mem_sup_of_triv {v : G}
    (hv : v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))
    (htriv : ∀ q ∈ c134Q X L, v * q * v⁻¹ * q⁻¹ ∈ centerOf (c134Q X L)) :
    v ∈ burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) := by
  obtain ⟨w, hw, hvw⟩ := H.exists_mul_mem_E hv htriv
  have hE : v * w ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) :=
    ⟨(pCoreOf 2 X).mul_mem hv.1 (H.Q_le (burnsideC135_Wc_le 1 hw)), hvw⟩
  have e : v = w⁻¹ * (w * (v * w) * w⁻¹) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ((burnsideC135_Wc β 1).inv_mem hw))
    (Subgroup.mem_sup_right ?_)
  have hwX : w ∈ X := pCoreOf_le 2 X (H.Q_le (burnsideC135_Wc_le 1 hw))
  exact (Subgroup.mem_normalizer_iff.mp (H.normE hwX) _).mp hE

theorem sup_le_V : burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤
    pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) :=
  sup_le H.W₁_le_V H.E_le_V

theorem inf_WE_le : burnsideC135_Wc β 1 ⊓
    (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤ centerOf (c134Q X L) :=
  fun _ h => ⟨burnsideC135_Wc_le 1 h.1, h.2.2⟩

@[expose] noncomputable def proj (t : G) : Fin 3 → F :=
  haveI := Classical.propDecidable (t ∈ pCoreOf 2 X)
  if ht : t ∈ pCoreOf 2 X then
    burnsideC135_qc β (Classical.choose (Classical.choose_spec (H.exists_V_mul ht)).2) 1
  else 0

theorem qc_eq_of_decomp {v q v' q' : G}
    (hv : v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))
    (hq : q ∈ c134Q X L)
    (hv' : v' ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))
    (hq' : q' ∈ c134Q X L) (h : v * q = v' * q') :
    burnsideC135_qc β q 1 = burnsideC135_qc β q' 1 := by
  have e : v'⁻¹ * v = q' * q⁻¹ := by
    calc v'⁻¹ * v = v'⁻¹ * (v * q) * q⁻¹ := by group
      _ = v'⁻¹ * (v' * q') * q⁻¹ := by rw [h]
      _ = q' * q⁻¹ := by group
  have hmemQ : q' * q⁻¹ ∈ c134Q X L := (c134Q X L).mul_mem hq' ((c134Q X L).inv_mem hq)
  have hmemV : q' * q⁻¹ ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) := by
    rw [← e]
    exact (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).mul_mem
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).inv_mem hv') hv
  have hW := (H.mem_W₁_iff.mp (H.mem_W₁_of_commute hmemQ hmemV.2)).2
  rw [burnsideC135_qc_mul hq' ((c134Q X L).inv_mem hq), burnsideC135_qc_inv hq] at hW
  have := congrArg (fun x => x + burnsideC135_qc β q 1) hW
  simp only [Pi.add_apply, Pi.neg_apply, neg_add_cancel_right, zero_add] at this
  exact this.symm

theorem proj_eq {t v q : G}
    (hv : v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))
    (hq : q ∈ c134Q X L) (htvq : t = v * q) : H.proj t = burnsideC135_qc β q 1 := by
  have ht : t ∈ pCoreOf 2 X := htvq ▸ (pCoreOf 2 X).mul_mem hv.1 (H.Q_le hq)
  rw [proj, dif_pos ht]
  have hspec := Classical.choose_spec (H.exists_V_mul ht)
  have hspec3 := Classical.choose_spec hspec.2
  exact (H.qc_eq_of_decomp hv hq hspec.1 hspec3.1 (htvq.symm.trans hspec3.2)).symm

theorem proj_mul {t t' : G} (ht : t ∈ pCoreOf 2 X) (ht' : t' ∈ pCoreOf 2 X) :
    H.proj (t * t') = H.proj t + H.proj t' := by
  obtain ⟨v, hv, q, hq, rfl⟩ := H.exists_V_mul ht
  obtain ⟨v', hv', q', hq', rfl⟩ := H.exists_V_mul ht'
  have hv'inv : v'⁻¹ ∈ pCoreOf 2 X := (pCoreOf 2 X).inv_mem hv'.1
  have hmem : v'⁻¹ * q * v'⁻¹⁻¹ ∈ c134Q X L :=
    (Subgroup.mem_normalizer_iff.mp (H.normQ (pCoreOf_le 2 X hv'inv)) q).mp hq
  have e : v * q * (v' * q') = (v * v') * ((v'⁻¹ * q * v'⁻¹⁻¹) * q') := by group
  rw [e, H.proj_eq ((pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).mul_mem hv hv')
    ((c134Q X L).mul_mem hmem hq') rfl, H.proj_eq hv hq rfl, H.proj_eq hv' hq' rfl,
    burnsideC135_qc_mul hmem hq', Pi.add_apply, H.qc_conj_one hv'inv hq]

theorem proj_eq_zero_iff {t : G} (ht : t ∈ pCoreOf 2 X) :
    H.proj t = 0 ↔ t ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) := by
  obtain ⟨v, hv, q, hq, rfl⟩ := H.exists_V_mul ht
  rw [H.proj_eq hv hq rfl]
  constructor
  · intro h
    have hqW : q ∈ burnsideC135_Wc β 1 := H.mem_W₁_iff.mpr ⟨hq, h⟩
    exact (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).mul_mem hv
      (H.W₁_le_V hqW)
  · intro h
    have hqV : q ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) := by
      have e : q = v⁻¹ * (v * q) := by group
      rw [e]
      exact (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).mul_mem
        ((pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).inv_mem hv) h
    exact (H.mem_W₁_iff.mp (H.mem_W₁_of_commute hq hqV.2)).2

theorem proj_conj {A : Subgroup G} (hAX : A ≤ X) (a : ↥A) {t : G} (ht : t ∈ pCoreOf 2 X) :
    H.proj ((a : G) * t * (a : G)⁻¹) =
      H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW) a (H.proj t) := by
  obtain ⟨v, hv, q, hq, rfl⟩ := H.exists_V_mul ht
  have haX : (a : G) ∈ X := hAX a.2
  have hmemV := (Subgroup.mem_normalizer_iff.mp (H.normV haX) v).mp hv
  have hmemQ := (Subgroup.mem_normalizer_iff.mp (H.normQ haX) q).mp hq
  have e : (a : G) * (v * q) * (a : G)⁻¹ = ((a : G) * v * (a : G)⁻¹) * ((a : G) * q * (a : G)⁻¹) := by
    group
  rw [e, H.proj_eq hmemV hmemQ rfl, H.proj_eq hv hq rfl, burnsideC135_qc_of_mem hmemQ,
    burnsideC135_qc_of_mem hq]
  have h := H.q2.rep_κ (hAX.trans H.normQ) (hAX.trans H.normW) a ⟨q, hq⟩
  rw [H.q2_κ, H.q2_κ] at h
  exact h.symm

end burnsideC135_H1

end CFSG.ASVolI

end
