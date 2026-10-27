module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.TB4

open S35.Std S35.Fin S35.Ch S35.Ch2

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Nr (γ : Geo H M) (r : G) : Subgroup G where
  carrier := {g | g ∈ stab γ ∧ ⁅g, r⁆ ∈ Vn γ}
  mul_mem' := by
    rintro g1 g2 ⟨h1s, h1v⟩ ⟨h2s, h2v⟩
    refine ⟨(stab γ).mul_mem h1s h2s, ?_⟩
    have e : ⁅g1 * g2, r⁆ = (g1 * ⁅g2, r⁆ * g1⁻¹) * ⁅g1, r⁆ := by group
    rw [e]
    exact (Vn γ).mul_mem (conj_mem_Vn h1s h2v) h1v
  one_mem' := by
    refine ⟨(stab γ).one_mem, ?_⟩
    show ⁅(1 : G), r⁆ ∈ Vn γ
    rw [commutatorElement_def]
    simp
  inv_mem' := by
    rintro g ⟨hs, hv⟩
    refine ⟨(stab γ).inv_mem hs, ?_⟩
    have e : ⁅g⁻¹, r⁆ = g⁻¹ * (⁅g, r⁆)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_Vn ((stab γ).inv_mem hs) ((Vn γ).inv_mem hv)

omit [Finite G] in
theorem conj_mem_Qv {γ : Geo H M} {g q : G} (hg : g ∈ stab γ) (hq : q ∈ Qv γ) :
    g * q * g⁻¹ ∈ Qv γ :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab γ) hg) q).mp hq

variable {γ : Geo H M} (c : Chart2 γ)

@[expose] noncomputable def Phi (hS : Sit H M S) (hγ : vtype γ = false) (r : G)
    (hQ : Qv γ ≤ Nr γ r) : ↥(Qv γ) →* orth.W where
  toFun q := c.π ⟨⁅(q : G), r⁆, (hQ q.2).2⟩
  map_one' := by
    have : (⟨⁅((1 : ↥(Qv γ)) : G), r⁆, (hQ (1 : ↥(Qv γ)).2).2⟩ : ↥(Vn γ)) = 1 := by
      apply Subtype.ext
      show ⁅(1 : G), r⁆ = 1
      simp [commutatorElement_def]
    rw [this, map_one]
  map_mul' := by
    intro q1 q2
    have hs1 : (q1 : G) ∈ stab γ := S35.Ch.Qv_le_stab' γ q1.2
    have hθ : c.θ ⟨(q1 : G), hs1⟩ = 1 := (c.ker_iff hS hγ ⟨(q1 : G), hs1⟩).mpr q1.2
    have e : (⟨⁅((q1 * q2 : ↥(Qv γ)) : G), r⁆, (hQ (q1 * q2).2).2⟩ : ↥(Vn γ)) =
        conjV ⟨(q1 : G), hs1⟩ ⟨⁅(q2 : G), r⁆, (hQ q2.2).2⟩ * ⟨⁅(q1 : G), r⁆, (hQ q1.2).2⟩ := by
      apply Subtype.ext
      show ⁅(q1 : G) * (q2 : G), r⁆ = _
      show _ = (q1 : G) * ⁅(q2 : G), r⁆ * (q1 : G)⁻¹ * ⁅(q1 : G), r⁆
      group
    show c.π _ = c.π _ * c.π _
    rw [e, map_mul, c.π_conj, hθ, map_one, MulAut.one_apply, mul_comm]

theorem Phi_apply (hS : Sit H M S) (hγ : vtype γ = false) (r : G) (hQ : Qv γ ≤ Nr γ r)
    (q : ↥(Qv γ)) :
    Phi c hS hγ r hQ q = c.π ⟨⁅(q : G), r⁆, (hQ q.2).2⟩ := rfl

theorem Phi_conj (hS : Sit H M S) (hγ : vtype γ = false) (r : G) (hQ : Qv γ ≤ Nr γ r)
    {g : G} (hg : g ∈ Nr γ r) {q : G} (hq : q ∈ Qv γ) :
    Phi c hS hγ r hQ ⟨g * q * g⁻¹, conj_mem_Qv hg.1 hq⟩ =
      orth.act (c.θ ⟨g, hg.1⟩) (Phi c hS hγ r hQ ⟨q, hq⟩) := by
  have hgi : g⁻¹ ∈ Nr γ r := (Nr γ r).inv_mem hg
  set w : G := ⁅g⁻¹, r⁆ with hw
  have hwV : w ∈ Vn γ := hgi.2
  have hqV : ⁅q, r⁆ ∈ Vn γ := (hQ hq).2
  have hqwZ : ⁅q, w⁆ ∈ Zv γ := by
    rw [← commutatorElement_inv]
    refine (Zv γ).inv_mem ?_
    rw [← comm_Vn_Qv hS hγ]
    exact Subgroup.commutator_mem_commutator hwV hq
  have hcomm : w * ⁅q, r⁆ * w⁻¹ = ⁅q, r⁆ := by
    have := isElemAbelian_comm (Vn_isElemAbelian hS γ) hwV hqV
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have e : ⁅g * q * g⁻¹, r⁆ = g * (⁅q, w⁆ * ⁅q, r⁆) * g⁻¹ := by
    have e1 : ⁅g * q * g⁻¹, r⁆ = g * ⁅q, w * r⁆ * g⁻¹ := by
      rw [hw]; simp only [commutatorElement_def]; group
    have e2 : ⁅q, w * r⁆ = ⁅q, w⁆ * (w * ⁅q, r⁆ * w⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e1, e2, hcomm]
  have hxa : (⟨⁅q, w⁆, S34.Zv_le_Cb hS.glob hγ |>.trans (S34.Cb_le_Vn γ) hqwZ⟩ : ↥(Vn γ)) ∈
      (c.π).ker := by
    rw [MonoidHom.mem_ker, c.π_eq_one]
    exact S34.Zv_le_Cb hS.glob hγ hqwZ
  have e' : (⟨⁅g * q * g⁻¹, r⁆, (hQ (conj_mem_Qv hg.1 hq)).2⟩ : ↥(Vn γ)) =
      conjV ⟨g, hg.1⟩ (⟨⁅q, w⁆, S34.Zv_le_Cb hS.glob hγ |>.trans (S34.Cb_le_Vn γ) hqwZ⟩ *
        ⟨⁅q, r⁆, hqV⟩) := by
    apply Subtype.ext
    show ⁅g * q * g⁻¹, r⁆ = g * (⁅q, w⁆ * ⁅q, r⁆) * g⁻¹
    exact e
  rw [Phi_apply, Phi_apply]
  show c.π _ = _
  rw [e', c.π_conj, map_mul, MonoidHom.mem_ker.mp hxa, one_mul]

end S35.TB4

end F53.Stellmacher

end CFSG.Quasithin
