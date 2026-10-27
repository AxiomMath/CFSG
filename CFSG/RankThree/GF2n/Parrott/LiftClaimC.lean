module

public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.RankThree.GF2n.Parrott.Section4CentreSylow

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem quotientV_mul_comm (h : Tim79a.ParrottHyp z) (a b : QuotientV.V z) : a * b = b * a :=
  (QuotientV.isMulCommutative_V h).is_comm.comm a b

theorem quotientV_mul_self (h : Tim79a.ParrottHyp z) (a : QuotientV.V z) : a * a = 1 := by
  have := QuotientV.pow_two_eq_one_V h a
  rwa [pow_two] at this

theorem pi_mk_mul_J (a b : G) (ha : a ∈ J z) (hb : b ∈ J z) :
    QuotientV.pi z ⟨a * b, (J z).mul_mem ha hb⟩ =
      QuotientV.pi z ⟨a, ha⟩ * QuotientV.pi z ⟨b, hb⟩ :=
  map_mul (QuotientV.pi z) (⟨a, ha⟩ : J z) ⟨b, hb⟩

theorem pi_mk_inv_J (a : G) (ha : a ∈ J z) :
    QuotientV.pi z ⟨a⁻¹, (J z).inv_mem ha⟩ = (QuotientV.pi z ⟨a, ha⟩)⁻¹ :=
  map_inv (QuotientV.pi z) (⟨a, ha⟩ : J z)

theorem conjV_conjV_of_sq_mem_J (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z)
    (hxx : x * x ∈ J z) (v : QuotientV.V z) :
    conjV h ⟨x, hxH⟩ (conjV h ⟨x, hxH⟩ v) = v := by
  have hmem : (⟨x, hxH⟩ : ↥(H z)) * ⟨x, hxH⟩ ∈ (J z).subgroupOf (H z) :=
    Subgroup.mem_subgroupOf.mpr hxx
  have h1 : conjV h ((⟨x, hxH⟩ : ↥(H z)) * ⟨x, hxH⟩) = 1 :=
    MonoidHom.mem_ker.mp (J_le_ker_conjV h hmem)
  rw [map_mul] at h1
  have h2 := congrArg (fun f : MulAut (QuotientV.V z) => f v) h1
  simpa using h2

theorem conjV_inv_of_sq_mem_J (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z)
    (hxx : x * x ∈ J z) (v : QuotientV.V z) :
    conjV h ⟨x⁻¹, (H z).inv_mem hxH⟩ v = conjV h ⟨x, hxH⟩ v := by
  have h2 : conjV h ⟨x⁻¹, (H z).inv_mem hxH⟩ = (conjV h ⟨x, hxH⟩)⁻¹ := by
    have : (⟨x⁻¹, (H z).inv_mem hxH⟩ : ↥(H z)) = (⟨x, hxH⟩ : ↥(H z))⁻¹ := rfl
    rw [this, map_inv]
  rw [h2, MulAut.inv_def, MulEquiv.symm_apply_eq]
  exact (conjV_conjV_of_sq_mem_J h hxH hxx v).symm

theorem inv_conj_mem_J {x : G} (hxH : x ∈ H z) {j : G} (hj : j ∈ J z) : x⁻¹ * j * x ∈ J z := by
  simpa using H_conj_mem_J (⟨x⁻¹, (H z).inv_mem hxH⟩ : ↥(H z)) hj

theorem pi_mk_conj_inv (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z) (j : G) (hj : j ∈ J z) :
    QuotientV.pi z ⟨x⁻¹ * j * x, inv_conj_mem_J hxH hj⟩ =
      conjV h ⟨x⁻¹, (H z).inv_mem hxH⟩ (QuotientV.pi z ⟨j, hj⟩) := by
  rw [conjV_pi_conj h ⟨x⁻¹, (H z).inv_mem hxH⟩ hj]
  congr 1
  apply Subtype.ext
  simp

theorem pi_mk_conj (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z) (j : G) (hj : j ∈ J z) :
    QuotientV.pi z ⟨x * j * x⁻¹, H_conj_mem_J (⟨x, hxH⟩ : ↥(H z)) hj⟩ =
      conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨j, hj⟩) :=
  (conjV_pi_conj h ⟨x, hxH⟩ hj).symm

theorem exists_lift_sq_mem_centerIn (h : Tim79a.ParrottHyp z) (x₀ : ↥(H z))
    (hdim : fixDimV h x₀ = 4) (hxx : (x₀ : G) * x₀ ∈ J z) :
    ∃ j ∈ J z, ((x₀ : G) * j) * ((x₀ : G) * j) ∈ centerIn (J z) := by
  obtain ⟨x, hxH⟩ := x₀
  set σ : MulAut (QuotientV.V z) := conjV h ⟨x, hxH⟩ with hσ
  have hσσ : ∀ v, σ (σ v) = v := conjV_conjV_of_sq_mem_J h hxH hxx
  have hcard : Nat.card (autFixedSubgroup σ) ^ 2 = Nat.card (QuotientV.V z) := by
    rw [hσ, card_fix h ⟨x, hxH⟩, hdim, QuotientV.card_V h]
    norm_num
  have hfix : σ (QuotientV.pi z ⟨x * x, hxx⟩) = QuotientV.pi z ⟨x * x, hxx⟩ := by
    rw [hσ, ← pi_mk_conj h hxH (x * x) hxx]
    congr 1
    apply Subtype.ext
    group
  obtain ⟨u, hu⟩ := exists_mul_inv_eq_of_card_fix_sq (quotientV_mul_comm h) (quotientV_mul_self h)
    hσσ hcard _ hfix
  obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z u
  have hjJ : (j : G) ∈ J z := j.2
  have hxinvJ : x⁻¹ * (j : G) * x ∈ J z := by
    simpa using H_conj_mem_J (⟨x⁻¹, (H z).inv_mem hxH⟩ : ↥(H z)) hjJ
  have hxjJ : (x * (j : G)) * (x * (j : G)) ∈ J z := by
    have e : (x * (j : G)) * (x * (j : G)) = (x * x) * (x⁻¹ * (j : G) * x) * (j : G) := by group
    rw [e]
    exact (J z).mul_mem ((J z).mul_mem hxx hxinvJ) hjJ
  refine ⟨j, hjJ, ?_⟩
  rw [← pi_eq_one_iff_mem_centerIn hxjJ]
  have e : (x * (j : G)) * (x * (j : G)) = (x * x) * (x⁻¹ * (j : G) * x) * (j : G) := by group
  have key : QuotientV.pi z ⟨(x * (j : G)) * (x * (j : G)), hxjJ⟩ =
      QuotientV.pi z ⟨x * x, hxx⟩ * QuotientV.pi z ⟨x⁻¹ * (j : G) * x, hxinvJ⟩ *
        QuotientV.pi z ⟨(j : G), hjJ⟩ := by
    rw [← pi_mk_mul_J, ← pi_mk_mul_J]
    congr 1
    apply Subtype.ext
    exact e
  rw [key, pi_mk_conj_inv h hxH, conjV_inv_of_sq_mem_J h hxH hxx]
  have hu' : σ (QuotientV.pi z j) * (QuotientV.pi z j)⁻¹ = QuotientV.pi z ⟨x * x, hxx⟩ := hu
  have hinvj : (QuotientV.pi z j)⁻¹ = QuotientV.pi z j := by
    have := quotientV_mul_self h (QuotientV.pi z j)
    exact inv_eq_of_mul_eq_one_right this
  rw [hinvj] at hu'
  show QuotientV.pi z ⟨x * x, hxx⟩ * σ (QuotientV.pi z j) * QuotientV.pi z j = 1
  calc QuotientV.pi z ⟨x * x, hxx⟩ * σ (QuotientV.pi z j) * QuotientV.pi z j
      = QuotientV.pi z ⟨x * x, hxx⟩ * (σ (QuotientV.pi z j) * QuotientV.pi z j) := mul_assoc _ _ _
    _ = QuotientV.pi z ⟨x * x, hxx⟩ * QuotientV.pi z ⟨x * x, hxx⟩ := by rw [hu']
    _ = 1 := quotientV_mul_self h _

theorem centerIn_J_comm_H (hZ : centerIn (J z) = centerIn (H z)) {c g : G}
    (hc : c ∈ centerIn (J z)) (hg : g ∈ H z) : g * c = c * g := by
  have hc' : c ∈ centerIn (H z) := hZ ▸ hc
  exact Subgroup.mem_centralizer_iff.mp hc'.2 g hg

theorem exists_comm_mod_centerIn (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    {x g : G} (hxH : x ∈ H z) (hgH : g ∈ H z) (hxx : x * x ∈ centerIn (J z))
    (hdim : fixDimV h ⟨x, hxH⟩ = 4) (hg : x⁻¹ * (g⁻¹ * x * g) ∈ J z) :
    ∃ j ∈ J z, x⁻¹ * ((g * j)⁻¹ * x * (g * j)) ∈ centerIn (J z) := by
  have hxxJ : x * x ∈ J z := (inf_le_left : centerIn (J z) ≤ J z) hxx
  set σ : MulAut (QuotientV.V z) := conjV h ⟨x, hxH⟩ with hσ
  have hσσ : ∀ v, σ (σ v) = v := conjV_conjV_of_sq_mem_J h hxH hxxJ
  have hσinv : ∀ v, conjV h ⟨x⁻¹, (H z).inv_mem hxH⟩ v = σ v := conjV_inv_of_sq_mem_J h hxH hxxJ
  have hcard : Nat.card (autFixedSubgroup σ) ^ 2 = Nat.card (QuotientV.V z) := by
    rw [hσ, card_fix h ⟨x, hxH⟩, hdim, QuotientV.card_V h]
    norm_num
  set u : G := x⁻¹ * (g⁻¹ * x * g) with hu_def
  have hgxg : g⁻¹ * x * g = x * u := by rw [hu_def]; group
  have hx2g : g * (x * x) = (x * x) * g := centerIn_J_comm_H hZ hxx hgH
  have hxu2 : (x * u) * (x * u) = x * x := by
    rw [← hgxg]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = g⁻¹ * ((x * x) * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * (x * x)) := by rw [hx2g]
      _ = x * x := by group
  have hxux : x⁻¹ * u * x = u⁻¹ := by
    have h1 : u * x * u = x := by
      have : x * (u * x * u) = x * x := by
        calc x * (u * x * u) = (x * u) * (x * u) := by group
          _ = x * x := hxu2
      exact mul_left_cancel this
    calc x⁻¹ * u * x = x⁻¹ * (u * x * u) * u⁻¹ := by group
      _ = x⁻¹ * x * u⁻¹ := by rw [h1]
      _ = u⁻¹ := by group
  have huJ : u ∈ J z := hg
  have hfix : σ (QuotientV.pi z ⟨u, huJ⟩) = QuotientV.pi z ⟨u, huJ⟩ := by
    have h1 := pi_mk_conj_inv h hxH u huJ
    rw [hσinv] at h1
    rw [← h1]
    have e : QuotientV.pi z ⟨x⁻¹ * u * x, inv_conj_mem_J hxH huJ⟩ =
        QuotientV.pi z ⟨u⁻¹, (J z).inv_mem huJ⟩ := by
      congr 1
      apply Subtype.ext
      exact hxux
    rw [e, pi_mk_inv_J u huJ]
    exact inv_eq_of_mul_eq_one_right (quotientV_mul_self h _)
  obtain ⟨w, hw⟩ := exists_mul_inv_eq_of_card_fix_sq (quotientV_mul_comm h) (quotientV_mul_self h)
    hσσ hcard _ hfix
  obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z w
  have hjJ : (j : G) ∈ J z := j.2
  refine ⟨j, hjJ, ?_⟩
  have hjinvJ : (j : G)⁻¹ ∈ J z := (J z).inv_mem hjJ
  have hxinvJ : x⁻¹ * (j : G)⁻¹ * x ∈ J z := inv_conj_mem_J hxH hjinvJ
  have hgJ : x⁻¹ * ((g * (j : G))⁻¹ * x * (g * (j : G))) =
      (x⁻¹ * (j : G)⁻¹ * x) * u * (j : G) := by
    rw [hu_def]; group
  have hmemJ : (x⁻¹ * (j : G)⁻¹ * x) * u * (j : G) ∈ J z :=
    (J z).mul_mem ((J z).mul_mem hxinvJ huJ) hjJ
  rw [hgJ, ← pi_eq_one_iff_mem_centerIn hmemJ]
  have key : QuotientV.pi z ⟨(x⁻¹ * (j : G)⁻¹ * x) * u * (j : G), hmemJ⟩ =
      QuotientV.pi z ⟨x⁻¹ * (j : G)⁻¹ * x, hxinvJ⟩ * QuotientV.pi z ⟨u, huJ⟩ *
        QuotientV.pi z j := by
    rw [← pi_mk_mul_J, ← pi_mk_mul_J]
  have hcj : QuotientV.pi z ⟨x⁻¹ * (j : G)⁻¹ * x, hxinvJ⟩ = (σ (QuotientV.pi z j))⁻¹ := by
    have h1 := pi_mk_conj_inv h hxH ((j : G)⁻¹) hjinvJ
    rw [h1, hσinv, pi_mk_inv_J (j : G) hjJ, map_inv]
  have hw' : σ (QuotientV.pi z j) * (QuotientV.pi z j)⁻¹ = QuotientV.pi z ⟨u, huJ⟩ := hw
  rw [key, hcj, ← hw', inv_mul_cancel_left, inv_mul_cancel]

theorem commutatorElement_mul_mul_of_commute {a b c₁ c₂ : G} (h1a : Commute c₁ a)
    (h1b : Commute c₁ b)
    (h2a : Commute c₂ a) (h2b : Commute c₂ b) (h12 : Commute c₁ c₂) :
    ⁅a * c₁, b * c₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : c₁ * b = b * c₁ := h1b.eq
  have e2 : c₁ * c₂ = c₂ * c₁ := h12.eq
  have e3 : c₂ * a⁻¹ = a⁻¹ * c₂ := (h2a.inv_right).eq
  calc a * c₁ * (b * c₂) * (a * c₁)⁻¹ * (b * c₂)⁻¹
      = a * (c₁ * b) * c₂ * c₁⁻¹ * a⁻¹ * c₂⁻¹ * b⁻¹ := by group
    _ = a * (b * c₁) * c₂ * c₁⁻¹ * a⁻¹ * c₂⁻¹ * b⁻¹ := by rw [e1]
    _ = a * b * (c₁ * c₂) * c₁⁻¹ * a⁻¹ * c₂⁻¹ * b⁻¹ := by group
    _ = a * b * (c₂ * c₁) * c₁⁻¹ * a⁻¹ * c₂⁻¹ * b⁻¹ := by rw [e2]
    _ = a * b * c₂ * a⁻¹ * c₂⁻¹ * b⁻¹ := by group
    _ = a * b * (c₂ * a⁻¹) * c₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * c₂) * c₂⁻¹ * b⁻¹ := by rw [e3]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem inv_mul_mul_of_comm_mod {x g c : G} (e : x⁻¹ * (g⁻¹ * x * g) = c) :
    x⁻¹ * g * x = g * c⁻¹ := by
  have h1 : g⁻¹ * x * g = x * c := by rw [← e]; group
  have h2 : x * g = g * x * c := by
    calc x * g = g * (g⁻¹ * x * g) := by group
      _ = g * (x * c) := by rw [h1]
      _ = g * x * c := by group
  calc x⁻¹ * g * x = x⁻¹ * (g * x * c) * c⁻¹ := by group
    _ = x⁻¹ * (x * g) * c⁻¹ := by rw [← h2]
    _ = g * c⁻¹ := by group

theorem mul_comm_commutator_of_comm_mod_centerIn (hZ : centerIn (J z) = centerIn (H z))
    {x g₁ g₂ c₁ c₂ : G} (hg₁H : g₁ ∈ H z) (hg₂H : g₂ ∈ H z)
    (hc₁ : c₁ ∈ centerIn (J z)) (hc₂ : c₂ ∈ centerIn (J z))
    (e₁ : x⁻¹ * (g₁⁻¹ * x * g₁) = c₁) (e₂ : x⁻¹ * (g₂⁻¹ * x * g₂) = c₂) :
    x * ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆ * x := by
  have c₁H : c₁ ∈ H z := J_le_H ((inf_le_left : centerIn (J z) ≤ J z) hc₁)
  have c₂H : c₂ ∈ H z := J_le_H ((inf_le_left : centerIn (J z) ≤ J z) hc₂)
  have k1 := inv_mul_mul_of_comm_mod e₁
  have k2 := inv_mul_mul_of_comm_mod e₂
  have a1 : Commute g₁ c₁ := centerIn_J_comm_H hZ hc₁ hg₁H
  have a2 : Commute g₂ c₂ := centerIn_J_comm_H hZ hc₂ hg₂H
  have b1 : Commute g₂ c₁ := centerIn_J_comm_H hZ hc₁ hg₂H
  have b2 : Commute g₁ c₂ := centerIn_J_comm_H hZ hc₂ hg₁H
  have d12 : Commute c₁ c₂ := (centerIn_J_comm_H hZ hc₁ c₂H).symm
  have hconj : x⁻¹ * ⁅g₁, g₂⁆ * x = ⁅x⁻¹ * g₁ * x, x⁻¹ * g₂ * x⁆ := by
    simp only [commutatorElement_def]; group
  have hcc : x⁻¹ * ⁅g₁, g₂⁆ * x = ⁅g₁, g₂⁆ := by
    rw [hconj, k1, k2]
    exact commutatorElement_mul_mul_of_commute a1.inv_right.symm b1.inv_right.symm b2.inv_right.symm
      a2.inv_right.symm d12.inv_inv
  have : ⁅g₁, g₂⁆ * x = x * ⁅g₁, g₂⁆ := by
    calc ⁅g₁, g₂⁆ * x = x * (x⁻¹ * ⁅g₁, g₂⁆ * x) := by group
      _ = x * ⁅g₁, g₂⁆ := by rw [hcc]
  exact this.symm

theorem mul_self_eq_one_of_qVZMod_eq_zero (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    (hq : qVZMod h (QuotientV.pi z ⟨j, hj⟩) = 0) : j * j = 1 := by
  have h1 := (qVZMod_eq_zero_iff h _).mp hq
  have h2 : ((qV h (QuotientV.pi z ⟨j, hj⟩) : Subgroup.zpowers z) : G) = j ^ 2 :=
    qV_pi_coe h ⟨j, hj⟩
  rw [h1] at h2
  have h3 : ((1 : Subgroup.zpowers z) : G) = 1 := rfl
  rw [h3] at h2
  rw [← pow_two]
  exact h2.symm

theorem exists_commuting_lift_sq_mem_centerIn (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {x y₂ : G} (hxH : x ∈ H z) (hy₂H : y₂ ∈ H z)
    (hxx : x * x ∈ centerIn (J z)) (hdim : fixDimV h ⟨x, hxH⟩ = 4)
    (hq0 : ∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v → qVZMod h v = 0)
    (hcomm : x * y₂ = y₂ * x) (hsJ : y₂ * y₂ ∈ J z)
    (hfree : ∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v → conjV h ⟨y₂, hy₂H⟩ v = v →
      ∃ w : QuotientV.V z, conjV h ⟨x, hxH⟩ w = w ∧ conjV h ⟨y₂, hy₂H⟩ w * w⁻¹ = v) :
    ∃ j ∈ J z, x * (y₂ * j) = (y₂ * j) * x ∧ (y₂ * j) * (y₂ * j) ∈ centerIn (J z) := by
  have hxxJ : x * x ∈ J z := (inf_le_left : centerIn (J z) ≤ J z) hxx
  set σ : MulAut (QuotientV.V z) := conjV h ⟨x, hxH⟩ with hσ
  set τ : MulAut (QuotientV.V z) := conjV h ⟨y₂, hy₂H⟩ with hτ
  have hσσ : ∀ v, σ (σ v) = v := conjV_conjV_of_sq_mem_J h hxH hxxJ
  have hτinv : ∀ v, conjV h ⟨y₂⁻¹, (H z).inv_mem hy₂H⟩ v = τ v := conjV_inv_of_sq_mem_J h hy₂H hsJ
  have hcard : Nat.card (autFixedSubgroup σ) ^ 2 = Nat.card (QuotientV.V z) := by
    rw [hσ, card_fix h ⟨x, hxH⟩, hdim, QuotientV.card_V h]
    norm_num
  have hsσ : σ (QuotientV.pi z ⟨y₂ * y₂, hsJ⟩) = QuotientV.pi z ⟨y₂ * y₂, hsJ⟩ :=
    mem_autFixedSubgroup.mp (pi_mem_autFixedSubgroup_conjV h hsJ (x := ⟨x, hxH⟩) (by
      show x * (y₂ * y₂) = (y₂ * y₂) * x
      rw [← mul_assoc, hcomm, mul_assoc, hcomm, ← mul_assoc]))
  have hsτ : τ (QuotientV.pi z ⟨y₂ * y₂, hsJ⟩) = QuotientV.pi z ⟨y₂ * y₂, hsJ⟩ :=
    mem_autFixedSubgroup.mp (pi_mem_autFixedSubgroup_conjV h hsJ (x := ⟨y₂, hy₂H⟩) (by
      show y₂ * (y₂ * y₂) = (y₂ * y₂) * y₂
      exact (mul_assoc _ _ _).symm))
  obtain ⟨w, hwσ, hwτ⟩ := hfree _ hsσ hsτ
  obtain ⟨k, hk⟩ := exists_mul_inv_eq_of_card_fix_sq (quotientV_mul_comm h) (quotientV_mul_self h)
    hσσ hcard w hwσ
  obtain ⟨k₀, rfl⟩ := QuotientV.pi_surjective z k
  have hk₀J : (k₀ : G) ∈ J z := k₀.2
  have hk₀H : (k₀ : G) ∈ H z := J_le_H hk₀J
  set j : G := x * (k₀ : G) * x⁻¹ * (k₀ : G)⁻¹ with hj_def
  have hjJ : j ∈ J z := by
    have h1 : x * (k₀ : G) * x⁻¹ ∈ J z := H_conj_mem_J (⟨x, hxH⟩ : ↥(H z)) hk₀J
    exact (J z).mul_mem h1 ((J z).inv_mem hk₀J)
  have hpij : QuotientV.pi z ⟨j, hjJ⟩ = w := by
    rw [← hk]
    have h1 : x * (k₀ : G) * x⁻¹ ∈ J z := H_conj_mem_J (⟨x, hxH⟩ : ↥(H z)) hk₀J
    have e : QuotientV.pi z ⟨j, hjJ⟩ =
        QuotientV.pi z ⟨x * (k₀ : G) * x⁻¹, h1⟩ * QuotientV.pi z ⟨(k₀ : G)⁻¹, (J z).inv_mem hk₀J⟩ :=
      (pi_mk_mul_J _ _ h1 ((J z).inv_mem hk₀J)).symm.symm ▸ rfl
    rw [e, pi_mk_inv_J (k₀ : G) hk₀J, pi_mk_conj h hxH (k₀ : G) hk₀J]
  have hx2k : (x * x) * (k₀ : G) = (k₀ : G) * (x * x) := (centerIn_J_comm_H hZ hxx hk₀H).symm
  have hxjx : x * j * x⁻¹ = j⁻¹ := by
    rw [hj_def]
    calc x * (x * (k₀ : G) * x⁻¹ * (k₀ : G)⁻¹) * x⁻¹
        = ((x * x) * (k₀ : G)) * x⁻¹ * (k₀ : G)⁻¹ * x⁻¹ := by group
      _ = ((k₀ : G) * (x * x)) * x⁻¹ * (k₀ : G)⁻¹ * x⁻¹ := by rw [hx2k]
      _ = (x * (k₀ : G) * x⁻¹ * (k₀ : G)⁻¹)⁻¹ := by group
  have hjq : qVZMod h (QuotientV.pi z ⟨j, hjJ⟩) = 0 := by
    rw [hpij]
    exact hq0 w hwσ
  have hjj : j * j = 1 := mul_self_eq_one_of_qVZMod_eq_zero h hjJ hjq
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hjj
  have hxj : x * j = j * x := by
    have h1 : x * j * x⁻¹ = j := by rw [hxjx, hjinv]
    calc x * j = (x * j * x⁻¹) * x := by group
      _ = j * x := by rw [h1]
  refine ⟨j, hjJ, ?_, ?_⟩
  · calc x * (y₂ * j) = (x * y₂) * j := (mul_assoc x y₂ j).symm
      _ = (y₂ * x) * j := by rw [hcomm]
      _ = y₂ * (x * j) := mul_assoc y₂ x j
      _ = y₂ * (j * x) := by rw [hxj]
      _ = (y₂ * j) * x := (mul_assoc y₂ j x).symm
  ·
    have hy₂invJ : y₂⁻¹ * j * y₂ ∈ J z := inv_conj_mem_J hy₂H hjJ
    have hyyJ : (y₂ * j) * (y₂ * j) ∈ J z := by
      have e : (y₂ * j) * (y₂ * j) = (y₂ * y₂) * (y₂⁻¹ * j * y₂) * j := by group
      rw [e]
      exact (J z).mul_mem ((J z).mul_mem hsJ hy₂invJ) hjJ
    refine (pi_eq_one_iff_mem_centerIn hyyJ).mp ?_
    have key : QuotientV.pi z ⟨(y₂ * j) * (y₂ * j), hyyJ⟩ =
        QuotientV.pi z ⟨y₂ * y₂, hsJ⟩ * QuotientV.pi z ⟨y₂⁻¹ * j * y₂, hy₂invJ⟩ *
          QuotientV.pi z ⟨j, hjJ⟩ := by
      rw [← pi_mk_mul_J, ← pi_mk_mul_J]
      congr 1
      apply Subtype.ext
      group
    have hcj : QuotientV.pi z ⟨y₂⁻¹ * j * y₂, hy₂invJ⟩ = τ w := by
      rw [pi_mk_conj_inv h hy₂H j hjJ, hτinv, hpij]
    rw [key, hcj, hpij]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (quotientV_mul_self h w)
    rw [hwinv] at hwτ
    calc QuotientV.pi z ⟨y₂ * y₂, hsJ⟩ * τ w * w
        = QuotientV.pi z ⟨y₂ * y₂, hsJ⟩ * (τ w * w) := mul_assoc _ _ _
      _ = QuotientV.pi z ⟨y₂ * y₂, hsJ⟩ * QuotientV.pi z ⟨y₂ * y₂, hsJ⟩ := by rw [hwτ]
      _ = 1 := quotientV_mul_self h _

theorem inv_mul_mul_mem_J_of_commutator_mem_J {x g : G} (hxH : x ∈ H z) (hgH : g ∈ H z)
    (hg : ⁅x, g⁆ ∈ J z) : x⁻¹ * (g⁻¹ * x * g) ∈ J z := by
  have hgx : g * x ∈ H z := (H z).mul_mem hgH hxH
  have h1 := inv_conj_mem_J hgx hg
  have e : (g * x)⁻¹ * ⁅x, g⁆ * (g * x) = x⁻¹ * (g⁻¹ * x * g) := by
    rw [commutatorElement_def]; group
  rwa [e] at h1

theorem exists_commuting_lift_of_derived (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (x g₁ g₂ : ↥(H z)) (hdim : fixDimV h x = 4)
    (hxx : (x : G) * x ∈ centerIn (J z))
    (hq0 : ∀ v : QuotientV.V z, conjV h x v = v → qVZMod h v = 0)
    (hg₁ : ⁅(x : G), (g₁ : G)⁆ ∈ J z) (hg₂ : ⁅(x : G), (g₂ : G)⁆ ∈ J z)
    (hb2 : (((⁅g₁, g₂⁆ : ↥(H z)) : G) * ((⁅g₁, g₂⁆ : ↥(H z)) : G)) ∈ J z)
    (hfree : ∀ y' : ↥(H z), ((⁅g₁, g₂⁆ : ↥(H z))⁻¹ * y' : ↥(H z)) ∈ (J z).subgroupOf (H z) →
      ∀ v : QuotientV.V z, conjV h x v = v → conjV h y' v = v →
        ∃ w : QuotientV.V z, conjV h x w = w ∧ conjV h y' w * w⁻¹ = v) :
    ∃ y : ↥(H z), ((⁅g₁, g₂⁆ : ↥(H z))⁻¹ * y : ↥(H z)) ∈ (J z).subgroupOf (H z) ∧
      (y : G) * y ∈ centerIn (J z) ∧ (x : G) * y = y * x := by
  obtain ⟨x, hxH⟩ := x
  obtain ⟨g₁, hg₁H⟩ := g₁
  obtain ⟨g₂, hg₂H⟩ := g₂
  simp only at hdim hxx hg₁ hg₂ hb2 hq0 hfree
  obtain ⟨j₁, hj₁J, hc₁⟩ := exists_comm_mod_centerIn h hZ hxH hg₁H hxx hdim
    (inv_mul_mul_mem_J_of_commutator_mem_J hxH hg₁H hg₁)
  obtain ⟨j₂, hj₂J, hc₂⟩ := exists_comm_mod_centerIn h hZ hxH hg₂H hxx hdim
    (inv_mul_mul_mem_J_of_commutator_mem_J hxH hg₂H hg₂)
  set g₁' : G := g₁ * j₁ with hg₁'
  set g₂' : G := g₂ * j₂ with hg₂'
  have hg₁'H : g₁' ∈ H z := (H z).mul_mem hg₁H (J_le_H hj₁J)
  have hg₂'H : g₂' ∈ H z := (H z).mul_mem hg₂H (J_le_H hj₂J)
  set y₂ : G := ⁅g₁', g₂'⁆ with hy₂
  have hy₂H : y₂ ∈ H z := by
    rw [hy₂, commutatorElement_def]
    exact (H z).mul_mem ((H z).mul_mem ((H z).mul_mem hg₁'H hg₂'H) ((H z).inv_mem hg₁'H))
      ((H z).inv_mem hg₂'H)
  have hcomm : x * y₂ = y₂ * x :=
    mul_comm_commutator_of_comm_mod_centerIn hZ hg₁'H hg₂'H hc₁ hc₂ rfl rfl
  have hmk : QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨y₂, hy₂H⟩ : ↥(H z)) =
      QuotientGroup.mk' ((J z).subgroupOf (H z)) (⁅(⟨g₁, hg₁H⟩ : ↥(H z)), ⟨g₂, hg₂H⟩⁆) := by
    have e₁ : QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨g₁', hg₁'H⟩ : ↥(H z)) =
        QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨g₁, hg₁H⟩ : ↥(H z)) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show (g₁ * j₁)⁻¹ * g₁ ∈ J z
      simpa using (J z).inv_mem hj₁J
    have e₂ : QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨g₂', hg₂'H⟩ : ↥(H z)) =
        QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨g₂, hg₂H⟩ : ↥(H z)) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show (g₂ * j₂)⁻¹ * g₂ ∈ J z
      simpa using (J z).inv_mem hj₂J
    have e₃ : (⟨y₂, hy₂H⟩ : ↥(H z)) = ⁅(⟨g₁', hg₁'H⟩ : ↥(H z)), ⟨g₂', hg₂'H⟩⁆ := rfl
    rw [e₃, map_commutatorElement, map_commutatorElement, e₁, e₂]
  have hbmem : (⁅(⟨g₁, hg₁H⟩ : ↥(H z)), ⟨g₂, hg₂H⟩⁆)⁻¹ * ⟨y₂, hy₂H⟩ ∈ (J z).subgroupOf (H z) := by
    have h1 := hmk.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h1
    exact QuotientGroup.eq.mp h1
  have hy₂sq : y₂ * y₂ ∈ J z := by
    have hbb : (⁅(⟨g₁, hg₁H⟩ : ↥(H z)), ⟨g₂, hg₂H⟩⁆ * ⁅(⟨g₁, hg₁H⟩ : ↥(H z)), ⟨g₂, hg₂H⟩⁆) ∈
        (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr hb2
    have h1 : QuotientGroup.mk' ((J z).subgroupOf (H z))
        ((⟨y₂, hy₂H⟩ : ↥(H z)) * ⟨y₂, hy₂H⟩) = 1 := by
      rw [map_mul, hmk, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hbb
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hfree' := hfree ⟨y₂, hy₂H⟩ hbmem
  obtain ⟨j, hjJ, hxy, hyy⟩ :=
    exists_commuting_lift_sq_mem_centerIn h hZ hxH hy₂H hxx hdim hq0 hcomm
    hy₂sq hfree'
  refine ⟨⟨y₂ * j, (H z).mul_mem hy₂H (J_le_H hjJ)⟩, ?_, hyy, hxy⟩
  have : (⟨j, J_le_H hjJ⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr hjJ
  have e : (⟨y₂ * j, (H z).mul_mem hy₂H (J_le_H hjJ)⟩ : ↥(H z)) =
      ⟨y₂, hy₂H⟩ * ⟨j, J_le_H hjJ⟩ := rfl
  rw [e, ← mul_assoc]
  exact ((J z).subgroupOf (H z)).mul_mem hbmem this

end CFSG.RankThree.GF2n.Parrott
