module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSInv

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixCoxAux

variable {G : Type} [Group G]

theorem class_conj {x r t g : G} (hgr : g * r * g⁻¹ = r)
    (hcl : ∀ z : G, (∃ k ∈ CGOf x, z = k * r * k⁻¹) ↔ z = r ∨ z = t ∨ z = t * (x * r))
    (z : G) :
    (∃ k ∈ CGOf (g * x * g⁻¹), z = k * r * k⁻¹) ↔
      z = r ∨ z = g * t * g⁻¹ ∨ z = g * t * g⁻¹ * (g * x * g⁻¹ * r) := by
  have hgr' : g⁻¹ * r * g = r := by
    calc g⁻¹ * r * g = g⁻¹ * (g * r * g⁻¹) * g := by rw [hgr]
      _ = r := by group
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk1 : k * (g * x * g⁻¹) * k⁻¹ = g * x * g⁻¹ := mem_centralizer_zpowers_iff.1 hk
    have hk' : g⁻¹ * k * g ∈ CGOf x := by
      refine mem_centralizer_zpowers_iff.2 ?_
      calc g⁻¹ * k * g * x * (g⁻¹ * k * g)⁻¹ = g⁻¹ * (k * (g * x * g⁻¹) * k⁻¹) * g := by group
        _ = x := by rw [hk1]; group
    have hz : g⁻¹ * (k * r * k⁻¹) * g = (g⁻¹ * k * g) * r * (g⁻¹ * k * g)⁻¹ := by
      calc g⁻¹ * (k * r * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * r * g) * (g⁻¹ * k * g)⁻¹ := by
            group
        _ = _ := by rw [hgr']
    have e : k * r * k⁻¹ = g * (g⁻¹ * (k * r * k⁻¹) * g) * g⁻¹ := by group
    rcases (hcl _).1 ⟨_, hk', hz⟩ with h | h | h
    · left
      rw [e, h, hgr]
    · right; left
      rw [e, h]
    · right; right
      rw [e, h]
      calc g * (t * (x * r)) * g⁻¹ = g * t * g⁻¹ * (g * x * g⁻¹ * (g * r * g⁻¹)) := by group
        _ = _ := by rw [hgr]
  · intro hz
    have hz' : g⁻¹ * z * g = r ∨ g⁻¹ * z * g = t ∨ g⁻¹ * z * g = t * (x * r) := by
      rcases hz with rfl | rfl | rfl
      · exact Or.inl hgr'
      · exact Or.inr (Or.inl (by group))
      · refine Or.inr (Or.inr ?_)
        calc g⁻¹ * (g * t * g⁻¹ * (g * x * g⁻¹ * r)) * g = t * (x * (g⁻¹ * r * g)) := by group
          _ = t * (x * r) := by rw [hgr']
    obtain ⟨k, hk, hke⟩ := (hcl _).2 hz'
    have hk1 : k * x * k⁻¹ = x := mem_centralizer_zpowers_iff.1 hk
    refine ⟨g * k * g⁻¹, mem_centralizer_zpowers_iff.2 ?_, ?_⟩
    · calc g * k * g⁻¹ * (g * x * g⁻¹) * (g * k * g⁻¹)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hk1]
    · calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = g * (k * r * k⁻¹) * g⁻¹ := by rw [hke]
        _ = (g * k * g⁻¹) * (g * r * g⁻¹) * (g * k * g⁻¹)⁻¹ := by group
        _ = _ := by rw [hgr]

theorem conj_mul_conj {g t : G} (ht : t * t = 1) : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [ht]; group

theorem conj_mul_lift {M : Subgroup G} {t : ↥M} (htt : (t : G) * t = 1) (m m' : ↥M) :
    ((m * t * m⁻¹ * m' : ↥M) : G) * t * ((m * t * m⁻¹ * m' : ↥M) : G)⁻¹ =
      ((m * t * m⁻¹ * (m' * t * m'⁻¹) * (m * t * m⁻¹) : ↥M) : G) := by
  have hsi : (m * t * m⁻¹)⁻¹ = m * t * m⁻¹ :=
    inv_eq_of_mul_eq_one_right (conj_mul_conj (Subtype.ext htt))
  calc _ = ((m * t * m⁻¹ * (m' * t * m'⁻¹) * (m * t * m⁻¹)⁻¹ : ↥M) : G) := by
        push_cast
        group
    _ = _ := by rw [hsi]

theorem comm_of_conj {s s' : G} (hs : s * s = 1) (h : s * s' * s = s') : s * s' = s' * s := by
  calc s * s' = s * s' * (s * s) := by rw [hs, mul_one]
    _ = (s * s' * s) * s := by group
    _ = s' * s := by rw [h]

theorem comm_core {s s' w w' : G} (hs : s * s = 1) (hs' : s' * s' = 1)
    (h : s * s' * s = s' * w') (h' : s' * s * s' = s * w) : w' = w⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'
  have e1 : w' = s' * s * s' * s := by
    calc w' = s'⁻¹ * (s' * w') := by group
      _ = s'⁻¹ * (s * s' * s) := by rw [h]
      _ = s' * s * s' * s := by rw [hs'i]; group
  have e2 : w = s * s' * s * s' := by
    calc w = s⁻¹ * (s * w) := by group
      _ = s⁻¹ * (s' * s * s') := by rw [h']
      _ = s * s' * s * s' := by rw [hsi]; group
  rw [e1, e2]
  simp only [mul_inv_rev, hsi, hs'i, mul_assoc]

theorem braid_core {s s' y r : G} (hs : s * s = 1) (hs' : s' * s' = 1) (hsr : s * r * s = r)
    (h : s' * s * s' = s * s' * s * (s * y * s * r)) : y * r = (s * y * s * r)⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'
  have hsl : ∀ z : G, s * (s * z) = z := fun z => by rw [← mul_assoc, hs, one_mul]
  have hs'l : ∀ z : G, s' * (s' * z) = z := fun z => by rw [← mul_assoc, hs', one_mul]
  set w := s * y * s * r with hw
  have e : w = s * s' * s * s' * s * s' := by
    calc w = (s * s' * s)⁻¹ * (s * s' * s * w) := by group
      _ = (s * s' * s)⁻¹ * (s' * s * s') := by rw [h]
      _ = s * s' * s * s' * s * s' := by simp only [mul_inv_rev, hsi, hs'i, mul_assoc]
  have e2 : y * r = s * w * s := by
    calc y * r = (s * s) * y * (s * r * s) := by rw [hs, hsr, one_mul]
      _ = s * w * s := by rw [hw]; group
  rw [e2, e]
  simp only [mul_inv_rev, hsi, hs'i, mul_assoc, hsl, hs'l, hs, hs']

end SixCoxAux

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem sixCox_conj_eq (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) {m m' : ↥M}
    (hmm : ({C.θ m i, C.θ m j} : Finset (Fin 6)) = {C.θ m' i, C.θ m' j}) :
    (m : G) * x * (m : G)⁻¹ = (m' : G) * x * (m' : G)⁻¹ := by
  have hθ : C.θ (m⁻¹ * m') ∈ setStab ({i, j} : Finset (Fin 6)) := by
    rw [← image_eq_iff_mem_setStab, map_mul, map_inv, Perm.coe_mul, ← Finset.image_image,
      Finset.image_insert, Finset.image_singleton, ← hmm, Finset.image_insert,
      Finset.image_singleton, perm_inv_apply_self, perm_inv_apply_self]
  have hk : ((m⁻¹ * m' : ↥M) : G) ∈ CMOf M x := by
    rw [D.CMOf_eq_thetaPre hR hsurj hx hij hπ]
    exact C.mem_thetaPre.2 ⟨(m⁻¹ * m').2, hθ⟩
  have hc : ((m⁻¹ * m' : ↥M) : G) * x * ((m⁻¹ * m' : ↥M) : G)⁻¹ = x :=
    mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  calc (m : G) * x * (m : G)⁻¹
      = m * ((m : G)⁻¹ * m' * x * ((m : G)⁻¹ * m')⁻¹) * (m : G)⁻¹ := by rw [hc]
    _ = (m' : G) * x * (m' : G)⁻¹ := by group

theorem sixCox_theta_conj {i j : Fin 6} (m t : ↥M) (ht : C.θ t = swap i j) :
    C.θ (m * t * m⁻¹) = swap (C.θ m i) (C.θ m j) := by
  rw [map_mul, map_mul, map_inv, ht, swap_apply_apply]

theorem sixCox_piQ_conj {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6}
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) {r : G} (hr : r ∈ Rc X) (n : ↥M)
    (h : (n : G) * x * (n : G)⁻¹ * r ∈ CFSG.Open.pCoreOf 2 M) :
    Multiplicative.toAdd (D.piQ ⟨(n : G) * x * (n : G)⁻¹ * r, h⟩) =
      barInd {C.θ n i, C.θ n j} := by
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    rw [C.S.R_eq_inf] at hr
    exact hr.1
  have hy : (n : G) * x * (n : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M n.2 hx
  have e : (⟨(n : G) * x * (n : G)⁻¹ * r, h⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
      ⟨(n : G) * x * (n : G)⁻¹, hy⟩ * ⟨r, hrQ⟩ := rfl
  rw [e, map_mul, (D.piQ_eq_one_iff ⟨r, hrQ⟩).2 hr, mul_one, D.piQ_conj n ⟨x, hx⟩ ⟨_, hy⟩ rfl, hπ,
    barAct_barInd, Finset.image_insert, Finset.image_singleton]

theorem sixCox_pair_eq_of_inv {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6}
    (hij : i ≠ j) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) {r : G}
    (hr : r ∈ Rc X) {n n' : ↥M}
    (h : (n' : G) * x * (n' : G)⁻¹ * r = ((n : G) * x * (n : G)⁻¹ * r)⁻¹) :
    ({C.θ n i, C.θ n j} : Finset (Fin 6)) = {C.θ n' i, C.θ n' j} := by
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    rw [C.S.R_eq_inf] at hr
    exact hr.1
  have hw : (n : G) * x * (n : G)⁻¹ * r ∈ CFSG.Open.pCoreOf 2 M :=
    (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M n.2 hx) hrQ
  have hw' : (n' : G) * x * (n' : G)⁻¹ * r ∈ CFSG.Open.pCoreOf 2 M :=
    (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M n'.2 hx) hrQ
  have e : (⟨_, hw'⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = (⟨_, hw⟩ : ↥(CFSG.Open.pCoreOf 2 M))⁻¹ :=
    Subtype.ext h
  have h1 := congrArg (fun q => Multiplicative.toAdd (D.piQ q)) e
  simp only [map_inv, toAdd_inv, permBar_neg_eq] at h1
  rw [D.sixCox_piQ_conj hx hπ hr n' hw', D.sixCox_piQ_conj hx hπ hr n hw] at h1
  have hne : ∀ m : ↥M, C.θ m i ≠ C.θ m j := fun m hm => hij ((C.θ m).injective hm)
  exact (eq_of_barInd_eq (by rw [Finset.card_pair (hne n')]; norm_num)
    (by rw [Finset.card_pair (hne n), Finset.card_pair (hne n')]) h1).symm

theorem sixCox_same_pair (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) {r : G} (hr : r ∈ Rc X)
    {t : ↥M} (ht : C.θ t = swap i j)
    (hcl : ∀ z : G, (∃ k ∈ CGOf x, z = k * r * k⁻¹) ↔ z = r ∨ z = t ∨ z = t * (x * r))
    {n n' : ↥M} (hnn : ({C.θ n i, C.θ n j} : Finset (Fin 6)) = {C.θ n' i, C.θ n' j}) :
    (n' : G) * t * (n' : G)⁻¹ = (n : G) * t * (n : G)⁻¹ ∨
      (n' : G) * t * (n' : G)⁻¹ = (n : G) * t * (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹ * r) := by
  have hy : (n : G) * x * (n : G)⁻¹ = (n' : G) * x * (n' : G)⁻¹ :=
    D.sixCox_conj_eq hR hsurj hx hij hπ hnn
  have h1 := (SixCoxAux.class_conj (C.R_central hR n' n'.2 r hr) hcl
    ((n' : G) * t * (n' : G)⁻¹)).2 (Or.inr (Or.inl rfl))
  rw [← hy] at h1
  rcases (SixCoxAux.class_conj (C.R_central hR n n.2 r hr) hcl _).1 h1 with h2 | h2 | h2
  · exfalso
    have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
      rw [C.S.R_eq_inf] at hr
      exact hr.1
    have e : n' * t * n'⁻¹ = (⟨r, pCoreOf_le_self M hrQ⟩ : ↥M) := Subtype.ext h2
    have h3 : C.θ (n' * t * n'⁻¹) = 1 := by
      rw [e, ← MonoidHom.mem_ker, C.theta_ker_eq hR]
      exact hrQ
    rw [sixCox_theta_conj n' t ht, swap_eq_one_iff] at h3
    exact hij ((C.θ n').injective h3)
  · exact Or.inl h2
  · exact Or.inr h2

theorem sixCox_comm (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) {r : G} (hr : r ∈ Rc X)
    {t : ↥M} (htt : (t : G) * t = 1) (ht : C.θ t = swap i j)
    (hcl : ∀ z : G, (∃ k ∈ CGOf x, z = k * r * k⁻¹) ↔ z = r ∨ z = t ∨ z = t * (x * r))
    {m m' : ↥M} {a b c d : Fin 6} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hma : C.θ m i = a) (hmb : C.θ m j = b) (hm'c : C.θ m' i = c) (hm'd : C.θ m' j = d) :
    m * t * m⁻¹ * (m' * t * m'⁻¹) = m' * t * m'⁻¹ * (m * t * m⁻¹) := by
  have hθs : C.θ (m * t * m⁻¹) = swap a b := by rw [sixCox_theta_conj m t ht, hma, hmb]
  have hθs' : C.θ (m' * t * m'⁻¹) = swap c d := by rw [sixCox_theta_conj m' t ht, hm'c, hm'd]
  have h1 := D.sixCox_same_pair hR hsurj hx hij hπ hr ht hcl (n := m')
    (n' := m * t * m⁻¹ * m') (by
      rw [map_mul, Perm.mul_apply, Perm.mul_apply, hθs, hm'c, hm'd,
        swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_of_ne_of_ne had.symm hbd.symm])
  have h2 := D.sixCox_same_pair hR hsurj hx hij hπ hr ht hcl (n := m)
    (n' := m' * t * m'⁻¹ * m) (by
      rw [map_mul, Perm.mul_apply, Perm.mul_apply, hθs', hma, hmb,
        swap_apply_of_ne_of_ne hac had, swap_apply_of_ne_of_ne hbc hbd])
  have htt' : t * t = 1 := Subtype.ext htt
  have hss : (m * t * m⁻¹) * (m * t * m⁻¹) = 1 := SixCoxAux.conj_mul_conj htt'
  have hss' : (m' * t * m'⁻¹) * (m' * t * m'⁻¹) = 1 := SixCoxAux.conj_mul_conj htt'
  rw [SixCoxAux.conj_mul_lift htt m m'] at h1
  rw [SixCoxAux.conj_mul_lift htt m' m] at h2
  rcases h1 with h1 | h1
  · exact SixCoxAux.comm_of_conj hss (Subtype.ext h1)
  rcases h2 with h2 | h2
  · exact (SixCoxAux.comm_of_conj hss' (Subtype.ext h2)).symm
  exfalso
  have hrM : r ∈ M := H4b.Rc_le_M C hr
  have h3 := SixCoxAux.comm_core (G := ↥M) (w := ⟨(m : G) * x * (m : G)⁻¹ * r, M.mul_mem
      (M.mul_mem (M.mul_mem m.2 (pCoreOf_le_self M hx)) (M.inv_mem m.2)) hrM⟩)
    (w' := ⟨(m' : G) * x * (m' : G)⁻¹ * r, M.mul_mem
      (M.mul_mem (M.mul_mem m'.2 (pCoreOf_le_self M hx)) (M.inv_mem m'.2)) hrM⟩)
    hss hss' (Subtype.ext h1) (Subtype.ext h2)
  have h4 := D.sixCox_pair_eq_of_inv hx hij hπ hr (n := m) (n' := m') (congrArg Subtype.val h3)
  rw [hma, hmb, hm'c, hm'd] at h4
  have h5 : a ∈ ({c, d} : Finset (Fin 6)) := by
    rw [← h4]
    exact Finset.mem_insert_self a {b}
  simp only [Finset.mem_insert, Finset.mem_singleton] at h5
  rcases h5 with h5 | h5
  · exact hac h5
  · exact had h5

theorem sixCox_braid (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) {r : G} (hr : r ∈ Rc X)
    {t : ↥M} (htt : (t : G) * t = 1) (ht : C.θ t = swap i j)
    (hcl : ∀ z : G, (∃ k ∈ CGOf x, z = k * r * k⁻¹) ↔ z = r ∨ z = t ∨ z = t * (x * r))
    {m m' : ↥M} {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : C.θ m i = a) (hmb : C.θ m j = b) (hm'b : C.θ m' i = b) (hm'c : C.θ m' j = c) :
    m * t * m⁻¹ * (m' * t * m'⁻¹) * (m * t * m⁻¹) =
      m' * t * m'⁻¹ * (m * t * m⁻¹) * (m' * t * m'⁻¹) := by
  have hθs : C.θ (m * t * m⁻¹) = swap a b := by rw [sixCox_theta_conj m t ht, hma, hmb]
  have hθs' : C.θ (m' * t * m'⁻¹) = swap b c := by rw [sixCox_theta_conj m' t ht, hm'b, hm'c]
  have hni : C.θ (m * t * m⁻¹ * m') i = a := by
    rw [map_mul, Perm.mul_apply, hθs, hm'b, swap_apply_right]
  have hnj : C.θ (m * t * m⁻¹ * m') j = c := by
    rw [map_mul, Perm.mul_apply, hθs, hm'c, swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hn'i : C.θ (m' * t * m'⁻¹ * m) i = a := by
    rw [map_mul, Perm.mul_apply, hθs', hma, swap_apply_of_ne_of_ne hab hac]
  have hn'j : C.θ (m' * t * m'⁻¹ * m) j = c := by
    rw [map_mul, Perm.mul_apply, hθs', hmb, swap_apply_left]
  have h1 := D.sixCox_same_pair hR hsurj hx hij hπ hr ht hcl (n := m * t * m⁻¹ * m')
    (n' := m' * t * m'⁻¹ * m) (by rw [hni, hnj, hn'i, hn'j])
  have htt' : t * t = 1 := Subtype.ext htt
  have hss : (m * t * m⁻¹) * (m * t * m⁻¹) = 1 := SixCoxAux.conj_mul_conj htt'
  have hss' : (m' * t * m'⁻¹) * (m' * t * m'⁻¹) = 1 := SixCoxAux.conj_mul_conj htt'
  have hsi : (m * t * m⁻¹)⁻¹ = m * t * m⁻¹ := inv_eq_of_mul_eq_one_right hss
  rw [SixCoxAux.conj_mul_lift htt m m', SixCoxAux.conj_mul_lift htt m' m] at h1
  rcases h1 with h1 | h1
  · exact (Subtype.ext h1).symm
  exfalso
  have hrM : r ∈ M := H4b.Rc_le_M C hr
  have hy' : (m' : G) * x * (m' : G)⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem m'.2 (pCoreOf_le_self M hx)) (M.inv_mem m'.2)
  have hsr : (m * t * m⁻¹) * ⟨r, hrM⟩ * (m * t * m⁻¹) = ⟨r, hrM⟩ := by
    apply Subtype.ext
    have h0 := C.R_central hR _ (m * t * m⁻¹ : ↥M).2 r hr
    rw [← Subgroup.coe_inv, hsi] at h0
    exact h0
  have e3 : ((m * t * m⁻¹ * m' : ↥M) : G) * x * ((m * t * m⁻¹ * m' : ↥M) : G)⁻¹ * r =
      ((m * t * m⁻¹ * ⟨_, hy'⟩ * (m * t * m⁻¹) * ⟨r, hrM⟩ : ↥M) : G) := by
    calc _ = ((m * t * m⁻¹ * ⟨_, hy'⟩ * (m * t * m⁻¹)⁻¹ * ⟨r, hrM⟩ : ↥M) : G) := by
          push_cast
          group
      _ = _ := by rw [hsi]
  rw [e3] at h1
  have h3 := SixCoxAux.braid_core hss hss' hsr (y := ⟨_, hy'⟩) (Subtype.ext h1)
  have h4 := D.sixCox_pair_eq_of_inv hx hij hπ hr (n := m * t * m⁻¹ * m') (n' := m') (by
    rw [e3]
    exact congrArg Subtype.val h3)
  rw [hni, hnj, hm'b, hm'c] at h4
  have h5 : a ∈ ({b, c} : Finset (Fin 6)) := by
    rw [← h4]
    exact Finset.mem_insert_self a {c}
  simp only [Finset.mem_insert, Finset.mem_singleton] at h5
  rcases h5 with h5 | h5
  · exact hab h5
  · exact hac h5

theorem sixCox_exists_section_of_class (hR : Nat.card ↥(Rc X) ≤ 2)
    (hsurj : Function.Surjective C.θ) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6}
    (hij : i ≠ j) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) {r : G}
    (hr : r ∈ Rc X) {t : ↥M} (htt : (t : G) * t = 1) (ht : C.θ t = swap i j)
    (hcl : ∀ z : G, (∃ k ∈ CGOf x, z = k * r * k⁻¹) ↔ z = r ∨ z = t ∨ z = t * (x * r)) :
    ∃ ψ : Equiv.Perm (Fin 6) →* ↥M, ∀ σ, C.θ (ψ σ) = σ := by
  have hne : ∀ {a b : ℕ} {ha : a < 6} {hb : b < 6}, a ≠ b → (⟨a, ha⟩ : Fin 6) ≠ ⟨b, hb⟩ :=
    fun hab h => hab (Fin.mk.inj h)
  have hex : ∀ k : ℕ, ∀ hk : k < 5,
      ∃ m : ↥M, C.θ m i = ⟨k, by omega⟩ ∧ C.θ m j = ⟨k + 1, by omega⟩ := by
    intro k hk
    have h2 : ∃ σ : Perm (Fin 6), σ • i = (⟨k, by omega⟩ : Fin 6) ∧ σ • j = ⟨k + 1, by omega⟩ :=
      MulAction.is_two_pretransitive_iff.1 (Perm.isMultiplyPretransitive (Fin 6) 2) hij
        (hne (by omega))
    obtain ⟨σ, hσi, hσj⟩ := h2
    obtain ⟨m, hm⟩ := hsurj σ
    exact ⟨m, by rw [hm, ← Perm.smul_def, hσi], by rw [hm, ← Perm.smul_def, hσj]⟩
  choose mk hmk using hex
  let g : ℕ → ↥M := fun k => if hk : k < 5 then mk k hk * t * (mk k hk)⁻¹ else 1
  have hg : ∀ k (hk : k < 5), g k = mk k hk * t * (mk k hk)⁻¹ := fun k hk => dif_pos hk
  have hcox : Permutation.SymmetricCoxeter.IsCoxeterA 5 g := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k l hkl hl => ?_⟩
    · rw [hg k hk]
      exact SixCoxAux.conj_mul_conj (Subtype.ext htt)
    · rw [hg k (by omega), hg (k + 1) hk]
      exact D.sixCox_braid hR hsurj hx hij hπ hr htt ht hcl (hne (by omega)) (hne (by omega))
        (hne (by omega)) (hmk k (by omega)).1 (hmk k (by omega)).2 (hmk (k + 1) hk).1
        (hmk (k + 1) hk).2
    · rw [hg k (by omega), hg l hl]
      exact D.sixCox_comm hR hsurj hx hij hπ hr htt ht hcl (hne (by omega)) (hne (by omega))
        (hne (by omega)) (hne (by omega)) (hmk k (by omega)).1 (hmk k (by omega)).2
        (hmk l hl).1 (hmk l hl).2
  obtain ⟨ψ, hψ⟩ := Permutation.SymmetricCoxeter.exists_hom_perm 5 g hcox
  have hθψ : (C.θ.comp ψ : Perm (Fin 6) →* Perm (Fin 6)) = MonoidHom.id (Perm (Fin 6)) := by
    refine MonoidHom.eq_of_eqOn_dense (Permutation.SymmetricCoxeter.closure_adjSwap 5) ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 5 := hk
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hψ k hk', hg k hk', sixCox_theta_conj _ t ht,
      (hmk k hk').1, (hmk k hk').2, Permutation.SymmetricCoxeter.adjSwap_of_lt hk']
  exact ⟨ψ, fun σ => DFunLike.congr_fun hθψ σ⟩

section Residual

variable (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M)
  (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x)
include hR2 hsurj hQ16 hij hπ hK h

theorem sixCox_exists_section : ∃ ψ : Equiv.Perm (Fin 6) →* ↥M, ∀ σ, C.θ (ψ σ) = σ := by
  obtain ⟨r, hr, -, t, htt, ht, hcl, -⟩ := D.sixInv_exists hR2 hsurj hQ16 hx hij hπ hK h
  exact D.sixCox_exists_section_of_class hR2.le hsurj hx hij hπ hr htt ht hcl

end Residual

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
