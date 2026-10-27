module

public import CFSG.Quasithin.Recognition.St84.G24Vertex1Frame
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel
public import CFSG.GroupTheory.FixedPointFreeModCentral

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.GroupTheory
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single conj_eElt map_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem)
open Certificates.A5GL42 (aO bO)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

section Frame

variable {L1 L2 S E : Subgroup G}

private theorem eq_zero_of_eElt_mem_centerOf
    (hZE : centerOf (dsQ L1 L2 S) ≤ E)
    {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S)) Certificates.A5GL42.HO}
    {e : Fin 4 → G} (heE : ∀ i, e i ∈ E)
    (hephi : ∀ i, M.F.φ ⟨e i, heE i⟩ = Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))
    {u : Fin 4 → ZMod 2} (hu : eElt e u ∈ centerOf (dsQ L1 L2 S)) : u = 0 := by
  have huE : eElt e u ∈ E := hZE hu
  have hphi : eElt (fun i => M.F.φ ⟨e i, heE i⟩) u = 1 := by
    rw [← map_eElt (v := fun i => (⟨e i, heE i⟩ : ↥E)) M.F.φ u]
    have hcoe : ((eElt (fun i => (⟨e i, heE i⟩ : ↥E)) u : ↥E) : G) = eElt e u := by
      simpa using map_eElt (v := fun i => (⟨e i, heE i⟩ : ↥E))
        (Subgroup.subtype E) u
    have hsub : (⟨eElt e u, huE⟩ : ↥E) = eElt (fun i => (⟨e i, heE i⟩ : ↥E)) u :=
      Subtype.ext hcoe.symm
    rw [← hsub]
    exact (M.F.ker ⟨eElt e u, huE⟩).mpr hu
  have hbasis : eElt (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) u =
      Multiplicative.ofAdd u := by
    have h := CFSG.GroupTheory.eElt_ofAdd_cols (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) u
    rw [Matrix.one_mulVec] at h
    have hfun : (fun i : Fin 4 => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) =
        (fun i : Fin 4 => Multiplicative.ofAdd (fun j : Fin 4 =>
          (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j i)) := by
      funext i
      congr 1
      funext j
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [hfun]
    exact h
  have h1 : Multiplicative.ofAdd u = 1 := by
    rw [← hbasis]
    simpa [hephi] using hphi
  exact ofAdd_eq_one.mp h1

theorem G24Vertex1.indep_v1Frame {k : G}
    (hkB : k ∈ bigB L1 L2 S) (hZE : centerOf (dsQ L1 L2 S) ≤ E)
    {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S)) Certificates.A5GL42.HO}
    {e : Fin 4 → G} (heE : ∀ i, e i ∈ E)
    (hephi : ∀ i, M.F.φ ⟨e i, heE i⟩ = Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))
    (hinter : E ⊓ E.map (MulAut.conj k).toMonoidHom = centerOf (dsQ L1 L2 S)) :
    ∀ v : Fin 8 → ZMod 2, eElt (v1Frame k e) v ∈ centerOf (dsQ L1 L2 S) → v = 0 := by
  intro v hv
  set v1 : Fin 4 → ZMod 2 := fun i => v (Fin.castAdd 4 i) with hv1def
  set v2 : Fin 4 → ZMod 2 := fun i => v (Fin.natAdd 4 i) with hv2def
  have hsplit : eElt (v1Frame k e) v =
      eElt e v1 * eElt (fun i => k * e i * k⁻¹) v2 := by
    rw [eElt_v1Frame]
  have hA : eElt e v1 ∈ E := eElt_mem_of_forall_mem heE v1
  have hB : eElt (fun i => k * e i * k⁻¹) v2 ∈ E.map (MulAut.conj k).toMonoidHom := by
    have h := eElt_mem_of_forall_mem
      (fun i => Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom (heE i)) v2
    simpa [MulAut.conj_apply] using h
  have hABE : eElt e v1 * eElt (fun i => k * e i * k⁻¹) v2 ∈ E := by
    rw [← hsplit]
    exact hZE hv
  have hBE : eElt (fun i => k * e i * k⁻¹) v2 ∈ E := by
    have h : eElt (fun i => k * e i * k⁻¹) v2 =
        (eElt e v1)⁻¹ * (eElt e v1 * eElt (fun i => k * e i * k⁻¹) v2) := by group
    rw [h]
    exact E.mul_mem (E.inv_mem hA) hABE
  have hBZ : eElt (fun i => k * e i * k⁻¹) v2 ∈ centerOf (dsQ L1 L2 S) := by
    have hmem : eElt (fun i => k * e i * k⁻¹) v2 ∈
        E ⊓ E.map (MulAut.conj k).toMonoidHom := ⟨hBE, hB⟩
    rwa [hinter] at hmem
  have hAZ : eElt e v1 ∈ centerOf (dsQ L1 L2 S) := by
    have h1 : eElt e v1 = eElt (v1Frame k e) v *
        (eElt (fun i => k * e i * k⁻¹) v2)⁻¹ := by
      calc eElt e v1 = (eElt e v1 * eElt (fun i => k * e i * k⁻¹) v2) *
            (eElt (fun i => k * e i * k⁻¹) v2)⁻¹ := by group
        _ = eElt (v1Frame k e) v * (eElt (fun i => k * e i * k⁻¹) v2)⁻¹ := by
              rw [← hsplit]
    rw [h1]
    exact (centerOf (dsQ L1 L2 S)).mul_mem hv
      ((centerOf (dsQ L1 L2 S)).inv_mem hBZ)
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  have hkZ : k ∈ Subgroup.normalizer (centerOf (dsQ L1 L2 S) : Set G) :=
    P_le_normalizer_centerOf_dsQ_left L1 L2 S hkP
  have hA2Z : eElt e v2 ∈ centerOf (dsQ L1 L2 S) := by
    have hBconj : eElt (fun i => k * e i * k⁻¹) v2 = k * eElt e v2 * k⁻¹ :=
      (conj_eElt (v := e) k v2).symm
    have hconj : k⁻¹ * eElt (fun i => k * e i * k⁻¹) v2 * k ∈
        centerOf (dsQ L1 L2 S) := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkZ) _).mp hBZ
    have hAeq : k⁻¹ * eElt (fun i => k * e i * k⁻¹) v2 * k = eElt e v2 := by
      rw [hBconj]
      group
    rwa [hAeq] at hconj
  have hv1 : v1 = 0 := eq_zero_of_eElt_mem_centerOf hZE heE hephi hAZ
  have hv2 : v2 = 0 := eq_zero_of_eElt_mem_centerOf hZE heE hephi hA2Z
  funext i
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ i
  · intro i
    simpa [v1] using congrFun hv1 i
  · intro j
    simpa [v2] using congrFun hv2 j

private theorem act_first_mem {g : G} {R : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hL1E : L1 ≤ Subgroup.normalizer (E : Set G))
    {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S)) Certificates.A5GL42.HO}
    {e : Fin 4 → G} (heE : ∀ i, e i ∈ E)
    (hephi : ∀ i, M.F.φ ⟨e i, heE i⟩ = Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))
    (hgL : g ∈ L1) (hR : glMat (M.F.M ⟨g, hgL⟩) = R) (j : Fin 4) :
    g * e j * g⁻¹ * (eElt e (fun i => R i j))⁻¹ ∈ centerOf (dsQ L1 L2 S) := by
  have hgE : g * e j * g⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hL1E hgL) (e j)).mp (heE j)
  have hfE : eElt e (fun i => R i j) ∈ E := eElt_mem_of_forall_mem heE _
  have hqE : g * e j * g⁻¹ * (eElt e (fun i => R i j))⁻¹ ∈ E :=
    E.mul_mem hgE (E.inv_mem hfE)
  have hge : M.F.φ ⟨g * e j * g⁻¹, hgE⟩ = Multiplicative.ofAdd (fun i => R i j) := by
    have hact := M.F.act ⟨g, hgL⟩ ⟨e j, heE j⟩ ⟨g * e j * g⁻¹, hgE⟩ rfl
    have hej : Multiplicative.toAdd (M.F.φ ⟨e j, heE j⟩) = Pi.single j 1 := by
      rw [hephi j]
      exact toAdd_ofAdd _
    rw [hej, hR] at hact
    apply Multiplicative.toAdd.injective
    rw [← hact, Matrix.mulVec_single_one, toAdd_ofAdd]
    rfl
  have hfpow : M.F.φ ⟨eElt e (fun i => R i j), hfE⟩ =
      Multiplicative.ofAdd (fun i => R i j) := by
    have hcoe : ((eElt (fun i => (⟨e i, heE i⟩ : ↥E)) (fun i => R i j) : ↥E) : G) =
        eElt e (fun i => R i j) := by
      simpa using map_eElt (v := fun i => (⟨e i, heE i⟩ : ↥E))
        (Subgroup.subtype E) (fun i => R i j)
    have hsub : (⟨eElt e (fun i => R i j), hfE⟩ : ↥E) =
        eElt (fun i => (⟨e i, heE i⟩ : ↥E)) (fun i => R i j) := Subtype.ext hcoe.symm
    rw [hsub, map_eElt]
    have hfun : (fun i : Fin 4 => M.F.φ ⟨e i, heE i⟩) =
        fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)) := funext hephi
    rw [hfun]
    have h := CFSG.GroupTheory.eElt_ofAdd_cols (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
      (fun i => R i j)
    rw [Matrix.one_mulVec] at h
    have hfun2 : (fun i : Fin 4 => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) =
        (fun i : Fin 4 => Multiplicative.ofAdd (fun j : Fin 4 =>
          (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j i)) := by
      funext i
      congr 1
      funext j
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [hfun2]
    exact h
  have hphi : M.F.φ ⟨g * e j * g⁻¹ * (eElt e (fun i => R i j))⁻¹, hqE⟩ = 1 := by
    change M.F.φ (⟨g * e j * g⁻¹, hgE⟩ *
      (⟨eElt e (fun i => R i j), hfE⟩)⁻¹) = 1
    rw [map_mul, map_inv, hge, hfpow]
    exact mul_inv_cancel _
  exact (M.F.ker ⟨_, hqE⟩).mp hphi

theorem G24Vertex1.act_diag_mem {k : G}
    (hkB : k ∈ bigB L1 L2 S)
    (hL1E : L1 ≤ Subgroup.normalizer (E : Set G))
    {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S)) Certificates.A5GL42.HO}
    {e : Fin 4 → G} (heE : ∀ i, e i ∈ E)
    (hephi : ∀ i, M.F.φ ⟨e i, heE i⟩ = Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))
    {g : G} (hgA : g ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G))
    (hgL : g ∈ L1) (R : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hR : glMat (M.F.M ⟨g, hgL⟩) = R) :
    ∀ j : Fin 8, g * v1Frame k e j * g⁻¹ *
      (eElt (v1Frame k e) (fun i => v1Diag R i j))⁻¹ ∈ centerOf (dsQ L1 L2 S) := by
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  have hkZ : k ∈ Subgroup.normalizer (centerOf (dsQ L1 L2 S) : Set G) :=
    P_le_normalizer_centerOf_dsQ_left L1 L2 S hkP
  intro j
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ j
  · intro j'
    have hfj : v1Frame k e (Fin.castAdd 4 j') = e j' := v1Frame_castAdd k e j'
    have hcol : eElt (v1Frame k e) (fun i => v1Diag R i (Fin.castAdd 4 j')) =
        eElt e (fun i => R i j') := by
      rw [eElt_v1Frame]
      have h1 : (fun i : Fin 4 => v1Diag R (Fin.castAdd 4 i) (Fin.castAdd 4 j')) =
          fun i => R i j' := funext fun i => v1Diag_castAdd_castAdd R i j'
      have h2 : (fun i : Fin 4 => v1Diag R (Fin.natAdd 4 i) (Fin.castAdd 4 j')) = 0 :=
        funext fun i => v1Diag_natAdd_castAdd R i j'
      rw [h1, h2, eElt_zero, mul_one]
    rw [hfj, hcol]
    exact act_first_mem hL1E heE hephi hgL hR j'
  · intro j'
    have hfj : v1Frame k e (Fin.natAdd 4 j') = k * e j' * k⁻¹ := v1Frame_natAdd k e j'
    have hcol : eElt (v1Frame k e) (fun i => v1Diag R i (Fin.natAdd 4 j')) =
        k * eElt e (fun i => R i j') * k⁻¹ := by
      rw [eElt_v1Frame]
      have h1 : (fun i : Fin 4 => v1Diag R (Fin.castAdd 4 i) (Fin.natAdd 4 j')) = 0 :=
        funext fun i => v1Diag_castAdd_natAdd R i j'
      have h2 : (fun i : Fin 4 => v1Diag R (Fin.natAdd 4 i) (Fin.natAdd 4 j')) =
          fun i => R i j' := funext fun i => v1Diag_natAdd_natAdd R i j'
      rw [h1, h2, eElt_zero, one_mul, ← conj_eElt]
    rw [hfj, hcol]
    have hgk : g * k = k * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hgA).2
    have hgk_inv' : k⁻¹ * g⁻¹ = g⁻¹ * k⁻¹ := by
      simpa [mul_inv_rev] using congrArg Inv.inv hgk
    have hbase : g * e j' * g⁻¹ * (eElt e (fun i => R i j'))⁻¹ ∈
        centerOf (dsQ L1 L2 S) :=
      act_first_mem hL1E heE hephi hgL hR j'
    let B := eElt e (fun i => R i j')
    have heq : g * (k * e j' * k⁻¹) * g⁻¹ * (k * B * k⁻¹)⁻¹ =
        k * (g * e j' * g⁻¹ * B⁻¹) * k⁻¹ := by
      calc g * (k * e j' * k⁻¹) * g⁻¹ * (k * B * k⁻¹)⁻¹
          = (g * k) * e j' * (k⁻¹ * g⁻¹) * (k * B * k⁻¹)⁻¹ := by group
        _ = (k * g) * e j' * (k⁻¹ * g⁻¹) * (k * B * k⁻¹)⁻¹ := by rw [hgk]
        _ = k * (g * e j' * g⁻¹) * k⁻¹ * (k * B * k⁻¹)⁻¹ := by
              rw [hgk_inv']
              group
        _ = k * (g * e j' * g⁻¹ * B⁻¹) * k⁻¹ := by group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp hkZ _).mp hbase

theorem G24Vertex1.act_k_mem [Finite G] {k : G}
    (hD : G24LocalData L1 L2 S) (hkB : k ∈ bigB L1 L2 S) (hk3 : orderOf k = 3)
    (hfix : ∀ q ∈ dsQ L1 L2 S,
      k * q * k⁻¹ * q⁻¹ ∈ centerOf (dsQ L1 L2 S) → q ∈ centerOf (dsQ L1 L2 S))
    (hEQ : E ≤ dsQ L1 L2 S) {e : Fin 4 → G} (heE : ∀ i, e i ∈ E) :
    ∀ j : Fin 8, k * v1Frame k e j * k⁻¹ *
      (eElt (v1Frame k e) (fun i => v1Omega i j))⁻¹ ∈ centerOf (dsQ L1 L2 S) := by
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  have hkQ : k ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    P_le_normalizer_dsQ_left L1 L2 S hkP
  have hk3pow : k ^ 3 = 1 := by
    rw [← hk3]
    exact pow_orderOf_eq_one k
  intro j
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ j
  · intro j'
    have hfj : v1Frame k e (Fin.castAdd 4 j') = e j' := v1Frame_castAdd k e j'
    have hcol : eElt (v1Frame k e) (fun i => v1Omega i (Fin.castAdd 4 j')) =
        k * e j' * k⁻¹ := by
      rw [eElt_v1Frame]
      have h1 : (fun i : Fin 4 => v1Omega (Fin.castAdd 4 i) (Fin.castAdd 4 j')) = 0 :=
        funext fun i => v1Omega_castAdd_castAdd i j'
      have h2 : (fun i : Fin 4 => v1Omega (Fin.natAdd 4 i) (Fin.castAdd 4 j')) =
          fun i => (if i = j' then (1 : ZMod 2) else 0) :=
        funext fun i => v1Omega_natAdd_castAdd i j'
      have hs : (fun i : Fin 4 => (if i = j' then (1 : ZMod 2) else 0)) =
          Pi.single j' (1 : ZMod 2) := by
        funext i
        rw [Pi.single_apply]
      rw [h1, h2, hs, eElt_zero, one_mul, eElt_single]
    rw [hfj, hcol]
    simpa using mul_inv_cancel (k * e j' * k⁻¹)
  · intro j'
    have hfj : v1Frame k e (Fin.natAdd 4 j') = k * e j' * k⁻¹ := v1Frame_natAdd k e j'
    have hcol : eElt (v1Frame k e) (fun i => v1Omega i (Fin.natAdd 4 j')) =
        e j' * (k * e j' * k⁻¹) := by
      rw [eElt_v1Frame]
      have h1 : (fun i : Fin 4 => v1Omega (Fin.castAdd 4 i) (Fin.natAdd 4 j')) =
          fun i => (if i = j' then (1 : ZMod 2) else 0) :=
        funext fun i => v1Omega_castAdd_natAdd i j'
      have h2 : (fun i : Fin 4 => v1Omega (Fin.natAdd 4 i) (Fin.natAdd 4 j')) =
          fun i => (if i = j' then (1 : ZMod 2) else 0) :=
        funext fun i => v1Omega_natAdd_natAdd i j'
      have hs : (fun i : Fin 4 => (if i = j' then (1 : ZMod 2) else 0)) =
          Pi.single j' (1 : ZMod 2) := by
        funext i
        rw [Pi.single_apply]
      rw [h1, h2, hs, eElt_single, eElt_single]
    rw [hfj, hcol]
    exact CFSG.GroupTheory.conj_conj_mul_inv_mem_of_pow_three_eq_one
      (Q := dsQ L1 L2 S) (Z := centerOf (dsQ L1 L2 S)) (k := k) (x := e j')
      hk3pow (fun q hq => (Subgroup.mem_normalizer_iff.mp hkQ q).mp hq)
      (fun z hz q hq => G24Vertex1.centerOf_dsQ_comm z hz q hq)
      (fun q hq => G24Vertex1.sq_mem_centerOf_dsQ hD q hq)
      (fun q hq r hr => G24Vertex1.commutator_mem_centerOf_dsQ hD q hq r hr)
      hfix (hEQ (heE j'))

end Frame

end CFSG.Quasithin.F112R.St84
