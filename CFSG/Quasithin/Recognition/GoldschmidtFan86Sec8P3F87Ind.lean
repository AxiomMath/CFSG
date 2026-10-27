module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87V
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86.F87

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem three_ne_one (h71c : Fan71c F L) {u v w : V} (hu : valence Γ u = 5)
    (hv : valence Γ v = 5) (hw : valence Γ w = 5) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hd : 2 < Γ.dist u v) : L.z u * L.z v * L.z w ≠ 1 := by
  refine h71c.2.2 u v w hu hv hw huv huw hvw ?_
  rintro ⟨β, hβ⟩
  have hu' : Γ.Adj β u := by
    have : u ∈ Γ.neighborSet β := by rw [← hβ]; simp
    exact this
  have hv' : Γ.Adj β v := by
    have : v ∈ Γ.neighborSet β := by rw [← hβ]; simp
    exact this
  have := F.isTree.connected.dist_triangle (u := u) (v := β) (w := v)
  have h1 : Γ.dist u β = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hu'.symm
  have h2 : Γ.dist β v = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hv'
  omega

theorem fin5_complement : ∀ i j t : Fin 5, i ≠ j → i ≠ t → j ≠ t →
    ∃ p q : Fin 5, p ≠ q ∧ Function.Injective (![i, j, t, p, q] : Fin 5 → Fin 5) := by
  decide

theorem fin5_kstar_facts : ∀ i j : Fin 5, i ≠ j →
    kstar (kstar i j) (kstar j i) = j ∧ kstar (kstar j i) (kstar i j) = i ∧
    kstar (kstar i j) (midlab i j) = kstar j i ∧ kstar (midlab i j) (kstar i j) = j ∧
    kstar (kstar j i) (midlab i j) = kstar i j ∧ kstar (midlab i j) (kstar j i) = i := by
  unfold kstar midlab
  decide

open scoped IsMulCommutative in
theorem no_rel (h7 : Fan7 F L) (h82 : Fan82a F L) (D : D10Set L α) {i j t : Fin 5}
    (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t) (a b f e₁ e₂ e₃ : ℕ) :
    L.z (D.alpha t) * (L.z (D.alpha i) ^ a * L.z (D.alpha j) ^ b) * L.z α ^ f ≠
      L.z (D.alpha i) ^ e₁ * L.z (D.alpha j) ^ e₂ * L.z α ^ e₃ := by
  have h71c : Fan71c F L := h7.2.2.1
  have hα : valence Γ α = 5 := D.val
  have hcomm := isMulCommutative_zGroup (α := α) h71c
  obtain ⟨p, q, hpq, hinj⟩ := fin5_complement i j t hij hit hjt
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have hzαV : L.z α ∈ L.zGroup 2 α := z_mem_zGroup (by simp) hα
  have hv5 := D.valence_alpha F
  have hd4 : ∀ {s s' : Fin 5}, s ≠ s' → 2 < Γ.dist (D.alpha s) (D.alpha s') := fun h => by
    rw [D.dist_alpha_alpha F h71c h]
    norm_num
  have hne : ∀ {s s' : Fin 5}, s ≠ s' → D.alpha s ≠ D.alpha s' := fun h h' => by
    have := hd4 h
    rw [h', SimpleGraph.dist_self] at this
    omega
  have h82' := h82 α D
  unfold prodFive at h82'
  have hR : L.z (D.alpha i) * L.z (D.alpha j) * L.z (D.alpha t) * L.z (D.alpha p) *
      L.z (D.alpha q) = 1 := by
    have h := prodFive_perm (fun s => (⟨L.z (D.alpha s), hzV s⟩ : ↥(L.zGroup 2 α))) hinj
    have h1 : prodFive (fun s => (⟨L.z (D.alpha s), hzV s⟩ : ↥(L.zGroup 2 α))) = 1 :=
      Subtype.ext (by simpa [prodFive] using h82')
    rw [h1] at h
    simpa using (congrArg Subtype.val h).symm
  have hsq : ∀ s, L.z (D.alpha s) * L.z (D.alpha s) = 1 := fun s => L.z_mul_self (hv5 s)
  have hti : t ≠ i := hit.symm
  have htj : t ≠ j := hjt.symm
  have h5 := three_ne_one h71c (hv5 t) (hv5 i) (hv5 j) (hne hti) (hne htj) (hne hij) (hd4 hti)
  have h6 := three_ne_one h71c (hv5 t) (hv5 i) hα (hne hti) (D.alpha_ne_start t)
    (D.alpha_ne_start i) (hd4 hti)
  have h7' := three_ne_one h71c (hv5 t) (hv5 j) hα (hne htj) (D.alpha_ne_start t)
    (D.alpha_ne_start j) (hd4 htj)
  have h8 := three_ne_one h71c (hv5 p) (hv5 q) hα (hne hpq) (D.alpha_ne_start p)
    (D.alpha_ne_start q) (hd4 hpq)
  have key := no_rel_nat (A := ↥(L.zGroup 2 α))
    (zi := ⟨L.z (D.alpha i), hzV i⟩) (zj := ⟨L.z (D.alpha j), hzV j⟩)
    (zt := ⟨L.z (D.alpha t), hzV t⟩) (zp := ⟨L.z (D.alpha p), hzV p⟩)
    (zq := ⟨L.z (D.alpha q), hzV q⟩) (z := ⟨L.z α, hzαV⟩)
    (Subtype.ext (hsq i)) (Subtype.ext (hsq j)) (Subtype.ext (hsq t))
    (Subtype.ext (L.z_mul_self hα)) (Subtype.ext hR)
    (fun h => L.z_ne_one (hv5 t) (congrArg Subtype.val h))
    (fun h => hne hti (h71c.z_injective (hv5 t) (hv5 i) (congrArg Subtype.val h)))
    (fun h => hne htj (h71c.z_injective (hv5 t) (hv5 j) (congrArg Subtype.val h)))
    (fun h => D.alpha_ne_start t (h71c.z_injective (hv5 t) hα (congrArg Subtype.val h)))
    (fun h => h5 (by simpa using congrArg Subtype.val h))
    (fun h => h6 (by simpa using congrArg Subtype.val h))
    (fun h => h7' (by simpa using congrArg Subtype.val h))
    (fun h => h8 (by simpa using congrArg Subtype.val h)) a b f e₁ e₂ e₃
  intro h
  exact key (Subtype.ext (by simpa using h))

open scoped IsMulCommutative in
theorem label_quads (h7 : Fan7 F L) (h82 : Fan82a F L) (D : D10Set L α) {i j : Fin 5}
    (hij : i ≠ j) :
    L.z (D.alpha j) * L.z (D.alpha i) * (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) =
      L.z (D.alpha (midlab i j)) ∧
    L.z (D.alpha (kstar j i)) * L.z (D.alpha j) *
        (L.z (D.alpha (kstar i j)) * L.z (D.alpha (midlab i j))) = L.z (D.alpha i) ∧
    L.z (D.alpha (kstar i j)) * L.z (D.alpha i) *
        (L.z (D.alpha (kstar j i)) * L.z (D.alpha (midlab i j))) = L.z (D.alpha j) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hcomm := isMulCommutative_zGroup (α := α) h71c
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have hsq : ∀ s, L.z (D.alpha s) * L.z (D.alpha s) = 1 := fun s =>
    L.z_mul_self (D.valence_alpha F s)
  have h82' := h82 α D
  unfold prodFive at h82'
  have h := prodFive_reindex (fun s => (⟨L.z (D.alpha s), hzV s⟩ : ↥(L.zGroup 2 α))) hij
  have h1 : prodFive (fun s => (⟨L.z (D.alpha s), hzV s⟩ : ↥(L.zGroup 2 α))) = 1 :=
    Subtype.ext (by simpa [prodFive] using h82')
  rw [h1] at h
  obtain ⟨q1, q2, q3⟩ := quad3 (A := ↥(L.zGroup 2 α))
    (zi := ⟨L.z (D.alpha i), hzV i⟩) (zj := ⟨L.z (D.alpha j), hzV j⟩)
    (za := ⟨L.z (D.alpha (kstar i j)), hzV _⟩) (zb := ⟨L.z (D.alpha (kstar j i)), hzV _⟩)
    (zm := ⟨L.z (D.alpha (midlab i j)), hzV _⟩) (Subtype.ext (hsq i)) (Subtype.ext (hsq j))
    (Subtype.ext (hsq _)) h.symm
  exact ⟨by simpa using congrArg Subtype.val q1, by simpa using congrArg Subtype.val q2,
    by simpa using congrArg Subtype.val q3⟩

end CFSG.Quasithin.Fan86.F87
