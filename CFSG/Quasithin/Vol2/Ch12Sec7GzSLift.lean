module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSKap
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSMdl
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSPhi
public import Certificates.Data.S1277Cand

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Struct Certificates.Data.S1277Cand Certificates.Data.S1277Bfs

section Lift

variable {G : Type} [Group G] {K Q : Subgroup G} {T : KTab} {κ : G → Nat}

def ModelInv (T : KTab) : Prop :=
  ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T

theorem ModelInv.mk' {T : KTab}
    (h : ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T) : ModelInv T := h

theorem ModelInv.elim {T : KTab} (h : ModelInv T) :
    ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T := h

theorem KCod.comm (hκ : KCod K T κ) (hinv : ModelInv T) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    κ (a * b * a⁻¹ * b⁻¹) = commN T (κ a) (κ b) := by
  have h1 : a * b ∈ K := K.mul_mem ha hb
  have h2 : a * b * a⁻¹ ∈ K := K.mul_mem h1 (K.inv_mem ha)
  unfold commN
  rw [hκ.mul _ h2 _ (K.inv_mem hb), hκ.mul _ h1 _ (K.inv_mem ha), hκ.mul _ ha _ hb,
    hκ.inv hinv ha, hκ.inv hinv hb]

theorem Phi'_codes_le (hκ : KCod K T κ) (hinv : ModelInv T) (hQK : Q ≤ K) {N : List Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) {Pl : List Nat}
    (hsq : ∀ x ∈ N, mulN T x x ∈ Pl) (hcm : ∀ x ∈ N, ∀ y ∈ N, commN T x y ∈ Pl)
    (hmul : ∀ x ∈ Pl, ∀ y ∈ Pl, mulN T x y ∈ Pl) (hone : oneN T ∈ Pl)
    (hinvPl : ∀ x ∈ Pl, invN T x ∈ Pl) : ∀ r ∈ Phi' Q, κ r ∈ Pl := by
  intro r hr
  let S : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ κ x ∈ Pl}
      one_mem' := ⟨Q.one_mem, by rw [hκ.one]; exact hone⟩
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [hκ.mul a (hQK ha.1) b (hQK hb.1)]; exact hmul _ ha.2 _ hb.2⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by
        rw [hκ.inv hinv (hQK ha.1)]; exact hinvPl _ ha.2⟩ }
  have key : Phi' Q ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (⟨y, hy, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · refine ⟨Q.pow_mem hy 2, ?_⟩
      rw [pow_two, hκ.mul y (hQK hy) y (hQK hy)]
      exact hsq _ ((hQN _).1 ⟨y, hy, rfl⟩)
    · refine ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb), ?_⟩
      rw [hκ.comm hinv (hQK ha) (hQK hb)]
      exact hcm _ ((hQN _).1 ⟨a, ha, rfl⟩) _ ((hQN _).1 ⟨b, hb, rfl⟩)
  exact (key hr).2

theorem Phi'_codes_ge (hκ : KCod K T κ) (hinv : ModelInv T) (hQK : Q ≤ K) {N : List Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) :
    ∀ y ∈ mulCl T (phiGens T N), ∃ r ∈ Phi' Q, κ r = y := by
  have hgen : ∀ g ∈ phiGens T N, ∃ r ∈ Phi' Q, κ r = g := by
    intro g hg
    unfold phiGens at hg
    rw [mem_sortSet] at hg
    have hg' : g ∈ phiGensFull T N := by
      have := (mem_foldl_insert (phiGensFull T N) ∅ g).1 hg
      simpa using this
    unfold phiGensFull at hg'
    rcases List.mem_append.1 hg' with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      obtain ⟨q, hq, rfl⟩ := (hQN x).2 hx
      refine ⟨q ^ 2, sq_mem_Phi' hq, ?_⟩
      rw [pow_two, hκ.mul q (hQK hq) q (hQK hq)]
    · obtain ⟨x, hx, h2⟩ := List.mem_flatMap.1 h
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h2
      obtain ⟨a, ha, rfl⟩ := (hQN x).2 hx
      obtain ⟨b, hb, rfl⟩ := (hQN y).2 hy
      exact ⟨a * b * a⁻¹ * b⁻¹, comm_mem_Phi' ha hb, hκ.comm hinv (hQK ha) (hQK hb)⟩
  intro y hy
  refine mulCl_inv T (phiGens T N) (fun y => ∃ r ∈ Phi' Q, κ r = y) ?_ hgen ?_ y hy
  · exact ⟨1, (Phi' Q).one_mem, hκ.one⟩
  · rintro g hg x ⟨r, hr, rfl⟩
    obtain ⟨r', hr', rfl⟩ := hgen g hg
    exact ⟨r * r', (Phi' Q).mul_mem hr hr', hκ.mul r (hQK (Phi'_le Q hr)) r'
      (hQK (Phi'_le Q hr'))⟩

end Lift

end CFSG.Quasithin.H13.I1277

end
