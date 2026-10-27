module

public import Certificates.Kernel.AE6CertE.Chains
public import Certificates.Kernel.AE6CertE.Keys
public import CFSG.Certificates.Kernel.AE6CertESound

public section

namespace CertificateChecks.KernelAE6CertE

open CFSG.Certificates CFSG.Sporadic.Schreier Certificates.AE6CertE Certificates.AE6Model
  Certificates.AE6CertEK CFSG.KC.AE6CertE CertificateChecks.KernelAE6F CFSG.KS.Raw

theorem card_of_ok {Q : RawSchreierDatum 360} {L : List ℕ} {N : ℕ}
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ eGens L})
    (h : Q.check = true ∧ Q.orderCertificate = N) :
    Nat.card (Subgroup.closure {g | g ∈ eGens L}) = N := by
  rw [← hQ, ← h.2, Q.orderCertificate_eq_card h.1]

theorem e517611_orders : ∀ p ∈ ([([0, 2, 4, 6], 4096), ([0, 2, 3, 4, 5, 6, 7], 1290240),
    ([0, 1, 2, 3, 4, 5, 6], 1290240), ([0, 1, 2, 3, 4, 6, 7], 1290240), ([0, 1, 2, 4, 6], 12288),
    ([0, 2, 3, 4, 6], 12288), ([0, 2, 4, 5, 6], 12288), ([0, 2, 4, 6, 7], 12288),
    ([0, 2, 4, 5, 6, 7], 36864), ([0, 1, 2, 4, 5, 6], 36864), ([0, 1, 2, 4, 6, 7], 36864)] :
    List (List ℕ × ℕ)), Nat.card (Subgroup.closure {g | g ∈ eGens p.1}) = p.2 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eUQ_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eV0Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eV1Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eV2Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eP1Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eP3Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eP5Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eP7Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eP57Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eP15Q_ok
  · exact card_of_ok (certificate_originalSubgroup _ _ _ _ _) eP17Q_ok

noncomputable abbrev eU : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure {g | g ∈ eGens [0, 2, 4, 6]}

theorem eT_letters : Letters eT (curtisPerms ()) := by
  intro a ha
  have e : getK eT a = CertificateChecks.KernelO8.AP.S a := by
    interval_cases a <;> rfl
  have hp : Orb.PRep 360 9 (getK eT a) ((curtisPerms ()).getD a 1) := by
    rw [e]
    exact prep_curtis ha
  exact ⟨hp, inv_of_invoK hp (ch517611_invo a ha)⟩

theorem mem_eU {d : ℕ} (hd : d < 4) : (curtisPerms ()).getD (d + d) 1 ∈ eU := by
  apply Subgroup.subset_closure
  simp only [Set.mem_setOf_eq, eGens, List.mem_map]
  exact ⟨d + d, by interval_cases d <;> decide, rfl⟩

theorem eU_le_stabO {O : List ℕ} (h : ∀ l < 4, invarK (getK eT (l + l)) O 360 = true) :
    eU ≤ stabO O := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq, eGens, List.mem_map] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi' : ∃ l < 4, i = l + l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩
  obtain ⟨l, hl, rfl⟩ := hi'
  exact mem_stabO_of_invarK ((eT_letters (l + l) (by omega)).1) (h l hl)

theorem keyData {O : List ℕ} {Lk : List ℕ} {k : ℕ} (hO : O.Nodup) (hlt : ∀ o ∈ O, o < 360)
    (hinv : ∀ l < 4, invarK (getK eT (l + l)) O 360 = true) (hU : ∀ d < 4, d + d ∈ Lk)
    (hL : ∀ a ∈ Lk, a < 8)
    (hc : Nat.card (Subgroup.closure {g | g ∈ eGens Lk}) = 1290240)
    (hw : ((List.range 315).all fun j => (eWordOf k j).all fun a => memK a Lk) = true)
    (hk : keysK eT O (eWordOf k) 315 = true) :
    KeyData eT (curtisPerms ()) O eU (Subgroup.closure {g | g ∈ eGens Lk}) (eWordOf k) Lk where
  letters := eT_letters
  nodup := hO
  lt := hlt
  stab := eU_le_stabO hinv
  le := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq, eGens, List.mem_map] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    have hi' : ∃ l < 4, i = l + l := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
      · exact ⟨2, by norm_num, rfl⟩
      · exact ⟨3, by norm_num, rfl⟩
    obtain ⟨l, hl, rfl⟩ := hi'
    apply Subgroup.subset_closure
    simp only [Set.mem_setOf_eq, eGens, List.mem_map]
    exact ⟨l + l, hU l hl, rfl⟩
  card := by
    rw [hc, card_of_ok (certificate_originalSubgroup _ _ _ _ _) eUQ_ok]
  lk := fun a ha => ⟨hL a ha, Subgroup.subset_closure (by
    simp only [Set.mem_setOf_eq, eGens, List.mem_map]
    exact ⟨a, ha, rfl⟩)⟩
  words := fun j hj a ha => by
    simp only [List.all_eq_true, List.mem_range] at hw
    exact (memK_iff a Lk).1 (hw j hj a ha)
  keys := hk

theorem keyData0 : KeyData eT (curtisPerms ()) eO0 eU
    (Subgroup.closure {g | g ∈ eGens [0, 2, 3, 4, 5, 6, 7]}) (eWordOf 0) [0, 2, 3, 4, 5, 6, 7] :=
  keyData (by decide) (by decide) ch517611_inv0 (by decide) (by decide)
    (e517611_orders ([0, 2, 3, 4, 5, 6, 7], 1290240) (by simp)) ch517611_w0 ch517611_k0

theorem keyData1 : KeyData eT (curtisPerms ()) eO2 eU
    (Subgroup.closure {g | g ∈ eGens [0, 1, 2, 3, 4, 5, 6]}) (eWordOf 1) [0, 1, 2, 3, 4, 5, 6] :=
  keyData (by decide) (by decide) ch517611_inv2 (by decide) (by decide)
    (e517611_orders ([0, 1, 2, 3, 4, 5, 6], 1290240) (by simp)) ch517611_w1 ch517611_k1

theorem keyData2 : KeyData eT (curtisPerms ()) eO1 eU
    (Subgroup.closure {g | g ∈ eGens [0, 1, 2, 3, 4, 6, 7]}) (eWordOf 2) [0, 1, 2, 3, 4, 6, 7] :=
  keyData (by decide) (by decide) ch517611_inv1 (by decide) (by decide)
    (e517611_orders ([0, 1, 2, 3, 4, 6, 7], 1290240) (by simp)) ch517611_w2 ch517611_k2

theorem e517611_graph : ∀ k < 3, ∀ j < 315, ∀ x < 8, x ≠ eOmit.getD k 0 → ∃ j' < 315,
    aeWord (curtisPerms ()) (eWordOf k j) * (curtisPerms ()).getD x 1 *
      (aeWord (curtisPerms ()) (eWordOf k j'))⁻¹ ∈ eU := by
  intro k hk j hj x hx ho
  interval_cases k
  · exact keyData0.graph hj (by revert x; decide)
  · exact keyData1.graph hj (by revert x; decide)
  · exact keyData2.graph hj (by revert x; decide)

theorem e517611_letters : ∀ k < 3, ∀ j < 315, ∀ i ∈ eWordOf k j, (curtisPerms ()).getD i 1 ∈
    eU ⊔ Subgroup.zpowers (aeWord (curtisPerms ()) (eWordOf k j)) := by
  intro k hk j hj
  interval_cases k
  · exact keyData0.letters_of_paths (fun d hd => mem_eU hd) hj
      (paths_all ch517611_p0a ch517611_p0b ch517611_p0c ch517611_p0d ch517611_p0e j hj)
  · exact keyData1.letters_of_paths (fun d hd => mem_eU hd) hj
      (paths_all ch517611_p1a ch517611_p1b ch517611_p1c ch517611_p1d ch517611_p1e j hj)
  · exact keyData2.letters_of_paths (fun d hd => mem_eU hd) hj
      (paths_all ch517611_p2a ch517611_p2b ch517611_p2c ch517611_p2d ch517611_p2e j hj)

end CertificateChecks.KernelAE6CertE

end
