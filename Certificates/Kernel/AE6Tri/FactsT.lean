module

public import Certificates.Kernel.AE6Tri.FactsG
public import Certificates.Kernel.AE6Tri.Orb
public import Certificates.Certificate517532Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open scoped Pointwise

theorem band_t {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem map_letter {L : Nat} {A : Finset (Fin 8)} (hA : ∀ i : Fin 8, bit L i.val = true ↔ i ∈ A) :
    (ae6LetterSub ↑A).map omegaT.subtype = lsub gP L := by
  rw [ae6LetterSub, MonoidHom.map_closure, lsub]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i.val, i.isLt, (hA i).2 hi, (coe_curtisGen i).symm⟩
  · rintro ⟨c, hc, hb, rfl⟩
    exact ⟨_, ⟨⟨c, hc⟩, (hA ⟨c, hc⟩).1 hb, rfl⟩, coe_curtisGen ⟨c, hc⟩⟩

theorem card_letter {L : Nat} {A : Finset (Fin 8)} (hA : ∀ i : Fin 8, bit L i.val = true ↔ i ∈ A) :
    Nat.card (ae6LetterSub ↑A) = Nat.card (lsub gP L) := by
  rw [← map_letter hA, Subgroup.card_map_of_injective omegaT.subtype_injective]

theorem card_v0_ge : 1290240 ≤ Nat.card (ae6ModelV 0) := by
  obtain ⟨h1, h2⟩ := band_t (a := rowsOK RG orbV0 253 0 true)
    (b := Nat.beq (chainCnt orbV0) 1290240) kOrbV0
  have h := rowsOK_sound gRep h1
  rw [Nat.eq_of_beq_eq_true h2] at h
  rw [ae6ModelV_eq, card_letter fun i => (mask_iff i).2.1]
  exact h

theorem card_e0_ge : 86016 ≤ Nat.card (ae6LetterSub ↑(ae6EdgeLetters 0 1)) := by
  obtain ⟨h1, h2⟩ := band_t (a := rowsOK RG orbE0 125 0 true)
    (b := Nat.beq (chainCnt orbE0) 86016) kOrbE0
  have h := rowsOK_sound gRep h1
  rw [Nat.eq_of_beq_eq_true h2] at h
  rw [card_letter fun i => (mask_iff i).2.2]
  exact h

theorem triB_eq : ∀ l : Fin 3, triB.getD l.val [] = Certificates.AE6CertB.triB l := by decide

theorem triB_lt : ∀ l : Fin 3, ∀ x ∈ triB.getD l.val [], x < 360 := by decide

theorem vl_len : vl.length = 3 := by decide

theorem v_le_stab (l : Fin 3) : ae6ModelV l ≤ Certificates.ae6TriStab l := by
  rw [ae6ModelV_eq, ae6LetterSub, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hk := allIx_get kInv l.val (by rw [vl_len]; exact l.isLt)
  rw [Nat.add_zero, ← List.getD_eq_getElem _ []] at hk
  have h := invB_sound gRep hk i.val ((vl_iff l i).1 (Finset.mem_coe.1 hi))
  rw [triB_eq l] at h
  change (A6.curtisGen i : Equiv.Perm (Fin 360)) ∈
    setStab (finOfL (Certificates.AE6CertB.triB l))
  rw [coe_curtisGen]
  exact h

theorem card_inf_mul_le {G : Type*} [Group G] {K S : Subgroup G} [Finite K] {m : ℕ}
    (h : Fin m → G) (hK : ∀ j, h j ∈ K) (hd : ∀ a b, a ≠ b → (h a)⁻¹ * h b ∉ S) :
    Nat.card ↥(K ⊓ S) * m ≤ Nat.card K := by
  set H : Subgroup K := (K ⊓ S).subgroupOf K
  have hinj : Function.Injective fun j : Fin m => (QuotientGroup.mk ⟨h j, hK j⟩ : K ⧸ H) := by
    intro a b hab
    by_contra hne
    have h1 := QuotientGroup.eq.mp hab
    rw [Subgroup.mem_subgroupOf] at h1
    exact hd a b hne (Subgroup.mem_inf.mp h1).2
  have h1 : m ≤ H.index := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fin, ← Subgroup.index] at this
  have h2 := H.card_mul_index
  have h3 : Nat.card H = Nat.card ↥(K ⊓ S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h3] at h2
  calc Nat.card ↥(K ⊓ S) * m ≤ Nat.card ↥(K ⊓ S) * H.index := Nat.mul_le_mul_left _ h1
    _ = Nat.card K := h2

theorem card_mul_le_of_dist {K : Subgroup AE6Om} {S : Set (Fin 360)} (ws : List (List (Fin 8)))
    (hK : ∀ w ∈ ws, ae6Word w ∈ K)
    (hd : (ws.map (List.map Fin.val)).Pairwise fun u v => wv gP u • S ≠ wv gP v • S) :
    Nat.card ↥(K ⊓ (MulAction.stabilizer (Equiv.Perm (Fin 360)) S).comap omegaT.subtype) *
      ws.length ≤ Nat.card K := by
  have hd' := List.pairwise_map.1 hd
  have hne : ∀ a b : Fin ws.length, a ≠ b →
      ((ae6Word ws[a] : AE6Om) : Equiv.Perm (Fin 360)) • S ≠
        ((ae6Word ws[b] : AE6Om) : Equiv.Perm (Fin 360)) • S := by
    intro a b hab
    rw [coe_ae6Word, coe_ae6Word]
    rcases Nat.lt_or_gt_of_ne (Fin.val_injective.ne hab) with h' | h'
    · exact List.pairwise_iff_getElem.1 hd' a b a.2 b.2 h'
    · exact (List.pairwise_iff_getElem.1 hd' b a b.2 a.2 h').symm
  refine card_inf_mul_le (fun j : Fin ws.length => ae6Word ws[j])
    (fun j => hK _ (List.getElem_mem _)) fun a b hab hmem => hne a b hab ?_
  have hmem' : (((ae6Word ws[a])⁻¹ * ae6Word ws[b] : AE6Om) : Equiv.Perm (Fin 360)) ∈
      MulAction.stabilizer (Equiv.Perm (Fin 360)) S := hmem
  have e : ((ae6Word ws[b] : AE6Om) : Equiv.Perm (Fin 360)) =
      ((ae6Word ws[a] : AE6Om) : Equiv.Perm (Fin 360)) *
        (((ae6Word ws[a])⁻¹ * ae6Word ws[b] : AE6Om) : Equiv.Perm (Fin 360)) := by simp
  rw [e, mul_smul, MulAction.mem_stabilizer_iff.1 hmem']

theorem distV_eq : ∀ e : Fin 3,
    distV.getD e.val [] = (Certificates.AE6CertB.distV e).map (List.map Fin.val) := by decide

theorem distE_eq : ∀ e : Fin 3,
    distE.getD e.val [] = (Certificates.AE6CertB.distE e).map (List.map Fin.val) := by decide

theorem distV_len : ∀ e : Fin 3, (Certificates.AE6CertB.distV e).length = 15 := by decide

theorem distE_len : ∀ e : Fin 3, (Certificates.AE6CertB.distE e).length = 7 := by decide

theorem distV_letters : ∀ e : Fin 3, ∀ w ∈ Certificates.AE6CertB.distV e, ∀ i ∈ w,
    i ∈ ae6VertexLetters (ae6EdgeK e) := by
  decide +kernel

theorem distE_letters : ∀ e : Fin 3, ∀ w ∈ Certificates.AE6CertB.distE e, ∀ i ∈ w,
    i ∈ ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e) := by
  decide +kernel

theorem kDistV' : ∀ e : Fin 3,
    distB RG (distV.getD e.val []) (triB.getD (ae6EdgeL e).val []) = true := by
  obtain ⟨h0, h12⟩ := band_t (a := distB RG (distV.getD 0 []) (triB.getD 1 []))
    (b := bAnd(distB RG (distV.getD 1 []) (triB.getD 2 []),
      distB RG (distV.getD 2 []) (triB.getD 2 []))) kDistV
  obtain ⟨h1, h2⟩ := band_t (a := distB RG (distV.getD 1 []) (triB.getD 2 []))
    (b := distB RG (distV.getD 2 []) (triB.getD 2 [])) h12
  intro e
  fin_cases e
  exacts [h0, h1, h2]

theorem kDistE' : ∀ e : Fin 3,
    distB RG (distE.getD e.val []) (triB.getD (Certificates.AE6CertB.triEM e).val []) = true := by
  obtain ⟨h0, h12⟩ := band_t (a := distB RG (distE.getD 0 []) (triB.getD 2 []))
    (b := bAnd(distB RG (distE.getD 1 []) (triB.getD 1 []),
      distB RG (distE.getD 2 []) (triB.getD 0 []))) kDistE
  obtain ⟨h1, h2⟩ := band_t (a := distB RG (distE.getD 1 []) (triB.getD 1 []))
    (b := distB RG (distE.getD 2 []) (triB.getD 0 [])) h12
  intro e
  fin_cases e
  exacts [h0, h1, h2]

theorem dist_v (e : Fin 3) : 15 * Nat.card ↥(ae6ModelV (ae6EdgeK e) ⊓
    Certificates.ae6TriStab (ae6EdgeL e)) ≤ Nat.card (ae6ModelV (ae6EdgeK e)) := by
  have hd := distB_sound gRep (triB_lt _) (kDistV' e)
  rw [distV_eq, triB_eq] at hd
  have h := card_mul_le_of_dist (K := ae6ModelV (ae6EdgeK e)) _ (fun w hw => by
    rw [ae6ModelV_eq]
    exact ae6Word_mem fun i hi => Finset.mem_coe.2 (distV_letters e w hw i hi)) hd
  rw [distV_len] at h
  rw [Nat.mul_comm]
  exact h

theorem dist_e (e : Fin 3) : 7 * Nat.card ↥(ae6LetterSub ↑(ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e)) ⊓
    Certificates.ae6TriStab (Certificates.AE6CertB.triEM e)) ≤
      Nat.card (ae6LetterSub ↑(ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e))) := by
  have hd := distB_sound gRep (triB_lt _) (kDistE' e)
  rw [distE_eq, triB_eq] at hd
  have h := card_mul_le_of_dist (K := ae6LetterSub ↑(ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e))) _
    (fun w hw => ae6Word_mem fun i hi => Finset.mem_coe.2 (distE_letters e w hw i hi)) hd
  rw [distE_len] at h
  rw [Nat.mul_comm]
  exact h

end CertificateChecks.KernelAE6Tri

end
