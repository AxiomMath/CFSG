module

public import CFSG.Sporadic.Th.Recog.AltNine
public import CFSG.Sporadic.Th.Recog.MFactsB.Letters
public import CFSG.Sporadic.Th.Recog.MFactsB.Lift
public import CFSG.Sporadic.Th.Recog.MFactsB.QCount
public import Certificates.Certificate687012

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Max3.InvRep
open CFSG.Sporadic.Th.Recog.MFactsBData
open CFSG.Certificates Certificates

private theorem cert_centT_card :
    (CFSG.Sporadic.Th.Recog.MFactsBData.centTList ()).length = 32 :=
  Certificates.certificate687012.1

private theorem cert_centT_center :
    CFSG.Sporadic.Th.Recog.MFactsBData.centTCenter () = true :=
  Certificates.certificate687012.2

private theorem isRows_rowsT : IsRows (rowsT ()) (tLetter : J) := by
  have h := IsRows.word isRows_x isRows_y (wJ 6)
  change IsRows (rowsT ()) (hswJ 6)
  have h6 : hswJ 6 = Max3.wordProd (wJ 6) := by
    have h' := hswJ_eq_wordProd 6 (by decide)
    rw [show εJ 6 = 0 by rfl, pow_zero, mul_one] at h'
    exact h'
  rw [h6]
  simpa [rowsT] using h

theorem card_Q_inf_centralizer_t :
    Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓ Subgroup.centralizer ({tLetter} : Set ↥Max3.M)) = 32 := by
  rw [card_Q_inf_centralizer_eq_length (g := tLetter) (G := rowsT ()) isRows_rowsT]
  simpa [centTList] using cert_centT_card

private noncomputable abbrev CM : Subgroup ↥Max3.M :=
  Subgroup.centralizer ({tLetter} : Set ↥Max3.M)

private theorem card_centralizer_t_le : Nat.card ↥CM ≤ 1728 := by
  have h := card_centralizer_le_mul tLetter
  rw [card_Q_inf_centralizer_t,
    card_centralizer_of_cycleType_three_three MFactsB.cycleType_kap_tLetter] at h
  simpa using h

private theorem dJ_four : dJ 4 = hswJ 7 := rfl

private theorem card_centralizer_DJ :
    Nat.card ↥(Subgroup.centralizer ({dJD 5} : Set ↥DJ)) = 1728 := by
  have htD : orderOf (dJD 5) = 3 := by
    rw [← Subgroup.orderOf_coe, coe_dJD, dJ_five]
    exact orderOf_hswJ_six
  have huD : dJD 4 * dJD 5 * (dJD 4)⁻¹ = (dJD 5)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_dJD]
    rw [dJ_four, dJ_five]
    exact hswJ_seven_conj_six
  have htop : Subgroup.normalizer (Subgroup.zpowers (dJD 5) : Set ↥DJ) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [Subgroup.le_normalizer_iff]
    intro x _ y hy
    have h5 : DJ.subtype (dJD 5) = hswJ 6 := by
      rw [show DJ.subtype (dJD 5) = ((dJD 5 : ↥DJ) : J) from rfl, coe_dJD, dJ_five]
    have hxN : (x : J) ∈ Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set J) :=
      DJ_le_normalizer x.2
    have hyJ : (y : J) ∈ Subgroup.zpowers (hswJ 6) := by
      have h := Subgroup.mem_map_of_mem DJ.subtype hy
      rw [MonoidHom.map_zpowers, h5] at h
      exact h
    have hmemJ : (x : J) * (y : J) * (x : J)⁻¹ ∈ Subgroup.zpowers (hswJ 6) :=
      ((Subgroup.mem_normalizer_iff.mp hxN) (y : J)).mp hyJ
    have hmap : (Subgroup.zpowers (dJD 5)).map DJ.subtype = Subgroup.zpowers (hswJ 6) := by
      rw [MonoidHom.map_zpowers, h5]
    have hmemMap : ((x * y * x⁻¹ : ↥DJ) : J) ∈
        (Subgroup.zpowers (dJD 5)).map DJ.subtype := by
      rw [hmap]
      simpa using hmemJ
    obtain ⟨z, hz, hzco⟩ := Subgroup.mem_map.mp hmemMap
    rw [Subtype.ext hzco.symm]
    exact hz
  have hcardN :
      Nat.card ↥(Subgroup.normalizer (Subgroup.zpowers (dJD 5) : Set ↥DJ)) = 3456 := by
    rw [htop, Subgroup.card_top, card_DJ]
  have h2 := card_normalizer_zpowers_eq_two_mul (A := ↥DJ) htD huD
  rw [hcardN] at h2
  omega

private theorem card_centralizer_t_ge : 1728 ≤ Nat.card ↥CM := by
  let CD : Subgroup ↥DJ := Subgroup.centralizer ({dJD 5} : Set ↥DJ)
  have hCD : Nat.card ↥CD = 1728 := card_centralizer_DJ
  let f : ↥CD → ↥CM := fun x =>
    ⟨⟨(x.1 : J), DJ_le_M x.1.2⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
      simpa [tLetter, coe_dJD, dJ_five, Subgroup.coe_mul] using
        congrArg (fun z : ↥DJ => (z : J)) hx⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa [f] using congrArg (fun z : ↥CM => ((z : ↥Max3.M) : J)) hxy
  calc 1728 = Nat.card ↥CD := hCD.symm
    _ ≤ Nat.card ↥CM := Nat.card_le_card_of_injective f hf

theorem card_centralizer_t :
    Nat.card ↥(Subgroup.centralizer ({tLetter} : Set ↥Max3.M)) = 1728 :=
  le_antisymm card_centralizer_t_le card_centralizer_t_ge

private theorem exists_commuting_number {w : ↥Max3.M} (hQ : (w : J) ∈ Max3.Q)
    (hcomm : w * tLetter = tLetter * w) :
    ∃ k : Fin 512, nfAt k = (w : J) ∧ k ∈ centTList () := by
  obtain ⟨k, hk⟩ := InvRep.exists_nfAt_eq hQ
  have hkF : k ∈ commFilter (rowsT ()) := by
    rw [mem_commFilter_iff isRows_rowsT, hk]
    have h := congrArg (fun z : ↥Max3.M => (z : J)) hcomm
    simpa [Subgroup.coe_mul] using h
  exact ⟨k, hk, by simpa [centTList] using hkF⟩

private theorem exists_noncommuting_partner {k : Fin 512} {w : ↥Max3.M}
    (hk : nfAt k = (w : J)) (hkC : k ∈ centTList ()) (h1 : w ≠ 1)
    (hz : (w : J) ≠ Max3.z) :
    ∃ k' : Fin 512, k' ∈ centTList () ∧
      nfAt k' * (tLetter : J) = (tLetter : J) * nfAt k' ∧
        eqRows (mulRows (rowsNfAt k) (rowsNfAt k'))
          (mulRows (rowsNfAt k') (rowsNfAt k)) = false := by
  have hk0 : k.val ≠ 0 := by
    intro h0
    apply h1
    have hk0' : k = (0 : Fin 512) := Fin.ext (by simpa using h0)
    have : (w : J) = 1 := by rw [← hk, hk0', nfAt_zero]
    exact Subtype.ext this
  have hk1 : k.val ≠ 1 := by
    intro h1'
    apply hz
    have hk1' : k = (1 : Fin 512) := Fin.ext (by simpa using h1')
    rw [← hk, hk1', nfAt_one]
  have hcheck : ∀ k ∈ centTList (),
      (if k.val = 0 ∨ k.val = 1 then true
        else (centTList ()).any fun k' =>
          eqRows (mulRows (rowsNfAt k) (rowsNfAt k'))
            (mulRows (rowsNfAt k') (rowsNfAt k)) == false) = true := by
    simpa [centTCenter, List.all_eq_true] using cert_centT_center
  have hk' : (centTList ()).any (fun k' =>
      eqRows (mulRows (rowsNfAt k) (rowsNfAt k'))
        (mulRows (rowsNfAt k') (rowsNfAt k)) == false) = true := by
    simpa [hk0, hk1] using hcheck k hkC
  rw [List.any_eq_true] at hk'
  obtain ⟨k', hk'C, hk'false⟩ := hk'
  have hk'F : k' ∈ commFilter (rowsT ()) := by simpa [centTList] using hk'C
  have hk'comm : nfAt k' * (tLetter : J) = (tLetter : J) * nfAt k' :=
    (mem_commFilter_iff isRows_rowsT k').mp hk'F
  have hneRows : eqRows (mulRows (rowsNfAt k) (rowsNfAt k'))
      (mulRows (rowsNfAt k') (rowsNfAt k)) = false := by
    simpa using (beq_iff_eq.mp hk'false)
  exact ⟨k', hk'C, hk'comm, hneRows⟩

theorem center_t : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * tLetter = tLetter * w → w ≠ 1 →
    (w : J) ≠ Max3.z →
      ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ q * tLetter = tLetter * q ∧ q * w ≠ w * q := by
  intro w hQ hcomm h1 hz
  obtain ⟨k, hk, hkC⟩ := exists_commuting_number hQ hcomm
  obtain ⟨k', hk'C, hk'comm, hneRows⟩ := exists_noncommuting_partner hk hkC h1 hz
  refine ⟨⟨nfAt k', Max3.Q_le_M (AltQuot.nfAt_mem_Q k')⟩, AltQuot.nfAt_mem_Q k', ?_, ?_⟩
  · apply Subtype.ext
    exact hk'comm
  · intro hq
    have hJ : nfAt k' * nfAt k = nfAt k * nfAt k' := by
      have h := congrArg (fun z : ↥Max3.M => (z : J)) hq
      simpa [← hk, Subgroup.coe_mul] using h
    exact ((isRows_nfAt k).mul (isRows_nfAt k')).ne_of_eqRows
      ((isRows_nfAt k').mul (isRows_nfAt k)) hneRows hJ.symm

end CFSG.Sporadic.Th.Recog
