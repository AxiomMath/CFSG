module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Hj
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Lat
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam
open CFSG.Quasithin.A312M24

theorem memIdx_not_dvd : ∀ j < 13, ¬ 11 ∣ memIdx[j]! ∧ ¬ 23 ∣ memIdx[j]! := by decide

theorem g24_top_of_dvd [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {T K : Subgroup G24} (hT : IsSylowTwoOf T ⊤) (hTK : T ≤ K)
    {p : ℕ} (hp : p = 11 ∨ p = 23) (hdvd : p ∣ Nat.card K) : K = ⊤ := by
  by_contra hne
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf m24_S_sylow' hT
  let e : G24 ≃* G24 := (MulAut.conj g).symm
  have hT' : T.map e.toMonoidHom = m24CtxE.S := by
    rw [← hg]
    exact map_map_symm (MulAut.conj g) m24CtxE.S
  have hK : m24CtxE.S ≤ K.map e.toMonoidHom := by
    rw [← hT']
    exact Subgroup.map_mono hTK
  have hKne : K.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  obtain ⟨j, hj, -, hcard⟩ := overgroup_member hK hKne
  have hc : Nat.card (K.map e.toMonoidHom) = Nat.card K := Nat.card_congr (mapEquiv e K).toEquiv
  rw [hc] at hcard
  rw [hcard] at hdvd
  have hcop : Nat.Coprime p (2 ^ 10) := by
    rcases hp with rfl | rfl <;> norm_num
  have h1 : p ∣ memIdx[j]! := hcop.dvd_of_dvd_mul_right hdvd
  have h2 := memIdx_not_dvd j hj
  rcases hp with rfl | rfl
  · exact h2.1 h1
  · exact h2.2 h1


section Hj


theorem Hj_le_of_elt [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {D : Subgroup J} (hP : P0 ≤ D) {s : J} (hsD : s ∈ D) (hsH : s ∈ Hj)
    (hsE : s ∉ Eg uJ 11) {p : ℕ} (hp : p = 11 ∨ p = 23) (hpE : s ^ p ∈ Eg uJ 11) :
    Hj ≤ D := by
  have hprime : Nat.Prime p := by rcases hp with rfl | rfl <;> norm_num
  have hP0H : P0 ≤ Hj := P0_le_Hj
  have hT' : IsSylowTwoOf (P0.subgroupOf Hj) ⊤ := isSylowTwoOf_subgroupOf_of_le isSylowTwoOf_P0 hP0H
  have hTf : IsSylowTwoOf ((P0.subgroupOf Hj).map fHj) ⊤ :=
    A312.isSylowTwoOf_top_map fHj fHj_surjective hT'
  set K : Subgroup G24 := (D.subgroupOf Hj).map fHj with hKdef
  have hTK : (P0.subgroupOf Hj).map fHj ≤ K :=
    Subgroup.map_mono fun x hx => hP hx
  have hxK : fHj ⟨s, hsH⟩ ∈ K := ⟨⟨s, hsH⟩, hsD, rfl⟩
  have hsker : (⟨s, hsH⟩ : ↥Hj) ∈ fHj.ker ↔ s ∈ Eg uJ 11 := by
    rw [ker_fHj]; exact Iff.rfl
  have hxp : fHj ⟨s, hsH⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨s, hsH⟩ : ↥Hj) ^ p ∈ fHj.ker := by
      rw [ker_fHj]
      exact hpE
    exact this
  have hx1 : fHj ⟨s, hsH⟩ ≠ 1 := fun h => hsE (hsker.1 h)
  have hord : orderOf (fHj ⟨s, hsH⟩) = p := by
    have := Fact.mk hprime
    exact orderOf_eq_prime hxp hx1
  have hdvd : p ∣ Nat.card K := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard K hxK
  have htop : K = ⊤ := g24_top_of_dvd hTf hTK hp hdvd
  intro g hg
  have hmem : fHj ⟨g, hg⟩ ∈ K := htop ▸ Subgroup.mem_top _
  obtain ⟨y, hyD, hy⟩ := hmem
  have hk : y⁻¹ * ⟨g, hg⟩ ∈ fHj.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  rw [ker_fHj] at hk
  have hE : ((y⁻¹ * ⟨g, hg⟩ : ↥Hj) : J) ∈ Eg uJ 11 := hk
  have hyD' : (y : J) ∈ D := hyD
  have e : g = (y : J) * ((y⁻¹ * ⟨g, hg⟩ : ↥Hj) : J) := by
    simp
  rw [e]
  exact D.mul_mem hyD' (hP (Eg_le_P0 hE))

end Hj

end CFSG.Quasithin.J4Ov
