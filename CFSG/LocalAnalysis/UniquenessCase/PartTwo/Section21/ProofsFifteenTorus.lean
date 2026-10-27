module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Swap
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.PGroup
public import CFSG.Quasithin.EmptyFaithful.S153UMain
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private def conjJoin (L S : Subgroup G) : Subgroup G :=
  ⨆ s : S, L.map (MulAut.conj (s : G)).toMonoidHom

private def TorusWitness (M T L : Subgroup G) (r : ℕ) (S : Subgroup G) : Prop :=
  (T ⊓ normalizer (L : Set G) : Subgroup G) ≤ S ∧ S ≤ T ∧
    ∃ h : ↥M, (h : G) ∈ conjJoin L S ∧ orderOf h = r ∧
      (h : G) ∈ normalizer (S : Set G) ∧
        ¬ ∀ a ∈ barImage M L, uc22p21cPi M h * a = a * uc22p21cPi M h

private theorem map_conj_le {M L : Subgroup G} (hLM : L ≤ M) {s : G} (hs : s ∈ M) :
    L.map (MulAut.conj s).toMonoidHom ≤ M := by
  rintro x ⟨l, hl, rfl⟩
  exact M.mul_mem (M.mul_mem hs (hLM hl)) (M.inv_mem hs)

private theorem map_conj_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) {x : G} (hx : x ∈ M) :
    L.map (MulAut.conj x).toMonoidHom ∈ calC M := by
  have h := uc22p22u_calC_conj (X := M) (M := M) le_normalizer hL (M.inv_mem hx)
  rwa [show uniqueFourConj x⁻¹ L = L.map (MulAut.conj x).toMonoidHom by
    simp [uniqueFourConj]] at h

private theorem le_conjJoin_self (L S : Subgroup G) : L ≤ conjJoin L S := by
  have h := le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom)
    (⟨1, S.one_mem⟩ : S)
  have h1 : L.map (MulAut.conj ((⟨1, S.one_mem⟩ : S) : G)).toMonoidHom = L := by
    rw [map_one]
    exact Subgroup.map_id L
  rw [h1] at h
  simpa [conjJoin] using h

private theorem conjJoin_mono {L S S' : Subgroup G} (h : S ≤ S') :
    conjJoin L S ≤ conjJoin L S' := by
  refine iSup_le fun s => ?_
  exact le_iSup (fun s' : S' => L.map (MulAut.conj (s' : G)).toMonoidHom) ⟨s, h s.2⟩

private theorem conjJoin_le_conjClosure (M L S : Subgroup G) (hSM : S ≤ M) :
    conjJoin L S ≤ conjClosure M L := by
  refine iSup_le fun s => ?_
  exact le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf M L) => K)
    (L.map (MulAut.conj (s : G)).toMonoidHom) ⟨(s : G), hSM s.2, rfl⟩ le_rfl

private theorem conjClosure_le_of_le {M L : Subgroup G} (hLM : L ≤ M) :
    conjClosure M L ≤ M := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨g, hg, rfl⟩ := hK
  exact map_conj_le hLM hg

private theorem map_conj_conjJoin (L S : Subgroup G) (t : G) :
    (conjJoin L S).map (MulAut.conj t).toMonoidHom =
      ⨆ s : S, L.map (MulAut.conj (t * (s : G))).toMonoidHom := by
  rw [conjJoin, Subgroup.map_iSup]
  exact iSup_congr fun s => map_conj_map_conj L (s : G) t

private theorem barImage_iSup {M : Subgroup G} {ι : Sort*} (P : ι → Subgroup G)
    (hP : ∀ i, P i ≤ M) :
    barImage M (⨆ i, P i) = ⨆ i, barImage M (P i) := by
  unfold barImage
  rw [CFSG.LieType.Steinberg.iSup_subgroupOf (F := M) (T := P) hP, Subgroup.map_iSup]

private theorem barImage_conjJoin {M L S : Subgroup G} (hLM : L ≤ M) (hSM : S ≤ M) :
    barImage M (conjJoin L S) =
      ⨆ s : S, barImage M (L.map (MulAut.conj (s : G)).toMonoidHom) := by
  simpa only [conjJoin] using barImage_iSup
    (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom)
    (fun s => map_conj_le hLM (hSM s.2))

private theorem conj_ne_of_mem_not_mem {T L S : Subgroup G}
    (hT₁S : (T ⊓ normalizer (L : Set G)) ≤ S) (hST : S ≤ T)
    {t : G} (htT : t ∈ T) (htS : t ∉ S) {s s' : G} (hs : s ∈ S) (hs' : s' ∈ S) :
    L.map (MulAut.conj s).toMonoidHom ≠ L.map (MulAut.conj (t * s')).toMonoidHom := by
  intro heq
  have h1 : (L.map (MulAut.conj (t * s')).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom =
      L.map (MulAut.conj (s⁻¹ * (t * s'))).toMonoidHom :=
    map_conj_map_conj L (t * s') s⁻¹
  have h2 : (L.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom = L := by
    rw [map_conj_map_conj, inv_mul_cancel, map_one]
    exact Subgroup.map_id L
  have hLmap : L.map (MulAut.conj (s⁻¹ * (t * s'))).toMonoidHom = L := by
    rw [← h1, ← heq, h2]
  have hN : s⁻¹ * (t * s') ∈ normalizer (L : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hLmap
  have hT : s⁻¹ * (t * s') ∈ T :=
    T.mul_mem (T.inv_mem (hST hs)) (T.mul_mem htT (hST hs'))
  have hSmem : s⁻¹ * (t * s') ∈ S := hT₁S (mem_inf.2 ⟨hT, hN⟩)
  have ht : t = s * (s⁻¹ * (t * s')) * s'⁻¹ := by group
  exact htS (ht ▸ S.mul_mem (S.mul_mem hs hSmem) (S.inv_mem hs'))

private theorem barImage_conjJoin_commute {M T L S : Subgroup G} (hL : L ∈ calC M)
    (hTM : T ≤ M) (hT₁S : (T ⊓ normalizer (L : Set G)) ≤ S) (hST : S ≤ T)
    {t : G} (htT : t ∈ T) (htS : t ∉ S) :
    ∀ a ∈ barImage M (conjJoin L S),
      ∀ b ∈ barImage M ((conjJoin L S).map (MulAut.conj t).toMonoidHom), a * b = b * a := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hSM : S ≤ M := hST.trans hTM
  have hcomm : (⨆ s : S, barImage M (L.map (MulAut.conj (s : G)).toMonoidHom)) ≤
      Subgroup.centralizer
        (↑(⨆ s : S, barImage M (L.map (MulAut.conj (t * (s : G))).toMonoidHom))) := by
    refine iSup_le fun s => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup_le fun s' => ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact uc22p22l_barImage_commute (map_conj_mem_calC hL (hSM s.2))
      (map_conj_mem_calC hL (hTM (T.mul_mem htT (hST s'.2))))
      (conj_ne_of_mem_not_mem hT₁S hST htT htS s.2 s'.2) a ha b hb
  intro a ha b hb
  rw [barImage_conjJoin hLM hSM] at ha
  rw [map_conj_conjJoin, barImage_iSup (fun s : S => L.map (MulAut.conj (t * (s : G))).toMonoidHom)
    (fun s => map_conj_le hLM (hTM (T.mul_mem htT (hST s.2))))] at hb
  exact ((Subgroup.mem_centralizer_iff.mp (hcomm ha)) b hb).symm

private theorem map_conj_conjJoin_le {L S S' : Subgroup G} (hSS' : S ≤ S') {u : G} (hu : u ∈ S') :
    (conjJoin L S).map (MulAut.conj u).toMonoidHom ≤ conjJoin L S' := by
  rw [map_conj_conjJoin]
  refine iSup_le fun s => ?_
  exact le_iSup (fun s' : S' => L.map (MulAut.conj (s' : G)).toMonoidHom)
    ⟨u * (s : G), S'.mul_mem hu (hSS' s.2)⟩

private theorem mem_conjJoin_mul_conj {M T L S : Subgroup G} (hTM : T ≤ M) {h uh : ↥M} {u : G}
    (huh : (uh : G) = u * (h : G) * u⁻¹)
    (hD : (h : G) ∈ conjJoin L S) (hN : (h : G) ∈ normalizer (S : Set G))
    (huT : u ∈ T) (huS : u ∉ S) (huN : u ∈ normalizer (S : Set G)) (hu2 : u ^ 2 ∈ S)
    (hcommS : (h : G) * (uh : G) * (h : G)⁻¹ * (uh : G)⁻¹ ∈ S) :
    ∃ d : ↥M, (d : G) ∈ conjJoin L (S ⊔ Subgroup.zpowers u) ∧
      (d : G) ∈ normalizer ((S ⊔ Subgroup.zpowers u : Subgroup G) : Set G) ∧ d = h * uh := by
  have hSS' : S ≤ S ⊔ Subgroup.zpowers u := le_sup_left
  have huS' : u ∈ S ⊔ Subgroup.zpowers u :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have huhD : (uh : G) ∈ conjJoin L (S ⊔ Subgroup.zpowers u) := by
    refine map_conj_conjJoin_le hSS' huS' ?_
    exact Subgroup.mem_map.2 ⟨(h : G), hD, by simp [huh, MulAut.conj_apply]⟩
  have hD' : (h : G) ∈ conjJoin L (S ⊔ Subgroup.zpowers u) := conjJoin_mono hSS' hD
  have hdD : (h : G) * (uh : G) ∈ conjJoin L (S ⊔ Subgroup.zpowers u) :=
    (conjJoin L (S ⊔ Subgroup.zpowers u)).mul_mem hD' huhD
  have hdN : (h : G) * (uh : G) ∈
      normalizer ((S ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := by
    have hgen : ∀ x ∈ S ⊔ Subgroup.zpowers u, x ∈ S ∨ u⁻¹ * x ∈ S :=
      fun x hx => (CFSG.Quasithin.S153U.mem_sup_zpowers_iff huN hu2).1 hx
    have hcomm' : (h : G) * (u * (h : G) * u⁻¹) * (h : G)⁻¹ *
        (u * (h : G) * u⁻¹)⁻¹ ∈ S ⊔ Subgroup.zpowers u := by
      refine hSS' ?_
      simpa [huh] using hcommS
    have h := uc22ine229_mul_conj_mem_normalizer hSS' huS' hgen hN hcomm'
    simpa [huh] using h
  exact ⟨⟨(h : G) * (uh : G), M.mul_mem h.2 uh.2⟩, by simpa using hdD,
    by simpa using hdN, rfl⟩

private theorem orderOf_mul_not_mem_centralizer {M : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2)
    {h uh d : ↥M} (hd : d = h * uh) (hrh : orderOf (uc22p21cPi M h) = r)
    (hruh : orderOf (uc22p21cPi M uh) = r)
    (hcomm : uc22p21cPi M h * uc22p21cPi M uh = uc22p21cPi M uh * uc22p21cPi M h)
    {C : Subgroup (Bar2 M)} (hC : uc22p21cPi M uh ∈ Subgroup.centralizer (C : Set (Bar2 M)))
    (hnc : uc22p21cPi M h ∉ Subgroup.centralizer (C : Set (Bar2 M))) :
    orderOf (uc22p21cPi M d) = r ∧
      uc22p21cPi M d ∉ Subgroup.centralizer (C : Set (Bar2 M)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hpi : uc22p21cPi M d = uc22p21cPi M h * uc22p21cPi M uh := by
    rw [hd, map_mul]
  have hcomm' : Commute (uc22p21cPi M h) (uc22p21cPi M uh) := hcomm
  have har : uc22p21cPi M h ^ r = 1 := by
    rw [← hrh]
    exact pow_orderOf_eq_one (uc22p21cPi M h)
  have hbr : uc22p21cPi M uh ^ r = 1 := by
    rw [← hruh]
    exact pow_orderOf_eq_one (uc22p21cPi M uh)
  have hne : uc22p21cPi M h * uc22p21cPi M uh ≠ 1 := by
    intro h1
    apply hnc
    have hph : uc22p21cPi M h = (uc22p21cPi M uh)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [hph]
    exact (Subgroup.centralizer (C : Set (Bar2 M))).inv_mem hC
  constructor
  · rw [hpi]
    exact orderOf_eq_prime (by rw [hcomm'.mul_pow, har, hbr, one_mul]) hne
  · intro hdC
    apply hnc
    have hph : uc22p21cPi M h = uc22p21cPi M d * (uc22p21cPi M uh)⁻¹ := by
      rw [hpi]
      group
    rw [hph]
    exact (Subgroup.centralizer (C : Set (Bar2 M))).mul_mem hdC
      ((Subgroup.centralizer (C : Set (Bar2 M))).inv_mem hC)

private theorem exists_pow_mem_normalizer_not_mem_centralizer {M L S' : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    {d : ↥M} (hdD : (d : G) ∈ conjJoin L S')
    (hdN : (d : G) ∈ normalizer (S' : Set G))
    (hdorder : orderOf (uc22p21cPi M d) = r)
    (hdnc : uc22p21cPi M d ∉ Subgroup.centralizer (barImage M L : Set (Bar2 M))) :
    ∃ h' : ↥M, (h' : G) ∈ conjJoin L S' ∧ orderOf h' = r ∧
      (h' : G) ∈ normalizer (S' : Set G) ∧
      uc22p21cPi M h' ∉ Subgroup.centralizer (barImage M L : Set (Bar2 M)) := by
  obtain ⟨c, hc⟩ := uc22ine229_exists_pow_orderOf_eq d hr hr2
    (by simpa [uc22p21cPi] using hdorder)
  refine ⟨d ^ 2 ^ c, ?_, hc, ?_, ?_⟩
  · simpa using (conjJoin L S').pow_mem hdD (2 ^ c)
  · simpa using (normalizer (S' : Set G)).pow_mem hdN (2 ^ c)
  · intro hcent
    apply hdnc
    have hpowC : uc22p21cPi M (d ^ 2 ^ c) ∈
        Subgroup.centralizer (barImage M L : Set (Bar2 M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcent a ha
    have hpowEq : uc22p21cPi M (d ^ 2 ^ c) = uc22p21cPi M d ^ (2 ^ c) := map_pow _ _ _
    have hcop : Nat.Coprime (2 ^ c) (orderOf (uc22p21cPi M d)) := by
      have hcop' : Nat.Coprime (orderOf (uc22p21cPi M d)) (2 ^ c) := by
        rw [hdorder]
        exact ((Nat.coprime_primes hr Nat.prime_two).2 hr2).pow_right c
      exact hcop'.symm
    have hmem : uc22p21cPi M d ∈ Subgroup.zpowers (uc22p21cPi M d ^ 2 ^ c) :=
      mem_zpowers_pow_iff.mpr hcop
    exact Subgroup.zpowers_le.2 (by rwa [hpowEq] at hpowC) hmem

private theorem torusWitness_step_commute {M T L S : Subgroup G} (hL : L ∈ calC M)
    (hTM : T ≤ M) (hT₁S : (T ⊓ normalizer (L : Set G)) ≤ S) (hST : S ≤ T)
    {h : ↥M} (hD : (h : G) ∈ conjJoin L S) {u : G} (huT : u ∈ T) (huS : u ∉ S) :
    ∃ uh : ↥M, (uh : G) = u * (h : G) * u⁻¹ ∧
      uc22p21cPi M h * uc22p21cPi M uh = uc22p21cPi M uh * uc22p21cPi M h ∧
      (h : G) * (uh : G) * (h : G)⁻¹ * (uh : G)⁻¹ ∈ pCoreOf 2 M := by
  have huM : u ∈ M := hTM huT
  let uh : ↥M := ⟨u * (h : G) * u⁻¹, M.mul_mem (M.mul_mem huM h.2) (M.inv_mem huM)⟩
  have huh : (uh : G) = u * (h : G) * u⁻¹ := rfl
  have huhmap : (uh : G) ∈ (conjJoin L S).map (MulAut.conj u).toMonoidHom :=
    Subgroup.mem_map.2 ⟨(h : G), hD, by simp [huh, MulAut.conj_apply]⟩
  have hcomm : uc22p21cPi M h * uc22p21cPi M uh =
      uc22p21cPi M uh * uc22p21cPi M h :=
    barImage_conjJoin_commute hL hTM hT₁S hST huT huS (uc22p21cPi M h)
      (uc22p21c_mem_barImage.2 ⟨h, hD, rfl⟩) (uc22p21cPi M uh)
      (uc22p21c_mem_barImage.2 ⟨uh, huhmap, rfl⟩)
  refine ⟨uh, huh, hcomm, ?_⟩
  have h1 := uc22p22u_commutator_mem_pCoreOf (X := M) (a := (h : G)) (b := (uh : G))
    h.2 uh.2 (by simpa using hcomm)
  rwa [commutatorElement_def] at h1

private theorem torusWitness_step {M T L S : Subgroup G} (hL : L ∈ calC M) (hTM : T ≤ M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hP : TorusWitness M T L r S)
    (hO : pCoreOf 2 M ≤ S) {u : G} (huT : u ∈ T) (huS : u ∉ S)
    (huN : u ∈ normalizer (S : Set G)) (hu2 : u ^ 2 ∈ S) :
    TorusWitness M T L r (S ⊔ Subgroup.zpowers u) := by
  obtain ⟨hT₁S, hST, h, hD, horder, hN, hnc⟩ := hP
  obtain ⟨uh, huh, hcomm, hcommS0⟩ :=
    torusWitness_step_commute hL hTM hT₁S hST hD huT huS
  have hcommS : (h : G) * (uh : G) * (h : G)⁻¹ * (uh : G)⁻¹ ∈ S := hO hcommS0
  have huhmap : (uh : G) ∈ (conjJoin L S).map (MulAut.conj u).toMonoidHom :=
    Subgroup.mem_map.2 ⟨(h : G), hD, by simp [huh, MulAut.conj_apply]⟩
  obtain ⟨d, hdD, hdN, hdEq⟩ := mem_conjJoin_mul_conj hTM huh hD hN huT huS huN hu2 hcommS
  have horderPiH : orderOf (uc22p21cPi M h) = r :=
    uc22ine229_orderOf_mk h hr hr2 horder
  have horderU : orderOf uh = r := by
    rw [← Subgroup.orderOf_coe uh, huh]
    rw [← MulAut.conj_apply, (MulAut.conj u).orderOf_eq, Subgroup.orderOf_coe]
    exact horder
  have horderPiU : orderOf (uc22p21cPi M uh) = r :=
    uc22ine229_orderOf_mk uh hr hr2 horderU
  have hLD : barImage M L ≤ barImage M (conjJoin L S) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M (le_conjJoin_self L S))
  have hC : uc22p21cPi M uh ∈
      Subgroup.centralizer (barImage M L : Set (Bar2 M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact barImage_conjJoin_commute hL hTM hT₁S hST huT huS a (hLD ha) (uc22p21cPi M uh)
      (uc22p21c_mem_barImage.2 ⟨uh, huhmap, rfl⟩)
  have hncC : uc22p21cPi M h ∉
      Subgroup.centralizer (barImage M L : Set (Bar2 M)) := by
    intro hmem
    exact hnc fun a ha => (Subgroup.mem_centralizer_iff.mp hmem a ha).symm
  obtain ⟨hdorder, hdnc⟩ :=
    orderOf_mul_not_mem_centralizer hr hr2 hdEq horderPiH horderPiU hcomm hC hncC
  obtain ⟨h', h'D, h'order, h'N, h'nc⟩ :=
    exists_pow_mem_normalizer_not_mem_centralizer hr hr2 hdD hdN hdorder hdnc
  refine ⟨hT₁S.trans le_sup_left, sup_le hST (Subgroup.zpowers_le.2 huT),
    ⟨h', h'D, h'order, h'N, ?_⟩⟩
  intro hcent
  exact h'nc (Subgroup.mem_centralizer_iff.2 fun a ha => (hcent a ha).symm)

private theorem torusWitness_base {M T L : Subgroup G} (hL : L ∈ calC M) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hone : ∃ x ∈ L, orderOf x = r ∧
      x ∈ normalizer ((T ⊓ normalizer (L : Set G) : Subgroup G) : Set G)) :
    TorusWitness M T L r (T ⊓ normalizer (L : Set G) : Subgroup G) := by
  obtain ⟨x, hxL, hxo, hxN⟩ := hone
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hxM : x ∈ M := hLM hxL
  refine ⟨le_rfl, inf_le_left, ⟨⟨x, hxM⟩, ?_, ?_, ?_, ?_⟩⟩
  · exact le_conjJoin_self L _ hxL
  · rw [← Subgroup.orderOf_coe]
    exact hxo
  · exact hxN
  · intro hcent
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
    have hxbar : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M L :=
      uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hxL, rfl⟩
    let y : Bar2 L := e.symm ⟨uc22p21cPi M ⟨x, hxM⟩, hxbar⟩
    have hy : y ∈ center (Bar2 L) := by
      refine Subgroup.mem_center_iff.2 fun z => ?_
      apply e.injective
      calc e (z * y) = e z * e y := map_mul e z y
        _ = e z * ⟨uc22p21cPi M ⟨x, hxM⟩, hxbar⟩ := by rw [e.apply_symm_apply]
        _ = ⟨uc22p21cPi M ⟨x, hxM⟩, hxbar⟩ * e z := by
              ext
              exact (hcent (e z) (e z).2).symm
        _ = e y * e z := by rw [e.apply_symm_apply]
        _ = e (y * z) := (map_mul e y z).symm
    have hyo : orderOf y = r := by
      rw [show orderOf y = orderOf (e y) from (MulEquiv.orderOf_eq e y).symm,
        e.apply_symm_apply, ← Subgroup.orderOf_coe]
      exact uc22ine229_orderOf_mk ⟨x, hxM⟩ hr hr2 (by rw [← Subgroup.orderOf_coe]; exact hxo)
    exact hZ (by
      have h := Subgroup.orderOf_dvd_natCard (center (Bar2 L)) hy
      rwa [hyo] at h)

private theorem torusWitness_top {M T L : Subgroup G} (hT : IsSylowOf 2 T M)
    (hL : L ∈ calC M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hO : pCoreOf 2 M ≤ T ⊓ normalizer (L : Set G))
    (hP : TorusWitness M T L r (T ⊓ normalizer (L : Set G))) : TorusWitness M T L r T := by
  have hmain : ∀ n, ∀ S : Subgroup G, TorusWitness M T L r S → Nat.card T - Nat.card S = n →
      TorusWitness M T L r T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hS hn
      by_cases hSeq : S = T
      · simpa [hSeq] using hS
      · have hT₁S := hS.1
        have hST := hS.2.1
        have hlt : S < T := lt_of_le_of_ne hST hSeq
        obtain ⟨u, huT, huN, huS, hu2⟩ :=
          CFSG.EvenSporadicStandard.HNRecog.Harada.exists_mem_normalizer_sq_mem
            hT.isPGroup hlt
        have hS' := torusWitness_step hL hT.le hr hr2 hS (hO.trans hT₁S) huT huS huN hu2
        have hcard : Nat.card T - Nat.card (S ⊔ Subgroup.zpowers u : Subgroup G) <
            Nat.card T - Nat.card S := by
          have hlt' : S < (S ⊔ Subgroup.zpowers u : Subgroup G) := by
            refine lt_of_le_of_ne le_sup_left ?_
            intro heq
            exact huS (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
          have hc := Subgroup.card_lt_of_lt hlt'
          have hle : Nat.card (S ⊔ Subgroup.zpowers u : Subgroup G) ≤ Nat.card T :=
            Subgroup.card_le_of_le hS'.2.1
          omega
        have hcardn : Nat.card T - Nat.card (S ⊔ Subgroup.zpowers u : Subgroup G) < n := by
          omega
        exact ih _ hcardn (S ⊔ Subgroup.zpowers u : Subgroup G) hS' rfl
  exact hmain _ (T ⊓ normalizer (L : Set G)) hP rfl

theorem exists_mem_conjClosure_orderOf_mem_normalizer {M T L : Subgroup G}
    (hT : IsSylowOf 2 T M) (hL : L ∈ calC M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hone : ∃ x ∈ L, orderOf x = r ∧
      x ∈ normalizer ((T ⊓ normalizer (L : Set G) : Subgroup G) : Set G)) :
    ∃ x ∈ conjClosure M L, orderOf x = r ∧ x ∈ normalizer (T : Set G) := by
  have hO : pCoreOf 2 M ≤ T ⊓ normalizer (L : Set G) := by
    refine le_inf ?_ (uc22p22u_pCore_normalizes_calC hL)
    obtain ⟨Q, hQ⟩ := hT
    rw [← hQ]
    exact map_mono (CFSG.fitting_pCore_le_sylow Q)
  obtain ⟨-, -, h, hD, horder, hN, -⟩ :=
    torusWitness_top hT hL hr hr2 hO (torusWitness_base hL hr hr2 hZ hone)
  exact ⟨(h : G), conjJoin_le_conjClosure M L T hT.le hD,
    by rw [Subgroup.orderOf_coe]; exact horder, hN⟩

theorem s21_15Torus_of_szHone (D : Data G) (Ch : Choice2011 G)
    (hSz : ∀ {L T₀ : Subgroup G} {n r : ℕ}, IsSz (Bar2 L) n → IsPGroup 2 T₀ →
      T₀ ≤ normalizer (L : Set G) → IsSylowOf 2 (T₀ ⊓ L) L → r.Prime → r ∣ 2 ^ n - 1 →
        ∃ x ∈ L, orderOf x = r ∧ x ∈ normalizer (T₀ : Set G)) :
    S21_15Torus D Ch := by
  intro hH c L hL n hshape hne s hs hsn r hr hrs
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hT₁ : IsPGroup 2 (D.T ⊓ normalizer (L : Set G) : Subgroup G) :=
    D.sylowM.isPGroup.to_le inf_le_left
  have hTL : IsSylowOf 2 ((D.T ⊓ normalizer (L : Set G) : Subgroup G) ⊓ L) L := by
    rw [inf_assoc, inf_eq_right.2 (le_normalizer : L ≤ normalizer (L : Set G))]
    exact uc22p2214_isSylowOf_inf D.sylowM hL.1
  have hone : ∃ x ∈ L, orderOf x = r ∧
      x ∈ normalizer ((D.T ⊓ normalizer (L : Set G) : Subgroup G) : Set G) := by
    rcases hshape with hX | hX
    · exact uc22ine229_exists_mem_normalizer_of_isL2 hT₁ inf_le_right hTL hX hs hsn hr hrs
    · exact hSz hX hT₁ inf_le_right hTL hr (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
  have hZ : ¬ r ∣ Nat.card (center (Bar2 L)) := by
    rcases hshape with hX | hX
    · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
      rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.card_bot]
      exact hr.not_dvd_one
    · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
      rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.card_bot]
      exact hr.not_dvd_one
  obtain ⟨x, hxcl, hxo, hxN⟩ :=
    exists_mem_conjClosure_orderOf_mem_normalizer D.sylowM hL hr hr2 hZ hone
  refine ⟨Subgroup.zpowers x, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hxo]
  · exact (Subgroup.zpowers_le.2 hxcl).trans
      (conjClosure_le_of_le (CFSG.Quasithin.A3.subnormal_le hL.1))
  · exact Subgroup.zpowers_le.2 hxN

end CFSG.LocalAnalysis.UniquenessCase.UC22
