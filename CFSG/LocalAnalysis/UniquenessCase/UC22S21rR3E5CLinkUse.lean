module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.ClassicalGroups.PCoreSection
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_link_conj {X L K : Subgroup G} (hLX : L ≤ X) (hKX : K ≤ X)
    (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥X) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥X) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {b : G} (hbX : b ∈ normalizer (X : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer (K : Set G)) (z : Bar2 X) :
    e (UC6S846.rhoL X ⟨b, hbX⟩ z) =
      (UC6S846.rhoL L ⟨b, hbL⟩ (e z).1, UC6S846.rhoL K ⟨b, hbK⟩ (e z).2) := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e z).1
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e z).2
  have hxl : e (QuotientGroup.mk (⟨(l : G), hLX l.2⟩ : ↥X)) = (QuotientGroup.mk l, 1) := by
    simpa using heL (⟨(l : G), hLX l.2⟩ : ↥X) l.2
  have hxk : e (QuotientGroup.mk (⟨(k : G), hKX k.2⟩ : ↥X)) = (1, QuotientGroup.mk k) := by
    simpa using heK (⟨(k : G), hKX k.2⟩ : ↥X) k.2
  have hz : QuotientGroup.mk (⟨(l : G), hLX l.2⟩ : ↥X) *
      QuotientGroup.mk (⟨(k : G), hKX k.2⟩ : ↥X) = z := by
    apply e.injective
    rw [map_mul, hxl, hxk]
    simp [hl, hk]
  have hbl : ((Subgroup.normalizerMonoidHom X ⟨b, hbX⟩
      (⟨(l : G), hLX l.2⟩ : ↥X) : ↥X) : G) ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp hbL (l : G)).mp l.2
    simpa using h
  have hbk : ((Subgroup.normalizerMonoidHom X ⟨b, hbX⟩
      (⟨(k : G), hKX k.2⟩ : ↥X) : ↥X) : G) ∈ K := by
    have h := (Subgroup.mem_normalizer_iff.mp hbK (k : G)).mp k.2
    simpa using h
  rw [← hl, ← hk, ← hz, map_mul (UC6S846.rhoL X ⟨b, hbX⟩), UC6S846.rhoL_mk,
    UC6S846.rhoL_mk, map_mul e, heL _ hbl, heK _ hbk]
  simp only [Prod.mk_mul_mk, mul_one, one_mul, UC6S846.rhoL_mk]
  exact Prod.ext (congrArg QuotientGroup.mk (Subtype.ext (by simp [UC6S846.rhoL_mk_coe])))
    (congrArg QuotientGroup.mk (Subtype.ext (by simp [UC6S846.rhoL_mk_coe])))

theorem uc22r3e5c_link_mem_of_snd_eq_one {X L K : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥X) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    {x : ↥X} (hx : (e (QuotientGroup.mk x)).2 = 1)
    (hodd : Nat.Coprime (orderOf (x : G)) 2) : (x : G) ∈ L := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk x)).1
  have hxl : e (QuotientGroup.mk (⟨(l : G), hLX l.2⟩ : ↥X)) = e (QuotientGroup.mk x) := by
    rw [heL (⟨(l : G), hLX l.2⟩ : ↥X) l.2]
    exact Prod.ext hl hx.symm
  have hq : QuotientGroup.mk (⟨(l : G), hLX l.2⟩ : ↥X) = QuotientGroup.mk x :=
    e.injective hxl
  have hmem : ((⟨(l : G), hLX l.2⟩ : ↥X)⁻¹ * x : ↥X) ∈ CFSG.pCore 2 ↥X :=
    QuotientGroup.eq.mp hq
  have hmemG : (l : G)⁻¹ * (x : G) ∈ pCoreOf 2 X := by
    have h := (CFSG.mem_openPCoreOf_iff ((⟨(l : G), hLX l.2⟩ : ↥X)⁻¹ * x)).mpr hmem
    simpa using h
  have hsup : (x : G) ∈ L ⊔ pCoreOf 2 X := by
    have h := Subgroup.mul_mem_sup (S := L) (T := pCoreOf 2 X) l.2 hmemG
    simpa using h
  exact CFSG.RankThree.PartTwo.Sec14.mem_left_of_coprime_of_isPGroup Nat.prime_two
    ((CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 X).trans hLXn)
    (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X) hsup hodd

theorem uc22r3e5c_link_mem_of_fst_eq_one {X L K : Subgroup G} (hKX : K ≤ X)
    (hKXn : X ≤ normalizer (K : Set G)) (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heK : ∀ (x : ↥X) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {x : ↥X} (hx : (e (QuotientGroup.mk x)).1 = 1)
    (hodd : Nat.Coprime (orderOf (x : G)) 2) : (x : G) ∈ K := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk x)).2
  have hxk : e (QuotientGroup.mk (⟨(k : G), hKX k.2⟩ : ↥X)) = e (QuotientGroup.mk x) := by
    rw [heK (⟨(k : G), hKX k.2⟩ : ↥X) k.2]
    exact Prod.ext hx.symm hk
  have hq : QuotientGroup.mk (⟨(k : G), hKX k.2⟩ : ↥X) = QuotientGroup.mk x :=
    e.injective hxk
  have hmem : ((⟨(k : G), hKX k.2⟩ : ↥X)⁻¹ * x : ↥X) ∈ CFSG.pCore 2 ↥X :=
    QuotientGroup.eq.mp hq
  have hmemG : (k : G)⁻¹ * (x : G) ∈ pCoreOf 2 X := by
    have h := (CFSG.mem_openPCoreOf_iff ((⟨(k : G), hKX k.2⟩ : ↥X)⁻¹ * x)).mpr hmem
    simpa using h
  have hsup : (x : G) ∈ K ⊔ pCoreOf 2 X := by
    have h := Subgroup.mul_mem_sup (S := K) (T := pCoreOf 2 X) k.2 hmemG
    simpa using h
  exact CFSG.RankThree.PartTwo.Sec14.mem_left_of_coprime_of_isPGroup Nat.prime_two
    ((CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 X).trans hKXn)
    (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X) hsup hodd

private theorem uc22r3e5c_map_le_of_isStable {Y C : Type} [Group Y] [Group C]
    (φ : Y →* C) {P : Subgroup Y} {αY : MulAut Y} {αC : MulAut C}
    (hP : P.map αY.toMonoidHom = P) (hconj : ∀ z : Y, φ (αY z) = αC (φ z))
    {DC : Subgroup C} (hE : P.map φ = DC) : DC.map αC.toMonoidHom ≤ DC := by
  rintro _ ⟨d, hd, rfl⟩
  have hd1 : d ∈ P.map φ := by rw [hE]; exact hd
  obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hd1
  have hw2 : αY w ∈ P := by
    rw [← hP]
    exact Subgroup.mem_map_of_mem αY.toMonoidHom hw
  have hmem : φ (αY w) ∈ DC := by
    rw [← hE]
    exact Subgroup.mem_map_of_mem φ hw2
  rwa [hconj, hw'] at hmem

private theorem uc22r3e5c_map_fst_snd_prod {A B : Type} [Group A] [Group B]
    (DA : Subgroup A) (DB : Subgroup B) :
    Subgroup.map (MonoidHom.fst A B) (DA.prod DB) = DA ∧
      Subgroup.map (MonoidHom.snd A B) (DA.prod DB) = DB := by
  constructor
  · refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hy
      rw [← hpy]
      exact (Subgroup.mem_prod.mp hp).1
    · intro d hd
      exact Subgroup.mem_map.mpr
        ⟨(d, 1), Subgroup.mem_prod.mpr ⟨hd, Subgroup.one_mem DB⟩, rfl⟩
  · refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hy
      rw [← hpy]
      exact (Subgroup.mem_prod.mp hp).2
    · intro d hd
      exact Subgroup.mem_map.mpr
        ⟨(1, d), Subgroup.mem_prod.mpr ⟨Subgroup.one_mem DA, hd⟩, rfl⟩

theorem uc22r3e5c_link_map_rhoL_eq {X L K : Subgroup G} (hLX : L ≤ X) (hKX : K ≤ X)
    (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥X) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥X) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {C : Subgroup G} {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hCe : (barImage X C).map e.toMonoidHom = DL.prod DK)
    {b : G} (hbX : b ∈ normalizer (X : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer (K : Set G))
    (hCb : (barImage X C).map (UC6S846.rhoL X ⟨b, hbX⟩).toMonoidHom = barImage X C) :
    DL.map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = DL ∧
      DK.map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom = DK := by
  have hlink : ∀ z : Bar2 X, e (UC6S846.rhoL X ⟨b, hbX⟩ z) =
      (UC6S846.rhoL L ⟨b, hbL⟩ (e z).1, UC6S846.rhoL K ⟨b, hbK⟩ (e z).2) :=
    fun z => uc22r3e5c_link_conj hLX hKX e heL heK hbX hbL hbK z
  obtain ⟨hfs, hsn⟩ := uc22r3e5c_map_fst_snd_prod DL DK
  have hE₁ : (barImage X C).map
      ((MonoidHom.fst (Bar2 L) (Bar2 K)).comp e.toMonoidHom) = DL := by
    rw [← Subgroup.map_map, hCe, hfs]
  have hE₂ : (barImage X C).map
      ((MonoidHom.snd (Bar2 L) (Bar2 K)).comp e.toMonoidHom) = DK := by
    rw [← Subgroup.map_map, hCe, hsn]
  have hleL : DL.map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom ≤ DL := by
    refine uc22r3e5c_map_le_of_isStable
      ((MonoidHom.fst (Bar2 L) (Bar2 K)).comp e.toMonoidHom) hCb (fun z => ?_) hE₁
    simpa [MonoidHom.comp_apply] using congrArg (MonoidHom.fst (Bar2 L) (Bar2 K)) (hlink z)
  have hleK : DK.map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom ≤ DK := by
    refine uc22r3e5c_map_le_of_isStable
      ((MonoidHom.snd (Bar2 L) (Bar2 K)).comp e.toMonoidHom) hCb (fun z => ?_) hE₂
    simpa [MonoidHom.comp_apply] using congrArg (MonoidHom.snd (Bar2 L) (Bar2 K)) (hlink z)
  exact ⟨Subgroup.eq_of_le_of_card_ge hleL
      (le_of_eq (Subgroup.card_map_of_injective (UC6S846.rhoL L ⟨b, hbL⟩).injective).symm),
    Subgroup.eq_of_le_of_card_ge hleK
      (le_of_eq (Subgroup.card_map_of_injective (UC6S846.rhoL K ⟨b, hbK⟩).injective).symm)⟩

theorem uc22r3e5c_eq_one_of_mk_eq_one {X C : Subgroup G} (hCodd : Odd (Nat.card C))
    {x : ↥X} (hxC : (x : G) ∈ C) (h : (QuotientGroup.mk x : Bar2 X) = 1) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpc : x ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff x).mp h
  have hpcG : (x : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff x).mpr hpc
  have hbot : C ⊓ pCoreOf 2 X = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨n, hn⟩ := (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hCodd).pow_right n
  have hinf : (x : G) ∈ C ⊓ pCoreOf 2 X := Subgroup.mem_inf.mpr ⟨hxC, hpcG⟩
  rw [hbot] at hinf
  exact Subtype.ext (by simpa using hinf)

end CFSG.LocalAnalysis.UniquenessCase.UC22
