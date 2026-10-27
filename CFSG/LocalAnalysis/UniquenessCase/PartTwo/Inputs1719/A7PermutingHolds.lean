module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur
public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26bProof
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerThreeCycle
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOrderThreeKleinFourThreeCycle
public import CFSG.Dihedral.GorensteinWalter.ASevenNormalizerCosetData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenCubeEqOneOfPowNine
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.SylowInfNormal
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open BenderSuzuki.PFAppendixIII

theorem a7_centralizer_involution_card
    (u : alternatingGroup (Fin 7)) (hu : IsInvolution u) :
    Nat.card (Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7)))) = 24 := by
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.aSeven_involutions_conjugate u
    CFSG.GorensteinWalter.a7t hu CFSG.GorensteinWalter.a7t_involution
  have he : MulAut.conj g u = CFSG.GorensteinWalter.a7t := by
    simpa [MulAut.conj_apply] using hg
  have hmap : (Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7)))).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({CFSG.GorensteinWalter.a7t} : Set (alternatingGroup (Fin 7))) := by
    rw [CFSG.centralizer_singleton_map, he]
  have hcard := congrArg (fun H : Subgroup (alternatingGroup (Fin 7)) => Nat.card H) hmap
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    CFSG.GorensteinWalter.a7t_centralizer_card] at hcard
  exact hcard

theorem a7_centralizer_involution_unique_order_three
    (u : alternatingGroup (Fin 7)) (hu : IsInvolution u)
    (U₁ U₂ : Subgroup (alternatingGroup (Fin 7)))
    (h₁ : Nat.card U₁ = 3)
    (h₁c : U₁ ≤ Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7))))
    (h₂ : Nat.card U₂ = 3)
    (h₂c : U₂ ≤ Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7)))) :
    U₁ = U₂ := by
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.aSeven_involutions_conjugate u
    CFSG.GorensteinWalter.a7t hu CFSG.GorensteinWalter.a7t_involution
  let e : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := MulAut.conj g
  have he : e u = CFSG.GorensteinWalter.a7t := by
    simpa [e, MulAut.conj_apply] using hg
  have hzcard : Nat.card (Subgroup.zpowers CFSG.GorensteinWalter.a7a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  have key : ∀ U : Subgroup (alternatingGroup (Fin 7)), Nat.card U = 3 →
      U ≤ Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7))) →
      U.map e.toMonoidHom = Subgroup.zpowers CFSG.GorensteinWalter.a7a := by
    intro U hU hUc
    have hU'c : U.map e.toMonoidHom ≤
        Subgroup.centralizer ({CFSG.GorensteinWalter.a7t} :
          Set (alternatingGroup (Fin 7))) := by
      have hmap := Subgroup.map_mono hUc (f := e.toMonoidHom)
      rwa [CFSG.centralizer_singleton_map e u, he] at hmap
    have hodd : ∀ x ∈ U.map e.toMonoidHom, Odd (orderOf x) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hdvd : orderOf y ∣ 3 := by
        rw [← hU]
        exact Subgroup.orderOf_dvd_natCard U hy
      have hord : orderOf (e.toMonoidHom y) = orderOf y := MulEquiv.orderOf_eq e y
      rw [hord]
      exact Odd.of_dvd_nat (by norm_num) hdvd
    have hle := CFSG.GorensteinWalter.aSeven_odd_subgroup_centralizing_a7t_le_zpowers
      hodd hU'c
    have hcard' : Nat.card (U.map e.toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective e.injective, hU]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard', hzcard])
  have hmap_eq : U₁.map e.toMonoidHom = U₂.map e.toMonoidHom := by
    rw [key U₁ h₁ h₁c, key U₂ h₂ h₂c]
  exact Subgroup.map_injective e.injective hmap_eq

theorem a7_normalizer_zpowers_card_of_commutes_involution
    (u z : alternatingGroup (Fin 7)) (hu : IsInvolution u) (hz : orderOf z = 3)
    (hcomm : u * z = z * u) :
    Nat.card (Subgroup.normalizer
      (Subgroup.zpowers z : Set (alternatingGroup (Fin 7)))) = 72 := by
  have hUcard : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hz]
  have hUcent : Subgroup.zpowers z ≤
      Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute u z := hcomm
    exact (hc.zpow_right k).eq.symm
  obtain ⟨V, hVK, hVcentU, -⟩ :=
    CFSG.GorensteinWalter.aSeven_exists_kleinFour_centralizing_card_three_of_centralizes_involution
      u hu (Subgroup.zpowers z) hUcard hUcent
  have hVcentz : V ≤ Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hVcentU
    exact hVcentU
  have hz3 : Equiv.Perm.IsThreeCycle (z : Equiv.Perm (Fin 7)) :=
    CFSG.GorensteinWalter.aSeven_isThreeCycle_of_order_three_and_kleinFour_centralizer
      z hz V hVK hVcentz
  have ha3 : Equiv.Perm.IsThreeCycle
      (CFSG.GorensteinWalter.a7a : Equiv.Perm (Fin 7)) := by
    have heq : (CFSG.GorensteinWalter.a7a : Equiv.Perm (Fin 7)) =
        Equiv.swap (5 : Fin 7) 4 * Equiv.swap 5 6 := by
      rw [show (CFSG.GorensteinWalter.a7a : Equiv.Perm (Fin 7)) =
        Equiv.swap (4 : Fin 7) 5 * Equiv.swap 5 6 from rfl, Equiv.swap_comm 4 5]
    rw [heq]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have h5 : 5 ≤ Nat.card (Fin 7) := by simp
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (alternatingGroup.isThreeCycle_isConj h5 hz3 ha3)
  let e : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := MulAut.conj g
  have he : e z = CFSG.GorensteinWalter.a7a := by
    simpa [e, MulAut.conj_apply] using hg
  have hmap := Subgroup.map_equiv_normalizer_eq (Subgroup.zpowers z) e
  have hmapz : (Subgroup.zpowers z).map e.toMonoidHom =
      Subgroup.zpowers CFSG.GorensteinWalter.a7a := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (e z) = Subgroup.zpowers CFSG.GorensteinWalter.a7a
    rw [he]
  have hcard := congrArg (fun H : Subgroup (alternatingGroup (Fin 7)) => Nat.card H) hmap
  rw [Subgroup.card_map_of_injective e.injective, hmapz] at hcard
  have h72 : Nat.card (Subgroup.normalizer
      (Subgroup.zpowers CFSG.GorensteinWalter.a7a :
        Set (alternatingGroup (Fin 7)))) = 72 := by
    rw [← CFSG.GorensteinWalter.a7U_eq_zpowers]
    exact CFSG.GorensteinWalter.a7ThreeNormalizer_card
  rwa [h72] at hcard

theorem k_A7Permuting_holds :
    K_A7Permuting := by
  intro Y _ _ K S hKY hA
  classical
  obtain ⟨hKN, hKq, hZodd, hCent, ⟨a, hKindex⟩, hSylY⟩ := hKY
  let eA := Classical.choice hA
  have hA7card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hKcard : Nat.card ↥K = Nat.card (Subgroup.center ↥K) * 2520 := by
    have h := Subgroup.card_mul_index (H := Subgroup.center ↥K)
    rw [Subgroup.index_eq_card, Nat.card_congr eA.toEquiv, hA7card] at h
    exact h.symm
  set T : Subgroup Y := S ⊓ K with hTdef
  have hTle : T ≤ K := inf_le_right
  have hTS : T ≤ S := inf_le_left
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 T K := by
    have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hSylY
    have h := CFSG.isSylowTwoOf_inf_of_normal (S := S) (X := ⊤) (N := K) hS'
      (le_top : K ≤ ⊤) (by rw [Subgroup.normalizer_eq_top_iff.mpr hKN])
    have h' : CFSG.Quasithin.IsSylowIn 2 (K ⊓ S) K := by
      refine ⟨h.1, h.2.1, ?_⟩
      simpa [Subgroup.relIndex] using h.2.2
    simpa [T, inf_comm] using h'
  have hTcard : Nat.card T = 8 := by
    rw [CFSG.Quasithin.IsSylowIn.card_eq hTsyl]
    have hfac : (Nat.card ↥K).factorization 2 = 3 := by
      rw [hKcard]
      rw [Nat.factorization_mul (a := Nat.card ↥(Subgroup.center ↥K)) (b := 2520)
        (Nat.card_pos (α := ↥(Subgroup.center ↥K))).ne' (by norm_num : (2520 : ℕ) ≠ 0)]
      rw [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hZodd.not_two_dvd_nat,
        CFSG.GorensteinWalter.factorization_two_2520, zero_add]
    rw [hfac]
    norm_num
  have hTne : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hTcard
    norm_num at hTcard
  have hTp : IsPGroup 2 T := hTsyl.isPGroup
  have hST : S ≤ Subgroup.normalizer (T : Set Y) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxS, hxK⟩
      exact ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), hKN.conj_mem x hxK s⟩
    · intro hx
      have hmem : s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ ∈ T :=
        ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hx.1) (S.inv_mem (S.inv_mem hs)),
          by simpa using hKN.conj_mem (s * x * s⁻¹) hx.2 s⁻¹⟩
      have heq : s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ = x := by group
      rwa [heq] at hmem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hnT, hn1, hncomm⟩ :=
    CFSG.GroupTheory.WielandtProduct.exists_mem_commute_of_le_of_isPGroup
      hSylY.isPGroup hTS hST hTne
  obtain ⟨t, htmem, htord, -⟩ :=
    CFSG.GroupTheory.WielandtProduct.exists_orderOf_eq_commute_of_isPGroup
      (hTp.to_le (Subgroup.zpowers_le.mpr hnT))
      (fun h => hn1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers n)))
  have htT : t ∈ T := Subgroup.zpowers_le.mpr hnT htmem
  have htcentS : ∀ s ∈ S, t * s = s * t := by
    intro s hs
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp htmem
    exact (Commute.zpow_left (hncomm s hs) i).eq
  have htcentT : ∀ y ∈ T, t * y = y * t := fun y hy => htcentS y (hTS hy)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    norm_num at htord
  let tK : ↥K := ⟨t, htT.2⟩
  have htKord : orderOf tK = 2 := by
    rw [← Subgroup.orderOf_coe tK, htord]
  have htK2 : tK ^ 2 = 1 := by
    rw [← htKord]
    exact pow_orderOf_eq_one tK
  let conjK (s : Y) : ↥K ≃* ↥K :=
    { toFun := fun x => ⟨s * (x : Y) * s⁻¹, hKN.conj_mem x x.2 s⟩
      invFun := fun x => ⟨s⁻¹ * (x : Y) * s, by simpa using hKN.conj_mem x x.2 s⁻¹⟩
      left_inv := by
        intro x
        ext
        group
      right_inv := by
        intro x
        ext
        group
      map_mul' := by
        intro x y
        ext
        simp [mul_assoc] }
  have hconjK_coe (s : Y) (x : ↥K) : ((conjK s x : ↥K) : Y) = s * (x : Y) * s⁻¹ := rfl
  rcases CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15k_schur_alt_seven hKq hZodd hA with
    hAlt | hZ3
  ·
    obtain ⟨eK⟩ := hAlt
    let u : alternatingGroup (Fin 7) := eK tK
    have hu : IsInvolution u := by
      refine ⟨?_, ?_⟩
      · intro h
        apply ht1
        have h1 : tK = 1 := eK.injective (by simpa [u] using h)
        exact congrArg Subtype.val h1
      · show u ^ 2 = 1
        rw [show u = eK tK from rfl, ← map_pow, htK2, map_one]
    have hCcard : Nat.card (Subgroup.centralizer ({tK} : Set ↥K)) = 24 := by
      have hmap := CFSG.centralizer_singleton_map eK tK
      have hcard := congrArg (fun H : Subgroup (alternatingGroup (Fin 7)) => Nat.card H) hmap
      rw [Subgroup.card_map_of_injective eK.injective] at hcard
      rw [hcard]
      exact a7_centralizer_involution_card u hu
    obtain ⟨zC, hzCord⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.centralizer ({tK} : Set ↥K)) 3 (by rw [hCcard]; norm_num)
    let zK : ↥K := (zC : Subgroup.centralizer ({tK} : Set ↥K))
    have hzKord : orderOf zK = 3 := (Subgroup.orderOf_coe zC).trans hzCord
    have hzKcomm : zK * tK = tK * zK :=
      Subgroup.mem_centralizer_singleton_iff.mp zC.2
    let QK : Subgroup ↥K := Subgroup.zpowers zK
    have hQKcard : Nat.card QK = 3 := by
      rw [Nat.card_zpowers, hzKord]
    have hQKcent : QK ≤ Subgroup.centralizer ({tK} : Set ↥K) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left hzKcomm i).eq
    have huniq3 : ∀ U : Subgroup ↥K, Nat.card U = 3 →
        U ≤ Subgroup.centralizer ({tK} : Set ↥K) → U = QK := by
      intro U hU hUc
      have hmapU : U.map eK.toMonoidHom ≤
          Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7))) := by
        have h := Subgroup.map_mono hUc (f := eK.toMonoidHom)
        rwa [CFSG.centralizer_singleton_map eK tK] at h
      have hmapQ : QK.map eK.toMonoidHom ≤
          Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7))) := by
        have h := Subgroup.map_mono hQKcent (f := eK.toMonoidHom)
        rwa [CFSG.centralizer_singleton_map eK tK] at h
      have hcardU : Nat.card (U.map eK.toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective eK.injective, hU]
      have hcardQ : Nat.card (QK.map eK.toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective eK.injective, hQKcard]
      have heq := a7_centralizer_involution_unique_order_three u hu
        (U.map eK.toMonoidHom) (QK.map eK.toMonoidHom) hcardU hmapU hcardQ hmapQ
      exact Subgroup.map_injective eK.injective heq
    have hconjQ : ∀ s : Y, s * t = t * s → QK.map (conjK s).toMonoidHom = QK := by
      intro s hst
      have hleC : QK.map (conjK s).toMonoidHom ≤
          Subgroup.centralizer ({tK} : Set ↥K) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
        apply Subtype.ext
        have hqt : q * tK = tK * q := Subgroup.mem_centralizer_singleton_iff.mp (hQKcent hq)
        have hst' : s⁻¹ * t = t * s⁻¹ := (Commute.inv_left hst).eq
        change (s * (q : Y) * s⁻¹) * t = t * (s * (q : Y) * s⁻¹)
        calc (s * (q : Y) * s⁻¹) * t = s * (q : Y) * (s⁻¹ * t) := by group
          _ = s * (q : Y) * (t * s⁻¹) := by rw [hst']
          _ = s * ((q : Y) * t) * s⁻¹ := by group
          _ = s * (t * (q : Y)) * s⁻¹ := by
              rw [show (q : Y) * t = t * (q : Y) from congrArg Subtype.val hqt]
          _ = (s * t) * (q : Y) * s⁻¹ := by group
          _ = (t * s) * (q : Y) * s⁻¹ := by rw [hst]
          _ = t * (s * (q : Y) * s⁻¹) := by group
      have hcard' : Nat.card (QK.map (conjK s).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (conjK s).injective, hQKcard]
      have heq := huniq3 (QK.map (conjK s).toMonoidHom) hcard' hleC
      simpa [QK] using heq
    have hSnormalQ : S ≤ Subgroup.normalizer (QK.map K.subtype : Set Y) := by
      intro s hs
      have hQmap := hconjQ s (htcentS s hs).symm
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hcomp : (MulAut.conj s).toMonoidHom.comp K.subtype =
          K.subtype.comp (conjK s).toMonoidHom := by
        ext x
        exact (hconjK_coe s x).symm
      calc (QK.map K.subtype).map (MulAut.conj s).toMonoidHom
          = (QK.map (conjK s).toMonoidHom).map K.subtype := by
              rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
        _ = QK.map K.subtype := by rw [hQmap]
    have hNcard : Nat.card (Subgroup.normalizer (QK : Set ↥K)) = 72 := by
      have hmap := Subgroup.map_equiv_normalizer_eq QK eK
      have hmapQ : QK.map eK.toMonoidHom = Subgroup.zpowers (eK zK) := by
        rw [MonoidHom.map_zpowers]
        rfl
      have hcard := congrArg (fun H : Subgroup (alternatingGroup (Fin 7)) => Nat.card H) hmap
      rw [Subgroup.card_map_of_injective eK.injective, hmapQ] at hcard
      rw [hcard]
      refine a7_normalizer_zpowers_card_of_commutes_involution u (eK zK) hu ?_ ?_
      · rw [MulEquiv.orderOf_eq, hzKord]
      · have h := congrArg eK hzKcomm
        simp only [map_mul, u] at h
        exact h.symm
    let NK : Subgroup Y := (Subgroup.normalizer (QK : Set ↥K)).map K.subtype
    have hNKK : NK ≤ K := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hNKcard : Nat.card NK = 72 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hNcard]
    have hTleNK : T ≤ NK := by
      intro y hyT
      have hyK : y ∈ K := hTle hyT
      have hcomm : y * t = t * y := (htcentT y hyT).symm
      have hQmap := hconjQ y hcomm
      have hconjKeq : conjK y = MulAut.conj (⟨y, hyK⟩ : ↥K) := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        rfl
      rw [hconjKeq] at hQmap
      have hyN : (⟨y, hyK⟩ : ↥K) ∈ Subgroup.normalizer (QK : Set ↥K) :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hQmap
      exact Subgroup.mem_map.mpr ⟨⟨y, hyK⟩, hyN, rfl⟩
    have hSnormalNK : S ≤ Subgroup.normalizer (NK : Set Y) := by
      intro s hs
      have hQmap := hconjQ s (htcentS s hs).symm
      have hNmap : (Subgroup.normalizer (QK : Set ↥K)).map (conjK s).toMonoidHom =
          Subgroup.normalizer (QK : Set ↥K) := by
        rw [Subgroup.map_equiv_normalizer_eq, hQmap]
      have hcompNK : (MulAut.conj s).toMonoidHom.comp K.subtype =
          K.subtype.comp (conjK s).toMonoidHom := by
        ext x
        exact (hconjK_coe s x).symm
      have hNmapY : NK.map (MulAut.conj s).toMonoidHom = NK := by
        calc NK.map (MulAut.conj s).toMonoidHom
            = ((Subgroup.normalizer (QK : Set ↥K)).map (conjK s).toMonoidHom).map K.subtype := by
                rw [show NK = (Subgroup.normalizer (QK : Set ↥K)).map K.subtype from rfl,
                  Subgroup.map_map, hcompNK, ← Subgroup.map_map]
          _ = NK := by rw [hNmap]
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hNKinfS : NK ⊓ S = T := by
      refine le_antisymm ?_ ?_
      · calc NK ⊓ S ≤ K ⊓ S :=
            le_inf (inf_le_left.trans hNKK) inf_le_right
          _ = T := by rw [inf_comm, hTdef]
      · exact le_inf hTleNK hTS
    have hPcard : Nat.card ↥(NK ⊔ S) = 9 * Nat.card S := by
      have hform :=
        CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := S) (K := NK) hSnormalNK
      rw [inf_comm, hNKinfS, hNKcard, hTcard] at hform
      have h1 : Nat.card ↥(S ⊔ NK) * 8 = Nat.card S * 72 := hform
      have h2 : Nat.card ↥(S ⊔ NK) = 9 * Nat.card S := by omega
      rwa [sup_comm] at h2
    obtain ⟨E₀, hE₀card⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2)
      (by rw [hNKcard]; norm_num : 3 ^ 2 ∣ Nat.card ↥NK)
    let E : Subgroup Y := E₀.map NK.subtype
    have hEcard : Nat.card E = 9 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE₀card]
      norm_num
    have hEleNK : E ≤ NK := by
      dsimp [E]
      calc E₀.map NK.subtype ≤ (⊤ : Subgroup ↥NK).map NK.subtype := Subgroup.map_mono le_top
        _ = NK := by rw [Subgroup.map_top, Subgroup.range_subtype]
    have hEleK : E ≤ K := hEleNK.trans hNKK
    have hEinfS : E ⊓ S = ⊥ := by
      have h1 : Nat.card ↥(E ⊓ S) ∣ 9 := by
        rw [← hEcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(E ⊓ S) ∣ 8 := by
        have hle : E ⊓ S ≤ T := by
          calc E ⊓ S ≤ K ⊓ S := le_inf (inf_le_left.trans hEleK) inf_le_right
            _ = T := by rw [inf_comm, hTdef]
        rw [← hTcard]
        exact Subgroup.card_dvd_of_le hle
      have hdvd : Nat.card ↥(E ⊓ S) ∣ 1 := by
        have := Nat.dvd_gcd h1 h2
        simpa using this
      exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)
    have hE_exp : ∀ x ∈ E, x ^ 3 = 1 := by
      intro x hx
      have hxK : x ∈ K := hEleK hx
      let xK : ↥K := ⟨x, hxK⟩
      have hxK9 : xK ^ 9 = 1 := by
        apply Subtype.ext
        have hdvd : orderOf x ∣ 9 := by
          rw [← hEcard]
          exact Subgroup.orderOf_dvd_natCard E hx
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hx9 : (eK xK) ^ 9 = 1 := by
        rw [← map_pow, hxK9, map_one]
      have hx3 : (eK xK) ^ 3 = 1 :=
        CFSG.GorensteinWalter.a7_cube_eq_one_of_pow_nine (eK xK) hx9
      have hxK3 : xK ^ 3 = 1 := eK.injective (by rw [map_pow, hx3, map_one])
      exact congrArg Subtype.val hxK3
    have hE_nc : ¬ IsCyclic ↥E := by
      intro hcyc
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
      have hgord : orderOf g = 9 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg, hEcard]
      have hg3 : orderOf g ∣ 3 := by
        rw [← Subgroup.orderOf_coe g]
        exact orderOf_dvd_iff_pow_eq_one.mpr (hE_exp (g : Y) g.2)
      have h93 : (9 : ℕ) ∣ 3 := hgord ▸ hg3
      norm_num at h93
    have hEne : E ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hEcard
      norm_num at hEcard
    refine ⟨E, hEleK, hEne, ?_, hE_exp, hE_nc, ?_⟩
    · exact IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
    · refine CFSG.Quasithin.H.L3Wr.permute_of_card hEinfS ?_
      have hleP : E ⊔ S ≤ NK ⊔ S := sup_le (hEleNK.trans le_sup_left) le_sup_right
      have hEcardS : Nat.card ↥(E ⊔ S) ≤ Nat.card E * Nat.card S := by
        calc Nat.card ↥(E ⊔ S) ≤ Nat.card ↥(NK ⊔ S) :=
              Nat.card_le_card_of_injective (Subgroup.inclusion hleP)
                (Subgroup.inclusion_injective hleP)
          _ = 9 * Nat.card S := hPcard
          _ = Nat.card E * Nat.card S := by rw [hEcard]
      exact hEcardS

  ·

    obtain ⟨-, hZcard, hAltZ⟩ := hZ3
    let ZK : Subgroup ↥K := Subgroup.center ↥K
    have hZcard' : Nat.card ↥ZK = 3 := hZcard
    let π : ↥K →* (↥K ⧸ ZK) := QuotientGroup.mk' ZK
    let eZ : (↥K ⧸ ZK) ≃* alternatingGroup (Fin 7) := Classical.choice hAltZ
    let uZ : alternatingGroup (Fin 7) := eZ (π tK)
    have htKnotZK : tK ∉ ZK := by
      intro h
      have hdvd : orderOf tK ∣ Nat.card ↥ZK := Subgroup.orderOf_dvd_natCard ZK h
      rw [htKord, hZcard'] at hdvd
      norm_num at hdvd
    have huZ : IsInvolution uZ := by
      refine ⟨?_, ?_⟩
      · intro h
        have h1 : π tK = 1 := eZ.injective (by simpa [uZ] using h)
        exact htKnotZK ((QuotientGroup.eq_one_iff (N := ZK) (x := tK)).mp h1)
      · show uZ ^ 2 = 1
        rw [show uZ = eZ (π tK) from rfl, ← map_pow]
        have h2 : (π tK) ^ 2 = 1 := by
          rw [← map_pow, htK2, map_one]
        rw [h2, map_one]
    let W : Subgroup (↥K ⧸ ZK) :=
      Subgroup.centralizer ({π tK} : Set (↥K ⧸ ZK))
    have hCcardZ : Nat.card ↥W = 24 := by
      have hmap := CFSG.centralizer_singleton_map eZ (π tK)
      have hcard := congrArg (fun H : Subgroup (alternatingGroup (Fin 7)) => Nat.card H) hmap
      rw [Subgroup.card_map_of_injective eZ.injective] at hcard
      rw [hcard]
      exact a7_centralizer_involution_card uZ huZ
    obtain ⟨zbarC, hzbarCord⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 3
      (by rw [hCcardZ]; norm_num)
    let zbar : ↥K ⧸ ZK := (zbarC : ↥W)
    have hzbarord : orderOf zbar = 3 := (Subgroup.orderOf_coe zbarC).trans hzbarCord
    have hzbarcomm : zbar * π tK = π tK * zbar :=
      Subgroup.mem_centralizer_singleton_iff.mp zbarC.2
    obtain ⟨zK, hzKπ⟩ := QuotientGroup.mk'_surjective ZK zbar
    have hzK3Z : zK ^ 3 ∈ ZK := by
      rw [← QuotientGroup.eq_one_iff (N := ZK) (x := zK ^ 3)]
      change π (zK ^ 3) = 1
      rw [map_pow, hzKπ]
      simpa [hzbarord] using pow_orderOf_eq_one zbar
    have hKIsHat : CFSG.Quasithin.IsHat ↥K (alternatingGroup (Fin 7)) := by
      refine ⟨?_, hZcard', hAltZ⟩
      exact (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1.mpr hKq
    have hzK3 : zK ^ 3 = 1 := CFSG.Quasithin.H13.HatA7L.cube_eq_one hKIsHat hzK3Z
    have hzKnotZK : zK ∉ ZK := by
      intro h
      have h1 : π zK = 1 := (QuotientGroup.eq_one_iff (N := ZK) (x := zK)).mpr h
      rw [hzKπ] at h1
      rw [h1, orderOf_one] at hzbarord
      norm_num at hzbarord
    let c : ↥K := tK * zK * tK⁻¹ * zK⁻¹
    have hcZ : c ∈ ZK := by
      rw [← QuotientGroup.eq_one_iff (N := ZK) (x := c)]
      change π c = 1
      dsimp [c]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hzKπ]
      have hcomm : zbar * π tK = π tK * zbar := hzbarcomm
      rw [← hcomm]
      group
    have htKmul : tK * tK = 1 := by simpa [pow_two] using htK2
    have htKinv : tK⁻¹ = tK := inv_eq_of_mul_eq_one_left htKmul
    have htz_c : tK * zK * tK⁻¹ = c * zK := by
      dsimp [c]
      group
    have htKctK : tK * c * tK = c := by
      have hc := (Subgroup.mem_center_iff.mp hcZ) tK
      calc tK * c * tK = c * tK * tK := by rw [hc]
        _ = c := by rw [mul_assoc, htKmul, mul_one]
    have htz_eq' : tK * zK * tK = c * zK := by
      rwa [htKinv] at htz_c
    have hc' : tK * c = c * tK := Subgroup.mem_center_iff.mp hcZ tK
    have hc2 : c * c = 1 := by
      have h1 : c * c * zK = zK := by
        calc c * c * zK = c * (c * zK) := by group
          _ = c * (tK * zK * tK) := by rw [htz_eq']
          _ = (c * tK) * zK * tK := by group
          _ = (tK * c) * zK * tK := by rw [hc']
          _ = tK * (c * zK) * tK := by group
          _ = tK * (tK * zK * tK) * tK := by rw [htz_eq']
          _ = zK := by
              calc tK * (tK * zK * tK) * tK = (tK * tK) * zK * (tK * tK) := by group
                _ = zK := by rw [htKmul]; group
      have h1' : c * c * zK = 1 * zK := by rw [h1, one_mul]
      exact mul_right_cancel h1'
    have hc1 : c = 1 := by
      have hdvd2 : orderOf c ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hc2)
      have hdvd3 : orderOf c ∣ 3 := by
        rw [← hZcard']
        exact Subgroup.orderOf_dvd_natCard ZK hcZ
      have hdvd : orderOf c ∣ 1 := by
        have hg := Nat.dvd_gcd hdvd2 hdvd3
        have h23 : Nat.gcd 2 3 = 1 := by norm_num
        rwa [h23] at hg
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    have htz : tK * zK * tK⁻¹ = zK := by
      have hcz : c * zK = zK := by rw [hc1, one_mul]
      calc tK * zK * tK⁻¹ = (tK * zK * tK⁻¹ * zK⁻¹) * zK := by group
        _ = c * zK := rfl
        _ = zK := hcz
    have hzKcommtK : zK * tK = tK * zK := by
      have h1 : tK * zK * tK = zK := by
        rwa [htKinv] at htz
      have h2 := congrArg (fun x => tK * x) h1
      calc zK * tK = (tK * tK) * zK * tK := by rw [htKmul]; group
        _ = tK * (tK * zK * tK) := by group
        _ = tK * zK := h2
    have hzKne : zK ≠ 1 := by
      intro h
      exact hzKnotZK (by rw [h]; exact Subgroup.one_mem ZK)
    have hzKord : orderOf zK = 3 := orderOf_eq_prime hzK3 hzKne
    let EK : Subgroup ↥K := Subgroup.zpowers zK ⊔ ZK
    have hzpcard : Nat.card ↥(Subgroup.zpowers zK) = 3 := by
      rw [Nat.card_zpowers, hzKord]
    have hEKcard : Nat.card ↥EK = 9 := by
      have hinfcard : Nat.card ↥(Subgroup.zpowers zK ⊓ ZK) = 1 := by
        have h1 : Nat.card ↥(Subgroup.zpowers zK ⊓ ZK) ∣ 3 := by
          rw [← hzpcard]
          exact Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
        · exact h
        · exfalso
          have heq : Subgroup.zpowers zK ⊓ ZK = Subgroup.zpowers zK :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hzpcard])
          have hzmem : zK ∈ Subgroup.zpowers zK ⊓ ZK := by
            rw [heq]
            exact Subgroup.mem_zpowers zK
          exact hzKnotZK hzmem.2
      have hcen : ZK ≤ Subgroup.centralizer (Subgroup.zpowers zK : Set ↥K) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact Subgroup.mem_center_iff.mp hz y
      have hnorm : ZK ≤ Subgroup.normalizer (Subgroup.zpowers zK : Set ↥K) :=
        hcen.trans (Subgroup.centralizer_le_normalizer _)
      have hform :=
        CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := ZK) (K := Subgroup.zpowers zK) hnorm
      rw [inf_comm, hinfcard, hZcard', hzpcard, mul_one] at hform
      dsimp [EK]
      rw [sup_comm]
      exact hform
    have hEKp : IsPGroup 3 ↥EK := IsPGroup.of_card (n := 2) (by rw [hEKcard]; norm_num)
    have hEK_exp : ∀ x ∈ EK, x ^ 3 = 1 := by
      intro x hx
      dsimp [EK] at hx
      rcases Subgroup.mem_sup_of_normal_right.mp hx with ⟨a, ha, b, hb, rfl⟩
      have ha3 : a ^ 3 = 1 := by
        have hdvd : orderOf a ∣ 3 := by
          rw [← hzpcard]
          exact Subgroup.orderOf_dvd_natCard (Subgroup.zpowers zK) ha
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hb3 : b ^ 3 = 1 := by
        have hdvd : orderOf b ∣ 3 := by
          rw [← hZcard']
          exact Subgroup.orderOf_dvd_natCard ZK hb
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hcomm : Commute a b := Subgroup.mem_center_iff.mp hb a
      rw [hcomm.mul_pow, ha3, hb3, one_mul]
    have hEK_nc : ¬ IsCyclic ↥EK := by
      intro hcyc
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥EK)
      have hgord : orderOf g = 9 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg, hEKcard]
      have hg3 : orderOf g ∣ 3 := by
        rw [← Subgroup.orderOf_coe g]
        exact orderOf_dvd_iff_pow_eq_one.mpr (hEK_exp (g : ↥K) g.2)
      have h93 : (9 : ℕ) ∣ 3 := hgord ▸ hg3
      norm_num at h93
    have hEK_le_C : EK ≤ Subgroup.centralizer ({tK} : Set ↥K) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      dsimp [EK] at hx
      rcases Subgroup.mem_sup_of_normal_right.mp hx with ⟨a, ha, b, hb, rfl⟩
      have hzpowC : Subgroup.zpowers zK ≤ Subgroup.centralizer ({tK} : Set ↥K) := by
        intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left hzKcommtK i).eq
      have haC : a * tK = tK * a :=
        Subgroup.mem_centralizer_singleton_iff.mp (hzpowC ha)
      have hbC : b * tK = tK * b := (Subgroup.mem_center_iff.mp hb tK).symm
      calc (a * b) * tK = a * (b * tK) := by group
        _ = a * (tK * b) := by rw [hbC]
        _ = (a * tK) * b := by group
        _ = (tK * a) * b := by rw [haC]
        _ = tK * (a * b) := by group
    have huniqW : ∀ U₁ U₂ : Subgroup (↥K ⧸ ZK), Nat.card U₁ = 3 → U₁ ≤ W →
        Nat.card U₂ = 3 → U₂ ≤ W → U₁ = U₂ := by
      intro U₁ U₂ h1 h1W h2 h2W
      have hmap1 : U₁.map eZ.toMonoidHom ≤
          Subgroup.centralizer ({uZ} : Set (alternatingGroup (Fin 7))) := by
        have h := Subgroup.map_mono h1W (f := eZ.toMonoidHom)
        rwa [CFSG.centralizer_singleton_map eZ (π tK), show eZ (π tK) = uZ from rfl] at h
      have hmap2 : U₂.map eZ.toMonoidHom ≤
          Subgroup.centralizer ({uZ} : Set (alternatingGroup (Fin 7))) := by
        have h := Subgroup.map_mono h2W (f := eZ.toMonoidHom)
        rwa [CFSG.centralizer_singleton_map eZ (π tK), show eZ (π tK) = uZ from rfl] at h
      have heq := a7_centralizer_involution_unique_order_three uZ huZ
        (U₁.map eZ.toMonoidHom) (U₂.map eZ.toMonoidHom)
        (by rw [Subgroup.card_map_of_injective eZ.injective, h1]) hmap1
        (by rw [Subgroup.card_map_of_injective eZ.injective, h2]) hmap2
      exact Subgroup.map_injective eZ.injective heq
    let Ubar : Subgroup (↥K ⧸ ZK) := Subgroup.zpowers zbar
    have hUbarcard : Nat.card ↥Ubar = 3 := by
      rw [Nat.card_zpowers, hzbarord]
    have hUbarW : Ubar ≤ W := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hzbarcomm
    have hmap_image_le : ∀ Q : Subgroup ↥K, IsPGroup 3 Q →
        Q ≤ Subgroup.centralizer ({tK} : Set ↥K) → Q.map π ≤ Ubar := by
      intro Q hQp hQc
      have hQW : Q.map π ≤ W := by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hqc : q * tK = tK * q := Subgroup.mem_centralizer_singleton_iff.mp (hQc hq)
        calc π q * π tK = π (q * tK) := (map_mul π q tK).symm
          _ = π (tK * q) := by rw [hqc]
          _ = π tK * π q := map_mul π tK q
      have hQpW : IsPGroup 3 ↥(Q.map π) := hQp.map π
      have hdvd : Nat.card ↥(Q.map π) ∣ 3 := by
        obtain ⟨k, hk⟩ := hQpW.exists_card_eq
        have hdvdW : 3 ^ k ∣ Nat.card ↥W := by
          rw [← hk]
          exact Subgroup.card_dvd_of_le hQW
        rw [hCcardZ] at hdvdW
        have hk_le : k ≤ 2 := by
          have hle : 3 ^ k ≤ 24 := Nat.le_of_dvd (by norm_num) hdvdW
          by_contra hk2
          have h3 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at h3
          omega
        interval_cases k
        · rw [hk]; norm_num
        · rw [hk]; norm_num
        · exfalso
          norm_num at hdvdW
      by_cases hbot : Q.map π = ⊥
      · rw [hbot]
        exact bot_le
      · have : Nontrivial ↥(Q.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
        obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(Q.map π))
        have hxR : (x : ↥K ⧸ ZK) ∈ Q.map π := x.2
        have hRcard : Nat.card ↥(Q.map π) = 3 := by
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
          · exact absurd (Subgroup.card_eq_one.mp h) hbot
          · exact h
        have hxord : orderOf x = 3 := by
          have hdvd3 : orderOf x ∣ 3 := by
            rw [← hRcard, ← Subgroup.orderOf_coe x]
            exact Subgroup.orderOf_dvd_natCard (Q.map π) hxR
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hx1
          · exact h
        let xq : ↥K ⧸ ZK := (x : ↥K ⧸ ZK)
        have hxqR : xq ∈ Q.map π := x.2
        have hxqord : orderOf xq = 3 := by
          change orderOf (x : ↥K ⧸ ZK) = 3
          rw [Subgroup.orderOf_coe x]
          exact hxord
        have hzpcard : Nat.card ↥(Subgroup.zpowers xq) = 3 := by
          rw [Nat.card_zpowers, hxqord]
        have hzpW : Subgroup.zpowers xq ≤ W := (Subgroup.zpowers_le.mpr hxqR).trans hQW
        have heq : Subgroup.zpowers xq = Ubar :=
          huniqW (Subgroup.zpowers xq) Ubar hzpcard hzpW hUbarcard hUbarW
        have hle : Ubar ≤ Q.map π := by
          rw [← heq]
          exact Subgroup.zpowers_le.mpr hxqR
        have heqRQ : Q.map π = Ubar :=
          (Subgroup.eq_of_le_of_card_ge hle (by rw [hRcard, hUbarcard])).symm
        rw [heqRQ]
    have huniqE : ∀ Q : Subgroup ↥K, IsPGroup 3 Q →
        Q ≤ Subgroup.centralizer ({tK} : Set ↥K) → Q ≤ EK := by
      intro Q hQp hQc
      have hmap_le := hmap_image_le Q hQp hQc
      intro x hx
      have hxmap : π x ∈ Ubar := hmap_le (Subgroup.mem_map_of_mem π hx)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxmap
      have hmemZ : x * (zK ^ i)⁻¹ ∈ ZK := by
        rw [← QuotientGroup.eq_one_iff (N := ZK) (x := x * (zK ^ i)⁻¹)]
        change π (x * (zK ^ i)⁻¹) = 1
        rw [map_mul, map_inv, map_zpow, hzKπ, hi]
        group
      have hmemSup : (x * (zK ^ i)⁻¹) * zK ^ i ∈ ZK ⊔ Subgroup.zpowers zK :=
        Subgroup.mul_mem_sup hmemZ (Subgroup.zpow_mem_zpowers zK i)
      rw [sup_comm] at hmemSup
      rw [show (x * (zK ^ i)⁻¹) * zK ^ i = x from by group] at hmemSup
      dsimp [EK]
      exact hmemSup
    let E : Subgroup Y := EK.map K.subtype
    have hEcard : Nat.card E = 9 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hEKcard]
    have hEleK : E ≤ K := Subgroup.map_subtype_le EK
    have hconjE : ∀ s : Y, s * t = t * s → EK.map (conjK s).toMonoidHom = EK := by
      intro s hst
      have hleC : EK.map (conjK s).toMonoidHom ≤
          Subgroup.centralizer ({tK} : Set ↥K) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
        apply Subtype.ext
        have hqt : q * tK = tK * q :=
          Subgroup.mem_centralizer_singleton_iff.mp (hEK_le_C hq)
        have hst' : s⁻¹ * t = t * s⁻¹ := (Commute.inv_left hst).eq
        change (s * (q : Y) * s⁻¹) * t = t * (s * (q : Y) * s⁻¹)
        calc (s * (q : Y) * s⁻¹) * t = s * (q : Y) * (s⁻¹ * t) := by group
          _ = s * (q : Y) * (t * s⁻¹) := by rw [hst']
          _ = s * ((q : Y) * t) * s⁻¹ := by group
          _ = s * (t * (q : Y)) * s⁻¹ := by
              rw [show (q : Y) * t = t * (q : Y) from congrArg Subtype.val hqt]
          _ = (s * t) * (q : Y) * s⁻¹ := by group
          _ = (t * s) * (q : Y) * s⁻¹ := by rw [hst]
          _ = t * (s * (q : Y) * s⁻¹) := by group
      have hle : EK.map (conjK s).toMonoidHom ≤ EK :=
        huniqE _ (hEKp.map (conjK s).toMonoidHom) hleC
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (conjK s).injective, hEKcard])
    have hSnormalE : S ≤ Subgroup.normalizer (E : Set Y) := by
      intro s hs
      have hmapE := hconjE s (htcentS s hs).symm
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hcomp : (MulAut.conj s).toMonoidHom.comp K.subtype =
          K.subtype.comp (conjK s).toMonoidHom := by
        ext x
        exact (hconjK_coe s x).symm
      calc E.map (MulAut.conj s).toMonoidHom
          = (EK.map (conjK s).toMonoidHom).map K.subtype := by
              dsimp [E]
              rw [Subgroup.map_map]
              erw [hcomp]
              rw [Subgroup.map_map]
              rfl
        _ = E := by dsimp [E]; erw [hmapE]
    have hEinfS : E ⊓ S = ⊥ := by
      have h1 : Nat.card ↥(E ⊓ S) ∣ 9 := by
        rw [← hEcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(E ⊓ S) ∣ 8 := by
        have hle : E ⊓ S ≤ T := by
          calc E ⊓ S ≤ K ⊓ S := le_inf (inf_le_left.trans hEleK) inf_le_right
            _ = T := by rw [inf_comm, hTdef]
        rw [← hTcard]
        exact Subgroup.card_dvd_of_le hle
      have hdvd : Nat.card ↥(E ⊓ S) ∣ 1 := by
        have hg := Nat.dvd_gcd h1 h2
        have h98 : Nat.gcd 9 8 = 1 := by norm_num
        rwa [h98] at hg
      exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)
    have hE_exp : ∀ x ∈ E, x ^ 3 = 1 := by
      intro x hx
      dsimp [E] at hx
      obtain ⟨xK, hxK, rfl⟩ := Subgroup.mem_map.mp hx
      exact congrArg Subtype.val (hEK_exp xK hxK)
    have hE_nc : ¬ IsCyclic ↥E := by
      intro hcyc
      have : IsCyclic ↥(EK.map K.subtype) := hcyc
      have hEKcyc : IsCyclic ↥EK := by
        let ee := Subgroup.equivMapOfInjective EK K.subtype K.subtype_injective
        exact isCyclic_of_surjective ee.symm.toMonoidHom ee.symm.surjective
      exact hEK_nc hEKcyc
    have hEne : E ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hEcard
      norm_num at hEcard
    refine ⟨E, hEleK, hEne, ?_, hE_exp, hE_nc, ?_⟩
    · exact IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
    · refine CFSG.Quasithin.H.L3Wr.permute_of_card hEinfS ?_
      have hform :=
        CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := S) (K := E) hSnormalE
      rw [inf_comm, sup_comm, hEinfS, Subgroup.card_bot, hEcard, mul_one] at hform
      have hsup : Nat.card ↥(S ⊔ E) = Nat.card E * Nat.card S := by
        rw [sup_comm]
        rw [hform, hEcard]
        ring
      rw [sup_comm, hsup]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
