module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918SmallOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OrderTwentyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918Quot
import CFSG.GroupTheory.PCoreOfSubnormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open scoped Pointwise

private theorem alt6_eq_top_of_index_le_five {H : Subgroup (alternatingGroup (Fin 6))}
    (hH : H.index ≤ 5) : H = ⊤ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with hb | ht
  · exfalso
    have hdvd := Subgroup.index_normalCore_dvd_factorial_index H
    rw [hb, Subgroup.index_bot, hcard] at hdvd
    have hle : H.index.factorial ≤ 120 := (Nat.factorial_le hH).trans (by norm_num)
    have := Nat.le_of_dvd (Nat.factorial_pos H.index) hdvd
    omega
  · exact le_antisymm le_top (ht ▸ Subgroup.normalCore_le H)

private theorem relIndex_sup_eq_of_normalizes {G : Type} [Group G] {K C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (K : Set G)) : K.relIndex (K ⊔ C) = K.relIndex C := by
  have hX : K ⊔ C ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hC
  have hKX : K ≤ K ⊔ C := le_sup_left
  have hCX : C ≤ K ⊔ C := le_sup_right
  have hK' : (K.subgroupOf (K ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hX
  have key := Subgroup.relIndex_sup_right (C.subgroupOf (K ⊔ C)) (K.subgroupOf (K ⊔ C))
  have htop : C.subgroupOf (K ⊔ C) ⊔ K.subgroupOf (K ⊔ C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCX hKX, sup_comm, Subgroup.subgroupOf_self]
  rw [htop, Subgroup.relIndex_top_right] at key
  calc K.relIndex (K ⊔ C) = (K.subgroupOf (K ⊔ C)).index := rfl
    _ = (K.subgroupOf (K ⊔ C)).relIndex (C.subgroupOf (K ⊔ C)) := key
    _ = K.relIndex C := Subgroup.relIndex_subgroupOf hCX

theorem center_le_of_isA6ModZ3 {X : Type} [Group X] [Finite X] (hX : IsA6ModZ3 X)
    {Y : Subgroup X} (hY : Y.index = 15) : Subgroup.center X ≤ Y := by
  obtain ⟨hcov, hZcard⟩ := hX
  obtain ⟨e⟩ := hcov.2
  set q : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hqker : q.ker = Subgroup.center X := QuotientGroup.ker_mk' (Subgroup.center X)
  have hZnorm : Subgroup.center X ≤ Subgroup.normalizer (Y : Set X) :=
    Subgroup.center_le_normalizer (Y : Set X)
  have hrel : Y.relIndex (Y ⊔ Subgroup.center X) = Y.relIndex (Subgroup.center X) :=
    relIndex_sup_eq_of_normalizes hZnorm
  have hrelmul :
      Y.relIndex (Y ⊔ Subgroup.center X) * (Y ⊔ Subgroup.center X).index = 15 := by
    rw [Subgroup.relIndex_mul_index le_sup_left, hY]
  have hrel_dvd : Y.relIndex (Y ⊔ Subgroup.center X) ∣ 3 := by
    rw [hrel]
    calc Y.relIndex (Subgroup.center X) = (Y.subgroupOf (Subgroup.center X)).index := rfl
      _ ∣ Nat.card ↥(Subgroup.center X) :=
          Subgroup.index_dvd_card (Y.subgroupOf (Subgroup.center X))
      _ = 3 := hZcard
  rcases (Nat.dvd_prime Nat.prime_three).mp hrel_dvd with h1 | h3
  · exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    have hindex : (Y ⊔ Subgroup.center X).index = 5 := by
      rw [h3] at hrelmul
      omega
    have hmapidx : ((Y ⊔ Subgroup.center X).map q).index ≤ 5 := by
      rw [Subgroup.index_map_eq (f := q) (H := Y ⊔ Subgroup.center X)
        (QuotientGroup.mk'_surjective (Subgroup.center X))
        (by rw [hqker]; exact le_sup_right)]
      exact le_of_eq hindex
    have hHqidx : (((Y ⊔ Subgroup.center X).map q).map e.toMonoidHom).index ≤ 5 := by
      rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective
        ((Y ⊔ Subgroup.center X).map q)]
      exact hmapidx
    have hHq := alt6_eq_top_of_index_le_five hHqidx
    have hqtop : (Y ⊔ Subgroup.center X).map q = ⊤ := by
      have h1 : Subgroup.comap e.toMonoidHom
          (Subgroup.map e.toMonoidHom ((Y ⊔ Subgroup.center X).map q))
          = (Y ⊔ Subgroup.center X).map q :=
        Subgroup.comap_map_eq_self_of_injective e.injective _
      rw [hHq, Subgroup.comap_top] at h1
      exact h1.symm
    have hYtop : Y ⊔ Subgroup.center X = ⊤ := by
      have h := Subgroup.comap_map_eq_self (f := q) (H := Y ⊔ Subgroup.center X)
        (by rw [hqker]; exact le_sup_right)
      rw [hqtop, Subgroup.comap_top] at h
      exact h.symm
    rw [hYtop, Subgroup.index_top] at hindex
    omega

private theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem card_of_isA6ModZ3 {X : Type} [Group X] [Finite X] (hX : IsA6ModZ3 X) :
    Nat.card X = 1080 := by
  obtain ⟨hcov, hZcard⟩ := hX
  obtain ⟨e⟩ := hcov.2
  have h := (Subgroup.center X).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, card_alt6, hZcard] at h
  norm_num at h
  exact h

theorem kFacts1918_of_isA6ModZ3 {X : Type} [Group X] [Finite X] (hX : IsA6ModZ3 X)
    (Y : Subgroup X) (hY : Y.index = 15) :
    (∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)) ∧
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) = 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZleY : Subgroup.center X ≤ Y := center_le_of_isA6ModZ3 hX hY
  have hXcard : Nat.card X = 1080 := card_of_isA6ModZ3 hX
  obtain ⟨hcov, hZcard⟩ := hX
  obtain ⟨e⟩ := hcov.2
  have hYcard : Nat.card ↥Y = 72 := by
    have h := Subgroup.index_mul_card (H := Y)
    rw [hY, hXcard] at h
    omega
  let π : X →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπker : π.ker = Subgroup.center X := by
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  let H : Subgroup (alternatingGroup (Fin 6)) := Y.map π
  let ρ : ↥Y →* ↥H := π.subgroupMap Y
  have hρsurj : Function.Surjective ρ := MonoidHom.subgroupMap_surjective π Y
  have hρker : ρ.ker = (Subgroup.center X).subgroupOf Y := by
    rw [show ρ = π.subgroupMap Y from rfl, Subgroup.ker_subgroupMap, hπker]
  have hZbcard : Nat.card ↥((Subgroup.center X).subgroupOf Y) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleY).toEquiv]
    exact hZcard
  have hHcard : Nat.card ↥H = 24 := by
    have hidx : ρ.ker.index = Nat.card ↥H := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj).toEquiv
    have h := Subgroup.index_mul_card (H := ρ.ker)
    rw [hidx, hρker, hZbcard, hYcard] at h
    omega
  let N : Subgroup ↥H := CFSG.pCore 2 ↥H
  have hNsyl : ∀ P : Sylow 2 ↥H, normalizer ((P : Subgroup ↥H) : Set ↥H) = P :=
    fun P => normalizer_sylow_eq_of_le_alt6 (H := H) (by rw [hHcard]; norm_num) P
  have hNdata := card_pCore_of_card_eq_24 (H := ↥H) hHcard hNsyl
  have hNcard : Nat.card ↥N = 4 := hNdata.1
  obtain ⟨aH, bH, habH⟩ := hNdata.2
  let Qy : Subgroup ↥Y := CFSG.pCore 2 ↥Y
  haveI hQyN : Qy.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQp : IsPGroup 2 ↥Qy := CFSG.pCore_isPGroup (p := 2) (G := ↥Y)
  haveI hNN : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 ↥N := CFSG.pCore_isPGroup (p := 2) (G := ↥H)
  have hρkerQ : (ρ.ker).subgroupOf Qy = ⊥ := by
    have hinf : ρ.ker ⊓ Qy = ⊥ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
      have hcop : Nat.Coprime (Nat.card ↥(ρ.ker)) (Nat.card ↥Qy) := by
        rw [hρker, hZbcard, hk]
        exact (by norm_num : Nat.Coprime 3 2).pow_right k
      exact Subgroup.inf_eq_bot_of_coprime hcop
    rw [← Subgroup.map_subtype_inj (H := Qy)]
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, hinf]
  have hQmapinj : Function.Injective (ρ.subgroupMap Qy) := by
    rw [← MonoidHom.ker_eq_bot_iff (ρ.subgroupMap Qy), Subgroup.ker_subgroupMap]
    exact hρkerQ
  have hQmapcard : Nat.card ↥(Qy.map ρ) = Nat.card ↥Qy :=
    Nat.card_congr (Equiv.ofBijective (ρ.subgroupMap Qy)
      ⟨hQmapinj, MonoidHom.subgroupMap_surjective ρ Qy⟩).symm
  have hQmap_le : Qy.map ρ ≤ N :=
    CFSG.LieType.BorelTits.le_pCore 2 (hQyN.map ρ hρsurj) (hQp.map ρ)
  have hQle4 : Nat.card ↥Qy ≤ 4 := by
    rw [← hQmapcard, ← hNcard]
    exact Subgroup.card_le_of_le hQmap_le
  let R : Subgroup ↥Y := N.comap ρ
  have hRnormal : R.Normal := hNN.comap ρ
  haveI hRN : R.Normal := hRnormal
  have hRcard : Nat.card ↥R = 12 := by
    have hNidx : N.index = 6 := by
      have h := Subgroup.index_mul_card (H := N)
      rw [hNcard, hHcard] at h
      omega
    have hidx : R.index = N.index :=
      Subgroup.index_comap_of_surjective (H := N) (f := ρ) hρsurj
    have h := Subgroup.index_mul_card (H := R)
    rw [hidx, hNidx, hYcard] at h
    omega
  have hZRcenter : (ρ.ker).subgroupOf R ≤ Subgroup.center ↥R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hz1 : (z : ↥R).1 ∈ ρ.ker := Subgroup.mem_subgroupOf.mp hz
    have hzc : (((z : ↥R).1 : ↥Y) : X) ∈ Subgroup.center X :=
      Subgroup.mem_subgroupOf.mp (hρker ▸ hz1)
    exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp hzc (((w : ↥R).1 : ↥Y) : X)))
  let ρR : ↥R →* ↥N := (ρ.comp R.subtype).codRestrict N (fun r => Subgroup.mem_comap.mp r.2)
  have hρRsurj : Function.Surjective ρR := by
    intro n
    obtain ⟨y, hy⟩ := hρsurj n
    refine ⟨⟨y, ?_⟩, ?_⟩
    · exact Subgroup.mem_comap.mpr (by rw [hy]; exact n.2)
    · exact Subtype.ext hy
  have hρRker : ρR.ker = (ρ.ker).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hquot2 : IsPGroup 2 (↥R ⧸ (ρ.ker).subgroupOf R) :=
    (hNp.of_equiv (QuotientGroup.quotientKerEquivOfSurjective ρR hρRsurj).symm).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hρRker)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥R))
  have hPnorm : (P : Subgroup ↥R).Normal := by
    have hmap : (P : Subgroup ↥R).map (QuotientGroup.mk' ((ρ.ker).subgroupOf R)) = ⊤ := by
      rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P]
      exact ((Sylow.mapSurjective (QuotientGroup.mk'_surjective _) P).3
        (hquot2.to_subgroup ⊤) le_top).symm
    have htop : (ρ.ker).subgroupOf R ⊔ (P : Subgroup ↥R) = ⊤ := by
      rw [← QuotientGroup.comap_map_mk', hmap, comap_top]
    refine Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 (htop ▸ sup_le ?_ le_normalizer))
    exact hZRcenter.trans (Subgroup.center_le_normalizer _)
  have hPchar : (P : Subgroup ↥R).Characteristic := Sylow.characteristic_of_normal P hPnorm
  have hPRchar : (P.map R.subtype).Normal := by
    haveI := hPchar
    exact ConjAct.normal_of_characteristic_of_normal
  have hPmap2 : IsPGroup 2 (P.map R.subtype) := (P.isPGroup').map R.subtype
  have hPleQ : P.map R.subtype ≤ Qy :=
    CFSG.LieType.BorelTits.le_pCore 2 hPRchar hPmap2
  have hPcard : Nat.card ↥(P : Subgroup ↥R) = 4 := by
    rw [Sylow.card_eq_multiplicity P, hRcard]
    rw [Nat.factorization_def 12 (by norm_num : Nat.Prime 2)]
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 2,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    norm_num
  have hPmapcard : Nat.card ↥(P.map R.subtype) = 4 := by
    rw [← Nat.card_congr
      (Subgroup.equivMapOfInjective (P : Subgroup ↥R) R.subtype R.subtype_injective).toEquiv]
    exact hPcard
  have hQge4 : 4 ≤ Nat.card ↥Qy := by
    rw [← hPmapcard]
    exact Subgroup.card_le_of_le hPleQ
  have hQcard : Nat.card ↥Qy = 4 := le_antisymm hQle4 hQge4
  have hρQ : Qy.map ρ = N :=
    Subgroup.eq_of_le_of_card_ge hQmap_le (by rw [hNcard, hQmapcard, hQcard])
  let Ybar := ↥Y ⧸ Qy
  let qy : ↥Y →* Ybar := QuotientGroup.mk' Qy
  let C : Subgroup Ybar := ((Subgroup.center X).subgroupOf Y).map qy
  have hQleR : Qy ≤ R := by
    intro q hq
    rw [show R = N.comap ρ from rfl, Subgroup.mem_comap, ← hρQ]
    exact Subgroup.mem_map_of_mem ρ hq
  have hZbleR : (Subgroup.center X).subgroupOf Y ≤ R := by
    intro z hz
    rw [show R = N.comap ρ from rfl, Subgroup.mem_comap]
    have hz' : z ∈ ρ.ker := by rw [hρker]; exact hz
    rw [MonoidHom.mem_ker.mp hz']
    exact N.one_mem
  have hZQR : ((Subgroup.center X).subgroupOf Y : Set ↥Y) * (Qy : Set ↥Y) ⊆ (R : Set ↥Y) := by
    intro x hx
    obtain ⟨z, hz, q, hq, rfl⟩ := Set.mem_mul.mp hx
    exact R.mul_mem (hZbleR hz) (hQleR hq)
  have hYbarcard : Nat.card Ybar = 18 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Qy
    rw [hYcard, hQcard] at h
    dsimp only [Ybar]
    omega
  have hCcard : Nat.card ↥C = 3 := by
    have hinf : Qy ⊓ ((Subgroup.center X).subgroupOf Y) = ⊥ := by
      have hcop : Nat.Coprime (Nat.card ↥Qy)
          (Nat.card ↥((Subgroup.center X).subgroupOf Y)) := by
        rw [hQcard, hZbcard]
        norm_num
      exact Subgroup.inf_eq_bot_of_coprime hcop
    have hkerbot : Qy.subgroupOf ((Subgroup.center X).subgroupOf Y) = ⊥ := by
      rw [← Subgroup.map_subtype_inj (H := (Subgroup.center X).subgroupOf Y)]
      rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, hinf]
    have hinj : Function.Injective (qy.subgroupMap ((Subgroup.center X).subgroupOf Y)) := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
        show qy.ker = Qy from QuotientGroup.ker_mk' Qy]
      exact hkerbot
    have hbij : Function.Bijective (qy.subgroupMap ((Subgroup.center X).subgroupOf Y)) :=
      ⟨hinj, MonoidHom.subgroupMap_surjective qy ((Subgroup.center X).subgroupOf Y)⟩
    have hcard : Nat.card ↥((Subgroup.center X).subgroupOf Y) = Nat.card ↥C := by
      dsimp only [C]
      exact Nat.card_congr
        (Equiv.ofBijective (qy.subgroupMap ((Subgroup.center X).subgroupOf Y)) hbij)
    rw [hZbcard] at hcard
    exact hcard.symm
  have hCcenter : C ≤ Subgroup.center Ybar := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective Qy w
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hz) (w' : X))
  have hncYbar : ∃ a b : Ybar, a * b * a⁻¹ * b⁻¹ ∉ C := by
    obtain ⟨aY, haY⟩ := hρsurj aH
    obtain ⟨bY, hbY⟩ := hρsurj bH
    refine ⟨qy aY, qy bY, ?_⟩
    intro hcomm
    have hxR : ¬ (aY * bY * aY⁻¹ * bY⁻¹) ∈ R := by
      intro hx
      apply habH
      have := Subgroup.mem_comap.mp hx
      simpa only [map_mul, map_inv, haY, hbY] using this
    apply hxR
    have hxC : qy (aY * bY * aY⁻¹ * bY⁻¹) ∈ C := by
      simpa only [map_mul, map_inv] using hcomm
    dsimp only [C] at hxC
    rw [Subgroup.mem_map] at hxC
    obtain ⟨z, hz, hzx⟩ := hxC
    have hq : (aY * bY * aY⁻¹ * bY⁻¹)⁻¹ * z ∈ Qy := by
      rw [← QuotientGroup.eq_one_iff]
      change qy ((aY * bY * aY⁻¹ * bY⁻¹)⁻¹ * z) = 1
      rw [map_mul, map_inv, hzx, inv_mul_cancel]
    have hxeq : aY * bY * aY⁻¹ * bY⁻¹ = z * ((aY * bY * aY⁻¹ * bY⁻¹)⁻¹ * z)⁻¹ := by
      group
    rw [hxeq]
    exact hZQR (Set.mem_mul.mpr
      ⟨z, hz, ((aY * bY * aY⁻¹ * bY⁻¹)⁻¹ * z)⁻¹, Qy.inv_mem hq, rfl⟩)
  have hopp := opp_top_of_card_eighteen hYbarcard hCcenter hCcard hncYbar
  let Y₀ : Subgroup X := Opp 2 Y
  have hY₀le : Y₀ ≤ Y := by
    dsimp only [Y₀, Opp, CFSG.RankThree.PartOne.pElementSubgroup]
    exact (Subgroup.closure_le Y).mpr fun x hx => hx.1
  have hY0map : Y₀ = (Opp 2 (⊤ : Subgroup ↥Y)).map Y.subtype := by
    change CFSG.RankThree.PartOne.pElementSubgroup 2 Y =
      (CFSG.RankThree.PartOne.pElementSubgroup 2 (⊤ : Subgroup ↥Y)).map Y.subtype
    rw [s13_pElementSubgroup_map Nat.prime_two Y.subtype (⊤ : Subgroup ↥Y)]
    congr 1
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hY₀sub : Y₀.subgroupOf Y = Opp 2 (⊤ : Subgroup ↥Y) := by
    rw [hY0map]
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have hQleY0sub : Qy ≤ Y₀.subgroupOf Y := by
    rw [hY₀sub]
    intro q hq
    refine Subgroup.subset_closure ⟨Subgroup.mem_top q, ?_⟩
    obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
    have hqk : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hqk)
    exact ⟨j, hj⟩
  have hY0normal : (Y₀.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hY₀le]
    intro g hg
    have hg' := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := Y) hg)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp only [Y₀, Opp]
    rw [CFSG.RankThree.PartOne.pElementSubgroup, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨hxL, k, hk⟩, rfl⟩
      refine ⟨(hg' x).mp hxL, k, ?_⟩
      rw [← hk]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    · rintro ⟨hyL, k, hk⟩
      have hx : g⁻¹ * y * g ∈ Y := by
        have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        exact (hg' _).mpr (by rw [e]; exact hyL)
      refine ⟨g⁻¹ * y * g, ⟨hx, k, ?_⟩, ?_⟩
      · rw [← hk]
        have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
        simpa [MulAut.conj_apply] using this
      · show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hY0subn : CFSG.Open.IsSubnormal Y₀ Y :=
    CFSG.Open.IsSubnormal.step hY₀le hY0normal (CFSG.Open.IsSubnormal.refl Y)
  have hpCoreY0card : Nat.card ↥(CFSG.pCore 2 ↥Y₀) = 4 := by
    have hsub := CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal (K := Y₀) (H := Y) hY0subn
    have hQmapY : Qy.map Y.subtype ≤ Y₀ := (Subgroup.map_le_iff_le_comap).mpr hQleY0sub
    have hmap : (CFSG.pCore 2 ↥Y₀).map Y₀.subtype = Qy.map Y.subtype := by
      rw [show (CFSG.pCore 2 ↥Y₀).map Y₀.subtype = pCoreOf 2 Y₀ from rfl, hsub,
        show pCoreOf 2 Y = Qy.map Y.subtype from rfl, inf_eq_right.mpr hQmapY]
    calc Nat.card ↥(CFSG.pCore 2 ↥Y₀)
        = Nat.card ↥((CFSG.pCore 2 ↥Y₀).map Y₀.subtype) :=
          (Subgroup.card_map_of_injective Y₀.subtype_injective).symm
      _ = Nat.card ↥(Qy.map Y.subtype) := by rw [hmap]
      _ = Nat.card ↥Qy := Subgroup.card_map_of_injective Y.subtype_injective
      _ = 4 := hQcard
  let g : ↥Y₀ →* Ybar := qy.comp (Subgroup.inclusion hY₀le)
  have hgker : g.ker = Qy.comap (Subgroup.inclusion hY₀le) := by
    rw [show g = qy.comp (Subgroup.inclusion hY₀le) from rfl,
      (MonoidHom.comap_ker qy (Subgroup.inclusion hY₀le)).symm]
    congr 1
    exact QuotientGroup.ker_mk' Qy
  have hgrange : g.range = Opp 2 (⊤ : Subgroup Ybar) := by
    change g.range = CFSG.RankThree.PartOne.pElementSubgroup 2 (⊤ : Subgroup Ybar)
    rw [show g = qy.comp (Subgroup.inclusion hY₀le) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range hY₀le, hY₀sub]
    dsimp only [Opp]
    rw [s13_pElementSubgroup_map Nat.prime_two qy (⊤ : Subgroup ↥Y),
      Subgroup.map_top_of_surjective qy (QuotientGroup.mk'_surjective Qy)]
  let φ : ↥Y₀ →* ↥(Opp 2 (⊤ : Subgroup Ybar)) :=
    g.codRestrict _ (fun y => by rw [← hgrange]; exact ⟨y, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (by rw [hgrange]; exact x.2)
    exact ⟨y, Subtype.ext hy⟩
  have hφker_g : φ.ker = g.ker := by
    show (g.codRestrict _ _).ker = g.ker
    rw [MonoidHom.ker_codRestrict]
  have hQcomap_card : Nat.card ↥(Qy.comap (Subgroup.inclusion hY₀le)) = 4 := by
    have hmapQ : (Qy.comap (Subgroup.inclusion hY₀le)).map (Subgroup.inclusion hY₀le) = Qy :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.inclusion_range]; exact hQleY0sub)
    calc Nat.card ↥(Qy.comap (Subgroup.inclusion hY₀le))
        = Nat.card ↥((Qy.comap (Subgroup.inclusion hY₀le)).map (Subgroup.inclusion hY₀le)) :=
          (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hY₀le)).symm
      _ = Nat.card ↥Qy := by rw [hmapQ]
      _ = 4 := hQcard
  have hφker : φ.ker = CFSG.pCore 2 ↥Y₀ := by
    have hle : φ.ker ≤ CFSG.pCore 2 ↥Y₀ := by
      rw [hφker_g, hgker]
      exact CFSG.LieType.BorelTits.le_pCore 2 ((inferInstance : Qy.Normal).comap _)
        (hQp.comap_of_injective (Subgroup.inclusion hY₀le)
          (Subgroup.inclusion_injective hY₀le))
    have hcardker : Nat.card ↥(φ.ker) = 4 := by
      rw [hφker_g, hgker]
      exact hQcomap_card
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hpCoreY0card, hcardker])
  have hncS : ∃ a b : ↥(Opp 2 (⊤ : Subgroup Ybar)), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hopp.2
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hmin : ∀ M : Subgroup ↥(Opp 2 (⊤ : Subgroup Ybar)), M.Normal → M ≠ ⊥ →
      S17.oUpperTwo (⊤ : Subgroup ↥(Opp 2 (⊤ : Subgroup Ybar))) ≤ M :=
    fun M hM hne => oUpperTwo_le_of_normal_of_card_six hopp.1 hncS hM hne
  refine ⟨fun Nn hNnY hNn hNnQ => ?_, ?_⟩
  · exact oUpperTwo_le_sup_pCoreOf_of_quot Y₀ φ hφsurj (le_of_eq hφker) hmin Nn hNnY hNn hNnQ
  · rw [card_bar2_oUpperTwo_of_quot Y₀ φ hφsurj hφker]
    exact card_oUpperTwo_of_card_six hopp.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
