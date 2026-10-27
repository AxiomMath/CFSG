module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LargeExtraspecial.S8CBFSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (Data IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_normal)

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_iff_map_conj {X : Type} [Group X] {H : Subgroup X} {g : X} :
    g ∈ Subgroup.normalizer (H : Set X) ↔ H.map (MulAut.conj g).toMonoidHom = H := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    apply le_antisymm
    · rintro z ⟨y, hy, hyz⟩
      rw [← hyz]
      simpa [MulAut.conj_apply] using (hg y).mp hy
    · intro z hz
      refine ⟨(MulAut.conj g)⁻¹ z, (hg _).mpr ?_, by simp [mul_assoc]⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro hmap z
    constructor
    · intro hz
      have hzmap : (MulAut.conj g).toMonoidHom z ∈ H.map (MulAut.conj g).toMonoidHom :=
        ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using (hmap ▸ hzmap)
    · intro hz
      have hzmap : (MulAut.conj g).toMonoidHom z ∈ H.map (MulAut.conj g).toMonoidHom := by
        rw [hmap]; simpa [MulAut.conj_apply] using hz
      obtain ⟨y, hy, hyz⟩ := hzmap
      have hyz' : y = z := (MulAut.conj g).injective (by simpa using hyz)
      exact hyz' ▸ hy

private theorem three_dvd_four_pow_sub_one (k : ℕ) : 3 ∣ 4 ^ k - 1 := by
  have h := geom_sum_mul_of_one_le (x := (4 : ℕ)) (by norm_num) k
  refine ⟨∑ i ∈ Finset.range k, (4 : ℕ) ^ i, ?_⟩
  rw [← h]
  ring

private theorem nat_gcd_three_four_pow_add_one (k : ℕ) : Nat.gcd 3 (4 ^ k + 1) = 1 := by
  have hmod : (4 : ℕ) ^ k ≡ 1 [MOD 3] := by
    have h : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    simpa using Nat.ModEq.pow k h
  have hmod2 : (4 : ℕ) ^ k + 1 ≡ 2 [MOD 3] := by
    simpa using hmod.add_right 1
  have hnot : ¬ 3 ∣ 4 ^ k + 1 := by
    intro hd
    have h0 : (4 : ℕ) ^ k + 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr hd
    rw [Nat.ModEq] at hmod2 h0
    norm_num at hmod2 h0
    omega
  exact (Nat.prime_three.coprime_iff_not_dvd.mpr hnot).gcd_eq_one

private theorem le_fStarMod {N H : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    N ≤ fStarMod N H := by
  intro n hn
  rw [fStarMod]
  refine Subgroup.mem_map.mpr ⟨⟨n, hNH hn⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  haveI := hN
  have h1 : (QuotientGroup.mk' (N.subgroupOf H).normalCore) ⟨n, hNH hn⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := (N.subgroupOf H).normalCore) ⟨n, hNH hn⟩).mpr (by
      rw [Subgroup.normalCore_eq_self]
      exact hn)
  rw [h1]
  exact (genFittingFStar _).one_mem

private theorem fStarMod_normal (N H : Subgroup G) : ((fStarMod N H).subgroupOf H).Normal := by
  let K : Subgroup ↥H := (genFittingFStar (↥H ⧸ (N.subgroupOf H).normalCore)).comap
    (QuotientGroup.mk' (N.subgroupOf H).normalCore)
  have hnorm : (genFittingFStar (↥H ⧸ (N.subgroupOf H).normalCore)).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal _
  have hgoal : ((fStarMod N H).subgroupOf H) = K := by
    rw [fStarMod]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  rw [hgoal]
  exact hnorm.comap _

private theorem false_of_borel_lift
    {H T M : Subgroup G} (hT : IsSylowIn 2 T H) (hTM : T ≤ M) (hHM : ¬ H ≤ M)
    (hcalN : calNIn H T = {H ⊓ M})
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M)
    {X : Type} [Group X] [Finite X] (hBender : fusionIsBenderGroup X)
    (h3D : ∀ (P : Sylow 2 X) (D : Subgroup X),
      CFSG.Goldschmidt.G3a.BorelSetup P D → 3 ∣ Nat.card D)
    {L K : Subgroup G} (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hKL : K ≤ L) (hKn : (K.subgroupOf H).Normal)
    {φ : ↥L →* X} (hφ : Function.Surjective φ)
    (hkerK : ∀ l : ↥L, φ l = 1 ↔ (l : G) ∈ K) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hXsimple : IsSimpleGroup X :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hBender
  have hKH : K ≤ H := hKL.trans hLH
  have hHnormL : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLn
  have hHnormK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  let S : Subgroup G := T ⊓ L
  have hSL : S ≤ L := inf_le_right
  have hSylS : IsSylowIn 2 S L := hT.inf_normal hLH hLn
  let Ssl : Sylow 2 ↥L := hSylS.toSylow
  let T₀ : Sylow 2 X := Sylow.mapSurjective hφ Ssl
  have hT0coe : (T₀ : Subgroup X) = (S.subgroupOf L).map φ := by
    change ((Sylow.mapSurjective hφ Ssl : Sylow 2 X) : Subgroup X) = (S.subgroupOf L).map φ
    rw [Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hBender T₀
  have hD3 : 3 ∣ Nat.card D := h3D T₀ D hD
  obtain ⟨T₁, hT1ne, hDT1⟩ := hD.exists_fixed
  have hT0ne_bot : (T₀ : Subgroup X) ≠ ⊥ := hD.ne_bot
  have h3X : 3 ∣ Nat.card X := by
    have h1 : Nat.card D ∣ Nat.card (⊤ : Subgroup X) := Subgroup.card_dvd_of_le le_top
    rw [Subgroup.card_top] at h1
    exact hD3.trans h1
  have hT0ne_top : (T₀ : Subgroup X) ≠ ⊤ := by
    intro htop
    obtain ⟨e3, he3⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3X
    have he3T : e3 ∈ (T₀ : Subgroup X) := by rw [htop]; trivial
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp T₀.isPGroup' ⟨e3, he3T⟩
    have hk' : orderOf (e3 : X) = 2 ^ k := by simpa using hk
    rw [he3] at hk'
    have hne : (2 : ℕ) ^ k ≠ 3 := by
      intro h
      exact absurd (Nat.prime_three.pow_eq_iff.mp h).1 (by norm_num)
    exact hne hk'.symm
  have hTnormS : T ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht s hs
    refine ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht), ?_⟩
    have h := (Subgroup.le_normalizer_iff.mp hHnormL) t (hT.le ht) s hs.2
    simpa using h
  have hTnormK : T ≤ Subgroup.normalizer (K : Set G) := hT.le.trans hHnormK
  let SK : Subgroup G := S ⊔ K
  have hSKdef : SK = S ⊔ K := rfl
  have hTnormSK : T ≤ Subgroup.normalizer (SK : Set G) := by
    intro t ht
    refine mem_normalizer_iff_map_conj.mpr ?_
    change SK.map (MulAut.conj t).toMonoidHom = SK
    rw [hSKdef, Subgroup.map_sup, (mem_normalizer_iff_map_conj.mp (hTnormS ht)),
      (mem_normalizer_iff_map_conj.mp (hTnormK ht))]
  have normS_false : H ≤ Subgroup.normalizer (S : Set G) → False := by
    intro hHnormS
    have hSLn : (S.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSL).mpr (hLH.trans hHnormS)
    have hN : ((S.subgroupOf L).map φ).Normal := hSLn.map φ hφ
    haveI : (T₀ : Subgroup X).Normal := by rw [hT0coe]; exact hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T₀ : Subgroup X) with hbot | htop
    · exact hT0ne_bot hbot
    · exact hT0ne_top htop
  have normSK_false : H ≤ Subgroup.normalizer (SK : Set G) → False := by
    intro hHnormSK
    have hSKL : SK ≤ L := hSKdef.symm ▸ sup_le hSL hKL
    have hSKLn : ((S ⊔ K).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSKL).mpr (hLH.trans hHnormSK)
    have heq : ((S ⊔ K).subgroupOf L).map φ = (S.subgroupOf L).map φ := by
      apply le_antisymm
      · rw [Subgroup.map_le_map_iff]
        rw [Subgroup.subgroupOf_sup hSL hKL]
        refine sup_le le_sup_left ?_
        intro k hk
        exact Subgroup.mem_sup_right (by rw [MonoidHom.mem_ker, hkerK]; exact hk)
      · exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_left)
    haveI : (T₀ : Subgroup X).Normal := by
      rw [hT0coe, ← heq]
      exact hSKLn.map φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T₀ : Subgroup X) with hbot | htop
    · exact hT0ne_bot hbot
    · exact hT0ne_top htop
  have hKTlt : K ⊔ T < H := by
    refine lt_of_le_of_ne (sup_le hKH hT.le) ?_
    intro hKTH
    have hT0top : (T₀ : Subgroup X) = ⊤ := by
      have htop : (⊤ : Subgroup ↥L) ≤ φ.ker ⊔ (S.subgroupOf L) := by
        intro l _
        have hlH : (l : G) ∈ H := hLH l.2
        have hmemH : (⟨(l : G), hlH⟩ : ↥H) ∈ (K.subgroupOf H) ⊔ (T.subgroupOf H) := by
          rw [← Subgroup.subgroupOf_sup hKH hT.le, hKTH, Subgroup.subgroupOf_self]
          exact Subgroup.mem_top _
        obtain ⟨k, hk, t, ht, hkt⟩ := Subgroup.mem_sup_of_normal_left.mp hmemH
        have hkK : (k : G) ∈ K := hk
        have htT : (t : G) ∈ T := ht
        have htL : (t : G) ∈ L := by
          have heq : (t : G) = (k : G)⁻¹ * (l : G) := by
            have h1 : (k : G) * (t : G) = (l : G) := congrArg Subtype.val hkt
            rw [← h1]; group
          rw [heq]
          exact L.mul_mem (L.inv_mem (hKL hkK)) l.2
        have htS : (t : G) ∈ S := ⟨htT, htL⟩
        refine Subgroup.mem_sup_of_normal_left.mpr
          ⟨⟨(k : G), hKL hkK⟩, ?_, ⟨(t : G), htL⟩, htS, ?_⟩
        · rw [MonoidHom.mem_ker, hkerK]; exact hkK
        · apply Subtype.ext
          simpa using congrArg Subtype.val hkt
      have hXle : (⊤ : Subgroup X) ≤ (S.subgroupOf L).map φ := by
        rw [← Subgroup.map_top_of_surjective φ hφ, Subgroup.map_le_map_iff, sup_comm]
        exact htop
      rw [hT0coe]
      exact le_antisymm le_top (hT0coe.symm ▸ hXle)
    exact hT0ne_top hT0top
  have hKM : K ≤ M := by
    obtain ⟨Y, hY, hle⟩ := exists_mem_calNIn_of_lt (H := H) (T := T)
      (Y := K ⊔ T) le_sup_right hKTlt
    rw [hcalN, Set.mem_singleton_iff] at hY
    exact (le_sup_left.trans (hY ▸ hle)).trans inf_le_right
  have hNlt : H ⊓ Subgroup.normalizer (S : Set G) < H := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    exact normS_false (by rw [← hEq]; exact inf_le_right)
  have hNleM : H ⊓ Subgroup.normalizer (S : Set G) ≤ M := by
    obtain ⟨Y, hY, hle⟩ := exists_mem_calNIn_of_lt (H := H) (T := T)
      (Y := H ⊓ normalizer (S : Set G)) (le_inf hT.le hTnormS) hNlt
    rw [hcalN, Set.mem_singleton_iff] at hY
    exact (hY ▸ hle).trans inf_le_right
  let Y₀ : Subgroup X := (((H ⊓ M) ⊓ L).subgroupOf L).map φ
  have hT0Y₀ : (T₀ : Subgroup X) ≤ Y₀ := by
    change (T₀ : Subgroup X) ≤ (((H ⊓ M) ⊓ L).subgroupOf L).map φ
    rw [hT0coe]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L
      (le_inf (le_inf (inf_le_left.trans hT.le) (inf_le_left.trans hTM)) inf_le_right))
  have hY0ne : Y₀ ≠ ⊤ := by
    intro hYtop
    have hLM : L ≤ (H ⊓ M) ⊔ K := by
      intro l hl
      have hlY : φ ⟨l, hl⟩ ∈ Y₀ := by rw [hYtop]; trivial
      obtain ⟨y, hy, hy_eq⟩ := Subgroup.mem_map.mp hlY
      have hyHM : (y : G) ∈ H ⊓ M := (Subgroup.mem_subgroupOf.mp hy).1
      have hkK : ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ K :=
        (hkerK _).mp (by rw [map_mul, map_inv, hy_eq, inv_mul_cancel])
      have hval : (y : G) * (((y⁻¹ * ⟨l, hl⟩ : ↥L)) : G) = (l : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [← hval]
      exact ((H ⊓ M) ⊔ K).mul_mem (Subgroup.mem_sup_left hyHM) (Subgroup.mem_sup_right hkK)
    have hLM_M : L ≤ M := hLM.trans (sup_le inf_le_right hKM)
    have hHleM : H ≤ M := by
      intro x hx
      obtain ⟨kk, hkk, nn, hnn, hxmul⟩ := frattini_argument hLH hLn hSylS hx
      rw [hxmul]
      exact M.mul_mem (hLM_M hkk) (hNleM hnn)
    exact hHM hHleM
  have hY0leN : Y₀ ≤ Subgroup.normalizer (T₀ : Set X) :=
    hD.le_normalizer_of_le hT0Y₀ hY0ne
  let B : Subgroup ↥L := (Subgroup.normalizer (T₀ : Set X)).comap φ
  have hHMl_B : ((H ⊓ M) ⊓ L).subgroupOf L ≤ B := by
    intro y hy
    rw [Subgroup.mem_comap]
    exact hY0leN (Subgroup.mem_map_of_mem φ hy)
  have hBkey : ∀ b ∈ B, SK.map (MulAut.conj (b : G)).toMonoidHom ≤ SK := by
    intro b hb
    have hbN : φ b ∈ Subgroup.normalizer (T₀ : Set X) := hb
    have hmapS : S.map (MulAut.conj (b : G)).toMonoidHom ≤ SK := by
      rintro _ ⟨s, hs, rfl⟩
      have hsL : s ∈ L := hs.2
      let bl : ↥L := b
      let sl : ↥L := ⟨s, hsL⟩
      have hslT0 : φ sl ∈ (T₀ : Subgroup X) := by
        rw [hT0coe]
        exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hs)
      have hxT : φ (bl * sl * bl⁻¹) ∈ (T₀ : Subgroup X) := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hbN (φ sl)).mp hslT0
      rw [hT0coe] at hxT
      obtain ⟨t, ht, ht_eq⟩ := Subgroup.mem_map.mp hxT
      have htS : (t : G) ∈ S := Subgroup.mem_subgroupOf.mp ht
      have htk : (t⁻¹ * (bl * sl * bl⁻¹) : ↥L) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ht_eq, inv_mul_cancel]
      have hkK : (((t⁻¹ * (bl * sl * bl⁻¹) : ↥L)) : G) ∈ K := (hkerK _).mp htk
      have hcoeeq : (((t⁻¹ * (bl * sl * bl⁻¹) : ↥L)) : G) =
          (t : G)⁻¹ * ((b : G) * s * (b : G)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, bl, sl]
      have hEq : (b : G) * s * (b : G)⁻¹ = (t : G) * (((t⁻¹ * (bl * sl * bl⁻¹) : ↥L)) : G) := by
        rw [hcoeeq]; group
      change (b : G) * s * (b : G)⁻¹ ∈ SK
      rw [hEq]
      exact SK.mul_mem (hSKdef.symm ▸ Subgroup.mem_sup_left htS)
        (hSKdef.symm ▸ Subgroup.mem_sup_right hkK)
    have hmapK : K.map (MulAut.conj (b : G)).toMonoidHom ≤ SK := by
      rw [(mem_normalizer_iff_map_conj.mp (hHnormK (hLH b.2)))]
      exact hSKdef.symm ▸ le_sup_right
    rw [hSKdef, Subgroup.map_sup]
    exact sup_le (hSKdef ▸ hmapS) (hSKdef ▸ hmapK)
  have hBleN : B.map L.subtype ≤ H ⊓ Subgroup.normalizer (SK : Set G) := by
    intro b hb
    obtain ⟨bl, hbl, rfl⟩ := Subgroup.mem_map.mp hb
    refine ⟨hLH bl.2, ?_⟩
    have hle := hBkey bl hbl
    have hcard : Nat.card (SK.map (MulAut.conj (bl : G)).toMonoidHom) = Nat.card SK :=
      Subgroup.card_map_of_injective (MulAut.conj (bl : G)).injective
    exact mem_normalizer_iff_map_conj.mpr
      (Subgroup.eq_of_le_of_card_ge (hSKdef ▸ hle) (le_of_eq hcard.symm))
  have hNSKlt : H ⊓ Subgroup.normalizer (SK : Set G) < H := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    exact normSK_false (by rw [← hEq]; exact inf_le_right)
  have hNSKleM : H ⊓ Subgroup.normalizer (SK : Set G) ≤ M := by
    obtain ⟨Y, hY, hle⟩ := exists_mem_calNIn_of_lt (H := H) (T := T)
      (Y := H ⊓ Subgroup.normalizer (SK : Set G)) (le_inf hT.le hTnormSK) hNSKlt
    rw [hcalN, Set.mem_singleton_iff] at hY
    exact (hY ▸ hle).trans inf_le_right
  have hBleM : B.map L.subtype ≤ M := hBleN.trans hNSKleM
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq X T₀ T₁
  have hT1sub : (T₁ : Subgroup X) = (T₀ : Subgroup X).map (MulAut.conj w).toMonoidHom := by
    rw [← hw, Sylow.coe_subgroup_smul (g := w) (P := T₀)]
    rfl
  obtain ⟨l, hl⟩ := hφ w
  have hl_notM : (l : G) ∉ M := by
    intro hlM
    have hlY : φ l ∈ Y₀ :=
      Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hLH l.2, hlM⟩, l.2⟩))
    have hwY : w ∈ Y₀ := hl ▸ hlY
    have hwN : w ∈ Subgroup.normalizer (T₀ : Set X) := hY0leN hwY
    exact hT1ne (by rw [← hw]; exact Sylow.smul_eq_iff_mem_normalizer.mpr hwN)
  obtain ⟨d, hdord⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 3 hD3
  have hdN0 : ((d : ↥D) : X) ∈ Subgroup.normalizer (T₀ : Set X) := hD.le d.2
  have hdXord : orderOf (((d : ↥D) : X)) = 3 := (Subgroup.orderOf_coe d).trans hdord
  obtain ⟨x₀, hx₀⟩ := hφ ((d : ↥D) : X)
  obtain ⟨k, m, hm, hdecomp⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₀).ne' 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hpos := orderOf_pos x₀
    rw [hdecomp, mul_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  have hmdvd : m ∣ orderOf x₀ := ⟨3 ^ k, by rw [hdecomp, mul_comm]⟩
  have hxord : orderOf (x₀ ^ m) = 3 ^ k := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hdecomp,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have h3dvd : 3 ∣ orderOf x₀ := by
    have h1 := orderOf_map_dvd φ x₀
    rw [hx₀, hdXord] at h1
    exact h1
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    have : 3 ∣ m := by
      rw [hdecomp, hk0, pow_zero, one_mul] at h3dvd
      exact h3dvd
    exact hm this
  have hx3 : 3 ∣ orderOf (x₀ ^ m) := by
    rw [hxord]
    exact dvd_pow_self 3 (by omega)
  have hxB : x₀ ^ m ∈ B := by
    rw [Subgroup.mem_comap, map_pow, hx₀]
    exact (Subgroup.normalizer (T₀ : Set X)).pow_mem hdN0 m
  have hxM : (((x₀ ^ m : ↥L)) : G) ∈ M :=
    hBleM (Subgroup.mem_map_of_mem L.subtype hxB)
  have hdmNT1 : (((d : ↥D) : X) ^ m) ∈ Subgroup.normalizer (T₁ : Set X) :=
    (Subgroup.normalizer (T₁ : Set X)).pow_mem (hDT1 d.2) m
  have hconjInv : ∀ y ∈ (T₁ : Subgroup X), w⁻¹ * y * w ∈ (T₀ : Subgroup X) := by
    intro y hy
    have hy' : y ∈ (T₀ : Subgroup X).map (MulAut.conj w).toMonoidHom := hT1sub ▸ hy
    obtain ⟨z, hz, hz_eq⟩ := Subgroup.mem_map.mp hy'
    rw [← hz_eq]
    simpa [MulAut.conj_apply, mul_assoc] using hz
  have hlxB : l⁻¹ * x₀ ^ m * l ∈ B := by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, map_pow, hx₀, hl]
    let gW : X := w⁻¹ * ((d : ↥D) : X) ^ m * w
    have hle : (T₀ : Subgroup X).map (MulAut.conj gW).toMonoidHom ≤ T₀ := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 : w * z * w⁻¹ ∈ (T₁ : Subgroup X) := by
        rw [hT1sub]
        exact Subgroup.mem_map.mpr ⟨z, hz, by rfl⟩
      have h2 : ((d : ↥D) : X) ^ m * (w * z * w⁻¹) * (((d : ↥D) : X) ^ m)⁻¹ ∈
          (T₁ : Subgroup X) := (Subgroup.mem_normalizer_iff.mp hdmNT1 _).mp h1
      have h3 := hconjInv _ h2
      change gW * z * gW⁻¹ ∈ (T₀ : Subgroup X)
      have h3' : gW * z * gW⁻¹ =
          w⁻¹ * (((d : ↥D) : X) ^ m * (w * z * w⁻¹) * (((d : ↥D) : X) ^ m)⁻¹) * w := by
        simp only [gW]; group
      rw [h3']
      exact h3
    have hcard : Nat.card ((T₀ : Subgroup X).map (MulAut.conj gW).toMonoidHom) =
        Nat.card (T₀ : Subgroup X) :=
      Subgroup.card_map_of_injective (MulAut.conj gW).injective
    exact mem_normalizer_iff_map_conj.mpr
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))
  have hlxM : (((l⁻¹ * x₀ ^ m * l : ↥L)) : G) ∈ M :=
    hBleM (Subgroup.mem_map_of_mem L.subtype hlxB)
  have hxM' : (((x₀ ^ m : ↥L)) : G) ∈
      M ⊓ M.map (MulAut.conj (l : G)).toMonoidHom := by
    refine ⟨hxM, ?_⟩
    refine Subgroup.mem_map.mpr ⟨(((l⁻¹ * x₀ ^ m * l : ↥L)) : G), hlxM, ?_⟩
    show (l : G) * (((l⁻¹ * x₀ ^ m * l : ↥L)) : G) * (l : G)⁻¹ = (((x₀ ^ m : ↥L)) : G)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hzp : Subgroup.zpowers (((x₀ ^ m : ↥L)) : G) ≤
      M ⊓ M.map (MulAut.conj (l : G)).toMonoidHom := Subgroup.zpowers_le.mpr hxM'
  have h3G : 3 ∣ orderOf (((x₀ ^ m : ↥L)) : G) := by
    rw [Subgroup.orderOf_coe]; exact hx3
  have h3div : 3 ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj (l : G)).toMonoidHom) := by
    have h1 : Nat.card (Subgroup.zpowers (((x₀ ^ m : ↥L)) : G)) ∣
        Nat.card ↥(M ⊓ M.map (MulAut.conj (l : G)).toMonoidHom) :=
      Subgroup.card_dvd_of_le hzp
    rw [Nat.card_zpowers] at h1
    exact h3G.trans h1
  exact hsp.2.2 (l : G) hl_notM h3div

theorem not_shape_four {H T M : Subgroup G}
    (hT : IsSylowIn 2 T H) (hTM : T ≤ M) (hHM : ¬ H ≤ M) (hcalN : calNIn H T = {H ⊓ M})
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M) (n : ℕ) (hn : 1 ≤ n) :
    ¬ (HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set G)
          (fun X _ => IsL2 X (2 * n)) ∨
        HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set G)
          (fun X _ => IsU3 X (2 * n))) := by
  rintro (⟨X, hXgrp, φ, hφ, hker, hL2⟩ | ⟨X, hXgrp, φ, hφ, hker, hU3⟩)
  · letI : Group X := hXgrp
    have hBender : fusionIsBenderGroup X :=
      CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psl_two hL2
    haveI : Finite X := by
      rcases hBender with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
      · exact Finite.of_equiv _ e.symm.toEquiv
      · exact Finite.of_equiv _ e.symm.toEquiv
      · exact Finite.of_equiv _ e.symm.toEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2n : 2 ≤ 2 * n := by omega
    have h3D : ∀ (P : Sylow 2 X) (D : Subgroup X),
        CFSG.Goldschmidt.G3a.BorelSetup P D → 3 ∣ Nat.card D := by
      intro P D hD
      have hcl := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL2
      obtain ⟨-, Kf, hKf_field, hKf_fin, hKf_card, ⟨e⟩⟩ := hcl
      letI : Field Kf := hKf_field
      letI : Finite Kf := hKf_fin
      have e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * n)) :=
        e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL Kf 2 2 (2 * n)
          (by omega) hKf_card)
      obtain ⟨-, hDcard, -⟩ := hD.orders_psl2 h2n e'
      rw [hDcard]
      have hpow : (2 : ℕ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
      rw [hpow]
      exact three_dvd_four_pow_sub_one n
    exact false_of_borel_lift hT hTM hHM hcalN hsp hBender h3D
      (Subgroup.map_subtype_le _) (fStarMod_normal _ _)
      (le_fStarMod (relPPrimeCore_le H) (relPPrimeCore_normal (p := 3) (by norm_num) H))
      (relPPrimeCore_normal (p := 3) (by norm_num) H)
      hφ hker
  · letI : Group X := hXgrp
    have hBender : fusionIsBenderGroup X :=
      CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psu_three hU3
    haveI : Finite X := by
      rcases hBender with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
      · exact Finite.of_equiv _ e.symm.toEquiv
      · exact Finite.of_equiv _ e.symm.toEquiv
      · exact Finite.of_equiv _ e.symm.toEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2n : 2 ≤ 2 * n := by omega
    have h3D : ∀ (P : Sylow 2 X) (D : Subgroup X),
        CFSG.Goldschmidt.G3a.BorelSetup P D → 3 ∣ Nat.card D := by
      intro P D hD
      have hcl := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU3
      obtain ⟨-, Kf, hKf_field, hKf_fin, hKf_card, ⟨e⟩⟩ := hcl
      letI : Field Kf := hKf_field
      letI : Finite Kf := hKf_fin
      have hcard : Nat.card Kf = 2 ^ (2 * (2 * n)) := by
        rw [hKf_card, ← pow_mul]
        congr 1
        ring
      let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) Kf (2 ^ (2 * n))) := e
      have e'' : X ≃* ↥(PSU3 2 (2 * n)) :=
        e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative (2 * n) h2n hcard)
      obtain ⟨-, -, hDcard⟩ := hD.orders_psu3 h2n e''
      have hgcd : Nat.gcd 3 (2 ^ (2 * n) + 1) = 1 := by
        have hpow : (2 : ℕ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
        rw [hpow]
        exact nat_gcd_three_four_pow_add_one n
      have h3 : 3 ∣ (2 ^ (2 * n)) ^ 2 - 1 := by
        have hpow : (2 : ℕ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
        rw [hpow, ← pow_mul, show n * 2 = 2 * n by ring]
        exact three_dvd_four_pow_sub_one (2 * n)
      rw [hDcard, hgcd, Nat.div_one]
      exact h3
    exact false_of_borel_lift hT hTM hHM hcalN hsp hBender h3D
      (Subgroup.map_subtype_le _) (fStarMod_normal _ _)
      (le_fStarMod (relPPrimeCore_le H) (relPPrimeCore_normal (p := 3) (by norm_num) H))
      (relPPrimeCore_normal (p := 3) (by norm_num) H)
      hφ hker

@[expose] def Shape512Four {Q : Type} [Group Q] [Finite Q] (H : Subgroup Q) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    (HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
        (fun X _ => IsL2 X (2 * n)) ∨
      HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
        (fun X _ => IsU3 X (2 * n)))

theorem not_shape512Four_of_calNIn {H T M : Subgroup G}
    (hT : IsSylowIn 2 T H) (hTM : T ≤ M) (hHM : ¬ H ≤ M) (hcalN : calNIn H T = {H ⊓ M})
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M) : ¬ Shape512Four H := by
  rintro ⟨n, hn, h⟩
  exact not_shape_four hT hTM hHM hcalN hsp n hn h

end CFSG.LocalAnalysis.WeakClosure81

end
