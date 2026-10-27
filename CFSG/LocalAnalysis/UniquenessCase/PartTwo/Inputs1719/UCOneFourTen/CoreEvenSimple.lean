module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Quot
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.AlmostSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem false_of_pCoreOf_eq_bot_of_even {K L T Y : Subgroup X} {n : ℕ}
    (hcomp : ∀ t : ↥K ⧸ center ↥K, orderOf t = 2 →
      ∀ B : Subgroup (centralizer ({t} : Set (↥K ⧸ center ↥K))), ¬ CFSG.IsComponent B)
    (hO2 : CFSG.pCore 2 X = ⊥) (hKn : K.Normal) (hLK : L ≤ K) (hSz : IsSz (Bar2 L) n)
    (hL2 : CFSG.Open.pCoreOf 2 L = ⊥)
    (hSyl : IsSylowOf 2 T (F08.CentOverO2 Y L))
    (hA : ∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set X) ≤ Y)
    (hT2 : ∀ X₁ : Subgroup X, X₁ ≠ ⊤ → L ≤ X₁ → T ≤ X₁ → CFSG.Open.IsSubnormal L X₁)
    (heven : Even (Nat.card ↥(K ⊓ centralizer (L : Set X)))) : False := by
  classical
  have hCY : centralizer (L : Set X) ≤ Y := centralizer_le_of_normalizer_le hSz hA
  have hCent : F08.CentOverO2 Y L = centralizer (L : Set X) := by
    rw [centOverO2_eq_of_pCoreOf_eq_bot hL2, inf_eq_right.mpr hCY]
  have hSylC : IsSylowOf 2 T (centralizer (L : Set X)) := by
    rwa [hCent] at hSyl
  let C : Subgroup X := centralizer (L : Set X)
  let A0 : Subgroup X := K ⊓ C
  have hA0even : Even (Nat.card ↥A0) := by simpa [A0, C] using heven
  have hA0norm : C ≤ normalizer (A0 : Set X) := by
    refine (le_inf (@Subgroup.le_normalizer_of_normal X _ K C hKn)
      Subgroup.le_normalizer).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := K) (K := C)
  have hSylA0 : IsSylowOf 2 (T ⊓ A0) A0 :=
    IsSylowOf.inf_of_le_normalizer hSylC inf_le_right hA0norm
  have hTleC : T ≤ C := hSylC.le
  have hTgroup : IsPGroup 2 T := hSylC.isPGroup
  have hfac : 0 < (Nat.card ↥A0).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos.ne')
      (even_iff_two_dvd.mp hA0even)
  have hcardP : Nat.card ↥(T ⊓ A0) = 2 ^ (Nat.card ↥A0).factorization 2 :=
    hSylA0.card_eq
  have hPne : T ⊓ A0 ≠ ⊥ := by
    intro hbot
    have h2 : 2 ≤ Nat.card ↥(T ⊓ A0) := by
      rw [hcardP]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.card ↥A0).factorization 2 :=
            Nat.pow_le_pow_right (by norm_num) hfac
    rw [hbot] at h2
    simp at h2
  have hNnormal : ((T ⊓ A0).subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    refine (le_inf Subgroup.le_normalizer ?_).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    exact hTleC.trans hA0norm
  let Em : Subgroup ↥T := (T ⊓ A0).subgroupOf T ⊓ Subgroup.center ↥T
  have hNne : (T ⊓ A0).subgroupOf T ≠ ⊥ := by
    intro h
    apply hPne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥T) ∈ (T ⊓ A0).subgroupOf T := hx
    rw [h] at hxN
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxN)
  have hEne : Em ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      (p := 2) hTgroup ((T ⊓ A0).subgroupOf T) hNne
  have hE2 : IsPGroup 2 Em := hTgroup.to_subgroup Em
  have hEeven : 2 ∣ Nat.card ↥Em := by
    rcases hE2.card_eq_or_dvd with h1 | h2
    · exact absurd ((Subgroup.card_eq_one (H := Em)).mp h1) hEne
    · exact h2
  obtain ⟨u, hu_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥Em) 2 hEeven
  have huE : (u : ↥T) ∈ Em := u.2
  let zT : ↥T := (u : ↥T)
  let z : X := (zT : X)
  have hzP : z ∈ T ⊓ A0 := by
    have h : zT ∈ (T ⊓ A0).subgroupOf T := (Subgroup.mem_inf.mp huE).1
    rwa [Subgroup.mem_subgroupOf] at h
  have hzT : z ∈ T := hzP.1
  have hzK : z ∈ K := hzP.2.1
  have hz_comm : ∀ t ∈ T, t * z = z * t := by
    intro t ht
    have h := (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp huE).2) ⟨t, ht⟩
    exact congrArg Subtype.val h
  have hz_order : orderOf z = 2 := by
    change orderOf ((u : ↥T) : X) = 2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hu_order
  have hz_ne : z ≠ 1 := by
    intro h
    rw [h] at hz_order
    simp at hz_order
  let Cz : Subgroup X := centralizer ({z} : Set X)
  have hzC : z ∈ C := hTleC hzT
  have hL_Cz : L ≤ Cz := by
    intro l hl
    change l ∈ centralizer ({z} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzC) l hl
  have hT_Cz : T ≤ Cz := by
    intro t ht
    change t ∈ centralizer ({z} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hz_comm t ht
  have hCz_ne_top : Cz ≠ ⊤ := by
    intro htop
    have hzcenter : z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cz := by rw [htop]; exact Subgroup.mem_top g
      change g ∈ centralizer ({z} : Set X) at hg
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hnorm : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem hzcenter)
    have hp2 : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz_order, pow_one])
    have hle : Subgroup.zpowers z ≤ CFSG.pCore 2 X :=
      CFSG.LieType.BorelTits.le_pCore 2 hnorm hp2
    rw [hO2, le_bot_iff] at hle
    have hzbot : z ∈ (⊥ : Subgroup X) := by
      rw [← hle]
      exact Subgroup.mem_zpowers z
    exact hz_ne (Subgroup.mem_bot.mp hzbot)
  have hsubCz : CFSG.Open.IsSubnormal L Cz := hT2 Cz hCz_ne_top hL_Cz hT_Cz
  let Kz : Subgroup X := K ⊓ Cz
  have hsubKz : CFSG.Open.IsSubnormal L Kz :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410.isSubnormal_mono hsubCz
      (le_inf hLK hL_Cz) inf_le_right
  have hZodd : Odd (Nat.card ↥(Subgroup.center ↥K)) := odd_card_center_of_normal hO2 hKn
  have hLsimpleBar : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have hLcore : CFSG.pCore 2 ↥L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
      (by simpa [CFSG.Open.pCoreOf] using hL2)
  let eBar : Bar2 L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hLcore).trans QuotientGroup.quotientBot
  have hSimpleL : IsSimpleGroup ↥L := eBar.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz
  have hNonabL : ∃ a b : ↥L, a * b ≠ b * a := by
    refine ⟨eBar a, eBar b, ?_⟩
    intro h
    apply hab
    have h' : eBar (a * b) = eBar (b * a) := by rw [map_mul, map_mul, h]
    exact eBar.injective h'
  have hLq : CFSG.IsQuasisimple ↥L :=
    (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ↥L _ hSimpleL hNonabL).1
  have hcenterL : Subgroup.center ↥L = ⊥ :=
    (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ↥L _ hSimpleL hNonabL).2
  let ZK : Subgroup ↥K := Subgroup.center ↥K
  let S := ↥K ⧸ ZK
  let mkK : ↥K →* S := QuotientGroup.mk' ZK
  let zK : ↥K := ⟨z, hzK⟩
  let t : S := mkK zK
  have hzK_order : orderOf zK = 2 := by
    have h := (Subgroup.orderOf_coe zK).symm.trans hz_order
    simpa [zK] using h
  let Cbar : Subgroup S := Subgroup.centralizer ({t} : Set S)
  have hCeq : Cbar = (Subgroup.centralizer ({zK} : Set ↥K)).map mkK := by
    change Subgroup.centralizer ({QuotientGroup.mk zK} : Set (↥K ⧸ ZK)) =
      (Subgroup.centralizer ({zK} : Set ↥K)).map (QuotientGroup.mk' ZK)
    exact CFSG.OddStandard.Seitz77.centralizer_map_of_odd (M := ZK) hZodd (t := zK)
      hzK_order
  have hCentK : Subgroup.centralizer ({zK} : Set ↥K) = Kz.subgroupOf K := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      change x.1 ∈ centralizer ({z} : Set X)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hx
    · rintro ⟨-, hxz⟩
      change x.1 ∈ centralizer ({z} : Set X) at hxz
      rw [Subgroup.mem_centralizer_singleton_iff] at hxz
      exact Subtype.ext hxz
  let ρ0 : ↥L →* S := mkK.comp (Subgroup.inclusion hLK)
  have hker : ∀ l : ↥L, ρ0 l = 1 → l = 1 := by
    intro l hl
    change mkK ⟨l.1, hLK l.2⟩ = 1 at hl
    have hmem : (⟨l.1, hLK l.2⟩ : ↥K) ∈ ZK := (QuotientGroup.eq_one_iff _).mp hl
    have hcent : l ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro m
      have h := (Subgroup.mem_center_iff.mp hmem) ⟨m.1, hLK m.2⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val h
    rw [hcenterL] at hcent
    exact Subgroup.mem_bot.mp hcent
  have hρ0inj : Function.Injective ρ0 := by
    intro a b hab
    have h1 : ρ0 (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker (a * b⁻¹) h1)
  have hρ0_mem : ∀ l : ↥L, ρ0 l ∈ Cbar := by
    intro l
    change ρ0 l ∈ Subgroup.centralizer ({t} : Set S)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change mkK ⟨l.1, hLK l.2⟩ * mkK zK = mkK zK * mkK ⟨l.1, hLK l.2⟩
    have hcomm : (⟨l.1, hLK l.2⟩ : ↥K) * zK = zK * ⟨l.1, hLK l.2⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hzC) l.1 l.2
    rw [← map_mul, ← map_mul, hcomm]
  let ρ : ↥L →* ↥Cbar := ρ0.codRestrict Cbar hρ0_mem
  have hρinj : Function.Injective ρ := by
    intro a b hab
    exact hρ0inj (congrArg Subtype.val hab)
  let B : Subgroup ↥Cbar := ρ.range
  have hBq : CFSG.IsQuasisimple ↥B := by
    have e : ↥L ≃* ↥B := MonoidHom.ofInjective hρinj
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hLq
  let φ0 : ↥Kz →* S := mkK.comp (Subgroup.inclusion inf_le_left)
  have hφ0_mem : ∀ x : ↥Kz, φ0 x ∈ Cbar := by
    intro x
    change φ0 x ∈ Subgroup.centralizer ({t} : Set S)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change mkK ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩ * mkK zK =
      mkK zK * mkK ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩
    have hxz : x.1 ∈ centralizer ({z} : Set X) := (Subgroup.mem_inf.mp x.2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxz
    have hcomm : (⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩ : ↥K) * zK =
        zK * ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩ := by
      apply Subtype.ext
      exact hxz
    rw [← map_mul, ← map_mul, hcomm]
  let φ : ↥Kz →* ↥Cbar := φ0.codRestrict Cbar hφ0_mem
  have hφsurj : Function.Surjective φ := by
    intro c
    have hc : (c : S) ∈ (Subgroup.centralizer ({zK} : Set ↥K)).map mkK := by
      rw [← hCeq]
      exact c.2
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hc
    have hyKz : (y : X) ∈ Kz := by
      have hy' : y ∈ Kz.subgroupOf K := by
        rw [← hCentK]
        exact hy
      exact (Subgroup.mem_subgroupOf).mp hy'
    refine ⟨⟨y, hyKz⟩, ?_⟩
    apply Subtype.ext
    exact hyc
  have hB_eq : B = (L.subgroupOf Kz).map φ := by
    ext b
    constructor
    · intro hb
      change b ∈ ρ.range at hb
      rw [MonoidHom.mem_range] at hb
      obtain ⟨l, rfl⟩ := hb
      rw [Subgroup.mem_map]
      refine ⟨⟨l.1, le_inf hLK hL_Cz l.2⟩, ?_, ?_⟩
      · exact l.2
      · apply Subtype.ext
        rfl
    · intro hb
      rw [Subgroup.mem_map] at hb
      obtain ⟨x, hx, rfl⟩ := hb
      change (φ x) ∈ ρ.range
      rw [MonoidHom.mem_range]
      refine ⟨⟨x.1, hx⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hBsub : B.IsSubnormal := by
    rw [hB_eq]
    exact (CFSG.Open.IsSubnormal.subgroupOf hsubKz).map hφsurj
  have hz_sq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz_order, pow_two] at h
  have hzK_sq : zK * zK = 1 := by
    apply Subtype.ext
    exact hz_sq
  have ht_ne : t ≠ 1 := by
    intro ht1
    have hzcenter : zK ∈ ZK := (QuotientGroup.eq_one_iff zK).mp ht1
    have h2dvd : 2 ∣ Nat.card ↥ZK := hzK_order ▸ Subgroup.orderOf_dvd_natCard ZK hzcenter
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2dvd)
  have ht_sq : t * t = 1 := by
    change mkK zK * mkK zK = 1
    rw [← map_mul, ← map_one mkK, hzK_sq]
  have ht : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ht_sq) ht_ne
  exact hcomp t ht B ⟨hBq, hBsub⟩


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
