module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
public import CFSG.Milestones.ASVolI.I2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsPerm
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndWeakClosure
import CFSG.GF2Type.Aschbacher1976Full.HSBurnside
import CFSG.GroupTheory.CardMapInfKer
public import CFSG.Fischer.Classification.Unitary.Coords
public import CFSG.LargeExtraspecial.AS35QThModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem A_le_centralizer (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A) :
    F.A ≤ Subgroup.centralizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg (fun z : ↥F.A => (z : G))
    (F.elemAbelian.1.is_comm.comm ⟨y, hBA hy⟩ ⟨x, hx⟩)

private theorem deg_zpowers_eq_deg_of_card_three (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    F.deg (Subgroup.zpowers b) = F.deg B := by
  have hbA : b ∈ F.A := hBA hb
  have hZB : Subgroup.zpowers b = B := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (F.elemAbelian.2 b hbA) hb1, hB3]
  rw [hZB]

private theorem phiA_ne_one_of_mem_A (F : A10Frame c) {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1) :
    F.phiA ⟨a, F.A_le_M haA⟩ ≠ 1 := by
  intro h
  have hker : (⟨a, F.A_le_M haA⟩ : ↥D.M) ∈ F.phiA.ker := MonoidHom.mem_ker.mpr h
  have ha3 : (⟨a, F.A_le_M haA⟩ : ↥D.M) ^ 3 = 1 := by
    apply Subtype.ext
    exact F.elemAbelian.2 a haA
  have hord3 : orderOf (⟨a, F.A_le_M haA⟩ : ↥D.M) ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
  have hordK : orderOf (⟨a, F.A_le_M haA⟩ : ↥D.M) ∣ Nat.card F.phiA.ker :=
    Subgroup.orderOf_dvd_natCard _ hker
  have hone : orderOf (⟨a, F.A_le_M haA⟩ : ↥D.M) = 1 :=
    Nat.eq_one_of_dvd_coprimes F.coprime_card_ker_phiA.symm hord3 hordK
  exact ha1 (congrArg Subtype.val (orderOf_eq_one_iff.mp hone))

private theorem conj_mem_A_of_conjugate_le (F : A10Frame c) {B : Subgroup G}
    {a : G} (haA : a ∈ F.A) (hAH : F.A ≤ Subgroup.centralizer (B : Set G))
    {g : ↥(Subgroup.centralizer (B : Set G))}
    (hg : CFSG.conjugate ((Subgroup.zpowers a).subgroupOf
        (Subgroup.centralizer (B : Set G))) g ≤
      F.A.subgroupOf (Subgroup.centralizer (B : Set G))) :
    (g : G)⁻¹ * a * (g : G) ∈ F.A := by
  let H := Subgroup.centralizer (B : Set G)
  let aH : H := ⟨a, hAH haA⟩
  have haH : aH ∈ (Subgroup.zpowers a).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a)
  have hmem : (MulAut.conj (g⁻¹)) aH ∈
      CFSG.conjugate ((Subgroup.zpowers a).subgroupOf H) g :=
    Subgroup.mem_map_of_mem (MulAut.conj (g⁻¹)).toMonoidHom haH
  have hres := Subgroup.mem_subgroupOf.mp (hg hmem)
  simpa [H, aH, MulAut.conj_apply] using hres

private theorem map_subgroupOf_eq_atilde (F : A10Frame c)
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6)
    {T : Subgroup G} (hAT : F.A ≤ T) (hT3 : IsPGroup 3 T)
    (hTC : T ≤ Subgroup.centralizer (B : Set G)) :
    (T.subgroupOf D.M).map F.phiA = A10Perm.atilde := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup (Equiv.Perm (Fin 10)) := (T.subgroupOf D.M).map F.phiA
  have hQp : IsPGroup 3 Q := hT3.comap_subtype.map F.phiA
  have hAtQ : A10Perm.atilde ≤ Q := by
    rw [← F.map_A_phiA]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hAT)
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hB3
    norm_num at hB3
  obtain ⟨bB, hbB1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := B)).mp hBne
  let b : G := bB
  have hb : b ∈ B := bB.2
  have hb1 : b ≠ 1 := fun h => hbB1 (Subtype.ext h)
  have hx6 : (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support.card = 6 := by
    rw [← F.deg_zpowers_eq (F.P_le_L (F.A_le (hBA hb))),
      deg_zpowers_eq_deg_of_card_three F hBA hB3 hb hb1, hB6]
  have hx_at : F.phiA ⟨b, F.A_le_M (hBA hb)⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr (hBA hb))
  have hQK : Q ≤ Subgroup.centralizer
      ({F.phiA ⟨b, F.A_le_M (hBA hb)⟩} : Set (Equiv.Perm (Fin 10))) := by
    rintro y ⟨t, ht, rfl⟩
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have htb : b * (t : G) = (t : G) * b :=
      (Subgroup.mem_centralizer_iff.mp (hTC htT)) b hb
    have hsub : t * (⟨b, F.A_le_M (hBA hb)⟩ : ↥D.M) =
        ⟨b, F.A_le_M (hBA hb)⟩ * t := Subtype.ext htb.symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc F.phiA t * F.phiA ⟨b, F.A_le_M (hBA hb)⟩ =
          F.phiA (t * ⟨b, F.A_le_M (hBA hb)⟩) := (map_mul _ _ _).symm
      _ = F.phiA (⟨b, F.A_le_M (hBA hb)⟩ * t) := by rw [hsub]
      _ = F.phiA ⟨b, F.A_le_M (hBA hb)⟩ * F.phiA t := map_mul _ _ _
  exact (A10Perm.isSylowOf_atilde hx_at (Or.inr hx6)).eq_of_le hAtQ hQK hQp

private theorem card_eq_27_of_map_eq_atilde (F : A10Frame c)
    {T : Subgroup G} (hT3 : IsPGroup 3 T) (hTM : T ≤ D.M)
    (hmap : (T.subgroupOf D.M).map F.phiA = A10Perm.atilde) :
    Nat.card T = 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTsubp : IsPGroup 3 (T.subgroupOf D.M) := hT3.comap_subtype
  obtain ⟨m, hm⟩ := hTsubp.exists_card_eq
  have hdisj : (T.subgroupOf D.M) ⊓ F.phiA.ker = ⊥ := by
    have hcop : Nat.Coprime (Nat.card (T.subgroupOf D.M)) (Nat.card F.phiA.ker) := by
      rw [hm]
      exact Nat.Coprime.pow_left m F.coprime_card_ker_phiA.symm
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hsubcard : Nat.card (T.subgroupOf D.M) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv
  have hcardmap : Nat.card ((T.subgroupOf D.M).map F.phiA) = Nat.card (T.subgroupOf D.M) :=
    CFSG.card_map_eq_card_of_inf_ker_eq_bot F.phiA hdisj
  rw [← hsubcard, ← hcardmap, hmap, A10Perm.card_atilde]

theorem isSylowOf_A_centralizer_of_deg_six (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) :
    CFSG.ABGLocalTools.IsSylowOf 3 F.A (Subgroup.centralizer (B : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := Subgroup.centralizer (B : Set G)
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  have hAp : IsPGroup 3 (F.A.subgroupOf H) := F.elemAbelian.isPGroup.comap_subtype
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  let T : Subgroup G := (S : Subgroup H).map H.subtype
  have hT3 : IsPGroup 3 T := S.isPGroup'.map H.subtype
  have hTC : T ≤ H := Subgroup.map_subtype_le _
  have hAT : F.A ≤ T := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hAH hx⟩, hAS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTM : T ≤ D.M := F.le_M_of_isPGroup hNA hT3 hAT
  have hmap : (T.subgroupOf D.M).map F.phiA = A10Perm.atilde :=
    map_subgroupOf_eq_atilde F hBA hB3 hB6 hAT hT3 hTC
  have hTcard : Nat.card T = 27 := card_eq_27_of_map_eq_atilde F hT3 hTM hmap
  have hTA : T = F.A :=
    (Subgroup.eq_of_le_of_card_ge hAT (by rw [hTcard, F.card_A])).symm
  refine ⟨S, ?_⟩
  change T = F.A
  exact hTA

private theorem conjugate_zpowers_subgroupOf_eq_of_mem_zpowers (F : A10Frame c)
    {B : Subgroup G} (hBA : B ≤ F.A) {a : G} (haA : a ∈ F.A)
    {g : ↥(Subgroup.centralizer (B : Set G))}
    (ha' : (g : G)⁻¹ * a * (g : G) ∈ Subgroup.zpowers a) :
    CFSG.conjugate ((Subgroup.zpowers a).subgroupOf
        (Subgroup.centralizer (B : Set G))) g =
      (Subgroup.zpowers a).subgroupOf (Subgroup.centralizer (B : Set G)) := by
  let H := Subgroup.centralizer (B : Set G)
  let X := ↥H
  let aH : X := ⟨a, A_le_centralizer F hBA haA⟩
  let a' : G := (g : G)⁻¹ * a * (g : G)
  have ha'Za : a' ∈ Subgroup.zpowers a := by simpa [a'] using ha'
  have ha'H : a' ∈ H := (Subgroup.zpowers_le.mpr (A_le_centralizer F hBA haA)) ha'Za
  have hQ : (Subgroup.zpowers a).subgroupOf H = Subgroup.zpowers aH := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [aH] using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [aH] using congrArg Subtype.val hk⟩
  have hconj_eq : CFSG.conjugate (Subgroup.zpowers aH) g =
      Subgroup.zpowers ((MulAut.conj (g⁻¹)) aH) := by
    rw [CFSG.conjugate, MonoidHom.map_zpowers]
    rfl
  have hconjA : (MulAut.conj (g⁻¹)) aH = (⟨a', ha'H⟩ : X) := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    simp [aH, a']
  have ha'X : (⟨a', ha'H⟩ : X) ∈ Subgroup.zpowers aH := by
    rw [← hQ]
    exact Subgroup.mem_subgroupOf.mpr ha'Za
  have hle : CFSG.conjugate ((Subgroup.zpowers a).subgroupOf H) g ≤
      (Subgroup.zpowers a).subgroupOf H := by
    rw [hQ, hconj_eq, hconjA]
    exact Subgroup.zpowers_le.mpr ha'X
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj (g⁻¹)).injective]

private theorem mul_comm_of_mem_subgroupOf (F : A10Frame c) {H : Subgroup G}
    {x y : ↥H} (hx : x ∈ F.A.subgroupOf H) (hy : y ∈ F.A.subgroupOf H) :
    x * y = y * x := by
  have hx' : (x : G) ∈ F.A := Subgroup.mem_subgroupOf.mp hx
  have hy' : (y : G) ∈ F.A := Subgroup.mem_subgroupOf.mp hy
  exact Subtype.ext (congrArg (fun z : ↥F.A => (z : G))
    (F.elemAbelian.1.is_comm.comm ⟨x, hx'⟩ ⟨y, hy'⟩))

private theorem exists_burnside_normalizer (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M)
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6)
    {a : G} (haA : a ∈ F.A)
    {g : ↥(Subgroup.centralizer (B : Set G))}
    (hg : CFSG.conjugate ((Subgroup.zpowers a).subgroupOf
        (Subgroup.centralizer (B : Set G))) g ≤
      F.A.subgroupOf (Subgroup.centralizer (B : Set G))) :
    ∃ n : ↥(Subgroup.centralizer (B : Set G)),
      n ∈ Subgroup.normalizer
        ((F.A.subgroupOf (Subgroup.centralizer (B : Set G)) :
          Subgroup ↥(Subgroup.centralizer (B : Set G))) : Set _) ∧
      (n : G) * a * (n : G)⁻¹ = (g : G)⁻¹ * a * (g : G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := Subgroup.centralizer (B : Set G)
  let X := ↥H
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  obtain ⟨P, hP⟩ := F.isSylowOf_A_centralizer_of_deg_six hNA hBA hB3 hB6
  have hPsub : (P : Subgroup X) = F.A.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
  have hab : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x := by
    intro x hx y hy
    exact mul_comm_of_mem_subgroupOf F (by rwa [hPsub] at hx) (by rwa [hPsub] at hy)
  have hweak : ∀ z : X, CFSG.conjugate (P : Subgroup X) z ≤ (P : Subgroup X) →
      CFSG.conjugate (P : Subgroup X) z = (P : Subgroup X) := by
    intro z hz
    refine Subgroup.eq_of_le_of_card_ge hz ?_
    rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj (z⁻¹)).injective]
  let aH : X := ⟨a, hAH haA⟩
  have haH : aH ∈ (Subgroup.zpowers a).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a)
  have haP : aH ∈ (P : Subgroup X) := by
    rw [hPsub]
    exact Subgroup.mem_subgroupOf.mpr haA
  have hginv : (g⁻¹) * aH * (g⁻¹)⁻¹ ∈ (P : Subgroup X) := by
    rw [hPsub]
    have hmem := hg (Subgroup.mem_map_of_mem (MulAut.conj (g⁻¹)).toMonoidHom haH)
    simpa [H, X, aH, MulAut.conj_apply] using hmem
  obtain ⟨n, hnN, hnconj⟩ :=
    CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion P (P : Subgroup X) le_rfl
      hab hweak haP hginv
  refine ⟨n, ?_, ?_⟩
  · rwa [hPsub] at hnN
  · have h := congrArg (fun z : X => (z : G)) hnconj
    simpa [H, X, aH, mul_assoc] using h

private theorem mem_normalizer_of_mem_normalizer_subgroupOf (F : A10Frame c)
    {B : Subgroup G} (hAH : F.A ≤ Subgroup.centralizer (B : Set G))
    {n : ↥(Subgroup.centralizer (B : Set G))}
    (hnNA : n ∈ Subgroup.normalizer
      ((F.A.subgroupOf (Subgroup.centralizer (B : Set G)) :
        Subgroup ↥(Subgroup.centralizer (B : Set G))) : Set _)) :
    (n : G) ∈ Subgroup.normalizer (F.A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro x ⟨y, hyA, rfl⟩
    show (MulAut.conj (n : G)) y ∈ F.A
    rw [MulAut.conj_apply]
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp hnNA ⟨y, hAH hyA⟩).mp
        (Subgroup.mem_subgroupOf.mpr hyA))
  · intro x hx
    refine ⟨(n : G)⁻¹ * x * (n : G), ?_, ?_⟩
    · show (n : G)⁻¹ * x * (n : G) ∈ F.A
      have h := Subgroup.mem_subgroupOf.mp
        ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnNA) ⟨x, hAH hx⟩).mp
          (Subgroup.mem_subgroupOf.mpr hx))
      simpa using h
    · show (MulAut.conj (n : G)) ((n : G)⁻¹ * x * (n : G)) = x
      rw [MulAut.conj_apply]
      group

private theorem exists_fusion_data (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M)
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6)
    {a b a' : G} (hb : b ∈ B) (haA : a ∈ F.A) (ha'A : a' ∈ F.A)
    {g : ↥(Subgroup.centralizer (B : Set G))}
    (ha'def : a' = (g : G)⁻¹ * a * (g : G))
    (hg : CFSG.conjugate ((Subgroup.zpowers a).subgroupOf
        (Subgroup.centralizer (B : Set G))) g ≤
      F.A.subgroupOf (Subgroup.centralizer (B : Set G))) :
    ∃ n : ↥D.M, (n : G) ∈ Subgroup.centralizer (B : Set G) ∧
      F.phiA n * F.phiA ⟨b, F.A_le_M (hBA hb)⟩ =
        F.phiA ⟨b, F.A_le_M (hBA hb)⟩ * F.phiA n ∧
      F.phiA n ∈ Subgroup.normalizer (A10Perm.atilde : Set (Equiv.Perm (Fin 10))) ∧
      F.phiA ⟨a', F.A_le_M ha'A⟩ =
        F.phiA n * F.phiA ⟨a, F.A_le_M haA⟩ * (F.phiA n)⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := Subgroup.centralizer (B : Set G)
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  obtain ⟨n, hnNA, hnconjG⟩ :=
    exists_burnside_normalizer F hNA hBA hB3 hB6 haA hg
  have hnG : (n : G) ∈ Subgroup.normalizer (F.A : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf F hAH hnNA
  have hnM : (n : G) ∈ D.M := hNA hnG
  have hnb : b * (n : G) = (n : G) * b :=
    (Subgroup.mem_centralizer_iff.mp n.2) b hb
  have hxcomm : F.phiA ⟨(n : G), hnM⟩ * F.phiA ⟨b, F.A_le_M (hBA hb)⟩ =
      F.phiA ⟨b, F.A_le_M (hBA hb)⟩ * F.phiA ⟨(n : G), hnM⟩ := by
    have hsub : (⟨(n : G), hnM⟩ : ↥D.M) * ⟨b, F.A_le_M (hBA hb)⟩ =
        ⟨b, F.A_le_M (hBA hb)⟩ * ⟨(n : G), hnM⟩ := Subtype.ext hnb.symm
    calc F.phiA ⟨(n : G), hnM⟩ * F.phiA ⟨b, F.A_le_M (hBA hb)⟩ =
          F.phiA (⟨(n : G), hnM⟩ * ⟨b, F.A_le_M (hBA hb)⟩) := (map_mul _ _ _).symm
      _ = F.phiA (⟨b, F.A_le_M (hBA hb)⟩ * ⟨(n : G), hnM⟩) := by rw [hsub]
      _ = F.phiA ⟨b, F.A_le_M (hBA hb)⟩ * F.phiA ⟨(n : G), hnM⟩ := map_mul _ _ _
  have hnN_M : (⟨(n : G), hnM⟩ : ↥D.M) ∈
      Subgroup.normalizer ((F.A.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hnG (x : G)).mp (Subgroup.mem_subgroupOf.mp hx))
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hnG (x : G)).mpr (Subgroup.mem_subgroupOf.mp hx))
  have hn_norm : F.phiA ⟨(n : G), hnM⟩ ∈
      Subgroup.normalizer (A10Perm.atilde : Set (Equiv.Perm (Fin 10))) := by
    have hle := Subgroup.le_normalizer_map (H := F.A.subgroupOf D.M) F.phiA
    rw [F.map_A_phiA] at hle
    exact hle (Subgroup.mem_map_of_mem F.phiA hnN_M)
  have hnconjG' : (n : G) * a * (n : G)⁻¹ = a' := by
    rw [hnconjG, ← ha'def]
  refine ⟨⟨(n : G), hnM⟩, n.2, hxcomm, hn_norm, ?_⟩
  have hsub : (⟨a', F.A_le_M ha'A⟩ : ↥D.M) =
      ⟨(n : G), hnM⟩ * ⟨a, F.A_le_M haA⟩ * ⟨(n : G), hnM⟩⁻¹ := by
    apply Subtype.ext
    exact hnconjG'.symm
  rw [hsub, map_mul, map_mul, map_inv]

private theorem support_setup (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) {a b a' : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) (haA : a ∈ F.A) (ha'A : a' ∈ F.A)
    {n : ↥D.M}
    (hφeq : F.phiA ⟨a', F.A_le_M ha'A⟩ =
      F.phiA n * F.phiA ⟨a, F.A_le_M haA⟩ * (F.phiA n)⁻¹)
    (hxcomm : F.phiA n * F.phiA ⟨b, F.A_le_M (hBA hb)⟩ =
      F.phiA ⟨b, F.A_le_M (hBA hb)⟩ * F.phiA n) :
    (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support.card = 6 ∧
      F.phiA ⟨b, F.A_le_M (hBA hb)⟩ ∈ A10Perm.atilde ∧
      F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde ∧
      (F.phiA ⟨a', F.A_le_M ha'A⟩).support =
        (F.phiA ⟨a, F.A_le_M haA⟩).support.map (Equiv.toEmbedding (F.phiA n)) ∧
      (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support.map
        (Equiv.toEmbedding (F.phiA n)) =
        (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support ∧
      F.phiA ⟨a', F.A_le_M ha'A⟩ ∈ A10Perm.atilde := by
  have hx6 : (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support.card = 6 := by
    rw [← F.deg_zpowers_eq (F.P_le_L (F.A_le (hBA hb))),
      deg_zpowers_eq_deg_of_card_three F hBA hB3 hb hb1, hB6]
  have hx_at : F.phiA ⟨b, F.A_le_M (hBA hb)⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr (hBA hb))
  have hw_at : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr haA)
  have hφsupp : (F.phiA ⟨a', F.A_le_M ha'A⟩).support =
      (F.phiA ⟨a, F.A_le_M haA⟩).support.map (Equiv.toEmbedding (F.phiA n)) := by
    rw [hφeq, Equiv.Perm.support_conj]
  have hxmap : (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support.map
      (Equiv.toEmbedding (F.phiA n)) =
      (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support := by
    rw [← Equiv.Perm.support_conj, hxcomm]
    simp
  have hφa'_at : F.phiA ⟨a', F.A_le_M ha'A⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr ha'A)
  exact ⟨hx6, hx_at, hw_at, hφsupp, hxmap, hφa'_at⟩

theorem isWeaklyClosedIn_of_disjoint (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) {a b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (haA : a ∈ F.A) (ha1 : a ≠ 1)
    (hdisj : Disjoint (F.phiA ⟨a, F.A_le_M haA⟩).support
      (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support) :
    IsWeaklyClosedIn ((Subgroup.zpowers a).subgroupOf (Subgroup.centralizer (B : Set G)))
      (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) := by
  classical
  intro g hg
  let H := Subgroup.centralizer (B : Set G)
  let a' : G := (g : G)⁻¹ * a * (g : G)
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  have ha'A : a' ∈ F.A := by
    have := conj_mem_A_of_conjugate_le F haA hAH (g := g) hg
    simpa [H, a'] using this
  obtain ⟨n, -, hxcomm, -, hφeq⟩ :=
    exists_fusion_data F hNA hBA hB3 hB6 hb haA ha'A (by rfl) hg
  obtain ⟨hx6, hx_at, hw_at, hφsupp, hxmap, hφa'_at⟩ :=
    support_setup F hBA hB3 hB6 hb hb1 haA ha'A hφeq hxcomm
  have hw1 : F.phiA ⟨a, F.A_le_M haA⟩ ≠ 1 := phiA_ne_one_of_mem_A F haA ha1
  obtain ⟨y, -, -, -, hy3, -, hyuniq, -⟩ :=
    A10Perm.exists_basis_of_card_support_eq_six hx_at hx6
  have hw3 : (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 3 := by
    rw [hyuniq (F.phiA ⟨a, F.A_le_M haA⟩) hw_at hw1 hdisj, hy3]
  have hvx : Disjoint (F.phiA ⟨a', F.A_le_M ha'A⟩).support
      (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support := by
    rw [hφsupp, ← hxmap]
    exact (Finset.disjoint_map _).2 hdisj
  have hφa'_1 : F.phiA ⟨a', F.A_le_M ha'A⟩ ≠ 1 := by
    rw [hφeq]
    intro h
    apply hw1
    have := congrArg (fun z => (F.phiA n)⁻¹ * z * F.phiA n) h
    simpa [mul_assoc] using this
  have hsupp_eq : (F.phiA ⟨a', F.A_le_M ha'A⟩).support =
      (F.phiA ⟨a, F.A_le_M haA⟩).support :=
    A10Perm.support_eq_of_disjoint hx_at hx6 hw_at hw1 hdisj hφa'_at hφa'_1 hvx
  have hmem : F.phiA ⟨a', F.A_le_M ha'A⟩ ∈
      Subgroup.zpowers (F.phiA ⟨a, F.A_le_M haA⟩) :=
    A10Perm.mem_zpowers_of_support_eq hw_at hφa'_at hw3 hsupp_eq
  have ha'Za : a' ∈ Subgroup.zpowers a :=
    mem_zpowers_of_phiA_mem_zpowers F haA ha'A hmem
  exact conjugate_zpowers_subgroupOf_eq_of_mem_zpowers F hBA haA (by simpa [a'] using ha'Za)

theorem isWeaklyClosedIn_of_support_eq (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) {a b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (haA : a ∈ F.A)
    (hsupp : (F.phiA ⟨a, F.A_le_M haA⟩).support = (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support)
    (hab : F.phiA ⟨a, F.A_le_M haA⟩ ∉ Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hb)⟩)) :
    IsWeaklyClosedIn ((Subgroup.zpowers a).subgroupOf (Subgroup.centralizer (B : Set G)))
      (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) := by
  classical
  intro g hg
  let H := Subgroup.centralizer (B : Set G)
  let a' : G := (g : G)⁻¹ * a * (g : G)
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  have ha'A : a' ∈ F.A := by
    have := conj_mem_A_of_conjugate_le F haA hAH (g := g) hg
    simpa [H, a'] using this
  obtain ⟨n, -, hxcomm, -, hφeq⟩ :=
    exists_fusion_data F hNA hBA hB3 hB6 hb haA ha'A (by rfl) hg
  obtain ⟨hx6, hx_at, hw_at, hφsupp, hxmap, hφa'_at⟩ :=
    support_setup F hBA hB3 hB6 hb hb1 haA ha'A hφeq hxcomm
  have hsupp_a' : (F.phiA ⟨a', F.A_le_M ha'A⟩).support =
      (F.phiA ⟨b, F.A_le_M (hBA hb)⟩).support := by
    rw [hφsupp, hsupp, hxmap]
  have hφa'_not : F.phiA ⟨a', F.A_le_M ha'A⟩ ∉
      Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hb)⟩) := by
    intro hmem
    apply hab
    have hw_eq : F.phiA ⟨a, F.A_le_M haA⟩ =
        (MulAut.conj (F.phiA n)⁻¹) (F.phiA ⟨a', F.A_le_M ha'A⟩) := by
      rw [hφeq]
      simp [MulAut.conj_apply]
      group
    have hconj_inv : (MulAut.conj (F.phiA n)⁻¹) (F.phiA ⟨b, F.A_le_M (hBA hb)⟩) =
        F.phiA ⟨b, F.A_le_M (hBA hb)⟩ := by
      rw [MulAut.conj_apply]
      calc (F.phiA n)⁻¹ * F.phiA ⟨b, F.A_le_M (hBA hb)⟩ * F.phiA n =
            (F.phiA n)⁻¹ * (F.phiA ⟨b, F.A_le_M (hBA hb)⟩ * F.phiA n) := by group
        _ = (F.phiA n)⁻¹ * (F.phiA n * F.phiA ⟨b, F.A_le_M (hBA hb)⟩) := by
              rw [← hxcomm]
        _ = F.phiA ⟨b, F.A_le_M (hBA hb)⟩ := by group
    have hmap : (Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hb)⟩)).map
        (MulAut.conj (F.phiA n)⁻¹).toMonoidHom =
        Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hb)⟩) := by
      rw [MonoidHom.map_zpowers]
      simpa using congrArg Subgroup.zpowers hconj_inv
    rw [hw_eq]
    exact hmap ▸ Subgroup.mem_map_of_mem (MulAut.conj (F.phiA n)⁻¹).toMonoidHom hmem
  have hmem : F.phiA ⟨a', F.A_le_M ha'A⟩ ∈
      Subgroup.zpowers (F.phiA ⟨a, F.A_le_M haA⟩) :=
    A10Perm.mem_zpowers_of_support_eq_of_not_mem hx_at hx6 hw_at hsupp hab hφa'_at
      hsupp_a' hφa'_not
  have ha'Za : a' ∈ Subgroup.zpowers a :=
    mem_zpowers_of_phiA_mem_zpowers F haA ha'A hmem
  exact conjugate_zpowers_subgroupOf_eq_of_mem_zpowers F hBA haA (by simpa [a'] using ha'Za)

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
