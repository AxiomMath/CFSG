module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs3
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D} (F : A10Frame c)

private theorem map_L_phiA_perfect :
    ⁅(c.L.subgroupOf D.M).map F.phiA, (c.L.subgroupOf D.M).map F.phiA⁆ =
      (c.L.subgroupOf D.M).map F.phiA := by
  classical
  let N : Subgroup ↥D.M := c.L.subgroupOf D.M
  change ⁅N.map F.phiA, N.map F.phiA⁆ = N.map F.phiA
  have hNcomm : ⁅N, N⁆ = N := by
    apply Subgroup.map_injective (f := (D.M).subtype) (D.M).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le c.hyp81.1,
      c.hyp81.2.2.1]
  rw [← Subgroup.map_commutator, hNcomm]

private theorem map_L_phiA_le_alternatingGroup :
    (c.L.subgroupOf D.M).map F.phiA ≤ alternatingGroup (Fin 10) := by
  classical
  rw [← map_L_phiA_perfect F, Subgroup.commutator_le]
  intro x _ y _
  rw [Equiv.Perm.mem_alternatingGroup, commutatorElement_def, map_mul, map_mul, map_mul,
    map_inv, map_inv, mul_comm (Equiv.Perm.sign x) (Equiv.Perm.sign y)]
  group

private theorem map_L_phiA_normal :
    (((c.L.subgroupOf D.M).map F.phiA).subgroupOf (alternatingGroup (Fin 10))).Normal := by
  classical
  let N : Subgroup ↥D.M := c.L.subgroupOf D.M
  let H : Subgroup (Equiv.Perm (Fin 10)) := N.map F.phiA
  change (H.subgroupOf (alternatingGroup (Fin 10))).Normal
  have hNnormal : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp81.1]
    exact c.le_normalizer_L
  have hDleA : H ≤ alternatingGroup (Fin 10) := map_L_phiA_le_alternatingGroup F
  have hconj : ∀ b ∈ alternatingGroup (Fin 10), ∀ z ∈ H, b * z * b⁻¹ ∈ H := by
    intro b hb z hz
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (F.alternatingGroup_le_range_phiA hb)
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← hm]
    exact Subgroup.mem_map.mpr
      ⟨m * n * m⁻¹, hNnormal.conj_mem n hn m, by simp [map_mul, map_inv]⟩
  have hAnormD : alternatingGroup (Fin 10) ≤
      Subgroup.normalizer (H : Set (Equiv.Perm (Fin 10))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => hconj a ha y hy, fun hy => by
      have := hconj a⁻¹ (Subgroup.inv_mem _ ha) (a * y * a⁻¹) hy
      simpa [mul_assoc] using this⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDleA]
  exact hAnormD

theorem map_L_phiA : (c.L.subgroupOf D.M).map F.phiA = alternatingGroup (Fin 10) := by
  classical
  let N : Subgroup ↥D.M := c.L.subgroupOf D.M
  let H : Subgroup (Equiv.Perm (Fin 10)) := N.map F.phiA
  change H = alternatingGroup (Fin 10)
  have hDne : H ≠ ⊥ := by
    have hle : A10Perm.atilde ≤ H := by
      rw [← F.map_A_phiA]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono D.M (F.A_le.trans F.P_le_L))
    intro hbot
    have hat : A10Perm.atilde = ⊥ := le_bot_iff.mp (hbot ▸ hle)
    have hcard := congrArg (fun K : Subgroup (Equiv.Perm (Fin 10)) => Nat.card K) hat
    rw [A10Perm.card_atilde] at hcard
    simp at hcard
  have hDleA : H ≤ alternatingGroup (Fin 10) := map_L_phiA_le_alternatingGroup F
  have hDnormal : (H.subgroupOf (alternatingGroup (Fin 10))).Normal := map_L_phiA_normal F
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  haveI : (H.subgroupOf (alternatingGroup (Fin 10))).Normal := hDnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf (alternatingGroup (Fin 10))) with
    h | h
  · exfalso
    apply hDne
    have hmap := congrArg (Subgroup.map (alternatingGroup (Fin 10)).subtype) h
    rwa [Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hDleA] at hmap
  · rw [← Subgroup.map_subgroupOf_eq_of_le hDleA, h, Subgroup.map_top, Subgroup.range_subtype]

theorem exists_map_le_kleinV {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    ∃ k : Fin 3, (S.subgroupOf D.M).map F.phiA ≤ A10Perm.kleinV k := by
  classical
  have hSx2 : IsPGroup 2 (S.subgroupOf D.M) := by
    rw [← Subgroup.comap_subtype]
    exact hS.comap_subtype (K := D.M)
  have hW2 : IsPGroup 2 ((S.subgroupOf D.M).map F.phiA) := hSx2.map F.phiA
  have hcop : Nat.Coprime (Nat.card ((S.subgroupOf D.M).map F.phiA)) 3 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hW2
        Nat.prime_three (by norm_num))).symm
  refine A10Perm.exists_le_kleinV ?_ hcop
  have hAnorm : F.A.subgroupOf D.M ≤
      Subgroup.normalizer ((S.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hAS (Subgroup.mem_subgroupOf.mp ha)) (s : G))
  have hmap := CoprimeImage.map_le_normalizer_map F.phiA hAnorm
  rwa [F.map_A_phiA] at hmap

theorem pCoreOf_le_of_maxInv {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G))
    (hmax : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → S ≤ S' → S' = S) :
    CFSG.Open.pCoreOf 2 D.M ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) :=
    hSM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hA2 : F.A ≤ Subgroup.normalizer (Q : Set G) :=
    F.A_le_M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hsup2 : IsPGroup 2 ↥(Q ⊔ S) := IsPGroup.to_sup_of_normal_left' hQ2 hS hSQ
  have hsupM : Q ⊔ S ≤ D.M := sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M) hSM
  have hAsup : F.A ≤ Subgroup.normalizer ((Q ⊔ S : Subgroup G) : Set G) :=
    (le_inf hA2 hAS).trans (Subgroup.inf_normalizer_le_normalizer_sup Q S)
  have hEq : Q ⊔ S = S := hmax (Q ⊔ S) hsupM hsup2 hAsup le_sup_right
  calc Q ≤ Q ⊔ S := le_sup_left
    _ = S := hEq

noncomputable def phiJoin {S : Subgroup G} (hSM : S ≤ D.M) :
    ↥(c.L ⊔ S) →* Equiv.Perm (Fin 10) :=
  F.phiA.comp (Subgroup.inclusion (sup_le c.hyp81.1 hSM))

private theorem kleinV_le_alternatingGroup (k : Fin 3) :
    A10Perm.kleinV k ≤ alternatingGroup (Fin 10) := by
  rw [A10Perm.kleinV, Subgroup.closure_le]
  rintro v (rfl | rfl)
  · change Equiv.Perm.sign
      (Equiv.swap (A10Perm.blockPt k 0) (A10Perm.blockPt k 1) *
        Equiv.swap (A10Perm.blockPt k 2) 9) = 1
    rw [Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by
        intro h
        exact absurd (A10Perm.blockPt_injective k h) (by decide)),
      Equiv.Perm.sign_swap (A10Perm.blockPt_ne_nine k 2)]
    norm_num
  · change Equiv.Perm.sign
      (Equiv.swap (A10Perm.blockPt k 0) (A10Perm.blockPt k 2) *
        Equiv.swap (A10Perm.blockPt k 1) 9) = 1
    rw [Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by
        intro h
        exact absurd (A10Perm.blockPt_injective k h) (by decide)),
      Equiv.Perm.sign_swap (A10Perm.blockPt_ne_nine k 1)]
    norm_num

theorem range_phiJoin {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    (F.phiJoin hSM).range = alternatingGroup (Fin 10) := by
  obtain ⟨k, hk⟩ := exists_map_le_kleinV F hSM hS hAS
  have hrange : (F.phiJoin hSM).range = ((c.L ⊔ S).subgroupOf D.M).map F.phiA := by
    rw [phiJoin, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [hrange, Subgroup.subgroupOf_sup c.hyp81.1 hSM, Subgroup.map_sup, map_L_phiA]
  exact sup_eq_left.mpr (hk.trans (kleinV_le_alternatingGroup k))

private noncomputable def phiJoinAlt {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    ↥(c.L ⊔ S) →* alternatingGroup (Fin 10) :=
  (F.phiJoin hSM).codRestrict (alternatingGroup (Fin 10)) fun x => by
    rw [← range_phiJoin F hSM hS hAS]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩

private theorem ker_phiJoinAlt {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    (F.phiJoinAlt hSM hS hAS).ker = (F.phiJoin hSM).ker := by
  ext x
  exact Subtype.ext_iff

private theorem surjective_phiJoinAlt {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    Function.Surjective (F.phiJoinAlt hSM hS hAS) := by
  intro y
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (by
    rw [range_phiJoin F hSM hS hAS]
    exact y.2)
  exact ⟨x, Subtype.ext hx⟩

theorem normal_L_subgroupOf_join {S : Subgroup G} (hSM : S ≤ D.M) :
    (c.L.subgroupOf (c.L ⊔ S)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact (sup_le c.hyp81.1 hSM).trans c.le_normalizer_L

theorem not_L_le_ker_phiJoin {S : Subgroup G} (hSM : S ≤ D.M) :
    ¬ c.L.subgroupOf (c.L ⊔ S) ≤ (F.phiJoin hSM).ker := by
  intro hLK
  have hmap : (F.A.subgroupOf D.M).map F.phiA = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro a ha
    have haA : (a : G) ∈ F.A := Subgroup.mem_subgroupOf.mp ha
    have haL : (a : G) ∈ c.L := F.P_le_L (F.A_le haA)
    let x : ↥(c.L ⊔ S) := ⟨(a : G), (show c.L ≤ c.L ⊔ S from le_sup_left) haL⟩
    have hxL : x ∈ c.L.subgroupOf (c.L ⊔ S) := Subgroup.mem_subgroupOf.mpr haL
    have hx := hLK hxL
    rw [MonoidHom.mem_ker] at hx
    have hincl : Subgroup.inclusion (sup_le c.hyp81.1 hSM) x = a := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
    exact hincl ▸ hx
  rw [F.map_A_phiA] at hmap
  have hne : A10Perm.atilde ≠ ⊥ := by
    intro hbot
    have hcard := congrArg (fun H : Subgroup (Equiv.Perm (Fin 10)) => Nat.card H) hbot
    rw [A10Perm.card_atilde] at hcard
    simp at hcard
  exact hne hmap

private theorem eq_bot_of_normal_isPGroup_alt10 {N : Subgroup (alternatingGroup (Fin 10))}
    [N.Normal] (hN : IsPGroup 2 ↥N) : N = ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have htop2 : IsPGroup 2 ↥(⊤ : Subgroup (alternatingGroup (Fin 10))) := h ▸ hN
    have hA2 : IsPGroup 2 ↥(alternatingGroup (Fin 10)) :=
      htop2.of_equiv Subgroup.topEquiv
    have h3dvd : 3 ∣ Nat.card (alternatingGroup (Fin 10)) := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    exact (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hA2
      Nat.prime_three (by norm_num)) h3dvd

private theorem quotient_join_isPGroup {S : Subgroup G} (hSM : S ≤ D.M)
    (hS : IsPGroup 2 S) [hLxN : (c.L.subgroupOf (c.L ⊔ S)).Normal] :
    IsPGroup 2 (⊤ : Subgroup (↥(c.L ⊔ S) ⧸ c.L.subgroupOf (c.L ⊔ S))) := by
  classical
  let X := ↥(c.L ⊔ S)
  let Lx : Subgroup X := c.L.subgroupOf (c.L ⊔ S)
  haveI : Lx.Normal := hLxN
  let Sx : Subgroup X := S.subgroupOf (c.L ⊔ S)
  have hSx2 : IsPGroup 2 ↥Sx := by
    rw [show Sx = Subgroup.comap (c.L ⊔ S).subtype S from
      (Subgroup.comap_subtype S (c.L ⊔ S)).symm]
    exact hS.comap_subtype (K := c.L ⊔ S)
  let q : X →* X ⧸ Lx := QuotientGroup.mk' Lx
  have hsup : Lx ⊔ Sx = ⊤ := by
    change (c.L.subgroupOf (c.L ⊔ S)) ⊔ (S.subgroupOf (c.L ⊔ S)) = ⊤
    rw [← Subgroup.subgroupOf_sup (B := c.L ⊔ S) le_sup_left le_sup_right,
      Subgroup.subgroupOf_self]
  have hLxbot : Lx.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hqtop : Sx.map q = ⊤ := by
    calc Sx.map q = ⊥ ⊔ Sx.map q := (bot_sup_eq _).symm
      _ = Lx.map q ⊔ Sx.map q := by rw [hLxbot]
      _ = (Lx ⊔ Sx).map q := (Subgroup.map_sup Lx Sx q).symm
      _ = (⊤ : Subgroup X).map q := by rw [hsup]
      _ = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Lx)]
  change IsPGroup 2 (⊤ : Subgroup (X ⧸ Lx))
  rw [← hqtop]
  exact hSx2.map q

private theorem ker_phiJoin_isPGroup {S : Subgroup G} (hSM : S ≤ D.M)
    (hS : IsPGroup 2 S) :
    IsPGroup 2 ↥(F.phiJoin hSM).ker := by
  classical
  let X := ↥(c.L ⊔ S)
  let Lx : Subgroup X := c.L.subgroupOf (c.L ⊔ S)
  haveI hLxN : Lx.Normal := normal_L_subgroupOf_join hSM
  let K : Subgroup X := (F.phiJoin hSM).ker
  change IsPGroup 2 ↥K
  have htop2 : IsPGroup 2 (⊤ : Subgroup (X ⧸ Lx)) :=
    quotient_join_isPGroup hSM hS (hLxN := hLxN)
  let q : X →* X ⧸ Lx := QuotientGroup.mk' Lx
  let ψ : K →* X ⧸ Lx := q.comp K.subtype
  let O : Subgroup X := ((CFSG.Open.pCore 2 ↥c.L).map c.L.subtype).subgroupOf (c.L ⊔ S)
  have hO2 : IsPGroup 2 ↥O := by
    change IsPGroup 2 ↥(((CFSG.Open.pCore 2 ↥c.L).map c.L.subtype).subgroupOf (c.L ⊔ S))
    rw [← Subgroup.comap_subtype]
    exact ((CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype).comap_subtype
      (K := c.L ⊔ S)
  have hO2K : IsPGroup 2 ↥(O.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact hO2.comap_subtype (K := K)
  have hψker : IsPGroup 2 ↥ψ.ker := by
    refine hO2K.to_le ?_
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hkLx : ((k : K) : X) ∈ Lx :=
      (QuotientGroup.eq_one_iff ((k : K) : X)).mp hk
    have hkL : (((k : K) : X) : G) ∈ c.L := Subgroup.mem_subgroupOf.mp hkLx
    have hkK : ((k : K) : X) ∈ K := k.2
    have hphi : F.phiA ⟨(((k : K) : X) : G), c.hyp81.1 hkL⟩ = 1 := by
      have h1 := MonoidHom.mem_ker.mp hkK
      change F.phiA (Subgroup.inclusion (sup_le c.hyp81.1 hSM) ((k : K) : X)) = 1 at h1
      have hincl : Subgroup.inclusion (sup_le c.hyp81.1 hSM) ((k : K) : X) =
          ⟨(((k : K) : X) : G), c.hyp81.1 hkL⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_inclusion]
      rwa [hincl] at h1
    exact Subgroup.mem_subgroupOf.mpr ((F.phiA_eq_one_iff hkL).mp hphi)
  have hψrange : IsPGroup 2 ↥ψ.range := htop2.to_le le_top
  exact CFSG.Quasithin.H13.S126P31.isPGroup_of_ker_range ψ hψker hψrange

private theorem pCoreOf_le_ker_phiJoin {S : Subgroup G} (hSM : S ≤ D.M)
    (hS : IsPGroup 2 S) (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(c.L ⊔ S)) ≤ (F.phiJoin hSM).ker := by
  classical
  let X := ↥(c.L ⊔ S)
  let K : Subgroup X := (F.phiJoin hSM).ker
  change CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ K
  let P : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)
  have hPnormal : P.Normal :=
    CFSG.AGLEmbeddingD2.GN.normal_pCoreOf_top (X := X)
  let N : Subgroup (alternatingGroup (Fin 10)) := P.map (F.phiJoinAlt hSM hS hAS)
  have hN2 : IsPGroup 2 ↥N := hP2.map _
  have hNnormal : N.Normal :=
    hPnormal.map _ (surjective_phiJoinAlt F hSM hS hAS)
  haveI : N.Normal := hNnormal
  have hNbot : N = ⊥ := eq_bot_of_normal_isPGroup_alt10 hN2
  have hPker : P ≤ (F.phiJoinAlt hSM hS hAS).ker :=
    (Subgroup.map_eq_bot_iff _).mp hNbot
  change P ≤ K
  rwa [ker_phiJoinAlt F hSM hS hAS] at hPker

theorem ker_phiJoin {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    (F.phiJoin hSM).ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(c.L ⊔ S)) := by
  classical
  let X := ↥(c.L ⊔ S)
  let K : Subgroup X := (F.phiJoin hSM).ker
  change K = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  have hK2 : IsPGroup 2 ↥K := ker_phiJoin_isPGroup F hSM hS
  have hKle : K ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 le_top
      (Subgroup.Normal.subgroupOf (MonoidHom.normal_ker (F.phiJoin hSM)) ⊤) hK2
  have hPle : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ K :=
    pCoreOf_le_ker_phiJoin F hSM hS hAS
  exact le_antisymm hKle hPle

private theorem subgroupOf_pCoreOf_le_ker_phiJoin {S : Subgroup G} (hSM : S ≤ D.M)
    (hS : IsPGroup 2 S) (hAS : F.A ≤ Subgroup.normalizer (S : Set G))
    (hmax : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → S ≤ S' → S' = S) :
    (CFSG.Open.pCoreOf 2 D.M).subgroupOf (c.L ⊔ S) ≤ (F.phiJoin hSM).ker := by
  classical
  let X := ↥(c.L ⊔ S)
  let K : Subgroup X := (F.phiJoin hSM).ker
  change (CFSG.Open.pCoreOf 2 D.M).subgroupOf (c.L ⊔ S) ≤ K
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hQleS : Q ≤ S := pCoreOf_le_of_maxInv F hSM hS hAS hmax
  have hQleX : Q ≤ c.L ⊔ S := hQleS.trans le_sup_right
  have hQXnormal : (Q.subgroupOf (c.L ⊔ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQleX]
    exact (sup_le c.hyp81.1 hSM).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hQX2 : IsPGroup 2 ↥(Q.subgroupOf (c.L ⊔ S)) := hQ2.comap_subtype (K := c.L ⊔ S)
  let N : Subgroup (alternatingGroup (Fin 10)) :=
    (Q.subgroupOf (c.L ⊔ S)).map (F.phiJoinAlt hSM hS hAS)
  have hN2 : IsPGroup 2 ↥N := hQX2.map _
  have hNnormal : N.Normal :=
    hQXnormal.map _ (surjective_phiJoinAlt F hSM hS hAS)
  haveI : N.Normal := hNnormal
  have hNbot : N = ⊥ := eq_bot_of_normal_isPGroup_alt10 hN2
  have hQker : Q.subgroupOf (c.L ⊔ S) ≤ (F.phiJoinAlt hSM hS hAS).ker :=
    (Subgroup.map_eq_bot_iff _).mp hNbot
  rwa [ker_phiJoinAlt F hSM hS hAS] at hQker

theorem charTwo_join {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G))
    (hmax : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → S ≤ S' → S' = S) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥(c.L ⊔ S)) := by
  classical
  let X := ↥(c.L ⊔ S)
  let K : Subgroup X := (F.phiJoin hSM).ker
  have hK : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) = K :=
    (ker_phiJoin F hSM hS hAS).symm
  rw [CFSG.QuasithinUnique.CharTwo]
  rw [hK]
  have hQXleK := subgroupOf_pCoreOf_le_ker_phiJoin F hSM hS hAS hmax
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  intro x hx
  have hxM : (x : G) ∈ D.M := (sup_le c.hyp81.1 hSM) x.2
  have hxcentQ : (x : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqX : q ∈ c.L ⊔ S :=
      (pCoreOf_le_of_maxInv F hSM hS hAS hmax).trans le_sup_right hq
    have hqK : (⟨q, hqX⟩ : X) ∈ K :=
      hQXleK (Subgroup.mem_subgroupOf.mpr hq)
    have hcomm := Subgroup.mem_centralizer_iff.mp hx.2 ⟨q, hqX⟩ hqK
    simpa [mul_comm] using congrArg (fun z : X => (z : G)) hcomm
  have hxQ : (x : G) ∈ Q :=
    D.standing.charTwo D.M D.maxLocal.1 ⟨hxM, hxcentQ⟩
  exact hQXleK (Subgroup.mem_subgroupOf.mpr hxQ)

theorem pCoreOf_join_le {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G))
    (hmax : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → S ≤ S' → S' = S) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(c.L ⊔ S)) ≤ S.subgroupOf (c.L ⊔ S) := by
  classical
  let X := ↥(c.L ⊔ S)
  let P : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  change P ≤ S.subgroupOf (c.L ⊔ S)
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)
  have hPnormal : P.Normal := CFSG.AGLEmbeddingD2.GN.normal_pCoreOf_top (X := X)
  let R : Subgroup G := P.map (c.L ⊔ S).subtype
  have hR2 : IsPGroup 2 ↥R := hP2.map _
  have hXR : c.L ⊔ S ≤ Subgroup.normalizer (R : Set G) := by
    have h := Subgroup.le_normalizer_map (f := (c.L ⊔ S).subtype) (H := P)
    rw [Subgroup.normalizer_eq_top_iff.mpr hPnormal, Subgroup.map_top,
      Subgroup.range_subtype] at h
    exact h
  have hARM : R ≤ D.M := (Subgroup.map_subtype_le P).trans (sup_le c.hyp81.1 hSM)
  have hSleNR : S ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hXR
  have hsup2 : IsPGroup 2 ↥(R ⊔ S) := IsPGroup.to_sup_of_normal_left' hR2 hS hSleNR
  have hsupM : R ⊔ S ≤ D.M := sup_le hARM hSM
  have hAnormR : F.A ≤ Subgroup.normalizer (R : Set G) :=
    ((F.A_le.trans F.P_le_L).trans le_sup_left).trans hXR
  have hAsup : F.A ≤ Subgroup.normalizer ((R ⊔ S : Subgroup G) : Set G) :=
    (le_inf hAnormR hAS).trans (Subgroup.inf_normalizer_le_normalizer_sup R S)
  have hEq : R ⊔ S = S := hmax (R ⊔ S) hsupM hsup2 hAsup le_sup_right
  have hRS : R ≤ S := by
    calc R ≤ R ⊔ S := le_sup_left
      _ = S := hEq
  intro p hp
  exact Subgroup.mem_subgroupOf.mpr (hRS (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩))

theorem exists_fixed_phiJoin {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    ∃ i : Fin 10, ∀ t ∈ S.subgroupOf (c.L ⊔ S), F.phiJoin hSM t i = i := by
  classical
  obtain ⟨k, hk⟩ := exists_map_le_kleinV F hSM hS hAS
  have hlt : (A10Perm.tBlock k).card < (Finset.univ : Finset (Fin 10)).card := by
    rw [A10Perm.card_tBlock, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨i, ?_⟩
  intro t ht
  have htS : ((t : ↥(c.L ⊔ S)) : G) ∈ S := Subgroup.mem_subgroupOf.mp ht
  have hincl : Subgroup.inclusion (sup_le c.hyp81.1 hSM) t ∈ S.subgroupOf D.M :=
    Subgroup.mem_subgroupOf.mpr htS
  have hmem : F.phiA (Subgroup.inclusion (sup_le c.hyp81.1 hSM) t) ∈
      (S.subgroupOf D.M).map F.phiA :=
    Subgroup.mem_map.mpr ⟨_, hincl, rfl⟩
  have hv := hk hmem
  rw [A10Perm.mem_kleinV_iff] at hv
  change F.phiA (Subgroup.inclusion (sup_le c.hyp81.1 hSM) t) i = i
  rcases hv with h1 | ⟨-, hsupp⟩
  · rw [h1]
    rfl
  · rw [← hsupp] at hi
    by_contra hne
    exact hi (Equiv.Perm.mem_support.mpr hne)

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
