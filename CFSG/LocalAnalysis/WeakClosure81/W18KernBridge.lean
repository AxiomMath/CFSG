module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernGroup
public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack
public import CFSG.LocalAnalysis.WeakClosure81.W18ASCtx
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineShape
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem kbr_not_isPGroup_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : ¬ IsPGroup 2 X := by
  intro hP
  have hne : Subgroup.center X ≠ ⊥ := hP.bot_lt_center.ne'
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h1 | h1
  · exact hne h1
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center X := by rw [h1]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem not_isPGroup_of_isCalL1 {X : Type} [Group X] [Finite X] (h : IsCalL1 X) :
    ¬ IsPGroup 2 X := by
  obtain ⟨n, hn_odd, hn_gt1, hL2 | hSz | hL3⟩ := h
  ·
    have hm : StatedClassicalModel X .PSL 2 2 n := hL2.statedClassicalModel (by decide)
    haveI : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hm
    have hn2 : 2 ≤ n := by omega
    have hcard : 3 < Nat.card F := by
      rw [hF]
      calc 3 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        F (by omega) (by omega)
    let e' := eF.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    exact kbr_not_isPGroup_of_simple
      ⟨e'.symm x, e'.symm y, fun hc => hxy (by simpa using congrArg e' hc)⟩
  ·
    haveI : IsSimpleGroup X :=
      CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    exact kbr_not_isPGroup_of_simple
      (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz)
  ·
    have hm : StatedClassicalModel X .PSL 3 2 n := hL3.statedClassicalModel (by decide)
    haveI : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨eF⟩⟩ := hm
    have hcard : Nat.card X = Nat.card (StatedProj (StatedSL 3 F)) := Nat.card_congr eF.toEquiv
    have hord :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := F)
    refine kbr_not_isPGroup_of_simple (X := X) ?_
    refine exists_noncomm_of_simple_of_pow_three_dvd (X := X)
      Nat.prime_two (g := Nat.gcd 3 (Nat.card F - 1))
      ((Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _)) ?_
    rw [hcard, hord, hF]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 3) _) _

theorem kbr_isCompositionFactor_of_normal_subgroup {Y : Type} [Group Y] (B : Subgroup Y)
    [B.Normal] {L : Type} [Group L] (h : E1.IsCompositionFactor ↥B L) :
    E1.IsCompositionFactor Y L := by
  obtain ⟨N₁, M₁, hN₁, hNM, hNs, hMs, hs, ⟨e⟩⟩ := h
  haveI := hs
  have hL : IsSimpleGroup L := e.symm.isSimpleGroup
  haveI := hL
  let A : Subgroup Y := M₁.map B.subtype
  have hAsub : A.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le M₁) ?_
      (inferInstance : B.Normal).isSubnormal
    rw [show A.subgroupOf B = M₁ from
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective M₁]
    exact hMs
  let g := Subgroup.equivMapOfInjective M₁ B.subtype B.subtype_injective
  let ψ : ↥A →* L :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (N₁.subgroupOf M₁)).comp g.symm.toMonoidHom)
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨q, rfl⟩ := e.surjective l
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (N₁.subgroupOf M₁) q
    obtain ⟨a, rfl⟩ := g.symm.surjective m
    exact ⟨a, rfl⟩
  exact CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection hAsub hL ψ hψ

theorem not_hasCompFactor_sup_of_normal {H N T : Subgroup G} (hNH : N ≤ H)
    (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hTH : T ≤ H) (hT : IsPGroup 2 ↥T)
    (hH : ¬ HasCompFactor H IsCalL1) : ¬ HasCompFactor (N ⊔ T) IsCalL1 := by
  rintro ⟨L, hLgrp, hLc, hcal⟩
  letI := hLgrp
  have hNX : N ≤ N ⊔ T := le_sup_left
  have hTX : T ≤ N ⊔ T := le_sup_right
  have hXH : N ⊔ T ≤ H := sup_le hNH hTH
  let A : Subgroup ↥(N ⊔ T) := N.subgroupOf (N ⊔ T)
  have hAn : A.Normal := by
    refine ⟨fun a ha x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hNn (x : G) (hXH x.2) a ha
  haveI := hAn
  rcases isCompositionFactor_of_normal A hLc with hA | hQ
  ·
    have hLN : E1.IsCompositionFactor ↥N L :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hNX)).mp hA
    have hNnorm : (N.subgroupOf H).Normal := by
      refine ⟨fun a ha x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact hNn (x : G) x.2 a ha
    haveI := hNnorm
    have hLN' : E1.IsCompositionFactor ↥(N.subgroupOf H) L :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hNH)).mpr hLN
    exact hH ⟨L, hLgrp, kbr_isCompositionFactor_of_normal_subgroup (N.subgroupOf H) hLN', hcal⟩
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hPq : IsPGroup 2 (↥(N ⊔ T) ⧸ A) := by
      let g : ↥T →* ↥(N ⊔ T) ⧸ A :=
        (QuotientGroup.mk' A).comp (Subgroup.inclusion hTX)
      have hg : Function.Surjective g := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A q
        have hsup : (N.subgroupOf (N ⊔ T)) ⊔ (T.subgroupOf (N ⊔ T)) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hNX hTX]
          exact Subgroup.subgroupOf_self (N ⊔ T)
        have hx : x ∈ (N.subgroupOf (N ⊔ T)) ⊔ (T.subgroupOf (N ⊔ T)) := by
          rw [hsup]; exact Subgroup.mem_top x
        obtain ⟨n, hn, t, ht, hnt⟩ :=
          (Subgroup.mem_sup_of_normal_left
            (s := N.subgroupOf (N ⊔ T)) (t := T.subgroupOf (N ⊔ T))).mp hx
        refine ⟨⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩, ?_⟩
        have hgapp : g ⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩ =
            QuotientGroup.mk' A t := by
          apply congrArg (QuotientGroup.mk' A)
          exact Subtype.ext rfl
        have hn1 : QuotientGroup.mk' A n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
        calc g ⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩
            = QuotientGroup.mk' A t := hgapp
          _ = QuotientGroup.mk' A (n * t) := by rw [map_mul, hn1, one_mul]
          _ = QuotientGroup.mk' A x := by rw [hnt]
      exact hT.of_surjective g hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hPq
    have hdvd : Nat.card L ∣ 2 ^ k := hk ▸ isCompositionFactor_natCard_dvd hQ
    haveI : Finite L := isCompositionFactor_finite hQ
    exact not_isPGroup_of_isCalL1 hcal (IsPGroup.of_card_dvd_pow hdvd)

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem sup_eq_of_normal_not_le_kerMV (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H)
    {N : Subgroup G} (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNK : ¬ N ≤ kerMV V H) : N ⊔ D.T = H := by
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  by_contra hne
  have hlt : N ⊔ D.T < H := lt_of_le_of_ne (sup_le hNH hTH) hne
  have hX : ¬ HasCompFactor (N ⊔ D.T) IsCalL1 :=
    not_hasCompFactor_sup_of_normal hNH hNn hTH c.hyp.isSylowIn_T.isPGroup
      (not_concl181_iff.mp h1).2.2
  have hM : N ⊔ D.T ≤ D.M := c.le_normalizer_one h1 le_sup_right hlt hX
  refine hNK (le_kerMV_of_normal hNH hNn ?_)
  rw [c.hyp.setting.normalizer_eq]
  exact le_sup_left.trans hM

end MinCex183

section Transfer

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem MinCex183.two_quotient_img (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {Kk : Subgroup ↥(M.img H)}
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    {N : Subgroup ↥(M.img H)} (hN : N.Normal) (hNK : ¬ N ≤ Kk) :
    ∀ y : ↥(M.img H), ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
  obtain ⟨π, hπs, hπval, -⟩ := M.exists_surjective_img
  let N' : Subgroup G := (N.comap π).map H.subtype
  have hN'H : N' ≤ H := Subgroup.map_subtype_le _
  have hN'eq : N'.subgroupOf H = N.comap π := by
    show ((N.comap π).map H.subtype).comap H.subtype = N.comap π
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hN'norm : (N'.subgroupOf H).Normal := by
    rw [hN'eq]
    exact hN.comap π
  have hN'n : ∀ h ∈ H, ∀ n ∈ N', h * n * h⁻¹ ∈ N' := by
    intro h hh n hn
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨⟨h, hh⟩ * j * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hN.conj_mem (π j) (Subgroup.mem_comap.mp hj) (π ⟨h, hh⟩)
  have hN'K : ¬ N' ≤ kerMV V H := by
    intro hle
    obtain ⟨r, hrN, hrK⟩ := SetLike.not_le_iff_exists.mp hNK
    obtain ⟨j, -, hj⟩ := M.mem_img.1 r.2
    have hjr : π j = r := Subtype.ext ((hπval j).trans hj)
    have hjN' : (j : G) ∈ N' := by
      refine Subgroup.mem_map.2 ⟨j, ?_, rfl⟩
      rw [Subgroup.mem_comap, hjr]
      exact hrN
    exact hrK ((hKk j r hj.symm).mpr (hle hjN'))
  have hsup : N' ⊔ D.T = H := MinCex183.sup_eq_of_normal_not_le_kerMV c h1 hN'H hN'n hN'K
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  have hsupH : (N'.subgroupOf H) ⊔ (D.T.subgroupOf H) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hN'H hTH, hsup]
    exact Subgroup.subgroupOf_self H
  let Tsub : Subgroup (LGL 2 M.W) := M.img D.T
  let TsubH : Subgroup ↥(M.img H) := Tsub.subgroupOf (M.img H)
  have hTsub_le : Tsub ≤ M.img H := M.img_mono hTH
  have hTsubH2 : IsPGroup 2 ↥TsubH :=
    (M.isPGroup_img (S := D.T) c.hyp.isSylowIn_T.isPGroup).of_equiv
      (Subgroup.subgroupOfEquivOfLe hTsub_le).symm
  intro y
  obtain ⟨j, rfl⟩ := hπs y
  have hjmem : j ∈ (N'.subgroupOf H) ⊔ (D.T.subgroupOf H) := by
    rw [hsupH]; exact Subgroup.mem_top j
  haveI := hN'norm
  obtain ⟨n, hn, t, ht, hnt⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := N'.subgroupOf H)
      (t := D.T.subgroupOf H)).mp hjmem
  have hmem_n : π n ∈ N := by
    have h1 : n ∈ N.comap π := by rw [← hN'eq]; exact hn
    exact Subgroup.mem_comap.mp h1
  have hmem_t : π t ∈ TsubH := by
    show π t ∈ Tsub.subgroupOf (M.img H)
    rw [Subgroup.mem_subgroupOf]
    refine M.mem_img.2 ⟨t, Subgroup.mem_subgroupOf.mp ht, (hπval t).symm⟩
  obtain ⟨a, ha⟩ := hTsubH2 ⟨π t, hmem_t⟩
  refine ⟨a, (QuotientGroup.eq_one_iff ((π j) ^ 2 ^ a)).mp ?_⟩
  have hq : (QuotientGroup.mk' N (π j)) ^ 2 ^ a = 1 := by
    have hntπ : π n * π t = π j := by rw [← map_mul, hnt]
    have h1 : QuotientGroup.mk' N (π j) = QuotientGroup.mk' N (π t) := by
      rw [← hntπ, map_mul]
      have hn1 : QuotientGroup.mk' N (π n) = 1 := (QuotientGroup.eq_one_iff (π n)).mpr hmem_n
      rw [hn1, one_mul]
    have ht1 : (π t) ^ 2 ^ a = 1 := by
      have h := congrArg Subtype.val ha
      simpa using h
    rw [h1, ← map_pow, ht1, map_one]
  simpa [map_pow] using hq

theorem isSolvable_kk (M : ModDataE H (eOmegaZ H D.T)) {K : Subgroup G} (hKH : K ≤ H)
    {Kk : Subgroup ↥(M.img H)}
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j → (r ∈ Kk ↔ (j : G) ∈ K))
    (hK : Group.IsSolvable ↥K) : Group.IsSolvable ↥Kk := by
  let f : ↥K →* ↥Kk :=
    { toFun := fun k =>
        let j : ↥H := ⟨(k : G), hKH k.2⟩
        let r : ↥(M.img H) := ⟨M.ρ j, M.mem_img.2 ⟨j, j.2, rfl⟩⟩
        ⟨r, (hKk j r rfl).2 k.2⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change M.ρ (1 : ↥H) = 1
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        change M.ρ ⟨↑(a * b), hKH (a * b).2⟩ =
          M.ρ ⟨↑a, hKH a.2⟩ * M.ρ ⟨↑b, hKH b.2⟩
        rw [show (⟨↑(a * b), hKH (a * b).2⟩ : ↥H) =
            ⟨↑a, hKH a.2⟩ * ⟨↑b, hKH b.2⟩ from Subtype.ext rfl, map_mul] }
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨j, -, hjρ⟩ := M.mem_img.1 r.1.2
    have hjK : (j : G) ∈ K := (hKk j r.1 hjρ.symm).1 r.2
    refine ⟨⟨(j : G), hjK⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change M.ρ ⟨(j : G), hKH hjK⟩ = (r.1 : LGL 2 M.W)
    rw [show (⟨(j : G), hKH hjK⟩ : ↥H) = j from Subtype.ext rfl]
    exact hjρ
  haveI : Group.IsSolvable ↥K := hK
  exact Group.isSolvable_of_surjective (f := f) hf

theorem eq_bot_of_pCoreOf_eq_bot {Q : Type*} [Group Q] [Finite Q] {J : Subgroup Q}
    (h : pCoreOf 2 J = ⊥) : ∀ N : Subgroup ↥J, N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
  have hcore : CFSG.pCore 2 ↥J = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥J).map J.subtype = ⊥ := by
      rw [← Open.pCoreOf]
      exact h
    exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp hmap
  intro N hN hNp
  exact le_bot_iff.mp ((le_sSup (show N ∈ {K : Subgroup ↥J | K.Normal ∧ IsPGroup 2 K} from
    ⟨hN, hNp⟩) : N ≤ CFSG.pCore 2 ↥J).trans (le_of_eq hcore))

theorem opResidual_top_props {Y : Type*} [Group Y] [Finite Y] :
    (opResidual 2 (⊤ : Subgroup Y)).Normal ∧
      (∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ opResidual 2 (⊤ : Subgroup Y)) ∧
      ∀ N : Subgroup Y, (∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N) → opResidual 2 (⊤ : Subgroup Y) ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨fun x hx g => ?_⟩, fun y => exists_pow_mem_opResidual (p := 2) (A := ⊤) (mem_top y),
    fun N h => opResidual_le_of_pow_mem fun x _ => h x⟩
  have hn : (⟨x, mem_top x⟩ : (⊤ : Subgroup Y)) ∈
      (opResidual 2 (⊤ : Subgroup Y)).subgroupOf ⊤ := hx
  exact (opResidual_normal 2 (⊤ : Subgroup Y)).conj_mem _ hn ⟨g, mem_top g⟩

theorem MinCex183.kernSetting_of_minCex (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H)
    (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) {Kk F : Subgroup ↥(M.img H)}
    (hsoc : SimpleSocleMod Kk F) (hK : Group.IsSolvable ↥(kerMV V H))
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H)) :
    KernSetting Kk F (opResidual 2 (⊤ : Subgroup ↥(M.img H))) where
  socle := hsoc.toPerf
  solvable := isSolvable_kk M (kerMV_le_self V H) hKk hK
  o2_eq_bot := eq_bot_of_pCoreOf_eq_bot (x.pCoreOf_img_eq_bot M)
  normal := opResidual_top_props.1
  two_quotient := opResidual_top_props.2.1
  le_of_not_le := fun _ hN hNK => opResidual_top_props.2.2 _ (c.two_quotient_img h1 M hKk hN hNK)

theorem four_le_card_img (M : ModDataE H (eOmegaZ H D.T)) {S : Subgroup G} (hSH : S ≤ H)
    (hab : IsElemAbelian 2 S)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex S) :
    IsPGroup 2 ↥((M.img S).subgroupOf (M.img H)) ∧
      4 ≤ Nat.card ↥((M.img S).subgroupOf (M.img H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH' : M.img S ≤ M.img H := M.img_mono hSH
  let e := Subgroup.subgroupOfEquivOfLe hSH'
  have hcard : Nat.card ↥((M.img S).subgroupOf (M.img H)) = Nat.card ↥(M.img S) :=
    Nat.card_congr e.toEquiv
  have h2 : IsPGroup 2 ↥(M.img S) :=
    M.isPGroup_img (CFSG.Open.IsElemAbelian.isPGroup hab)
  refine ⟨h2.of_equiv e.symm, ?_⟩
  have hge : 3 ≤ Nat.card ↥(M.img S) := by
    rw [M.card_img hSH]
    exact hA
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  rw [hcard, hk]
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := by omega
    have hle : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

theorem Ctx188.index_le_two_of_gam183 (x : Ctx188 D V₀ V H i j)
    (M : ModDataE H (eOmegaZ H D.T)) {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g) :
    ∀ N : Subgroup ↥(M.img H), N.Normal → Odd (Nat.card ↥N) →
      (((M.img (vInH V H g)).subgroupOf (M.img H)) ⊓
          Subgroup.centralizer (N : Set ↥(M.img H))).relIndex
        ((M.img (vInH V H g)).subgroupOf (M.img H)) ≤ 2 := by
  intro N hN hodd
  let A : Subgroup (LGL 2 M.W) := M.img (vInH V H g)
  have hAG : A ≤ M.img H := M.img_mono inf_le_right
  let X : Subgroup (LGL 2 M.W) := N.map (M.img H).subtype
  have hXG : X ≤ M.img H := Subgroup.map_subtype_le N
  have hoddX : Odd (Nat.card ↥X) := by
    have hc := Nat.card_congr (Subgroup.equivMapOfInjective N (M.img H).subtype
      (Subgroup.subtype_injective _)).toEquiv
    rwa [← hc]
  have hAX : A ≤ Subgroup.normalizer (X : Set (LGL 2 M.W)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_map.2 ⟨(⟨a, hAG ha⟩ : ↥(M.img H)) * n *
        (⟨a, hAG ha⟩ : ↥(M.img H))⁻¹,
        hN.conj_mem n hn (⟨a, hAG ha⟩ : ↥(M.img H)), rfl⟩
    · intro hy
      obtain ⟨n, hn, hn_eq⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨(⟨a, hAG ha⟩ : ↥(M.img H))⁻¹ * n *
        (⟨a, hAG ha⟩ : ↥(M.img H)),
        hN.conj_mem n hn (⟨a, hAG ha⟩ : ↥(M.img H))⁻¹, ?_⟩
      show (((⟨a, hAG ha⟩ : ↥(M.img H))⁻¹ * n *
        (⟨a, hAG ha⟩ : ↥(M.img H))) : LGL 2 M.W) = y
      change a⁻¹ * ((M.img H).subtype n) * a = y
      rw [hn_eq]
      group
  have hidx := index_centralizer_le_two (x.assumption131U M) (A := A) ⟨g, hg, rfl⟩ hXG hoddX hAX
  have hcent : Subgroup.centralizer (N : Set ↥(M.img H)) =
      (Subgroup.centralizer (X : Set (LGL 2 M.W))).comap (M.img H).subtype := by
    ext u
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
      simpa using congrArg (M.img H).subtype (h n hn)
    · intro h n hn
      apply (M.img H).subtype_injective
      simpa using h ((M.img H).subtype n) (Subgroup.mem_map.2 ⟨n, hn, rfl⟩)
  have hinf : (A.subgroupOf (M.img H)) ⊓ Subgroup.centralizer (N : Set ↥(M.img H)) =
      (A ⊓ Subgroup.centralizer (X : Set (LGL 2 M.W))).subgroupOf (M.img H) := by
    rw [hcent]
    change A.comap (M.img H).subtype ⊓
        (Subgroup.centralizer (X : Set (LGL 2 M.W))).comap (M.img H).subtype =
      (A ⊓ Subgroup.centralizer (X : Set (LGL 2 M.W))).comap (M.img H).subtype
    rw [← Subgroup.comap_inf]
  change (((A.subgroupOf (M.img H)) ⊓ Subgroup.centralizer (N : Set ↥(M.img H))).relIndex
      (A.subgroupOf (M.img H)) ≤ 2)
  rw [hinf, Subgroup.relIndex_subgroupOf hAG]
  exact hidx

@[expose] def OddMultiplierSocle185 : Prop :=
  ∀ (S : Type) [Group S], Socle185Shape S →
    ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal], Z ≤ Subgroup.center X →
      Odd (Nat.card ↥Z) → ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ →
        Nonempty ((X ⧸ Z) ≃* S) → Z = ⊥

theorem kk_eq_bot_of_multiplier (hMult : OddMultiplierSocle185) {Y : Type} [Group Y] [Finite Y]
    {Kk F : Subgroup Y} (hF : ⁅F, F⁆ = F) (hKF : Kk ≤ F)
    (hKC : Kk ≤ Subgroup.centralizer (F : Set Y)) (hodd : Odd (Nat.card ↥Kk)) {S : Type}
    [Group S] (hS : Socle185Shape S) (φ : ↥F →* S) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥F, φ k = 1 ↔ (k : Y) ∈ Kk) : Kk = ⊥ := by
  let Z : Subgroup ↥F := Kk.subgroupOf F
  have hZker : φ.ker = Z := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφk k
  have hZnorm : Z.Normal := hZker ▸ φ.normal_ker
  haveI := hZnorm
  have hZcenter : Z ≤ Subgroup.center ↥F := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    change (w : Y) * (z : Y) = (z : Y) * (w : Y)
    exact Subgroup.mem_centralizer_iff.mp
      (hKC (Subgroup.mem_subgroupOf.mp hz)) (w : Y) w.2
  have hZodd : Odd (Nat.card ↥Z) := by
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKF).toEquiv
    rwa [hc]
  have hperf : ⁅(⊤ : Subgroup ↥F), (⊤ : Subgroup ↥F)⁆ = ⊤ := by
    apply Subgroup.map_injective F.subtype_injective
    have hmapF : Subgroup.map F.subtype (⊤ : Subgroup ↥F) = F :=
      (Subgroup.map_top F.subtype).trans (Subgroup.range_subtype F)
    rw [Subgroup.map_commutator, hmapF, hF]
  have hiso : Nonempty ((↥F ⧸ Z) ≃* S) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩
  have hZbot : Z = ⊥ := hMult S hS ↥F Z hZcenter hZodd hperf hiso
  refine le_bot_iff.mp fun k hk => ?_
  have hkZ : (⟨k, hKF hk⟩ : ↥F) ∈ Z := Subgroup.mem_subgroupOf.mpr hk
  rw [hZbot, Subgroup.mem_bot] at hkZ
  exact congrArg Subtype.val hkZ

end Transfer

section Final

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem MinCex183.kerMV_le_centralizer_of_four_181 (h162 : W3Thm162Gt2 G) (h172 : W3Thm172Weak G)
    (h5_11 : Asch5_11AS) (h5_12 : Asch5_12) (h5_13 : Asch5_13AS)
    (hMult : OddMultiplierSocle185) (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) {g : G}
    (hgK : ¬ vInH V H g ≤ kerMV V H) (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g)) :
    kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
  have x : Ctx188 D V₀ V H i 2 := c.ctx188_two_AS h162 h5_11 h5_13 h1
  obtain ⟨hsolv, hkerEq, hshape⟩ := c.exists_shape185_AS h172 h5_12 h5_11 h5_13 h1
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ
    (Hyp183.normalizer_eOmegaZ H D.T)
  have hker : H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ relPPrimeCore 3 H :=
    hkerEq ▸ c.hyp.inf_centralizer_eOmegaZ_le_kerMV
  obtain ⟨Kk, F, S, _, φ, hsoc, hφs, hφk, hS, hKk⟩ := M.exists_simpleSocleMod hker hshape
  have hKk' : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H) := fun j r hr => by
    rw [hkerEq]
    exact hKk j r hr
  have hset := c.kernSetting_of_minCex h1 x M hsoc (hkerEq ▸ hsolv) hKk'
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
    hgK ((le_inf (inf_le_right : vInH V H g ≤ H) hle).trans c.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
  obtain ⟨hA2, hA4⟩ := four_le_card_img M inf_le_right hab hA
  obtain ⟨hperf, hPF, hKP, hKC, hodd⟩ :=
    hset.kern_eq_centralizer hA2 hA4 (x.index_le_two_of_gam183 M hgam)
  have hKbot : Kk = ⊥ := by
    refine kk_eq_bot_of_multiplier hMult ?_ hsoc.le ?_ hodd hS φ hφs hφk
    · rw [hPF] at hperf
      exact hperf
    · rw [← hPF]
      exact hKC.le
  intro k hk
  have hkH : k ∈ H := kerMV_le_self V H hk
  have hr : (M.ρ ⟨k, hkH⟩ : LGL 2 M.W) ∈ M.img H := M.mem_img.2 ⟨⟨k, hkH⟩, hkH, rfl⟩
  have hrK : (⟨M.ρ ⟨k, hkH⟩, hr⟩ : ↥(M.img H)) ∈ Kk :=
    (hKk' ⟨k, hkH⟩ ⟨M.ρ ⟨k, hkH⟩, hr⟩ rfl).2 hk
  rw [hKbot, Subgroup.mem_bot] at hrK
  exact (M.ρ_eq_one_iff ⟨k, hkH⟩).1 (congrArg Subtype.val hrK)

end Final

end CFSG.LocalAnalysis.WeakClosure81

end
