module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.StandardType.UnitaryTwoLocalRankLower
public import CFSG.GroupTheory.PerfectCentralizer
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Quasithin.Background.B1Restrict

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

private theorem lup8u3_CB_eq_zpowers (hS : GGQTwoSetting p B Bs x L D J) :
    B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have hThmI : GGThmIHyp p B x L := hS.1.1.1
  have hp : p.Prime := hThmI.2.2.2.2.2.1.1
  have hSStar : LargeEvenSStar p B x L := hThmI.2.2.2.2.2.2.1
  have hBmax : LargeEvenIsBmax p B := hSStar.1
  have hxmem : x ∈ B := hSStar.2.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSStar.2.2.2.1.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) →
      IsPGroup p S → IsCyclic S := hSStar.2.2.2.2
  have hEA : IsElemAbelian p B := hBmax.1
  have hxp : x ^ p = 1 := hEA.2 x hxmem
  have : Fact (Nat.Prime p) := ⟨hp⟩
  set CB : Subgroup G := B ⊓ Subgroup.centralizer (L : Set G) with hCBdef
  have hCBp : IsPGroup p CB := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro y
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hEA.2 y.1 y.2.1)⟩
  have hCBcyc : IsCyclic CB := hcyc CB inf_le_right hCBp
  have hCBle : Nat.card CB ≤ p := by
    obtain ⟨c, hc⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hCBcyc
    have hord : Nat.card CB = orderOf c := by
      rw [← Nat.card_zpowers, hc, Subgroup.card_top]
    have hcp : c ^ p = 1 := Subtype.ext (by simpa using hEA.2 c.1 c.2.1)
    have hdvd : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcp
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · rw [hord, h]; exact hp.one_le
    · rw [hord, h]
  have hxCB : x ∈ CB := ⟨hxmem, Subgroup.mem_centralizer_iff.mpr fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)⟩
  have hzxle : Subgroup.zpowers x ≤ CB := Subgroup.zpowers_le.mpr hxCB
  have hzxcard : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxp hxne
  have hCBcard : Nat.card CB = p := by
    have h1 : p ≤ Nat.card CB := by
      rw [← hzxcard]
      exact Subgroup.card_le_of_le hzxle
    exact le_antisymm hCBle h1
  exact (Subgroup.eq_of_le_of_card_ge hzxle (by rw [hCBcard, hzxcard])).symm

private theorem lup8u3_twoLocalRank_ge (hS : GGQTwoSetting p B Bs x L D J)
    (M : lup8f_UnitaryMarking Bs L n K) (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    n - 2 ≤ LargeEvenTwoLocalRank 3 G := by
  have hThmI : GGThmIHyp p B x L := hS.1.1.1
  have hSStar : LargeEvenSStar p B x L := hThmI.2.2.2.2.2.2.1
  have hxmem : x ∈ B := hSStar.2.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSStar.2.2.2.1.1
  have hLcomp : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hSStar.2.2.2.1
  have hLperf : commutator ↥L = ⊤ := hLcomp.2.2.1
  have hxp : x ^ 3 = 1 := by
    have hEA : IsElemAbelian p B := hSStar.1.1
    have := hEA.2 x hxmem
    rwa [← hp]
  have hUF : Nat.card K = (2 ^ 1) ^ 2 := by rw [M.card_K]; norm_num
  have hd : 3 ≤ n := by omega
  have hdq : (n, 2 ^ 1) ≠ (3, 2) := by simp; omega
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 n)
      (LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ 1))) :=
    CFSG.StandardType.ggTorusLift_unitary (K := K) (n := 1) (d := n) (p := 3)
      hUF (le_refl 1) hd hdq Nat.prime_three hpq
  have hrank := CFSG.StandardType.succ_le_twoLocalRank_of_torusLift (p := 3)
    (r := ggUnitaryTorusRank 3 n)
    Nat.prime_three hLx hxp hxne hLperf M.theta hlift
  have hrank' : ggUnitaryTorusRank 3 n + 1 ≤ LargeEvenTwoLocalRank 3 G := hrank
  simp only [ggUnitaryTorusRank, hdvd, ↓reduceIte] at hrank'
  omega

private theorem lup8u3_centralizes_of_trivial
    {H : Type} [Group H] [Finite H] {L' E' : Subgroup H}
    (C : lup8f_CentralCover H L' E') [C.N.Normal]
    (F : lup8f_UFrame0 H C.N L' E' n K)
    (hL'perf : commutator ↥L' = ⊤)
    (g : ↥E')
    (hg : ∀ l : ↥L', lup8f_conjLQ C.N L' E' F.E'_le_norm g l =
      ⟨QuotientGroup.mk' C.N (l : H), Subgroup.mem_map_of_mem _ l.2⟩) :
    ∀ l : ↥L', (g : H) * (l : H) * (g : H)⁻¹ = (l : H) := by
  have hNmem : ∀ l : ↥L', (g : H) * (l : H) * (g : H)⁻¹ * (l : H)⁻¹ ∈ C.N := by
    intro l
    have h1 : QuotientGroup.mk' C.N ((g : H) * (l : H) * (g : H)⁻¹) =
        QuotientGroup.mk' C.N (l : H) := by
      have h := congrArg Subtype.val (hg l)
      simpa [lup8f_conjLQ] using h
    obtain ⟨z, hz, hzeq⟩ := (QuotientGroup.mk'_eq_mk' C.N).mp h1
    have hcomm : Commute (l : H) z := C.central z hz (l : H) l.2
    have hcentral : (l : H) * z⁻¹ * (l : H)⁻¹ = z⁻¹ := by
      rw [(hcomm.inv_right).eq, mul_assoc, mul_inv_cancel, mul_one]
    have hXeq : (g : H) * (l : H) * (g : H)⁻¹ = (l : H) * z⁻¹ :=
      eq_mul_inv_of_mul_eq hzeq
    have hmain : (g : H) * (l : H) * (g : H)⁻¹ * (l : H)⁻¹ =
        (l : H) * z⁻¹ * (l : H)⁻¹ := by rw [hXeq]
    rw [hmain, hcentral]
    exact C.N.inv_mem hz
  have hgN : (g : H) ∈ Subgroup.normalizer (L' : Set H) := F.E'_le_norm g.2
  have hσ : ∀ l : ↥L',
      (Subgroup.normalizerMonoidHom L') ⟨(g : H), hgN⟩ l * l⁻¹ ∈ Subgroup.center ↥L' := by
    intro l
    have hz : (Subgroup.normalizerMonoidHom L') ⟨(g : H), hgN⟩ l * l⁻¹ =
        (⟨(g : H) * (l : H) * (g : H)⁻¹ * (l : H)⁻¹, C.le_L (hNmem l)⟩ : ↥L') := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [Subgroup.mem_center_iff]
    intro m
    rw [hz]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact C.central ((g : H) * (l : H) * (g : H)⁻¹ * (l : H)⁻¹) (hNmem l) (m : H) m.2
  have hσ1 := CFSG.GroupTheory.MulAut.eq_one_of_mul_mem_center
    (Group.isPerfect_def.mpr hL'perf)
    ((Subgroup.normalizerMonoidHom L') ⟨(g : H), hgN⟩) hσ
  intro l
  have h2 := congrArg (fun φ : MulAut ↥L' => (φ l : H)) hσ1
  simpa only [MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using h2

private theorem lup8u3_trivial_action_of_proj_eq
    {H : Type} [Group H] {L' E' : Subgroup H}
    (C : lup8f_CentralCover H L' E') [C.N.Normal]
    (F : lup8f_UFrame0 H C.N L' E' n K)
    {a b : ↥E'}
    (h : LargeEvenProjMk (Subgroup.closure (LargeEvenGUSet (Fin n) K 2))
          ⟨F.mat a, Subgroup.subset_closure (F.mat_mem a)⟩ =
         LargeEvenProjMk (Subgroup.closure (LargeEvenGUSet (Fin n) K 2))
          ⟨F.mat b, Subgroup.subset_closure (F.mat_mem b)⟩) :
    ∀ l : ↥L', lup8f_conjLQ C.N L' E' F.E'_le_norm (b⁻¹ * a) l =
      ⟨QuotientGroup.mk' C.N (l : H), Subgroup.mem_map_of_mem _ l.2⟩ := by
  set Hc : Subgroup (GL (Fin n) K) := Subgroup.closure (LargeEvenGUSet (Fin n) K 2) with hHc
  set Nsc : Subgroup ↥Hc := (LargeEvenScalars (Fin n) K).subgroupOf Hc with hNsc
  have hquot : QuotientGroup.mk' Nsc (⟨F.mat a, Subgroup.subset_closure (F.mat_mem a)⟩ : ↥Hc) =
      QuotientGroup.mk' Nsc (⟨F.mat b, Subgroup.subset_closure (F.mat_mem b)⟩ : ↥Hc) := h
  obtain ⟨z, hz, hzeq⟩ := (QuotientGroup.mk'_eq_mk' Nsc).mp hquot
  have hzGL : (z : GL (Fin n) K) ∈ LargeEvenScalars (Fin n) K := Subgroup.mem_subgroupOf.mp hz
  rw [CFSG.Assembly.largeEvenScalars_def] at hzGL
  obtain ⟨c, hc⟩ := hzGL
  have hmat : F.mat a * Matrix.GeneralLinearGroup.scalar (Fin n) c = F.mat b := by
    have h' := congrArg Subtype.val hzeq
    rw [Subgroup.coe_mul] at h'
    rwa [← hc] at h'
  have hconj1 : MulAut.conj (Matrix.GeneralLinearGroup.scalar (Fin n) c) = 1 := by
    ext X
    rw [MulAut.conj_apply, MulAut.one_apply]
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hcom : Matrix.GeneralLinearGroup.scalar (Fin n) c * X =
        X * Matrix.GeneralLinearGroup.scalar (Fin n) c :=
      (Subgroup.mem_center_iff.mp hmem X).symm
    rw [hcom]; group
  have hconjm : MulAut.conj (F.mat b) = MulAut.conj (F.mat a) := by
    rw [show F.mat b = F.mat a * Matrix.GeneralLinearGroup.scalar (Fin n) c from hmat.symm,
      map_mul, hconj1, mul_one]
  have h4 : ∀ l : ↥L', lup8f_conjLQ C.N L' E' F.E'_le_norm a l =
      lup8f_conjLQ C.N L' E' F.E'_le_norm b l := by
    intro l
    apply F.eps.injective
    apply Subtype.ext
    rw [F.mat_ind a, F.mat_ind b, hconjm]
  intro l
  have h5 : QuotientGroup.mk' C.N ((a : H) * (l : H) * (a : H)⁻¹) =
      QuotientGroup.mk' C.N ((b : H) * (l : H) * (b : H)⁻¹) := by
    exact congrArg Subtype.val (h4 l)
  obtain ⟨z, hz, hzeq⟩ := (QuotientGroup.mk'_eq_mk' C.N).mp h5
  have hwN : (b : H)⁻¹ * z * (b : H) ∈ C.N := by
    simpa using (inferInstance : C.N.Normal).conj_mem z hz (b : H)⁻¹
  have hcoea : ((b⁻¹ * a : ↥E') : H) = (b : H)⁻¹ * (a : H) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  have hgl : ((b⁻¹ * a : ↥E') : H) * (l : H) * (((b⁻¹ * a : ↥E')) : H)⁻¹ *
      ((b : H)⁻¹ * z * (b : H)) = (l : H) := by
    rw [hcoea]
    calc (b : H)⁻¹ * (a : H) * (l : H) * ((b : H)⁻¹ * (a : H))⁻¹ * ((b : H)⁻¹ * z * (b : H))
        = (b : H)⁻¹ * ((a : H) * (l : H) * (a : H)⁻¹ * z) * (b : H) := by group
      _ = (l : H) := by rw [hzeq]; group
  have hX : ((b⁻¹ * a : ↥E') : H) * (l : H) * (((b⁻¹ * a : ↥E')) : H)⁻¹ =
      (l : H) * ((b : H)⁻¹ * z * (b : H))⁻¹ :=
    eq_mul_inv_of_mul_eq hgl
  have hw1 : QuotientGroup.mk' C.N ((b : H)⁻¹ * z * (b : H)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hwN
  apply Subtype.ext
  change QuotientGroup.mk' C.N (((b⁻¹ * a : ↥E') : H) * (l : H) * (((b⁻¹ * a : ↥E')) : H)⁻¹) =
    QuotientGroup.mk' C.N (l : H)
  rw [hX, map_mul, map_inv, hw1, inv_one, mul_one]


noncomputable def lup8f_frame1
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame0 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    lup8f_UFrame1 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K := by
  classical
  have hBBs : B ≤ Bs := hS.1.1.2.1.1
  have hSStar : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hBmax : LargeEvenIsBmax p B := hSStar.1
  have hxmem : x ∈ B := hSStar.2.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have hEA : IsElemAbelian p B := hBmax.1
  have hLperf : commutator ↥L = ⊤ := hSStar.2.2.2.1.2.2.1
  have hLL : ⁅L, L⁆ = L :=
    (Subgroup.isPerfect_iff (H := L)).mp (Group.isPerfect_def.mpr hLperf)
  have hL'perf : commutator ↥(lup8f_L' L Bs) = ⊤ := by
    have hsub : ⁅lup8f_L' L Bs, lup8f_L' L Bs⁆ = lup8f_L' L Bs := by
      rw [show lup8f_L' L Bs = L.subgroupOf (L ⊔ Bs) from rfl]
      rw [CFSG.GroupTheory.commutator_subgroupOf_eq (A := L) (B := L) (H := L ⊔ Bs)
        le_sup_left le_sup_left, hLL]
    exact Group.isPerfect_def.mp ((Subgroup.isPerfect_iff (H := lup8f_L' L Bs)).mpr hsub)
  let B' : Subgroup (lup8f_HT L Bs) := B.subgroupOf (L ⊔ Bs)
  have hB'leE' : B' ≤ lup8f_E' L Bs := Subgroup.subgroupOf_mono (L ⊔ Bs) hBBs
  let incl : ↥B' →* ↥(lup8f_E' L Bs) := Subgroup.inclusion hB'leE'
  let proj : ↥(lup8f_E' L Bs) → lup8f_PGU n K := fun b =>
    LargeEvenProjMk (Subgroup.closure (LargeEvenGUSet (Fin n) K 2))
      ⟨F.mat b, Subgroup.subset_closure (F.mat_mem b)⟩
  let f : ↥B' → lup8f_PGU n K := fun b => proj (incl b)
  haveI : Fintype ↥B' := Fintype.ofFinite ↥B'
  haveI : Fintype ↥(Set.range f) := Fintype.ofFinite ↥(Set.range f)
  let A : Subgroup (lup8f_PGU n K) := Subgroup.closure (Set.range proj)
  let x' : ↥B' := ⟨⟨x, Subgroup.mem_sup_left hxL⟩, Subgroup.mem_subgroupOf.mpr hxmem⟩
  have hx'ord : orderOf x' = 3 := by
    have hx3 : x ^ 3 = 1 := by
      have := hEA.2 x hxmem
      rwa [hp] at this
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext; apply Subtype.ext
      simpa using hx3
    · intro h
      apply hxne
      have := congrArg (fun y : ↥B' => (y : G)) h
      simpa [x'] using this
  have hfiber : ∀ y ∈ Finset.image f (Finset.univ : Finset ↥B'),
      (Finset.univ.filter fun a => f a = y).card ≤ 3 := by
    intro y hy
    obtain ⟨b0, -, hb0⟩ := Finset.mem_image.mp hy
    have hmem : ∀ a ∈ Finset.univ.filter (fun a => f a = y),
        b0⁻¹ * a ∈ Subgroup.zpowers x' := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have hfa : f a = f b0 := by rw [ha.2, hb0]
      have hproj : LargeEvenProjMk (Subgroup.closure (LargeEvenGUSet (Fin n) K 2))
            ⟨F.mat (incl a), Subgroup.subset_closure (F.mat_mem (incl a))⟩ =
          LargeEvenProjMk (Subgroup.closure (LargeEvenGUSet (Fin n) K 2))
            ⟨F.mat (incl b0), Subgroup.subset_closure (F.mat_mem (incl b0))⟩ := by
        simpa [f, proj] using hfa
      have htriv : ∀ l : ↥(lup8f_L' L Bs),
          lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs) F.E'_le_norm
            (incl (b0⁻¹ * a)) l =
          ⟨QuotientGroup.mk' C.N (l : lup8f_HT L Bs), Subgroup.mem_map_of_mem _ l.2⟩ := by
        intro l
        simpa only [map_mul, map_inv] using
          lup8u3_trivial_action_of_proj_eq C F (a := incl a) (b := incl b0) hproj l
      have hcent := lup8u3_centralizes_of_trivial C F hL'perf (incl (b0⁻¹ * a)) htriv
      have hcentG : ((b0⁻¹ * a : ↥B') : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have h := hcent ⟨⟨l, Subgroup.mem_sup_left hl⟩, Subgroup.mem_subgroupOf.mpr hl⟩
        have h' : ((b0⁻¹ * a : ↥B') : G) * l * (((b0⁻¹ * a : ↥B') : G))⁻¹ = l := by
          simpa [incl] using congrArg (fun z : ↥(L ⊔ Bs) => (z : G)) h
        calc l * ((b0⁻¹ * a : ↥B') : G) = (((b0⁻¹ * a : ↥B') : G) * l *
              (((b0⁻¹ * a : ↥B') : G))⁻¹) * ((b0⁻¹ * a : ↥B') : G) := by rw [h']
          _ = ((b0⁻¹ * a : ↥B') : G) * l := by group
      have hgB : ((b0⁻¹ * a : ↥B') : G) ∈ B :=
        Subgroup.mem_subgroupOf.mp (b0⁻¹ * a : ↥B').2
      have hgCB : ((b0⁻¹ * a : ↥B') : G) ∈ B ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨hgB, hcentG⟩
      rw [lup8u3_CB_eq_zpowers hS] at hgCB
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgCB
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      simpa [x'] using hk
    have hinj : Function.Injective (fun a : ↥(Finset.univ.filter fun a => f a = y) =>
        (⟨b0⁻¹ * (a : ↥B'), hmem a a.2⟩ : ↥(Subgroup.zpowers x'))) := by
      intro a b hab
      apply Subtype.ext
      exact mul_left_cancel (Subtype.ext_iff.mp hab)
    have hle : Nat.card ↥(Finset.univ.filter fun a => f a = y) ≤
        Nat.card ↥(Subgroup.zpowers x') :=
      Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_zpowers, hx'ord] at hle
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at hle
  have hcount : Nat.card ↥B' ≤ 3 * Nat.card ↥A := by
    have h := Finset.card_le_mul_card_image (s := (Finset.univ : Finset ↥B')) (f := f) 3 hfiber
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h
    have hcard : (Finset.image f (Finset.univ : Finset ↥B')).card =
        Nat.card ↥(Finset.image f (Finset.univ : Finset ↥B')) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [hcard] at h
    have himageA : Nat.card ↥(Finset.image f (Finset.univ : Finset ↥B')) ≤ Nat.card ↥A := by
      let g : ↥(Finset.image f (Finset.univ : Finset ↥B')) → ↥A := fun y => ⟨y.1, by
        obtain ⟨b, -, hb⟩ := Finset.mem_image.mp y.2
        rw [← hb]
        exact Subgroup.subset_closure ⟨incl b, rfl⟩⟩
      refine Nat.card_le_card_of_injective g ?_
      intro u v h
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥A → lup8f_PGU n K) h
    exact h.trans (Nat.mul_le_mul_left 3 himageA)
  have hBcard : 3 ^ (n - 2) ≤ Nat.card ↥B' := by
    have hB : Nat.card ↥B' = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans hBBs le_sup_right)).toEquiv
    rw [hB]
    have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := by
      have := hBmax.2.1
      rwa [hp] at this
    rw [hcardB]
    exact Nat.pow_le_pow_right (by norm_num) (lup8u3_twoLocalRank_ge hS M hp hdvd hn)
  have hrank : 3 ^ max (n - 3) 3 ≤ Nat.card ↥A := by
    have hpow : 3 ^ (n - 2) ≤ 3 * Nat.card ↥A := hBcard.trans hcount
    have h3 : 3 ^ (n - 2) = 3 * 3 ^ (n - 3) := by
      rw [show n - 2 = n - 3 + 1 by omega, pow_succ]; ring
    rw [h3] at hpow
    have hmain : 3 ^ (n - 3) ≤ Nat.card ↥A :=
      Nat.le_of_mul_le_mul_left hpow (by norm_num)
    have hmax : max (n - 3) 3 = n - 3 := by omega
    rw [hmax]
    exact hmain
  exact
    { le_L := F.le_L
      central := F.central
      E'_le_norm := F.E'_le_norm
      eps := F.eps
      mat := F.mat
      mat_mem := F.mat_mem
      mat_ind := F.mat_ind
      A := A
      A_def := rfl
      rank_ge := hrank }

end CFSG.StandardType.GGXInL

end
