module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Sub
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Basic
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem injective_toMonoidHom_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') :
    Function.Injective e.toMonoidHom := e.injective

theorem map_map_symm_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (S' : Subgroup G') :
    (S'.map e.symm.toMonoidHom).map e.toMonoidHom = S' := by
  rw [Subgroup.map_map]
  ext x
  simp

theorem isSylowTwoOf_top_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.map e.toMonoidHom) ⊤ ↔
      CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
  have hinj := injective_toMonoidHom_cs5 e
  have hidx1 : ((S.map e.toMonoidHom).subgroupOf (⊤ : Subgroup G')).index =
      (S.map e.toMonoidHom).index := Subgroup.relIndex_top_right _
  have hidx2 : (S.subgroupOf (⊤ : Subgroup G)).index = S.index :=
    Subgroup.relIndex_top_right _
  have hidx : (S.map e.toMonoidHom).index = S.index := Subgroup.index_map_equiv S e
  unfold CFSG.QuasithinUnique.IsSylowTwoOf
  constructor
  · rintro ⟨-, hP, hd⟩
    rw [hidx1, hidx] at hd
    rw [hidx2]
    exact ⟨le_top, hP.of_equiv (Subgroup.equivMapOfInjective S e.toMonoidHom hinj).symm, hd⟩
  · rintro ⟨-, hP, hd⟩
    rw [hidx2] at hd
    rw [hidx1, hidx]
    exact ⟨le_top, hP.of_equiv (Subgroup.equivMapOfInjective S e.toMonoidHom hinj), hd⟩

theorem mem_normalizer_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) (g : G') :
    g ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G') ↔
      e.symm g ∈ Subgroup.normalizer (S : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq S e, Subgroup.mem_map_equiv]

theorem conjSub_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (g : G)
    (S : Subgroup G) :
    B6.conjSub (e g) (S.map e.toMonoidHom) = (B6.conjSub g S).map e.toMonoidHom := by
  ext x
  simp only [B6.mem_conjSub, Subgroup.mem_map_equiv, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem mem_centerSub_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) (z : G) :
    e z ∈ centerSub (S.map e.toMonoidHom) ↔ z ∈ centerSub S := by
  rw [mem_centerSub_cs5, mem_centerSub_cs5, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun s hs => ?_⟩
    have h1 := hc (e s) (Subgroup.mem_map_of_mem _ hs)
    have h2 : e (s * z) = e (z * s) := by simpa [map_mul] using h1
    exact e.injective h2
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun s' hs' => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
    simpa [map_mul] using congrArg e (hc s hs)

theorem centerSub_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) : centerSub (S.map e.toMonoidHom) = (centerSub S).map e.toMonoidHom := by
  ext x
  obtain ⟨z, rfl⟩ := e.surjective x
  rw [mem_centerSub_map_mulEquiv_cs5 e S z, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem ti_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    ∀ g ∈ (⊤ : Subgroup G'), g ∉ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G') →
      S.map e.toMonoidHom ⊓ B6.conjSub g (S.map e.toMonoidHom) = ⊥ := by
  intro g _ hg
  obtain ⟨x, rfl⟩ := e.surjective g
  have hx : x ∉ Subgroup.normalizer (S : Set G) := fun hc =>
    hg ((mem_normalizer_map_mulEquiv_cs5 e S (e x)).mpr (by
      rw [MulEquiv.symm_apply_apply]
      exact hc))
  have key := h.ti x (Subgroup.mem_top _) hx
  rw [conjSub_map_mulEquiv_cs5, ← Subgroup.map_inf_eq S (B6.conjSub x S) e.toMonoidHom
    (injective_toMonoidHom_cs5 e), key, Subgroup.map_bot]

theorem index_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    ((⊤ : Subgroup G') ⊓ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G')).relIndex
        ⊤ = Nat.card (S.map e.toMonoidHom) + 1 := by
  have hi := h.index
  rw [inf_eq_right.mpr le_top, Subgroup.relIndex_top_right] at hi
  have hidxN : ((Subgroup.normalizer (S : Set G)).map e.toMonoidHom).index =
      (Subgroup.normalizer (S : Set G)).index := Subgroup.index_map_equiv _ e
  rw [inf_eq_right.mpr le_top, Subgroup.relIndex_top_right, ← Subgroup.map_equiv_normalizer_eq S e,
    hidxN, hi, Subgroup.card_map_of_injective (injective_toMonoidHom_cs5 e)]

theorem core_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    ∀ N : Subgroup G', N ≤ (⊤ : Subgroup G') ⊓
        Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G') →
      (∀ x ∈ (⊤ : Subgroup G'), ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N = ⊥ := by
  intro N hN hnorm
  have hNS : ∀ n ∈ N, e.symm n ∈ Subgroup.normalizer (S : Set G) := fun n hn =>
    (mem_normalizer_map_mulEquiv_cs5 e S n).mp (Subgroup.mem_inf.mp (hN hn)).2
  have hM : ∀ m : G, m ∈ N.map e.symm.toMonoidHom ↔ e m ∈ N := by
    intro m
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hMle : N.map e.symm.toMonoidHom ≤ (⊤ : Subgroup G) ⊓ Subgroup.normalizer (S : Set G) := by
    intro m hm
    have h1 := hNS (e m) ((hM m).mp hm)
    rw [MulEquiv.symm_apply_apply] at h1
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, h1⟩
  have hMnorm : ∀ x ∈ (⊤ : Subgroup G), ∀ m ∈ N.map e.symm.toMonoidHom,
      x * m * x⁻¹ ∈ N.map e.symm.toMonoidHom := by
    intro x _ m hm
    have hem : e m ∈ N := (hM m).mp hm
    have h1 := hnorm (e x) (Subgroup.mem_top _) (e m) hem
    exact (hM _).mpr (by simpa [map_mul, map_inv] using h1)
  have hMbot := h.core _ hMle hMnorm
  rw [eq_bot_iff]
  intro n hn
  have hmem : e.symm n ∈ N.map e.symm.toMonoidHom :=
    (hM (e.symm n)).mpr (by rw [MulEquiv.apply_symm_apply]; exact hn)
  rw [hMbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  have h2 := congrArg e hmem
  rwa [map_one, MulEquiv.apply_symm_apply] at h2

theorem zcard_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    Nat.card ↥(centerSub (S.map e.toMonoidHom)) = q := by
  rw [centerSub_map_mulEquiv_cs5 e S, Subgroup.card_map_of_injective (injective_toMonoidHom_cs5 e)]
  exact h.zcard

theorem zexp_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    ∀ z ∈ centerSub (S.map e.toMonoidHom), z * z = 1 := by
  intro z hz
  rw [centerSub_map_mulEquiv_cs5 e S] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
  rw [← map_mul, h.zexp z₀ hz₀, map_one]

theorem ztrans_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    ∀ z ∈ centerSub (S.map e.toMonoidHom), z ≠ 1 → ∀ z' ∈ centerSub (S.map e.toMonoidHom),
      z' ≠ 1 → ∃ b ∈ (⊤ : Subgroup G') ⊓
        Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G'), b * z * b⁻¹ = z' := by
  intro z hz hz1 z' hz' hz'1
  rw [centerSub_map_mulEquiv_cs5 e S] at hz hz'
  obtain ⟨z₁, hz₁, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨z₂, hz₂, rfl⟩ := Subgroup.mem_map.mp hz'
  have hz₁1 : z₁ ≠ 1 := fun h1 => hz1 (by rw [h1, map_one])
  have hz₂1 : z₂ ≠ 1 := fun h1 => hz'1 (by rw [h1, map_one])
  obtain ⟨b, hb, hbeq⟩ := h.ztrans z₁ hz₁ hz₁1 z₂ hz₂ hz₂1
  refine ⟨e b, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩, ?_⟩
  · rw [mem_normalizer_map_mulEquiv_cs5, MulEquiv.symm_apply_apply]
    exact (Subgroup.mem_inf.mp hb).2
  · simpa [map_mul, map_inv] using congrArg e hbeq

theorem omega1_map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    ∀ x ∈ S.map e.toMonoidHom, x * x = 1 → x ∈ centerSub (S.map e.toMonoidHom) := by
  intro x hx hx2
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
  have hx₂ : x₀ * x₀ = 1 := by
    apply injective_toMonoidHom_cs5 e
    rw [map_mul, map_one]
    exact hx2
  rw [centerSub_map_mulEquiv_cs5 e S]
  exact Subgroup.mem_map_of_mem _ (h.omega1 x₀ hx₀ hx₂)

theorem RankOneSyl.map_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    {S : Subgroup G} (h : RankOneSyl (⊤ : Subgroup G) S q) :
    RankOneSyl (⊤ : Subgroup G') (S.map e.toMonoidHom) q :=
  { sylow := (isSylowTwoOf_top_map_mulEquiv_cs5 e S).mpr h.sylow
    ti := ti_map_mulEquiv_cs5 e h
    index := index_map_mulEquiv_cs5 e h
    core := core_map_mulEquiv_cs5 e h
    zcard := zcard_map_mulEquiv_cs5 e h
    zexp := zexp_map_mulEquiv_cs5 e h
    ztrans := ztrans_map_mulEquiv_cs5 e h
    omega1 := omega1_map_mulEquiv_cs5 e h
    three_le := h.three_le }

theorem RankOneSyl.of_mulEquiv_cs5 {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {q : ℕ}
    (h : ∀ S : Subgroup G, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → RankOneSyl (⊤ : Subgroup G) S q) :
    ∀ S' : Subgroup G', CFSG.QuasithinUnique.IsSylowTwoOf S' ⊤ → RankOneSyl (⊤ : Subgroup G') S' q := by
  intro S' hS'
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (S'.map e.symm.toMonoidHom) ⊤ :=
    (isSylowTwoOf_top_map_mulEquiv_cs5 e.symm S').mpr hS'
  have hT := RankOneSyl.map_mulEquiv_cs5 e (h _ hS)
  rwa [map_map_symm_cs5 e S'] at hT

theorem exists_mulEquiv_psu3_proj_cs5 {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n)
    (hG : IsPSU 3 2 n G) :
    Nonempty (G ≃* CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup
      (CFSG.BenderSuzuki.binaryQuadraticHermitian n (by omega))) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hG
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 //
      (CFSG.BenderSuzuki.binaryQuadraticHermitian n (by omega)).conj x = x} = 2 ^ n :=
    CFSG.BenderSuzuki.quadraticBinaryFrobenius_fixed_card n (by omega)
  obtain ⟨eJ⟩ := CFSG.BenderSuzuki.projectiveSpecialUnitary_equiv_PSU3Model
    (CFSG.BenderSuzuki.binaryQuadraticHermitian n (by omega)) n hn rfl hEcard hfixed
  exact ⟨((e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hK')).trans
    (MulEquiv.subgroupCongr
      (show CFSG.Open.PSU3 2 n = CFSG.Theory.Comparator.PSU3Model n from rfl))).trans eJ.symm⟩

end CFSG.Quasithin.H13
