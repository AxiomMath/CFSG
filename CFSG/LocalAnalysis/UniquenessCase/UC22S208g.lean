module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208f
public import CFSG.LocalAnalysis.UniquenessCase.UC22S208K
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846f
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Holds
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20j
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem s208g_bar2_image_equiv {A B : Subgroup G} (hAB : A ≤ B) :
    Nonempty (Bar2 ((A.subgroupOf B).map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))) ≃* Bar2 A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' : Subgroup ↥B := A.subgroupOf B with hA'
  set π : ↥B →* Bar2 B := QuotientGroup.mk' (CFSG.pCore 2 ↥B) with hπ
  set Y : Subgroup (Bar2 B) := A'.map π with hY
  let ψ : ↥A' →* ↥Y := π.subgroupMap A'
  have hψ : Function.Surjective ψ := π.subgroupMap_surjective A'
  have hker : IsPGroup 2 ψ.ker := by
    intro x
    have hx : π ((x : ↥A') : ↥B) = 1 := congrArg Subtype.val x.2
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) ⟨((x : ↥A') : ↥B), hx⟩
    have h1 : ((x : ↥A') : ↥B) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥B) => (z : ↥B)) hk
      simpa using this
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using h1
  have hO : (CFSG.pCore 2 ↥A').map ψ = CFSG.pCore 2 ↥Y :=
    CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker ψ hψ hker
  have hkerle : ψ.ker ≤ CFSG.pCore 2 ↥A' :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hker
  let φ : ↥A' →* Bar2 Y := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp ψ
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)).comp hψ
  have hφker : φ.ker = CFSG.pCore 2 ↥A' := by
    have h1 : φ.ker = (CFSG.pCore 2 ↥Y).comap ψ := by
      ext x
      simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_comap]
    rw [h1, ← hO, Subgroup.comap_map_eq, sup_eq_left.2 hkerle]
  let e₁ : (↥A' ⧸ CFSG.pCore 2 ↥A') ≃* Bar2 Y :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  let eA : ↥A ≃* ↥A' := (Subgroup.subgroupOfEquivOfLe hAB).symm
  let e₂ : Bar2 A ≃* (↥A' ⧸ CFSG.pCore 2 ↥A') :=
    QuotientGroup.congr (CFSG.pCore 2 ↥A) (CFSG.pCore 2 ↥A') eA (CFSG.pCore_map_iso 2 eA)
  exact ⟨(e₂.trans e₁).symm⟩

theorem s208g_pRank_image {A B : Subgroup G} (hAB : A ≤ B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p ((A.subgroupOf B).map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))) =
      CFSG.Open.pRank p A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥B)) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  rw [CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hp (CFSG.pCore 2 ↥B) hcop,
    Subgroup.map_subgroupOf_eq_of_le hAB]

theorem s208g_pRank_top (B : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 B)) = CFSG.Open.pRank p B := by
  have h := s208g_pRank_image (le_refl B) hp hp2
  rwa [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)] at h

theorem s208g_eq_of_sup {A B R : Subgroup G} (hBp : ⁅B, B⁆ = B) (hAB : A ≤ B)
    (hBn : B ≤ normalizer (A : Set G)) (hR : IsPGroup 2 R) (hBR : B = A ⊔ R) : A = B :=
  UC6S846.eq_of_subnormal_sup_isPGroup hBp
    (CFSG.Quasithin.A3.subnormal_of_normal hAB
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAB).2 hBn)) hR hBR

open CFSG.RankThree.PartTwo.Sec18 in
omit [Finite G] in
theorem s208g_le_of_perfect_sup {Y : Type*} [Group Y] [Finite Y] {X N O : Subgroup Y}
    (hX : ⁅X, X⁆ = X) (hXNO : X ≤ N ⊔ O) (hOn : O ≤ normalizer (N : Set Y)) (hO : IsPGroup 2 O) :
    X ≤ N := by
  have hNU : N ≤ N ⊔ O := le_sup_left
  have hUn : N ⊔ O ≤ normalizer (N : Set Y) := sup_le Subgroup.le_normalizer hOn
  have hNn : (N.subgroupOf (N ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNU).2 hUn
  have : Group.IsNilpotent ↥O := hO.isNilpotent
  have : Group.IsSolvable ↥O := inferInstance
  have hsurj : Function.Surjective ((QuotientGroup.mk' (N.subgroupOf (N ⊔ O))).comp
      (Subgroup.inclusion (le_sup_right : O ≤ N ⊔ O))) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (N ⊔ O)) q
    have hx' : x ∈ ((N ⊔ O : Subgroup Y) : Set Y) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N O hOn] at hx'
    obtain ⟨n, hn, o, ho, rfl⟩ := hx'
    refine ⟨⟨o, ho⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.1 (hOn ho) n).1 hn
  have hsolv : Group.IsSolvable ((N ⊔ O : Subgroup Y) ⧸ N.subgroupOf (N ⊔ O)) :=
    Group.isSolvable_of_surjective hsurj
  exact (le_inSubgroup_perfectResidual hX hXNO).trans
    (inSubgroup_perfectResidual_le_of_isSolvable hNU hsolv)

theorem s208g_center_eq_bot_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ center X := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem s208g_center_eq_bot_of_SzL2 {X : Type} [Group X] {n : ℕ} (hn : 2 < n)
    (h : IsSz X n ∨ IsL2 X n) : center X = ⊥ := by
  obtain ⟨hs, hnab⟩ := uc22p20g_simple_nonab_SzL2 hn h
  have := hs
  exact s208g_center_eq_bot_of_simple hnab

theorem s208g_center_eq_bot_of_prod {X : Type} [Group X] {n : ℕ} (hn : 2 < n)
    (h : IsSzL2Product X n) : center X = ⊥ := by
  obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := h
  have hZA := s208g_center_eq_bot_of_SzL2 hn hA
  have hZB := s208g_center_eq_bot_of_SzL2 hn hB
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ center (A × B) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx z)]
  rw [Subgroup.center_prod] at hex
  have h1 : (e x).1 = 1 := by
    have := hex.1
    rw [hZA] at this
    exact Subgroup.mem_bot.1 this
  have h2 : (e x).2 = 1 := by
    have := hex.2
    rw [hZB] at this
    exact Subgroup.mem_bot.1 this
  have h3 : e x = 1 := Prod.ext h1 h2
  rw [Subgroup.mem_bot]
  exact e.injective (h3.trans e.map_one.symm)

theorem s208g_isSzL2Product_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsSzL2Product X n) : IsSzL2Product Y n := by
  obtain ⟨A, B, _, _, ⟨e'⟩, hA, hB⟩ := h
  exact ⟨A, B, inferInstance, inferInstance, ⟨e.symm.trans e'⟩, hA, hB⟩

theorem s208g_orb_cj {T K : Subgroup G} {u : G} (hu : u ∈ T) :
    uc22p20bOrb T (uc22p20bCj u K) = uc22p20bOrb T K := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rw [uc22p20b_cj_cj]
    exact uc22p20b_cj_le_orb (T.mul_mem t.2 hu)
  · refine iSup_le fun t => ?_
    have : uc22p20bCj (t : G) K = uc22p20bCj ((t : G) * u⁻¹) (uc22p20bCj u K) := by
      rw [uc22p20b_cj_cj, inv_mul_cancel_right]
    rw [this]
    exact uc22p20b_cj_le_orb (T.mul_mem t.2 (T.inv_mem hu))

omit [Finite G] in
theorem s208g_le_pre_iff {H X : Subgroup G} (hXH : X ≤ H)
    (W : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    X ≤ (W.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype ↔
      (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤ W := by
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h (Subgroup.mem_subgroupOf.1 hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h x hx
    exact ⟨⟨x, hXH hx⟩, h ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩, rfl⟩

theorem s208g_images_commute {H C C' : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp H)
    (hC' : C' ∈ CFSG.Quasithin.cComp H) (hq : CFSG.Open.IsQuasisimple (Bar2 C))
    (hq' : CFSG.Open.IsQuasisimple (Bar2 C')) (hne : C ≠ C') :
    (C.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      centralizer (((C'.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hCH : C ≤ H := CFSG.Quasithin.le_of_mem_cComp hC
  have hC'H : C' ≤ H := CFSG.Quasithin.le_of_mem_cComp hC'
  have hsub : ∀ {D : Subgroup G}, D ∈ CFSG.Quasithin.cComp H →
      CFSG.Open.IsSubnormal (D.subgroupOf H) ⊤ := fun hD =>
    CFSG.Quasithin.subnormal_of_mem_cComp (CFSG.Quasithin.subgroupOf_mem_cComp hD)
  have hperf : ∀ {D : Subgroup G}, D ∈ CFSG.Quasithin.cComp H →
      ⁅D.subgroupOf H, D.subgroupOf H⁆ = D.subgroupOf H := fun hD =>
    CFSG.Quasithin.perfect_of_mem_cComp (CFSG.Quasithin.subgroupOf_mem_cComp hD)
  have hqs : ∀ {D : Subgroup G}, D ≤ H → CFSG.Open.IsQuasisimple (Bar2 D) →
      CFSG.Open.IsQuasisimple (↥(D.subgroupOf H) ⧸ CFSG.pCore 2 ↥(D.subgroupOf H)) := by
    intro D hDH hD
    obtain ⟨e⟩ := s208a_bar2_nonempty_equiv (A := D) (B := D) (MulEquiv.refl _)
    let eD : ↥(D.subgroupOf H) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDH
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr (CFSG.pCore 2 ↥(D.subgroupOf H)) (CFSG.pCore 2 ↥D) eD
        (CFSG.pCore_map_iso 2 eD)) (hD.of_mulEquiv e)
  have hAc := UC6S846.isComponent_image (hsub hC) (hqs hCH hq)
  have hA'c := UC6S846.isComponent_image (hsub hC') (hqs hC'H hq')
  have hne' : (C.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≠
      (C'.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    intro h
    apply hne
    have h1 := UC6S846.image_injective (hsub hC) (hperf hC) (hsub hC') (hperf hC') h
    have h2 : C ⊓ H = C' ⊓ H := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hCH, inf_eq_left.mpr hC'H] at h2
  have hcomm := (CFSG.LocalCores.distinct_components_commute hAc hA'c).resolve_left hne'
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

theorem s208g_pRank_add (D : Data G) {H L B : Subgroup G} (hTH : D.T ≤ H)
    (hL : L ∈ calLOf D.T D.M H) (hB : B ∈ calLOf D.T D.M H) (hne : L ≠ B)
    (hZ : center (Bar2 L) = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p L + CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (L ⊔ B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  obtain ⟨⟨-, -, -, CL, hCL, hLCL⟩, hLsub⟩ := hL
  obtain ⟨⟨-, -, -, CB, hCB, hBCB⟩, hBsub⟩ := hB
  have hLH : L ≤ H := CFSG.Quasithin.A3.subnormal_le hLsub
  have hBH : B ≤ H := CFSG.Quasithin.A3.subnormal_le hBsub
  have hCLc : CL ∈ CFSG.Quasithin.cComp H :=
    CFSG.Quasithin.cComp_mem_of_subnormal hLsub (uc22p20e_cComp_of_calC hCL)
  have hCBc : CB ∈ CFSG.Quasithin.cComp H :=
    CFSG.Quasithin.cComp_mem_of_subnormal hBsub (uc22p20e_cComp_of_calC hCB)
  have hcjc : ∀ {C : Subgroup G}, C ∈ CFSG.Quasithin.cComp H → ∀ t ∈ D.T,
      uc22p20bCj t C ∈ CFSG.Quasithin.cComp H := fun hC t ht => uc22p20b_cj_mem_cComp hC (hTH ht)
  have hcjq : ∀ {C : Subgroup G}, CFSG.Open.IsQuasisimple (Bar2 C) → ∀ t : G,
      CFSG.Open.IsQuasisimple (Bar2 (uc22p20bCj t C)) := by
    intro C hC t
    obtain ⟨e⟩ := s208a_bar2_cj_equiv t C
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e hC
  have hdist : ∀ t ∈ D.T, ∀ s ∈ D.T, uc22p20bCj t CL ≠ uc22p20bCj s CB := by
    intro t ht s hs h
    apply hne
    have hCB' : CB = uc22p20bCj (s⁻¹ * t) CL := by
      rw [← uc22p20b_cj_cj, h, s208a_cj_inv_cj]
    calc L = uc22p20bOrb D.T CL := hLCL
      _ = uc22p20bOrb D.T (uc22p20bCj (s⁻¹ * t) CL) :=
        (s208g_orb_cj (D.T.mul_mem (D.T.inv_mem hs) ht)).symm
      _ = B := by rw [← hCB']; exact hBCB.symm
  set Lb := (L.subgroupOf H).map π with hLb
  set Bb := (B.subgroupOf H).map π with hBb
  have hcomm : Lb ≤ centralizer (Bb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine (s208g_le_pre_iff hLH _).1 ?_
    have hLeq : L = ⨆ t : D.T, uc22p20bCj (t : G) CL := hLCL
    rw [hLeq]
    refine iSup_le fun t => ?_
    have htH : uc22p20bCj (t : G) CL ≤ H := CFSG.Quasithin.le_of_mem_cComp (hcjc hCLc t t.2)
    refine (s208g_le_pre_iff htH _).2 ?_
    rw [Subgroup.le_centralizer_iff]
    refine (s208g_le_pre_iff hBH _).1 ?_
    have hBeq : B = ⨆ s : D.T, uc22p20bCj (s : G) CB := hBCB
    rw [hBeq]
    refine iSup_le fun s => ?_
    have hsH : uc22p20bCj (s : G) CB ≤ H := CFSG.Quasithin.le_of_mem_cComp (hcjc hCBc s s.2)
    refine (s208g_le_pre_iff hsH _).2 ?_
    rw [← Subgroup.le_centralizer_iff]
    exact s208g_images_commute (hcjc hCLc t t.2) (hcjc hCBc s s.2) (hcjq hCL.2.2 t)
      (hcjq hCB.2.2 s) (hdist t t.2 s s.2)
  have hcen : Lb ⊓ Bb = ⊥ := by
    have hLsubT : CFSG.Open.IsSubnormal (L.subgroupOf H) ⊤ := by
      have := CFSG.Quasithin.A3.subnormal_comap H.subtype hLsub
      rwa [show H.comap H.subtype = ⊤ from Subgroup.subgroupOf_self H] at this
    let eL : (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) ≃* ↥Lb :=
      UC6S846.barIso hLsubT
    let eLL : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
    let e₀ : (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) ≃* Bar2 L :=
      QuotientGroup.congr _ _ eLL (CFSG.pCore_map_iso 2 eLL)
    have hZLb : center ↥Lb = ⊥ := by
      let f : ↥Lb ≃* Bar2 L := eL.symm.trans e₀
      rw [eq_bot_iff]
      intro z hz
      have h1 : f z ∈ center (Bar2 L) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨w, rfl⟩ := f.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
      rw [hZ, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact f.injective (h1.trans f.map_one.symm)
    rw [eq_bot_iff]
    intro x hx
    have hxz : (⟨x, hx.1⟩ : ↥Lb) ∈ center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 (hcomm g.2) x hx.2).symm
    rw [hZLb, Subgroup.mem_bot] at hxz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxz
  have hcop : Nat.Coprime p (Nat.card (Lb ⊓ Bb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) := by
    rw [hcen, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime hp
    (fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hcomm hx) y hy).symm) hcop
  have hsup : Lb ⊔ Bb = ((L ⊔ B).subgroupOf H).map π := by
    rw [hLb, hBb, ← Subgroup.map_sup]
    congr 1
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_subgroupOf_eq_of_le hBH,
      Subgroup.map_subgroupOf_eq_of_le (sup_le hLH hBH)]
  rw [hsup, hLb, hBb, s208g_pRank_image hLH hp hp2, s208g_pRank_image hBH hp hp2,
    s208g_pRank_image (sup_le hLH hBH) hp hp2] at hadd
  exact hadd

theorem s208g_not_config (D : Data G) (hLevi : KLeviRank208)
    (hS : H1930 D → ∀ L ∈ calL D.T D.M, uc22p20jSandwich (Bar2 L)) (hE : UC22P20gExcFacts)
    (hB : ListBNonabelian) (h66 : UC6.R6_6 D) (h205 : S20_5 D) (h207 : S20_7 D) :
    H1930 D → ∀ (L A : Subgroup G) (n : ℕ), ¬ S208Config D L A n := by
  intro h1930 L A n hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLs, hA, hAN, hAL, hAnot, hn, hsh⟩ := hc
  set H₀ : Subgroup G := normalizer (L : Set G) with hH₀def
  have hH₀ : H₀ ∈ hSet D.T D.M := s208a_normalizer_mem_hSet D hLs.1
  have hTH₀ : D.T ≤ H₀ := hLs.1.1
  have hLof : L ∈ calLOf D.T D.M H₀ := s208b_mem_calLOf_normalizer D hLs.1
  obtain ⟨B, hBof, hAB⟩ := h205 h1930 A hA H₀ hH₀ hAN
  have hAneB : A ≠ B := fun h => hAnot (h ▸ hBof)
  have hLneB : L ≠ B := fun h => hAL (h ▸ hAB)
  have hBcal : B ∈ calL D.T D.M := hBof.1
  obtain ⟨hTB, hBperf, -, CB, hCB, hBCB⟩ := hBcal
  have hAnM : ¬ A ≤ D.M := uc22p20i_not_le_M D hA
  have hTA : D.T ≤ normalizer (A : Set G) := hA.1
  have hBnA : D.T ⊓ B ≤ normalizer (A : Set G) := inf_le_left.trans hTA
  have hshA : IsL2 (Bar2 A) n ∨ IsSz (Bar2 A) n ∨ IsSzL2Product (Bar2 A) n := by
    rcases hsh with ⟨-, h⟩ | ⟨-, h | h⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  have key : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧
      CFSG.Open.pRank p A < CFSG.Open.pRank p B := by
    by_cases hfix : ∀ t ∈ D.T, uc22p20bCj t CB = CB
    ·
      have hBeq : B = CB := by
        rw [hBCB]
        exact le_antisymm (iSup_le fun t => (hfix t t.2).le) (uc22p20b_le_orb D.T CB)
      have hBq : CFSG.Open.IsQuasisimple (Bar2 B) := by
        rw [hBeq]
        exact hCB.2.2
      set π : ↥B →* Bar2 B := QuotientGroup.mk' (CFSG.pCore 2 ↥B) with hπ
      set Y : Subgroup (Bar2 B) := (A.subgroupOf B).map π with hYdef
      let S : Sylow 2 (Bar2 B) :=
        (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hBof.1)
      have hSY : (S : Subgroup (Bar2 B)) ≤ normalizer (Y : Set (Bar2 B)) := by
        show uc22p20iSylowBar D B ≤ _
        refine le_trans ?_ (Subgroup.le_normalizer_map π)
        refine Subgroup.map_mono fun x hx => ?_
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have hxA := Subgroup.mem_normalizer_iff.1 (hBnA (Subgroup.mem_subgroupOf.1 hx)) (y : G)
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hxA
      have hYperf : ⁅Y, Y⁆ = Y := by
        rw [hYdef, ← Subgroup.map_commutator]
        congr 1
        apply Subgroup.map_injective B.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAB, hA.2.1]
      have hYtop : Y ≠ ⊤ := by
        intro hY
        apply hAneB
        have hBeq2 : B = A ⊔ pCoreOf 2 B := by
          apply le_antisymm
          · intro b hb
            have hmem : π ⟨b, hb⟩ ∈ Y := hY ▸ Subgroup.mem_top _
            obtain ⟨a, ha, hab⟩ := hmem
            have hk : a⁻¹ * ⟨b, hb⟩ ∈ CFSG.pCore 2 ↥B := by
              rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
              exact hab
            have hbeq : b = (a : G) * ((a⁻¹ * ⟨b, hb⟩ : ↥B) : G) := by simp
            rw [hbeq]
            exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 ha) ⟨_, hk, rfl⟩
          · exact sup_le hAB (uc22p20b_pCoreOf_le B)
        refine s208g_eq_of_sup hBperf hAB ?_ (uc22p20b_isPGroup_pCoreOf B) hBeq2
        rw [hBeq2]
        exact sup_le Subgroup.le_normalizer ((uc22p20i_pCoreOf_le D hBof.1).trans hBnA)
      have hshY : IsL2 (Bar2 Y) n ∨ IsSz (Bar2 Y) n ∨ IsSzL2Product (Bar2 Y) n := by
        obtain ⟨e⟩ := s208g_bar2_image_equiv hAB
        rcases hshA with h | h | h
        · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
        · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h))
        · exact Or.inr (Or.inr (s208g_isSzL2Product_of_mulEquiv e.symm h))
      obtain ⟨P, hNP, hYSP, hPY⟩ :=
        hS h1930 B hBof.1 S (Y ⊔ (S : Subgroup (Bar2 B))) le_sup_right
      have hS2 : IsPGroup 2 (S : Subgroup (Bar2 B)) := S.isPGroup'
      have hYP : Y = Hinf P := by
        apply le_antisymm
        · exact CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual hYperf
            (le_sup_left.trans hYSP)
        · exact s208g_le_of_perfect_sup
            (CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual P) hPY hSY hS2
      have hPtop : P ≠ ⊤ := by
        rintro rfl
        apply hYtop
        rw [hYP, eq_top_iff]
        exact CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual hBq.1 le_rfl
      rw [hYP] at hshY
      obtain ⟨p, hp, hp2, hpn, hlt⟩ := hLevi (Bar2 B) hBq (uc22p20p_odd_center_bar2 ↥B)
        (h207 h1930 B hBof.1) P ⟨S, hNP⟩ hPtop n hn hshY
      refine ⟨p, hp, hp2, hpn, ?_⟩
      rwa [← hYP, hYdef, s208g_pRank_image hAB hp hp2, s208g_pRank_top B hp hp2] at hlt
    ·
      exfalso
      push Not at hfix
      obtain ⟨t, ht, hmov⟩ := hfix
      have hBorbeq : uc22p20bOrb D.T CB = B := hBCB.symm
      have hBorb : uc22p20bOrb D.T CB ∈ calL D.T D.M := hBorbeq ▸ hBof.1
      have hCBc : CB ∈ calC (uc22p20bOrb D.T CB) := hBorbeq ▸ hCB
      obtain ⟨-, hshape⟩ := s208d_orbit_two D hE h207 h1930 hBorb hCBc ht hmov
      have hBsup : B = CB ⊔ uc22p20bCj t CB := by
        rw [hBCB]
        exact s208d_orb_eq_sup D hE h207 h1930 hBorb hCBc ht hmov
      have hCBt : uc22p20bCj t CB ∈ calC B := by
        obtain ⟨hsub, hperf, hq⟩ := hCB
        refine ⟨?_, ?_, ?_⟩
        · have h1 := CFSG.Quasithin.A3.subnormal_map (MulAut.conj t).toMonoidHom hsub
          rwa [show B.map (MulAut.conj t).toMonoidHom = B from
            s208a_cj_eq_of_mem_normalizer (hTB ht)] at h1
        · show ⁅CB.map _, CB.map _⁆ = CB.map _
          rw [← Subgroup.map_commutator, hperf]
        · obtain ⟨e⟩ := s208a_bar2_cj_equiv t CB
          exact CFSG.Open.IsQuasisimple.of_mulEquiv e hq
      have hshape10 : S20_10Shape D.T B := by
        refine Or.inr (Or.inl ⟨CB, uc22p20bCj t CB, hCB, hCBt, hBsup, fun h => hmov h.symm,
          ⟨t, ht, rfl⟩, ?_⟩)
        rcases hshape with ⟨m, -, -, hm⟩ | ⟨-, hU⟩
        · refine ⟨m, fun L' hL' => ?_⟩
          rcases hL' with rfl | hL'
          · rcases hm with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rw [Set.mem_singleton_iff] at hL'
            subst hL'
            rcases s208f_shape_cj (g := t) hm with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
        · refine ⟨3, fun L' hL' => ?_⟩
          rcases hL' with rfl | hL'
          · exact Or.inr (Or.inr ⟨rfl, hU⟩)
          · rw [Set.mem_singleton_iff] at hL'
            subst hL'
            obtain ⟨e⟩ := s208a_bar2_cj_equiv t CB
            exact Or.inr (Or.inr ⟨rfl, uc22p20p_isSU3_of_mulEquiv e.symm hU⟩)
      have hSyl : CFSG.Quasithin.IsSylowIn 2 (D.T ⊓ B) B :=
        CFSG.ABGLocalTools.isSylowOf_iff.1 (uc22p20i_isSylowOf_inf D hBof.1)
      have hTJ : D.T ≤ normalizer ((A ⊔ (D.T ⊓ B) : Subgroup G) : Set G) :=
        s208f_le_normalizer_sup hTA
          ((le_inf Subgroup.le_normalizer hTB).trans Subgroup.inf_normalizer_le_normalizer_inf)
      rcases kRankOneBorel_holds (T := D.T) (L := B) (J := A ⊔ (D.T ⊓ B)) D.sylowM.isPGroup hTB
          hSyl hBperf hshape10 le_sup_right (sup_le hAB inf_le_right) hTJ with hJN | hJB
      · apply hAnM
        refine le_trans ?_ (uc22p20i_normalizer_le_M D hB h1930 hBof.1)
        exact le_inf (le_sup_left.trans hJN) (hAB.trans le_sup_left)
      · apply hAneB
        refine s208g_eq_of_sup hBperf hAB (hJB ▸ sup_le Subgroup.le_normalizer hBnA)
          (D.sylowM.isPGroup.to_le inf_le_left) hJB.symm
  obtain ⟨p, hp, hp2, hpn, hlt⟩ := key
  have hZL : center (Bar2 L) = ⊥ := by
    rcases hsh with ⟨h, -⟩ | ⟨h, -⟩
    · exact s208g_center_eq_bot_of_SzL2 hn h
    · exact s208g_center_eq_bot_of_prod hn h
  have hadd := s208g_pRank_add D hTH₀ hLof hBof hLneB hZL hp hp2
  have hLAB : L ⊔ B ≤ H₀ :=
    sup_le Subgroup.le_normalizer (CFSG.Quasithin.A3.subnormal_le hBof.2)
  have hH₀rank : CFSG.Open.pRank p (L ⊔ B) ≤ CFSG.Open.pRank p H₀ :=
    CFSG.SectionRank.pRank_mono hp.one_lt hLAB
  have hsum : 3 ≤ CFSG.Open.pRank p L + CFSG.Open.pRank p A := by
    rcases hsh with ⟨hL1, hA2⟩ | ⟨hL2, hA1⟩
    · have := s208e_one_le_pRank hn hL1 hp hpn
      have := s208e_two_le_pRank hn hA2 hp hpn
      omega
    · have := s208e_two_le_pRank hn hL2 hp hpn
      have := s208e_one_le_pRank hn hA1 hp hpn
      omega
  have hM2 : 2 ≤ CFSG.Open.pRank p (H₀ ⊓ D.M) := by
    rcases hsh with ⟨-, hA2⟩ | ⟨hL2, -⟩
    · have h := s208e_two_le_pRank_borel D hB h1930 hA hn hA2 hp hpn
      exact h.trans (CFSG.SectionRank.pRank_mono hp.one_lt
        (inf_le_inf_right D.M (sup_le hAN hTH₀)))
    · have h := s208e_two_le_pRank_borel D hB h1930 hLs.1 hn hL2 hp hpn
      exact h.trans (CFSG.SectionRank.pRank_mono hp.one_lt
        (inf_le_inf_right D.M (sup_le Subgroup.le_normalizer hTH₀)))
  have h1 := (s20_1_12 D h66 H₀ hH₀).2 p hp hp2 (by omega)
  omega

theorem s20_8_of (D : Data G) (hE : UC22P20gExcFacts) (hB : ListBNonabelian)
    (hU38 : uc22p20oU38Witness) (hLevi : KLeviRank208)
    (hS : H1930 D → ∀ L ∈ calL D.T D.M, uc22p20jSandwich (Bar2 L)) (h66 : UC6.R6_6 D)
    (h204 : S20_4 D) (h205 : S20_5 D) (h207 : S20_7 D) : S20_8 D :=
  s20_8_of_not_config D hE hB hU38 h66 h204 h205 h207
    (s208g_not_config D hLevi hS hE hB h66 h205 h207)

end CFSG.LocalAnalysis.UniquenessCase.UC22
