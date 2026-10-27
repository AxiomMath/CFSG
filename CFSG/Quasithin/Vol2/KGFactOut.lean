module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Red
public import CFSG.RankThree.PartOne.S11b.Sec109LnTwoOuter
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

namespace KGOut

section General

variable {G : Type*} [Group G]

@[expose] def conjK (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ↥K ≃* ↥K where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    apply (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2
    have e : g * (g⁻¹ * (x : G) * g) * g⁻¹ = x := by group
    rw [e]
    exact x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjK_apply (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G))
    (x : ↥K) : ((conjK K g hg x : ↥K) : G) = g * x * g⁻¹ := rfl

theorem map_conjK_pCore (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    (CFSG.pCore 2 ↥K).map (conjK K g hg).toMonoidHom = CFSG.pCore 2 ↥K :=
  Subgroup.characteristic_iff_map_eq.1 inferInstance _

@[expose] noncomputable def inducedQ (K : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  QuotientGroup.congr _ _ (conjK K g hg) (map_conjK_pCore K g hg)

theorem inducedQ_mk (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G))
    (x : ↥K) : inducedQ K g hg (QuotientGroup.mk x) = QuotientGroup.mk (conjK K g hg x) := rfl

theorem mem_normalizer_pCoreOf (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := by
  have key : ∀ g : G, ∀ hg : g ∈ Subgroup.normalizer (K : Set G), ∀ x : G,
      x ∈ pCoreOf 2 K → g * x * g⁻¹ ∈ pCoreOf 2 K := by
    intro g hg x hx
    rw [pCoreOf] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨conjK K g hg y, ?_, rfl⟩
    rw [← map_conjK_pCore K g hg]
    exact ⟨y, hy, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  have := key g⁻¹ hg' _ h
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

variable [Finite G]

theorem exists_mem_centralizerMod_of_sq_inner (X K S : Subgroup G) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S X)
    (hOut : ∀ α : MulAut (↥K ⧸ CFSG.pCore 2 ↥K), ∃ k : ↥K ⧸ CFSG.pCore 2 ↥K,
      α * α = MulAut.conj k) :
    ∀ x ∈ X, ∃ d ∈ centralizerMod (pCoreOf 2 K) X K, d⁻¹ * x ∈ K ⊔ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := centralizerMod (pCoreOf 2 K) X K with hD
  have hDX : D ≤ X := centralizerMod_le_left _ _ _
  have hOK : ∀ y : ↥K, y ∈ CFSG.pCore 2 ↥K → (y : G) ∈ pCoreOf 2 K := by
    intro y hy
    rw [pCoreOf]
    exact ⟨y, hy, rfl⟩
  have hsq : ∀ x ∈ X, ∃ k ∈ K, ∃ d ∈ D, x * x = k * d := by
    intro x hx
    have hxN := hXN hx
    have hxxN : x * x ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hxN hxN
    obtain ⟨kb, hkb⟩ := hOut (inducedQ K x hxN)
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective kb
    refine ⟨k₀, k₀.2, (k₀ : G)⁻¹ * (x * x), ?_, by group⟩
    refine ⟨X.mul_mem (X.inv_mem (hKX k₀.2)) (X.mul_mem hx hx), ?_, fun u hu => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_normalizer_pCoreOf K (hXN (hKX k₀.2))))
        (mem_normalizer_pCoreOf K hxxN)
    ·
      have h1 := congrArg (fun f : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
        f (QuotientGroup.mk ⟨u, hu⟩)) hkb
      simp only [MulAut.mul_apply, inducedQ_mk, MulAut.conj_apply] at h1
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq] at h1
      have h2 := hOK _ h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply] at h2
      have hA : x * (x * u * x⁻¹) * x⁻¹ ∈ K :=
        ((conjK K x hxN (conjK K x hxN ⟨u, hu⟩)) : ↥K).2
      have hc : (k₀ : G)⁻¹ * (x * (x * u * x⁻¹) * x⁻¹) ∈
          Subgroup.normalizer (pCoreOf 2 K : Set G) :=
        mem_normalizer_pCoreOf K (Subgroup.le_normalizer (K.mul_mem (K.inv_mem k₀.2) hA))
      have h3 := (Subgroup.mem_normalizer_iff.1 hc _).1 (Subgroup.inv_mem _ h2)
      have e : (k₀ : G)⁻¹ * (x * x) * u * ((k₀ : G)⁻¹ * (x * x))⁻¹ * u⁻¹ =
          ((k₀ : G)⁻¹ * (x * (x * u * x⁻¹) * x⁻¹)) *
            ((x * (x * u * x⁻¹) * x⁻¹)⁻¹ * ((k₀ : G) * u * (k₀ : G)⁻¹))⁻¹ *
            ((k₀ : G)⁻¹ * (x * (x * u * x⁻¹) * x⁻¹))⁻¹ := by group
      rw [e]
      exact h3
  have hDn : (D.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnX, hnN, hn⟩ := hn
    have hgN := mem_normalizer_pCoreOf K (hXN g.2)
    refine ⟨X.mul_mem (X.mul_mem g.2 hnX) (X.inv_mem g.2),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hnN) (Subgroup.inv_mem _ hgN), fun u hu => ?_⟩
    have hu' : (g : G)⁻¹ * u * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hXN g.2)) u).1 hu
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.1 hgN _).1 (hn _ hu')
    convert h1 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hKn : (K.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.1 (hXN g.2) (n : G)).1 hn⟩
  set N : Subgroup ↥X := D.subgroupOf X ⊔ K.subgroupOf X with hN
  have hNn : N.Normal := Subgroup.sup_normal _ _
  have hQ2 : IsPGroup 2 (↥X ⧸ N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, sq]
    obtain ⟨k, hk, d, hd, he⟩ := hsq x x.2
    have hmem : x * x = (⟨k, hKX hk⟩ : ↥X) * ⟨d, hDX hd⟩ := Subtype.ext he
    rw [hmem]
    refine N.mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
    · rw [Subgroup.mem_subgroupOf]; exact hk
    · rw [Subgroup.mem_subgroupOf]; exact hd
  obtain ⟨-, hS2, hSodd⟩ := hS
  have hS2' : IsPGroup 2 (S.subgroupOf X) := hS2.comap_subtype
  let SX : Sylow 2 ↥X := hS2'.toSylow hSodd
  let SQ : Sylow 2 (↥X ⧸ N) := SX.mapSurjective (QuotientGroup.mk'_surjective N)
  have hSQ : (SQ : Subgroup (↥X ⧸ N)) = ⊤ :=
    (SQ.is_maximal' (IsPGroup.of_equiv hQ2 Subgroup.topEquiv.symm) le_top).symm
  intro x hx
  have hq : (QuotientGroup.mk ⟨x, hx⟩ : ↥X ⧸ N) ∈ (SQ : Subgroup (↥X ⧸ N)) := by
    rw [hSQ]; exact Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hq
  obtain ⟨s, hs, hsx⟩ := hq
  have hsx' : s⁻¹ * ⟨x, hx⟩ ∈ N := by
    rw [← QuotientGroup.eq]
    exact hsx
  have hn : (⟨x, hx⟩ : ↥X) * s⁻¹ ∈ N := by
    have := hNn.conj_mem _ hsx' s
    simpa [mul_assoc] using this
  obtain ⟨d, hd, k, hk, hdk⟩ := Subgroup.mem_sup_of_normal_right.1 hn
  rw [Subgroup.mem_subgroupOf] at hd hk
  refine ⟨d, hd, ?_⟩
  have hs' : (s : G) ∈ S := by
    have : s ∈ (SX : Subgroup ↥X) := hs
    rw [IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at this
    exact this
  have e : (d : G)⁻¹ * x = k * s := by
    have := congrArg Subtype.val hdk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc (d : G)⁻¹ * x = (d : G)⁻¹ * (x * (s : G)⁻¹) * s := by group
      _ = (d : G)⁻¹ * ((d : G) * k) * s := by rw [← this]
      _ = k * s := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hs')

end General

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem sq_inner_of_card_outer_le_two {L : Type} [Group L] [Finite L]
    (h : Nat.card (Outer L) ≤ 2) (α : MulAut L) : ∃ k : L, α * α = MulAut.conj k := by
  have : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  have hα : (QuotientGroup.mk (α * α) : Outer L) = 1 := by
    rw [QuotientGroup.mk_mul, ← sq]
    apply orderOf_dvd_iff_pow_eq_one.1
    have h1 := orderOf_dvd_natCard (QuotientGroup.mk α : Outer L)
    have h2 : 0 < Nat.card (Outer L) := Nat.card_pos
    have h3 : Nat.card (Outer L) ∣ 2 := by
      interval_cases hc : Nat.card (Outer L) <;> norm_num
    exact h1.trans h3
  rw [QuotientGroup.eq_one_iff] at hα
  obtain ⟨k, hk⟩ := hα
  exact ⟨k, hk.symm⟩

theorem sq_inner_sl_two {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (α : MulAut L) :
    ∃ k : L, α * α = MulAut.conj k := by
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  let e₁ := CFSG.RankThree.PartOne.Sec109.projectiveSLEquivSL_two h2 (n := n) (by omega)
  let e₂ := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    n (ZMod 2)
  let e₃ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n (ZMod 2)
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL n 2 1 := by
    refine ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega,
      fun h => by simp at h⟩, ZMod 2, inferInstance, inferInstance, by simp, ⟨?_⟩⟩
    exact e.trans (e₁.trans (e₂.symm.trans e₃))
  exact sq_inner_of_card_outer_le_two (CFSG.RankThree.PartOne.Sec109.lnTwoOuter L n hmodel).2 α

theorem sq_inner_alt_seven {L : Type} [Group L] (e : L ≃* alternatingGroup (Fin 7))
    (α : MulAut L) : ∃ k : L, α * α = MulAut.conj k := by
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 (MulAut.congr e α)
  have hσ2 : σ * σ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, ← sq, Int.units_sq]
  refine ⟨e.symm ⟨σ * σ, hσ2⟩, ?_⟩
  apply (MulAut.congr e).injective
  rw [map_mul, ← hσ, ← map_mul, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    MulEquiv.apply_symm_apply]
  ext y
  simp [MulAut.conjNormal_apply]

end KGOut

open KGOut in
theorem outFact1295_holds : OutFact1295 := by
  intro G _ _ X K S hKX hXN hS hK
  refine exists_mem_centralizerMod_of_sq_inner X K S hKX hXN hS ?_
  rcases hK with h | h
  · obtain ⟨e⟩ := h
    exact fun α => sq_inner_sl_two (by norm_num) e α
  · obtain ⟨e⟩ := h
    exact fun α => sq_inner_sl_two (by norm_num) e α

open KGOut in
theorem outFact1297_holds : OutFact1297 := by
  intro G _ _ X K S hKX hXN hS hK
  refine exists_mem_centralizerMod_of_sq_inner X K S hKX hXN hS ?_
  rcases hK with h | h | h
  · obtain ⟨e⟩ := h
    exact fun α => sq_inner_alt_seven e α
  · obtain ⟨e⟩ := h
    exact fun α => sq_inner_sl_two (by norm_num) e α
  · obtain ⟨e⟩ := h
    exact fun α => sq_inner_sl_two (by norm_num) e α

end CFSG.Quasithin.H13
