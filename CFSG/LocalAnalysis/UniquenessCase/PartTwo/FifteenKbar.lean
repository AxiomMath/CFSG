module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Kbar_commSub_map_conj {W : Type*} [CommGroup W]
    (U : Subgroup W) (Y : Subgroup (MulAut W)) (α : MulAut W) :
    commSub (U.map α.toMonoidHom) (Y.map (MulAut.conj α).toMonoidHom) =
      (commSub U Y).map α.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨x₀ w₀ * w₀⁻¹, ⟨x₀, hx₀, w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, w₀, hw₀, rfl⟩ := hs
    refine ⟨MulAut.conj α x₀, ⟨x₀, hx₀, rfl⟩, α w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]

theorem s15_Kbar_conj_mem_of_normal {W : Type*} [CommGroup W] {A Y : Subgroup (MulAut W)}
    (hYA : Y ≤ A) (hN : (Y.subgroupOf A).Normal) {φ y : MulAut W} (hφ : φ ∈ A) (hy : y ∈ Y) :
    φ * y * φ⁻¹ ∈ Y :=
  (Subgroup.normal_subgroupOf_iff hYA).1 hN y φ hy hφ

private lemma s15_Kbar_eq_one_of_mem_v0 {V₀ : Subgroup G} (h0 : V₀ = ⊥) {x : G}
    (hx : x ∈ V₀) : x = 1 := by
  rw [h0] at hx
  exact Subgroup.mem_bot.mp hx

private lemma s15_Kbar_mem_v0_of_eq_one {V₀ : Subgroup G} (h0 : V₀ = ⊥) {x : G}
    (hx : x = 1) : x ∈ V₀ := by
  rw [h0]
  exact Subgroup.mem_bot.mpr hx

theorem s15_Kbar_irreducible {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) (U : Subgroup (Vtil V₀ V h.isElemAbelian))
    (hU : ∀ φ ∈ Mbar D.M V₀ V h.isElemAbelian, ∀ u ∈ U, φ u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have hV := h.isElemAbelian
  rcases h.1.resolve_left (fun hh => hV₀ hh.2) with ⟨hV0, -, -⟩
  obtain ⟨-, -, -, -, -, hgen, -⟩ := hV0
  by_cases hUbot : U = ⊥
  · exact Or.inl hUbot
  · right
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUbot
    have hu1' : u.1 ≠ 1 := fun hh => hu1 (Subtype.ext hh)
    obtain ⟨x, hx⟩ := mkTil_surjective V₀ V hV u.1
    have hxV : x.val ∈ V := x.val_mem
    have hx0 : x.val ∉ V₀ := by
      intro hx0
      apply hu1'
      rw [← hx, ← map_one (mkTil V₀ V hV), mkTil_eq_iff]
      simpa using hx0
    have hcl_le : Subgroup.closure {y : G | ∃ m ∈ D.M, y = m * x.val * m⁻¹} ≤
        preTil V₀ V hV U := by
      rw [Subgroup.closure_le]
      rintro y ⟨m, hm, rfl⟩
      have hm_st : m ∈ stabTil V₀ V :=
        le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ hm
      have hmv : m * x.val * m⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (h.pairFacts.le_normalizer hm) x.val).1 x.val_mem
      have hEq : actStab V₀ V hV ⟨m, hm_st⟩ x = IntMod.mk hV ⟨m * x.val * m⁻¹, hmv⟩ :=
        IntMod.val_injective (by
          show (actStab V₀ V hV ⟨m, hm_st⟩ x).val = m * x.val * m⁻¹
          rw [actStab_apply_val])
      have hmem : mkTil V₀ V hV (IntMod.mk hV ⟨m * x.val * m⁻¹, hmv⟩) ∈ U := by
        rw [← hEq, ← actTil_mk V₀ V hV ⟨m, hm_st⟩ x]
        rw [hx]
        exact hU _ (actTil_mem_barSub V₀ V hV hm hm_st) u.1 u.2
      exact (mem_preTil_iff_of_mem V₀ V hV U hmv).2 hmem
    have hle : V ≤ preTil V₀ V hV U :=
      (le_of_eq (hgen x.val hxV hx0).symm).trans hcl_le
    refine le_antisymm le_top fun q _ => ?_
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV q
    exact (mem_preTil_iff_of_mem V₀ V hV U y.val_mem).1 (hle y.val_mem)

private theorem s15_Kbar_fixV_invariant {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hYM : Y ≤ Mbar D.M V₀ V h.isElemAbelian)
    (hYn : (Y.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal) :
    ∀ φ ∈ Mbar D.M V₀ V h.isElemAbelian, ∀ u ∈ fixV Y, φ u ∈ fixV Y := by
  intro φ hφ u hu
  rw [mem_fixV] at hu ⊢
  intro y hy
  have hy' : φ⁻¹ * y * φ ∈ Y := by
    have h1 : φ⁻¹ * y * (φ⁻¹)⁻¹ ∈ Y :=
      (Subgroup.normal_subgroupOf_iff hYM).1 hYn y (φ⁻¹) hy (inv_mem hφ)
    simpa only [inv_inv] using h1
  calc y (φ u) = (y * φ) u := rfl
    _ = (φ * (φ⁻¹ * y * φ)) u := by rw [show y * φ = φ * (φ⁻¹ * y * φ) by group]
    _ = φ ((φ⁻¹ * y * φ) u) := rfl
    _ = φ u := by rw [hu _ hy']

theorem s15_Kbar_no_two_quotient {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    ∀ N : Subgroup ↥(barSub V₀ V h.isElemAbelian L), N.Normal →
      (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤ := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hLs : L ≤ stabTil V₀ V := h.le.trans hMs
  let ψ : ↥L →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hLs)
  have hrange : ψ.range = barSub V₀ V hV L := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLs x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  let φ₀ : ↥L →* ↥(barSub V₀ V hV L) :=
    ψ.codRestrict (barSub V₀ V hV L)
      (fun x => hrange ▸ MonoidHom.mem_range.2 ⟨x, rfl⟩)
  have hφ₀surj : Function.Surjective φ₀ := by
    intro y
    have hy : (y : MulAut (Vtil V₀ V hV)) ∈ ψ.range := by
      rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
    exact ⟨x, Subtype.ext hx⟩
  intro N hN h2
  obtain ⟨n, hn⟩ := h2
  have hN₁ : (N.comap φ₀).Normal := hN.comap φ₀
  have hidx : (N.comap φ₀).index = 2 ^ n := by
    rw [Subgroup.index_comap_of_surjective (H := N) (f := φ₀) hφ₀surj, hn]
  have hKle : (N.comap φ₀).map (Subgroup.subtype L) ≤ L :=
    Subgroup.map_subtype_le (N.comap φ₀)
  have hKsub : ((N.comap φ₀).map (Subgroup.subtype L)).subgroupOf L = N.comap φ₀ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hnorm : L ≤ normalizer ((N.comap φ₀).map (Subgroup.subtype L) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).1 (hKsub.symm ▸ hN₁)
  have hpow : ∀ y ∈ L, ∃ k : ℕ, y ^ 2 ^ k ∈ (N.comap φ₀).map (Subgroup.subtype L) := by
    intro y hy
    refine ⟨n, ?_⟩
    haveI : (N.comap φ₀).Normal := hN₁
    have hmem : (⟨y, hy⟩ : ↥L) ^ (2 ^ n) ∈ N.comap φ₀ := by
      rw [← hidx]
      exact Subgroup.pow_index_mem (N.comap φ₀) ⟨y, hy⟩
    refine Subgroup.mem_map.2 ⟨(⟨y, hy⟩ : ↥L) ^ (2 ^ n), hmem, ?_⟩
    rw [map_pow]
    rfl
  have hle : L ≤ (N.comap φ₀).map (Subgroup.subtype L) := by
    have hstep := twoResidual_le_of_isTwoQuotient hKle hnorm hpow
    rwa [h.twoResidual_eq] at hstep
  have hKeq : (N.comap φ₀).map (Subgroup.subtype L) = L := le_antisymm hKle hle
  have hN₁top : N.comap φ₀ = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    have hxK : (Subgroup.subtype L) x ∈ (N.comap φ₀).map (Subgroup.subtype L) := by
      rw [hKeq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxK
    rwa [Subtype.ext_iff.mpr hyx] at hy
  ext y
  simp only [Subgroup.mem_top, iff_true]
  obtain ⟨z, hz⟩ := hφ₀surj y
  have hzN : z ∈ N.comap φ₀ := by rw [hN₁top]; exact Subgroup.mem_top z
  rw [← hz]
  exact Subgroup.mem_comap.1 hzN

theorem s15_Kbar_commute_conj {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {m m' : G} (hm : m ∈ D.M) (hm' : m' ∈ D.M)
    (hne : m' * m⁻¹ ∉ nBar D.M V₀ V h.isElemAbelian L) :
    ⁅barSub V₀ V h.isElemAbelian (conjSubgroup L m),
        barSub V₀ V h.isElemAbelian (conjSubgroup L m')⁆ = ⊥ ∧
      commSub (commSub ⊤ (barSub V₀ V h.isElemAbelian (conjSubgroup L m)))
        (barSub V₀ V h.isElemAbelian (conjSubgroup L m')) = ⊥ := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hm_st : m ∈ stabTil V₀ V := hMs hm
  let g : G := m' * m⁻¹
  have hgM : g ∈ D.M := D.M.mul_mem hm' (D.M.inv_mem hm)
  have hgne : g ∉ nBar D.M V₀ V hV L := hne
  let α : MulAut (Vtil V₀ V hV) := (actTil V₀ V hV ⟨m, hm_st⟩)⁻¹
  have hKm : barSub V₀ V hV (conjSubgroup L m) =
      (barSub V₀ V hV L).map (MulAut.conj α).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup V₀ V hV hm_st L
  have hg_eq : conjSubgroup (conjSubgroup L g) m = conjSubgroup L m' := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    show (m' * m⁻¹) * m = m'
    group
  have hKm' : barSub V₀ V hV (conjSubgroup L m') =
      (barSub V₀ V hV (conjSubgroup L g)).map (MulAut.conj α).toMonoidHom := by
    rw [← hg_eq]
    exact s15_Infra_barSub_conjSubgroup V₀ V hV hm_st (conjSubgroup L g)
  obtain ⟨hc1, hc2⟩ := h.commute g hgM hgne
  have h1 : ⁅barSub V₀ V hV (conjSubgroup L m),
      barSub V₀ V hV (conjSubgroup L m')⁆ = ⊥ := by
    rw [hKm, hKm', ← Subgroup.map_commutator (f := (MulAut.conj α).toMonoidHom), hc1,
      Subgroup.map_bot]
  have hmap1 : commSub ⊤ ((barSub V₀ V hV L).map (MulAut.conj α).toMonoidHom) =
      (commSub ⊤ (barSub V₀ V hV L)).map α.toMonoidHom := by
    have hh := s15_Kbar_commSub_map_conj (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) α
    have htop : (⊤ : Subgroup (Vtil V₀ V hV)).map α.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact α.surjective
    rwa [htop] at hh
  have hmap2 : commSub ((commSub ⊤ (barSub V₀ V hV L)).map α.toMonoidHom)
      ((barSub V₀ V hV (conjSubgroup L g)).map (MulAut.conj α).toMonoidHom) = ⊥ := by
    have hh := s15_Kbar_commSub_map_conj (commSub ⊤ (barSub V₀ V hV L))
      (barSub V₀ V hV (conjSubgroup L g)) α
    have hc2' : commSub (commSub ⊤ (barSub V₀ V hV L))
        (barSub V₀ V hV (conjSubgroup L g)) = ⊥ := by
      simpa [wTil] using hc2
    rw [hh, hc2', Subgroup.map_bot]
  exact ⟨h1, by rw [hKm, hKm', hmap1, hmap2]⟩

theorem s15_Kbar_eq_bot_of_normal_isPGroup (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {P : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hP : P ≤ Mbar D.M V₀ V h.isElemAbelian)
    (hN : (P.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal) (h2 : IsPGroup 2 P) :
    P = ⊥ := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  rcases h.1 with ⟨hW, h0⟩ | ⟨hV0, -, -⟩
  ·
    have hTR : TwoReduced D.M V := hW.1.2.2
    let K : Subgroup G := preBarSub D.M V₀ V hV P
    have hKM : K ≤ D.M := inf_le_left
    let ρ : ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
      ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)).codRestrict (Mbar D.M V₀ V hV)
        (fun x => actTil_mem_barSub V₀ V hV x.2 (hMs x.2))
    have hρ : K.subgroupOf D.M = (P.subgroupOf (Mbar D.M V₀ V hV)).comap ρ := by
      ext x
      rw [Subgroup.mem_subgroupOf, mem_preBarSub, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.2.2, fun h => ⟨x.2, hMs x.2, h⟩⟩
    have hK'M : (K.subgroupOf D.M).Normal := by
      rw [hρ]
      exact hN.comap ρ
    have hMnormK : D.M ≤ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hK'M
    have hCMK : D.M ⊓ centralizer (V : Set G) ≤ K := by
      rintro c ⟨hcM, hcc⟩
      rw [mem_preBarSub]
      refine ⟨hcM, hMs hcM, ?_⟩
      have hv : ∀ v ∈ V, (c : G) * v * (c : G)⁻¹ * v⁻¹ = 1 := by
        intro v hv'
        have hcomm : (c : G) * v = v * c :=
          (Subgroup.mem_centralizer_iff.mp hcc v hv').symm
        rw [show (c : G) * v * (c : G)⁻¹ = v by rw [hcomm]; group, mul_inv_cancel]
      rw [show actTil V₀ V hV ⟨c, hMs hcM⟩ = 1 from
        (actTil_eq_one_iff V₀ V hV ⟨c, hMs hcM⟩).2 fun v hv' =>
          s15_Kbar_mem_v0_of_eq_one h0 (hv v hv')]
      exact Subgroup.one_mem P
    have hKs : K ≤ stabTil V₀ V := hKM.trans hMs
    let ψK : ↥K →* MulAut (Vtil V₀ V hV) :=
      (actTil V₀ V hV).comp (Subgroup.inclusion hKs)
    have hψrange : ψK.range = P := by
      ext p
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨k, rfl⟩
        obtain ⟨h, hh⟩ := ((mem_preBarSub D.M V₀ V hV P).1 k.2).2
        exact hh
      · intro hp
        obtain ⟨g, hgM, hgp⟩ := (mem_barSub V₀ V hV D.M p).1 (hP hp)
        have hgK : (g : G) ∈ K := by
          rw [mem_preBarSub]
          exact ⟨hgM, g.2, hgp ▸ hp⟩
        refine ⟨⟨g.1, hgK⟩, ?_⟩
        show actTil V₀ V hV ⟨(g : G), hKs hgK⟩ = p
        rw [← hgp]
    have hψker : ψK.ker = (centralizer (V : Set G)).subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      constructor
      · intro hk v hv
        have h1 : (k : G) * v * (k : G)⁻¹ * v⁻¹ = 1 :=
          s15_Kbar_eq_one_of_mem_v0 h0
            ((actTil_eq_one_iff V₀ V hV ⟨(k : G), hKs k.2⟩).1 hk v hv)
        have h1' : ((k : G) * v * (k : G)⁻¹) * v⁻¹ = 1 := h1
        rw [mul_inv_eq_one] at h1'
        have h2 : (k : G) * v = v * (k : G) := by
          calc (k : G) * v = ((k : G) * v * (k : G)⁻¹) * (k : G) := by group
            _ = v * (k : G) := by rw [h1']
        rw [eq_comm]
        exact h2
      · intro hk
        apply (actTil_eq_one_iff V₀ V hV ⟨(k : G), hKs k.2⟩).2
        intro v hv
        have h2 : (k : G) * v = v * (k : G) := (hk v hv).symm
        have h1 : (k : G) * v * (k : G)⁻¹ * v⁻¹ = 1 := by
          rw [show (k : G) * v * (k : G)⁻¹ = v by rw [h2]; group, mul_inv_cancel]
        exact s15_Kbar_mem_v0_of_eq_one h0 h1
    have hidx2 : ∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 h2
      exact ⟨n, by rw [← hψker, Subgroup.index_ker, hψrange, hn]⟩
    have hKc : K ≤ centralizer (V : Set G) := hTR K hKM hMnormK hCMK hidx2
    rw [Subgroup.eq_bot_iff_forall]
    intro p hp
    obtain ⟨g, hgM, hgp⟩ := (mem_barSub V₀ V hV D.M p).1 (hP hp)
    have hgK : (g : G) ∈ K := by
      rw [mem_preBarSub]
      exact ⟨hgM, g.2, hgp ▸ hp⟩
    have hgc : (g : G) ∈ centralizer (V : Set G) := hKc hgK
    rw [← hgp]
    apply (actTil_eq_one_iff V₀ V hV g).2
    intro v hv
    have hcomm : (g : G) * v = v * (g : G) :=
      (Subgroup.mem_centralizer_iff.mp hgc v hv).symm
    have h1 : (g : G) * v * (g : G)⁻¹ * v⁻¹ = 1 := by
      rw [show (g : G) * v * (g : G)⁻¹ = v by rw [hcomm]; group, mul_inv_cancel]
    exact s15_Kbar_mem_v0_of_eq_one h0 h1
  ·
    obtain ⟨hVc₀, -, hle, hTI₀, hnTI, hgen, -⟩ := hV0
    by_contra hPne
    have hVne : V ≠ V₀ := by
      intro heq
      exact hnTI (heq ▸ hTI₀)
    have hnotle : ¬ V ≤ V₀ := fun hle' => hVne (le_antisymm hle' hle)
    obtain ⟨v, hvV, hv0⟩ := SetLike.not_le_iff_exists.1 hnotle
    have hvne : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ≠ 1 := by
      intro hh
      apply hv0
      have h1 : (IntMod.mk hV ⟨v, hvV⟩ : IntMod V hV).val ∈ V₀ := by
        have h1' : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) = mkTil V₀ V hV 1 := by
          rwa [map_one]
        rw [mkTil_eq_iff] at h1'
        simpa using h1'
      rw [show (IntMod.mk hV ⟨v, hvV⟩ : IntMod V hV).val = v from rfl] at h1
      exact h1
    have hUtne : (⊤ : Subgroup (Vtil V₀ V hV)) ≠ ⊥ := by
      intro htop
      have hv : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
          (⊥ : Subgroup (Vtil V₀ V hV)) := by
        rw [← htop]; exact Subgroup.mem_top _
      exact hvne (Subgroup.mem_bot.mp hv)
    obtain ⟨u, -, hu1, hufix⟩ := s15_Lin_exists_ne_one_mem_fixV h2
      (s15_Infra_vtil_sq_eq_one V₀ V hV) hUtne
      (fun x _ y _ => Subgroup.mem_top (x y))
    have hfixPinv := s15_Kbar_fixV_invariant h hP hN
    rcases s15_Kbar_irreducible h hVc₀.1 (fixV P) hfixPinv with hbot | htop
    · exact hu1 (Subgroup.mem_bot.mp (hbot ▸ hufix))
    · apply hPne
      rw [Subgroup.eq_bot_iff_forall]
      intro p hp
      ext w
      exact mem_fixV.mp (by rw [htop]; trivial) p hp

theorem s15_Kbar_fixV_eq_bot_of_ne_bot {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hYM : Y ≤ Mbar D.M V₀ V h.isElemAbelian)
    (hYn : (Y.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal) (hY : Y ≠ ⊥) :
    fixV Y = ⊥ := by
  have hinv := s15_Kbar_fixV_invariant h hYM hYn
  rcases s15_Kbar_irreducible h hV₀ (fixV Y) hinv with hbot | htop
  · exact hbot
  · exfalso
    apply hY
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    ext u
    exact mem_fixV.mp (by rw [htop]; trivial) y hy

theorem s15_Kbar_isSubnormal_barSub {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) :
    CFSG.Open.IsSubnormal (barSub V₀ V h.isElemAbelian L) (Mbar D.M V₀ V h.isElemAbelian) := by
  have hV := h.isElemAbelian
  let Y : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))
  have hYleM : Y ≤ Mbar D.M V₀ V hV := s15_Infra_iSup_barSub_le h
  have hYnorm : (Y.subgroupOf (Mbar D.M V₀ V hV)).Normal := s15_Infra_iSup_barSub_normal h
  have hYM : CFSG.Open.IsSubnormal Y (Mbar D.M V₀ V hV) :=
    CFSG.Open.IsSubnormal.step hYleM hYnorm (CFSG.Open.IsSubnormal.refl _)
  have hLY : barSub V₀ V hV L ≤ Y := by
    have h1 := le_iSup (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))) (1 : D.M)
    simpa [Y, conjSubgroup_one] using h1
  have hYnormL : Y ≤ normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    refine iSup_le fun m => ?_
    by_cases hm : (m : G) ∈ nBar D.M V₀ V hV L
    · rw [(s15_Infra_mem_nBar_iff h.hyp125 hV m.2).1 hm]
      exact Subgroup.le_normalizer
    · have hc := (h.commute (m : G) m.2 hm).1
      rw [Subgroup.commutator_comm] at hc
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
        (Subgroup.centralizer_le_normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
  have hLnormal : ((barSub V₀ V hV L).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).2 hYnormL
  exact CFSG.Open.IsSubnormal.trans
    (CFSG.Open.IsSubnormal.step hLY hLnormal (CFSG.Open.IsSubnormal.refl _)) hYM

private theorem s15_Kbar_iSup_map_conj_normal {A : Type*} [Group A] {K B : Subgroup A}
    (hKB : K ≤ B) :
    ((⨆ φ : B, K.map (MulAut.conj (φ : A)).toMonoidHom).subgroupOf B).Normal := by
  classical
  set X : Subgroup A := ⨆ φ : B, K.map (MulAut.conj (φ : A)).toMonoidHom with hX
  have hXB : X ≤ B := by
    refine iSup_le fun φ => ?_
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    exact B.mul_mem (B.mul_mem φ.2 (hKB hc)) (B.inv_mem φ.2)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXB]
  have hfwd : ∀ b ∈ B, ∀ x ∈ X, MulAut.conj b x ∈ X := by
    intro b hb x hx
    have hx' : x ∈ ⨆ φ : B, K.map (MulAut.conj (φ : A)).toMonoidHom := by
      rw [hX] at hx; exact hx
    refine Subgroup.iSup_induction (fun φ : B => K.map (MulAut.conj (φ : A)).toMonoidHom)
      (C := fun z => MulAut.conj b z ∈ X) hx' ?_ ?_ ?_
    · intro φ c hc
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hc
      have h1 : MulAut.conj b ((MulEquiv.toMonoidHom (MulAut.conj (φ : A))) d) =
          (MulEquiv.toMonoidHom (MulAut.conj (((⟨b * φ, B.mul_mem hb φ.2⟩ : B)) : A))) d := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h1]
      exact Subgroup.mem_iSup_of_mem ⟨b * φ, B.mul_mem hb φ.2⟩
        (Subgroup.mem_map_of_mem _ hd)
    · simp
    · intro x y hx hy
      rw [map_mul]
      exact X.mul_mem hx hy
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hfwd b hb x hx
  · intro hx
    have hb' : b⁻¹ ∈ B := B.inv_mem hb
    have h1 := hfwd b⁻¹ hb' (b * x * b⁻¹) hx
    rwa [show MulAut.conj b⁻¹ (b * x * b⁻¹) = x by
      simp only [MulAut.conj_apply]; group] at h1

theorem s15_Kbar_exists_shape (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    ∃ X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)),
      X ≠ ⊥ ∧ X ≤ (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) ∧
      X ≤ Mbar D.M V₀ V h.isElemAbelian ∧
      (X.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal ∧
      (Odd (Nat.card X) ∨ ∃ K ∈ compBar D.M V₀ V h.isElemAbelian,
        X = ⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian, K.map (MulAut.conj φ).toMonoidHom) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let Y : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))
  have hYleM : Y ≤ Mbar D.M V₀ V hV := s15_Infra_iSup_barSub_le h
  have hYnorm : (Y.subgroupOf (Mbar D.M V₀ V hV)).Normal := s15_Infra_iSup_barSub_normal h
  have hLbY : Lb ≤ Y := by
    have h1 := le_iSup (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))) (1 : D.M)
    simpa [Lb, Y, conjSubgroup_one] using h1
  have hLbM : Lb ≤ Mbar D.M V₀ V hV := hLbY.trans hYleM
  rcases s15_Lin_exists_component_or_isNilpotent (A := MulAut (Vtil V₀ V hV)) (H := Lb)
      h.fstar_eq with ⟨C, hC⟩ | hnil
  ·
    have hCne : C ≠ ⊥ := by
      intro hCbot
      haveI : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2
      haveI : Subsingleton (↥C ⧸ Subgroup.center ↥C) := by rw [hCbot]; infer_instance
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (↥C ⧸ Subgroup.center ↥C))
      exact hab (Subsingleton.elim a b)
    have hCM : CFSG.Open.IsComponentOf C (Mbar D.M V₀ V hV) := by
      refine ⟨hC.1.trans hLbM, ?_, hC.2.2⟩
      exact CFSG.Open.IsSubnormal.trans hC.2.1 (s15_Kbar_isSubnormal_barSub h)
    let X : Subgroup (MulAut (Vtil V₀ V hV)) :=
      ⨆ φ : Mbar D.M V₀ V hV, C.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom
    have hCX : C ≤ X := by
      have h1 := le_iSup (fun φ : Mbar D.M V₀ V hV =>
        C.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom) (1 : Mbar D.M V₀ V hV)
      have h2 : C.map (MulAut.conj ((1 : Mbar D.M V₀ V hV) :
          MulAut (Vtil V₀ V hV))).toMonoidHom = C := by
        rw [show ((1 : Mbar D.M V₀ V hV) : MulAut (Vtil V₀ V hV)) = 1 from rfl,
          map_one MulAut.conj]
        exact Subgroup.map_id C
      rwa [h2] at h1
    have hXne : X ≠ ⊥ := fun hXbot => hCne (le_bot_iff.mp (hCX.trans (le_of_eq hXbot)))
    have hXY : X ≤ Y := by
      refine iSup_le fun φ => ?_
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
      exact s15_Kbar_conj_mem_of_normal hYleM hYnorm φ.2 (hC.1.trans hLbY hc)
    have hXM : X ≤ Mbar D.M V₀ V hV := by
      refine iSup_le fun φ => ?_
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
      exact (Mbar D.M V₀ V hV).mul_mem
        ((Mbar D.M V₀ V hV).mul_mem φ.2 (hC.1.trans hLbM hc))
        ((Mbar D.M V₀ V hV).inv_mem φ.2)
    have hXnorm : (X.subgroupOf (Mbar D.M V₀ V hV)).Normal :=
      s15_Kbar_iSup_map_conj_normal (K := C) (B := Mbar D.M V₀ V hV) (hC.1.trans hLbM)
    refine ⟨X, hXne, hXY, hXM, hXnorm, Or.inr ⟨C, hCM, ?_⟩⟩
    exact iSup_subtype'' (Mbar D.M V₀ V hV : Set (MulAut (Vtil V₀ V hV)))
      (fun φ => C.map (MulAut.conj φ).toMonoidHom)
  ·
    have hoddL : Odd (Nat.card ↥Lb) :=
      s15_Lin_odd_card_of_isNilpotent hnil (s15_Kbar_no_two_quotient h)
    have hcard : ∀ m : D.M, Nat.card (barSub V₀ V hV (conjSubgroup L (m : G))) =
        Nat.card ↥Lb := by
      intro m
      have hm_st : (m : G) ∈ stabTil V₀ V := hMs m.2
      rw [s15_Infra_barSub_conjSubgroup V₀ V hV hm_st L]
      exact Subgroup.card_map_of_injective
        (f := (MulAut.conj (actTil V₀ V hV ⟨(m : G), hm_st⟩)⁻¹).toMonoidHom)
        (MulAut.conj (actTil V₀ V hV ⟨(m : G), hm_st⟩)⁻¹).injective
    have hodd : ∀ m : D.M, Odd (Nat.card (barSub V₀ V hV (conjSubgroup L (m : G)))) := by
      intro m
      rw [hcard m]
      exact hoddL
    have hcomm : ∀ m m' : D.M,
        barSub V₀ V hV (conjSubgroup L (m : G)) ≠
          barSub V₀ V hV (conjSubgroup L (m' : G)) →
        ∀ x ∈ barSub V₀ V hV (conjSubgroup L (m : G)),
        ∀ y ∈ barSub V₀ V hV (conjSubgroup L (m' : G)), Commute x y := by
      intro m m' hne x hx y hy
      have hne' : (m' : G) * (m : G)⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
        hne (((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m.2 m'.2).1 hmem).symm)
      have hc := (s15_Kbar_commute_conj h m.2 m'.2 hne').1
      have hmem : ⁅x, y⁆ ∈ ⁅barSub V₀ V hV (conjSubgroup L (m : G)),
          barSub V₀ V hV (conjSubgroup L (m' : G))⁆ :=
        Subgroup.commutator_mem_commutator hx hy
      rw [hc, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_commute.mp hmem
    have hoddY : Odd (Nat.card Y) :=
      s15_Lin_odd_card_iSup (A := MulAut (Vtil V₀ V hV))
        (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))) hodd hcomm
    have hYne : Y ≠ ⊥ := fun hYbot =>
      hL (le_bot_iff.mp (hLbY.trans (le_of_eq hYbot)))
    exact ⟨Y, hYne, le_rfl, hYleM, hYnorm, Or.inl hoddY⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
