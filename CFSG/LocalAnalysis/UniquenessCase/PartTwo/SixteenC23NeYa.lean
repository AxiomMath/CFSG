module

public import CFSG.GroupTheory.IndexFourQuotientKernel
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_ya_isPGroup {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) {K : Subgroup G} (hKM : K ≤ D.M)
    (hK2 : ∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n) :
    IsPGroup 2 ↥(barSub V₀ V hV K) := by
  classical
  have hKs : K ≤ stabTil V₀ V := hKM.trans hMs
  let ψ : ↥K →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hKs)
  have hrange : ψ.range = barSub V₀ V hV K := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨Subgroup.inclusion hKs k, ?_, rfl⟩
      simpa using k.2
    · rintro ⟨g, hg, hgφ⟩
      refine ⟨⟨(g : G), hg⟩, ?_⟩
      show actTil V₀ V hV (Subgroup.inclusion hKs ⟨(g : G), hg⟩) = φ
      rw [← hgφ, show Subgroup.inclusion hKs ⟨(g : G), hg⟩ = g from Subtype.ext rfl]
  have hker : ((centralizer (V : Set G)).subgroupOf K) ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply (actTil_eq_one_iff V₀ V hV ⟨(k : G), hKs k.2⟩).2
    intro v hv
    have hkv : (k : G) * v = v * (k : G) :=
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hk) v hv).symm
    rw [show (k : G) * v * (k : G)⁻¹ * v⁻¹ = 1 by rw [hkv]; group]
    exact V₀.one_mem
  obtain ⟨n, hn⟩ := hK2
  have hdvd : Nat.card ↥(barSub V₀ V hV K) ∣ 2 ^ n := by
    rw [← hrange, ← Subgroup.index_ker]
    exact hn ▸ Subgroup.index_dvd_of_le hker
  exact IsPGroup.of_card_dvd_pow hdvd

private theorem c23ne_ya_normal {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) {K : Subgroup G} (hKM : K ≤ D.M)
    (hKn : D.M ≤ normalizer (K : Set G)) :
    ((barSub V₀ V hV K).subgroupOf (Mbar D.M V₀ V hV)).Normal := by
  classical
  have hKb_le : barSub V₀ V hV K ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hKM
  have hKnx : ∀ n ∈ barSub V₀ V hV K, ∀ g ∈ Mbar D.M V₀ V hV,
      g * n * g⁻¹ ∈ barSub V₀ V hV K := by
    intro n hn g hg
    obtain ⟨g₀, hg₀K, hg₀n⟩ := (mem_barSub V₀ V hV K n).1 hn
    obtain ⟨m, hmM, hmg⟩ := (mem_barSub V₀ V hV D.M g).1 hg
    have hm_st : (m : G) ∈ stabTil V₀ V := hMs hmM
    have hconjK : (m : G) * (g₀ : G) * (m : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hKn hmM) (g₀ : G)).1 hg₀K
    have hconj_st : (m : G) * (g₀ : G) * (m : G)⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem hm_st g₀.2)
        ((stabTil V₀ V).inv_mem hm_st)
    have hEq : g * n * g⁻¹ = actTil V₀ V hV ⟨(m : G) * (g₀ : G) * (m : G)⁻¹, hconj_st⟩ := by
      rw [← hmg, ← hg₀n, ← map_mul, ← map_inv, ← map_mul]
      congr 1
    rw [hEq]
    exact actTil_mem_barSub V₀ V hV hconjK hconj_st
  exact (Subgroup.normal_subgroupOf_iff hKb_le).2 fun h k hh hk => hKnx h hh k hk

private theorem c23ne_ya_fixV_invariant {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) {K : Subgroup G} (hKM : K ≤ D.M)
    (hKn : D.M ≤ normalizer (K : Set G)) :
    ∀ φ ∈ Mbar D.M V₀ V hV, ∀ u ∈ fixV (barSub V₀ V hV K),
      φ u ∈ fixV (barSub V₀ V hV K) := by
  have hKb_le : barSub V₀ V hV K ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hKM
  have hKbN : ((barSub V₀ V hV K).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    c23ne_ya_normal hctx hMs hKM hKn
  have hKnx : ∀ n ∈ barSub V₀ V hV K, ∀ g ∈ Mbar D.M V₀ V hV,
      g * n * g⁻¹ ∈ barSub V₀ V hV K :=
    fun n hn g hg => (Subgroup.normal_subgroupOf_iff hKb_le).1 hKbN n g hn hg
  intro φ hφ u hu
  rw [mem_fixV] at hu ⊢
  intro k hk
  have hmem : φ⁻¹ * k * φ ∈ barSub V₀ V hV K := by
    have h := hKnx k hk φ⁻¹ ((Mbar D.M V₀ V hV).inv_mem hφ)
    simpa using h
  calc k (φ u) = (k * φ) u := rfl
    _ = (φ * (φ⁻¹ * k * φ)) u := by rw [show k * φ = φ * (φ⁻¹ * k * φ) by group]
    _ = φ ((φ⁻¹ * k * φ) u) := rfl
    _ = φ u := by rw [hu _ hmem]

private theorem c23ne_ya_swap {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) :
    ∃ φ ∈ Mbar D.M V₀ V hV,
      (wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV (conjSubgroup L x) ∧
        (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom = wTil V₀ V hV L := by
  classical
  have hxs : x ∈ stabTil V₀ V := hMs hctx.hxM
  have hαM : actTil V₀ V hV ⟨x, hxs⟩ ∈ Mbar D.M V₀ V hV :=
    actTil_mem_barSub V₀ V hV hctx.hxM hxs
  have hA : barSub V₀ V hV (conjSubgroup L x) =
      (barSub V₀ V hV L).map (MulAut.conj (actTil V₀ V hV ⟨x, hxs⟩)⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup V₀ V hV hxs L
  rcases hctx.core.perm (actTil V₀ V hV ⟨x, hxs⟩) hαM with hpres | hswap
  · exfalso
    have htriv : ∀ b ∈ barSub V₀ V hV (conjSubgroup L x),
        ∀ y ∈ wTil V₀ V hV (conjSubgroup L x),
          (b : MulAut (Vtil V₀ V hV)) y = y := by
      intro b hb y hy
      rw [hA] at hb
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.1 hb
      have hy' : actTil V₀ V hV ⟨x, hxs⟩ y ∈ wTil V₀ V hV (conjSubgroup L x) := by
        have hmem : actTil V₀ V hV ⟨x, hxs⟩ y ∈
            (wTil V₀ V hV (conjSubgroup L x)).map
              (actTil V₀ V hV ⟨x, hxs⟩).toMonoidHom :=
          Subgroup.mem_map_of_mem (actTil V₀ V hV ⟨x, hxs⟩).toMonoidHom hy
        rwa [hpres.2] at hmem
      rw [← haeq]
      change (MulAut.conj (actTil V₀ V hV ⟨x, hxs⟩)⁻¹ a) y = y
      rw [MulAut.conj_apply, inv_inv, MulAut.mul_apply, MulAut.mul_apply,
        hctx.core.triv₁ a ha (actTil V₀ V hV ⟨x, hxs⟩ y) hy', MulAut.inv_apply_self]
    have hA₂bot : barSub V₀ V hV (conjSubgroup L x) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro b hb
      ext u
      have hu : u ∈ wTil V₀ V hV L ⊔ wTil V₀ V hV (conjSubgroup L x) := by
        rw [hctx.core.sup_eq]
        trivial
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
      simp only [MulAut.one_apply]
      rw [map_mul, hctx.core.triv₂ b hb y hy, htriv b hb z hz]
    have hcard := hctx.core.card_A₂
    rw [hA₂bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exact ⟨actTil V₀ V hV ⟨x, hxs⟩, hαM, hswap.1, hswap.2⟩

private theorem c23ne_ya_barSub_eq_bot {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) {K : Subgroup G} (hKM : K ≤ D.M)
    (hKn : D.M ≤ normalizer (K : Set G))
    (hK2 : ∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n) :
    barSub V₀ V hV K = ⊥ := by
  classical
  have hKb2 : IsPGroup 2 ↥(barSub V₀ V hV K) := c23ne_ya_isPGroup hctx hMs hKM hK2
  have hUinv := c23ne_ya_fixV_invariant hctx hMs hKM hKn
  have hswap := c23ne_ya_swap hctx hMs
  have htop : (⊤ : Subgroup (Vtil V₀ V hV)) ≠ ⊥ := by
    intro h
    have hc : Nat.card (Vtil V₀ V hV) = 1 := by
      have hcard := congrArg (fun H : Subgroup (Vtil V₀ V hV) => Nat.card ↥H) h
      simpa [Subgroup.card_top, Subgroup.card_bot] using hcard
    rw [c23_core_card_top hctx.core] at hc
    norm_num at hc
  have hgen : ∃ v₀ ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)),
      v₀ ∈ fixV (barSub V₀ V hV K) := by
    obtain ⟨u, -, hu1, hufix⟩ := s15_Lin_exists_ne_one_mem_fixV hKb2
      (s15_Infra_vtil_sq_eq_one V₀ V hV) htop (fun _ _ y _ => Subgroup.mem_top y)
    by_cases huOm : u ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x))
    · exact ⟨u, huOm, hufix⟩
    · have hu' : u ∈ wTil V₀ V hV L ∨ u ∈ wTil V₀ V hV (conjSubgroup L x) := by
        simp only [c23Omega, Set.mem_setOf_eq] at huOm
        rcases not_and_or.mp huOm with h | h
        · exact Or.inl (not_not.mp h)
        · exact Or.inr (not_not.mp h)
      obtain ⟨φ, hφM, hφAB, hφBA⟩ := hswap
      have hφfix : φ u ∈ fixV (barSub V₀ V hV K) := hUinv φ hφM u hufix
      have hφne : φ u ≠ 1 := fun h => hu1 (φ.injective (by rw [h, map_one]))
      have hprod : u * φ u ∈ fixV (barSub V₀ V hV K) :=
        (fixV (barSub V₀ V hV K)).mul_mem hufix hφfix
      refine ⟨u * φ u, ?_, hprod⟩
      rw [c23Omega, Set.mem_setOf_eq]
      constructor
      · intro hmem
        rcases hu' with huA | huB
        · have hφB : φ u ∈ wTil V₀ V hV (conjSubgroup L x) := by
            have hmem' : φ u ∈ (wTil V₀ V hV L).map φ.toMonoidHom :=
              Subgroup.mem_map_of_mem φ.toMonoidHom huA
            rwa [hφAB] at hmem'
          have hφA : φ u ∈ wTil V₀ V hV L := by
            have h := (wTil V₀ V hV L).mul_mem ((wTil V₀ V hV L).inv_mem huA) hmem
            simpa using h
          have h1 : φ u ∈ wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) := ⟨hφA, hφB⟩
          rw [hctx.core.inf_eq, Subgroup.mem_bot] at h1
          exact hφne h1
        · have hφA : φ u ∈ wTil V₀ V hV L := by
            have hmem' : φ u ∈ (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom :=
              Subgroup.mem_map_of_mem φ.toMonoidHom huB
            rwa [hφBA] at hmem'
          have huA : u ∈ wTil V₀ V hV L := by
            have h := (wTil V₀ V hV L).mul_mem hmem ((wTil V₀ V hV L).inv_mem hφA)
            simpa using h
          have h1 : u ∈ wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) := ⟨huA, huB⟩
          rw [hctx.core.inf_eq, Subgroup.mem_bot] at h1
          exact hu1 h1
      · intro hmem
        rcases hu' with huA | huB
        · have hφB : φ u ∈ wTil V₀ V hV (conjSubgroup L x) := by
            have hmem' : φ u ∈ (wTil V₀ V hV L).map φ.toMonoidHom :=
              Subgroup.mem_map_of_mem φ.toMonoidHom huA
            rwa [hφAB] at hmem'
          have huB : u ∈ wTil V₀ V hV (conjSubgroup L x) := by
            have h := (wTil V₀ V hV (conjSubgroup L x)).mul_mem hmem
              ((wTil V₀ V hV (conjSubgroup L x)).inv_mem hφB)
            simpa using h
          have h1 : u ∈ wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) := ⟨huA, huB⟩
          rw [hctx.core.inf_eq, Subgroup.mem_bot] at h1
          exact hu1 h1
        · have hφA : φ u ∈ wTil V₀ V hV L := by
            have hmem' : φ u ∈ (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom :=
              Subgroup.mem_map_of_mem φ.toMonoidHom huB
            rwa [hφBA] at hmem'
          have hφB : φ u ∈ wTil V₀ V hV (conjSubgroup L x) := by
            have h := (wTil V₀ V hV (conjSubgroup L x)).mul_mem
              ((wTil V₀ V hV (conjSubgroup L x)).inv_mem huB) hmem
            simpa using h
          have h1 : φ u ∈ wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) := ⟨hφA, hφB⟩
          rw [hctx.core.inf_eq, Subgroup.mem_bot] at h1
          exact hφne h1
  have hOm : ∀ u ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)),
      u ∈ fixV (barSub V₀ V hV K) := by
    obtain ⟨v₀, hv₀Ω, hv₀U⟩ := hgen
    intro u hu
    obtain ⟨a, ha, b, hb, hab⟩ := c23_omega_trans hctx.core hv₀Ω hu
    have habM : a * b ∈ Mbar D.M V₀ V hV :=
      (Mbar D.M V₀ V hV).mul_mem (hctx.core.le₁ ha) (hctx.core.le₂ hb)
    have h1 : (a * b) v₀ ∈ fixV (barSub V₀ V hV K) := hUinv (a * b) habM v₀ hv₀U
    have h2 : (a * b) v₀ = u := by rw [MulAut.mul_apply]; exact hab
    rwa [h2] at h1
  have hcardA : Nat.card ↥(wTil V₀ V hV L) = 8 := hctx.core.card₁
  have hcardB : Nat.card ↥(wTil V₀ V hV (conjSubgroup L x)) = 8 := hctx.core.card₂
  have hexA : ∃ y ∈ wTil V₀ V hV L, y ≠ 1 := by
    have hne : wTil V₀ V hV L ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcardA
      norm_num at hcardA
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨(y : Vtil V₀ V hV), y.2, fun h => hy1 (Subtype.ext h)⟩
  have hexB : ∃ z ∈ wTil V₀ V hV (conjSubgroup L x), z ≠ 1 := by
    have hne : wTil V₀ V hV (conjSubgroup L x) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcardB
      norm_num at hcardB
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨(z : Vtil V₀ V hV), z.2, fun h => hz1 (Subtype.ext h)⟩
  have hexA_avoid : ∀ w ∈ wTil V₀ V hV L, w ≠ 1 →
      ∃ y ∈ wTil V₀ V hV L, y ≠ 1 ∧ y ≠ w := by
    intro w hw _
    have h2 : ({1, w} : Set (Vtil V₀ V hV)).ncard <
        (wTil V₀ V hV L : Set (Vtil V₀ V hV)).ncard := by
      have hle : ({1, w} : Set (Vtil V₀ V hV)).ncard ≤ 2 := by
        rcases eq_or_ne (1 : Vtil V₀ V hV) w with h | h
        · rw [h]; simp
        · exact le_of_eq (Set.ncard_pair h)
      have hcard : (wTil V₀ V hV L : Set (Vtil V₀ V hV)).ncard = 8 := by
        rw [← Nat.card_coe_set_eq]
        exact hcardA
      rw [hcard]
      omega
    obtain ⟨y, hyA, hy_not⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h2
    exact ⟨y, hyA,
      fun h => hy_not (by rw [h]; exact Set.mem_insert _ _),
      fun h => hy_not (by rw [h]; exact Set.mem_insert_of_mem _ rfl)⟩
  have hgenOm : ∀ y' ∈ wTil V₀ V hV L, y' ≠ 1 →
      ∀ z' ∈ wTil V₀ V hV (conjSubgroup L x), z' ≠ 1 →
        y' * z' ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) := by
    intro y' hy'A hy'1 z' hz'B hz'1
    rw [c23Omega, Set.mem_setOf_eq]
    constructor
    · intro hmem
      have hz'A : z' ∈ wTil V₀ V hV L := by
        have h := (wTil V₀ V hV L).mul_mem ((wTil V₀ V hV L).inv_mem hy'A) hmem
        simpa using h
      have h1 : z' ∈ wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) := ⟨hz'A, hz'B⟩
      rw [hctx.core.inf_eq, Subgroup.mem_bot] at h1
      exact hz'1 h1
    · intro hmem
      have hy'B : y' ∈ wTil V₀ V hV (conjSubgroup L x) := by
        have h := (wTil V₀ V hV (conjSubgroup L x)).mul_mem hmem
          ((wTil V₀ V hV (conjSubgroup L x)).inv_mem hz'B)
        simpa using h
      have h1 : y' ∈ wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) := ⟨hy'A, hy'B⟩
      rw [hctx.core.inf_eq, Subgroup.mem_bot] at h1
      exact hy'1 h1
  have hY₁ : wTil V₀ V hV L ≤ fixV (barSub V₀ V hV K) := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]; exact (fixV (barSub V₀ V hV K)).one_mem
    · obtain ⟨z, hzB, hz1⟩ := hexB
      obtain ⟨y, hyA, hy1, hyw⟩ := hexA_avoid w hw hw1
      have hy'1 : y * w ≠ 1 := by
        intro h
        apply hyw
        have hw2 : w * w = 1 := by
          simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV w
        calc y = y * 1 := (mul_one y).symm
          _ = y * (w * w) := by rw [hw2]
          _ = y * w * w := by rw [mul_assoc]
          _ = w := by rw [h, one_mul]
      have h1 : y * z ∈ fixV (barSub V₀ V hV K) := hOm (y * z) (hgenOm y hyA hy1 z hzB hz1)
      have h2 : (y * w) * z ∈ fixV (barSub V₀ V hV K) :=
        hOm ((y * w) * z) (hgenOm (y * w) ((wTil V₀ V hV L).mul_mem hyA hw) hy'1 z hzB hz1)
      have h3 : (y * z) * ((y * w) * z) ∈ fixV (barSub V₀ V hV K) :=
        (fixV (barSub V₀ V hV K)).mul_mem h1 h2
      have hw2 : w * w = 1 := by
        simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV w
      have hzy : (y * z) * ((y * w) * z) = w := by
        have hy2 : y * y = 1 := by
          simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV y
        have hz2 : z * z = 1 := by
          simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV z
        calc (y * z) * ((y * w) * z)
            = (y * z) * (y * z) * w := by ac_rfl
          _ = (y * y) * (z * z) * w := by ac_rfl
          _ = w := by rw [hy2, hz2]; simp
      rwa [hzy] at h3
  have hY₂ : wTil V₀ V hV (conjSubgroup L x) ≤ fixV (barSub V₀ V hV K) := by
    intro z' hz'B
    by_cases hz'1 : z' = 1
    · rw [hz'1]; exact (fixV (barSub V₀ V hV K)).one_mem
    · obtain ⟨y, hyA, hy1⟩ := hexA
      have hyz : y * z' ∈ fixV (barSub V₀ V hV K) := hOm (y * z') (hgenOm y hyA hy1 z' hz'B hz'1)
      have hyU : y ∈ fixV (barSub V₀ V hV K) := hY₁ hyA
      have h3 : y⁻¹ * (y * z') ∈ fixV (barSub V₀ V hV K) :=
        (fixV (barSub V₀ V hV K)).mul_mem ((fixV (barSub V₀ V hV K)).inv_mem hyU) hyz
      rwa [show y⁻¹ * (y * z') = z' by group] at h3
  have hfix : fixV (barSub V₀ V hV K) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hctx.core.sup_eq]
    exact sup_le hY₁ hY₂
  rw [Subgroup.eq_bot_iff_forall]
  intro φ hφ
  ext u
  exact (mem_fixV.mp (by rw [hfix]; trivial : u ∈ fixV (barSub V₀ V hV K))) φ hφ

theorem c23ne_normal_two_le_cTilde {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) {K : Subgroup G} (hKM : K ≤ D.M)
    (hKn : D.M ≤ normalizer (K : Set G))
    (hK2 : ∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n) :
    K ≤ F11.CTilde D.M V₀ V := by
  have hKb : barSub V₀ V hV K = ⊥ := c23ne_ya_barSub_eq_bot hctx hMs hKM hKn hK2
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hKs : K ≤ stabTil V₀ V := hKM.trans hMs
  intro k hk
  refine (mem_cTilde_iff hV hM).2 ⟨hKM hk, hKs hk, ?_⟩
  have hmem : actTil V₀ V hV ⟨k, hKs hk⟩ ∈ barSub V₀ V hV K :=
    actTil_mem_barSub V₀ V hV hk (hKs hk)
  rw [hKb, Subgroup.mem_bot] at hmem
  exact hmem

theorem c23ne_exists_q0 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) (hsmall : mSub V₀ ≤ 2) (h0 : InCalV0 D.M V₀ V) :
    ∃ q ∈ F11.CTilde D.M V₀ V ⊓ centralizer (V₀ : Set G), ¬ V ≤ centralizer ({q} : Set G) := by
  classical
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := fun g hg => (hMs hg).2
  obtain ⟨hV₀cal, hVcal, hV₀V, hTI0, hnotTI, hgenV, hnotTR⟩ := h0
  obtain ⟨hV₀ne, hV₀M, hMnormV₀, hV₀E⟩ := hV₀cal
  have hV₀p : IsPGroup 2 ↥V₀ := fun g => ⟨1, Subtype.ext (by
    simpa using hV₀E.2 (g : G) g.2)⟩
  have hV₀card : Nat.card ↥V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV₀p
  have hm1 : 1 ≤ mSub V₀ := by
    have hlt : 1 < Nat.card ↥V₀ := (Subgroup.one_lt_card_iff_ne_bot V₀).2 hV₀ne
    rw [hV₀card] at hlt
    by_contra h
    rw [show mSub V₀ = 0 by omega, pow_zero] at hlt
    omega
  have hm2 : mSub V₀ ≤ 2 := hsmall
  have hV0card_cases : Nat.card ↥V₀ = 2 ∨ Nat.card ↥V₀ = 4 := by
    rcases (show mSub V₀ = 1 ∨ mSub V₀ = 2 by omega) with hm | hm
    · left; rw [hV₀card, hm]; norm_num
    · right; rw [hV₀card, hm]; norm_num
  have hnotTR' : ∃ K : Subgroup G, ∃ (_ : K ≤ D.M), ∃ (_ : D.M ≤ normalizer (K : Set G)),
      ∃ (_ : D.M ⊓ centralizer (V : Set G) ≤ K),
      ∃ (_ : ∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n),
      ¬ K ≤ centralizer (V : Set G) := by
    unfold TwoReduced at hnotTR
    simpa only [not_forall, not_imp, not_exists] using hnotTR
  obtain ⟨K, hKM, hKn, hCVK, hK2, hKnotC⟩ := hnotTR'
  have hKct : K ≤ F11.CTilde D.M V₀ V := c23ne_normal_two_le_cTilde hctx hMs hKM hKn hK2
  by_contra hcon
  have hcon' : ∀ q ∈ F11.CTilde D.M V₀ V ⊓ centralizer (V₀ : Set G),
      V ≤ centralizer ({q} : Set G) := by
    intro q hq
    by_contra hqV
    exact hcon ⟨q, hq, hqV⟩
  have hK0 : (centralizer (V₀ : Set G)).subgroupOf K = (centralizer (V : Set G)).subgroupOf K := by
    refine le_antisymm ?_ ?_
    · intro k hk
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hkC : (k : G) ∈ F11.CTilde D.M V₀ V := hKct k.2
      have hVk : V ≤ centralizer ({(k : G)} : Set G) := hcon' (k : G) ⟨hkC, hk⟩
      exact (Subgroup.mem_centralizer_iff.1 (hVk hv) (k : G) (Set.mem_singleton _)).symm
    · intro k hk
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.1 hk v (hV₀V hv)
  obtain ⟨n, hn⟩ := hK2
  have hK0index : ((centralizer (V₀ : Set G)).subgroupOf K).index = 2 ^ n := by
    rw [hK0]; exact hn
  have hK0ne : ((centralizer (V₀ : Set G)).subgroupOf K) ≠ ⊤ := by
    intro htop
    apply hKnotC
    intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ (centralizer (V : Set G)).subgroupOf K := by
      rw [← hK0, htop]; trivial
    exact Subgroup.mem_subgroupOf.1 hk'
  have hK0index_ne1 : ((centralizer (V₀ : Set G)).subgroupOf K).index ≠ 1 := by
    intro h1
    exact hK0ne (Subgroup.index_eq_one.mp h1)
  have hAutdvd : Nat.card (MulAut ↥V₀) ∣ 6 := by
    rcases hV0card_cases with hc | hc
    · have h1 : Nat.card (MulAut ↥V₀) ∣ Nat.card (Equiv.Perm ↥V₀) := by
        refine Subgroup.card_dvd_of_injective
          { toFun := fun e => e.toEquiv, map_one' := rfl, map_mul' := fun a b => rfl } ?_
        intro a b h
        apply MulEquiv.ext
        intro x
        exact congrArg (fun e : Equiv.Perm ↥V₀ => e x) h
      rw [Nat.card_perm, hc] at h1
      norm_num at h1
      exact h1.trans (by norm_num : 2 ∣ 6)
    · exact CFSG.GroupTheory.card_mulAut_dvd_six_of_card_eq_four hc
  let φ : ↥K →* MulAut ↥V₀ := V₀.normalizerMonoidHom.comp (Subgroup.inclusion (hKM.trans hM₀))
  have hφker : φ.ker = (centralizer (V₀ : Set G)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h v hv
      have h1 := congrArg (fun f : MulAut ↥V₀ => ((f ⟨v, hv⟩ : ↥V₀) : G)) h
      simp only [MulAut.one_apply] at h1
      change ((V₀.normalizerMonoidHom (Subgroup.inclusion (hKM.trans hM₀) k) ⟨v, hv⟩ : ↥V₀) : G)
        = v at h1
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      have h1' : (k : G) * v * (k : G)⁻¹ = v := by simpa using h1
      have h2 : (k : G) * v = v * (k : G) := by
        calc (k : G) * v = ((k : G) * v * (k : G)⁻¹) * (k : G) := by group
          _ = v * (k : G) := by rw [h1']
      exact h2.symm
    · intro h
      ext x
      rw [MulAut.one_apply]
      change ((V₀.normalizerMonoidHom (Subgroup.inclusion (hKM.trans hM₀) k) x : ↥V₀) : G) = (x : G)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hx := h (x : G) x.2
      change (k : G) * (x : G) * (k : G)⁻¹ = (x : G)
      rw [← hx]; group
  have hindex_dvd : ((centralizer (V₀ : Set G)).subgroupOf K).index ∣ 6 := by
    rw [← hφker, Subgroup.index_ker]
    exact (Subgroup.card_subgroup_dvd_card φ.range).trans hAutdvd
  have hindex2 : ((centralizer (V₀ : Set G)).subgroupOf K).index = 2 := by
    have hdvd : 2 ^ n ∣ 6 := by rw [← hK0index]; exact hindex_dvd
    have hne1 : 2 ^ n ≠ 1 := by rw [← hK0index]; exact hK0index_ne1
    have hnle : n ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ n := by omega
      have h8 : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      have hle6 : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases n
    · exact absurd (by rw [pow_zero]) hne1
    · rw [hK0index, pow_one]
    · norm_num at hdvd
  have ht_ex : ∃ t : ↥K, t ∉ (centralizer (V₀ : Set G)).subgroupOf K := by
    by_contra h
    apply hK0ne
    rw [eq_top_iff]
    intro t _
    by_contra ht
    exact h ⟨t, ht⟩
  obtain ⟨t, htC⟩ := ht_ex
  have htV₀ : (t : G) ∉ centralizer (V₀ : Set G) := fun h => htC (Subgroup.mem_subgroupOf.2 h)
  have htVK : t ∉ (centralizer (V : Set G)).subgroupOf K := by
    intro h
    apply htC
    rw [hK0]
    exact h
  have htV : (t : G) ∉ centralizer (V : Set G) := fun h => htVK (Subgroup.mem_subgroupOf.2 h)
  have ht2V : (t : G) ^ 2 ∈ centralizer (V : Set G) := by
    have := Subgroup.sq_mem_of_index_two hindex2 t
    rw [hK0] at this
    exact Subgroup.mem_subgroupOf.1 this
  have hcmemV : ∀ w ∈ V, ⁅(t : G), w⁆ ∈ V := by
    intro w hw
    have htN : (t : G) ∈ normalizer (V : Set G) := (hMs (hKM t.2)).1
    have h1 : (t : G) * w * (t : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 htN w).1 hw
    change ((t : G) * w * (t : G)⁻¹) * w⁻¹ ∈ V
    exact V.mul_mem h1 (V.inv_mem hw)
  have htcomm : ∀ v ∈ V, ⁅(t : G), v⁆ ∈ V₀ := by
    intro v hv
    obtain ⟨-, h, hh⟩ := (mem_cTilde_iff hV hM).1 (hKct t.2)
    have h1 := (actTil_eq_one_iff V₀ V hV ⟨(t : G), h⟩).1 hh v hv
    simpa only [commutatorElement_def] using h1
  let CVt : Subgroup G := V ⊓ centralizer ({(t : G)} : Set G)
  have htwt : ∀ v : ↥V, (t : G) * ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) * (t : G)⁻¹ =
      (t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹ := by
    intro v
    have hc : (t : G) * (t : G) * (v : G) = (v : G) * ((t : G) * (t : G)) := by
      simpa [pow_two] using (Subgroup.mem_centralizer_iff.1 ht2V (v : G) v.2).symm
    have h1 : (t : G) * (t : G) * (v : G) * ((t : G) * (t : G))⁻¹ = (v : G) := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : ((t : G) * ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) * (t : G)⁻¹) *
        ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) * (v : G) =
        (t : G) * (t : G) * (v : G) * ((t : G) * (t : G))⁻¹ := by
      group
    have h3 : ((t : G) * ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) * (t : G)⁻¹) *
        ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) = 1 := by
      have h4 : ((t : G) * ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) * (t : G)⁻¹) *
          ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) * (v : G) = 1 * (v : G) := by
        rw [one_mul, h2, h1]
      exact mul_right_cancel h4
    have hww : ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) *
        ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) = 1 := by
      have := hV.2 ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) (hcmemV (v : G) v.2)
      simpa [pow_two] using this
    have h3inv : ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹)⁻¹ =
        (t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹ := (eq_inv_of_mul_eq_one_left hww).symm
    rw [eq_inv_of_mul_eq_one_left h3]
    exact h3inv
  have hCV0_proper : V₀ ⊓ centralizer ({(t : G)} : Set G) ≠ V₀ := by
    intro h
    apply htV₀
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ V₀ ⊓ centralizer ({(t : G)} : Set G) := (le_of_eq h.symm) hv
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hv').2 (t : G)
      (Set.mem_singleton _)).symm
  have hCV0_le_two : Nat.card ↥(V₀ ⊓ centralizer ({(t : G)} : Set G)) ≤ 2 := by
    have hdvd : Nat.card ↥(V₀ ⊓ centralizer ({(t : G)} : Set G)) ∣ Nat.card ↥V₀ :=
      Subgroup.card_dvd_of_le inf_le_left
    have hlt : Nat.card ↥(V₀ ⊓ centralizer ({(t : G)} : Set G)) < Nat.card ↥V₀ :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left hCV0_proper)
    rcases hV0card_cases with hc | hc
    · rw [hc] at hlt; omega
    · rw [hc] at hdvd
      have hdvd' : Nat.card ↥(V₀ ⊓ centralizer ({(t : G)} : Set G)) ∣ 2 ^ 2 := by
        rwa [show (2 : ℕ) ^ 2 = 4 by norm_num]
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd' with ⟨j, hj, hjeq⟩
      rw [hjeq] at hlt ⊢
      interval_cases j
      · norm_num
      · norm_num
      · exfalso; rw [hc] at hlt; norm_num at hlt
  let δ : ↥V →* ↥V :=
    { toFun := fun v => ⟨⁅(t : G), (v : G)⁆, hcmemV (v : G) v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro u v
        apply Subtype.ext
        change ⁅(t : G), (u : G) * (v : G)⁆ = ⁅(t : G), (u : G)⁆ * ⁅(t : G), (v : G)⁆
        have hcomm : (u : G) * ⁅(t : G), (v : G)⁆ = ⁅(t : G), (v : G)⁆ * (u : G) :=
          congrArg (fun z : ↥V => (z : G)) (hV.1.is_comm.comm ⟨(u : G), u.2⟩
            ⟨⁅(t : G), (v : G)⁆, hcmemV (v : G) v.2⟩)
        rw [commutatorElement_mul_right_eq_mul_conj,
          show ⁅(t : G), (u : G)⁆ * (u : G) * ⁅(t : G), (v : G)⁆ * (u : G)⁻¹ =
            ⁅(t : G), (u : G)⁆ * ((u : G) * ⁅(t : G), (v : G)⁆) * (u : G)⁻¹ by group,
          hcomm]
        group }
  have hδker : δ.ker = CVt.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ⁅(t : G), (v : G)⁆ = 1 := by
        exact congrArg (fun z : ↥V => (z : G)) h
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      refine ⟨v.2, ?_⟩
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h2 : (t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹ = 1 := by
        simpa only [commutatorElement_def] using h1
      rw [mul_inv_eq_one] at h2
      exact (calc (t : G) * (v : G) = ((t : G) * (v : G) * (t : G)⁻¹) * (t : G) := by group
        _ = (v : G) * (t : G) := by rw [h2])
    · intro hv
      obtain ⟨-, hc⟩ := Subgroup.mem_inf.1 hv
      rw [Subgroup.mem_centralizer_iff] at hc
      apply Subtype.ext
      change ⁅(t : G), (v : G)⁆ = (1 : G)
      have h1 : (t : G) * (v : G) = (v : G) * (t : G) := hc (t : G) (Set.mem_singleton _)
      rw [commutatorElement_def, h1]; group
  have hδrange_V0 : δ.range ≤ (V₀ ⊓ centralizer ({(t : G)} : Set G)).subgroupOf V := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨v, rfl⟩ := hx
    rw [Subgroup.mem_subgroupOf]
    change ⁅(t : G), (v : G)⁆ ∈ V₀ ⊓ centralizer ({(t : G)} : Set G)
    rw [Subgroup.mem_inf]
    refine ⟨htcomm (v : G) v.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have h1 := htwt v
    have h2 : (t : G) * ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) =
        ((t : G) * (v : G) * (t : G)⁻¹ * (v : G)⁻¹) * (t : G) := by
      have := congrArg (fun z => z * (t : G)) h1
      simpa [mul_assoc] using this
    show (t : G) * ⁅(t : G), (v : G)⁆ = ⁅(t : G), (v : G)⁆ * (t : G)
    exact h2
  have hδindex_le : (CVt.subgroupOf V).index ≤ 2 := by
    rw [← hδker, Subgroup.index_ker]
    calc Nat.card δ.range
        ≤ Nat.card ↥((V₀ ⊓ centralizer ({(t : G)} : Set G)).subgroupOf V) :=
          Subgroup.card_le_of_le hδrange_V0
      _ = Nat.card ↥(V₀ ⊓ centralizer ({(t : G)} : Set G)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            ((inf_le_left : V₀ ⊓ centralizer ({(t : G)} : Set G) ≤ V₀).trans hV₀V)).toEquiv
      _ ≤ 2 := hCV0_le_two
  have hCVt_ne_top : CVt.subgroupOf V ≠ ⊤ := by
    intro htop
    apply htV
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ CVt := by
      have : (⟨v, hv⟩ : ↥V) ∈ CVt.subgroupOf V := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hv').2 (t : G)
      (Set.mem_singleton _)).symm
  have hCVt_index2 : (CVt.subgroupOf V).index = 2 := by
    have hne : (CVt.subgroupOf V).index ≠ 1 := fun h1 =>
      hCVt_ne_top (Subgroup.index_eq_one.mp h1)
    have h0 : (CVt.subgroupOf V).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hMinv : ∀ m ∈ D.M, ∀ v ∈ CVt, (m : G) * v * (m : G)⁻¹ ∈ CVt := by
    intro m hm v hv
    obtain ⟨hvV, hvt⟩ := Subgroup.mem_inf.1 hv
    rw [Subgroup.mem_centralizer_iff] at hvt
    have htm : (m : G) * (t : G) * (m : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hKn hm) (t : G)).1 t.2
    have hbK : (⟨(m : G) * (t : G) * (m : G)⁻¹, htm⟩ : ↥K) ∉
        (centralizer (V : Set G)).subgroupOf K := by
      intro hb
      apply htV
      have hb' := Subgroup.mem_subgroupOf.1 hb
      rw [Subgroup.mem_centralizer_iff] at hb' ⊢
      intro u hu
      have hu' : (m : G) * u * (m : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hM hm) u).1 hu
      have h1 := hb' ((m : G) * u * (m : G)⁻¹) hu'
      have h2 := congrArg (fun z => (m : G)⁻¹ * z * (m : G)) h1
      rw [show (m : G)⁻¹ * (((m : G) * u * (m : G)⁻¹) * ((m : G) * (t : G) * (m : G)⁻¹)) *
            (m : G) = u * (t : G) by group,
        show (m : G)⁻¹ * (((m : G) * (t : G) * (m : G)⁻¹) * ((m : G) * u * (m : G)⁻¹)) *
            (m : G) = (t : G) * u by group] at h2
      exact h2
    have hbC : (⟨(m : G) * (t : G) * (m : G)⁻¹, htm⟩ : ↥K) * t⁻¹ ∈
        (centralizer (V : Set G)).subgroupOf K := by
      rw [Subgroup.mul_mem_iff_of_index_two (by rw [← hK0]; exact hindex2)]
      exact ⟨fun hb => absurd hb hbK, fun ht => False.elim (htVK (by
        simpa using ((centralizer (V : Set G)).subgroupOf K).inv_mem ht))⟩
    set c : ↥K := (⟨(m : G) * (t : G) * (m : G)⁻¹, htm⟩ : ↥K) * t⁻¹ with hc_def
    have hcV : (c : G) ∈ centralizer (V : Set G) := Subgroup.mem_subgroupOf.1 hbC
    have hmt : (m : G) * (t : G) * (m : G)⁻¹ = (c : G) * (t : G) := by
      have hmtK : (⟨(m : G) * (t : G) * (m : G)⁻¹, htm⟩ : ↥K) = c * t := by
        rw [hc_def]; group
      have := congrArg (fun z : ↥K => (z : G)) hmtK
      simpa using this
    rw [Subgroup.mem_inf]
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hM hm) v).1 hvV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hmvV : (m : G) * v * (m : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hM hm) v).1 hvV
    have hcommcv : (c : G) * ((m : G) * v * (m : G)⁻¹) =
        ((m : G) * v * (m : G)⁻¹) * (c : G) :=
      (Subgroup.mem_centralizer_iff.1 hcV ((m : G) * v * (m : G)⁻¹) hmvV).symm
    have hconj : ((m : G) * v * (m : G)⁻¹) * ((m : G) * (t : G) * (m : G)⁻¹) =
        ((m : G) * (t : G) * (m : G)⁻¹) * ((m : G) * v * (m : G)⁻¹) := by
      have h1 := congrArg (fun z : G => (m : G) * z * (m : G)⁻¹)
        ((hvt (t : G) (Set.mem_singleton _)).symm)
      rwa [show (m : G) * (v * (t : G)) * (m : G)⁻¹ =
            ((m : G) * v * (m : G)⁻¹) * ((m : G) * (t : G) * (m : G)⁻¹) by group,
          show (m : G) * ((t : G) * v) * (m : G)⁻¹ =
            ((m : G) * (t : G) * (m : G)⁻¹) * ((m : G) * v * (m : G)⁻¹) by group] at h1
    rw [hmt] at hconj
    have h1 : (c : G) * (((m : G) * v * (m : G)⁻¹) * (t : G)) =
        (c : G) * ((t : G) * ((m : G) * v * (m : G)⁻¹)) := by
      rw [show ((m : G) * v * (m : G)⁻¹) * ((c : G) * (t : G)) =
            (c : G) * (((m : G) * v * (m : G)⁻¹) * (t : G)) by
              rw [← mul_assoc, ← hcommcv, mul_assoc],
          show ((c : G) * (t : G)) * ((m : G) * v * (m : G)⁻¹) =
            (c : G) * ((t : G) * ((m : G) * v * (m : G)⁻¹)) by group] at hconj
      exact hconj
    exact (mul_left_cancel h1).symm
  have hCVt_not_le_V₀ : ¬ CVt ≤ V₀ := by
    intro hle
    have hdvd : (V₀.subgroupOf V).index ∣ (CVt.subgroupOf V).index :=
      Subgroup.index_dvd_of_le (by
        intro x hx
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hle hx)
    have hV₀index : (V₀.subgroupOf V).index = 64 := by
      show Nat.card (Vtil V₀ V hV) = 64
      exact c23_core_card_top hctx.core
    rw [hCVt_index2, hV₀index] at hdvd
    norm_num at hdvd
  obtain ⟨v, hvCVt, hvV0⟩ := SetLike.not_le_iff_exists.1 hCVt_not_le_V₀
  have hvV : v ∈ V := (Subgroup.mem_inf.1 hvCVt).1
  have hclosure_le : Subgroup.closure {x : G | ∃ m ∈ D.M, x = m * v * m⁻¹} ≤ CVt := by
    rw [Subgroup.closure_le]
    rintro x ⟨m, hm, rfl⟩
    exact hMinv m hm v hvCVt
  have hVle : V ≤ CVt := hgenV v hvV hvV0 ▸ hclosure_le
  exact hCVt_ne_top (by
    rw [show CVt = V from le_antisymm inf_le_left hVle]
    exact Subgroup.subgroupOf_self V)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
