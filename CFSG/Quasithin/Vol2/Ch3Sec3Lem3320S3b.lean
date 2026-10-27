module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S3a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_odd {B K : Subgroup G} (h2 : (conjSubgroupsBy B K).ncard = 2) {b : G}
    (hb : b ∈ B) (hodd : Odd (orderOf b)) : b ∈ Subgroup.normalizer (K : Set G) := by
  have hmem : ∀ g ∈ B, K.map (MulAut.conj g).toMonoidHom ∈ conjSubgroupsBy B K :=
    fun g hg => ⟨g, hg, rfl⟩
  have hK1 : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
    rw [map_one]
    exact Subgroup.map_id K
  have hsq : ∀ g : G, K.map (MulAut.conj (g * g)).toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    intro g
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hcases : b ∈ Subgroup.normalizer (K : Set G) ∨
      b * b ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2'⟩ := hcon
    have h3 : K.map (MulAut.conj b).toMonoidHom ≠ K.map (MulAut.conj (b * b)).toMonoidHom := by
      intro h
      apply h1
      rw [hsq] at h
      have := Subgroup.map_injective (MulAut.conj b).injective h
      exact this.symm
    have hsub : ({K, K.map (MulAut.conj b).toMonoidHom,
        K.map (MulAut.conj (b * b)).toMonoidHom} : Set (Subgroup G)) ⊆ conjSubgroupsBy B K := by
      intro K' hK'
      rcases hK' with h | h | h
      · rw [h]
        exact ⟨1, B.one_mem, hK1.symm⟩
      · rw [h]
        exact hmem b hb
      · rw [h]
        exact hmem (b * b) (B.mul_mem hb hb)
    have h4 : ({K, K.map (MulAut.conj b).toMonoidHom,
        K.map (MulAut.conj (b * b)).toMonoidHom} : Set (Subgroup G)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨_, _, _, fun h => h1 h.symm, fun h => h2' h.symm, h3, rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  rcases hcases with h | h
  · exact h
  · obtain ⟨n, hn⟩ := hodd
    have e : b = (b * b) ^ (n + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ, ← hn,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ h _

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem exists_cComp_not_le (h39 : Vol2Native.A39ForSQTKCat) (hB : IsB₀ X T D B₀)
    (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀) :
    ∃ K ∈ cComp (X ⊔ T ⊔ D), ¬ K ≤ B₀ := by
  have hN : (B₀.subgroupOf (X ⊔ T ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  have := H.h.simple
  have hKc : LocalSQTK G := (qtkeCore_of_cat H.h.nonabelian H.h.qtke).1
  by_contra hcon
  push Not at hcon
  have h1 := Vol2Native.lemma_1_2_1_one hKc h39 H.hB.2
  have hPB : perfectCore (X ⊔ T ⊔ D) ≤ B₀ := by
    rw [← h1]
    exact sSup_le hcon
  apply H.star_Y_ne_bot hB
  rw [eq_bot_iff]
  set π := QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) with hπ
  have hP : (perfectCore (⊤ : Subgroup ↥(X ⊔ T ⊔ D))).map (X ⊔ T ⊔ D).subtype =
      perfectCore (X ⊔ T ⊔ D) := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hP' : perfectCore (⊤ : Subgroup ↥(X ⊔ T ⊔ D)) ≤ B₀.subgroupOf (X ⊔ T ⊔ D) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have h2 : (x : G) ∈ (perfectCore (⊤ : Subgroup ↥(X ⊔ T ⊔ D))).map (X ⊔ T ⊔ D).subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [hP] at h2
    exact hPB h2
  have hQ : (perfectCore (⊤ : Subgroup ↥(X ⊔ T ⊔ D))).map π = perfectCore ⊤ := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hYP : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) ≤ perfectCore ⊤ :=
    le_perfectCore_of_perfect le_top (star_Y_perfect hB hY)
  intro q hq
  have h3 := hYP hq
  rw [← hQ] at h3
  obtain ⟨x, hx, rfl⟩ := h3
  exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff x).mpr (hP' hx))

theorem le_normalizer_of_T_le (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D)) (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) := by
  have := H.h.simple
  have hKc : LocalSQTK G := (qtkeCore_of_cat H.h.nonabelian H.h.qtke).1
  rcases Vol2Native.lemma_1_2_1_three hKc h37 h38 H.hB.2 hK with hn | ⟨h2, -⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK)).mp hn
  have hX : X ≤ Subgroup.normalizer (K : Set G) := by
    rw [← H.hXX, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hxX, hxo⟩
    exact mem_normalizer_of_odd h2 (Subgroup.mem_sup_left (Subgroup.mem_sup_left hxX)) hxo
  have hD : D ≤ Subgroup.normalizer (K : Set G) := by
    intro d hd
    refine mem_normalizer_of_odd h2 (Subgroup.mem_sup_right hd) ?_
    have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat H.h.Dodd h1
  exact sup_le (sup_le hX hT) hD

theorem T_le_normalizer_of_comm (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hB : IsB₀ X T D B₀) (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀)
    (hcomm : ∀ t ∈ T, ∀ t' ∈ T, ⁅t, t'⁆ ∈ B₀) {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hKB₀ : ¬ K ≤ B₀) : T ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := H.h.simple
  have hKc : LocalSQTK G := (qtkeCore_of_cat H.h.nonabelian H.h.qtke).1
  have hKB : K ≤ X ⊔ T ⊔ D := le_of_mem_cComp hK
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hconjB₀ : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ :=
    fun hg b hb => (Subgroup.mem_normalizer_iff.mp (hB.nor hg) b).mp hb
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  intro t ht
  by_contra htK
  have htB := hTB ht
  rcases Vol2Native.lemma_1_2_1_three hKc h37 h38 H.hB.2 hK with hn | ⟨h2, -⟩
  · exact htK ((Subgroup.normal_subgroupOf_iff_le_normalizer hKB).mp hn htB)
  set K' := conjByElt t K with hK'
  have hK'K : K' ≠ K := fun h => htK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hK'c : K' ∈ cComp (X ⊔ T ⊔ D) :=
    C2Nine.conjByElt_mem_cComp hK (Subgroup.le_normalizer htB)
  have hK'B : K' ≤ X ⊔ T ⊔ D := le_of_mem_cComp hK'c
  have hcKK : ⁅K, K'⁆ ≤ B₀ := by
    have h1 := Vol2Native.lemma_1_2_1_two hKc h37 H.hB.2 hK hK'c hK'K.symm
    exact (h1.1.trans h1.2).trans ((le_of_eq hT₀.symm).trans inf_le_right)
  have hS : conjSubgroupsBy (X ⊔ T ⊔ D) K = {K, K'} := by
    have hsub : ({K, K'} : Set (Subgroup G)) ⊆ conjSubgroupsBy (X ⊔ T ⊔ D) K := by
      intro K'' hK''
      rcases hK'' with rfl | rfl
      · refine ⟨1, (X ⊔ T ⊔ D).one_mem, ?_⟩
        rw [map_one]
        exact (Subgroup.map_id K'').symm
      · exact ⟨t, htB, rfl⟩
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
    rw [h2, Set.ncard_pair hK'K.symm]
  have hconjS : ∀ b ∈ X ⊔ T ⊔ D, conjByElt b K = K ∨ conjByElt b K = K' := fun b hb => by
    have : conjByElt b K ∈ conjSubgroupsBy (X ⊔ T ⊔ D) K := ⟨b, hb, rfl⟩
    rw [hS] at this
    exact this
  have hmul : ∀ b : G, conjByElt b K' = conjByElt (b * t) K := fun b => by
    unfold conjByElt
    rw [hK', conjByElt, Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hL₀n : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    have h1 := hconjS b hb
    have h2' := hconjS (b * t) ((X ⊔ T ⊔ D).mul_mem hb htB)
    rw [← hmul] at h2'
    have hne : conjByElt b K ≠ conjByElt b K' := fun h =>
      hK'K (Subgroup.map_injective (MulAut.conj b).injective h).symm
    change conjByElt b K ⊔ conjByElt b K' = K ⊔ K'
    rcases h1 with h1 | h1 <;> rcases h2' with h2' | h2'
    · exact absurd (h1.trans h2'.symm) hne
    · rw [h1, h2']
    · rw [h1, h2', sup_comm]
    · exact absurd (h1.trans h2'.symm) hne
  have hsolv : solvRad K ≤ B₀ := by
    have hKn : ((K).subgroupOf (K ⊔ K')).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hK hK'c))
    have h1 := solvRad_le_solvRad_of_subnormal (A3.subnormal_of_normal le_sup_left hKn)
    exact h1.trans (H.le_B₀_of_isSolvable hB hY ((solvRad_le _).trans (sup_le hKB hK'B))
      (hL₀n.trans (normalizer_le_normalizer_solvRad _)) (solvRad_isSolvable _))
  obtain ⟨a, ⟨haT, haK⟩, haB⟩ : ∃ a ∈ T ⊓ K, a ∉ B₀ := by
    by_contra hcon
    push Not at hcon
    have hsyl := A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) H.isSylowTwoOf_B
    have hle : T ⊓ K ≤ K ⊓ B₀ := fun x hx => ⟨hx.2, hcon x hx⟩
    have hodd : ¬ 2 ∣ (K ⊓ B₀).relIndex K := fun h2' =>
      hsyl.2.2 (h2'.trans (Subgroup.relIndex_dvd_of_le_left (L := K) hle))
    have hNn : ((K ⊓ B₀).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
        ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hk) (hB.nor (hKB hk))
    have hQs : Group.IsSolvable (↥K ⧸ (K ⊓ B₀).subgroupOf K) :=
      CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp fun he =>
        hodd (even_iff_two_dvd.mp he))
    have hKp : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact perfect_of_mem_cComp hK
    have hQp : ⁅(⊤ : Subgroup (↥K ⧸ (K ⊓ B₀).subgroupOf K)),
        (⊤ : Subgroup (↥K ⧸ (K ⊓ B₀).subgroupOf K))⁆ =
        (⊤ : Subgroup (↥K ⧸ (K ⊓ B₀).subgroupOf K)) := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' ((K ⊓ B₀).subgroupOf K))) hKp
      rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h1
    have htop : (⊤ : Subgroup (↥K ⧸ (K ⊓ B₀).subgroupOf K)) = ⊥ := by
      have h1 := le_perfectCore_of_perfect le_rfl hQp
      have hsol : Group.IsSolvable ↥(⊤ : Subgroup (↥K ⧸ (K ⊓ B₀).subgroupOf K)) :=
        inferInstance
      rw [(isSolvable_iff_perfectCore_eq_bot ⊤).mp hsol] at h1
      exact le_bot_iff.mp h1
    apply hKB₀
    intro k hk
    have h1 : (QuotientGroup.mk' ((K ⊓ B₀).subgroupOf K) ⟨k, hk⟩) ∈
        (⊤ : Subgroup (↥K ⧸ (K ⊓ B₀).subgroupOf K)) := Subgroup.mem_top _
    rw [htop, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1.2
  have haB' : a ∈ X ⊔ T ⊔ D := hTB haT
  have hcentral : ∀ k ∈ K, ⁅a, k⁆ ∈ B₀ := by
    intro k hk
    have hkB := hKB hk
    have hβ : t * a⁻¹ * t⁻¹ * a ∈ B₀ := by
      have := hcomm t ht a⁻¹ (T.inv_mem haT)
      simpa [commutatorElement_def] using this
    have hta : t * a * t⁻¹ ∈ K' := by
      rw [hK', mem_conjByElt]
      simpa [mul_assoc] using haK
    have hc1 : ⁅t * a * t⁻¹, k⁆ ∈ B₀ := by
      rw [Subgroup.commutator_comm] at hcKK
      exact hcKK (Subgroup.commutator_mem_commutator hta hk)
    have hc2 : ⁅t * a⁻¹ * t⁻¹ * a, k⁆ ∈ B₀ := by
      have e : ⁅t * a⁻¹ * t⁻¹ * a, k⁆ =
          (t * a⁻¹ * t⁻¹ * a) * (k * (t * a⁻¹ * t⁻¹ * a)⁻¹ * k⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact B₀.mul_mem hβ (hconjB₀ hkB (B₀.inv_mem hβ))
    have htaB : t * a * t⁻¹ ∈ X ⊔ T ⊔ D :=
      (X ⊔ T ⊔ D).mul_mem ((X ⊔ T ⊔ D).mul_mem htB haB') ((X ⊔ T ⊔ D).inv_mem htB)
    have e : ⁅a, k⁆ = (t * a * t⁻¹) * ⁅t * a⁻¹ * t⁻¹ * a, k⁆ * (t * a * t⁻¹)⁻¹ *
        ⁅t * a * t⁻¹, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact B₀.mul_mem (hconjB₀ htaB hc2) hc1
  let Z : Subgroup G :=
    { carrier := {z | z ∈ K ∧ ∀ k ∈ K, ⁅z, k⁆ ∈ B₀}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨K.mul_mem hx hy, fun k hk => ?_⟩
        have e : ⁅x * y, k⁆ = x * ⁅y, k⁆ * x⁻¹ * ⁅x, k⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact B₀.mul_mem (hconjB₀ (hKB hx) (hy' k hk)) (hx' k hk)
      one_mem' := ⟨K.one_mem, fun k _ => by
        rw [commutatorElement_one_left]; exact B₀.one_mem⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨K.inv_mem hx, fun k hk => ?_⟩
        have e : ⁅x⁻¹, k⁆ = x⁻¹ * ⁅x, k⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hconjB₀ (hKB (K.inv_mem hx)) (B₀.inv_mem (hx' k hk)) }
  have hZK : Z ≤ K := fun z hz => hz.1
  have hZn : (Z.subgroupOf K).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hZK).mpr ?_
    refine Main3324.le_normalizer_of_conj fun g hg z hz =>
      ⟨K.mul_mem (K.mul_mem hg hz.1) (K.inv_mem hg), fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hg) hk) (K.inv_mem
      (K.inv_mem hg))
    have e : ⁅g * z * g⁻¹, k⁆ = g * ⁅z, g⁻¹ * k * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconjB₀ (hKB hg) (hz.2 _ hk')
  have hZlt : Z < K := by
    refine lt_of_le_of_ne hZK fun hZ => hKB₀ ?_
    rw [← perfect_of_mem_cComp hK, Subgroup.commutator_le]
    intro x hx y hy
    have hxZ : x ∈ Z := by rw [hZ]; exact hx
    exact hxZ.2 y hy
  have haZ : a ∈ Z := ⟨haK, hcentral⟩
  exact haB (hsolv (le_solvRad_of_subnormal_lt hK (A3.subnormal_of_normal hZK hZn) hZlt haZ))

end Hyp3320

end S3320

end CFSG.Quasithin.H13
