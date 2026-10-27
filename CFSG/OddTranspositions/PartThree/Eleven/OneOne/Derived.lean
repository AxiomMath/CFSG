module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.DerivedShared
public import CFSG.GH74.Generic.BProg.B2.L2Cover
import CFSG.OddTranspositions.PartThree.Eleven.GroupLemmas
import CFSG.Milestones.ASVolI.I2Covers
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.OddTranspositions.PartThree

open DerivedShared
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open scoped Pointwise commutatorElement


variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

private lemma s11d_perfect_of_isSimple {X : Type*} [Group X] [IsSimpleGroup X]
    (hcard : Nat.card X = 60) : Group.IsPerfect X := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator X) with h | h
  · exfalso
    have hcomm : IsMulCommutative X := (commutator_eq_bot_iff X).mp h
    haveI := hcomm
    have hp : Nat.Prime (Nat.card X) := (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcard] at hp
    exact absurd hp (by norm_num)
  · exact Group.IsPerfect.mk h

private theorem s11d_H_facts (h : ElevenOneHyp hC)
    {A B : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hAB : O4PlusFactors (imageClass hC) A B) :
    let H := Halpha D hC.alpha
    let K : Subgroup H := CFSG.solvableRadical H
    let π : H →* (H ⧸ K) := QuotientGroup.mk' K
    (∀ a ∈ A.comap π, ∀ b ∈ B.comap π, Commute a b) ∧
      A.comap π ⊔ B.comap π = commutator H ∧
      A.comap π ⊓ B.comap π = K ∧
      (commutator H).index = 2 ∧
      (∀ r ∈ DstarH hC, (A.comap π).map (MulAut.conj r).toMonoidHom = B.comap π) ∧
      Nat.card K ≤ 2 ∧
      CFSG.IsQuasisimple (A.comap π) ∧
      Subgroup.center (A.comap π) = K.subgroupOf (A.comap π) ∧
      Nonempty ((A.comap π) ⧸ Subgroup.center (A.comap π) ≃* alternatingGroup (Fin 5)) ∧
      CFSG.IsQuasisimple (B.comap π) ∧
      Subgroup.center (B.comap π) = K.subgroupOf (B.comap π) ∧
      Nonempty ((B.comap π) ⧸ Subgroup.center (B.comap π) ≃* alternatingGroup (Fin 5)) := by
  classical
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let π : H →* (H ⧸ K) := QuotientGroup.mk' K
  let Lam1 : Subgroup H := A.comap π
  let Lam2 : Subgroup H := B.comap π
  let H1 : Subgroup H := commutator H
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hπker : π.ker = K := QuotientGroup.ker_mk' K
  have hπrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπsurj
  have hcenter : K = Subgroup.center H := h.center
  obtain ⟨d₀, hd₀⟩ := DstarH_isClass hC
  have hindex_le : (commutator H).index ≤ 2 :=
    (⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩ :
      Setup H (DstarH hC)).index_commutator_le_two
  have hQ : (commutator (H ⧸ K)).index = 2 := h.facts.index_two
  have hKle : K ≤ commutator H := le_commutator_of_index_commutator_quotient K hindex_le hQ
  have hindex : (commutator H).index = 2 := by
    have hne : (commutator H).index ≠ 1 := by
      intro h1
      have htop : commutator H = ⊤ := Subgroup.index_eq_one.mp h1
      have hmap := TauCeti.Subgroup.map_commutator_eq_commutator (f := π) hπsurj
      rw [htop, Subgroup.map_top, hπrange] at hmap
      have h1' : (commutator (H ⧸ K)).index = 1 := Subgroup.index_eq_one.mpr hmap.symm
      omega
    have hpos : 0 < (commutator H).index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    omega
  have hker_le : π.ker ≤ Lam1 ⊔ Lam2 := by
    intro x hx
    have hxLam1 : x ∈ Lam1 := by
      rw [Subgroup.mem_comap]
      rw [MonoidHom.mem_ker] at hx
      rw [hx]
      exact A.one_mem
    exact Subgroup.mem_sup_left hxLam1
  have hinf : Lam1 ⊓ Lam2 = K := by
    have h1 : Lam1 ⊓ Lam2 = (A ⊓ B).comap π := by rw [Subgroup.comap_inf]
    rw [h1, hAB.inf_eq]
    change π.ker = K
    exact hπker
  have hsup : Lam1 ⊔ Lam2 = commutator H := by
    have hmap : (commutator H).map π = commutator (H ⧸ K) :=
      TauCeti.Subgroup.map_commutator_eq_commutator hπsurj
    have hmapSup : (Lam1 ⊔ Lam2).map π = (commutator H).map π := by
      rw [Subgroup.map_sup]
      rw [Subgroup.map_comap_eq_self (H := A) (by rw [hπrange]; exact le_top),
        Subgroup.map_comap_eq_self (H := B) (by rw [hπrange]; exact le_top)]
      rw [hAB.sup_eq, hmap]
    calc Lam1 ⊔ Lam2
        = Subgroup.comap π ((Lam1 ⊔ Lam2).map π) :=
          (Subgroup.comap_map_eq_self hker_le).symm
      _ = Subgroup.comap π ((commutator H).map π) := by rw [hmapSup]
      _ = commutator H := Subgroup.comap_map_eq_self (by rw [hπker]; exact hKle)
  let L1' : Subgroup H := ⁅Lam1, Lam1⁆
  let L2' : Subgroup H := ⁅Lam2, Lam2⁆
  let H2 : Subgroup H := ⁅H1, H1⁆
  have hAperf : Group.IsPerfect A := by
    haveI := hAB.simpleA
    exact s11d_perfect_of_isSimple hAB.cardA
  have hBperf : Group.IsPerfect B := by
    haveI := hAB.simpleB
    exact s11d_perfect_of_isSimple hAB.cardB
  let π₁ : Lam1 →* (H ⧸ K) := π.comp Lam1.subtype
  have hker₁ : π₁.ker = K.subgroupOf Lam1 := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker]
    rfl
  have hrange₁ : π₁.range = A := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change Subgroup.map π Lam1 = A
    rw [Subgroup.map_comap_eq, hπrange, top_inf_eq]
  have hmap₁ : (commutator ↥Lam1).map π₁ = A := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, hrange₁]
    exact Subgroup.isPerfect_iff.mp hAperf
  let π₂ : Lam2 →* (H ⧸ K) := π.comp Lam2.subtype
  have hker₂ : π₂.ker = K.subgroupOf Lam2 := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker]
    rfl
  have hrange₂ : π₂.range = B := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change Subgroup.map π Lam2 = B
    rw [Subgroup.map_comap_eq, hπrange, top_inf_eq]
  have hmap₂ : (commutator ↥Lam2).map π₂ = B := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, hrange₂]
    exact Subgroup.isPerfect_iff.mp hBperf
  have hperf : commutator ↥Lam1 ⊔ K.subgroupOf Lam1 = ⊤ := by
    have hmapS : (commutator ↥Lam1 ⊔ π₁.ker).map π₁ = A := by
      rw [Subgroup.map_sup, hmap₁]
      have : (π₁.ker).map π₁ = ⊥ := (Subgroup.map_eq_bot_iff (π₁.ker)).mpr le_rfl
      rw [this, sup_bot_eq]
    have hcomapA : Subgroup.comap π₁ A = ⊤ := by
      apply (Subgroup.eq_top_iff' (Subgroup.comap π₁ A)).mpr
      intro x
      rw [Subgroup.mem_comap, ← hrange₁]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    calc commutator ↥Lam1 ⊔ K.subgroupOf Lam1
        = commutator ↥Lam1 ⊔ π₁.ker := by rw [hker₁]
      _ = Subgroup.comap π₁ ((commutator ↥Lam1 ⊔ π₁.ker).map π₁) :=
          (Subgroup.comap_map_eq_self le_sup_right).symm
      _ = Subgroup.comap π₁ A := by rw [hmapS]
      _ = ⊤ := hcomapA
  have hcomm : ∀ a ∈ Lam1, ∀ b ∈ Lam2, Commute a b := by
    intro a ha b hb
    have hmem : ∀ x ∈ Lam1, ⁅x, b⁆ ∈ K := by
      intro x hx
      have hxA : π x ∈ A := Subgroup.mem_comap.mp hx
      have hbB : π b ∈ B := Subgroup.mem_comap.mp hb
      have h1 : π ⁅x, b⁆ = 1 := by
        rw [map_commutatorElement]
        exact (hAB.commute (π x) hxA (π b) hbB).commutator_eq
      rwa [← hπker, MonoidHom.mem_ker]
    exact comm_of_perfect K (by rw [hcenter]) Lam1 hperf hmem a ha
  have hswap : ∀ r ∈ DstarH hC, Lam1.map (MulAut.conj r).toMonoidHom = Lam2 := by
    intro r hr
    have hrIm : π r ∈ imageClass hC := ⟨r, hr, rfl⟩
    exact map_conj_comap π (hAB.swap (π r) hrIm)
  have hH1sup : H1 = Lam1 ⊔ Lam2 := hsup.symm
  have hL1'le : L1' ≤ Lam1 := by
    show ⁅Lam1, Lam1⁆ ≤ Lam1
    simpa using Subgroup.commutator_le_sup Lam1 Lam1
  have hL2'le : L2' ≤ Lam2 := by
    show ⁅Lam2, Lam2⁆ ≤ Lam2
    simpa using Subgroup.commutator_le_sup Lam2 Lam2
  have hL1'comm : ∀ a ∈ L1', ∀ b ∈ L2', Commute a b := by
    intro a ha b hb
    exact hcomm a (hL1'le ha) b (hL2'le hb)
  have hKleLam1 : K ≤ Lam1 := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : π x = 1 := by
      rw [← hπker, MonoidHom.mem_ker] at hx
      exact hx
    rw [hx1]
    exact A.one_mem
  have hKleLam2 : K ≤ Lam2 := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : π x = 1 := by
      rw [← hπker, MonoidHom.mem_ker] at hx
      exact hx
    rw [hx1]
    exact B.one_mem
  have hmapLam1 : Lam1.map π = A := by
    rw [show Lam1 = A.comap π from rfl, Subgroup.map_comap_eq, hπrange, top_inf_eq]
  have hmapLam2 : Lam2.map π = B := by
    rw [show Lam2 = B.comap π from rfl, Subgroup.map_comap_eq, hπrange, top_inf_eq]
  have hmapL1' : L1'.map π = A := by
    show (⁅Lam1, Lam1⁆ : Subgroup H).map π = A
    rw [Subgroup.map_commutator, hmapLam1, Subgroup.isPerfect_iff.mp hAperf]
  have hmapL2' : L2'.map π = B := by
    show (⁅Lam2, Lam2⁆ : Subgroup H).map π = B
    rw [Subgroup.map_commutator, hmapLam2, Subgroup.isPerfect_iff.mp hBperf]
  have hL1_eq : Lam1 = L1' ⊔ K := by
    apply le_antisymm
    · intro x hx
      have hxA : π x ∈ A := Subgroup.mem_comap.mp hx
      have hxmap : π x ∈ L1'.map π := by rw [hmapL1']; exact hxA
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
      have hyK : y⁻¹ * x ∈ K := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have hx_eq : x = y * (y⁻¹ * x) := by group
      rw [hx_eq]
      exact Subgroup.mul_mem_sup hy hyK
    · exact sup_le hL1'le hKleLam1
  have hL2_eq : Lam2 = L2' ⊔ K := by
    apply le_antisymm
    · intro x hx
      have hxB : π x ∈ B := Subgroup.mem_comap.mp hx
      have hxmap : π x ∈ L2'.map π := by rw [hmapL2']; exact hxB
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
      have hyK : y⁻¹ * x ∈ K := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have hx_eq : x = y * (y⁻¹ * x) := by group
      rw [hx_eq]
      exact Subgroup.mul_mem_sup hy hyK
    · exact sup_le hL2'le hKleLam2
  have hH2eq : H2 = L1' ⊔ L2' := by
    apply le_antisymm
    · rw [show H2 = ⁅H1, H1⁆ from rfl, hH1sup, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨x1, hx1, x2, hx2, rfl⟩ := (mem_sup_of_commute hcomm).mp hx
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := (mem_sup_of_commute hcomm).mp hy
      have hm1 : ⁅x1, y1⁆ ∈ Lam1 := hL1'le
        (Subgroup.commutator_mem_commutator hx1 hy1)
      have hm2 : ⁅x2, y2⁆ ∈ Lam2 := hL2'le
        (Subgroup.commutator_mem_commutator hx2 hy2)
      have h := TauCeti.commutatorElement_mul_mul_eq_mul_of_commute
        (hcomm y1 hy1 x2 hx2).symm (hcomm x1 hx1 y2 hy2)
        (hcomm y1 hy1 ⁅x2, y2⁆ hm2) (hcomm x1 hx1 ⁅x2, y2⁆ hm2)
        (hcomm ⁅x1, y1⁆ hm1 ⁅x2, y2⁆ hm2)
      rw [h]
      exact Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator hx1 hy1)
        (Subgroup.commutator_mem_commutator hx2 hy2)
    · show L1' ⊔ L2' ≤ (⁅H1, H1⁆ : Subgroup H)
      rw [hH1sup]
      exact sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)
  have hH1_eq : H1 = H2 ⊔ K := by
    rw [hH1sup, hL1_eq, hL2_eq, hH2eq]
    ac_rfl
  have hH1_perf : H1 = H2 := by
    have hH2le : H2 ≤ H1 := by
      show (⁅H1, H1⁆ : Subgroup H) ≤ H1
      simpa using Subgroup.commutator_le_sup H1 H1
    apply le_antisymm ?_ hH2le
    let Q := H ⧸ H2
    let π₂' : H →* Q := QuotientGroup.mk' H2
    obtain ⟨c, hc⟩ := CFSG.OddTranspositions.image_isClass_quotient hd₀ H2
    have hQgen : Subgroup.closure {g : Q | IsConj c g} = ⊤ := by
      rw [← hc]
      exact CFSG.OddTranspositions.image_closure_eq_top_quotient H2 (DstarH_closure_eq_top hC)
    have hQle : commutator Q ≤ Subgroup.center Q := by
      have hmap : (commutator H).map π₂' = commutator Q :=
        TauCeti.Subgroup.map_commutator_eq_commutator (QuotientGroup.mk'_surjective H2)
      rw [← hmap]
      refine (Subgroup.map_le_iff_le_comap).mpr ?_
      have hle1 : H2 ≤ Subgroup.comap π₂' (Subgroup.center Q) := by
        intro x hx
        rw [Subgroup.mem_comap]
        have hx1 : π₂' x = 1 := by
          rw [← MonoidHom.mem_ker, show π₂'.ker = H2 from QuotientGroup.ker_mk' H2]
          exact hx
        rw [hx1]
        exact Subgroup.one_mem _
      have hle2 : K ≤ Subgroup.comap π₂' (Subgroup.center Q) := by
        intro x hx
        rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective H2 q
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp (hcenter ▸ hx) y
      calc H1 = H2 ⊔ K := hH1_eq
        _ ≤ Subgroup.comap π₂' (Subgroup.center Q) := sup_le hle1 hle2
    have hab := commute_of_closure_isConj_of_commutator_le_center c hQgen hQle
    have hQab : IsMulCommutative Q :=
      isMulCommutative_iff.mpr (fun a b => (hab a b).eq)
    have hQbot : commutator Q = ⊥ := (commutator_eq_bot_iff Q).mpr hQab
    have hmapH1 : H1.map π₂' = ⊥ := by
      change (commutator H).map π₂' = ⊥
      rw [TauCeti.Subgroup.map_commutator_eq_commutator (QuotientGroup.mk'_surjective H2),
        hQbot]
    have hle : H1 ≤ π₂'.ker := (Subgroup.map_eq_bot_iff H1).mp hmapH1
    rwa [show π₂'.ker = H2 from QuotientGroup.ker_mk' H2] at hle
  have hKleH2 : K ≤ H2 := by
    have h := hKle
    change K ≤ H1 at h
    rwa [hH1_perf] at h
  have hK_decomp : K = (L1' ⊓ K) ⊔ (L2' ⊓ K) := by
    apply le_antisymm
    · intro k hk
      have hkH2 : k ∈ H2 := hKleH2 hk
      rw [hH2eq] at hkH2
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_commute hL1'comm).mp hkH2
      have hpa : π a ∈ A := Subgroup.mem_comap.mp (hL1'le ha)
      have hpb : π b ∈ B := Subgroup.mem_comap.mp (hL2'le hb)
      have hk1 : π k = 1 := by
        rw [← hπker, MonoidHom.mem_ker] at hk
        exact hk
      have hpab : π a * π b = 1 := by
        rw [← map_mul, hab, hk1]
      have haK : a ∈ K := by
        have hpaB : π a ∈ B := by
          have hpa_eq : π a = (π b)⁻¹ := by
            have h := congrArg (fun z => z * (π b)⁻¹) hpab
            simpa using h
          rw [hpa_eq]
          exact B.inv_mem hpb
        have hpa1 : π a = 1 := by
          have : π a ∈ A ⊓ B := ⟨hpa, hpaB⟩
          rw [hAB.inf_eq] at this
          exact Subgroup.mem_bot.mp this
        rwa [← hπker, MonoidHom.mem_ker]
      have hbK : b ∈ K := by
        have hpbA : π b ∈ A := by
          have hpb_eq : π b = (π a)⁻¹ := by
            have h := congrArg (fun z => (π a)⁻¹ * z) hpab
            simpa using h
          rw [hpb_eq]
          exact A.inv_mem hpa
        have hpb1 : π b = 1 := by
          have : π b ∈ A ⊓ B := ⟨hpbA, hpb⟩
          rw [hAB.inf_eq] at this
          exact Subgroup.mem_bot.mp this
        rwa [← hπker, MonoidHom.mem_ker]
      rw [← hab]
      exact Subgroup.mul_mem_sup ⟨ha, haK⟩ ⟨hb, hbK⟩
    · exact sup_le inf_le_right inf_le_right
  have hL1'K_eq : L1' ⊓ K = L2' ⊓ K := by
    obtain ⟨ρ, hρ⟩ := DstarH_nonempty hC
    have hfixK : ∀ x ∈ K, (MulAut.conj ρ).toMonoidHom x = x := by
      intro x hx
      have hxcen : x ∈ Subgroup.center H := hcenter ▸ hx
      have h := Subgroup.mem_center_iff.mp hxcen ρ
      rw [show (MulAut.conj ρ).toMonoidHom x = ρ * x * ρ⁻¹ by simp [MulAut.conj_apply],
        h, mul_assoc, mul_inv_cancel, mul_one]
    have hmapL1'conj : L1'.map (MulAut.conj ρ).toMonoidHom = L2' := by
      show (⁅Lam1, Lam1⁆ : Subgroup H).map _ = L2'
      rw [Subgroup.map_commutator, hswap ρ hρ]
    have hmapKconj : K.map (MulAut.conj ρ).toMonoidHom = K :=
      map_eq_self _ K hfixK
    calc L1' ⊓ K = (L1' ⊓ K).map (MulAut.conj ρ).toMonoidHom :=
          (map_eq_self _ _ (fun x hx => hfixK x (Subgroup.mem_inf.mp hx).2)).symm
      _ = L1'.map (MulAut.conj ρ).toMonoidHom ⊓ K.map (MulAut.conj ρ).toMonoidHom :=
          Subgroup.map_inf L1' K _ (MulAut.conj ρ).injective
      _ = L2' ⊓ K := by rw [hmapL1'conj, hmapKconj]
  have hKleL1' : K ≤ L1' := by
    calc K = (L1' ⊓ K) ⊔ (L2' ⊓ K) := hK_decomp
      _ = (L1' ⊓ K) ⊔ (L1' ⊓ K) := by rw [hL1'K_eq]
      _ = L1' ⊓ K := sup_idem _
      _ ≤ L1' := inf_le_left
  have hL1_perf : Lam1 = L1' := by
    calc Lam1 = L1' ⊔ K := hL1_eq
      _ = L1' := sup_eq_left.mpr hKleL1'
  have hperfect : Group.IsPerfect Lam1 := Subgroup.isPerfect_iff.mpr hL1_perf.symm
  have hcenterA : Subgroup.center A = ⊥ := by
    haveI := hAB.simpleA
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center A) with h | h
    · exact h
    · exfalso
      have hcommA : IsMulCommutative A := by
        rw [isMulCommutative_iff]
        intro x y
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm
      haveI := hcommA
      have hp : Nat.Prime (Nat.card A) := (Group.is_simple_iff_prime_card).mp inferInstance
      rw [hAB.cardA] at hp
      exact absurd hp (by norm_num)
  have hcenterL1 : Subgroup.center Lam1 = K.subgroupOf Lam1 := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxA : π (x : H) ∈ A := Subgroup.mem_comap.mp x.2
      have hxcent : (⟨π (x : H), hxA⟩ : A) ∈ Subgroup.center A := by
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        change a.val * π (x : H) = π (x : H) * a.val
        have ha : a.val ∈ π₁.range := by rw [hrange₁]; exact a.2
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp ha
        rw [← hy]
        change π (y : H) * π (x : H) = π (x : H) * π (y : H)
        have hc := Subgroup.mem_center_iff.mp hx y
        have hc' : (y : H) * (x : H) = (x : H) * (y : H) := by
          simpa using congrArg (Subgroup.subtype Lam1) hc
        rw [← map_mul, ← map_mul, hc']
      rw [hcenterA, Subgroup.mem_bot] at hxcent
      have hx1 : π (x : H) = 1 := congrArg Subtype.val hxcent
      rw [← hπker, MonoidHom.mem_ker]
      exact hx1
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hxcen : (x : H) ∈ Subgroup.center H :=
        hcenter ▸ (Subgroup.mem_subgroupOf.mp hx)
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxcen (y : H))
  have eA : Lam1 ⧸ Subgroup.center Lam1 ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq (hcenterL1.trans hker₁.symm)).trans
      ((QuotientGroup.quotientKerEquivRange π₁).trans (MulEquiv.subgroupCongr hrange₁))
  have hsimpleL1 : IsSimpleGroup (Lam1 ⧸ Subgroup.center Lam1) := by
    haveI := hAB.simpleA
    exact MulEquiv.isSimpleGroup eA
  have hnotcommA : ¬ IsMulCommutative A := by
    intro hc
    haveI := hc
    have hp : Nat.Prime (Nat.card A) := (Group.is_simple_iff_prime_card).mp hAB.simpleA
    rw [hAB.cardA] at hp
    exact absurd hp (by norm_num)
  have hnoncommL1 : ∃ a b : Lam1 ⧸ Subgroup.center Lam1, a * b ≠ b * a := by
    by_contra h
    push Not at h
    apply hnotcommA
    rw [isMulCommutative_iff]
    intro a b
    have h1 := congrArg eA (h (eA.symm a) (eA.symm b))
    simpa using h1
  have hq : CFSG.IsQuasisimple Lam1 := ⟨hperfect, hsimpleL1, hnoncommL1⟩
  obtain ⟨e5⟩ := by
    haveI := hAB.simpleA
    exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (G := A) hAB.cardA
  have e : Lam1 ⧸ Subgroup.center Lam1 ≃* alternatingGroup (Fin 5) := eA.trans e5
  have hdvd : Nat.card (Subgroup.center Lam1) ∣ 2 := by
    have h := CFSG.GH74.Generic.BProg.B2.L2Cover.card_center_dvd_card_hopfMultiplier_qs
      (K := Lam1) (X := alternatingGroup (Fin 5)) hq e
    rwa [CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five.2] at h
  have hmapKsub : (K.subgroupOf Lam1).map Lam1.subtype = K := by
    rw [← Subgroup.comap_subtype K Lam1, Subgroup.map_comap_eq, Subgroup.range_subtype,
      inf_eq_right.mpr (hKleL1'.trans hL1'le)]
  have hcard_center : Nat.card (Subgroup.center Lam1) = Nat.card K := by
    rw [hcenterL1,
      ← Subgroup.card_map_of_injective (K := K.subgroupOf Lam1) Lam1.subtype_injective,
      hmapKsub]
  have hcardK : Nat.card K ≤ 2 := by
    rw [← hcard_center]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hstruct : CFSG.IsQuasisimple Lam1 ∧
      Subgroup.center Lam1 = K.subgroupOf Lam1 ∧
      Nonempty (Lam1 ⧸ Subgroup.center Lam1 ≃* alternatingGroup (Fin 5)) :=
    ⟨hq, hcenterL1, ⟨e⟩⟩
  have hcenterB : Subgroup.center B = ⊥ := by
    haveI := hAB.simpleB
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center B) with h | h
    · exact h
    · exfalso
      have hcommB : IsMulCommutative B := by
        rw [isMulCommutative_iff]
        intro x y
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm
      haveI := hcommB
      have hp : Nat.Prime (Nat.card B) := (Group.is_simple_iff_prime_card).mp inferInstance
      rw [hAB.cardB] at hp
      exact absurd hp (by norm_num)
  have hcenterL2 : Subgroup.center Lam2 = K.subgroupOf Lam2 := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxB : π (x : H) ∈ B := Subgroup.mem_comap.mp x.2
      have hxcent : (⟨π (x : H), hxB⟩ : B) ∈ Subgroup.center B := by
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        change a.val * π (x : H) = π (x : H) * a.val
        have ha : a.val ∈ π₂.range := by rw [hrange₂]; exact a.2
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp ha
        rw [← hy]
        change π (y : H) * π (x : H) = π (x : H) * π (y : H)
        have hc := Subgroup.mem_center_iff.mp hx y
        have hc' : (y : H) * (x : H) = (x : H) * (y : H) := by
          simpa using congrArg (Subgroup.subtype Lam2) hc
        rw [← map_mul, ← map_mul, hc']
      rw [hcenterB, Subgroup.mem_bot] at hxcent
      have hx1 : π (x : H) = 1 := congrArg Subtype.val hxcent
      rw [← hπker, MonoidHom.mem_ker]
      exact hx1
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hxcen : (x : H) ∈ Subgroup.center H :=
        hcenter ▸ (Subgroup.mem_subgroupOf.mp hx)
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxcen (y : H))
  have eB : Lam2 ⧸ Subgroup.center Lam2 ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq (hcenterL2.trans hker₂.symm)).trans
      ((QuotientGroup.quotientKerEquivRange π₂).trans (MulEquiv.subgroupCongr hrange₂))
  have hsimpleL2 : IsSimpleGroup (Lam2 ⧸ Subgroup.center Lam2) := by
    haveI := hAB.simpleB
    exact MulEquiv.isSimpleGroup eB
  have hnotcommB : ¬ IsMulCommutative B := by
    intro hc
    haveI := hc
    have hp : Nat.Prime (Nat.card B) := (Group.is_simple_iff_prime_card).mp hAB.simpleB
    rw [hAB.cardB] at hp
    exact absurd hp (by norm_num)
  have hnoncommL2 : ∃ a b : Lam2 ⧸ Subgroup.center Lam2, a * b ≠ b * a := by
    by_contra h
    push Not at h
    apply hnotcommB
    rw [isMulCommutative_iff]
    intro a b
    have h1 := congrArg eB (h (eB.symm a) (eB.symm b))
    simpa using h1
  have hKleL2' : K ≤ L2' := by
    have h : L2' ⊓ K = K := by rw [← hL1'K_eq, inf_eq_right.mpr hKleL1']
    exact h ▸ inf_le_left
  have hL2_perf : Lam2 = L2' := by
    calc Lam2 = L2' ⊔ K := hL2_eq
      _ = L2' := sup_eq_left.mpr hKleL2'
  have hperfect2 : Group.IsPerfect Lam2 := Subgroup.isPerfect_iff.mpr hL2_perf.symm
  have hq2 : CFSG.IsQuasisimple Lam2 := ⟨hperfect2, hsimpleL2, hnoncommL2⟩
  obtain ⟨e5b⟩ := by
    haveI := hAB.simpleB
    exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (G := B) hAB.cardB
  have e2 : Lam2 ⧸ Subgroup.center Lam2 ≃* alternatingGroup (Fin 5) := eB.trans e5b
  exact ⟨hcomm, hsup, hinf, hindex, hswap, hcardK, hstruct.1, hstruct.2.1, hstruct.2.2,
    hq2, hcenterL2, ⟨e2⟩⟩

theorem derived (h : ElevenOneHyp hC)
    {A B : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hAB : O4PlusFactors (imageClass hC) A B) :
    (∀ a ∈ liftH hC A, ∀ b ∈ liftH hC B, Commute a b) ∧
      liftH hC A ⊔ liftH hC B =
        (commutator (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧
      liftH hC A ⊓ liftH hC B = Malpha D hC.alpha ∧
      (commutator (Halpha D hC.alpha)).index = 2 ∧
      (∀ r ∈ DalphaStar D hC.alpha,
        (liftH hC A).map (MulAut.conj r).toMonoidHom = liftH hC B) ∧
      Nat.card (Malpha D hC.alpha) ≤ 2 := by
  classical
  obtain ⟨hcomm, hsup, hinf, hindex, hswap, hcardK, -, -, -, -, -, -⟩ :=
    s11d_H_facts h hAB
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let Lam1 : Subgroup H := A.comap (QuotientGroup.mk' K)
  let Lam2 : Subgroup H := B.comap (QuotientGroup.mk' K)
  have hlift_sup : liftH hC A ⊔ liftH hC B = (commutator H).map H.subtype := by
    change Lam1.map H.subtype ⊔ Lam2.map H.subtype = (commutator H).map H.subtype
    rw [← Subgroup.map_sup, hsup]
  have hlift_inf : liftH hC A ⊓ liftH hC B = K.map H.subtype := by
    change Lam1.map H.subtype ⊓ Lam2.map H.subtype = K.map H.subtype
    rw [← Subgroup.map_inf Lam1 Lam2 H.subtype H.subtype_injective, hinf]
  have hlift_card : Nat.card (K.map H.subtype) ≤ 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hcardK
  refine ⟨?_, ?_, ?_, hindex, ?_, ?_⟩
  · intro a ha b hb
    rw [liftH] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact (hcomm a' ha' b' hb').map H.subtype
  · exact hlift_sup
  · rw [hlift_inf]
    rfl
  · intro r hr
    change (Lam1.map H.subtype).map (MulAut.conj r).toMonoidHom = Lam2.map H.subtype
    let rH : H := ⟨r, Subgroup.subset_closure hr⟩
    have hrH : rH ∈ DstarH hC := hr
    have hswapH := hswap rH hrH
    have hcomp : (MulAut.conj r).toMonoidHom.comp H.subtype =
        H.subtype.comp (MulAut.conj rH).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, rH]
    calc (Lam1.map H.subtype).map (MulAut.conj r).toMonoidHom
        = Lam1.map ((MulAut.conj r).toMonoidHom.comp H.subtype) :=
          Subgroup.map_map Lam1 (MulAut.conj r).toMonoidHom H.subtype
      _ = Lam1.map (H.subtype.comp (MulAut.conj rH).toMonoidHom) := by rw [hcomp]
      _ = (Lam1.map (MulAut.conj rH).toMonoidHom).map H.subtype :=
          (Subgroup.map_map Lam1 H.subtype (MulAut.conj rH).toMonoidHom).symm
      _ = Lam2.map H.subtype := by rw [hswapH]
  · rw [show Malpha D hC.alpha = K.map H.subtype from rfl]
    exact hlift_card

theorem liftH_equiv (h : ElevenOneHyp hC)
    {A B : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hAB : O4PlusFactors (imageClass hC) A B) (hM : Malpha D hC.alpha ≠ ⊥) :
    Nonempty (liftH hC A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      Nonempty (liftH hC B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  classical
  obtain ⟨-, -, -, -, -, hcardK, hq1, hcenterL1, ⟨e1⟩, hq2, hcenterL2, ⟨e2⟩⟩ :=
    s11d_H_facts h hAB
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let π : H →* (H ⧸ K) := QuotientGroup.mk' K
  let Lam1 : Subgroup H := A.comap π
  let Lam2 : Subgroup H := B.comap π
  have hπker : π.ker = K := QuotientGroup.ker_mk' K
  have hKne : K ≠ ⊥ := by
    intro h0
    apply hM
    rw [show Malpha D hC.alpha = K.map H.subtype from rfl, h0, Subgroup.map_bot]
  have hKleLam1 : K ≤ Lam1 := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : π x = 1 := by
      rw [← hπker, MonoidHom.mem_ker] at hx
      exact hx
    rw [hx1]
    exact A.one_mem
  have hKleLam2 : K ≤ Lam2 := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : π x = 1 := by
      rw [← hπker, MonoidHom.mem_ker] at hx
      exact hx
    rw [hx1]
    exact B.one_mem
  have hmapKsub1 : (K.subgroupOf Lam1).map Lam1.subtype = K := by
    rw [← Subgroup.comap_subtype K Lam1, Subgroup.map_comap_eq, Subgroup.range_subtype,
      inf_eq_right.mpr hKleLam1]
  have hmapKsub2 : (K.subgroupOf Lam2).map Lam2.subtype = K := by
    rw [← Subgroup.comap_subtype K Lam2, Subgroup.map_comap_eq, Subgroup.range_subtype,
      inf_eq_right.mpr hKleLam2]
  have hc1ne : Subgroup.center Lam1 ≠ ⊥ := by
    rw [hcenterL1]
    intro h
    apply hKne
    have hbot : (K.subgroupOf Lam1).map Lam1.subtype = ⊥ := by rw [h, Subgroup.map_bot]
    rwa [hmapKsub1] at hbot
  have hc2ne : Subgroup.center Lam2 ≠ ⊥ := by
    rw [hcenterL2]
    intro h
    apply hKne
    have hbot : (K.subgroupOf Lam2).map Lam2.subtype = ⊥ := by rw [h, Subgroup.map_bot]
    rwa [hmapKsub2] at hbot
  have hle1 : Nat.card (Subgroup.center Lam1) ≤ 2 := by
    rw [hcenterL1,
      ← Subgroup.card_map_of_injective (K := K.subgroupOf Lam1) Lam1.subtype_injective,
      hmapKsub1]
    exact hcardK
  have hle2 : Nat.card (Subgroup.center Lam2) ≤ 2 := by
    rw [hcenterL2,
      ← Subgroup.card_map_of_injective (K := K.subgroupOf Lam2) Lam2.subtype_injective,
      hmapKsub2]
    exact hcardK
  have hSL1 : Nonempty (Lam1 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    isSL2_of_center_eq_bot hq1 hc1ne hle1 e1
  have hSL2 : Nonempty (Lam2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    isSL2_of_center_eq_bot hq2 hc2ne hle2 e2
  refine ⟨?_, ?_⟩
  · obtain ⟨eL⟩ := hSL1
    exact ⟨(Subgroup.equivMapOfInjective Lam1 H.subtype H.subtype_injective).symm.trans eL⟩
  · obtain ⟨eL⟩ := hSL2
    exact ⟨(Subgroup.equivMapOfInjective Lam2 H.subtype H.subtype_injective).symm.trans eL⟩

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
