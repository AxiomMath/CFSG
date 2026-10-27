module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndGold

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
open scoped commutatorElement

section AbelianCase



variable {X : Type} [Group X] [Finite X] {A R N H : Subgroup X} {t : X}

theorem endg_abelian_of (h : EndgameHyp X A R N H t)
    (hSyl : ∃ T : Sylow 2 X, (T : Subgroup X) ≤ Subgroup.normalizer (A : Set X))
    (hEab : ∀ x ∈ EgenX A, ∀ y ∈ EgenX A, x * y = y * x)
    (hK : ∃ K : Subgroup X, K ≤ R ∧ ⁅K, K⁆ = K ∧ K ≠ ⊥ ∧ R ≤ K ⊔ N ∧
      (∀ g : X, g ∈ Subgroup.normalizer (R : Set X) → g ∈ Subgroup.normalizer (K : Set X)) ∧
      ∀ J : Subgroup X, J ≤ K → (J.subgroupOf K).Normal → J ≠ K →
        16 ∣ (J.subgroupOf K).index)
    (hC8 : ∀ {Kp Cj : Subgroup X}, Kp ≤ R → ⁅Kp, Kp⁆ = Kp → R ≤ Kp ⊔ N →
      (∀ g : X, g ∈ Subgroup.normalizer (R : Set X) → g ∈ Subgroup.normalizer (Kp : Set X)) →
      IsSimpleGroup ↥Cj → (∃ a ∈ Cj, ∃ b ∈ Cj, a * b ≠ b * a) →
      (∀ k ∈ Kp, k ∈ Subgroup.normalizer (Cj : Set X)) → (∀ c ∈ Cj, c * t = t * c) →
      (∃ k ∈ Kp, ∃ c ∈ Cj, k * c ≠ c * k) → False) : False := by
  classical
  obtain ⟨T, hT⟩ := hSyl
  haveI := h.H_normal
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa [pow_two] using h.A_sq a a.2)⟩
  have hA1 : A ≠ ⊥ := fun hb => h.t_ne (by
    have := h.t_mem
    rw [hb, Subgroup.mem_bot] at this
    exact this)
  obtain ⟨z, hzA, hz1, hzT, hzc⟩ := endg_exists_sylow_central hA2 hA1 T hT
  have hwcl : CFSG.LargeExtraspecial.S11.wcl z ≤ EgenX A := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨m, rfl, hyz⟩
    have hyA : m * z * m⁻¹ ∈ conjSubgroup m A :=
      mem_conjSubgroup.mpr (by simpa [mul_assoc] using hzA)
    have hy1 : m * z * m⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      have : z = m⁻¹ * (m * z * m⁻¹) * m := by group
      rw [this, h1]; group
    have hzA' : z ∈ conjSubgroup 1 A := by rwa [conjSubgroup_one]
    have hcomm := h.N1 m 1 (m * z * m⁻¹) hyA hy1 z hzA' hz1 hyz
    have hIn : InOmegaA A m := fun w hw y' hy' =>
      (hcomm y' hy' w (by rwa [conjSubgroup_one])).symm
    have hle : conjSubgroup m A ≤ EgenX A := le_iSup₂_of_le m hIn le_rfl
    exact hle hyA
  have hab : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl z) :=
    ⟨⟨fun a b => Subtype.ext (hEab a (hwcl a.2) b (hwcl b.2))⟩⟩
  set U : Subgroup X := Subgroup.normalClosure ({z} : Set X) with hU
  haveI hUn : U.Normal := Subgroup.normalClosure_normal
  have hzH : z ∈ H := h.R_le_H (h.A_le_R hzA)
  have hUH : U ≤ H := Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hzH)
  have hzU : z ∈ U := Subgroup.subset_normalClosure (Set.mem_singleton z)
  have hO := endg_goldschmidtOddCore_eq_bot h.F5 hUn hUH
  have hO2 := endg_pCore_eq_bot_of_normal h.o2 hUn
  obtain ⟨hgen, hsimp⟩ := endg_gold_decomp T hzT hzc hab hO hO2
  set 𝒦 : Set (Subgroup X) := {C | IsComponent C ∧ C ≤ U} with h𝒦
  obtain ⟨F, hFcard, hF⟩ := h.count
  have h𝒦F : 𝒦 ⊆ (F : Set (Subgroup X)) := fun C hC => by simpa using hF C hC.1
  haveI : Finite ↥𝒦 := (Finset.finite_toSet F).subset h𝒦F |>.to_subtype
  have hcard : Nat.card ↥𝒦 ≤ 4 := by
    rw [Nat.card_coe_set_eq]
    calc 𝒦.ncard ≤ (F : Set (Subgroup X)).ncard := Set.ncard_le_ncard h𝒦F (Finset.finite_toSet F)
      _ = F.card := Set.ncard_coe_finset F
      _ ≤ 4 := by omega
  obtain ⟨Kp, hKR, hKperf, hKne, hRK, hKnorm, hKidx⟩ := hK
  have hS : ∀ C ∈ 𝒦, ∀ k : X, conjSubgroup k C ∈ 𝒦 := by
    rintro C ⟨hC, hCU⟩ k
    refine ⟨isComponent_conjSubgroup k hC, ?_⟩
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 := hUn.conj_mem _ (hCU hx) k
    simpa [mul_assoc] using h1
  have hfix := endg_perfect_fixes_small_set hKperf 𝒦 hcard hS
  have hex : ∃ Cj ∈ 𝒦, ∃ k ∈ Kp, ∃ c ∈ Cj, k * c ≠ c * k := by
    by_contra hno
    push Not at hno
    have hcentU : U ≤ Subgroup.centralizer (Kp : Set X) := by
      calc U = ⨆ (K : Subgroup X) (_ : IsComponent K ∧ K ≤ U), K := hgen
        _ ≤ Subgroup.centralizer (Kp : Set X) := by
          refine iSup₂_le fun C hC c hc => ?_
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          exact hno C hC k hk c hc
    have hUA : U ⊓ A ≠ ⊥ := by
      intro hb
      have : z ∈ U ⊓ A := ⟨hzU, hzA⟩
      rw [hb, Subgroup.mem_bot] at this
      exact hz1 this
    have hbot := endg_R_inf_centralizer_eq_bot h hUn hUA
    apply hKne
    rw [eq_bot_iff, ← hbot]
    intro k hk
    refine ⟨hKR hk, ?_⟩
    show k ∈ Subgroup.centralizer (U : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := Subgroup.mem_centralizer_iff.mp (hcentU hu) k hk
    exact this.symm
  obtain ⟨Cj, hCj, k0, hk0, c0, hc0, hkc⟩ := hex
  have hCjc : IsComponent Cj := hCj.1
  have hCjU : Cj ≤ U := hCj.2
  have hcen : Subgroup.center ↥Cj = ⊥ := h.comps Cj hCjc
  have hCs : IsSimpleGroup ↥Cj := isSimpleGroup_of_center_eq_bot hCjc hcen
  have hCnc : ∃ a ∈ Cj, ∃ b ∈ Cj, a * b ≠ b * a := by
    obtain ⟨a, b, hab'⟩ := exists_noncomm_of_isComponent hCjc
    exact ⟨a, a.2, b, b.2, fun he => hab' (Subtype.ext he)⟩
  have hKC' : ∀ k ∈ Kp, k ∈ Subgroup.normalizer (Cj : Set X) := fun k hk =>
    conjSubgroup_eq_self_iff.mp (hfix k hk Cj hCj)
  by_cases hCz : ∀ c ∈ Cj, c * z = z * c
  · refine hC8 hKR hKperf hRK hKnorm hCs hCnc hKC' ?_ ⟨k0, hk0, c0, hc0, hkc⟩
    intro c hc
    exact h.N2 c (hUH (hCjU hc)) z hzA hz1 (hCz c hc) t h.t_mem
  ·
    set D : Subgroup X := Subgroup.centralizer (Cj : Set X) ⊓ U with hD
    have hCD : ∀ c ∈ Cj, ∀ d ∈ D, c * d = d * c := fun c hc d hd =>
      Subgroup.mem_centralizer_iff.mp hd.1 c hc
    have hZ : ∀ a ∈ Cj, (∀ c ∈ Cj, c * a = a * c) → a = 1 := by
      intro a ha hall
      have : (⟨a, ha⟩ : ↥Cj) ∈ Subgroup.center ↥Cj := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hall g g.2)
      rw [hcen, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hbot : Cj ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxC, hxD⟩
      exact Subgroup.mem_bot.mpr (hZ x hxC (fun c hc => hCD c hc x hxD))
    have hzCD : z ∈ Cj ⊔ D := by
      have hle : U ≤ Cj ⊔ D := by
        calc U = ⨆ (K : Subgroup X) (_ : IsComponent K ∧ K ≤ U), K := hgen
          _ ≤ Cj ⊔ D := by
            refine iSup₂_le fun C hC => ?_
            by_cases hCC : C = Cj
            · rw [hCC]; exact le_sup_left
            · refine le_sup_of_le_right ?_
              intro x hx
              refine ⟨?_, hC.2 hx⟩
              show x ∈ Subgroup.centralizer (Cj : Set X)
              rw [Subgroup.mem_centralizer_iff]
              intro y hy
              exact (comm_of_ne_component hC.1 hCjc hCC x hx y hy).symm
      exact hle hzU
    have hKz : ∀ k ∈ Kp, k * z = z * k := fun k hk => (h.A_cent z hzA k (hKR hk)).symm
    have hKCe : ∀ k ∈ Kp, ∀ c ∈ Cj, k * c * k⁻¹ ∈ Cj := fun k hk c hc =>
      (Subgroup.mem_normalizer_iff.mp (hKC' k hk) c).mp hc
    have hKD : ∀ k ∈ Kp, ∀ d ∈ D, k * d * k⁻¹ ∈ D := by
      intro k hk d hd
      refine ⟨?_, hUn.conj_mem d hd.2 k⟩
      show k * d * k⁻¹ ∈ Subgroup.centralizer (Cj : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hc' : k⁻¹ * c * k ∈ Cj := by
        have := hKCe k⁻¹ (Kp.inv_mem hk) c hc
        simpa using this
      have h1 := hCD _ hc' d hd
      calc c * (k * d * k⁻¹) = k * ((k⁻¹ * c * k) * d) * k⁻¹ := by group
        _ = k * (d * (k⁻¹ * c * k)) * k⁻¹ := by rw [h1]
        _ = (k * d * k⁻¹) * c := by group
    obtain ⟨a, haCj, ha2, hKa, hiff⟩ :=
      endg_split_elem hCD hbot hZ hzCD (h.A_sq z hzA) hKz hKCe hKD
    have ha1 : a ≠ 1 := fun ha => hCz (hiff.mpr ha)
    have hgold := hsimp Cj hCjc hCjU
    haveI := hCs
    have e : ↥Cj ≃* ↥Cj ⧸ Subgroup.center ↥Cj :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
    obtain ⟨hout, hdich⟩ := endg_gold_facts (endg_goldschmidtSimpleType_congr e hgold)
    exact endg_lemmaP hCs hCnc hout hdich hKperf hKCe haCj ha1 ha2 hKa
      ⟨k0, hk0, c0, hc0, hkc⟩ hKidx

theorem endg_abelian (h : EndgameHyp X A R N H t)
    (hSyl : ∃ T : Sylow 2 X, (T : Subgroup X) ≤ Subgroup.normalizer (A : Set X))
    (hEab : ∀ x ∈ EgenX A, ∀ y ∈ EgenX A, x * y = y * x) : False :=
  endg_abelian_of h hSyl hEab (endg_perfCore_spec h)
    (fun {_ _} hKR hKperf hRK hKnorm hCs hCnc hKC hCt hact =>
      endg_case_eight h hKR hKperf hRK hKnorm hCs hCnc hKC hCt hact)

end AbelianCase

end CFSG.RankThree.GF2n.Stroth80
