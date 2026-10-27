module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusHall
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusEdge
public import CFSG.Quasithin.EmptyFaithful.S146xU1Orb

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

section Local

variable {G₀ G₁ G₂ : Subgroup G} {ν : CosetGeom G₀ G₁ G₂} {L : Subgroup G}

theorem BenderLocal.exists_fixed_nbrs_ne (hB : BenderLocal ν L) {y y₀ : CosetGeom G₀ G₁ G₂}
    (hy : y ∈ nbrs ν) (hy₀ : y₀ ∈ nbrs ν) (hne : y₀ ≠ y) {T : Subgroup G}
    (hTH : T ≤ stab ν ⊓ stab y) (hHT : stab ν ⊓ stab y ≤ Subgroup.normalizer (T : Set G))
    (hT : IsPGroup 2 T) (hodd : Odd (T.relIndex (stab ν ⊓ stab y))) {X : Subgroup G}
    (hX : IsEdgeHall ν y X) : ∃ y' ∈ nbrs ν, y' ≠ y ∧ X ≤ stab y' := by
  obtain ⟨U, hUL, hU2, hUy, hUtr, -, -⟩ := hB.unipotent y hy
  let H : Subgroup G := stab ν ⊓ stab y
  let K : Subgroup G := H ⊓ stab y₀
  have hUH : U ≤ H := le_inf (hUL.trans hB.le_stab) hUy
  have hKH : K ≤ H := inf_le_left
  have hcover : ∀ h ∈ H, ∃ u ∈ U, u⁻¹ * h ∈ K := by
    intro h hh
    have hhν : h ∈ stab ν := hh.1
    have hhy : h ∈ stab y := hh.2
    let h' : ↥G₀ := ⟨h, CosetGeom.stab_le ν hhν⟩
    have hhy' : h' • y = y := CosetGeom.smul_eq_of_mem_stab hhy
    have h'ν : h' • ν = ν := CosetGeom.smul_eq_of_mem_stab hhν
    have hmem : h' • y₀ ∈ nbrs ν := by
      rw [← h'ν]
      exact (CosetGeom.smul_adj h').mpr hy₀
    have hne' : h' • y₀ ≠ y := by
      intro heq
      have h1 : h'⁻¹ • y = y₀ := by rw [← heq, inv_smul_smul]
      have h2 : h'⁻¹ • y = y := by
        calc h'⁻¹ • y = h'⁻¹ • (h' • y) := by rw [hhy']
          _ = y := by rw [← mul_smul, inv_mul_cancel, one_smul]
      exact hne (h1.symm.trans h2)
    obtain ⟨u, huU, hu⟩ := hUtr y₀ hy₀ (h' • y₀) hmem hne hne'
    have huH : (u : G) ∈ H := hUH huU
    have huν : (u : G) ∈ stab ν := huH.1
    have huy : (u : G) ∈ stab y := huH.2
    have huν' : (u : G)⁻¹ ∈ stab ν := (stab ν).inv_mem huν
    have huy' : (u : G)⁻¹ ∈ stab y := (stab y).inv_mem huy
    have hGH : (u : G)⁻¹ * h ∈ G₀ := CosetGeom.stab_le ν (mul_mem huν' hhν)
    refine ⟨(u : G), huU, ⟨⟨mul_mem huν' hhν, mul_mem huy' hhy⟩, ?_⟩⟩
    refine CosetGeom.mem_stab_of_smul_eq (g := ⟨(u : G)⁻¹ * h, hGH⟩) ?_
    change (⟨(u : G)⁻¹ * h, hGH⟩ : ↥G₀) • y₀ = y₀
    rw [show (⟨(u : G)⁻¹ * h, hGH⟩ : ↥G₀) = u⁻¹ * h' from rfl, mul_smul, ← hu,
      inv_smul_smul]
  have hmul : ∀ h ∈ H, ∃ u ∈ U, ∃ k ∈ K, h = u * k := by
    intro h hh
    obtain ⟨u, huU, huk⟩ := hcover h hh
    exact ⟨u, huU, u⁻¹ * h, huk, by group⟩
  have hidx : K.relIndex H = (K ⊓ U).relIndex U :=
    (CFSG.Quasithin.relIndex_inf_eq_of_forall_mul hUH hmul).symm
  obtain ⟨a, ha⟩ := hU2.exists_card_eq
  have hdvd : K.relIndex H ∣ 2 ^ a := by
    rw [hidx]
    simpa [ha] using Subgroup.relIndex_dvd_card (K ⊓ U) U
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨k, hk⟩ := hX.2.2
  obtain ⟨c, hcH, hc⟩ := exists_conj_le_of_hall hTH hHT hT hodd hX.1 hX.2.1 hk hKH hm
  let c' : ↥G₀ := ⟨c, CosetGeom.stab_le ν hcH.1⟩
  refine ⟨c'⁻¹ • y₀, ?_, ?_, ?_⟩
  · have hfix : c'⁻¹ • ν = ν := by
      calc c'⁻¹ • ν = c'⁻¹ • (c' • ν) := by
            rw [CosetGeom.smul_eq_of_mem_stab (g := c') hcH.1]
        _ = ν := by rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [← hfix]
    exact (CosetGeom.smul_adj c'⁻¹).mpr hy₀
  · intro heq
    have h1 : y₀ = c' • (c'⁻¹ • y₀) := (smul_inv_smul c' y₀).symm
    rw [heq, CosetGeom.smul_eq_of_mem_stab hcH.2] at h1
    exact hne h1
  · intro x hxX
    have hxν : x ∈ stab ν := (hX.1 hxX).1
    have hxG : x ∈ G₀ := CosetGeom.stab_le ν hxν
    have hcx : c * x * c⁻¹ ∈ stab y₀ := (hc x hxX).2
    have hkey : (c' * (⟨x, hxG⟩ : ↥G₀) * c'⁻¹) • y₀ = y₀ := CosetGeom.smul_eq_of_mem_stab hcx
    refine CosetGeom.mem_stab_of_smul_eq (g := ⟨x, hxG⟩) ?_
    change (⟨x, hxG⟩ : ↥G₀) • (c'⁻¹ • y₀) = c'⁻¹ • y₀
    calc (⟨x, hxG⟩ : ↥G₀) • (c'⁻¹ • y₀) = ((⟨x, hxG⟩ : ↥G₀) * c'⁻¹) • y₀ :=
          (mul_smul _ _ _).symm
      _ = (c'⁻¹ * (c' * (⟨x, hxG⟩ : ↥G₀) * c'⁻¹)) • y₀ := by
          rw [show c'⁻¹ * (c' * (⟨x, hxG⟩ : ↥G₀) * c'⁻¹) = (⟨x, hxG⟩ : ↥G₀) * c'⁻¹ by
            group]
      _ = c'⁻¹ • ((c' * (⟨x, hxG⟩ : ↥G₀) * c'⁻¹) • y₀) := mul_smul _ _ _
      _ = c'⁻¹ • y₀ := by rw [hkey]

theorem CartanLocal.eq_or_eq_of_isEdgeHall (hB : BenderLocal ν L) (hC : CartanLocal ν L)
    {y y' ε : CosetGeom G₀ G₁ G₂} (hy : y ∈ nbrs ν) (hy' : y' ∈ nbrs ν) (hne : y ≠ y')
    (hε : ε ∈ nbrs ν) {X : Subgroup G} (hX : IsEdgeHall ν y X) (hXy' : X ≤ stab y')
    (hXε : X ≤ stab ε) : ε = y ∨ ε = y' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := stab ν ⊓ stab y
  let C : Subgroup G := L ⊓ stab y ⊓ stab y'
  have hCH : C ≤ H :=
    le_inf ((inf_le_left.trans inf_le_left).trans hB.le_stab) (inf_le_left.trans inf_le_right)
  have hXH : X ≤ H := hX.1
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := by
    have h1 : X ≤ Subgroup.normalizer (L : Set G) := fun x hx => hB.normal (hX.1 hx).1
    have h2 : X ≤ Subgroup.normalizer ((stab y : Subgroup G) : Set G) :=
      fun x hx => Subgroup.le_normalizer ((hX.1 hx).2)
    have h3 : X ≤ Subgroup.normalizer ((stab y' : Subgroup G) : Set G) :=
      hXy'.trans Subgroup.le_normalizer
    have h4 : X ≤ Subgroup.normalizer ((L ⊓ stab y : Subgroup G) : Set G) :=
      (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf h4 h3).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨k, hk⟩ := hX.2.2
  obtain ⟨m, hm⟩ := relIndex_two_pow_of_le_normalizer hXH hCH hXC hk
  let P : Sylow 2 ↥C := Classical.choice Sylow.nonempty
  have hPodd : Odd (P : Subgroup ↥C).index := by
    have h := Sylow.not_dvd_index P
    exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hPle : (P : Subgroup ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hle : (P : Subgroup ↥C).map C.subtype ≤ stab ε ⊓ C := by
    refine le_inf (fun g hg => ?_) hPle
    obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hg
    have hxC : (x : G) ∈ C := hPle (Subgroup.mem_map_of_mem C.subtype hxP)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨x, hxP⟩
    have hxk : (x : G) ^ 2 ^ n = 1 := by
      have h1 : (⟨x, hxP⟩ : ↥(P : Subgroup ↥C)) ^ 2 ^ n = 1 := by
        rw [← hn]; exact pow_orderOf_eq_one _
      have h2 := congrArg (fun y : ↥(P : Subgroup ↥C) => ((y : ↥C) : G)) h1
      simpa using h2
    exact CosetGeom.ballStab_le_stab_of_dist_le
      (CosetGeom.dist_eq_one_iff_adj.mpr hε).le (hC.two_elt y hy y' hy' hne (x : G) hxC n hxk)
  have hrel : ((P : Subgroup ↥C).map C.subtype).relIndex C = (P : Subgroup ↥C).index := by
    have h := Subgroup.relIndex_map_map_of_injective (f := C.subtype) (P : Subgroup ↥C) ⊤
      C.subtype_injective
    rwa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  have hoddC : Odd ((stab ε ⊓ C).relIndex C) :=
    Odd.of_dvd_nat hPodd (hrel ▸ Subgroup.relIndex_dvd_of_le_left C hle)
  have hoddE : Odd ((stab ε).relIndex C) := by
    rw [← Subgroup.inf_relIndex_right (stab ε) C]
    exact hoddC
  exact hC.fix_two y hy y' hy' hne ε hε (le_of_relIndex_odd hXε hoddE hm)

end Local

namespace Setting

variable {L₁ L₂ S Z : Subgroup G}

theorem exists_fixed_nbrs_eq_pair (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂))
    {ν y : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hν : vtype ν = false)
    (hy : y ∈ nbrs ν) {X : Subgroup G} (hX : IsEdgeHall ν y X) :
    ∃ y' ∈ nbrs ν, y' ≠ y ∧ ∀ ε ∈ nbrs ν, X ≤ stab ε ↔ ε = y ∨ ε = y' := by
  obtain ⟨L, hB, hCL⟩ := hs.exists_benderLocal_cartanLocal hK hC hν
  obtain ⟨y₀, hy₀, hne⟩ := hs.exists_nbrs_ne hν hy
  obtain ⟨T, hTH, hHT, hT, hodd⟩ := hs.exists_normal_two_edge hν hy
  obtain ⟨y', hy', hney', hXy'⟩ :=
    BenderLocal.exists_fixed_nbrs_ne hB hy hy₀ hne hTH hHT hT hodd hX
  refine ⟨y', hy', hney', ?_⟩
  intro ε hε
  constructor
  · intro hXε
    exact CartanLocal.eq_or_eq_of_isEdgeHall hB hCL hy hy' (Ne.symm hney') hε hX hXy' hXε
  · rintro (rfl | rfl)
    · exact fun x hx => (hX.1 hx).2
    · exact hXy'

end Setting

end CFSG.Quasithin.F112Crit

end
