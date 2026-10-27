module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.corollary_9_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Corollary 9.3 from BG Section 9

This file contains the support package and proof of Corollary 9.3 from `docs/section9.tex`.
-/

section Section9

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section9_c93_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
    {p : ℕ} {R : Type*} [Group R] [Finite R] (hrank : 3 ≤ primeRank p R) :
    ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ 3 ≤ generatorRank A := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hrank' : 2 < sSup T := by
    exact lt_of_lt_of_le (by decide : 2 < 3) (by simpa [primeRank, T] using hrank)
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section9_c92_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by simp [hTempty]
    exact this hrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAp, hAcomm, htSup_le⟩
  exact ⟨A, hAp, hAcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hrank' htSup_le)⟩

omit [IsMinCE G] in
public theorem CFSG.section9_c93_groupRank_at_least_two_of_generatorRank_subgroup
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 2 ≤ generatorRank A) :
    2 ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : 2 ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section9_c92_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hAgen⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section9_c92_primeRank_le_natCard (p := r) K)
  · exact ⟨q, hq, hqrankK⟩

omit [IsMinCE G] in
private theorem CFSG.section9_c93_groupRank_at_least_two_of_noncyclic_pgroup
    {p : ℕ} [Fact p.Prime] (R : Type*) [Group R] [Finite R] [Fact (IsPGroup p R)]
    (hpodd : p ≠ 2) (hncyc : ¬ IsCyclic R) :
    2 ≤ groupRank R := by
  classical
  obtain ⟨E, _hEnorm, hEcard, hEelem⟩ := lemma_4_5_a (R := R) (p := p) hpodd hncyc
  let : IsElementaryAbelian p E := hEelem
  have hEgen : 2 ≤ generatorRank E :=
    section9_c92_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq (p := p) hEcard
  have hprank : 2 ≤ primeRank p R := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card R, ?_⟩
      intro n hn
      rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
      exact hnA.trans <|
        (section9_c92_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
    · exact ⟨E, IsElementaryAbelian.isPGroup p E, inferInstance, hEgen⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (section9_c92_primeRank_le_natCard (p := q) R)
  · exact ⟨p, Fact.out, hprank⟩

omit [IsMinCE G] in
public theorem CFSG.section9_c93_prime_dvd_card_of_nontrivial_pSubgroup
    {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hBp : IsPGroup p B) (hBnontrivial : Nontrivial B) :
    p ∣ Nat.card G := by
  obtain ⟨n, hn_pos, hBcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := B) (hG := hBp)).mp hBnontrivial
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hp_dvd_B : p ∣ Nat.card B := by
    rw [hBcard, pow_succ']
    exact dvd_mul_right p (p ^ m)
  exact hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)

private theorem CFSG.section9_c93_prime_odd_of_noncyclic_pSubgroup
    {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hBp : IsPGroup p B) (hBnoncyclic : ¬ IsCyclic B) :
    p ≠ 2 := by
  have hBnontrivial : Nontrivial B := by
    by_contra hnt
    let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
    exact hBnoncyclic (isCyclic_of_subsingleton (α := B))
  exact Odd.ne_two_of_dvd_nat IsMinCE.odd_order
    (section9_c93_prime_dvd_card_of_nontrivial_pSubgroup (G := G) hBp hBnontrivial)

omit [IsMinCE G] in
private theorem CFSG.section9_c93_conjNormal_ker_not_isCyclic
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    {D A : Subgroup R} [D.Normal] [IsElementaryAbelian p D]
    (hDcard : Nat.card D = p ^ 2) (hAp : IsPGroup p A)
    (hAgen : 3 ≤ generatorRank A) :
    ¬ IsCyclic (((MulAut.conjNormal (H := D)).comp A.subtype).ker) := by
  classical
  let φ : A →* MulAut D := (MulAut.conjNormal (H := D)).comp A.subtype
  change ¬ IsCyclic φ.ker
  have hφrange_p : IsPGroup p φ.range := by
    have hAtop : IsPGroup p (⊤ : Subgroup A) := by
      simpa using hAp.to_subgroup (⊤ : Subgroup A)
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup A)) hAtop φ
  have hquot_p : IsPGroup p (A ⧸ φ.ker) := hAp.to_quotient φ.ker
  have hquot_card_eq_range : Nat.card (A ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hφcard : Nat.card φ.range ≤ p :=
    natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq
      (A := D) (p := p) hφrange_p (by exact le_of_eq hDcard)
  have hquot_card_le : Nat.card (A ⧸ φ.ker) ≤ p := by
    rw [hquot_card_eq_range]
    exact hφcard
  have hquot_card_dvd : Nat.card (A ⧸ φ.ker) ∣ p := by
    obtain ⟨n, hn⟩ := hquot_p.exists_card_eq
    have hnle : n ≤ 1 := by
      have hpow_le : p ^ n ≤ p ^ 1 := by
        simpa [hn] using hquot_card_le
      exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_le
    have hn_cases : n = 0 ∨ n = 1 := by omega
    rcases hn_cases with rfl | rfl
    · simp [hn]
    · simp [hn]
  have hquotcyc : IsCyclic (A ⧸ φ.ker) :=
    isCyclic_of_card_dvd_prime hquot_card_dvd
  exact not_isCyclic_of_three_le_generatorRank_of_cyclic_quotient hAgen hquotcyc


omit [IsMinCE G] in
private theorem CFSG.section9_c93_conjNormal_ker_image_groupRank_at_least_two
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} {D A : Subgroup P}
    [D.Normal] [IsElementaryAbelian p D]
    (hpodd : p ≠ 2) (hDcard : Nat.card D = p ^ 2) (hAp : IsPGroup p A)
    (hAgen : 3 ≤ generatorRank A) :
    let φ : A →* MulAut D := (MulAut.conjNormal (H := D)).comp A.subtype
    let ψ : A →* G := P.subtype.comp A.subtype
    2 ≤ groupRank (φ.ker.map ψ) := by
  classical
  intro φ ψ
  have hkerp : IsPGroup p φ.ker := hAp.to_subgroup φ.ker
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact Subtype.ext <| Subtype.ext <| by
      simpa [ψ] using hxy
  have hKp : IsPGroup p (φ.ker.map ψ) :=
    IsPGroup.map hkerp ψ
  have hKnoncyc : ¬ IsCyclic (φ.ker.map ψ) := by
    intro hKcyc
    let e : φ.ker ≃* φ.ker.map ψ :=
      Subgroup.equivMapOfInjective (f := ψ) φ.ker hψinj
    have hker_cyc : IsCyclic φ.ker := e.isCyclic.2 hKcyc
    exact
      section9_c93_conjNormal_ker_not_isCyclic
        (p := p) (D := D) (A := A) hDcard hAp hAgen hker_cyc
  let : Fact (IsPGroup p (φ.ker.map ψ)) := ⟨hKp⟩
  exact
    section9_c93_groupRank_at_least_two_of_noncyclic_pgroup
      (p := p) (φ.ker.map ψ) hpodd hKnoncyc

omit [IsMinCE G] in
private theorem CFSG.section9_c93_groupRank_map_subtype_at_least_two_of_elementaryAbelian_card_p_sq
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} {D : Subgroup P}
    [IsElementaryAbelian p D] (hDcard : Nat.card D = p ^ 2) :
    2 ≤ groupRank (D.map P.subtype) := by
  have hDgen : 2 ≤ generatorRank D :=
    section9_c92_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq (p := p) hDcard
  have hgen_map : generatorRank (D.map P.subtype) = generatorRank D :=
    section9_c92_generatorRank_map_injective_eq
      (A := D) P.subtype P.subtype_injective
  have hDmap_p : IsPGroup p (D.map P.subtype) :=
    IsPGroup.map (IsElementaryAbelian.isPGroup p D) P.subtype
  have hDmap_comm : IsMulCommutative (D.map P.subtype) := by
    simpa using (Subgroup.map_isMulCommutative (f := P.subtype) (H := D))
  exact
    section9_c93_groupRank_at_least_two_of_generatorRank_subgroup
      (G := G) (q := p) (Fact.out : Nat.Prime p)
      (A := D.map P.subtype) (K := D.map P.subtype) le_rfl
      hDmap_p hDmap_comm (by simpa [hgen_map] using hDgen)

omit [IsMinCE G] in
private theorem CFSG.section9_c93_generatorRank_conjBy_eq
    (H : Subgroup G) (g : G) :
    generatorRank (H.conjBy g) = generatorRank H := by
  exact
    section9_c92_generatorRank_map_injective_eq
      (A := H) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_conjBy_le_centralizer_conjBy
    {C B : Subgroup G} (hCB : C ≤ Subgroup.centralizer (B : Set G)) (g : G) :
    C.conjBy g ≤ Subgroup.centralizer ((B.conjBy g) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨c, hc, hcx⟩
  change y ∈ B.conjBy g at hy
  rw [Subgroup.conjBy, Subgroup.mem_map] at hy
  rcases hy with ⟨b, hb, hby⟩
  have hcomm : b * c = c * b := (Subgroup.mem_centralizer_iff.mp (hCB hc)) b hb
  rw [← hcx, ← hby]
  simpa [mul_assoc] using congrArg (fun t : G => t * g⁻¹) hcomm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_le_centralizer_symm
    {C B : Subgroup G} (hCB : C ≤ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.centralizer (C : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact ((Subgroup.mem_centralizer_iff.mp (hCB hc)) b hb).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_conjNormal_ker_image_le_centralizer_map
    {P : Subgroup G} {D A : Subgroup P} [D.Normal] :
    let φ : A →* MulAut D := (MulAut.conjNormal (H := D)).comp A.subtype
    let ψ : A →* G := P.subtype.comp A.subtype
    φ.ker.map ψ ≤ Subgroup.centralizer ((D.map P.subtype) : Set G) := by
  intro φ ψ x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Subgroup.mem_map] at hx
  rcases hx with ⟨a, ha, hax⟩
  change y ∈ D.map P.subtype at hy
  rw [Subgroup.mem_map] at hy
  rcases hy with ⟨d, hd, hdy⟩
  have hfix : φ a ⟨(d : P), hd⟩ = ⟨(d : P), hd⟩ := by
    simpa using congrArg (fun f : MulAut D => f ⟨(d : P), hd⟩) ha
  have hconjP : (a : P) * (d : P) * (a : P)⁻¹ = (d : P) := by
    simpa [φ, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
  have hcommP : (d : P) * (a : P) = (a : P) * (d : P) := by
    have := congrArg (fun t : P => t * (a : P)) hconjP
    simpa [mul_assoc] using this.symm
  rw [← hax, ← hdy]
  change ((d : P) : G) * ((a : P) : G) = ((a : P) : G) * ((d : P) : G)
  exact congrArg Subtype.val hcommP

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_conjBy_inv (H : Subgroup G) (g : G) :
    (H.conjBy g).conjBy g⁻¹ = H := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, hyx⟩
    rw [Subgroup.conjBy, Subgroup.mem_map] at hy
    rcases hy with ⟨z, hz, hzy⟩
    have hxz : x = z := by
      rw [← hyx, ← hzy]
      simp [mul_assoc]
    simpa [hxz] using hz
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [mul_assoc]⟩
    · simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_conjBy_inv' (H : Subgroup G) (g : G) :
    (H.conjBy g⁻¹).conjBy g = H := by
  simpa using section9_c93_conjBy_inv (G := G) H g⁻¹

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_top_conjBy (g : G) :
    ((⊤ : Subgroup G).conjBy g) = ⊤ := by
  ext x
  constructor
  · intro _; exact Subgroup.mem_top x
  · intro _
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨g⁻¹ * x * g, Subgroup.mem_top _, by simp [mul_assoc]⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_le_conjBy_inv_of_conjBy_le
    {H K : Subgroup G} {g : G} (hHK : H.conjBy g ≤ K) :
    H ≤ K.conjBy g⁻¹ := by
  intro h hh
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨g * h * g⁻¹, ?_, ?_⟩
  · exact hHK (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh)
  · simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_maximal_conjBy
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (g : G) :
    M.conjBy g ∈ section9MaximalSubgroups G := by
  have h_map : M.conjBy g = Subgroup.map ((MulAut.conj g : G ≃* G) : G →* G) M := rfl
  rw [h_map]
  exact ((MulAut.conj g : G ≃* G).mapSubgroup.isCoatom_iff M).mpr hM

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c93_unique_conjBy
    {H : Subgroup G} (hH : H ∈ section9UniqueSubgroups G) (g : G) :
    H.conjBy g ∈ section9UniqueSubgroups G := by
  classical
  rcases hH with ⟨hHproper, M, hMuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining H := by
    rw [hMuniq]
    simp
  refine ⟨?_, M.conjBy g, ?_⟩
  · intro htop
    have hHtop : H = ⊤ := by
      calc
        H = (H.conjBy g).conjBy g⁻¹ := (section9_c93_conjBy_inv (G := G) H g).symm
        _ = (⊤ : Subgroup G).conjBy g⁻¹ := by rw [htop]
        _ = ⊤ := section9_c93_top_conjBy (G := G) g⁻¹
    exact hHproper hHtop
  · ext N
    constructor
    · intro hN
      have hNinv_max : N.conjBy g⁻¹ ∈ section9MaximalSubgroups G :=
        section9_c93_maximal_conjBy (G := G) hN.1 g⁻¹
      have hH_le_Ninv : H ≤ N.conjBy g⁻¹ :=
        section9_c93_le_conjBy_inv_of_conjBy_le (G := G) hN.2
      have hNinv_cont : N.conjBy g⁻¹ ∈ section9MaximalSubgroupsContaining H :=
        ⟨hNinv_max, hH_le_Ninv⟩
      have hNinv_eq : N.conjBy g⁻¹ = M := by
        have hsingle : N.conjBy g⁻¹ ∈ ({M} : Set (Subgroup G)) := by
          simpa [hMuniq] using hNinv_cont
        simpa using hsingle
      have hN_eq : N = M.conjBy g := by
        calc
          N = (N.conjBy g⁻¹).conjBy g := (section9_c93_conjBy_inv' (G := G) N g).symm
          _ = M.conjBy g := by rw [hNinv_eq]
      simp [hN_eq]
    · intro hN
      have hN_eq : N = M.conjBy g := by simpa using hN
      subst N
      refine ⟨section9_c93_maximal_conjBy (G := G) hMcont.1 g, ?_⟩
      exact Subgroup.map_mono hMcont.2

/-- Corollary 9.3. -/
public theorem CFSG.corollary_9_3
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hAp : IsPGroup p A) (hAcomm : IsMulCommutative A)
    (hBp : IsPGroup p B) (hBnoncyclic : ¬ IsCyclic B)
    (hAunique : A ∈ section9UniqueSubgroups G)
    (hArank : 3 ≤ generatorRank A)
    (hcentralizerRank : 3 ≤ primeRank p (Subgroup.centralizer (B : Set G))) :
    B ∈ section9UniqueSubgroups G := by
  classical
  have hpodd : p ≠ 2 :=
    section9_c93_prime_odd_of_noncyclic_pSubgroup hBp hBnoncyclic
  obtain ⟨C₀, hC₀p, hC₀comm, hC₀gen⟩ :=
    section9_c93_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
      (R := Subgroup.centralizer (B : Set G)) hcentralizerRank
  let C : Subgroup G := C₀.map (Subgroup.centralizer (B : Set G)).subtype
  have hC_le_centB : C ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, _hc, rfl⟩
    exact c.2
  have hCp : IsPGroup p C := by
    dsimp [C]
    exact IsPGroup.map hC₀p (Subgroup.centralizer (B : Set G)).subtype
  have hCcomm : IsMulCommutative C := by
    dsimp [C]
    let : IsMulCommutative C₀ := hC₀comm
    simpa using
      (Subgroup.map_isMulCommutative
        (f := (Subgroup.centralizer (B : Set G)).subtype) (H := C₀))
  have hCgen_eq : generatorRank C = generatorRank C₀ := by
    simpa [C] using
      section9_c92_generatorRank_map_injective_eq
        (A := C₀) (Subgroup.centralizer (B : Set G)).subtype
        (Subgroup.centralizer (B : Set G)).subtype_injective
  have hCgen : 3 ≤ generatorRank C := by
    simpa [hCgen_eq] using hC₀gen
  obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hAp
  obtain ⟨PC, hCPC⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hCp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PC P
  let Bc : Subgroup G := B.conjBy g
  let Cc : Subgroup G := C.conjBy g
  have hCc_le_P : Cc ≤ (P : Subgroup G) := by
    have hCc_le_smul : C.conjBy g ≤ ((g • PC : Sylow p G) : Subgroup G) := by
      change C.map (MulAut.conj g).toMonoidHom ≤
        ((PC : Subgroup G).map (MulAut.conj g).toMonoidHom)
      exact Subgroup.map_mono hCPC
    simpa [Cc, hg] using hCc_le_smul
  have hCc_le_cent_Bc : Cc ≤ Subgroup.centralizer (Bc : Set G) := by
    simpa [Cc, Bc] using section9_c93_conjBy_le_centralizer_conjBy hC_le_centB g
  have hBcp : IsPGroup p Bc := by
    dsimp [Bc]
    exact IsPGroup.map hBp (MulAut.conj g).toMonoidHom
  have hBcnoncyclic : ¬ IsCyclic Bc := by
    intro hcyc
    let e : B ≃* Bc :=
      Subgroup.equivMapOfInjective
        (f := (MulAut.conj g).toMonoidHom) B (MulAut.conj g).injective
    exact hBnoncyclic (e.isCyclic.2 hcyc)
  let Psub : Subgroup G := (P : Subgroup G)
  let Aₚ : Subgroup Psub := A.subgroupOf Psub
  let Cₚ : Subgroup Psub := Cc.subgroupOf Psub
  have hAₚp : IsPGroup p Aₚ := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := Psub) hAP).symm
  have hAₚcomm : IsMulCommutative Aₚ := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := Psub)
  have hAₚgen_eq : generatorRank Aₚ = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := Psub) hAP)
  have hAₚgen : 3 ≤ generatorRank Aₚ := by
    simpa [hAₚgen_eq] using hArank
  have hCcp : IsPGroup p Cc := by
    dsimp [Cc]
    exact IsPGroup.map hCp (MulAut.conj g).toMonoidHom
  have hCccomm : IsMulCommutative Cc := by
    let : IsMulCommutative C := hCcomm
    refine ⟨⟨fun (x y : Cc) => ?_⟩⟩
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    have hx : (x : G) ∈ C.map (MulAut.conj g).toMonoidHom := by
      change (x : G) ∈ Cc
      exact x.2
    have hy : (y : G) ∈ C.map (MulAut.conj g).toMonoidHom := by
      change (y : G) ∈ Cc
      exact y.2
    obtain ⟨x₀, hx₀, hx_eq⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y₀, hy₀, hy_eq⟩ := Subgroup.mem_map.mp hy
    change (MulAut.conj g) x₀ = (x : G) at hx_eq
    change (MulAut.conj g) y₀ = (y : G) at hy_eq
    calc
      (x : G) * (y : G) = (MulAut.conj g) x₀ * (MulAut.conj g) y₀ := by
        rw [hx_eq, hy_eq]
      _ = (MulAut.conj g) (x₀ * y₀) := by rw [map_mul]
      _ = (MulAut.conj g) (y₀ * x₀) := by
        rw [setLike_mul_comm (s := C) hx₀ hy₀]
      _ = (MulAut.conj g) y₀ * (MulAut.conj g) x₀ := by rw [map_mul]
      _ = (y : G) * (x : G) := by rw [hx_eq, hy_eq]
  have hCcgen_eq : generatorRank Cc = generatorRank C := by
    simpa [Cc] using section9_c93_generatorRank_conjBy_eq (G := G) C g
  have hCcgen : 3 ≤ generatorRank Cc := by
    simpa [hCcgen_eq] using hCgen
  have hCₚp : IsPGroup p Cₚ := by
    exact hCcp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Cc) (K := Psub) hCc_le_P).symm
  have hCₚcomm : IsMulCommutative Cₚ := by
    let : IsMulCommutative Cc := hCccomm
    exact Subgroup.subgroupOf_isMulCommutative (H := Cc) (K := Psub)
  have hCₚgen_eq : generatorRank Cₚ = generatorRank Cc := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := Cc) (K := Psub) hCc_le_P)
  have hCₚgen : 3 ≤ generatorRank Cₚ := by
    simpa [hCₚgen_eq] using hCcgen
  have : Fact (IsPGroup p Psub) := ⟨P.isPGroup'⟩
  have hPnoncyc : ¬ IsCyclic Psub := by
    intro hPcyc
    let : IsCyclic Psub := hPcyc
    have hAₚcyc : IsCyclic Aₚ := inferInstance
    have hAcyc : IsCyclic A :=
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := Psub) hAP).isCyclic.1 hAₚcyc
    have hle : generatorRank A ≤ 1 := generatorRank_le_one_of_isCyclic (G := A) hAcyc
    omega
  obtain ⟨D, hDnorm, hDcard, hDelem⟩ :=
    lemma_4_5_a (R := Psub) (p := p) hpodd hPnoncyc
  let : D.Normal := hDnorm
  let : IsElementaryAbelian p D := hDelem
  let DG : Subgroup G := D.map Psub.subtype
  have hDGrank : 2 ≤ groupRank DG := by
    simpa [DG] using
      section9_c93_groupRank_map_subtype_at_least_two_of_elementaryAbelian_card_p_sq
        (G := G) (p := p) (P := Psub) (D := D) hDcard
  let φA : Aₚ →* MulAut D := (MulAut.conjNormal (H := D)).comp Aₚ.subtype
  let ψA : Aₚ →* G := Psub.subtype.comp Aₚ.subtype
  let KA : Subgroup G := φA.ker.map ψA
  have hKArank : 2 ≤ groupRank KA := by
    simpa [KA, φA, ψA] using
      section9_c93_conjNormal_ker_image_groupRank_at_least_two
        (G := G) (p := p) (P := Psub) (D := D) (A := Aₚ)
        hpodd hDcard hAₚp hAₚgen
  have hKA_le_A : KA ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
    exact (a : Aₚ).2
  have hKA_le_centA : KA ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hxA : x ∈ A := hKA_le_A hx
    exact (setLike_mul_comm (s := A) hxA ha).symm
  have hKAunique : KA ∈ section9UniqueSubgroups G :=
    corollary_9_2 (L := A) (K := KA) hAunique hKA_le_centA hKArank
  have hKA_le_cent_DG : KA ≤ Subgroup.centralizer (DG : Set G) := by
    simpa [KA, DG, φA, ψA] using
      section9_c93_conjNormal_ker_image_le_centralizer_map
        (G := G) (P := Psub) (D := D) (A := Aₚ)
  have hDG_le_cent_KA : DG ≤ Subgroup.centralizer (KA : Set G) :=
    section9_c93_le_centralizer_symm hKA_le_cent_DG
  have hDGunique : DG ∈ section9UniqueSubgroups G :=
    corollary_9_2 (L := KA) (K := DG) hKAunique hDG_le_cent_KA hDGrank
  let φC : Cₚ →* MulAut D := (MulAut.conjNormal (H := D)).comp Cₚ.subtype
  let ψC : Cₚ →* G := Psub.subtype.comp Cₚ.subtype
  let KC : Subgroup G := φC.ker.map ψC
  have hKCrank : 2 ≤ groupRank KC := by
    simpa [KC, φC, ψC] using
      section9_c93_conjNormal_ker_image_groupRank_at_least_two
        (G := G) (p := p) (P := Psub) (D := D) (A := Cₚ)
        hpodd hDcard hCₚp hCₚgen
  have hKC_le_cent_DG : KC ≤ Subgroup.centralizer (DG : Set G) := by
    simpa [KC, DG, φC, ψC] using
      section9_c93_conjNormal_ker_image_le_centralizer_map
        (G := G) (P := Psub) (D := D) (A := Cₚ)
  have hKCunique : KC ∈ section9UniqueSubgroups G :=
    corollary_9_2 (L := DG) (K := KC) hDGunique hKC_le_cent_DG hKCrank
  have hKC_le_Cc : KC ≤ Cc := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, _hc, rfl⟩
    exact (c : Cₚ).2
  have hCcrank : 2 ≤ groupRank Cc :=
    section9_c93_groupRank_at_least_two_of_generatorRank_subgroup
      (G := G) (q := p) (Fact.out : Nat.Prime p)
      (A := Cc) (K := Cc) le_rfl hCcp hCccomm
      (le_trans (by decide : 2 ≤ 3) hCcgen)
  have hCc_le_cent_KC : Cc ≤ Subgroup.centralizer (KC : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (setLike_mul_comm (s := Cc) hc (hKC_le_Cc hk)).symm
  have hCcunique : Cc ∈ section9UniqueSubgroups G :=
    corollary_9_2 (L := KC) (K := Cc) hKCunique hCc_le_cent_KC hCcrank
  have hBcrank : 2 ≤ groupRank Bc := by
    let : Fact (IsPGroup p Bc) := ⟨hBcp⟩
    exact section9_c93_groupRank_at_least_two_of_noncyclic_pgroup
      (p := p) Bc hpodd hBcnoncyclic
  have hBc_le_cent_Cc : Bc ≤ Subgroup.centralizer (Cc : Set G) :=
    section9_c93_le_centralizer_symm hCc_le_cent_Bc
  have hBcunique : Bc ∈ section9UniqueSubgroups G :=
    corollary_9_2 (L := Cc) (K := Bc) hCcunique hBc_le_cent_Cc hBcrank
  have hBback : Bc.conjBy g⁻¹ ∈ section9UniqueSubgroups G :=
    section9_c93_unique_conjBy hBcunique g⁻¹
  simpa [Bc, section9_c93_conjBy_inv] using hBback

end Section9
