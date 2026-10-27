module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24
public import Certificates.Certificate7166

public section

namespace CFSG.Quasithin.H13.Ch4.HatM

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Quasithin.H13.Ch4.HatChk
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Blueprint
open CFSG.EvenSporadicStandard.HypOne CFSG.LieType.BorelTits

theorem rep_arr24 (g : Equiv.Perm (Fin 24)) : Rep 24 (arr24 g) g := fun x => by
  rw [arr24, getElem!_ofFn_nat _ x.2]

theorem permOfArr_arr24 (g : Equiv.Perm (Fin 24)) : permOfArr 24 (arr24 g) = g :=
  permOfArr_eq_of_rep (rep_arr24 g)

theorem m24W_mem (s : String) : m24W s ∈ NativeSporadic.M24 :=
  evalCodes_mem _ (fun g hg => by
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact m24a.2
    · exact m24b.2) _

theorem mem_wordGens {l : List String} {x : Array ℕ}
    (hx : x ∈ (l.map fun s => arr24 (m24W s)).toArray) : ∃ s, x = arr24 (m24W s) := by
  rw [List.mem_toArray, List.mem_map] at hx
  obtain ⟨s, -, hs⟩ := hx
  exact ⟨s, hs.symm⟩

theorem getElem!_mem {a : Array (Array ℕ)} {k : ℕ} (hk : k < a.size) : a[k]! ∈ a := by
  rw [getElem!_pos a k hk]
  exact Array.getElem_mem hk

theorem s1Gens_mem (k : ℕ) (hk : k < s1Gens.size) :
    permOfArr 24 s1Gens[k]! ∈ NativeSporadic.M24 := by
  have hmem : s1Gens[k]! ∈ (s1WordStrs.map fun s => arr24 (m24W s)).toArray := getElem!_mem hk
  obtain ⟨s, hs⟩ := mem_wordGens hmem
  rw [hs, permOfArr_arr24]
  exact m24W_mem s

theorem p1Gens_mem (k : ℕ) (hk : k < p1Gens.size) :
    permOfArr 24 p1Gens[k]! ∈ NativeSporadic.M24 := by
  have hmem : p1Gens[k]! ∈ (p1WordStrs.map fun s => arr24 (m24W s)).toArray := getElem!_mem hk
  obtain ⟨s, hs⟩ := mem_wordGens hmem
  rw [hs, permOfArr_arr24]
  exact m24W_mem s

theorem check_parts :
    fpfA 24 r1Arr = true ∧ enumOK 24 s1Gens ps24 cS1 = true ∧ cS1.pts.size = 512 ∧
      (∀ k < s1Gens.size, cmA 24 s1Gens[k]! r1Arr = true) ∧ fpfPairOK 24 s1Gens cS1 r1Arr = true ∧
      validA 24 cArr = true ∧ cmA 24 cArr r2Arr = true ∧
      enumOK 24 p1Gens ps24 cP1 = true ∧ cP1.pts.size = 1024 ∧
      (∀ k < p1Gens.size, cmA 24 p1Gens[k]! r2Arr = true) ∧
      enumOK 24 p2Gens ps24 cP2 = true ∧ cP2.pts.size = 1024 ∧
      coverOK 24 63 ps24 cP1 cP2 clsP = true := by
  have h := Certificates.certificate7166
  simp only [hatM24Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, allLt_iff.1 h4, h5, h6, h7, h8, h9, allLt_iff.1 h10, h11, h12, h13⟩

theorem ps24_lt : ∀ q ∈ ps24, q < 24 := fun _ hq => List.mem_range.1 hq

theorem card_centralizer_rep1 :
    Nat.card ↥(NativeSporadic.M24 ⊓ Subgroup.centralizer
      ({m24Rep1} : Set (Equiv.Perm (Fin 24)))) = 2 ^ 9 * 15 := by
  have h := M24.centralizerIn_rep1
  rw [centralizerIn] at h
  rw [h]
  exact m24_rep_data1.2.2.2.1.trans (by norm_num)

theorem card_centralizer_rep2 :
    Nat.card ↥(NativeSporadic.M24 ⊓ Subgroup.centralizer
      ({m24Rep2} : Set (Equiv.Perm (Fin 24)))) = 2 ^ 10 * 21 := by
  have h := M24.centralizerIn_rep2
  rw [centralizerIn] at h
  rw [h]
  exact m24_rep_data2.2.2.2.1.trans (by norm_num)

theorem rep_r2 : Rep 24 r2Arr m24Rep2 := rep_arr24 _

theorem rep_r1 : Rep 24 r1Arr m24Rep1 := rep_arr24 _

theorem hatCoreAt_rep2 :
    HatCoreAt (Equiv.Perm (Fin 24)) NativeSporadic.M24 m24Rep2 := by
  obtain ⟨-, -, -, -, -, hvc, hcr, hP1, hP1c, hP1r, hP2, hP2c, hcov⟩ := check_parts
  have hval1 : ∀ k < p1Gens.size, validA 24 p1Gens[k]! = true := fun k hk =>
    enumOK_gens_valid hP1 hk
  have hP1C := HatS.closure_le_of_gens rep_r2 hval1 p1Gens_mem hP1r
  have hcC : permOfArr 24 cArr ∈ NativeSporadic.M24 ⊓
      Subgroup.centralizer ({m24Rep2} : Set (Equiv.Perm (Fin 24))) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [cArr, permOfArr_arr24]
      exact m24W_mem _
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (cmA_iff (rep_of_validA hvc) rep_r2).1 hcr
  exact HatS.hatCoreAt_of_coverOK ps24_lt card_centralizer_rep2 (by decide) hP1C
    (HatS.closure_conj_le hvc hcC hval1 hP1C) hP1 hP1c hP2 hP2c hcov

theorem fpf_conj {g : Equiv.Perm (Fin 24)} (hg : ∀ i, g i ≠ i) (x : Equiv.Perm (Fin 24)) :
    ∀ i, (x * g * x⁻¹) i ≠ i := by
  intro i h
  apply hg (x⁻¹ i)
  have h1 : x (g (x⁻¹ i)) = i := h
  calc g (x⁻¹ i) = x⁻¹ (x (g (x⁻¹ i))) := by simp
    _ = x⁻¹ i := by rw [h1]

theorem hatCoreAt_rep1 :
    HatCoreAt (Equiv.Perm (Fin 24)) NativeSporadic.M24 m24Rep1 := by
  intro t U S hUM hSM htM hUc hU hS2 hS hUS hzU hzS hz2 hz1 htS htU htz hzt _
  obtain ⟨hr1f, hS1, hS1c, hS1r, hfpf, -⟩ := check_parts
  set C := NativeSporadic.M24 ⊓ Subgroup.centralizer ({m24Rep1} : Set (Equiv.Perm (Fin 24)))
    with hCdef
  have hval1 : ∀ k < s1Gens.size, validA 24 s1Gens[k]! = true := fun k hk =>
    enumOK_gens_valid hS1 hk
  have hS1C : Subgroup.closure (permsA 24 s1Gens) ≤ C :=
    HatS.closure_le_of_gens rep_r1 hval1 s1Gens_mem hS1r
  have hcard : Nat.card C = 2 ^ 9 * 15 := card_centralizer_rep1
  have hsyl1 : IsSylowTwoOf (Subgroup.closure (permsA 24 s1Gens)) C :=
    HatS.isSylowTwoOf_of_card hS1C ((enumOK_spec ps24_lt hS1).2.1.trans hS1c) hcard (by decide)
  have hSC : S ≤ C := fun s hs => Subgroup.mem_inf.mpr ⟨hSM hs, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzS s hs)⟩
  have hsylS : IsSylowTwoOf S C := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS2
    have hdvd : 2 ^ a ∣ 2 ^ 9 * 15 := by
      rw [← ha, ← hcard]
      exact Subgroup.card_dvd_of_le hSC
    have ha9 : a ≤ 9 := by
      by_contra h
      have h1 : 2 ^ 10 ∣ 2 ^ 9 * 15 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at h1
    have ha9' : 9 ≤ a := by
      by_contra h
      have h1 : 2 ^ a ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : a = 9 := le_antisymm ha9 ha9'
    subst this
    exact HatS.isSylowTwoOf_of_card hSC ha hcard (by decide)
  obtain ⟨h, hhC, hconj⟩ := exists_conj_of_isSylowTwoOf hsyl1 hsylS
  obtain ⟨-, hhr⟩ := Subgroup.mem_inf.mp hhC
  rw [Subgroup.mem_centralizer_singleton_iff] at hhr
  have hr1fpf : ∀ i, m24Rep1 i ≠ i := (fpfA_iff rep_r1).1 hr1f
  set u := t * m24Rep1 * t⁻¹ with hu
  have huS : u ∈ S := hUS ((Subgroup.mem_normalizer_iff.mp htU _).mp hzU)
  have huC : ∀ s ∈ S, s * u = u * s := by
    intro s hs
    have hs' : t⁻¹ * s * t ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htS) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hzS _ hs'
    rw [hu]
    calc s * (t * m24Rep1 * t⁻¹) = t * ((t⁻¹ * s * t) * m24Rep1) * t⁻¹ := by group
      _ = t * (m24Rep1 * (t⁻¹ * s * t)) * t⁻¹ := by rw [h1]
      _ = t * m24Rep1 * t⁻¹ * s := by group
  set b := h⁻¹ * u * h with hb
  have hbS1 : b ∈ Subgroup.closure (permsA 24 s1Gens) := (hconj u).mp huS
  have hbc : ∀ k < s1Gens.size, permOfArr 24 s1Gens[k]! * b = b * permOfArr 24 s1Gens[k]! := by
    intro k hk
    have hgS1 : permOfArr 24 s1Gens[k]! ∈ Subgroup.closure (permsA 24 s1Gens) :=
      Subgroup.subset_closure (mem_permsA hk)
    set g := permOfArr 24 s1Gens[k]! with hg
    have hgS : h * g * h⁻¹ ∈ S := by
      have := (hconj (h * g * h⁻¹)).mpr (by simpa [mul_assoc] using hgS1)
      exact this
    have h1 := huC _ hgS
    calc g * b = h⁻¹ * ((h * g * h⁻¹) * u) * h := by rw [hb]; group
      _ = h⁻¹ * (u * (h * g * h⁻¹)) * h := by rw [h1]
      _ = b * g := by rw [hb]; group
  have hbf : ∀ i, b i ≠ i := by
    have := fpf_conj hr1fpf (h⁻¹ * t)
    intro i
    have e : b = (h⁻¹ * t) * m24Rep1 * (h⁻¹ * t)⁻¹ := by rw [hb, hu]; group
    rw [e]
    exact this i
  have hbr : b ≠ m24Rep1 := by
    intro hbr
    apply htz
    have e : u = h * b * h⁻¹ := by rw [hb]; group
    rw [e, hbr, hhr]
    group
  obtain ⟨i, hi⟩ := exists_fixed_of_fpfPairOK ps24_lt hS1 rep_r1 hfpf hbS1 hbc hbf hbr
  have hz2' : m24Rep1⁻¹ = m24Rep1 := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
  have e : m24Rep1 * b = (h⁻¹ * t ^ 2) * m24Rep1 * (h⁻¹ * t ^ 2)⁻¹ := by
    have h1 : m24Rep1 * u = (t ^ 2 * m24Rep1 * (t ^ 2)⁻¹)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hzt
    have h2 : m24Rep1 = h⁻¹ * m24Rep1 * h := by
      rw [mul_assoc, ← hhr]; group
    calc m24Rep1 * b = h⁻¹ * (m24Rep1 * u) * h := by
          rw [hb]; nth_rewrite 1 [h2]; group
      _ = h⁻¹ * (t ^ 2 * m24Rep1⁻¹ * (t ^ 2)⁻¹) * h := by rw [h1]; group
      _ = (h⁻¹ * t ^ 2) * m24Rep1 * (h⁻¹ * t ^ 2)⁻¹ := by rw [hz2']; group
  rw [e] at hi
  exact fpf_conj hr1fpf _ i hi

theorem hatCoreAmb_m24 :
    HatCoreAmb (Equiv.Perm (Fin 24)) NativeSporadic.M24 := by
  intro z t U S hUM hSM htM hUc hU hS2 hS hUS hzU hzS hz2 hz1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzM : z ∈ NativeSporadic.M24 := hUM hzU
  obtain ⟨r, hr, c, hc, hzc⟩ :=
    M24.involution_cover.1 z (by simpa using hzM) (orderOf_eq_prime hz2 hz1)
  have hrep : HatCoreAt (Equiv.Perm (Fin 24)) NativeSporadic.M24 r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hatCoreAt_rep1
    · exact hatCoreAt_rep2
  subst hzc
  exact HatS.hatCoreAt_conj hc hrep t U S hUM hSM htM hUc hU hS2 hS hUS hzU hzS hz2 hz1

end CFSG.Quasithin.H13.Ch4.HatM
