module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI
import CFSG.LocalAnalysis.WeakClosure81.A6Case.Triangle
import CFSG.LocalAnalysis.WeakClosure81.A6Case.Alt6
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.A6Case

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem mul_involution_mul_inv_eq {G : Type*} [Group G] {a s : G} (ha : a ^ 3 = 1)
    (hs : s * s = 1) (h : s * a * s⁻¹ = a⁻¹) : a * s * a⁻¹ = s * a := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h' : s * a * s = a⁻¹ := by rwa [hs'] at h
  have has : a * s = s * a⁻¹ := by
    have h1 : s * (s * a * s) = s * a⁻¹ := congrArg (fun x => s * x) h'
    rw [show s * (s * a * s) = (s * s) * (a * s) by group, hs, one_mul] at h1
    exact h1
  have haa : a⁻¹ * a⁻¹ = a := by
    have h3 : a * a * a = 1 := by simpa [pow_succ, pow_two, mul_assoc] using ha
    have ha2 : a * a = a⁻¹ := mul_eq_one_iff_eq_inv.mp h3
    rw [← mul_inv_rev, ha2, inv_inv]
  calc a * s * a⁻¹ = (a * s) * a⁻¹ := by rw [mul_assoc]
    _ = (s * a⁻¹) * a⁻¹ := by rw [has]
    _ = s * (a⁻¹ * a⁻¹) := by rw [mul_assoc]
    _ = s * a := by rw [haa]

private theorem conj_mul_eq_inv {G : Type*} [Group G] {d e : G} (hd : d * d = 1)
    (he : e * e = 1) : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
  have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hgoal : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [mul_inv_rev, hd', he']
    calc d * (d * e) * d = d * d * e * d := by group
      _ = e * d := by rw [hd, one_mul]
  exact hgoal

private theorem conj_pow_three_eq_one {G : Type*} [Group G] {d x : G} (hx : x ^ 3 = 1) :
    (d * x * d⁻¹) ^ 3 = 1 := by
  rw [← MulAut.conj_apply d x, ← map_pow, hx, map_one]

private theorem mul_mul_inv_pow_three_eq_one {G : Type*} [Group G] {d e₁ e₂ : G}
    (hd : d * d = 1) (he₁ : e₁ * e₁ = 1) (h : (e₂ * e₁) ^ 3 = 1) :
    ((d * e₂) * (d * e₁)⁻¹) ^ 3 = 1 := by
  have h1 : (d * e₂) * (d * e₁)⁻¹ = d * (e₂ * e₁) * d⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right he₁, inv_eq_of_mul_eq_one_right hd]
    group
  rw [h1]
  exact conj_pow_three_eq_one h

private theorem not_isPGroup_closure_of_map_eq {G : Type*} [Group G] {K : Subgroup G}
    {ψ : ↥K →* alternatingGroup (Fin 6)} {x y : ↥K} {p : alternatingGroup (Fin 6)}
    (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1) (hψ : ψ (x * y) = p) :
    ¬ IsPGroup 2 (Subgroup.closure ({(x : G), (y : G)} : Set G)) := by
  intro h2
  have h2' : IsPGroup 2 (Subgroup.closure ({x, y} : Set ↥K)) :=
    (h2.comap_of_injective K.subtype Subtype.coe_injective).to_le (by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl) <;> exact Subgroup.subset_closure (by simp))
  have himg : IsPGroup 2 ((Subgroup.closure ({x, y} : Set ↥K)).map ψ) := h2'.map ψ
  have hmem : p ∈ (Subgroup.closure ({x, y} : Set ↥K)).map ψ :=
    ⟨x * y, (Subgroup.closure ({x, y} : Set ↥K)).mul_mem
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)), hψ⟩
  have hne : (⟨p, hmem⟩ : ↥((Subgroup.closure ({x, y} : Set ↥K)).map ψ)) ≠ 1 :=
    fun hh => hp1 (congrArg Subtype.val hh)
  have h2dvd : 2 ∣ orderOf (⟨p, hmem⟩ : ↥((Subgroup.closure ({x, y} : Set ↥K)).map ψ)) :=
    himg.dvd_orderOf hne
  have h3dvd : orderOf (⟨p, hmem⟩ : ↥((Subgroup.closure ({x, y} : Set ↥K)).map ψ)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [Subgroup.coe_pow] using hp3))
  exact absurd (h2dvd.trans h3dvd) (by norm_num)

private theorem pow_three_eq_one_of_isBarMap {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    {ψ : ↥K →* alternatingGroup (Fin 6)} (hψ : IsBarMap K (pCoreOf 2 K) ψ) {x : ↥K}
    {p : alternatingGroup (Fin 6)} (hp3 : p ^ 3 = 1) (hψx : ψ x = p)
    (hodd : Odd (orderOf (x : G))) : (x : G) ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx3 : ψ (x ^ 3) = 1 := by rw [map_pow, hψx, hp3]
  have hmem : ((x ^ 3 : ↥K) : G) ∈ pCoreOf 2 K := (hψ.ker_iff (x ^ 3)).mp hx3
  have hodd3 : Odd (orderOf ((x ^ 3 : ↥K) : G)) := by
    have hdvd : orderOf ((x ^ 3 : ↥K) : G) ∣ orderOf (x : G) := by
      rw [Subgroup.coe_pow]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨3, by simp⟩)
    exact hodd.of_dvd_nat hdvd
  have h := eq_one_of_mem_isPGroup_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hmem hodd3
  rwa [Subgroup.coe_pow] at h

private theorem conj_pow_mul_eq_inv_mul_inv {G : Type*} [Group G] {d a b : G} (m : ℕ)
    (ha : d * a * d⁻¹ = a⁻¹) (hb : d * b * d⁻¹ = b⁻¹) :
    d * (a * b) ^ m * d⁻¹ = a⁻¹ * ((a * b) ^ m)⁻¹ * a := by
  have h1 : d * (a * b) * d⁻¹ = a⁻¹ * b⁻¹ := by
    calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [ha, hb]
  calc d * (a * b) ^ m * d⁻¹ = (d * (a * b) * d⁻¹) ^ m := by
        rw [← MulAut.conj_apply d ((a * b) ^ m), map_pow, MulAut.conj_apply]
    _ = (a⁻¹ * b⁻¹) ^ m := by rw [h1]
    _ = a⁻¹ * ((a * b) ^ m)⁻¹ * a := by
        have h2 : (a⁻¹ * (b⁻¹ * a⁻¹) * a) ^ m = a⁻¹ * ((a * b) ^ m)⁻¹ * a := by
          rw [show a⁻¹ * (b⁻¹ * a⁻¹) * a = MulAut.conj a⁻¹ (b⁻¹ * a⁻¹) by
            rw [MulAut.conj_apply, inv_inv]]
          rw [← map_pow, MulAut.conj_apply, inv_inv, ← inv_pow, mul_inv_rev]
        rw [← h2]
        congr 1
        group

private theorem map_mul_of_inverted {K Q : Type*} [Group K] [Group Q] (ψ : K →* Q)
    {s p₁ p₂ : Q} {e₁ e₂ : K} (h₁ : ψ e₁ = s * p₁) (h₂ : ψ e₂ = s * p₂)
    (hs : s⁻¹ = s) (hinv : s * p₂ * s⁻¹ = p₂⁻¹) : ψ (e₂ * e₁) = p₂⁻¹ * p₁ := by
  have hinv' : s * p₂ * s = p₂⁻¹ := by rwa [hs] at hinv
  rw [map_mul, h₂, h₁,
    show s * p₂ * (s * p₁) = (s * p₂ * s) * p₁ by group, hinv']

private theorem mul_self_eq_one_of_mem {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) {d : G} (hd : d ∈ E) : d * d = 1 := by
  have h2 := hE.2 d hd
  rwa [pow_two] at h2

private theorem inverted_pair_aux {p₁ p₂ : alternatingGroup (Fin 6)} (hcomm : Commute p₁ p₂)
    (hp₁3 : p₁ ^ 3 = 1) (hp₂3 : p₂ ^ 3 = 1) (hnotin : p₂ ∉ Subgroup.zpowers p₁) :
    p₂ ≠ 1 ∧ (p₂⁻¹ * p₁) ^ 3 = 1 ∧ p₂⁻¹ * p₁ ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1
    exact hnotin (by rw [h1]; exact Subgroup.one_mem _)
  · rw [(hcomm.symm.inv_left).mul_pow 3, inv_pow, hp₂3, hp₁3, inv_one, one_mul]
  · intro h1
    exact hnotin (by rw [inv_mul_eq_one.mp h1]; exact Subgroup.mem_zpowers p₁)

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

private theorem exists_member_element (h : Hyp711 V H E) :
    ∃ d ∈ V, d ∉ pCoreOf 2 H := by
  obtain ⟨-, -, -, hVO⟩ := mem_omegaSet.mp h.mem
  exact Set.not_subset.mp hVO

private theorem bar_involution (h : Hyp711 V H E)
    {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)}
    (hψ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) ψ) {d : G}
    (hdK : d ∈ kSub V H E) (hd2 : d * d = 1) (hdO : d ∉ pCoreOf 2 H) :
    ψ ⟨d, hdK⟩ * ψ ⟨d, hdK⟩ = 1 ∧ ψ ⟨d, hdK⟩ ≠ 1 := by
  constructor
  · rw [← map_mul, show (⟨d, hdK⟩ : ↥(kSub V H E)) * ⟨d, hdK⟩ = 1 from
      Subtype.ext (by simpa using hd2), map_one]
  · intro h1
    exact hdO (h.pcore_le ((hψ.ker_iff ⟨d, hdK⟩).mp h1))

private theorem isPGroup_ker_of_isBarMap
    {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)}
    (hψ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) ψ) : IsPGroup 2 ψ.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (pCoreOf 2 (kSub V H E)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have heq : ψ.ker = (pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E) := by
    ext k
    rw [MonoidHom.mem_ker, hψ.ker_iff k]
    exact Iff.rfl
  rw [heq]
  exact hp.comap_of_injective (kSub V H E).subtype Subtype.coe_injective

private theorem conj_image_facts (h : Hyp711 V H E)
    {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)} {d : G}
    (hdK : d ∈ kSub V H E) (hdV : d ∈ V) (hd2 : d * d = 1)
    {p : alternatingGroup (Fin 6)} {k : ↥(kSub V H E)} (hk : ψ k = p) (hp3 : p ^ 3 = 1)
    (hs2 : ψ ⟨d, hdK⟩ * ψ ⟨d, hdK⟩ = 1)
    (hinv : ψ ⟨d, hdK⟩ * p * (ψ ⟨d, hdK⟩)⁻¹ = p⁻¹) :
    ∃ (e : G) (heK : e ∈ kSub V H E), e = (k : G) * d * (k : G)⁻¹ ∧
      e ∈ conjSubgroup V (k : G)⁻¹ ∧ e * e = 1 ∧
      ψ ⟨e, heK⟩ = (ψ ⟨d, hdK⟩) * p ∧ ψ (⟨d, hdK⟩ * ⟨e, heK⟩) = p := by
  have heK : (k : G) * d * (k : G)⁻¹ ∈ kSub V H E :=
    (kSub V H E).mul_mem ((kSub V H E).mul_mem k.2 hdK) ((kSub V H E).inv_mem k.2)
  have hψe : ψ ⟨(k : G) * d * (k : G)⁻¹, heK⟩ = (ψ ⟨d, hdK⟩) * p := by
    have heq : (⟨(k : G) * d * (k : G)⁻¹, heK⟩ : ↥(kSub V H E)) = k * ⟨d, hdK⟩ * k⁻¹ :=
      Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_inv, hk]
    exact mul_involution_mul_inv_eq hp3 hs2 hinv
  have hψde : ψ (⟨d, hdK⟩ * ⟨(k : G) * d * (k : G)⁻¹, heK⟩) = p := by
    rw [map_mul, hψe, ← mul_assoc, hs2, one_mul]
  refine ⟨(k : G) * d * (k : G)⁻¹, heK, rfl, ?_, ?_, hψe, hψde⟩
  · rw [mem_conjSubgroup_iff]
    rw [show (k : G)⁻¹ * ((k : G) * d * (k : G)⁻¹) * ((k : G)⁻¹)⁻¹ = d by group]
    exact hdV
  · calc ((k : G) * d * (k : G)⁻¹) * ((k : G) * d * (k : G)⁻¹)
        = (k : G) * (d * d) * (k : G)⁻¹ := by group
      _ = 1 := by rw [hd2, mul_one, mul_inv_cancel]

private theorem odd_cube_of_pair (h : Hyp711 V H E)
    {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)}
    (hψ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) ψ)
    {U U' : Subgroup G} (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    {x₁ x₂ : ↥(kSub V H E)} (hx₁ : (x₁ : G) ∈ U) (hx₂ : (x₂ : G) ∈ U')
    {p : alternatingGroup (Fin 6)} (hψx : ψ (x₁ * x₂) = p) (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1) :
    ((x₁ : G) * (x₂ : G)) ^ 3 = 1 := by
  have hnot : ¬ IsPGroup 2 (Subgroup.closure ({(x₁ : G), (x₂ : G)} : Set G)) :=
    not_isPGroup_closure_of_map_eq hp3 hp1 hψx
  have hodd : Odd (orderOf ((x₁ : G) * (x₂ : G))) :=
    seven_three_A h.elemAbelian h.ti h.abelian hU hU' hx₁ hx₂ hnot
  exact pow_three_eq_one_of_isBarMap hψ hp3 hψx hodd

private theorem three_part_facts {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)}
    (hker : IsPGroup 2 ψ.ker) {ρ σ : G} (hρK : ρ ∈ kSub V H E) (hσK : σ ∈ kSub V H E)
    (hcK : ρ * σ ∈ kSub V H E) (hρ3 : ρ ^ 3 = 1) (hσ3 : σ ^ 3 = 1)
    (hσρ3 : (σ * ρ⁻¹) ^ 3 = 1) {p₁ p₂ : alternatingGroup (Fin 6)}
    (hψρ : ψ ⟨ρ, hρK⟩ = p₁) (hψσ : ψ ⟨σ, hσK⟩ = p₂) (hp₁3 : p₁ ^ 3 = 1) (hp₂3 : p₂ ^ 3 = 1)
    (hcomm : Commute p₁ p₂) :
    Commute ρ ((ρ * σ) ^ (Nat.card ψ.ker) ^ 2) ∧
      ((ρ * σ) ^ (Nat.card ψ.ker) ^ 2) ^ 3 = 1 ∧
      ψ ⟨(ρ * σ) ^ (Nat.card ψ.ker) ^ 2, (kSub V H E).pow_mem hcK _⟩ = p₁ * p₂ := by
  have htri : Commute (ρ * σ) (ρ * (ρ * σ) * ρ⁻¹) :=
    commute_mul_conj_of_pow_three hρ3 hσ3 hσρ3
  have hψσ' : ψ ⟨ρ * σ, hcK⟩ = p₁ * p₂ := by
    rw [show (⟨ρ * σ, hcK⟩ : ↥(kSub V H E)) = ⟨ρ, hρK⟩ * ⟨σ, hσK⟩ from Subtype.ext rfl,
      map_mul, hψρ, hψσ]
  have hcK3 : ψ ⟨ρ * σ, hcK⟩ ^ 3 = 1 := by
    rw [hψσ', hcomm.mul_pow 3, hp₁3, hp₂3, one_mul]
  have hcc : Commute (⟨ρ * σ, hcK⟩ : ↥(kSub V H E))
      (⟨ρ, hρK⟩ * ⟨ρ * σ, hcK⟩ * ⟨ρ, hρK⟩⁻¹) := by
    show (⟨ρ * σ, hcK⟩ : ↥(kSub V H E)) * (⟨ρ, hρK⟩ * ⟨ρ * σ, hcK⟩ * ⟨ρ, hρK⟩⁻¹) =
      (⟨ρ, hρK⟩ * ⟨ρ * σ, hcK⟩ * ⟨ρ, hρK⟩⁻¹) * ⟨ρ * σ, hcK⟩
    exact Subtype.ext htri
  have hcommp : Commute (ψ ⟨ρ, hρK⟩) (ψ ⟨ρ * σ, hcK⟩) := by
    rw [hψρ, hψσ']
    exact (Commute.refl p₁).mul_right hcomm
  obtain ⟨hc_comm, hc_cube, hc_image⟩ :=
    commute_pow_card_ker_of_commute_conj ψ hker hcK3 hcc hcommp
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg Subtype.val hc_comm
  · have h := congrArg Subtype.val hc_cube
    simpa [Subgroup.coe_pow] using h
  · have heq : (⟨(ρ * σ) ^ (Nat.card ψ.ker) ^ 2, (kSub V H E).pow_mem hcK _⟩ :
        ↥(kSub V H E)) = ⟨ρ * σ, hcK⟩ ^ (Nat.card ψ.ker) ^ 2 :=
      Subtype.ext (by rw [Subgroup.coe_pow])
    rw [heq, hc_image, hψσ']

private theorem assemble_final {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)}
    (hker : IsPGroup 2 ψ.ker) {U : Subgroup G} (hU : U ∈ omegaSet V H E) {d : G} (hd : d ∈ U)
    {ρ σ : G} (hρK : ρ ∈ kSub V H E) (hσK : σ ∈ kSub V H E) (hcK : ρ * σ ∈ kSub V H E)
    (hρ3 : ρ ^ 3 = 1) (hσ3 : σ ^ 3 = 1) (hσρ3 : (σ * ρ⁻¹) ^ 3 = 1)
    (hdρ : d * ρ * d⁻¹ = ρ⁻¹) (hdσ : d * σ * d⁻¹ = σ⁻¹)
    {p₁ p₂ : alternatingGroup (Fin 6)} (hψρ : ψ ⟨ρ, hρK⟩ = p₁) (hψσ : ψ ⟨σ, hσK⟩ = p₂)
    (hp₁3 : p₁ ^ 3 = 1) (hp₁1 : p₁ ≠ 1) (hp₂3 : p₂ ^ 3 = 1) (hcomm : Commute p₁ p₂)
    (hnotin : p₂ ∉ Subgroup.zpowers p₁) :
    ∃ U ∈ omegaSet V H E, ∃ d ∈ U, ∃ ρ ∈ kSub V H E, ∃ c ∈ kSub V H E,
      ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧ c ^ 3 = 1 ∧ Commute ρ c ∧ d * ρ * d⁻¹ = ρ⁻¹ ∧
      d * c * d⁻¹ = c⁻¹ ∧ c ∉ Subgroup.zpowers ρ := by
  obtain ⟨hcomm_c, hc_cube, hc_image⟩ :=
    three_part_facts hker hρK hσK hcK hρ3 hσ3 hσρ3 hψρ hψσ hp₁3 hp₂3 hcomm
  refine ⟨U, hU, d, hd, ρ, hρK, (ρ * σ) ^ (Nat.card ψ.ker) ^ 2, (kSub V H E).pow_mem hcK _, hρ3,
    ?_, hc_cube, hcomm_c, hdρ, ?_, ?_⟩
  · intro hρ1
    apply hp₁1
    rw [← hψρ, show (⟨ρ, hρK⟩ : ↥(kSub V H E)) = 1 from Subtype.ext hρ1, map_one]
  · have h1 : d * ((ρ * σ) ^ (Nat.card ψ.ker) ^ 2) * d⁻¹ =
        ρ⁻¹ * (((ρ * σ) ^ (Nat.card ψ.ker) ^ 2))⁻¹ * ρ :=
      conj_pow_mul_eq_inv_mul_inv _ hdρ hdσ
    rw [h1, mul_assoc, ← hcomm_c.inv_right.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro hmem
    have hψmem : ψ ⟨(ρ * σ) ^ (Nat.card ψ.ker) ^ 2, (kSub V H E).pow_mem hcK _⟩ ∈
        Subgroup.zpowers (ψ ⟨ρ, hρK⟩) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [← map_zpow]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hn
    rw [hψρ, hc_image] at hψmem
    refine hnotin ?_
    have h : p₂ = p₁⁻¹ * (p₁ * p₂) := by group
    rw [h]
    exact (Subgroup.zpowers p₁).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers p₁)) hψmem

theorem exists_inverted_pair_of_isBarMap (h : Hyp711 V H E)
    {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)}
    (hψ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) ψ) :
    ∃ U ∈ omegaSet V H E, ∃ d ∈ U, ∃ ρ ∈ kSub V H E, ∃ c ∈ kSub V H E,
      ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧ c ^ 3 = 1 ∧ Commute ρ c ∧ d * ρ * d⁻¹ = ρ⁻¹ ∧
      d * c * d⁻¹ = c⁻¹ ∧ c ∉ Subgroup.zpowers ρ := by
  obtain ⟨d, hdV, hdO⟩ := exists_member_element h
  have hd2 : d * d = 1 := mul_self_eq_one_of_mem h.elemAbelian hdV
  have hdK : d ∈ kSub V H E := le_kSub h.mem hdV
  obtain ⟨hs2, hs1⟩ := bar_involution h hψ hdK hd2 hdO
  obtain ⟨p₁, p₂, hp₁3, hp₂3, hp₁1, hcomm, hinv₁, hinv₂, hnotin⟩ :=
    exists_inverted_pair (ψ ⟨d, hdK⟩) hs2 hs1
  obtain ⟨hp₂1, hp₂₁3, hp₂₁1⟩ := inverted_pair_aux hcomm hp₁3 hp₂3 hnotin
  obtain ⟨k₁, hk₁⟩ := hψ.surjective p₁
  obtain ⟨k₂, hk₂⟩ := hψ.surjective p₂
  obtain ⟨e₁, he₁K, he₁, he₁mem, he₁2, hψe₁, hψde₁⟩ :=
    conj_image_facts h hdK hdV hd2 hk₁ hp₁3 hs2 hinv₁
  obtain ⟨e₂, he₂K, he₂, he₂mem, he₂2, hψe₂, hψde₂⟩ :=
    conj_image_facts h hdK hdV hd2 hk₂ hp₂3 hs2 hinv₂
  have hψe₂e₁ : ψ (⟨e₂, he₂K⟩ * ⟨e₁, he₁K⟩) = p₂⁻¹ * p₁ :=
    map_mul_of_inverted ψ hψe₁ hψe₂ (inv_eq_of_mul_eq_one_right hs2) hinv₂
  have hKle : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hU₁ : conjSubgroup V (k₁ : G)⁻¹ ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (H.inv_mem (hKle k₁.2))
  have hU₂ : conjSubgroup V (k₂ : G)⁻¹ ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (H.inv_mem (hKle k₂.2))
  have hρ3 : (d * e₁) ^ 3 = 1 :=
    odd_cube_of_pair h hψ h.mem hU₁ hdV he₁mem hψde₁ hp₁3 hp₁1
  have hσ3 : (d * e₂) ^ 3 = 1 :=
    odd_cube_of_pair h hψ h.mem hU₂ hdV he₂mem hψde₂ hp₂3 hp₂1
  have hee3 : (e₂ * e₁) ^ 3 = 1 :=
    odd_cube_of_pair h hψ hU₂ hU₁ he₂mem he₁mem hψe₂e₁ hp₂₁3 hp₂₁1
  have hσρ3 : ((d * e₂) * (d * e₁)⁻¹) ^ 3 = 1 :=
    mul_mul_inv_pow_three_eq_one hd2 he₁2 hee3
  have hdρ : d * (d * e₁) * d⁻¹ = (d * e₁)⁻¹ := conj_mul_eq_inv hd2 he₁2
  have hdσ : d * (d * e₂) * d⁻¹ = (d * e₂)⁻¹ := conj_mul_eq_inv hd2 he₂2
  have hρK : d * e₁ ∈ kSub V H E := (kSub V H E).mul_mem hdK he₁K
  have hσK : d * e₂ ∈ kSub V H E := (kSub V H E).mul_mem hdK he₂K
  have hcK : (d * e₁) * (d * e₂) ∈ kSub V H E := (kSub V H E).mul_mem hρK hσK
  have hψρ : ψ ⟨d * e₁, hρK⟩ = p₁ := hψde₁
  have hψσ : ψ ⟨d * e₂, hσK⟩ = p₂ := hψde₂
  exact assemble_final (isPGroup_ker_of_isBarMap hψ) h.mem hdV hρK hσK hcK hρ3 hσ3 hσρ3 hdρ hdσ
    hψρ hψσ hp₁3 hp₁1 hp₂3 hcomm hnotin

end CFSG.LocalAnalysis.WeakClosure81.A6Case
