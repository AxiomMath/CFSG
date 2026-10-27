module

public import CFSG.RankThree.PartOne.MB3.FieldSetting
public import CFSG.RankThree.PartOne.S11d.InnerBasic
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.MB3.Orbit

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_pow_order_thetaComponentsAt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hG : CFSG.Assembly.evenRank G ≤ 3) {a : G} {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p a)
    {x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G)) (hord : ∃ k : ℕ, orderOf x = p ^ k) :
    x ∈ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsAt_iff.mp hY
  have hH : CFSG.Assembly.evenRank (Subgroup.centralizer ({a} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans hG
  have hord' : ∃ k : ℕ, orderOf (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) = p ^ k := by
    obtain ⟨k, hk⟩ := hord
    exact ⟨k, by rwa [Subgroup.orderOf_mk]⟩
  have hmem := selected_prime_elements_normalize_theta_components.1
    (Subgroup.centralizer ({a} : Set G)) hH p hp hp3 _ hord' _ hY'
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ Subgroup.centralizer ({a} : Set G)
  · have := Subgroup.mem_normalizer_iff.mp hmem ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY
      exact absurd (hYC hgY) hg
    · intro hxgY
      have h1 : x * g * x⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := hYC hxgY
      refine absurd ?_ hg
      have h2 := mul_mem (mul_mem (inv_mem hx) h1) hx
      simpa [mul_assoc] using h2

theorem normalizer_K_of_lines {p : ℕ} {b d x : G} {K : Subgroup G} (hp : p.Prime)
    (hKθ : K ∈ thetaComponentsAt p b) (hKq : CFSG.IsQuasisimple ↥K)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥K)) (hdK : d ∈ K) (hd1 : d ≠ 1) (hdp : d ^ p = 1)
    (hb1 : b ≠ 1) (hbp : b ^ p = 1) (hxb : x * b * x⁻¹ ∈ Subgroup.zpowers b)
    (hxd : x * d * x⁻¹ ∈ Subgroup.zpowers d) : x ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hx
  obtain ⟨lam, hlam'⟩ := Subgroup.mem_zpowers_iff.mp hxb
  have hbsc : x * b * x⁻¹ = b ^ lam := hlam'.symm
  have hlam : ¬ (p : ℤ) ∣ lam := MB3.not_dvd_of_scalar hb1 hbp hbsc
  have hK' : conjBy x K ∈ thetaComponentsAt p b :=
    S11d.conjBy_mem_thetaComponentsAt_of_zpow hp hKθ hbp hlam hbsc
  have hne : conjBy x K ≠ K := fun h =>
    hx (by rw [Subgroup.mem_normalizer_iff_map_conj_eq]; exact h)
  have hcomm := MB3.commute_of_ne_thetaComponents hKθ hK' hKq (MB3.isQuasisimple_conjBy hKq x) hne.symm
  obtain ⟨mu, hmu'⟩ := Subgroup.mem_zpowers_iff.mp hxd
  have hdsc : x * d * x⁻¹ = d ^ mu := hmu'.symm
  have hmu : ¬ (p : ℤ) ∣ mu := MB3.not_dvd_of_scalar hd1 hdp hdsc
  obtain ⟨u, hu'⟩ := MB3.mem_zpowers_zpow_of_not_dvd hp hdp hmu
  have hu : (d ^ mu) ^ u = d := hu'
  have hdK' : d ∈ conjBy x K := by
    have h1 : x * d ^ u * x⁻¹ ∈ conjBy x K := MB3.conj_mem_conjBy (zpow_mem hdK u) x
    have h2 : x * d ^ u * x⁻¹ = (d ^ mu) ^ u := by rw [← hdsc, conj_zpow]
    rwa [h2, hu] at h1
  have hdc : d ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => hcomm k hk d hdK'
  exact hd1 (Sec12Two.eq_one_of_mem_center_of_pow_eq_one hp hZ hdK hdc hdp)

theorem mem_normalizer_L_of_normalizer_B {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G}
    {n : ℕ} (h : Sec109.Config p A c L B n) (hqL : CFSG.IsQuasisimple ↥L) {b y : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hy : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) : y ∈ Subgroup.normalizer (L : Set G) := by
  have hp := h.prime
  by_contra hyL
  set L' : Subgroup G := L.map (MulAut.conj y).toMonoidHom with hL'
  have hL'c : L' ∈ thetaComponentsAt p c :=
    Sec12TwoAssembly.conj_mem_thetaComponentsAt hp hy h.L_mem.2
  have hne : L' ≠ L := fun heq => hyL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  have hbL : b ∈ L := h.B_le_L hbB
  have hbL' : b ∈ L' := by
    refine Subgroup.mem_map.mpr ⟨y⁻¹ * b * y, h.B_le_L ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyB) b).mp hbB
      simpa using this
    · change y * (y⁻¹ * b * y) * y⁻¹ = b
      group
  have hcent := Sec12TwoAssembly.le_centralizer_of_mem_thetaComponentsAt_ne hp hL'c h.L_mem.2 hqL
    hne (B := Subgroup.zpowers b) ((Subgroup.zpowers_le).mpr hbL')
    ((Subgroup.zpowers_le).mpr (Subgroup.le_normalizer hbL))
  have hbc : b ∈ Subgroup.centralizer (L : Set G) := hcent (Subgroup.mem_zpowers b)
  have hcenter : Subgroup.center ↥L = ⊥ := (Sec109.lnTwoOuter ↥L n h.model).1
  have hmem : (⟨b, hbL⟩ : L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hbc g g.2)
  rw [hcenter, Subgroup.mem_bot] at hmem
  exact hb1 (congrArg Subtype.val hmem)

end CFSG.RankThree.PartOne.TAIL
