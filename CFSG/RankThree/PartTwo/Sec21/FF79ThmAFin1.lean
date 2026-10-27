module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAAct
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG
open CFSG.Open (StatedProj StatedSL StatedScalars)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem nor_cenS_of_nor {U : Subgroup G} {g : G} (hg : g ∈ Nor U) : g ∈ Nor (CenS U) := by
  have key : ∀ g ∈ Nor U, ∀ x, x ∈ CenS U → g * x * g⁻¹ ∈ CenS U := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) u).mp hu
      simpa using this
    have h := hx (g⁻¹ * u * g) hu'
    calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * u := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem nor_OppE_of_nor {N : Subgroup G} {g : G} (hg : g ∈ Nor N) : g ∈ Nor (OppE 3 N) := by
  have key : ∀ g : ↥(Nor N), ∀ x, x ∈ OppE 3 N → (g : G) * x * (g : G)⁻¹ ∈ OppE 3 N := by
    intro g x hx
    obtain ⟨hxN, hxl⟩ := mem_OppE.mp hx
    have hy := (actE N g ⟨_, hxl⟩).2
    rw [actE_coe N g ⟨_, hxl⟩ ⟨x, hxN⟩ rfl] at hy
    exact mem_OppE.mpr ⟨(Subgroup.mem_normalizer_iff.mp g.2 x).mp hxN, hy⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key ⟨g, hg⟩ x, fun hx => ?_⟩
  have := key ⟨g⁻¹, inv_mem hg⟩ _ hx
  simpa [mul_assoc] using this

theorem nor_inf {H K : Subgroup G} {g : G} (hH : g ∈ Nor H) (hK : g ∈ Nor K) : g ∈ Nor (H ⊓ K) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH x, hK x]

theorem mem_nor_self {H : Subgroup G} {g : G} (hg : g ∈ H) : g ∈ Nor H :=
  Subgroup.le_normalizer hg

theorem OUpp_le (p : ℕ) (H : Subgroup G) : OUpp p H ≤ H := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem OUpp_mono (p : ℕ) {H K : Subgroup G} (hHK : H ≤ K) : OUpp p H ≤ OUpp p K := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨Subgroup.inclusion hHK y, ?_, rfl⟩
  have : Subgroup.normalClosure {g : ↥H | ∃ k : ℕ, g ^ (p ^ k) = 1} ≤
      (Subgroup.normalClosure {g : ↥K | ∃ k : ℕ, g ^ (p ^ k) = 1}).comap
        (Subgroup.inclusion hHK) := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    obtain ⟨k, hk⟩ := hg
    apply Subgroup.subset_normalClosure
    refine ⟨k, ?_⟩
    have : Subgroup.inclusion hHK (g ^ (p ^ k)) = 1 := by rw [hk, map_one]
    simpa using this
  exact this hy

theorem OUpp_conj_mem (p : ℕ) {H : Subgroup G} {g : G} (hg : g ∈ Nor H) {x : G}
    (hx : x ∈ OUpp p H) : g * x * g⁻¹ ∈ OUpp p H := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨conjAut H g hg y, ?_, rfl⟩
  have hs : (conjAut H g hg).toMonoidHom '' {g : ↥H | ∃ k : ℕ, g ^ (p ^ k) = 1} ⊆
      {g : ↥H | ∃ k : ℕ, g ^ (p ^ k) = 1} := by
    rintro _ ⟨z, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by
      have := congrArg (conjAut H g hg) hk
      simpa using this⟩
  have hmap := Subgroup.map_normalClosure {g : ↥H | ∃ k : ℕ, g ^ (p ^ k) = 1}
    (conjAut H g hg).toMonoidHom (conjAut H g hg).surjective
  have hle : (Subgroup.normalClosure {g : ↥H | ∃ k : ℕ, g ^ (p ^ k) = 1}).map
      (conjAut H g hg).toMonoidHom ≤
      Subgroup.normalClosure {g : ↥H | ∃ k : ℕ, g ^ (p ^ k) = 1} := by
    rw [hmap]
    exact Subgroup.normalClosure_mono hs
  exact hle ⟨y, hy, rfl⟩

section Finite

variable [Finite G]

theorem l24_card_eq (K : Subgroup G) (hK : StatedClassicalModel K .PSL 2 2 2) :
    Nat.card K = 60 := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hK
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp, n, hpp, hpn⟩ := FiniteField.card' (K := F)
  have hcard4 : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have hp2 : p = 2 := by
    have h1 : p ∣ 4 := by
      rw [← hcard4, hpn]; exact dvd_pow_self p n.ne_zero
    have h2 : p ∣ 2 ^ 2 := by simpa using h1
    exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h2)
  subst hp2
  haveI : CharP F 2 := hp
  have hN := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := F)
  have h1 : Nat.card K = Nat.card (StatedProj (StatedSL 2 F)) := Nat.card_congr e.toEquiv
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
  have hNc : Nat.card ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) = 1 := by
    rw [hN]; exact Subgroup.card_bot
  rw [hNc, mul_one, CFSG.Open.StatedAPI.card_statedSL_two] at h2
  have h3 : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card]; exact hcard4
  rw [h1, ← h2, h3]
  norm_num

theorem inf_opp_eq_bot_of_l24 {N K : Subgroup G} (hKN : K ≤ N)
    (hK : StatedClassicalModel K .PSL 2 2 2) : K ⊓ Opp 3 N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_PSL_simplicity K 2 2 2 hK).2
  have hnorm : ((Opp 3 N).subgroupOf K).Normal := by
    constructor
    intro y hy k
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp hy
    have hkN : (k : G) ∈ N := hKN k.2
    refine Subgroup.mem_map.mpr ⟨⟨k, hkN⟩ * y' * ⟨k, hkN⟩⁻¹, ?_, ?_⟩
    · exact (pPrimeCore_normal (p := 3) (G := ↥N)).conj_mem y' hy' _
    · have hyy'' : (y' : G) = (y : G) := hyy'
      simp [hyy'']
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Opp 3 N).subgroupOf K) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hx.1
    have : (⟨x, hxK⟩ : K) ∈ (Opp 3 N).subgroupOf K := hx.2
    rw [h] at this
    simpa using this
  · exfalso
    have hle : K ≤ Opp 3 N := by
      intro x hx
      have : (⟨x, hx⟩ : K) ∈ (Opp 3 N).subgroupOf K := by rw [h]; trivial
      exact this
    have hcop := coprime_three_card_opp N
    have h3K : 3 ∣ Nat.card K := by rw [l24_card_eq K hK]; norm_num
    have : 3 ∣ Nat.card (Opp 3 N) := h3K.trans (Subgroup.card_dvd_of_le hle)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop this

end Finite

end CFSG.RankThree.PartTwo.Sec21.FF79
