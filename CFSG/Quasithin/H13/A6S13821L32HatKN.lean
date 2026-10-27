module

public import CFSG.Quasithin.H13.A6S13821L32HatStep21
public import CFSG.Quasithin.H13.A6S13821L32HatOut

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace L32HatStep

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem H_le_K_mul_N {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    ∀ h ∈ H, ∃ k ∈ K, ∃ n ∈ centralizerMod (pCoreOf 2 K) H K, h = k * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ⊔ T ≤ H := hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hL1H
  have hL1' : S.L1 ≤ H := le_sup_left.trans hL1H
  have P := S.plusData_X13820
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  obtain ⟨π, hπ, hker, hD⟩ := exists_pi_sl3 hK hKn hTsylH hP'
  have hL0K : l0 L ≤ K := S.l0_le_of_hat h139 h37 h38 hhat hH hK hKn hP
  have hO2KH : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  have hHN : H ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    hKn.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hHNH : H ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 H)
  set A : Subgroup G := (S.L1 ⊔ T) ⊔ pCoreOf 2 H with hAdef
  have hAH : A ≤ H := sup_le hL1H (pCoreOf_le 2 H)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAH.trans hKn
  have hAN : A ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) := hAH.trans hHN
  have hAsolv : Group.IsSolvable ↥A := by
    haveI := S.isSolvable_L1T h1334 hS
    haveI hNsolv : Group.IsSolvable ↥(pCoreOf 2 H) := by
      haveI := IsPGroup.isNilpotent (pCoreOf_isPGroup 2 H)
      infer_instance
    have := CFSG.Quasithin.C126.isSolvable_sup_of_le_normalizer'
      (hL1H.trans hHNH) hNsolv ‹Group.IsSolvable ↥(S.L1 ⊔ T)›
    rw [hAdef, sup_comm]
    exact this
  set PA : Subgroup SL3.S := ((K ⊓ A).subgroupOf K).map π with hPAdef
  have hPA_mem : ∀ k (hk : k ∈ K), π ⟨k, hk⟩ ∈ PA ↔ k ∈ A := by
    intro k hk
    constructor
    · intro h
      obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp h
      have h1 : π (a⁻¹ * ⟨k, hk⟩) = 1 := by
        rw [map_mul, map_inv, hak, inv_mul_cancel]
      have h2 : ((a⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := (hker _).mp h1
      have h3 : ((a⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ A := Subgroup.mem_sup_right (hO2KH h2)
      have ha' : (a : G) ∈ A := (Subgroup.mem_subgroupOf.mp ha).2
      have e : k = (a : G) * ((a⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
      rw [e]
      exact A.mul_mem ha' h3
    · intro h
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hk, h⟩)
  have hTA : ∀ x ∈ T, x ∈ A := fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)
  have hL1A : ∀ m ∈ S.L1 ⊔ T, m ∈ A := fun m hm => Subgroup.mem_sup_left hm
  have hL1A' : ∀ m ∈ S.L1, m ∈ A := fun m hm => Subgroup.mem_sup_left (Subgroup.mem_sup_left hm)
  have hKnorm : ∀ k ∈ K, ∀ z ∈ pCoreOf 2 K, k * z * k⁻¹ ∈ pCoreOf 2 K := fun k hk z hz =>
    (Subgroup.mem_normalizer_iff.mp (hHN (hKH hk)) z).mp hz
  have hP0PA : SL3.P0 ≤ PA := by
    rw [← hD]
    have hle : T.subgroupOf K ≤ (K ⊓ A).subgroupOf K := by
      intro t ht
      have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
      exact Subgroup.mem_subgroupOf.mpr ⟨t.2, hTA _ htT⟩
    exact Subgroup.map_mono hle
  have hPAtop : PA ≠ ⊤ := by
    intro htop
    have hKA : K ≤ A := by
      intro k hk
      have hmem : π ⟨k, hk⟩ ∈ PA := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (hPA_mem k hk).mp hmem
    haveI := hAsolv
    exact not_isSolvable_of_mem_cComp hK
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKA)
        (Subgroup.inclusion_injective hKA))
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := l0_decomp hhat
  have hc1 : c ≠ 1 := fun h1 => hcO (h1 ▸ Subgroup.one_mem _)
  have hcK : c ∈ K := hL0K hcl0
  have hcA : c ∈ A := hL1A' c (S.l0_le_L1 hcl0)
  have hcOK : c ∉ pCoreOf 2 K := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨c, h⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hc1 (eq_one_of_pow_three_pow_two hc3 hk')
  have hπc : π ⟨c, hcK⟩ ≠ 1 := fun h => hcOK ((hker _).mp h)
  have hcPA : π ⟨c, hcK⟩ ∈ PA := (hPA_mem c hcK).mpr hcA
  have hcP0 : π ⟨c, hcK⟩ ∉ SL3.P0 := by
    intro hP0
    obtain ⟨k, hk⟩ := SL3.P0_sylow.1 ⟨π ⟨c, hcK⟩, hP0⟩
    have hk' : (π ⟨c, hcK⟩) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc3K : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext hc3
    have h3 : (π ⟨c, hcK⟩) ^ 3 = 1 := by rw [← map_pow, hc3K, map_one]
    exact hπc (eq_one_of_pow_three_pow_two h3 hk')
  have hPAX : PA = SL3.X1 ∨ PA = SL3.X2 := by
    rcases SL3.overgroups_SL3 PA hP0PA with h | h | h | h
    · exact absurd (h ▸ hcPA) hcP0
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hPAtop
  have hgclaim : ∀ g ∈ A, ∃ k ∈ K, ∃ n ∈ centralizerMod (pCoreOf 2 K) H K, g = k * n := by
    intro g hg
    set σ : MulAut SL3.S := L32A.C.indHom π hπ hker hAK hAN ⟨g, hg⟩ with hσdef
    have hσapp : ∀ k : ↥K, σ (π k) = π (conjK (hAK hg) k) := fun k =>
      L32A.C.indHom_apply π hπ hker hAK hAN ⟨g, hg⟩ k
    have hconjA : ∀ k : ↥K, ((conjK (hAK hg) k : ↥K) : G) = g * (k : G) * g⁻¹ := fun k =>
      conjK_apply _ _
    have hpres : ∀ x : SL3.S, x ∈ PA ↔ σ x ∈ PA := by
      intro x
      obtain ⟨k, rfl⟩ := hπ x
      rw [hσapp]
      have hk := k.2
      have hk1 : π k = π ⟨(k : G), hk⟩ := rfl
      have hk2 : π (conjK (hAK hg) k) = π ⟨((conjK (hAK hg) k : ↥K) : G), (conjK (hAK hg) k).2⟩ := rfl
      rw [hk1, hk2, hPA_mem _ hk, hPA_mem _ (conjK (hAK hg) k).2, hconjA]
      constructor
      · intro hkA
        exact A.mul_mem (A.mul_mem hg hkA) (A.inv_mem hg)
      · intro hgk
        have e : (k : G) = g⁻¹ * (g * (k : G) * g⁻¹) * g := by group
        rw [e]
        exact A.mul_mem (A.mul_mem (A.inv_mem hg) hgk) hg
    have hinner : σ ∈ inner SL3.S := by
      rcases hPAX with hX1 | hX2
      · apply L32HatOut.inner_of_preserves_X1 σ
        intro x
        have := hpres x
        rw [hX1] at this
        exact this
      · apply L32HatOut.inner_of_preserves_X2 σ
        intro x
        have := hpres x
        rw [hX2] at this
        exact this
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hinner
    obtain ⟨k₀, hk₀⟩ := hπ s
    have hk₀K : (k₀ : G) ∈ K := k₀.2
    have hconj : ∀ u : ↥K, π (conjK (hAK hg) u) = π k₀ * π u * (π k₀)⁻¹ := by
      intro u
      have h1 := hσapp u
      have h2 : σ (π u) = π k₀ * π u * (π k₀)⁻¹ := by
        rw [← hs, MulAut.conj_apply, hk₀]
      exact h1.symm.trans h2
    refine ⟨(k₀ : G), hk₀K, (k₀ : G)⁻¹ * g, ?_, by group⟩
    have hk₀H : (k₀ : G) ∈ H := hKH hk₀K
    have hn_H : (k₀ : G)⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hk₀H) (hAH hg)
    refine ⟨hn_H, hHN hn_H, ?_⟩
    intro u hu
    set uK : ↥K := ⟨u, hu⟩ with huK
    set zK : ↥K := (k₀ * uK * k₀⁻¹)⁻¹ * conjK (hAK hg) uK with hzK
    have hzPi : π zK = 1 := by
      simp only [hzK, map_mul, map_inv, hconj uK]
      group
    have hzG : ((zK : ↥K) : G) ∈ pCoreOf 2 K := (hker zK).mp hzPi
    have hzG' : ((zK : ↥K) : G) = ((k₀ : G) * u * (k₀ : G)⁻¹)⁻¹ * (g * u * g⁻¹) := by
      simp [hzK, hconjA, huK]
    have hconjz : (k₀ : G)⁻¹ * ((zK : ↥K) : G) * k₀ ∈ pCoreOf 2 K := by
      have := hKnorm (k₀ : G)⁻¹ (K.inv_mem hk₀K) _ hzG
      simpa using this
    have hfin := hKnorm u hu _ hconjz
    have e : ((k₀ : G)⁻¹ * g) * u * ((k₀ : G)⁻¹ * g)⁻¹ * u⁻¹ =
        u * ((k₀ : G)⁻¹ * ((zK : ↥K) : G) * k₀) * u⁻¹ := by
      rw [hzG']
      group
    rw [e]
    exact hfin
  intro h hh
  obtain ⟨k, hk, m, hm, rfl⟩ := mem_mul_of_sup_eq hKn hL1H hHK h hh
  obtain ⟨k', hk', n', hn', hm'⟩ := hgclaim m (hL1A m hm)
  refine ⟨k * k', K.mul_mem hk hk', n', hn', ?_⟩
  rw [hm', ← mul_assoc]

end L32HatStep

end CFSG.Quasithin.H13.A6
