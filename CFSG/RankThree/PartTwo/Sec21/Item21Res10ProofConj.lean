module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofLift
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_le
    {A K : Subgroup G} {d : G}
    (hA : Late.IsE27 A) (hAK : A ≤ K) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hKd : K ≤ centralizer ({d} : Set G))
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (hON : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K)
      CFSG.Blueprint.NativeSporadic.ON)
    {a a' : G} (ha : a ∈ A) (ha' : a' ∈ A) (had : a ∉ zpowers d)
    (had' : a' ∉ zpowers d) :
    ∃ g ∈ K ⊓ normalizer (A : Set G),
      (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers a' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 K with hNdef
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hq.1 hON
  obtain ⟨-, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set A' : Subgroup K := A.subgroupOf K with hA'
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv, hA.2]
  have hA'3 : IsPGroup 3 A' := IsPGroup.of_card (n := 3) (by rw [hA'27]; norm_num)
  have hinj : Set.InjOn π (A' : Set K) := injOn_mk_of_isPGroup Nat.prime_three hA'3
  have hAbar : Late.IsE27 (A'.map π) := by
    refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := u
      obtain ⟨_, y, hy, rfl⟩ := v
      apply Subtype.ext
      change π x * π y = π y * π x
      have hc : x * y = y * x := Subtype.ext (by
        simpa using congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      rw [← map_mul, ← map_mul, hc]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 x hx)
      rw [this, map_one]
    · rw [card_map_eq_of_injOn' π hinj, hA'27]
  obtain ⟨hZ, -, -⟩ := Sec13.ON134.center_eq_zpowers (hAK hdA) (hA.1.2 d hdA) hd1 hKd hON
  have hnz : ∀ b (hb : b ∈ A), b ∉ zpowers d → π ⟨b, hAK hb⟩ ∉ center (K ⧸ N) := by
    intro b hb hbd hmem
    rw [hZ] at hmem
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hmem
    apply hbd
    have h2 := hinj (zpow_mem (show (⟨d, hAK hdA⟩ : K) ∈ A' from hdA) n)
      (show (⟨b, hAK hb⟩ : K) ∈ A' from hb) ((map_zpow π _ n).trans hn)
    have h3 : (((⟨d, hAK hdA⟩ : K) ^ n : K) : G) = b := congrArg Subtype.val h2
    rw [← h3, coe_zpow]
    exact zpow_mem_zpowers d n
  obtain ⟨gb, hgb, hgbe⟩ := Sec13.ON134.transitive ψ hAbar
    (⟨⟨a, hAK ha⟩, ha, rfl⟩ : π ⟨a, hAK ha⟩ ∈ A'.map π)
    (⟨⟨a', hAK ha'⟩, ha', rfl⟩ : π ⟨a', hAK ha'⟩ ∈ A'.map π) (hnz a ha had) (hnz a' ha' had')
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective N gb
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 A' (N ⊔ A') :=
    CFSG.ABGLocalTools.isSylowOf_sup_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3) hA'3
  have hcomap : (A'.map π).comap π = N ⊔ A' := by
    rw [comap_map_eq, hπ, QuotientGroup.ker_mk', sup_comm]
  have hA''le : A'.map (MulAut.conj g₀).toMonoidHom ≤ N ⊔ A' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hcomap, mem_comap]
    have h1 : π ((MulAut.conj g₀).toMonoidHom x) = π g₀ * π x * (π g₀)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [h1]
    exact (mem_normalizer_iff.mp hgb (π x)).mp ⟨x, hx, rfl⟩
  have hSyl' : CFSG.ABGLocalTools.IsSylowOf 3 (A'.map (MulAut.conj g₀).toMonoidHom) (N ⊔ A') :=
    CFSG.ABGLocalTools.isSylowOf_of_card hA''le (by
      rw [card_map_of_injective (MulAut.conj g₀).injective, ← hSyl.card_eq])
  obtain ⟨t, ht, htA⟩ := hSyl.exists_mem_conj hSyl'
  set g : K := t⁻¹ * g₀ with hg
  have hgN : ∀ x ∈ A', g * x * g⁻¹ ∈ A' := by
    intro x hx
    have h1 : g₀ * x * g₀⁻¹ ∈ A'.map (MulAut.conj g₀).toMonoidHom := ⟨x, hx, rfl⟩
    have h2 := (htA _).mp h1
    have e : g * x * g⁻¹ = t⁻¹ * (g₀ * x * g₀⁻¹) * t := by rw [hg]; group
    rw [e]
    exact h2
  have htb : π t ∈ A'.map π := by
    have : t ∈ (A'.map π).comap π := hcomap ▸ ht
    exact this
  have hga : g * ⟨a, hAK ha⟩ * g⁻¹ ∈ A' := hgN _ ha
  have hπga : π (g * ⟨a, hAK ha⟩ * g⁻¹) =
      π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ := by
    have hw : π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ ∈ A'.map π :=
      (mem_normalizer_iff.mp hgb _).mp ⟨_, ha, rfl⟩
    have hct : π t * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) =
        (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) * π t :=
      congrArg Subtype.val (hAbar.1.1.is_comm.comm ⟨_, htb⟩ ⟨_, hw⟩)
    have e1 : π (g * ⟨a, hAK ha⟩ * g⁻¹) =
        (π t)⁻¹ * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) * π t := by
      rw [hg]
      simp only [map_mul, map_inv]
      group
    rw [e1]
    calc (π t)⁻¹ * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) * π t
        = (π t)⁻¹ * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ * π t) := by group
      _ = (π t)⁻¹ * (π t * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹)) := by rw [hct]
      _ = π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ := by group
  have hzk : zpowers (g * ⟨a, hAK ha⟩ * g⁻¹) = zpowers ⟨a', hAK ha'⟩ := by
    apply Sec13.ON134.zpowers_eq_of_mk hA'3 hga ha'
    rw [show QuotientGroup.mk' (aschbacherSolvableCore 3 K) (g * ⟨a, hAK ha⟩ * g⁻¹) =
      π (g * ⟨a, hAK ha⟩ * g⁻¹) from rfl, hπga]
    rw [MonoidHom.map_zpowers] at hgbe
    exact hgbe
  refine ⟨(g : G), ⟨g.2, ?_⟩, ?_⟩
  · refine mem_normalizer_fintype fun x hx => ?_
    have := hgN ⟨x, hAK hx⟩ hx
    exact this
  · rw [MonoidHom.map_zpowers]
    have := congrArg (Subgroup.map K.subtype) hzk
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
    simpa [MulAut.conj_apply] using this

end CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof
