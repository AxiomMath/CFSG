module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBd

section Frattini

theorem frattini_map_le_of_normal {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal] :
    (frattini N).map N.subtype ≤ frattini Q := by
  set F : Subgroup Q := (frattini N).map N.subtype with hF
  have hFN : F ≤ N := Subgroup.map_subtype_le _
  have hFnorm : F.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨n, hn, rfl⟩ := hx
    have hchar := (inferInstance : (frattini N).Characteristic)
    let c : MulAut N := MulAut.conjNormal g
    have h1 : c n ∈ frattini N := by
      have := Subgroup.characteristic_iff_map_eq.1 hchar c
      rw [← this]
      exact ⟨n, hn, rfl⟩
    exact ⟨c n, h1, by simp [c]⟩
  show F ≤ ⨅ a ∈ {H : Subgroup Q | IsCoatom H}, a
  refine le_iInf₂ fun K hK => ?_
  by_contra hFK
  have hsup : K ⊔ F = ⊤ := by
    have hlt : K < K ⊔ F := lt_of_le_of_ne le_sup_left fun h => hFK (h ▸ le_sup_right)
    exact hK.2 _ hlt
  have hN : (K ⊓ N).subgroupOf N ⊔ frattini N = ⊤ := by
    rw [eq_top_iff]
    intro n _
    have hn : (n : Q) ∈ K ⊔ F := hsup ▸ Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hn
    obtain ⟨z', hz', rfl⟩ := hz
    have hyz' : y * (z' : Q) = (n : Q) := hyz
    have hyN : y ∈ N := by
      have : y = (n : Q) * (z' : Q)⁻¹ := by rw [← hyz']; group
      rw [this]
      exact N.mul_mem n.2 (N.inv_mem z'.2)
    have : n = ⟨y, hyN⟩ * z' := Subtype.ext hyz'.symm
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr ⟨hy, hyN⟩) hz'
  have hNK : N ≤ K := by
    have := frattini_nongenerating hN
    intro n hn
    have h1 : (⟨n, hn⟩ : ↥N) ∈ (K ⊓ N).subgroupOf N := this ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp h1).1
  exact hFK (hFN.trans hNK)

end Frattini

section Perm3

theorem frattini_perm_three : frattini (Equiv.Perm (Fin 3)) = ⊥ := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hcoatom : ∀ a : Equiv.Perm (Fin 3), orderOf a = 2 → IsCoatom (Subgroup.zpowers a) := by
    intro a ha
    have hz : Nat.card (Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, ha]
    refine ⟨fun h => ?_, fun K hK => ?_⟩
    · rw [h, Subgroup.card_top, hcard] at hz
      omega
    · have h2 : 2 ∣ Nat.card K := hz ▸ Subgroup.card_dvd_of_le hK.le
      have h6 : Nat.card K ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card K
      have hlt : 2 < Nat.card K := by
        have := Subgroup.card_lt_of_lt hK
        omega
      have hK6 : Nat.card K = 6 := by
        have hle : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) h6
        interval_cases h : Nat.card K <;> omega
      exact Subgroup.eq_top_of_card_eq K (by rw [hK6, hcard])
  have hmem : ∀ a x : Equiv.Perm (Fin 3), a * a = 1 → x ∈ Subgroup.zpowers a → x = 1 ∨ x = a := by
    intro a x haa hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : a ^ 2 = 1 := by rw [pow_two]; exact haa
    have : a ^ k = a ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
      rw [zpow_add, zpow_mul]
      simp [h2]
    rw [this]
    have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk with h | h <;> simp [h]
  have h1 : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 1 = 1 := by decide
  have h2 : Equiv.swap (1 : Fin 3) 2 * Equiv.swap 1 2 = 1 := by decide
  have o1 : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h1) (by decide)
  have o2 : orderOf (Equiv.swap (1 : Fin 3) 2) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h2) (by decide)
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx1 := hmem _ _ h1 (frattini_le_coatom (hcoatom _ o1) hx)
  have hx2 := hmem _ _ h2 (frattini_le_coatom (hcoatom _ o2) hx)
  rw [Subgroup.mem_bot]
  rcases hx1 with h | h
  · exact h
  · rcases hx2 with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') (by decide)

theorem frattini_perm_three_prod :
    frattini (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have h1 := frattini_le_comap_frattini_of_surjective (φ := MonoidHom.fst _ _)
    (Prod.fst_surjective) hx
  have h2 := frattini_le_comap_frattini_of_surjective (φ := MonoidHom.snd _ _)
    (Prod.snd_surjective) hx
  rw [Subgroup.mem_comap, frattini_perm_three, Subgroup.mem_bot] at h1 h2
  rw [Subgroup.mem_bot]
  exact Prod.ext h1 h2

theorem frattini_eq_bot_of_mulEquiv {Q : Type*} [Group Q]
    (e : Q ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : frattini Q = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have h1 := frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective hx
  rw [Subgroup.mem_comap, frattini_perm_three_prod, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using h1)

end Perm3

section OTwoPhi

variable {G : Type*} [Group G]

theorem mem_oTwoPhi_iff (L : Subgroup G) (x : G) :
    x ∈ oTwoPhi L ↔ ∃ hx : x ∈ L,
      (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.Open.pCore 2 ↥L) ∈
        frattini (↥L ⧸ CFSG.Open.pCore 2 ↥L) := by
  unfold oTwoPhi
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pCoreOf_le_oTwoPhi (L : Subgroup G) : pCoreOf 2 L ≤ oTwoPhi L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : (QuotientGroup.mk y : ↥L ⧸ CFSG.Open.pCore 2 ↥L) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hy
  rw [mem_oTwoPhi_iff]
  refine ⟨y.2, ?_⟩
  show (QuotientGroup.mk y : ↥L ⧸ CFSG.Open.pCore 2 ↥L) ∈ frattini _
  rw [hy']
  exact Subgroup.one_mem _

theorem oTwoPhi_le_ker (L : Subgroup G) {Q : Type*} [Group Q] (ρ : ↥L →* Q)
    (hρ : Function.Surjective ρ) (hO : CFSG.Open.pCore 2 ↥L ≤ ρ.ker) (hΦ : frattini Q = ⊥)
    {x : G} (hx : x ∈ oTwoPhi L) : ∃ h : x ∈ L, ρ ⟨x, h⟩ = 1 := by
  obtain ⟨h, hf⟩ := (mem_oTwoPhi_iff L x).mp hx
  refine ⟨h, ?_⟩
  let ρ' : (↥L ⧸ CFSG.Open.pCore 2 ↥L) →* Q := QuotientGroup.lift _ ρ (fun y hy => hO hy)
  have hs : Function.Surjective ρ' := by
    intro q
    obtain ⟨l, rfl⟩ := hρ q
    exact ⟨QuotientGroup.mk l, rfl⟩
  have h1 := frattini_le_comap_frattini_of_surjective (φ := ρ') hs hf
  rw [Subgroup.mem_comap, hΦ, Subgroup.mem_bot] at h1
  exact h1

end OTwoPhi

end SBd

end CFSG.Quasithin
