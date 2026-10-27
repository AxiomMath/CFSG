module

public import CFSG.Quasithin.Vol2.Ch11SecGTL1
public import CFSG.Quasithin.Vol2.Ch11SecGTAut
public import CFSG.Quasithin.Vol2.Ch11SecGTShape

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem mem_pCoreOf_of_case1 [Finite G] {H K T L₁ Y : Subgroup G} {a y₀ : G}
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hT : QuasithinUnique.IsSylowTwoOf T H) (hKT : K ⊔ T = H) (hKK : ⁅K, K⁆ = K)
    (hL : L₁ ≤ K) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* SL(2, F)) (hcl : CFSG.Quasithin.conjClosure L₁ K = K)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hY : IsElemAbelian 2 Y)
    (hCL : K ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (L₁ : Set G))
    (ha : a ∈ H) {n : ℕ} (han : a ^ 2 ^ n = 1) (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀)
    (ha2 : a ^ 2 ∈ Subgroup.centralizer (Y : Set G)) (hS : Case1Struct (Bar.KBar K)) :
    a ∈ pCoreOf 2 H := by
  obtain ⟨hCF, hprimes, q, hq, hq5, ψ, hψ, hker⟩ := hS
  have : Fact q.Prime := ⟨hq⟩
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := hKH.trans hHY
  have haK : a ∈ Subgroup.normalizer (K : Set G) := hHK ha
  have haY : a ∈ Subgroup.normalizer (Y : Set G) := hHY ha
  set Fb := CFSG.fittingSubgroup (Bar.KBar K) with hFb
  set α := Bar.aut K ⟨a, haK⟩ with hα
  have hFpos : 0 < Nat.card Fb := Nat.card_pos
  have hFodd : Odd (Nat.card Fb) := by
    rcases Nat.even_or_odd (Nat.card Fb) with h | h
    · have := hprimes 2 Nat.prime_two (even_iff_two_dvd.mp h)
      omega
    · exact h
  have hpowF : ∀ x ∈ Fb, x ^ Nat.card Fb = 1 := fun x hx => by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := Fb) (x := ⟨x, hx⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have : (Bar.cBar K Y).Normal := Bar.cBar_normal hKY
  have hNc : Bar.cBar K Y ⊓ Fb ≤ Subgroup.center (Bar.KBar K) :=
    Bar.le_center_of_odd hL hcl hF e hCL inf_le_left
      (fun x hx => ⟨Nat.card Fb, hFodd, hpowF x hx.2⟩)
  have hαF : ∀ f ∈ Fb, α f * f⁻¹ ∈ Subgroup.center (Bar.KBar K) := by
    intro f hf
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective f
    have hmk := Bar.mk_commK haK hz
    have hαf : α ((⟨z, hz⟩ : ↥K) : Bar.KBar K) ∈ Fb := by
      have hmap : Fb.map α.toMonoidHom = Fb := by
        rw [hFb]
        exact Subgroup.characteristic_iff_map_eq.mp CFSG.fittingSubgroup_characteristic α
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hf
    have hxF : ((⟨a * z * a⁻¹ * z⁻¹, Bar.commK_mem haK hz⟩ : ↥K) : Bar.KBar K) ∈ Fb := by
      rw [hmk]
      exact mul_mem hαf (inv_mem hf)
    have hxC := Bar.commK_mem_cBar hY hKY haY haK hy₀ htr ha2 hz hFpos hprimes (hpowF _ hxF)
    rw [hα, ← hmk]
    exact hNc ⟨hxC, hxF⟩
  have hαn : α ^ 2 ^ n = 1 := by
    have h1 : (⟨a, haK⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using han)
    rw [hα, ← map_pow, h1, map_one]
  have hα1 : α = 1 := AutFit.eq_one_of_commFitting (Bar.commutator_top_eq_top hKK)
    (F := Fb) inferInstance hCF hFodd (k := ZMod q) (by rw [Nat.card_zmod]; omega) ψ hψ hker
    hαn hαF
  exact mem_pCoreOf_of_comm_mem hKH hHK hT hKT ha han (Bar.comm_mem_of_aut_eq_one hα1)

end CFSG.Quasithin.Vol2.Ch11.SecG
