module

public import CFSG.Quasithin.H13.U3S1347M

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s3_pow_six : ∀ g : Perm (Fin 3), g ^ 6 = 1 := by decide +kernel

theorem s3_comm : ∀ a b : Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a := by
  decide +kernel

theorem s3_mul_pow_three : ∀ a b : Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by
  decide +kernel

theorem s3s3_pow_three {g : Perm (Fin 3) × Perm (Fin 3)} (hg : Odd (orderOf g)) : g ^ 3 = 1 := by
  have h6 : g ^ 6 = 1 := Prod.ext (by rw [Prod.pow_fst, s3_pow_six, Prod.fst_one])
    (by rw [Prod.pow_snd, s3_pow_six, Prod.snd_one])
  have hd : orderOf g ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one h6
  exact orderOf_dvd_iff_pow_eq_one.1 ((Nat.coprime_two_right.2 hg).dvd_of_dvd_mul_left hd)

theorem s3s3_mul_pow_three {a b : Perm (Fin 3) × Perm (Fin 3)} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a * b) ^ 3 = 1 := by
  have ha1 : a.1 ^ 3 = 1 := by rw [← Prod.pow_fst, ha, Prod.fst_one]
  have ha2 : a.2 ^ 3 = 1 := by rw [← Prod.pow_snd, ha, Prod.snd_one]
  have hb1 : b.1 ^ 3 = 1 := by rw [← Prod.pow_fst, hb, Prod.fst_one]
  have hb2 : b.2 ^ 3 = 1 := by rw [← Prod.pow_snd, hb, Prod.snd_one]
  exact Prod.ext (by rw [Prod.pow_fst, Prod.fst_mul, s3_mul_pow_three _ _ ha1 hb1, Prod.fst_one])
    (by rw [Prod.pow_snd, Prod.snd_mul, s3_mul_pow_three _ _ ha2 hb2, Prod.snd_one])

theorem s3s3_comm {a b : Perm (Fin 3) × Perm (Fin 3)} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    a * b = b * a := by
  have ha1 : a.1 ^ 3 = 1 := by rw [← Prod.pow_fst, ha, Prod.fst_one]
  have ha2 : a.2 ^ 3 = 1 := by rw [← Prod.pow_snd, ha, Prod.snd_one]
  have hb1 : b.1 ^ 3 = 1 := by rw [← Prod.pow_fst, hb, Prod.fst_one]
  have hb2 : b.2 ^ 3 = 1 := by rw [← Prod.pow_snd, hb, Prod.snd_one]
  exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, s3_comm _ _ ha1 hb1])
    (by rw [Prod.snd_mul, Prod.snd_mul, s3_comm _ _ ha2 hb2])

theorem s1347_not_s3s3 (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) (hN : CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂) = Open.pCore 2 ↥(H₁ ⊔ H₂))
    (hcomm : ¬ ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G))
    (e : ↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂) ≃* Perm (Fin 3) × Perm (Fin 3)) : False := by
  set f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) with hf
  let E : Subgroup (↥(H₁ ⊔ H₂) ⧸ CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) :=
    { carrier := {d | e d ^ 3 = 1}
      mul_mem' := fun {a b} ha hb => by
        show e (a * b) ^ 3 = 1
        rw [map_mul]
        exact s3s3_mul_pow_three ha hb
      one_mem' := by
        show e 1 ^ 3 = 1
        rw [map_one, one_pow]
      inv_mem' := fun {a} ha => by
        show e a⁻¹ ^ 3 = 1
        rw [map_inv, inv_pow, show e a ^ 3 = 1 from ha, inv_one] }
  have hE : ∀ d, d ∈ E ↔ e d ^ 3 = 1 := fun _ => Iff.rfl
  have hK : ∀ {Hi : Subgroup G}, Hi ≤ H₁ ⊔ H₂ →
      oTwoRes Hi ≤ (E.comap f).map (H₁ ⊔ H₂).subtype := by
    intro Hi hHi
    rw [oTwoRes, closure_le]
    rintro y ⟨hyH, m, hm, hym⟩
    have h1 : orderOf (⟨y, hHi hyH⟩ : ↥(H₁ ⊔ H₂)) ∣ m :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hym))
    have h2 : orderOf (e (f ⟨y, hHi hyH⟩)) ∣ m :=
      (orderOf_map_dvd (e.toMonoidHom.comp f) _).trans h1
    exact ⟨⟨y, hHi hyH⟩, (hE _).2 (s3s3_pow_three (Odd.of_dvd_nat hm h2)), rfl⟩
  apply hcomm
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := hK le_sup_left ha
  obtain ⟨b', hb', rfl⟩ := hK le_sup_right hb
  have h1 : f ⁅a', b'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply e.injective
    rw [map_mul, map_mul]
    exact s3s3_comm ((hE _).1 ha') ((hE _).1 hb')
  have h2 : ⁅a', b'⁆ ∈ Open.pCore 2 ↥(H₁ ⊔ H₂) := by
    rw [← hN]
    exact (QuotientGroup.eq_one_iff _).1 h1
  exact pCoreOf_le_centralizer_of_reduced' (s1347_reduced S hH₀) ⟨_, h2, rfl⟩

theorem isExtensionWith_of_eq {D A : Type*} [Group D] [Group A] {N₁ N₂ : Subgroup D}
    [N₁.Normal] [N₂.Normal] (hN : N₁ = N₂)
    (h : F6.IsExtensionWith (D ⧸ N₁) A fun K => IsPOnePlusTwo 3 ↥K) :
    F6.IsExtensionWith (D ⧸ N₂) A fun K => IsPOnePlusTwo 3 ↥K := by
  subst hN
  exact h

theorem s1347_centralizer_eq_of_pPrimeCore (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hN : CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂) = Open.pCore 2 ↥(H₁ ⊔ H₂)) :
    (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_
    (le_inf (pCoreOf_le 2 _) (pCoreOf_le_centralizer_of_reduced' (s1347_reduced S hH₀)))
  have hCn : (((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G)).subgroupOf (H₁ ⊔ H₂)).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).2 (s1347_normalizer_centralizer S hH₀)
  have hC3 : Nat.Coprime 3
      (Nat.card ↥(((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G)).subgroupOf (H₁ ⊔ H₂))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact s1347_coprime_centralizer S h hH₀
  have hCN : ((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G)).subgroupOf (H₁ ⊔ H₂) ≤
      CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂) := le_sSup ⟨hCn, hC3⟩
  rw [hN] at hCN
  intro x hx
  exact ⟨⟨x, hx.1⟩, hCN (mem_subgroupOf.2 hx), rfl⟩

end CFSG.Quasithin.H13.U3
