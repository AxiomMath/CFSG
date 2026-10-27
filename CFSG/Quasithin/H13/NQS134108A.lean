module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.H13.NQS13410Asm4

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

theorem eq_or_eq_of_relIndex_prime {Γ : Type} [Group Γ] {H Y K : Subgroup Γ} (hHY : H ≤ Y)
    (hYK : Y ≤ K) (hp : (H.relIndex K).Prime) : Y = H ∨ Y = K := by
  have h1 := relIndex_mul_relIndex H Y K hHY hYK
  rcases Nat.prime_mul_iff.mp (h1 ▸ hp) with ⟨-, hb⟩ | ⟨-, ha⟩
  · exact Or.inr (le_antisymm hYK (relIndex_eq_one.mp hb))
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp ha) hHY)

theorem l3B_relIndex_P2 : l3B.relIndex l3P2 = 3 := by
  have h := relIndex_mul_card l3B l3P2
  rw [inf_eq_left.2 (fun g hg => l3B_le_P2 g hg), card_l3B, card_l3P2] at h
  omega

theorem l3B_relIndex_P1 : l3B.relIndex (l3Stab l3e1) = 3 := by
  have h := relIndex_mul_card l3B (l3Stab l3e1)
  rw [inf_eq_left.2 (fun g hg => l3B_le_P1 g hg), card_l3B, card_l3Stab (by decide +kernel)] at h
  omega

theorem l3B_self_normalizing : ∀ g : L3.Γ, (∀ b ∈ l3Blist, g * b * g⁻¹ ∈ l3Blist) →
    g ∈ l3Blist := by
  decide +kernel

theorem exists_l3P2_conj : ∃ g : L3.Γ, InL3P2 g ∧ ∃ b ∈ l3Blist, g * b * g⁻¹ ∉ l3Blist := by
  decide +kernel

theorem exists_l3Stab_not_P2 : ∃ g : L3.Γ, L3.act g l3e1 = l3e1 ∧ ¬ InL3P2 g := by
  decide +kernel

theorem l3Stab_not_le_P2 : ¬ l3Stab l3e1 ≤ l3P2 := by
  intro h
  obtain ⟨g, hg, hg2⟩ := exists_l3Stab_not_P2
  exact hg2 (mem_l3P2.1 (h (mem_l3Stab.2 hg)))

theorem l3_overgroups {Y : Subgroup L3.Γ} (hY : l3B ≤ Y) :
    Y = l3B ∨ Y = l3Stab l3e1 ∨ Y = l3P2 ∨ Y = ⊤ := by
  by_cases h1 : Y ≤ l3Stab l3e1
  · rcases eq_or_eq_of_relIndex_prime hY h1 (by rw [l3B_relIndex_P1]; norm_num) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have h2 := l3P2_le_of hY h1
    have h7 : l3P2.relIndex ⊤ = 7 := by
      rw [relIndex_top_right]
      have := Subgroup.card_mul_index l3P2
      rw [card_l3P2, card_l3Γ] at this
      omega
    rcases eq_or_eq_of_relIndex_prime h2 le_top (by rw [h7]; norm_num) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem a6D_relIndex_P2 : a6D.relIndex a6P2 = 3 := by
  have h := relIndex_mul_card a6D a6P2
  rw [inf_eq_left.2 (fun g hg => a6D_le_P2 g hg), card_a6D, card_a6P2] at h
  omega

theorem a6D_relIndex_stab45 : a6D.relIndex stab45 = 3 := by
  have h := relIndex_mul_card a6D stab45
  rw [inf_eq_left.2 (fun g hg => a6D_le_stab45 g hg), card_a6D, card_stab45] at h
  omega

theorem a6P2_conj_D : ∀ σ : Perm (Fin 6), InD6 σ → ∀ τ ∈ a6P2list, σ * τ * σ⁻¹ ∈ a6P2list := by
  decide +kernel

theorem exists_a6P2_conj : ∃ γ ∈ a6P2list, ∃ β ∈ a6Dlist, γ * β * γ⁻¹ ∉ a6Dlist := by
  decide +kernel

theorem exists_stab45_not_P2 : ∃ σ ∈ stab45List, σ ∉ a6P2list := by decide +kernel

theorem stab45_not_le_P2 : ¬ stab45 ≤ a6P2 := by
  intro h
  obtain ⟨σ, hσ, hσ'⟩ := exists_stab45_not_P2
  exact hσ' (mem_a6P2.1 (h hσ))

theorem a6_overgroups {Y : Subgroup (Perm (Fin 6))} (hY : a6D ≤ Y)
    (hYA : Y ≤ alternatingGroup (Fin 6)) :
    Y = a6D ∨ Y = stab45 ∨ Y = a6P2 ∨ Y = alternatingGroup (Fin 6) := by
  by_cases h1 : Y ≤ stab45
  · rcases eq_or_eq_of_relIndex_prime hY h1 (by rw [a6D_relIndex_stab45]; norm_num) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have h2 := a6P2_le_of hYA hY h1
    by_cases h3 : Y ≤ a6P2
    · exact Or.inr (Or.inr (Or.inl (le_antisymm h3 h2)))
    · obtain ⟨s, hsY, hsP⟩ := IsConcreteLE.not_le_iff_exists.1 h3
      exact Or.inr (Or.inr (Or.inr (le_antisymm hYA (alt6_le_of_overgroup24 card_a6P2
        a6P2_le_alt h2 hsY (Perm.mem_alternatingGroup.1 (hYA hsY)) hsP))))

variable {G : Type} [Group G] {Γ : Type} [Group Γ]

namespace ParData

variable {K T U L1T : Subgroup G} {ρ : ↥(normalizer (U : Set G)) →* Γ} {Q P : Subgroup Γ}
  (D : ParData K T U L1T ρ Q P)
include D

@[expose] def parOf (_ : ParData K T U L1T ρ Q P) (Y : Subgroup Γ) : Subgroup G :=
  ((Y.comap ρ).map (normalizer (U : Set G)).subtype ⊓ K) ⊔ T

theorem mem_parOf {Y : Subgroup Γ} {g : ↥(normalizer (U : Set G))} (hgK : (g : G) ∈ K)
    (hgY : ρ g ∈ Y) : (g : G) ∈ D.parOf Y :=
  mem_sup_left (mem_inf.2 ⟨⟨g, hgY, rfl⟩, hgK⟩)

theorem T_le_parOf (Y : Subgroup Γ) : T ≤ D.parOf Y := le_sup_right

theorem parOf_le_sup (Y : Subgroup Γ) : D.parOf Y ≤ K ⊔ T :=
  sup_le (inf_le_right.trans le_sup_left) le_sup_right

theorem parOf_mono {Y Y' : Subgroup Γ} (h : Y ≤ Y') : D.parOf Y ≤ D.parOf Y' :=
  sup_le_sup_right (inf_le_inf_right _ (Subgroup.map_mono (Subgroup.comap_mono h))) _

theorem le_parOf_img' {X : Subgroup G} (hTX : T ≤ X) (hXKT : X ≤ K ⊔ T) :
    X ≤ D.parOf (D.img' X) := by
  intro x hx
  obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_le_sup D.TK hTX hXKT hx
  have hkU : k ∈ normalizer (U : Set G) := D.KU (mem_inf.1 hk).2
  exact mul_mem (D.mem_parOf (g := ⟨k, hkU⟩) (mem_inf.1 hk).2 (D.mem_img' hk))
    (mem_sup_right ht)

theorem parOf_img'_le {X : Subgroup G} (hTX : T ≤ X) : D.parOf (D.img' X) ≤ X := by
  refine sup_le ?_ hTX
  rintro g ⟨⟨g', hg', rfl⟩, hgK⟩
  exact D.mem_of_img' hTX hgK hg'

theorem eq_parOf {X : Subgroup G} (hTX : T ≤ X) (hXKT : X ≤ K ⊔ T) :
    X = D.parOf (D.img' X) :=
  le_antisymm (D.le_parOf_img' hTX hXKT) (D.parOf_img'_le hTX)

theorem parOf_B {B : Subgroup Γ}
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β) :
    D.parOf B = T := by
  refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
  rintro g ⟨⟨g', hg', rfl⟩, hgK⟩
  obtain ⟨t, htTK, hρt⟩ := hB _ hg'
  have h1 : ρ (g' * t⁻¹) = 1 := by rw [map_mul, map_inv, hρt, mul_inv_cancel]
  have h2 := D.ker (g' * t⁻¹) (mul_mem hgK (inv_mem (mem_inf.1 htTK).2)) h1
  have e : (g' : G) = ((g' * t⁻¹ : ↥(normalizer (U : Set G))) : G) * t := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  show (g' : G) ∈ T
  rw [e]
  exact mul_mem h2 (mem_inf.1 htTK).1

theorem parOf_P : D.parOf P = L1T := by
  refine le_antisymm (sup_le ?_ D.T_le) ?_
  · rintro g ⟨⟨g', hg', rfl⟩, hgK⟩
    exact (D.P_iff g' hgK).1 hg'
  · refine (D.le_parOf_img' D.T_le D.L1T_le).trans (D.parOf_mono ?_)
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgX, hgK⟩ := mem_inf.1 (mem_subgroupOf.1 hg)
    exact (D.P_iff g hgK).2 hgX

theorem parOf_Q : D.parOf Q = K ⊔ T :=
  le_antisymm (D.parOf_le_sup Q) (sup_le (fun k hk =>
    D.mem_parOf (g := ⟨k, D.KU hk⟩) hk (D.img_le ⟨k, D.KU hk⟩ hk)) le_sup_right)

theorem overgroups {B P₂ : Subgroup Γ}
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    (hcls : ∀ Y : Subgroup Γ, B ≤ Y → Y ≤ Q → Y = B ∨ Y = P ∨ Y = P₂ ∨ Y = Q)
    {X : Subgroup G} (hTX : T ≤ X) (hXKT : X ≤ K ⊔ T) :
    X = T ∨ X = L1T ∨ X = D.parOf P₂ ∨ X = K ⊔ T := by
  have hBX : B ≤ D.img' X := fun β hβ => by
    obtain ⟨g, hg, rfl⟩ := hB β hβ
    exact D.mem_img' (mem_inf.2 ⟨hTX (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩)
  have e := D.eq_parOf hTX hXKT
  rcases hcls _ hBX (D.img'_le X) with h | h | h | h <;> rw [h] at e
  · exact Or.inl (e.trans (D.parOf_B hB))
  · exact Or.inr (Or.inl (e.trans D.parOf_P))
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr (e.trans D.parOf_Q)))

theorem relIndex_parOf [Finite G] {B Y : Subgroup Γ} (hTU : T ≤ normalizer (U : Set G))
    (hTB : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K → ρ g ∈ B)
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    (hYQ : Y ≤ Q)
    (hTY : ∀ t : ↥(normalizer (U : Set G)), (t : G) ∈ T → ∀ γ ∈ Y, ρ t * γ * (ρ t)⁻¹ ∈ Y) :
    T.relIndex (D.parOf Y) = B.relIndex Y := by
  set A := (Y.comap ρ).map (normalizer (U : Set G)).subtype ⊓ K with hA
  have hAU : A ≤ normalizer (U : Set G) := fun a ha => by
    obtain ⟨⟨a', -, rfl⟩, -⟩ := ha
    exact a'.2
  have hTA : T ≤ normalizer (A : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun t ht a ha => ?_
    obtain ⟨⟨a', ha'Y, rfl⟩, haK⟩ := ha
    have htU := hTU ht
    refine mem_inf.2 ⟨⟨⟨t, htU⟩ * a' * ⟨t, htU⟩⁻¹, ?_, rfl⟩,
      (mem_normalizer_iff.mp (D.TK ht) _).mp haK⟩
    show ρ (⟨t, htU⟩ * a' * ⟨t, htU⟩⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv]
    exact hTY ⟨t, htU⟩ ht _ ha'Y
  have hsup : T.relIndex (D.parOf Y) = (A ⊓ T).relIndex A := U3.relIndex_sup_eq hTA
  rw [hsup]
  set f : ↥A →* Γ := ρ.comp (Subgroup.inclusion hAU) with hf
  have hrange : f.range = Y := by
    ext γ
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨⟨a', ha'Y, ha'⟩, -⟩ := a.2
      have e : (Subgroup.inclusion hAU a : ↥(normalizer (U : Set G))) = a' :=
        Subtype.ext ha'.symm
      show ρ (Subgroup.inclusion hAU a) ∈ Y
      rw [e]
      exact ha'Y
    · intro hγ
      obtain ⟨g, hgK, rfl⟩ := D.img γ (hYQ hγ)
      exact ⟨⟨g, mem_inf.2 ⟨⟨g, hγ, rfl⟩, hgK⟩⟩, rfl⟩
  have hcomap : (A ⊓ T).subgroupOf A = B.comap f := by
    ext a
    rw [mem_subgroupOf, Subgroup.mem_comap]
    have haK : (a : G) ∈ K := (mem_inf.1 a.2).2
    constructor
    · intro h
      exact hTB (Subgroup.inclusion hAU a) (mem_inf.2 ⟨(mem_inf.1 h).2, haK⟩)
    · intro h
      obtain ⟨t, htTK, hρt⟩ := hB _ h
      refine mem_inf.2 ⟨a.2, ?_⟩
      have h1 : ρ (Subgroup.inclusion hAU a * t⁻¹) = 1 := by
        rw [map_mul, map_inv, hρt]
        exact mul_inv_cancel _
      have h2 := D.ker _ (mul_mem haK (inv_mem (mem_inf.1 htTK).2)) h1
      have e : (a : G) =
          ((Subgroup.inclusion hAU a * t⁻¹ : ↥(normalizer (U : Set G))) : G) * t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right, coe_inclusion]
      rw [e]
      exact mul_mem h2 (mem_inf.1 htTK).1
  rw [relIndex, hcomap, Subgroup.index_comap, hrange]

theorem not_le_normalizer_parOf {B Y : Subgroup Γ}
    (hTB : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K → ρ g ∈ B)
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    (hYQ : Y ≤ Q) {γ β : Γ} (hγ : γ ∈ Y) (hβ : β ∈ B) (hγβ : γ * β * γ⁻¹ ∉ B) :
    ¬ D.parOf Y ≤ normalizer (T : Set G) := by
  intro hN
  obtain ⟨g, hgK, rfl⟩ := D.img γ (hYQ hγ)
  obtain ⟨t, htTK, rfl⟩ := hB β hβ
  have hg : (g : G) ∈ D.parOf Y := D.mem_parOf hgK hγ
  have h1 : (g : G) * t * (g : G)⁻¹ ∈ T :=
    (mem_normalizer_iff.mp (hN hg) t).mp (mem_inf.1 htTK).1
  have h2 : (g : G) * t * (g : G)⁻¹ ∈ K :=
    mul_mem (mul_mem hgK (mem_inf.1 htTK).2) (inv_mem hgK)
  apply hγβ
  have := hTB (g * t * g⁻¹) (mem_inf.2 ⟨h1, h2⟩)
  rwa [map_mul, map_mul, map_inv] at this

theorem img'_mono {X X' : Subgroup G} (h : X ≤ X') : D.img' X ≤ D.img' X' :=
  Subgroup.map_mono fun _ hg => mem_subgroupOf.2 (inf_le_inf_right K h (mem_subgroupOf.1 hg))

theorem le_img'_parOf {Y : Subgroup Γ} (hYQ : Y ≤ Q) : Y ≤ D.img' (D.parOf Y) := by
  intro γ hγ
  obtain ⟨g, hgK, rfl⟩ := D.img γ (hYQ hγ)
  exact D.mem_img' (mem_inf.2 ⟨D.mem_parOf hgK hγ, hgK⟩)

theorem img'_parOf_le {B Y : Subgroup Γ} (hTU : T ≤ normalizer (U : Set G))
    (hTB : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K → ρ g ∈ B) (hBY : B ≤ Y)
    (hTY : ∀ t : ↥(normalizer (U : Set G)), (t : G) ∈ T → ∀ γ ∈ Y, ρ t * γ * (ρ t)⁻¹ ∈ Y) :
    D.img' (D.parOf Y) ≤ Y := by
  set A := (Y.comap ρ).map (normalizer (U : Set G)).subtype ⊓ K with hA
  have hTA : T ≤ normalizer (A : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun t ht a ha => ?_
    obtain ⟨⟨a', ha'Y, rfl⟩, haK⟩ := ha
    have htU := hTU ht
    refine mem_inf.2 ⟨⟨⟨t, htU⟩ * a' * ⟨t, htU⟩⁻¹, ?_, rfl⟩,
      (mem_normalizer_iff.mp (D.TK ht) _).mp haK⟩
    show ρ (⟨t, htU⟩ * a' * ⟨t, htU⟩⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv]
    exact hTY ⟨t, htU⟩ ht _ ha'Y
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hgX, hgK⟩ := mem_inf.1 (mem_subgroupOf.1 hg)
  obtain ⟨a, haA, t, ht, hat⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hTA hgX
  obtain ⟨⟨a', ha'Y, rfl⟩, haK⟩ := haA
  have hat' : (g : G) = (a' : G) * t := hat
  have haK' : (a' : G) ∈ K := haK
  have htK : t ∈ K := by
    have e : t = ((a' : G))⁻¹ * g := by rw [hat']; group
    rw [e]
    exact mul_mem (inv_mem haK') hgK
  have htU := hTU ht
  have e : g = a' * ⟨t, htU⟩ := Subtype.ext hat'
  rw [e, map_mul]
  exact mul_mem ha'Y (hBY (hTB ⟨t, htU⟩ (mem_inf.2 ⟨ht, htK⟩)))

theorem quot_parOf [Finite G] {B Y : Subgroup Γ} (hTU : T ≤ normalizer (U : Set G))
    (hTB : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K → ρ g ∈ B)
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    (hYQ : Y ≤ Q)
    (hTY : ∀ t : ↥(normalizer (U : Set G)), (t : G) ∈ T → ∀ γ ∈ Y, ρ t * γ * (ρ t)⁻¹ ∈ Y)
    (h3 : B.relIndex Y = 3) {γ β : Γ} (hγ : γ ∈ Y) (hβ : β ∈ B) (hγβ : γ * β * γ⁻¹ ∉ B)
    (hTsyl : IsSylowTwoOf T (D.parOf Y)) :
    quasithinO2QuotientIso (D.parOf Y) (Perm (Fin 3)) :=
  U3.quot_S3_of_index_three hTsyl (by rw [D.relIndex_parOf hTU hTB hB hYQ hTY, h3])
    (D.not_le_normalizer_parOf hTB hB hYQ hγ hβ hγβ)

end ParData

end CFSG.Quasithin.H13.NQS134
