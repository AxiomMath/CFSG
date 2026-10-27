module

public import CFSG.Quasithin.Vol2.Ch11SecOE9O
public import CFSG.Quasithin.Vol2.Ch11SecOE9K
public import CFSG.Quasithin.Vol2.Ch11SecU1Crit

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin CFSG.Open
open CFSG.Quasithin.SteinbergBS (upper_of_mem_normalizer map_minorAut_pow_antiUnipotent)
open CFSG.QuasithinUnique.Fin257.Sp4 (wT wT_conj_uElt_zero)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} [L.Normal] (ψ : antiSp K ≃* ↥L)

omit [Finite K] [Finite G] [L.Normal] in
theorem exists_rootA_of_comap
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {A : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) : ∃ i : Axis, A.comap (emb ψ) ≤ rootA K i := by
  rcases elementary_le_radA1_or_radA2 (comap_le_antiUnipotent ψ hψ hAT)
    (fun x hx => mul_self_of_mem_comap ψ hA hx) with h | h
  · exact ⟨.one, h⟩
  · exact ⟨.two, h⟩

omit [Finite K] [CharP K 2] [Finite G] [L.Normal] in
theorem card_inf_eq (A : Subgroup G) :
    Nat.card ↥(A ⊓ L) = Nat.card (A.comap (emb ψ)) := by
  have h : (A.comap (emb ψ)).map (emb ψ) = A ⊓ L := by
    rw [Subgroup.map_comap_eq, range_emb, inf_comm]
  rw [← h, Subgroup.card_map_of_injective (emb_injective ψ)]

theorem exists_member_of_le_center (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hAS : AlmostSimple L) (hT : IsSylowIn 2 T ⊤)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcA : 2 ^ n < Nat.card A) (hAL : A ≤ L)
    (hZ : A.comap (emb ψ) ≤ antiUnipotentCenter K) :
    ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ X : Subgroup G,
      E1.IsE n ⊤ T (A1b.conjSub g A) X ∧ ¬ Group.IsSolvable ↥X := by
  set A₀ := A.comap (emb ψ) with hA₀
  have hAeq : A₀.map (emb ψ) = A := Subgroup.map_comap_eq_self (by rw [range_emb]; exact hAL)
  set A₀' := A₀.map (MulAut.conj (wT : antiSp K)).toMonoidHom with hA₀'
  have hconj : A1b.conjSub (emb ψ wT) A = A₀'.map (emb ψ) := by
    conv_lhs => rw [← hAeq]
    rw [conjSub_map_emb, autHom_emb]
  have hA₀'2 : A₀' ≤ radA2 K := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, c, rfl⟩ := hZ hz
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wT_conj_uElt_zero]
    exact ⟨b, 0, c, rfl⟩
  have hnZ : ¬ A₀' ≤ antiUnipotentCenter K := by
    intro h
    have hl : ∀ z ∈ A₀, ∃ c : K, z = uElt 0 0 c 0 := by
      intro z hz
      obtain ⟨b, c, rfl⟩ := hZ hz
      obtain ⟨b', c', h1⟩ := h ⟨_, hz, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wT_conj_uElt_zero] at h1
      obtain ⟨hb, -⟩ := uElt_inj h1
      exact ⟨c, by rw [hb]⟩
    let f : ↥A₀ → K := fun z => glMat ((z : antiSp K) : GL (Fin 4) K) 0 3
    have hf : Function.Injective f := by
      intro z₁ z₂ h12
      obtain ⟨c₁, hz₁⟩ := hl z₁ z₁.2
      obtain ⟨c₂, hz₂⟩ := hl z₂ z₂.2
      have h3 : c₁ = c₂ := by
        simpa [f, hz₁, hz₂, glMat_uElt, uMat] using h12
      exact Subtype.ext (by rw [hz₁, hz₂, h3])
    have h1 := Nat.card_le_card_of_injective f hf
    rw [hK, ← Subgroup.card_map_of_injective (emb_injective ψ), hAeq] at h1
    omega
  have hA'T : A1b.conjSub (emb ψ wT) A ≤ T := by
    rw [hconj]
    refine (Subgroup.map_mono (hA₀'2.trans radA2_le_antiUnipotent)).trans ?_
    rw [← inf_eq_map_emb ψ hψ]
    exact inf_le_left
  have hA' := SecU1.isElemAbelian_conjSub hA (emb ψ wT)
  have hcomap : (A1b.conjSub (emb ψ wT) A).comap (emb ψ) = A₀' := by
    rw [hconj, Subgroup.comap_map_eq_self_of_injective (emb_injective ψ)]
  obtain ⟨X, hX, hXs⟩ := exists_member_of_not_le_center ψ hK hn hAS hT hψ hA'T hA'
    (i := .two) (j := .one) (Or.inr ⟨rfl, rfl⟩) (hcomap ▸ hA₀'2) (hcomap ▸ hnZ)
  exact ⟨emb ψ wT, hA'T, X, hX, hXs⟩

theorem exists_member_of_not_le_even (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hev : Even n)
    (hAS : AlmostSimple L) (hT : IsSylowIn 2 T ⊤)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {A : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hcA : 2 ^ n < Nat.card A) (hAL : ¬ A ≤ L)
    (hZ : A.comap (emb ψ) ≤ antiUnipotentCenter K) :
    ∃ X : Subgroup G, E1.IsE n ⊤ T A X ∧ ¬ Group.IsSolvable ↥X := by
  have hC := hAS.centralizer_eq
  have h2 : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  have hcard : Nat.card A ≤ 2 * Nat.card (A.comap (emb ψ)) := by
    rw [← card_inf_eq ψ]
    exact card_le_two_mul_inf (by omega) hK ψ hC h2
  obtain ⟨a, haA, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hAL
  refine ⟨_, isE_parC ψ hK hn hψ hT hAT hA .one (fun t ht => ?_) ?_,
    fun hs => not_le_of_isSolvable hK hn (emb_injective ψ) .one hs le_sup_left⟩
  · have htN := SecE3.le_normalizer_inf (T := T) (L := L) (E1.tauOf_le _ _ _ ht)
    rcases fix_or_swap ψ hψ htN with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso
      obtain ⟨h, hh, r, hr⟩ :=
        exists_odd_of_swap (by omega) hK (map_autHom_antiUnipotent ψ hψ htN) h1
      have h3 := card_le_of_fixed_swap hK hev (by omega) hh r hZ fun z hz => by
        rw [← hr]
        exact autHom_eq_of_mem_comap ψ hAS ht hz
      have h4 : 2 * 2 ^ (n - 1) = 2 ^ n := by
        rw [← pow_succ']
        congr 1
        omega
      omega
  · refine ⟨a, haA, ?_⟩
    have haN := SecE3.le_normalizer_inf (T := T) (L := L) (hAT haA)
    have hθ2 : autHom ψ a * autHom ψ a = 1 := by rw [← map_mul, h2 a haA, map_one]
    have hθi : autHom ψ a ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
      intro hin
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hin
      exact haL ((eq_emb_of_autHom_eq ψ hC hy.symm) ▸ emb_mem ψ y)
    obtain ⟨g, hg⟩ := outer_involution_form (by omega) hK _ hθ2 hθi
    have hgU : g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
      have hU := map_autHom_antiUnipotent ψ hψ haN
      have hcomp : (MulAut.conj g * minorAut K ^ n).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp (minorAut K ^ n).toMonoidHom :=
        MonoidHom.ext fun _ => rfl
      rw [hg, hcomp, ← Subgroup.map_map, map_minorAut_pow_antiUnipotent] at hU
      rw [← A1b.conjSub_eq_iff_mem_normalizer]
      exact hU
    obtain ⟨s, rfl⟩ := hev
    obtain ⟨x, hx⟩ := exists_not_mem_radA1 hK (upper_of_mem_normalizer hgU) (s := s)
      (by omega) (by omega)
    refine ⟨uElt x 0 0 0, antiUnipotent_le_parC .one (uElt_mem_antiUnipotent x 0 0 0), ?_⟩
    rw [hg, show minorAut K ^ (s + s) = (minorAut K ^ 2) ^ s by rw [← pow_mul, two_mul]]
    exact hx

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
