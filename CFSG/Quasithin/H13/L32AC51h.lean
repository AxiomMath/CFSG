module

public import CFSG.Quasithin.H13.L32AC51g
public import CFSG.Quasithin.H13.L32ACSk4
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.Quasithin.H13.L32AC51f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Equiv Equiv.Perm

abbrev Alt8 : Type := ↥(alternatingGroup (Fin 8))

local notation "cS8" =>
  (MulAut.conjNormal : Equiv.Perm (Fin 8) →* MulAut CFSG.Quasithin.H13.L32A.C.Alt8)

namespace Lin

noncomputable def slFourEquivAlt8 : SLn 4 ≃* Alt8 :=
  (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm

theorem conjNormal_injective8 : Function.Injective cS8 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ Subgroup.centralizer (alternatingGroup (Fin 8) : Set (Perm (Fin 8))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut Alt8 => ((φ ⟨x, hx⟩ : Alt8) : Perm (Fin 8))) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rwa [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by simp)] at hc

theorem conjNormal_surjective8 : Function.Surjective cS8 :=
  CFSG.ComponentClassification.CatalogueSchreierAlternating.conjugation_surjective
    (Or.inr (by norm_num))

theorem eq_top_of_alt8 {R : Subgroup (Perm (Fin 8))} (hA : alternatingGroup (Fin 8) ≤ R)
    {x : Perm (Fin 8)} (hx : x ∈ R) (hxA : x ∉ alternatingGroup (Fin 8)) : R = ⊤ := by
  have h := Subgroup.relIndex_mul_index hA
  rw [alternatingGroup.index_eq_two] at h
  have hR : R.index = 1 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd R.index (Dvd.intro_left _ h) with h1 | h2
    · exact h1
    · exfalso
      rw [h2] at h
      have h3 : (alternatingGroup (Fin 8)).relIndex R = 1 := by omega
      exact hxA (Subgroup.relIndex_eq_one.mp h3 hx)
  exact Subgroup.index_eq_one.mp hR

end Lin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem false_of_graph (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h4 : Lemma14_7_4_two_three) (h28 : Lemma14_7_28) (hMod : Lemma14_7_51_Mod)
    (S : Setting147 G T L V H) {K : Subgroup G} (hcK : cComp H = {K}) (hHKT : H = K ⊔ T)
    (hL1K : l1 T L V ≤ K) (hP : IsPSL 4 2 1 (cStar K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {π : ↥K →* Lin.SLn 4}
    (hπ : Function.Surjective π) (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    {t₀ : G} (ht₀ : t₀ ∈ H)
    (hout : indHom π hπ hker hKn hHN ⟨t₀, ht₀⟩ ∉
      (MulAut.conj : Lin.SLn 4 →* MulAut (Lin.SLn 4)).range) : False := by
  have hK : K ∈ cComp H := by rw [hcK]; exact Set.mem_singleton K
  have hKH : K ≤ H := le_of_mem_cComp hK
  set ι := Lin.slFourEquivAlt8 with hι
  set π' : ↥K →* Alt8 := ι.toMonoidHom.comp π with hπ'def
  have hπ' : Function.Surjective π' := ι.surjective.comp hπ
  have hker' : ∀ k : ↥K, π' k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker]
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN
  set β' := indHom π' hπ' hker' hKn hHN with hβ'def
  have hβ' : ∀ (y : ↥H) (k : ↥K), β' y (π' k) = π' (conjK (hKn y.2) k) :=
    indHom_apply π' hπ' hker' hKn hHN
  have hKin : ∀ k (hk : k ∈ K), β' ⟨k, hKH hk⟩ = cS8 (π' ⟨k, hk⟩ : Perm (Fin 8)) := by
    intro k hk
    have e : MulAut.conj (π' ⟨k, hk⟩) = cS8 (π' ⟨k, hk⟩ : Perm (Fin 8)) := by
      ext x
      simp [MulAut.conjNormal_apply]
    rw [← e]
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ' a
    rw [hβ', MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hZ : Subgroup.center (cStar K) = ⊥ := by
    obtain ⟨φ⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
    have hc := card_center_eq_of_mulEquiv φ
    rw [Lin.center_eq_bot, Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc
  obtain ⟨ψ, hψ, hψker⟩ := quotIso_of_range π' hπ' hker' hKH hKn hHN cS8
    Lin.conjNormal_injective8 (fun y => Lin.conjNormal_surjective8 _)
    fun x hx hxc => mem_pCoreOf_of_comm h28 S hcK hL1K hKn hZ hx hxc
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = (π' ⟨k, hk⟩ : Perm (Fin 8)) := by
    intro k hk
    apply Lin.conjNormal_injective8
    rw [hψ, hKin k hk]
  have hA8 : alternatingGroup (Fin 8) ≤ ψ.range := by
    intro a ha
    obtain ⟨k, hk⟩ := hπ' ⟨a, ha⟩
    exact ⟨⟨k, hKH k.2⟩, by rw [hψK k k.2, hk]⟩
  have hnot : ψ ⟨t₀, ht₀⟩ ∉ alternatingGroup (Fin 8) := by
    intro ha
    set b : Alt8 := ⟨ψ ⟨t₀, ht₀⟩, ha⟩ with hb
    have hcb : β' ⟨t₀, ht₀⟩ = MulAut.conj b := by
      rw [← hψ]
      ext x
      simp [MulAut.conjNormal_apply, hb]
    apply hout
    refine ⟨ι.symm b, ?_⟩
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := hπ x
    apply ι.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hβ]
    have h1 := hβ' ⟨t₀, ht₀⟩ k
    rw [hcb, MulAut.conj_apply] at h1
    exact h1
  have hψs : Function.Surjective ψ := MonoidHom.range_eq_top.mp
    (Lin.eq_top_of_alt8 hA8 ⟨⟨t₀, ht₀⟩, rfl⟩ hnot)
  have h13322 := stmt13_3_2_two_of h1332
  have hMod' := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp h13322 hMod' h1222
  have h2 := hMod G T L V H S K hK hHKT hL1K hP ψ hψs hψker V₂ hV2
  have h1 := (h4 _ T L V V₂ S.hyp hV2).2.2.2.2
  omega

end CFSG.Quasithin.H13.L32A.C
