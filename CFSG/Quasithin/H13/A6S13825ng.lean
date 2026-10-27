module

public import CFSG.Quasithin.H13.A6S13825nb
public import CFSG.Quasithin.H13.A6S13825nc

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.SBd8.Flag

namespace L13825

section Hom

variable {Y : Type} [Group Y] {n : ℕ} {K : Subgroup Y}
  (e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2))

theorem alphaOf_congr {s t : Y} (hs : s ∈ Subgroup.normalizer (K : Set Y))
    (ht : t ∈ Subgroup.normalizer (K : Set Y)) (h : s = t) : alphaOf e hs = alphaOf e ht := by
  subst h
  rfl

theorem alphaOf_mul {s t : Y} (hs : s ∈ Subgroup.normalizer (K : Set Y))
    (ht : t ∈ Subgroup.normalizer (K : Set Y)) :
    alphaOf e (Subgroup.mul_mem _ hs ht) = alphaOf e hs * alphaOf e ht := by
  refine MulEquiv.ext fun g => ?_
  obtain ⟨k, rfl⟩ := e.surjective g
  rw [MulAut.mul_apply, alphaOf_apply, alphaOf_apply, alphaOf_apply]
  congr 1
  apply Subtype.ext
  simp only [conjOn_coe]
  group

theorem alphaOf_one : alphaOf e (Subgroup.one_mem (Subgroup.normalizer (K : Set Y))) = 1 := by
  refine MulEquiv.ext fun g => ?_
  obtain ⟨k, rfl⟩ := e.surjective g
  rw [alphaOf_apply, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  simp [conjOn_coe]

theorem alphaOf_of_mem {k : Y} (hk : k ∈ K) (hkN : k ∈ Subgroup.normalizer (K : Set Y)) :
    alphaOf e hkN = MulAut.conj (e ⟨k, hk⟩) := by
  refine MulEquiv.ext fun g => ?_
  obtain ⟨x, rfl⟩ := e.surjective g
  rw [alphaOf_apply, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  rfl

theorem alphaOf_eq_one_iff {t : Y} (ht : t ∈ Subgroup.normalizer (K : Set Y)) :
    alphaOf e ht = 1 ↔ t ∈ Subgroup.centralizer (K : Set Y) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) => φ (e ⟨k, hk⟩)) h
    simp only [alphaOf_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    rw [conjOn_coe] at h2
    calc k * t = t * k * t⁻¹ * t := by rw [h2]
      _ = t * k := by group
  · intro h
    refine MulEquiv.ext fun g => ?_
    obtain ⟨k, rfl⟩ := e.surjective g
    rw [alphaOf_apply, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [conjOn_coe, ← Subgroup.mem_centralizer_iff.mp h k k.2, mul_inv_cancel_right]

@[expose] def rhoAut {X : Type*} [Group X] (st : X →* Y)
    (hst : ∀ x, st x ∈ Subgroup.normalizer (K : Set Y)) :
    X →* MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) where
  toFun x := alphaOf e (hst x)
  map_one' := (alphaOf_congr e _ _ (map_one st)).trans (alphaOf_one e)
  map_mul' x y := (alphaOf_congr e _ _ (map_mul st x y)).trans (alphaOf_mul e (hst x) (hst y))

theorem rhoAut_apply {X : Type*} [Group X] (st : X →* Y)
    (hst : ∀ x, st x ∈ Subgroup.normalizer (K : Set Y)) (x : X) :
    rhoAut e st hst x = alphaOf e (hst x) := rfl

end Hom

end L13825

namespace L4Tw

open L4Ind

theorem slGraphAut_eq : CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 (ZMod 2) =
    MulAut.conj w0 * tauW := by
  have hw : w0 * w0 = 1 := Subtype.ext w0_mul_self
  rw [tauW, ← mul_assoc, ← map_mul, hw, map_one, one_mul]

theorem exists_nf (α : MulAut SL4) : ∃ A ε, α = nf A ε := by
  rcases G11.P4GL.aut_SL_cases (by norm_num : 3 ≤ 4) α with ⟨A, hA⟩ | ⟨A, hA⟩
  · exact ⟨_, false, by rw [hA, L13825.slConjugation_eq_conj, nf_false]⟩
  · refine ⟨(G11.P4GL.slEquiv 4).symm A * w0, true, ?_⟩
    rw [hA, L13825.slConjugation_eq_conj, slGraphAut_eq, nf_true, map_mul, mul_assoc]

theorem mem_U_of_map {A : SL4} {ε : Bool}
    (h : (unitriangular 4 (ZMod 2)).map (nf A ε).toMonoidHom = unitriangular 4 (ZMod 2)) :
    A ∈ unitriangular 4 (ZMod 2) := by
  have hτU : (unitriangular 4 (ZMod 2)).map (cond ε tauW 1).toMonoidHom =
      unitriangular 4 (ZMod 2) := by
    cases ε
    · exact Subgroup.map_id _
    · refine le_antisymm ?_ fun u hu => ⟨tauW u, tauW_mem_unitriangular hu, tauW_tauW u⟩
      rintro _ ⟨u, hu, rfl⟩
      exact tauW_mem_unitriangular hu
  have e1 : (unitriangular 4 (ZMod 2)).map (nf A ε).toMonoidHom =
      ((unitriangular 4 (ZMod 2)).map (cond ε tauW 1).toMonoidHom).map
        (MulAut.conj A).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  have h1 : (unitriangular 4 (ZMod 2)).map (MulAut.conj A).toMonoidHom =
      unitriangular 4 (ZMod 2) := by
    rw [← hτU, ← e1, hτU]
    exact h
  have h2 := CFSG.Quasithin.A38.map_conj_eq_iff.mp h1
  rw [normalizer_unitriangular,
    CFSG.Quasithin.SBd8.Flag.upperTriangular_eq_unitriangular (Nat.card_zmod 2)] at h2
  exact h2

theorem tauW_ne_one : tauW ≠ 1 := by
  intro h
  have h1 := congrArg (fun φ : MulAut SL4 => φ (uSL 1 0 0 0 0)) h
  simp only [MulAut.one_apply, tauW_uSL] at h1
  have := congrFun (congrFun (congrArg Subtype.val h1) 0) 1
  exact absurd this (by decide)

end L4Tw

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

open L13825 L4Ind L4Tw in
theorem aut_coords (h21 : Lem13821) (h16 : Lem13816)
    (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKn : IsPSL 4 2 1 ↥(S.KSt H K)) (hhat : ¬ IsHatA6 L)
    (hTK' : ¬ T ≤ K ⊔ pCoreOf 2 H) :
    ∃ ρ : ↥H →* MulAut SL4,
      Function.Surjective ρ ∧ (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      (∀ h : ↥H, (h : G) ∈ S.L1 → ∃ q ∈ Q13, ρ h = MulAut.conj q) ∧
      (∀ h : ↥H, (h : G) ∈ T → ∃ u ∈ unitriangular 4 (ZMod 2), ∃ ε, ρ h = L4Tw.nf u ε) ∧
      (∀ u ∈ unitriangular 4 (ZMod 2), ∃ h : ↥H, (h : G) ∈ T ∧ ρ h = MulAut.conj u) ∧
      (∀ q ∈ Q13, ∃ h : ↥H, (h : G) ∈ S.L1 ⊔ T ∧ ρ h = MulAut.conj q) ∧
      ∃ h : ↥H, (h : G) ∈ T ∧ ρ h = tauW := by
  obtain ⟨hKsHs, hHsN, -, -, hC, -⟩ := star_setup h21 h16 hS hH hK (by norm_num) hKn
  obtain ⟨e, he, hQ⟩ := exists_std_equiv_A6 h21 h16 h1334 hS hH hK hKn hhat hTK'
  have hF := (hS.hF H hH).toHypF91
  obtain ⟨st, hstdef⟩ : ∃ st, st = S1549C.starHom hF := ⟨_, rfl⟩
  have hstH : ∀ h : ↥H, st h ∈ S.KSt H H := fun h => by
    rw [S.kst_top hF, hstdef]
    exact ⟨h, rfl⟩
  have hstN : ∀ h : ↥H, st h ∈ Subgroup.normalizer (S.KSt H K : Set _) := fun h => hHsN (hstH h)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = rhoAut e st hstN := ⟨_, rfl⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hL1K : S.L1 ≤ K := (h21 G T L V S hS H hH K hK).1
  have hker : ∀ h : ↥H, st h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
    rw [hstdef]
    exact S1549C.starHom_eq_one_iff hF
  have hKst : S.KSt H K = (K.subgroupOf H).map st := by rw [hstdef]; exact S.kst_eq hF hKH
  have hTst : S.KSt H T = (T.subgroupOf H).map st := by rw [hstdef]; exact S.kst_eq hF hTH
  have hρK : ∀ (h : ↥H) (hk : st h ∈ S.KSt H K), ρ h = MulAut.conj (e ⟨st h, hk⟩) :=
    fun h hk => by rw [hρ, rhoAut_apply]; exact alphaOf_of_mem e hk (hstN h)
  have hstK : ∀ h : ↥H, (h : G) ∈ K → st h ∈ S.KSt H K := fun h hh => by
    rw [hKst]
    exact ⟨h, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
  have hP7 : ∀ u ∈ unitriangular 4 (ZMod 2), ∃ h : ↥H, (h : G) ∈ T ∧ ρ h = MulAut.conj u := by
    intro u hu
    rw [← he] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have hxT := (Subgroup.mem_subgroupOf.mp hx).1
    rw [hTst] at hxT
    obtain ⟨t, ht, htx⟩ := hxT
    have htK : st t ∈ S.KSt H K := htx ▸ x.2
    refine ⟨t, Subgroup.mem_subgroupOf.mp ht, ?_⟩
    rw [hρK t htK, show (⟨st t, htK⟩ : ↥(S.KSt H K)) = x from Subtype.ext htx]
    rfl
  have hP3 : ∀ h : ↥H, (h : G) ∈ T →
      ∃ u ∈ unitriangular 4 (ZMod 2), ∃ ε, ρ h = L4Tw.nf u ε := by
    intro t ht
    have htT : st t ∈ S.KSt H T := by
      rw [hTst]
      exact ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have htTK : st t ∈ Subgroup.normalizer ((S.KSt H T ⊓ S.KSt H K : Subgroup _) : Set _) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htT, hstN t⟩
    have hα : (unitriangular 4 (ZMod 2)).map (ρ t).toMonoidHom = unitriangular 4 (ZMod 2) := by
      rw [← he]
      rw [hρ, rhoAut_apply]
      exact map_alphaOf e (hstN t) htTK
    obtain ⟨A, ε, hA⟩ := exists_nf (ρ t)
    rw [hA] at hα
    exact ⟨A, mem_U_of_map hα, ε, hA⟩
  have hnotK : ∀ h : ↥H, (h : G) ∉ K ⊔ pCoreOf 2 H → st h ∉ S.KSt H K := by
    intro h hh hk
    rw [hKst] at hk
    obtain ⟨k, hk, hkh⟩ := hk
    apply hh
    have h1 : st (k⁻¹ * h) = 1 := by rw [map_mul, map_inv, hkh, inv_mul_cancel]
    have h2 := (hker _).1 h1
    have e : (h : G) = (k : G) * ((k⁻¹ * h : ↥H) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hk) h2
  obtain ⟨tτ, htτT, htτ⟩ : ∃ h : ↥H, (h : G) ∈ T ∧ ρ h = tauW := by
    obtain ⟨t₀, ht₀T, ht₀K⟩ : ∃ t ∈ T, t ∉ K ⊔ pCoreOf 2 H := by
      by_contra hcon
      push Not at hcon
      exact hTK' hcon
    obtain ⟨u, hu, ε, hu₀⟩ := hP3 ⟨t₀, hTH ht₀T⟩ ht₀T
    cases ε
    · exfalso
      refine alphaOf_ne_conj e (hstN ⟨t₀, hTH ht₀T⟩) hKsHs (hstH _) (hnotK _ ht₀K) hC u ?_
      rw [← rhoAut_apply e st hstN, ← hρ, hu₀, nf_false]
    obtain ⟨t₁, ht₁T, ht₁⟩ := hP7 u hu
    refine ⟨t₁⁻¹ * ⟨t₀, hTH ht₀T⟩, T.mul_mem (T.inv_mem ht₁T) ht₀T, ?_⟩
    rw [map_mul, map_inv, ht₁, hu₀, nf_true, inv_mul_cancel_left]
  refine ⟨ρ, ?_, ?_, ?_, hP3, hP7, ?_, tτ, htτT, htτ⟩
  ·
    intro α
    obtain ⟨A, ε, rfl⟩ := exists_nf α
    obtain ⟨x, rfl⟩ := e.surjective A
    obtain ⟨k, -, hkx⟩ : (x : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ∈
        (K.subgroupOf H).map st := by
      rw [← hKst]
      exact x.2
    have hkK : st k ∈ S.KSt H K := hkx ▸ x.2
    have hρk : ρ k = MulAut.conj (e x) := by
      rw [hρK k hkK, show (⟨st k, hkK⟩ : ↥(S.KSt H K)) = x from Subtype.ext hkx]
    cases ε
    · exact ⟨k, by rw [hρk, nf_false]⟩
    · exact ⟨k * tτ, by rw [map_mul, hρk, htτ, nf_true]⟩
  ·
    intro h
    rw [hρ, rhoAut_apply, alphaOf_eq_one_iff, ← hker]
    constructor
    · intro hc
      have : st h ∈ S.KSt H H ⊓ Subgroup.centralizer (S.KSt H K : Set _) := ⟨hstH h, hc⟩
      rw [hC] at this
      exact this
    · intro h1
      rw [h1]
      exact Subgroup.one_mem _
  ·
    intro l hl
    have hlK := hstK l (hL1K hl)
    refine ⟨e ⟨st l, hlK⟩, ?_, hρK l hlK⟩
    rw [show Q13 = flagStabilizer 4 (ZMod 2) (minPar 4 2) from rfl, ← hQ, mem_toSL e]
    simp only [MulEquiv.symm_apply_apply]
    refine Subgroup.mem_sup_left ?_
    rw [S.kst_eq hF hL1H, ← hstdef]
    exact ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  ·
    intro q hq
    rw [show Q13 = flagStabilizer 4 (ZMod 2) (minPar 4 2) from rfl, ← hQ, mem_toSL e] at hq
    have hq' : ((e.symm q : ↥(S.KSt H K)) : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ∈
        S.KSt H (S.L1 ⊔ T) := by
      rw [S.kst_sup hF hL1H hTH]
      exact (sup_le_sup_left (inf_le_left : S.KSt H T ⊓ S.KSt H K ≤ S.KSt H T)
        (S.KSt H S.L1)) hq
    rw [S.kst_eq hF (sup_le hL1H hTH), ← hstdef] at hq'
    obtain ⟨h, hh, hhq⟩ := hq'
    have hhK : st h ∈ S.KSt H K := hhq ▸ (e.symm q).2
    refine ⟨h, Subgroup.mem_subgroupOf.mp hh, ?_⟩
    rw [hρK h hhK, show (⟨st h, hhK⟩ : ↥(S.KSt H K)) = e.symm q from Subtype.ext hhq,
      e.apply_symm_apply]

end Setting4

end CFSG.Quasithin.H13.A6
