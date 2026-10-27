module

public import CFSG.Quasithin.H13.KGFact68AltBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

@[expose] def SporadicSylowCenterCyclic : Prop :=
  ∀ s : TauCeti.SporadicName, Ch1.IsLemma115SporadicName s →
    ∀ T : Sylow 2 (NativeSporadic.Carrier s),
      IsCyclic (Subgroup.center ↥(T : Subgroup (NativeSporadic.Carrier s)))

section Facts

theorem eq_one_of_mem_center_quot {X : Type} [Group X] [Finite X] {w : X ⧸ CFSG.pCore 2 X}
    (hw : w ∈ Subgroup.center (X ⧸ CFSG.pCore 2 X)) {k : ℕ} (hk : w ^ 2 ^ k = 1) : w = 1 := by
  have hzn : (Subgroup.zpowers w).Normal := by
    constructor
    intro n hn g
    have hnc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hw) hn) g
    rw [hnc, mul_inv_cancel_right]
    exact hn
  let M : Subgroup X := (Subgroup.zpowers w).comap (QuotientGroup.mk' (CFSG.pCore 2 X))
  have hMn : M.Normal := hzn.comap _
  have hMp : IsPGroup 2 M := by
    intro x
    have hx : QuotientGroup.mk' (CFSG.pCore 2 X) (x : X) ∈ Subgroup.zpowers w := x.2
    obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.mpr hx
    dsimp only at hj
    have h1 : (x : X) ^ 2 ^ k ∈ CFSG.pCore 2 X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      change (QuotientGroup.mk' (CFSG.pCore 2 X) (x : X)) ^ 2 ^ k = 1
      rw [← hj, ← pow_mul, Nat.mul_comm, pow_mul, hk, one_pow]
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨_, h1⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, pow_add, pow_mul]
    exact congrArg Subtype.val hm
  have hMN : M ≤ CFSG.pCore 2 X :=
    le_sSup (show M ∈ {K : Subgroup X | K.Normal ∧ IsPGroup 2 K} from ⟨hMn, hMp⟩)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  have hy : y ∈ M := Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
  exact (QuotientGroup.eq_one_iff y).mpr (hMN hy)

end Facts

section Main

variable {Y : Type} [Group Y] [Finite Y] {L A R : Subgroup Y} {z : Y}

theorem pCore_two_le_center (h : E6.E68Hyp L A R z) :
    CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups h.quasisimple
      (N := CFSG.pCore 2 ↥L) CFSG.pCore_normal with hN | hN
  · exfalso
    have : Group.IsPerfect ↥L := h.quasisimple.1
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial h.quasisimple
    have hp : IsPGroup 2 ↥L := by
      have h1 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
      rw [hN] at h1
      exact h1.of_equiv Subgroup.topEquiv
    exact Group.IsPerfect.not_isNilpotent ↥L hp.isNilpotent
  · exact hN

theorem not_e68Hyp_of_inner_cyclic {K : Type} [Group K] [Finite K] (h : E6.E68Hyp L A R z)
    (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* K)
    (hinn : ∀ β : K ≃* K, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → Ch1.IsInnerAut β)
    (hcyc : ∀ P : Sylow 2 K, IsCyclic (Subgroup.center ↥(P : Subgroup K))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥L with hNdef
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.mp h.quasisimple.1
  have hN : N ≤ Subgroup.center ↥L := pCore_two_le_center h
  let ind : MulAut ↥L → MulAut K := fun α => MulAut.congr ψ (quotAut N α)
  have hind_inj : Function.Injective ind := by
    intro α β hαβ
    have h1 : quotAut N α = quotAut N β := (MulAut.congr ψ).injective hαβ
    have h2 : quotAut N (α * β⁻¹) = 1 := by
      rw [quotAut_mul, h1, ← quotAut_mul, mul_inv_cancel, quotAut_one]
    exact mul_inv_eq_one.mp (eq_one_of_quotAut_eq_one hN hperf h2)
  have hind_apply : ∀ (α : MulAut ↥L) (x : ↥L),
      ind α (ψ (x : ↥L ⧸ N)) = ψ ((α x : ↥L) : ↥L ⧸ N) := by
    intro α x
    show ψ (quotAut N α (ψ.symm (ψ (x : ↥L ⧸ N)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hind_mul : ∀ α β : MulAut ↥L, ind (α * β) = ind α * ind β := fun α β => by
    show MulAut.congr ψ (quotAut N (α * β)) =
      MulAut.congr ψ (quotAut N α) * MulAut.congr ψ (quotAut N β)
    rw [quotAut_mul, map_mul]
  have hind_one : ind 1 = 1 := by
    show MulAut.congr ψ (quotAut N 1) = 1
    rw [quotAut_one, map_one]
  let f : ↥L →* K := ψ.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q : Sylow 2 K := (sylowIn h).mapSurjective hf
  have hZK : ∀ c ∈ Subgroup.center K, ∀ k : ℕ, c ^ 2 ^ k = 1 → c = 1 := by
    intro c hc k hk
    have h1 : ψ.symm c ∈ Subgroup.center (↥L ⧸ N) := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro g
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc (ψ g)
    have h2 : ψ.symm c ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have h3 := eq_one_of_mem_center_quot h1 h2
    simpa using congrArg ψ h3
  have key : ∀ a (ha : a ∈ A), ∃ g ∈ omegaZ (Q : Subgroup K),
      ind (conjOn L a (leN h ha)) = MulAut.conj g := by
    intro a ha
    set β := ind (conjOn L a (leN h ha)) with hβ
    have hfix : ∀ t ∈ (Q : Subgroup K), β t = t := by
      intro t ht
      have ht' : t ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L).map f := ht
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ht'
      show ind (conjOn L a (leN h ha)) (ψ (p : ↥L ⧸ N)) = ψ (p : ↥L ⧸ N)
      rw [hind_apply, conjOn_fix_of_hyp h ha hp]
    have hsq : β * β = 1 := by
      rw [hβ, ← hind_mul, conjOn_sq_of_hyp h ha, hind_one]
    have hinv : ∀ x, β (β x) = x := fun x => by
      have := congrArg (fun γ : MulAut K => γ x) hsq
      simpa using this
    obtain ⟨l, hl⟩ := hinn β hinv ⟨Q, hfix⟩
    have hβg : β = MulAut.conj l⁻¹ := by
      ext x
      rw [hl x, MulAut.conj_apply, inv_inv]
    have hg2 : l⁻¹ * l⁻¹ ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : l⁻¹ * (l⁻¹ * y * l⁻¹⁻¹) * l⁻¹⁻¹ = y := by
        have := congrArg (fun γ : MulAut K => γ y) hsq
        rw [hβg] at this
        exact this
      calc y * (l⁻¹ * l⁻¹) = (l⁻¹ * (l⁻¹ * y * l⁻¹⁻¹) * l⁻¹⁻¹) * (l⁻¹ * l⁻¹) := by rw [h1]
        _ = l⁻¹ * l⁻¹ * y := by group
    obtain ⟨e, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card K) Nat.card_pos.ne'
    have hgm2 : l⁻¹ ^ m * l⁻¹ ^ m = 1 := by
      have h1 : (l⁻¹ * l⁻¹) ^ m ∈ Subgroup.center K := Subgroup.pow_mem _ hg2 m
      have h2 : ((l⁻¹ * l⁻¹) ^ m) ^ 2 ^ e = 1 := by
        rw [← pow_mul, Nat.mul_comm, ← hcard]
        exact pow_card_eq_one'
      rw [← (Commute.refl l⁻¹).mul_pow]
      exact hZK _ h1 e h2
    have hβm : β = MulAut.conj (l⁻¹ ^ m) := by
      obtain ⟨j, rfl⟩ := hm
      rw [map_pow, ← hβg, pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
    refine ⟨l⁻¹ ^ m, mem_omegaZ_of_commute Q (fun t ht => ?_) hgm2, hβm⟩
    have h1 := hfix t ht
    rw [hβm, MulAut.conj_apply] at h1
    calc l⁻¹ ^ m * t = (l⁻¹ ^ m * t * (l⁻¹ ^ m)⁻¹) * l⁻¹ ^ m := by group
      _ = t * l⁻¹ ^ m := by rw [h1]
  have hcard : Nat.card (actHom L A (leN h)).range ≤ Nat.card (omegaZ (Q : Subgroup K)) := by
    have key' : ∀ φ : ↥(actHom L A (leN h)).range,
        ∃ g : omegaZ (Q : Subgroup K), ind φ = MulAut.conj (g : K) := by
      rintro ⟨φ, a, rfl⟩
      obtain ⟨g, hg, he⟩ := key a a.2
      exact ⟨⟨g, hg⟩, he⟩
    choose F hF using key'
    refine Nat.card_le_card_of_injective F fun φ₁ φ₂ h12 => Subtype.ext (hind_inj ?_)
    rw [hF φ₁, hF φ₂, h12]
  have h4 := h.four_le
  rw [relIndex_eq_card_range L A (leN h)] at h4
  have h2 := card_omegaZ_le_two (Q : Subgroup K) (hcyc Q)
  omega

end Main

theorem isSQTK_of_isLemma115 {s : TauCeti.SporadicName} (hs : Ch1.IsLemma115SporadicName s) :
    Ch1.IsSQTKSporadicName s ∧ s ≠ .J1 := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by unfold Ch1.IsSQTKSporadicName; decide, by decide⟩

theorem e68ComponentFactsSpor_of (hInn : Ch1.SporadicAutInner)
    (hcyc : SporadicSylowCenterCyclic) : E6.E68ComponentFactsSpor := by
  intro Y _ _ L A R z hcase h
  exfalso
  obtain ⟨⟨s, hs, ⟨ψ⟩⟩, -⟩ := hcase
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨hsq, hne⟩ := isSQTK_of_isLemma115 hs
  exact not_e68Hyp_of_inner_cyclic h ψ
    (fun β hβ hP => hInn s hsq hne (NativeSporadic.Carrier s) ⟨MulEquiv.refl _⟩ β hβ hP)
    (hcyc s hs)

end CFSG.Quasithin.H13.KG68
