module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin

namespace Lem1227Eq

variable {Γ : Type} [Group Γ]

theorem exists_maximal_overgroup [Finite Γ] {B Ks : Subgroup Γ} (hB : B ≤ Ks) (hne : B ≠ Ks) :
    ∃ P : Subgroup Γ, B ≤ P ∧ P ≤ Ks ∧ P ≠ Ks ∧
      ∀ Q : Subgroup Γ, Q ≤ Ks → P ≤ Q → Q = P ∨ Q = Ks := by
  classical
  have : Finite (Subgroup Γ) :=
    Finite.of_injective (fun H : Subgroup Γ => (H : Set Γ)) SetLike.coe_injective
  obtain ⟨P, ⟨hBP, hPK, hPne⟩, hmax⟩ := Set.exists_max_image
    {P : Subgroup Γ | B ≤ P ∧ P ≤ Ks ∧ P ≠ Ks} (fun P : Subgroup Γ => Nat.card P)
    (Set.toFinite _) ⟨B, le_rfl, hB, hne⟩
  refine ⟨P, hBP, hPK, hPne, fun Q hQK hPQ => ?_⟩
  by_cases hQ : Q = Ks
  · exact Or.inr hQ
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hPQ (hmax Q ⟨hBP.trans hPQ, hQK, hQ⟩)).symm

theorem not_isDiagramNontrivial_of_stable {Ks S Ts P : Subgroup Γ} (hS : IsSylowTwoOf S Ks)
    (hPK : P ≤ Ks) (hPne : P ≠ Ks)
    (hPmax : ∀ Q : Subgroup Γ, Q ≤ Ks → P ≤ Q → Q = P ∨ Q = Ks)
    (hB : Ks ⊓ Subgroup.normalizer (S : Set Γ) ≤ P)
    (hT : Ts ≤ Subgroup.normalizer (P : Set Γ)) : ¬ E2.IsDiagramNontrivial Ts Ks S := by
  intro hD
  have hpar : IsParabolic2 Ks P := ⟨hPK, S, hS, hB⟩
  refine hD P ⟨hpar, hPne, fun Q hQ hQne hPQ => ?_⟩ hB hT
  rcases hPmax Q hQ.1 hPQ with h | h
  · exact h
  · exact absurd h hQne

theorem not_isDiagramNontrivial_of_inner [Finite Γ] {Ks S Ts : Subgroup Γ}
    (hS : IsSylowTwoOf S Ks) (hnn : ¬ Ks ≤ Subgroup.normalizer (S : Set Γ))
    (hTK : Ts ≤ Subgroup.normalizer (Ks : Set Γ)) (hTS : Ts ≤ Subgroup.normalizer (S : Set Γ))
    (hinn : ∀ d ∈ Ts, ∃ k ∈ Ks, ∀ x ∈ Ks, d * x * d⁻¹ = k * x * k⁻¹) :
    ¬ E2.IsDiagramNontrivial Ts Ks S := by
  have hBK : Ks ⊓ Subgroup.normalizer (S : Set Γ) ≤ Ks := inf_le_left
  have hBne : Ks ⊓ Subgroup.normalizer (S : Set Γ) ≠ Ks := fun h =>
    hnn (h ▸ inf_le_right)
  obtain ⟨P, hBP, hPK, hPne, hPmax⟩ := exists_maximal_overgroup hBK hBne
  refine not_isDiagramNontrivial_of_stable hS hPK hPne hPmax hBP fun d hd => ?_
  obtain ⟨k, hkK, hk⟩ := hinn d hd
  have hkN : k ∈ Subgroup.normalizer (S : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hk y (hS.1 hy)]
      exact (Subgroup.mem_normalizer_iff.1 (hTS hd) y).1 hy
    · intro hy
      have hyK : y ∈ Ks := by
        have h1 := Ks.mul_mem (Ks.mul_mem (Ks.inv_mem hkK) (hS.1 hy)) hkK
        simpa [mul_assoc] using h1
      rw [← hk y hyK] at hy
      exact (Subgroup.mem_normalizer_iff.1 (hTS hd) y).2 hy
  have hkP : k ∈ P := hBP ⟨hkK, hkN⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hk y (hPK hy)]
    exact P.mul_mem (P.mul_mem hkP hy) (P.inv_mem hkP)
  · intro hy
    have hyK : y ∈ Ks :=
      (Subgroup.mem_normalizer_iff.1 (hTK hd) y).2 (hPK hy)
    rw [hk y hyK] at hy
    have h1 := P.mul_mem (P.mul_mem (P.inv_mem hkP) hy) hkP
    simpa [mul_assoc] using h1

theorem autCard_le_eight_of_inner [Finite Γ] {Ks Ts : Subgroup Γ} (hT2 : IsPGroup 2 ↥Ts)
    (hTK : Ts ≤ Subgroup.normalizer (Ks : Set Γ)) (hZ : Subgroup.center ↥Ks = ⊥)
    (hcard : Nat.card ↥Ks = 168)
    (hinn : ∀ d ∈ Ts, ∃ k ∈ Ks, ∀ x ∈ Ks, d * x * d⁻¹ = k * x * k⁻¹) :
    E2.autCard Ts Ks ≤ 8 := by
  have hTs : Ts ⊓ Subgroup.normalizer (Ks : Set Γ) = Ts := inf_eq_left.2 hTK
  unfold E2.autCard
  rw [hTs]
  set f : ↥Ts →* MulAut ↥Ks := Ks.normalizerMonoidHom.comp (Subgroup.inclusion hTK) with hf
  have hker : f.ker = (Ts ⊓ Subgroup.centralizer (Ks : Set Γ)).subgroupOf Ts := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨t.2, fun x hx => ?_⟩
      have h1 := congrArg (fun φ : MulAut ↥Ks => ((φ ⟨x, hx⟩ : ↥Ks) : Γ)) h
      simp only [hf, MonoidHom.comp_apply, MulAut.one_apply] at h1
      have h2 : ((Ks.normalizerMonoidHom (Subgroup.inclusion hTK t)) ⟨x, hx⟩ : Γ) =
          (t : Γ) * x * (t : Γ)⁻¹ := rfl
      rw [h2] at h1
      calc x * (t : Γ) = ((t : Γ) * x * (t : Γ)⁻¹) * t := by rw [h1]
        _ = (t : Γ) * x := by group
    · rintro ⟨-, h⟩
      refine MulEquiv.ext fun x => Subtype.ext ?_
      have h2 : ((Ks.normalizerMonoidHom (Subgroup.inclusion hTK t)) x : Γ) =
          (t : Γ) * x * (t : Γ)⁻¹ := rfl
      simp only [hf, MonoidHom.comp_apply, MulAut.one_apply]
      rw [h2, ← (h x x.2)]
      group
  have hrel : ((Ts ⊓ Subgroup.centralizer (Ks : Set Γ)).relIndex Ts) = Nat.card f.range := by
    unfold Subgroup.relIndex
    rw [← hker]
    exact Subgroup.index_ker f
  rw [hrel]
  set c : ↥Ks →* MulAut ↥Ks := MulAut.conj with hc
  have hcinj : Function.Injective c := by
    refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
    have hcen : g ∈ Subgroup.center ↥Ks := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut ↥Ks => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [hc, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hZ, Subgroup.mem_bot] at hcen
  have hrange : f.range ≤ c.range := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨k, hkK, hk⟩ := hinn t t.2
    refine ⟨⟨k, hkK⟩, ?_⟩
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have h2 : ((Ks.normalizerMonoidHom (Subgroup.inclusion hTK t)) x : Γ) =
        (t : Γ) * x * (t : Γ)⁻¹ := rfl
    simp only [hf, MonoidHom.comp_apply, hc, MulAut.conj_apply]
    rw [h2, hk x x.2]
    rfl
  have hcrange : Nat.card c.range = 168 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hcinj).toEquiv).symm
  have hdvd : Nat.card f.range ∣ 168 := hcrange ▸ Subgroup.card_dvd_of_le hrange
  have hp2 : IsPGroup 2 ↥f.range :=
    hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := hp2.exists_card_eq
  rw [hn] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hn4 : 4 ≤ n := by
    by_contra h4
    push Not at h4
    interval_cases n <;> simp at hlt
  have h16 : 16 ∣ 2 ^ n := by
    have : (2 : ℕ) ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 hn4
    simpa using this
  have := h16.trans hdvd
  omega

theorem isSylowTwoOf_top_iff' {X : Type*} [Group X] {S : Subgroup X} :
    IsSylowTwoOf S ⊤ ↔ IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.index := by
  unfold IsSylowTwoOf
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨le_top, h.1, h.2⟩⟩

theorem isSylowTwoOf_top_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ := by
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff'.mp hT
  refine isSylowTwoOf_top_iff'.mpr ⟨hp.map e.toMonoidHom, ?_⟩
  rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  exact hi

theorem exists_mulEquiv_map_eq_of_sylow {X Γ' : Type*} [Group X] [Finite X] [Group Γ']
    [Finite Γ'] (e : X ≃* Γ') {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) {S : Subgroup Γ'}
    (hS : IsSylowTwoOf S ⊤) : ∃ ψ : X ≃* Γ', T.map ψ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ := isSylowTwoOf_top_map e hT
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff'.mp hT'
  obtain ⟨hp₀, hi₀⟩ := isSylowTwoOf_top_iff'.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ' (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ' => (T : Subgroup Γ')) hg
    exact this.symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem not_le_normalizer_of_simple {Ks S : Subgroup Γ} (hS : IsSylowTwoOf S Ks)
    [IsSimpleGroup ↥Ks] (heven : 2 ∣ Nat.card ↥Ks) (hnot : ¬ IsPGroup 2 ↥Ks) :
    ¬ Ks ≤ Subgroup.normalizer (S : Set Γ) := by
  intro h
  have hN : (S.subgroupOf Ks).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hS.1).2 h
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf Ks) with h0 | h1
  · apply hS.2.2
    rw [h0, Subgroup.index_bot]
    exact heven
  · apply hnot
    have h2 : IsPGroup 2 ↥(S.subgroupOf Ks) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    rw [h1] at h2
    exact h2.of_equiv Subgroup.topEquiv

end Lem1227Eq

end CFSG.Quasithin.H13
