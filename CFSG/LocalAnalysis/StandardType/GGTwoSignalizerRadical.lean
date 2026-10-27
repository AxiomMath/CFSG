module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.BorelTits

section Defs

variable {G : Type*} [Group G]

@[expose] def GGRadicalTwo (G₀ Q : Subgroup G) : Prop :=
  pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = Q

@[expose] def ggOppositeRadicals (G₀ Q : Subgroup G) : Set (Subgroup G) :=
  {V | GGRadicalTwo G₀ V ∧ Nat.card V = Nat.card Q ∧
    V ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = ⊥}

theorem GGRadicalTwo.le {G₀ Q : Subgroup G} (h : GGRadicalTwo G₀ Q) : Q ≤ G₀ :=
  calc Q = pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (Q : Set G)) := h.symm
    _ ≤ G₀ ⊓ Subgroup.normalizer (Q : Set G) := pCoreOf_le 2 _
    _ ≤ G₀ := inf_le_left

theorem GGRadicalTwo.isPGroup [Finite G] {G₀ Q : Subgroup G} (h : GGRadicalTwo G₀ Q) :
    IsPGroup 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← h]
  exact pCoreOf_isPGroup 2 _

end Defs

namespace GGTwoSig

variable {G : Type*} [Group G]

theorem map_conj_eq {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  refine SetLike.coe_injective ?_
  rw [Subgroup.coe_map]
  exact Subgroup.mem_normalizer_iff_conj_image_eq.1 hg

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff_conj_image_eq.2 ?_
  have h' := congrArg (fun K : Subgroup G => (K : Set G)) h
  simpa only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom] using h'

theorem map_conj_normalizer (H : Subgroup G) (g : G) :
    (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)

theorem map_conj_inf (A B : Subgroup G) (g : G) :
    (A ⊓ B).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom ⊓ B.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_inf_eq A B _ (MulAut.conj g).injective

theorem map_conj_pCoreOf (H : Subgroup G) (g : G) :
    (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom =
      pCoreOf 2 (H.map (MulAut.conj g).toMonoidHom) :=
  (pCoreOf_map_mulEquiv 2 (MulAut.conj g) H).symm

theorem map_conj_one (H : Subgroup G) : H.map (MulAut.conj (1 : G)).toMonoidHom = H :=
  map_conj_eq (Subgroup.one_mem _)

theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_inf_normalizer {G₀ T : Subgroup G} {g : G}
    (hg₀ : g ∈ Subgroup.normalizer (G₀ : Set G)) (hgT : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer ((G₀ ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_conj_eq ?_
  rw [map_conj_inf, map_conj_normalizer, map_conj_eq hg₀, map_conj_eq hgT]

end GGTwoSig

open GGTwoSig in
theorem GGRadicalTwo.map_conj {G : Type*} [Group G] {G₀ V : Subgroup G}
    (hV : GGRadicalTwo G₀ V) {g : G} (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    GGRadicalTwo G₀ (V.map (MulAut.conj g).toMonoidHom) := by
  have h1 : G₀ ⊓ Subgroup.normalizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (G₀ ⊓ Subgroup.normalizer (V : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [map_conj_inf, map_conj_normalizer, map_conj_eq hg]
  unfold GGRadicalTwo at hV ⊢
  rw [h1, ← map_conj_pCoreOf, hV]

namespace GGTwoSig

variable {G : Type*} [Group G]

theorem mem_ggOppositeRadicals_map_conj {G₀ Q V : Subgroup G}
    (hV : V ∈ ggOppositeRadicals G₀ Q) {g : G} (hg₀ : g ∈ Subgroup.normalizer (G₀ : Set G))
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ∈ ggOppositeRadicals G₀ Q := by
  obtain ⟨hrad, hcard, hbot⟩ := hV
  refine ⟨hrad.map_conj hg₀, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  · have h1 : (G₀ ⊓ Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom =
        G₀ ⊓ Subgroup.normalizer (Q : Set G) := by
      rw [map_conj_inf, map_conj_normalizer, map_conj_eq hg₀, map_conj_eq hgQ]
    calc V.map (MulAut.conj g).toMonoidHom ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G))
        = V.map (MulAut.conj g).toMonoidHom ⊓
            (G₀ ⊓ Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom := by
          rw [h1]
      _ = (V ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G))).map (MulAut.conj g).toMonoidHom :=
          (map_conj_inf _ _ g).symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]

theorem exists_radicalTwo [Finite G] {G₀ E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (G₀ : Set G)) :
    ∀ T : Subgroup G, T ≤ G₀ → IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set G) →
      ∃ Q : Subgroup G, T ≤ Q ∧ GGRadicalTwo G₀ Q ∧ E ≤ Subgroup.normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T
  induction T using WellFoundedGT.induction with
  | _ T ih =>
    intro hTG₀ hT hET
    have hTT' : T ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (T : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 (le_inf hTG₀ Subgroup.le_normalizer) inf_le_right hT
    by_cases hfix : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (T : Set G)) = T
    · exact ⟨T, le_rfl, hfix, hET⟩
    · have hlt : T < pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (T : Set G)) :=
        lt_of_le_of_ne hTT' (Ne.symm hfix)
      have hT'G₀ : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (T : Set G)) ≤ G₀ :=
        (pCoreOf_le 2 _).trans inf_le_left
      have hET' : E ≤ Subgroup.normalizer
          (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (T : Set G)) : Set G) := fun e he =>
        normalizer_le_normalizer_pCoreOf 2 _ (mem_normalizer_inf_normalizer (hE he) (hET he))
      obtain ⟨Q, hT'Q, hQ, hEQ⟩ := ih _ hlt hT'G₀ (pCoreOf_isPGroup 2 _) hET'
      exact ⟨Q, hTT'.trans hT'Q, hQ, hEQ⟩

end GGTwoSig

theorem GGRadicalTwo.eq_of_normalizer_le {G : Type*} [Group G] [Finite G] {G₀ Q P : Subgroup G}
    (hQ : GGRadicalTwo G₀ Q) (hPG₀ : P ≤ G₀)
    (hNP : G₀ ⊓ Subgroup.normalizer (Q : Set G) ≤ P) (hQP : Q ≤ pCoreOf 2 P) :
    pCoreOf 2 P = Q ∧ G₀ ⊓ Subgroup.normalizer (Q : Set G) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hPR : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) := le_normalizer_pCoreOf 2 P
  have hNRQ : pCoreOf 2 P ⊓ Subgroup.normalizer (Q : Set G) ≤ Q :=
    calc pCoreOf 2 P ⊓ Subgroup.normalizer (Q : Set G)
        ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (Q : Set G)) :=
          le_pCoreOf_of_le_normalizer 2 (inf_le_inf_right _ ((pCoreOf_le 2 P).trans hPG₀))
            (fun g hg => GGTwoSig.mem_normalizer_inf_normalizer (hPR (hNP hg)) hg.2)
            (hR2.to_le inf_le_left)
      _ = Q := hQ
  have hQR : Q = pCoreOf 2 P := by
    by_contra hne
    have hlt : Q.subgroupOf (pCoreOf 2 P) < ⊤ := by
      refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hQP ?_)
      exact Subgroup.subgroupOf_eq_top.mp htop
    have : Group.IsNilpotent ↥(pCoreOf 2 P) := hR2.isNilpotent
    obtain ⟨r, hrN, hrQ⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    apply hrQ
    rw [Subgroup.mem_subgroupOf]
    refine hNRQ ⟨r.2, Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp hrN ⟨x, hQP hx⟩).mp
        (Subgroup.mem_subgroupOf.mpr hx)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    · have hxR : x ∈ pCoreOf 2 P := by
        have h2 := (pCoreOf 2 P).mul_mem ((pCoreOf 2 P).mul_mem ((pCoreOf 2 P).inv_mem r.2)
          (hQP hx)) r.2
        simpa [mul_assoc] using h2
      have h3 := (Subgroup.mem_normalizer_iff.mp hrN ⟨x, hxR⟩).mpr (by
        rw [Subgroup.mem_subgroupOf]
        simpa using hx)
      rwa [Subgroup.mem_subgroupOf] at h3
  refine ⟨hQR.symm, le_antisymm hNP fun g hg => ⟨hPG₀ hg, ?_⟩⟩
  rw [hQR]
  exact hPR hg

namespace GGTwoSig

variable {G : Type*} [Group G]

@[reducible] def conjAction (A : Subgroup G) (Ω : Set (Subgroup G))
    (hA : ∀ a ∈ A, ∀ V ∈ Ω, V.map (MulAut.conj a).toMonoidHom ∈ Ω) : MulAction A Ω where
  smul a V := ⟨(V : Subgroup G).map (MulAut.conj (a : G)).toMonoidHom, hA a a.2 V V.2⟩
  one_smul V := Subtype.ext (map_conj_one (V : Subgroup G))
  mul_smul a b V := Subtype.ext (map_conj_mul (V : Subgroup G) a b)

theorem exists_fixed_of_card_two_pow [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup G} (hE : IsPGroup p E) {Ω : Set (Subgroup G)}
    (hΩ : ∀ e ∈ E, ∀ V ∈ Ω, V.map (MulAut.conj e).toMonoidHom ∈ Ω) {k : ℕ}
    (hcard : Nat.card Ω = 2 ^ k) : ∃ V ∈ Ω, E ≤ Subgroup.normalizer (V : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  let := conjAction E Ω hΩ
  have hmod := hE.card_modEq_card_fixedPoints (α := Ω)
  by_contra hno
  have hempty : Nat.card (MulAction.fixedPoints E Ω) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨V, hV⟩
    refine hno ⟨V.1, V.2, fun e he => mem_normalizer_of_map_conj_eq ?_⟩
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hV ⟨e, he⟩)
  rw [hempty, hcard] at hmod
  have hdvd : p ∣ 2 ^ k := Nat.modEq_zero_iff_dvd.mp hmod
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem card_eq_two_pow_of_transitive [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    {Ω : Set (Subgroup G)} (hΩ : ∀ u ∈ Q, ∀ V ∈ Ω, V.map (MulAut.conj u).toMonoidHom ∈ Ω)
    {V₀ : Subgroup G} (hV₀ : V₀ ∈ Ω)
    (htr : ∀ V ∈ Ω, ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom) :
    ∃ k : ℕ, Nat.card Ω = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := conjAction Q Ω hΩ
  obtain ⟨k, hk⟩ := hQ.card_orbit (⟨V₀, hV₀⟩ : Ω)
  refine ⟨k, ?_⟩
  have horb : MulAction.orbit Q (⟨V₀, hV₀⟩ : Ω) = Set.univ := by
    refine Set.eq_univ_of_forall fun V => ?_
    obtain ⟨u, hu, hV⟩ := htr V.1 V.2
    exact ⟨⟨u, hu⟩, Subtype.ext hV.symm⟩
  rwa [horb, Nat.card_univ] at hk

theorem sup_map_conj_eq {G₀ Q V : Subgroup G} (hQG₀ : Q ≤ G₀) (hgen : Q ⊔ V = G₀) {u : G}
    (hu : u ∈ Q) : Q ⊔ V.map (MulAut.conj u).toMonoidHom = G₀ :=
  calc Q ⊔ V.map (MulAut.conj u).toMonoidHom
      = Q.map (MulAut.conj u).toMonoidHom ⊔ V.map (MulAut.conj u).toMonoidHom := by
        rw [map_conj_eq (Subgroup.le_normalizer hu)]
    _ = (Q ⊔ V).map (MulAut.conj u).toMonoidHom := (Subgroup.map_sup _ _ _).symm
    _ = G₀ := by rw [hgen, map_conj_eq (Subgroup.le_normalizer (hQG₀ hu))]

theorem forall_map_conj_mem_ggOppositeRadicals {G₀ Q A : Subgroup G}
    (hA₀ : A ≤ Subgroup.normalizer (G₀ : Set G)) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    ∀ a ∈ A, ∀ V ∈ ggOppositeRadicals G₀ Q,
      V.map (MulAut.conj a).toMonoidHom ∈ ggOppositeRadicals G₀ Q := fun _ ha _ hV =>
  mem_ggOppositeRadicals_map_conj hV (hA₀ ha) (hAQ ha)

theorem count_of_conj [Finite G] {G₀ Q V₀ : Subgroup G} (hQ : GGRadicalTwo G₀ Q)
    (hV₀ : V₀ ∈ ggOppositeRadicals G₀ Q) (hgen : Q ⊔ V₀ = G₀)
    (hconj : ∀ V ∈ ggOppositeRadicals G₀ Q, ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom) :
    (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
      ∀ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀ := by
  refine ⟨card_eq_two_pow_of_transitive hQ.isPGroup
    (forall_map_conj_mem_ggOppositeRadicals
      (fun u hu => Subgroup.le_normalizer (hQ.le hu)) Subgroup.le_normalizer) hV₀ hconj,
    fun V hV => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hconj V hV
  exact sup_map_conj_eq hQ.le hgen hu

theorem exists_two_signalizers_of_count [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ E T : Subgroup G} (hEp : IsPGroup p E) (hEG₀ : E ≤ Subgroup.normalizer (G₀ : Set G))
    (hTG₀ : T ≤ G₀) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set G))
    (hcount : ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
        ∀ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀) :
    ∃ Q₁ Q₂ : Subgroup G, Q₁ ≤ G₀ ∧ Q₂ ≤ G₀ ∧ IsPGroup 2 Q₁ ∧ IsPGroup 2 Q₂ ∧
      E ≤ Subgroup.normalizer (Q₁ : Set G) ∧ E ≤ Subgroup.normalizer (Q₂ : Set G) ∧
      Q₁ ⊔ Q₂ = G₀ := by
  obtain ⟨Q, hTQ, hQ, hEQ⟩ := exists_radicalTwo hEG₀ T hTG₀ hT2 hET
  have hQne : Q ≠ ⊥ := fun h => hT (le_bot_iff.mp (h ▸ hTQ))
  obtain ⟨⟨k, hk⟩, hgen⟩ := hcount Q hQne hQ
  obtain ⟨V, hV, hEV⟩ := exists_fixed_of_card_two_pow hp hp2 hEp
    (forall_map_conj_mem_ggOppositeRadicals hEG₀ hEQ) hk
  exact ⟨Q, V, hQ.le, hV.1.le, hQ.isPGroup, hV.1.isPGroup, hEQ, hEV, hgen V hV⟩

theorem exists_two_signalizers [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ E T : Subgroup G} (hEp : IsPGroup p E) (hEG₀ : E ≤ Subgroup.normalizer (G₀ : Set G))
    (hTG₀ : T ≤ G₀) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set G))
    (hex : ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      ∃ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀)
    (hconj : ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      ∀ V ∈ ggOppositeRadicals G₀ Q, ∀ V' ∈ ggOppositeRadicals G₀ Q,
        ∃ u ∈ Q, V' = V.map (MulAut.conj u).toMonoidHom) :
    ∃ Q₁ Q₂ : Subgroup G, Q₁ ≤ G₀ ∧ Q₂ ≤ G₀ ∧ IsPGroup 2 Q₁ ∧ IsPGroup 2 Q₂ ∧
      E ≤ Subgroup.normalizer (Q₁ : Set G) ∧ E ≤ Subgroup.normalizer (Q₂ : Set G) ∧
      Q₁ ⊔ Q₂ = G₀ := by
  refine exists_two_signalizers_of_count hp hp2 hEp hEG₀ hTG₀ hT hT2 hET fun Q hQne hQ => ?_
  obtain ⟨V₀, hV₀, hgen⟩ := hex Q hQne hQ
  exact count_of_conj hQ hV₀ hgen (hconj Q hQne hQ V₀ hV₀)

end GGTwoSig

end CFSG.StandardType
