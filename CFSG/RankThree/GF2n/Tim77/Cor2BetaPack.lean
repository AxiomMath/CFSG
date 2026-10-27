module

public import CFSG.RankThree.GF2n.Tim77.Cor2BetaBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSimpleFactorsAut
public import CFSG.LocalAnalysis.LargeEvenClassification.ProperSections

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem cor2Beta_hasNormalTwoComplement_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : HasNormalTwoComplement X) : HasNormalTwoComplement Y := by
  obtain ⟨O, hO, hodd, hO2, hp⟩ := h
  have hO' : (O.map e.toMonoidHom).Normal := hO.map e.toMonoidHom e.surjective
  refine ⟨O.map e.toMonoidHom, hO', ?_, hO', ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective]
  · exact IsPGroup.of_equiv hp (QuotientGroup.congr O (O.map e.toMonoidHom) e rfl)

theorem cor2Beta_isCoveringOf_of_mulEquiv {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y)
    {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (h : IsCoveringOf P H) :
    IsCoveringOf P H' := by
  obtain ⟨hc, Z, hZ, hZn, hQ⟩ := h
  refine ⟨?_, Z.map e.toMonoidHom, ?_, hZn.map e.toMonoidHom e.surjective, ?_⟩
  · have := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
      at this
    simpa [commutator_def] using this
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    have := Subgroup.mem_center_iff.mp (hZ hz') g'
    simpa using congrArg e this
  · exact hP _ _ (QuotientGroup.congr Z (Z.map e.toMonoidHom) e rfl) hQ

theorem cor2Beta_shape_target {Y : Subgroup G} (h : Cor2BetaShape Y) :
    ∃ (r : ℕ) (X : Fin r → Subgroup ↥Y), (∀ i, (X i).Normal) ∧
      (∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) ∧ ⨆ i, X i = ⊤ ∧
      ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i) := by
  obtain ⟨r, X, hle, hn, hc, hsup, hcov⟩ := h
  refine ⟨r, fun i => (X i).subgroupOf Y, hn, ?_, ?_, ?_⟩
  · intro i j hij x hx y hy
    exact Subtype.ext (hc i j hij x hx y hy)
  · apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    conv_rhs => rw [← hsup]
    refine iSup_congr fun i => ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hle i)]
  · intro i
    have e : ↥(X i) ≃* ↥((X i).subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe (hle i)).symm
    rcases hcov i with h1 | h1
    · exact Or.inl (cor2Beta_isCoveringOf_of_mulEquiv
        (fun X Y _ _ e h => tim77Cor2BetaList_of_mulEquiv e h) e h1)
    · exact Or.inr (cor2Beta_hasNormalTwoComplement_of_mulEquiv e h1)

theorem cor2Beta_shape_of_family {Y : Subgroup G} {ι : Type} [Fintype ι] (X : ι → Subgroup G)
    (hle : ∀ i, X i ≤ Y) (hn : ∀ i, ((X i).subgroupOf Y).Normal)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) (hsup : ⨆ i, X i = Y)
    (hcov : ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i)) :
    Cor2BetaShape Y := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => X (e.symm i), fun i => hle _, fun i => hn _, ?_, ?_,
    fun i => hcov _⟩
  · intro i j hij x hx y hy
    exact hc _ _ (fun h => hij (e.symm.injective h)) x hx y hy
  · rw [← hsup]
    exact e.symm.iSup_comp (g := X)

theorem cor2Beta_le_normalizer_of_commute {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ normalizer (A : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h2 : q * x * q⁻¹ = x := by
      calc q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [← h x hx q hq]
        _ = x := by group
    rwa [h2]
  · intro hx
    have h1 := h _ hx q hq
    have h3 : q * x = q * (q * x * q⁻¹) := by
      calc q * x = (q * x * q⁻¹) * q := by group
        _ = q * (q * x * q⁻¹) := h1
    have h2 : x = q * x * q⁻¹ := mul_left_cancel h3
    rw [h2]
    exact hx

theorem cor2Beta_shape_of_decomp_mul {H E Y Q Gs : Subgroup G} (hd : Cor2BetaDecomp H E Y)
    (hQ : ∀ q ∈ Q, ∀ h ∈ H, q * h = h * q) (hGs : Gs = H ⊔ Q)
    (hQc : HasNormalTwoComplement ↥Q) : Cor2BetaShape Gs := by
  classical
  obtain ⟨r, K, hKE, hKn, hKc, hKsup, hKcov⟩ := hd.E_shape
  have hKH : ∀ i, K i ≤ H := fun i => (hKE i).trans hd.E_le
  have hHnK : ∀ i, H ≤ normalizer (K i : Set G) := fun i =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hKH i)).mp (hKn i)
  have hQnK : ∀ i, Q ≤ normalizer (K i : Set G) := fun i =>
    cor2Beta_le_normalizer_of_commute fun a ha b hb => (hQ b hb a (hKH i ha)).symm
  have hHnQ : H ≤ normalizer (Q : Set G) :=
    cor2Beta_le_normalizer_of_commute fun a ha b hb => hQ a ha b hb
  let X : Fin r ⊕ Bool → Subgroup G := fun i => Sum.elim K (fun b => bif b then Y else Q) i
  have hXle : ∀ i, X i ≤ Gs := by
    rintro (i | b)
    · exact (hKH i).trans (hGs ▸ le_sup_left)
    · cases b
      · exact hGs ▸ le_sup_right
      · exact hd.Y_le.trans (hGs ▸ le_sup_left)
  refine cor2Beta_shape_of_family X hXle ?_ ?_ ?_ ?_
  · rintro (i | b)
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hXle (Sum.inl i))]
      exact hGs ▸ sup_le (hHnK i) (hQnK i)
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hXle (Sum.inr b))]
      cases b
      · exact hGs ▸ sup_le hHnQ (Subgroup.le_normalizer)
      · intro g _
        change g ∈ normalizer (Y : Set G)
        rw [Subgroup.normalizer_eq_top_iff.mpr hd.Y_normal]
        trivial
  · rintro (i | b) (j | b') hij x hx y hy
    · exact hKc i j (fun h => hij (congrArg Sum.inl h)) x hx y hy
    · cases b'
      · exact (hQ y hy x (hKH i hx)).symm
      · exact hd.comm x (hKE i hx) y hy
    · cases b
      · exact hQ x hx y (hKH j hy)
      · exact (hd.comm y (hKE j hy) x hx).symm
    · cases b <;> cases b'
      · exact absurd rfl hij
      · exact hQ x hx y (hd.Y_le hy)
      · exact (hQ y hy x (hd.Y_le hx)).symm
      · exact absurd rfl hij
  · rw [iSup_sum, iSup_bool_eq]
    change (⨆ i, K i) ⊔ (Y ⊔ Q) = Gs
    rw [hKsup, ← sup_assoc, hd.sup_eq, hGs]
  · rintro (i | b)
    · exact Or.inl (hKcov i)
    · cases b
      · exact Or.inr hQc
      · exact Or.inr hd.Y_compl

theorem cor2Beta_hasNormalTwoComplement_of_comm {Q : Subgroup G} [IsMulCommutative ↥Q] :
    HasNormalTwoComplement ↥Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥Q := default
  haveI : (P : Subgroup ↥Q).Normal := inferInstance
  have hcop : Nat.Coprime (Nat.card (P : Subgroup ↥Q)) (P : Subgroup ↥Q).index :=
    P.card_coprime_index
  obtain ⟨O, hO⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  haveI : O.Normal := inferInstance
  have hidx : (P : Subgroup ↥Q).index = Nat.card O := hO.symm.index_eq_card
  have hidx' : O.index = Nat.card (P : Subgroup ↥Q) := hO.index_eq_card
  refine ⟨O, inferInstance, ?_, inferInstance, ?_⟩
  · rw [← hidx]
    exact Nat.not_even_iff_odd.mp (fun h => P.not_dvd_index (even_iff_two_dvd.mp h))
  · obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [← Subgroup.index_eq_card, hidx', hk]

theorem cor2Beta_exists_complement {A : Subgroup G} (hTI : IsTI A) (hroot : IsRootType 2 A)
    {t : G} (ht : t ∈ A) (ht1 : t ≠ 1)
    (hnab : ¬ IsMulCommutative ↥(normalClosure (A : Set G)))
    (hinner : ∀ a ∈ A, ∃ h ∈ normalClosure ({t} : Set G),
      ∃ c ∈ centralizer (normalClosure ({t} : Set G) : Set G), a = h * c) :
    ∃ Q : Subgroup G, normalClosure (A : Set G) = normalClosure ({t} : Set G) ⊔ Q ∧
      (∀ q ∈ Q, ∀ h ∈ normalClosure ({t} : Set G), q * h = h * q) ∧ IsMulCommutative ↥Q := by
  classical
  set H : Subgroup G := normalClosure ({t} : Set G) with hH
  have hHn : H.Normal := inferInstance
  have hCn : ∀ g c : G, c ∈ Subgroup.centralizer (H : Set G) →
      g⁻¹ * c * g ∈ Subgroup.centralizer (H : Set G) := by
    intro g c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g * x * g⁻¹ ∈ H := hHn.conj_mem x hx g
    have := hc _ hx'
    calc x * (g⁻¹ * c * g) = g⁻¹ * ((g * x * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * x * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * c * g) * x := by group
  have hAC : ∀ (g : G), ∀ a ∈ A, ∀ c ∈ Subgroup.centralizer (H : Set G),
      (g * a * g⁻¹) * c = c * (g * a * g⁻¹) := by
    intro g a ha c hc
    have hz : ∀ h ∈ normalClosure ({t} : Set G), (g⁻¹ * c * g) * h = h * (g⁻¹ * c * g) :=
      fun h hh => (Subgroup.mem_centralizer_iff.mp (hCn g c hc)) h hh |>.symm
    have key := cor2Beta_commute_of_centralizes hTI hroot ht ht1 hnab hz a ha
    calc (g * a * g⁻¹) * c = g * (a * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * a) * g⁻¹ := by rw [key]
      _ = c * (g * a * g⁻¹) := by group
  let gens : Set G := {c | c ∈ Subgroup.centralizer (H : Set G) ∧
    ∃ x ∈ Group.conjugatesOfSet (A : Set G), x * c⁻¹ ∈ H}
  have hgenC : ∀ c ∈ gens, ∀ x ∈ Group.conjugatesOfSet (A : Set G), x * c = c * x := by
    intro c hc x hx
    obtain ⟨a₁, ha₁, hcx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hcx
    exact hAC g a₁ ha₁ c hc.1
  refine ⟨Subgroup.closure gens, ?_, ?_, ?_⟩
  · apply le_antisymm
    ·
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      obtain ⟨a₁, ha₁, hcx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, hg⟩ := isConj_iff.mp hcx
      obtain ⟨h, hh, c, hc, hac⟩ := hinner a₁ ha₁
      have hcc : g * c * g⁻¹ ∈ gens := by
        refine ⟨?_, x, hx, ?_⟩
        · have := hCn g⁻¹ c hc
          simpa using this
        · have e : x * (g * c * g⁻¹)⁻¹ = g * h * g⁻¹ := by
            rw [← hg, hac]; group
          rw [e]
          exact hHn.conj_mem h hh g
      have e : x = (g * h * g⁻¹) * (g * c * g⁻¹) := by rw [← hg, hac]; group
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem_sup (hHn.conj_mem h hh g) (Subgroup.subset_closure hcc)
    · refine sup_le ?_ ?_
      · exact Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr ht)
      · refine (Subgroup.closure_le _).mpr ?_
        intro c hc
        obtain ⟨-, x, hx, hxc⟩ := hc
        have hxG : x ∈ normalClosure (A : Set G) := Subgroup.subset_closure hx
        have hhG : x * c⁻¹ ∈ normalClosure (A : Set G) :=
          (Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr ht)) hxc
        have : c = (x * c⁻¹)⁻¹ * x := by group
        rw [SetLike.mem_coe, this]
        exact mul_mem (inv_mem hhG) hxG
  · intro q hq h hh
    have hle : Subgroup.closure gens ≤ Subgroup.centralizer (H : Set G) :=
      (Subgroup.closure_le _).mpr fun c hc => hc.1
    exact (Subgroup.mem_centralizer_iff.mp (hle hq) h hh).symm
  ·
    have hgg : ∀ c ∈ gens, ∀ c' ∈ gens, c * c' = c' * c := by
      intro c hc c' hc'
      obtain ⟨-, x', hx', hh'⟩ := hc'
      have h1 := hgenC c hc x' hx'
      have h2 : c * (x' * c'⁻¹) = (x' * c'⁻¹) * c :=
        (Subgroup.mem_centralizer_iff.mp hc.1 _ hh').symm
      have : c' = (x' * c'⁻¹)⁻¹ * x' := by group
      calc c * c' = c * ((x' * c'⁻¹)⁻¹ * x') := by rw [← this]
        _ = ((x' * c'⁻¹)⁻¹ * x') * c := by
            have h3 : c * (x' * c'⁻¹)⁻¹ = (x' * c'⁻¹)⁻¹ * c := by
              have := (Commute.inv_right (show Commute c (x' * c'⁻¹) from h2)).eq
              exact this
            calc c * ((x' * c'⁻¹)⁻¹ * x') = (c * (x' * c'⁻¹)⁻¹) * x' := by group
              _ = ((x' * c'⁻¹)⁻¹ * c) * x' := by rw [h3]
              _ = (x' * c'⁻¹)⁻¹ * (c * x') := by group
              _ = (x' * c'⁻¹)⁻¹ * (x' * c) := by rw [← h1]
              _ = ((x' * c'⁻¹)⁻¹ * x') * c := by group
        _ = c' * c := by rw [← this]
    have hcomm : ∀ x y : G, x ∈ Subgroup.closure gens → y ∈ Subgroup.closure gens →
        Commute x y := by
      intro x y hx hy
      induction hx, hy using Subgroup.closure_induction₂ with
      | mem x y hx hy => exact hgg x hx y hy
      | one_left x hx => exact Commute.one_left x
      | one_right x hx => exact Commute.one_right x
      | mul_left x y z hx hy hz h1 h2 => exact h1.mul_left h2
      | mul_right y z x hy hz hx h1 h2 => exact h1.mul_right h2
      | inv_left x y hx hy h => exact h.inv_left
      | inv_right x y hx hy h => exact h.inv_right
    exact ⟨⟨fun x y => Subtype.ext (hcomm x y x.2 y.2)⟩⟩

theorem cor2Beta_hasNormalTwoComplement_bot : HasNormalTwoComplement ↥(⊥ : Subgroup G) := by
  refine ⟨⊥, inferInstance, ?_, inferInstance, fun g => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subgroup.card_bot]
  exact odd_one

end CFSG.RankThree.GF2n.Tim77
