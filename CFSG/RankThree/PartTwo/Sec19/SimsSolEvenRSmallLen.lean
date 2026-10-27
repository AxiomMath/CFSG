module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallBase
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallPerm

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.CGT.PushingUpLit.BHS (altOn setStab)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

private theorem lenBarPt_injective (hn : 3 ≤ n) :
    Function.Injective (barPt : Fin n → permBar n) := by
  intro a b hab
  by_contra hne
  obtain ⟨c, hca, hcb⟩ :=
    CFSG.HardMathSupport.RichardWeiss.Proving.exists_ne_pair_heart hn a b
  rcases (mem_zmultiples_allOnes_iff _).1 (QuotientAddGroup.eq.1 hab) with h0 | h1
  · have := congrFun h0 a
    simp [Pi.single_apply, hne] at this
  · have := congrFun h1 c
    simp [Pi.single_apply, hca, hcb, allOnes] at this

private theorem lenBarPt_ne_zero (hn : 3 ≤ n) (a : Fin n) : barPt a ≠ 0 := by
  intro h
  obtain ⟨c, hca, -⟩ := CFSG.HardMathSupport.RichardWeiss.Proving.exists_ne_pair_heart hn a a
  rcases (mem_zmultiples_allOnes_iff _).1 ((QuotientAddGroup.eq_zero_iff _).1 h) with h0 | h1
  · have := congrFun h0 a
    simp at this
  · have := congrFun h1 c
    simp [Pi.single_apply, hca, allOnes] at this

private theorem lenConj_mem_of_threeCycles {B : Finset (Fin n)}
    {N : Subgroup (Perm (Fin n))}
    (h : ∀ c : Perm (Fin n), c.IsThreeCycle → (∀ x, x ∉ B → c x = x) →
      ∀ σ ∈ N, c * σ * c⁻¹ ∈ N) :
    ∀ τ ∈ altOn B, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := by
  have hle : altOn B ≤ Subgroup.normalizer (N : Set (Perm (Fin n))) := by
    rw [altOn, ← closure_three_cycles_eq_alternating, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hc3 : (ofSubtype c).IsThreeCycle := by
      rw [Perm.IsThreeCycle, cycleType_ofSubtype]
      exact hc
    have hfix : ∀ x, x ∉ B → ofSubtype c x = x := fun x hx => ofSubtype_apply_of_not_mem c hx
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro σ
    refine ⟨fun hσ => h _ hc3 hfix σ hσ, fun hσ => ?_⟩
    have := h (ofSubtype c)⁻¹ hc3.inv (fun x hx => (Perm.inv_eq_iff_eq).2 (hfix x hx).symm) _ hσ
    simpa [mul_assoc] using this
  exact fun τ hτ σ hσ => (Subgroup.mem_normalizer_iff.1 (hle hτ) σ).1 hσ

theorem normalizer_le_of_W_le (C : Cfg G M X n) {P : Subgroup G} (hWP : blockU X ≤ P)
    (hPQ : P ≤ CFSG.Open.pCoreOf 2 M) : Subgroup.normalizer (P : Set G) ≤ M := by
  have hXP : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    intro x hx p hp
    have hc : ⁅p, x⁆ ∈ blockU X := C.comm_mem_W ⟨p, Q_le_K C (hPQ hp)⟩ hx
    have : x * p * x⁻¹ = (⁅p, x⁆)⁻¹ * p := by
      rw [commutator_inv' p x]
      exact conj_eq_commutator_mul x p
    rw [this]
    exact P.mul_mem (P.inv_mem (hWP hc)) hp
  have hXN : X ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hXP x hx p hp, fun hp => ?_⟩
    have := hXP x⁻¹ (X.inv_mem hx) _ hp
    simpa [mul_assoc] using this
  have hWne : blockU X ≠ ⊥ := (bot_le.trans_lt C.S.block.1.blockZ_lt_blockU).ne'
  have hPne : P ≠ ⊥ := fun hbot => hWne (le_bot_iff.1 (hbot ▸ hWP))
  exact local_le_of_unique C.S.uniq ⟨P, hPne, isPGroup_of_le (isPGroup_pCoreOf' M) hPQ, rfl⟩ hXN

theorem pCoreOf_centralizer_le_Q (C : Cfg G M X n) (D : C.PiData) (hn : 6 ≤ n)
    (hKQ : C.K ≤ CFSG.Open.pCoreOf 2 M) {e : G} (he : e ∈ CFSG.Open.pCoreOf 2 M) {a : Fin n}
    (hπ : Multiplicative.toAdd (D.π ⟨e, Q_le_K C he⟩) = barPt a) :
    CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({e} : Set G)) ≤ CFSG.Open.pCoreOf 2 M := by
  have hse : ∀ s : ↥M, (s : G) ∈ M ⊓ Subgroup.centralizer ({e} : Set G) →
      (s : G) * e = e * (s : G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2
  have hfixH : ∀ s : ↥M, (s : G) ∈ M ⊓ Subgroup.centralizer ({e} : Set G) → C.θ s a = a := by
    intro s hs
    have h1 := D.equivar s ⟨e, Q_le_K C he⟩ ⟨e, Q_le_K C he⟩
      (by show e = (s : G) * e * (s : G)⁻¹; rw [hse s hs, mul_inv_cancel_right])
    rw [hπ, barAct_barPt] at h1
    exact (lenBarPt_injective (by omega) h1).symm
  let N : Subgroup (Perm (Fin n)) :=
    ((CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({e} : Set G))).comap M.subtype).map C.θ
  have hN2 : IsPGroup 2 N :=
    ((isPGroup_pCoreOf' (M ⊓ Subgroup.centralizer ({e} : Set G))).comap_subtype).map C.θ
  have hNfix : ∀ σ ∈ N, σ a = a := by
    intro σ hσ
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hσ
    exact hfixH s (pCoreOf_le_self _ hs)
  have hnormN : ∀ c : Perm (Fin n), c.IsThreeCycle → c a = a → ∀ σ ∈ N, c * σ * c⁻¹ ∈ N := by
    intro c hc hca σ hσ
    obtain ⟨x, hx3, hxc⟩ := exists_lift_pow_three C hc
    have hfix : barAct (C.α x : Perm (Fin n)) (Multiplicative.toAdd (D.π ⟨e, Q_le_K C he⟩)) =
        Multiplicative.toAdd (D.π ⟨e, Q_le_K C he⟩) := by
      rw [hxc, hπ, barAct_barPt, hca]
    have hxe : (x : G) * e = e * (x : G) := comm_of_pow_three D hx3 hfix
    have hxM : (x : G) ∈ M := C.S.le x.2
    have hxH : (x : G) ∈ M ⊓ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_inf.2 ⟨hxM, Subgroup.mem_centralizer_singleton_iff.2 hxe⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hσ
    refine Subgroup.mem_map.2 ⟨⟨x, hxM⟩ * s * ⟨x, hxM⟩⁻¹, ?_, ?_⟩
    · exact pCoreOf_normalized _ hxH hs
    · rw [map_mul, map_mul, map_inv, C.θ_X x, hxc]
  have hBcard : 5 ≤ (Finset.univ.erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  have hNB : N ≤ setStab (Finset.univ.erase a) := by
    intro σ hσ x
    have hσa := hNfix σ hσ
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact not_congr ⟨fun h => σ.injective (h.trans hσa.symm), fun h => by rw [h, hσa]⟩
  have hfixB := block_fixes hN2 hNB
    (lenConj_mem_of_threeCycles fun c hc hcB σ hσ =>
      hnormN c hc (hcB a (by simp)) σ hσ) (Or.inr (Or.inr hBcard))
  intro p hp
  have hpH : p ∈ M ⊓ Subgroup.centralizer ({e} : Set G) := pCoreOf_le_self _ hp
  have hpM : p ∈ M := hpH.1
  have hθ : C.θ ⟨p, hpM⟩ = 1 := by
    have hmem : C.θ ⟨p, hpM⟩ ∈ N := Subgroup.mem_map_of_mem _ hp
    refine Equiv.ext fun b => ?_
    by_cases hb : b = a
    · rw [hb]
      exact hNfix _ hmem
    · exact hfixB _ hmem b (by simp [hb])
  exact hKQ (C.mem_K.2 ⟨hpM, hθ⟩)

theorem centralizer_le_of_length_one (C : Cfg G M X n) (D : C.PiData) (hn : 6 ≤ n)
    (hKQ : C.K ≤ CFSG.Open.pCoreOf 2 M) {e : G} (he : e ∈ CFSG.Open.pCoreOf 2 M) {a : Fin n}
    (hπ : Multiplicative.toAdd (D.π ⟨e, Q_le_K C he⟩) = barPt a) :
    Subgroup.centralizer ({e} : Set G) ≤ M := by
  have hQ1Q := pCoreOf_centralizer_le_Q C D hn hKQ he hπ
  have hWK : blockU X ≤ Subgroup.centralizer ({e} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (W_comm_Q C hw he)
  have hWQ : blockU X ≤ CFSG.Open.pCoreOf 2 M := C.S.W_le_Q
  have hWQ1 : blockU X ≤ CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({e} : Set G)) :=
    le_pCoreOf_of_normalized (fun w hw => ⟨pCoreOf_le_self M (hWQ hw), hWK hw⟩)
      (fun h hh w hw => C.S.W_normalized hh.1 hw) (isPGroup_of_le (isPGroup_pCoreOf' M) hWQ)
  have hN1 : Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({e} : Set G)) : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_W_le C hWQ1 hQ1Q
  have he1 : e ≠ 1 := by
    intro h
    have h0 : Multiplicative.toAdd (D.π ⟨e, Q_le_K C he⟩) = 0 := by
      have : (⟨e, Q_le_K C he⟩ : ↥C.K) = 1 := Subtype.ext h
      rw [this, map_one, toAdd_one]
    rw [hπ] at h0
    exact lenBarPt_ne_zero (by omega) a h0
  have hB2 : IsPGroup 2 (Subgroup.zpowers e) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 he)
  have hcz : Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) =
      Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcons := centralizer_two_constrained C.S.charTwo
    (Subgroup.zpowers_eq_bot.not.2 he1) hB2
  rw [hcz] at hcons
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  set Kc : Subgroup G := Subgroup.centralizer ({e} : Set G)
  set K1 : Subgroup G := M ⊓ Kc
  set Q1 : Subgroup G := CFSG.Open.pCoreOf 2 K1
  set P : Subgroup G := CFSG.Open.pCoreOf 2 Kc
  have hQ1K1 : Q1 ≤ K1 := pCoreOf_le_self K1
  have hK1Kc : K1 ≤ Kc := inf_le_right
  have hP2 : IsPGroup 2 P := isPGroup_pCoreOf' Kc
  have hQ12 : IsPGroup 2 Q1 := isPGroup_pCoreOf' K1
  have hPnorm : ∀ k ∈ Kc, ∀ p ∈ P, k * p * k⁻¹ ∈ P := fun k hk p hp => pCoreOf_normalized Kc hk hp
  have hQ1norm : ∀ k ∈ K1, ∀ q ∈ Q1, k * q * k⁻¹ ∈ Q1 := fun k hk q hq =>
    pCoreOf_normalized K1 hk hq
  have hQ1NP : Q1 ≤ Subgroup.normalizer (P : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hPnorm q (hK1Kc (hQ1K1 hq)) p hp, fun hp => ?_⟩
    have := hPnorm q⁻¹ (Kc.inv_mem (hK1Kc (hQ1K1 hq))) _ hp
    simpa [mul_assoc] using this
  have hT2 : IsPGroup 2 (P ⊔ Q1 : Subgroup G) := hP2.to_sup_of_normal_left' hQ12 hQ1NP
  have hTKc : P ⊔ Q1 ≤ Kc := sup_le (pCoreOf_le_self Kc) (hQ1K1.trans hK1Kc)
  have hTnorm : ∀ k ∈ K1, ∀ t ∈ P ⊔ Q1, k * t * k⁻¹ ∈ P ⊔ Q1 := by
    intro k hk t ht
    have hle : (P ⊔ Q1).map (MulAut.conj k).toMonoidHom ≤ P ⊔ Q1 := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact hPnorm k (hK1Kc hk) z hz
      · rintro _ ⟨z, hz, rfl⟩
        exact hQ1norm k hk z hz
    exact hle ⟨t, ht, rfl⟩
  have hNQ1 : (P ⊔ Q1) ⊓ Subgroup.normalizer (Q1 : Set G) ≤ Q1 := by
    intro g hg
    have hle : (P ⊔ Q1) ⊓ M ≤ Q1 := by
      refine le_pCoreOf_of_normalized (fun t ht => ⟨ht.2, hTKc ht.1⟩) (fun k hk z hz => ?_)
        (isPGroup_of_le hT2 inf_le_left)
      exact Subgroup.mem_inf.2 ⟨hTnorm k hk z hz.1,
        M.mul_mem (M.mul_mem hk.1 hz.2) (M.inv_mem hk.1)⟩
    exact hle ⟨hg.1, hN1 hg.2⟩
  have hPQ1 : P ≤ Q1 := by
    by_contra hnot
    have hne : Q1 ≠ P ⊔ Q1 := by
      intro heq
      apply hnot
      rw [heq]
      exact le_sup_left
    obtain ⟨t, htT, htQ, htN⟩ := exists_mem_normalizer_of_lt hT2 le_sup_right hne
    exact htQ (hNQ1 ⟨htT, htN⟩)
  have hPQ : P ≤ Q := hPQ1.trans hQ1Q
  have hWP : blockU X ≤ P := fun w hw =>
    hcons ⟨hWK hw, Subgroup.mem_centralizer_iff.2 fun p hp => (W_comm_Q C hw (hPQ hp)).symm⟩
  have hNP : Subgroup.normalizer (P : Set G) ≤ M := normalizer_le_of_W_le C hWP hPQ
  intro g hg
  apply hNP
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => hPnorm g hg p hp, fun hp => ?_⟩
  have := hPnorm g⁻¹ (Kc.inv_mem hg) _ hp
  simpa [mul_assoc] using this

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall
