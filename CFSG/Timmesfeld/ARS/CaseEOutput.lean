module

public import CFSG.Timmesfeld.ARS.CaseEFrameOf
public import CFSG.Timmesfeld.ARS.ConfigA2
public import CFSG.Timmesfeld.ARS.CaseEStar
public import CFSG.Timmesfeld.ARS.CaseEConfig
public import CFSG.Timmesfeld.ARS.Induction

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}

theorem Sec13.hasGenConfig_of_caseENode (hS : Sec13 R A A₀) {r r' : ℕ}
    {adj : Fin r → Fin r → Prop} {adj' : Fin r' → Fin r' → Prop} {P Q : Fin r → Subgroup G}
    (hX : IsConfig R adj P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin r} (hN : CaseENode R A A₀ P Q E F j) (ι : Fin r → Fin r') (n₀ : Fin r')
    (hι : Function.Injective ι) (hn₀ : ∀ k, ι k ≠ n₀) (hcover : ∀ x, x = n₀ ∨ ∃ k, ι k = x)
    (hadj : ∀ a b, adj' (ι a) (ι b) → adj a b ∨ adj b a)
    (hadj' : ∀ a b, adj a b → adj' (ι a) (ι b) ∨ adj' (ι b) (ι a))
    (hnew : ∀ k, adj' n₀ (ι k) ∨ adj' (ι k) n₀ → k = j) (hnewj : adj' n₀ (ι j) ∨ adj' (ι j) n₀)
    (hnn : ¬ adj' n₀ n₀) : HasGenConfig R adj' := by
  classical
  let A' : Fin r' → Subgroup G := fun x => if h : ∃ k, ι k = x then P h.choose else E
  let B' : Fin r' → Subgroup G := fun x => if h : ∃ k, ι k = x then Q h.choose else F
  have hA'ι : ∀ k, A' (ι k) = P k := fun k => by
    have h : ∃ k', ι k' = ι k := ⟨k, rfl⟩
    show (if h : ∃ k', ι k' = ι k then P h.choose else E) = P k
    rw [dite_eq_left h, hι h.choose_spec]
  have hB'ι : ∀ k, B' (ι k) = Q k := fun k => by
    have h : ∃ k', ι k' = ι k := ⟨k, rfl⟩
    show (if h : ∃ k', ι k' = ι k then Q h.choose else F) = Q k
    rw [dite_eq_left h, hι h.choose_spec]
  have hn : ¬ ∃ k, ι k = n₀ := fun ⟨k, hk⟩ => hn₀ k hk
  have hA'n : A' n₀ = E := by
    show (if h : ∃ k, ι k = n₀ then P h.choose else E) = E
    rw [dite_eq_right hn]
  have hB'n : B' n₀ = F := by
    show (if h : ∃ k, ι k = n₀ then Q h.choose else F) = F
    rw [dite_eq_right hn]
  exact ⟨A', B', hX.extend hN.memE.1.1.1 hN.memF.1.1.1 hN.opp hN.comm hN.edge ι n₀ hn₀ hcover
    hadj hadj' hnew hnewj hnn hA'ι hB'ι hA'n hB'n,
    iSup_eq_top_of_extend hS hgen hN ι n₀ hA'ι hB'ι hA'n hB'n⟩

theorem Sec13.hasGenConfig_A_succ (hS : Sec13 R A A₀) {m : ℕ} {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeA m) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin m} (hN : CaseENode R A A₀ P Q E F j) (hj : j.val = 0) :
    HasGenConfig R (edgeA (m + 1)) := by
  refine hS.hasGenConfig_of_caseENode hX hgen hN Fin.succ 0 (Fin.succ_injective _)
    (fun k => Fin.succ_ne_zero k) (fun x => ?_) (fun a b h => ?_) (fun a b h => ?_)
    (fun k h => ?_) ?_ ?_
  · rcases Fin.eq_zero_or_eq_succ x with h | ⟨k, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, rfl⟩
  · left
    simp only [edgeA, Fin.val_succ] at h ⊢
    omega
  · left
    simp only [edgeA, Fin.val_succ] at h ⊢
    omega
  · simp only [edgeA, Fin.val_succ, Fin.val_zero] at h
    exact Fin.ext (by omega)
  · left
    simp only [edgeA, Fin.val_succ, Fin.val_zero]
    omega
  · simp [edgeA]

theorem Sec13.hasGenConfig_A_castSucc (hS : Sec13 R A A₀) {m : ℕ} {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeA m) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin m} (hN : CaseENode R A A₀ P Q E F j) (hj : j.val + 1 = m) :
    HasGenConfig R (edgeA (m + 1)) := by
  refine hS.hasGenConfig_of_caseENode hX hgen hN Fin.castSucc (Fin.last m)
    (Fin.castSucc_injective _) (fun k => (Fin.castSucc_lt_last k).ne) (fun x => ?_)
    (fun a b h => ?_) (fun a b h => ?_) (fun k h => ?_) ?_ ?_
  · rcases Fin.eq_castSucc_or_eq_last x with ⟨k, rfl⟩ | h
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl h
  · left
    simpa [edgeA] using h
  · left
    simpa [edgeA] using h
  · simp only [edgeA, Fin.val_castSucc, Fin.val_last] at h
    exact Fin.ext (by omega)
  · right
    simp only [edgeA, Fin.val_castSucc, Fin.val_last]
    omega
  · simp [edgeA]

theorem Sec13.hasGenConfig_D_of_A_castSucc (hS : Sec13 R A A₀) {m : ℕ}
    {P Q : Fin m → Subgroup G} (hX : IsConfig R (edgeA m) P Q)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G} {j : Fin m}
    (hN : CaseENode R A A₀ P Q E F j) (hj : j.val + 2 = m) :
    HasGenConfig R (edgeD (m + 1)) := by
  refine hS.hasGenConfig_of_caseENode hX hgen hN Fin.castSucc (Fin.last m)
    (Fin.castSucc_injective _) (fun k => (Fin.castSucc_lt_last k).ne) (fun x => ?_)
    (fun a b h => ?_) (fun a b h => ?_) (fun k h => ?_) ?_ ?_
  · rcases Fin.eq_castSucc_or_eq_last x with ⟨k, rfl⟩ | h
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl h
  · have ha := a.2
    have hb := b.2
    left
    simp only [edgeD, edgeA, Fin.val_castSucc] at h ⊢
    omega
  · have hb := b.2
    left
    simp only [edgeD, edgeA, Fin.val_castSucc] at h ⊢
    omega
  · have hk := k.2
    simp only [edgeD, Fin.val_castSucc, Fin.val_last] at h
    exact Fin.ext (by omega)
  · right
    simp only [edgeD, Fin.val_castSucc, Fin.val_last, and_true]
    omega
  · simp only [edgeD, Fin.val_last]
    omega

theorem Sec13.hasGenConfig_D_of_A_rev (hS : Sec13 R A A₀) {m : ℕ}
    {P Q : Fin m → Subgroup G} (hX : IsConfig R (edgeA m) P Q)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G} {j : Fin m}
    (hN : CaseENode R A A₀ P Q E F j) (hm : 3 ≤ m) (hj : j.val = 1) :
    HasGenConfig R (edgeD (m + 1)) := by
  refine hS.hasGenConfig_of_caseENode hX hgen hN (fun k => (Fin.rev k).castSucc) (Fin.last m)
    ((Fin.castSucc_injective _).comp Fin.rev_injective)
    (fun k => (Fin.castSucc_lt_last _).ne) (fun x => ?_) (fun a b h => ?_) (fun a b h => ?_)
    (fun k h => ?_) ?_ ?_
  · rcases Fin.eq_castSucc_or_eq_last x with ⟨k, rfl⟩ | h
    · exact Or.inr ⟨Fin.rev k, by simp⟩
    · exact Or.inl h
  · have ha := a.2
    have hb := b.2
    right
    simp only [edgeD, edgeA, Fin.val_castSucc, Fin.val_rev] at h ⊢
    omega
  · have ha := a.2
    have hb := b.2
    right
    simp only [edgeD, edgeA, Fin.val_castSucc, Fin.val_rev] at h ⊢
    omega
  · have hk := k.2
    simp only [edgeD, Fin.val_castSucc, Fin.val_last, Fin.val_rev] at h
    exact Fin.ext (by omega)
  · right
    simp only [edgeD, Fin.val_castSucc, Fin.val_last, Fin.val_rev, and_true]
    omega
  · simp only [edgeD, Fin.val_last]
    omega

theorem Sec13.hasGenConfig_D_succ (hS : Sec13 R A A₀) {m : ℕ} {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeD m) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin m} (hN : CaseENode R A A₀ P Q E F j) (hm : 4 ≤ m) (hj : j.val = 0) :
    HasGenConfig R (edgeD (m + 1)) := by
  refine hS.hasGenConfig_of_caseENode hX hgen hN Fin.succ 0 (Fin.succ_injective _)
    (fun k => Fin.succ_ne_zero k) (fun x => ?_) (fun a b h => ?_) (fun a b h => ?_)
    (fun k h => ?_) ?_ ?_
  · rcases Fin.eq_zero_or_eq_succ x with h | ⟨k, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, rfl⟩
  · left
    simp only [edgeD, Fin.val_succ] at h ⊢
    omega
  · left
    simp only [edgeD, Fin.val_succ] at h ⊢
    omega
  · simp only [edgeD, Fin.val_succ, Fin.val_zero] at h
    exact Fin.ext (by omega)
  · left
    simp only [edgeD, Fin.val_succ, Fin.val_zero]
    omega
  · simp only [edgeD, Fin.val_zero]
    omega

theorem Sec13.exists_caseENode_of_surjective' (hS : Sec13 R A A₀) {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {adj : Fin D.rank → Fin D.rank → Prop}
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {θ : Fin D.rank → ℤ}
    (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i) {P Q : Fin D.rank → Subgroup G}
    (hX : IsConfig R adj P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (Ψ₀ : K →* ↥(levi R A A₀))
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ₀ = (P k).subgroupOf (levi R A A₀))
    (hQ : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ₀ = (Q k).subgroupOf (levi R A A₀))
    (hsurj : Function.Surjective Ψ₀) :
    ∃ j, θ j = 1 ∧ ¬ StarAt D.cartan D.isFiniteType j ∧
      ∃ E F, CaseENode R A A₀ P Q E F j := by
  obtain ⟨hF, hP', hQ'⟩ := leviFrame_of_surjective hS.hyp.root hct hext hdiv hX hPQ Ψ₀ hP hQ hsurj
  have eP : (fun k => (D.rootGroup (Pi.single k 1)).map ((levi R A A₀).subtype.comp Ψ₀)) = P :=
    funext hP'
  have eQ : (fun k => (D.rootGroup (-Pi.single k 1)).map ((levi R A A₀).subtype.comp Ψ₀)) = Q :=
    funext hQ'
  have hX' := hX
  rw [← eP, ← eQ] at hX'
  obtain ⟨E, hE, hEU⟩ := hS.exists_mem_lambdaStar_commuting_negUnipotent hF.hext hF.hdiv _ hF.mem
  obtain ⟨j, hθj, hj⟩ := exists_eq_of_highest hS.hyp hS.mem hS.sec8.2 hS.max hS.opp
    hF.toCompFrame hpd hE hEU hX' hadj hθ hθ1 hF.surj
  obtain ⟨F, hN⟩ := exists_caseENode hS.hyp hS.mem hS.sec8.2 hS.max hS.opp hF hpd hX' hadj hE hEU
    hj
  rw [eP, eQ] at hN
  exact ⟨j, hθj, fun hstar => false_of_levelInv hS hF hpd hX' hadj hE hEU hj hstar, E, F, hN⟩

theorem Sec13.exists_caseENode_A (hS : Sec13 R A A₀) {m : ℕ} (hm : 2 ≤ m)
    {P Q : Fin m → Subgroup G} (hX : IsConfig R (edgeA m) P Q)
    (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) :
    ∃ j : Fin m, (j.val ≤ 1 ∨ m ≤ j.val + 2 ∨ (j.val = 2 ∧ m ≤ 7) ∨
      (m = j.val + 3 ∧ j.val ≤ 4)) ∧ ∃ E F, CaseENode R A A₀ P Q E F j := by
  have := hS.hyp.finite
  have hX' := Sec13.isConfig_restrict hX hPQ
  have hgen' := Sec13.iSup_subgroupOf_eq_top hgen
  have key : ∀ (f : ℕ)
      (Ψ₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* ↥(levi R A A₀)),
      (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (sroot k)).map Ψ₀ =
        (P k).subgroupOf (levi R A A₀)) →
      (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ₀ =
        (Q k).subgroupOf (levi R A A₀)) → Function.Surjective Ψ₀ →
      ∃ j : Fin m, (j.val ≤ 1 ∨ m ≤ j.val + 2 ∨ (j.val = 2 ∧ m ≤ 7) ∨
        (m = j.val + 3 ∧ j.val ≤ 4)) ∧ ∃ E F, CaseENode R A A₀ P Q E F j :=
      fun f Ψ₀ hP hQ hsurj => by
    obtain ⟨j, -, hns, E, F, hN⟩ := hS.exists_caseENode_of_surjective'
      (D := SpecialLinear.rootDatum m (GaloisField 2 f))
      (SpecialLinear.isCTGroupDatum m (GaloisField 2 f))
      (SpecialLinear.steinbergExtras m (GaloisField 2 f)) rfl
      (TauCeti.posDef_map_intCast_cartanMatrix_A m) CaseE.adj_A
      (CaseE.highest_mem_A (by omega) (GaloisField 2 f)) (fun _ => le_rfl) hX hPQ Ψ₀ hP hQ hsurj
    refine ⟨j, ?_, E, F, hN⟩
    by_contra hsph
    exact hns (CaseE.starAt_A m (j := j) (by omega) (by omega) (by omega))
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    obtain ⟨f, -, -, Ψ₀, hP, hQ, hsurj⟩ :=
      hX'.exists_surjective_A_two hS.isRootClass_restrict hS.noIsolated_restrict hgen'
    exact key f Ψ₀ hP hQ hsurj
  · obtain ⟨f, -, -, Ψ₀, hP, hQ, hsurj, -⟩ :=
      hX'.exists_surjective_A hS.isRootClass_restrict hS.noIsolated_restrict hm3 hgen'
    exact key f Ψ₀ hP hQ hsurj

theorem Sec13.exists_caseENode_D (hS : Sec13 R A A₀) {m : ℕ} (hm : 4 ≤ m)
    {P Q : Fin m → Subgroup G} (hX : IsConfig R (edgeD m) P Q)
    (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) :
    ∃ j : Fin m, (j.val = 0 ∨ ((j.val + 2 = m ∨ j.val + 1 = m) ∧ m ≤ 6)) ∧
      ∃ E F, CaseENode R A A₀ P Q E F j := by
  have := hS.hyp.finite
  obtain ⟨f, -, -, Ψ₀, hP, hQ, hsurj, -⟩ := (Sec13.isConfig_restrict hX hPQ).exists_surjective_D
    hS.isRootClass_restrict hS.noIsolated_restrict hm (Sec13.iSup_subgroupOf_eq_top hgen)
  obtain ⟨j, hj, hns, E, F, hN⟩ := hS.exists_caseENode_of_surjective'
    (D := Spin.plusDatum m (GaloisField 2 f) (by omega))
    (Spin.plusDatum_isCTGroupDatum (n := m) (by omega)
      (Spin.plusDatum_iSup_eq_top m _ (by omega)))
    (Spin.plusDatum_steinbergExtras (n := m) (by omega)) rfl (CaseE.posDef_D m) CaseE.adj_D
    (CaseE.highestD_mem (n := m) hm (GaloisField 2 f) (by omega)) CaseE.one_le_highestD hX hPQ
    Ψ₀ hP hQ hsurj
  refine ⟨j, ?_, E, F, hN⟩
  have hj' : j.val = 0 ∨ j.val + 2 = m ∨ j.val + 1 = m := by
    unfold CaseE.highestD at hj
    split_ifs at hj with h
    · exact h
    · omega
  rcases hj' with h0 | hspin
  · exact Or.inl h0
  · refine Or.inr ⟨hspin, ?_⟩
    by_contra h7
    exact hns (CaseE.starAt_D (by omega) hspin)

theorem Sec13.exists_caseENode_E6 (hS : Sec13 R A A₀) {P Q : Fin 6 → Subgroup G}
    (hX : IsConfig R (edgeE 6) P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) :
    ∃ j : Fin 6, (j.val = 0 ∨ j.val = 5) ∧ ∃ E F, CaseENode R A A₀ P Q E F j := by
  have := hS.hyp.finite
  obtain ⟨f, -, -, Ψ₀, hP, hQ, hsurj, -⟩ := (Sec13.isConfig_restrict hX hPQ).exists_surjective_E6
    hS.isRootClass_restrict hS.noIsolated_restrict (Sec13.iSup_subgroupOf_eq_top hgen)
  obtain ⟨j, hj, E, F, hN⟩ := hS.exists_caseENode_of_surjective
    (D := Minuscule.e6Datum (GaloisField 2 f))
    (Minuscule.e6Datum_isCTGroupDatum _) (Minuscule.e6Datum_steinbergExtras _) rfl
    Minuscule.posDef_cartan_E6 CaseE.adj_E6 (CaseE.highest_mem_E6 (GaloisField 2 f))
    CaseE.one_le_highest_E6 hX hPQ Ψ₀ hP hQ hsurj
  exact ⟨j, CaseE.eq_of_highest_E6 j hj, E, F, hN⟩

theorem Sec13.exists_caseENode_E7 (hS : Sec13 R A A₀) {P Q : Fin 7 → Subgroup G}
    (hX : IsConfig R (edgeE 7) P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) : ∃ E F, CaseENode R A A₀ P Q E F 6 := by
  have := hS.hyp.finite
  obtain ⟨f, -, -, Ψ₀, hP, hQ, hsurj, -⟩ := (Sec13.isConfig_restrict hX hPQ).exists_surjective_E7
    hS.isRootClass_restrict hS.noIsolated_restrict (Sec13.iSup_subgroupOf_eq_top hgen)
  obtain ⟨j, hj, E, F, hN⟩ := hS.exists_caseENode_of_surjective
    (D := Minuscule.e7Datum (GaloisField 2 f))
    (Minuscule.e7Datum_isCTGroupDatum _) (Minuscule.e7Datum_steinbergExtras _) rfl
    Minuscule.posDef_cartan_E7 CaseE.adj_E7 (CaseE.highest_mem_E7 (GaloisField 2 f))
    CaseE.one_le_highest_E7 hX hPQ Ψ₀ hP hQ hsurj
  obtain rfl : j = ⟨6, show 6 < 7 by decide⟩ := Fin.ext (CaseE.eq_of_highest_E7 j hj)
  exact ⟨E, F, hN⟩

theorem Sec13.not_isConfig_E8 (hS : Sec13 R A A₀) {P Q : Fin 8 → Subgroup G}
    (hX : IsConfig R (edgeE 8) P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) : False := by
  have := hS.hyp.finite
  obtain ⟨f, -, -, Ψ₀, hP, hQ, hsurj, -⟩ := (Sec13.isConfig_restrict hX hPQ).exists_surjective_E8
    hS.isRootClass_restrict hS.noIsolated_restrict (Sec13.iSup_subgroupOf_eq_top hgen)
  obtain ⟨j, hj, -⟩ := hS.exists_caseENode_of_surjective
    (D := Adjoint.e8Datum (GaloisField 2 f))
    (Adjoint.e8_isCTGroupDatum _) (Adjoint.e8_steinbergExtras _) rfl
    CaseE.posDef_E8 CaseE.adj_E8 (CaseE.highest_mem_E8 (GaloisField 2 f))
    CaseE.one_le_highest_E8 hX hPQ Ψ₀ hP hQ hsurj
  exact CaseE.ne_one_highest_E8 j hj

theorem Sec13.hasGenConfig_E_of_A (hS : Sec13 R A A₀) {m : ℕ} {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeA m) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin m} (hN : CaseENode R A A₀ P Q E F j)
    (hj : (m = 5 ∧ j.val = 2) ∨ (m = 6 ∧ j.val = 2) ∨ (m = 6 ∧ j.val = 3) ∨
      (m = 7 ∧ j.val = 2) ∨ (m = 7 ∧ j.val = 4)) :
    HasGenConfig R (edgeE 6) ∨ HasGenConfig R (edgeE 7) ∨ HasGenConfig R (edgeE 8) := by
  rcases hj with ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩
  · obtain rfl : j = 2 := Fin.ext hj
    exact Or.inl (hS.hasGenConfig_of_caseENode hX hgen hN ![0, 2, 3, 4, 5] 1 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · obtain rfl : j = 2 := Fin.ext hj
    exact Or.inr (Or.inl (hS.hasGenConfig_of_caseENode hX hgen hN ![0, 2, 3, 4, 5, 6] 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)))
  · obtain rfl : j = 3 := Fin.ext hj
    exact Or.inr (Or.inl (hS.hasGenConfig_of_caseENode hX hgen hN ![6, 5, 4, 3, 2, 0] 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)))
  · obtain rfl : j = 2 := Fin.ext hj
    exact Or.inr (Or.inr (hS.hasGenConfig_of_caseENode hX hgen hN ![0, 2, 3, 4, 5, 6, 7] 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)))
  · obtain rfl : j = 4 := Fin.ext hj
    exact Or.inr (Or.inr (hS.hasGenConfig_of_caseENode hX hgen hN ![7, 6, 5, 4, 3, 2, 0] 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)))

theorem Sec13.hasGenConfig_D5_of_D4 (hS : Sec13 R A A₀) {P Q : Fin 4 → Subgroup G}
    (hX : IsConfig R (edgeD 4) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin 4} (hN : CaseENode R A A₀ P Q E F j) (hj : j.val = 2 ∨ j.val = 3) :
    HasGenConfig R (edgeD 5) := by
  rcases hj with hj | hj
  · obtain rfl : j = 2 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![3, 2, 1, 4] 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain rfl : j = 3 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![3, 2, 4, 1] 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem Sec13.hasGenConfig_E6_of_D5 (hS : Sec13 R A A₀) {P Q : Fin 5 → Subgroup G}
    (hX : IsConfig R (edgeD 5) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin 5} (hN : CaseENode R A A₀ P Q E F j) (hj : j.val = 3 ∨ j.val = 4) :
    HasGenConfig R (edgeE 6) := by
  rcases hj with hj | hj
  · obtain rfl : j = 3 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![0, 2, 3, 4, 1] 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain rfl : j = 4 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![0, 2, 3, 1, 4] 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem Sec13.hasGenConfig_E7_of_D6 (hS : Sec13 R A A₀) {P Q : Fin 6 → Subgroup G}
    (hX : IsConfig R (edgeD 6) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin 6} (hN : CaseENode R A A₀ P Q E F j) (hj : j.val = 4 ∨ j.val = 5) :
    HasGenConfig R (edgeE 7) := by
  rcases hj with hj | hj
  · obtain rfl : j = 4 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![6, 5, 4, 3, 2, 1] 0 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain rfl : j = 5 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![6, 5, 4, 3, 1, 2] 0 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem Sec13.hasGenConfig_E7_of_E6 (hS : Sec13 R A A₀) {P Q : Fin 6 → Subgroup G}
    (hX : IsConfig R (edgeE 6) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    {j : Fin 6} (hN : CaseENode R A A₀ P Q E F j) (hj : j.val = 0 ∨ j.val = 5) :
    HasGenConfig R (edgeE 7) := by
  rcases hj with hj | hj
  · obtain rfl : j = 0 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![5, 1, 4, 3, 2, 0] 6 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain rfl : j = 5 := Fin.ext hj
    exact hS.hasGenConfig_of_caseENode hX hgen hN ![0, 1, 2, 3, 4, 5] 6 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem Sec13.hasGenConfig_E8_of_E7 (hS : Sec13 R A A₀) {P Q : Fin 7 → Subgroup G}
    (hX : IsConfig R (edgeE 7) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G}
    (hN : CaseENode R A A₀ P Q E F 6) : HasGenConfig R (edgeE 8) :=
  hS.hasGenConfig_of_caseENode hX hgen hN ![0, 1, 2, 3, 4, 5, 6] 7 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem Sec13.output_A (hS : Sec13 R A A₀) {m : ℕ} (hm : 2 ≤ m)
    {P Q : Fin m → Subgroup G} (hX : IsConfig R (edgeA m) P Q)
    (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) : Output G R := by
  obtain ⟨j, hs, E, F, hN⟩ := hS.exists_caseENode_A hm hX hPQ hgen
  have hjm := j.2
  by_cases h0 : j.val = 0
  · exact Or.inl ⟨m + 1, by omega, hS.hasGenConfig_A_succ hX hgen hN h0⟩
  by_cases h1 : j.val + 1 = m
  · exact Or.inl ⟨m + 1, by omega, hS.hasGenConfig_A_castSucc hX hgen hN h1⟩
  by_cases h2 : j.val + 2 = m
  · exact .inr (.inl ⟨m + 1, by omega, hS.hasGenConfig_D_of_A_castSucc hX hgen hN h2⟩)
  by_cases h3 : j.val = 1
  · exact .inr (.inl ⟨m + 1, by omega, hS.hasGenConfig_D_of_A_rev hX hgen hN (by omega) h3⟩)
  rcases hS.hasGenConfig_E_of_A hX hgen hN (by omega) with h | h | h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))

theorem Sec13.output_D (hS : Sec13 R A A₀) {m : ℕ} (hm : 4 ≤ m)
    {P Q : Fin m → Subgroup G} (hX : IsConfig R (edgeD m) P Q)
    (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) : Output G R := by
  obtain ⟨j, hj, E, F, hN⟩ := hS.exists_caseENode_D hm hX hPQ hgen
  rcases hj with h0 | ⟨hspin, h6⟩
  · exact .inr (.inl ⟨m + 1, by omega, hS.hasGenConfig_D_succ hX hgen hN hm h0⟩)
  have hm' : m = 4 ∨ m = 5 ∨ m = 6 := by omega
  rcases hm' with rfl | rfl | rfl
  · exact .inr (.inl ⟨5, by omega, hS.hasGenConfig_D5_of_D4 hX hgen hN (by omega)⟩)
  · exact .inr (.inr (.inl (hS.hasGenConfig_E6_of_D5 hX hgen hN (by omega))))
  · exact .inr (.inr (.inr (.inl (hS.hasGenConfig_E7_of_D6 hX hgen hN (by omega)))))

theorem Sec13.output_E6 (hS : Sec13 R A A₀) {P Q : Fin 6 → Subgroup G}
    (hX : IsConfig R (edgeE 6) P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) : Output G R := by
  obtain ⟨j, hj, E, F, hN⟩ := hS.exists_caseENode_E6 hX hPQ hgen
  exact .inr (.inr (.inr (.inl (hS.hasGenConfig_E7_of_E6 hX hgen hN hj))))

theorem Sec13.output_E7 (hS : Sec13 R A A₀) {P Q : Fin 7 → Subgroup G}
    (hX : IsConfig R (edgeE 7) P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) : Output G R := by
  obtain ⟨E, F, hN⟩ := hS.exists_caseENode_E7 hX hPQ hgen
  exact .inr (.inr (.inr (.inr (.inl (hS.hasGenConfig_E8_of_E7 hX hgen hN)))))

end CFSG.Timmesfeld.ARS
