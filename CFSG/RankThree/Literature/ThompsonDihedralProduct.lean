module

public import CFSG.RankThree.Literature.ThompsonDihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.CharacterTheory.Semidihedral.Principal.ThreeCentralizerSymmetricLocal
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.Literature

open Subgroup CFSG.OddInversion CFSG.RankThree.Literature.Thompson534

variable {G : Type*} [Group G]

@[expose] def thompsonT (T : Subgroup G) {n : ℕ} (A : Fin n → Subgroup G) (i : Fin n) :
    Subgroup G :=
  T ⊓ ⨅ (j : Fin n) (_ : j ≠ i), centralizer (A j : Set G)

@[expose] def thompsonD (T : Subgroup G) {n : ℕ} (A : Fin n → Subgroup G) (i : Fin n) :
    Subgroup G :=
  A i ⊔ thompsonT T A i

theorem mem_thompsonT {T : Subgroup G} {n : ℕ} {A : Fin n → Subgroup G} {i : Fin n} {s : G} :
    s ∈ thompsonT T A i ↔ s ∈ T ∧ ∀ j, j ≠ i → s ∈ centralizer (A j : Set G) := by
  simp only [thompsonT, mem_inf, mem_iInf]

theorem nonempty_closure_mulEquiv_dihedralGroup [Finite G] {ρ σ : G} (hσ : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ zpowers ρ) :
    Nonempty (closure {ρ, σ} ≃* DihedralGroup (orderOf ρ)) := by
  set H := closure ({ρ, σ} : Set G)
  have hρH : ρ ∈ H := subset_closure (by simp)
  have hσH : σ ∈ H := subset_closure (by simp)
  have hgen : (⊤ : Subgroup H) = zpowers ⟨ρ, hρH⟩ ⊔ zpowers ⟨σ, hσH⟩ := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union,
      ← closure_closure_coe_preimage (k := ({ρ, σ} : Set G))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (D := H) ⟨ρ, hρH⟩ ⟨σ, hσH⟩
    hgen (Subtype.ext (by simpa using hσ)) (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ
      (by
        obtain ⟨k, hk⟩ := (mem_zpowers_iff).mp hmem
        exact (mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk] at h

theorem card_iSup_of_iSupIndep {n : ℕ} (H : Fin n → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H) : Nat.card (⨆ i, H i : Subgroup G) = ∏ i, Nat.card (H i) := by
  obtain ⟨e, -⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup H hcomm hind
  rw [← Nat.card_congr e.toEquiv, Nat.card_pi]

theorem thompson_of_dihedralBasis [Finite G] {X T : Subgroup G} {n : ℕ}
    {A : Fin n → Subgroup G} {t : Fin n → G} (hB : DihedralBasis X T A t)
    (hXodd : Odd (Nat.card X)) (hTcomm : ∀ s ∈ T, ∀ u ∈ T, s * u = u * s)
    (hT2 : ∀ s ∈ T, s * s = 1) (hTcard : Nat.card T = 2 ^ n) :
    ((Pairwise fun i j => ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) ∧ iSupIndep A) ∧
      T ⊓ centralizer ((⨆ i, A i : Subgroup G) : Set G) = ⊥ ∧
      (∀ i, Nat.card (thompsonT T A i) = 2 ∧
        (∀ s ∈ thompsonT T A i, s ≠ 1 → ∀ a ∈ A i, s * a * s⁻¹ = a⁻¹) ∧
        Nat.card (thompsonD T A i) = 2 * Nat.card (A i) ∧
        Nonempty (thompsonD T A i ≃* DihedralGroup (Nat.card (A i)))) ∧
      ((Pairwise fun i j => ∀ x ∈ thompsonT T A i, ∀ y ∈ thompsonT T A j, Commute x y) ∧
        iSupIndep (thompsonT T A) ∧ ⨆ i, thompsonT T A i = T) ∧
      ((Pairwise fun i j => ∀ x ∈ thompsonD T A i, ∀ y ∈ thompsonD T A j, Commute x y) ∧
        iSupIndep (thompsonD T A) ∧ ⨆ i, thompsonD T A i = (⨆ i, A i) ⊔ T) := by
  classical
  have hAodd : ∀ i, Odd (Nat.card (A i)) := fun i =>
    Odd.of_dvd_nat hXodd (card_dvd_of_le (hB.le i))
  have hnormbot : T ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hpm : ∀ s ∈ T, ∀ i, (∀ a ∈ A i, s * a * s⁻¹ = a) ∨ (∀ a ∈ A i, s * a * s⁻¹ = a⁻¹) := by
    intro s hs i
    have hbotn : A i ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    rcases conj_mod_trivial_or_inv (hAodd i) bot_le hbotn (hB.le_normalizer i) hnormbot hTcomm
      (fun H _ hH _ => eq_bot_or_eq_of_card_prime (hB.prime i) hH) hs (hT2 s hs) with h | h
    · left
      intro a ha
      exact (inv_mul_eq_one.mp ((mem_bot).mp (h a ha))).symm
    · right
      intro a ha
      exact eq_inv_of_mul_eq_one_right ((mem_bot).mp (h a ha))
  have hgen : ∀ i, ∃ a ∈ A i, a ≠ 1 ∧ zpowers a = A i := by
    intro i
    have hne : A i ≠ ⊥ := fun h => by
      have := hB.prime i
      rw [h, card_bot] at this
      exact Nat.not_prime_one this
    obtain ⟨⟨a, ha⟩, ha1⟩ := ne_bot_iff_exists_ne_one.mp hne
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    refine ⟨a, ha, ha1', ?_⟩
    rcases eq_bot_or_eq_of_card_prime (hB.prime i) (zpowers_le.mpr ha) with h | h
    · exact absurd (zpowers_eq_bot.mp h) ha1'
    · exact h
  have hinvne : ∀ i, ∀ a ∈ A i, a ≠ 1 → a ≠ a⁻¹ := fun i a ha ha1 h =>
    ha1 (eq_one_of_eq_inv (hAodd i) ha h)
  have ht1 : ∀ i, t i ≠ 1 := by
    intro i h
    obtain ⟨a, ha, ha1, -⟩ := hgen i
    apply hinvne i a ha ha1
    have := hB.inv i a ha
    rwa [h, one_mul, inv_one, mul_one] at this
  have hfaith : ∀ s ∈ T, (∀ j, s ∈ centralizer (A j : Set G)) → s = 1 := by
    intro s hs h
    have hle : (⨆ j, A j) ≤ centralizer ({s} : Set G) := iSup_le fun j a ha =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (h j)) a ha)
    have : s ∈ T ⊓ centralizer ((⨆ i, A i : Subgroup G) : Set G) :=
      ⟨hs, mem_centralizer_of_le hle⟩
    rw [hB.faithful] at this
    exact this
  have htT : ∀ i, t i ∈ thompsonT T A i := fun i =>
    mem_thompsonT.mpr ⟨hB.mem i, fun j hj => hB.mem_centralizer i j (Ne.symm hj)⟩
  have hTi : ∀ i, ∀ s ∈ thompsonT T A i, s = 1 ∨ s = t i := by
    intro i s hs
    obtain ⟨hsT, hsc⟩ := mem_thompsonT.mp hs
    rcases hpm s hsT i with h | h
    · left
      refine hfaith s hsT fun j => ?_
      by_cases hj : j = i
      · subst hj
        exact mem_centralizer_of_conj_eq h
      · exact hsc j hj
    · right
      have hst : s * t i = 1 := by
        refine hfaith _ (T.mul_mem hsT (hB.mem i)) fun j => ?_
        by_cases hj : j = i
        · subst hj
          refine mem_centralizer_of_conj_eq fun a ha => ?_
          calc s * t j * a * (s * t j)⁻¹ = s * (t j * a * (t j)⁻¹) * s⁻¹ := by group
            _ = (s * a * s⁻¹)⁻¹ := by rw [hB.inv j a ha]; group
            _ = a := by rw [h a ha, inv_inv]
        · exact (centralizer (A j : Set G)).mul_mem (hsc j hj)
            (hB.mem_centralizer i j (Ne.symm hj))
      have := eq_inv_of_mul_eq_one_left hst
      rwa [inv_eq_of_mul_eq_one_right (hT2 _ (hB.mem i))] at this
  have hTset : ∀ i, (thompsonT T A i : Set G) = {1, t i} := by
    intro i
    ext s
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨hTi i s, ?_⟩
    rintro (rfl | rfl)
    · exact one_mem _
    · exact htT i
  have hTcard2 : ∀ i, Nat.card (thompsonT T A i) = 2 := by
    intro i
    rw [← SetLike.coe_sort_coe, hTset i, Nat.card_coe_set_eq, Set.ncard_pair (ht1 i).symm]
  have hTzp : ∀ i, thompsonT T A i = zpowers (t i) := by
    intro i
    refine le_antisymm (fun s hs => ?_) (zpowers_le.mpr (htT i))
    rcases hTi i s hs with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have hDcl : ∀ i, ∀ a, zpowers a = A i → thompsonD T A i = closure {a, t i} := by
    intro i a ha
    rw [thompsonD, ← ha, hTzp i, zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  have hDdih : ∀ i, Nat.card (thompsonD T A i) = 2 * Nat.card (A i) ∧
      Nonempty (thompsonD T A i ≃* DihedralGroup (Nat.card (A i))) := by
    intro i
    obtain ⟨a, ha, -, hza⟩ := hgen i
    have hord : orderOf a = Nat.card (A i) := by
      rw [← hza, Nat.card_zpowers]
    have htnot : t i ∉ zpowers a := by
      rw [hza]
      exact notMem_of_odd_card (hAodd i) (orderOf_eq_prime (by rw [sq]; exact hT2 _ (hB.mem i))
        (ht1 i))
    obtain ⟨e⟩ := nonempty_closure_mulEquiv_dihedralGroup (by rw [sq]; exact hT2 _ (hB.mem i))
      (hB.inv i a ha) htnot
    rw [hord, ← hDcl i a hza] at e
    exact ⟨by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card], ⟨e⟩⟩
  have hAcomm := hB.comm
  have hAind : iSupIndep A := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_def]
    intro x hx hx'
    have hle : (⨆ (j : Fin n) (_ : j ≠ i), A j) ≤ centralizer ({t i} : Set G) :=
      iSup₂_le fun j hj a ha => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp (hB.mem_centralizer i j (Ne.symm hj))) a ha)
    have h1 : t i * x * (t i)⁻¹ = x := by
      have := mem_centralizer_singleton_iff.mp (hle hx')
      rw [← this]
      group
    exact eq_one_of_eq_inv (hAodd i) hx (h1.symm.trans (hB.inv i x hx))
  have hTle : ∀ i, thompsonT T A i ≤ T := fun i => inf_le_left
  have hTcomm' : Pairwise fun i j => ∀ x ∈ thompsonT T A i, ∀ y ∈ thompsonT T A j,
      Commute x y := fun i j _ x hx y hy => hTcomm x (hTle i hx) y (hTle j hy)
  have hTcentA : ∀ i j, j ≠ i → thompsonT T A j ≤ centralizer (A i : Set G) :=
    fun i j hji s hs => (mem_thompsonT.mp hs).2 i (Ne.symm hji)
  have hTind : iSupIndep (thompsonT T A) := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_def]
    intro x hx hx'
    have hle : (⨆ (j : Fin n) (_ : j ≠ i), thompsonT T A j) ≤ centralizer (A i : Set G) :=
      iSup₂_le fun j hj => hTcentA i j hj
    rcases hTi i x hx with h | h
    · exact h
    · exfalso
      subst h
      obtain ⟨a, ha, ha1, -⟩ := hgen i
      apply hinvne i a ha ha1
      exact (conj_eq_of_mem_centralizer (hle hx') ha).symm.trans (hB.inv i a ha)
  have hTsup : ⨆ i, thompsonT T A i = T := by
    refine Subgroup.eq_of_le_of_card_ge (iSup_le hTle) ?_
    rw [card_iSup_of_iSupIndep _ (fun i j hij x y hx hy => hTcomm' hij x hx y hy) hTind, hTcard]
    simp [hTcard2]
  have hDcentA : ∀ i j, j ≠ i → thompsonD T A j ≤ centralizer (A i : Set G) := by
    intro i j hji
    refine sup_le (fun x hx => ?_) (hTcentA i j hji)
    rw [mem_centralizer_iff]
    intro y hy
    exact (hAcomm hji x hx y hy).eq.symm
  have hDcentt : ∀ i j, j ≠ i → thompsonD T A j ≤ centralizer ({t i} : Set G) := by
    intro i j hji
    refine sup_le (fun a ha => ?_) (fun s hs => ?_)
    · exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp (hB.mem_centralizer i j (Ne.symm hji))) a ha)
    · exact mem_centralizer_singleton_iff.mpr (hTcomm s (hTle j hs) (t i) (hB.mem i))
  have hDcomm : Pairwise fun i j => ∀ x ∈ thompsonD T A i, ∀ y ∈ thompsonD T A j,
      Commute x y := by
    intro i j hij x hx y hy
    have hle : thompsonD T A i ≤ centralizer (thompsonD T A j : Set G) := by
      refine sup_le ?_ ?_
      · rw [le_centralizer_iff]
        exact hDcentA i j (Ne.symm hij)
      · intro s hs
        rw [mem_centralizer_iff]
        intro z hz
        have hz' : z ∈ thompsonD T A j := hz
        refine (sup_le (fun a ha => ?_) (fun u hu => ?_) : thompsonD T A j ≤
          centralizer ({s} : Set G)) hz' |> mem_centralizer_singleton_iff.mp
        · exact mem_centralizer_singleton_iff.mpr
            ((mem_centralizer_iff.mp ((mem_thompsonT.mp hs).2 j (Ne.symm hij))) a ha)
        · exact mem_centralizer_singleton_iff.mpr (hTcomm u (hTle j hu) s (hTle i hs))
    exact ((mem_centralizer_iff.mp (hle hx)) y hy).symm
  have hDind : iSupIndep (thompsonD T A) := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_def]
    intro x hx hx'
    have hleA : (⨆ (j : Fin n) (_ : j ≠ i), thompsonD T A j) ≤ centralizer (A i : Set G) :=
      iSup₂_le fun j hj => hDcentA i j hj
    have hlet : (⨆ (j : Fin n) (_ : j ≠ i), thompsonD T A j) ≤ centralizer ({t i} : Set G) :=
      iSup₂_le fun j hj => hDcentt i j hj
    have hAD : A i ≤ thompsonD T A i := le_sup_left
    have hxA : x ∈ A i := by
      have hCD : A i ≤ thompsonD T A i ⊓ centralizer (A i : Set G) := by
        refine le_inf hAD fun a ha => ?_
        rw [mem_centralizer_iff]
        intro b hb
        obtain ⟨g, -, -, hg⟩ := hgen i
        rw [← hg] at ha hb
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
        obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hb
        exact (Commute.zpow_zpow_self g l k).eq
      have hrel : (A i).relIndex (thompsonD T A i) = 2 := by
        have h := relIndex_mul_card (A i) (thompsonD T A i)
        rw [inf_eq_left.mpr hAD, (hDdih i).1] at h
        have hpos : 0 < Nat.card (A i) := Nat.card_pos
        nlinarith
      have hne : thompsonD T A i ⊓ centralizer (A i : Set G) ≠ thompsonD T A i := by
        intro h
        have htD : t i ∈ thompsonD T A i := mem_sup_right (htT i)
        rw [← h] at htD
        obtain ⟨a, ha, ha1, -⟩ := hgen i
        apply hinvne i a ha ha1
        exact (conj_eq_of_mem_centralizer (mem_inf.mp htD).2 ha).symm.trans (hB.inv i a ha)
      have hmul := relIndex_mul_relIndex (A i) (thompsonD T A i ⊓ centralizer (A i : Set G))
        (thompsonD T A i) hCD inf_le_left
      rw [hrel] at hmul
      have h2 : (thompsonD T A i ⊓ centralizer (A i : Set G)).relIndex (thompsonD T A i) ≠ 1 :=
        fun h => hne (le_antisymm inf_le_left (relIndex_eq_one.mp h))
      have h1 : (A i).relIndex (thompsonD T A i ⊓ centralizer (A i : Set G)) = 1 := by
        rcases Nat.eq_zero_or_pos ((A i).relIndex (thompsonD T A i ⊓ centralizer (A i : Set G)))
          with h0 | h0
        · rw [h0, zero_mul] at hmul
          exact absurd hmul (by norm_num)
        · have : (thompsonD T A i ⊓ centralizer (A i : Set G)).relIndex (thompsonD T A i) ∣ 2 :=
            Dvd.intro_left _ hmul
          rcases (Nat.dvd_prime Nat.prime_two).mp this with h3 | h3
          · exact absurd h3 h2
          · rw [h3] at hmul
            omega
      exact relIndex_eq_one.mp h1 ⟨hx, hleA hx'⟩
    have h1 : t i * x * (t i)⁻¹ = x := by
      have := mem_centralizer_singleton_iff.mp (hlet hx')
      rw [← this]
      group
    exact eq_one_of_eq_inv (hAodd i) hxA (h1.symm.trans (hB.inv i x hxA))
  have hDsup : ⨆ i, thompsonD T A i = (⨆ i, A i) ⊔ T := by
    simp only [thompsonD]
    rw [iSup_sup_eq, hTsup]
  exact ⟨⟨hAcomm, hAind⟩, hB.faithful, fun i => ⟨hTcard2 i, fun s hs hs1 a ha => by
    rcases hTi i s hs with h | h
    · exact absurd h hs1
    · rw [h]
      exact hB.inv i a ha, (hDdih i).1, (hDdih i).2⟩, ⟨hTcomm', hTind, hTsup⟩,
    ⟨hDcomm, hDind, hDsup⟩⟩

theorem thompson_lemma_5_34 [Finite G] (hG : Group.IsSolvable G)
    (hF : Odd (Nat.card (fittingSubgroup G))) (T : Subgroup G) [IsElementaryAbelian 2 T]
    {n : ℕ} (hT : Nat.card T = 2 ^ n) :
    ∃ A : Fin n → Subgroup G,
      (∀ i, A i ≤ fittingSubgroup G ∧ T ≤ normalizer (A i : Set G) ∧ (Nat.card (A i)).Prime) ∧
      ((Pairwise fun i j => ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) ∧ iSupIndep A) ∧
      T ⊓ centralizer ((⨆ i, A i : Subgroup G) : Set G) = ⊥ ∧
      (∀ i, Nat.card (thompsonT T A i) = 2 ∧
        (∀ s ∈ thompsonT T A i, s ≠ 1 → ∀ a ∈ A i, s * a * s⁻¹ = a⁻¹) ∧
        Nat.card (thompsonD T A i) = 2 * Nat.card (A i) ∧
        Nonempty (thompsonD T A i ≃* DihedralGroup (Nat.card (A i)))) ∧
      ((Pairwise fun i j => ∀ x ∈ thompsonT T A i, ∀ y ∈ thompsonT T A j, Commute x y) ∧
        iSupIndep (thompsonT T A) ∧ ⨆ i, thompsonT T A i = T) ∧
      ((Pairwise fun i j => ∀ x ∈ thompsonD T A i, ∀ y ∈ thompsonD T A j, Commute x y) ∧
        iSupIndep (thompsonD T A) ∧ ⨆ i, thompsonD T A i = (⨆ i, A i) ⊔ T) ∧
      ∀ p : ℕ, p.Prime → IsPGroup p (fittingSubgroup G) →
        T ≤ (⨆ i, A i) ⊔ T ∧ (⨆ i, A i) ⊔ T ≤ fittingSubgroup G ⊔ T ∧
        Nonempty (((⨆ i, A i) ⊔ T : Subgroup G) ≃* (Fin n → DihedralGroup p)) ∧
        (p = 3 → Nonempty (((⨆ i, A i) ⊔ T : Subgroup G) ≃* (Fin n → Equiv.Perm (Fin 3)))) := by
  classical
  set F := fittingSubgroup G with hFdef
  have hnil : ∀ H : Subgroup G, H ≤ F → Group.IsNilpotent H := fun H hH =>
    Group.nilpotent_of_mulEquiv (subgroupOfEquivOfLe hH)
  have hTcomm : ∀ s ∈ T, ∀ u ∈ T, s * u = u * s := by
    intro s hs u hu
    have := (inferInstance : IsMulCommutative T).is_comm.comm ⟨s, hs⟩ ⟨u, hu⟩
    exact congrArg Subtype.val this
  have hT2 : ∀ s ∈ T, s * s = 1 := fun s hs => by
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian s hs
  have hTF : T ≤ normalizer (F : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hfaith : T ⊓ centralizer (F : Set G) = ⊥ := by
    have hcop : (Nat.card T).Coprime (Nat.card F) := by
      rw [hT]
      exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hF)
    have hTF0 : T ⊓ F = ⊥ := disjoint_iff.mp (disjoint_of_coprime_natCard hcop)
    rw [eq_bot_iff, ← hTF0]
    exact inf_le_inf_left T (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hG)
  obtain ⟨A, t, hB⟩ := exists_dihedral_basis n hnil hF hTcomm hT2 hT hTF hfaith
  obtain ⟨ha, hb, hc, hd, he⟩ := thompson_of_dihedralBasis hB hF hTcomm hT2 hT
  refine ⟨A, fun i => ⟨hB.le i, hB.le_normalizer i, hB.prime i⟩, ha, hb, hc, hd, he, ?_⟩
  intro p hp hpF
  have : Fact p.Prime := ⟨hp⟩
  have hAp : ∀ i, Nat.card (A i) = p := by
    intro i
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hpF.to_le (hB.le i))
    have hq := hB.prime i
    rw [hk] at hq ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hq
      exact Nat.not_prime_one hq
    have hdvd : p ∣ p ^ k := dvd_pow_self p hk0
    exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd).symm
  obtain ⟨e, -⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup (thompsonD T A)
    (fun i j hij x y hx hy => he.1 hij x hx y hy) he.2.1
  let e' : ((⨆ i, A i) ⊔ T : Subgroup G) ≃* ((i : Fin n) → thompsonD T A i) :=
    (MulEquiv.subgroupCongr he.2.2.symm).trans e.symm
  have hDp : ∀ i, Nonempty (thompsonD T A i ≃* DihedralGroup p) := by
    intro i
    have := (hc i).2.2.2
    rwa [hAp i] at this
  let eD : ∀ i, thompsonD T A i ≃* DihedralGroup p := fun i => (hDp i).some
  let e2 : ((⨆ i, A i) ⊔ T : Subgroup G) ≃* (Fin n → DihedralGroup p) :=
    e'.trans (MulEquiv.piCongrRight eD)
  refine ⟨le_sup_right, sup_le_sup_right (iSup_le fun i => hB.le i) T, ⟨e2⟩, ?_⟩
  rintro rfl
  obtain ⟨s3⟩ := CFSG.Semidihedral.Principal.nonempty_perm_three_mulEquiv_dihedralGroup_three
  exact ⟨e2.trans (MulEquiv.piCongrRight fun _ => s3.symm)⟩

end CFSG.RankThree.Literature
