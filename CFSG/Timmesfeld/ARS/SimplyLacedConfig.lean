module

public import CFSG.Timmesfeld.RankTwo.LevisSpin
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import CFSG.LieType.CurtisTits.Exceptional
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.ARS.LinearChain
public import CFSG.Timmesfeld.RankTwo.LeviData

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace SimplyLaced

theorem exists_tree {T : Type*} {r : ℕ} (N : Fin r → T → Prop) (E : Fin r → T → T → Prop)
    (par : Fin r → Fin r) (dep : Fin r → ℕ) (k₀ : Fin r)
    (hlt : ∀ k, k ≠ k₀ → dep (par k) < dep k)
    (hf : ∀ k, k ≠ k₀ → ∀ t, N (par k) t → ∃ t', N k t' ∧ E k t t')
    {t₀ : T} (h₀ : N k₀ t₀) :
    ∃ ρ : Fin r → T, ρ k₀ = t₀ ∧ (∀ k, N k (ρ k)) ∧ ∀ k, k ≠ k₀ → E k (ρ (par k)) (ρ k) := by
  classical
  choose g hg using hf
  have key : ∀ d : ℕ, ∃ ρ : Fin r → T, ρ k₀ = t₀ ∧ ∀ k, (k = k₀ ∨ dep k < d) →
      N k (ρ k) ∧ (k ≠ k₀ → E k (ρ (par k)) (ρ k)) := by
    intro d
    induction d with
    | zero =>
      refine ⟨fun _ => t₀, rfl, fun k hk => ?_⟩
      rcases hk with rfl | hk
      · exact ⟨h₀, fun h => absurd rfl h⟩
      · exact absurd hk (Nat.not_lt_zero _)
    | succ d ih =>
      obtain ⟨ρ, hρ0, hρ⟩ := ih
      have hpar : ∀ k, k ≠ k₀ → dep k = d → N (par k) (ρ (par k)) := by
        intro k hk hd
        by_cases hp : par k = k₀
        · exact (hρ _ (Or.inl hp)).1
        · exact (hρ _ (Or.inr (hd ▸ hlt k hk))).1
      let ρ' : Fin r → T := fun k =>
        if h : k ≠ k₀ ∧ dep k = d then g k h.1 (ρ (par k)) (hpar k h.1 h.2) else ρ k
      have hold : ∀ k, ¬ (k ≠ k₀ ∧ dep k = d) → ρ' k = ρ k := fun k h =>
        dite_eq_right_of_eq_false (eq_false h)
      have hnew : ∀ k (h : k ≠ k₀ ∧ dep k = d),
          ρ' k = g k h.1 (ρ (par k)) (hpar k h.1 h.2) := fun k h => dite_eq_left_of_eq_true (eq_true h)
      have hpold : ∀ k, k ≠ k₀ → dep k ≤ d → ρ' (par k) = ρ (par k) := by
        intro k hk0 hkd
        apply hold
        rintro ⟨-, hpd⟩
        have := hlt k hk0
        omega
      refine ⟨ρ', by rw [hold k₀ (fun h => h.1 rfl)]; exact hρ0, fun k hk => ?_⟩
      by_cases hk' : k ≠ k₀ ∧ dep k = d
      · rw [hnew k hk', hpold k hk'.1 hk'.2.le]
        exact ⟨(hg k hk'.1 _ _).1, fun _ => (hg k hk'.1 _ _).2⟩
      · rw [hold k hk']
        have hk'' : k = k₀ ∨ dep k < d := by
          by_cases hk0 : k = k₀
          · exact Or.inl hk0
          · right
            have hne : dep k ≠ d := fun e => hk' ⟨hk0, e⟩
            rcases hk with h | h
            · exact absurd h hk0
            · omega
        refine ⟨(hρ k hk'').1, fun hk0 => ?_⟩
        rw [hpold k hk0 (hk''.resolve_left hk0).le]
        exact (hρ k hk'').2 hk0
  obtain ⟨ρ, hρ0, hρ⟩ := key (Finset.univ.sup dep + 1)
  have hall : ∀ k, k = k₀ ∨ dep k < Finset.univ.sup dep + 1 := fun k =>
    Or.inr (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k)))
  exact ⟨ρ, hρ0, fun k => (hρ k (hall k)).1, fun k hk => (hρ k (hall k)).2 hk⟩

end SimplyLaced

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

structure IsConfig (R : Set (Subgroup G)) {r : ℕ} (adj : Fin r → Fin r → Prop)
    (A B : Fin r → Subgroup G) : Prop where
  memA : ∀ k, A k ∈ R
  memB : ∀ k, B k ∈ R
  opp : ∀ k, Opposite (A k) (B k)
  edge : ∀ i j, adj i j → Special R (A i) (A j) ∧ Commuting (B i) (A j) ∧
    ⁅B i, ⁅A i, A j⁆⁆ = A j ∧ Commuting (A i) (B j) ∧ ⁅⁅A i, A j⁆, B j⁆ = A i ∧
      Special R (B i) (B j)
  nonadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → Commuting (A i) (A j) ∧
    Commuting (A i) (B j) ∧ Commuting (B i) (A j) ∧ Commuting (B i) (B j)

structure IsRootedTree {r : ℕ} (adj : Fin r → Fin r → Prop) (par : Fin r → Fin r)
    (dep : Fin r → ℕ) (k₀ : Fin r) : Prop where
  lt : ∀ k, k ≠ k₀ → dep (par k) < dep k
  adj_par : ∀ k, k ≠ k₀ → adj (par k) k ∨ adj k (par k)
  asymm : ∀ i j, adj i j → ¬ adj j i
  par_of_adj : ∀ i j, adj i j → (j ≠ k₀ ∧ par j = i) ∨ (i ≠ k₀ ∧ par i = j)

theorem IsConfig.exists_frame [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {r : ℕ}
    {adj : Fin r → Fin r → Prop} {A B : Fin r → Subgroup G} (hX : IsConfig R adj A B)
    {par : Fin r → Fin r} {dep : Fin r → ℕ} {k₀ : Fin r} (hT : IsRootedTree adj par dep k₀) :
    ∃ n : ℕ, 1 ≤ n ∧ (∀ E ∈ R, Nat.card E = 2 ^ n) ∧
      ∃ ρ : Fin r → SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* G,
        (∀ k, Function.Injective (ρ k) ∧ (upperUnipotent _).map (ρ k) = A k ∧
          (lowerUnipotent _).map (ρ k) = B k) ∧
        ∀ i j, adj i j → ∃ ψ : SpecialLinearGroup (Fin 3) (GaloisField 2 n) →* G, ∀ c,
          ψ (tv 0 1 c) = ρ i (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ i (tv 1 0 c) ∧
          ψ (tv 1 2 c) = ρ j (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ j (tv 1 0 c) := by
  obtain ⟨n, hn, hq, φ₀, hφ₀, hφ₀'⟩ := (hX.opp k₀).exists_mulEquiv_SL2' hR (hX.memA k₀)
  obtain ⟨hinj₀, hup₀, hlow₀⟩ := Linear.injective_of_mulEquiv φ₀ hφ₀ hφ₀'
  have hcard : ∀ E ∈ R, Nat.card E = 2 ^ n := fun E hE => (hR.card_eq hE (hX.memA k₀)).trans hq
  set F := GaloisField 2 n
  let Nd : Fin r → (SpecialLinearGroup (Fin 2) F →* G) → Prop := fun k ρ =>
    Function.Injective ρ ∧ (upperUnipotent F).map ρ = A k ∧
      (lowerUnipotent F).map ρ = B k
  let Eh : (SpecialLinearGroup (Fin 2) F →* G) → (SpecialLinearGroup (Fin 2) F →* G) → Prop :=
    fun ρ ρ' => ∃ ψ : SpecialLinearGroup (Fin 3) F →* G, ∀ c,
      ψ (tv 0 1 c) = ρ (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ (tv 1 0 c) ∧
      ψ (tv 1 2 c) = ρ' (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ' (tv 1 0 c)
  let Ed : Fin r → (SpecialLinearGroup (Fin 2) F →* G) → (SpecialLinearGroup (Fin 2) F →* G) →
      Prop := fun k ρp ρc => (adj (par k) k → Eh ρp ρc) ∧ (adj k (par k) → Eh ρc ρp)
  have hf : ∀ k, k ≠ k₀ → ∀ t, Nd (par k) t → ∃ t', Nd k t' ∧ Ed k t t' := by
    rintro k hk t ⟨hinj, hup, hlow⟩
    rcases hT.adj_par k hk with hpk | hkp
    · obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hX.edge _ _ hpk
      obtain ⟨ψ, ρ', ⟨h1, h2, h3⟩, hψ⟩ := Linear.exists_sl3_right hR hiso (hX.memA _)
        (hX.memA _) (hX.memB _) (hX.memB _) c1 (hX.opp _) (hX.opp _) c2 c3 c4 c5 c6
        (hcard _ (hX.memA _)) hinj hup hlow
      exact ⟨ρ', ⟨h1, h2, h3⟩, fun _ => ⟨ψ, hψ⟩, fun h => absurd hpk (hT.asymm _ _ h)⟩
    · obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hX.edge _ _ hkp
      obtain ⟨ψ, ρ, ⟨h1, h2, h3⟩, hψ⟩ := Linear.exists_sl3_left hR hiso (hX.memA _)
        (hX.memA _) (hX.memB _) (hX.memB _) c1 (hX.opp _) (hX.opp _) c2 c3 c4 c5 c6
        (hcard _ (hX.memA _)) hinj hup hlow
      exact ⟨ρ, ⟨h1, h2, h3⟩, fun h => absurd hkp (hT.asymm _ _ h), fun _ => ⟨ψ, hψ⟩⟩
  obtain ⟨ρ, -, hρN, hρE⟩ :=
    SimplyLaced.exists_tree Nd Ed par dep k₀ hT.lt hf (t₀ := _) ⟨hinj₀, hup₀, hlow₀⟩
  refine ⟨n, hn, hcard, ρ, hρN, fun i j hij => ?_⟩
  rcases hT.par_of_adj i j hij with ⟨hj, hpj⟩ | ⟨hi, hpi⟩
  · subst hpj
    exact (hρE j hj).1 hij
  · subst hpi
    exact (hρE i hi).2 hij

open CurtisTits in
theorem lieModel_of_rho {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
    {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K} {t : StatedLieTag}
    {N p f : ℕ} (hCT : CurtisTitsConclusion.{0} D t N p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) {G : Type} [Group G] (hZ : Subgroup.center G = ⊥)
    {A B : Fin D.rank → Subgroup G}
    (hnonadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → Commuting (A i) (A j) ∧
      Commuting (A i) (B j) ∧ Commuting (B i) (A j) ∧ Commuting (B i) (B j))
    (ρ : Fin D.rank → SpecialLinearGroup (Fin 2) F →* G)
    (hρ : ∀ k, (upperUnipotent F).map (ρ k) = A k ∧
      (lowerUnipotent F).map (ρ k) = B k)
    (hedge : ∀ i j, adj i j → ∃ ψ : SpecialLinearGroup (Fin 3) F →* G, ∀ c,
      ψ (tv 0 1 c) = ρ i (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ i (tv 1 0 c) ∧
      ψ (tv 1 2 c) = ρ j (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ j (tv 1 0 c))
    (hgen : ⨆ k, (A k ⊔ B k) = ⊤) (hnt : ∃ k, ∃ a ∈ A k, a ≠ 1) : LieModel G t N p f := by
  have hu : ∀ k, Set.range (fun c => ρ k (tv 0 1 c)) = (A k : Set G) := fun k => by
    rw [← (hρ k).1]
    exact Linear.range_tv_upper (ρ k)
  have hv : ∀ k, Set.range (fun c => ρ k (tv 1 0 c)) = (B k : Set G) := fun k => by
    rw [← (hρ k).2]
    exact Linear.range_tv_lower (ρ k)
  have mu : ∀ k c, ρ k (tv 0 1 c) ∈ A k := fun k c => by
    rw [← SetLike.mem_coe, ← hu]
    exact ⟨c, rfl⟩
  have mv : ∀ k c, ρ k (tv 1 0 c) ∈ B k := fun k c => by
    rw [← SetLike.mem_coe, ← hv]
    exact ⟨c, rfl⟩
  have hfr : SimplyLacedFrame D F adj (fun k c => ρ k (tv 0 1 c)) (fun k c => ρ k (tv 1 0 c)) := by
    refine ⟨fun i j hij => hedge i j hij, fun k => ⟨ρ k, fun c => ⟨rfl, rfl⟩⟩,
      fun i j hij h1 h2 c d => ?_⟩
    obtain ⟨c1, c2, c3, c4⟩ := hnonadj i j hij h1 h2
    exact ⟨c1 _ (mu i c) _ (mu j d), c2 _ (mu i c) _ (mv j d), c3 _ (mv i c) _ (mu j d),
      c4 _ (mv i c) _ (mv j d)⟩
  refine lieModel_of_simplyLacedFrame hCT hL hD hZ hfr ?_ ?_
  · rw [Subgroup.closure_iUnion]
    simp_rw [Subgroup.closure_union, hu, hv, Subgroup.closure_eq]
    exact hgen
  · obtain ⟨k, a, ha, ha1⟩ := hnt
    rw [← SetLike.mem_coe, ← hu] at ha
    obtain ⟨c, rfl⟩ := ha
    exact ⟨k, c, ha1⟩

open CurtisTits in
theorem exists_surjective_of_rho {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type}
    [Field F] {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}
    {t : StatedLieTag} {N p f : ℕ} (hCT : CurtisTitsConclusion.{0} D t N p f)
    (hL : LeviConePresented D) (hD : SimplyLacedLevis D F adj x) {G : Type} [Group G]
    {A B : Fin D.rank → Subgroup G}
    (hnonadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → Commuting (A i) (A j) ∧
      Commuting (A i) (B j) ∧ Commuting (B i) (A j) ∧ Commuting (B i) (B j))
    (ρ : Fin D.rank → SpecialLinearGroup (Fin 2) F →* G)
    (hρ : ∀ k, (upperUnipotent F).map (ρ k) = A k ∧ (lowerUnipotent F).map (ρ k) = B k)
    (hedge : ∀ i j, adj i j → ∃ ψ : SpecialLinearGroup (Fin 3) F →* G, ∀ c,
      ψ (tv 0 1 c) = ρ i (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ i (tv 1 0 c) ∧
      ψ (tv 1 2 c) = ρ j (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ j (tv 1 0 c))
    (hgen : ⨆ k, (A k ⊔ B k) = ⊤) (hnt : ∃ k, ∃ a ∈ A k, a ≠ 1) :
    ∃ Ψ : K →* G, (∀ k, (D.rootGroup (sroot k)).map Ψ = A k) ∧
      (∀ k, (D.rootGroup (-sroot k)).map Ψ = B k) ∧ Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center K := by
  have hu : ∀ k, Set.range (fun c => ρ k (tv 0 1 c)) = (A k : Set G) := fun k => by
    rw [← (hρ k).1]
    exact Linear.range_tv_upper (ρ k)
  have hv : ∀ k, Set.range (fun c => ρ k (tv 1 0 c)) = (B k : Set G) := fun k => by
    rw [← (hρ k).2]
    exact Linear.range_tv_lower (ρ k)
  have mu : ∀ k c, ρ k (tv 0 1 c) ∈ A k := fun k c => by
    rw [← SetLike.mem_coe, ← hu]
    exact ⟨c, rfl⟩
  have mv : ∀ k c, ρ k (tv 1 0 c) ∈ B k := fun k c => by
    rw [← SetLike.mem_coe, ← hv]
    exact ⟨c, rfl⟩
  have hfr : SimplyLacedFrame D F adj (fun k c => ρ k (tv 0 1 c)) (fun k c => ρ k (tv 1 0 c)) := by
    refine ⟨fun i j hij => hedge i j hij, fun k => ⟨ρ k, fun c => ⟨rfl, rfl⟩⟩,
      fun i j hij h1 h2 c d => ?_⟩
    obtain ⟨c1, c2, c3, c4⟩ := hnonadj i j hij h1 h2
    exact ⟨c1 _ (mu i c) _ (mu j d), c2 _ (mu i c) _ (mv j d), c3 _ (mv i c) _ (mu j d),
      c4 _ (mv i c) _ (mv j d)⟩
  have hgen' : Subgroup.closure (⋃ k, Set.range (fun c => ρ k (tv 0 1 c)) ∪
      Set.range (fun c => ρ k (tv 1 0 c))) = ⊤ := by
    rw [Subgroup.closure_iUnion]
    simp_rw [Subgroup.closure_union, hu, hv, Subgroup.closure_eq]
    exact hgen
  have hnt' : ∃ k c, ρ k (tv 0 1 c) ≠ 1 := by
    obtain ⟨k, a, ha, ha1⟩ := hnt
    rw [← SetLike.mem_coe, ← hu] at ha
    obtain ⟨c, rfl⟩ := ha
    exact ⟨k, c, ha1⟩
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, -⟩ :=
    exists_surjective_of_simplyLacedFrame hCT hL hD hfr hgen' hnt'
  have hroot : ∀ k, sroot k ∈ D.roots ∧ -sroot k ∈ D.roots := fun k =>
    ⟨(Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (Or.inl rfl)).1.1,
      (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (Or.inl rfl)).2.1⟩
  refine ⟨Ψ, fun k => ?_, fun k => ?_, hsurj, hker⟩
  · ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ (hroot k).1 g hg
      rw [hΨu]
      exact mu k c
    · intro hy
      rw [← SetLike.mem_coe, ← hu] at hy
      obtain ⟨c, rfl⟩ := hy
      exact ⟨x (sroot k) c, hD.mem _ (hroot k).1 c, hΨu k c⟩
  · ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ (hroot k).2 g hg
      rw [hΨv]
      exact mv k c
    · intro hy
      rw [← SetLike.mem_coe, ← hv] at hy
      obtain ⟨c, rfl⟩ := hy
      exact ⟨x (-sroot k) c, hD.mem _ (hroot k).2 c, hΨv k c⟩

@[expose] def parD (n : ℕ) (k : Fin n) : Fin n :=
  if k.val + 1 = n then ⟨n - 3, by have := k.2; omega⟩ else ⟨k.val - 1, by have := k.2; omega⟩

@[expose] def depD (n : ℕ) (k : Fin n) : ℕ := if k.val + 1 = n then n - 2 else k.val

theorem val_parD {n : ℕ} (k : Fin n) :
    (parD n k).val = if k.val + 1 = n then n - 3 else k.val - 1 := by
  unfold parD
  split_ifs <;> rfl

theorem isRootedTree_D {n : ℕ} (hn : 4 ≤ n) :
    IsRootedTree (edgeD n) (parD n) (depD n) ⟨0, by omega⟩ := by
  have hk0 : ∀ k : Fin n, k ≠ ⟨0, by omega⟩ → k.val ≠ 0 := fun k hk h => hk (Fin.ext h)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have h1 := hk0 k hk
    have h2 := k.2
    have h3 := val_parD k
    unfold depD
    split_ifs at h3 ⊢ <;> omega
  · have h1 := hk0 k hk
    have h2 := k.2
    have h3 := val_parD k
    unfold edgeD
    split_ifs at h3 <;> omega
  · unfold edgeD at hij hji
    omega
  · left
    unfold edgeD at hij
    have h3 := val_parD j
    refine ⟨fun h => ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · split_ifs at h3 <;> omega

@[expose] def parE (r : ℕ) (hr : 4 ≤ r) (k : Fin r) : Fin r :=
  if k.val = 1 then ⟨3, by omega⟩ else if k.val = 2 then ⟨0, by omega⟩ else
    ⟨k.val - 1, by have := k.2; omega⟩

@[expose] def depE (r : ℕ) (k : Fin r) : ℕ :=
  if k.val = 1 then 3 else if k.val = 2 then 1 else if k.val = 0 then 0 else k.val - 1

theorem val_parE {r : ℕ} (hr : 4 ≤ r) (k : Fin r) :
    (parE r hr k).val = if k.val = 1 then 3 else if k.val = 2 then 0 else k.val - 1 := by
  unfold parE
  split_ifs <;> rfl

theorem isRootedTree_E {r : ℕ} (hr : 4 ≤ r) :
    IsRootedTree (edgeE r) (parE r hr) (depE r) ⟨0, by omega⟩ := by
  have hk0 : ∀ k : Fin r, k ≠ ⟨0, by omega⟩ → k.val ≠ 0 := fun k hk h => hk (Fin.ext h)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have h1 := hk0 k hk
    have h3 := val_parE hr k
    unfold depE
    split_ifs at h3 ⊢ <;> omega
  · have h1 := hk0 k hk
    have h3 := val_parE hr k
    unfold edgeE
    split_ifs at h3 <;> omega
  · unfold edgeE at hij hji
    omega
  · unfold edgeE at hij
    have hi := val_parE hr i
    have hj := val_parE hr j
    have hne : ∀ k : Fin r, k.val ≠ 0 → k ≠ ⟨0, by omega⟩ := fun k hk h => hk (by rw [h])
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨hne j (by omega), Fin.ext ?_⟩
      split_ifs at hj <;> omega
    · right
      refine ⟨hne i (by omega), Fin.ext ?_⟩
      simp only [h1, ↓reduceIte] at hi
      omega
    · left
      refine ⟨hne j (by omega), Fin.ext ?_⟩
      split_ifs at hj <;> omega

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem IsConfig.lieModel_D [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hZ : Subgroup.center G = ⊥) {n : ℕ} (hn : 4 ≤ n) {A B : Fin n → Subgroup G}
    (hX : IsConfig R (edgeD n) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ LieModel G .POmegaPlus n 2 f := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_D hn)
  have hn3 : 3 ≤ n := by omega
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨f, hf, hcard, lieModel_of_rho (D := Spin.plusDatum n F hn3)
    (CurtisTits.curtisTitsConclusion_spinPlus ⟨Nat.prime_two, hf, hn⟩ hF hn3)
    (leviConePresented_spinPlus F hn3) (simplyLacedLevis_spinPlus F hn3) hZ hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
  exact ⟨(⟨0, by omega⟩ : Fin n), a, ha, ha1⟩

theorem IsConfig.lieModel_E6 [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hZ : Subgroup.center G = ⊥) {A B : Fin 6 → Subgroup G}
    (hX : IsConfig R (edgeE 6) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ LieModel G .E6 0 2 f := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_E (by norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  refine ⟨f, hf, hcard, lieModel_of_rho (D := Minuscule.e6Datum F)
    (CurtisTits.curtisTitsConclusion_e6 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e6 F) (simplyLacedLevis_e6 F) hZ hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA 0)
  exact ⟨(0 : Fin 6), a, ha, ha1⟩

theorem IsConfig.lieModel_E7 [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hZ : Subgroup.center G = ⊥) {A B : Fin 7 → Subgroup G}
    (hX : IsConfig R (edgeE 7) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ LieModel G .E7 0 2 f := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_E (by norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  refine ⟨f, hf, hcard, lieModel_of_rho (D := Minuscule.e7Datum F)
    (CurtisTits.curtisTitsConclusion_e7 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e7 F) (simplyLacedLevis_e7 F) hZ hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA 0)
  exact ⟨(0 : Fin 7), a, ha, ha1⟩

theorem IsConfig.lieModel_E8 [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hZ : Subgroup.center G = ⊥) {A B : Fin 8 → Subgroup G}
    (hX : IsConfig R (edgeE 8) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ LieModel G .E8 0 2 f := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_E (by norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  refine ⟨f, hf, hcard, lieModel_of_rho (D := Adjoint.e8Datum F)
    (CurtisTits.curtisTitsConclusion_e8 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e8 F) (simplyLacedLevis_e8 F) hZ hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA 0)
  exact ⟨(0 : Fin 8), a, ha, ha1⟩

theorem IsConfig.exists_surjective_D [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {n : ℕ} (hn : 4 ≤ n) {A B : Fin n → Subgroup G} (hX : IsConfig R (edgeD n) A B)
    (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : _ →* G,
        (∀ k, ((Spin.plusDatum n (GaloisField 2 f) (by omega)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((Spin.plusDatum n (GaloisField 2 f) (by omega)).rootGroup (-sroot k)).map Ψ =
          B k) ∧ Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_D hn)
  have hn3 : 3 ≤ n := by omega
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨f, hf, hcard, exists_surjective_of_rho (D := Spin.plusDatum n F hn3)
    (CurtisTits.curtisTitsConclusion_spinPlus ⟨Nat.prime_two, hf, hn⟩ hF hn3)
    (leviConePresented_spinPlus F hn3) (simplyLacedLevis_spinPlus F hn3) hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
  exact ⟨(⟨0, by omega⟩ : Fin n), a, ha, ha1⟩

theorem IsConfig.exists_surjective_E6 [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Fin 6 → Subgroup G} (hX : IsConfig R (edgeE 6) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : ↥(Minuscule.e6Data_valid.minGroup (GaloisField 2 f)) →* G,
        (∀ k, ((Minuscule.e6Datum (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((Minuscule.e6Datum (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ = B k) ∧
        Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_E (by norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  refine ⟨f, hf, hcard, exists_surjective_of_rho (D := Minuscule.e6Datum F)
    (CurtisTits.curtisTitsConclusion_e6 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e6 F) (simplyLacedLevis_e6 F) hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA 0)
  exact ⟨(0 : Fin 6), a, ha, ha1⟩

theorem IsConfig.exists_surjective_E7 [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Fin 7 → Subgroup G} (hX : IsConfig R (edgeE 7) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : ↥(Minuscule.e7Data_valid.minGroup (GaloisField 2 f)) →* G,
        (∀ k, ((Minuscule.e7Datum (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((Minuscule.e7Datum (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ = B k) ∧
        Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_E (by norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  refine ⟨f, hf, hcard, exists_surjective_of_rho (D := Minuscule.e7Datum F)
    (CurtisTits.curtisTitsConclusion_e7 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e7 F) (simplyLacedLevis_e7 F) hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA 0)
  exact ⟨(0 : Fin 7), a, ha, ha1⟩

theorem IsConfig.exists_surjective_E8 [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Fin 8 → Subgroup G} (hX : IsConfig R (edgeE 8) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : ↥(Chevalley.adjointGroup .E8 (GaloisField 2 f)) →* G,
        (∀ k, ((Adjoint.e8Datum (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((Adjoint.e8Datum (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ = B k) ∧
        Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_E (by norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  refine ⟨f, hf, hcard, exists_surjective_of_rho (D := Adjoint.e8Datum F)
    (CurtisTits.curtisTitsConclusion_e8 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e8 F) (simplyLacedLevis_e8 F) hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA 0)
  exact ⟨(0 : Fin 8), a, ha, ha1⟩

end CFSG.Timmesfeld.ARS
