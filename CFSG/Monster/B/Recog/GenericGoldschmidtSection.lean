module

public import CFSG.Monster.B.Recog.GenericGoldschmidtApp
public import CFSG.Adapters.Involutions

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open CFSG.Open CFSG.ComponentClassification GoldschmidtApp

namespace GoldschmidtSection

variable {G : Type*} [Group G]

theorem relIndex_centralizer_dvd {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) {H : Subgroup Y} (hHE : H ≤ goldschmidtLayer Y) :
    (Subgroup.centralizer (K : Set Y)).relIndex H ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hKE : K ≤ goldschmidtLayer Y := Layer.component_le hK
  have hEK : goldschmidtLayer Y ≤ Subgroup.normalizer (K : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).1 (Layer.normal_component hK)
  have hEC : goldschmidtLayer Y ≤ Subgroup.normalizer
      ((goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) : Set Y) :=
    fun e he => Subgroup.mem_normalizer_fintype fun c hc =>
      ⟨(goldschmidtLayer Y).mul_mem ((goldschmidtLayer Y).mul_mem he hc.1)
        ((goldschmidtLayer Y).inv_mem he), conj_mem_centralizer (hEK he) hc.2⟩
  have hsup : (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) ⊔ K = goldschmidtLayer Y := by
    refine le_antisymm (sup_le inf_le_left hKE) (sSup_le fun K₂ hK₂ => ?_)
    by_cases hne : K₂ = K
    · exact hne ▸ le_sup_right
    · exact le_sup_of_le_left (le_inf (Layer.component_le hK₂)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne K₂ K hK₂ hK hne)))
  have hinf : ((goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) ⊓ K : Subgroup Y) =
      (Subgroup.center K).map K.subtype := by
    rw [map_center_eq_inf_centralizer, inf_comm, ← inf_assoc, inf_eq_left.mpr hKE]
  have h2 := natCard_sup_mul_natCard_inf_of_le_normalizer (hKE.trans hEC)
  rw [hsup, hinf, Subgroup.card_map_of_injective K.subtype_injective] at h2
  have h3 := (Subgroup.center K).card_mul_index
  have hrel : (Subgroup.centralizer (K : Set Y)).relIndex H =
      (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)).relIndex H := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (K : Set Y)) H,
      ← Subgroup.inf_relIndex_right (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) H,
      inf_comm (goldschmidtLayer Y), inf_assoc, inf_eq_right.mpr hHE]
  have h4 := Subgroup.relIndex_mul_card (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) H
  have h5 := natCard_sup_mul_natCard_inf_of_le_normalizer (hHE.trans hEC)
  have h6 := Subgroup.card_dvd_of_le (sup_le (inf_le_left :
    goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) ≤ goldschmidtLayer Y) hHE)
  rw [hrel]
  set c := Nat.card (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y)
  set r := (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)).relIndex H
  set i := Nat.card (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) ⊓ H : Subgroup Y)
  have hi : 0 < i := Nat.card_pos
  have hc : 0 < c := Nat.card_pos
  have hz : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
  have e1 : c * r = Nat.card ((goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) ⊔ H :
      Subgroup Y) := by
    refine Nat.eq_of_mul_eq_mul_right hi ?_
    rw [h5, ← h4]
    ring
  have e2 : Nat.card (goldschmidtLayer Y) = c * (Subgroup.center K).index := by
    refine Nat.eq_of_mul_eq_mul_right hz ?_
    rw [h2, ← h3]
    ring
  rw [e2, ← e1] at h6
  exact (Nat.mul_dvd_mul_iff_left hc).1 h6

theorem peel_step {Y : Type*} [Group Y] [Finite Y] {Q : Type*} [Group Q] [IsSimpleGroup Q]
    {H : Subgroup Y} (hHE : H ≤ goldschmidtLayer Y) (f : H →* Q) {A : Subgroup Y} (hAH : A ≤ H)
    (hA : (A.subgroupOf H).map f = ⊤) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    ((A ⊓ Subgroup.centralizer (K : Set Y)).subgroupOf H).map f = ⊤ ∨
      Nat.card Q ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hKE : K ≤ goldschmidtLayer Y := Layer.component_le hK
  have hEK : goldschmidtLayer Y ≤ Subgroup.normalizer (K : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).1 (Layer.normal_component hK)
  have hnorm : (((A ⊓ Subgroup.centralizer (K : Set Y)).subgroupOf H).map f).Normal := by
    constructor
    rintro _ ⟨y, hy, rfl⟩ q
    obtain ⟨a, ha, rfl⟩ : q ∈ (A.subgroupOf H).map f := hA ▸ Subgroup.mem_top q
    refine ⟨a * y * a⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha hy ⊢
    refine ⟨A.mul_mem (A.mul_mem ha hy.1) (A.inv_mem ha), ?_⟩
    exact conj_mem_centralizer (hEK (hHE a.2)) hy.2
  have := hnorm
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (((A ⊓ Subgroup.centralizer (K : Set Y)).subgroupOf H).map f) with h | h
  · right
    let fA : A →* Q := f.comp (Subgroup.inclusion hAH)
    have hfA : Function.Surjective fA := by
      intro q
      obtain ⟨a, ha, rfl⟩ : q ∈ (A.subgroupOf H).map f := hA ▸ Subgroup.mem_top q
      exact ⟨⟨a, ha⟩, rfl⟩
    have hker : (Subgroup.centralizer (K : Set Y)).subgroupOf A ≤ fA.ker := by
      intro a ha
      rw [MonoidHom.mem_ker]
      have hmem : Subgroup.inclusion hAH a ∈ (A ⊓ Subgroup.centralizer (K : Set Y)).subgroupOf H :=
        ⟨a.2, ha⟩
      have h1 := Subgroup.mem_map_of_mem f hmem
      rw [h, Subgroup.mem_bot] at h1
      exact h1
    have hQ : Nat.card Q = fA.ker.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fA hfA).toEquiv).symm
    rw [hQ]
    exact (Subgroup.index_dvd_of_le hker).trans (relIndex_centralizer_dvd hK (hAH.trans hHE))
  · exact Or.inl h

theorem exists_component_dvd_of_simple_quotient {Y : Type*} [Group Y] [Finite Y] {Q : Type*}
    [Group Q] [IsSimpleGroup Q] (hQ : ¬ IsMulCommutative Q) {H : Subgroup Y}
    (hHE : H ≤ goldschmidtLayer Y) (f : H →* Q) (hf : Function.Surjective f) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ Nat.card Q ∣ Nat.card (K ⧸ Subgroup.center K) := by
  by_contra hno
  push Not at hno
  have key : ∀ 𝒥 : Set (Subgroup Y), 𝒥.Finite → (∀ K ∈ 𝒥, IsComponentOf K ⊤) →
      ((H ⊓ ⨅ K ∈ 𝒥, Subgroup.centralizer (K : Set Y)).subgroupOf H).map f = ⊤ := by
    intro 𝒥 h𝒥
    induction 𝒥, h𝒥 using Set.Finite.induction_on with
    | empty =>
      intro _
      simp only [Set.mem_empty_iff_false, not_false_eq_true, iInf_neg, iInf_top, inf_top_eq,
        Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact hf
    | @insert K 𝒥 _ _ ih =>
      intro hall
      have hK : IsComponentOf K ⊤ := hall K (Set.mem_insert _ _)
      have hA := ih fun K' hK' => hall K' (Set.mem_insert_of_mem _ hK')
      rw [iInf_insert, inf_left_comm, inf_comm (Subgroup.centralizer (K : Set Y))]
      rcases peel_step hHE f inf_le_left hA hK with h | h
      · exact h
      · exact absurd h (hno K hK)
  have hall := key {K : Subgroup Y | IsComponentOf K ⊤} (Set.toFinite _) fun K hK => hK
  apply hQ
  have hcomm : ∀ x ∈ (H ⊓ ⨅ K ∈ {K : Subgroup Y | IsComponentOf K ⊤},
      Subgroup.centralizer (K : Set Y)), ∀ y ∈ (H ⊓ ⨅ K ∈ {K : Subgroup Y | IsComponentOf K ⊤},
      Subgroup.centralizer (K : Set Y)), x * y = y * x := by
    intro x hx y hy
    have hyE : y ∈ goldschmidtLayer Y := hHE hy.1
    have hxE : goldschmidtLayer Y ≤ Subgroup.centralizer ({x} : Set Y) := by
      refine sSup_le fun K hK => fun k hk => ?_
      have hxK := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 K) hK
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hxK k hk
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hxE hyE)).symm
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, hx, rfl⟩ : a ∈ _ := hall ▸ Subgroup.mem_top a
  obtain ⟨y, hy, rfl⟩ : b ∈ _ := hall ▸ Subgroup.mem_top b
  rw [← map_mul, ← map_mul]
  exact congrArg f (Subtype.ext (hcomm _ hx _ hy))

theorem eq_inf_of_isPGroup [Finite G] (S : Sylow 2 G) {N R : Subgroup G} [N.Normal]
    (hR : IsPGroup 2 R) (hRN : R ≤ N) (hSR : (S : Subgroup G) ⊓ N ≤ R) :
    R = (S : Subgroup G) ⊓ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := natCard_sup_mul_natCard_inf_of_le_normalizer (A := N) (B := (S : Subgroup G))
    (by rw [Subgroup.normalizer_eq_top N]; exact le_top)
  have h2 := Subgroup.relIndex_mul_card ((S : Subgroup G) ⊓ N) N
  rw [inf_assoc, inf_idem] at h2
  have h3 := Subgroup.relIndex_mul_card (S : Subgroup G) ((S : Subgroup G) ⊔ N)
  rw [inf_eq_left.mpr le_sup_left] at h3
  have hS : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
  have hSN : 0 < Nat.card ((S : Subgroup G) ⊓ N : Subgroup G) := Nat.card_pos
  have e : ((S : Subgroup G) ⊓ N).relIndex N =
      (S : Subgroup G).relIndex ((S : Subgroup G) ⊔ N) := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hS hSN) ?_
    calc ((S : Subgroup G) ⊓ N).relIndex N * (Nat.card (S : Subgroup G) *
          Nat.card ((S : Subgroup G) ⊓ N : Subgroup G)) =
        Nat.card (S : Subgroup G) * Nat.card N := by rw [← h2]; ring
      _ = (S : Subgroup G).relIndex ((S : Subgroup G) ⊔ N) * (Nat.card (S : Subgroup G) *
          Nat.card ((S : Subgroup G) ⊓ N : Subgroup G)) := by
        rw [mul_comm (Nat.card (S : Subgroup G)), ← h1, sup_comm, inf_comm, ← h3]; ring
  have hodd : ¬ 2 ∣ ((S : Subgroup G) ⊓ N).relIndex N := by
    rw [e]
    exact fun h => S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hSR hRN
  have hodd' : ¬ 2 ∣ ((S : Subgroup G) ⊓ N).relIndex R := fun h =>
    hodd (hmul ▸ Dvd.dvd.mul_right h _)
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hone : ((S : Subgroup G) ⊓ N).relIndex R = 1 := by
    refine Nat.Coprime.eq_one_of_dvd (m := 2 ^ k) ?_ (hk ▸ Subgroup.relIndex_dvd_card _ _)
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).2 hodd')))
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hSR

theorem eq_bot_of_isPGroup_of_isPerfect [Finite G] {E : Subgroup G} (hE2 : IsPGroup 2 E)
    (hEp : Group.IsPerfect E) : E = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent E := hE2.isNilpotent
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 hnil
  have htop : ∀ k, (⊤ : Subgroup E).lowerCentralSeries k = ⊤ := by
    intro k
    induction k with
    | zero => exact Subgroup.lowerCentralSeries_zero _
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ih, ← commutator_def]
      exact hEp.commutator_eq_top
  rw [htop] at hn
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : E) = 1 := (Subgroup.mem_bot).1 (hn ▸ Subgroup.mem_top _)
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val h1)

theorem eq_bot_of_map_isPGroup {Y : Type*} [Group Y] [Finite Y] {E : Subgroup Y}
    (hEp : Group.IsPerfect E) {ι : Y →* G} (hι : Function.Injective ι)
    (h2 : IsPGroup 2 (E.map ι)) : E = ⊥ := by
  have h := h2.comap_of_injective ι hι
  rw [Subgroup.comap_map_eq_self_of_injective hι] at h
  exact eq_bot_of_isPGroup_of_isPerfect h hEp

end GoldschmidtSection

open GoldschmidtSection

theorem normal_of_goldschmidt_conclusion_of_section {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) {V : Subgroup X} (hVS : V ≤ S)
    (hGold :
      let M : Subgroup X := Subgroup.normalClosure (V : Set X)
      let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
      let T := ((S : Subgroup X).subgroupOf M).map π ⊓
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
      (V.subgroupOf M).map π =
        CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
      ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
        CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (hclosed : ∀ a ∈ V, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ V)
    (hO : CFSG.oddCore X = ⊥)
    (hC2 : IsPGroup 2 (Subgroup.centralizer (V : Set X)))
    (hQB1' : ∀ U : Subgroup X, U ≤ V →
      Subgroup.normalizer (V : Set X) ≤ Subgroup.normalizer (U : Set X) → U = ⊥ ∨ U = V)
    {O : Type*} [Group O] (ρ : ↥(Subgroup.normalizer (V : Set X)) →* O)
    (hρ : Function.Surjective ρ)
    (hker : ∀ g : ↥(Subgroup.normalizer (V : Set X)),
      ρ g = 1 ↔ (g : X) ∈ Subgroup.centralizer (V : Set X))
    (Ω : Subgroup O) (hΩ : IsSimpleGroup Ω) (hΩnab : ¬ IsMulCommutative Ω)
    (hΩmin : ∀ R : Subgroup O, R.Normal → R ≠ ⊥ → Ω ≤ R)
    (hAr : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.goldschmidtSimpleType L →
      Nat.card Ω ∣ Nat.card L → Nat.card L ∣ Nat.card X → False) :
    V.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne V ⊥ with hV1 | hV1
  · rw [hV1]
    infer_instance
  obtain ⟨-, hGb, hGc⟩ := hGold
  have hOM : goldschmidtOddCore (Subgroup.normalClosure (V : Set X)) = ⊥ := by
    have h := OddCore.normal_intersection X (Subgroup.normalClosure (V : Set X))
    have h' : componentClassificationOddCore X = ⊥ := hO
    rw [h', inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h
  set M : Subgroup X := Subgroup.normalClosure (V : Set X) with hM
  have hVM : V ≤ M := Subgroup.le_normalClosure
  have hπ : Function.Injective (QuotientGroup.mk' (goldschmidtOddCore M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOM]
  obtain ⟨φ, hφ⟩ : ∃ φ : M ≃* M ⧸ goldschmidtOddCore M,
      ∀ m, φ m = QuotientGroup.mk' (goldschmidtOddCore M) m :=
    ⟨MulEquiv.ofBijective _ ⟨hπ, QuotientGroup.mk'_surjective _⟩, fun _ => rfl⟩
  obtain ⟨ι, hιdef⟩ : ∃ ι : M ⧸ goldschmidtOddCore M →* X,
      ι = M.subtype.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hι : Function.Injective ι := by
    rw [hιdef]
    exact M.subtype_injective.comp φ.symm.injective
  have hιπ : ∀ m : M, ι (QuotientGroup.mk' (goldschmidtOddCore M) m) = m := by
    intro m
    rw [hιdef, ← hφ]
    simp
  have hnormal : ∀ A : Subgroup (M ⧸ goldschmidtOddCore M), A.Characteristic →
      (A.map ι).Normal := by
    intro A hA
    rw [hιdef]
    exact normal_map_of_characteristic φ hA
  have hnorm : ∀ (A : Subgroup X) [A.Normal] (n : X), n ∈ Subgroup.normalizer (A : Set X) :=
    fun A _ n => (Subgroup.normalizer_eq_top A).symm ▸ Subgroup.mem_top n
  have hVeq : ((V.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M))).map ι = V := by
    have hcomp : ι.comp (QuotientGroup.mk' (goldschmidtOddCore M)) = M.subtype := by
      ext m
      exact hιπ m
    rw [Subgroup.map_map, hcomp, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVM]
  have hLX : ∀ K : Subgroup (M ⧸ goldschmidtOddCore M),
      Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card X := by
    intro K
    refine (Subgroup.index_dvd_card (Subgroup.center K)).trans
      ((Subgroup.card_subgroup_dvd_card K).trans ?_)
    rw [← Nat.card_congr φ.toEquiv]
    exact Subgroup.card_subgroup_dvd_card M
  set E := goldschmidtLayer (M ⧸ goldschmidtOddCore M) with hE
  have hEX : (E.map ι).Normal := hnormal E (Layer.characteristic _)
  by_cases hO2 : CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) = ⊥
  swap
  · have hle : (CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M)).map ι ≤ V := by
      rw [← hVeq, hGb]
      exact Subgroup.map_mono le_sup_left
    have hP := hnormal _ (openPCore_characteristic _)
    rcases hQB1' _ hle (fun n _ => hnorm _ n) with h | h
    · exact absurd ((Subgroup.map_eq_bot_iff_of_injective _ hι).1 h) hO2
    · rw [← h]
      exact hP
  have hVE : V ≤ E.map ι := by
    rw [← hVeq, hGb, hO2, bot_sup_eq]
    exact Subgroup.map_mono ((Subgroup.closure_le _).2 fun t ht => ht.1.2)
  have hRn : ((E.map ι).subgroupOf (Subgroup.normalizer (V : Set X))).Normal := inferInstance
  by_cases hR : ((E.map ι).subgroupOf (Subgroup.normalizer (V : Set X))).map ρ = ⊥
  ·
    have hRC : Subgroup.normalizer (V : Set X) ⊓ E.map ι ≤ Subgroup.centralizer (V : Set X) := by
      intro x hx
      have h1 := Subgroup.mem_map_of_mem ρ
        (show (⟨x, hx.1⟩ : Subgroup.normalizer (V : Set X)) ∈
          (E.map ι).subgroupOf (Subgroup.normalizer (V : Set X)) from hx.2)
      rw [hR, Subgroup.mem_bot] at h1
      exact (hker _).1 h1
    have hSN : (S : Subgroup X) ≤ Subgroup.normalizer (V : Set X) := fun s hs =>
      Subgroup.mem_normalizer_fintype fun v hv => by
        have h := hclosed v hv s⁻¹ (by
          rw [inv_inv]
          exact S.mul_mem (S.mul_mem hs (hVS hv)) (S.inv_mem hs))
        rwa [inv_inv] at h
    have hReq : Subgroup.normalizer (V : Set X) ⊓ E.map ι = (S : Subgroup X) ⊓ E.map ι :=
      eq_inf_of_isPGroup S (hC2.to_le hRC) inf_le_right (inf_le_inf_right _ hSN)
    obtain ⟨P, hP⟩ : ∃ P : Sylow 2 (E.map ι),
        (P : Subgroup (E.map ι)) = ((S : Subgroup X) ⊓ E.map ι).subgroupOf (E.map ι) := by
      obtain ⟨P, hP⟩ := ((S.isPGroup'.to_le (inf_le_left :
        (S : Subgroup X) ⊓ E.map ι ≤ S)).comap_of_injective _
          (E.map ι).subtype_injective).exists_le_sylow
      refine ⟨P, ?_⟩
      have h := eq_inf_of_isPGroup S (R := (P : Subgroup (E.map ι)).map (E.map ι).subtype)
        (P.isPGroup'.map _) (Subgroup.map_subtype_le _)
        (fun x hx => ⟨⟨x, hx.2⟩, hP hx, rfl⟩)
      rw [← h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        (E.map ι).subtype_injective]
    have hPC : ∀ p ∈ (P : Subgroup (E.map ι)), (p : X) ∈ Subgroup.centralizer (V : Set X) := by
      intro p hp
      rw [hP, Subgroup.mem_subgroupOf, ← hReq] at hp
      exact hRC hp
    have hV2 : IsPGroup 2 V := S.isPGroup'.to_le hVS
    have h2V : 2 ∣ Nat.card V := by
      rcases hV2.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hV1
      · exact h
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2V
    have hvE : (v : X) ∈ E.map ι := hVE v.2
    have hvP : (⟨v, hvE⟩ : E.map ι) ∈ (P : Subgroup (E.map ι)) := by
      rw [hP, Subgroup.mem_subgroupOf]
      exact ⟨hVS v.2, hvE⟩
    have hvZ : (⟨⟨v, hvE⟩, hvP⟩ : (P : Subgroup (E.map ι))) ∈
        Subgroup.center (P : Subgroup (E.map ι)) := by
      rw [Subgroup.mem_center_iff]
      intro p
      refine Subtype.ext (Subtype.ext ?_)
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_iff.1 (hPC p p.2) v v.2).symm
    have hv2 : orderOf (⟨⟨v, hvE⟩, hvP⟩ : (P : Subgroup (E.map ι))) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hv]
    have hwc : ∀ g : E.map ι, g⁻¹ * (⟨v, hvE⟩ : E.map ι) * g ∈ (P : Subgroup (E.map ι)) →
        g⁻¹ * (⟨v, hvE⟩ : E.map ι) * g = ⟨v, hvE⟩ := by
      intro g hg
      have hgS : (g : X)⁻¹ * v * g ∈ (S : Subgroup X) := by
        rw [hP, Subgroup.mem_subgroupOf] at hg
        exact hg.1
      have hgV := hclosed v v.2 g hgS
      have hcent : ∀ y : E.map ι, (y : X) ∈ V → y ∈ Subgroup.centralizer
          ((P : Subgroup (E.map ι)) : Set (E.map ι)) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hPC p hp) y hy).symm)
      obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P ⟨v, hvE⟩ g
        (hcent _ v.2) (hcent _ hgV)
      have hnN : (n : X) ∈ Subgroup.normalizer (V : Set X) := Subgroup.mem_normalizer_fintype
        fun w hw => by
          have hwP : (⟨w, hVE hw⟩ : E.map ι) ∈ (P : Subgroup (E.map ι)) := by
            rw [hP, Subgroup.mem_subgroupOf]
            exact ⟨hVS hw, hVE hw⟩
          have h := (Subgroup.mem_normalizer_iff.1 hn _).1 hwP
          rw [hP, Subgroup.mem_subgroupOf] at h
          have h' := hclosed w hw (n : X)⁻¹ (by rw [inv_inv]; exact h.1)
          rwa [inv_inv] at h'
      have hnC := hRC ⟨hnN, n.2⟩
      rw [hgn]
      refine Subtype.ext ?_
      show (n : X)⁻¹ * v * n = v
      have hvn := Subgroup.mem_centralizer_iff.1 hnC v v.2
      rw [mul_assoc, hvn, ← mul_assoc, inv_mul_cancel, one_mul]
    have hGl := CFSG.Adapters.glauberman_zStar P ⟨⟨v, hvE⟩, hvP⟩ hvZ hv2 hwc
    have hOE : CFSG.oddCore (E.map ι) = ⊥ := by
      have h := OddCore.normal_intersection X (E.map ι)
      have h' : componentClassificationOddCore X = ⊥ := hO
      rw [h', inf_bot_eq] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h
    have hvC : (v : X) ∈ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨c, hc, k, hk, hck⟩ := hGl.1 ⟨x, hx⟩
      rw [hOE, Subgroup.mem_bot] at hk
      rw [hk, mul_one] at hck
      have h := Subgroup.mem_centralizer_singleton_iff.1 hc
      rw [← hck] at h
      have h2 := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at h2
      exact h2
    rcases hQB1' (V ⊓ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X)) inf_le_left
        (fun n hn => mem_normalizer_inf hn
          (hnorm (Subgroup.centralizer ((E.map ι : Subgroup X) : Set X)) n)) with h | h
    · have hmem : (v : X) ∈ V ⊓ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) :=
        ⟨v.2, hvC⟩
      rw [h, Subgroup.mem_bot] at hmem
      have hv1 : v = 1 := Subtype.ext hmem
      rw [hv1, orderOf_one] at hv
      exact absurd hv (by norm_num)
    · have hle : V ≤ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) := h ▸ inf_le_right
      have hE2 : IsPGroup 2 (E.map ι) := hC2.to_le (Subgroup.le_centralizer_iff.1 hle)
      have hEbot : E = ⊥ := eq_bot_of_map_isPGroup (Layer.perfect _) hι hE2
      exfalso
      apply hV1
      rw [eq_bot_iff]
      refine hVE.trans ?_
      rw [hEbot, Subgroup.map_bot]
  ·
    have hΩR := hΩmin _ (hRn.map ρ hρ) hR
    have := hΩ
    set HY : Subgroup (M ⧸ goldschmidtOddCore M) :=
      ((((E.map ι).subgroupOf (Subgroup.normalizer (V : Set X))) ⊓ Ω.comap ρ).map
        (Subgroup.normalizer (V : Set X)).subtype).comap ι with hHY
    have hHYE : HY ≤ E := by
      intro y hy
      obtain ⟨n, ⟨⟨e, he, hen⟩, -⟩, hny⟩ := hy
      rw [hny] at hen
      rw [← hι hen]
      exact he
    have hmemN : ∀ y : HY, ι y ∈ Subgroup.normalizer (V : Set X) := by
      intro y
      obtain ⟨n, -, hny⟩ := y.2
      rw [← hny]
      exact n.2
    let f₁ : HY →* Subgroup.normalizer (V : Set X) :=
      (ι.comp HY.subtype).codRestrict _ hmemN
    have hf₁ : ∀ y : HY, ρ (f₁ y) ∈ Ω := by
      intro y
      obtain ⟨n, ⟨-, hnΩ⟩, hny⟩ := y.2
      have e1 : f₁ y = n := Subtype.ext hny.symm
      rw [e1]
      exact hnΩ
    let f : HY →* Ω := (ρ.comp f₁).codRestrict Ω hf₁
    have hf : Function.Surjective f := by
      intro ω
      obtain ⟨n, hnR, hnω⟩ := hΩR ω.2
      obtain ⟨e, he, hen⟩ := hnR
      have hnΩ : n ∈ Ω.comap ρ := by
        rw [Subgroup.mem_comap, hnω]
        exact ω.2
      have hy : e ∈ HY := ⟨n, ⟨⟨e, he, hen⟩, hnΩ⟩, hen.symm⟩
      refine ⟨⟨e, hy⟩, Subtype.ext ?_⟩
      show ρ (f₁ ⟨e, hy⟩) = ω
      have e1 : f₁ ⟨e, hy⟩ = n := Subtype.ext hen
      rw [e1, hnω]
    obtain ⟨K, hK, hdvd⟩ := exists_component_dvd_of_simple_quotient hΩnab hHYE f hf
    exact (hAr _ (hGc K hK) hdvd (hLX K)).elim

end CFSG.Monster.B.Recog
