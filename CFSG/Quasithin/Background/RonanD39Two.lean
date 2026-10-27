module

public import CFSG.Quasithin.Background.F918V3SZTop
public import CFSG.Quasithin.Background.SmithD39TwoSzHolds
public import CFSG.Quasithin.EmptyFaithful.S146R5

public section

namespace CFSG.Quasithin.RonanD39

open CFSG.Open

section Conj

variable {W : Type} [CommGroup W]

theorem suzukiModel_conjAutSub_iff (g : MulAut W) (K : Subgroup (MulAut W)) (n : ℕ) :
    CFSG.Blueprint.SuzukiModel (↥(conjAutSub g K) ⧸ Subgroup.center ↥(conjAutSub g K)) 2 n ↔
      CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n := by
  let e : ↥K ≃* ↥(conjAutSub g K) :=
    Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let e' : ↥K ⧸ Subgroup.center ↥K ≃* ↥(conjAutSub g K) ⧸ Subgroup.center ↥(conjAutSub g K) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥(conjAutSub g K)) e
      (Subgroup.map_center_eq e)
  exact ⟨H13.suzukiModel_of_mulEquiv e', H13.suzukiModel_of_mulEquiv e'.symm⟩

theorem isComponentOf_conjAutSub {K M : Subgroup (MulAut W)} (hK : IsComponentOf K M)
    {g : MulAut W} (hg : g ∈ M) : IsComponentOf (conjAutSub g K) M := by
  have h := B15P4.isComponentOf_map_equiv (MulAut.conj g) hK
  have hM : M.map (MulAut.conj g).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  rwa [hM] at h

theorem conjAutSub_commutator (g : MulAut W) (H K : Subgroup (MulAut W)) :
    conjAutSub g ⁅H, K⁆ = ⁅conjAutSub g H, conjAutSub g K⁆ :=
  Subgroup.map_commutator H K _

theorem conjAutSub_iSup_eq (g : MulAut W) (A K : Subgroup (MulAut W)) :
    conjAutSub g (⨆ a ∈ A, conjAutSub a K) =
      conjClosure (conjAutSub g K) (conjAutSub g A) := by
  apply le_antisymm
  · show (⨆ a ∈ A, conjAutSub a K).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun a ha z hz => ?_
    rw [Subgroup.mem_comap]
    rw [mem_conjAutSub_iff] at hz
    have h := mem_conjClosure (H13.conj_mem_conjAutSub (s := g) ha)
      (H13.conj_mem_conjAutSub (s := g) hz)
    have e : (MulAut.conj g).toMonoidHom z =
        g * a * g⁻¹ * (g * (a⁻¹ * z * a) * g⁻¹) * (g * a * g⁻¹)⁻¹ := by
      show g * z * g⁻¹ = _
      group
    rw [e]
    exact h
  · refine conjClosure_le fun h hh z hz => ?_
    rw [mem_conjAutSub_iff] at hh hz ⊢
    have hmem := H13.conj_mem_conjAutSub (s := g⁻¹ * h * g) hz
    have h2 := (le_iSup₂ (f := fun (a : MulAut W) (_ : a ∈ A) => conjAutSub a K)
      (g⁻¹ * h * g) hh) hmem
    have e : g⁻¹ * (h * z * h⁻¹) * g =
        (g⁻¹ * h * g) * (g⁻¹ * z * g) * (g⁻¹ * h * g)⁻¹ := by group
    rw [e]
    exact h2

end Conj

theorem d39_two_L
    {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) (hMp : Mp = L) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (hcase : V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L))
    {A : Subgroup (MulAut W)} (hA : A ∈ QhatStar M)
    (hnf : ¬ (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1)) :
    (∃ X : Subgroup (MulAut W), X ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) ∧
        (∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) ∧
        X = ⁅X, A ⊓ Subgroup.centralizer (Mp : Set (MulAut W))⁆ ∧
        ((∃ K : Subgroup (MulAut W), (K ∈ CFSG.Quasithin.cComp M ∧ CFSG.IsQuasisimple ↥K) ∧
            ¬ (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n) ∧
            X = CFSG.Quasithin.conjClosure K A) ∨
          (X ≤ CFSG.Open.pCoreOf 3 M ∧ Nat.card ↥X = 3))) ∧
      Mp = L ∧
      (∀ a ∈ A, ∀ y ∈ ⨆ (p : ℕ) (_ : p.Prime) (_ : p ≠ 3), CFSG.Open.pCoreOf p M,
        a * y = y * a) ∧
      (∀ K : Subgroup (MulAut W),
        K ∈ CFSG.Quasithin.cComp (M ⊓ Subgroup.centralizer (L : Set (MulAut W))) →
        CFSG.IsQuasisimple ↥K →
        (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n) →
        ∀ a ∈ A, ∀ y ∈ K, a * y = y * a) := by
  obtain ⟨a, ha, hac, ha1⟩ : ∃ a ∈ A, (∀ y ∈ Mp, a * y = y * a) ∧ a ≠ 1 := by
    by_contra hcon
    exact hnf fun b hb hbc => by
      by_contra hb1
      exact hcon ⟨b, hb, hbc, hb1⟩
  have hA2 : IsPGroup 2 ↥A := by
    obtain ⟨-, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
    exact hA2.isElemAbelian2.isPGroup
  obtain ⟨x, hxM, hAx⟩ := F7.isSylowTwoOf_exists_conj_le hD.hyp.sylow (QhatStar_le hA) hA2
  obtain ⟨A', hA'def⟩ : ∃ A' : Subgroup (MulAut W), A' = conjBy x⁻¹ A := ⟨_, rfl⟩
  have hmemA' : ∀ y, y ∈ A' ↔ x * y * x⁻¹ ∈ A := fun y => by
    rw [hA'def, mem_conjBy_iff, inv_inv]
  have hconjA : ∀ b ∈ A, x⁻¹ * b * x ∈ A' := fun b hb => by
    rw [hmemA']
    have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
    rw [e]
    exact hb
  have hAeq : conjAutSub x A' = A := by
    ext y
    rw [mem_conjAutSub_iff, hmemA']
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [e]
  have hA'Q : A' ∈ QhatStar M := by
    rw [hA'def]
    exact conjBy_mem_QhatStar hA (M.inv_mem hxM)
  have hA'T : A' ≤ T := by
    intro y hy
    rw [hmemA'] at hy
    have h := CFSG.Quasithin.mem_conjSub.mp (hAx hy)
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rwa [e] at h
  have hxN : x ∈ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.hyp.Mp_normal hxM
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    hD.hyp.Mp_normal (M.inv_mem hxM)
  have ha'c : ∀ y ∈ Mp, x⁻¹ * a * x * y = y * (x⁻¹ * a * x) := by
    intro y hy
    have h := hac _ ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy)
    calc x⁻¹ * a * x * y = x⁻¹ * (a * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * a) * x := by rw [h]
      _ = y * (x⁻¹ * a * x) := by group
  have ha'1 : x⁻¹ * a * x ≠ 1 := by
    intro h
    apply ha1
    calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨X', -, hX'M, hX'c, hAX', hX'comm, hX'case, hX'O, hX'Sz, -⟩ :=
    d392_of_d38 SmithD39Two.d38Top_holds W M Mp T L V hD hMp hqM hcase A' hA'Q hA'T
      ⟨x⁻¹ * a * x, hconjA a ha, ha'1, ha'c⟩
  have hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) =
      conjAutSub x (A' ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) := by
    ext y
    rw [mem_conjAutSub_iff, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hyA, hyC⟩
      refine ⟨hconjA y hyA, ?_⟩
      have h := conj_mem_centralizer hxN' hyC
      rwa [inv_inv] at h
    · rintro ⟨hyA, hyC⟩
      rw [hmemA'] at hyA
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rw [e] at hyA
      have h := conj_mem_centralizer hxN hyC
      rw [e] at h
      exact ⟨hyA, h⟩
  refine ⟨⟨conjAutSub x X', ?_, ?_, ?_, ?_⟩, hMp, ?_, ?_⟩
  ·
    intro y hy
    rw [mem_conjAutSub_iff] at hy
    have hyc : x⁻¹ * y * x ∈ Subgroup.centralizer (Mp : Set (MulAut W)) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => (hX'c _ hy z hz).symm
    have hmem : x * (x⁻¹ * y * x) * x⁻¹ ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
      Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hxM (hX'M hy)) (M.inv_mem hxM),
        conj_mem_centralizer hxN hyc⟩
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [e] at hmem
  ·
    intro b hb y hy
    rw [mem_conjAutSub_iff] at hy ⊢
    have h := (Subgroup.mem_normalizer_iff.mp (hAX' (hconjA b hb)) _).mp hy
    have e : x⁻¹ * (b * y * b⁻¹) * x =
        (x⁻¹ * b * x) * (x⁻¹ * y * x) * (x⁻¹ * b * x)⁻¹ := by group
    rw [e]
    exact h
  ·
    rw [hAC, ← conjAutSub_commutator, hX'comm]
  · rcases hX'case with ⟨K, hK, hKns, hX'eq⟩ | ⟨hX'3, hX'card⟩
    ·
      left
      have hK₀ : IsComponentOf (conjAutSub x K) M := isComponentOf_conjAutSub hK hxM
      refine ⟨conjAutSub x K, ⟨F918V3S3.mem_cComp_of_isComponentOf hK₀,
        A3.isQuasisimple_iff_open.mpr hK₀.2.2⟩, ?_, ?_⟩
      · rintro ⟨n, hn⟩
        exact hKns ⟨n, (suzukiModel_conjAutSub_iff x K n).mp hn⟩
      · rw [hX'eq, conjAutSub_iSup_eq, hAeq]
    ·
      right
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [mem_conjAutSub_iff] at hy
        have h := (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 M hxM) _).mp (hX'3 hy)
        have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
        rwa [e] at h
      · have h : Nat.card ↥(conjAutSub x X') = Nat.card ↥X' :=
          Subgroup.card_map_of_injective (MulAut.conj x).injective
        rw [h, hX'card]
  ·
    have hO : (⨆ (p : ℕ) (_ : p.Prime) (_ : p ≠ 3), CFSG.Open.pCoreOf p M) ≤
        Subgroup.centralizer (A : Set (MulAut W)) := by
      refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp3 => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hy' : x⁻¹ * y * x ∈ CFSG.Open.pCoreOf p M :=
        (Subgroup.mem_normalizer_iff''.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p M hxM) y).mp hy
      have h := hX'O p hp hp3 _ (hconjA b hb) _ hy'
      calc b * y = x * ((x⁻¹ * b * x) * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * y * x) * (x⁻¹ * b * x)) * x⁻¹ := by rw [h]
        _ = y * b := by group
    intro b hb y hy
    exact Subgroup.mem_centralizer_iff.mp (hO hy) b hb
  ·
    intro K hKc hKq hKsz b hb y hy
    have hLn : M ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
      rw [← hMp]
      exact hD.hyp.Mp_normal
    have hCnorm : ((M ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.mp hn
      exact Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem g.2 hn1) (M.inv_mem g.2),
        conj_mem_centralizer (hLn g.2) hn2⟩
    have hKM : IsComponentOf K M :=
      ⟨(le_of_mem_cComp hKc).trans inf_le_left,
        A3.subnormal_trans (subnormal_of_mem_cComp hKc)
          (A3.subnormal_of_normal inf_le_left hCnorm),
        A3.isQuasisimple_iff_open.mp hKq⟩
    obtain ⟨n, hn⟩ := hKsz
    have hK₁sz : IsSuzukiComponent (conjAutSub x⁻¹ K) :=
      ⟨n, (suzukiModel_conjAutSub_iff x⁻¹ K n).mpr hn⟩
    have hK₁c : ∀ u ∈ conjAutSub x⁻¹ K, ∀ z ∈ Mp, u * z = z * u := by
      intro u hu z hz
      rw [mem_conjAutSub_iff, inv_inv] at hu
      have hc : x * u * x⁻¹ ∈ Subgroup.centralizer (Mp : Set (MulAut W)) := by
        rw [hMp]
        exact (Subgroup.mem_inf.mp (le_of_mem_cComp hKc hu)).2
      have hc' := conj_mem_centralizer hxN' hc
      have e : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
      rw [e] at hc'
      exact (Subgroup.mem_centralizer_iff.mp hc' z hz).symm
    have hy' : x⁻¹ * y * x ∈ conjAutSub x⁻¹ K := by
      rw [mem_conjAutSub_iff, inv_inv]
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rw [e]
      exact hy
    have h := hX'Sz _ (isComponentOf_conjAutSub hKM (M.inv_mem hxM)) hK₁sz hK₁c _
      (hconjA b hb) _ hy'
    calc b * y = x * ((x⁻¹ * b * x) * (x⁻¹ * y * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * y * x) * (x⁻¹ * b * x)) * x⁻¹ := by rw [h]
      _ = y * b := by group

end CFSG.Quasithin.RonanD39
