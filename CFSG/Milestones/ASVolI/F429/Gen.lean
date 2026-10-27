module

public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.Milestones.ASVolI.A3Aut.Core
public import CFSG.Milestones.ASVolI.F429.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open CFSG.LieType.BorelTits (pCoreOf_le pCoreOf_isPGroup le_pCoreOf_of_le_normalizer
  normalizer_le_normalizer_pCoreOf)

section Generic

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_le_normalizer_inf [Gp.Normal] (X : Subgroup E) :
    X ≤ Subgroup.normalizer ((Gp ⊓ X : Subgroup E) : Set E) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyG, hyX⟩
    exact ⟨‹Gp.Normal›.conj_mem y hyG x, X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx)⟩
  · rintro ⟨hyG, hyX⟩
    refine ⟨?_, ?_⟩
    · have := ‹Gp.Normal›.conj_mem _ hyG x⁻¹
      simpa [mul_assoc] using this
    · have := X.mul_mem (X.mul_mem (X.inv_mem hx) hyX) hx
      simpa [mul_assoc] using this

theorem burnsideF429_le_normalizer_pCore_inf [Gp.Normal] (X : Subgroup E) :
    X ≤ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ X) : Subgroup E) : Set E) :=
  (burnsideF429_le_normalizer_inf X).trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem burnsideF429_pCore_inf_le [Finite E] [Gp.Normal] (X : Subgroup E) :
    pCoreOf 2 (Gp ⊓ X) ≤ pCoreOf 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_right)
    (burnsideF429_le_normalizer_pCore_inf X) (pCoreOf_isPGroup 2 _)

theorem burnsideF429_pCore_inf_Gp_le [Finite E] [Gp.Normal] (X : Subgroup E) :
    pCoreOf 2 X ⊓ Gp ≤ pCoreOf 2 (Gp ⊓ X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 (le_inf inf_le_right (inf_le_left.trans (pCoreOf_le 2 X)))
    ?_ ((pCoreOf_isPGroup 2 X).to_le inf_le_left)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hgX : g ∈ X := hg.2
  have hgG : g ∈ Gp := hg.1
  have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hgX
  have hNi := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (X.inv_mem hgX)
  constructor
  · rintro ⟨hyO, hyG⟩
    exact ⟨(Subgroup.mem_normalizer_iff.1 hN y).1 hyO,
      Gp.mul_mem (Gp.mul_mem hgG hyG) (Gp.inv_mem hgG)⟩
  · rintro ⟨hyO, hyG⟩
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hNi _).1 hyO
      simpa [mul_assoc] using this
    · have := Gp.mul_mem (Gp.mul_mem (Gp.inv_mem hgG) hyG) hgG
      simpa [mul_assoc] using this

theorem burnsideF429_pCore_eq_of_le [Finite E] [Gp.Normal] {X : Subgroup E}
    (h : pCoreOf 2 X ≤ Gp) : pCoreOf 2 X = pCoreOf 2 (Gp ⊓ X) :=
  le_antisymm (le_inf le_rfl h |>.trans (burnsideF429_pCore_inf_Gp_le X))
    (burnsideF429_pCore_inf_le X)

theorem burnsideF429_sbar_le [Finite E] [Gp.Normal] {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ T :=
  (burnsideF429_pCore_inf_le (M₁ ⊓ M₂)).trans (F7.isSylowTwoOf_pCoreOf_le hT)

theorem burnsideF429_mem_of_odd [Finite E] [Gp.Normal] (hodd : Odd Gp.index) {x : E} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ Gp :=
  burnsideF4d_two_elt_mem hodd hx

theorem burnsideF429_le_of_odd [Finite E] [Gp.Normal] (hodd : Odd Gp.index) {P : Subgroup E}
    (hP : IsPGroup 2 P) : P ≤ Gp := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact burnsideF429_mem_of_odd hodd (k := k) (by simpa using congrArg Subtype.val hk)

theorem burnsideF429_sbar_le_oPPrime [Finite E] {P : Subgroup E}
    (hP : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ P) : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ oPPrime 2 P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (pCoreOf_isPGroup 2 (Gp ⊓ (M₁ ⊓ M₂)))) ⟨s, hs⟩
  exact Subgroup.subset_closure ⟨hP hs, k, by rw [← hk, Subgroup.orderOf_mk]⟩

theorem burnsideF429_ctr_eq_of_le [Finite E] [Gp.Normal] {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) (hTG : T ⊓ Gp ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hZ : ctr T ≤ Gp) :
    ctr T = ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ⊓ Subgroup.centralizer (T : Set E) := by
  have hST := burnsideF429_sbar_le (Gp := Gp) hT
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxS : x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := hTG ⟨hx.1, hZ hx⟩
    exact ⟨⟨hxS, Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 hx.2) y (hST hy)⟩, hx.2⟩
  · rintro x ⟨⟨hxS, -⟩, hxc⟩
    exact ⟨hST hxS, hxc⟩

end Generic

section Setting

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_T_inf_Gp (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : T ⊓ Gp = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (burnsideF429_sbar_le hT)
    ((pCoreOf_le 2 _).trans inf_le_left))
  have hSyl := burnsideF429_sylowBar_inf hyp (M := M₁ ⊓ M₂) le_rfl
  have hle : T ⊓ Gp ≤ Gp ⊓ (M₁ ⊓ M₂) := fun x hx => ⟨hx.2, hT.1 hx.1⟩
  obtain ⟨x, hx, hconj⟩ := F7.isSylowTwoOf_exists_conj_le hSyl hle (hT.2.1.to_le inf_le_left)
  intro s hs
  have h1 : x⁻¹ * s * x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := mem_conjSub.1 (hconj hs)
  have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) hx
  have := (Subgroup.mem_normalizer_iff.1 hN _).1 h1
  simpa [mul_assoc] using this

theorem burnsideF429_T_eq_of_odd (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hodd : Odd Gp.index)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : T = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  rw [← burnsideF429_T_inf_Gp hyp hT]
  exact (inf_eq_left.2 (burnsideF429_le_of_odd hodd hT.2.1)).symm

theorem burnsideF429_C2_of_odd (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hodd : Odd Gp.index)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C2 κ f Gp M₁ M₂ hyp T := by
  have hTS := burnsideF429_T_eq_of_odd hyp hodd hT
  refine ⟨⟨1, T.one_mem, ?_⟩, ⟨⊥, ?_⟩, ?_⟩
  · rw [Subgroup.zpowers_one_eq_bot, bot_sup_eq, hTS]
  · refine ⟨hTS.ge, bot_le, inf_bot_eq _, fun g hg => ⟨g, hTS.le hg, 1, Subgroup.one_mem _, mul_one g⟩⟩
  · intro t ht hts
    exact absurd (hTS.le ht) hts

theorem burnsideF429_C4_of_odd (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hodd : Odd Gp.index) :
    burnsideF429_C4 Gp M₁ M₂ := by
  haveI := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨burnsideF429_pCore_eq_of_le (burnsideF429_le_of_odd hodd (pCoreOf_isPGroup 2 _)),
    burnsideF429_pCore_eq_of_le (burnsideF429_le_of_odd hodd (pCoreOf_isPGroup 2 _)),
    burnsideF429_pCore_eq_of_le (burnsideF429_le_of_odd hodd (pCoreOf_isPGroup 2 _))⟩

theorem burnsideF429_C6_of_odd (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hodd : Odd Gp.index)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C6 κ f Gp M₁ M₂ T := by
  rw [burnsideF429_C6, burnsideF429_T_eq_of_odd hyp hodd hT]
  exact Or.inl ⟨rfl, rfl⟩

theorem burnsideF429_ctr_of_le (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) (hZ : ctr T ≤ Gp) :
    ctr T = ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ⊓ Subgroup.centralizer (T : Set E) := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF429_ctr_eq_of_le hT (burnsideF429_T_inf_Gp hyp hT).le hZ

theorem burnsideF429_normalizer_sbar_inf (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) :
    Gp ⊓ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) ≤
      Gp ⊓ (M₁ ⊓ M₂) := by
  haveI := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨S, hS, hB⟩, -⟩ := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB]
    exact le_inf hS.1 Subgroup.le_normalizer
  have hBN : Gp ⊓ (M₁ ⊓ M₂) ≤ Subgroup.normalizer (S : Set E) := by
    rw [hB]
    exact inf_le_right
  have hS1 : S ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := le_pCoreOf_of_le_normalizer 2 hSB hBN hS.2.1
  have hS2 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ S :=
    burnsideAut_le_of_sylow hS hS1 ((pCoreOf_le 2 _).trans inf_le_left) (pCoreOf_isPGroup 2 _)
  rw [le_antisymm hS2 hS1, hB]

theorem burnsideF429_normalizer_sbar_le (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) :
    Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) ≤ M₁ ⊓ M₂ := by
  haveI := hyp.normal
  intro x hx
  obtain ⟨n, hn, h, hh, rfl⟩ := hyp.split x
  have hhN := burnsideF429_le_normalizer_pCore_inf (Gp := Gp) (M₁ ⊓ M₂) hh
  have hnN : n ∈ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
    have : n = n * h * h⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hhN)
  exact (M₁ ⊓ M₂).mul_mem (burnsideF429_normalizer_sbar_inf hyp ⟨hn, hnN⟩).2 hh

theorem burnsideF429_pCore_le_normalizer_sbar (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {M : Subgroup E}
    (hM : M₁ ⊓ M₂ ≤ M) :
    pCoreOf 2 M ≤ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
  haveI := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set R := pCoreOf 2 M with hRdef
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := pCoreOf_le 2 _
  have hSM : S ≤ M := hSB.trans (inf_le_right.trans hM)
  have hRM : R ≤ M := pCoreOf_le 2 M
  have hSnR : S ≤ Subgroup.normalizer (R : Set E) :=
    hSM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hRS2 : IsPGroup 2 ↥(S ⊔ R) :=
    IsPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 _) (pCoreOf_isPGroup 2 M) hSnR
  have hRSM : S ⊔ R ≤ M := sup_le hSM hRM
  have hInt : (S ⊔ R) ⊓ Gp = S := by
    refine le_antisymm ?_ (le_inf le_sup_left (hSB.trans inf_le_left))
    exact burnsideAut_le_of_sylow (burnsideF429_sylowBar_inf hyp hM)
      (le_inf le_sup_left (hSB.trans inf_le_left))
      (fun x hx => ⟨hx.2, hRSM hx.1⟩) (hRS2.to_le inf_le_left)
  intro r hr
  have hrRS : r ∈ S ⊔ R := Subgroup.mem_sup_right hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [← hInt]
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hrRS hy1) (Subgroup.inv_mem _ hrRS),
      ‹Gp.Normal›.conj_mem y hy2 r⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hrRS) hy1) hrRS
      simpa [mul_assoc] using this
    · have := ‹Gp.Normal›.conj_mem _ hy2 r⁻¹
      simpa [mul_assoc] using this

theorem burnsideF429_C4_of_key (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    (hkey : ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp) :
    burnsideF429_C4 Gp M₁ M₂ := by
  haveI := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have step : ∀ X : Subgroup E, pCoreOf 2 X ≤ M₁ ⊓ M₂ → Gp ⊓ (M₁ ⊓ M₂) ≤ X →
      pCoreOf 2 (Gp ⊓ X) ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → pCoreOf 2 X ≤ Gp := by
    intro X hXB hBX hXS r hr
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (pCoreOf_isPGroup 2 X)) ⟨r, hr⟩
    refine hkey r (hXB hr) k (by rw [← hk, Subgroup.orderOf_mk]; exact pow_orderOf_eq_one r) ?_
    intro b hb
    refine hXS (burnsideF429_pCore_inf_Gp_le X ⟨?_, ?_⟩)
    ·
      have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hBX hb)
      have h1 : b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 X :=
        (Subgroup.mem_normalizer_iff.1 hN _).1 (Subgroup.inv_mem _ hr)
      have e : r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hr h1
    ·
      have h1 : r * b * r⁻¹ ∈ Gp := ‹Gp.Normal›.conj_mem b hb.1 r
      exact Gp.mul_mem h1 (Gp.inv_mem hb.1)
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) := pCoreOf_le 2 _
  have hQi : ∀ {M : Subgroup E}, M₁ ⊓ M₂ ≤ M →
      pCoreOf 2 (Gp ⊓ M) ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := fun hM =>
    F7.isSylowTwoOf_pCoreOf_le (burnsideF429_sylowBar_inf hyp hM)
  have hOi : ∀ {M : Subgroup E}, M₁ ⊓ M₂ ≤ M → pCoreOf 2 M ≤ M₁ ⊓ M₂ := fun hM =>
    (burnsideF429_pCore_le_normalizer_sbar hyp hM).trans (burnsideF429_normalizer_sbar_le hyp)
  exact ⟨burnsideF429_pCore_eq_of_le (step _ (pCoreOf_le 2 _) inf_le_right le_rfl),
    burnsideF429_pCore_eq_of_le
      (step _ (hOi inf_le_left) (inf_le_right.trans inf_le_left) (hQi inf_le_left)),
    burnsideF429_pCore_eq_of_le
      (step _ (hOi inf_le_right) (inf_le_right.trans inf_le_right) (hQi inf_le_right))⟩

end Setting

end CFSG.ASVolI
