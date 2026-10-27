module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.Milestones.ASVolI.A3Spor.Out
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TripleCoverON
public import CFSG.RankThree.Native.ONTripleRed
public import CFSG.LargeExtraspecial.S12Seven
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.ONRigidInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.ONThreeCent

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

@[expose] def ONThreeInnerCore : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .ONan →
    ∀ y : Y, orderOf y = 3 → ∀ R : Subgroup Y,
      R ≤ Subgroup.centralizer {y} →
      (∀ c ∈ Subgroup.centralizer ({y} : Set Y), ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
      Nat.Coprime (Nat.card R) 3 → R = ⊥

@[expose] def K4Theta : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .ONan →
    ∀ H : Subgroup (MulAut Y), (MulAut.conj : Y →* MulAut Y).range ≤ H →
      ∀ σ ∈ H, orderOf σ = 3 →
        inSubgroup (aschbacherSolvableCore 3) (H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))) = ⊥

private lemma conj_injective_of_center_eq_bot
    {Y : Type} [Group Y] (hZY : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyZ : y ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h2 : y * h * y⁻¹ = h := by
      have hc := congrArg (fun φ : MulAut Y => φ h) hy
      simpa only [MulAut.conj_apply, MulAut.one_apply] using hc
    calc h * y = (y * h * y⁻¹) * y := by rw [h2]
      _ = y * h := by group
  rw [hZY] at hyZ
  exact Subgroup.mem_bot.1 hyZ

private lemma exists_order_three_of_conj_injective
    {Y : Type} [Group Y] [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ∣ 2)
    (σ : MulAut Y) (hσ3 : orderOf σ = 3) :
    ∃ y : Y, orderOf y = 3 ∧ σ = MulAut.conj y := by
  have hInner : ∀ α : MulAut Y, Odd (orderOf α) → ∃ y : Y, α = MulAut.conj y :=
    CFSG.ASVolI.burnsideA315s_oddInner_of_not_dvd (fun p hp hp2 hdvd => by
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) (hdvd.trans hOut)
      exact hp2 (le_antisymm hle hp.two_le))
  obtain ⟨y, hyσ⟩ := hInner σ ⟨1, by rw [hσ3]; norm_num⟩
  have hy3pow : y ^ 3 = 1 := by
    apply hinj
    rw [map_pow, ← hyσ]
    have h := pow_orderOf_eq_one σ
    rw [hσ3] at h
    simpa using h
  have hyne : y ≠ 1 := by
    intro hy1
    have hσ1 : σ = 1 := by rw [hyσ, hy1, map_one]
    rw [hσ1, orderOf_one] at hσ3
    omega
  exact ⟨y, orderOf_eq_prime hy3pow hyne, hyσ⟩

private lemma comap_solvableCore_le_centralizer
    {Y : Type} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {H : Subgroup (MulAut Y)}
    {σ : MulAut Y} {y : Y} (hσ : σ = MulAut.conj y)
    {N : Subgroup (MulAut Y)}
    (hNle : N ≤ inSubgroup (aschbacherSolvableCore 3)
      (H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)))) :
    N.comap (MulAut.conj : Y →* MulAut Y) ≤
      Subgroup.centralizer ({y} : Set Y) := by
  intro r hr
  have hrN : MulAut.conj r ∈ N := Subgroup.mem_comap.mp hr
  have hrC : MulAut.conj r ∈
      H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)) := by
    obtain ⟨n₀, -, h₀⟩ := hNle hrN
    rw [← h₀]
    exact n₀.2
  have hcomm : MulAut.conj r * σ = σ * MulAut.conj r :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hrC).2
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply hinj
  rw [map_mul, map_mul]
  simpa only [hσ] using hcomm

private lemma comap_solvableCore_normalized_by_centralizer
    {Y : Type} [Group Y]
    {H : Subgroup (MulAut Y)}
    (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ H)
    {σ : MulAut Y} {y : Y} (hσ : σ = MulAut.conj y)
    {N : Subgroup (MulAut Y)}
    (hNnormal : ∀ c ∈ H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)),
      ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    ∀ c ∈ Subgroup.centralizer ({y} : Set Y),
      ∀ r ∈ N.comap (MulAut.conj : Y →* MulAut Y),
        c * r * c⁻¹ ∈ N.comap (MulAut.conj : Y →* MulAut Y) := by
  intro c hc r hr
  have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcC : MulAut.conj c ∈
      H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)) := by
    constructor
    · exact hInn ⟨c, rfl⟩
    · change MulAut.conj c ∈ Subgroup.centralizer ({σ} : Set (MulAut Y))
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hσ]
      simpa only [map_mul] using congrArg (MulAut.conj : Y →* MulAut Y) hcy
  have hrN : MulAut.conj r ∈ N := Subgroup.mem_comap.mp hr
  have hmem : MulAut.conj c * MulAut.conj r * (MulAut.conj c)⁻¹ ∈ N :=
    hNnormal (MulAut.conj c) hcC (MulAut.conj r) hrN
  rw [Subgroup.mem_comap]
  simpa only [map_mul, map_inv] using hmem

private lemma not_three_dvd_card_solvableCore
    {Y : Type} [Group Y] [Finite Y] (Cσ : Subgroup (MulAut Y)) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) Cσ) := by
  have hNcard : Nat.card (inSubgroup (aschbacherSolvableCore 3) Cσ) =
      Nat.card (aschbacherSolvableCore 3 Cσ) :=
    Subgroup.card_map_of_injective Cσ.subtype_injective
  rw [hNcard]
  exact (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
    (H := ↥Cσ) (p := 3) Nat.prime_three).2.2.1

private lemma solvableCore_inSubgroup_conj_mem
    {Y : Type} [Group Y] (Cσ : Subgroup (MulAut Y)) :
    ∀ c ∈ Cσ, ∀ n ∈ inSubgroup (aschbacherSolvableCore 3) Cσ,
      c * n * c⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Cσ := by
  intro c hc n hn
  obtain ⟨n₀, hn₀, rfl⟩ := hn
  exact ⟨⟨c, hc⟩ * n₀ * ⟨c, hc⟩⁻¹,
    (CFSG.RankThree.LocalRank.aschbacherSolvableCore_normal 3 Cσ).conj_mem n₀ hn₀
      ⟨c, hc⟩, rfl⟩

private lemma comap_solvableCore_eq_bot
    {Y : Type} [Group Y] [Finite Y]
    (h : ONThreeInnerCore) (hY : IsSpor Y .ONan)
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {y : Y} (hy3 : orderOf y = 3)
    {N : Subgroup (MulAut Y)}
    (hRle : N.comap (MulAut.conj : Y →* MulAut Y) ≤
      Subgroup.centralizer ({y} : Set Y))
    (hRnorm : ∀ c ∈ Subgroup.centralizer ({y} : Set Y),
      ∀ r ∈ N.comap (MulAut.conj : Y →* MulAut Y),
        c * r * c⁻¹ ∈ N.comap (MulAut.conj : Y →* MulAut Y))
    (hN3 : ¬ 3 ∣ Nat.card N) :
    N.comap (MulAut.conj : Y →* MulAut Y) = ⊥ ∧
      N ⊓ (MulAut.conj : Y →* MulAut Y).range = ⊥ := by
  let R : Subgroup Y := N.comap (MulAut.conj : Y →* MulAut Y)
  let Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range
  have hmap : R.map (MulAut.conj : Y →* MulAut Y) = N ⊓ Inn := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Subgroup.mem_comap.mp hr, ⟨r, rfl⟩⟩
    · rintro ⟨hxN, hxInn⟩
      obtain ⟨r, rfl⟩ := hxInn
      exact ⟨r, Subgroup.mem_comap.mpr hxN, rfl⟩
  have hRcard : Nat.card R = Nat.card (N ⊓ Inn : Subgroup (MulAut Y)) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (K := R)
      (f := (MulAut.conj : Y →* MulAut Y)) hinj).symm
  have hR3 : Nat.Coprime (Nat.card R) 3 := by
    have hdvd : Nat.card (N ⊓ Inn : Subgroup (MulAut Y)) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le (inf_le_left : N ⊓ Inn ≤ N)
    have hnot : ¬ 3 ∣ Nat.card (N ⊓ Inn : Subgroup (MulAut Y)) := fun h3 =>
      hN3 (h3.trans hdvd)
    rw [hRcard]
    exact Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr hnot)
  have hRbot : R = ⊥ := h Y hY y hy3 R hRle hRnorm hR3
  constructor
  · exact hRbot
  · rw [← hmap, hRbot, Subgroup.map_bot]

private lemma card_solvableCore_dvd_two
    {Y : Type} [Group Y]
    {N : Subgroup (MulAut Y)}
    (hNinfbot : N ⊓ (MulAut.conj : Y →* MulAut Y).range = ⊥)
    (hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ∣ 2) :
    Nat.card N ∣ 2 := by
  let Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range
  let q : MulAut Y →*
      CFSG.ComponentClassification.OuterAutomorphisms.Outer Y :=
    QuotientGroup.mk' Inn
  let f : N →* CFSG.ComponentClassification.OuterAutomorphisms.Outer Y :=
    q.comp N.subtype
  have hker : f.ker = (N ⊓ Inn).subgroupOf N := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro ha
      exact ⟨a.2, (QuotientGroup.eq_one_iff (a : MulAut Y)).mp ha⟩
    · rintro ⟨-, hin⟩
      exact (QuotientGroup.eq_one_iff (a : MulAut Y)).mpr hin
  have hkerbot : f.ker = ⊥ := by rw [hker, hNinfbot, Subgroup.bot_subgroupOf]
  have hcardN : Nat.card N = Nat.card f.range := by
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hkerbot, Subgroup.card_bot, one_mul] at hcard
    exact hcard.symm
  rw [hcardN]
  exact (Subgroup.card_subgroup_dvd_card f.range).trans hOut

private lemma exists_central_outer_involution
    {Y : Type} [Group Y]
    {N : Subgroup (MulAut Y)} {Cσ : Subgroup (MulAut Y)}
    (hNnormal : ∀ c ∈ Cσ, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hNinfbot : N ⊓ (MulAut.conj : Y →* MulAut Y).range = ⊥)
    (hNcard2 : Nat.card N = 2) :
    ∃ τ : N, (τ : MulAut Y) ^ 2 = 1 ∧
      (τ : MulAut Y) ∉ (MulAut.conj : Y →* MulAut Y).range ∧
      ∀ c ∈ Cσ, c * (τ : MulAut Y) * c⁻¹ = (τ : MulAut Y) := by
  let Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range
  obtain ⟨τ, hτne, hunique⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hNcard2
  have hτN : (τ : MulAut Y) ∈ N := τ.2
  have hτ1 : (τ : MulAut Y) ≠ 1 := by
    intro h1
    exact hτne (Subtype.ext h1)
  have hτ2 : (τ : MulAut Y) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := τ)
    rw [hNcard2] at h
    exact congrArg Subtype.val h
  have hτnotInn : (τ : MulAut Y) ∉ Inn := by
    intro hin
    have hmem : (τ : MulAut Y) ∈ N ⊓ Inn := ⟨hτN, hin⟩
    rw [hNinfbot] at hmem
    exact hτ1 (Subgroup.mem_bot.mp hmem)
  have hτcentral : ∀ c ∈ Cσ, c * (τ : MulAut Y) * c⁻¹ = (τ : MulAut Y) := by
    intro c hc
    have hmem : c * (τ : MulAut Y) * c⁻¹ ∈ N := hNnormal c hc τ hτN
    let x : N := ⟨c * (τ : MulAut Y) * c⁻¹, hmem⟩
    have hxne : x ≠ 1 := by
      intro hx1
      have hxval : c * (τ : MulAut Y) * c⁻¹ = 1 := congrArg Subtype.val hx1
      have hτeq : (τ : MulAut Y) = 1 := by
        calc (τ : MulAut Y) = c⁻¹ * (c * (τ : MulAut Y) * c⁻¹) * c := by group
          _ = c⁻¹ * 1 * c := by rw [hxval]
          _ = 1 := by group
      exact hτ1 hτeq
    have hxτ : x = τ := hunique x hxne
    exact congrArg Subtype.val hxτ
  exact ⟨τ, hτ2, hτnotInn, hτcentral⟩

private lemma fixed_centralizer_of_central_automorphism
    {Y : Type} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {H : Subgroup (MulAut Y)}
    (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ H)
    {σ : MulAut Y} {y : Y} (hσ : σ = MulAut.conj y)
    {τ : MulAut Y}
    (hτcentral : ∀ c ∈ H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)),
      c * τ * c⁻¹ = τ) :
    ∀ g ∈ Subgroup.centralizer ({y} : Set Y), τ g = g := by
  have hconj : ∀ g : Y, MulAut.conj (τ g) = τ * MulAut.conj g * τ⁻¹ := by
    intro g
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  intro g hg
  have hc : MulAut.conj g ∈ H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)) := by
    constructor
    · exact hInn ⟨g, rfl⟩
    · change MulAut.conj g ∈ Subgroup.centralizer ({σ} : Set (MulAut Y))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgy : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [hσ]
      simpa only [map_mul] using congrArg (MulAut.conj : Y →* MulAut Y) hgy
  have hcomm : τ * MulAut.conj g = MulAut.conj g * τ := by
    have hcτ := hτcentral (MulAut.conj g) hc
    calc τ * MulAut.conj g =
        (MulAut.conj g * τ * (MulAut.conj g)⁻¹) * MulAut.conj g := by rw [hcτ]
      _ = MulAut.conj g * τ := by group
  apply hinj
  rw [hconj g]
  calc τ * MulAut.conj g * τ⁻¹ = (MulAut.conj g * τ) * τ⁻¹ := by rw [hcomm]
    _ = MulAut.conj g := by group

private lemma no_outer_involution_fixes_nine
    {Y : Type} [Group Y] [Finite Y]
    (eY : Y ≃* CFSG.Blueprint.NativeSporadic.ON)
    (τ : MulAut Y) (hτ2 : τ ^ 2 = 1)
    (hτnotInn : τ ∉ (MulAut.conj : Y →* MulAut Y).range)
    {C : Subgroup Y} (hCcard : Nat.card C = 3240)
    (hfix : ∀ g ∈ C, τ g = g) : False := by
  have h9 : 3 ^ 2 ∣ Nat.card C := by
    rw [hCcard]
    norm_num
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 3 h9
  have hEcard : Nat.card (K.map C.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (K := K) (f := C.subtype)
      C.subtype_injective, hKcard]
    norm_num
  have hEfix : ∀ g ∈ K.map C.subtype, τ g = g := by
    intro g hg
    obtain ⟨k, -, rfl⟩ := hg
    exact hfix (k : Y) k.2
  exact CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.no_outer_fix_nine
    (G := Y) eY τ hτ2 hτnotInn (K.map C.subtype) hEcard hEfix


theorem k4Theta_of_innerCore
    (h : ONThreeInnerCore) : K4Theta := by
  intro Y _ _ hY H hInn σ hσH hσ3
  have hYcopy := hY
  obtain ⟨eY⟩ := hYcopy
  have hZY : Subgroup.center Y = ⊥ :=
    CFSG.Sporadic.FischerOddCore.center_eq_bot_of_mulEquiv eY
      (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.center_ON_eq_bot)
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_eq_bot hZY
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ∣ 2 :=
    CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two hY
  obtain ⟨y, hy3, hyσ⟩ :=
    exists_order_three_of_conj_injective hinj hOut σ hσ3
  let C : Subgroup Y := Subgroup.centralizer ({y} : Set Y)
  let Cσ : Subgroup (MulAut Y) :=
    H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))
  let N : Subgroup (MulAut Y) := inSubgroup (aschbacherSolvableCore 3) Cσ
  have hCcard : Nat.card C = 3240 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.card_centralizer_three_ON
      eY hy3
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_solvableCore Cσ
  have hNnormal : ∀ c ∈ Cσ, ∀ n ∈ N, c * n * c⁻¹ ∈ N :=
    solvableCore_inSubgroup_conj_mem Cσ
  have hNle : N ≤ inSubgroup (aschbacherSolvableCore 3) Cσ := le_rfl
  have hRle : N.comap (MulAut.conj : Y →* MulAut Y) ≤ C :=
    comap_solvableCore_le_centralizer hinj hyσ hNle
  have hRnorm : ∀ c ∈ C, ∀ r ∈ N.comap (MulAut.conj : Y →* MulAut Y),
      c * r * c⁻¹ ∈ N.comap (MulAut.conj : Y →* MulAut Y) :=
    comap_solvableCore_normalized_by_centralizer hInn hyσ hNnormal
  obtain ⟨hRbot, hNinfbot⟩ :=
    comap_solvableCore_eq_bot h hY hinj hy3 hRle hRnorm hN3
  have hN2 : Nat.card N ∣ 2 := card_solvableCore_dvd_two hNinfbot hOut
  by_contra hNne
  have hNcard2 : Nat.card N = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hN2
    have hpos := Nat.card_pos (α := N)
    have hne1 : Nat.card N ≠ 1 := fun h1 => hNne ((Subgroup.eq_bot_iff_card N).2 h1)
    omega
  obtain ⟨τ, hτ2, hτnotInn, hτcentral⟩ :=
    exists_central_outer_involution hNnormal hNinfbot hNcard2
  have hfix : ∀ g ∈ C, (τ : MulAut Y) g = g :=
    fixed_centralizer_of_central_automorphism hinj hInn hyσ hτcentral
  exact no_outer_involution_fixes_nine eY τ hτ2 hτnotInn hCcard hfix

@[irreducible] noncomputable def onTripleKerQuotEquiv :
    CFSG.RankThree.Native.ONTriple.GM ⧸
      (CFSG.RankThree.Native.ONTriple.phiM).ker ≃*
      CFSG.Blueprint.NativeSporadic.ON :=
  (QuotientGroup.quotientKerEquivOfSurjective
    CFSG.RankThree.Native.ONTriple.phiM
    CFSG.RankThree.Native.ONTriple.phiM_surjective).trans
    CFSG.ONSchreier.onEquivPv.symm

@[irreducible] noncomputable def onTripleCenterQuotEquiv :
    CFSG.RankThree.Native.ONTriple.GM ⧸
      Subgroup.center CFSG.RankThree.Native.ONTriple.GM ≃*
      CFSG.Blueprint.NativeSporadic.ON :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.RankThree.Native.ONTriple.center_GM.trans
      CFSG.RankThree.Native.ONTriple.ker_phiM.symm)).trans
    onTripleKerQuotEquiv

theorem threeCover_GM :
    CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover (fun Y _ => IsSpor Y .ONan)
      CFSG.RankThree.Native.ONTriple.GM := by
  have hSimpleON : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  have hSimpleKer : IsSimpleGroup (CFSG.RankThree.Native.ONTriple.GM ⧸
      (CFSG.RankThree.Native.ONTriple.phiM).ker) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hSimpleON onTripleKerQuotEquiv
  have hZeq : (CFSG.RankThree.Native.ONTriple.phiM).ker =
      Subgroup.center CFSG.RankThree.Native.ONTriple.GM :=
    CFSG.RankThree.Native.ONTriple.ker_phiM.trans
      CFSG.RankThree.Native.ONTriple.center_GM.symm
  have hSimpleQuot : IsSimpleGroup (CFSG.RankThree.Native.ONTriple.GM ⧸
      Subgroup.center CFSG.RankThree.Native.ONTriple.GM) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hSimpleKer
      (QuotientGroup.quotientMulEquivOfEq hZeq.symm)
  have hPerfect : Group.IsPerfect CFSG.RankThree.Native.ONTriple.GM :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.isPerfect_GM
  refine ⟨⟨hPerfect.commutator_eq_top, hSimpleQuot⟩, ?_, ?_⟩
  · rw [CFSG.RankThree.Native.ONTriple.center_GM, Nat.card_zpowers,
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.orderOf_zG_eq_three]
  · exact ⟨onTripleCenterQuotEquiv⟩

private lemma exists_lift_of_order_three
    {Y : Type} [Group Y]
    (φ : CFSG.RankThree.Native.ONTriple.GM →*
      CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.ONan)
    (hφsurj : Function.Surjective φ)
    (hφker : φ.ker =
      Subgroup.zpowers CFSG.RankThree.Native.ONTriple.zG)
    (eY : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier
      TauCeti.SporadicName.ONan)
    {y : Y} (hy3 : orderOf y = 3) :
    ∃ ŷ : CFSG.RankThree.Native.ONTriple.GM,
      orderOf ŷ = 3 ∧ eY.symm (φ ŷ) = y := by
  have hx3 : orderOf (CFSG.RankThree.Native.ONTriple.xG 0) = 3 :=
    CFSG.RankThree.Native.ONTriple.orderOf_xG0
  have hxCenter : CFSG.RankThree.Native.ONTriple.xG 0 ∉
      Subgroup.center CFSG.RankThree.Native.ONTriple.GM := by
    rw [CFSG.RankThree.Native.ONTriple.center_GM]
    intro hx
    exact CFSG.RankThree.Native.ONTriple.xG0_not_mem_K0
      (Subgroup.zpowers_le.2 CFSG.RankThree.Native.ONTriple.zG_mem_K0 hx)
  have hv3 : orderOf (φ (CFSG.RankThree.Native.ONTriple.xG 0)) = 3 := by
    have hne : φ (CFSG.RankThree.Native.ONTriple.xG 0) ≠ 1 := by
      intro h1
      apply hxCenter
      rw [CFSG.RankThree.Native.ONTriple.center_GM, ← hφker,
        MonoidHom.mem_ker]
      exact h1
    have hdvd := orderOf_map_dvd φ (CFSG.RankThree.Native.ONTriple.xG 0)
    rw [hx3] at hdvd
    rcases (Nat.dvd_prime (p := 3)
      (m := orderOf (φ (CFSG.RankThree.Native.ONTriple.xG 0)))
      Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hw3 : orderOf (eY y) = 3 := by rw [MulEquiv.orderOf_eq, hy3]
  obtain ⟨g, hg⟩ := CFSG.RankThree.Native.onThree_fusion hv3 hw3
  obtain ⟨g', hg'⟩ := hφsurj g
  let gC : CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.ONan := g
  have hgC' : φ g' = gC := hg'
  have hgC : gC * φ (CFSG.RankThree.Native.ONTriple.xG 0) * gC⁻¹ = eY y := hg
  let ŷ : CFSG.RankThree.Native.ONTriple.GM :=
    g' * CFSG.RankThree.Native.ONTriple.xG 0 * g'⁻¹
  have hφŷ : φ ŷ = eY y := by
    have h1 : φ ŷ =
        gC * φ (CFSG.RankThree.Native.ONTriple.xG 0) * gC⁻¹ := by
      simp [ŷ, map_mul, map_inv, hgC']
    rw [h1]
    exact hgC
  have hπŷ : eY.symm (φ ŷ) = y := by
    rw [hφŷ, MulEquiv.symm_apply_apply]
  have hŷ3 : orderOf ŷ = 3 := by
    have h1 : ŷ = MulAut.conj g'
        (CFSG.RankThree.Native.ONTriple.xG 0) := by
      rw [MulAut.conj_apply]
    rw [h1, MulEquiv.orderOf_eq, hx3]
  exact ⟨ŷ, hŷ3, hπŷ⟩

private lemma K2_centralizer_data_of_lift
    (hK2 : K2ONanCentralizer)
    {ŷ : CFSG.RankThree.Native.ONTriple.GM}
    (hŷ3 : orderOf ŷ = 3)
    (hŷcenter : ŷ ∉ Subgroup.center CFSG.RankThree.Native.ONTriple.GM) :
    (let C₀ : Subgroup CFSG.RankThree.Native.ONTriple.GM :=
        Subgroup.centralizer ({ŷ} : Set CFSG.RankThree.Native.ONTriple.GM)
     let J₀ : Subgroup CFSG.RankThree.Native.ONTriple.GM := ⁅C₀, C₀⁆
     Nat.card C₀ = 3240 ∧
       Subgroup.center CFSG.RankThree.Native.ONTriple.GM ≤ J₀ ∧
       Nat.card J₀ = 1080 ∧ C₀ = Subgroup.zpowers ŷ ⊔ J₀ ∧
       IsAlt (J₀ ⧸
         (Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) 6) := by
  haveI : Finite CFSG.RankThree.Native.ONTriple.GM :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.RankThree.Native.ONTriple.card_GM]; norm_num)
  simpa only using
    hK2 CFSG.RankThree.Native.ONTriple.GM threeCover_GM ŷ hŷ3 hŷcenter

private lemma card_center_subgroupOf_commutator
    {J₀ : Subgroup CFSG.RankThree.Native.ONTriple.GM}
    (hZJ : Subgroup.center CFSG.RankThree.Native.ONTriple.GM ≤ J₀) :
    Nat.card ((Subgroup.center
      CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) = 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZJ).toEquiv,
    CFSG.RankThree.Native.ONTriple.center_GM, Nat.card_zpowers,
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.orderOf_zG_eq_three]

private lemma card_quotient_commutator
    {J₀ : Subgroup CFSG.RankThree.Native.ONTriple.GM}
    (hJcard : Nat.card J₀ = 1080)
    (hZhatJ : Nat.card ((Subgroup.center
      CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) = 3) :
    Nat.card (J₀ ⧸
      (Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) = 360 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀)
  rw [hJcard, hZhatJ] at h
  omega

private lemma commutator_image_is_A6
    {Y : Type} [Group Y]
    {ŷ : CFSG.RankThree.Native.ONTriple.GM}
    {J₀ : Subgroup CFSG.RankThree.Native.ONTriple.GM} {y : Y}
    (hJle : J₀ ≤ Subgroup.centralizer
      ({ŷ} : Set CFSG.RankThree.Native.ONTriple.GM))
    (π : CFSG.RankThree.Native.ONTriple.GM →* Y)
    (hπker : π.ker = Subgroup.center CFSG.RankThree.Native.ONTriple.GM)
    (hπŷ : π ŷ = y)
    (hquotcard : Nat.card (J₀ ⧸
      (Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) = 360)
    (hAltJ : IsAlt (J₀ ⧸
      (Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) 6) :
    ∃ A : Subgroup Y, Nat.card A = 360 ∧ IsAlt A 6 ∧
      A ≤ Subgroup.centralizer ({y} : Set Y) := by
  let A : Subgroup Y := J₀.map π
  let fJ : J₀ →* Y := π.domRestrict J₀
  have hfJker : fJ.ker =
      (Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀ := by
    rw [MonoidHom.ker_domRestrict, hπker]
  have hfJrange : fJ.range = A := by
    rw [MonoidHom.domRestrict_range]
  let eJA : J₀ ⧸
      (Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀ ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hfJker.symm).trans
      ((QuotientGroup.quotientKerEquivRange fJ).trans
        (MulEquiv.subgroupCongr hfJrange))
  have hAcard : Nat.card A = 360 := by
    rw [← hquotcard]
    exact (Nat.card_congr eJA.toEquiv).symm
  have hAltA : IsAlt A 6 := by
    obtain ⟨e6⟩ := hAltJ
    exact ⟨eJA.symm.trans e6⟩
  have hAleC : A ≤ Subgroup.centralizer ({y} : Set Y) := by
    rintro a ⟨j, hj, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hJle hj)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul, hπŷ] using congrArg π hcomm
  exact ⟨A, hAcard, hAltA, hAleC⟩


private lemma exists_A6_image_of_K2
    {Y : Type} [Group Y]
    (hK2 : K2ONanCentralizer)
    (eY : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier
      TauCeti.SporadicName.ONan)
    {y : Y} (hy3 : orderOf y = 3) :
    ∃ A : Subgroup Y, Nat.card A = 360 ∧ IsAlt A 6 ∧
      A ≤ Subgroup.centralizer ({y} : Set Y) := by
  obtain ⟨φ, hφsurj, hφker⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.exists_hom_ON
  let π : CFSG.RankThree.Native.ONTriple.GM →* Y :=
    eY.symm.toMonoidHom.comp φ
  have hπker : π.ker =
      Subgroup.center CFSG.RankThree.Native.ONTriple.GM := by
    ext g
    change eY.symm (φ g) = 1 ↔
      g ∈ Subgroup.center CFSG.RankThree.Native.ONTriple.GM
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφker,
      CFSG.RankThree.Native.ONTriple.center_GM]
  obtain ⟨ŷ, hŷ3, hπŷ⟩ :=
    exists_lift_of_order_three φ hφsurj hφker eY hy3
  have hŷcenter : ŷ ∉
      Subgroup.center CFSG.RankThree.Native.ONTriple.GM := by
    rw [← hπker, MonoidHom.mem_ker, show π ŷ = y from hπŷ]
    intro h1
    rw [h1, orderOf_one] at hy3
    omega
  let C₀ : Subgroup CFSG.RankThree.Native.ONTriple.GM :=
    Subgroup.centralizer ({ŷ} : Set CFSG.RankThree.Native.ONTriple.GM)
  let J₀ : Subgroup CFSG.RankThree.Native.ONTriple.GM := ⁅C₀, C₀⁆
  obtain ⟨-, hZJ, hJcard, -, hAltJ⟩ :=
    K2_centralizer_data_of_lift hK2 hŷ3 hŷcenter
  have hJle : J₀ ≤ C₀ := Subgroup.commutator_le_self C₀
  have hZhatJ : Nat.card ((Subgroup.center
      CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) = 3 :=
    card_center_subgroupOf_commutator hZJ
  have hquotcard : Nat.card (J₀ ⧸
      (Subgroup.center CFSG.RankThree.Native.ONTriple.GM).subgroupOf J₀) = 360 :=
    card_quotient_commutator hJcard hZhatJ
  exact commutator_image_is_A6 hJle π hπker hπŷ hquotcard hAltJ

private lemma le_normalizer_of_normalized
    {Y : Type} [Group Y] {R A : Subgroup Y} {y : Y}
    (hRnorm : ∀ c ∈ Subgroup.centralizer ({y} : Set Y),
      ∀ r ∈ R, c * r * c⁻¹ ∈ R)
    (hAleC : A ≤ Subgroup.centralizer ({y} : Set Y)) :
    A ≤ Subgroup.normalizer (R : Set Y) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    exact hRnorm (a : Y) (hAleC ha) r hr
  · intro x hx
    refine ⟨(a : Y)⁻¹ * x * (a : Y), ?_, ?_⟩
    · have h := hRnorm (a : Y)⁻¹ (hAleC (A.inv_mem ha)) x hx
      rw [inv_inv] at h
      exact h
    · change (a : Y) * ((a : Y)⁻¹ * x * (a : Y)) * (a : Y)⁻¹ = x
      group

private lemma exists_bijection_prod_sup_of_le_normalizer
    {Y : Type} [Group Y] {R A : Subgroup Y}
    (hAnorm : A ≤ Subgroup.normalizer (R : Set Y))
    (hRA : R ⊓ A = ⊥) :
    ∃ f : A × R → (R ⊔ A : Subgroup Y), Function.Bijective f := by
  have hset : ((R ⊔ A : Subgroup Y) : Set Y) =
      (A : Set Y) * (R : Set Y) := by
    have h := Subgroup.coe_mul_of_left_le_normalizer_right A R hAnorm
    rw [sup_comm]
    exact h
  let f : A × R → (R ⊔ A : Subgroup Y) := fun p =>
    ⟨(p.1 : Y) * (p.2 : Y),
      (R ⊔ A).mul_mem (Subgroup.mem_sup_right p.1.2)
        (Subgroup.mem_sup_left p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨a₁, r₁⟩ ⟨a₂, r₂⟩ h
    have h1 : (a₁ : Y) * (r₁ : Y) = (a₂ : Y) * (r₂ : Y) :=
      congrArg Subtype.val h
    have h2 : (a₂ : Y)⁻¹ * (a₁ : Y) = (r₂ : Y) * (r₁ : Y)⁻¹ := by
      calc (a₂ : Y)⁻¹ * (a₁ : Y) =
          (a₂ : Y)⁻¹ * ((a₁ : Y) * (r₁ : Y)) * (r₁ : Y)⁻¹ := by group
        _ = (a₂ : Y)⁻¹ * ((a₂ : Y) * (r₂ : Y)) * (r₁ : Y)⁻¹ := by rw [h1]
        _ = (r₂ : Y) * (r₁ : Y)⁻¹ := by group
    have hAmem : (a₂ : Y)⁻¹ * (a₁ : Y) ∈ A :=
      A.mul_mem (A.inv_mem a₂.2) a₁.2
    have hRmem : (r₂ : Y) * (r₁ : Y)⁻¹ ∈ R :=
      R.mul_mem r₂.2 (R.inv_mem r₁.2)
    have hbot : (a₂ : Y)⁻¹ * (a₁ : Y) ∈ R ⊓ A := ⟨h2 ▸ hRmem, hAmem⟩
    rw [hRA] at hbot
    have hleft : (a₂ : Y)⁻¹ * (a₁ : Y) = 1 := Subgroup.mem_bot.mp hbot
    have hright : (r₂ : Y) * (r₁ : Y)⁻¹ = 1 := by rw [← h2]; exact hleft
    have haeq : (a₁ : Y) = (a₂ : Y) := by
      calc (a₁ : Y) = (a₂ : Y) * ((a₂ : Y)⁻¹ * (a₁ : Y)) := by group
        _ = (a₂ : Y) * 1 := by rw [hleft]
        _ = (a₂ : Y) := by group
    have hreq : (r₁ : Y) = (r₂ : Y) := by
      have h : (r₂ : Y) = (r₁ : Y) := by
        calc (r₂ : Y) = (r₂ : Y) * (r₁ : Y)⁻¹ * (r₁ : Y) := by group
          _ = 1 * (r₁ : Y) := by rw [hright]
          _ = (r₁ : Y) := by group
      exact h.symm
    exact Prod.ext (Subtype.ext haeq) (Subtype.ext hreq)
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : (x : Y) ∈ (A : Set Y) * (R : Set Y) := by
      rw [← hset]
      exact x.2
    obtain ⟨a, ha, r, hr, har⟩ := hx
    refine ⟨(⟨a, ha⟩, ⟨r, hr⟩), ?_⟩
    exact Subtype.ext har
  exact ⟨f, hf_inj, hf_surj⟩

private lemma card_sup_eq_mul_card
    {Y : Type} [Group Y] {R A : Subgroup Y}
    (hAnorm : A ≤ Subgroup.normalizer (R : Set Y))
    (hRA : R ⊓ A = ⊥) :
    Nat.card (R ⊔ A : Subgroup Y) = Nat.card A * Nat.card R := by
  obtain ⟨f, hf⟩ := exists_bijection_prod_sup_of_le_normalizer hAnorm hRA
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

private lemma eq_bot_of_disjoint_image
    {Y : Type} [Group Y] [Finite Y] {R A : Subgroup Y} {y : Y}
    (hRA : R ⊓ A = ⊥)
    (hRle : R ≤ Subgroup.centralizer ({y} : Set Y))
    (hRnorm : ∀ c ∈ Subgroup.centralizer ({y} : Set Y),
      ∀ r ∈ R, c * r * c⁻¹ ∈ R)
    (hAleC : A ≤ Subgroup.centralizer ({y} : Set Y))
    (hAcard : Nat.card A = 360)
    (hCcardY : Nat.card (Subgroup.centralizer ({y} : Set Y)) = 3240)
    (hR3 : Nat.Coprime (Nat.card R) 3) :
    R = ⊥ := by
  have hAnorm := le_normalizer_of_normalized hRnorm hAleC
  have hcard_mul := card_sup_eq_mul_card hAnorm hRA
  have hsupdvd : Nat.card (R ⊔ A : Subgroup Y) ∣ 3240 := by
    have hle : (R ⊔ A : Subgroup Y) ≤
        Subgroup.centralizer ({y} : Set Y) :=
      sup_le hRle hAleC
    exact (Subgroup.card_dvd_of_le hle).trans (by rw [hCcardY])
  have hdvd : 360 * Nat.card R ∣ 3240 := by
    rw [hcard_mul, hAcard] at hsupdvd
    exact hsupdvd
  have hRdvd9 : Nat.card R ∣ 9 := by
    have h := hdvd
    rw [show (3240 : ℕ) = 360 * 9 by norm_num] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have h' : 360 * (Nat.card R * k) = 360 * 9 := by
      rw [hk]
      ring
    exact (mul_left_cancel₀ (by norm_num : (360 : ℕ) ≠ 0) h').symm
  have hRdvd3 : Nat.card R ∣ 3 := by
    apply hR3.dvd_of_dvd_mul_left
    rwa [show (3 : ℕ) * 3 = 9 by norm_num]
  have hRcard1 : Nat.card R = 1 := by
    rcases (Nat.dvd_prime (p := 3) (m := Nat.card R)
      Nat.prime_three).mp hRdvd3 with h1 | h3
    · exact h1
    · exfalso
      rw [h3] at hR3
      norm_num at hR3
  exact (Subgroup.eq_bot_iff_card R).mpr hRcard1

private lemma eq_bot_of_inf_eq_top
    {Y : Type} [Group Y] {R A : Subgroup Y}
    (h : (R ⊓ A).subgroupOf A = ⊤)
    (hAcard : Nat.card A = 360)
    (hR3not : ¬ 3 ∣ Nat.card R) :
    R = ⊥ := by
  exfalso
  have hcardNA : Nat.card ((R ⊓ A).subgroupOf A) = Nat.card A := by
    rw [h, Subgroup.card_top]
  have hcardRA : Nat.card (R ⊓ A : Subgroup Y) = Nat.card A := by
    have h1 : Nat.card ((R ⊓ A : Subgroup Y).subgroupOf A) =
        Nat.card (R ⊓ A : Subgroup Y) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : (R ⊓ A : Subgroup Y) ≤ A)).toEquiv
    rw [hcardNA] at h1
    exact h1.symm
  have hdvd : Nat.card A ∣ Nat.card R := by
    rw [← hcardRA]
    exact Subgroup.card_dvd_of_le (H := (R ⊓ A : Subgroup Y)) (K := R) inf_le_left
  have h3 : 3 ∣ Nat.card A := by rw [hAcard]; norm_num
  exact absurd (h3.trans hdvd) hR3not


theorem onThreeInnerCore_of_K2
    (hK2 : K2ONanCentralizer) : ONThreeInnerCore := by
  intro Y _ _ hY y hy3 R hRle hRnorm hR3
  obtain ⟨eY⟩ := hY
  obtain ⟨A, hAcard, hAltA, hAleC⟩ := exists_A6_image_of_K2 hK2 eY hy3
  have hCcardY : Nat.card (Subgroup.centralizer ({y} : Set Y)) = 3240 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.card_centralizer_three_ON
      eY hy3
  have hR3not : ¬ 3 ∣ Nat.card R :=
    (Nat.prime_three.coprime_iff_not_dvd).mp (Nat.coprime_comm.mp hR3)
  have hNnormal : ((R ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun n hn a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact hRnorm (a : Y) (hAleC a.2) (n : Y) hn.1
    · exact A.mul_mem (A.mul_mem a.2 hn.2) (A.inv_mem a.2)
  haveI hA6simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  obtain ⟨eA6⟩ := hAltA
  haveI hAsimple : IsSimpleGroup A := MulEquiv.isSimpleGroup eA6
  haveI hNnormalI : ((R ⊓ A).subgroupOf A).Normal := hNnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ A).subgroupOf A)
    with h | h
  · have hRA : R ⊓ A = ⊥ := by
      have h1 : (R ⊓ A).subgroupOf A = (⊥ : Subgroup Y).subgroupOf A := by
        rw [h, Subgroup.bot_subgroupOf]
      have h2 := Subgroup.subgroupOf_inj.mp h1
      simpa using h2
    exact eq_bot_of_disjoint_image hRA hRle hRnorm hAleC hAcard hCcardY hR3
  · exact eq_bot_of_inf_eq_top h hAcard hR3not

theorem k4Theta_of_K2
    (hK2 : K2ONanCentralizer) : K4Theta :=
  k4Theta_of_innerCore (onThreeInnerCore_of_K2 hK2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

end
