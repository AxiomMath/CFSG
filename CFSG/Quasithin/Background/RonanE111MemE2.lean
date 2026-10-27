module

public import CFSG.Quasithin.Background.RonanE111Ex2
public import CFSG.Quasithin.Background.RonanE111CoverSec

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_inf_le_tauOf {H T A : Subgroup G} (hTH : T ≤ H) :
    T ⊓ Subgroup.centralizer (A : Set G) ≤ E1.tauOf H T A := by
  intro t ht
  refine ⟨ht.1, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH ht.1), fun a ha => ?_⟩
  have : a * t = t * a := Subgroup.mem_centralizer_iff.mp ht.2 a ha
  have h1 : ⁅t, a⁆ = 1 := by
    rw [commutatorElement_def]
    have : t * a = a * t := this.symm
    rw [this]
    group
  rw [h1]
  exact Subgroup.one_mem _

theorem pow_mem_of_mem_sup_two {J S : Subgroup G} (hSJ : S ≤ Subgroup.normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) {y : G} (hy : y ∈ J ⊔ S) : ∃ k : ℕ, y ^ 2 ^ k ∈ J := by
  have hSJ' : ∀ s ∈ S, ∀ j ∈ J, s * j * s⁻¹ ∈ J := fun s hs j hj =>
    (Subgroup.mem_normalizer_iff.mp (hSJ hs) j).mp hj
  have hy' : y ∈ S ⊔ J := by rwa [sup_comm]
  obtain ⟨s, hs, j, hj, rfl⟩ := wr_mem_sup hSJ' hy'
  obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
  have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have key : ∀ m : ℕ, ∃ j' ∈ J, (s * j) ^ 2 ^ m = s ^ 2 ^ m * j' := by
    intro m
    induction m with
    | zero => exact ⟨j, hj, by simp⟩
    | succ m ih =>
      obtain ⟨j', hj', hjm⟩ := ih
      have hsm' : s⁻¹ ^ 2 ^ m ∈ S := S.pow_mem (S.inv_mem hs) _
      refine ⟨(s⁻¹ ^ 2 ^ m) * j' * (s⁻¹ ^ 2 ^ m)⁻¹ * j', J.mul_mem (hSJ' _ hsm' _ hj') hj', ?_⟩
      rw [pow_succ, pow_mul, hjm, sq]
      simp only [inv_pow, mul_inv_rev, inv_inv, pow_succ, pow_mul]
      group
  obtain ⟨j', hj', hjm⟩ := key m
  exact ⟨m, by rw [hjm, hsm, one_mul]; exact hj'⟩

theorem perfectCore_le_of_le_sup_two {J S P : Subgroup G} (hSJ : S ≤ Subgroup.normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hP : P ≤ J ⊔ S) : perfectCore P ≤ J := by
  have hJS : J ⊔ S ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSJ
  have hX : perfectCore P ≤ J ⊔ S := (perfectCore_le P).trans hP
  have : Group.IsSolvable ↥S := by
    have := hS2.isNilpotent
    infer_instance
  refine le_of_le_sup_of_perfect (perfectCore_perfect P) (fun x hx r hr => ?_)
    (fun y hy r hr => ?_) this hX
  · exact (Subgroup.mem_normalizer_iff.mp (hJS (hX hx)) r).mp hr
  · exact (Subgroup.mem_normalizer_iff.mp (hSJ hy) r).mp hr

theorem P_le_cov_E2 {X T J : Subgroup G} (hR : E111Reduced G X T) (hJ : IsComp X J) {n : ℕ}
    (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hmem : ∀ K : Subgroup G, E1.IsE n ⊤ T A K → K ≤ G₁)
    {P : Subgroup G}
    (hPH : P ≤ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
    (htau : E1.tauOf (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) (T ⊓ Subgroup.normalizer (J : Set G))
      (A ⊓ Subgroup.normalizer (J : Set G)) ≤ (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P)
    (hSyl : IsSylowIn 2 ((T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P) P)
    (hE2 : E1.ETwo ↥P (((T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P).subgroupOf P)
      ((A ⊓ Subgroup.normalizer (J : Set G)).subgroupOf P))
    (hbar : Nat.card (E1.barRad ↥P ((A ⊓ Subgroup.normalizer (J : Set G)).subgroupOf P)) ≤ 2 ^ n) :
    P ≤ Cov G₁ J := by
  classical
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hSdef
  set V : Subgroup G := A ⊓ Subgroup.normalizer (J : Set G) with hVdef
  set H : Subgroup G := J ⊔ S with hHdef
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hHS : S ≤ H := le_sup_right
  have hVS : V ≤ S := le_inf (inf_le_left.trans hAT) inf_le_right
  have hJN : J ≤ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer
  have hAcent : ∀ v ∈ V, v ∈ Subgroup.centralizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := congrArg Subtype.val (hAab.1.is_comm.comm ⟨w, hw.1⟩ ⟨v, hv.1⟩)
    exact this
  have hVP : V ≤ P := fun v hv =>
    (htau (centralizer_inf_le_tauOf hHS ⟨hVS hv, hAcent v hv⟩)).2
  have hEM : actE T A J ≤ S ⊓ P := by
    intro e he
    obtain ⟨heT, heN, heA⟩ := mem_actE_iff.mp he
    refine htau (centralizer_inf_le_tauOf hHS ⟨⟨heT, heN⟩, ?_⟩)
    show e ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.mp heA v hv.1
  obtain ⟨XM, YM, ℒ, L₁, hXM, hYX, hSec, hL₁, hperf, hSylX, hPX, hmove, hrank⟩ :=
    e2_sec hVP hSyl hE2 hbar
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hS2 : IsPGroup 2 ↥S := hT.2.1.to_le hST
  have hXJ : XM ≤ J := by
    rw [hXM]
    exact perfectCore_le_of_le_sup_two hSN hS2 hPH
  obtain ⟨Z, hZA, hZV, hZVA⟩ := exists_compl hAab (inf_le_left : V ≤ A)
  have hset : DiagSetting X T A J Z := ⟨hR, hAT, hAab, hJ, hZA, hZV⟩
  haveI : Fintype ↥Z := Fintype.ofFinite _
  have hSylX' : IsSylowIn 2 (T ⊓ XM) XM := by
    have : T ⊓ XM = S ⊓ XM := by
      ext x
      constructor
      · rintro ⟨hxT, hxX⟩
        exact ⟨⟨hxT, Subgroup.le_normalizer (hXJ hxX)⟩, hxX⟩
      · rintro ⟨⟨hxT, _⟩, hxX⟩
        exact ⟨hxT, hxX⟩
    rw [this]
    exact hSylX
  have hcov := cover_section hn hset hSec hperf (inf_le_left : S ⊓ P ≤ T ⊓ Subgroup.normalizer (J : Set G))
    hEM hXJ hSylX' hL₁ (Or.inl hmove) hrank
  have hG₁ : T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K ≤ G₁ :=
    sup_le hTG (iSup₂_le fun K hK => hmem K hK)
  have hXCov : XM ≤ Cov G₁ J := hcov.trans (Cov_mono J hG₁)
  have hSCov : S ≤ Cov G₁ J := fun s hs => mem_Cov_of_mem (hTG hs.1) hs.2
  rw [hPX]
  exact sup_le hXCov (inf_le_left.trans hSCov)

end CFSG.Quasithin.RonanE111
