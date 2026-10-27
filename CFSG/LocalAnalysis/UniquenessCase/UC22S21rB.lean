module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
import CFSG.Quasithin.Background.E1Sec6
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.PreuniquenessRankFour.CoprimeAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin (IsSylowIn)
open scoped Pointwise commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

theorem uc22s21rb_sup_eq_top {R S : Subgroup Q} [R.Normal] (hQR : IsPGroup 2 (Q ⧸ R))
    (hS : IsSylowIn 2 S ⊤) : R ⊔ S = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQR
  have hR : R.index = 2 ^ k := hk
  have h1 : (R ⊔ S).index ∣ R.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (R ⊔ S).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_right
  have hodd : ¬ 2 ∣ S.index := by
    have := hS.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this
  rw [hR] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j = 0 := by
    by_contra hne
    exact hodd ((dvd_pow_self 2 hne).trans (hj ▸ h2))
  rw [hj0, pow_zero] at hj
  exact Subgroup.index_eq_one.mp hj

theorem uc22s21rb_isPGroup_quotient {R S₀ : Subgroup Q} [R.Normal] (hS₀ : IsPGroup 2 S₀)
    (hRS : R ⊔ S₀ = ⊤) : IsPGroup 2 (Q ⧸ R) := by
  refine hS₀.of_surjective ((QuotientGroup.mk' R).comp S₀.subtype) ?_
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R x
  obtain ⟨r, hr, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hRS ▸ Subgroup.mem_top y)
  refine ⟨⟨s, hs⟩, ?_⟩
  simp [map_mul, (QuotientGroup.eq_one_iff r).mpr hr]

theorem uc22s21rb_inF_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {R Φ : Subgroup Q} [R.Normal]
    (hR : IsPGroup q R) (hQR : IsPGroup 2 (Q ⧸ R))
    (hirr : ∀ N : Subgroup Q, N.Normal → N ≤ R → N ≤ Φ ∨ N = R)
    (hfaith : ∀ A : Subgroup Q, A ≠ ⊥ → IsPGroup 2 A → ¬ ⁅R, A⁆ ≤ Φ) :
    F12.InF 1 (⊤ : Subgroup Q) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS Ω hΩ hne hbot
  have hS' : IsSylowIn 2 S ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  have hRS : R ⊔ S = ⊤ := uc22s21rb_sup_eq_top hQR hS'
  set E : Subgroup Q := F12.eGenP 1 (⊤ : Subgroup Q) S Ω with hE
  have hRN : ∀ g : Q, g ∈ normalizer (R : Set Q) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have key1 : ∀ B ∈ Ω, B ≤ S → ⁅R, B⁆ ≤ E := by
    intro B hB hBS
    refine (CFSG.Quasithin.E1.comm_le_iSup_twoResidual hq hq2 hS' hBS (hΩ.isElemAbelian B hB)
      hR).trans (iSup₂_le fun K hK => ?_)
    obtain ⟨hKE, hKc, hKcard⟩ := hK
    have hKP : F12.IsEP 1 (⊤ : Subgroup Q) S B K :=
      ⟨hKE.1, hKE.2.1, hKE.2.2.1, Or.inl ⟨hKc, hKcard⟩⟩
    exact (CFSG.Quasithin.twoResidual_le K).trans
      (le_iSup₂_of_le B hB (le_iSup_of_le hBS (le_iSup₂_of_le K hKP le_rfl)))
  have key2 : ∀ g : Q, ∀ B ∈ Ω, B ≤ S → ∀ c ∈ ⁅R, B⁆, g * c * g⁻¹ ∈ E := by
    intro g B hB hBS c hc
    obtain ⟨r, hr, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hRS ▸ Subgroup.mem_top g)
    have hB'Ω : CFSG.Quasithin.A1b.conjSub s B ∈ Ω := hΩ.conj B hB s (Subgroup.mem_top s)
    have hB'S : CFSG.Quasithin.A1b.conjSub s B ≤ S := by
      rintro _ ⟨b, hb, rfl⟩
      exact S.mul_mem (S.mul_mem hs (hBS hb)) (S.inv_mem hs)
    have hRs : R.map (MulAut.conj s).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRN s)
    have hsc : s * c * s⁻¹ ∈ ⁅R, CFSG.Quasithin.A1b.conjSub s B⁆ := by
      have h1 : (⁅R, B⁆).map (MulAut.conj s).toMonoidHom = ⁅R, CFSG.Quasithin.A1b.conjSub s B⁆ := by
        rw [Subgroup.map_commutator, hRs]
        rfl
      rw [← h1]
      exact ⟨c, hc, by simp [MulAut.conj_apply]⟩
    have hrN : r ∈ normalizer ((⁅R, CFSG.Quasithin.A1b.conjSub s B⁆ : Subgroup Q) : Set Q) :=
      CFSG.Quasithin.E1.le_normalizer_commutator_left hr
    have h2 : r * (s * c * s⁻¹) * r⁻¹ ∈ ⁅R, CFSG.Quasithin.A1b.conjSub s B⁆ :=
      (Subgroup.mem_normalizer_iff.mp hrN _).mp hsc
    have e : r * s * c * (r * s)⁻¹ = r * (s * c * s⁻¹) * r⁻¹ := by group
    rw [e]
    exact key1 _ hB'Ω hB'S h2
  set 𝒞 : Set Q := {c | ∃ B ∈ Ω, B ≤ S ∧ c ∈ ⁅R, B⁆} with h𝒞
  set N : Subgroup Q := Subgroup.normalClosure 𝒞 with hN
  have hNE : N ≤ E := by
    rw [hN, Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨c, ⟨B, hB, hBS, hcB⟩, hcx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hcx
    exact key2 g B hB hBS c hcB
  have hNR : N ≤ R := by
    refine Subgroup.normalClosure_le_normal fun c hc => ?_
    obtain ⟨B, -, -, hcB⟩ := hc
    exact Subgroup.commutator_le_left R B hcB
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨A, hAΩ, hAS⟩ : ∃ A ∈ Ω, A ≤ S := by
    have hA₀2 : IsPGroup 2 A₀ :=
      fun g => ⟨1, Subtype.ext (by simpa using (hΩ.isElemAbelian A₀ hA₀).2 g g.2)⟩
    obtain ⟨S', hS'', hA₀S'⟩ := CFSG.Quasithin.exists_isSylowIn_ge 2 (le_top : A₀ ≤ ⊤) hA₀2
    obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hS'' hS'
    refine ⟨CFSG.Quasithin.A1b.conjSub g A₀, hΩ.conj A₀ hA₀ g (Subgroup.mem_top g), ?_⟩
    intro x hx
    rw [hg, CFSG.Quasithin.B6.mem_conjSub]
    exact hA₀S' (CFSG.Quasithin.A1b.mem_conjSub_iff.mp hx)
  have hA2 : IsPGroup 2 A :=
    fun g => ⟨1, Subtype.ext (by simpa using (hΩ.isElemAbelian A hAΩ).2 g g.2)⟩
  have hNΦ : ¬ N ≤ Φ := by
    intro hle
    refine hfaith A (hbot A hAΩ) hA2 fun c hc => hle ?_
    exact Subgroup.subset_normalClosure ⟨A, hAΩ, hAS, hc⟩
  have hNeq : N = R := (hirr N inferInstance hNR).resolve_left hNΦ
  have hRE : R ≤ E := hNeq ▸ hNE
  refine Set.Subset.antisymm (fun x _ => Subgroup.mem_top x) fun x _ => ?_
  obtain ⟨r, hr, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hRS ▸ Subgroup.mem_top x)
  exact ⟨r, hRE hr, s, hs, rfl⟩

theorem uc22s21rb_faith {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {R : Subgroup Q} [R.Normal]
    (hR : IsPGroup q R) (hQR : IsPGroup 2 (Q ⧸ R)) (hO2 : CFSG.pCore 2 Q = ⊥)
    {A : Subgroup Q} (hA : IsPGroup 2 A) (hAΦ : ⁅R, A⁆ ≤ (frattini ↥R).map R.subtype) :
    A = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hAN : A ≤ normalizer (R : Set Q) := fun a _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top a
  letI : MulDistribMulAction ↥A ↥R := Subgroup.conjMulDistribMulActionOfLeNormalizer A R hAN
  have hcop : ¬ 2 ∣ Nat.card ↥(frattini ↥R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hR.to_subgroup (frattini ↥R))
    rw [hn]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)).symm
  have htriv : ∀ (a : ↥A) (x : ↥R), QuotientGroup.mk' (frattini ↥R) (a • x) =
      QuotientGroup.mk' (frattini ↥R) x := by
    intro a x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : ⁅(a : Q), (x : Q)⁻¹⁆ ∈ ⁅R, A⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator a.2 (R.inv_mem x.2)
    obtain ⟨y, hy, hyx⟩ := hAΦ h1
    have hyeq : y = (a • x)⁻¹ * x := by
      apply Subtype.ext
      change (y : Q) = ((a : Q) * (x : Q) * (a : Q)⁻¹)⁻¹ * (x : Q)
      rw [show (y : Q) = ⁅(a : Q), (x : Q)⁻¹⁆ from hyx, commutatorElement_def]
      group
    rw [← hyeq]
    exact hy
  have hfix := CFSG.PreuniquenessRankFour.Helpers.coprime_pGroup_action_trivial_of_frattini_trivial
    2 hA hcop htriv
  have hAC : A ≤ Subgroup.centralizer (R : Set Q) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : (a : Q) * x * (a : Q)⁻¹ = x := congrArg Subtype.val (hfix ⟨a, ha⟩ ⟨x, hx⟩)
    calc x * a = (a * x * a⁻¹) * a := by rw [h1]
      _ = a * x := by group
  set C : Subgroup Q := Subgroup.centralizer (R : Set Q) with hC
  haveI : Group.IsNilpotent (Q ⧸ R) := hQR.isNilpotent
  have hCnil : Group.IsNilpotent ↥C := by
    refine Subgroup.isNilpotent_of_ker_le_center ((QuotientGroup.mk' R).comp C.subtype) ?_
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcR : (c : Q) ∈ R := (QuotientGroup.eq_one_iff (c : Q)).mp hc
    rw [Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp d.2 (c : Q) hcR).symm
  have hA' : IsPGroup 2 (A.subgroupOf C) := hA.comap_subtype
  obtain ⟨P, hP⟩ := hA'.exists_le_sylow
  have hPle := Sylow.map_le_pCore (inferInstance : C.Normal) hCnil 2 P
  rw [hO2, le_bot_iff] at hPle
  refine (Subgroup.eq_bot_iff_forall A).mpr fun a ha => ?_
  have hmem : a ∈ (P : Subgroup ↥C).map C.subtype := ⟨⟨a, hAC ha⟩, hP ha, rfl⟩
  rw [hPle] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem uc22s21rb_inF_one_frattini {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {R : Subgroup Q}
    [R.Normal] (hR : IsPGroup q R) (hQR : IsPGroup 2 (Q ⧸ R)) (hO2 : CFSG.pCore 2 Q = ⊥)
    (hirr : ∀ N : Subgroup Q, N.Normal → N ≤ R → N ≤ (frattini ↥R).map R.subtype ∨ N = R) :
    F12.InF 1 (⊤ : Subgroup Q) :=
  uc22s21rb_inF_one hq hq2 hR hQR hirr fun _ hA hA2 hle =>
    hA (uc22s21rb_faith hq hq2 hR hQR hO2 hA2 hle)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
