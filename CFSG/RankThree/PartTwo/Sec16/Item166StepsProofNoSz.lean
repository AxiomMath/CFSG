module

public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.Monster.B.TwoA.Fischer.M22Aut
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank
open scoped Pointwise

@[expose] def KSL3PiNoSz : Prop :=
  ∀ (T : Type) [Group T], IsLThreePi T → ∀ (X : Subgroup (MulAut T)) (N : Subgroup X) [N.Normal]
    (p f : ℕ), ¬ CFSG.Blueprint.SuzukiModel (X ⧸ N) p f

namespace Steps166

section NoSzSection

@[expose] def NoSzSection (M : Type) [Group M] : Prop :=
  ∀ (X : Subgroup M) (N : Subgroup X) [N.Normal] (p f : ℕ),
    ¬ CFSG.Blueprint.SuzukiModel (X ⧸ N) p f

theorem noSzSection_of_injective {M M' : Type} [Group M] [Group M'] (φ : M →* M')
    (hφ : Function.Injective φ) (h : NoSzSection M') : NoSzSection M := by
  intro X N _ p f hSz
  set X' := X.map φ with hX'
  let e : X ≃* X' := X.equivMapOfInjective φ hφ
  set N' : Subgroup X' := N.map e.toMonoidHom with hN'
  have : N'.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have e' : X ⧸ N ≃* X' ⧸ N' := QuotientGroup.congr N N' e rfl
  exact h X' N' p f (suzukiModel_of_mulEquiv e'.symm hSz)

theorem noSzSection_of_card {M : Type} [Group M] [Finite M]
    (h13 : ¬ 13 ∣ Nat.card M) (h2 : ¬ 2 ^ 10 ∣ Nat.card M) : NoSzSection M :=
  fun X N _ _ _ => KFacts.KP7.not_suzukiModel_section h13 h2 X N

theorem noSzSection_mulAut_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : NoSzSection (MulAut T')) : NoSzSection (MulAut T) :=
  noSzSection_of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective h

theorem card_mulAut_alternatingGroup {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem noSzSection_mulAut_alt7 :
    NoSzSection (MulAut (alternatingGroup (Fin 7))) := by
  have h := card_mulAut_alternatingGroup (n := 7) (by norm_num) (by norm_num)
  refine noSzSection_of_card ?_ ?_ <;> rw [h] <;> decide

theorem noSzSection_mulAut_alt10 :
    NoSzSection (MulAut (alternatingGroup (Fin 10))) := by
  have h := card_mulAut_alternatingGroup (n := 10) (by norm_num) (by norm_num)
  refine noSzSection_of_card ?_ ?_ <;> rw [h] <;> decide

theorem noSzSection_mulAut_j2 :
    NoSzSection (MulAut CFSG.Blueprint.NativeSporadic.J2) := by
  have h :=
    (CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model).2.2.2.2.1
  have : Finite (MulAut CFSG.Blueprint.NativeSporadic.J2) := KFacts.KP7.finite_mulAut _
  refine noSzSection_of_card ?_ ?_ <;> rw [h] <;> norm_num

theorem noSzSection_mulAut_m22 :
    NoSzSection (MulAut CFSG.Blueprint.NativeSporadic.M22) := by
  have h := (CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order).1
  have : Finite (MulAut CFSG.Blueprint.NativeSporadic.M22) := KFacts.KP7.finite_mulAut _
  refine noSzSection_of_card ?_ ?_ <;> rw [h] <;> norm_num

end NoSzSection

section Cover

variable {G : Type} [Group G] [Finite G]

theorem nonempty_quot_center_mulEquiv_lBar {L Y : Subgroup G} (hLY : L ≤ Y)
    (hYeq : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hQ : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
      (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := ↥Y ⧸ CFSG.pCore 2 ↥Y with hQdef
  have : Group.IsPerfect Q := hQ.1
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  set f : ↥L →* Q := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY)
    with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) q
    have hy' : y ∈ ((L : Set G) * (CFSG.Open.pCoreOf 2 Y : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _
        (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)), ← hYeq]
      exact hy
    obtain ⟨l, hl, t, ht, hlt⟩ := hy'
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    rw [CFSG.Open.pCoreOf] at ht
    obtain ⟨t', ht', ht't⟩ := ht
    have : (Subgroup.inclusion hLY ⟨l, hl⟩)⁻¹ * ⟨y, hy⟩ = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hlt, ← ht't]
      simp
    rw [this]
    exact ht'
  set g : ↥L →* Q ⧸ Subgroup.center Q := (QuotientGroup.mk' (Subgroup.center Q)).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hfs
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  have hθsol : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hθker : θ ≤ g.ker := by
    have hnorm : (θ.map g).Normal := Subgroup.Normal.map inferInstance g hgs
    have hsolT : Group.IsSolvable (θ.map g) :=
      Group.isSolvable_of_surjective (g.subgroupMap_surjective θ)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (θ.map g) with h0 | h1
    · exact (Subgroup.map_eq_bot_iff _).mp h0
    · exfalso
      have : Group.IsSolvable (Q ⧸ Subgroup.center Q) := by
        rw [h1] at hsolT
        exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
          (MulEquiv.surjective _)
      exact Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.center Q) this
  set gbar := QuotientGroup.lift θ g hθker with hgbar
  have hgbs : Function.Surjective gbar := by
    intro x
    obtain ⟨l, rfl⟩ := hgs x
    exact ⟨(l : ↥L ⧸ θ), rfl⟩
  have hgbi : Function.Injective gbar := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal gbar.ker with h0 | h1
    · exact h0
    · exfalso
      obtain ⟨x, y, hxy⟩ := hQ.2.2
      apply hxy
      obtain ⟨x', rfl⟩ := hgbs x
      obtain ⟨y', rfl⟩ := hgbs y
      have hx' : gbar x' = 1 := by rw [← MonoidHom.mem_ker, h1]; exact Subgroup.mem_top _
      have hy' : gbar y' = 1 := by rw [← MonoidHom.mem_ker, h1]; exact Subgroup.mem_top _
      rw [hx', hy']
  exact ⟨(MulEquiv.ofBijective gbar ⟨hgbi, hgbs⟩).symm⟩

theorem noSzSection_of_cover {L Y : Subgroup G} (hLY : L ≤ Y)
    (hYeq : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hQ : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hT : NoSzSection (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    NoSzSection (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
  have : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hQ.1
  obtain ⟨e⟩ := nonempty_quot_center_mulEquiv_lBar hLY hYeq hQ hs
  exact noSzSection_of_injective _
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _)
    (noSzSection_mulAut_of_mulEquiv e hT)

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {T : Type} [Group T]
    (hq : CFSG.IsQuasisimple T) (hc : Subgroup.center T = ⊥) : IsSimpleGroup T := by
  have : IsSimpleGroup (T ⧸ Subgroup.center T) := hq.2.1
  have e : T ⧸ Subgroup.center T ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem center_eq_bot_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : Subgroup.center T' = ⊥) : Subgroup.center T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center T' := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hx'
  rw [hx', Subgroup.mem_bot]

theorem not_isSolvable_of_isQuasisimple {T : Type} [Group T] (hq : CFSG.IsQuasisimple T) :
    ¬ Group.IsSolvable T := by
  intro hsol
  have : Group.IsPerfect T := hq.1
  obtain ⟨x, y, hxy⟩ := hq.2.2
  have : Nontrivial (T ⧸ Subgroup.center T) := by
    refine ⟨⟨x * y, y * x, hxy⟩⟩
  have : Group.IsSolvable (T ⧸ Subgroup.center T) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center T))
  exact Group.IsPerfect.not_isSolvable (T ⧸ Subgroup.center T) this

theorem isSimpleGroup_of_isLThreePi {T : Type} [Group T] (hq : CFSG.IsQuasisimple T)
    (hT : IsLThreePi T) : IsSimpleGroup T := by
  obtain ⟨p, e, hp, he, hiso⟩ := hT
  rcases hiso with ⟨hmod, ⟨φ⟩⟩ | ⟨hmod, ⟨φ⟩⟩
  · exact isSimpleGroup_of_isQuasisimple_of_center_eq_bot hq
      (center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he hmod).2)
  · by_cases hq2 : 2 < p ^ e
    · exact isSimpleGroup_of_isQuasisimple_of_center_eq_bot hq
        (center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he hmod hq2).2)
    · exfalso
      have hp2 : p = 2 ∧ e = 1 := by
        have h1 : p ≤ p ^ e := Nat.le_self_pow (by omega) p
        have h2 := hp.out.two_le
        have hpe : p = 2 := by omega
        subst hpe
        refine ⟨rfl, ?_⟩
        by_contra hne
        have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨rfl, rfl⟩ := hp2
      have hsol := isSolvable_projSU_two
      exact not_isSolvable_of_isQuasisimple hq
        (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)

end Cover

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem noSz166_of_item1514
    (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀)
    (hL3 : KSL3PiNoSz) : NoSz166 Y₀ := by
  have hQ : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := h.mem_y0Star.prop.1.2.2.2
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  rcases h1514 Y₀ h.mem_y0Star hMeets with
    ⟨hY, -, -, -, hM12⟩ | ⟨-, -, -, hY7 | hY10⟩ | ⟨-, -, -, -, hno, -⟩
  ·
    rw [inf_eq_right.mpr h.le_y0] at hY
    rcases (h.hypR.2.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with
      hJ | hL3' | h7 | h22 | h12
    · obtain ⟨eJ⟩ := hJ
      have hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
        @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 eJ
      exact noSzSection_of_cover h.le_y0 hY hQ hs
        (noSzSection_mulAut_of_mulEquiv eJ noSzSection_mulAut_j2)
    · exact noSzSection_of_cover h.le_y0 hY hQ (isSimpleGroup_of_isLThreePi hLq hL3')
        (fun X N _ p f => hL3 _ hL3' X N p f)
    · obtain ⟨e7⟩ := h7
      have hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
        isSimpleGroup_of_isQuasisimple_of_center_eq_bot hLq
          (center_eq_bot_of_mulEquiv e7 isPerfect_center_alt7.2)
      exact noSzSection_of_cover h.le_y0 hY hQ hs
        (noSzSection_mulAut_of_mulEquiv e7 noSzSection_mulAut_alt7)
    · obtain ⟨e22⟩ := h22
      have hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
        @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2 e22
      exact noSzSection_of_cover h.le_y0 hY hQ hs
        (noSzSection_mulAut_of_mulEquiv e22 noSzSection_mulAut_m22)
    · obtain ⟨e12⟩ := h12
      exact (hM12.false e12).elim
  ·
    obtain ⟨e⟩ := hY7
    exact noSzSection_mulAut_of_mulEquiv e noSzSection_mulAut_alt7
  ·
    obtain ⟨e⟩ := hY10
    exact noSzSection_mulAut_of_mulEquiv e noSzSection_mulAut_alt10
  ·
    exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

end Main

end Steps166

theorem step166NoSz_of
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hL3 : KSL3PiNoSz) : Step166NoSz :=
  fun G _ _ A c L Y₀ h =>
    Steps166.noSz166_of_item1514 h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h) hL3

end CFSG.RankThree.PartTwo.Sec16
