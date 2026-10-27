module

public import CFSG.RankThree.PartTwo.Sec19.Step1919CoreCount
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.KFacts.KS14GL33
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

namespace Item19Res4Proof

section Inner

variable {X : Type} [Group X]

theorem not_injective_of_isTripleA6 [Finite X] [Group.IsPerfect X] (h : IsTripleA6 X)
    {E : Type*} [Group E] (hE : Nat.card E = 27) (hEe : ∀ e : E, e ^ 3 = 1)
    (φ : E →* MulAut X) : ¬ Function.Injective φ := by
  intro hφ
  have hcard := card_eq_of_isTripleA6 h
  have hle : φ.range ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨y, hy⟩ := exists_eq_conj_of_isTripleA6 h (φ e) (by rw [← map_pow, hEe, map_one])
    exact ⟨y, hy.symm⟩
  have h27 : Nat.card φ.range = 27 := by
    rw [← hE]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have hZk : Subgroup.center X ≤ (MulAut.conj : X →* MulAut X).ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hz x,
      mul_inv_cancel_right]
  have h3 : 3 ∣ Nat.card (MulAut.conj : X →* MulAut X).ker := by
    rw [← h.1]
    exact Subgroup.card_dvd_of_le hZk
  have hprod : Nat.card (MulAut.conj : X →* MulAut X).range *
      Nat.card (MulAut.conj : X →* MulAut X).ker = 1080 := by
    rw [← hcard, ((MulAut.conj : X →* MulAut X).ker).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
  have h27' : 27 ∣ Nat.card (MulAut.conj : X →* MulAut X).range := by
    rw [← h27]
    exact Subgroup.card_dvd_of_le hle
  have h81 := Nat.mul_dvd_mul h27' h3
  rw [hprod] at h81
  omega

end Inner

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isProperParabolic_of_isTripleA6 {J H : Subgroup G}
    (htriple : IsTripleA6 (J ⧸ CFSG.pCore 2 J))
    (hpar : (IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        IsProperParabolic (starIm J H)) ∨
      (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2)))) :
    IsProperParabolic (starIm J H) := by
  rcases hpar with ⟨-, h⟩ | ⟨⟨e⟩, -⟩
  · exact h
  · exfalso
    have h1 := card_eq_of_isTripleA6 htriple
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
    exact absurd h1 (by decide)

theorem exists_fixed_noncentral_triple {M J H A : Subgroup G} (hJM : J ∈ oTwoComponentsIn M)
    (htriple : IsTripleA6 (J ⧸ CFSG.pCore 2 J)) (hpar : IsProperParabolic (starIm J H))
    (hA3 : IsPGroup 3 A) (hAe : ∀ a ∈ A, a ^ 3 = 1)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hAH : A ≤ H) :
    ∃ y : J, (y : G) ^ 3 = 1 ∧ (∀ a ∈ A, a * y = (y : G) * a) ∧
      (y : J ⧸ CFSG.pCore 2 J) ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
  have hperfJ : Group.IsPerfect (J ⧸ CFSG.pCore 2 J) :=
    (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hJM).1
  have hW3 : ∀ w ∈ (Step1910Proof.quotAct hAJ).range, w ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha : a ^ 3 = 1 := Subtype.ext (by simpa using hAe a a.2)
    rw [← map_pow, ha, map_one]
  have hWP : ∀ w ∈ (Step1910Proof.quotAct hAJ).range, ∀ p ∈ starIm J H, w p ∈ starIm J H := by
    rintro _ ⟨a, rfl⟩ _ ⟨j, hjH, rfl⟩
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hAJ a j
    refine ⟨j', Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [hj']
      exact H.mul_mem (H.mul_mem (hAH a.2) (Subgroup.mem_subgroupOf.mp hjH))
        (H.inv_mem (hAH a.2))
    · exact hact.symm
  obtain ⟨x, hx3, hxc, hxf⟩ := exists_fixed_of_isTripleA6 htriple _ hW3 _ hpar hWP
  exact Step1910Proof.exists_lift_of_fixed hA3 hAJ (fun a => hxf _ ⟨a, rfl⟩) hx3 hxc

theorem exists_fixed_noncentral_wide3
    {M J H A : Subgroup G} (hJM : J ∈ oTwoComponentsIn M)
    (hlist : IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J) ∨
      IsTripleA6 (J ⧸ CFSG.pCore 2 J))
    (hpar : (IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        IsProperParabolic (starIm J H)) ∨
      (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))
    (hA3 : IsPGroup 3 A) (hAe : ∀ a ∈ A, a ^ 3 = 1)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hAH : A ≤ H) :
    ∃ y : J, (y : G) ^ 3 = 1 ∧ (∀ a ∈ A, a * y = (y : G) * a) ∧
      (y : J ⧸ CFSG.pCore 2 J) ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
  rcases hlist with h | h | htriple
  · exact Step1919NarrowTools.exists_fixed_noncentral hJM (Or.inl h) hpar hA3 hAe hAJ hAH
  · exact Step1919NarrowTools.exists_fixed_noncentral hJM (Or.inr h) hpar hA3 hAe hAJ hAH
  · exact exists_fixed_noncentral_triple hJM htriple
      (isProperParabolic_of_isTripleA6 htriple hpar) hA3 hAe hAJ hAH

open Step1919Narrow in
theorem le_normalizer_of_mem_scriptJ_wide3
    (h194 : Item194UsedWide3) {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {H : Subgroup G} (hH : H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G))
    (hHM : H ≠ M) {J : Subgroup G} (hJ : J ∈ scriptJ M H) :
    E ≤ Subgroup.normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hE3 : IsPGroup 3 E := hE.isPGroup
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1
  have hJM : J ∈ oTwoComponentsIn M := hJ.1
  have hJMle : J ≤ M := le_of_mem_oTwoComponentsIn hJM
  obtain ⟨-, hJall⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  obtain ⟨hlist, hpar⟩ := hJall J hJ
  have hperfJ : Group.IsPerfect (J ⧸ CFSG.pCore 2 J) :=
    (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hJM).1
  obtain ⟨xb, hxb3, hxbc⟩ : ∃ x : J ⧸ CFSG.pCore 2 J, x ^ 3 = 1 ∧
      x ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
    rcases hlist with h | h | h
    · exact Step1910Proof.exists_noncentral_of_isList194_wide (Or.inl h) hperfJ
    · exact Step1910Proof.exists_noncentral_of_isList194_wide (Or.inr h) hperfJ
    · exact exists_noncentral_of_isTripleA6 h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hx3 : (x : G) ^ 3 ∈ Q := pow_three_mem_of_mk hJM x hxb3
  have hxnc := exists_not_mem_of_not_mem_center hJM x hxbc
  have hxM : (x : G) ∈ M := hJMle x.2
  by_contra hne
  obtain ⟨e, heE, heJ⟩ := Set.not_subset.mp hne
  have heM : e ∈ M := hEM heE
  have heeM : e * e ∈ M := M.mul_mem heM heM
  set J₁ := J.map (MulAut.conj e).toMonoidHom with hJ₁
  set J₂ := J.map (MulAut.conj (e * e)).toMonoidHom with hJ₂
  have hJ₁M : J₁ ∈ oTwoComponentsIn M := Sec18.map_conj_mem_oTwoComponentsIn hJM heM
  have hJ₂M : J₂ ∈ oTwoComponentsIn M := Sec18.map_conj_mem_oTwoComponentsIn hJM heeM
  obtain ⟨hJJ₁, hJJ₂, hJ₁J₂⟩ := map_conj_ne (hEe e heE) heJ
  have hJ₁le : J₁ ≤ M := le_of_mem_oTwoComponentsIn hJ₁M
  have hJ₂le : J₂ ≤ M := le_of_mem_oTwoComponentsIn hJ₂M
  have hxe : e * x * e⁻¹ ∈ J₁ := ⟨x, x.2, rfl⟩
  have hxee : (e * e) * x * (e * e)⁻¹ ∈ J₂ := ⟨x, x.2, rfl⟩
  have hxeM : e * x * e⁻¹ ∈ M := hJ₁le hxe
  have hxeeM : (e * e) * x * (e * e)⁻¹ ∈ M := hJ₂le hxee
  have hcm := @Step1910Proof.commutator_mem_pCoreOf G _ _ M
  suffices h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G by
    rw [hst.toTheoremFourHyp.localRank_three] at h4
    omega
  by_cases h4c : ∃ g ∈ E, J.map (MulAut.conj g).toMonoidHom ≠ J ∧
      J.map (MulAut.conj g).toMonoidHom ≠ J₁ ∧ J.map (MulAut.conj g).toMonoidHom ≠ J₂
  ·
    obtain ⟨g, hgE, hg0, hg1, hg2⟩ := h4c
    have hgM : g ∈ M := hEM hgE
    set J₃ := J.map (MulAut.conj g).toMonoidHom with hJ₃
    have hJ₃M : J₃ ∈ oTwoComponentsIn M := Sec18.map_conj_mem_oTwoComponentsIn hJM hgM
    have hxg : g * x * g⁻¹ ∈ J₃ := ⟨x, x.2, rfl⟩
    exact Step1919NarrowTools.four_le_localRank_of_components hQ
      ⟨g * x * g⁻¹, le_of_mem_oTwoComponentsIn hJ₃M hxg⟩ ⟨x, hxM⟩ ⟨_, hxeM⟩ ⟨_, hxeeM⟩
      (hcm hJ₃M hJM hg0 hxg x.2) (hcm hJ₃M hJ₁M hg1 hxg hxe) (hcm hJ₃M hJ₂M hg2 hxg hxee)
      (hcm hJM hJ₁M hJJ₁ x.2 hxe) (hcm hJM hJ₂M hJJ₂ x.2 hxee) (hcm hJ₁M hJ₂M hJ₁J₂ hxe hxee)
      (conj_pow_three_mem hgM hx3) hx3 (conj_pow_three_mem heM hx3)
      (conj_pow_three_mem heeM hx3)
      (not_mem_of_exists_not_mem (le_of_mem_oTwoComponentsIn hJ₃M)
        (conj_exists_not_mem hgM hxnc))
      hJMle hJ₁le hJ₂le (fun k hk => hcm hJ₃M hJM hg0 hxg hk) hxnc
      (fun k hk => hcm hJ₃M hJ₁M hg1 hxg hk) (fun k hk => hcm hJM hJ₁M hJJ₁ x.2 hk)
      (conj_exists_not_mem heM hxnc) (fun k hk => hcm hJ₃M hJ₂M hg2 hxg hk)
      (fun k hk => hcm hJM hJ₂M hJJ₂ x.2 hk) (fun k hk => hcm hJ₁M hJ₂M hJ₁J₂ hxe hk)
      (conj_exists_not_mem heeM hxnc)
  push Not at h4c
  have horb : ∀ g ∈ E, J.map (MulAut.conj g).toMonoidHom = J ∨
      J.map (MulAut.conj g).toMonoidHom = J₁ ∨ J.map (MulAut.conj g).toMonoidHom = J₂ := by
    intro g hg
    by_cases h0 : J.map (MulAut.conj g).toMonoidHom = J
    · exact Or.inl h0
    by_cases h1 : J.map (MulAut.conj g).toMonoidHom = J₁
    · exact Or.inr (Or.inl h1)
    exact Or.inr (Or.inr (h4c g hg h0 h1))
  set E₀ := E ⊓ Subgroup.normalizer (J : Set G) with hE₀
  have hE₀9 : 9 ≤ Nat.card E₀ := by
    set f : E₀ × Fin 3 → E := fun p =>
      ⟨e ^ (p.2 : ℕ) * (p.1 : G), E.mul_mem (E.pow_mem heE _) p.1.2.1⟩ with hf
    have hfs : Function.Surjective f := by
      rintro ⟨g, hg⟩
      have hback : ∀ b : G, J.map (MulAut.conj g).toMonoidHom = J.map (MulAut.conj b).toMonoidHom →
          b⁻¹ * g ∈ Subgroup.normalizer (J : Set G) := by
        intro b hb
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have h1 := congrArg (Subgroup.map (MulAut.conj b⁻¹).toMonoidHom) hb
        rw [Step199Proof.map_conj_map_conj, Step199Proof.map_conj_map_conj, inv_mul_cancel,
          Step199Proof.map_conj_one] at h1
        exact h1
      rcases horb g hg with h0 | h1 | h2
      · refine ⟨(⟨g, hg, ?_⟩, 0), ?_⟩
        · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h0
        · apply Subtype.ext
          simp [hf]
      · refine ⟨(⟨e⁻¹ * g, E.mul_mem (E.inv_mem heE) hg, hback e h1⟩, 1), ?_⟩
        apply Subtype.ext
        simp [hf]
      · refine ⟨(⟨(e * e)⁻¹ * g, E.mul_mem (E.inv_mem (E.mul_mem heE heE)) hg,
          hback (e * e) h2⟩, 2), ?_⟩
        apply Subtype.ext
        simp only [hf]
        rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_two]
        group
    have h1 := Nat.card_le_card_of_surjective f hfs
    rw [Nat.card_prod, Nat.card_fin, hE.2] at h1
    omega
  have hE₀3 : IsPGroup 3 E₀ := hE3.to_le inf_le_left
  have hE₀e : ∀ a ∈ E₀, a ^ 3 = 1 := fun a ha => hEe a ha.1
  have hE₀J : E₀ ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hE₀H : E₀ ≤ H := inf_le_left.trans hEH
  have hwe : ∀ w ∈ E₀, w * e = e * w := fun w hw => hEc w hw.1 e heE
  have hwee : ∀ w ∈ E₀, w * (e * e) = (e * e) * w := fun w hw =>
    hEc w hw.1 _ (E.mul_mem heE heE)
  by_cases hfaith : ∃ w ∈ E₀, w ≠ 1 ∧ ∀ j ∈ J, w * j * w⁻¹ * j⁻¹ ∈ Q
  ·
    obtain ⟨w, hwE₀, hw1, hwJ⟩ := hfaith
    have hwM : w ∈ M := hEM hwE₀.1
    have hwJ₁ := conj_forall_mem heM (hwe w hwE₀) hwJ
    have hwJ₂ := conj_forall_mem heeM (hwee w hwE₀) hwJ
    have hw3 : w ^ 3 ∈ Q := by rw [hEe w hwE₀.1]; exact Q.one_mem
    exact Step1919NarrowTools.four_le_localRank_of_components hQ ⟨w, hwM⟩ ⟨x, hxM⟩
      ⟨_, hxeM⟩ ⟨_, hxeeM⟩ (hwJ _ x.2) (hwJ₁ _ hxe) (hwJ₂ _ hxee)
      (hcm hJM hJ₁M hJJ₁ x.2 hxe) (hcm hJM hJ₂M hJJ₂ x.2 hxee) (hcm hJ₁M hJ₂M hJ₁J₂ hxe hxee)
      hw3 hx3 (conj_pow_three_mem heM hx3) (conj_pow_three_mem heeM hx3)
      (not_mem_pCoreOf_of_pow_three (hEe w hwE₀.1) hw1) hJMle hJ₁le hJ₂le hwJ hxnc hwJ₁
      (fun k hk => hcm hJM hJ₁M hJJ₁ x.2 hk) (conj_exists_not_mem heM hxnc) hwJ₂
      (fun k hk => hcm hJM hJ₂M hJJ₂ x.2 hk) (fun k hk => hcm hJ₁M hJ₂M hJ₁J₂ hxe hk)
      (conj_exists_not_mem heeM hxnc)
  push Not at hfaith
  obtain ⟨y, hy3, hyA, hyc⟩ := exists_fixed_noncentral_wide3 hJM hlist hpar
    hE₀3 hE₀e hE₀J hE₀H
  have hync := exists_not_mem_of_not_mem_center hJM y hyc
  have hy3Q : (y : G) ^ 3 ∈ Q := by rw [hy3]; exact Q.one_mem
  have hye : e * y * e⁻¹ ∈ J₁ := ⟨y, y.2, rfl⟩
  have hyee : (e * e) * y * (e * e)⁻¹ ∈ J₂ := ⟨y, y.2, rfl⟩
  have hyeM : e * y * e⁻¹ ∈ M := hJ₁le hye
  have hyeeM : (e * e) * y * (e * e)⁻¹ ∈ M := hJ₂le hyee
  have hE₀ne : E₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE₀9
    omega
  obtain ⟨⟨w₁, hw₁⟩, hw₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE₀ne
  have hw₁1' : w₁ ≠ 1 := fun h => hw₁1 (Subtype.ext h)
  have hw₁o : orderOf w₁ = 3 := orderOf_eq_prime (hE₀e w₁ hw₁) hw₁1'
  obtain ⟨w₂, hw₂, hw₂n⟩ : ∃ w₂ ∈ E₀, w₂ ∉ Subgroup.zpowers w₁ := by
    by_contra hall
    push Not at hall
    have hle : E₀ ≤ Subgroup.zpowers w₁ := hall
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hw₁o] at h1
    omega
  have hw₁M : w₁ ∈ M := hEM hw₁.1
  have hw₂M : w₂ ∈ M := hEM hw₂.1
  have hcomm_conj : ∀ w ∈ E₀, ∀ b ∈ E, w * (b * y * b⁻¹) = (b * y * b⁻¹) * w := by
    intro w hw b hb
    have h1 : Commute w b := hEc w hw.1 b hb
    have h2 : Commute w (y : G) := hyA w hw
    exact ((h1.mul_right h2).mul_right h1.inv_right).eq
  have hcomm_Q : ∀ {a b : G}, a * b = b * a → a * b * a⁻¹ * b⁻¹ ∈ Q := by
    intro a b hab
    rw [hab, mul_inv_cancel_right, mul_inv_cancel]
    exact Q.one_mem
  set π := QuotientGroup.mk' (CFSG.pCore 2 M) with hπ
  set CJ := Subgroup.centralizer ((J.subgroupOf M).map π : Set (M ⧸ CFSG.pCore 2 M)) with hCJ
  have hcomm_mk : ∀ (a b : M), (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ Q → π a * π b = π b * π a :=
    fun a b h => (Step1919NarrowTools.mk_mul_comm_iff a b).mpr h
  have hcube : ∀ (a : M), (a : G) ^ 3 ∈ Q → π a ^ 3 = 1 := fun a h =>
    Step1919NarrowTools.mk_pow_three a h
  have hcen : ∀ {K : Subgroup G} (hK : K ≤ M) (a : M),
      (∀ k ∈ K, (a : G) * k * (a : G)⁻¹ * k⁻¹ ∈ Q) →
      π a ∈ Subgroup.centralizer ((K.subgroupOf M).map π : Set (M ⧸ CFSG.pCore 2 M)) :=
    fun hK a h => (Step1919NarrowTools.mk_mem_centralizer_iff hK a).mpr h
  have hncen : ∀ {K : Subgroup G} (hK : K ≤ M) (a : M),
      (∃ k ∈ K, (a : G) * k * (a : G)⁻¹ * k⁻¹ ∉ Q) →
      π a ∉ Subgroup.centralizer ((K.subgroupOf M).map π : Set (M ⧸ CFSG.pCore 2 M)) := by
    intro K hK a ⟨k, hk, hak⟩ h
    exact hak ((Step1919NarrowTools.mk_mem_centralizer_iff hK a).mp h k hk)
  set v₁ := π ⟨_, hyeM⟩ with hv₁
  set v₂ := π ⟨_, hyeeM⟩ with hv₂
  set v₃ := π ⟨w₁, hw₁M⟩ with hv₃
  set v₄ := π ⟨w₂, hw₂M⟩ with hv₄
  have hv₁C : Subgroup.zpowers v₁ ≤ CJ :=
    Subgroup.zpowers_le.mpr (hcen hJMle _ fun k hk => hcm hJ₁M hJM (Ne.symm hJJ₁) hye hk)
  have hv₂C : Subgroup.zpowers v₂ ≤ CJ :=
    Subgroup.zpowers_le.mpr (hcen hJMle _ fun k hk => hcm hJ₂M hJM (Ne.symm hJJ₂) hyee hk)
  have hw₁3 : w₁ ^ 3 ∈ Q := by rw [hEe w₁ hw₁.1]; exact Q.one_mem
  have hw₂3 : w₂ ^ 3 ∈ Q := by rw [hEe w₂ hw₂.1]; exact Q.one_mem
  refine Step1919NarrowRank.four_le_localRank_of_chain (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
    (v₄ := v₄) hQ
    (hcomm_mk ⟨_, hyeM⟩ ⟨_, hyeeM⟩ (hcm hJ₁M hJ₂M hJ₁J₂ hye hyee))
    (hcomm_mk ⟨_, hyeM⟩ ⟨w₁, hw₁M⟩ (hcomm_Q (hcomm_conj w₁ hw₁ e heE).symm))
    (hcomm_mk ⟨_, hyeM⟩ ⟨w₂, hw₂M⟩ (hcomm_Q (hcomm_conj w₂ hw₂ e heE).symm))
    (hcomm_mk ⟨_, hyeeM⟩ ⟨w₁, hw₁M⟩
      (hcomm_Q (hcomm_conj w₁ hw₁ _ (E.mul_mem heE heE)).symm))
    (hcomm_mk ⟨_, hyeeM⟩ ⟨w₂, hw₂M⟩
      (hcomm_Q (hcomm_conj w₂ hw₂ _ (E.mul_mem heE heE)).symm))
    (hcomm_mk ⟨w₁, hw₁M⟩ ⟨w₂, hw₂M⟩ (hcomm_Q (hEc w₁ hw₁.1 w₂ hw₂.1)))
    (hcube ⟨_, hyeM⟩ (conj_pow_three_mem heM hy3Q))
    (hcube ⟨_, hyeeM⟩ (conj_pow_three_mem heeM hy3Q))
    (hcube ⟨w₁, hw₁M⟩ hw₁3) (hcube ⟨w₂, hw₂M⟩ hw₂3) ?_ ?_ ?_ ?_
  ·
    intro h
    have h1 : (⟨_, hyeM⟩ : M) ∈ CFSG.pCore 2 M := by
      rw [← QuotientGroup.eq_one_iff]
      exact h
    rw [Step1911EndProof.mem_pCore_iff] at h1
    exact not_mem_of_exists_not_mem hJ₁le (conj_exists_not_mem heM hync) h1
  ·
    intro h
    have h1 := Subgroup.zpowers_le.mpr (hcen hJ₂le ⟨_, hyeM⟩
      fun k hk => hcm hJ₁M hJ₂M hJ₁J₂ hye hk) h
    exact hncen hJ₂le ⟨_, hyeeM⟩ (conj_exists_not_mem heeM hync) h1
  ·
    intro h
    exact hncen hJMle ⟨w₁, hw₁M⟩ (hfaith w₁ hw₁ hw₁1') (sup_le hv₁C hv₂C h)
  ·
    intro h
    have hN : Subgroup.zpowers v₃ ≤ Subgroup.normalizer (CJ : Set (M ⧸ CFSG.pCore 2 M)) :=
      Subgroup.zpowers_le.mpr (mem_normalizer_centralizer
        (mk_mem_normalizer_map ⟨w₁, hw₁M⟩ (hE₀J hw₁)))
    have hle : Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ ⊔ Subgroup.zpowers v₃ ≤
        Subgroup.zpowers v₃ ⊔ CJ :=
      sup_le (sup_le (hv₁C.trans le_sup_right) (hv₂C.trans le_sup_right)) le_sup_left
    have h' := hle h
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at h'
    obtain ⟨a, ha, cc, hcc, hac⟩ := h'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hwk : w₁ ^ (-k) * w₂ ∈ M := M.mul_mem (M.zpow_mem hw₁M _) hw₂M
    have hcc' : π ⟨w₁ ^ (-k) * w₂, hwk⟩ = cc := by
      have e1 : (⟨w₁ ^ (-k) * w₂, hwk⟩ : M) = (⟨w₁, hw₁M⟩ : M) ^ (-k) * ⟨w₂, hw₂M⟩ :=
        Subtype.ext (by simp)
      rw [e1, map_mul, map_zpow, ← hv₃, ← hv₄, ← hac, zpow_neg, inv_mul_cancel_left]
    have hcen' := (Step1919NarrowTools.mk_mem_centralizer_iff hJMle _).mp (hcc' ▸ hcc)
    have hwk1 : w₁ ^ (-k) * w₂ = 1 := by
      by_contra hne'
      obtain ⟨j, hj, hjn⟩ := hfaith _ (E₀.mul_mem (E₀.zpow_mem hw₁ _) hw₂) hne'
      exact hjn (hcen' j hj)
    apply hw₂n
    have : w₂ = w₁ ^ k := by
      rw [zpow_neg, inv_mul_eq_one] at hwk1
      exact hwk1.symm
    rw [this]
    exact Subgroup.zpow_mem_zpowers w₁ k

open Step1919Narrow in
theorem exists_commutator_not_mem_of_mem_scriptJ_wide3
    (h194 : Item194UsedWide3) {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {H : Subgroup G} (hH : H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G))
    (hHM : H ≠ M) {J : Subgroup G} (hJ : J ∈ scriptJ M H) :
    ∃ j ∈ J, c * j * c⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E := mem_of_le_centralizer hst hctx.partTwoS_eq hEE
    (hctx.mem_partTwoE.1.2 c hcA) hctx.le_centralizer
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  have hJM : J ∈ oTwoComponentsIn M := hJ.1
  obtain ⟨-, hJall⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  obtain ⟨-, hpar⟩ := hJall J hJ
  have hcN : c ∈ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_mem_scriptJ_wide3 h194 hctx hH hHM hJ hcE
  by_contra hall
  push Not at hall
  set O := CFSG.Open.pCoreOf 2 J with hO
  have hOJ : O ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  set B := Subgroup.zpowers c with hB
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hB, Nat.card_zpowers, hc3]; rfl)
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := Subgroup.zpowers_le.mpr hcN
  have hBO : B ≤ Subgroup.normalizer (O : Set G) :=
    hBJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hact1 : Step1910Proof.quotAct hBJ ⟨c, Subgroup.mem_zpowers c⟩ = 1 := by
    ext q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hBJ ⟨c, Subgroup.mem_zpowers c⟩ k
    rw [hact, MulAut.one_apply]
    apply QuotientGroup.eq.mpr
    rw [Step1911EndProof.mem_pCore_iff]
    have hckJ : c * k * c⁻¹ * (k : G)⁻¹ ∈ J :=
      J.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN k).mp k.2) (J.inv_mem k.2)
    have h1 : c * k * c⁻¹ * (k : G)⁻¹ ∈ O :=
      Step1910Proof.inf_pCoreOf_le hJM ⟨hckJ, hall k k.2⟩
    have hkN : (k : G) ∈ Subgroup.normalizer (O : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J k.2
    have h2 := (Subgroup.mem_normalizer_iff.mp hkN _).mpr
      (show (k : G) * ((j' : G)⁻¹ * k) * (k : G)⁻¹ ∈ O by
        rw [hj', show (k : G) * ((c * k * c⁻¹)⁻¹ * k) * (k : G)⁻¹ =
          (c * k * c⁻¹ * (k : G)⁻¹)⁻¹ by group]
        exact inv_mem h1)
    simpa using h2
  have hBK : ∀ b ∈ B, ∀ k ∈ J, k⁻¹ * (b * k * b⁻¹) ∈ O := by
    intro b hb k hk
    have hall' : Step1910Proof.quotAct hBJ ⟨b, hb⟩ = 1 := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
      have e1 : (⟨b, hb⟩ : B) = (⟨c, Subgroup.mem_zpowers c⟩ : B) ^ n :=
        Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
      rw [e1, map_zpow, hact1, one_zpow]
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hBJ ⟨b, hb⟩ ⟨k, hk⟩
    rw [hall', MulAut.one_apply] at hact
    have h1 : (⟨k, hk⟩ : J)⁻¹ * j' ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp hact
    rw [Step1911EndProof.mem_pCore_iff] at h1
    simpa [hj'] using h1
  have hcov := Step199Proof.le_inf_centralizer_sup hOJ hB3 hO3 hBO hBK
  have htop : starIm J H = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk := hcov k.2
    have hNle : J ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (O : Set G) :=
      inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNle] at hk
    obtain ⟨a, ha, n, hn, han⟩ := hk
    have haH : a ∈ H := hH.2 (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)) ha.2)
    refine ⟨⟨a, ha.1⟩, Subgroup.mem_subgroupOf.mpr haH, ?_⟩
    change ((⟨a, ha.1⟩ : J) : J ⧸ CFSG.pCore 2 J) = (k : J ⧸ CFSG.pCore 2 J)
    apply QuotientGroup.eq.mpr
    rw [Step1911EndProof.mem_pCore_iff]
    have : ((⟨a, ha.1⟩ : J)⁻¹ * k : J) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← han]
      group
    rw [this]
    exact hn
  rcases hpar with ⟨-, hpp⟩ | ⟨⟨eA⟩, hext⟩
  · exact hpp.1 htop
  · have hcard : Nat.card (starIm J H) = 1920 := by
      obtain ⟨N, hN, hN1, hN2⟩ := hext
      obtain ⟨eN⟩ := hN1
      obtain ⟨eQ⟩ := hN2
      rw [N.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr eQ.toEquiv,
        Nat.card_congr eN.toEquiv, Nat.card_perm, Nat.card_fin,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ _),
        Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      decide
    rw [htop, Subgroup.card_top, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin] at hcard
    exact absurd hcard (by decide)

theorem false_of_isTripleA6_of_mem_scriptJ {A L E M H J : Subgroup G} {c : G}
    (hctx : Ctx1912 G A c L E M) (h9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (hX : Sec4.IsExtOf
      (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hH : H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G)) (hJ : J ∈ scriptJ M H)
    (htriple : IsTripleA6 (J ⧸ CFSG.pCore 2 J)) (hpar : IsProperParabolic (starIm J H))
    (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hcJ : ∃ j ∈ J, c * j * c⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  set F := E ⊓ L with hFdef
  have hFE : F ≤ E := inf_le_left
  have hFN : Subgroup.normalizer (F : Set G) ≤ M :=
    (normalizer_le_gamma hFE (two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hFE)
      h9.ge)).trans hctx.mem_scriptM.2
  have hJM : J ∈ oTwoComponentsIn M := hJ.1
  have hperfJ : Group.IsPerfect (J ⧸ CFSG.pCore 2 J) :=
    (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hJM).1
  obtain ⟨y, hy3, hyc, hync⟩ :=
    exists_fixed_noncentral_triple hJM htriple hpar hE.isPGroup hEe hEJ hEH
  have hyE : (y : G) ∈ E := mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
    hy3 fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hyc a ha)
  have hyn := Step1919Narrow.exists_not_mem_of_not_mem_center hJM y hync
  have hcE : c ∈ E :=
    mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
      (hctx.mem_partTwoE.1.2 c (hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)))
      hctx.le_centralizer
  obtain ⟨u, huE, huF, hu3, hufix, hcu⟩ :=
    Step1919CoreProof.exists_transvection KFacts.KS14.ks18GL33 hctx h9 hX
  have hue : ∃ e ∈ E, u * e * u⁻¹ ≠ e := ⟨c, hcE, fun h => hcu (by
    calc c * u = u * c * u⁻¹ * u := by rw [h]
      _ = u * c := by group)⟩
  have hP3 : ∀ g ∈ Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G),
      (∃ k : ℕ, g ^ 3 ^ k = 1) → g ∈ Subgroup.normalizer (J : Set G) := fun g hg hg3 =>
    Step1919CoreProof.mem_normalizer_of_pow hEc hEe hE.2 hFE h9 hJM hyE y.2 hyn (hFN huF) huE
      hu3 hufix hue (hFN hg.1) hg.2 hg3
  have hy1 : (y : G) ≠ 1 := fun h =>
    Step1919CoreProof.not_mem_cenMod hyn (h ▸ Subgroup.one_mem _)
  have hV1 : E ⊓ J ≠ ⊥ := fun h => hy1 ((Subgroup.mem_bot).mp (h ▸ ⟨hyE, y.2⟩))
  have hEJF : E ⊓ J = F := by
    rcases Step1919CoreProof.eq_or_eq_of_conj_mem hctx h9 hX inf_le_left hV1
        (fun z hz hz3 v hv => ⟨(Subgroup.mem_normalizer_iff.mp hz.2 v).mp hv.1,
          (Subgroup.mem_normalizer_iff.mp (hP3 z hz hz3) v).mp hv.2⟩) with h | h
    · exact h
    · exfalso
      have hEJ' : E ≤ J := h ▸ inf_le_right
      exact card_ne_twentySeven_of_isTripleA6 htriple (starIm J E)
        (Step1919EndProof.isElemAbelian_starIm hE.1)
        ((Step1919EndProof.card_starIm hE.isPGroup hEJ').trans hE.2)
  have hyF : (y : G) ∈ F := hEJF ▸ ⟨hyE, y.2⟩
  set V := E ⊓ Step1919CoreProof.cenMod M J with hVdef
  have hV : V = ⊥ := by
    by_contra hV1
    have hinv : ∀ z ∈ Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G),
        (∃ k : ℕ, z ^ 3 ^ k = 1) → ∀ v ∈ V, z * v * z⁻¹ ∈ V := by
      intro z hz hz3 v hv
      have h1 := Step1919CoreProof.conj_mem_cenMod (hFN hz.1) hv.2
      have hJz : J.map (MulAut.conj z).toMonoidHom = J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP3 z hz hz3)
      rw [hJz] at h1
      exact ⟨(Subgroup.mem_normalizer_iff.mp hz.2 v).mp hv.1, h1⟩
    rcases Step1919CoreProof.eq_or_eq_of_conj_mem hctx h9 hX inf_le_left hV1 hinv with h | h
    · have hyV : (y : G) ∈ E ⊓ Step1919CoreProof.cenMod M J := by
        rw [h]
        exact hyF
      exact Step1919CoreProof.not_mem_cenMod hyn hyV.2
    · have hcV : c ∈ E ⊓ Step1919CoreProof.cenMod M J := by
        rw [h]
        exact hcE
      exact Step1919CoreProof.not_mem_cenMod hcJ hcV.2
  apply not_injective_of_isTripleA6 htriple hE.2 (fun e => Subtype.ext (by simpa using hEe e e.2))
    (Step1910Proof.quotAct hEJ)
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hg1
  have hg1' : (g : G) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hgV : (g : G) ∉ V := by
    rw [hV, Subgroup.mem_bot]
    exact hg1'
  apply hgV
  refine ⟨g.2, hEM g.2, fun k hk => ?_⟩
  obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hEJ g ⟨k, hk⟩
  rw [hg, MulAut.one_apply] at hact
  have h1 : (⟨k, hk⟩ : J)⁻¹ * j' ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp hact
  rw [Step1911EndProof.mem_pCore_iff] at h1
  have h2 : k⁻¹ * ((g : G) * k * (g : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 J := by
    simpa [hj'] using h1
  have h3 : (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 J := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J hk) _).mp h2
    rwa [show k * (k⁻¹ * ((g : G) * k * (g : G)⁻¹)) * k⁻¹ =
      (g : G) * k * (g : G)⁻¹ * k⁻¹ by group] at this
  exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hJM h3

end Item19Res4Proof

theorem step1919_of_core_wide3
    (hcore : Step1919Core) (h194 : Item194UsedWide3) (h1914E : Step1914E)
    (hmore : Step1914More) : Step1919 := by
  intro G _ _ A c L E M hctx hLM H hH hHM
  have hE := isE27_of_mem_partTwoE hctx.mem_partTwoT.1
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  obtain ⟨hne, hJall⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  have h9 := h1914E G A c L E M hctx hLM
  have hX := hmore G A c L E M hctx hLM
  have hEN : ∀ J ∈ scriptJ M H, E ≤ Subgroup.normalizer (J : Set G) := fun J hJ =>
    Item19Res4Proof.le_normalizer_of_mem_scriptJ_wide3 h194 hctx hH hHM hJ
  have hcJ : ∀ J ∈ scriptJ M H, ∃ j ∈ J, c * j * c⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M :=
    fun J hJ => Item19Res4Proof.exists_commutator_not_mem_of_mem_scriptJ_wide3 h194 hctx hH hHM hJ
  refine hcore G A c L E M hctx hLM h9 hX H hH hHM hne (fun J hJ => ?_) hEN hcJ
  obtain ⟨hlist, hpar⟩ := hJall J hJ
  refine ⟨?_, hpar⟩
  rcases hlist with h | h | htriple
  · exact Or.inl h
  · exact Or.inr h
  · exact (Item19Res4Proof.false_of_isTripleA6_of_mem_scriptJ hctx h9 hX hH hJ htriple
      (Item19Res4Proof.isProperParabolic_of_isTripleA6 htriple hpar) (hEN J hJ)
      (hcJ J hJ)).elim

theorem step1919_of_split_wide3
    (hsplit : Step1919CoreSplit) (h194 : Item194UsedWide3) (h1914E : Step1914E)
    (hmore : Step1914More) : Step1919 :=
  step1919_of_core_wide3 (step1919Core_of hsplit) h194 h1914E hmore

theorem step1919_of_lie_wide3
    (hlie : Step1919CoreSplitLie) (h194 : Item194UsedWide3) (h1914E : Step1914E)
    (hmore : Step1914More) : Step1919 :=
  step1919_of_split_wide3 (step1919CoreSplit_of hlie) h194 h1914E hmore

end CFSG.RankThree.PartTwo.Sec19
