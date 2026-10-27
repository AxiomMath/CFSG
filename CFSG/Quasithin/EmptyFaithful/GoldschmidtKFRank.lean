module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFComp
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

section Transfer

variable {C : Type*} [Group C] [Finite C]

omit [Finite C] in
open scoped IsMulCommutative in
theorem eq_one_of_mem_center_of_perfect (hperf : Group.IsPerfect C) {p : ℕ} [Fact p.Prime]
    {P : Subgroup C} [IsMulCommutative P] (hP : IsPGroup p P) (hidx : ¬ p ∣ P.index) {z : C}
    (hz : z ∈ Subgroup.center C) (hzP : z ∈ P) : z = 1 := by
  classical
  have : P.FiniteIndex := ⟨fun h0 => hidx (h0 ▸ dvd_zero p)⟩
  have key : ∀ (k : ℕ) (g₀ : C), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h1 : g₀ * z ^ k = z ^ k * g₀ := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := mul_assoc _ _ _
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [h1]
      _ = z ^ k := by group
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id P) z key
  have h2 : MonoidHom.transfer (MonoidHom.id P) = (1 : C →* P) := by
    have hker : commutator C ≤ (MonoidHom.transfer (MonoidHom.id P)).ker :=
      Abelianization.commutator_subset_ker _
    rw [hperf.commutator_eq_top] at hker
    exact MonoidHom.ext fun g => MonoidHom.mem_ker.mp (hker (Subgroup.mem_top g))
  rw [h2, MonoidHom.one_apply] at h1
  have h3 : z ^ P.index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  obtain ⟨n, hn⟩ := hP ⟨z, hzP⟩
  have hn' : z ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hd1 : orderOf z ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn'
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd1
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0, pow_zero] at ha
    exact orderOf_eq_one_iff.mp ha
  · exfalso
    apply hidx
    have hd2 : orderOf z ∣ P.index := orderOf_dvd_of_pow_eq_one h3
    rw [ha] at hd2
    exact (dvd_pow_self p hpos.ne').trans hd2

end Transfer

variable {H : Type} [Group H] [Finite H]

theorem exists_noncentral_order_three {C : Subgroup H} (hC : IsQuasisimple ↥C)
    (h1 : CFSG.Open.pRank 3 C = 1) :
    ∃ a ∈ C, a ^ 3 = 1 ∧ ∃ c ∈ C, a * c ≠ c * a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEC, hEel, hEcard⟩ :=
    CFSG.RankThree.PartTwo.Sec5.exists_elemAbelian_le_of_le_pRank Nat.prime_three
      (show 1 ≤ CFSG.Assembly.pRank 3 C from h1.ge)
  have hE3 : 1 < Nat.card E := by rw [hEcard]; norm_num
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := E)).mp
    (fun hb => by rw [hb, Subgroup.card_bot] at hE3; omega)
  have haC : (a : H) ∈ C := hEC a.2
  have ha3 : (a : H) ^ 3 = 1 := hEel.2 a a.2
  have ha1' : (a : H) ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine ⟨a, haC, ha3, ?_⟩
  by_contra hcon
  push Not at hcon
  set a' : ↥C := ⟨a, haC⟩ with ha'
  have hcen : a' ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (hcon c c.2).symm
  have ha'3 : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_of_cube ha'3).exists_le_sylow
  have hrank : CFSG.pRank 3 ↥C ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype (p := 3) C]
    exact h1.le
  have hcyc' : IsCyclic ↥((P : Subgroup ↥C).map C.subtype) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
      (show (P : Subgroup ↥C).map C.subtype ≤ C from Subgroup.map_subtype_le _)
      (P.isPGroup'.map C.subtype) hrank
  let e : ↥(P : Subgroup ↥C) ≃* ↥((P : Subgroup ↥C).map C.subtype) :=
    Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective
  have hcycP : IsCyclic ↥(P : Subgroup ↥C) :=
    isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have : IsMulCommutative (P : Subgroup ↥C) :=
    ⟨⟨fun a b => (IsCyclic.commGroup (α := ↥(P : Subgroup ↥C))).mul_comm a b⟩⟩
  have := eq_one_of_mem_center_of_perfect (p := 3) hC.1 P.isPGroup' P.not_dvd_index hcen
    (hP (Subgroup.mem_zpowers a'))
  exact ha1' (congrArg Subtype.val this)

theorem exists_elemAbelian_twentySeven {S₁ S₂ S₃ : Subgroup H} {a₁ a₂ a₃ : H}
    (h12 : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) (h13 : ∀ x ∈ S₁, ∀ y ∈ S₃, x * y = y * x)
    (h23 : ∀ x ∈ S₂, ∀ y ∈ S₃, x * y = y * x) (ha₁ : a₁ ∈ S₁) (ha₂ : a₂ ∈ S₂) (ha₃ : a₃ ∈ S₃)
    (h₁ : a₁ ^ 3 = 1) (h₂ : a₂ ^ 3 = 1) (h₃ : a₃ ^ 3 = 1) (hn₁ : a₁ ≠ 1)
    (hn₂ : ∃ c ∈ S₂, a₂ * c ≠ c * a₂) (hn₃ : ∃ c ∈ S₃, a₃ * c ≠ c * a₃) :
    ∃ E : Subgroup H, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE₁ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a₁) :=
    isElemAbelian_zpowers_of_cube h₁
  have hE₁card : Nat.card (Subgroup.zpowers a₁) = 3 := by
    rw [Nat.card_zpowers]
    have hd : orderOf a₁ ∣ 3 := orderOf_dvd_of_pow_eq_one h₁
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hn₁
    · exact h
  have hnot₂ : a₂ ∉ Subgroup.zpowers a₁ := by
    intro hmem
    obtain ⟨c, hc, hne⟩ := hn₂
    exact hne (h12 a₂ ((Subgroup.zpowers_le.mpr ha₁) hmem) c hc)
  have hyA₂ : ∀ x ∈ Subgroup.zpowers a₁, x * a₂ = a₂ * x := fun x hx =>
    h12 x ((Subgroup.zpowers_le.mpr ha₁) hx) a₂ ha₂
  obtain ⟨hE₂, hE₂card⟩ :=
    CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE₁ hnot₂ h₂ hyA₂
  have hle : Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ≤ Subgroup.centralizer (S₃ : Set H) :=
    sup_le (Subgroup.zpowers_le.mpr (fun y hy => (h13 a₁ ha₁ y hy).symm))
      (Subgroup.zpowers_le.mpr (fun y hy => (h23 a₂ ha₂ y hy).symm))
  have hnot₃ : a₃ ∉ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ := by
    intro hmem
    obtain ⟨c, hc, hne⟩ := hn₃
    exact hne ((Subgroup.mem_centralizer_iff.mp (hle hmem) c hc).symm)
  have hyA₃ : ∀ x ∈ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂, x * a₃ = a₃ * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hle hx) a₃ ha₃).symm
  obtain ⟨hE₃, hE₃card⟩ :=
    CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE₂ hnot₃ h₃ hyA₃
  exact ⟨_, hE₃, by rw [hE₃card, hE₂card, hE₁card]⟩

omit [Finite H] in
theorem conj_comm {x y : H} (b : H) (h : x * y = y * x) :
    (b * x * b⁻¹) * (b * y * b⁻¹) = (b * y * b⁻¹) * (b * x * b⁻¹) := by
  have h1 : (b * x * b⁻¹) * (b * y * b⁻¹) = b * (x * y) * b⁻¹ := by group
  have h2 : (b * y * b⁻¹) * (b * x * b⁻¹) = b * (y * x) * b⁻¹ := by group
  rw [h1, h2, h]

theorem three_le_pRank_of_moved {C : Subgroup H} (hC : IsComponent C) {b : H} (hb3 : b ^ 3 = 1)
    (hbN : b ∉ Subgroup.normalizer (C : Set H)) {a : H} (haC : a ∈ C) (ha3 : a ^ 3 = 1)
    (hnc : ∃ c ∈ C, a * c ≠ c * a) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  classical
  have hb3' : b * b * b = 1 := by rw [← pow_three']; exact hb3
  have hbb : b * b * b⁻¹ * b⁻¹ * b = b := by group
  have h12 : ∀ x ∈ C, ∀ y ∈ C.map (MulAut.conj b).toMonoidHom, x * y = y * x := by
    rcases distinct_components_commute hC (isComponent_conj hC b) with heq | hcomm
    · exfalso
      apply hbN
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have : b * g * b⁻¹ ∈ C.map (MulAut.conj b).toMonoidHom := ⟨g, hg, rfl⟩
        rwa [← heq] at this
      · intro hg
        rw [heq] at hg
        obtain ⟨g', hg', hgg⟩ := hg
        have : g' = g := by
          have h1 : b * g' * b⁻¹ = b * g * b⁻¹ := hgg
          simpa using h1
        rwa [this] at hg'
    · intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hx) y hy).symm
  obtain ⟨c₀, hc₀, hne₀⟩ := hnc
  have hbb : b * b = b⁻¹ := by
    have : b * (b * b) = 1 := by rw [← mul_assoc]; exact hb3'
    exact (inv_eq_of_mul_eq_one_right this).symm
  have hbb' : (b * b)⁻¹ = b := by rw [hbb, inv_inv]
  set S₂ : Subgroup H := C.map (MulAut.conj b).toMonoidHom with hS₂
  set S₃ : Subgroup H := C.map (MulAut.conj b⁻¹).toMonoidHom with hS₃
  have mem₂ : ∀ c ∈ C, b * c * b⁻¹ ∈ S₂ := fun c hc => ⟨c, hc, rfl⟩
  have mem₃ : ∀ c ∈ C, b⁻¹ * c * b ∈ S₃ := fun c hc => ⟨c, hc, by simp⟩
  have h13 : ∀ x ∈ C, ∀ y ∈ S₃, x * y = y * x := by
    rintro x hx _ ⟨c', hc', rfl⟩
    have h := h12 c' hc' _ (mem₂ x hx)
    have h' := conj_comm b⁻¹ h
    have e1 : b⁻¹ * c' * b⁻¹⁻¹ = b⁻¹ * c' * b := by simp
    have e2 : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
    rw [e2, e1] at h'
    change x * (b⁻¹ * c' * b⁻¹⁻¹) = (b⁻¹ * c' * b⁻¹⁻¹) * x
    rw [e1]
    exact h'.symm
  have h23 : ∀ x ∈ S₂, ∀ y ∈ S₃, x * y = y * x := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    have h := h12 c hc _ (mem₂ c' hc')
    have h' := conj_comm b h
    have e : b * (b * c' * b⁻¹) * b⁻¹ = b⁻¹ * c' * b := by
      have : b * (b * c' * b⁻¹) * b⁻¹ = (b * b) * c' * (b * b)⁻¹ := by group
      rw [this, hbb]
      group
    rw [e] at h'
    change (b * c * b⁻¹) * (b⁻¹ * c' * b⁻¹⁻¹) = (b⁻¹ * c' * b⁻¹⁻¹) * (b * c * b⁻¹)
    rw [inv_inv]
    exact h'
  have hn₂ : ∃ c ∈ S₂, (b * a * b⁻¹) * c ≠ c * (b * a * b⁻¹) := by
    refine ⟨b * c₀ * b⁻¹, mem₂ c₀ hc₀, fun h => hne₀ ?_⟩
    have h1 : (b * a * b⁻¹) * (b * c₀ * b⁻¹) = b * (a * c₀) * b⁻¹ := by group
    have h2 : (b * c₀ * b⁻¹) * (b * a * b⁻¹) = b * (c₀ * a) * b⁻¹ := by group
    rw [h1, h2] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hn₃ : ∃ c ∈ S₃, (b⁻¹ * a * b) * c ≠ c * (b⁻¹ * a * b) := by
    refine ⟨b⁻¹ * c₀ * b, mem₃ c₀ hc₀, fun h => hne₀ ?_⟩
    have h1 : (b⁻¹ * a * b) * (b⁻¹ * c₀ * b) = b⁻¹ * (a * c₀) * b := by group
    have h2 : (b⁻¹ * c₀ * b) * (b⁻¹ * a * b) = b⁻¹ * (c₀ * a) * b := by group
    rw [h1, h2] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hcubeconj : ∀ g : H, (g * a * g⁻¹) ^ 3 = 1 := fun g => by
    rw [← MulAut.conj_apply, ← map_pow, ha3, map_one]
  have hne1 : a ≠ 1 := fun h1 => hne₀ (by rw [h1]; simp)
  obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_twentySeven (S₁ := C) (S₂ := S₂) (S₃ := S₃)
    (a₁ := a) (a₂ := b * a * b⁻¹) (a₃ := b⁻¹ * a * b) h12 h13 h23 haC (mem₂ a haC) (mem₃ a haC)
    ha3 (hcubeconj b) (by simpa using hcubeconj b⁻¹) hne1 hn₂ hn₃
  exact CFSG.RankThree.PartTwo.Sec5.le_pRank_of_elemAbelian Nat.prime_three (le_top : E ≤ ⊤) hE
    (by rw [hEcard]; norm_num)

end CFSG.Quasithin.SBd19F
