module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualInv
import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualField

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem conjSubgroup_pow_of_odd {u : G} {V₁ V₂ : Subgroup G} (h₁ : conjSubgroup u V₁ = V₂)
    (h₂ : conjSubgroup u V₂ = V₁) {k : ℕ} (hk : Odd k) : conjSubgroup (u ^ k) V₁ = V₂ := by
  obtain ⟨j, rfl⟩ := hk
  induction j with
  | zero => simpa using h₁
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, pow_succ', pow_succ',
      conjSubgroup_mul, conjSubgroup_mul, ih, h₂, h₁]

theorem not_le_of_sectionAct {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {F : Type}
    [Field F] {S V Z : Subgroup G} {φ : S →* GL ι F} {act : GL ι F → Matrix ι ι F}
    (h : SectionAct F S V Z φ act) : ¬ V ≤ Z := by
  intro hle
  obtain ⟨-, hN, ψ, -⟩ := h
  letI := hN
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
    (ψ.symm (Multiplicative.ofAdd (Pi.single i 1 : ι → F)))
  have h1 : (QuotientGroup.mk x : ↥V ⧸ Z.subgroupOf V) = 1 :=
    (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr (hle x.2))
  have h2 : ψ.symm (Multiplicative.ofAdd (Pi.single i 1 : ι → F)) = 1 := hx ▸ h1
  have h3 : Multiplicative.ofAdd (Pi.single i 1 : ι → F) = 1 := by
    have := congrArg ψ h2
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have h4 := congrFun (ofAdd_eq_one.mp h3) i
  simp at h4

structure XbarCore (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] (n : ℕ) where
  F : Type
  [field : Field F]
  [fin : Finite F]
  card : Nat.card F = Nat.card Z
  φ : ↥(XbarPre M Q Z B) →* GL (Fin n) F
  range_eq : φ.range = StatedSL n F
  ker_eq : φ.ker = Q.subgroupOf (XbarPre M Q Z B)
  V₁ : Subgroup G
  V₂ : Subgroup G
  Z_le₁ : Z ≤ V₁
  le_Q₁ : V₁ ≤ Q
  Z_le₂ : Z ≤ V₂
  le_Q₂ : V₂ ≤ Q
  inf_eq : V₁ ⊓ V₂ = Z
  sup_eq : V₁ ⊔ V₂ = Q
  act₁ : SectionAct (ι := Fin n) F (XbarPre M Q Z B) V₁ Z φ
    (fun g => (g : Matrix (Fin n) (Fin n) F))
  act₂ : SectionAct (ι := Fin n) F (XbarPre M Q Z B) V₂ Z φ
    (fun g => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ)

attribute [instance] XbarCore.field XbarCore.fin

variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] {n : ℕ}

theorem XbarCore.nonempty_of_caseVICore (h : CaseVICore M Q Z (XbarPre M Q Z B) n) :
    Nonempty (XbarCore M Q Z B n) := by
  obtain ⟨F, hF, hFfin, hcard, φ, hr, hk, V₁, V₂, h1, h2, h3, h4, h5, h6, hA1, hA2, -⟩ := h
  letI := hF
  letI := hFfin
  exact ⟨⟨F, hcard, φ, hr, hk, V₁, V₂, h1, h2, h3, h4, h5, h6, hA1, hA2⟩⟩

theorem XbarCore.not_V₁_le_Z (hn : 1 ≤ n) (S : XbarCore M Q Z B n) : ¬ S.V₁ ≤ Z := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact not_le_of_sectionAct S.act₁

theorem XbarCore.not_V₂_le_Z (hn : 1 ≤ n) (S : XbarCore M Q Z B n) : ¬ S.V₂ ≤ Z := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact not_le_of_sectionAct S.act₂

theorem XbarCore.V₁_ne_V₂ (hn : 1 ≤ n) (S : XbarCore M Q Z B n) : S.V₁ ≠ S.V₂ := by
  intro h
  have h2 := S.inf_eq.le
  rw [← h, inf_idem] at h2
  exact S.not_V₁_le_Z hn h2

theorem XbarCore.V₁_ne_Q (hn : 1 ≤ n) (S : XbarCore M Q Z B n) : S.V₁ ≠ Q := by
  intro h
  have h1 : S.V₁ ⊓ S.V₂ = S.V₂ := inf_eq_right.mpr (by rw [h]; exact S.le_Q₂)
  have h2 := S.inf_eq.le
  rw [h1] at h2
  exact S.not_V₂_le_Z hn h2

theorem XbarCore.V₂_ne_Q (hn : 1 ≤ n) (S : XbarCore M Q Z B n) : S.V₂ ≠ Q := by
  intro h
  have h1 : S.V₁ ⊓ S.V₂ = S.V₁ := inf_eq_left.mpr (by rw [h]; exact S.le_Q₁)
  have h2 := S.inf_eq.le
  rw [h1] at h2
  exact S.not_V₁_le_Z hn h2

private theorem eq_of_mem_img_iff {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {W V : Subgroup G} (hZW : Z ≤ W) (hWQ : W ≤ Q) (hZV : Z ≤ V)
    (hVQ : V ≤ Q) (h : ∀ e, e ∈ M₀.img W ↔ e ∈ M₀.img V) : W = V := by
  ext x
  constructor
  · intro hx
    exact (M₀.mem_img_iff hZV (hWQ hx)).mp ((h _).mp (M₀.pi_mem_img hx (hWQ hx)))
  · intro hx
    exact (M₀.mem_img_iff hZW (hVQ hx)).mp ((h _).mpr (M₀.pi_mem_img hx (hVQ hx)))

section Coord

variable [Finite G]

theorem XbarCore.exists_coord (hc : Ctx M Q Z B) (hn : 3 ≤ n) (S : XbarCore M Q Z B n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ φH0 : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E),
        (∀ (m : H0 M Z) (x : G), x ∈ Q →
          M₀.π ((m : G) * x * (m : G)⁻¹) = φH0 m (M₀.π x)) ∧
        (∀ m : H0 M Z, φH0 m = 1 ↔ (m : G) ∈ Q) ∧
        (∀ (m : H0 M Z) (e : M₀.E), M₀.Qf (φH0 m e) = M₀.Qf e) ∧
        ∃ C : NatDualCoord (φH0.comp (Subgroup.inclusion (XbarPre_le_H0 hc))) S.φ,
          (∀ e, e ∈ M₀.img S.V₁ ↔ e ∈ C.W₁) ∧ ∀ e, e ∈ M₀.img S.V₂ ↔ e ∈ C.W₂ := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φH0, hφπ, hφker, hφQf⟩ := exists_actionHom_H0 hc.hyp hD
  have hρπ : ∀ (s : ↥(XbarPre M Q Z B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) =
        (φH0.comp (Subgroup.inclusion (XbarPre_le_H0 hc))) s (M₀.π x) :=
    fun s x hx => hφπ ⟨s, XbarPre_le_H0 hc s.2⟩ x hx
  obtain ⟨Φ, hΦact, hΦV₁, hΦV₂⟩ := exists_equivariant_coord (M₀ := M₀)
    (φH0.comp (Subgroup.inclusion (XbarPre_le_H0 hc))) hρπ S.Z_le₁ S.le_Q₁ S.Z_le₂ S.le_Q₂
    S.inf_eq S.sup_eq S.φ S.act₁ S.act₂
  obtain ⟨C, hC⟩ := exists_natDualCoord_of_equivariant _ S.φ hn S.range_eq
    (hD.card.trans S.card.symm) Φ hΦact
  refine ⟨K, inferInstance, inferInstance, inferInstance, γ, M₀, hD, φH0, hφπ, hφker, hφQf, C,
    fun e => ?_, fun e => ?_⟩
  · rw [C.mem_W₁, hC]
    exact hΦV₁ e
  · rw [C.mem_W₂, hC]
    exact hΦV₂ e

theorem XbarCore.eq_of_le_normalizer (hc : Ctx M Q Z B) (hn : 3 ≤ n) (S : XbarCore M Q Z B n)
    {W : Subgroup G} (hZW : Z ≤ W) (hWQ : W ≤ Q)
    (hW : XbarPre M Q Z B ≤ Subgroup.normalizer (W : Set G)) :
    W = Z ∨ W = S.V₁ ∨ W = S.V₂ ∨ W = Q := by
  obtain ⟨K, _, _, _, γ, M₀, -, φH0, hφπ, -, -, C, hW₁, hW₂⟩ := S.exists_coord hc hn
  have hinv : ∀ (g : ↥(XbarPre M Q Z B)) (e : M₀.E), e ∈ M₀.img W →
      (φH0.comp (Subgroup.inclusion (XbarPre_le_H0 hc))) g e ∈ M₀.img W := by
    rintro g _ ⟨w, hwW, hwQ, rfl⟩
    have hgw : (g : G) * w * (g : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hW g.2) w).mp hwW
    have h1 : (φH0.comp (Subgroup.inclusion (XbarPre_le_H0 hc))) g (M₀.π w) =
        M₀.π ((g : G) * w * (g : G)⁻¹) := (hφπ ⟨g, XbarPre_le_H0 hc g.2⟩ w hwQ).symm
    rw [h1]
    exact M₀.pi_mem_img hgw (hWQ hgw)
  rcases C.invariant_classification hn S.range_eq (M₀.img W) hinv with h | h | h | h
  · left
    refine le_antisymm (fun w hw => ?_) hZW
    have hw0 := M₀.pi_mem_img hw (hWQ hw)
    rw [h, AddSubgroup.mem_bot] at hw0
    exact (M₀.π_ker w (hWQ hw)).mp hw0
  · right; left
    exact eq_of_mem_img_iff M₀ hZW hWQ S.Z_le₁ S.le_Q₁ fun e => by rw [h, hW₁]
  · right; right; left
    exact eq_of_mem_img_iff M₀ hZW hWQ S.Z_le₂ S.le_Q₂ fun e => by rw [h, hW₂]
  · right; right; right
    refine le_antisymm hWQ fun x hx => (M₀.mem_img_iff hZW hx).mp ?_
    rw [h]
    exact AddSubgroup.mem_top _

private theorem XbarCore.conj_eq_or_eq (hc : Ctx M Q Z B) (hn : 3 ≤ n) (S : XbarCore M Q Z B n)
    {u : G} (hu : u ∈ M) {V : Subgroup G} (hZV : Z ≤ V) (hVQ : V ≤ Q)
    (hVN : XbarPre M Q Z B ≤ Subgroup.normalizer (V : Set G)) (hVZ : ¬ V ≤ Z) (hVQ' : V ≠ Q) :
    conjSubgroup u V = S.V₁ ∨ conjSubgroup u V = S.V₂ := by
  have hZ : conjSubgroup u Z = Z := hc.conj_Z_eq hu
  have hQ : conjSubgroup u Q = Q := hc.conj_Q_eq hu
  have hZW : Z ≤ conjSubgroup u V := fun z hz =>
    mem_conjSubgroup.mpr (hZV (mem_conjSubgroup.mp (by rw [hZ]; exact hz)))
  have hWQ : conjSubgroup u V ≤ Q := fun x hx => by
    rw [← hQ]
    exact mem_conjSubgroup.mpr (hVQ (mem_conjSubgroup.mp hx))
  have hWN : XbarPre M Q Z B ≤ Subgroup.normalizer (conjSubgroup u V : Set G) := by
    intro g hg
    rw [← conjSubgroup_eq_self_iff]
    have hg' : u⁻¹ * g * u ∈ XbarPre M Q Z B := by
      rw [← XbarPre_normal hc (M.inv_mem hu), mem_conjSubgroup]
      simpa [mul_assoc] using hg
    have h1 : conjSubgroup (u⁻¹ * g * u) V = V := conjSubgroup_eq_self_iff.mpr (hVN hg')
    calc conjSubgroup g (conjSubgroup u V) =
        conjSubgroup u (conjSubgroup (u⁻¹ * g * u) V) := by
          rw [← conjSubgroup_mul, ← conjSubgroup_mul]
          congr 1
          group
      _ = conjSubgroup u V := by rw [h1]
  rcases S.eq_of_le_normalizer hc hn hZW hWQ hWN with h | h | h | h
  · exact absurd (conjSubgroup_inj.mp (h.trans hZ.symm)).le hVZ
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (conjSubgroup_inj.mp (h.trans hQ.symm)) hVQ'

theorem XbarCore.conj_dichotomy (hc : Ctx M Q Z B) (hn : 3 ≤ n) (S : XbarCore M Q Z B n)
    {u : G} (hu : u ∈ M) :
    (conjSubgroup u S.V₁ = S.V₁ ∧ conjSubgroup u S.V₂ = S.V₂) ∨
      (conjSubgroup u S.V₁ = S.V₂ ∧ conjSubgroup u S.V₂ = S.V₁) := by
  have hne := S.V₁_ne_V₂ (by omega)
  rcases S.conj_eq_or_eq hc hn hu S.Z_le₁ S.le_Q₁ S.act₁.1 (S.not_V₁_le_Z (by omega))
      (S.V₁_ne_Q (by omega)) with h₁ | h₁ <;>
    rcases S.conj_eq_or_eq hc hn hu S.Z_le₂ S.le_Q₂ S.act₂.1 (S.not_V₂_le_Z (by omega))
      (S.V₂_ne_Q (by omega)) with h₂ | h₂
  · exact absurd (conjSubgroup_inj.mp (h₁.trans h₂.symm)) hne
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (conjSubgroup_inj.mp (h₁.trans h₂.symm)) hne

theorem XbarCore.conj_eq_of_pow_eq_one (hc : Ctx M Q Z B) (hn : 3 ≤ n) (S : XbarCore M Q Z B n)
    {u : G} (hu : u ∈ M) {k : ℕ} (hk : Odd k) (huk : u ^ k = 1) :
    conjSubgroup u S.V₁ = S.V₁ ∧ conjSubgroup u S.V₂ = S.V₂ := by
  rcases S.conj_dichotomy hc hn hu with h | h
  · exact h
  · have h1 := conjSubgroup_pow_of_odd h.1 h.2 hk
    rw [huk, conjSubgroup_one] at h1
    exact absurd h1 (S.V₁_ne_V₂ (by omega))

end Coord

end CFSG.RankThree.GF2n.Stroth80
