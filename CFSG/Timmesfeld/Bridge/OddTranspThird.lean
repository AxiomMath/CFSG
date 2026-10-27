module

public import CFSG.Timmesfeld.Bridge.OddTranspLocal

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {D : Set G}

namespace OddTransp

section Local

variable (hD : IsOddTransp D) (hN : IsNormalSet D) {Q : Subgroup G} [hQn : Q.Normal]
  (hQ : IsPGroup 2 Q)
include hD hN hQ

theorem mem_commutator_of_commute {v b y : G} (hv : v ∈ D) (hb : b ∈ D) (hvb : ¬ Commute v b)
    (hy : y ∈ ⁅Q, Subgroup.zpowers b⁆) (hyv : Commute y v) : y ∈ ⁅Q, Subgroup.zpowers v⁆ := by
  obtain ⟨g, hg, hgv⟩ := hD.exists_conj hv hb hvb
  have hyb : Commute y b := (commute_of_mem_commutator hD hN hQ hb hb (Commute.refl b) hy).symm
  have hgy : Commute g y := by
    refine Asc72.commute_of_mem_closure (S := {v, b}) (T := {y}) ?_ hg
      (Subgroup.subset_closure rfl)
    intro x hx y' hy'
    rw [Set.mem_singleton_iff] at hy'
    rw [hy']
    rcases hx with hx | hx
    · rw [hx]; exact hyv.symm
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hyb.symm
  have hmap : (⁅Q, Subgroup.zpowers b⁆).map (MulAut.conj g⁻¹).toMonoidHom ≤
      ⁅Q, Subgroup.zpowers v⁆ := by
    rw [Subgroup.map_commutator]
    apply Subgroup.commutator_mono
    · rintro _ ⟨q, hq, rfl⟩
      exact hQn.conj_mem q hq g⁻¹
    · rw [MonoidHom.map_zpowers]
      have e : (MulAut.conj g⁻¹).toMonoidHom b = v := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ← hgv]
        group
      rw [e]
  have h1 := hmap ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
  rwa [mul_assoc, ← hgy.eq, inv_mul_cancel_left] at h1

theorem exists_commutator_mul_of_commute [Finite G] {e b y : G} (he : e ∈ D) (hb : b ∈ D)
    (heb : ¬ Commute e b) (hy : y ∈ Q) (hye : Commute y e) :
    ∃ x ∈ ⁅Q, Subgroup.zpowers e⁆, ∃ w ∈ Q, Commute w e ∧ Commute w b ∧ y = x * w := by
  have hb'D : y * b * y⁻¹ ∈ D := hN y b hb
  have hb'b : y * b * y⁻¹ * b⁻¹ ∈ Q := by
    have h1 := hQn.conj_mem _ (Q.inv_mem hy) b
    have e1 : y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
    rw [e1]
    exact Q.mul_mem hy h1
  have hb'e : ¬ Commute (y * b * y⁻¹) e := by
    intro hc
    apply heb
    have h1 := hc.map (MulAut.conj y⁻¹).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    have e1 : y⁻¹ * (y * b * y⁻¹) * y = b := by group
    have e2 : y⁻¹ * e * y = e := by rw [mul_assoc, ← hye.eq, inv_mul_cancel_left]
    rw [e1, e2] at h1
    exact h1.symm
  obtain ⟨x, hx, hxe⟩ := exists_conj_of_mul_inv_mem hD hN hQ hb he (fun h => heb h.symm) hb'D
    hb'b hb'e
  have hxQ : x ∈ Q := Subgroup.commutator_le_left Q _ hx
  refine ⟨x, hx, x⁻¹ * y, Q.mul_mem (Q.inv_mem hxQ) hy, ?_, ?_, by group⟩
  · have hxe' : Commute x e := (commute_of_mem_commutator hD hN hQ he he (Commute.refl e) hx).symm
    exact hxe'.inv_left.mul_left hye
  · show x⁻¹ * y * b = b * (x⁻¹ * y)
    have h1 : x⁻¹ * (y * b * y⁻¹) * x = b := by rw [← hxe]; group
    calc x⁻¹ * y * b = x⁻¹ * (y * b * y⁻¹) * x * (x⁻¹ * y) := by group
      _ = b * (x⁻¹ * y) := by rw [h1]

end Local

end OddTransp

@[expose] def sylowCommutator (D : Set G) (S : Sylow 2 G) : Subgroup G :=
  Subgroup.closure {y | ∃ v ∈ D ∩ (S : Set G), y ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆}

namespace ThirdKindHyp

variable {S : Sylow 2 G} {a b c : G} {n : ℕ} (h : ThirdKindHyp G D S a b c n)
include h

theorem oddT : IsOddTransp D := h.setup.oddT

theorem normal : IsNormalSet D := h.setup.normal

omit h in
theorem isPGroup_pCore : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup

theorem a_mem' : a ∈ D ∩ (S : Set G) := ⟨h.tri.1, h.a_mem⟩

theorem c_mem' : c ∈ D ∩ (S : Set G) := ⟨h.tri.2.1, h.c_mem⟩

theorem b_mem : b ∈ D := h.tri.2.2.1

omit h in
theorem pCore_le : CFSG.pCore 2 G ≤ S :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isPGroup_pCore.le_sylow_of_normal S

theorem commute_of_mem {v w : G} (hv : v ∈ D ∩ (S : Set G)) (hw : w ∈ D ∩ (S : Set G)) :
    Commute v w :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  h.oddT.commute_of_isPGroup S.isPGroup' hv.1 hw.1 hv.2 hw.2

theorem mem_center_of_commute {y : G} (hb : Commute b y)
    (hL : ∀ v ∈ D ∩ (S : Set G), Commute v y) : y ∈ Subgroup.center G := by
  have hle : Subgroup.closure (insert b (D ∩ (S : Set G))) ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    rintro t (rfl | ht)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hb
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hL t ht)
  rw [h.gen] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))

theorem not_commute_b {v : G} (hv : v ∈ D ∩ (S : Set G)) : ¬ Commute v b := by
  intro hvb
  have hvz : v ∈ Subgroup.center G :=
    h.mem_center_of_commute hvb.symm (fun w hw => h.commute_of_mem hw hv)
  have hcen : ∀ x ∈ D, x = v := by
    intro x hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (h.setup.isConj hv.1 hx)
    rw [← hg, Subgroup.mem_center_iff.mp hvz g, mul_inv_cancel_right]
  exact h.tri.2.2.2.1 ((hcen a h.tri.1).trans (hcen c h.tri.2.1).symm)

theorem z_spec : (a * c * b) ^ n * (a * c * b) ^ n = 1 ∧ (a * c * b) ^ n ≠ 1 ∧
    Commute ((a * c * b) ^ n) a ∧ Commute ((a * c * b) ^ n) c ∧
    Commute ((a * c * b) ^ n) b ∧ a * c * (a * c * b) ^ n ∈ D :=
  h.tri.third_kind h.oddT h.normal h.odd h.order

theorem z_mem_center : (a * c * b) ^ n ∈ Subgroup.center G := by
  obtain ⟨-, -, hza, hzc, hzb, hacz⟩ := h.z_spec
  have hS' : a * c * (a * c * b) ^ n ∈ D ∩ (S : Set G) :=
    ⟨hacz, S.mul_mem (S.mul_mem h.a_mem h.c_mem) h.z_mem⟩
  have he : (a * c * b) ^ n = a * c * (a * c * (a * c * b) ^ n) := by
    rw [← mul_assoc, IsTriangle.uv_mul_self h.oddT h.tri, one_mul]
  refine h.mem_center_of_commute hzb.symm fun v hv => ?_
  rw [he]
  exact ((h.commute_of_mem hv h.a_mem').mul_right (h.commute_of_mem hv h.c_mem')).mul_right
    (h.commute_of_mem hv hS')

theorem z_mem_pCore : (a * c * b) ^ n ∈ CFSG.pCore 2 G := by
  obtain ⟨hzz, -⟩ := h.z_spec
  have hle : Subgroup.zpowers ((a * c * b) ^ n) ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr h.z_mem_center
  have hn : (Subgroup.zpowers ((a * c * b) ^ n)).Normal := Subgroup.normal_of_le_center hle
  have h2 : IsPGroup 2 (Subgroup.zpowers ((a * c * b) ^ n)) := by
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    rcases (mem_zpowers_of_mul_self hzz).mp hg with rfl | rfl
    · simp
    · simp [pow_two, hzz]
  have hle2 : Subgroup.zpowers ((a * c * b) ^ n) ≤ CFSG.pCore 2 G := le_sSup ⟨hn, h2⟩
  exact hle2 (Subgroup.mem_zpowers _)

theorem mem_or_mul_mem [Finite G] {q : G} (hq : q ∈ CFSG.pCore 2 G) :
    q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆ ∨
      q * (a * c * b) ^ n ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆ := by
  have hnpc := h.npc ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆ inferInstance
    (Subgroup.commutator_le_left _ _) le_rfl
  by_cases hq' : q ∈ commutator G
  · exact Or.inl (hnpc ⟨hq, hq'⟩)
  right
  have hne : commutator G ≠ ⊤ := fun htop => hq' (htop ▸ Subgroup.mem_top q)
  have hidx : (commutator G).index = 2 := by
    have h1 := h.setup.index_commutator_le_two
    have h2 : (commutator G).index ≠ 1 := fun h1 => hne (Subgroup.index_eq_one.mp h1)
    have h0 : (commutator G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hdisj : ∀ x ∈ D, x ∉ commutator G := by
    rcases h.setup.subset_or_disjoint (commutator G) with h' | h'
    · exact absurd (h.setup.eq_top_of_subset _ h') hne
    · exact h'
  obtain ⟨-, -, -, -, -, hacz⟩ := h.z_spec
  have hac : a * c ∈ commutator G := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false (hdisj a h.tri.1) (hdisj c h.tri.2.1)
  have hz : (a * c * b) ^ n ∉ commutator G := by
    have he : (a * c * b) ^ n = a * c * (a * c * (a * c * b) ^ n) := by
      rw [← mul_assoc, IsTriangle.uv_mul_self h.oddT h.tri, one_mul]
    rw [he, Subgroup.mul_mem_iff_of_index_two hidx]
    exact fun hiff => hdisj _ hacz (hiff.mp hac)
  have hqz : q * (a * c * b) ^ n ∈ commutator G := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false hq' hz
  exact hnpc ⟨(CFSG.pCore 2 G).mul_mem hq h.z_mem_pCore, hqz⟩

omit h in
theorem sylowCommutator_le : sylowCommutator D S ≤ CFSG.pCore 2 G := by
  rw [sylowCommutator, Subgroup.closure_le]
  rintro y ⟨v, -, hy⟩
  exact Subgroup.commutator_le_left _ _ hy

theorem commute_of_mem_sylowCommutator {v y : G} (hv : v ∈ D ∩ (S : Set G))
    (hy : y ∈ sylowCommutator D S) : Commute v y := by
  have hle : sylowCommutator D S ≤ Subgroup.centralizer {v} := by
    rw [sylowCommutator, Subgroup.closure_le]
    rintro x ⟨w, hw, hx⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_mem_commutator h.oddT h.normal isPGroup_pCore hw.1 hv.1
      (h.commute_of_mem hv hw) hx).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem commutator_top_eq : ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆ =
    sylowCommutator D S ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ := by
  refine le_antisymm ?_ (sup_le ?_ (Subgroup.commutator_mono_right le_top))
  · refine commutator_le_of_closure
      (sup_le sylowCommutator_le (Subgroup.commutator_le_left _ _)) h.gen ?_ ?_
    · rintro t (rfl | ht)
      · exact h.oddT.mul_self_eq_one h.b_mem
      · exact h.oddT.mul_self_eq_one ht.1
    · rintro t (rfl | ht) q hq
      · exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq
          (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, ht,
          Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers _)⟩)
  · rw [sylowCommutator, Subgroup.closure_le]
    rintro y ⟨v, -, hy⟩
    exact Subgroup.commutator_mono_right le_top hy

theorem commute_of_commute [Finite G] {v w y : G} (hv : v ∈ D ∩ (S : Set G))
    (hw : w ∈ D ∩ (S : Set G))
    (hy : y ∈ CFSG.pCore 2 G) (hyv : Commute y v) : Commute y w := by
  have hQ : IsPGroup 2 (CFSG.pCore 2 G) := isPGroup_pCore
  have key : ∀ y₀ ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, Commute y₀ v → Commute y₀ w := by
    intro y₀ hy₀ hy₀v
    rw [h.commutator_top_eq] at hy₀
    have hnorm : sylowCommutator D S ≤
        Subgroup.normalizer ((⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ : Subgroup G) : Set G) :=
      sylowCommutator_le.trans (Subgroup.normalizer_commutator_ge_left _ _)
    have hy₀' : y₀ ∈ (↑(sylowCommutator D S ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆) : Set G) :=
      hy₀
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hy₀'
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Set.mem_mul.mp hy₀'
    have hy₁v : Commute y₁ v := (h.commute_of_mem_sylowCommutator hv hy₁).symm
    have hy₂v : Commute y₂ v := by
      have e : y₂ = y₁⁻¹ * (y₁ * y₂) := by group
      rw [e]
      exact hy₁v.inv_left.mul_left hy₀v
    have hy₂Q₁ : y₂ ∈ sylowCommutator D S :=
      Subgroup.subset_closure ⟨v, hv, mem_commutator_of_commute h.oddT h.normal hQ hv.1 h.b_mem
        (h.not_commute_b hv) hy₂ hy₂v⟩
    exact ((h.commute_of_mem_sylowCommutator hw hy₁).mul_right
      (h.commute_of_mem_sylowCommutator hw hy₂Q₁)).symm
  have hz := Subgroup.mem_center_iff.mp h.z_mem_center
  rcases h.mem_or_mul_mem hy with h0 | h0
  · exact key y h0 hyv
  · have h1 := key _ h0 (hyv.mul_left (show Commute v ((a * c * b) ^ n) from hz v).symm)
    have e : y = y * (a * c * b) ^ n * ((a * c * b) ^ n)⁻¹ := by group
    rw [e]
    exact h1.mul_left (show Commute w ((a * c * b) ^ n) from hz w).symm.inv_left

theorem commute_and_iff [Finite G] {y : G} (hy : y ∈ CFSG.pCore 2 G) :
    Commute y a ∧ Commute y b ↔ y ∈ Subgroup.center G := by
  constructor
  · rintro ⟨hya, hyb⟩
    exact h.mem_center_of_commute hyb.symm fun v hv =>
      (h.commute_of_commute h.a_mem' hv hy hya).symm
  · intro hyc
    exact ⟨(Subgroup.mem_center_iff.mp hyc a).symm, (Subgroup.mem_center_iff.mp hyc b).symm⟩

theorem exists_eq_mul_of_mem_commutator [Finite G] {e : G} (he : e ∈ D ∩ (S : Set G)) {x : G}
    (hx : x ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers e⁆) :
    ∃ e₁ ∈ D ∩ (S : Set G), e₁ * e⁻¹ ∈ CFSG.pCore 2 G ∧
      ∃ z ∈ CFSG.pCore 2 G ⊓ Subgroup.center G, x = e * e₁ * z := by
  have hQ : IsPGroup 2 (CFSG.pCore 2 G) := isPGroup_pCore
  have he2 := h.oddT.mul_self_eq_one he.1
  have hei : e⁻¹ = e := h.oddT.inv_eq he.1
  have hone : ∃ e₁ ∈ D ∩ (S : Set G), e₁ * e⁻¹ ∈ CFSG.pCore 2 G ∧
      ∃ z ∈ CFSG.pCore 2 G ⊓ Subgroup.center G, (1 : G) = e * e₁ * z :=
    ⟨e, he, by rw [mul_inv_cancel]; exact Subgroup.one_mem _, 1,
      ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, by rw [mul_one, he2]⟩
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨q, hq, t, ht, rfl⟩ := hy
    rcases (mem_zpowers_of_mul_self he2).mp ht with h1 | h1
    · rw [h1, commutatorElement_one_right]
      exact hone
    · rw [h1]
      have hqe : q * e * q⁻¹ ∈ D ∩ (S : Set G) :=
        ⟨h.normal q e he.1, S.mul_mem (S.mul_mem (pCore_le hq) he.2)
          (S.inv_mem (pCore_le hq))⟩
      refine ⟨q * e * q⁻¹, hqe, ?_, 1, ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, ?_⟩
      · have := (CFSG.pCore 2 G).mul_mem hq ((CFSG.pCore_normal (p := 2) (G := G)).conj_mem _
          ((CFSG.pCore 2 G).inv_mem hq) e)
        simpa [mul_assoc] using this
      · rw [mul_one, commutatorElement_def, hei, (h.commute_of_mem hqe he).eq]
  | one => exact hone
  | mul x₁ x₂ _ _ ih₁ ih₂ =>
    obtain ⟨e₁, he₁, he₁Q, z₁, hz₁, rfl⟩ := ih₁
    obtain ⟨e₂, he₂, he₂Q, z₂, hz₂, rfl⟩ := ih₂
    have hb := h.b_mem
    have heb := h.not_commute_b he
    obtain ⟨y₁, hy₁, hy₁e⟩ := exists_conj_of_mul_inv_mem h.oddT h.normal hQ he.1 hb heb he₁.1
      he₁Q (h.not_commute_b he₁)
    obtain ⟨y₂, hy₂, hy₂e⟩ := exists_conj_of_mul_inv_mem h.oddT h.normal hQ he.1 hb heb he₂.1
      he₂Q (h.not_commute_b he₂)
    obtain ⟨hz₃, he₃⟩ := conj_mul_conj_eq h.oddT h.normal hQ he.1 hy₁ hy₂
    rw [hy₁e, hy₂e] at he₃
    set z₃ := ⁅⁅y₂, e⁆⁻¹, y₁⁆ with hz₃def
    have hz₃c : z₃ ∈ Subgroup.center G := by
      refine h.mem_center_of_commute
        (commute_of_mem_commutator h.oddT h.normal hQ hb hb (Commute.refl b) hz₃.2) ?_
      intro v hv
      exact commute_of_mem_commutator h.oddT h.normal hQ he.1 hv.1 (h.commute_of_mem hv he)
        hz₃.1
    have hz₃Q : z₃ ∈ CFSG.pCore 2 G := Subgroup.commutator_le_left _ _ hz₃.1
    have hy₁Q : y₁ ∈ CFSG.pCore 2 G := Subgroup.commutator_le_left _ _ hy₁
    have hy₂Q : y₂ ∈ CFSG.pCore 2 G := Subgroup.commutator_le_left _ _ hy₂
    set e₃ := y₁ * y₂ * e * (y₁ * y₂)⁻¹ with he₃def
    have he₃S : e₃ ∈ D ∩ (S : Set G) := by
      refine ⟨h.normal _ e he.1, ?_⟩
      have hyS : y₁ * y₂ ∈ S := S.mul_mem (pCore_le hy₁Q) (pCore_le hy₂Q)
      exact S.mul_mem (S.mul_mem hyS he.2) (S.inv_mem hyS)
    have he₃Q : e₃ * e⁻¹ ∈ CFSG.pCore 2 G := by
      have hyQ : y₁ * y₂ ∈ CFSG.pCore 2 G := Subgroup.mul_mem _ hy₁Q hy₂Q
      have := (CFSG.pCore 2 G).mul_mem hyQ ((CFSG.pCore_normal (p := 2) (G := G)).conj_mem _
        ((CFSG.pCore 2 G).inv_mem hyQ) e)
      simpa [he₃def, mul_assoc] using this
    have hz₁c := Subgroup.mem_center_iff.mp hz₁.2
    have hz₂c := Subgroup.mem_center_iff.mp hz₂.2
    have hz₃c' := Subgroup.mem_center_iff.mp hz₃c
    refine ⟨e₃, he₃S, he₃Q, z₃⁻¹ * z₁ * z₂, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₃Q) hz₁.1) hz₂.1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₃c) hz₁.2) hz₂.2
    ·
      have hee₁ : Commute e e₁ := h.commute_of_mem he he₁
      have h1 : e * e₁ * e = e₁ := by rw [hee₁.eq, mul_assoc, he2, mul_one]
      have hz₃i := Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hz₃c)
      have hL : e * e₁ * z₁ * (e * e₂ * z₂) = e₁ * e₂ * (z₁ * z₂) := by
        calc e * e₁ * z₁ * (e * e₂ * z₂) = e * e₁ * (z₁ * (e * e₂)) * z₂ := by group
          _ = e * e₁ * (e * e₂ * z₁) * z₂ := by rw [← hz₁c (e * e₂)]
          _ = e * e₁ * e * e₂ * (z₁ * z₂) := by group
          _ = e₁ * e₂ * (z₁ * z₂) := by rw [h1]
      have hR : e * e₃ * (z₃⁻¹ * z₁ * z₂) = e₁ * e₂ * (z₁ * z₂) := by
        rw [he₃]
        calc e * (z₃ * (e * e₁ * e₂)) * (z₃⁻¹ * z₁ * z₂) =
            e * z₃ * (e * e₁ * e₂) * z₃⁻¹ * (z₁ * z₂) := by group
          _ = z₃ * e * (e * e₁ * e₂) * z₃⁻¹ * (z₁ * z₂) := by rw [hz₃c' e]
          _ = z₃ * (e * e * e₁ * e₂ * z₃⁻¹) * (z₁ * z₂) := by group
          _ = z₃ * (z₃⁻¹ * (e * e * e₁ * e₂)) * (z₁ * z₂) := by
            rw [hz₃i (e * e * e₁ * e₂)]
          _ = e * e * e₁ * e₂ * (z₁ * z₂) := by group
          _ = e₁ * e₂ * (z₁ * z₂) := by rw [he2, one_mul]
      rw [hL, hR]
  | inv x _ ih =>
    obtain ⟨e₁, he₁, he₁Q, z, hz, rfl⟩ := ih
    refine ⟨e₁, he₁, he₁Q, z⁻¹, ⟨Subgroup.inv_mem _ hz.1, Subgroup.inv_mem _ hz.2⟩, ?_⟩
    have hzic := Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hz.2)
    calc (e * e₁ * z)⁻¹ = z⁻¹ * e₁⁻¹ * e⁻¹ := by group
      _ = z⁻¹ * (e₁ * e) := by rw [h.oddT.inv_eq he₁.1, hei, mul_assoc]
      _ = e₁ * e * z⁻¹ := by rw [hzic (e₁ * e)]
      _ = e * e₁ * z⁻¹ := by rw [← (h.commute_of_mem he he₁).eq]

theorem main [Finite G] :
    (∀ y ∈ CFSG.pCore 2 G, (Commute y a ∧ Commute y b ↔ y ∈ Subgroup.center G)) ∧
    ∀ d ∈ D ∩ (S : Set G), ∀ e ∈ D ∩ (S : Set G), ∀ f ∈ D, f * d⁻¹ ∈ CFSG.pCore 2 G →
      ∃! p : G × G, p.1 ∈ D ∧ p.2 ∈ CFSG.pCore 2 G ⊓ Subgroup.center G ∧
        d * e * f = p.1 * p.2 := by
  refine ⟨fun y hy => h.commute_and_iff hy, ?_⟩
  intro d hd e he f hf hfd
  have hQ : IsPGroup 2 (CFSG.pCore 2 G) := isPGroup_pCore
  have hfS : f ∈ D ∩ (S : Set G) := by
    refine ⟨hf, ?_⟩
    have h1 := S.mul_mem (pCore_le hfd) hd.2
    rwa [inv_mul_cancel_right] at h1
  have hdi : d⁻¹ = d := h.oddT.inv_eq hd.1
  have hdfQ : d * f ∈ CFSG.pCore 2 G := by
    have h1 := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem _ hfd d
    have e1 : d * (f * d⁻¹) * d⁻¹ = d * f := by
      calc d * (f * d⁻¹) * d⁻¹ = d * f * (d * d)⁻¹ := by group
        _ = d * f := by rw [h.oddT.mul_self_eq_one hd.1, inv_one, mul_one]
    rwa [e1] at h1
  have hdfe : Commute (d * f) e :=
    ((h.commute_of_mem he hd).mul_right (h.commute_of_mem he hfS)).symm
  obtain ⟨x, hx, w, hwQ, hwe, hwb, hxw⟩ := exists_commutator_mul_of_commute h.oddT h.normal hQ
    he.1 h.b_mem (h.not_commute_b he) hdfQ hdfe
  have hwc : w ∈ Subgroup.center G := h.mem_center_of_commute hwb.symm fun v hv =>
    (h.commute_of_commute he hv hwQ hwe).symm
  obtain ⟨e₁, he₁, -, z₁, hz₁, rfl⟩ := h.exists_eq_mul_of_mem_commutator he hx
  have hwc' := Subgroup.mem_center_iff.mp hwc
  refine ⟨(e₁, z₁ * w), ⟨he₁.1, ⟨(CFSG.pCore 2 G).mul_mem hz₁.1 hwQ,
    (Subgroup.center G).mul_mem hz₁.2 hwc⟩, ?_⟩, ?_⟩
  ·
    have hde : Commute d e := h.commute_of_mem hd he
    show d * e * f = e₁ * (z₁ * w)
    calc d * e * f = e * (d * f) := by rw [hde.eq, mul_assoc]
      _ = e * (e * e₁ * z₁ * w) := by rw [hxw]
      _ = e₁ * (z₁ * w) := by
        rw [show e * (e * e₁ * z₁ * w) = e * e * e₁ * z₁ * w by group,
          h.oddT.mul_self_eq_one he.1, one_mul, mul_assoc]
  · rintro ⟨u, z'⟩ ⟨hu, hz', heq⟩
    have hz'c := Subgroup.mem_center_iff.mp hz'.2
    have hu1 : e₁ = u := by
      refine eq_of_inv_mul_mem_center h.setup he₁.1 hu ?_
      have h1 : e₁ * (z₁ * w) = u * z' := by
        rw [← heq]
        have hde : Commute d e := h.commute_of_mem hd he
        calc e₁ * (z₁ * w) = e * (e * e₁ * z₁ * w) := by
              rw [show e * (e * e₁ * z₁ * w) = e * e * e₁ * z₁ * w by group,
                h.oddT.mul_self_eq_one he.1, one_mul, mul_assoc]
          _ = e * (d * f) := by rw [hxw]
          _ = d * e * f := by rw [hde.eq, mul_assoc]
      have h2 : e₁⁻¹ * u = z₁ * w * z'⁻¹ := by
        calc e₁⁻¹ * u = e₁⁻¹ * (u * z') * z'⁻¹ := by group
          _ = e₁⁻¹ * (e₁ * (z₁ * w)) * z'⁻¹ := by rw [h1]
          _ = z₁ * w * z'⁻¹ := by group
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hz₁.2 hwc) (Subgroup.inv_mem _ hz'.2)
    subst hu1
    have : z' = z₁ * w := by
      have h1 : e₁ * z' = e₁ * (z₁ * w) := by
        rw [← heq]
        have hde : Commute d e := h.commute_of_mem hd he
        calc d * e * f = e * (d * f) := by rw [hde.eq, mul_assoc]
          _ = e * (e * e₁ * z₁ * w) := by rw [hxw]
          _ = e₁ * (z₁ * w) := by
            rw [show e * (e * e₁ * z₁ * w) = e * e * e₁ * z₁ * w by group,
              h.oddT.mul_self_eq_one he.1, one_mul, mul_assoc]
      exact mul_left_cancel h1
    rw [this]

end ThirdKindHyp

namespace OddTransp

theorem oddTranspThirdKind : OddTranspThirdKind := fun _ _ _ _ _ _ _ _ _ h => h.main

end OddTransp

end CFSG.Timmesfeld.Bridge
