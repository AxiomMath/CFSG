module

public import CFSG.Quasithin.MS93.S32Basic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {M T L : Subgroup G}

section CentIn

@[expose] def S5B.centIn (L W Z : Subgroup G) (hZn : L ≤ Subgroup.normalizer (Z : Set G)) :
    Subgroup G where
  carrier := {l | l ∈ L ∧ ∀ w ∈ W, l * w * l⁻¹ * w⁻¹ ∈ Z}
  one_mem' := ⟨L.one_mem, fun w _ => by simp [Z.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨L.mul_mem ha hb, fun w hw => ?_⟩
    have e : a * b * w * (a * b)⁻¹ * w⁻¹ =
        a * (b * w * b⁻¹ * w⁻¹) * a⁻¹ * (a * w * a⁻¹ * w⁻¹) := by group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hZn ha) _).mp (hb' w hw)) (ha' w hw)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨L.inv_mem ha, fun w hw => ?_⟩
    have e : a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ = a⁻¹ * (a * w * a⁻¹ * w⁻¹)⁻¹ * a := by group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hZn (L.inv_mem ha)) _).mp (Z.inv_mem (ha' w hw))
    simpa using this

theorem S5B.le_normalizer_centIn {W Z : Subgroup G} (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hZn : L ≤ Subgroup.normalizer (Z : Set G)) :
    L ≤ Subgroup.normalizer (S5B.centIn L W Z hZn : Set G) := by
  have key : ∀ g ∈ L, ∀ x ∈ S5B.centIn L W Z hZn, g * x * g⁻¹ ∈ S5B.centIn L W Z hZn := by
    rintro g hg x ⟨hx, hx'⟩
    refine ⟨L.mul_mem (L.mul_mem hg hx) (L.inv_mem hg), fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hWn (L.inv_mem hg)) w).mp hw
      simpa using this
    have e : g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ * w⁻¹ =
        g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hZn hg) _).mp (hx' _ hw')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (L.inv_mem hg) _ hx
  simpa [mul_assoc] using this

end CentIn

section NormalL

variable [Finite G]

theorem S5B.commutator_le_pCoreOf_of_normal (h : PUHyp M T L) {K : Subgroup G} (hKL : K ≤ L)
    (hKn : L ≤ Subgroup.normalizer (K : Set G)) (hLK : ¬ L ≤ K) : ⁅K, L⁆ ≤ pCoreOf 2 L := by
  have hNn : L ≤ Subgroup.normalizer (K : Set G) := hKn
  set D : Subgroup ↥L := K.subgroupOf L with hD
  have hDn : D.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hD, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hNn g.2) n).mp hn
    simpa using this
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hHn : (D.map π).Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple h.quasisimple (D.map π)
    with hc | htop
  · rw [Subgroup.commutator_le]
    intro x hx l hl
    have hxD : (⟨x, hKL hx⟩ : ↥L) ∈ D := by
      rw [hD, Subgroup.mem_subgroupOf]
      exact hx
    have hcen := hc (Subgroup.mem_map_of_mem π hxD)
    have hk : π ⁅(⟨x, hKL hx⟩ : ↥L), (⟨l, hl⟩ : ↥L)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcen _).symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact mem_pCoreOf_of_mem_pCore_two hk
  · exfalso
    apply hLK
    have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
    have htopD : D = ⊤ := by
      refine eq_top_of_perfect_of_two D fun l => ?_
      have hl : π l ∈ D.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨d, hd, hdl⟩ := hl
      refine ⟨d, hd, ?_⟩
      have hmem : d⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdl
        exact hdl
      obtain ⟨e, he⟩ := isPGroup_pCore_two L ⟨d⁻¹ * l, hmem⟩
      exact ⟨e, congrArg Subtype.val he⟩
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ D := by rw [htopD]; exact Subgroup.mem_top _
    rw [hD, Subgroup.mem_subgroupOf] at this
    exact this

theorem S5B.not_L_le_pCoreOf (h : PUHyp M T L) : ¬ L ≤ pCoreOf 2 M := by
  intro hL
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  have hp : IsPGroup 2 ↥L :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 h.L_ne_bot
  exact Group.IsPerfect.not_isNilpotent ↥L hp.isNilpotent

theorem S5B.commutator_le_of_two_elt (h : PUHyp M T L) {W Z : Subgroup G}
    (hWn : L ≤ Subgroup.normalizer (W : Set G)) (hZn : L ≤ Subgroup.normalizer (Z : Set G))
    {y : G} (hyM : y ∈ M) (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1) (hyO : y ∉ pCoreOf 2 M)
    (hyZ : y ∈ Subgroup.normalizer (Z : Set G)) (hyW : ∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ Z) :
    ⁅W, L⁆ ≤ Z := by
  set K := S5B.centIn L W Z hZn
  by_cases hLK : L ≤ K
  · rw [Subgroup.commutator_le]
    intro w hw l hl
    have := Z.inv_mem ((hLK hl).2 w hw)
    have e : ⁅w, l⁆ = (l * w * l⁻¹ * w⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact this
  exfalso
  have hKK : ⁅K, L⁆ ≤ pCoreOf 2 L :=
    S5B.commutator_le_pCoreOf_of_normal h (fun _ hx => hx.1) (S5B.le_normalizer_centIn hWn hZn) hLK
  have hQn : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf M
  have hKR : ∀ k ∈ K, k ∈ relCent M L (pCoreOf 2 M) hQn h.le_normalizer := by
    intro k hk
    refine ⟨h.L_le hk.1, fun l hl => ?_⟩
    exact pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer
      (hKK (Subgroup.commutator_mem_commutator hk hl))
  apply hyO
  refine h.mem_pCoreOf_of_rel le_normalizer_relCent
    (not_le_relCent h.perfect (S5B.not_L_le_pCoreOf h)) hyM hy2
    fun l hl => hKR _ ⟨?_, fun w hw => ?_⟩
  ·
    have hlM := h.L_le hl
    have hyl : y * l * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer hyM) l).mp hl
    rw [commutatorElement_def]
    exact L.mul_mem hyl (L.inv_mem hl)
  ·
    have hw₁ : l⁻¹ * w * l ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hWn (L.inv_mem hl)) w).mp hw
      simpa using this
    set w₁ := l⁻¹ * w * l
    have hz₁ : y⁻¹ * w₁ * y * w₁⁻¹ ∈ Z := by
      have e : y⁻¹ * w₁ * y * w₁⁻¹ = y⁻¹ * (y * w₁ * y⁻¹ * w₁⁻¹)⁻¹ * y := by group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyZ) _).mp
        (Z.inv_mem (hyW w₁ hw₁))
      simpa using this
    set z₁ := y⁻¹ * w₁ * y * w₁⁻¹
    have hz₂ : l * z₁ * l⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZn hl) _).mp hz₁
    have e : ⁅y, l⁆ * w * ⁅y, l⁆⁻¹ * w⁻¹ = (y * (l * z₁ * l⁻¹) * y⁻¹) * (y * w * y⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def, z₁, w₁]
      group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hyZ _).mp hz₂) (hyW w hw)

end NormalL

namespace S5B

section PreM

variable (hTM : T ≤ M)

@[expose] def preM (W : Subgroup (puAmalgam hTM).Universal) : Subgroup G :=
  (W.comap (puAmalgam hTM).ofA).map M.subtype

theorem preM_le (W : Subgroup (puAmalgam hTM).Universal) : preM hTM W ≤ M :=
  Subgroup.map_subtype_le _

theorem mem_preM {W : Subgroup (puAmalgam hTM).Universal} (m : ↥M) :
    (m : G) ∈ preM hTM W ↔ (puAmalgam hTM).ofA m ∈ W := by
  constructor
  · rintro ⟨m', hm', he⟩
    rw [Subtype.ext he] at hm'
    exact hm'
  · intro hm
    exact ⟨m, hm, rfl⟩

theorem imM_preM {W : Subgroup (puAmalgam hTM).Universal}
    (hW : W ≤ stab (puAmalgam hTM) (baseA _)) : imM hTM (preM hTM W) = W := by
  rw [puAmalgam.stab_baseA, imM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at hW
  rw [imM, preM, PU.map_subtype_subgroupOf, Subgroup.map_comap_eq, inf_eq_right.2 hW]

theorem le_normalizer_preM {K : Subgroup G} (hKM : K ≤ M) {W : Subgroup (puAmalgam hTM).Universal}
    (hKW : imM hTM K ≤ Subgroup.normalizer (W : Set (puAmalgam hTM).Universal)) :
    K ≤ Subgroup.normalizer (preM hTM W : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ preM hTM W, k * x * k⁻¹ ∈ preM hTM W := by
    rintro k hk _ ⟨m, hm, rfl⟩
    have hkW := hKW ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hkW _).1 hm
    refine (mem_preM hTM (⟨k, hKM hk⟩ * m * (⟨k, hKM hk⟩)⁻¹)).2 ?_
    simpa [map_mul, map_inv] using this
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key k hk x, fun hx => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

theorem commutator_imM_le_iff {A B C : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    ⁅imM hTM A, imM hTM B⁆ ≤ imM hTM C ↔ ⁅A, B⁆ ≤ C := by
  rw [← imM_commutator hTM hA hB, imM_le_imM_iff hTM (commutator_le_of_le hA hB)]

end PreM

section L2

variable [Finite G]

theorem finite_imM (hTM : T ≤ M) (K : Subgroup G) : Finite ↥(imM hTM K) :=
  Finite.of_surjective (fun x : ↥(K.subgroupOf M) =>
    (⟨_, Subgroup.mem_map_of_mem (puAmalgam hTM).ofA x.2⟩ : ↥(imM hTM K)))
    (by rintro ⟨_, ⟨m, hm, rfl⟩⟩; exact ⟨⟨m, hm⟩, rfl⟩)

theorem card_qv_eq (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    Nat.card (Qv (puAmalgam h.le) δ) = Nat.card (Qv (puAmalgam h.le) (baseA _)) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  rw [qv_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective]

end L2

end S5B

end CFSG.Quasithin.MS93
