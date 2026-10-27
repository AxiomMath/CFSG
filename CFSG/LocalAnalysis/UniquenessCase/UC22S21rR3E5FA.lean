module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3B
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XA
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

def uc22r3e5_innerOn {Q : Type} [Group Q] (F : Subgroup Q) : Subgroup Q where
  carrier := {g | ∃ y ∈ F, ∀ x ∈ F, g * x * g⁻¹ = y * x * y⁻¹}
  one_mem' := ⟨1, F.one_mem, by intro x _; rfl⟩
  mul_mem' := by
    rintro g h ⟨y, hy, hgy⟩ ⟨z, hz, hhz⟩
    have hgN : ∀ x ∈ F, g * x * g⁻¹ ∈ F := fun x hx => by
      rw [hgy x hx]; exact F.mul_mem (F.mul_mem hy hx) (F.inv_mem hy)
    refine ⟨g * z * g⁻¹ * y, F.mul_mem (hgN z hz) hy, fun x hx => ?_⟩
    calc (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group
      _ = g * (z * x * z⁻¹) * g⁻¹ := by rw [hhz x hx]
      _ = (g * z * g⁻¹) * (g * x * g⁻¹) * (g * z * g⁻¹)⁻¹ := by group
      _ = (g * z * g⁻¹ * y) * x * (g * z * g⁻¹ * y)⁻¹ := by rw [hgy x hx]; group
  inv_mem' := by
    rintro g ⟨y, hy, hgy⟩
    refine ⟨y⁻¹, F.inv_mem hy, fun x hx => ?_⟩
    have h2 : g * (y⁻¹ * x * y) * g⁻¹ = x := by
      rw [hgy (y⁻¹ * x * y) (F.mul_mem (F.mul_mem (F.inv_mem hy) hx) hy)]
      group
    have h3 : g⁻¹ * x * g = y⁻¹ * x * y := by
      calc g⁻¹ * x * g = g⁻¹ * (g * (y⁻¹ * x * y) * g⁻¹) * g := by rw [h2]
        _ = y⁻¹ * x * y := by group
    simpa using h3

theorem uc22r3e5_mem_innerOn_of_normalizer {Q : Type} [Group Q] {F : Subgroup Q} {g : Q}
    (hg : g ∈ normalizer (F : Set Q))
    (h : F.normalizerMonoidHom ⟨g, hg⟩ ∈ (MulAut.conj : ↥F →* MulAut ↥F).range) :
    g ∈ uc22r3e5_innerOn F := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y, y.2, fun x hx => ?_⟩
  have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe F ⟨g, hg⟩ ⟨x, hx⟩
  rw [← hy] at h1
  simpa [MulAut.conj_apply] using h1.symm

theorem uc22r3e5_normalizerMonoidHom_mem_range_of_mem_innerOn {Q : Type} [Group Q]
    {F : Subgroup Q} {g : Q} (hg : g ∈ uc22r3e5_innerOn F)
    (hN : g ∈ normalizer (F : Set Q)) :
    F.normalizerMonoidHom ⟨g, hN⟩ ∈ (MulAut.conj : ↥F →* MulAut ↥F).range := by
  obtain ⟨y, hy, hgy⟩ := hg
  refine ⟨⟨y, hy⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  exact (hgy x x.2).symm

theorem uc22r3e5_barImage_map_conj {M L : Subgroup G} {m : ↥M} :
    barImage M (L.map (MulAut.conj (m : G)).toMonoidHom) =
      (barImage M L).map (MulAut.conj (uc22p21cPi M m)).toMonoidHom := by
  ext q
  constructor
  · intro hq
    rw [uc22p21c_mem_barImage] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.1 hy
    have hly' : (y : G) = (m : G) * l * (m : G)⁻¹ := by
      simpa [MulAut.conj_apply] using hly.symm
    have hlM : l ∈ M := by
      have h5 : l = (m : G)⁻¹ * (y : G) * (m : G) := by rw [hly']; group
      rw [h5]
      exact M.mul_mem (M.mul_mem (M.inv_mem m.2) y.2) m.2
    refine Subgroup.mem_map.2 ⟨uc22p21cPi M ⟨l, hlM⟩,
      uc22p21c_mem_barImage.2 ⟨⟨l, hlM⟩, hl, rfl⟩, ?_⟩
    show (MulAut.conj (uc22p21cPi M m)) (uc22p21cPi M ⟨l, hlM⟩) = uc22p21cPi M y
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg (uc22p21cPi M) (Subtype.ext hly'.symm)
  · intro hq
    obtain ⟨z, hz, hqz⟩ := Subgroup.mem_map.1 hq
    rw [uc22p21c_mem_barImage] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine uc22p21c_mem_barImage.2 ⟨⟨(m : G) * (y : G) * (m : G)⁻¹,
      M.mul_mem (M.mul_mem m.2 y.2) (M.inv_mem m.2)⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.2 ⟨(y : G), hy, by simp⟩
    · rw [← hqz]
      show uc22p21cPi M ⟨(m : G) * (y : G) * (m : G)⁻¹, _⟩ =
        (MulAut.conj (uc22p21cPi M m)) (uc22p21cPi M y)
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      exact congrArg (uc22p21cPi M) (Subtype.ext rfl)

theorem uc22r3e5_conjSetOf_barImage {M L : Subgroup G} :
    conjSetOf (⊤ : Subgroup (Bar2 M)) (barImage M L) = barImage M '' conjSetOf M L := by
  ext P
  constructor
  · rintro ⟨x, -, rfl⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) x
    exact ⟨L.map (MulAut.conj (m : G)).toMonoidHom, ⟨(m : G), m.2, rfl⟩,
      (uc22r3e5_barImage_map_conj (M := M) (L := L) (m := m))⟩
  · rintro ⟨L', ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨uc22p21cPi M ⟨m, hm⟩, Subgroup.mem_top _,
      (uc22r3e5_barImage_map_conj (M := M) (L := L) (m := ⟨m, hm⟩))⟩

theorem uc22r3e5_conjSetOf_barImage_L {M L K : Subgroup G}
    (hset : conjSetOf M L = {L, K}) :
    conjSetOf (⊤ : Subgroup (Bar2 M)) (barImage M L) = {barImage M L, barImage M K} := by
  rw [uc22r3e5_conjSetOf_barImage, hset]
  ext P
  simp

theorem uc22r3e5_conjSetOf_barImage_K {M L K : Subgroup G}
    (hset : conjSetOf M L = {L, K}) :
    conjSetOf (⊤ : Subgroup (Bar2 M)) (barImage M K) = {barImage M L, barImage M K} := by
  have hmemK : K ∈ conjSetOf M L := by rw [hset]; simp
  rw [uc22r3e5_conjSetOf_barImage, uc22p2214_conjSetOf_eq hmemK, hset]
  ext P
  simp

theorem uc22r3e5_map_conj_pair_L {M L K : Subgroup G}
    (hset : conjSetOf M L = {L, K}) (g : Bar2 M) :
    (barImage M L).map (MulAut.conj g).toMonoidHom = barImage M L ∨
      (barImage M L).map (MulAut.conj g).toMonoidHom = barImage M K := by
  have h : (barImage M L).map (MulAut.conj g).toMonoidHom ∈
      conjSetOf (⊤ : Subgroup (Bar2 M)) (barImage M L) := ⟨g, Subgroup.mem_top _, rfl⟩
  rw [uc22r3e5_conjSetOf_barImage_L hset] at h
  simpa using h

theorem uc22r3e5_map_conj_pair_K {M L K : Subgroup G}
    (hset : conjSetOf M L = {L, K}) (g : Bar2 M) :
    (barImage M K).map (MulAut.conj g).toMonoidHom = barImage M L ∨
      (barImage M K).map (MulAut.conj g).toMonoidHom = barImage M K := by
  have h : (barImage M K).map (MulAut.conj g).toMonoidHom ∈
      conjSetOf (⊤ : Subgroup (Bar2 M)) (barImage M K) := ⟨g, Subgroup.mem_top _, rfl⟩
  rw [uc22r3e5_conjSetOf_barImage_K hset] at h
  simpa using h

theorem uc22r3e5_innerOn_conj_mem {Q : Type} [Group Q] {F Z : Subgroup Q} {n g : Q}
    (hZ : Z = F.map (MulAut.conj g⁻¹).toMonoidHom)
    (hn : n ∈ uc22r3e5_innerOn Z) : g * n * g⁻¹ ∈ uc22r3e5_innerOn F := by
  obtain ⟨z, hz, hzn⟩ := hn
  have hzF : g * z * g⁻¹ ∈ F := by
    have hz' : z ∈ F.map (MulAut.conj g⁻¹).toMonoidHom := hZ ▸ hz
    obtain ⟨f, hf, hfz⟩ := Subgroup.mem_map.1 hz'
    have hzf : z = (g⁻¹ : Q) * f * g := by
      simpa [MulAut.conj_apply] using hfz.symm
    have h5 : g * z * g⁻¹ = f := by rw [hzf]; group
    rw [h5]; exact hf
  refine ⟨g * z * g⁻¹, hzF, fun x hx => ?_⟩
  have hxZ : g⁻¹ * x * g ∈ Z := by
    rw [hZ]
    exact Subgroup.mem_map.2 ⟨x, hx, by simp⟩
  have h1 := hzn (g⁻¹ * x * g) hxZ
  calc (g * n * g⁻¹) * x * (g * n * g⁻¹)⁻¹
      = g * (n * (g⁻¹ * x * g) * n⁻¹) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * x * g) * z⁻¹) * g⁻¹ := by rw [h1]
    _ = (g * z * g⁻¹) * x * (g * z * g⁻¹)⁻¹ := by group

theorem uc22r3e5_pairKernel_normal {M L K : Subgroup G}
    (hset : conjSetOf M L = {L, K}) :
    (uc22r3e5_innerOn (barImage M L) ⊓ uc22r3e5_innerOn (barImage M K)).Normal := by
  constructor
  intro n hn g
  obtain ⟨hn₀, hn₁⟩ := Subgroup.mem_inf.1 hn
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rcases uc22r3e5_map_conj_pair_L hset g⁻¹ with h | h
    · exact uc22r3e5_innerOn_conj_mem h.symm hn₀
    · exact uc22r3e5_innerOn_conj_mem h.symm hn₁
  · rcases uc22r3e5_map_conj_pair_K hset g⁻¹ with h | h
    · exact uc22r3e5_innerOn_conj_mem h.symm hn₀
    · exact uc22r3e5_innerOn_conj_mem h.symm hn₁

theorem uc22r3e5_comm_mem_inner_of_outer {X : Type} [Group X]
    (h : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer X, a * b = b * a) :
    ∀ α β : MulAut X, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  intro α β
  have h1 : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
      (α * β * α⁻¹ * β⁻¹) = 1 := by
    have h2 := h (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X) α)
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X) β)
    simp only [map_mul, map_inv]
    rw [h2]
    group
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem uc22r3e5_comm_inner_barImage {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    ∀ α β : MulAut ↥(barImage M L), α * β * α⁻¹ * β⁻¹ ∈
      (MulAut.conj : ↥(barImage M L) →* MulAut ↥(barImage M L)).range := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (L := M) (K := L) hL
  have hbar : ∀ α β : MulAut (Bar2 L), α * β * α⁻¹ * β⁻¹ ∈
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    rcases hS with hL2 | hSz
    · exact uc22r3e5_comm_mem_inner_of_outer (uc22p22g_outer_comm hL2)
    · intro α β
      set e' := (quotCenterEquivBar2 hL.2.2 (center_eq_bot_of_isSz hL.2.2 hSz)).symm with he'
      have h := uc22r3g_comm_of_isSz hL hSz (MulAut.congr e' α) (MulAut.congr e' β)
      refine uc22p2214_out_mem_of_congr e' ?_
      convert h using 2; simp [MulAut.congr_apply, MulEquiv.map_mul, MulEquiv.map_inv]
  intro α β
  refine uc22p2214_out_mem_of_congr e.symm ?_
  have h := hbar (MulAut.congr e.symm α) (MulAut.congr e.symm β)
  convert h using 2; simp [MulAut.congr_apply, MulEquiv.map_mul, MulEquiv.map_inv]

theorem uc22r3e5_perm_pair {Q : Type} [Group Q] {F₀ F₁ : Subgroup Q}
    (hpair₀ : ∀ g : Q, F₀.map (MulAut.conj g).toMonoidHom = F₀ ∨
      F₀.map (MulAut.conj g).toMonoidHom = F₁)
    (hpair₁ : ∀ g : Q, F₁.map (MulAut.conj g).toMonoidHom = F₀ ∨
      F₁.map (MulAut.conj g).toMonoidHom = F₁)
    (hne : F₀ ≠ F₁) (g : Q) :
    (F₀.map (MulAut.conj g).toMonoidHom = F₀ ∧ F₁.map (MulAut.conj g).toMonoidHom = F₁) ∨
      (F₀.map (MulAut.conj g).toMonoidHom = F₁ ∧
        F₁.map (MulAut.conj g).toMonoidHom = F₀) := by
  have hinj := Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rcases hpair₀ g with h₀ | h₀ <;> rcases hpair₁ g with h₁ | h₁
  · exact absurd (hinj (h₁.trans h₀.symm)).symm hne
  · exact Or.inl ⟨h₀, h₁⟩
  · exact Or.inr ⟨h₀, h₁⟩
  · exact absurd (hinj (h₀.trans h₁.symm)) hne

theorem uc22r3e5_pair_perm {M L K : Subgroup G} (hset : conjSetOf M L = {L, K}) :
    ∀ g : Bar2 M,
      ((barImage M L).map (MulAut.conj g).toMonoidHom = barImage M L ∧
        (barImage M K).map (MulAut.conj g).toMonoidHom = barImage M K) ∨
      ((barImage M L).map (MulAut.conj g).toMonoidHom = barImage M K ∧
        (barImage M K).map (MulAut.conj g).toMonoidHom = barImage M L) := by
  by_cases hne : barImage M L = barImage M K
  · intro g
    have h := uc22r3e5_map_conj_pair_L hset g
    rw [hne] at h ⊢
    exact Or.inl ⟨h.elim id id, h.elim id id⟩
  · exact uc22r3e5_perm_pair (uc22r3e5_map_conj_pair_L hset)
      (uc22r3e5_map_conj_pair_K hset) hne

theorem uc22r3e5_map_conj_mul {Q : Type} [Group Q] (A : Subgroup Q) (x y : Q) :
    A.map (MulAut.conj (x * y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [show (MulAut.conj (x * y)).toMonoidHom =
      ((MulAut.conj x).toMonoidHom).comp ((MulAut.conj y).toMonoidHom) from by
    ext z
    simp [map_mul]]
  exact (Subgroup.map_map A (MulAut.conj x).toMonoidHom (MulAut.conj y).toMonoidHom).symm

theorem uc22r3e5_map_conj_inv {Q : Type} [Group Q] {A B : Subgroup Q} {x : Q}
    (h : A.map (MulAut.conj x).toMonoidHom = B) :
    B.map (MulAut.conj x⁻¹).toMonoidHom = A := by
  rw [← h, uc22p22d_map_conj_map_conj A x x⁻¹, inv_mul_cancel]
  have h1 : (MulAut.conj (1 : Q)).toMonoidHom = MonoidHom.id Q := by
    rw [map_one (MulAut.conj : Q →* MulAut Q)]
    rfl
  rw [h1]
  exact Subgroup.map_id A

theorem uc22r3e5_map_conj_commutator {Q : Type} [Group Q] {F₀ F₁ : Subgroup Q}
    (hperm : ∀ g : Q,
      (F₀.map (MulAut.conj g).toMonoidHom = F₀ ∧ F₁.map (MulAut.conj g).toMonoidHom = F₁) ∨
      (F₀.map (MulAut.conj g).toMonoidHom = F₁ ∧
        F₁.map (MulAut.conj g).toMonoidHom = F₀))
    (u v : Q) : F₀.map (MulAut.conj ⁅u, v⁆).toMonoidHom = F₀ := by
  rw [commutatorElement_def]
  rw [uc22r3e5_map_conj_mul, uc22r3e5_map_conj_mul, uc22r3e5_map_conj_mul]
  rcases hperm u with ⟨hu₀, hu₁⟩ | ⟨hu₀, hu₁⟩ <;> rcases hperm v with ⟨hv₀, hv₁⟩ | ⟨hv₀, hv₁⟩
  · rw [show F₀.map (MulAut.conj v⁻¹).toMonoidHom = F₀ from
        uc22r3e5_map_conj_inv hv₀,
      show F₀.map (MulAut.conj u⁻¹).toMonoidHom = F₀ from uc22r3e5_map_conj_inv hu₀,
      hv₀, hu₀]
  · rw [show F₀.map (MulAut.conj v⁻¹).toMonoidHom = F₁ from
        uc22r3e5_map_conj_inv hv₁,
      show F₁.map (MulAut.conj u⁻¹).toMonoidHom = F₁ from uc22r3e5_map_conj_inv hu₁,
      hv₁, hu₀]
  · rw [show F₀.map (MulAut.conj v⁻¹).toMonoidHom = F₀ from
        uc22r3e5_map_conj_inv hv₀,
      show F₀.map (MulAut.conj u⁻¹).toMonoidHom = F₁ from uc22r3e5_map_conj_inv hu₁,
      hv₁, hu₁]
  · rw [show F₀.map (MulAut.conj v⁻¹).toMonoidHom = F₁ from
        uc22r3e5_map_conj_inv hv₁,
      show F₁.map (MulAut.conj u⁻¹).toMonoidHom = F₀ from uc22r3e5_map_conj_inv hu₀,
      hv₀, hu₁]

theorem uc22r3e5_commutator_le_pairNormalizer {Q : Type} [Group Q] {F₀ F₁ : Subgroup Q}
    (hperm : ∀ g : Q,
      (F₀.map (MulAut.conj g).toMonoidHom = F₀ ∧ F₁.map (MulAut.conj g).toMonoidHom = F₁) ∨
      (F₀.map (MulAut.conj g).toMonoidHom = F₁ ∧
        F₁.map (MulAut.conj g).toMonoidHom = F₀)) :
    ⁅(⊤ : Subgroup Q), ⊤⁆ ≤
      Subgroup.normalizer (F₀ : Set Q) ⊓ Subgroup.normalizer (F₁ : Set Q) := by
  rw [Subgroup.commutator_le]
  intro u _ v _
  have hswap : ∀ g : Q,
      (F₁.map (MulAut.conj g).toMonoidHom = F₁ ∧ F₀.map (MulAut.conj g).toMonoidHom = F₀) ∨
      (F₁.map (MulAut.conj g).toMonoidHom = F₀ ∧
        F₀.map (MulAut.conj g).toMonoidHom = F₁) := by
    intro g
    rcases hperm g with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨b, a⟩
    · exact Or.inr ⟨b, a⟩
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact uc22r3e5_map_conj_commutator hperm u v
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact uc22r3e5_map_conj_commutator hswap u v

theorem uc22r3e5_commutator_mem_pairKernel {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ calC M) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {u v : Bar2 M}
    (hu : u ∈ Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
      Subgroup.normalizer (barImage M K : Set (Bar2 M)))
    (hv : v ∈ Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
      Subgroup.normalizer (barImage M K : Set (Bar2 M))) :
    ⁅u, v⁆ ∈ uc22r3e5_innerOn (barImage M L) ⊓ uc22r3e5_innerOn (barImage M K) := by
  obtain ⟨hu₀, hu₁⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hv₀, hv₁⟩ := Subgroup.mem_inf.1 hv
  have hKS := uc22s21ru4e_shape_conj (K := K) (by rw [hset]; simp) hS
  have hN₀ : ⁅u, v⁆ ∈ Subgroup.normalizer (barImage M L : Set (Bar2 M)) := by
    rw [commutatorElement_def]
    let H := Subgroup.normalizer (barImage M L : Set (Bar2 M))
    exact H.mul_mem (H.mul_mem (H.mul_mem hu₀ hv₀) (H.inv_mem hu₀)) (H.inv_mem hv₀)
  have hN₁ : ⁅u, v⁆ ∈ Subgroup.normalizer (barImage M K : Set (Bar2 M)) := by
    rw [commutatorElement_def]
    let H := Subgroup.normalizer (barImage M K : Set (Bar2 M))
    exact H.mul_mem (H.mul_mem (H.mul_mem hu₁ hv₁) (H.inv_mem hu₁)) (H.inv_mem hv₁)
  have key : ∀ (P : Subgroup G) (hP : P ∈ calC M) (hPS : IsL2 (Bar2 P) n ∨ IsSz (Bar2 P) n)
      (hx : u ∈ Subgroup.normalizer (barImage M P : Set (Bar2 M)))
      (hy : v ∈ Subgroup.normalizer (barImage M P : Set (Bar2 M)))
      (hN : ⁅u, v⁆ ∈ Subgroup.normalizer (barImage M P : Set (Bar2 M))),
      ⁅u, v⁆ ∈ uc22r3e5_innerOn (barImage M P) := by
    intro P hP hPS hx hy hN
    refine uc22r3e5_mem_innerOn_of_normalizer hN ?_
    have h := uc22r3e5_comm_inner_barImage hP hPS
      (Subgroup.normalizerMonoidHom (barImage M P) ⟨u, hx⟩)
      (Subgroup.normalizerMonoidHom (barImage M P) ⟨v, hy⟩)
    have h1 : Subgroup.normalizerMonoidHom (barImage M P) ⟨⁅u, v⁆, hN⟩ =
        (Subgroup.normalizerMonoidHom (barImage M P) ⟨u, hx⟩) *
        (Subgroup.normalizerMonoidHom (barImage M P) ⟨v, hy⟩) *
        ((Subgroup.normalizerMonoidHom (barImage M P) ⟨u, hx⟩))⁻¹ *
        ((Subgroup.normalizerMonoidHom (barImage M P) ⟨v, hy⟩))⁻¹ := by
      rw [show (⟨⁅u, v⁆, hN⟩ : ↥(Subgroup.normalizer (barImage M P : Set (Bar2 M)))) =
          ⟨u, hx⟩ * ⟨v, hy⟩ * ⟨u, hx⟩⁻¹ * ⟨v, hy⟩⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rwa [h1]
  exact Subgroup.mem_inf.2 ⟨key L hL hS hu₀ hv₀ hN₀, key K hK hKS hu₁ hv₁ hN₁⟩

theorem uc22r3e5_commutator_le_pairKernel {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ calC M) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    ⁅(Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
        Subgroup.normalizer (barImage M K : Set (Bar2 M))),
      (Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
        Subgroup.normalizer (barImage M K : Set (Bar2 M)))⁆ ≤
      uc22r3e5_innerOn (barImage M L) ⊓ uc22r3e5_innerOn (barImage M K) := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  exact uc22r3e5_commutator_mem_pairKernel hL hK hset hS hu hv

theorem uc22r3e5_isSolvable_quotient {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ calC M) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    [hF : (uc22r3e5_innerOn (barImage M L) ⊓ uc22r3e5_innerOn (barImage M K)).Normal] :
    Group.IsSolvable (Bar2 M ⧸
      (uc22r3e5_innerOn (barImage M L) ⊓ uc22r3e5_innerOn (barImage M K))) := by
  set Fbar : Subgroup (Bar2 M) :=
    uc22r3e5_innerOn (barImage M L) ⊓ uc22r3e5_innerOn (barImage M K) with hFbar
  have hMN : ⁅(⊤ : Subgroup (Bar2 M)), ⊤⁆ ≤
      Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
        Subgroup.normalizer (barImage M K : Set (Bar2 M)) :=
    uc22r3e5_commutator_le_pairNormalizer (uc22r3e5_pair_perm hset)
  have hNN : ⁅(Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
        Subgroup.normalizer (barImage M K : Set (Bar2 M))),
      (Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
        Subgroup.normalizer (barImage M K : Set (Bar2 M)))⁆ ≤ Fbar :=
    uc22r3e5_commutator_le_pairKernel hL hK hset hS
  have hstep : derivedSeries (Bar2 M ⧸ Fbar) 1 =
      (⁅(⊤ : Subgroup (Bar2 M)), (⊤ : Subgroup (Bar2 M))⁆).map (QuotientGroup.mk' Fbar) := by
    rw [derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Fbar)]
  refine ⟨2, ?_⟩
  rw [derivedSeries_succ, hstep, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']
  calc ⁅⁅(⊤ : Subgroup (Bar2 M)), (⊤ : Subgroup (Bar2 M))⁆,
        ⁅(⊤ : Subgroup (Bar2 M)), (⊤ : Subgroup (Bar2 M))⁆⁆
      ≤ ⁅Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
          Subgroup.normalizer (barImage M K : Set (Bar2 M)),
        Subgroup.normalizer (barImage M L : Set (Bar2 M)) ⊓
          Subgroup.normalizer (barImage M K : Set (Bar2 M))⁆ :=
      Subgroup.commutator_mono hMN hMN
    _ ≤ Fbar := hNN

theorem uc22r3e5_normalizer_map_subtype {X : Type} [Group X] {F : Subgroup X}
    (Q : Subgroup ↥F) :
    Subgroup.normalizer (Q.map F.subtype : Set X) ⊓ F =
      (Subgroup.normalizer (Q : Set ↥F)).map F.subtype := by
  ext x
  constructor
  · rintro ⟨hxN, hxF⟩
    have hxN' := Subgroup.mem_normalizer_iff.1 hxN
    refine Subgroup.mem_map.2 ⟨⟨x, hxF⟩, Subgroup.mem_normalizer_iff.2 (fun q => ?_), rfl⟩
    have h1 := hxN' (q : X)
    have e1 : ((q : X) ∈ Q.map F.subtype) ↔ q ∈ Q := by
      constructor
      · rintro ⟨y, hy, hyq⟩
        exact (Subtype.ext hyq) ▸ hy
      · intro hq
        exact ⟨q, hq, rfl⟩
    have e2 : (x * (q : X) * x⁻¹ ∈ Q.map F.subtype) ↔
        (⟨x, hxF⟩ * q * ⟨x, hxF⟩⁻¹ ∈ Q) := by
      constructor
      · rintro ⟨y, hy, hyq⟩
        have h2 : (⟨x, hxF⟩ * q * ⟨x, hxF⟩⁻¹ : ↥F) = y := Subtype.ext hyq.symm
        rwa [h2]
      · intro hq
        exact ⟨⟨x, hxF⟩ * q * ⟨x, hxF⟩⁻¹, hq, rfl⟩
    rw [e1, e2] at h1
    exact h1
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Subgroup.mem_normalizer_iff.2 (fun z => ?_), y.2⟩
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨y * a * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy a).1 ha, rfl⟩
    · rintro ⟨b, hb, hbz⟩
      refine ⟨y⁻¹ * b * y⁻¹⁻¹,
        (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Q : Set ↥F)).inv_mem hy) b).1 hb, ?_⟩
      have h3 : (b : X) = (y : X) * z * (y : X)⁻¹ := hbz
      show (y : X)⁻¹ * (b : X) * ((y : X)⁻¹)⁻¹ = z
      rw [h3]
      group

theorem uc22r3e5_isSolvable_normalizer_sylow {X : Type} [Group X] [Finite X]
    (Q : Sylow 2 X) : Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup X) : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NQ := Subgroup.normalizer ((Q : Subgroup X) : Set X) with hNQ
  have hQle : (Q : Subgroup X) ≤ NQ := Subgroup.le_normalizer
  have hrel : (Q : Subgroup X).relIndex NQ ∣ (Q : Subgroup X).index := by
      have h := Subgroup.relIndex_mul_relIndex (Q : Subgroup X) NQ ⊤ hQle le_top
      rw [Subgroup.relIndex_top_right (Q : Subgroup X), Subgroup.relIndex_top_right NQ] at h
      exact ⟨NQ.index, h.symm⟩
  have hodd : Odd (Nat.card (↥NQ ⧸ ((Q : Subgroup X)).subgroupOf NQ)) := by
    have h2 : ¬ 2 ∣ (Q : Subgroup X).relIndex NQ :=
      fun h => Q.not_dvd_index (h.trans hrel)
    have h3 : (((Q : Subgroup X)).subgroupOf NQ).index = (Q : Subgroup X).relIndex NQ := rfl
    rw [show Nat.card (↥NQ ⧸ ((Q : Subgroup X)).subgroupOf NQ) =
      (((Q : Subgroup X)).subgroupOf NQ).index from rfl, h3]
    exact Nat.odd_iff.2 (by omega)
  have : Group.IsSolvable ↥(((Q : Subgroup X)).subgroupOf NQ) :=
    CFSG.GorensteinWalter.isSolvable_of_isPGroup
      (Q.isPGroup'.comap_of_injective NQ.subtype NQ.subtype_injective)
  have : Group.IsSolvable (↥NQ ⧸ ((Q : Subgroup X)).subgroupOf NQ) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range (((Q : Subgroup X)).subgroupOf NQ).subtype
    (QuotientGroup.mk' (((Q : Subgroup X)).subgroupOf NQ)) (by simp)

theorem uc22r3e5_isSolvable_normalizer_inf {X : Type} [Group X] [Finite X]
    {F : Subgroup X} [_hF : F.Normal] (Q : Sylow 2 ↥F) :
    Group.IsSolvable ↥(Subgroup.normalizer (((Q : Subgroup ↥F)).map F.subtype : Set X) ⊓ F) := by
  rw [uc22r3e5_normalizer_map_subtype (Q : Subgroup ↥F)]
  have hNQ : Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup ↥F) : Set ↥F)) :=
    uc22r3e5_isSolvable_normalizer_sylow Q
  let φ : ↥(Subgroup.normalizer ((Q : Subgroup ↥F) : Set ↥F)) →*
      ↥((Subgroup.normalizer ((Q : Subgroup ↥F) : Set ↥F)).map F.subtype) :=
    { toFun := fun x => ⟨F.subtype x, Subgroup.mem_map.2 ⟨x, x.2, rfl⟩⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  exact Group.isSolvable_of_surjective (f := φ) (fun y => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

private theorem uc22r3e5_isSolvable_normalizer {M : Subgroup G} {F : Subgroup (Bar2 M)}
    [hF : F.Normal] (hsol : Group.IsSolvable (Bar2 M ⧸ F)) (Q : Sylow 2 ↥F) :
    Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup ↥F).map F.subtype : Set (Bar2 M))) := by
  have : Group.IsSolvable (Bar2 M ⧸ F) := hsol
  set N : Subgroup (Bar2 M) :=
    Subgroup.normalizer ((Q : Subgroup ↥F).map F.subtype : Set (Bar2 M)) with hN
  have hNinf : Group.IsSolvable ↥(N ⊓ F) := by
    rw [hN]
    exact uc22r3e5_isSolvable_normalizer_inf (F := F) Q
  have hNq : Group.IsSolvable ↥((N ⊓ F).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f :=
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ F ≤ N)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ F ≤ N)).injective
  have hker : ((QuotientGroup.mk' F).comp N.subtype).ker = (N ⊓ F).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact Subgroup.mem_inf.2 ⟨n.2, (QuotientGroup.eq_one_iff (n : Bar2 M)).1 h⟩
    · intro h
      exact (QuotientGroup.eq_one_iff (n : Bar2 M)).2 (Subgroup.mem_inf.1 h).2
  exact Group.isSolvable_of_ker_le_range ((N ⊓ F).subgroupOf N).subtype
    ((QuotientGroup.mk' F).comp N.subtype) (by rw [hker, Subgroup.subtype_range])

private theorem uc22r3e5_exists_solvable_normalizer {M : Subgroup G} {T : Subgroup G}
    {F : Subgroup (Bar2 M)} [hF : F.Normal] (hsol : Group.IsSolvable (Bar2 M ⧸ F))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 (barImage M T) ⊤) :
    ∃ N : Subgroup (Bar2 M), N ⊔ F = ⊤ ∧ Group.IsSolvable ↥N ∧ barImage M T ≤ N := by
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2
      ((barImage M T : Subgroup (Bar2 M)) ⊓ F) F :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hT le_top (u4x_top_le_normalizer hF)
  obtain ⟨Q, hQ⟩ := hSyl
  refine ⟨Subgroup.normalizer ((Q : Subgroup ↥F).map F.subtype : Set (Bar2 M)), ?_, ?_, ?_⟩
  · exact Sylow.normalizer_sup_eq_top Q
  · exact uc22r3e5_isSolvable_normalizer hsol Q
  · rw [hQ, Subgroup.le_normalizer_iff]
    intro t ht s hs
    exact ⟨(barImage M T).mul_mem ((barImage M T).mul_mem ht hs.1) ((barImage M T).inv_mem ht),
      hF.conj_mem s hs.2 t⟩

private theorem uc22r3e5_card_dvd_barPreimage (M : Subgroup G) (N : Subgroup (Bar2 M)) :
    Nat.card ↥N ∣ Nat.card ↥(barPreimage M N) := by
  let ι : ↥(barPreimage M N) →* ↥M := Subgroup.inclusion (uc22p21c_barPreimage_le M N)
  let φ : ↥(barPreimage M N) →* Bar2 M := (uc22p21cPi M).comp ι
  have hφrange : φ.range = N := by
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨hM, hN'⟩ := uc22p21c_mem_barPreimage.1 y.2
      have he : ι y = ⟨(y : G), hM⟩ := Subtype.ext rfl
      show uc22p21cPi M (ι y) ∈ N
      rw [he]
      exact hN'
    · intro hq
      obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) q
      refine ⟨⟨(m : G), uc22p21c_mem_barPreimage.2 ⟨m.2, ?_⟩⟩, ?_⟩
      · rw [hm]; exact hq
      · exact hm
  rw [show Nat.card ↥N = Nat.card ↥φ.range from by rw [hφrange],
    ← Subgroup.index_ker (f := φ)]
  exact Subgroup.index_dvd_card _

private theorem uc22r3e5_mem_of_sup_eq_top {M : Subgroup G} {F N : Subgroup (Bar2 M)}
    [hF : F.Normal] (hsup : N ⊔ F = ⊤) {p : ℕ} (hpp : p.Prime) {x : Bar2 M}
    (hxp : x ^ p = 1) (hpN : ¬ p ∣ Nat.card ↥N) : x ∈ F := by
  have hNF : N ≤ Subgroup.normalizer (F : Set (Bar2 M)) :=
    le_trans le_top (u4x_top_le_normalizer hF)
  have htop : x ∈ (N : Set (Bar2 M)) * (F : Set (Bar2 M)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right N F hNF, hsup]
    exact Subgroup.mem_top x
  obtain ⟨nn, hnn, fn, hfn, hxn⟩ := Set.mem_mul.1 htop
  let q : Bar2 M ⧸ F := QuotientGroup.mk' F x
  have hq1 : q = QuotientGroup.mk' F nn := by
    show QuotientGroup.mk' F x = QuotientGroup.mk' F nn
    rw [← hxn, map_mul,
      show QuotientGroup.mk' F fn = 1 from (QuotientGroup.eq_one_iff fn).2 hfn, mul_one]
  have hqpow : q ^ p = 1 := by
    rw [show q = QuotientGroup.mk' F x from rfl, ← map_pow, hxp, map_one]
  have hqord : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hqpow
  have hqordN : orderOf q ∣ Nat.card ↥N := by
    rw [hq1]
    exact (orderOf_map_dvd (QuotientGroup.mk' F) nn).trans (Subgroup.orderOf_dvd_natCard N hnn)
  have hq1' : orderOf q = 1 := by
    rcases (Nat.dvd_prime hpp).1 hqord with h | h
    · exact h
    · exact absurd (h ▸ hqordN) hpN
  have hq1'' : (x : Bar2 M ⧸ F) = 1 := orderOf_eq_one_iff.1 hq1'
  exact (QuotientGroup.eq_one_iff x).1 hq1''

theorem uc22r3e5_inner_of_sig {D : Data G} {Ch : Choice2011 G}
    (st : Standing22 D) (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {p : ℕ} (hp : p ∈ D.sig) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {x : G} (hxM : x ∈ D.M) (hxp : x ^ p = 1) {Y : Subgroup G} (hY : Y = L ∨ Y = K) :
    ∀ (hN : uc22p21cPi D.M ⟨x, hxM⟩ ∈ normalizer (barImage D.M Y : Set (Bar2 D.M))),
      (barImage D.M Y).normalizerMonoidHom ⟨uc22p21cPi D.M ⟨x, hxM⟩, hN⟩ ∈
        (MulAut.conj : ↥(barImage D.M Y) →* MulAut ↥(barImage D.M Y)).range := by
  classical
  have hpp : p.Prime := (D.sig_prime p hp).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Fbar : Subgroup (Bar2 D.M) :=
    uc22r3e5_innerOn (barImage D.M L) ⊓ uc22r3e5_innerOn (barImage D.M K)
  have hFnorm : Fbar.Normal := uc22r3e5_pairKernel_normal hset
  have hQsol : Group.IsSolvable (Bar2 D.M ⧸ Fbar) :=
    uc22r3e5_isSolvable_quotient hL hK hset hS
  obtain ⟨N, hfrattini, hNsol, hTN⟩ :=
    uc22r3e5_exists_solvable_normalizer hQsol (u4x_isSylowOf_barImage D.sylowM)
  set YP : Subgroup G := barPreimage D.M N with hYPdef
  have hYM : YP ≤ D.M := uc22p21c_barPreimage_le D.M N
  have hTY : D.T ≤ YP := by
    rw [hYPdef]
    exact fun t ht => uc22p21c_mem_barPreimage.2 ⟨D.sylowM.le ht,
      hTN (uc22p21c_mem_barImage.2 ⟨⟨t, D.sylowM.le ht⟩, ht, rfl⟩)⟩
  have hYsol : Group.IsSolvable ↥YP := by
    rw [hYPdef]
    exact uc22s21ru3c_isSolvable_barPreimage hNsol
  have hpY : ¬ p ∣ Nat.card ↥YP :=
    uc22s21ru3b_not_dvd_card D Ch st h211 h1930 c hH₁ hH₂ hfX hp hsp hTY hYM hYsol
  have hdvdNY : Nat.card ↥N ∣ Nat.card ↥YP := by
    rw [hYPdef]
    exact uc22r3e5_card_dvd_barPreimage D.M N
  have hpN : ¬ p ∣ Nat.card ↥N := fun h => hpY (h.trans hdvdNY)
  intro hN
  have hxbar_mem : uc22p21cPi D.M ⟨x, hxM⟩ ∈ Fbar :=
    uc22r3e5_mem_of_sup_eq_top hfrattini hpp (by
      rw [← map_pow, show (⟨x, hxM⟩ : ↥D.M) ^ p = 1 from Subtype.ext (by simpa using hxp),
        map_one]) hpN
  have hxOn : uc22p21cPi D.M ⟨x, hxM⟩ ∈ uc22r3e5_innerOn (barImage D.M Y) := by
    rcases hY with rfl | rfl
    · exact (Subgroup.mem_inf.1 hxbar_mem).1
    · exact (Subgroup.mem_inf.1 hxbar_mem).2
  exact uc22r3e5_normalizerMonoidHom_mem_range_of_mem_innerOn hxOn hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
