module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6Proj
public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6CycX
public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6Inn

public section

namespace CFSG.StandardType

open CFSG.Open

variable {G : Type*} [Group G]

theorem exists_ne_bot_isPGroup_two_normalized [Finite G] {p : ℕ} (hp : p.Prime)
    {B L T : Subgroup G} {x : G} (hB : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hZL : Subgroup.center ↥L = ⊥)
    (hAut : ∀ φ : MulAut ↥L, ∃ l : ↥L, φ = MulAut.conj l)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hT : T ≤ Subgroup.centralizer ({x} : Set G)) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) ∧ U ≠ ⊥ := by
  let C : Subgroup G :=
    Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({x} : Set G)
  have hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l := by
    intro l hl c hc
    exact Subgroup.mem_centralizer_iff.mp hc.1 l hl
  have htriv : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z = 1 := by
    intro z hz hcomm
    have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hcomm (g : G) g.2).symm
    rw [hZL] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hdec : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ l ∈ L, ∃ c ∈ C, g = l * c := by
    intro g hg
    obtain ⟨l, hlL, hl⟩ := exists_inner_of_mem_normalizer (L := L) hAut (hN hg)
    refine ⟨l, hlL, l⁻¹ * g, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change l⁻¹ * g ∈ Subgroup.centralizer (L : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h' : l⁻¹ * g * y = y * (l⁻¹ * g) := by
          calc l⁻¹ * g * y = l⁻¹ * (g * y * g⁻¹) * g := by group
            _ = l⁻¹ * (l * y * l⁻¹) * g := by rw [hl y hy]
            _ = y * (l⁻¹ * g) := by group
        exact h'.symm
      · change l⁻¹ * g ∈ Subgroup.centralizer ({x} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hlx : Commute l x := Subgroup.mem_centralizer_singleton_iff.mp (hLx hlL)
        have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg
        exact ((hlx.inv_left.symm).mul_right hgx.symm).symm
    · group
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨x, hxB⟩)
  have hxC : x ∈ C := by
    refine ⟨?_, ?_⟩
    · change x ∈ Subgroup.centralizer (L : Set G)
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hLx hy)
    · change x ∈ Subgroup.centralizer ({x} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let U : Subgroup G := ggProjLeft L C T hLC
  have hUL : U ≤ L := ggProjLeft_le_left (L := L) (C := C) (T := T) (hLC := hLC)
  have hU2 : IsPGroup 2 U :=
    isPGroup_ggProjLeft (L := L) (C := C) (T := T) (hLC := hLC) htriv hT2
  have hconjC : ∀ b ∈ B, ∀ c ∈ C, b * c * b⁻¹ ∈ C := by
    intro b hb c hc
    refine ⟨?_, ?_⟩
    · change b * c * b⁻¹ ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : b⁻¹ * y * b ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hBL (B.inv_mem hb)) y).mp hy
        simpa using this
      have hcu : (b⁻¹ * y * b) * c = c * (b⁻¹ * y * b) :=
        Subgroup.mem_centralizer_iff.mp hc.1 (b⁻¹ * y * b) hy'
      calc y * (b * c * b⁻¹) = (b * (b⁻¹ * y * b)) * c * b⁻¹ := by group
        _ = b * ((b⁻¹ * y * b) * c) * b⁻¹ := by group
        _ = b * (c * (b⁻¹ * y * b)) * b⁻¹ := by rw [hcu]
        _ = (b * c * b⁻¹) * y := by group
    · change b * c * b⁻¹ ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hbx : Commute b x := Subgroup.mem_centralizer_singleton_iff.mp (hBx hb)
      have hcx : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      exact (hbx.mul_left hcx).mul_left hbx.inv_left
  have hconjU : ∀ b ∈ B, ∀ h ∈ U, b * h * b⁻¹ ∈ U := by
    intro b hb h hh
    refine conj_mem_ggProjLeft (L := L) (C := C) (T := T) (hLC := hLC) (b := b)
      (fun l hl => (Subgroup.mem_normalizer_iff.mp (hBL hb) l).mp hl)
      (hconjC b hb)
      (fun t ht => (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht) hh
  have hBU : B ≤ Subgroup.normalizer (U : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconjU b hb h
    · intro hh
      have h' := hconjU b⁻¹ (B.inv_mem hb) (b * h * b⁻¹) hh
      have heq : b⁻¹ * (b * h * b⁻¹) * (b⁻¹)⁻¹ = h := by group
      rwa [heq] at h'
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hdecT : ∀ g ∈ T, ∃ l ∈ L, ∃ c ∈ C, g = l * c := fun g hg => hdec g (hT hg)
    have hTC : T ≤ C := le_right_of_ggProjLeft_eq_bot hdecT hbot
    let Cb : Subgroup G := ggProjRight L C B hLC
    have hCbp : ∀ c ∈ Cb, c ^ p = 1 :=
      pow_eq_one_of_mem_ggProjRight (L := L) (C := C) (T := B) (hLC := hLC) htriv hB.2
    have hCbP : IsPGroup p Cb := by
      intro c
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa using hCbp (c : G) c.2
    have hCbL : Cb ≤ Subgroup.centralizer (L : Set G) :=
      fun c hc => ((mem_ggProjRight (L := L) (C := C) (T := B) (hLC := hLC)).mp hc).1.1
    have hCbCyc : IsCyclic Cb := hcyc Cb hCbL hCbP
    have hxCb : x ∈ Cb :=
      (mem_ggProjRight (L := L) (C := C) (T := B) (hLC := hLC)).mpr
        ⟨hxC, 1, L.one_mem, by simpa using hxB⟩
    have hCbZ : Cb ≤ Subgroup.zpowers x :=
      le_zpowers_of_isCyclic_of_pow_eq_one hp hCbCyc hCbp hxCb hx1
    have hTcentB : T ≤ Subgroup.centralizer (B : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨l, hlL, c, hcC, hbc⟩ := hdec b (hBx hb)
      have hcCb : c ∈ Cb :=
        (mem_ggProjRight (L := L) (C := C) (T := B) (hLC := hLC)).mpr
          ⟨hcC, l, hlL, by rw [← hbc]; exact hb⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hCbZ hcCb)
      have htx : Commute t x := Subgroup.mem_centralizer_singleton_iff.mp (hT ht)
      have hct : Commute c t := by
        rw [← hk]
        exact (htx.symm).zpow_left k
      have hlt : l * t = t * l := hLC l hlL t (hTC ht)
      calc b * t = (l * c) * t := by rw [hbc]
        _ = l * (c * t) := by group
        _ = l * (t * c) := by rw [hct]
        _ = (l * t) * c := by group
        _ = (t * l) * c := by rw [hlt]
        _ = t * (l * c) := by group
        _ = t * b := by rw [hbc]
    exact hTB (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hTcentB)
  exact ⟨U, hUL, hU2, hBU, hUne⟩

end CFSG.StandardType
