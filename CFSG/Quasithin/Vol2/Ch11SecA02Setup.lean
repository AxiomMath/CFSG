module

public import CFSG.Quasithin.Vol2.Ch11SecA02Ctx
public import CFSG.Quasithin.Vol2.Ch11SecA02Quot

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem mem_conjugate' {H : Subgroup G} {t x : G} :
    x ∈ CFSG.conjugate H t ↔ t * x * t⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp

theorem inv_mul_mul_mem {L : Subgroup G} {t l : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (hl : l ∈ L) : t⁻¹ * l * t ∈ L := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) l).mp hl
  simpa using this

theorem mul_mul_inv_mem {L : Subgroup G} {t l : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (hl : l ∈ L) : t * l * t⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp ht l).mp hl

theorem le_normalizer_conjugate {L A : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (hLA : L ≤ Subgroup.normalizer (A : Set G)) :
    L ≤ Subgroup.normalizer (CFSG.conjugate A t : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjugate', mem_conjugate']
  have h := Subgroup.mem_normalizer_iff.mp (hLA (mul_mul_inv_mem ht hl)) (t * x * t⁻¹)
  rw [h]
  constructor <;> intro hx <;> convert hx using 1 <;> group

theorem not_le_centralizer_conjugate {L A : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (hA : ¬ A ≤ Subgroup.centralizer (L : Set G)) :
    ¬ CFSG.conjugate A t ≤ Subgroup.centralizer (L : Set G) := by
  intro hAt
  apply hA
  intro a ha
  have ha' : t⁻¹ * a * t ∈ CFSG.conjugate A t := by
    rw [mem_conjugate']
    simpa [mul_assoc] using ha
  have hc := Subgroup.mem_centralizer_iff.mp (hAt ha')
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := hc _ (inv_mul_mul_mem ht hl)
  have h2 : t * (t⁻¹ * l * t * (t⁻¹ * a * t)) * t⁻¹ = t * (t⁻¹ * a * t * (t⁻¹ * l * t)) * t⁻¹ := by
    rw [h1]
  simpa [mul_assoc] using h2

theorem irr_conjugate {L A : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ A → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = A) :
    ∀ J : Subgroup G, J ≤ CFSG.conjugate A t → L ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = CFSG.conjugate A t := by
  intro J hJ hLJ
  have htJ : J = CFSG.conjugate (CFSG.conjugate J t⁻¹) t := by
    ext x
    rw [mem_conjugate', mem_conjugate']
    simp [mul_assoc]
  have hle : CFSG.conjugate J t⁻¹ ≤ A := by
    intro x hx
    rw [mem_conjugate'] at hx
    have := hJ hx
    rw [mem_conjugate'] at this
    simpa [mul_assoc] using this
  have hinv : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ ht
  rcases hirr _ hle (le_normalizer_conjugate hinv hLJ) with h | h
  · left
    rw [htJ, h]
    ext x
    rw [mem_conjugate', Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro hx
      have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [this, hx]
      group
    · rintro rfl
      group
  · right
    rw [htJ, h]

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem exists_recogCtx (hG2 : FactG2AdjointOrder) (h8 : Ch10.TmpL6_3_2_2_eight)
    (h : Hyp11 G T L I n) :
    ∃ f : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autOn L (fsuV T I)), RecogCtx _ _ n f := by
  obtain ⟨f, hf, hZ, hodd⟩ := exists_quot_hom h8 h
  have hn : 2 ≤ n := h.one_lt
  exact ⟨f, ⟨shapeData_of_shape11 hG2 hn h.shape, hn, hf, hZ, hodd⟩⟩

omit [Finite G] in
theorem autOn_ne_bot {X : Type} [Group X] {f : X →* ↥(autOn L (fsuV T I))}
    (hc : RecogCtx X _ n f) : autOn L (fsuV T I) ≠ ⊥ := by
  intro hb
  obtain ⟨y, hy⟩ := hc.exists_ne_one
  apply hy
  have : (y : MulAut ↥(fsuV T I)) ∈ (⊥ : Subgroup (MulAut ↥(fsuV T I))) := hb ▸ y.2
  exact Subtype.ext (Subgroup.mem_bot.mp this)

omit [Finite G] in
theorem autOn_eq_of_isSimpleGroup {X : Type} [Group X] {f : X →* ↥(autOn L (fsuV T I))}
    (hc : RecogCtx X _ n f) {B : Subgroup G} (hLB : L ≤ B)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hB : IsSimpleGroup ↥(autOn B (fsuV T I))) :
    autOn L (fsuV T I) = autOn B (fsuV T I) := by
  have := autOn_normal_subgroupOf (V := fsuV T I) hBL
  exact eq_of_normal_of_isSimpleGroup (Subgroup.map_mono fun _ hx => hLB hx) hB (autOn_ne_bot hc)

theorem sqtkGroup_L (h : Hyp11 G T L I n) : SQTKGroup ↥L := by
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  have hP : pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) ≠ ⊥ := by
    have hle : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (isPGroup_fsuV h)
    intro hb
    rw [hb] at hle
    exact fsuV_ne_bot h (le_bot_iff.mp hle)
  exact InternalSec.sqtkGroup_mono (InternalSec.sqtkGroup_of_localSQTK hloc hP)
    (L_le_normalizer_fsuV h)

end CFSG.Quasithin.Vol2.Ch11.SecA
