module

public import CFSG.RankThree.PartTwo.Sec17.Item174KFactStar
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2Strong
import CFSG.Dihedral.Glauberman.DicksonMaxB
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.GL2NonsplitTransport
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Small
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG

@[expose] def StarCore (H : Type) [Group H] [Finite H] : Prop :=
  IsSimpleGroup H → ∀ t : H, orderOf t = 3 →
    ∀ I : Subgroup H, Subgroup.normalizer (Subgroup.zpowers t : Set H) ≤ I →
    ∀ D : Subgroup H, D ≤ I → IsPGroup 2 D → I ≤ Subgroup.normalizer (D : Set H) →
      ⁅D, Subgroup.zpowers t⁆ ≠ ⊥ →
        ∃ n : ℕ, Odd n ∧ Nonempty (H ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 n))

theorem starFor_of_starCore {H : Type} [Group H] [Finite H] (h : StarCore H) : StarFor H := by
  intro hs t ht I hI hO2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h hs t ht I hI _ (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
    hO2

theorem starCore_of_mulEquiv {H K : Type} [Group H] [Finite H] [Group K] [Finite K]
    (e : H ≃* K) (h : StarCore K) : StarCore H := by
  intro hs t ht I hI D hDI hD hID hc
  haveI := hs
  have hsK : IsSimpleGroup K := e.symm.isSimpleGroup
  have hN : Subgroup.normalizer (Subgroup.zpowers (e t) : Set K) ≤ I.map e.toMonoidHom := by
    intro y hy
    refine ⟨e.symm y, hI (mem_normalizer_zpowers_of ?_ ?_), by simp⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        ((Subgroup.mem_normalizer_iff.mp hy (e t)).mp (Subgroup.mem_zpowers _))
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective (by simpa using hk)⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        ((Subgroup.mem_normalizer_iff.mp (inv_mem hy) (e t)).mp (Subgroup.mem_zpowers _))
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective (by simpa using hk)⟩
  have hID' : I.map e.toMonoidHom ≤
      Subgroup.normalizer ((D.map e.toMonoidHom : Subgroup K) : Set K) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hID
  have hc' : ⁅D.map e.toMonoidHom, Subgroup.zpowers (e t)⁆ ≠ ⊥ := by
    intro hb
    apply hc
    have hz : Subgroup.zpowers (e t) = (Subgroup.zpowers t).map e.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hz, ← Subgroup.map_commutator] at hb
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb
  obtain ⟨n, hn, ⟨f⟩⟩ := h hsK (e t) (by rw [MulEquiv.orderOf_eq]; exact ht) _ hN _
    (Subgroup.map_mono hDI) (hD.map _) hID' hc'
  exact ⟨n, hn, ⟨e.trans f⟩⟩

section Generic

variable {G : Type} [Group G]

theorem commutator_zpowers_eq_bot {D : Subgroup G} {t : G} (h : ∀ d ∈ D, d * t = t * d) :
    ⁅D, Subgroup.zpowers t⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((show Commute t d from (h d hd).symm).zpow_left k).eq

theorem not_mem_of_orderOf_three {D : Subgroup G} (hD : IsPGroup 2 D) {s : G} (hs : orderOf s = 3)
    (hsD : s ∈ D) : False := by
  obtain ⟨k, hk⟩ := hD ⟨s, hsD⟩
  have h1 : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := hs ▸ orderOf_dvd_of_pow_eq_one h1
  have := (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem not_inv_of_mem {D : Subgroup G} (hD : IsPGroup 2 D) {t : G} (ht : orderOf t = 3)
    (htD : t ∈ Subgroup.normalizer (D : Set G)) {d : G} (hd : d ∈ D) (hinv : d * t * d⁻¹ = t⁻¹) :
    False := by
  have h1 : t * d⁻¹ * t⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp htD _).mp (inv_mem hd)
  have h2 : d * (t * d⁻¹ * t⁻¹) ∈ D := mul_mem hd h1
  have h3 : d * (t * d⁻¹ * t⁻¹) = t⁻¹ ^ 2 := by
    rw [pow_two, ← hinv]
    group
  rw [h3] at h2
  refine not_mem_of_orderOf_three hD ?_ h2
  rw [orderOf_pow' _ (by norm_num), orderOf_inv, ht]
  norm_num

theorem commutator_eq_bot_of_commute_or_inv {I D : Subgroup G} (hDI : D ≤ I) (hD : IsPGroup 2 D)
    {t : G} (ht : orderOf t = 3) (htD : t ∈ Subgroup.normalizer (D : Set G))
    (h : ∀ y ∈ I, y * t = t * y ∨ y * t * y⁻¹ = t⁻¹) : ⁅D, Subgroup.zpowers t⁆ = ⊥ := by
  refine commutator_zpowers_eq_bot fun d hd => ?_
  rcases h d (hDI hd) with h1 | h1
  · exact h1
  · exact (not_inv_of_mem hD ht htD hd h1).elim

theorem dihedral_commute_or_inv {z : ℕ} (x y : DihedralGroup z) (hx : orderOf x = 3) :
    y * x = x * y ∨ y * x * y⁻¹ = x⁻¹ := by
  rcases x with i | i
  · rcases y with j | j
    · left
      simp [DihedralGroup.r_mul_r, add_comm]
    · right
      simp [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
  · rw [DihedralGroup.orderOf_sr] at hx
    omega

theorem commutator_eq_bot_of_card_le_two [Finite G] {D : Subgroup G} (hD : Nat.card D ≤ 2) {t : G}
    (htD : t ∈ Subgroup.normalizer (D : Set G)) : ⁅D, Subgroup.zpowers t⁆ = ⊥ := by
  classical
  refine commutator_zpowers_eq_bot fun d hd => ?_
  have hd' : t * d * t⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp htD _).mp hd
  by_contra hne
  have hne' : t * d * t⁻¹ ≠ d := fun h => hne (by
    calc d * t = t * d * t⁻¹ * t := by rw [h]
      _ = t * d := by group)
  have hd1 : d ≠ 1 := by
    rintro rfl
    simp at hne'
  have hd'1 : t * d * t⁻¹ ≠ 1 := by
    intro h
    apply hd1
    have := congrArg (fun x => t⁻¹ * x * t) h
    simpa [mul_assoc] using this
  letI : Fintype D := Fintype.ofFinite D
  have hcard : ({1, ⟨d, hd⟩, ⟨t * d * t⁻¹, hd'⟩} : Finset D).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hne' (congrArg Subtype.val h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hd1 (congrArg Subtype.val h).symm,
        fun h => hd'1 (congrArg Subtype.val h).symm⟩
  have := Finset.card_le_univ ({1, ⟨d, hd⟩, ⟨t * d * t⁻¹, hd'⟩} : Finset D)
  rw [hcard, ← Nat.card_eq_fintype_card] at this
  omega

theorem eq_bot_of_isSimpleGroup {I D : Subgroup G} (hs : IsSimpleGroup I) (hDI : D ≤ I)
    (hD : IsPGroup 2 D) (hID : I ≤ Subgroup.normalizer (D : Set G)) {t : G} (ht : orderOf t = 3)
    (htI : t ∈ I) : D = ⊥ := by
  have hN : (D.subgroupOf I).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDI]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hID hk) h).mp hh
  haveI := hs
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.subgroupOf I) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact le_bot_iff.mp fun d hd => (Subgroup.disjoint_def.mp h) hd (hDI hd)
  · exfalso
    have : (⟨t, htI⟩ : I) ∈ D.subgroupOf I := h ▸ Subgroup.mem_top _
    exact not_mem_of_orderOf_three hD ht (Subgroup.mem_subgroupOf.mp this)

theorem sq_mem_of_inv_of_sup {X : Type} [Group X] {E C : Subgroup X} [E.Normal] (hC : IsCyclic C)
    (hsup : E ⊔ C = ⊤) {t w : X} (hw : w * t * w⁻¹ = t⁻¹) : t ^ 2 ∈ E := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' E).comp C.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Subgroup.map_sup E C (QuotientGroup.mk' E)
    have hEb : E.map (QuotientGroup.mk' E) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hsup, hEb, bot_sup_eq, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective E)]
      at h1
    exact h1.symm
  have hcomm : ∀ a b : X ⧸ E, a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_mul]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hC.commGroup.mul_comm a' b']
  have h1 : (t : X ⧸ E) * (w : X ⧸ E) * (t : X ⧸ E)⁻¹ * (w : X ⧸ E)⁻¹ = 1 := by
    rw [hcomm (t : X ⧸ E) (w : X ⧸ E)]
    group
  have h2 : t * w * t⁻¹ * w⁻¹ = t ^ 2 := by
    have h3 : w * t⁻¹ * w⁻¹ = t := by
      have := congrArg (·⁻¹) hw
      simpa [mul_assoc] using this
    calc t * w * t⁻¹ * w⁻¹ = t * (w * t⁻¹ * w⁻¹) := by group
      _ = t * t := by rw [h3]
      _ = t ^ 2 := (pow_two t).symm
  rw [← h2, ← QuotientGroup.eq_one_iff]
  simpa using h1

end Generic

section PSL2

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.BenderSuzuki.MatrixGroups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem three_ne_zero_of_card (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3) : (3 : F) ≠ 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  intro h
  have hc : ringChar F ∣ 3 := by
    have : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
    exact (CharP.cast_eq_zero_iff F (ringChar F) 3).mp this
  obtain ⟨n, hpr, hcard⟩ := FiniteField.card F (ringChar F)
  have h3 : ringChar F = 3 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp hc
  have h3F : 3 ∣ p ^ f := by
    rw [← hF, Nat.card_eq_fintype_card, hcard, h3]
    exact dvd_pow_self 3 n.ne_zero
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
    (Nat.prime_three.dvd_of_dvd_pow h3F)).symm

theorem exists_inv_psl2 (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3)
    {t : PSL2MatrixGroup F} (ht : orderOf t = 3) : ∃ w, w * t * w⁻¹ = t⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hsdet, hs⟩ := exists_inverting_det_one (three_ne_zero_of_card hF hp3)
  set s' : Matrix.SpecialLinearGroup (Fin 2) F := ⟨s, hsdet⟩ with hs'def
  have hss : Matrix.SpecialLinearGroup.toGL s' = s := Units.ext rfl
  have hs' : s' * cSL * s'⁻¹ = cSL⁻¹ := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv, map_inv, toGL_cSL, hss, hs]
  set a0 := projPSL F (cSL (F := F)) with ha0
  set w0 := projPSL F s' with hw0def
  have hw0 : w0 * a0 * w0⁻¹ = a0⁻¹ := by
    rw [ha0, hw0def, ← map_inv, ← map_mul, ← map_mul, hs', map_inv]
  have hA : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, ht]
  have hB : Nat.card (Subgroup.zpowers a0) = 3 := by rw [Nat.card_zpowers, orderOf_projPSL_cSL]
  obtain ⟨g, hg⟩ := OvergroupConj.exists_conj_eq_of_card_three
    (OvergroupPSL2.isCyclic_of_isPGroup_three hF hp3) hA hB
  have htm : t ∈ (Subgroup.zpowers a0).map (MulAut.conj g).toMonoidHom :=
    hg ▸ Subgroup.mem_zpowers t
  obtain ⟨y, hy, hyt⟩ := htm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyt' : g * a0 ^ k * g⁻¹ = t := by simpa [MulAut.conj_apply] using hyt
  have hk : w0 * a0 ^ k * w0⁻¹ = a0⁻¹ ^ k := by rw [← conj_zpow, hw0]
  refine ⟨g * w0 * g⁻¹, ?_⟩
  rw [← hyt']
  calc g * w0 * g⁻¹ * (g * a0 ^ k * g⁻¹) * (g * w0 * g⁻¹)⁻¹
      = g * (w0 * a0 ^ k * w0⁻¹) * g⁻¹ := by group
    _ = g * a0⁻¹ ^ k * g⁻¹ := by rw [hk]
    _ = (g * a0 ^ k * g⁻¹)⁻¹ := by group

theorem nonempty_projSL_of_card_seven (h7 : Nat.card F = 7) :
    Nonempty (PSL2MatrixGroup F ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 1)) := by
  refine CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.nonempty_projSL_three_two_of_psl_two_seven
    ⟨⟨Nat.prime_seven, le_rfl, by decide⟩, F, inferInstance, inferInstance, by rw [h7]; norm_num,
      ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩

theorem alternating_four_no_inv :
    ∀ a b : alternatingGroup (Fin 4), a ^ 3 = 1 → a ≠ 1 → b * a * b⁻¹ ≠ a⁻¹ := by
  decide

theorem perm_four_pow : ∀ g : Equiv.Perm (Fin 4), g ^ 3 = 1 ∨ g ^ 4 = 1 := by
  decide

theorem card_le_two_of_dvd_six {G : Type} [Group G] [Finite G] {D I : Subgroup G} (hDI : D ≤ I)
    (hD : IsPGroup 2 D) (hI : Nat.card I ∣ 6) : Nat.card D ≤ 2 := by
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  have h6 : 2 ^ n ∣ 6 := hn ▸ (Subgroup.card_dvd_of_le hDI).trans hI
  rcases n with _ | _ | n
  · omega
  · omega
  · exfalso
    have : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans h6
    omega

theorem starCore_psl2 (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3) :
    StarCore (PSL2MatrixGroup F) := by
  intro hs t ht I hI D hDI hD hID hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc := OvergroupPSL2.isCyclic_of_isPGroup_three hF hp3
  have htI : t ∈ I := hI (Subgroup.le_normalizer (Subgroup.mem_zpowers t))
  have htD : t ∈ Subgroup.normalizer (D : Set (PSL2MatrixGroup F)) := hID htI
  obtain ⟨w, hw⟩ := exists_inv_psl2 hF hp3 ht
  have hwI : w ∈ I := by
    refine hI (mem_normalizer_zpowers_of ?_ ?_)
    · rw [hw]
      exact inv_mem (Subgroup.mem_zpowers t)
    · have : w⁻¹ * t * w = t⁻¹ := by
        have := congrArg (fun x => w⁻¹ * x⁻¹ * w) hw
        simpa [mul_assoc] using this.symm
      rw [this]
      exact inv_mem (Subgroup.mem_zpowers t)
  obtain ⟨z, g, t0, hz3, hg0, hg2, hzg, ht0⟩ := OvergroupPSL2.exists_torus_element hF hp3
  have hA : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, ht]
  obtain ⟨x, hxo, hxc⟩ := OvergroupConj.exists_conj_mem_centralizer hcyc hA (t := t0) (ht0 ▸ hz3)
  have hxI : x ∈ I := hI (Subgroup.centralizer_le_normalizer _ hxc)
  have hxo' : orderOf (⟨x, hxI⟩ : I) = z := by rw [Subgroup.orderOf_mk, hxo, ht0]
  have hf0 : f ≠ 0 := CFSG.BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hq1 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hzq : Nat.card F ≤ 2 * z + 1 := by
    have : z * g ≤ z * 2 := Nat.mul_le_mul_left z hg2
    omega
  have hto : orderOf (⟨t, htI⟩ : I) = 3 := by rw [Subgroup.orderOf_mk, ht]
  have key : ⁅D, Subgroup.zpowers t⁆ = ⊥ ∨ Nat.card F = 7 := by
    rcases Glauberman.Dickson.dickson_psl2_subgroup_list hF I with
      ⟨-, -, -, hE⟩ | ⟨-, -, -, hC⟩ | ⟨z', -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨hS4, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t', -, -, -, -, E, C, hEn, hEel, -, hCc, -, -, hsup, -⟩ | ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
    ·
      left
      refine commutator_eq_bot_of_commute_or_inv hDI hD ht htD fun y hy => Or.inl ?_
      exact congrArg Subtype.val (hE.is_comm.comm (⟨y, hy⟩ : I) ⟨t, htI⟩)
    ·
      left
      refine commutator_eq_bot_of_commute_or_inv hDI hD ht htD fun y hy => Or.inl ?_
      exact congrArg Subtype.val (hC.commGroup.mul_comm (⟨y, hy⟩ : I) ⟨t, htI⟩)
    ·
      left
      refine commutator_eq_bot_of_commute_or_inv hDI hD ht htD fun y hy => ?_
      rcases dihedral_commute_or_inv (e ⟨t, htI⟩) (e ⟨y, hy⟩)
          (by rw [MulEquiv.orderOf_eq, hto]) with h | h
      · left
        rw [← map_mul, ← map_mul] at h
        exact congrArg Subtype.val (e.injective h)
      · right
        rw [← map_inv, ← map_mul, ← map_mul, ← map_inv] at h
        exact congrArg Subtype.val (e.injective h)
    ·
      exfalso
      refine alternating_four_no_inv (e ⟨t, htI⟩) (e ⟨w, hwI⟩) ?_ ?_ ?_
      · rw [← map_pow, ← hto, pow_orderOf_eq_one, map_one]
      · intro h
        have := e.injective (h.trans (map_one e).symm)
        rw [this, orderOf_one] at hto
        omega
      · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
        exact congrArg e (Subtype.ext hw)
    ·
      right
      have hz : z = 3 := by
        rcases perm_four_pow (e ⟨x, hxI⟩) with h | h
        · have h1 := orderOf_dvd_of_pow_eq_one h
          rw [MulEquiv.orderOf_eq, hxo'] at h1
          exact Nat.dvd_antisymm h1 hz3
        · have h1 := orderOf_dvd_of_pow_eq_one h
          rw [MulEquiv.orderOf_eq, hxo'] at h1
          have := hz3.trans h1
          omega
      subst hz
      have hq7 : Nat.card F ≤ 7 := by omega
      have h16 : Nat.card F ^ 2 % 16 = 1 := by rw [hF]; exact hS4
      clear hzq hzg
      interval_cases hq : Nat.card F <;> first | rfl | norm_num at h16
    ·
      left
      have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
      rw [eq_bot_of_isSimpleGroup e.isSimpleGroup hDI hD hID ht htI]
      exact Subgroup.commutator_bot_left _
    ·
      exfalso
      haveI := hEn
      have hw' : (⟨w, hwI⟩ : I) * ⟨t, htI⟩ * (⟨w, hwI⟩ : I)⁻¹ = (⟨t, htI⟩ : I)⁻¹ := Subtype.ext hw
      have h2 := sq_mem_of_inv_of_sup hCc hsup hw'
      have htE : (⟨t, htI⟩ : I) ∈ E := by
        have h4 : ((⟨t, htI⟩ : I) ^ 2) ^ 2 = ⟨t, htI⟩ := by
          rw [← pow_mul]
          have : (⟨t, htI⟩ : I) ^ 3 = 1 := by rw [← hto]; exact pow_orderOf_eq_one _
          calc (⟨t, htI⟩ : I) ^ (2 * 2) = (⟨t, htI⟩ : I) ^ 3 * ⟨t, htI⟩ := by
                rw [← pow_succ]
            _ = ⟨t, htI⟩ := by rw [this, one_mul]
        rw [← h4]
        exact pow_mem h2 2
      haveI := hEel
      obtain ⟨k, hk⟩ := CFSG.IsElementaryAbelian.isPGroup p E ⟨_, htE⟩
      have hk' : (⟨t, htI⟩ : I) ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have h3 : 3 ∣ p ^ k := hto ▸ orderOf_dvd_of_pow_eq_one hk'
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    ·
      have hm0 : m ≠ 0 := by rintro rfl; exact hf0 (Nat.eq_zero_of_zero_dvd hmf)
      have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
      by_cases h2 : p ^ m = 2
      · left
        refine commutator_eq_bot_of_card_le_two (card_le_two_of_dvd_six hDI hD ?_) htD
        rw [Nat.card_congr e.toEquiv]
        have := OvergroupPSL2.card_psl2_dvd (GaloisField p m)
        rw [hGF, h2] at this
        simpa using this
      have ha := OvergroupPSL2.four_le_pow hp3 hm0 h2
      by_cases hmeq : m = f
      · left
        obtain ⟨φ⟩ := Glauberman.Dickson.nonempty_galoisField_ringHom hF hmf
        have hcardle : Nat.card F ≤ Nat.card (GaloisField p m) := by rw [hF, hGF, hmeq]
        have hbij := φ.injective.bijective_of_nat_card_le hcardle
        let ψ : F ≃+* GaloisField p m := (RingEquiv.ofBijective φ hbij).symm
        have hle : Nat.card (PSL2MatrixGroup F) ≤ Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
          Nat.card_le_card_of_injective _ (Glauberman.Dickson.psl2Map_injective ψ.toRingHom)
        have hItop : I = ⊤ := by
          refine Subgroup.eq_top_of_card_eq I ?_
          refine le_antisymm (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card I)) ?_
          rw [Nat.card_congr e.toEquiv]
          exact hle
        haveI := hs
        have hsI : IsSimpleGroup I :=
          ((MulEquiv.subgroupCongr hItop).trans Subgroup.topEquiv).isSimpleGroup
        rw [eq_bot_of_isSimpleGroup hsI hDI hD hID ht htI]
        exact Subgroup.commutator_bot_left _
      · exfalso
        obtain ⟨k, hk⟩ := hmf
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h | h
          · interval_cases k <;> simp_all
          · exact h
        have hf2 : 2 * m ≤ f := by nlinarith
        have hpow : (p ^ m) ^ 2 ≤ Nat.card F := by
          rw [hF, ← pow_mul, mul_comm]
          exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
        have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le
          (GaloisField p m) (e ⟨x, hxI⟩)
        rw [MulEquiv.orderOf_eq, hxo', hGF] at hord
        exact OvergroupPSL2.false_of_subfield_bound ha hord hpow hzq
    ·
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hf0 (Nat.eq_zero_of_zero_dvd (by simpa using hmf))
      have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
      have hf2 : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
      by_cases h2 : p ^ m = 2
      · left
        refine commutator_eq_bot_of_card_le_two (card_le_two_of_dvd_six hDI hD ?_) htD
        rw [Nat.card_congr e.toEquiv, Glauberman.Dickson.MaxUp.card_pgl2_galoisField hm0,
          pow_mul' p 2 m, h2]
        norm_num
      exfalso
      have ha := OvergroupPSL2.four_le_pow hp3 hm0 h2
      have hpow : (p ^ m) ^ 2 ≤ Nat.card F := by
        rw [hF, ← pow_mul, mul_comm]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
      have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le
        (GaloisField p m) (e ⟨x, hxI⟩)
      rw [MulEquiv.orderOf_eq, hxo', hGF] at hord
      exact OvergroupPSL2.false_of_subfield_bound ha hord hpow hzq
  rcases key with h | h
  · exact absurd h hc
  · exact ⟨1, odd_one, nonempty_projSL_of_card_seven h⟩

end PSL2

theorem starL2_proved : StarL2 := by
  intro H _ _ d q hq hd ⟨e2⟩
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hmodel := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.statedClassical_of_lieModel
    (by omega) (CFSG.Models.lieModel_A 1 q hv e2)
  obtain ⟨-, F, instF, instFin, hF, ⟨eF⟩⟩ := hmodel
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e3 : H ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F :=
    eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  exact starFor_of_starCore (starCore_of_mulEquiv e3 (starCore_psl2 hF hq))

theorem starA5_proved : StarA5 := by
  intro H _ _ ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  have e' : H ≃* alternatingGroup (Fin 5) := e
  exact starFor_of_starCore (starCore_of_mulEquiv (e'.trans eA.symm)
    (starCore_psl2 (GaloisField.card 2 2 (by norm_num)) (by norm_num)))

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
