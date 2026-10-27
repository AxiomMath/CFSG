module

public import CFSG.LocalAnalysis.StandardType.FF81.FrameChain
public import CFSG.LocalAnalysis.StandardType.FF81.FrameJ
public import CFSG.LocalAnalysis.StandardType.FF81.FrameTau
public import CFSG.LocalAnalysis.StandardType.FF81.FrameCore
import CFSG.Adapters.StatedSLTwoField

public section

namespace CFSG.StandardType.FF81

open CFSG.Open

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}

private lemma simple_card_map {G H : Type*} [Group G] [Group H] {A : Subgroup G}
    (hA : IsSimpleGroup ↥A) (hcard : Nat.card A = 168) {f : G →* H}
    (hf : Function.Injective f) :
    IsSimpleGroup ↥(A.map f) ∧ Nat.card (A.map f) = 168 := by
  refine ⟨(MulEquiv.isSimpleGroup_congr (Subgroup.equivMapOfInjective A f hf)).mp hA, ?_⟩
  rw [Subgroup.card_map_of_injective hf, hcard]

private lemma frame_mem_L_comm_b (hA : HypA G n b L) {u : ↥L} :
    (u : G) * b = b * (u : G) := by
  exact ((Subgroup.mem_centralizer_iff.mp (hA.le u.2)) b (by simp)).symm

omit [Finite G] in
private lemma frame_u_orderOf [NeZero n] (φ : ↥L ≃* SL(n + 1, ZMod 2)) :
    orderOf (φ.symm (blockSL2 (ZMod 2) n 0 sTwo)) = 2 := by
  rw [MulEquiv.orderOf_eq, orderOf_injective (blockSL2 (ZMod 2) n 0)
    (blockSL2_injective n 0) sTwo, orderOf_sTwo]

omit [Finite G] in
private lemma frame_u_comm_J [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)} {u : ↥L}
    (hu : φ u = blockSL2 (ZMod 2) n 0 sTwo) {j : G} (hj : j ∈ frameJ φ) :
    (u : G) * j = j * (u : G) := by
  have hjL : j ∈ L := pullSL_le φ (jBlock n).range hj
  have hj' : φ ⟨j, hjL⟩ ∈ (jBlock n).range :=
    (mem_pullSL_iff φ (jBlock n).range ⟨j, hjL⟩).mp hj
  obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hj'
  have h : u * (⟨j, hjL⟩ : ↥L) = (⟨j, hjL⟩ : ↥L) * u := φ.injective (by
    rw [map_mul, map_mul, hu, ← hB]
    exact blockSL2_zero_mul_jBlock n sTwo B)
  simpa using congrArg (Subtype.val) h

omit [Finite G] in
private lemma frame_u_conj_z [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)} {u : ↥L}
    (hu : φ u = blockSL2 (ZMod 2) n 0 sTwo) {z : Fin 3 → ↥L} (hφ0 : φ (z 0) = tOne n) :
    (u : G) * (z 0 : G) * (u : G)⁻¹ = (z 0 : G)⁻¹ := by
  have h : u * (z 0) * u⁻¹ = (z 0)⁻¹ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, hu, hφ0, tOne]
    rw [← map_mul, ← map_inv, ← map_mul, sTwo_mul_rhoTwo_mul_inv]
    rw [map_inv φ (z 0), hφ0, tOne, ← map_inv]
  simpa using congrArg (Subtype.val) h

omit [Finite G] in
private lemma frame_t_orderOf {u τ : G} (hu : orderOf u = 2) :
    orderOf (τ * u * τ⁻¹) = 2 := by
  rw [show τ * u * τ⁻¹ = MulAut.conj τ u by rw [MulAut.conj_apply]]
  rw [MulEquiv.orderOf_eq, hu]

omit [Finite G] in
private lemma frame_t_inv_b {b z0 u τ t : G}
    (hτz : τ * z0 * τ⁻¹ = b) (huz : u * z0 * u⁻¹ = z0⁻¹)
    (ht : t = τ * u * τ⁻¹) : t * b * t⁻¹ = b⁻¹ := by
  have hb : τ⁻¹ * b * τ = z0 := by rw [← hτz]; group
  rw [ht]
  calc
    τ * u * τ⁻¹ * b * (τ * u * τ⁻¹)⁻¹ = τ * u * (τ⁻¹ * b * τ) * u⁻¹ * τ⁻¹ := by group
    _ = τ * u * z0 * u⁻¹ * τ⁻¹ := by rw [hb]
    _ = τ * (u * z0 * u⁻¹) * τ⁻¹ := by group
    _ = τ * z0⁻¹ * τ⁻¹ := by rw [huz]
    _ = (τ * z0 * τ⁻¹)⁻¹ := by group
    _ = b⁻¹ := by rw [hτz]

omit [Finite G] in
private lemma frame_t_comm_z {b z0 u τ t : G} (hτb : τ * b * τ⁻¹ = z0)
    (hu_comm_b : u * b = b * u) (ht : t = τ * u * τ⁻¹) : t * z0 = z0 * t := by
  have h1 : τ⁻¹ * z0 * τ = b := by rw [← hτb]; group
  have h2 : u * b * u⁻¹ = b := by rw [hu_comm_b]; group
  have h : t * z0 * t⁻¹ = z0 := by
    rw [ht]
    calc
      τ * u * τ⁻¹ * z0 * (τ * u * τ⁻¹)⁻¹ = τ * u * (τ⁻¹ * z0 * τ) * u⁻¹ * τ⁻¹ := by group
      _ = τ * u * b * u⁻¹ * τ⁻¹ := by rw [h1]
      _ = τ * (u * b * u⁻¹) * τ⁻¹ := by group
      _ = τ * b * τ⁻¹ := by rw [h2]
      _ = z0 := hτb
  calc
    t * z0 = (t * z0 * t⁻¹) * t := by group
    _ = z0 * t := by rw [h]

omit [Finite G] in
private lemma frame_t_comm_J [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)} {u : ↥L} {τ t : G}
    (ht : t = τ * (u : G) * τ⁻¹)
    (hτJ : (frameJ φ).map (MulAut.conj τ).toMonoidHom = frameJ φ)
    (hu_comm_J : ∀ j ∈ frameJ φ, (u : G) * j = j * (u : G)) {j : G}
    (hj : j ∈ frameJ φ) : t * j = j * t := by
  have hk : τ⁻¹ * j * τ ∈ frameJ φ := by
    have hj' : j ∈ (frameJ φ).map (MulAut.conj τ).toMonoidHom := by rw [hτJ]; exact hj
    obtain ⟨k, hk, hkj⟩ := Subgroup.mem_map.mp hj'
    have hkj' : τ * k * τ⁻¹ = j := by simpa [MulAut.conj_apply] using hkj
    have hkeq : k = τ⁻¹ * j * τ := by rw [← hkj']; group
    exact hkeq ▸ hk
  have h : t * j * t⁻¹ = j := by
    rw [ht]
    calc
      τ * (u : G) * τ⁻¹ * j * (τ * (u : G) * τ⁻¹)⁻¹
          = τ * ((u : G) * (τ⁻¹ * j * τ) * (u : G)⁻¹) * τ⁻¹ := by group
      _ = τ * (τ⁻¹ * j * τ) * τ⁻¹ := by
        rw [hu_comm_J (τ⁻¹ * j * τ) hk]
        group
      _ = j := by group
  calc
    t * j = (t * j * t⁻¹) * t := by group
    _ = j * t := by rw [h]

private lemma frame_t_comm_L [NeZero n] (hn4 : 4 ≤ n) (hA : HypA G n b L)
    {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z) {φ : ↥L ≃* SL(n + 1, ZMod 2)}
    (hφ0 : φ (z 0) = tOne n) {t : G} (htb : t * b * t⁻¹ = b⁻¹)
    (htorder : orderOf t = 2) (htz : t * (z 0 : G) = (z 0 : G) * t)
    (htJ : ∀ j ∈ frameJ φ, t * j = j * t) : ∀ y ∈ L, t * y = y * t := by
  have htN : t ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact HypA.map_conj_eq hA hz (by
      rw [htb]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp⟩)
  refine commute_of_commute_centralizer (n := n) hn4 φ hφ0 htN ?_ htz ?_
  · rw [htorder]; decide
  · intro B
    exact htJ _ ((mem_pullSL_iff φ (jBlock n).range (φ.symm (jBlock n B))).mpr (by simp))

omit [Finite G] in
private lemma frame_g_facts {b z0 u τ j t : G} (hτb : τ * b * τ⁻¹ = z0)
    (hτz : τ * z0 * τ⁻¹ = b) (hjb : j * b = b * j) (hjz : z0 * j = j * z0)
    (hjt : j * t = t * j) (ht : t = τ * u * τ⁻¹) :
    (j⁻¹ * τ) * b * (j⁻¹ * τ)⁻¹ = z0 ∧ (j⁻¹ * τ) * z0 * (j⁻¹ * τ)⁻¹ = b ∧
      (j⁻¹ * τ) * u * (j⁻¹ * τ)⁻¹ = t := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      (j⁻¹ * τ) * b * (j⁻¹ * τ)⁻¹ = j⁻¹ * (τ * b * τ⁻¹) * j := by group
      _ = j⁻¹ * z0 * j := by rw [hτb]
      _ = j⁻¹ * (z0 * j) := by group
      _ = j⁻¹ * (j * z0) := by rw [hjz]
      _ = z0 := by group
  · calc
      (j⁻¹ * τ) * z0 * (j⁻¹ * τ)⁻¹ = j⁻¹ * (τ * z0 * τ⁻¹) * j := by group
      _ = j⁻¹ * b * j := by rw [hτz]
      _ = j⁻¹ * (b * j) := by group
      _ = j⁻¹ * (j * b) := by rw [← hjb]
      _ = b := by group
  · calc
      (j⁻¹ * τ) * u * (j⁻¹ * τ)⁻¹ = j⁻¹ * (τ * u * τ⁻¹) * j := by group
      _ = j⁻¹ * t * j := by rw [ht]
      _ = j⁻¹ * (t * j) := by group
      _ = j⁻¹ * (j * t) := by rw [← hjt]
      _ = t := by group

omit [Finite G] in
private lemma frame_fix_roots [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)} {τ j : G}
    (hfixτ : ∀ i : Fin n, 2 ≤ (i : ℕ) →
      (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj τ).toMonoidHom =
        (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj j).toMonoidHom) :
    ∀ i : Fin n, 2 ≤ (i : ℕ) →
      (pullSL φ (blockSL2 (ZMod 2) n i).range).map
          (MulAut.conj (j⁻¹ * τ)).toMonoidHom =
        pullSL φ (blockSL2 (ZMod 2) n i).range := by
  intro i hi
  have h := hfixτ i hi
  have hcomp : (MulAut.conj (j⁻¹ * τ)).toMonoidHom =
      (MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj τ).toMonoidHom := by
    ext x
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hid : (MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj j).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_coe, MulAut.conj_apply, MonoidHom.id_apply]
    group
  calc
    (pullSL φ (blockSL2 (ZMod 2) n i).range).map
        (MulAut.conj (j⁻¹ * τ)).toMonoidHom
        = (pullSL φ (blockSL2 (ZMod 2) n i).range).map
            ((MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj τ).toMonoidHom) := by rw [hcomp]
    _ = ((pullSL φ (blockSL2 (ZMod 2) n i).range).map
          (MulAut.conj τ).toMonoidHom).map (MulAut.conj j⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
    _ = ((pullSL φ (blockSL2 (ZMod 2) n i).range).map
          (MulAut.conj j).toMonoidHom).map (MulAut.conj j⁻¹).toMonoidHom := by rw [h]
    _ = (pullSL φ (blockSL2 (ZMod 2) n i).range).map
          ((MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj j).toMonoidHom) := by
      rw [Subgroup.map_map]
    _ = (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MonoidHom.id G) := by rw [hid]
    _ = pullSL φ (blockSL2 (ZMod 2) n i).range := Subgroup.map_id _

omit [Finite G] in
private lemma frame_pullSL_block_zero [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)}
    {z : Fin 3 → ↥L} {u : ↥L} (hu : φ u = blockSL2 (ZMod 2) n 0 sTwo)
    (hφ0 : φ (z 0) = tOne n) :
    pullSL φ (blockSL2 (ZMod 2) n 0).range =
      Subgroup.zpowers (z 0 : G) ⊔ Subgroup.zpowers (u : G) := by
  have hz0 : (φ.symm (tOne n) : ↥L) = z 0 := by rw [← hφ0]; simp
  have hu' : (φ.symm (blockSL2 (ZMod 2) n 0 sTwo) : ↥L) = u := by rw [← hu]; simp
  rw [range_blockSL2_eq n 0, pullSL]
  simp only [Subgroup.map_sup, MonoidHom.map_zpowers]
  change Subgroup.zpowers ((φ.symm (tOne n) : ↥L) : G) ⊔
      Subgroup.zpowers ((φ.symm (blockSL2 (ZMod 2) n 0 sTwo) : ↥L) : G) =
    Subgroup.zpowers (z 0 : G) ⊔ Subgroup.zpowers (u : G)
  rw [hz0, hu']

omit [Finite G] in
private lemma frame_K0 [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)} {z : Fin 3 → ↥L}
    {uz : ↥L} {g t b : G} (hu : φ uz = blockSL2 (ZMod 2) n 0 sTwo)
    (hφ0 : φ (z 0) = tOne n) (hg_z : g * (z 0 : G) * g⁻¹ = b)
    (hg_u : g * (uz : G) * g⁻¹ = t) :
    (pullSL φ (blockSL2 (ZMod 2) n 0).range).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers b ⊔ Subgroup.zpowers t := by
  rw [frame_pullSL_block_zero hu hφ0]
  simp only [Subgroup.map_sup, MonoidHom.map_zpowers]
  have hgz : (MulAut.conj g).toMonoidHom (z 0 : G) = b := by simpa [MulAut.conj_apply] using hg_z
  have hgu : (MulAut.conj g).toMonoidHom (uz : G) = t := by simpa [MulAut.conj_apply] using hg_u
  rw [hgz, hgu]

omit [Finite G] in
private lemma frame_A_spec [NeZero n] (hn2 : 2 ≤ n) (φ : ↥L ≃* SL(n + 1, ZMod 2))
    (τ : G) :
    IsSimpleGroup ↥((pullSL φ (blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range).map
        (MulAut.conj τ).toMonoidHom) ∧
      Nat.card ((pullSL φ (blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range).map
        (MulAut.conj τ).toMonoidHom) = 168 := by
  have h1 := simple_card_map (A := (blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range)
    (isSimpleGroup_range_blockSL_three n hn2) (card_range_blockSL_three n hn2)
    (f := φ.symm.toMonoidHom) φ.symm.injective
  have h2 := simple_card_map h1.1 h1.2 (f := L.subtype) (Subgroup.subtype_injective L)
  have h3 := simple_card_map h2.1 h2.2 (f := (MulAut.conj τ).toMonoidHom)
    (MulAut.conj τ).injective
  exact h3

private lemma frame_comm_A [NeZero n] (hA : HypA G n b L) {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) {φ : ↥L ≃* SL(n + 1, ZMod 2)} (hφ0 : φ (z 0) = tOne n)
    {τ : G} (hτb : τ * b * τ⁻¹ = z 0) (hτz : τ * (z 0 : G) * τ⁻¹ = b)
    (hτJ : (frameJ φ).map (MulAut.conj τ).toMonoidHom = frameJ φ) {x : G}
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) (hxb : x * b = b * x)
    (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k) (hn2 : 2 ≤ n) :
    ∀ y ∈ (pullSL φ (blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range).map
      (MulAut.conj τ).toMonoidHom, x * y = y * x := by
  have hxJ : ∀ j ∈ frameJ φ, x * j = j * x := by
    intro j hj
    exact ((Subgroup.mem_centralizer_iff.mp hxL) j (pullSL_le φ (jBlock n).range hj)).symm
  have hxz : x * (z 0 : G) * x⁻¹ ∈ Subgroup.zpowers (z 0 : G) := by
    have hc : x * (z 0 : G) = (z 0 : G) * x :=
      ((Subgroup.mem_centralizer_iff.mp hxL) (z 0 : G) (z 0).2).symm
    have h : x * (z 0 : G) * x⁻¹ = z 0 := by rw [hc]; group
    rw [h]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hx3 : Nat.Coprime (orderOf x) 3 := by
    obtain ⟨k, hk⟩ := hx2
    rw [hk]
    exact Nat.Coprime.pow_left k (by decide)
  have hcomm := commute_map_conj hA hz hφ0 hτb hτz hτJ hxb hxJ hxz hx3
  intro y hy
  exact hcomm y (Subgroup.map_mono (f := (MulAut.conj τ).toMonoidHom)
    (pullSL_le φ (blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range) hy)

private lemma frame_odd_core [NeZero n] (hG : IsCharTwoType G) (hA : HypA G n b L)
    {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z) {φ : ↥L ≃* SL(n + 1, ZMod 2)}
    (hφ0 : φ (z 0) = tOne n) {τ : G} (hτb : τ * b * τ⁻¹ = z 0)
    (hτz : τ * (z 0 : G) * τ⁻¹ = b)
    (hτJ : (frameJ φ).map (MulAut.conj τ).toMonoidHom = frameJ φ) (hn2 : 2 ≤ n) :
    ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b} : Set G) →
      (R.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
        Odd (Nat.card R) := by
  let B3 : Subgroup SL(n + 1, ZMod 2) :=
    (blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range
  let A : Subgroup G := (pullSL φ B3).map (MulAut.conj τ).toMonoidHom
  have hAspec : IsSimpleGroup ↥A ∧ Nat.card A = 168 := by
    simpa [A, B3] using frame_A_spec hn2 φ τ
  have hz0ord : orderOf (z 0 : ↥L) = 3 := by
    have h := (MulEquiv.orderOf_eq φ (z 0)).symm
    rw [hφ0, orderOf_tOne n] at h
    exact h
  have h3L : 3 ∣ Nat.card L := by
    have h := orderOf_dvd_natCard (z 0)
    rwa [hz0ord] at h
  have hz0P : (z 0 : G) ∈ pullSL φ B3 := by
    rw [mem_pullSL_iff]
    rw [hφ0]
    exact tOne_mem_range_blockSL_three n hn2
  have hbA : b ∈ A := by
    have hbz : b = (MulAut.conj τ).toMonoidHom (z 0 : G) := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      exact hτz.symm
    rw [hbz]
    exact Subgroup.mem_map_of_mem _ hz0P
  have hDA : ∀ x : G, x ∈ Subgroup.centralizer (L : Set G) → x * b = b * x →
      (∃ k : ℕ, orderOf x = 2 ^ k) → ∀ y ∈ A, x * y = y * x := by
    intro x hxL hxb hx2 y hy
    exact frame_comm_A hA hz hφ0 hτb hτz hτJ hxL hxb hx2 hn2 y
      (by simpa [A, B3] using hy)
  intro R hRb hRN hR3
  exact odd_card_of_normal hG hA.ord hA.le hA.nor hz.simple h3L hAspec.1 hAspec.2 hbA hDA
    R hRb hRN hR3

private abbrev FrameBase [NeZero n] (z : Fin 3 → ↥L) (b : G)
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) (τ j : G) : Prop :=
  φ (z 0) = tOne n ∧ τ * b * τ⁻¹ = (z 0 : G) ∧ τ * (z 0 : G) * τ⁻¹ = b ∧
    (frameJ φ).map (MulAut.conj τ).toMonoidHom = frameJ φ ∧
    (∀ i : Fin n, 2 ≤ (i : ℕ) →
      (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj τ).toMonoidHom =
        (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj j).toMonoidHom) ∧
    j ∈ frameJ φ ∧
    L.map (MulAut.conj (j⁻¹ * τ)).toMonoidHom = L.map (MulAut.conj τ).toMonoidHom

private abbrev FrameUT [NeZero n] (z : Fin 3 → ↥L) (b : G)
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) (τ j : G) (u : ↥L) (t : G) : Prop :=
  φ u = blockSL2 (ZMod 2) n 0 sTwo ∧ orderOf (u : G) = 2 ∧
    (u : G) * b = b * (u : G) ∧ (u : G) * (z 0 : G) * (u : G)⁻¹ = (z 0 : G)⁻¹ ∧
    (∀ j' ∈ frameJ φ, (u : G) * j' = j' * (u : G)) ∧
    (j⁻¹ * τ) * b * (j⁻¹ * τ)⁻¹ = (z 0 : G) ∧
    (j⁻¹ * τ) * (z 0 : G) * (j⁻¹ * τ)⁻¹ = b ∧
    (j⁻¹ * τ) * (u : G) * (j⁻¹ * τ)⁻¹ = t ∧
    orderOf t = 2 ∧ t * b * t⁻¹ = b⁻¹ ∧ t * (z 0 : G) = (z 0 : G) * t ∧
    (∀ j' ∈ frameJ φ, t * j' = j' * t) ∧ (∀ y ∈ L, t * y = y * t)

private abbrev FrameSetup [NeZero n] (z : Fin 3 → ↥L) (b : G) : Prop :=
  ∃ (φ : ↥L ≃* SL(n + 1, ZMod 2)) (τ j : G), FrameBase z b φ τ j

private abbrev FrameSetup2 [NeZero n] (z : Fin 3 → ↥L) (b : G) : Prop :=
  ∃ (φ : ↥L ≃* SL(n + 1, ZMod 2)) (τ j : G) (u : ↥L) (t : G),
    FrameBase z b φ τ j ∧ FrameUT z b φ τ j u t

private abbrev FrameAll [NeZero n] (z : Fin 3 → ↥L) (b : G) (hn1 : 1 < n) : Prop :=
  ∃ (φ : ↥L ≃* SL(n + 1, ZMod 2)) (τ j : G) (u : ↥L) (t : G) (K : ℕ → Subgroup G),
    FrameBase z b φ τ j ∧ FrameUT z b φ τ j u t ∧
    K = frameK φ (Subgroup.zpowers b ⊔ Subgroup.zpowers t)
      ((pullSL φ (frameSys n ⟨1, hn1⟩)).map
        (MulAut.conj (j⁻¹ * τ)).toMonoidHom) ∧
    (⨆ i : Fin n, K (i : ℕ)) = L.map (MulAut.conj (j⁻¹ * τ)).toMonoidHom ∧
    (∀ y ∈ L.map (MulAut.conj τ).toMonoidHom, (u : G) * y = y * (u : G)) ∧
    (∀ y ∈ L.map (MulAut.conj τ).toMonoidHom, (z 0 : G) * y = y * (z 0 : G)) ∧
    K (n + 1) = pullSL φ (blockSL2 (ZMod 2) n 0).range ∧
    (z 0 : G) ∈ pullSL φ (blockSL2 (ZMod 2) n 0).range

private lemma frame_setup [NeZero n] (hA : HypA G n b L) {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) (hM : ContainsMonomial b z) : FrameSetup (n := n) z b := by
  have hn4 : 4 ≤ n := by rcases hA.n_cases with rfl | rfl <;> norm_num
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hA.model
  obtain ⟨φ, hφ0, hφ1, _hφ2⟩ := exists_frameModel hA.n_cases ⟨e⟩ hz
  obtain ⟨τ, hτb, hτz, hτ1, _hτ2⟩ := exists_swap_of_containsMonomial (b := b) (L := L) hM
  have hτJ := map_conj_frameJ hA hz hφ0 hφ1 hτb hτz hτ1
  obtain ⟨j, hjJ, hfixτ⟩ := exists_mem_frameJ_map_conj_eq hn4 hτJ
  have hjL : j ∈ L := pullSL_le φ (jBlock n).range hjJ
  have hjLτ : j ∈ L.map (MulAut.conj τ).toMonoidHom := by
    have hj' : j ∈ (frameJ φ).map (MulAut.conj τ).toMonoidHom := by rw [hτJ]; exact hjJ
    exact Subgroup.map_mono (pullSL_le φ (jBlock n).range) hj'
  have hLg : L.map (MulAut.conj (j⁻¹ * τ)).toMonoidHom =
      L.map (MulAut.conj τ).toMonoidHom := by
    have hcomp : (MulAut.conj (j⁻¹ * τ)).toMonoidHom =
        (MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj τ).toMonoidHom := by
      ext x
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, Function.comp_apply,
        MonoidHom.coe_coe, MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hjLτ))
  exact ⟨φ, τ, j, hφ0, hτb, hτz, hτJ, hfixτ, hjJ, hLg⟩

private lemma frame_ut [NeZero n] (hA : HypA G n b L) {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) (D : FrameSetup (n := n) z b) : FrameSetup2 (n := n) z b := by
  obtain ⟨φ, τ, j, hBase⟩ := D
  obtain ⟨hφ0, hτb, hτz, hτJ, hfixτ, hjJ, hLg⟩ := hBase
  have hn4 : 4 ≤ n := by rcases hA.n_cases with rfl | rfl <;> norm_num
  let u : ↥L := φ.symm (blockSL2 (ZMod 2) n 0 sTwo)
  have hu : φ u = blockSL2 (ZMod 2) n 0 sTwo := φ.apply_symm_apply _
  have hu2 : orderOf (u : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact frame_u_orderOf φ
  have hu_comm_b : (u : G) * b = b * (u : G) := frame_mem_L_comm_b hA
  have huz : (u : G) * (z 0 : G) * (u : G)⁻¹ = (z 0 : G)⁻¹ := frame_u_conj_z hu hφ0
  have huJ : ∀ j' ∈ frameJ φ, (u : G) * j' = j' * (u : G) :=
    fun j' hj => frame_u_comm_J hu hj
  let t : G := τ * (u : G) * τ⁻¹
  have ht_order : orderOf t = 2 := frame_t_orderOf hu2
  have ht_inv : t * b * t⁻¹ = b⁻¹ := frame_t_inv_b hτz huz rfl
  have ht_comm_z : t * (z 0 : G) = (z 0 : G) * t := frame_t_comm_z hτb hu_comm_b rfl
  have ht_comm_J : ∀ j' ∈ frameJ φ, t * j' = j' * t :=
    fun j' hj => frame_t_comm_J (t := t) rfl hτJ huJ hj
  have ht_comm_L : ∀ y ∈ L, t * y = y * t :=
    frame_t_comm_L hn4 hA hz hφ0 ht_inv ht_order ht_comm_z ht_comm_J
  have hjL : j ∈ L := pullSL_le φ (jBlock n).range hjJ
  have hjb : j * b = b * j :=
    ((Subgroup.mem_centralizer_iff.mp (hA.le hjL)) b (by simp)).symm
  have hjz : (z 0 : G) * j = j * (z 0 : G) := commute_of_mem_frameJ hφ0 hjJ
  have hjt : j * t = t * j := (ht_comm_L j hjL).symm
  obtain ⟨hg_b, hg_z, hg_u⟩ := frame_g_facts (z0 := (z 0 : G)) (u := (u : G))
    (j := j) (t := t) hτb hτz hjb hjz hjt rfl
  exact ⟨φ, τ, j, u, t, ⟨hφ0, hτb, hτz, hτJ, hfixτ, hjJ, hLg⟩,
    ⟨hu, hu2, hu_comm_b, huz, huJ, hg_b, hg_z, hg_u, ht_order, ht_inv,
      ht_comm_z, ht_comm_J, ht_comm_L⟩⟩

private lemma frame_Kdata [NeZero n] (hA : HypA G n b L) {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) (hn1 : 1 < n) (D : FrameSetup2 (n := n) z b) :
    FrameAll (n := n) z b hn1 := by
  obtain ⟨φ, τ, j, u, t, hBase, hUT⟩ := D
  obtain ⟨hφ0, hτb, hτz, hτJ, hfixτ, hjJ, hLg⟩ := hBase
  obtain ⟨hu, hu2, hu_comm_b, huz, huJ, hg_b, hg_z, hg_u, ht_order, ht_inv,
    ht_comm_z, ht_comm_J, ht_comm_L⟩ := hUT
  let K1 : Subgroup G := (pullSL φ (frameSys n ⟨1, hn1⟩)).map (MulAut.conj (j⁻¹ * τ)).toMonoidHom
  let K : ℕ → Subgroup G := frameK φ (Subgroup.zpowers b ⊔ Subgroup.zpowers t) K1
  have hK0 := frame_K0 (uz := u) hu hφ0 hg_z hg_u
  have hconj := a2System_frameK_conj hn1 φ hK0 (frame_fix_roots hfixτ)
  have hjoin : (⨆ i : Fin n, K (i : ℕ)) =
      L.map (MulAut.conj (j⁻¹ * τ)).toMonoidHom := by
    simpa [K, K1] using hconj.2.1
  have hu_comm_Lτ : ∀ y ∈ L.map (MulAut.conj τ).toMonoidHom,
      (u : G) * y = y * (u : G) := by
    have h3 : Nat.Coprime (orderOf (u : G)) 3 := by rw [hu2]; decide
    have huz' : (u : G) * (z 0 : G) * (u : G)⁻¹ ∈ Subgroup.zpowers (z 0 : G) := by
      rw [huz]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp⟩
    exact commute_map_conj hA hz hφ0 hτb hτz hτJ hu_comm_b huJ huz' h3
  have hz_comm_Lτ : ∀ y ∈ L.map (MulAut.conj τ).toMonoidHom,
      (z 0 : G) * y = y * (z 0 : G) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have hwb : w * b = b * w := ((Subgroup.mem_centralizer_iff.mp (hA.le hw)) b (by simp)).symm
    calc
      (z 0 : G) * (τ * w * τ⁻¹) = τ * (b * w) * τ⁻¹ := by rw [← hτb]; group
      _ = τ * (w * b) * τ⁻¹ := by rw [← hwb]
      _ = (τ * w * τ⁻¹) * (z 0 : G) := by rw [← hτb]; group
  have hKn1 : K (n + 1) = pullSL φ (blockSL2 (ZMod 2) n 0).range := by
    have hrev : (⟨n - 1, by omega⟩ : Fin n).rev = 0 := by
      apply Fin.ext
      simp [Fin.rev]
      omega
    have h := frameK_add_two φ (Subgroup.zpowers b ⊔ Subgroup.zpowers t) K1
      ⟨n - 1, by omega⟩
    have hidx : n - 1 + 2 = n + 1 := by omega
    rw [hrev] at h
    simpa [K, hidx] using h
  have hz0P : (z 0 : G) ∈ pullSL φ (blockSL2 (ZMod 2) n 0).range := by
    rw [mem_pullSL_iff, hφ0, tOne, MonoidHom.mem_range]
    exact ⟨rhoTwo, rfl⟩
  exact ⟨φ, τ, j, u, t, K, ⟨hφ0, hτb, hτz, hτJ, hfixτ, hjJ, hLg⟩,
    ⟨hu, hu2, hu_comm_b, huz, huJ, hg_b, hg_z, hg_u, ht_order, ht_inv,
      ht_comm_z, ht_comm_J, ht_comm_L⟩, rfl, hjoin, hu_comm_Lτ, hz_comm_Lτ, hKn1, hz0P⟩

private theorem exists_frameSystem_aux [NeZero n] (hG : IsCharTwoType G)
    (hA : HypA G n b L) {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z)
    (hM : ContainsMonomial b z) : ∃ (K : ℕ → Subgroup G) (t : G), FrameSystem n b L K t := by
  have hn1 : 1 < n := by rcases hA.n_cases with rfl | rfl <;> norm_num
  have hn2 : 2 ≤ n := by rcases hA.n_cases with rfl | rfl <;> norm_num
  obtain ⟨φ, τ, j, u, t, K, hBase, hUT, hKdef, hjoin, hu_comm_Lτ, hz_comm_Lτ,
    hKn1, hz0P⟩ := frame_Kdata hA hz hn1 (frame_ut hA hz (frame_setup hA hz hM))
  obtain ⟨hφ0, hτb, hτz, hτJ, hfixτ, hjJ, hLg⟩ := hBase
  obtain ⟨hu, hu2, hu_comm_b, huz, huJ, hg_b, hg_z, hg_u, ht_order, ht_inv,
    ht_comm_z, ht_comm_J, ht_comm_L⟩ := hUT
  have hK0 : (pullSL φ (blockSL2 (ZMod 2) n 0).range).map
      (MulAut.conj (j⁻¹ * τ)).toMonoidHom =
      Subgroup.zpowers b ⊔ Subgroup.zpowers t :=
    frame_K0 (uz := u) hu hφ0 hg_z hg_u
  have hconj := a2System_frameK_conj hn1 φ hK0 (frame_fix_roots hfixτ)
  refine ⟨K, t, ?_, ?_, ?_, ht_order, ht_inv, ?_, ?_, ?_, ?_⟩
  · rw [hKdef]
    exact a2System_frameK_L φ (Subgroup.zpowers b ⊔ Subgroup.zpowers t)
      ((pullSL φ (frameSys n ⟨1, hn1⟩)).map (MulAut.conj (j⁻¹ * τ)).toMonoidHom)
  · rw [← hKdef] at hconj
    rw [← hjoin] at hconj
    exact hconj
  · rw [hKdef]; rfl
  · intro x hx y hy
    rw [hKdef] at hx; change x ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers t at hx
    have hbC : b ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_centralizer_iff.mpr fun w hw =>
        ((Subgroup.mem_centralizer_iff.mp (hA.le hw)) b (by simp)).symm
    have htC : t ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw => (ht_comm_L w hw).symm
    have hsup := sup_le (Subgroup.zpowers_le.mpr hbC) (Subgroup.zpowers_le.mpr htC)
    exact ((Subgroup.mem_centralizer_iff.mp (hsup hx)) y hy).symm
  · intro i hi
    simpa [hKdef] using exists_conj_mem_frameK hn1 hA.ord hφ0 hτb t (j⁻¹ * τ) i hi
  · exact frame_odd_core hG hA hz hφ0 hτb hτz hτJ hn2
  · refine ⟨j⁻¹ * τ, ?_, ?_, ?_⟩
    · rw [hg_b, hKn1]
      exact hz0P
    · exact hjoin
    · intro x hx y hy
      rw [hKn1, frame_pullSL_block_zero hu hφ0] at hx
      rw [hLg] at hy
      have hzC : (z 0 : G) ∈ Subgroup.centralizer
          (L.map (MulAut.conj τ).toMonoidHom : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => (hz_comm_Lτ y hy).symm
      have huC : (u : G) ∈ Subgroup.centralizer
          (L.map (MulAut.conj τ).toMonoidHom : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => (hu_comm_Lτ y hy).symm
      have hsup := sup_le (Subgroup.zpowers_le.mpr hzC) (Subgroup.zpowers_le.mpr huC)
      exact ((Subgroup.mem_centralizer_iff.mp (hsup hx)) y hy).symm

theorem exists_frameSystem {G : Type} [Group G] [Finite G] (hG : IsCharTwoType G) {n : ℕ}
    {b : G} {L : Subgroup G} (hA : HypA G n b L) {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z)
    (hM : ContainsMonomial b z) : ∃ (K : ℕ → Subgroup G) (t : G), FrameSystem n b L K t := by
  rcases hA.n_cases with rfl | rfl
  · exact exists_frameSystem_aux hG hA hz hM
  · exact exists_frameSystem_aux hG hA hz hM

theorem frameStep_holds : FrameStep := by
  intro G _ _ _ _ hG n b L hA z hP
  exact exists_frameSystem hG hA hP.model
    (hP.out.elim (fun h => h.1.1) (fun h => h.1))

end CFSG.StandardType.FF81
