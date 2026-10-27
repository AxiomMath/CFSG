module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148APGLConjLeaves
import CFSG.RankThree.PartTwo.Sec14.Ronan148NCent
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Ronan148DM24
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofModel
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

@[expose] def Step148OmegaRankThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ e ∈ A, Subgroup.zpowers e ∈ omegaA A → ∀ Le ∈ lA A e,
      IsLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) →
      ∀ F : Subgroup G, e ∈ F → CFSG.Open.IsElemAbelian 3 F → Nat.card F = 81 → False

section Elem

variable {X : Type*} [Group X]

theorem exists_mul_of_mem_sup_of_commute {S T : Subgroup X}
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : X} (hx : x ∈ S ⊔ T) :
    ∃ y ∈ S, ∃ z ∈ T, y * z = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, T.one_mem, mul_one x⟩
    · exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, S.one_mem, 1, T.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := ihx
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := ihy
    have h := hcomm y2 hy2 z1 hz1
    refine ⟨y1 * y2, S.mul_mem hy1 hy2, z1 * z2, T.mul_mem hz1 hz2, ?_⟩
    calc y1 * y2 * (z1 * z2) = y1 * (y2 * z1) * z2 := by simp only [mul_assoc]
      _ = y1 * (z1 * y2) * z2 := by rw [h]
      _ = y1 * z1 * (y2 * z2) := by simp only [mul_assoc]
  | inv x _ ih =>
    obtain ⟨y, hy, z, hz, rfl⟩ := ih
    refine ⟨y⁻¹, S.inv_mem hy, z⁻¹, T.inv_mem hz, ?_⟩
    rw [hcomm y hy z hz, mul_inv_rev]

theorem le_normalizer_of_commute {S T : Subgroup X}
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) : S ≤ Subgroup.normalizer (T : Set X) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    rw [hcomm s hs t ht, mul_inv_cancel_right]
    exact ht
  · intro ht
    have h1 := hcomm s⁻¹ (S.inv_mem hs) _ ht
    rw [show s⁻¹ * (s * t * s⁻¹) = t * s⁻¹ by group] at h1
    have h2 : t = s * t * s⁻¹ := mul_right_cancel h1
    rw [h2]
    exact ht

theorem isElemAbelian_sup_of_commute {S T : Subgroup X} (hS : CFSG.Open.IsElemAbelian 3 S)
    (hT : CFSG.Open.IsElemAbelian 3 T) (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    CFSG.Open.IsElemAbelian 3 (S ⊔ T) := by
  have hcS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hS.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc : ∀ x ∈ S ⊔ T, ∀ y ∈ S ⊔ T, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    have h1 : x₂ * y₁ = y₁ * x₂ := (hcomm y₁ hy₁ x₂ hx₂).symm
    have h2 : y₂ * x₁ = x₁ * y₂ := (hcomm x₁ hx₁ y₂ hy₂).symm
    calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by simp only [mul_assoc]
      _ = x₁ * (y₁ * x₂) * y₂ := by rw [h1]
      _ = (x₁ * y₁) * (x₂ * y₂) := by simp only [mul_assoc]
      _ = (y₁ * x₁) * (y₂ * x₂) := by rw [hcS x₁ hx₁ y₁ hy₁, hcT x₂ hx₂ y₂ hy₂]
      _ = y₁ * (x₁ * y₂) * x₂ := by simp only [mul_assoc]
      _ = y₁ * (y₂ * x₁) * x₂ := by rw [h2]
      _ = y₁ * y₂ * (x₁ * x₂) := by simp only [mul_assoc]
  refine ⟨⟨⟨fun x y => Subtype.ext (hc x.1 x.2 y.1 y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
  rw [Commute.mul_pow (hcomm x₁ hx₁ x₂ hx₂) 3, hS.2 x₁ hx₁, hT.2 x₂ hx₂, one_mul]

theorem isElemAbelian_zpowers {x : X} (hx : x ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isElemAbelian_map {Y : Type*} [Group Y] (f : X →* Y) {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 3 E) : CFSG.Open.IsElemAbelian 3 (E.map f) := by
  have hcE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hxa, ← hzb, ← map_mul, hcE x hx z hz]
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow, hE.2 x hx, map_one]

end Elem

theorem exists_e9_mem_of_isoLThreePi {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8))
    {x : X} (hx : x ^ 3 = 1) :
    ∃ E : Subgroup X, x ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, x₂, -, -, h12, hx1, hx2, hP9, -⟩ :=
    Sec13.L3Proof.exists_heis_data_of_isoLThreePi he hiso
  have hfac := Sec13.Item138Proof.factorization_card_three_eq_two he hiso h9
  have hHab : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := by
    refine isElemAbelian_sup_of_commute (isElemAbelian_zpowers hx1) (isElemAbelian_zpowers hx2) ?_
    intro s hs t ht
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (Commute.zpow_zpow h12 i j).eq
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [hP9, Subgroup.card_top, hfac]; norm_num)
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact (isElemAbelian_zpowers hx).2 g g.2)⟩
  obtain ⟨P, hxP⟩ := hxp.exists_le_sylow
  have hSylP : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup X) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by
      rw [Subgroup.card_top]
      exact Sylow.card_eq_multiplicity P)
  obtain ⟨n, -, hn⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hSylH hSylP
  refine ⟨P, hxP (Subgroup.mem_zpowers x), ?_, ?_⟩
  · rw [hn]
    exact isElemAbelian_map _ hHab
  · rw [Sylow.card_eq_multiplicity P, hfac]
    norm_num

section Quot

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem exists_e81_of_conj148 {J : Subgroup G} {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hJpi : Sec4.IsoLThreePi ↥(img148 A Y J) p f) (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8))
    (hJZ : Subgroup.center ↥(img148 A Y J) = ⊥) (x : ↥(Y ⊔ A) ⧸ ker148 A Y)
    (hDC : (img148 A Y J).map (MulAut.conj x).toMonoidHom ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {e : G} (he : e ∈ A) (he3 : e ^ 3 = 1)
    (heD : alpha148 A Y e he ∈ (img148 A Y J).map (MulAut.conj x).toMonoidHom) :
    ∃ F : Subgroup G, e ∈ F ∧ CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Jb := img148 A Y J with hJb
  set D := Jb.map (MulAut.conj x).toMonoidHom with hD
  have hDpi : Sec4.IsoLThreePi ↥D p f :=
    isoLThreePi_of_mulEquiv148 (Jb.equivMapOfInjective _ (MulAut.conj x).injective).symm hJpi
  obtain ⟨E₁', -, hE₁', hE₁9'⟩ := exists_e9_mem_of_isoLThreePi hf hJpi h9 (x := 1) (one_pow 3)
  have heα3 : (⟨alpha148 A Y e he, heD⟩ : ↥D) ^ 3 = 1 := by
    apply Subtype.ext
    have h' : (⟨e, Subgroup.mem_sup_right he⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext he3
    change (QuotientGroup.mk' (ker148 A Y) ⟨e, Subgroup.mem_sup_right he⟩) ^ 3 = 1
    rw [← map_pow, h', map_one]
  obtain ⟨E₂', heE₂', hE₂', hE₂9'⟩ := exists_e9_mem_of_isoLThreePi hf hDpi h9 heα3
  set E₁ := E₁'.map Jb.subtype with hE₁def
  set E₂ := E₂'.map D.subtype with hE₂def
  have hE₁J : E₁ ≤ Jb := Subgroup.map_subtype_le _
  have hE₂D : E₂ ≤ D := Subgroup.map_subtype_le _
  have hE₁ : CFSG.Open.IsElemAbelian 3 E₁ := isElemAbelian_map _ hE₁'
  have hE₂ : CFSG.Open.IsElemAbelian 3 E₂ := isElemAbelian_map _ hE₂'
  have hE₁9 : Nat.card E₁ = 9 := by
    rw [hE₁def, Subgroup.card_map_of_injective Jb.subtype_injective, hE₁9']
  have hE₂9 : Nat.card E₂ = 9 := by
    rw [hE₂def, Subgroup.card_map_of_injective D.subtype_injective, hE₂9']
  have heE₂ : alpha148 A Y e he ∈ E₂ := ⟨_, heE₂', rfl⟩
  have hcomm : ∀ s ∈ E₁, ∀ t ∈ E₂, s * t = t * s := fun s hs t ht =>
    Subgroup.mem_centralizer_iff.mp (hDC (hE₂D ht)) s (hE₁J hs)
  set E := E₁ ⊔ E₂ with hE
  have hEab : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_sup_of_commute hE₁ hE₂ hcomm
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzJ : z ∈ Jb := hE₁J hz.1
    have hzZ : (⟨z, hzJ⟩ : ↥Jb) ∈ Subgroup.center ↥Jb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDC (hE₂D hz.2)) g g.2)
    rw [hJZ, Subgroup.mem_bot] at hzZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hzZ
  have hcard := Sec6.card_sup_mul_card_inf (le_normalizer_of_commute hcomm)
  rw [hinf, Subgroup.card_bot, mul_one, hE₁9, hE₂9] at hcard
  set φ : ↥(Y ⊔ A) →* ↥(Y ⊔ A) ⧸ ker148 A Y := QuotientGroup.mk' (ker148 A Y) with hφ
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    rw [hφ, QuotientGroup.ker_mk']
    exact Main148.not_three_dvd_card_ker148
  have hEU : E ≤ (⊤ : Subgroup ↥(Y ⊔ A)).map φ := by
    intro z _
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) z
    exact ⟨w, trivial, rfl⟩
  set e' : ↥(Y ⊔ A) := ⟨e, Subgroup.mem_sup_right he⟩ with he'
  have he'3 : e' ^ 3 = 1 := Subtype.ext he3
  have hDE : (Subgroup.zpowers e').map φ ≤ E := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right heE₂
  have hDp : IsPGroup 3 (Subgroup.zpowers e') := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact (isElemAbelian_zpowers he'3).2 g g.2)⟩
  obtain ⟨T, -, hDT, -, hT81, hT⟩ :=
    Ronan148D.exists_lift_elemAbelian Nat.prime_three φ hker hEU hEab le_top hDE hDp
  refine ⟨T.map (Y ⊔ A).subtype, ⟨e', hDT (Subgroup.mem_zpowers e'), rfl⟩,
    isElemAbelian_map _ hT, ?_⟩
  rw [Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective, hT81, hcard]

end Quot

theorem card_mul_three_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) :
    ∃ π : Bool, Sec4.ModThree π (p ^ e) ∧ Nat.card X * 3 =
      (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * cond π ((p ^ e) ^ 3 - 1) ((p ^ e) ^ 3 + 1) := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he h
  exact ⟨π, hq, by rw [Nat.card_congr φ.toEquiv]; exact Sec13.card_projImage_slPi_mul_three hK hq⟩

theorem two_pow_card_ne {f : ℕ} (hf : 1 ≤ f) (π : Bool) :
    (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) ≠ 5630688 := by
  rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with rfl | rfl | h3
  · cases π <;> norm_num
  · cases π <;> norm_num
  · have h8 : 8 ≤ 2 ^ f :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    obtain ⟨n, hn⟩ : ∃ n, n = 2 ^ f := ⟨_, rfl⟩
    rw [← hn] at h8 ⊢
    have h1 : 512 ≤ n ^ 3 :=
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ n ^ 3 := Nat.pow_le_pow_left h8 3
    have h2 : 64 ≤ n ^ 2 :=
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left h8 2
    have h3' : 511 ≤ cond π (n ^ 3 - 1) (n ^ 3 + 1) := by
      cases π
      · change 511 ≤ n ^ 3 + 1
        omega
      · change 511 ≤ n ^ 3 - 1
        omega
    have h4 := Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega : 63 ≤ n ^ 2 - 1)) h3'
    omega

theorem isLThreePi_of_kType148 {G : Type} [Group G] [Finite G] {A Y : Subgroup G}
    [(ker148 A Y).Normal] {e : G} {K Le : Subgroup G} (hkt : KType148 A Y e K Le) {f : ℕ}
    (hf : 1 ≤ f) [Fact (Nat.Prime 2)] (hK : Sec4.IsoLThreePi ↥(img148 A Y K) 2 f) :
    IsLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) := by
  rcases hkt.2 with ⟨-, -, ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f', e', hp, hf', he', hL, -⟩⟩ |
      ⟨-, ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩⟩
  · exact ⟨2, f, inferInstance, hf, isoLThreePi_of_mulEquiv148 φ.symm hK⟩
  · exact absurd (isoLThreePi_of_mulEquiv148 φ.symm hK) (not_isoLThreePi_alternating_seven 2 f)
  · exact ⟨p, f' * e', hp, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      hL⟩
  · exact absurd (isoLThreePi_of_mulEquiv148 φ.symm hK) (not_isoLThreePi_alternating_seven 2 f)
  · exfalso
    haveI := h7
    have h7iso : Sec4.IsoLThreePi ↥(img148 A Y K) 7 1 :=
      isoLThreePi_of_mulEquiv148 φ (Or.inl ⟨by norm_num, ⟨MulEquiv.refl _⟩⟩)
    obtain ⟨π₁, -, hc₁⟩ := card_mul_three_of_isoLThreePi hf hK
    obtain ⟨π₂, hq₂, hc₂⟩ := card_mul_three_of_isoLThreePi le_rfl h7iso
    cases π₂
    · change 7 ^ 1 % 3 = 2 at hq₂
      norm_num at hq₂
    · change Nat.card ↥(img148 A Y K) * 3 = (7 ^ 1) ^ 3 * ((7 ^ 1) ^ 2 - 1) * ((7 ^ 1) ^ 3 - 1)
        at hc₂
      norm_num at hc₂
      exact two_pow_card_ne hf π₁ (hc₁.symm.trans hc₂)

theorem step148PGLConjU3_of_rank (hR : Step148OmegaRankThree) : Ronan148A.Step148PGLConjU3 := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq f hf hq3 hq9 hpgl heΩ
    hLeA hX1 y hy D hDne hDC hAD heD hcent
  letI := ker148_normal hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.mem_partTwoF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  haveI : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  haveI hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hDne
    show (img148 A Y J).map _ = img148 A Y J
    rw [hbot, Subgroup.map_bot]
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  obtain ⟨hp, hJpi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
  haveI := hp
  have hJs : IsSimpleGroup ↥(img148 A Y J) :=
    (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hf hJpi).1
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h9 : ¬ (2 ^ f % 9 = 1 ∨ 2 ^ f % 9 = 8) := by
    obtain ⟨n, hn⟩ : ∃ n, n = 2 ^ f := ⟨_, rfl⟩
    rw [← hn] at hq3 hq9 ⊢
    omega
  obtain ⟨F, heF, hF, hF81⟩ := exists_e81_of_conj148 hf hJpi h9 hJZ _ hDC he (hA3 e he) heD
  have hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) 2 f := by
    rw [show img148 A Y K = img148 A Y J from hEq]
    exact hJpi
  exact hR G A c L h e he heΩ Le hLeA (isLThreePi_of_kType148 hkt hf hKpi) F heF hF hF81

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
