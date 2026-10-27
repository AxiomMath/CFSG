module

public import CFSG.RankThree.GF2n.Tim81.Sec4.HBarData
public import CFSG.RankThree.GF2n.Tim81.Sec4.KNonabelian
public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTISzInputs
public import CFSG.Timmesfeld.ARS.BasicLines
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.SuzukiTwoGroupsQuadratic
public import CFSG.Quasithin.Vol2.Ch3E215MH
public import CFSG.Quasithin.MS93.Sec2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec2
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem RootHyp.centralizer_le_M (h : RootHyp M V) :
    Subgroup.centralizer (V : Set G) ≤ M := by
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.toHyp.ne_bot
  have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  intro c hc
  have hcv : c * v = v * c := (Subgroup.mem_centralizer_iff.mp hc v hvV).symm
  exact h.toHyp.centralizer_le_M hvV hv1'
    (Subgroup.mem_centralizer_singleton_iff.mpr hcv)

theorem RootHyp.le_normalizer_centralizer_V (h : RootHyp M V) :
    M ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have hMleNV : M ≤ Subgroup.normalizer (V : Set G) := by
    simpa [← h.toHyp.normalizer_eq] using Subgroup.le_normalizer (H := V)
  exact hMleNV.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup V)

private theorem mem_center_suzukiU_of_mul_self
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hK : Nat.card F = 2 ^ (2 * a + 1)) {u : CFSG.Blueprint.suzukiGroup a F}
    (hu : u ∈ CFSG.LieType.Ree.suzukiU a F) (hu2 : u * u = 1) :
    u ∈ (Subgroup.center (CFSG.LieType.Ree.suzukiU a F)).map
      (CFSG.LieType.Ree.suzukiU a F).subtype := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB : CFSG.LieType.Ree.suzukiU a F ≤ CFSG.LieType.Ree.suzukiB a F :=
    CFSG.LieType.Ree.suzukiU_le_suzukiB a F
  by_cases hu1 : u = 1
  · rw [hu1]
    exact Subgroup.mem_map_of_mem (CFSG.LieType.Ree.suzukiU a F).subtype (Subgroup.one_mem _)
  · have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    obtain ⟨v, -, hv⟩ :=
      (CFSG.ShultStronglyClosedTI.SuzukiModel.mem_suzukiB_and_orderOf_eq_two_iff
        (a := a) (K := F) hK).1 ⟨hKB hu, hord⟩
    subst hv
    exact CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiSElt_zero_mem_center
      (a := a) (K := F) hK v

private theorem mem_center_conj_suzukiU_of_mul_self
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hK : Nat.card F = 2 ^ (2 * a + 1)) (g : CFSG.Blueprint.suzukiGroup a F)
    {w : CFSG.Blueprint.suzukiGroup a F}
    (hw : w ∈ conjSubgroup g (CFSG.LieType.Ree.suzukiU a F)) (hw2 : w * w = 1) :
    w ∈ (Subgroup.center (conjSubgroup g (CFSG.LieType.Ree.suzukiU a F))).map
      (conjSubgroup g (CFSG.LieType.Ree.suzukiU a F)).subtype := by
  classical
  obtain ⟨u, hu, hwu⟩ := Subgroup.mem_map.mp hw
  have hw2' : ((MulAut.conj g) u) * ((MulAut.conj g) u) = 1 := by rwa [← hwu] at hw2
  have hu2 : u * u = 1 := by
    have h := congrArg (fun t => g⁻¹ * t * g) hw2'
    simpa [mul_assoc] using h
  have huc : u ∈ (Subgroup.center (CFSG.LieType.Ree.suzukiU a F)).map
      (CFSG.LieType.Ree.suzukiU a F).subtype :=
    mem_center_suzukiU_of_mul_self hK hu hu2
  obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp huc
  rw [← hwu, ← hce]
  have hgc : (MulAut.conj g) (c : CFSG.Blueprint.suzukiGroup a F) ∈
      conjSubgroup g (CFSG.LieType.Ree.suzukiU a F) :=
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom c.2
  refine Subgroup.mem_map.mpr ⟨⟨(MulAut.conj g) (c : _), hgc⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp x.2
  have hcomm : y * (c : CFSG.Blueprint.suzukiGroup a F) = c * y :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  rw [← hxy]
  simp only [MulAut.conj_apply]
  show (g * y * g⁻¹) * (g * c * g⁻¹) = (g * c * g⁻¹) * (g * y * g⁻¹)
  calc (g * y * g⁻¹) * (g * c * g⁻¹) = g * (y * (c : _)) * g⁻¹ := by group
    _ = g * (c * y) * g⁻¹ := by rw [hcomm]
    _ = (g * c * g⁻¹) * (g * y * g⁻¹) := by group

private theorem inf_conj_szZ_eq_bot_of_ne
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) {x y : CFSG.Blueprint.suzukiGroup a F}
    (hne : conjSubgroup x (szZ a F) ≠ conjSubgroup y (szZ a F)) :
    conjSubgroup x (szZ a F) ⊓ conjSubgroup y (szZ a F) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  by_contra hu_ne
  have huA : u ∈ conjSubgroup x (szZ a F) := (Subgroup.mem_inf.mp hu).1
  have huB : u ∈ conjSubgroup y (szZ a F) := (Subgroup.mem_inf.mp hu).2
  have hB : conjSubgroup y (szZ a F) =
      conjSubgroup (y * x⁻¹) (conjSubgroup x (szZ a F)) := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  have hu2 : u ∈ conjSubgroup (y * x⁻¹) (conjSubgroup x (szZ a F)) := by
    rw [← hB]
    exact huB
  have hmem :=
    CFSG.RankThree.GF2n.Tim81.CentralTI.mem_normalizer_conjSubgroup_szZ_of_inf_ne_bot
      (a := a) hF hu_ne huA hu2
  have hEq : conjSubgroup (y * x⁻¹) (conjSubgroup x (szZ a F)) = conjSubgroup x (szZ a F) :=
    conjSubgroup_eq_self_iff.mpr hmem
  rw [← hB] at hEq
  exact hne hEq.symm

private theorem sq_eq_one_of_mem_conj_szZ
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hK : Nat.card F = 2 ^ (2 * a + 1)) {x : CFSG.Blueprint.suzukiGroup a F}
    {w : CFSG.Blueprint.suzukiGroup a F} (hw : w ∈ conjSubgroup x (szZ a F)) :
    w * w = 1 := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
  have hz2 : z * z = 1 := Sec2.szZ_mul_self (a := a) (K := F) hK hz
  calc (MulAut.conj x) z * (MulAut.conj x) z = (MulAut.conj x) (z * z) := by rw [map_mul]
    _ = 1 := by rw [hz2, map_one]

private theorem commute_of_mem_center_map {X : Type} [Group X] {S : Subgroup X} {p q : X}
    (hp : p ∈ (Subgroup.center S).map S.subtype)
    (hq : q ∈ (Subgroup.center S).map S.subtype) : p * q = q * p := by
  obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hp' q')).symm

private theorem isElemAbelian_of_le_center_map {X : Type} [Group X] {S B : Subgroup X}
    (hBS : B ≤ S) (hB : B ≤ (Subgroup.center S).map S.subtype)
    (hsq : ∀ b ∈ B, b * b = 1) :
    CFSG.Open.IsElemAbelian 2 B := by
  have hmemS : ∀ u : ↥B, (⟨(u : X), hBS u.2⟩ : ↥S) ∈ Subgroup.center S := by
    intro u
    obtain ⟨u', hu', hu'e⟩ := Subgroup.mem_map.mp (hB u.2)
    have heq : (⟨(u : X), hBS u.2⟩ : ↥S) = u' := Subtype.ext hu'e.symm
    rw [heq]
    exact hu'
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
  · have hcen := Subgroup.mem_center_iff.mp (hmemS u) (⟨(v : X), hBS v.2⟩ : ↥S)
    exact Subtype.ext (congrArg Subtype.val hcen).symm
  · rw [pow_two]
    exact hsq u hu

private theorem mem_center_of_mem_isSylow_conj_suzukiU
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hK : Nat.card F = 2 ^ (2 * a + 1))
    {S : Sylow 2 (CFSG.Blueprint.suzukiGroup a F)} {g : CFSG.Blueprint.suzukiGroup a F}
    (hS : (S : Subgroup (CFSG.Blueprint.suzukiGroup a F)) =
      conjSubgroup g (CFSG.LieType.Ree.suzukiU a F))
    {u : CFSG.Blueprint.suzukiGroup a F}
    (hu : u ∈ (S : Subgroup (CFSG.Blueprint.suzukiGroup a F))) (hu2 : u * u = 1) :
    u ∈ (Subgroup.center (S : Subgroup (CFSG.Blueprint.suzukiGroup a F))).map
      (S : Subgroup (CFSG.Blueprint.suzukiGroup a F)).subtype := by
  rw [hS] at hu ⊢
  exact mem_center_conj_suzukiU_of_mul_self hK g hu hu2

private theorem isElemAbelian_zpowers_sup_conj_szZ
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hK : Nat.card F = 2 ^ (2 * a + 1)) {y : CFSG.Blueprint.suzukiGroup a F}
    {z : CFSG.Blueprint.suzukiGroup a F}
    (hzB : z ∉ conjSubgroup y (szZ a F))
    (hzN : z ∈ Subgroup.normalizer
      (conjSubgroup y (szZ a F) : Set (CFSG.Blueprint.suzukiGroup a F)))
    (hz2 : z * z = 1) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers z ⊔ conjSubgroup y (szZ a F)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup (CFSG.Blueprint.suzukiGroup a F) := conjSubgroup y (szZ a F) with hB
  have hzB' : z ∉ B := by rw [hB]; exact hzB
  have hzN' : z ∈ Subgroup.normalizer (B : Set (CFSG.Blueprint.suzukiGroup a F)) := by
    rw [hB]; exact hzN
  have hBsq : ∀ w ∈ B, w * w = 1 := by
    intro w hw
    rw [hB] at hw
    exact sq_eq_one_of_mem_conj_szZ hK hw
  have hBp : IsPGroup 2 B := by
    rw [hB]
    exact isPGroup_two_of_isElemAbelian
      (isElemAbelian_conjSubgroup (Sec2.isElemAbelian_szZ (a := a) (K := F) hK) y)
  have hz1 : z ≠ 1 := fun h => hzB' (h ▸ B.one_mem)
  have hzp : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using hz2) hz1
  have hZpE : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers z) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) (by
      rw [← hzp]; exact pow_orderOf_eq_one z)
  have hZP : IsPGroup 2 (Subgroup.zpowers z) := hZpE.isPGroup
  set E : Subgroup (CFSG.Blueprint.suzukiGroup a F) := Subgroup.zpowers z ⊔ B with hE
  have hsupP : IsPGroup 2 E := by
    rw [hE]
    exact IsPGroup.to_sup_of_normal_right' hZP hBp (Subgroup.zpowers_le.mpr hzN')
  obtain ⟨S, hSB⟩ := hsupP.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ :=
    CFSG.ShultStronglyClosedTI.SuzukiModel.exists_sylow_eq_suzukiU (a := a) (K := F) hK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (CFSG.Blueprint.suzukiGroup a F) P₀ S
  have hScoe : (S : Subgroup (CFSG.Blueprint.suzukiGroup a F)) =
      conjSubgroup g (CFSG.LieType.Ree.suzukiU a F) := by
    rw [← hg, Sylow.coe_subgroup_smul, hP₀, Sec4.conj_smul_eq_conjSubgroup]
  have hzS : z ∈ (S : Subgroup (CFSG.Blueprint.suzukiGroup a F)) :=
    hSB (by rw [hE]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hBS : B ≤ (S : Subgroup (CFSG.Blueprint.suzukiGroup a F)) :=
    fun b hb => hSB (by rw [hE]; exact Subgroup.mem_sup_right hb)
  have hzZ : z ∈ (Subgroup.center (S : Subgroup (CFSG.Blueprint.suzukiGroup a F))).map
      (S : Subgroup (CFSG.Blueprint.suzukiGroup a F)).subtype :=
    mem_center_of_mem_isSylow_conj_suzukiU hK hScoe hzS hz2
  have hBZ : B ≤ (Subgroup.center (S : Subgroup (CFSG.Blueprint.suzukiGroup a F))).map
      (S : Subgroup (CFSG.Blueprint.suzukiGroup a F)).subtype :=
    fun b hb => mem_center_of_mem_isSylow_conj_suzukiU hK hScoe (hBS hb) (hBsq b hb)
  have hcomm : ∀ p ∈ Subgroup.zpowers z, ∀ q ∈ B, p * q = q * p :=
    fun p hp q hq => commute_of_mem_center_map (Subgroup.zpowers_le.mpr hzZ hp) (hBZ hq)
  have hBE : CFSG.Open.IsElemAbelian 2 B :=
    isElemAbelian_of_le_center_map hBS hBZ hBsq
  have hEel : CFSG.Open.IsElemAbelian 2 E := by
    rw [hE]
    exact CFSG.Open.IsElemAbelian.sup_of_commute hZpE hBE hcomm
  simpa [hE, hB] using hEel

private theorem false_of_mem_normalizer_conj_szZ_of_not_mem
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hK : Nat.card F = 2 ^ (2 * a + 1)) {y : CFSG.Blueprint.suzukiGroup a F}
    {z : CFSG.Blueprint.suzukiGroup a F}
    (hzB : z ∉ conjSubgroup y (szZ a F))
    (hzN : z ∈ Subgroup.normalizer
      (conjSubgroup y (szZ a F) : Set (CFSG.Blueprint.suzukiGroup a F)))
    (hz2 : z * z = 1) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup (CFSG.Blueprint.suzukiGroup a F) := conjSubgroup y (szZ a F) with hB
  have hzB' : z ∉ B := by rwa [hB]
  have hz1 : z ≠ 1 := fun h => hzB' (h ▸ B.one_mem)
  have hzp : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using hz2) hz1
  set E : Subgroup (CFSG.Blueprint.suzukiGroup a F) := Subgroup.zpowers z ⊔ B with hE
  have hEelem : CFSG.Open.IsElemAbelian 2 E := by
    rw [hE]
    simpa [hB] using isElemAbelian_zpowers_sup_conj_szZ hK hzB hzN hz2
  have hEcard : Nat.card E ≤ 2 ^ (2 * a + 1) :=
    CFSG.Quasithin.Ch3E215M.card_le_of_isElemAbelian_suzuki hK (MulEquiv.refl _) hEelem
  have hdisj : Subgroup.zpowers z ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    have hwz : w ∈ Subgroup.zpowers z := (Subgroup.mem_inf.mp hw).1
    have hwB : w ∈ B := (Subgroup.mem_inf.mp hw).2
    have hdvd : orderOf w ∣ orderOf z := orderOf_dvd_of_mem_zpowers hwz
    rw [hzp] at hdvd
    have hordw : orderOf w = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hw1
      · exact h
    have hle : Subgroup.zpowers w ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hwz
    have heq : Subgroup.zpowers w = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hordw, hzp])
    have hzmem : z ∈ Subgroup.zpowers w := by
      rw [heq]; exact Subgroup.mem_zpowers z
    exact hzB' (Subgroup.zpowers_le.mpr hwB hzmem)
  have hBcard : Nat.card B = 2 ^ (2 * a + 1) := by
    rw [hB, card_conjSubgroup, Sec2.card_szZ (a := a) (K := F) hK]
  have hlow : 2 * Nat.card B ≤ Nat.card E := by
    have h := CFSG.Timmesfeld.ARS.card_mul_card_le_card_sup
      (H := Subgroup.zpowers z) (K := B) hdisj
    rw [Nat.card_zpowers, hzp, ← hE] at h
    exact h
  have hcontr : 2 ^ (2 * a + 2) ≤ 2 ^ (2 * a + 1) := by
    calc 2 ^ (2 * a + 2) = 2 * 2 ^ (2 * a + 1) := by ring
      _ = 2 * Nat.card B := by rw [hBcard]
      _ ≤ Nat.card E := hlow
      _ ≤ 2 ^ (2 * a + 1) := hEcard
  exact absurd hcontr (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega)))

private theorem inf_normalizer_conj_szZ_eq_bot
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    {x y : CFSG.Blueprint.suzukiGroup a F}
    (hne : conjSubgroup x (szZ a F) ≠ conjSubgroup y (szZ a F)) :
    conjSubgroup x (szZ a F) ⊓
      Subgroup.normalizer (conjSubgroup y (szZ a F) : Set _) = ⊥ := by
  classical
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  set A : Subgroup (CFSG.Blueprint.suzukiGroup a F) := conjSubgroup x (szZ a F) with hA
  set B : Subgroup (CFSG.Blueprint.suzukiGroup a F) := conjSubgroup y (szZ a F) with hB
  have hAsq : ∀ w ∈ A, w * w = 1 := by
    intro w hw
    rw [hA] at hw
    exact sq_eq_one_of_mem_conj_szZ hK hw
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzA, hzN⟩ := Subgroup.mem_inf.mp hz
  have hzB : z ∈ B := by
    by_contra hzB
    have hzB' : z ∉ conjSubgroup y (szZ a F) := by rwa [hB] at hzB
    have hzN' : z ∈ Subgroup.normalizer
        (conjSubgroup y (szZ a F) : Set (CFSG.Blueprint.suzukiGroup a F)) := by
      rwa [hB] at hzN
    exact false_of_mem_normalizer_conj_szZ_of_not_mem hK hzB' hzN' (hAsq z hzA)
  have hzbot : z ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨hzA, hzB⟩
  rw [show A ⊓ B = ⊥ from inf_conj_szZ_eq_bot_of_ne hF (by rwa [hA, hB] at hne)] at hzbot
  exact hzbot

private theorem inf_normalizer_map_eq_bot_of_bijective {X : Type} [Group X]
    (ψ : HBar V H ≃* X) {L L' : Subgroup (HBar V H)} {T T' : Subgroup X}
    (hT : Subgroup.map ψ.toMonoidHom L = T) (hT' : Subgroup.map ψ.toMonoidHom L' = T')
    (h : T ⊓ Subgroup.normalizer (T' : Set X) = ⊥) :
    L ⊓ Subgroup.normalizer (L' : Set (HBar V H)) = ⊥ := by
  rw [eq_bot_iff] at h ⊢
  intro z hz
  have hzL : z ∈ L := (Subgroup.mem_inf.mp hz).1
  have hzN : z ∈ Subgroup.normalizer (L' : Set (HBar V H)) := (Subgroup.mem_inf.mp hz).2
  have hzT : ψ z ∈ T := by
    rw [← hT]
    exact Subgroup.mem_map_of_mem ψ.toMonoidHom hzL
  have hNmap : Subgroup.map ψ.toMonoidHom (Subgroup.normalizer (L' : Set (HBar V H))) =
      Subgroup.normalizer (T' : Set X) := by
    rw [← hT']
    exact Subgroup.map_normalizer_eq_of_bijective L' ψ.bijective
  have hzN' : ψ z ∈ Subgroup.normalizer (T' : Set X) := by
    rw [← hNmap]
    exact Subgroup.mem_map_of_mem ψ.toMonoidHom hzN
  have hzbot : ψ z ∈ (⊥ : Subgroup X) := h (Subgroup.mem_inf.mpr ⟨hzT, hzN'⟩)
  have hz1 : ψ z = 1 := Subgroup.mem_bot.mp hzbot
  exact Subgroup.mem_bot.mpr (ψ.injective (by simpa using hz1))

theorem RootHyp.inf_imgK_normalizer_eq_bot_of_sz
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (ψ : HBar V H ≃* CFSG.Blueprint.suzukiGroup a F) :
    imgK V H (Pc M V) ⊓ Subgroup.normalizer
      (imgK V H (conjSubgroup h₀ (Pc M V)) : Set (HBar V H)) = ⊥ := by
  classical
  obtain ⟨-, x, y, hTx, hTy, hne⟩ :=
    RootHyp.imgK_map_sz h hPH hVH hH hnM (a := a) (F := F) hF ψ
  have hT : Subgroup.map ψ.toMonoidHom (imgK V H (Pc M V)) =
      conjSubgroup x (szZ a F) := hTx
  have hT' : Subgroup.map ψ.toMonoidHom (imgK V H (conjSubgroup h₀ (Pc M V))) =
      conjSubgroup y (szZ a F) := hTy
  exact inf_normalizer_map_eq_bot_of_bijective (X := CFSG.Blueprint.suzukiGroup a F) ψ
    (L := imgK V H (Pc M V)) (L' := imgK V H (conjSubgroup h₀ (Pc M V)))
    (T := conjSubgroup x (szZ a F)) (T' := conjSubgroup y (szZ a F)) hT hT'
    (inf_normalizer_conj_szZ_eq_bot hF hne)

theorem RootHyp.inf_imgK_normalizer_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) :
    imgK V H (Pc M V) ⊓ Subgroup.normalizer
      (imgK V H (conjSubgroup h₀ (Pc M V)) : Set (HBar V H)) = ⊥ := by
  rcases hL with ⟨F, hField, hFintype, hCharP, -, ⟨ψ⟩⟩ |
    ⟨a, F, hField, hFintype, hCharP, ha, hcard, ⟨ψ⟩⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    exact RootHyp.inf_imgK_normalizer_eq_bot_of_sl2 h hPH hH hnM ψ
  · letI := hField
    letI := hFintype
    letI := hCharP
    exact RootHyp.inf_imgK_normalizer_eq_bot_of_sz h hPH hVH hH hnM hcard ψ

theorem RootHyp.mem_kOf_of_mem_normalizer_conjSubgroup_V
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {x : G} (hxP : x ∈ Pc M V)
    (hxN : x ∈ Subgroup.normalizer (conjSubgroup h₀ V : Set G)) :
    x ∈ kOf V H := by
  classical
  have hxH : x ∈ H := hPH hxP
  have hxMh : x ∈ conjSubgroup h₀ M := by
    have h1 : x ∈ Subgroup.normalizer (conjSubgroup h₀ V : Set G) := hxN
    rwa [normalizer_conjSubgroup, h.toHyp.normalizer_eq] at h1
  have hxNP : x ∈ Subgroup.normalizer (conjSubgroup h₀ (Pc M V) : Set G) := by
    have hle : conjSubgroup h₀ M ≤ conjSubgroup h₀ (Subgroup.normalizer (Pc M V : Set G)) :=
      Subgroup.map_mono (f := (MulAut.conj h₀).toMonoidHom) h.toHyp.le_normalizer_Pc
    rw [normalizer_conjSubgroup]
    exact hle hxMh
  have hP'hH : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
  have hNimg : piK V H ⟨x, hxH⟩ ∈ Subgroup.normalizer
      (imgK V H (conjSubgroup h₀ (Pc M V)) : Set (HBar V H)) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hconj : conjSubgroup x (conjSubgroup h₀ (Pc M V)) = conjSubgroup h₀ (Pc M V) :=
      conjSubgroup_eq_self_iff.mpr hxNP
    calc conjSubgroup (piK V H ⟨x, hxH⟩) (imgK V H (conjSubgroup h₀ (Pc M V)))
        = imgK V H (conjSubgroup x (conjSubgroup h₀ (Pc M V))) :=
          (imgK_conjSubgroup (V := V) (H := H) hxH hP'hH).symm
      _ = imgK V H (conjSubgroup h₀ (Pc M V)) := by rw [hconj]
  have hPimg : piK V H ⟨x, hxH⟩ ∈ imgK V H (Pc M V) :=
    Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hbot : piK V H ⟨x, hxH⟩ ∈ (⊥ : Subgroup (HBar V H)) := by
    have hEq := inf_imgK_normalizer_eq_bot h hPH hVH hH hnM hL
    simpa [hEq] using Subgroup.mem_inf.mpr ⟨hPimg, hNimg⟩
  exact (piK_eq_one_iff (V := V) (H := H) ⟨x, hxH⟩).mp (Subgroup.mem_bot.mp hbot)

theorem RootHyp.inf_commutator_kOf_ne_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) :
    V ⊓ ⁅kOf V H, kOf V H⁆ ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK'_ne : ⁅kOf V H, kOf V H⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    have hmem : ⁅x, y⁆ ∈ ⁅kOf V H, kOf V H⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hbot] at hmem
    have h1 : ⁅x, y⁆ = 1 := Subgroup.mem_bot.mp hmem
    exact hxy (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hK2 : IsPGroup 2 (kOf V H) := isPGroup_kOf_of_factorization h hK
  have hK'leK : ⁅kOf V H, kOf V H⁆ ≤ kOf V H := by
    simpa using Subgroup.commutator_le_sup (kOf V H) (kOf V H)
  have hK'2 : IsPGroup 2 (⁅kOf V H, kOf V H⁆ : Subgroup G) := hK2.to_le hK'leK
  have hP_norm_K' : Pc M V ≤
      Subgroup.normalizer ((⁅kOf V H, kOf V H⁆ : Subgroup G) : Set G) := by
    intro p hp
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hpK : conjSubgroup p (kOf V H) = kOf V H :=
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (hPH hp))
    calc conjSubgroup p ⁅kOf V H, kOf V H⁆
        = ⁅conjSubgroup p (kOf V H), conjSubgroup p (kOf V H)⁆ := by
          rw [conjSubgroup, Subgroup.map_commutator]
          rfl
      _ = ⁅kOf V H, kOf V H⁆ := by rw [hpK]
  have hK'_norm_P : (⁅kOf V H, kOf V H⁆ : Subgroup G) ≤
      Subgroup.normalizer (Pc M V : Set G) :=
    (hK'leK.trans (kOf_le_M h)).trans h.toHyp.le_normalizer_Pc
  set K' : Subgroup G := ⁅kOf V H, kOf V H⁆ with hK'def
  set R : Subgroup G := Pc M V ⊔ K' with hR
  have hR2 : IsPGroup 2 R := by
    have h := IsPGroup.to_sup_of_normal_right' hP2 hK'2 hP_norm_K'
    rwa [hR]
  have hK'leR : K' ≤ R := by rw [hR]; exact le_sup_right
  have hR_norm_K' : R ≤ Subgroup.normalizer (K' : Set G) := by
    rw [hR]
    exact sup_le hP_norm_K' (Subgroup.le_normalizer)
  haveI : (K'.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK'leR).mpr hR_norm_K'
  have hK'sub_ne : K'.subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hK'_ne
    rw [eq_bot_iff]
    intro k hk
    have hkR : k ∈ R := hK'leR hk
    have hmem : (⟨k, hkR⟩ : ↥R) ∈ K'.subgroupOf R := Subgroup.mem_subgroupOf.mpr hk
    rw [hbot] at hmem
    have h1 : (⟨k, hkR⟩ : ↥R) = 1 := Subgroup.mem_bot.mp hmem
    simpa using congrArg Subtype.val h1
  haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
  have hcenter := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥R) hK'sub_ne
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
  have hzK' : ((z : ↥R) : G) ∈ K' := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
  have hzZ : (z : ↥R) ∈ Subgroup.center ↥R := (Subgroup.mem_inf.mp z.2).2
  have hzC : ((z : ↥R) : G) ∈ Subgroup.centralizer (Pc M V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpR : p ∈ R := by rw [hR]; exact Subgroup.mem_sup_left hp
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨p, hpR⟩)
  have hzV : ((z : ↥R) : G) ∈ V := by
    rw [← h.toHyp.centralizer_Pc]
    exact hzC
  intro hbot
  have hmem : ((z : ↥R) : G) ∈ V ⊓ K' := Subgroup.mem_inf.mpr ⟨hzV, hzK'⟩
  rw [hbot] at hmem
  exact hz1 (Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem))

private theorem conj_sq_eq_mul_commutator {K : Subgroup G} {x y : G}
    (hxNK : conjSubgroup x K = K) (hyK : y ∈ K)
    (hKc : ⁅K, K⁆ ≤ Subgroup.centralizer (K : Set G))
    (he : ⁅x, y⁆ * ⁅x, y⁆ = 1) :
    ⁅y⁻¹, x * y * x⁻¹⁆⁻¹ ∈ ⁅K, K⁆ ∧
      x * (y * y) * x⁻¹ = (y * y) * ⁅y⁻¹, x * y * x⁻¹⁆⁻¹ ∧
      ⁅y⁻¹, x * y * x⁻¹⁆⁻¹ * (y * y) = (y * y) * ⁅y⁻¹, x * y * x⁻¹⁆⁻¹ := by
  classical
  have hyxK : x * y * x⁻¹ ∈ K := by
    have h := conj_mem_conjSubgroup x hyK
    rwa [hxNK] at h
  set a : G := x * y * x⁻¹ with ha
  set b : G := y⁻¹ with hb
  set c₀ : G := ⁅b, a⁆ with hc₀
  have hc₀K : c₀ ∈ ⁅K, K⁆ := by
    rw [hc₀]
    exact Subgroup.commutator_mem_commutator (K.inv_mem hyK) hyxK
  have hc₀C : c₀ ∈ Subgroup.centralizer (K : Set G) := hKc hc₀K
  have hc₀a : a * c₀ = c₀ * a := Subgroup.mem_centralizer_iff.mp hc₀C a hyxK
  have hc₀y : (y * y) * c₀ = c₀ * (y * y) :=
    Subgroup.mem_centralizer_iff.mp hc₀C (y * y) (K.mul_mem hyK hyK)
  have hba : b * a = c₀ * (a * b) := by
    rw [hc₀, commutatorElement_def]
    group
  have he' : (a * b) * (a * b) = 1 := by
    rw [ha, hb]
    simpa [commutatorElement_def] using he
  have hsq : c₀ * (a * a) * (b * b) = 1 := by
    rw [show c₀ * (a * a) * (b * b) = ⁅b, a⁆ * a ^ 2 * b ^ 2 by
      rw [hc₀, pow_two, pow_two]]
    rw [← CFSG.GroupTheory.SuzukiTwoGroup.mul_sq_of_commute (x := a) (y := b) hc₀a]
    simpa [pow_two] using he'
  have ha2 : a * a = x * (y * y) * x⁻¹ := by rw [ha]; group
  have hb2 : b * b = (y * y)⁻¹ := by rw [hb]; group
  have hsq2 : c₀ * (x * (y * y) * x⁻¹) * (y * y)⁻¹ = 1 := by
    rw [← ha2, ← hb2]
    exact hsq
  have hc₀invC : c₀⁻¹ ∈ Subgroup.centralizer (K : Set G) := Subgroup.inv_mem _ hc₀C
  refine ⟨Subgroup.inv_mem _ hc₀K, ?_, ?_⟩
  · have h := congrArg (fun t => c₀⁻¹ * t * (y * y)) hsq2
    have h' : x * (y * y) * x⁻¹ = c₀⁻¹ * (y * y) := by
      simpa [mul_assoc] using h
    rw [h']
    exact (Subgroup.mem_centralizer_iff.mp hc₀invC (y * y) (K.mul_mem hyK hyK)).symm
  · exact (Subgroup.mem_centralizer_iff.mp hc₀invC (y * y) (K.mul_mem hyK hyK)).symm

private theorem le_Pc_of_isElemAbelian (h : RootHyp M V) {Z : Subgroup G}
    (hZ : Assembly.IsElemAbelian 2 Z)
    (hZC : Z ≤ Subgroup.centralizer (V : Set G))
    (hZN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Z : Set G)) :
    Z ≤ Pc M V := by
  classical
  have hZopen : CFSG.Open.IsElemAbelian 2 Z := hZ
  have hZcore : Z ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (V : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZC hZN hZopen.isPGroup
  have hcoreM : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (V : Set G)) ≤
      CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans h.centralizer_le_M)
      (h.le_normalizer_centralizer_V.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact le_inf (hZcore.trans hcoreM) hZC

theorem RootHyp.sq_mem_conjSubgroup_V_of_mem_conjSubgroup_Pc (h : RootHyp M V)
    {y₀ y : G} (hy : y ∈ conjSubgroup y₀ (Pc M V)) :
    y * y ∈ conjSubgroup y₀ V := by
  have hQ2 : IsPGroup 2 (conjSubgroup y₀ (Pc M V)) :=
    ((inSubgroup_pCore_two M).1.to_le inf_le_left).map _
  have hPhi : inSubgroup frattini (conjSubgroup y₀ (Pc M V)) ≤ conjSubgroup y₀ V := by
    refine CFSG.RankThree.GF2n.Tim78.inSubgroup_frattini_le_of_sq hQ2 ?_ ?_
    · intro u hu
      rw [mem_conjSubgroup] at hu ⊢
      have hp2 : (y₀⁻¹ * u * y₀) ^ 2 ∈ V :=
        h.toHyp.frattini_Pc_le
          (CFSG.RankThree.GF2n.Tim78.sq_mem_inSubgroup_frattini
            ((inSubgroup_pCore_two M).1.to_le inf_le_left) hu)
      have he : y₀⁻¹ * u ^ 2 * y₀ = (y₀⁻¹ * u * y₀) ^ 2 := by
        rw [pow_two, pow_two]
        group
      rw [he]
      exact hp2
    · intro u hu v hv
      rw [mem_conjSubgroup] at hu hv ⊢
      have hcom : ⁅y₀⁻¹ * u * y₀, y₀⁻¹ * v * y₀⁆ ∈ V :=
        h.toHyp.frattini_Pc_le
          (CFSG.RankThree.GF2n.Tim78.commutatorElement_mem_inSubgroup_frattini
            ((inSubgroup_pCore_two M).1.to_le inf_le_left) hu hv)
      have he : y₀⁻¹ * ⁅u, v⁆ * y₀ = ⁅y₀⁻¹ * u * y₀, y₀⁻¹ * v * y₀⁆ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rwa [he]
  have h := CFSG.RankThree.GF2n.Tim78.sq_mem_inSubgroup_frattini hQ2 hy
  rw [pow_two] at h
  exact hPhi h

private theorem conj_sq_eq_mul_and_mem_conjSubgroup_Pc
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {Z : Subgroup G} (hZ : Assembly.IsElemAbelian 2 Z)
    (hZN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Z : Set G))
    {x : G} (hxZ : x ∈ Z) (hxP : x ∈ Pc M V)
    {y₀ : G} (hy₀H : y₀ ∈ H) {y : G}
    (hyQ : y ∈ conjSubgroup y₀ (Pc M V)) (hyK : y ∈ kOf V H) :
    x * (y * y) * x⁻¹ = (y * y) * ⁅y⁻¹, x * y * x⁻¹⁆⁻¹ ∧
      ⁅y⁻¹, x * y * x⁻¹⁆⁻¹ ∈ conjSubgroup y₀ (Pc M V) := by
  classical
  have hyC : y ∈ Subgroup.centralizer (V : Set G) := kOf_le_centralizer_V V H hyK
  have heZ : ⁅x, y⁆ ∈ Z := by
    have hyxZ : y * x * y⁻¹ ∈ Z := by
      have hcN : y ∈ Subgroup.normalizer (Z : Set G) := hZN hyC
      exact (Subgroup.mem_normalizer_iff.mp hcN x).mp hxZ
    have h1 : ⁅x, y⁆ = x * (y * x * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [h1]
    exact Z.mul_mem hxZ (Z.inv_mem hyxZ)
  have he2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    have h := hZ.2 ⁅x, y⁆ heZ
    rwa [pow_two] at h
  have hxNK : conjSubgroup x (kOf V H) = kOf V H :=
    conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (hPH hxP))
  have hKc : ⁅kOf V H, kOf V H⁆ ≤
      Subgroup.centralizer (kOf V H : Set G) :=
    RootHyp.commutator_kOf_le_center h hPH hH hnM hK
  obtain ⟨-, hceq, -⟩ := conj_sq_eq_mul_commutator hxNK hyK hKc he2
  set Q : Subgroup G := conjSubgroup y₀ (Pc M V) with hQ
  set a : G := x * y * x⁻¹ with ha
  have haK : a ∈ kOf V H := by
    rw [ha, ← hxNK]
    exact conj_mem_conjSubgroup x hyK
  have hKNQ : kOf V H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    exact RootHyp.kOf_le_normalizer_conjSubgroup_Pc_of_mem h hy₀H
  have hbQ : y⁻¹ ∈ Q := Q.inv_mem hyQ
  have hc₀Q : ⁅y⁻¹, a⁆ ∈ Q := by
    have haNQ : a ∈ Subgroup.normalizer (Q : Set G) := hKNQ haK
    have hayQ : a * y * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp haNQ y).mp hyQ
    have he : ⁅y⁻¹, a⁆ = y⁻¹ * (a * y * a⁻¹) := by rw [commutatorElement_def]; group
    rw [he]
    exact Q.mul_mem hbQ hayQ
  have hcQ : ⁅y⁻¹, a⁆⁻¹ ∈ Q := Q.inv_mem hc₀Q
  refine ⟨hceq, ?_⟩
  simpa [ha, hQ] using hcQ

private theorem conjSubgroup_conjSubgroup_V_eq_of_mem_conjSubgroup_Pc (h : RootHyp M V)
    {x y₀ w : G} (hwV : w ∈ conjSubgroup x (conjSubgroup y₀ V))
    (hwQ : w ∈ conjSubgroup y₀ (Pc M V)) (hw1 : w ≠ 1) :
    conjSubgroup x (conjSubgroup y₀ V) = conjSubgroup y₀ V := by
  have hne0 : conjSubgroup (y₀⁻¹ * x * y₀) V ⊓ Pc M V ≠ ⊥ := by
    intro hbot
    have hmemV : y₀⁻¹ * w * y₀ ∈ conjSubgroup (y₀⁻¹ * x * y₀) V := by
      have h := conj_mem_conjSubgroup (y₀⁻¹) hwV
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at h
      simpa using h
    have hmemP : y₀⁻¹ * w * y₀ ∈ Pc M V := by
      have h := conj_mem_conjSubgroup (y₀⁻¹) hwQ
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
      simpa using h
    have hmem : y₀⁻¹ * w * y₀ ∈ conjSubgroup (y₀⁻¹ * x * y₀) V ⊓ Pc M V :=
      Subgroup.mem_inf.mpr ⟨hmemV, hmemP⟩
    rw [hbot] at hmem
    have h1 : y₀⁻¹ * w * y₀ = 1 := Subgroup.mem_bot.mp hmem
    apply hw1
    have h2 := congrArg (fun t => y₀ * t * y₀⁻¹) h1
    simpa [mul_assoc] using h2
  have hconj : conjSubgroup (y₀⁻¹ * x * y₀)
      (V ⊓ conjSubgroup (y₀⁻¹ * x * y₀)⁻¹ (Pc M V)) =
      conjSubgroup (y₀⁻¹ * x * y₀) V ⊓ Pc M V := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_inf, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one]
  have hne' : V ⊓ conjSubgroup (y₀⁻¹ * x * y₀)⁻¹ (Pc M V) ≠ ⊥ := by
    intro hbot
    apply hne0
    rw [← hconj, hbot, conjSubgroup_eq_bot_iff.mpr rfl]
  have hG1inv : conjSubgroup (y₀⁻¹ * x * y₀)⁻¹ V = V :=
    RootHyp.conj_eq_of_inf_conj_Pc_ne_bot h hne'
  have hG1 : conjSubgroup (y₀⁻¹ * x * y₀) V = V := by
    have h := congrArg (conjSubgroup (y₀⁻¹ * x * y₀)) hG1inv
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
    exact h.symm
  have h2 : conjSubgroup (y₀ * (y₀⁻¹ * x * y₀)) V = conjSubgroup y₀ V := by
    have h := congrArg (conjSubgroup y₀) hG1
    rwa [conjSubgroup_conjSubgroup] at h
  rw [show y₀ * (y₀⁻¹ * x * y₀) = x * y₀ from by group] at h2
  rwa [← conjSubgroup_conjSubgroup x y₀ V] at h2

theorem RootHyp.le_Pc_inf_kOf_of_isElemAbelian
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {Z : Subgroup G} (hZ : Assembly.IsElemAbelian 2 Z)
    (hZC : Z ≤ Subgroup.centralizer (V : Set G))
    (hZN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Z : Set G)) :
    Z ≤ Pc M V ⊓ kOf V H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZP : Z ≤ Pc M V := le_Pc_of_isElemAbelian h hZ hZC hZN
  refine le_inf hZP ?_
  intro x hxZ
  have hxP : x ∈ Pc M V := hZP hxZ
  by_contra hxK
  obtain ⟨y, hyQK, hy2ne⟩ := RootHyp.exists_sq_ne_one_conj_inf h hPH hH hnM hK hnab
  obtain ⟨y₀, hy₀H, hPy₀, -, hHy₀⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hyQ : y ∈ conjSubgroup y₀ (Pc M V) := by rw [← hPy₀]; exact hyQK.1
  have hyK : y ∈ kOf V H := hyQK.2
  obtain ⟨hceq, hcQ⟩ :=
    conj_sq_eq_mul_and_mem_conjSubgroup_Pc h hPH hH hnM hK hZ hZN hxZ hxP
      hy₀H hyQ hyK
  have hy2V : y * y ∈ conjSubgroup y₀ V :=
    h.sq_mem_conjSubgroup_V_of_mem_conjSubgroup_Pc hyQ
  have hy2Q : y * y ∈ conjSubgroup y₀ (Pc M V) :=
    (Subgroup.map_mono (f := (MulAut.conj y₀).toMonoidHom) h.toHyp.le_Pc) hy2V
  have hwV : x * (y * y) * x⁻¹ ∈ conjSubgroup x (conjSubgroup y₀ V) := by
    rw [mem_conjSubgroup]
    have he : x⁻¹ * (x * (y * y) * x⁻¹) * x = y * y := by group
    rw [he]
    exact hy2V
  have hwQ : x * (y * y) * x⁻¹ ∈ conjSubgroup y₀ (Pc M V) := by
    rw [hceq]
    exact (conjSubgroup y₀ (Pc M V)).mul_mem hy2Q hcQ
  have hw1 : x * (y * y) * x⁻¹ ≠ 1 := by
    intro h1
    apply hy2ne
    have h2 := congrArg (fun t => x⁻¹ * t * x) h1
    simpa [mul_assoc] using h2
  have hVeq : conjSubgroup x (conjSubgroup y₀ V) = conjSubgroup y₀ V :=
    conjSubgroup_conjSubgroup_V_eq_of_mem_conjSubgroup_Pc h hwV hwQ hw1
  have hxN : x ∈ Subgroup.normalizer (conjSubgroup y₀ V : Set G) :=
    conjSubgroup_eq_self_iff.mp hVeq
  exact hxK (RootHyp.mem_kOf_of_mem_normalizer_conjSubgroup_V h hPH hVH hHy₀ hnM hL hxP hxN)

private theorem isElemAbelian_sup_V_data (h : RootHyp M V) {Z : Subgroup G}
    (hZ : Assembly.IsElemAbelian 2 Z)
    (hZC : Z ≤ Subgroup.centralizer (V : Set G))
    (hZN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Z : Set G)) :
    CFSG.Open.IsElemAbelian 2 (Z ⊔ V) ∧
      Z ⊔ V ≤ Subgroup.centralizer (V : Set G) ∧
      Subgroup.centralizer (V : Set G) ≤
        Subgroup.normalizer ((Z ⊔ V : Subgroup G) : Set G) := by
  have hVopen : CFSG.Open.IsElemAbelian 2 V := h.toHyp.elem
  have hV_CV : V ≤ Subgroup.centralizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hVopen.comm hv hw).symm
  have hZV : ∀ a ∈ Z, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hZC ha) b hb).symm
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hZ hVopen hZV, sup_le hZC hV_CV, ?_⟩
  exact CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hZN
    (Subgroup.centralizer_le_normalizer (V : Set G))

private theorem iSup_conjSubgroup_le_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H) {Z' : Subgroup G}
    (hZ'el : CFSG.Open.IsElemAbelian 2 Z')
    (hZ'C : Z' ≤ Subgroup.centralizer (V : Set G))
    (hZ'N : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Z' : Set G)) :
    (⨆ m : ↥M, conjSubgroup (m : G) Z') ≤ kOf V H := by
  refine iSup_le fun m => ?_
  have hZm_el : CFSG.Open.IsElemAbelian 2 (conjSubgroup (m : G) Z') :=
    CFSG.CGT.Timmesfeld75.isElemAbelian_conjSubgroup hZ'el (m : G)
  have hZm_C : conjSubgroup (m : G) Z' ≤ Subgroup.centralizer (V : Set G) := by
    calc conjSubgroup (m : G) Z'
        ≤ conjSubgroup (m : G) (Subgroup.centralizer (V : Set G)) := Subgroup.map_mono hZ'C
      _ = Subgroup.centralizer (V : Set G) :=
          conjSubgroup_eq_self_iff.mpr (h.le_normalizer_centralizer_V m.2)
  have hZm_N : Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer (conjSubgroup (m : G) Z' : Set G) := by
    have h1 : conjSubgroup (m : G) (Subgroup.centralizer (V : Set G)) ≤
        conjSubgroup (m : G) (Subgroup.normalizer (Z' : Set G)) := Subgroup.map_mono hZ'N
    rw [← normalizer_conjSubgroup] at h1
    rwa [conjSubgroup_eq_self_iff.mpr (h.le_normalizer_centralizer_V m.2)] at h1
  exact (RootHyp.le_Pc_inf_kOf_of_isElemAbelian h hPH hVH hH hnM hK hnab hL
    hZm_el hZm_C hZm_N).trans inf_le_right

private theorem V_le_center_map_of_le_kOf {F : Subgroup G}
    (hV_le_F : V ≤ F) (hF_le_K : F ≤ kOf V H) :
    V ≤ (Subgroup.center F).map F.subtype := by
  intro v hv
  have hvF : v ∈ F := hV_le_F hv
  refine Subgroup.mem_map.mpr ⟨⟨v, hvF⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  have hyK : ((y : ↥F) : G) ∈ kOf V H := hF_le_K y.2
  have hvW : v ∈ Tim79a.xOf V H := (le_xOf_self V H) hv
  have hcomm := Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hyK).2 v hvW
  exact Subtype.ext hcomm.symm

private theorem inf_xOf_le_center_map {Z Z' F : Subgroup G}
    (hZZ' : Z ≤ Z') (hF : F = ⨆ m : ↥M, conjSubgroup (m : G) Z')
    (hF_le_K : F ≤ kOf V H) :
    Z ⊓ Tim79a.xOf V H ≤ (Subgroup.center F).map F.subtype := by
  intro z hz
  obtain ⟨hzZ, hzW⟩ := Subgroup.mem_inf.mp hz
  have hzF : z ∈ F := by
    have h1 : z ∈ Z' := hZZ' hzZ
    rw [hF]
    exact Subgroup.mem_iSup_of_mem (⟨1, M.one_mem⟩ : ↥M)
      (by simpa [conjSubgroup_one] using h1)
  refine Subgroup.mem_map.mpr ⟨⟨z, hzF⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  have hyK : ((y : ↥F) : G) ∈ kOf V H := hF_le_K y.2
  have hcomm := Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hyK).2 z hzW
  exact Subtype.ext hcomm.symm

private theorem center_map_eq_V_of_le_kOf (h : RootHyp M V) {F : Subgroup G}
    (hF_le_K : F ≤ kOf V H) (hF_normal : M ≤ Subgroup.normalizer (F : Set G))
    (hV_le_center : V ≤ (Subgroup.center F).map F.subtype) :
    (Subgroup.center F).map F.subtype = V := by
  refine le_antisymm ?_ hV_le_center
  have hcenter_le_M : (Subgroup.center F).map F.subtype ≤ M :=
    (Subgroup.map_subtype_le _).trans (hF_le_K.trans (RootHyp.kOf_le_M h))
  have hcenter_comm : IsMulCommutative ((Subgroup.center F).map F.subtype) := inferInstance
  have hcenter_normal : M ≤ Subgroup.normalizer
      ((Subgroup.center F).map F.subtype : Set G) := by
    haveI : (Subgroup.center F).Characteristic := Subgroup.centerCharacteristic
    exact hF_normal.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (Subgroup.center F))
  exact h.toHyp.maxAb.le_of_ge ⟨hcenter_le_M, hcenter_normal, hcenter_comm⟩ hV_le_center

theorem RootHyp.inf_xOf_le_V_of_isElemAbelian
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {Z : Subgroup G} (hZ : Assembly.IsElemAbelian 2 Z)
    (hZC : Z ≤ Subgroup.centralizer (V : Set G))
    (hZN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Z : Set G)) :
    Z ⊓ Tim79a.xOf V H ≤ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ'el, hZ'C, hZ'N⟩ := isElemAbelian_sup_V_data h hZ hZC hZN
  set F : Subgroup G := ⨆ m : ↥M, conjSubgroup (m : G) (Z ⊔ V) with hF
  have hF_le_K : F ≤ kOf V H :=
    iSup_conjSubgroup_le_kOf h hPH hVH hH hnM hK hnab hL hZ'el hZ'C hZ'N
  have hV_le_F : V ≤ F := by
    rw [hF]
    refine le_iSup_of_le (⟨1, M.one_mem⟩ : ↥M) ?_
    show V ≤ conjSubgroup (1 : G) (Z ⊔ V)
    rw [conjSubgroup_one]
    exact le_sup_right
  have hF_normal : M ≤ Subgroup.normalizer (F : Set G) := by
    rw [hF]
    simpa only [conjSubgroup, iSup_subtype] using
      CFSG.Quasithin.MS93.le_normalizer_iSup_conj M (Z ⊔ V)
  have hV_le_center := V_le_center_map_of_le_kOf hV_le_F hF_le_K
  have hcenter_eq_V := center_map_eq_V_of_le_kOf h hF_le_K hF_normal hV_le_center
  intro z hz
  have hmem : z ∈ (Subgroup.center F).map F.subtype :=
    inf_xOf_le_center_map le_sup_left hF hF_le_K hz
  rwa [hcenter_eq_V] at hmem

private theorem closure_conjSubgroup_le_of_forall {D L K : Subgroup G}
    (h : ∀ c ∈ D, conjSubgroup c L ≤ K) :
    Subgroup.closure {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L} ≤ K := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨c, hc, hx⟩
  exact h c hc hx

private theorem closure_conjSubgroup_le_of_le_normalizer {D L C : Subgroup G}
    (hL : L ≤ C) (hD : D ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.closure {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L} ≤ C := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨c, hc, hx⟩
  have hle : conjSubgroup c L ≤ C := by
    calc conjSubgroup c L ≤ conjSubgroup c C := Subgroup.map_mono hL
      _ = C := conjSubgroup_eq_self_iff.mpr (hD hc)
  exact hle hx

private theorem le_normalizer_closure_conjSubgroup {D L : Subgroup G} :
    D ≤ Subgroup.normalizer
      ((Subgroup.closure {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L} : Subgroup G) : Set G) := by
  intro d hd
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hset : (⇑(MulAut.conj d).toMonoidHom) ''
      {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L} =
      {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L} := by
    ext x
    constructor
    · rintro ⟨y, ⟨c, hc, hy⟩, rfl⟩
      refine ⟨d * c, D.mul_mem hd hc, ?_⟩
      have h := conj_mem_conjSubgroup d hy
      rwa [conjSubgroup_conjSubgroup] at h
    · rintro ⟨c, hc, hx⟩
      refine ⟨(MulAut.conj d)⁻¹ x, ⟨d⁻¹ * c, D.mul_mem (D.inv_mem hd) hc, ?_⟩, ?_⟩
      · have h := conj_mem_conjSubgroup (d⁻¹) hx
        rw [conjSubgroup_conjSubgroup] at h
        simpa using h
      · exact (MulAut.conj d).apply_symm_apply x
  calc conjSubgroup d (Subgroup.closure {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L})
      = Subgroup.map (MulAut.conj d).toMonoidHom
          (Subgroup.closure {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L}) := rfl
    _ = Subgroup.closure {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L} := by
      have h := MonoidHom.map_closure (f := (MulAut.conj d).toMonoidHom)
        (s := {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L})
      rw [hset] at h
      exact h

private theorem isElemAbelian_closure_conjSubgroup {D L K W : Subgroup G}
    (hLW : L ≤ W) (hcon : ∀ c ∈ D, conjSubgroup c L ≤ K)
    (hKC : K ≤ Subgroup.centralizer (W : Set G))
    (hW : CFSG.Open.IsElemAbelian 2 W) :
    CFSG.Open.IsElemAbelian 2
      (Subgroup.closure {x : G | ∃ c ∈ D, x ∈ conjSubgroup c L}) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨c₁, hc₁, a₀, ha₀, rfl⟩ b ⟨c₂, hc₂, b₀, hb₀, rfl⟩
    have hd : c₁⁻¹ * c₂ ∈ D := D.mul_mem (D.inv_mem hc₁) hc₂
    have hb'K : c₁⁻¹ * (c₂ * b₀ * c₂⁻¹) * c₁ ∈ K := by
      apply hcon (c₁⁻¹ * c₂) hd
      rw [mem_conjSubgroup]
      have he : (c₁⁻¹ * c₂)⁻¹ * (c₁⁻¹ * (c₂ * b₀ * c₂⁻¹) * c₁) * (c₁⁻¹ * c₂) = b₀ := by
        group
      rw [he]
      exact hb₀
    have hcomm := Subgroup.mem_centralizer_iff.mp (hKC hb'K) a₀ (hLW ha₀)
    calc (c₁ * a₀ * c₁⁻¹) * (c₂ * b₀ * c₂⁻¹)
        = c₁ * (a₀ * (c₁⁻¹ * (c₂ * b₀ * c₂⁻¹) * c₁)) * c₁⁻¹ := by group
      _ = c₁ * ((c₁⁻¹ * (c₂ * b₀ * c₂⁻¹) * c₁) * a₀) * c₁⁻¹ := by rw [hcomm]
      _ = (c₂ * b₀ * c₂⁻¹) * (c₁ * a₀ * c₁⁻¹) := by group
  · rintro a ⟨c, hc, a₀, ha₀, rfl⟩
    rw [pow_two]
    have ha₀2 : a₀ * a₀ = 1 := by
      have h := hW.2 a₀ (hLW ha₀)
      rwa [pow_two] at h
    calc (c * a₀ * c⁻¹) * (c * a₀ * c⁻¹) = c * (a₀ * a₀) * c⁻¹ := by group
      _ = 1 := by rw [ha₀2]; group

theorem RootHyp.exists_conj_not_le_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {L : Subgroup G} (hLW : L ≤ Tim79a.xOf V H) (hLV : ¬ L ≤ V) :
    ∃ c ∈ Subgroup.centralizer (V : Set G), ¬ conjSubgroup c L ≤ kOf V H := by
  classical
  by_contra hcon
  push Not at hcon
  have hCVleM : Subgroup.centralizer (V : Set G) ≤ M := h.centralizer_le_M
  have hMleNCV : M ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    h.le_normalizer_centralizer_V
  have hK_le_CV : kOf V H ≤ Subgroup.centralizer (V : Set G) := kOf_le_centralizer_V V H
  have hL_CV : L ≤ Subgroup.centralizer (V : Set G) :=
    (hLW.trans (xOf_le_kOf h hPH hVH)).trans hK_le_CV
  set E : Subgroup G :=
    Subgroup.closure {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
      x ∈ conjSubgroup c L} with hE
  have hE_le_K : E ≤ kOf V H := by
    rw [hE]
    exact closure_conjSubgroup_le_of_forall hcon
  have hE_le_CV : E ≤ Subgroup.centralizer (V : Set G) := by
    rw [hE]
    exact closure_conjSubgroup_le_of_le_normalizer hL_CV (hCVleM.trans hMleNCV)
  have hE_N : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]
    exact le_normalizer_closure_conjSubgroup
  have hE_el : Assembly.IsElemAbelian 2 E := by
    rw [hE]
    exact isElemAbelian_closure_conjSubgroup hLW hcon (fun k hk => (mem_kOf_iff.mp hk).2)
      (isElemAbelian_xOf h hPH hVH)
  have hE_inf_W_le_V : E ⊓ Tim79a.xOf V H ≤ V :=
    RootHyp.inf_xOf_le_V_of_isElemAbelian h hPH hVH hH hnM hK hnab hL hE_el hE_le_CV hE_N
  have hL_le_E : L ≤ E := by
    rw [hE]
    intro l hl
    exact Subgroup.subset_closure ⟨1, (Subgroup.centralizer (V : Set G)).one_mem,
      by simpa [conjSubgroup_one] using hl⟩
  exact hLV (le_trans (le_inf hL_le_E hLW) hE_inf_W_le_V)

end CFSG.RankThree.GF2n.Tim81
