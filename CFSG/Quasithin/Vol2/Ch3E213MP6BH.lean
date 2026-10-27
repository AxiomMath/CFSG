module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CH
public import CFSG.Quasithin.Vol2.Ch3E213MLift
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Quasithin.H13.QRCBenderPairModel
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzuki
public import CFSG.Quasithin.Vol2.Ch3E213MP6BC
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt antiSp_ext
  antiUnipotent antiUnipotentCenter minorJ minorJ_apply mem_antiUnipotent_iff_upper
  suzukiGroup_le_minorFixGroup uMat)
open CFSG.Blueprint (suzukiGroup suzukiS suzukiD suzukiN)
open CFSG.LieType.Ree (suzukiU suzukiT suzukiB suzukiSElt suzukiDElt coe_suzukiSElt
  coe_suzukiDElt suzukiSElt_mem_suzukiU)
open CFSG.Quasithin.H13.QRC (BenderData benderData_suzuki bender_pair_props bender_pair_suzuki
  exists_mem_sup_conjugate suzuki_normalizer_suzukiU not_three_dvd_card_suzukiGroup)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Timmesfeld (exists_isPrimitivePrimeDivisor)

variable {k : Type} [Field k] [CharP k 2] [Finite k]

omit [CharP k 2] [Finite k] in
theorem minorJ_mul_mul_minorJ_apply (M : Matrix (Fin 4) (Fin 4) k) (i j : Fin 4) :
    (minorJ k * M * minorJ k) i j = M (Fin.rev i) (Fin.rev j) := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply, Fin.rev]

omit [CharP k 2] [Finite k] in
theorem isElementaryAbelian_of {G : Type*} [Group G] {E : Subgroup G}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) :
    IsElementaryAbelian 2 E := CFSG.IsElementaryAbelian.two_of_forall_mul_self hcomm hsq

omit [CharP k 2] [Finite k] in
theorem inSubgroup_pCore_map {G G' : Type} [Group G] [Group G'] {f : G' →* G}
    (hf : Function.Injective f) (X : Subgroup G') :
    CFSG.inSubgroup (CFSG.pCore 2) (X.map f) = (CFSG.inSubgroup (CFSG.pCore 2) X).map f := by
  set e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf with he
  rw [CFSG.inSubgroup, CFSG.inSubgroup, ← CFSG.pCore_map_iso 2 e, Subgroup.map_map,
    Subgroup.map_map]
  congr 1

omit [CharP k 2] [Finite k] in
theorem isSylowOf_map {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {f : G' →* G}
    (hf : Function.Injective f) {P X : Subgroup G'} (h : IsSylowOf 2 P X) :
    IsSylowOf 2 (P.map f) (X.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ hf]
  exact h.2.2

omit [CharP k 2] [Finite k] in
theorem map_inf_eq_map_inf_comap {G G' : Type} [Group G] [Group G'] (f : G' →* G)
    (A : Subgroup G') (B : Subgroup G) : A.map f ⊓ B = (A ⊓ B.comap f).map f := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hb⟩
    exact ⟨y, ⟨hy, hb⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hb⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hb⟩

omit [CharP k 2] [Finite k] in
theorem kerIn_map_of_injective {G G' : Type} [Group G] [Group G'] {f : G' →* G}
    (hf : Function.Injective f) (P X : Subgroup G') :
    kerIn (P.map f) (X.map f) = (kerIn P X).map f := by
  ext z
  constructor
  · intro hz
    obtain ⟨z₀, -, rfl⟩ : z ∈ P.map f := by simpa using hz 1 (Subgroup.one_mem _)
    refine ⟨z₀, fun y hy => ?_, rfl⟩
    obtain ⟨p, hp, hpe⟩ := hz (f y) ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at hpe
    rwa [← hf hpe]
  · rintro ⟨z₀, hz₀, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨_, hz₀ y hy, by rw [map_mul, map_mul, map_inv]⟩

section Embedding

variable (F₀ : Subfield k) (a : ℕ)

theorem suzukiGroup_le_antiSp (hcard : Nat.card F₀ = 2 ^ (2 * a + 1)) :
    suzukiGroup a ↥F₀ ≤ antiSp ↥F₀ := by
  intro g hg
  obtain ⟨g', -, rfl⟩ := suzukiGroup_le_minorFixGroup a hcard hg
  exact g'.2

@[expose] noncomputable def szEmb (hcard : Nat.card F₀ = 2 ^ (2 * a + 1)) (d : antiSp k) :
    ↥(suzukiGroup a ↥F₀) →* antiSp k :=
  (MulAut.conj (d * wLong)).toMonoidHom.comp
    ((subAntiSp F₀).comp (Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard)))

variable {F₀ a} (hcard : Nat.card F₀ = 2 ^ (2 * a + 1)) {d : antiSp k}

theorem szEmb_injective : Function.Injective (szEmb F₀ a hcard d) :=
  (MulAut.conj (d * wLong)).injective.comp
    ((subAntiSp_injective F₀).comp (Subgroup.inclusion_injective _))

theorem szEmb_apply (g : ↥(suzukiGroup a ↥F₀)) :
    szEmb F₀ a hcard d g = d * (wLong * subAntiSp F₀
      (Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard) g) * wLong) * d⁻¹ := by
  change d * wLong * subAntiSp F₀ (Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard) g) *
    (d * wLong)⁻¹ = _
  rw [mul_inv_rev, wLong_inv]
  group

theorem glMat_wLong_conj (g : ↥(suzukiGroup a ↥F₀)) (i j : Fin 4) :
    glMat ((wLong * subAntiSp F₀ (Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard) g) *
      wLong : antiSp k) : GL (Fin 4) k) i j =
      (((g : GL (Fin 4) ↥F₀) : Matrix (Fin 4) (Fin 4) ↥F₀) (Fin.rev i) (Fin.rev j) : k) := by
  change (minorJ k * glMat (subAntiSp F₀ _ : GL (Fin 4) k) * minorJ k) i j = _
  rw [minorJ_mul_mul_minorJ_apply, glMat_subAntiSp]
  rfl

theorem wLong_conj_suzukiS_mem (u v : ↥F₀) :
    wLong * subAntiSp F₀ (Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard)
      (suzukiSElt a ↥F₀ u v)) * wLong ∈ antiUnipotent k := by
  rw [mem_antiUnipotent_iff_upper]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [glMat_wLong_conj hcard, coe_suzukiSElt]
    fin_cases i <;> fin_cases j <;> simp at hij <;> simp [suzukiS, Fin.rev]
  · rw [glMat_wLong_conj hcard, coe_suzukiSElt]
    fin_cases i <;> simp [suzukiS, Fin.rev]

theorem wLong_conj_suzukiD_isUpper (l : (↥F₀)ˣ) :
    IsUpper (wLong * subAntiSp F₀ (Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard)
      (suzukiDElt a ↥F₀ l)) * wLong) := by
  intro i j hij
  rw [glMat_wLong_conj hcard, coe_suzukiDElt]
  have hne : Fin.rev i ≠ Fin.rev j := fun h => (ne_of_gt hij) (Fin.rev_injective h)
  simp [suzukiD, Matrix.diagonal_apply_ne _ hne]

theorem wLong_conj_suzukiS_zero (v : ↥F₀) :
    wLong * subAntiSp F₀ (Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard)
      (suzukiSElt a ↥F₀ 0 v)) * wLong = uElt 0 (v : k) ((v : k) ^ 2 ^ (a + 1)) 0 := by
  refine antiSp_ext ?_
  ext i j
  rw [glMat_wLong_conj hcard, coe_suzukiSElt,
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.glMat_uElt]
  fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN, uMat, Fin.rev]

theorem map_szEmb_suzukiU_le (hd : IsUpper d) :
    (suzukiU a ↥F₀).map (szEmb F₀ a hcard d) ≤ antiUnipotent k := by
  rw [CFSG.LieType.Ree.suzukiU, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨⟨u, v⟩, rfl⟩
  change szEmb F₀ a hcard d (suzukiSElt a ↥F₀ u v) ∈ antiUnipotent k
  rw [szEmb_apply]
  exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_isUpper hd) _).mp
    (wLong_conj_suzukiS_mem hcard u v)

theorem map_szEmb_suzukiB_le (hd : IsUpper d) :
    (suzukiB a ↥F₀).map (szEmb F₀ a hcard d) ≤
      Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
  rw [CFSG.LieType.Ree.suzukiB, Subgroup.map_sup]
  refine sup_le ((map_szEmb_suzukiU_le hcard hd).trans Subgroup.le_normalizer) ?_
  rw [CFSG.LieType.Ree.suzukiT, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨l, rfl⟩
  change szEmb F₀ a hcard d (suzukiDElt a ↥F₀ l) ∈
    Subgroup.normalizer (antiUnipotent k : Set (antiSp k))
  rw [szEmb_apply]
  exact mem_normalizer_of_isUpper (isUpper_mul (isUpper_mul hd
    (wLong_conj_suzukiD_isUpper hcard l)) (isUpper_inv hd))

theorem comap_szEmb_antiUnipotent (ha : 1 ≤ a) (hd : IsUpper d) :
    (antiUnipotent k).comap (szEmb F₀ a hcard d) = suzukiU a ↥F₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := benderData_suzuki ha hcard
  have hle : suzukiU a ↥F₀ ≤ (antiUnipotent k).comap (szEmb F₀ a hcard d) :=
    Subgroup.map_le_iff_le_comap.mp (map_szEmb_suzukiU_le hcard hd)
  have hU2 : IsPGroup 2 (antiUnipotent k) :=
    (CFSG.QuasithinUnique.Setup.X7b.card_and_isSylowTwoOf_antiUnipotent (K := k)).2.2.1
  have h2 : IsPGroup 2 ((antiUnipotent k).comap (szEmb F₀ a hcard d)) :=
    hU2.comap_of_injective _ (szEmb_injective hcard)
  have h := (hD.isPGroup.toSylow hD.not_dvd_index).is_maximal' h2 hle
  exact h

theorem comap_szEmb_normalizer (ha : 1 ≤ a) (hd : IsUpper d) :
    (Subgroup.normalizer (antiUnipotent k : Set (antiSp k))).comap (szEmb F₀ a hcard d) =
      Subgroup.normalizer (suzukiU a ↥F₀ : Set ↥(suzukiGroup a ↥F₀)) := by
  refine le_antisymm ?_ ?_
  · intro l hl
    have hU := comap_szEmb_antiUnipotent hcard ha hd
    rw [Subgroup.mem_comap] at hl
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [← hU, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hl _)
  · rw [suzuki_normalizer_suzukiU hcard]
    exact Subgroup.map_le_iff_le_comap.mp (map_szEmb_suzukiB_le hcard hd)

theorem exists_szEmb_eq_of_mem {w : antiSp k}
    (hw : w ∈ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom) :
    ∃ s ∈ suzukiU a ↥F₀, szEmb F₀ a hcard d s = w := by
  obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hw
  refine ⟨suzukiSElt a ↥F₀ 0 ⟨b, hb⟩, suzukiSElt_mem_suzukiU a ↥F₀ 0 _, ?_⟩
  rw [szEmb_apply, wLong_conj_suzukiS_zero hcard]
  rfl

theorem exists_sz_member_card
    {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k) (hW4 : 4 ≤ Nat.card W)
    {F₀ : Subfield k} {a : ℕ} (ha : 1 ≤ a) (hcard : Nat.card F₀ = 2 ^ (2 * a + 1))
    {d : antiSp k} (hd : IsUpper d)
    (hW : W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom) :
    ∃ (Y : Subgroup (antiSp k)) (g : antiSp k), g ∈ Y ∧
      W ⊔ W.map (MulAut.conj g).toMonoidHom = Y ∧
      IsSylowOf 2 (Y ⊓ antiUnipotent k) Y ∧
      kerIn (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) Y = ⊥ ∧
      CFSG.inSubgroup (CFSG.pCore 2) Y = ⊥ ∧
      CFSG.inSubgroup (CFSG.pCore 2)
        (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) = Y ⊓ antiUnipotent k ∧
      OddCoverExact ↥Y ∧
      ∃ m : ℕ, 3 ≤ m ∧ Nat.card ↥Y = (2 ^ m) ^ 2 * (((2 ^ m) ^ 2 + 1) * (2 ^ m - 1)) ∧
        Nat.card W ≤ 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcU := comap_szEmb_antiUnipotent hcard ha hd
  have hcN := comap_szEmb_normalizer hcard ha hd
  set ι := szEmb F₀ a hcard d with hιdef
  have hι : Function.Injective ι := szEmb_injective hcard
  have hD := benderData_suzuki ha hcard
  set E := W.comap ι with hE
  have hWr : W ≤ ι.range := fun w hw => by
    obtain ⟨s, -, hs⟩ := exists_szEmb_eq_of_mem hcard (hW hw)
    exact ⟨s, hs⟩
  have hEW : E.map ι = W := Subgroup.map_comap_eq_self hWr
  have hEU : E ≤ suzukiU a ↥F₀ := fun s hs => by
    obtain ⟨s', hs', he⟩ := exists_szEmb_eq_of_mem hcard (hW hs)
    rwa [← hι he]
  have hZc : ∀ x ∈ antiUnipotentCenter k, ∀ y ∈ antiUnipotentCenter k, x * y = y * x := by
    rintro _ ⟨b, c, rfl⟩ _ ⟨b', c', rfl⟩
    rw [CFSG.ComponentClassification.UnbalancedCatalog.SpChain.uElt_mul,
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.uElt_mul]
    congr 1 <;> ring
  have : IsElementaryAbelian 2 E := isElementaryAbelian_of
    (fun x hx y hy => hι (by rw [map_mul, map_mul]; exact hZc _ (hWZ hx) _ (hWZ hy)))
    (fun x hx => hι (by
      obtain ⟨b, c, hbc⟩ := hWZ hx
      rw [map_mul, map_one, hbc, uElt_center_mul_self]))
  have hE4 : 4 ≤ Nat.card E := by
    rwa [Nat.card_congr (E.equivMapOfInjective ι hι).toEquiv, hEW]
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  have hE1 : E ≠ ⊥ := by
    rintro h
    rw [h, Subgroup.card_bot] at hE4
    omega
  have hC : ∀ e ∈ E, e ≠ 1 → IsPGroup 2 (Subgroup.centralizer ({e} : Set _)) :=
    fun e he he1 => hD.centralizer_isPGroup e
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e he) he1)
  obtain ⟨x, hxN, hxL⟩ := exists_mem_sup_conjugate hD.stronglyEmbedded
    (hEU.trans Subgroup.le_normalizer) hE2 hE1
  obtain ⟨-, hsyl, -, -, hcore, hO2, hO2P⟩ :=
    bender_pair_props hD.isPGroup hD.not_dvd_index hD.stronglyEmbedded hC hEU hE4 hxN
  obtain ⟨b, hb, -, hEb, e, -, -⟩ :=
    bender_pair_suzuki hD (not_three_dvd_card_suzukiGroup hcard) hEU hE4 hxN
  set L := E ⊔ CFSG.conjugate E x with hL
  have hYU : L.map ι ⊓ antiUnipotent k = (suzukiU a ↥F₀ ⊓ L).map ι := by
    rw [map_inf_eq_map_inf_comap, hcU, inf_comm]
  have hYN : L.map ι ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) =
      (L ⊓ Subgroup.normalizer (suzukiU a ↥F₀ : Set ↥(suzukiGroup a ↥F₀))).map ι := by
    rw [map_inf_eq_map_inf_comap, hcN]
  have hconj : (CFSG.conjugate E x).map ι = W.map (MulAut.conj (ι x)⁻¹).toMonoidHom := by
    rw [← hEW, CFSG.conjugate, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp [map_inv]
  have hgY : (ι x)⁻¹ ∈ L.map ι := (L.map ι).inv_mem ⟨x, hxL, rfl⟩
  have hY : W ⊔ W.map (MulAut.conj (ι x)⁻¹).toMonoidHom = L.map ι := by
    rw [hL, Subgroup.map_sup, hEW, hconj]
  have hcardGF : Nat.card (GaloisField 2 (2 * b + 1)) = 2 ^ (2 * b + 1) :=
    GaloisField.card 2 (2 * b + 1) (by omega)
  refine ⟨L.map ι, (ι x)⁻¹, hgY, hY, ?_, ?_, ?_, ?_, ?_, 2 * b + 1, by omega, ?_, ?_⟩
  · rw [hYU]
    exact isSylowOf_map hι hsyl
  · rw [hYN, kerIn_map_of_injective hι, hcore, Subgroup.map_bot]
  · rw [inSubgroup_pCore_map hι, hO2, Subgroup.map_bot]
  · rw [hYN, inSubgroup_pCore_map hι, hO2P, ← hYU]
  · exact oddCoverExact_of_mulEquiv_suzuki hb hcardGF ((L.equivMapOfInjective ι hι).symm.trans e)
  · rw [← Nat.card_congr (L.equivMapOfInjective ι hι).toEquiv, Nat.card_congr e.toEquiv,
      CFSG.LieType.Ree.suzuki_order hcardGF]
    ring
  · rw [← hEW, ← Nat.card_congr (E.equivMapOfInjective ι hι).toEquiv]
    exact hEb

theorem exists_sz_member
    {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k) (hW4 : 4 ≤ Nat.card W)
    {F₀ : Subfield k} {a : ℕ} (ha : 1 ≤ a) (hcard : Nat.card F₀ = 2 ^ (2 * a + 1))
    {d : antiSp k} (hd : IsUpper d)
    (hW : W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom) :
    ∃ (Y : Subgroup (antiSp k)) (g : antiSp k), g ∈ Y ∧
      W ⊔ W.map (MulAut.conj g).toMonoidHom = Y ∧
      IsSylowOf 2 (Y ⊓ antiUnipotent k) Y ∧
      kerIn (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) Y = ⊥ ∧
      CFSG.inSubgroup (CFSG.pCore 2) Y = ⊥ ∧
      CFSG.inSubgroup (CFSG.pCore 2)
        (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) = Y ⊓ antiUnipotent k ∧
      OddCoverExact ↥Y ∧
      ∃ c ∈ Y, ∃ ℓ a' : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf c = ℓ ^ (a' + 1) ∧
        ∀ m : ℕ, 0 < m → ℓ ^ (a' + 1) ∣ 2 ^ m - 1 → Nat.card W ^ 2 ≤ 2 ^ m := by
  obtain ⟨Y, g, hgY, hY, hSyl, hcore, hO2, hO2B, hexact, m, hm3, hYc, hWm⟩ :=
    exists_sz_member_card hWZ hW4 ha hcard hd hW
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * m) (by omega) (by omega)
  have : Fact r.Prime := ⟨hr.prime⟩
  have hrY : r ∣ Nat.card ↥Y := by
    rw [hYc]
    exact ((primitive_dvd_sq_add_one (by omega) hr).trans (Dvd.intro _ rfl)).trans
      (Dvd.intro_left _ rfl)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hrY
  refine ⟨Y, g, hgY, hY, hSyl, hcore, hO2, hO2B, hexact, c, c.2, r, 0, hr.prime,
    hr.ne_two (by omega), by rw [zero_add, pow_one, Subgroup.orderOf_coe, hc], ?_⟩
  intro m' hm' hdvd
  rw [zero_add, pow_one] at hdvd
  have h4 : 4 * m ∣ m' := (hr.dvd_sub_one_iff (by omega) m').1 hdvd
  calc Nat.card W ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hWm 2
    _ = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ m' := Nat.pow_le_pow_right two_pos (by
        have := Nat.le_of_dvd hm' h4
        omega)

end Embedding

end CFSG.Quasithin.Ch3E213M.P6B
