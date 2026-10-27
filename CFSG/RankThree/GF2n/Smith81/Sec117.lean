module

public import CFSG.RankThree.GF2n.Smith81.Sec114
public import CFSG.RankThree.GF2n.Smith81.TiFusion
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Smith81.Sec1Main

public section

namespace CFSG.RankThree.GF2n.Smith81.Sec117

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

def IsMaxP (C P : Subgroup G) : Prop :=
  P ≤ C ∧ IsPGroup 2 P ∧ ∀ P' : Subgroup G, IsPGroup 2 P' → P ≤ P' → P' ≤ C → P' = P

theorem conj_conj_inv (g : G) (P : Subgroup G) :
    conjSubgroup g (conjSubgroup g⁻¹ P) = P := by
  ext x
  simp only [mem_conjSubgroup]
  rw [show g⁻¹⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x by group]

theorem conj_inv_conj (g : G) (P : Subgroup G) :
    conjSubgroup g⁻¹ (conjSubgroup g P) = P := by
  have := conj_conj_inv g⁻¹ P
  rwa [inv_inv] at this

theorem IsMaxP.conj {C P : Subgroup G} (h : IsMaxP C P) (g : G) :
    IsMaxP (conjSubgroup g C) (conjSubgroup g P) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, fun P' hP' hle hleC => ?_⟩
  have h1 := h.2.2 (conjSubgroup g⁻¹ P') (hP'.map _) ?_ ?_
  · rw [← h1, conj_conj_inv]
  · have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    exact (conj_inv_conj g P).symm.le.trans this
  · have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hleC
    exact this.trans (conj_inv_conj g C).le

theorem centralizer_conj (g a : G) :
    conjSubgroup g (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * a * g⁻¹ * x := by group
  · intro h
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [h]
      _ = a * (g⁻¹ * x * g) := by group

section Fin

variable [Finite G]

theorem exists_isMaxP {C R : Subgroup G} (hR : IsPGroup 2 R) (hRC : R ≤ C) :
    ∃ S, R ≤ S ∧ IsMaxP C S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' : IsPGroup 2 (R.subgroupOf C) := hR.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨X, hX⟩ := hR'.exists_le_sylow
  refine ⟨(X : Subgroup C).map C.subtype, fun x hx => ?_, Subgroup.map_subtype_le _,
    X.isPGroup'.map _, fun P' hP' hle hleC => ?_⟩
  · exact ⟨⟨x, hRC hx⟩, hX (show (⟨x, hRC hx⟩ : C) ∈ R.subgroupOf C from hx), rfl⟩
  · have hP'' : IsPGroup 2 (P'.subgroupOf C) :=
      hP'.comap_of_injective C.subtype C.subtype_injective
    have hXle : (X : Subgroup C) ≤ P'.subgroupOf C := fun y hy => hle ⟨y, hy, rfl⟩
    have heq := X.is_maximal' hP'' hXle
    ext x
    constructor
    · intro hx
      have : (⟨x, hleC hx⟩ : C) ∈ P'.subgroupOf C := hx
      rw [heq] at this
      exact ⟨_, this, rfl⟩
    · intro hx
      exact hle hx

def IsMaxP.toSylow {C P : Subgroup G} (h : IsMaxP C P) : Sylow 2 C where
  toSubgroup := P.subgroupOf C
  isPGroup' := h.2.1.comap_of_injective C.subtype C.subtype_injective
  is_maximal' := by
    intro Y hY hle
    have hYG : IsPGroup 2 (Y.map C.subtype) := hY.map _
    have hPY : P ≤ Y.map C.subtype := fun x hx =>
      ⟨⟨x, h.1 hx⟩, hle (show (⟨x, h.1 hx⟩ : C) ∈ P.subgroupOf C from hx), rfl⟩
    have heq := h.2.2 _ hYG hPY (Subgroup.map_subtype_le _)
    ext y
    constructor
    · intro hy
      have : (y : G) ∈ Y.map C.subtype := ⟨y, hy, rfl⟩
      rw [heq] at this
      exact this
    · intro hy
      exact hle hy

theorem IsMaxP.exists_conj {C P T : Subgroup G} (hP : IsMaxP C P) (hT : IsMaxP C T) :
    ∃ c ∈ C, conjSubgroup c P = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C hP.toSylow hT.toSylow
  refine ⟨c, c.2, ?_⟩
  have key2 : MulAut.conj c • (hP.toSylow : Subgroup C) = (hT.toSylow : Subgroup C) := by
    rw [← Sylow.coe_subgroup_smul, hc]
  have mem : ∀ x : C, x ∈ (hT.toSylow : Subgroup C) ↔ (c : G)⁻¹ * x * c ∈ P := by
    intro x
    rw [← key2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    show ((MulAut.conj c)⁻¹ • x : C) ∈ P.subgroupOf C ↔ _
    rw [Subgroup.mem_subgroupOf]
    simp [MulAut.smul_def, MulAut.conj_apply]
  have hC : ∀ x : G, (c : G)⁻¹ * x * c ∈ C → x ∈ C := by
    intro x h1
    have : x = c * ((c : G)⁻¹ * x * c) * (c : G)⁻¹ := by group
    rw [this]
    exact C.mul_mem (C.mul_mem c.2 h1) (C.inv_mem c.2)
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro hx
    have hxC := hC x (hP.1 hx)
    have := (mem ⟨x, hxC⟩).mpr hx
    exact this
  · intro hx
    exact (mem ⟨x, hT.1 hx⟩).mp hx

end Fin

def IsRoot (Z : Subgroup G) (x : G) : Prop := ∃ h z : G, z ∈ Z ∧ x = h * z * h⁻¹

theorem conj_mul' (g h : G) (T : Subgroup G) :
    conjSubgroup (g * h) T = conjSubgroup g (conjSubgroup h T) := by
  ext x
  simp only [mem_conjSubgroup]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

section Stroth

variable [Finite G] {M Q Z : Subgroup G}

theorem isPGroup_Q' (H : StrothHyp M Q Z) : IsPGroup 2 Q := by
  rw [H.hQ]
  exact (CFSG.RankThree.GF2n.inSubgroup_pCore_two M).1

theorem exists_ne_one_Z (H : StrothHyp M Q Z) : ∃ z ∈ Z, z ≠ 1 := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (by
    intro h
    have := H.q4
    rw [h, Subgroup.card_bot] at this
    omega : Z ≠ ⊥)
  exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩

theorem mem_M_of_conj_mem_Z (H : StrothHyp M Q Z) {z m : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h : m * z * m⁻¹ ∈ Z) : m ∈ M := by
  have hne : Z ⊓ conjSubgroup m Z ≠ ⊥ := by
    intro hbot
    have hmem : m * z * m⁻¹ ∈ Z ⊓ conjSubgroup m Z :=
      Subgroup.mem_inf.mpr ⟨h, by
        rw [mem_conjSubgroup, show m⁻¹ * (m * z * m⁻¹) * m = z by group]; exact hz⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hz1
    have : z = m⁻¹ * (m * z * m⁻¹) * m := by group
    rw [this, hmem]
    group
  have h2 := conjSubgroup_eq_of_isTI H.ti hne
  have h3 := conjSubgroup_eq_self_iff.mp h2
  rwa [H.normalizer_Z.1] at h3

theorem exists_pow_conj (H : StrothHyp M Q Z) {k : G} (hkM' : k ∈ M)
    (hkreg : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ v ∈ Z, k ^ i * v = v * k ^ i → v = 1)
    {z z' : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz' : z' ∈ Z) (hz1' : z' ≠ 1) :
    ∃ i : ℕ, k ^ i * z * (k ^ i)⁻¹ = z' := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set q := Nat.card Z with hq
  have hconjZ : ∀ (m : G), m ∈ M → ∀ v ∈ Z, m * v * m⁻¹ ∈ Z := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hm) v).mp hv
  let f : ℕ → G := fun i => k ^ i * z * (k ^ i)⁻¹
  have hfmem : ∀ i, f i ∈ Z := fun i => hconjZ _ (pow_mem hkM' i) z hz
  have hfne : ∀ i, f i ≠ 1 := by
    intro i h
    apply hz1
    have : z = (k ^ i)⁻¹ * f i * k ^ i := by simp only [f]; group
    rw [this, h]; group
  have hinj : ∀ i j, i < j → j < q - 1 → f i ≠ f j := by
    intro i j hij hjq hfe
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd0 : 0 < d := by omega
    have h1 : k ^ d * z = z * k ^ d := by
      have h2 : k ^ i * z * (k ^ i)⁻¹ = k ^ i * (k ^ d * z * (k ^ d)⁻¹) * (k ^ i)⁻¹ := by
        have := hfe
        simp only [f, pow_add, mul_inv_rev] at this
        calc k ^ i * z * (k ^ i)⁻¹ = k ^ i * k ^ d * z * ((k ^ d)⁻¹ * (k ^ i)⁻¹) := this
          _ = _ := by group
      have h3 : z = k ^ d * z * (k ^ d)⁻¹ := by
        have := mul_left_cancel (mul_right_cancel (b := (k ^ i)⁻¹) h2)
        simpa [mul_assoc] using this
      calc k ^ d * z = (k ^ d * z * (k ^ d)⁻¹) * k ^ d := by group
        _ = z * k ^ d := by rw [← h3]
    exact hz1 (hkreg d hd0 (by omega) z hz h1)
  let S : Finset G := Finset.univ.filter (fun x => x ∈ Z ∧ x ≠ 1)
  have hSc : S.card = q - 1 := by
    have h1 : (Finset.univ.filter (fun x => x ∈ Z)).card = q := by
      rw [hq, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h2 : S = (Finset.univ.filter (fun x => x ∈ Z)).erase 1 := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [h2, Finset.card_erase_of_mem (by simp [Z.one_mem]), h1]
  let T : Finset G := (Finset.range (q - 1)).image f
  have hTc : T.card = q - 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hinj i j h hj hij
    · exact hinj j i h hi hij.symm
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hfmem i, hfne i⟩
  have hTS' : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hSc, hTc])
  have hz'S : z' ∈ S := by simp [S, hz', hz1']
  rw [← hTS'] at hz'S
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz'S
  exact ⟨i, hi⟩

section Model

variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem line_of_ctx {X : Subgroup G} (hc : Ctx M Q Z X) [Finite K]
    (hD : GlobalModelData M Q Z γ M₀) :
    ∃ b : M₀.E, b ≠ 0 ∧ ∀ y ∈ Q, (y ∈ X ⊔ Z ↔ ∃ s : K, M₀.π y = s • b) := by
  obtain ⟨b, hb0, -, hb, -, -⟩ := hc.dictB hD
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  refine ⟨b, hb0, fun y hy => ⟨fun h => ?_, fun ⟨s, hs⟩ => ?_⟩⟩
  · have hle : X ⊔ Z ≤ M₀.lift (M₀.img X) := sup_le
      (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩)
      (fun z hz => ⟨hZQ hz, by
        rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact AddSubgroup.zero_mem _⟩)
    exact (hb _).mp (hle h).2
  · obtain ⟨x, hxX, hxQ, hx⟩ := (hb _).mpr ⟨s, hs⟩
    have h1 : x⁻¹ * y ∈ Z := by
      refine (M₀.π_ker _ (Q.mul_mem (Q.inv_mem hxQ) hy)).mp ?_
      rw [M₀.π_mul _ (Q.inv_mem hxQ) _ hy, Tim79.QuadModel.pi_inv M₀ hxQ, hx, hs, neg_add_cancel]
    have : y = x * (x⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hxX h1

theorem exists_smul_of_perp {e₀ v : M₀.E} (he₀ : e₀ ≠ 0)
    (hv : ∀ e, M₀.B e e₀ = 0 → M₀.B v e = 0) : ∃ c : K, v = c • e₀ := by
  obtain ⟨e₁, he₁⟩ : ∃ e₁, M₀.B e₁ e₀ = 1 := by
    obtain ⟨f, hf⟩ : ∃ f, M₀.B f e₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact he₀ (M₀.nondeg e₀ fun f => by rw [Tim79.QuadModel.B_comm e₀ f, hcon f, neg_zero])
    refine ⟨(M₀.B f e₀)⁻¹ • f, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
  refine ⟨-M₀.B v e₁, ?_⟩
  have h0 : v + M₀.B v e₁ • e₀ = 0 := by
    refine M₀.nondeg _ fun f => ?_
    have hd : M₀.B (f - M₀.B f e₀ • e₁) e₀ = 0 := by
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, he₁,
        mul_one, sub_self]
    have h1 := hv _ hd
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h1
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h1,
      Tim79.QuadModel.B_comm e₀ f]
    ring
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h0

theorem mem_Q_and_line (H : StrothHyp M Q Z) (hD : GlobalModelData M Q Z γ M₀) {a r : G}
    (haQ : a ∈ Q) (haZ : a ∉ Z) (hrM : r ∈ M)
    (hr : ∀ c ∈ Q ⊓ Subgroup.centralizer ({a} : Set G), r * c = c * r) :
    r ∈ Q ∧ ∃ c : K, M₀.π r = c • M₀.π a := by
  have hrQ := smith_1_14 H haQ haZ hrM hr
  refine ⟨hrQ, exists_smul_of_perp (fun h => haZ ((M₀.π_ker a haQ).mp h)) fun e he => ?_⟩
  obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
  have hya : ⁅y, a⁆ = 1 := (GM.comm_eq_one_iff hD hyQ haQ).mpr he
  have hyC : y ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hya)⟩
  exact (GM.comm_eq_one_iff hD hrQ hyQ).mp (commutatorElement_eq_one_iff_mul_comm.mpr (hr y hyC))

theorem root_of_line [Finite K] (H : StrothHyp M Q Z) (hD : GlobalModelData M Q Z γ M₀)
    {a x : G} (haQ : a ∈ Q) (haZ : a ∉ Z) (hxQ : x ∈ Q) (hxZ : x ∉ Z)
    (hx : ∃ c : K, M₀.π x = c • M₀.π a) (hroot : IsRoot Z x) : IsRoot Z a := by
  obtain ⟨g, hgQ, hxg⟩ := stroth_2_6 H hxQ hxZ hroot
  have hne : conjSubgroup g Z ≠ Z := fun h => hxZ (h ▸ hxg)
  have hc : Ctx M Q Z (conjSubgroup g Z) := ⟨H, ⟨g, rfl⟩, hgQ, hne⟩
  obtain ⟨b, -, hb⟩ := line_of_ctx hc hD
  obtain ⟨s, hs⟩ := (hb x hxQ).mp (Subgroup.mem_sup_left hxg)
  obtain ⟨c, hc'⟩ := hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hxZ ((M₀.π_ker x hxQ).mp (by rw [hc', zero_smul]))
  have haX : a ∈ conjSubgroup g Z ⊔ Z := (hb a haQ).mpr ⟨c⁻¹ * s, by
    rw [mul_smul, ← hs, hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  obtain ⟨h, hh⟩ := hc.exists_conj_mem_Z (by rwa [sup_comm]) ha1
  exact ⟨h, h⁻¹ * a * h, hh, by group⟩

end Model

theorem sup_le_of_mem {X X' : Subgroup G} (hc : Ctx M Q Z X) (hc' : Ctx M Q Z X')
    {x : G} (hx : x ∈ X ⊔ Z) (hx' : x ∈ X' ⊔ Z) (hxZ : x ∉ Z) : X ⊔ Z ≤ X' ⊔ Z := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, -, hb⟩ := line_of_ctx hc hD
  obtain ⟨b', -, hb'⟩ := line_of_ctx hc' hD
  have hXQ : X ⊔ Z ≤ Q := sup_le hc.le hc.hyp.Z_normal.1
  have hxQ := hXQ hx
  obtain ⟨s, hs⟩ := (hb x hxQ).mp hx
  obtain ⟨s', hs'⟩ := (hb' x hxQ).mp hx'
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hxZ ((M₀.π_ker x hxQ).mp (by rw [hs, zero_smul]))
  intro y hy
  have hyQ := hXQ hy
  obtain ⟨t, ht⟩ := (hb y hyQ).mp hy
  refine (hb' y hyQ).mpr ⟨t * (s⁻¹ * s'), ?_⟩
  have hbb : b = (s⁻¹ * s') • b' := by
    rw [mul_smul, ← hs', hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [ht, hbb, smul_smul]

theorem sup_eq_of_mem {X X' : Subgroup G} (hc : Ctx M Q Z X) (hc' : Ctx M Q Z X')
    {x : G} (hx : x ∈ X ⊔ Z) (hx' : x ∈ X' ⊔ Z) (hxZ : x ∉ Z) : X ⊔ Z = X' ⊔ Z :=
  le_antisymm (sup_le_of_mem hc hc' hx hx' hxZ) (sup_le_of_mem hc' hc hx' hx hxZ)

theorem center_root_mem_Z (H : StrothHyp M Q Z) {a : G} (haQ : a ∈ Q) (haZ : a ∉ Z)
    (hna : ¬ IsRoot Z a) {S : Subgroup G} (hCS : Q ⊓ Subgroup.centralizer ({a} : Set G) ≤ S)
    (hSM : S ≤ M) {x : G} (hxS : x ∈ S) (hxc : ∀ s ∈ S, s * x = x * s) (hx : IsRoot Z x) :
    x ∈ Z := by
  by_contra hxZ
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨hxQ, hline⟩ :=
    mem_Q_and_line H hD haQ haZ (hSM hxS) (fun c hc => (hxc c (hCS hc)).symm)
  exact hna (root_of_line H hD haQ haZ hxQ hxZ hline hx)

theorem exists_center_Z (H : StrothHyp M Q Z) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hZS : Z ≤ S) (hSM : S ≤ M) : ∃ z ∈ Z, z ≠ 1 ∧ ∀ s ∈ S, s * z = z * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hS.isNilpotent
  let N : Subgroup S := Z.subgroupOf S
  haveI : N.Normal := ⟨fun n hn s => by
    show ((s : G) * n * (s : G)⁻¹) ∈ Z
    exact (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 (hSM s.2)) n).mp hn⟩
  have hN : N ≠ ⊥ := by
    obtain ⟨z, hz, hz1⟩ := exists_ne_one_Z H
    intro h
    have : (⟨z, hZS hz⟩ : S) ∈ N := hz
    rw [h, Subgroup.mem_bot] at this
    exact hz1 (congrArg Subtype.val this)
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  obtain ⟨⟨w, hwN, hwC⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  refine ⟨(w : G), hwN, fun h => hw1 (Subtype.ext (Subtype.ext h)), fun s hs => ?_⟩
  have := Subgroup.mem_center_iff.mp hwC ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem isMaxP_centralizer (H : StrothHyp M Q Z) {a : G} (haQ : a ∈ Q) (haZ : a ∉ Z)
    (hna : ¬ IsRoot Z a) {S : Subgroup G}
    (hS : IsMaxP (M ⊓ Subgroup.centralizer ({a} : Set G)) S)
    (hCS : Q ⊓ Subgroup.centralizer ({a} : Set G) ≤ S) :
    IsMaxP (Subgroup.centralizer ({a} : Set G)) S := by
  refine ⟨hS.1.trans inf_le_right, hS.2.1, fun P hP hSP hPC => ?_⟩
  have hSM : S ≤ M := hS.1.trans inf_le_left
  have hPM : P ⊓ M = S := hS.2.2 _ (hP.to_le inf_le_left) (le_inf hSP hSM)
    (fun x hx => ⟨(Subgroup.mem_inf.mp hx).2, hPC (Subgroup.mem_inf.mp hx).1⟩)
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hP.isNilpotent
  have hlt' : S.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hne (le_antisymm htop hSP)
  obtain ⟨y, hyN, hyS⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt')
  have hyconj : ∀ t : P, (t : G) ∈ S ↔ (y : G) * t * (y : G)⁻¹ ∈ S := fun t =>
    Subgroup.mem_normalizer_iff.mp hyN t
  have hy1 : ∀ s ∈ S, (y : G) * s * (y : G)⁻¹ ∈ S := fun s hs =>
    (hyconj ⟨s, hSP hs⟩).mp hs
  have hy2 : ∀ s ∈ S, (y : G)⁻¹ * s * y ∈ S := by
    intro s hs
    have ht : (y : G)⁻¹ * s * y ∈ P := P.mul_mem (P.mul_mem (P.inv_mem y.2) (hSP hs)) y.2
    refine (hyconj ⟨_, ht⟩).mpr ?_
    show (y : G) * ((y : G)⁻¹ * s * y) * (y : G)⁻¹ ∈ S
    rw [show (y : G) * ((y : G)⁻¹ * s * y) * (y : G)⁻¹ = s by group]
    exact hs
  have hZS : Z ≤ S := fun z hz => hCS ⟨H.Z_normal.1 hz,
    Subgroup.mem_centralizer_singleton_iff.mpr (Z_central H hz haQ)⟩
  obtain ⟨z, hzZ, hz1, hzc⟩ := exists_center_Z H hS.2.1 hZS hSM
  have hcen : ∀ t ∈ S, t * ((y : G) * z * (y : G)⁻¹) = ((y : G) * z * (y : G)⁻¹) * t := by
    intro t ht
    have h1 := hzc _ (hy2 t ht)
    calc t * ((y : G) * z * (y : G)⁻¹) = y * (((y : G)⁻¹ * t * y) * z) * (y : G)⁻¹ := by group
      _ = y * (z * ((y : G)⁻¹ * t * y)) * (y : G)⁻¹ := by rw [h1]
      _ = _ := by group
  have hw := center_root_mem_Z H haQ haZ hna hCS hSM (hy1 z (hZS hzZ)) hcen ⟨y, z, hzZ, rfl⟩
  have hyM := mem_M_of_conj_mem_Z H hzZ hz1 hw
  have hyPM : (y : G) ∈ P ⊓ M := ⟨y.2, hyM⟩
  rw [hPM] at hyPM
  exact hyS hyPM

theorem smith_1_17_nonroot (H : StrothHyp M Q Z) {a b g : G} (haQ : a ∈ Q) (haZ : a ∉ Z)
    (hbQ : b ∈ Q) (hbZ : b ∉ Z) (hna : ¬ IsRoot Z a) (hg : g * a * g⁻¹ = b) :
    ∃ m ∈ M, m * a * m⁻¹ = b := by
  have hnb : ¬ IsRoot Z b := by
    rintro ⟨h, z, hz, e⟩
    refine hna ⟨g⁻¹ * h, z, hz, ?_⟩
    have : a = g⁻¹ * b * g := by rw [← hg]; group
    rw [this, e]
    group
  have hQ2 := isPGroup_Q' H
  have hsub : ∀ c : G, Q ⊓ Subgroup.centralizer ({c} : Set G) ≤
      M ⊓ Subgroup.centralizer ({c} : Set G) := fun c => inf_le_inf_right _ H.Q_normal.1
  obtain ⟨S, hCS, hS⟩ := exists_isMaxP (hQ2.to_le inf_le_left) (hsub a)
  obtain ⟨T, hCT, hT⟩ := exists_isMaxP (hQ2.to_le inf_le_left) (hsub b)
  have hS' := isMaxP_centralizer H haQ haZ hna hS hCS
  have hT' := isMaxP_centralizer H hbQ hbZ hnb hT hCT
  have hgS := hS'.conj g
  rw [centralizer_conj, hg] at hgS
  obtain ⟨c, hcC, hcT⟩ := hgS.exists_conj hT'
  have hZS : Z ≤ S := fun z hz => hCS ⟨H.Z_normal.1 hz,
    Subgroup.mem_centralizer_singleton_iff.mpr (Z_central H hz haQ)⟩
  obtain ⟨z, hzZ, hz1, hzc⟩ := exists_center_Z H hS.2.1 hZS (hS.1.trans inf_le_left)
  have hmS : conjSubgroup (c * g) S = T := by rw [conj_mul', hcT]
  have hmzT : (c * g) * z * (c * g)⁻¹ ∈ T := by
    rw [← hmS, mem_conjSubgroup, show (c * g)⁻¹ * ((c * g) * z * (c * g)⁻¹) * (c * g) = z by
      group]
    exact hZS hzZ
  have hcen : ∀ t ∈ T, t * ((c * g) * z * (c * g)⁻¹) = ((c * g) * z * (c * g)⁻¹) * t := by
    intro t ht
    rw [← hmS, mem_conjSubgroup] at ht
    have h1 := hzc _ ht
    calc t * ((c * g) * z * (c * g)⁻¹) = (c * g) * (((c * g)⁻¹ * t * (c * g)) * z) * (c * g)⁻¹ :=
          by group
      _ = (c * g) * (z * ((c * g)⁻¹ * t * (c * g))) * (c * g)⁻¹ := by rw [h1]
      _ = _ := by group
  have hw := center_root_mem_Z H hbQ hbZ hnb hCT (hT.1.trans inf_le_left) hmzT hcen
    ⟨c * g, z, hzZ, rfl⟩
  refine ⟨c * g, mem_M_of_conj_mem_Z H hzZ hz1 hw, ?_⟩
  have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  calc c * g * a * (c * g)⁻¹ = c * (g * a * g⁻¹) * c⁻¹ := by group
    _ = b := by rw [hg, hcb]; group

theorem isPGroup_LB {A : Subgroup G} (hc : Ctx M Q Z A) : IsPGroup 2 (LB M Q A) := by
  intro l
  have h2 : (l : G) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB l.2
  obtain ⟨k, hk⟩ := isPGroup_Q' hc.hyp ⟨_, h2⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  rw [pow_succ', pow_mul]
  exact this

theorem exists_conj_sup_eq
    (h5 : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G))
    {A B' : Subgroup G} (hA : Ctx M Q Z A) (hB : Ctx M Q Z B') :
    ∃ m ∈ M, conjSubgroup m B' ⊔ Z = A ⊔ Z := by
  have H := hA.hyp
  obtain ⟨S, hLS, hS⟩ := exists_isMaxP (isPGroup_LB hA) hA.LB_le_H0
  obtain ⟨S', hLS', hS'⟩ := exists_isMaxP (isPGroup_LB hB) hB.LB_le_H0
  obtain ⟨c, hcH, hcS⟩ := hS'.exists_conj hS
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hcH).1
  have hB'' := hB.conj_of_mem hcM
  have hLS'' : LB M Q (conjSubgroup c B') ≤ S := by
    rw [hB.LB_conj hcM, ← hcS]
    exact Subgroup.map_mono hLS'
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 H hD
  haveI : Finite M₀.E := Module.finite_of_finite K
  let φ' := φ.comp (Subgroup.inclusion hS.1)
  let Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E) := φ'.range
  have hΛ : IsPGroup 2 Λ := hS.2.1.of_surjective φ'.rangeRestrict φ'.rangeRestrict_surjective
  obtain ⟨b, hb0, -⟩ := hA.dictB hD
  have hTop : (⊤ : Submodule K M₀.E) ≠ ⊥ := by
    intro h
    have : b ∈ (⊤ : Submodule K M₀.E) := Submodule.mem_top
    rw [h] at this
    exact hb0 ((Submodule.mem_bot K).mp this)
  obtain ⟨v, -, hv0, hfix⟩ :=
    exists_fixed_vector_of_isPGroup Λ hΛ ⊤ (fun _ _ _ _ => Submodule.mem_top) hTop
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
  have hfixS : ∀ l ∈ S, ⁅l, x⁆ ∈ Z := by
    intro l hl
    have hmem : φ ⟨l, hS.1 hl⟩ ∈ Λ := ⟨⟨l, hl⟩, rfl⟩
    have h1 := hfix _ hmem
    rw [← hφπ _ x hxQ] at h1
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ
      (conj_mem_Q H (Subgroup.mem_inf.mp (hS.1 hl)).1 hxQ)).mpr h1
  have hxA : x ∈ A ⊔ Z := by
    have : x ∈ CQt Q Z (LB M Q A) := ⟨hxQ, fun l hl => hfixS l (hLS hl)⟩
    rw [h5 A hA] at this
    exact this
  have hxB : x ∈ conjSubgroup c B' ⊔ Z := by
    have : x ∈ CQt Q Z (LB M Q (conjSubgroup c B')) := ⟨hxQ, fun l hl => hfixS l (hLS'' hl)⟩
    rw [h5 _ hB''] at this
    exact this
  have hxZ : x ∉ Z := fun h => hv0 ((M₀.π_ker x hxQ).mpr h)
  exact ⟨c, hcM, sup_eq_of_mem hB'' hA hxB hxA hxZ⟩

theorem exists_conj_in {A : Subgroup G} (hc : Ctx M Q Z A) {a a' : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (ha' : a' ∈ A) (ha1' : a' ≠ 1) : ∃ m ∈ M, m * a * m⁻¹ = a' := by
  have H := hc.hyp
  obtain ⟨g, rfl⟩ := hc.conj
  have hz : g⁻¹ * a * g ∈ Z := mem_conjSubgroup.mp ha
  have hz' : g⁻¹ * a' * g ∈ Z := mem_conjSubgroup.mp ha'
  have hz1 : g⁻¹ * a * g ≠ 1 := fun h => ha1 (by
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hz1' : g⁻¹ * a' * g ≠ 1 := fun h => ha1' (by
    have : a' = g * (g⁻¹ * a' * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hZQA : Z ≤ conjSubgroup g Q := by
    have := hc.Z_le_QB.1
    rwa [(hc.QB_eq rfl).2] at this
  have hc' : Ctx M Q Z (conjSubgroup g⁻¹ Z) := by
    refine ⟨H, ⟨g⁻¹, rfl⟩, fun x hx => ?_, fun h => ?_⟩
    · rw [mem_conjSubgroup, inv_inv] at hx
      have := hZQA hx
      rw [mem_conjSubgroup] at this
      simpa [mul_assoc] using this
    · apply hc.ne
      have h1 : g⁻¹ ∈ Subgroup.normalizer (Z : Set G) := conjSubgroup_eq_self_iff.mp h
      have h2 : g ∈ Subgroup.normalizer (Z : Set G) := by simpa using Subgroup.inv_mem _ h1
      exact conjSubgroup_eq_self_iff.mpr h2
  obtain ⟨k, hk, -, hkreg⟩ := hc'.cartan
  rw [(hc'.QB_eq rfl).2] at hk
  obtain ⟨hkM, hkQ⟩ := Subgroup.mem_inf.mp hk
  obtain ⟨i, hi⟩ := exists_pow_conj H hkM hkreg hz hz1 hz' hz1'
  have hk₁M : k ^ i ∈ M := pow_mem hkM i
  have hk₁Q : k ^ i ∈ Q ⊔ conjSubgroup g⁻¹ Q := pow_mem hkQ i
  set k₁ := k ^ i with hk₁
  set A' := conjSubgroup g⁻¹ Z with hA'
  have hZQ' : Z ≤ conjSubgroup g⁻¹ Q := by
    have := hc'.Z_le_QB.1
    rwa [(hc'.QB_eq rfl).2] at this
  have hA'Q' : A' ≤ conjSubgroup g⁻¹ Q := Subgroup.map_mono H.Z_normal.1
  have hWQ : A' ⊔ Z ≤ Q := sup_le hc'.le H.Z_normal.1
  have hWQ' : A' ⊔ Z ≤ conjSubgroup g⁻¹ Q := sup_le hA'Q' hZQ'
  have hnorm : Q ⊔ conjSubgroup g⁻¹ Q ≤ Subgroup.normalizer ((A' ⊔ Z : Subgroup G) : Set G) := by
    refine sup_le (fun y hy => Subgroup.mem_normalizer_fintype fun x hx => ?_)
      (fun y hy => Subgroup.mem_normalizer_fintype fun x hx => ?_)
    · have e : y * x * y⁻¹ = ⁅y, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact (A' ⊔ Z).mul_mem (Subgroup.mem_sup_right (comm_mem_Z H hy (hWQ hx))) hx
    · have e : y * x * y⁻¹ = ⁅y, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact (A' ⊔ Z).mul_mem
        (Subgroup.mem_sup_left (H.toHyp79.comm_mem_conj g⁻¹ hy (hWQ' hx))) hx
  set a₀ := g⁻¹ * (g⁻¹ * a * g) * g with ha₀def
  have ha₀ : a₀ ∈ A' := by
    rw [hA', mem_conjSubgroup, inv_inv, ha₀def,
      show g * (g⁻¹ * (g⁻¹ * a * g) * g) * g⁻¹ = g⁻¹ * a * g by group]
    exact hz
  have ha₀1 : a₀ ≠ 1 := fun h => hz1 (by
    have : g⁻¹ * a * g = g * a₀ * g⁻¹ := by rw [ha₀def]; group
    rw [this, h]; group)
  have hwW : k₁ * a₀ * k₁⁻¹ ∈ A' ⊔ Z :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hk₁Q) a₀).mp (Subgroup.mem_sup_left ha₀)
  have hwZ : k₁ * a₀ * k₁⁻¹ ∉ Z := by
    intro hw
    have h1 := (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 (M.inv_mem hk₁M)) _).mp hw
    rw [show k₁⁻¹ * (k₁ * a₀ * k₁⁻¹) * k₁⁻¹⁻¹ = a₀ by group] at h1
    have h2 : a₀ ∈ Z ⊓ A' := Subgroup.mem_inf.mpr ⟨h1, ha₀⟩
    rw [hc'.inf_eq_bot, Subgroup.mem_bot] at h2
    exact ha₀1 h2
  have hdec : ((A' ⊔ Z : Subgroup G) : Set G) = (A' : Set G) * Z :=
    Subgroup.coe_mul_of_left_le_normalizer_right A' Z (fun u hu => H.Z_normal.2 (hc'.Z_le_QB.2 hu))
  have hwW' : k₁ * a₀ * k₁⁻¹ ∈ (A' : Set G) * Z := by rw [← hdec]; exact hwW
  obtain ⟨a₁, ha₁, z₁, hz₁, hw_eq⟩ := Set.mem_mul.mp hwW'
  have ha₁Z : a₁ ∉ Z := fun h => hwZ (hw_eq ▸ Z.mul_mem h hz₁)
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨y, hyQ, hy⟩ := GM.exists_comm hD (hc'.le ha₁) ha₁Z (Z.inv_mem hz₁)
  have hya : y * a₁ * y⁻¹ = k₁ * a₀ * k₁⁻¹ := by
    have h1 : ⁅y, a₁⁆ = z₁ := by rw [← commutatorElement_inv, hy, inv_inv]
    have hcz : a₁ * z₁ = z₁ * a₁ := (Z_central H hz₁ (hc'.le ha₁)).symm
    rw [← hw_eq, hcz, ← h1, commutatorElement_def]
    group
  have hTI : IsTI A' := isTI_conjSubgroup H.ti g⁻¹
  have hne : A' ⊓ conjSubgroup (y⁻¹ * k₁) A' ≠ ⊥ := by
    intro hbot
    have hmem : a₁ ∈ A' ⊓ conjSubgroup (y⁻¹ * k₁) A' := Subgroup.mem_inf.mpr ⟨ha₁, by
      rw [mem_conjSubgroup,
        show (y⁻¹ * k₁)⁻¹ * a₁ * (y⁻¹ * k₁) = k₁⁻¹ * (y * a₁ * y⁻¹) * k₁ by group, hya,
        show k₁⁻¹ * (k₁ * a₀ * k₁⁻¹) * k₁ = a₀ by group]
      exact ha₀⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ha₁Z (hmem ▸ Z.one_mem)
  have hfix := conjSubgroup_eq_of_isTI hTI hne
  have hm₀ : g * (y⁻¹ * k₁) * g⁻¹ ∈ M := by
    rw [← H.normalizer_Z.1, ← conjSubgroup_eq_self_iff]
    calc conjSubgroup (g * (y⁻¹ * k₁) * g⁻¹) Z
        = conjSubgroup g (conjSubgroup (y⁻¹ * k₁) (conjSubgroup g⁻¹ Z)) := by
          rw [conj_mul', conj_mul']
      _ = conjSubgroup g A' := by rw [← hA', hfix]
      _ = Z := by rw [hA', conj_conj_inv]
  refine ⟨g * (y⁻¹ * k₁) * g⁻¹, hm₀, ?_⟩
  have hyz : y⁻¹ * (g⁻¹ * a' * g) * y = g⁻¹ * a' * g := by
    have := Z_central H hz' hyQ
    calc y⁻¹ * (g⁻¹ * a' * g) * y = y⁻¹ * ((g⁻¹ * a' * g) * y) := by group
      _ = y⁻¹ * (y * (g⁻¹ * a' * g)) := by rw [this]
      _ = _ := by group
  calc g * (y⁻¹ * k₁) * g⁻¹ * a * (g * (y⁻¹ * k₁) * g⁻¹)⁻¹ =
      g * (y⁻¹ * (k₁ * (g⁻¹ * a * g) * k₁⁻¹) * y) * g⁻¹ := by group
    _ = g * (g⁻¹ * a' * g) * g⁻¹ := by rw [hi, hyz]
    _ = a' := by group

theorem exists_conj_of_mem_sup {A : Subgroup G} (hc : Ctx M Q Z A) {a x : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hx : x ∈ A ⊔ Z) (hxZ : x ∉ Z) : ∃ m ∈ M, m * a * m⁻¹ = x := by
  have H := hc.hyp
  have hdec : ((A ⊔ Z : Subgroup G) : Set G) = (A : Set G) * Z :=
    Subgroup.coe_mul_of_left_le_normalizer_right A Z (fun u hu => H.Z_normal.2 (hc.Z_le_QB.2 hu))
  have hx' : x ∈ (A : Set G) * Z := by rw [← hdec]; exact hx
  obtain ⟨a', ha', z₀, hz₀, rfl⟩ := Set.mem_mul.mp hx'
  have ha'Z : a' ∉ Z := fun h => hxZ (Z.mul_mem h hz₀)
  have ha'1 : a' ≠ 1 := fun h => ha'Z (h ▸ Z.one_mem)
  obtain ⟨m, hm, hma⟩ := exists_conj_in hc ha ha1 ha' ha'1
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨y, hyQ, hy⟩ := GM.exists_comm hD (hc.le ha') ha'Z (Z.inv_mem hz₀)
  refine ⟨y * m, M.mul_mem (H.Q_normal.1 hyQ) hm, ?_⟩
  have h1 : ⁅y, a'⁆ = z₀ := by rw [← commutatorElement_inv, hy, inv_inv]
  have hcz : a' * z₀ = z₀ * a' := (Z_central H hz₀ (hc.le ha')).symm
  calc y * m * a * (y * m)⁻¹ = y * (m * a * m⁻¹) * y⁻¹ := by group
    _ = y * a' * y⁻¹ := by rw [hma]
    _ = a' * z₀ := by rw [hcz, ← h1, commutatorElement_def]; group

theorem smith_1_17_root
    (h5 : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G))
    (H : StrothHyp M Q Z) {a b g : G} (haQ : a ∈ Q) (haZ : a ∉ Z) (hbQ : b ∈ Q) (hbZ : b ∉ Z)
    (hra : IsRoot Z a) (hg : g * a * g⁻¹ = b) : ∃ m ∈ M, m * a * m⁻¹ = b := by
  have hrb : IsRoot Z b := by
    obtain ⟨h, z, hz, rfl⟩ := hra
    exact ⟨g * h, z, hz, by rw [← hg]; group⟩
  obtain ⟨ga, hgaQ, haA⟩ := stroth_2_6 H haQ haZ hra
  obtain ⟨gb, hgbQ, hbB⟩ := stroth_2_6 H hbQ hbZ hrb
  have hA : Ctx M Q Z (conjSubgroup ga Z) := ⟨H, ⟨ga, rfl⟩, hgaQ, fun h => haZ (h ▸ haA)⟩
  have hB : Ctx M Q Z (conjSubgroup gb Z) := ⟨H, ⟨gb, rfl⟩, hgbQ, fun h => hbZ (h ▸ hbB)⟩
  obtain ⟨m₁, hm₁, heq⟩ := exists_conj_sup_eq h5 hA hB
  have hx : m₁ * b * m₁⁻¹ ∈ conjSubgroup ga Z ⊔ Z := by
    rw [← heq]
    refine Subgroup.mem_sup_left ?_
    rw [mem_conjSubgroup, show m₁⁻¹ * (m₁ * b * m₁⁻¹) * m₁ = b by group]
    exact hbB
  have hxZ : m₁ * b * m₁⁻¹ ∉ Z := by
    intro h
    have h1 := (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 (M.inv_mem hm₁)) _).mp h
    rw [show m₁⁻¹ * (m₁ * b * m₁⁻¹) * m₁⁻¹⁻¹ = b by group] at h1
    exact hbZ h1
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  obtain ⟨m, hm, hma⟩ := exists_conj_of_mem_sup hA haA ha1 hx hxZ
  refine ⟨m₁⁻¹ * m, M.mul_mem (M.inv_mem hm₁) hm, ?_⟩
  calc m₁⁻¹ * m * a * (m₁⁻¹ * m)⁻¹ = m₁⁻¹ * (m * a * m⁻¹) * m₁ := by group
    _ = b := by rw [hma]; group

end Stroth

end CFSG.RankThree.GF2n.Smith81.Sec117

namespace CFSG.RankThree.GF2n.Smith81

open Sec117

theorem smith117Statement_holds : Smith117Statement := by
  intro G _ _ M Q Z B hc n hw hn hnoA2 h5 a haQ haZ b hbQ hbZ g hg
  by_cases hra : IsRoot Z a
  · exact smith_1_17_root h5 hc.hyp haQ haZ hbQ hbZ hra hg
  · exact smith_1_17_nonroot hc.hyp haQ haZ hbQ hbZ hra hg

end CFSG.RankThree.GF2n.Smith81
