module

public import CFSG.RankThree.GF2n.Smith81.Statement
public import CFSG.RankThree.GF2n.Smith81.Sec1Types

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def CentDvdN (c : ℕ) (M Q Z S : Subgroup G) : Prop :=
  ∃ C : Subgroup G, Q ≤ C ∧ C ≤ H0 M Z ∧ (∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ S, ⁅h, x⁆ ∈ Q) ∧
    Nat.card C ∣ Nat.card Q * (c * (Nat.card Z - 1))

theorem centDvd_iff_centDvdN_one {M Q Z S : Subgroup G} :
    CentDvd M Q Z S ↔ CentDvdN 1 M Q Z S := by
  simp [CentDvd, CentDvdN]

theorem CentDvdN.mono {M Q Z S : Subgroup G} {c d : ℕ} (hcd : c ∣ d) (h : CentDvdN c M Q Z S) :
    CentDvdN d M Q Z S := by
  obtain ⟨C, hQC, hCH, hC, hdvd⟩ := h
  refine ⟨C, hQC, hCH, hC, hdvd.trans (Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_right hcd _))⟩

@[expose] def LinSetup (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    ∃ φ : (Lgen M (LB M Q B)) →* GL (Fin n) K, φ.range = StatedSL n K ∧
      φ.ker = Q.subgroupOf (Lgen M (LB M Q B)) ∧
      Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ V₁ ⊓ V₂ = Z ∧ V₁ ⊔ V₂ = Q ∧
        SectionAct (ι := Fin n) K (Lgen M (LB M Q B)) V₁ Z φ
          (fun g => (g : Matrix (Fin n) (Fin n) K)) ∧
        SectionAct (ι := Fin n) K (Lgen M (LB M Q B)) V₂ Z φ
          (fun g => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) ∧
        (∃ x ∈ M, conjSubgroup x V₁ = V₂) ∧ CentDvdN 2 M Q Z (Lgen M (LB M Q B))

theorem CaseE6.exists_linSetup {M Q Z B : Subgroup G} {n : ℕ} (h : CaseE6 M Q Z B n) :
    ∃ V₁ V₂ : Subgroup G, LinSetup M Q Z B n V₁ V₂ := by
  obtain ⟨K, hK, hKf, hKc, φ, hφr, hφk, V₁, V₂, h1, h2, h3, h4, h5, h6, hA1, hA2, hx, hC⟩ := h
  exact ⟨V₁, V₂, K, hK, hKf, hKc, φ, hφr, hφk, h1, h2, h3, h4, h5, h6, hA1, hA2, hx,
    (centDvd_iff_centDvdN_one.mp hC).mono (by norm_num)⟩

@[expose] def InZClass (Z : Subgroup G) (v : G) : Prop :=
  ∃ g z : G, z ∈ Z ∧ z ≠ 1 ∧ v = g * z * g⁻¹

@[expose] def HasDimOn (V Z : Subgroup G) (k : ℕ) (x : G) : Prop :=
  Nat.card ↥(⁅V, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (k + 1)

theorem card_sup_mul_card_inf_of_normalizer {A C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) = Nat.card ↥A * Nat.card ↥C := by
  have hAC : A ⊔ C ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hC
  haveI hN : (A.subgroupOf (A ⊔ C)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAC
  have hsup : C.subgroupOf (A ⊔ C) ⊔ A.subgroupOf (A ⊔ C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_right : C ≤ A ⊔ C) (le_sup_left : A ≤ A ⊔ C),
      show C ⊔ A = A ⊔ C from sup_comm C A, Subgroup.subgroupOf_self]
  have h1 : (A.subgroupOf (A ⊔ C)).relIndex (C.subgroupOf (A ⊔ C) ⊔ A.subgroupOf (A ⊔ C)) =
      (A.subgroupOf (A ⊔ C)).relIndex (C.subgroupOf (A ⊔ C)) :=
    Subgroup.relIndex_sup_right (H := C.subgroupOf (A ⊔ C)) (K := A.subgroupOf (A ⊔ C))
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have key1 : Nat.card ↥(A ⊔ C) = Nat.card ↥A * (A.subgroupOf (A ⊔ C)).index := by
    have h := Subgroup.card_mul_index (H := A.subgroupOf (A ⊔ C))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ C)).toEquiv] at h
    exact h.symm
  have hinf : A.subgroupOf (A ⊔ C) ⊓ C.subgroupOf (A ⊔ C) = (A ⊓ C).subgroupOf (A ⊔ C) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have h5 : Nat.card ↥(C.subgroupOf (A ⊔ C)) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : C ≤ A ⊔ C)).toEquiv
  have h6 : Nat.card ↥((A ⊓ C).subgroupOf (A ⊔ C)) = Nat.card ↥(A ⊓ C) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((inf_le_left : A ⊓ C ≤ A).trans (le_sup_left : A ≤ A ⊔ C))).toEquiv
  have key2 : Nat.card ↥C = Nat.card ↥(A ⊓ C) *
      (A.subgroupOf (A ⊔ C)).relIndex (C.subgroupOf (A ⊔ C)) := by
    have h := Subgroup.card_mul_index
      (H := (A.subgroupOf (A ⊔ C)).subgroupOf (C.subgroupOf (A ⊔ C)))
    have hm := Subgroup.card_map_of_injective
      (K := (A.subgroupOf (A ⊔ C)).subgroupOf (C.subgroupOf (A ⊔ C)))
      (C.subgroupOf (A ⊔ C)).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, hinf, h6] at hm
    rw [← hm, h5] at h
    exact h.symm
  rw [key1, h1, key2]
  ring

theorem Q_le_normalizer_of_Z_le [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) {A : Subgroup G} (hZA : Z ≤ A) (hAQ : A ≤ Q) :
    Q ≤ Subgroup.normalizer (A : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hh : h ∈ Q
  · have hc : ⁅q, h⁆ ∈ A := hZA (comm_mem_Z H hq hh)
    have e : q * h * q⁻¹ = ⁅q, h⁆ * h := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine ⟨fun h' => A.mul_mem hc h', fun h' => ?_⟩
    have h'' := A.mul_mem (A.inv_mem hc) h'
    rwa [inv_mul_cancel_left] at h''
  · have h1 : h ∉ A := fun hA => hh (hAQ hA)
    have h2 : q * h * q⁻¹ ∉ A := by
      intro hA
      apply hh
      have h3 : q⁻¹ * (q * h * q⁻¹) * q ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem hq) (hAQ hA)) hq
      have e2 : q⁻¹ * (q * h * q⁻¹) * q = h := by group
      rwa [e2] at h3
    exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩

theorem card_eq_pow_of_sectionIso {K : Type} [Field K] {n : ℕ} {A Z : Subgroup G}
    [(Z.subgroupOf A).Normal]
    (hZA : Z ≤ A) (hK : Nat.card K = Nat.card Z)
    (ψ : ↥A ⧸ Z.subgroupOf A ≃* Multiplicative (Fin n → K)) :
    Nat.card ↥A = Nat.card ↥Z ^ (n + 1) := by
  have h := Subgroup.card_mul_index (H := Z.subgroupOf A)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv] at h
  have hidx : (Z.subgroupOf A).index = Nat.card ↥Z ^ n := by
    calc (Z.subgroupOf A).index = Nat.card (↥A ⧸ Z.subgroupOf A) := rfl
      _ = Nat.card (Multiplicative (Fin n → K)) := Nat.card_congr ψ.toEquiv
      _ = Nat.card (Fin n → K) := Nat.card_congr Multiplicative.ofAdd.symm
      _ = Nat.card K ^ n := by rw [Nat.card_fun, Nat.card_fin]
      _ = Nat.card ↥Z ^ n := by rw [hK]
  rw [hidx] at h
  rw [← h]
  ring

private theorem le_Lgen_aux (M L : Subgroup G) : L ≤ Lgen M L := by
  unfold Lgen
  have h1 : conjSubgroup 1 L ≤ ⨆ (m : G) (_ : m ∈ M), conjSubgroup m L :=
    le_iSup₂_of_le 1 M.one_mem le_rfl
  rwa [conjSubgroup_one] at h1

theorem LinSetup.width [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (H : StrothHyp M Q Z) (h : LinSetup M Q Z B n V₁ V₂) :
    Width Q Z n := by
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
    hs₁, hs₂, hswap, hcent⟩ := h
  obtain ⟨-, hN₁, ψ₁, -⟩ := hs₁
  obtain ⟨-, hN₂, ψ₂, -⟩ := hs₂
  have hA := card_sup_mul_card_inf_of_normalizer (A := V₁) (C := V₂)
    (le_trans hV₂Q (Q_le_normalizer_of_Z_le H hZV₁ hV₁Q))
  rw [hsup, hint] at hA
  have hV₁c := card_eq_pow_of_sectionIso hZV₁ hcard ψ₁
  have hV₂c := card_eq_pow_of_sectionIso hZV₂ hcard ψ₂
  have hZpos : 0 < Nat.card ↥Z := by
    have := H.q4
    omega
  unfold Width
  apply Nat.eq_of_mul_eq_mul_right hZpos
  rw [hA, hV₁c, hV₂c]
  ring

theorem LinSetup.exists_mul [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (H : StrothHyp M Q Z) (h : LinSetup M Q Z B n V₁ V₂) :
    ∀ q ∈ Q, ∃ a ∈ V₁, ∃ b ∈ V₂, q = a * b := by
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
    hs₁, hs₂, hswap, hcent⟩ := h
  haveI hN : (V₁.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Q_le_normalizer_of_Z_le H hZV₁ hV₁Q)
  have hsupQ : V₁.subgroupOf Q ⊔ V₂.subgroupOf Q = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hV₁Q hV₂Q, hsup, Subgroup.subgroupOf_self]
  intro q hq
  have hmem : (⟨q, hq⟩ : ↥Q) ∈ V₁.subgroupOf Q ⊔ V₂.subgroupOf Q := by
    rw [hsupQ]
    exact Subgroup.mem_top _
  obtain ⟨a', ha', b', hb', hab⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have ha : (a' : G) ∈ V₁ := Subgroup.mem_subgroupOf.mp ha'
  have hb : (b' : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hb'
  refine ⟨(a' : G), ha, (b' : G), hb, ?_⟩
  have h2 : ((a' * b' : ↥Q) : G) = q := congrArg Subtype.val hab
  rw [Subgroup.coe_mul] at h2
  exact h2.symm

theorem CaseE6.width [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
    (H : StrothHyp M Q Z) (h : CaseE6 M Q Z B n) : Width Q Z n := by
  obtain ⟨V₁, V₂, hS⟩ := h.exists_linSetup
  exact hS.width H

theorem CaseE6.two_le [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
    (hc : Ctx M Q Z B) (hnTI : ¬ IsTIMod M Q (LB M Q B)) (h : CaseE6 M Q Z B n) : 2 ≤ n := by
  by_contra hlt
  push Not at hlt
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  interval_cases n
  ·
    have hw := CaseE6.width hc.hyp h
    unfold Width at hw
    have hQZ : Nat.card ↥Q = Nat.card ↥Z := by
      rw [hw]
      norm_num
    have hZQeq : Z = Q := Subgroup.eq_of_le_of_card_ge hZQ hQZ.le
    obtain ⟨g, hg⟩ := hc.conj
    have hBZ : B ≤ Z := by
      rw [hZQeq]
      exact hc.le
    have hBeq : B = Z :=
      Subgroup.eq_of_le_of_card_ge hBZ (le_of_eq (by rw [hg, card_conjSubgroup]))
    exact hc.ne hBeq
  ·
    obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, V₁, V₂, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
      hs₁, hs₂, hswap, hcent⟩ := h
    have hbot : StatedSL 1 K = ⊥ := by
      unfold StatedSL
      rw [eq_bot_iff, Subgroup.closure_le]
      intro A hA
      have hdet : (A : Matrix (Fin 1) (Fin 1) K).det = 1 := hA
      have hmat : (A : Matrix (Fin 1) (Fin 1) K) = 1 := by
        ext i j
        rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, Matrix.one_apply_eq]
        rw [Matrix.det_fin_one] at hdet
        exact hdet
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      exact Units.ext hmat
    have hφ : ∀ g : Lgen M (LB M Q B), φ g = 1 := by
      intro g
      have hg : φ g ∈ φ.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
      rw [hrange, hbot, Subgroup.mem_bot] at hg
      exact hg
    have hLQ : Lgen M (LB M Q B) ≤ Q := by
      intro x hx
      have hx' : (⟨x, hx⟩ : Lgen M (LB M Q B)) ∈ φ.ker := MonoidHom.mem_ker.mpr (hφ _)
      rw [hker, Subgroup.mem_subgroupOf] at hx'
      exact hx'
    have hBQ : LB M Q B = Q :=
      le_antisymm ((le_Lgen_aux M (LB M Q B)).trans hLQ) le_sup_left
    apply hnTI
    rw [hBQ]
    unfold IsTIMod
    intro m hm
    left
    rw [conjSubgroup_eq_self_iff.mpr (hc.hyp.Q_normal.2 hm), inf_idem]

def linInvT {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) : GL (Fin n) K :=
  ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ, (g : Matrix (Fin n) (Fin n) K)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

def linInvTHom (n : ℕ) (K : Type) [Field K] : GL (Fin n) K →* GL (Fin n) K where
  toFun := linInvT
  map_one' := by
    apply Units.ext
    show (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [_root_.inv_one, Units.val_one, Matrix.transpose_one]
  map_mul' g h := by
    apply Units.ext
    show (((g * h)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ *
        (((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem linInvT_linInvT {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    linInvT (linInvT g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) K)

theorem linInvT_inv_transpose {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    (((linInvT g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      (g : Matrix (Fin n) (Fin n) K) :=
  Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) K)

theorem linInvTHom_apply_apply (n : ℕ) (K : Type) [Field K] (g : GL (Fin n) K) :
    linInvTHom n K (linInvTHom n K g) = g :=
  linInvT_linInvT g

theorem linInvTHom_injective (n : ℕ) (K : Type) [Field K] :
    Function.Injective (linInvTHom n K) := by
  intro a b hab
  calc a = linInvTHom n K (linInvTHom n K a) := (linInvTHom_apply_apply n K a).symm
    _ = linInvTHom n K (linInvTHom n K b) := by rw [hab]
    _ = b := linInvTHom_apply_apply n K b

theorem det_linInvTHom {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    (linInvTHom n K g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h := congrArg Matrix.det (Units.inv_mul g)
  rw [Matrix.det_mul, hg, mul_one, Matrix.det_one] at h
  show Matrix.det (Matrix.transpose ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1
  rw [Matrix.det_transpose]
  exact h

theorem map_linInvTHom_statedSL (n : ℕ) (K : Type) [Field K] :
    (StatedSL n K).map (linInvTHom n K) = StatedSL n K := by
  unfold StatedSL
  rw [MonoidHom.map_closure]
  congr 1
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact det_linInvTHom (g := B) hB
  · intro hA
    exact ⟨linInvTHom n K A, det_linInvTHom (g := A) hA, linInvTHom_apply_apply n K A⟩

theorem range_linInvTHom_comp {S : Type} [Group S] {n : ℕ} {K : Type} [Field K]
    (φ : S →* GL (Fin n) K) (h : φ.range = StatedSL n K) :
    ((linInvTHom n K).comp φ).range = StatedSL n K := by
  rw [MonoidHom.range_comp, h, map_linInvTHom_statedSL]

theorem sectionAct_congr_of_forall_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {S V Z : Subgroup G} {φ φ' : S →* GL ι K} {act act' : GL ι K → Matrix ι ι K}
    (h : SectionAct K S V Z φ act) (hact : ∀ s : S, act' (φ' s) = act (φ s)) :
    SectionAct K S V Z φ' act' := by
  obtain ⟨hS, hN, ψ, hψ⟩ := h
  exact ⟨hS, hN, ψ, fun s v w hw => by rw [hact s]; exact hψ s v w hw⟩

theorem LinSetup.symm {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (h : LinSetup M Q Z B n V₁ V₂) : LinSetup M Q Z B n V₂ V₁ := by
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
    hs₁, hs₂, hswap, hcent⟩ := h
  refine ⟨K, hK, hfin, hcard, (linInvTHom n K).comp φ, ?_, ?_,
    hZV₂, hV₂Q, hZV₁, hV₁Q, (inf_comm _ _).trans hint, (sup_comm _ _).trans hsup,
    ?_, ?_, ?_, hcent⟩
  · exact range_linInvTHom_comp φ hrange
  · exact (MonoidHom.ker_comp_of_injective φ (linInvTHom n K)
      (linInvTHom_injective n K)).trans hker
  · exact sectionAct_congr_of_forall_eq hs₂ (fun s => rfl)
  · exact sectionAct_congr_of_forall_eq hs₁ (fun s => linInvT_inv_transpose (φ s))
  · obtain ⟨x, hx, hxV⟩ := hswap
    refine ⟨x⁻¹, M.inv_mem hx, ?_⟩
    rw [← hxV, ← CFSG.RankThree.GF2n.conjSubgroup_mul, _root_.inv_mul_cancel,
      CFSG.RankThree.GF2n.conjSubgroup_one]

end CFSG.RankThree.GF2n.Smith81
