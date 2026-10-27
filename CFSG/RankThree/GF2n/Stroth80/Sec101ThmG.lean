module

public import CFSG.RankThree.GF2n.Stroth80.Sec101TwoAbelian
public import CFSG.RankThree.GF2n.Stroth80.Sec101TwoFlag
public import CFSG.RankThree.GF2n.Stroth80.Sec101Half
public import CFSG.RankThree.GF2n.Stroth80.Sec101FlagLB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem GlobalModelAction.halfPair {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (Pk : GlobalModelAction M Q Z K γ M₀)
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X X' : Subgroup G} (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X)
    (hX' : IsClique101 M Q Z B X') (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X) (hD : IsRootB M B D)
    (hDX' : D ≤ X') : HalfPair (Pk.lam C) (Pk.lam D) := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  have hLCD : LB M Q C ⊓ LB M Q D = Q :=
    IsSaturated101.LB_inf_eq_of_inf_eq h34 H hX hsat hXX' hC hCX hD hDX'
  refine ⟨Pk.lam_comm hcC, Pk.lam_mul_self hcC, Pk.lam_comm hcD, Pk.lam_mul_self hcD,
    Pk.lam_inf_eq_bot hcC hcD hLCD, ?_, ?_⟩
  · intro t ht ht1 htN s hs hst
    obtain ⟨mt, hmt, rfl⟩ := Pk.mem_lam.mp ht
    obtain ⟨ms, hms, rfl⟩ := Pk.mem_lam.mp hs
    have hmtQ : (mt : G) ∉ Q := fun h => ht1 ((Pk.hφker mt).mpr h)
    exact (Pk.phi_mem_normalizer_iff hcD ms).mpr
      (IsSaturated101.mem_normalizer_of_comm h34 H hsat hX' hsat' hXX' hC hCX hD hDX' hms hmt
        hmtQ ((Pk.phi_mem_normalizer_iff hcC mt).mp htN) ((Pk.phi_comm_iff ms mt).mp hst))
  · intro s hs hs1 hsN t ht hts
    obtain ⟨ms, hms, rfl⟩ := Pk.mem_lam.mp hs
    obtain ⟨mt, hmt, rfl⟩ := Pk.mem_lam.mp ht
    have hmsQ : (ms : G) ∉ Q := fun h => hs1 ((Pk.hφker ms).mpr h)
    exact (Pk.phi_mem_normalizer_iff hcC mt).mpr
      (IsSaturated101.mem_normalizer_of_comm h34 H hsat' hX hsat (by rw [inf_comm]; exact hXX')
        hD hDX' hC hCX hmt hms hmsQ ((Pk.phi_mem_normalizer_iff hcD ms).mp hsN)
        ((Pk.phi_comm_iff mt ms).mp hts))

private theorem IsSaturated101.B_line_eq_zero_of_mem_normalizer
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {C D : Subgroup G} {c₀ d₀ : M₀.E} (hcl : IsLineGen M₀ C c₀)
    (hcentD : ∀ x ∈ Q, x ∈ Subgroup.centralizer (D : Set G) ↔ M₀.B (M₀.π x) d₀ = 0)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) : M₀.B c₀ d₀ = 0 := by
  obtain ⟨u, huC, huQ, hu⟩ : c₀ ∈ M₀.img C := (hcl c₀).mpr ⟨1, (one_smul K c₀).symm⟩
  rw [← hu]
  exact (hcentD u huQ).mp (Subgroup.mem_centralizer_iff.mpr fun d hd => (hCD u huC d hd).symm)

private theorem IsRootB.mapsTo_imgQInfQB_of_mem_normalizer
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (Pk : GlobalModelAction M Q Z K γ M₀) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {C D : Subgroup G} (hC : IsRootB M B C) (hD : IsRootB M B D)
    {g : M₀.E ≃ₗ[K] M₀.E} {x : M₀.E}
    (hg : g ∈ Pk.lam D ⊓ Subgroup.normalizer (Pk.lam C : Set (M₀.E ≃ₗ[K] M₀.E)))
    (hx : x ∈ imgQInfQB M₀ C) : g x ∈ imgQInfQB M₀ C := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  obtain ⟨hgD, hgN⟩ := hg
  obtain ⟨m, hm, rfl⟩ := Pk.mem_lam.mp hgD
  have hmN := (Pk.phi_mem_normalizer_iff hcC m).mp hgN
  have hP3 := IsRootB.conj_inf_QB_of_mem_normalizer H hC (hcD.LB_le_M hm) hmN
  rw [hcC.mem_imgQInfQB_iff HC.width HC.n_gt HC.noA2 Pk.h] at hx ⊢
  obtain ⟨y, hy, hyQ, rfl⟩ := hx
  rw [← Pk.hφπ m y hyQ]
  have hy' : (m : G) * y * (m : G)⁻¹ ∈ Q ⊓ QB C := by
    rw [← hP3, mem_conjSubgroup]; simpa [mul_assoc] using hy
  exact M₀.pi_mem_img hy' hy'.1

private theorem IsSaturated101.img_inf_imgQInfQB_eq_bot
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (Pk : GlobalModelAction M Q Z K γ M₀) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X X' : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {D : Subgroup G} (hD : IsRootB M B D) (hDX' : D ≤ X') :
    ∀ w ∈ M₀.img X, w ∈ imgQInfQB M₀ D → w = 0 := by
  have hcD : Ctx M Q Z D := hD.ctx hc
  have HD : Sec10Hyp hcD n := hD.sec10 H
  rintro w ⟨x, hx, hxQ, rfl⟩ hwD
  rw [hcD.mem_imgQInfQB_iff HD.width HD.n_gt HD.noA2 Pk.h,
    M₀.mem_img_iff (le_inf hcD.Z_le_Q hcD.Z_le_QB.1) hxQ] at hwD
  have hxZ : x ∈ Z := IsSaturated101.inf_QB_le_Z hc hsat' hX (by rw [inf_comm]; exact hXX')
    hD hDX' ⟨hx, hwD.2⟩
  exact (M₀.π_ker x hxQ).mpr hxZ

private theorem IsSaturated101.exists_img_not_smul (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X : Subgroup G}
    (hX : IsMaxClique101 M Q Z B X) {C : Subgroup G} (hCX : C ≤ X)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (Pk : GlobalModelAction M Q Z K γ M₀) {c₀ : M₀.E} (hcl : IsLineGen M₀ C c₀) :
    ∃ y ∈ M₀.img X, ∀ s : K, y ≠ s • c₀ := by
  by_contra hall
  push Not at hall
  have hsurj : Function.Surjective
      (fun s : K => (⟨s • c₀, M₀.img_mono hCX ((hcl _).mpr ⟨s, rfl⟩)⟩ :
        ↥(M₀.img X))) := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := hall y hy
    exact ⟨s, rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  have h2 := M₀.card_eq hX.1.le_Q hX.1.Z_le
  have h3 := hX.card_ge h34 H
  have hq4 := hc.hyp.q4
  rw [Pk.h.card] at h1
  have h5 : Nat.card X ≤ Nat.card Z * Nat.card Z := h2 ▸ Nat.mul_le_mul_left _ h1
  have h6 : Nat.card Z * Nat.card Z < Nat.card Z ^ 3 := by
    rw [← sq]; exact Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

private theorem IsSaturated101.mapsTo_img_of_mem_normalizer
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (Pk : GlobalModelAction M Q Z K γ M₀) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X : Subgroup G} (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X) (hD : IsRootB M B D)
    {g : M₀.E ≃ₗ[K] M₀.E}
    (hg : g ∈ Pk.lam D ⊓ Subgroup.normalizer (Pk.lam C : Set (M₀.E ≃ₗ[K] M₀.E)))
    {w : M₀.E} (hw : w ∈ M₀.img X) : g w ∈ M₀.img X := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  obtain ⟨hgD, hgN⟩ := hg
  obtain ⟨m, hm, rfl⟩ := Pk.mem_lam.mp hgD
  have hmX := IsSaturated101.mem_normalizer_of_mem_normalizer_LB H hX hsat hC hCX
    (hcD.LB_le_M hm) ((Pk.phi_mem_normalizer_iff hcC m).mp hgN)
  obtain ⟨x, hx, hxQ, rfl⟩ := hw
  rw [← Pk.hφπ m x hxQ]
  exact M₀.pi_mem_img ((Subgroup.mem_normalizer_iff.mp hmX x).mp hx)
    ((hcC.conj_mem_Q_of_mem_M (hcD.LB_le_M hm)).1 x hxQ)

private theorem HalfPair.card_lt_card_inf_normalizer {Γ : Type} [Group Γ] {P R : Subgroup Γ}
    [Finite P] (h : HalfPair P R) {f : Γ}
    (hf : f ∈ R ⊓ Subgroup.normalizer (P : Set Γ)) (hf1 : f ≠ 1)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hcardP : Nat.card P = Nat.card K ^ (n - 1))
    (h4 : 4 ≤ n) : Nat.card K < Nat.card ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) := by
  by_contra hle
  push Not at hle
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  have hsq := h.card_le_sq hf hf1
  rw [hcardP] at hsq
  have h1 : Nat.card K ^ 3 ≤ Nat.card K ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : Nat.card ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) ^ 2 ≤ Nat.card K ^ 2 :=
    Nat.pow_le_pow_left hle 2
  have h3 : Nat.card K ^ 2 < Nat.card K ^ 3 := Nat.pow_lt_pow_right hK2 (by norm_num)
  omega

private theorem IsSaturated101.false_of_two_flag_groups
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (Pk : GlobalModelAction M Q Z K γ M₀)
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X X' : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    (hD : IsRootB M B D) (hDX' : D ≤ X') {c₀ d₀ : M₀.E}
    (hFC : FlagData M₀ c₀ (imgQInfQB M₀ C) (Pk.lam C))
    (hinjC : ∀ T ∈ Pk.lam C, (∀ e ∈ imgQInfQB M₀ C, T e = e) → T = 1)
    (hcardC : Nat.card (Pk.lam C) = Nat.card K ^ (n - 1))
    (hFD : FlagData M₀ d₀ (imgQInfQB M₀ D) (Pk.lam D))
    (hinjD : ∀ T ∈ Pk.lam D, (∀ e ∈ imgQInfQB M₀ D, T e = e) → T = 1)
    (hDim : Module.finrank K (imgQInfQB M₀ C) = n)
    (hcl : IsLineGen M₀ C c₀)
    (hcentD : ∀ x ∈ Q, x ∈ Subgroup.centralizer (D : Set G) ↔ M₀.B (M₀.π x) d₀ = 0)
    (hHP : HalfPair (Pk.lam C) (Pk.lam D))
    {τ : G} (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hτN : τ ∈ Subgroup.normalizer (LB M Q C : Set G))
    (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c)
    {l r : G} (hl : l ∈ LB M Q C)
    (hlN : l ∉ Subgroup.normalizer (LB M Q D : Set G))
    (hr : r ∈ LB M Q D) (hrN : r ∉ Subgroup.normalizer (LB M Q C : Set G))
    (hq : Nat.card K <
      Nat.card ↥(Pk.lam C ⊓ Subgroup.normalizer (Pk.lam D : Set (M₀.E ≃ₗ[K] M₀.E))))
    (hEF : Nat.card ↥(Pk.lam C ⊓ Subgroup.normalizer (Pk.lam D : Set (M₀.E ≃ₗ[K] M₀.E))) ≤
      Nat.card ↥(Pk.lam D ⊓ Subgroup.normalizer (Pk.lam C : Set (M₀.E ≃ₗ[K] M₀.E)))) :
    False := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  haveI := Pk.finite_lam C
  haveI := Pk.finite_lam D
  have hτH : τ ∈ H0 M Z := hcD.LB_le_H0_cb hτ
  have hf1 : Pk.φ ⟨τ, hτH⟩ ≠ 1 := fun h1 => hτQ ((Pk.hφker _).mp h1)
  have hfF : Pk.φ ⟨τ, hτH⟩ ∈ Pk.lam D ⊓ Subgroup.normalizer (Pk.lam C : Set _) :=
    ⟨(Pk.phi_mem_lam_iff _).mpr hτ, (Pk.phi_mem_normalizer_iff hcC _).mpr hτN⟩
  have hlH : l ∈ H0 M Z := hcC.LB_le_H0_cb hl
  have hrH : r ∈ H0 M Z := hcD.LB_le_H0_cb hr
  have hl' : Pk.φ ⟨l, hlH⟩ ∈ Pk.lam C := (Pk.phi_mem_lam_iff _).mpr hl
  have hlN' : Pk.φ ⟨l, hlH⟩ ∉ Subgroup.normalizer (Pk.lam D : Set _) :=
    fun h => hlN ((Pk.phi_mem_normalizer_iff hcD _).mp h)
  have hr' : Pk.φ ⟨r, hrH⟩ ∈ Pk.lam D := (Pk.phi_mem_lam_iff _).mpr hr
  have hrN' : Pk.φ ⟨r, hrH⟩ ∉ Subgroup.normalizer (Pk.lam C : Set _) :=
    fun h => hrN ((Pk.phi_mem_normalizer_iff hcC _).mp h)
  refine FlagData.false_of_two_flags hFC hinjC hFD hinjD hDim hcardC inf_le_left inf_le_left
    inf_le_right ?_ ?_ (M₀.img X) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq hEF
  · exact fun g hg x hx => IsRootB.mapsTo_imgQInfQB_of_mem_normalizer Pk H hC hD hg hx
  · exact IsSaturated101.B_line_eq_zero_of_mem_normalizer hcl hcentD hCD
  · exact fun s => M₀.img_mono hCX ((hcl _).mpr ⟨s, rfl⟩)
  · intro w hw
    exact (hcC.mem_imgQInfQB_iff HC.width HC.n_gt HC.noA2 Pk.h w).mpr
      (M₀.img_mono (le_inf hX.1.le_Q (hX.1.le_QB C hC hCX)) hw)
  · exact IsSaturated101.img_inf_imgQInfQB_eq_bot Pk H hX.1 hsat' hXX' hD hDX'
  · exact IsSaturated101.exists_img_not_smul h34 H hX hCX Pk hcl
  · exact fun g hg w hw =>
      IsSaturated101.mapsTo_img_of_mem_normalizer Pk H hX.1 hsat hC hCX hD hg hw
  · intro l₁ hl₁ hl₁E e he
    exact hHP.exists_comm_eq hr' hrN' hl₁ (fun h => hl₁E ⟨hl₁, h⟩) he
  · exact ⟨_, hl', fun h => hlN' h.2⟩

private theorem IsSaturated101.false_of_halfPair_data
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (Pk : GlobalModelAction M Q Z K γ M₀)
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X X' : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    (hD : IsRootB M B D) (hDX' : D ≤ X') {c₀ d₀ : M₀.E}
    (hFC : FlagData M₀ c₀ (imgQInfQB M₀ C) (Pk.lam C))
    (hinjC : ∀ T ∈ Pk.lam C, (∀ e ∈ imgQInfQB M₀ C, T e = e) → T = 1)
    (hcardC : Nat.card (Pk.lam C) = Nat.card K ^ (n - 1))
    (hFD : FlagData M₀ d₀ (imgQInfQB M₀ D) (Pk.lam D))
    (hinjD : ∀ T ∈ Pk.lam D, (∀ e ∈ imgQInfQB M₀ D, T e = e) → T = 1)
    (hDim : Module.finrank K (imgQInfQB M₀ C) = n)
    (hcl : IsLineGen M₀ C c₀)
    (hcentD : ∀ x ∈ Q, x ∈ Subgroup.centralizer (D : Set G) ↔ M₀.B (M₀.π x) d₀ = 0)
    (hHP : HalfPair (Pk.lam C) (Pk.lam D))
    {τ : G} (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hτN : τ ∈ Subgroup.normalizer (LB M Q C : Set G)) : False := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  have h4 : 4 ≤ n := H.four_le h34
  haveI := Pk.finite_lam C
  haveI := Pk.finite_lam D
  have hτH : τ ∈ H0 M Z := hcD.LB_le_H0_cb hτ
  have hf1 : Pk.φ ⟨τ, hτH⟩ ≠ 1 := fun h1 => hτQ ((Pk.hφker _).mp h1)
  have hfF : Pk.φ ⟨τ, hτH⟩ ∈ Pk.lam D ⊓ Subgroup.normalizer (Pk.lam C : Set _) :=
    ⟨(Pk.phi_mem_lam_iff _).mpr hτ, (Pk.phi_mem_normalizer_iff hcC _).mpr hτN⟩
  have hCD := H.comm_of_mem_normalizer h34 hC hD hτ hτQ hτN
  obtain ⟨l, hl, hlN⟩ :=
    IsSaturated101.exists_not_mem_normalizer h34 H hsat hX' hXX' hC hCX hD hDX' hCD
  obtain ⟨r, hr, hrN⟩ := IsSaturated101.exists_not_mem_normalizer h34 H hsat' hX.1
    (by rw [inf_comm]; exact hXX') hD hDX' hC hCX fun d hd c hc' => (hCD c hc' d hd).symm
  have hlH : l ∈ H0 M Z := hcC.LB_le_H0_cb hl
  have hrH : r ∈ H0 M Z := hcD.LB_le_H0_cb hr
  have hl' : Pk.φ ⟨l, hlH⟩ ∈ Pk.lam C := (Pk.phi_mem_lam_iff _).mpr hl
  have hlN' : Pk.φ ⟨l, hlH⟩ ∉ Subgroup.normalizer (Pk.lam D : Set _) :=
    fun h => hlN ((Pk.phi_mem_normalizer_iff hcD _).mp h)
  have hr' : Pk.φ ⟨r, hrH⟩ ∈ Pk.lam D := (Pk.phi_mem_lam_iff _).mpr hr
  have hrN' : Pk.φ ⟨r, hrH⟩ ∉ Subgroup.normalizer (Pk.lam C : Set _) :=
    fun h => hrN ((Pk.phi_mem_normalizer_iff hcC _).mp h)
  have hEF := (hHP.card_eq hl' hlN' hr' hrN').le
  have hq := hHP.card_lt_card_inf_normalizer hfF hf1 hcardC h4
  exact IsSaturated101.false_of_two_flag_groups Pk h34 H hX hsat hX' hsat' hXX' hC hCX hD hDX'
    hFC hinjC hcardC hFD hinjD hDim hcl hcentD hHP hτ hτQ hτN hCD hl hlN hr hrN hq hEF

private theorem IsSaturated101.false_of_flag_setup
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (Pk : GlobalModelAction M Q Z K γ M₀)
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X X' : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    (hD : IsRootB M B D) (hDX' : D ≤ X') {τ : G}
    (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hτN : τ ∈ Subgroup.normalizer (LB M Q C : Set G)) : False := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  have HD : Sec10Hyp hcD n := hD.sec10 H
  obtain ⟨c₀, hc0, -, hcl, -, -⟩ := hcC.dictB Pk.h
  obtain ⟨d₀, hd0, -, hdl, hcentD, -⟩ := hcD.dictB Pk.h
  obtain ⟨hFC, hinjC, hcardC⟩ := hcC.flagData_lam HC.width HC.n_gt HC.noA2 Pk hc0 hcl
  obtain ⟨hFD, hinjD, -⟩ := hcD.flagData_lam HD.width HD.n_gt HD.noA2 Pk hd0 hdl
  obtain ⟨hDim, -, -⟩ := hcC.imgQInfQB_lagr HC.width HC.n_gt HC.noA2 Pk.h
  have hHP : HalfPair (Pk.lam C) (Pk.lam D) :=
    Pk.halfPair h34 H hX.1 hsat hX' hsat' hXX' hC hCX hD hDX'
  exact IsSaturated101.false_of_halfPair_data Pk h34 H hX hsat hX' hsat' hXX' hC hCX hD hDX'
    hFC hinjC hcardC hFD hinjD hDim hcl hcentD hHP hτ hτQ hτN

theorem IsSaturated101.mem_Q_of_mem_normalizer (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {X X' : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z) {C D : Subgroup G}
    (hC : IsRootB M B C) (hCX : C ≤ X) (hD : IsRootB M B D) (hDX' : D ≤ X') {τ : G}
    (hτ : τ ∈ LB M Q D) (hτN : τ ∈ Subgroup.normalizer (LB M Q C : Set G)) : τ ∈ Q := by
  classical
  by_contra hτQ
  obtain ⟨K, _, _, _, γ, M₀, ⟨Pk⟩⟩ := exists_globalModelAction hc.hyp
  exact IsSaturated101.false_of_flag_setup Pk h34 H hX hsat hX' hsat' hXX' hC hCX hD hDX'
    hτ hτQ hτN

end CFSG.RankThree.GF2n.Stroth80
