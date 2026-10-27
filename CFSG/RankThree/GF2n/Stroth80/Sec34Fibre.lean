module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Symm
public import CFSG.RankThree.GF2n.Stroth80.Sec36

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def OrthLe (M B : Subgroup G) : Prop :=
  ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) → conjSubgroup m B ≤ QB B

omit [Finite G] in
private theorem orthLe_comm_conj {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (g : G) : ∀ x ∈ conjSubgroup g X, ∀ y ∈ conjSubgroup g Y, x * y = y * x := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, h x hx y hy]

theorem OrthLe.conj {M B : Subgroup G} (h : OrthLe M B) {m : G} (hm : m ∈ M) :
    OrthLe M (conjSubgroup m B) := by
  intro m' hm' hcomm
  have hkM : m⁻¹ * m' * m ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hm) hm') hm
  have e1 : conjSubgroup m' (conjSubgroup m B) =
      conjSubgroup m (conjSubgroup (m⁻¹ * m' * m) B) := by
    rw [← conjSubgroup_mul, ← conjSubgroup_mul]
    congr 1
    group
  have hkc : ∀ x ∈ conjSubgroup (m⁻¹ * m' * m) B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have h1 : m * x * m⁻¹ ∈ conjSubgroup m' (conjSubgroup m B) := by
      rw [e1, mem_conjSubgroup, show m⁻¹ * (m * x * m⁻¹) * m = x by group]
      exact hx
    have h2 : m * y * m⁻¹ ∈ conjSubgroup m B := by
      rw [mem_conjSubgroup, show m⁻¹ * (m * y * m⁻¹) * m = y by group]
      exact hy
    have h3 := hcomm _ h1 _ h2
    have e : x * y = m⁻¹ * ((m * x * m⁻¹) * (m * y * m⁻¹)) * m := by group
    rw [e, h3]
    group
  rw [e1, QB_conj]
  exact Subgroup.map_mono (h _ hkM hkc)

omit [Finite G] in
private theorem orthLe_comm_iSup_of_pairwise {M B : Subgroup G}
    (h : ∀ m ∈ M, ∀ m' ∈ M, ∀ x ∈ conjSubgroup m B, ∀ y ∈ conjSubgroup m' B, x * y = y * x) :
    ∀ x ∈ (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B),
      ∀ y ∈ (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B), x * y = y * x := by
  have h1 : ∀ m ∈ M, (⨆ (k : G) (_ : k ∈ M), conjSubgroup k B) ≤
      Subgroup.centralizer (conjSubgroup m B : Set G) := fun m hm =>
    iSup₂_le fun m' hm' y hy =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => h m hm m' hm' x hx y hy
  have h2 : (⨆ (k : G) (_ : k ∈ M), conjSubgroup k B) ≤
      Subgroup.centralizer ((⨆ (k : G) (_ : k ∈ M), conjSubgroup k B : Subgroup G) : Set G) :=
    iSup₂_le fun m hm => Subgroup.le_centralizer_iff.mpr (h1 m hm)
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (h2 hy) x hx

theorem Ctx.orthLe_of_card_Spure (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (hS : Nat.card Q * Nat.card Z < Nat.card hc.Spure) :
    OrthLe M B := by
  intro m hm hcomm
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ conjSubgroup m B, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : conjSubgroup m B = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    obtain ⟨g, hg⟩ := hc.conj
    have h1 : Nat.card (conjSubgroup m B) = Nat.card Z := by
      rw [card_conjSubgroup, hg, card_conjSubgroup]
    have h4 := hc.hyp.q4
    rw [hbot, Subgroup.card_bot] at h1
    omega
  exact hc.conj_le_QB_of_card_Spure hw hn hno hS hm hx hx1
    (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)

theorem Ctx.exists_mem_QB_M_comm_eq {C : Subgroup G} (hC : Ctx M Q Z C) {b : G}
    (hbQ : b ∈ QB C) (hb : b ∉ Z ⊔ C) {c : G} (hc : c ∈ C) : ∃ s ∈ QB C ⊓ M, ⁅s, b⁆ = c := by
  obtain ⟨g, hg⟩ := hC.conj
  obtain ⟨-, hQC⟩ := Ctx.QB_eq hC hg
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hC.hyp
  have hZQC : Z ≤ conjSubgroup g Q := hQC ▸ hC.Z_le_QB.1
  have hbQg : b ∈ conjSubgroup g Q := hQC ▸ hbQ
  have hcg : c ∈ conjSubgroup g Z := hg ▸ hc
  have hZ' : conjSubgroup g⁻¹ (conjSubgroup g Z) = Z := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hne : conjSubgroup g⁻¹ (conjSubgroup g Z) ≠ conjSubgroup g Z := by
    rw [hZ', ← hg]
    exact hC.ne.symm
  have hle : conjSubgroup g⁻¹ (conjSubgroup g Z) ≤ conjSubgroup g Q := by
    rw [hZ']
    exact hZQC
  obtain ⟨e, -, he⟩ := (h.conj g).line g⁻¹ hne hle
  rw [hZ'] at he
  set M₁ := M₀.conj g
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hZ : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hcon
    have h4 := hC.hyp.q4
    rw [hZ, Subgroup.card_bot] at h4
    omega
  have hzQ : z ∈ conjSubgroup g Q := hZQC hzZ
  have hz0 : M₁.π z ≠ 0 := by
    intro h0
    have h1 : z ∈ Z ⊓ C := ⟨hzZ, hg ▸ (M₁.π_ker z hzQ).mp h0⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at h1
    exact hz1 h1
  obtain ⟨s₁, hs₁⟩ := (he _).mp (M₁.pi_mem_img hzZ hzQ)
  have hs₁0 : s₁ ≠ 0 := by
    rintro rfl
    exact hz0 (by rw [hs₁, zero_smul])
  have hind : ∀ s : GaloisField 2 n, M₁.π b ≠ s • M₁.π z := by
    intro s hs
    have hbim : M₁.π b ∈ M₁.img Z := (he _).mpr ⟨s * s₁, by rw [hs, hs₁, smul_smul]⟩
    have := (M₁.mem_img_iff (S := Z ⊔ conjSubgroup g Z) le_sup_right hbQg).mp
      (M₁.img_mono le_sup_left hbim)
    exact hb (hg ▸ this)
  obtain ⟨y, hy, h1, h2⟩ := M₁.exists_comm_eq_one (h.conj g).reg hbQg hzQ hz0 hind hcg
  have hyZ : y ∈ Subgroup.centralizer (Z : Set G) := by
    rw [Tim79.QuadModel.centralizer_iff (h.conj g).reg hZQC he hy]
    have h3 := (M₁.comm_iff_B (h.conj g).reg hy hzQ).mp
      (commutatorElement_eq_one_iff_mul_comm.mp h2)
    rw [hs₁, map_smul, smul_eq_mul] at h3
    exact (mul_eq_zero.mp h3).resolve_left hs₁0
  refine ⟨y, ?_, h1⟩
  rw [hC.QB_inf_M_eq]
  exact ⟨hQC ▸ hy, hyZ⟩

private theorem Ctx.orthLe_comm_of_comm_conj (hc : Ctx M Q Z B) (hO : OrthLe M B) {s m' : G}
    (hs : s ∈ M) (hm' : m' ∈ M) (h1 : ∀ x ∈ conjSubgroup s B, ∀ y ∈ B, x * y = y * x)
    (h2 : ∀ x ∈ conjSubgroup s B, ∀ y ∈ conjSubgroup m' B, x * y = y * x) :
    ∀ x ∈ conjSubgroup m' B, ∀ y ∈ B, x * y = y * x := by
  have hB1 := hc.conj_of_mem hs
  have hO1 := hO.conj hs
  have eB : conjSubgroup s⁻¹ (conjSubgroup s B) = B := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have eD : conjSubgroup (m' * s⁻¹) (conjSubgroup s B) = conjSubgroup m' B := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hBle : B ≤ QB (conjSubgroup s B) := by
    have := hO1 s⁻¹ (M.inv_mem hs) (by rw [eB]; exact fun x hx y hy => (h1 y hy x hx).symm)
    rwa [eB] at this
  have hDle : conjSubgroup m' B ≤ QB (conjSubgroup s B) := by
    have := hO1 (m' * s⁻¹) (M.mul_mem hm' (M.inv_mem hs))
      (by rw [eD]; exact fun x hx y hy => (h2 y hy x hx).symm)
    rwa [eD] at this
  intro x hx y hy
  exact elemAbelian_mul_comm hB1.inf_QB_elemAbelian ⟨(hc.conj_of_mem hm').le hx, hDle hx⟩
    ⟨hc.le hy, hBle hy⟩

private theorem Ctx.orthLe_comm_conj_of_not_le (hc : Ctx M Q Z B) (hO : OrthLe M B) {m : G}
    (hm : m ∈ M) (hcomm : ∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x)
    (hnot : ¬ conjSubgroup m B ≤ B ⊔ Z) {m' : G} (hm' : m' ∈ M) :
    ∀ x ∈ conjSubgroup m' B, ∀ y ∈ B, x * y = y * x := by
  have hC := hc.conj_of_mem hm
  have hD := hc.conj_of_mem hm'
  have hne : B ≠ conjSubgroup m B := fun h => hnot (by rw [← h]; exact le_sup_left)
  have hBC : B ≤ QB (conjSubgroup m B) :=
    (hc.hyp.le_QB_iff_le_QB hc.conj hC.conj hne).mpr (hO m hm hcomm)
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, -, hBl, hBc, -⟩ := hc.dictB h
  obtain ⟨c, -, -, hCl, -, -⟩ := hC.dictB h
  obtain ⟨d, -, -, -, hDc, -⟩ := hD.dictB h
  have hcb : ∀ s : GaloisField 2 n, c ≠ s • b := by
    intro s hs
    apply hnot
    intro x hx
    have hxQ := hC.le hx
    obtain ⟨t, ht⟩ := (hCl _).mp (M₀.pi_mem_img hx hxQ)
    refine (M₀.mem_img_iff (S := B ⊔ Z) le_sup_right hxQ).mp
      (M₀.img_mono le_sup_left ((hBl _).mpr ⟨t * s, ?_⟩))
    rw [ht, hs, smul_smul]
  have hind : ∀ s t : GaloisField 2 n, s • b = t • c → s = 0 := by
    intro s t hst
    by_contra hs
    by_cases ht : t = 0
    · rw [ht, zero_smul, smul_eq_zero] at hst
      exact hb0 (hst.resolve_left hs)
    · apply hcb (t⁻¹ * s)
      rw [mul_smul, hst, smul_smul, inv_mul_cancel₀ ht, one_smul]
  obtain ⟨c₀, hc₀C, hc₀Q, hc₀⟩ := (hCl c).mpr ⟨1, (one_smul _ c).symm⟩
  have hcb0 : M₀.B c b = 0 := by
    rw [← hc₀]
    exact (hBc c₀ hc₀Q).mp
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm c₀ hc₀C y hy).symm)
  by_cases hβ : M₀.B c d = 0
  ·
    refine hc.orthLe_comm_of_comm_conj hO hm hm' hcomm fun x hx y hy => ?_
    have hxQ := hC.le hx
    obtain ⟨t, ht⟩ := (hCl _).mp (M₀.pi_mem_img hx hxQ)
    have : x ∈ Subgroup.centralizer (conjSubgroup m' B : Set G) := by
      rw [hDc x hxQ, ht, map_smul, LinearMap.smul_apply, hβ, smul_zero]
    exact (Subgroup.mem_centralizer_iff.mp this y hy).symm
  ·
    set α := M₀.B b d
    set β := M₀.B c d
    obtain ⟨b', hb'B, hb'Q, hb'⟩ := (hBl (β • b)).mpr ⟨β, rfl⟩
    obtain ⟨c', hc'C, hc'Q, hc'⟩ := (hCl ((-α) • c)).mpr ⟨-α, rfl⟩
    have hb'ZC : b' ∉ Z ⊔ conjSubgroup m B := by
      intro hmem
      rw [sup_comm] at hmem
      have hCN : conjSubgroup m B ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
        hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hC.le hu))
      obtain ⟨u, hu, z, hz, huz⟩ := exists_mul_of_mem_sup_of_le_normalizer hCN hmem
      obtain ⟨t, ht⟩ := (hCl _).mp (M₀.pi_mem_img hu (hC.le hu))
      apply hβ
      apply hind β t
      rw [← hb', ← huz, M₀.π_mul _ (hC.le hu) _ (hc.Z_le_Q hz),
        (M₀.π_ker z (hc.Z_le_Q hz)).mpr hz, add_zero, ht]
    obtain ⟨s, hs, hsb⟩ := hC.exists_mem_QB_M_comm_eq (hBC hb'B) hb'ZC hc'C
    have hy : b' * c' ∈ conjSubgroup s B := by
      rw [mem_conjSubgroup]
      have e : s * b' * s⁻¹ = c' * b' := by rw [← hsb, commutatorElement_def]; group
      have e2 : c' * b' = b' * c' := hcomm c' hc'C b' hb'B
      have : s⁻¹ * (b' * c') * s = b' := by rw [← e2, ← e]; group
      rw [this]
      exact hb'B
    have hB1 := hc.conj_of_mem hs.2
    obtain ⟨e1, -, -, hB1l, -, -⟩ := hB1.dictB h
    have hyQ : b' * c' ∈ Q := Q.mul_mem hb'Q hc'Q
    have hπy : M₀.π (b' * c') = β • b + (-α) • c := by
      rw [M₀.π_mul _ hb'Q _ hc'Q, hb', hc']
    have hπy0 : M₀.π (b' * c') ≠ 0 := by
      rw [hπy]
      intro h0
      apply hβ
      apply hind β α
      rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
      exact h0
    obtain ⟨t, ht⟩ := (hB1l _).mp (M₀.pi_mem_img hy hyQ)
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hπy0 (by rw [ht, zero_smul])
    have hmul : ∀ x ∈ conjSubgroup s B, ∃ r : GaloisField 2 n,
        M₀.π x = r • M₀.π (b' * c') := by
      intro x hx
      obtain ⟨r, hr⟩ := (hB1l _).mp (M₀.pi_mem_img hx (hB1.le hx))
      exact ⟨r * t⁻¹, by rw [hr, ht, smul_smul, mul_assoc, inv_mul_cancel₀ ht0, mul_one]⟩
    have hpb : M₀.B (M₀.π (b' * c')) b = 0 := by
      rw [hπy, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smul,
        LinearMap.smul_apply, M₀.alt, hcb0, smul_zero, smul_zero, add_zero]
    have hpd : M₀.B (M₀.π (b' * c')) d = 0 := by
      rw [hπy, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    refine hc.orthLe_comm_of_comm_conj hO hs.2 hm' (fun x hx y hy => ?_) (fun x hx y hy => ?_)
    · obtain ⟨r, hr⟩ := hmul x hx
      have : x ∈ Subgroup.centralizer (B : Set G) := by
        rw [hBc x (hB1.le hx), hr, map_smul, LinearMap.smul_apply, hpb, smul_zero]
      exact (Subgroup.mem_centralizer_iff.mp this y hy).symm
    · obtain ⟨r, hr⟩ := hmul x hx
      have : x ∈ Subgroup.centralizer (conjSubgroup m' B : Set G) := by
        rw [hDc x (hB1.le hx), hr, map_smul, LinearMap.smul_apply, hpd, smul_zero]
      exact (Subgroup.mem_centralizer_iff.mp this y hy).symm

theorem Ctx.conj_le_sup_Z_of_orthLe (hc : Ctx M Q Z B) (hO : OrthLe M B) {m : G} (hm : m ∈ M)
    (hcomm : ∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) : conjSubgroup m B ≤ B ⊔ Z := by
  by_contra hnot
  refine hc.not_commutative_genB (orthLe_comm_iSup_of_pairwise fun m₁ hm₁ m₂ hm₂ => ?_)
  have hB₂ := hc.conj_of_mem hm₂
  have hk : m₂ * m * m₂⁻¹ ∈ M := M.mul_mem (M.mul_mem hm₂ hm) (M.inv_mem hm₂)
  have e1 : conjSubgroup (m₂ * m * m₂⁻¹) (conjSubgroup m₂ B) =
      conjSubgroup m₂ (conjSubgroup m B) := by
    rw [← conjSubgroup_mul, ← conjSubgroup_mul, inv_mul_cancel_right]
  have e2 : conjSubgroup (m₁ * m₂⁻¹) (conjSubgroup m₂ B) = conjSubgroup m₁ B := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hcomm₂ : ∀ x ∈ conjSubgroup (m₂ * m * m₂⁻¹) (conjSubgroup m₂ B),
      ∀ y ∈ conjSubgroup m₂ B, x * y = y * x := by
    rw [e1]
    exact orthLe_comm_conj hcomm m₂
  have hnot₂ : ¬ conjSubgroup (m₂ * m * m₂⁻¹) (conjSubgroup m₂ B) ≤ conjSubgroup m₂ B ⊔ Z := by
    rw [e1]
    intro hle
    apply hnot
    have : conjSubgroup m₂ (conjSubgroup m B) ≤ conjSubgroup m₂ (B ⊔ Z) := by
      rwa [conjSubgroup_sup', hc.conj_Z_eq hm₂]
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj m₂).injective).mp this
  have := hB₂.orthLe_comm_conj_of_not_le (hO.conj hm₂) hk hcomm₂ hnot₂
    (M.mul_mem hm₁ (M.inv_mem hm₂))
  rwa [e2] at this

end CFSG.RankThree.GF2n.Stroth80
