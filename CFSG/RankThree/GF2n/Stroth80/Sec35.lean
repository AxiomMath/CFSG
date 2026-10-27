module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec33

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_mem_Z_of_normalizes (hc : Ctx M Q Z B) {x : G} (hxM : x ∈ M)
    (hxc : ∀ z ∈ Z, x * z * x⁻¹ = z) (hx2 : x ^ 2 ∈ Q)
    (hxV : ∀ u ∈ B, x * u * x⁻¹ ∈ (B ⊔ Z : Subgroup G)) : ∀ u ∈ B, ⁅x, u⁆ ∈ Z := by
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  obtain ⟨T, hTπ, hTQ, hTB⟩ := h.linear_of_centralizes hxM hxc
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hxM) y).mp hy
  have hT2 : ∀ e, T (T e) = e := by
    intro e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    rw [← hTπ y hyQ, ← hTπ _ (hxQ y hyQ)]
    have : x * (x * y * x⁻¹) * x⁻¹ = x ^ 2 * y * (x ^ 2)⁻¹ := by rw [pow_two]; group
    rw [this, Tim79.QuadModel.pi_conj_self (M₀ := M₀) hx2 hyQ]
  have hle : (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := by
    refine sup_le (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩) (fun z hz => ?_)
    refine ⟨h.reg.V_le hz, ?_⟩
    rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  have himg : ∀ u ∈ B, M₀.π (x * u * x⁻¹) ∈ M₀.img B := fun u hu => (hle (hxV u hu)).2
  obtain ⟨u₀, hu₀B, hu₀Q, hu₀⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
  have hTbB : T b ∈ M₀.img B := by
    rw [← hu₀, ← hTπ u₀ hu₀Q]
    exact himg u₀ hu₀B
  obtain ⟨lam, hTb⟩ := (hB _).mp hTbB
  have hlam2 : lam * lam = 1 := by
    have h1 : T (T b) = b := hT2 b
    rw [hTb, map_smul, hTb, smul_smul] at h1
    have h2 : (lam * lam - 1) • b = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hb0
  have hlam1 : lam = 1 := by
    have h2 : (2 : GaloisField 2 m) = 0 := CharTwo.two_eq_zero
    have h3 : (lam - 1) * (lam - 1) = 0 := by
      linear_combination hlam2 + (1 - lam) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  intro u hu
  obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hu (hc.le hu))
  have hxu : x * u * x⁻¹ ∈ Q := hxQ u (hc.le hu)
  refine (M₀.comm_mem_iff (hc.le hu) hxu).mpr ?_
  rw [hTπ u (hc.le hu), hs, map_smul, hTb, hlam1, one_smul]

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_normalizer {H K : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  set L := H ⊔ K with hL
  have : (K.subgroupOf L).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  have hx' : (⟨x, hx⟩ : L) ∈ H.subgroupOf L ⊔ K.subgroupOf L := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨y, hy, z, hz, congrArg Subtype.val hyz⟩

theorem Ctx.exists_mul_of_mem_LB (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B) :
    ∃ s ∈ QB B ⊓ M, ∃ y ∈ Q, a = s * y := by
  have hnorm : QB B ⊓ M ≤ Subgroup.normalizer (Q : Set G) := fun x hx => hc.hyp.Q_normal.2 hx.2
  have ha' : a ∈ (QB B ⊓ M) ⊔ Q := by
    unfold LB at ha
    rwa [sup_comm] at ha
  obtain ⟨s, hs, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm ha'
  exact ⟨s, hs, y, hy, rfl⟩

theorem Ctx.sq_mem_Q_of_mem_LB (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B) : a ^ 2 ∈ Q := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB ha
  obtain ⟨g, hg⟩ := hc.conj
  have hsQB : s ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hs.1
  have hs2 : s ^ 2 ∈ Q := hc.le (hg ▸ hc.hyp.toHyp79.sq_mem_conj g hsQB)
  have hsy : s * y * s⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hs.2) y).mp hy
  have e : (s * y) ^ 2 = (s * y * s⁻¹) * s ^ 2 * y := by rw [pow_two, pow_two]; group
  rw [e]
  exact Q.mul_mem (Q.mul_mem hsy hs2) hy

theorem Ctx.conj_Z_of_mem_Q (hc : Ctx M Q Z B) {x z : G} (hx : x ∈ Q) (hz : z ∈ Z) :
    x * z * x⁻¹ = z := by
  have := hc.hyp.toHyp79.V_central hz hx
  rw [← this]
  group

theorem Ctx.LB_centralizes_Z (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B) :
    ∀ z ∈ Z, a * z * a⁻¹ = z := by
  intro z hz
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB ha
  have h1 := hc.conj_Z_of_mem_Q hy hz
  have h2 : s * z * s⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp (hc.QB_inf_M_le hs) z hz
    rw [← this]
    group
  calc s * y * z * (s * y)⁻¹ = s * (y * z * y⁻¹) * s⁻¹ := by group
    _ = z := by rw [h1, h2]

theorem Ctx.comm_B_mem_Z (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {u : G} (hu : u ∈ B) :
    ⁅t, u⁆ ∈ Z := by
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB ht
  have hsQB : s ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hs.1
  have hu' : u ∈ conjSubgroup g Z := hg ▸ hu
  have h1 : s * u = u * s := (hc.hyp.toHyp79.conj_central g hu' hsQB).symm
  have h2 : ⁅y, u⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy (hc.le hu)
  have h3 : s * ⁅y, u⁆ * s⁻¹ ∈ Z := by
    have hsN : s ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 hs.2
    simpa using (Subgroup.mem_normalizer_iff.mp hsN _).mp h2
  have e : ⁅s * y, u⁆ = s * ⁅y, u⁆ * s⁻¹ * ⁅s, u⁆ := by
    simp only [commutatorElement_def]; group
  have e2 : ⁅s, u⁆ = 1 := by
    rw [commutatorElement_def, h1]; group
  rw [e, e2, mul_one]
  exact h3

@[expose] def CQtGrp (hc : Ctx M Q Z B) (S : Subgroup G) : Subgroup G where
  carrier := CQt Q Z S
  mul_mem' := by
    rintro a b ⟨ha, hat⟩ ⟨hb, hbt⟩
    refine ⟨Q.mul_mem ha hb, fun t ht => ?_⟩
    have e : ⁅t, a * b⁆ = ⁅t, a⁆ * (a * ⁅t, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, hc.conj_Z_of_mem_Q ha (hbt t ht)]
    exact Z.mul_mem (hat t ht) (hbt t ht)
  one_mem' := ⟨Q.one_mem, fun t _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro a ⟨ha, hat⟩
    refine ⟨Q.inv_mem ha, fun t ht => ?_⟩
    have e : ⁅t, a⁻¹⁆ = a⁻¹ * ⁅t, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have h1 : a⁻¹ * ⁅t, a⁆⁻¹ * a = ⁅t, a⁆⁻¹ := by
      have := hc.conj_Z_of_mem_Q (Q.inv_mem ha) (Z.inv_mem (hat t ht))
      simpa [mul_assoc] using this
    rw [e, h1]
    exact Z.inv_mem (hat t ht)

theorem mem_CQtGrp {hc : Ctx M Q Z B} {S : Subgroup G} {x : G} :
    x ∈ CQtGrp hc S ↔ x ∈ CQt Q Z S := Iff.rfl

theorem Ctx.exists_conj_of_le_ZB (hc : Ctx M Q Z B) {B' : Subgroup G} (hc' : Ctx M Q Z B')
    (hle : B' ≤ Z ⊔ B) : ∃ p ∈ Q, conjSubgroup p B = B' := by
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨g', hg'⟩ := hc'.conj
  have hgV : conjSubgroup g Z ≠ Z := by rw [← hg]; exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by rw [← hg]; exact hc.le
  have h := hc.hyp.toHyp79.toHyp218 hgV hgQ
  obtain ⟨y, hy⟩ := h.exists_isOpp
  have hU : B ∈ Tim78.classIn Z (Z ⊔ conjSubgroup g Z) :=
    ⟨⟨g, hg⟩, by rw [← hg]; exact le_sup_right⟩
  have hU' : B' ∈ Tim78.classIn Z (Z ⊔ conjSubgroup g Z) :=
    ⟨⟨g', hg'⟩, by rw [← hg]; exact hle⟩
  obtain ⟨p, hp, hpe⟩ := h.exists_conj_eq hy hU hc.ne hU' hc'.ne
  exact ⟨p, (inf_le_left : Q ⊓ _ ≤ Q) hp, hpe⟩

theorem Ctx.no_involution_CQt (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) :
    ¬ ∃ x ∈ CQt Q Z (LB M Q B), x ∉ (B ⊔ Z : Subgroup G) ∧ x ^ 2 = 1 := by
  rcases stroth_3_1 hc hw hn with h | ⟨a, ha, hA⟩
  · exact h
  · exact absurd hA (hno a ha)

theorem Ctx.CQt_eq_of_3_4 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (h34 : Conc34 M Q Z B) :
    CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) := by
  have h31 := hc.no_involution_CQt hw hn hno
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have hBZle : (B ⊔ Z : Subgroup G) ≤ CQtGrp hc (LB M Q B) := by
    refine sup_le (fun u hu => ⟨hc.le hu, fun t ht => hc.comm_B_mem_Z ht hu⟩)
      (fun z hz => ⟨hc.hyp.Z_normal.1 hz, fun t ht => ?_⟩)
    have := hc.LB_centralizes_Z ht z hz
    have e : ⁅t, z⁆ = 1 := by rw [commutatorElement_def, this]; group
    rw [e]
    exact Z.one_mem
  have hle : (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := by
    refine sup_le (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩) (fun z hz => ?_)
    refine ⟨h.reg.V_le hz, ?_⟩
    rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  ext x
  constructor
  · rintro ⟨hxQ, hxt⟩
    have hxG : x ∈ CQtGrp hc (LB M Q B) := ⟨hxQ, hxt⟩
    have hxC : x ∈ Subgroup.centralizer (B : Set G) := by
      by_contra hxC
      have hlam : M₀.B (M₀.π x) b ≠ 0 := fun h0 => hxC ((hcent x hxQ).mpr h0)
      set lam := M₀.B (M₀.π x) b with hlamdef
      set c : GaloisField 2 m := M₀.Qf (M₀.π x) / lam with hcdef
      obtain ⟨u, huB, huQ, hu⟩ : c • b ∈ M₀.img B := (hB _).mpr ⟨c, rfl⟩
      have hx'G : x * u ∈ CQtGrp hc (LB M Q B) :=
        (CQtGrp hc (LB M Q B)).mul_mem hxG (hBZle (Subgroup.mem_sup_left huB))
      have hx'Q : x * u ∈ Q := hx'G.1
      have hπ : M₀.π (x * u) = M₀.π x + c • b := by rw [M₀.π_mul x hxQ u huQ, hu]
      have hQf : M₀.Qf (M₀.π (x * u)) = 0 := by
        rw [hπ, M₀.Qf_add, M₀.Qf_smul, hbs, map_smul, smul_eq_mul]
        have h2 : (2 : GaloisField 2 m) = 0 := CharTwo.two_eq_zero
        have h3 : c * lam = M₀.Qf (M₀.π x) := by
          rw [hcdef, div_mul_cancel₀ _ hlam]
        rw [← hlamdef, h3]
        linear_combination (M₀.Qf (M₀.π x)) * h2
      have hx2 : (x * u) ^ 2 = 1 := (M₀.sq_iff_Qf h.reg hx'Q).mpr hQf
      have hnot : x * u ∉ (B ⊔ Z : Subgroup G) := by
        intro hmem
        obtain ⟨s, hs⟩ := (hB _).mp (hle hmem).2
        have h1 : M₀.B (M₀.π (x * u)) b = 0 := by
          rw [hs, map_smul, LinearMap.smul_apply, M₀.alt, smul_zero]
        rw [hπ, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, M₀.alt, smul_zero,
          add_zero] at h1
        exact hlam h1
      exact h31 ⟨x * u, hx'G, hnot, hx2⟩
    have hX : Subgroup.zpowers x ≤ Q ⊓ Subgroup.centralizer (B : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hxQ, hxC⟩
    have hXG : Subgroup.zpowers x ≤ CQtGrp hc (LB M Q B) := Subgroup.zpowers_le.mpr hxG
    have hmain := h34 _ hX (fun y hy t ht => (le_sup_right : Z ≤ B ⊔ Z) ((hXG hy).2 t ht))
      (Subgroup.mem_zpowers x)
    by_contra hnot
    exact h31 ⟨x, ⟨hxQ, hxt⟩, hnot, hc.inf_QB_elemAbelian.2 x hmain⟩
  · intro hx
    exact hBZle hx

theorem Ctx.card_of_3_3 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 1 ≤ n)
    (hno : NoA2 Q Z (LB M Q B))
    (h33 : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) ∨
      ∃ a ∈ LB M Q B, IsA2 Q Z a) :
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) ∧
      Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := by
  rcases h33 with h | ⟨a, ha, hA⟩
  · refine ⟨h, ?_⟩
    have hmul := hc.card_LB_mul hw
    rw [h] at hmul
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have h1 : Nat.card Z ^ (n - 1) * Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (2 * n) := by
      have := hmul
      rw [mul_assoc] at this
      exact Nat.eq_of_mul_eq_mul_left hQpos this
    have h2 : Nat.card Z ^ (2 * n) = Nat.card Z ^ (n - 1) * Nat.card Z ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos _) h1
  · exact absurd hA (hno a ha)

theorem Ctx.noA2_conj (hc : Ctx M Q Z B) (hno : NoA2 Q Z (LB M Q B)) {m : G} (hm : m ∈ M) :
    NoA2 Q Z (LB M Q (conjSubgroup m B)) := by
  intro a' ha' hA
  rw [hc.LB_conj hm] at ha'
  have h1 := mem_conjSubgroup.mp ha'
  have h2 := IsA2.conj hA m⁻¹
  rw [hc.conj_Q_eq (M.inv_mem hm), hc.conj_Z_eq (M.inv_mem hm), inv_inv] at h2
  exact hno _ h1 h2

theorem Ctx.card_sup_Z (hc : Ctx M Q Z B) :
    Nat.card ↥(B ⊔ Z : Subgroup G) = Nat.card B * Nat.card Z := by
  have hEN : Z ≤ Subgroup.normalizer (B : Set G) := by
    intro z hz
    refine Subgroup.mem_normalizer_fintype fun h hh => ?_
    have := hc.hyp.toHyp79.V_central hz (hc.le hh)
    rwa [this, mul_inv_cancel_right]
  have h := card_sup_mul_card_inf_of_le_normalizer hEN
  rw [inf_comm, hc.inf_eq_bot, Subgroup.card_bot, mul_one] at h
  exact h

theorem Ctx.conj_mem_CQt (hc : Ctx M Q Z B) {a : G} (haM : a ∈ M)
    (haL : a ∈ Subgroup.normalizer (LB M Q B : Set G)) {u : G}
    (hu : u ∈ CQt Q Z (LB M Q B)) : a * u * a⁻¹ ∈ CQt Q Z (LB M Q B) := by
  obtain ⟨huQ, hut⟩ := hu
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haM) u).mp huQ, fun t ht => ?_⟩
  have ht' : a⁻¹ * t * a ∈ LB M Q B := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haL) t).mp ht
    simpa using this
  have e : ⁅t, a * u * a⁻¹⁆ = a * ⁅a⁻¹ * t * a, u⁆ * a⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : ⁅a⁻¹ * t * a, u⁆ ∈ Z := hut _ ht'
  have haZ : a ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 haM
  simpa using (Subgroup.mem_normalizer_iff.mp haZ _).mp h1

theorem Ctx.weaklyClosed_of_3_4 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (h34 : ∀ m ∈ M, Conc34 M Q Z (conjSubgroup m B)) {m : G}
    (hm : m ∈ M) (hmN : conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G)) :
    conjSubgroup m (LB M Q B) = LB M Q B := by
  have hc' := hc.conj_of_mem hm
  have hno' := hc.noA2_conj hno hm
  have hCQ : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    hc.CQt_eq_of_3_4 hw hn hno (by simpa [conjSubgroup_one] using h34 1 M.one_mem)
  have hCQ' := hc'.CQt_eq_of_3_4 hw hn hno' (h34 m hm)
  have hBle : ∀ a ∈ LB M Q (conjSubgroup m B), ∀ u ∈ B, a * u * a⁻¹ ∈ (B ⊔ Z : Subgroup G) := by
    intro a ha u hu
    have haL : a ∈ Subgroup.normalizer (LB M Q B : Set G) := hmN (by rwa [← hc.LB_conj hm])
    have haM : a ∈ M := hc'.LB_le_M ha
    have huC : u ∈ CQt Q Z (LB M Q B) := by
      rw [hCQ]; exact Subgroup.mem_sup_left hu
    have := hc.conj_mem_CQt haM haL huC
    rw [hCQ] at this
    exact this
  have hBZ : ∀ a ∈ LB M Q (conjSubgroup m B), ∀ u ∈ B, ⁅a, u⁆ ∈ Z := fun a ha =>
    hc.comm_mem_Z_of_normalizes (hc'.LB_le_M ha) (hc'.LB_centralizes_Z ha)
      (hc'.sq_mem_Q_of_mem_LB ha) (hBle a ha)
  have hBsub : B ≤ CQtGrp hc' (LB M Q (conjSubgroup m B)) := fun u hu => ⟨hc.le hu, fun t ht =>
    hBZ t ht u hu⟩
  have hBle' : B ≤ conjSubgroup m B ⊔ Z := by
    intro u hu
    have := hBsub hu
    rw [mem_CQtGrp, hCQ'] at this
    exact this
  have hZB : (conjSubgroup m B ⊔ Z : Subgroup G) = B ⊔ Z := by
    have hle1 : (B ⊔ Z : Subgroup G) ≤ conjSubgroup m B ⊔ Z := sup_le hBle' le_sup_right
    exact (Subgroup.eq_of_le_of_card_ge hle1 (by
      rw [hc'.card_sup_Z, hc.card_sup_Z, card_conjSubgroup])).symm
  have hB'le : conjSubgroup m B ≤ Z ⊔ B := by
    rw [sup_comm, ← hZB]
    exact le_sup_left
  obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB hc' hB'le
  have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
  have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
  rw [← hc.LB_conj hm, ← hpB, hc.LB_conj hpM, hLp]

theorem stroth_3_5_of_3_3_3_4 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (h33 : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) ∨
      ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h34 : ∀ m ∈ M, Conc34 M Q Z (conjSubgroup m B)) :
    (∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) →
        conjSubgroup m (LB M Q B) = LB M Q B) ∧
    CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) ∧
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) ∧
    Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := by
  have h34B : Conc34 M Q Z B := by simpa [conjSubgroup_one] using h34 1 M.one_mem
  obtain ⟨hcard1, hcard2⟩ := hc.card_of_3_3 hw (by omega) hno h33
  exact ⟨fun m hm hmN => hc.weaklyClosed_of_3_4 hw hn hno h34 hm hmN,
    hc.CQt_eq_of_3_4 hw hn hno h34B, hcard1, hcard2⟩

theorem stroth_3_5_of_3_4 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (h34 : ∀ m ∈ M, Conc34 M Q Z (conjSubgroup m B)) :
    (∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) →
        conjSubgroup m (LB M Q B) = LB M Q B) ∧
    CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) ∧
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) ∧
    Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
  stroth_3_5_of_3_3_3_4 hc hw hn hno (stroth_3_3 hc hw (by omega)) h34

theorem Ctx.mem_normalizer_LB_iff (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {a : G} (haM : a ∈ M) :
    a ∈ Subgroup.normalizer (LB M Q B : Set G) ↔
      a ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  constructor
  · intro haL
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxC : x ∈ CQt Q Z (LB M Q B) := by rw [h35]; exact hx
    have := hc.conj_mem_CQt haM haL hxC
    rw [h35] at this
    exact this
  · intro haV
    have hc' := hc.conj_of_mem haM
    have hVa : conjSubgroup a (B ⊔ Z : Subgroup G) = B ⊔ Z := conjSubgroup_eq_self_iff.mpr haV
    have hle : conjSubgroup a B ≤ Z ⊔ B := by
      have h1 : conjSubgroup a B ≤ conjSubgroup a (B ⊔ Z : Subgroup G) :=
        Subgroup.map_mono le_sup_left
      rw [hVa, sup_comm] at h1
      exact h1
    obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB hc' hle
    have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
    have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
    have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
    refine conjSubgroup_eq_self_iff.mp ?_
    rw [← hc.LB_conj haM, ← hpB, hc.LB_conj hpM, hLp]

@[expose] def Conc34' (M Q Z B : Subgroup G) : Prop :=
  ∀ t ∈ QB B ⊓ M, (∀ y ∈ Q ⊓ Subgroup.centralizer (B : Set G), ⁅t, y⁆ ∈ (B ⊔ Z : Subgroup G)) →
    t ∈ Q

theorem Ctx.conc34_of_star (hc : Ctx M Q Z B) (h : Conc34' M Q Z B) : Conc34 M Q Z B := by
  obtain ⟨n, h1, h2, h3, h4⟩ := hc.exists_swap'
  have hinv : ∀ (S : Subgroup G), conjSubgroup n⁻¹ (conjSubgroup n S) = S := fun S => by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hQ' : conjSubgroup n⁻¹ Q = QB B := by rw [← h2, hinv]
  have hZ' : conjSubgroup n⁻¹ B = Z := by rw [← h3, hinv]
  have hB' : conjSubgroup n⁻¹ Z = B := by rw [← h4, hinv]
  have hQB' : conjSubgroup n⁻¹ (QB B) = Q := by rw [← h1, hinv]
  intro X hX hXL x hx
  have hxQ : x ∈ Q := (hX hx).1
  have hxC : x ∈ Subgroup.centralizer (B : Set G) := (hX hx).2
  refine ⟨hxQ, ?_⟩
  have hCmem : n * x * n⁻¹ ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := by
    rw [← hc.conj_centralizer_B h1 h4]
    exact ⟨x, hX hx, by simp [MulAut.conj_apply]⟩
  have htM : n * x * n⁻¹ ∈ QB B ⊓ M := by rw [hc.QB_inf_M_eq]; exact hCmem
  have hstar := h _ htM (fun y' hy' => by
    have hy : n⁻¹ * y' * n ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := by
      rw [← hZ', ← hQ', ← conjSubgroup_centralizer, ← conjSubgroup_inf]
      exact ⟨y', hy', by simp [MulAut.conj_apply]⟩
    have hyL : n⁻¹ * y' * n ∈ LB M Q B := hc.L0_le_LB hy
    have h5 : ⁅n⁻¹ * y' * n, x⁆ ∈ (B ⊔ Z : Subgroup G) := hXL x hx _ hyL
    have h6 : ⁅y', n * x * n⁻¹⁆ = n * ⁅n⁻¹ * y' * n, x⁆ * n⁻¹ := by
      simp only [commutatorElement_def]; group
    have h7 : n * ⁅n⁻¹ * y' * n, x⁆ * n⁻¹ ∈ (Z ⊔ B : Subgroup G) := by
      have : n * ⁅n⁻¹ * y' * n, x⁆ * n⁻¹ ∈ conjSubgroup n (B ⊔ Z : Subgroup G) :=
        ⟨_, h5, by show (MulAut.conj n) _ = _; rw [MulAut.conj_apply]⟩
      rwa [conjSubgroup_sup', h3, h4] at this
    have h8 : ⁅n * x * n⁻¹, y'⁆ = ⁅y', n * x * n⁻¹⁆⁻¹ := (commutatorElement_inv _ _).symm
    rw [h8, h6]
    exact (B ⊔ Z : Subgroup G).inv_mem (by rwa [sup_comm] at h7))
  have hxQB : x ∈ conjSubgroup n⁻¹ Q := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hstar
  rwa [hQ'] at hxQB

end CFSG.RankThree.GF2n.Stroth80
