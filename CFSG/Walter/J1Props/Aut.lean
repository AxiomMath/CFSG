module

public import CFSG.Walter.J1Props.Multiplier

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word
open scoped Pointwise

@[expose] def wsWord : Word 5 :=
  wt ++ wn ++ wu ++ Word.inv wn ++ wm ++ wu ++ Word.inv wn ++ wt ++ wn ++ wm ++ wu ++ wn ++ wu ++
    Word.inv wn ++ wt

theorem sJ_eq : sJ = elt wsWord := by
  rw [elt_eq_elt_iff]
  decide +kernel

theorem exists_elt (g : walterJ1) : ∃ w : Word 5, elt w = g := by
  obtain ⟨g, hg⟩ := g
  rw [← toMat_range_eq] at hg
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨z.toWord, Subtype.ext ?_⟩
  have hz : (QuotientGroup.mk z : Pres .O1a) = ev PresentedGroup.of z.toWord := by
    rw [← presentedGroup_mk_eq_ev, FreeGroup.mk_toWord]
    rfl
  rw [coe_elt]
  change ev unit z.toWord = toMat (QuotientGroup.mk z)
  rw [hz, toMat_ev]

theorem elt_mem_closure (w : Word 5) : elt w ∈ Subgroup.closure {tJ, nJ, mJ, uJ} := by
  set C := Subgroup.closure ({tJ, nJ, mJ, uJ} : Set walterJ1)
  have hgen : ∀ i : Fin 5, elt (gen i) ∈ C := by
    intro i
    fin_cases i
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
    · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
    · change sJ ∈ C
      rw [sJ_eq]
      have h1 : tJ ∈ C := Subgroup.subset_closure (by simp)
      have h2 : nJ ∈ C := Subgroup.subset_closure (by simp)
      have h3 : mJ ∈ C := Subgroup.subset_closure (by simp)
      have h4 : uJ ∈ C := Subgroup.subset_closure (by simp)
      simp only [wsWord, elt_append, elt_inv]
      exact C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem
        (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem h1 h2) h4)
        (C.inv_mem h2)) h3) h4) (C.inv_mem h2)) h1) h2) h3) h4) h2) h4) (C.inv_mem h2)) h1
    · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))
  induction w with
  | nil => rw [elt_nil]; exact C.one_mem
  | cons l w ih =>
    rw [show l :: w = [l] ++ w from rfl, elt_append]
    refine C.mul_mem ?_ ih
    obtain ⟨i, b⟩ := l
    cases b with
    | true => exact hgen i
    | false =>
      rw [show ([(i, false)] : Word 5) = Word.inv (gen i) from rfl, elt_inv]
      exact C.inv_mem (hgen i)

theorem closure_tnmu : Subgroup.closure ({tJ, nJ, mJ, uJ} : Set walterJ1) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨w, rfl⟩ := exists_elt g
  exact elt_mem_closure w

theorem eq_one_of_fix {φ : MulAut walterJ1} (ht : φ tJ = tJ) (hn : φ nJ = nJ) (hm : φ mJ = mJ)
    (hu : φ uJ = uJ) : φ = 1 := by
  have h : Set.EqOn φ.toMonoidHom (MonoidHom.id walterJ1) ({tJ, nJ, mJ, uJ} : Set walterJ1) := by
    rintro x (rfl | rfl | rfl | rfl)
    exacts [ht, hn, hm, hu]
  have h2 := MonoidHom.eqOn_closure h
  rw [closure_tnmu] at h2
  exact MulEquiv.ext fun g => h2 (Set.mem_univ g)

theorem elems_S₀ {s : walterJ1} (hs : s ∈ S₀) :
    s = 1 ∨ s = tJ ∨ s = xJ ∨ s = x'J ∨ s = xJ * x'J ∨ s = tJ * xJ ∨ s = tJ * x'J ∨
      s = tJ * (xJ * x'J) := by
  have hle : Subgroup.zpowers tJ ≤ Subgroup.normalizer
      ((GorensteinWalter.kleinFourOfCommutingInvolutions xJ x'J rels_F.1 rels_F.2.1
        rels_F.2.2.2.1 : Subgroup walterJ1) : Set walterJ1) := by
    rw [Subgroup.zpowers_le]
    refine J1.mem_normalizer_of_conj_mem fun y hy => ?_
    have hc : ∀ z ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1), tJ * z * tJ⁻¹ = z := by
      have c1 := commute_tJ.1
      have c2 := commute_tJ.2.1
      rintro z (rfl | rfl | rfl | rfl)
      · calc tJ * (xJ * x'J) * tJ⁻¹ = (tJ * xJ) * (x'J * tJ⁻¹) := by group
          _ = (xJ * tJ) * (x'J * tJ⁻¹) := by rw [c1]
          _ = xJ * (tJ * x'J) * tJ⁻¹ := by group
          _ = xJ * (x'J * tJ) * tJ⁻¹ := by rw [c2]
          _ = xJ * x'J := by group
      · rw [← c1, mul_inv_cancel_right]
      · rw [← c2, mul_inv_cancel_right]
      · group
    rw [hc y hy]
    exact hy
  have hs' : s ∈ ((Subgroup.zpowers tJ : Set walterJ1) *
      ((GorensteinWalter.kleinFourOfCommutingInvolutions xJ x'J rels_F.1 rels_F.2.1
        rels_F.2.2.2.1 : Subgroup walterJ1) : Set walterJ1)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hs
  obtain ⟨a, ha, v, hv, rfl⟩ := Set.mem_mul.mp hs'
  rcases (J1.mem_zpowers_of_orderOf_eq_two orderOf_tJ).mp ha with rfl | rfl
  · change v ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1) at hv
    rw [one_mul]
    rcases hv with rfl | rfl | rfl | rfl <;> simp
  · change v ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1) at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp

theorem rels_aut : xJ * nJ ≠ nJ * xJ ∧ x'J * nJ ≠ nJ * x'J ∧ xJ * x'J * nJ ≠ nJ * (xJ * x'J) ∧
    tJ * nJ ≠ nJ * tJ ∧ tJ * xJ * nJ ≠ nJ * (tJ * xJ) ∧ tJ * x'J * nJ ≠ nJ * (tJ * x'J) ∧
    tJ * (xJ * x'J) * nJ ≠ nJ * (tJ * (xJ * x'J)) ∧
    mJ * tJ = tJ * mJ ∧ mJ⁻¹ * nJ * mJ = nJ ^ 2 ∧ mJ ^ 3 = 1 ∧ mJ * nJ * mJ⁻¹ = nJ ^ 4 ∧
    mJ * nJ ^ 2 * mJ⁻¹ = nJ ∧ mJ ^ 2 * nJ ^ 4 * (mJ ^ 2)⁻¹ = nJ := by
  simp only [ne_eq, ← elt_inv, ← elt_pow, ← elt_append, elt_eq_one_iff, elt_eq_elt_iff]
  decide +kernel

theorem eq_one_of_mem_S₀_of_commute {s : walterJ1} (hs : s ∈ S₀) (hsn : s * nJ = nJ * s) :
    s = 1 := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, -⟩ := rels_aut
  rcases elems_S₀ hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals exfalso
  exacts [r4 hsn, r1 hsn, r2 hsn, r3 hsn, r5 hsn, r6 hsn, r7 hsn]

theorem tJ_mem_S₀ : tJ ∈ S₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers tJ)

theorem t_mem_sylowS₀ : jankoHyp.t ∈ sylowS₀ := by
  rw [jankoHyp_t]
  exact tJ_mem_S₀

theorem S₀_mul_self {s : walterJ1} (hs : s ∈ S₀) : s * s = 1 :=
  (jankoHyp.sylow_structure sylowS₀).2.1 s hs

theorem S₀_comm {a b : walterJ1} (ha : a ∈ S₀) (hb : b ∈ S₀) : a * b = b * a :=
  congrArg Subtype.val ((hasAbelianSylowTwo sylowS₀).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem rels_m : mJ⁻¹ * tJ * mJ = tJ ∧ mJ⁻¹ * t2J * mJ = t3J ∧
    mJ⁻¹ * t3J * mJ = tJ * t2J * t3J := by
  simp only [← elt_inv, ← elt_append, elt_eq_elt_iff]
  decide +kernel

theorem xJ_mem_S₀ : xJ ∈ S₀ := Subgroup.mem_sup_right (show xJ ∈ ({xJ * x'J, xJ, x'J, 1} :
  Set walterJ1) by simp)

theorem x'J_mem_S₀ : x'J ∈ S₀ := Subgroup.mem_sup_right (show x'J ∈ ({xJ * x'J, xJ, x'J, 1} :
  Set walterJ1) by simp)

theorem S₀_eq_closure : S₀ = Subgroup.closure {tJ, t2J, t3J} := by
  obtain ⟨-, -, -, -, -, -, hx, hx'⟩ := rels_S
  refine le_antisymm S₀_le_closure ?_
  rw [Subgroup.closure_le]
  have h2 : t2J = tJ * xJ := by rw [hx, ← mul_assoc, tJ_mul_self, one_mul]
  have h3 : t3J = tJ * x'J := by rw [hx', ← mul_assoc, tJ_mul_self, one_mul]
  rintro y (rfl | rfl | rfl)
  · exact tJ_mem_S₀
  · rw [SetLike.mem_coe, h2]
    exact S₀.mul_mem tJ_mem_S₀ xJ_mem_S₀
  · rw [SetLike.mem_coe, h3]
    exact S₀.mul_mem tJ_mem_S₀ x'J_mem_S₀

theorem mem_normalizer_S₀ {g : walterJ1} (h1 : g⁻¹ * tJ * g ∈ S₀) (h2 : g⁻¹ * t2J * g ∈ S₀)
    (h3 : g⁻¹ * t3J * g ∈ S₀) : g ∈ Subgroup.normalizer (S₀ : Set walterJ1) := by
  suffices h : g⁻¹ ∈ Subgroup.normalizer (S₀ : Set walterJ1) by
    simpa using Subgroup.inv_mem _ h
  refine J1.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [inv_inv]
  rw [S₀_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl | rfl
    exacts [h1, h2, h3]
  | one => rw [mul_one, inv_mul_cancel]; exact S₀.one_mem
  | mul y z _ _ hy hz =>
    rw [show g⁻¹ * (y * z) * g = (g⁻¹ * y * g) * (g⁻¹ * z * g) by group]
    exact S₀.mul_mem hy hz
  | inv y _ hy =>
    rw [show g⁻¹ * y⁻¹ * g = (g⁻¹ * y * g)⁻¹ by group]
    exact S₀.inv_mem hy

theorem t2J_mem_S₀ : t2J ∈ S₀ := S₀_eq_closure ▸ Subgroup.subset_closure (by simp)

theorem t3J_mem_S₀ : t3J ∈ S₀ := S₀_eq_closure ▸ Subgroup.subset_closure (by simp)

theorem nJ_mem_normalizer : nJ ∈ Subgroup.normalizer (S₀ : Set walterJ1) := by
  obtain ⟨-, -, -, hn1, hn2, hn3, -, -⟩ := rels_S
  refine mem_normalizer_S₀ ?_ ?_ ?_
  · rw [hn1]; exact t2J_mem_S₀
  · rw [hn2]; exact t3J_mem_S₀
  · rw [hn3]; exact S₀.mul_mem tJ_mem_S₀ t3J_mem_S₀

theorem mJ_mem_normalizer : mJ ∈ Subgroup.normalizer (S₀ : Set walterJ1) := by
  obtain ⟨hm1, hm2, hm3⟩ := rels_m
  refine mem_normalizer_S₀ ?_ ?_ ?_
  · rw [hm1]; exact tJ_mem_S₀
  · rw [hm2]; exact t3J_mem_S₀
  · rw [hm3]; exact S₀.mul_mem (S₀.mul_mem tJ_mem_S₀ t2J_mem_S₀) t3J_mem_S₀

@[expose] def PresS (φ : MulAut walterJ1) : Prop := ∀ s, φ s ∈ S₀ ↔ s ∈ S₀

theorem presS_conj_mul {g : walterJ1} (hg : g ∈ Subgroup.normalizer (S₀ : Set walterJ1))
    {φ : MulAut walterJ1} (hφ : PresS φ) : PresS (MulAut.conj g * φ) := by
  intro s
  rw [MulAut.mul_apply, MulAut.conj_apply, ← hφ s]
  exact ((Subgroup.mem_normalizer_iff.mp hg) (φ s)).symm

theorem exists_conj_fix_t (φ : MulAut walterJ1) :
    ∃ g : walterJ1, (MulAut.conj g * φ) tJ = tJ ∧ PresS (MulAut.conj g * φ) := by
  set Q := S₀.map φ.toMonoidHom
  have hcard : Nat.card Q = 8 := by
    rw [Subgroup.card_map_of_injective φ.injective, card_S₀]
  have hP : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hidx : ¬ 2 ∣ Q.index := by
    have := Q.card_mul_index
    rw [hcard, card_walterJ1] at this
    omega
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq walterJ1 (hP.toSylow hidx) sylowS₀
  have hpres : PresS (MulAut.conj g₁ * φ) := by
    intro s
    have hmem : ∀ y : walterJ1, y ∈ S₀ ↔ g₁⁻¹ * y * g₁ ∈ Q := by
      intro y
      have : y ∈ ((g₁ • hP.toSylow hidx : Sylow 2 walterJ1) : Subgroup walterJ1) ↔ y ∈ S₀ := by
        rw [hg₁]
        exact Iff.rfl
      rw [← this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply]
      rfl
    have hsy : ∀ y : walterJ1, y ∈ ((sylowS₀ : Sylow 2 walterJ1) : Subgroup walterJ1) ↔ y ∈ S₀ :=
      fun y => Iff.rfl
    rw [hmem, MulAut.mul_apply, MulAut.conj_apply, show g₁⁻¹ * (g₁ * φ s * g₁⁻¹) * g₁ = φ s by
      group]
    exact Subgroup.mem_map_iff_mem φ.injective
  set φ₁ := MulAut.conj g₁ * φ
  have ht1 : φ₁ tJ ∈ S₀ := (hpres tJ).mpr tJ_mem_S₀
  have ht1' : φ₁ tJ ≠ 1 := by
    rw [Ne, map_eq_one_iff _ φ₁.injective]
    exact ne_one_F.2.2.2.2.2
  obtain ⟨h, hh, hht⟩ := jankoHyp.exists_conj_of_mem_sylow sylowS₀ t_mem_sylowS₀ ht1 ht1'
    tJ_mem_S₀ ne_one_F.2.2.2.2.2
  refine ⟨h * g₁, ?_, ?_⟩
  · rw [map_mul, mul_assoc, MulAut.mul_apply, MulAut.conj_apply]
    exact hht
  · rw [map_mul, mul_assoc]
    exact presS_conj_mul hh hpres

theorem card_K : Nat.card (S₀ ⊔ Subgroup.zpowers nJ : Subgroup walterJ1) = 56 := by
  have h7 : orderOf nJ = 7 := orderOf_yJ (p := 7) (by norm_num)
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (Subgroup.zpowers_le.mpr nJ_mem_normalizer), card_S₀, Nat.card_zpowers, h7]
  rw [Subgroup.disjoint_def]
  intro y hyS hyn
  have h1 : orderOf y ∣ 8 := card_S₀ ▸ Subgroup.orderOf_dvd_natCard _ hyS
  have h2 : orderOf y ∣ 7 := by
    have := Subgroup.orderOf_dvd_natCard _ hyn
    rwa [Nat.card_zpowers, h7] at this
  have : orderOf y ∣ Nat.gcd 8 7 := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 8 7 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

theorem mem_K_iff {y : walterJ1} :
    y ∈ (S₀ ⊔ Subgroup.zpowers nJ : Subgroup walterJ1) ↔ ∃ s ∈ S₀, ∃ k : ℤ, y = s * nJ ^ k := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (Subgroup.zpowers_le.mpr nJ_mem_normalizer), Set.mem_mul]
  constructor
  · rintro ⟨s, hs, z, ⟨k, rfl⟩, rfl⟩
    exact ⟨s, hs, k, rfl⟩
  · rintro ⟨s, hs, k, rfl⟩
    exact ⟨s, hs, nJ ^ k, ⟨k, rfl⟩, rfl⟩

theorem mJ_mem_normalizer_K :
    mJ ∈ Subgroup.normalizer ((S₀ ⊔ Subgroup.zpowers nJ : Subgroup walterJ1) : Set walterJ1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmn', -, -⟩ := rels_aut
  refine J1.mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨s, hs, k, rfl⟩ := mem_K_iff.mp hy
  refine mem_K_iff.mpr ⟨mJ * s * mJ⁻¹, ?_, 4 * k, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp mJ_mem_normalizer s).mp hs
  · rw [zpow_mul, zpow_ofNat, ← hmn', conj_zpow]
    group

theorem exists_S₀_conj (φ : MulAut walterJ1) (hφ : PresS φ) :
    ∃ s ∈ S₀, (MulAut.conj s * φ) nJ ∈ Subgroup.zpowers nJ := by
  set N := Subgroup.normalizer (S₀ : Set walterJ1)
  set K := (S₀ ⊔ Subgroup.zpowers nJ : Subgroup walterJ1)
  have h7 : orderOf nJ = 7 := orderOf_yJ (p := 7) (by norm_num)
  have hN : Nat.card N = 168 := jankoHyp.card_normalizer_sylow sylowS₀ t_mem_sylowS₀
  have hφn : φ nJ ∈ N := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_inv, ← map_mul, ← map_mul, hφ, hφ]
    exact (Subgroup.mem_normalizer_iff.mp nJ_mem_normalizer) y'
  have hKN : K ≤ N := sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr nJ_mem_normalizer)
  have hmK : Subgroup.zpowers mJ ≤ Subgroup.normalizer (K : Set walterJ1) :=
    Subgroup.zpowers_le.mpr mJ_mem_normalizer_K
  have hKm : Nat.card (K ⊔ Subgroup.zpowers mJ : Subgroup walterJ1) = 168 := by
    have h3 : orderOf mJ = 3 := orderOf_yJ (p := 3) (by norm_num)
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hmK, card_K,
      Nat.card_zpowers, h3]
    rw [Subgroup.disjoint_def]
    intro y hyK hym
    have h1 : orderOf y ∣ 56 := card_K ▸ Subgroup.orderOf_dvd_natCard _ hyK
    have h2 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard _ hym
      rwa [Nat.card_zpowers, h3] at this
    have : orderOf y ∣ Nat.gcd 56 3 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 56 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this
  have hNeq : K ⊔ Subgroup.zpowers mJ = N := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hKN (Subgroup.zpowers_le.mpr mJ_mem_normalizer))
      ?_
    rw [hN, hKm]
  have hNK : N ≤ Subgroup.normalizer (K : Set walterJ1) := by
    rw [← hNeq]
    exact sup_le Subgroup.le_normalizer hmK
  have hKn : (K.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hNK
  have hidx : (K.subgroupOf N).index = 3 := by
    have h := Subgroup.relIndex_mul_card K N
    rw [inf_eq_left.mpr hKN, card_K, hN] at h
    change (K.subgroupOf N).index = 3
    rw [← Subgroup.relIndex]
    omega
  have hφnK : φ nJ ∈ K := by
    have h := mem_of_pow_eq_one_of_coprime (K.subgroupOf N) (x := ⟨φ nJ, hφn⟩) (n := 7)
      (Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, orders_yJ.2.2.1, map_one]; rfl))
      (by rw [hidx]; norm_num)
    exact h
  obtain ⟨s₀, hs₀, k, hk⟩ := mem_K_iff.mp hφnK
  have hk1 : nJ ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hk
    have h2 : φ nJ * φ nJ = 1 := by rw [hk]; exact S₀_mul_self hs₀
    have : orderOf (φ nJ) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [MulEquiv.orderOf_eq, h7] at this
    norm_num at this
  have hnk : nJ ∈ Subgroup.zpowers (nJ ^ k) := by
    have hord : orderOf (nJ ^ k) = 7 := by
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hd : orderOf (nJ ^ k) ∣ 7 := orderOf_dvd_of_pow_eq_one (by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, orders_yJ.2.2.1,
          one_zpow])
      rcases (Nat.dvd_prime Fact.out).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hk1
      · exact h
    have hle : Subgroup.zpowers (nJ ^ k) ≤ Subgroup.zpowers nJ :=
      Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers nJ k)
    have heq : Subgroup.zpowers (nJ ^ k) = Subgroup.zpowers nJ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, h7])
    rw [heq]
    exact Subgroup.mem_zpowers nJ
  let μ : S₀ → S₀ := fun s => ⟨s * nJ ^ k * (s : walterJ1)⁻¹ * (nJ ^ k)⁻¹, by
    have : nJ ^ k * (s : walterJ1)⁻¹ * (nJ ^ k)⁻¹ ∈ S₀ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ nJ_mem_normalizer k) _).mp
        (S₀.inv_mem s.2)
    rw [show (s : walterJ1) * nJ ^ k * (s : walterJ1)⁻¹ * (nJ ^ k)⁻¹ =
      s * (nJ ^ k * (s : walterJ1)⁻¹ * (nJ ^ k)⁻¹) by group]
    exact S₀.mul_mem s.2 this⟩
  have hμ : Function.Injective μ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [μ] at h
    have hc : ((b : walterJ1)⁻¹ * a) * nJ ^ k = nJ ^ k * ((b : walterJ1)⁻¹ * a) := by
      have h' : (a : walterJ1) * nJ ^ k * (a : walterJ1)⁻¹ = b * nJ ^ k * (b : walterJ1)⁻¹ := by
        have := congrArg (· * nJ ^ k) h
        simpa only [inv_mul_cancel_right] using this
      calc ((b : walterJ1)⁻¹ * a) * nJ ^ k = (b : walterJ1)⁻¹ * (a * nJ ^ k * (a : walterJ1)⁻¹) *
            a := by group
        _ = (b : walterJ1)⁻¹ * (b * nJ ^ k * (b : walterJ1)⁻¹) * a := by rw [h']
        _ = nJ ^ k * ((b : walterJ1)⁻¹ * a) := by group
    have hcn : ((b : walterJ1)⁻¹ * a) * nJ = nJ * ((b : walterJ1)⁻¹ * a) := by
      obtain ⟨j, hj⟩ := hnk
      rw [← hj]
      exact (Commute.zpow_right hc j)
    have := eq_one_of_mem_S₀_of_commute (S₀.mul_mem (S₀.inv_mem b.2) a.2) hcn
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hμ) ⟨s₀, hs₀⟩
  have hs' : (s : walterJ1) * nJ ^ k * (s : walterJ1)⁻¹ = φ nJ := by
    have := congrArg Subtype.val hs
    simp only [μ] at this
    rw [hk, ← this]
    group
  refine ⟨(s : walterJ1)⁻¹, S₀.inv_mem s.2, ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, ← hs', inv_inv]
  rw [show (s : walterJ1)⁻¹ * (s * nJ ^ k * (s : walterJ1)⁻¹) * s = nJ ^ k by group]
  exact Subgroup.zpow_mem_zpowers nJ k

theorem rels_R : (nJ⁻¹) ^ 3 * tJ * nJ * tJ * nJ ^ 2 * tJ = 1 ∧
    (nJ ^ 0)⁻¹ ^ 3 * tJ * nJ ^ 0 * tJ * (nJ ^ 0) ^ 2 * tJ ≠ 1 ∧
    (nJ ^ 3)⁻¹ ^ 3 * tJ * nJ ^ 3 * tJ * (nJ ^ 3) ^ 2 * tJ ≠ 1 ∧
    (nJ ^ 5)⁻¹ ^ 3 * tJ * nJ ^ 5 * tJ * (nJ ^ 5) ^ 2 * tJ ≠ 1 ∧
    (nJ ^ 6)⁻¹ ^ 3 * tJ * nJ ^ 6 * tJ * (nJ ^ 6) ^ 2 * tJ ≠ 1 := by
  simp only [ne_eq, ← elt_inv, ← elt_pow, ← elt_append, elt_eq_one_iff]
  decide +kernel

theorem exists_m_conj (φ : MulAut walterJ1) (ht : φ tJ = tJ)
    (hn : φ nJ ∈ Subgroup.zpowers nJ) : ∃ j : ℕ, (MulAut.conj (mJ ^ j) * φ) nJ = nJ := by
  obtain ⟨r0, r1, r3, r5, r6⟩ := rels_R
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hm2, hm4⟩ := rels_aut
  have h7 : orderOf nJ = 7 := orderOf_yJ (p := 7) (by norm_num)
  obtain ⟨k, hk⟩ := hn
  have hk' : φ nJ = nJ ^ ((k % 7).toNat) := by
    rw [← hk]
    change nJ ^ k = nJ ^ (k % 7).toNat
    have hmod := zpow_mod_orderOf nJ k
    rw [h7, Nat.cast_ofNat] at hmod
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num)), hmod]
  have hR : (nJ ^ (k % 7).toNat)⁻¹ ^ 3 * tJ * nJ ^ (k % 7).toNat * tJ *
      (nJ ^ (k % 7).toNat) ^ 2 * tJ = 1 := by
    have := congrArg φ r0
    simp only [map_mul, map_pow, map_inv, map_one, ht] at this
    rwa [hk'] at this
  have hlt : (k % 7).toNat < 7 := by omega
  set i := (k % 7).toNat
  interval_cases i
  · exact absurd hR r1
  · exact ⟨0, by rw [pow_zero, map_one, one_mul, hk', pow_one]⟩
  · refine ⟨1, ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, hk', pow_one]
    exact hm2
  · exact absurd hR r3
  · refine ⟨2, ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, hk']
    exact hm4
  · exact absurd hR r5
  · exact absurd hR r6

theorem fix_m
    (φ : MulAut walterJ1) (ht : φ tJ = tJ) (hn : φ nJ = nJ) : φ mJ = mJ := by
  obtain ⟨-, -, -, -, -, -, -, hmt, hmn, -⟩ := rels_aut
  set c := φ mJ * mJ⁻¹ with hc
  have hct : c * tJ = tJ * c := by
    have h1 : φ mJ * tJ = tJ * φ mJ := by
      have := congrArg φ hmt
      rwa [map_mul, map_mul, ht] at this
    calc c * tJ = φ mJ * (mJ⁻¹ * tJ) := by rw [hc]; group
      _ = φ mJ * (tJ * mJ⁻¹) := by
        rw [show mJ⁻¹ * tJ = tJ * mJ⁻¹ by
          calc mJ⁻¹ * tJ = mJ⁻¹ * (tJ * mJ) * mJ⁻¹ := by group
            _ = mJ⁻¹ * (mJ * tJ) * mJ⁻¹ := by rw [hmt]
            _ = tJ * mJ⁻¹ := by group]
      _ = (φ mJ * tJ) * mJ⁻¹ := by group
      _ = tJ * c := by rw [h1, hc]; group
  have hcn : c * nJ = nJ * c := by
    have h1 : (φ mJ)⁻¹ * nJ * φ mJ = nJ ^ 2 := by
      have := congrArg φ hmn
      rwa [map_mul, map_mul, map_inv, map_pow, hn] at this
    calc c * nJ = φ mJ * (mJ⁻¹ * nJ * mJ) * mJ⁻¹ := by rw [hc]; group
      _ = φ mJ * ((φ mJ)⁻¹ * nJ * φ mJ) * mJ⁻¹ := by rw [hmn, h1]
      _ = nJ * c := by rw [hc]; group
  have hcS : c ∈ Subgroup.centralizer (S₀ : Set walterJ1) := by
    rw [S₀_eq_closure, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    have hconj : ∀ y : walterJ1, y * c = c * y → (nJ⁻¹ * y * nJ) * c = c * (nJ⁻¹ * y * nJ) := by
      intro y hy
      have hcn' : c * nJ⁻¹ = nJ⁻¹ * c := by
        calc c * nJ⁻¹ = nJ⁻¹ * (nJ * c) * nJ⁻¹ := by group
          _ = nJ⁻¹ * (c * nJ) * nJ⁻¹ := by rw [hcn]
          _ = nJ⁻¹ * c := by group
      calc nJ⁻¹ * y * nJ * c = nJ⁻¹ * y * (c * nJ) := by rw [mul_assoc, hcn, ← mul_assoc]
        _ = nJ⁻¹ * (y * c) * nJ := by group
        _ = nJ⁻¹ * (c * y) * nJ := by rw [hy]
        _ = (c * nJ⁻¹) * y * nJ := by rw [hcn']; group
        _ = c * (nJ⁻¹ * y * nJ) := by group
    obtain ⟨-, -, -, hn1, hn2, -, -, -⟩ := rels_S
    have h1 : tJ * c = c * tJ := hct.symm
    have h2 : t2J * c = c * t2J := hn1 ▸ hconj _ h1
    have h3 : t3J * c = c * t3J := hn2 ▸ hconj _ h2
    rintro y (rfl | rfl | rfl)
    exacts [h1, h2, h3]
  have hC := jankoHyp.centralizer_sylow sylowS₀ t_mem_sylowS₀
  change Subgroup.centralizer (S₀ : Set walterJ1) = S₀ at hC
  rw [hC] at hcS
  have hc1 := eq_one_of_mem_S₀_of_commute hcS hcn
  rw [hc, mul_inv_eq_one] at hc1
  exact hc1

theorem rels_u : mJ * uJ * (mJ * uJ) = 1 ∧
    mJ ^ 2 * uJ * (mJ ^ 2 * uJ) = 1 ∧ uJ ≠ mJ * uJ ∧ uJ ≠ mJ ^ 2 * uJ ∧
    mJ * uJ ≠ mJ ^ 2 * uJ ∧ mJ * uJ ≠ 1 ∧ mJ ^ 2 * uJ ≠ 1 ∧
    (mJ * uJ) * mJ * (mJ * uJ)⁻¹ = mJ⁻¹ ∧ (mJ ^ 2 * uJ) * mJ * (mJ ^ 2 * uJ)⁻¹ = mJ⁻¹ ∧
    (mJ * uJ * x'J) ^ 3 ≠ 1 ∧ (mJ ^ 2 * uJ * xJ) ^ 5 ≠ 1 ∧ (tJ * uJ * xJ) ^ 5 ≠ 1 ∧
    (tJ * (mJ * uJ) * xJ) ^ 5 ≠ 1 ∧ (tJ * (mJ ^ 2 * uJ) * xJ) ^ 5 ≠ 1 := by
  simp only [ne_eq, ← elt_inv, ← elt_pow, ← elt_append, elt_eq_one_iff, elt_eq_elt_iff]
  decide +kernel

theorem fix_u
    (φ : MulAut walterJ1) (ht : φ tJ = tJ) (hn : φ nJ = nJ) (hm : φ mJ = mJ) :
    φ uJ = uJ := by
  obtain ⟨x2, -, u2, -, h5, h3, -⟩ := rels_F
  obtain ⟨-, -, -, -, -, hx, hx'⟩ := rels_S
  obtain ⟨-, u1, um, -⟩ := inv_yJ
  obtain ⟨m3, m1, -⟩ := orders_yJ
  obtain ⟨ru2, ru3, ne1, ne2, ne3, ne4, ne5, inv1, inv2, c1, c2, c3, c4, c5⟩ := rels_u
  have hφx : φ xJ = xJ := by
    obtain ⟨-, -, -, hn1, -, -, hx, -⟩ := rels_S
    rw [hx, map_mul, ht, ← hn1, map_mul, map_mul, map_inv, ht, hn]
  have hφx' : φ x'J = x'J := by
    obtain ⟨-, -, -, hn1, hn2, -, -, hx'⟩ := rels_S
    rw [hx', map_mul, ht, ← hn2, ← hn1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ht,
      hn]
  set u' := φ uJ
  have hu'2 : u' * u' = 1 := by rw [← map_mul, u2, map_one]
  have hu't : u' * tJ = tJ * u' := by
    have := congrArg φ commute_tJ.2.2
    rwa [map_mul, map_mul, ht] at this
  have hu'm : u' * mJ * u'⁻¹ = mJ⁻¹ := by
    have := congrArg φ um
    rwa [map_mul, map_mul, map_inv, map_inv, hm] at this
  have hu'x : (u' * xJ) ^ 5 = 1 := by rw [← hφx, ← map_mul, ← map_pow, h5, map_one]
  have hu'x' : (u' * x'J) ^ 3 = 1 := by rw [← hφx', ← map_mul, ← map_pow, h3, map_one]
  have hmF : mJ ∈ FJ := by
    have hmC : mJ ∈ Subgroup.centralizer ({jankoHyp.t} : Set walterJ1) := by
      rw [jankoHyp_t, Subgroup.mem_centralizer_singleton_iff]
      exact (rels_aut.2.2.2.2.2.2.2.1)
    have h3 : orderOf mJ = 3 := orderOf_yJ (p := 3) (by norm_num)
    have := jankoHyp.mem_F_of_odd hmC (by rw [h3]; decide)
    rwa [jankoHyp_F] at this
  have hset := J1.A5Sub.ncard_inv_three jankoHyp.iso (jankoHyp_F ▸ hmF) m3 m1
  rw [jankoHyp_F] at hset
  have huF : uJ ∈ FJ := mem_F.2.2
  have hmuF : mJ * uJ ∈ FJ := FJ.mul_mem hmF huF
  have hm2uF : mJ ^ 2 * uJ ∈ FJ := FJ.mul_mem (FJ.pow_mem hmF 2) huF
  have hsub : ({uJ, mJ * uJ, mJ ^ 2 * uJ} : Set walterJ1) ⊆
      {f | f ∈ FJ ∧ f ^ 2 = 1 ∧ f ≠ 1 ∧ f * mJ * f⁻¹ = mJ⁻¹} := by
    rintro f (rfl | rfl | rfl)
    · exact ⟨huF, by rw [pow_two]; exact u2, u1, um⟩
    · exact ⟨hmuF, by rw [pow_two]; exact ru2, ne4, inv1⟩
    · exact ⟨hm2uF, by rw [pow_two]; exact ru3, ne5, inv2⟩
  have hcard3 : ({uJ, mJ * uJ, mJ ^ 2 * uJ} : Set walterJ1).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair ne3]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ne1, ne2⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hset, hcard3]) (Set.toFinite _)
  have hinv : ∀ f : walterJ1, f ∈ FJ → f * f = 1 → f ≠ 1 → f * mJ * f⁻¹ = mJ⁻¹ →
      f = uJ ∨ f = mJ * uJ ∨ f = mJ ^ 2 * uJ := by
    intro f hf hf2 hf1 hfm
    have : f ∈ ({uJ, mJ * uJ, mJ ^ 2 * uJ} : Set walterJ1) := by
      rw [heq]
      exact ⟨hf, by rw [pow_two]; exact hf2, hf1, hfm⟩
    simpa using this
  have hu'C : u' ∈ Subgroup.centralizer ({jankoHyp.t} : Set walterJ1) := by
    rw [jankoHyp_t, Subgroup.mem_centralizer_singleton_iff]
    exact hu't
  have hu'1 : u' ≠ 1 := by
    rw [Ne, map_eq_one_iff _ φ.injective]
    exact u1
  rcases jankoHyp.mem_centralizer_t.mp hu'C with hF | hF
  · rw [jankoHyp_F] at hF
    rcases hinv u' hF hu'2 hu'1 hu'm with h | h | h
    · exact h
    · rw [h] at hu'x'
      exact absurd hu'x' c1
    · rw [h] at hu'x
      exact absurd hu'x c2
  · rw [jankoHyp_F, jankoHyp_t] at hF
    have hf2 : tJ * u' * (tJ * u') = 1 := by
      calc tJ * u' * (tJ * u') = tJ * (u' * tJ) * u' := by group
        _ = tJ * (tJ * u') * u' := by rw [hu't]
        _ = 1 := by rw [← mul_assoc, tJ_mul_self, one_mul, hu'2]
    have hf1 : tJ * u' ≠ 1 := by
      intro h1
      have hu't' : u' = tJ := by
        calc u' = tJ * (tJ * u') := by rw [← mul_assoc, tJ_mul_self, one_mul]
          _ = tJ := by rw [h1, mul_one]
      rw [hu't', ← rels_aut.2.2.2.2.2.2.2.1, mul_inv_cancel_right] at hu'm
      have : mJ ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [hu'm]
        exact mul_inv_cancel mJ
      have h3' := orderOf_dvd_of_pow_eq_one this
      have h3 : orderOf mJ = 3 := orderOf_yJ (p := 3) (by norm_num)
      rw [h3] at h3'
      norm_num at h3'
    have hfm : tJ * u' * mJ * (tJ * u')⁻¹ = mJ⁻¹ := by
      have htm : tJ * mJ = mJ * tJ := rels_aut.2.2.2.2.2.2.2.1.symm
      calc tJ * u' * mJ * (tJ * u')⁻¹ = tJ * (u' * mJ * u'⁻¹) * tJ⁻¹ := by group
        _ = tJ * mJ⁻¹ * tJ⁻¹ := by rw [hu'm]
        _ = mJ⁻¹ := by
          rw [show tJ * mJ⁻¹ = mJ⁻¹ * tJ by
            calc tJ * mJ⁻¹ = mJ⁻¹ * (mJ * tJ) * mJ⁻¹ := by group
              _ = mJ⁻¹ * (tJ * mJ) * mJ⁻¹ := by rw [htm]
              _ = mJ⁻¹ * tJ := by group]
          group
    have hu'eq : u' = tJ * (tJ * u') := by rw [← mul_assoc, tJ_mul_self, one_mul]
    rw [hu'eq] at hu'x
    rcases hinv _ hF hf2 hf1 hfm with h | h | h
    · rw [h] at hu'x
      exact absurd hu'x c3
    · rw [h] at hu'x
      exact absurd hu'x c4
    · rw [h] at hu'x
      exact absurd hu'x c5

theorem J3_aut
    (φ : MulAut walterJ1) : ∃ g : walterJ1, φ = MulAut.conj g := by
  obtain ⟨g₁, ht₁, hp₁⟩ := exists_conj_fix_t φ
  obtain ⟨s, hs, hn₂⟩ := exists_S₀_conj (MulAut.conj g₁ * φ) hp₁
  have ht₂ : (MulAut.conj s * (MulAut.conj g₁ * φ)) tJ = tJ := by
    rw [MulAut.mul_apply, ht₁, MulAut.conj_apply, S₀_comm hs tJ_mem_S₀, mul_inv_cancel_right]
  obtain ⟨j, hn₃⟩ := exists_m_conj _ ht₂ hn₂
  have ht₃ : (MulAut.conj (mJ ^ j) * (MulAut.conj s * (MulAut.conj g₁ * φ))) tJ = tJ := by
    have hmt : mJ ^ j * tJ = tJ * mJ ^ j :=
      (Commute.pow_left (rels_aut.2.2.2.2.2.2.2.1 : Commute mJ tJ) j)
    rw [MulAut.mul_apply, ht₂, MulAut.conj_apply, hmt, mul_inv_cancel_right]
  have hm₃ := fix_m _ ht₃ hn₃
  have hu₃ := fix_u _ ht₃ hn₃ hm₃
  have h1 := eq_one_of_fix ht₃ hn₃ hm₃ hu₃
  refine ⟨(mJ ^ j * s * g₁)⁻¹, ?_⟩
  have h2 : MulAut.conj (mJ ^ j * s * g₁) * φ = 1 := by
    rw [map_mul, map_mul, mul_assoc, mul_assoc]
    exact h1
  rw [map_inv]
  exact (inv_eq_of_mul_eq_one_right h2).symm

end CFSG.Walter.J1Props
