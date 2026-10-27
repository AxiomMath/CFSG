module

public import CFSG.RankThree.GF2n.Parrott.Lemma16EqualityFusion

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

section Counting

variable {M : Type} [Group M] [Finite M]

theorem card_modEq_card_inf_autFixedSubgroup {p n : ℕ} [Fact p.Prime] {f : MulAut M}
    (hf : f ^ p ^ n = 1) {A : Subgroup M} (hA : ∀ a ∈ A, f a ∈ A) :
    Nat.card A ≡ Nat.card ↥(A ⊓ autFixedSubgroup f) [MOD p] := by
  classical
  let F : Function.End ↥A := fun a => ⟨f a, hA _ a.2⟩
  have hpow : ∀ k : ℕ, ∀ a : ↥A, (((F ^ k) a : ↥A) : M) = (f ^ k) a := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [pow_succ, pow_succ]
      change (((F ^ k) (F a) : ↥A) : M) = (f ^ k) (f a)
      rw [ih]
  have hF : F ^ p ^ n = 1 := by
    funext a
    apply Subtype.ext
    rw [hpow, hf]
    rfl
  have : Fintype ↥A := Fintype.ofFinite _
  have h1 := Equiv.Perm.card_fixedPoints_modEq (f := F) hF
  have e1 : Fintype.card ↥A = Nat.card A := (Nat.card_eq_fintype_card).symm
  have e2 : Fintype.card (Function.fixedPoints F) = Nat.card ↥(A ⊓ autFixedSubgroup f) := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact
      { toFun := fun a => ⟨(a.1 : M), a.1.2, mem_autFixedSubgroup.mpr
          (congrArg Subtype.val a.2)⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, Subtype.ext (mem_autFixedSubgroup.mp b.2.2)⟩
        left_inv := fun a => rfl
        right_inv := fun b => rfl }
  rw [e1, e2] at h1
  exact h1

omit [Finite M] in
theorem exists_card_eq_card_inf_mul_card_of_mul_self_eq_one
    (hcomm : ∀ m m' : M, m * m' = m' * m) (hM : ∀ m : M, m * m = 1) {f : MulAut M}
    (hf : f * f = 1) {A : Subgroup M} (hA : ∀ a ∈ A, f a ∈ A) :
    ∃ R : Subgroup M, R ≤ A ⊓ autFixedSubgroup f ∧ (∀ a ∈ A, f a * a⁻¹ ∈ R) ∧
      (∀ r ∈ R, ∃ a ∈ A, f a * a⁻¹ = r) ∧
      Nat.card A = Nat.card ↥(A ⊓ autFixedSubgroup f) * Nat.card R := by
  let φ : ↥A →* M :=
    { toFun := fun a => f a * (a : M)⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc f a * f b * ((b : M)⁻¹ * (a : M)⁻¹)
            = f a * (f b * (b : M)⁻¹) * (a : M)⁻¹ := by group
          _ = f a * (a : M)⁻¹ * (f b * (b : M)⁻¹) := by
              rw [mul_assoc (f a), hcomm (f b * (b : M)⁻¹) (a : M)⁻¹, ← mul_assoc] }
  refine ⟨φ.range, ?_, fun a ha => ⟨⟨a, ha⟩, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨A.mul_mem (hA _ a.2) (A.inv_mem a.2), mem_autFixedSubgroup.mpr ?_⟩
    change f (f a * (a : M)⁻¹) = f a * (a : M)⁻¹
    have hff : f (f a) = a := by
      rw [← MulAut.mul_apply, hf]
      rfl
    rw [map_mul, map_inv, hff]
    have hinv : ∀ m : M, m⁻¹ = m := fun m => inv_eq_of_mul_eq_one_right (hM m)
    rw [hinv (f a), hinv (a : M), hcomm]
  · rintro r ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · have hker : φ.ker = (A ⊓ autFixedSubgroup f).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_autFixedSubgroup]
      change f a * (a : M)⁻¹ = 1 ↔ (a : M) ∈ A ∧ f a = a
      rw [mul_inv_eq_one]
      exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
    rw [h1, mul_comm]

theorem card_le_card_inf_autFixedSubgroup_sq (hcomm : ∀ m m' : M, m * m' = m' * m)
    (hM : ∀ m : M, m * m = 1) {f : MulAut M} (hf : f * f = 1) {A : Subgroup M}
    (hA : ∀ a ∈ A, f a ∈ A) :
    Nat.card A ≤ Nat.card ↥(A ⊓ autFixedSubgroup f) ^ 2 := by
  obtain ⟨R, hR, -, -, hcard⟩ := exists_card_eq_card_inf_mul_card_of_mul_self_eq_one hcomm hM hf hA
  rw [hcard, sq]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hR)

theorem conj_mul_inv_eq_one_or_eq_of_card_eq_two_mul (hcomm : ∀ m m' : M, m * m' = m' * m)
    (hM : ∀ m : M, m * m = 1) {f : MulAut M} (hf : f * f = 1) {A : Subgroup M}
    (hA : ∀ a ∈ A, f a ∈ A) (hcard : Nat.card A = 2 * Nat.card ↥(A ⊓ autFixedSubgroup f))
    {a₀ : M} (ha₀ : a₀ ∈ A) (hfa₀ : f a₀ ≠ a₀) :
    ∀ a ∈ A, f a * a⁻¹ = 1 ∨ f a * a⁻¹ = f a₀ * a₀⁻¹ := by
  obtain ⟨R, -, hRA, -, hRcard⟩ :=
    exists_card_eq_card_inf_mul_card_of_mul_self_eq_one hcomm hM hf hA
  have hpos : 0 < Nat.card ↥(A ⊓ autFixedSubgroup f) := Nat.card_pos
  have hR2 : Nat.card R = 2 := by
    rw [hcard, mul_comm] at hRcard
    exact (Nat.eq_of_mul_eq_mul_left hpos hRcard).symm
  have hr₀ : f a₀ * a₀⁻¹ ∈ R := hRA a₀ ha₀
  have hr₀1 : f a₀ * a₀⁻¹ ≠ 1 := fun h1 => hfa₀ (mul_inv_eq_one.mp h1)
  have hord : orderOf (f a₀ * a₀⁻¹) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hM _) hr₀1
  have hRz : R = Subgroup.zpowers (f a₀ * a₀⁻¹) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hr₀)
      (by rw [hR2, Nat.card_zpowers, hord])).symm
  intro a ha
  have hr := hRA a ha
  rw [hRz] at hr
  exact (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord).mp hr

end Counting

section Action

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

omit
  hN in
theorem conjV_pi_eq_iff (h : Tim79a.ParrottHyp z) (g : ↥(H z)) (x : ↥(J z)) :
    conjV h g (QuotientV.pi z x) = QuotientV.pi z x ↔
      (g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹ ∈ centerIn (J z) := by
  rw [conjV_mk]
  change (QuotientGroup.mk (conjJ' z g x) : J z ⧸ (centerIn (J z)).subgroupOf (J z)) =
    QuotientGroup.mk x ↔ _
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, div_eq_mul_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]

private theorem conjV_eq_of_qH_eq_aux (h : Tim79a.ParrottHyp z) {a b : ↥(H z)}
    (hab : qH D a = qH D b) : conjV h a = conjV h b := by
  rw [← actionA_mk h a, ← actionA_mk h b, mk_eq_of_qH_eq D hab]

theorem conjV_mem_Fsub_sigma1Nine (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) (g : ↥(H z))
    {v : QuotientV.V z} (hv : v ∈ Fsub (z := z) (sigma1Nine D)) :
    conjV h g v ∈ Fsub (z := z) (sigma1Nine D) := by
  have hJ0 := J0sub_normal (z := z) (D := D) h hEq hσ₂ hq₂
  rw [← Fsub_map_conjV_eq (z := z) (D := D) h hJ0 g]
  exact Subgroup.mem_map_of_mem _ hv

theorem conjV_mem_Wsub_sigma1Nine (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) (g : ↥(H z))
    {v : QuotientV.V z} (hv : v ∈ Wsub h (sigma1Nine D)) :
    conjV h g v ∈ Wsub h (sigma1Nine D) := by
  change v ∈ ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
    (J z)).map (QuotientV.pi z) at hv
  change conjV h g v ∈ ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype,
    J z⁆).subgroupOf (J z)).map (QuotientV.pi z)
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
  rw [conjV_mk]
  refine Subgroup.mem_map_of_mem _ ?_
  rw [Subgroup.mem_subgroupOf, conjJ'_apply_coe]
  exact commutator_sigma1Nine_conj_mem (z := z) (D := D) h hEq hσ₂ hq₂ hcomm.eq.symm g x
    (Subgroup.mem_subgroupOf.mp hx)

theorem card_Wsub_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Nat.card ↥(Wsub h (sigma1Nine D)) = 64 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  have hc : ∀ a ∈ Fsub (z := z) (sigma1Nine D), ∀ b ∈ Wsub h (sigma1Nine D), Commute a b :=
    fun a _ b _ => Commute.all a b
  have h1 := CFSG.card_sup_eq_mul_of_commute _ _ hc (inf_Fsub_Wsub_sigma1Nine (z := z) (D := D) h)
  rw [sup_Fsub_Wsub_sigma1Nine (z := z) (D := D) h, Subgroup.card_top, QuotientV.card_V h,
    card_Fsub_sigma1Nine (z := z) (D := D) h] at h1
  omega

theorem card_autFixedSubgroup_conjV_eq_mul (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) (g : ↥(H z)) :
    Nat.card (autFixedSubgroup (conjV h g)) =
      Nat.card ↥(Fsub (z := z) (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g)) *
        Nat.card ↥(Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g)) := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  have hFW := inf_Fsub_Wsub_sigma1Nine (z := z) (D := D) h
  have hdisj : (Fsub (z := z) (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g)) ⊓
      (Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g)) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hvF, -⟩, hvW, -⟩
    rw [← hFW]
    exact ⟨hvF, hvW⟩
  have hsup : (Fsub (z := z) (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g)) ⊔
      (Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g)) =
      autFixedSubgroup (conjV h g) := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) fun v hv => ?_
    have hvtop : v ∈ Fsub (z := z) (sigma1Nine D) ⊔ Wsub h (sigma1Nine D) := by
      rw [sup_Fsub_Wsub_sigma1Nine (z := z) (D := D) h]
      exact Subgroup.mem_top v
    obtain ⟨f, hf, w, hw, rfl⟩ := (CFSG.mem_sup_of_commute fun a _ b _ => Commute.all a b).mp hvtop
    have hfix := mem_autFixedSubgroup.mp hv
    rw [map_mul] at hfix
    have hTf := conjV_mem_Fsub_sigma1Nine (z := z) D h hσ₂ hq₂ hEq g hf
    have hTw := conjV_mem_Wsub_sigma1Nine (z := z) D h hσ₂ hq₂ hcomm hEq g hw
    have hm : conjV h g f * f⁻¹ ∈ Fsub (z := z) (sigma1Nine D) ⊓ Wsub h (sigma1Nine D) := by
      refine Subgroup.mem_inf.mpr ⟨(Fsub (z := z) (sigma1Nine D)).mul_mem hTf
        ((Fsub (z := z) (sigma1Nine D)).inv_mem hf), ?_⟩
      have e : conjV h g f * f⁻¹ = w * (conjV h g w)⁻¹ := by
        calc conjV h g f * f⁻¹ = conjV h g f * conjV h g w * (conjV h g w)⁻¹ * f⁻¹ := by group
          _ = f * w * (conjV h g w)⁻¹ * f⁻¹ := by rw [hfix]
          _ = w * (conjV h g w)⁻¹ := by
              rw [mul_comm f w, mul_assoc w, mul_assoc w, mul_comm f, mul_assoc, mul_inv_cancel,
                mul_one]
      rw [e]
      exact (Wsub h (sigma1Nine D)).mul_mem hw ((Wsub h (sigma1Nine D)).inv_mem hTw)
    rw [hFW] at hm
    have hTf' : conjV h g f = f := by
      have := (Subgroup.mem_bot.mp hm)
      rwa [mul_inv_eq_one] at this
    have hTw' : conjV h g w = w := by
      rw [hTf'] at hfix
      exact mul_left_cancel hfix
    exact Subgroup.mul_mem_sup ⟨hf, mem_autFixedSubgroup.mpr hTf'⟩
      ⟨hw, mem_autFixedSubgroup.mpr hTw'⟩
  calc Nat.card (autFixedSubgroup (conjV h g))
      = Nat.card ↥((Fsub (z := z) (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g)) ⊔
          (Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h g))) := by rw [hsup]
    _ = _ := CFSG.card_sup_eq_mul_of_commute _ _ (fun a _ b _ => Commute.all a b) hdisj

theorem conjV_sigma1Nine_ne_one (h : Tim79a.ParrottHyp z) :
    conjV h (sigma1Nine (z := z) D) ≠ 1 := by
  intro h1
  have hW : Wsub h (sigma1Nine D) ≠ ⊥ := by
    intro hbot
    have := card_Wsub_sigma1Nine (z := z) D h
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  apply hw1
  have : (w : QuotientV.V z) ∈ Wsub h (sigma1Nine D) ⊓
      autFixedSubgroup (conjV h (sigma1Nine D)) :=
    ⟨w.2, mem_autFixedSubgroup.mpr (by rw [h1]; rfl)⟩
  rw [inf_Wsub_autFixedSubgroup_sigma1Nine (z := z) (D := D) h] at this
  exact Subtype.ext (Subgroup.mem_bot.mp this)

theorem qH_eq_one_of_conjV_eq_one (h : Tim79a.ParrottHyp z) {g : ↥(H z)}
    (hgQ : qH D g ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    (hg : conjV h g = 1) : qH D g = 1 := by
  have : IsSimpleGroup QP45.originalSubgroup := isSimpleGroup_QP45_of_model
  let φ : ↥QP45.originalSubgroup →* MulAut (QuotientV.V z) :=
    (actionA h).comp ((D.toQA45 (z := z) (hN := hN)).symm.toMonoidHom.comp
      (Subgroup.inclusion QP45_le_QA45))
  have hφ : ∀ x : ↥(H z), ∀ hx : qH D x ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup,
      φ ⟨(qH D x : Equiv.Perm (Fin 45)), Subgroup.mem_subgroupOf.mp hx⟩ = conjV h x := by
    intro x hx
    have e : Subgroup.inclusion QP45_le_QA45
        ⟨(qH D x : Equiv.Perm (Fin 45)), Subgroup.mem_subgroupOf.mp hx⟩ = qH D x := rfl
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, toQA45_symm_qH,
      actionA_mk]
  rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hbot | htop
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
    have h1 : φ ⟨(qH D g : Equiv.Perm (Fin 45)), Subgroup.mem_subgroupOf.mp hgQ⟩ = φ 1 := by
      rw [hφ g hgQ, hg, map_one]
    have h2 := congrArg Subtype.val (hinj h1)
    apply Subtype.ext
    simpa using h2
  · exfalso
    have hσQ : qH D (sigma1Nine (z := z) D) ∈
        QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [qH_sigma1Nine]
      exact Subgroup.mem_subgroupOf.mpr sigma1_mem_Q
    have hmem : (⟨(qH D (sigma1Nine (z := z) D) : Equiv.Perm (Fin 45)),
        Subgroup.mem_subgroupOf.mp hσQ⟩ : ↥QP45.originalSubgroup) ∈ φ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hφ _ hσQ] at hmem
    exact conjV_sigma1Nine_ne_one (z := z) D h hmem

end Action

section FiveAndUVT

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

omit [Finite G] in
theorem qH_mem_QP45_of_orderOf_eq_five {b : ↥(H z)} (hb : orderOf b = 5) :
    qH D b ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  have h5 : qH D b ^ 5 = 1 := by rw [← map_pow, ← hb, pow_orderOf_eq_one, map_one]
  have hsq := Subgroup.sq_mem_of_index_two index_QP45 (qH D b)
  have e : qH D b = (qH D b ^ 2) ^ 3 := by
    rw [← pow_mul]
    calc qH D b = qH D b ^ 5 * qH D b := by rw [h5, one_mul]
      _ = qH D b ^ (2 * 3) := by rw [← pow_succ]
  rw [e]
  exact Subgroup.pow_mem _ hsq 3

theorem conjV_eq_self_of_mem_Fsub_of_qH_mem_QP45 (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {g : ↥(H z)}
    (hgQ : qH D g ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {v : QuotientV.V z} (hv : v ∈ Fsub (z := z) (sigma1Nine D)) : conjV h g v = v := by
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hv
  rw [conjV_pi_eq_iff]
  have heC : (e : G) ∈ CJ z (sigma1Nine (z := z) D : G) :=
    mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp he), e.2⟩
  exact conj_mul_inv_mem_centerIn_of_mem_CJ_sigma1Nine (z := z) D h hσ₂ hq₂ hEq g.2 hgQ heC

omit
  hN in
theorem mul_comm_V (h : Tim79a.ParrottHyp z) (v w : QuotientV.V z) : v * w = w * v :=
  (QuotientV.isMulCommutative_V h).is_comm.comm v w

omit
  hN in
theorem mul_self_eq_one_V (h : Tim79a.ParrottHyp z) (v : QuotientV.V z) : v * v = 1 := by
  rw [← sq]
  exact QuotientV.pow_two_eq_one_V h v

private theorem exists_eq_two_pow_of_dvd {m n : ℕ} (hm : m ∣ 2 ^ n) : ∃ k ≤ n, m = 2 ^ k :=
  (Nat.dvd_prime_pow Nat.prime_two).mp hm

theorem mem_commutatorV_iff (h : Tim79a.ParrottHyp z) (b : ↥(H z)) {r : QuotientV.V z} :
    r ∈ commutatorV h b ↔ ∃ w : QuotientV.V z, conjV h b w * w⁻¹ = r := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  let φ : QuotientV.V z →* QuotientV.V z :=
    { toFun := fun w => conjV h b w * w⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul, mul_inv_rev]
        rw [mul_comm w⁻¹ v⁻¹]
        exact mul_mul_mul_comm _ _ _ _ }
  have hφ : ∀ w, φ w = conjV h b w * w⁻¹ := fun _ => rfl
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hnat : ∀ n : ℕ, ∀ w, (conjV h b ^ n) w * w⁻¹ ∈ φ.range := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, MulAut.one_apply, mul_inv_cancel]; exact one_mem _
    | succ n ih =>
      intro w
      have e : (conjV h b ^ (n + 1)) w * w⁻¹ =
          ((conjV h b ^ n) (conjV h b w) * (conjV h b w)⁻¹) * φ w := by
        rw [hφ, pow_succ, MulAut.mul_apply]; group
      rw [e]
      exact mul_mem (ih _) ⟨w, rfl⟩
  have hint : ∀ k : ℤ, ∀ w, (conjV h b ^ k) w * w⁻¹ ∈ φ.range := by
    intro k w
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast]; exact hnat n w
    · have e : (conjV h b ^ (-(n : ℤ))) w * w⁻¹ =
          ((conjV h b ^ n) ((conjV h b ^ (-(n : ℤ))) w) * ((conjV h b ^ (-(n : ℤ))) w)⁻¹)⁻¹ := by
        rw [← MulAut.mul_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero,
          MulAut.one_apply, mul_inv_rev, inv_inv]
      rw [e]
      exact inv_mem (hnat n _)
  constructor
  · intro hr
    have hle : ⁅(Subgroup.zpowers b).map (H z).subtype, J z⁆ ≤
        (φ.range.comap (QuotientV.pi z)).map (J z).subtype := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg₁
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hJc : ((b ^ k : ↥(H z)) : G) * g₂ * ((b ^ k : ↥(H z)) : G)⁻¹ ∈ J z :=
        (Subgroup.mem_normalizer_iff.mp (hHN (b ^ k).2) g₂).mp hg₂
      refine ⟨⟨((b ^ k : ↥(H z)) : G) * g₂ * ((b ^ k : ↥(H z)) : G)⁻¹ * g₂⁻¹,
        mul_mem hJc (inv_mem hg₂)⟩, ?_, by simp [commutatorElement_def]⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (⟨((b ^ k : ↥(H z)) : G) * g₂ * ((b ^ k : ↥(H z)) : G)⁻¹ * g₂⁻¹,
          mul_mem hJc (inv_mem hg₂)⟩ : ↥(J z)) =
          conjJ' z (b ^ k) ⟨g₂, hg₂⟩ * (⟨g₂, hg₂⟩ : ↥(J z))⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
      rw [e, map_mul, map_inv, ← conjV_mk, map_zpow]
      exact hint k _
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_subgroupOf.mp hy))
    have hyy : y' = y := Subtype.ext hyy'
    rw [← hyy]
    exact Subgroup.mem_comap.mp hy'
  · rintro ⟨w, rfl⟩
    obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z w
    have hbA : (b : G) ∈ (Subgroup.zpowers b).map (H z).subtype :=
      ⟨b, Subgroup.mem_zpowers b, rfl⟩
    have hJb : (b : G) * (j : G) * (b : G)⁻¹ ∈ J z :=
      (Subgroup.mem_normalizer_iff.mp (hHN b.2) j).mp j.2
    refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (j : G) * (b : G)⁻¹ * (j : G)⁻¹,
      mul_mem hJb (inv_mem j.2)⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := Subgroup.commutator_mem_commutator hbA j.2
      rwa [commutatorElement_def] at this
    · have e : (⟨(b : G) * (j : G) * (b : G)⁻¹ * (j : G)⁻¹, mul_mem hJb (inv_mem j.2)⟩ :
          ↥(J z)) = conjJ' z b j * j⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
      rw [e, map_mul, map_inv, ← conjV_mk]

theorem card_Wsub_inf_autFixedSubgroup_of_orderOf_eq_five (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {b : ↥(H z)} (hb : orderOf b = 5) :
    Nat.card ↥(Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h b)) = 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbQ := qH_mem_QP45_of_orderOf_eq_five (z := z) D hb
  have hT5 : conjV h b ^ 5 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← hb, pow_orderOf_eq_one, map_one]
  have hFfix : ∀ v ∈ Fsub (z := z) (sigma1Nine D), conjV h b v = v := fun v hv =>
    conjV_eq_self_of_mem_Fsub_of_qH_mem_QP45 (z := z) D h hσ₂ hq₂ hEq hbQ hv
  have hWinv : ∀ v ∈ Wsub h (sigma1Nine D), conjV h b v ∈ Wsub h (sigma1Nine D) := fun v hv =>
    conjV_mem_Wsub_sigma1Nine (z := z) D h hσ₂ hq₂ hcomm hEq b hv
  have hmod := card_modEq_card_inf_autFixedSubgroup hT5 hWinv
  rw [card_Wsub_sigma1Nine (z := z) D h] at hmod
  have hdvd : Nat.card ↥(Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h b)) ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← card_Wsub_sigma1Nine (z := z) D h]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkc⟩ := exists_eq_two_pow_of_dvd hdvd
  rw [hkc] at hmod ⊢
  interval_cases k
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · rfl
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exfalso
    have hWeq : Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h b) = Wsub h (sigma1Nine D) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [hkc, card_Wsub_sigma1Nine (z := z) D h]; norm_num)
    have hT1 : conjV h b = 1 := by
      apply MulEquiv.ext
      intro v
      have hvtop : v ∈ Fsub (z := z) (sigma1Nine D) ⊔ Wsub h (sigma1Nine D) := by
        rw [sup_Fsub_Wsub_sigma1Nine (z := z) (D := D) h]
        exact Subgroup.mem_top v
      obtain ⟨f, hf, w, hw, rfl⟩ :=
        (CFSG.mem_sup_of_commute fun a _ b _ => (mul_comm_V h a b : Commute a b)).mp hvtop
      have hw' : w ∈ Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h b) := by
        rw [hWeq]; exact hw
      rw [map_mul, hFfix f hf, mem_autFixedSubgroup.mp hw'.2]
      rfl
    have hq1 := qH_eq_one_of_conjV_eq_one (z := z) D h hbQ hT1
    have hbJ : (b : G) ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D b).mpr hq1)
    have hdvd5 : orderOf (⟨(b : G), hbJ⟩ : ↥(J z)) ∣ 2 ^ 10 := by
      rw [← card_J h]
      exact orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hb] at hdvd5
    norm_num at hdvd5

theorem card_autFixedSubgroup_conjV_of_orderOf_eq_five (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {b : ↥(H z)} (hb : orderOf b = 5) :
    Nat.card (autFixedSubgroup (conjV h b)) = 16 := by
  have hbQ := qH_mem_QP45_of_orderOf_eq_five (z := z) D hb
  have hFeq : Fsub (z := z) (sigma1Nine D) ⊓ autFixedSubgroup (conjV h b) =
      Fsub (z := z) (sigma1Nine D) :=
    inf_eq_left.mpr fun v hv => mem_autFixedSubgroup.mpr
      (conjV_eq_self_of_mem_Fsub_of_qH_mem_QP45 (z := z) D h hσ₂ hq₂ hEq hbQ hv)
  rw [card_autFixedSubgroup_conjV_eq_mul (z := z) D h hσ₂ hq₂ hcomm hEq b, hFeq,
    card_Wsub_inf_autFixedSubgroup_of_orderOf_eq_five (z := z) D h hσ₂ hq₂ hcomm hEq hb,
    card_Fsub_sigma1Nine (z := z) (D := D) h]

theorem card_commutatorV_of_orderOf_eq_five (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {b : ↥(H z)} (hb : orderOf b = 5) :
    Nat.card (commutatorV h b) = 16 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  let φ : QuotientV.V z →* QuotientV.V z :=
    { toFun := fun w => conjV h b w * w⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul, mul_inv_rev]
        rw [mul_comm w⁻¹ v⁻¹]
        exact mul_mul_mul_comm _ _ _ _ }
  have hR : commutatorV h b = φ.range := by
    ext r
    rw [mem_commutatorV_iff (z := z) h b]
    rfl
  have hK : φ.ker = autFixedSubgroup (conjV h b) := by
    ext w
    rw [MonoidHom.mem_ker, mem_autFixedSubgroup]
    exact mul_inv_eq_one
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hK,
    card_autFixedSubgroup_conjV_of_orderOf_eq_five (z := z) D h hσ₂ hq₂ hcomm hEq hb,
    QuotientV.card_V h] at h1
  rw [hR]
  omega

theorem conjV_eq_self_of_mem_commutatorV_of_orderOf_eq_five (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {b : ↥(H z)} (hb : orderOf b = 5) {g : ↥(H z)} (hg2 : qH D g * qH D g = 1)
    (hgb : qH D g * qH D b = qH D b * qH D g) :
    ∀ v ∈ commutatorV h b, conjV h g v = v := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set R := commutatorV h b with hRdef
  have hTb5 : conjV h b ^ 5 = 1 := by
    rw [← map_pow, ← hb, pow_orderOf_eq_one, map_one]
  have hgb' : conjV h g * conjV h b = conjV h b * conjV h g := by
    rw [← map_mul, ← map_mul]
    exact conjV_eq_of_qH_eq_aux (z := z) D h (by rw [map_mul, map_mul, hgb])
  have hgg : conjV h g * conjV h g = 1 := by
    rw [← map_mul, ← map_one (conjV h)]
    exact conjV_eq_of_qH_eq_aux (z := z) D h (by rw [map_mul, hg2, map_one])
  have hRmem := fun r => mem_commutatorV_iff (z := z) h b (r := r)
  have hgR : ∀ r ∈ R, conjV h g r ∈ R := by
    intro r hr
    obtain ⟨w, rfl⟩ := (hRmem r).mp hr
    refine (hRmem _).mpr ⟨conjV h g w, ?_⟩
    rw [map_mul (conjV h g), map_inv (conjV h g), ← MulAut.mul_apply _ (conjV h g), hgb',
      MulAut.mul_apply]
  have hbR : ∀ r ∈ R, conjV h b r ∈ R := by
    intro r hr
    obtain ⟨w, rfl⟩ := (hRmem r).mp hr
    exact (hRmem _).mpr ⟨conjV h b w, by rw [map_mul, map_inv]⟩
  have hRb : R ⊓ autFixedSubgroup (conjV h b) = ⊥ := by
    rw [eq_bot_iff]
    rintro r ⟨hr, hrb⟩
    obtain ⟨w, rfl⟩ := (hRmem _).mp hr
    set r' := conjV h b w * w⁻¹ with hr'
    have hrb' : conjV h b r' = r' := mem_autFixedSubgroup.mp hrb
    have hTw : conjV h b w = w * r' := by
      rw [hr', mul_comm_V h (conjV h b w) w⁻¹]
      group
    have hpow : ∀ n : ℕ, (conjV h b ^ n) w = w * r' ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (conjV h b ^ (n + 1)) w = conjV h b ((conjV h b ^ n) w) := by
              rw [pow_succ', MulAut.mul_apply]
          _ = conjV h b w * conjV h b r' ^ n := by rw [ih, map_mul, map_pow]
          _ = w * r' ^ (n + 1) := by rw [hTw, hrb', pow_succ', mul_assoc]
    have h5 := hpow 5
    rw [hTb5, MulAut.one_apply] at h5
    have hr5 : r' ^ 5 = 1 := by
      have := congrArg (w⁻¹ * ·) h5
      simpa using this.symm
    have hr2 : r' * r' = 1 := mul_self_eq_one_V h r'
    rw [Subgroup.mem_bot]
    calc r' = r' ^ 5 * (r' * r')⁻¹ * (r' * r')⁻¹ := by group
      _ = 1 := by rw [hr5, hr2]; group
  have hb51 : conjV h b ^ 5 ^ 1 = 1 := by rw [pow_one]; exact hTb5
  have hinv : ∀ r ∈ R ⊓ autFixedSubgroup (conjV h g),
      conjV h b r ∈ R ⊓ autFixedSubgroup (conjV h g) := by
    rintro r ⟨hr, hrg⟩
    refine ⟨hbR r hr, mem_autFixedSubgroup.mpr ?_⟩
    rw [← MulAut.mul_apply, hgb', MulAut.mul_apply, mem_autFixedSubgroup.mp hrg]
  have hmod := card_modEq_card_inf_autFixedSubgroup hb51 hinv
  have hbot : R ⊓ autFixedSubgroup (conjV h g) ⊓ autFixedSubgroup (conjV h b) = ⊥ := by
    rw [eq_bot_iff, ← hRb]
    exact fun r hr => ⟨hr.1.1, hr.2⟩
  rw [hbot, Subgroup.card_bot] at hmod
  have hcard : Nat.card R = 16 :=
    card_commutatorV_of_orderOf_eq_five (z := z) D h hσ₂ hq₂ hcomm hEq hb
  have hdvd : Nat.card ↥(R ⊓ autFixedSubgroup (conjV h g)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkc⟩ := exists_eq_two_pow_of_dvd hdvd
  have hsq := card_le_card_inf_autFixedSubgroup_sq (mul_comm_V h) (mul_self_eq_one_V h) hgg hgR
  rw [hcard, hkc] at hsq
  rw [hkc] at hmod
  have hk4 : k = 4 := by
    interval_cases k
    · norm_num at hsq
    · norm_num at hsq
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · rfl
  have hRg : R ⊓ autFixedSubgroup (conjV h g) = R :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hkc, hk4, hcard]; norm_num)
  intro r hr
  rw [← hRg] at hr
  exact mem_autFixedSubgroup.mp hr.2

theorem card_Wsub_inf_autFixedSubgroup_mul_inv_eq_four (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card ↥(Wsub h (sigma1Nine D) ⊓
        autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹))) = 4 ∧
      ∀ u ∈ Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)),
        ∃ q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
            ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
          ∃ hq : q ∈ J z, QuotientV.pi z ⟨q, hq⟩ = u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hσdef
  set Q : Subgroup G := CJ z (σ : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ with hQdef
  set U : Subgroup (QuotientV.V z) :=
    Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h σ) with hUdef
  have hQJ : Q ≤ J z := fun q hq => (mem_CJ.mp hq.1).2
  have hσ3 : orderOf σ = 3 := orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  have hzQZ : ∀ q ∈ Q, q ∈ centerIn (J z) → q ∈ Subgroup.zpowers z := by
    intro q hq hqZ
    rw [← centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
    exact ⟨⟨hQJ hq, (mem_CJ.mp (centerIn_le_CJ_sigma1Nine (z := z) D h hqZ)).1⟩, hq.2⟩
  have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hzQ : z ∈ Q := by
    have hzA : z ∈ (J z ⊓ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G)) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      rw [centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
      exact Subgroup.mem_zpowers z
    refine ⟨mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, z_mem_J h⟩, hzA.2⟩
    exact (hcent z (Subgroup.mem_zpowers z) _ σ.2).symm
  let ψ : ↥Q →* QuotientV.V z := (QuotientV.pi z).comp (Subgroup.inclusion hQJ)
  have hψU : ψ.range ≤ U := by
    rintro _ ⟨q, rfl⟩
    refine ⟨?_, mem_autFixedSubgroup.mpr ?_⟩
    · change QuotientV.pi z (Subgroup.inclusion hQJ q) ∈
        ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
          (J z)).map (QuotientV.pi z)
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr q.2.2)
    · change conjV h σ (QuotientV.pi z (Subgroup.inclusion hQJ q)) =
        QuotientV.pi z (Subgroup.inclusion hQJ q)
      rw [conjV_pi_eq_iff]
      have hqs := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp q.2.1).1
      change (σ : G) * (q : G) * (σ : G)⁻¹ * (q : G)⁻¹ ∈ centerIn (J z)
      rw [← hqs, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hker : Nat.card ψ.ker = 2 := by
    have hk : ψ.ker = (Subgroup.zpowers z).subgroupOf Q := by
      ext q
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change QuotientV.pi z (Subgroup.inclusion hQJ q) = 1 ↔ _
      rw [← MonoidHom.mem_ker, QuotientV.pi_ker, Subgroup.mem_subgroupOf]
      exact ⟨fun hq => hzQZ q q.2 hq, fun hq => Subgroup.zpowers_le_of_mem hzZ hq⟩
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le_of_mem hzQ)).toEquiv,
      Nat.card_zpowers, h.1]
  have hrange : Nat.card ψ.range = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker,
      card_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq] at h1
    omega
  have hFfix : ∀ v ∈ Fsub (z := z) (sigma1Nine D), conjV h σ v = v := by
    intro v hv
    have h1 : conjV h (sigma1Nine D) v = v := conjV_trivial_on_Fsub h (sigma1Nine D) v hv
    have h2 : conjV h σ₂ v = v := conjV_trivial_on_Fsub_of_le h (le_of_eq hEq) v hv
    have h2' : (conjV h σ₂)⁻¹ v = v := by
      calc (conjV h σ₂)⁻¹ v = (conjV h σ₂)⁻¹ ((conjV h σ₂) v) := by rw [h2]
        _ = v := by simp
    rw [hσdef, map_mul, map_inv, MulAut.mul_apply, h2', h1]
  have hFeq : Fsub (z := z) (sigma1Nine D) ⊓ autFixedSubgroup (conjV h σ) =
      Fsub (z := z) (sigma1Nine D) :=
    inf_eq_left.mpr fun v hv => mem_autFixedSubgroup.mpr (hFfix v hv)
  have hfixV := card_autFixedSubgroup_conjV_eq_mul (z := z) D h hσ₂ hq₂ hcomm hEq σ
  rw [hFeq, card_Fsub_sigma1Nine (z := z) (D := D) h] at hfixV
  have hcop : Nat.Coprime (orderOf σ) (Nat.card (J z)) := by rw [hσ3, card_J h]; norm_num
  have hC := card_centralizer_eq_card_inf_centerIn_mul_card_fixedBy h hcop
  rw [← card_autFixedSubgroup_conjV_eq_card_fixedBy h σ] at hC
  have hZσ : conjZ z σ = 1 := by
    rw [hσdef, map_mul, map_inv, conjZ_sigma1Nine h D, conjZ_eq_one_of_qH_eq_sigma2 D h hq₂,
      inv_one, mul_one]
  have hCZ : Subgroup.centralizer ({(σ : G)} : Set G) ⊓ centerIn (J z) = centerIn (J z) :=
    inf_eq_right.mpr (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZσ)
  rw [hCZ, card_centerIn_J h] at hC
  have hJ₀P : CJ z (sigma1Nine (z := z) D : G) ≤ CJ z (σ : G) := by
    intro y hy
    obtain ⟨hy1, hyJ⟩ := mem_CJ.mp hy
    have h1 : Commute y (sigma1Nine (z := z) D : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hy1
    have h2' : (⟨y, hyJ⟩ : ↥(J z)) ∈ centralizerJ σ₂ := by
      rw [← hEq]
      exact mem_centralizerJ_iff.mpr h1
    have h2 : Commute y (σ₂ : G) := mem_centralizerJ_iff.mp h2'
    refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hyJ⟩
    rw [hσdef, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (h1.mul_right h2.inv_right).eq
  have hle128 : Nat.card ↥(CJ z (σ : G)) ≤ 128 := by
    let f : ↥Q × ↥(CJ z (sigma1Nine (z := z) D : G)) → ↥(CJ z (σ : G)) := fun p =>
      ⟨(p.1 : G) * (p.2 : G), (CJ z (σ : G)).mul_mem p.1.2.1 (hJ₀P p.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨c, hc⟩
      obtain ⟨q, hq, a, ha, hqa⟩ := exists_mul_eq_of_mem_CJ_mul_inv (z := z) D h hEq hc
      exact ⟨(⟨q, hq⟩, ⟨a, ha⟩), Subtype.ext hqa⟩
    have h1 := Nat.card_le_card_of_surjective f hf
    have h16 : Nat.card ↥(CJ z (sigma1Nine (z := z) D : G)) = 16 := by
      rw [card_CJ_eq_card_centralizerJ]
      exact card_centralizerJ_sigma1Nine h D
    rw [Nat.card_prod, card_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq, h16] at h1
    exact h1
  have hU8 : Nat.card U ≤ 8 := by
    change Nat.card ↥(CJ z (σ : G)) = 4 * Nat.card (autFixedSubgroup (conjV h σ)) at hC
    change Nat.card (autFixedSubgroup (conjV h σ)) = 4 * Nat.card ↥U at hfixV
    omega
  have hσ3' : conjV h σ ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← hσ3, pow_orderOf_eq_one, map_one]
  have hmod := card_modEq_card_inf_autFixedSubgroup hσ3'
    (fun v hv => conjV_mem_Wsub_sigma1Nine (z := z) D h hσ₂ hq₂ hcomm hEq σ hv)
  rw [card_Wsub_sigma1Nine (z := z) D h] at hmod
  have hdvd : Nat.card U ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← card_Wsub_sigma1Nine (z := z) D h]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hge : 4 ≤ Nat.card U := hrange ▸ Subgroup.card_le_of_le hψU
  obtain ⟨k, hk, hkc⟩ := exists_eq_two_pow_of_dvd hdvd
  have hU4 : Nat.card U = 4 := by
    change 64 ≡ Nat.card ↥U [MOD 3] at hmod
    rw [hkc] at hmod hU8 hge ⊢
    interval_cases k
    · exact absurd hge (by norm_num)
    · exact absurd hge (by norm_num)
    · rfl
    · exact absurd hmod (by decide)
    · exact absurd hU8 (by norm_num)
    · exact absurd hU8 (by norm_num)
    · exact absurd hU8 (by norm_num)
  refine ⟨hU4, fun u hu => ?_⟩
  have hR : ψ.range = U := Subgroup.eq_of_le_of_card_ge hψU (by rw [hU4, hrange])
  rw [← hR] at hu
  obtain ⟨q, rfl⟩ := hu
  exact ⟨q, q.2, hQJ q.2, rfl⟩

theorem card_Wsub_inf_autFixedSubgroup_conjV_eq_eight (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {b : ↥(H z)} (hb : orderOf b = 5)
    (hbuv : qH D b * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) =
      ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) * qH D b)
    {x : ↥(H z)}
    (hqx : qH D x = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) :
    Nat.card ↥(Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h x)) = 8 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcV := mul_comm_V h
  have hMV := mul_self_eq_one_V h
  set σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hσdef
  set W : Subgroup (QuotientV.V z) := Wsub h (sigma1Nine D) with hWdef
  set U : Subgroup (QuotientV.V z) := W ⊓ autFixedSubgroup (conjV h σ) with hUdef
  set Q : Subgroup G := CJ z (σ : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ with hQdef
  have hσ3 : orderOf σ = 3 := orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  have hqσ : qH D σ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
    rw [hσdef, map_mul, map_inv, qH_sigma1Nine, hq₂]
  set uA : QA45.originalSubgroup := ⟨u, u_mem_A⟩ with huAdef
  set vA : QA45.originalSubgroup := ⟨v, v_mem_A⟩ with hvAdef
  set tA : QA45.originalSubgroup := ⟨t, t_mem_A⟩ with htAdef
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hvv : vA * vA = 1 := Subtype.ext v_sq
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have hvt : Commute tA vA := Subtype.ext t_commute_v
  have huv : Commute uA vA := Subtype.ext u_commute_v
  have ht1 : Commute tA (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) :=
    Subtype.ext t_commute_sigma1
  have ht2 : Commute tA (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) :=
    Subtype.ext t_commute_sigma2
  have htuv : Commute tA (uA * vA) := hut.mul_right hvt
  have huv2 : (uA * vA) * (uA * vA) = 1 := by
    rw [Commute.mul_mul_mul_comm huv.symm uA vA, huu, hvv, one_mul]
  have huvt2 : (uA * vA * tA) * (uA * vA * tA) = 1 := by
    rw [Commute.mul_mul_mul_comm htuv (uA * vA) tA, huv2, htt, one_mul]
  have huv_uvt : (uA * vA) * (uA * vA * tA) = (uA * vA * tA) * (uA * vA) := by
    rw [mul_assoc (uA * vA) tA, ← htuv.eq, ← mul_assoc, ← mul_assoc]
  have huvtσ : (uA * vA * tA) * qH D σ = qH D σ * (uA * vA * tA) := by
    rw [hqσ]; exact Subtype.ext uvt_mul_sigma1_mul_sigma2_inv
  obtain ⟨sH, hsq, hsσ⟩ := exists_lift_centralizer D hσ3 huvtσ
  have htσ : tA * qH D σ = qH D σ * tA := by rw [hqσ]; exact (ht1.mul_right ht2.inv_right).eq
  obtain ⟨tH, htq, htσ'⟩ := exists_lift_centralizer D hσ3 htσ
  set g : ↥(H z) := sH * tH⁻¹ with hgdef
  have hgq : qH D g = uA * vA := by
    rw [hgdef, map_mul, map_inv, hsq, htq, mul_inv_cancel_right]
  have hgσ : g * σ = σ * g := by
    have h1 : tH⁻¹ * σ = σ * tH⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, htσ', mul_assoc, mul_inv_cancel, mul_one]
    rw [hgdef, mul_assoc, h1, ← mul_assoc, hsσ, mul_assoc]
  have htg : tH = g⁻¹ * sH := by rw [hgdef]; group
  have hxs : conjV h x = conjV h sH := conjV_eq_of_qH_eq_aux (z := z) D h (hqx.trans hsq.symm)
  rw [hxs]
  have hq2 : ∀ k : ↥(H z), qH D k * qH D k = 1 → conjV h k * conjV h k = 1 := by
    intro k hk
    rw [← map_mul, ← map_one (conjV h)]
    exact conjV_eq_of_qH_eq_aux (z := z) D h (by rw [map_mul, hk, map_one])
  have hqc : ∀ k k' : ↥(H z), qH D k * qH D k' = qH D k' * qH D k →
      conjV h k * conjV h k' = conjV h k' * conjV h k := by
    intro k k' hk
    rw [← map_mul, ← map_mul]
    exact conjV_eq_of_qH_eq_aux (z := z) D h (by rw [map_mul, map_mul, hk])
  have hss : conjV h sH * conjV h sH = 1 := hq2 sH (by rw [hsq]; exact huvt2)
  have hgg : conjV h g * conjV h g = 1 := hq2 g (by rw [hgq]; exact huv2)
  have hsσV : conjV h sH * conjV h σ = conjV h σ * conjV h sH := by
    rw [← map_mul, ← map_mul, hsσ]
  have hgb : conjV h g * conjV h b = conjV h b * conjV h g := hqc g b (by rw [hgq]; exact hbuv.symm)
  have ht1V : conjV h tH * conjV h (sigma1Nine D) = conjV h (sigma1Nine D) * conjV h tH :=
    hqc tH _ (by rw [htq, qH_sigma1Nine]; exact ht1.eq)
  have hginv : (conjV h g)⁻¹ = conjV h g := inv_eq_of_mul_eq_one_right hgg
  have htgs : conjV h tH = conjV h g * conjV h sH := by rw [htg, map_mul, map_inv, hginv]
  have hgts : conjV h g = conjV h tH * conjV h sH := by
    rw [htgs, mul_assoc, hss, mul_one]
  have hWinv : ∀ k : ↥(H z), ∀ w ∈ W, conjV h k w ∈ W := fun k w hw =>
    conjV_mem_Wsub_sigma1Nine (z := z) D h hσ₂ hq₂ hcomm hEq k hw
  have hUinv : ∀ k : ↥(H z), conjV h k * conjV h σ = conjV h σ * conjV h k →
      ∀ w ∈ U, conjV h k w ∈ U := by
    rintro k hk w ⟨hwW, hwσ⟩
    refine ⟨hWinv k w hwW, mem_autFixedSubgroup.mpr ?_⟩
    rw [← MulAut.mul_apply, ← hk, MulAut.mul_apply, mem_autFixedSubgroup.mp hwσ]
  obtain ⟨hU4, hUQ⟩ :=
    card_Wsub_inf_autFixedSubgroup_mul_inv_eq_four (z := z) D h hσ₂ hq₂ hcomm hEq
  have hQJ : ∀ q ∈ Q, q ∈ J z := fun q hq => (mem_CJ.mp hq.1).2
  have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have htQ : ∀ q ∈ Q, (tH : G) * q * (tH : G)⁻¹ ∈ Q := fun q hq =>
    conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq tH.2
      (Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val htσ')) hq
  have htJ : (tH : G) * (tH : G) ∈ J z := by
    have : tH * tH ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_mul, htq]; exact htt
    exact Subgroup.mem_subgroupOf.mp this
  have htω : (tH : G) * ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * (tH : G)⁻¹ *
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹ ∈ J z := by
    have : tH * (sigma1Nine (z := z) D * σ₂) * tH⁻¹ * (sigma1Nine (z := z) D * σ₂)⁻¹ ∈
        (J z).subgroupOf (H z) := by
      rw [J_mem_iff D]
      simp only [map_mul, map_inv, qH_sigma1Nine, hq₂, htq]
      rw [(ht1.mul_right ht2).eq]
      group
    simpa using Subgroup.mem_subgroupOf.mp this
  have htU : ∀ w ∈ U, conjV h tH w = w := by
    intro w hw
    obtain ⟨q, hq, hqJ, rfl⟩ := hUQ w hw
    rw [conjV_pi_eq_iff]
    exact Subgroup.zpowers_le_of_mem hzZ
      (conj_mul_inv_mem_zpowers_of_conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm
        hEq tH.2 htQ htJ htω hq)
  obtain ⟨kU, hkU, hkUz⟩ := exists_conj_mul_inv_not_mem_zpowers (z := z) D h hσ₂ hq₂ hcomm hEq
    (x := (sH : G)) sH.2 hsq
  set u₀ : QuotientV.V z := QuotientV.pi z ⟨kU, hQJ kU hkU⟩ with hu₀def
  have hu₀U : u₀ ∈ U := by
    refine ⟨?_, mem_autFixedSubgroup.mpr ?_⟩
    · change QuotientV.pi z ⟨kU, hQJ kU hkU⟩ ∈
        ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
          (J z)).map (QuotientV.pi z)
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hkU.2)
    · rw [hu₀def, conjV_pi_eq_iff]
      have hks := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hkU.1).1
      change (σ : G) * kU * (σ : G)⁻¹ * kU⁻¹ ∈ centerIn (J z)
      rw [← hks, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hsu₀ : conjV h sH u₀ ≠ u₀ := by
    rw [Ne, hu₀def, conjV_pi_eq_iff]
    intro hZ
    apply hkUz
    have hsQ : (sH : G) * kU * (sH : G)⁻¹ ∈ Q :=
      conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq sH.2
        (Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hsσ)) hkU
    have hδQ : (sH : G) * kU * (sH : G)⁻¹ * kU⁻¹ ∈ Q := Q.mul_mem hsQ (Q.inv_mem hkU)
    rw [← centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
    exact ⟨⟨hQJ _ hδQ, (mem_CJ.mp (centerIn_le_CJ_sigma1Nine (z := z) D h hZ)).1⟩, hδQ.2⟩
  have hgU : ∀ w ∈ U, conjV h g w = conjV h sH w := by
    intro w hw
    rw [hgts, MulAut.mul_apply, htU _ (hUinv sH hsσV w hw)]
  have hgu₀ : conjV h g u₀ ≠ u₀ := by rw [hgU u₀ hu₀U]; exact hsu₀
  have hWb4 := card_Wsub_inf_autFixedSubgroup_of_orderOf_eq_five (z := z) D h hσ₂ hq₂ hcomm hEq hb
  have hb51 : conjV h b ^ 5 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← hb, pow_orderOf_eq_one, map_one]
  have hinvb : ∀ w ∈ W ⊓ autFixedSubgroup (conjV h g),
      conjV h b w ∈ W ⊓ autFixedSubgroup (conjV h g) := by
    rintro w ⟨hwW, hwg⟩
    refine ⟨hWinv b w hwW, mem_autFixedSubgroup.mpr ?_⟩
    rw [← MulAut.mul_apply, hgb, MulAut.mul_apply, mem_autFixedSubgroup.mp hwg]
  have hmod5 := card_modEq_card_inf_autFixedSubgroup hb51 hinvb
  have hgWb : ∀ w ∈ W ⊓ autFixedSubgroup (conjV h b),
      conjV h g w ∈ W ⊓ autFixedSubgroup (conjV h b) := by
    rintro w ⟨hwW, hwb⟩
    refine ⟨hWinv g w hwW, mem_autFixedSubgroup.mpr ?_⟩
    rw [← MulAut.mul_apply, ← hgb, MulAut.mul_apply, mem_autFixedSubgroup.mp hwb]
  have hlow := card_le_card_inf_autFixedSubgroup_sq hcV hMV hgg hgWb
  rw [hWb4] at hlow
  have heq : W ⊓ autFixedSubgroup (conjV h g) ⊓ autFixedSubgroup (conjV h b) =
      (W ⊓ autFixedSubgroup (conjV h b)) ⊓ autFixedSubgroup (conjV h g) := by
    rw [inf_assoc, inf_comm (autFixedSubgroup (conjV h g)), ← inf_assoc]
  rw [heq] at hmod5
  have hup : Nat.card ↥((W ⊓ autFixedSubgroup (conjV h b)) ⊓ autFixedSubgroup (conjV h g)) ≤ 4 :=
    hWb4 ▸ Subgroup.card_le_of_le inf_le_left
  have hdvd4 : Nat.card ↥((W ⊓ autFixedSubgroup (conjV h b)) ⊓ autFixedSubgroup (conjV h g)) ∣
      2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hWb4]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hjc⟩ := exists_eq_two_pow_of_dvd hdvd4
  have hWcard : Nat.card W = 64 := card_Wsub_sigma1Nine (z := z) D h
  have hdvdg : Nat.card ↥(W ⊓ autFixedSubgroup (conjV h g)) ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hWcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨a, ha, hac⟩ := exists_eq_two_pow_of_dvd hdvdg
  have hlowg := card_le_card_inf_autFixedSubgroup_sq hcV hMV hgg (hWinv g)
  rw [hWcard, hac] at hlowg
  rw [hjc, hac] at hmod5
  rw [hjc] at hlow
  have hWg : Nat.card ↥(W ⊓ autFixedSubgroup (conjV h g)) = 32 := by
    rw [hac]
    interval_cases a
    · norm_num at hlowg
    · norm_num at hlowg
    · norm_num at hlowg
    · exfalso
      revert hlow hmod5
      interval_cases j <;> decide
    · exfalso
      revert hlow hmod5
      interval_cases j <;> decide
    · rfl
    · exfalso
      have hWeq : W ⊓ autFixedSubgroup (conjV h g) = W :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hac, hWcard]; norm_num)
      have : u₀ ∈ W ⊓ autFixedSubgroup (conjV h g) := by rw [hWeq]; exact hu₀U.1
      exact hgu₀ (mem_autFixedSubgroup.mp this.2)
  have hgtrans := conj_mul_inv_eq_one_or_eq_of_card_eq_two_mul hcV hMV hgg (hWinv g)
    (by rw [hWcard, hWg]) hu₀U.1 hgu₀
  set r₀ : QuotientV.V z := conjV h g u₀ * u₀⁻¹ with hr₀def
  have hr₀1 : r₀ ≠ 1 := fun h1 => hgu₀ (mul_inv_eq_one.mp h1)
  have hr₀W : r₀ ∈ W := W.mul_mem (hWinv g u₀ hu₀U.1) (W.inv_mem hu₀U.1)
  have hgr₀ : conjV h g r₀ = r₀ := by
    have hff : conjV h g (conjV h g u₀) = u₀ := by rw [← MulAut.mul_apply, hgg]; rfl
    rw [hr₀def, map_mul, map_inv, hff]
    calc u₀ * (conjV h g u₀)⁻¹ = (conjV h g u₀ * u₀⁻¹)⁻¹ := by group
      _ = conjV h g u₀ * u₀⁻¹ := inv_eq_of_mul_eq_one_right (hMV _)
  have hσ31 : conjV h σ ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← hσ3, pow_orderOf_eq_one, map_one]
  have hinvσ : ∀ w ∈ W ⊓ autFixedSubgroup (conjV h sH),
      conjV h σ w ∈ W ⊓ autFixedSubgroup (conjV h sH) := by
    rintro w ⟨hwW, hws⟩
    refine ⟨hWinv σ w hwW, mem_autFixedSubgroup.mpr ?_⟩
    rw [← MulAut.mul_apply, hsσV, MulAut.mul_apply, mem_autFixedSubgroup.mp hws]
  have hmod3 := card_modEq_card_inf_autFixedSubgroup hσ31 hinvσ
  have heq3 : W ⊓ autFixedSubgroup (conjV h sH) ⊓ autFixedSubgroup (conjV h σ) =
      U ⊓ autFixedSubgroup (conjV h sH) := by
    rw [hUdef, inf_assoc, inf_comm (autFixedSubgroup (conjV h sH)), ← inf_assoc]
  rw [heq3] at hmod3
  have hUs : Nat.card ↥(U ⊓ autFixedSubgroup (conjV h sH)) = 2 := by
    have hl := card_le_card_inf_autFixedSubgroup_sq hcV hMV hss (hUinv sH hsσV)
    rw [hU4] at hl
    have hd : Nat.card ↥(U ⊓ autFixedSubgroup (conjV h sH)) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU4]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨c, hc, hcc⟩ := exists_eq_two_pow_of_dvd hd
    rw [hcc] at hl ⊢
    interval_cases c
    · norm_num at hl
    · rfl
    · exfalso
      have hUeq : U ⊓ autFixedSubgroup (conjV h sH) = U :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcc, hU4]; norm_num)
      have : u₀ ∈ U ⊓ autFixedSubgroup (conjV h sH) := by rw [hUeq]; exact hu₀U
      exact hsu₀ (mem_autFixedSubgroup.mp this.2)
  rw [hUs] at hmod3
  have hdvds : Nat.card ↥(W ⊓ autFixedSubgroup (conjV h sH)) ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hWcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨c, hc, hcc⟩ := exists_eq_two_pow_of_dvd hdvds
  have hlows := card_le_card_inf_autFixedSubgroup_sq hcV hMV hss (hWinv sH)
  rw [hWcard, hcc] at hlows
  rw [hcc] at hmod3 ⊢
  interval_cases c
  · norm_num at hlows
  · norm_num at hlows
  · norm_num at hlows
  · rfl
  · exact absurd hmod3 (by decide)
  ·
    exfalso
    have hstrans := conj_mul_inv_eq_one_or_eq_of_card_eq_two_mul hcV hMV hss (hWinv sH)
      (by rw [hWcard, hcc]; norm_num) hu₀U.1 hsu₀
    have hsr₀ : conjV h sH u₀ * u₀⁻¹ = r₀ := by rw [hr₀def, hgU u₀ hu₀U]
    have htW : ∀ w ∈ W, conjV h tH w * w⁻¹ = 1 ∨ conjV h tH w * w⁻¹ = r₀ := by
      intro w hw
      have hs := hstrans w hw
      rw [hsr₀] at hs
      have hg := hgtrans (conjV h sH w) (hWinv sH w hw)
      have hTt : conjV h tH w = conjV h g (conjV h sH w) := by rw [htgs, MulAut.mul_apply]
      have e : conjV h tH w * w⁻¹ =
          (conjV h g (conjV h sH w) * (conjV h sH w)⁻¹) * (conjV h sH w * w⁻¹) := by
        rw [hTt]; group
      rw [e]
      have hr₀2 : r₀ * r₀ = 1 := hMV r₀
      rcases hs with hs | hs <;> rcases hg with hg | hg <;> rw [hs, hg]
      · left; rw [one_mul]
      · right; rw [mul_one]
      · right; rw [one_mul]
      · left; exact hr₀2
    have htW1 : ∀ w ∈ W, conjV h tH w = w := by
      intro w hw
      rcases htW w hw with h1 | h1
      · exact mul_inv_eq_one.mp h1
      · exfalso
        have hw' : conjV h (sigma1Nine D) w ∈ W := hWinv _ w hw
        have h2 : conjV h tH (conjV h (sigma1Nine D) w) * (conjV h (sigma1Nine D) w)⁻¹ =
            conjV h (sigma1Nine D) r₀ := by
          rw [← h1, map_mul, map_inv, ← MulAut.mul_apply (QuotientV.V z) (conjV h tH), ht1V,
            MulAut.mul_apply]
        have h3 : conjV h (sigma1Nine D) r₀ ≠ 1 := by
          intro h0
          apply hr₀1
          have := congrArg (conjV h (sigma1Nine D))⁻¹ h0
          simpa using this
        rcases htW _ hw' with h4 | h4
        · exact h3 (h2 ▸ h4)
        · rw [h2] at h4
          have hmem : r₀ ∈ Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h (sigma1Nine D)) :=
            ⟨hr₀W, mem_autFixedSubgroup.mpr h4⟩
          rw [inf_Wsub_autFixedSubgroup_sigma1Nine (z := z) (D := D) h] at hmem
          exact hr₀1 (Subgroup.mem_bot.mp hmem)
    have htQP : qH D tH ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [htq]; exact Subgroup.mem_subgroupOf.mpr t_mem_Q
    have hT1 : conjV h tH = 1 := by
      apply MulEquiv.ext
      intro w
      have hvtop : w ∈ Fsub (z := z) (sigma1Nine D) ⊔ W := by
        rw [hWdef, sup_Fsub_Wsub_sigma1Nine (z := z) (D := D) h]
        exact Subgroup.mem_top w
      obtain ⟨f, hf, w', hw', rfl⟩ :=
        (CFSG.mem_sup_of_commute fun a _ b _ => (hcV a b : Commute a b)).mp hvtop
      rw [map_mul, conjV_eq_self_of_mem_Fsub_of_qH_mem_QP45 (z := z) D h hσ₂ hq₂ hEq htQP hf,
        htW1 w' hw']
      rfl
    have hq1 := qH_eq_one_of_conjV_eq_one (z := z) D h htQP hT1
    rw [htq] at hq1
    exact t_ne_one (congrArg Subtype.val hq1)
  · exact absurd hmod3 (by decide)

end FiveAndUVT

end CFSG.RankThree.GF2n.Parrott
