module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Irr
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem conjugate_commutator (X Y : Subgroup G) (g : G) :
    CFSG.conjugate ⁅X, Y⁆ g = ⁅CFSG.conjugate X g, CFSG.conjugate Y g⁆ :=
  Subgroup.map_commutator X Y _

theorem conjugate_conjugate_inv (X : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate X g) g⁻¹ = X := by
  rw [← SteinbergBS.conjugate_mul, mul_inv_cancel, SteinbergBS.conjugate_one]

theorem conjugate_eq_bot_iff {X : Subgroup G} {g : G} : CFSG.conjugate X g = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj g⁻¹).injective

theorem le_normalizer_commutator_left (H₁ H₂ : Subgroup G) :
    H₁ ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  refine LinearS3.le_normalizer_of_conj_mem fun k hk x hx => ?_
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have e : k * ⁅a, b⁆ * k⁻¹ = ⁅k * a, b⁆ * ⁅k, b⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k * a, H₁.mul_mem hk ha, b, hb, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨k, hk, b, hb, rfl⟩))
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

theorem commutator_mem_of_mem_pCoreOf [Finite G] {V V₁ L T H : Subgroup G}
    (hA : AlmostSpecialHyp V V₁ L T H) {x y : G} (hx : x ∈ conjClosure V H)
    (hy : y ∈ pCoreOf 2 H) : x * y * x⁻¹ * y⁻¹ ∈ V₁ := by
  have hU := hA.G22_one.2
  have hcc := hA.conjClosure_le_N
  have hyN : y ∈ Subgroup.normalizer (V₁ : Set G) :=
    hA.H_le (LieType.BorelTits.pCoreOf_le 2 H hy)
  have hxY : tmk V₁ ⟨x, hcc hx⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    (secImg_le_iff.1 hU) ⟨x, hcc hx⟩ hx
  have hyQ : tmk V₁ ⟨y, hyN⟩ ∈ tildeOf V₁ (pCoreOf 2 H) := mem_secImg.2 ⟨⟨y, hyN⟩, hy, rfl⟩
  exact commutator_mem_of_secMk_commute (mem_centralizer_of_mem_omegaOneCenterOf hxY hyQ).symm

theorem isSimpleGroup_and_nonabelian_of_mulEquiv {Q : Type} [Group Q]
    (h : Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :
    IsSimpleGroup Q ∧ ∃ a b : Q, a * b ≠ b * a := by
  have key : ∀ {X : Type} [Group X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      (Q ≃* X) → IsSimpleGroup Q ∧ ∃ a b : Q, a * b ≠ b * a := by
    intro X _ hX ⟨a, b, hab⟩ e
    refine ⟨e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  rcases h with he | he | he
  · obtain ⟨e⟩ := he
    exact key (alternatingGroup.isSimpleGroup (by norm_num [Nat.card_fin]))
      (alternatingGroup_nonabelian (by norm_num)) e
  · obtain ⟨e⟩ := he
    exact key isSimpleGroup_sl_four_zmod_two sl_four_zmod_two_nonabelian e
  · obtain ⟨e⟩ := he
    have hq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      CFSG.LieType.Universal.SpecialLinear.isQuasisimple 4 (ZMod 2) (by norm_num)
    have hZ := center_sl_zmod_two (n := 5) (by norm_num)
    obtain ⟨-, hs, a, b, hab⟩ := hq
    let f : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    refine key f.symm.isSimpleGroup ⟨f a, f b, fun h => hab ?_⟩ e
    have := congrArg f.symm h
    simpa using this

theorem solvRad_le_pCoreOf [Finite G] {K : Subgroup G}
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a) :
    solvRad K ≤ pCoreOf 2 K := by
  let π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let N : Subgroup ↥K := (solvRad K).subgroupOf K
  have hNn : N.Normal := solvRad_normal K
  have hNs : Group.IsSolvable N := by
    have := solvRad_isSolvable K
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le K)).symm.toMonoidHom) (MulEquiv.surjective _)
  have hNπ : (N.map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · intro x hx
    have hxN : (⟨x, solvRad_le K hx⟩ : ↥K) ∈ N := hx
    have h1 : π ⟨x, solvRad_le K hx⟩ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_map_of_mem π hxN
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine ⟨⟨x, solvRad_le K hx⟩, ?_, rfl⟩
    exact h1
  · exfalso
    have hrange : N.map π = (π.comp N.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : Group.IsSolvable ↥(N.map π) := by
      rw [hrange]
      exact Group.isSolvable_of_surjective (π.comp N.subtype).rangeRestrict_surjective
    rw [h] at h1
    have h2 : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom) (MulEquiv.surjective _)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h2) a b)

theorem exists_conjugate_eq_of_card_eq_two [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {g : G}
    {A₁ : Subgroup G} (hA₁ : A₁ ≤ CFSG.conjugate V g) (hA₁2 : Nat.card A₁ = 2) :
    ∃ k : G, CFSG.conjugate V k = CFSG.conjugate V g ∧ CFSG.conjugate V₁ k = A₁ := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hZV : CFSG.conjugate A₁ g⁻¹ ≤ V := by
    intro x hx
    rw [SteinbergBS.mem_conjugate_iff, inv_inv] at hx
    have h1 := SteinbergBS.mem_conjugate_iff.1 (hA₁ hx)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  have hZ2 : Nat.card ↥(CFSG.conjugate A₁ g⁻¹) = 2 ^ 1 := by
    rw [LinearS3.card_conjugate, hA₁2, pow_one]
  obtain ⟨l, hl, hlZ⟩ := lemma12_8_3_two h hV₁.1 hZV hV₁.2.1 hZ2
  refine ⟨l * g, ?_, ?_⟩
  · rw [SteinbergBS.conjugate_mul, SteinbergBS.conjugate_of_mem_normalizer (hLV hl)]
  · rw [SteinbergBS.conjugate_mul, hlZ, ← SteinbergBS.conjugate_mul, inv_mul_cancel,
      SteinbergBS.conjugate_one]

theorem commutator_eq_bot_of_conjugate_le [Finite G] (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h1293 : Lemma12_9_3One) (h1294 : Lemma12_9_4) (h1295 : Lemma12_9_5) (h1296 : Lemma12_9_6)
    (h1297 : Lemma12_9_7) {T L V : Subgroup G} {n : ℕ} (hcx : Cx1291 G T L V n) {g : G}
    (hAT : CFSG.conjugate V g ≤ T) : ⁅CFSG.conjugate V g, V⁆ = ⊥ := by
  classical
  by_contra hAV
  have h1298 := lemma12_9_8 h1222 h37 h38 h39 h1294 h1297
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  have : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2) }
  obtain ⟨V₁, hV₁⟩ := exists_tsub hT2 hsq hab hTV hcard 1 (by omega)
  obtain ⟨V₂, hV₂, hV₁₂⟩ := exists_tsub_two_of_one hT2 hsq hab hTV hcard (by omega) hV₁
  obtain ⟨W, hW⟩ := exists_tsub hT2 hsq hab hTV hcard (n - 1) (by omega)
  obtain ⟨hA₁2, hWAV⟩ :=
    card_inf_centralizer_eq_two_and_le_commutator h1222 h1297 h1298 hcx hAT hAV hW
  have hbotg := inf_conjugate_eq_bot_of_commutator_ne_bot h1298 hcx hAV
  have hF2 := inf_normalizer_eq_inf_centralizer h1222 h1298 hcx hAT hAV
  have hnle := not_le_centralizer_of_commutator_ne_bot hAV
  obtain ⟨k, hVk, hV₁k⟩ := exists_conjugate_eq_of_card_eq_two hcx.hyp hV₁ inf_le_left hA₁2
  rw [← hVk] at hAT hbotg hF2 hnle hWAV hAV hV₁k
  set V' := CFSG.conjugate V k⁻¹ with hV'def
  have hmem' : ∀ x, x ∈ V' ↔ k⁻¹ * x * k ∈ V := fun x => by
    rw [hV'def, SteinbergBS.mem_conjugate_iff, inv_inv]
  have hmemA : ∀ x ∈ V, k⁻¹ * x * k ∈ CFSG.conjugate V k := fun x hx => by
    rw [SteinbergBS.mem_conjugate_iff, show k * (k⁻¹ * x * k) * k⁻¹ = x by group]
    exact hx
  have hV'C : V' ≤ Subgroup.centralizer (V₁ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyA : k⁻¹ * y * k ∈ CFSG.conjugate V₁ k := by
      rw [SteinbergBS.mem_conjugate_iff, show k * (k⁻¹ * y * k) * k⁻¹ = y by group]
      exact hy
    rw [hV₁k] at hyA
    have h1 := Subgroup.mem_centralizer_iff.1 hyA.2 _ ((hmem' x).1 hx)
    calc y * x = k * ((k⁻¹ * y * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by rw [h1]
      _ = x * y := by group
  have hV'N : V' ≤ Subgroup.normalizer (V₁ : Set G) :=
    hV'C.trans (Subgroup.centralizer_le_normalizer _)
  have hVN' : V ≤ Subgroup.normalizer (V' : Set G) := by
    intro v hv
    rw [hV'def, mem_normalizer_conjugate_iff, inv_inv]
    exact hTV (hAT (hmemA v hv))
  have hbot' : V ⊓ V' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : k⁻¹ * x * k ∈ V ⊓ CFSG.conjugate V k := ⟨(hmem' x).1 hx.2, hmemA x hx.1⟩
    rw [hbotg, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hVV' : ⁅V, V'⁆ = CFSG.conjugate ⁅CFSG.conjugate V k, V⁆ k⁻¹ := by
    rw [conjugate_commutator, conjugate_conjugate_inv]
  have hVV'ne : ⁅V, V'⁆ ≠ ⊥ := by
    rw [hVV', Ne, conjugate_eq_bot_iff]
    exact hAV
  set W' := CFSG.conjugate W k⁻¹ with hW'def
  have hW'VV : W' ≤ ⁅V, V'⁆ := by
    rw [hVV']
    exact LinearS3.conjugate_mono hWAV _
  have hW'V' : W' ≤ V' := LinearS3.conjugate_mono hW.1 _
  have hcW' : Nat.card W' = 2 ^ (n - 1) := by rw [LinearS3.card_conjugate, hW.2.1]
  have hcV' : Nat.card V' = 2 ^ n := by rw [LinearS3.card_conjugate, hcard]
  have hA := lemma12_8_4_one h1222 hcx.hyp hV₁ (isHzOne_normalizer h12213 hcx.hyp hV₁)
  have hUQ : ∀ x ∈ u128 V V₁, ∀ y ∈ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)),
      x * y * x⁻¹ * y⁻¹ ∈ V₁ := fun x hx y hy => commutator_mem_of_mem_pCoreOf hA hx hy
  have hUab : ∀ x ∈ u128 V V₁, ∀ y ∈ u128 V V₁, x * y = y * x := by
    have hU := h1294 G T L V n hcx V₁ hV₁
    exact fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(u128 V V₁)) ⟨y, hy⟩)
  have hVU : V ≤ u128 V V₁ := le_conjClosure V _
  have hG₁U : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    le_normalizer_conjClosure V _
  have hUQle : u128 V V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hA.conjClosure_le_N hG₁U
      (hT2.to_le hA.G22_three.1)
  have hG₁Q : Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQG₁ : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.normalizer (V₁ : Set G) := LieType.BorelTits.pCoreOf_le 2 _
  have hUC : u128 V V₁ ≤ Subgroup.centralizer (V : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hUab v (hVU hv) u hu
  have hVV'U : ⁅V, V'⁆ ≤ u128 V V₁ := by
    rw [Subgroup.commutator_le]
    intro v hv v' hv'
    rw [commutatorElement_def, show v * v' * v⁻¹ * v'⁻¹ = v * (v' * v⁻¹ * v'⁻¹) by group]
    exact mul_mem (hVU hv) ((Subgroup.mem_normalizer_iff.1 (hG₁U (hV'N hv')) _).1
      (inv_mem (hVU hv)))
  have hW'U : W' ≤ u128 V V₁ := hW'VV.trans hVV'U
  have hQN' : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ Subgroup.normalizer (V' : Set G) := by
    intro y hy
    obtain ⟨R, hRV₁, -, hcardW'⟩ := exists_commutator_image (A := W') (W := V₁) (v := y)
      (fun a ha b hb => hab a (hV₁.1 ha) b (hV₁.1 hb))
      (fun a ha w hw => (Subgroup.mem_centralizer_iff.1 (hV'C (hW'V' ha)) w hw).symm)
      (fun a ha => hUQ a (hW'U ha) y hy)
    set B := W' ⊓ Subgroup.centralizer ({y} : Set G) with hB
    have hcardB : 4 ≤ Nat.card B := by
      have h1 := Subgroup.card_le_of_le hRV₁
      rw [hV₁.2.1, pow_one] at h1
      rw [hcW'] at hcardW'
      have h2 : 2 ^ (n - 1) ≤ 2 * Nat.card B := by
        rw [hcardW']
        exact Nat.mul_le_mul_right _ h1
      have h3 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by rw [← pow_succ']; congr 1; omega
      rw [h3] at h2
      have h4 := Nat.le_of_mul_le_mul_left h2 (by norm_num)
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ Nat.card B := h4
    have hBc : ¬ IsCyclic B := LinearS3.not_isCyclic_of_four_le
      (fun x hx => LinearS3.sq_eq_one_of_mem_conjugate (hW'V' hx.1)) hcardB
    have hN := LinearS3.centralizer_le_normalizer_conjugate
      (fun B hB hc => centralizer_le_normalizer_of_not_isCyclic h1222 h1297 hcx hB hc) k⁻¹
      (inf_le_left.trans hW'V') hBc
    refine hN (Subgroup.mem_centralizer_iff.2 fun b hb => ?_)
    exact (Subgroup.mem_centralizer_iff.1 hb.2 y rfl).symm
  have hV'QU : V' ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ u128 V V₁ := by
    have hW'X : W' ≤ V' ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
      le_inf hW'V' (hW'U.trans hUQle)
    have hXne : V' ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ V' := by
      intro hX
      apply hVV'ne
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv v' hv'
      have hv'Q : v' ∈ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
        rw [← hX] at hv'
        exact hv'.2
      have h1 : v * v' * v⁻¹ * v'⁻¹ ∈ V₁ := hUQ v (hVU hv) v' hv'Q
      have h2 : v * v' * v⁻¹ * v'⁻¹ ∈ V' :=
        V'.mul_mem ((Subgroup.mem_normalizer_iff.1 (hVN' hv) v').1 hv') (V'.inv_mem hv')
      have h3 : v * v' * v⁻¹ * v'⁻¹ ∈ V ⊓ V' := ⟨hV₁.1 h1, h2⟩
      rw [hbot'] at h3
      rw [commutatorElement_def]
      exact h3
    have hXeq : V' ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) = W' := by
      refine (Subgroup.eq_of_le_of_card_ge hW'X ?_).symm
      have hdvd := Subgroup.card_dvd_of_le
        (inf_le_left : V' ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ V')
      rw [hcV'] at hdvd
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hge := Subgroup.card_le_of_le hW'X
      rw [hcW', hjeq] at hge
      have hjn : j ≠ n := by
        intro hjn
        apply hXne
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hjeq, hcV', hjn]
      have hj1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hge
      rw [hjeq, hcW', show j = n - 1 by omega]
    rw [hXeq]
    exact hW'U
  have hQV'U : ∀ y ∈ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)), ∀ v' ∈ V',
      y * v' * y⁻¹ * v'⁻¹ ∈ u128 V V₁ := by
    intro y hy v' hv'
    refine hV'QU ⟨V'.mul_mem ((Subgroup.mem_normalizer_iff.1 (hQN' hy) v').1 hv')
      (V'.inv_mem hv'), ?_⟩
    rw [show y * v' * y⁻¹ * v'⁻¹ = y * (v' * y⁻¹ * v'⁻¹) by group]
    exact mul_mem hy ((Subgroup.mem_normalizer_iff.1 (hG₁Q (hV'N hv')) _).1 (inv_mem hy))
  obtain ⟨K₁, hLK₁, hK₁c, hK₁n⟩ := h1293 G T L V n hcx V₁ hV₁
  obtain ⟨⟨hCM, -⟩, hK₁iso, -⟩ := h1295 G T L V n hcx V₁ K₁ hV₁ hLK₁ hK₁c
  obtain ⟨hne₂, -⟩ := h1296 G T L V n hcx V₁ V₂ K₁ hV₁ hV₂ hV₁₂ hLK₁ hK₁c
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_of_mem_cComp (show K₁ ∈ cComp _ from hK₁c)
  obtain ⟨hsK, hnabK⟩ := isSimpleGroup_and_nonabelian_of_mulEquiv hK₁iso
  have hKV'nle : ¬ ⁅K₁, V'⁆ ≤ pCoreOf 2 K₁ := by
    intro hle
    have hV'CM : V' ≤ centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (V₁ : Set G)) K₁ := by
      intro v' hv'
      refine ⟨hV'N hv', (hK₁n.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
        (hV'N hv'), fun u hu => ?_⟩
      have h1 := hle (Subgroup.commutator_mem_commutator hu hv')
      rw [commutatorElement_def] at h1
      have h2 := (pCoreOf 2 K₁).inv_mem h1
      rwa [show (u * v' * u⁻¹ * v'⁻¹)⁻¹ = v' * u * v'⁻¹ * u⁻¹ by group] at h2
    have hV'V : V' ≤ Subgroup.normalizer (V : Set G) := by
      intro m hm
      rcases hyp.ti_of_1222 h1222 (hCM (hV'CM hm)) with h | h
      · exact SteinbergBS.mem_normalizer_of_conjugate_eq h
      · exfalso
        have h1 : V₁ ≤ V ⊓ CFSG.conjugate V m := le_inf hV₁.1 fun x hx => by
          rw [SteinbergBS.mem_conjugate_iff]
          exact hV₁.1 ((Subgroup.mem_normalizer_iff.1 (hV'N hm) x).1 hx)
        rw [h, le_bot_iff] at h1
        have h2 := hV₁.2.1
        rw [h1, Subgroup.card_bot] at h2
        norm_num at h2
    apply hnle
    rw [← inf_eq_left, ← hF2, inf_eq_left]
    intro v hv
    rw [mem_normalizer_conjugate_iff]
    exact hV'V ((hmem' _).2 (by rw [show k⁻¹ * (k * v * k⁻¹) * k = v by group]; exact hv))
  have hK₁eq : ⁅K₁, V'⁆ = K₁ := by
    have hNK : ⁅K₁, V'⁆ ≤ K₁ := by
      rw [Subgroup.commutator_le]
      intro x hx v' hv'
      rw [commutatorElement_def, show x * v' * x⁻¹ * v'⁻¹ = x * (v' * x⁻¹ * v'⁻¹) by group]
      exact mul_mem hx ((Subgroup.mem_normalizer_iff.1 (hK₁n (hV'N hv')) _).1 (inv_mem hx))
    by_contra hne
    have hnorm : (⁅K₁, V'⁆.subgroupOf K₁).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 (le_normalizer_commutator_left K₁ V')
    have hrad := le_solvRad_of_subnormal_lt (show K₁ ∈ cComp _ from hK₁c)
      (A3.subnormal_of_normal hNK hnorm) (lt_of_le_of_ne hNK hne)
    exact hKV'nle (hrad.trans (solvRad_le_pCoreOf hsK hnabK))
  have hK₁Q : K₁ ≤ centralizerMod (u128 V V₁) (Subgroup.normalizer (V₁ : Set G))
      (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) := by
    rw [← hK₁eq, Subgroup.commutator_le]
    intro x hx v' hv'
    have hxG₁ := hK₁G₁ hx
    have hv'G₁ := hV'N hv'
    refine ⟨?_, hG₁U (mul_mem (mul_mem (mul_mem hxG₁ hv'G₁) (inv_mem hxG₁)) (inv_mem hv'G₁)),
      fun y hy => ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxG₁ hv'G₁) (inv_mem hxG₁)) (inv_mem hv'G₁)
    ·
      have hc : ∀ z ∈ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)),
          v' * z * v'⁻¹ * z⁻¹ ∈ u128 V V₁ := fun z hz => by
        have h1 := (u128 V V₁).inv_mem (hQV'U z hz v' hv')
        rwa [show (z * v' * z⁻¹ * v'⁻¹)⁻¹ = v' * z * v'⁻¹ * z⁻¹ by group] at h1
      have hz : x⁻¹ * y * x ∈ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
        have := (Subgroup.mem_normalizer_iff.1 (hG₁Q (inv_mem hxG₁)) y).1 hy
        rwa [inv_inv] at this
      have h1 : x * (v' * (x⁻¹ * y * x) * v'⁻¹ * (x⁻¹ * y * x)⁻¹) * x⁻¹ ∈ u128 V V₁ :=
        (Subgroup.mem_normalizer_iff.1 (hG₁U hxG₁) _).1 (hc _ hz)
      have he : v'⁻¹ * (y * v' * y⁻¹ * v'⁻¹) * v'⁻¹⁻¹ ∈ u128 V V₁ :=
        (Subgroup.mem_normalizer_iff.1 (hG₁U (inv_mem hv'G₁)) _).1 (hQV'U y hy v' hv')
      have hfG₁ : x * v' * x⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) :=
        mul_mem (mul_mem hxG₁ hv'G₁) (inv_mem hxG₁)
      have h2 : (x * v' * x⁻¹) * (v'⁻¹ * (y * v' * y⁻¹ * v'⁻¹) * v'⁻¹⁻¹) * (x * v' * x⁻¹)⁻¹ ∈
          u128 V V₁ := (Subgroup.mem_normalizer_iff.1 (hG₁U hfG₁) _).1 he
      have h4 : ⁅x, v'⁆ * y * ⁅x, v'⁆⁻¹ * y⁻¹ =
          ((x * v' * x⁻¹) * (v'⁻¹ * (y * v' * y⁻¹ * v'⁻¹) * v'⁻¹⁻¹) * (x * v' * x⁻¹)⁻¹) *
            (x * (v' * (x⁻¹ * y * x) * v'⁻¹ * (x⁻¹ * y * x)⁻¹) * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [h4]
      exact mul_mem h2 h1
  have hQC : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ Subgroup.centralizer (V : Set G) :=
    L1299.le_centralizer_of_commutator_le_lOne hcx.hyp hV₁ hQG₁
      (fun v hv y hy => by
        have h1 := V₁.inv_mem (hUQ v (hVU hv) y hy)
        rwa [show (v * y * v⁻¹ * y⁻¹)⁻¹ = y * v * y⁻¹ * v⁻¹ by group] at h1)
      (fun l hl y hy => hUC ((hK₁Q (hLK₁ hl)).2.2 y hy))
  have hO₂ : pCoreOf 2 K₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁G₁)
      (hK₁n.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  apply hne₂
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  exact (Subgroup.mem_centralizer_iff.1 (hQC (hO₂ hp)) v (hV₂.1 hv)).symm

end CFSG.Quasithin.H13
