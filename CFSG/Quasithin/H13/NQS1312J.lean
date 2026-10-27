module

public import CFSG.Quasithin.H13.NQS1312G
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
public import CFSG.Quasithin.Background.E6TwentySeven
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

theorem c6List_cases' : ∀ e ∈ c6List, e = id6 ∨
    (mul6 e (mul6 e e) = id6 ∧ ∃ v < 64, vapp e v ≠ v ∧ vapp e v < 64) ∨
    (mul6 e e = id6 ∧ ((Finset.range 64).filter (fun v => vapp e v = v)).card ≤ 16) := by
  decide +kernel

theorem c6List_invol_mul : ∀ e ∈ c6List, ∀ e' ∈ c6List, mul6 e e = id6 → mul6 e' e' = id6 →
    e ≠ id6 → e' ≠ id6 → e ≠ e' →
    mul6 (mul6 e e') (mul6 (mul6 e e') (mul6 e e')) = id6 ∧
      ∃ v < 64, vapp (mul6 e e') v ≠ v ∧ vapp (mul6 e e') v < 64 := by
  decide +kernel

theorem c6List_lt : ∀ e ∈ c6List, ∀ v < 64, vapp e v < 64 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal_line (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf_line {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal_line (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

omit [Finite G] in
theorem card_le_two_mul_card_inf {A B : Subgroup G} {a : G} (ha : a ∈ A)
    (h : ∀ b ∈ A, b ∉ B → a⁻¹ * b ∈ B) : Nat.card A ≤ 2 * Nat.card (A ⊓ B : Subgroup G) := by
  set C := (A ⊓ B).subgroupOf A with hC
  have hsurj : Function.Surjective (fun i : Bool =>
      if i then (QuotientGroup.mk (⟨a, ha⟩ : A) : A ⧸ C) else (QuotientGroup.mk 1 : A ⧸ C)) := by
    intro q
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases hbB : b ∈ B
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [QuotientGroup.eq, hC, mem_subgroupOf]
      simpa using ⟨hb, hbB⟩
    · refine ⟨true, ?_⟩
      simp only [↓reduceIte]
      rw [QuotientGroup.eq, hC, mem_subgroupOf]
      exact ⟨A.mul_mem (A.inv_mem ha) hb, h b hb hbB⟩
  have hidx : C.index ≤ 2 := by
    calc C.index = Nat.card (A ⧸ C) := rfl
      _ ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
      _ = 2 := by simp
  have h1 := C.card_mul_index
  have h2 : Nat.card C = Nat.card (A ⊓ B : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _ hidx

theorem thompsonJ_le_of_fix {S Q V : Subgroup G} (hVQ : V ≤ Q) (hQS : Q ≤ S)
    (hQC : Q ≤ centralizer (V : Set G)) (hVe : IsElemAbelian 2 V)
    (hidx : ∀ a ∈ S, ∀ b ∈ S, a ∉ Q → b ∉ Q → a⁻¹ * b ∈ Q)
    (hfix : ∀ a ∈ S, a ∉ Q →
      4 * Nat.card (V ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ Nat.card V) :
    thompsonJ S ≤ Q := by
  refine GammaExtra.thompsonJ_le fun A hA => ?_
  by_contra hAQ
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.1 hAQ
  have haS : a ∈ S := hA.1 haA
  set A₀ := A ⊓ Q with hA₀
  have hAe := hA.2.1
  have hA₀e : IsElemAbelian 2 A₀ := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hAe.2 x hx.1⟩
    have h := congrArg Subtype.val (hAe.1.1.1 ⟨x, x.2.1⟩ ⟨y, y.2.1⟩)
    exact h
  have hBS : A₀ ⊔ V ≤ S := sup_le (inf_le_right.trans hQS) (hVQ.trans hQS)
  have hBe : IsElemAbelian 2 (A₀ ⊔ V) :=
    Setup.Campbell.isElemAbelian_sup hA₀e hVe fun x hx v hv =>
      (mem_centralizer_iff.1 (hQC hx.2) v hv).symm
  have hcard := hA.2.2 _ hBS hBe
  have h1 : Nat.card A ≤ 2 * Nat.card A₀ :=
    card_le_two_mul_card_inf haA fun b hb hbQ => hidx a haS b (hA.1 hb) haQ hbQ
  have hVn : A₀ ≤ normalizer (V : Set G) := fun x hx =>
    centralizer_le_normalizer_self V (hQC hx.2)
  have h2 := card_sup_mul_card_inf_line hVn
  rw [sup_comm, inf_comm] at h2
  have h3 : Nat.card (A₀ ⊓ V : Subgroup G) ≤
      Nat.card (V ⊓ centralizer ({a} : Set G) : Subgroup G) := by
    refine Subgroup.card_le_of_le fun v hv => ⟨hv.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h := congrArg Subtype.val (hAe.1.1.1 ⟨v, hv.1.1⟩ ⟨a, haA⟩)
    exact h
  have h4 := hfix a haS haQ
  have hpos : 0 < Nat.card (A₀ ⊓ V : Subgroup G) := Nat.card_pos
  have hA₀pos : 0 < Nat.card A₀ := Nat.card_pos
  have h5 : 4 * Nat.card A₀ * Nat.card (A₀ ⊓ V : Subgroup G) ≤
      Nat.card (A₀ ⊔ V : Subgroup G) * Nat.card (A₀ ⊓ V : Subgroup G) := by
    rw [h2]
    calc 4 * Nat.card A₀ * Nat.card (A₀ ⊓ V : Subgroup G)
        ≤ Nat.card A₀ * (4 * Nat.card (V ⊓ centralizer ({a} : Set G) : Subgroup G)) := by
          rw [mul_comm 4 (Nat.card A₀), mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ Nat.card A₀ * Nat.card V := Nat.mul_le_mul_left _ h4
      _ = Nat.card V * Nat.card A₀ := mul_comm _ _
  have h6 := Nat.le_of_mul_le_mul_right h5 hpos
  omega

omit [Finite G] in
theorem card_inf_centralizer_le {V : Subgroup G} [IsElementaryAbelian 2 V]
    {Φ : Additive V ≃ₗ[ZMod 2] W6} {n : G} (hn : n ∈ normalizer (V : Set G))
    {κ : GL (Fin 6) (ZMod 2)}
    (hκ : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin κ)
    {e : List ℕ} (he : (κ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e)
    (he64 : ∀ v < 64, vapp e v < 64)
    (hcount : ((Finset.range 64).filter (fun v => vapp e v = v)).card ≤ 16) :
    Nat.card (V ⊓ centralizer ({n} : Set G) : Subgroup G) ≤ 16 := by
  classical
  set F := (Finset.range 64).filter (fun v => vapp e v = v) with hF
  have hcode : ∀ w : W6, ∃ c < 64, vecOf c = w := exists_vecOf
  have hmem : ∀ x : (V ⊓ centralizer ({n} : Set G) : Subgroup G),
      Classical.choose (hcode (Φ (Additive.ofMul ⟨x, x.2.1⟩))) ∈ F := by
    intro x
    have hc := Classical.choose_spec (hcode (Φ (Additive.ofMul ⟨x, x.2.1⟩)))
    rw [hF, Finset.mem_filter, Finset.mem_range]
    refine ⟨hc.1, vecOf_injective (he64 _ hc.1) hc.1 ?_⟩
    have hxn : n * (x : G) * n⁻¹ = x := by
      have := mem_centralizer_singleton_iff.1 x.2.2
      rw [← this]
      group
    have h1 := phi_conj hn hκ x.2.1
    have h2 : (⟨n * (x : G) * n⁻¹, (mem_normalizer_iff.1 hn x).1 x.2.1⟩ : V) = ⟨x, x.2.1⟩ :=
      Subtype.ext hxn
    rw [h2] at h1
    rw [← glLin_vecOf_of_coe he, hc.2]
    exact h1.symm
  let f : (V ⊓ centralizer ({n} : Set G) : Subgroup G) → F := fun x =>
    ⟨Classical.choose (hcode (Φ (Additive.ofMul ⟨x, x.2.1⟩))), hmem x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : Classical.choose (hcode (Φ (Additive.ofMul ⟨x, x.2.1⟩))) =
        Classical.choose (hcode (Φ (Additive.ofMul ⟨y, y.2.1⟩))) := congrArg Subtype.val hxy
    have hx := Classical.choose_spec (hcode (Φ (Additive.ofMul ⟨x, x.2.1⟩)))
    have hy := Classical.choose_spec (hcode (Φ (Additive.ofMul ⟨y, y.2.1⟩)))
    have h2 : Φ (Additive.ofMul (⟨x, x.2.1⟩ : V)) = Φ (Additive.ofMul ⟨y, y.2.1⟩) := by
      rw [← hx.2, ← hy.2, h1]
    have h3 := congrArg Subtype.val (Additive.ofMul.injective (Φ.injective h2))
    exact Subtype.ext h3
  calc Nat.card (V ⊓ centralizer ({n} : Set G) : Subgroup G) ≤ Nat.card F :=
        Nat.card_le_card_of_injective f hf
    _ = F.card := Nat.card_eq_card_toFinset _ |>.trans (by simp)
    _ ≤ 16 := hcount

theorem exists_sylow_lineH
    (h1332 : Stmt13_3_2) {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V]
    (hH : QTH13 G T L) (hF : QTU3InternalFrame T L V z) {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k) :
    ∃ S : Subgroup G, IsSylowTwoOf S (lineH Φ) ∧ pCoreOf 2 (L ⊔ T) ≤ S ∧
      S ≤ normalizer (pCoreOf 2 (L ⊔ T) : Set G) ∧ S ≤ normalizer (L : Set G) ∧
      S ⊓ centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) ∧
      ∀ a ∈ S, ∀ b ∈ S, a ∉ pCoreOf 2 (L ⊔ T) → b ∉ pCoreOf 2 (L ⊔ T) →
        a⁻¹ * b ∈ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hVT, hVe, hV64, hVQ, -, hLV, hTV, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, -, -, -, hTI⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  set H := lineH Φ with hHdef
  set M := normalizer (L : Set G) with hM
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hQT : Q ≤ T := hTC ▸ inf_le_left
  have hQM : Q ≤ M := hQT.trans hTL
  have hCVH : centralizer (V : Set G) ≤ H := by
    refine Subgroup.centralizer_le ?_
    rintro _ (rfl | rfl)
    exacts [ptOf_mem _, ptOf_mem _]
  have hQH : Q ≤ H := hQC.trans hCVH
  have hHu : H ≤ centralizer ({ptOf Φ (vecOf 15)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hHM : M ⊓ H ≤ normalizer (V : Set G) := fun x hx =>
    hTI _ (ptOf_mem _) ptOf_fifteen_ne_one ⟨hx.1, hHu hx.2⟩
  have hcen : ∀ x ∈ H, x * ptOf Φ (vecOf 15) * x⁻¹ = ptOf Φ (vecOf 15) ∧
      x * ptOf Φ (vecOf 52) * x⁻¹ = ptOf Φ (vecOf 52) := by
    intro x hx
    rw [hHdef, lineH, mem_centralizer_iff] at hx
    refine ⟨?_, ?_⟩
    · rw [← hx _ (Set.mem_insert _ _)]; group
    · rw [← hx _ (Set.mem_insert_of_mem _ rfl)]; group
  obtain ⟨S, hQS, hS⟩ := exists_isSylowTwoOf_of_le (le_inf hQM hQH) hQp
  have hSp : IsPGroup 2 S := hS.2.1
  have hSMH : S ≤ M ⊓ H := hS.1
  have hSN : S ≤ normalizer (V : Set G) := hSMH.trans hHM
  have hSQ : S ⊓ centralizer (V : Set G) = Q := by
    refine le_antisymm ?_ (le_inf hQS hQC)
    exact (eq_of_isSylowTwoOf_le (isSylowTwoOf_Q hH hF) (le_inf hQS hQC)
      (inf_le_inf_right _ (hSMH.trans inf_le_left)) (hSp.to_le inf_le_left)).le
  have hSnQ : S ≤ normalizer (Q : Set G) := by
    intro s hs
    rw [← hSQ]
    exact inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
      normalizer_le_normalizer_centralizer V (hSN hs)⟩
  have hact : ∀ a (ha : a ∈ S), ∃ κ : GL (Fin 6) (ZMod 2), tau Φ ⟨a, hSN ha⟩ = κ ∧ ∃ e ∈ c6List,
      (κ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e := by
    intro a ha
    obtain ⟨κ, -, hκ, e, he, hκe⟩ := exists_c6List_of_centralizes hΦN (hSN ha)
      (hcen a (hSMH ha).2).1 (hcen a (hSMH ha).2).2
    exact ⟨κ, tau_eq_iff.2 hκ, e, he, hκe⟩
  have hinv : ∀ a (ha : a ∈ S), a ∉ Q → ∃ e ∈ c6List,
      ((tau Φ ⟨a, hSN ha⟩ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e ∧
        e ≠ id6 ∧ mul6 e e = id6 ∧
        ((Finset.range 64).filter (fun v => vapp e v = v)).card ≤ 16 := by
    intro a ha haQ
    obtain ⟨κ, hκ, e, he, hκe⟩ := hact a ha
    rw [hκ]
    rcases c6List_cases' e he with rfl | ⟨h3, hv⟩ | ⟨h2, hc⟩
    · exfalso
      apply haQ
      rw [← hSQ]
      refine ⟨ha, mem_centralizer_of_tau (Φ := Φ) (hSN ha) ?_⟩
      rw [hκ]
      exact Units.ext (by rw [hκe, colMat_id6, Units.val_one])
    · exact (false_of_tau_order_three hSp ha (hSN ha) (by rw [hκ]; exact hκe) h3 hv).elim
    · refine ⟨e, he, hκe, ?_, h2, hc⟩
      rintro rfl
      apply haQ
      rw [← hSQ]
      refine ⟨ha, mem_centralizer_of_tau (Φ := Φ) (hSN ha) ?_⟩
      rw [hκ]
      exact Units.ext (by rw [hκe, colMat_id6, Units.val_one])
  have hidx : ∀ a ∈ S, ∀ b ∈ S, a ∉ Q → b ∉ Q → a⁻¹ * b ∈ Q := by
    intro a ha b hb haQ hbQ
    obtain ⟨e, he, hae, he1, he2, -⟩ := hinv a ha haQ
    obtain ⟨e', he', hbe, he'1, he'2, -⟩ := hinv b hb hbQ
    have hab : a⁻¹ * b ∈ S := S.mul_mem (S.inv_mem ha) hb
    have hτ : tau Φ ⟨a⁻¹ * b, hSN hab⟩ = tau Φ ⟨a, hSN ha⟩ * tau Φ ⟨b, hSN hb⟩ := by
      have hsq : tau Φ ⟨a, hSN ha⟩ * tau Φ ⟨a, hSN ha⟩ = 1 :=
        Units.ext (by rw [Units.val_mul, hae, ← colMat_mul6, he2, colMat_id6, Units.val_one])
      have h1 : (⟨a⁻¹ * b, hSN hab⟩ : normalizer (V : Set G)) =
          (⟨a, hSN ha⟩ : normalizer (V : Set G))⁻¹ * ⟨b, hSN hb⟩ := rfl
      rw [h1, map_mul, map_inv, inv_eq_of_mul_eq_one_right hsq]
    by_cases hee : e = e'
    · subst hee
      rw [← hSQ]
      refine ⟨hab, mem_centralizer_of_tau (Φ := Φ) (hSN hab) ?_⟩
      rw [hτ]
      have : tau Φ ⟨a, hSN ha⟩ = tau Φ ⟨b, hSN hb⟩ := Units.ext (by rw [hae, hbe])
      rw [this]
      exact Units.ext (by rw [Units.val_mul, hbe, ← colMat_mul6, he'2, colMat_id6,
        Units.val_one])
    · obtain ⟨h3, hv⟩ := c6List_invol_mul e he e' he' he2 he'2 he1 he'1 hee
      exact (false_of_tau_order_three hSp hab (hSN hab)
        (by rw [hτ, Units.val_mul, hae, hbe, ← colMat_mul6]) h3 hv).elim
  have hVe' : IsElemAbelian 2 V := isElemAbelian_of_frame
  have hfix : ∀ a ∈ S, a ∉ Q →
      4 * Nat.card (V ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ Nat.card V := by
    intro a ha haQ
    obtain ⟨e, he, hae, -, -, hc⟩ := hinv a ha haQ
    have h16 := card_inf_centralizer_le (hSN ha) (tau_eq_iff.1 rfl) hae (c6List_lt e he) hc
    rw [hV64]
    omega
  have hJ : thompsonJ S ≤ Q := thompsonJ_le_of_fix hVQ hQS hQC hVe' hidx hfix
  have hJeq : thompsonJ Q = thompsonJ S := GammaExtra.thompsonJ_eq_of_le hJ hQS
  have hJ1 : thompsonJ Q ≠ ⊥ := by
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian Q
    have h1 := hA.2.2 V hVQ hVe'
    rw [hV64] at h1
    intro h0
    have hA0 : A = ⊥ := le_bot_iff.1 (h0 ▸ GammaExtra.le_thompsonJ hA)
    rw [hA0, card_bot] at h1
    omega
  have hNJ : normalizer (thompsonJ Q : Set G) ≤ M :=
    normalizer_le_of_le_Q h1332 hH hJ1 (hQp.to_le (GammaExtra.thompsonJ_le_self Q))
      (GammaExtra.thompsonJ_le_self Q)
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
        (GammaExtra.normalizer_le_normalizer_thompsonJ Q))
  have hNS : normalizer (S : Set G) ≤ M := by
    have h1 := GammaExtra.normalizer_le_normalizer_thompsonJ S
    rw [← hJeq] at h1
    exact h1.trans hNJ
  exact ⟨S, E6.isSylowTwoOf_of_normalizer_le hS (hSMH.trans inf_le_right)
    (hSMH.trans inf_le_left) hNS, hQS, hSnQ, hSMH.trans inf_le_left, hSQ, hidx⟩

end CFSG.Quasithin.H13.U3.NLine
