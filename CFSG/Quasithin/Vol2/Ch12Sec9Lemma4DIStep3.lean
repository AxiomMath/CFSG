module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts2
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep2

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

section Transport

variable {G : Type} [Group G] [Finite G]

theorem mem_stabS_iff {I : Type} [AddCommGroup I] [Module (ZMod 2) I] {S : Submodule (ZMod 2) I}
    {g : I ≃ₗ[ZMod 2] I} : g ∈ stabS S ↔ ∀ v, v ∈ S ↔ g v ∈ S := Iff.rfl

@[expose] noncomputable def linAct {V : Subgroup G} [IsMulCommutative ↥V]
    [Module (ZMod 2) (Additive ↥V)] :
    Subgroup.normalizer (V : Set G) →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
  linHom.comp (conjAct V)

theorem coe_linAct {V : Subgroup G} [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)]
    (g : Subgroup.normalizer (V : Set G)) (x : Additive ↥V) :
    ((Additive.toMul (linAct g x) : ↥V) : G) =
      (g : G) * ((Additive.toMul x : ↥V) : G) * (g : G)⁻¹ := by
  show ((conjAct V g (Additive.toMul x) : ↥V) : G) = _
  rw [AutOn.coe_conjAct_apply]

theorem linHom_surj {V : Subgroup G} [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)]
    (σ' : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) : ∃ σ : MulAut ↥V, linHom σ = σ' := by
  refine ⟨{ toFun := fun x => Additive.toMul (σ' (Additive.ofMul x))
            invFun := fun x => Additive.toMul (σ'.symm (Additive.ofMul x))
            left_inv := fun x => by simp
            right_inv := fun x => by simp
            map_mul' := fun x y => by simp }, ?_⟩
  ext x
  simp [linHom, linOfMulAut_apply]

theorem exists_lift {V : Subgroup G} [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)]
    {X V₁ : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G)) (htop : autOn X V = ⊤)
    (hV₁ : V₁ ≤ V) {γ : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V}
    (hγ : γ ∈ stabS (subOf (V := V) V₁)) :
    ∃ l : G, ∃ hl : l ∈ Subgroup.normalizer (V : Set G), l ∈ X ∧
      l ∈ Subgroup.normalizer (V₁ : Set G) ∧ linAct (V := V) ⟨l, hl⟩ = γ := by
  obtain ⟨σ, hσ⟩ := linHom_surj γ
  have hmem : σ ∈ autOn X V := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxX, hxσ⟩ := AutOn.mem_autOn_iff_exists.1 hmem
  have hlin : linAct (V := V) (⟨x, hx⟩ : Subgroup.normalizer (V : Set G)) = γ := by
    rw [← hσ, ← hxσ]; rfl
  refine ⟨x, hx, hxX, ?_, hlin⟩
  have hγ' := mem_stabS_iff.1 hγ
  have hgen : ∀ h : G, ∀ hV : h ∈ V, (h ∈ V₁ ↔ x * h * x⁻¹ ∈ V₁) := by
    intro h hV
    have hv := hγ' (Additive.ofMul ⟨h, hV⟩)
    have hcoe : ((Additive.toMul (γ (Additive.ofMul ⟨h, hV⟩)) : ↥V) : G) = x * h * x⁻¹ := by
      rw [← hlin, coe_linAct]
      rfl
    have e1 : h ∈ V₁ ↔ (Additive.ofMul (⟨h, hV⟩ : ↥V) : Additive ↥V) ∈ subOf (V := V) V₁ := by
      rw [mem_subOf (V := V)]
      rfl
    have e2 : x * h * x⁻¹ ∈ V₁ ↔ ((Additive.toMul (γ (Additive.ofMul ⟨h, hV⟩)) : ↥V) : G) ∈ V₁ := by
      rw [hcoe]
    have e3 : (γ (Additive.ofMul ⟨h, hV⟩) ∈ subOf (V := V) V₁) ↔
        ((Additive.toMul (γ (Additive.ofMul ⟨h, hV⟩)) : ↥V) : G) ∈ V₁ := mem_subOf (V := V)
    rw [e1, e2, ← e3]
    exact hv
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhV : h ∈ V := hV₁ hh
    exact (hgen h hhV).1 hh
  · intro hh
    have hxV : x * h * x⁻¹ ∈ V := hV₁ hh
    have hhV : h ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 hx h).2 hxV
      exact this
    exact (hgen h hhV).2 hh

theorem exists_pow_two_pow_inv {Γ : Type} [Group Γ] (γ : Γ) (hγ : IsOfFinOrder γ)
    (hodd : Odd (orderOf γ)) (k : ℕ) : ∃ s : ℕ, (γ ^ (2 ^ k)) ^ s = γ := by
  have hc : 0 < orderOf γ := hγ.orderOf_pos
  have hcop : Nat.Coprime (2 ^ k) (orderOf γ) := by
    apply Nat.Coprime.pow_left
    exact Nat.coprime_two_left.2 hodd
  refine ⟨(2 ^ k) ^ (Nat.totient (orderOf γ) - 1), ?_⟩
  rw [← pow_mul]
  have htot : 0 < Nat.totient (orderOf γ) := Nat.totient_pos.2 hc
  have e1 : 2 ^ k * (2 ^ k) ^ (Nat.totient (orderOf γ) - 1) = (2 ^ k) ^ Nat.totient (orderOf γ) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [e1]
  have hmod : (2 ^ k) ^ Nat.totient (orderOf γ) ≡ 1 [MOD orderOf γ] :=
    Nat.ModEq.pow_totient hcop
  calc γ ^ (2 ^ k) ^ Nat.totient (orderOf γ) = γ ^ ((2 ^ k) ^ Nat.totient (orderOf γ) % orderOf γ) :=
        (pow_mod_orderOf γ _).symm
    _ = γ ^ (1 % orderOf γ) := congrArg (γ ^ ·) hmod
    _ = γ ^ 1 := pow_mod_orderOf γ 1
    _ = γ := pow_one γ

theorem odd_mem_image_oTwoUpper {V : Subgroup G} [IsMulCommutative ↥V]
    [Module (ZMod 2) (Additive ↥V)] {X V₁ : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (htop : autOn X V = ⊤) (hV₁ : V₁ ≤ V)
    {γ : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V} (hγ : γ ∈ stabS (subOf (V := V) V₁))
    (hodd : Odd (orderOf γ)) :
    ∃ l : G, ∃ hl : l ∈ Subgroup.normalizer (V : Set G),
      l ∈ oTwoUpper (X ⊓ Subgroup.normalizer (V₁ : Set G)) ∧ linAct (V := V) ⟨l, hl⟩ = γ := by
  haveI hfin : Finite (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    Finite.of_injective (fun f : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V =>
      (f : Additive ↥V → Additive ↥V)) DFunLike.coe_injective
  have hγfin : IsOfFinOrder γ := isOfFinOrder_of_finite γ
  obtain ⟨l₀, hl₀, hl₀X, hl₀N, hlin₀⟩ := exists_lift hXV htop hV₁ hγ
  set x : Subgroup.normalizer (V : Set G) := ⟨l₀, hl₀⟩ with hxdef
  have hl₀fin : IsOfFinOrder l₀ := isOfFinOrder_of_finite l₀
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hl₀fin.orderOf_pos.ne'
  obtain ⟨s, hs⟩ := exists_pow_two_pow_inv γ hγfin hodd k
  have hodd_e : Odd (orderOf (l₀ ^ (2 ^ k))) := by
    have h1 : (l₀ ^ (2 ^ k)) ^ m = 1 := by
      rw [← pow_mul, ← hn, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  have hmem_e : l₀ ^ (2 ^ k) ∈ oTwoUpper (X ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    Subgroup.subset_closure ⟨(X ⊓ Subgroup.normalizer (V₁ : Set G)).pow_mem
      (Subgroup.mem_inf.2 ⟨hl₀X, hl₀N⟩) _, hodd_e⟩
  refine ⟨l₀ ^ (2 ^ k * s), (Subgroup.normalizer (V : Set G)).pow_mem hl₀ _, ?_, ?_⟩
  · rw [pow_mul]
    exact Subgroup.pow_mem _ hmem_e s
  · have hx : (⟨l₀ ^ (2 ^ k * s), (Subgroup.normalizer (V : Set G)).pow_mem hl₀ _⟩ :
        Subgroup.normalizer (V : Set G)) = x ^ (2 ^ k * s) := by
      apply Subtype.ext
      simp [hxdef]
    rw [hx, map_pow, hxdef, hlin₀, pow_mul, hs]

end Transport

section Step2Q

variable {G : Type} [Group G] [Finite G]

theorem step2_q {K₁ V V₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (D : HatModelU (u128 V V₁)) {q : D.V → ZMod 2}
    (hcardO : Nat.card (orthogonalSubgroupOf q) = 40320)
    (hno2 : ∀ N : Subgroup (D.V ≃ₗ[ZMod 2] D.V), N ≤ orthogonalSubgroupOf q →
      (∀ γ ∈ orthogonalSubgroupOf q, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → Nat.card N ≠ 2)
    (hΓO : D.img (Subgroup.normalizer (V₁ : Set G)) ≤ orthogonalSubgroupOf q)
    (hidx : (D.img (Subgroup.normalizer (V₁ : Set G))).relIndex (orthogonalSubgroupOf q) ≤ 2)
    (himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2) :
    (D.img K₁).relIndex (orthogonalSubgroupOf q) = 2 ∧ D.img K₁ ≤ orthogonalSubgroupOf q ∧
      Nat.card (D.img K₁) = 20160 ∧
      ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
        D.ρ ⟨k, hkN⟩ = 1 ↔ k ∈ pCoreOf 2 K₁ := by
  classical
  have hK₁U := K₁_le_normalizer_u128 (V := V) hK
  set Γ := D.img (Subgroup.normalizer (V₁ : Set G)) with hΓdef
  set Kd := D.img K₁ with hKd
  set O := orthogonalSubgroupOf q with hOdef
  set ρK : ↥K₁ →* (D.V ≃ₗ[ZMod 2] D.V) := D.ρ.comp (Subgroup.inclusion hK₁U) with hρK
  have hrange : ρK.range = Kd := (L1294.img_eq_range D hK₁U).symm
  have hKΓ : Kd ≤ Γ := L1294.img_mono D (K₁_le_normalizer hK)
  have hKO : Kd ≤ O := le_trans hKΓ hΓO
  have hO : ρK.range ≤ O := by rw [hrange]; exact hKO
  have hrelΓ : Γ.relIndex O * Nat.card Γ = 40320 := by
    have h := Subgroup.relIndex_mul_card (H := Γ) (K := O)
    rw [inf_eq_left.2 hΓO, hcardO] at h
    exact h
  have hΓcard : 20160 ≤ Nat.card Γ := by
    have hpos : 0 < Nat.card Γ := by
      rcases Nat.eq_zero_or_pos (Nat.card Γ) with h0 | h0
      · rw [h0, mul_zero] at hrelΓ; omega
      · exact h0
    nlinarith
  have hrelK : Kd.relIndex Γ * Nat.card Kd = Nat.card Γ := by
    have h := Subgroup.relIndex_mul_card (H := Kd) (K := Γ)
    rw [inf_eq_left.2 hKΓ] at h
    exact h
  have hle : Nat.card Γ ≤ 2 * Nat.card Kd := by
    rw [← hrelK]
    exact Nat.mul_le_mul_right _ himg
  have hbigKd : 10080 ≤ Nat.card Kd := by omega
  have hbig : 10080 ≤ Nat.card ρK.range := by
    rw [hrange]
    exact hbigKd
  have hker : ρK.ker = CFSG.pCore 2 ↥K₁ :=
    ker_eq_of_perfect (CFSG.pCore 2 ↥K₁) CFSG.pCore_isPGroup (isSimpleGroup_quot hK4)
      (index_pCore_eq hK4) (perfect_top_of_cComp hK) q ρK hO hcardO hbig hno2
  have hcardK : Nat.card Kd = 20160 := by
    rw [← hrange]
    have h1 : Nat.card ρK.range = ρK.ker.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρK).toEquiv).symm
    rw [h1, hker, index_pCore_eq hK4]
  refine ⟨?_, hKO, hcardK, ?_⟩
  · have h := Subgroup.relIndex_mul_card (H := Kd) (K := O)
    rw [inf_eq_left.2 hKO, hcardO, hcardK] at h
    exact Nat.eq_of_mul_eq_mul_right (show 0 < 20160 by norm_num) (h.trans (by norm_num))
  · intro k hk hkN
    have hmem : (⟨k, hk⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ ↔ k ∈ pCoreOf 2 K₁ := by
      constructor
      · intro h
        exact Subgroup.mem_map.2 ⟨⟨k, hk⟩, h, rfl⟩
      · intro h
        obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.1 h
        have : x = ⟨k, hk⟩ := Subtype.ext hxk
        rw [← this]
        exact hx
    have hkerρ : D.ρ ⟨k, hkN⟩ = 1 ↔ (⟨k, hk⟩ : ↥K₁) ∈ ρK.ker := by
      rw [MonoidHom.mem_ker]
      rfl
    rw [hkerρ, hker, hmem]

end Step2Q

section Singular

variable {G : Type} [Group G] [Finite G]

theorem finrank_of_natCard {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M] {n : ℕ}
    (h : Nat.card M = 2 ^ n) : Module.finrank (ZMod 2) M = n := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  rw [Nat.card_zmod] at h1
  exact Nat.pow_right_injective le_rfl (h1.symm.trans h)

theorem natCard_subOf {V W : Subgroup G} [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)]
    (hWV : W ≤ V) : Nat.card (subOf (V := V) W) = Nat.card W := by
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨((x.1.toMul : ↥V) : G), mem_subOf.1 x.2⟩
      invFun := fun y => ⟨Additive.ofMul ⟨(y : G), hWV y.2⟩, mem_subOf.2 (by simp)⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }

end Singular

theorem card_ker_functional {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (f : M →ₗ[ZMod 2] ZMod 2) (hf : ∃ x, f x ≠ 0) :
    Nat.card (LinearMap.ker f) * 2 = Nat.card M := by
  have hsurj : Function.Surjective f := by
    obtain ⟨x, hx⟩ := hf
    intro c
    have h1 : f x = 1 := by
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from fun c => by revert c; decide) (f x) with h | h
      · exact absurd h hx
      · exact h
    exact ⟨c • x, by rw [map_smul, h1, smul_eq_mul, mul_one]⟩
  have h1 := AddSubgroup.card_mul_index (LinearMap.ker f).toAddSubgroup
  have h2 : (LinearMap.ker f).toAddSubgroup.index = 2 := by
    have h3 := AddSubgroup.index_ker (f : M →+ ZMod 2)
    have h4 : (f : M →+ ZMod 2).ker = (LinearMap.ker f).toAddSubgroup := rfl
    rw [h4] at h3
    rw [h3]
    rw [AddMonoidHom.range_eq_top.2 hsurj]
    simp
  rw [h2] at h1
  simpa [Nat.card_eq_fintype_card, mul_comm] using h1

section TotSing

variable {G : Type} [Group G] [Finite G]

theorem totally_singular (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (F5 : FactF5)
    {T L V V₁ V₂ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    (D : HatModelU (u128 V V₁)) {q : D.V → ZMod 2}
    (hq : ∀ v w, q (v + w) = q v + q w + D.B v w)
    (hΓO : D.img (Subgroup.normalizer (V₁ : Set G)) ≤ orthogonalSubgroupOf q) :
    ∀ v ∈ V, q (D.π v) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc, -⟩ := hcx.hyp.natural
  obtain ⟨hcard, hsq, -⟩ := hcx.hyp.card_sq
  haveI := hc
  letI : Module (ZMod 2) (Additive ↥V) := zmodModuleOf hsq
  have hV₁V : V₁ ≤ V := hs.v1.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hcx.hyp.hyp.irrPlus.2.2.1
  have htop : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One hcx.hyp
  have hUV : ∀ v ∈ V, v ∈ u128 V V₁ := fun v hv => le_conjClosure V _ hv
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  have hBV : ∀ a ∈ V, ∀ b ∈ V, D.B (D.π a) (D.π b) = 0 := by
    intro a ha b hb
    apply (D.B_spec a (hUV a ha) b (hUV b hb)).2
    rw [hcomm a ha b hb]
    group
  have hπV : ∀ a ∈ V, ∀ b ∈ V, D.π (a * b) = D.π a + D.π b := fun a ha b hb =>
    D.π_mul a (hUV a ha) b (hUV b hb)
  have hq0 : q 0 = 0 := by
    have h := hq 0 0
    have hB : D.B 0 0 = 0 := by simp
    rw [add_zero, hB, add_zero] at h
    calc q 0 = q 0 + q 0 := h
      _ = 0 := CharTwo.add_self_eq_zero _
  have hπV₁ : ∀ a ∈ V₁, D.π a = 0 := by
    intro a ha
    have haZ : a ∈ V ⊓ zU128 V V₁ := by
      rw [lemma12_8_8_three h1222 h12213 hs]
      exact ha
    exact (L128A.HatU.π_eq_zero_iff D (hUV a (hV₁V ha))).2 (Subgroup.mem_inf.1 haZ).2
  let ψ : Additive ↥V →+ ZMod 2 :=
    { toFun := fun x => q (D.π ((Additive.toMul x : ↥V) : G))
      map_zero' := by
        show q (D.π ((1 : ↥V) : G)) = 0
        rw [Subgroup.coe_one, L128A.HatU.π_one D, hq0]
      map_add' := fun x y => by
        show q (D.π (((Additive.toMul x : ↥V) : G) * ((Additive.toMul y : ↥V) : G))) =
          q (D.π ((Additive.toMul x : ↥V) : G)) + q (D.π ((Additive.toMul y : ↥V) : G))
        rw [hπV _ (Additive.toMul x).2 _ (Additive.toMul y).2, hq, hBV _ (Additive.toMul x).2 _
          (Additive.toMul y).2, add_zero] }
  let lam : Additive ↥V →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => q (D.π ((Additive.toMul x : ↥V) : G))
      map_add' := ψ.map_add
      map_smul' := fun c x => by
        rcases zmod_two_cases c with rfl | rfl
        · simp [hq0, L128A.HatU.π_one D]
        · simp }
  have hlam : ∀ x : Additive ↥V, lam x = q (D.π ((Additive.toMul x : ↥V) : G)) := fun x => rfl
  have hinv : ∀ (l : G) (hl : l ∈ Subgroup.normalizer (V : Set G)),
      l ∈ Subgroup.normalizer (V₁ : Set G) → ∀ v : Additive ↥V,
        lam (linAct (V := V) ⟨l, hl⟩ v) = lam v := by
    intro l hl hlV₁ v
    have hlU : l ∈ Subgroup.normalizer (u128 V V₁ : Set G) := le_normalizer_conjClosure V _ hlV₁
    have hρ : D.ρ ⟨l, hlU⟩ ∈ D.img (Subgroup.normalizer (V₁ : Set G)) :=
      L128A.HatU.rho_mem_img D hlV₁ hlU
    have hqρ : ∀ w, q (D.ρ ⟨l, hlU⟩ w) = q w := fun w => (hΓO hρ) w
    have hvU : ((Additive.toMul v : ↥V) : G) ∈ u128 V V₁ := hUV _ (Additive.toMul v).2
    have e := D.ρ_π ⟨l, hlU⟩ _ hvU
    rw [hlam, hlam, coe_linAct]
    exact (congrArg q e).symm.trans (hqρ _)
  have hle : oTwoUpper (stabS (subOf (V := V) V₁)) ≤ stabS (LinearMap.ker lam) := by
    unfold oTwoUpper
    rw [Subgroup.closure_le]
    rintro γ ⟨hγ, hodd⟩
    obtain ⟨l, hl, hlO, hlin⟩ := odd_mem_image_oTwoUpper hLV htop hV₁V hγ hodd
    have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) :=
      (Subgroup.mem_inf.1 ((oTwoUpper_le _) hlO)).2
    show γ ∈ stabS (LinearMap.ker lam)
    rw [mem_stabS_iff]
    intro v
    rw [← hlin]
    simp only [LinearMap.mem_ker]
    rw [hinv l hl hlV₁ v]
  have hlam0 : lam = 0 := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, lam x₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext fun x => h x)
    haveI : Finite (Additive ↥V) := by
      show Finite ↥V
      infer_instance
    haveI : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
    have h4 : Module.finrank (ZMod 2) (Additive ↥V) = 4 := finrank_of_natCard hcard
    have h1 : lam x₀ = 1 := by
      rcases zmod_two_cases (lam x₀) with h | h
      · exact absurd h hx₀
      · exact h
    have hrange : LinearMap.range lam = ⊤ := by
      rw [eq_top_iff]
      intro c _
      exact ⟨c • x₀, by rw [map_smul, h1, smul_eq_mul, mul_one]⟩
    have hX3 : Module.finrank (ZMod 2) (LinearMap.ker lam) = 3 := by
      have hc := card_ker_functional lam ⟨x₀, hx₀⟩
      have hc16 : Nat.card (Additive ↥V) = 2 ^ 4 := hcard
      apply finrank_of_natCard (n := 3)
      rw [hc16] at hc
      omega
    have hV₁1 : Module.finrank (ZMod 2) (subOf (V := V) V₁) = 1 :=
      finrank_of_natCard (by rw [natCard_subOf hV₁V]; exact hs.v1.2.1)
    have hV₁X : subOf (V := V) V₁ ≤ LinearMap.ker lam := by
      intro x hx
      rw [LinearMap.mem_ker]
      show q (D.π ((Additive.toMul x : ↥V) : G)) = 0
      rw [hπV₁ _ ((mem_subOf (V := V)).1 hx)]
      exact hq0
    exact F5 (Additive ↥V) h4 (subOf (V := V) V₁) hV₁1 (LinearMap.ker lam) hX3 hV₁X
      (fun γ hγ => mem_stabS_iff.1 (hle hγ))
  intro v hv
  have := congrArg (fun f => f (Additive.ofMul (⟨v, hv⟩ : ↥V))) hlam0
  simp only [LinearMap.zero_apply] at this
  rw [hlam] at this
  simpa using this

end TotSing

theorem card_ker_mul_card_range {M N : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    [AddCommGroup N] [Module (ZMod 2) N] (f : M →ₗ[ZMod 2] N) :
    Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) = Nat.card M := by
  have h1 := AddSubgroup.card_mul_index (LinearMap.ker f).toAddSubgroup
  have h2 : (LinearMap.ker f).toAddSubgroup.index = Nat.card (LinearMap.range f) := by
    have h3 := AddSubgroup.index_ker (f : M →+ N)
    have h4 : (f : M →+ N).ker = (LinearMap.ker f).toAddSubgroup := rfl
    rw [h4] at h3
    rw [h3]
    rfl
  rw [h2] at h1
  simpa [Nat.card_eq_fintype_card, mul_comm] using h1

section Main3

variable {G : Type} [Group G] [Finite G]

theorem step3_main (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (F5 : FactF5)
    {T L V V₁ V₂ K₁ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    (D : HatModelU (u128 V V₁)) {q : D.V → ZMod 2}
    (hq : ∀ v w, q (v + w) = q v + q w + D.B v w)
    (hΓO : D.img (Subgroup.normalizer (V₁ : Set G)) ≤ orthogonalSubgroupOf q)
    (hΩF4 : F4Out q D.B (D.img K₁)) :
    (∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
        D.ρ ⟨t, htU⟩ ∈ D.img K₁) ∧
    ∃ S : Submodule (ZMod 2) D.V, Module.finrank (ZMod 2) S = 3 ∧ (∀ s ∈ S, q s = 0) ∧
      (∀ v ∈ V, D.π v ∈ S) ∧ (∀ s ∈ S, ∃ v ∈ V, D.π v = s) ∧
      ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
        D.ρ ⟨t, htU⟩ ∈ stabS S := by
  have htot := totally_singular h1222 h12213 F5 hcx hs D hq hΓO
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc, -⟩ := hcx.hyp.natural
  obtain ⟨hcard, hsq, -⟩ := hcx.hyp.card_sq
  haveI := hc
  letI : Module (ZMod 2) (Additive ↥V) := zmodModuleOf hsq
  have hV₁V : V₁ ≤ V := hs.v1.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := (hcx.hyp.hyp.le_and_normalizes h1222).2
  have hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := hs.v1.2.2
  have hUV : ∀ v ∈ V, v ∈ u128 V V₁ := fun v hv => le_conjClosure V _ hv
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  have hπV : ∀ a ∈ V, ∀ b ∈ V, D.π (a * b) = D.π a + D.π b := fun a ha b hb =>
    D.π_mul a (hUV a ha) b (hUV b hb)
  have hπ1 : D.π 1 = 0 := L128A.HatU.π_one D
  have hπ0 : ∀ v ∈ V, D.π v = 0 ↔ v ∈ V₁ := by
    intro v hv
    constructor
    · intro h0
      have h1 : v ∈ V ⊓ zU128 V V₁ :=
        ⟨hv, (L128A.HatU.π_eq_zero_iff D (hUV v hv)).1 h0⟩
      rw [lemma12_8_8_three h1222 h12213 hs] at h1
      exact h1
    · intro hv1
      have h1 : v ∈ V ⊓ zU128 V V₁ := by
        rw [lemma12_8_8_three h1222 h12213 hs]
        exact hv1
      exact (L128A.HatU.π_eq_zero_iff D (hUV v hv)).2 (Subgroup.mem_inf.1 h1).2
  let φ : Additive ↥V →ₗ[ZMod 2] D.V :=
    { toFun := fun x => D.π ((Additive.toMul x : ↥V) : G)
      map_add' := fun x y => by
        show D.π (((Additive.toMul x : ↥V) : G) * ((Additive.toMul y : ↥V) : G)) = _
        exact hπV _ (Additive.toMul x).2 _ (Additive.toMul y).2
      map_smul' := fun c x => by
        rcases zmod_two_cases c with rfl | rfl
        · simp [hπ1]
        · simp }
  set S := LinearMap.range φ with hSdef
  have hkerφ : LinearMap.ker φ = subOf (V := V) V₁ := by
    ext x
    rw [LinearMap.mem_ker, mem_subOf (V := V)]
    exact hπ0 _ (Additive.toMul x).2
  have hS8 : Nat.card S = 8 := by
    have hc1 : Nat.card (LinearMap.ker φ) * Nat.card S = Nat.card (Additive ↥V) :=
      card_ker_mul_card_range φ
    have hc2 : Nat.card (LinearMap.ker φ) = 2 := by
      rw [hkerφ, natCard_subOf hV₁V]
      exact hs.v1.2.1 ▸ (by norm_num)
    have hc3 : Nat.card (Additive ↥V) = 16 := by
      show Nat.card ↥V = 16
      rw [hcard]
      norm_num
    rw [hc2, hc3] at hc1
    omega
  have hS3 : Module.finrank (ZMod 2) S = 3 := finrank_of_natCard (n := 3) (by rw [hS8]; norm_num)
  have hSq : ∀ s ∈ S, q s = 0 := by
    rintro s ⟨x, rfl⟩
    exact htot _ (Additive.toMul x).2
  have hπS : ∀ v ∈ V, D.π v ∈ S := fun v hv => ⟨Additive.ofMul ⟨v, hv⟩, by
    show D.π (((Additive.ofMul (⟨v, hv⟩ : ↥V)).toMul : ↥V) : G) = D.π v
    rfl⟩
  have hSπ : ∀ s ∈ S, ∃ v ∈ V, D.π v = s := by
    rintro s ⟨x, rfl⟩
    exact ⟨_, (Additive.toMul x).2, rfl⟩
  have hconj : ∀ g : G, ∀ hg : g ∈ Subgroup.normalizer (V : Set G),
      ∀ htU : g ∈ Subgroup.normalizer (u128 V V₁ : Set G), ∀ x ∈ V,
        D.π (g * x * g⁻¹) ∈ S := by
    intro g hg htU x hx
    apply hπS
    exact (Subgroup.mem_normalizer_iff.1 hg x).1 hx
  have fwd : ∀ g : G, ∀ hg : g ∈ Subgroup.normalizer (V : Set G),
      ∀ hgU : g ∈ Subgroup.normalizer (u128 V V₁ : Set G), ∀ w ∈ S,
        D.ρ ⟨g, hgU⟩ w ∈ S := by
    intro g hg hgU w hw
    obtain ⟨x, hx, rfl⟩ := hSπ w hw
    have e : D.ρ ⟨g, hgU⟩ (D.π x) = D.π (g * x * g⁻¹) := D.ρ_π ⟨g, hgU⟩ x (hUV x hx)
    rw [e]
    exact hconj g hg hgU x hx
  have hpresT : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      ∀ v, v ∈ S ↔ D.ρ ⟨t, htU⟩ v ∈ S := by
    intro t ht htU v
    constructor
    · exact fun hv => fwd t (hTV ht) htU v hv
    · intro hv
      have h1 := fwd t⁻¹ (Subgroup.inv_mem _ (hTV ht)) (Subgroup.inv_mem _ htU) _ hv
      have hinv : D.ρ ⟨t⁻¹, Subgroup.inv_mem _ htU⟩ (D.ρ ⟨t, htU⟩ v) = v := by
        rw [← LinearEquiv.mul_apply, ← map_mul]
        have h1' : (⟨t⁻¹, Subgroup.inv_mem _ htU⟩ * ⟨t, htU⟩ :
            Subgroup.normalizer (u128 V V₁ : Set G)) = 1 := Subtype.ext (by simp)
        rw [h1', map_one]
        rfl
      rw [hinv] at h1
      exact h1
  have hstab : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ stabS S := fun t ht htU => mem_stabS_iff.2 (hpresT t ht htU)
  refine ⟨?_, S, hS3, hSq, hπS, hSπ, hstab⟩
  intro t ht htU
  have htN1 : t ∈ Subgroup.normalizer (V₁ : Set G) := hTV₁ ht
  have htΓ : D.ρ ⟨t, htU⟩ ∈ D.img (Subgroup.normalizer (V₁ : Set G)) :=
    L128A.HatU.rho_mem_img D htN1 htU
  have htO : D.ρ ⟨t, htU⟩ ∈ orthogonalSubgroupOf q := hΓO htΓ
  exact (hΩF4.2.2.1 S hS3 hSq).1 _ htO (hpresT t ht htU)

end Main3

end CFSG.Quasithin.H13.C1294
