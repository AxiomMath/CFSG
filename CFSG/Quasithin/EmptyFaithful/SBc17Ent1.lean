module

public import CFSG.Quasithin.EmptyFaithful.SBc17Ent0
public import CFSG.Quasithin.EmptyFaithful.SBc17N2
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc17

variable {G : Type} [Group G]

@[expose] noncomputable def actOn {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G)) :
    ↥J →* ↥(autOn J V) :=
  ((conjAct V).comp (Subgroup.inclusion hJV)).codRestrict (autOn J V)
    (fun x => mem_autOn_iff.mpr ⟨x, hJV x.2, x.2, rfl⟩)

theorem coe_actOn {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G)) (x : ↥J) :
    ((actOn hJV x : ↥(autOn J V)) : MulAut ↥V) = conjAct V ⟨x, hJV x.2⟩ := rfl

theorem actOn_surjective {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (actOn hJV) := by
  rintro ⟨a, ha⟩
  obtain ⟨x, hx, hxJ, rfl⟩ := mem_autOn_iff.mp ha
  exact ⟨⟨x, hxJ⟩, Subtype.ext rfl⟩

theorem actOn_eq_one_iff {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G)) (x : ↥J) :
    actOn hJV x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 : conjAct V ⟨x, hJV x.2⟩ = 1 := by
      have := congrArg (fun a : ↥(autOn J V) => (a : MulAut ↥V)) h
      exact this
    have h2 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : G)) h1
    simp only [conjAct_coe, MulAut.one_apply] at h2
    calc v * (x : G) = ((x : G) * v * (x : G)⁻¹) * x := by rw [h2]
      _ = x * v := by group
  · intro h
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have h1 := h (v : G) v.2
    show ((conjAct V ⟨x, hJV x.2⟩ v : ↥V) : G) = (v : G)
    rw [conjAct_coe]
    calc (x : G) * v * (x : G)⁻¹ = (v * x) * (x : G)⁻¹ := by rw [← h1]
      _ = v := by group

theorem isPGroup_comap_of_ker {K A : Type*} [Group K] [Group A] (π : K →* A)
    (hker : IsPGroup 2 π.ker) {T : Subgroup A} (hT : IsPGroup 2 T) : IsPGroup 2 (T.comap π) := by
  intro g
  obtain ⟨n, hn⟩ := hT ⟨π g, g.2⟩
  have h1 : (g : K) ^ 2 ^ n ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨m, hm⟩ := hker ⟨(g : K) ^ 2 ^ n, h1⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  have := congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

theorem isBorelOfBlock_of_isBorelIn_autOn [Finite G] {J V B : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G))
    (hCO : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J)
    (h3 : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) ≠ 3) (hBJ : B ≤ J)
    (hB : IsBorelIn (autOn J V) (autOn B V)) : IsBorelOfBlock J B := by
  unfold IsBorelOfBlock
  split_ifs with hc3
  · exact absurd hc3 h3
  obtain ⟨Ss, hSs, hBS⟩ := hB
  have hπs := actOn_surjective hJV
  have hker : IsPGroup 2 (actOn hJV).ker := by
    intro g
    have hg : ((g : ↥J) : G) ∈ pCoreOf 2 J := by
      have := g.2
      rw [MonoidHom.mem_ker, actOn_eq_one_iff] at this
      exact hCO ⟨(g : ↥J).2, this⟩
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 J ⟨((g : ↥J) : G), hg⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hT : IsPGroup 2 (Ss.subgroupOf (autOn J V)) := hSs.2.1.comap_subtype (K := autOn J V)
  set K : Subgroup ↥J := (Ss.subgroupOf (autOn J V)).comap (actOn hJV) with hK
  have hK2 : IsPGroup 2 K := isPGroup_comap_of_ker _ hker hT
  set S : Subgroup G := K.map J.subtype with hS
  have hSJ : S ≤ J := Subgroup.map_subtype_le K
  have hmemS : ∀ x : G, x ∈ S ↔ ∃ hx : x ∈ J,
      ((actOn hJV ⟨x, hx⟩ : ↥(autOn J V)) : MulAut ↥V) ∈ Ss := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hactmul : ∀ (x y : G) (hx : x ∈ J) (hy : y ∈ J),
      ((actOn hJV ⟨x * y * x⁻¹, mul_mem (mul_mem hx hy) (inv_mem hx)⟩ : ↥(autOn J V)) :
        MulAut ↥V) = ((actOn hJV ⟨x, hx⟩ : ↥(autOn J V)) : MulAut ↥V) *
          ((actOn hJV ⟨y, hy⟩ : ↥(autOn J V)) : MulAut ↥V) *
            ((actOn hJV ⟨x, hx⟩ : ↥(autOn J V)) : MulAut ↥V)⁻¹ := by
    intro x y hx hy
    have e : (⟨x * y * x⁻¹, mul_mem (mul_mem hx hy) (inv_mem hx)⟩ : ↥J) =
        ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hnorm : ∀ (x : G) (hx : x ∈ J), x ∈ Subgroup.normalizer (S : Set G) ↔
      ((actOn hJV ⟨x, hx⟩ : ↥(autOn J V)) : MulAut ↥V) ∈
        Subgroup.normalizer (Ss : Set (MulAut ↥V)) := by
    intro x hx
    have hfwd : ∀ (x : G) (hx : x ∈ J), x ∈ Subgroup.normalizer (S : Set G) →
        ∀ s ∈ Ss, ((actOn hJV ⟨x, hx⟩ : ↥(autOn J V)) : MulAut ↥V) * s *
          ((actOn hJV ⟨x, hx⟩ : ↥(autOn J V)) : MulAut ↥V)⁻¹ ∈ Ss := by
      intro x hx hxN s hs
      obtain ⟨y, hyN, hyJ, rfl⟩ := mem_autOn_iff.mp (hSs.1 hs)
      have hyS : y ∈ S := (hmemS y).mpr ⟨hyJ, hs⟩
      have hxyS : x * y * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxN y).mp hyS
      obtain ⟨hxyJ, hxyA⟩ := (hmemS _).mp hxyS
      have h1 := hactmul x y hx hyJ
      rw [h1] at hxyA
      exact hxyA
    constructor
    · intro hxN
      rw [Subgroup.mem_normalizer_iff]
      intro s
      refine ⟨fun hs => hfwd x hx hxN s hs, fun hs => ?_⟩
      have h1 := hfwd x⁻¹ (inv_mem hx) (inv_mem hxN) _ hs
      have e : ((actOn hJV ⟨x⁻¹, inv_mem hx⟩ : ↥(autOn J V)) : MulAut ↥V) =
          ((actOn hJV ⟨x, hx⟩ : ↥(autOn J V)) : MulAut ↥V)⁻¹ := by
        have : (⟨x⁻¹, inv_mem hx⟩ : ↥J) = ⟨x, hx⟩⁻¹ := rfl
        rw [this, map_inv]
        rfl
      rw [e] at h1
      simpa [mul_assoc] using h1
    · intro hN
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨hyJ, hyA⟩ := (hmemS y).mp hy
        refine (hmemS _).mpr ⟨mul_mem (mul_mem hx hyJ) (inv_mem hx), ?_⟩
        rw [hactmul x y hx hyJ]
        exact (Subgroup.mem_normalizer_iff.mp hN _).mp hyA
      · intro hy
        obtain ⟨hxyJ, hxyA⟩ := (hmemS _).mp hy
        have hyJ : y ∈ J := by
          have := mul_mem (mul_mem (inv_mem hx) hxyJ) hx
          simpa [mul_assoc] using this
        refine (hmemS y).mpr ⟨hyJ, ?_⟩
        rw [hactmul x y hx hyJ] at hxyA
        exact (Subgroup.mem_normalizer_iff.mp hN _).mpr hxyA
  refine ⟨S, ⟨hSJ, hK2.map J.subtype, ?_⟩, ?_⟩
  · have h1 : S.subgroupOf J = K := Subgroup.comap_map_eq_self_of_injective Subtype.val_injective K
    rw [h1, hK, Subgroup.index_comap_of_surjective _ hπs]
    exact hSs.2.2
  · apply le_antisymm
    · refine sup_le (fun b hb => ⟨hBJ hb, ?_⟩) (fun o ho => ⟨pCoreOf_le 2 J ho, ?_⟩)
      · have hbJ := hBJ hb
        refine (hnorm b hbJ).mpr ?_
        have h1 : conjAct V ⟨b, hJV hbJ⟩ ∈ autOn B V := mem_autOn_iff.mpr ⟨b, hJV hbJ, hb, rfl⟩
        rw [hBS] at h1
        exact h1.2
      · have hoJ := pCoreOf_le 2 J ho
        refine (hnorm o hoJ).mpr ?_
        have h1 : ((actOn hJV ⟨o, hoJ⟩ : ↥(autOn J V)) : MulAut ↥V) = 1 := by
          have := (actOn_eq_one_iff hJV ⟨o, hoJ⟩).mpr (hOC ho)
          rw [this]
          rfl
        rw [h1]
        exact one_mem _
    · intro x hx
      obtain ⟨hxJ, hxN⟩ := hx
      have h1 := (hnorm x hxJ).mp hxN
      have h2 : ((actOn hJV ⟨x, hxJ⟩ : ↥(autOn J V)) : MulAut ↥V) ∈ autOn B V := by
        rw [hBS]
        exact ⟨(actOn hJV ⟨x, hxJ⟩).2, h1⟩
      obtain ⟨b, hbN, hbB, hb⟩ := mem_autOn_iff.mp h2
      have hbJ := hBJ hbB
      have h3 : b⁻¹ * x ∈ pCoreOf 2 J := by
        apply hCO
        have hmem : b⁻¹ * x ∈ J := mul_mem (inv_mem hbJ) hxJ
        refine ⟨hmem, ?_⟩
        have e : (⟨b⁻¹ * x, hmem⟩ : ↥J) = ⟨b, hbJ⟩⁻¹ * ⟨x, hxJ⟩ := rfl
        have h4 : actOn hJV ⟨b⁻¹ * x, hmem⟩ = 1 := by
          apply Subtype.ext
          rw [e, map_mul, map_inv]
          show (((actOn hJV ⟨b, hbJ⟩ : ↥(autOn J V)) : MulAut ↥V))⁻¹ *
            ((actOn hJV ⟨x, hxJ⟩ : ↥(autOn J V)) : MulAut ↥V) = 1
          have h5 : ((actOn hJV ⟨b, hbJ⟩ : ↥(autOn J V)) : MulAut ↥V) =
              ((actOn hJV ⟨x, hxJ⟩ : ↥(autOn J V)) : MulAut ↥V) := hb
          rw [h5, inv_mul_cancel]
        exact (actOn_eq_one_iff hJV ⟨b⁻¹ * x, hmem⟩).mp h4
      have e : x = b * (b⁻¹ * x) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left hbB) (Subgroup.mem_sup_right h3)

theorem center_sl_two_charTwo_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  have hr1 : r = 1 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h0 : (r - 1) ^ 2 = 0 := by
      calc (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        _ = 0 := by rw [hr]; linear_combination (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  ext i j
  rw [← hA', hr1]
  simp [Matrix.one_apply]

theorem card_ne_three_of_quasisimple {Γ : Type*} [Group Γ] (h : CFSG.IsQuasisimple Γ) :
    Nat.card Γ ≠ 3 := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic Γ := isCyclic_of_prime_card h3
  have hfin : Finite Γ := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  have hcommu : IsMulCommutative Γ := IsCyclic.isMulCommutative
  have hcen : Subgroup.center Γ = ⊤ :=
    eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun g => hcommu.is_comm.comm g x
  have hcomm : commutator Γ = ⊥ := (commutator_eq_bot_iff_center_eq_top Γ).mpr hcen
  have htop : (⊤ : Subgroup Γ) = ⊥ := h.1.commutator_eq_top.symm.trans hcomm
  have h1 : Nat.card Γ = 1 := by
    rw [← Subgroup.card_top (G := Γ), htop, Subgroup.card_bot]
  omega

theorem isL2BorelBlock_of_C27L2 [Finite G] {H R M J : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (J : Set G))
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (h1a : pCoreOf 2 (J ⊔ R) ≤ (J ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G))
    (h1b : (J ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) ≤
      pCoreOf 2 (J ⊔ R) ⊔ oTwoZIn J)
    (h : C27L2 H R M J (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)))) : IsL2BorelBlock J (J ⊓ M) := by
  obtain ⟨hchi, ⟨n, hn, hlin⟩, -, hB⟩ := h
  refine ⟨hchi.1.1, ⟨n, hn, hlin⟩, ?_⟩
  set V := omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) with hV
  have hJV : J ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V J R
  have hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    (h1a (pCoreOf_le_pCoreOf_sup hR hx)).2
  have hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J := inf_centralizer_le_oTwoZIn h1b
  have hCO : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J := by
    intro x hx
    obtain ⟨F, hF, hFin, hcard, α, hα, hker, -⟩ := hlin
    have : CharP F 2 := charP_two_of_card_eq_pow hcard
    obtain ⟨hxJ, hxc⟩ := mem_oTwoZIn_iff.mp (hD hx)
    have h1 : α ⟨x, hxJ⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      obtain ⟨ℓ, rfl⟩ := hα g
      have h2 := Subgroup.mem_center_iff.mp hxc (QuotientGroup.mk ℓ)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h2
      have h3 : α ((ℓ * ⟨x, hxJ⟩)⁻¹ * (⟨x, hxJ⟩ * ℓ)) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact h2
      rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h3
      exact h3
    rw [center_sl_two_charTwo_eq_bot, Subgroup.mem_bot] at h1
    exact (map_eq_one_iff_mem_pCoreOf hker ⟨x, hxJ⟩).mp h1
  have h3 : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) ≠ 3 := card_ne_three_of_quasisimple hq
  have := isBorelOfBlock_of_isBorelIn_autOn hJV hOC hCO h3 (inf_le_right : M ⊓ J ≤ J) hB
  rwa [inf_comm] at this

end SBc17

end CFSG.Quasithin
