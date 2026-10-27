module

public import CFSG.Quasithin.H13.A6S13816r
public import CFSG.Quasithin.H13.A6S13816s
public import CFSG.Quasithin.H13.A6S13816t
public import CFSG.Quasithin.H13.A6S13834

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

attribute [local instance] commGroupOfFact

namespace L2Orth

variable {G : Type} [Group G]

@[expose] def modMkHom {V₁ U : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V₁ : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ U))] : ↥U →* ↥(tildeOf V₁ U) where
  toFun u := modMk hUV u u.2
  map_one' := modMk_one hUV
  map_mul' a b := modMk_mul hUV a.2 b.2

theorem modMkHom_surjective {V₁ U : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V₁ : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ U))] : Function.Surjective (modMkHom hUV) := by
  intro w
  obtain ⟨a, haU, haw⟩ := exists_mk_of_mem_tilde w
  exact ⟨⟨a, haU⟩, Subtype.ext haw⟩

theorem modMk_congr {V₁ U : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V₁ : Set G)) {a b : G}
    (h : a = b) (ha : a ∈ U) (hb : b ∈ U) : modMk hUV a ha = modMk hUV b hb := by
  subst h
  rfl

theorem card_range_le_index_mul {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (D : Subgroup A) : Nat.card f.range ≤ D.index * Nat.card (D.map f) := by
  have h1 := Subgroup.index_mul_card (D.map f.rangeRestrict)
  have h2 : (D.map f.rangeRestrict).index ∣ D.index :=
    Subgroup.index_map_dvd D f.rangeRestrict_surjective
  have h3 : Nat.card (D.map f.rangeRestrict) = Nat.card (D.map f) := by
    rw [← Subgroup.card_map_of_injective (f := f.range.subtype) f.range.subtype_injective,
      Subgroup.map_map]
    rfl
  rw [← h1, h3]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (Nat.pos_of_ne_zero D.index_ne_zero_of_finite) h2)

theorem range_delta_eq {V₁ U : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V₁ : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ U))] (σ : MulAut ↥(tildeOf V₁ U)) :
    (L2Om.delta σ).range = ((L2Om.delta σ).comp (modMkHom hUV)).range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ (modMkHom_surjective hUV),
    ← MonoidHom.range_eq_map]

theorem card_map_delta_le [Finite G] {V₁ U H : Subgroup G}
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hUV : U ≤ Subgroup.normalizer (V₁ : Set G)) [Fact (IsElemAbelian 2 (tildeOf V₁ U))]
    (x : ↥H) {C : Subgroup G} {D : Subgroup ↥U}
    (hC : ∀ u ∈ D, (x : G) * (u : G) * (x : G)⁻¹ * (u : G)⁻¹ ∈ C) :
    Nat.card (D.map ((L2Om.delta (actH hV₁ hUN x)).comp (modMkHom hUV))) ≤ Nat.card C := by
  have hxu : ∀ u : ↥U, (x : G) * (u : G) * (x : G)⁻¹ ∈ U := fun u =>
    (Subgroup.mem_normalizer_iff.mp (hUN x.2) u).mp u.2
  have hmem : ∀ u : ↥U, (x : G) * (u : G) * (x : G)⁻¹ * (u : G)⁻¹ ∈ U := fun u =>
    U.mul_mem (hxu u) (U.inv_mem u.2)
  have hle : D.map ((L2Om.delta (actH hV₁ hUN x)).comp (modMkHom hUV)) ≤
      (C.subgroupOf U).map (modMkHom hUV) := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨⟨_, hmem u⟩, Subgroup.mem_subgroupOf.mpr (hC u hu), ?_⟩
    show modMk hUV _ (hmem u) = actH hV₁ hUN x (modMk hUV u u.2) * (modMk hUV u u.2)⁻¹
    rw [actH_modMk hV₁ hUV hUN x u.2, ← modMk_inv hUV u.2,
      ← modMk_mul hUV (hxu u) (U.inv_mem u.2)]
  calc Nat.card (D.map ((L2Om.delta (actH hV₁ hUN x)).comp (modMkHom hUV)))
      ≤ Nat.card ((C.subgroupOf U).map (modMkHom hUV)) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (C.subgroupOf U) := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    _ ≤ Nat.card C := Nat.card_le_card_of_injective (fun a => (⟨a.1.1, a.2⟩ : ↥C)) fun a b h => by
        have h' : ((a : ↥U) : G) = ((b : ↥U) : G) := congrArg (fun z : ↥C => (z : G)) h
        exact Subtype.ext (Subtype.ext h')

theorem exists_noncomm_of_isPSL {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X)
    (hn : 2 ≤ n) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, -, ⟨φ⟩⟩ := SBc6.exists_sl2_equiv_of_psl hX
  classical
  have := Fintype.ofFinite F
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, c ≠ 1 := by
    have h1 : 1 < Nat.card Fˣ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hFcard]
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne 1
  refine ⟨φ (SBc5SL2.dm c), φ (SBc5SL2.xm 1), fun h => hc ?_⟩
  rw [← map_mul, ← map_mul] at h
  have h1 := φ.injective h
  have h2 : SBc5SL2.dm c * SBc5SL2.xm (1 : F) * (SBc5SL2.dm c)⁻¹ = SBc5SL2.xm 1 := by
    rw [h1, mul_inv_cancel_right]
  rw [L2Borel.dm_conj_xm, mul_one] at h2
  have h3 := L2Aut.xm_injective h2
  exact Units.ext (L2Borel.eq_one_of_sq h3)

end L2Orth

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem orth_false
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hS : S.Hyp138) (hhat : IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K) (hHeq : H = (K ⊔ T) ⊔ S.L1)
    (hn : IsPSL 2 2 2 (↥K ⧸ CFSG.pCore 2 ↥K))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
    (hO4 : Omega4PlusModule (S.KSt H (conjClosure K T)) 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hF⟩ := S.hypF918_K0 h36 h37 h38 h139 h1334 h13 hS hH hK
  rw [← hHeq] at hF
  have hF98 := hF.toHypF98
  have hHq : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hℓK : S.L1 ≤ conjClosure K T :=
    S.L1_le_conjClosure' h37 h38 h122 hH hK hne (L2Case.three_dvd_card (Or.inl ⟨2, hn⟩))
  have hK₀KT : conjClosure K T ≤ K ⊔ T := conjClosure_le fun s hs k hk =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left hk))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hs))
  have hHK : H = K ⊔ T := by
    rw [hHeq]
    exact sup_eq_left.mpr (hℓK.trans hK₀KT)
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply le_antisymm
    · exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  obtain ⟨hKt, hK₀eq, hcomm, hperm⟩ := (five_group_data hF hHq h37 h38 hne).2 t htT htK
  have htH : t ∈ H := hF.T_le_H htT
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  have hV₁ : H ≤ Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G) := hF.H_le_normalizer_V₁
  have hUN : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) := le_normalizer_conjClosure _ _
  have hUV : conjClosure S.V3 H ≤ Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure S.V3 H)
  set φ := actH hV₁ hUN with hφ
  have hφQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → φ x = 1 := fun x hx =>
    hF.actH_eq_one_of_mem_pCoreOf (le_conjClosure S.V3 H) hx
  have hφ1 : ∀ x : ↥H, φ x = 1 ↔ ∀ u ∈ conjClosure S.V3 H,
      (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ fsuV1 T V := fun x =>
    S153M.actE_eq_one_iff hV₁ hUN hUV x
  have hconjφ : ∀ y a : ↥H, φ y * φ a * (φ y)⁻¹ = φ (y * a * y⁻¹) := fun y a => by
    rw [map_mul, map_mul, map_inv]
  set Mp := S.KSt H (conjClosure K T) with hMpdef
  have hMpeq : Mp = ((conjClosure K T).subgroupOf H).map φ :=
    autOn_tilde_eq_map_actH hV₁ hUN hF.K₀_le_H
  set K₁ : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    (K.subgroupOf H).map φ with hK₁
  set K₂ : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ((K.map (MulAut.conj t).toMonoidHom).subgroupOf H).map φ with hK₂
  have hMp : Mp = K₁ ⊔ K₂ := by
    rw [hMpeq, hK₀eq, Subgroup.subgroupOf_sup hKH hKtH, Subgroup.map_sup]
  have hK₂conj : K₂ = K₁.map (MulAut.conj (φ ⟨t, htH⟩)).toMonoidHom := by
    rw [hK₂, hK₁, L2Hat.map_map_conj, S153M.map_conj_subgroupOf hKH htH]
  have hcommK : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : φ (a * b * a⁻¹ * b⁻¹) = 1 := hφQ _ (hcomm (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb)))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc φ a * φ b = (φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹) * φ b * φ a := by group
      _ = φ b * φ a := by rw [h1, one_mul]
  obtain ⟨F, fF, finF, hF4, πM, β, hπs, hd⟩ := L2Om.exists_tensorData hO4
  have hchar : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF4])
  have hK4 : 4 ≤ Nat.card F := by rw [hF4]; norm_num
  have hinjπ := hd.injective
  have hMpne : Mp ≠ ⊥ := by
    intro h
    have h3 : πM (L2Om.xmS 1, 1) = πM 1 :=
      Subtype.ext ((Subgroup.mem_bot.mp (h.le (πM (L2Om.xmS 1, 1)).2)).trans
        (Subgroup.mem_bot.mp (h.le (πM 1).2)).symm)
    have h4 := congrArg (fun γ : TensorG2 F =>
      ((γ.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1) (hinjπ h3)
    simp [L2Om.coe_xmS, L2Om.um] at h4
  let ρ₁ : ↥K →* ↥K₁ :=
    (φ.comp (Subgroup.inclusion hKH)).codRestrict K₁ fun k =>
      ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hρ₁ : Function.Surjective ρ₁ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hker : CFSG.pCore 2 ↥K ≤ ρ₁.ker := fun k hk => by
    have hk' : (k : G) ∈ pCoreOf 2 H :=
      CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
        ((mem_pCore_iff k).1 hk)
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (hφQ _ hk')
  have hK₁ne : K₁ ≠ ⊥ := by
    intro h
    apply hMpne
    rw [hMp, hK₂conj, h, Subgroup.map_bot, sup_bot_eq]
  have hnt₁ : Nontrivial ↥K₁ := (Subgroup.nontrivial_iff_ne_bot _).mpr hK₁ne
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 hn).2
  obtain ⟨e₁⟩ := L2Ten.nonempty_quot_mulEquiv ρ₁ hρ₁ hker
  have hK₁P : IsPSL 2 2 2 ↥K₁ := isPSL_congr e₁ hn
  have hK₁s : IsSimpleGroup ↥K₁ := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 hK₁P).2
  obtain ⟨hK₁q, hZ₁⟩ :=
    CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (L2Orth.exists_noncomm_of_isPSL hK₁P le_rfl)
  let e₂ : ↥K₁ ≃* ↥K₂ :=
    ((MulAut.conj (φ ⟨t, htH⟩)).subgroupMap K₁).trans (MulEquiv.subgroupCongr hK₂conj.symm)
  have hK₂q := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₂ hK₁q
  have hK₂ne : K₂ ≠ ⊥ := by
    rw [hK₂conj]
    intro h
    exact hK₁ne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp h)
  have hK₁f := eq_factor_or2 hK4 hd hπs hMp hcommK hK₁q hK₁ne
  have hK₂f := eq_factor_or2 hK4 hd hπs (hMp.trans (sup_comm _ _))
    (fun x hx y hy => (hcommK y hy x hx).symm) hK₂q hK₂ne
  have hfac₁ : ∀ x ∈ K₁, x ∈ factorL2 Mp πM ∨ x ∈ factorR2 Mp πM := fun x hx => by
    rcases hK₁f with h | h
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  have hfac₂ : ∀ x ∈ K₂, x ∈ factorL2 Mp πM ∨ x ∈ factorR2 Mp πM := fun x hx => by
    rcases hK₂f with h | h
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  have hinf : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    have hxc : (⟨x, hx₁⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (hcommK y y.2 x hx₂)
    rw [hZ₁] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxc))
  have hcard₁ : Nat.card ↥K₁ = 2 ^ 2 * (4 ^ 2 - 1) :=
    CFSG.Quasithin.card_of_isPSL_two_even hK₁P.1.2.1 hK₁P
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₁) 2 (by rw [hcard₁]; norm_num)
  have hu1 : (u₀ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ≠ 1 := fun h => by
    rw [show u₀ = 1 from Subtype.ext h, orderOf_one] at hu₀
    norm_num at hu₀
  have hu2 : (u₀ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ^ 2 = 1 := by
    have h1 : u₀ ^ 2 = 1 := hu₀ ▸ pow_orderOf_eq_one u₀
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hperm' : ∀ y : ↥H, ((∀ x ∈ K₁, φ y * x * (φ y)⁻¹ ∈ K₁) ∧
      ∀ x ∈ K₂, φ y * x * (φ y)⁻¹ ∈ K₂) ∨
        φ y * (u₀ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) * (φ y)⁻¹ ∈ K₂ := by
    intro y
    rcases hperm y y.2 with hy | hy
    · left
      have hyt : t⁻¹ * (y : G) * t ∈ Subgroup.normalizer (K : Set G) := by
        rcases hperm ((y : G) * t) (H.mul_mem y.2 htH) with h | h
        · exact absurd (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) h) htK
        · simpa [mul_assoc] using h
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩
        rw [hconjφ]
        refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hy _).mp (Subgroup.mem_subgroupOf.mp ha)
      · rintro _ ⟨a, ha, rfl⟩
        rw [hconjφ]
        refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
        obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha)
        refine Subgroup.mem_map.mpr ⟨(t⁻¹ * y * t) * k * (t⁻¹ * y * t)⁻¹,
          (Subgroup.mem_normalizer_iff.mp hyt k).mp hk, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hka ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hka]
        group
    · right
      obtain ⟨a, ha, ha'⟩ := u₀.2
      rw [← ha', hconjφ]
      refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      refine Subgroup.mem_map.mpr ⟨(t⁻¹ * y) * a * (t⁻¹ * y)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hy _).mp (Subgroup.mem_subgroupOf.mp ha), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
  have hNT : ∀ y (hy : y ∈ H), ∀ C : Subgroup G, Nat.card C ≤ 2 →
      (∀ w ∈ conjClosure S.V3 H, y * w * y⁻¹ * w⁻¹ ∈ C) → φ ⟨y, hy⟩ = 1 := by
    intro y hy C hC hyC
    refine L2Om.eq_one_of_card_range_le_two hF4 hd hπs hMp hcommK hinf hfac₁ hfac₂ u₀.2 hu1
      hu2 (hperm' ⟨y, hy⟩) ?_
    rw [L2Orth.range_delta_eq hUV, MonoidHom.range_eq_map]
    exact (L2Orth.card_map_delta_le hV₁ hUN hUV ⟨y, hy⟩ fun u _ => hyC u u.2).trans hC
  obtain ⟨γ, γ', g, s⟩ := hF98.exists_F8Setup
  have hlt : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
    have hstab : CosetGeom.stab γ = conjSub (g : G) H := by
      rw [← s.edge₁, CosetGeom.stab_smul, CosetGeom.stab_γ₁ hF98.amalgamHypV.le₂]
    obtain ⟨X, hXγ, hXc⟩ : ∃ X : Subgroup G, X ≤ conjSub (g : G) H ∧
        ⁅X, F8.Uγ S.V3 H (g : G)⁆ = fsuV1 T V := by
      rcases hF98.F916_1 s hD.symm with ⟨-, -, -, hc⟩ | ⟨-, -, -, -, hc⟩
      · refine ⟨conjClosure S.V3 H, ?_, hc⟩
        rw [← hstab]
        exact (conjClosure_le fun _ hk _ hz => mem_conjClosure hk (hF98.Vp_le_V hz)).trans
          ((hF98.F913_2 s).1.trans ((pCoreOf_le 2 _).trans inf_le_right))
      · refine ⟨V, ?_, hc⟩
        rw [← hstab]
        exact CosetGeom.V_le_stab_of_dist_le hF98.amalgamHypV hF98.V_ne_bot
          s.critical.dist_eq.le
    obtain ⟨x, hxX, u, huU, hxu⟩ : ∃ x ∈ X, ∃ u ∈ F8.Uγ S.V3 H (g : G),
        x * u * x⁻¹ * u⁻¹ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : ⁅X, F8.Uγ S.V3 H (g : G)⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact Subgroup.mem_bot.mpr (hcon a ha b hb)
      have h2 := hF98.card_V₁
      rw [← hXc, h1, Subgroup.card_bot] at h2
      norm_num at h2
    have hyH : (g : G)⁻¹ * x * g ∈ H := mem_conjSub.mp (hXγ hxX)
    have hwU : (g : G)⁻¹ * u * g ∈ conjClosure S.V3 H := mem_conjSub.mp huU
    have hy1 := hNT _ hyH (conjSub (g : G)⁻¹ (fsuV1 T V))
      ((CosetGeom.card_conjSub _ _).trans hF98.card_V₁).le fun w hw => by
        rw [mem_conjSub, inv_inv]
        have h1 : x * ((g : G) * w * (g : G)⁻¹) * x⁻¹ * ((g : G) * w * (g : G)⁻¹)⁻¹ ∈
            fsuV1 T V := by
          rw [← hXc]
          exact Subgroup.commutator_mem_commutator hxX (mul_mem_conjSub hw)
        have e : (g : G) * ((g : G)⁻¹ * x * g * w * ((g : G)⁻¹ * x * g)⁻¹ * w⁻¹) * (g : G)⁻¹ =
            x * ((g : G) * w * (g : G)⁻¹) * x⁻¹ * ((g : G) * w * (g : G)⁻¹)⁻¹ := by group
        rw [e]
        exact h1
    have h2 : ((g : G)⁻¹ * x * g) * ((g : G)⁻¹ * u * g) * ((g : G)⁻¹ * x * g)⁻¹ *
        ((g : G)⁻¹ * u * g)⁻¹ ∈ fsuV1 T V := (hφ1 ⟨_, hyH⟩).mp hy1 _ hwU
    have h3 : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) := by
      refine ⟨?_, ?_⟩
      · rw [← hXc]
        exact Subgroup.commutator_mem_commutator hxX huU
      · show _ ∈ conjSub (g : G) (fsuV1 T V)
        rw [mem_conjSub]
        have e : (g : G)⁻¹ * (x * u * x⁻¹ * u⁻¹) * g = ((g : G)⁻¹ * x * g) *
            ((g : G)⁻¹ * u * g) * ((g : G)⁻¹ * x * g)⁻¹ * ((g : G)⁻¹ * u * g)⁻¹ := by group
        rw [e]
        exact h2
    rw [hF98.F913_5b s] at h3
    exact hxu (Subgroup.mem_bot.mp h3)
  obtain ⟨δ, δ', k, sk, hpos, hle, -, c, hcH, hcV⟩ := exists_case13_8_8_two hF98 s hlt
  have hO2 := S.O2_le_K0 h37 h38 h122 hhat hH hK hne hHK hn
  have hMpN : ∀ y : ↥H, ∀ m ∈ Mp, φ y * m * (φ y)⁻¹ ∈ Mp := by
    intro y m hm
    rw [hMpeq] at hm ⊢
    obtain ⟨a, ha, rfl⟩ := hm
    rw [hconjφ]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hF.K₀_normal y.2) _).mp
      (Subgroup.mem_subgroupOf.mp ha)
  have hMpQ : ∀ z : ↥H, (z : G) ∈ conjClosure K T ⊔ pCoreOf 2 H → φ z ∈ Mp := by
    intro z hz
    have h1 : z ∈ (conjClosure K T).subgroupOf H ⊔ (pCoreOf 2 H).subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup hF.K₀_le_H (pCoreOf_le 2 H)]
      exact Subgroup.mem_subgroupOf.mpr hz
    have h2 := Subgroup.mem_map_of_mem φ h1
    have h3 : ((pCoreOf 2 H).subgroupOf H).map φ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_bot.mpr (hφQ q (Subgroup.mem_subgroupOf.mp hq))
    rw [Subgroup.map_sup, h3, sup_bot_eq, ← hMpeq] at h2
    exact h2
  have hUδH : F8.Uγ S.V3 H (k : G) ≤ H := hF98.Uγ_le_H sk
  have hUδMp : ∀ x : ↥H, (x : G) ∈ F8.Uγ S.V3 H (k : G) → φ x ∈ Mp := by
    intro x hx
    have hcx : (c : G) * x * c⁻¹ ∈ conjClosure K T ⊔ pCoreOf 2 H :=
      hO2 (hcV (mul_mem_conjSub (hF98.Uγ_le_Vγ hx)))
    have hcxH : (c : G) * x * c⁻¹ ∈ H := H.mul_mem (H.mul_mem hcH x.2) (H.inv_mem hcH)
    have e : φ x = φ (⟨c, hcH⟩⁻¹) * φ ⟨_, hcxH⟩ * (φ (⟨c, hcH⟩⁻¹))⁻¹ := by
      rw [hconjφ]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e]
    exact hMpN _ _ (hMpQ _ hcx)
  have hUδab := hF98.isElemAbelian_Uγ (g := k)
  have hAeq : autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (k : G)))
      (tildeOf (fsuV1 T V) (conjClosure S.V3 H)) = ((F8.Uγ S.V3 H (k : G)).subgroupOf H).map φ :=
    autOn_tilde_eq_map_actH hV₁ hUN hUδH
  have hA4 : Nat.card (autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (k : G)))
      (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ≤ Nat.card F := by
    rw [hAeq]
    refine L2Om.card_le_of_quadratic hF4 hd hπs ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hUδMp a (Subgroup.mem_subgroupOf.mp ha)
    · rintro _ ⟨a, ha, rfl⟩
      have h1 : a ^ 2 = 1 := Subtype.ext (by
        simpa using F7.isElemAbelian_pow_eq_one hUδab (Subgroup.mem_subgroupOf.mp ha))
      rw [← map_pow, h1, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
      obtain ⟨u, rfl⟩ := L2Orth.modMkHom_surjective hUV w
      have hbu : (b : G) * u * (b : G)⁻¹ ∈ conjClosure S.V3 H :=
        (Subgroup.mem_normalizer_iff.mp (hUN b.2) u).mp u.2
      have hz : (b : G) * u * (b : G)⁻¹ * (u : G)⁻¹ ∈ conjClosure S.V3 H :=
        mul_mem hbu (inv_mem u.2)
      have e1 : φ b (L2Orth.modMkHom hUV u) * (L2Orth.modMkHom hUV u)⁻¹ = modMk hUV _ hz := by
        show actH hV₁ hUN b (modMk hUV u u.2) * (modMk hUV u u.2)⁻¹ = _
        rw [actH_modMk hV₁ hUV hUN b u.2, ← modMk_inv hUV u.2, ← modMk_mul hUV hbu (inv_mem u.2)]
      rw [e1]
      have hzδ : (b : G) * u * (b : G)⁻¹ * (u : G)⁻¹ ∈ F8.Uγ S.V3 H (k : G) := by
        have h3 := hF98.F913_3 sk (X := S.V3) (Y := S.V3) (Or.inl rfl) (Or.inl rfl)
          (Subgroup.commutator_mem_commutator u.2 (Subgroup.mem_subgroupOf.mp hb))
        have h4 := (F8.Uγ S.V3 H (k : G)).inv_mem h3.2
        have e : (b : G) * u * (b : G)⁻¹ * (u : G)⁻¹ = ⁅(u : G), (b : G)⁆⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact h4
      show actH hV₁ hUN a (modMk hUV _ hz) = modMk hUV _ hz
      rw [actH_modMk hV₁ hUV hUN a hz]
      refine L2Orth.modMk_congr hUV ?_ _ _
      rw [F7.isElemAbelian_comm hUδab (Subgroup.mem_subgroupOf.mp ha) hzδ, mul_inv_cancel_right]
  have hcardA : Nat.card (autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (k : G)))
      (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) =
        2 ^ mIdx (F8.Uγ S.V3 H (k : G)) (F8.Dγ S.V3 (fsuV1 T V) H (k : G)) := by
    rw [hF98.toHypF91.card_autOn_tilde hUδH, ← hF98.Dγ_eq_inf_pCoreOf sk]
    exact HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hUδab)
  have hmδ : mIdx (F8.Uγ S.V3 H (k : G)) (F8.Dγ S.V3 (fsuV1 T V) H (k : G)) ≤ 2 := by
    have h1 : 2 ^ mIdx (F8.Uγ S.V3 H (k : G)) (F8.Dγ S.V3 (fsuV1 T V) H (k : G)) ≤ 2 ^ 2 := by
      rw [← hcardA, ← hF4]
      exact hA4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hidx : ((F8.DH S.V3 (fsuV1 T V) H (k : G)).subgroupOf (conjClosure S.V3 H)).index ≤ 4 := by
    have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.DH S.V3 (fsuV1 T V) H (k : G))
      (isPGroup_of_isElemAbelian hF98.F911_3)
    rw [Subgroup.relIndex] at h1
    rw [h1]
    calc 2 ^ mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (k : G)) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) (hle.trans hmδ)
      _ = 4 := by norm_num
  obtain ⟨x, hxU, hxD⟩ : ∃ x ∈ F8.Uγ S.V3 H (k : G), x ∉ F8.Dγ S.V3 (fsuV1 T V) H (k : G) := by
    by_contra hcon
    push Not at hcon
    have h1 : (F8.Dγ S.V3 (fsuV1 T V) H (k : G)).relIndex (F8.Uγ S.V3 H (k : G)) = 1 :=
      Subgroup.relIndex_eq_one.mpr hcon
    unfold mIdx at hpos
    rw [h1] at hpos
    simp at hpos
  have hxH : x ∈ H := hUδH hxU
  have hσMp := hUδMp ⟨x, hxH⟩ hxU
  have hσ2 : φ ⟨x, hxH⟩ ^ 2 = 1 := by
    have h1 : (⟨x, hxH⟩ : ↥H) ^ 2 = 1 :=
      Subtype.ext (by simpa using F7.isElemAbelian_pow_eq_one hUδab hxU)
    rw [← map_pow, h1, map_one]
  have hσ1 : φ ⟨x, hxH⟩ ≠ 1 := fun h =>
    hxD (mem_centralizerMod.mpr ⟨hxU, hV₁ hxH, fun u hu => (hφ1 ⟨x, hxH⟩).mp h u hu⟩)
  have h16 := L2Om.le_card_range_of_sq hF4 hd hπs hσMp hσ2 hσ1
  have h8 : Nat.card (L2Om.delta (φ ⟨x, hxH⟩)).range ≤ 4 * 2 := by
    rw [L2Orth.range_delta_eq hUV]
    refine (L2Orth.card_range_le_index_mul _ ((F8.DH S.V3 (fsuV1 T V) H (k : G)).subgroupOf
      (conjClosure S.V3 H))).trans (Nat.mul_le_mul hidx ?_)
    refine (L2Orth.card_map_delta_le hV₁ hUN hUV ⟨x, hxH⟩ (C := F8.A₁ (fsuV1 T V) (k : G))
      fun u hu => ?_).trans hF98.card_A₁.le
    show x * (u : G) * x⁻¹ * (u : G)⁻¹ ∈ _
    have h1 := (mem_centralizerMod.mp (Subgroup.mem_subgroupOf.mp hu)).2.2 x hxU
    have e : x * (u : G) * x⁻¹ * (u : G)⁻¹ = ((u : G) * x * (u : G)⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hF16 : Nat.card F ^ 2 = 16 := by rw [hF4]; norm_num
  omega

end Setting4

theorem case13816L2HatOrth_of
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) : Case13816L2HatOrth := by
  intro G _ _ T L V S hS hhat H hH K hK hne hHeq hn _ hO4
  exact S.orth_false h36 h37 h38 h122 h139 h1334 h13 hS hhat hH hK hne hHeq hn hO4

theorem case13816L2Hat_holds
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h1337 : Stmt13_3_7) (h13 : Lem13813) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (hA21 : AsA21SQTKSection) (h56 : AsB56) : Case13816L2Hat :=
  case13816L2Hat_of h37 h38 h122 (case13816L2HatTensor_of h36 h37 h38 h122 h139 h1334 h1337 h13
    hD36 hD37 hD321 hI5 hA21 h56 (case13816L2HatOrth_of h36 h37 h38 h122 h139 h1334 h13))

end CFSG.Quasithin.H13.A6
