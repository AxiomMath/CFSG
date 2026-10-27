module

public import CFSG.Quasithin.Background.C41PfW
public import CFSG.Quasithin.Background.C41PfM

public section

namespace CFSG.Quasithin.C41Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isStabilizedLine_of {R M K W V' : Subgroup G} {F : Type} [Field F] [Fintype F]
    (α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    {β : ↥W →* Multiplicative (Fin 3 → F)}
    (hnat : IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K)
      (CFSG.Assembly.LowTwoRank.StatedSL 3 F) α β)
    (g : SpecialLinearGroup (Fin 3) F) (hV'W : V' ≤ W) (hV'ne : V' ≠ ⊥)
    (hV'Z : V' ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆)
    (hline : ∀ u : ↥W, (u : G) ∈ V' ↔
      (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β u)) 2 = 0)
    (hpres : ∀ x : ↥K, (x : G) ∈ M → ∀ y : Fin 3 → F,
      (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) 2 = 0 →
      (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((α x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y)) 2 = 0)
    (hN : K ⊓ Subgroup.normalizer (V' : Set G) ≤ M) :
    IsStabilizedLineOfNatural F R M K V' := by
  classical
  have hnat₀ := hnat
  obtain ⟨hKW, hαs, hαk, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    intro x y hxy
    have hk : x * y⁻¹ ∈ β.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hβk] at hk
    have h1 : ((x * y⁻¹ : ↥W) : G) = 1 := Subgroup.mem_bot.mp hk
    exact mul_inv_eq_one.mp (Subtype.ext h1)
  set gi : Matrix (Fin 3) (Fin 3) F :=
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgi
  set L2 : Submodule F (Fin 3 → F) :=
    (flagSpace 3 F 2).map ((SpecialLinearGroup.toLin' g : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
      (Fin 3 → F) →ₗ[F] (Fin 3 → F)) with hL2
  have hmemL2 : ∀ y, y ∈ L2 ↔ (gi *ᵥ y) 2 = 0 := by
    intro y
    rw [hL2, Submodule.mem_map_equiv, mem_flagSpace]
    constructor
    · intro hy
      exact hy 2 le_rfl
    · intro hy k hk
      have hk2 : k = 2 := by
        have := k.isLt
        ext
        simp only [Fin.isValue, Fin.val_two]
        omega
      rw [hk2]
      exact hy
  have hL2fr : Module.finrank F ↥L2 = 2 := by
    rw [hL2, LinearEquiv.finrank_map_eq]
    exact finrank_flagSpace (by norm_num)
  have hiff : ∀ u : ↥W, (u : G) ∈ V' ↔ Multiplicative.toAdd (β u) ∈ L2 := fun u => by
    rw [hline, hmemL2]
  have hFL : IsFLineVia W V' β := ⟨hV'W, L2, hL2fr, hiff⟩
  have hMKN : M ⊓ K ≤ Subgroup.normalizer (V' : Set G) := by
    intro x hx
    apply mem_normalizer_of_map_le
    rintro _ ⟨v, hv, rfl⟩
    have hxw : x * v * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hKW hx.2) v).mp (hV'W hv)
    show x * v * x⁻¹ ∈ V'
    refine (hline ⟨_, hxw⟩).mpr ?_
    rw [hβe ⟨x, hx.2⟩ ⟨v, hV'W hv⟩ ⟨_, hxw⟩ rfl]
    exact hpres ⟨x, hx.2⟩ hx.1 _ ((hline ⟨v, hV'W hv⟩).mp hv)
  have hMKeq : M ⊓ K = K ⊓ Subgroup.normalizer (V' : Set G) :=
    le_antisymm (fun x hx => ⟨hx.2, hMKN hx⟩) (fun x hx => ⟨hN hx, hx.1⟩)
  set Z1 := ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆ with hZ1
  have hZ1n : K ≤ Subgroup.normalizer (Z1 : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ K
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F with he
  have hWZ : W ≤ Z1 := by
    set Y : AddSubgroup (Fin 3 → F) :=
      Subgroup.toAddSubgroup' (((W ⊓ Z1).subgroupOf W).map β) with hY
    have hYinv : ∀ A : SpecialLinearGroup (Fin 3) F, ∀ y ∈ Y,
        (A : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ Y := by
      intro A y hy
      obtain ⟨w, ⟨hwW, hwZ⟩, hwe⟩ := hy
      obtain ⟨k, hk⟩ := hαs (e A)
      have hkw : (k : G) * w * (k : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hKW k.2) w).mp w.2
      have hkz : (k : G) * w * (k : G)⁻¹ ∈ Z1 :=
        (Subgroup.mem_normalizer_iff.mp (hZ1n k.2) w).mp hwZ
      refine ⟨⟨_, hkw⟩, ⟨hkw, hkz⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      show Multiplicative.toAdd (β ⟨_, hkw⟩) = (A : Matrix (Fin 3) (Fin 3) F) *ᵥ y
      have hwy : Multiplicative.toAdd (β w) = y := by rw [hwe]; rfl
      rw [hβe k w ⟨_, hkw⟩ rfl, hwy, hk,
        CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
    rcases SL3N.eq_bot_or_eq_top_of_invariant Y hYinv with hYb | hYt
    · exfalso
      apply hV'ne
      rw [eq_bot_iff]
      intro v hv
      have hmem : Multiplicative.toAdd (β ⟨v, hV'W hv⟩) ∈ Y :=
        ⟨⟨v, hV'W hv⟩, ⟨hV'W hv, hV'Z hv⟩, rfl⟩
      rw [hYb, AddSubgroup.mem_bot] at hmem
      have h1 : β ⟨v, hV'W hv⟩ = 1 := congrArg Multiplicative.ofAdd hmem
      have h2 : (⟨v, hV'W hv⟩ : ↥W) = 1 := hβinj (h1.trans (map_one β).symm)
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
    · intro w hw
      have hmem : Multiplicative.toAdd (β ⟨w, hw⟩) ∈ Y := hYt ▸ AddSubgroup.mem_top _
      obtain ⟨w', ⟨-, hw'Z⟩, hw'e⟩ := hmem
      have hww : w' = ⟨w, hw⟩ := hβinj hw'e
      have hww' : (w' : G) = w := congrArg Subtype.val hww
      rw [← hww']
      exact hw'Z
  exact ⟨W, hWZ, α, β, hnat₀, hFL, hMKeq⟩

theorem c47_line_one {H R M L V K W : Subgroup G} (hP : C41Post H R M L V K) {F : Type} [Field F]
    [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    {β : ↥W →* Multiplicative (Fin 3 → F)}
    (hnat : IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K)
      (CFSG.Assembly.LowTwoRank.StatedSL 3 F) α β)
    (hMKmax : IsMaxParabolic2 K (M ⊓ K)) (hVW : V ≤ W)
    (hVZ : V ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆) :
    IsStabilizedLineOfNatural F R M K V ∧ IsPSL 2 2 n (ModO2 (conjClosure L M)) := by
  classical
  have hnat₀ := hnat
  obtain ⟨hKW, hαs, hαk, hβs, hβk, hβe⟩ := hnat
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F with he
  set α' : ↥K →* SpecialLinearGroup (Fin 3) F := e.symm.toMonoidHom.comp α with hα'
  have hα'm : ∀ k : ↥K, ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α' k : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro k
    rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F (α' k)]
    simp [hα', he]
  have hα's : Function.Surjective α' := e.symm.surjective.comp hαs
  have hα'k : α'.ker = CFSG.pCore 2 ↥K := by
    rw [← hαk]
    ext k
    simp [hα', MonoidHom.mem_ker]
  obtain ⟨g, j, hXsub, hXmem, hTO, hPrad, hpsl⟩ := c47_core hP hn hF α' hα's hα'k hMKmax
  refine ⟨?_, hpsl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.hyp
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := n) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four h4
  set M0 := conjClosure L M with hM0
  have hM0K : M0 ≤ K := hP.le
  have hKH : K ≤ H := le_of_mem_cComp hP.comp
  have hMM0 : M ≤ Subgroup.normalizer (M0 : Set G) := le_normalizer_conjClosure L M
  have hM0V : M0 ≤ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right V M0
    rwa [h.V_comm] at this
  have hO2M0 : pCoreOf 2 M0 ≤ pCoreOf 2 (M0 ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 M0).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 M0)
        ((h.le_M.trans hMM0).trans (normalizer_le_normalizer_pCoreOf 2 M0)))
      (pCoreOf_isPGroup 2 M0)
  have hVcen : ∀ v ∈ V, ∀ q ∈ pCoreOf 2 (M0 ⊔ R), q * v = v * q := fun v hv q hq =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h.V_center hv)).2 q hq
  have hβinj : Function.Injective β := by
    intro x y hxy
    have hk : x * y⁻¹ ∈ β.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hβk] at hk
    have h1 : ((x * y⁻¹ : ↥W) : G) = 1 := Subgroup.mem_bot.mp hk
    exact mul_inv_eq_one.mp (Subtype.ext h1)
  set bv : ↥V → (Fin 3 → F) := fun v => Multiplicative.toAdd (β ⟨v, hVW v.2⟩) with hbv
  have hconjV : ∀ (m : ↥K) (v : ↥V) (hmv : (m : G) * v * (m : G)⁻¹ ∈ V),
      bv ⟨_, hmv⟩ = ((α' m : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        bv v := fun m v hmv => by
    rw [← hα'm]
    exact hβe m ⟨v, hVW v.2⟩ ⟨_, hVW hmv⟩ rfl
  have hfix : ∀ r ∈ SL3N.rad3 (K := F) j, ∀ v : ↥V,
      ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv v =
        bv v := by
    intro r hr v
    obtain ⟨m, hm, hme⟩ := hXmem r (SL3N.rad3_le j hr)
    have hmT : (m : G) ∈ pCoreOf 2 M0 := hTO m hm (by
      rw [hme]
      simpa [mul_assoc] using hr)
    have hc : (m : G) * v * (m : G)⁻¹ = v := by
      rw [hVcen v v.2 m (hO2M0 hmT), mul_inv_cancel_right]
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V := by rw [hc]; exact v.2
    have h3 := hconjV m v hmv
    rw [← hme]
    rw [show (⟨_, hmv⟩ : ↥V) = v from Subtype.ext hc] at h3
    exact h3.symm
  have hVne : ∃ v : ↥V, bv v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply h.V_ne
    rw [eq_bot_iff]
    intro v hv
    have h1 : β ⟨v, hVW hv⟩ = 1 := congrArg Multiplicative.ofAdd (hall ⟨v, hv⟩)
    have h2 : (⟨v, hVW hv⟩ : ↥W) = 1 := hβinj (h1.trans (map_one β).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
  obtain rfl | rfl : j = 0 ∨ j = 1 := by
    rcases j with ⟨_ | _ | _, hj⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  · exfalso
    obtain ⟨v₀, hv₀⟩ := hVne
    apply h.V_ne
    have hfixM0 : ∀ (m : ↥K), (m : G) ∈ M0 → ∀ v : ↥V,
        ((α' m : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv v = bv v := by
      intro m hm v
      set w := ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv v with hw
      have hR0 : ∀ r ∈ SL3N.rad3 (K := F) 0,
          ((r : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := fun r hr =>
        (SL3N.conj_mulVec_fixed_iff g r (bv v)).mp (hfix r hr v)
      obtain ⟨hw1, hw2⟩ := SL3N.fixed_rad3_zero hK4 hR0
      have hn := hXsub m hm
      have h3 : ((g⁻¹ * α' m * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
          w := SL3N.mulVec_of_mem_perfectCore_zero hn hw1 hw2
      have h4 := (SL3N.conj_mulVec_fixed_iff g (g⁻¹ * α' m * g) (bv v)).mpr h3
      rwa [show g * (g⁻¹ * α' m * g) * g⁻¹ = α' m by group] at h4
    rw [eq_bot_iff, ← h.V_comm, Subgroup.commutator_le]
    intro v hv m hm
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hM0V hm) v).mp hv
    have h3 := hconjV ⟨m, hM0K hm⟩ ⟨v, hv⟩ hmv
    rw [hfixM0 ⟨m, hM0K hm⟩ hm ⟨v, hv⟩] at h3
    have h5 : (⟨_, hVW hmv⟩ : ↥W) = ⟨v, hVW hv⟩ := hβinj (Multiplicative.toAdd.injective h3)
    have h6 : m * v * m⁻¹ = v := congrArg Subtype.val h5
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc v * m * v⁻¹ * m⁻¹ = (m * v * m⁻¹ * v⁻¹)⁻¹ := by group
      _ = 1 := by rw [h6, mul_inv_cancel, inv_one]
  set gi : Matrix (Fin 3) (Fin 3) F :=
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgi
  set L2 : Submodule F (Fin 3 → F) :=
    (flagSpace 3 F 2).map ((SpecialLinearGroup.toLin' g : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
      (Fin 3 → F) →ₗ[F] (Fin 3 → F)) with hL2
  have hmemL2 : ∀ y, y ∈ L2 ↔ (gi *ᵥ y) 2 = 0 := by
    intro y
    rw [hL2, Submodule.mem_map_equiv, mem_flagSpace]
    constructor
    · intro hy
      exact hy 2 le_rfl
    · intro hy k hk
      have hk2 : k = 2 := by
        have := k.isLt
        ext
        simp only [Fin.isValue, Fin.val_two]
        omega
      rw [hk2]
      exact hy
  have hL2fr : Module.finrank F ↥L2 = 2 := by
    rw [hL2, LinearEquiv.finrank_map_eq]
    exact finrank_flagSpace (by norm_num)
  have hFix : ∀ y, y ∈ L2 ↔ ∀ r ∈ SL3N.rad3 (K := F) 1,
      ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
    intro y
    rw [hmemL2]
    constructor
    · intro hy r hr
      exact (SL3N.conj_mulVec_fixed_iff g r y).mpr (SL3N.mulVec_of_mem_rad3_one hr hy)
    · intro hy
      exact SL3N.fixed_rad3_one hK4 fun r hr => (SL3N.conj_mulVec_fixed_iff g r y).mp (hy r hr)
  have hVL : ∀ v : ↥V, bv v ∈ L2 := fun v => (hFix _).mpr fun r hr => hfix r hr v
  have hWV : ∀ y ∈ L2, ∃ v : ↥V, bv v = y := by
    intro y hy
    by_cases hy0 : y = 0
    · refine ⟨1, ?_⟩
      rw [hy0]
      show Multiplicative.toAdd (β ⟨1, hVW V.one_mem⟩) = 0
      rw [show (⟨1, hVW V.one_mem⟩ : ↥W) = 1 from rfl, map_one]
      rfl
    obtain ⟨v₀, hv₀⟩ := hVne
    set a := gi *ᵥ bv v₀ with ha
    set b := gi *ᵥ y with hb
    have ha2 : a 2 = 0 := (hmemL2 _).mp (hVL v₀)
    have hb2 : b 2 = 0 := (hmemL2 _).mp hy
    have hga : ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a = bv v₀ :=
      SL3N.mulVec_mulVec_inv g _
    have hgb : ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b = y :=
      SL3N.mulVec_mulVec_inv g _
    have ha0 : ![a 0, a 1] ≠ 0 := by
      intro h0
      apply hv₀
      have h00 : a 0 = 0 := congrFun h0 0
      have h01 : a 1 = 0 := congrFun h0 1
      have : a = 0 := by
        funext i
        fin_cases i
        · exact h00
        · exact h01
        · exact ha2
      rw [← hga, this, Matrix.mulVec_zero]
    have hb0 : ![b 0, b 1] ≠ 0 := by
      intro h0
      apply hy0
      have h00 : b 0 = 0 := congrFun h0 0
      have h01 : b 1 = 0 := congrFun h0 1
      have : b = 0 := by
        funext i
        fin_cases i
        · exact h00
        · exact h01
        · exact hb2
      rw [← hgb, this, Matrix.mulVec_zero]
    obtain ⟨A, hA⟩ := SpN.exists_sl2_mulVec_eq ha0 hb0
    have hn : embSL 1 A ∈ perfectCore (Q3 F 1) := embSL_mem_perfectCore hK4 1 A
    have hna : ((embSL 1 A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a =
        b := by
      rw [SL3N.embSL_one_mulVec A ha2, hA]
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact hb2.symm
    obtain ⟨m, hm, hme⟩ := hXmem _ hn
    have hmv : (m : G) * v₀ * (m : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hM0V hm) v₀).mp v₀.2
    refine ⟨⟨_, hmv⟩, ?_⟩
    rw [hconjV m v₀ hmv, hme, ← hga, Matrix.mulVec_mulVec]
    have e : ((g * embSL 1 A * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((embSL 1 A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have : g * embSL 1 A * g⁻¹ * g = g * embSL 1 A := by group
      exact congrArg Subtype.val this
    rw [e, ← Matrix.mulVec_mulVec, hna, hgb]
  have hline : ∀ u : ↥W, (u : G) ∈ V ↔ (gi *ᵥ Multiplicative.toAdd (β u)) 2 = 0 := by
    intro u
    constructor
    · intro hu
      exact (hmemL2 _).mp (hVL ⟨u, hu⟩)
    · intro hu
      obtain ⟨v, hv⟩ := hWV _ ((hmemL2 _).mpr hu)
      have h1 : β ⟨v, hVW v.2⟩ = β u := Multiplicative.toAdd.injective hv
      have h2 : (⟨v, hVW v.2⟩ : ↥W) = u := hβinj h1
      rw [← h2]
      exact v.2
  have hpres : ∀ x : ↥K, (x : G) ∈ M → ∀ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 →
      (gi *ᵥ (((α x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y)) 2 = 0 := by
    intro x hxM y hy
    rw [hα'm, ← hmemL2, hFix]
    intro r hr
    obtain ⟨r', hr', he'⟩ := hPrad x hxM r hr
    have e : g * r * g⁻¹ * α' x = α' x * (g * r' * g⁻¹) := by
      rw [← he']
      group
    have h5 := (hFix _).mp ((hmemL2 _).mpr hy) r' hr'
    calc ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
        ((g * r * g⁻¹ * α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
          rw [Matrix.mulVec_mulVec]
          rfl
      _ = ((α' x * (g * r' * g⁻¹) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ y := by rw [e]
      _ = ((α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((g * r' * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) := by
          rw [Matrix.mulVec_mulVec]
          rfl
      _ = ((α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by rw [h5]
  exact isStabilizedLine_of α hnat₀ g hVW h.V_ne hVZ hline hpres
    fun x hx => h.V_norm ⟨hKH hx.1, hx.2⟩

section Graph

variable {K Q : Subgroup G} {F : Type} [Field F]
  {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
  {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)} (i₀ i₁ : Fin 2) (c : F)

omit [Finite G] in
theorem fin2_eq_or_eq {i₀ i₁ : Fin 2} (hi : i₀ ≠ i₁) (i : Fin 2) : i = i₀ ∨ i = i₁ := by
  rw [Ne, Fin.ext_iff] at hi
  rw [Fin.ext_iff, Fin.ext_iff]
  have := i.isLt
  have := i₀.isLt
  have := i₁.isLt
  omega

@[expose] def graphRel : (Fin 2 → Fin 3 → F) →+ (Fin 3 → F) where
  toFun x := x i₁ - c • x i₀
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, smul_add]
    abel

variable (β) in
@[expose] def graphSub : Subgroup G :=
  ((AddSubgroup.toSubgroup (graphRel (F := F) i₀ i₁ c).ker).comap β).map Q.subtype

omit [Finite G] in
theorem mem_graphSub {q : G} : q ∈ graphSub β i₀ i₁ c ↔ ∃ hq : q ∈ Q,
    Multiplicative.toAdd (β ⟨q, hq⟩) i₁ = c • Multiplicative.toAdd (β ⟨q, hq⟩) i₀ := by
  constructor
  · rintro ⟨q', hq', rfl⟩
    refine ⟨q'.2, ?_⟩
    have : graphRel i₀ i₁ c (Multiplicative.toAdd (β q')) = 0 := hq'
    rw [← sub_eq_zero]
    exact this
  · rintro ⟨hq, he⟩
    refine ⟨⟨q, hq⟩, ?_, rfl⟩
    show graphRel i₀ i₁ c (Multiplicative.toAdd (β ⟨q, hq⟩)) = 0
    show Multiplicative.toAdd (β ⟨q, hq⟩) i₁ - c • Multiplicative.toAdd (β ⟨q, hq⟩) i₀ = 0
    rw [he, sub_self]

omit [Finite G] in
theorem graphSub_le : graphSub β i₀ i₁ c ≤ Q := by
  rintro _ ⟨q, -, rfl⟩
  exact q.2

variable (β) in
@[expose] noncomputable def graphCoord : ↥(graphSub β i₀ i₁ c) →* Multiplicative (Fin 3 → F) :=
  (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 2 => Fin 3 → F) i₀)).comp
    (β.comp (Subgroup.inclusion (graphSub_le i₀ i₁ c)))

omit [Finite G] in
theorem graphCoord_apply (w : ↥(graphSub β i₀ i₁ c)) :
    Multiplicative.toAdd (graphCoord β i₀ i₁ c w) =
      Multiplicative.toAdd (β (Subgroup.inclusion (graphSub_le i₀ i₁ c) w)) i₀ := rfl

theorem graph_natural (hα : IsModO2Surj K α)
    (hQ : K ≤ Subgroup.normalizer (Q : Set G)) (hβs : Function.Surjective β)
    (hβk : β.ker = (⊥ : Subgroup G).subgroupOf Q)
    (hβe : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
        (Multiplicative.toAdd (β u) i))
    (hi : i₀ ≠ i₁) :
    IsNaturalSectionWith K (graphSub β i₀ i₁ c) ⊥ (CFSG.pCore 2 ↥K)
      (CFSG.Assembly.LowTwoRank.StatedSL 3 F) α (graphCoord β i₀ i₁ c) := by
  classical
  have hβe' : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i = ((α a : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u) i := by
    intro a u v h i
    have := hβe a u v h i
    simpa [moduleAct] using this
  have hall : ∀ i : Fin 2, i = i₀ ∨ i = i₁ := fun i => fin2_eq_or_eq hi i
  refine ⟨fun k hk => ?_, hα.1, hα.2, fun y => ?_, ?_, fun a u v h => ?_⟩
  ·
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    obtain ⟨hqQ, he⟩ := (mem_graphSub i₀ i₁ c).mp hq
    have hkq : k * q * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQ hk) q).mp hqQ
    refine (mem_graphSub i₀ i₁ c).mpr ⟨hkq, ?_⟩
    rw [hβe' ⟨k, hk⟩ ⟨q, hqQ⟩ ⟨_, hkq⟩ rfl, hβe' ⟨k, hk⟩ ⟨q, hqQ⟩ ⟨_, hkq⟩ rfl, he,
      Matrix.mulVec_smul]
  ·
    set x : Fin 2 → Fin 3 → F := fun i => if i = i₀ then Multiplicative.toAdd y
      else c • Multiplicative.toAdd y with hx
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd x)
    have hq' : Multiplicative.toAdd (β q) = x := by rw [hq]; rfl
    have hmem : (q : G) ∈ graphSub β i₀ i₁ c := by
      refine (mem_graphSub i₀ i₁ c).mpr ⟨q.2, ?_⟩
      rw [show (⟨(q : G), q.2⟩ : ↥Q) = q from rfl, hq']
      simp [hx, Ne.symm hi]
    refine ⟨⟨q, hmem⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [graphCoord_apply]
    show Multiplicative.toAdd (β q) i₀ = Multiplicative.toAdd y
    rw [hq']
    simp [hx]
  ·
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hw
      obtain ⟨hwQ, he⟩ := (mem_graphSub i₀ i₁ c).mp w.2
      have h0 : Multiplicative.toAdd (β ⟨w, hwQ⟩) i₀ = 0 := by
        have := congrArg Multiplicative.toAdd hw
        rw [graphCoord_apply] at this
        exact this
      have h1 : Multiplicative.toAdd (β ⟨w, hwQ⟩) = 0 := by
        funext i
        rcases hall i with rfl | rfl
        · exact h0
        · rw [he, h0, smul_zero]
          rfl
      have hk : (⟨w, hwQ⟩ : ↥Q) ∈ β.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Multiplicative.ofAdd h1
      rw [hβk] at hk
      exact hk
    · intro hw
      have hw1 : w = 1 := Subtype.ext (Subgroup.mem_bot.mp hw)
      rw [hw1, map_one]
  ·
    rw [graphCoord_apply, graphCoord_apply]
    exact hβe' a _ _ h i₀

end Graph

theorem c47_line_two {H R M L V K Q : Subgroup G} (hP : C41Post H R M L V K) {F : Type}
    [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hα : IsModO2Surj K α)
    (hsum : IsSumOfNaturalModulesVia K Q ⊥ α false 2)
    (hMKmax : IsMaxParabolic2 K (M ⊓ K)) (hVQ : V ≤ Q)
    (hVZ : V ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆) :
    (IsStabilizedLineOfNatural F R M K V ∨ ∃ V₁ V₂ : Subgroup G,
        IsStabilizedLineOfNatural F R M K V₁ ∧ IsStabilizedLineOfNatural F R M K V₂ ∧
          V = V₁ ⊔ V₂) ∧
      IsPSL 2 2 n (ModO2 (conjClosure L M)) := by
  classical
  obtain ⟨hKQ, -, β, hβs, hβk, hβe⟩ := hsum
  have hβe' : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i = ((α a : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u) i := by
    intro a u v h i
    have := hβe a u v h i
    simpa [moduleAct] using this
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F with he
  set α' : ↥K →* SpecialLinearGroup (Fin 3) F := e.symm.toMonoidHom.comp α with hα'
  have hα'm : ∀ k : ↥K, ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α' k : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro k
    rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F (α' k)]
    simp [hα', he]
  have hα's : Function.Surjective α' := e.symm.surjective.comp hα.1
  have hα'k : α'.ker = CFSG.pCore 2 ↥K := by
    rw [← hα.2]
    ext k
    simp [hα', MonoidHom.mem_ker]
  obtain ⟨g, j, hXsub, hXmem, hTO, hPrad, hpsl⟩ := c47_core hP hn hF α' hα's hα'k hMKmax
  refine ⟨?_, hpsl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.hyp
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := n) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four h4
  set M0 := conjClosure L M with hM0
  have hM0K : M0 ≤ K := hP.le
  have hKH : K ≤ H := le_of_mem_cComp hP.comp
  have hMM0 : M ≤ Subgroup.normalizer (M0 : Set G) := le_normalizer_conjClosure L M
  have hM0V : M0 ≤ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right V M0
    rwa [h.V_comm] at this
  have hO2M0 : pCoreOf 2 M0 ≤ pCoreOf 2 (M0 ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 M0).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 M0)
        ((h.le_M.trans hMM0).trans (normalizer_le_normalizer_pCoreOf 2 M0)))
      (pCoreOf_isPGroup 2 M0)
  have hVcen : ∀ v ∈ V, ∀ q ∈ pCoreOf 2 (M0 ⊔ R), q * v = v * q := fun v hv q hq =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h.V_center hv)).2 q hq
  have hβinj : Function.Injective β := by
    intro x y hxy
    have hk : x * y⁻¹ ∈ β.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hβk] at hk
    have h1 : ((x * y⁻¹ : ↥Q) : G) = 1 := Subgroup.mem_bot.mp hk
    exact mul_inv_eq_one.mp (Subtype.ext h1)
  set bv : ↥V → (Fin 2 → Fin 3 → F) := fun v => Multiplicative.toAdd (β ⟨v, hVQ v.2⟩) with hbv
  have hconjV : ∀ (m : ↥K) (v : ↥V) (hmv : (m : G) * v * (m : G)⁻¹ ∈ V) (i : Fin 2),
      bv ⟨_, hmv⟩ i = ((α' m : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        bv v i := fun m v hmv i => by
    rw [← hα'm]
    exact hβe' m ⟨v, hVQ v.2⟩ ⟨_, hVQ hmv⟩ rfl i
  have hfix : ∀ r ∈ SL3N.rad3 (K := F) j, ∀ (v : ↥V) (i : Fin 2),
      ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv v i =
        bv v i := by
    intro r hr v i
    obtain ⟨m, hm, hme⟩ := hXmem r (SL3N.rad3_le j hr)
    have hmT : (m : G) ∈ pCoreOf 2 M0 := hTO m hm (by
      rw [hme]
      simpa [mul_assoc] using hr)
    have hc : (m : G) * v * (m : G)⁻¹ = v := by
      rw [hVcen v v.2 m (hO2M0 hmT), mul_inv_cancel_right]
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V := by rw [hc]; exact v.2
    have h3 := hconjV m v hmv i
    rw [← hme]
    rw [show (⟨_, hmv⟩ : ↥V) = v from Subtype.ext hc] at h3
    exact h3.symm
  have hbv0 : ∀ v : ↥V, bv v = 0 → (v : G) = 1 := by
    intro v hv
    have h1 : β ⟨v, hVQ v.2⟩ = 1 := congrArg Multiplicative.ofAdd hv
    have h2 : (⟨v, hVQ v.2⟩ : ↥Q) = 1 := hβinj (h1.trans (map_one β).symm)
    exact congrArg Subtype.val h2
  have hVne : ∃ v : ↥V, bv v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply h.V_ne
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.mpr (hbv0 ⟨v, hv⟩ (hall ⟨v, hv⟩))
  obtain rfl | rfl : j = 0 ∨ j = 1 := by
    rcases j with ⟨_ | _ | _, hj⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  · exfalso
    apply h.V_ne
    have hfixM0 : ∀ (m : ↥K), (m : G) ∈ M0 → ∀ (v : ↥V) (i : Fin 2),
        ((α' m : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv v i =
          bv v i := by
      intro m hm v i
      set w := ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv v i
        with hw
      have hR0 : ∀ r ∈ SL3N.rad3 (K := F) 0,
          ((r : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := fun r hr =>
        (SL3N.conj_mulVec_fixed_iff g r (bv v i)).mp (hfix r hr v i)
      obtain ⟨hw1, hw2⟩ := SL3N.fixed_rad3_zero hK4 hR0
      have hn := hXsub m hm
      have h3 : ((g⁻¹ * α' m * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          w = w := SL3N.mulVec_of_mem_perfectCore_zero hn hw1 hw2
      have h4 := (SL3N.conj_mulVec_fixed_iff g (g⁻¹ * α' m * g) (bv v i)).mpr h3
      rwa [show g * (g⁻¹ * α' m * g) * g⁻¹ = α' m by group] at h4
    rw [eq_bot_iff, ← h.V_comm, Subgroup.commutator_le]
    intro v hv m hm
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hM0V hm) v).mp hv
    have h3 : bv ⟨_, hmv⟩ = bv ⟨v, hv⟩ := by
      funext i
      rw [hconjV ⟨m, hM0K hm⟩ ⟨v, hv⟩ hmv i, hfixM0 ⟨m, hM0K hm⟩ hm ⟨v, hv⟩ i]
    have h5 : (⟨_, hVQ hmv⟩ : ↥Q) = ⟨v, hVQ hv⟩ := hβinj (Multiplicative.toAdd.injective h3)
    have h6 : m * v * m⁻¹ = v := congrArg Subtype.val h5
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc v * m * v⁻¹ * m⁻¹ = (m * v * m⁻¹ * v⁻¹)⁻¹ := by group
      _ = 1 := by rw [h6, mul_inv_cancel, inv_one]
  set gi : Matrix (Fin 3) (Fin 3) F :=
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgi
  set gm : Matrix (Fin 3) (Fin 3) F := ((g : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hgm
  have hL : ∀ (v : ↥V) (i : Fin 2), (gi *ᵥ bv v i) 2 = 0 := fun v i =>
    SL3N.fixed_rad3_one hK4 fun r hr =>
      (SL3N.conj_mulVec_fixed_iff g r (bv v i)).mp (hfix r hr v i)
  have hFix : ∀ y, (gi *ᵥ y) 2 = 0 ↔ ∀ r ∈ SL3N.rad3 (K := F) 1,
      ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
    intro y
    constructor
    · intro hy r hr
      exact (SL3N.conj_mulVec_fixed_iff g r y).mpr (SL3N.mulVec_of_mem_rad3_one hr hy)
    · intro hy
      exact SL3N.fixed_rad3_one hK4 fun r hr => (SL3N.conj_mulVec_fixed_iff g r y).mp (hy r hr)
  set pr : (Fin 3 → F) → (Fin 2 → F) := fun y => ![(gi *ᵥ y) 0, (gi *ᵥ y) 1] with hpr
  have hprinj : ∀ y y' : Fin 3 → F, (gi *ᵥ y) 2 = 0 → (gi *ᵥ y') 2 = 0 → pr y = pr y' →
      y = y' := by
    intro y y' hy hy' he
    have h0 : (gi *ᵥ y) 0 = (gi *ᵥ y') 0 := congrFun he 0
    have h1 : (gi *ᵥ y) 1 = (gi *ᵥ y') 1 := congrFun he 1
    have hg : gi *ᵥ y = gi *ᵥ y' := by
      funext i
      match i with
      | 0 => exact h0
      | 1 => exact h1
      | 2 => rw [hy, hy']
    rw [← SL3N.mulVec_mulVec_inv g y, ← SL3N.mulVec_mulVec_inv g y']
    exact congrArg _ hg
  have hpr0 : ∀ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 → pr y = 0 → y = 0 := by
    intro y hy h0
    exact hprinj y 0 hy (by simp) (by rw [h0]; funext i; fin_cases i <;> simp [hpr])
  have hprsmul : ∀ (c : F) (y : Fin 3 → F), pr (c • y) = c • pr y := by
    intro c y
    funext i
    fin_cases i <;> simp [hpr, Matrix.mulVec_smul]
  have hgigm : ∀ z : Fin 3 → F, gi *ᵥ (gm *ᵥ z) = z := fun z => SL3N.mulVec_inv_mulVec g z
  have hgmgi : ∀ z : Fin 3 → F, gm *ᵥ (gi *ᵥ z) = z := fun z => SL3N.mulVec_mulVec_inv g z
  have hprsurj : ∀ a : Fin 2 → F, ∃ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 ∧ pr y = a := by
    intro a
    refine ⟨gm *ᵥ ![a 0, a 1, 0], ?_, ?_⟩
    · rw [hgigm]
      rfl
    · show ![(gi *ᵥ (gm *ᵥ ![a 0, a 1, 0])) 0, (gi *ᵥ (gm *ᵥ ![a 0, a 1, 0])) 1] = a
      rw [hgigm]
      funext i
      match i with
      | 0 => rfl
      | 1 => rfl
  set PrHom : (Fin 2 → Fin 3 → F) →+ (Fin 2 → F) × (Fin 2 → F) :=
    { toFun := fun x => (pr (x 0), pr (x 1))
      map_zero' := by
        refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp [hpr]
      map_add' := fun x y => by
        refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp [hpr, Matrix.mulVec_add] }
    with hPrHom
  set D : AddSubgroup ((Fin 2 → F) × (Fin 2 → F)) :=
    (Subgroup.toAddSubgroup' ((V.subgroupOf Q).map β)).map PrHom with hD
  have hDmem : ∀ p, p ∈ D ↔ ∃ v : ↥V, (pr (bv v 0), pr (bv v 1)) = p := by
    intro p
    constructor
    · rintro ⟨x, ⟨q, hqV, hqe⟩, rfl⟩
      refine ⟨⟨q, hqV⟩, ?_⟩
      have hx : bv ⟨q, hqV⟩ = x := by
        show Multiplicative.toAdd (β ⟨q, hVQ hqV⟩) = x
        rw [show (⟨(q : G), hVQ hqV⟩ : ↥Q) = q from rfl, hqe]
        rfl
      rw [hx]
      rfl
    · rintro ⟨v, rfl⟩
      exact ⟨bv v, ⟨⟨v, hVQ v.2⟩, v.2, rfl⟩, rfl⟩
  have hDinv : ∀ A : SpecialLinearGroup (Fin 2) F, ∀ p ∈ D,
      ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ p.1, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ p.2) ∈ D := by
    intro A p hp
    obtain ⟨v, rfl⟩ := (hDmem p).mp hp
    have hn : embSL 1 A ∈ perfectCore (Q3 F 1) := embSL_mem_perfectCore hK4 1 A
    obtain ⟨m, hm, hme⟩ := hXmem _ hn
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hM0V hm) v).mp v.2
    have hact : ∀ i : Fin 2,
        pr (bv ⟨_, hmv⟩ i) = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ pr (bv v i) := by
      intro i
      rw [hconjV m v hmv i, hme]
      have e1 : gi *ᵥ (((g * embSL 1 A * g⁻¹ : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ bv v i) =
          ((embSL 1 A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (gi *ᵥ bv v i) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        have : g⁻¹ * (g * embSL 1 A * g⁻¹) = embSL 1 A * g⁻¹ := by group
        exact congrArg Subtype.val this
      funext k
      fin_cases k
      · show (gi *ᵥ _) 0 = _
        rw [e1, SL3N.embSL_one_mulVec A (hL v i)]
        rfl
      · show (gi *ᵥ _) 1 = _
        rw [e1, SL3N.embSL_one_mulVec A (hL v i)]
        rfl
    refine (hDmem _).mpr ⟨⟨_, hmv⟩, ?_⟩
    rw [hact 0, hact 1]
  have hpres : ∀ x : ↥K, (x : G) ∈ M → ∀ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 →
      (gi *ᵥ (((α x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y)) 2 = 0 := by
    intro x hxM y hy
    rw [hα'm, hFix]
    intro r hr
    obtain ⟨r', hr', he'⟩ := hPrad x hxM r hr
    have e : g * r * g⁻¹ * α' x = α' x * (g * r' * g⁻¹) := by
      rw [← he']
      group
    have h5 := (hFix _).mp hy r' hr'
    calc ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
        ((g * r * g⁻¹ * α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
          rw [Matrix.mulVec_mulVec]
          rfl
      _ = ((α' x * (g * r' * g⁻¹) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ y := by rw [e]
      _ = ((α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((g * r' * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) := by
          rw [Matrix.mulVec_mulVec]
          rfl
      _ = ((α' x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by rw [h5]
  have hnatG : ∀ (i₀ i₁ : Fin 2) (c : F), i₀ ≠ i₁ → IsNaturalSectionWith K (graphSub β i₀ i₁ c)
      ⊥ (CFSG.pCore 2 ↥K) (CFSG.Assembly.LowTwoRank.StatedSL 3 F) α (graphCoord β i₀ i₁ c) :=
    fun i₀ i₁ c hi => graph_natural i₀ i₁ c hα hKQ hβs hβk hβe hi
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rcases SL3N.sl2_submodule_pair D hDinv with hDb | hDt | ⟨c, hDc⟩ | hDi
  ·
    exfalso
    obtain ⟨v₀, hv₀⟩ := hVne
    have hmem : (pr (bv v₀ 0), pr (bv v₀ 1)) ∈ D := (hDmem _).mpr ⟨v₀, rfl⟩
    rw [hDb, AddSubgroup.mem_bot] at hmem
    apply hv₀
    funext i
    have h0 : pr (bv v₀ 0) = 0 := congrArg Prod.fst hmem
    have h1 : pr (bv v₀ 1) = 0 := congrArg Prod.snd hmem
    rcases fin2_eq_or_eq h01 i with rfl | rfl
    · exact hpr0 _ (hL v₀ 0) h0
    · exact hpr0 _ (hL v₀ 1) h1
  ·
    right
    have hT2 : ∀ y₀ y₁ : Fin 3 → F, (gi *ᵥ y₀) 2 = 0 → (gi *ᵥ y₁) 2 = 0 →
        ∃ v : ↥V, bv v 0 = y₀ ∧ bv v 1 = y₁ := by
      intro y₀ y₁ h0 h1
      have hmem : (pr y₀, pr y₁) ∈ D := hDt ▸ AddSubgroup.mem_top _
      obtain ⟨v, hv⟩ := (hDmem _).mp hmem
      exact ⟨v, hprinj _ _ (hL v 0) h0 (congrArg Prod.fst hv),
        hprinj _ _ (hL v 1) h1 (congrArg Prod.snd hv)⟩
    have hT1 : ∀ u : ↥Q, (u : G) ∈ V ↔ (gi *ᵥ Multiplicative.toAdd (β u) 0) 2 = 0 ∧
        (gi *ᵥ Multiplicative.toAdd (β u) 1) 2 = 0 := by
      intro u
      constructor
      · intro hu
        exact ⟨hL ⟨u, hu⟩ 0, hL ⟨u, hu⟩ 1⟩
      · rintro ⟨h0, h1⟩
        obtain ⟨v, hv0, hv1⟩ := hT2 _ _ h0 h1
        have hβ : β ⟨v, hVQ v.2⟩ = β u := by
          apply Multiplicative.toAdd.injective
          funext i
          rcases fin2_eq_or_eq h01 i with rfl | rfl
          · exact hv0
          · exact hv1
        rw [← hβinj hβ]
        exact v.2
    have hgi0 : (gi *ᵥ (0 : Fin 3 → F)) 2 = 0 := by simp
    have hline : ∀ (i₀ i₁ : Fin 2), i₀ ≠ i₁ →
        (∀ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 → ∃ v : ↥V, bv v i₀ = y ∧ bv v i₁ = 0) →
        IsStabilizedLineOfNatural F R M K (V ⊓ graphSub β i₀ i₁ 0) := by
      intro i₀ i₁ hi hT2i
      have hall := fin2_eq_or_eq hi
      have hboth : ∀ u : ↥Q, (gi *ᵥ Multiplicative.toAdd (β u) i₀) 2 = 0 →
          (gi *ᵥ Multiplicative.toAdd (β u) i₁) 2 = 0 → (u : G) ∈ V := by
        intro u h0 h1
        refine (hT1 u).mpr ⟨?_, ?_⟩
        · rcases hall 0 with h | h
          · rw [h]; exact h0
          · rw [h]; exact h1
        · rcases hall 1 with h | h
          · rw [h]; exact h0
          · rw [h]; exact h1
      have hcoord : ∀ u : ↥Q, (u : G) ∈ V → ∀ i : Fin 2,
          (gi *ᵥ Multiplicative.toAdd (β u) i) 2 = 0 := by
        intro u hu i
        rcases fin2_eq_or_eq h01 i with rfl | rfl
        · exact ((hT1 u).mp hu).1
        · exact ((hT1 u).mp hu).2
      have hN : K ⊓ Subgroup.normalizer ((V ⊓ graphSub β i₀ i₁ 0 : Subgroup G) : Set G) ≤ M := by
        intro x hx
        have hpx : ∀ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 →
            (gi *ᵥ (((α ⟨x, hx.1⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y)) 2 = 0 := by
          intro y hy
          obtain ⟨v, hv0, hv1⟩ := hT2i y hy
          have hvW : (v : G) ∈ V ⊓ graphSub β i₀ i₁ 0 := by
            refine ⟨v.2, (mem_graphSub i₀ i₁ 0).mpr ⟨hVQ v.2, ?_⟩⟩
            rw [zero_smul]
            exact hv1
          have hxv := (Subgroup.mem_normalizer_iff.mp hx.2 v).mp hvW
          have hxQ : x * v * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ hx.1) v).mp (hVQ v.2)
          have h3 := hcoord ⟨_, hxQ⟩ hxv.1 i₀
          rw [hβe' ⟨x, hx.1⟩ ⟨v, hVQ v.2⟩ ⟨_, hxQ⟩ rfl i₀] at h3
          rw [← hv0]
          exact h3
        have hxV : x ∈ Subgroup.normalizer (V : Set G) := by
          apply mem_normalizer_of_map_le
          rintro _ ⟨v, hv, rfl⟩
          have hxQ : x * v * x⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp (hKQ hx.1) v).mp (hVQ hv)
          show x * v * x⁻¹ ∈ V
          refine (hT1 ⟨_, hxQ⟩).mpr ⟨?_, ?_⟩
          · rw [hβe' ⟨x, hx.1⟩ ⟨v, hVQ hv⟩ ⟨_, hxQ⟩ rfl 0]
            exact hpx _ (hcoord ⟨v, hVQ hv⟩ hv 0)
          · rw [hβe' ⟨x, hx.1⟩ ⟨v, hVQ hv⟩ ⟨_, hxQ⟩ rfl 1]
            exact hpx _ (hcoord ⟨v, hVQ hv⟩ hv 1)
        exact h.V_norm ⟨hKH hx.1, hxV⟩
      have hl : ∀ u : ↥(graphSub β i₀ i₁ 0), (u : G) ∈ V ⊓ graphSub β i₀ i₁ 0 ↔
          (gi *ᵥ Multiplicative.toAdd (graphCoord β i₀ i₁ 0 u)) 2 = 0 := by
        intro u
        rw [graphCoord_apply]
        obtain ⟨huQ, hu1⟩ := (mem_graphSub i₀ i₁ 0).mp u.2
        rw [zero_smul] at hu1
        constructor
        · rintro ⟨huV, -⟩
          exact hcoord _ huV i₀
        · intro hu
          refine ⟨hboth _ hu ?_, u.2⟩
          show (gi *ᵥ Multiplicative.toAdd (β ⟨u, huQ⟩) i₁) 2 = 0
          rw [hu1]
          exact hgi0
      have hne : V ⊓ graphSub β i₀ i₁ 0 ≠ ⊥ := by
        intro hb
        obtain ⟨y, hy, hpy⟩ := hprsurj ![1, 0]
        obtain ⟨v, hv0, hv1⟩ := hT2i y hy
        have hvW : (v : G) ∈ V ⊓ graphSub β i₀ i₁ 0 := by
          refine ⟨v.2, (mem_graphSub i₀ i₁ 0).mpr ⟨hVQ v.2, ?_⟩⟩
          rw [zero_smul]
          exact hv1
        rw [hb, Subgroup.mem_bot] at hvW
        have hbv : bv v = 0 := by
          have : (⟨v, hVQ v.2⟩ : ↥Q) = 1 := Subtype.ext hvW
          show Multiplicative.toAdd (β ⟨v, hVQ v.2⟩) = 0
          rw [this, map_one]
          rfl
        have hy0 : y = 0 := by rw [← hv0, hbv]; rfl
        have := congrFun hpy 0
        rw [hy0] at this
        simp [hpr] at this
      exact isStabilizedLine_of α (hnatG i₀ i₁ 0 hi) g inf_le_right hne (inf_le_left.trans hVZ)
        hl hpres hN
    have hT20 : ∀ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 → ∃ v : ↥V, bv v 0 = y ∧ bv v 1 = 0 :=
      fun y hy => hT2 y 0 hy hgi0
    have hT21 : ∀ y : Fin 3 → F, (gi *ᵥ y) 2 = 0 → ∃ v : ↥V, bv v 1 = y ∧ bv v 0 = 0 :=
      fun y hy => by
        obtain ⟨v, hv0, hv1⟩ := hT2 0 y hgi0 hy
        exact ⟨v, hv1, hv0⟩
    refine ⟨V ⊓ graphSub β 0 1 0, V ⊓ graphSub β 1 0 0, hline 0 1 h01 hT20,
      hline 1 0 h01.symm hT21, le_antisymm (fun v hv => ?_) (sup_le inf_le_left inf_le_left)⟩
    obtain ⟨v₁, h10, h11⟩ := hT20 _ (hL ⟨v, hv⟩ 0)
    obtain ⟨v₂, h21, h20⟩ := hT21 _ (hL ⟨v, hv⟩ 1)
    have hv₁ : (v₁ : G) ∈ V ⊓ graphSub β 0 1 0 := by
      refine ⟨v₁.2, (mem_graphSub 0 1 0).mpr ⟨hVQ v₁.2, ?_⟩⟩
      rw [zero_smul]
      exact h11
    have hv₂ : (v₂ : G) ∈ V ⊓ graphSub β 1 0 0 := by
      refine ⟨v₂.2, (mem_graphSub 1 0 0).mpr ⟨hVQ v₂.2, ?_⟩⟩
      rw [zero_smul]
      exact h20
    have hprod : (v₁ : G) * v₂ = v := by
      have hβ : β (⟨v₁, hVQ v₁.2⟩ * ⟨v₂, hVQ v₂.2⟩) = β ⟨v, hVQ hv⟩ := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, toAdd_mul]
        funext i
        rcases fin2_eq_or_eq h01 i with rfl | rfl
        · show bv v₁ 0 + bv v₂ 0 = bv ⟨v, hv⟩ 0
          rw [h10, h20, add_zero]
        · show bv v₁ 1 + bv v₂ 1 = bv ⟨v, hv⟩ 1
          rw [h11, h21, zero_add]
      exact congrArg Subtype.val (hβinj hβ)
    rw [← hprod]
    exact Subgroup.mul_mem_sup hv₁ hv₂
  ·
    left
    have hVW : V ≤ graphSub β 0 1 c := by
      intro v hv
      refine (mem_graphSub 0 1 c).mpr ⟨hVQ hv, ?_⟩
      have hmem : (pr (bv ⟨v, hv⟩ 0), pr (bv ⟨v, hv⟩ 1)) ∈ D := (hDmem _).mpr ⟨⟨v, hv⟩, rfl⟩
      have h1 := (hDc _).mp hmem
      rw [← hprsmul] at h1
      refine hprinj _ _ (hL ⟨v, hv⟩ 1) ?_ h1
      show (gi *ᵥ (c • bv ⟨v, hv⟩ 0)) 2 = 0
      rw [Matrix.mulVec_smul, Pi.smul_apply, hL ⟨v, hv⟩ 0, smul_zero]
    exact (c47_line_one hP hn hF α (hnatG 0 1 c h01) hMKmax hVW hVZ).1
  ·
    left
    have hVW : V ≤ graphSub β 1 0 0 := by
      intro v hv
      refine (mem_graphSub 1 0 0).mpr ⟨hVQ hv, ?_⟩
      have hmem : (pr (bv ⟨v, hv⟩ 0), pr (bv ⟨v, hv⟩ 1)) ∈ D := (hDmem _).mpr ⟨⟨v, hv⟩, rfl⟩
      have h0 := (hDi _).mp hmem
      rw [zero_smul]
      exact hpr0 _ (hL ⟨v, hv⟩ 0) h0
    exact (c47_line_one hP hn hF α (hnatG 1 0 0 h01.symm) hMKmax hVW hVZ).1

end CFSG.Quasithin.C41Pf
