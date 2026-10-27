module

public import CFSG.Quasithin.H13.A5S1327zl
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A5S1327zc
public import CFSG.Quasithin.H13.A5S1328Sym1

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

theorem fix_pa_eq : ∀ x : W5, pact pa x = x → ∃ u : W5, x = u * pact pa u := by
  decide +kernel

theorem fixed_pa_pb : ∀ x : W5, pact pa x = x → pact pb x = x → x = 1 ∨ x = W4 := by
  decide +kernel

theorem W4_eq : pact pa (Multiplicative.ofAdd (e2 0 1)) = Multiplicative.ofAdd (e2 0 1) ∧
    W4 = Multiplicative.ofAdd (e2 0 1) * pact pb (Multiplicative.ofAdd (e2 0 1)) := by
  decide +kernel

theorem fix_pa_pb_eq (x : W5) (ha : pact pa x = x) (hb : pact pb x = x) :
    ∃ y : W5, pact pa y = y ∧ x = y * pact pb y := by
  rcases fixed_pa_pb x ha hb with rfl | rfl
  · exact ⟨1, map_one _, by rw [map_one, one_mul]⟩
  · exact ⟨_, W4_eq.1, W4_eq.2⟩

theorem K4_facts : pa * pa = 1 ∧ pb * pb = 1 ∧ pb * pa * pb⁻¹ * pa⁻¹ = 1 := by
  decide

theorem isElemAbelian_zpowers_of_mul_self {G : Type} [Group G] {x : G} (hx : x * x = 1) :
    IsElemAbelian 2 (Subgroup.zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hx2 : x ^ 2 = 1 := by rw [pow_two, hx]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]

theorem mem_v0list_cases : ∀ σ ∈ E1.LiftS5.v0list, σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pa * pb := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem rho_V {v : G} (hv : v ∈ V) : S.frame.ρ ⟨v, Subgroup.le_normalizer hv⟩ = 1 := by
  refine S.frame.rho_eq_one_of_mem _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact B2F.isElemAbelian_comm S.elemAbelian_V hw hv

theorem eq_mul_conj_of_psi (g : ↥(Subgroup.normalizer (V : Set G))) {v : G} (hv : v ∈ V)
    {u₀ : W5} (h : S.frame.ψ ⟨v, hv⟩ = u₀ * pact (S.frame.ρ g) u₀) :
    v = (S.frame.ψ.symm u₀ : G) * ((g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹) := by
  have hmem : (g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp g.2 _).mp (S.frame.ψ.symm u₀).2
  have h2 : S.frame.ψ ⟨(g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹, hmem⟩ =
      pact (S.frame.ρ g) u₀ := by
    rw [S.psi_conj, MulEquiv.apply_symm_apply]
  have h3 : S.frame.ψ (S.frame.ψ.symm u₀ *
      ⟨(g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹, hmem⟩) = S.frame.ψ ⟨v, hv⟩ := by
    rw [map_mul, h2, MulEquiv.apply_symm_apply, h]
  exact (congrArg Subtype.val (S.frame.ψ.injective h3)).symm

theorem exists_K4_lift (hTV : T ⊓ Subgroup.centralizer (V : Set G) ≤ V) :
    ∃ (a b : G) (ha : a ∈ Subgroup.normalizer (V : Set G))
      (hb : b ∈ Subgroup.normalizer (V : Set G)), a ∈ T ⊓ L ∧ b ∈ T ⊓ L ∧
      S.frame.ρ ⟨a, ha⟩ = pa ∧ S.frame.ρ ⟨b, hb⟩ = pb ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a := by
  classical
  set N := Subgroup.normalizer (V : Set G) with hNdef
  have hVN : V ≤ N := Subgroup.le_normalizer
  have hVTL : V ≤ T ⊓ L := le_inf S.V_le_T S.V_le_L
  have hρmul : ∀ (x y : G) (hx : x ∈ N) (hy : y ∈ N),
      S.frame.ρ ⟨x * y, N.mul_mem hx hy⟩ = S.frame.ρ ⟨x, hx⟩ * S.frame.ρ ⟨y, hy⟩ := by
    intro x y hx hy
    rw [← map_mul]
    rfl
  have hρinv : ∀ (x : G) (hx : x ∈ N),
      S.frame.ρ ⟨x⁻¹, N.inv_mem hx⟩ = (S.frame.ρ ⟨x, hx⟩)⁻¹ := by
    intro x hx
    rw [← map_inv]
    rfl
  have hker : ∀ (g : G) (hg : g ∈ N), g ∈ T → S.frame.ρ ⟨g, hg⟩ = 1 → g ∈ V :=
    fun g hg hgT h1 => hTV ⟨hgT, S.frame.mem_centralizer_of_rho ⟨g, hg⟩ h1⟩
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := S.elemAbelian_V.2 v hv
    rwa [pow_two] at this
  obtain ⟨hpa2, hpb2, hpab⟩ := K4_facts
  obtain ⟨⟨a₀, ha₀N⟩, ha₀TL, ha₀⟩ := S.K4_TL pa (Or.inr (Or.inl rfl))
  simp only at ha₀TL
  have hs : a₀ * a₀ ∈ V :=
    hker _ (N.mul_mem ha₀N ha₀N) (T.mul_mem ha₀TL.1 ha₀TL.1)
      (by rw [hρmul a₀ a₀ ha₀N ha₀N, ha₀, hpa2])
  have hsfix : pact (S.frame.ρ ⟨a₀, ha₀N⟩) (S.frame.ψ ⟨a₀ * a₀, hs⟩) =
      S.frame.ψ ⟨a₀ * a₀, hs⟩ := by
    refine (S.conj_eq_iff ⟨a₀, ha₀N⟩ ⟨a₀ * a₀, hs⟩).1 ?_
    show a₀ * (a₀ * a₀) * a₀⁻¹ = a₀ * a₀
    group
  rw [ha₀] at hsfix
  obtain ⟨u₀, hu₀⟩ := fix_pa_eq _ hsfix
  rw [← ha₀] at hu₀
  have hs' := S.eq_mul_conj_of_psi ⟨a₀, ha₀N⟩ hs hu₀
  obtain ⟨u, hu⟩ : ∃ u : G, u = (S.frame.ψ.symm u₀ : G) := ⟨_, rfl⟩
  rw [← hu] at hs'
  have huV : u ∈ V := hu ▸ (S.frame.ψ.symm u₀).2
  obtain ⟨a, ha_def⟩ : ∃ a : G, a = u * a₀ := ⟨_, rfl⟩
  have haN : a ∈ N := ha_def ▸ N.mul_mem (hVN huV) ha₀N
  have haTL : a ∈ T ⊓ L := ha_def ▸ (T ⊓ L).mul_mem (hVTL huV) ha₀TL
  have haρ : S.frame.ρ ⟨a, haN⟩ = pa := by
    subst ha_def
    rw [hρmul u a₀ (hVN huV) ha₀N, S.rho_V huV, one_mul, ha₀]
  have ha2 : a * a = 1 := by
    calc a * a = (u * (a₀ * u * a₀⁻¹)) * (a₀ * a₀) := by rw [ha_def]; group
      _ = (a₀ * a₀) * (a₀ * a₀) := by rw [← hs']
      _ = 1 := hsq _ hs
  obtain ⟨⟨b₀, hb₀N⟩, hb₀TL, hb₀⟩ := S.K4_TL pb (Or.inr (Or.inr (Or.inl rfl)))
  simp only at hb₀TL
  obtain ⟨w, hw_def⟩ : ∃ w : G, w = b₀ * a * b₀⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hwN : w ∈ N := hw_def ▸
    N.mul_mem (N.mul_mem (N.mul_mem hb₀N haN) (N.inv_mem hb₀N)) (N.inv_mem haN)
  have hwT : w ∈ T := hw_def ▸ T.mul_mem (T.mul_mem (T.mul_mem hb₀TL.1 haTL.1)
    (T.inv_mem hb₀TL.1)) (T.inv_mem haTL.1)
  have hwV : w ∈ V := by
    refine hker w hwN hwT ?_
    subst hw_def
    rw [hρmul _ _ (N.mul_mem (N.mul_mem hb₀N haN) (N.inv_mem hb₀N)) (N.inv_mem haN),
      hρmul _ _ (N.mul_mem hb₀N haN) (N.inv_mem hb₀N), hρmul _ _ hb₀N haN, hρinv _ hb₀N,
      hρinv _ haN, hb₀, haρ, hpab]
  have hwa : a * w * a⁻¹ = w := by
    have h1 : (w * a) * (w * a) = 1 := by
      calc (w * a) * (w * a) = b₀ * (a * a) * b₀⁻¹ := by rw [hw_def]; group
        _ = 1 := by rw [ha2]; group
    have h2 : a * w * a⁻¹ = w⁻¹ := by
      calc a * w * a⁻¹ = w⁻¹ * ((w * a) * (w * a)) * (a * a)⁻¹ := by group
        _ = w⁻¹ := by rw [h1, ha2]; group
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (hsq w hwV)
  have hwfix : pact (S.frame.ρ ⟨a, haN⟩) (S.frame.ψ ⟨w, hwV⟩) = S.frame.ψ ⟨w, hwV⟩ :=
    (S.conj_eq_iff ⟨a, haN⟩ ⟨w, hwV⟩).1 hwa
  rw [haρ] at hwfix
  obtain ⟨y₀, hy₀⟩ := fix_pa_eq _ hwfix
  rw [← haρ] at hy₀
  have hw' := S.eq_mul_conj_of_psi ⟨a, haN⟩ hwV hy₀
  obtain ⟨y, hy⟩ : ∃ y : G, y = (S.frame.ψ.symm y₀ : G) := ⟨_, rfl⟩
  rw [← hy] at hw'
  have hyV : y ∈ V := hy ▸ (S.frame.ψ.symm y₀).2
  obtain ⟨b₁, hb₁_def⟩ : ∃ b₁ : G, b₁ = y * b₀ := ⟨_, rfl⟩
  have hb₁N : b₁ ∈ N := hb₁_def ▸ N.mul_mem (hVN hyV) hb₀N
  have hb₁TL : b₁ ∈ T ⊓ L := hb₁_def ▸ (T ⊓ L).mul_mem (hVTL hyV) hb₀TL
  have hb₁ρ : S.frame.ρ ⟨b₁, hb₁N⟩ = pb := by
    subst hb₁_def
    rw [hρmul y b₀ (hVN hyV) hb₀N, S.rho_V hyV, one_mul, hb₀]
  have hb₁a : b₁ * a = a * b₁ := by
    have hb₀a : b₀ * a = w * a * b₀ := by rw [hw_def]; group
    calc b₁ * a = y * (b₀ * a) := by rw [hb₁_def]; group
      _ = y * (y * (a * y * a⁻¹)) * a * b₀ := by rw [hb₀a, hw']; group
      _ = (y * y) * (a * y * a⁻¹) * a * b₀ := by group
      _ = a * b₁ := by rw [hsq y hyV, hb₁_def]; group
  obtain ⟨t, ht_def⟩ : ∃ t : G, t = b₁ * b₁ := ⟨_, rfl⟩
  have htV : t ∈ V := by
    refine hker t (ht_def ▸ N.mul_mem hb₁N hb₁N) (ht_def ▸ T.mul_mem hb₁TL.1 hb₁TL.1) ?_
    subst ht_def
    rw [hρmul _ _ hb₁N hb₁N, hb₁ρ, hpb2]
  have hconj : a * b₁ * a⁻¹ = b₁ := by rw [← hb₁a]; group
  have hta : a * t * a⁻¹ = t := by
    calc a * t * a⁻¹ = (a * b₁ * a⁻¹) * (a * b₁ * a⁻¹) := by rw [ht_def]; group
      _ = t := by rw [hconj, ht_def]
  have htb : b₁ * t * b₁⁻¹ = t := by rw [ht_def]; group
  have htfa : pact pa (S.frame.ψ ⟨t, htV⟩) = S.frame.ψ ⟨t, htV⟩ := by
    rw [← haρ]
    exact (S.conj_eq_iff ⟨a, haN⟩ ⟨t, htV⟩).1 hta
  have htfb : pact pb (S.frame.ψ ⟨t, htV⟩) = S.frame.ψ ⟨t, htV⟩ := by
    rw [← hb₁ρ]
    exact (S.conj_eq_iff ⟨b₁, hb₁N⟩ ⟨t, htV⟩).1 htb
  obtain ⟨x₀, hx₀a, hx₀⟩ := fix_pa_pb_eq _ htfa htfb
  rw [← hb₁ρ] at hx₀
  have ht' := S.eq_mul_conj_of_psi ⟨b₁, hb₁N⟩ htV hx₀
  obtain ⟨x, hx⟩ : ∃ x : G, x = (S.frame.ψ.symm x₀ : G) := ⟨_, rfl⟩
  rw [← hx] at ht'
  have hxV : x ∈ V := hx ▸ (S.frame.ψ.symm x₀).2
  have hxa : a * x = x * a := by
    have h1 : a * x * a⁻¹ = x := by
      refine (S.conj_eq_iff ⟨a, haN⟩ ⟨x, hxV⟩).2 ?_
      have e : (⟨x, hxV⟩ : ↥V) = S.frame.ψ.symm x₀ := Subtype.ext hx
      rw [e, MulEquiv.apply_symm_apply, haρ]
      exact hx₀a
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  obtain ⟨b, hb_def⟩ : ∃ b : G, b = x * b₁ := ⟨_, rfl⟩
  have hbN : b ∈ N := hb_def ▸ N.mul_mem (hVN hxV) hb₁N
  have hbTL : b ∈ T ⊓ L := hb_def ▸ (T ⊓ L).mul_mem (hVTL hxV) hb₁TL
  have hbρ : S.frame.ρ ⟨b, hbN⟩ = pb := by
    subst hb_def
    rw [hρmul x b₁ (hVN hxV) hb₁N, S.rho_V hxV, one_mul, hb₁ρ]
  have hb2 : b * b = 1 := by
    calc b * b = (x * (b₁ * x * b₁⁻¹)) * (b₁ * b₁) := by rw [hb_def]; group
      _ = t * t := by rw [← ht', ← ht_def]
      _ = 1 := hsq t htV
  have hab : a * b = b * a := by
    calc a * b = (a * x) * b₁ := by rw [hb_def]; group
      _ = x * (b₁ * a) := by rw [hxa, hb₁a]; group
      _ = b * a := by rw [hb_def]; group
  exact ⟨a, b, haN, hbN, haTL, hbTL, haρ, hbρ, ha2, hb2, hab⟩

theorem rootFourLiftQuot_of (hTV : T ⊓ Subgroup.centralizer (V : Set G) ≤ V) :
    E1.LiftS5.RootFourLiftQuot T L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, haN, hbN, haTL, hbTL, haρ, hbρ, ha2, hb2, hab⟩ := S.exists_K4_lift hTV
  set A := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hA
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hab m n).eq
  have hAT : A ≤ T := sup_le (Subgroup.zpowers_le.mpr haTL.1) (Subgroup.zpowers_le.mpr hbTL.1)
  have hAL : A ≤ L := sup_le (Subgroup.zpowers_le.mpr haTL.2) (Subgroup.zpowers_le.mpr hbTL.2)
  have hAel : IsElemAbelian 2 A := isElemAbelian_sup_of_commute
    (isElemAbelian_zpowers_of_mul_self ha2) (isElemAbelian_zpowers_of_mul_self hb2) hcomm
  refine ⟨A, hAT, hAL, hAel, ?_⟩
  set φ : ↥L →* Equiv.Perm (Fin 5) := S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le) with hφ
  have hN : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    have hl' : l ∈ CFSG.Open.pCore 2 ↥L := by
      exact hl
    have hlP : (l : G) ∈ pCoreOf 2 L := ⟨l, hl', rfl⟩
    have hlP' : (l : G) ∈ pCoreOf 2 (L ⊔ T) := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) ?_
        (pCoreOf_isPGroup 2 L) hlP
      exact sup_le (le_normalizer_pCoreOf 2 L)
        (S.T_le_NL.trans (normalizer_le_normalizer_pCoreOf 2 L))
    rw [← S.cLT] at hlP'
    exact S.frame.rho_eq_one_of_mem _ hlP'.2
  have hdvd := E1.LiftS5.card_map_dvd_card_map_mk φ (CFSG.pCore 2 ↥L) hN (A.subgroupOf L)
  have hV0 : E1.LiftS5.V0 ≤ (A.subgroupOf L).map φ := by
    intro σ hσ
    have haA : a ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    have hbA : b ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rcases mem_v0list_cases σ (E1.LiftS5.mem_V0.mp hσ) with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨⟨a, haTL.2⟩, haA, haρ⟩
    · exact ⟨⟨b, hbTL.2⟩, hbA, hbρ⟩
    · refine ⟨⟨a * b, L.mul_mem haTL.2 hbTL.2⟩, A.mul_mem haA hbA, ?_⟩
      rw [← haρ, ← hbρ, ← map_mul]
      try rfl
  have h4le : 4 ≤ Nat.card ↥((A.subgroupOf L).map φ) := by
    rw [← E1.LiftS5.card_V0]
    exact Subgroup.card_le_of_le hV0
  have hA4 : Nat.card ↥A ≤ 4 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    have hza : Nat.card ↥(Subgroup.zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one two_pos (by rw [pow_two]; exact ha2)
    have hzb : Nat.card ↥(Subgroup.zpowers b) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one two_pos (by rw [pow_two]; exact hb2)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) := Nat.card_pos
    calc Nat.card ↥A ≤ Nat.card ↥A * Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card ↥(Subgroup.zpowers a) * Nat.card ↥(Subgroup.zpowers b) := h
      _ ≤ 2 * 2 := Nat.mul_le_mul hza hzb
  have hle : Nat.card ↥((A.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ≤ 4 := by
    refine (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact hA4
  have := Nat.le_of_dvd Nat.card_pos hdvd
  omega

theorem exists_setting_cComp (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) {H K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) : ∃ VH : Subgroup G, Nonempty (Setting G T K VH) := by
  have hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    rw [hHK]
    refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, cComp_subset_lFamily hH.1.1 hKc,
      (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2, by rw [← hHK]; exact hH.1.2⟩
  have hKf : quasithinIsFaithfulLocal T K :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hKloc hZK
  exact exists_setting h132two h132fsu h132A5 (QTH13.of_faithful S.h13 S.a5 hKf)
    (S.h13.a5 S.a5 K hKf)

end Setting

end CFSG.Quasithin.H13.A5
