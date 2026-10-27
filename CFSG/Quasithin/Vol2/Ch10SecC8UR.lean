module

public import CFSG.Quasithin.Vol2.Ch10SecCL3P
public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10SecC8Mod
public import CFSG.Quasithin.Vol2.Ch10SecCBasic
public import CFSG.Quasithin.Vol2.Ch10StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32 L3F
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isPa_of_isU {γ : L3.Γ} (h : IsU γ) : IsPa γ := ⟨h.1, h.2.1⟩

theorem act_e0_of_isU {γ : L3.Γ} (h : IsU γ) : L3.act γ e0 = e0 :=
  (act_e0_iff γ).mpr (isPa_of_isU h)

omit [Finite G] in
theorem autOn_mono {X K W : Subgroup G} (h : X ≤ K) : autOn X W ≤ autOn K W :=
  CFSG.Quasithin.AutOn.autOn_mono h

theorem mem_pCoreOf_iff_of_equiv {M Γ' : Type*} [Group M] [Group Γ'] [Finite M]
    {H : Subgroup M} {P E : Subgroup Γ'} (e : ↥H ≃* ↥P)
    (hP : CFSG.pCore 2 ↥P = E.subgroupOf P) {a : M} :
    a ∈ pCoreOf 2 H ↔ ∃ h : a ∈ H, ((e ⟨a, h⟩ : ↥P) : Γ') ∈ E := by
  have h1 : CFSG.pCore 2 ↥H = (E.subgroupOf P).comap e.toMonoidHom := by
    rw [← hP, ← CFSG.pCore_map_iso 2 e]
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← e.injective hyx]
  unfold pCoreOf
  rw [h1]
  constructor
  · rintro ⟨⟨a, ha⟩, hx, rfl⟩
    exact ⟨ha, Subgroup.mem_subgroupOf.mp hx⟩
  · rintro ⟨ha, hE⟩
    exact ⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr hE, rfl⟩

section Component

variable {K : Subgroup G} [IsMulCommutative ↥(Vi T L I K)]
  (D : L3Data (autOn K (Vi T L I K)) ⊤
    ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K)))

omit [Finite G] in
theorem mem_fsuCVM_of_coord (hKN : K ≤ Subgroup.normalizer (fsuVM T L I : Set G)) {x : G}
    (hx : x ∈ Vi T L I K) (h0 : coordOf D ⟨x, hx⟩ = 0) : x ∈ fsuCVM T L I := by
  have h1 := (coordOf_eq_zero_iff D _).mp h0
  exact ⟨commutator_le_left_of_le_normalizer hKN hx, Subgroup.mem_subgroupOf.mp h1⟩

omit [Finite G] in
theorem coord_conj {k : G} (hk : k ∈ Subgroup.normalizer (Vi T L I K : Set G)) {γ : L3.Γ}
    (hγ : conjAct (Vi T L I K) ⟨k, hk⟩ = (D.π γ : MulAut ↥(Vi T L I K)))
    {w : G} (hw : w ∈ Vi T L I K) (hw' : k * w * k⁻¹ ∈ Vi T L I K) :
    coordOf D ⟨k * w * k⁻¹, hw'⟩ = L3.act γ (coordOf D ⟨w, hw⟩) := by
  rw [← coordOf_π, ← hγ]
  rfl

omit [Finite G] in
theorem mem_U_iff (hKN : K ≤ Subgroup.normalizer (fsuVM T L I : Set G))
    (hD : ∀ γ, ((D.π γ : ↥(autOn K (Vi T L I K))) : MulAut ↥(Vi T L I K)) ∈
      autOn (T ⊓ K) (Vi T L I K) ↔ γ ∈ U3)
    (hTK : T ⊓ K ≤ T1 T L)
    (hact : ∀ s ∈ T1 T L, ∃ d ∈ T ⊓ K, ∀ w ∈ Vi T L I K, s * w * s⁻¹ = d * w * d⁻¹)
    {U : Subgroup G} (hU : IsU10_2_8 T L I K U) {v : G} (hv : v ∈ Vi T L I K) :
    v ∈ U ↔ (⟨v, hv⟩ : ↥(Vi T L I K)) ∈ secSub D e0 := by
  rw [hU.2 v hv]
  have hWN : ∀ k ∈ K, k ∈ Subgroup.normalizer (Vi T L I K : Set G) := fun k hk =>
    SecA.le_normalizer_commutator hKN Subgroup.le_normalizer hk
  constructor
  · intro h
    refine fix_U3 _ fun γ hγ => ?_
    obtain ⟨⟨d, hdN⟩, hdTK, hdγ⟩ := SecB.mem_autOn_iff.mp ((hD γ).mpr hγ)
    have hdv : d * v * d⁻¹ ∈ Vi T L I K := (Subgroup.mem_normalizer_iff.mp hdN v).mp hv
    have h1 := h d (hTK hdTK)
    have h2 : coordOf D ⟨d * v * d⁻¹, hdv⟩ = coordOf D ⟨v, hv⟩ := by
      have hm : d * v * d⁻¹ * v⁻¹ ∈ Vi T L I K := Subgroup.mul_mem _ hdv (Subgroup.inv_mem _ hv)
      have h0 : coordOf D ⟨_, hm⟩ = 0 :=
        (coordOf_eq_zero_iff D _).mpr (Subgroup.mem_subgroupOf.mpr h1.2)
      have e : (⟨d * v * d⁻¹ * v⁻¹, hm⟩ : ↥(Vi T L I K)) = ⟨_, hdv⟩ * (⟨v, hv⟩)⁻¹ := rfl
      rw [e, coordOf_mul, coordOf_inv] at h0
      exact eq_of_add_neg_eq_zero h0
    rw [← coord_conj D hdN hdγ hv hdv]
    exact h2
  · intro h s hs
    obtain ⟨d, hdTK, hds⟩ := hact s hs
    have hdN := hWN d hdTK.2
    obtain ⟨γ, hγ⟩ := D.π_surj ⟨conjAct (Vi T L I K) ⟨d, hdN⟩,
      SecB.mem_autOn_iff.mpr ⟨⟨d, hdN⟩, hdTK.2, rfl⟩⟩
    have hγU : γ ∈ U3 := by
      rw [← hD, hγ]
      exact SecB.mem_autOn_iff.mpr ⟨⟨d, hdN⟩, hdTK, rfl⟩
    have hdv : d * v * d⁻¹ ∈ Vi T L I K := (Subgroup.mem_normalizer_iff.mp hdN v).mp hv
    have h2 : coordOf D ⟨d * v * d⁻¹, hdv⟩ = coordOf D ⟨v, hv⟩ := by
      rw [coord_conj D hdN (congrArg Subtype.val hγ).symm hv hdv]
      rcases h with h | h <;> rw [h]
      · exact L3.act_zero γ
      · exact act_e0_of_isU hγU
    rw [hds v hv]
    have hm : d * v * d⁻¹ * v⁻¹ ∈ Vi T L I K := Subgroup.mul_mem _ hdv (Subgroup.inv_mem _ hv)
    refine mem_fsuCVM_of_coord D hKN hm ?_
    have e : (⟨d * v * d⁻¹ * v⁻¹, hm⟩ : ↥(Vi T L I K)) = ⟨_, hdv⟩ * (⟨v, hv⟩)⁻¹ := rfl
    rw [e, coordOf_mul, coordOf_inv, h2]
    exact add_neg_cancel _

omit [Finite G] in
theorem mem_centralizerSection_iff (hKN : K ≤ Subgroup.normalizer (fsuVM T L I : Set G))
    (hKL0 : K ≤ fsuL0 T L)
    (hD : ∀ γ, ((D.π γ : ↥(autOn K (Vi T L I K))) : MulAut ↥(Vi T L I K)) ∈
      autOn (T ⊓ K) (Vi T L I K) ↔ γ ∈ U3)
    (hTK : T ⊓ K ≤ T1 T L)
    (hact : ∀ s ∈ T1 T L, ∃ d ∈ T ⊓ K, ∀ w ∈ Vi T L I K, s * w * s⁻¹ = d * w * d⁻¹)
    {U : Subgroup G} (hU : IsU10_2_8 T L I K U) {k : G} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (Vi T L I K : Set G)) {γ : L3.Γ}
    (hγ : conjAct (Vi T L I K) ⟨k, hkN⟩ = (D.π γ : MulAut ↥(Vi T L I K))) :
    k ∈ centralizerSection K U (fsuCVM T L I) ↔ IsPa γ := by
  have hUW : U ≤ Vi T L I K := hU.1
  constructor
  · rintro ⟨-, -, -, h⟩
    obtain ⟨w, hw⟩ := coordOf_surj D e0
    have hwU : (w : G) ∈ U := (mem_U_iff D hKN hD hTK hact hU w.2).mpr (Or.inr hw)
    have h1 := h w hwU
    have hkw : k * w * k⁻¹ ∈ Vi T L I K := (Subgroup.mem_normalizer_iff.mp hkN w).mp w.2
    have hm : (w : G) * k * (w : G)⁻¹ * k⁻¹ ∈ Vi T L I K := by
      have e : (w : G) * k * (w : G)⁻¹ * k⁻¹ = w * (k * w * k⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ w.2 (Subgroup.inv_mem _ hkw)
    have h0 : coordOf D ⟨_, hm⟩ = 0 :=
      (coordOf_eq_zero_iff D _).mpr (Subgroup.mem_subgroupOf.mpr h1.2)
    have e : (⟨(w : G) * k * (w : G)⁻¹ * k⁻¹, hm⟩ : ↥(Vi T L I K)) =
        w * (⟨k * w * k⁻¹, hkw⟩ : ↥(Vi T L I K))⁻¹ := Subtype.ext (by
      change (w : G) * k * (w : G)⁻¹ * k⁻¹ = w * (k * w * k⁻¹)⁻¹
      group)
    rw [e, coordOf_mul, coordOf_inv] at h0
    have h2 := eq_of_add_neg_eq_zero h0
    rw [coord_conj D hkN hγ w.2 hkw] at h2
    rw [← act_e0_iff, ← hw]
    exact h2.symm
  · intro hpa
    have hfix : L3.act γ e0 = e0 := (act_e0_iff γ).mpr hpa
    have hc : ∀ w (hw : w ∈ Vi T L I K), ∃ hw' : k * w * k⁻¹ ∈ Vi T L I K,
        coordOf D ⟨k * w * k⁻¹, hw'⟩ = L3.act γ (coordOf D ⟨w, hw⟩) := fun w hw =>
      ⟨(Subgroup.mem_normalizer_iff.mp hkN w).mp hw,
        coord_conj D hkN hγ hw ((Subgroup.mem_normalizer_iff.mp hkN w).mp hw)⟩
    refine ⟨hk, ?_, ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨hx', hcx⟩ := hc x (hUW hx)
        rw [mem_U_iff D hKN hD hTK hact hU hx'] 
        rw [mem_U_iff D hKN hD hTK hact hU (hUW hx)] at hx
        rw [mem_secSub, hcx]
        rcases hx with h | h <;> rw [h]
        · left; exact L3.act_zero γ
        · right; exact hfix
      · intro hx
        have hxW : x ∈ Vi T L I K := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) _).mp (hUW hx)
          have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
          rwa [e] at this
        obtain ⟨hx', hcx⟩ := hc x hxW
        rw [mem_U_iff D hKN hD hTK hact hU hxW]
        rw [mem_U_iff D hKN hD hTK hact hU hx', mem_secSub, hcx] at hx
        rcases hx with h | h
        · left
          have h1 := congrArg (L3.act γ⁻¹) h
          rwa [L3.act_inv_act, L3.act_zero] at h1
        · right
          have h1 := congrArg (L3.act γ⁻¹) h
          rw [L3.act_inv_act] at h1
          rw [h1]
          have h2 := congrArg (L3.act γ⁻¹) hfix
          rw [L3.act_inv_act] at h2
          exact h2.symm
    · exact le_normalizer_inf' ((hKL0.trans (SecA.fsuL0_le_normalizer_fsuVM T L I)))
        (SecA.le_normalizer_centralizer (hKL0.trans Subgroup.le_normalizer)) hk
    · have hxW := hUW hx
      obtain ⟨hx', hcx⟩ := hc x hxW
      have hm : x * k * x⁻¹ * k⁻¹ ∈ Vi T L I K := by
        have e : x * k * x⁻¹ * k⁻¹ = x * (k * x * k⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ hxW (Subgroup.inv_mem _ hx')
      refine mem_fsuCVM_of_coord D hKN hm ?_
      have e : (⟨x * k * x⁻¹ * k⁻¹, hm⟩ : ↥(Vi T L I K)) =
          ⟨x, hxW⟩ * (⟨k * x * k⁻¹, hx'⟩ : ↥(Vi T L I K))⁻¹ := Subtype.ext (by
        change x * k * x⁻¹ * k⁻¹ = x * (k * x * k⁻¹)⁻¹
        group)
      rw [e, coordOf_mul, coordOf_inv, hcx]
      rw [mem_U_iff D hKN hD hTK hact hU hxW] at hx
      rcases hx with h | h <;> rw [h]
      · rw [L3.act_zero]
        exact add_neg_cancel _
      · rw [hfix]
        exact add_neg_cancel _

theorem mem_R_iff (hKN : K ≤ Subgroup.normalizer (fsuVM T L I : Set G))
    (hKL0 : K ≤ fsuL0 T L)
    (hD : ∀ γ, ((D.π γ : ↥(autOn K (Vi T L I K))) : MulAut ↥(Vi T L I K)) ∈
      autOn (T ⊓ K) (Vi T L I K) ↔ γ ∈ U3)
    (hTK : T ⊓ K ≤ T1 T L)
    (hact : ∀ s ∈ T1 T L, ∃ d ∈ T ⊓ K, ∀ w ∈ Vi T L I K, s * w * s⁻¹ = d * w * d⁻¹)
    {K' : Subgroup G} (hV : fsuVM T L I = Vi T L I K ⊔ Vi T L I K')
    (hW'K : Vi T L I K' ≤ Subgroup.centralizer (K : Set G))
    {U R : Subgroup G} (hU : IsU10_2_8 T L I K U) (hR : IsR10_2_8 T L I K U R)
    {x : G} (hxT : x ∈ T) :
    x ∈ R ↔ ∃ k ∈ K, (∀ v ∈ fsuVM T L I, x * v * x⁻¹ = k * v * k⁻¹) ∧
      ∃ γ, IsEa γ ∧ ∃ hkN : k ∈ Subgroup.normalizer (Vi T L I K : Set G),
        conjAct (Vi T L I K) ⟨k, hkN⟩ = (D.π γ : MulAut ↥(Vi T L I K)) := by
  have hXK : centralizerSection K U (fsuCVM T L I) ≤ K := centralizerSection_le_left _ _ _
  have hWN : K ≤ Subgroup.normalizer (Vi T L I K : Set G) := fun k hk =>
    SecA.le_normalizer_commutator hKN Subgroup.le_normalizer hk
  have hXV := hXK.trans hKN
  have hXW := hXK.trans hWN
  have hWV : Vi T L I K ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hKN
  have hC : ∀ l ∈ centralizerSection K U (fsuCVM T L I),
      l ∈ Subgroup.centralizer (fsuVM T L I : Set G) ↔
        l ∈ Subgroup.centralizer (Vi T L I K : Set G) := by
    intro l hl
    refine ⟨fun h => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWV) h, fun h => ?_⟩
    rw [hV]
    refine mem_centralizer_sup h (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hW'K hw) l (hXK hl)).symm
  obtain ⟨ψ, hψ⟩ := exists_autOnEquiv hXV hXW hC
  let πe : ↥(autOn K (Vi T L I K)) ≃* L3.Γ :=
    (MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).symm
  let ρ : ↥(autOn (centralizerSection K U (fsuCVM T L I)) (fsuVM T L I)) →* L3.Γ :=
    πe.toMonoidHom.comp ((Subgroup.inclusion (autOn_mono hXK)).comp ψ.toMonoidHom)
  have hρinj : Function.Injective ρ := πe.injective.comp
    ((Subgroup.inclusion_injective (autOn_mono hXK)).comp ψ.injective)
  have hρ : ∀ (m : G) (hm : m ∈ centralizerSection K U (fsuCVM T L I)) (γ : L3.Γ),
      ρ ⟨conjAct (fsuVM T L I) ⟨m, hXV hm⟩, SecB.mem_autOn_iff.mpr ⟨⟨m, hXV hm⟩, hm, rfl⟩⟩ = γ ↔
        conjAct (Vi T L I K) ⟨m, hXW hm⟩ = (D.π γ : MulAut ↥(Vi T L I K)) := by
    intro m hm γ
    change πe (Subgroup.inclusion (autOn_mono hXK) (ψ _)) = γ ↔ _
    rw [hψ m hm]
    constructor
    · intro h
      rw [← h]
      change _ = ((MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩)
        ((MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).symm _) : MulAut ↥(Vi T L I K))
      rw [MulEquiv.apply_symm_apply]
      rfl
    · intro h
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext h
  have hrange : ρ.range = Pa := by
    ext γ
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨⟨m, hmN⟩, hm, rfl⟩ := SecB.mem_autOn_iff.mp ha
      have h1 := (hρ m hm (ρ ⟨_, ha⟩)).mp rfl
      exact (mem_centralizerSection_iff D hKN hKL0 hD hTK hact hU (hXK hm) (hXW hm) h1).mp hm
    · intro hγ
      obtain ⟨⟨m, hmN⟩, hmK, hmγ⟩ := SecB.mem_autOn_iff.mp (D.π γ).2
      have hm : m ∈ centralizerSection K U (fsuCVM T L I) :=
        (mem_centralizerSection_iff D hKN hKL0 hD hTK hact hU hmK hmN hmγ).mpr hγ
      exact ⟨_, (hρ m hm γ).mpr hmγ⟩
  let e' : ↥(autOn (centralizerSection K U (fsuCVM T L I)) (fsuVM T L I)) ≃* ↥Pa :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hrange)
  have he' : ∀ a, ((e' a : ↥Pa) : L3.Γ) = ρ a := fun a => rfl
  rw [hR.2 x hxT]
  constructor
  · rintro ⟨hxN, hx⟩
    obtain ⟨ha, hE⟩ := (mem_pCoreOf_iff_of_equiv e' pCore_pa).mp hx
    obtain ⟨⟨m, hmN⟩, hm, hmx⟩ := SecB.mem_autOn_iff.mp ha
    refine ⟨m, hXK hm, fun v hv => ?_, ρ ⟨_, ha⟩, ?_, hXW hm, ?_⟩
    · have := congrArg (fun f : MulAut ↥(fsuVM T L I) => ((f ⟨v, hv⟩ : ↥(fsuVM T L I)) : G)) hmx
      exact this.symm
    · rw [← he']
      exact hE
    · have hsub : (⟨conjAct (fsuVM T L I) ⟨x, hxN⟩, ha⟩ :
          ↥(autOn (centralizerSection K U (fsuCVM T L I)) (fsuVM T L I))) =
          ⟨conjAct (fsuVM T L I) ⟨m, hXV hm⟩, SecB.mem_autOn_iff.mpr ⟨⟨m, hXV hm⟩, hm, rfl⟩⟩ :=
        Subtype.ext hmx.symm
      rw [hsub]
      exact (hρ m hm _).mp rfl
  · rintro ⟨k, hk, hkx, γ, hγE, hkN, hkγ⟩
    have hxN : x ∈ Subgroup.normalizer (fsuVM T L I : Set G) := SecA.le_normalizer_fsuVM T L I hxT
    have hkX : k ∈ centralizerSection K U (fsuCVM T L I) :=
      (mem_centralizerSection_iff D hKN hKL0 hD hTK hact hU hk hkN hkγ).mpr hγE.1
    have hxk : conjAct (fsuVM T L I) ⟨x, hxN⟩ = conjAct (fsuVM T L I) ⟨k, hXV hkX⟩ := by
      ext v
      exact hkx v v.2
    have ha : conjAct (fsuVM T L I) ⟨x, hxN⟩ ∈
        autOn (centralizerSection K U (fsuCVM T L I)) (fsuVM T L I) := by
      rw [hxk]
      exact SecB.mem_autOn_iff.mpr ⟨⟨k, hXV hkX⟩, hkX, rfl⟩
    refine ⟨hxN, (mem_pCoreOf_iff_of_equiv e' pCore_pa).mpr ⟨ha, ?_⟩⟩
    have hsub : (⟨conjAct (fsuVM T L I) ⟨x, hxN⟩, ha⟩ :
        ↥(autOn (centralizerSection K U (fsuCVM T L I)) (fsuVM T L I))) =
        ⟨conjAct (fsuVM T L I) ⟨k, hXV hkX⟩,
          SecB.mem_autOn_iff.mpr ⟨⟨k, hXV hkX⟩, hkX, rfl⟩⟩ := Subtype.ext hxk
    rw [he', hsub, (hρ k hkX γ).mpr hkγ]
    exact hγE

end Component

end CFSG.Quasithin.Vol2.Ch10.SecC
