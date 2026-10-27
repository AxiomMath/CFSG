module

public import CFSG.Quasithin.Vol2.Ch3xC58NSCentral
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 CFSG.Quasithin.C58
  Subgroup

variable {G : Type} [Group G]

structure BlockConfigNS (H T R K₁ : Subgroup G) : Prop where
  short : IsShort2 K₁
  typ : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 5
  le_H : K₁ ≤ H
  comm_J : ⁅K₁, thompsonJ R⁆ = K₁
  U_le_R : blockU K₁ ≤ R
  syl : IsSylowTwoOf (T ⊓ K₁) K₁
  perm : ∀ g ∈ T, conjSubgroup K₁ g = K₁ ∨ ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ g, a * b = b * a
  index : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≤ 2
  gen : oTwoUpper H ≤ ⨆ (g : G) (_ : g ∈ T), conjSubgroup K₁ g
  QH : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ K₁, k * q * k⁻¹ * q⁻¹ ∈ blockU K₁
  CH : T ⊓ centralizer ((⨆ (g : G) (_ : g ∈ T), conjSubgroup (blockU K₁) g : Subgroup G) :
    Set G) ≤ pCoreOf 2 H

structure GammaSetupNS (H T R K₁ : Subgroup G) (t x : G) : Prop where
  cfg : BlockConfigNS H T R K₁
  charTwo : CharTwo H
  sylow : quasithinIsSylowTwo T
  even : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G
  RT : R ≤ T
  TH : T ≤ H
  tT : t ∈ T
  tK : t ∉ normalizer (K₁ : Set G)
  xN : x ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G)
  xU : ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G)

namespace GammaSetupNS

variable {H T R K₁ : Subgroup G} {t x : G} (hs : GammaSetupNS H T R K₁ t x)
include hs

theorem relIndex_T₁ [Finite G] : (T ⊓ normalizer (K₁ : Set G)).relIndex T = 2 := by
  have h1 : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≠ 1 := fun h =>
    hs.tK (((Subgroup.relIndex_eq_one.mp h).trans inf_le_right) hs.tT)
  have h0 : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≠ 0 :=
    Subgroup.index_ne_zero_of_finite (H := (T ⊓ normalizer (K₁ : Set G)).subgroupOf T)
  have := hs.cfg.index
  omega

theorem le_normalizer_T₁ [Finite G] :
    T ≤ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) := by
  have hn : ((T ⊓ normalizer (K₁ : Set G)).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two hs.relIndex_T₁
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

theorem sq_mem_T₁ [Finite G] {g : G} (hg : g ∈ T) : g * g ∈ T ⊓ normalizer (K₁ : Set G) :=
  Subgroup.mul_self_mem_of_index_two (H := (T ⊓ normalizer (K₁ : Set G)).subgroupOf T)
    hs.relIndex_T₁ ⟨g, hg⟩

omit hs in
theorem blockU_le (hK : IsShort2 K₁) : blockU K₁ ≤ K₁ :=
  (C1.blockU_le_blockQ hK).trans (C1.blockQ_le K₁)

theorem U_le_T₁ : blockU K₁ ≤ T ⊓ normalizer (K₁ : Set G) :=
  le_inf (hs.cfg.U_le_R.trans hs.RT) ((blockU_le hs.cfg.short).trans Subgroup.le_normalizer)

omit hs in
theorem T₁_le_normalizer_U : T ⊓ normalizer (K₁ : Set G) ≤ normalizer (blockU K₁ : Set G) :=
  fun _ hy => C1.mem_normalizer_blockU hy.2

theorem syl₁ : IsSylowTwoOf ((T ⊓ normalizer (K₁ : Set G)) ⊓ K₁) K₁ := by
  have e : (T ⊓ normalizer (K₁ : Set G)) ⊓ K₁ = T ⊓ K₁ :=
    le_antisymm (inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)) inf_le_right)
  rw [e]; exact hs.cfg.syl

theorem comm_K₂ : ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ t, a * b = b * a := by
  rcases hs.cfg.perm t hs.tT with h | h
  · exact absurd (conjSubgroup_eq_iff_mem_normalizer.mp h) hs.tK
  · exact h

theorem inf_K₂_le : K₁ ⊓ conjSubgroup K₁ t ≤ blockQ K₁ := by
  intro g hg
  refine hs.cfg.short.2.1 ⟨hg.1, ?_⟩
  refine Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (C1.blockQ_le K₁)) ?_
  exact mem_centralizer_iff.mpr fun a ha => hs.comm_K₂ a ha g hg.2

theorem le_sup_zpowers [Finite G] : T ≤ (T ⊓ normalizer (K₁ : Set G)) ⊔ zpowers t := by
  set X := (T ⊓ normalizer (K₁ : Set G)) ⊔ zpowers t with hX
  have hT₁X : T ⊓ normalizer (K₁ : Set G) ≤ X := le_sup_left
  have hXT : X ≤ T := sup_le inf_le_left (zpowers_le.mpr hs.tT)
  have hmul := Subgroup.relIndex_mul_relIndex _ X T hT₁X hXT
  rw [hs.relIndex_T₁] at hmul
  have h1 : (T ⊓ normalizer (K₁ : Set G)).relIndex X ≠ 1 := fun h =>
    hs.tK ((Subgroup.relIndex_eq_one.mp h (mem_sup_right (mem_zpowers t))).2)
  have h2 : X.relIndex T = 1 := by
    have hd : (T ⊓ normalizer (K₁ : Set G)).relIndex X ∣ 2 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd h h1
    · rw [h] at hmul; omega
  exact Subgroup.relIndex_eq_one.mp h2

theorem exists_central [Finite G] :
    ∃ e ∈ blockU K₁, e ∉ blockZ K₁ ∧ ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e = e * y :=
  exists_central_of_block hs.cfg.short hs.cfg.typ (hs.sylow.1.to_le inf_le_left) inf_le_right
    hs.syl₁ hs.U_le_T₁

theorem z_mem [Finite G] {e : G} (heU : e ∈ blockU K₁) (heZ : e ∉ blockZ K₁)
    (heT₁ : ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e = e * y) :
    e * (t⁻¹ * e * t) ∈ quasithinOmegaOneCenter T ∧ e * (t⁻¹ * e * t) ≠ 1 := by
  have hUK := blockU_le hs.cfg.short
  set e₂ := t⁻¹ * e * t with he₂
  have he₂K : e₂ ∈ conjSubgroup K₁ t := by
    rw [mem_conjSubgroup_iff]
    have : t * e₂ * t⁻¹ = e := by rw [he₂]; group
    rw [this]; exact hUK heU
  have hee₂ : e * e₂ = e₂ * e := hs.comm_K₂ e (hUK heU) e₂ he₂K
  have he2 : e ^ 2 = 1 := C1.blockU_sq hs.cfg.short e heU
  have hTN := hs.le_normalizer_T₁
  have hzT : e * e₂ ∈ T := mul_mem (hs.U_le_T₁ heU).1
    (by rw [he₂]; exact mul_mem (mul_mem (inv_mem hs.tT) (hs.U_le_T₁ heU).1) hs.tT)
  have he₂T₁ : ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e₂ = e₂ * y := by
    intro y hy
    have hty : t * y * t⁻¹ ∈ T ⊓ normalizer (K₁ : Set G) :=
      (mem_normalizer_iff.mp (hTN hs.tT) y).mp hy
    have h1 := heT₁ _ hty
    calc y * e₂ = t⁻¹ * ((t * y * t⁻¹) * e) * t := by rw [he₂]; group
      _ = t⁻¹ * (e * (t * y * t⁻¹)) * t := by rw [h1]
      _ = e₂ * y := by rw [he₂]; group
  have htt : t * t ∈ T ⊓ normalizer (K₁ : Set G) := hs.sq_mem_T₁ hs.tT
  have hte : t * e * t⁻¹ = e₂ := by
    have h1 := heT₁ _ htt
    calc t * e * t⁻¹ = t⁻¹ * ((t * t) * e) * t⁻¹ * t⁻¹ * t := by group
      _ = t⁻¹ * (e * (t * t)) * t⁻¹ * t⁻¹ * t := by rw [h1]
      _ = e₂ := by rw [he₂]; group
  have hzc : T ≤ centralizer ({e * e₂} : Set G) := by
    refine hs.le_sup_zpowers.trans (sup_le ?_ (zpowers_le.mpr ?_))
    · intro y hy
      rw [mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      calc e * e₂ * y = e * (e₂ * y) := by group
        _ = e * (y * e₂) := by rw [he₂T₁ y hy]
        _ = (e * y) * e₂ := by group
        _ = (y * e) * e₂ := by rw [heT₁ y hy]
        _ = y * (e * e₂) := by group
    · rw [mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have h1 : t * (e * e₂) * t⁻¹ = e * e₂ := by
        have h2 : t * e₂ * t⁻¹ = e := by rw [he₂]; group
        calc t * (e * e₂) * t⁻¹ = (t * e * t⁻¹) * (t * e₂ * t⁻¹) := by group
          _ = e₂ * e := by rw [hte, h2]
          _ = e * e₂ := hee₂.symm
      calc e * e₂ * t = t * (e * e₂) * t⁻¹ * t := by rw [h1]
        _ = t * (e * e₂) := by group
  have he₂2 : e₂ ^ 2 = 1 := by
    rw [he₂]
    have : (t⁻¹ * e * t) ^ 2 = t⁻¹ * e ^ 2 * t := by simp [pow_two]; group
    rw [this, he2]; group
  have hz2 : (e * e₂) ^ 2 = 1 := by
    have : (e * e₂) ^ 2 = e ^ 2 * e₂ ^ 2 := by
      simp only [pow_two]
      calc e * e₂ * (e * e₂) = e * (e₂ * e) * e₂ := by group
        _ = e * (e * e₂) * e₂ := by rw [hee₂]
        _ = e * e * (e₂ * e₂) := by group
    rw [this, he2, he₂2, one_mul]
  refine ⟨mem_quasithinOmegaOneCenter_iff.mpr ⟨hzT, ?_, hz2⟩, ?_⟩
  · rw [mem_centralizer_iff]
    intro g hg
    exact ((mem_centralizer_iff.mp (hzc hg)) (e * e₂) rfl).symm
  · intro h1
    have h2 : e = e₂⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : e ∈ conjSubgroup K₁ t := by rw [h2]; exact (conjSubgroup K₁ t).inv_mem he₂K
    exact heZ ⟨heU, mem_centralizer_iff.mpr fun a ha => hs.comm_K₂ a ha e h3⟩

theorem no_common_normal [Finite G] {R₀ : Subgroup G}
    (hR₀ : R₀ ≤ T ⊓ normalizer (K₁ : Set G)) (hne : R₀ ≠ ⊥)
    (hY : normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) ≤
      normalizer (R₀ : Set G))
    (hK : K₁ ≤ normalizer (R₀ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUK := blockU_le hs.cfg.short
  set U₁ := blockU K₁ with hU₁
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set H₀ := normalizer (R₀ : Set G) with hH₀
  have hT2 : IsPGroup 2 T := hs.sylow.1
  set Tsyl : Sylow 2 G := hT2.toSylow hs.sylow.2 with hTsyl
  have hTH₀ : (Tsyl : Subgroup G) ≤ H₀ := hs.le_normalizer_T₁.trans hY
  have hloc : IsTwoLocal H₀ := ⟨R₀, hne, hT2.to_le (hR₀.trans inf_le_left), rfl⟩
  have hF : H₀ ⊓ centralizer (pCoreOf 2 H₀ : Set G) ≤ pCoreOf 2 H₀ :=
    hs.even H₀ hloc ⟨Tsyl, hTH₀⟩
  obtain ⟨-, hCab⟩ := conjClosure_le_centerOf_pCoreOf H₀ Tsyl hTH₀ hF
    (le_rfl : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter T)
  set C := conjClosure (quasithinOmegaOneCenter T) H₀ with hCdef
  have hCN : H₀ ≤ normalizer (C : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨e, heU, heZ, heT₁⟩ := hs.exists_central
  obtain ⟨hzZ, -⟩ := hs.z_mem heU heZ heT₁
  set e₂ := t⁻¹ * e * t with he₂
  have hzC : e * e₂ ∈ C := le_conjClosure _ _ hzZ
  have he₂K : e₂ ∈ conjSubgroup K₁ t := by
    rw [mem_conjSubgroup_iff]
    have : t * e₂ * t⁻¹ = e := by rw [he₂]; group
    rw [this]; exact hUK heU
  have hmem : ∀ k ∈ K₁, e * (k * e * k⁻¹)⁻¹ ∈ C := by
    intro k hk
    have hkC : k * (e * e₂) * k⁻¹ ∈ C := (mem_normalizer_iff.mp (hCN (hK hk)) _).mp hzC
    have hke₂ : k * e₂ = e₂ * k := hs.comm_K₂ k hk e₂ he₂K
    have e1 : (e * e₂) * (k * (e * e₂) * k⁻¹)⁻¹ = e * (k * e * k⁻¹)⁻¹ := by
      have hke₂' : k * e₂ * k⁻¹ = e₂ := by rw [hke₂]; group
      have : k * (e * e₂) * k⁻¹ = (k * e * k⁻¹) * e₂ := by
        calc k * (e * e₂) * k⁻¹ = (k * e * k⁻¹) * (k * e₂ * k⁻¹) := by group
          _ = (k * e * k⁻¹) * e₂ := by rw [hke₂']
      rw [this]; group
    rw [← e1]; exact mul_mem hzC (inv_mem hkC)
  have hUC : U₁ ≤ C := blockU_le_of_mem hs.cfg.short (hK.trans hCN) heU heZ hmem
  have hxH₀ : x ∈ H₀ := hY hs.xN
  have hUxC : conjSubgroup U₁ x ≤ C := by
    intro v hv
    rw [mem_conjSubgroup_iff] at hv
    have := (mem_normalizer_iff.mp (hCN (inv_mem hxH₀)) _).mp (hUC hv)
    simpa [mul_assoc] using this
  apply hs.xU
  intro v hv
  rw [mem_centralizer_iff]
  intro u hu
  exact (hCab.1.is_comm.comm ⟨u, hUC hu⟩ ⟨v, hUxC hv⟩) |> congrArg Subtype.val

end GammaSetupNS

end CFSG.Quasithin.C58NS
