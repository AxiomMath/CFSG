module

public import CFSG.Quasithin.Background.C58Core

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup

variable {G : Type} [Group G]

structure BlockConfig (H T R K₁ : Subgroup G) : Prop where
  short : IsShort2 K₁
  alt : IsAltType K₁ 3
  le_H : K₁ ≤ H
  comm_J : ⁅K₁, thompsonJ R⁆ = K₁
  U_le_R : blockU K₁ ≤ R
  perm : ∀ g ∈ T, conjSubgroup K₁ g = K₁ ∨ ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ g, a * b = b * a
  disj : ∀ g ∈ T, conjSubgroup K₁ g ≠ K₁ → K₁ ⊓ conjSubgroup K₁ g = ⊥
  index : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≤ 2
  gen : oTwoUpper H ≤ ⨆ (g : G) (_ : g ∈ T), conjSubgroup K₁ g
  QH : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ K₁, k * q * k⁻¹ * q⁻¹ ∈ blockU K₁
  CH : T ⊓ centralizer ((⨆ (g : G) (_ : g ∈ T), conjSubgroup (blockU K₁) g : Subgroup G) :
    Set G) ≤ pCoreOf 2 H

namespace BlockConfig

variable {H T R K₁ : Subgroup G} (hcfg : BlockConfig H T R K₁)
include hcfg

theorem isA4 [Finite G] : IsA4Block K₁ (blockU K₁) := IsA4Block.of_alt3 hcfg.short hcfg.alt

theorem baum_facts [Finite G] (hR2 : IsPGroup 2 R) (hRT : R ≤ T) :
    blockU K₁ ≤ baum R ∧ baum R ≤ normalizer (K₁ : Set G) ∧
      ¬ baum R ≤ centralizer (blockU K₁ : Set G) := by
  have hU := (C56.a3_blockU_le_baum hR2 hcfg.short hcfg.alt hcfg.U_le_R hcfg.comm_J).1
  have hN := C56.a3_baum_le_normalizer hR2 hcfg.short hcfg.alt hcfg.U_le_R hcfg.comm_J
    (fun s hs => hcfg.perm s (hRT (Subgroup.mem_inf.mp hs).1))
  refine ⟨hU, hN, fun hle => ?_⟩
  exact C56.a3_not_le_centralizer hcfg.short hcfg.alt hcfg.comm_J
    ((thompsonJ_le_baum' R).trans hle)

omit hcfg in
theorem conj_le_iSup {T U : Subgroup G} {g : G} (hg : g ∈ T) :
    conjSubgroup U g ≤ ⨆ (g : G) (_ : g ∈ T), conjSubgroup U g :=
  le_iSup₂_of_le g hg le_rfl

theorem exists_conj_not_le_centralizer [Finite G] {M₀ : Subgroup G} (hNC : NoCommonNormal R H M₀)
    (hTM₀ : T ≤ M₀) (hM₀R : M₀ ≤ normalizer (R : Set G)) (hRT : R ≤ T) (hTH : T ≤ H)
    (hH : H ≤ oTwoUpper H ⊔ T) (hT2 : IsPGroup 2 T) :
    ∃ x ∈ M₀, ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G) := by
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  obtain ⟨hUS, -, -⟩ := hcfg.baum_facts hR2 hRT
  set U₁ := blockU K₁ with hU₁
  set U₀ := conjClosure U₁ M₀ with hU₀
  have hM₀S : M₀ ≤ normalizer ((baum R : Subgroup G) : Set G) :=
    hM₀R.trans (normalizer_le_normalizer_baum R)
  have hSR : baum R ≤ R := inf_le_left
  have hU₀R : U₀ ≤ R := conjClosure_le fun m hm u hu =>
    (mem_normalizer_iff.mp (hM₀R hm) u).mp (hcfg.U_le_R hu)
  have hU₁ne : U₁ ≠ ⊥ := by
    intro h
    have := hcfg.isA4.card_U
    rw [← hU₁, h, Subgroup.card_bot] at this
    norm_num at this
  have hU₀ne : U₀ ≠ ⊥ := fun h => hU₁ne (le_bot_iff.mp (h ▸ le_conjClosure U₁ M₀))
  have hM₀U₀ : M₀ ≤ normalizer (U₀ : Set G) := le_normalizer_conjClosure U₁ M₀
  by_contra hall
  push Not at hall
  have hconj : ∀ x ∈ M₀, conjSubgroup U₁ x ≤ pCoreOf 2 H := by
    intro x hx
    have hxH : conjSubgroup U₁ x ≤ T := by
      have h1 := conjSubgroup_mono hUS x
      rw [conjSubgroup_eq_iff_mem_normalizer.mpr (hM₀S hx)] at h1
      exact h1.trans (hSR.trans hRT)
    have hxC : conjSubgroup U₁ x ≤
        centralizer ((⨆ (g : G) (_ : g ∈ T), conjSubgroup U₁ g : Subgroup G) : Set G) := by
      rw [le_centralizer_iff]
      refine iSup₂_le fun g hg => ?_
      rw [← le_centralizer_iff]
      have h1 := hall (x * g⁻¹) (mul_mem hx (inv_mem (hTM₀ hg)))
      rw [← conjSubgroup_conjSubgroup] at h1
      have h2 := (le_centralizer_iff_conj g).mp h1
      rwa [conjSubgroup_inv_conjSubgroup] at h2
    exact (le_inf hxH hxC).trans hcfg.CH
  have hU₀Q : U₀ ≤ pCoreOf 2 H := by
    refine conjClosure_le fun m hm u hu => ?_
    have := hconj m⁻¹ (inv_mem hm)
    exact this (mem_conjSubgroup_iff.mpr (by
      have e : m⁻¹ * (m * u * m⁻¹) * m⁻¹⁻¹ = u := by group
      rw [e]; exact hu))
  have hQn : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hKU₀ : ∀ g ∈ T, conjSubgroup K₁ g ≤ normalizer (U₀ : Set G) := by
    intro g hg
    have key : ∀ k ∈ conjSubgroup K₁ g, ∀ u ∈ U₀, k * u * k⁻¹ ∈ U₀ := by
      intro k hk u hu
      rw [mem_conjSubgroup_iff] at hk
      have hgu : g * u * g⁻¹ ∈ pCoreOf 2 H :=
        (mem_normalizer_iff.mp (hQn (hTH hg)) u).mp (hU₀Q hu)
      have hw := hcfg.QH _ hgu _ hk
      set w := g * k * g⁻¹ * (g * u * g⁻¹) * (g * k * g⁻¹)⁻¹ * (g * u * g⁻¹)⁻¹ with hw'
      have e : k * u * k⁻¹ = (g⁻¹ * w * g) * u := by rw [hw']; group
      rw [e]
      refine mul_mem ?_ hu
      have := mem_conjClosure (inv_mem (hTM₀ hg)) hw
      simpa using this
    intro k hk
    exact B6.mem_normalizer_of_forall_mem (fun u hu => key k hk u hu)
      (fun u hu => by simpa using key k⁻¹ (inv_mem hk) u hu)
  have hHU₀ : H ≤ normalizer (U₀ : Set G) := by
    refine hH.trans (sup_le ?_ (hTM₀.trans hM₀U₀))
    exact hcfg.gen.trans (iSup₂_le fun g hg => hKU₀ g hg)
  exact hNC U₀ hU₀R hU₀ne hHU₀ hM₀U₀

theorem exists_good_elt [Finite G] {M₀ : Subgroup G} (hNC : NoCommonNormal R H M₀)
    (hTM₀ : T ≤ M₀) (hM₀R : M₀ ≤ normalizer (R : Set G)) (hRT : R ≤ T) (hTH : T ≤ H)
    (hH : H ≤ oTwoUpper H ⊔ T) (hT : quasithinIsSylowTwo T) :
    ¬ T ≤ normalizer (K₁ : Set G) ∧ ∃ x ∈ M₀,
      x ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) ∧
      ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hT.1
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  obtain ⟨hUS, hSK, hSnt⟩ := hcfg.baum_facts hR2 hRT
  have hA := hcfg.isA4
  set U₁ := blockU K₁ with hU₁
  set S := baum R with hSdef
  have hS2 : IsPGroup 2 S := hR2.to_le inf_le_left
  have hM₀S : M₀ ≤ normalizer (S : Set G) := hM₀R.trans (normalizer_le_normalizer_baum R)
  obtain ⟨y, hyM₀, hyU⟩ := hcfg.exists_conj_not_le_centralizer hNC hTM₀ hM₀R hRT hTH hH hT2
  obtain ⟨W, hP⟩ := pairData_of_block hA hcfg.short hS2 hUS hSK hSnt (hM₀S hyM₀) hyU
  set Q := S ⊓ centralizer (U₁ : Set G) with hQ
  set D := Q ⊓ centralizer (K₁ : Set G) with hD
  set F := sqSub D with hF
  set M₁ := M₀ ⊓ normalizer (F : Set G) with hM₁
  set N' := M₁ ⊓ normalizer (Q : Set G) with hN'
  have hyM₁ : y ∈ M₁ := ⟨hyM₀, hP.mem_normalizer_sqSub⟩
  have hyQ : y ∉ normalizer (Q : Set G) := by
    intro hyQ
    apply hyU
    have h1 := conjSubgroup_mono hP.rank1.U_le_Q y
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr hyQ] at h1
    exact h1.trans inf_le_right
  have hor : ∀ m ∈ M₁, m ∈ normalizer (Q : Set G) ∨ m * y⁻¹ ∈ normalizer (Q : Set G) :=
    fun m hm => hP.mem_or_mem (hM₀S hm.1) hm.2
  have hyy : y * y ∈ normalizer (Q : Set G) := by
    rcases hor (y * y) (mul_mem hyM₁ hyM₁) with h | h
    · exact h
    · exfalso; apply hyQ; simpa using h
  have hidx : N'.relIndex M₁ = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyM₁⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, coe_mul, hN', mem_inf]
    have hbM₁ : (b : G) ∈ M₁ := b.2
    by_cases hb : (b : G) ∈ normalizer (Q : Set G)
    · refine Or.inr ⟨⟨hbM₁, hb⟩, ?_⟩
      rintro ⟨-, hby⟩
      apply hyQ
      have := mul_mem (inv_mem hb) hby
      simpa using this
    · refine Or.inl ⟨⟨mul_mem hbM₁ hyM₁, ?_⟩, fun h => hb h.2⟩
      have h1 := (hor b hbM₁).resolve_left hb
      have : (b : G) * y = (b * y⁻¹) * (y * y) := by group
      rw [this]; exact mul_mem h1 hyy
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  have hT₁S : T₁ ≤ normalizer (S : Set G) := inf_le_left.trans (hTM₀.trans hM₀S)
  have hT₁U : T₁ ≤ normalizer (U₁ : Set G) := inf_le_right.trans (IsA4Block.normalizer_le hA)
  have hT₁Q : T₁ ≤ normalizer (Q : Set G) := fun t ht =>
    mem_normalizer_inf (hT₁S ht) (mem_normalizer_centralizer (hT₁U ht))
  have hT₁D : T₁ ≤ normalizer (D : Set G) := fun t ht =>
    mem_normalizer_inf (hT₁Q ht) (mem_normalizer_centralizer ht.2)
  have hT₁F : T₁ ≤ normalizer (F : Set G) := fun t ht =>
    conjSubgroup_eq_iff_mem_normalizer.mp (conjSubgroup_sqSub_of_mem_normalizer (hT₁D ht))
  have hT₁N' : T₁ ≤ N' := fun t ht => ⟨⟨hTM₀ ht.1, hT₁F ht⟩, hT₁Q ht⟩
  have hT₁M₁ : T₁ ≤ M₁ := hT₁N'.trans inf_le_left
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  obtain ⟨T₀, hT₀, hT₁T₀⟩ := A4.exists_isSylowTwoOf_ge hT₁M₁ hT₁2
  have hT₀N' : ¬ T₀ ≤ N' := by
    intro hle
    apply hT₀.2.2
    show 2 ∣ T₀.relIndex M₁
    rw [← Subgroup.relIndex_mul_relIndex T₀ N' M₁ hle inf_le_left, hidx]
    exact dvd_mul_left 2 _
  obtain ⟨x, hxT₀, hxN'⟩ := IsConcreteLE.not_le_iff_exists.mp hT₀N'
  have hxM₁ : x ∈ M₁ := hT₀.1 hxT₀
  have hxQ : x ∉ normalizer (Q : Set G) := fun h => hxN' ⟨hxM₁, h⟩
  set Tsyl : Sylow 2 G := hT.1.toSylow hT.2 with hTsyldef
  have hTsyl : (Tsyl : Subgroup G) = T := rfl
  have hT₀card : Nat.card T₀ ≤ Nat.card T := by
    obtain ⟨P, hP'⟩ := hT₀.2.1.exists_le_sylow
    have h1 : Nat.card T₀ ≤ Nat.card P := Subgroup.card_le_of_le hP'
    have h2 : Nat.card P = Nat.card Tsyl := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    rw [← hTsyl]; exact h1.trans h2.le
  have hne : T₁ ≠ T₀ := fun h => hxQ (hT₁Q (h ▸ hxT₀))
  have hidx₀ : 2 ≤ T₁.relIndex T₀ := by
    have hpos : T₁.relIndex T₀ ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (H := T₁.subgroupOf T₀)
    have h1 : T₁.relIndex T₀ ≠ 1 := fun h =>
      hne (le_antisymm hT₁T₀ (Subgroup.relIndex_eq_one.mp h))
    omega
  have hcard₀ : Nat.card T₀ = Nat.card T₁ * T₁.relIndex T₀ := card_eq_card_mul_relIndex hT₁T₀
  have hcardT : Nat.card T = Nat.card T₁ * T₁.relIndex T := card_eq_card_mul_relIndex inf_le_left
  have hpos₁ : 0 < Nat.card T₁ := Nat.card_pos
  have hns : ¬ T ≤ normalizer (K₁ : Set G) := by
    intro hTK
    have h1 : T₁ = T := le_antisymm inf_le_left (le_inf le_rfl hTK)
    rw [h1] at hcard₀ hidx₀
    have : Nat.card T * T.relIndex T₀ ≤ Nat.card T * 1 := by
      rw [← hcard₀, mul_one]; exact hT₀card
    have := Nat.le_of_mul_le_mul_left this (Nat.card_pos)
    omega
  refine ⟨hns, x, hxM₁.1, ?_, ?_⟩
  ·
    have hidxT : T₁.relIndex T = 2 := by
      have h1 : T₁.relIndex T ≠ 1 := fun h =>
        hns ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)
      have h0 : T₁.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite (H := T₁.subgroupOf T)
      have hle2 : T₁.relIndex T ≤ 2 := hcfg.index
      omega
    have h2 : T₁.relIndex T₀ = 2 := by
      have : Nat.card T₁ * T₁.relIndex T₀ ≤ Nat.card T₁ * 2 := by
        rw [← hcard₀, ← hidxT, ← hcardT]; exact hT₀card
      have := Nat.le_of_mul_le_mul_left this hpos₁
      omega
    have hn : (T₁.subgroupOf T₀).Normal := Subgroup.normal_of_index_eq_two h2
    exact (normal_subgroupOf_iff_le_normalizer hT₁T₀).mp hn hxT₀
  ·
    intro hle
    apply hxQ
    have hxS : x ∈ normalizer (S : Set G) := hM₀S hxM₁.1
    have hxF : x ∈ normalizer (F : Set G) := hxM₁.2
    have hUx : conjSubgroup U₁ x ≤ Q := by
      refine le_inf ?_ hle
      have := conjSubgroup_mono hUS x
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hxS] at this
    have hDx : conjSubgroup D x ≤ Q := hP.conj_D_le hxS hxF
    have hQx : conjSubgroup Q x ≤ Q := by
      have e : conjSubgroup Q x = conjSubgroup U₁ x ⊔ conjSubgroup D x := by
        conv_lhs => rw [hP.hQ]
        exact conjSubgroup_sup _ _ _
      rw [e]
      exact sup_le hUx hDx
    have := Subgroup.eq_of_le_of_card_ge hQx (by rw [card_conjSubgroup])
    exact conjSubgroup_eq_iff_mem_normalizer.mp this

end BlockConfig

end CFSG.Quasithin.C58
